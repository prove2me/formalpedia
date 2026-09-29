-- Prove2me | solution 1 for HighDimProb.Chaining.sauer_shelah
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-27T05:09:42.866124+00:00
-- url     : https://prove2.me/submissions/be8eb230-a59c-4c4e-ad11-bc1ae27f49b7

import Mathlib
import Definitions.Def_HighDimProb_Chaining_VcDim



namespace HighDimProb.Chaining

lemma ss_binom_bound (d m : ℕ) (hd : 1 ≤ d) (hdm : d ≤ m) :
    ∑ i ∈ Finset.range (d + 1), (m.choose i : ℝ) ≤ (Real.exp 1 * m / d) ^ d := by
  have hdR : (0:ℝ) < d := by exact_mod_cast hd
  have hmR : (0:ℝ) < m := by exact_mod_cast (lt_of_lt_of_le hd hdm)
  have hdm' : (d:ℝ) ≤ m := by exact_mod_cast hdm
  set r : ℝ := d / m with hr
  have hr0 : 0 < r := by positivity
  have hr1 : r ≤ 1 := by rw [hr, div_le_one hmR]; exact hdm'
  have hrd : 0 < r ^ d := pow_pos hr0 d
  have step1 : ∑ i ∈ Finset.range (d + 1), (m.choose i : ℝ) ≤
      (∑ i ∈ Finset.range (d + 1), (m.choose i : ℝ) * r ^ i) / r ^ d := by
    rw [le_div_iff₀ hrd, Finset.sum_mul]
    apply Finset.sum_le_sum
    intro i hi
    simp only [Finset.mem_range] at hi
    have : r ^ d ≤ r ^ i := pow_le_pow_of_le_one hr0.le hr1 (by omega)
    exact mul_le_mul_of_nonneg_left this (Nat.cast_nonneg _)
  have step2 : ∑ i ∈ Finset.range (d + 1), (m.choose i : ℝ) * r ^ i ≤
      ∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) * r ^ i := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr (by omega))
    intro i _ _
    positivity
  have step3 : ∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) * r ^ i = (r + 1) ^ m := by
    rw [add_pow]
    apply Finset.sum_congr rfl
    intro i _
    rw [one_pow, mul_one, mul_comm]
  have step4 : (r + 1) ^ m ≤ Real.exp d := by
    calc (r + 1) ^ m ≤ (Real.exp r) ^ m :=
          pow_le_pow_left₀ (by linarith) (by linarith [Real.add_one_le_exp r]) m
      _ = Real.exp (m * r) := by rw [← Real.exp_nat_mul]
      _ = Real.exp d := by rw [hr]; congr 1; field_simp
  have step5 : Real.exp d / r ^ d = (Real.exp 1 * m / d) ^ d := by
    rw [show Real.exp d = Real.exp 1 ^ d by rw [← Real.exp_nat_mul, mul_one], hr, div_pow,
      mul_div_assoc, mul_pow, div_pow]
    field_simp
  calc ∑ i ∈ Finset.range (d + 1), (m.choose i : ℝ)
      ≤ (∑ i ∈ Finset.range (d + 1), (m.choose i : ℝ) * r ^ i) / r ^ d := step1
    _ ≤ (∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) * r ^ i) / r ^ d :=
        div_le_div_of_nonneg_right step2 hrd.le
    _ = (r + 1) ^ m / r ^ d := by rw [step3]
    _ ≤ Real.exp d / r ^ d := div_le_div_of_nonneg_right step4 hrd.le
    _ = (Real.exp 1 * m / d) ^ d := step5

lemma ss_vc_le_card {Ω : Type} [Fintype Ω] (F : Set (Ω → Bool)) :
    vcDim F ≤ Fintype.card Ω := by
  unfold vcDim
  refine iSup_le fun Λ => ?_
  calc Λ.1.encard ≤ (Set.univ : Set Ω).encard := Set.encard_le_encard (Set.subset_univ _)
    _ = Fintype.card Ω := by rw [Set.encard_univ, ENat.card_eq_coe_fintype_card]

lemma ss_vc_ne_top {Ω : Type} [Fintype Ω] (F : Set (Ω → Bool)) : vcDim F ≠ ⊤ :=
  ne_top_of_le_ne_top (ENat.coe_ne_top _) (ss_vc_le_card F)

lemma ss_card_le_vc {Ω : Type} [Fintype Ω] [DecidableEq Ω] (F : Finset (Ω → Bool))
    (t : Finset Ω)
    (ht : t ∈ (F.image (fun f => Finset.univ.filter (fun x => f x = true))).shatterer) :
    t.card ≤ (vcDim (F : Set (Ω → Bool))).toNat := by
  rw [Finset.mem_shatterer] at ht
  have hsh : Shatters (F : Set (Ω → Bool)) (t : Set Ω) := by
    intro g
    set u : Finset Ω := t.filter
      (fun y => if h : y ∈ t then g ⟨y, Finset.mem_coe.mpr h⟩ = true else False) with hu
    have hut : u ⊆ t := Finset.filter_subset _ t
    obtain ⟨v, hv, hvu⟩ := ht hut
    obtain ⟨f, hfF, rfl⟩ := Finset.mem_image.mp hv
    refine ⟨f, Finset.mem_coe.mpr hfF, ?_⟩
    rintro ⟨x, hx⟩
    have hxt : x ∈ t := Finset.mem_coe.mp hx
    have key : x ∈ t ∩ Finset.univ.filter (fun y => f y = true) ↔ x ∈ u := by rw [hvu]
    simp only [Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and, hu,
      dif_pos hxt] at key
    apply Bool.eq_iff_iff.mpr
    constructor
    · intro h; exact (key.mp ⟨hxt, h⟩).2
    · intro h; exact (key.mpr ⟨hxt, h⟩).2
  have h1 : (t : Set Ω).encard ≤ vcDim (F : Set (Ω → Bool)) :=
    le_iSup (fun Λ : {Λ : Set Ω // Shatters (F : Set (Ω → Bool)) Λ} => Λ.1.encard) ⟨t, hsh⟩
  rw [Set.encard_coe_eq_coe_finsetCard, ← ENat.coe_toNat (ss_vc_ne_top _)] at h1
  exact_mod_cast h1

theorem ss_main {Ω : Type} [Fintype Ω] (F : Finset (Ω → Bool)) :
    (F.card : ℝ) ≤
        ∑ k ∈ Finset.range ((vcDim (F : Set (Ω → Bool))).toNat + 1),
          ((Fintype.card Ω).choose k : ℝ) ∧
      (F.card : ℝ) ≤
        (Real.exp 1 * (Fintype.card Ω : ℝ) / (vcDim (F : Set (Ω → Bool))).toNat) ^
          (vcDim (F : Set (Ω → Bool))).toNat := by
  classical
  set d := (vcDim (F : Set (Ω → Bool))).toNat with hd
  set tset : (Ω → Bool) → Finset Ω := fun f => Finset.univ.filter (fun x => f x = true)
    with htset
  have hinj : Function.Injective tset := by
    intro f g hfg
    funext x
    have hx := congrArg (fun s : Finset Ω => x ∈ s) hfg
    simp only [htset, Finset.mem_filter, Finset.mem_univ, true_and, eq_iff_iff] at hx
    exact Bool.eq_iff_iff.mpr hx
  set 𝒜 := F.image tset with h𝒜
  have hcard : F.card = 𝒜.card := (Finset.card_image_of_injective _ hinj).symm
  have hvc : 𝒜.vcDim ≤ d := by
    unfold Finset.vcDim
    exact Finset.sup_le fun t ht => ss_card_le_vc F t ht
  have h1 : F.card ≤ ∑ k ∈ Finset.range (d + 1), (Fintype.card Ω).choose k := by
    calc F.card = 𝒜.card := hcard
      _ ≤ 𝒜.shatterer.card := Finset.card_le_card_shatterer 𝒜
      _ ≤ ∑ k ∈ Finset.Iic 𝒜.vcDim, (Fintype.card Ω).choose k :=
          Finset.card_shatterer_le_sum_vcDim
      _ ≤ ∑ k ∈ Finset.Iic d, (Fintype.card Ω).choose k :=
          Finset.sum_le_sum_of_subset (Finset.Iic_subset_Iic.mpr hvc)
      _ = ∑ k ∈ Finset.range (d + 1), (Fintype.card Ω).choose k := by
          congr 1
          ext k
          simp [Nat.lt_succ_iff]
  have h1R : (F.card : ℝ) ≤ ∑ k ∈ Finset.range (d + 1), ((Fintype.card Ω).choose k : ℝ) := by
    exact_mod_cast h1
  refine ⟨h1R, ?_⟩
  rcases Nat.eq_zero_or_pos d with h0 | hpos
  · rw [h0] at h1R ⊢
    simpa using h1R
  · have hdn : d ≤ Fintype.card Ω := by
      have := ss_vc_le_card (F : Set (Ω → Bool))
      rw [← ENat.coe_toNat (ss_vc_ne_top _)] at this
      exact_mod_cast this
    exact h1R.trans (ss_binom_bound d _ hpos hdn)

end HighDimProb.Chaining

open HighDimProb.Chaining

theorem solution {Ω : Type} [Fintype Ω] (F : Finset (Ω → Bool)) :
    (F.card : ℝ) ≤
        ∑ k ∈ Finset.range ((vcDim (F : Set (Ω → Bool))).toNat + 1),
          ((Fintype.card Ω).choose k : ℝ) ∧
      (F.card : ℝ) ≤
        (Real.exp 1 * (Fintype.card Ω : ℝ) / (vcDim (F : Set (Ω → Bool))).toNat) ^
          (vcDim (F : Set (Ω → Bool))).toNat := by
  exact ss_main F
