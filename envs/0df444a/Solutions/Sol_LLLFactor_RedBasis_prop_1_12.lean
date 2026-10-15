-- Prove2me | solution 1 for LLLFactor.RedBasis.prop_1_12
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T19:44:19.938351+00:00
-- url     : https://prove2.me/submissions/cc48ef3e-0877-4d70-a383-06e81f5f4e8e

import Mathlib
import Definitions.Def_LLLFactor_RedBasis_Setting

set_option autoImplicit false

namespace LLLFactor.RedBasis

open InnerProductSpace in
lemma gs_orth {n : ℕ} (b : Fin n → Vec n) {i j : Fin n} (h : i ≠ j) :
    inner ℝ (gs b i) (gs b j) = 0 :=
  gramSchmidt_orthogonal ℝ b h

lemma gs_ne_zero {n : ℕ} {b : Fin n → Vec n} (hb : LinearIndependent ℝ b) (i : Fin n) :
    gs b i ≠ 0 :=
  InnerProductSpace.gramSchmidt_ne_zero i hb

lemma gs_norm_step {n : ℕ} {b : Fin n → Vec n} (hred : IsReduced b) (i : ℕ) (hi : i + 1 < n) :
    ‖gs b ⟨i, by omega⟩‖ ^ 2 ≤ 2 * ‖gs b ⟨i + 1, hi⟩‖ ^ 2 := by
  have h1 := hred.2 i hi
  have h2 := hred.1 ⟨i + 1, hi⟩ ⟨i, by omega⟩ (by simp [Fin.lt_def])
  set a := gs b ⟨i, by omega⟩ with ha
  set c := gs b ⟨i + 1, hi⟩ with hc
  set m := mu b ⟨i + 1, hi⟩ ⟨i, by omega⟩ with hm
  have horth : inner ℝ c (m • a) = 0 := by
    rw [inner_smul_right]
    have : inner ℝ c a = 0 := gs_orth b (by simp [Fin.ext_iff])
    rw [this]; simp
  have hsq : ‖c + m • a‖ ^ 2 = ‖c‖ ^ 2 + ‖m • a‖ ^ 2 := by
    have := norm_add_sq_eq_norm_sq_add_norm_sq_real horth
    nlinarith [this]
  rw [hsq, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs] at h1
  have hm2 : m ^ 2 ≤ 1 / 4 := by
    have := abs_le.mp h2
    nlinarith
  have : m ^ 2 * ‖a‖ ^ 2 ≤ 1 / 4 * ‖a‖ ^ 2 := by
    exact mul_le_mul_of_nonneg_right hm2 (sq_nonneg _)
  nlinarith

lemma gs_norm_le {n : ℕ} {b : Fin n → Vec n} (hred : IsReduced b) :
    ∀ d : ℕ, ∀ j k : Fin n, (k : ℕ) = j + d →
      ‖gs b j‖ ^ 2 ≤ 2 ^ d * ‖gs b k‖ ^ 2 := by
  intro d
  induction d with
  | zero =>
    intro j k h
    have : j = k := Fin.ext (by simpa using h.symm)
    subst this; simp
  | succ d ih =>
    intro j k h
    have hk : (k : ℕ) = ((j : ℕ) + d) + 1 := by omega
    have hlt : (j : ℕ) + d < n := by omega
    have h1 := ih j ⟨(j : ℕ) + d, hlt⟩ rfl
    have h2 := gs_norm_step hred ((j : ℕ) + d) (by omega)
    have hkk : (⟨(j : ℕ) + d + 1, by omega⟩ : Fin n) = k := Fin.ext (by simp [hk])
    rw [hkk] at h2
    have hpos : (0 : ℝ) < 2 ^ d := by positivity
    calc ‖gs b j‖ ^ 2 ≤ 2 ^ d * ‖gs b ⟨(j : ℕ) + d, hlt⟩‖ ^ 2 := h1
      _ ≤ 2 ^ d * (2 * ‖gs b k‖ ^ 2) := mul_le_mul_of_nonneg_left h2 hpos.le
      _ = 2 ^ (d + 1) * ‖gs b k‖ ^ 2 := by ring

lemma b_decomp {n : ℕ} (b : Fin n → Vec n) (i : Fin n) :
    b i = gs b i + ∑ l ∈ Finset.Iio i, mu b i l • gs b l := by
  have h := InnerProductSpace.gramSchmidt_def'' ℝ b i
  conv_lhs => rw [h]
  congr 1
  apply Finset.sum_congr rfl
  intro l _
  congr 1
  simp only [mu, gs]
  rw [real_inner_comm (b i), real_inner_self_eq_norm_sq]
  simp

lemma inner_b_gs {n : ℕ} {b : Fin n → Vec n} (hb : LinearIndependent ℝ b) (i l : Fin n) :
    inner ℝ (b i) (gs b l) = mu b i l * ‖gs b l‖ ^ 2 := by
  have h0 : gs b l ≠ 0 := gs_ne_zero hb l
  have h1 : inner ℝ (gs b l) (gs b l) = ‖gs b l‖ ^ 2 := real_inner_self_eq_norm_sq _
  have h2 : ‖gs b l‖ ^ 2 ≠ 0 := by positivity
  simp only [mu, h1]
  field_simp

lemma inner_b_gs_self {n : ℕ} (b : Fin n → Vec n) (i : Fin n) :
    inner ℝ (b i) (gs b i) = ‖gs b i‖ ^ 2 := by
  conv_lhs => rw [b_decomp b i]
  rw [inner_add_left, sum_inner, real_inner_self_eq_norm_sq]
  have : ∑ l ∈ Finset.Iio i, inner ℝ (mu b i l • gs b l) (gs b i) = 0 := by
    apply Finset.sum_eq_zero
    intro l hl
    have hne : l ≠ i := (Finset.mem_Iio.mp hl).ne
    rw [real_inner_smul_left, gs_orth b hne]; simp
  rw [this]; simp

lemma norm_b_sq {n : ℕ} {b : Fin n → Vec n} (hb : LinearIndependent ℝ b) (i : Fin n) :
    ‖b i‖ ^ 2 = ‖gs b i‖ ^ 2 + ∑ l ∈ Finset.Iio i, mu b i l ^ 2 * ‖gs b l‖ ^ 2 := by
  have h1 : ‖b i‖ ^ 2 = inner ℝ (b i) (b i) := (real_inner_self_eq_norm_sq _).symm
  rw [h1]
  conv_lhs => rw [show inner ℝ (b i) (b i) = inner ℝ (b i) (gs b i + ∑ l ∈ Finset.Iio i, mu b i l • gs b l) from by rw [← b_decomp b i]]
  rw [inner_add_right, inner_sum, inner_b_gs_self]
  congr 1
  apply Finset.sum_congr rfl
  intro l _
  rw [real_inner_smul_right, inner_b_gs hb]
  ring

lemma geom_aux (i : ℕ) : ∑ m ∈ Finset.range i, (2 : ℝ) ^ (i - m) + 2 = 2 ^ (i + 1) := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [Finset.sum_range_succ]
    have : ∑ m ∈ Finset.range i, (2 : ℝ) ^ (i + 1 - m) = 2 * ∑ m ∈ Finset.range i, (2 : ℝ) ^ (i - m) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro m hm
      have : i + 1 - m = (i - m) + 1 := by have := Finset.mem_range.mp hm; omega
      rw [this, pow_succ]; ring
    rw [this]
    simp only [Nat.add_sub_cancel_left]
    rw [pow_succ 2 (i+1)]
    nlinarith [ih]

lemma norm_b_le {n : ℕ} {b : Fin n → Vec n} (hb : LinearIndependent ℝ b) (hred : IsReduced b)
    (i : Fin n) : ‖b i‖ ^ 2 ≤ 2 ^ (i : ℕ) * ‖gs b i‖ ^ 2 := by
  rw [norm_b_sq hb i]
  have hterm : ∀ l ∈ Finset.Iio i, mu b i l ^ 2 * ‖gs b l‖ ^ 2 ≤
      (1 / 4) * (2 : ℝ) ^ ((i : ℕ) - (l : ℕ)) * ‖gs b i‖ ^ 2 := by
    intro l hl
    have hli : l < i := Finset.mem_Iio.mp hl
    have hm := abs_le.mp (hred.1 i l hli)
    have hm2 : mu b i l ^ 2 ≤ 1 / 4 := by nlinarith
    have hg := gs_norm_le hred ((i : ℕ) - (l : ℕ)) l i (by have := Fin.lt_def.mp hli; omega)
    calc mu b i l ^ 2 * ‖gs b l‖ ^ 2 ≤ (1 / 4) * ‖gs b l‖ ^ 2 :=
          mul_le_mul_of_nonneg_right hm2 (sq_nonneg _)
      _ ≤ (1 / 4) * (2 ^ ((i : ℕ) - (l : ℕ)) * ‖gs b i‖ ^ 2) :=
          mul_le_mul_of_nonneg_left hg (by norm_num)
      _ = _ := by ring
  have hsum := Finset.sum_le_sum hterm
  have hs : ∑ l ∈ Finset.Iio i, (1 / 4) * (2 : ℝ) ^ ((i : ℕ) - (l : ℕ)) * ‖gs b i‖ ^ 2
      = (1 / 4) * ‖gs b i‖ ^ 2 * ∑ m ∈ Finset.range (i : ℕ), (2 : ℝ) ^ ((i : ℕ) - m) := by
    have e : ∑ l ∈ Finset.Iio i, (2 : ℝ) ^ ((i : ℕ) - (l : ℕ))
        = ∑ m ∈ Finset.range (i : ℕ), (2 : ℝ) ^ ((i : ℕ) - m) := by
      have h := Finset.sum_map (Finset.Iio i) Fin.valEmbedding (fun m => (2 : ℝ) ^ ((i : ℕ) - m))
      rw [Fin.map_valEmbedding_Iio, Nat.Iio_eq_range] at h
      simpa using h.symm
    rw [← e, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro l _
    ring
  have hg := geom_aux (i : ℕ)
  have hone : (1 : ℝ) ≤ 2 ^ (i : ℕ) := one_le_pow₀ (by norm_num)
  have hnn : 0 ≤ ‖gs b i‖ ^ 2 := sq_nonneg _
  rw [hs] at hsum
  have hp : (2 : ℝ) ^ ((i : ℕ) + 1) = 2 * 2 ^ (i : ℕ) := by ring
  nlinarith [mul_nonneg hnn (sub_nonneg.mpr hone)]

lemma bK_inner {n : ℕ} (b : Fin n → Vec n) (K : Fin n) :
    inner ℝ (gs b K) (b K) = ‖gs b K‖ ^ 2 := by
  rw [real_inner_comm]; exact inner_b_gs_self b K

lemma lattice_lb {n : ℕ} {b : Fin n → Vec n} (hb : LinearIndependent ℝ b) (r : Fin n → ℤ)
    (K : Fin n) (hK : r K ≠ 0) (hr : ∀ k, K < k → r k = 0) :
    ‖gs b K‖ ≤ ‖∑ k, (r k : ℝ) • b k‖ := by
  set x : Vec n := ∑ k, (r k : ℝ) • b k with hx
  have hinner : inner ℝ x (gs b K) = (r K : ℝ) * ‖gs b K‖ ^ 2 := by
    rw [hx, sum_inner]
    rw [Finset.sum_eq_single K]
    · rw [real_inner_smul_left, inner_b_gs_self]
    · intro k _ hk
      rcases lt_or_gt_of_ne hk with hlt | hgt
      · rw [real_inner_smul_left, real_inner_comm, ← real_inner_comm]
        have := InnerProductSpace.gramSchmidt_inv_triangular ℝ b hlt
        rw [real_inner_comm] at this
        have h2 : inner ℝ (b k) (gs b K) = 0 := this
        rw [h2]; simp
      · rw [hr k hgt]; simp
    · intro h; exact absurd (Finset.mem_univ K) h
  have h0 : gs b K ≠ 0 := gs_ne_zero hb K
  have hpos : 0 < ‖gs b K‖ := norm_pos_iff.mpr h0
  have hcs := abs_real_inner_le_norm x (gs b K)
  rw [hinner, abs_mul, abs_of_nonneg (sq_nonneg _ : (0:ℝ) ≤ ‖gs b K‖ ^ 2)] at hcs
  have h1 : (1 : ℝ) ≤ |(r K : ℝ)| := by
    have : (1 : ℤ) ≤ |r K| := Int.one_le_abs hK
    have h' : ((1 : ℤ) : ℝ) ≤ ((|r K| : ℤ) : ℝ) := Int.cast_le.mpr this
    simpa using h'
  have : |(r K : ℝ)| * ‖gs b K‖ ≤ ‖x‖ := by
    have h3 : (|(r K : ℝ)| * ‖gs b K‖) * ‖gs b K‖ ≤ ‖x‖ * ‖gs b K‖ := by nlinarith
    exact le_of_mul_le_mul_right h3 hpos
  nlinarith


lemma exists_top_index {n : ℕ} {b : Fin n → Vec n} (hb : LinearIndependent ℝ b)
    {t : ℕ} (x : Fin t → Vec n) (r : Fin t → Fin n → ℤ)
    (hr : ∀ i, ∑ k, (r i k : ℝ) • b k = x i)
    (hxind : LinearIndependent ℝ x) (j : Fin n) (hjt : (j : ℕ) < t) :
    ∃ (i : Fin t) (K : Fin n), j ≤ K ∧ r i K ≠ 0 ∧ ∀ k, K < k → r i k = 0 := by
  have key : ∃ (i : Fin t) (k : Fin n), j ≤ k ∧ r i k ≠ 0 := by
    by_contra hcon
    have hcon' : ∀ i k, j ≤ k → r i k = 0 := fun i k hk => by
      by_contra h; exact hcon ⟨i, k, hk, h⟩
    set w : Fin (j : ℕ) → Vec n := fun k => b ⟨k, lt_trans k.2 j.2⟩ with hw
    set W : Submodule ℝ (Vec n) := Submodule.span ℝ (Set.range w) with hW
    have hmem : ∀ i, x i ∈ W := by
      intro i
      rw [← hr i]
      apply Submodule.sum_mem
      intro k _
      by_cases hk : k < j
      · apply Submodule.smul_mem
        exact Submodule.subset_span ⟨⟨k, hk⟩, rfl⟩
      · rw [hcon' i k (not_lt.mp hk)]; simp
    let x' : Fin t → W := fun i => ⟨x i, hmem i⟩
    have hind' : LinearIndependent ℝ x' := by
      apply LinearIndependent.of_comp W.subtype
      exact hxind
    have h1 := hind'.fintype_card_le_finrank
    have h2 : Module.finrank ℝ W ≤ Fintype.card (Fin (j : ℕ)) := finrank_range_le_card w
    simp only [Fintype.card_fin] at h1 h2
    omega
  obtain ⟨i, k, hjk, hk⟩ := key
  refine ⟨i, ?_⟩
  set S : Finset (Fin n) := Finset.univ.filter (fun k => r i k ≠ 0) with hS
  have hne : S.Nonempty := ⟨k, by simp [hS, hk]⟩
  refine ⟨S.max' hne, ?_, ?_, ?_⟩
  · exact hjk.trans (Finset.le_max' S k (by simp [hS, hk]))
  · have := Finset.max'_mem S hne
    simpa [hS] using this
  · intro k' hk'
    by_contra hne'
    have : k' ∈ S := by simp [hS, hne']
    exact absurd (Finset.le_max' S k' this) (not_le.mpr hk')

end LLLFactor.RedBasis

open LLLFactor.RedBasis in
theorem solution {n : ℕ} (hn : 0 < n) (L : Submodule ℤ (Vec n))
  (b : Fin n → Vec n) (hb : IsBasisFor b L) (hred : IsReduced b)
  {t : ℕ} (x : Fin t → Vec n) (hxL : ∀ j, x j ∈ L)
  (hxind : LinearIndependent ℝ x) :
  ∀ j : Fin t, ∀ (hj : (j : ℕ) < n),
    ‖b ⟨j, hj⟩‖ ^ 2 ≤
      (2 : ℝ) ^ (n - 1) * Finset.univ.sup' ⟨j, Finset.mem_univ j⟩ (fun i => ‖x i‖ ^ 2) := by
  intro j hj
  have hbi : LinearIndependent ℝ b := hb.1
  have hcoef : ∀ i, ∃ c : Fin n → ℤ, ∑ k, (c k : ℝ) • b k = x i := by
    intro i
    have h := hxL i
    rw [← hb.2, latticeOf, Submodule.mem_span_range_iff_exists_fun] at h
    obtain ⟨c, hc⟩ := h
    refine ⟨c, ?_⟩
    rw [← hc]
    apply Finset.sum_congr rfl
    intro k _
    exact Int.cast_smul_eq_zsmul ℝ (c k) (b k)
  choose r hr using hcoef
  obtain ⟨i, K, hjK, hrK, hrt⟩ := exists_top_index hbi x r hr hxind ⟨j, hj⟩ j.2
  have hlb := lattice_lb hbi (r i) K hrK hrt
  rw [hr i] at hlb
  have hKn : (K : ℕ) ≤ n - 1 := by have := K.2; omega
  have hjK' : (j : ℕ) ≤ K := hjK
  have h1 := norm_b_le hbi hred ⟨j, hj⟩
  have h2 := gs_norm_le hred ((K : ℕ) - j) ⟨j, hj⟩ K (by simp; omega)
  have h3 : ‖gs b K‖ ^ 2 ≤ ‖x i‖ ^ 2 := by
    exact pow_le_pow_left₀ (norm_nonneg _) hlb 2
  have h4 : ‖x i‖ ^ 2 ≤ Finset.univ.sup' ⟨j, Finset.mem_univ j⟩ (fun i => ‖x i‖ ^ 2) :=
    Finset.le_sup' (fun i => ‖x i‖ ^ 2) (Finset.mem_univ i)
  have h5 : (2 : ℝ) ^ (K : ℕ) ≤ 2 ^ (n - 1) := pow_le_pow_right₀ (by norm_num) hKn
  have hp : (2 : ℝ) ^ (j : ℕ) * 2 ^ ((K : ℕ) - j) = 2 ^ (K : ℕ) := by
    rw [← pow_add]; congr 1; omega
  have hpos : (0 : ℝ) ≤ 2 ^ (j : ℕ) := by positivity
  have hpos2 : (0 : ℝ) ≤ 2 ^ (K : ℕ) := by positivity
  calc ‖b ⟨j, hj⟩‖ ^ 2 ≤ 2 ^ (j : ℕ) * ‖gs b ⟨j, hj⟩‖ ^ 2 := h1
    _ ≤ 2 ^ (j : ℕ) * (2 ^ ((K : ℕ) - j) * ‖gs b K‖ ^ 2) := mul_le_mul_of_nonneg_left h2 hpos
    _ = 2 ^ (K : ℕ) * ‖gs b K‖ ^ 2 := by rw [← mul_assoc, hp]
    _ ≤ 2 ^ (K : ℕ) * ‖x i‖ ^ 2 := mul_le_mul_of_nonneg_left h3 hpos2
    _ ≤ 2 ^ (n - 1) * ‖x i‖ ^ 2 := mul_le_mul_of_nonneg_right h5 (sq_nonneg _)
    _ ≤ _ := mul_le_mul_of_nonneg_left h4 (by positivity)
