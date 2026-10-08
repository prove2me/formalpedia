-- Prove2me | solution 1 for JMMS.isAmenable_of_isAmenable_inf_range_inr
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-07T10:57:49.340984+00:00
-- url     : https://prove2.me/submissions/27528c39-0b49-48fe-91f4-70b69cfd2b44

import Mathlib
import Definitions.Def_IntervalExchange
import Theorems.Thm_JMMS_isAmenableAction_and_isExtensivelyAmenable_functorProduct_and_isExtensivelyAmenable_of_isTight
import Theorems.Thm_JMMS_isExtensivelyAmenable_of_isAmenable_and_isAmenableAction_of_isExtensivelyAmenable

section
/-! # JMMS Corollary 1.4

By Theorem 1.3 the action of `FunctorProduct F G X` on `extend F X` is extensively amenable. The
mean on finite sets restricts to a subgroup `H` and to the `H`-orbit `O` of `1` (`E ↦ E ∩ O`), so
`H ↷ O` is extensively amenable; Lemma 2.1(b) gives an `H`-invariant mean on `O`. The stabilizer of
`1` in `H` is `H ⊓ range inr`, which is amenable; the induced-mean argument (average a left-invariant
mean of the stabilizer over each coset, then integrate over `O`) makes `H` amenable. Finitely
additive integration is copied from `Solutions/FAmen/HZ/Lib.lean`. -/

open IntervalExchange
open scoped ENNReal Pointwise

namespace JMMS.IETP14

/-! ## Part B1: integrating `[0,1]`-valued functions against a finitely additive probability -/

/-- `∑_{k < 2^n} 2^{-n} m {f ≥ (k+1)/2^n}`: the integral of `⌊2^n f⌋ / 2^n`. -/
noncomputable def layerSum {α : Type*} (m : Set α → ℝ≥0∞) (f : α → ℝ) (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (2 ^ n), (m {a | ((k + 1 : ℕ) : ℝ) / 2 ^ n ≤ f a}).toReal / 2 ^ n

/-- The integral: the supremum of the layer sums. -/
noncomputable def integ {α : Type*} (m : Set α → ℝ≥0∞) (f : α → ℝ) : ℝ := ⨆ n, layerSum m f n


namespace PartB1
open scoped ENNReal


variable {α : Type*} {m : Set α → ℝ≥0∞}

/-! ### Elementary facts about a finitely additive probability -/

lemma fa_mono (hm : Garrido.IsFinitelyAdditiveMeasure m) {S T : Set α} (h : S ⊆ T) :
    m S ≤ m T := by
  have hd : Disjoint S (T \ S) := Set.disjoint_sdiff_right
  have := hm.2 S (T \ S) hd
  rw [Set.union_sdiff_cancel h] at this
  rw [this]
  exact le_self_add

lemma fa_le_one (hm : Garrido.IsFinitelyAdditiveMeasure m) (h1 : m Set.univ = 1) (S : Set α) :
    m S ≤ 1 := h1 ▸ fa_mono hm (Set.subset_univ S)

lemma fa_ne_top (hm : Garrido.IsFinitelyAdditiveMeasure m) (h1 : m Set.univ = 1) (S : Set α) :
    m S ≠ ∞ := ne_top_of_le_ne_top ENNReal.one_ne_top (fa_le_one hm h1 S)

lemma fa_toReal_union (hm : Garrido.IsFinitelyAdditiveMeasure m) (h1 : m Set.univ = 1)
    {S T : Set α} (h : Disjoint S T) :
    (m (S ∪ T)).toReal = (m S).toReal + (m T).toReal := by
  rw [hm.2 S T h, ENNReal.toReal_add (fa_ne_top hm h1 S) (fa_ne_top hm h1 T)]

lemma fa_toReal_mono (hm : Garrido.IsFinitelyAdditiveMeasure m) (h1 : m Set.univ = 1)
    {S T : Set α} (h : S ⊆ T) : (m S).toReal ≤ (m T).toReal :=
  ENNReal.toReal_mono (fa_ne_top hm h1 T) (fa_mono hm h)

lemma fa_toReal_le_one (hm : Garrido.IsFinitelyAdditiveMeasure m) (h1 : m Set.univ = 1)
    (S : Set α) : (m S).toReal ≤ 1 := by
  have := fa_toReal_mono hm h1 (Set.subset_univ S)
  rwa [h1, ENNReal.toReal_one] at this

/-! ### Bounds on the layer sums -/

lemma layerSum_nonneg (f : α → ℝ) (n : ℕ) : 0 ≤ layerSum m f n := by
  unfold layerSum
  exact Finset.sum_nonneg fun k _ => div_nonneg ENNReal.toReal_nonneg (by positivity)

lemma layerSum_le_one (hm : Garrido.IsFinitelyAdditiveMeasure m) (h1 : m Set.univ = 1)
    (f : α → ℝ) (n : ℕ) : layerSum m f n ≤ 1 := by
  unfold layerSum
  calc ∑ k ∈ Finset.range (2 ^ n), (m {a | ((k + 1 : ℕ) : ℝ) / 2 ^ n ≤ f a}).toReal / 2 ^ n
      ≤ ∑ _k ∈ Finset.range (2 ^ n), (1 : ℝ) / 2 ^ n := by
        gcongr with k
        exact fa_toReal_le_one hm h1 _
    _ = 1 := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        push_cast
        field_simp

lemma bddAbove_layerSum (hm : Garrido.IsFinitelyAdditiveMeasure m) (h1 : m Set.univ = 1)
    (f : α → ℝ) : BddAbove (Set.range (layerSum m f)) :=
  ⟨1, by rintro _ ⟨n, rfl⟩; exact layerSum_le_one hm h1 f n⟩

/-! ### The four easy lemmas -/

theorem integ_indicator (hm : Garrido.IsFinitelyAdditiveMeasure m) (h1 : m Set.univ = 1)
    (S : Set α) : integ m (S.indicator 1) = (m S).toReal := by
  have key : ∀ n, layerSum m (S.indicator 1) n = (m S).toReal := by
    intro n
    unfold layerSum
    have hset : ∀ k ∈ Finset.range (2 ^ n),
        {a | ((k + 1 : ℕ) : ℝ) / 2 ^ n ≤ S.indicator 1 a} = S := by
      intro k hk
      have hk' : k + 1 ≤ 2 ^ n := Finset.mem_range.1 hk
      have hpos : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) / 2 ^ n := by positivity
      have hle : ((k + 1 : ℕ) : ℝ) / 2 ^ n ≤ 1 := by
        rw [div_le_one (by positivity)]
        exact_mod_cast hk'
      push_cast at hpos hle
      ext a
      by_cases ha : a ∈ S
      · simp [ha, hle]
      · simp [ha, hpos]
    rw [Finset.sum_congr rfl fun k hk => by rw [hset k hk], Finset.sum_const,
      Finset.card_range, nsmul_eq_mul]
    push_cast
    field_simp
  unfold integ
  simp only [key, ciSup_const]

theorem integ_comp_equiv (τ : α ≃ α) (hτ : ∀ S : Set α, m (τ '' S) = m S) (f : α → ℝ) :
    integ m (f ∘ τ) = integ m f := by
  have heq : ∀ c : ℝ, m {a | c ≤ (f ∘ τ) a} = m {a | c ≤ f a} := by
    intro c
    have : {a | c ≤ (f ∘ τ) a} = τ ⁻¹' {a | c ≤ f a} := rfl
    rw [this, ← hτ (τ ⁻¹' {a | c ≤ f a}), Equiv.image_preimage]
  unfold integ layerSum
  simp only [heq]

theorem integ_nonneg_le_one (hm : Garrido.IsFinitelyAdditiveMeasure m) (h1 : m Set.univ = 1)
    {f : α → ℝ} (hf : ∀ a, 0 ≤ f a) (hf1 : ∀ a, f a ≤ 1) : 0 ≤ integ m f ∧ integ m f ≤ 1 :=
  ⟨Real.iSup_nonneg fun n => layerSum_nonneg f n,
    Real.iSup_le (fun n => layerSum_le_one hm h1 f n) zero_le_one⟩

/-! ### `ℕ`-valued layer sums: the integral of a finitely-valued function -/

/-- `∑_{k<N} m{φ ≥ k+1}`: the integral of an `ℕ`-valued function `φ ≤ N`. -/
noncomputable def J (m : Set α → ℝ≥0∞) (φ : α → ℕ) (N : ℕ) : ℝ :=
  ∑ k ∈ Finset.range N, (m {a | k + 1 ≤ φ a}).toReal

lemma J_mono (hm : Garrido.IsFinitelyAdditiveMeasure m) (h1 : m Set.univ = 1)
    {φ ψ : α → ℕ} (h : ∀ a, φ a ≤ ψ a) (N : ℕ) : J m φ N ≤ J m ψ N := by
  unfold J
  exact Finset.sum_le_sum fun k _ => fa_toReal_mono hm h1 fun a ha => le_trans ha (h a)

lemma J_extend (hm : Garrido.IsFinitelyAdditiveMeasure m) {φ : α → ℕ} {N : ℕ}
    (h : ∀ a, φ a ≤ N) (N' : ℕ) (hN' : N ≤ N') : J m φ N' = J m φ N := by
  induction N', hN' using Nat.le_induction with
  | base => rfl
  | succ n hn ih =>
    unfold J at ih ⊢
    rw [Finset.sum_range_succ, ih]
    have : {a | n + 1 ≤ φ a} = ∅ := by
      ext a
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_le]
      exact Nat.lt_succ_of_le ((h a).trans hn)
    rw [this, hm.1, ENNReal.toReal_zero, add_zero]

lemma sum_level (hm : Garrido.IsFinitelyAdditiveMeasure m) (h1 : m Set.univ = 1)
    (A : Set α) (φ : α → ℕ) (N : ℕ) :
    ∑ k ∈ Finset.range N, (m {a | a ∈ A ∧ φ a = k}).toReal =
      (m {a | a ∈ A ∧ φ a < N}).toReal := by
  induction N with
  | zero => simp [hm.1]
  | succ N ih =>
    rw [Finset.sum_range_succ, ih, ← fa_toReal_union hm h1]
    · congr 2
      ext a
      by_cases ha : a ∈ A <;> (simp [ha]; try omega)
    · rw [Set.disjoint_left]
      rintro a ⟨_, ha⟩ ⟨_, hb⟩
      omega

/-- Adding a `{0,1}`-valued function adds the measure of its support. -/
lemma J_add_le_one (hm : Garrido.IsFinitelyAdditiveMeasure m) (h1 : m Set.univ = 1)
    (φ χ : α → ℕ) (N : ℕ) (hχ : ∀ a, χ a ≤ 1) (h : ∀ a, φ a + χ a ≤ N) :
    J m (φ + χ) N = J m φ N + (m {a | 1 ≤ χ a}).toReal := by
  have hterm : ∀ k, (m {a | k + 1 ≤ (φ + χ) a}).toReal =
      (m {a | k + 1 ≤ φ a}).toReal + (m {a | a ∈ {a | 1 ≤ χ a} ∧ φ a = k}).toReal := by
    intro k
    rw [← fa_toReal_union hm h1]
    · congr 2
      ext a
      have := hχ a
      simp only [Pi.add_apply, Set.mem_ofPred_eq, Set.mem_union]
      omega
    · rw [Set.disjoint_left]
      rintro a ha ⟨hb, hc⟩
      simp only [Set.mem_ofPred_eq] at ha hb
      omega
  unfold J
  rw [Finset.sum_congr rfl fun k _ => hterm k, Finset.sum_add_distrib, sum_level hm h1]
  congr 3
  ext a
  simp only [Set.mem_ofPred_eq, and_iff_left_iff_imp]
  intro ha
  have := h a
  omega

lemma J_zero (hm : Garrido.IsFinitelyAdditiveMeasure m) (N : ℕ) : J m 0 N = 0 := by
  unfold J
  refine Finset.sum_eq_zero fun k _ => ?_
  have : {a : α | k + 1 ≤ (0 : α → ℕ) a} = ∅ := by
    ext a; simp
  rw [this, hm.1, ENNReal.toReal_zero]

/-- Additivity of `J` (induction on a bound for `ψ`). -/
lemma J_add (hm : Garrido.IsFinitelyAdditiveMeasure m) (h1 : m Set.univ = 1) (N : ℕ) :
    ∀ (M : ℕ) (φ ψ : α → ℕ), (∀ a, ψ a ≤ M) → (∀ a, φ a + ψ a ≤ N) →
      J m (φ + ψ) N = J m φ N + J m ψ N := by
  intro M
  induction M with
  | zero =>
    intro φ ψ hψ _
    have hψ0 : ψ = 0 := funext fun a => Nat.le_zero.1 (hψ a)
    subst hψ0
    rw [add_zero, J_zero hm, add_zero]
  | succ M ih =>
    intro φ ψ hψ h
    have hsplit : ψ = (fun a => min (ψ a) M) + (fun a => ψ a - M) :=
      funext fun a => by simp only [Pi.add_apply]; omega
    have hχ : ∀ a, (fun a => ψ a - M) a ≤ 1 := fun a => by
      have := hψ a; try dsimp only
      omega
    rw [hsplit, ← add_assoc, J_add_le_one hm h1 _ _ N hχ, ih φ _ (fun a => min_le_right _ _),
      J_add_le_one hm h1 _ _ N hχ]
    · ring
    all_goals
      intro a; have := h a; have := hψ a
      try dsimp only [Pi.add_apply]
      omega

/-! ### The layer sums through `J` -/

lemma layerSum_eq (f : α → ℝ) (n : ℕ) :
    layerSum m f n = J m (fun a => ⌊2 ^ n * f a⌋₊) (2 ^ n) / 2 ^ n := by
  unfold layerSum J
  push_cast
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun k _ => ?_
  congr 3
  ext a
  simp only [Set.mem_ofPred_eq]
  rw [← Nat.cast_succ, Nat.le_floor_iff' (Nat.succ_ne_zero k), div_le_iff₀ (by positivity),
    mul_comm]

lemma floor_le_pow {f : α → ℝ} (hf1 : ∀ a, f a ≤ 1) (n : ℕ) (a : α) :
    ⌊2 ^ n * f a⌋₊ ≤ 2 ^ n := by
  apply Nat.floor_le_of_le
  push_cast
  have : (0 : ℝ) < 2 ^ n := by positivity
  nlinarith [hf1 a]

lemma layerSum_mono (hm : Garrido.IsFinitelyAdditiveMeasure m) (h1 : m Set.univ = 1)
    {f : α → ℝ} (hf : ∀ a, 0 ≤ f a) (hf1 : ∀ a, f a ≤ 1) : Monotone (layerSum m f) := by
  refine monotone_nat_of_le_succ fun n => ?_
  rw [layerSum_eq, layerSum_eq]
  set φ : α → ℕ := fun a => ⌊2 ^ n * f a⌋₊ with hφdef
  have hφ : ∀ a, φ a ≤ 2 ^ n := floor_le_pow hf1 n
  have h2 : ∀ a, (φ + φ) a ≤ ⌊2 ^ (n + 1) * f a⌋₊ := by
    intro a
    apply Nat.le_floor
    have := Nat.floor_le (show 0 ≤ (2 : ℝ) ^ n * f a by have := hf a; positivity)
    simp only [Pi.add_apply, hφdef]
    push_cast
    rw [pow_succ]
    linarith
  have key : 2 * J m φ (2 ^ n) ≤ J m (fun a => ⌊2 ^ (n + 1) * f a⌋₊) (2 ^ (n + 1)) := by
    calc 2 * J m φ (2 ^ n) = J m φ (2 ^ (n + 1)) + J m φ (2 ^ (n + 1)) := by
          rw [J_extend hm hφ (2 ^ (n + 1)) (Nat.pow_le_pow_right (by norm_num) (by omega))]
          ring
      _ = J m (φ + φ) (2 ^ (n + 1)) :=
          (J_add hm h1 _ (2 ^ n) φ φ hφ fun a => by have := hφ a; rw [pow_succ]; omega).symm
      _ ≤ _ := J_mono hm h1 h2 _
  have hp : (0 : ℝ) < 2 ^ n := by positivity
  rw [div_le_div_iff₀ hp (by positivity)]
  have e : J m φ (2 ^ n) * (2 : ℝ) ^ (n + 1) = 2 * J m φ (2 ^ n) * 2 ^ n := by
    rw [pow_succ]; ring
  rw [e]
  exact mul_le_mul_of_nonneg_right key hp.le

/-! ### Additivity -/

theorem integ_add (hm : Garrido.IsFinitelyAdditiveMeasure m) (h1 : m Set.univ = 1)
    {f g : α → ℝ} (hf : ∀ a, 0 ≤ f a) (hg : ∀ a, 0 ≤ g a) (hfg : ∀ a, f a + g a ≤ 1) :
    integ m (f + g) = integ m f + integ m g := by
  have hfg0 : ∀ a, 0 ≤ (f + g) a := fun a => add_nonneg (hf a) (hg a)
  have hf1 : ∀ a, f a ≤ 1 := fun a => by linarith [hfg a, hg a]
  have hg1 : ∀ a, g a ≤ 1 := fun a => by linarith [hfg a, hf a]
  have hfg1 : ∀ a, (f + g) a ≤ 1 := hfg
  have tf := tendsto_atTop_ciSup (layerSum_mono hm h1 hf hf1) (bddAbove_layerSum hm h1 f)
  have tg := tendsto_atTop_ciSup (layerSum_mono hm h1 hg hg1) (bddAbove_layerSum hm h1 g)
  have tfg := tendsto_atTop_ciSup (layerSum_mono hm h1 hfg0 hfg1) (bddAbove_layerSum hm h1 (f + g))
  have hbound : ∀ n, layerSum m f n + layerSum m g n ≤ layerSum m (f + g) n ∧
      layerSum m (f + g) n ≤ layerSum m f n + layerSum m g n + (1 / 2) ^ n := by
    intro n
    rw [layerSum_eq, layerSum_eq, layerSum_eq]
    set φ : α → ℕ := fun a => ⌊2 ^ n * f a⌋₊ with hφdef
    set ψ : α → ℕ := fun a => ⌊2 ^ n * g a⌋₊ with hψdef
    set χ : α → ℕ := fun a => ⌊2 ^ n * (f + g) a⌋₊ with hχdef
    have hp : (0 : ℝ) < 2 ^ n := by positivity
    have hlow : ∀ a, (φ + ψ) a ≤ χ a := by
      intro a
      apply Nat.le_floor
      have := Nat.floor_le (show 0 ≤ (2 : ℝ) ^ n * f a by have := hf a; positivity)
      have := Nat.floor_le (show 0 ≤ (2 : ℝ) ^ n * g a by have := hg a; positivity)
      simp only [Pi.add_apply, hφdef, hψdef]
      push_cast
      linarith
    have hup : ∀ a, χ a ≤ (φ + ψ + 1) a := by
      intro a
      have hlt : χ a < φ a + ψ a + 2 := by
        apply (Nat.floor_lt (by have := hfg0 a; positivity)).2
        have := Nat.lt_floor_add_one ((2 : ℝ) ^ n * f a)
        have := Nat.lt_floor_add_one ((2 : ℝ) ^ n * g a)
        simp only [Pi.add_apply, hφdef, hψdef]
        push_cast
        linarith
      simp only [Pi.add_apply, Pi.one_apply]
      omega
    have hχ : ∀ a, χ a ≤ 2 ^ n := floor_le_pow hfg1 n
    have hφ : ∀ a, φ a ≤ 2 ^ n := floor_le_pow hf1 n
    have hφψ : ∀ a, φ a + ψ a ≤ 2 ^ n := fun a => le_trans (hlow a) (hχ a)
    have hadd := J_add hm h1 (2 ^ n) (2 ^ n) φ ψ (floor_le_pow hg1 n) hφψ
    have h_lower : J m φ (2 ^ n) + J m ψ (2 ^ n) ≤ J m χ (2 ^ n) :=
      hadd ▸ J_mono hm h1 hlow (2 ^ n)
    have h_upper : J m χ (2 ^ n) ≤ J m φ (2 ^ n) + J m ψ (2 ^ n) + 1 := by
      rw [← J_extend hm hχ (2 ^ n + 1) (by omega)]
      calc J m χ (2 ^ n + 1) ≤ J m (φ + ψ + 1) (2 ^ n + 1) := J_mono hm h1 hup _
        _ = J m (φ + ψ) (2 ^ n + 1) + (m {a | 1 ≤ (1 : α → ℕ) a}).toReal :=
            J_add_le_one hm h1 _ _ _ (fun a => le_refl _)
              (fun a => by have := hφψ a; simp only [Pi.add_apply, Pi.one_apply]; omega)
        _ ≤ J m (φ + ψ) (2 ^ n + 1) + 1 := by gcongr; exact fa_toReal_le_one hm h1 _
        _ = J m φ (2 ^ n) + J m ψ (2 ^ n) + 1 := by
            rw [J_extend hm (N := 2 ^ n) (fun a => by simpa only [Pi.add_apply] using hφψ a)
              (2 ^ n + 1) (by omega), hadd]
    rw [one_div_pow, ← add_div, ← add_div]
    exact ⟨div_le_div_of_nonneg_right h_lower hp.le, div_le_div_of_nonneg_right h_upper hp.le⟩
  have hd : Filter.Tendsto (fun n => layerSum m (f + g) n - (layerSum m f n + layerSum m g n))
      Filter.atTop (nhds 0) :=
    squeeze_zero (fun n => by linarith [(hbound n).1]) (fun n => by linarith [(hbound n).2])
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num))
  have := tendsto_nhds_unique (tfg.sub (tf.add tg)) hd
  unfold integ
  linarith

end PartB1

open PartB1

/-! ## Induced means: transitive action with an invariant mean and amenable stabilizer -/

theorem isAmenable_of_orbit {H Z K : Type*} [Group H] [MulAction H Z] [Group K]
    (ι : K →* H) (hK : Garrido.IsAmenable K) (z₀ : Z)
    (hstab : ∀ h : H, h • z₀ = z₀ → ∃ k, ι k = h)
    (μ : Set Z → ℝ≥0∞) (hμ : Garrido.IsFinitelyAdditiveMeasure μ) (hμ1 : μ Set.univ = 1)
    (hinv : ∀ (g : H) (S : Set Z), μ (g • S) = μ S)
    (horb : μ (MulAction.orbit H z₀) = 1) : Garrido.IsAmenable H := by
  classical
  obtain ⟨ν, hν, hν1, hνinv⟩ := hK
  set O := MulAction.orbit H z₀ with hO
  let s : Z → H := fun z => if hz : z ∈ O then hz.choose else 1
  have hs : ∀ z ∈ O, s z • z₀ = z := fun z hz => by
    simp only [s, dif_pos hz]; exact hz.choose_spec
  let φ : Set H → Z → ℝ := fun S z => if z ∈ O then (ν {k | s z * ι k ∈ S}).toReal else 0
  have hφ0 : ∀ S z, 0 ≤ φ S z := fun S z => by
    simp only [φ]; split_ifs <;> simp
  have hφ1 : ∀ S z, φ S z ≤ 1 := fun S z => by
    simp only [φ]; split_ifs
    · exact fa_toReal_le_one hν hν1 _
    · norm_num
  have hφuniv : φ Set.univ = O.indicator 1 := by
    funext z; simp only [φ, Set.indicator]; split_ifs <;> simp [hν1]
  have hφempty : φ ∅ = (∅ : Set Z).indicator 1 := by
    funext z; simp only [φ, Set.indicator]; split_ifs <;> simp_all [hν.1]
  have hφadd : ∀ S T : Set H, Disjoint S T → φ (S ∪ T) = φ S + φ T := by
    intro S T hST
    funext z
    simp only [φ, Pi.add_apply]
    split_ifs
    · have : {k | s z * ι k ∈ S ∪ T} = {k | s z * ι k ∈ S} ∪ {k | s z * ι k ∈ T} := by
        ext k; simp
      rw [this, fa_toReal_union hν hν1]
      exact hST.preimage (fun k => s z * ι k)
    · simp
  have hint : ∀ S, 0 ≤ integ μ (φ S) := fun S =>
    (integ_nonneg_le_one hμ hμ1 (hφ0 S) (hφ1 S)).1
  refine ⟨fun S => ENNReal.ofReal (integ μ (φ S)), ⟨?_, ?_⟩, ?_, ?_⟩
  · simp only
    rw [hφempty, integ_indicator hμ hμ1, hμ.1]; simp
  · intro S T hST
    simp only
    rw [hφadd S T hST, integ_add hμ hμ1 (hφ0 S) (hφ0 T)
      (fun z => by rw [← Pi.add_apply (f := φ S), ← hφadd S T hST]; exact hφ1 _ z),
      ENNReal.ofReal_add (hint S) (hint T)]
  · simp only
    rw [hφuniv, integ_indicator hμ hμ1, horb]; simp
  · intro g S
    simp only
    congr 1
    let τ : Equiv.Perm Z := MulAction.toPerm g⁻¹
    have hτ : ∀ A : Set Z, μ (τ '' A) = μ A := fun A => by
      have : τ '' A = g⁻¹ • A := by
        ext z; simp [τ, Set.mem_smul_set]
      rw [this, hinv]
    have hcomp : φ (g • S) = φ S ∘ τ := by
      funext z
      have hmem : (g⁻¹ • z ∈ O) ↔ z ∈ O := by
        constructor
        · rintro ⟨h, hh⟩; exact ⟨g * h, by simp only at hh ⊢; rw [mul_smul, hh, smul_inv_smul]⟩
        · rintro ⟨h, hh⟩; exact ⟨g⁻¹ * h, by simp only at hh ⊢; rw [mul_smul, hh]⟩
      simp only [φ, Function.comp_apply, τ, MulAction.toPerm_apply, hmem]
      split_ifs with hz
      · have hz' : g⁻¹ • z ∈ O := hmem.2 hz
        obtain ⟨k₀, hk₀⟩ := hstab ((s (g⁻¹ • z))⁻¹ * g⁻¹ * s z) (by
          rw [mul_smul, mul_smul, hs z hz, inv_smul_eq_iff, hs _ hz'])
        have hset : {k | s z * ι k ∈ g • S} = k₀⁻¹ • {k | s (g⁻¹ • z) * ι k ∈ S} := by
          ext k
          simp only [Set.mem_setOf_eq, Set.mem_smul_set_iff_inv_smul_mem, smul_eq_mul, inv_inv,
            map_mul, hk₀]
          group
        rw [hset, hνinv]
      · rfl
    rw [hcomp, integ_comp_equiv τ hτ]

/-! ## Restricting an extensively amenable action to a subgroup and an invariant subset -/

/-- If `G ↷ Z` is extensively amenable, `H ≤ G` and `O ⊆ Z` is `H`-invariant, then `H ↷ O` is
extensively amenable: push the mean forward along `E ↦ E ∩ O`. -/
theorem isExtensivelyAmenable_restrict {G Z : Type*} [Group G] [MulAction G Z]
    (hGZ : IsExtensivelyAmenable G Z) (H : Subgroup G) (O : Set Z)
    (hO : ∀ (h : H) (z : Z), z ∈ O → (h : G) • z ∈ O) :
    @IsExtensivelyAmenable H O _
      { smul := fun h z => ⟨(h : G) • (z : Z), hO h z z.2⟩
        one_smul := fun z => Subtype.ext (one_smul G (z : Z))
        mul_smul := fun a b z => Subtype.ext (mul_smul (a : G) (b : G) (z : Z)) } := by
  classical
  obtain ⟨m, hm, -, hm1, hinv, hE⟩ := hGZ
  let inst : MulAction H O :=
      { smul := fun h z => ⟨(h : G) • (z : Z), hO h z z.2⟩
        one_smul := fun z => Subtype.ext (one_smul G (z : Z))
        mul_smul := fun a b z => Subtype.ext (mul_smul (a : G) (b : G) (z : Z)) }
  let r : Finset Z → Finset O := fun E => E.subtype (· ∈ O)
  -- `r` intertwines the actions
  have hr : ∀ (h : H) (E : Finset Z),
      r ((MulAction.toPerm (h : G)).finsetCongr E) =
        (@MulAction.toPerm H O _ inst h).finsetCongr (r E) := by
    intro h E
    ext ⟨z, hz⟩
    simp only [r, Equiv.finsetCongr_apply, Finset.mem_subtype, Finset.mem_map_equiv,
      MulAction.toPerm_symm_apply]
    rfl
  refine ⟨fun S => m {E | r E ∈ S}, ⟨?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · simpa using hm.1
  · intro S T hST
    have : {E | r E ∈ S ∪ T} = {E | r E ∈ S} ∪ {E | r E ∈ T} := by ext; simp
    simp only
    rw [this, hm.2]
    exact hST.preimage r
  · simpa using hm1
  · simpa using hm1
  · intro h S
    simp only
    have : {E | r E ∈ (fun E => E.map (@MulAction.toPerm H O _ inst h).toEmbedding) '' S} =
        (fun E => E.map (MulAction.toPerm (h : G)).toEmbedding) '' {E | r E ∈ S} := by
      have e1 : (fun E => E.map (@MulAction.toPerm H O _ inst h).toEmbedding) '' S =
          (@MulAction.toPerm H O _ inst h).finsetCongr.symm ⁻¹' S :=
        by rw [← Equiv.image_eq_preimage_symm]; rfl
      have e2 : (fun E => E.map (MulAction.toPerm (h : G)).toEmbedding) '' {E | r E ∈ S} =
          (MulAction.toPerm (h : G)).finsetCongr.symm ⁻¹' {E | r E ∈ S} :=
        by rw [← Equiv.image_eq_preimage_symm]; rfl
      rw [e1, e2]
      ext E
      simp only [Set.mem_ofPred_eq, Set.mem_preimage, Equiv.finsetCongr_symm]
      have := hr h⁻¹ E
      have ha : (MulAction.toPerm (h : G) : Equiv.Perm Z).symm =
          MulAction.toPerm ((h⁻¹ : H) : G) := by
        ext; simp
      have hb : (@MulAction.toPerm H O _ inst h).symm = @MulAction.toPerm H O _ inst h⁻¹ := by
        ext; rfl
      rw [ha, hb, this]
    rw [this, hinv]
  · intro E₀ _
    simp only
    apply le_antisymm
    · calc _ ≤ m Set.univ := PartB1.fa_mono hm (Set.subset_univ _)
        _ = 1 := hm1
    · rw [← hE (E₀.map (Function.Embedding.subtype _)) (by simp)]
      apply PartB1.fa_mono hm
      intro E hE
      simp only [Set.mem_ofPred_eq] at hE ⊢
      intro x hx
      simp only [r, Finset.mem_subtype]
      exact hE (Finset.mem_map_of_mem _ hx)

end JMMS.IETP14

namespace JMMS

universe u v

theorem chk_isAmenable_of_isAmenable_inf_range_inr
    (F : CategoryTheory.Functor FinInj.{u} GrpCat.{u}) (hF : IsAmenableValued F)
    (G : Type v) [Group G] (X : Type u) [MulAction G X] (hGX : IsExtensivelyAmenable G X)
    (H : Subgroup (FunctorProduct F G X))
    (hH : Garrido.IsAmenable ↥(H ⊓ (SemidirectProduct.inr : G →* FunctorProduct F G X).range)) :
    Garrido.IsAmenable ↥H := by
  classical
  have hext := ((isAmenableAction_and_isExtensivelyAmenable_functorProduct_and_isExtensivelyAmenable_of_isTight
    F hF G X).1 hGX).2
  set O : Set (extend F X) := MulAction.orbit H (1 : extend F X) with hOdef
  have hO : ∀ (h : H) (z : extend F X), z ∈ O → (h : FunctorProduct F G X) • z ∈ O := by
    rintro h z ⟨g, rfl⟩
    refine ⟨h * g, ?_⟩
    show ((h * g : H) : FunctorProduct F G X) • (1 : extend F X) = _
    rw [Subgroup.coe_mul, mul_smul]
    rfl
  have hEA := IETP14.isExtensivelyAmenable_restrict hext H O hO
  let inst : MulAction H O :=
      { smul := fun h z => ⟨(h : FunctorProduct F G X) • (z : extend F X), hO h z z.2⟩
        one_smul := fun z => Subtype.ext (one_smul _ (z : extend F X))
        mul_smul := fun a b z => Subtype.ext (mul_smul (a : FunctorProduct F G X) b (z : extend F X)) }
  have hne : Nonempty O := ⟨⟨1, MulAction.mem_orbit_self _⟩⟩
  obtain ⟨μO, hμO, hμO1, hμOinv⟩ :=
    (@isExtensivelyAmenable_of_isAmenable_and_isAmenableAction_of_isExtensivelyAmenable H O _ inst).2
      hne hEA
  refine IETP14.isAmenable_of_orbit (Subgroup.inclusion (inf_le_left :
      H ⊓ (SemidirectProduct.inr : G →* FunctorProduct F G X).range ≤ H)) hH
    (1 : extend F X) ?_ (fun S => μO (Subtype.val ⁻¹' S)) ?_ ?_ ?_ ?_
  · intro h hh
    have hl : (h : FunctorProduct F G X).left = 1 := by
      have : (h : FunctorProduct F G X).left * extendAut F G X (h : FunctorProduct F G X).right 1
          = 1 := hh
      simpa using this
    refine ⟨⟨h, h.2, (h : FunctorProduct F G X).right, ?_⟩, rfl⟩
    ext
    · simp [hl]
    · simp
  · exact ⟨by simpa using hμO.1, fun s t hst => by simpa using hμO.2 _ _ (hst.preimage _)⟩
  · simpa using hμO1
  · intro g S
    rw [← hμOinv g (Subtype.val ⁻¹' S)]
    congr 1
    ext ⟨z, hz⟩
    simp only [Set.mem_preimage, Set.mem_smul_set_iff_inv_smul_mem]
    rfl
  · rw [show Subtype.val ⁻¹' O = (Set.univ : Set O) by ext; simp]
    exact hμO1

end JMMS
end

open IntervalExchange
universe u v
open JMMS in
theorem solution
    (F : CategoryTheory.Functor FinInj.{u} GrpCat.{u}) (hF : IsAmenableValued F)
    (G : Type v) [Group G] (X : Type u) [MulAction G X] (hGX : IsExtensivelyAmenable G X)
    (H : Subgroup (FunctorProduct F G X))
    (hH : Garrido.IsAmenable ↥(H ⊓ (SemidirectProduct.inr : G →* FunctorProduct F G X).range)) :
    Garrido.IsAmenable ↥H := by
  apply JMMS.chk_isAmenable_of_isAmenable_inf_range_inr <;> assumption
