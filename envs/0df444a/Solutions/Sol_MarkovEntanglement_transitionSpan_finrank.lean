-- Prove2me | solution 1 for MarkovEntanglement.transitionSpan_finrank
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-08-07T15:43:00.558913+00:00
-- url     : https://prove2.me/submissions/ed79429d-1cc1-42de-a423-39e8b8b0834f

import Definitions.Def_markov_entanglement_multi

open scoped BigOperators
open MarkovEntanglement

/-- The linear map sending a matrix to its vector of row sums. -/
private def rowSum (m : ℕ) : Matrix (Fin m) (Fin m) ℝ →ₗ[ℝ] (Fin m → ℝ) where
  toFun M := fun i => ∑ k, M i k
  map_add' := by intro a b; funext i; simp [Finset.sum_add_distrib]
  map_smul' := by intro c a; funext i; simp [Finset.mul_sum]

private theorem rowSum_apply (m : ℕ) (M : Matrix (Fin m) (Fin m) ℝ) (i : Fin m) :
    rowSum m M i = ∑ k, M i k := rfl

theorem solution (m : ℕ) (hm : 0 < m) :
    Module.finrank ℝ (transitionSpan (Fin m)) = m ^ 2 - m + 1 := by
  classical
  set z : Fin m := ⟨0, hm⟩ with hz
  set T : Submodule ℝ (Matrix (Fin m) (Fin m) ℝ) := transitionSpan (Fin m) with hT
  -- the "all rows are `δ z`" transition matrix
  set S0 : Matrix (Fin m) (Fin m) ℝ := fun _ j => if j = z then 1 else 0 with hS0
  have hS0trans : IsTransitionMatrix S0 := by
    constructor
    · intro i j; by_cases h : j = z <;> simp [hS0, h]
    · intro i; simp [hS0]
  have hS0mem : S0 ∈ T := Submodule.subset_span hS0trans
  -- the elementary transition matrices
  set A : Fin m → Fin m → Matrix (Fin m) (Fin m) ℝ :=
    fun a k => fun i j => if i = a then (if j = k then 1 else 0) else (if j = z then 1 else 0)
    with hA
  have hAtrans : ∀ a k, IsTransitionMatrix (A a k) := by
    intro a k
    constructor
    · intro i j
      by_cases h : i = a
      · by_cases h2 : j = k <;> simp [hA, h, h2]
      · by_cases h2 : j = z <;> simp [hA, h, h2]
    · intro i
      by_cases h : i = a <;> simp [hA, h]
  have hAmem : ∀ a k, A a k ∈ T := fun a k => Submodule.subset_span (hAtrans a k)
  have hdiff : ∀ a k, ((A a k - A a z : Matrix (Fin m) (Fin m) ℝ)) ∈ T :=
    fun a k => Submodule.sub_mem _ (hAmem a k) (hAmem a z)
  -- every matrix with zero row sums lies in `T`
  have hker : ∀ M : Matrix (Fin m) (Fin m) ℝ, rowSum m M = 0 → M ∈ T := by
    intro M hM
    have hM' : ∀ i, ∑ k, M i k = 0 := fun i => congrFun hM i
    have hrep : M = ∑ a : Fin m, ∑ k : Fin m, M a k • (A a k - A a z) := by
      ext i j
      rw [Matrix.sum_apply]
      rw [Finset.sum_eq_single i]
      · rw [Matrix.sum_apply]
        have hstep : ∀ k : Fin m, (M i k • (A i k - A i z)) i j
            = M i k * (if j = k then (1:ℝ) else 0) - M i k * (if j = z then (1:ℝ) else 0) := by
          intro k
          rw [Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul, mul_sub]
          simp [hA, mul_ite]
        rw [Finset.sum_congr rfl (fun k _ => hstep k), Finset.sum_sub_distrib,
          ← Finset.sum_mul, hM' i, zero_mul, sub_zero]
        simp
      · intro a _ ha
        rw [Matrix.sum_apply]
        refine Finset.sum_eq_zero (fun k _ => ?_)
        rw [Matrix.smul_apply, Matrix.sub_apply]
        simp [hA, Ne.symm ha]
      · intro h; exact absurd (Finset.mem_univ i) h
    rw [hrep]
    exact Submodule.sum_mem _ (fun a _ =>
      Submodule.sum_mem _ (fun k _ => Submodule.smul_mem _ _ (hdiff a k)))
  -- `T` is the kernel of `rowSum` plus the line through `S0`
  have hTeq : T = LinearMap.ker (rowSum m) ⊔ (ℝ ∙ S0) := by
    apply le_antisymm
    · rw [hT, transitionSpan]
      refine Submodule.span_le.mpr ?_
      intro M hMtrans
      have hsub : rowSum m (M - S0) = 0 := by
        funext i
        rw [map_sub]
        simp only [Pi.sub_apply, rowSum_apply, Pi.zero_apply]
        rw [hMtrans.2 i, hS0trans.2 i, sub_self]
      have h1 : M - S0 ∈ LinearMap.ker (rowSum m) := hsub
      have h2 : M = (M - S0) + S0 := (sub_add_cancel M S0).symm
      rw [h2]
      exact Submodule.add_mem _ (Submodule.mem_sup_left h1)
        (Submodule.mem_sup_right (Submodule.mem_span_singleton_self S0))
    · refine sup_le ?_ ?_
      · intro M hM
        exact hker M hM
      · rw [Submodule.span_singleton_le_iff_mem]
        exact hS0mem
  -- dimension count
  have hsurj : Function.Surjective (rowSum m) := by
    intro v
    refine ⟨Matrix.of fun i j => if j = z then v i else 0, ?_⟩
    funext i
    rw [rowSum_apply]
    simp
  have hkerrank : Module.finrank ℝ (LinearMap.ker (rowSum m)) + m = m * m := by
    have h := LinearMap.finrank_range_add_finrank_ker (rowSum m)
    rw [LinearMap.range_eq_top.mpr hsurj, finrank_top] at h
    simp only [Module.finrank_pi, Fintype.card_fin, Module.finrank_matrix, Module.finrank_self,
      mul_one] at h
    omega
  have hinf : LinearMap.ker (rowSum m) ⊓ (ℝ ∙ S0) = ⊥ := by
    rw [Submodule.eq_bot_iff]
    rintro M ⟨hM1, hM2⟩
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hM2
    have : rowSum m (c • S0) = 0 := hM1
    have hc : c = 0 := by
      have := congrFun this z
      rw [map_smul] at this
      simp only [Pi.smul_apply, rowSum_apply, Pi.zero_apply, smul_eq_mul] at this
      rw [hS0trans.2 z] at this
      simpa using this
    simp [hc]
  have hline : Module.finrank ℝ (ℝ ∙ S0 : Submodule ℝ (Matrix (Fin m) (Fin m) ℝ)) = 1 := by
    apply finrank_span_singleton
    intro h
    have := congrFun (congrFun h z) z
    simp [hS0] at this
  have hsup := Submodule.finrank_sup_add_finrank_inf_eq
    (LinearMap.ker (rowSum m)) (ℝ ∙ S0)
  rw [hinf, finrank_bot, hline, ← hTeq] at hsup
  rw [pow_two]
  omega
