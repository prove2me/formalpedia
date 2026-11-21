-- Prove2me | solution 1 for MasulloGRH.traceNorm_le_nuclear_series
-- status  : ACCEPTED   (prove)
-- author  : @marozols
-- created : 2026-11-20T23:08:52.187663+00:00
-- url     : https://prove2.me/submissions/73f9b1df-efad-4028-a33c-c89edb48bd97

import Theorems.Thm_MasulloGRH_operatorTrace_of_nuclear_series

open MasulloGRH
open scoped ComplexOrder

private theorem factor_abs_by_contraction {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (T : H →L[ℂ] H) :
    ∃ R : H →L[ℂ] H, (∀ z, ‖R z‖ ≤ ‖z‖) ∧ ∀ z, R (T z) = operatorAbs T z := by
  let A := operatorAbs T
  have hprod : star A * A = star T * T := by
    change star (CFC.sqrt (star T * T)) * CFC.sqrt (star T * T) = _
    rw [(CFC.sqrt_nonneg _).star_eq, CFC.sqrt_mul_sqrt_self _]
  have hnorm (z : H) : ‖A z‖ = ‖T z‖ := by
    rw [A.apply_norm_eq_sqrt_inner_adjoint_left, T.apply_norm_eq_sqrt_inner_adjoint_left]
    change Real.sqrt (inner ℂ ((star A * A) z) z).re = Real.sqrt (inner ℂ ((star T * T) z) z).re
    rw [hprod]
  let M := (LinearMap.range T.toLinearMap).topologicalClosure
  let e : H →ₗ[ℂ] M := T.toLinearMap.codRestrict M fun z =>
    Submodule.le_topologicalClosure _ (LinearMap.mem_range_self _ z)
  have hd : DenseRange e := by
    exact ((denseRange_inclusion_iff subset_closure).2 Set.Subset.rfl).comp
      (Set.rangeFactorization_surjective (f := (T : H → H))).denseRange
      (continuous_inclusion subset_closure)
  have hb (z : H) : ‖A.toLinearMap z‖ ≤ 1 * ‖e z‖ := by simpa [e] using (hnorm z).le
  let Q := A.toLinearMap.extendOfNorm e
  let : CompleteSpace M := (Submodule.isClosed_topologicalClosure _).isComplete.completeSpace_coe
  refine ⟨Q.comp M.orthogonalProjectionOnto, ?_, ?_⟩
  · intro z
    change ‖Q (M.orthogonalProjectionOnto z)‖ ≤ ‖z‖
    calc
      _ ≤ 1 * ‖M.orthogonalProjectionOnto z‖ := LinearMap.norm_extendOfNorm_apply_le hd 1 hb _
      _ ≤ ‖z‖ := by simpa only [one_mul] using M.norm_orthogonalProjectionOnto_apply_le z
  · intro z
    change Q (M.orthogonalProjectionOnto ((e z : M) : H)) = A z
    rw [M.orthogonalProjectionOnto_mem_subspace_eq_self]
    exact LinearMap.extendOfNorm_eq hd ⟨1, hb⟩ z

theorem solution {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (T : H →L[ℂ] H) (x y : ℕ → H) (hs : Summable (fun m => ‖x m‖ * ‖y m‖))
    (hxy : ∀ u : H, HasSum (fun m => inner ℂ (x m) u • y m) (T u)) :
    traceNorm T ≤ ∑' m, ‖x m‖ * ‖y m‖ := by
  obtain ⟨R, hle, hRT⟩ := factor_abs_by_contraction T
  have hcost (m : ℕ) : ‖x m‖ * ‖R (y m)‖ ≤ ‖x m‖ * ‖y m‖ :=
    mul_le_mul_of_nonneg_left (hle _) (norm_nonneg _)
  have hs' := hs.of_nonneg_of_le (fun m => mul_nonneg (norm_nonneg (x m)) (norm_nonneg (R (y m)))) hcost
  have hrep (u : H) : HasSum (fun m => inner ℂ (x m) u • R (y m)) (operatorAbs T u) := by
    simpa only [map_smul, hRT] using (hxy u).mapL R
  have hbound (m : ℕ) : ‖inner ℂ (x m) (R (y m))‖ ≤ ‖x m‖ * ‖y m‖ :=
    (norm_inner_le_norm _ _).trans (hcost m)
  have hnorms := hs.of_nonneg_of_le (fun m => norm_nonneg (inner ℂ (x m) (R (y m)))) hbound
  unfold traceNorm
  rw [operatorTrace_of_nuclear_series _ x (fun m => R (y m)) hs' hrep]
  exact (Complex.re_le_norm _).trans ((norm_tsum_le_tsum_norm hnorms).trans (hnorms.tsum_le_tsum hbound hs))
