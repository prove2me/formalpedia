-- Prove2me | solution 1 for John.exists_johnPosition
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:09:17.830729+00:00
-- url     : https://prove2.me/submissions/279b8ed8-cf6d-4abf-b057-83dac054fd9a

module
public import Definitions.Def_BasicResults_Determinant
public import Definitions.Def_BasicResults_CompactConvexHull
public import Definitions.Def_BasicResults_JohnIngredients
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.InnerProductSpace.Spectrum
public import Mathlib.Analysis.InnerProductSpace.Trace
public import Mathlib.Analysis.LocallyConvex.Separation
public import Mathlib.Analysis.Normed.Group.Quotient
public import Mathlib.Analysis.Normed.Module.DoubleDual
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.Normed.Module.HahnBanach
public import Mathlib.Analysis.Seminorm
public import Mathlib.Topology.Order.Compact
public import Definitions.Def_BasicResults_John
public import Theorems.Thm_John_exists_maxVolume

set_option autoImplicit true
@[expose] public section
public section
universe u
open scoped InnerProductSpace ComplexConjugate
open RCLike (re)
open John
variable {𝕜 : Type u} [RCLike 𝕜] {k : ℕ}
namespace John
theorem _root_.solution {W : Type u} [NormedAddCommGroup W] [NormedSpace 𝕜 W]
    (hk : 0 < k) (L : EuclideanSpace 𝕜 (Fin k) ≃L[𝕜] W) :
    ∃ (M : EuclideanSpace 𝕜 (Fin k) ≃L[𝕜] W)
      (q : Seminorm 𝕜 (EuclideanSpace 𝕜 (Fin k))),
      Continuous q ∧ (∀ u, q u ≤ ‖u‖) ∧ (∀ S ∈ Feasible q, ‖S.det‖ ≤ 1) ∧
      ∀ z, ‖M z‖ = q z := by
  classical
  -- the body seminorm `p x = ‖L x‖`, equivalent to the Euclidean norm
  set p : Seminorm 𝕜 (EuclideanSpace 𝕜 (Fin k)) :=
    (normSeminorm 𝕜 W).comp (L : EuclideanSpace 𝕜 (Fin k) →L[𝕜] W).toLinearMap with hpdef
  have hp_apply : ∀ x, p x = ‖L x‖ := fun x => by
    simp only [hpdef, Seminorm.comp_apply, coe_normSeminorm, ContinuousLinearMap.coe_coe,
      ContinuousLinearEquiv.coe_coe]
  have hpc : Continuous p := by
    refine (continuous_norm.comp L.continuous).congr fun x => ?_
    exact (hp_apply x).symm
  -- upper bound `p x ≤ ‖L‖ ‖x‖`
  have hup : ∀ x, p x ≤ ‖(L : EuclideanSpace 𝕜 (Fin k) →L[𝕜] W)‖ * ‖x‖ := fun x => by
    rw [hp_apply]
    exact (L : EuclideanSpace 𝕜 (Fin k) →L[𝕜] W).le_opNorm x
  -- lower bound `‖L.symm‖⁻¹ ‖x‖ ≤ p x`; the constant is positive since `0 < k`
  set D : ℝ := ‖(L.symm : W →L[𝕜] EuclideanSpace 𝕜 (Fin k))‖ with hD
  have hDpos : 0 < D := by
    have hne : (L.symm : W →L[𝕜] EuclideanSpace 𝕜 (Fin k)) ≠ 0 := by
      intro hzero
      have he1 : ‖(EuclideanSpace.single (⟨0, hk⟩ : Fin k) (1 : 𝕜))‖ = 1 := by
        rw [PiLp.norm_single, norm_one]
      have hcontra : (EuclideanSpace.single (⟨0, hk⟩ : Fin k) (1 : 𝕜)) = 0 := by
        have h2 : (L.symm : W →L[𝕜] EuclideanSpace 𝕜 (Fin k))
            (L (EuclideanSpace.single (⟨0, hk⟩ : Fin k) (1 : 𝕜))) = 0 := by
          rw [hzero]; rfl
        rwa [ContinuousLinearEquiv.coe_coe, L.symm_apply_apply] at h2
      rw [hcontra, norm_zero] at he1
      exact one_ne_zero he1.symm
    rw [hD]
    rcases eq_or_lt_of_le (norm_nonneg (L.symm : W →L[𝕜] EuclideanSpace 𝕜 (Fin k))) with h | h
    · exact absurd ((ContinuousLinearMap.opNorm_zero_iff _).mp h.symm) hne
    · exact h
  have hlo : ∀ x, D⁻¹ * ‖x‖ ≤ p x := fun x => by
    have hbound : ‖x‖ ≤ D * p x := by
      rw [hp_apply]
      have e : ‖x‖ = ‖(L.symm : W →L[𝕜] EuclideanSpace 𝕜 (Fin k)) (L x)‖ := by
        rw [ContinuousLinearEquiv.coe_coe, L.symm_apply_apply]
      rw [e]
      exact (L.symm : W →L[𝕜] EuclideanSpace 𝕜 (Fin k)).le_opNorm (L x)
    have h2 := mul_le_mul_of_nonneg_left hbound (le_of_lt (inv_pos.mpr hDpos))
    rwa [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hDpos), one_mul] at h2
  -- the maximal-volume ellipsoid `T₀` and the John-position seminorm `q = p ∘ T₀`
  obtain ⟨T₀, hT₀feas, hT₀det, hT₀max⟩ :=
    exists_maxVolume p hpc (inv_pos.mpr hDpos) hlo hup
  set q : Seminorm 𝕜 (EuclideanSpace 𝕜 (Fin k)) := p.comp T₀.toLinearMap with hqdef
  have hq1 : ∀ u, q u ≤ ‖u‖ := fun u => by
    rw [hqdef, Seminorm.comp_apply]; exact hT₀feas u
  have hqc : Continuous q := by
    rw [hqdef]; exact hpc.comp T₀.continuous
  have hqmax : ∀ S ∈ Feasible q, ‖S.det‖ ≤ 1 := fun S hS => by
    have hTS : T₀.comp S ∈ Feasible p := fun u => by
      have h := hS u
      rw [hqdef, Seminorm.comp_apply, ContinuousLinearMap.coe_coe] at h
      simpa [ContinuousLinearMap.comp_apply] using h
    have hdc : (T₀.comp S).det = T₀.det * S.det := by
      simp only [ContinuousLinearMap.det, ContinuousLinearMap.toLinearMap_comp, LinearMap.det_comp]
    have hle := hT₀max (T₀.comp S) hTS
    rw [hdc, norm_mul] at hle
    exact (mul_le_iff_le_one_right (norm_pos_iff.mpr hT₀det)).mp hle
  -- the composite equivalence `M = L ∘ T₀`
  refine ⟨(T₀.toContinuousLinearEquivOfDetNeZero hT₀det).trans L, q, hqc, hq1, hqmax,
    fun z => ?_⟩
  rw [ContinuousLinearEquiv.trans_apply,
    ContinuousLinearMap.toContinuousLinearEquivOfDetNeZero_apply, hqdef,
    Seminorm.comp_apply, ContinuousLinearMap.coe_coe, hp_apply]
end John
