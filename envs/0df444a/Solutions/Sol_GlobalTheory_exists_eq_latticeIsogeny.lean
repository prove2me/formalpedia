-- Prove2me | solution 1 for GlobalTheory.exists_eq_latticeIsogeny
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:34:19.346464+00:00
-- url     : https://prove2.me/submissions/0de1cfcb-d909-485a-81f6-03ed6b18158f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsVariableChangeEqLatticeCurve
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_WeierstrassCurvePointOfLatticeAddOfGeneric
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsNumeratorOfInvolution
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsMulEqPolynomialWeierstrassP
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_AddMonoidHomEqZeroOfEventually
import Theorems.Thm_GlobalTheory_latticeIsogeny_latticePoint
import Theorems.Thm_GlobalTheory_exists_eq_latticePoint_mul
import Theorems.Thm_GlobalTheory_eventually_notMem_periodLattice
import Theorems.Thm_GlobalTheory_exists_weierstrassP_eq
import Theorems.Thm_GlobalTheory_latticePointEquiv_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.latticePointEquiv_mk


attribute [local simp] GlobalTheory.latticeIsogeny_latticePoint

set_option autoImplicit false
open Filter PeriodPair Polynomial WeierstrassCurve UpperHalfPlane
open scoped Topology
noncomputable section
open GlobalTheory
variable {L L' : PeriodPair} {α : ℂ}
namespace GlobalTheory
theorem _root_.solution
    (φ : (latticeCurve L).toAffine.Point →+ (latticeCurve L').toAffine.Point) (A B D : ℂ[X])
    (hD : D ≠ 0) (hφ : ∀ x y h, D.eval x ≠ 0 →
      ∃ y' h', φ (.some x y h) = .some ((A.eval x + B.eval x * y) / D.eval x) y' h') :
    ∃ (α : ℂ) (hα : ∀ l ∈ L.lattice, α * l ∈ L'.lattice), α ≠ 0 ∧ φ = latticeIsogeny α hα := by
  obtain ⟨x₀, hx₀⟩ : ∃ x, D.eval x ≠ 0 := by
    by_contra! hc
    exact hD (Polynomial.funext (by simpa using hc))
  obtain ⟨z₀, hz₀, rfl⟩ := exists_weierstrassP_eq L x₀
  have hP := L.analyticOnNhd_weierstrassP z₀ hz₀
  have hP' := L.analyticOnNhd_derivWeierstrassP z₀ hz₀
  have hp : ∀ Q : ℂ[X], AnalyticAt ℂ (fun z ↦ Q.eval (℘[L] z)) z₀ := fun Q ↦
    (Q.differentiable.analyticAt _).comp hP
  obtain ⟨α, hα⟩ := exists_eq_latticePoint_mul (φ.comp (latticePointHom L)) (z₀ := z₀)
    (F := fun z ↦ (A.eval (℘[L] z) + B.eval (℘[L] z) * (℘'[L] z / 2)) / D.eval (℘[L] z))
    (((hp A).add ((hp B).mul (by fun_prop (disch := simp)))).div (hp D) hx₀) (by
      filter_upwards [eventually_notMem_periodLattice L hz₀,
        (hp D).continuousAt.eventually_ne hx₀] with z h1 h2
      simpa [latticePoint_of_notMem L h1] using hφ _ _ (latticeCurve_nonsingular L h1) h2)
  simp only [AddMonoidHom.comp_apply, latticePointHom_apply] at hα
  refine ⟨α, fun l hl ↦ ?_, ?_, ?_⟩
  · rw [← latticePoint_eq_zero_iff, ← hα, latticePoint_of_mem L hl, map_zero]
  · rintro rfl
    obtain ⟨y, h', e⟩ := hφ _ _ (latticeCurve_nonsingular L hz₀) hx₀
    rw [← latticePoint_of_notMem L hz₀, hα, latticePoint_of_mem L' (by simp)] at e
    exact Affine.Point.some_ne_zero _ e.symm
  · ext P
    obtain ⟨z, rfl⟩ := latticePoint_surjective L P
    rw [hα, latticeIsogeny_latticePoint]
end GlobalTheory
