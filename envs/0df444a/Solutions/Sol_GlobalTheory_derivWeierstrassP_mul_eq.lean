-- Prove2me | solution 1 for GlobalTheory.derivWeierstrassP_mul_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:15:26.791271+00:00
-- url     : https://prove2.me/submissions/0d5599bf-eade-4d8a-b436-04cfa6940fad

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsVariableChangeEqLatticeCurve
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_WeierstrassCurvePointOfLatticeAddOfGeneric
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsNumeratorOfInvolution
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsMulEqPolynomialWeierstrassP
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_AddMonoidHomEqZeroOfEventually
import Theorems.Thm_GlobalTheory_latticeIsogeny_latticePoint
import Theorems.Thm_GlobalTheory_eventually_notMem_periodLattice
import Theorems.Thm_GlobalTheory_hasDerivAt_weierstrassP
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
theorem _root_.solution (hα : ∀ l ∈ L.lattice, α * l ∈ L'.lattice) {A D : ℂ[X]}
    (h : ∀ z, α * z ∉ L'.lattice → ℘[L'] (α * z) = A.eval (℘[L] z) / D.eval (℘[L] z))
    {z : ℂ} (hz : α * z ∉ L'.lattice) (hD : D.eval (℘[L] z) ≠ 0) :
    α * ℘'[L'] (α * z) =
      (derivative A * D - A * derivative D).eval (℘[L] z) / D.eval (℘[L] z) ^ 2 * ℘'[L] z := by
  have d := hasDerivAt_weierstrassP L (z := z) fun h ↦ hz (hα z h)
  have d1 := (hasDerivAt_weierstrassP L' hz).comp z ((hasDerivAt_id z).const_mul α)
  have d2 := ((A.hasDerivAt _).comp z d).div ((D.hasDerivAt _).comp z d) hD
  have := d1.unique (d2.congr_of_eventuallyEq (by
    filter_upwards [(continuous_const_mul α).continuousAt.eventually
      (eventually_notMem_periodLattice L' hz)] with w hw using h w hw))
  simp only [Function.comp_apply, mul_one] at this
  rw [mul_comm, this]
  simp only [eval_sub, eval_mul]
  ring
end GlobalTheory
