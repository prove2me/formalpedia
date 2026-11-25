-- Prove2me | solution 1 for GlobalTheory.addMonoidHom_eq_zero_of_eventually
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:15:32.004577+00:00
-- url     : https://prove2.me/submissions/89b7e0e2-8c1a-48e3-bd54-56c9d261835f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsVariableChangeEqLatticeCurve
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_WeierstrassCurvePointOfLatticeAddOfGeneric
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsNumeratorOfInvolution
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsMulEqPolynomialWeierstrassP
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_AddMonoidHomEqZeroOfEventually
import Theorems.Thm_GlobalTheory_latticeIsogeny_latticePoint
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
theorem _root_.solution {G : Type*} [AddCommGroup G] (χ : ℂ →+ G) {z₀ : ℂ}
    (h : ∀ᶠ z in 𝓝 z₀, χ z = 0) (z : ℂ) : χ z = 0 := by
  have h1 : Tendsto (fun n : ℕ ↦ z₀ + z / n) atTop (𝓝 z₀) := by
    simpa using (tendsto_const_div_atTop_nhds_zero_nat z).const_add z₀
  obtain ⟨n, hn, hn0⟩ := ((h1.eventually h).and (eventually_gt_atTop 0)).exists
  rw [map_add, h.self_of_nhds, zero_add] at hn
  have : z = n • (z / n) := by
    have : (n : ℂ) ≠ 0 := by exact_mod_cast hn0.ne'
    rw [nsmul_eq_mul]; field_simp
  rw [this, map_nsmul, hn, nsmul_zero]
end GlobalTheory
