-- Prove2me | solution 1 for GlobalTheory.card_ker_latticeIsogeny
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:15:33.264058+00:00
-- url     : https://prove2.me/submissions/fef155b9-19f8-4395-b084-cf3336160fee

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsVariableChangeEqLatticeCurve
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_WeierstrassCurvePointOfLatticeAddOfGeneric
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsNumeratorOfInvolution
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsMulEqPolynomialWeierstrassP
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_AddMonoidHomEqZeroOfEventually
import Theorems.Thm_GlobalTheory_latticeIsogeny_latticePoint
import Theorems.Thm_GlobalTheory_latticePointEquiv_mk
import Theorems.Thm_GlobalTheory_latticePoint_eq_iff
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
theorem _root_.solution (hα0 : α ≠ 0) (hα : ∀ l ∈ L.lattice, α * l ∈ L'.lattice) :
    Nat.card (latticeIsogeny α hα).ker =
      (L.lattice.toAddSubgroup.map (AddMonoidHom.mulLeft α)).relIndex
        L'.lattice.toAddSubgroup := by
  have h1 : (latticeIsogeny α hα).ker =
      (L'.lattice.toAddSubgroup.comap (AddMonoidHom.mulLeft α)).map (latticePointHom L) := by
    ext P
    obtain ⟨z, rfl⟩ := latticePoint_surjective L P
    rw [AddMonoidHom.mem_ker, latticeIsogeny_latticePoint, latticePoint_eq_zero_iff]
    refine ⟨fun h ↦ ⟨z, h, rfl⟩, ?_⟩
    rintro ⟨w, hw, e⟩
    have hw' : α * w ∈ L'.lattice := hw
    simpa [mul_sub] using sub_mem hw' (hα _ ((latticePoint_eq_iff L).mp e))
  have h2 : (L'.lattice.toAddSubgroup.comap (AddMonoidHom.mulLeft α)).map
      (AddMonoidHom.mulLeft α) = L'.lattice.toAddSubgroup :=
    AddSubgroup.map_comap_eq_self_of_surjective (mul_left_surjective₀ hα0) _
  rw [h1, ← AddSubgroup.relIndex_ker, ker_latticePointHom,
    ← AddSubgroup.relIndex_map_map_of_injective (f := AddMonoidHom.mulLeft α) _ _
      (mul_right_injective₀ hα0), h2]
end GlobalTheory
