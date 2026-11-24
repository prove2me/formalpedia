-- Prove2me | solution 1 for GlobalTheory.IrreducibleGeneralizations.component_eq_closure
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T18:08:38.492021+00:00
-- url     : https://prove2.me/submissions/cf6ecd20-a468-4c88-b4db-043203c2ab15

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsIrreducibleGeneralizations
import Theorems.Thm_GlobalTheory_IrreducibleGeneralizations_isIrreducible_generalizations

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u_1
open GlobalTheory GlobalTheory.IrreducibleGeneralizations
open AlgebraicGeometry Topology
namespace GlobalTheory.IrreducibleGeneralizations
theorem _root_.solution {X : Scheme.{u_1}} {x : X} [IsDomain (X.presheaf.stalk x)]
    {Z : Set X} (hZ : Z ∈ irreducibleComponents X) (hx : x ∈ Z) :
    Z = closure {y : X | y ⤳ x} := by

  obtain ⟨η, hη⟩ := QuasiSober.sober hZ.1 (isClosed_of_mem_irreducibleComponents Z hZ)
  have hsub : Z ⊆ closure {y : X | y ⤳ x} := fun z hz =>
    closure_mono (Set.singleton_subset_iff.mpr (hη.specializes hx)) (hη.specializes hz).mem_closure
  exact hsub.antisymm (hZ.2 (isIrreducible_generalizations x).closure hsub)
end GlobalTheory.IrreducibleGeneralizations
