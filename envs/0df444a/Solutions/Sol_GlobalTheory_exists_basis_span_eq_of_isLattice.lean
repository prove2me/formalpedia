-- Prove2me | solution 1 for GlobalTheory.exists_basis_span_eq_of_isLattice
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:46:49.234894+00:00
-- url     : https://prove2.me/submissions/78a530f4-3f0e-434f-882a-6f71b08a01b0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FiniteAndNcardSetOfSubmoduleLeRelIndexEqLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_RelIndexDualSubmoduleInfOfSelfDual

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module
open GlobalTheory
variable {V : Type*} [AddCommGroup V] [Module ℚ V]
variable [FiniteDimensional ℚ V]
namespace GlobalTheory
theorem _root_.solution (L : Submodule ℤ V) [L.IsLattice ℚ] :
    ∃ b : Basis (Fin (finrank ℚ V)) ℚ V, L = Submodule.span ℤ (Set.range b) := by
  have hr : finrank ℤ L = finrank ℚ V := by
    let b := Module.Free.chooseBasis ℤ L
    rw [finrank_eq_card_basis b, finrank_eq_card_basis (b.extendOfIsLattice ℚ)]
  let b := Module.finBasisOfFinrankEq ℤ L hr
  refine ⟨b.extendOfIsLattice ℚ, ?_⟩
  have h1 : Set.range (b.extendOfIsLattice ℚ) = L.subtype '' Set.range b := by
    rw [← Set.range_comp]
    congr 1
    exact funext fun i => b.extendOfIsLattice_apply ℚ i
  rw [h1, ← Submodule.map_span, b.span_eq, Submodule.map_subtype_top]
end GlobalTheory
