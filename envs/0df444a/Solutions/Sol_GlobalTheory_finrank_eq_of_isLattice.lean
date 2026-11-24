-- Prove2me | solution 1 for GlobalTheory.finrank_eq_of_isLattice
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:50:05.409551+00:00
-- url     : https://prove2.me/submissions/406009de-f7ad-4bc5-abc1-55aa57ddcdfd

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
    finrank ℤ L = finrank ℚ V := by
  let b := Module.Free.chooseBasis ℤ L
  rw [finrank_eq_card_basis b, finrank_eq_card_basis (b.extendOfIsLattice ℚ)]
end GlobalTheory
