-- Prove2me | solution 1 for GlobalTheory.T.weylRowAction_mem_weylLattice_square
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:34:40.440069+00:00
-- url     : https://prove2.me/submissions/c14be35a-ee15-437f-b687-00f8ba09fa5d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_WeylRowActionMemWeylLatticeSquare
import Mathlib
import Definitions.Def_Formalism_GradedWeylDivisibility_DualWeylDominanceOf
import Definitions.Def_Formalism_SatakeDualWeyl_KpqSubgroupCompact
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LClosedeqLemmas
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_WeylRowActionMemWeylLatticeSquareStatement
import Theorems.Thm_Formalism_UG_Final_KpqSubgroupCompact
import Theorems.Thm_GlobalTheory_WeylRowAll_rowAct_mem_weyl_square


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (R : Type) [CommRing R] (n : ℕ) (ν : Fin n → ℕ), Antitone ν → ∀ (M : Matrix (Fin n) (Fin n) R), ∀ f ∈ Formalism.GradedWeylDivisibility.weyl R n n le_rfl ν, Formalism.GradedWeylDivisibility.rowAct R M f ∈ Formalism.GradedWeylDivisibility.weyl R n n le_rfl ν := by
  first | exact @GlobalTheory.WeylRowAll.rowAct_mem_weyl_square | exact GlobalTheory.WeylRowAll.rowAct_mem_weyl_square | (intros; apply GlobalTheory.WeylRowAll.rowAct_mem_weyl_square <;> assumption)
end _root_.GlobalTheory.T
