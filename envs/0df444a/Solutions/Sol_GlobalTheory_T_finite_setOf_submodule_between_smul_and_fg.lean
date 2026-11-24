-- Prove2me | solution 1 for GlobalTheory.T.finite_setOf_submodule_between_smul_and_fg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:07:26.064418+00:00
-- url     : https://prove2.me/submissions/5059a9ba-1fcd-4623-bf60-6d4291c7f2ae

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FiniteSubmodulesBetweenSmulAndSelf
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FiniteSubmodulesBetweenSmulAndSelfStatement
import Theorems.Thm_GlobalTheory_finite_submodules_between_smul_and_self


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (O A : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Finite (IsLocalRing.ResidueField O)] [AddCommGroup A] [Module O A] (C : Submodule O A), C.FG → ∀ c : O, c ≠ 0 → {N : Submodule O A | N ≤ C ∧ ∀ x ∈ C, c • x ∈ N}.Finite := by
  first | exact @GlobalTheory.finite_submodules_between_smul_and_self | exact GlobalTheory.finite_submodules_between_smul_and_self | (intros; apply GlobalTheory.finite_submodules_between_smul_and_self <;> assumption)
end _root_.GlobalTheory.T
