-- Prove2me | solution 1 for GlobalTheory.T.piExteriorTensor_flattenedIndex_equiv_nested
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T04:34:12.517601+00:00
-- url     : https://prove2.me/submissions/12dd706c-c0d7-48f4-813b-2f92f60aa90b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_PiExteriorTensorFlattenedIndexEquivNested
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsSubquotientOfEquiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_PiExteriorTensorFlattenedIndexEquivNestedStatement
import Theorems.Thm_GlobalTheory_JacStages_piTensor_flatHom_equiv
import Theorems.Thm_GlobalTheory_SmGL_IsSmoothChar_comp


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.JacStages
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (s : ℕ) (t : Fin s → ℕ) (Γ : ∀ a, Fin (t a) → Type) [∀ a b, Group (Γ a b)]
    (Y : ∀ a, Fin (t a) → Type) [∀ a b, AddCommGroup (Y a b)] [∀ a b, Module ℂ (Y a b)]
    (ρ : ∀ a b, Representation ℂ (Γ a b) (Y a b)),
    Nonempty (Representation.Equiv ((piTensor fun c : Fin (∑ a, t a) =>
        ρ (finSigmaFinEquiv.symm c).1 (finSigmaFinEquiv.symm c).2).comp (flatHom Γ))
      (piTensor fun a => piTensor (ρ a))) := by
  first | exact @GlobalTheory.JacStages.piTensor_flatHom_equiv | exact GlobalTheory.JacStages.piTensor_flatHom_equiv | (intros; apply GlobalTheory.JacStages.piTensor_flatHom_equiv <;> assumption)
end _root_.GlobalTheory.T
