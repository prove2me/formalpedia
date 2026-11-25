-- Prove2me | solution 1 for GlobalTheory.exists_adicCompletion_ringHom_extend
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T02:53:58.53666+00:00
-- url     : https://prove2.me/submissions/d7c38d10-6133-4be9-9cb8-c1d8e52b0663

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_PowLeComapMapPow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsAbsoluteValueOfIsDiscreteValuationRing
import Theorems.Thm_GlobalTheory_PowerExtensionEvaluation_exists_extension


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open GlobalTheory
universe u
variable {A B : Type*} [CommRing A] [CommRing B]
namespace GlobalTheory
theorem _root_.solution (I : Ideal A) (f : A →+* B)
    [IsAdicComplete (I.map f) B] :
    ∃ g : AdicCompletion I A →+* B, g.comp (algebraMap A _) = f := by
  first
  | exact @_root_.GlobalTheory.PowerExtensionEvaluation.exists_extension
  | exact _root_.GlobalTheory.PowerExtensionEvaluation.exists_extension
  | (apply _root_.GlobalTheory.PowerExtensionEvaluation.exists_extension <;> assumption)
  | (intros; apply _root_.GlobalTheory.PowerExtensionEvaluation.exists_extension <;> assumption)
  | (intros; apply @_root_.GlobalTheory.PowerExtensionEvaluation.exists_extension <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.PowerExtensionEvaluation.exists_extension ..)
end GlobalTheory
