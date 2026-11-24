-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.TfLoc.Iw.exists_subgroup
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T14:02:37.43532+00:00
-- url     : https://prove2.me/submissions/22a0867e-1746-4b6f-a7f5-6f4f585ef34d

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_TwistedFactors_IntegralUnitBaseChange_Development
import Definitions.Def_GroundTheory_LocalFields_Integers
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IwahoriFactorization
import Theorems.Thm_GlobalTheory_CompanionTheory_TfLoc_Iw_iwahori_mul
import Theorems.Thm_GlobalTheory_CompanionTheory_TfLoc_Iw_iwahori_inv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel PositivityTheory.Rg.Tf.Loc Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.TfLoc GlobalTheory.CompanionTheory.TfLoc.Iw
variable {F : Type*} [Field F] [ValuativeRel F] {m : ℕ}
namespace GlobalTheory.CompanionTheory.TfLoc.Iw
theorem _root_.solution : ∃ U : Subgroup (GL (Fin m) F), (U : Set (GL (Fin m) F)) = iwahori (m := m) F :=
  ⟨{ carrier := iwahori (m := m) F
     mul_mem' := iwahori_mul
     one_mem' := ⟨one_mem _, fun i j hij => by
       rw [Units.val_one, Matrix.one_apply_ne (ne_of_gt hij)]; simp⟩
     inv_mem' := iwahori_inv }, rfl⟩
end GlobalTheory.CompanionTheory.TfLoc.Iw
