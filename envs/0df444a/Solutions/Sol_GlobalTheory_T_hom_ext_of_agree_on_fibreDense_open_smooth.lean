-- Prove2me | solution 1 for GlobalTheory.T.hom_ext_of_agree_on_fibreDense_open_smooth
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:47:31.560164+00:00
-- url     : https://prove2.me/submissions/7bf2ae34-757d-40b3-ba1a-4f1f480e0dbd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HomExtOfAgreeOnFibreDenseOpenSmooth
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HomExtOfAgreeOnFibreDenseOpenSmoothStatement
import Theorems.Thm_GlobalTheory_FibreDense_main
import Theorems.Thm_GlobalTheory_IrreducibleGeneralizations_main


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (X T Y : Scheme.{0}) (p : X ⟶ T) [Smooth p] (q : Y ⟶ T) [IsSeparated q] (W : X.Opens), (∀ x : X, x ∈ closure ((W : Set X) ∩ p ⁻¹' {p x})) → ∀ f g : X ⟶ Y, f ≫ q = g ≫ q → W.ι ≫ f = W.ι ≫ g → f = g := by
  first | exact @GlobalTheory.FibreDense.main | exact GlobalTheory.FibreDense.main | (intros; apply GlobalTheory.FibreDense.main <;> assumption)
end _root_.GlobalTheory.T
