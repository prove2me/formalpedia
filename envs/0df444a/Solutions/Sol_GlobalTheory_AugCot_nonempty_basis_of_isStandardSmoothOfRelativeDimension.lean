-- Prove2me | solution 1 for GlobalTheory.AugCot.nonempty_basis_of_isStandardSmoothOfRelativeDimension
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:46:32.589405+00:00
-- url     : https://prove2.me/submissions/168f6c96-7806-43ec-ba2e-5a19343ffff9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_FinrankOfIsStandardSmoothOfRelativeDimension
import Theorems.Thm_GlobalTheory_AugCot_finrank_of_isStandardSmoothOfRelativeDimension

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct
noncomputable section
open GlobalTheory
open GlobalTheory.AugCot
variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] (ε : A →ₐ[R] R)
namespace GlobalTheory.AugCot
theorem _root_.solution (n : ℕ)
    [Algebra.IsStandardSmoothOfRelativeDimension n R A] :
    Nonempty (Module.Basis (Fin n) R (AugCot ε)) := by
  haveI := Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth n (R := R) (S := A)
  cases subsingleton_or_nontrivial R
  · haveI := Module.subsingleton R (AugCot ε)
    exact ⟨⟨LinearEquiv.ofSubsingleton _ _⟩⟩
  · exact ⟨Module.finBasisOfFinrankEq _ _ (finrank_of_isStandardSmoothOfRelativeDimension ε n)⟩
end GlobalTheory.AugCot
