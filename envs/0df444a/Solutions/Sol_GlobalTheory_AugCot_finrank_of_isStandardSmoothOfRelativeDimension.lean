-- Prove2me | solution 1 for GlobalTheory.AugCot.finrank_of_isStandardSmoothOfRelativeDimension
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:29:56.544348+00:00
-- url     : https://prove2.me/submissions/9d97c368-8de6-405d-86d8-500079a2c257

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_FinrankOfIsStandardSmoothOfRelativeDimension
import Theorems.Thm_GlobalTheory_AugCot_finrank_eq_of_free
import Theorems.Thm_GlobalTheory_AugCot_finrank_kaehler_of_isStandardSmoothOfRelativeDimension

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
theorem _root_.solution [Nontrivial R] (n : ℕ)
    [Algebra.IsStandardSmoothOfRelativeDimension n R A] : Module.finrank R (AugCot ε) = n := by
  haveI := Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth n (R := R) (S := A)
  haveI : Nontrivial A := (ε : A →+* R).domain_nontrivial
  rw [finrank_eq_of_free, finrank_kaehler_of_isStandardSmoothOfRelativeDimension n]
end GlobalTheory.AugCot
