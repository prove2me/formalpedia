-- Prove2me | solution 1 for GlobalTheory.AugCot.nonempty_basis_of_locally
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T13:20:13.602896+00:00
-- url     : https://prove2.me/submissions/f99ebf01-d50f-4b80-9d50-88f0537990ce

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_FinrankOfIsStandardSmoothOfRelativeDimension
import Theorems.Thm_GlobalTheory_AugCot_smooth_of_locally
import Theorems.Thm_GlobalTheory_AugCot_finrank_of_locally

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
universe u
variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A] (ε : A →ₐ[R] R) {n : ℕ}
namespace GlobalTheory.AugCot
theorem _root_.solution [IsLocalRing R]
    (h : RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension n) (algebraMap R A)) :
    Nonempty (Module.Basis (Fin n) R (AugCot ε)) :=
  haveI := smooth_of_locally h
  ⟨Module.finBasisOfFinrankEq _ _ (finrank_of_locally ε h)⟩
end GlobalTheory.AugCot
