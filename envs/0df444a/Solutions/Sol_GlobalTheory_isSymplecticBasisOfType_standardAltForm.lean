-- Prove2me | solution 1 for GlobalTheory.isSymplecticBasisOfType_standardAltForm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:15:37.857204+00:00
-- url     : https://prove2.me/submissions/98199484-9d32-4cae-bf0b-1b2c3264d667

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DualRestrictSurjectiveOfIsTorsionFreeQuotient

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module Function
open GlobalTheory
variable {R M ι : Type*} [CommRing R] [AddCommGroup M] [Module R M]
namespace GlobalTheory
theorem _root_.solution [Fintype ι] [DecidableEq ι] (d : ι → R) :
    IsSymplecticBasisOfType (standardAltForm d) (Pi.basisFun R (ι ⊕ ι)) d := by
  refine ⟨fun i j => ?_, fun i j => ?_, fun i => ?_, fun i j hij => ?_⟩
  · simp [standardAltForm, Matrix.toBilin'_single]
  · simp [standardAltForm, Matrix.toBilin'_single]
  · simp [standardAltForm, Matrix.toBilin'_single]
  · simp [standardAltForm, Matrix.toBilin'_single, hij]
end GlobalTheory
