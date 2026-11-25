-- Prove2me | solution 1 for GlobalTheory.PDiv.mulBy_groupLike
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:51:40.90604+00:00
-- url     : https://prove2.me/submissions/6946fc7e-d08d-4256-9f6c-a1a88ce1a00c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_MemPrimitiveTensorsIffIsPrimitiveElem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_FinrankOfIsStandardSmoothOfRelativeDimension
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_KerIdealCompOfSurjective
import Theorems.Thm_GlobalTheory_PDiv_convPow_apply_groupLike
import Theorems.Thm_GlobalTheory_PDiv_comp_mulBy_pts

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open TensorProduct Coalgebra Bialgebra WithConv
open GlobalTheory GlobalTheory.PDiv
variable {R A B C D : Type*} [CommRing R] [CommRing A] [CommRing B] [CommRing C] [CommRing D]
variable [Bialgebra R A] [Bialgebra R B] [Bialgebra R C] [Bialgebra R D]
namespace GlobalTheory.PDiv
theorem _root_.solution [IsCocomm R A] (n : ℕ) {u : A} (hu : IsGroupLikeElem R u) :
    mulBy R A n u = u ^ n := by
  have h := DFunLike.congr_fun (comp_mulBy_pts (AlgHom.id R A) n) u
  exact h.trans (convPow_apply_groupLike (toConv (AlgHom.id R A)) hu n)
end GlobalTheory.PDiv
