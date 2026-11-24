-- Prove2me | solution 1 for GlobalTheory.PDiv.torsionIdeal_le_ker_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:47:51.116199+00:00
-- url     : https://prove2.me/submissions/14044c62-9965-477d-bf22-d9c62e48f963

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_MemPrimitiveTensorsIffIsPrimitiveElem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_FinrankOfIsStandardSmoothOfRelativeDimension
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_KerIdealCompOfSurjective
import Theorems.Thm_GlobalTheory_PDiv_comp_mulBy_pts
import Theorems.Thm_GlobalTheory_PDiv_kerIdeal_le_ker_iff

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
theorem _root_.solution [IsCocomm R A] (n : ℕ) {E : Type*} [CommRing E] [Algebra R E]
    (x : A →ₐ[R] E) : torsionIdeal R A n ≤ RingHom.ker x ↔ toConv x ^ n = 1 := by
  rw [kerIdeal_le_ker_iff]
  have h := comp_mulBy_pts x n
  constructor
  · intro h'
    refine ofConv_injective (h.symm.trans (AlgHom.ext h'))
  · intro h' c
    rw [h'] at h
    exact DFunLike.congr_fun h c
end GlobalTheory.PDiv
