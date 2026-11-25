-- Prove2me | solution 1 for GlobalTheory.PDiv.map_torsionIdeal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:02:09.477028+00:00
-- url     : https://prove2.me/submissions/ced6cbb8-0d88-4910-bf79-22930b719cd9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_MemPrimitiveTensorsIffIsPrimitiveElem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_FinrankOfIsStandardSmoothOfRelativeDimension
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_KerIdealCompOfSurjective
import Theorems.Thm_GlobalTheory_PDiv_comp_mulBy
import Theorems.Thm_GlobalTheory_PDiv_mulBy_comp
import Theorems.Thm_GlobalTheory_PDiv_kerIdeal_comp
import Theorems.Thm_GlobalTheory_PDiv_kerIdeal_comp_of_surjective
import Theorems.Thm_GlobalTheory_IsBicharacter_map


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
theorem _root_.solution [IsCocomm R C] [IsCocomm R A] {f : C →ₐc[R] A}
    (hf : Function.Surjective f) (n : ℕ) :
    Ideal.map (f : C →ₐ[R] A) (torsionIdeal R C n) = torsionIdeal R A n := by
  rw [← kerIdeal_comp, comp_mulBy, ← mulBy_comp, kerIdeal_comp_of_surjective _ hf]
end GlobalTheory.PDiv
