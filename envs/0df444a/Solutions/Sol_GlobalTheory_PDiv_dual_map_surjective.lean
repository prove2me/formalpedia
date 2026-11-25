-- Prove2me | solution 1 for GlobalTheory.PDiv.dual_map_surjective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:05:12.229136+00:00
-- url     : https://prove2.me/submissions/30336b5e-f688-4476-9a65-3bbc70d954d7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_KerIdealCompOfSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PointsGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsSpanEqTopOfFinrankFibreEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KerCounitAlgHomBaseChangeField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FinrankDualAndRangeDualMapBaseChange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SubsingletonOfResidueFieldFibres
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_FibreRankCompOfSurjective
import Theorems.Thm_GlobalTheory_PDiv_fibreDim_dual
import Theorems.Thm_GlobalTheory_PDiv_fibreRank_transpose
import Theorems.Thm_GlobalTheory_PDiv_fibreDim_eq_ker_mul_range
import Theorems.Thm_GlobalTheory_PDiv_fibreDim_ne_zero
import Theorems.Thm_GlobalTheory_IsBicharacter_map
import Theorems.Thm_GlobalTheory_surjective_injective_of_fibre_rank


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open TensorProduct Coalgebra Bialgebra WithConv Module
open GlobalTheory GlobalTheory.PDiv
variable {O : Type} [CommRing O]
variable {A B : Type} [CommRing A] [CommRing B] [HopfAlgebra O A] [HopfAlgebra O B]
  [Module.Finite O A]
variable [Module.Projective O A] [Module.Finite O B] [Module.Projective O B]
namespace GlobalTheory.PDiv
theorem _root_.solution (f : B →ₐc[O] A)
    (h : ∀ q : PrimeSpectrum O, fibreDim A q = fibreDim (A ⧸ kerIdeal f) q * fibreDim B q) :
    Function.Surjective (CartierDual.map f) := by
  refine (GlobalTheory.surjective_injective_of_fibre_rank O _ _ (CartierDual.transpose (f : B →ₐ[O] A).toLinearMap)).1 fun q => ?_
  refine (fibreRank_transpose _ q).trans (Eq.trans ?_ (fibreDim_dual q).symm)
  have h1 := fibreDim_eq_ker_mul_range f q
  have h2 : fibreDim (A ⧸ kerIdeal f) q ≠ 0 := fun h0 =>
    fibreDim_ne_zero (A := A) q (by rw [h1, h0, zero_mul])
  exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero h2) (h1.symm.trans (h q))
end GlobalTheory.PDiv
