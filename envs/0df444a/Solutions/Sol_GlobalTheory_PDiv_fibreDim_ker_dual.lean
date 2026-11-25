-- Prove2me | solution 1 for GlobalTheory.PDiv.fibreDim_ker_dual
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:05:13.112329+00:00
-- url     : https://prove2.me/submissions/4305ed76-e6b2-47f7-a73c-255c27c40e09

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
theorem _root_.solution [IsCocomm O A] (g : A →ₐc[O] A) (q : PrimeSpectrum O) :
    fibreDim (CartierDual O A ⧸ kerIdeal (CartierDual.map g)) q =
      fibreDim (A ⧸ kerIdeal g) q := by
  have h1 := fibreDim_eq_ker_mul_range g q
  have h2 := fibreDim_eq_ker_mul_range (CartierDual.map g) q
  have h3 : fibreRank (CartierDual.map g : CartierDual O A →ₐ[O] CartierDual O A).toLinearMap q =
    fibreRank (g : A →ₐ[O] A).toLinearMap q := fibreRank_transpose (g : A →ₐ[O] A).toLinearMap q
  rw [h3, fibreDim_dual, h1] at h2
  have h4 : fibreRank (g : A →ₐ[O] A).toLinearMap q ≠ 0 := fun h0 =>
    fibreDim_ne_zero (A := A) q (by rw [h1, h0, mul_zero])
  exact (Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero h4) h2).symm
end GlobalTheory.PDiv
