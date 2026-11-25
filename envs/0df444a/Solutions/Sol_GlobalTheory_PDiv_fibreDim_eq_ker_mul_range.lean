-- Prove2me | solution 1 for GlobalTheory.PDiv.fibreDim_eq_ker_mul_range
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:53:37.955865+00:00
-- url     : https://prove2.me/submissions/12b521bf-77ff-4428-8b21-58ac90e97819

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_KerIdealCompOfSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PointsGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsSpanEqTopOfFinrankFibreEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KerCounitAlgHomBaseChangeField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FinrankDualAndRangeDualMapBaseChange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SubsingletonOfResidueFieldFibres
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_FibreRankCompOfSurjective
import Theorems.Thm_GlobalTheory_PDiv_finrank_eq_ker_mul_range
import Theorems.Thm_GlobalTheory_hopf_order_formula_fibre


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
namespace GlobalTheory.PDiv
theorem _root_.solution (f : B →ₐc[O] A) (q : PrimeSpectrum O) :
    fibreDim A q = fibreDim (A ⧸ kerIdeal f) q * fibreRank (f : B →ₐ[O] A).toLinearMap q :=
  GlobalTheory.hopf_order_formula_fibre finrank_eq_ker_mul_range O A B _ f
end GlobalTheory.PDiv
