-- Prove2me | solution 1 for GlobalTheory.UnRep.NormOne.val_le_of_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:57:07.243644+00:00
-- url     : https://prove2.me/submissions/c956c98b-e65d-4fc9-9b1f-8c67708dcc9b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_IsHermForm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ValuationEqOneOfNormOneOfNotMoved
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsDenominatorPrimesPrescribed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_NormOneApproximationAtLevelPrimes
import Theorems.Thm_GlobalTheory_UnRep_NormOne_val_eq_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.AdLat GlobalTheory.UnRep
open scoped TensorProduct Matrix
open GlobalTheory GlobalTheory.UnRep GlobalTheory.UnRep.NormOne
variable {E : Type} [Field E] [NumberField E]
namespace GlobalTheory.UnRep.NormOne
theorem _root_.solution (P : HeightOneSpectrum (𝓞 E)) (x y : E) (d : 𝓞 E) (hd : d ∉ P.asIdeal)
    (h : x * d = y) (hy : P.valuation E y ≤ 1) : P.valuation E x ≤ 1 := by
  rw [← h, map_mul, val_eq_one P d hd, mul_one] at hy
  exact hy
end GlobalTheory.UnRep.NormOne
