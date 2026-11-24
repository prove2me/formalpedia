-- Prove2me | solution 1 for GlobalTheory.UnRep.NormOne.val_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:45:04.520799+00:00
-- url     : https://prove2.me/submissions/11f27099-5b4d-41ab-8d37-e96be08e89d1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_IsHermForm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ValuationEqOneOfNormOneOfNotMoved
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsDenominatorPrimesPrescribed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_NormOneApproximationAtLevelPrimes

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
theorem _root_.solution (P : HeightOneSpectrum (𝓞 E)) (d : 𝓞 E) (hd : d ∉ P.asIdeal) :
    P.valuation E (d : E) = 1 := by
  have h1 : P.valuation E (algebraMap (𝓞 E) E d) ≤ 1 := P.valuation_le_one d
  have h2 : ¬ P.valuation E (algebraMap (𝓞 E) E d) < 1 := by
    rw [HeightOneSpectrum.valuation_lt_one_iff_mem]; exact hd
  exact le_antisymm h1 (not_lt.mp h2)
end GlobalTheory.UnRep.NormOne
