-- Prove2me | solution 1 for GlobalTheory.T.valuation_uniformizer_integralClosure_eq_exp_neg_ramificationIdx
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T18:26:02.0436+00:00
-- url     : https://prove2.me/submissions/cb0277f1-f054-40cf-8a52-1ff5ddf8b318

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ValuationUniformizerIntegralClosureEqExpNegRamif
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ValuationUniformizerIntegralClosureEqExpNegRamifStatement
import Theorems.Thm_GlobalTheory_valuation_uniformizer_integralClosure


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsDedekindDomain
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (R K L : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K] [Field L] [Algebra K L] [FiniteDimensional K L] [Algebra R L] [IsScalarTower R K L] [IsDedekindDomain (integralClosure R L)] [IsFractionRing (integralClosure R L) L] (P : IsDedekindDomain.HeightOneSpectrum (integralClosure R L)) (π : R), Irreducible π → P.valuation L (algebraMap K L (algebraMap R K π)) = WithZero.exp (-(P.asIdeal.ramificationIdx R : ℤ)) := by
  first | exact @GlobalTheory.valuation_uniformizer_integralClosure | exact GlobalTheory.valuation_uniformizer_integralClosure | (intros; apply GlobalTheory.valuation_uniformizer_integralClosure <;> assumption)
end _root_.GlobalTheory.T
