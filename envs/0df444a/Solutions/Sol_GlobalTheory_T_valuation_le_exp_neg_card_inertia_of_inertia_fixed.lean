-- Prove2me | solution 1 for GlobalTheory.T.valuation_le_exp_neg_card_inertia_of_inertia_fixed
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T18:25:58.01013+00:00
-- url     : https://prove2.me/submissions/a3015247-8f72-4922-8ffd-12d36affd2c7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ValuationLeExpNegCardInertiaOfInertiaFixed
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ValuationLeExpNegCardInertiaOfInertiaFixedStatement
import Theorems.Thm_GlobalTheory_InertiaFixedVal_valuation_le_exp_neg_card_inertia


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
theorem _root_.solution : ∀ (R K L : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [PerfectField (IsLocalRing.ResidueField R)] [Field K] [Algebra R K] [IsFractionRing R K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L] [Algebra R L] [IsScalarTower R K L] [SMulCommClass (L ≃ₐ[K] L) R L] [IsDedekindDomain (integralClosure R L)] [IsFractionRing (integralClosure R L) L] (P : IsDedekindDomain.HeightOneSpectrum (integralClosure R L)) (y : L), (∀ σ ∈ P.asIdeal.inertia (L ≃ₐ[K] L), σ y = y) → P.valuation L y < 1 → P.valuation L y ≤ WithZero.exp (-(Nat.card (P.asIdeal.inertia (L ≃ₐ[K] L)) : ℤ)) := by
  first | exact @GlobalTheory.InertiaFixedVal.valuation_le_exp_neg_card_inertia | exact GlobalTheory.InertiaFixedVal.valuation_le_exp_neg_card_inertia | (intros; apply GlobalTheory.InertiaFixedVal.valuation_le_exp_neg_card_inertia <;> assumption)
end _root_.GlobalTheory.T
