-- Prove2me | solution 1 for GlobalTheory.SmulIntegralDenominator.exists_smul_integral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:49:51.168792+00:00
-- url     : https://prove2.me/submissions/c40de56b-c24e-4901-b64c-7b123ddef4eb

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_PsiEDef
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_GFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsSmulIntegral

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel
open GlobalTheory GlobalTheory.SmulIntegralDenominator
namespace GlobalTheory.SmulIntegralDenominator
theorem _root_.solution {K : Type} [Field K] [ValuativeRel K]
    {R : Type} [CommRing R] [Algebra K R] [Module.Finite K R] (x : R) :
    ∃ e : 𝒪[K], e ≠ 0 ∧ IsIntegral 𝒪[K] (e • x) := by
  have h1 : IsAlgebraic K x := (Algebra.IsIntegral.isIntegral (R := K) x).isAlgebraic
  have h2 : IsAlgebraic 𝒪[K] x := (IsFractionRing.isAlgebraic_iff 𝒪[K] K R).mpr h1
  exact h2.exists_integral_multiple
end GlobalTheory.SmulIntegralDenominator
