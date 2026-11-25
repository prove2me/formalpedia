-- Prove2me | solution 1 for GlobalTheory.ResProd.place_eq_zpow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T07:54:08.179832+00:00
-- url     : https://prove2.me/submissions/60ac0ec0-989f-4292-aae0-b6d307ea394e

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_PsiEDef
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_GFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsEqZpowMulUnit
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsIrreducible
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsIntegralOfQuad
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ProdResQZpow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.ResProd
namespace GlobalTheory.ResProd
theorem _root_.solution {F : Type} [Field F] [NumberField F] (p : HeightOneSpectrum (𝓞 F))
    {x : F} (hx : x ≠ 0) :
    FinitePlace.equivHeightOneSpectrum.symm p x =
      (Ideal.absNorm p.asIdeal : ℝ) ^ WithZero.log (p.valuation F x) := by
  have h0 : p.valuation F x ≠ 0 := (Valuation.ne_zero_iff _).mpr hx
  rw [NumberField.FinitePlace.equivHeightOneSpectrum_symm_apply,
    NumberField.FinitePlace.norm_embedding', WithZeroMulInt.toNNReal_neg_apply _ h0,
    NNReal.coe_zpow, NNReal.coe_natCast]
  congr 1
  conv_rhs => rw [← WithZero.coe_unzero h0]
  rfl
end GlobalTheory.ResProd
