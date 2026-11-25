-- Prove2me | solution 1 for GlobalTheory.HL.LatDet.exp_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:58:48.677736+00:00
-- url     : https://prove2.me/submissions/b399c40a-981a-435f-a0f5-39df9a192145

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_HermLat
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_CardQuotPow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CardQuotPow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ImportsBis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_RelativeLatticeVolumeOfDetValuation
import Theorems.Thm_GlobalTheory_CardQuotientPow_main
import Theorems.Thm_GlobalTheory_QuotientCardinality_main


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.LatDet
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
namespace GlobalTheory.HL.LatDet
theorem _root_.solution {ϖ : 𝒪[F]} (hϖ : Irreducible ϖ) {a : ℤ} {m : ℕ} {u v : (𝒪[F])ˣ}
    (h : (ϖ : F) ^ a * ((u : 𝒪[F]) : F) * ((v : 𝒪[F]) : F) = (ϖ : F) ^ m) : a = m :=
  _root_.GlobalTheory.QuotientCardinality.main hϖ h
end GlobalTheory.HL.LatDet
