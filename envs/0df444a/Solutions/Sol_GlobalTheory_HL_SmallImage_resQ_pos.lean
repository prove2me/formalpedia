-- Prove2me | solution 1 for GlobalTheory.HL.SmallImage.resQ_pos
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T07:40:21.350384+00:00
-- url     : https://prove2.me/submissions/53618ad2-6386-4b0c-ab8e-5076d5265fdc

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CardEqPowAndIndexGe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianDoubleCosetTermBasicFacts
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_TermExponentsNonnegAndDefectGroupBoundStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_PairingSecondTypeTestOnRepresentativesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_GluingImageCardPowLeDefectGroupCard

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
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.SmallImage
open ValuativeRel MeasureTheory
open scoped Pointwise ENNReal Classical
namespace GlobalTheory.HL.SmallImage
namespace _root_.GlobalTheory.HL.SmallImage
theorem _root_.solution {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    (ϖ : 𝒪[F]) (h : Irreducible ϖ) : 0 < _root_.GlobalTheory.HL.resQ ϖ := by
  unfold _root_.GlobalTheory.HL.resQ
  have hmax : IsLocalRing.maximalIdeal 𝒪[F] = Ideal.span {ϖ} :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp h
  rw [← hmax]
  have : Finite (IsLocalRing.ResidueField 𝒪[F]) := inferInstance
  exact Nat.card_pos_iff.mpr ⟨inferInstance, this⟩
end _root_.GlobalTheory.HL.SmallImage
end GlobalTheory.HL.SmallImage
