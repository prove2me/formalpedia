-- Prove2me | solution 1 for GlobalTheory.MoveFine.finite_image_mk
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:19:43.627292+00:00
-- url     : https://prove2.me/submissions/1c04714f-80cb-4989-9bc4-406a24d2b419

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_Cint
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NoLeak
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_BasisOfIsCompl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianDoubleCosetTermBasicFactsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_TermExponentsNonnegAndDefectGroupBoundStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_EichlerLatticeLocallyConstantDataStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsFineSubgroupMovesAtLattice

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL GlobalTheory.IdxInt MeasureTheory
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.MoveFine
namespace GlobalTheory.MoveFine
theorem _root_.solution {W : Type} [AddCommGroup W] (B G : AddSubgroup W) (h : B.relIndex G ≠ 0)
    (s : Set W) (hs : s ⊆ G) : ((fun w => (QuotientAddGroup.mk w : W ⧸ B)) '' s).Finite := by
  haveI : Finite (G ⧸ B.addSubgroupOf G) := AddSubgroup.index_ne_zero_iff_finite.1 h
  let φ : G ⧸ B.addSubgroupOf G → W ⧸ B :=
    QuotientAddGroup.map (B.addSubgroupOf G) B G.subtype (fun x hx => hx)
  refine (Set.finite_range φ).subset ?_
  rintro _ ⟨w, hw, rfl⟩
  exact ⟨QuotientAddGroup.mk ⟨w, hs hw⟩, rfl⟩
end GlobalTheory.MoveFine
