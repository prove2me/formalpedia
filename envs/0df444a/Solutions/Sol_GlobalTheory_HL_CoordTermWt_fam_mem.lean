-- Prove2me | solution 1 for GlobalTheory.HL.CoordTermWt.fam_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T06:56:36.817828+00:00
-- url     : https://prove2.me/submissions/abc8fedf-95eb-4192-89f3-f0679d1242ba

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_IsTermOver
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_GgNone
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SpanToLePerp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianDoubleCosetTermBasicFacts
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_TermInvariantsIndependentOfWitnesses
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SpanToZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianFrameCoordinatesTransportInnerLatticesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_FramePairCoordinatesTransportInnerLatticesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_TermOverFrameCoordinates
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_TermsCorrespond
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc GlobalTheory.HL
open scoped Pointwise ENNReal Classical
noncomputable section
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.CoordTermWt
open GlobalTheory.HL.CoordTerm
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] {H : HermSp M V} {r k : ℕ}
variable {P : LocNG.FPair H r} {S : Frames M.L r k} (c : Coord P S)
namespace GlobalTheory.HL.CoordTermWt
theorem _root_.solution {R : Type} [Ring R] [Module R V] (t : Term V M r) (A : Submodule R V) :
    (∀ i, H.MMfam t i ∈ A) ↔ (∀ b, t.f b ∈ A) ∧
      ∀ b, algebraMap F E (LocNG.theta M)⁻¹ • (t.f' b - t.f b) ∈ A := by
  unfold HermSp.MMfam LocNG.theta
  cases M.split with
  | none =>
    simp only [Sum.forall, Sum.elim_inl, Sum.elim_inr, inv_one, map_one, one_smul]
    refine and_congr_right fun h => forall_congr' fun b => ?_
    exact (A.sub_mem_iff_left (h b)).symm
  | some g => simp only [Sum.forall, Sum.elim_inl, Sum.elim_inr]
end GlobalTheory.HL.CoordTermWt
