-- Prove2me | solution 1 for GlobalTheory.HL.CoordTermWt.map_span
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T07:36:55.685286+00:00
-- url     : https://prove2.me/submissions/844628b0-3395-4c7a-a4fd-4a7b57d8b0e7

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
import Theorems.Thm_GlobalTheory_HL_CoordTermWt_fam_mem
import Theorems.Thm_GlobalTheory_HL_CoordTermWt_th_ne
import Theorems.Thm_GlobalTheory_HL_CoordUnip_theta_eq
import Theorems.Thm_GlobalTheory_HL_WitIndep_th_ne


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
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
theorem _root_.solution (t : Term V M r) (A : Submodule E S.V) :
    (Submodule.span E (Set.range (H.MMfam t))).map (c.e : V →ₗ[E] S.V) ≤ A ↔
      (∀ b, c.e (t.f b) ∈ A) ∧ ∀ b, c.e (t.f' b) ∈ A := by
  rw [Submodule.map_le_iff_le_comap, Submodule.span_le, Set.range_subset_iff]
  refine (fam_mem t _).trans ?_
  rw [CoordUnip.theta_eq c]
  refine and_congr_right fun h => forall_congr' fun b => ?_
  have hu : IsUnit (algebraMap F E S.th⁻¹) := (IsUnit.mk0 _ (inv_ne_zero (th_ne S))).map _
  rw [Submodule.smul_mem_iff_of_isUnit _ hu, Submodule.sub_mem_iff_left _ (h b)]
  rfl
end GlobalTheory.HL.CoordTermWt
