-- Prove2me | solution 1 for GlobalTheory.HL.Defect.lead_translate
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:15:49.633225+00:00
-- url     : https://prove2.me/submissions/49279075-6b07-4b15-832d-69d4e9155d3d

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsEqZpowMulUnit
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CardEqPowAndIndexGe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_EichlerIsometry
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_BasisOfIsCompl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SpanToLePerp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MemPerpSpan
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianDoubleCosetTermBasicFacts
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_DetUpdateRowLastSingle
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CardCokernelUnramifiedOrderMatrixOfDetBaseStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianDoubleCosetFramesLevelLeIffCongrFlagSteStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_TermExponentsNonnegAndDefectGroupBound
import Theorems.Thm_GlobalTheory_HL_Defect_lead_mul_tri
import Theorems.Thm_GlobalTheory_HL_Defect_gram_change
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_HL_FrameOnto_exists_matrix
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.Defect
open GlobalTheory.HL.Eichler GlobalTheory.HL.StdLat GlobalTheory.UnramOrder Matrix
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E} {r k : ℕ} (S : Frames L r k)
namespace GlobalTheory.HL.Defect
theorem _root_.solution {n n' : S.GLV} (hn : n ∈ S.N) (hn' : n' ∈ S.N') (l : Fin (r + 2)) :
    lead (Matrix.of fun a b => hf L S.Hm (n' (S.f' b)) (n (S.f a))) l = S.D l := by
  obtain ⟨s, hs, h⟩ := FrameOnto.exists_matrix S S.f S.T S.gram n hn
  obtain ⟨s', hs', h'⟩ := FrameOnto.exists_matrix S S.f' S.T' S.gram' n' hn'
  have h1 := congrArg Matrix.transpose (gram_change L S.Hm S.f' S.f _ _ s' s h' h)
  have h2 : (Matrix.of fun a b => hf L S.Hm (n' (S.f' b)) (n (S.f a))) =
      (s.map L.cj)ᵀ * (S.Zh * s') := by
    rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose] at h1
    exact h1
  rw [h2, (lead_mul_tri _ (s.map L.cj) ⟨fun i j h => by simp [hs.1 i j h], fun i => by simp [hs.2]⟩ l).2,
    (lead_mul_tri _ s' hs' l).1]
  rfl
end GlobalTheory.HL.Defect
