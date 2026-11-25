-- Prove2me | solution 1 for GlobalTheory.FrameAct.graph_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T07:36:45.399847+00:00
-- url     : https://prove2.me/submissions/c8d9d1b5-264f-48ba-9e3c-428bfbf804f5

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_NormAdditiveCharacterTypePrimeEqOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_FramesCharactersAgreeCommonStabiliserStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_TermInvariantsIndependentOfWitnessesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianFramesStabilizerActsOnTerms
import Theorems.Thm_GlobalTheory_FrameAct_mem_smul_iff
import Theorems.Thm_GlobalTheory_FrameAct_inTh_iff
import Theorems.Thm_GlobalTheory_FrameAct_spanTo_iff
import Theorems.Thm_P2M_GlobalTheory_FrameAct_spanTo_iff__721488b8eec6
import Theorems.Thm_GlobalTheory_FrameAct_perp_iff
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
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.FrameAct
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E} {r k : ℕ} (S : Frames L r k)
namespace GlobalTheory.FrameAct
theorem _root_.solution (h : S.GLV) (hh : h ∈ S.St) (Λ : Submodule L.O S.V) :
    S.graphOf Λ ⊆ S.graphOf (h • Λ) := by
  rintro p ⟨y', hy', y, hy, hy'p, hyp, h1, h2, h3⟩
  have hN : h ∈ S.N := (Subgroup.mem_inf.mp hh).1
  have hN' : h ∈ S.N' := (Subgroup.mem_inf.mp hh).2
  simp only [Frames.N, Frames.N', Frames.Nof, Subgroup.mem_inf] at hN hN'
  have u1 : (∀ w, h w ∈ perp L S.Hm (S.spanTo S.f r) ↔ w ∈ perp L S.Hm (S.spanTo S.f r)) ∧
      ∀ w ∈ perp L S.Hm (S.spanTo S.f r), h w - w ∈ S.spanTo S.f r := hN.2
  have u2 : (∀ w, h w ∈ perp L S.Hm (S.spanTo S.f' r) ↔ w ∈ perp L S.Hm (S.spanTo S.f' r)) ∧
      ∀ w ∈ perp L S.Hm (S.spanTo S.f' r), h w - w ∈ S.spanTo S.f' r := hN'.2
  refine ⟨h y', (mem_smul_iff S h Λ y').2 hy', h y, (mem_smul_iff S h Λ y).2 hy, ?_, ?_, ?_, ?_, ?_⟩
  · exact (perp_iff S h hh S.X' (fun v => spanTo_iff' S h hh r v) y').2 hy'p
  · exact (perp_iff S h hh S.X (fun v => spanTo_iff S h hh r v) y).2 hyp
  · have e : h y' - p.1 = (h y' - y') + (y' - p.1) := by abel
    rw [e]
    exact Submodule.add_mem _ (u2.2 y' hy'p) h1
  · have e : h y - p.2 = (h y - y) + (y - p.2) := by abel
    rw [e]
    exact Submodule.add_mem _ (u1.2 y hyp) h2
  · have h4 := (inTh_iff S h Λ (y' - y)).2 h3
    rw [map_sub] at h4
    exact h4
end GlobalTheory.FrameAct
