-- Prove2me | solution 1 for GlobalTheory.FrameAct.tauRel_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T07:31:44.225319+00:00
-- url     : https://prove2.me/submissions/d9da7814-7b52-4294-bb0f-a779c31d58ef

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
theorem _root_.solution (h : S.GLV) (hh : h ∈ S.St) (d : S.Datum) (Λ : Submodule L.O S.V)
    (hM : S.M d (h • Λ) = h • S.M d Λ) (w : S.V) (hw : w ∈ S.W0) (y : S.V)
    (H : S.TauRel d Λ w y) : S.TauRel d (h • Λ) w (h y) := by
  obtain ⟨la, hla, la', hla', h1, h2, h3, h4⟩ := H
  have hN : h ∈ S.N := (Subgroup.mem_inf.mp hh).1
  have hN' : h ∈ S.N' := (Subgroup.mem_inf.mp hh).2
  simp only [Frames.N, Frames.N', Frames.Nof, Subgroup.mem_inf] at hN hN'
  have u1 : (∀ v, h v ∈ perp L S.Hm (S.spanTo S.f r) ↔ v ∈ perp L S.Hm (S.spanTo S.f r)) ∧
      ∀ v ∈ perp L S.Hm (S.spanTo S.f r), h v - v ∈ S.spanTo S.f r := hN.2
  have u2 : (∀ v, h v ∈ perp L S.Hm (S.spanTo S.f' r) ↔ v ∈ perp L S.Hm (S.spanTo S.f' r)) ∧
      ∀ v ∈ perp L S.Hm (S.spanTo S.f' r), h v - v ∈ S.spanTo S.f' r := hN'.2
  have hw' : ∀ z ∈ S.ME, hf L S.Hm w z = 0 := hw
  have hsub : ∀ g : Fin (r + 1) → S.V, S.spanTo g r ≤ S.spanTo g (r + 1) := fun g =>
    Submodule.span_mono (Set.image_mono fun i (hi : (i : ℕ) < r) => Nat.lt_succ_of_lt hi)
  have hw1 : w ∈ perp L S.Hm (S.spanTo S.f r) := by
    show ∀ z ∈ S.spanTo S.f r, hf L S.Hm w z = 0
    intro z hz
    exact hw' z (le_sup_left (a := S.spanTo S.f (r + 1)) (hsub S.f hz))
  have hw2 : w ∈ perp L S.Hm (S.spanTo S.f' r) := by
    show ∀ z ∈ S.spanTo S.f' r, hf L S.Hm w z = 0
    intro z hz
    exact hw' z (le_sup_right (b := S.spanTo S.f' (r + 1)) (hsub S.f' hz))
  have e3 : h w - w + h la' - (h w - w + h la) = h (la' - la) := by
    rw [map_sub]
    abel
  refine ⟨h w - w + h la, ?_, h w - w + h la', ?_, ?_, ?_, ?_, ?_⟩
  · exact Submodule.add_mem _ (u1.2 w hw1) ((spanTo_iff S h hh r la).2 hla)
  · exact Submodule.add_mem _ (u2.2 w hw2) ((spanTo_iff' S h hh r la').2 hla')
  · have e : w + (h w - w + h la) = h (w + la) := by
      rw [map_add]
      abel
    rw [e]
    exact (mem_smul_iff S h Λ _).2 h1
  · have e : w + (h w - w + h la') = h (w + la') := by
      rw [map_add]
      abel
    rw [e]
    exact (mem_smul_iff S h Λ _).2 h2
  · rw [e3]
    exact (inTh_iff S h Λ _).2 h3
  · rw [e3, ← LinearEquiv.map_smul, ← map_sub, hM]
    exact (mem_smul_iff S h _ _).2 h4
end GlobalTheory.FrameAct
