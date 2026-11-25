-- Prove2me | solution 1 for GlobalTheory.HL.UnimodTerm.mem_iff_graph
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:02:41.350363+00:00
-- url     : https://prove2.me/submissions/8db308af-0b39-4563-966b-c0cba2b65a09

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsEqZpowMulUnit
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_BasisOfIsCompl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianDoubleCosetTermBasicFacts
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianDoubleCosetFrameClassProperties
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_FrameLatticeGramDetAndMinorsOrbitInvariantStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IntegralOfMulVec
import Theorems.Thm_GlobalTheory_HL_UnimodTerm_proj_mem
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_HL_FrameTri_spanTo_mono
import Theorems.Thm_GlobalTheory_HL_FrameTri_sub_mem
import Theorems.Thm_GlobalTheory_HL_TermBasic_spanTo_mono
import Theorems.Thm_GlobalTheory_HL_TermBasic_sub_mem
import Theorems.Thm_GlobalTheory_HL_TermBasic_term_basic
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
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.UnimodTerm
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E} {r k : ℕ} (S : Frames L r k)
open ValuativeRel MeasureTheory
open scoped Pointwise ENNReal Classical
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : _root_.Formalism.MainNotions.S.Loc.LocE F E} {r k : ℕ} (S : _root_.GlobalTheory.HL.Frames L r k)
namespace GlobalTheory.HL.UnimodTerm
namespace _root_.GlobalTheory.HL.UnimodTerm
theorem _root_.solution {d : S.Datum} {Λ : Submodule L.O S.V}
    (hT : S.IsTerm d Λ) (ha : S.a = 0) {w : S.V}
    (hw : w ∈ S.W0) : w ∈ Λ ↔ (w, w) ∈ d.2.2 := by
  obtain ⟨-, hW, hMs, -, -, -, -, -⟩ := _root_.GlobalTheory.HL.TermBasic.term_basic L r k S d Λ hT
  obtain ⟨-, -, -, -, -, -, -, hgraph⟩ := hW
  have hXME : S.X ≤ S.ME :=
    (_root_.GlobalTheory.HL.TermBasic.spanTo_mono S S.f (Nat.le_succ r)).trans le_sup_left
  have hX'ME : S.X' ≤ S.ME :=
    (_root_.GlobalTheory.HL.TermBasic.spanTo_mono S S.f' (Nat.le_succ r)).trans le_sup_right
  have hworth : ∀ y ∈ S.ME, _root_.GlobalTheory.HL.hf L S.Hm w y = 0 := hw
  rw [hgraph]
  unfold _root_.GlobalTheory.HL.Frames.graphOf
  simp only [Set.mem_setOf_eq]
  constructor
  · intro hwΛ
    exact ⟨w, hwΛ, w, hwΛ, fun y hy => hworth y (hX'ME hy), fun y hy => hworth y (hXME hy),
      by simp, by simp, ⟨0, Λ.zero_mem, by simp⟩⟩
  · rintro ⟨y', hy', y, hy, -, -, -, hyw, -⟩
    have hproj := _root_.GlobalTheory.HL.UnimodTerm.proj_mem S hT ha hy (hXME hyw)
      (by rw [sub_sub_cancel]; exact hw)
    have h1 : y - w ∈ Λ ⊓ Submodule.restrictScalars L.O S.ME := hMs hproj
    have h2 := Λ.sub_mem hy (Submodule.mem_inf.mp h1).1
    rwa [sub_sub_cancel] at h2
end _root_.GlobalTheory.HL.UnimodTerm
end GlobalTheory.HL.UnimodTerm
