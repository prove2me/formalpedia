-- Prove2me | solution 1 for GlobalTheory.HL.UnimodTerm.le_of_M_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T09:32:33.084232+00:00
-- url     : https://prove2.me/submissions/4544c8a0-d589-42dd-add2-62e610418ff4

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
import Theorems.Thm_GlobalTheory_HL_UnimodTerm_mem_iff_graph
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_FrameBasic_main
import Theorems.Thm_GlobalTheory_FrameGram_main
import Theorems.Thm_GlobalTheory_HL_FrameTri_sub_mem
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
theorem _root_.solution {d : S.Datum} {Λ Λ' : Submodule L.O S.V}
    (hT : S.IsTerm d Λ) (hT' : S.IsTerm d Λ') (ha : S.a = 0)
    (hM : S.M d Λ' = S.M d Λ) : Λ' ≤ Λ := by
  obtain ⟨-, -, hMs, -, -, -, -, -⟩ := _root_.GlobalTheory.HL.TermBasic.term_basic L r k S d Λ hT
  obtain ⟨-, -, hMs', -, -, -, -, -⟩ := _root_.GlobalTheory.HL.TermBasic.term_basic L r k S d Λ' hT'
  obtain ⟨-, hc, -⟩ := _root_.GlobalTheory.FrameBasic.main L r k S
  intro x hx
  have hxtop : x ∈ S.ME ⊔ S.W0 := by
    rw [hc.sup_eq_top]; exact Submodule.mem_top
  obtain ⟨m, hm, w, hw, rfl⟩ := Submodule.mem_sup.mp hxtop
  have hm' : m ∈ S.M d Λ' :=
    _root_.GlobalTheory.HL.UnimodTerm.proj_mem S hT' ha hx hm (by simpa using hw)
  have hmΛ' : m ∈ Λ' := (Submodule.mem_inf.mp
    (show m ∈ Λ' ⊓ Submodule.restrictScalars L.O S.ME from hMs' hm')).1
  rw [hM] at hm'
  have hmΛ : m ∈ Λ := (Submodule.mem_inf.mp
    (show m ∈ Λ ⊓ Submodule.restrictScalars L.O S.ME from hMs hm')).1
  have hwΛ' : w ∈ Λ' := by simpa using Λ'.sub_mem hx hmΛ'
  have hwΛ : w ∈ Λ := (_root_.GlobalTheory.HL.UnimodTerm.mem_iff_graph S hT ha hw).mpr
    ((_root_.GlobalTheory.HL.UnimodTerm.mem_iff_graph S hT' ha hw).mp hwΛ')
  exact Λ.add_mem hmΛ hwΛ
end _root_.GlobalTheory.HL.UnimodTerm
end GlobalTheory.HL.UnimodTerm
