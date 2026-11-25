-- Prove2me | solution 1 for GlobalTheory.HL.WitIndep.lev_step
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T07:41:10.808261+00:00
-- url     : https://prove2.me/submissions/aca1ed7f-d0cf-4ee3-b705-a9eb884bb3bd

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_NormAdditiveCharacterTypePrimeEqOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SpanToLePerp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MemPerpSpan
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_TermInvariantsIndependentOfWitnesses
import Theorems.Thm_GlobalTheory_HL_WitIndep_sum_sum
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
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.WitIndep
open GlobalTheory.HL.Eichler
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E} {r k : ℕ} (S : Frames L r k)
namespace GlobalTheory.HL.WitIndep
theorem _root_.solution {g g' h h' : Fin (r + 1) → S.V} (H : (h, h') ∈ S.frameCls g g') (b : S.V) (j : ℕ)
    (hb : ∃ al al' : Fin (r + 1) → E, b = ∑ i, al i • h i + ∑ i, al' i • h' i ∧
      ∀ i : Fin (r + 1), j ≤ (i : ℕ) → S.RR (al i) (al' i)) :
    ∃ al al' : Fin (r + 1) → E, b = ∑ i, al i • g i + ∑ i, al' i • g' i ∧
      ∀ i : Fin (r + 1), j ≤ (i : ℕ) → S.RR (al i) (al' i) := by
  obtain ⟨A, A', hA, hA', h0, -, hc, e, e'⟩ := H
  simp only at e e'
  obtain ⟨al, al', rfl, hR⟩ := hb
  refine ⟨fun i => ∑ l, A i l * al l, fun i => ∑ l, A' i l * al' l, by simp only [e, e', sum_sum],
    fun i hi => ?_⟩
  have key : ∀ l, S.RR (A i l * al l) (A' i l * al' l) := by
    intro l
    by_cases hl : l < i
    · rw [(h0 i l hl).1, (h0 i l hl).2, zero_mul, zero_mul]
      exact ⟨L.O.zero_mem, 0, L.O.zero_mem, by simp⟩
    · obtain ⟨h1, c, hcO, h2⟩ := hR l (hi.trans (not_lt.1 hl))
      obtain ⟨d, hdO, h3⟩ := hc i l
      exact ⟨L.O.mul_mem (hA' i l) h1, A i l * c + d * al' l,
        L.O.add_mem (L.O.mul_mem (hA i l) hcO) (L.O.mul_mem hdO h1),
        by linear_combination A i l * h2 + al' l * h3⟩
  refine ⟨L.O.sum_mem fun l _ => (key l).1, ?_⟩
  choose c hcO hc using fun l => (key l).2
  refine ⟨∑ l, c l, L.O.sum_mem fun l _ => hcO l, ?_⟩
  simp only [← Finset.sum_add_distrib, hc, Finset.mul_sum]
end GlobalTheory.HL.WitIndep
