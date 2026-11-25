-- Prove2me | solution 1 for GlobalTheory.HL.MoveChar.coords
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T06:32:42.666626+00:00
-- url     : https://prove2.me/submissions/db53c2f3-69f0-417d-ba9a-2a166340d163

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_DualInterSelfDualHermitianLatticeSubspace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_BasisOfIsCompl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianDoubleCosetTermBasicFacts
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_FrameMoveCharacterNeOne
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
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.MoveChar
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E} {r k : ℕ} (S : Frames L r k)
namespace GlobalTheory.HL.MoveChar
theorem _root_.solution {g : Fin (r + 1) → S.V} {n : S.GLV} (hn : n ∈ S.Nof g) (j : Fin r) {x : S.V}
    (hx : x ∈ S.spanTo g (j + 1)) :
    ∃ c : Fin (r + 1) → E, (∀ i : Fin (r + 1), (j : ℕ) + 1 ≤ i → c i = 0) ∧ x = ∑ i, c i • n (g i) := by
  have h1 : ∀ v, n v ∈ S.spanTo g (j + 1) ↔ v ∈ S.spanTo g (j + 1) :=
    (Subgroup.mem_iInf.1 hn.1.2 j).1
  obtain ⟨y, rfl⟩ := n.surjective x
  have hy := (h1 y).1 hx
  clear hx
  induction hy using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨i, hi, rfl⟩ := hv
    refine ⟨Pi.single i 1, fun i' hi' => Pi.single_eq_of_ne ?_ _, ?_⟩
    · rintro rfl
      exact absurd hi (not_lt.2 hi')
    · simp [Pi.single_apply]
  | zero => exact ⟨0, fun _ _ => rfl, by simp⟩
  | add a b _ _ ha hb =>
    obtain ⟨c, h, e⟩ := ha
    obtain ⟨c', h', e'⟩ := hb
    exact ⟨c + c', fun i hi => by simp [h i hi, h' i hi],
      by rw [map_add, e, e']; simp [add_smul, Finset.sum_add_distrib]⟩
  | smul t a _ ha =>
    obtain ⟨c, h, e⟩ := ha
    exact ⟨t • c, fun i hi => by simp [h i hi],
      by rw [map_smul, e]; simp [Finset.smul_sum, mul_smul]⟩
end GlobalTheory.HL.MoveChar
