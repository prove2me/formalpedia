-- Prove2me | solution 1 for GlobalTheory.HL.BlockStab.exists_monomial
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:29:05.885702+00:00
-- url     : https://prove2.me/submissions/3589ad52-105c-43b4-bed7-97f9a1108f82

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_HermLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianFramesPairingStabilizerBlockDiagonal
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
noncomputable section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.BlockStab
namespace GlobalTheory.HL.BlockStab
theorem _root_.solution {E : Type} [CommRing E] (bs : List (Eˣ × ℕ+)) :
    ∃ (σ β : ℕ → ℕ) (t : ℕ → Eˣ), ∀ a, a < (bs.map (fun b => (b.2 : ℕ))).sum →
      σ a < (bs.map (fun b => (b.2 : ℕ))).sum ∧ σ (σ a) = a ∧ β (σ a) = β a ∧
      ∀ b, b < (bs.map (fun b => (b.2 : ℕ))).sum →
        (sameBlock bs a b = true ↔ β a = β b) ∧ (a ≤ b → β a ≤ β b) ∧
        (β a = β b → a + σ a = b + σ b) ∧
        ptEntryL bs a b = if b = σ a then (t (β a) : E) else 0 := by
  induction bs with
  | nil => exact ⟨id, id, fun _ => 1, by simp⟩
  | cons x bs ih =>
    obtain ⟨t0, s⟩ := x
    obtain ⟨σ, β, t, h⟩ := ih
    simp only [List.map_cons, List.sum_cons]
    generalize (bs.map (fun b => (b.2 : ℕ))).sum = N at h ⊢
    refine ⟨fun a => if a < (s : ℕ) then s - 1 - a else σ (a - s) + s,
      fun a => if a < (s : ℕ) then 0 else β (a - s) + 1,
      fun k => if k = 0 then t0 else t (k - 1), fun a ha => ?_⟩
    simp only [sameBlock, ptEntryL]
    generalize (s : ℕ) = m at *
    by_cases h1 : a < m
    · have h2 : m - 1 - a < m := by omega
      simp only [h1, h2, if_true]
      refine ⟨by omega, by omega, trivial, fun b hb => ?_⟩
      by_cases h3 : b < m
      · simp only [h3, if_true]
        refine ⟨by simp, by simp, fun _ => by omega, ?_⟩
        have : a + b + 1 = m ↔ b = m - 1 - a := by omega
        simp [this]
      · have h4 : ¬ m ≤ a := by omega
        have h5 : ¬ b = m - 1 - a := by omega
        simp [h3, h4, h5]
    · obtain ⟨e1, e2, e3, e4⟩ := h (a - m) (by omega)
      have h2 : ¬ σ (a - m) + m < m := by omega
      have h4 : m ≤ a := by omega
      simp only [h1, h2, if_false, Nat.add_sub_cancel, e2, e3]
      refine ⟨by omega, by omega, trivial, fun b hb => ?_⟩
      by_cases h3 : b < m
      · have h5 : ¬ m ≤ b := by omega
        have h6 : ¬ b = σ (a - m) + m := by omega
        have h7 : ¬ a ≤ b := by omega
        simp [h3, h5, h6, h7]
      · obtain ⟨f1, f2, f3, f4⟩ := e4 (b - m) (by omega)
        have h5 : m ≤ b := by omega
        have h6 : b = σ (a - m) + m ↔ b - m = σ (a - m) := by omega
        simp only [h3, h4, h5, if_false, h6, f4]
        refine ⟨by simp [f1], fun hab => ?_, fun hab => ?_, by simp⟩
        · have := f2 (by omega); omega
        · have := f3 (by omega); omega
end GlobalTheory.HL.BlockStab
