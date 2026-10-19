-- Prove2me | solution 1 for OAI.AsymptoticallyMinimalLittlewood.Auxiliary.exists_binary_energy
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T07:07:19.978154+00:00
-- url     : https://prove2.me/submissions/8ef6ca4e-fe08-46cf-bed8-50864f08fd98

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Littlewood/BinaryPacket.lean:L199-L222
-- (upload_full_project.md Phase 4): solution for node OAI.AsymptoticallyMinimalLittlewood.Auxiliary.exists_binary_energy. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_AsymptoticallyMinimalLittlewood
import Definitions.Def_OAI_Analysis_Littlewood_Gaussian
import Definitions.Def_OAI_Analysis_Littlewood_Rounding
import Definitions.Def_OAI_Analysis_Littlewood_BinaryPacket
import Theorems.Thm_OAI_AsymptoticallyMinimalLittlewood_Auxiliary_binary_abs_le
import Theorems.Thm_OAI_AsymptoticallyMinimalLittlewood_Auxiliary_energy_increment

-- ---- from OAI.Analysis.Littlewood.BinaryPacket ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe uE uX

namespace AsymptoticallyMinimalLittlewood
namespace Auxiliary
noncomputable section
open MeasureTheory Filter Topology Complex
open scoped BigOperators ComplexConjugate ENNReal
attribute [local instance] OAI.AsymptoticallyMinimalLittlewood.Auxiliary.instMeasureSpaceUnitAddCircle_oAI
attribute [local instance] OAI.AsymptoticallyMinimalLittlewood.Auxiliary.instIsAddHaarMeasureUnitAddCircleVolume_oAI
attribute [local instance] OAI.AsymptoticallyMinimalLittlewood.Auxiliary.instIsProbabilityMeasureUnitAddCircleVolume_oAI
lemma energy_bounds (n : ℕ) : 0 ≤ energy n ∧ energy n ≤ 1 := by
  refine ⟨integral_nonneg (fun x ↦ sq_nonneg _), ?_⟩
  calc
    energy n ≤ ∫ _ : Fin n → UnitAddCircle, (1:ℝ) := by
      apply integral_mono (((binary_continuous n).pow 2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)) (integrable_const _)
      intro x
      exact (sq_le_one_iff_abs_le_one _).mpr (binary_abs_le n x)
    _ = 1 := by simp

lemma energy_monotone : Monotone energy := by
  apply monotone_nat_of_le_succ
  intro n
  exact le_trans (by nlinarith [sq_nonneg (1-energy n)]) (energy_increment n)

lemma exists_binary_energy {δ : ℝ} (hδ : 0 < δ) :
    ∃ d : ℕ, 2 ≤ d ∧ 1-δ ≤ energy d := by
  by_contra hc
  have hall : ∀ n : ℕ, energy n < 1-δ := by
    intro n
    have hm : energy (max 2 n) < 1-δ := by
      by_contra h
      exact hc ⟨max 2 n, le_max_left _ _, le_of_not_gt h⟩
    exact lt_of_le_of_lt (energy_monotone (le_max_right _ _)) hm
  have hgrowth : ∀ n : ℕ, (n:ℝ)*(δ^2/8) ≤ energy n := by
    intro n
    induction n with
    | zero => simpa using (energy_bounds 0).1
    | succ n ih =>
      have hi := energy_increment n
      have hb := hall n
      rw [Nat.cast_succ]
      nlinarith [sq_nonneg (1-energy n-δ)]
  obtain ⟨n,hn⟩ := exists_nat_gt (8/δ^2)
  have hpos : 0 < δ^2 := sq_pos_of_pos hδ
  have hnum : 1 < (n:ℝ)*(δ^2/8) := by
    have hh := (div_lt_iff₀ hpos).mp hn
    nlinarith
  linarith [hgrowth n, (energy_bounds n).2]

open UnitAddTorus

end
end Auxiliary
end AsymptoticallyMinimalLittlewood

end OAI

-- ---- platform node ----
open OAI OAI.AsymptoticallyMinimalLittlewood OAI.AsymptoticallyMinimalLittlewood.Auxiliary
open MeasureTheory Filter Topology Complex
open scoped BigOperators ComplexConjugate ENNReal
attribute [local instance] OAI.AsymptoticallyMinimalLittlewood.Auxiliary.instMeasureSpaceUnitAddCircle_oAI
attribute [local instance] OAI.AsymptoticallyMinimalLittlewood.Auxiliary.instIsAddHaarMeasureUnitAddCircleVolume_oAI
attribute [local instance] OAI.AsymptoticallyMinimalLittlewood.Auxiliary.instIsProbabilityMeasureUnitAddCircleVolume_oAI


theorem solution : type_of% @_root_.OAI.AsymptoticallyMinimalLittlewood.Auxiliary.exists_binary_energy := @_root_.OAI.AsymptoticallyMinimalLittlewood.Auxiliary.exists_binary_energy
