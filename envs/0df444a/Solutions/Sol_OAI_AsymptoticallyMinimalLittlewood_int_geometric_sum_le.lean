-- Prove2me | solution 1 for OAI.AsymptoticallyMinimalLittlewood.int_geometric_sum_le
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T06:22:40.076982+00:00
-- url     : https://prove2.me/submissions/20d33f2f-a41c-4099-a035-98bf1bb20d86

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Littlewood/Rounding.lean:L137-L161
-- (upload_full_project.md Phase 4): solution for node OAI.AsymptoticallyMinimalLittlewood.int_geometric_sum_le. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_AsymptoticallyMinimalLittlewood
import Definitions.Def_OAI_Analysis_Littlewood_Gaussian
import Definitions.Def_OAI_Analysis_Littlewood_Rounding

-- ---- from OAI.Analysis.Littlewood.Rounding ----
-- Lean 4.34 name, proved using the Mathlib 0df444a lemma (same statement); as in oai-math-oct-2026.
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe u v w

namespace AsymptoticallyMinimalLittlewood
noncomputable section
open MeasureTheory Complex Real FourierTransform Filter Topology
open scoped FourierTransform SchwartzMap ContDiff

/-- The geometric partition function for integer quantization labels. -/
theorem int_geometric_sum_le (S : Finset ℤ) {q : ℝ} (hq : 0 ≤ q) (hq' : q ≤ 1 / 2) :
    (∑ z ∈ S, q ^ z.natAbs) ≤ Real.exp (4 * q) := by
  have hq1 : q < 1 := by linarith
  have hnat : HasSum (fun n : ℕ ↦ q ^ (n : ℤ).natAbs) (1 - q)⁻¹ := by
    simpa using hasSum_geometric_of_lt_one hq hq1
  have hneg : HasSum (fun n : ℕ ↦ q ^ (-(n : ℤ)).natAbs) (1 - q)⁻¹ := by
    simpa using hasSum_geometric_of_lt_one hq hq1
  have hfull := HasSum.of_nat_of_neg (f := fun z : ℤ ↦ q ^ z.natAbs) hnat hneg
  have hsum : (∑ z ∈ S, q ^ z.natAbs) ≤ (1 - q)⁻¹ + (1 - q)⁻¹ - 1 := by
    simpa using (hfull.summable.sum_le_tsum S (fun z hz ↦ pow_nonneg hq _)).trans_eq
      hfull.tsum_eq
  have hden : 0 < 1 - q := by linarith
  have hinv : (1 - q)⁻¹ ≤ (2 : ℝ) := by
    rw [inv_eq_one_div]
    apply (div_le_iff₀ hden).mpr
    linarith
  have hid : (1 - q)⁻¹ + (1 - q)⁻¹ - 1 = 1 + 2 * q * (1 - q)⁻¹ := by
    field_simp [ne_of_gt hden]
    ring
  have hrat : (1 - q)⁻¹ + (1 - q)⁻¹ - 1 ≤ 1 + 4 * q := by
    rw [hid]
    have := mul_le_mul_of_nonneg_left hinv (show 0 ≤ 2 * q by positivity)
    nlinarith
  exact hsum.trans (hrat.trans (by simpa [add_comm] using Real.add_one_le_exp (4 * q)))

open scoped ComplexConjugate
open Finset

end

end AsymptoticallyMinimalLittlewood

end OAI

-- ---- platform node ----
open OAI OAI.AsymptoticallyMinimalLittlewood
open MeasureTheory Complex Real FourierTransform Filter Topology
open scoped FourierTransform SchwartzMap ContDiff


theorem solution : type_of% @_root_.OAI.AsymptoticallyMinimalLittlewood.int_geometric_sum_le := @_root_.OAI.AsymptoticallyMinimalLittlewood.int_geometric_sum_le
