-- Prove2me | solution 1 for OAI.ShortEgyptian.truncatedDivisors_mul
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T02:02:31.183993+00:00
-- url     : https://prove2.me/submissions/0c9d187e-6331-40d4-98e5-3582ec5cffdd

-- Generated from openai/math@1581d4c lean/OAI/NumberTheory/ShortEgyptian/TruncatedDivisors.lean:L16-L32
-- (upload_full_project.md Phase 4): solution for node OAI.ShortEgyptian.truncatedDivisors_mul. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_ShortEgyptianFractions
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_Basic
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_FirstDerivative
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_ReciprocalDifferences
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_IntervalDifferencing
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_IteratedDifferencing
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_ParameterBounds
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_FourierDiscrepancy
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_WindowSpectrum
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_WindowDiscrepancy
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_EmpiricalDiscrepancy
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_DivisorWeights
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_TruncatedDivisors

-- ---- from OAI.NumberTheory.ShortEgyptian.TruncatedDivisors ----
namespace OAI

namespace ShortEgyptian

open scoped BigOperators
open Finset

theorem truncatedDivisors_mul (X : ℝ) {d e : ℕ} (hd : d ≠ 0) (he : e ≠ 0) :
    truncatedDivisorCount X (d*e) ≤ d.divisors.card * truncatedDivisorCount X e := by
  classical
  have hsub : truncatedDivisors X (d*e) ⊆
      (d.divisors ×ˢ truncatedDivisors X e).image (fun bc => bc.1 * bc.2) := by
    intro a ha
    obtain ⟨ha, hX⟩ := mem_filter.mp ha
    obtain ⟨had, han⟩ := Nat.mem_divisors.mp ha
    obtain ⟨b, c, hb, hc, hbc⟩ := exists_dvd_and_dvd_of_dvd_mul had
    have hbpos : 0 < b := Nat.pos_of_dvd_of_pos hb (Nat.pos_of_ne_zero hd)
    have hcle : c ≤ a := by rw [hbc]; exact Nat.le_mul_of_pos_left c hbpos
    exact mem_image.mpr ⟨(b,c), mem_product.mpr ⟨Nat.mem_divisors.mpr ⟨hb,hd⟩,
      mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨hc,he⟩, le_trans (by exact_mod_cast hcle) hX⟩⟩, hbc.symm⟩
  calc
    _ ≤ ((d.divisors ×ˢ truncatedDivisors X e).image (fun bc => bc.1 * bc.2)).card := card_le_card hsub
    _ ≤ (d.divisors ×ˢ truncatedDivisors X e).card := card_image_le
    _ = _ := by simp [truncatedDivisorCount]

end ShortEgyptian

end OAI

-- ---- platform node ----
open OAI OAI.ShortEgyptian
open scoped BigOperators
open Finset


theorem solution : type_of% @_root_.OAI.ShortEgyptian.truncatedDivisors_mul := @_root_.OAI.ShortEgyptian.truncatedDivisors_mul
