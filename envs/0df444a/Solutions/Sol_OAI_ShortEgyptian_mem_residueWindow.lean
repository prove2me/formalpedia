-- Prove2me | solution 1 for OAI.ShortEgyptian.mem_residueWindow
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T01:39:11.808285+00:00
-- url     : https://prove2.me/submissions/063fc990-6c14-4b1d-8bdf-31205b7c9121

-- Generated from openai/math@1581d4c lean/OAI/NumberTheory/ShortEgyptian/WindowDiscrepancy.lean:L123-L135
-- (upload_full_project.md Phase 4): solution for node OAI.ShortEgyptian.mem_residueWindow. The node keeps its source
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

-- ---- from OAI.NumberTheory.ShortEgyptian.WindowDiscrepancy ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

namespace ShortEgyptian

open scoped BigOperators
open Finset

theorem mem_residueWindow {q : ℕ} [NeZero q] {δ : ℝ} (hδ1 : δ ≤ 1) (x : ZMod q) :
    x ∈ residueWindow q δ ↔ (x.val : ℝ) < δ * q := by
  have hceil : ⌈δ * (q : ℝ)⌉₊ ≤ q := Nat.ceil_le.mpr (by nlinarith [show (0 : ℝ) ≤ q by positivity])
  constructor
  · intro hx
    obtain ⟨n, hn, hncast⟩ := Finset.mem_image.mp hx
    have hn' := Finset.mem_range.mp hn
    have hnv : (n : ZMod q).val = n := ZMod.val_natCast_of_lt (hn'.trans_le hceil)
    rw [← hncast, hnv]
    exact Nat.lt_ceil.mp hn'
  · intro hx
    apply Finset.mem_image.mpr
    exact ⟨x.val, Finset.mem_range.mpr (Nat.lt_ceil.mpr hx), ZMod.natCast_zmod_val x⟩

end ShortEgyptian

end OAI

-- ---- platform node ----
open OAI OAI.ShortEgyptian
open scoped BigOperators
open Finset


theorem solution : type_of% @_root_.OAI.ShortEgyptian.mem_residueWindow := @_root_.OAI.ShortEgyptian.mem_residueWindow
