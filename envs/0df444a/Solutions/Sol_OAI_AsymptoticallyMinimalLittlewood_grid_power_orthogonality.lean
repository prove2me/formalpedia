-- Prove2me | solution 1 for OAI.AsymptoticallyMinimalLittlewood.grid_power_orthogonality
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T06:54:31.335584+00:00
-- url     : https://prove2.me/submissions/23fc60cd-efad-42e7-8d37-de9c52a3934f

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Littlewood/Rounding.lean:L1046-L1064
-- (upload_full_project.md Phase 4): solution for node OAI.AsymptoticallyMinimalLittlewood.grid_power_orthogonality. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_AsymptoticallyMinimalLittlewood
import Definitions.Def_OAI_Analysis_Littlewood_Gaussian
import Definitions.Def_OAI_Analysis_Littlewood_Rounding

-- ---- from OAI.Analysis.Littlewood.Rounding ----
-- Lean 4.34 name, proved using the Mathlib 0df444a lemma (same statement); as in oai-math-oct-2026.
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e
namespace OAI

universe u v w

namespace AsymptoticallyMinimalLittlewood
noncomputable section
open MeasureTheory Complex Real FourierTransform Filter Topology
open scoped FourierTransform SchwartzMap ContDiff

open scoped ComplexConjugate
open Finset

/-- Orthogonality of the exact full root-of-unity grid. -/
theorem grid_power_orthogonality {M a b : ℕ} [NeZero M] (ha : a < M) (hb : b < M) :
    (∑ j : ZMod M, ZMod.stdAddChar j ^ a * conj (ZMod.stdAddChar j ^ b)) =
      if a = b then (M : ℂ) else 0 := by
  have hpow (n : ℕ) (j : ZMod M) : ZMod.stdAddChar j ^ n =
      ZMod.stdAddChar ((n : ZMod M) * j) := by
    rw [← AddChar.map_nsmul_eq_pow, nsmul_eq_mul]
  have hconj (j : ZMod M) : conj (ZMod.stdAddChar j) = ZMod.stdAddChar (-j) := by
    rw [AddChar.map_neg_eq_inv, ZMod.stdAddChar_apply]
    exact (Circle.coe_inv_eq_conj (ZMod.toCircle j)).symm
  simp_rw [hpow, hconj, ← AddChar.map_add_eq_mul, ← sub_eq_add_neg, ← sub_mul]
  have hzero : ((a : ZMod M) - b = 0) ↔ a = b := by
    rw [sub_eq_zero, ZMod.natCast_eq_natCast_iff]
    simp only [Nat.ModEq, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]
  by_cases hab : a = b
  · subst b
    simp
  · rw [ite_eq_right hab]
    exact AddChar.sum_eq_zero_of_ne_one (ZMod.isPrimitive_stdAddChar M (mt hzero.mp hab))

end

end AsymptoticallyMinimalLittlewood

end OAI

-- ---- platform node ----
open OAI OAI.AsymptoticallyMinimalLittlewood
open MeasureTheory Complex Real FourierTransform Filter Topology
open scoped FourierTransform SchwartzMap ContDiff
open scoped ComplexConjugate
open Finset


theorem solution : type_of% @_root_.OAI.AsymptoticallyMinimalLittlewood.grid_power_orthogonality := @_root_.OAI.AsymptoticallyMinimalLittlewood.grid_power_orthogonality
