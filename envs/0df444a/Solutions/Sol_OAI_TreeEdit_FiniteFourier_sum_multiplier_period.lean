-- Prove2me | solution 1 for OAI.TreeEdit.FiniteFourier.sum_multiplier_period
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T03:04:01.289143+00:00
-- url     : https://prove2.me/submissions/c0b6bee4-ef59-4297-8176-acf8a291bf80

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/TreeEdit/FiniteFourier.lean:L376-L389
-- (upload_full_project.md Phase 4): solution for node OAI.TreeEdit.FiniteFourier.sum_multiplier_period. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_TreeEdit
import Definitions.Def_OAI_Combinatorics_TreeEdit_Model
import Definitions.Def_OAI_Combinatorics_TreeEdit_FiniteProbability
import Definitions.Def_OAI_Combinatorics_TreeEdit_EditMetric
import Definitions.Def_OAI_Combinatorics_TreeEdit_Alignments
import Definitions.Def_OAI_Combinatorics_TreeEdit_SegmentComparison
import Definitions.Def_OAI_Combinatorics_TreeEdit_CyclicWords
import Definitions.Def_OAI_Combinatorics_TreeEdit_TreeArithmetic
import Definitions.Def_OAI_Combinatorics_TreeEdit_CircleTree
import Definitions.Def_OAI_Combinatorics_TreeEdit_CircleSeparation
import Definitions.Def_OAI_Combinatorics_TreeEdit_RandomCircle
import Definitions.Def_OAI_Combinatorics_TreeEdit_FiniteFourier

-- ---- from OAI.Combinatorics.TreeEdit.FiniteFourier ----
namespace OAI

namespace TreeEdit

universe u

attribute [local instance] Classical.propDecidable

namespace FiniteFourier

open scoped ComplexConjugate
open RCLike

variable {A : Type*} [Fintype A] [AddCommGroup A]

lemma multiplier_eq (χ : AddChar A ℂ) (z : A) :
    multiplier χ z = 2 - 2 * (χ z).re := by
  rw [multiplier, Complex.sq_norm, Complex.normSq_sub]
  norm_num [Complex.normSq_eq_norm_sq, χ.norm_apply]

end FiniteFourier

namespace FiniteFourier

variable {A B : Type*} [Fintype A] [Fintype B] [AddCommGroup A] [AddCommGroup B]

lemma sum_multiplier_period (χ : AddChar A ℂ) (v : A) (n : ℕ)
    (hne : χ v ≠ 1) (hper : (χ v) ^ n = 1) :
    ∑ s ∈ Finset.range n, multiplier χ ((s + 1) • v) = 2 * n := by
  have hs : ∑ s ∈ Finset.range n, (χ v) ^ s = 0 := by
    have hh := geom_sum_mul (χ v) n
    rw [hper, sub_self] at hh
    exact (mul_eq_zero.mp hh).resolve_right (sub_ne_zero.mpr hne)
  have hs' : ∑ s ∈ Finset.range n, χ ((s + 1) • v) = 0 := by
    simp only [AddChar.map_nsmul_eq_pow, pow_succ, ← Finset.sum_mul, hs, zero_mul]
  have hr : ∑ s ∈ Finset.range n, (χ ((s + 1) • v)).re = 0 := by
    simpa only [Complex.re_sum, Complex.zero_re] using congrArg Complex.re hs'
  simp only [multiplier_eq, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range,
    nsmul_eq_mul, ← Finset.mul_sum, hr, mul_zero, sub_zero]
  ring

end FiniteFourier

namespace FiniteFourier

variable {A B : Type*} [Fintype A] [Fintype B] [AddCommGroup A] [AddCommGroup B]

end FiniteFourier

namespace FiniteFourier

variable {A : Type*} [Fintype A] [AddCommGroup A]

end FiniteFourier

end TreeEdit

end OAI

-- ---- platform node ----
open OAI OAI.TreeEdit OAI.TreeEdit.FiniteFourier
attribute [local instance] Classical.propDecidable


theorem solution : type_of% @_root_.OAI.TreeEdit.FiniteFourier.sum_multiplier_period := @_root_.OAI.TreeEdit.FiniteFourier.sum_multiplier_period
