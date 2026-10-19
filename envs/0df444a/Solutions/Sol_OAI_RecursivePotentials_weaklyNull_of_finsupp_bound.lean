-- Prove2me | solution 1 for OAI.RecursivePotentials.weaklyNull_of_finsupp_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T08:57:10.381421+00:00
-- url     : https://prove2.me/submissions/f157196c-392b-4a3d-a316-de1896a8731d

-- Generated from openai/math@1581d4c lean/OAI/Analysis/RecursivePotentials/EquivalentNorms.lean:L347-L373
-- (upload_full_project.md Phase 4): solution for node OAI.RecursivePotentials.weaklyNull_of_finsupp_bound. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_RecursivePotentials
import Definitions.Def_OAI_Analysis_RecursivePotentials_Model
import Definitions.Def_OAI_Analysis_RecursivePotentials_TreeGeometry
import Definitions.Def_OAI_Analysis_RecursivePotentials_ZeroRootGeometry
import Definitions.Def_OAI_Analysis_RecursivePotentials_EquivalentNorms

-- ---- from OAI.Analysis.RecursivePotentials.EquivalentNorms ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe uIndex uSpace uOther uDomain uTarget uFiber

open scoped BigOperators

namespace RecursivePotentials

open Filter Topology

lemma weaklyNull_of_square_sum_bound {E : Type uSpace} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (d : ℕ → E) {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ (S : Finset ℕ) (a : ℕ → ℝ),
      ‖∑ i ∈ S, a i • d i‖ ≤ C * Real.sqrt (∑ i ∈ S, (a i) ^ 2)) : WeaklyNull d := by
  intro f
  have hs : Summable (fun i => (f (d i)) ^ 2) := by
    apply summable_of_sum_le (fun i => sq_nonneg (f (d i)))
      (c := (‖f‖ * C) ^ 2)
    intro S
    let q := ∑ i ∈ S, (f (d i)) ^ 2
    have hq : 0 ≤ q := Finset.sum_nonneg (fun i hi => sq_nonneg _)
    have hsq := Real.sq_sqrt hq
    have hb := h S (fun i => f (d i))
    have hf := f.le_opNorm (∑ i ∈ S, f (d i) • d i)
    have he : f (∑ i ∈ S, f (d i) • d i) = q := by
      simp only [map_sum, map_smul, smul_eq_mul, q, pow_two]
    rw [he, Real.norm_eq_abs, abs_of_nonneg hq] at hf
    have hmul := mul_le_mul_of_nonneg_left hb (norm_nonneg f)
    have hK : 0 ≤ ‖f‖ * C := mul_nonneg (norm_nonneg f) hC
    have hroot : Real.sqrt q ≤ ‖f‖ * C := by
      have hroot0 := Real.sqrt_nonneg q
      nlinarith
    change q ≤ (‖f‖ * C) ^ 2
    nlinarith [Real.sqrt_nonneg q]
  have hsqrt := Real.continuous_sqrt.continuousAt.tendsto.comp hs.tendsto_atTop_zero
  simp only [Function.comp_def, Real.sqrt_zero, Real.sqrt_sq_eq_abs] at hsqrt
  exact (tendsto_zero_iff_norm_tendsto_zero).mpr hsqrt

namespace EquivalentNorm

variable {E : Type uSpace} [NormedAddCommGroup E] [NormedSpace ℝ E] (A : EquivalentNorm E)

end EquivalentNorm

namespace FiniteRootedTree

variable {ι : Type uIndex} [indexDecidable : DecidableEq ι] (T : FiniteRootedTree ι)

end FiniteRootedTree

lemma weaklyNull_of_finsupp_bound {E : Type uSpace} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L : (ℕ →₀ ℝ) →ₗ[ℝ] E) {C : ℝ} (hC : 0 ≤ C)
    (hL : ∀ a, ‖L a‖ ≤ C * Real.sqrt (∑ k ∈ a.support, a k ^ 2)) :
    WeaklyNull (fun k => L (Finsupp.single k 1)) := by
  classical
  apply weaklyNull_of_square_sum_bound _ hC
  intro S a
  let b : ℕ →₀ ℝ := Finsupp.onFinset S (fun k => if k ∈ S then a k else 0)
    (by intro k hk; by_contra hn; simp [hn] at hk)
  have hb : b.support ⊆ S := Finsupp.support_onFinset_subset
  have he : b = ∑ k ∈ S, a k • Finsupp.single k 1 := by
    rw [← b.sum_single, b.sum_of_support_subset hb]
    · apply Finset.sum_congr rfl
      intro k hk
      simp [b, hk]
    · intro i hi; simp
  have hs : (∑ k ∈ b.support, b k ^ 2) = ∑ k ∈ S, a k ^ 2 := by
    calc
      _ = ∑ k ∈ S, b k ^ 2 := by
        apply Finset.sum_subset hb
        intro k hk hn
        rw [Finsupp.notMem_support_iff.mp hn]
        norm_num
      _ = _ := by apply Finset.sum_congr rfl; intro k hk; simp [b, hk]
  have h := hL b
  rw [hs, he, map_sum] at h
  simpa only [map_smul] using h

namespace TreeSpace

noncomputable section

variable {ι : Type uIndex} [indexDecidable : DecidableEq ι] (T : FiniteRootedTree ι)

open UniformSpace

end

end TreeSpace

namespace TreeSpace

noncomputable section

variable {ι : Type uIndex} [indexDecidable : DecidableEq ι] (T : FiniteRootedTree ι)

open UniformSpace

end

end TreeSpace

namespace ZeroTreeSpace

noncomputable section

variable {ι : Type uIndex} [indexDecidable : DecidableEq ι] (T : FiniteRootedTree ι)

open UniformSpace

end

end ZeroTreeSpace

namespace EquivalentNorm

variable {E : Type uSpace} [NormedAddCommGroup E] [NormedSpace ℝ E] (A : EquivalentNorm E)

end EquivalentNorm

end RecursivePotentials

end OAI

-- ---- platform node ----
open OAI OAI.RecursivePotentials
open scoped BigOperators
open Filter Topology


theorem solution.{uSpace} : type_of% @_root_.OAI.RecursivePotentials.weaklyNull_of_finsupp_bound.{uSpace} := @_root_.OAI.RecursivePotentials.weaklyNull_of_finsupp_bound.{uSpace}
