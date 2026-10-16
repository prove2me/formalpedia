-- Prove2me | solution 1 for OAI.ShortEgyptian.convolution_discrepancy
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T01:35:13.667649+00:00
-- url     : https://prove2.me/submissions/ffa53f23-e5e8-410e-9f52-6dc3640db4f0

-- Generated from openai/math@1581d4c lean/OAI/NumberTheory/ShortEgyptian/FourierDiscrepancy.lean:L90-L136
-- (upload_full_project.md Phase 4): solution for node OAI.ShortEgyptian.convolution_discrepancy. The node keeps its source
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

-- ---- from OAI.NumberTheory.ShortEgyptian.FiniteFourier ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe uι uG

namespace ShortEgyptian

open scoped BigOperators
open Finset

theorem additive_orthogonality {q : ℕ} [NeZero q] (t : ZMod q) :
    (∑ x : ZMod q, ZMod.stdAddChar (t * x)) = if t = 0 then (q : ℂ) else 0 := by
  split_ifs with ht
  · simp [ht]
  · exact AddChar.sum_eq_zero_of_ne_one (ZMod.isPrimitive_stdAddChar q ht)

end ShortEgyptian

end OAI

-- ---- from OAI.NumberTheory.ShortEgyptian.FourierDiscrepancy ----
namespace OAI

namespace ShortEgyptian

open scoped BigOperators
open Finset

theorem convolution_fourier {q : ℕ} [NeZero q] (A B : Finset (ZMod q))
    (μ : ZMod q → ℝ) :
    ∑ k : ZMod q, charSum A k * charSum B k * probabilityFourier μ k =
      (q : ℂ) * (∑ a ∈ A, ∑ b ∈ B, (μ (a + b) : ℂ)) := by
  classical
  have horth (a b : ZMod q) :
      (∑ k : ZMod q, ZMod.stdAddChar (k * a) * ZMod.stdAddChar (k * b) *
        probabilityFourier μ k) = (q : ℂ) * μ (a + b) := by
    have hterm (k x : ZMod q) :
        ZMod.stdAddChar (k * a) * ZMod.stdAddChar (k * b) *
          ((μ x : ℂ) * ZMod.stdAddChar (-(k * x))) =
        (μ x : ℂ) * ZMod.stdAddChar ((a + b - x) * k) := by
      rw [show (a + b - x) * k = k * a + k * b + -(k * x) by ring]
      simp only [AddChar.map_add_eq_mul]
      ring
    simp only [probabilityFourier, Finset.mul_sum, hterm]
    rw [Finset.sum_comm]
    simp only [← Finset.mul_sum, additive_orthogonality, sub_eq_zero]
    simp only [mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    ring
  calc
    _ = ∑ k : ZMod q, ∑ a ∈ A, ∑ b ∈ B,
        ZMod.stdAddChar (k * a) * ZMod.stdAddChar (k * b) * probabilityFourier μ k := by
      apply Finset.sum_congr rfl
      intro k _
      simp only [charSum, ← Finset.sum_mul, ← Finset.mul_sum]
    _ = ∑ a ∈ A, ∑ k : ZMod q, ∑ b ∈ B,
        ZMod.stdAddChar (k * a) * ZMod.stdAddChar (k * b) * probabilityFourier μ k := Finset.sum_comm
    _ = ∑ a ∈ A, ∑ b ∈ B, ∑ k : ZMod q,
        ZMod.stdAddChar (k * a) * ZMod.stdAddChar (k * b) * probabilityFourier μ k := by
      apply Finset.sum_congr rfl
      intro a _
      exact Finset.sum_comm
    _ = _ := by simp only [horth, Finset.mul_sum]

theorem convolution_discrepancy {q : ℕ} [NeZero q] (A B I : Finset (ZMod q))
    (μ : ZMod q → ℝ) (hμ : ∀ x, 0 ≤ μ x) (hmass : ∑ x, μ x = 1)
    (hsupport : ∀ a ∈ A, ∀ b ∈ B, a + b ∈ I) :
    (A.card : ℝ) * B.card -
        ∑ k ∈ (Finset.univ : Finset (ZMod q)).erase 0,
          ‖charSum A k‖ * ‖charSum B k‖ * ‖probabilityFourier μ k‖ ≤
      (q : ℝ) * B.card * ∑ x ∈ I, μ x := by
  classical
  let W : ℝ := ∑ a ∈ A, ∑ b ∈ B, μ (a + b)
  have hW : W ≤ (B.card : ℝ) * ∑ x ∈ I, μ x := by
    dsimp only [W]
    rw [Finset.sum_comm]
    calc
      _ ≤ ∑ b ∈ B, ∑ x ∈ I, μ x := by
        apply Finset.sum_le_sum
        intro b hb
        calc
          _ = ∑ x ∈ A.image (fun a => a + b), μ x := by
            rw [Finset.sum_image]
            intro a _ a' _ heq
            exact add_right_cancel heq
          _ ≤ ∑ x ∈ I, μ x := by
            apply Finset.sum_le_sum_of_subset_of_nonneg
            · intro x hx
              obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
              exact hsupport a ha b hb
            · intro x _ _
              exact hμ x
      _ = _ := by simp [nsmul_eq_mul]
  have hFourier := convolution_fourier A B μ
  have hzero : charSum A 0 * charSum B 0 * probabilityFourier μ 0 =
      (A.card : ℂ) * B.card := by simp [probabilityFourier_zero μ hmass]
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : ZMod q)), hzero] at hFourier
  have hreal : (q : ℝ) * W = (A.card : ℝ) * B.card +
      (∑ k ∈ (Finset.univ : Finset (ZMod q)).erase 0,
        charSum A k * charSum B k * probabilityFourier μ k).re := by
    have hh := congrArg Complex.re hFourier
    simpa [W, Complex.mul_re, Complex.mul_im] using hh.symm
  have hn := norm_sum_le ((Finset.univ : Finset (ZMod q)).erase 0)
    (fun k => charSum A k * charSum B k * probabilityFourier μ k)
  simp only [norm_mul] at hn
  have hre := Complex.re_le_norm
    (-(∑ k ∈ (Finset.univ : Finset (ZMod q)).erase 0,
      charSum A k * charSum B k * probabilityFourier μ k))
  simp only [Complex.neg_re, norm_neg] at hre
  have hqW := mul_le_mul_of_nonneg_left hW (by positivity : (0 : ℝ) ≤ q)
  nlinarith

end ShortEgyptian

end OAI

-- ---- platform node ----
open OAI OAI.ShortEgyptian
open scoped BigOperators
open Finset


theorem solution : type_of% @_root_.OAI.ShortEgyptian.convolution_discrepancy := @_root_.OAI.ShortEgyptian.convolution_discrepancy
