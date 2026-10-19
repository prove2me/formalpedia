-- Prove2me | solution 1 for OAI.AsymptoticallyMinimalLittlewood.grid_dirichlet_square
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T06:55:55.858404+00:00
-- url     : https://prove2.me/submissions/5d774d70-d249-4feb-a617-60bc51435a02

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Littlewood/Rounding.lean:L1066-L1110
-- (upload_full_project.md Phase 4): solution for node OAI.AsymptoticallyMinimalLittlewood.grid_dirichlet_square. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_AsymptoticallyMinimalLittlewood
import Definitions.Def_OAI_Analysis_Littlewood_Gaussian
import Definitions.Def_OAI_Analysis_Littlewood_Rounding
import Theorems.Thm_OAI_AsymptoticallyMinimalLittlewood_grid_power_orthogonality

-- ---- from OAI.Analysis.Littlewood.Rounding ----
-- Lean 4.34 name, proved using the Mathlib 0df444a lemma (same statement); as in oai-math-oct-2026.
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe u v w

namespace AsymptoticallyMinimalLittlewood
noncomputable section
open MeasureTheory Complex Real FourierTransform Filter Topology
open scoped FourierTransform SchwartzMap ContDiff

open scoped ComplexConjugate
open Finset

/-- Mean square of a translated Dirichlet kernel on an oversampling grid. -/
theorem grid_dirichlet_square {M n : ℕ} [NeZero M] (hn : n ≤ M)
    {z : ℂ} (hz : ‖z‖ = 1) :
    (∑ j : ZMod M, ‖∑ a : Fin n, z ^ (a : ℕ) * conj (ZMod.stdAddChar j ^ (a : ℕ))‖ ^ 2) =
      (M : ℝ) * n := by
  have hcomplex : (∑ j : ZMod M,
      (∑ a : Fin n, z ^ (a : ℕ) * conj (ZMod.stdAddChar j ^ (a : ℕ))) *
      conj (∑ a : Fin n, z ^ (a : ℕ) * conj (ZMod.stdAddChar j ^ (a : ℕ)))) =
      (M : ℂ) * n := by
    simp only [map_sum, map_mul, Complex.conj_conj, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Eq.trans ?_ (show (∑ a : Fin n, (M : ℂ)) = (M : ℂ) * n by simp [mul_comm])
    apply Finset.sum_congr rfl
    intro a ha
    rw [Finset.sum_comm]
    calc
      (∑ b : Fin n, ∑ j : ZMod M,
          z ^ (b : ℕ) * conj (ZMod.stdAddChar j ^ (b : ℕ)) *
            (conj (z ^ (a : ℕ)) * ZMod.stdAddChar j ^ (a : ℕ))) =
        ∑ b : Fin n, (z ^ (b : ℕ) * conj (z ^ (a : ℕ))) *
          (∑ j : ZMod M, ZMod.stdAddChar j ^ (a : ℕ) *
            conj (ZMod.stdAddChar j ^ (b : ℕ))) := by
          apply Finset.sum_congr rfl
          intro b hb
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j hj
          ring
      _ = ∑ b : Fin n, if b = a then (z ^ (a : ℕ) * conj (z ^ (a : ℕ))) * M else 0 := by
        apply Finset.sum_congr rfl
        intro b hb
        rw [grid_power_orthogonality (a.isLt.trans_le hn) (b.isLt.trans_le hn)]
        by_cases heq : b = a
        · subst b
          simp
        · have hval : (b : ℕ) ≠ (a : ℕ) := fun h ↦ heq (Fin.ext h)
          simp [heq, Ne.symm hval]
      _ = (M : ℂ) := by
        simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
        rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, norm_pow, hz]
        simp
  have hreal := congrArg Complex.re hcomplex
  simpa only [Complex.mul_conj, Complex.normSq_eq_norm_sq, ← Complex.ofReal_pow,
    ← Complex.ofReal_sum, Complex.ofReal_re, Complex.mul_re,
    Complex.natCast_re, Complex.natCast_im, mul_zero, sub_zero] using hreal

end

end AsymptoticallyMinimalLittlewood

end OAI

-- ---- platform node ----
open OAI OAI.AsymptoticallyMinimalLittlewood
open MeasureTheory Complex Real FourierTransform Filter Topology
open scoped FourierTransform SchwartzMap ContDiff
open scoped ComplexConjugate
open Finset


theorem solution : type_of% @_root_.OAI.AsymptoticallyMinimalLittlewood.grid_dirichlet_square := @_root_.OAI.AsymptoticallyMinimalLittlewood.grid_dirichlet_square
