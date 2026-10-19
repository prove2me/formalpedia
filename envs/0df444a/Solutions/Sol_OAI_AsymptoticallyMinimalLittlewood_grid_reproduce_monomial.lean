-- Prove2me | solution 1 for OAI.AsymptoticallyMinimalLittlewood.grid_reproduce_monomial
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T06:57:49.782294+00:00
-- url     : https://prove2.me/submissions/9daa5b3e-65ee-440d-a9e1-3606a23a5b42

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Littlewood/Rounding.lean:L1116-L1171
-- (upload_full_project.md Phase 4): solution for node OAI.AsymptoticallyMinimalLittlewood.grid_reproduce_monomial. The node keeps its source
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

/-- The cross-Dirichlet kernel reproduces each required nonnegative frequency. -/
theorem grid_reproduce_monomial {M N : ℕ} [NeZero M] (hNM : 2 * N ≤ M)
    (k : Fin N) {z : ℂ} (hz : ‖z‖ = 1) :
    (∑ j : ZMod M, ZMod.stdAddChar j ^ (k : ℕ) * gridDirichlet (2 * N) z j *
      conj (gridDirichlet N z j)) = (M : ℂ) * N * z ^ (k : ℕ) := by
  have hb (b : Fin N) : (∑ j : ZMod M,
      ZMod.stdAddChar j ^ (k : ℕ) * gridDirichlet (2 * N) z j *
        (conj (z ^ (b : ℕ)) * ZMod.stdAddChar j ^ (b : ℕ))) =
      (M : ℂ) * z ^ (k : ℕ) := by
    have hkb : (k : ℕ) + b < 2 * N := by omega
    let a₀ : Fin (2 * N) := ⟨(k : ℕ) + b, hkb⟩
    simp only [gridDirichlet, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    calc
      (∑ a : Fin (2 * N), ∑ j : ZMod M,
          ZMod.stdAddChar j ^ (k : ℕ) *
            (z ^ (a : ℕ) * conj (ZMod.stdAddChar j ^ (a : ℕ))) *
              (conj (z ^ (b : ℕ)) * ZMod.stdAddChar j ^ (b : ℕ))) =
        ∑ a : Fin (2 * N), (z ^ (a : ℕ) * conj (z ^ (b : ℕ))) *
          (∑ j : ZMod M, ZMod.stdAddChar j ^ ((k : ℕ) + b) *
            conj (ZMod.stdAddChar j ^ (a : ℕ))) := by
        apply Finset.sum_congr rfl
        intro a ha
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        rw [pow_add]
        ring
      _ = ∑ a : Fin (2 * N), if a = a₀ then
          (z ^ ((k : ℕ) + b) * conj (z ^ (b : ℕ))) * M else 0 := by
        apply Finset.sum_congr rfl
        intro a ha
        rw [grid_power_orthogonality (hkb.trans_le hNM) (a.isLt.trans_le hNM)]
        by_cases heq : a = a₀
        · subst a
          simp [a₀]
        · have hval : (k : ℕ) + b ≠ (a : ℕ) := fun h ↦ heq (Fin.ext h.symm)
          simp [heq, hval]
      _ = (M : ℂ) * z ^ (k : ℕ) := by
        simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
        rw [pow_add, mul_assoc (z ^ (k : ℕ)) (z ^ (b : ℕ)) (conj (z ^ (b : ℕ))),
          Complex.mul_conj, Complex.normSq_eq_norm_sq,
          norm_pow, hz]
        simp [mul_comm]
  calc
    _ = ∑ j : ZMod M, ∑ b : Fin N,
        ZMod.stdAddChar j ^ (k : ℕ) * gridDirichlet (2 * N) z j *
          (conj (z ^ (b : ℕ)) * ZMod.stdAddChar j ^ (b : ℕ)) := by
      apply Finset.sum_congr rfl
      intro j hj
      simp only [gridDirichlet, map_sum, map_mul, Complex.conj_conj, Finset.mul_sum]
    _ = ∑ b : Fin N, ∑ j : ZMod M,
        ZMod.stdAddChar j ^ (k : ℕ) * gridDirichlet (2 * N) z j *
          (conj (z ^ (b : ℕ)) * ZMod.stdAddChar j ^ (b : ℕ)) := Finset.sum_comm
    _ = ∑ _b : Fin N, (M : ℂ) * z ^ (k : ℕ) := Finset.sum_congr rfl (fun b _ ↦ hb b)
    _ = _ := by simp; ring

end

end AsymptoticallyMinimalLittlewood

end OAI

-- ---- platform node ----
open OAI OAI.AsymptoticallyMinimalLittlewood
open MeasureTheory Complex Real FourierTransform Filter Topology
open scoped FourierTransform SchwartzMap ContDiff
open scoped ComplexConjugate
open Finset


theorem solution : type_of% @_root_.OAI.AsymptoticallyMinimalLittlewood.grid_reproduce_monomial := @_root_.OAI.AsymptoticallyMinimalLittlewood.grid_reproduce_monomial
