-- Prove2me | solution 1 for OAI.AsymptoticallyMinimalLittlewood.defect_rounding
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T07:02:07.16841+00:00
-- url     : https://prove2.me/submissions/35c760b6-f284-490f-9aed-5cfb320d63fb

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Littlewood/Rounding.lean:L1233-L1369
-- (upload_full_project.md Phase 4): solution for node OAI.AsymptoticallyMinimalLittlewood.defect_rounding. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_AsymptoticallyMinimalLittlewood
import Definitions.Def_OAI_Analysis_Littlewood_Gaussian
import Definitions.Def_OAI_Analysis_Littlewood_Rounding
import Theorems.Thm_OAI_AsymptoticallyMinimalLittlewood_matrix_defect_rounding
import Theorems.Thm_OAI_AsymptoticallyMinimalLittlewood_polynomial_grid_bound

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

theorem defect_rounding {N : ℕ} (hN : 1 ≤ N) (X : Fin N → ℝ)
    (hX : ∀ k, |X k| ≤ 1) :
    ∃ ε : Fin N → ℝ, IsRealSigning ε ∧
      ∀ z : ℂ, ‖z‖ = 1 →
        ‖littlewoodValue ε z - littlewoodValue X z‖ ≤
          196608 * (1 + Real.sqrt (defectMass X * Real.log (80 * N / defectMass X))) := by
  classical
  let μ := defectMass X
  have hμ0 : 0 ≤ μ := by
    dsimp [μ, defectMass]
    exact div_nonneg (Finset.sum_nonneg fun k _ ↦ sub_nonneg.mpr (hX k)) (by norm_num)
  have hμN : 2 * μ ≤ N := by
    have hh : (∑ k : Fin N, (1 - |X k|)) ≤ ∑ _k : Fin N, (1 : ℝ) :=
      Finset.sum_le_sum fun k _ ↦ by linarith [abs_nonneg (X k)]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one] at hh
    dsimp [μ, defectMass]
    linarith
  by_cases hμzero : μ = 0
  · have hsumzero : (∑ k : Fin N, (1 - |X k|)) = 0 := by dsimp [μ, defectMass] at hμzero; linarith
    have hxone (k : Fin N) : |X k| = 1 := by
      have hk := (Finset.sum_eq_zero_iff_of_nonneg
        (fun k (_ : k ∈ (Finset.univ : Finset (Fin N))) ↦ sub_nonneg.mpr (hX k))).mp hsumzero k (Finset.mem_univ k)
      linarith
    refine ⟨X, ?_, ?_⟩
    · intro k
      by_cases hk : 0 ≤ X k
      · exact Or.inr (by simpa only [abs_of_nonneg hk] using hxone k)
      · exact Or.inl (by have := hxone k; rw [abs_of_neg (lt_of_not_ge hk)] at this; linarith)
    · intro z hz
      rw [sub_self, norm_zero]
      positivity
  have hμ : 0 < μ := lt_of_le_of_ne hμ0 (Ne.symm hμzero)
  let σ : Fin N → ℝ := fun k ↦ if 0 ≤ X k then 1 else -1
  let p : Fin N → ℝ := fun k ↦ (1 - |X k|) / 2
  have hσ (k : Fin N) : σ k = -1 ∨ σ k = 1 := by dsimp [σ]; split_ifs <;> simp
  have hσabs (k : Fin N) : |σ k| = 1 := by rcases hσ k with hk | hk <;> simp [hk]
  have hp (k : Fin N) : 0 ≤ p k ∧ p k ≤ 1 := by
    dsimp [p]
    constructor <;> linarith [hX k, abs_nonneg (X k)]
  have hXp (k : Fin N) : σ k * (1 - 2 * p k) = X k := by
    dsimp [σ, p]
    split_ifs with hk
    · rw [abs_of_nonneg hk]
      ring
    · rw [abs_of_neg (lt_of_not_ge hk)]
      ring
  have hmass : (∑ k, p k) = μ := by dsimp [p, μ, defectMass]; rw [Finset.sum_div]
  let M := 20 * N
  have hM : M ≠ 0 := by dsimp [M]; omega
  let : NeZero M := ⟨hM⟩
  let A : (ZMod M × Bool) → Fin N → ℝ := fun i k ↦
    σ k * (if i.2 then (ZMod.stdAddChar i.1 ^ (k : ℕ)).im else (ZMod.stdAddChar i.1 ^ (k : ℕ)).re)
  have hrootnorm (j : ZMod M) : ‖ZMod.stdAddChar j‖ = 1 := Circle.norm_coe (ZMod.toCircle j)
  have hA (i : ZMod M × Bool) (k : Fin N) : |A i k| ≤ 1 := by
    dsimp [A]
    rw [abs_mul, hσabs, one_mul]
    split_ifs
    · calc
        _ ≤ ‖ZMod.stdAddChar i.1 ^ (k : ℕ)‖ := Complex.abs_im_le_norm _
        _ = 1 := by rw [norm_pow, hrootnorm]; simp
    · calc
        _ ≤ ‖ZMod.stdAddChar i.1 ^ (k : ℕ)‖ := Complex.abs_re_le_norm _
        _ = 1 := by rw [norm_pow, hrootnorm]; simp
  have hcard : Fintype.card (ZMod M × Bool) = 40 * N := by
    simp [Fintype.card_prod, ZMod.card, M]
    omega
  have hNR : Fintype.card (Fin N) ≤ Fintype.card (ZMod M × Bool) := by rw [hcard, Fintype.card_fin]; omega
  have hμR : 2 * μ ≤ Fintype.card (ZMod M × Bool) := by
    rw [hcard]
    push_cast
    nlinarith [show (0 : ℝ) ≤ N from Nat.cast_nonneg N]
  obtain ⟨p', hp', hmass', herr⟩ := matrix_defect_rounding A hA hNR p hp hμ hμR hmass.le
  let ε : Fin N → ℝ := fun k ↦ σ k * (1 - 2 * p' k)
  have hε : IsRealSigning ε := by
    intro k
    rcases hp' k with hp'k | hp'k <;> rcases hσ k with hσk | hσk <;> norm_num [IsRealSigning, ε, hp'k, hσk]
  let D := 1 + 24576 * Real.sqrt (μ * Real.log (80 * N / μ))
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have herr' (i : ZMod M × Bool) : |∑ k, A i k * (p' k - p k)| ≤ D := by
    have hh := herr i
    rw [hcard] at hh
    push_cast at hh
    convert hh using 1; dsimp [D]; congr 3; ring_nf
  let E : ZMod M → ℂ := fun j ↦ ∑ k, ((σ k * (p' k - p k) : ℝ) : ℂ) * ZMod.stdAddChar j ^ (k : ℕ)
  have hEre (j : ZMod M) : (E j).re = ∑ k, A (j, false) k * (p' k - p k) := by
    dsimp [E, A]
    simp only [Complex.re_sum, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    apply Finset.sum_congr rfl
    intro k hk
    ring
  have hEim (j : ZMod M) : (E j).im = ∑ k, A (j, true) k * (p' k - p k) := by
    dsimp [E, A]
    simp only [Complex.im_sum, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
    apply Finset.sum_congr rfl
    intro k hk
    ring
  have hEnorm (j : ZMod M) : ‖E j‖ ≤ 2 * D := by
    calc
      _ ≤ |(E j).re| + |(E j).im| := Complex.norm_le_abs_re_add_abs_im _
      _ ≤ D + D := by rw [hEre, hEim]; exact add_le_add (herr' (j, false)) (herr' (j, true))
      _ = _ := by ring
  have hcoef (k : Fin N) : ε k - X k = -2 * (σ k * (p' k - p k)) := by
    have hh := hXp k
    dsimp [ε]
    nlinarith
  have hgrid (j : ZMod M) : ‖∑ k : Fin N, ((ε k - X k : ℝ) : ℂ) *
      ZMod.stdAddChar j ^ (k : ℕ)‖ ≤ 4 * D := by
    have heq : (∑ k : Fin N, ((ε k - X k : ℝ) : ℂ) * ZMod.stdAddChar j ^ (k : ℕ)) =
        (-2 : ℂ) * E j := by
      dsimp [E]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      rw [hcoef]
      push_cast
      ring
    rw [heq, norm_mul]
    norm_num
    nlinarith [hEnorm j]
  refine ⟨ε, hε, fun z hz ↦ ?_⟩
  have hpoly := polynomial_grid_bound (M := M) (by omega : 0 < N)
    (by dsimp [M]; omega : 2 * N ≤ M) (fun k ↦ ((ε k - X k : ℝ) : ℂ))
    (show 0 ≤ 4 * D by positivity) hgrid hz
  have heq : littlewoodValue ε z - littlewoodValue X z =
      ∑ k : Fin N, ((ε k - X k : ℝ) : ℂ) * z ^ (k : ℕ) := by
    dsimp [littlewoodValue]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    push_cast
    ring
  rw [heq]
  apply hpoly.trans
  dsimp [D, μ]
  nlinarith [Real.sqrt_nonneg (defectMass X * Real.log (80 * N / defectMass X))]

end

end AsymptoticallyMinimalLittlewood

end OAI

-- ---- platform node ----
open OAI OAI.AsymptoticallyMinimalLittlewood
open MeasureTheory Complex Real FourierTransform Filter Topology
open scoped FourierTransform SchwartzMap ContDiff
open scoped ComplexConjugate
open Finset


theorem solution : type_of% @_root_.OAI.AsymptoticallyMinimalLittlewood.defect_rounding := @_root_.OAI.AsymptoticallyMinimalLittlewood.defect_rounding
