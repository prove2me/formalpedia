-- Prove2me | solution 1 for GrothendieckLB.eq_35_36
-- status  : ACCEPTED   (prove)
-- author  : @Mr Robbins
-- created : 2026-11-23T04:01:17.39007+00:00
-- url     : https://prove2.me/submissions/389dc2c4-c3ed-4e90-b272-baf373b8bf32

import Mathlib
import Definitions.Def_GrothendieckLB_IsSignFn
import Definitions.Def_GrothendieckLB_agreePart
import Definitions.Def_GrothendieckLB_disagreePart
import Definitions.Def_GrothendieckLB_B1
import Definitions.Def_GrothendieckLB_D1
import Definitions.Def_GrothendieckLB_p1Inner
import Definitions.Def_GrothendieckLB_p3Inner
import Definitions.Def_ABPOnline_cG
import Theorems.Thm_GrothendieckLB_agreement_disagreement_bound
import Theorems.Thm_GrothendieckLB_corollary_8_2
import Theorems.Thm_GrothendieckLB_theorem_8_4
import Theorems.Thm_GrothendieckLB_theorem_8_5
import Theorems.Thm_GrothendieckLB_eq_43
import Theorems.Thm_GrothendieckLB_linear_mass_bound

namespace GrothendieckLB

/-- Cauchy--Schwarz for the finite coordinate vectors defining `p1Inner`. -/
lemma eq3536_abs_p1Inner_le {d : ℕ} (f g : (Fin d → ℝ) → ℝ) :
    |p1Inner f g| ≤ p1Norm f * p1Norm g := by
  let a : Fin d → ℝ := linearMoment f
  let b : Fin d → ℝ := linearMoment g
  have hcs : (∑ i, a i * b i) ^ 2 ≤ (∑ i, a i ^ 2) * (∑ i, b i ^ 2) :=
    Finset.sum_mul_sq_le_sq_mul_sq _ _ _
  have ha : 0 ≤ ∑ i, a i ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hb : 0 ≤ ∑ i, b i ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hsa : Real.sqrt (∑ i, a i ^ 2) ^ 2 = ∑ i, a i ^ 2 := Real.sq_sqrt ha
  have hsb : Real.sqrt (∑ i, b i ^ 2) ^ 2 = ∑ i, b i ^ 2 := Real.sq_sqrt hb
  have hprod : (Real.sqrt (∑ i, a i ^ 2) * Real.sqrt (∑ i, b i ^ 2)) ^ 2 =
      (∑ i, a i ^ 2) * (∑ i, b i ^ 2) := by rw [mul_pow, hsa, hsb]
  have hnonneg : 0 ≤ Real.sqrt (∑ i, a i ^ 2) * Real.sqrt (∑ i, b i ^ 2) :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have habs : |∑ i, a i * b i| ≤
      Real.sqrt (∑ i, a i ^ 2) * Real.sqrt (∑ i, b i ^ 2) := by
    rw [abs_le]
    constructor <;> nlinarith
  change |∑ i, a i * b i| ≤
    Real.sqrt (∑ i, a i * a i) * Real.sqrt (∑ i, b i * b i)
  simpa only [sq] using habs

end GrothendieckLB

open GrothendieckLB

theorem solution {d : ℕ} {f g : (Fin d → ℝ) → ℝ} (hf : IsSignFn f) (hg : IsSignFn g) :
    D1 (agreePart f g) (disagreePart f g) ≤ 11 / 6 * ABPOnline.cG ^ 2 ∧
    B1 f g ≤ 11 / 6 * ABPOnline.cG ^ 2 ∧
    2 * p1Inner f g - p3Inner f g ≤ 11 / 6 * ABPOnline.cG ^ 2 := by
  let h : (Fin d → ℝ) → ℝ := agreePart f g
  let k : (Fin d → ℝ) → ℝ := disagreePart f g
  let ν : ℝ := ABPOnline.cG
  let x : ℝ := p1Norm h / ν
  have hνpos : 0 < ν := by
    dsimp [ν, ABPOnline.cG]
    exact Real.sqrt_pos.2 (div_pos (by norm_num) Real.pi_pos)
  have hνsq : ν ^ 2 ≠ 0 := pow_ne_zero _ hνpos.ne'
  have hh : IsTernaryFn h := by
    refine ⟨?_, ?_⟩
    · exact (hf.1.add hg.1).div_const 2
    · intro z
      rcases hf.2 z with hfz | hfz <;> rcases hg.2 z with hgz | hgz <;>
        norm_num [h, agreePart, hfz, hgz]
  have hhbound : ∀ z, |h z| ≤ 1 := by
    intro z
    rcases hh.2 z with hz | hz | hz <;> simp [hz]
  have hp1nonneg : 0 ≤ p1Norm h := Real.sqrt_nonneg _
  have hx0 : 0 ≤ x := div_nonneg hp1nonneg hνpos.le
  have hx1 : x ≤ 1 := by
    apply (div_le_one hνpos).2
    exact (linear_mass_bound d).1 h hh.1 hhbound
  have hdiag := (corollary_8_2 hh).2
  have hres1 : p3NormSq k ≤
      ν ^ 2 * (3 * (1 - x) - (1 - x) ^ 2) := by
    simpa [h, k, x, ν] using theorem_8_4 hf hg
  have hres2 : p3NormSq k ≤ Pfun x := by
    simpa [h, k, x, ν] using theorem_8_5 hf hg
  have hres : p3NormSq k ≤ ν ^ 2 * Rfun x := by
    change p3NormSq k ≤ ν ^ 2 *
      min (3 * (1 - x) - (1 - x) ^ 2) ((1 / ν ^ 2) * Pfun x)
    by_cases hbranch : 3 * (1 - x) - (1 - x) ^ 2 ≤ (1 / ν ^ 2) * Pfun x
    · simpa only [min_eq_left hbranch] using hres1
    · have hbranch' : (1 / ν ^ 2) * Pfun x ≤ 3 * (1 - x) - (1 - x) ^ 2 :=
        le_of_not_ge hbranch
      simp only [min_eq_right hbranch']
      calc
        p3NormSq k ≤ Pfun x := hres2
        _ = ν ^ 2 * ((1 / ν ^ 2) * Pfun x) := by field_simp
  have hD_scaled : D1 h k ≤ ν ^ 2 * E1 x := by
    calc
      D1 h k = (2 * p1Norm h ^ 2 - p3NormSq h) + p3NormSq k := by
        unfold D1
        ring
      _ ≤ ν ^ 2 * (2 * x ^ 2 - DeltaPlus x ^ 2 / 6) + ν ^ 2 * Rfun x :=
        add_le_add (by simpa [x, ν] using hdiag) hres
      _ = ν ^ 2 * E1 x := by
        unfold E1
        ring
  have hD : D1 h k ≤ 11 / 6 * ν ^ 2 := by
    calc
      D1 h k ≤ ν ^ 2 * E1 x := hD_scaled
      _ ≤ ν ^ 2 * (11 / 6) :=
        mul_le_mul_of_nonneg_left (eq_43.1 x ⟨hx0, hx1⟩) (sq_nonneg ν)
      _ = 11 / 6 * ν ^ 2 := by ring
  have hB : B1 f g ≤ 11 / 6 * ν ^ 2 :=
    (agreement_disagreement_bound hf hg).trans (by simpa [h, k] using hD)
  refine ⟨?_, hB, ?_⟩
  · simpa [h, k, ν] using hD
  · have hcs : p1Inner f g ≤ p1Norm f * p1Norm g :=
      (le_abs_self _).trans (eq3536_abs_p1Inner_le f g)
    dsimp [B1] at hB
    simpa [ν] using (show 2 * p1Inner f g - p3Inner f g ≤ 11 / 6 * ν ^ 2 by linarith)
