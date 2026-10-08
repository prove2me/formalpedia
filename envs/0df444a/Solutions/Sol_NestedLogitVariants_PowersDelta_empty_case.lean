-- Prove2me | solution 1 for NestedLogitVariants.PowersDelta.empty_case
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-07T13:21:16.287027+00:00
-- url     : https://prove2.me/submissions/c216f7f2-a081-46ce-88bb-4e973f8ca8b8

import Mathlib
import Definitions.Def_NestedLogitVariants_PowersDelta_Levels

set_option autoImplicit false

namespace NestedLogitVariants.PowersDelta

private theorem prep_V_nonneg {ι : Type*} {n : ℕ} (I : Instance ι n) (hI : I.Standing)
    (i : ι) (S : Finset (Fin n)) : 0 ≤ V I i S :=
  add_nonneg (hI.vnp_nonneg i) (Finset.sum_nonneg fun j _ => (hI.v_pos i j).le)

private theorem prep_R_nonneg {ι : Type*} {n : ℕ} (I : Instance ι n) (hI : I.Standing)
    (i : ι) (S : Finset (Fin n)) : 0 ≤ R I i S := by
  exact div_nonneg (Finset.sum_nonneg fun j _ =>
    mul_nonneg (hI.r_nonneg i j) (hI.v_pos i j).le) (prep_V_nonneg I hI i S)

private theorem prep_lp4_opt_nonneg {ι : Type*} [Fintype ι] {n : ℕ} (I : Instance ι n)
    (hI : I.Standing) (A : ι → Set (Finset (Fin n))) (xh : ℝ) (yh : ι → ℝ)
    (hopt : LP4Optimal I A xh yh) : 0 ≤ xh := by
  have hfeas : LP4Feasible I A (2 * xh) (fun i => 2 * yh i) := by
    constructor
    · rw [← Finset.mul_sum]
      nlinarith [hopt.1.1]
    · intro i S hS
      have hc := hopt.1.2 i S hS
      have hwr : 0 ≤ nestWeight I i S * R I i S :=
        mul_nonneg (Real.rpow_nonneg (prep_V_nonneg I hI i S) _) (prep_R_nonneg I hI i S)
      nlinarith
  have hm := hopt.2 (2 * xh) (fun i => 2 * yh i) hfeas
  linarith

private theorem xh_nonneg {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ} [NeZero n] (I : Instance ι n)
    (hI : I.Standing) (γbar : ℝ) (hγbar : IsGreatest (Set.range I.γ) γbar) (hγbar1 : 1 < γbar)
    (δ : ℝ) (hδ : 1 < δ)
    (Sh : ι → ℤ → Finset (Fin n)) (hSh : IsPowersFamily I δ Sh)
    (xh : ℝ) (yh : ι → ℝ) (hopt : LP4Optimal I (powersCandidates I δ Sh) xh yh) :
    0 ≤ xh :=
  prep_lp4_opt_nonneg I hI _ xh yh hopt

end NestedLogitVariants.PowersDelta

open NestedLogitVariants.PowersDelta

theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ} [NeZero n] (I : Instance ι n)
    (hI : I.Standing) (γbar : ℝ) (hγbar : IsGreatest (Set.range I.γ) γbar) (hγbar1 : 1 < γbar)
    (δ : ℝ) (hδ : 1 < δ)
    (Sh : ι → ℤ → Finset (Fin n)) (hSh : IsPowersFamily I δ Sh)
    (xh : ℝ) (yh : ι → ℝ) (hopt : LP4Optimal I (powersCandidates I δ Sh) xh yh)
    (i : ι) :
    nestWeight I i ∅ * (R I i ∅ - δ ^ (2 * γbar + 1) * xh) ≤ δ ^ (γbar + 1) * yh i := by
  have hδ0 : 0 < δ := zero_lt_one.trans hδ
  have hx : 0 ≤ xh := xh_nonneg I hI γbar hγbar hγbar1 δ hδ Sh hSh xh yh hopt
  have hw : 0 ≤ nestWeight I i ∅ := Real.rpow_nonneg (prep_V_nonneg I hI i ∅) _
  have hscale : δ ^ (γbar + 1) ≤ δ ^ (2 * γbar + 1) :=
    Real.rpow_le_rpow_of_exponent_le hδ.le (by linarith)
  have hnegative := mul_le_mul_of_nonneg_right hscale (mul_nonneg hw hx)
  have hfeas := hopt.1.2 i ∅ (Or.inr rfl)
  have hscaled := mul_le_mul_of_nonneg_left hfeas (Real.rpow_nonneg hδ0.le (γbar + 1))
  have hR : R I i ∅ = 0 := by simp [R]
  rw [hR] at hscaled ⊢
  nlinarith
