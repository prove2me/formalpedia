-- Prove2me | solution 1 for NahmiasPerishable.Inventory.m02
-- status  : ACCEPTED   (disprove)
-- author  : @kmehltretter82
-- created : 2026-11-09T12:12:04.895143+00:00
-- url     : https://prove2.me/submissions/399d28ba-81f2-4567-bbf3-64f913eabbc4

import Definitions.Def_NahmiasPerishable_Inventory_Cycles

open MeasureTheory Set
open NahmiasPerishable.Inventory

private lemma stockCost_zero (z : ℝ) :
    stockCost (Measure.dirac (0 : ℝ)) 0 0 z = 0 := by
  unfold stockCost ZhengQR.OrderQty.newsvendorCost
  have hfun : (fun d : ℝ => 0 * pos (z - d) + 0 * pos (d - z)) = fun _ => 0 := by
    ext d; ring
  have hfun2 : (fun x : ℝ => 0 * max (z - x) 0 + 0 * max (x - z) 0) = fun _ => 0 := by
    ext x; ring
  rw [if_pos (by rw [hfun]; exact integrable_zero _ _ _), hfun2, integral_zero]
  rfl

private lemma expectation_zero :
    expectation (Measure.dirac (0 : ℝ)) (fun _ : ℝ => (0 : EReal)) = 0 := by
  unfold expectation
  simp

private lemma value_eq_zero (n : ℕ) :
    (singlePeriodControl (Measure.dirac (0 : ℝ)) true 1 0 0 0 (1 / 2)).value n = fun _ => 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    ext x
    simp only [ShockControl.value, ih]
    dsimp only [singlePeriodControl]
    have hexp : expectation (Measure.dirac (0 : ℝ)) (fun _ : ℝ => (0 : EReal)) = 0 :=
      expectation_zero
    simp_rw [add_zero, stockCost_zero, add_zero, hexp, mul_zero, add_zero, one_mul]
    apply le_antisymm
    · exact iInf_le (fun y : {y : ℝ // 0 ≤ y} => (y.val : EReal)) ⟨0, le_rfl⟩
    · exact le_iInf (fun y : {y : ℝ // 0 ≤ y} => EReal.coe_nonneg.mpr y.2)

private lemma defined_zero :
    (singlePeriodControl (Measure.dirac (0 : ℝ)) true 1 0 0 0 (1 / 2)).defined
      {x | x ≤ 0 ∧ (true = false → x = 0)} := by
  intro n x _ y _
  rw [value_eq_zero]
  exact ⟨aemeasurable_const, Or.inl (by simp)⟩

set_option linter.unusedVariables false in
theorem solution : ¬ (∀ (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ : ∀ᵐ d ∂μ, 0 ≤ d) (b : Bool)
    (c h p theta alpha : ℝ) (hc : 0 ≤ c) (hh : 0 ≤ h) (hp : 0 ≤ p) (htheta : 0 ≤ theta)
    (halpha : 0 < alpha ∧ alpha < 1)
    (hdefined : (singlePeriodControl μ b c h p theta alpha).defined {x | x ≤ 0 ∧ (b = false → x = 0)}),
    ∃ z : ℕ → ℝ,
      (∀ j, 0 ≤ z j ∧ ∀ w, 0 ≤ w →
        singlePeriodNews μ b c h p theta alpha (decide (0 < j)) (z j) ≤
        singlePeriodNews μ b c h p theta alpha (decide (0 < j)) w) ∧
      (∀ n x, x ≤ 0 → (b = false → x = 0) →
        (singlePeriodControl μ b c h p theta alpha).optimal n x (z n-x)) ∧
      (∀ n x, 0 < n → x ≤ 0 → (b = false → x = 0) →
        (singlePeriodControl μ b c h p theta alpha).value n x = (-c*x : ℝ) +
          ∑ t ∈ Finset.range n, ((alpha^t : ℝ) : EReal) *
            singlePeriodNews μ b c h p theta alpha (decide (t+1 < n)) (z (n-1-t)))) := by
  intro h
  have hμ : ∀ᵐ d ∂(Measure.dirac (0 : ℝ)), 0 ≤ d := by
    rw [ae_iff]
    change (Measure.dirac (0 : ℝ)) (Ici (0 : ℝ))ᶜ = 0
    rw [Measure.dirac_apply' _ measurableSet_Ici.compl]
    simp
  rcases h (Measure.dirac (0 : ℝ)) hμ true 1 0 0 0 (1 / 2)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) ⟨by norm_num, by norm_num⟩
    defined_zero with ⟨z, hz1, hz2, _⟩
  have hz0 : 0 ≤ z 0 := (hz1 0).1
  have hopt := (hz2 0 (-1) (by norm_num) (by decide)).2
  unfold ShockControl.objective at hopt
  rw [value_eq_zero 0, value_eq_zero 1] at hopt
  dsimp only [singlePeriodControl] at hopt
  rw [add_zero, stockCost_zero, expectation_zero] at hopt
  simp only [add_zero, mul_zero, one_mul] at hopt
  have hcoe : z 0 - (-1) = 0 := EReal.coe_eq_zero.mp hopt
  linarith
