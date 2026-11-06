-- Prove2me | solution 1 for LostSalesExpGap.ConstOrder.lemma_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T08:18:46.378484+00:00
-- url     : https://prove2.me/submissions/7bd88949-f82e-4da8-a99d-2b129c4633b9

import Mathlib
import Definitions.Def_LostSalesExpGap_ConstOrder_ConstantOrder
import Theorems.Thm_LostSalesExpGap_ConstOrder_eq_3
import Theorems.Thm_LostSalesExpGap_ConstOrder_best_constant_exists

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace LSExpGapL1

open CappedBaseStock LostSalesExpGap.ConstOrder

lemma EIinf_zero (P : DemandLaw) : EIinf P 0 = 0 := by
  unfold EIinf
  have : ∀ d : DemandPath,
      LostSalesConstantOrder.LargeLeadTime.supWalk (0 : ℝ).toNNReal d = 0 := by
    intro d
    unfold LostSalesConstantOrder.LargeLeadTime.supWalk
    apply ENNReal.iSup_eq_zero.mpr
    intro k
    apply ENNReal.ofReal_of_nonpos
    unfold LostSalesConstantOrder.LargeLeadTime.walk
    have : 0 ≤ ∑ i ∈ Finset.Icc 1 k, (d (i - 1) : ℝ) := by positivity
    simp only [Real.toNNReal_zero, NNReal.coe_zero, mul_zero, zero_sub, neg_nonpos]
    exact this
  have h0 : (0 : ℝ).toNNReal = 0 := Real.toNNReal_zero
  simp only [h0] at this
  simp only [Real.toNNReal_zero, this, lintegral_zero]

/-- Real form of the optimality of `r∞` against another level `r ∈ [0, E[D])`. -/
lemma opt_real (P : DemandLaw) (c : Parameters) (hP : LostSalesConstantOrder.LargeLeadTime.NonDeterministic P)
    (r : ℝ) (hr0 : 0 ≤ r) (hr : r < mean P) (hfin : EIinf P r ≠ ⊤) :
    EIinf P (rInf P c) ≠ ⊤ ∧
    c.h * (EIinf P (rInf P c)).toReal + c.p * (mean P - rInf P c) ≤
      c.h * (EIinf P r).toReal + c.p * (mean P - r) := by
  obtain ⟨_, _, hrmem, hrlt⟩ := best_constant_exists P c hP
  have hh := c.holding_pos
  have hp := c.penalty_pos
  have hm : 0 < mean P := P.positiveMean
  have hr0' : 0 ≤ rInf P c := hrmem.1.1
  have hC0 : constCost P c 0 ≠ ⊤ := by
    rw [eq_3 P c 0 le_rfl hm, EIinf_zero, mul_zero, zero_add]; exact ENNReal.ofReal_ne_top
  have hCfin : constCost P c (rInf P c) ≠ ⊤ :=
    ne_top_of_le_ne_top hC0 (hrmem.2 0 ⟨le_rfl, hm.le⟩)
  have hEfin : EIinf P (rInf P c) ≠ ⊤ := by
    intro htop
    rw [eq_3 P c _ hr0' hrlt, htop, ENNReal.mul_top (by simp [hh]), top_add] at hCfin
    exact hCfin rfl
  refine ⟨hEfin, ?_⟩
  have hle := hrmem.2 r ⟨hr0, hr.le⟩
  rw [eq_3 P c _ hr0' hrlt, eq_3 P c r hr0 hr] at hle
  have := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr
    ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin, ENNReal.ofReal_ne_top⟩) hle
  rwa [ENNReal.toReal_add (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hEfin) ENNReal.ofReal_ne_top,
    ENNReal.toReal_add (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin) ENNReal.ofReal_ne_top,
    ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal hh.le,
    ENNReal.toReal_ofReal (by nlinarith), ENNReal.toReal_ofReal (by nlinarith)] at this

lemma EIinf_fin (P : DemandLaw) (c : Parameters)
    (hP : LostSalesConstantOrder.LargeLeadTime.NonDeterministic P) : EIinf P (rInf P c) ≠ ⊤ :=
  (opt_real P c hP 0 le_rfl P.positiveMean (by rw [EIinf_zero]; exact ENNReal.zero_ne_top)).1

end LSExpGapL1

open LostSalesExpGap.ConstOrder LSExpGapL1 CappedBaseStock in
theorem solution (P : CappedBaseStock.DemandLaw)
    (hP : LostSalesConstantOrder.LargeLeadTime.NonDeterministic P)
    (c₁ c₂ : CappedBaseStock.Parameters) (h₁₂ : c₁.p / c₁.h ≤ c₂.p / c₂.h) :
    gamma P c₁ ≤ gamma P c₂ := by
  -- monotone comparative statics: `r∞(c₁) ≤ r∞(c₂)`
  obtain ⟨_, _, hm1, hlt1⟩ := best_constant_exists P c₁ hP
  obtain ⟨_, _, hm2, hlt2⟩ := best_constant_exists P c₂ hP
  set r₁ := rInf P c₁ with hr₁
  set r₂ := rInf P c₂ with hr₂
  have hr12 : r₁ ≤ r₂ := by
    by_contra hcon
    push_neg at hcon
    have hh1 := c₁.holding_pos; have hh2 := c₂.holding_pos
    have hp1 := c₁.penalty_pos
    have hf1 := EIinf_fin P c₁ hP
    have hf2 := EIinf_fin P c₂ hP
    have o1 := (opt_real P c₁ hP r₂ hm2.1.1 hlt2 hf2).2
    have o2 := (opt_real P c₂ hP r₁ hm1.1.1 hlt1 hf1).2
    set E₁ := (EIinf P r₁).toReal
    set E₂ := (EIinf P r₂).toReal
    set m := mean P
    -- `E₁ - E₂ ≤ ϱ₁ (r₁ - r₂)` and `E₁ - E₂ ≥ ϱ₂ (r₁ - r₂)`
    have h1 : c₁.h * (E₁ - E₂) ≤ c₁.p * (r₁ - r₂) := by linarith
    have h2 : c₂.p * (r₁ - r₂) ≤ c₂.h * (E₁ - E₂) := by linarith
    have hd : 0 < r₁ - r₂ := by linarith
    have hϱ : c₂.p / c₂.h ≤ c₁.p / c₁.h := by
      have e1 : E₁ - E₂ ≤ c₁.p / c₁.h * (r₁ - r₂) := by
        rw [div_mul_eq_mul_div, le_div_iff₀ hh1]; linarith
      have e2 : c₂.p / c₂.h * (r₁ - r₂) ≤ E₁ - E₂ := by
        rw [div_mul_eq_mul_div, div_le_iff₀ hh2]; linarith
      have := e2.trans e1
      exact le_of_mul_le_mul_right this hd
    have heq : c₁.p / c₁.h = c₂.p / c₂.h := le_antisymm h₁₂ hϱ
    -- hence `r₂` is also optimal for `c₁`
    have h3 : c₁.p * (r₁ - r₂) ≤ c₁.h * (E₁ - E₂) := by
      have e2 : c₂.p / c₂.h * (r₁ - r₂) ≤ E₁ - E₂ := by
        rw [div_mul_eq_mul_div, div_le_iff₀ hh2]; linarith
      rw [← heq, div_mul_eq_mul_div, div_le_iff₀ hh1] at e2
      linarith
    have hopt : r₂ ∈ argminConst P c₁ := by
      refine ⟨hm2.1, fun r' hr' => ?_⟩
      have hle := hm1.2 r' hr'
      refine le_trans ?_ hle
      rw [eq_3 P c₁ r₂ hm2.1.1 hlt2, eq_3 P c₁ r₁ hm1.1.1 hlt1,
        ← ENNReal.ofReal_toReal hf1, ← ENNReal.ofReal_toReal hf2,
        ← ENNReal.ofReal_mul hh1.le, ← ENNReal.ofReal_mul hh1.le,
        ← ENNReal.ofReal_add (mul_nonneg hh1.le ENNReal.toReal_nonneg) (by nlinarith),
        ← ENNReal.ofReal_add (mul_nonneg hh1.le ENNReal.toReal_nonneg) (by nlinarith)]
      apply ENNReal.ofReal_le_ofReal
      linarith
    have : r₁ ≤ r₂ := csInf_le ⟨0, fun y hy => hy.1.1⟩ hopt
    linarith
  -- `γ` is monotone in `r∞`
  have hphinn : ∀ θ : ℝ, 0 ≤ phi P c₁ θ := fun θ =>
    mul_nonneg (Real.exp_pos _).le (integral_nonneg fun _ => (Real.exp_pos _).le)
  have hbdd : BddBelow (Set.range fun θ : Set.Ici (0 : ℝ) => phi P c₁ θ) :=
    ⟨0, by rintro _ ⟨θ, rfl⟩; exact hphinn θ⟩
  apply ciInf_mono hbdd
  intro θ
  simp only [phi]
  apply mul_le_mul_of_nonneg_right _ (integral_nonneg fun _ => (Real.exp_pos _).le)
  apply Real.exp_le_exp.mpr
  exact mul_le_mul_of_nonneg_left hr12 θ.2
