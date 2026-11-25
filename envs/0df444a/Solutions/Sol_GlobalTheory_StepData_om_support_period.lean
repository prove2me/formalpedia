-- Prove2me | solution 1 for GlobalTheory.StepData.om_support_period
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:52:11.996551+00:00
-- url     : https://prove2.me/submissions/7bdd7eb2-4b9d-440c-9341-b99f401cb396

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_StandardOrderExtendedBasisApplyLowBlock
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_LinearWeilActionSupportAndPeriodIntegral
import Theorems.Thm_GlobalTheory_StepData_IntM_mul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData
noncomputable section
open GlobalTheory GlobalTheory.StepData
namespace GlobalTheory.StepData
theorem _root_.solution : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] (ϖ : kˣ), valuation k (ϖ : k) < 1 → ∀ (i : ℕ)
    (μ : kˣ →* ℂˣ) (Φ : Matrix B A k → ℂ), (∀ x, Φ x ≠ 0 → IntM x) → (∀ x y, MaxM y → Φ (x + y) = Φ x) →
    ∀ (g : GL A k) (g' : GL B k), IntM (g⁻¹ : GL A k).val → IntM ((ϖ : k) ^ i • g.val) →
      IntM (g'⁻¹ : GL B k).val → IntM ((ϖ : k) ^ (i + 1) • g'.val) →
    (∀ x, om μ g g' Φ x ≠ 0 → ∀ r s, valuation k (x r s) ≤ valuation k (((ϖ ^ (i + 1))⁻¹ : kˣ) : k)) ∧
    (∀ x y, (∀ r s, valuation k (y r s) ≤ valuation k ((ϖ : k) ^ (i + 1))) → om μ g g' Φ (x + y) = om μ g g' Φ x) := by
  intro k _ _ _ _ A B _ _ _ _ ϖ hϖ i μ Φ hsupp hper g g' hg hgi hg' hg'i
  have hϖ0 : (ϖ : k) ≠ 0 := ϖ.ne_zero
  have hvp : valuation k ((ϖ : k) ^ (i + 1)) ≠ 0 := by
    rw [Valuation.ne_zero_iff]; exact pow_ne_zero _ hϖ0
  constructor
  · intro x hx r s
    have hΦ : Φ ((g'⁻¹ : GL B k).val * x * g.val) ≠ 0 := by
      intro h0; apply hx; simp only [om, h0, mul_zero]
    have hz := hsupp _ hΦ
    have hx' : (ϖ : k) ^ (i + 1) • x = ((ϖ : k) ^ (i + 1) • g'.val) * ((g'⁻¹ : GL B k).val * x * g.val) *
        (g⁻¹ : GL A k).val := by
      rw [Matrix.smul_mul, Matrix.smul_mul]
      congr 1
      simp only [Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
      rw [← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]
    have hint : IntM ((ϖ : k) ^ (i + 1) • x) := by rw [hx']; exact (hg'i.mul hz).mul hg
    have h1 : valuation k ((ϖ : k) ^ (i + 1) * x r s) ≤ 1 := hint r s
    rw [map_mul] at h1
    rw [Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val, map_inv₀]
    calc valuation k (x r s) = (valuation k ((ϖ : k) ^ (i + 1)))⁻¹ * (valuation k ((ϖ : k) ^ (i + 1)) * valuation k (x r s)) := by
          rw [inv_mul_cancel_left₀ hvp]
      _ ≤ (valuation k ((ϖ : k) ^ (i + 1)))⁻¹ * 1 := by gcongr
      _ = _ := mul_one _
  · intro x y hy
    have hy' : IntM (((ϖ : k) ^ (i + 1))⁻¹ • y) := fun r s => by
      show valuation k (((ϖ : k) ^ (i + 1))⁻¹ * y r s) ≤ 1
      rw [map_mul, map_inv₀]
      calc _ ≤ (valuation k ((ϖ : k) ^ (i + 1)))⁻¹ * valuation k ((ϖ : k) ^ (i + 1)) := by gcongr; exact hy r s
        _ = 1 := inv_mul_cancel₀ hvp
    have hc : (ϖ : k) * (ϖ : k) ^ i * ((ϖ : k) ^ (i + 1))⁻¹ = 1 := by
      rw [pow_succ]; field_simp
    have heq : (g'⁻¹ : GL B k).val * y * g.val = (ϖ : k) • ((g'⁻¹ : GL B k).val * (((ϖ : k) ^ (i + 1))⁻¹ • y) * ((ϖ : k) ^ i • g.val)) := by
      rw [Matrix.mul_smul, Matrix.mul_smul, Matrix.smul_mul, smul_smul, smul_smul, hc, one_smul]
    have hM : IntM ((g'⁻¹ : GL B k).val * (((ϖ : k) ^ (i + 1))⁻¹ • y) * ((ϖ : k) ^ i • g.val)) :=
      (hg'.mul hy').mul hgi
    have hmax : MaxM ((g'⁻¹ : GL B k).val * y * g.val) := by
      rw [heq]
      intro r s
      rw [Matrix.smul_apply, smul_eq_mul, map_mul]
      exact mul_lt_one_of_nonneg_of_lt_one_left zero_le hϖ (hM r s)
    simp only [om, Matrix.mul_add, Matrix.add_mul, hper _ _ hmax]
end GlobalTheory.StepData
