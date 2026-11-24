-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.WeilSiegel.Inf0.RealBox.image_box_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T14:39:42.655047+00:00
-- url     : https://prove2.me/submissions/b9e7543d-2096-4922-a5a7-6143f6352c90

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CoreR
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_QuadraticBoxVolumeBound
import Theorems.Thm_GlobalTheory_CompanionTheory_WeilSiegel_Inf0_RealBox_map_pi_smul
import Theorems.Thm_GlobalTheory_CompanionTheory_WeilSiegel_Inf0_RealBox_continuous_qR0
import Theorems.Thm_GlobalTheory_CompanionTheory_WeilSiegel_Inf0_RealBox_unit_box_bound
import Theorems.Thm_GlobalTheory_CompanionTheory_WeilSiegel_Inf0_RealBox_qR0_scale

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Topology GlobalTheory.CompanionTheory.WeilSiegel.Inf0
open scoped ENNReal NNReal Matrix
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.WeilSiegel GlobalTheory.CompanionTheory.WeilSiegel.Inf0 GlobalTheory.CompanionTheory.WeilSiegel.Inf0.RealBox
variable {P ι : Type}
namespace GlobalTheory.CompanionTheory.WeilSiegel.Inf0.RealBox
theorem _root_.solution : ∀ (P ι : Type) [Fintype P] [Fintype ι] (A Pm : P → Matrix ι ι ℝ) (Di : (P → ℝ) → ℝ), 2 ≤ Fintype.card ι → Continuous Di → (∀ U : Set (P → ℝ), MeasurableSet U → ∫⁻ x in qR0 A ⁻¹' U, ENNReal.ofReal (gaussR Pm x) = ∫⁻ y in U, ENNReal.ofReal (Di y)) → ∃ C : ℝ≥0, ∀ t : P → ℝ, (∀ w, 0 < t w) → ∀ U : Set (P → ℝ), MeasurableSet U → (volume : Measure (P → ι → ℝ)) (qR0 A ⁻¹' U ∩ boxR t) ≤ (C : ℝ≥0∞) * ENNReal.ofReal (∏ w, t w ^ (Fintype.card ι - 2)) * volume U := by
  intro P ι _ _ A Pm Di hcard hDi hD
  obtain ⟨C, hC⟩ := GlobalTheory.CompanionTheory.WeilSiegel.Inf0.RealBox.unit_box_bound A Pm Di hDi hD
  refine ⟨C, fun t ht U hU => ?_⟩
  have hQc : Continuous (GlobalTheory.CompanionTheory.WeilSiegel.Inf0.qR0 (P := P) A) := GlobalTheory.CompanionTheory.WeilSiegel.Inf0.RealBox.continuous_qR0 A
  have hφm : Measurable (fun (x : P → ι → ℝ) (w : P) => t w • x w) :=
    (continuous_pi fun w => (continuous_apply w).const_smul (t w)).measurable
  have hψm : Measurable (fun (z : P → ℝ) (w : P) => t w ^ 2 • z w) :=
    (continuous_pi fun w => (continuous_apply w).const_smul (t w ^ 2)).measurable
  have hBox : IsClosed (GlobalTheory.CompanionTheory.WeilSiegel.Inf0.boxR t : Set (P → ι → ℝ)) := by
    show IsClosed {x : P → ι → ℝ | ∀ w, ‖x w‖ ≤ t w}
    rw [Set.setOf_forall]
    exact isClosed_iInter fun w => isClosed_le (continuous_apply w).norm continuous_const
  have hSm : MeasurableSet (GlobalTheory.CompanionTheory.WeilSiegel.Inf0.qR0 A ⁻¹' U ∩ (GlobalTheory.CompanionTheory.WeilSiegel.Inf0.boxR t : Set (P → ι → ℝ))) :=
    (hQc.measurable hU).inter hBox.measurableSet
  have hpre : (fun (x : P → ι → ℝ) (w : P) => t w • x w) ⁻¹'
      (GlobalTheory.CompanionTheory.WeilSiegel.Inf0.qR0 A ⁻¹' U ∩ GlobalTheory.CompanionTheory.WeilSiegel.Inf0.boxR t) =
      GlobalTheory.CompanionTheory.WeilSiegel.Inf0.qR0 A ⁻¹' ((fun (z : P → ℝ) (w : P) => t w ^ 2 • z w) ⁻¹' U) ∩
        GlobalTheory.CompanionTheory.WeilSiegel.Inf0.boxR (fun _ => (1 : ℝ)) := by
    ext y
    simp only [Set.mem_preimage, Set.mem_inter_iff, GlobalTheory.CompanionTheory.WeilSiegel.Inf0.RealBox.qR0_scale]
    refine and_congr_right fun _ => ?_
    simp only [GlobalTheory.CompanionTheory.WeilSiegel.Inf0.boxR, Set.mem_setOf_eq]
    exact forall_congr' fun w => by
      rw [norm_smul, Real.norm_of_nonneg (ht w).le, mul_le_iff_le_one_right (ht w)]
  have hφ := GlobalTheory.CompanionTheory.WeilSiegel.Inf0.RealBox.map_pi_smul (P := P) (ι → ℝ) t ht
  have hψ := GlobalTheory.CompanionTheory.WeilSiegel.Inf0.RealBox.map_pi_smul (P := P) ℝ (fun w => t w ^ 2) (fun w => pow_pos (ht w) 2)
  rw [Module.finrank_fintype_fun_eq_card] at hφ
  rw [Module.finrank_self] at hψ
  have e1 : ENNReal.ofReal (∏ w, (t w ^ Fintype.card ι)⁻¹) *
      (volume : Measure (P → ι → ℝ)) (GlobalTheory.CompanionTheory.WeilSiegel.Inf0.qR0 A ⁻¹' U ∩ GlobalTheory.CompanionTheory.WeilSiegel.Inf0.boxR t) =
      volume (GlobalTheory.CompanionTheory.WeilSiegel.Inf0.qR0 A ⁻¹' ((fun (z : P → ℝ) (w : P) => t w ^ 2 • z w) ⁻¹' U) ∩
        GlobalTheory.CompanionTheory.WeilSiegel.Inf0.boxR (fun _ => (1 : ℝ))) := by
    rw [← hpre, ← Measure.map_apply hφm hSm, hφ, Measure.smul_apply, smul_eq_mul]
  have e2 : ENNReal.ofReal (∏ w, ((t w ^ 2) ^ 1)⁻¹) * (volume : Measure (P → ℝ)) U =
      volume ((fun (z : P → ℝ) (w : P) => t w ^ 2 • z w) ⁻¹' U) := by
    rw [← Measure.map_apply hψm hU, hψ, Measure.smul_apply, smul_eq_mul]
  have hprod : ENNReal.ofReal (∏ w, t w ^ Fintype.card ι) *
      ENNReal.ofReal (∏ w, (t w ^ Fintype.card ι)⁻¹) = 1 := by
    rw [← ENNReal.ofReal_mul (Finset.prod_nonneg fun w _ => (pow_pos (ht w) _).le),
      ← Finset.prod_mul_distrib,
      Finset.prod_eq_one fun w _ => mul_inv_cancel₀ (pow_ne_zero _ (ht w).ne'), ENNReal.ofReal_one]
  have hreal : (∏ w, t w ^ Fintype.card ι) * ∏ w, ((t w ^ 2) ^ 1)⁻¹ =
      ∏ w, t w ^ (Fintype.card ι - 2) := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun w _ => ?_
    rw [pow_one, show t w ^ Fintype.card ι = t w ^ (Fintype.card ι - 2) * t w ^ 2 by
        rw [← pow_add, Nat.sub_add_cancel hcard],
      mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ (ht w).ne'), mul_one]
  calc (volume : Measure (P → ι → ℝ)) (GlobalTheory.CompanionTheory.WeilSiegel.Inf0.qR0 A ⁻¹' U ∩ GlobalTheory.CompanionTheory.WeilSiegel.Inf0.boxR t)
      = ENNReal.ofReal (∏ w, t w ^ Fintype.card ι) * (ENNReal.ofReal (∏ w, (t w ^ Fintype.card ι)⁻¹) *
          (volume : Measure (P → ι → ℝ)) (GlobalTheory.CompanionTheory.WeilSiegel.Inf0.qR0 A ⁻¹' U ∩ GlobalTheory.CompanionTheory.WeilSiegel.Inf0.boxR t)) := by
        rw [← mul_assoc, hprod, one_mul]
    _ = ENNReal.ofReal (∏ w, t w ^ Fintype.card ι) *
          volume (GlobalTheory.CompanionTheory.WeilSiegel.Inf0.qR0 A ⁻¹' ((fun (z : P → ℝ) (w : P) => t w ^ 2 • z w) ⁻¹' U) ∩
            GlobalTheory.CompanionTheory.WeilSiegel.Inf0.boxR (fun _ => (1 : ℝ))) := by rw [e1]
    _ ≤ ENNReal.ofReal (∏ w, t w ^ Fintype.card ι) *
          ((C : ℝ≥0∞) * volume ((fun (z : P → ℝ) (w : P) => t w ^ 2 • z w) ⁻¹' U)) :=
        mul_le_mul_right (hC _ (hψm hU)) _
    _ = ENNReal.ofReal (∏ w, t w ^ Fintype.card ι) *
          ((C : ℝ≥0∞) * (ENNReal.ofReal (∏ w, ((t w ^ 2) ^ 1)⁻¹) * volume U)) := by rw [e2]
    _ = (C : ℝ≥0∞) * (ENNReal.ofReal (∏ w, t w ^ Fintype.card ι) *
          ENNReal.ofReal (∏ w, ((t w ^ 2) ^ 1)⁻¹)) * volume U := by ring
    _ = (C : ℝ≥0∞) * ENNReal.ofReal (∏ w, t w ^ (Fintype.card ι - 2)) * volume U := by
        rw [← ENNReal.ofReal_mul (Finset.prod_nonneg fun w _ => (pow_pos (ht w) _).le), hreal]
end GlobalTheory.CompanionTheory.WeilSiegel.Inf0.RealBox
