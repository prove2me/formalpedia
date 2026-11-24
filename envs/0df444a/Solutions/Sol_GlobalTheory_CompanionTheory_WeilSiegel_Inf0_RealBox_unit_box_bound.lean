-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.WeilSiegel.Inf0.RealBox.unit_box_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T14:15:44.189085+00:00
-- url     : https://prove2.me/submissions/5a9f28df-7f28-4e1a-a255-358a04ca9b4c

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CoreR
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_QuadraticBoxVolumeBound
import Theorems.Thm_GlobalTheory_CompanionTheory_WeilSiegel_Inf0_RealBox_continuous_qR0
import Theorems.Thm_GlobalTheory_CompanionTheory_WeilSiegel_Inf0_RealBox_continuous_gaussR
import Theorems.Thm_GlobalTheory_CompanionTheory_WeilSiegel_Inf0_RealBox_boxR_one_eq

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
theorem _root_.solution [Fintype P] [Fintype ι] (A Pm : P → Matrix ι ι ℝ) (Di : (P → ℝ) → ℝ)
    (hDi : Continuous Di)
    (hD : ∀ U : Set (P → ℝ), MeasurableSet U →
      ∫⁻ x in qR0 A ⁻¹' U, ENNReal.ofReal (gaussR Pm x) = ∫⁻ y in U, ENNReal.ofReal (Di y)) :
    ∃ C : ℝ≥0, ∀ U : Set (P → ℝ), MeasurableSet U →
      (volume : Measure (P → ι → ℝ)) (qR0 A ⁻¹' U ∩ boxR (fun _ => (1 : ℝ))) ≤
        (C : ℝ≥0∞) * volume U := by
  have hBc : IsCompact (GlobalTheory.CompanionTheory.WeilSiegel.Inf0.boxR (fun _ : P => (1 : ℝ)) : Set (P → ι → ℝ)) := by
    rw [GlobalTheory.CompanionTheory.WeilSiegel.Inf0.RealBox.boxR_one_eq]; exact isCompact_closedBall _ _
  have hBm : MeasurableSet (GlobalTheory.CompanionTheory.WeilSiegel.Inf0.boxR (fun _ : P => (1 : ℝ)) : Set (P → ι → ℝ)) :=
    hBc.isClosed.measurableSet
  have hBne : (GlobalTheory.CompanionTheory.WeilSiegel.Inf0.boxR (fun _ : P => (1 : ℝ)) : Set (P → ι → ℝ)).Nonempty := by
    rw [GlobalTheory.CompanionTheory.WeilSiegel.Inf0.RealBox.boxR_one_eq]; exact ⟨0, Metric.mem_closedBall_self zero_le_one⟩
  have hQc : Continuous (GlobalTheory.CompanionTheory.WeilSiegel.Inf0.qR0 (P := P) A) := GlobalTheory.CompanionTheory.WeilSiegel.Inf0.RealBox.continuous_qR0 A
  have hKc : IsCompact (GlobalTheory.CompanionTheory.WeilSiegel.Inf0.qR0 A '' (GlobalTheory.CompanionTheory.WeilSiegel.Inf0.boxR (fun _ : P => (1 : ℝ)) : Set (P → ι → ℝ))) :=
    hBc.image hQc
  obtain ⟨x₀, -, hx₀⟩ := hBc.exists_isMinOn hBne (GlobalTheory.CompanionTheory.WeilSiegel.Inf0.RealBox.continuous_gaussR Pm).continuousOn
  obtain ⟨D, hD'⟩ := hKc.exists_bound_of_continuousOn hDi.continuousOn
  have hm : 0 < GlobalTheory.CompanionTheory.WeilSiegel.Inf0.gaussR Pm x₀ := Real.exp_pos _
  refine ⟨Real.toNNReal ((GlobalTheory.CompanionTheory.WeilSiegel.Inf0.gaussR Pm x₀)⁻¹ * D), fun U hU => ?_⟩
  change _ ≤ ENNReal.ofReal ((GlobalTheory.CompanionTheory.WeilSiegel.Inf0.gaussR Pm x₀)⁻¹ * D) * _
  have hS : MeasurableSet (GlobalTheory.CompanionTheory.WeilSiegel.Inf0.qR0 A ⁻¹' U ∩
      (GlobalTheory.CompanionTheory.WeilSiegel.Inf0.boxR (fun _ : P => (1 : ℝ)) : Set (P → ι → ℝ))) := (hQc.measurable hU).inter hBm
  have hK : MeasurableSet (U ∩ GlobalTheory.CompanionTheory.WeilSiegel.Inf0.qR0 A ''
      (GlobalTheory.CompanionTheory.WeilSiegel.Inf0.boxR (fun _ : P => (1 : ℝ)) : Set (P → ι → ℝ))) := hU.inter hKc.isClosed.measurableSet
  have h1 : ENNReal.ofReal (GlobalTheory.CompanionTheory.WeilSiegel.Inf0.gaussR Pm x₀) * (volume : Measure (P → ι → ℝ))
      (GlobalTheory.CompanionTheory.WeilSiegel.Inf0.qR0 A ⁻¹' U ∩ GlobalTheory.CompanionTheory.WeilSiegel.Inf0.boxR (fun _ => (1 : ℝ))) ≤
      ENNReal.ofReal D * volume U := by
    calc ENNReal.ofReal (GlobalTheory.CompanionTheory.WeilSiegel.Inf0.gaussR Pm x₀) * (volume : Measure (P → ι → ℝ))
          (GlobalTheory.CompanionTheory.WeilSiegel.Inf0.qR0 A ⁻¹' U ∩ GlobalTheory.CompanionTheory.WeilSiegel.Inf0.boxR (fun _ => (1 : ℝ)))
        = ∫⁻ _ in GlobalTheory.CompanionTheory.WeilSiegel.Inf0.qR0 A ⁻¹' U ∩ GlobalTheory.CompanionTheory.WeilSiegel.Inf0.boxR (fun _ => (1 : ℝ)),
            ENNReal.ofReal (GlobalTheory.CompanionTheory.WeilSiegel.Inf0.gaussR Pm x₀) := (setLIntegral_const _ _).symm
      _ ≤ ∫⁻ x in GlobalTheory.CompanionTheory.WeilSiegel.Inf0.qR0 A ⁻¹' U ∩ GlobalTheory.CompanionTheory.WeilSiegel.Inf0.boxR (fun _ => (1 : ℝ)),
            ENNReal.ofReal (GlobalTheory.CompanionTheory.WeilSiegel.Inf0.gaussR Pm x) :=
          setLIntegral_mono' hS fun x hx => ENNReal.ofReal_le_ofReal (isMinOn_iff.mp hx₀ x hx.2)
      _ ≤ ∫⁻ x in GlobalTheory.CompanionTheory.WeilSiegel.Inf0.qR0 A ⁻¹' (U ∩ GlobalTheory.CompanionTheory.WeilSiegel.Inf0.qR0 A ''
            (GlobalTheory.CompanionTheory.WeilSiegel.Inf0.boxR (fun _ : P => (1 : ℝ)) : Set (P → ι → ℝ))),
            ENNReal.ofReal (GlobalTheory.CompanionTheory.WeilSiegel.Inf0.gaussR Pm x) :=
          lintegral_mono_set fun x hx => ⟨hx.1, x, hx.2, rfl⟩
      _ = ∫⁻ y in U ∩ GlobalTheory.CompanionTheory.WeilSiegel.Inf0.qR0 A ''
            (GlobalTheory.CompanionTheory.WeilSiegel.Inf0.boxR (fun _ : P => (1 : ℝ)) : Set (P → ι → ℝ)), ENNReal.ofReal (Di y) := hD _ hK
      _ ≤ ∫⁻ _ in U ∩ GlobalTheory.CompanionTheory.WeilSiegel.Inf0.qR0 A ''
            (GlobalTheory.CompanionTheory.WeilSiegel.Inf0.boxR (fun _ : P => (1 : ℝ)) : Set (P → ι → ℝ)), ENNReal.ofReal D :=
          setLIntegral_mono' hK fun y hy =>
            ENNReal.ofReal_le_ofReal ((Real.le_norm_self _).trans (hD' y hy.2))
      _ = ENNReal.ofReal D * volume (U ∩ GlobalTheory.CompanionTheory.WeilSiegel.Inf0.qR0 A ''
            (GlobalTheory.CompanionTheory.WeilSiegel.Inf0.boxR (fun _ : P => (1 : ℝ)) : Set (P → ι → ℝ))) := setLIntegral_const _ _
      _ ≤ ENNReal.ofReal D * volume U := mul_le_mul_right (measure_mono Set.inter_subset_left) _
  calc (volume : Measure (P → ι → ℝ)) (GlobalTheory.CompanionTheory.WeilSiegel.Inf0.qR0 A ⁻¹' U ∩ GlobalTheory.CompanionTheory.WeilSiegel.Inf0.boxR (fun _ => (1 : ℝ)))
      = ENNReal.ofReal ((GlobalTheory.CompanionTheory.WeilSiegel.Inf0.gaussR Pm x₀)⁻¹ * GlobalTheory.CompanionTheory.WeilSiegel.Inf0.gaussR Pm x₀) *
          (volume : Measure (P → ι → ℝ)) (GlobalTheory.CompanionTheory.WeilSiegel.Inf0.qR0 A ⁻¹' U ∩ GlobalTheory.CompanionTheory.WeilSiegel.Inf0.boxR (fun _ => (1 : ℝ))) := by
        rw [inv_mul_cancel₀ hm.ne', ENNReal.ofReal_one, one_mul]
    _ = ENNReal.ofReal (GlobalTheory.CompanionTheory.WeilSiegel.Inf0.gaussR Pm x₀)⁻¹ * (ENNReal.ofReal (GlobalTheory.CompanionTheory.WeilSiegel.Inf0.gaussR Pm x₀) *
          (volume : Measure (P → ι → ℝ)) (GlobalTheory.CompanionTheory.WeilSiegel.Inf0.qR0 A ⁻¹' U ∩ GlobalTheory.CompanionTheory.WeilSiegel.Inf0.boxR (fun _ => (1 : ℝ)))) := by
        rw [ENNReal.ofReal_mul (inv_nonneg.mpr hm.le), mul_assoc]
    _ ≤ ENNReal.ofReal (GlobalTheory.CompanionTheory.WeilSiegel.Inf0.gaussR Pm x₀)⁻¹ * (ENNReal.ofReal D * volume U) :=
        mul_le_mul_right h1 _
    _ = ENNReal.ofReal ((GlobalTheory.CompanionTheory.WeilSiegel.Inf0.gaussR Pm x₀)⁻¹ * D) * volume U := by
        rw [ENNReal.ofReal_mul (inv_nonneg.mpr hm.le), mul_assoc]
end GlobalTheory.CompanionTheory.WeilSiegel.Inf0.RealBox
