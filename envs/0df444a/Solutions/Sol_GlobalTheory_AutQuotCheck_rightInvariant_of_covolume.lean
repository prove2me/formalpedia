-- Prove2me | solution 1 for GlobalTheory.AutQuotCheck.rightInvariant_of_covolume
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:25:58.648151+00:00
-- url     : https://prove2.me/submissions/73176d37-90f2-4686-9cb4-e051e3e98d22

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_LevelGroupExamples_RightInvariantOfCovolume

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped Pointwise
open GlobalTheory GlobalTheory.AutQuotCheck
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
  (Γ : Subgroup G) [Countable Γ]
open MeasureTheory
open scoped Pointwise
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
  (Γ : Subgroup G) [Countable Γ]
namespace GlobalTheory.AutQuotCheck
namespace _root_.GlobalTheory.AutQuotCheck
theorem _root_.solution (μ : Measure G) [μ.IsHaarMeasure] {F : Set G}
    (h : IsFundamentalDomain Γ F μ) (h0 : μ F ≠ 0) (h1 : μ F ≠ ⊤) (g : G) :
    μ.map (· * g) = μ := by
  haveI := Measure.isHaarMeasure_map_mul_right μ g
  have hc := Measure.isMulLeftInvariant_eq_smul (μ.map (· * g)) μ
  have hF' : IsFundamentalDomain Γ ((· * g) ⁻¹' F) μ :=
    h.preimage_of_equiv (quasiMeasurePreserving_mul_right μ g) Function.bijective_id
      fun γ x => by simp [Subgroup.smul_def, mul_assoc]
  have hmeas : μ.map (· * g) F = μ F := by
    rw [show (· * g) = (MeasurableEquiv.mulRight g : G → G) from rfl,
      MeasurableEquiv.map_apply]
    exact hF'.measure_eq h
  have hc1 : (μ.map (· * g)).haarScalarFactor μ = 1 := by
    rw [hc, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] at hmeas
    exact ENNReal.coe_eq_one.mp ((ENNReal.mul_eq_right h0 h1).mp hmeas)
  rw [hc, hc1, one_smul]
end _root_.GlobalTheory.AutQuotCheck
end GlobalTheory.AutQuotCheck
