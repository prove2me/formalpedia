-- Prove2me | solution 1 for GlobalTheory.AutQuotCheck.normalised_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:25:54.102871+00:00
-- url     : https://prove2.me/submissions/83895fe0-359d-4c9f-9b3e-dd973a6d0a0d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_LevelGroupExamples_RightInvariantOfCovolume
import Theorems.Thm_GlobalTheory_AutQuotCheck_map_restrict_eq

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
namespace GlobalTheory.AutQuotCheck
theorem _root_.solution (μ ν : Measure G) [μ.IsHaarMeasure] [ν.IsHaarMeasure] {F F' : Set G}
    (h : IsFundamentalDomain Γ F μ) (h' : IsFundamentalDomain Γ F' ν) :
    (μ F)⁻¹ • (μ.restrict F).map (cls Γ) = (ν F')⁻¹ • (ν.restrict F').map (cls Γ) := by
  have e := Measure.isMulLeftInvariant_eq_smul μ ν
  have hc0 := Measure.haarScalarFactor_pos_of_isHaarMeasure μ ν
  set c := Measure.haarScalarFactor μ ν with hc
  have hF' : IsFundamentalDomain Γ F' μ := by
    refine h'.mono ?_
    rw [e]; exact Measure.smul_absolutelyContinuous
  have e' : μ = (c : ENNReal) • ν := e
  have hq2 : (μ.restrict F).map (cls Γ) = (c : ENNReal) • (ν.restrict F').map (cls Γ) := by
    rw [map_restrict_eq Γ μ h hF', ← Measure.map_smul, ← Measure.restrict_smul, ← e']
  have hu : μ F = c * ν F' := by
    rw [h.measure_eq hF']
    conv_lhs => rw [e']
    rfl
  rw [hu, hq2, smul_smul]
  congr 1
  have c0 : (c : ENNReal) ≠ 0 := by exact_mod_cast hc0.ne'
  rw [ENNReal.mul_inv (Or.inl c0) (Or.inl ENNReal.coe_ne_top), mul_comm (c : ENNReal)⁻¹, mul_assoc,
    ENNReal.inv_mul_cancel c0 ENNReal.coe_ne_top, mul_one]
end GlobalTheory.AutQuotCheck
