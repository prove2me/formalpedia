-- Prove2me | solution 1 for GlobalTheory.WeilCriterion.lintegral_mul_fibre_symm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:24:51.418636+00:00
-- url     : https://prove2.me/submissions/18f28970-7d9c-4ba0-9125-6dde3e81dca8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_GlobalSignature_InvariantRadonFibre
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ExistsBruhatFunctionClosedSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ExistsUniqueHaarOfInvariantRadonOnCosets
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_WeilCriterionInvariantMeasureHomogeneousSpace
import Theorems.Thm_GlobalTheory_WeilCriterion_lintegral_mul_right_eq_modulus
import Theorems.Thm_GlobalTheory_WeilCriterion_measurable_modulus
import Theorems.Thm_GlobalTheory_WeilCriterion_lintegral_modulus_mul_inv
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_InvariantRadonFibre_fibreIntegral_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.IndefiniteRowSideFullHecke.InvariantRadonFibre.fibreIntegral_mk



set_option autoImplicit false
open MeasureTheory MeasureTheory.Measure GlobalTheory.IndefiniteRowSideFullHecke.InvariantRadonFibre Topology
open scoped ENNReal NNReal
open GlobalTheory GlobalTheory.WeilCriterion
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
  (H : Subgroup G) [LocallyCompactSpace H]
namespace GlobalTheory.WeilCriterion
theorem _root_.solution
    (hΔ : ∀ h : H, modularCharacterFun (h : G) = modularCharacterFun h)
    (dg : Measure G) [dg.IsHaarMeasure] (ν : Measure H) [ν.IsHaarMeasure]
    {f f' : G → ℝ≥0∞} (hf : Measurable f) (hf' : Measurable f') :
    ∫⁻ g, f g * ∫⁻ h : H, f' (g * h) ∂ν ∂dg = ∫⁻ g, (∫⁻ h : H, f (g * h) ∂ν) * f' g ∂dg := by
  haveI : SecondCountableTopology H := TopologicalSpace.Subtype.secondCountableTopology _
  have e1 : ∀ g, f g * ∫⁻ h : H, f' (g * h) ∂ν = ∫⁻ h : H, f g * f' (g * h) ∂ν := fun g =>
    (lintegral_const_mul _ (by fun_prop)).symm
  have e2 : ∀ g, (∫⁻ h : H, f (g * h) ∂ν) * f' g =
      ∫⁻ h : H, (modularCharacterFun h : ℝ≥0∞) * (f (g * (h : G)⁻¹) * f' g) ∂ν := fun g => by
    rw [← lintegral_mul_const _ (by fun_prop),
      ← lintegral_modulus_mul_inv ν (f := fun h : H => f (g * h) * f' g) (by fun_prop)]
    rfl
  have hm := measurable_modulus (G := H)
  simp_rw [e1, e2]
  have m1 : Measurable fun p : G × H => f p.1 * f' (p.1 * p.2) := by fun_prop
  have m2 : Measurable fun p : G × H => f (p.1 * (p.2 : G)⁻¹) * f' p.1 := by fun_prop
  rw [lintegral_lintegral_swap m1.aemeasurable,
    lintegral_lintegral_swap (μ := dg) ((hm.comp measurable_snd).mul m2).aemeasurable]
  congr 1
  funext h
  rw [lintegral_const_mul _ (by fun_prop), ← hΔ,
    ← lintegral_mul_right_eq_modulus dg (f := fun g => f (g * (h : G)⁻¹) * f' g) (by fun_prop)]
  simp
end GlobalTheory.WeilCriterion
