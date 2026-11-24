-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.FourierPi.integral_ann_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T13:15:13.962803+00:00
-- url     : https://prove2.me/submissions/0ebb665f-9510-4a8f-80cb-ec535d4c8519

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_HarrisTaylorCardKilledByIdealEqAbsNormPow
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_FourierPi_integral_subgroup_eq_zero
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_FourierPi_integral_subgroup_eq_real

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.FourierPi
variable {R : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
  [LocallyCompactSpace R] [SecondCountableTopology R] [T2Space R] [MeasurableSpace R] [BorelSpace R]
  {ψ : R → ℂ} {ι : Type} [Fintype ι]
open Classical
namespace GlobalTheory.CompanionTheory.SW.FourierPi
theorem _root_.solution (lam : Measure R) [lam.IsAddHaarMeasure] (L P : AddSubgroup R)
    (hPm : MeasurableSet (P : Set R)) (ha : ∀ x y, ψ (x + y) = ψ x * ψ y)
    (hLP : ∀ s ∈ L, ∀ t ∈ P, ψ (s * t) = 1) (hPL : ∀ z, (∀ t ∈ P, ψ (t * z) = 1) → z ∈ L) (s : R) :
    ∫ t in (P : Set R), ψ (s * t) ∂lam = if s ∈ L then (lam.real (P : Set R) : ℂ) else 0 := by
  simp_rw [mul_comm s]
  by_cases h : s ∈ L
  · rw [if_pos h]
    exact integral_subgroup_eq_real lam _ hPm s fun x hx => by
      rw [mul_comm]
      exact hLP s h x hx
  · rw [if_neg h]
    have : ∃ a ∈ P, ψ (a * s) ≠ 1 := by
      by_contra hcon
      push_neg at hcon
      exact h (hPL s hcon)
    obtain ⟨a, haP, hne⟩ := this
    exact integral_subgroup_eq_zero lam P hPm ha s a haP hne
end GlobalTheory.CompanionTheory.SW.FourierPi
