-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.FourierPi.box_formula
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T14:09:37.282857+00:00
-- url     : https://prove2.me/submissions/2c55a97c-ee8d-41e1-bd99-850e12cc1ec0

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_HarrisTaylorCardKilledByIdealEqAbsNormPow
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_FourierPi_integral_box
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_FourierPi_fubini_box

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
namespace GlobalTheory.CompanionTheory.SW.FourierPi
theorem _root_.solution (hc : Continuous ψ) (ha : ∀ x y, ψ (x + y) = ψ x * ψ y) (hn : ∀ x, ‖ψ x‖ = 1)
    (lam : Measure R) [lam.IsAddHaarMeasure] [SigmaFinite lam] (L P : AddSubgroup R)
    (hLm : MeasurableSet (L : Set R)) (hPm : MeasurableSet (P : Set R)) (hPf : lam (P : Set R) < ⊤)
    (hLP : ∀ s ∈ L, ∀ t ∈ P, ψ (s * t) = 1) (hPL : ∀ z, (∀ t ∈ P, ψ (t * z) = 1) → z ∈ L)
    (Φ : (ι → R) → ℂ) (Φc : Continuous Φ) (hi : Integrable Φ (Measure.pi fun _ : ι => lam))
    (z : ι → R) :
    ∫ y in box ι (P : Set R), (∫ x, Φ x * ψ (x ⬝ᵥ y) ∂(Measure.pi fun _ : ι => lam)) * ψ (y ⬝ᵥ z)
        ∂(Measure.pi fun _ : ι => lam) =
      (lam.real (P : Set R) : ℂ) ^ Fintype.card ι *
        ∫ u in box ι (L : Set R), Φ (u - z) ∂(Measure.pi fun _ : ι => lam) := by
  classical
  have hBf : (Measure.pi fun _ : ι => lam) (box ι (P : Set R)) < ⊤ := by
    rw [Measure.pi_pi]
    exact ENNReal.prod_lt_top fun _ _ => hPf
  rw [fubini_box hc ha hn _ _ hBf Φ Φc hi z]
  simp_rw [integral_box lam L P hPm ha hn hLP hPL]
  set g : (ι → R) → ℂ := (box ι (L : Set R)).indicator
    fun u => (lam.real (P : Set R) : ℂ) ^ Fintype.card ι * Φ (u - z) with hg
  have hbm : MeasurableSet (box ι (L : Set R)) := MeasurableSet.univ_pi fun _ => hLm
  have e : ∀ x, Φ x * (box ι (L : Set R)).indicator
      (fun _ => (lam.real (P : Set R) : ℂ) ^ Fintype.card ι) (x + z) = g (x + z) := by
    intro x
    by_cases hx : x + z ∈ box ι (L : Set R)
    · simp only [hg, Set.indicator_of_mem hx, add_sub_cancel_right]
      ring
    · simp only [hg, Set.indicator_of_notMem hx, mul_zero]
  simp_rw [e]
  rw [integral_add_right_eq_self g z, hg, integral_indicator hbm, integral_const_mul]
end GlobalTheory.CompanionTheory.SW.FourierPi
