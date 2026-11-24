-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.FourierPi.integral_box
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T13:50:12.527632+00:00
-- url     : https://prove2.me/submissions/d2ac6f0b-8e0c-42bc-8232-346d44fd925f

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_HarrisTaylorCardKilledByIdealEqAbsNormPow
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_FourierPi_psi_dot
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_FourierPi_integral_ann_eq

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
theorem _root_.solution (lam : Measure R) [lam.IsAddHaarMeasure] [SigmaFinite lam] (L P : AddSubgroup R)
    (hPm : MeasurableSet (P : Set R)) (ha : ∀ x y, ψ (x + y) = ψ x * ψ y) (hn : ∀ x, ‖ψ x‖ = 1)
    (hLP : ∀ s ∈ L, ∀ t ∈ P, ψ (s * t) = 1) (hPL : ∀ z, (∀ t ∈ P, ψ (t * z) = 1) → z ∈ L)
    (w : ι → R) :
    ∫ y in box ι (P : Set R), ψ (w ⬝ᵥ y) ∂(Measure.pi fun _ : ι => lam) =
      (box ι (L : Set R)).indicator (fun _ => (lam.real (P : Set R) : ℂ) ^ Fintype.card ι) w := by
  classical
  rw [Measure.restrict_pi_pi]
  simp_rw [psi_dot ha hn]
  rw [integral_fintype_prod_eq_prod (fun i t => ψ (w i * t))]
  simp_rw [integral_ann_eq lam L P hPm ha hLP hPL]
  by_cases hw : w ∈ box ι (L : Set R)
  · rw [Set.indicator_of_mem hw]
    have : ∀ i, w i ∈ L := fun i => hw i (Set.mem_univ i)
    simp [this]
  · rw [Set.indicator_of_notMem hw]
    have : ∃ i, w i ∉ L := by
      by_contra hcon
      push_neg at hcon
      exact hw fun i _ => hcon i
    obtain ⟨i, hi⟩ := this
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])
end GlobalTheory.CompanionTheory.SW.FourierPi
