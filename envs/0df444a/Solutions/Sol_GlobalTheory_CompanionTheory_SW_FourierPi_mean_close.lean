-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.FourierPi.mean_close
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T13:15:14.635589+00:00
-- url     : https://prove2.me/submissions/53cb4d27-c17a-4b52-bd3b-a192a81f1fd0

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_HarrisTaylorCardKilledByIdealEqAbsNormPow

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
theorem _root_.solution (lam : Measure R) [lam.IsAddHaarMeasure] [SigmaFinite lam] (A : Set R)
    (hAm : MeasurableSet A) (hAf : lam A < ⊤) (c : ℝ) (hc0 : 0 ≤ c) (hcm : lam.real A * c = 1)
    (f : (ι → R) → ℂ) (hf : IntegrableOn f (box ι A) (Measure.pi fun _ : ι => lam)) (v : ℂ) (ε : ℝ)
    (h : ∀ u ∈ box ι A, ‖f u - v‖ ≤ ε) :
    ‖(c : ℂ) ^ Fintype.card ι * ∫ u in box ι A, f u ∂(Measure.pi fun _ : ι => lam) - v‖ ≤ ε := by
  classical
  have hBf : (Measure.pi fun _ : ι => lam) (box ι A) < ⊤ := by
    rw [Measure.pi_pi]
    exact ENNReal.prod_lt_top fun _ _ => hAf
  have hvol : (Measure.pi fun _ : ι => lam).real (box ι A) = lam.real A ^ Fintype.card ι := by
    simp [Measure.real, Measure.pi_pi, ENNReal.toReal_prod]
  have hone : (c : ℝ) ^ Fintype.card ι * (Measure.pi fun _ : ι => lam).real (box ι A) = 1 := by
    rw [hvol, ← mul_pow, mul_comm, hcm, one_pow]
  have hconst : IntegrableOn (fun _ : ι → R => v) (box ι A) (Measure.pi fun _ : ι => lam) :=
    integrableOn_const hBf.ne
  have e : (c : ℂ) ^ Fintype.card ι * ∫ u in box ι A, f u ∂(Measure.pi fun _ : ι => lam) - v =
      (c : ℂ) ^ Fintype.card ι * ∫ u in box ι A, (f u - v) ∂(Measure.pi fun _ : ι => lam) := by
    rw [integral_sub hf hconst, setIntegral_const, mul_sub]
    have h1 : (c : ℂ) ^ Fintype.card ι * ((Measure.pi fun _ : ι => lam).real (box ι A) : ℂ) = 1 := by
      exact_mod_cast hone
    rw [Complex.real_smul, ← mul_assoc, h1, one_mul]
  rw [e, norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hc0]
  have hb := norm_setIntegral_le_of_norm_le_const hBf h
  calc c ^ Fintype.card ι * ‖∫ u in box ι A, (f u - v) ∂(Measure.pi fun _ : ι => lam)‖
      ≤ c ^ Fintype.card ι * (ε * (Measure.pi fun _ : ι => lam).real (box ι A)) :=
        mul_le_mul_of_nonneg_left hb (pow_nonneg hc0 _)
    _ = ε * (c ^ Fintype.card ι * (Measure.pi fun _ : ι => lam).real (box ι A)) := by ring
    _ = ε := by rw [hone, mul_one]
end GlobalTheory.CompanionTheory.SW.FourierPi
