-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Equi.InfScale.map_theta_mul_pi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T13:01:36.324442+00:00
-- url     : https://prove2.me/submissions/9ca69c3a-0047-4e22-b71b-1802437ad57e

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CosetOff
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_InfiniteAdelesLocalRingTotallyReal
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ScalingMeasureProductArchimedean
import Theorems.Thm_GlobalTheory_CompanionTheory_Equi_InfScale_eInf_theta
import Theorems.Thm_GlobalTheory_CompanionTheory_Equi_InfScale_map_theta_mul
import Theorems.Thm_GlobalTheory_CompanionTheory_Equi_InfScale_pi_const_smul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter GlobalTheory.CompanionTheory.Equi
open scoped Classical
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Equi GlobalTheory.CompanionTheory.Equi.InfScale
open GlobalTheory.CompanionTheory.SW.LocInf
namespace GlobalTheory.CompanionTheory.Equi.InfScale
theorem _root_.solution : ∀ (F : Type) [Field F] [NumberField F], IsTotallyReal F → ∀ θ : ℝ →+* Ainf F, Continuous θ →
    ∀ li : Measure (Ainf F), li.IsAddHaarMeasure → ∀ (ι : Type) [Fintype ι] (ε : ℝ), 0 < ε →
    Measure.map (fun (y : ι → Ainf F) (i : ι) => θ ε * y i) (Measure.pi fun _ => li) =
      ENNReal.ofReal ((ε ^ (Module.finrank ℚ F * Fintype.card ι))⁻¹) • Measure.pi fun _ => li := by
  intro F _ _ h θ _ li _ ι _ ε hε
  haveI : BorelSpace (Ainf F) := ⟨rfl⟩
  have h1 := map_theta_mul h θ li hε
  have hc : Continuous (eInf F h) := continuous_eInf F h
  have hcs : Continuous (eInf F h).symm := continuous_eInf_symm F h
  have hm : Measurable (eInf F h) := hc.measurable
  have hms : Measurable (eInf F h).symm := hcs.measurable
  haveI : (Measure.map (eInf F h) li).IsAddHaarMeasure :=
    AddEquiv.isAddHaarMeasure_map li (eInf F h).toAddEquiv hc hcs
  haveI : SigmaFinite (Measure.map (eInf F h) li) := Measure.IsAddHaarMeasure.sigmaFinite _
  let me : (InfinitePlace F → ℝ) ≃ᵐ Ainf F :=
    { toEquiv := (eInf F h).symm.toEquiv
      measurable_toFun := hms
      measurable_invFun := hm }
  have hme : (⇑me : (InfinitePlace F → ℝ) → Ainf F) = (eInf F h).symm := rfl
  have hli : Measure.map me (Measure.map (eInf F h) li) = li := by
    rw [Measure.map_map me.measurable hm, hme]
    have hid : ((eInf F h).symm ∘ (eInf F h)) = id := by
      funext x
      simp
    rw [hid, Measure.map_id]
  haveI : SigmaFinite li := by
    rw [← hli]
    exact MeasurableEquiv.sigmaFinite_map me
  haveI hsf : SigmaFinite (ENNReal.ofReal ((ε ^ Module.finrank ℚ F)⁻¹) • li) := by
    have hle : ENNReal.ofReal ((ε ^ Module.finrank ℚ F)⁻¹) • li =
        ((ε ^ Module.finrank ℚ F)⁻¹).toNNReal • li := rfl
    rw [hle]
    infer_instance
  have hmeas : Measurable (fun y : Ainf F => θ ε * y) := by
    have hθ' : (fun y : Ainf F => θ ε * y) = (eInf F h).symm ∘ (fun x => ε • x) ∘ (eInf F h) := by
      funext y
      apply (eInf F h).injective
      simp only [Function.comp_apply, RingEquiv.apply_symm_apply, map_mul]
      funext w
      rw [Pi.mul_apply, Pi.smul_apply, eInf_theta h θ ε w, smul_eq_mul]
    rw [hθ']
    exact hms.comp ((continuous_const_smul ε).measurable.comp hm)
  have h2 := Measure.pi_map_pi (μ := fun _ : ι => li) (f := fun _ y => θ ε * y)
    (hμ := fun _ => by
      show SigmaFinite (Measure.map (fun y : Ainf F => θ ε * y) li)
      rw [h1]
      exact hsf)
    (fun _ => hmeas.aemeasurable)
  rw [h2]
  simp only [h1]
  rw [pi_const_smul ι li _, ← ENNReal.ofReal_pow (inv_nonneg.mpr (pow_nonneg hε.le _)), inv_pow, ← pow_mul]
end GlobalTheory.CompanionTheory.Equi.InfScale
