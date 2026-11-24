-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Equi.InfScale.map_theta_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:45:25.572752+00:00
-- url     : https://prove2.me/submissions/fe0eff14-4585-4220-9a9a-12d1c1446c24

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CosetOff
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_InfiniteAdelesLocalRingTotallyReal
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ScalingMeasureProductArchimedean
import Theorems.Thm_GlobalTheory_CompanionTheory_Equi_InfScale_eInf_theta
import Theorems.Thm_GlobalTheory_CompanionTheory_Equi_InfScale_finrank_fun_places

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
theorem _root_.solution {F : Type} [Field F] [NumberField F] (h : IsTotallyReal F) (θ : ℝ →+* Ainf F)
    (li : Measure (Ainf F)) [li.IsAddHaarMeasure] {ε : ℝ} (hε : 0 < ε) :
    Measure.map (fun y : Ainf F => θ ε * y) li =
      ENNReal.ofReal ((ε ^ Module.finrank ℚ F)⁻¹) • li := by
  haveI : BorelSpace (Ainf F) := ⟨rfl⟩
  have hc : Continuous (eInf F h) := continuous_eInf F h
  have hcs : Continuous (eInf F h).symm := continuous_eInf_symm F h
  have hm : Measurable (eInf F h) := hc.measurable
  have hms : Measurable (eInf F h).symm := hcs.measurable
  have hL : Measurable (fun x : InfinitePlace F → ℝ => ε • x) := (continuous_const_smul ε).measurable
  have hθ : (fun y : Ainf F => θ ε * y) = (eInf F h).symm ∘ (fun x => ε • x) ∘ (eInf F h) := by
    funext y
    apply (eInf F h).injective
    simp only [Function.comp_apply, RingEquiv.apply_symm_apply, map_mul]
    funext w
    rw [Pi.mul_apply, Pi.smul_apply, eInf_theta h θ ε w, smul_eq_mul]
  haveI : (Measure.map (eInf F h) li).IsAddHaarMeasure :=
    AddEquiv.isAddHaarMeasure_map li (eInf F h).toAddEquiv hc hcs
  have hdet : LinearMap.det (ε • (LinearMap.id : (InfinitePlace F → ℝ) →ₗ[ℝ] (InfinitePlace F → ℝ))) ≠ 0 := by
    rw [LinearMap.det_smul, LinearMap.det_id, mul_one]
    exact pow_ne_zero _ hε.ne'
  have hmapL := Measure.map_linearMap_addHaar_eq_smul_addHaar (Measure.map (eInf F h) li) hdet
  rw [LinearMap.det_smul, LinearMap.det_id, mul_one, finrank_fun_places F h] at hmapL
  have hcoe : (⇑(ε • (LinearMap.id : (InfinitePlace F → ℝ) →ₗ[ℝ] (InfinitePlace F → ℝ)))) =
      fun x => ε • x := by
    funext x
    simp
  rw [hcoe] at hmapL
  have hid : (eInf F h).symm ∘ (eInf F h) = id := by
    funext x
    simp
  rw [hθ, ← Measure.map_map hms (hL.comp hm), ← Measure.map_map hL hm, hmapL, Measure.map_smul,
    Measure.map_map hms hm, hid, Measure.map_id, abs_of_pos (inv_pos.mpr (pow_pos hε _))]
end GlobalTheory.CompanionTheory.Equi.InfScale
