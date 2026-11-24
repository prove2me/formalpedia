-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.HaarTransport.map_addEquiv_haar
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T13:24:07.697871+00:00
-- url     : https://prove2.me/submissions/39fe8807-e998-42d7-bdee-db25c6e36200

import Definitions.Def_Formalism_UnipotentAdelicQuotients_SWXSDefs
import Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GeneralLinearActions_GenusMassVolumes
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_HaarMeasureProdOfAddGroups

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Topology Matrix
open scoped ENNReal NNReal
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.HaarTransport
namespace GlobalTheory.CompanionTheory.SW.HaarTransport
theorem _root_.solution (V V' : Type) [AddCommGroup V] [TopologicalSpace V] [LocallyCompactSpace V]
    [SecondCountableTopology V] [T2Space V] [MeasurableSpace V] [BorelSpace V]
    [IsTopologicalAddGroup V] [AddCommGroup V'] [TopologicalSpace V'] [LocallyCompactSpace V']
    [SecondCountableTopology V'] [T2Space V'] [MeasurableSpace V'] [BorelSpace V']
    [IsTopologicalAddGroup V'] (μ : Measure V) [μ.IsAddHaarMeasure] (μ' : Measure V')
    [μ'.IsAddHaarMeasure] (e : V ≃+ V') (he : Continuous e) (hes : Continuous e.symm) :
    (∃ a : ℝ≥0, a ≠ 0 ∧ μ.map e = a • μ') ∧
      ∀ (L : Set V) (L' : Set V'), IsCompact L → IsOpen L → L.Nonempty →
        (∀ v, e v ∈ L' ↔ v ∈ L) → μ L = μ' L' → μ.map e = μ' := by
  let E : V ≃ₜ+ V' := { e with continuous_toFun := he, continuous_invFun := hes }
  haveI hH : (μ.map e).IsAddHaarMeasure := E.isAddHaarMeasure_map μ
  have ha := Measure.isAddLeftInvariant_eq_smul (μ.map e) μ'
  have ha0 : Measure.addHaarScalarFactor (μ.map e) μ' ≠ 0 :=
    (Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure _ _).ne'
  generalize Measure.addHaarScalarFactor (μ.map e) μ' = a at ha ha0
  have hemb : MeasurableEmbedding e :=
    (Homeomorph.mk e.toEquiv he hes).measurableEmbedding
  refine ⟨⟨a, ha0, ha⟩, ?_⟩
  · intro L L' hLc hLo hLn hL hmass
    have hpre : e ⁻¹' L' = L := by ext v; exact hL v
    have hpos : μ L ≠ 0 := (hLo.measure_pos μ hLn).ne'
    have hfin : μ L ≠ ∞ := hLc.measure_lt_top.ne
    have hLm : μ.map e L' = μ L := by
      rw [hemb.map_apply, hpre]
    have hval : μ L = (a : ℝ≥0∞) * μ L := by
      have h1 := congrArg (fun m => m L') ha
      simp only [Measure.smul_apply, hLm] at h1
      rw [← hmass] at h1
      simpa [ENNReal.smul_def] using h1
    have ha1 : (a : ℝ≥0∞) = 1 := by
      have h2 : (a : ℝ≥0∞) * μ L = 1 * μ L := by rw [one_mul]; exact hval.symm
      exact (ENNReal.mul_left_inj hpos hfin).1 h2
    have ha1' : a = 1 := by exact_mod_cast ha1
    rw [ha, ha1', one_smul]
end GlobalTheory.CompanionTheory.SW.HaarTransport
