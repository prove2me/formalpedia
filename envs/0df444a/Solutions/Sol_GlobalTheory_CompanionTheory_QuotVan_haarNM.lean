-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.QuotVan.haarNM
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T14:11:07.939969+00:00
-- url     : https://prove2.me/submissions/693c6b09-0826-43ce-b8ef-2f43ae9d1b28

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerVolume_TopoPolish
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_MapWithDensityEqOfScale
import Theorems.Thm_GlobalTheory_CompanionTheory_QuotVan_modInv_ne_top
import Theorems.Thm_GlobalTheory_CompanionTheory_QuotVan_modInv_ne_zero
import Theorems.Thm_GlobalTheory_CompanionTheory_QuotVan_measurable_modInv
import Theorems.Thm_GlobalTheory_CompanionTheory_QuotVan_map_translate
import Theorems.Thm_GlobalTheory_CompanionTheory_QuotVan_mulMap_injective
import Theorems.Thm_PI_VolStabS_TopoPolish_polish_of_lcsc


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory MeasureTheory.Measure
open scoped ENNReal NNReal
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.QuotVan
namespace GlobalTheory.CompanionTheory.QuotVan
theorem _root_.solution : HaarNM := by
  intro Q _ _ _ _ _ _ _ _ νQ _ N M _ hNc hMc hdec hinf νN _ νM _
  haveI : LocallyCompactSpace N := hNc.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : LocallyCompactSpace M := hMc.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : SecondCountableTopology N := Topology.IsEmbedding.subtypeVal.secondCountableTopology
  haveI : SecondCountableTopology M := Topology.IsEmbedding.subtypeVal.secondCountableTopology
  haveI : PolishSpace N := PI.VolStabS.TopoPolish.polish_of_lcsc N
  haveI : PolishSpace M := PI.VolStabS.TopoPolish.polish_of_lcsc M
  let φ : N × M → Q := fun p => (p.1 : Q) * (p.2 : Q)
  have φc : Continuous φ := by fun_prop
  have φemb : MeasurableEmbedding φ := φc.measurableEmbedding (mulMap_injective N M hinf)
  let f : N × M → ℝ≥0∞ := fun p => modInv N M p.2
  have hf : Measurable f := (measurable_modInv N M).comp measurable_snd
  let ρ : Measure (N × M) := (νN.prod νM).withDensity f
  let ν' : Measure Q := ρ.map φ
  haveI : SigmaFinite ρ := SigmaFinite.withDensity_of_ne_top
    (Filter.Eventually.of_forall fun p => modInv_ne_top N M p.2)
  haveI : SigmaFinite ν' := φemb.sigmaFinite_map
  haveI : ν'.IsMulLeftInvariant := ⟨fun q => by
    obtain ⟨u, hu, m, hm, rfl⟩ := hdec q
    have hS1 : Measurable fun x : N => (⟨u, hu⟩ : N) * conjCE N m x :=
      (continuous_const.mul (map_continuous _)).measurable
    have hS2 : Measurable fun x : M => (⟨m, hm⟩ : M) * x :=
      (continuous_const.mul continuous_id).measurable
    have hS : Measurable fun p : N × M => ((⟨u, hu⟩ : N) * conjCE N m p.1, (⟨m, hm⟩ : M) * p.2) :=
      hS1.prodMap hS2
    have hcomm : (fun x => u * m * x) ∘ φ =
        φ ∘ fun p : N × M => ((⟨u, hu⟩ : N) * conjCE N m p.1, (⟨m, hm⟩ : M) * p.2) := by
      funext p
      show (u * m) * ((p.1 : Q) * p.2) = (u * ((m * p.1) * m⁻¹)) * (m * p.2)
      group
    show map (fun x => u * m * x) (map φ ρ) = map φ ρ
    rw [map_map (measurable_const_mul _) φemb.measurable, hcomm, ← map_map φemb.measurable hS]
    exact congrArg (map φ) (map_translate N M νN νM ⟨u, hu⟩ ⟨m, hm⟩)⟩
  have hν0 : ν' Set.univ ≠ 0 := by
    intro h0
    rw [φemb.map_apply, Set.preimage_univ] at h0
    have hac : (νN.prod νM) ≪ ρ := withDensity_absolutelyContinuous' hf.aemeasurable
      (Filter.Eventually.of_forall fun p => modInv_ne_zero N M p.2)
    exact (isOpen_univ.measure_pos (νN.prod νM) Set.univ_nonempty).ne' (hac h0)
  obtain ⟨n, hn⟩ : ∃ n, ν' (spanningSets (ν' + νQ) n) ≠ 0 := by
    by_contra! h
    exact hν0 (by rw [← iUnion_spanningSets (ν' + νQ)]; exact measure_iUnion_null h)
  have hfin := measure_spanningSets_lt_top (ν' + νQ) n
  rw [Measure.add_apply] at hfin
  obtain ⟨h1, h2⟩ := ENNReal.add_lt_top.1 hfin
  have key := measure_eq_div_smul νQ ν' hn h1.ne
  have hc : νQ (spanningSets (ν' + νQ) n) / ν' (spanningSets (ν' + νQ) n) ≠ ∞ :=
    ENNReal.div_ne_top h2.ne hn
  generalize νQ (spanningSets (ν' + νQ) n) / ν' (spanningSets (ν' + νQ) n) = c at key hc
  refine ⟨fun m => c * modInv N M m, (measurable_modInv N M).const_mul c,
    fun m => ENNReal.mul_ne_top hc (modInv_ne_top N M m), key.trans ?_⟩
  have h3 : (fun p : N × M => c * modInv N M p.2) = c • f := rfl
  rw [h3, withDensity_smul c hf, Measure.map_smul]
end GlobalTheory.CompanionTheory.QuotVan
