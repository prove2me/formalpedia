-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.FibreFam.BumpFamily.measurable_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T13:53:18.868744+00:00
-- url     : https://prove2.me/submissions/9de3e88e-60a0-47a9-8f6d-0196a6fe097a

import Mathlib
import Definitions.Def_Formalism_UnipotentAdelicQuotients_SWXSDefs
import Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GeneralLinearActions_GenusMassVolumes
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_DisintegrationDensityContinuous
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_FibreFam_exists_exhaustion
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_FibreFam_BumpFamily_measurable_open
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_FibreFam_BumpFamily_lt_top

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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.FibreFam
variable {V X : Type} [TopologicalSpace V] [MeasurableSpace V] [BorelSpace V]
variable [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
namespace GlobalTheory.CompanionTheory.SW.FibreFam
namespace BumpFamily
theorem _root_.solution [LocallyCompactSpace V] [SecondCountableTopology V] [T2Space V]
    {U : Set V} {B : Set X} {fib : X → Measure V}
    (h : BumpFamily U B fib) (hB : IsOpen B) (hU : IsOpen U) (hc : ∀ b, fib b Uᶜ = 0)
    {A : Set V} (hA : MeasurableSet A) : Measurable fun b => fib b A := by
  obtain ⟨K, W, hKc, hWo, hWK, hKU, -, hWmono, -, hWU⟩ := exists_exhaustion hU
  have hWn : ∀ n, Measurable fun b => fib b (A ∩ W n) := by
    intro n
    haveI : ∀ b, IsFiniteMeasure ((fib b).restrict (W n)) := fun b =>
      isFiniteMeasure_restrict.mpr
        (ne_of_lt (lt_of_le_of_lt (measure_mono (hWK n)) (h.lt_top hU (hKc n) (hKU n) b)))
    have hmeas : Measurable fun b => (fib b).restrict (W n) := by
      refine Measurable.measure_of_isPiSystem (S := {s : Set V | IsOpen s}) BorelSpace.measurable_eq
        isPiSystem_isOpen ?_ ?_
      · intro s hs
        have hso : IsOpen s := hs
        simp only [Measure.restrict_apply hso.measurableSet]
        exact h.measurable_open hB (hso.inter (hWo n))
          (Set.inter_subset_right.trans ((hWK n).trans (hKU n)))
      · simp only [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
        exact h.measurable_open hB (hWo n) ((hWK n).trans (hKU n))
    have h2 := (Measure.measurable_coe hA).comp hmeas
    simpa [Function.comp_def, Measure.restrict_apply hA] using h2
  have hlim : ∀ b, Filter.Tendsto (fun n => fib b (A ∩ W n)) Filter.atTop (𝓝 (fib b A)) := by
    intro b
    have hmono : Monotone fun n => A ∩ W n := fun m n hmn => Set.inter_subset_inter_right _ (hWmono hmn)
    have h2 := tendsto_measure_iUnion_atTop (μ := fib b) hmono
    rw [← Set.inter_iUnion, hWU, measure_inter_conull (hc b)] at h2
    exact h2
  exact measurable_of_tendsto_metrizable hWn (tendsto_pi_nhds.mpr hlim)
end BumpFamily
end GlobalTheory.CompanionTheory.SW.FibreFam
