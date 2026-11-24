-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.FibreFam.fibre_family_basic
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T14:09:20.933097+00:00
-- url     : https://prove2.me/submissions/9139f2bd-dccd-413c-b6b5-c16d3e171554

import Mathlib
import Definitions.Def_Formalism_UnipotentAdelicQuotients_SWXSDefs
import Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GeneralLinearActions_GenusMassVolumes
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_DisintegrationDensityContinuous
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_FibreFam_exists_bump
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_FibreFam_le_lintegral_bump
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_FibreFam_BumpFamily_lt_top
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_FibreFam_BumpFamily_measurable_apply

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
namespace GlobalTheory.CompanionTheory.SW.FibreFam
theorem _root_.solution : ∀ (V X Y : Type) [TopologicalSpace V] [LocallyCompactSpace V]
    [SecondCountableTopology V] [T2Space V] [MeasurableSpace V] [BorelSpace V]
    [TopologicalSpace X] [LocallyCompactSpace X] [SecondCountableTopology X] [T2Space X]
    [MeasurableSpace X] [BorelSpace X] (μ : Measure V) (ν : Measure X)
    [IsLocallyFiniteMeasure μ] [IsLocallyFiniteMeasure ν] [ν.IsOpenPosMeasure]
    (f : V → Y) (g : V → X) (ι : X → Y), Function.Injective ι → Continuous g →
    (∀ v, f v = ι (g v)) → ∀ (B : Set X), IsOpen B → ∀ fib : X → Measure V,
    Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily μ f ι (g ⁻¹' B) ν B fib →
    (∀ b, IsLocallyFiniteMeasure (fib b)) ∧ (∀ b, b ∉ B → fib b = 0) ∧
    (∀ A : Set V, MeasurableSet A → Measurable fun b => fib b A) ∧
    ∀ (C : Set V) (D : Set X), IsCompact C → IsCompact D → D ⊆ B →
      ∃ c : ℝ≥0, ∀ b ∈ D, fib b C ≤ c := by
  intro V X Y _ _ _ _ _ _ _ _ _ _ _ _ μ ν _ _ _ f g ι hι hg hfv B hB fib hF
  classical
  obtain ⟨hfib0, -, hbump⟩ := hF
  have hU : IsOpen (g ⁻¹' B) := hB.preimage hg
  have hmemι : ∀ b w, w ∈ f ⁻¹' {ι b} → g w = b := by
    intro b w hw
    apply hι
    rw [← hfv w]
    exact hw
  have hfibB : ∀ b, b ∉ B → fib b = 0 := by
    intro b hb
    have hempty : f ⁻¹' {ι b} ∩ g ⁻¹' B = ∅ := by
      refine Set.subset_empty_iff.mp fun w hw => (hb ?_).elim
      rw [← hmemι b w hw.1]
      exact hw.2
    have h0 := hfib0 b
    rw [hempty, Set.compl_empty] at h0
    exact Measure.measure_univ_eq_zero.mp h0
  have hBF : BumpFamily (g ⁻¹' B) B fib := ⟨hfibB, hbump⟩
  refine ⟨?_, hfibB, ?_, ?_⟩
  · intro b
    refine ⟨fun v => ?_⟩
    by_cases hb : b ∈ B
    · by_cases hgv : g v = b
      · have hvU : v ∈ g ⁻¹' B := by
          rw [Set.mem_preimage, hgv]
          exact hb
        obtain ⟨K, hKn, hKU, hKc⟩ := local_compact_nhds (hU.mem_nhds hvU)
        exact ⟨K, hKn, hBF.lt_top hU hKc hKU b⟩
      · refine ⟨g ⁻¹' {b}ᶜ, (isClosed_singleton.preimage hg).isOpen_compl.mem_nhds hgv, ?_⟩
        have h0 : fib b (g ⁻¹' {b}ᶜ) = 0 := by
          exact measure_mono_null (show g ⁻¹' {b}ᶜ ⊆ (f ⁻¹' {ι b} ∩ g ⁻¹' B)ᶜ from
            fun w hw hw' => hw (hmemι b w hw'.1)) (hfib0 b)
        rw [h0]
        exact ENNReal.zero_lt_top
    · refine ⟨Set.univ, Filter.univ_mem, ?_⟩
      rw [hfibB b hb]
      simp
  · intro A hA
    exact hBF.measurable_apply hB hU (fun b => measure_mono_null
      (show (g ⁻¹' B)ᶜ ⊆ (f ⁻¹' {ι b} ∩ g ⁻¹' B)ᶜ from fun w hw hw' => hw hw'.2) (hfib0 b)) hA
  · intro C D hC hD hDB
    have hC' : IsCompact (C ∩ g ⁻¹' D) := hC.inter_right (hD.isClosed.preimage hg)
    have hC'U : C ∩ g ⁻¹' D ⊆ g ⁻¹' B := fun w hw => hDB hw.2
    obtain ⟨φ, hc, hcs, hs, h0, -, h1⟩ := exists_bump hC' hU hC'U
    obtain ⟨hint, hcont⟩ := hbump φ hc hcs hs
    obtain ⟨M, hM⟩ := hD.exists_bound_of_continuousOn (hcont.mono hDB)
    refine ⟨Real.toNNReal M, fun b hb => ?_⟩
    calc fib b C = fib b (C ∩ (f ⁻¹' {ι b} ∩ g ⁻¹' B)) := (measure_inter_conull (hfib0 b)).symm
      _ ≤ fib b (C ∩ g ⁻¹' D) := by
          refine measure_mono (show C ∩ (f ⁻¹' {ι b} ∩ g ⁻¹' B) ⊆ C ∩ g ⁻¹' D from
            fun w hw => ⟨hw.1, ?_⟩)
          show g w ∈ D
          rw [hmemι b w hw.2.1]
          exact hb
      _ ≤ ∫⁻ v, ENNReal.ofReal (φ v) ∂(fib b) := le_lintegral_bump (fib b) hC' h0 h1
      _ = ENNReal.ofReal (∫ v, φ v ∂(fib b)) :=
          (ofReal_integral_eq_lintegral_ofReal (hint b (hDB hb)) (ae_of_all _ h0)).symm
      _ ≤ ENNReal.ofReal M := ENNReal.ofReal_le_ofReal ((Real.le_norm_self _).trans (hM b hb))
      _ = (Real.toNNReal M : ℝ≥0∞) := rfl
end GlobalTheory.CompanionTheory.SW.FibreFam
