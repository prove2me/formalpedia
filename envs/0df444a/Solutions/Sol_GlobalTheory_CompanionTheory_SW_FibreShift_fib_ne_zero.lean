-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.FibreShift.fib_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T15:00:43.017923+00:00
-- url     : https://prove2.me/submissions/0bafc661-91bf-4e08-aa6b-cdebb38155ec

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_DisintegrationDensityExists
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_ContinuousDensitiesEqOfIntegralsOnCompactsStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_DisintegrationDensityContinuous
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_DisintegrationHaarBase
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_FibreShift_lintegral_shift
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_FibreFam_exists_bump


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Topology
open scoped ENNReal NNReal
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.FibreShift
namespace GlobalTheory.CompanionTheory.SW.FibreShift
theorem _root_.solution : ∀ (V X Y : Type) [TopologicalSpace V] [LocallyCompactSpace V] [SecondCountableTopology V] [T2Space V] [MeasurableSpace V] [BorelSpace V] [AddCommGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X] [LocallyCompactSpace X] [SecondCountableTopology X] [T2Space X] [MeasurableSpace X] [BorelSpace X] (μ : Measure V) (ν : Measure X) [IsLocallyFiniteMeasure μ] [μ.IsOpenPosMeasure] [ν.IsAddHaarMeasure] (f : V → Y) (g : V → X) (ι : X → Y), Function.Injective ι → Continuous g → (∀ v, f v = ι (g v)) → ∀ (U W : Set V), IsOpen W → W ⊆ U → W.Nonempty → ∀ fib : X → Measure V, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily μ f ι U ν Set.univ fib → ∀ T : X → V → V, (∀ s, Measurable (T s)) → (∀ s, μ.map (T s) = μ) → (∀ s, ContinuousOn (T s) W) → (∀ s v, T s v ∈ W ↔ v ∈ W) → (∀ s, ∀ v ∈ W, T (-s) (T s v) = v) → (∀ s, ∀ v ∈ W, g (T s v) = g v + s) → ∀ b : X, fib b ≠ 0 := by
  intro V X Y _ _ _ _ _ _ _ _ _ _ _ _ _ _ μ ν _ _ _ f g ι hι hg hf U W hW hWU hne fib hF T hTm hTμ
    hTc hTW hinv hgT b hb
  obtain ⟨v₀, hv₀⟩ := hne
  obtain ⟨φ, hφ, hc, hs, h0, -, h1⟩ := GlobalTheory.CompanionTheory.SW.FibreFam.exists_bump
    (isCompact_singleton (x := v₀)) hW (Set.singleton_subset_iff.2 hv₀)
  have hzero : ∀ c, ∫⁻ v, ENNReal.ofReal (φ v) ∂(fib c) = 0 := by
    intro c
    have key := lintegral_shift hι hg hf hW hWU hF hTm hTμ hTc hTW hinv hgT hφ hc hs h0 (c - b) b
    rw [add_sub_cancel] at key
    rw [← key, hb]
    simp
  have hm : Measurable fun v => ENNReal.ofReal (φ v) :=
    ENNReal.measurable_ofReal.comp hφ.measurable
  have h2 := hF.2.1 _ hm
  simp only [hzero, lintegral_zero] at h2
  have h3 : ∫⁻ v in W, ENNReal.ofReal (φ v) ∂μ = 0 :=
    le_antisymm (h2 ▸ lintegral_mono_set hWU) bot_le
  have hae := (ae_restrict_iff' hW.measurableSet).1 ((lintegral_eq_zero_iff hm).1 h3)
  have hOpen : IsOpen ({v | 0 < φ v} ∩ W) := (isOpen_lt continuous_const hφ).inter hW
  have hpos : 0 < μ ({v | 0 < φ v} ∩ W) :=
    hOpen.measure_pos μ ⟨v₀, by simp [h1 v₀ rfl], hv₀⟩
  have hnull := ae_iff.1 hae
  refine hpos.ne' (measure_mono_null ?_ hnull)
  intro v hv
  rw [Set.mem_setOf_eq]
  intro hcon
  have h4 := hcon hv.2
  simp only [Pi.zero_apply, ENNReal.ofReal_eq_zero] at h4
  exact absurd hv.1 (not_lt.2 h4)
end GlobalTheory.CompanionTheory.SW.FibreShift
