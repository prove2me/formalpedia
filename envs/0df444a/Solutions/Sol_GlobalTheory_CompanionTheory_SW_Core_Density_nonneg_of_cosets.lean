-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.Core.Density.nonneg_of_cosets
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T13:54:51.423187+00:00
-- url     : https://prove2.me/submissions/20cf74e9-5485-4fb4-a99d-e833785219ac

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_CountData
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_FourierInversionSchwartzBruhatStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_PositiveDefiniteDensity
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_Core_Density_coset_isOpen
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_Core_Density_coset_isCompact

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.Core GlobalTheory.CompanionTheory.SW.Core.Density
variable {V : Type} [AddCommGroup V] [TopologicalSpace V] [MeasurableSpace V]
variable [IsTopologicalAddGroup V] [T2Space V] [LocallyCompactSpace V] [SecondCountableTopology V]
  [BorelSpace V]
namespace GlobalTheory.CompanionTheory.SW.Core.Density
theorem _root_.solution {μ : Measure V} [μ.IsAddHaarMeasure] {f : V → ℝ} (hf : Continuous f)
    (hb : ∀ U ∈ 𝓝 (0 : V), ∃ L : AddSubgroup V, IsCompact (L : Set V) ∧ IsOpen (L : Set V) ∧
      (L : Set V) ⊆ U)
    (hi : ∀ (L : AddSubgroup V) (a : V), IsCompact (L : Set V) → IsOpen (L : Set V) →
      0 ≤ ∫ x in coset L a, f x ∂μ) (x : V) : 0 ≤ f x := by
  by_contra hx
  push_neg at hx
  have hU : (fun t => f (t + x)) ⁻¹' Set.Iio 0 ∈ 𝓝 (0 : V) :=
    ((isOpen_Iio.preimage (hf.comp (continuous_id.add continuous_const))).mem_nhds (by simpa using hx))
  obtain ⟨L, hK, hO, hLU⟩ := hb _ hU
  have hneg : ∀ y ∈ coset L x, f y < 0 := fun y hy => by
    have := hLU hy
    simpa using this
  have hmeas : MeasurableSet (coset L x) := (coset_isOpen hO x).measurableSet
  have hnon : (coset L x).Nonempty := ⟨x, by simp [coset, L.zero_mem]⟩
  have hpos : 0 < μ (coset L x) := (coset_isOpen hO x).measure_pos μ hnon
  have hfi : IntegrableOn (fun y => -f y) (coset L x) μ :=
    (hf.neg.continuousOn).integrableOn_compact (coset_isCompact hK x)
  have h0 : 0 ≤ᵐ[μ.restrict (coset L x)] fun y => -f y := by
    refine (ae_restrict_iff' hmeas).2 (Filter.Eventually.of_forall fun y hy => ?_)
    simpa using (hneg y hy).le
  have hsup : Function.support (fun y => -f y) ∩ coset L x = coset L x := by
    refine Set.inter_eq_right.2 fun y hy => ?_
    simpa using (hneg y hy).ne
  have := (setIntegral_pos_iff_support_of_nonneg_ae h0 hfi).2 (by rw [hsup]; exact hpos)
  rw [integral_neg] at this
  linarith [hi L x hK hO]
end GlobalTheory.CompanionTheory.SW.Core.Density
