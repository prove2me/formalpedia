-- Prove2me | solution 1 for GlobalTheory.Mass.LatticeGens.exists_scaled_span
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:30:25.9445+00:00
-- url     : https://prove2.me/submissions/50341f64-fb4c-49f1-a2ed-2d65b79aa0e9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_LatticeQuotientGensAndIntermediateCount

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical
open GlobalTheory GlobalTheory.Mass GlobalTheory.Mass.LatticeGens
namespace GlobalTheory.Mass.LatticeGens
theorem _root_.solution (K V : Type) [Field K] [NumberField K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
    (B : Submodule (𝓞 K) V) (hB : B.FG) :
    ∃ (c : 𝓞 K) (t : Finset V), c ≠ 0 ∧ t.card ≤ Module.finrank K V ∧ (∀ x ∈ t, c • x ∈ B) ∧
      B ≤ Submodule.span (𝓞 K) (t : Set V) := by
  obtain ⟨b, hbB, hspan, hli⟩ := exists_linearIndependent K (B : Set V)
  have hbf : b.Finite := hli.setFinite
  obtain ⟨s, rfl⟩ := hbf.exists_finset_coe
  have hcard : s.card ≤ Module.finrank K V := LinearIndependent.finset_card_le_finrank hli
  obtain ⟨G, rfl⟩ := hB
  have h1 : ∀ x ∈ G, ∃ c : 𝓞 K, c ≠ 0 ∧ c • x ∈ Submodule.span (𝓞 K) (s : Set V) := by
    intro x hx
    have hx' : x ∈ Submodule.span K (s : Set V) := by
      rw [hspan]; exact Submodule.subset_span (Submodule.subset_span hx)
    obtain ⟨c, hc⟩ := multiple_mem_span_of_mem_localization_span (nonZeroDivisors (𝓞 K)) K _ _ hx'
    exact ⟨c, nonZeroDivisors.coe_ne_zero c, hc⟩
  choose! f hf0 hf using h1
  set c : 𝓞 K := ∏ x ∈ G, f x with hc
  have hc0 : c ≠ 0 := Finset.prod_ne_zero_iff.2 hf0
  have hcK : algebraMap (𝓞 K) K c ≠ 0 := by simpa using hc0
  have hcG : ∀ x ∈ G, c • x ∈ Submodule.span (𝓞 K) (s : Set V) := by
    intro x hx
    rw [hc, ← Finset.prod_erase_mul _ _ hx, mul_smul]
    exact Submodule.smul_mem _ _ (hf x hx)
  let φ : V →ₗ[𝓞 K] V := (LinearMap.lsmul K V (algebraMap (𝓞 K) K c)⁻¹).restrictScalars (𝓞 K)
  have hφ : ∀ x, φ (c • x) = x := by
    intro x
    simp only [φ, LinearMap.restrictScalars_apply, LinearMap.lsmul_apply]
    rw [← algebraMap_smul K c x, smul_smul, inv_mul_cancel₀ hcK, one_smul]
  refine ⟨c, s.image φ, hc0, Finset.card_image_le.trans hcard, ?_, ?_⟩
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hx
    rw [← map_smul, hφ]
    exact hbB hy
  · rw [Submodule.span_le]
    intro x hx
    rw [Finset.coe_image, ← Submodule.map_span, ← hφ x]
    exact Submodule.mem_map_of_mem (hcG x hx)
end GlobalTheory.Mass.LatticeGens
