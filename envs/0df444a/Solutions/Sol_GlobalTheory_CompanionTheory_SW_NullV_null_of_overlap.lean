-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.NullV.null_of_overlap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T20:24:17.800463+00:00
-- url     : https://prove2.me/submissions/c1172975-4ab9-47bf-a7b8-fc42091215a7

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_HermitianNondegRepresentsNonzeroScalar
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_CompletionIsLocalRing
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_TensorLocallyCompactRing
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_HaarMeasureNonunitsNull
import Theorems.Thm_Formalism_FrobeniusOrbits_Group_key
import Theorems.Thm_Formalism_FrobeniusOrbits_ThickOrbit_key
import Theorems.Thm_Formalism_FrobeniusOrbits_galEquiv_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.FrobeniusOrbits.galEquiv_apply
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
noncomputable section
open scoped Pointwise
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.NullV
namespace GlobalTheory.CompanionTheory.SW.NullV
theorem _root_.solution {V : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V]
    [LocallyCompactSpace V] [SecondCountableTopology V] [T2Space V] [MeasurableSpace V] [BorelSpace V]
    (μ : Measure V) [μ.IsAddHaarMeasure] {Z : Set V} (hZ : MeasurableSet Z) (u : ℕ → V)
    (hu : Filter.Tendsto u Filter.atTop (𝓝 0))
    (hov : ∀ (x : V) (s : Finset ℕ), (∀ i ∈ s, x - u i ∈ Z) → s.card ≤ 2) : μ Z = 0 := by
  classical
  have hcov : Z = ⋃ n, Z ∩ compactCovering V n := by
    rw [← Set.inter_iUnion, iUnion_compactCovering, Set.inter_univ]
  rw [hcov]
  refine measure_iUnion_null fun n => ?_
  have hC : IsCompact (compactCovering V n) := isCompact_compactCovering V n
  generalize compactCovering V n = C at hC
  have hZ' : MeasurableSet (Z ∩ C) := hZ.inter hC.measurableSet
  have hT : IsCompact (insert (0 : V) (Set.range u)) := hu.isCompact_insert_range
  have hD : IsCompact (C + insert (0 : V) (Set.range u)) := hC.add hT
  generalize hDdef : C + insert (0 : V) (Set.range u) = D at hD
  have hDm : MeasurableSet D := hD.measurableSet
  have hDfin : μ D ≠ ∞ := hD.measure_lt_top.ne
  by_contra h0
  obtain ⟨N, hN⟩ := ENNReal.exists_nat_mul_gt h0 (b := 2 * μ D) (ENNReal.mul_ne_top (by simp) hDfin)
  have hA : ∀ i, MeasurableSet ((fun x => x - u i) ⁻¹' (Z ∩ C)) :=
    fun i => (measurable_sub_const (u i)) hZ'
  have hpt : ∀ x, ∑ i ∈ Finset.range N, ((fun x => x - u i) ⁻¹' (Z ∩ C)).indicator (1 : V → ℝ≥0∞) x ≤
      D.indicator (fun _ => (2 : ℝ≥0∞)) x := by
    intro x
    have hsum : ∑ i ∈ Finset.range N, ((fun x => x - u i) ⁻¹' (Z ∩ C)).indicator (1 : V → ℝ≥0∞) x =
        (((Finset.range N).filter fun i => x - u i ∈ Z ∩ C).card : ℝ≥0∞) := by
      simp only [Set.indicator_apply, Set.mem_preimage, Pi.one_apply]
      rw [Finset.sum_boole]
    rw [hsum]
    by_cases hs : ((Finset.range N).filter fun i => x - u i ∈ Z ∩ C) = ∅
    · rw [hs]; simp
    · obtain ⟨i, hi⟩ := Finset.nonempty_iff_ne_empty.2 hs
      have hxD : x ∈ D := by
        rw [← hDdef]
        refine Set.mem_add.2 ⟨x - u i, (Finset.mem_filter.1 hi).2.2, u i, Or.inr ⟨i, rfl⟩, by abel⟩
      rw [Set.indicator_of_mem hxD]
      have := hov x ((Finset.range N).filter fun i => x - u i ∈ Z ∩ C)
        (fun i hi => (Finset.mem_filter.1 hi).2.1)
      exact_mod_cast this
  have key : (N : ℝ≥0∞) * μ (Z ∩ C) ≤ 2 * μ D := by
    calc (N : ℝ≥0∞) * μ (Z ∩ C)
        = ∑ i ∈ Finset.range N, μ ((fun x => x - u i) ⁻¹' (Z ∩ C)) := by
          have : ∀ i, μ ((fun x => x - u i) ⁻¹' (Z ∩ C)) = μ (Z ∩ C) := by
            intro i
            simp only [sub_eq_add_neg]
            exact measure_preimage_add_right μ (-u i) (Z ∩ C)
          rw [Finset.sum_congr rfl fun i _ => this i]
          simp
      _ = ∑ i ∈ Finset.range N, ∫⁻ x, ((fun x => x - u i) ⁻¹' (Z ∩ C)).indicator (1 : V → ℝ≥0∞) x ∂μ := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [lintegral_indicator_one (hA i)]
      _ = ∫⁻ x, ∑ i ∈ Finset.range N, ((fun x => x - u i) ⁻¹' (Z ∩ C)).indicator (1 : V → ℝ≥0∞) x ∂μ := by
          rw [lintegral_finsetSum]
          intro i _
          exact measurable_one.indicator (hA i)
      _ ≤ ∫⁻ x, D.indicator (fun _ => (2 : ℝ≥0∞)) x ∂μ := lintegral_mono hpt
      _ = 2 * μ D := by
          rw [lintegral_indicator hDm, lintegral_const, Measure.restrict_apply_univ]
  exact absurd hN (not_lt.2 key)
end GlobalTheory.CompanionTheory.SW.NullV
