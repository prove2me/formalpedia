-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.HaarScale.exists_continuous_scale
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T13:40:23.350619+00:00
-- url     : https://prove2.me/submissions/6b3a663f-a692-42fe-a3bc-f9f010276ca9

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_TensorLocallyCompactRing
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_UnitsOpenEmbeddingLocalTensor
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_HermitianMatricesLocallyCompactBorel
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_TensorLocallyCompactRingStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_UnitsOpenEmbeddingLocalTensorStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsContinuousScale
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_HaarScale_map_eq_smul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.HaarScale
variable {V P : Type*} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V]
  [LocallyCompactSpace V] [T2Space V] [SecondCountableTopology V] [MeasurableSpace V] [BorelSpace V]
  [TopologicalSpace P] [LocallyCompactSpace P]
namespace GlobalTheory.CompanionTheory.SW.HaarScale
theorem _root_.solution (μ : Measure V) [μ.IsAddHaarMeasure] (T Ti : P → V → V)
    (hT : Continuous (Function.uncurry T)) (hTi : Continuous (Function.uncurry Ti))
    (hadd : ∀ p x y, T p (x + y) = T p x + T p y)
    (hl : ∀ p x, Ti p (T p x) = x) (hr : ∀ p x, T p (Ti p x) = x) :
    ∃ A : P → ℝ≥0, Continuous A ∧ ∀ p, μ.map (T p) = A p • μ := by
  have hTp : ∀ p, Continuous (T p) := fun p => hT.comp (Continuous.prodMk_right p)
  have hTip : ∀ p, Continuous (Ti p) := fun p => hTi.comp (Continuous.prodMk_right p)
  choose A hform using fun p =>
    map_eq_smul μ (T p) (Ti p) (hTp p) (hTip p) (hadd p) (hl p) (hr p)
  refine ⟨A, ?_, hform⟩
  obtain ⟨f, hf1, -, hfc, hf01⟩ := exists_continuous_one_zero_of_isCompact (X := V)
    (s := {0}) (t := ∅) isCompact_singleton isClosed_empty (by simp)
  have hf0 : (0 : V → ℝ) ≤ f := fun x => (hf01 x).1
  have hpos : 0 < ∫ x, f x ∂μ := by
    refine f.continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero hfc hf0 (x := 0) ?_
    rw [hf1 (Set.mem_singleton 0)]; exact one_ne_zero
  have hval : ∀ p, (A p : ℝ) = (∫ x, f (T p x) ∂μ) / ∫ x, f x ∂μ := by
    intro p
    have h1 : ∫ x, f x ∂(μ.map (T p)) = ∫ x, f (T p x) ∂μ :=
      integral_map (hTp p).aemeasurable f.continuous.aestronglyMeasurable
    have h2 : ∫ x, f x ∂(μ.map (T p)) = (A p : ℝ) * ∫ x, f x ∂μ := by
      conv_lhs => rw [hform p]
      rw [integral_smul_nnreal_measure]
      simp [NNReal.smul_def]
    rw [eq_div_iff hpos.ne', ← h2, h1]
  refine continuous_induced_rng.2 ?_
  have hI : Continuous fun p => ∫ x, f (T p x) ∂μ := by
    refine continuous_iff_continuousAt.2 fun p₀ => ?_
    obtain ⟨C, hCc, hCn⟩ := exists_compact_mem_nhds p₀
    have hk : IsCompact (Function.uncurry Ti '' (C ×ˢ tsupport f)) :=
      (hCc.prod hfc).image hTi
    have hcont : ContinuousOn (fun p x => f (T p x)).uncurry (C ×ˢ Set.univ) :=
      (f.continuous.comp hT).continuousOn
    refine (continuousOn_integral_of_compact_support hk hcont ?_).continuousAt hCn
    intro p x hp hx
    by_contra hne
    exact hx ⟨(p, T p x), ⟨hp, subset_tsupport _ hne⟩, hl p x⟩
  exact (hI.div_const _).congr fun p => (hval p).symm
end GlobalTheory.CompanionTheory.SW.HaarScale
