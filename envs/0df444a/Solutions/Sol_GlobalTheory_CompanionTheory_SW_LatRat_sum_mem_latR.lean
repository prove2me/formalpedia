-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.LatRat.sum_mem_latR
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:31:38.129342+00:00
-- url     : https://prove2.me/submissions/fdf68ec5-fb2b-45f4-bd6d-f3195338a75e

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_LatticeStableAlmostEverywhere

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.LatRat
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
namespace GlobalTheory.CompanionTheory.SW.LatRat
theorem _root_.solution {d : ℕ} {b : Module.Basis (Fin d) F E} {v : HeightOneSpectrum (𝓞 F)} {ι : Type}
    (s : Finset ι) (f : ι → Fv F v ⊗[F] E) (h : ∀ c ∈ s, f c ∈ latR b v) : ∑ c ∈ s, f c ∈ latR b v := by
  intro k
  rw [map_sum, Finsupp.finsetSum_apply]
  exact sum_mem fun c hc => h c hc k
end GlobalTheory.CompanionTheory.SW.LatRat
