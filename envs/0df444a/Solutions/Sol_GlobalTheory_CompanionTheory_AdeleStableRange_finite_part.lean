-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.AdeleStableRange.finite_part
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:33:10.507956+00:00
-- url     : https://prove2.me/submissions/7c0c917d-5226-47ca-ba3f-97221008bf23

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_AdeleRingStableRangeOne
import Theorems.Thm_GlobalTheory_CompanionTheory_AdeleStableRange_local_val

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.AdeleStableRange
namespace GlobalTheory.CompanionTheory.AdeleStableRange
theorem _root_.solution (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
    [IsFractionRing R K] (a b : FiniteAdeleRing R K) (hab : IsCoprime a b) :
    ∃ t : FiniteAdeleRing R K, IsUnit (a + t * b) := by
  obtain ⟨x, y, hxy⟩ := hab
  have hloc : ∀ v : HeightOneSpectrum R, x v * a v + y v * b v = 1 := fun v =>
    congrArg (fun z : FiniteAdeleRing R K => z v) hxy
  choose e he hne hval using fun v : HeightOneSpectrum R =>
    local_val (Valued.v : Valuation (v.adicCompletion K) _) (a v) (b v) (x v) (y v) (hloc v)
  have hint : ∀ v : HeightOneSpectrum R, e v ∈ v.adicCompletionIntegers K := by
    intro v
    rcases he v with h | h <;> rw [h]
    · exact zero_mem _
    · exact one_mem _
  let E : FiniteAdeleRing R K := ⟨e, Filter.Eventually.of_forall hint⟩
  refine ⟨E, ?_⟩
  rw [FiniteAdeleRing.isUnit_iff]
  refine ⟨fun v h0 => hne v h0, ?_⟩
  filter_upwards [a.2, b.2, x.2, y.2] with v h1 h2 h3 h4
  exact hval v h1 h2 h3 h4
end GlobalTheory.CompanionTheory.AdeleStableRange
