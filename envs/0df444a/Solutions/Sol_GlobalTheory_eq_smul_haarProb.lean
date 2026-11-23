-- Prove2me | solution 1 for GlobalTheory.eq_smul_haarProb
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:53:26.04883+00:00
-- url     : https://prove2.me/submissions/33c8d26d-9214-4544-8d7d-aa6ba23fe987

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_IntegralConjInnerMulInnerOfIsEmptyEquiv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory MeasureTheory.Measure
open scoped InnerProductSpace ComplexConjugate
open GlobalTheory
variable (K : Type*) [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K]
  [MeasurableSpace K] [BorelSpace K]
variable {K}
namespace GlobalTheory
theorem _root_.solution (μ : Measure K) [μ.IsHaarMeasure] :
    μ = μ Set.univ • haarProb K := by
  have h := isMulInvariant_eq_smul_of_compactSpace μ (haarProb K)
  have h1 : μ Set.univ = haarScalarFactor μ (haarProb K) := by
    conv_lhs => rw [h]
    simp
  rw [h1]
  exact h
end GlobalTheory
