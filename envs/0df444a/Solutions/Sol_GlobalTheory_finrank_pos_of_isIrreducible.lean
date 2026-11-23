-- Prove2me | solution 1 for GlobalTheory.finrank_pos_of_isIrreducible
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:53:41.209624+00:00
-- url     : https://prove2.me/submissions/7d024e0d-0c28-4c66-8e2d-aa7a6b447478

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
variable {K : Type*} [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K]
  [MeasurableSpace K] [BorelSpace K] (μ : Measure K)
  {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
  [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]
variable [IsFiniteMeasure μ] [μ.IsMulLeftInvariant]
  (ρ : Representation ℂ K V) (σ : Representation ℂ K W)
omit [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K] [MeasurableSpace K]
  [BorelSpace K]
namespace GlobalTheory
theorem _root_.solution [h : ρ.IsIrreducible] : 0 < Module.finrank ℂ V := by
  rw [Module.finrank_pos_iff]
  by_contra hV
  rw [not_nontrivial_iff_subsingleton] at hV
  have : (⊥ : Subrepresentation ρ) = ⊤ :=
    Subrepresentation.toSubmodule_injective (Subsingleton.elim _ _)
  exact bot_ne_top this
end GlobalTheory
