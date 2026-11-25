-- Prove2me | solution 1 for GlobalTheory.finrank_inf_restrictScalars_lt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:23:46.814994+00:00
-- url     : https://prove2.me/submissions/42f2567c-fb12-438a-843d-f95184875bef

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_MemSaturatedOrderIsoSubspaceSpanSymmApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FinrankMulDiscrRpowLeSumSqOfMemTraceDual
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_ExistsSmulMemOfMemSpanLattice

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module Matrix
open scoped ComplexOrder ComplexConjugate
open GlobalTheory
variable {K : Type*} [Field K] [NumberField K] {V V' : Type*} [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [AddCommGroup V'] [Module K V']
  [Module (𝓞 K) V'] [IsScalarTower (𝓞 K) K V']
namespace GlobalTheory
theorem _root_.solution {A : Submodule (𝓞 K) V} (hA : A.FG) {W : Submodule K V}
    (hW : ¬ A ≤ W.restrictScalars (𝓞 K)) :
    finrank (𝓞 K) (A ⊓ W.restrictScalars (𝓞 K) : Submodule (𝓞 K) V) < finrank (𝓞 K) A := by
  haveI := finiteDimensional_span_of_fg hA
  rw [finrank_lattice_eq_finrank_span, finrank_lattice_eq_finrank_span,
    span_inf_restrictScalars]
  refine Submodule.finrank_lt_finrank_of_lt (lt_of_le_of_ne inf_le_left fun h => hW ?_)
  intro x hx
  have : x ∈ Submodule.span K (A : Set V) ⊓ W := by
    rw [h]
    exact Submodule.subset_span hx
  exact this.2
end GlobalTheory
