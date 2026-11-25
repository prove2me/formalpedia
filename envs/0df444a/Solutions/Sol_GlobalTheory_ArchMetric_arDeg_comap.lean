-- Prove2me | solution 1 for GlobalTheory.ArchMetric.arDeg_comap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:22:38.110069+00:00
-- url     : https://prove2.me/submissions/f8865eb5-872a-427c-b118-2acaa762a3c4

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
open GlobalTheory.ArchMetric
variable {K : Type*} [Field K] [NumberField K] {V V' : Type*} [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [AddCommGroup V'] [Module K V']
  [Module (𝓞 K) V'] [IsScalarTower (𝓞 K) K V'] (h : ArchMetric K V)
variable {A : Submodule (𝓞 K) V} {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace GlobalTheory.ArchMetric
theorem _root_.solution (f : V' →ₗ[K] V) (hf : Function.Injective f) {A : Submodule (𝓞 K) V'}
    (hA : A.FG) : (h.comap f hf).arDeg A = h.arDeg (A.map (f.restrictScalars (𝓞 K))) := by
  obtain ⟨e, he⟩ := exists_isLatticeFrame hA
  rw [arDeg_eq_frameDeg _ hA he, arDeg_eq_frameDeg _ (hA.map _) (he.map f hf),
    frameDeg_eq_relIndex, frameDeg_eq_relIndex]
  have : Submodule.span (𝓞 K) (Set.range (f ∘ e)) =
      (Submodule.span (𝓞 K) (Set.range e)).map (f.restrictScalars (𝓞 K)) := by
    rw [Submodule.map_span, Set.range_comp]
    rfl
  rw [this, Submodule.map_toAddSubgroup, Submodule.map_toAddSubgroup,
    AddSubgroup.relIndex_map_map_of_injective _ _ hf]
  rfl
end GlobalTheory.ArchMetric
