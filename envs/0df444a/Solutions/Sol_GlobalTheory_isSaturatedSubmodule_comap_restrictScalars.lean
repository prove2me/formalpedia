-- Prove2me | solution 1 for GlobalTheory.isSaturatedSubmodule_comap_restrictScalars
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-26T02:49:48.101986+00:00
-- url     : https://prove2.me/submissions/f2b1e32a-0f14-4ff2-9909-8da3fc455aba

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_MemSaturatedOrderIsoSubspaceSpanSymmApply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped nonZeroDivisors Pointwise
open GlobalTheory
variable {R : Type*} [CommRing R] (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]
  {V : Type*} [AddCommGroup V] [Module R V] [Module K V] [IsScalarTower R K V]
variable {K}
theorem _root_.solution {M : Type*} [AddCommGroup M] [Module R M]
    (f : M →ₗ[R] V) (W : Submodule K V) :
    IsSaturatedSubmodule ((W.restrictScalars R).comap f) := by
  unfold GlobalTheory.IsSaturatedSubmodule
  ext x
  rw [GlobalTheory.mem_saturation_iff']
  constructor
  · rintro ⟨a, ha, hax⟩
    have hax' : f (a • x) ∈ W := hax
    rw [map_smul, ← algebraMap_smul K a (f x)] at hax'
    have h0 : algebraMap R K a ≠ 0 := by
      have : Nontrivial R := (algebraMap R K).domain_nontrivial
      exact IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors ha
    show f x ∈ W
    have := W.smul_mem (algebraMap R K a)⁻¹ hax'
    rwa [inv_smul_smul₀ h0] at this
  · intro hx
    exact ⟨1, one_mem _, by rwa [one_smul]⟩

