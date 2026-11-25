-- Prove2me | solution 1 for GlobalTheory.ArchMetric.quotSlope_comap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T06:16:30.02691+00:00
-- url     : https://prove2.me/submissions/d25b0327-9e71-4e11-a4cb-ebe8b6dc2ae3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_MemSaturatedOrderIsoSubspaceSpanSymmApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FinrankMulDiscrRpowLeSumSqOfMemTraceDual
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_ExistsSmulMemOfMemSpanLattice
import Theorems.Thm_GlobalTheory_ArchMetric_degNorm_comap

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
variable {A B : Submodule (𝓞 K) V}
variable (f : V' →ₗ[K] V) (hf : Function.Injective f) {A' : Submodule (𝓞 K) V'}
namespace GlobalTheory.ArchMetric
theorem _root_.solution {B' : Submodule (𝓞 K) V'} (hA : A'.FG) (hB : B'.FG) :
    (h.comap f hf).quotSlope A' B' =
      h.quotSlope (A'.map (f.restrictScalars (𝓞 K))) (B'.map (f.restrictScalars (𝓞 K))) := by
  rw [quotSlope, quotSlope, h.degNorm_comap f hf hA, h.degNorm_comap f hf hB,
    (Submodule.equivMapOfInjective (f.restrictScalars (𝓞 K)) hf A').finrank_eq,
    (Submodule.equivMapOfInjective (f.restrictScalars (𝓞 K)) hf B').finrank_eq]
end GlobalTheory.ArchMetric
