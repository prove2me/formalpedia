-- Prove2me | solution 1 for GlobalTheory.ArchMetric.muMax_comap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:29:10.825627+00:00
-- url     : https://prove2.me/submissions/49b4f362-e604-4ce8-a2a3-e35f5d686bc5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_MemSaturatedOrderIsoSubspaceSpanSymmApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FinrankMulDiscrRpowLeSumSqOfMemTraceDual
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_ExistsSmulMemOfMemSpanLattice
import Theorems.Thm_GlobalTheory_ArchMetric_slope_comap

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
theorem _root_.solution (hA : A'.FG) :
    (h.comap f hf).muMax A' = h.muMax (A'.map (f.restrictScalars (𝓞 K))) := by
  have hf' : Function.Injective (f.restrictScalars (𝓞 K)) := hf
  have hne : ∀ B : Submodule (𝓞 K) V', B.map (f.restrictScalars (𝓞 K)) = ⊥ ↔ B = ⊥ := fun B => by
    rw [← Submodule.map_bot (f.restrictScalars (𝓞 K)),
      (Submodule.map_injective_of_injective hf').eq_iff]
  refine le_antisymm ((muMax_le_iff _).2 fun B hB h0 => ?_) ((muMax_le_iff _).2 fun B hB h0 => ?_)
  · rw [h.slope_comap f hf (hA.of_le hB)]
    exact h.slope_le_muMax (Submodule.map_mono hB) ((hne B).not.2 h0)
  · have h1 : (B.comap (f.restrictScalars (𝓞 K))).map (f.restrictScalars (𝓞 K)) = B :=
      Submodule.map_comap_eq_self (hB.trans LinearMap.map_le_range)
    have h2 : B.comap (f.restrictScalars (𝓞 K)) ≤ A' :=
      (Submodule.comap_mono hB).trans (Submodule.comap_map_eq_of_injective hf' A').le
    rw [← h1, ← h.slope_comap f hf (hA.of_le h2)]
    exact slope_le_muMax _ h2 ((hne _).not.1 (h1.symm ▸ h0))
end GlobalTheory.ArchMetric
