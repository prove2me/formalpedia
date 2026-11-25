-- Prove2me | solution 1 for GlobalTheory.ArchMetric.muMin_comap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:29:26.615929+00:00
-- url     : https://prove2.me/submissions/94dc5851-90b1-4e7e-943b-b629740accc7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_MemSaturatedOrderIsoSubspaceSpanSymmApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FinrankMulDiscrRpowLeSumSqOfMemTraceDual
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_ExistsSmulMemOfMemSpanLattice
import Theorems.Thm_GlobalTheory_ArchMetric_muMin_le_quotSlope
import Theorems.Thm_GlobalTheory_ArchMetric_le_muMin_iff
import Theorems.Thm_GlobalTheory_ArchMetric_quotSlope_comap

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
    (h.comap f hf).muMin A' = h.muMin (A'.map (f.restrictScalars (𝓞 K))) := by
  have key : ∀ W : Submodule K V,
      (A' ⊓ (W.comap f).restrictScalars (𝓞 K)).map (f.restrictScalars (𝓞 K)) =
        A'.map (f.restrictScalars (𝓞 K)) ⊓ W.restrictScalars (𝓞 K) := fun W =>
    (Submodule.map_inf_eq_map_inf_comap (f := f.restrictScalars (𝓞 K)) (p := A')
      (p' := W.restrictScalars (𝓞 K))).symm
  have key' : ∀ W : Submodule K V, A' ≤ (W.comap f).restrictScalars (𝓞 K) ↔
      A'.map (f.restrictScalars (𝓞 K)) ≤ W.restrictScalars (𝓞 K) := fun W =>
    (Submodule.map_le_iff_le_comap (f := f.restrictScalars (𝓞 K)) (p := A')
      (q := W.restrictScalars (𝓞 K))).symm
  refine le_antisymm ((le_muMin_iff _).2 fun W hW => ?_) ((le_muMin_iff _).2 fun W hW => ?_)
  · rw [← key, ← h.quotSlope_comap f hf hA (hA.of_le inf_le_left)]
    exact muMin_le_quotSlope _ ((key' W).not.2 hW)
  · rw [← Submodule.comap_map_eq_of_injective hf W] at hW ⊢
    rw [h.quotSlope_comap f hf hA (hA.of_le inf_le_left), key]
    exact muMin_le_quotSlope _ ((key' _).not.1 hW)
end GlobalTheory.ArchMetric
