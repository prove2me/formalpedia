-- Prove2me | solution 1 for GlobalTheory.hasSum_multilinear_tuples
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:43:13.354678+00:00
-- url     : https://prove2.me/submissions/e8f018d1-01bc-4a5d-9919-d950d1ab5118

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_SummablePiProd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_SetIntegralPowEqZeroOfPosFreqEuclidean
import Theorems.Thm_GlobalTheory_summable_norm_multilinear_tuples

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Filter Topology
open scoped Real FourierTransform Pointwise
open GlobalTheory
variable {ι : Type*} [Fintype ι] {J : ι → Type*}
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {V : ι → Type*} [∀ i, NormedAddCommGroup (V i)]
  [∀ i, NormedSpace 𝕜 (V i)] {W : Type*} [NormedAddCommGroup W] [NormedSpace 𝕜 W]
namespace GlobalTheory
theorem _root_.solution [CompleteSpace W] (M : ContinuousMultilinearMap 𝕜 V W)
    {x : ∀ i, J i → V i} {A : ∀ i, V i} (hx : ∀ i, Summable fun j => ‖x i j‖)
    (hA : ∀ i, HasSum (x i) (A i)) :
    HasSum (fun t : ∀ i, J i => M fun i => x i (t i)) (M A) := by
  classical
  have hs := (summable_norm_multilinear_tuples M hx).of_norm.hasSum
  have hpi : Tendsto (fun s : ∀ i, Finset (J i) => Fintype.piFinset s) atTop atTop := by
    refine tendsto_atTop_atTop_of_monotone (fun s s' hss => Fintype.piFinset_subset _ _ hss)
      fun T => ⟨fun i => T.image fun t => t i, fun t ht => ?_⟩
    exact Fintype.mem_piFinset.2 fun i => Finset.mem_image_of_mem _ ht
  have h1 : Tendsto (fun s : ∀ i, Finset (J i) => M fun i => ∑ j ∈ s i, x i j) atTop (𝓝 (M A)) := by
    refine (M.cont.tendsto A).comp (tendsto_pi_nhds.2 fun i => ?_)
    refine Tendsto.comp (hA i) (g := fun s => ∑ j ∈ s, x i j) (f := fun s : ∀ i, Finset (J i) => s i) ?_
    refine tendsto_atTop_atTop_of_monotone (fun s s' hss => hss i) fun T => ?_
    exact ⟨Function.update (fun _ => ∅) i T, by simp⟩
  have h2 : Tendsto (fun s : ∀ i, Finset (J i) => M fun i => ∑ j ∈ s i, x i j) atTop
      (𝓝 (∑' t : ∀ i, J i, M fun i => x i (t i))) := by
    have hs' : Tendsto (fun s : Finset (∀ i, J i) => ∑ t ∈ s, M fun i => x i (t i)) atTop
        (𝓝 (∑' t : ∀ i, J i, M fun i => x i (t i))) := hs
    exact (hs'.comp hpi).congr fun s => (M.map_sum_finset x s).symm
  rwa [tendsto_nhds_unique h1 h2]
end GlobalTheory
