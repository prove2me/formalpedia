-- Prove2me | solution 1 for GlobalTheory.hasSum_pi_prod_of_summable_norm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T06:05:23.881838+00:00
-- url     : https://prove2.me/submissions/711cd34e-dd85-4500-8f7e-e32f76651093

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHilbertSchmidtOfFiniteDimensional
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_SplitHeightSummableExpNegAbs
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasSumTupleProdOfSummableNormComplex
import Theorems.Thm_GlobalTheory_splitHeight_summable_pi_prod


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped InnerProductSpace
open GlobalTheory
open Filter Topology
namespace GlobalTheory
theorem _root_.solution : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (J : ι → Type) (f : ∀ i, J i → ℂ), (∀ i, Summable (fun j => ‖f i j‖)) → HasSum (fun j : ∀ i, J i => ∏ i, f i (j i)) (∏ i, ∑' j, f i j) := by
  intro ι _ _ J f hf
  classical
  have hnorm : Summable fun j : ∀ i, J i => ‖∏ i, f i (j i)‖ := by
    have := splitHeight_summable_pi_prod (α := J) (f := fun i x => ‖f i x‖)
      (fun i x => norm_nonneg (f i x)) hf
    refine this.congr fun j => ?_
    exact (norm_prod _ _).symm
  have hs : Summable fun j : ∀ i, J i => ∏ i, f i (j i) := hnorm.of_norm
  have hcof : Tendsto (fun S : ∀ i, Finset (J i) => Fintype.piFinset S) atTop atTop := by
    refine Filter.tendsto_atTop_atTop.2 fun t => ⟨fun i => t.image (· i), fun S hS => ?_⟩
    intro x hx
    exact Fintype.mem_piFinset.2 fun i => hS i (Finset.mem_image_of_mem _ hx)
  have h1 : Tendsto (fun S : ∀ i, Finset (J i) => ∑ x ∈ Fintype.piFinset S, ∏ i, f i (x i))
      atTop (𝓝 (∑' j : ∀ i, J i, ∏ i, f i (j i))) := hs.hasSum.comp hcof
  have hproj : ∀ i, Tendsto (fun S : ∀ i, Finset (J i) => S i) atTop atTop := by
    intro i
    refine Filter.tendsto_atTop_atTop.2 fun b =>
      ⟨Function.update (fun j => (∅ : Finset (J j))) i b, fun S hS => ?_⟩
    have := hS i
    simpa using this
  have h2 : Tendsto (fun S : ∀ i, Finset (J i) => ∏ i, ∑ x ∈ S i, f i x)
      atTop (𝓝 (∏ i, ∑' j, f i j)) :=
    tendsto_finset_prod _ fun i _ => ((hf i).of_norm.hasSum).comp (hproj i)
  have h3 : (fun S : ∀ i, Finset (J i) => ∑ x ∈ Fintype.piFinset S, ∏ i, f i (x i)) =
      fun S => ∏ i, ∑ x ∈ S i, f i x := by
    funext S; exact (Finset.prod_univ_sum S fun i x => f i x).symm
  rw [h3] at h1
  have := tendsto_nhds_unique h1 h2
  rw [← this]; exact hs.hasSum
end GlobalTheory
