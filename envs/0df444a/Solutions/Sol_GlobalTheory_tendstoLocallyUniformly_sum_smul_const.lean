-- Prove2me | solution 1 for GlobalTheory.tendstoLocallyUniformly_sum_smul_const
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:37:01.333359+00:00
-- url     : https://prove2.me/submissions/cc1cd2a2-5b41-42db-9ec8-63be810bcc16

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_DifferentiableAtLimitOfDirectionalDerivsConverge

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped ContDiff Topology
open GlobalTheory
open Filter
namespace GlobalTheory
theorem _root_.solution {E : Type} [TopologicalSpace E] {F : Type}
    [NormedAddCommGroup F] [NormedSpace ℂ F] {A : Type} (s : Finset A) (L : A → F)
    (f : A → ℕ → E → ℂ) (ψ : A → E → ℂ)
    (h : ∀ a, TendstoLocallyUniformly (f a) (ψ a) atTop) :
    TendstoLocallyUniformly (fun j y => ∑ a ∈ s, f a j y • L a)
      (fun y => ∑ a ∈ s, ψ a y • L a) atTop := by
  classical
  have hterm : ∀ a, TendstoLocallyUniformly (fun j y => f a j y • L a)
      (fun y => ψ a y • L a) atTop := by
    intro a
    have hu : UniformContinuous (fun z : ℂ => z • L a) :=
      ((ContinuousLinearMap.id ℂ ℂ).smulRight (L a)).uniformContinuous
    exact hu.comp_tendstoLocallyUniformly (h a)
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact fun u hu x => ⟨Set.univ, Filter.univ_mem,
      Filter.Eventually.of_forall fun _ _ _ => refl_mem_uniformity hu⟩
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (hterm a).add ih
end GlobalTheory
