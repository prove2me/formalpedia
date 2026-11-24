-- Prove2me | solution 1 for GlobalTheory.GaussCoset.discrete_of_finite
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T16:10:02.542952+00:00
-- url     : https://prove2.me/submissions/f1258319-be9a-4664-a8c7-fee956696ff1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_SummableGaussianCoset

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped ContDiff
open GlobalTheory GlobalTheory.GaussCoset
namespace GlobalTheory.GaussCoset
theorem _root_.solution {V : Type} [NormedAddCommGroup V] (L : AddSubgroup V)
    (h : {v : V | v ∈ L ∧ ‖v‖ ≤ 1}.Finite) : DiscreteTopology L := by
  rw [discreteTopology_iff_isOpen_singleton_zero]
  have hU : IsOpen (Metric.ball (0 : V) 1 ∩ ({v : V | v ∈ L ∧ ‖v‖ ≤ 1} \ {0})ᶜ) :=
    Metric.isOpen_ball.inter (h.subset Set.sdiff_subset).isClosed.isOpen_compl
  have hset : ({0} : Set L) = Subtype.val ⁻¹' (Metric.ball (0 : V) 1 ∩
      ({v : V | v ∈ L ∧ ‖v‖ ≤ 1} \ {0})ᶜ) := by
    ext z
    constructor
    · intro hz
      rw [Set.mem_singleton_iff] at hz
      subst hz
      simp
    · rintro ⟨h1, h2⟩
      rw [Set.mem_singleton_iff]
      by_contra hne
      have h1' : ‖(z : V)‖ < 1 := by simpa using h1
      apply h2
      refine ⟨⟨z.2, h1'.le⟩, ?_⟩
      intro hz0
      apply hne
      simpa using hz0
  rw [hset]
  exact hU.preimage continuous_subtype_val
end GlobalTheory.GaussCoset
