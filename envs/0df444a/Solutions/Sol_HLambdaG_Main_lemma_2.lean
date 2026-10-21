-- Prove2me | solution 1 for HLambdaG.Main.lemma_2
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T04:50:09.627177+00:00
-- url     : https://prove2.me/submissions/e08aa687-7263-409a-90a0-8d01f53f9e9a

import Mathlib
import Definitions.Def_HLambdaG_Main_Setting

set_option autoImplicit false
open scoped NNReal
open HLambdaG.Main Filter Topology

theorem solution (τ : TimeChange) (t : ℝ≥0) :
    t ≤ τ.T (inv τ t) ∧ leftLim τ (inv τ t) ≤ t := by
  set A : Set ℝ≥0 := {s | t < τ.T s} with hA
  have hne : A.Nonempty := by
    have := (τ.tendsto.eventually (eventually_gt_atTop t)).and (eventually_ge_atTop 0)
    obtain ⟨s, hs, _⟩ := this.exists
    exact ⟨s, hs⟩
  have hinv : inv τ t = sInf A := rfl
  have hup : ∀ s, inv τ t < s → s ∈ A := by
    intro s hs
    rw [hinv] at hs
    obtain ⟨a, haA, has⟩ := exists_lt_of_csInf_lt hne hs
    exact lt_of_lt_of_le haA (τ.mono has.le)
  constructor
  · have hc : ContinuousWithinAt τ.T (Set.Ioi (inv τ t)) (inv τ t) :=
      (τ.rcont (inv τ t)).mono Set.Ioi_subset_Ici_self
    have hev : ∀ᶠ s in 𝓝[Set.Ioi (inv τ t)] (inv τ t), t ≤ τ.T s :=
      eventually_nhdsWithin_of_forall (fun s hs => (hup s hs).le)
    exact ge_of_tendsto hc hev
  · unfold leftLim
    apply csSup_le'
    rintro _ ⟨u, hu, rfl⟩
    by_contra hcon
    rw [not_le] at hcon
    have : inv τ t ≤ u := csInf_le (OrderBot.bddBelow A) hcon
    exact absurd hu (not_lt.mpr this)
