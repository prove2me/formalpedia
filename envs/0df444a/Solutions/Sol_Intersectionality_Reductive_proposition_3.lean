-- Prove2me | solution 1 for Intersectionality.Reductive.proposition_3
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-24T07:04:01.697397+00:00
-- url     : https://prove2.me/submissions/1ec3ab36-8e6a-4e84-b2d6-8af854c909df

import Mathlib
import Definitions.Def_Intersectionality_Reductive_Setting
import Theorems.Thm_Intersectionality_Reductive_lemma_3
import Theorems.Thm_Intersectionality_Reductive_lemma_4
import Theorems.Thm_Intersectionality_Reductive_poincare_miranda_step

open Filter Topology
open Intersectionality.Reductive

theorem solution (X : Set ℝ) (hX : X.OrdConnected) (hXnt : X.Nontrivial) [Nonempty ↥X]
    (n : ℕ) (hn : 2 ≤ n) (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1) (Q : Set (↥X → ↥X))
    (hQ : Intersectionality.Generic.IsPolicyFamily Q) :
    ∃ U : Set (Intersectionality.Generic.DistSpace X n), IsOpen U ∧ U.Nonempty ∧ ∀ p ∈ U,
      ∃ q : Intersectionality.Generic.Grp n → (↥X → ↥X), (∀ g, q g ∈ Q) ∧ Intersectionality.Generic.IsNonintersectional q ∧
        ∃ xs : ↥X, IsReductiveRepresentative p.1 α q xs := by
  obtain ⟨x0⟩ := (inferInstance : Nonempty ↥X)
  obtain ⟨pbar, a, b, hab, h5⟩ := lemma_4 X hX hXnt n hn α hα0 hα1 Q hQ x0
  have hev := lemma_3 X hX n hn α hα0 hα1 Q hQ x0 pbar a b h5
  obtain ⟨U, hUsub, hUo, hpU⟩ := mem_nhds_iff.mp hev
  refine ⟨U, hUo, ⟨pbar, hpU⟩, fun p hp => ?_⟩
  obtain ⟨θs, -, -, hQm, hNI, hRR⟩ :=
    poincare_miranda_step X hX n hn α hα0 hα1 Q hQ p x0 a b hab (hUsub hp)
  exact ⟨_, hQm, hNI, _, hRR⟩
