-- Prove2me | solution 1 for Intersectionality.Generic.theorem_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-24T12:42:29.821004+00:00
-- url     : https://prove2.me/submissions/1e302fc2-6b9a-45fb-9f84-41e918b79d2b

import Mathlib
import Definitions.Def_Intersectionality_Generic_Setting
import Theorems.Thm_Intersectionality_Generic_lemma_2
import Theorems.Thm_Intersectionality_Generic_beta_one_identity
import Theorems.Thm_Intersectionality_Generic_part_b_construction
import Theorems.Thm_Intersectionality_Generic_lemma_1_b

open Intersectionality.Generic

theorem solution (X : Set ℝ) (hX : X.OrdConnected) [Nonempty ↥X] (n : ℕ) (hn : 2 ≤ n)
    (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1) (Q : Set (↥X → ↥X)) (hQ : IsPolicyFamily Q) :
    ∃ U : Set (DistSpace X n), IsOpen U ∧ Dense U ∧ ∀ p ∈ U,
      (¬ ∃ q : Grp n → (↥X → ↥X), (∀ g, q g ∈ Q) ∧ IsNonintersectional q ∧
          ∃ xs : ↥X, IsRepresentative p.1 α q xs) ∧
      (∃ q : Grp n → (↥X → ↥X), (∀ g, q g ∈ Q) ∧ ¬ IsNonintersectional q ∧
          ∃ xs : ↥X, IsRepresentative p.1 α q xs) := by
  have hL2 := lemma_2 X hX n hn α hα0 hα1 Q hQ
  simp only at hL2
  refine ⟨_, hL2.1, hL2.2, ?_⟩
  intro p hp
  obtain ⟨hne, hpos⟩ := hp
  have partA : ¬ ∃ q : Grp n → (↥X → ↥X), (∀ g, q g ∈ Q) ∧ IsNonintersectional q ∧
      ∃ xs : ↥X, IsRepresentative p.1 α q xs := by
    rintro ⟨q, hqQ, hq, xs, hrep⟩
    obtain ⟨-, h2, h3⟩ :=
      beta_one_identity X hX n α hα0 hα1 Q hQ p hpos q hqQ hq xs hrep
    apply hne
    rw [h3]
    congr 1
    funext x i
    congr 1
    -- q (unitGrp i) = transport Q β_{e_i} β_0
    have hex : ∃ r ∈ Q, r (quantile p.1 α (unitGrp i)) = quantile p.1 α (zeroGrp n) :=
      hQ.rich _ _
    have ht : transport Q (quantile p.1 α (unitGrp i)) (quantile p.1 α (zeroGrp n))
        = Classical.choose hex := by
      unfold transport; rw [dif_pos hex]
    rw [ht]
    obtain ⟨hmem, hmap⟩ := Classical.choose_spec hex
    exact lemma_1_b X hX Q hQ _ _ _ (hqQ _) _ hmem (h2 i) hmap
  refine ⟨partA, ?_⟩
  obtain ⟨xs⟩ := (inferInstance : Nonempty ↥X)
  obtain ⟨q, hqQ, -, hrep⟩ := part_b_construction X hX n α hα0 hα1 Q hQ p xs
  exact ⟨q, hqQ, fun hni => partA ⟨q, hqQ, hni, xs, hrep⟩, xs, hrep⟩
