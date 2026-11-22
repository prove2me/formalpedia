-- Prove2me | solution 1 for LovaszECCKernel.claim_12
-- status  : ACCEPTED   (prove)
-- author  : @I am wealthy
-- created : 2026-11-21T16:51:14.783881+00:00
-- url     : https://prove2.me/submissions/03ae30d2-e499-44ad-964b-b8ef53ce792c

import Definitions.Def_LovaszECCKernel_Lb
open LovaszECCKernel

theorem solution {V : Type*} [Fintype V] (G : SimpleGraph V) (k : ℕ)
    (h₂ : ¬ ((edgeCount G : ℤ) ≤ (Lb G : ℤ) - k))
    (h₅ : ¬ (edgeCount G ≤ k ∧ Fintype.card V ≤ k)) :
    (Fintype.card V : ℝ) * ((Fintype.card V : ℝ) - 3) / 6 ≤ edgeCount G := by
  classical
  let n := Fintype.card V
  let m := edgeCount G
  let b := (nonEdges G).card
  have hcount : m + b = n.choose 2 := by
    change G.edgeFinset.card + Gᶜ.edgeFinset.card = _
    rw [← Finset.card_union_of_disjoint ((SimpleGraph.disjoint_edgeFinset).mpr disjoint_compl_right),
      ← SimpleGraph.edgeFinset_sup,
      (SimpleGraph.edgeFinset_inj.mpr (sup_compl_eq_top : G ⊔ Gᶜ = ⊤)),
      SimpleGraph.card_edgeFinset_top_eq_card_choose_two]
  have hcountR : (m : ℝ) + b = (n : ℝ) * (n-1) / 2 := by
    rw [← Nat.cast_add, hcount, Nat.cast_choose_two]
  have hbound : b < m + k := by
    change ¬ ((m : ℤ) ≤ ((b + sMax b : ℕ) : ℤ) - k) at h₂
    omega
  change ¬ (m ≤ k ∧ n ≤ k) at h₅
  change (n : ℝ) * (n-3)/6 ≤ m
  rcases lt_or_ge k m with hk | hk
  · have hsmall : (b : ℝ) < m + (m : ℝ) := by exact_mod_cast (show b < m+m by omega)
    nlinarith [Nat.cast_nonneg (α := ℝ) n]
  · have hsmall : (b : ℝ) < m + (n : ℝ) := by exact_mod_cast (show b < m+n by omega)
    nlinarith [Nat.cast_nonneg (α := ℝ) m]
#print axioms solution
