-- Prove2me | solution 1 for HighDimSteinerSpanners.Proofs.CSP.hammingSphere_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:50:32.698494+00:00
-- url     : https://prove2.me/submissions/a130a7e9-02c0-45d0-8eee-8c318070cdbb

module
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.NormNum
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Definitions.Def_LeanPool_SteinerSpanners_CSP_Expurgation
public import Definitions.Def_LeanPool_SteinerSpanners_CSP_Calibration

set_option autoImplicit true
@[expose] public section
public section
open scoped ENNReal
open HighDimSteinerSpanners
open HighDimSteinerSpanners HighDimSteinerSpanners.Proofs HighDimSteinerSpanners.Proofs.CSP
noncomputable section
namespace HighDimSteinerSpanners.Proofs.CSP
theorem _root_.solution {N q : ℕ} : ∀ (x : Fin N → Fin q) (s : ℕ),
    (Finset.univ.filter (fun y => dHam x y = s)).card = N.choose s * (q - 1) ^ s := by
  classical
  intro x s
  let Fib : Finset (Fin N) → Finset (Fin N → Fin q) := fun S =>
    Fintype.piFinset (fun v : Fin N =>
      if v ∈ S then Finset.univ.erase (x v) else ({x v} : Finset (Fin q)))
  have hFib_mem : ∀ (S : Finset (Fin N)) (y : Fin N → Fin q),
      y ∈ Fib S ↔ disagreeSet x y = S := by
    intro S y
    simp only [Fib, Fintype.mem_piFinset, Finset.ext_iff, disagreeSet, Finset.mem_filter,
      Finset.mem_univ, true_and]
    constructor
    · intro hy v
      specialize hy v
      by_cases hv : v ∈ S
      · simp only [if_pos hv, Finset.mem_erase, Finset.mem_univ, and_true] at hy
        exact ⟨fun _ => hv, fun _ => Ne.symm hy⟩
      · simp only [if_neg hv, Finset.mem_singleton] at hy
        exact ⟨fun hne => absurd hy.symm hne, fun h => absurd h hv⟩
    · intro hS v
      by_cases hv : v ∈ S
      · simp only [if_pos hv, Finset.mem_erase, Finset.mem_univ, and_true]
        exact Ne.symm ((hS v).mpr hv)
      · simp only [if_neg hv, Finset.mem_singleton]
        by_contra hne
        exact hv ((hS v).mp (Ne.symm hne))
  have h_bi : Finset.univ.filter (fun y : Fin N → Fin q => dHam x y = s) =
      ((Finset.univ : Finset (Fin N)).powersetCard s).biUnion Fib := by
    ext y
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion,
      Finset.mem_powersetCard, hFib_mem, dHam]
    constructor
    · intro hs
      exact ⟨disagreeSet x y, ⟨Finset.subset_univ _, hs⟩, rfl⟩
    · rintro ⟨S, ⟨_, hScard⟩, rfl⟩
      exact hScard
  have h_disj : (((Finset.univ : Finset (Fin N)).powersetCard s : Finset (Finset (Fin N))) :
      Set (Finset (Fin N))).PairwiseDisjoint Fib := by
    intro S₁ _ S₂ _ hne
    rw [Function.onFun, Finset.disjoint_left]
    intro y hy₁ hy₂
    rw [hFib_mem] at hy₁ hy₂
    exact hne (hy₁.symm.trans hy₂)
  rw [h_bi, Finset.card_biUnion h_disj]
  have hFib_card : ∀ S ∈ (Finset.univ : Finset (Fin N)).powersetCard s,
      (Fib S).card = (q - 1) ^ s := by
    intro S hS
    rw [Finset.mem_powersetCard] at hS
    dsimp [Fib]
    rw [Fintype.card_piFinset]
    have hterm : ∀ v : Fin N,
        (if v ∈ S then Finset.univ.erase (x v) else ({x v} : Finset (Fin q))).card =
          if v ∈ S then q - 1 else 1 := by
      intro v
      split_ifs
      · rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
      · exact Finset.card_singleton _
    simp_rw [hterm]
    rw [Finset.prod_ite_mem, Finset.univ_inter, Finset.prod_const, hS.2]
  rw [Finset.sum_congr rfl hFib_card, Finset.sum_const, smul_eq_mul,
    Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
end HighDimSteinerSpanners.Proofs.CSP
