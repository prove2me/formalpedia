-- Prove2me | solution 1 for OAI.PiExponent.LiteralAnalytic.allocationSum_eq_weakCompositionFiber_card
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T17:13:48.482862+00:00
-- url     : https://prove2.me/submissions/29a2568f-f802-4206-9aa8-e6b0a1ede475

import Mathlib.Tactic
import Mathlib.Algebra.Order.Antidiag.FinsuppEquiv
import Definitions.Def_allocationSum
import Definitions.Def_weakCompositionFiber
set_option autoImplicit false
open scoped BigOperators

theorem VV_L1 (k m e : ℕ) (hm : m ≤ k) :
    (Finset.univ.filter (fun g : Fin e → Fin (k + 1) => ∑ j, (g j : ℕ) = m)).card =
      (if e = 0 then (if m = 0 then 1 else 0) else Nat.choose (m + e - 1) m) := by
  by_cases he : e = 0
  · subst he
    simp only [if_true]
    by_cases h0 : m = 0
    · subst h0; simp
    · simp [h0, Ne.symm h0]
  · rw [if_neg he]
    have h := Finset.card_finsuppAntidiag_nat_eq_multichoose (s := (Finset.univ : Finset (Fin e))) m
    rw [Nat.multichoose_eq] at h
    simp only [Finset.card_univ, Fintype.card_fin] at h
    rw [show m + e - 1 = e + m - 1 by omega, ← h]
    have hco : ∀ g : Fin e → Fin (k+1), ⇑(Finsupp.equivFunOnFinite.symm (fun j => (g j : ℕ))) = fun j => (g j : ℕ) :=
      fun g => Finsupp.coe_equivFunOnFinite_symm _
    apply Finset.card_nbij'
      (fun g : Fin e → Fin (k+1) => (Finsupp.equivFunOnFinite.symm (fun j => (g j : ℕ)) : Fin e →₀ ℕ))
      (fun f : Fin e →₀ ℕ => (fun j => (⟨min (f j) k, by omega⟩ : Fin (k+1)) : Fin e → Fin (k+1)))
    · intro g hg
      simp only [Finset.coe_filter, Finset.mem_univ, true_and] at hg
      simp only [Finset.mem_coe, Finset.mem_finsuppAntidiag]
      refine ⟨?_, Finset.subset_univ _⟩
      rw [hco]
      exact hg
    · intro f hf
      simp only [Finset.mem_coe, Finset.mem_finsuppAntidiag] at hf
      simp only [Finset.coe_filter, Finset.mem_univ, true_and]
      have hle : ∀ j, f j ≤ m := by
        intro j
        rw [← hf.1]
        exact Finset.single_le_sum (f := fun j => f j) (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
      have : ∀ j, min (f j) k = f j := fun j => min_eq_left (le_trans (hle j) hm)
      simp only [this]
      exact hf.1
    · intro g _
      ext j
      show min ((Finsupp.equivFunOnFinite.symm (fun j => (g j : ℕ))) j) k = (g j : ℕ)
      rw [show (Finsupp.equivFunOnFinite.symm (fun j => (g j : ℕ))) j = (g j : ℕ) from congrFun (hco g) j]
      exact min_eq_left (Nat.le_of_lt_succ (g j).2)
    · intro f hf
      simp only [Finset.mem_coe, Finset.mem_finsuppAntidiag] at hf
      ext j
      have hle : f j ≤ m := by
        rw [← hf.1]
        exact Finset.single_le_sum (f := fun j => f j) (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
      show ((Finsupp.equivFunOnFinite.symm (fun j => ((⟨min (f j) k, by omega⟩ : Fin (k+1)) : ℕ))) j) = f j
      rw [show (Finsupp.equivFunOnFinite.symm (fun j => ((⟨min (f j) k, by omega⟩ : Fin (k+1)) : ℕ))) j = min (f j) k from rfl]
      exact min_eq_left (le_trans hle hm)

theorem solution
    {σ : Type*} [Fintype σ] [DecidableEq σ]
    (e : σ → ℕ) (k : ℕ) :
    OAI.PiExponent.LiteralAnalytic.allocationSum e k =
      Fintype.card
        (OAI.PiExponent.LiteralAnalytic.weakCompositionFiber (Σ i, Fin (e i)) k) := by
  classical
  unfold OAI.PiExponent.LiteralAnalytic.allocationSum OAI.PiExponent.LiteralAnalytic.weakCompositionFiber
  -- step 1: curry
  have hc : Fintype.card { f : (Σ i, Fin (e i)) → Fin (k + 1) // Finset.univ.sum (fun a => (f a).val) = k }
      = Fintype.card { g : (∀ i, Fin (e i) → Fin (k + 1)) // ∑ i, ∑ j, (g i j).val = k } := by
    apply Fintype.card_congr
    refine Equiv.subtypeEquiv (Equiv.piCurry (fun i (_ : Fin (e i)) => Fin (k + 1))) ?_
    intro f
    simp only [Equiv.piCurry_apply, Fintype.sum_sigma]
    exact Iff.rfl
  rw [hc, Fintype.card_subtype]
  -- fibre over the vector of block sums
  set S : Finset (∀ i, Fin (e i) → Fin (k + 1)) :=
    Finset.univ.filter (fun g => ∑ i, ∑ j, (g i j).val = k) with hS
  set t : Finset (σ → Fin (k + 1)) := Finset.univ.filter (fun n => ∑ i, (n i).val = k) with ht
  let F : (∀ i, Fin (e i) → Fin (k + 1)) → (σ → Fin (k + 1)) :=
    fun g i => ⟨min (∑ j, (g i j).val) k, Nat.lt_succ_of_le (min_le_right _ _)⟩
  have hle : ∀ g ∈ S, ∀ i, ∑ j, (g i j).val ≤ k := by
    intro g hg i
    rw [hS, Finset.mem_filter] at hg
    calc ∑ j, (g i j).val ≤ ∑ i, ∑ j, (g i j).val :=
          Finset.single_le_sum (f := fun i => ∑ j, (g i j).val) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
      _ = k := hg.2
  have hFt : ∀ g ∈ S, F g ∈ t := by
    intro g hg
    rw [ht, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    have hg' := hg
    rw [hS, Finset.mem_filter] at hg'
    calc ∑ i, (F g i).val = ∑ i, ∑ j, (g i j).val := by
          apply Finset.sum_congr rfl
          intro i _
          exact min_eq_left (hle g hg i)
      _ = k := hg'.2
  rw [Finset.card_eq_sum_card_fiberwise hFt]
  have hrhs : (∑ n : σ → Fin (k + 1),
      (if ∑ i, (n i : ℕ) = k then
        ∏ i, (if e i = 0 then (if (n i : ℕ) = 0 then 1 else 0)
          else Nat.choose ((n i : ℕ) + e i - 1) (n i : ℕ)) else 0)) =
      ∑ n ∈ t, ∏ i, (if e i = 0 then (if (n i : ℕ) = 0 then 1 else 0)
          else Nat.choose ((n i : ℕ) + e i - 1) (n i : ℕ)) := by
    rw [ht, Finset.sum_filter]
  rw [hrhs]
  apply Finset.sum_congr rfl
  intro n hn
  rw [ht, Finset.mem_filter] at hn
  have hfib : S.filter (fun g => F g = n) =
      Fintype.piFinset (fun i => Finset.univ.filter (fun gi : Fin (e i) → Fin (k + 1) => ∑ j, (gi j : ℕ) = (n i : ℕ))) := by
    ext g
    rw [Finset.mem_filter, Fintype.mem_piFinset]
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hg, hF⟩
      intro i
      have h1 := congrArg (fun m : Fin (k + 1) => m.val) (congrFun hF i)
      simp only [F] at h1
      rw [min_eq_left (hle g hg i)] at h1
      exact h1
    · intro h
      have htot : ∑ i, ∑ j, (g i j).val = k := by
        calc ∑ i, ∑ j, (g i j).val = ∑ i, (n i).val := Finset.sum_congr rfl (fun i _ => h i)
          _ = k := hn.2
      refine ⟨?_, ?_⟩
      · rw [hS, Finset.mem_filter]; exact ⟨Finset.mem_univ _, htot⟩
      · funext i
        apply Fin.ext
        simp only [F]
        rw [h i]
        exact min_eq_left (Nat.le_of_lt_succ (n i).2)
  rw [hfib, Fintype.card_piFinset]
  apply Finset.prod_congr rfl
  intro i _
  exact (VV_L1 k (n i : ℕ) (e i) (Nat.le_of_lt_succ (n i).2)).symm

