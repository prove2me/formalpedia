-- Prove2me | solution 1 for LawlerMoore.FunctionalEq.eq1_value
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T08:52:42.781034+00:00
-- url     : https://prove2.me/submissions/44202d7d-9d86-402d-9c48-0c58d555db2d

import Mathlib
import Definitions.Def_LawlerMoore_FunctionalEq_Problem
import Definitions.Def_LawlerMoore_FunctionalEq_Recursion



namespace LawlerMoore.FunctionalEq

def LGood (v : WithTop ℝ) (S : Set ℝ) : Prop :=
  (v = ⊤ ↔ S = ∅) ∧ ∀ x : ℝ, v = (x : WithTop ℝ) → IsLeast S x

lemma lgood_bot : LGood ⊤ ∅ := ⟨by simp, by intro x hx; exact absurd hx (by simp)⟩

lemma lgood_zero : LGood 0 {0} := by
  refine ⟨?_, ?_⟩
  · simp
  · intro x hx
    have : x = 0 := by exact_mod_cast hx.symm
    subst this
    refine ⟨rfl, ?_⟩
    intro y hy
    simp at hy
    simp [hy]

lemma lgood_min {v w : WithTop ℝ} {S S' : Set ℝ} (hv : LGood v S) (hw : LGood w S') :
    LGood (min v w) (S ∪ S') := by
  induction v using WithTop.recTopCoe with
  | top =>
    have hS : S = ∅ := hv.1.1 rfl
    simp only [min_top_left, hS, Set.empty_union]
    exact hw
  | coe x =>
    have hx := hv.2 x rfl
    induction w using WithTop.recTopCoe with
    | top =>
      have hS : S' = ∅ := hw.1.1 rfl
      simp only [min_top_right, hS, Set.union_empty]
      exact hv
    | coe y =>
      have hy := hw.2 y rfl
      rw [← WithTop.coe_min]
      refine ⟨⟨fun h => absurd h (by simp), fun h => ?_⟩, ?_⟩
      · have : x ∈ S ∪ S' := Or.inl hx.1
        rw [h] at this; exact absurd this (by simp)
      · intro z hz
        have hz' : z = min x y := by exact_mod_cast hz.symm
        subst hz'
        refine ⟨?_, ?_⟩
        · rcases min_choice x y with h | h
          · rw [h]; exact Or.inl hx.1
          · rw [h]; exact Or.inr hy.1
        · intro u hu
          rcases hu with hu | hu
          · exact le_trans (min_le_left _ _) (hx.2 hu)
          · exact le_trans (min_le_right _ _) (hy.2 hu)

lemma lgood_add (c : ℝ) {v : WithTop ℝ} {S : Set ℝ} (hv : LGood v S) :
    LGood ((c : WithTop ℝ) + v) ((fun l => c + l) '' S) := by
  induction v using WithTop.recTopCoe with
  | top =>
    have hS : S = ∅ := hv.1.1 rfl
    simp only [WithTop.add_top, hS, Set.image_empty]
    exact lgood_bot
  | coe x =>
    have hx := hv.2 x rfl
    rw [← WithTop.coe_add]
    refine ⟨⟨fun h => absurd h (by simp), fun h => ?_⟩, ?_⟩
    · have : c + x ∈ (fun l => c + l) '' S := ⟨x, hx.1, rfl⟩
      rw [h] at this; exact absurd this (by simp)
    · intro z hz
      have hz' : z = c + x := by exact_mod_cast hz.symm
      subst hz'
      refine ⟨⟨x, hx.1, rfl⟩, ?_⟩
      rintro _ ⟨l, hl, rfl⟩
      have := hx.2 hl
      show c + x ≤ c + l
      linarith

lemma lossesBy_neg {n : ℕ} (a b : Fin n → ℕ) (α β : Fin n → ℕ → ℝ) (j : ℕ) (t : ℤ) (ht : t < 0) :
    lossesBy a b α β j t = ∅ := by
  ext L
  simp only [lossesBy, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
  rintro ⟨m, c, _, hd, _⟩
  have : (0:ℤ) ≤ ((doneAt c j : ℕ) : ℤ) := by positivity
  omega

lemma lossesBy_zero {n : ℕ} (a b : Fin n → ℕ) (α β : Fin n → ℕ → ℝ) (t : ℤ) (ht : 0 ≤ t) :
    lossesBy a b α β 0 t = {0} := by
  ext L
  simp only [lossesBy, Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨m, c, _, _, rfl⟩
    simp [totalLoss]
  · rintro rfl
    refine ⟨fun _ => true, fun _ => 0, ?_, ?_, ?_⟩
    · intro i hi; omega
    · simp [doneAt]; exact ht
    · simp [totalLoss]

lemma totalLoss_succ {n : ℕ} (α β : Fin n → ℕ → ℝ) (m : Fin n → Bool) (c : Fin n → ℕ) (j : ℕ)
    (hj : j < n) :
    totalLoss α β m c (j+1) = totalLoss α β m c j +
      (if m ⟨j, hj⟩ then α ⟨j, hj⟩ (c ⟨j, hj⟩) else β ⟨j, hj⟩ (c ⟨j, hj⟩)) := by
  unfold totalLoss
  have : Finset.univ.filter (fun i : Fin n => i.val < j + 1) =
      insert ⟨j, hj⟩ (Finset.univ.filter (fun i : Fin n => i.val < j)) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.ext_iff]
    omega
  rw [this, Finset.sum_insert (by simp), add_comm]

lemma doneAt_update {n : ℕ} (c : Fin n → ℕ) (j : ℕ) (hj : j < n) (v : ℕ) (k : ℕ) (hk : k ≤ j) :
    doneAt (Function.update c ⟨j, hj⟩ v) k = doneAt c k := by
  unfold doneAt
  by_cases h : 0 < k ∧ k ≤ n
  · have h2 : (⟨k - 1, by omega⟩ : Fin n) ≠ ⟨j, hj⟩ := by
      intro h'; have := congrArg Fin.val h'; simp at this; omega
    rw [dif_pos h, dif_pos h, Function.update_of_ne h2]
  · rw [dif_neg h, dif_neg h]

lemma doneAt_succ {n : ℕ} (c : Fin n → ℕ) (j : ℕ) (hj : j < n) :
    doneAt c (j+1) = c ⟨j, hj⟩ := by
  unfold doneAt
  rw [dif_pos (by omega)]
  rfl

lemma lossesBy_succ {n : ℕ} (a b : Fin n → ℕ) (α β : Fin n → ℕ → ℝ) (j : ℕ) (hj : j < n) (t : ℤ)
    (ht : 0 ≤ t) :
    lossesBy a b α β (j+1) t = lossesBy a b α β (j+1) (t-1) ∪
      ((fun l => α ⟨j, hj⟩ t.toNat + l) '' lossesBy a b α β j (t - (a ⟨j, hj⟩ : ℤ)) ∪
       (fun l => β ⟨j, hj⟩ t.toNat + l) '' lossesBy a b α β j (t - (b ⟨j, hj⟩ : ℤ))) := by
  ext L
  constructor
  · rintro ⟨m, c, hf, hd, rfl⟩
    rw [doneAt_succ c j hj] at hd
    by_cases hc : ((c ⟨j, hj⟩ : ℕ) : ℤ) ≤ t - 1
    · left
      exact ⟨m, c, hf, by rw [doneAt_succ c j hj]; exact hc, rfl⟩
    · right
      have hceq : ((c ⟨j, hj⟩ : ℕ) : ℤ) = t := by omega
      have hfj : IsFeasible a b m c j := fun i hi => hf i (by omega)
      have hlast := hf ⟨j, hj⟩ (by simp)
      simp only at hlast
      rw [totalLoss_succ α β m c j hj]
      have hct : c ⟨j, hj⟩ = t.toNat := by omega
      cases hm : m ⟨j, hj⟩
      · right
        refine ⟨totalLoss α β m c j, ⟨m, c, hfj, ?_, rfl⟩, ?_⟩
        · unfold procTime at hlast; rw [hm] at hlast; simp at hlast; omega
        · simp [hct]; ring
      · left
        refine ⟨totalLoss α β m c j, ⟨m, c, hfj, ?_, rfl⟩, ?_⟩
        · unfold procTime at hlast; rw [hm] at hlast; simp at hlast; omega
        · simp [hct]; ring
  · intro h
    rcases h with h | h | h
    · rcases h with ⟨m, c, hf, hd, rfl⟩
      exact ⟨m, c, hf, by omega, rfl⟩
    · rcases h with ⟨l, ⟨m, c, hf, hd, rfl⟩, rfl⟩
      refine ⟨Function.update m ⟨j, hj⟩ true, Function.update c ⟨j, hj⟩ t.toNat, ?_, ?_, ?_⟩
      · intro i hi
        by_cases hij : i.val = j
        · have : i = ⟨j, hj⟩ := Fin.ext hij
          subst this
          rw [doneAt_update c j hj _ j le_rfl]
          simp only [Function.update_self, procTime, if_true]
          omega
        · have hne : i ≠ ⟨j, hj⟩ := fun h' => hij (by rw [h']) 
          rw [doneAt_update c j hj _ i.val (by omega)]
          simp only [Function.update_of_ne hne, procTime]
          exact hf i (by omega)
      · rw [doneAt_succ _ j hj]; simp; omega
      · rw [totalLoss_succ α β _ _ j hj]
        simp only [Function.update_self, if_true]
        have : totalLoss α β (Function.update m ⟨j, hj⟩ true) (Function.update c ⟨j, hj⟩ t.toNat) j
            = totalLoss α β m c j := by
          unfold totalLoss
          apply Finset.sum_congr rfl
          intro i hi
          simp only [Finset.mem_filter] at hi
          have hne : i ≠ ⟨j, hj⟩ := fun h' => by have := hi.2; rw [h'] at this; simp at this
          simp only [Function.update_of_ne hne]
        rw [this]; ring
    · rcases h with ⟨l, ⟨m, c, hf, hd, rfl⟩, rfl⟩
      refine ⟨Function.update m ⟨j, hj⟩ false, Function.update c ⟨j, hj⟩ t.toNat, ?_, ?_, ?_⟩
      · intro i hi
        by_cases hij : i.val = j
        · have : i = ⟨j, hj⟩ := Fin.ext hij
          subst this
          rw [doneAt_update c j hj _ j le_rfl]
          simp only [Function.update_self, procTime, Bool.false_eq_true, if_false]
          omega
        · have hne : i ≠ ⟨j, hj⟩ := fun h' => hij (by rw [h']) 
          rw [doneAt_update c j hj _ i.val (by omega)]
          simp only [Function.update_of_ne hne, procTime]
          exact hf i (by omega)
      · rw [doneAt_succ _ j hj]; simp; omega
      · rw [totalLoss_succ α β _ _ j hj]
        simp only [Function.update_self, if_false, Bool.false_eq_true]
        have : totalLoss α β (Function.update m ⟨j, hj⟩ false) (Function.update c ⟨j, hj⟩ t.toNat) j
            = totalLoss α β m c j := by
          unfold totalLoss
          apply Finset.sum_congr rfl
          intro i hi
          simp only [Finset.mem_filter] at hi
          have hne : i ≠ ⟨j, hj⟩ := fun h' => by have := hi.2; rw [h'] at this; simp at this
          simp only [Function.update_of_ne hne]
        rw [this]; ring

lemma lm_good {n : ℕ} (a b : Fin n → ℕ) (α β : Fin n → ℕ → ℝ) :
    ∀ j : ℕ, j ≤ n → ∀ t : ℤ, LGood (f a b α β j t) (lossesBy a b α β j t) := by
  intro j
  induction j with
  | zero =>
    intro _ t
    by_cases ht : t < 0
    · rw [lossesBy_neg a b α β 0 t ht, f]; simp only [ht, dif_pos]; exact lgood_bot
    · rw [lossesBy_zero a b α β t (by omega), f]; simp only [ht, dif_neg, not_false_eq_true]
      exact lgood_zero
  | succ j ih =>
    intro hjle
    have hj : j < n := by omega
    have key : ∀ N : ℕ, ∀ t : ℤ, (t + 1).toNat = N →
        LGood (f a b α β (j+1) t) (lossesBy a b α β (j+1) t) := by
      intro N
      induction N using Nat.strong_induction_on with
      | _ N ihN =>
        intro t hN
        by_cases ht : t < 0
        · rw [lossesBy_neg a b α β (j+1) t ht, f]; simp only [ht, dif_pos]; exact lgood_bot
        · have e : f a b α β (j+1) t =
              min (f a b α β (j+1) (t - 1))
                (min ((α ⟨j, hj⟩ t.toNat : WithTop ℝ) + f a b α β j (t - (a ⟨j, hj⟩ : ℤ)))
                  ((β ⟨j, hj⟩ t.toNat : WithTop ℝ) + f a b α β j (t - (b ⟨j, hj⟩ : ℤ)))) := by
            rw [f]; simp only [ht, dif_neg, not_false_eq_true, hj, dif_pos]
          rw [e, lossesBy_succ a b α β j hj t (by omega)]
          exact lgood_min (ihN (t-1+1).toNat (by omega) (t-1) rfl)
            (lgood_min (lgood_add _ (ih (by omega) _)) (lgood_add _ (ih (by omega) _)))
    exact fun t => key _ t rfl

theorem lm_core {n : ℕ} (a b : Fin n → ℕ) (α β : Fin n → ℕ → ℝ) (j : ℕ) (hj : j ≤ n)
    (t : ℤ) :
    (f a b α β j t = ⊤ ↔ lossesBy a b α β j t = ∅) ∧
      ∀ x : ℝ, f a b α β j t = (x : WithTop ℝ) → IsLeast (lossesBy a b α β j t) x :=
  lm_good a b α β j hj t

end LawlerMoore.FunctionalEq

open LawlerMoore.FunctionalEq


theorem solution {n : ℕ} (a b : Fin n → ℕ) (α β : Fin n → ℕ → ℝ) (j : ℕ) (hj : j ≤ n)
    (t : ℤ) :
    (f a b α β j t = ⊤ ↔ lossesBy a b α β j t = ∅) ∧
      ∀ x : ℝ, f a b α β j t = (x : WithTop ℝ) → IsLeast (lossesBy a b α β j t) x := by
  exact lm_core a b α β j hj t
