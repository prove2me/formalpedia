-- Prove2me | solution 1 for NonmonotoneSubmod.Nonadaptive.expect_union_upper
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-28T05:34:26.596364+00:00
-- url     : https://prove2.me/submissions/47e815fc-7c87-4d32-bb94-daaa04cbdad3

import Mathlib
import Definitions.Def_NonmonotoneSubmod_Shared_Submodular
import Definitions.Def_NonmonotoneSubmod_Shared_OPT
import Definitions.Def_NonmonotoneSubmod_Shared_F
import Definitions.Def_NonmonotoneSubmod_Nonadaptive_omega

open NonmonotoneSubmod.Shared

/-- With `p = 1/2` every weight equals `(1/2)^n`, so `F` is a normalised plain sum. -/
private theorem F_half {X : Type} [Fintype X] [DecidableEq X] (g : Finset X → ℝ) :
    F g (fun _ => (1:ℝ) / 2) = (1/2 : ℝ) ^ (Fintype.card X) * ∑ S : Finset X, g S := by
  unfold F
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun S _ => ?_
  have hpt : ∀ i : X, (if i ∈ S then (1:ℝ) / 2 else 1 - 1 / 2) = 1 / 2 := by
    intro i
    by_cases h : i ∈ S
    · rw [if_pos h]
    · rw [if_neg h]; norm_num
  rw [Finset.prod_congr rfl fun i (_ : i ∈ Finset.univ) => hpt i]
  rw [Finset.prod_const, Finset.card_univ]
  ring

/-- Toggling the element `x` is an involution of the power set, so it preserves sums. -/
private theorem toggle_sum {X : Type} [Fintype X] [DecidableEq X] (x : X) (k : Finset X → ℝ) :
    ∑ S : Finset X, k (if x ∈ S then S.erase x else insert x S) = ∑ S : Finset X, k S := by
  classical
  have hinv : Function.Involutive
      (fun S : Finset X => if x ∈ S then S.erase x else insert x S) := by
    intro S
    by_cases h : x ∈ S
    · simp only [h, if_true]
      rw [if_neg (Finset.notMem_erase x S), Finset.insert_erase h]
    · simp only [h, if_false]
      rw [if_pos (Finset.mem_insert_self x S), Finset.erase_insert h]
  exact Fintype.sum_equiv hinv.toPerm _ _ (fun S => rfl)

/-- The two ways of writing the marginal of `x` have the same uniform average. -/
private theorem marg_sum_eq {X : Type} [Fintype X] [DecidableEq X] (f : Finset X → ℝ) (x : X) :
    ∑ S : Finset X, (f S - f (S.erase x)) = ∑ S : Finset X, (f (insert x S) - f S) := by
  classical
  have h := toggle_sum x (fun S => f S - f (S.erase x))
  rw [← h]
  refine Finset.sum_congr rfl fun S _ => ?_
  by_cases hS : x ∈ S
  · rw [if_pos hS, Finset.erase_idem, Finset.insert_eq_self.mpr hS]
    ring
  · rw [if_neg hS, Finset.erase_insert hS]

/-- `E[f(R ∪ {x}) - f(R)] = ω(x)/2` for a uniformly random `R`. -/
private theorem omega_half {X : Type} [Fintype X] [DecidableEq X] (f : Finset X → ℝ) (x : X) :
    (1/2 : ℝ) ^ (Fintype.card X) * ∑ S : Finset X, (f (insert x S) - f S)
      = NonmonotoneSubmod.Nonadaptive.omega f x / 2 := by
  have key := marg_sum_eq f x
  have hsplit : ∑ S : Finset X, (f (insert x S) - f (S.erase x))
      = 2 * ∑ S : Finset X, (f (insert x S) - f S) := by
    have hd : ∑ S : Finset X, (f (insert x S) - f (S.erase x))
        = ∑ S : Finset X, (f (insert x S) - f S) + ∑ S : Finset X, (f S - f (S.erase x)) := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun S _ => by ring
    rw [hd, key]; ring
  rw [NonmonotoneSubmod.Nonadaptive.omega, F_half, hsplit]
  ring

/-- `E[f(R \ {x}) - f(R)] = -ω(x)/2`. -/
private theorem omega_half_neg {X : Type} [Fintype X] [DecidableEq X] (f : Finset X → ℝ)
    (x : X) :
    (1/2 : ℝ) ^ (Fintype.card X) * ∑ S : Finset X, (f (S.erase x) - f S)
      = -(NonmonotoneSubmod.Nonadaptive.omega f x / 2) := by
  have h := omega_half f x
  have key := marg_sum_eq f x
  have hz : ∑ S : Finset X, (f (S.erase x) - f S) + ∑ S : Finset X, (f S - f (S.erase x)) = 0 := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_eq_zero fun S _ => by ring
  have hneg : ∑ S : Finset X, (f (S.erase x) - f S)
      = -∑ S : Finset X, (f (insert x S) - f S) := by
    rw [← key]; linarith
  rw [hneg, mul_neg, h]

/-- Submodular marginals are subadditive: adding `D` gains at most the single-element gains. -/
private theorem marg_union {X : Type} [Fintype X] [DecidableEq X]
    {f : Finset X → ℝ} (hf : Submodular f) :
    ∀ D : Finset X, ∀ S : Finset X,
      f (S ∪ D) ≤ f S + ∑ x ∈ D, (f (insert x S) - f S) := by
  intro D
  induction D using Finset.induction_on with
  | empty => intro S; simp
  | insert a D' ha ih =>
    intro S
    rw [Finset.sum_insert ha]
    by_cases haS : a ∈ S
    · have h1 : S ∪ insert a D' = S ∪ D' := by
        ext b
        simp only [Finset.mem_union, Finset.mem_insert]
        constructor
        · rintro (h | h | h)
          · exact Or.inl h
          · exact Or.inl (h ▸ haS)
          · exact Or.inr h
        · rintro (h | h)
          · exact Or.inl h
          · exact Or.inr (Or.inr h)
      have h2 : insert a S = S := Finset.insert_eq_self.mpr haS
      rw [h1, h2]
      have := ih S
      linarith
    · have hun : S ∪ insert a D' = insert a (S ∪ D') := by
        ext b; simp only [Finset.mem_union, Finset.mem_insert]; tauto
      have hsub := hf (S ∪ D') (insert a S)
      have e1 : (S ∪ D') ∪ insert a S = insert a (S ∪ D') := by
        ext b; simp only [Finset.mem_union, Finset.mem_insert]; tauto
      have e2 : (S ∪ D') ∩ insert a S = S := by
        ext b
        simp only [Finset.mem_inter, Finset.mem_union, Finset.mem_insert]
        constructor
        · intro h
          rcases h.2 with hb | hb
          · subst hb
            rcases h.1 with h' | h'
            · exact absurd h' haS
            · exact absurd h' ha
          · exact hb
        · intro h; exact ⟨Or.inl h, Or.inr h⟩
      rw [e1, e2] at hsub
      rw [hun]
      have := ih S
      linarith

/-- Dual form: deleting `D` loses at most the single-element losses. -/
private theorem marg_inter {X : Type} [Fintype X] [DecidableEq X]
    {f : Finset X → ℝ} (hf : Submodular f) :
    ∀ D : Finset X, ∀ S : Finset X,
      f (S \ D) ≤ f S + ∑ x ∈ D, (f (S.erase x) - f S) := by
  intro D
  induction D using Finset.induction_on with
  | empty => intro S; simp
  | insert a D' ha ih =>
    intro S
    rw [Finset.sum_insert ha]
    have hset : S \ insert a D' = (S \ D').erase a := by
      ext b
      simp only [Finset.mem_sdiff, Finset.mem_erase, Finset.mem_insert]
      tauto
    rw [hset]
    by_cases haU : a ∈ S \ D'
    · have hsub := hf (S \ D') (S.erase a)
      have e1 : (S \ D') ∪ S.erase a = S := by
        ext b
        simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_erase]
        constructor
        · rintro (⟨h, _⟩ | ⟨_, h⟩)
          · exact h
          · exact h
        · intro h
          by_cases hb : b = a
          · exact Or.inl ⟨h, by rw [hb]; exact (Finset.mem_sdiff.mp haU).2⟩
          · exact Or.inr ⟨hb, h⟩
      have e2 : (S \ D') ∩ S.erase a = (S \ D').erase a := by
        ext b
        simp only [Finset.mem_inter, Finset.mem_sdiff, Finset.mem_erase]
        tauto
      rw [e1, e2] at hsub
      have := ih S
      linarith
    · have haS : a ∉ S := by
        intro hmem
        exact haU (Finset.mem_sdiff.mpr ⟨hmem, ha⟩)
      rw [Finset.erase_eq_of_notMem haU, Finset.erase_eq_of_notMem haS]
      have := ih S
      linarith

/-- `card D * OPT/(2n²) ≤ OPT/(2n)` whenever `card D ≤ n` and `OPT ≥ 0`. -/
private theorem tail_bound {X : Type} [Fintype X] (f : Finset X → ℝ) (D : Finset X)
    (hOPT : 0 ≤ OPT f) (hn : (0:ℝ) < (Fintype.card X : ℝ))
    (hcard : (D.card : ℝ) ≤ (Fintype.card X : ℝ)) :
    (D.card : ℝ) * (OPT f / (2 * (Fintype.card X : ℝ) ^ 2))
      ≤ OPT f / (2 * (Fintype.card X : ℝ)) := by
  have hne : (Fintype.card X : ℝ) ≠ 0 := ne_of_gt hn
  have hnn : (0:ℝ) ≤ OPT f * ((Fintype.card X : ℝ) - (D.card : ℝ)) /
      (2 * (Fintype.card X : ℝ) ^ 2) :=
    div_nonneg (mul_nonneg hOPT (by linarith)) (by positivity)
  have key : OPT f / (2 * (Fintype.card X : ℝ))
      - (D.card : ℝ) * (OPT f / (2 * (Fintype.card X : ℝ) ^ 2))
      = OPT f * ((Fintype.card X : ℝ) - (D.card : ℝ)) / (2 * (Fintype.card X : ℝ) ^ 2) := by
    field_simp
  linarith

theorem solution {X : Type} [Fintype X] [DecidableEq X] [Nonempty X]
    (f : Finset X → ℝ) (hf0 : ∀ S, 0 ≤ f S) (hf : NonmonotoneSubmod.Shared.Submodular f)
    (B C : Finset X)
    (hB : ∀ x ∈ B, NonmonotoneSubmod.Nonadaptive.omega f x
      ≤ NonmonotoneSubmod.Shared.OPT f / (Fintype.card X : ℝ) ^ 2) :
    NonmonotoneSubmod.Shared.F (fun S => f (S ∪ (B ∩ C))) (fun _ => 1 / 2) ≤
      NonmonotoneSubmod.Shared.F f (fun _ => 1 / 2)
        + NonmonotoneSubmod.Shared.OPT f / (2 * (Fintype.card X : ℝ)) := by
  classical
  have hnpos : 0 < Fintype.card X := Fintype.card_pos
  have hnR : (0:ℝ) < (Fintype.card X : ℝ) := by exact_mod_cast hnpos
  have hOPT : 0 ≤ OPT f := le_trans (hf0 ∅) (Finset.le_sup' f (Finset.mem_univ ∅))
  have hpow : (0:ℝ) < (1/2 : ℝ) ^ (Fintype.card X) := by positivity
  have hsum : ∑ S : Finset X, f (S ∪ (B ∩ C))
      ≤ ∑ S : Finset X, f S
        + ∑ x ∈ B ∩ C, ∑ S : Finset X, (f (insert x S) - f S) := by
    have h1 : ∑ S : Finset X, f (S ∪ (B ∩ C))
        ≤ ∑ S : Finset X, (f S + ∑ x ∈ B ∩ C, (f (insert x S) - f S)) :=
      Finset.sum_le_sum fun S _ => marg_union hf (B ∩ C) S
    rw [Finset.sum_add_distrib, Finset.sum_comm] at h1
    exact h1
  rw [F_half, F_half]
  have hin : ∑ x ∈ B ∩ C, (1/2 : ℝ) ^ (Fintype.card X) * ∑ S : Finset X, (f (insert x S) - f S)
      = ∑ x ∈ B ∩ C, NonmonotoneSubmod.Nonadaptive.omega f x / 2 :=
    Finset.sum_congr rfl fun x _ => omega_half f x
  have hmul : (1/2 : ℝ) ^ (Fintype.card X) * ∑ S : Finset X, f (S ∪ (B ∩ C))
      ≤ (1/2 : ℝ) ^ (Fintype.card X) * ∑ S : Finset X, f S
        + ∑ x ∈ B ∩ C, NonmonotoneSubmod.Nonadaptive.omega f x / 2 := by
    have h2 := mul_le_mul_of_nonneg_left hsum hpow.le
    have h3 : (1/2 : ℝ) ^ (Fintype.card X) * (∑ S : Finset X, f S
        + ∑ x ∈ B ∩ C, ∑ S : Finset X, (f (insert x S) - f S)) = (1/2 : ℝ) ^ (Fintype.card X) * ∑ S : Finset X, f S
          + ∑ x ∈ B ∩ C, NonmonotoneSubmod.Nonadaptive.omega f x / 2 := by
      rw [mul_add]
      congr 1
      rw [Finset.mul_sum]
      exact hin
    rw [h3] at h2
    exact h2
  have hb : ∀ x ∈ B ∩ C, NonmonotoneSubmod.Nonadaptive.omega f x / 2
      ≤ OPT f / (2 * (Fintype.card X : ℝ) ^ 2) := by
    intro x hx
    have h := hB x (Finset.mem_of_mem_inter_left hx)
    have h2 : OPT f / (Fintype.card X : ℝ) ^ 2 / 2 = OPT f / (2 * (Fintype.card X : ℝ) ^ 2) := by
      rw [div_div]; ring_nf
    calc NonmonotoneSubmod.Nonadaptive.omega f x / 2
        ≤ OPT f / (Fintype.card X : ℝ) ^ 2 / 2 := by linarith
      _ = OPT f / (2 * (Fintype.card X : ℝ) ^ 2) := h2
  have h1 := Finset.sum_le_sum hb
  rw [Finset.sum_const, nsmul_eq_mul] at h1
  have hcard : (((B ∩ C).card : ℕ) : ℝ) ≤ (Fintype.card X : ℝ) := by
    exact_mod_cast Finset.card_le_univ (B ∩ C)
  have h2 := tail_bound f (B ∩ C) hOPT hnR hcard
  linarith
