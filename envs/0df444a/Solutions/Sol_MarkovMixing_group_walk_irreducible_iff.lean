-- Prove2me | solution 1 for MarkovMixing.group_walk_irreducible_iff
-- status  : ACCEPTED   (prove)
-- author  : @allychan327
-- created : 2026-08-22T03:29:40.237157+00:00
-- url     : https://prove2.me/submissions/30d8c66d-2ea9-4767-96db-5801091073d5

import Definitions.Def_mm_basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Tactic.Group

open scoped BigOperators
open MarkovMixing

theorem solution {G : Type*} [Group G] [Fintype G]
    [DecidableEq G] (μ : G → ℝ) (hμ : IsDist μ) :
    MarkovMixing.Irreducible (groupWalk μ) ↔ Subgroup.closure {g : G | 0 < μ g} = ⊤ := by
  classical
  set S : Set G := {g : G | 0 < μ g} with hSdef
  have hentry : ∀ a b : G, groupWalk μ a b = μ (b * a⁻¹) := fun a b => rfl
  have hpow_nonneg : ∀ (t : ℕ) (a b : G), 0 ≤ ((groupWalk μ) ^ t) a b := by
    intro t
    induction t with
    | zero => intro a b; by_cases hab : a = b <;> simp [Matrix.one_apply, hab]
    | succ n ih =>
        intro a b
        rw [pow_succ]
        exact Finset.sum_nonneg fun z _ => mul_nonneg (ih a z) (hμ.1 _)
  -- right translation invariance of the transition probabilities
  have hinv : ∀ (t : ℕ) (a b c : G),
      ((groupWalk μ) ^ t) (a * c) (b * c) = ((groupWalk μ) ^ t) a b := by
    intro t
    induction t with
    | zero =>
        intro a b c
        by_cases hab : a = b
        · subst hab; simp [Matrix.one_apply]
        · have : a * c ≠ b * c := fun h => hab (mul_right_cancel h)
          simp [Matrix.one_apply, hab, this]
    | succ n ih =>
        intro a b c
        have hL : ((groupWalk μ) ^ (n + 1)) (a * c) (b * c)
            = ∑ z, ((groupWalk μ) ^ n) (a * c) z * μ (b * c * z⁻¹) := by
          rw [pow_succ]; rfl
        have hR : ((groupWalk μ) ^ (n + 1)) a b
            = ∑ w, ((groupWalk μ) ^ n) a w * μ (b * w⁻¹) := by
          rw [pow_succ]; rfl
        rw [hL, hR]
        have hre := Equiv.sum_comp (Equiv.mulRight c)
          (fun z : G => ((groupWalk μ) ^ n) (a * c) z * μ (b * c * z⁻¹))
        rw [← hre]
        refine Finset.sum_congr rfl fun w _ => ?_
        simp only [Equiv.coe_mulRight]
        rw [ih a w c]
        congr 2
        group
  constructor
  · -- irreducible ⇒ the support generates
    intro hirr
    have hkey : ∀ (t : ℕ) (a b : G),
        0 < ((groupWalk μ) ^ t) a b → b * a⁻¹ ∈ Subgroup.closure S := by
      intro t
      induction t with
      | zero =>
          intro a b hab
          by_cases h : a = b
          · subst h; simpa using Subgroup.one_mem _
          · rw [pow_zero, Matrix.one_apply, if_neg h] at hab; linarith
      | succ n ih =>
          intro a b hab
          rw [pow_succ] at hab
          have hsum : (0:ℝ) < ∑ z, ((groupWalk μ) ^ n) a z * μ (b * z⁻¹) := hab
          obtain ⟨z, -, hz⟩ : ∃ z ∈ (Finset.univ : Finset G),
              0 < ((groupWalk μ) ^ n) a z * μ (b * z⁻¹) := by
            by_contra hcon
            push_neg at hcon
            have := Finset.sum_nonpos fun z hz => hcon z hz
            linarith
          have h1 : 0 < ((groupWalk μ) ^ n) a z :=
            lt_of_le_of_ne (hpow_nonneg n a z) (by
              intro hc
              rw [← hc, zero_mul] at hz
              exact lt_irrefl 0 hz)
          have h2 : 0 < μ (b * z⁻¹) := by nlinarith [hpow_nonneg n a z, hμ.1 (b * z⁻¹)]
          have hmem1 : z * a⁻¹ ∈ Subgroup.closure S := ih a z h1
          have hmem2 : b * z⁻¹ ∈ Subgroup.closure S :=
            Subgroup.subset_closure (Set.mem_setOf.mpr h2)
          have := Subgroup.mul_mem _ hmem2 hmem1
          rwa [show b * z⁻¹ * (z * a⁻¹) = b * a⁻¹ by group] at this
    refine eq_top_iff.mpr fun g _ => ?_
    obtain ⟨t, ht⟩ := hirr 1 g
    have := hkey t 1 g ht
    simpa using this
  · -- the support generates ⇒ irreducible
    intro htop
    set H : Set G := {g : G | ∃ t : ℕ, 0 < ((groupWalk μ) ^ t) 1 g} with hHdef
    have hone : (1 : G) ∈ H := ⟨0, by simp [Matrix.one_apply]⟩
    have hmul : ∀ u v : G, u ∈ H → v ∈ H → u * v ∈ H := by
      rintro u v ⟨s, hs⟩ ⟨t, ht⟩
      refine ⟨t + s, ?_⟩
      have hchain : ((groupWalk μ) ^ t) 1 v * ((groupWalk μ) ^ s) v (u * v)
          ≤ ((groupWalk μ) ^ (t + s)) 1 (u * v) := by
        have hsum : ((groupWalk μ) ^ (t + s)) 1 (u * v)
            = ∑ z, ((groupWalk μ) ^ t) 1 z * ((groupWalk μ) ^ s) z (u * v) := by
          rw [pow_add]; rfl
        rw [hsum]
        exact Finset.single_le_sum
          (f := fun z => ((groupWalk μ) ^ t) 1 z * ((groupWalk μ) ^ s) z (u * v))
          (fun z _ => mul_nonneg (hpow_nonneg t 1 z) (hpow_nonneg s z (u * v)))
          (Finset.mem_univ v)
      have hs' : 0 < ((groupWalk μ) ^ s) v (u * v) := by
        have := hinv s 1 u v
        rw [one_mul] at this
        rw [this]; exact hs
      nlinarith [mul_pos ht hs']
    have hpowmem : ∀ (u : G) (n : ℕ), u ∈ H → u ^ n ∈ H := by
      intro u n hu
      induction n with
      | zero => simpa using hone
      | succ k ih => rw [pow_succ]; exact hmul _ _ ih hu
    have hinvmem : ∀ u : G, u ∈ H → u⁻¹ ∈ H := by
      intro u hu
      have hord : 0 < orderOf u := orderOf_pos u
      have hpow : u ^ (orderOf u - 1) = u⁻¹ := by
        have h1 : u ^ (orderOf u) = 1 := pow_orderOf_eq_one u
        have h2 : u ^ (orderOf u - 1) * u = 1 := by
          rw [← pow_succ]
          rw [show orderOf u - 1 + 1 = orderOf u by omega]
          exact h1
        exact eq_inv_of_mul_eq_one_left h2
      rw [← hpow]
      exact hpowmem u _ hu
    let Hsub : Subgroup G :=
      { carrier := H
        one_mem' := hone
        mul_mem' := fun {a b} ha hb => hmul a b ha hb
        inv_mem' := fun {a} ha => hinvmem a ha }
    have hSle : Subgroup.closure S ≤ Hsub := by
      refine Subgroup.closure_le Hsub |>.mpr ?_
      intro g hg
      exact ⟨1, by rw [pow_one]; simpa [hentry] using (Set.mem_setOf.mp hg)⟩
    intro x y
    have hgy : y * x⁻¹ ∈ H := by
      have : y * x⁻¹ ∈ Subgroup.closure S := by rw [htop]; trivial
      exact hSle this
    obtain ⟨t, ht⟩ := hgy
    refine ⟨t, ?_⟩
    have := hinv t 1 (y * x⁻¹) x
    rw [one_mul, inv_mul_cancel_right] at this
    rw [this]
    exact ht
