-- Prove2me | solution 1 for MarkovMixing.green_resistance
-- status  : ACCEPTED   (prove)
-- author  : @MKPynnic
-- created : 2026-08-22T16:23:50.59531+00:00
-- url     : https://prove2.me/submissions/8a343328-f402-4120-b688-7129d9ca605f

import Theorems.Thm_MarkovMixing_summable_hitting_tails
import Theorems.Thm_MarkovMixing_harmonic_extension
import Definitions.Def_mm_network
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.Positivity
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

open scoped BigOperators
open MarkovMixing

set_option maxRecDepth 8000

/-- The chain `Q` killed on entering the set `S`. -/
private def killedSet {W : Type*} [Fintype W] [DecidableEq W]
    (Q : Matrix W W ℝ) (S : Finset W) : Matrix W W ℝ :=
  fun a b => if b ∈ S then 0 else Q a b

/-- Splitting a trajectory of length `n+1` into its first `n` steps and its final state. -/
private def snocEquivV (V : Type*) (n : ℕ) : ((Fin (n + 1) → V) × V) ≃ (Fin (n + 2) → V) where
  toFun p := Fin.snoc p.1 p.2
  invFun ω := (fun i => ω i.castSucc, ω (Fin.last (n + 1)))
  left_inv := by rintro ⟨q, v⟩; ext <;> simp
  right_inv := by intro ω; exact Fin.snoc_init_self ω

@[simp] private lemma snocEquivV_castSucc {V : Type*} (n : ℕ)
    (p : (Fin (n + 1) → V) × V) (i : Fin (n + 1)) :
    snocEquivV V n p i.castSucc = p.1 i :=
  Fin.snoc_castSucc (α := fun _ => V) p.2 p.1 i

@[simp] private lemma snocEquivV_last {V : Type*} (n : ℕ) (p : (Fin (n + 1) → V) × V) :
    snocEquivV V n p (Fin.last (n + 1)) = p.2 :=
  Fin.snoc_last (α := fun _ => V) p.2 p.1

/-- The set-avoidance path sum with a prescribed endpoint is an entry of a power of
the killed chain. -/
private lemma avoidSetAt_eq_killed_pow {W : Type*} [Fintype W] [DecidableEq W]
    (Q : Matrix W W ℝ) (S : Finset W) :
    ∀ (t : ℕ) (p₀ y : W), p₀ ∉ S →
      avoidSetAtProb Q p₀ S y t = ((killedSet Q S) ^ t) p₀ y := by
  classical
  set K := killedSet Q S with hKdef
  have hKval : ∀ a b : W, K a b = if b ∈ S then 0 else Q a b := fun a b => rfl
  intro t
  induction t with
  | zero =>
      intro p₀ y hp₀
      have hL : avoidSetAtProb Q p₀ S y 0
          = ∑ ω : Fin 1 → W, (if ω 0 = p₀ ∧ ω 0 = y then (1:ℝ) else 0) := by
        refine Finset.sum_congr rfl fun ω _ => ?_
        have hcond : (ω 0 = p₀ ∧ (∀ i : Fin 1, ω i ∉ S) ∧ ω (Fin.last 0) = y)
            ↔ (ω 0 = p₀ ∧ ω 0 = y) := by
          constructor
          · rintro ⟨h1, -, h3⟩; exact ⟨h1, h3⟩
          · rintro ⟨h1, h2⟩
            refine ⟨h1, fun i => ?_, h2⟩
            rw [Subsingleton.elim i 0, h1]
            exact hp₀
        by_cases h : ω 0 = p₀ ∧ ω 0 = y
        · rw [if_pos (hcond.mpr h), if_pos h]
          simp [pathWeight]
        · rw [if_neg (fun hc => h (hcond.mp hc)), if_neg h]
      rw [hL, Fintype.sum_equiv (Equiv.funUnique (Fin 1) W)
        (fun ω : Fin 1 → W => if ω 0 = p₀ ∧ ω 0 = y then (1:ℝ) else 0)
        (fun v : W => if v = p₀ ∧ v = y then (1:ℝ) else 0) (fun ω => rfl)]
      rw [pow_zero, Matrix.one_apply]
      by_cases hpy : p₀ = y
      · subst hpy
        rw [if_pos rfl, Finset.sum_eq_single p₀]
        · rw [if_pos ⟨rfl, rfl⟩]
        · intro b _ hb; rw [if_neg (fun hc => hb hc.1)]
        · intro hc; exact absurd (Finset.mem_univ p₀) hc
      · rw [if_neg hpy]
        refine Finset.sum_eq_zero fun v _ => ?_
        rw [if_neg]
        rintro ⟨h1, h2⟩
        exact hpy (h1.symm.trans h2)
  | succ n ih =>
      intro p₀ y hp₀
      have hunfold : avoidSetAtProb Q p₀ S y (n + 1)
          = ∑ ω : Fin (n + 2) → W,
              (if ω 0 = p₀ ∧ (∀ i : Fin (n + 2), ω i ∉ S) ∧
                  ω (Fin.last (n + 1)) = y then pathWeight Q ω else 0) := rfl
      rw [hunfold, ← Equiv.sum_comp (snocEquivV W n)
        (fun ω : Fin (n + 2) → W =>
          if ω 0 = p₀ ∧ (∀ i : Fin (n + 2), ω i ∉ S) ∧
              ω (Fin.last (n + 1)) = y then pathWeight Q ω else 0)]
      have hstep : ∀ p : (Fin (n + 1) → W) × W,
          (if (snocEquivV W n p) 0 = p₀ ∧
              (∀ i : Fin (n + 2), (snocEquivV W n p) i ∉ S) ∧
              (snocEquivV W n p) (Fin.last (n + 1)) = y then
            pathWeight Q (snocEquivV W n p) else 0)
          = (if (p.1 0 = p₀ ∧ ∀ i : Fin (n + 1), p.1 i ∉ S) ∧ (p.2 ∉ S ∧ p.2 = y) then
              pathWeight Q p.1 * Q (p.1 (Fin.last n)) p.2 else 0) := by
        intro p
        have hrestrict : ∀ i : Fin (n + 1), (snocEquivV W n p) i.castSucc = p.1 i :=
          fun i => snocEquivV_castSucc n p i
        have hlast : (snocEquivV W n p) (Fin.last (n + 1)) = p.2 := snocEquivV_last n p
        have hzero : (snocEquivV W n p) 0 = p.1 0 := by
          have h := hrestrict 0
          rwa [Fin.castSucc_zero] at h
        have hcond : ((snocEquivV W n p) 0 = p₀ ∧
              (∀ i : Fin (n + 2), (snocEquivV W n p) i ∉ S) ∧
              (snocEquivV W n p) (Fin.last (n + 1)) = y)
            ↔ ((p.1 0 = p₀ ∧ ∀ i : Fin (n + 1), p.1 i ∉ S) ∧ (p.2 ∉ S ∧ p.2 = y)) := by
          constructor
          · rintro ⟨h0, hne, hy⟩
            refine ⟨⟨hzero ▸ h0, fun i => ?_⟩, ?_, hlast ▸ hy⟩
            · rw [← hrestrict i]; exact hne i.castSucc
            · rw [← hlast]; exact hne _
          · rintro ⟨⟨h0, hne⟩, hlz, hy⟩
            refine ⟨hzero ▸ h0, fun i => ?_, hlast ▸ hy⟩
            induction i using Fin.lastCases with
            | last => rw [hlast]; exact hlz
            | cast j => rw [hrestrict j]; exact hne j
        have hweight : pathWeight Q (snocEquivV W n p)
            = pathWeight Q p.1 * Q (p.1 (Fin.last n)) p.2 := by
          have hpw : pathWeight Q (snocEquivV W n p)
              = ∏ i : Fin (n + 1),
                  Q ((snocEquivV W n p) i.castSucc) ((snocEquivV W n p) i.succ) := rfl
          rw [hpw, Fin.prod_univ_castSucc]
          congr 1
          · refine Finset.prod_congr rfl fun i _ => ?_
            rw [hrestrict i.castSucc]
            congr 1
            exact hrestrict i.succ
          · rw [hrestrict (Fin.last n)]
            congr 1
        by_cases h : (p.1 0 = p₀ ∧ ∀ i : Fin (n + 1), p.1 i ∉ S) ∧ (p.2 ∉ S ∧ p.2 = y)
        · rw [if_pos (hcond.mpr h), if_pos h, hweight]
        · rw [if_neg (fun hc => h (hcond.mp hc)), if_neg h]
      rw [Finset.sum_congr rfl fun p _ => hstep p, Fintype.sum_prod_type]
      have hinner : ∀ ω : Fin (n + 1) → W,
          (∑ v : W, if (ω 0 = p₀ ∧ ∀ i : Fin (n + 1), ω i ∉ S) ∧ (v ∉ S ∧ v = y) then
              pathWeight Q ω * Q (ω (Fin.last n)) v else 0)
          = (if ω 0 = p₀ ∧ ∀ i : Fin (n + 1), ω i ∉ S then
              pathWeight Q ω * K (ω (Fin.last n)) y else 0) := by
        intro ω
        by_cases h : ω 0 = p₀ ∧ ∀ i : Fin (n + 1), ω i ∉ S
        · rw [if_pos h]
          by_cases hyS : y ∈ S
          · rw [hKval, if_pos hyS, mul_zero]
            refine Finset.sum_eq_zero fun v _ => ?_
            rw [if_neg]
            rintro ⟨-, hvS, hvy⟩
            exact hvS (hvy ▸ hyS)
          · rw [Finset.sum_eq_single y]
            · rw [if_pos ⟨h, hyS, rfl⟩, hKval, if_neg hyS]
            · intro v _ hv
              rw [if_neg]
              rintro ⟨-, -, hvy⟩
              exact hv hvy
            · intro hc; exact absurd (Finset.mem_univ y) hc
        · rw [if_neg h]
          exact Finset.sum_eq_zero fun v _ => by rw [if_neg (fun hc => h hc.1)]
      rw [Finset.sum_congr rfl fun ω _ => hinner ω]
      rw [pow_succ]
      have hrhs : (K ^ n * K) p₀ y = ∑ w, (K ^ n) p₀ w * K w y := rfl
      rw [hrhs]
      have hexp : ∀ w : W, (K ^ n) p₀ w * K w y
          = ∑ ω : Fin (n + 1) → W,
              (if (ω 0 = p₀ ∧ (∀ i : Fin (n + 1), ω i ∉ S) ∧ ω (Fin.last n) = w) then
                pathWeight Q ω * K w y else 0) := by
        intro w
        rw [← ih p₀ w hp₀]
        have hun : avoidSetAtProb Q p₀ S w n
            = ∑ ω : Fin (n + 1) → W,
                (if (ω 0 = p₀ ∧ (∀ i : Fin (n + 1), ω i ∉ S) ∧
                    ω (Fin.last n) = w) then pathWeight Q ω else 0) := rfl
        rw [hun, Finset.sum_mul]
        refine Finset.sum_congr rfl fun ω _ => ?_
        by_cases h : ω 0 = p₀ ∧ (∀ i : Fin (n + 1), ω i ∉ S) ∧ ω (Fin.last n) = w
        · rw [if_pos h, if_pos h]
        · rw [if_neg h, if_neg h, zero_mul]
      rw [Finset.sum_congr rfl fun w _ => hexp w, Finset.sum_comm]
      refine Finset.sum_congr rfl fun ω _ => ?_
      by_cases h : ω 0 = p₀ ∧ ∀ i : Fin (n + 1), ω i ∉ S
      · rw [if_pos h, Finset.sum_eq_single (ω (Fin.last n))]
        · rw [if_pos ⟨h.1, h.2, rfl⟩]
        · intro w _ hw
          rw [if_neg]
          rintro ⟨-, -, hlw⟩
          exact hw hlw.symm
        · intro hc; exact absurd (Finset.mem_univ _) hc
      · rw [if_neg h]
        exact (Finset.sum_eq_zero fun w _ => by
          rw [if_neg (fun hc => h ⟨hc.1, hc.2.1⟩)]).symm

/-- The set-avoidance tail probability is the corresponding row sum. -/
private lemma setAvoidTail_eq_rowSum {W : Type*} [Fintype W] [DecidableEq W]
    (Q : Matrix W W ℝ) (S : Finset W) (t : ℕ) (p₀ : W) (hp₀ : p₀ ∉ S) :
    setAvoidTailProb Q p₀ S t = ∑ y, ((killedSet Q S) ^ t) p₀ y := by
  classical
  have hsum : ∑ y, ((killedSet Q S) ^ t) p₀ y = ∑ y, avoidSetAtProb Q p₀ S y t :=
    Finset.sum_congr rfl fun y _ => (avoidSetAt_eq_killed_pow Q S t p₀ y hp₀).symm
  rw [hsum]
  have hexp : ∀ y : W, avoidSetAtProb Q p₀ S y t
      = ∑ ω : Fin (t + 1) → W,
          (if (ω 0 = p₀ ∧ (∀ i : Fin (t + 1), ω i ∉ S) ∧ ω (Fin.last t) = y) then
            pathWeight Q ω else 0) := fun y => rfl
  rw [Finset.sum_congr rfl fun y _ => hexp y, Finset.sum_comm]
  refine Finset.sum_congr rfl fun ω _ => ?_
  by_cases h : ω 0 = p₀ ∧ ∀ i : Fin (t + 1), ω i ∉ S
  · rw [if_pos h, Finset.sum_eq_single (ω (Fin.last t))]
    · rw [if_pos ⟨h.1, h.2, rfl⟩]
    · intro y _ hy
      rw [if_neg]
      rintro ⟨-, -, hly⟩
      exact hy hly.symm
    · intro hc; exact absurd (Finset.mem_univ _) hc
  · rw [if_neg h]
    exact (Finset.sum_eq_zero fun y _ => by
      rw [if_neg (fun hc => h ⟨hc.1, hc.2.1⟩)]).symm


/-- Summing the endpoint of the set-avoidance path sum gives the tail probability. -/
private lemma sum_avoidSetAt {W : Type*} [Fintype W] [DecidableEq W]
    (Q : Matrix W W ℝ) (S : Finset W) (t : ℕ) (p₀ : W) :
    ∑ y, avoidSetAtProb Q p₀ S y t = setAvoidTailProb Q p₀ S t := by
  classical
  have hexp : ∀ y : W, avoidSetAtProb Q p₀ S y t
      = ∑ ω : Fin (t + 1) → W,
          (if (ω 0 = p₀ ∧ (∀ i : Fin (t + 1), ω i ∉ S) ∧ ω (Fin.last t) = y) then
            pathWeight Q ω else 0) := fun y => rfl
  rw [Finset.sum_congr rfl fun y _ => hexp y, Finset.sum_comm]
  refine Finset.sum_congr rfl fun ω _ => ?_
  by_cases h : ω 0 = p₀ ∧ ∀ i : Fin (t + 1), ω i ∉ S
  · rw [if_pos h, Finset.sum_eq_single (ω (Fin.last t))]
    · rw [if_pos ⟨h.1, h.2, rfl⟩]
    · intro y _ hy
      rw [if_neg]
      rintro ⟨-, -, hly⟩
      exact hy hly.symm
    · intro hc; exact absurd (Finset.mem_univ _) hc
  · rw [if_neg h]
    exact Finset.sum_eq_zero fun y _ => by
      rw [if_neg (fun hc => h ⟨hc.1, hc.2.1⟩)]

/-- First-passage probabilities at time `0`. -/
private lemma hitSetAt_zero {V : Type*} [Fintype V] [DecidableEq V]
    (P : Matrix V V ℝ) (B : Finset V) (x y : V) :
    hitSetAtProb P x B y 0 = if x = y then 1 else 0 := by
  classical
  have hL : hitSetAtProb P x B y 0
      = ∑ ω : Fin 1 → V, (if ω 0 = x ∧ ω 0 = y then (1 : ℝ) else 0) := by
    refine Finset.sum_congr rfl fun ω _ => ?_
    have hcond : (ω 0 = x ∧ (∀ i : Fin 1, i ≠ Fin.last 0 → ω i ∉ B) ∧ ω (Fin.last 0) = y)
        ↔ (ω 0 = x ∧ ω 0 = y) := by
      constructor
      · rintro ⟨h1, -, h3⟩; exact ⟨h1, h3⟩
      · rintro ⟨h1, h2⟩
        exact ⟨h1, fun i hi => absurd (Subsingleton.elim i (Fin.last 0)) hi, h2⟩
    by_cases h : ω 0 = x ∧ ω 0 = y
    · rw [if_pos (hcond.mpr h), if_pos h]
      simp [pathWeight]
    · rw [if_neg (fun hc => h (hcond.mp hc)), if_neg h]
  rw [hL]
  by_cases hxy : x = y
  · rw [if_pos hxy, Finset.sum_eq_single (fun _ : Fin 1 => x)]
    · rw [if_pos ⟨rfl, hxy⟩]
    · intro ω _ hne
      rw [if_neg]
      rintro ⟨h1, -⟩
      exact hne (funext fun i => by rw [Subsingleton.elim i 0, h1])
    · intro hc; exact absurd (Finset.mem_univ _) hc
  · rw [if_neg hxy]
    refine Finset.sum_eq_zero fun ω _ => ?_
    rw [if_neg]
    rintro ⟨h1, h2⟩
    exact hxy (h1.symm.trans h2)

/-- Splitting off the last step of a first-passage trajectory. -/
private lemma hitSetAt_succ {V : Type*} [Fintype V] [DecidableEq V]
    (P : Matrix V V ℝ) (B : Finset V) (x y : V) (t : ℕ) :
    hitSetAtProb P x B y (t + 1) = ∑ z, avoidSetAtProb P x B z t * P z y := by
  classical
  have hL : hitSetAtProb P x B y (t + 1)
      = ∑ ω : Fin (t + 2) → V,
          (if ω 0 = x ∧ (∀ i : Fin (t + 2), i ≠ Fin.last (t + 1) → ω i ∉ B) ∧
              ω (Fin.last (t + 1)) = y then pathWeight P ω else 0) := rfl
  rw [hL, ← Equiv.sum_comp (snocEquivV V t)
    (fun ω : Fin (t + 2) → V =>
      if ω 0 = x ∧ (∀ i : Fin (t + 2), i ≠ Fin.last (t + 1) → ω i ∉ B) ∧
          ω (Fin.last (t + 1)) = y then pathWeight P ω else 0)]
  have hstep : ∀ p : (Fin (t + 1) → V) × V,
      (if (snocEquivV V t p) 0 = x ∧
          (∀ i : Fin (t + 2), i ≠ Fin.last (t + 1) → (snocEquivV V t p) i ∉ B) ∧
          (snocEquivV V t p) (Fin.last (t + 1)) = y then
        pathWeight P (snocEquivV V t p) else 0)
      = (if (p.1 0 = x ∧ ∀ i : Fin (t + 1), p.1 i ∉ B) ∧ p.2 = y then
          pathWeight P p.1 * P (p.1 (Fin.last t)) p.2 else 0) := by
    intro p
    have hrestrict : ∀ i : Fin (t + 1), (snocEquivV V t p) i.castSucc = p.1 i :=
      fun i => snocEquivV_castSucc t p i
    have hlast : (snocEquivV V t p) (Fin.last (t + 1)) = p.2 := snocEquivV_last t p
    have hzero : (snocEquivV V t p) 0 = p.1 0 := by
      have h := hrestrict 0
      rwa [Fin.castSucc_zero] at h
    have hcond : ((snocEquivV V t p) 0 = x ∧
          (∀ i : Fin (t + 2), i ≠ Fin.last (t + 1) → (snocEquivV V t p) i ∉ B) ∧
          (snocEquivV V t p) (Fin.last (t + 1)) = y)
        ↔ ((p.1 0 = x ∧ ∀ i : Fin (t + 1), p.1 i ∉ B) ∧ p.2 = y) := by
      constructor
      · rintro ⟨h0, hne, hy⟩
        refine ⟨⟨hzero ▸ h0, fun i => ?_⟩, hlast ▸ hy⟩
        rw [← hrestrict i]
        refine hne i.castSucc ?_
        intro hc
        have h1 : (i : ℕ) = t + 1 := by
          have := congrArg Fin.val hc
          simpa using this
        have h2 := i.isLt
        omega
      · rintro ⟨⟨h0, hall⟩, hy⟩
        refine ⟨hzero ▸ h0, fun i hi => ?_, hlast ▸ hy⟩
        induction i using Fin.lastCases with
        | last => exact absurd rfl hi
        | cast j => rw [hrestrict j]; exact hall j
    have hweight : pathWeight P (snocEquivV V t p)
        = pathWeight P p.1 * P (p.1 (Fin.last t)) p.2 := by
      have hpw : pathWeight P (snocEquivV V t p)
          = ∏ i : Fin (t + 1),
              P ((snocEquivV V t p) i.castSucc) ((snocEquivV V t p) i.succ) := rfl
      rw [hpw, Fin.prod_univ_castSucc]
      congr 1
      · refine Finset.prod_congr rfl fun i _ => ?_
        rw [hrestrict i.castSucc]
        congr 1
        exact hrestrict i.succ
      · rw [hrestrict (Fin.last t)]
        congr 1
    by_cases h : (p.1 0 = x ∧ ∀ i : Fin (t + 1), p.1 i ∉ B) ∧ p.2 = y
    · rw [if_pos (hcond.mpr h), if_pos h, hweight]
    · rw [if_neg (fun hc => h (hcond.mp hc)), if_neg h]
  rw [Finset.sum_congr rfl fun p _ => hstep p, Fintype.sum_prod_type]
  have hinner : ∀ ω : Fin (t + 1) → V,
      (∑ v : V, if (ω 0 = x ∧ ∀ i : Fin (t + 1), ω i ∉ B) ∧ v = y then
          pathWeight P ω * P (ω (Fin.last t)) v else 0)
      = (if ω 0 = x ∧ ∀ i : Fin (t + 1), ω i ∉ B then
          pathWeight P ω * P (ω (Fin.last t)) y else 0) := by
    intro ω
    by_cases h : ω 0 = x ∧ ∀ i : Fin (t + 1), ω i ∉ B
    · rw [if_pos h, Finset.sum_eq_single y]
      · rw [if_pos ⟨h, rfl⟩]
      · intro v _ hv; rw [if_neg (fun hc => hv hc.2)]
      · intro hc; exact absurd (Finset.mem_univ y) hc
    · rw [if_neg h]
      exact Finset.sum_eq_zero fun v _ => by rw [if_neg (fun hc => h hc.1)]
  rw [Finset.sum_congr rfl fun ω _ => hinner ω]
  have hR : ∑ z, avoidSetAtProb P x B z t * P z y
      = ∑ z, ∑ ω : Fin (t + 1) → V,
          (if ω 0 = x ∧ (∀ i : Fin (t + 1), ω i ∉ B) ∧ ω (Fin.last t) = z then
            pathWeight P ω * P z y else 0) := by
    refine Finset.sum_congr rfl fun z _ => ?_
    have hexp : avoidSetAtProb P x B z t
        = ∑ ω : Fin (t + 1) → V,
            (if ω 0 = x ∧ (∀ i : Fin (t + 1), ω i ∉ B) ∧ ω (Fin.last t) = z then
              pathWeight P ω else 0) := rfl
    rw [hexp, Finset.sum_mul]
    refine Finset.sum_congr rfl fun ω _ => ?_
    by_cases h : ω 0 = x ∧ (∀ i : Fin (t + 1), ω i ∉ B) ∧ ω (Fin.last t) = z
    · rw [if_pos h, if_pos h]
    · rw [if_neg h, if_neg h, zero_mul]
  rw [hR, Finset.sum_comm]
  refine Finset.sum_congr rfl fun ω _ => ?_
  by_cases h : ω 0 = x ∧ ∀ i : Fin (t + 1), ω i ∉ B
  · rw [if_pos h, Finset.sum_eq_single (ω (Fin.last t))]
    · rw [if_pos ⟨h.1, h.2, rfl⟩]
    · intro z _ hz
      rw [if_neg]
      rintro ⟨-, -, hlz⟩
      exact hz hlz.symm
    · intro hc; exact absurd (Finset.mem_univ _) hc
  · rw [if_neg h]
    exact (Finset.sum_eq_zero fun z _ => by
      rw [if_neg (fun hc => h ⟨hc.1, hc.2.1⟩)]).symm

/-- Trajectories avoiding `B` cannot start in `B`. -/
private lemma avoidSetAt_of_mem {V : Type*} [Fintype V] [DecidableEq V]
    (P : Matrix V V ℝ) (B : Finset V) (x : V) (hx : x ∈ B) (z : V) (t : ℕ) :
    avoidSetAtProb P x B z t = 0 := by
  refine Finset.sum_eq_zero fun ω _ => ?_
  rw [if_neg]
  rintro ⟨h0, hall, -⟩
  exact hall 0 (by rw [h0]; exact hx)

theorem solution {V : Type*} [Fintype V] [DecidableEq V]
    (c : V → V → ℝ) (hc : IsConductance c)
    (hpos : ∀ x : V, 0 < vertexConductance c x)
    (hirr : MarkovMixing.Irreducible (networkWalk c)) (a z : V) (haz : a ≠ z) :
    greenFn (networkWalk c) a z a =
      vertexConductance c a * effectiveResistance c a z := by
  classical
  haveI : Nonempty V := ⟨a⟩
  set P : Matrix V V ℝ := networkWalk c with hPdef
  have hPval : ∀ x y : V, P x y = c x y / vertexConductance c x := fun x y => rfl
  have hcx : ∀ x : V, vertexConductance c x ≠ 0 := fun x => ne_of_gt (hpos x)
  have hsumdiv : ∀ (u : V → ℝ) (d : ℝ), ∑ y, u y / d = (∑ y, u y) / d := by
    intro u d
    simp only [div_eq_mul_inv, ← Finset.sum_mul]
  have hP : IsStochastic P := by
    constructor
    · intro x y; rw [hPval]; exact div_nonneg (hc.1 x y) (le_of_lt (hpos x))
    · intro x
      rw [Finset.sum_congr rfl fun y _ => hPval x y, hsumdiv]
      exact div_self (hcx x)
  -- reversibility of the network walk
  have hrev : ∀ x y : V,
      vertexConductance c y * P y x = vertexConductance c x * P x y := by
    intro x y
    rw [hPval y x, hPval x y,
      mul_comm (vertexConductance c y) (c y x / vertexConductance c y),
      mul_comm (vertexConductance c x) (c x y / vertexConductance c x),
      div_mul_cancel₀ _ (hcx y), div_mul_cancel₀ _ (hcx x)]
    exact hc.2 y x
  have haz' : a ∉ ({z} : Finset V) := by simp [haz]
  set K : Matrix V V ℝ := killedSet P {z} with hKdef
  have hKval : ∀ x y : V, K x y = if y ∈ ({z} : Finset V) then 0 else P x y := fun x y => rfl
  -- the Green function as a sum of powers of the killed chain
  have hGpow : ∀ (t : ℕ) (x : V), avoidSetAtProb P a {z} x t = (K ^ t) a x :=
    fun t x => avoidSetAt_eq_killed_pow P {z} t a x haz'
  have hnn : ∀ (t : ℕ) (x : V), 0 ≤ avoidSetAtProb P a {z} x t := by
    intro t x
    refine Finset.sum_nonneg fun ω _ => ?_
    split
    · exact Finset.prod_nonneg fun i _ => hP.1 _ _
    · exact le_refl 0
  have hcmp : ∀ t : ℕ, setAvoidTailProb P a {z} t ≤ avoidTailProb P a z t := by
    intro t
    refine Finset.sum_le_sum fun ω _ => ?_
    by_cases h1 : ω 0 = a ∧ ∀ i : Fin (t + 1), ω i ∉ ({z} : Finset V)
    · rw [if_pos h1, if_pos ⟨h1.1, fun i _ hi => h1.2 i (by rw [hi]; simp)⟩]
    · rw [if_neg h1]
      split
      · exact Finset.prod_nonneg fun i _ => hP.1 _ _
      · exact le_refl 0
  have hsummable : ∀ x : V, Summable (fun t : ℕ => avoidSetAtProb P a {z} x t) := by
    intro x
    refine Summable.of_nonneg_of_le (fun t => hnn t x) (fun t => ?_)
      (MarkovMixing.summable_hitting_tails P hP hirr a z)
    calc avoidSetAtProb P a {z} x t ≤ ∑ y, avoidSetAtProb P a {z} y t :=
          Finset.single_le_sum (fun y _ => hnn t y) (Finset.mem_univ x)
      _ = setAvoidTailProb P a {z} t := sum_avoidSetAt P {z} t a
      _ ≤ avoidTailProb P a z t := hcmp t
  -- the Green function vanishes at `z` and satisfies the column recursion
  have hGz : greenFn P a z z = 0 := by
    unfold greenFn
    have h0 : ∀ t : ℕ, avoidSetAtProb P a {z} z t = 0 := by
      intro t
      refine Finset.sum_eq_zero fun ω _ => ?_
      rw [if_neg]
      rintro ⟨-, hall, hl⟩
      exact hall (Fin.last t) (by rw [hl]; simp)
    simp [h0]
  have hGrec : ∀ x : V, greenFn P a z x
      = (if a = x then (1 : ℝ) else 0) + ∑ y, greenFn P a z y * K y x := by
    intro x
    unfold greenFn
    rw [(hsummable x).tsum_eq_zero_add]
    congr 1
    · rw [hGpow 0 x, pow_zero, Matrix.one_apply]
    · have hstep : ∀ t : ℕ,
          avoidSetAtProb P a {z} x (t + 1) = ∑ y, avoidSetAtProb P a {z} y t * K y x := by
        intro t
        rw [hGpow (t + 1) x, pow_succ, Matrix.mul_apply]
        exact Finset.sum_congr rfl fun y _ => by rw [hGpow t y]
      rw [tsum_congr hstep,
        Summable.tsum_finsetSum (fun y _ => (hsummable y).mul_right _)]
      exact Finset.sum_congr rfl fun y _ => tsum_mul_right
  -- the potential `g = G / c`
  set g : V → ℝ := fun x => greenFn P a z x / vertexConductance c x with hgdef
  have hgval : ∀ x : V, g x = greenFn P a z x / vertexConductance c x := fun x => rfl
  have hgz : g z = 0 := by rw [hgval, hGz, zero_div]
  have hgrec : ∀ x : V, x ≠ z →
      g x = (if a = x then (1 : ℝ) / vertexConductance c x else 0) + ∑ y, P x y * g y := by
    intro x hxz
    have h1 : ∑ y, greenFn P a z y * K y x
        = vertexConductance c x * ∑ y, P x y * g y := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun y _ => ?_
      have hy0 : vertexConductance c y ≠ 0 := hcx y
      rw [hKval, if_neg (by simp [hxz])]
      have e1 : vertexConductance c x * (P x y * g y)
          = (vertexConductance c x * P x y) * (greenFn P a z y / vertexConductance c y) := by
        rw [hgval]; ring
      rw [e1, ← hrev x y]
      field_simp
    have hx0 : vertexConductance c x ≠ 0 := hcx x
    rw [hgval, hGrec x, h1]
    by_cases hax : a = x
    · rw [if_pos hax, if_pos hax]
      field_simp
    · rw [if_neg hax, if_neg hax]
      field_simp
      ring
  have hgharm : HarmonicOn P g {x : V | x ∉ ({a, z} : Finset V)} := by
    intro x hx
    simp only [Set.mem_setOf_eq] at hx
    have hxa : x ≠ a := fun hcc => hx (by rw [hcc]; simp)
    have hxz : x ≠ z := fun hcc => hx (by rw [hcc]; simp)
    rw [hgrec x hxz, if_neg (Ne.symm hxa), zero_add]
  have hgdrift : g a - ∑ y, P a y * g y = 1 / vertexConductance c a := by
    rw [hgrec a haz, if_pos rfl]; ring
  -- identify `g` with a multiple of the voltage
  set φ : V → ℝ := fun y => if y = a then g a else 0 with hφdef
  obtain ⟨-, -, huniq⟩ :=
    MarkovMixing.harmonic_extension P hP hirr {a, z} ⟨a, by simp⟩ φ
  have hgeq := huniq g (by
    intro x hx
    rcases Finset.mem_insert.mp hx with h | h
    · rw [h]
      show g a = if a = a then g a else 0
      rw [if_pos rfl]
    · rw [Finset.mem_singleton.mp h]
      show g z = if z = a then g a else 0
      rw [if_neg (Ne.symm haz)]
      exact hgz) hgharm
  have hgvolt : ∀ x : V, g x = g a * firstHitAtProb P x {a, z} a := by
    intro x
    have hx := congrFun hgeq x
    rw [hx, Finset.sum_pair haz]
    show (if a = a then g a else 0) * firstHitAtProb P x {a, z} a
      + (if z = a then g a else 0) * firstHitAtProb P x {a, z} z
      = g a * firstHitAtProb P x {a, z} a
    rw [if_pos rfl, if_neg (Ne.symm haz)]
    ring
  have hvolt : ∀ x : V, voltage c a z x = firstHitAtProb P x {a, z} a := by
    intro x
    show hitBeforeProb P x a z = firstHitAtProb P x {a, z} a
    unfold firstHitAtProb hitBeforeProb
    refine (tsum_congr fun t => ?_).symm
    refine Finset.sum_congr rfl fun ω _ => ?_
    have hiff : (ω 0 = x ∧ (∀ i : Fin (t + 1), i ≠ Fin.last t → ω i ∉ ({a, z} : Finset V)) ∧
          ω (Fin.last t) = a)
        ↔ (ω 0 = x ∧ ω (Fin.last t) = a ∧
          (∀ i : Fin (t + 1), i ≠ Fin.last t → ω i ≠ a) ∧ ∀ i : Fin (t + 1), ω i ≠ z) := by
      constructor
      · rintro ⟨h0, hav, hl⟩
        refine ⟨h0, hl, fun i hi hcc => hav i hi (by rw [hcc]; simp), fun i => ?_⟩
        by_cases hi : i = Fin.last t
        · rw [hi, hl]; exact haz
        · exact fun hcc => hav i hi (by rw [hcc]; simp)
      · rintro ⟨h0, hl, hna, hnz⟩
        refine ⟨h0, fun i hi hmem => ?_, hl⟩
        rcases Finset.mem_insert.mp hmem with h | h
        · exact hna i hi h
        · exact hnz i (Finset.mem_singleton.mp h)
    by_cases hcond : ω 0 = x ∧ (∀ i : Fin (t + 1), i ≠ Fin.last t → ω i ∉ ({a, z} : Finset V)) ∧
        ω (Fin.last t) = a
    · rw [if_pos hcond, if_pos (hiff.mp hcond)]
    · rw [if_neg hcond, if_neg (fun hd => hcond (hiff.mpr hd))]
  -- the current out of `a`
  have hcurrent : ∑ y, c a y * (g a - g y) = 1 := by
    have h1 : ∀ y : V, c a y * (g a - g y)
        = vertexConductance c a * (P a y * g a - P a y * g y) := by
      intro y
      rw [hPval]
      field_simp
      rw [mul_div_assoc, div_self (hcx a), mul_one]
    rw [Finset.sum_congr rfl fun y _ => h1 y, ← Finset.mul_sum]
    have h2 : ∑ y, (P a y * g a - P a y * g y) = g a - ∑ y, P a y * g y := by
      rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hP.2 a, one_mul]
    rw [h2, hgdrift]
    field_simp
    exact div_self (hcx a)
  have hkey : g a * currentStrength c a z = 1 := by
    rw [← hcurrent]
    unfold currentStrength
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [hvolt a, hvolt y]
    linear_combination (-(c a y)) * hgvolt a + (c a y) * hgvolt y
  have hcurne : currentStrength c a z ≠ 0 := by
    intro hcc
    rw [hcc, mul_zero] at hkey
    exact absurd hkey.symm one_ne_zero
  have hga : g a = effectiveResistance c a z := by
    unfold effectiveResistance
    field_simp
    linarith [hkey]
  rw [hgval] at hga
  show greenFn P a z a = vertexConductance c a * effectiveResistance c a z
  rw [← hga, mul_comm (vertexConductance c a), div_mul_cancel₀ _ (hcx a)]
