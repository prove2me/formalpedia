-- Prove2me | solution 1 for MarkovMixing.top_to_random_strong_stationary
-- status  : ACCEPTED   (prove)
-- author  : @ann
-- created : 2026-08-22T23:45:30.366521+00:00
-- url     : https://prove2.me/submissions/c698b733-9762-41dd-9b8c-a49b14a165b1

import Definitions.Def_mm_stopping
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.GroupTheory.Perm.Fin

/-!
# The top-to-random strong stationary time (LPW Proposition 6.1, Example 6.7)
-/

namespace MarkovMixing

noncomputable section
open scoped BigOperators
open Finset

section Paths

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Reindex a sum over trajectories of length `t+2` by (prefix, last state). -/
private lemma snoc_sum {t : ℕ} (f : (Fin (t + 2) → V) → ℝ) :
    ∑ ω : Fin (t + 2) → V, f ω
      = ∑ ω : Fin (t + 1) → V, ∑ y : V, f (Fin.snoc ω y) := by
  let e : ((Fin (t + 1) → V) × V) ≃ (Fin (t + 2) → V) :=
    { toFun := fun p => Fin.snoc p.1 p.2
      invFun := fun ω => (Fin.init ω, ω (Fin.last _))
      left_inv := by intro p; ext <;> simp
      right_inv := by intro ω; simp }
  have := Equiv.sum_comp e f
  rw [← this, Fintype.sum_prod_type]
  rfl

private lemma pathWeight_snoc (P : Matrix V V ℝ) {t : ℕ}
    (ω : Fin (t + 1) → V) (y : V) :
    pathWeight P (Fin.snoc ω y : Fin (t + 2) → V)
      = pathWeight P ω * P (ω (Fin.last t)) y := by
  simp only [pathWeight]
  rw [Fin.prod_univ_castSucc]
  congr 1
  · refine Finset.prod_congr rfl fun i _ => ?_
    rw [show (i.castSucc : Fin (t + 1)).castSucc = (i.castSucc : Fin (t+1)).castSucc from rfl,
      Fin.snoc_castSucc, Fin.succ_castSucc, Fin.snoc_castSucc]
  · rw [Fin.snoc_castSucc]
    congr 1
    rw [show (Fin.last t).succ = Fin.last (t + 1) from rfl, Fin.snoc_last]

/-- Group a sum over trajectories by their final state. -/
private lemma group_by_last {t : ℕ} (F : (Fin (t + 1) → V) → ℝ) :
    ∑ ω : Fin (t + 1) → V, F ω
      = ∑ z : V, ∑ ω : Fin (t + 1) → V, (if ω (Fin.last t) = z then F ω else 0) := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun ω _ => ?_
  simp

/-- The weight of the trajectories of length `u` from `x` to `h`, damped at each
intermediate state by `q`. -/
private def Ap (P : Matrix V V ℝ) (x : V) (q : ℕ → V → ℝ) (u : ℕ) (h : V) : ℝ :=
  ∑ ω : Fin (u + 1) → V,
    if ω 0 = x ∧ ω (Fin.last u) = h then
      pathWeight P ω * ∏ v : Fin u, q v.val (ω v.castSucc)
    else 0

private lemma sum_ite_last (c : ℝ) (f : V → ℝ) (h : V) :
    ∑ y : V, c * f y * (if y = h then (1 : ℝ) else 0) = c * f h := by
  have hcong : ∀ y ∈ (univ : Finset V), c * f y * (if y = h then (1 : ℝ) else 0)
      = if y = h then c * f h else 0 := by
    intro y _
    by_cases hy : y = h
    · subst hy; simp
    · simp [hy]
  rw [Finset.sum_congr rfl hcong]
  simp

private lemma Ap_zero (P : Matrix V V ℝ) (x : V) (q : ℕ → V → ℝ) (h : V) :
    Ap P x q 0 h = if h = x then (1 : ℝ) else 0 := by
  simp only [Ap]
  rw [Fintype.sum_equiv (Equiv.funUnique (Fin 1) V)
      (fun ω : Fin 1 → V => if ω 0 = x ∧ ω (Fin.last 0) = h then
          pathWeight P ω * ∏ v : Fin 0, q v.val (ω v.castSucc) else 0)
      (fun v : V => if v = x then (if h = x then (1 : ℝ) else 0) else 0)]
  · simp
  · intro ω
    simp only [pathWeight, Finset.univ_eq_empty, Finset.prod_empty, mul_one,
      Equiv.funUnique_apply]
    have hl : (Fin.last 0 : Fin 1) = 0 := rfl
    rw [hl]
    show (if ω 0 = x ∧ ω 0 = h then (1 : ℝ) else 0)
        = if ω 0 = x then (if h = x then (1 : ℝ) else 0) else 0
    by_cases h1 : ω 0 = x
    · rw [if_pos h1]
      by_cases h2 : h = x
      · rw [if_pos h2, if_pos ⟨h1, by rw [h1, h2]⟩]
      · rw [if_neg h2, if_neg]
        rintro ⟨-, hcon⟩
        exact h2 (by rw [← hcon, h1])
    · rw [if_neg h1, if_neg]
      rintro ⟨hcon, -⟩
      exact h1 hcon

private lemma Ap_succ (P : Matrix V V ℝ) (x : V) (q : ℕ → V → ℝ) (u : ℕ) (h : V) :
    Ap P x q (u + 1) h = ∑ z : V, Ap P x q u z * q u z * P z h := by
  simp only [Ap]
  rw [snoc_sum]
  have key : ∀ ω : Fin (u + 1) → V, ∀ y : V,
      (if (Fin.snoc ω y : Fin (u + 2) → V) 0 = x ∧
            (Fin.snoc ω y : Fin (u + 2) → V) (Fin.last (u + 1)) = h then
          pathWeight P (Fin.snoc ω y : Fin (u + 2) → V) *
            ∏ v : Fin (u + 1), q v.val ((Fin.snoc ω y : Fin (u + 2) → V) v.castSucc)
        else 0)
      = (if ω 0 = x then (1 : ℝ) else 0) * pathWeight P ω *
          (∏ v : Fin u, q v.val (ω v.castSucc)) * q u (ω (Fin.last u)) *
          P (ω (Fin.last u)) y * (if y = h then (1 : ℝ) else 0) := by
    intro ω y
    have h0 : (Fin.snoc ω y : Fin (u + 2) → V) 0 = ω 0 := by
      have : (0 : Fin (u + 2)) = Fin.castSucc (0 : Fin (u + 1)) := rfl
      rw [this, Fin.snoc_castSucc]
    have hl : (Fin.snoc ω y : Fin (u + 2) → V) (Fin.last (u + 1)) = y := by
      simp
    have hprod : (∏ v : Fin (u + 1),
        q v.val ((Fin.snoc ω y : Fin (u + 2) → V) v.castSucc))
        = (∏ v : Fin u, q v.val (ω v.castSucc)) * q u (ω (Fin.last u)) := by
      rw [Fin.prod_univ_castSucc]
      congr 1
      · refine Finset.prod_congr rfl fun i _ => ?_
        rw [show (i.castSucc : Fin (u+1)).castSucc = (i.castSucc : Fin (u+1)).castSucc from rfl,
          Fin.snoc_castSucc]
        rfl
      · rw [Fin.snoc_castSucc]
        rfl
    rw [h0, hl, hprod, pathWeight_snoc]
    by_cases hx : ω 0 = x <;> by_cases hy : y = h <;> simp [hx, hy] <;> ring
  calc ∑ ω : Fin (u + 1) → V, ∑ y : V, _
      = ∑ ω : Fin (u + 1) → V, ∑ y : V,
          ((if ω 0 = x then (1 : ℝ) else 0) * pathWeight P ω *
            (∏ v : Fin u, q v.val (ω v.castSucc)) * q u (ω (Fin.last u)) *
            P (ω (Fin.last u)) y * (if y = h then (1 : ℝ) else 0)) := by
        exact Finset.sum_congr rfl fun ω _ => Finset.sum_congr rfl fun y _ => key ω y
    _ = ∑ ω : Fin (u + 1) → V,
          ((if ω 0 = x then (1 : ℝ) else 0) * pathWeight P ω *
            (∏ v : Fin u, q v.val (ω v.castSucc)) * q u (ω (Fin.last u)) *
            P (ω (Fin.last u)) h) := by
        exact Finset.sum_congr rfl fun ω _ => sum_ite_last _ _ h
    _ = ∑ z : V, Ap P x q u z * q u z * P z h := by
        rw [group_by_last (t := u)]
        refine Finset.sum_congr rfl fun z _ => ?_
        simp only [Ap, Finset.sum_mul]
        refine Finset.sum_congr rfl fun ω _ => ?_
        by_cases hz : ω (Fin.last u) = z
        · by_cases hx : ω 0 = x <;> simp [hz, hx] <;> ring
        · simp [hz]

private lemma Ap_congr (P : Matrix V V ℝ) (x : V) (q q' : ℕ → V → ℝ) (u : ℕ)
    (hq : ∀ v : ℕ, v < u → q v = q' v) (h : V) : Ap P x q u h = Ap P x q' u h := by
  simp only [Ap]
  refine Finset.sum_congr rfl fun ω _ => ?_
  by_cases hc : ω 0 = x ∧ ω (Fin.last u) = h
  · rw [if_pos hc, if_pos hc]
    refine congrArg _ (Finset.prod_congr rfl fun v _ => ?_)
    rw [hq v.val v.isLt]
  · rw [if_neg hc, if_neg hc]

private lemma sum_of_inj {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    (φ : α → β) (hφ : Function.Injective φ) (F : β → ℝ)
    (hF : ∀ b : β, (∀ a : α, φ a ≠ b) → F b = 0) :
    ∑ b : β, F b = ∑ a : α, F (φ a) := by
  have h1 : ∑ b ∈ (univ : Finset α).image φ, F b = ∑ a : α, F (φ a) :=
    Finset.sum_image fun a _ a' _ hEq => hφ hEq
  rw [← h1]
  refine (Finset.sum_subset (Finset.subset_univ _) ?_).symm
  intro b _ hb
  refine hF b fun a hEq => hb ?_
  exact Finset.mem_image.mpr ⟨a, Finset.mem_univ a, hEq⟩

end Paths

/-! ### The top-to-random shuffle as a right random walk -/

private lemma cyc_inv_zero {n : ℕ} (j : Fin n) :
    (Fin.cycleRange j)⁻¹ (⟨0, j.pos⟩ : Fin n) = j := by
  haveI : NeZero n := NeZero.of_pos j.pos
  have h : Fin.cycleRange j j = (⟨0, j.pos⟩ : Fin n) := Fin.cycleRange_self j
  exact (Equiv.Perm.inv_eq_iff_eq).mpr h.symm

private lemma cyc_inj {n : ℕ} : Function.Injective (Fin.cycleRange : Fin n → Equiv.Perm (Fin n)) := by
  intro j k hjk
  rw [← cyc_inv_zero j, ← cyc_inv_zero k, hjk]

private lemma insert_eq {n : ℕ} (x : Equiv.Perm (Fin n)) (j i : Fin n) :
    topToRandomInsert x j i = (x * Fin.cycleRange j) i := by
  haveI : NeZero n := NeZero.of_pos i.pos
  show _ = x (Fin.cycleRange j i)
  simp only [topToRandomInsert]
  by_cases h1 : i.val < j.val
  · rw [dif_pos h1]
    congr 1
    refine (Fin.ext ?_).symm
    rw [Fin.coe_cycleRange_of_lt (by exact h1)]
  · rw [dif_neg h1]
    by_cases h2 : i = j
    · rw [if_pos h2, h2, Fin.cycleRange_self]
      rfl
    · rw [if_neg h2]
      have : j < i := lt_of_le_of_ne (by omega) (Ne.symm h2)
      rw [Fin.cycleRange_of_gt this]

private lemma ttr_apply {n : ℕ} (x y : Equiv.Perm (Fin n)) :
    topToRandom n x y = if ∃ j : Fin n, y = x * Fin.cycleRange j then (1 : ℝ) / n else 0 := by
  simp only [topToRandom]
  have hfilt : (univ.filter fun j : Fin n => ∀ i : Fin n, y i = topToRandomInsert x j i)
      = univ.filter fun j : Fin n => y = x * Fin.cycleRange j := by
    refine Finset.filter_congr fun j _ => ?_
    constructor
    · intro h; exact Equiv.ext fun i => by rw [h i, insert_eq]
    · intro h i; rw [h, insert_eq]
  rw [hfilt]
  by_cases hex : ∃ j : Fin n, y = x * Fin.cycleRange j
  · obtain ⟨j₀, hj₀⟩ := hex
    have : (univ.filter fun j : Fin n => y = x * Fin.cycleRange j) = {j₀} := by
      refine Finset.eq_singleton_iff_unique_mem.mpr ⟨by simp [hj₀], ?_⟩
      intro j hj
      simp only [Finset.mem_filter] at hj
      have : x * Fin.cycleRange j = x * Fin.cycleRange j₀ := by rw [← hj.2, ← hj₀]
      exact cyc_inj (mul_left_cancel this)
    rw [this, if_pos ⟨j₀, hj₀⟩]
    simp
  · rw [if_neg hex]
    have : (univ.filter fun j : Fin n => y = x * Fin.cycleRange j) = ∅ := by
      refine Finset.filter_eq_empty_iff.mpr fun j _ hj => hex ⟨j, hj⟩
    rw [this]
    simp

/-- Forward one-step sum: the walk multiplies on the right by a uniform `cycleRange`. -/
private lemma sum_next {n : ℕ} (z : Equiv.Perm (Fin n)) (g : Equiv.Perm (Fin n) → ℝ) :
    ∑ y : Equiv.Perm (Fin n), topToRandom n z y * g y
      = ∑ j : Fin n, (1 / n : ℝ) * g (z * Fin.cycleRange j) := by
  rw [sum_of_inj (fun j : Fin n => z * Fin.cycleRange j)
      (fun j k hjk => cyc_inj (mul_left_cancel hjk))
      (fun y => topToRandom n z y * g y) ?_]
  · refine Finset.sum_congr rfl fun j _ => ?_
    rw [ttr_apply, if_pos ⟨j, rfl⟩]
  · intro y hy
    show topToRandom n z y * g y = 0
    rw [ttr_apply, if_neg (fun ⟨j, hj⟩ => hy j hj.symm), zero_mul]

/-- Backward one-step sum: reindex the previous state. -/
private lemma sum_prev {n : ℕ} (h : Equiv.Perm (Fin n)) (f : Equiv.Perm (Fin n) → ℝ) :
    ∑ z : Equiv.Perm (Fin n), f z * topToRandom n z h
      = ∑ j : Fin n, f (h * (Fin.cycleRange j)⁻¹) * (1 / n : ℝ) := by
  rw [sum_of_inj (fun j : Fin n => h * (Fin.cycleRange j)⁻¹)
      (fun j k hjk => cyc_inj (inv_injective (mul_left_cancel hjk)))
      (fun z => f z * topToRandom n z h) ?_]
  · refine Finset.sum_congr rfl fun j _ => ?_
    rw [ttr_apply, if_pos ⟨j, by group⟩]
  · intro z hz
    show f z * topToRandom n z h = 0
    rw [ttr_apply, if_neg ?_, mul_zero]
    rintro ⟨j, hj⟩
    exact hz j (by rw [hj]; group)

/-! ### The stopping rule, unwound -/

private def bcard {n : ℕ} (hn : 0 < n) (x : Equiv.Perm (Fin n)) : Fin n := x ⟨n - 1, by omega⟩

private def indA {n : ℕ} (hn : 0 < n) (b : Fin n) (z : Equiv.Perm (Fin n)) : ℝ :=
  if z ⟨0, hn⟩ = b then 0 else 1

private def indB {n : ℕ} (hn : 0 < n) (b : Fin n) (z : Equiv.Perm (Fin n)) : ℝ :=
  if z ⟨0, hn⟩ = b then 1 else 0

private lemma indA_add_indB {n : ℕ} (hn : 0 < n) (b : Fin n) (z : Equiv.Perm (Fin n)) :
    indA hn b z = 1 - indB hn b z := by
  simp only [indA, indB]; split_ifs <;> ring

/-- The number of trajectories, weighted, that have not yet put the bottom card on
top at any time `< u` and end at `h`. -/
private def Acnt {n : ℕ} (hn : 0 < n) (x : Equiv.Perm (Fin n)) (u : ℕ)
    (h : Equiv.Perm (Fin n)) : ℝ :=
  Ap (topToRandom n) x (fun _ => indA hn (bcard hn x)) u h

private lemma Acnt_zero {n : ℕ} (hn : 0 < n) (x h : Equiv.Perm (Fin n)) :
    Acnt hn x 0 h = if h = x then (1 : ℝ) else 0 := Ap_zero _ _ _ _

private lemma Acnt_succ {n : ℕ} (hn : 0 < n) (x : Equiv.Perm (Fin n)) (u : ℕ)
    (h : Equiv.Perm (Fin n)) :
    Acnt hn x (u + 1) h
      = ∑ z : Equiv.Perm (Fin n),
          Acnt hn x u z * indA hn (bcard hn x) z * topToRandom n z h := Ap_succ _ _ _ _ _

private lemma rule_at {n : ℕ} (hn : 0 < n) (x : Equiv.Perm (Fin n)) (t : ℕ) (ht : 1 ≤ t)
    (ρ : Fin (t + 1) → Equiv.Perm (Fin n)) (hx : ρ 0 = x) :
    topToRandomRule n t ρ = indB hn (bcard hn x) (ρ ⟨t - 1, by omega⟩) := by
  simp only [topToRandomRule, indB, bcard]
  rw [dif_pos ⟨hn, ht⟩, hx]
  rfl

private lemma rule_zero {n t : ℕ} (ht : ¬ 1 ≤ t) (ρ : Fin (t + 1) → Equiv.Perm (Fin n)) :
    topToRandomRule n t ρ = 0 := by
  simp only [topToRandomRule]
  rw [dif_neg (fun h => ht h.2)]

/-- The stopping-rule weights, packaged as a state-dependent damping. -/
private def qt {n : ℕ} (hn : 0 < n) (b : Fin n) (u : ℕ) : ℕ → Equiv.Perm (Fin n) → ℝ :=
  fun v z => if v < u then indA hn b z else indB hn b z

private lemma prod_rule {n : ℕ} (hn : 0 < n) (x : Equiv.Perm (Fin n)) (u : ℕ)
    (ω : Fin (u + 2) → Equiv.Perm (Fin n)) (hx : ω 0 = x) :
    (∏ v : Fin (u + 1), (1 - topToRandomRule n v.val (pathPrefix ω v)))
        * topToRandomRule n (u + 1) ω
      = ∏ v : Fin (u + 1), qt hn (bcard hn x) u v.val (ω v.castSucc) := by
  have hL : (∏ v : Fin (u + 1), (1 - topToRandomRule n v.val (pathPrefix ω v)))
      = ∏ v : Fin u, indA hn (bcard hn x) (ω v.castSucc.castSucc) := by
    rw [Fin.prod_univ_succ]
    have h0 : (1 : ℝ) - topToRandomRule n (0 : Fin (u + 1)).val (pathPrefix ω 0) = 1 := by
      rw [rule_zero (by simp)]; ring
    rw [h0, one_mul]
    refine Finset.prod_congr rfl fun v _ => ?_
    have hpx : (pathPrefix ω v.succ) 0 = x := hx
    have hrule := rule_at hn x (v.succ : Fin (u + 1)).val (by simp)
      (pathPrefix ω v.succ) hpx
    rw [hrule, indA_add_indB]
    rfl
  have hR : topToRandomRule n (u + 1) ω = indB hn (bcard hn x) (ω (Fin.last u).castSucc) := by
    rw [rule_at hn x (u + 1) (by omega) ω hx]
    rfl
  rw [hL, hR, Fin.prod_univ_castSucc]
  congr 1
  · refine Finset.prod_congr rfl fun v _ => ?_
    simp only [qt]
    rw [if_pos (by exact v.isLt)]
  · simp only [qt]
    rw [if_neg (by simp)]

private lemma stop_zero {n : ℕ} (x y : Equiv.Perm (Fin n)) :
    stopAtProb (topToRandom n) x (topToRandomRule n) 0 y = 0 := by
  simp only [stopAtProb]
  refine Finset.sum_eq_zero fun ω _ => ?_
  rw [rule_zero (by simp)]
  split_ifs <;> simp

private lemma stop_succ {n : ℕ} (hn : 0 < n) (x : Equiv.Perm (Fin n)) (u : ℕ)
    (y : Equiv.Perm (Fin n)) :
    stopAtProb (topToRandom n) x (topToRandomRule n) (u + 1) y
      = ∑ z : Equiv.Perm (Fin n),
          Acnt hn x u z * indB hn (bcard hn x) z * topToRandom n z y := by
  have hEq : stopAtProb (topToRandom n) x (topToRandomRule n) (u + 1) y
      = Ap (topToRandom n) x (qt hn (bcard hn x) u) (u + 1) y := by
    simp only [stopAtProb, Ap]
    refine Finset.sum_congr rfl fun ω _ => ?_
    by_cases hc : ω 0 = x ∧ ω (Fin.last (u + 1)) = y
    · rw [if_pos hc, if_pos hc, mul_assoc, prod_rule hn x u ω hc.1]
    · rw [if_neg hc, if_neg hc]
  rw [hEq, Ap_succ]
  refine Finset.sum_congr rfl fun z _ => ?_
  have h1 : Ap (topToRandom n) x (qt hn (bcard hn x) u) u z = Acnt hn x u z := by
    refine Ap_congr _ _ _ _ _ (fun v hv => ?_) _
    funext w
    simp only [qt]
    rw [if_pos hv]
  have h2 : qt hn (bcard hn x) u u z = indB hn (bcard hn x) z := by
    simp only [qt]; rw [if_neg (by omega)]
  rw [h1, h2]

/-! ### Undoing one shuffle -/

private lemma cyc_inv_mid {n : ℕ} (j i : Fin n) (h1 : 1 ≤ i.val) (h2 : i.val ≤ j.val) :
    (Fin.cycleRange j)⁻¹ i = ⟨i.val - 1, by omega⟩ := by
  refine (Equiv.Perm.inv_eq_iff_eq).mpr (Fin.ext ?_).symm
  rw [Fin.coe_cycleRange_of_lt (show (⟨i.val - 1, by omega⟩ : Fin n) < j from by
    rw [Fin.lt_def]; simp only []; omega)]
  simp only []
  omega

private lemma cyc_inv_hi {n : ℕ} (j i : Fin n) (h1 : j.val < i.val) :
    (Fin.cycleRange j)⁻¹ i = i := by
  refine (Equiv.Perm.inv_eq_iff_eq).mpr ?_
  rw [Fin.cycleRange_of_gt (by rw [Fin.lt_def]; exact h1)]

private lemma prev_zero {n : ℕ} (hn : 0 < n) (h : Equiv.Perm (Fin n)) (j : Fin n) :
    (h * (Fin.cycleRange j)⁻¹) (⟨0, hn⟩ : Fin n) = h j := by
  show h ((Fin.cycleRange j)⁻¹ ⟨0, hn⟩) = h j
  rw [cyc_inv_zero]

private lemma prev_mid {n : ℕ} (h : Equiv.Perm (Fin n)) (j i : Fin n)
    (h1 : 1 ≤ i.val) (h2 : i.val ≤ j.val) :
    (h * (Fin.cycleRange j)⁻¹) i = h ⟨i.val - 1, by omega⟩ := by
  show h ((Fin.cycleRange j)⁻¹ i) = _
  rw [cyc_inv_mid j i h1 h2]

private lemma prev_hi {n : ℕ} (h : Equiv.Perm (Fin n)) (j i : Fin n) (h1 : j.val < i.val) :
    (h * (Fin.cycleRange j)⁻¹) i = h i := by
  show h ((Fin.cycleRange j)⁻¹ i) = _
  rw [cyc_inv_hi j i h1]

/-- Two decks are equivalent when the bottom card sits at the same position and the
cards weakly above it agree; the cards strictly below may be permuted arbitrarily. -/
private def Rel {n : ℕ} (b : Fin n) (h h' : Equiv.Perm (Fin n)) : Prop :=
  h⁻¹ b = h'⁻¹ b ∧ ∀ i : Fin n, i.val ≤ (h⁻¹ b).val → h i = h' i

private lemma Rel_symm {n : ℕ} {b : Fin n} {h h' : Equiv.Perm (Fin n)} (hR : Rel b h h') :
    Rel b h' h := by
  refine ⟨hR.1.symm, fun i hi => (hR.2 i ?_).symm⟩
  rw [hR.1]; exact hi

private lemma Rel_top {n : ℕ} {b : Fin n} {h h' : Equiv.Perm (Fin n)} (hR : Rel b h h')
    (hn : 0 < n) : h (⟨0, hn⟩ : Fin n) = h' ⟨0, hn⟩ :=
  hR.2 _ (Nat.zero_le _)

/-- Undoing one shuffle preserves the equivalence, after the matching reindexing
`j ↦ h'⁻¹ (h j)` of the insertion position. -/
private lemma prev_rel {n : ℕ} (hn : 0 < n) (b : Fin n) (h h' : Equiv.Perm (Fin n))
    (hR : Rel b h h') (j : Fin n) :
    Rel b (h * (Fin.cycleRange j)⁻¹) (h' * (Fin.cycleRange (h'⁻¹ (h j)))⁻¹) := by
  set m : Fin n := h⁻¹ b with hm
  have hbm : h m = b := by rw [hm]; simp
  have hbm' : h' (h'⁻¹ b) = b := by simp
  have hmm' : h'⁻¹ b = m := hR.1.symm
  rcases lt_trichotomy j.val m.val with hcase | hcase | hcase
  · -- the insertion happened strictly above the bottom card
    have hsig : h'⁻¹ (h j) = j := by
      rw [hR.2 j (le_of_lt hcase)]; simp
    rw [hsig]
    have hz : (h * (Fin.cycleRange j)⁻¹) m = b := by rw [prev_hi h j m hcase, hbm]
    have hz' : (h' * (Fin.cycleRange j)⁻¹) m = b := by
      rw [prev_hi h' j m hcase, ← hR.2 m (le_refl _), hbm]
    have hinv : (h * (Fin.cycleRange j)⁻¹)⁻¹ b = m := (Equiv.Perm.inv_eq_iff_eq).mpr hz.symm
    have hinv' : (h' * (Fin.cycleRange j)⁻¹)⁻¹ b = m := (Equiv.Perm.inv_eq_iff_eq).mpr hz'.symm
    refine ⟨by rw [hinv, hinv'], fun i hi => ?_⟩
    rw [hinv] at hi
    rcases Nat.eq_zero_or_pos i.val with h0 | h0
    · have hie : i = (⟨0, hn⟩ : Fin n) := Fin.ext (by omega)
      rw [hie, prev_zero hn h j, prev_zero hn h' j, hR.2 j (le_of_lt hcase)]
    · by_cases hij : i.val ≤ j.val
      · rw [prev_mid h j i h0 hij, prev_mid h' j i h0 hij]
        exact hR.2 _ (by simp only []; omega)
      · have hij' : j.val < i.val := by omega
        rw [prev_hi h j i hij', prev_hi h' j i hij']
        exact hR.2 _ hi
  · -- the bottom card itself was inserted: it is now on top of both decks
    have hjm : j = m := Fin.ext hcase
    have hsig : h'⁻¹ (h j) = j := by rw [hjm, hbm, hmm']
    rw [hsig]
    have hz : (h * (Fin.cycleRange j)⁻¹) (⟨0, hn⟩ : Fin n) = b := by
      rw [prev_zero hn h j, hjm, hbm]
    have hz' : (h' * (Fin.cycleRange j)⁻¹) (⟨0, hn⟩ : Fin n) = b := by
      rw [prev_zero hn h' j, hjm, ← hR.2 m (le_refl _), hbm]
    have hinv : (h * (Fin.cycleRange j)⁻¹)⁻¹ b = (⟨0, hn⟩ : Fin n) :=
      (Equiv.Perm.inv_eq_iff_eq).mpr hz.symm
    have hinv' : (h' * (Fin.cycleRange j)⁻¹)⁻¹ b = (⟨0, hn⟩ : Fin n) :=
      (Equiv.Perm.inv_eq_iff_eq).mpr hz'.symm
    refine ⟨by rw [hinv, hinv'], fun i hi => ?_⟩
    rw [hinv] at hi
    have hi0 : i.val ≤ 0 := hi
    have hie : i = (⟨0, hn⟩ : Fin n) := Fin.ext (show i.val = 0 by omega)
    rw [hie, hz, hz']
  · -- the insertion happened strictly below the bottom card
    set k : Fin n := h'⁻¹ (h j) with hk
    have hhk : h' k = h j := by rw [hk]; simp
    have hkm : m.val < k.val := by
      by_contra hcon
      have hle : k.val ≤ m.val := by omega
      have : h j = h k := by rw [← hhk, ← hR.2 k hle]
      have : j = k := h.injective this
      omega
    have hp : m.val + 1 < n := by omega
    set p : Fin n := ⟨m.val + 1, hp⟩ with hpdef
    have hz : (h * (Fin.cycleRange j)⁻¹) p = b := by
      rw [prev_mid h j p (by simp only [hpdef]; omega) (by simp only [hpdef]; omega)]
      rw [show (⟨p.val - 1, by omega⟩ : Fin n) = m from Fin.ext (by simp only [hpdef]; omega), hbm]
    have hz' : (h' * (Fin.cycleRange k)⁻¹) p = b := by
      rw [prev_mid h' k p (by simp only [hpdef]; omega) (by simp only [hpdef]; omega)]
      rw [show (⟨p.val - 1, by omega⟩ : Fin n) = m from Fin.ext (by simp only [hpdef]; omega),
        ← hR.2 m (le_refl _), hbm]
    have hinv : (h * (Fin.cycleRange j)⁻¹)⁻¹ b = p := (Equiv.Perm.inv_eq_iff_eq).mpr hz.symm
    have hinv' : (h' * (Fin.cycleRange k)⁻¹)⁻¹ b = p := (Equiv.Perm.inv_eq_iff_eq).mpr hz'.symm
    refine ⟨by rw [hinv, hinv'], fun i hi => ?_⟩
    rw [hinv] at hi
    simp only [hpdef] at hi
    rcases Nat.eq_zero_or_pos i.val with h0 | h0
    · have hie : i = (⟨0, hn⟩ : Fin n) := Fin.ext (by omega)
      rw [hie, prev_zero hn h j, prev_zero hn h' k, hhk]
    · rw [prev_mid h j i h0 (by omega), prev_mid h' k i h0 (by omega)]
      exact hR.2 _ (by simp only []; omega)

/-! ### The uniformity invariant -/

private lemma rel_eq_x {n : ℕ} (hn : 0 < n) (x h : Equiv.Perm (Fin n))
    (hR : Rel (bcard hn x) h x) : h = x := by
  have hx : x⁻¹ (bcard hn x) = (⟨n - 1, by omega⟩ : Fin n) := by
    simp only [bcard]
    simp
  refine Equiv.ext fun i => hR.2 i ?_
  rw [hR.1, hx]
  have := i.isLt
  simp only []
  omega

private lemma Acnt_rel {n : ℕ} (hn : 0 < n) (x : Equiv.Perm (Fin n)) :
    ∀ (u : ℕ) (h h' : Equiv.Perm (Fin n)), Rel (bcard hn x) h h' →
      Acnt hn x u h = Acnt hn x u h' := by
  intro u
  induction u with
  | zero =>
    intro h h' hR
    rw [Acnt_zero, Acnt_zero]
    by_cases hx : h = x
    · have hR' : Rel (bcard hn x) x h' := by rw [hx] at hR; exact hR
      have hx' : h' = x := rel_eq_x hn x h' (Rel_symm hR')
      rw [if_pos hx, if_pos hx']
    · have hx' : h' ≠ x := by
        intro hcon
        refine hx (rel_eq_x hn x h ?_)
        rw [hcon] at hR; exact hR
      rw [if_neg hx, if_neg hx']
  | succ u ih =>
    intro h h' hR
    rw [Acnt_succ, Acnt_succ, sum_prev, sum_prev]
    set b := bcard hn x with hb
    set F : Fin n → ℝ :=
      fun k => Acnt hn x u (h' * (Fin.cycleRange k)⁻¹) *
        indA hn b (h' * (Fin.cycleRange k)⁻¹) * (1 / n : ℝ) with hF
    have hstep : ∀ j : Fin n,
        Acnt hn x u (h * (Fin.cycleRange j)⁻¹) * indA hn b (h * (Fin.cycleRange j)⁻¹)
            * (1 / n : ℝ)
          = F ((h'⁻¹ * h : Equiv.Perm (Fin n)) j) := by
      intro j
      have hrel := prev_rel hn b h h' hR j
      have hsig : (h'⁻¹ * h : Equiv.Perm (Fin n)) j = h'⁻¹ (h j) := rfl
      rw [hF]
      simp only [hsig]
      rw [ih _ _ hrel]
      congr 2
      simp only [indA, Rel_top hrel hn]
    calc ∑ j : Fin n, Acnt hn x u (h * (Fin.cycleRange j)⁻¹) *
            indA hn b (h * (Fin.cycleRange j)⁻¹) * (1 / n : ℝ)
        = ∑ j : Fin n, F ((h'⁻¹ * h : Equiv.Perm (Fin n)) j) :=
          Finset.sum_congr rfl fun j _ => hstep j
      _ = ∑ j : Fin n, F j := Equiv.sum_comp (h'⁻¹ * h : Equiv.Perm (Fin n)) F

/-- After the stopping time, the deck is at a `Rel`-equivalent state whatever the
target `y` is, so the stopped law is constant. -/
private lemma stop_const {n : ℕ} (hn : 0 < n) (x : Equiv.Perm (Fin n)) (u : ℕ)
    (y : Equiv.Perm (Fin n)) :
    stopAtProb (topToRandom n) x (topToRandomRule n) (u + 1) y
      = Acnt hn x u (y * (Fin.cycleRange (y⁻¹ (bcard hn x)))⁻¹) * (1 / n : ℝ) := by
  set b := bcard hn x with hb
  rw [stop_succ hn x u y, sum_prev]
  have hterm : ∀ j : Fin n,
      Acnt hn x u (y * (Fin.cycleRange j)⁻¹) * indB hn b (y * (Fin.cycleRange j)⁻¹)
          * (1 / n : ℝ)
        = if j = y⁻¹ b then
            Acnt hn x u (y * (Fin.cycleRange j)⁻¹) * (1 / n : ℝ) else 0 := by
    intro j
    have hz : (y * (Fin.cycleRange j)⁻¹) (⟨0, hn⟩ : Fin n) = y j := prev_zero hn y j
    simp only [indB, hz]
    by_cases hj : j = y⁻¹ b
    · rw [if_pos hj, if_pos (by rw [hj]; simp)]
      ring
    · rw [if_neg hj, if_neg ?_]
      · ring
      · intro hcon
        exact hj ((Equiv.Perm.inv_eq_iff_eq).mpr hcon.symm).symm
  rw [Finset.sum_congr rfl fun j _ => hterm j]
  simp

private lemma stop_uniform {n : ℕ} (hn : 0 < n) (x : Equiv.Perm (Fin n)) (u : ℕ)
    (y y' : Equiv.Perm (Fin n)) :
    stopAtProb (topToRandom n) x (topToRandomRule n) (u + 1) y
      = stopAtProb (topToRandom n) x (topToRandomRule n) (u + 1) y' := by
  set b := bcard hn x with hb
  rw [stop_const hn x u y, stop_const hn x u y']
  have htop : ∀ w : Equiv.Perm (Fin n),
      (w * (Fin.cycleRange (w⁻¹ b))⁻¹) (⟨0, hn⟩ : Fin n) = b := by
    intro w
    rw [prev_zero hn w (w⁻¹ b)]
    simp
  have hinv : ∀ w : Equiv.Perm (Fin n),
      (w * (Fin.cycleRange (w⁻¹ b))⁻¹)⁻¹ b = (⟨0, hn⟩ : Fin n) := fun w =>
    (Equiv.Perm.inv_eq_iff_eq).mpr (htop w).symm
  have hrel : Rel b (y * (Fin.cycleRange (y⁻¹ b))⁻¹) (y' * (Fin.cycleRange (y'⁻¹ b))⁻¹) := by
    refine ⟨by rw [hinv, hinv], fun i hi => ?_⟩
    rw [hinv] at hi
    have hi0 : i.val ≤ 0 := hi
    have hie : i = (⟨0, hn⟩ : Fin n) := Fin.ext (show i.val = 0 by omega)
    rw [hie, htop, htop]
  rw [Acnt_rel hn x u _ _ hrel]

/-! ### Total mass and its geometric decay -/

private lemma ttr_nonneg {n : ℕ} (z y : Equiv.Perm (Fin n)) : 0 ≤ topToRandom n z y := by
  rw [ttr_apply]
  split_ifs
  · positivity
  · exact le_refl 0

private lemma Acnt_nonneg {n : ℕ} (hn : 0 < n) (x : Equiv.Perm (Fin n)) (u : ℕ)
    (h : Equiv.Perm (Fin n)) : 0 ≤ Acnt hn x u h := by
  refine Finset.sum_nonneg fun ω _ => ?_
  split_ifs with hc
  · refine mul_nonneg (Finset.prod_nonneg fun i _ => ttr_nonneg _ _)
      (Finset.prod_nonneg fun v _ => ?_)
    simp only [indA]
    split_ifs <;> norm_num
  · exact le_refl 0

private lemma row_sum {n : ℕ} (hn : 0 < n) (z : Equiv.Perm (Fin n)) :
    ∑ y : Equiv.Perm (Fin n), topToRandom n z y = 1 := by
  have h := sum_next z (fun _ => (1 : ℝ))
  simp only [mul_one] at h
  rw [h]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp

private lemma sum_swap_row {n : ℕ} (c g : Equiv.Perm (Fin n) → ℝ) :
    ∑ h : Equiv.Perm (Fin n), (∑ z : Equiv.Perm (Fin n), c z * topToRandom n z h) * g h
      = ∑ z : Equiv.Perm (Fin n), c z * ∑ y : Equiv.Perm (Fin n), topToRandom n z y * g y := by
  have h1 : ∀ h : Equiv.Perm (Fin n),
      (∑ z : Equiv.Perm (Fin n), c z * topToRandom n z h) * g h
        = ∑ z : Equiv.Perm (Fin n), c z * (topToRandom n z h * g h) := by
    intro h; rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun z _ => by ring
  rw [Finset.sum_congr rfl fun h _ => h1 h, Finset.sum_comm]
  exact Finset.sum_congr rfl fun z _ => by rw [Finset.mul_sum]

private lemma Acnt_push {n : ℕ} (hn : 0 < n) (x : Equiv.Perm (Fin n)) (u : ℕ)
    (g : Equiv.Perm (Fin n) → ℝ) :
    ∑ h : Equiv.Perm (Fin n), Acnt hn x (u + 1) h * g h
      = ∑ z : Equiv.Perm (Fin n), Acnt hn x u z * indA hn (bcard hn x) z *
          ∑ y : Equiv.Perm (Fin n), topToRandom n z y * g y := by
  rw [Finset.sum_congr rfl fun h _ => by rw [Acnt_succ hn x u h]]
  exact sum_swap_row _ g

private def Rsum {n : ℕ} (hn : 0 < n) (x : Equiv.Perm (Fin n)) (u : ℕ) : ℝ :=
  ∑ h : Equiv.Perm (Fin n), Acnt hn x u h

private def Ssum {n : ℕ} (hn : 0 < n) (x : Equiv.Perm (Fin n)) (u : ℕ) : ℝ :=
  ∑ h : Equiv.Perm (Fin n), Acnt hn x u h * indB hn (bcard hn x) h

private lemma Rsum_zero {n : ℕ} (hn : 0 < n) (x : Equiv.Perm (Fin n)) : Rsum hn x 0 = 1 := by
  simp only [Rsum]
  rw [Finset.sum_congr rfl fun h _ => Acnt_zero hn x h]
  simp

private lemma Rsum_succ {n : ℕ} (hn : 0 < n) (x : Equiv.Perm (Fin n)) (u : ℕ) :
    Rsum hn x (u + 1) = Rsum hn x u - Ssum hn x u := by
  have h := Acnt_push hn x u (fun _ => (1 : ℝ))
  simp only [mul_one] at h
  simp only [Rsum]
  rw [h]
  rw [Finset.sum_congr rfl fun z _ => by rw [row_sum hn z]]
  simp only [mul_one, Ssum]
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [indA_add_indB]
  ring

private lemma sum_stop {n : ℕ} (hn : 0 < n) (x : Equiv.Perm (Fin n)) (u : ℕ) :
    ∑ y : Equiv.Perm (Fin n), stopAtProb (topToRandom n) x (topToRandomRule n) (u + 1) y
      = Ssum hn x u := by
  have h : ∀ y : Equiv.Perm (Fin n),
      stopAtProb (topToRandom n) x (topToRandomRule n) (u + 1) y
        = (∑ z : Equiv.Perm (Fin n),
            Acnt hn x u z * indB hn (bcard hn x) z * topToRandom n z y) * 1 := by
    intro y; rw [stop_succ hn x u y, mul_one]
  rw [Finset.sum_congr rfl fun y _ => h y, sum_swap_row]
  simp only [mul_one]
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [row_sum hn z, mul_one]

private def Vsum {n : ℕ} (hn : 0 < n) (x : Equiv.Perm (Fin n)) (u : ℕ) : ℝ :=
  ∑ h : Equiv.Perm (Fin n), Acnt hn x u h * (2 : ℝ) ^ ((h⁻¹ (bcard hn x)).val)

private lemma pos_shift {n : ℕ} (b : Fin n) (z : Equiv.Perm (Fin n)) (j : Fin n) :
    ((z * Fin.cycleRange j)⁻¹ b) = (Fin.cycleRange j)⁻¹ (z⁻¹ b) := by
  rw [mul_inv_rev]; rfl

private lemma cyc_inv_le {n : ℕ} (j i : Fin n) (hi : 1 ≤ i.val) :
    ((Fin.cycleRange j)⁻¹ i).val ≤ i.val := by
  by_cases hij : i.val ≤ j.val
  · rw [cyc_inv_mid j i hi hij]; simp only []; omega
  · rw [cyc_inv_hi j i (by omega)]

private lemma step_bound {n : ℕ} (hn : 0 < n) (b : Fin n) (z : Equiv.Perm (Fin n))
    (hz : 1 ≤ (z⁻¹ b).val) :
    ∑ y : Equiv.Perm (Fin n), topToRandom n z y * (2 : ℝ) ^ ((y⁻¹ b).val)
      ≤ (1 - 1 / (2 * n)) * (2 : ℝ) ^ ((z⁻¹ b).val) := by
  obtain ⟨mm, hmm⟩ : ∃ mm : ℕ, (z⁻¹ b).val = mm + 1 := ⟨(z⁻¹ b).val - 1, by omega⟩
  rw [sum_next z (fun y => (2 : ℝ) ^ ((y⁻¹ b).val)), ← Finset.mul_sum]
  set L : Fin n := ⟨n - 1, by omega⟩ with hL
  have hlast : ((z * Fin.cycleRange L)⁻¹ b).val = mm := by
    rw [pos_shift, cyc_inv_mid L (z⁻¹ b) (by omega) (by simp only [hL]; have := (z⁻¹ b).isLt; omega)]
    simp only []
    omega
  have hother : ∀ j : Fin n,
      ((z * Fin.cycleRange j)⁻¹ b).val ≤ mm + 1 := by
    intro j
    rw [pos_shift]
    have := cyc_inv_le j (z⁻¹ b) hz
    omega
  have hsplit : ∑ j : Fin n, (2 : ℝ) ^ (((z * Fin.cycleRange j)⁻¹ b).val)
      ≤ (2 : ℝ) ^ mm + ((n : ℝ) - 1) * (2 : ℝ) ^ (mm + 1) := by
    have hmem : L ∈ (univ : Finset (Fin n)) := Finset.mem_univ L
    rw [← Finset.add_sum_erase _ _ hmem, hlast]
    have hcard : ((univ : Finset (Fin n)).erase L).card = n - 1 := by
      rw [Finset.card_erase_of_mem hmem, Finset.card_univ, Fintype.card_fin]
    have hb : ∑ j ∈ (univ : Finset (Fin n)).erase L,
        (2 : ℝ) ^ (((z * Fin.cycleRange j)⁻¹ b).val)
          ≤ ((univ : Finset (Fin n)).erase L).card • ((2 : ℝ) ^ (mm + 1)) := by
      refine Finset.sum_le_card_nsmul _ _ _ fun j _ => ?_
      exact pow_le_pow_right₀ (by norm_num) (hother j)
    rw [hcard, nsmul_eq_mul] at hb
    have hn1 : (((n - 1 : ℕ) : ℝ)) = (n : ℝ) - 1 := by
      have : (1 : ℕ) ≤ n := hn
      push_cast [Nat.cast_sub this]
      ring
    rw [hn1] at hb
    linarith
  have hpos : (0 : ℝ) < n := by exact_mod_cast hn
  rw [hmm]
  have hfinal : (1 / (n : ℝ)) * ((2 : ℝ) ^ mm + ((n : ℝ) - 1) * (2 : ℝ) ^ (mm + 1))
      = (1 - 1 / (2 * n)) * (2 : ℝ) ^ (mm + 1) := by
    field_simp
    ring
  calc (1 / (n : ℝ)) * ∑ j : Fin n, (2 : ℝ) ^ (((z * Fin.cycleRange j)⁻¹ b).val)
      ≤ (1 / (n : ℝ)) * ((2 : ℝ) ^ mm + ((n : ℝ) - 1) * (2 : ℝ) ^ (mm + 1)) := by
        exact mul_le_mul_of_nonneg_left hsplit (by positivity)
    _ = (1 - 1 / (2 * n)) * (2 : ℝ) ^ (mm + 1) := hfinal

private lemma lam_pos {n : ℕ} (hn : 0 < n) : (0 : ℝ) ≤ 1 - 1 / (2 * n) := by
  have h1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have : (1 : ℝ) / (2 * n) ≤ 1 := by
    rw [div_le_one (by linarith)]
    linarith
  linarith

private lemma lam_lt {n : ℕ} (hn : 0 < n) : (1 : ℝ) - 1 / (2 * n) < 1 := by
  have h1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have : (0 : ℝ) < 1 / (2 * n) := by positivity
  linarith

private lemma Vsum_succ_le {n : ℕ} (hn : 0 < n) (x : Equiv.Perm (Fin n)) (u : ℕ) :
    Vsum hn x (u + 1) ≤ (1 - 1 / (2 * n)) * Vsum hn x u := by
  set b := bcard hn x with hb
  simp only [Vsum]
  rw [Acnt_push hn x u (fun y => (2 : ℝ) ^ ((y⁻¹ b).val))]
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun z _ => ?_
  by_cases hzb : z (⟨0, hn⟩ : Fin n) = b
  · have : indA hn b z = 0 := by simp only [indA]; rw [if_pos hzb]
    rw [this]
    simp only [mul_zero, zero_mul]
    exact mul_nonneg (lam_pos hn) (mul_nonneg (Acnt_nonneg hn x u z) (by positivity))
  · have hia : indA hn b z = 1 := by simp only [indA]; rw [if_neg hzb]
    have hz1 : 1 ≤ (z⁻¹ b).val := by
      rcases Nat.eq_zero_or_pos (z⁻¹ b).val with h0 | h0
      · exfalso
        have : z⁻¹ b = (⟨0, hn⟩ : Fin n) := Fin.ext (by simpa using h0)
        exact hzb (((Equiv.Perm.inv_eq_iff_eq).mp this).symm)
      · omega
    rw [hia, mul_one]
    have hstep := step_bound hn b z hz1
    have hA := Acnt_nonneg hn x u z
    nlinarith [hA, hstep]

private lemma Vsum_zero {n : ℕ} (hn : 0 < n) (x : Equiv.Perm (Fin n)) :
    Vsum hn x 0 = (2 : ℝ) ^ (n - 1) := by
  simp only [Vsum]
  rw [Finset.sum_congr rfl fun h _ => by rw [Acnt_zero hn x h]]
  rw [Finset.sum_eq_single x]
  · have : x⁻¹ (bcard hn x) = (⟨n - 1, by omega⟩ : Fin n) := by
      simp only [bcard]; simp
    rw [this]
    simp
  · intro h _ hne; rw [if_neg hne]; ring
  · intro hcon; exact absurd (Finset.mem_univ x) hcon

private lemma Vsum_le {n : ℕ} (hn : 0 < n) (x : Equiv.Perm (Fin n)) (u : ℕ) :
    Vsum hn x u ≤ (2 : ℝ) ^ (n - 1) * (1 - 1 / (2 * n)) ^ u := by
  induction u with
  | zero => rw [Vsum_zero hn x]; simp
  | succ u ih =>
    calc Vsum hn x (u + 1) ≤ (1 - 1 / (2 * n)) * Vsum hn x u := Vsum_succ_le hn x u
      _ ≤ (1 - 1 / (2 * n)) * ((2 : ℝ) ^ (n - 1) * (1 - 1 / (2 * n)) ^ u) :=
          mul_le_mul_of_nonneg_left ih (lam_pos hn)
      _ = (2 : ℝ) ^ (n - 1) * (1 - 1 / (2 * n)) ^ (u + 1) := by ring

private lemma Rsum_le_Vsum {n : ℕ} (hn : 0 < n) (x : Equiv.Perm (Fin n)) (u : ℕ) :
    Rsum hn x u ≤ Vsum hn x u := by
  simp only [Rsum, Vsum]
  refine Finset.sum_le_sum fun h _ => ?_
  have hA := Acnt_nonneg hn x u h
  have : (1 : ℝ) ≤ (2 : ℝ) ^ ((h⁻¹ (bcard hn x)).val) := one_le_pow₀ (by norm_num)
  nlinarith

private lemma Rsum_nonneg {n : ℕ} (hn : 0 < n) (x : Equiv.Perm (Fin n)) (u : ℕ) :
    0 ≤ Rsum hn x u := Finset.sum_nonneg fun h _ => Acnt_nonneg hn x u h

private lemma Rsum_tendsto {n : ℕ} (hn : 0 < n) (x : Equiv.Perm (Fin n)) :
    Filter.Tendsto (fun u => Rsum hn x u) Filter.atTop (nhds 0) := by
  have hlim : Filter.Tendsto
      (fun u => (2 : ℝ) ^ (n - 1) * (1 - 1 / (2 * n)) ^ u) Filter.atTop (nhds 0) := by
    have := tendsto_pow_atTop_nhds_zero_of_lt_one (lam_pos hn) (lam_lt hn)
    simpa using this.const_mul ((2 : ℝ) ^ (n - 1))
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
    (fun u => Rsum_nonneg hn x u) (fun u => le_trans (Rsum_le_Vsum hn x u) (Vsum_le hn x u))

private lemma tsum_of_partial (v : ℕ → ℝ) (L : ℝ) (hnn : ∀ t, 0 ≤ v t)
    (hlim : Filter.Tendsto (fun T => ∑ t ∈ Finset.range (T + 1), v t)
      Filter.atTop (nhds L)) : (∑' t, v t) = L := by
  have hlim' : Filter.Tendsto (fun m => ∑ t ∈ Finset.range m, v t)
      Filter.atTop (nhds L) := (Filter.tendsto_add_atTop_iff_nat 1).mp hlim
  have hmono : Monotone fun m => ∑ t ∈ Finset.range m, v t := by
    intro a b hab
    refine Finset.sum_le_sum_of_subset_of_nonneg
      (fun i hi => Finset.mem_range.mpr
        (lt_of_lt_of_le (Finset.mem_range.mp hi) hab)) fun i _ _ => hnn i
  have hle : ∀ m, ∑ t ∈ Finset.range m, v t ≤ L := hmono.ge_of_tendsto hlim'
  have hsum : Summable v := summable_of_sum_range_le hnn hle
  exact tendsto_nhds_unique hsum.hasSum.tendsto_sum_nat hlim'

private lemma Ssum_nonneg {n : ℕ} (hn : 0 < n) (x : Equiv.Perm (Fin n)) (u : ℕ) :
    0 ≤ Ssum hn x u := by
  refine Finset.sum_nonneg fun h _ => mul_nonneg (Acnt_nonneg hn x u h) ?_
  simp only [indB]; split_ifs <;> norm_num

private lemma partial_Ssum {n : ℕ} (hn : 0 < n) (x : Equiv.Perm (Fin n)) (U : ℕ) :
    ∑ u ∈ Finset.range U, Ssum hn x u = 1 - Rsum hn x U := by
  induction U with
  | zero => simp [Rsum_zero hn x]
  | succ U ih =>
    rw [Finset.sum_range_succ, ih, Rsum_succ hn x U]
    ring

private lemma partial_stop {n : ℕ} (hn : 0 < n) (x : Equiv.Perm (Fin n)) (U : ℕ) :
    ∑ t ∈ Finset.range (U + 1),
        (∑ y : Equiv.Perm (Fin n), stopAtProb (topToRandom n) x (topToRandomRule n) t y)
      = 1 - Rsum hn x U := by
  rw [Finset.sum_range_succ']
  have h0 : ∑ y : Equiv.Perm (Fin n),
      stopAtProb (topToRandom n) x (topToRandomRule n) 0 y = 0 := by
    refine Finset.sum_eq_zero fun y _ => stop_zero x y
  rw [h0, add_zero]
  rw [Finset.sum_congr rfl fun u _ => sum_stop hn x u]
  exact partial_Ssum hn x U

end

end MarkovMixing

open MarkovMixing

theorem solution (n : ℕ) (hn : 2 ≤ n) (x : Equiv.Perm (Fin n)) :
    IsStrongStationaryTime (topToRandom n) (uniformDist (Equiv.Perm (Fin n))) x
      (topToRandomRule n) := by
  have hn0 : 0 < n := by omega
  refine ⟨?_, ?_, ?_⟩
  · -- the rule takes values in `[0,1]`
    intro t ω
    simp only [topToRandomRule]
    split_ifs <;> norm_num
  · -- the stopping time is almost surely finite
    refine tsum_of_partial _ _ ?_ ?_
    · intro t
      cases t with
      | zero => exact le_of_eq (Finset.sum_eq_zero fun y _ => (stop_zero x y)).symm
      | succ u => rw [sum_stop hn0 x u]; exact Ssum_nonneg hn0 x u
    · have hlim : Filter.Tendsto (fun U => 1 - Rsum hn0 x U) Filter.atTop (nhds 1) := by
        have := (tendsto_const_nhds (x := (1 : ℝ))
          (f := Filter.atTop (α := ℕ))).sub (Rsum_tendsto hn0 x)
        simpa using this
      exact hlim.congr fun U => (partial_stop hn0 x U).symm
  · -- the stopped deck is uniform and independent of the stopping time
    intro t y
    have hcard : (0 : ℝ) < (Fintype.card (Equiv.Perm (Fin n)) : ℝ) := by
      exact_mod_cast Fintype.card_pos
    cases t with
    | zero =>
      rw [stop_zero x y, Finset.sum_eq_zero fun z _ => stop_zero x z, zero_mul]
    | succ u =>
      have hconst : ∑ z : Equiv.Perm (Fin n),
          stopAtProb (topToRandom n) x (topToRandomRule n) (u + 1) z
            = (Fintype.card (Equiv.Perm (Fin n)) : ℝ) *
              stopAtProb (topToRandom n) x (topToRandomRule n) (u + 1) y := by
        rw [Finset.sum_congr rfl fun z _ => stop_uniform hn0 x u z y]
        simp [Finset.card_univ, mul_comm]
      rw [hconst]
      simp only [uniformDist]
      field_simp
