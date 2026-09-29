-- Prove2me | solution 1 for MarkovMixing.cftp_correct
-- status  : ACCEPTED   (prove)
-- author  : @MKPynnic
-- created : 2026-08-22T18:35:55.500762+00:00
-- url     : https://prove2.me/submissions/3b09d723-af56-4a72-8d9d-60ce8695215a

import Definitions.Def_mm_cftp
import Mathlib.Order.Filter.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Algebra.BigOperators.Fin

/-!
# Correctness of coupling from the past (Propp–Wilson)

Two ingredients.

1. **The random map iterates.**  If `ν` represents `P`, then composing `t`
   i.i.d. maps realises `P^t`:
   `∑_F 1{F(x) = y} ∏_i ν(F_i) = P^t(x,y)`.
   The induction peels off the outermost map `F 0` (the one applied last),
   splitting the tuple with an explicit `head/tail` equivalence.

2. **Coalescence controls the error.**  The CFTP output probability counts
   only the tuples that have collapsed to the constant `y`, so it is
   dominated by `P^t(x,y)` for *every* `x`, and the gap is supported on the
   non-coalesced tuples.  Averaging over `x` against the stationary `π`
   replaces `P^t(x,y)` by `π(y)` exactly, leaving
   `0 ≤ π(y) − cftpOutputProb ν t y ≤ cftpNotCoalescedProb ν t`.

The hypothesis that the non-coalescence probability tends to `0` then
squeezes the output probability to `π(y)` — with no error term at all in the
limit, which is the point of CFTP: the output is *exactly* stationary.
-/

namespace MarkovMixing

open scoped BigOperators

/-- Splitting a tuple of update maps into its first entry and the rest. -/
private def consEquiv (M : Type*) (t : ℕ) : M × (Fin t → M) ≃ (Fin (t + 1) → M) where
  toFun p := Fin.cons p.1 p.2
  invFun F := (F 0, fun i => F i.succ)
  left_inv p := by simp
  right_inv F := by
    funext i
    refine Fin.cases ?_ ?_ i <;> simp

private lemma cftpCompose_cons {V : Type*} [Fintype V] [DecidableEq V] {t : ℕ}
    (f : V → V) (G : Fin t → (V → V)) (x : V) :
    cftpCompose (Fin.cons f G) x = f (cftpCompose G x) := by
  simp [cftpCompose, List.ofFn_succ]

/-- Applying `t` i.i.d. update maps realises the `t`-step transition matrix. -/
private lemma compose_pow {V : Type*} [Fintype V] [DecidableEq V]
    (P : Matrix V V ℝ) (ν : (V → V) → ℝ) (hν : IsRandomMapRep P ν) (t : ℕ) :
    ∀ x y : V, ∑ F : Fin t → (V → V),
      (if cftpCompose F x = y then ∏ i : Fin t, ν (F i) else 0) = (P ^ t) x y := by
  classical
  have hstep : ∀ z y : V, ∑ f : V → V, (if f z = y then ν f else 0) = P z y := by
    intro z y
    rw [← Finset.sum_filter]
    exact hν.2 z y
  induction t with
  | zero =>
      intro x y
      simp [cftpCompose, Matrix.one_apply]
  | succ n ih =>
      intro x y
      have hsplit : ∑ F : Fin (n + 1) → (V → V),
            (if cftpCompose F x = y then ∏ i : Fin (n + 1), ν (F i) else 0)
          = ∑ f : V → V, ∑ G : Fin n → (V → V),
              (if f (cftpCompose G x) = y then ν f * ∏ i : Fin n, ν (G i) else 0) := by
        rw [← Equiv.sum_comp (consEquiv (V → V) n)
          (fun F => if cftpCompose F x = y then ∏ i : Fin (n + 1), ν (F i) else 0)]
        rw [Fintype.sum_prod_type]
        refine Finset.sum_congr rfl fun f _ => Finset.sum_congr rfl fun G _ => ?_
        have h1 : cftpCompose ((consEquiv (V → V) n) (f, G)) x = f (cftpCompose G x) :=
          cftpCompose_cons f G x
        have h2 : ∏ i : Fin (n + 1), ν (((consEquiv (V → V) n) (f, G)) i)
            = ν f * ∏ i : Fin n, ν (G i) := by
          rw [Fin.prod_univ_succ]
          simp [consEquiv]
        rw [h1, h2]
      rw [hsplit]
      have hswap : ∑ f : V → V, ∑ G : Fin n → (V → V),
            (if f (cftpCompose G x) = y then ν f * ∏ i : Fin n, ν (G i) else 0)
          = ∑ G : Fin n → (V → V),
              (∏ i : Fin n, ν (G i)) * P (cftpCompose G x) y := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun G _ => ?_
        rw [← hstep (cftpCompose G x) y, Finset.mul_sum]
        refine Finset.sum_congr rfl fun f _ => ?_
        by_cases h : f (cftpCompose G x) = y <;> simp [h, mul_comm]
      rw [hswap]
      have hgroup : ∑ G : Fin n → (V → V), (∏ i : Fin n, ν (G i)) * P (cftpCompose G x) y
          = ∑ z : V, (∑ G : Fin n → (V → V),
              (if cftpCompose G x = z then ∏ i : Fin n, ν (G i) else 0)) * P z y := by
        have hexp : ∀ G : Fin n → (V → V),
            (∏ i : Fin n, ν (G i)) * P (cftpCompose G x) y
              = ∑ z : V, (if cftpCompose G x = z then ∏ i : Fin n, ν (G i) else 0) * P z y := by
          intro G
          rw [Finset.sum_eq_single (cftpCompose G x)]
          · simp
          · intro z _ hz
            simp [Ne.symm hz, hz]
          · intro hcon
            exact absurd (Finset.mem_univ _) hcon
        rw [Finset.sum_congr rfl fun G _ => hexp G, Finset.sum_comm]
        refine Finset.sum_congr rfl fun z _ => ?_
        rw [← Finset.sum_mul]
      rw [hgroup]
      simp only [ih x]
      rw [pow_succ, Matrix.mul_apply]

private lemma vecMul_pow_stationary {V : Type*} [Fintype V] [DecidableEq V]
    {P : Matrix V V ℝ} {π : V → ℝ} (hπ : IsStationary P π) (t : ℕ) :
    Matrix.vecMul π (P ^ t) = π := by
  induction t with
  | zero => simp
  | succ n ih => rw [pow_succ, ← Matrix.vecMul_vecMul, ih, hπ.2]

private lemma output_bounds {V : Type*} [Fintype V] [DecidableEq V]
    (P : Matrix V V ℝ) (ν : (V → V) → ℝ) (hν : IsRandomMapRep P ν) (t : ℕ) (x y : V) :
    cftpOutputProb ν t y ≤ (P ^ t) x y ∧
    (P ^ t) x y - cftpOutputProb ν t y ≤ cftpNotCoalescedProb ν t := by
  have hw : ∀ F : Fin t → (V → V), (0 : ℝ) ≤ ∏ i, ν (F i) :=
    fun F => Finset.prod_nonneg fun i _ => hν.1.1 (F i)
  have hPt := compose_pow P ν hν t x y
  have hcnn : ∀ F : Fin t → (V → V),
      (0 : ℝ) ≤ (if ¬∀ a b : V, cftpCompose F a = cftpCompose F b then ∏ i, ν (F i) else 0) := by
    intro F
    by_cases h : ∀ a b : V, cftpCompose F a = cftpCompose F b
    · rw [if_neg (not_not_intro h)]
    · rw [if_pos h]
      exact hw F
  constructor
  · rw [← hPt]
    refine Finset.sum_le_sum fun F _ => ?_
    by_cases hall : ∀ z : V, cftpCompose F z = y
    · simp [hall, hall x]
    · simp only [hall, if_false]
      by_cases hx : cftpCompose F x = y
      · simp [hx, hw F]
      · simp [hx]
  · rw [← hPt]
    show (∑ F : Fin t → (V → V), (if cftpCompose F x = y then ∏ i, ν (F i) else 0))
        - (∑ F : Fin t → (V → V), (if ∀ z : V, cftpCompose F z = y then ∏ i, ν (F i) else 0))
        ≤ ∑ F : Fin t → (V → V),
            (if ¬∀ a b : V, cftpCompose F a = cftpCompose F b then ∏ i, ν (F i) else 0)
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_le_sum fun F _ => ?_
    by_cases hall : ∀ z : V, cftpCompose F z = y
    · rw [if_pos hall, if_pos (hall x), sub_self]
      exact hcnn F
    · rw [if_neg hall, sub_zero]
      by_cases hx : cftpCompose F x = y
      · rw [if_pos hx]
        have hnc : ¬∀ a b : V, cftpCompose F a = cftpCompose F b := by
          intro hc
          exact hall fun z => (hc z x).trans hx
        rw [if_pos hnc]
      · rw [if_neg hx]
        exact hcnn F

end MarkovMixing

open MarkovMixing

/-- **Propp–Wilson, correctness of coupling from the past** (LPW §22.2–22.3). -/
theorem solution {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (P : Matrix V V ℝ) (hP : IsStochastic P)
    (π : V → ℝ) (hπ : IsStationary P π)
    (ν : (V → V) → ℝ) (hν : IsRandomMapRep P ν)
    (hcoal : Filter.Tendsto (fun t => cftpNotCoalescedProb ν t)
      Filter.atTop (nhds 0)) (y : V) :
    Filter.Tendsto (fun t => cftpOutputProb ν t y)
      Filter.atTop (nhds (π y)) := by
  have hstat : ∀ t : ℕ, ∑ x : V, π x * ((P ^ t) x y) = π y := by
    intro t
    have h := congrFun (vecMul_pow_stationary hπ t) y
    simpa [Matrix.vecMul, dotProduct] using h
  have hup : ∀ t : ℕ, cftpOutputProb ν t y ≤ π y := by
    intro t
    rw [← hstat t]
    calc cftpOutputProb ν t y = ∑ x : V, π x * cftpOutputProb ν t y := by
          rw [← Finset.sum_mul, hπ.1.2, one_mul]
      _ ≤ ∑ x : V, π x * ((P ^ t) x y) :=
          Finset.sum_le_sum fun x _ =>
            mul_le_mul_of_nonneg_left (output_bounds P ν hν t x y).1 (hπ.1.1 x)
  have hlow : ∀ t : ℕ, π y - cftpNotCoalescedProb ν t ≤ cftpOutputProb ν t y := by
    intro t
    have hsum : (∑ x : V, π x * ((P ^ t) x y)) - (∑ x : V, π x * cftpOutputProb ν t y)
        ≤ ∑ x : V, π x * cftpNotCoalescedProb ν t := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_le_sum fun x _ => ?_
      rw [← mul_sub]
      exact mul_le_mul_of_nonneg_left (output_bounds P ν hν t x y).2 (hπ.1.1 x)
    rw [hstat t, ← Finset.sum_mul, hπ.1.2, one_mul, ← Finset.sum_mul, hπ.1.2, one_mul] at hsum
    linarith
  have h1 : Filter.Tendsto (fun t : ℕ => π y - cftpNotCoalescedProb ν t)
      Filter.atTop (nhds (π y)) := by
    have h := Filter.Tendsto.const_sub (π y) hcoal
    simpa using h
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le h1 tendsto_const_nhds hlow hup
