-- Prove2me | solution 1 for GreatCircleTrigPoly
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T00:27:49.760565+00:00
-- url     : https://prove2.me/submissions/5964f6fd-7a5b-4768-9f66-c93ded707fc5

module
public import Definitions.Def_PHarmonicPoly_TrigPolyMul
public import Definitions.Def_PHarmonicPoly_TrigPolyLinComb
public import Definitions.Def_PHarmonicPoly_GreatCircleTrigPoly
public import Theorems.Thm_TrigPolyLinComb
public import Theorems.Thm_TrigPolyMul


set_option autoImplicit false
@[expose] public section
public section
open MvPolynomial
theorem _root_.solution {n m : ℕ} {P : MvPolynomial (Fin n) ℝ}
    (hdeg : P.totalDegree ≤ m) (A B : EuclideanSpace ℝ (Fin n)) :
    TrigPolyLe m (fun t => MvPolynomial.eval
      (fun i => (Real.cos t • A + Real.sin t • B : EuclideanSpace ℝ (Fin n)) i) P) := by
  classical
  have htr : ∀ (N : ℕ) (f g : ℝ → ℝ), TrigPolyLe N f → (∀ t, g t = f t) →
      TrigPolyLe N g := by
    intro N f g hf hg
    obtain ⟨p, q, hp⟩ := hf
    exact ⟨p, q, fun t => (hg t).trans (hp t)⟩
  have hconst : ∀ (N : ℕ) (u : ℝ), TrigPolyLe N (fun _ => u) := by
    intro N u
    refine ⟨fun k => if k = 0 then u else 0, fun _ => 0, fun t => ?_⟩
    rw [Finset.sum_eq_single_of_mem 0 (Finset.mem_range.mpr (by omega))
      (fun k _ hk => by simp [hk])]
    simp
  have hmono : ∀ (N N' : ℕ) (f : ℝ → ℝ), TrigPolyLe N f → N ≤ N' →
      TrigPolyLe N' f := by
    intro N N' f hf hle
    obtain ⟨p, q, hp⟩ := hf
    refine ⟨fun k => if k ≤ N then p k else 0, fun k => if k ≤ N then q k else 0,
      fun t => ?_⟩
    rw [hp t]
    refine (Finset.sum_congr rfl ?_).trans
      (Finset.sum_subset (show Finset.range (N + 1) ⊆ Finset.range (N' + 1) from
        fun x hx => Finset.mem_range.mpr
          (by simp only [Finset.mem_range] at hx; omega)) ?_)
    · intro k hk
      simp only [Finset.mem_range] at hk
      simp only [if_pos (show k ≤ N by omega)]
    · intro k _ hk
      simp only [Finset.mem_range] at hk
      simp only [if_neg (show ¬ k ≤ N by omega), zero_mul, add_zero]
  have hsum : ∀ (N : ℕ) {ι : Type} (s : Finset ι) (F : ι → ℝ → ℝ),
      (∀ i ∈ s, TrigPolyLe N (F i)) →
      TrigPolyLe N (fun t => ∑ i ∈ s, F i t) := by
    intro N ι s
    induction s using Finset.induction_on with
    | empty => intro F _; exact htr _ _ _ (hconst N 0) (by simp)
    | insert i s hi ih =>
      intro F hF
      refine htr _ _ _ (TrigPolyLinComb (hF i (Finset.mem_insert_self i s))
        (ih F fun j hj => hF j (Finset.mem_insert_of_mem hj)) 1 1) (fun t => ?_)
      rw [Finset.sum_insert hi]
      ring
  have hg1 : ∀ i : Fin n, TrigPolyLe 1
      (fun t => (Real.cos t • A + Real.sin t • B : EuclideanSpace ℝ (Fin n)) i) := by
    intro i
    refine ⟨fun k => if k = 1 then A i else 0, fun k => if k = 1 then B i else 0,
      fun t => ?_⟩
    simp [Finset.sum_range_succ]
    ring
  have hpow : ∀ (f : ℝ → ℝ) (e : ℕ), TrigPolyLe 1 f →
      TrigPolyLe e (fun t => f t ^ e) := by
    intro f e hf
    induction e with
    | zero => exact htr _ _ _ (hconst 0 1) (by simp)
    | succ e ih => exact htr _ _ _ (TrigPolyMul ih hf) (fun t => by rw [pow_succ])
  have hprod : ∀ (s : Finset (Fin n)) (e : Fin n → ℕ),
      TrigPolyLe (∑ i ∈ s, e i) (fun t => ∏ i ∈ s,
        ((Real.cos t • A + Real.sin t • B : EuclideanSpace ℝ (Fin n)) i) ^ e i) := by
    intro s
    induction s using Finset.induction_on with
    | empty => intro e; exact htr _ _ _ (hconst 0 1) (by simp)
    | insert i s hi ih =>
      intro e
      rw [Finset.sum_insert hi]
      refine htr _ _ _ (TrigPolyMul (hpow _ (e i) (hg1 i)) (ih e)) (fun t => ?_)
      rw [Finset.prod_insert hi]
  refine htr _ _ _ (hsum m P.support
    (fun dd t => P.coeff dd * ∏ i,
      ((Real.cos t • A + Real.sin t • B : EuclideanSpace ℝ (Fin n)) i) ^ dd i) ?_)
    (fun t => by rw [MvPolynomial.eval_eq'])
  intro dd hdd
  have hdegsum : ∑ i, dd i ≤ m := by
    have h1 : (dd.sum fun _ e => e) ≤ P.totalDegree := MvPolynomial.le_totalDegree hdd
    rw [Finsupp.sum_fintype dd (fun _ e => e) (fun _ => rfl)] at h1
    omega
  exact htr _ _ _ (TrigPolyLinComb
    (hmono _ _ _ (hprod Finset.univ (fun i => dd i)) hdegsum)
    (hmono _ _ _ (hprod Finset.univ (fun i => dd i)) hdegsum)
    (P.coeff dd) 0) (fun t => by ring)
