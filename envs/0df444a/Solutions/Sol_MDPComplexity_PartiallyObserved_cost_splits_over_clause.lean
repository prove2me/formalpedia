-- Prove2me | solution 1 for MDPComplexity.PartiallyObserved.cost_splits_over_clause
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-02T05:32:44.08781+00:00
-- url     : https://prove2.me/submissions/0a42f80b-1eb1-494b-83bd-6532be10da72

import Definitions.Def_MDPComplexity_PartiallyObserved_Construction
import Mathlib.Tactic.Ring

open Finset
open MDPComplexity.PartiallyObserved

namespace MDPClauseCost

variable {S Z : Type} (M : POMDP S Z)

lemma obsHist_snoc {T : ℕ} (x : Fin (T + 1) → S) (s : S) (t : Fin (T + 1)) :
    M.obsHist (Fin.snoc x s) t.castSucc = M.obsHist x t := by
  unfold POMDP.obsHist
  congr 1
  funext k
  change M.obs (Fin.snoc (α := fun _ : Fin (T + 2) ↦ S)
    x s (Fin.castLE t.isLt.le k).castSucc) = _
  rw [Fin.snoc_castSucc]

lemma dec_snoc {T : ℕ} (π : M.Policy) (x : Fin (T + 1) → S) (s : S)
    (t : Fin (T + 1)) :
    HEq (M.dec π (Fin.snoc x s) t.castSucc) (M.dec π x t) := by
  unfold POMDP.dec
  rw [obsHist_snoc, Fin.snoc_castSucc]

lemma trajProb_snoc [DecidableEq S] {T : ℕ} (s₀ : S) (π : M.Policy)
    (x : Fin (T + 1) → S) (s : S) :
    M.trajProb s₀ π (T + 1) (Fin.snoc x s) =
      M.trajProb s₀ π T x *
        ((M.p (x (Fin.last T)) (M.dec π x (Fin.last T))) s).toReal := by
  unfold POMDP.trajProb
  rw [Fin.prod_univ_castSucc]
  have hstep (t : Fin (T + 1)) (s' : S) :
      (M.p (Fin.snoc (α := fun _ : Fin (T + 2) ↦ S) x s t.castSucc)
        (M.dec π (Fin.snoc x s) t.castSucc)) s' =
        (M.p (x t) (M.dec π x t)) s' := by
    unfold POMDP.dec
    rw [obsHist_snoc, Fin.snoc_castSucc]
  simp only [Fin.snoc_apply_zero, hstep]
  have hprod : (∏ i : Fin T,
      ((M.p (x i.castSucc) (M.dec π x i.castSucc))
        (Fin.snoc (α := fun _ : Fin (T + 2) ↦ S) x s i.castSucc.succ)).toReal) =
      ∏ i : Fin T, ((M.p (x i.castSucc) (M.dec π x i.castSucc)) (x i.succ)).toReal := by
    apply Finset.prod_congr rfl
    intro i _
    rw [show i.castSucc.succ = i.succ.castSucc from rfl, Fin.snoc_castSucc]
  rw [hprod]
  simp only [show (Fin.last T).succ = Fin.last (T + 1) from rfl, Fin.snoc_last]
  exact (mul_assoc (G := ℝ) _ _ _).symm

lemma pmf_sum_toReal [Fintype S] (p : PMF S) : ∑ s, (p s).toReal = 1 := by
  rw [← ENNReal.toReal_sum (fun s _ ↦ p.apply_ne_top s)]
  have h := p.tsum_coe
  rw [tsum_fintype] at h
  rw [h, ENNReal.toReal_one]

lemma sum_snoc [Fintype S] {T : ℕ} (f : (Fin (T + 2) → S) → ℝ) :
    ∑ y, f y = ∑ x : Fin (T + 1) → S, ∑ s, f (Fin.snoc x s) := by
  rw [← (Fin.snocEquiv (fun _ : Fin (T + 2) ↦ S)).sum_comp f]
  change (∑ z : S × (Fin (T + 1) → S), f (Fin.snoc z.2 z.1)) = _
  rw [Fintype.sum_prod_type, Finset.sum_comm]

lemma sum_trajProb_init [Fintype S] [DecidableEq S] {T : ℕ}
    (s₀ : S) (π : M.Policy) (f : (Fin (T + 1) → S) → ℝ) :
    ∑ y, M.trajProb s₀ π (T + 1) y * f (Fin.init y) =
      ∑ x, M.trajProb s₀ π T x * f x := by
  rw [sum_snoc]
  simp_rw [trajProb_snoc, Fin.init_snoc]
  conv_lhs =>
    enter [2, x, 2, s]
    rw [mul_right_comm]
  simp_rw [← Finset.mul_sum, pmf_sum_toReal, mul_one]

lemma sum_trajProb_prefix [Fintype S] [DecidableEq S] {k T : ℕ} (h : k ≤ T)
    (s₀ : S) (π : M.Policy) (f : (Fin (k + 1) → S) → ℝ) :
    ∑ y, M.trajProb s₀ π T y * f (fun t ↦ y (Fin.castLE (Nat.succ_le_succ h) t)) =
      ∑ x, M.trajProb s₀ π k x * f x := by
  induction T, h using Nat.le_induction with
  | base => rfl
  | succ T h ih =>
    have heq (y : Fin (T + 2) → S) :
        (fun t : Fin (k + 1) ↦ y (Fin.castLE (Nat.succ_le_succ (Nat.le_succ_of_le h)) t)) =
        (fun t ↦ Fin.init y (Fin.castLE (Nat.succ_le_succ h) t)) := rfl
    simp_rw [heq]
    exact (sum_trajProb_init M s₀ π
      (fun x : Fin (T + 1) → S ↦ f (fun t ↦ x (Fin.castLE (Nat.succ_le_succ h) t)))).trans ih

lemma trajProb_nonneg [DecidableEq S] (s₀ : S) (π : M.Policy) (T : ℕ)
    (x : Fin (T + 1) → S) : 0 ≤ M.trajProb s₀ π T x := by
  unfold POMDP.trajProb
  apply mul_nonneg
  · split_ifs <;> norm_num
  · exact Finset.prod_nonneg (fun _ _ ↦ ENNReal.toReal_nonneg)

lemma sum_first_step [Fintype S] [DecidableEq S] {T : ℕ} (hT : 1 ≤ T)
    (s₀ : S) (π : M.Policy) (f : S → ℝ) :
    ∑ x, M.trajProb s₀ π T x * f (x ⟨1, by omega⟩) =
      ∑ s, ((M.p s₀ (π [] (M.obs s₀))) s).toReal * f s := by
  have hprefix : (∑ x, M.trajProb s₀ π T x * f (x ⟨1, by omega⟩)) =
      ∑ x, M.trajProb s₀ π 1 x * f (x 1) :=
    sum_trajProb_prefix M hT s₀ π (fun x ↦ f (x 1))
  rw [hprefix, sum_snoc]
  simp_rw [trajProb_snoc]
  rw [Finset.sum_eq_single (fun _ ↦ s₀)]
  · have hs (s : S) : Fin.snoc (α := fun _ : Fin 2 ↦ S)
        (fun _ ↦ s₀) s 1 = s := by
      change Fin.snoc (α := fun _ : Fin 2 ↦ S) (fun _ ↦ s₀) s (Fin.last 1) = s
      exact Fin.snoc_last (n := 1) (α := fun _ : Fin 2 ↦ S) s (fun _ ↦ s₀)
    simp [POMDP.trajProb, POMDP.dec, POMDP.obsHist, hs]
  · intro x _ hx
    have hx0 : x 0 ≠ s₀ := by
      intro h
      apply hx
      funext i
      have hi : i = 0 := Fin.ext (by omega)
      simpa only [hi] using h
    simp [POMDP.trajProb, hx0]
  · simp

lemma first_transition_ne_zero [DecidableEq S] {T : ℕ} (hT : 1 ≤ T)
    (s₀ : S) (π : M.Policy) (x : Fin (T + 1) → S)
    (hx : M.trajProb s₀ π T x ≠ 0) :
    (M.p s₀ (π [] (M.obs s₀))) (x ⟨1, by omega⟩) ≠ 0 := by
  have hx0 : x 0 = s₀ := by
    by_contra h
    simp [POMDP.trajProb, h] at hx
  have hprod : (∏ t : Fin T,
      ((M.p (x t.castSucc) (M.dec π x t.castSucc)) (x t.succ)).toReal) ≠ 0 := by
    simpa [POMDP.trajProb, hx0] using hx
  have hfirst := Finset.prod_ne_zero_iff.mp hprod ⟨0, by omega⟩ (mem_univ _)
  have hr : ((M.p s₀ (π [] (M.obs s₀))) (x ⟨1, by omega⟩)).toReal ≠ 0 := by
    simp only [POMDP.dec, POMDP.obsHist, List.ofFn_zero] at hfirst
    change ((M.p (x 0) (π [] (M.obs (x 0)))) (x ⟨1, by omega⟩)).toReal ≠ 0 at hfirst
    cases hx0
    exact hfirst
  intro h
  exact hr (by rw [h]; rfl)

variable {n m : ℕ} (φ : QBF n m) (hm : 0 < m)

lemma lvlA'_eq_iff (i j : Fin m) (k : ℕ) :
    lvlA' (n := n) i k = lvlA' j k ↔ i = j := by
  unfold lvlA'
  split_ifs <;> simp

lemma initial_mass (π : (φ.toPOMDP hm).Policy) (i : Fin m) :
    (((φ.toPOMDP hm).p .s0 (π [] .s0)) (lvlA' i 0)).toReal = 1 / (m : ℝ) := by
  simp [QBF.toPOMDP, QBF.trans, PMF.map_apply, tsum_fintype, lvlA'_eq_iff,
    ENNReal.toReal_inv, one_div]

lemma first_clause (π : (φ.toPOMDP hm).Policy)
    (x : Fin (horizon n + 1) → St n m)
    (hx : (φ.toPOMDP hm).trajProb .s0 π (horizon n) x ≠ 0) :
    ∃ i : Fin m, x ⟨1, by unfold horizon; omega⟩ = lvlA' i 0 := by
  have h := first_transition_ne_zero (φ.toPOMDP hm)
    (by unfold horizon; omega) .s0 π x hx
  have hs : x ⟨1, by unfold horizon; omega⟩ ∈
      ((@PMF.uniformOfFintype (Fin m) _ ⟨⟨0, hm⟩⟩).map
        (fun i ↦ lvlA' (n := n) i 0)).support := h
  obtain ⟨i, _, hi⟩ := (PMF.mem_support_map_iff _ _ _).mp hs
  exact ⟨i, hi.symm⟩

lemma clause_mass (π : (φ.toPOMDP hm).Policy) (i : Fin m) :
    ∑ x ∈ univ.filter (fun x : Fin (horizon n + 1) → St n m ↦
        x ⟨1, by unfold horizon; omega⟩ = lvlA' i 0),
      (φ.toPOMDP hm).trajProb .s0 π (horizon n) x = 1 / (m : ℝ) := by
  have h := sum_first_step (φ.toPOMDP hm) (T := horizon n)
    (by unfold horizon; omega) .s0 π
    (fun s ↦ if s = lvlA' i 0 then 1 else 0)
  rw [Finset.sum_filter]
  simpa only [mul_ite, mul_one, mul_zero, sum_ite_eq', mem_univ,
    if_true, QBF.toPOMDP, St.obs, initial_mass] using h.trans
      (by simp only [mul_ite, mul_one, mul_zero, sum_ite_eq', mem_univ, if_true]
          exact initial_mass φ hm π i)

lemma trajCost_nonneg (π : (φ.toPOMDP hm).Policy) (T : ℕ)
    (x : Fin (T + 1) → St n m) : 0 ≤ (φ.toPOMDP hm).trajCost π T x := by
  unfold POMDP.trajCost
  apply sum_nonneg
  intro t _
  have hcost (z : Obs n m) (d : φ.Dec z) : 0 ≤ φ.cost z d := by
    cases z <;> simp [QBF.cost]
  exact hcost _ _

end MDPClauseCost

/-- §4, proof of Theorem 6 (p. 449): the transition from `s₀` "chooses" clause `C_i` by moving to
`A′_{i1}` with probability `1/m`; the expected cost is the sum over clauses of the partial
expectations over trajectories through `A′_{i1}` at time 1, each nonnegative, so it is zero iff
the cost is zero for every choice of clause. -/
theorem solution {n m : ℕ} (φ : QBF n m) (hm : 0 < m)
    (hqsat : φ.IsPaperQSAT)
    (π : (φ.toPOMDP hm).Policy) :
    (∀ i : Fin m,
      ∑ x ∈ Finset.univ.filter (fun x : Fin (horizon n + 1) → St n m =>
          x ⟨1, by unfold horizon; omega⟩ = lvlA' i 0),
        (φ.toPOMDP hm).trajProb .s0 π (horizon n) x = 1 / (m : ℝ)) ∧
    (φ.toPOMDP hm).expCost .s0 π (horizon n) =
      ∑ i : Fin m, ∑ x ∈ Finset.univ.filter (fun x : Fin (horizon n + 1) → St n m =>
          x ⟨1, by unfold horizon; omega⟩ = lvlA' i 0),
        (φ.toPOMDP hm).trajProb .s0 π (horizon n) x * (φ.toPOMDP hm).trajCost π (horizon n) x ∧
    ((φ.toPOMDP hm).expCost .s0 π (horizon n) = 0 ↔
      ∀ i : Fin m, ∑ x ∈ Finset.univ.filter (fun x : Fin (horizon n + 1) → St n m =>
          x ⟨1, by unfold horizon; omega⟩ = lvlA' i 0),
        (φ.toPOMDP hm).trajProb .s0 π (horizon n) x * (φ.toPOMDP hm).trajCost π (horizon n) x = 0)  := by
  classical
  have hn (x : Fin (horizon n + 1) → St n m) :
      0 ≤ (φ.toPOMDP hm).trajProb .s0 π (horizon n) x *
        (φ.toPOMDP hm).trajCost π (horizon n) x :=
    mul_nonneg (MDPClauseCost.trajProb_nonneg _ _ _ _ _)
      (MDPClauseCost.trajCost_nonneg φ hm π _ x)
  have hs : (φ.toPOMDP hm).expCost .s0 π (horizon n) =
      ∑ i : Fin m, ∑ x ∈ Finset.univ.filter (fun x : Fin (horizon n + 1) → St n m ↦
          x ⟨1, by unfold horizon; omega⟩ = lvlA' i 0),
        (φ.toPOMDP hm).trajProb .s0 π (horizon n) x *
          (φ.toPOMDP hm).trajCost π (horizon n) x := by
    unfold POMDP.expCost
    simp_rw [Finset.sum_filter]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro x _
    by_cases hx : (φ.toPOMDP hm).trajProb .s0 π (horizon n) x = 0
    · simp [hx]
    · obtain ⟨i, hi⟩ := MDPClauseCost.first_clause φ hm π x hx
      simp [hi, MDPClauseCost.lvlA'_eq_iff]
  refine ⟨MDPClauseCost.clause_mass φ hm π, hs, ?_⟩
  rw [hs]
  simpa only [Finset.mem_univ, forall_const] using
    (Finset.sum_eq_zero_iff_of_nonneg (fun i (_ : i ∈ (Finset.univ : Finset (Fin m))) ↦
      Finset.sum_nonneg (fun x _ ↦ hn x)))
