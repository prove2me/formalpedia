-- Prove2me | solution 1 for NahmiasPerishable.Inventory.m12
-- status  : ACCEPTED   (prove)
-- author  : @CGTMoyano
-- created : 2026-11-24T14:15:12.556637+00:00
-- url     : https://prove2.me/submissions/aad92da4-2de6-41a0-9d3e-0da54af1959d

import Definitions.Def_NahmiasPerishable_Inventory_Stationary

open MeasureTheory Set
open NahmiasPerishable.Inventory

namespace NahmiasM12

/-- Prefix sums of the age vector: the stock in the j oldest classes. -/
noncomputable def A {k : ℕ} (v : Fin k → ℝ) (j : ℕ) : ℝ := ∑ i : Fin k, if i.val < j then v i else 0

lemma A0 {k : ℕ} (v : Fin k → ℝ) : A v 0 = 0 := by simp [A]

lemma A_succ {k : ℕ} (v : Fin k → ℝ) (j : ℕ) (hj : j < k) : A v (j+1) = A v j + v ⟨j, hj⟩ := by
  have h : ∀ i : Fin k, (if i.val < j+1 then v i else 0)
      = (if i.val < j then v i else 0) + (if i = ⟨j, hj⟩ then v i else 0) := by
    intro i
    by_cases h1 : i.val < j
    · have h2 : i ≠ ⟨j, hj⟩ := by
        intro h; rw [h] at h1; exact lt_irrefl _ h1
      rw [if_pos h1, if_neg h2, if_pos (by omega), add_zero]
    · by_cases h2 : i = ⟨j, hj⟩
      · subst h2; rw [if_pos (Nat.lt_succ_self j), if_neg h1, if_pos rfl, zero_add]
      · have h3 : ¬ i.val < j+1 := by
          intro h; exact h2 (Fin.ext (by show i.val = j; omega))
        rw [if_neg h3, if_neg h1, if_neg h2, add_zero]
  unfold A
  rw [Finset.sum_congr rfl (fun i _ => h i), Finset.sum_add_distrib, Finset.sum_ite_eq']
  rw [if_pos (Finset.mem_univ _)]

lemma A_k {k : ℕ} (v : Fin k → ℝ) : A v k = ∑ i, v i := by
  unfold A; exact Finset.sum_congr rfl fun i _ => if_pos i.is_lt

lemma A_filter {k : ℕ} (v : Fin k → ℝ) (j : ℕ) :
    ∑ i ∈ Finset.univ.filter (fun i : Fin k => i.val ≤ j), v i = A v (j+1) := by
  unfold A; rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases h : i.val ≤ j
  · rw [if_pos h, if_pos (Nat.lt_succ_of_le h)]
  · rw [if_neg h, if_neg (by omega)]

lemma A_nonneg {k : ℕ} (v : Fin k → ℝ) (hv : ∀ i, 0 ≤ v i) (j : ℕ) : 0 ≤ A v j :=
  Finset.sum_nonneg fun i _ => by split_ifs; exacts [hv i, le_rfl]

lemma A_mono {k : ℕ} (v : Fin k → ℝ) (hv : ∀ i, 0 ≤ v i) {j j' : ℕ} (h : j ≤ j') :
    A v j ≤ A v j' := by
  refine Finset.sum_le_sum fun i _ => ?_
  by_cases h1 : i.val < j
  · rw [if_pos h1, if_pos (by omega)]
  · rw [if_neg h1]; split_ifs; exacts [hv i, le_rfl]

lemma total_eq {k : ℕ} (x : AgeState k) : total x = A x.1 k - x.2 := by
  rw [A_k]; rfl

lemma R1 (a u d : ℝ) (hu : 0 ≤ u) : pos (u - pos (d - a)) = max (a + u) d - max a d := by
  simp only [pos, max_def]; split_ifs <;> linarith

lemma step_coord_lt (k : ℕ) (S : ℝ) (x : AgeState k) (d : ℝ) (j : ℕ) (hj' : j < k)
    (hj : j + 1 < k) :
    (baseStep k S x d).1 ⟨j, hj'⟩ = pos (x.1 ⟨j+1, hj⟩ - pos (d + x.2 - A x.1 (j+1))) := by
  rw [← A_filter]
  simp only [baseStep, fifo, dif_pos hj]

lemma step_coord_last (k : ℕ) (S : ℝ) (x : AgeState k) (d : ℝ) (j : ℕ) (hj' : j < k)
    (hj : ¬ j + 1 < k) :
    (baseStep k S x d).1 ⟨j, hj'⟩ = pos (pos (S - total x) - pos (d - total x)) := by
  simp only [baseStep, fifo, dif_neg hj]

lemma step_snd (k : ℕ) (S : ℝ) (x : AgeState k) (d : ℝ) :
    (baseStep k S x d).2 = pos (d - total x - pos (S - total x)) := by
  simp only [baseStep, fifo, if_true]

lemma KL1 (k : ℕ) (S : ℝ) (x : AgeState k) (d : ℝ) (hv : ∀ i, 0 ≤ x.1 i) (hb : x.2 = 0) :
    ∀ j, j < k → A (baseStep k S x d).1 j = max (A x.1 (j+1)) d - max (A x.1 1) d := by
  intro j
  induction j with
  | zero => intro _; rw [A0]; simp
  | succ j ih =>
    intro hj
    have hj' : j < k := by omega
    rw [A_succ _ j hj', ih hj', step_coord_lt k S x d j hj' hj, hb, A_succ x.1 (j+1) hj,
      add_zero, R1 (A x.1 (j+1)) (x.1 ⟨j+1, hj⟩) d (hv _)]
    ring

lemma expired_pos (k : ℕ) (S : ℝ) (x : AgeState k) (d : ℝ) (hk : 0 < k) (hb : x.2 = 0) :
    baseExpired k S x d = max (A x.1 1) d - d := by
  have hA1 : A x.1 1 = x.1 ⟨0, hk⟩ := by
    have := A_succ x.1 0 hk
    rw [A0] at this
    simpa using this
  unfold baseExpired expires
  rw [if_neg (by omega), dif_pos hk, hb, hA1]
  simp only [pos, max_def]; split_ifs <;> linarith

lemma measurable_A {k : ℕ} (j : ℕ) : Measurable fun v : Fin k → ℝ => A v j := by
  unfold A
  refine Finset.measurable_sum _ fun i _ => ?_
  by_cases h : i.val < j
  · simp only [if_pos h]; exact measurable_pi_apply i
  · simp only [if_neg h]; exact measurable_const

lemma measurable_total {k : ℕ} : Measurable fun x : AgeState k => total x := by
  have h : (fun x : AgeState k => total x) = fun x => A x.1 k - x.2 := funext total_eq
  rw [h]
  exact ((measurable_A k).comp measurable_fst).sub measurable_snd

lemma measurable_pos' {α : Type*} [MeasurableSpace α] {f : α → ℝ} (hf : Measurable f) :
    Measurable fun a => pos (f a) := hf.max measurable_const

lemma measurable_baseStep (k : ℕ) (S : ℝ) :
    Measurable fun z : AgeState k × ℝ => baseStep k S z.1 z.2 := by
  have hx1 : ∀ i : Fin k, Measurable fun z : AgeState k × ℝ => z.1.1 i := fun i =>
    (measurable_pi_apply i).comp (measurable_fst.comp measurable_fst)
  have hb : Measurable fun z : AgeState k × ℝ => z.1.2 := measurable_snd.comp measurable_fst
  have hd : Measurable fun z : AgeState k × ℝ => z.2 := measurable_snd
  have htot : Measurable fun z : AgeState k × ℝ => total z.1 :=
    measurable_total.comp measurable_fst
  have hA : ∀ j, Measurable fun z : AgeState k × ℝ => A z.1.1 j := fun j =>
    (measurable_A j).comp (measurable_fst.comp measurable_fst)
  have hy : Measurable fun z : AgeState k × ℝ => pos (S - total z.1) :=
    measurable_pos' (measurable_const.sub htot)
  have h1 : Measurable fun z : AgeState k × ℝ => (baseStep k S z.1 z.2).1 := by
    refine measurable_pi_iff.2 fun i => ?_
    obtain ⟨j, hj'⟩ := i
    by_cases hj : j + 1 < k
    · have e : (fun z : AgeState k × ℝ => (baseStep k S z.1 z.2).1 ⟨j, hj'⟩)
          = fun z => pos (z.1.1 ⟨j+1, hj⟩ - pos (z.2 + z.1.2 - A z.1.1 (j+1))) :=
        funext fun z => step_coord_lt k S z.1 z.2 j hj' hj
      rw [e]
      exact measurable_pos' ((hx1 _).sub (measurable_pos' ((hd.add hb).sub (hA _))))
    · have e : (fun z : AgeState k × ℝ => (baseStep k S z.1 z.2).1 ⟨j, hj'⟩)
          = fun z => pos (pos (S - total z.1) - pos (z.2 - total z.1)) :=
        funext fun z => step_coord_last k S z.1 z.2 j hj' hj
      rw [e]
      exact measurable_pos' (hy.sub (measurable_pos' (hd.sub htot)))
  have h2 : Measurable fun z : AgeState k × ℝ => (baseStep k S z.1 z.2).2 := by
    have e : (fun z : AgeState k × ℝ => (baseStep k S z.1 z.2).2)
        = fun z => pos (z.2 - total z.1 - pos (S - total z.1)) :=
      funext fun z => step_snd k S z.1 z.2
    rw [e]
    exact measurable_pos' ((hd.sub htot).sub hy)
  exact h1.prodMk h2

lemma measurableSet_good (k : ℕ) (S : ℝ) :
    MeasurableSet {x : AgeState k | canonical true x ∧ total x ≤ S} := by
  have c0 : ∀ i : Fin k, Measurable fun x : AgeState k => x.1 i := fun i =>
    (measurable_pi_apply i).comp measurable_fst
  have c1 : Measurable fun x : AgeState k => x.2 := measurable_snd
  have p1 : Measurable fun x : AgeState k => ∀ i, 0 ≤ x.1 i :=
    Measurable.forall fun i => measurableSet_setOfPred.1 (measurableSet_le measurable_const (c0 i))
  have p2 : Measurable fun x : AgeState k => 0 ≤ x.2 :=
    measurableSet_setOfPred.1 (measurableSet_le measurable_const c1)
  have p3 : Measurable fun x : AgeState k => x.2 > 0 :=
    measurableSet_setOfPred.1 (measurableSet_lt measurable_const c1)
  have p4 : Measurable fun x : AgeState k => ∀ i, x.1 i = 0 :=
    Measurable.forall fun i =>
      measurableSet_setOfPred.1 (measurableSet_eq_fun (c0 i) measurable_const)
  have p5 : Measurable fun x : AgeState k => (true = false → x.2 = 0) :=
    Measurable.imp measurable_const
      (measurableSet_setOfPred.1 (measurableSet_eq_fun c1 measurable_const))
  have p6 : Measurable fun x : AgeState k => total x ≤ S :=
    measurableSet_setOfPred.1 (measurableSet_le measurable_total measurable_const)
  exact measurableSet_setOfPred.2 (((p1.and p2).and ((p3.imp p4).and p5)).and p6)

lemma bdd_integrable {X : Type*} [MeasurableSpace X] (m : Measure X) [IsFiniteMeasure m]
    (f : X → ℝ) (hf : Measurable f) (C : ℝ) (h : ∀ᵐ x ∂m, |f x| ≤ C) : Integrable f m :=
  Integrable.mono' (integrable_const C) hf.aestronglyMeasurable
    (h.mono fun x hx => by rw [Real.norm_eq_abs]; exact hx)

lemma R2' (a S d : ℝ) (ha : a ≤ S) : pos (pos (S - a) - pos (d - a)) = max S d - max a d := by
  simp only [pos, max_def]; split_ifs <;> linarith

/-- One period in max-plus form, acting on the positions of the age-class boundaries. -/
noncomputable def T (k : ℕ) (S d : ℝ) (b : ℕ → ℝ) : ℕ → ℝ :=
  fun j => if j < k then max (b (j+1)) (b 0 + d) else b 0 + max S d

/-- Canonical states with total stock at most S. -/
def Good (k : ℕ) (S : ℝ) (x : AgeState k) : Prop := canonical true x ∧ total x ≤ S

/-- The compact set of stock vectors. -/
def InK (k : ℕ) (S : ℝ) (v : Fin k → ℝ) : Prop := (∀ i, 0 ≤ v i) ∧ A v k ≤ S

lemma T_zero_ge (k : ℕ) (S d : ℝ) (b : ℕ → ℝ) : b 0 + d ≤ T k S d b 0 := by
  unfold T
  split_ifs
  · exact le_max_right _ _
  · linarith [le_max_right S d]

lemma step_A (k : ℕ) (S : ℝ) (x : AgeState k) (d : ℝ) (hv : ∀ i, 0 ≤ x.1 i) (hb : x.2 = 0)
    (hT : A x.1 k ≤ S) :
    ∀ j, j ≤ k → A (baseStep k S x d).1 j = T k S d (A x.1) j - T k S d (A x.1) 0 := by
  intro j hj
  rcases Nat.eq_zero_or_pos k with hk0 | hkpos
  · have hj0 : j = 0 := by omega
    rw [hj0, A0, sub_self]
  · have hT0 : T k S d (A x.1) 0 = max (A x.1 1) d := by
      simp only [T, if_pos hkpos, A0, zero_add]
    rw [hT0]
    rcases Nat.lt_or_ge j k with hjk | hjk
    · rw [KL1 k S x d hv hb j hjk]
      simp only [T, if_pos hjk, A0, zero_add]
    · have e : j = k := by omega
      have hk1 : k - 1 < k := by omega
      have hk2 : ¬ (k - 1) + 1 < k := by omega
      have e1 : k - 1 + 1 = k := by omega
      have h1 := A_succ (baseStep k S x d).1 (k-1) hk1
      have h2 := KL1 k S x d hv hb (k-1) hk1
      have h3 := step_coord_last k S x d (k-1) hk1 hk2
      rw [e1] at h1 h2
      rw [e, h1, h2, h3, total_eq, hb, sub_zero, R2' _ S d hT]
      simp only [T, if_neg (lt_irrefl k), A0, zero_add]
      ring

lemma step_exp (k : ℕ) (S : ℝ) (x : AgeState k) (d : ℝ) (hb : x.2 = 0) (hS : 0 ≤ S) :
    baseExpired k S x d = T k S d (A x.1) 0 - d := by
  rcases Nat.eq_zero_or_pos k with hk0 | hkpos
  · subst hk0
    unfold baseExpired
    rw [if_pos rfl, total_eq, hb, A0]
    simp only [T, lt_irrefl, if_false, A0, zero_add]
    simp only [pos, max_def]; split_ifs <;> linarith
  · rw [expired_pos k S x d hkpos hb]
    simp only [T, if_pos hkpos, A0, zero_add]

lemma good_v (k : ℕ) (S : ℝ) (hS : 0 ≤ S) (x : AgeState k) (hx : Good k S x) : InK k S x.1 := by
  obtain ⟨⟨⟨hv, hb⟩, hc, -⟩, ht⟩ := hx
  refine ⟨hv, ?_⟩
  rcases hb.eq_or_lt with h0 | hpos
  · rw [total_eq, ← h0, sub_zero] at ht
    exact ht
  · rw [A_k, Finset.sum_congr rfl fun i _ => hc hpos i, Finset.sum_const_zero]
    exact hS

lemma zero_good (k : ℕ) (S : ℝ) (v : Fin k → ℝ) (hv : InK k S v) : Good k S (v, 0) := by
  refine ⟨⟨⟨hv.1, le_rfl⟩, fun h => absurd h (lt_irrefl _), fun _ => rfl⟩, ?_⟩
  rw [total_eq]
  show A v k - 0 ≤ S
  rw [sub_zero]
  exact hv.2

/-- A backlog does not influence the next state or the expiration. -/
lemma norm_step (k : ℕ) (S : ℝ) (hS : 0 ≤ S) (x : AgeState k) (hx : Good k S x) (d : ℝ)
    (hd : 0 ≤ d) :
    baseStep k S x d = baseStep k S (x.1, 0) d ∧
      baseExpired k S x d = baseExpired k S (x.1, 0) d := by
  obtain ⟨⟨⟨hv, hb⟩, hc, -⟩, ht⟩ := hx
  rcases hb.eq_or_lt with h0 | hpos
  · have hx' : x = (x.1, 0) := Prod.ext rfl h0.symm
    rw [← hx']
    exact ⟨rfl, rfl⟩
  · have hv0 : ∀ i, x.1 i = 0 := hc hpos
    have hAk : A x.1 k = 0 := by
      rw [A_k, Finset.sum_congr rfl fun i _ => hv0 i, Finset.sum_const_zero]
    have ht1 : total x = - x.2 := by rw [total_eq, hAk]; ring
    have ht2 : total ((x.1, 0) : AgeState k) = 0 := by
      rw [total_eq]
      show A x.1 k - 0 = 0
      rw [hAk, sub_zero]
    constructor
    · apply Prod.ext
      · funext i
        obtain ⟨j, hj'⟩ := i
        by_cases hj : j + 1 < k
        · rw [step_coord_lt k S x d j hj' hj, step_coord_lt k S (x.1, 0) d j hj' hj]
          show pos (x.1 ⟨j+1, hj⟩ - _) = pos (x.1 ⟨j+1, hj⟩ - _)
          rw [hv0]
          simp only [pos, max_def]; split_ifs <;> linarith
        · rw [step_coord_last k S x d j hj' hj, step_coord_last k S (x.1, 0) d j hj' hj,
            ht1, ht2]
          simp only [pos, max_def]; split_ifs <;> linarith
      · rw [step_snd, step_snd, ht1, ht2]
        simp only [pos, max_def]; split_ifs <;> linarith
    · unfold baseExpired
      by_cases hk0 : k = 0
      · rw [if_pos hk0, if_pos hk0, ht1, ht2]
        show pos (pos (S - -x.2) - x.2 - d) = pos (pos (S - 0) - 0 - d)
        simp only [pos, max_def]; split_ifs <;> linarith
      · rw [if_neg hk0, if_neg hk0]
        have hk : 0 < k := Nat.pos_of_ne_zero hk0
        unfold expires
        rw [dif_pos hk, dif_pos hk]
        show pos (x.1 ⟨0, hk⟩ - (d + x.2)) = pos (x.1 ⟨0, hk⟩ - (d + 0))
        rw [hv0]
        simp only [pos, max_def]; split_ifs <;> linarith

lemma T0_le (k : ℕ) (S d : ℝ) (v : Fin k → ℝ) (hv : InK k S v) :
    T k S d (A v) 0 ≤ max S d := by
  unfold T
  split_ifs with h
  · rw [A0, zero_add, zero_add]
    exact max_le_max ((A_mono v hv.1 h).trans hv.2) le_rfl
  · rw [A0, zero_add]

lemma step_good0 (k : ℕ) (S : ℝ) (hS : 0 ≤ S) (v : Fin k → ℝ) (hv : InK k S v) (d : ℝ)
    (hd : 0 ≤ d) : Good k S (baseStep k S (v, 0) d) := by
  have hA := step_A k S (v, 0) d hv.1 rfl hv.2 k le_rfl
  have hTk : T k S d (A v) k = max S d := by
    simp only [T, if_neg (lt_irrefl k), A0, zero_add]
  have h0a := T_zero_ge k S d (A v)
  rw [A0, zero_add] at h0a
  have h0b := T0_le k S d v hv
  have hsnd : (baseStep k S (v, 0) d).2 = pos (d - S) := by
    rw [step_snd, total_eq]
    show pos (d - (A v k - 0) - pos (S - (A v k - 0))) = pos (d - S)
    have := hv.2
    simp only [pos, max_def]; split_ifs <;> linarith
  have hnn : ∀ i, 0 ≤ (baseStep k S (v, 0) d).1 i := by
    intro i
    obtain ⟨j, hj'⟩ := i
    by_cases hj : j + 1 < k
    · rw [step_coord_lt k S (v, 0) d j hj' hj]; exact le_max_right _ _
    · rw [step_coord_last k S (v, 0) d j hj' hj]; exact le_max_right _ _
  have hA' : A (baseStep k S (v, 0) d).1 k = max S d - T k S d (A v) 0 := by
    rw [← hTk]; exact hA
  refine ⟨⟨⟨hnn, ?_⟩, ?_, fun h => absurd h (by decide)⟩, ?_⟩
  · rw [hsnd]; exact le_max_right _ _
  · intro hpos i
    rw [hsnd] at hpos
    have hdS : S < d := by
      by_contra hcon
      rw [not_lt] at hcon
      simp only [pos, max_def] at hpos
      split_ifs at hpos <;> linarith
    have hz : A (baseStep k S (v, 0) d).1 k = 0 := by
      rw [hA']
      rw [max_eq_right hdS.le] at h0b ⊢
      linarith
    rw [A_k] at hz
    exact (Finset.sum_eq_zero_iff_of_nonneg fun i _ => hnn i).1 hz i (Finset.mem_univ i)
  · rw [total_eq, hA', hsnd]
    simp only [pos, max_def] at *
    split_ifs at * <;> linarith

/-- Shift equivariance of the max-plus step. -/
lemma T_shift (k : ℕ) (S d : ℝ) (b b' : ℕ → ℝ) (c : ℝ) (h : ∀ j, j ≤ k → b j = b' j + c) :
    ∀ j, T k S d b j = T k S d b' j + c := by
  intro j
  unfold T
  split_ifs with hj
  · rw [h (j+1) hj, h 0 (Nat.zero_le k), add_right_comm, max_add_add_right]
  · rw [h 0 (Nat.zero_le k)]; ring

lemma T_nonexp (k : ℕ) (S d : ℝ) (b b' : ℕ → ℝ) (C : ℝ) (h : ∀ j, j ≤ k → |b j - b' j| ≤ C) :
    ∀ j, |T k S d b j - T k S d b' j| ≤ C := by
  intro j
  unfold T
  split_ifs with hj
  · refine (abs_max_sub_max_le_max _ _ _ _).trans (max_le (h (j+1) hj) ?_)
    have := h 0 (Nat.zero_le k)
    rwa [add_sub_add_right_eq_sub]
  · have := h 0 (Nat.zero_le k)
    rwa [add_sub_add_right_eq_sub]

lemma T_convex (k : ℕ) (d : ℝ) (b : ℝ → ℕ → ℝ)
    (h : ∀ j, ConvexOn ℝ univ (fun S => b S j)) :
    ∀ j, ConvexOn ℝ univ (fun S => T k S d (b S) j) := by
  intro j
  by_cases hj : j < k
  · have e : (fun S => T k S d (b S) j) = fun S => max (b S (j+1)) (b S 0 + d) := by
      funext S; simp only [T, if_pos hj]
    rw [e]
    exact (h (j+1)).sup ((h 0).add_const d)
  · have e : (fun S => T k S d (b S) j) = fun S => b S 0 + max S d := by
      funext S; simp only [T, if_neg hj]
    rw [e]
    exact (h 0).add ((convexOn_id convex_univ).sup (convexOn_const d convex_univ))

lemma pos_nonneg' (z : ℝ) : 0 ≤ pos z := le_max_right _ _

/-- Retraction onto the set of admissible stock vectors. -/
noncomputable def proj (k : ℕ) (S : ℝ) (v : Fin k → ℝ) : Fin k → ℝ :=
  fun i => S / max S (∑ j, pos (v j)) * pos (v i)

lemma proj_mem (k : ℕ) (S : ℝ) (hS : 0 ≤ S) (v : Fin k → ℝ) : InK k S (proj k S v) := by
  have hm : 0 ≤ max S (∑ j, pos (v j)) := le_max_of_le_left hS
  refine ⟨fun i => mul_nonneg (div_nonneg hS hm) (pos_nonneg' _), ?_⟩
  rw [A_k]
  show ∑ i, S / max S (∑ j, pos (v j)) * pos (v i) ≤ S
  rw [← Finset.mul_sum]
  rcases hm.eq_or_lt with h0 | hpos
  · rw [← h0, div_zero, zero_mul]; exact hS
  · rw [div_mul_eq_mul_div, div_le_iff₀ hpos]
    exact mul_le_mul_of_nonneg_left (le_max_right _ _) hS

lemma proj_id (k : ℕ) (S : ℝ) (hS : 0 ≤ S) (v : Fin k → ℝ) (hv : InK k S v) :
    proj k S v = v := by
  have hp : ∀ i, pos (v i) = v i := fun i => max_eq_left (hv.1 i)
  have hs : ∑ j, pos (v j) = A v k := by
    rw [A_k]; exact Finset.sum_congr rfl fun i _ => hp i
  funext i
  show S / max S (∑ j, pos (v j)) * pos (v i) = v i
  rw [hs, max_eq_left hv.2, hp]
  rcases hS.eq_or_lt with h0 | hpos
  · have hz : A v k = 0 := le_antisymm (by rw [h0]; exact hv.2) (A_nonneg v hv.1 k)
    rw [A_k] at hz
    rw [(Finset.sum_eq_zero_iff_of_nonneg fun i _ => hv.1 i).1 hz i (Finset.mem_univ i), mul_zero]
  · rw [div_self hpos.ne', one_mul]

/-- The stock dynamics, made total by the retraction and the positive part of the demand. -/
noncomputable def stepC (k : ℕ) (S : ℝ) (v : Fin k → ℝ) (d : ℝ) : Fin k → ℝ :=
  (baseStep k S (proj k S v, 0) (pos d)).1

noncomputable def expC (k : ℕ) (S : ℝ) (v : Fin k → ℝ) (d : ℝ) : ℝ :=
  baseExpired k S (proj k S v, 0) (pos d)

lemma stepC_mem (k : ℕ) (S : ℝ) (hS : 0 ≤ S) (v : Fin k → ℝ) (d : ℝ) :
    InK k S (stepC k S v d) :=
  good_v k S hS _ (step_good0 k S hS _ (proj_mem k S hS v) _ (pos_nonneg' d))

lemma stepC_proj (k : ℕ) (S : ℝ) (hS : 0 ≤ S) (v : Fin k → ℝ) (d : ℝ) :
    stepC k S (proj k S v) d = stepC k S v d := by
  unfold stepC; rw [proj_id k S hS _ (proj_mem k S hS v)]

lemma expC_proj (k : ℕ) (S : ℝ) (hS : 0 ≤ S) (v : Fin k → ℝ) (d : ℝ) :
    expC k S (proj k S v) d = expC k S v d := by
  unfold expC; rw [proj_id k S hS _ (proj_mem k S hS v)]

lemma stepC_A (k : ℕ) (S : ℝ) (hS : 0 ≤ S) (v : Fin k → ℝ) (hv : InK k S v) (d : ℝ) :
    ∀ j, j ≤ k → A (stepC k S v d) j = T k S (pos d) (A v) j - T k S (pos d) (A v) 0 := by
  unfold stepC; rw [proj_id k S hS v hv]
  exact step_A k S (v, 0) (pos d) hv.1 rfl hv.2

lemma expC_eq (k : ℕ) (S : ℝ) (hS : 0 ≤ S) (v : Fin k → ℝ) (hv : InK k S v) (d : ℝ) :
    expC k S v d = T k S (pos d) (A v) 0 - pos d := by
  unfold expC; rw [proj_id k S hS v hv]
  exact step_exp k S (v, 0) (pos d) rfl hS

lemma expC_bound (k : ℕ) (S : ℝ) (hS : 0 ≤ S) (v : Fin k → ℝ) (d : ℝ) :
    0 ≤ expC k S v d ∧ expC k S v d ≤ S := by
  rw [← expC_proj k S hS, expC_eq k S hS _ (proj_mem k S hS v)]
  have h1 := T_zero_ge k S (pos d) (A (proj k S v))
  rw [A0, zero_add] at h1
  have h2 := T0_le k S (pos d) _ (proj_mem k S hS v)
  have h3 : max S (pos d) ≤ S + pos d := max_le (by linarith [pos_nonneg' d]) (by linarith)
  constructor <;> linarith

/-- Cumulative expiration over n periods. -/
noncomputable def Cum (k : ℕ) (S : ℝ) : (n : ℕ) → (Fin k → ℝ) → (Fin n → ℝ) → ℝ
  | 0, _, _ => 0
  | n+1, v, d => expC k S v (d 0) + Cum k S n (stepC k S v (d 0)) (Fin.tail d)

/-- The n-period max-plus evolution. -/
noncomputable def Bv (k : ℕ) (S : ℝ) : (n : ℕ) → (Fin n → ℝ) → (ℕ → ℝ) → ℕ → ℝ
  | 0, _, b => b
  | n+1, d, b => Bv k S n (Fin.tail d) (T k S (pos (d 0)) b)

lemma Bv_shift (k : ℕ) (S : ℝ) : ∀ (n : ℕ) (d : Fin n → ℝ) (b b' : ℕ → ℝ) (c : ℝ),
    (∀ j, j ≤ k → b j = b' j + c) → ∀ j, j ≤ k → Bv k S n d b j = Bv k S n d b' j + c := by
  intro n
  induction n with
  | zero => intro d b b' c h j hj; exact h j hj
  | succ n ih =>
    intro d b b' c h j hj
    show Bv k S n (Fin.tail d) (T k S (pos (d 0)) b) j =
      Bv k S n (Fin.tail d) (T k S (pos (d 0)) b') j + c
    exact ih (Fin.tail d) _ _ c (fun j _ => T_shift k S _ b b' c h j) j hj

lemma Bv_nonexp (k : ℕ) (S : ℝ) : ∀ (n : ℕ) (d : Fin n → ℝ) (b b' : ℕ → ℝ) (C : ℝ),
    (∀ j, j ≤ k → |b j - b' j| ≤ C) → ∀ j, j ≤ k → |Bv k S n d b j - Bv k S n d b' j| ≤ C := by
  intro n
  induction n with
  | zero => intro d b b' C h j hj; exact h j hj
  | succ n ih =>
    intro d b b' C h j hj
    show |Bv k S n (Fin.tail d) (T k S (pos (d 0)) b) j -
      Bv k S n (Fin.tail d) (T k S (pos (d 0)) b') j| ≤ C
    exact ih (Fin.tail d) _ _ C (fun j _ => T_nonexp k S _ b b' C h j) j hj

lemma Bv_convex (k : ℕ) : ∀ (n : ℕ) (d : Fin n → ℝ) (b : ℝ → ℕ → ℝ),
    (∀ j, ConvexOn ℝ univ (fun S => b S j)) →
      ∀ j, ConvexOn ℝ univ (fun S => Bv k S n d (b S) j) := by
  intro n
  induction n with
  | zero => intro d b h j; exact h j
  | succ n ih =>
    intro d b h j
    show ConvexOn ℝ univ (fun S => Bv k S n (Fin.tail d) (T k S (pos (d 0)) (b S)) j)
    exact ih (Fin.tail d) (fun S => T k S (pos (d 0)) (b S)) (T_convex k _ b h) j

/-- The cumulative expiration is the displacement of the oldest boundary minus the demand. -/
lemma Cum_eq (k : ℕ) (S : ℝ) (hS : 0 ≤ S) : ∀ (n : ℕ) (v : Fin k → ℝ), InK k S v →
    ∀ d : Fin n → ℝ, Cum k S n v d = Bv k S n d (A v) 0 - ∑ i, pos (d i) := by
  intro n
  induction n with
  | zero =>
    intro v hv d
    show (0 : ℝ) = A v 0 - ∑ i : Fin 0, pos (d i)
    rw [A0]; simp
  | succ n ih =>
    intro v hv d
    show expC k S v (d 0) + Cum k S n (stepC k S v (d 0)) (Fin.tail d) =
      Bv k S n (Fin.tail d) (T k S (pos (d 0)) (A v)) 0 - ∑ i, pos (d i)
    have hsh := Bv_shift k S n (Fin.tail d) (T k S (pos (d 0)) (A v)) (A (stepC k S v (d 0)))
      (T k S (pos (d 0)) (A v) 0)
      (fun j hj => by rw [stepC_A k S hS v hv (d 0) j hj]; ring) 0 (Nat.zero_le k)
    rw [ih _ (stepC_mem k S hS v (d 0)) (Fin.tail d), expC_eq k S hS v hv, hsh,
      Fin.sum_univ_succ]
    simp only [Fin.tail]
    ring

lemma Cum_bound (k : ℕ) (S : ℝ) (hS : 0 ≤ S) : ∀ (n : ℕ) (v : Fin k → ℝ) (d : Fin n → ℝ),
    0 ≤ Cum k S n v d ∧ Cum k S n v d ≤ n * S := by
  intro n
  induction n with
  | zero =>
    intro v d
    show (0 : ℝ) ≤ 0 ∧ (0 : ℝ) ≤ ((0 : ℕ) : ℝ) * S
    simp
  | succ n ih =>
    intro v d
    show 0 ≤ expC k S v (d 0) + Cum k S n (stepC k S v (d 0)) (Fin.tail d) ∧
      expC k S v (d 0) + Cum k S n (stepC k S v (d 0)) (Fin.tail d) ≤ ((n + 1 : ℕ) : ℝ) * S
    have h1 := expC_bound k S hS v (d 0)
    have h2 := ih (stepC k S v (d 0)) (Fin.tail d)
    push_cast
    constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

lemma Cum_abs (k : ℕ) (S : ℝ) (hS : 0 ≤ S) (n : ℕ) (v : Fin k → ℝ) (d : Fin n → ℝ) :
    |Cum k S n v d| ≤ n * S := by
  have h := Cum_bound k S hS n v d
  rw [abs_of_nonneg h.1]; exact h.2

lemma Cum_proj (k : ℕ) (S : ℝ) (hS : 0 ≤ S) (n : ℕ) (v : Fin k → ℝ) (d : Fin n → ℝ) :
    Cum k S n (proj k S v) d = Cum k S n v d := by
  cases n with
  | zero => rfl
  | succ n =>
    show expC k S (proj k S v) (d 0) + Cum k S n (stepC k S (proj k S v) (d 0)) (Fin.tail d) =
      expC k S v (d 0) + Cum k S n (stepC k S v (d 0)) (Fin.tail d)
    rw [expC_proj k S hS, stepC_proj k S hS]

/-- Two starting states lead to cumulative expirations differing by at most S. -/
lemma Cum_diff (k : ℕ) (S : ℝ) (hS : 0 ≤ S) (n : ℕ) (v v' : Fin k → ℝ) (d : Fin n → ℝ) :
    |Cum k S n v d - Cum k S n v' d| ≤ S := by
  have h1 := proj_mem k S hS v
  have h2 := proj_mem k S hS v'
  rw [← Cum_proj k S hS n v, ← Cum_proj k S hS n v', Cum_eq k S hS n _ h1, Cum_eq k S hS n _ h2,
    sub_sub_sub_cancel_right]
  refine Bv_nonexp k S n d _ _ S (fun j hj => ?_) 0 (Nat.zero_le k)
  have a1 := A_nonneg _ h1.1 j
  have a2 := A_nonneg _ h2.1 j
  have a3 := (A_mono _ h1.1 hj).trans h1.2
  have a4 := (A_mono _ h2.1 hj).trans h2.2
  exact abs_sub_le_iff.2 ⟨by linarith, by linarith⟩

lemma zero_mem (k : ℕ) (S : ℝ) (hS : 0 ≤ S) : InK k S (0 : Fin k → ℝ) := by
  refine ⟨fun i => le_rfl, ?_⟩
  rw [A_k]; simpa using hS

/-- Starting from the empty state, the cumulative expiration is convex in the level S. -/
lemma Cum_convex (k : ℕ) (n : ℕ) (d : Fin n → ℝ) (S1 S2 : ℝ) (h1 : 0 ≤ S1) (h2 : 0 ≤ S2)
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    Cum k (a * S1 + b * S2) n 0 d ≤ a * Cum k S1 n 0 d + b * Cum k S2 n 0 d := by
  have hS : 0 ≤ a * S1 + b * S2 := by positivity
  rw [Cum_eq k _ hS n 0 (zero_mem k _ hS), Cum_eq k S1 h1 n 0 (zero_mem k S1 h1),
    Cum_eq k S2 h2 n 0 (zero_mem k S2 h2)]
  have hc := Bv_convex k n d (fun _ => A (0 : Fin k → ℝ)) (fun j => convexOn_const _ convex_univ) 0
  have h := hc.2 (mem_univ S1) (mem_univ S2) ha hb hab
  simp only [smul_eq_mul] at h
  have e : a * (∑ i, pos (d i)) + b * (∑ i, pos (d i)) = ∑ i, pos (d i) := by
    rw [← add_mul, hab, one_mul]
  linarith

lemma continuous_A {k : ℕ} (j : ℕ) : Continuous fun v : Fin k → ℝ => A v j := by
  unfold A
  refine continuous_finsetSum _ fun i _ => ?_
  by_cases h : i.val < j
  · simp only [if_pos h]; exact continuous_apply i
  · simp only [if_neg h]; exact continuous_const

lemma continuous_proj (k : ℕ) (S : ℝ) (hS : 0 ≤ S) : Continuous (proj k S) := by
  rcases hS.eq_or_lt with h0 | hpos
  · have e : proj k S = fun _ => fun _ => 0 := by
      funext v i
      show S / max S (∑ j, pos (v j)) * pos (v i) = 0
      rw [← h0, zero_div, zero_mul]
    rw [e]; exact continuous_const
  · refine continuous_pi fun i => ?_
    have hs : Continuous fun v : Fin k → ℝ => ∑ j, pos (v j) :=
      continuous_finsetSum _ fun j _ => (continuous_apply j).max continuous_const
    show Continuous fun v : Fin k → ℝ => S / max S (∑ j, pos (v j)) * pos (v i)
    exact (continuous_const.div (continuous_const.max hs)
      fun v => (lt_max_of_lt_left hpos).ne').mul ((continuous_apply i).max continuous_const)

lemma continuous_baseStep_fst (k : ℕ) (S d : ℝ) :
    Continuous fun x : AgeState k => (baseStep k S x d).1 := by
  have htot : Continuous fun x : AgeState k => total x := by
    have h : (fun x : AgeState k => total x) = fun x => A x.1 k - x.2 := funext total_eq
    rw [h]
    exact ((continuous_A k).comp continuous_fst).sub continuous_snd
  refine continuous_pi fun i => ?_
  obtain ⟨j, hj'⟩ := i
  by_cases hj : j + 1 < k
  · have e : (fun x : AgeState k => (baseStep k S x d).1 ⟨j, hj'⟩)
        = fun x => pos (x.1 ⟨j+1, hj⟩ - pos (d + x.2 - A x.1 (j+1))) :=
      funext fun x => step_coord_lt k S x d j hj' hj
    rw [e]
    exact (((continuous_apply _).comp continuous_fst).sub
      (((continuous_const.add continuous_snd).sub
        ((continuous_A (j+1)).comp continuous_fst)).max continuous_const)).max continuous_const
  · have e : (fun x : AgeState k => (baseStep k S x d).1 ⟨j, hj'⟩)
        = fun x => pos (pos (S - total x) - pos (d - total x)) :=
      funext fun x => step_coord_last k S x d j hj' hj
    rw [e]
    exact (((continuous_const.sub htot).max continuous_const).sub
      ((continuous_const.sub htot).max continuous_const)).max continuous_const

lemma continuous_stepC (k : ℕ) (S : ℝ) (hS : 0 ≤ S) (d : ℝ) :
    Continuous fun v : Fin k → ℝ => stepC k S v d :=
  (continuous_baseStep_fst k S (pos d)).comp ((continuous_proj k S hS).prodMk continuous_const)

lemma measurable_proj (k : ℕ) (S : ℝ) (hS : 0 ≤ S) : Measurable (proj k S) :=
  (continuous_proj k S hS).measurable

/-- The embedding of a stock vector and a demand into the state space. -/
noncomputable def emb (k : ℕ) (S : ℝ) (p : (Fin k → ℝ) × ℝ) : AgeState k × ℝ :=
  ((proj k S p.1, 0), pos p.2)

lemma measurable_emb (k : ℕ) (S : ℝ) (hS : 0 ≤ S) : Measurable (emb k S) := by
  have hp1 : Measurable fun p : (Fin k → ℝ) × ℝ => proj k S p.1 :=
    (measurable_proj k S hS).comp measurable_fst
  have hd : Measurable fun p : (Fin k → ℝ) × ℝ => pos p.2 := measurable_pos' measurable_snd
  exact (hp1.prodMk measurable_const).prodMk hd

lemma measurable_stepC (k : ℕ) (S : ℝ) (hS : 0 ≤ S) :
    Measurable fun p : (Fin k → ℝ) × ℝ => stepC k S p.1 p.2 := by
  have h1 : Measurable fun z : AgeState k × ℝ => (baseStep k S z.1 z.2).1 :=
    (measurable_baseStep k S).fst
  have e : (fun p : (Fin k → ℝ) × ℝ => stepC k S p.1 p.2)
      = fun p => (baseStep k S (emb k S p).1 (emb k S p).2).1 := by
    funext p; simp only [stepC, emb]
  rw [e]
  exact h1.comp (measurable_emb k S hS)

lemma measurable_baseExpired (k : ℕ) (S : ℝ) :
    Measurable fun z : AgeState k × ℝ => baseExpired k S z.1 z.2 := by
  by_cases hk : k = 0
  · have e : (fun z : AgeState k × ℝ => baseExpired k S z.1 z.2)
        = fun z => pos (pos (S - total z.1) - z.1.2 - z.2) := by
      funext z; simp only [baseExpired, if_pos hk]
    rw [e]
    exact measurable_pos' (((measurable_pos' (measurable_const.sub
      (measurable_total.comp measurable_fst))).sub (measurable_snd.comp measurable_fst)).sub
        measurable_snd)
  · have hk' : 0 < k := Nat.pos_of_ne_zero hk
    have e : (fun z : AgeState k × ℝ => baseExpired k S z.1 z.2)
        = fun z => pos (z.1.1 ⟨0, hk'⟩ - (z.2 + z.1.2)) := by
      funext z; simp only [baseExpired, if_neg hk, expires, dif_pos hk']
    rw [e]
    exact measurable_pos' (((measurable_pi_apply _).comp (measurable_fst.comp measurable_fst)).sub
      (measurable_snd.add (measurable_snd.comp measurable_fst)))

lemma measurable_expC (k : ℕ) (S : ℝ) (hS : 0 ≤ S) :
    Measurable fun p : (Fin k → ℝ) × ℝ => expC k S p.1 p.2 := by
  have e : (fun p : (Fin k → ℝ) × ℝ => expC k S p.1 p.2)
      = fun p => baseExpired k S (emb k S p).1 (emb k S p).2 := by
    funext p; simp only [expC, emb]
  rw [e]
  exact (measurable_baseExpired k S).comp (measurable_emb k S hS)

lemma measurable_Cum (k : ℕ) (S : ℝ) (hS : 0 ≤ S) : ∀ n : ℕ,
    Measurable fun p : (Fin k → ℝ) × (Fin n → ℝ) => Cum k S n p.1 p.2 := by
  intro n
  induction n with
  | zero =>
    show Measurable fun _ : (Fin k → ℝ) × (Fin 0 → ℝ) => (0 : ℝ)
    exact measurable_const
  | succ n ih =>
    show Measurable fun p : (Fin k → ℝ) × (Fin (n+1) → ℝ) =>
      expC k S p.1 (p.2 0) + Cum k S n (stepC k S p.1 (p.2 0)) (Fin.tail p.2)
    have h0 : Measurable fun p : (Fin k → ℝ) × (Fin (n+1) → ℝ) => (p.1, p.2 0) :=
      measurable_fst.prodMk ((measurable_pi_apply 0).comp measurable_snd)
    have ht : Measurable fun p : (Fin k → ℝ) × (Fin (n+1) → ℝ) => Fin.tail p.2 :=
      measurable_pi_lambda _ fun i => (measurable_pi_apply i.succ).comp measurable_snd
    exact ((measurable_expC k S hS).comp h0).add
      (ih.comp (((measurable_stepC k S hS).comp h0).prodMk ht))

section Core

variable (μ : Measure ℝ) [IsProbabilityMeasure μ]

lemma meas_cons {n : ℕ} {Φ : (Fin (n + 1) → ℝ) → ℝ} (hΦ : Measurable Φ) :
    Measurable (fun z : ℝ × (Fin n → ℝ) => Φ (Fin.cons z.1 z.2)) := by
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0
  have heq : ∀ z : ℝ × (Fin n → ℝ), e.symm z = Fin.cons z.1 z.2 := by
    intro z
    simp [e, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv, Fin.insertNth_zero']
  have h : (fun z : ℝ × (Fin n → ℝ) => Φ (Fin.cons z.1 z.2)) = fun z => Φ (e.symm z) :=
    funext fun z => by rw [heq]
  rw [h]
  exact hΦ.comp e.symm.measurable

lemma integral_cons {n : ℕ} {Φ : (Fin (n + 1) → ℝ) → ℝ}
    (hint : Integrable (fun z : ℝ × (Fin n → ℝ) => Φ (Fin.cons z.1 z.2))
      (μ.prod (Measure.pi (fun _ : Fin n => μ)))) :
    ∫ s, Φ s ∂(Measure.pi (fun _ : Fin (n + 1) => μ))
      = ∫ x, ∫ s', Φ (Fin.cons x s') ∂(Measure.pi (fun _ : Fin n => μ)) ∂μ := by
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0
  have mp : MeasurePreserving e (Measure.pi (fun _ : Fin (n + 1) => μ))
      (μ.prod (Measure.pi (fun _ : Fin n => μ))) :=
    measurePreserving_piFinSuccAbove (fun _ => μ) 0
  have heq : ∀ z : ℝ × (Fin n → ℝ), e.symm z = Fin.cons z.1 z.2 := by
    intro z
    simp [e, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv, Fin.insertNth_zero']
  calc ∫ s, Φ s ∂(Measure.pi (fun _ : Fin (n + 1) => μ))
      = ∫ z, Φ (e.symm z) ∂(μ.prod (Measure.pi (fun _ : Fin n => μ))) :=
        ((mp.symm e).integral_comp' Φ).symm
    _ = ∫ z, Φ (Fin.cons z.1 z.2) ∂(μ.prod (Measure.pi (fun _ : Fin n => μ))) := by
        simp only [heq]
    _ = ∫ x, ∫ s', Φ (Fin.cons x s') ∂(Measure.pi (fun _ : Fin n => μ)) ∂μ :=
        integral_prod _ hint

/-- Expected cumulative expiration over n periods from the stock vector v. -/
noncomputable def G (k : ℕ) (S : ℝ) (n : ℕ) (v : Fin k → ℝ) : ℝ :=
  ∫ d, Cum k S n v d ∂(Measure.pi fun _ : Fin n => μ)

lemma measurable_Cum_right (k : ℕ) (S : ℝ) (hS : 0 ≤ S) (n : ℕ) (v : Fin k → ℝ) :
    Measurable fun d : Fin n → ℝ => Cum k S n v d :=
  (measurable_Cum k S hS n).comp measurable_prodMk_left

lemma integrable_Cum (k : ℕ) (S : ℝ) (hS : 0 ≤ S) (n : ℕ) (v : Fin k → ℝ) :
    Integrable (fun d : Fin n → ℝ => Cum k S n v d) (Measure.pi fun _ : Fin n => μ) :=
  bdd_integrable _ _ (measurable_Cum_right k S hS n v) (n * S)
    (ae_of_all _ fun d => Cum_abs k S hS n v d)

lemma Cum_cons (k : ℕ) (S : ℝ) (n : ℕ) (v : Fin k → ℝ) (x : ℝ) (s : Fin n → ℝ) :
    Cum k S (n+1) v (Fin.cons x s) = expC k S v x + Cum k S n (stepC k S v x) s := by
  show expC k S v ((Fin.cons x s : Fin (n+1) → ℝ) 0)
      + Cum k S n (stepC k S v ((Fin.cons x s : Fin (n+1) → ℝ) 0))
        (Fin.tail (Fin.cons x s : Fin (n+1) → ℝ)) = _
  rw [Fin.cons_zero, Fin.tail_cons]

omit [IsProbabilityMeasure μ] in
lemma G_zero (k : ℕ) (S : ℝ) (v : Fin k → ℝ) : G μ k S 0 v = 0 := by
  show ∫ _d : Fin 0 → ℝ, (0 : ℝ) ∂(Measure.pi fun _ : Fin 0 => μ) = 0
  exact integral_zero _ _

lemma G_succ (k : ℕ) (S : ℝ) (hS : 0 ≤ S) (n : ℕ) (v : Fin k → ℝ) :
    G μ k S (n+1) v = ∫ x, (expC k S v x + G μ k S n (stepC k S v x)) ∂μ := by
  have hint : Integrable (fun z : ℝ × (Fin n → ℝ) => Cum k S (n+1) v (Fin.cons z.1 z.2))
      (μ.prod (Measure.pi (fun _ : Fin n => μ))) :=
    bdd_integrable _ _ (meas_cons (measurable_Cum_right k S hS (n+1) v)) ((n + 1 : ℕ) * S)
      (ae_of_all _ fun z => Cum_abs k S hS (n+1) v _)
  unfold G
  rw [integral_cons μ hint]
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  show ∫ s', Cum k S (n+1) v (Fin.cons x s') ∂(Measure.pi fun _ : Fin n => μ)
    = expC k S v x + ∫ d, Cum k S n (stepC k S v x) d ∂(Measure.pi fun _ : Fin n => μ)
  simp_rw [Cum_cons]
  rw [integral_add (integrable_const _) (integrable_Cum μ k S hS n _), integral_const]
  simp

lemma measurable_G (k : ℕ) (S : ℝ) (hS : 0 ≤ S) (n : ℕ) : Measurable (G μ k S n) := by
  have h := (measurable_Cum k S hS n).stronglyMeasurable.integral_prod_right'
    (ν := Measure.pi fun _ : Fin n => μ)
  exact h.measurable

lemma pi_real_univ (n : ℕ) : (Measure.pi fun _ : Fin n => μ).real univ = 1 := by simp

lemma G_abs (k : ℕ) (S : ℝ) (hS : 0 ≤ S) (n : ℕ) (v : Fin k → ℝ) : |G μ k S n v| ≤ n * S := by
  have h := norm_integral_le_of_norm_le_const (μ := Measure.pi fun _ : Fin n => μ)
    (f := fun d : Fin n → ℝ => Cum k S n v d) (C := n * S)
    (ae_of_all _ fun d => by rw [Real.norm_eq_abs]; exact Cum_abs k S hS n v d)
  rw [Real.norm_eq_abs, pi_real_univ, mul_one] at h
  exact h

lemma G_diff (k : ℕ) (S : ℝ) (hS : 0 ≤ S) (n : ℕ) (v v' : Fin k → ℝ) :
    |G μ k S n v - G μ k S n v'| ≤ S := by
  have h := norm_integral_le_of_norm_le_const (μ := Measure.pi fun _ : Fin n => μ)
    (f := fun d : Fin n → ℝ => Cum k S n v d - Cum k S n v' d) (C := S)
    (ae_of_all _ fun d => by rw [Real.norm_eq_abs]; exact Cum_diff k S hS n v v' d)
  rw [Real.norm_eq_abs, pi_real_univ, mul_one,
    integral_sub (integrable_Cum μ k S hS n v) (integrable_Cum μ k S hS n v')] at h
  exact h

lemma G_convex (k : ℕ) (n : ℕ) (S1 S2 : ℝ) (h1 : 0 ≤ S1) (h2 : 0 ≤ S2)
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    G μ k (a * S1 + b * S2) n 0 ≤ a * G μ k S1 n 0 + b * G μ k S2 n 0 := by
  have hS : 0 ≤ a * S1 + b * S2 := by positivity
  unfold G
  rw [← integral_const_mul, ← integral_const_mul,
    ← integral_add ((integrable_Cum μ k S1 h1 n 0).const_mul a)
      ((integrable_Cum μ k S2 h2 n 0).const_mul b)]
  exact integral_mono (integrable_Cum μ k _ hS n 0)
    (((integrable_Cum μ k S1 h1 n 0).const_mul a).add ((integrable_Cum μ k S2 h2 n 0).const_mul b))
    fun d => Cum_convex k n d S1 S2 h1 h2 a b ha hb hab

/-- Invariant laws of the stock vector. -/
def CInv (k : ℕ) (S : ℝ) (m : Measure (Fin k → ℝ)) : Prop :=
  IsProbabilityMeasure m ∧ (m.prod μ).map (fun p : (Fin k → ℝ) × ℝ => stepC k S p.1 p.2) = m

/-- Expected one-period expiration under a law of the stock vector. -/
noncomputable def rhat (k : ℕ) (S : ℝ) (m : Measure (Fin k → ℝ)) : ℝ :=
  ∫ p : (Fin k → ℝ) × ℝ, expC k S p.1 p.2 ∂(m.prod μ)

lemma inv_G (k : ℕ) (S : ℝ) (hS : 0 ≤ S) (m : Measure (Fin k → ℝ)) (hm : CInv μ k S m) :
    ∀ n : ℕ, ∫ v, G μ k S n v ∂m = n * rhat μ k S m := by
  have := hm.1
  intro n
  induction n with
  | zero => simp [G_zero]
  | succ n ih =>
    have hst := measurable_stepC k S hS
    have i1 : Integrable (fun p : (Fin k → ℝ) × ℝ => expC k S p.1 p.2) (m.prod μ) :=
      bdd_integrable _ _ (measurable_expC k S hS) S
        (ae_of_all _ fun p => by
          have h := expC_bound k S hS p.1 p.2
          rw [abs_of_nonneg h.1]; exact h.2)
    have i2 : Integrable (fun p : (Fin k → ℝ) × ℝ => G μ k S n (stepC k S p.1 p.2)) (m.prod μ) :=
      bdd_integrable _ _ ((measurable_G μ k S hS n).comp hst) (n * S)
        (ae_of_all _ fun p => G_abs μ k S hS n _)
    have e1 : ∫ v, G μ k S (n+1) v ∂m
        = ∫ p : (Fin k → ℝ) × ℝ, (expC k S p.1 p.2 + G μ k S n (stepC k S p.1 p.2)) ∂(m.prod μ) := by
      have hp := integral_prod
        (fun p : (Fin k → ℝ) × ℝ => expC k S p.1 p.2 + G μ k S n (stepC k S p.1 p.2)) (i1.add i2)
      refine Eq.trans ?_ hp.symm
      exact integral_congr_ae (ae_of_all _ fun v => G_succ μ k S hS n v)
    have e2 : ∫ p : (Fin k → ℝ) × ℝ, G μ k S n (stepC k S p.1 p.2) ∂(m.prod μ)
        = ∫ v, G μ k S n v ∂m := by
      have h := integral_map (μ := m.prod μ) hst.aemeasurable (f := G μ k S n)
        (measurable_G μ k S hS n).aestronglyMeasurable
      rw [hm.2] at h
      exact h.symm
    rw [e1, integral_add i1 i2, e2, ih]
    unfold rhat
    push_cast
    ring

lemma core_bound (k : ℕ) (S : ℝ) (hS : 0 ≤ S) (m : Measure (Fin k → ℝ)) (hm : CInv μ k S m)
    (n : ℕ) : |n * rhat μ k S m - G μ k S n 0| ≤ S := by
  have := hm.1
  have iG : Integrable (G μ k S n) m :=
    bdd_integrable _ _ (measurable_G μ k S hS n) (n * S) (ae_of_all _ fun v => G_abs μ k S hS n v)
  have h := norm_integral_le_of_norm_le_const (μ := m)
    (f := fun v : Fin k → ℝ => G μ k S n v - G μ k S n 0) (C := S)
    (ae_of_all _ fun v => by rw [Real.norm_eq_abs]; exact G_diff μ k S hS n v 0)
  have hu : m.real univ = 1 := by simp
  rw [Real.norm_eq_abs, hu, mul_one, integral_sub iG (integrable_const _), integral_const, hu,
    one_smul, inv_G μ k S hS m hm n] at h
  exact h

lemma rhat_unique (k : ℕ) (S : ℝ) (hS : 0 ≤ S) (m m' : Measure (Fin k → ℝ))
    (hm : CInv μ k S m) (hm' : CInv μ k S m') : rhat μ k S m = rhat μ k S m' := by
  by_contra hne
  have hδ : 0 < |rhat μ k S m - rhat μ k S m'| := abs_pos.2 (sub_ne_zero.2 hne)
  obtain ⟨n, hn⟩ := exists_nat_gt (2 * S / |rhat μ k S m - rhat μ k S m'|)
  rw [div_lt_iff₀ hδ] at hn
  have h1 := abs_le.1 (core_bound μ k S hS m hm n)
  have h2 := abs_le.1 (core_bound μ k S hS m' hm' n)
  have h3 : (n : ℝ) * |rhat μ k S m - rhat μ k S m'| ≤ 2 * S := by
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    rw [← abs_of_nonneg hn0, ← abs_mul, abs_le]
    constructor <;> nlinarith [h1.1, h1.2, h2.1, h2.2]
  linarith

lemma rhat_convex (k : ℕ) (S1 S2 : ℝ) (h1 : 0 ≤ S1) (h2 : 0 ≤ S2)
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1)
    (m1 m2 m : Measure (Fin k → ℝ)) (hm1 : CInv μ k S1 m1) (hm2 : CInv μ k S2 m2)
    (hm : CInv μ k (a * S1 + b * S2) m) :
    rhat μ k (a * S1 + b * S2) m ≤ a * rhat μ k S1 m1 + b * rhat μ k S2 m2 := by
  have hS : 0 ≤ a * S1 + b * S2 := by positivity
  by_contra hlt
  rw [not_le] at hlt
  set δ := rhat μ k (a * S1 + b * S2) m - (a * rhat μ k S1 m1 + b * rhat μ k S2 m2) with hδdef
  have hδ : 0 < δ := by rw [hδdef]; linarith
  obtain ⟨n, hn⟩ := exists_nat_gt (2 * (a * S1 + b * S2) / δ)
  rw [div_lt_iff₀ hδ] at hn
  have c0 := abs_le.1 (core_bound μ k _ hS m hm n)
  have c1 := abs_le.1 (core_bound μ k S1 h1 m1 hm1 n)
  have c2 := abs_le.1 (core_bound μ k S2 h2 m2 hm2 n)
  have cv := G_convex μ k n S1 S2 h1 h2 a b ha hb hab
  have e1 : a * G μ k S1 n 0 ≤ a * (n * rhat μ k S1 m1 + S1) :=
    mul_le_mul_of_nonneg_left (by linarith [c1.1]) ha
  have e2 : b * G μ k S2 n 0 ≤ b * (n * rhat μ k S2 m2 + S2) :=
    mul_le_mul_of_nonneg_left (by linarith [c2.1]) hb
  have e3 : (n : ℝ) * δ ≤ 2 * (a * S1 + b * S2) := by
    rw [hδdef]
    nlinarith [c0.2]
  linarith

end Core

section KB

open Filter Topology BoundedContinuousFunction

variable (μ : Measure ℝ) [IsProbabilityMeasure μ]

/-- The transition operator acting on laws of the stock vector. -/
noncomputable def Phi (k : ℕ) (S : ℝ) (m : Measure (Fin k → ℝ)) : Measure (Fin k → ℝ) :=
  (m.prod μ).map (fun p : (Fin k → ℝ) × ℝ => stepC k S p.1 p.2)

lemma Phi_prob (k : ℕ) (S : ℝ) (hS : 0 ≤ S) (m : Measure (Fin k → ℝ)) [IsProbabilityMeasure m] :
    IsProbabilityMeasure (Phi μ k S m) :=
  Measure.isProbabilityMeasure_map (measurable_stepC k S hS).aemeasurable

/-- The transition operator acting on functions. -/
noncomputable def Pf (k : ℕ) (S : ℝ) (f : (Fin k → ℝ) → ℝ) (v : Fin k → ℝ) : ℝ :=
  ∫ d, f (stepC k S v d) ∂μ

lemma measurable_stepC_right (k : ℕ) (S : ℝ) (hS : 0 ≤ S) (v : Fin k → ℝ) :
    Measurable fun d : ℝ => stepC k S v d := by
  have e : (fun d : ℝ => stepC k S v d)
      = (fun p : (Fin k → ℝ) × ℝ => stepC k S p.1 p.2) ∘ (fun d : ℝ => (v, d)) := by
    funext d; simp only [Function.comp_apply]
  rw [e]
  exact (measurable_stepC k S hS).comp measurable_prodMk_left

lemma Phi_integral (k : ℕ) (S : ℝ) (hS : 0 ≤ S) (m : Measure (Fin k → ℝ)) [IsProbabilityMeasure m]
    (f : (Fin k → ℝ) →ᵇ ℝ) : ∫ v, f v ∂(Phi μ k S m) = ∫ v, Pf μ k S f v ∂m := by
  unfold Phi
  rw [integral_map (measurable_stepC k S hS).aemeasurable
    f.continuous.measurable.aestronglyMeasurable]
  have hi : Integrable (fun p : (Fin k → ℝ) × ℝ => f (stepC k S p.1 p.2)) (m.prod μ) :=
    bdd_integrable _ _ (f.continuous.measurable.comp (measurable_stepC k S hS)) ‖f‖
      (ae_of_all _ fun p => by rw [← Real.norm_eq_abs]; exact f.norm_coe_le_norm _)
  exact integral_prod _ hi

lemma Pf_cont (k : ℕ) (S : ℝ) (hS : 0 ≤ S) (f : (Fin k → ℝ) →ᵇ ℝ) :
    Continuous (Pf μ k S f) := by
  show Continuous fun v : Fin k → ℝ => ∫ d, f (stepC k S v d) ∂μ
  refine continuous_of_dominated (bound := fun _ => ‖f‖) (fun v => ?_)
    (fun v => ae_of_all _ fun d => f.norm_coe_le_norm _) (integrable_const _)
    (ae_of_all _ fun d => f.continuous.comp (continuous_stepC k S hS d))
  exact (f.continuous.measurable.comp (measurable_stepC_right k S hS v)).aestronglyMeasurable

lemma Pf_bound (k : ℕ) (S : ℝ) (f : (Fin k → ℝ) →ᵇ ℝ) (v : Fin k → ℝ) :
    ‖Pf μ k S f v‖ ≤ ‖f‖ := by
  have h := norm_integral_le_of_norm_le_const (μ := μ)
    (f := fun d : ℝ => f (stepC k S v d)) (C := ‖f‖)
    (ae_of_all _ fun d => f.norm_coe_le_norm _)
  have hu : μ.real univ = 1 := by simp
  rw [hu, mul_one] at h
  exact h

/-- The transition operator on bounded continuous functions. -/
noncomputable def PfB (k : ℕ) (S : ℝ) (hS : 0 ≤ S) (f : (Fin k → ℝ) →ᵇ ℝ) : (Fin k → ℝ) →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (Pf μ k S f) (Pf_cont μ k S hS f) ‖f‖
    (Pf_bound μ k S f)

/-- Laws of the stock vector started from the empty state. -/
noncomputable def mseq (k : ℕ) (S : ℝ) : ℕ → Measure (Fin k → ℝ)
  | 0 => Measure.dirac 0
  | n+1 => Phi μ k S (mseq k S n)

lemma mseq_prob (k : ℕ) (S : ℝ) (hS : 0 ≤ S) : ∀ n, IsProbabilityMeasure (mseq μ k S n) := by
  intro n
  induction n with
  | zero => show IsProbabilityMeasure (Measure.dirac (0 : Fin k → ℝ)); infer_instance
  | succ n ih => exact Phi_prob μ k S hS (mseq μ k S n)

lemma isClosed_K (k : ℕ) (S : ℝ) : IsClosed {v : Fin k → ℝ | InK k S v} := by
  have e : {v : Fin k → ℝ | InK k S v} = (⋂ i : Fin k, {v | 0 ≤ v i}) ∩ {v | A v k ≤ S} := by
    ext v
    exact ⟨fun h => ⟨mem_iInter.2 h.1, h.2⟩, fun h => ⟨mem_iInter.1 h.1, h.2⟩⟩
  rw [e]
  exact (isClosed_iInter fun i => isClosed_le continuous_const (continuous_apply i)).inter
    (isClosed_le (continuous_A k) continuous_const)

lemma isCompact_K (k : ℕ) (S : ℝ) : IsCompact {v : Fin k → ℝ | InK k S v} := by
  refine IsCompact.of_isClosed_subset (isCompact_Icc (a := (0 : Fin k → ℝ)) (b := fun _ => S))
    (isClosed_K k S) (fun v hv => ⟨fun i => hv.1 i, fun i => ?_⟩)
  have h1 : v i ≤ ∑ j, v j := Finset.single_le_sum (fun j _ => hv.1 j) (Finset.mem_univ i)
  have h2 := hv.2
  rw [A_k] at h2
  exact h1.trans h2

omit [IsProbabilityMeasure μ] in
lemma mseq_K (k : ℕ) (S : ℝ) (hS : 0 ≤ S) :
    ∀ n, mseq μ k S n {v : Fin k → ℝ | InK k S v}ᶜ = 0 := by
  intro n
  cases n with
  | zero =>
    show Measure.dirac (0 : Fin k → ℝ) {v : Fin k → ℝ | InK k S v}ᶜ = 0
    rw [Measure.dirac_apply]
    exact Set.indicator_of_notMem (Set.notMem_compl_iff.2
      (show (0 : Fin k → ℝ) ∈ {v : Fin k → ℝ | InK k S v} from zero_mem k S hS)) _
  | succ n =>
    show ((mseq μ k S n).prod μ).map (fun p : (Fin k → ℝ) × ℝ => stepC k S p.1 p.2)
      {v : Fin k → ℝ | InK k S v}ᶜ = 0
    rw [Measure.map_apply (measurable_stepC k S hS) (isClosed_K k S).measurableSet.compl]
    have he : (fun p : (Fin k → ℝ) × ℝ => stepC k S p.1 p.2) ⁻¹' {v : Fin k → ℝ | InK k S v}ᶜ = ∅ :=
      Set.eq_empty_iff_forall_notMem.2 fun p hp => hp (stepC_mem k S hS p.1 p.2)
    rw [he, measure_empty]

/-- Time averages of the laws. -/
noncomputable def avg (k : ℕ) (S : ℝ) (N : ℕ) : Measure (Fin k → ℝ) :=
  ((N + 1 : ℕ) : ENNReal)⁻¹ • ∑ n ∈ Finset.range (N + 1), mseq μ k S n

lemma avg_prob (k : ℕ) (S : ℝ) (hS : 0 ≤ S) (N : ℕ) : IsProbabilityMeasure (avg μ k S N) := by
  have hp := mseq_prob μ k S hS
  constructor
  unfold avg
  simp only [Measure.smul_apply, Measure.coe_finsetSum, Finset.sum_apply, measure_univ,
    Finset.sum_const, Finset.card_range, smul_eq_mul, nsmul_eq_mul, mul_one]
  exact ENNReal.inv_mul_cancel (by simp) (by simp)

omit [IsProbabilityMeasure μ] in
lemma avg_K (k : ℕ) (S : ℝ) (hS : 0 ≤ S) (N : ℕ) :
    avg μ k S N {v : Fin k → ℝ | InK k S v}ᶜ = 0 := by
  unfold avg
  simp only [Measure.smul_apply, Measure.coe_finsetSum, Finset.sum_apply, mseq_K μ k S hS,
    Finset.sum_const_zero, smul_zero]

omit [IsProbabilityMeasure μ] in
lemma avg_integral (k : ℕ) (S : ℝ) (N : ℕ) (g : (Fin k → ℝ) → ℝ)
    (hg : ∀ n, Integrable g (mseq μ k S n)) :
    ∫ v, g v ∂(avg μ k S N) = ((N : ℝ) + 1)⁻¹ * ∑ n ∈ Finset.range (N + 1), ∫ v, g v ∂(mseq μ k S n) := by
  unfold avg
  have hc : (((N + 1 : ℕ) : ENNReal)⁻¹).toReal = ((N : ℝ) + 1)⁻¹ := by
    rw [ENNReal.toReal_inv, ENNReal.toReal_natCast, Nat.cast_add, Nat.cast_one]
  rw [integral_smul_measure, integral_finsetSum_measure (fun n _ => hg n), hc, smul_eq_mul]

lemma avg_diff (k : ℕ) (S : ℝ) (hS : 0 ≤ S) (N : ℕ) (f : (Fin k → ℝ) →ᵇ ℝ) :
    ∫ v, Pf μ k S f v ∂(avg μ k S N) - ∫ v, f v ∂(avg μ k S N)
      = ((N : ℝ) + 1)⁻¹ * (∫ v, f v ∂(mseq μ k S (N + 1)) - ∫ v, f v ∂(mseq μ k S 0)) := by
  have hp := mseq_prob μ k S hS
  have hI : ∀ n, ∫ v, Pf μ k S f v ∂(mseq μ k S n) = ∫ v, f v ∂(mseq μ k S (n + 1)) :=
    fun n => (Phi_integral μ k S hS (mseq μ k S n) f).symm
  rw [avg_integral μ k S N (Pf μ k S f) (fun n => (PfB μ k S hS f).integrable (mseq μ k S n)),
    avg_integral μ k S N f (fun n => f.integrable (mseq μ k S n)), ← mul_sub,
    ← Finset.sum_sub_distrib]
  congr 1
  rw [Finset.sum_congr rfl fun n _ => by rw [hI n]]
  exact Finset.sum_range_sub (fun n => ∫ v, f v ∂(mseq μ k S n)) (N + 1)

theorem exists_CInv (k : ℕ) (S : ℝ) (hS : 0 ≤ S) : ∃ m, CInv μ k S m := by
  have hp := mseq_prob μ k S hS
  let aP : ℕ → ProbabilityMeasure (Fin k → ℝ) := fun N => ⟨avg μ k S N, avg_prob μ k S hS N⟩
  have htight : IsTightMeasureSet
      {((ρ : ProbabilityMeasure (Fin k → ℝ)) : Measure (Fin k → ℝ)) | ρ ∈ range aP} := by
    rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
    intro ε hε
    refine ⟨_, isCompact_K k S, ?_⟩
    rintro _ ⟨ρ, ⟨N, rfl⟩, rfl⟩
    show avg μ k S N {v : Fin k → ℝ | InK k S v}ᶜ ≤ ε
    rw [avg_K μ k S hS N]
    exact hε.le
  have hcomp : IsCompact (closure (range aP)) := isCompact_closure_of_isTightMeasureSet htight
  have hU : ((hyperfilter ℕ : Ultrafilter ℕ) : Filter ℕ) ≤ atTop := Nat.hyperfilter_le_atTop
  obtain ⟨ν, -, hν' : Tendsto _ _ _⟩ := hcomp.ultrafilter_le_nhds ((hyperfilter ℕ).map aP)
    (.trans (by simp) (monotone_principal subset_closure))
  have hν : Tendsto aP ((hyperfilter ℕ : Ultrafilter ℕ) : Filter ℕ) (𝓝 ν) := hν'
  have hPν := Phi_prob μ k S hS (ν : Measure (Fin k → ℝ))
  refine ⟨(ν : Measure (Fin k → ℝ)), inferInstance, ?_⟩
  show Phi μ k S (ν : Measure (Fin k → ℝ)) = (ν : Measure (Fin k → ℝ))
  refine ext_of_forall_integral_eq_of_IsFiniteMeasure fun f => ?_
  rw [Phi_integral μ k S hS _ f]
  have hlim := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.1 hν
  have l3 : Tendsto (fun N => ∫ v, Pf μ k S f v ∂(avg μ k S N) - ∫ v, f v ∂(avg μ k S N))
      ((hyperfilter ℕ : Ultrafilter ℕ) : Filter ℕ)
      (𝓝 (∫ v, Pf μ k S f v ∂(ν : Measure (Fin k → ℝ)) - ∫ v, f v ∂(ν : Measure (Fin k → ℝ)))) :=
    (hlim (PfB μ k S hS f)).sub (hlim f)
  have hb : ∀ n, |∫ v, f v ∂(mseq μ k S n)| ≤ ‖f‖ := by
    intro n
    have h := norm_integral_le_of_norm_le_const (μ := mseq μ k S n)
      (f := fun v : Fin k → ℝ => f v) (C := ‖f‖) (ae_of_all _ fun v => f.norm_coe_le_norm _)
    have hu : (mseq μ k S n).real univ = 1 := by simp
    rw [hu, mul_one, Real.norm_eq_abs] at h
    exact h
  have l0 : Tendsto (fun N : ℕ => 1 / ((N : ℝ) + 1) * (2 * ‖f‖)) atTop (𝓝 0) := by
    have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).mul_const (2 * ‖f‖)
    rwa [zero_mul] at h
  have l4 : Tendsto (fun N => ∫ v, Pf μ k S f v ∂(avg μ k S N) - ∫ v, f v ∂(avg μ k S N))
      atTop (𝓝 0) := by
    refine squeeze_zero_norm (fun N => ?_) l0
    rw [avg_diff μ k S hS N f, Real.norm_eq_abs, abs_mul, abs_inv,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ (N : ℝ) + 1), one_div]
    exact mul_le_mul_of_nonneg_left
      ((abs_sub _ _).trans (by linarith [hb (N + 1), hb 0])) (by positivity)
  exact sub_eq_zero.1 (tendsto_nhds_unique l3 (l4.mono_left hU))

end KB

section Transport

variable (μ : Measure ℝ) [IsProbabilityMeasure μ]

/-- The next full state as a function of the stock vector and the demand. -/
noncomputable def gmap (k : ℕ) (S : ℝ) (p : (Fin k → ℝ) × ℝ) : AgeState k :=
  baseStep k S (emb k S p).1 (emb k S p).2

lemma measurable_gmap (k : ℕ) (S : ℝ) (hS : 0 ≤ S) : Measurable (gmap k S) := by
  have e : gmap k S = (fun z : AgeState k × ℝ => baseStep k S z.1 z.2) ∘ emb k S := by
    funext p; simp only [gmap, Function.comp_apply]
  rw [e]
  exact (measurable_baseStep k S).comp (measurable_emb k S hS)

lemma fst_gmap (k : ℕ) (S : ℝ) :
    (fun p : (Fin k → ℝ) × ℝ => stepC k S p.1 p.2) = Prod.fst ∘ gmap k S := by
  funext p; simp only [stepC, gmap, emb, Function.comp_apply]

lemma good_step (k : ℕ) (S : ℝ) (hS : 0 ≤ S) (x : AgeState k) (hx : Good k S x) (d : ℝ)
    (hd : 0 ≤ d) :
    baseStep k S x d = gmap k S (x.1, d) ∧ baseExpired k S x d = expC k S x.1 d := by
  have h := norm_step k S hS x hx d hd
  have hp := proj_id k S hS x.1 (good_v k S hS x hx)
  have hd' : pos d = d := max_eq_left hd
  show baseStep k S x d = baseStep k S (proj k S x.1, 0) (pos d) ∧
    baseExpired k S x d = baseExpired k S (proj k S x.1, 0) (pos d)
  rw [hp, hd']
  exact h

lemma measurable_fstid (k : ℕ) :
    Measurable (Prod.map (Prod.fst : AgeState k → Fin k → ℝ) (id : ℝ → ℝ)) :=
  (measurable_fst.comp measurable_fst).prodMk measurable_snd

omit [IsProbabilityMeasure μ] in
lemma ae_good (k : ℕ) (S : ℝ) (hnn : ∀ᵐ d ∂μ, 0 ≤ d) (ν : Measure (AgeState k))
    [IsProbabilityMeasure ν] (hG : ν {x | canonical true x ∧ total x ≤ S} = 1) :
    ∀ᵐ z ∂ν.prod μ, Good k S z.1 ∧ 0 ≤ z.2 := by
  have hνG : ∀ᵐ x ∂ν, x ∈ {x : AgeState k | canonical true x ∧ total x ≤ S} :=
    (mem_ae_iff_prob_eq_one (measurableSet_good k S)).2 hG
  have hP1 : ∀ᵐ z ∂ν.prod μ, z.1 ∈ {x : AgeState k | canonical true x ∧ total x ≤ S} :=
    Measure.quasiMeasurePreserving_fst.ae hνG
  have hP2 : ∀ᵐ z ∂ν.prod μ, 0 ≤ z.2 := Measure.quasiMeasurePreserving_snd.ae hnn
  filter_upwards [hP1, hP2] with z h1 h2
  exact ⟨h1, h2⟩

lemma prod_fst_eq (k : ℕ) (ν : Measure (AgeState k)) [IsProbabilityMeasure ν] :
    (ν.prod μ).map (Prod.map (Prod.fst : AgeState k → Fin k → ℝ) (id : ℝ → ℝ))
      = (ν.map Prod.fst).prod μ := by
  have h := Measure.map_prod_map ν μ (measurable_fst : Measurable (Prod.fst : AgeState k → Fin k → ℝ))
    (measurable_id : Measurable (id : ℝ → ℝ))
  rw [Measure.map_id] at h
  exact h.symm

lemma step_law (k : ℕ) (S : ℝ) (hS : 0 ≤ S) (hnn : ∀ᵐ d ∂μ, 0 ≤ d) (ν : Measure (AgeState k))
    [IsProbabilityMeasure ν] (hG : ν {x | canonical true x ∧ total x ≤ S} = 1) :
    (ν.prod μ).map (fun z : AgeState k × ℝ => baseStep k S z.1 z.2)
      = ((ν.map Prod.fst).prod μ).map (gmap k S) := by
  have hc : (fun z : AgeState k × ℝ => baseStep k S z.1 z.2)
      =ᵐ[ν.prod μ] (gmap k S ∘ Prod.map (Prod.fst : AgeState k → Fin k → ℝ) (id : ℝ → ℝ)) := by
    filter_upwards [ae_good μ k S hnn ν hG] with z hz
    exact (good_step k S hS z.1 hz.1 z.2 hz.2).1
  rw [Measure.map_congr hc, ← Measure.map_map (measurable_gmap k S hS) (measurable_fstid k),
    prod_fst_eq μ k ν]

lemma rate_law (k : ℕ) (S : ℝ) (hS : 0 ≤ S) (hnn : ∀ᵐ d ∂μ, 0 ≤ d) (ν : Measure (AgeState k))
    [IsProbabilityMeasure ν] (hG : ν {x | canonical true x ∧ total x ≤ S} = 1) :
    stationaryOutdate μ k S ν = rhat μ k S (ν.map Prod.fst) := by
  have hc : (fun z : AgeState k × ℝ => baseExpired k S z.1 z.2)
      =ᵐ[ν.prod μ] fun z => (fun p : (Fin k → ℝ) × ℝ => expC k S p.1 p.2)
        (Prod.map (Prod.fst : AgeState k → Fin k → ℝ) (id : ℝ → ℝ) z) := by
    filter_upwards [ae_good μ k S hnn ν hG] with z hz
    exact (good_step k S hS z.1 hz.1 z.2 hz.2).2
  have h := integral_map (μ := ν.prod μ) (measurable_fstid k).aemeasurable
    (f := fun p : (Fin k → ℝ) × ℝ => expC k S p.1 p.2)
    (measurable_expC k S hS).aestronglyMeasurable
  rw [prod_fst_eq μ k ν] at h
  unfold stationaryOutdate rhat
  rw [integral_congr_ae hc]
  exact h.symm

lemma stat_to_clean (k : ℕ) (S : ℝ) (hS : 0 ≤ S) (hnn : ∀ᵐ d ∂μ, 0 ≤ d)
    (ν : Measure (AgeState k)) (hν : StationaryStock μ k S ν) :
    CInv μ k S (ν.map Prod.fst) ∧ stationaryOutdate μ k S ν = rhat μ k S (ν.map Prod.fst) := by
  obtain ⟨⟨hp, hinv⟩, hG⟩ := hν
  have hp' := hp
  have hL := step_law μ k S hS hnn ν hG
  have hinv' : (ν.prod μ).map (fun z : AgeState k × ℝ => baseStep k S z.1 z.2) = ν := hinv
  rw [hinv'] at hL
  refine ⟨⟨Measure.isProbabilityMeasure_map measurable_fst.aemeasurable, ?_⟩,
    rate_law μ k S hS hnn ν hG⟩
  rw [fst_gmap k S, ← Measure.map_map measurable_fst (measurable_gmap k S hS), ← hL]

lemma clean_to_stat (k : ℕ) (S : ℝ) (hS : 0 ≤ S) (hnn : ∀ᵐ d ∂μ, 0 ≤ d)
    (m : Measure (Fin k → ℝ)) (hm : CInv μ k S m) :
    StationaryStock μ k S ((m.prod μ).map (gmap k S)) := by
  have hpm := hm.1
  have hg := measurable_gmap k S hS
  have hp : IsProbabilityMeasure ((m.prod μ).map (gmap k S)) :=
    Measure.isProbabilityMeasure_map hg.aemeasurable
  have hG : ((m.prod μ).map (gmap k S)) {x | canonical true x ∧ total x ≤ S} = 1 := by
    rw [Measure.map_apply hg (measurableSet_good k S)]
    have hu : gmap k S ⁻¹' {x : AgeState k | canonical true x ∧ total x ≤ S} = univ :=
      Set.eq_univ_of_forall fun p =>
        step_good0 k S hS _ (proj_mem k S hS p.1) _ (pos_nonneg' p.2)
    rw [hu, measure_univ]
  have hfst : ((m.prod μ).map (gmap k S)).map Prod.fst = m := by
    rw [Measure.map_map measurable_fst hg, ← fst_gmap k S]
    exact hm.2
  have hL := step_law μ k S hS hnn ((m.prod μ).map (gmap k S)) hG
  rw [hfst] at hL
  exact ⟨⟨hp, hL⟩, hG⟩

end Transport

end NahmiasM12

open NahmiasM12 in
theorem solution (μ : Measure ℝ) (hμ : DiscreteDemand μ) (k : ℕ) :
    ∃ rate : ℝ → ℝ, (∀ S, 0 ≤ S → IsStationaryRate μ k S (rate S)) ∧
      ConvexOn ℝ (Ici 0) rate := by
  obtain ⟨hprob, hnn, -⟩ := hμ
  have hex : ∀ S : ℝ, ∃ m : Measure (Fin k → ℝ), 0 ≤ S → CInv μ k S m := by
    intro S
    by_cases h : 0 ≤ S
    · obtain ⟨m, hm⟩ := exists_CInv μ k S h
      exact ⟨m, fun _ => hm⟩
    · exact ⟨0, fun h' => absurd h' h⟩
  choose cm hcm using hex
  refine ⟨fun S => rhat μ k S (cm S), fun S hS =>
    ⟨⟨_, clean_to_stat μ k S hS hnn _ (hcm S hS)⟩, fun ν hν => ?_⟩,
    convex_Ici 0, fun S1 h1 S2 h2 a b ha hb hab => ?_⟩
  · obtain ⟨hc, hr⟩ := stat_to_clean μ k S hS hnn ν hν
    rw [hr]
    exact rhat_unique μ k S hS _ _ hc (hcm S hS)
  · have h1' : 0 ≤ S1 := h1
    have h2' : 0 ≤ S2 := h2
    show rhat μ k (a * S1 + b * S2) (cm (a * S1 + b * S2))
      ≤ a * rhat μ k S1 (cm S1) + b * rhat μ k S2 (cm S2)
    exact rhat_convex μ k S1 S2 h1' h2' a b ha hb hab _ _ _ (hcm S1 h1') (hcm S2 h2')
      (hcm _ (by positivity))
