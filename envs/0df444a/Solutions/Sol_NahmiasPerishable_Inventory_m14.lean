-- Prove2me | solution 1 for NahmiasPerishable.Inventory.m14
-- status  : ACCEPTED   (prove)
-- author  : @CGTMoyano
-- created : 2026-11-24T02:36:53.912353+00:00
-- url     : https://prove2.me/submissions/d4e50abc-9286-4f3a-832d-3a93ca28df60

import Definitions.Def_NahmiasPerishable_Inventory_Stationary

open MeasureTheory
open NahmiasPerishable.Inventory

namespace NahmiasM14

/-- Prefix sums of the age vector: the stock in the j oldest classes. -/
noncomputable def A {k : ℕ} (v : Fin k → ℝ) (j : ℕ) : ℝ := ∑ i : Fin k, if i.val < j then v i else 0

/-- The maximum over 1 ≤ i ≤ j of A i - i q, truncated below at zero. -/
noncomputable def Nf {k : ℕ} (q : ℝ) (v : Fin k → ℝ) : ℕ → ℝ
  | 0 => 0
  | (j+1) => max (Nf q v j) (A v (j+1) - ((j+1 : ℕ) : ℝ) * q)

noncomputable def Lf {k : ℕ} (v : Fin k → ℝ) : ℝ := ∑ j ∈ Finset.range k, A v (j+1)

noncomputable def Ex {k : ℕ} (S : ℝ) (v : Fin k → ℝ) (i : ℕ) : ℝ := if i ≤ k then A v i else S

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

lemma R2 (a S d : ℝ) (ha : a ≤ S) (hd : d ≤ S) :
    pos (pos (S - a) - pos (d - a)) = S - max a d := by
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

lemma snd_zero (k : ℕ) (S : ℝ) (x : AgeState k) (d : ℝ) (hx : total x ≤ S) (hd : d ≤ S) :
    (baseStep k S x d).2 = 0 := by
  rw [step_snd]; simp only [pos, max_def]; split_ifs <;> linarith

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

lemma KL2 (k : ℕ) (S : ℝ) (x : AgeState k) (d : ℝ) (hv : ∀ i, 0 ≤ x.1 i) (hb : x.2 = 0)
    (hT : A x.1 k ≤ S) (hdS : d ≤ S) (hk : 1 ≤ k) :
    A (baseStep k S x d).1 k = S - max (A x.1 1) d := by
  have hk1 : k - 1 < k := by omega
  have hk2 : ¬ (k - 1) + 1 < k := by omega
  have e : k - 1 + 1 = k := by omega
  have h1 := A_succ (baseStep k S x d).1 (k-1) hk1
  have h2 := KL1 k S x d hv hb (k-1) hk1
  have h3 := step_coord_last k S x d (k-1) hk1 hk2
  rw [e] at h1 h2
  rw [h1, h2, h3, total_eq, hb, sub_zero, R2 _ S d hT hdS]
  ring

lemma Nf_nonneg {k : ℕ} (q : ℝ) (v : Fin k → ℝ) (j : ℕ) : 0 ≤ Nf q v j := by
  induction j with
  | zero => exact le_rfl
  | succ j ih => exact le_max_of_le_left ih

lemma Nf_le {k : ℕ} (q : ℝ) (v : Fin k → ℝ) (j i : ℕ) (hi1 : 1 ≤ i) (hij : i ≤ j) :
    A v i - (i : ℝ) * q ≤ Nf q v j := by
  induction j with
  | zero => omega
  | succ j ih =>
    rcases Nat.eq_or_lt_of_le hij with h | h
    · subst h; exact le_max_right _ _
    · exact le_max_of_le_left (ih (by omega))

lemma Nf_ub {k : ℕ} (q : ℝ) (v : Fin k → ℝ) (C : ℝ) (hC : 0 ≤ C) (j : ℕ)
    (h : ∀ i, i ≤ j → A v i - (i : ℝ) * q ≤ C) : Nf q v j ≤ C := by
  induction j with
  | zero => exact hC
  | succ j ih =>
    exact max_le (ih fun i hi => h i (by omega)) (h (j+1) le_rfl)

lemma F1 (k : ℕ) (S q : ℝ) (x : AgeState k) (d : ℝ) (hv : ∀ i, 0 ≤ x.1 i) (hb : x.2 = 0)
    (hT : A x.1 k ≤ S) (hd0 : 0 ≤ d) (hdq : d ≤ q) (hq0 : 0 ≤ q) (hS' : S = (k : ℝ) * q + q)
    (hk : 1 ≤ k) :
    ∀ j, j ≤ k → Nf q (baseStep k S x d).1 j ≤ Nf q x.1 k + q - max (A x.1 1) d := by
  have h0 := Nf_nonneg q x.1 k
  have hkq := mul_nonneg (Nat.cast_nonneg (α := ℝ) k) hq0
  intro j
  induction j with
  | zero =>
    intro _
    have h1 := Nf_le q x.1 k 1 le_rfl hk
    rw [Nat.cast_one, one_mul] at h1
    have h2 : max (A x.1 1) d ≤ Nf q x.1 k + q := max_le (by linarith) (by linarith)
    show (0 : ℝ) ≤ _
    linarith
  | succ j ih =>
    intro hj
    show max (Nf q (baseStep k S x d).1 j)
      (A (baseStep k S x d).1 (j+1) - ((j+1 : ℕ) : ℝ) * q) ≤ _
    refine max_le (ih (by omega)) ?_
    by_cases hjk : j + 1 < k
    · rw [KL1 k S x d hv hb (j+1) hjk]
      have h2 := Nf_le q x.1 k (j+1+1) (by omega) (by omega)
      have hjq := mul_nonneg (Nat.cast_nonneg (α := ℝ) j) hq0
      have hc : ((j+1+1 : ℕ) : ℝ) = (j : ℝ) + 1 + 1 := by push_cast; ring
      have hc' : ((j+1 : ℕ) : ℝ) = (j : ℝ) + 1 := by push_cast; ring
      rw [hc] at h2
      rw [hc']
      have h3 : max (A x.1 (j+1+1)) d ≤ Nf q x.1 k + ((j : ℝ) + 1 + 1) * q :=
        max_le (by linarith) (by nlinarith)
      linarith
    · have e : j + 1 = k := by omega
      rw [e, KL2 k S x d hv hb hT (by linarith) hk]
      linarith

lemma F2 (k : ℕ) (S : ℝ) (x : AgeState k) (d : ℝ) (hv : ∀ i, 0 ≤ x.1 i) (hb : x.2 = 0)
    (hT : A x.1 k ≤ S) (hdS : d ≤ S) (hk : 1 ≤ k) :
    Lf x.1 + S - ((k : ℝ) + 1) * max (A x.1 1) d ≤ Lf (baseStep k S x d).1 := by
  have key : ∀ j ∈ Finset.range k,
      Ex S x.1 (j+1+1) - max (A x.1 1) d ≤ A (baseStep k S x d).1 (j+1) := by
    intro j hj
    have hj := Finset.mem_range.1 hj
    by_cases h : j + 1 < k
    · rw [KL1 k S x d hv hb (j+1) h]
      have := le_max_left (A x.1 (j+1+1)) d
      unfold Ex; rw [if_pos (by omega)]; linarith
    · have e : j + 1 = k := by omega
      unfold Ex; rw [if_neg (by omega), e, KL2 k S x d hv hb hT hdS hk]
  have tel : ∑ j ∈ Finset.range k, (Ex S x.1 (j+1+1) - Ex S x.1 (j+1))
      = Ex S x.1 (k+1) - Ex S x.1 (0+1) :=
    Finset.sum_range_sub (fun j => Ex S x.1 (j+1)) k
  have hE1 : Ex S x.1 (0+1) = A x.1 1 := by unfold Ex; rw [if_pos (by omega)]
  have hEk : Ex S x.1 (k+1) = S := by unfold Ex; rw [if_neg (by omega)]
  have hEj : ∑ j ∈ Finset.range k, Ex S x.1 (j+1) = Lf x.1 := by
    refine Finset.sum_congr rfl fun j hj => ?_
    have hj := Finset.mem_range.1 hj
    unfold Ex; rw [if_pos (by omega)]
  have h1 : ∑ j ∈ Finset.range k, (Ex S x.1 (j+1+1) - max (A x.1 1) d)
      ≤ Lf (baseStep k S x d).1 := Finset.sum_le_sum key
  have h2 : ∑ j ∈ Finset.range k, (Ex S x.1 (j+1+1) - max (A x.1 1) d)
      = (∑ j ∈ Finset.range k, (Ex S x.1 (j+1+1) - Ex S x.1 (j+1)))
        + (∑ j ∈ Finset.range k, Ex S x.1 (j+1)) - (k : ℝ) * max (A x.1 1) d := by
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range,
      nsmul_eq_mul]
    ring
  have h3 := le_max_left (A x.1 1) d
  rw [h2, tel, hE1, hEk, hEj] at h1
  linarith

lemma expired_pos (k : ℕ) (S : ℝ) (x : AgeState k) (d : ℝ) (hk : 0 < k) (hb : x.2 = 0) :
    baseExpired k S x d = max (A x.1 1) d - d := by
  have hA1 : A x.1 1 = x.1 ⟨0, hk⟩ := by
    have := A_succ x.1 0 hk
    rw [A0] at this
    simpa using this
  unfold baseExpired expires
  rw [if_neg (by omega), dif_pos hk, hb, hA1]
  simp only [pos, max_def]; split_ifs <;> linarith

lemma expired_zero (k : ℕ) (S : ℝ) (x : AgeState k) (d : ℝ) (hk : k = 0) (hb : x.2 = 0)
    (hS : 0 ≤ S) (hd : d ≤ S) : baseExpired k S x d = S - d := by
  subst hk
  unfold baseExpired
  rw [if_pos rfl, total_eq, hb, A0]
  simp only [pos, max_def]; split_ifs <;> linarith

lemma A_const {k : ℕ} (q : ℝ) (x : AgeState k) (hxc : ∀ i, x.1 i = q) :
    A x.1 k = (k : ℝ) * q := by
  rw [A_k, Finset.sum_congr rfl (fun i _ => hxc i), Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]

lemma fixed_pt (k : ℕ) (S q : ℝ) (x : AgeState k) (d : ℝ) (hxc : ∀ i, x.1 i = q)
    (hb : x.2 = 0) (hq0 : 0 ≤ q) (hS' : S = (k : ℝ) * q + q) (h0 : 0 ≤ d) (h1 : d ≤ q) :
    baseStep k S x d = x := by
  have hAk := A_const q x hxc
  have ht : total x = (k : ℝ) * q := by rw [total_eq, hb, hAk, sub_zero]
  have hkq := mul_nonneg (Nat.cast_nonneg (α := ℝ) k) hq0
  apply Prod.ext
  · funext i
    obtain ⟨j, hj'⟩ := i
    by_cases hj : j + 1 < k
    · have h2 : q ≤ A x.1 (j+1) := by
        rw [A_succ x.1 j hj', hxc]
        linarith [A_nonneg x.1 (fun i => by rw [hxc]; exact hq0) j]
      rw [step_coord_lt k S x d j hj' hj, hb, hxc, hxc]
      simp only [pos, max_def]; split_ifs <;> linarith
    · have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast (by omega : 1 ≤ k)
      have h3 : q ≤ (k : ℝ) * q := by nlinarith
      rw [step_coord_last k S x d j hj' hj, ht, hxc]
      simp only [pos, max_def]; split_ifs <;> linarith
  · rw [step_snd, ht, hb]
    simp only [pos, max_def]; split_ifs <;> linarith

lemma measurable_A {k : ℕ} (j : ℕ) : Measurable fun v : Fin k → ℝ => A v j := by
  unfold A
  refine Finset.measurable_sum _ fun i _ => ?_
  by_cases h : i.val < j
  · simp only [if_pos h]; exact measurable_pi_apply i
  · simp only [if_neg h]; exact measurable_const

lemma measurable_Nf {k : ℕ} (q : ℝ) (j : ℕ) : Measurable fun v : Fin k → ℝ => Nf q v j := by
  induction j with
  | zero => show Measurable fun _ : Fin k → ℝ => (0 : ℝ); exact measurable_const
  | succ j ih =>
    show Measurable fun v : Fin k → ℝ => max (Nf q v j) (A v (j+1) - ((j+1 : ℕ) : ℝ) * q)
    exact ih.max ((measurable_A (j+1)).sub measurable_const)

lemma measurable_Lf {k : ℕ} : Measurable fun v : Fin k → ℝ => Lf v := by
  unfold Lf
  exact Finset.measurable_sum _ fun j _ => measurable_A (j+1)

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

/-- For an invariant law, a bounded potential has zero mean drift. -/
lemma inv_ineq {X : Type*} [MeasurableSpace X] (ν : Measure X) (μ : Measure ℝ)
    [IsProbabilityMeasure ν] [IsProbabilityMeasure μ] (F : X × ℝ → X) (hF : Measurable F)
    (hmap : (ν.prod μ).map F = ν) (Φ : X → ℝ) (hΦ : Measurable Φ) (C : ℝ)
    (hb : ∀ᵐ x ∂ν, |Φ x| ≤ C) (g : X × ℝ → ℝ) (hg : Integrable g (ν.prod μ))
    (h : ∀ᵐ z ∂ν.prod μ, Φ (F z) ≤ Φ z.1 + g z) : 0 ≤ ∫ z, g z ∂ν.prod μ := by
  have hΦint : Integrable Φ ν := bdd_integrable ν Φ hΦ C hb
  have h1 : ∫ z, Φ (F z) ∂ν.prod μ = ∫ x, Φ x ∂ν := by
    have := integral_map (μ := ν.prod μ) hF.aemeasurable (f := Φ) hΦ.aestronglyMeasurable
    rw [hmap] at this
    exact this.symm
  have hI1 : Integrable (fun z => Φ (F z)) (ν.prod μ) := by
    have hi : Integrable Φ ((ν.prod μ).map F) := by rw [hmap]; exact hΦint
    exact (integrable_map_measure hΦ.aestronglyMeasurable hF.aemeasurable).1 hi
  have hI2 : Integrable (fun z : X × ℝ => Φ z.1) (ν.prod μ) := hΦint.comp_fst μ
  have h2 : ∫ z, Φ z.1 ∂ν.prod μ = ∫ x, Φ x ∂ν := by
    rw [integral_fun_fst]; simp
  have h3 := integral_mono_ae hI1 (g := fun z => Φ z.1 + g z) (hI2.add hg) h
  rw [integral_add hI2 hg, h1, h2] at h3
  linarith

end NahmiasM14

open NahmiasM14 in
theorem solution (μ : Measure ℝ) (hμ : DiscreteDemand μ) (k : ℕ) (S : ℝ) (hS : 0 ≤ S)
    (hsmall : ∀ᵐ d ∂μ, d ≤ S/(k+1)) :
    IsStationaryRate μ k S (S/(k+1)-∫ d, d ∂μ) := by
  obtain ⟨hprob, hnn, -⟩ := hμ
  haveI := hprob
  have hk1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hq0 : 0 ≤ S / ((k : ℝ) + 1) := div_nonneg hS hk1.le
  have hS' : S = (k : ℝ) * (S / ((k : ℝ) + 1)) + S / ((k : ℝ) + 1) := by field_simp
  generalize S / ((k : ℝ) + 1) = q at hsmall hq0 hS' ⊢
  have hkq := mul_nonneg (Nat.cast_nonneg (α := ℝ) k) hq0
  have hqS : q ≤ S := by linarith
  have hF := measurable_baseStep k S
  have hdint : Integrable (fun d : ℝ => d) μ :=
    Integrable.mono' (integrable_const q) measurable_id.aestronglyMeasurable
      (by filter_upwards [hnn, hsmall] with d h0 h1
          rw [Real.norm_eq_abs, abs_of_nonneg h0]; exact h1)
  unfold IsStationaryRate
  refine ⟨?_, ?_⟩
  · -- existence: the constant state
    refine ⟨Measure.dirac ((fun _ => q, 0) : AgeState k), ?_⟩
    have hmem : ((fun _ => q, 0) : AgeState k) ∈ {x : AgeState k | canonical true x ∧ total x ≤ S} := by
      show canonical true ((fun _ => q, 0) : AgeState k) ∧ total ((fun _ => q, 0) : AgeState k) ≤ S
      refine ⟨⟨⟨fun _ => hq0, le_rfl⟩, fun h => absurd h (lt_irrefl _), fun _ => rfl⟩, ?_⟩
      rw [total_eq, A_const q _ (fun _ => rfl)]
      show (k : ℝ) * q - 0 ≤ S
      linarith
    unfold StationaryStock ShockInvariant
    refine ⟨⟨inferInstance, ?_⟩, Measure.dirac_apply_of_mem hmem⟩
    rw [Measure.dirac_prod, Measure.map_map hF measurable_prodMk_left]
    have hc : ((fun z : AgeState k × ℝ => baseStep k S z.1 z.2) ∘ Prod.mk ((fun _ => q, 0) : AgeState k))
        =ᵐ[μ] fun _ => ((fun _ => q, 0) : AgeState k) := by
      filter_upwards [hnn, hsmall] with d h0 h1
      exact fixed_pt k S q _ d (fun _ => rfl) rfl hq0 hS' h0 h1
    rw [Measure.map_congr hc]
    ext s hs
    rw [Measure.map_apply measurable_const hs, Measure.dirac_apply' _ hs]
    by_cases h : ((fun _ => q, 0) : AgeState k) ∈ s <;> simp [h]
  · -- every stationary law has the same outdating rate
    intro ν hν
    unfold StationaryStock ShockInvariant at hν
    obtain ⟨⟨hpν, hmap⟩, hG1⟩ := hν
    haveI := hpν
    have hνG : ∀ᵐ x ∂ν, x ∈ {x : AgeState k | canonical true x ∧ total x ≤ S} :=
      (mem_ae_iff_prob_eq_one (measurableSet_good k S)).2 hG1
    have hP1 : ∀ᵐ z ∂ν.prod μ, z.1 ∈ {x : AgeState k | canonical true x ∧ total x ≤ S} :=
      Measure.quasiMeasurePreserving_fst.ae hνG
    have hP2 : ∀ᵐ z ∂ν.prod μ, 0 ≤ z.2 ∧ z.2 ≤ q :=
      Measure.quasiMeasurePreserving_snd.ae (hnn.and hsmall)
    have hb' : ∀ᵐ x ∂ν, x.2 = 0 := by
      have h : ∀ᵐ y ∂(ν.prod μ).map (fun z : AgeState k × ℝ => baseStep k S z.1 z.2), y.2 = 0 :=
        (ae_map_iff hF.aemeasurable
          (measurableSet_eq_fun measurable_snd measurable_const)).2
          (by filter_upwards [hP1, hP2] with z hz1 hz2
              exact snd_zero k S z.1 z.2 hz1.2 (by linarith [hz2.2]))
      rwa [hmap] at h
    have hν' : ∀ᵐ x ∂ν, (∀ i, 0 ≤ x.1 i) ∧ x.2 = 0 ∧ A x.1 k ≤ S := by
      filter_upwards [hνG, hb'] with x hx hxb
      refine ⟨hx.1.1.1, hxb, ?_⟩
      have := hx.2
      rw [total_eq, hxb, sub_zero] at this
      exact this
    have hPz : ∀ᵐ z ∂ν.prod μ, ((∀ i, 0 ≤ z.1.1 i) ∧ z.1.2 = 0 ∧ A z.1.1 k ≤ S) ∧
        0 ≤ z.2 ∧ z.2 ≤ q := by
      filter_upwards [Measure.quasiMeasurePreserving_fst.ae hν', hP2] with z h1 h2
      exact ⟨h1, h2⟩
    have hsndint : Integrable (fun z : AgeState k × ℝ => z.2) (ν.prod μ) :=
      bdd_integrable _ _ measurable_snd q
        (by filter_upwards [hP2] with z hz; rw [abs_of_nonneg hz.1]; exact hz.2)
    have hsnd : ∫ z, z.2 ∂ν.prod μ = ∫ d, d ∂μ := by
      rw [integral_fun_snd (fun d : ℝ => d)]; simp
    show ∫ xd, baseExpired k S xd.1 xd.2 ∂ν.prod μ = q - ∫ d, d ∂μ
    rcases Nat.eq_zero_or_pos k with hk0 | hkpos
    · have hqS' : q = S := by
        have := hS'; rw [hk0] at this; simp at this; exact this.symm
      have hexp : ∀ᵐ z ∂ν.prod μ, baseExpired k S z.1 z.2 = S - z.2 := by
        filter_upwards [hPz] with z hz
        exact expired_zero k S z.1 z.2 hk0 hz.1.2.1 hS (by linarith [hz.2.2])
      rw [integral_congr_ae hexp, integral_sub (integrable_const S) hsndint, hsnd, hqS']
      simp
    · have hk : 1 ≤ k := hkpos
      have hMmeas : Measurable fun z : AgeState k × ℝ => max (A z.1.1 1) z.2 :=
        ((measurable_A 1).comp (measurable_fst.comp measurable_fst)).max measurable_snd
      have hMint : Integrable (fun z : AgeState k × ℝ => max (A z.1.1 1) z.2) (ν.prod μ) :=
        bdd_integrable _ _ hMmeas S
          (by filter_upwards [hPz] with z hz
              rw [abs_of_nonneg (le_max_of_le_right hz.2.1)]
              exact max_le ((A_mono z.1.1 hz.1.1 hk).trans hz.1.2.2) (by linarith [hz.2.2]))
      have hexp : ∀ᵐ z ∂ν.prod μ, baseExpired k S z.1 z.2 = max (A z.1.1 1) z.2 - z.2 := by
        filter_upwards [hPz] with z hz
        exact expired_pos k S z.1 z.2 hkpos hz.1.2.1
      rw [integral_congr_ae hexp, integral_sub hMint hsndint, hsnd]
      have hup : 0 ≤ ∫ z, (q - max (A z.1.1 1) z.2) ∂ν.prod μ :=
        inv_ineq ν μ _ hF hmap (fun x : AgeState k => Nf q x.1 k)
          ((measurable_Nf q k).comp measurable_fst) S
          (by filter_upwards [hν'] with x hx
              rw [abs_of_nonneg (Nf_nonneg q x.1 k)]
              refine Nf_ub q x.1 S hS k fun i hi => ?_
              have h1 := (A_mono x.1 hx.1 hi).trans hx.2.2
              have h2 := mul_nonneg (Nat.cast_nonneg (α := ℝ) i) hq0
              linarith)
          (fun z => q - max (A z.1.1 1) z.2) ((integrable_const q).sub hMint)
          (by filter_upwards [hPz] with z hz
              have := F1 k S q z.1 z.2 hz.1.1 hz.1.2.1 hz.1.2.2 hz.2.1 hz.2.2 hq0 hS' hk k le_rfl
              show Nf q (baseStep k S z.1 z.2).1 k ≤ Nf q z.1.1 k + (q - max (A z.1.1 1) z.2)
              linarith)
      have hlow : 0 ≤ ∫ z, (((k : ℝ) + 1) * max (A z.1.1 1) z.2 - S) ∂ν.prod μ :=
        inv_ineq ν μ _ hF hmap (fun x : AgeState k => - Lf x.1)
          ((measurable_Lf.comp measurable_fst).neg) ((k : ℝ) * S)
          (by filter_upwards [hν'] with x hx
              have hnn' : 0 ≤ Lf x.1 :=
                Finset.sum_nonneg fun j _ => A_nonneg x.1 hx.1 (j+1)
              have hle : Lf x.1 ≤ (k : ℝ) * S := by
                have : Lf x.1 ≤ ∑ _j ∈ Finset.range k, S :=
                  Finset.sum_le_sum fun j hj =>
                    (A_mono x.1 hx.1 (by have := Finset.mem_range.1 hj; omega)).trans hx.2.2
                rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at this
                exact this
              rw [abs_neg, abs_of_nonneg hnn']; exact hle)
          (fun z => ((k : ℝ) + 1) * max (A z.1.1 1) z.2 - S)
          ((hMint.const_mul _).sub (integrable_const S))
          (by filter_upwards [hPz] with z hz
              have := F2 k S z.1 z.2 hz.1.1 hz.1.2.1 hz.1.2.2 (by linarith [hz.2.2]) hk
              show - Lf (baseStep k S z.1 z.2).1
                ≤ - Lf z.1.1 + (((k : ℝ) + 1) * max (A z.1.1 1) z.2 - S)
              linarith)
      rw [integral_sub (integrable_const q) hMint] at hup
      rw [integral_sub (hMint.const_mul _) (integrable_const S), integral_const_mul] at hlow
      simp only [integral_const, probReal_univ, one_smul] at hup hlow
      have hkq' : ((k : ℝ) + 1) * q = S := by linarith
      have : q ≤ ∫ z, max (A z.1.1 1) z.2 ∂ν.prod μ := by
        by_contra hcon
        rw [not_le] at hcon
        nlinarith
      linarith
