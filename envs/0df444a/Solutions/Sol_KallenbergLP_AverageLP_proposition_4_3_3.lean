-- Prove2me | solution 1 for KallenbergLP.AverageLP.proposition_4_3_3
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-07T04:04:42.110989+00:00
-- url     : https://prove2.me/submissions/3291d92b-fd38-4d41-a327-c5ffc4b6d646

import Mathlib
import Definitions.Def_MarkovDecisionProcesses_AverageReward
import Definitions.Def_BlackwellDiscreteDP_NearOne_LimitMatrix
import Definitions.Def_KallenbergLP_AverageLP_Model
open MarkovDecisionProcesses BlackwellDiscreteDP.NearOne Matrix Filter

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace P433
open KallenbergLP.AverageLP

variable {S A : Type*} [Fintype S] [Fintype A] [DecidableEq S] [DecidableEq A]

noncomputable def X (M : StationaryMDP S A) (x : Pair M → ℝ) (i : S) (a : A) : ℝ :=
  if h : a ∈ M.admissible i then x ⟨(i, a), h⟩ else 0

lemma X_nonneg (M : StationaryMDP S A) (x : Pair M → ℝ) (hx : ∀ p, 0 ≤ x p) (i : S) (a : A) :
    0 ≤ X M x i a := by
  unfold X; split_ifs
  · exact hx _
  · exact le_rfl

lemma sum_pair (M : StationaryMDP S A) (g : S → A → ℝ) (x : Pair M → ℝ) :
    ∑ p : Pair M, g p.1.1 p.1.2 * x p = ∑ i, ∑ a, g i a * X M x i a := by
  have h1 : ∑ p : Pair M, g p.1.1 p.1.2 * x p
      = ∑ p : Pair M, (fun q : S × A => g q.1 q.2 * X M x q.1 q.2) p.1 := by
    refine Finset.sum_congr rfl (fun p _ => ?_)
    simp only [X, dif_pos p.2]
  rw [h1, ← Finset.sum_subtype (Finset.univ.filter (fun q : S × A => q.2 ∈ M.admissible q.1))
    (by simp) (fun q : S × A => g q.1 q.2 * X M x q.1 q.2)]
  rw [Finset.sum_filter_of_ne]
  · exact Fintype.sum_prod_type _
  · intro q _ hq
    by_contra hc
    apply hq
    simp [X, hc]

lemma dsum (f : S → A → ℝ) (j : S) :
    ∑ i, ∑ a, (if i = j then f i a else 0) = ∑ a, f j a := by
  rw [Finset.sum_eq_single j]
  · simp
  · intro b _ hb; simp [hb]
  · simp

lemma stateSum_eq (M : StationaryMDP S A) (x : Pair M → ℝ) (j : S) :
    stateSum M x j = ∑ a, X M x j a := by
  unfold stateSum
  rw [Finset.sum_filter]
  have e := sum_pair M (fun i _ => if i = j then (1:ℝ) else 0) x
  simp only [ite_mul, one_mul, zero_mul] at e
  rw [e, dsum (fun i a => X M x i a) j]

lemma dpw_eq (M : StationaryMDP S A) (x y : Pair M → ℝ) (i : S) (a : A) :
    dualPolicyWeight M x y i a =
      if 0 < stateSum M x i then X M x i a / stateSum M x i else X M y i a / stateSum M y i := by
  unfold dualPolicyWeight X
  by_cases ha : a ∈ M.admissible i
  · by_cases hs : 0 < stateSum M x i
    · simp [ha, hs]
    · simp [ha, hs]
  · by_cases hs : 0 < stateSum M x i
    · simp [ha, hs]
    · simp [ha, hs]

lemma P_entry (M : StationaryMDP S A) (x y : Pair M → ℝ) (i j : S) :
    weightMatrix M (dualPolicyWeight M x y) i j =
      ∑ a, dualPolicyWeight M x y i a * M.trans i a j := by
  simp only [weightMatrix, Matrix.of_apply]
  apply Finset.sum_subset (Finset.subset_univ _)
  intro a _ ha
  simp [dualPolicyWeight, ha]

lemma boundary (P : S → S → ℝ) (U : Finset S) {i j : S} (hij : Accessible P i j)
    (hi : i ∉ U) (hj : j ∈ U) :
    ∃ k l, Accessible P i k ∧ k ∉ U ∧ l ∈ U ∧ 0 < P k l := by
  unfold Accessible at hij ⊢
  revert hj
  induction hij with
  | refl => intro hj; exact absurd hj hi
  | @tail b c hab hbc ih =>
    intro hj
    by_cases hb : b ∈ U
    · exact ih hb
    · exact ⟨b, c, hab, hb, hj, hbc⟩

lemma acc_pos (P : S → S → ℝ) (s : S → ℝ) (Pnn : ∀ k l, 0 ≤ P k l) (snn : ∀ k, 0 ≤ s k)
    (stat : ∀ l, s l = ∑ k, s k * P k l) {i j : S} (hij : Accessible P i j) (hi : 0 < s i) :
    0 < s j := by
  unfold Accessible at hij
  induction hij with
  | refl => exact hi
  | @tail b c _ hbc ih =>
    rw [stat c]
    calc 0 < s b * P b c := mul_pos ih hbc
      _ ≤ ∑ k, s k * P k c :=
        Finset.single_le_sum (f := fun k => s k * P k c)
          (fun k _ => mul_nonneg (snn k) (Pnn k c)) (Finset.mem_univ b)

lemma rec_of_pos (P : S → S → ℝ) (s : S → ℝ) (Pnn : ∀ k l, 0 ≤ P k l) (snn : ∀ k, 0 ≤ s k)
    (stat : ∀ l, s l = ∑ k, s k * P k l) (row : ∀ k, 0 < s k → ∑ l, P k l = 1)
    {i : S} (hi : 0 < s i) : IsRecurrent P i := by
  classical
  intro j hij
  by_contra hji
  set U : Finset S := Finset.univ.filter (fun l => Accessible P j l) with hUdef
  have hU : ∀ l, l ∈ U ↔ Accessible P j l := by intro l; simp [hUdef]
  have hclosed : ∀ k ∈ U, ∀ l ∉ U, P k l = 0 := by
    intro k hk l hl
    rcases (Pnn k l).lt_or_eq with h | h
    · exfalso; apply hl; rw [hU] at hk ⊢
      exact Relation.ReflTransGen.tail hk h
    · exact h.symm
  have hbal : ∑ k, s k * ∑ l ∈ U, P k l = ∑ k ∈ U, s k := by
    calc ∑ k, s k * ∑ l ∈ U, P k l = ∑ l ∈ U, ∑ k, s k * P k l := by
          rw [Finset.sum_comm]; simp [Finset.mul_sum]
      _ = ∑ l ∈ U, s l := Finset.sum_congr rfl (fun l _ => (stat l).symm)
  have hin : ∀ k ∈ U, s k * ∑ l ∈ U, P k l = s k := by
    intro k hk
    rcases (snn k).lt_or_eq with h | h
    · rw [Finset.sum_subset (Finset.subset_univ U) (fun l _ hl => hclosed k hk l hl), row k h,
        mul_one]
    · rw [← h, zero_mul]
  have hout : ∑ k ∈ Finset.univ \ U, s k * ∑ l ∈ U, P k l = 0 := by
    have e := Finset.sum_sdiff (Finset.subset_univ U) (f := fun k => s k * ∑ l ∈ U, P k l)
    rw [Finset.sum_congr rfl hin] at e
    linarith [hbal]
  obtain ⟨k, l, hik, hk, hl, hkl⟩ :=
    boundary P U hij (fun h => hji ((hU i).1 h)) ((hU j).2 Relation.ReflTransGen.refl)
  have hsk : 0 < s k := acc_pos P s Pnn snn stat hik hi
  have hnn : ∀ m ∈ Finset.univ \ U, 0 ≤ s m * ∑ l ∈ U, P m l :=
    fun m _ => mul_nonneg (snn m) (Finset.sum_nonneg (fun l _ => Pnn m l))
  have h0 := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 hout k (by simp [hk])
  have hpos : 0 < ∑ l ∈ U, P k l :=
    lt_of_lt_of_le hkl (Finset.single_le_sum (f := fun l => P k l) (fun l _ => Pnn k l) hl)
  have := mul_pos hsk hpos
  linarith

end P433

open MarkovDecisionProcesses BlackwellDiscreteDP.NearOne Matrix Filter KallenbergLP.AverageLP in
theorem solution {S A : Type*} [Fintype S] [Fintype A] [DecidableEq S] [DecidableEq A]
    (M : StationaryMDP S A)
    (β : S → ℝ) (hβpos : ∀ j, 0 < β j) (hβsum : ∑ j, β j = 1)
    (z : (Pair M → ℝ) × (Pair M → ℝ)) (hz : z ∈ dualFeasible M β) :
    ∀ i : S, IsRecurrent (weightMatrix M (dualPolicyWeight M z.1 z.2)) i ↔ i ∈ Ex M z.1 := by
  obtain ⟨h1, h2, h3⟩ := hz
  set x := z.1 with hxdef
  set y := z.2 with hydef
  set P := weightMatrix M (dualPolicyWeight M x y) with hPdef
  set s := stateSum M x with hsdef
  set t := stateSum M y with htdef
  have hx : ∀ p, 0 ≤ x p := fun p => (h3 p).1
  have hy : ∀ p, 0 ≤ y p := fun p => (h3 p).2
  have Xnn : ∀ k a, 0 ≤ P433.X M x k a := P433.X_nonneg M x hx
  have Ynn : ∀ k a, 0 ≤ P433.X M y k a := P433.X_nonneg M y hy
  have snn : ∀ k, 0 ≤ s k := fun k => by
    rw [hsdef, P433.stateSum_eq]; exact Finset.sum_nonneg (fun a _ => Xnn k a)
  have tnn : ∀ k, 0 ≤ t k := fun k => by
    rw [htdef, P433.stateSum_eq]; exact Finset.sum_nonneg (fun a _ => Ynn k a)
  have Xzero : ∀ k, s k = 0 → ∀ a, P433.X M x k a = 0 := by
    intro k hk a
    rw [hsdef, P433.stateSum_eq] at hk
    exact (Finset.sum_eq_zero_iff_of_nonneg (fun a _ => Xnn k a)).1 hk a (Finset.mem_univ a)
  -- the constraints in X-form
  have c1 : ∀ j, s j = ∑ k, ∑ a, M.trans k a j * P433.X M x k a := by
    intro j
    have h := h1 j
    rw [show (∑ p : Pair M, ((if p.1.1 = j then (1:ℝ) else 0) - M.trans p.1.1 p.1.2 j) * x p)
        = _ from P433.sum_pair M (fun i a => (if i = j then (1:ℝ) else 0) - M.trans i a j) x] at h
    simp only [sub_mul, Finset.sum_sub_distrib, ite_mul, one_mul, zero_mul] at h
    rw [P433.dsum (fun i a => P433.X M x i a) j] at h
    rw [hsdef, P433.stateSum_eq]; linarith
  have c2 : ∀ j, s j + t j - ∑ k, ∑ a, M.trans k a j * P433.X M y k a = β j := by
    intro j
    have h := h2 j
    rw [show (∑ p : Pair M, ((if p.1.1 = j then (1:ℝ) else 0) - M.trans p.1.1 p.1.2 j) * y p)
        = _ from P433.sum_pair M (fun i a => (if i = j then (1:ℝ) else 0) - M.trans i a j) y] at h
    simp only [sub_mul, Finset.sum_sub_distrib, ite_mul, one_mul, zero_mul] at h
    rw [P433.dsum (fun i a => P433.X M y i a) j] at h
    rw [htdef, P433.stateSum_eq M y j]; linarith
  have Pnn : ∀ k l, 0 ≤ P k l := by
    intro k l
    rw [hPdef, P433.P_entry]
    refine Finset.sum_nonneg (fun a _ => mul_nonneg ?_ (M.trans_nonneg _ _ _))
    rw [P433.dpw_eq]
    split_ifs
    · exact div_nonneg (Xnn k a) (snn k)
    · exact div_nonneg (Ynn k a) (tnn k)
  have keyx : ∀ k l, s k * P k l = ∑ a, M.trans k a l * P433.X M x k a := by
    intro k l
    rw [hPdef, P433.P_entry, Finset.mul_sum]
    rcases (snn k).lt_or_eq with hs | hs
    · refine Finset.sum_congr rfl (fun a _ => ?_)
      rw [P433.dpw_eq, if_pos hs, show stateSum M x k = s k from rfl]
      field_simp
      try ring
    · refine Finset.sum_congr rfl (fun a _ => ?_)
      rw [Xzero k hs.symm a, ← hs]; ring
  have stat : ∀ l, s l = ∑ k, s k * P k l := by
    intro l; rw [c1 l]; exact Finset.sum_congr rfl (fun k _ => (keyx k l).symm)
  have row : ∀ k, 0 < s k → ∑ l, P k l = 1 := by
    intro k hk
    have e : ∀ l, P k l = (∑ a, M.trans k a l * P433.X M x k a) / s k := by
      intro l; rw [← keyx, mul_div_cancel_left₀ _ (ne_of_gt hk)]
    simp_rw [e]
    rw [← Finset.sum_div, Finset.sum_comm]
    simp_rw [← Finset.sum_mul, M.trans_sum, one_mul]
    rw [hsdef, P433.stateSum_eq] at hk ⊢
    exact div_self (ne_of_gt hk)
  intro i
  constructor
  · -- recurrent ⇒ in E_x
    intro hrec
    show 0 < s i
    by_contra hsi
    have hsi0 : s i = 0 := le_antisymm (not_lt.1 hsi) (snn i)
    classical
    set C : Finset S := Finset.univ.filter (fun l => Accessible P i l) with hCdef
    have hC : ∀ l, l ∈ C ↔ Accessible P i l := by intro l; simp [hCdef]
    have sC : ∀ l ∈ C, s l = 0 := by
      intro l hl
      by_contra hne
      have hpos : 0 < s l := lt_of_le_of_ne (snn l) (Ne.symm hne)
      have := P433.acc_pos P s Pnn snn stat (hrec l ((hC l).1 hl)) hpos
      linarith
    have hstep : ∀ k ∈ C, ∀ a m, 0 < P433.X M y k a → 0 < M.trans k a m → m ∈ C := by
      intro k hk a m hya htr
      have hs0 := sC k hk
      have htk : 0 < t k := by
        rw [htdef, P433.stateSum_eq]
        exact lt_of_lt_of_le hya
          (Finset.single_le_sum (f := fun a => P433.X M y k a) (fun a _ => Ynn k a) (Finset.mem_univ a))
      have hPkm : 0 < P k m := by
        rw [hPdef, P433.P_entry]
        have hterm : 0 < dualPolicyWeight M x y k a * M.trans k a m := by
          rw [P433.dpw_eq, if_neg (by rw [← hsdef, hs0]; exact lt_irrefl 0), ← htdef]
          exact mul_pos (div_pos hya htk) htr
        refine lt_of_lt_of_le hterm
          (Finset.single_le_sum (f := fun a => dualPolicyWeight M x y k a * M.trans k a m)
            (fun b _ => ?_) (Finset.mem_univ a))
        refine mul_nonneg ?_ (M.trans_nonneg _ _ _)
        rw [P433.dpw_eq]; split_ifs
        · exact div_nonneg (Xnn k b) (snn k)
        · exact div_nonneg (Ynn k b) (tnn k)
      exact (hC m).2 (Relation.ReflTransGen.tail ((hC k).1 hk) hPkm)
    have hmass : ∀ k ∈ C, ∀ a, P433.X M y k a * ∑ l ∈ C, M.trans k a l = P433.X M y k a := by
      intro k hk a
      rcases (Ynn k a).lt_or_eq with hya | hya
      · rw [Finset.sum_subset (Finset.subset_univ C), M.trans_sum, mul_one]
        intro l _ hl
        rcases (M.trans_nonneg k a l).lt_or_eq with htr | htr
        · exact absurd (hstep k hk a l hya htr) hl
        · exact htr.symm
      · rw [← hya, zero_mul]
    have hflow : ∑ l ∈ C, ∑ k, ∑ a, M.trans k a l * P433.X M y k a
        = ∑ k, ∑ a, P433.X M y k a * ∑ l ∈ C, M.trans k a l := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun a _ => ?_)
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun l _ => by ring)
    have hge : ∑ k ∈ C, t k ≤ ∑ l ∈ C, ∑ k, ∑ a, M.trans k a l * P433.X M y k a := by
      rw [hflow]
      calc ∑ k ∈ C, t k = ∑ k ∈ C, ∑ a, P433.X M y k a * ∑ l ∈ C, M.trans k a l := by
            refine Finset.sum_congr rfl (fun k hk => ?_)
            rw [htdef, P433.stateSum_eq]
            exact Finset.sum_congr rfl (fun a _ => (hmass k hk a).symm)
        _ ≤ ∑ k, ∑ a, P433.X M y k a * ∑ l ∈ C, M.trans k a l :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ C)
              (fun k _ _ => Finset.sum_nonneg (fun a _ => mul_nonneg (Ynn k a)
                (Finset.sum_nonneg (fun l _ => M.trans_nonneg k a l))))
    have hβC : ∑ l ∈ C, β l = ∑ l ∈ C, s l + ∑ l ∈ C, t l
        - ∑ l ∈ C, ∑ k, ∑ a, M.trans k a l * P433.X M y k a := by
      rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl (fun l _ => (c2 l).symm)
    have hs0 : ∑ l ∈ C, s l = 0 := Finset.sum_eq_zero sC
    have hiC : i ∈ C := (hC i).2 Relation.ReflTransGen.refl
    have hβpos' : 0 < ∑ l ∈ C, β l := Finset.sum_pos (fun l _ => hβpos l) ⟨i, hiC⟩
    linarith
  · -- in E_x ⇒ recurrent
    intro hi
    exact P433.rec_of_pos P s Pnn snn stat row hi
