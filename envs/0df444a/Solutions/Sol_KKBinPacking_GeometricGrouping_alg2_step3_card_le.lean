-- Prove2me | solution 1 for KKBinPacking.GeometricGrouping.alg2_step3_card_le
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-02T11:28:42.09899+00:00
-- url     : https://prove2.me/submissions/68a45a9e-63d6-4cff-b1b1-a11360be9146

-- Karmarkar--Karp, Algorithm 2: packing and bin count after Step 3.
-- Source: FOCS 1982, pp. 315--317.
-- The helpers below are proved from platform definitions and Mathlib only.
import Definitions.Def_KKBinPacking_GeometricGrouping_Algorithm2

set_option autoImplicit false

open KKBinPacking.GeometricGrouping

namespace KKContribution

lemma takeUntil_append_drop (k : ℝ) (L : List ℝ) :
    takeUntil k L ++ L.drop (takeUntil k L).length = L := by
  induction L generalizing k with
  | nil => simp [takeUntil]
  | cons x xs ih =>
    rw [takeUntil]
    split_ifs with h
    · simp
    · simpa using congrArg (List.cons x) (ih (k - x))

lemma groups_sum (k : ℝ) : (L : List ℝ) →
    ((geomGroupsList k L).map (fun (G : List ℝ) => (G : Multiset ℝ))).sum =
      (L : Multiset ℝ)
  | [] => by simp [geomGroupsList]
  | x :: xs => by
    rw [geomGroupsList]
    simp only [List.map_cons, List.sum_cons]
    rw [groups_sum k ((x :: xs).drop (takeUntil k (x :: xs)).length)]
    rw [Multiset.coe_add, takeUntil_append_drop]
termination_by L => L.length
decreasing_by
  simp only [List.length_drop, List.length_cons]
  have := takeUntil_cons_length_pos k x xs
  omega

lemma adjacent_partition (A : List ℝ) (Gs : List (List ℝ)) :
    (List.zipWith
      (fun (Gprev Gi : List ℝ) =>
        (((Gi.take Gprev.length).map (fun p => (p, Gi.headD 0))) : Multiset (ℝ × ℝ)))
      (A :: Gs) Gs).sum.map Prod.fst +
    (List.zipWith (fun (Gprev Gi : List ℝ) => ((Gi.drop Gprev.length) : Multiset ℝ))
      (A :: Gs) Gs).sum = (Gs.map (fun (G : List ℝ) => (G : Multiset ℝ))).sum := by
  induction Gs generalizing A with
  | nil => simp
  | cons G Gs ih =>
    have hsplit :
      ((G.take A.length : List ℝ) : Multiset ℝ) + (G.drop A.length : List ℝ) =
      (G : Multiset ℝ) := by rw [Multiset.coe_add, List.take_append_drop]
    simp only [List.zipWith_cons_cons, List.sum_cons, Multiset.map_add,
      Multiset.map_coe, List.map_map, Function.comp_def, List.map_id']
    simp only [List.map_cons, List.sum_cons]
    calc
      _ = ((G.take A.length : List ℝ) : Multiset ℝ) + (G.drop A.length : List ℝ) +
        ((List.zipWith
          (fun (Gprev Gi : List ℝ) =>
            (((Gi.take Gprev.length).map (fun p => (p, Gi.headD 0))) : Multiset (ℝ × ℝ)))
          (G :: Gs) Gs).sum.map Prod.fst +
        (List.zipWith (fun (Gprev Gi : List ℝ) => ((Gi.drop Gprev.length) : Multiset ℝ))
          (G :: Gs) Gs).sum) := by abel
      _ = _ := by rw [hsplit, ih G]

lemma geom_partition (k : ℕ) (I : Multiset ℝ) :
    (geomPairs k I).map Prod.fst + geomJ' k I = I := by
  have hsum : ((geomGroups k I).map (fun (G : List ℝ) => (G : Multiset ℝ))).sum = I := by
    rw [geomGroups, groups_sum, Multiset.sort_eq]
  apply Eq.trans (b := ((geomGroups k I).map (fun (G : List ℝ) => (G : Multiset ℝ))).sum) ?_ hsum
  unfold geomPairs geomJ'
  generalize geomGroups k I = Gs
  cases Gs with
  | nil => simp
  | cons A Gs =>
    simp only [List.tail_cons, List.headD_cons, List.map_cons, List.sum_cons]
    rw [show
      (List.zipWith
        (fun (Gprev Gi : List ℝ) =>
          (((Gi.take Gprev.length).map (fun p => (p, Gi.headD 0))) : Multiset (ℝ × ℝ)))
        (A :: Gs) Gs).sum.map Prod.fst +
      ((A : Multiset ℝ) +
        (List.zipWith (fun (Gprev Gi : List ℝ) => ((Gi.drop Gprev.length) : Multiset ℝ))
          (A :: Gs) Gs).sum) =
      (A : Multiset ℝ) + ((Gs.map (fun (G : List ℝ) => (G : Multiset ℝ))).sum) by
        rw [← adjacent_partition A Gs]
        abel]

lemma groups_pairwise (k : ℝ) : (L : List ℝ) → L.Pairwise (· ≥ ·) →
    ∀ G ∈ geomGroupsList k L, G.Pairwise (· ≥ ·)
  | [], _ => by simp [geomGroupsList]
  | x :: xs, hL => by
    rw [geomGroupsList]
    intro G hG
    simp only [List.mem_cons] at hG
    rcases hG with rfl | hG
    · have h : (takeUntil k (x :: xs) ++
          (x :: xs).drop (takeUntil k (x :: xs)).length).Pairwise (· ≥ ·) := by
        rwa [takeUntil_append_drop]
      exact (List.pairwise_append.mp h).1
    · exact groups_pairwise k _ hL.drop G hG
termination_by L => L.length
decreasing_by
  simp only [List.length_drop, List.length_cons]
  have := takeUntil_cons_length_pos k x xs
  omega

lemma headD_ge {G : List ℝ} (hG : G.Pairwise (· ≥ ·)) {x : ℝ} (hx : x ∈ G) :
    x ≤ G.headD 0 := by
  cases G with
  | nil => simp at hx
  | cons y ys => simpa using hG.rel_head hx

lemma adjacent_pair_le (A : List ℝ) (Gs : List (List ℝ))
    (hsorted : ∀ G ∈ Gs, G.Pairwise (· ≥ ·)) :
    ∀ p ∈ (List.zipWith
      (fun (Gprev Gi : List ℝ) =>
        (((Gi.take Gprev.length).map (fun x => (x, Gi.headD 0))) : Multiset (ℝ × ℝ)))
      (A :: Gs) Gs).sum, p.1 ≤ p.2 := by
  induction Gs generalizing A with
  | nil => simp
  | cons G Gs ih =>
    intro p hp
    simp only [List.zipWith_cons_cons, List.sum_cons, Multiset.mem_add,
      Multiset.mem_coe, List.mem_map] at hp
    rcases hp with ⟨x, hx, rfl⟩ | hp
    · exact headD_ge (hsorted G (by simp)) (List.mem_of_mem_take hx)
    · exact ih G (fun H hH => hsorted H (by simp [hH])) p hp

lemma geom_pair_le (k : ℕ) (I : Multiset ℝ) :
    ∀ p ∈ geomPairs k I, p.1 ≤ p.2 := by
  have hsorted : ∀ G ∈ geomGroups k I, G.Pairwise (· ≥ ·) := by
    exact groups_pairwise (k : ℝ) _ (Multiset.pairwise_sort _ _)
  unfold geomPairs
  generalize geomGroups k I = Gs at *
  cases Gs with
  | nil => simp
  | cons A Gs =>
    simp only [List.tail_cons]
    exact adjacent_pair_le A Gs (fun G hG => hsorted G (by simp [hG]))

lemma fst_mem_source (k : ℕ) (I : Multiset ℝ) {p : ℝ × ℝ} (hp : p ∈ geomPairs k I) :
    p.1 ∈ I := by
  rw [← geom_partition k I]
  exact Multiset.mem_add.mpr (Or.inl (Multiset.mem_map.mpr ⟨p, hp, rfl⟩))

end KKContribution

open KKBinPacking.Shared KKBinPacking.GeometricGrouping

namespace KKContribution

lemma submultiset_sum_le {a b : Multiset ℝ} (hab : a ≤ b)
    (hb : ∀ x ∈ b, 0 ≤ x) : a.sum ≤ b.sum := by
  obtain ⟨c, rfl⟩ := Multiset.le_iff_exists_add.mp hab
  have hc : 0 ≤ c.sum := Multiset.sum_nonneg (fun x hx => hb x (by simp [hx]))
  simpa only [Multiset.sum_add] using (le_add_of_nonneg_right hc : a.sum ≤ a.sum + c.sum)

lemma principal_mem_configuration {J : Multiset ℝ} {x : Multiset ℝ →₀ ℝ}
    (hx : IsBasicFeasible J x) {c : Multiset ℝ} (hc : c ∈ principalConfigs x) :
    IsConfiguration J c := by
  classical
  obtain ⟨d, hd, hcd⟩ := Multiset.mem_sum.mp hc
  have hcd' : c = d := Multiset.eq_of_mem_replicate hcd
  subst c
  exact hx.1.1 d hd

lemma step3_packing (k : ℕ) (g : ℝ) (I : Multiset ℝ)
    (hI : IsInstance I) (tr : Alg2Trace k g I)
    (hpartition : ∀ J : Multiset ℝ, (geomPairs k J).map Prod.fst + geomJ' k J = J)
    (hround : ∀ (J : Multiset ℝ) p, p ∈ geomPairs k J → p.1 ≤ p.2) :
    IsPacking (I.filter (fun p => g < p)) (alg2Step3Bins tr.t tr.Bp tr.PJ' tr.P3) := by
  classical
  have hfst : ∀ (J : Multiset ℝ), (geomPairs k J).map Prod.fst ≤ J := by
    intro J
    calc
      _ ≤ (geomPairs k J).map Prod.fst + geomJ' k J := le_self_add
      _ = J := hpartition J
  have hstep : ∀ i < tr.t,
      ((tr.Bp i).map (Multiset.map Prod.fst) + tr.PJ' i).join + tr.inst (i + 1) =
        tr.inst i := by
    intro i hi
    rw [Multiset.join_add, ← Multiset.map_join, (tr.PJ'_packing i hi).1,
      tr.inst_succ i hi]
    calc
      (tr.Bp i).join.map Prod.fst + geomJ' k (tr.inst i) +
          (geomPairs k (tr.inst i) - (tr.Bp i).join).map Prod.fst =
          ((geomPairs k (tr.inst i) - (tr.Bp i).join) + (tr.Bp i).join).map Prod.fst +
            geomJ' k (tr.inst i) := by simp [Multiset.map_add, add_comm, add_left_comm]
      _ = tr.inst i := by rw [Multiset.sub_add_cancel (tr.Bp_sub i hi), hpartition]
  have hinst : ∀ i, i ≤ tr.t → ∀ p ∈ tr.inst i, 0 ≤ p := by
    intro i
    induction i with
    | zero =>
      intro hi p hp
      rw [tr.inst_zero] at hp
      exact (hI p (Multiset.mem_filter.mp hp).1).1.le
    | succ i ih =>
      intro hi p hp
      apply ih (by omega) p
      rw [← hstep i (by omega)]
      exact Multiset.mem_add.mpr (Or.inr hp)
  have hbins : ∀ i < tr.t, ∀ b ∈ (tr.Bp i).map (Multiset.map Prod.fst) + tr.PJ' i,
      b.sum ≤ 1 := by
    intro i hi b hb
    rcases Multiset.mem_add.mp hb with hb | hb
    · obtain ⟨a, ha, rfl⟩ := Multiset.mem_map.mp hb
      obtain ⟨c, hc, hac⟩ := Multiset.exists_mem_of_rel_of_mem (tr.Bp_config i hi) ha
      have hconf := principal_mem_configuration (tr.x_basic i hi) hc
      have hpairs : ∀ p ∈ a, p ∈ geomPairs k (tr.inst i) := by
        intro p hp
        exact Multiset.mem_of_le (tr.Bp_sub i hi) (Multiset.mem_join.mpr ⟨a, ha, hp⟩)
      have hnonneg : ∀ s ∈ c, 0 ≤ s := by
        intro s hs
        obtain ⟨p, hp, rfl⟩ := Multiset.mem_map.mp (hconf.2.1 s hs)
        exact (hinst i (by omega) p.1
          (Multiset.mem_of_le (hfst _) (Multiset.mem_map.mpr ⟨p, hp, rfl⟩))).trans
            (hround _ p hp)
      exact (Multiset.sum_map_le_sum_map Prod.fst Prod.snd
        (fun p hp => hround _ p (hpairs p hp))).trans
          ((submultiset_sum_le hac hnonneg).trans hconf.2.2)
    · exact (tr.PJ'_packing i hi).2 b hb
  have htelescope : ∀ n, n ≤ tr.t →
      (∑ i ∈ Finset.range n, ((tr.Bp i).map (Multiset.map Prod.fst) + tr.PJ' i)).join +
        tr.inst n = tr.inst 0 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      intro hn
      rw [Finset.sum_range_succ, Multiset.join_add, add_assoc, hstep n (by omega)]
      exact ih (by omega)
  constructor
  · unfold alg2Step3Bins
    rw [Multiset.join_add, tr.P3_packing.1, htelescope _ le_rfl, tr.inst_zero]
  · intro b hb
    rcases Multiset.mem_add.mp hb with hb | hb
    · obtain ⟨i, hi, hb⟩ := Multiset.mem_sum.mp hb
      exact hbins i (Finset.mem_range.mp hi) b hb
    · exact tr.P3_packing.2 b hb

end KKContribution

open KKBinPacking.Shared KKBinPacking.GeometricGrouping
open scoped BigOperators

namespace KKContribution

lemma principalConfigs_card (x : Multiset ℝ →₀ ℝ) :
    (principalConfigs x).card = principalCount x := by
  classical
  simp [principalConfigs, principalCount]

lemma principal_bins_card (k : ℕ) (g : ℝ) (I : Multiset ℝ)
    (tr : Alg2Trace k g I) (i : ℕ) (hi : i < tr.t) :
    (tr.Bp i).card = principalCount (tr.x i) := by
  exact (Multiset.card_eq_card_of_rel (tr.Bp_config i hi)).trans
    (principalConfigs_card _)

lemma step3_card_bound (k : ℕ) (g : ℝ) (I : Multiset ℝ)
    (tr : Alg2Trace k g I) :
    (Multiset.card (alg2Step3Bins tr.t tr.Bp tr.PJ' tr.P3) : ℝ) ≤
      ((∑ i ∈ Finset.range tr.t, principalCount (tr.x i) : ℕ) : ℝ) +
        tr.t * (2 * (k : ℝ) * (2 + Real.log (1 / g))) +
        2 + (2 / (1 - 1 / (k : ℝ))) * Real.log (1 / g) := by
  classical
  have hc : (alg2Step3Bins tr.t tr.Bp tr.PJ' tr.P3).card =
      (∑ i ∈ Finset.range tr.t, (principalCount (tr.x i) + (tr.PJ' i).card)) +
        tr.P3.card := by
    simp only [alg2Step3Bins, Multiset.card_add, Multiset.card_sum, Multiset.card_map]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    rw [principal_bins_card k g I tr i (Finset.mem_range.mp hi)]
  rw [hc]
  push_cast
  have hJ : (∑ i ∈ Finset.range tr.t, ((tr.PJ' i).card : ℝ)) ≤
      tr.t * (2 * (k : ℝ) * (2 + Real.log (1 / g))) := by
    calc
      _ ≤ ∑ _i ∈ Finset.range tr.t, (2 * (k : ℝ) * (2 + Real.log (1 / g))) := by
        exact Finset.sum_le_sum fun i hi => tr.PJ'_card i (Finset.mem_range.mp hi)
      _ = _ := by simp
  rw [Finset.sum_add_distrib]
  linarith [tr.P3_card]

end KKContribution

theorem solution (k : ℕ) (hk : 2 ≤ k) (g : ℝ) (hg0 : 0 < g)
    (I : Multiset ℝ) (hI : IsInstance I) (tr : Alg2Trace k g I) :
    IsPacking (I.filter (fun p => g < p)) (alg2Step3Bins tr.t tr.Bp tr.PJ' tr.P3) ∧
    (Multiset.card (alg2Step3Bins tr.t tr.Bp tr.PJ' tr.P3) : ℝ) ≤
      ((∑ i ∈ Finset.range tr.t, principalCount (tr.x i) : ℕ) : ℝ) +
        tr.t * (2 * (k : ℝ) * (2 + Real.log (1 / g))) +
        2 + (2 / (1 - 1 / (k : ℝ))) * Real.log (1 / g)  := by
  exact ⟨KKContribution.step3_packing k g I hI tr
    (KKContribution.geom_partition k) (KKContribution.geom_pair_le k),
    KKContribution.step3_card_bound k g I tr⟩
