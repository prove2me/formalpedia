-- Prove2me | solution 1 for KKBinPacking.GeometricGrouping.lp_floor_rounding_certificate
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T15:09:42.958544+00:00
-- url     : https://prove2.me/submissions/6c4116ef-f74a-468b-9773-859b23c98218

import Definitions.Def_KKBinPacking_GeometricGrouping_Algorithm2
open KKBinPacking.Shared

namespace AKd4f0eca3
open KKBinPacking.GeometricGrouping

/-- Split a sub-multiset of `Q.join` into pieces, one per element of `Q`. -/
theorem split (Q : Multiset (Multiset ℝ)) : ∀ M : Multiset ℝ, M ≤ Q.join →
    ∃ P : Multiset (Multiset ℝ), P.join = M ∧ Multiset.card P = Multiset.card Q ∧
      ∀ b ∈ P, ∃ c ∈ Q, b ≤ c := by
  induction Q using Multiset.induction_on with
  | empty =>
    intro M hM
    refine ⟨0, ?_, by simp, by simp⟩
    simp only [Multiset.join_zero, nonpos_iff_eq_zero] at hM ⊢
    simpa using hM.symm
  | cons c Q ih =>
    intro M hM
    rw [Multiset.join_cons] at hM
    obtain ⟨P, hP1, hP2, hP3⟩ := ih (M - M ∩ c) (by
      rw [Multiset.le_iff_count] at hM ⊢
      intro t
      have := hM t
      rw [Multiset.count_add] at this
      rw [Multiset.count_sub, Multiset.count_inter]
      omega)
    refine ⟨(M ∩ c) ::ₘ P, ?_, by simp [hP2], ?_⟩
    · rw [Multiset.join_cons, hP1]
      exact add_tsub_cancel_of_le (Multiset.inter_le_left)
    · intro b hb
      rcases Multiset.mem_cons.1 hb with rfl | hb
      · exact ⟨c, Multiset.mem_cons_self _ _, Multiset.inter_le_right⟩
      · obtain ⟨c', hc', hbc⟩ := hP3 b hb
        exact ⟨c', Multiset.mem_cons_of_mem hc', hbc⟩

theorem sum_le_of_le {b c : Multiset ℝ} (h : b ≤ c) (hc : ∀ t ∈ c, 0 ≤ t) :
    b.sum ≤ c.sum := by
  obtain ⟨d, rfl⟩ := Multiset.le_iff_exists_add.1 h
  rw [Multiset.sum_add]
  have : 0 ≤ d.sum := Multiset.sum_nonneg fun t ht => hc t (Multiset.mem_add.2 (Or.inr ht))
  linarith

theorem packing_of_le (I : Multiset ℝ) (hI : IsInstance I) (Q : Multiset (Multiset ℝ))
    (hQ : ∀ c ∈ Q, IsConfiguration I c) (M : Multiset ℝ) (hM : M ≤ Q.join) :
    ∃ P, IsPacking M P ∧ Multiset.card P = Multiset.card Q := by
  obtain ⟨P, h1, h2, h3⟩ := split Q M hM
  refine ⟨P, ⟨h1, ?_⟩, h2⟩
  intro b hb
  obtain ⟨c, hc, hbc⟩ := h3 b hb
  have hc' := hQ c hc
  exact (sum_le_of_le hbc fun t ht => (hI t (hc'.2.1 t ht)).1.le).trans hc'.2.2

theorem count_join_cons (t : ℝ) : ∀ (S : Multiset (Multiset ℝ)),
    S.join.count t = (S.map (Multiset.count t)).sum := by
  intro S
  induction S using Multiset.induction_on with
  | empty => simp
  | cons c S ih => simp [Multiset.join_cons, Multiset.count_add, ih]

theorem count_join_principal (x : Multiset ℝ →₀ ℝ) (t : ℝ) :
    ((principalConfigs x).join.count t) = ∑ c ∈ x.support, ⌊x c⌋₊ * c.count t := by
  unfold principalConfigs
  rw [count_join_cons]
  induction x.support using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, Multiset.map_add, Multiset.sum_add, ih]
    simp [Multiset.map_replicate, Multiset.sum_replicate]

theorem card_principal (x : Multiset ℝ →₀ ℝ) :
    Multiset.card (principalConfigs x) = principalCount x := by
  unfold principalConfigs principalCount
  simp [Multiset.card_sum]

theorem mem_principal {x : Multiset ℝ →₀ ℝ} {c : Multiset ℝ} (h : c ∈ principalConfigs x) :
    c ∈ x.support := by
  unfold principalConfigs at h
  obtain ⟨d, hd, hcd⟩ := Multiset.mem_sum.1 h
  rw [Multiset.eq_of_mem_replicate hcd]; exact hd

end AKd4f0eca3

open KKBinPacking.Shared KKBinPacking.GeometricGrouping in
theorem solution
    (I : Multiset ℝ) (hI : KKBinPacking.GeometricGrouping.IsInstance I)
    (x : Multiset ℝ →₀ ℝ) (hx : IsLPFeasible I x) :
    let R := I - (KKBinPacking.GeometricGrouping.principalConfigs x).join
    ∃ P : Multiset (Multiset ℝ),
      KKBinPacking.GeometricGrouping.IsPacking (I - R) P ∧
      P.card ≤ KKBinPacking.GeometricGrouping.principalCount x ∧
      KKBinPacking.GeometricGrouping.SIZE R ≤ lpCost x
        - (KKBinPacking.GeometricGrouping.principalCount x : ℝ) ∧
      (KKBinPacking.GeometricGrouping.OPT R : ℝ) ≤ (x.support.card : ℝ) := by

  intro R
  set J := (principalConfigs x).join with hJ
  have hRle : R ≤ I := Multiset.sub_le_self _ _
  have hfrac0 : ∀ c, 0 ≤ x c - (⌊x c⌋₊ : ℝ) := fun c => by
    have := Nat.floor_le (hx.2.1 c); linarith
  have hfrac1 : ∀ c, x c - (⌊x c⌋₊ : ℝ) ≤ 1 := fun c => by
    have := Nat.lt_floor_add_one (x c); linarith
  -- per-type count bound
  have hcnt : ∀ t ∈ I.toFinset, (R.count t : ℝ)
      ≤ ∑ c ∈ x.support, (x c - (⌊x c⌋₊ : ℝ)) * (c.count t : ℝ) := by
    intro t ht
    have hb := hx.2.2 t ht
    have hRc : R.count t = I.count t - J.count t := Multiset.count_sub _ _ _
    have hJc : (J.count t : ℝ) = ∑ c ∈ x.support, (⌊x c⌋₊ : ℝ) * (c.count t : ℝ) := by
      rw [hJ, AKd4f0eca3.count_join_principal]; push_cast; rfl
    have hsplit : ∑ c ∈ x.support, (x c - (⌊x c⌋₊ : ℝ)) * (c.count t : ℝ)
        = ∑ c ∈ x.support, x c * (c.count t : ℝ) - J.count t := by
      rw [hJc, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun c _ => by ring
    have hnn : 0 ≤ ∑ c ∈ x.support, (x c - (⌊x c⌋₊ : ℝ)) * (c.count t : ℝ) :=
      Finset.sum_nonneg fun c _ => mul_nonneg (hfrac0 c) (Nat.cast_nonneg _)
    rw [hsplit] at hnn
    rw [hsplit, hRc]
    rcases le_or_gt (I.count t) (J.count t) with h | h
    · rw [Nat.sub_eq_zero_of_le h]
      have : (I.count t : ℝ) ≤ J.count t := by exact_mod_cast h
      push_cast; linarith
    · rw [Nat.cast_sub h.le]; linarith
  have hcnt0 : ∀ t, t ∉ I.toFinset → R.count t = 0 := by
    intro t ht
    have := Multiset.count_le_of_le t hRle
    have h0 : I.count t = 0 := Multiset.count_eq_zero.2 (by simpa using ht)
    omega
  -- packing of I - R
  obtain ⟨P, hP, hPc⟩ := AKd4f0eca3.packing_of_le I hI (principalConfigs x)
    (fun c hc => hx.1 c (AKd4f0eca3.mem_principal hc)) (I - R) (by
      rw [Multiset.le_iff_count]; intro t
      rw [Multiset.count_sub, Multiset.count_sub]; omega)
  refine ⟨P, hP, by rw [hPc, AKd4f0eca3.card_principal], ?_, ?_⟩
  · -- size bound
    have hsubR : R.toFinset ⊆ I.toFinset := Multiset.toFinset_subset.2 (Multiset.subset_of_le hRle)
    have hRsum : SIZE R = ∑ t ∈ I.toFinset, (R.count t : ℝ) * t := by
      unfold SIZE
      rw [Finset.sum_multiset_count_of_subset _ _ hsubR]
      simp [nsmul_eq_mul]
    have hcsum : ∀ c ∈ x.support, c.sum = ∑ t ∈ I.toFinset, (c.count t : ℝ) * t := by
      intro c hc
      rw [Finset.sum_multiset_count_of_subset _ _
        (Multiset.toFinset_subset.2 fun t ht => Multiset.mem_toFinset.2 ((hx.1 c hc).2.1 t ht))]
      simp [nsmul_eq_mul]
    calc SIZE R = ∑ t ∈ I.toFinset, (R.count t : ℝ) * t := hRsum
      _ ≤ ∑ t ∈ I.toFinset,
            (∑ c ∈ x.support, (x c - (⌊x c⌋₊ : ℝ)) * (c.count t : ℝ)) * t := by
          refine Finset.sum_le_sum fun t ht => ?_
          exact mul_le_mul_of_nonneg_right (hcnt t ht)
            (hI t (Multiset.mem_toFinset.1 ht)).1.le
      _ = ∑ c ∈ x.support, (x c - (⌊x c⌋₊ : ℝ)) * c.sum := by
          simp_rw [Finset.sum_mul]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun c hc => ?_
          rw [hcsum c hc, Finset.mul_sum]
          refine Finset.sum_congr rfl fun t _ => by ring
      _ ≤ ∑ c ∈ x.support, (x c - (⌊x c⌋₊ : ℝ)) := by
          refine Finset.sum_le_sum fun c hc => ?_
          have := (hx.1 c hc).2.2
          nlinarith [hfrac0 c]
      _ = lpCost x - (principalCount x : ℝ) := by
          unfold lpCost principalCount
          rw [Finset.sum_sub_distrib]; push_cast; rfl
  · -- OPT bound
    obtain ⟨P', hP', hP'c⟩ := AKd4f0eca3.packing_of_le I hI x.support.val
      (fun c hc => hx.1 c hc) R (by
        rw [Multiset.le_iff_count]; intro t
        rw [AKd4f0eca3.count_join_cons]
        by_cases ht : t ∈ I.toFinset
        · have h1 := hcnt t ht
          have h2 : ∑ c ∈ x.support, (x c - (⌊x c⌋₊ : ℝ)) * (c.count t : ℝ)
              ≤ ∑ c ∈ x.support, (c.count t : ℝ) :=
            Finset.sum_le_sum fun c _ =>
              mul_le_of_le_one_left (Nat.cast_nonneg _) (hfrac1 c)
          have h3 : (R.count t : ℝ) ≤ ((∑ c ∈ x.support, c.count t : ℕ) : ℝ) := by
            push_cast; linarith
          exact_mod_cast h3
        · rw [hcnt0 t ht]; exact Nat.zero_le _)
    have : OPT R ≤ Multiset.card P' := Nat.sInf_le ⟨P', hP', rfl⟩
    rw [hP'c] at this
    exact_mod_cast this
