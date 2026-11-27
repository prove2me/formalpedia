-- Prove2me | solution 1 for MaxPressure.FluidStab.Supplement.nonpreemptive_feasible_extreme
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:22:12.701501+00:00
-- url     : https://prove2.me/submissions/1ad2e5c2-790e-4b6a-b0fb-64c9f430c97b

import Mathlib
import Definitions.Def_MaxPressure_FluidStab_Supplement_Allocations

open MaxPressure
open MaxPressure.FluidStab
open MaxPressure.FluidStab.Supplement

open MeasureTheory Filter Topology

theorem solution
    {I J K : ℕ} (N : FluidStab.Network I J K)
    (hN : N.Standing) (hrev : ReversedLeontief.IsReversedLeontief (reversedNetwork N))
    (s : Snapshot I J) (hphysical : s.Legal N) :
    (feasibleExtremes N s).Nonempty := by
      classical
      obtain ⟨hA01, hB01, hBne, hIS, hAex, hInp, hex, hInpEx, hm, hP, hP0⟩ := hN
      obtain ⟨hz, hU, hzU⟩ := hphysical
      have hrev' : ∀ j, ∃! k, N.A k j = 1 := hrev
      let c : ∀ k, N.inputProc k → Fin J := fun k hk => (hInpEx k hk).choose
      have hc : ∀ k hk, N.A k (c k hk) = 1 := fun k hk => (hInpEx k hk).choose_spec
      let Q : Fin J → Prop := fun j =>
        ∃ k, ∃ hk : N.inputProc k, (∀ j' ∈ s.unfinished, N.A k j' ≠ 1) ∧ c k hk = j
      let a : Fin J → ℝ := fun j => if j ∈ s.unfinished ∨ Q j then 1 else 0
      have hA0 : ∀ k j, 0 ≤ N.A k j := fun k j => by rcases hA01 k j with h | h <;> simp [h]
      have hQ : ∀ j, Q j → ∀ k, N.A k j = 1 →
          N.inputProc k ∧ (∀ j' ∈ s.unfinished, N.A k j' ≠ 1) ∧ ∃ hk, c k hk = j := by
        rintro j ⟨k', hk', hno, rfl⟩ k hk
        have := (hrev' (c k' hk')).unique hk (hc k' hk')
        subst this
        exact ⟨hk', hno, hk', rfl⟩
      have hproc : ∀ k, ∑ j, N.A k j * a j ≤ 1 ∧ (N.inputProc k → ∑ j, N.A k j * a j = 1) := by
        intro k
        by_cases hk0 : ∃ j0 ∈ s.unfinished, N.A k j0 = 1
        · obtain ⟨j0, hj0U, hj0⟩ := hk0
          have heq : ∀ j, N.A k j * a j = if j ∈ s.unfinished then N.A k j else 0 := by
            intro j
            by_cases hjU : j ∈ s.unfinished
            · simp [a, hjU]
            · rcases hA01 k j with h | h
              · simp [h, hjU]
              · have hnQ : ¬ Q j := fun hq => (hQ j hq k h).2.1 j0 hj0U hj0
                simp [a, hjU, hnQ]
          have hsum : ∑ j, N.A k j * a j = ∑ j ∈ s.unfinished, N.A k j := by
            rw [Finset.sum_congr rfl (fun j _ => heq j), ← Finset.sum_filter]
            congr 1
            ext j; simp
          have hge : 1 ≤ ∑ j ∈ s.unfinished, N.A k j := by
            rw [← hj0]; exact Finset.single_le_sum (fun j _ => hA0 k j) hj0U
          have hle := hU k
          exact ⟨by linarith, fun _ => by linarith⟩
        · push Not at hk0
          by_cases hki : N.inputProc k
          · have heq : ∀ j, N.A k j * a j = if j = c k hki then 1 else 0 := by
              intro j
              by_cases hj : j = c k hki
              · subst hj
                have : Q (c k hki) := ⟨k, hki, hk0, rfl⟩
                simp [a, hc k hki, this]
              · rcases hA01 k j with h | h
                · simp [h, hj]
                · have hjU : j ∉ s.unfinished := fun hjU => hk0 j hjU h
                  have hnQ : ¬ Q j := by
                    intro hq
                    obtain ⟨_, _, hk', hk'eq⟩ := hQ j hq k h
                    exact hj hk'eq.symm
                  simp [a, hjU, hnQ, hj]
            rw [Finset.sum_congr rfl (fun j _ => heq j)]
            simp
          · have heq : ∀ j, N.A k j * a j = 0 := by
              intro j
              rcases hA01 k j with h | h
              · simp [h]
              · have hjU : j ∉ s.unfinished := fun hjU => hk0 j hjU h
                have hnQ : ¬ Q j := fun hq => hki (hQ j hq k h).1
                simp [a, hjU, hnQ]
            simp [heq, hki]
      have ha01 : ∀ j, a j = 0 ∨ a j = 1 := by
        intro j; by_cases h : j ∈ s.unfinished ∨ Q j <;> simp [a, h]
      have hmem : a ∈ allocSet N :=
        ⟨fun j => by rcases ha01 j with h | h <;> simp [h],
          fun k => (hproc k).1, fun k hk => (hproc k).2 hk⟩
      have hle1 : ∀ x ∈ allocSet N, ∀ j, x j ≤ 1 := by
        intro x hx j
        obtain ⟨k, hk⟩ := hAex j
        have := Finset.single_le_sum (f := fun j' => N.A k j' * x j')
          (fun j' _ => mul_nonneg (hA0 k j') (hx.1 j')) (Finset.mem_univ j)
        simp only [hk, one_mul] at this
        linarith [hx.2.1 k]
      have hext : a ∈ extremeAllocs N := by
        rw [extremeAllocs, mem_extremePoints]
        refine ⟨hmem, ?_⟩
        intro x1 hx1 x2 hx2 hseg
        obtain ⟨t1, t2, ht1, ht2, ht, hx⟩ := hseg
        have hj : ∀ j, t1 * x1 j + t2 * x2 j = a j := fun j => by
          have := congrFun hx j; simpa using this
        have key : ∀ j, x1 j = a j ∧ x2 j = a j := by
          intro j
          have h1 := hle1 x1 hx1 j
          have h2 := hle1 x2 hx2 j
          have n1 := hx1.1 j
          have n2 := hx2.1 j
          have e := hj j
          rcases ha01 j with h | h
          · rw [h] at e ⊢
            have p1 : t1 * x1 j = 0 := by nlinarith [mul_nonneg ht1.le n1, mul_nonneg ht2.le n2]
            have p2 : t2 * x2 j = 0 := by nlinarith [mul_nonneg ht1.le n1, mul_nonneg ht2.le n2]
            exact ⟨(mul_eq_zero.1 p1).resolve_left ht1.ne', (mul_eq_zero.1 p2).resolve_left ht2.ne'⟩
          · rw [h] at e ⊢
            have q1 := mul_nonneg ht1.le (sub_nonneg.2 h1)
            have q2 := mul_nonneg ht2.le (sub_nonneg.2 h2)
            have p1 : t1 * (1 - x1 j) = 0 := by nlinarith
            have p2 : t2 * (1 - x2 j) = 0 := by nlinarith
            constructor
            · have := (mul_eq_zero.1 p1).resolve_left ht1.ne'; linarith
            · have := (mul_eq_zero.1 p2).resolve_left ht2.ne'; linarith
        exact ⟨funext fun j => (key j).1, funext fun j => (key j).2⟩
      have hfresh : ∀ i, (∑ j : Fin J, if 0 < a j ∧ j ∉ s.unfinished then N.B j i.succ else 0) ≤
          s.z i - ∑ j ∈ s.unfinished, N.B j i.succ := by
        intro i
        have h0 : ∀ j, (if 0 < a j ∧ j ∉ s.unfinished then N.B j i.succ else 0) = 0 := by
          intro j
          by_cases hc' : 0 < a j ∧ j ∉ s.unfinished
          · rw [if_pos hc']
            have hq : Q j := by
              by_contra hnq
              have : a j = 0 := by simp [a, hc'.2, hnq]
              linarith [hc'.1]
            obtain ⟨k, hk, _, hkj⟩ := hq
            have hA : N.A k j = 1 := hkj ▸ hc k hk
            exact ((hInp k j hA).1 hk).2 i
          · rw [if_neg hc']
        rw [Finset.sum_eq_zero (fun j _ => h0 j)]
        linarith [hzU i]
      exact ⟨a, hext, hmem, fun _ j hj => by simp [a, hj], hfresh⟩
