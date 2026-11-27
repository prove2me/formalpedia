-- Prove2me | solution 1 for HeteroBass.HetP.Supplement.lemma_12
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:20:40.708841+00:00
-- url     : https://prove2.me/submissions/bdb28f2b-1a5e-47f1-8064-67373c6e0dfb

import Mathlib
import Definitions.Def_HeteroBass_HetP_Supplement_IntervalIVP

open HeteroBass
open HeteroBass.HetP
open HeteroBass.HetP.Supplement

theorem solution {M : ℕ} (hM : 2 ≤ M) (p : Fin M → ℝ)
    (Q : Fin M → Fin M → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hQ : ∀ k j, k ≠ j → 0 ≤ Q k j)
    (hin : ∀ j, 0 < ∑ k ∈ Finset.univ.erase j, Q k j)
    (hcircle : IsTwoSidedCircle Q) :
    SolvesCircleIVP p Q (circleObservation p Q) ∧
    (∀ j : Fin M, ∀ m n : ℕ, m + n + 1 = M → ∀ t : ℝ, 0 ≤ t →
      intervalNonadoption p Q j m n t = subsetNonadoption p Q Finset.univ t) ∧
    (∀ j : Fin M, ∀ m n : ℕ, m + n + 1 ≤ M →
      intervalNonadoption p Q j m n 0 = 1) := by
        classical
        have hM0 : (0 : ℤ) < M := by exact_mod_cast (by omega : 0 < M)
        -- cyclic arithmetic
        have hval : ∀ (j : Fin M) (x : ℤ), ((cyclicShift j x).val : ℤ) = ((j.val : ℤ) + x) % (M : ℤ) := by
          intro j x
          show ((((j.val : ℤ) + x) % (M : ℤ)).toNat : ℤ) = _
          exact Int.toNat_of_nonneg (Int.emod_nonneg _ (ne_of_gt hM0))
        have hext : ∀ i j : Fin M, (i.val : ℤ) = (j.val : ℤ) → i = j := by
          intro i j h
          exact Fin.ext (by exact_mod_cast h)
        have hadd : ∀ (j : Fin M) (x y : ℤ), cyclicShift (cyclicShift j x) y = cyclicShift j (x + y) := by
          intro j x y
          apply hext
          rw [hval, hval, hval, Int.emod_add_emod, add_assoc]
        have hper : ∀ (j : Fin M) (x : ℤ), cyclicShift j (x + M) = cyclicShift j x := by
          intro j x
          apply hext
          rw [hval, hval, ← add_assoc, Int.add_emod_right]
        have hinj : ∀ (j : Fin M) (x y : ℤ), x < y + M → y < x + M →
            cyclicShift j x = cyclicShift j y → x = y := by
          intro j x y h1 h2 h
          have h3 : ((cyclicShift j x).val : ℤ) = ((cyclicShift j y).val : ℤ) := by rw [h]
          rw [hval, hval] at h3
          have h4 : (M : ℤ) ∣ (((j.val : ℤ) + x) - ((j.val : ℤ) + y)) :=
            Int.dvd_of_emod_eq_zero (Int.emod_eq_emod_iff_emod_sub_eq_zero.mp h3)
          have h5 : ((j.val : ℤ) + x) - ((j.val : ℤ) + y) = x - y := by ring
          rw [h5] at h4
          have h6 : x - y = 0 := Int.eq_zero_of_abs_lt_dvd h4 (by rw [abs_lt]; constructor <;> linarith)
          linarith
        have hsurj : ∀ (j i : Fin M) (c : ℤ), ∃ s : ℤ, c ≤ s ∧ s < c + M ∧ i = cyclicShift j s := by
          intro j i c
          refine ⟨c + ((i.val : ℤ) - j.val - c) % M, ?_, ?_, ?_⟩
          · have := Int.emod_nonneg ((i.val : ℤ) - j.val - c) (ne_of_gt hM0)
            linarith
          · have := Int.emod_lt_of_pos ((i.val : ℤ) - j.val - c) hM0
            linarith
          · apply hext
            rw [hval, ← add_assoc, Int.add_emod_emod]
            have h1 : (j.val : ℤ) + c + ((i.val : ℤ) - j.val - c) = i.val := by ring
            rw [h1]
            symm
            exact Int.emod_eq_of_lt (by positivity) (by exact_mod_cast i.isLt)
        have hmem : ∀ (j : Fin M) (m n : ℕ) (i : Fin M), i ∈ intervalSet j m n ↔
            ∃ s : ℤ, -(m : ℤ) ≤ s ∧ s ≤ n ∧ i = cyclicShift j s := by
          intro j m n i
          unfold intervalSet
          rw [Finset.mem_image]
          constructor
          · rintro ⟨k, hk, rfl⟩
            rw [Finset.mem_range] at hk
            exact ⟨(k : ℤ) - m, by omega, by omega, rfl⟩
          · rintro ⟨s, h1, h2, rfl⟩
            refine ⟨(s + m).toNat, ?_, ?_⟩
            · rw [Finset.mem_range]; omega
            · congr 1; omega
        have hfull : ∀ (j : Fin M) (m n : ℕ), m + n + 1 = M → intervalSet j m n = Finset.univ := by
          intro j m n h
          ext i
          simp only [Finset.mem_univ, iff_true]
          rw [hmem]
          obtain ⟨s, h1, h2, h3⟩ := hsurj j i (-(m : ℤ))
          exact ⟨s, h1, by omega, h3⟩
        have hleft : ∀ (j : Fin M) (m n : ℕ), intervalSet j (m + 1) n =
            insert (cyclicShift j (-((m : ℤ) + 1))) (intervalSet j m n) := by
          intro j m n
          ext i
          rw [Finset.mem_insert, hmem, hmem]
          constructor
          · rintro ⟨s, h1, h2, h3⟩
            by_cases h : s = -((m : ℤ) + 1)
            · left; rw [h3, h]
            · right; push_cast at h1; exact ⟨s, by omega, h2, h3⟩
          · rintro (h | ⟨s, h1, h2, h3⟩)
            · exact ⟨-((m : ℤ) + 1), by push_cast; omega, by omega, h⟩
            · exact ⟨s, by push_cast; omega, h2, h3⟩
        have hright : ∀ (j : Fin M) (m n : ℕ), intervalSet j m (n + 1) =
            insert (cyclicShift j ((n : ℤ) + 1)) (intervalSet j m n) := by
          intro j m n
          ext i
          rw [Finset.mem_insert, hmem, hmem]
          constructor
          · rintro ⟨s, h1, h2, h3⟩
            by_cases h : s = (n : ℤ) + 1
            · left; rw [h3, h]
            · right; push_cast at h2; exact ⟨s, h1, by omega, h3⟩
          · rintro (h | ⟨s, h1, h2, h3⟩)
            · exact ⟨(n : ℤ) + 1, by omega, by push_cast; omega, h⟩
            · exact ⟨s, h1, by push_cast; omega, h3⟩
        -- initial data
        have hinit : ∀ U : Finset (Fin M), subsetNonadoption p Q U 0 = 1 := by
          intro U
          unfold subsetNonadoption transition
          rw [zero_smul, NormedSpace.exp_zero]
          rw [Finset.sum_eq_single ∅]
          · simp
          · intro A _ hA
            rw [Matrix.one_apply_ne (Ne.symm hA)]
            simp
          · simp
        -- generator action
        have hgen : ∀ (f : Finset (Fin M) → ℝ) (S : Finset (Fin M)),
            ∑ A, generator p Q S A * f A =
              ∑ j ∈ Sᶜ, adoptRate p Q S j * (f (insert j S) - f S) := by
          intro f S
          have h1 : ∀ A, generator p Q S A * f A =
              adopterJumpRate p Q S A * f A +
              (if S = A then -(∑ U, adopterJumpRate p Q S U) * f S else 0) := by
            intro A
            have hSS : adopterJumpRate p Q S S = 0 := by
              unfold adopterJumpRate
              apply Finset.sum_eq_zero
              intro j hj
              rw [Finset.mem_compl] at hj
              rw [if_neg]
              intro h
              apply hj
              rw [h]
              exact Finset.mem_insert_self _ _
            unfold generator finiteJumpGenerator
            by_cases h : S = A
            · subst h
              rw [if_pos rfl, if_pos rfl, hSS]
              have : ∑ U, (if U = S then 0 else adopterJumpRate p Q S U) = ∑ U, adopterJumpRate p Q S U := by
                apply Finset.sum_congr rfl
                intro U _
                split_ifs with h
                · rw [h, hSS]
                · rfl
              rw [this]; ring
            · rw [if_neg h, if_neg h]; ring
          have h2 : ∀ g : Finset (Fin M) → ℝ, ∑ A, adopterJumpRate p Q S A * g A =
              ∑ j ∈ Sᶜ, adoptRate p Q S j * g (insert j S) := by
            intro g
            unfold adopterJumpRate
            simp_rw [Finset.sum_mul]
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl
            intro j _
            rw [Finset.sum_eq_single (insert j S)]
            · rw [if_pos rfl]
            · intro A _ hA
              rw [if_neg hA, zero_mul]
            · simp
          have h3 : ∑ U, adopterJumpRate p Q S U = ∑ j ∈ Sᶜ, adoptRate p Q S j := by
            have := h2 (fun _ => 1)
            simpa using this
          rw [Finset.sum_congr rfl (fun A _ => h1 A), Finset.sum_add_distrib, h2, Finset.sum_ite_eq,
            if_pos (Finset.mem_univ _), h3]
          rw [neg_mul, Finset.sum_mul, ← sub_eq_add_neg, ← Finset.sum_sub_distrib]
          apply Finset.sum_congr rfl
          intro j _
          ring
        -- generator on the indicator
        have hind : ∀ (U S : Finset (Fin M)),
            ∑ A, generator p Q S A * (if Disjoint A U then (1:ℝ) else 0) =
              -(∑ i ∈ U, p i) * (if Disjoint S U then 1 else 0)
              - ∑ k ∈ Uᶜ, ∑ i ∈ U, Q k i * ((if Disjoint S U then (1:ℝ) else 0) -
                  (if Disjoint S (insert k U) then 1 else 0)) := by
          intro U S
          rw [hgen]
          by_cases hSU : Disjoint S U
          · have hUS : U ⊆ Sᶜ := by
              intro i hi
              rw [Finset.mem_compl]
              exact fun h => Finset.disjoint_left.mp hSU h hi
            have hSUc : S ⊆ Uᶜ := by
              intro i hi
              rw [Finset.mem_compl]
              exact fun h => Finset.disjoint_left.mp hSU hi h
            rw [← Finset.sum_subset hUS]
            · have e1 : ∀ j ∈ U, adoptRate p Q S j * ((if Disjoint (insert j S) U then (1:ℝ) else 0) -
                  (if Disjoint S U then 1 else 0)) = - p j - ∑ k ∈ S, Q k j := by
                intro j hj
                rw [if_neg, if_pos hSU]
                · unfold adoptRate; ring
                · intro h
                  exact Finset.disjoint_left.mp h (Finset.mem_insert_self _ _) hj
              rw [Finset.sum_congr rfl e1, Finset.sum_sub_distrib, Finset.sum_neg_distrib]
              rw [if_pos hSU, mul_one]
              congr 1
              rw [Finset.sum_comm]
              rw [← Finset.sum_subset hSUc]
              · apply Finset.sum_congr rfl
                intro k hk
                apply Finset.sum_congr rfl
                intro i _
                rw [if_neg]
                · ring
                · intro h
                  exact Finset.disjoint_left.mp h hk (Finset.mem_insert_self _ _)
              · intro k _ hk
                apply Finset.sum_eq_zero
                intro i _
                rw [if_pos]
                · ring
                · rw [Finset.disjoint_insert_right]
                  exact ⟨hk, hSU⟩
            · intro j _ hj
              rw [if_pos hSU, if_pos]
              · ring
              · rw [Finset.disjoint_insert_left]
                exact ⟨hj, hSU⟩
          · have e1 : ∀ k, ¬ Disjoint S (insert k U) := by
              intro k h
              rw [Finset.disjoint_insert_right] at h
              exact hSU h.2
            have e2 : ∀ k, ¬ Disjoint (insert k S) U := by
              intro k h
              rw [Finset.disjoint_insert_left] at h
              exact hSU h.2
            simp [hSU, e1, e2]
        -- derivative of the transition matrix
        have htrans : ∀ (t : ℝ) (A : Finset (Fin M)),
            HasDerivAt (fun s => transition p Q s ∅ A)
              (∑ S, transition p Q t ∅ S * generator p Q S A) t := by
          intro t A
          let _ : NormedRing (Matrix (Finset (Fin M)) (Finset (Fin M)) ℝ) := Matrix.linftyOpNormedRing
          let _ : NormedAlgebra ℝ (Matrix (Finset (Fin M)) (Finset (Fin M)) ℝ) :=
            Matrix.linftyOpNormedAlgebra
          have h := hasDerivAt_exp_smul_const (𝕂 := ℝ) (generator p Q) t
          have h2 := (LinearMap.toContinuousLinearMap
            (Matrix.entryLinearMap ℝ ℝ (∅ : Finset (Fin M)) A)).hasFDerivAt.comp_hasDerivAt t h
          exact h2
        -- master equation
        have hmaster : ∀ (U : Finset (Fin M)) (t : ℝ),
            HasDerivAt (fun s => subsetNonadoption p Q U s)
              (-(∑ i ∈ U, p i) * subsetNonadoption p Q U t
                - ∑ k ∈ Uᶜ, ∑ i ∈ U, Q k i * (subsetNonadoption p Q U t -
                  subsetNonadoption p Q (insert k U) t)) t := by
          intro U t
          have hsub : ∀ (V : Finset (Fin M)) (s : ℝ), subsetNonadoption p Q V s =
              ∑ A, transition p Q s ∅ A * (if Disjoint A V then (1:ℝ) else 0) := by
            intro V s
            unfold subsetNonadoption
            apply Finset.sum_congr rfl
            intro A _
            split_ifs <;> simp
          have h1 : HasDerivAt (fun s => ∑ A, transition p Q s ∅ A * (if Disjoint A U then (1:ℝ) else 0))
              (∑ A, (∑ S, transition p Q t ∅ S * generator p Q S A) * (if Disjoint A U then (1:ℝ) else 0)) t := by
            apply HasDerivAt.fun_sum
            intro A _
            exact (htrans t A).mul_const _
          have h2 : (fun s => subsetNonadoption p Q U s) =
              (fun s => ∑ A, transition p Q s ∅ A * (if Disjoint A U then (1:ℝ) else 0)) := by
            funext s; exact hsub U s
          rw [h2]
          convert h1 using 1
          have h3 : ∑ A, (∑ S, transition p Q t ∅ S * generator p Q S A) * (if Disjoint A U then (1:ℝ) else 0)
              = ∑ S, transition p Q t ∅ S * ∑ A, generator p Q S A * (if Disjoint A U then (1:ℝ) else 0) := by
            simp_rw [Finset.sum_mul, Finset.mul_sum]
            rw [Finset.sum_comm]
            simp_rw [mul_assoc]
          rw [h3]
          simp_rw [hind, hsub]
          simp only [mul_sub (transition _ _ _ _ _), Finset.sum_sub_distrib]
          congr 1
          · rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro S _
            ring
          · simp only [Finset.mul_sum]
            symm
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl
            intro k _
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl
            intro i _
            symm
            rw [← Finset.sum_sub_distrib, Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro S _
            ring
        refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
        · intro c
          rcases c with _ | ⟨j, mn⟩
          · exact hinit _
          · exact hinit _
        · intro t ht c
          apply HasDerivAt.hasDerivWithinAt
          rcases c with _ | ⟨j, mn⟩
          · have h := hmaster Finset.univ t
            simpa [circleRHS, circleObservation] using h
          · obtain ⟨⟨m, n⟩, hmn⟩ := mn
            obtain ⟨m, hm⟩ := m
            obtain ⟨n, hn⟩ := n
            simp only at hmn
            have h := hmaster (intervalSet j m n) t
            have hcoordL : circleObservation p Q t (intervalCoord j (m + 1) n) =
                subsetNonadoption p Q (insert (cyclicShift j (-((m : ℤ) + 1))) (intervalSet j m n)) t := by
              rw [← hleft]
              unfold intervalCoord
              split_ifs with h
              · rfl
              · rw [hfull j (m + 1) n (by omega)]; rfl
            have hcoordR : circleObservation p Q t (intervalCoord j m (n + 1)) =
                subsetNonadoption p Q (insert (cyclicShift j ((n : ℤ) + 1)) (intervalSet j m n)) t := by
              rw [← hright]
              unfold intervalCoord
              split_ifs with h
              · rfl
              · rw [hfull j m (n + 1) (by omega)]; rfl
            have hsum : ∀ g : Fin M → ℝ,
                ∑ k ∈ (intervalSet j m n)ᶜ, ∑ i ∈ intervalSet j m n, Q k i * g k =
                Q (cyclicShift j (-((m : ℤ) + 1))) (cyclicShift j (-(m : ℤ))) *
                    g (cyclicShift j (-((m : ℤ) + 1))) +
                (if M = 2 then 0 else Q (cyclicShift j ((n : ℤ) + 1)) (cyclicShift j (n : ℤ))) *
                    g (cyclicShift j ((n : ℤ) + 1)) := by
              intro g
              have hjm : cyclicShift j (-(m : ℤ)) ∈ intervalSet j m n := by
                rw [hmem]; exact ⟨_, le_refl _, by omega, rfl⟩
              have hjn : cyclicShift j (n : ℤ) ∈ intervalSet j m n := by
                rw [hmem]; exact ⟨_, by omega, le_refl _, rfl⟩
              have ha : cyclicShift j (-((m : ℤ) + 1)) ∉ intervalSet j m n := by
                rw [hmem]
                rintro ⟨s, h1, h2, h3⟩
                have := hinj j _ _ (by omega) (by omega) h3
                omega
              have hb : cyclicShift j ((n : ℤ) + 1) ∉ intervalSet j m n := by
                rw [hmem]
                rintro ⟨s, h1, h2, h3⟩
                have := hinj j _ _ (by omega) (by omega) h3
                omega
              have hzero : ∀ k i, k ∉ intervalSet j m n → i ∈ intervalSet j m n →
                  (k, i) ≠ (cyclicShift j (-((m : ℤ) + 1)), cyclicShift j (-(m : ℤ))) →
                  (k, i) ≠ (cyclicShift j ((n : ℤ) + 1), cyclicShift j (n : ℤ)) → Q k i = 0 := by
                intro k i hk hi h1 h2
                rw [hmem] at hi
                obtain ⟨r, hr1, hr2, rfl⟩ := hi
                apply hcircle
                · rintro rfl
                  exact hk ((hmem _ _ _ _).mpr ⟨r, hr1, hr2, rfl⟩)
                · rw [hadd]
                  rintro rfl
                  by_cases h : r = -(m : ℤ)
                  · subst h
                    apply h1
                    rw [neg_add]
                  · exact hk ((hmem _ _ _ _).mpr ⟨r + -1, by omega, by omega, rfl⟩)
                · rw [hadd]
                  rintro rfl
                  by_cases h : r = (n : ℤ)
                  · subst h
                    exact h2 rfl
                  · exact hk ((hmem _ _ _ _).mpr ⟨r + 1, by omega, by omega, rfl⟩)
              rw [← Finset.sum_product']
              have hsubs : ({(cyclicShift j (-((m : ℤ) + 1)), cyclicShift j (-(m : ℤ))),
                  (cyclicShift j ((n : ℤ) + 1), cyclicShift j (n : ℤ))} : Finset (Fin M × Fin M)) ⊆
                  (intervalSet j m n)ᶜ ×ˢ intervalSet j m n := by
                intro x hx
                rw [Finset.mem_insert, Finset.mem_singleton] at hx
                rw [Finset.mem_product, Finset.mem_compl]
                rcases hx with rfl | rfl
                · exact ⟨ha, hjm⟩
                · exact ⟨hb, hjn⟩
              rw [← Finset.sum_subset hsubs]
              · by_cases h2 : M = 2
                · have hm0 : m = 0 := by omega
                  have hn0 : n = 0 := by omega
                  subst hm0 hn0
                  have e : cyclicShift j (-(((0 : ℕ) : ℤ) + 1)) = cyclicShift j (((0 : ℕ) : ℤ) + 1) := by
                    rw [← hper j (-(((0 : ℕ) : ℤ) + 1))]
                    congr 1
                    push_cast
                    omega
                  rw [if_pos h2, e]
                  have e0 : (-((0 : ℕ) : ℤ)) = ((0 : ℕ) : ℤ) := by simp
                  rw [e0]
                  simp
                · rw [if_neg h2, Finset.sum_pair]
                  intro h
                  rw [Prod.mk.injEq] at h
                  have q1 := hinj j _ _ (by omega) (by omega) h.2
                  have q2 := hinj j _ _ (by omega) (by omega) h.1
                  omega
              · rintro ⟨k, i⟩ hx hx'
                rw [Finset.mem_product, Finset.mem_compl] at hx
                rw [Finset.mem_insert, Finset.mem_singleton, not_or] at hx'
                simp only
                rw [hzero k i hx.1 hx.2 hx'.1 hx'.2, zero_mul]
            rw [hsum] at h
            rw [← hcoordL, ← hcoordR] at h
            refine h.congr_deriv ?_
            unfold circleRHS
            have hself : circleObservation p Q t (some (j, ⟨(⟨m, hm⟩, ⟨n, hn⟩), hmn⟩)) =
                subsetNonadoption p Q (intervalSet j m n) t := rfl
            rw [hself]
            ring
        · intro j m n h t _
          unfold intervalNonadoption
          rw [hfull j m n h]
        · intro j m n _
          exact hinit _
