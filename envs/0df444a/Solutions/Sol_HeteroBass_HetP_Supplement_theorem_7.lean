-- Prove2me | solution 1 for HeteroBass.HetP.Supplement.theorem_7
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:20:55.009483+00:00
-- url     : https://prove2.me/submissions/bba19aff-c2c3-4966-9b60-ff8d522f1845

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
    ∃ u : ℝ → CircleCoord M → ℝ,
      SolvesCircleIVP p Q u ∧
      (∀ v : ℝ → CircleCoord M → ℝ, SolvesCircleIVP p Q v →
        ∀ t : ℝ, 0 ≤ t → v t = u t) ∧
      (∀ t : ℝ, 0 ≤ t → u t = circleObservation p Q t) ∧
      (∀ t : ℝ, 0 ≤ t → expectedFraction p Q t =
        1 - (1 / (M : ℝ)) * ∑ j : Fin M, u t (intervalCoord j 0 0)) := by
          classical
          -- derivative of the transition matrix entries
          have hder : ∀ (t : ℝ) (A : Finset (Fin M)),
              HasDerivAt (fun s => transition p Q s ∅ A)
                (∑ B, transition p Q t ∅ B * generator p Q B A) t := by
            intro t A
            let _ : NormedRing (Matrix (Finset (Fin M)) (Finset (Fin M)) ℝ) := Matrix.linftyOpNormedRing
            let _ : NormedAlgebra ℝ (Matrix (Finset (Fin M)) (Finset (Fin M)) ℝ) :=
              Matrix.linftyOpNormedAlgebra
            have h := hasDerivAt_exp_smul_const (𝕂 := ℝ) (generator p Q) t
            have h2 : HasDerivAt (fun s : ℝ => transition p Q s)
                (transition p Q t * generator p Q) t := h
            have h3 := (hasDerivAt_pi.1 ((hasDerivAt_pi.1 h2) ∅)) A
            simpa [Matrix.mul_apply] using h3
          have hzero : ∀ A : Finset (Fin M), transition p Q 0 ∅ A = if A = ∅ then 1 else 0 := by
            intro A
            unfold transition
            rw [zero_smul, NormedSpace.exp_zero, Matrix.one_apply]
            simp [eq_comm]
          -- generator applied to a function
          have hgen : ∀ (h : Finset (Fin M) → ℝ) (B : Finset (Fin M)),
              ∑ A, generator p Q B A * h A = ∑ i ∈ Bᶜ, adoptRate p Q B i * (h (insert i B) - h B) := by
            intro h B
            have h1 : ∀ A, generator p Q B A * h A =
                (if A = B then 0 else adopterJumpRate p Q B A) * h A +
                (if B = A then (-∑ U, if U = B then 0 else adopterJumpRate p Q B U) * h A else 0) := by
              intro A
              unfold generator finiteJumpGenerator
              by_cases hBA : B = A
              · simp [hBA]
              · simp [hBA, Ne.symm hBA]
            have h2 : ∀ U, (if U = B then 0 else adopterJumpRate p Q B U) =
                ∑ i ∈ Bᶜ, if U = insert i B then adoptRate p Q B i else 0 := by
              intro U
              unfold adopterJumpRate
              split_ifs with hU
              · symm
                apply Finset.sum_eq_zero
                intro i hi
                rw [if_neg]
                rw [hU]
                intro h
                rw [Finset.mem_compl] at hi
                exact hi (h ▸ Finset.mem_insert_self i B)
              · rfl
            have h3 : ∀ g : Finset (Fin M) → ℝ,
                ∑ U, (if U = B then 0 else adopterJumpRate p Q B U) * g U =
                ∑ i ∈ Bᶜ, adoptRate p Q B i * g (insert i B) := by
              intro g
              simp_rw [h2, Finset.sum_mul]
              rw [Finset.sum_comm]
              apply Finset.sum_congr rfl
              intro i _
              simp [ite_mul]
            have h4 := h3 (fun _ => 1)
            simp only [mul_one] at h4
            simp_rw [h1]
            rw [Finset.sum_add_distrib, h3, Finset.sum_ite_eq, if_pos (Finset.mem_univ _), h4]
            simp_rw [mul_sub]
            rw [Finset.sum_sub_distrib, ← Finset.sum_mul]
            ring
          -- master equation
          have hmaster : ∀ (U : Finset (Fin M)) (t : ℝ),
              HasDerivAt (fun s => subsetNonadoption p Q U s)
                (-(∑ i ∈ U, p i) * subsetNonadoption p Q U t
                  - ∑ k ∈ Uᶜ, (∑ i ∈ U, Q k i) *
                    (subsetNonadoption p Q U t - subsetNonadoption p Q (insert k U) t)) t := by
            intro U t
            have hS : ∀ (V : Finset (Fin M)) (s : ℝ), subsetNonadoption p Q V s =
                ∑ A, transition p Q s ∅ A * (if Disjoint A V then 1 else 0) := by
              intro V s
              unfold subsetNonadoption
              simp
            have h1 : HasDerivAt (fun s => subsetNonadoption p Q U s)
                (∑ A, (∑ B, transition p Q t ∅ B * generator p Q B A) * (if Disjoint A U then 1 else 0)) t := by
              simp_rw [hS]
              apply HasDerivAt.fun_sum
              intro A _
              exact (hder t A).mul_const _
            have hloc : ∀ B : Finset (Fin M),
                ∑ i ∈ Bᶜ, adoptRate p Q B i *
                  ((if Disjoint (insert i B) U then (1:ℝ) else 0) - if Disjoint B U then 1 else 0) =
                -(∑ i ∈ U, p i) * (if Disjoint B U then 1 else 0)
                  - ∑ k ∈ Uᶜ, (∑ i ∈ U, Q k i) *
                    ((if Disjoint B U then 1 else 0) - if Disjoint B (insert k U) then 1 else 0) := by
              intro B
              by_cases hB : Disjoint B U
              · have e1 : ∀ i, Disjoint (insert i B) U ↔ i ∉ U := by
                  intro i
                  rw [Finset.disjoint_insert_left]
                  exact and_iff_left hB
                have e2 : ∀ k, Disjoint B (insert k U) ↔ k ∉ B := by
                  intro k
                  rw [Finset.disjoint_insert_right]
                  exact and_iff_left hB
                simp_rw [e1, e2, if_pos hB]
                have l : ∑ i ∈ Bᶜ, adoptRate p Q B i * ((if i ∉ U then (1:ℝ) else 0) - 1) =
                    - ∑ i ∈ U, adoptRate p Q B i := by
                  rw [← Finset.sum_neg_distrib]
                  symm
                  apply Finset.sum_subset_zero_on_sdiff
                  · intro i hi
                    rw [Finset.mem_compl]
                    exact fun h => Finset.disjoint_left.1 hB h hi
                  · intro i hi
                    rw [Finset.mem_sdiff] at hi
                    simp [hi.2]
                  · intro i hi
                    simp [hi]
                have r : ∑ k ∈ Uᶜ, (∑ i ∈ U, Q k i) * ((1:ℝ) - if k ∉ B then 1 else 0) =
                    ∑ k ∈ B, ∑ i ∈ U, Q k i := by
                  symm
                  apply Finset.sum_subset_zero_on_sdiff
                  · intro i hi
                    rw [Finset.mem_compl]
                    exact fun h => Finset.disjoint_left.1 hB hi h
                  · intro i hi
                    rw [Finset.mem_sdiff] at hi
                    simp [hi.2]
                  · intro i hi
                    simp [hi]
                rw [l, r, Finset.sum_comm]
                unfold adoptRate
                rw [Finset.sum_add_distrib]
                ring
              · have e1 : ∀ i, ¬ Disjoint (insert i B) U := by
                  intro i h
                  exact hB (Finset.disjoint_insert_left.1 h).2
                have e2 : ∀ k, ¬ Disjoint B (insert k U) := by
                  intro k h
                  exact hB (Finset.disjoint_insert_right.1 h).2
                simp [e1, e2, hB]
            convert h1 using 1
            have h2 : (∑ A, (∑ B, transition p Q t ∅ B * generator p Q B A) *
                  (if Disjoint A U then (1:ℝ) else 0)) =
                ∑ B, transition p Q t ∅ B * (∑ i ∈ Bᶜ, adoptRate p Q B i *
                  ((if Disjoint (insert i B) U then (1:ℝ) else 0) - if Disjoint B U then 1 else 0)) := by
              simp_rw [Finset.sum_mul]
              rw [Finset.sum_comm]
              apply Finset.sum_congr rfl
              intro B _
              rw [← hgen (fun A => if Disjoint A U then (1:ℝ) else 0) B, Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro A _
              ring
            rw [h2]
            simp_rw [hloc, hS]
            have hk : ∑ k ∈ Uᶜ, (∑ i ∈ U, Q k i) *
                ((∑ A, transition p Q t ∅ A * (if Disjoint A U then (1:ℝ) else 0)) -
                  ∑ A, transition p Q t ∅ A * (if Disjoint A (insert k U) then (1:ℝ) else 0)) =
                ∑ B, transition p Q t ∅ B * ∑ k ∈ Uᶜ, (∑ i ∈ U, Q k i) *
                  ((if Disjoint B U then (1:ℝ) else 0) - if Disjoint B (insert k U) then 1 else 0) := by
              simp_rw [Finset.mul_sum (s := Uᶜ)]
              rw [Finset.sum_comm]
              apply Finset.sum_congr rfl
              intro k _
              rw [← Finset.sum_sub_distrib, Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro B _
              ring
            rw [hk, Finset.mul_sum, ← Finset.sum_sub_distrib]
            apply Finset.sum_congr rfl
            intro B _
            ring
          have hinit : ∀ U : Finset (Fin M), subsetNonadoption p Q U 0 = 1 := by
            intro U
            unfold subsetNonadoption
            rw [Finset.sum_eq_single ∅]
            · simp [hzero]
            · intro A _ hA
              simp [hzero, hA]
            · simp
          have htot : ∀ t : ℝ, ∑ A, transition p Q t ∅ A = 1 := by
            intro t
            have hd : ∀ s, HasDerivAt (fun s => subsetNonadoption p Q ∅ s) 0 s := by
              intro s
              simpa using hmaster ∅ s
            have hc := is_const_of_deriv_eq_zero (fun s => (hd s).differentiableAt)
              (fun s => (hd s).deriv) t 0
            simp only [hinit] at hc
            rw [← hc]
            simp [subsetNonadoption]
          -- cyclic arithmetic
          have hMpos : (0:ℤ) < M := by omega
          have hcv : ∀ (j : Fin M) (a : ℤ), ((cyclicShift j a).val : ℤ) = ((j.val : ℤ) + a) % (M:ℤ) := by
            intro j a
            unfold cyclicShift
            simp only
            exact Int.toNat_of_nonneg (Int.emod_nonneg _ (ne_of_gt hMpos))
          have hcadd : ∀ (j : Fin M) (a b : ℤ), cyclicShift (cyclicShift j a) b = cyclicShift j (a+b) := by
            intro j a b
            apply Fin.ext
            have : ((cyclicShift (cyclicShift j a) b).val : ℤ) = ((cyclicShift j (a+b)).val : ℤ) := by
              rw [hcv, hcv, hcv, Int.emod_add_emod, add_assoc]
            exact_mod_cast this
          have hceq : ∀ (j : Fin M) (a b : ℤ), cyclicShift j a = cyclicShift j b ↔ (M:ℤ) ∣ a - b := by
            intro j a b
            have e : cyclicShift j a = cyclicShift j b ↔
                ((j.val : ℤ) + a) % (M:ℤ) = ((j.val : ℤ) + b) % (M:ℤ) := by
              rw [← hcv, ← hcv, Fin.ext_iff]
              norm_cast
            rw [e, Int.emod_eq_emod_iff_emod_sub_eq_zero, ← Int.dvd_iff_emod_eq_zero]
            have : (j.val:ℤ) + a - (j.val + b) = a - b := by ring
            rw [this]
          have hczero : ∀ j : Fin M, cyclicShift j 0 = j := by
            intro j
            apply Fin.ext
            have : ((cyclicShift j 0).val : ℤ) = (j.val : ℤ) := by
              rw [hcv, add_zero]
              exact Int.emod_eq_of_lt (by omega) (by exact_mod_cast j.isLt)
            exact_mod_cast this
          have hmem : ∀ (j : Fin M) (m n : ℕ) (i : Fin M), i ∈ intervalSet j m n ↔
              ∃ s : ℤ, -(m:ℤ) ≤ s ∧ s ≤ n ∧ i = cyclicShift j s := by
            intro j m n i
            unfold intervalSet
            simp only [Finset.mem_image, Finset.mem_range]
            constructor
            · rintro ⟨k, hk, rfl⟩
              exact ⟨(k:ℤ) - m, by omega, by omega, rfl⟩
            · rintro ⟨s, h1, h2, rfl⟩
              refine ⟨(s + m).toNat, by omega, ?_⟩
              congr 1
              omega
          have huniv : ∀ (j : Fin M) (m n : ℕ), ¬ (m + n + 1 < M) → intervalSet j m n = Finset.univ := by
            intro j m n hmn
            ext i
            simp only [Finset.mem_univ, iff_true]
            rw [hmem]
            have e0 := Int.emod_nonneg ((i.val:ℤ) - j.val + m) (ne_of_gt hMpos)
            have e1 := Int.emod_lt_of_pos ((i.val:ℤ) - j.val + m) hMpos
            refine ⟨((i.val:ℤ) - j.val + m) % M - m, by omega, by omega, ?_⟩
            have : i = cyclicShift j ((i.val:ℤ) - j.val) := by
              apply Fin.ext
              have : (i.val : ℤ) = ((cyclicShift j ((i.val:ℤ) - j.val)).val : ℤ) := by
                rw [hcv, add_sub_cancel]
                symm
                exact Int.emod_eq_of_lt (by omega) (by exact_mod_cast i.isLt)
              exact_mod_cast this
            conv_lhs => rw [this]
            rw [hceq]
            have := Int.emod_add_mul_ediv ((i.val:ℤ) - j.val + m) (M:ℤ)
            exact ⟨((i.val:ℤ) - j.val + m) / M, by linarith⟩
          have hobs : ∀ (j : Fin M) (m n : ℕ) (t : ℝ),
              circleObservation p Q t (intervalCoord j m n) =
                subsetNonadoption p Q (intervalSet j m n) t := by
            intro j m n t
            unfold intervalCoord
            split_ifs with h
            · rfl
            · rw [huniv j m n h]
              rfl
          have hinsL : ∀ (j : Fin M) (m n : ℕ),
              insert (cyclicShift j (-((m:ℤ)+1))) (intervalSet j m n) = intervalSet j (m+1) n := by
            intro j m n
            ext i
            rw [Finset.mem_insert, hmem, hmem]
            constructor
            · rintro (rfl | ⟨s, h1, h2, rfl⟩)
              · exact ⟨_, by push_cast; omega, by omega, rfl⟩
              · exact ⟨s, by push_cast; omega, h2, rfl⟩
            · rintro ⟨s, h1, h2, rfl⟩
              push_cast at h1
              by_cases hs : s = -((m:ℤ)+1)
              · left; rw [hs]
              · right; exact ⟨s, by omega, h2, rfl⟩
          have hinsR : ∀ (j : Fin M) (m n : ℕ),
              insert (cyclicShift j ((n:ℤ)+1)) (intervalSet j m n) = intervalSet j m (n+1) := by
            intro j m n
            ext i
            rw [Finset.mem_insert, hmem, hmem]
            constructor
            · rintro (rfl | ⟨s, h1, h2, rfl⟩)
              · exact ⟨_, by omega, by push_cast; omega, rfl⟩
              · exact ⟨s, h1, by push_cast; omega, rfl⟩
            · rintro ⟨s, h1, h2, rfl⟩
              push_cast at h2
              by_cases hs : s = (n:ℤ)+1
              · left; rw [hs]
              · right; exact ⟨s, h1, by omega, rfl⟩
          have hnot : ∀ (j : Fin M) (m n : ℕ), m + n + 1 < M → ∀ a : ℤ,
              (a = -((m:ℤ)+1) ∨ a = (n:ℤ)+1) → cyclicShift j a ∉ intervalSet j m n := by
            intro j m n hmn a ha hmem'
            rw [hmem] at hmem'
            obtain ⟨s, h1, h2, h3⟩ := hmem'
            rw [hceq] at h3
            obtain ⟨c, hc⟩ := h3
            rcases ha with rfl | rfl
            · have hc1 : c < 0 := by nlinarith
              have hc2 : -1 < c := by nlinarith
              omega
            · have hc1 : 0 < c := by nlinarith
              have hc2 : c < 1 := by nlinarith
              omega
          -- boundary flux
          have hflux : ∀ (j : Fin M) (m n : ℕ), m + n + 1 < M → ∀ w : Fin M → ℝ,
              ∑ k ∈ (intervalSet j m n)ᶜ, (∑ i ∈ intervalSet j m n, Q k i) * w k =
              Q (cyclicShift j (-((m : ℤ) + 1))) (cyclicShift j (-(m : ℤ))) * w (cyclicShift j (-((m : ℤ) + 1)))
              + (if M = 2 then 0 else
                  Q (cyclicShift j ((n : ℤ) + 1)) (cyclicShift j (n : ℤ))) * w (cyclicShift j ((n : ℤ) + 1)) := by
            intro j m n hmn w
            have hkey : ∀ k ∈ (intervalSet j m n)ᶜ, ∀ i ∈ intervalSet j m n, Q k i =
                (if k = cyclicShift j (-((m : ℤ) + 1)) ∧ i = cyclicShift j (-(m : ℤ)) then
                  Q (cyclicShift j (-((m : ℤ) + 1))) (cyclicShift j (-(m : ℤ))) else 0)
                + (if k = cyclicShift j ((n : ℤ) + 1) ∧ i = cyclicShift j (n : ℤ) then
                  (if M = 2 then 0 else Q (cyclicShift j ((n : ℤ) + 1)) (cyclicShift j (n : ℤ))) else 0) := by
              intro k hk i hi
              rw [Finset.mem_compl] at hk
              have hki : k ≠ i := fun h => hk (h ▸ hi)
              by_cases c1 : k = cyclicShift j (-((m : ℤ) + 1)) ∧ i = cyclicShift j (-(m : ℤ))
              · rw [if_pos c1]
                have h0 : (if k = cyclicShift j ((n : ℤ) + 1) ∧ i = cyclicShift j (n : ℤ) then
                  (if M = 2 then 0 else Q (cyclicShift j ((n : ℤ) + 1)) (cyclicShift j (n : ℤ))) else 0) = 0 := by
                  by_cases c2 : k = cyclicShift j ((n : ℤ) + 1) ∧ i = cyclicShift j (n : ℤ)
                  · rw [if_pos c2]
                    have d1 := c1.1.symm.trans c2.1
                    have d2 := c1.2.symm.trans c2.2
                    rw [hceq] at d1 d2
                    have d3 := dvd_sub d2 d1
                    have d4 : (M:ℤ) ∣ 2 := by
                      have : -(m:ℤ) - n - (-((m:ℤ)+1) - (n+1)) = 2 := by ring
                      rwa [this] at d3
                    have d5 := Int.le_of_dvd (by norm_num) d4
                    rw [if_pos (by omega)]
                  · rw [if_neg c2]
                rw [h0, add_zero, c1.1, c1.2]
              · rw [if_neg c1, zero_add]
                by_cases c2 : k = cyclicShift j ((n : ℤ) + 1) ∧ i = cyclicShift j (n : ℤ)
                · rw [if_pos c2]
                  have hM2 : M ≠ 2 := by
                    intro hM2
                    apply c1
                    have hm0 : m = 0 := by omega
                    have hn0 : n = 0 := by omega
                    rw [c2.1, c2.2, hceq, hceq]
                    subst hm0 hn0
                    constructor
                    · rw [hM2]; norm_num
                    · norm_num
                  rw [if_neg hM2, c2.1, c2.2]
                · rw [if_neg c2]
                  rw [hmem] at hi
                  obtain ⟨s, h1, h2, rfl⟩ := hi
                  apply hcircle _ _ hki
                  · rw [hcadd]
                    intro h
                    by_cases hs : s = -(m:ℤ)
                    · apply c1
                      rw [h, hs]
                      refine ⟨by congr 1; ring, rfl⟩
                    · apply hk
                      rw [hmem]
                      exact ⟨s + -1, by omega, by omega, h⟩
                  · rw [hcadd]
                    intro h
                    by_cases hs : s = (n:ℤ)
                    · apply c2
                      rw [h, hs]
                      exact ⟨rfl, rfl⟩
                    · apply hk
                      rw [hmem]
                      exact ⟨s + 1, by omega, by omega, h⟩
            have hL := hnot j m n hmn _ (Or.inl rfl)
            have hR := hnot j m n hmn _ (Or.inr rfl)
            have hf : cyclicShift j (-(m:ℤ)) ∈ intervalSet j m n := by
              rw [hmem]; exact ⟨_, le_refl _, by omega, rfl⟩
            have hl : cyclicShift j (n:ℤ) ∈ intervalSet j m n := by
              rw [hmem]; exact ⟨_, by omega, le_refl _, rfl⟩
            have hsum : ∀ (K I : Fin M) (x : ℝ), K ∉ intervalSet j m n → I ∈ intervalSet j m n →
                ∑ k ∈ (intervalSet j m n)ᶜ, (∑ i ∈ intervalSet j m n,
                  if k = K ∧ i = I then x else 0) * w k = x * w K := by
              intro K I x hK hI
              rw [Finset.sum_eq_single K]
              · rw [Finset.sum_eq_single I]
                · simp
                · intro b _ hb
                  simp [hb]
                · intro h; exact absurd hI h
              · intro b _ hb
                simp [hb]
              · intro h
                exact absurd (Finset.mem_compl.2 hK) h
            rw [← hsum _ _ _ hL hf, ← hsum _ _ _ hR hl, ← Finset.sum_add_distrib]
            apply Finset.sum_congr rfl
            intro k hk
            rw [← add_mul, ← Finset.sum_add_distrib]
            congr 1
            apply Finset.sum_congr rfl
            intro i hi
            exact hkey k hk i hi
          -- existence
          have hsol : SolvesCircleIVP p Q (circleObservation p Q) := by
            constructor
            · intro c
              rcases c with _ | ⟨j, mn⟩
              · exact hinit _
              · exact hinit _
            · intro t _ c
              apply HasDerivAt.hasDerivWithinAt
              rcases c with _ | ⟨j, ⟨⟨m, n⟩, hmn⟩⟩
              · have := hmaster Finset.univ t
                simpa [circleRHS, circleObservation] using this
              · have h := hmaster (intervalSet j m.val n.val) t
                rw [hflux j m.val n.val hmn (fun k => subsetNonadoption p Q (intervalSet j m.val n.val) t
                  - subsetNonadoption p Q (insert k (intervalSet j m.val n.val)) t), hinsL, hinsR] at h
                have e : circleObservation p Q t (some (j, ⟨(m, n), hmn⟩)) =
                  subsetNonadoption p Q (intervalSet j m.val n.val) t := rfl
                have e2 : (fun s => circleObservation p Q s (some (j, ⟨(m, n), hmn⟩))) =
                  fun s => subsetNonadoption p Q (intervalSet j m.val n.val) s := rfl
                rw [e2]
                refine h.congr_deriv ?_
                simp only [circleRHS]
                rw [e, hobs, hobs]
                ring
          -- uniqueness
          have huniq : ∀ v : ℝ → CircleCoord M → ℝ, SolvesCircleIVP p Q v →
              ∀ t : ℝ, 0 ≤ t → v t = circleObservation p Q t := by
            intro v hv t ht
            let L : (CircleCoord M → ℝ) →ₗ[ℝ] (CircleCoord M → ℝ) :=
              { toFun := circleRHS p Q
                map_add' := by
                  intro x y
                  funext c
                  rcases c with _ | ⟨j, mn⟩
                  · simp only [circleRHS, Pi.add_apply]; ring
                  · simp only [circleRHS, Pi.add_apply]; ring
                map_smul' := by
                  intro a x
                  funext c
                  rcases c with _ | ⟨j, mn⟩
                  · simp only [circleRHS, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring
                  · simp only [circleRHS, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring }
            have hlip := (LinearMap.toContinuousLinearMap L).lipschitz
            have hd : ∀ w : ℝ → CircleCoord M → ℝ, SolvesCircleIVP p Q w → ∀ s, 0 ≤ s →
                HasDerivWithinAt w (LinearMap.toContinuousLinearMap L (w s)) (Set.Ici 0) s := by
              intro w hw s hs
              rw [hasDerivWithinAt_pi]
              exact fun c => hw.2 s hs c
            have hcont : ∀ w : ℝ → CircleCoord M → ℝ, SolvesCircleIVP p Q w →
                ContinuousOn w (Set.Icc 0 t) := by
              intro w hw s hs
              exact ((hd w hw s hs.1).mono Set.Icc_subset_Ici_self).continuousWithinAt
            have hd' : ∀ w : ℝ → CircleCoord M → ℝ, SolvesCircleIVP p Q w → ∀ s ∈ Set.Ico 0 t,
                HasDerivWithinAt w (LinearMap.toContinuousLinearMap L (w s)) (Set.Ici s) s := by
              intro w hw s hs
              exact (hd w hw s hs.1).mono (Set.Ici_subset_Ici.2 hs.1)
            have := ODE_solution_unique (v := fun _ => LinearMap.toContinuousLinearMap L)
              (fun _ => hlip) (hcont v hv) (hd' v hv) (hcont _ hsol) (hd' _ hsol)
              (by funext c; rw [hv.1, hsol.1])
            exact this ⟨ht, le_refl _⟩
          refine ⟨circleObservation p Q, hsol, huniq, fun _ _ => rfl, ?_⟩
          intro t _
          have hsing : ∀ j : Fin M, circleObservation p Q t (intervalCoord j 0 0) =
              ∑ A, if j ∉ A then transition p Q t ∅ A else 0 := by
            intro j
            rw [hobs]
            have : intervalSet j 0 0 = {j} := by
              simp [intervalSet, hczero]
            rw [this]
            simp [subsetNonadoption]
          simp_rw [hsing]
          rw [Finset.sum_comm]
          have hcard : ∀ A : Finset (Fin M),
              (∑ j : Fin M, if j ∉ A then transition p Q t ∅ A else 0) =
                ((M:ℝ) - A.card) * transition p Q t ∅ A := by
            intro A
            rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
            congr 1
            have : (Finset.univ.filter (fun j => j ∉ A)) = Aᶜ := by
              ext; simp
            rw [this, Finset.card_compl, Fintype.card_fin, Nat.cast_sub]
            exact (Finset.card_le_univ A).trans_eq (Fintype.card_fin M)
          simp_rw [hcard, sub_mul]
          rw [Finset.sum_sub_distrib, ← Finset.mul_sum, htot]
          unfold expectedFraction
          have hM0 : (M:ℝ) ≠ 0 := by
            have : (M:ℕ) ≠ 0 := by omega
            exact_mod_cast this
          field_simp
          ring
