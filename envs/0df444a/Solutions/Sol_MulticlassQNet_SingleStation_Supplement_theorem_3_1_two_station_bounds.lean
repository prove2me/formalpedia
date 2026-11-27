-- Prove2me | solution 1 for MulticlassQNet.SingleStation.Supplement.theorem_3_1_two_station_bounds
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:09:51.539137+00:00
-- url     : https://prove2.me/submissions/e85b59a7-0156-48ed-b2e6-f742c19feb52

import Mathlib
import Definitions.Def_MulticlassQNet_FirstOrder_Network
import Definitions.Def_MulticlassQNet_FirstOrder_Dynamics
import Definitions.Def_MulticlassQNet_SingleStation_Supplement_TwoStation

open MulticlassQNet
open MulticlassQNet.SingleStation
open MulticlassQNet.SingleStation.Supplement

open MulticlassQNet.FirstOrder

/-- Theorem 3.1 (p. 9): in the two-station network of §3, for every policy satisfying
Assumption A, the seven inequalities (2)–(8), each written with `λ_r x_r = n̄_r` (the mean
number of class-`r` customers): classes 1 and 3 have throughput `λ₁`, class 2 has `λ₂`, and an
inequality on an unweighted `x_r` is multiplied by that class's throughput. -/
theorem solution (lam1 lam2 mu1 mu2 : ℝ) (h1 : 0 ≤ lam1) (h2 : 0 ≤ lam2)
    (hm1 : 0 < mu1) (hm2 : 0 < mu2) (hst1 : lam1 + lam2 < mu1) (hst2 : lam1 < mu2)
    (P : Policy (twoStation lam1 lam2 mu1 mu2 h1 h2 hm1 hm2)) (π : (Fin 3 → ℕ) → ℝ)
    (hA : P.AssumptionA π) :
    -- (2) λ₁x₁ + λ₂x₂ ≥ (λ₁ + λ₂)/(μ₁ − λ₁ − λ₂)
    (lam1 + lam2) / (mu1 - lam1 - lam2) ≤ meanNum π 0 + meanNum π 1 ∧
    -- (3) x₁ ≥ 1/(μ₁ − λ₁)
    lam1 / (mu1 - lam1) ≤ meanNum π 0 ∧
    -- (4) x₂ ≥ 1/(μ₁ − λ₂)
    lam2 / (mu1 - lam2) ≤ meanNum π 1 ∧
    -- (5) x₃ ≥ 1/μ₂
    lam1 / mu2 ≤ meanNum π 2 ∧
    -- (6) x₁ + x₃ ≥ 1/(μ₂ − λ₁)
    lam1 / (mu2 - lam1) ≤ meanNum π 0 + meanNum π 2 ∧
    -- (7) λ₂x₂ + λ₁x₃ ≥ (λ₁ + λ₂)/(μ₁ + μ₂ − λ₂)
    (lam1 + lam2) / (mu1 + mu2 - lam2) ≤ meanNum π 1 + meanNum π 2 ∧
    -- (8) 2λ₁x₁ + λ₂x₂ + λ₁x₃ ≥ (3λ₁ + λ₂)/(μ₁ + μ₂ − 2λ₁ − λ₂)
    (3 * lam1 + lam2) / (mu1 + mu2 - 2 * lam1 - lam2) ≤
      2 * meanNum π 0 + meanNum π 1 + meanNum π 2 := by
        have hgen : ∀ (g : (Fin 3 → ℕ) → ℝ) n, P.generator g n =
            lam1 * (g (n + unitVec 0) - g n) + lam2 * (g (n + unitVec 1) - g n)
            + P.busy n 0 * mu1 * (g (n - unitVec 0 + unitVec 2) - g n)
            + P.busy n 1 * mu1 * (g (n - unitVec 1) - g n)
            + P.busy n 2 * mu2 * (g (n - unitVec 2) - g n) := by
          intro g n
          simp only [Policy.generator, Network.exitProb, Fin.sum_univ_three]
          simp [twoStation]
          ring
        have hb01 : ∀ n, P.busy n 0 + P.busy n 1 ≤ 1 := by
          intro n
          have := P.serve_one_class n 0 1 (by simp [twoStation]) (by decide)
          unfold Policy.busy
          split_ifs <;> simp_all
        have hb0 : ∀ n r, 0 ≤ P.busy n r := by
          intro n r; unfold Policy.busy; split_ifs <;> norm_num
        have hb1 : ∀ n r, P.busy n r ≤ 1 := by
          intro n r; unfold Policy.busy; split_ifs <;> norm_num
        have hbn : ∀ n r, P.busy n r ≤ (n r : ℝ) := by
          intro n r; unfold Policy.busy; split_ifs with h
          · exact_mod_cast P.serve_present n r h
          · positivity
        have hQ : ∀ (f : ℝ → ℝ → ℝ → ℝ) n, P.generator (fun k => f (k 0) (k 1) (k 2)) n =
            lam1 * (f ((n 0 : ℝ) + 1) (n 1) (n 2) - f (n 0) (n 1) (n 2))
            + lam2 * (f (n 0) ((n 1 : ℝ) + 1) (n 2) - f (n 0) (n 1) (n 2))
            + P.busy n 0 * mu1 * (f ((n 0 : ℝ) - 1) (n 1) ((n 2 : ℝ) + 1) - f (n 0) (n 1) (n 2))
            + P.busy n 1 * mu1 * (f (n 0) ((n 1 : ℝ) - 1) (n 2) - f (n 0) (n 1) (n 2))
            + P.busy n 2 * mu2 * (f (n 0) (n 1) ((n 2 : ℝ) - 1) - f (n 0) (n 1) (n 2)) := by
          intro f n
          rw [hgen]
          have p0 := P.serve_present n 0
          have p1 := P.serve_present n 1
          have p2 := P.serve_present n 2
          unfold Policy.busy
          by_cases s0 : P.serve n 0 = true <;> by_cases s1 : P.serve n 1 = true <;>
            by_cases s2 : P.serve n 2 = true <;>
            simp [s0, s1, s2, unitVec, Pi.single_apply, Nat.cast_sub, p0, p1, p2]
        have hπ : ∀ n, 0 ≤ π n := hA.1.1
        have hπ1 : HasSum π 1 := hA.1.2.1
        have hM : Summable (fun n : Fin 3 → ℕ =>
            π n * (1 + (n 0 : ℝ) ^ 2 + (n 1 : ℝ) ^ 2 + (n 2 : ℝ) ^ 2)) := by
          have := ((hπ1.summable.add (hA.2.2 0)).add (hA.2.2 1)).add (hA.2.2 2)
          convert this using 1
          funext n; (try simp only [Pi.add_apply]); ring
        let T : Fin 6 → (Fin 3 → ℕ) → (Fin 3 → ℕ) := fun k n =>
          ![n, n + unitVec 0, n + unitVec 1, n - unitVec 0 + unitVec 2, n - unitVec 1, n - unitVec 2] k
        have hT : ∀ k n i, (T k n) i ≤ n i + 1 := by
          intro k n i
          fin_cases k <;> fin_cases i <;> simp [T, unitVec, Pi.single_apply] <;> omega
        have hTM : ∀ k n, (1 + ((T k n) 0 : ℝ) ^ 2 + ((T k n) 1 : ℝ) ^ 2 + ((T k n) 2 : ℝ) ^ 2)
            ≤ 7 * (1 + (n 0 : ℝ) ^ 2 + (n 1 : ℝ) ^ 2 + (n 2 : ℝ) ^ 2) := by
          intro k n
          have q : ∀ i, ((T k n) i : ℝ) ^ 2 ≤ 2 * (n i : ℝ) ^ 2 + 2 := by
            intro i
            have h := hT k n i
            have h' : ((T k n) i : ℝ) ≤ (n i : ℝ) + 1 := by exact_mod_cast h
            have h0 : (0:ℝ) ≤ ((T k n) i : ℝ) := by positivity
            have := pow_le_pow_left₀ h0 h' 2
            linarith [sq_nonneg ((n i : ℝ) - 1)]
          linarith [q 0, q 1, q 2, sq_nonneg (n 0 : ℝ), sq_nonneg (n 1 : ℝ), sq_nonneg (n 2 : ℝ)]
        have hterm : ∀ w a b : ℝ, 0 ≤ w → 0 ≤ a → a ≤ 1 → 0 ≤ b → b ≤ 1 →
            -w ≤ w * (a - b) ∧ w * (a - b) ≤ w := by
          intro w a b hw ha ha' hb hb'
          have x1 := mul_le_of_le_one_right hw (show b - a ≤ 1 by linarith)
          have x2 := mul_le_of_le_one_right hw (show a - b ≤ 1 by linarith)
          constructor <;> linarith
        have hI : ∀ x y : Fin 3 → ℕ, 0 ≤ (if x = y then (1:ℝ) else 0) ∧ (if x = y then (1:ℝ) else 0) ≤ 1 := by
          intro x y; split_ifs <;> norm_num
        have hkey : ∀ (g : (Fin 3 → ℕ) → ℝ) (C : ℝ),
            (∀ n, |g n| ≤ C * (1 + (n 0 : ℝ) ^ 2 + (n 1 : ℝ) ^ 2 + (n 2 : ℝ) ^ 2)) →
            HasSum (fun n => π n * P.generator g n) 0 := by
          intro g C hg
          have hC : 0 ≤ C := by
            have := hg 0
            simp at this
            linarith [abs_nonneg (g 0)]
          set c := lam1 + lam2 + 2 * mu1 + mu2 with hc
          have hc0 : 0 ≤ c := by rw [hc]; linarith
          let G : (Fin 3 → ℕ) → (Fin 3 → ℕ) → ℝ := fun m k => if k = m then 1 else 0
          let F : (Fin 3 → ℕ) × (Fin 3 → ℕ) → ℝ := fun p => π p.1 * (g p.2 * P.generator (G p.2) p.1)
          let H : (Fin 3 → ℕ) × (Fin 3 → ℕ) → ℝ := fun p =>
            π p.1 * c * ∑ k : Fin 6, (if p.2 = T k p.1 then |g (T k p.1)| else 0)
          have hHrow : ∀ n, HasSum (fun m => H (n, m)) (π n * c * ∑ k : Fin 6, |g (T k n)|) := by
            intro n
            exact (hasSum_sum (fun k _ => hasSum_ite_eq (T k n) |g (T k n)|)).mul_left (π n * c)
          have hHnn : 0 ≤ H := by
            intro p
            simp only [H, Pi.zero_apply]
            apply mul_nonneg (mul_nonneg (hπ _) hc0)
            apply Finset.sum_nonneg
            intro k _
            split_ifs <;> simp
          have hH : Summable H := by
            rw [summable_prod_of_nonneg hHnn]
            refine ⟨fun n => (hHrow n).summable, ?_⟩
            have e : (fun n => ∑' m, H (n, m)) = fun n => π n * c * ∑ k : Fin 6, |g (T k n)| :=
              funext fun n => (hHrow n).tsum_eq
            rw [e]
            refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) (hM.mul_left (c * (42 * C)))
            · apply mul_nonneg (mul_nonneg (hπ _) hc0)
              exact Finset.sum_nonneg (fun k _ => abs_nonneg _)
            · have hs : ∑ k : Fin 6, |g (T k n)| ≤
                  ∑ k : Fin 6, C * (7 * (1 + (n 0 : ℝ) ^ 2 + (n 1 : ℝ) ^ 2 + (n 2 : ℝ) ^ 2)) := by
                apply Finset.sum_le_sum
                intro k _
                calc |g (T k n)| ≤ C * (1 + ((T k n) 0 : ℝ) ^ 2 + ((T k n) 1 : ℝ) ^ 2
                      + ((T k n) 2 : ℝ) ^ 2) := hg _
                  _ ≤ _ := by
                      have := mul_le_mul_of_nonneg_left (hTM k n) hC
                      linarith
              simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hs
              have := mul_le_mul_of_nonneg_left hs (mul_nonneg (hπ n) hc0)
              simp only [Nat.cast_ofNat] at this
              linarith
          have hbound : ∀ p, ‖F p‖ ≤ H p := by
            rintro ⟨n, m⟩
            simp only [F, H, Real.norm_eq_abs]
            by_cases hm : ∃ k, m = T k n
            · obtain ⟨k, rfl⟩ := hm
              have hQb : |P.generator (G (T k n)) n| ≤ c := by
                rw [hgen]
                simp only [G]
                have t1 := hterm lam1 _ _ h1 (hI (n + unitVec 0) (T k n)).1 (hI (n + unitVec 0) (T k n)).2
                  (hI n (T k n)).1 (hI n (T k n)).2
                have t2 := hterm lam2 _ _ h2 (hI (n + unitVec 1) (T k n)).1 (hI (n + unitVec 1) (T k n)).2
                  (hI n (T k n)).1 (hI n (T k n)).2
                have t3 := hterm (P.busy n 0 * mu1) _ _ (mul_nonneg (hb0 n 0) hm1.le)
                  (hI (n - unitVec 0 + unitVec 2) (T k n)).1 (hI (n - unitVec 0 + unitVec 2) (T k n)).2
                  (hI n (T k n)).1 (hI n (T k n)).2
                have t4 := hterm (P.busy n 1 * mu1) _ _ (mul_nonneg (hb0 n 1) hm1.le)
                  (hI (n - unitVec 1) (T k n)).1 (hI (n - unitVec 1) (T k n)).2
                  (hI n (T k n)).1 (hI n (T k n)).2
                have t5 := hterm (P.busy n 2 * mu2) _ _ (mul_nonneg (hb0 n 2) hm2.le)
                  (hI (n - unitVec 2) (T k n)).1 (hI (n - unitVec 2) (T k n)).2
                  (hI n (T k n)).1 (hI n (T k n)).2
                have u0 : P.busy n 0 * mu1 ≤ mu1 := mul_le_of_le_one_left hm1.le (hb1 n 0)
                have u1 : P.busy n 1 * mu1 ≤ mu1 := mul_le_of_le_one_left hm1.le (hb1 n 1)
                have u2 : P.busy n 2 * mu2 ≤ mu2 := mul_le_of_le_one_left hm2.le (hb1 n 2)
                rw [abs_le]
                constructor <;> linarith [t1.1, t1.2, t2.1, t2.2, t3.1, t3.2, t4.1, t4.2, t5.1, t5.2]
              have hle : |g (T k n)| ≤ ∑ k' : Fin 6, (if T k n = T k' n then |g (T k' n)| else 0) := by
                have := Finset.single_le_sum
                  (f := fun k' => if T k n = T k' n then |g (T k' n)| else 0)
                  (fun k' _ => by split_ifs <;> simp) (Finset.mem_univ k)
                simpa using this
              rw [abs_mul, abs_mul, abs_of_nonneg (hπ n)]
              calc π n * (|g (T k n)| * |P.generator (G (T k n)) n|) ≤ π n * (|g (T k n)| * c) :=
                    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hQb (abs_nonneg _)) (hπ n)
                _ = π n * c * |g (T k n)| := by ring
                _ ≤ _ := mul_le_mul_of_nonneg_left hle (mul_nonneg (hπ n) hc0)
            · push_neg at hm
              have e0 : n ≠ m := fun h => hm 0 (by simp [T, h])
              have e1 : n + unitVec 0 ≠ m := fun h => hm 1 (by simp [T, h])
              have e2 : n + unitVec 1 ≠ m := fun h => hm 2 (by simp [T, h])
              have e3 : n - unitVec 0 + unitVec 2 ≠ m := fun h => hm 3 (by simp [T, h])
              have e4 : n - unitVec 1 ≠ m := fun h => hm 4 (by simp [T, h])
              have e5 : n - unitVec 2 ≠ m := fun h => hm 5 (by simp [T, h])
              have : P.generator (G m) n = 0 := by
                rw [hgen]; simp only [G]; simp [e0, e1, e2, e3, e4, e5]
              rw [this]
              simpa using hHnn (n, m)
          have hF : Summable F := Summable.of_norm_bounded hH hbound
          have hrow : ∀ n, HasSum (fun m => F (n, m)) (π n * P.generator g n) := by
            intro n
            have hpt : ∀ x : Fin 3 → ℕ, HasSum (fun m => g m * (if x = m then (1:ℝ) else 0)) (g x) := by
              intro x
              convert hasSum_ite_eq x (g x) using 1
              funext m
              by_cases h : m = x
              · subst h; simp
              · simp [h, Ne.symm h]
            have a1 := ((hpt (n + unitVec 0)).sub (hpt n)).mul_left lam1
            have a2 := ((hpt (n + unitVec 1)).sub (hpt n)).mul_left lam2
            have a3 := ((hpt (n - unitVec 0 + unitVec 2)).sub (hpt n)).mul_left (P.busy n 0 * mu1)
            have a4 := ((hpt (n - unitVec 1)).sub (hpt n)).mul_left (P.busy n 1 * mu1)
            have a5 := ((hpt (n - unitVec 2)).sub (hpt n)).mul_left (P.busy n 2 * mu2)
            have := ((((a1.add a2).add a3).add a4).add a5).mul_left (π n)
            convert this using 1
            all_goals first
              | rfl
              | (funext m; simp only [F, G]; rw [hgen]; ring)
              | (rw [hgen])
          have hcol : ∀ m, HasSum (fun n => F (n, m)) 0 := by
            intro m
            have := (hA.1.2.2 m).mul_left (g m)
            convert this using 1
            all_goals first
              | rfl
              | (funext n; simp only [F, G]; ring)
              | simp
          have hA1 := hF.hasSum.prod_fiberwise hrow
          have hA2 := ((Equiv.prodComm _ _).hasSum_iff.mpr hF.hasSum).prod_fiberwise (fun m => hcol m)
          have h0 : ∑' p, F p = 0 := hA2.unique hasSum_zero
          rw [h0] at hA1
          exact hA1
        have hmn : ∀ r, HasSum (fun n => π n * (n r : ℝ)) (meanNum π r) := by
          intro r
          have hs : Summable (fun n => π n * (n r : ℝ)) := by
            refine Summable.of_nonneg_of_le (fun n => mul_nonneg (hπ n) (by positivity)) (fun n => ?_)
              (hπ1.summable.add (hA.2.2 r))
            have : (n r : ℝ) ≤ 1 + (n r : ℝ) ^ 2 := by nlinarith [sq_nonneg ((n r : ℝ) - 1)]
            have := mul_le_mul_of_nonneg_left this (hπ n)
            show π n * (n r : ℝ) ≤ π n + π n * (n r : ℝ) ^ 2
            linarith
          exact hs.hasSum
        have hgo : ∀ (f : ℝ → ℝ → ℝ → ℝ) (C α b0 b1 b2 : ℝ),
            (∀ n : Fin 3 → ℕ, |f (n 0) (n 1) (n 2)| ≤ C * (1 + (n 0 : ℝ) ^ 2 + (n 1 : ℝ) ^ 2 + (n 2 : ℝ) ^ 2)) →
            (∀ n : Fin 3 → ℕ, α + b0 * (n 0 : ℝ) + b1 * (n 1 : ℝ) + b2 * (n 2 : ℝ) ≤
            lam1 * (f ((n 0 : ℝ) + 1) (n 1) (n 2) - f (n 0) (n 1) (n 2))
            + lam2 * (f (n 0) ((n 1 : ℝ) + 1) (n 2) - f (n 0) (n 1) (n 2))
            + P.busy n 0 * mu1 * (f ((n 0 : ℝ) - 1) (n 1) ((n 2 : ℝ) + 1) - f (n 0) (n 1) (n 2))
            + P.busy n 1 * mu1 * (f (n 0) ((n 1 : ℝ) - 1) (n 2) - f (n 0) (n 1) (n 2))
            + P.busy n 2 * mu2 * (f (n 0) (n 1) ((n 2 : ℝ) - 1) - f (n 0) (n 1) (n 2))) →
            α + b0 * meanNum π 0 + b1 * meanNum π 1 + b2 * meanNum π 2 ≤ 0 := by
          intro f C α b0 b1 b2 hf hle
          have h0 := hkey (fun k => f (k 0) (k 1) (k 2)) C hf
          have hS : HasSum (fun n => π n * (α + b0 * (n 0 : ℝ) + b1 * (n 1 : ℝ) + b2 * (n 2 : ℝ)))
              (α + b0 * meanNum π 0 + b1 * meanNum π 1 + b2 * meanNum π 2) := by
            have := (((hπ1.mul_left α).add ((hmn 0).mul_left b0)).add ((hmn 1).mul_left b1)).add
              ((hmn 2).mul_left b2)
            convert this using 1
            all_goals first
              | rfl
              | (funext n; ring)
              | ring
          exact hasSum_le (fun n => mul_le_mul_of_nonneg_left (by rw [hQ]; exact hle n) (hπ n)) hS h0
        -- (3)
        have i3 := hgo (fun a _ _ => a ^ 2 + a) 2 (2 * lam1) (2 * lam1 - 2 * mu1) 0 0
          (fun n => by
            have ha : (0:ℝ) ≤ n 0 := by positivity
            beta_reduce
            rw [abs_of_nonneg (by positivity)]
            linarith [sq_nonneg ((n 0 : ℝ) - 1), sq_nonneg (n 1 : ℝ), sq_nonneg (n 2 : ℝ)])
          (fun n => by
            beta_reduce
            have ha : (0:ℝ) ≤ n 0 := by positivity
            linarith [mul_nonneg (mul_nonneg hm1.le ha) (sub_nonneg.2 (hb1 n 0))])
        -- (4)
        have i4 := hgo (fun _ b _ => b ^ 2 + b) 2 (2 * lam2) 0 (2 * lam2 - 2 * mu1) 0
          (fun n => by
            have ha : (0:ℝ) ≤ n 1 := by positivity
            beta_reduce
            rw [abs_of_nonneg (by positivity)]
            linarith [sq_nonneg ((n 1 : ℝ) - 1), sq_nonneg (n 0 : ℝ), sq_nonneg (n 2 : ℝ)])
          (fun n => by
            beta_reduce
            have ha : (0:ℝ) ≤ n 1 := by positivity
            linarith [mul_nonneg (mul_nonneg hm1.le ha) (sub_nonneg.2 (hb1 n 1))])
        -- (5)
        have i5 := hgo (fun a _ c => a + c) 2 lam1 0 0 (-mu2)
          (fun n => by
            have ha : (0:ℝ) ≤ n 0 := by positivity
            have hc : (0:ℝ) ≤ n 2 := by positivity
            beta_reduce
            rw [abs_of_nonneg (by positivity)]
            nlinarith [sq_nonneg ((n 0 : ℝ) - 1), sq_nonneg ((n 2 : ℝ) - 1), sq_nonneg (n 1 : ℝ)])
          (fun n => by
            beta_reduce
            linarith [mul_le_mul_of_nonneg_left (hbn n 2) hm2.le])
        -- (2)
        have i2 := hgo (fun a b _ => (a + b) ^ 2 + (a + b)) 4 (2 * (lam1 + lam2))
          (2 * lam1 + 2 * lam2 - 2 * mu1) (2 * lam1 + 2 * lam2 - 2 * mu1) 0
          (fun n => by
            have ha : (0:ℝ) ≤ n 0 := by positivity
            have hb : (0:ℝ) ≤ n 1 := by positivity
            beta_reduce
            rw [abs_of_nonneg (by positivity)]
            linarith [sq_nonneg ((n 0 : ℝ) - 1), sq_nonneg ((n 1 : ℝ) - 1), sq_nonneg (n 2 : ℝ),
              sq_nonneg ((n 0 : ℝ) - n 1)])
          (fun n => by
            beta_reduce
            have ha : (0:ℝ) ≤ n 0 := by positivity
            have hb : (0:ℝ) ≤ n 1 := by positivity
            linarith [mul_nonneg (mul_nonneg hm1.le (add_nonneg ha hb))
              (show 0 ≤ 1 - P.busy n 0 - P.busy n 1 by linarith [hb01 n])])
        -- (6)
        have i6 := hgo (fun a _ c => (a + c) ^ 2 + (a + c)) 4 (2 * lam1)
          (2 * lam1 - 2 * mu2) 0 (2 * lam1 - 2 * mu2)
          (fun n => by
            have ha : (0:ℝ) ≤ n 0 := by positivity
            have hc : (0:ℝ) ≤ n 2 := by positivity
            beta_reduce
            rw [abs_of_nonneg (by positivity)]
            linarith [sq_nonneg ((n 0 : ℝ) - 1), sq_nonneg ((n 2 : ℝ) - 1), sq_nonneg (n 1 : ℝ),
              sq_nonneg ((n 0 : ℝ) - n 2)])
          (fun n => by
            beta_reduce
            have ha : (0:ℝ) ≤ n 0 := by positivity
            have hc : (0:ℝ) ≤ n 2 := by positivity
            linarith [mul_nonneg (mul_nonneg hm2.le (add_nonneg ha hc)) (sub_nonneg.2 (hb1 n 2))])
        -- (7)
        have i7 := hgo (fun a b c => (b + c) ^ 2 + (b + c) + 2 * a) 6 (2 * lam1 + 2 * lam2)
          0 (2 * lam2 - 2 * mu1 - 2 * mu2) (2 * lam2 - 2 * mu1 - 2 * mu2)
          (fun n => by
            have ha : (0:ℝ) ≤ n 0 := by positivity
            have hb : (0:ℝ) ≤ n 1 := by positivity
            have hc : (0:ℝ) ≤ n 2 := by positivity
            beta_reduce
            rw [abs_of_nonneg (by positivity)]
            nlinarith [sq_nonneg ((n 0 : ℝ) - 1), sq_nonneg ((n 1 : ℝ) - 1), sq_nonneg ((n 2 : ℝ) - 1),
              sq_nonneg ((n 1 : ℝ) - n 2)])
          (fun n => by
            beta_reduce
            have hb : (0:ℝ) ≤ n 1 := by positivity
            have hc : (0:ℝ) ≤ n 2 := by positivity
            linarith [mul_nonneg (mul_nonneg hm1.le (add_nonneg hb hc)) (sub_nonneg.2 (hb1 n 1)),
              mul_nonneg (mul_nonneg hm2.le (add_nonneg hb hc)) (sub_nonneg.2 (hb1 n 2)),
              mul_nonneg (mul_nonneg hm1.le (add_nonneg hb hc)) (hb0 n 0)])
        -- (8)
        have i8 := hgo (fun a b c => (2 * a + b + c) ^ 2 + (2 * a + b + c)) 12 (6 * lam1 + 2 * lam2)
          (2 * (4 * lam1 + 2 * lam2 - 2 * mu1 - 2 * mu2)) (4 * lam1 + 2 * lam2 - 2 * mu1 - 2 * mu2)
          (4 * lam1 + 2 * lam2 - 2 * mu1 - 2 * mu2)
          (fun n => by
            have ha : (0:ℝ) ≤ n 0 := by positivity
            have hb : (0:ℝ) ≤ n 1 := by positivity
            have hc : (0:ℝ) ≤ n 2 := by positivity
            beta_reduce
            rw [abs_of_nonneg (by positivity)]
            nlinarith [sq_nonneg ((n 0 : ℝ) - 1), sq_nonneg ((n 1 : ℝ) - 1), sq_nonneg ((n 2 : ℝ) - 1),
              sq_nonneg ((n 1 : ℝ) - n 2), sq_nonneg (2 * (n 0 : ℝ) - n 1),
              sq_nonneg (2 * (n 0 : ℝ) - n 2)])
          (fun n => by
            beta_reduce
            have ha : (0:ℝ) ≤ n 0 := by positivity
            have hb : (0:ℝ) ≤ n 1 := by positivity
            have hc : (0:ℝ) ≤ n 2 := by positivity
            have hw : (0:ℝ) ≤ 2 * n 0 + n 1 + n 2 := by positivity
            linarith [mul_nonneg (mul_nonneg hm1.le hw)
                (show 0 ≤ 1 - P.busy n 0 - P.busy n 1 by linarith [hb01 n]),
              mul_nonneg (mul_nonneg hm2.le hw) (sub_nonneg.2 (hb1 n 2))])
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · rw [div_le_iff₀ (by linarith)]; linarith
        · rw [div_le_iff₀ (by linarith)]; linarith
        · rw [div_le_iff₀ (by linarith)]; linarith
        · rw [div_le_iff₀ (by linarith)]; linarith
        · rw [div_le_iff₀ (by linarith)]; linarith
        · rw [div_le_iff₀ (by linarith)]; linarith
        · rw [div_le_iff₀ (by linarith)]; linarith
