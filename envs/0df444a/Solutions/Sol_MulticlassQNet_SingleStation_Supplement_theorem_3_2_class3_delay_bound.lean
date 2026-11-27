-- Prove2me | solution 1 for MulticlassQNet.SingleStation.Supplement.theorem_3_2_class3_delay_bound
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:10:12.315811+00:00
-- url     : https://prove2.me/submissions/0293427f-e5b4-4655-9e09-a62f9fe15f28

import Mathlib
import Definitions.Def_MulticlassQNet_FirstOrder_Network
import Definitions.Def_MulticlassQNet_FirstOrder_Dynamics
import Definitions.Def_MulticlassQNet_SingleStation_Supplement_TwoStation

open MulticlassQNet
open MulticlassQNet.SingleStation
open MulticlassQNet.SingleStation.Supplement

open MulticlassQNet.FirstOrder

/-- Theorem 3.2 (p. 12): in the two-station network of §3 with `2λ₁ > max(μ₁, μ₂)`, every
policy satisfying Assumption A has
`x₃ ≥ [(2λ₁ − max(μ₁,μ₂))/(μ₁ + μ₂ − max(μ₁,μ₂))]·[μ₁/(μ₂(μ₁ + μ₂))] + 1/μ₂`, (13)
stated for `n̄₃ = λ₁ x₃` (class 3 has throughput `λ₁ > 0`). -/
theorem solution (lam1 lam2 mu1 mu2 : ℝ) (h1 : 0 ≤ lam1) (h2 : 0 ≤ lam2)
    (hm1 : 0 < mu1) (hm2 : 0 < mu2) (hst1 : lam1 + lam2 < mu1) (hst2 : lam1 < mu2)
    (hheavy : max mu1 mu2 < 2 * lam1)
    (P : Policy (twoStation lam1 lam2 mu1 mu2 h1 h2 hm1 hm2)) (π : (Fin 3 → ℕ) → ℝ)
    (hA : P.AssumptionA π) :
    lam1 * ((2 * lam1 - max mu1 mu2) / (mu1 + mu2 - max mu1 mu2) * (mu1 / (mu2 * (mu1 + mu2)))
      + 1 / mu2) ≤ meanNum π 2 := by
        classical
        let S := Fin 3 → ℕ
        let T : S → Fin 5 → S := fun n =>
          ![n + unitVec 0, n + unitVec 1, n - unitVec 0 + unitVec 2,
            n - unitVec 1, n - unitVec 2]
        let w : S → Fin 5 → ℝ := fun n =>
          ![lam1, lam2, P.busy n 0 * mu1, P.busy n 1 * mu1, P.busy n 2 * mu2]
        let d : S → ℝ := fun n => ∑ i, w n i
        let q : S → S → ℝ := fun n m => ∑ i, w n i * (if T n i = m then 1 else 0)
        have hp : ∀ n, 0 ≤ π n := hA.1.1
        have hπ : Summable π := hA.1.2.1.summable
        have hπsum : ∑' n, π n = 1 := hA.1.2.1.tsum_eq
        have hb : ∀ n r, 0 ≤ P.busy n r ∧ P.busy n r ≤ 1 := by
          intro n r
          simp only [Policy.busy]
          split <;> norm_num
        have hw : ∀ n i, 0 ≤ w n i := by
          intro n i
          fin_cases i <;> simp [w, h1, h2, mul_nonneg (hb n 0).1 hm1.le,
            mul_nonneg (hb n 1).1 hm1.le, mul_nonneg (hb n 2).1 hm2.le]
        have hd : ∀ n, 0 ≤ d n ∧ d n ≤ lam1 + lam2 + 2 * mu1 + mu2 := by
          intro n
          constructor
          · exact Finset.sum_nonneg (fun i _ => hw n i)
          · dsimp [d, w]
            simp only [Fin.sum_univ_succ, Matrix.cons_val_zero, Matrix.cons_val_succ,
              Matrix.head_cons, Matrix.head_fin_const, Fin.sum_univ_zero, add_zero]
            nlinarith [(hb n 0).2, (hb n 1).2, (hb n 2).2]
        have hgen : ∀ (g : S → ℝ) n,
            P.generator g n = ∑ i, w n i * (g (T n i) - g n) := by
          intro g n
          have hc : (Finset.univ.filter (fun x : Fin 3 => x = 2)).card = 1 := by decide
          simp [Policy.generator, twoStation, Network.exitProb, Fin.sum_univ_succ, w, T, hc]
          <;> ring
        have hcol : ∀ m, HasSum (fun n => π n * q n m) (π m * d m) := by
          intro m
          have heq : ∀ n, π n * q n m =
              π n * P.generator (fun k => if k = m then 1 else 0) n +
                (if n = m then π m * d m else 0) := by
            intro n
            rw [hgen]
            dsimp [q, d]
            by_cases hn : n = m
            · subst n
              simp only [if_pos rfl]
              rw [Finset.mul_sum, Finset.mul_sum]
              simp_rw [mul_sub, Finset.sum_sub_distrib]
              simp only [ite_true, mul_one]
              simp_rw [← Finset.mul_sum]
              ring
            · simp [if_neg hn, sub_zero, add_zero, Finset.mul_sum]
          simp_rw [heq]
          simpa using (hA.1.2.2 m).add (hasSum_ite_eq m (π m * d m))
        have hrow : ∀ (g : S → ℝ) n,
            HasSum (fun m => q n m * g m) (∑ i, w n i * g (T n i)) := by
          intro g n
          have hi : ∀ i : Fin 5,
              HasSum (fun m => w n i * (if T n i = m then 1 else 0) * g m)
                (w n i * g (T n i)) := by
            intro i
            convert hasSum_ite_eq' (T n i) (w n i * g (T n i)) using 1
            ext m
            by_cases h : T n i = m
            · subst m; simp
            · simp [h]
          have hsum : ∀ s : Finset (Fin 5),
              HasSum (fun m => ∑ i ∈ s, w n i * (if T n i = m then 1 else 0) * g m)
                (∑ i ∈ s, w n i * g (T n i)) := by
            intro s
            induction s using Finset.induction_on with
            | empty => simpa using (hasSum_zero : HasSum (fun _ : S => (0 : ℝ)) 0)
            | @insert i s he ih =>
              simpa only [Finset.sum_insert he] using (hi i).add ih
          simpa only [q, Finset.sum_mul] using hsum Finset.univ
        have hstat : ∀ (g : S → ℝ), (∀ n, 0 ≤ g n) →
            Summable (fun n => π n * g n) →
            (∑' n, π n * P.generator g n) = 0 := by
          intro g hg hsg
          have hout : Summable (fun n => π n * d n * g n) := by
            apply Summable.of_nonneg_of_le
              (fun n => mul_nonneg (mul_nonneg (hp n) (hd n).1) (hg n))
              (fun n => ?_) (hsg.mul_left (lam1 + lam2 + 2 * mu1 + mu2))
            nlinarith [mul_le_mul_of_nonneg_left (hd n).2 (mul_nonneg (hp n) (hg n))]
          have hpair : Summable (fun z : S × S => π z.2 * q z.2 z.1 * g z.1) := by
            apply (summable_prod_of_nonneg (fun z =>
              mul_nonneg (mul_nonneg (hp z.2)
                (Finset.sum_nonneg (fun i _ => mul_nonneg (hw z.2 i) (by split <;> norm_num))))
                (hg z.1))).2
            constructor
            · intro m
              exact ((hcol m).mul_right (g m)).summable
            · exact hout.congr (fun m => ((hcol m).mul_right (g m)).tsum_eq.symm)
          have hin : Summable (fun n => π n * (∑ i, w n i * g (T n i))) := by
            apply hpair.prod_symm.prod.congr
            intro n
            simpa [mul_assoc] using ((hrow g n).mul_left (π n)).tsum_eq
          have he : (∑' n, π n * (∑ i, w n i * g (T n i))) =
              ∑' n, π n * d n * g n := by
            calc
              _ = ∑' n, ∑' m, π n * q n m * g m := by
                apply tsum_congr
                intro n
                simpa [mul_assoc] using ((hrow g n).mul_left (π n)).tsum_eq.symm
              _ = ∑' m, ∑' n, π n * q n m * g m := hpair.tsum_comm
              _ = _ := tsum_congr (fun m => ((hcol m).mul_right (g m)).tsum_eq)
          calc
            _ = ∑' n, (π n * (∑ i, w n i * g (T n i)) - π n * d n * g n) := by
              apply tsum_congr
              intro n
              rw [hgen]
              simp [mul_sub, Finset.sum_sub_distrib, d, Finset.sum_mul, mul_assoc]
            _ = 0 := by rw [hin.tsum_sub hout, he, sub_self]
        have hmean : ∀ r : Fin 3, Summable (fun n => π n * (n r : ℝ)) := by
          intro r
          apply Summable.of_nonneg_of_le (fun n => mul_nonneg (hp n) (Nat.cast_nonneg _))
            (fun n => ?_) (hπ.add (hA.2.2 r))
          have hx : (n r : ℝ) ≤ 1 + (n r : ℝ)^2 := by nlinarith [sq_nonneg ((n r : ℝ) - 1)]
          nlinarith [mul_le_mul_of_nonneg_left hx (hp n)]
        have hbs : ∀ r, Summable (fun n => π n * P.busy n r) := by
          intro r
          exact Summable.of_nonneg_of_le (fun n => mul_nonneg (hp n) (hb n r).1)
            (fun n => by nlinarith [(hb n r).2, hp n]) hπ
        have hzero : ∀ n r, n r = 0 → P.busy n r = 0 := by
          intro n r hn
          have hs : P.serve n r = false := by
            cases he : P.serve n r
            · rfl
            · have := P.serve_present n r he; omega
          simp [Policy.busy, hs]
        have hT0 : ∀ n i, T n i 0 = (![n 0 + 1, n 0, n 0 - 1, n 0, n 0] : Fin 5 → ℕ) i := by
          intro n i
          fin_cases i <;> rfl
        have hT2 : ∀ n i, T n i 2 = (![n 2, n 2, n 2 + 1, n 2, n 2 - 1] : Fin 5 → ℕ) i := by
          intro n i
          fin_cases i <;> rfl
        have hg0 : ∀ n, P.generator (fun k : S => (k 0 : ℝ)) n =
            lam1 - P.busy n 0 * mu1 := by
          intro n
          rw [hgen]
          simp_rw [hT0]
          simp [w, Fin.sum_univ_succ]
          by_cases hs : P.serve n 0 = true
          · have hv : P.busy n 0 = 1 := by simp [Policy.busy, hs]
            rw [hv]
            simp [Nat.cast_sub (P.serve_present n 0 hs)] <;> ring
          · have hv : P.busy n 0 = 0 := by simp [Policy.busy, hs]
            simp [hv]
        have hg2 : ∀ n, P.generator (fun k : S => (k 2 : ℝ)) n =
            P.busy n 0 * mu1 - P.busy n 2 * mu2 := by
          intro n
          rw [hgen]
          simp_rw [hT2]
          simp [w, Fin.sum_univ_succ]
          by_cases hs : P.serve n 2 = true
          · have hv : P.busy n 2 = 1 := by simp [Policy.busy, hs]
            rw [hv]
            simp [Nat.cast_sub (P.serve_present n 2 hs)] <;> ring
          · have hv : P.busy n 2 = 0 := by simp [Policy.busy, hs]
            simp [hv] <;> ring
        let a : S → ℝ := fun n => if n 2 = 0 then 0 else P.busy n 0
        let c : S → ℝ := fun n => if n 2 ≤ 1 then 0 else P.busy n 2
        have ha : ∀ n, 0 ≤ a n ∧ a n ≤ 1 := by
          intro n; dsimp [a]; split <;> simp [hb]
        have hc : ∀ n, 0 ≤ c n ∧ c n ≤ 1 := by
          intro n; dsimp [c]; split <;> simp [hb]
        have has : Summable (fun n => π n * a n) :=
          Summable.of_nonneg_of_le (fun n => mul_nonneg (hp n) (ha n).1)
            (fun n => by nlinarith [(ha n).2, hp n]) hπ
        have hcs : Summable (fun n => π n * c n) :=
          Summable.of_nonneg_of_le (fun n => mul_nonneg (hp n) (hc n).1)
            (fun n => by nlinarith [(hc n).2, hp n]) hπ
        have hgex : ∀ n, P.generator (fun k : S => ((k 2 - 1 : ℕ) : ℝ)) n =
            mu1 * a n - mu2 * c n := by
          intro n
          rw [hgen]
          simp_rw [hT2]
          rcases hn : n 2 with _ | k
          · have hz := hzero n 2 hn
            simp [w, Fin.sum_univ_succ, hn, a, c, hz]
          · rcases k with _ | k
            · simp [w, Fin.sum_univ_succ, hn, a, c] <;> ring
            · simp [w, Fin.sum_univ_succ, hn, a, c] <;> ring
        have hu0 : (∑' n, π n * P.busy n 0) * mu1 = lam1 := by
          have hh := hstat (fun k => (k 0 : ℝ)) (fun n => Nat.cast_nonneg _) (hmean 0)
          simp_rw [hg0, mul_sub, ← mul_assoc] at hh
          rw [(hπ.mul_right lam1).tsum_sub ((hbs 0).mul_right mu1),
            tsum_mul_right, tsum_mul_right, hπsum] at hh
          linarith
        have hu2 : (∑' n, π n * P.busy n 2) * mu2 = lam1 := by
          have hh := hstat (fun k => (k 2 : ℝ)) (fun n => Nat.cast_nonneg _) (hmean 2)
          simp_rw [hg2, mul_sub, ← mul_assoc] at hh
          rw [((hbs 0).mul_right mu1).tsum_sub ((hbs 2).mul_right mu2),
            tsum_mul_right, tsum_mul_right] at hh
          linarith
        have hex : mu1 * (∑' n, π n * a n) = mu2 * (∑' n, π n * c n) := by
          have hsex : Summable (fun n => π n * ((n 2 - 1 : ℕ) : ℝ)) := by
            exact Summable.of_nonneg_of_le (fun n => mul_nonneg (hp n) (Nat.cast_nonneg _))
              (fun n => mul_le_mul_of_nonneg_left (by exact_mod_cast Nat.sub_le (n 2) 1) (hp n)) (hmean 2)
          have hh := hstat (fun k => ((k 2 - 1 : ℕ) : ℝ)) (fun n => Nat.cast_nonneg _) hsex
          have heq : ∀ n, π n * P.generator (fun k : S => ((k 2 - 1 : ℕ) : ℝ)) n =
              mu1 * (π n * a n) - mu2 * (π n * c n) := by
            intro n; rw [hgex]; ring
          simp_rw [heq] at hh
          rw [(has.mul_left mu1).tsum_sub (hcs.mul_left mu2), tsum_mul_left, tsum_mul_left] at hh
          linarith
        have hpoint : ∀ n, P.busy n 0 * mu1 + P.busy n 2 * mu2 ≤
            max mu1 mu2 + (mu1 + mu2 - max mu1 mu2) * a n := by
          intro n
          by_cases hn : n 2 = 0
          · rw [hzero n 2 hn]
            simp only [a, if_pos hn, mul_zero, zero_mul, add_zero]
            nlinarith [(hb n 0).2, le_max_left mu1 mu2]
          · simp only [a, if_neg hn]
            by_cases hs : P.serve n 0 = true
            · have hh : P.busy n 0 = 1 := by simp [Policy.busy, hs]
              rw [hh]
              nlinarith [(hb n 2).2]
            · have hh : P.busy n 0 = 0 := by simp [Policy.busy, hs]
              rw [hh]
              nlinarith [(hb n 2).2, le_max_right mu1 mu2]
        have hrate : 2 * lam1 ≤ max mu1 mu2 +
            (mu1 + mu2 - max mu1 mu2) * (∑' n, π n * a n) := by
          have hsleft := ((hbs 0).mul_right mu1).add ((hbs 2).mul_right mu2)
          have hsright := (hπ.mul_right (max mu1 mu2)).add
            (has.mul_left (mu1 + mu2 - max mu1 mu2))
          have hh := hsleft.tsum_le_tsum (fun n => show
              (π n * P.busy n 0) * mu1 + (π n * P.busy n 2) * mu2 ≤
                π n * max mu1 mu2 + (mu1 + mu2 - max mu1 mu2) * (π n * a n) by
            nlinarith [mul_le_mul_of_nonneg_left (hpoint n) (hp n)]) hsright
          rw [((hbs 0).mul_right mu1).tsum_add ((hbs 2).mul_right mu2),
            (hπ.mul_right (max mu1 mu2)).tsum_add (has.mul_left (mu1 + mu2 - max mu1 mu2)),
            tsum_mul_right, tsum_mul_right, tsum_mul_right, tsum_mul_left, hπsum] at hh
          linarith
        have hpop : ∀ n, P.busy n 2 + c n ≤ (n 2 : ℝ) := by
          intro n
          by_cases hn : n 2 ≤ 1
          · simp only [c, if_pos hn, add_zero]
            by_cases hz : n 2 = 0
            · simp [hzero n 2 hz, hz]
            · have hh : (1 : ℝ) ≤ (n 2 : ℝ) := by exact_mod_cast (show 1 ≤ n 2 by omega)
              linarith [(hb n 2).2]
          · have hh : (2 : ℝ) ≤ (n 2 : ℝ) := by exact_mod_cast (show 2 ≤ n 2 by omega)
            simp only [c, if_neg hn]
            linarith [(hb n 2).2]
        have hlow : (∑' n, π n * P.busy n 2) + (∑' n, π n * c n) ≤ meanNum π 2 := by
          rw [← (hbs 2).tsum_add hcs]
          exact ((hbs 2).add hcs).tsum_le_tsum
            (fun n => by nlinarith [mul_le_mul_of_nonneg_left (hpop n) (hp n)]) (hmean 2)
        have hden : 0 < mu1 + mu2 - max mu1 mu2 := by
          rcases le_total mu1 mu2 with h | h
          · rw [max_eq_right h]; linarith
          · rw [max_eq_left h]; linarith
        have ht : (2 * lam1 - max mu1 mu2) / (mu1 + mu2 - max mu1 mu2) ≤
            ∑' n, π n * a n := by
          apply (div_le_iff₀ hden).2
          linarith [hrate]
        have hC : (2 * lam1 - max mu1 mu2) / (mu1 + mu2 - max mu1 mu2) * (mu1 / mu2) ≤
            ∑' n, π n * c n := by
          rw [← mul_div_assoc, div_le_iff₀ hm2]
          nlinarith [mul_le_mul_of_nonneg_left ht hm1.le]
        have hu2' : (∑' n, π n * P.busy n 2) = lam1 / mu2 :=
          (eq_div_iff hm2.ne').2 hu2
        have hbound : lam1 / mu2 +
            (2 * lam1 - max mu1 mu2) / (mu1 + mu2 - max mu1 mu2) * (mu1 / mu2) ≤ meanNum π 2 := by
          rw [hu2'] at hlow
          linarith
        have hsum : 0 < mu1 + mu2 := add_pos hm1 hm2
        have hfac : lam1 * (mu1 / (mu2 * (mu1 + mu2))) ≤ mu1 / mu2 := by
          rw [← mul_div_assoc]
          apply (div_le_div_iff₀ (mul_pos hm2 hsum) hm2).2
          nlinarith [mul_nonneg (mul_nonneg hm1.le hm2.le)
            (show 0 ≤ mu1 + mu2 - lam1 by linarith)]
        have htpos : 0 ≤ (2 * lam1 - max mu1 mu2) / (mu1 + mu2 - max mu1 mu2) :=
          div_nonneg (by linarith [hheavy]) hden.le
        calc
          _ = lam1 / mu2 + (2 * lam1 - max mu1 mu2) / (mu1 + mu2 - max mu1 mu2) *
              (lam1 * (mu1 / (mu2 * (mu1 + mu2)))) := by ring
          _ ≤ lam1 / mu2 + (2 * lam1 - max mu1 mu2) / (mu1 + mu2 - max mu1 mu2) *
              (mu1 / mu2) := add_le_add (le_refl _) (mul_le_mul_of_nonneg_left hfac htpos)
          _ ≤ meanNum π 2 := hbound
