-- Prove2me | solution 1 for MulticlassQNet.SingleStation.Supplement.theorem_7_1_third_order_space
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:11:01.032087+00:00
-- url     : https://prove2.me/submissions/dd5e6aaa-e808-4229-9aa6-72fb685b1e1f

import Mathlib
import Definitions.Def_MulticlassQNet_FirstOrder_Network
import Definitions.Def_MulticlassQNet_FirstOrder_Dynamics
import Definitions.Def_MulticlassQNet_SingleStation_Supplement_ThirdMoments

open MulticlassQNet
open MulticlassQNet.SingleStation
open MulticlassQNet.SingleStation.Supplement

open MulticlassQNet.FirstOrder

/-- Theorem 7.1 (p. 28): in an open multiclass network with fixed routing, for every sequencing
policy satisfying the modified Assumption A (unique invariant law, `E[n_r³] < ∞`), the variables
`n_r`, `I_{rj}`, `H_{rjk}`, `M_{jk}`, `J_{rjk}` satisfy: the cubic polynomial `cubicPoly` vanishes
for every f-parameter vector `f` (equivalently, all its coefficients vanish: (48), (49) and (50)
with the printing errors repaired), the bounds (51) and (52), and nonnegativity (53). -/
theorem solution {N R : ℕ} (net : Network N R) (lam : Fin R → ℝ)
    (htraffic : net.IsTrafficSolution lam) (hopen : net.IsOpen)
    (P : Policy net) (π : (Fin R → ℕ) → ℝ) (hA : ThirdOrder.AssumptionA3 P π) :
    -- (48)–(50): every coefficient of the cubic in f vanishes
    (∀ f : Fin R → ℝ, cubicPoly net lam f (meanNum π) (P.busyMoment π) (ThirdOrder.H P π)
        (secondMoment π) = 0) ∧
    -- (51)
    (∀ i r, ∑ l ∈ net.C i, P.busyMoment π l r ≤ meanNum π r) ∧
    -- (52)
    (∀ i j k, ∑ l ∈ net.C i, ThirdOrder.H P π l j k ≤ secondMoment π j k) ∧
    -- (53)
    (∀ r, 0 ≤ meanNum π r) ∧ (∀ r j, 0 ≤ P.busyMoment π r j) ∧
    (∀ r j k, 0 ≤ ThirdOrder.H P π r j k) ∧ (∀ j k, 0 ≤ secondMoment π j k) ∧
    (∀ r j k, 0 ≤ thirdMoment π r j k) := by
      have hπ0 : ∀ n, 0 ≤ π n := hA.1.1
      have hπ1 : HasSum π 1 := hA.1.2.1
      have hπs : Summable π := hπ1.summable
      have hbal := hA.1.2.2
      have hB0 : ∀ n r, 0 ≤ P.busy n r := by
        intro n r; unfold Policy.busy; split_ifs <;> norm_num
      have hB1 : ∀ n r, P.busy n r ≤ 1 := by
        intro n r; unfold Policy.busy; split_ifs <;> norm_num
      have hP3 : ∀ a, Summable (fun n => π n * ((n a : ℝ) + 1) ^ 3) := by
        intro a
        refine Summable.of_nonneg_of_le (fun n => mul_nonneg (hπ0 n) (by positivity)) (fun n => ?_)
          (((hA.2.2 a).mul_left 4).add (hπs.mul_left 4))
        have hx : (0:ℝ) ≤ (n a : ℝ) := Nat.cast_nonneg _
        have h : ((n a : ℝ) + 1) ^ 3 ≤ 4 * (n a : ℝ) ^ 3 + 4 := by
          nlinarith [mul_nonneg (sq_nonneg ((n a : ℝ) - 1)) (by linarith : (0:ℝ) ≤ (n a : ℝ) + 1)]
        have := mul_le_mul_of_nonneg_left h (hπ0 n)
        nlinarith
      have hm3 : ∀ a b c, Summable (fun n => π n * ((n a : ℝ) + 1) * ((n b : ℝ) + 1) * ((n c : ℝ) + 1)) := by
        intro a b c
        refine Summable.of_nonneg_of_le (fun n => mul_nonneg (mul_nonneg (mul_nonneg (hπ0 n) (by positivity)) (by positivity)) (by positivity)) (fun n => ?_)
          (((hP3 a).add (hP3 b)).add (hP3 c))
        have hx : (0:ℝ) ≤ (n a : ℝ) + 1 := by positivity
        have hy : (0:ℝ) ≤ (n b : ℝ) + 1 := by positivity
        have hz : (0:ℝ) ≤ (n c : ℝ) + 1 := by positivity
        set x := (n a : ℝ) + 1
        set y := (n b : ℝ) + 1
        set z := (n c : ℝ) + 1
        have h : x * y * z ≤ x ^ 3 + y ^ 3 + z ^ 3 := by
          nlinarith [mul_nonneg (mul_nonneg hx hy) hz, mul_nonneg (add_nonneg (add_nonneg hx hy) hz)
            (add_nonneg (add_nonneg (sq_nonneg (x - y)) (sq_nonneg (y - z))) (sq_nonneg (x - z)))]
        have := mul_le_mul_of_nonneg_left h (hπ0 n)
        nlinarith
      have hW2 : ∀ w : (Fin R → ℕ) → ℝ, (∀ n, 0 ≤ w n) → (∀ n, w n ≤ 1) → ∀ j k,
          Summable (fun n => π n * w n * (n j : ℝ) * (n k : ℝ)) := by
        intro w hw0 hw1 j k
        refine Summable.of_nonneg_of_le (fun n => mul_nonneg (mul_nonneg (mul_nonneg (hπ0 n) (hw0 n))
          (Nat.cast_nonneg _)) (Nat.cast_nonneg _)) (fun n => ?_) (hm3 j k k)
        have hx : (0:ℝ) ≤ (n j : ℝ) := Nat.cast_nonneg _
        have hy : (0:ℝ) ≤ (n k : ℝ) := Nat.cast_nonneg _
        have h : w n * (n j : ℝ) * (n k : ℝ) ≤ ((n j : ℝ) + 1) * ((n k : ℝ) + 1) * ((n k : ℝ) + 1) := by
          have h1 : w n * (n j : ℝ) * (n k : ℝ) ≤ (n j : ℝ) * (n k : ℝ) := by
            nlinarith [mul_nonneg (mul_nonneg hx hy) (sub_nonneg.2 (hw1 n))]
          nlinarith [mul_nonneg hx hy, mul_nonneg (mul_nonneg hx hy) hy]
        have := mul_le_mul_of_nonneg_left h (hπ0 n)
        nlinarith
      have hW1 : ∀ w : (Fin R → ℕ) → ℝ, (∀ n, 0 ≤ w n) → (∀ n, w n ≤ 1) → ∀ j,
          Summable (fun n => π n * w n * (n j : ℝ)) := by
        intro w hw0 hw1 j
        refine Summable.of_nonneg_of_le (fun n => mul_nonneg (mul_nonneg (hπ0 n) (hw0 n))
          (Nat.cast_nonneg _)) (fun n => ?_) (hm3 j j j)
        have hx : (0:ℝ) ≤ (n j : ℝ) := Nat.cast_nonneg _
        have h : w n * (n j : ℝ) ≤ ((n j : ℝ) + 1) * ((n j : ℝ) + 1) * ((n j : ℝ) + 1) := by
          nlinarith [mul_nonneg hx (sub_nonneg.2 (hw1 n)), mul_nonneg hx hx, mul_nonneg (mul_nonneg hx hx) hx]
        have := mul_le_mul_of_nonneg_left h (hπ0 n)
        nlinarith
      have hW0 : ∀ w : (Fin R → ℕ) → ℝ, (∀ n, 0 ≤ w n) → (∀ n, w n ≤ 1) →
          Summable (fun n => π n * w n) := by
        intro w hw0 hw1
        refine Summable.of_nonneg_of_le (fun n => mul_nonneg (hπ0 n) (hw0 n)) (fun n => ?_) hπs
        nlinarith [hπ0 n, hw1 n]
      have one0 : ∀ n : Fin R → ℕ, (0:ℝ) ≤ (fun _ => (1:ℝ)) n := fun _ => zero_le_one
      have one1 : ∀ n : Fin R → ℕ, (fun _ => (1:ℝ)) n ≤ 1 := fun _ => le_refl _
      have sM : ∀ j k, HasSum (fun n => π n * (n j : ℝ) * (n k : ℝ)) (secondMoment π j k) := by
        intro j k; exact (by simpa using hW2 _ one0 one1 j k : Summable _).hasSum
      have sN : ∀ j, HasSum (fun n => π n * (n j : ℝ)) (meanNum π j) := by
        intro j; exact (by simpa using hW1 _ one0 one1 j : Summable _).hasSum
      have sH : ∀ r j k, HasSum (fun n => π n * P.busy n r * (n j : ℝ) * (n k : ℝ)) (ThirdOrder.H P π r j k) :=
        fun r j k => (hW2 (fun n => P.busy n r) (fun n => hB0 n r) (fun n => hB1 n r) j k).hasSum
      have sI : ∀ r j, HasSum (fun n => π n * P.busy n r * (n j : ℝ)) (P.busyMoment π r j) :=
        fun r j => (hW1 (fun n => P.busy n r) (fun n => hB0 n r) (fun n => hB1 n r) j).hasSum
      have sB : ∀ r, HasSum (fun n => π n * P.busy n r) (P.busyProb π r) :=
        fun r => (hW0 (fun n => P.busy n r) (fun n => hB0 n r) (fun n => hB1 n r)).hasSum
      have hφ1 : ∀ r (n : Fin R → ℕ) j, (n + unitVec r : Fin R → ℕ) j ≤ n j + 1 := by
        intro r n j; simp only [unitVec, Pi.add_apply, Pi.single_apply]; split_ifs <;> omega
      have hφ2 : ∀ r s (n : Fin R → ℕ) j, (n - unitVec r + unitVec s : Fin R → ℕ) j ≤ n j + 1 := by
        intro r s n j; simp only [unitVec, Pi.add_apply, Pi.sub_apply, Pi.single_apply]; split_ifs <;> omega
      have hφ3 : ∀ r (n : Fin R → ℕ) j, (n - unitVec r : Fin R → ℕ) j ≤ n j + 1 := by
        intro r n j; simp only [unitVec, Pi.sub_apply, Pi.single_apply]; split_ifs <;> omega
      have hφ0 : ∀ (n : Fin R → ℕ) j, n j ≤ n j + 1 := fun n j => Nat.le_succ _
      have key : ∀ g : (Fin R → ℕ) → ℝ, (∀ φ : (Fin R → ℕ) → (Fin R → ℕ), (∀ n j, φ n j ≤ n j + 1) →
          Summable (fun n => π n * |g (φ n)|)) → HasSum (fun n => π n * P.generator g n) 0 := by
        intro g hg
        have hS : ∀ φ : (Fin R → ℕ) → (Fin R → ℕ), (∀ n j, φ n j ≤ n j + 1) →
            ∀ c : (Fin R → ℕ) → ℝ, (∀ n, |c n| ≤ 1) →
            Summable (fun p : (Fin R → ℕ) × (Fin R → ℕ) =>
              c p.1 * ((if φ p.1 = p.2 then (1:ℝ) else 0) * (π p.1 * g p.2))) := by
          intro φ hφ c hc
          have hinj : Function.Injective (fun n : Fin R → ℕ => (n, φ n)) :=
            fun a b h => congrArg Prod.fst h
          rw [← hinj.summable_iff]
          · refine Summable.of_norm_bounded (hg φ hφ) (fun n => ?_)
            simp only [Function.comp, if_true, one_mul, Real.norm_eq_abs, abs_mul]
            rw [abs_of_nonneg (hπ0 n)]
            have := hc n
            nlinarith [abs_nonneg (g (φ n)), hπ0 n, mul_nonneg (hπ0 n) (abs_nonneg (g (φ n)))]
          · rintro ⟨n, m⟩ hnm
            have : φ n ≠ m := fun h => hnm ⟨n, by simp [h]⟩
            simp [this]
        have hdec : ∀ p : (Fin R → ℕ) × (Fin R → ℕ),
            π p.1 * P.generator (fun k => if k = p.2 then (1:ℝ) else 0) p.1 * g p.2 =
            ∑ r, net.lam0 r * ((fun _ => (1:ℝ)) p.1 * ((if p.1 + unitVec r = p.2 then (1:ℝ) else 0) * (π p.1 * g p.2))
                - (fun _ => (1:ℝ)) p.1 * ((if p.1 = p.2 then (1:ℝ) else 0) * (π p.1 * g p.2)))
            + ∑ r, net.μ r * (∑ s, net.p r s *
                (P.busy p.1 r * ((if p.1 - unitVec r + unitVec s = p.2 then (1:ℝ) else 0) * (π p.1 * g p.2))
                - P.busy p.1 r * ((if p.1 = p.2 then (1:ℝ) else 0) * (π p.1 * g p.2)))
              + net.exitProb r *
                (P.busy p.1 r * ((if p.1 - unitVec r = p.2 then (1:ℝ) else 0) * (π p.1 * g p.2))
                - P.busy p.1 r * ((if p.1 = p.2 then (1:ℝ) else 0) * (π p.1 * g p.2)))) := by
          intro p
          simp only [Policy.generator]
          rw [show ∀ x y z : ℝ, x * (y + z) * g p.2 = y * (x * g p.2) + z * (x * g p.2) from
            fun x y z => by ring, Finset.sum_mul, Finset.sum_mul]
          congr 1
          · exact Finset.sum_congr rfl fun r _ => by ring
          · refine Finset.sum_congr rfl fun r _ => ?_
            rw [show ∀ a b c d : ℝ, a * b * (c + d) * (π p.1 * g p.2) = b * (c * a * (π p.1 * g p.2) + d * a * (π p.1 * g p.2)) from
              fun a b c d => by ring, Finset.sum_mul, Finset.sum_mul]
            congr 2
            · exact Finset.sum_congr rfl fun s _ => by ring
            · ring
        have hc1 : ∀ n : Fin R → ℕ, |(fun _ => (1:ℝ)) n| ≤ 1 := fun n => by simp
        have hcB : ∀ r, ∀ n : Fin R → ℕ, |(fun n => P.busy n r) n| ≤ 1 := fun r n =>
          abs_le.mpr ⟨by linarith [hB0 n r], hB1 n r⟩
        have hFsum : Summable (fun p : (Fin R → ℕ) × (Fin R → ℕ) =>
            π p.1 * P.generator (fun k => if k = p.2 then (1:ℝ) else 0) p.1 * g p.2) := by
          rw [show (fun p : (Fin R → ℕ) × (Fin R → ℕ) =>
            π p.1 * P.generator (fun k => if k = p.2 then (1:ℝ) else 0) p.1 * g p.2) = _ from funext hdec]
          exact (summable_sum fun r _ => ((hS _ (hφ1 r) _ hc1).sub (hS _ hφ0 _ hc1)).mul_left _).add
            (summable_sum fun r _ => ((summable_sum fun s _ =>
              ((hS _ (hφ2 r s) _ (hcB r)).sub (hS _ hφ0 _ (hcB r))).mul_left _).add
              (((hS _ (hφ3 r) _ (hcB r)).sub (hS _ hφ0 _ (hcB r))).mul_left _)).mul_left _)
        have hfib1 : ∀ n, HasSum (fun m => π n * P.generator (fun k => if k = m then (1:ℝ) else 0) n * g m)
            (π n * P.generator g n) := by
          intro n
          have hU : ∀ x : Fin R → ℕ, HasSum (fun m => (if x = m then (1:ℝ) else 0) * (π n * g m)) (π n * g x) := by
            intro x
            convert hasSum_ite_eq x (π n * g x) using 1
            funext m
            by_cases h : x = m
            · subst h; simp
            · simp [h, Ne.symm h]
          have hc := (hasSum_sum (s := Finset.univ) fun r _ => (((hU (n + unitVec r)).mul_left 1).sub ((hU n).mul_left 1)).mul_left (net.lam0 r)).add
            (hasSum_sum (s := Finset.univ) fun r _ => ((hasSum_sum (s := Finset.univ) fun s _ => (((hU (n - unitVec r + unitVec s)).mul_left (P.busy n r)).sub
              ((hU n).mul_left (P.busy n r))).mul_left (net.p r s)).add
              ((((hU (n - unitVec r)).mul_left (P.busy n r)).sub ((hU n).mul_left (P.busy n r))).mul_left
                (net.exitProb r))).mul_left (net.μ r))
          convert hc using 1
          · rfl
          · funext m; exact hdec (n, m)
          · simp only [Policy.generator, mul_add, Finset.mul_sum]
            congr 1
            · exact Finset.sum_congr rfl fun r _ => by ring
            · refine Finset.sum_congr rfl fun r _ => ?_
              congr 1
              · exact Finset.sum_congr rfl fun s _ => by ring
              · ring
        have hfib2 : ∀ m, HasSum (fun n => π n * P.generator (fun k => if k = m then (1:ℝ) else 0) n * g m) 0 := by
          intro m
          have := (hbal m).mul_right (g m)
          rwa [zero_mul] at this
        obtain ⟨a, ha⟩ := hFsum
        have h1 := ha.prod_fiberwise hfib1
        have h2 : HasSum (fun _ : Fin R → ℕ => (0:ℝ)) a :=
          ((Equiv.prodComm (Fin R → ℕ) (Fin R → ℕ)).hasSum_iff.mpr ha).prod_fiberwise hfib2
        rw [h2.unique hasSum_zero] at h1
        exact h1
      obtain ⟨Rf, hRf⟩ : ∃ Rf : (Fin R → ℝ) → (Fin R → ℕ) → ℝ, ∀ f n, Rf f n = ∑ j, f j * (n j : ℝ) :=
        ⟨_, fun _ _ => rfl⟩
      have hsh1 : ∀ f (n : Fin R → ℕ) r, Rf f (n + unitVec r) = Rf f n + f r := by
        intro f n r
        rw [hRf, hRf]
        simp [unitVec, Pi.single_apply, mul_add, Finset.sum_add_distrib]
      have hsh3 : ∀ f (n : Fin R → ℕ) r, 1 ≤ n r → Rf f (n - unitVec r) = Rf f n - f r := by
        intro f n r hr
        rw [hRf, hRf]
        have : ∀ j, (((n - unitVec r : Fin R → ℕ) j : ℕ) : ℝ) = (n j : ℝ) - (if j = r then 1 else 0) := by
          intro j
          simp only [unitVec, Pi.sub_apply, Pi.single_apply]
          split_ifs with h
          · subst h; push_cast [Nat.cast_sub hr]; ring
          · simp
        simp only [this, mul_sub, Finset.sum_sub_distrib]
        simp
      have hsh2 : ∀ f (n : Fin R → ℕ) r s, 1 ≤ n r → Rf f (n - unitVec r + unitVec s) = Rf f n - f r + f s := by
        intro f n r s hr
        rw [hsh1, hsh3 f n r hr]
      have hgrow : ∀ f (φ : (Fin R → ℕ) → (Fin R → ℕ)), (∀ n j, φ n j ≤ n j + 1) → ∀ n,
          |Rf f (φ n)| ≤ ∑ j, |f j| * ((n j : ℝ) + 1) := by
        intro f φ hφ n
        rw [hRf]
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
        rw [abs_mul, Nat.abs_cast]
        exact mul_le_mul_of_nonneg_left (by exact_mod_cast hφ n j) (abs_nonneg _)
      have hA3 : ∀ f : Fin R → ℝ, Summable (fun n => π n * (∑ j, |f j| * ((n j : ℝ) + 1)) ^ 3) := by
        intro f
        refine (summable_sum (s := Finset.univ) fun a _ => summable_sum (s := Finset.univ) fun b _ =>
          summable_sum (s := Finset.univ) fun c _ => (hm3 a b c).mul_left (|f a| * |f b| * |f c|)).congr
          (fun n => ?_)
        simp only [pow_succ, pow_zero, one_mul, Finset.mul_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ => ?_
        ring
      have hA0 : ∀ (f : Fin R → ℝ) (n : Fin R → ℕ), 0 ≤ ∑ j, |f j| * ((n j : ℝ) + 1) := fun f n =>
        Finset.sum_nonneg fun j _ => mul_nonneg (abs_nonneg _) (by positivity)
      have hg1 : ∀ f, ∀ φ : (Fin R → ℕ) → (Fin R → ℕ), (∀ n j, φ n j ≤ n j + 1) →
          Summable (fun n => π n * |Rf f (φ n)|) := by
        intro f φ hφ
        refine Summable.of_nonneg_of_le (fun n => mul_nonneg (hπ0 n) (abs_nonneg _)) (fun n => ?_)
          (hπs.add (hA3 f))
        have h1 := hgrow f φ hφ n
        have h2 := hA0 f n
        set A := ∑ j, |f j| * ((n j : ℝ) + 1)
        have h3 : |Rf f (φ n)| ≤ 1 + A ^ 3 := by nlinarith [sq_nonneg (A - 1), mul_nonneg h2 (sq_nonneg (A - 1))]
        have := mul_le_mul_of_nonneg_left h3 (hπ0 n)
        nlinarith
      have hg3 : ∀ f, ∀ φ : (Fin R → ℕ) → (Fin R → ℕ), (∀ n j, φ n j ≤ n j + 1) →
          Summable (fun n => π n * |(fun m => Rf f m ^ 3) (φ n)|) := by
        intro f φ hφ
        refine Summable.of_nonneg_of_le (fun n => mul_nonneg (hπ0 n) (abs_nonneg _)) (fun n => ?_) (hA3 f)
        have h1 := hgrow f φ hφ n
        have h3 : |Rf f (φ n) ^ 3| ≤ (∑ j, |f j| * ((n j : ℝ) + 1)) ^ 3 := by
          rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) h1 3
        exact mul_le_mul_of_nonneg_left h3 (hπ0 n)
      -- first-order identity
      have hlin : ∀ f : Fin R → ℝ, ∑ r, net.lam0 r * f r * 1 +
          ∑ r, net.μ r * (∑ s, net.p r s * (f s - f r) - net.exitProb r * f r) * P.busyProb π r = 0 := by
        intro f
        refine HasSum.unique ?_ (key (Rf f) (hg1 f))
        have hc := (hasSum_sum (s := Finset.univ) fun r _ => hπ1.mul_left (net.lam0 r * f r)).add
          (hasSum_sum (s := Finset.univ) fun r _ =>
            (sB r).mul_left (net.μ r * (∑ s, net.p r s * (f s - f r) - net.exitProb r * f r)))
        convert hc using 1
        · rfl
        funext n
        simp only [Policy.generator, hsh1, mul_add, Finset.mul_sum]
        congr 1
        · exact Finset.sum_congr rfl fun r _ => by ring
        · refine Finset.sum_congr rfl fun r _ => ?_
          by_cases hs : P.serve n r = true
          · have hr := P.serve_present n r hs
            simp only [hsh2 f n r _ hr, hsh3 f n r hr]
            rw [show ∑ x, π n * (P.busy n r * net.μ r * (net.p r x * (Rf f n - f r + f x - Rf f n))) =
              π n * P.busy n r * net.μ r * ∑ x, net.p r x * (f x - f r) from by
                rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun x _ => by ring]
            ring
          · simp [Policy.busy, hs]
      have hv : ∀ r, net.μ r * P.busyProb π r = lam r := by
        have htr : ∀ r0, net.μ r0 * P.busyProb π r0 =
            net.lam0 r0 + ∑ r, net.μ r * P.busyProb π r * net.p r r0 := by
          intro r0
          have h := hlin (fun j => if j = r0 then 1 else 0)
          beta_reduce at h
          have hD : ∀ r, (∑ s, net.p r s * ((if s = r0 then (1:ℝ) else 0) - (if r = r0 then (1:ℝ) else 0))
              - net.exitProb r * (if r = r0 then (1:ℝ) else 0)) = net.p r r0 - (if r = r0 then 1 else 0) := by
            intro r
            simp only [Network.exitProb, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul]
            simp
            split_ifs <;> ring
          simp only [hD] at h
          simp only [mul_sub, sub_mul, Finset.sum_sub_distrib, mul_ite, ite_mul, mul_one, mul_zero, zero_mul,
            Finset.sum_ite_eq', Finset.mem_univ, if_true] at h
          rw [Finset.sum_congr rfl fun r _ => (by ring : net.μ r * net.p r r0 * P.busyProb π r =
            net.μ r * P.busyProb π r * net.p r r0)] at h
          linarith
        have hw := hopen (fun r => net.μ r * P.busyProb π r - lam r) (fun r => by
          rw [htr r, htraffic r]
          simp only [sub_mul, Finset.sum_sub_distrib]
          ring)
        intro r
        have := congrFun hw r
        simp only [Pi.zero_apply] at this
        linarith
      have hBs : ∀ i (n : Fin R → ℕ), ∑ l ∈ net.C i, P.busy n l ≤ 1 := by
        intro i n
        by_cases h : ∃ l ∈ net.C i, P.serve n l = true
        · obtain ⟨l0, hl0, hs0⟩ := h
          rw [Finset.sum_eq_single_of_mem l0 hl0 (fun b hb hne => ?_)]
          · exact hB1 n l0
          · have hσ : net.σ b = net.σ l0 := by
              simp only [Network.C, Finset.mem_filter, Finset.mem_univ, true_and] at hb hl0
              rw [hb, hl0]
            have := P.serve_one_class n b l0 hσ hne
            simp only [Policy.busy]
            split_ifs with hb'
            · exact absurd ⟨hb', hs0⟩ this
            · rfl
        · push_neg at h
          rw [Finset.sum_eq_zero (fun l hl => by simp [Policy.busy, h l hl])]
          norm_num
      refine ⟨fun f => ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · refine HasSum.unique ?_ (key (fun m => Rf f m ^ 3) (hg3 f))
        have hc := (((hasSum_sum (s := Finset.univ) fun r _ => ((((hasSum_sum (s := Finset.univ) fun j _ =>
            hasSum_sum (s := Finset.univ) fun k _ => (sM j k).mul_left (f j * f k)).mul_left (3 * f r)).add
            ((hasSum_sum (s := Finset.univ) fun j _ => (sN j).mul_left (f j)).mul_left (3 * f r ^ 2))).add
            (hπ1.mul_left (f r ^ 3))).mul_left (net.lam0 r)).add
          ((hasSum_sum (s := Finset.univ) fun r _ => (hasSum_sum (s := Finset.univ) fun j _ =>
            hasSum_sum (s := Finset.univ) fun k _ => (sH r j k).mul_left (f j * f k)).mul_left
            (net.μ r * (∑ s, net.p r s * (f s - f r) - net.exitProb r * f r))).mul_left 3)).add
          ((hasSum_sum (s := Finset.univ) fun r _ => (hasSum_sum (s := Finset.univ) fun j _ =>
            (sI r j).mul_left (f j)).mul_left
            (net.μ r * (∑ s, net.p r s * (f s - f r) ^ 2 + net.exitProb r * f r ^ 2))).mul_left 3)).add
          (hasSum_sum (s := Finset.univ) fun r _ => (sB r).mul_left
            (net.μ r * (∑ s, net.p r s * (f s - f r) ^ 3 - net.exitProb r * f r ^ 3)))
        convert hc using 1
        · rfl
        · funext n
          have hRR : ∀ c : ℝ, ∑ j, ∑ k, f j * f k * (c * (n j : ℝ) * (n k : ℝ)) = c * Rf f n ^ 2 := by
            intro c; rw [hRf, sq, Finset.sum_mul_sum, Finset.mul_sum]
            exact Finset.sum_congr rfl fun j _ => by
              rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => by ring
          have hR1 : ∀ c : ℝ, ∑ j, f j * (c * (n j : ℝ)) = c * Rf f n := by
            intro c; rw [hRf, Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
          simp only [Policy.generator, hsh1, hRR, hR1]
          rw [mul_add, Finset.mul_sum, Finset.mul_sum, add_assoc, add_assoc]
          congr 1
          · exact Finset.sum_congr rfl fun r _ => by ring
          · rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
            refine Finset.sum_congr rfl fun r _ => ?_
            by_cases hs : P.serve n r = true
            · have hr := P.serve_present n r hs
              simp only [hsh2 f n r _ hr, hsh3 f n r hr]
              rw [show ∑ s, net.p r s * ((Rf f n - f r + f s) ^ 3 - Rf f n ^ 3) =
                  3 * Rf f n ^ 2 * ∑ s, net.p r s * (f s - f r) + 3 * Rf f n * ∑ s, net.p r s * (f s - f r) ^ 2
                    + ∑ s, net.p r s * (f s - f r) ^ 3 from by
                rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
                exact Finset.sum_congr rfl fun s _ => by ring]
              ring
            · simp [Policy.busy, hs]
        · simp only [cubicPoly, mul_one]
          congr 1
          exact Finset.sum_congr rfl fun r _ => by rw [← hv r]; ring
      · intro i r
        show ∑ l ∈ net.C i, ∑' n, π n * P.busy n l * (n r : ℝ) ≤ ∑' n, π n * (n r : ℝ)
        rw [← Summable.tsum_finsetSum (fun l _ => (sI l r).summable)]
        refine Summable.tsum_le_tsum (fun n => ?_) (summable_sum fun l _ => (sI l r).summable) (sN r).summable
        rw [show ∑ l ∈ net.C i, π n * P.busy n l * (n r : ℝ) = (∑ l ∈ net.C i, P.busy n l) * (π n * n r) from by
          rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun l _ => by ring]
        exact mul_le_of_le_one_left (mul_nonneg (hπ0 n) (Nat.cast_nonneg _)) (hBs i n)
      · intro i j k
        show ∑ l ∈ net.C i, ∑' n, π n * P.busy n l * (n j : ℝ) * (n k : ℝ) ≤ ∑' n, π n * (n j : ℝ) * (n k : ℝ)
        rw [← Summable.tsum_finsetSum (fun l _ => (sH l j k).summable)]
        refine Summable.tsum_le_tsum (fun n => ?_) (summable_sum fun l _ => (sH l j k).summable) (sM j k).summable
        rw [show ∑ l ∈ net.C i, π n * P.busy n l * (n j : ℝ) * (n k : ℝ) =
            (∑ l ∈ net.C i, P.busy n l) * (π n * n j * n k) from by
          rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun l _ => by ring]
        exact mul_le_of_le_one_left (mul_nonneg (mul_nonneg (hπ0 n) (Nat.cast_nonneg _)) (Nat.cast_nonneg _))
          (hBs i n)
      · intro r
        exact tsum_nonneg fun n => mul_nonneg (hπ0 n) (Nat.cast_nonneg _)
      · intro r j
        exact tsum_nonneg fun n => mul_nonneg (mul_nonneg (hπ0 n) (hB0 n r)) (Nat.cast_nonneg _)
      · intro r j k
        exact tsum_nonneg fun n => mul_nonneg (mul_nonneg (mul_nonneg (hπ0 n) (hB0 n r)) (Nat.cast_nonneg _))
          (Nat.cast_nonneg _)
      · intro j k
        exact tsum_nonneg fun n => mul_nonneg (mul_nonneg (hπ0 n) (Nat.cast_nonneg _)) (Nat.cast_nonneg _)
      · intro r j k
        exact tsum_nonneg fun n => mul_nonneg (mul_nonneg (mul_nonneg (hπ0 n) (Nat.cast_nonneg _))
          (Nat.cast_nonneg _)) (Nat.cast_nonneg _)
