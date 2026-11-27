-- Prove2me | solution 1 for MulticlassQNet.SingleStation.Supplement.theorem_6_1_closed_polyhedron
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:10:42.430331+00:00
-- url     : https://prove2.me/submissions/9fde3966-259f-44f5-b8dd-90b67d13e8d2

import Mathlib
import Definitions.Def_MulticlassQNet_FirstOrder_Network
import Definitions.Def_MulticlassQNet_FirstOrder_Dynamics
import Definitions.Def_MulticlassQNet_SingleStation_Supplement_Closed

open MulticlassQNet
open MulticlassQNet.SingleStation
open MulticlassQNet.SingleStation.Supplement

open MulticlassQNet.FirstOrder

/-- Theorem 6.1 (p. 25): in a closed network (no external arrivals, no exits) with `F`
customers, for every sequencing policy satisfying Assumption A(a) on the population-`F` states,
`n_r = E[n_r]`, `u_r = E[1{B_r}]` and `I_{rr'} = E[1{B_r} n_{r'}]` satisfy (43)–(47) and are
nonnegative. -/
theorem solution {N R : ℕ} (net : Network N R)
    (hnoarr : ∀ r, net.lam0 r = 0) (hnoexit : ∀ r, ∑ s, net.p r s = 1) (F : ℕ)
    (P : Policy net) (π : (Fin R → ℕ) → ℝ) (hA : ClosedAssumptionA P F π) :
    -- (43)
    (∀ r, net.μ r * P.busyProb π r - ∑ l, net.μ l * P.busyProb π l * net.p l r = 0) ∧
    -- (44)
    (∀ r, 2 * net.μ r * P.busyMoment π r r - 2 * ∑ l, net.μ l * net.p l r * P.busyMoment π l r
      = P.busyProb π r * net.μ r * (1 - net.p r r)
        + ∑ l ∈ Finset.univ.erase r, net.μ l * P.busyProb π l * net.p l r) ∧
    -- (45)
    (∀ r r', r' < r →
      net.μ r * P.busyMoment π r r' + net.μ r' * P.busyMoment π r' r
        - ∑ w, net.μ w * net.p w r * P.busyMoment π w r'
        - ∑ w, net.μ w * net.p w r' * P.busyMoment π w r
      = -(net.μ r * P.busyProb π r * net.p r r') - net.μ r' * P.busyProb π r' * net.p r' r) ∧
    -- (46)
    (∀ i r, ∑ l ∈ net.C i, P.busyMoment π l r ≤ meanNum π r) ∧
    -- (47)
    (∑ l, meanNum π l = F) ∧
    -- nonnegativity
    (∀ r, 0 ≤ meanNum π r) ∧ (∀ r r', 0 ≤ P.busyMoment π r r') ∧
    (∀ r, 0 ≤ P.busyProb π r) := by
      set_option maxHeartbeats 2000000 in
      classical
      let S : Finset (Fin R → ℕ) := Finset.Iic (fun _ => F)
      let T : Finset (Fin R → ℕ) := Finset.Iic (fun _ => F + 1)
      have hπ : ∀ n, 0 ≤ π n := hA.1.1
      have hsupp : ∀ n, n ∉ S → π n = 0 := by
        intro n hn
        by_contra hp
        apply hn
        simp only [S, Finset.mem_Iic, Pi.le_def]
        intro r
        have hpop := hA.2.1 n hp
        exact (Finset.single_le_sum (fun i _ => Nat.zero_le (n i)) (Finset.mem_univ r)).trans hpop.le
      have htsum (g : (Fin R → ℕ) → ℝ) :
          (∑' n, π n * g n) = ∑ n ∈ S, π n * g n := by
        apply tsum_eq_sum
        intro n hn
        rw [hsupp n hn, zero_mul]
      have hu (r) : P.busyProb π r = ∑ n ∈ S, π n * P.busy n r := htsum _
      have hi (r r') : P.busyMoment π r r' = ∑ n ∈ S, π n * P.busy n r * (n r' : ℝ) := by
        simpa only [Policy.busyMoment, mul_assoc] using htsum (fun n => P.busy n r * (n r' : ℝ))
      have hn (r) : meanNum π r = ∑ n ∈ S, π n * (n r : ℝ) := htsum _
      have hmass : ∑ n ∈ S, π n = 1 := by
        have h := htsum (fun _ => 1)
        simpa only [mul_one, hA.1.2.1.tsum_eq] using h.symm
      have hclosed (g : (Fin R → ℕ) → ℝ) (n) :
          P.generator g n = ∑ l, P.busy n l * net.μ l *
            (∑ s, net.p l s * (g (n - unitVec l + unitVec s) - g n)) := by
        simp [Policy.generator, hnoarr, Network.exitProb, hnoexit]
      have hgenadd (g h : (Fin R → ℕ) → ℝ) (n) :
          P.generator (fun k => g k + h k) n = P.generator g n + P.generator h n := by
        simp only [hclosed]
        simp_rw [show ∀ a b c d : ℝ, (a + b) - (c + d) = (a - c) + (b - d) by intros; ring,
          mul_add, Finset.sum_add_distrib]
        simp only [mul_add, Finset.sum_add_distrib]
      have hgensmul (a : ℝ) (g : (Fin R → ℕ) → ℝ) (n) :
          P.generator (fun k => a * g k) n = a * P.generator g n := by
        simp only [hclosed]
        simp_rw [← mul_sub, ← mul_assoc, mul_comm (net.p _ _) a, mul_assoc a,
          ← Finset.mul_sum]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro l hl
        ring
      have hgensum (t : Finset (Fin R → ℕ)) (a : (Fin R → ℕ) → ℝ)
          (g : (Fin R → ℕ) → (Fin R → ℕ) → ℝ) (n) :
          P.generator (fun k => ∑ m ∈ t, a m * g m k) n =
            ∑ m ∈ t, a m * P.generator (g m) n := by
        induction t using Finset.induction_on with
        | empty => simp [hclosed]
        | @insert m t hm ih =>
          simp only [Finset.sum_insert hm]
          rw [hgenadd, hgensmul, ih]
      have hbal (g : (Fin R → ℕ) → ℝ) : ∑ n ∈ S, π n * P.generator g n = 0 := by
        have hmem (n) (hnS : n ∈ S) : n ∈ T := by
          simp only [S, T, Finset.mem_Iic, Pi.le_def] at *
          intro r
          exact (hnS r).trans (Nat.le_succ F)
        have hstep (n) (hnS : n ∈ S) (l s : Fin R) : n - unitVec l + unitVec s ∈ T := by
          simp only [S, T, Finset.mem_Iic, Pi.le_def] at *
          intro r
          simp only [Pi.add_apply, Pi.sub_apply, unitVec, Pi.single_apply]
          split_ifs <;> have := hnS r <;> omega
        have hrepr (k) (hk : k ∈ T) : (∑ m ∈ T, g m * (if k = m then 1 else 0)) = g k := by
          simp [mul_ite, Finset.sum_ite_eq, hk]
        have hlocal (n) (hnS : n ∈ S) :
            P.generator g n = P.generator (fun k => ∑ m ∈ T, g m * (if k = m then 1 else 0)) n := by
          simp only [hclosed, hrepr n (hmem n hnS)]
          apply Finset.sum_congr rfl
          intro l hl
          congr 1
          apply Finset.sum_congr rfl
          intro s hs
          rw [hrepr _ (hstep n hnS l s)]
        calc
          _ = ∑ n ∈ S, π n * ∑ m ∈ T, g m *
              P.generator (fun k => if k = m then 1 else 0) n := by
            apply Finset.sum_congr rfl
            intro n hnS
            rw [hlocal n hnS, hgensum]
          _ = ∑ m ∈ T, g m * (∑ n ∈ S, π n *
              P.generator (fun k => if k = m then 1 else 0) n) := by
            simp_rw [Finset.mul_sum]
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl
            intro m hm
            apply Finset.sum_congr rfl
            intros
            ring
          _ = 0 := by
            apply Finset.sum_eq_zero
            intro m hm
            have h := hA.1.2.2 m |>.tsum_eq
            rw [htsum] at h
            rw [h, mul_zero]
      have hbusy0 (n) (l) : 0 ≤ P.busy n l := by
        simp only [Policy.busy]
        split <;> norm_num
      have hupdate (n : Fin R → ℕ) (l s r : Fin R) (hl : P.serve n l = true) :
          ((n - unitVec l + unitVec s) r : ℝ) =
            (n r : ℝ) + (if s = r then 1 else 0) - (if l = r then 1 else 0) := by
        have hp := P.serve_present n l hl
        simp only [Pi.add_apply, Pi.sub_apply, unitVec, Pi.single_apply]
        by_cases hrl : r = l <;> by_cases hrs : r = s
        · subst l; subst s; simp [Nat.cast_sub hp]
        · subst l; simp [hrs, Ne.symm hrs, Nat.cast_sub hp]
        · subst s; simp [hrl, Ne.symm hrl]
        · simp [hrl, hrs, Ne.symm hrl, Ne.symm hrs]
      have hcoord (n : Fin R → ℕ) (r : Fin R) :
          P.generator (fun k => (k r : ℝ)) n =
            ∑ l, P.busy n l * net.μ l * (net.p l r - if l = r then 1 else 0) := by
        rw [hclosed]
        apply Finset.sum_congr rfl
        intro l hl
        by_cases hb : P.serve n l = true
        · congr 1
          simp_rw [hupdate n l _ r hb]
          simp only [show ∀ a b c : ℝ, a + b - c - a = b - c by intros; ring,
            mul_sub, Finset.sum_sub_distrib, mul_ite, mul_one, mul_zero,
            Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.sum_ite_irrel, hnoexit, Finset.sum_const_zero]
        · simp [Policy.busy, hb]
      have hfirst (r : Fin R) :
          net.μ r * P.busyProb π r - ∑ l, net.μ l * P.busyProb π l * net.p l r = 0 := by
        have h := hbal (fun k => (k r : ℝ))
        simp_rw [hcoord, Finset.mul_sum] at h
        rw [Finset.sum_comm] at h
        have heq : (∑ l, ∑ n ∈ S, π n * (P.busy n l * net.μ l *
            (net.p l r - if l = r then 1 else 0))) =
            (∑ l, net.μ l * P.busyProb π l * net.p l r) - net.μ r * P.busyProb π r := by
          simp only [hu, Finset.sum_mul, Finset.mul_sum, mul_sub, Finset.sum_sub_distrib]
          simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_irrel,
            Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.sum_const_zero]
          simp only [mul_assoc, mul_comm, mul_left_comm]
        rw [heq] at h
        linarith
      have hpoly (x y : ℝ) (l s r q : Fin R) :
          ((x + if s = r then 1 else 0) - if l = r then 1 else 0) *
              ((y + if s = q then 1 else 0) - if l = q then 1 else 0) - x * y =
          x * ((if s = q then 1 else 0) - if l = q then 1 else 0) +
          y * ((if s = r then 1 else 0) - if l = r then 1 else 0) +
          (if r = q then (if s = r then 1 else 0) + (if l = r then 1 else 0) else 0) -
          (if l = q then (if s = r then 1 else 0) else 0) -
          (if l = r then (if s = q then 1 else 0) else 0) := by
        by_cases hrq : r = q
        · subst q
          by_cases hsr : s = r <;> by_cases hlr : l = r <;> simp [hsr, hlr] <;> ring
        · by_cases hsr : s = r <;> by_cases hsq : s = q <;>
            by_cases hlr : l = r <;> by_cases hlq : l = q <;>
            simp [hrq, Ne.symm hrq, hsr, hsq, hlr, hlq] <;>
            ring
      have hrout (x y : ℝ) (l r q : Fin R) :
          (∑ s, net.p l s * (
          x * ((if s = q then 1 else 0) - if l = q then 1 else 0) +
          y * ((if s = r then 1 else 0) - if l = r then 1 else 0) +
          (if r = q then (if s = r then 1 else 0) + (if l = r then 1 else 0) else 0) -
          (if l = q then (if s = r then 1 else 0) else 0) -
          (if l = r then (if s = q then 1 else 0) else 0))) =
          x * (net.p l q - if l = q then 1 else 0) +
          y * (net.p l r - if l = r then 1 else 0) +
          (if r = q then net.p l r + (if l = r then 1 else 0) else 0) -
          (if l = q then net.p l r else 0) - (if l = r then net.p l q else 0) := by
        by_cases hrq : r = q <;> by_cases hlr : l = r <;> by_cases hlq : l = q <;>
          simp only [show q = r ↔ r = q from eq_comm, hrq, hlr, hlq, ite_true, ite_false, add_zero, sub_zero, mul_add,
            mul_sub, mul_ite, mul_one, mul_zero, Finset.sum_add_distrib, Finset.sum_sub_distrib,
            Finset.sum_ite_eq', Finset.mem_univ, hnoexit, ← Finset.sum_mul] <;> ring
      have hprod (n : Fin R → ℕ) (r q : Fin R) :
          P.generator (fun k => (k r : ℝ) * (k q : ℝ)) n =
          ∑ l, P.busy n l * net.μ l * (
          (n r : ℝ) * (net.p l q - if l = q then 1 else 0) +
          (n q : ℝ) * (net.p l r - if l = r then 1 else 0) +
          (if r = q then net.p l r + (if l = r then 1 else 0) else 0) -
          (if l = q then net.p l r else 0) - (if l = r then net.p l q else 0)) := by
        rw [hclosed]
        apply Finset.sum_congr rfl
        intro l hl
        by_cases hb : P.serve n l = true
        · congr 1
          simp_rw [hupdate n l _ r hb, hupdate n l _ q hb, hpoly]
          exact hrout _ _ _ _ _
        · simp [Policy.busy, hb]
      have havg (l r q : Fin R) (a b c d e : ℝ) :
          (∑ n ∈ S, π n * (P.busy n l * net.μ l *
            ((n r : ℝ) * a + (n q : ℝ) * b + c - d - e))) =
          net.μ l * P.busyMoment π l r * a + net.μ l * P.busyMoment π l q * b +
            net.μ l * P.busyProb π l * c - net.μ l * P.busyProb π l * d -
              net.μ l * P.busyProb π l * e := by
        simp only [hi, hu, mul_add, mul_sub, Finset.sum_add_distrib,
          Finset.sum_sub_distrib, Finset.mul_sum, Finset.sum_mul]
        simp only [mul_assoc, mul_comm, mul_left_comm]
      have hsecond (r q : Fin R) :
          net.μ r * P.busyMoment π r q + net.μ q * P.busyMoment π q r -
            (∑ l, net.μ l * net.p l r * P.busyMoment π l q) -
            (∑ l, net.μ l * net.p l q * P.busyMoment π l r) =
          (if r = q then (∑ l, net.μ l * P.busyProb π l * net.p l r) +
            net.μ r * P.busyProb π r else 0) -
          net.μ q * P.busyProb π q * net.p q r - net.μ r * P.busyProb π r * net.p r q := by
        have h := hbal (fun k => (k r : ℝ) * (k q : ℝ))
        simp_rw [hprod, Finset.mul_sum] at h
        rw [Finset.sum_comm] at h
        simp_rw [havg] at h
        have heq : (∑ l, (
            net.μ l * P.busyMoment π l r * (net.p l q - if l = q then 1 else 0) +
            net.μ l * P.busyMoment π l q * (net.p l r - if l = r then 1 else 0) +
            net.μ l * P.busyProb π l * (if r = q then net.p l r + (if l = r then 1 else 0) else 0) -
            net.μ l * P.busyProb π l * (if l = q then net.p l r else 0) -
            net.μ l * P.busyProb π l * (if l = r then net.p l q else 0))) =
            (∑ l, net.μ l * net.p l q * P.busyMoment π l r) - net.μ q * P.busyMoment π q r +
            ((∑ l, net.μ l * net.p l r * P.busyMoment π l q) - net.μ r * P.busyMoment π r q) +
            (if r = q then (∑ l, net.μ l * P.busyProb π l * net.p l r) +
              net.μ r * P.busyProb π r else 0) -
            net.μ q * P.busyProb π q * net.p q r - net.μ r * P.busyProb π r * net.p r q := by
          simp only [mul_sub, mul_add, mul_ite, mul_one, mul_zero,
            Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_ite_irrel,
            Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.sum_const_zero]
          simp only [mul_comm, mul_left_comm]
        rw [heq] at h
        linarith
      have h44 (r : Fin R) :
          2 * net.μ r * P.busyMoment π r r - 2 * ∑ l, net.μ l * net.p l r * P.busyMoment π l r =
          P.busyProb π r * net.μ r * (1 - net.p r r) +
            ∑ l ∈ Finset.univ.erase r, net.μ l * P.busyProb π l * net.p l r := by
        have hs := hsecond r r
        simp only [ite_true] at hs
        have he := Finset.sum_erase_add (Finset.univ : Finset (Fin R))
          (fun l => net.μ l * P.busyProb π l * net.p l r) (Finset.mem_univ r)
        linarith
      have h45 (r q : Fin R) (hqr : q < r) :
          net.μ r * P.busyMoment π r q + net.μ q * P.busyMoment π q r
            - ∑ w, net.μ w * net.p w r * P.busyMoment π w q
            - ∑ w, net.μ w * net.p w q * P.busyMoment π w r =
          -(net.μ r * P.busyProb π r * net.p r q) - net.μ q * P.busyProb π q * net.p q r := by
        have h := hsecond r q
        rw [if_neg (ne_of_gt hqr)] at h
        linarith
      have hcap (n : Fin R → ℕ) (i : Fin N) : ∑ l ∈ net.C i, P.busy n l ≤ 1 := by
        by_cases hex : ∃ l ∈ net.C i, P.serve n l = true
        · obtain ⟨l, hl, hb⟩ := hex
          have he : (∑ j ∈ net.C i, P.busy n j) = P.busy n l := by
            apply Finset.sum_eq_single_of_mem l hl
            intro j hj hjl
            have hσl : net.σ l = i := (Finset.mem_filter.mp hl).2
            have hσj : net.σ j = i := (Finset.mem_filter.mp hj).2
            have hjb : ¬P.serve n j = true := by
              intro hjb
              exact P.serve_one_class n j l (hσj.trans hσl.symm) hjl ⟨hjb, hb⟩
            simp [Policy.busy, hjb]
          rw [he]
          simp [Policy.busy, hb]
        · have he : (∑ l ∈ net.C i, P.busy n l) = 0 := by
            apply Finset.sum_eq_zero
            intro l hl
            have hb : ¬P.serve n l = true := by
              intro hb
              exact hex ⟨l, hl, hb⟩
            simp [Policy.busy, hb]
          rw [he]
          norm_num
      have h46 (i : Fin N) (r : Fin R) :
          ∑ l ∈ net.C i, P.busyMoment π l r ≤ meanNum π r := by
        calc
          _ = ∑ n ∈ S, (π n * (n r : ℝ)) * (∑ l ∈ net.C i, P.busy n l) := by
            simp only [hi, Finset.mul_sum]
            rw [Finset.sum_comm]
            simp only [mul_assoc, mul_comm, mul_left_comm]
          _ ≤ ∑ n ∈ S, π n * (n r : ℝ) := by
            apply Finset.sum_le_sum
            intro n hnS
            calc
              _ ≤ (π n * (n r : ℝ)) * 1 :=
                mul_le_mul_of_nonneg_left (hcap n i) (mul_nonneg (hπ n) (Nat.cast_nonneg _))
              _ = _ := mul_one _
          _ = _ := (hn r).symm
      have h47 : (∑ l, meanNum π l) = F := by
        calc
          _ = ∑ n ∈ S, π n * (∑ l, (n l : ℝ)) := by
            simp only [hn, Finset.mul_sum]
            rw [Finset.sum_comm]
          _ = ∑ n ∈ S, π n * (F : ℝ) := by
            apply Finset.sum_congr rfl
            intro n hnS
            by_cases hp : π n = 0
            · simp [hp]
            · rw [← Nat.cast_sum, hA.2.1 n hp]
          _ = _ := by rw [← Finset.sum_mul, hmass, one_mul]
      have hn0 (r : Fin R) : 0 ≤ meanNum π r := by
        apply tsum_nonneg
        intro n
        exact mul_nonneg (hπ n) (Nat.cast_nonneg _)
      have hi0 (r q : Fin R) : 0 ≤ P.busyMoment π r q := by
        apply tsum_nonneg
        intro n
        exact mul_nonneg (mul_nonneg (hπ n) (hbusy0 n r)) (Nat.cast_nonneg _)
      have hu0 (r : Fin R) : 0 ≤ P.busyProb π r := by
        apply tsum_nonneg
        intro n
        exact mul_nonneg (hπ n) (hbusy0 n r)
      exact ⟨hfirst, h44, h45, h46, h47, hn0, hi0, hu0⟩
