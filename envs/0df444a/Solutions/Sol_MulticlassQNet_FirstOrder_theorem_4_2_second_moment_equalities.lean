-- Prove2me | solution 1 for MulticlassQNet.FirstOrder.theorem_4_2_second_moment_equalities
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-06T05:34:50.885201+00:00
-- url     : https://prove2.me/submissions/a089953b-6fcd-4a59-bea0-084bda109fea

import Mathlib
import Definitions.Def_MulticlassQNet_FirstOrder_Network
import Definitions.Def_MulticlassQNet_FirstOrder_Dynamics
import Definitions.Def_MulticlassQNet_FirstOrder_Constraints



namespace MulticlassQNet.FirstOrder


lemma mq_busy_nonneg {N R : ℕ} {net : Network N R} (P : Policy net) (n : Fin R → ℕ) (r : Fin R) :
    0 ≤ P.busy n r := by unfold Policy.busy; split_ifs <;> norm_num

lemma mq_busy_le_one {N R : ℕ} {net : Network N R} (P : Policy net) (n : Fin R → ℕ) (r : Fin R) :
    P.busy n r ≤ 1 := by unfold Policy.busy; split_ifs <;> norm_num

lemma mq_idle_nonneg {N R : ℕ} {net : Network N R} (P : Policy net) (i : Fin N) (n : Fin R → ℕ) :
    0 ≤ P.idle i n := by unfold Policy.idle; split_ifs <;> norm_num

lemma mq_busy_idle_sum {N R : ℕ} {net : Network N R} (P : Policy net) (i : Fin N)
    (n : Fin R → ℕ) : ∑ r ∈ net.C i, P.busy n r + P.idle i n = 1 := by
  by_cases h : ∀ r ∈ net.C i, P.serve n r = false
  · have h1 : ∑ r ∈ net.C i, P.busy n r = 0 :=
      Finset.sum_eq_zero (fun r hr => by simp [Policy.busy, h r hr])
    simp only [h1, Policy.idle, if_pos h]; norm_num
  · push Not at h
    obtain ⟨r0, hr0, hs⟩ := h
    have hs' : P.serve n r0 = true := by simpa using hs
    have h1 : ∑ r ∈ net.C i, P.busy n r = 1 := by
      rw [Finset.sum_eq_single r0]
      · simp [Policy.busy, hs']
      · intro b hb hne
        have hσ : net.σ b = net.σ r0 := by
          simp [Network.C] at hb hr0; rw [hb, hr0]
        have := P.serve_one_class n b r0 hσ hne
        have : P.serve n b = false := by
          cases hh : P.serve n b
          · rfl
          · exact absurd ⟨hh, hs'⟩ this
        simp [Policy.busy, this]
      · intro h; exact absurd hr0 h
    have h2 : P.idle i n = 0 := by
      simp only [Policy.idle]; rw [if_neg]; push Not; exact ⟨r0, hr0, by simp [hs']⟩
    rw [h1, h2]; norm_num

lemma mq_summable_pi {N R : ℕ} {net : Network N R} {P : Policy net} {π : (Fin R → ℕ) → ℝ}
    (hA : P.AssumptionA π) : Summable π := hA.1.2.1.summable

lemma mq_pi_nonneg {N R : ℕ} {net : Network N R} {P : Policy net} {π : (Fin R → ℕ) → ℝ}
    (hA : P.AssumptionA π) (n) : 0 ≤ π n := hA.1.1 n

lemma mq_summable_lin {N R : ℕ} {net : Network N R} {P : Policy net} {π : (Fin R → ℕ) → ℝ}
    (hA : P.AssumptionA π) (r : Fin R) : Summable (fun n => π n * (n r : ℝ)) := by
  refine Summable.of_nonneg_of_le (fun n => mul_nonneg (mq_pi_nonneg hA n) (by positivity))
    (fun n => ?_) ((mq_summable_pi hA).add (hA.2.2 r))
  have := mq_pi_nonneg hA n
  have h0 : (0:ℝ) ≤ n r := by positivity
  nlinarith [sq_nonneg ((n r : ℝ) - 1)]

lemma mq_summable_bounded {N R : ℕ} {net : Network N R} {P : Policy net} {π : (Fin R → ℕ) → ℝ}
    (hA : P.AssumptionA π) (r : Fin R) (c : (Fin R → ℕ) → ℝ) (hc0 : ∀ n, 0 ≤ c n)
    (hc1 : ∀ n, c n ≤ 1) : Summable (fun n => π n * c n * (n r : ℝ)) := by
  refine Summable.of_nonneg_of_le (fun n => mul_nonneg (mul_nonneg (mq_pi_nonneg hA n) (hc0 n))
    (by positivity)) (fun n => ?_) (mq_summable_lin hA r)
  have := mq_pi_nonneg hA n
  have h0 : (0:ℝ) ≤ n r := by positivity
  have : π n * c n ≤ π n := by nlinarith [hc0 n, hc1 n]
  exact mul_le_mul_of_nonneg_right this h0

theorem idle_busy_core {N R : ℕ} (net : Network N R)
    (P : Policy net) (π : (Fin R → ℕ) → ℝ) (hA : P.AssumptionA π) :
    net.Eq28 (meanNum π) (P.busyMoment π) (P.idleMoment π) := by
  intro i r'
  simp only [Policy.busyMoment, Policy.idleMoment, meanNum]
  rw [← Summable.tsum_finsetSum (fun r _ => mq_summable_bounded hA r' _ (mq_busy_nonneg P · r)
      (mq_busy_le_one P · r))]
  rw [← Summable.tsum_add (summable_sum (fun r _ => mq_summable_bounded hA r' _
      (mq_busy_nonneg P · r) (mq_busy_le_one P · r)))
    (mq_summable_bounded hA r' _ (mq_idle_nonneg P i) (fun n => by
      unfold Policy.idle; split_ifs <;> norm_num))]
  congr 1; funext n
  have := mq_busy_idle_sum P i n
  calc ∑ r ∈ net.C i, π n * P.busy n r * (n r' : ℝ) + π n * P.idle i n * (n r' : ℝ)
      = π n * (n r' : ℝ) * (∑ r ∈ net.C i, P.busy n r + P.idle i n) := by
        simp only [mul_add, Finset.mul_sum]; congr 1
        · apply Finset.sum_congr rfl; intro r _; ring
        · ring
    _ = π n * (n r' : ℝ) := by rw [this, mul_one]



open Finset in
theorem nonparam_core {N R : ℕ} (net : Network N R) (lam : Fin R → ℝ)
    (htraffic : net.IsTrafficSolution lam)
    (n : Fin R → ℝ) (I : Fin R → Fin R → ℝ) (Nv : Fin N → Fin R → ℝ)
    (hI : ∀ r r', 0 ≤ I r r') (hNv : ∀ i r', 0 ≤ Nv i r')
    (h24 : net.Eq24 lam n I) (h25 : net.Eq25 lam n I) (h28 : net.Eq28 n I Nv)
    (S : Finset (Fin R)) (f : Fin R → ℝ) (fi : Fin N → ℝ)
    (hF : net.FCondition S f fi) (hf : ∀ r ∈ S, 0 ≤ f r) :
    net.Nprime lam S f ≤ net.Dprime S f fi * ∑ r ∈ S, f r * n r := by
  -- symmetric second-moment combination
  set H : Fin R → Fin R → ℝ := fun r r' =>
    net.μ r * I r r' - ∑ w, net.μ w * net.p w r' * I w r - net.lam0 r' * n r with hH
  set c : Fin R → Fin R → ℝ := fun r r' =>
    (if r = r' then 2 * lam r else 0) - lam r * net.p r r' - lam r' * net.p r' r with hc
  have hG : ∀ r r', H r r' + H r' r = c r r' := by
    intro r r'
    rcases lt_trichotomy r' r with h | h | h
    · have := h25 r r' h
      simp only [hH, hc, if_neg (ne_of_gt h)]
      linarith
    · subst h
      have e24 := h24 r'
      have ht := htraffic r'
      have hs : ∑ w ∈ univ.erase r', lam w * net.p w r' = ∑ w, lam w * net.p w r'
          - lam r' * net.p r' r' := by
        rw [← Finset.add_sum_erase _ _ (mem_univ r')]; ring
      rw [hs] at e24
      simp only [hH, hc, if_true]
      linarith
    · have := h25 r' r h
      simp only [hH, hc, if_neg (ne_of_lt h)]
      linarith
  set J : Fin R → ℝ := fun w => ∑ r' ∈ S, f r' * I w r' with hJ
  set Φ := ∑ r ∈ S, f r * n r with hΦ
  set L := ∑ r ∈ S, net.lam0 r * f r with hL
  have hJ0 : ∀ w, 0 ≤ J w := fun w => sum_nonneg (fun r' hr' => mul_nonneg (hf r' hr') (hI w r'))
  -- double sum of H
  have hsumH : ∑ r ∈ S, ∑ r' ∈ S, f r * f r' * H r r'
      = ∑ r ∈ S, f r * net.μ r * J r - ∑ w, net.μ w * (∑ s ∈ S, net.p w s * f s) * J w - L * Φ := by
    simp only [hH, hJ, hL, hΦ, mul_sub, sum_sub_distrib, mul_sum, sum_mul]
    congr 1; congr 1
    · apply sum_congr rfl; intro r _; apply sum_congr rfl; intro r' _; ring
    · rw [Finset.sum_congr rfl (fun y _ => Finset.sum_comm)]; rw [Finset.sum_comm]
      apply sum_congr rfl; intro w _
      apply sum_congr rfl; intro x _; apply sum_congr rfl; intro y _; ring
    · apply sum_congr rfl; intro r _; apply sum_congr rfl; intro r' _; ring
  have hsym : ∑ r ∈ S, ∑ r' ∈ S, f r * f r' * c r r'
      = 2 * ∑ r ∈ S, ∑ r' ∈ S, f r * f r' * H r r' := by
    have e : ∑ r ∈ S, ∑ r' ∈ S, f r * f r' * H r' r = ∑ r ∈ S, ∑ r' ∈ S, f r * f r' * H r r' := by
      rw [sum_comm]; apply sum_congr rfl; intro r _; apply sum_congr rfl; intro r' _; ring
    rw [two_mul]; nth_rewrite 2 [← e]; rw [← sum_add_distrib]
    apply sum_congr rfl; intro r _; rw [← sum_add_distrib]
    apply sum_congr rfl; intro r' _; rw [← hG]; ring
  -- the c double sum equals N'
  have hN : net.Nprime lam S f = ∑ r ∈ S, ∑ r' ∈ S, f r * f r' * c r r' := by
    have e1 : ∑ r ∈ S, ∑ r' ∈ S, f r * f r' * c r r'
        = 2 * ∑ r ∈ S, lam r * f r ^ 2 - 2 * ∑ r ∈ S, ∑ r' ∈ S, lam r * net.p r r' * f r * f r' := by
      simp only [hc, mul_sub, sum_sub_distrib, mul_ite, mul_zero, sum_ite_eq, mul_sum]
      have e : ∑ r ∈ S, ∑ r' ∈ S, f r * f r' * (lam r' * net.p r' r)
          = ∑ r ∈ S, ∑ r' ∈ S, lam r * net.p r r' * f r * f r' := by
        rw [sum_comm]; apply sum_congr rfl; intro r _; apply sum_congr rfl; intro r' _; ring
      rw [e]
      have e2 : ∑ r ∈ S, ∑ r' ∈ S, f r * f r' * (lam r * net.p r r')
          = ∑ r ∈ S, ∑ r' ∈ S, lam r * net.p r r' * f r * f r' := by
        apply sum_congr rfl; intro r _; apply sum_congr rfl; intro r' _; ring
      rw [e2]
      have e3 : ∑ r ∈ S, (if r ∈ S then f r * f r * (2 * lam r) else 0)
          = 2 * ∑ r ∈ S, lam r * f r ^ 2 := by
        rw [mul_sum]; apply sum_congr rfl; intro r hr; rw [if_pos hr]; ring
      rw [e3]; ring_nf; simp only [Finset.sum_mul]
    rw [e1]
    -- traffic: ∑_r lam r net.p r r' = lam r' - net.lam0 r'
    have htr : ∀ r', ∑ r, lam r * net.p r r' = lam r' - net.lam0 r' := by
      intro r'; have := htraffic r'; linarith
    have hall : ∑ r, lam r * ∑ r' ∈ S, net.p r r' * f r' ^ 2 = ∑ r' ∈ S, (lam r' - net.lam0 r') * f r' ^ 2 := by
      simp only [mul_sum]; rw [sum_comm]; apply sum_congr rfl; intro r' _
      rw [← htr r', sum_mul]; apply sum_congr rfl; intro r _; ring
    have hsplit := sum_add_sum_compl S (fun r => lam r * ∑ r' ∈ S, net.p r r' * f r' ^ 2)
    have hrow : ∀ r, ∑ r' ∈ Sᶜ, net.p r r' + net.exitProb r = 1 - ∑ r' ∈ S, net.p r r' := by
      intro r; simp only [Network.exitProb]; have := sum_add_sum_compl S (fun r' => net.p r r'); 
      linarith
    simp only [Network.Nprime]
    simp only [hrow]
    have e4 : ∑ r ∈ S, lam r * (∑ r' ∈ S, net.p r r' * (f r - f r') ^ 2 + (1 - ∑ r' ∈ S, net.p r r') * f r ^ 2)
        = ∑ r ∈ S, lam r * f r ^ 2 - 2 * ∑ r ∈ S, ∑ r' ∈ S, lam r * net.p r r' * f r * f r'
          + ∑ r ∈ S, lam r * ∑ r' ∈ S, net.p r r' * f r' ^ 2 := by
      have hexp : ∀ r, ∑ r' ∈ S, net.p r r' * (f r - f r') ^ 2 = (∑ r' ∈ S, net.p r r') * f r ^ 2
          - 2 * f r * ∑ r' ∈ S, net.p r r' * f r' + ∑ r' ∈ S, net.p r r' * f r' ^ 2 := by
        intro r; rw [sum_mul, mul_sum, ← sum_sub_distrib, ← sum_add_distrib]
        apply sum_congr rfl; intro _ _; ring
      have hdbl : ∑ r ∈ S, ∑ r' ∈ S, lam r * net.p r r' * f r * f r'
          = ∑ r ∈ S, lam r * f r * ∑ r' ∈ S, net.p r r' * f r' := by
        apply sum_congr rfl; intro r _; rw [mul_sum]; apply sum_congr rfl; intro _ _; ring
      rw [hdbl]; simp only [hexp]
      rw [mul_sum, ← sum_sub_distrib, ← sum_add_distrib]; apply sum_congr rfl; intro r _; ring
    rw [e4]
    have e5 : ∑ r' ∈ S, (lam r' - net.lam0 r') * f r' ^ 2 = ∑ r ∈ S, lam r * f r ^ 2
        - ∑ r ∈ S, net.lam0 r * f r ^ 2 := by rw [← sum_sub_distrib]; apply sum_congr rfl; intro r _; ring
    linarith
  -- use FCondition
  have hFw : ∀ w ∈ S, net.μ w * f w - net.μ w * ∑ s ∈ S, net.p w s * f s = fi (net.σ w) := by
    intro w hw
    have h1 := hF.1 w hw
    have hs := sum_add_sum_compl S (fun s => net.p w s)
    simp only [Network.exitProb] at h1
    rw [← h1]
    have : ∑ r' ∈ S, net.p w r' * (f w - f r') = f w * ∑ r' ∈ S, net.p w r' - ∑ s ∈ S, net.p w s * f s := by
      rw [mul_sum, ← sum_sub_distrib]; apply sum_congr rfl; intro _ _; ring
    rw [this]
    have : ∑ r' ∈ Sᶜ, net.p w r' + (1 - ∑ s, net.p w s) = 1 - ∑ r' ∈ S, net.p w r' := by linarith
    rw [this]; ring
  have hsplitW : ∑ w, net.μ w * (∑ s ∈ S, net.p w s * f s) * J w
      = ∑ w ∈ S, net.μ w * (∑ s ∈ S, net.p w s * f s) * J w
        + ∑ w ∈ Sᶜ, net.μ w * (∑ s ∈ S, net.p w s * f s) * J w := (sum_add_sum_compl S _).symm
  have hnegpart : 0 ≤ ∑ w ∈ Sᶜ, net.μ w * (∑ s ∈ S, net.p w s * f s) * J w := by
    apply sum_nonneg; intro w _
    apply mul_nonneg (mul_nonneg (le_of_lt (net.μ_pos w)) ?_) (hJ0 w)
    exact sum_nonneg (fun s hs => mul_nonneg (net.p_nonneg w s) (hf s hs))
  have hmain : ∑ r ∈ S, f r * net.μ r * J r - ∑ w ∈ S, net.μ w * (∑ s ∈ S, net.p w s * f s) * J w
      = ∑ w ∈ S, fi (net.σ w) * J w := by
    rw [← sum_sub_distrib]; apply sum_congr rfl; intro w hw; rw [← hFw w hw]; ring
  have hfiber : ∑ w ∈ S, fi (net.σ w) * J w ≤ (∑ i, fi i) * Φ := by
    calc ∑ w ∈ S, fi (net.σ w) * J w ≤ ∑ w, fi (net.σ w) * J w :=
          sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun w _ _ =>
            mul_nonneg (hF.2.1 _) (hJ0 w))
      _ = ∑ i, ∑ w ∈ net.C i, fi (net.σ w) * J w := by
          rw [← sum_fiberwise univ net.σ]; rfl
      _ = ∑ i, fi i * (Φ - ∑ r' ∈ S, f r' * Nv i r') := by
          apply sum_congr rfl; intro i _
          have : ∀ w ∈ net.C i, fi (net.σ w) * J w = fi i * J w := by
            intro w hw; simp [Network.C] at hw; rw [hw]
          rw [sum_congr rfl this, ← mul_sum]; congr 1
          simp only [hJ, hΦ]; rw [sum_comm, ← sum_sub_distrib]; apply sum_congr rfl
          intro r' _; rw [← mul_sum, ← h28 i r']; ring
      _ ≤ ∑ i, fi i * Φ := by
          apply sum_le_sum; intro i _
          apply mul_le_mul_of_nonneg_left _ (hF.2.1 i)
          have : 0 ≤ ∑ r' ∈ S, f r' * Nv i r' :=
            sum_nonneg (fun r' hr' => mul_nonneg (hf r' hr') (hNv i r'))
          linarith
      _ = (∑ i, fi i) * Φ := by rw [sum_mul]
  rw [hN, hsym, hsumH]
  simp only [Network.Dprime]
  rw [← hL]
  nlinarith [hfiber, hnegpart, hmain, hsplitW]



/-- transition rates of the chain, indexed by a finite type -/
noncomputable def mqRate {N R : ℕ} {net : Network N R} (P : Policy net) (n : Fin R → ℕ) :
    Fin R ⊕ (Fin R × Option (Fin R)) → ℝ
  | Sum.inl r => net.lam0 r
  | Sum.inr (r, some s) => P.busy n r * net.μ r * net.p r s
  | Sum.inr (r, none) => P.busy n r * net.μ r * net.exitProb r

/-- target states of the transitions -/
def mqJump {R : ℕ} (n : Fin R → ℕ) : Fin R ⊕ (Fin R × Option (Fin R)) → (Fin R → ℕ)
  | Sum.inl r => n + unitVec r
  | Sum.inr (r, some s) => n - unitVec r + unitVec s
  | Sum.inr (r, none) => n - unitVec r

lemma mq_gen_eq {N R : ℕ} {net : Network N R} (P : Policy net) (g : (Fin R → ℕ) → ℝ)
    (n : Fin R → ℕ) :
    P.generator g n = ∑ k, mqRate P n k * (g (mqJump n k) - g n) := by
  unfold Policy.generator
  rw [Fintype.sum_sum_type]
  simp only [Fintype.sum_prod_type, Fintype.sum_option, mqRate, mqJump]
  congr 1
  apply Finset.sum_congr rfl; intro r _
  rw [mul_add, Finset.mul_sum]; rw [add_comm]; congr 1
  · ring
  · apply Finset.sum_congr rfl; intro s _; ring

lemma mq_exit_nonneg {N R : ℕ} (net : Network N R) (r : Fin R) : 0 ≤ net.exitProb r := by
  unfold Network.exitProb; linarith [net.p_row_sum_le_one r]

lemma mq_rate_nonneg {N R : ℕ} {net : Network N R} (P : Policy net) (n) (k) :
    0 ≤ mqRate P n k := by
  have hb : 0 ≤ P.busy n := fun r => by unfold Policy.busy; split_ifs <;> norm_num
  rcases k with r | ⟨r, _ | s⟩
  · exact net.lam0_nonneg r
  · exact mul_nonneg (mul_nonneg (hb r) (net.μ_pos r).le) (mq_exit_nonneg net r)
  · exact mul_nonneg (mul_nonneg (hb r) (net.μ_pos r).le) (net.p_nonneg r s)

/-- rate bound independent of the state -/
noncomputable def mqRateMax {N R : ℕ} (net : Network N R) :
    Fin R ⊕ (Fin R × Option (Fin R)) → ℝ
  | Sum.inl r => net.lam0 r
  | Sum.inr (r, some s) => net.μ r * net.p r s
  | Sum.inr (r, none) => net.μ r * net.exitProb r

lemma mq_rate_le {N R : ℕ} {net : Network N R} (P : Policy net) (n) (k) :
    mqRate P n k ≤ mqRateMax net k := by
  have hb : ∀ r, P.busy n r ≤ 1 := fun r => by unfold Policy.busy; split_ifs <;> norm_num
  have hb0 : ∀ r, 0 ≤ P.busy n r := fun r => by unfold Policy.busy; split_ifs <;> norm_num
  rcases k with r | ⟨r, _ | s⟩
  · exact le_rfl
  · simp only [mqRate, mqRateMax]
    have := mul_nonneg (net.μ_pos r).le (mq_exit_nonneg net r)
    nlinarith [hb r, hb0 r]
  · simp only [mqRate, mqRateMax]
    have := mul_nonneg (net.μ_pos r).le (net.p_nonneg r s)
    nlinarith [hb r, hb0 r]

lemma mq_hasSum_gen {N R : ℕ} {net : Network N R} (P : Policy net) (g : (Fin R → ℕ) → ℝ)
    (n : Fin R → ℕ) :
    HasSum (fun m => g m * P.generator (fun k => if k = m then 1 else 0) n) (P.generator g n) := by
  have e : (fun m => g m * P.generator (fun k => if k = m then 1 else 0) n) =
      fun m => ∑ k, mqRate P n k * ((if mqJump n k = m then g m else 0) -
        (if n = m then g m else 0)) := by
    funext m; rw [mq_gen_eq, Finset.mul_sum]; apply Finset.sum_congr rfl; intro k _
    split_ifs <;> ring
  rw [e, mq_gen_eq]
  apply hasSum_sum; intro k _
  apply HasSum.mul_left
  apply HasSum.sub
  · convert hasSum_single (mqJump n k) (fun b hb => if_neg (Ne.symm hb)) using 1; simp
  · convert hasSum_single n (fun b hb => if_neg (Ne.symm hb)) using 1; simp

lemma mq_hasSum_bound {N R : ℕ} {net : Network N R} (P : Policy net) (g : (Fin R → ℕ) → ℝ)
    (n : Fin R → ℕ) :
    HasSum (fun m => ∑ k, mqRate P n k * ((if mqJump n k = m then |g m| else 0) +
        (if n = m then |g m| else 0)))
      (∑ k, mqRate P n k * (|g (mqJump n k)| + |g n|)) := by
  apply hasSum_sum; intro k _
  apply HasSum.mul_left
  apply HasSum.add
  · convert hasSum_single (mqJump n k) (fun b hb => if_neg (Ne.symm hb)) using 1; simp
  · convert hasSum_single n (fun b hb => if_neg (Ne.symm hb)) using 1; simp

/-- Balance for an unbounded test function. -/
theorem mq_balance {N R : ℕ} {net : Network N R} (P : Policy net) (π : (Fin R → ℕ) → ℝ)
    (hinv : P.IsInvariant π) (g : (Fin R → ℕ) → ℝ)
    (hs : Summable (fun n => π n * ∑ k, mqRate P n k * (|g (mqJump n k)| + |g n|))) :
    ∑' n, π n * P.generator g n = 0 := by
  set F : (Fin R → ℕ) × (Fin R → ℕ) → ℝ :=
    fun q => π q.1 * (g q.2 * P.generator (fun k => if k = q.2 then 1 else 0) q.1) with hF
  set G : (Fin R → ℕ) × (Fin R → ℕ) → ℝ :=
    fun q => π q.1 * ∑ k, mqRate P q.1 k * ((if mqJump q.1 k = q.2 then |g q.2| else 0) +
        (if q.1 = q.2 then |g q.2| else 0)) with hG
  have hG0 : 0 ≤ G := by
    intro q; apply mul_nonneg (hinv.1 q.1); apply Finset.sum_nonneg; intro k _
    apply mul_nonneg (mq_rate_nonneg P _ k)
    apply add_nonneg <;> split_ifs <;> simp
  have hGs : Summable G := by
    rw [summable_prod_of_nonneg hG0]
    refine ⟨fun n => ((mq_hasSum_bound P g n).mul_left (π n)).summable, ?_⟩
    convert hs using 1; funext n
    exact ((mq_hasSum_bound P g n).mul_left (π n)).tsum_eq
  have hFG : ∀ q, ‖F q‖ ≤ G q := by
    intro q
    simp only [hF, hG, Real.norm_eq_abs]
    rw [mq_gen_eq, abs_mul, abs_of_nonneg (hinv.1 q.1)]
    apply mul_le_mul_of_nonneg_left _ (hinv.1 q.1)
    rw [Finset.mul_sum]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ => ?_)
    rw [abs_mul, abs_mul, abs_of_nonneg (mq_rate_nonneg P _ k)]
    rw [← mul_assoc, mul_comm |g q.2|, mul_assoc]
    apply mul_le_mul_of_nonneg_left _ (mq_rate_nonneg P _ k)
    split_ifs <;> simp [abs_nonneg]
  have hFs : Summable F := Summable.of_norm_bounded hGs hFG
  have h1 : ∀ n, ∑' m, F (n, m) = π n * P.generator g n := by
    intro n; exact ((mq_hasSum_gen P g n).mul_left (π n)).tsum_eq
  have h2 : ∀ m, ∑' n, F (n, m) = 0 := by
    intro m
    have : (fun n => F (n, m)) = fun n => g m * (π n * P.generator (fun k => if k = m then 1 else 0) n) := by
      funext n; simp only [hF]; ring
    rw [this, tsum_mul_left, (hinv.2.2 m).tsum_eq, mul_zero]
  calc ∑' n, π n * P.generator g n = ∑' n, ∑' m, F (n, m) := by simp only [h1]
    _ = ∑' m, ∑' n, F (n, m) := (Summable.tsum_comm (f := fun n m => F (n, m)) hFs).symm
    _ = 0 := by simp only [h2, tsum_zero]

lemma mq_unit_le {R : ℕ} (t r : Fin R) : unitVec t r ≤ 1 := by
  simp only [unitVec, Pi.single_apply]; split_ifs <;> simp

lemma mq_jump_le {R : ℕ} (n : Fin R → ℕ) (k) (r : Fin R) : mqJump n k r ≤ n r + 1 := by
  rcases k with t | ⟨t, _ | s⟩
  · simp only [mqJump, Pi.add_apply]; have := mq_unit_le t r; omega
  · simp only [mqJump, Pi.sub_apply]; omega
  · simp only [mqJump, Pi.add_apply, Pi.sub_apply]; have := mq_unit_le s r; omega

lemma mq_sq_jump_le {R : ℕ} (n : Fin R → ℕ) (k) :
    1 + ∑ r, ((mqJump n k r : ℕ) : ℝ) ^ 2 ≤ (2 * R + 3) * (1 + ∑ r, ((n r : ℕ) : ℝ) ^ 2) := by
  have h : ∀ r, ((mqJump n k r : ℕ) : ℝ) ^ 2 ≤ 2 * ((n r : ℕ) : ℝ) ^ 2 + 2 := by
    intro r
    have h1 : ((mqJump n k r : ℕ) : ℝ) ≤ (n r : ℝ) + 1 := by exact_mod_cast mq_jump_le n k r
    have h0 : (0:ℝ) ≤ (mqJump n k r : ℝ) := by positivity
    nlinarith [sq_nonneg ((n r : ℝ) - 1)]
  have hs := Finset.sum_le_sum (fun r (_ : r ∈ Finset.univ) => h r)
  rw [Finset.sum_add_distrib, ← Finset.mul_sum] at hs
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hs
  have hQ : 0 ≤ ∑ r, ((n r : ℕ) : ℝ) ^ 2 := Finset.sum_nonneg (fun r _ => by positivity)
  have hR : (0:ℝ) ≤ R := by positivity
  nlinarith

theorem mq_balance_poly {N R : ℕ} {net : Network N R} (P : Policy net) (π : (Fin R → ℕ) → ℝ)
    (hA : P.AssumptionA π) (g : (Fin R → ℕ) → ℝ) (A : ℝ) (hA0 : 0 ≤ A)
    (hg : ∀ m, |g m| ≤ A * (1 + ∑ r, ((m r : ℕ) : ℝ) ^ 2)) :
    ∑' n, π n * P.generator g n = 0 := by
  apply mq_balance P π hA.1 g
  set T : (Fin R → ℕ) → ℝ := fun n => 1 + ∑ r, ((n r : ℕ) : ℝ) ^ 2 with hT
  have hT0 : ∀ n, 0 ≤ T n := fun n => by
    simp only [hT]; have := Finset.sum_nonneg (fun r (_ : r ∈ Finset.univ) =>
      sq_nonneg ((n r : ℕ) : ℝ)); linarith
  have hπT : Summable (fun n => π n * T n) := by
    simp only [hT, mul_add, mul_one, Finset.mul_sum]
    exact hA.1.2.1.summable.add (summable_sum (fun r _ => hA.2.2 r))
  refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_)
    (hπT.mul_left ((∑ k, mqRateMax net k) * (A * (2 * R + 4))))
  · apply mul_nonneg (hA.1.1 n); apply Finset.sum_nonneg; intro k _
    exact mul_nonneg (mq_rate_nonneg P n k) (by positivity)
  · have hπ := hA.1.1 n
    have hk : ∀ k, mqRate P n k * (|g (mqJump n k)| + |g n|) ≤
        mqRateMax net k * (A * (2 * R + 4) * T n) := by
      intro k
      have h1 := hg (mqJump n k)
      have h2 := hg n
      have h3 := mq_sq_jump_le n k
      have hR : (0:ℝ) ≤ R := by positivity
      have hb : |g (mqJump n k)| + |g n| ≤ A * (2 * R + 4) * T n := by
        have : A * (1 + ∑ r, ((mqJump n k r : ℕ) : ℝ) ^ 2) ≤ A * ((2 * R + 3) * T n) :=
          mul_le_mul_of_nonneg_left h3 hA0
        simp only [hT] at *
        nlinarith
      exact mul_le_mul (mq_rate_le P n k) hb (by positivity) ((mq_rate_nonneg P n k).trans
        (mq_rate_le P n k))
    calc π n * ∑ k, mqRate P n k * (|g (mqJump n k)| + |g n|)
        ≤ π n * ∑ k, mqRateMax net k * (A * (2 * R + 4) * T n) :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun k _ => hk k) hπ
      _ = (∑ k, mqRateMax net k) * (A * (2 * R + 4)) * (π n * T n) := by
          rw [Finset.sum_mul, Finset.sum_mul, Finset.mul_sum]
          apply Finset.sum_congr rfl; intro k _; ring

lemma mq_cast_up {R : ℕ} (n : Fin R → ℕ) (t r : Fin R) :
    (((n + unitVec t) r : ℕ) : ℝ) = n r + (if r = t then 1 else 0) := by
  simp only [unitVec, Pi.add_apply, Pi.single_apply]; split_ifs <;> simp

lemma mq_cast_down {N R : ℕ} {net : Network N R} (P : Policy net) (n : Fin R → ℕ) (w : Fin R)
    (h : P.serve n w = true) (r : Fin R) :
    (((n - unitVec w) r : ℕ) : ℝ) = n r - (if r = w then 1 else 0) := by
  have h1 := P.serve_present n w h
  simp only [unitVec, Pi.sub_apply, Pi.single_apply]
  split_ifs with hr
  · subst hr; rw [Nat.cast_sub h1]; simp
  · simp

lemma mq_cast_move {N R : ℕ} {net : Network N R} (P : Policy net) (n : Fin R → ℕ) (w s : Fin R)
    (h : P.serve n w = true) (r : Fin R) :
    (((n - unitVec w + unitVec s) r : ℕ) : ℝ) = n r - (if r = w then 1 else 0)
      + (if r = s then 1 else 0) := by
  rw [mq_cast_up, mq_cast_down P n w h]

lemma mq_busy_mul {N R : ℕ} {net : Network N R} (P : Policy net) (n : Fin R → ℕ) (w : Fin R)
    (X Y : ℝ) (h : P.serve n w = true → X = Y) : P.busy n w * X = P.busy n w * Y := by
  unfold Policy.busy; split_ifs with hs
  · rw [h hs]
  · simp

lemma mq_sum_p_exit {N R : ℕ} (net : Network N R) (w : Fin R) :
    ∑ s, net.p w s + net.exitProb w = 1 := by unfold Network.exitProb; ring

lemma mq_gen_lin {N R : ℕ} {net : Network N R} (P : Policy net) (n : Fin R → ℕ) (r : Fin R) :
    P.generator (fun m => ((m r : ℕ) : ℝ)) n
      = net.lam0 r + ∑ w, P.busy n w * net.μ w * net.p w r - P.busy n r * net.μ r := by
  unfold Policy.generator
  have e1 : ∑ t, net.lam0 t * ((((n + unitVec t) r : ℕ) : ℝ) - n r) = net.lam0 r := by
    simp only [mq_cast_up, add_sub_cancel_left, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq]; simp
  rw [e1]
  have e2 : ∀ w, P.busy n w * net.μ w *
      (∑ s, net.p w s * ((((n - unitVec w + unitVec s) r : ℕ) : ℝ) - n r) +
        net.exitProb w * ((((n - unitVec w) r : ℕ) : ℝ) - n r))
      = P.busy n w * net.μ w * net.p w r - (if r = w then P.busy n w * net.μ w else 0) := by
    intro w
    rw [mul_assoc]
    have := mq_busy_mul P n w (net.μ w * (∑ s, net.p w s * ((((n - unitVec w + unitVec s) r : ℕ) : ℝ) - n r) +
        net.exitProb w * ((((n - unitVec w) r : ℕ) : ℝ) - n r)))
      (net.μ w * (net.p w r - if r = w then 1 else 0)) (fun h => by
        simp only [mq_cast_move P n w _ h, mq_cast_down P n w h]
        have hs : ∑ s, net.p w s * ((n r : ℝ) - (if r = w then 1 else 0) + (if r = s then 1 else 0) - n r)
            = net.p w r - (∑ s, net.p w s) * (if r = w then 1 else 0) := by
          have : ∀ s, net.p w s * ((n r : ℝ) - (if r = w then 1 else 0) + (if r = s then 1 else 0) - n r)
              = (if r = s then net.p w s else 0) - net.p w s * (if r = w then 1 else 0) := by
            intro s; split_ifs <;> ring
          simp only [this, Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true,
            Finset.sum_mul]
        rw [hs]
        have := mq_sum_p_exit net w
        congr 1
        split_ifs <;> simp <;> linarith)
    rw [this]; split_ifs <;> ring
  simp only [e2, Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  ring

lemma mq_hasSum_busy {N R : ℕ} {net : Network N R} (P : Policy net) (π : (Fin R → ℕ) → ℝ)
    (hA : P.AssumptionA π) (w : Fin R) :
    HasSum (fun n => π n * P.busy n w) (P.busyProb π w) := by
  apply Summable.hasSum
  refine Summable.of_nonneg_of_le (fun n => mul_nonneg (hA.1.1 n) ?_) (fun n => ?_)
    hA.1.2.1.summable
  · unfold Policy.busy; split_ifs <;> norm_num
  · have := hA.1.1 n
    unfold Policy.busy; split_ifs <;> simp [this]

theorem utilization_core {N R : ℕ} (net : Network N R) (lam : Fin R → ℝ)
    (htraffic : net.IsTrafficSolution lam) (hopen : net.IsOpen)
    (P : Policy net) (π : (Fin R → ℕ) → ℝ) (hA : P.AssumptionA π) :
    ∀ r, P.busyProb π r = lam r / net.μ r := by
  set U := P.busyProb π with hU
  have key : ∀ r, net.lam0 r + ∑ w, net.μ w * net.p w r * U w - net.μ r * U r = 0 := by
    intro r
    have H : HasSum (fun n => net.lam0 r * π n + ∑ w, net.μ w * net.p w r * (π n * P.busy n w)
        - net.μ r * (π n * P.busy n r))
        (net.lam0 r * 1 + ∑ w, net.μ w * net.p w r * U w - net.μ r * U r) :=
      ((hA.1.2.1.mul_left _).add (hasSum_sum fun w _ => (mq_hasSum_busy P π hA w).mul_left _)).sub
        ((mq_hasSum_busy P π hA r).mul_left _)
    have h0 := mq_balance_poly P π hA (fun m => ((m r : ℕ) : ℝ)) 1 zero_le_one (fun m => by
      rw [abs_of_nonneg (by positivity), one_mul]
      have : ((m r : ℕ) : ℝ) ≤ 1 + ((m r : ℕ) : ℝ) ^ 2 := by nlinarith [sq_nonneg (((m r : ℕ) : ℝ) - 1)]
      have h2 : ((m r : ℕ) : ℝ) ^ 2 ≤ ∑ t, ((m t : ℕ) : ℝ) ^ 2 :=
        Finset.single_le_sum (f := fun t => ((m t : ℕ) : ℝ) ^ 2) (fun t _ => by positivity)
          (Finset.mem_univ r)
      linarith)
    have e : (fun n => π n * P.generator (fun m => ((m r : ℕ) : ℝ)) n) =
        (fun n => net.lam0 r * π n + ∑ w, net.μ w * net.p w r * (π n * P.busy n w)
          - net.μ r * (π n * P.busy n r)) := by
      funext n; rw [mq_gen_lin, mul_sub, mul_add, Finset.mul_sum]
      congr 1; congr 1
      · ring
      · apply Finset.sum_congr rfl; intro w _; ring
      · ring
    rw [e, H.tsum_eq, mul_one] at h0
    exact h0
  have hv : (fun w => net.μ w * U w - lam w) = 0 := by
    apply hopen
    intro r
    have h1 := key r
    have h2 := htraffic r
    have : ∑ r', (net.μ r' * U r' - lam r') * net.p r' r
        = ∑ w, net.μ w * net.p w r * U w - ∑ r', lam r' * net.p r' r := by
      rw [← Finset.sum_sub_distrib]; apply Finset.sum_congr rfl; intro w _; ring
    rw [this]; linarith
  intro r
  have := congrFun hv r
  simp only [Pi.zero_apply] at this
  have hμ := net.μ_pos r
  rw [eq_div_iff hμ.ne']; linarith

lemma mq_gen_quad {N R : ℕ} {net : Network N R} (P : Policy net) (n : Fin R → ℕ) (a b : Fin R) :
    P.generator (fun m => ((m a : ℕ) : ℝ) * ((m b : ℕ) : ℝ)) n
      = net.lam0 a * n b + net.lam0 b * n a + (if b = a then net.lam0 a else 0) +
        ∑ w, P.busy n w * net.μ w * (net.p w b * n a + net.p w a * n b
          - (if b = w then 1 else 0) * n a - (if a = w then 1 else 0) * n b
          + (if b = a then net.p w a else 0) - (if b = w then 1 else 0) * net.p w a
          - (if a = w then 1 else 0) * net.p w b
          + (if a = w then 1 else 0) * (if b = w then 1 else 0)) := by
  unfold Policy.generator
  have e1 : ∑ t, net.lam0 t * ((((n + unitVec t) a : ℕ) : ℝ) * (((n + unitVec t) b : ℕ) : ℝ)
      - (n a : ℝ) * n b) = net.lam0 a * n b + net.lam0 b * n a + (if b = a then net.lam0 a else 0) := by
    simp only [mq_cast_up]
    have : ∀ t, net.lam0 t * (((n a : ℝ) + (if a = t then 1 else 0)) * ((n b : ℝ) + (if b = t then 1 else 0))
        - (n a : ℝ) * n b) = (if a = t then net.lam0 t * n b else 0) + (if b = t then net.lam0 t * n a else 0)
          + (if a = t then (if b = t then net.lam0 t else 0) else 0) := by
      intro t; split_ifs <;> ring
    simp only [this, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [e1]
  congr 1
  apply Finset.sum_congr rfl; intro w _
  rw [mul_assoc, mul_assoc]
  apply mq_busy_mul P n w
  intro h
  congr 1
  simp only [mq_cast_move P n w _ h, mq_cast_down P n w h]
  set α : ℝ := if a = w then 1 else 0 with hα
  set β : ℝ := if b = w then 1 else 0 with hβ
  have hsp : ∀ s, net.p w s * (((n a : ℝ) - α + (if a = s then 1 else 0)) *
      ((n b : ℝ) - β + (if b = s then 1 else 0)) - (n a : ℝ) * n b)
      = net.p w s * (((n a : ℝ) - α) * ((n b : ℝ) - β) - (n a : ℝ) * n b)
        + (if a = s then net.p w s * ((n b : ℝ) - β) else 0)
        + (if b = s then net.p w s * ((n a : ℝ) - α) else 0)
        + (if a = s then (if b = s then net.p w s else 0) else 0) := by
    intro s; split_ifs <;> ring
  simp only [hsp, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true,
    ← Finset.sum_mul]
  have hpe := mq_sum_p_exit net w
  have hexit : net.exitProb w = 1 - ∑ s, net.p w s := by linarith
  rw [hexit]
  ring

lemma mq_hasSum_mom {N R : ℕ} {net : Network N R} (P : Policy net) (π : (Fin R → ℕ) → ℝ)
    (hA : P.AssumptionA π) (w t : Fin R) :
    HasSum (fun n => π n * P.busy n w * (n t : ℝ)) (P.busyMoment π w t) :=
  (mq_summable_bounded hA t _ (mq_busy_nonneg P · w) (mq_busy_le_one P · w)).hasSum

theorem mq_quad {N R : ℕ} (net : Network N R) (lam : Fin R → ℝ)
    (htraffic : net.IsTrafficSolution lam) (hopen : net.IsOpen)
    (P : Policy net) (π : (Fin R → ℕ) → ℝ) (hA : P.AssumptionA π) (a b : Fin R) :
    net.lam0 a * meanNum π b + net.lam0 b * meanNum π a
      + (if b = a then net.lam0 a + ∑ w, lam w * net.p w a + lam a else 0)
      + ∑ w, net.μ w * net.p w b * P.busyMoment π w a
      + ∑ w, net.μ w * net.p w a * P.busyMoment π w b
      - net.μ b * P.busyMoment π b a - net.μ a * P.busyMoment π a b
      - lam b * net.p b a - lam a * net.p a b = 0 := by
  have hU := utilization_core net lam htraffic hopen P π hA
  have hμU : ∀ w, net.μ w * P.busyProb π w = lam w := by
    intro w; rw [hU w]; field_simp [(net.μ_pos w).ne']
  have hM : ∀ t, HasSum (fun n => π n * (n t : ℝ)) (meanNum π t) :=
    fun t => (mq_summable_lin hA t).hasSum
  set c : Fin R → ℝ := fun w => (if b = a then net.p w a else 0)
    - (if b = w then 1 else 0) * net.p w a - (if a = w then 1 else 0) * net.p w b
    + (if a = w then 1 else 0) * (if b = w then 1 else 0) with hc
  have H : HasSum (fun n => net.lam0 a * (π n * (n b : ℝ)) + net.lam0 b * (π n * (n a : ℝ))
      + (if b = a then net.lam0 a else 0) * π n
      + ∑ w, (net.μ w * net.p w b * (π n * P.busy n w * (n a : ℝ))
        + net.μ w * net.p w a * (π n * P.busy n w * (n b : ℝ))
        - net.μ w * (if b = w then 1 else 0) * (π n * P.busy n w * (n a : ℝ))
        - net.μ w * (if a = w then 1 else 0) * (π n * P.busy n w * (n b : ℝ))
        + net.μ w * c w * (π n * P.busy n w)))
      (net.lam0 a * meanNum π b + net.lam0 b * meanNum π a
      + (if b = a then net.lam0 a else 0) * 1
      + ∑ w, (net.μ w * net.p w b * P.busyMoment π w a
        + net.μ w * net.p w a * P.busyMoment π w b
        - net.μ w * (if b = w then 1 else 0) * P.busyMoment π w a
        - net.μ w * (if a = w then 1 else 0) * P.busyMoment π w b
        + net.μ w * c w * P.busyProb π w)) :=
    ((((hM b).mul_left _).add ((hM a).mul_left _)).add (hA.1.2.1.mul_left _)).add
      (hasSum_sum fun w _ => (((((mq_hasSum_mom P π hA w a).mul_left _).add
        ((mq_hasSum_mom P π hA w b).mul_left _)).sub ((mq_hasSum_mom P π hA w a).mul_left _)).sub
        ((mq_hasSum_mom P π hA w b).mul_left _)).add ((mq_hasSum_busy P π hA w).mul_left _))
  have h0 := mq_balance_poly P π hA (fun m => ((m a : ℕ) : ℝ) * ((m b : ℕ) : ℝ)) 1 zero_le_one
    (fun m => by
      rw [abs_of_nonneg (by positivity), one_mul]
      have ha : ((m a : ℕ) : ℝ) ^ 2 ≤ ∑ t, ((m t : ℕ) : ℝ) ^ 2 :=
        Finset.single_le_sum (f := fun t => ((m t : ℕ) : ℝ) ^ 2) (fun t _ => by positivity)
          (Finset.mem_univ a)
      have hb : ((m b : ℕ) : ℝ) ^ 2 ≤ ∑ t, ((m t : ℕ) : ℝ) ^ 2 :=
        Finset.single_le_sum (f := fun t => ((m t : ℕ) : ℝ) ^ 2) (fun t _ => by positivity)
          (Finset.mem_univ b)
      nlinarith [sq_nonneg (((m a : ℕ) : ℝ) - ((m b : ℕ) : ℝ))])
  have e : (fun n => π n * P.generator (fun m => ((m a : ℕ) : ℝ) * ((m b : ℕ) : ℝ)) n) =
      (fun n => net.lam0 a * (π n * (n b : ℝ)) + net.lam0 b * (π n * (n a : ℝ))
      + (if b = a then net.lam0 a else 0) * π n
      + ∑ w, (net.μ w * net.p w b * (π n * P.busy n w * (n a : ℝ))
        + net.μ w * net.p w a * (π n * P.busy n w * (n b : ℝ))
        - net.μ w * (if b = w then 1 else 0) * (π n * P.busy n w * (n a : ℝ))
        - net.μ w * (if a = w then 1 else 0) * (π n * P.busy n w * (n b : ℝ))
        + net.μ w * c w * (π n * P.busy n w))) := by
    funext n; rw [mq_gen_quad, mul_add, mul_add, mul_add, Finset.mul_sum]
    congr 1
    · ring
    · apply Finset.sum_congr rfl; intro w _; simp only [hc]; ring
  rw [e, H.tsum_eq] at h0
  have s1 : ∑ w, net.μ w * (if b = w then 1 else 0) * P.busyMoment π w a
      = net.μ b * P.busyMoment π b a := by
    simp only [mul_ite, ite_mul, mul_one, mul_zero, zero_mul, Finset.sum_ite_eq, Finset.mem_univ,
      if_true]
  have s2 : ∑ w, net.μ w * (if a = w then 1 else 0) * P.busyMoment π w b
      = net.μ a * P.busyMoment π a b := by
    simp only [mul_ite, ite_mul, mul_one, mul_zero, zero_mul, Finset.sum_ite_eq, Finset.mem_univ,
      if_true]
  have s3 : ∑ w, net.μ w * c w * P.busyProb π w
      = (if b = a then ∑ w, lam w * net.p w a + lam a else 0)
        - lam b * net.p b a - lam a * net.p a b := by
    have : ∀ w, net.μ w * c w * P.busyProb π w = (if b = a then 1 else 0) * (lam w * net.p w a)
        - (if b = w then lam b * net.p b a else 0) - (if a = w then lam a * net.p a b else 0)
        + (if a = w then (if b = a then lam a else 0) else 0) := by
      intro w; rw [mul_assoc, mul_comm (c w), ← mul_assoc, hμU w]; simp only [hc]
      clear hc H h0 e
      split_ifs <;> subst_vars <;> first | contradiction | ring
    rw [Finset.sum_congr rfl (fun w _ => this w)]
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.mem_univ,
      if_true, ← Finset.mul_sum]
    split_ifs <;> ring
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, s1, s2, s3] at h0
  have : (if b = a then net.lam0 a else 0) * 1 + (if b = a then ∑ w, lam w * net.p w a + lam a else 0)
      = (if b = a then net.lam0 a + ∑ w, lam w * net.p w a + lam a else 0) := by
    split_ifs <;> ring
  linarith

theorem second_moment_core {N R : ℕ} (net : Network N R) (lam : Fin R → ℝ)
    (htraffic : net.IsTrafficSolution lam) (hopen : net.IsOpen)
    (P : Policy net) (π : (Fin R → ℕ) → ℝ) (hA : P.AssumptionA π) :
    net.Eq24 lam (meanNum π) (P.busyMoment π) ∧
      net.Eq25 lam (meanNum π) (P.busyMoment π) := by
  constructor
  · intro r
    have h := mq_quad net lam htraffic hopen P π hA r r
    rw [if_pos rfl] at h
    have hs : ∑ w ∈ Finset.univ.erase r, lam w * net.p w r = ∑ w, lam w * net.p w r
        - lam r * net.p r r := by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ r)]; ring
    rw [hs]
    linarith
  · intro r r' h
    have h1 := mq_quad net lam htraffic hopen P π hA r r'
    rw [if_neg (ne_of_lt h)] at h1
    linarith

theorem potential_bound_core {N R : ℕ} (net : Network N R) (lam : Fin R → ℝ)
    (htraffic : net.IsTrafficSolution lam) (hopen : net.IsOpen)
    (P : Policy net) (π : (Fin R → ℕ) → ℝ) (hA : P.AssumptionA π)
    (S : Finset (Fin R)) (f : Fin R → ℝ) (fi : Fin N → ℝ)
    (h17 : net.FCondition S f fi) (hf : ∀ r ∈ S, 0 ≤ f r) :
    net.Nprime lam S f ≤ net.Dprime S f fi * ∑ r ∈ S, f r * meanNum π r := by
  obtain ⟨h24, h25⟩ := second_moment_core net lam htraffic hopen P π hA
  have h28 := idle_busy_core net P π hA
  refine nonparam_core net lam htraffic (meanNum π) (P.busyMoment π) (P.idleMoment π)
    (fun r r' => ?_) (fun i r' => ?_) h24 h25 h28 S f fi h17 hf
  · exact tsum_nonneg fun n => mul_nonneg (mul_nonneg (hA.1.1 n) (mq_busy_nonneg P n r))
      (by positivity)
  · exact tsum_nonneg fun n => mul_nonneg (mul_nonneg (hA.1.1 n) (mq_idle_nonneg P i n))
      (by positivity)

end MulticlassQNet.FirstOrder

open MulticlassQNet.FirstOrder


theorem solution {N R : ℕ} (net : Network N R) (lam : Fin R → ℝ)
    (htraffic : net.IsTrafficSolution lam) (hopen : net.IsOpen) (hload : net.LoadLtOne lam)
    (P : Policy net) (π : (Fin R → ℕ) → ℝ) (hA : P.AssumptionA π) :
    net.Eq24 lam (meanNum π) (P.busyMoment π) ∧
      net.Eq25 lam (meanNum π) (P.busyMoment π) := by
  exact second_moment_core net lam htraffic hopen P π hA
