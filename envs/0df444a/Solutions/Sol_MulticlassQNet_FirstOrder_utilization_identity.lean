-- Prove2me | solution 1 for MulticlassQNet.FirstOrder.utilization_identity
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-06T05:29:07.277985+00:00
-- url     : https://prove2.me/submissions/3966c768-ba44-4dc2-848e-0b6a96ea812c

import Mathlib
import Definitions.Def_MulticlassQNet_FirstOrder_Network
import Definitions.Def_MulticlassQNet_FirstOrder_Dynamics



namespace MulticlassQNet.FirstOrder

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

end MulticlassQNet.FirstOrder

open MulticlassQNet.FirstOrder


theorem solution {N R : ℕ} (net : Network N R) (lam : Fin R → ℝ)
    (htraffic : net.IsTrafficSolution lam) (hopen : net.IsOpen) (hload : net.LoadLtOne lam)
    (P : Policy net) (π : (Fin R → ℕ) → ℝ) (hA : P.AssumptionA π) :
    ∀ r, P.busyProb π r = lam r / net.μ r := by
  exact utilization_core net lam htraffic hopen P π hA
