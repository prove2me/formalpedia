-- Prove2me | solution 1 for JewellMRP.Discounted.policyIteration_optimal_stationary
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T23:59:43.11231+00:00
-- url     : https://prove2.me/submissions/69fac82e-eb48-487f-9398-b18be421b31f

import Mathlib
import Definitions.Def_JewellMRP_Discounted_MRP
import Definitions.Def_JewellMRP_Discounted_PolicyIteration

open Filter Topology


namespace JewellMRP.Discounted

open MeasureTheory

section
variable {S A : Type*} [Fintype S]

lemma pi_ftilde_nonneg (M : MRP S A) (z : A) (i j : S) (s : ℝ) : 0 ≤ ftilde M z i j s :=
  setIntegral_nonneg measurableSet_Ioi (fun t _ => (Real.exp_pos _).le)

lemma pi_ftilde_lt_one (M : MRP S A) (z : A) (i j : S) {α : ℝ} (hα : 0 < α) :
    ftilde M z i j α < 1 := by
  haveI := M.F_prob z i j
  have hIoi : M.F z i j (Set.Ioi 0) = 1 := by
    rw [← Set.compl_Iic, measure_compl measurableSet_Iic (measure_ne_top _ _), M.F_Iic_zero,
      measure_univ]
    simp
  have hint : IntegrableOn (fun t : ℝ => Real.exp (-(α * t))) (Set.Ioi 0) (M.F z i j) := by
    refine Measure.integrableOn_of_bounded (M := 1) (measure_ne_top _ _) ?_ ?_
    · exact (by fun_prop : Continuous fun t : ℝ => Real.exp (-(α * t))).aestronglyMeasurable
    · refine ae_restrict_of_forall_mem measurableSet_Ioi (fun t ht => ?_)
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      apply Real.exp_le_one_iff.2
      have : 0 < t := ht
      nlinarith
  have hint1 : IntegrableOn (fun _ : ℝ => (1:ℝ)) (Set.Ioi 0) (M.F z i j) :=
    integrableOn_const (measure_ne_top _ _)
  have hpos : 0 < ∫ t in Set.Ioi (0:ℝ), (1 - Real.exp (-(α * t))) ∂(M.F z i j) := by
    rw [setIntegral_pos_iff_support_of_nonneg_ae]
    · have hsub : Set.Ioi (0:ℝ) ⊆ Function.support (fun t : ℝ => 1 - Real.exp (-(α * t)))
          ∩ Set.Ioi 0 := by
        intro t ht
        refine ⟨?_, ht⟩
        simp only [Function.mem_support]
        have : 0 < t := ht
        have : Real.exp (-(α * t)) < 1 := Real.exp_lt_one_iff.2 (by nlinarith)
        linarith
      have := measure_mono (μ := M.F z i j) hsub
      rw [hIoi] at this
      exact lt_of_lt_of_le zero_lt_one this
    · refine ae_restrict_of_forall_mem measurableSet_Ioi (fun t ht => ?_)
      have : 0 < t := ht
      have : Real.exp (-(α * t)) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
      simp only [Pi.zero_apply]; linarith
    · exact hint1.sub hint
  rw [integral_sub hint1 hint, setIntegral_const] at hpos
  simp only [Measure.real, hIoi, ENNReal.toReal_one, smul_eq_mul, mul_one] at hpos
  unfold ftilde; linarith

lemma pi_beta [Fintype A] (M : MRP S A) {α : ℝ} (hα : 0 < α) :
    ∃ β : ℝ, 0 ≤ β ∧ β < 1 ∧ ∀ z i j, ftilde M z i j α ≤ β := by
  classical
  let T : Finset ℝ := insert 0 (Finset.univ.image fun x : A × S × S => ftilde M x.1 x.2.1 x.2.2 α)
  have hT : T.Nonempty := Finset.insert_nonempty _ _
  refine ⟨T.max' hT, Finset.le_max' _ _ (Finset.mem_insert_self _ _), ?_, ?_⟩
  · rw [Finset.max'_lt_iff]
    intro y hy
    rcases Finset.mem_insert.1 hy with h | h
    · rw [h]; exact zero_lt_one
    · obtain ⟨x, -, rfl⟩ := Finset.mem_image.1 h
      exact pi_ftilde_lt_one M _ _ _ hα
  · intro z i j
    exact Finset.le_max' T _ (by
      simp only [T, Finset.mem_insert, Finset.mem_image]
      exact Or.inr ⟨(z, i, j), Finset.mem_univ _, rfl⟩)

end

section
variable {S A : Type*} [Fintype S] [Fintype A] [Nonempty A] (M : MRP S A) {α β : ℝ}

lemma pi_q_nonneg (z : A) (i j : S) : 0 ≤ qtilde M α z i j :=
  mul_nonneg (M.p_nonneg z i j) (pi_ftilde_nonneg M z i j α)

lemma pi_q_le (hf : ∀ z i j, ftilde M z i j α ≤ β) (z : A) (i j : S) :
    qtilde M α z i j ≤ β * M.p z i j := by
  unfold qtilde
  rw [mul_comm β]
  exact mul_le_mul_of_nonneg_left (hf z i j) (M.p_nonneg z i j)

lemma pi_qsum_le (hf : ∀ z i j, ftilde M z i j α ≤ β) (z : A) (i : S) :
    ∑ j, qtilde M α z i j ≤ β := by
  calc ∑ j, qtilde M α z i j ≤ ∑ j, β * M.p z i j := Finset.sum_le_sum fun j _ => pi_q_le M hf z i j
    _ = β := by rw [← Finset.mul_sum, M.p_sum, mul_one]

lemma pi_test_sub (z : A) (i : S) (v w : S → ℝ) :
    test M α z i v - test M α z i w = ∑ j, qtilde M α z i j * (v j - w j) := by
  unfold test
  simp only [mul_sub, Finset.sum_sub_distrib]
  ring

lemma pi_test_dist (hf : ∀ z i j, ftilde M z i j α ≤ β) (z : A) (i : S) (v w : S → ℝ) :
    |test M α z i v - test M α z i w| ≤ β * dist v w := by
  rw [pi_test_sub]
  calc |∑ j, qtilde M α z i j * (v j - w j)| ≤ ∑ j, |qtilde M α z i j * (v j - w j)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j, β * M.p z i j * dist v w := by
        apply Finset.sum_le_sum; intro j _
        rw [abs_mul, abs_of_nonneg (pi_q_nonneg M z i j)]
        have h1 : |v j - w j| ≤ dist v w := by
          rw [← Real.dist_eq]; exact dist_le_pi_dist v w j
        calc qtilde M α z i j * |v j - w j| ≤ qtilde M α z i j * dist v w :=
              mul_le_mul_of_nonneg_left h1 (pi_q_nonneg M z i j)
          _ ≤ β * M.p z i j * dist v w :=
              mul_le_mul_of_nonneg_right (pi_q_le M hf z i j) dist_nonneg
    _ = β * dist v w := by
        rw [← Finset.sum_mul, ← Finset.mul_sum, M.p_sum, mul_one]

lemma pi_test_mono (z : A) (i : S) {v w : S → ℝ} (h : ∀ j, v j ≤ w j) :
    test M α z i v ≤ test M α z i w := by
  have := pi_test_sub M (α := α) z i w v
  have : 0 ≤ ∑ j, qtilde M α z i j * (w j - v j) :=
    Finset.sum_nonneg fun j _ => mul_nonneg (pi_q_nonneg M z i j) (by linarith [h j])
  linarith

lemma pi_test_le_max (z : A) (i : S) (v : S → ℝ) : test M α z i v ≤ maxTest M α v i :=
  Finset.le_sup' (fun z => test M α z i v) (Finset.mem_univ z)

lemma pi_max_le (hf : ∀ z i j, ftilde M z i j α ≤ β) (i : S) (v w : S → ℝ) :
    maxTest M α v i ≤ maxTest M α w i + β * dist v w := by
  unfold maxTest
  apply Finset.sup'_le
  intro z _
  have h1 := pi_test_dist M hf z i v w
  have h2 := pi_test_le_max M (α := α) z i w
  unfold maxTest at h2
  linarith [le_abs_self (test M α z i v - test M α z i w)]

lemma pi_max_dist (hf : ∀ z i j, ftilde M z i j α ≤ β) (i : S) (v w : S → ℝ) :
    |maxTest M α v i - maxTest M α w i| ≤ β * dist v w := by
  have h1 := pi_max_le M hf i v w
  have h2 := pi_max_le M hf i w v
  rw [dist_comm] at h2
  rw [abs_le]; constructor <;> linarith

lemma pi_ret_stat (hf : ∀ z i j, ftilde M z i j α ≤ β) (hβ0 : 0 ≤ β) (d : S → A) (v : S → ℝ)
    (hv : SolvesEval M α d v) (V0 : S → ℝ) (n : ℕ) :
    dist (policyReturn M α (fun _ => d) V0 n) v ≤ β ^ n * dist V0 v := by
  induction n with
  | zero => simp [policyReturn]
  | succ n ih =>
    rw [dist_pi_le_iff (by positivity)]
    intro i
    show dist (test M α (d i) i (policyReturn M α (fun _ => d) V0 n)) (v i) ≤ _
    rw [hv i, Real.dist_eq]
    calc _ ≤ β * dist (policyReturn M α (fun _ => d) V0 n) v := pi_test_dist M hf _ _ _ _
      _ ≤ β * (β ^ n * dist V0 v) := mul_le_mul_of_nonneg_left ih hβ0
      _ = _ := by ring

lemma pi_opt (hf : ∀ z i j, ftilde M z i j α ≤ β) (hβ0 : 0 ≤ β) (v : S → ℝ)
    (hv : ∀ i, v i = maxTest M α v i) (V0 : S → ℝ) (n : ℕ) :
    dist (optValue M α V0 n) v ≤ β ^ n * dist V0 v := by
  induction n with
  | zero => simp [optValue]
  | succ n ih =>
    rw [dist_pi_le_iff (by positivity)]
    intro i
    show dist (maxTest M α (optValue M α V0 n) i) (v i) ≤ _
    rw [hv i, Real.dist_eq]
    calc _ ≤ β * dist (optValue M α V0 n) v := pi_max_dist M hf _ _ _
      _ ≤ β * (β ^ n * dist V0 v) := mul_le_mul_of_nonneg_left ih hβ0
      _ = _ := by ring

lemma pi_ret_dist (hf : ∀ z i j, ftilde M z i j α ≤ β) (hβ0 : 0 ≤ β) (n : ℕ) :
    ∀ (π : ℕ → S → A) (V W : S → ℝ),
    dist (policyReturn M α π V n) (policyReturn M α π W n) ≤ β ^ n * dist V W := by
  induction n with
  | zero => intro π V W; simp [policyReturn]
  | succ n ih =>
    intro π V W
    rw [dist_pi_le_iff (by positivity)]
    intro i
    show dist (test M α (π 0 i) i (policyReturn M α (fun k => π (k + 1)) V n))
      (test M α (π 0 i) i (policyReturn M α (fun k => π (k + 1)) W n)) ≤ _
    rw [Real.dist_eq]
    calc _ ≤ β * dist (policyReturn M α (fun k => π (k + 1)) V n)
          (policyReturn M α (fun k => π (k + 1)) W n) := pi_test_dist M hf _ _ _ _
      _ ≤ β * (β ^ n * dist V W) := mul_le_mul_of_nonneg_left (ih _ V W) hβ0
      _ = _ := by ring

lemma pi_ret_succ (n : ℕ) : ∀ (π : ℕ → S → A) (V : S → ℝ),
    policyReturn M α π V (n + 1) = policyReturn M α π (fun i => test M α (π n i) i V) n := by
  induction n with
  | zero => intro π V; rfl
  | succ n ih =>
    intro π V
    show (fun i => test M α (π 0 i) i (policyReturn M α (fun k => π (k + 1)) V (n + 1))) =
      (fun i => test M α (π 0 i) i (policyReturn M α (fun k => π (k + 1))
        (fun i => test M α (π (n + 1) i) i V) n))
    rw [ih]

lemma pi_ret_le_opt (n : ℕ) : ∀ (π : ℕ → S → A) (V0 : S → ℝ) (i : S),
    policyReturn M α π V0 n i ≤ optValue M α V0 n i := by
  induction n with
  | zero => intro π V0 i; exact le_rfl
  | succ n ih =>
    intro π V0 i
    show test M α (π 0 i) i (policyReturn M α (fun k => π (k + 1)) V0 n) ≤
      maxTest M α (optValue M α V0 n) i
    exact (pi_test_mono M _ _ (fun j => ih _ V0 j)).trans (pi_test_le_max M _ _ _)

lemma pi_ret_conv (hf : ∀ z i j, ftilde M z i j α ≤ β) (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (π : ℕ → S → A) (V0 : S → ℝ) :
    ∃ X : S → ℝ, Tendsto (fun n => policyReturn M α π V0 n) atTop (𝓝 X) := by
  obtain ⟨C, hC⟩ : ∃ C : ℝ, ∀ σ : S → A, dist V0 (fun i => test M α (σ i) i V0) ≤ C := by
    refine ⟨∑ i, ∑ z : A, |V0 i - test M α z i V0|, fun σ => ?_⟩
    rw [dist_pi_le_iff (by positivity)]
    intro i
    rw [Real.dist_eq]
    calc |V0 i - test M α (σ i) i V0| ≤ ∑ z : A, |V0 i - test M α z i V0| :=
          Finset.single_le_sum (f := fun z : A => |V0 i - test M α z i V0|)
            (fun z _ => abs_nonneg _) (Finset.mem_univ (σ i))
      _ ≤ ∑ i, ∑ z : A, |V0 i - test M α z i V0| :=
          Finset.single_le_sum (f := fun i => ∑ z : A, |V0 i - test M α z i V0|)
            (fun _ _ => by positivity) (Finset.mem_univ i)
  have hu : ∀ n, dist (policyReturn M α π V0 n) (policyReturn M α π V0 (n + 1)) ≤ C * β ^ n := by
    intro n
    rw [pi_ret_succ]
    refine (pi_ret_dist M hf hβ0 n π _ _).trans ?_
    rw [mul_comm C]
    exact mul_le_mul_of_nonneg_left (hC (π n)) (pow_nonneg hβ0 n)
  exact cauchySeq_tendsto_of_complete (cauchySeq_of_le_geometric β C hβ1 hu)

lemma pi_eval_unique (hf : ∀ z i j, ftilde M z i j α ≤ β) (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (d : S → A) (v w : S → ℝ) (hv : SolvesEval M α d v) (hw : SolvesEval M α d w) : v = w := by
  have h : dist v w ≤ β * dist v w := by
    rw [dist_pi_le_iff (by positivity)]
    intro i
    rw [Real.dist_eq, hv i, hw i]
    exact pi_test_dist M hf _ _ _ _
  have : dist v w ≤ 0 := by nlinarith [dist_nonneg (x := v) (y := w)]
  exact dist_le_zero.1 this

lemma pi_eval_exists (hf : ∀ z i j, ftilde M z i j α ≤ β) (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (d : S → A) : ∃ v, SolvesEval M α d v := by
  let f : (S → ℝ) → (S → ℝ) := fun v i => test M α (d i) i v
  have hc : ContractingWith (Real.toNNReal β) f := by
    refine ⟨?_, LipschitzWith.of_dist_le_mul fun v w => ?_⟩
    · rw [← NNReal.coe_lt_coe]; simp [hβ0, hβ1]
    · rw [Real.coe_toNNReal _ hβ0, dist_pi_le_iff (by positivity)]
      intro i
      rw [Real.dist_eq]
      exact pi_test_dist M hf _ _ _ _
  refine ⟨ContractingWith.fixedPoint f hc, fun i => ?_⟩
  have := ContractingWith.fixedPoint_isFixedPt (f := f) hc
  exact (congrFun this i).symm

/-- monotonicity of evaluation under improvement -/
lemma pi_eval_mono (hf : ∀ z i j, ftilde M z i j α ≤ β) (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (d d' : S → A) (v v' : S → ℝ) (hv : SolvesEval M α d v) (hv' : SolvesEval M α d' v')
    (himp : ∀ i, test M α (d i) i v ≤ test M α (d' i) i v) : ∀ i, v i ≤ v' i := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨i1, hi1⟩ := hcon
  obtain ⟨i0, -, hmin⟩ := Finset.exists_min_image Finset.univ (fun j => v' j - v j)
    ⟨i1, Finset.mem_univ _⟩
  have hneg : v' i0 - v i0 < 0 := by
    have := hmin i1 (Finset.mem_univ _); linarith
  have e1 : v' i0 - v i0 ≥ test M α (d' i0) i0 v' - test M α (d' i0) i0 v := by
    rw [hv' i0]; conv_lhs => rw [hv i0]
    linarith [himp i0]
  rw [pi_test_sub] at e1
  have e2 : ∑ j, qtilde M α (d' i0) i0 j * (v' j - v j) ≥
      ∑ j, qtilde M α (d' i0) i0 j * (v' i0 - v i0) :=
    Finset.sum_le_sum fun j _ =>
      mul_le_mul_of_nonneg_left (hmin j (Finset.mem_univ _)) (pi_q_nonneg M _ _ _)
  rw [← Finset.sum_mul] at e2
  have e3 := pi_qsum_le M hf (d' i0) i0
  have e4 : (∑ j, qtilde M α (d' i0) i0 j) * (v' i0 - v i0) ≥ β * (v' i0 - v i0) :=
    mul_le_mul_of_nonpos_right e3 hneg.le
  nlinarith

theorem pi_core (hα : 0 < α) [DecidableEq S] :
    (∀ d : S → A, ∃! v : S → ℝ, SolvesEval M α d v) ∧
    ∀ (d : ℕ → S → A) (v : ℕ → S → ℝ), IsFig1Run M α d v →
      ∃ K, K < Fintype.card (S → A) ∧ d (K + 1) = d K ∧
        (∀ V0 : S → ℝ,
          Tendsto (fun n => policyReturn M α (fun _ => d K) V0 n) atTop (𝓝 (v K))) ∧
        (∀ (π : ℕ → S → A) (V0 : S → ℝ) (i : S), ∃ x : ℝ,
          Tendsto (fun n => policyReturn M α π V0 n i) atTop (𝓝 x) ∧ x ≤ v K i) ∧
        (∀ V0 : S → ℝ, Tendsto (optValue M α V0) atTop (𝓝 (v K))) := by
  obtain ⟨β, hβ0, hβ1, hf⟩ := pi_beta M hα
  refine ⟨fun d => ?_, fun d v hrun => ?_⟩
  · obtain ⟨v, hv⟩ := pi_eval_exists M hf hβ0 hβ1 d
    exact ⟨v, hv, fun w hw => pi_eval_unique M hf hβ0 hβ1 d w v hw hv⟩
  have hmono1 : ∀ k i, v k i ≤ v (k + 1) i := by
    intro k
    apply pi_eval_mono M hf hβ0 hβ1 (d k) (d (k + 1)) (v k) (v (k + 1)) (hrun k).1 (hrun (k+1)).1
    intro i
    rw [((hrun k).2 i).1]
    exact pi_test_le_max M _ _ _
  have hmono : ∀ k m, k ≤ m → ∀ i, v k i ≤ v m i := by
    intro k m hkm
    induction hkm with
    | refl => intro i; exact le_rfl
    | step _ ih => intro i; exact (ih i).trans (hmono1 _ i)
  have hstrict : ∀ k, d (k + 1) ≠ d k → v k ≠ v (k + 1) := by
    intro k hne heq
    obtain ⟨i, hi⟩ := Function.ne_iff.1 hne
    have hlt : test M α (d k i) i (v k) < maxTest M α (v k) i := by
      rcases (pi_test_le_max M (α := α) (d k i) i (v k)).lt_or_eq with h | h
      · exact h
      · exact absurd (((hrun k).2 i).2 h) hi
    have h1 := (hrun k).1 i
    have h2 := (hrun (k + 1)).1 i
    rw [← heq, ((hrun k).2 i).1] at h2
    linarith
  have hK : ∃ K, K < Fintype.card (S → A) ∧ d (K + 1) = d K := by
    by_contra hcon
    push_neg at hcon
    set N := Fintype.card (S → A)
    have hinj : Function.Injective (fun k : Fin (N + 1) => d k) := by
      intro a b hab
      simp only at hab
      by_contra hne
      have key : ∀ k m : ℕ, k < m → m ≤ N → d k = d m → False := by
        intro k m hkm hmN hd
        have hvkm : v k = v m := pi_eval_unique M hf hβ0 hβ1 (d k) _ _ (hrun k).1
          (hd ▸ (hrun m).1)
        apply hstrict k (hcon k (by omega))
        funext i
        apply le_antisymm (hmono1 k i)
        rw [hvkm]; exact hmono (k + 1) m hkm i
      rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with h | h
      · exact key a b h (by omega) hab
      · exact key b a h (by omega) hab.symm
    have := Fintype.card_le_of_injective _ hinj
    rw [Fintype.card_fin] at this
    omega
  obtain ⟨K, hKlt, hKeq⟩ := hK
  have hfix : ∀ i, v K i = maxTest M α (v K) i := by
    intro i
    calc v K i = test M α (d K i) i (v K) := (hrun K).1 i
      _ = test M α (d (K + 1) i) i (v K) := by rw [hKeq]
      _ = maxTest M α (v K) i := ((hrun K).2 i).1
  have hoptlim : ∀ V0 : S → ℝ, Tendsto (optValue M α V0) atTop (𝓝 (v K)) := by
    intro V0
    rw [tendsto_iff_dist_tendsto_zero]
    have h0 : Tendsto (fun n => β ^ n * dist V0 (v K)) atTop (𝓝 0) := by
      simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hβ0 hβ1).mul_const (dist V0 (v K))
    exact squeeze_zero (fun _ => dist_nonneg) (fun n => pi_opt M hf hβ0 (v K) hfix V0 n) h0
  refine ⟨K, hKlt, hKeq, fun V0 => ?_, fun π V0 i => ?_, hoptlim⟩
  · rw [tendsto_iff_dist_tendsto_zero]
    have h0 : Tendsto (fun n => β ^ n * dist V0 (v K)) atTop (𝓝 0) := by
      simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hβ0 hβ1).mul_const (dist V0 (v K))
    exact squeeze_zero (fun _ => dist_nonneg)
      (fun n => pi_ret_stat M hf hβ0 (d K) (v K) (hrun K).1 V0 n) h0
  · obtain ⟨X, hX⟩ := pi_ret_conv M hf hβ0 hβ1 π V0
    have hXi : Tendsto (fun n => policyReturn M α π V0 n i) atTop (𝓝 (X i)) :=
      ((continuous_apply i).tendsto X).comp hX
    refine ⟨X i, hXi, ?_⟩
    have hopt_i : Tendsto (fun n => optValue M α V0 n i) atTop (𝓝 (v K i)) :=
      ((continuous_apply i).tendsto _).comp (hoptlim V0)
    exact le_of_tendsto_of_tendsto' hXi hopt_i (fun n => pi_ret_le_opt M n π V0 i)

end

end JewellMRP.Discounted

open JewellMRP.Discounted


theorem solution {S A : Type*} [Fintype S] [DecidableEq S]
    [Fintype A] [Nonempty A] (M : MRP S A) {α : ℝ} (hα : 0 < α) :
    (∀ d : S → A, ∃! v : S → ℝ, SolvesEval M α d v) ∧
    ∀ (d : ℕ → S → A) (v : ℕ → S → ℝ), IsFig1Run M α d v →
      ∃ K, K < Fintype.card (S → A) ∧ d (K + 1) = d K ∧
        (∀ V0 : S → ℝ,
          Tendsto (fun n => policyReturn M α (fun _ => d K) V0 n) atTop (𝓝 (v K))) ∧
        (∀ (π : ℕ → S → A) (V0 : S → ℝ) (i : S), ∃ x : ℝ,
          Tendsto (fun n => policyReturn M α π V0 n i) atTop (𝓝 x) ∧ x ≤ v K i) ∧
        (∀ V0 : S → ℝ, Tendsto (optValue M α V0) atTop (𝓝 (v K))) := by
  exact pi_core M hα
