-- Prove2me | solution 1 for KallenbergLP.Transient.totalOptimalPureStationary
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T14:25:31.353801+00:00
-- url     : https://prove2.me/submissions/aa41b6da-2cc4-4000-ada1-3668a5fbbd09

import Mathlib
import Definitions.Def_KallenbergLP_Transient_Criteria
import Definitions.Def_KallenbergLP_Transient_TotalReward
set_option autoImplicit false


namespace KallenbergLP.Transient

set_option linter.unusedSectionVars false
variable {N : ℕ} {α : Type} [Fintype α] [DecidableEq α]

def kt_hext {n : ℕ} (h : History N α n) (a : α) (j : Fin N) : History N α (n+1) :=
  ⟨Fin.snoc (α := fun _ => Fin N) h.states j, Fin.snoc (α := fun _ => α) h.chosen a⟩

def kt_histEquiv (n : ℕ) : History N α n × α × Fin N ≃ History N α (n+1) where
  toFun p := kt_hext p.1 p.2.1 p.2.2
  invFun H := (⟨Fin.init H.states, Fin.init H.chosen⟩, H.chosen (Fin.last n),
    H.states (Fin.last (n+1)))
  left_inv := by rintro ⟨⟨s, c⟩, a, j⟩; simp [kt_hext]
  right_inv := by rintro ⟨s, c⟩; simp [kt_hext]

lemma kt_hext_last {n : ℕ} (h : History N α n) (a : α) (j : Fin N) :
    (kt_hext h a j).last = j := by
  simp [History.last, kt_hext, Fin.snoc]

lemma kt_hext_prefix_cast {n : ℕ} (h : History N α n) (a : α) (j : Fin N) (k : Fin n) :
    (kt_hext h a j).prefix (Fin.castSucc k) = h.prefix k := by
  simp only [History.prefix, kt_hext]
  congr 1
  · funext i
    have : i.val < n + 1 := by omega
    simp [Fin.snoc, this]
  · funext i
    have : i.val < n := by omega
    simp [Fin.snoc, this]

lemma kt_hext_prefix_last {n : ℕ} (h : History N α n) (a : α) (j : Fin N) :
    (kt_hext h a j).prefix (Fin.last n) = h := by
  rcases h with ⟨s, c⟩
  simp only [History.prefix, kt_hext]
  congr 1
  · funext i
    have : i.val < n + 1 := by omega
    simp [Fin.snoc, this]
  · funext i
    have : i.val < n := by omega
    simp [Fin.snoc, this]

lemma kt_historyProb_hext (M : MDP N α) (R : Policy M) (i : Fin N) {n : ℕ}
    (h : History N α n) (a : α) (j : Fin N) :
    historyProb M R i (n+1) (kt_hext h a j) =
      historyProb M R i n h * (R.choose n h a * M.transition h.last a j) := by
  unfold historyProb
  rw [Fin.prod_univ_castSucc, ← mul_assoc]
  have h0 : (kt_hext h a j).states ⟨0, by omega⟩ = h.states ⟨0, by omega⟩ := by
    simp [kt_hext, Fin.snoc]
  have hP : ∀ k : Fin n, R.choose (Fin.castSucc k).val ((kt_hext h a j).prefix (Fin.castSucc k))
      ((kt_hext h a j).chosen (Fin.castSucc k)) *
      M.transition ((kt_hext h a j).states ⟨(Fin.castSucc k).val, by omega⟩)
        ((kt_hext h a j).chosen (Fin.castSucc k))
        ((kt_hext h a j).states ⟨(Fin.castSucc k).val + 1, by omega⟩) =
      R.choose k.val (h.prefix k) (h.chosen k) *
        M.transition (h.states ⟨k.val, by omega⟩) (h.chosen k) (h.states ⟨k.val + 1, by omega⟩) := by
    intro k
    rw [kt_hext_prefix_cast]
    have hk1 : k.val < n + 1 := by omega
    have hk2 : k.val + 1 < n + 1 := by omega
    simp [kt_hext, Fin.snoc, hk1, hk2, k.isLt]
  have hL : R.choose (Fin.last n).val ((kt_hext h a j).prefix (Fin.last n))
      ((kt_hext h a j).chosen (Fin.last n)) *
      M.transition ((kt_hext h a j).states ⟨(Fin.last n).val, by omega⟩)
        ((kt_hext h a j).chosen (Fin.last n))
        ((kt_hext h a j).states ⟨(Fin.last n).val + 1, by omega⟩) =
      R.choose n h a * M.transition h.last a j := by
    rw [kt_hext_prefix_last]
    simp [kt_hext, Fin.snoc, History.last]
  rw [h0, Finset.prod_congr rfl (fun k _ => hP k), hL]

lemma kt_historyProb_nonneg (M : MDP N α) (R : Policy M) (i : Fin N) (n : ℕ)
    (h : History N α n) : 0 ≤ historyProb M R i n h := by
  unfold historyProb
  apply mul_nonneg
  · split_ifs <;> norm_num
  · apply Finset.prod_nonneg
    intro k _
    by_cases ha : h.chosen k ∈ M.actions (h.prefix k).last
    · exact mul_nonneg (R.choose_nonneg _ _ _) (M.transition_nonneg _ _ _ ha)
    · rw [R.choose_outside _ _ _ ha, zero_mul]

lemma kt_occ_nonneg (M : MDP N α) (R : Policy M) (i j : Fin N) (a : α) (n : ℕ) :
    0 ≤ occupancy M R i j a n := by
  unfold occupancy
  apply Finset.sum_nonneg
  intro h _
  split_ifs
  · exact mul_nonneg (kt_historyProb_nonneg M R i n h) (R.choose_nonneg _ _ _)
  · exact le_refl _

lemma kt_st_nonneg (M : MDP N α) (R : Policy M) (i j : Fin N) (n : ℕ) :
    0 ≤ stateProb M R i j n := by
  unfold stateProb
  apply Finset.sum_nonneg
  intro h _
  split_ifs
  · exact kt_historyProb_nonneg M R i n h
  · exact le_refl _

lemma kt_occ_outside (M : MDP N α) (R : Policy M) (i j : Fin N) (a : α) (n : ℕ)
    (ha : a ∉ M.actions j) : occupancy M R i j a n = 0 := by
  unfold occupancy
  apply Finset.sum_eq_zero
  intro h _
  split_ifs with hj
  · rw [R.choose_outside _ _ _ (by rw [hj]; exact ha), mul_zero]
  · rfl

lemma kt_occ_sum (M : MDP N α) (R : Policy M) (i j : Fin N) (n : ℕ) :
    ∑ a, occupancy M R i j a n = stateProb M R i j n := by
  unfold occupancy stateProb
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro h _
  split_ifs
  · rw [← Finset.mul_sum, R.choose_sum_one, mul_one]
  · simp

lemma kt_st_succ (M : MDP N α) (R : Policy M) (i j' : Fin N) (n : ℕ) :
    stateProb M R i j' (n+1) =
      ∑ j, ∑ a, occupancy M R i j a n * M.transition j a j' := by
  unfold stateProb
  rw [← (kt_histEquiv n).sum_comp]
  rw [Fintype.sum_prod_type]
  simp only [kt_histEquiv, Equiv.coe_fn_mk, kt_hext_last, kt_historyProb_hext]
  simp only [Fintype.sum_prod_type, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  unfold occupancy
  have key : ∀ x : History N α n, ∑ j, ∑ a, (if x.last = j then
      historyProb M R i n x * R.choose n x a * M.transition j a j' else 0) =
      ∑ a, historyProb M R i n x * (R.choose n x a * M.transition x.last a j') := by
    intro x
    rw [Finset.sum_eq_single x.last]
    · simp only [if_true]; apply Finset.sum_congr rfl; intro a _; ring
    · intro b _ hb; apply Finset.sum_eq_zero; intro a _; rw [if_neg (Ne.symm hb)]
    · simp

  rw [← Finset.sum_congr rfl (fun x _ => key x)]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro j _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro a _
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl; intro x _
  split_ifs <;> simp

lemma kt_st_zero (M : MDP N α) (R : Policy M) (i j : Fin N) :
    stateProb M R i j 0 = if j = i then 1 else 0 := by
  unfold stateProb historyProb
  let e : History N α 0 ≃ Fin N :=
    { toFun := fun h => h.states 0
      invFun := fun k => ⟨fun _ => k, Fin.elim0⟩
      left_inv := by
        rintro ⟨s, c⟩
        dsimp only
        congr 1
        · funext x; fin_cases x; rfl
        · funext x; exact Fin.elim0 x
      right_inv := by intro k; rfl }
  rw [← e.symm.sum_comp]
  simp [e, History.last]

/-- push-forward identity -/
lemma kt_push (M : MDP N α) (R : Policy M) (i : Fin N) (n : ℕ) (g : Fin N → ℝ) :
    ∑ j', stateProb M R i j' (n+1) * g j' =
      ∑ j, ∑ a, occupancy M R i j a n * ∑ j', M.transition j a j' * g j' := by
  simp only [kt_st_succ, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro j _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro a _
  apply Finset.sum_congr rfl; intro j' _
  ring

/-- drift inequality -/
lemma kt_drift (M : MDP N α) (R : Policy M) (i : Fin N) (n : ℕ) (g hh : Fin N → ℝ)
    (hg : ∀ j a, a ∈ M.actions j → ∑ j', M.transition j a j' * g j' ≤ hh j) :
    ∑ j', stateProb M R i j' (n+1) * g j' ≤ ∑ j, stateProb M R i j n * hh j := by
  rw [kt_push]
  apply Finset.sum_le_sum; intro j _
  rw [← kt_occ_sum, Finset.sum_mul]
  apply Finset.sum_le_sum; intro a _
  by_cases ha : a ∈ M.actions j
  · exact mul_le_mul_of_nonneg_left (hg j a ha) (kt_occ_nonneg _ _ _ _ _ _)
  · simp [kt_occ_outside M R i j a n ha]

lemma kt_mass_le (M : MDP N α) (R : Policy M) (i : Fin N) (n : ℕ) :
    ∑ j, stateProb M R i j n ≤ 1 := by
  induction n with
  | zero => simp [kt_st_zero]
  | succ n ih =>
    have := kt_drift M R i n (fun _ => 1) (fun _ => 1) (by
      intro j a ha; simpa using M.transition_subprob j a ha)
    simp only [mul_one] at this
    linarith

lemma kt_st_le_one (M : MDP N α) (R : Policy M) (i j : Fin N) (n : ℕ) :
    stateProb M R i j n ≤ 1 :=
  le_trans (Finset.single_le_sum (f := fun j => stateProb M R i j n)
    (fun k _ => kt_st_nonneg M R i k n) (Finset.mem_univ j)) (kt_mass_le M R i n)

lemma kt_occ_le_st (M : MDP N α) (R : Policy M) (i j : Fin N) (a : α) (n : ℕ) :
    occupancy M R i j a n ≤ stateProb M R i j n := by
  rw [← kt_occ_sum]
  exact Finset.single_le_sum (f := fun a => occupancy M R i j a n)
    (fun b _ => kt_occ_nonneg M R i j b n) (Finset.mem_univ a)

lemma kt_occ_memoryless (M : MDP N α) (R : Policy M) (q : ℕ → Fin N → α → ℝ)
    (hq : ∀ n (h : History N α n) a, R.choose n h a = q n h.last a)
    (i j : Fin N) (a : α) (n : ℕ) :
    occupancy M R i j a n = stateProb M R i j n * q n j a := by
  unfold occupancy stateProb
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro h _
  split_ifs with hj
  · rw [hq, hj]
  · simp

lemma kt_occ_pure (M : MDP N α) (f : PureRule M) (i j : Fin N) (a : α) (n : ℕ) :
    occupancy M (purePolicy M f) i j a n =
      if a = f.choose j then stateProb M (purePolicy M f) i j n else 0 := by
  rw [kt_occ_memoryless M (purePolicy M f) (fun _ j a => if a = f.choose j then 1 else 0)
    (fun _ _ _ => rfl)]
  split_ifs <;> simp


lemma kt_abel_identity (a : ℕ → ℝ) (C : ℝ) (ha : ∀ t, |a t| ≤ C) (δ : ℝ) (h0 : 0 ≤ δ) (h1 : δ < 1) :
    Summable (fun n => δ ^ n * ∑ t ∈ Finset.range (n+1), a t) ∧
    ∑' t, δ ^ t * a t = (1 - δ) * ∑' n, δ ^ n * ∑ t ∈ Finset.range (n+1), a t := by
  have hg : Summable (fun k => ‖δ ^ k‖) := by
    simpa [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg h0 _)] using
      summable_geometric_of_lt_one h0 h1
  have hf : Summable (fun k => ‖δ ^ k * a k‖) := by
    refine Summable.of_nonneg_of_le (fun k => norm_nonneg _) (fun k => ?_)
      ((summable_geometric_of_lt_one h0 h1).mul_left C)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg h0 _), mul_comm]
    exact mul_le_mul_of_nonneg_right (ha k) (pow_nonneg h0 _)
  have hF : ∀ n, ∑ k ∈ Finset.range (n+1), δ ^ k * (δ ^ (n - k) * a (n - k)) =
      δ ^ n * ∑ t ∈ Finset.range (n+1), a t := by
    intro n
    rw [Finset.mul_sum, ← Finset.sum_range_reflect (fun t => δ ^ n * a t)]
    apply Finset.sum_congr rfl; intro k hk
    have hk' : k ≤ n := by simp at hk; omega
    rw [← mul_assoc, ← pow_add, Nat.add_sub_cancel' hk']
    congr 2
  have hcp := tsum_mul_tsum_eq_tsum_sum_range_of_summable_norm hg hf
  have hs := summable_norm_sum_mul_range_of_summable_norm hg hf
  simp only [hF] at hcp hs
  refine ⟨hs.of_norm, ?_⟩
  rw [← hcp, tsum_geometric_of_lt_one h0 h1, ← mul_assoc, mul_inv_cancel₀ (by linarith), one_mul]

lemma kt_abel_top (a : ℕ → ℝ) (C : ℝ) (ha : ∀ t, |a t| ≤ C)
    (h : ∀ K : ℝ, ∀ᶠ n in Filter.atTop, K ≤ ∑ t ∈ Finset.range n, a t) :
    ∀ K : ℝ, ∀ᶠ δ in nhdsWithin 1 (Set.Iio 1), K < ∑' t, δ ^ t * a t := by
  intro K
  have hC : 0 ≤ C := le_trans (abs_nonneg _) (ha 0)
  obtain ⟨T0, hT0⟩ := Filter.eventually_atTop.1 (h (K + 2))
  set B := C * T0
  let g : ℝ → ℝ := fun δ => -(1 - δ) * T0 * B + (K + 2) * δ ^ T0
  have hgc : Continuous g := by fun_prop
  have hg1 : K + 1 < g 1 := by simp [g]
  have ev1 : ∀ᶠ δ in nhds (1:ℝ), K + 1 < g δ :=
    (hgc.tendsto 1).eventually (lt_mem_nhds hg1)
  have ev2 : ∀ᶠ δ in nhdsWithin (1:ℝ) (Set.Iio 1), δ ∈ Set.Ioo (0:ℝ) 1 :=
    Ioo_mem_nhdsLT (by norm_num)
  filter_upwards [nhdsWithin_le_nhds ev1, ev2] with δ hδ1 hδ2
  obtain ⟨h0, h1⟩ := hδ2
  obtain ⟨hsum, hid⟩ := kt_abel_identity a C ha δ h0.le h1
  rw [hid]
  have hS : ∀ m, |∑ t ∈ Finset.range m, a t| ≤ C * m := by
    intro m
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    refine le_trans (Finset.sum_le_sum fun t _ => ha t) ?_
    simp [mul_comm]
  have hsplit := (hsum.sum_add_tsum_nat_add T0).symm
  have hhead : -(T0 * B) ≤ ∑ n ∈ Finset.range T0, δ ^ n * ∑ t ∈ Finset.range (n+1), a t := by
    have : ∑ n ∈ Finset.range T0, (-B) ≤
        ∑ n ∈ Finset.range T0, δ ^ n * ∑ t ∈ Finset.range (n+1), a t := by
      apply Finset.sum_le_sum; intro n hn
      have hn' : n + 1 ≤ T0 := by simp at hn; omega
      have e1 := hS (n+1)
      have e2 : C * ((n+1 : ℕ) : ℝ) ≤ B := mul_le_mul_of_nonneg_left (by exact_mod_cast hn') hC
      have e3 : δ ^ n ≤ 1 := pow_le_one₀ h0.le h1.le
      have e4 : 0 ≤ δ ^ n := pow_nonneg h0.le n
      have e5 := neg_abs_le (∑ t ∈ Finset.range (n+1), a t)
      have e6 : -B ≤ ∑ t ∈ Finset.range (n+1), a t := by linarith
      have e7 : 0 ≤ B := mul_nonneg hC (by positivity)
      nlinarith
    simpa using this
  have htail : (K + 2) * δ ^ T0 * (1 - δ)⁻¹ ≤
      ∑' n, δ ^ (n + T0) * ∑ t ∈ Finset.range (n + T0 + 1), a t := by
    have hgeo : Summable (fun n => δ ^ (n + T0) * (K + 2)) := by
      have := (summable_geometric_of_lt_one h0.le h1).mul_left (δ ^ T0 * (K + 2))
      refine this.congr fun n => ?_
      rw [pow_add]; ring
    have e : ∑' n, δ ^ (n + T0) * (K + 2) = (K + 2) * δ ^ T0 * (1 - δ)⁻¹ := by
      have : ∀ n, δ ^ (n + T0) * (K + 2) = ((K + 2) * δ ^ T0) * δ ^ n := by
        intro n; rw [pow_add]; ring
      simp only [this]
      rw [tsum_mul_left, tsum_geometric_of_lt_one h0.le h1]
    rw [← e]
    have htl : Summable (fun n => δ ^ (n + T0) * ∑ t ∈ Finset.range (n + T0 + 1), a t) :=
      (summable_nat_add_iff (f := fun n => δ ^ n * ∑ t ∈ Finset.range (n+1), a t) T0).2 hsum
    refine Summable.tsum_le_tsum (fun n => ?_) hgeo htl
    apply mul_le_mul_of_nonneg_left _ (pow_nonneg h0.le _)
    exact hT0 (n + T0 + 1) (by omega)
  rw [hsplit]
  have hpos : 0 < 1 - δ := by linarith
  have : g δ ≤ (1 - δ) * (∑ n ∈ Finset.range T0, δ ^ n * ∑ t ∈ Finset.range (n+1), a t +
      ∑' n, δ ^ (n + T0) * ∑ t ∈ Finset.range (n + T0 + 1), a t) := by
    have e : (1 - δ) * ((K + 2) * δ ^ T0 * (1 - δ)⁻¹) = (K + 2) * δ ^ T0 := by
      field_simp
    have := mul_le_mul_of_nonneg_left htail hpos.le
    have := mul_le_mul_of_nonneg_left hhead hpos.le
    simp only [g]
    nlinarith
  linarith

lemma kt_period_bound (M : MDP N α) (r : Fin N → α → ℝ) (R : Policy M) (i : Fin N) (t : ℕ) :
    |periodReward M r R i t| ≤ ∑ j, ∑ a ∈ M.actions j, |r j a| := by
  unfold periodReward
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum fun j _ => ?_)
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum fun a _ => ?_)
  rw [abs_mul, abs_of_nonneg (kt_occ_nonneg _ _ _ _ _ _)]
  exact mul_le_of_le_one_left (abs_nonneg _)
    (le_trans (kt_occ_le_st _ _ _ _ _ _) (kt_st_le_one _ _ _ _ _))

theorem kt_disc_core (M : MDP N α) (r : Fin N → α → ℝ)
    (hreward : TotalRewardExists M r) (i : Fin N) (R : Policy M) :
    Filter.Tendsto (fun δ : ℝ => (discountedValue M r R i δ : EReal))
      (nhdsWithin 1 (Set.Iio 1)) (nhds (policyValue M r R i)) := by
  obtain ⟨v, hv⟩ := hreward R i
  have hpv : policyValue M r R i = v := hv.limsup_eq
  rw [hpv]
  set a : ℕ → ℝ := fun t => periodReward M r R i t with ha_def
  set C := ∑ j, ∑ a ∈ M.actions j, |r j a|
  have ha : ∀ t, |a t| ≤ C := fun t => kt_period_bound M r R i t
  have hcum : ∀ T, cumulativeReward M r R i T = ∑ t ∈ Finset.range T, a t := fun T => rfl
  have hdisc : ∀ δ, discountedValue M r R i δ = ∑' t, δ ^ t * a t := fun δ => rfl
  simp only [hcum] at hv
  simp only [hdisc]
  induction v using EReal.rec with
  | bot =>
    rw [EReal.tendsto_nhds_bot_iff_real] at hv ⊢
    have hneg : ∀ K : ℝ, ∀ᶠ n in Filter.atTop, K ≤ ∑ t ∈ Finset.range n, (-a t) := by
      intro K
      filter_upwards [hv (-K)] with n hn
      rw [Finset.sum_neg_distrib]
      have : ∑ t ∈ Finset.range n, a t < -K := by exact_mod_cast hn
      linarith
    intro K
    filter_upwards [kt_abel_top (fun t => -a t) C (fun t => by rw [abs_neg]; exact ha t) hneg (-K)]
      with δ hδ
    have : ∑' t, δ ^ t * a t < K := by
      have e : ∑' t, δ ^ t * (-a t) = -∑' t, δ ^ t * a t := by
        rw [← tsum_neg]; apply tsum_congr; intro t; ring
      rw [e] at hδ; linarith
    exact_mod_cast this
  | top =>
    rw [EReal.tendsto_nhds_top_iff_real] at hv ⊢
    have hpos : ∀ K : ℝ, ∀ᶠ n in Filter.atTop, K ≤ ∑ t ∈ Finset.range n, a t := by
      intro K
      filter_upwards [hv K] with n hn
      have : K < ∑ t ∈ Finset.range n, a t := by exact_mod_cast hn
      exact this.le
    intro K
    filter_upwards [kt_abel_top a C ha hpos K] with δ hδ
    exact_mod_cast hδ
  | coe l =>
    have hl : Filter.Tendsto (fun T => ∑ t ∈ Finset.range T, a t) Filter.atTop (nhds l) :=
      EReal.tendsto_coe.1 hv
    have := Real.tendsto_tsum_powerSeries_nhdsWithin_lt hl
    have h2 : Filter.Tendsto (fun δ : ℝ => ∑' t, δ ^ t * a t) (nhdsWithin 1 (Set.Iio 1)) (nhds l) := by
      refine this.congr fun δ => ?_
      apply tsum_congr; intro t; ring
    exact (continuous_coe_real_ereal.tendsto l).comp h2

lemma kt_disc_summable (M : MDP N α) (r : Fin N → α → ℝ) (R : Policy M) (i : Fin N) (δ : ℝ)
    (h0 : 0 ≤ δ) (h1 : δ < 1) : Summable (fun t => δ ^ t * periodReward M r R i t) := by
  refine Summable.of_nonneg_of_le (fun t => abs_nonneg _) (fun t => ?_)
    ((summable_geometric_of_lt_one h0 h1).mul_left (∑ j, ∑ a ∈ M.actions j, |r j a|)) |>.of_abs
  rw [abs_mul, abs_of_nonneg (pow_nonneg h0 _), mul_comm]
  exact mul_le_mul_of_nonneg_right (kt_period_bound M r R i t) (pow_nonneg h0 _)

lemma kt_pr_univ (M : MDP N α) (r : Fin N → α → ℝ) (R : Policy M) (i : Fin N) (n : ℕ) :
    periodReward M r R i n = ∑ j, ∑ a, occupancy M R i j a n * r j a := by
  unfold periodReward
  apply Finset.sum_congr rfl; intro j _
  apply Finset.sum_subset (Finset.subset_univ _)
  intro a _ ha; simp [kt_occ_outside _ _ _ _ _ _ ha]

lemma kt_disc_step (M : MDP N α) (r : Fin N → α → ℝ) (δ : ℝ) (v : Fin N → ℝ)
    (hv : ∀ j a, a ∈ M.actions j → r j a + δ * ∑ k, M.transition j a k * v k ≤ v j)
    (R : Policy M) (i : Fin N) (n : ℕ) :
    periodReward M r R i n + δ * ∑ j, stateProb M R i j (n+1) * v j ≤
      ∑ j, stateProb M R i j n * v j := by
  rw [kt_push, kt_pr_univ, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum; intro j _
  rw [← kt_occ_sum, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum; intro a _
  by_cases ha : a ∈ M.actions j
  · have := mul_le_mul_of_nonneg_left (hv j a ha) (kt_occ_nonneg M R i j a n)
    linarith
  · simp [kt_occ_outside _ _ _ _ _ _ ha]

lemma kt_disc_step_eq (M : MDP N α) (r : Fin N → α → ℝ) (δ : ℝ) (v : Fin N → ℝ)
    (f : PureRule M)
    (hv : ∀ j, r j (f.choose j) + δ * ∑ k, M.transition j (f.choose j) k * v k = v j)
    (i : Fin N) (n : ℕ) :
    periodReward M r (purePolicy M f) i n + δ * ∑ j, stateProb M (purePolicy M f) i j (n+1) * v j =
      ∑ j, stateProb M (purePolicy M f) i j n * v j := by
  rw [kt_push, kt_pr_univ, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro j _
  simp only [kt_occ_pure, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [← hv j]; ring

lemma kt_tend0 (δ : ℝ) (h0 : 0 ≤ δ) (h1 : δ < 1) (E : ℕ → ℝ) (B : ℝ) (hE : ∀ T, |E T| ≤ B) :
    Filter.Tendsto (fun T => δ ^ T * E T) Filter.atTop (nhds 0) := by
  have hp := (tendsto_pow_atTop_nhds_zero_of_lt_one h0 h1).mul_const B
  rw [zero_mul] at hp
  refine squeeze_zero_norm (fun T => ?_) hp
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg h0 _)]
  exact mul_le_mul_of_nonneg_left (hE T) (pow_nonneg h0 _)

lemma kt_E_bound (M : MDP N α) (R : Policy M) (i : Fin N) (v : Fin N → ℝ) (T : ℕ) :
    |∑ j, stateProb M R i j T * v j| ≤ ∑ j, |v j| := by
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum fun j _ => ?_)
  rw [abs_mul, abs_of_nonneg (kt_st_nonneg _ _ _ _ _)]
  exact mul_le_of_le_one_left (abs_nonneg _) (kt_st_le_one _ _ _ _ _)

theorem kt_disc_opt (M : MDP N α) (r : Fin N → α → ℝ) (δ : ℝ) (h0 : 0 ≤ δ) (h1 : δ < 1) :
    ∃ f : PureRule M, ∀ i (R : Policy M),
      discountedValue M r R i δ ≤ discountedValue M r (purePolicy M f) i δ := by
  classical
  let Tm : (Fin N → ℝ) → (Fin N → ℝ) := fun v i =>
    (M.actions i).sup' (M.actions_nonempty i) (fun a => r i a + δ * ∑ k, M.transition i a k * v k)
  have hlip : ∀ v w, dist (Tm v) (Tm w) ≤ δ * dist v w := by
    intro v w
    apply (dist_pi_le_iff (mul_nonneg h0 dist_nonneg)).2
    intro i
    have hA : ∀ (x y : Fin N → ℝ) a, a ∈ M.actions i →
        r i a + δ * ∑ k, M.transition i a k * x k ≤
          r i a + δ * ∑ k, M.transition i a k * y k + δ * dist x y := by
      intro x y a ha
      have hs : ∑ k, M.transition i a k * x k - ∑ k, M.transition i a k * y k ≤
          ∑ k, M.transition i a k * dist x y := by
        rw [← Finset.sum_sub_distrib]; apply Finset.sum_le_sum; intro k _
        have : x k - y k ≤ dist x y :=
          le_trans (le_abs_self _) (by rw [← Real.dist_eq]; exact dist_le_pi_dist x y k)
        nlinarith [M.transition_nonneg i a k ha]
      have h2 : ∑ k, M.transition i a k * dist x y ≤ dist x y := by
        rw [← Finset.sum_mul]; exact mul_le_of_le_one_left dist_nonneg (M.transition_subprob i a ha)
      nlinarith
    have hB : ∀ x y : Fin N → ℝ, Tm x i ≤ Tm y i + δ * dist x y := by
      intro x y
      apply Finset.sup'_le; intro a ha
      refine le_trans (hA x y a ha) ?_
      have := Finset.le_sup' (fun a => r i a + δ * ∑ k, M.transition i a k * y k) ha
      simp only [Tm]
      linarith
    rw [Real.dist_eq, abs_sub_le_iff]
    constructor
    · linarith [hB v w]
    · have := hB w v
      rw [dist_comm] at this
      linarith
  let K : NNReal := ⟨δ, h0⟩
  have hK : (K : ℝ) = δ := rfl
  have hC : ContractingWith K Tm := by
    refine ⟨?_, LipschitzWith.of_dist_le_mul fun v w => by rw [hK]; exact hlip v w⟩
    have : (K : ℝ) < 1 := by rw [hK]; exact h1
    exact_mod_cast this
  set v := ContractingWith.fixedPoint Tm hC
  have hv : Tm v = v := ContractingWith.fixedPoint_isFixedPt hC
  have hvle : ∀ j a, a ∈ M.actions j → r j a + δ * ∑ k, M.transition j a k * v k ≤ v j := by
    intro j a ha
    have := Finset.le_sup' (fun a => r j a + δ * ∑ k, M.transition j a k * v k) ha
    rw [← congrFun hv j]; exact this
  have hex : ∀ j, ∃ a ∈ M.actions j, r j a + δ * ∑ k, M.transition j a k * v k = v j := by
    intro j
    obtain ⟨a, ha, he⟩ := Finset.exists_mem_eq_sup' (M.actions_nonempty j)
      (fun a => r j a + δ * ∑ k, M.transition j a k * v k)
    exact ⟨a, ha, by rw [← congrFun hv j]; exact he.symm⟩
  choose g hg hgv using hex
  let f : PureRule M := ⟨g, hg⟩
  have htend : ∀ (R : Policy M) i, Filter.Tendsto (fun T => ∑ n ∈ Finset.range T,
      δ ^ n * periodReward M r R i n + δ ^ T * ∑ j, stateProb M R i j T * v j)
      Filter.atTop (nhds (discountedValue M r R i δ)) := by
    intro R i
    have := ((kt_disc_summable M r R i δ h0 h1).hasSum.tendsto_sum_nat).add
      (kt_tend0 δ h0 h1 _ _ (kt_E_bound M R i v))
    simpa [discountedValue] using this
  have tele : ∀ (R : Policy M) i T, ∑ n ∈ Finset.range T, δ ^ n * periodReward M r R i n +
      δ ^ T * ∑ j, stateProb M R i j T * v j ≤ v i := by
    intro R i T
    induction T with
    | zero => simp [kt_st_zero]
    | succ T ih =>
      have := kt_disc_step M r δ v hvle R i T
      have hp := pow_nonneg h0 T
      rw [Finset.sum_range_succ, pow_succ]
      have := mul_le_mul_of_nonneg_left this hp
      nlinarith
  have tele_eq : ∀ i T, ∑ n ∈ Finset.range T, δ ^ n * periodReward M r (purePolicy M f) i n +
      δ ^ T * ∑ j, stateProb M (purePolicy M f) i j T * v j = v i := by
    intro i T
    induction T with
    | zero => simp [kt_st_zero]
    | succ T ih =>
      have := kt_disc_step_eq M r δ v f hgv i T
      rw [Finset.sum_range_succ, pow_succ, ← ih, ← this]
      ring
  refine ⟨f, fun i R => ?_⟩
  have h1' : discountedValue M r R i δ ≤ v i := le_of_tendsto' (htend R i) (tele R i)
  have h2' : discountedValue M r (purePolicy M f) i δ = v i :=
    tendsto_nhds_unique (htend (purePolicy M f) i) (by simp only [tele_eq]; exact tendsto_const_nhds)
  rw [h2']; exact h1'

theorem kt_total_core (M : MDP N α) (r : Fin N → α → ℝ) (h : TotalRewardExists M r) :
    ∃ f : PureRule M,
      ∀ i : Fin N, policyValue M r (purePolicy M f) i = valueVector M r i := by
  classical
  have : Finite (PureRule M) := Finite.of_injective (fun f : PureRule M => f.choose)
    (by rintro ⟨f, hf⟩ ⟨g, hg⟩ hfg; simp only at hfg; subst hfg; rfl)
  let D : PureRule M → Set ℝ := fun f =>
    {δ | ∀ i (R : Policy M), discountedValue M r R i δ ≤ discountedValue M r (purePolicy M f) i δ}
  have hfreq : ∃ f, ∃ᶠ δ in nhdsWithin (1:ℝ) (Set.Iio 1), δ ∈ D f := by
    by_contra hc
    simp only [not_exists, Filter.not_frequently] at hc
    have hall : ∀ᶠ δ in nhdsWithin (1:ℝ) (Set.Iio 1), ∀ f, δ ∉ D f := Filter.eventually_all.2 hc
    have hI : ∀ᶠ δ in nhdsWithin (1:ℝ) (Set.Iio 1), δ ∈ Set.Ioo (0:ℝ) 1 :=
      Ioo_mem_nhdsLT (by norm_num)
    obtain ⟨δ, hδ1, hδ2⟩ := (hall.and hI).exists
    obtain ⟨f, hf⟩ := kt_disc_opt M r δ hδ2.1.le hδ2.2
    exact hδ1 f hf
  obtain ⟨f, hf⟩ := hfreq
  refine ⟨f, fun i => le_antisymm (le_iSup (fun R => policyValue M r R i) (purePolicy M f))
    (iSup_le fun R => ?_)⟩
  have hNB : (nhdsWithin (1:ℝ) (Set.Iio 1) ⊓ Filter.principal {δ | δ ∈ D f}).NeBot :=
    (Filter.frequently_iff_neBot (l := nhdsWithin (1:ℝ) (Set.Iio 1)) (p := fun δ => δ ∈ D f)).1 hf
  have t1 : Filter.Tendsto (fun δ : ℝ => (discountedValue M r R i δ : EReal))
      (nhdsWithin (1:ℝ) (Set.Iio 1) ⊓ Filter.principal {δ | δ ∈ D f}) (nhds (policyValue M r R i)) :=
    (kt_disc_core M r h i R).mono_left inf_le_left
  have t2 : Filter.Tendsto (fun δ : ℝ => (discountedValue M r (purePolicy M f) i δ : EReal))
      (nhdsWithin (1:ℝ) (Set.Iio 1) ⊓ Filter.principal {δ | δ ∈ D f})
      (nhds (policyValue M r (purePolicy M f) i)) :=
    (kt_disc_core M r h i (purePolicy M f)).mono_left inf_le_left
  refine le_of_tendsto_of_tendsto t1 t2 ?_
  exact Filter.mem_of_superset (Filter.mem_inf_of_right (Filter.mem_principal_self _))
    (fun δ hδ => EReal.coe_le_coe_iff.2 (hδ i R))

end KallenbergLP.Transient

open KallenbergLP.Transient


theorem solution
    {N : ℕ} {α : Type} [Fintype α] [DecidableEq α]
    (M : MDP N α) (r : Fin N → α → ℝ)
    (h : TotalRewardExists M r) :
    ∃ f : PureRule M,
      ∀ i : Fin N, policyValue M r (purePolicy M f) i = valueVector M r i := by
  exact kt_total_core M r h
