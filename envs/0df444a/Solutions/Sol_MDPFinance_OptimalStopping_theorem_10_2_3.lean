-- Prove2me | solution 1 for MDPFinance.OptimalStopping.theorem_10_2_3
-- status  : ACCEPTED   (disprove)
-- author  : @mrfancypants
-- created : 2026-10-13T04:47:56.425986+00:00
-- url     : https://prove2.me/submissions/d8949600-b051-438b-9d39-cc6c9a8e3054

import Mathlib
import Definitions.Def_MDPFinance_OptimalStopping_Stationary

open MeasureTheory Filter Topology MDPFinance.OptimalStopping

namespace OSDbl

def nxt (x : ℕ) : ℕ := if x = 0 then 0 else x + 1

lemma nxt_zero : nxt 0 = 0 := by simp [nxt]
lemma nxt_ne {x : ℕ} (hx : x ≠ 0) : nxt x = x + 1 := by simp [nxt, hx]

lemma iter_nxt_zero (n : ℕ) : nxt^[n] 0 = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply, nxt_zero, ih]

lemma iter_nxt_ne : ∀ (n : ℕ) {x : ℕ}, x ≠ 0 → nxt^[n] x = x + n
  | 0, x, _ => rfl
  | n + 1, x, hx => by
    rw [Function.iterate_succ_apply, nxt_ne hx, iter_nxt_ne n (by omega)]; ring

noncomputable def QXd (x : ℕ) : Measure ℕ :=
  (2⁻¹ : ENNReal) • Measure.dirac (nxt x) + (2⁻¹ : ENNReal) • Measure.dirac 0

instance QXd_prob (x : ℕ) : IsProbabilityMeasure (QXd x) :=
  ⟨by simp [QXd, ENNReal.inv_two_add_inv_two]⟩

noncomputable def gd (x : ℕ) : ℝ := (2 : ℝ) ^ x - 1

lemma gd_nonneg (x : ℕ) : 0 ≤ gd x := by
  unfold gd; have : (1 : ℝ) ≤ 2 ^ x := one_le_pow₀ (by norm_num); linarith

lemma gd_zero : gd 0 = 0 := by simp [gd]

noncomputable def P0 : StationaryProblem ℕ where
  QX := QXd
  QX_prob := fun x => inferInstance
  QX_meas := Measurable.of_discrete
  c := fun _ => 0
  c_meas := measurable_const
  g := gd
  g_meas := Measurable.of_discrete
  beta := 1
  beta_mem := by norm_num

lemma P0_QX : P0.QX = QXd := rfl
lemma P0_c (x : ℕ) : P0.c x = 0 := rfl
lemma P0_g (x : ℕ) : P0.g x = gd x := rfl
lemma P0_beta : P0.beta = 1 := rfl

def zeros : ℕ → ℕ := fun _ => 0

def cons (x : ℕ) (w : ℕ → ℕ) : ℕ → ℕ := fun n =>
  match n with
  | 0 => x
  | k + 1 => w k

lemma measurable_cons (x : ℕ) : Measurable (cons x) := by
  apply measurable_pi_iff.mpr
  intro n
  cases n with
  | zero => exact measurable_const
  | succ k => exact measurable_pi_apply k

def path : ℕ → ℕ → (ℕ → ℕ)
  | x, 0 => cons x zeros
  | x, j + 1 => cons x (path (nxt x) j)

lemma path_zero_state : ∀ j, path 0 j = zeros
  | 0 => by funext n; cases n <;> rfl
  | j + 1 => by
    show cons 0 (path (nxt 0) j) = zeros
    rw [nxt_zero, path_zero_state j]; funext n; cases n <;> rfl

lemma path_apply : ∀ (j x n : ℕ), path x j n = if n ≤ j then nxt^[n] x else 0
  | 0, x, n => by
    cases n with
    | zero => rfl
    | succ k => simp [path, cons, zeros]
  | j + 1, x, n => by
    cases n with
    | zero => simp [path, cons]
    | succ k =>
      show path (nxt x) j k = _
      rw [path_apply j (nxt x) k, Function.iterate_succ_apply]
      simp

noncomputable def Prd (x : ℕ) : Measure (ℕ → ℕ) :=
  Measure.sum (fun j : ℕ => ((2⁻¹ : ENNReal) ^ (j + 1)) • Measure.dirac (path x j))

lemma lint_Prd (x : ℕ) (f : (ℕ → ℕ) → ENNReal) :
    ∫⁻ w, f w ∂(Prd x) = ∑' j, (2⁻¹ : ENNReal) ^ (j + 1) * f (path x j) := by
  rw [Prd, lintegral_sum_measure]
  congr 1
  funext j
  rw [lintegral_smul_measure, lintegral_dirac, smul_eq_mul]

lemma Prd_apply (x : ℕ) (S : Set (ℕ → ℕ)) (hS : MeasurableSet S) :
    Prd x S = ∑' j, (2⁻¹ : ENNReal) ^ (j + 1) * S.indicator 1 (path x j) := by
  rw [Prd, Measure.sum_apply _ hS]
  congr 1
  funext j
  rw [Measure.smul_apply, Measure.dirac_apply, smul_eq_mul]

lemma geom : ∑' j : ℕ, (2⁻¹ : ENNReal) ^ (j + 1) = 1 := by
  rw [show (fun j : ℕ => (2⁻¹ : ENNReal) ^ (j + 1)) = fun j => 2⁻¹ * 2⁻¹ ^ j by
    funext j; rw [pow_succ, mul_comm]]
  rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric, ENNReal.one_sub_inv_two, inv_inv,
    ENNReal.inv_mul_cancel (by norm_num) (by norm_num)]

lemma tail : ∀ n : ℕ, ∑' j : ℕ, (if n ≤ j then (2⁻¹ : ENNReal) ^ (j + 1) else 0) = 2⁻¹ ^ n
  | 0 => by simp only [zero_le, if_true, pow_zero]; exact geom
  | n + 1 => by
    rw [tsum_eq_zero_add' ENNReal.summable]
    simp only [show ¬ (n + 1 ≤ 0) by omega, if_false, zero_add]
    have : ∀ j : ℕ, (if n + 1 ≤ j + 1 then (2⁻¹ : ENNReal) ^ (j + 1 + 1) else 0)
        = 2⁻¹ * (if n ≤ j then (2⁻¹ : ENNReal) ^ (j + 1) else 0) := by
      intro j
      by_cases h : n ≤ j
      · rw [if_pos (by omega), if_pos h, pow_succ' _ (j + 1)]
      · rw [if_neg (by omega), if_neg h, mul_zero]
    simp only [this]
    rw [ENNReal.tsum_mul_left, tail n, pow_succ']

instance Prd_prob (x : ℕ) : IsProbabilityMeasure (Prd x) := by
  constructor
  rw [Prd_apply x _ MeasurableSet.univ]
  simp only [Set.indicator_univ, Pi.one_apply, mul_one]
  exact geom

lemma Prd_null (x : ℕ) (s : Set (ℕ → ℕ)) (hs : ∀ j, path x j ∉ s) : Prd x s = 0 := by
  have hsub : s ⊆ (Set.range (path x))ᶜ := by
    rintro w hw ⟨j, rfl⟩
    exact hs j hw
  apply measure_mono_null hsub
  have hm : MeasurableSet (Set.range (path x))ᶜ := (Set.countable_range _).measurableSet.compl
  rw [Prd_apply x _ hm]
  have : ∀ j, (Set.range (path x))ᶜ.indicator (1 : (ℕ → ℕ) → ENNReal) (path x j) = 0 := by
    intro j
    rw [Set.indicator_of_notMem]
    simp
  simp

lemma Prd_decomp (x : ℕ) (S : Set (ℕ → ℕ)) (hS : MeasurableSet S) :
    Prd x S = 2⁻¹ * Prd (nxt x) (cons x ⁻¹' S) + 2⁻¹ * Prd 0 (cons x ⁻¹' S) := by
  have hS' : MeasurableSet (cons x ⁻¹' S) := measurable_cons x hS
  rw [Prd_apply x S hS, Prd_apply _ _ hS', Prd_apply _ _ hS', tsum_eq_zero_add' ENNReal.summable]
  simp only [path_zero_state]
  rw [ENNReal.tsum_mul_right, geom, one_mul]
  have h0 : (cons x ⁻¹' S).indicator (1 : (ℕ → ℕ) → ENNReal) zeros = S.indicator 1 (path x 0) := by
    show _ = S.indicator 1 (cons x zeros)
    by_cases h : cons x zeros ∈ S
    · rw [Set.indicator_of_mem h, Set.indicator_of_mem (show zeros ∈ cons x ⁻¹' S from h)]; rfl
    · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem (show zeros ∉ cons x ⁻¹' S from h)]
  have h1 : ∀ j, (2⁻¹ : ENNReal) ^ (j + 1 + 1) * S.indicator 1 (path x (j + 1))
      = 2⁻¹ * ((2⁻¹ : ENNReal) ^ (j + 1) * (cons x ⁻¹' S).indicator 1 (path (nxt x) j)) := by
    intro j
    rw [← mul_assoc, ← pow_succ']
    congr 1
  simp only [h1]
  rw [ENNReal.tsum_mul_left, h0, zero_add, pow_one, add_comm]

def cylS (m : ℕ) (B : ℕ → Set ℕ) : Set (ℕ → ℕ) := {w | ∀ i ≤ m, w i ∈ B i}

lemma cylS_meas (m : ℕ) (B : ℕ → Set ℕ) : MeasurableSet (cylS m B) := by
  have : cylS m B = ⋂ i ∈ Set.Iic m, (fun w : ℕ → ℕ => w i) ⁻¹' B i := by
    ext w; simp [cylS]
  rw [this]
  exact MeasurableSet.biInter (Set.to_countable _) fun i _ =>
    measurable_pi_apply i (MeasurableSet.of_discrete)

lemma cons_pre_zero (x : ℕ) (B : ℕ → Set ℕ) (hx : x ∈ B 0) : cons x ⁻¹' cylS 0 B = Set.univ := by
  ext w; simp only [cylS, Set.mem_preimage, Set.mem_setOf_eq, Set.mem_univ, iff_true]
  intro i hi
  have : i = 0 := by omega
  subst this; exact hx

lemma cons_pre_succ (x m : ℕ) (B : ℕ → Set ℕ) (hx : x ∈ B 0) :
    cons x ⁻¹' cylS (m + 1) B = cylS m (fun i => B (i + 1)) := by
  ext w; simp only [cylS, Set.mem_preimage, Set.mem_setOf_eq]
  constructor
  · intro h i hi; exact h (i + 1) (by omega)
  · intro h i hi
    cases i with
    | zero => exact hx
    | succ i => exact h i (by omega)

lemma cons_pre_out (x m : ℕ) (B : ℕ → Set ℕ) (hx : x ∉ B 0) :
    cons x ⁻¹' cylS m B = ∅ := by
  ext w; simp only [cylS, Set.mem_preimage, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
  intro h; exact hx (h 0 (by omega))

lemma cyl_succ (m : ℕ) (B : ℕ → Set ℕ) (y : ℕ) :
    P0.cyl (m + 1) B y = 2⁻¹ * (B 0).indicator (P0.cyl m (fun i => B (i + 1))) (nxt y)
      + 2⁻¹ * (B 0).indicator (P0.cyl m (fun i => B (i + 1))) 0 := by
  show ∫⁻ z in B 0, P0.cyl m (fun i => B (i + 1)) z ∂(QXd y) = _
  rw [← lintegral_indicator MeasurableSet.of_discrete, QXd, lintegral_add_measure,
    lintegral_smul_measure, lintegral_smul_measure, lintegral_dirac, lintegral_dirac]
  rfl

lemma hPr : P0.IsPathLaw Prd := by
  refine ⟨fun x => inferInstance, ?_⟩
  intro x m
  induction m generalizing x with
  | zero =>
    intro B hB
    change Prd x (cylS 0 B) = _
    by_cases hx : x ∈ B 0
    · rw [Prd_decomp x _ (cylS_meas 0 B), cons_pre_zero x B hx, measure_univ, measure_univ,
        Set.indicator_of_mem hx]
      simp [StationaryProblem.cyl, ENNReal.inv_two_add_inv_two]
    · rw [Prd_decomp x _ (cylS_meas 0 B), cons_pre_out x 0 B hx, Set.indicator_of_notMem hx]
      simp
  | succ m ih =>
    intro B hB
    change Prd x (cylS (m + 1) B) = _
    by_cases hx : x ∈ B 0
    · rw [Prd_decomp x _ (cylS_meas _ B), cons_pre_succ x m B hx, Set.indicator_of_mem hx,
        cyl_succ]
      have e1 := ih (nxt x) (fun i => B (i + 1)) (fun i => hB _)
      have e2 := ih 0 (fun i => B (i + 1)) (fun i => hB _)
      change Prd (nxt x) (cylS m (fun i => B (i + 1))) = _ at e1
      change Prd 0 (cylS m (fun i => B (i + 1))) = _ at e2
      rw [e1, e2]
    · rw [Prd_decomp x _ (cylS_meas _ B), cons_pre_out x _ B hx, Set.indicator_of_notMem hx]
      simp

/-! ## Stopping times and rewards -/

def alive (x : ℕ) : ℕ → ℕ := fun n => nxt^[n] x

lemma stop_agree {τ : (ℕ → ℕ) → ℕ∞} (hτ : IsStopTime τ) {w w' : ℕ → ℕ} {n : ℕ}
    (h : ∀ i ≤ n, w i = w' i) : τ w ≤ n ↔ τ w' ≤ n := by
  have hm := hτ n
  unfold pathFiltration at hm
  rw [MeasurableSpace.measurableSet_comap] at hm
  obtain ⟨s, -, hs⟩ := hm
  have key : (fun i : Fin (n + 1) => w i) = (fun i : Fin (n + 1) => w' i) :=
    funext fun i => h i (Nat.lt_succ_iff.mp i.2)
  have e : ∀ v : ℕ → ℕ, τ v ≤ n ↔ (fun i : Fin (n + 1) => v i) ∈ s := by
    intro v
    constructor
    · intro hv
      have : v ∈ (fun w : ℕ → ℕ => fun i : Fin (n + 1) => w i) ⁻¹' s := by rw [hs]; exact hv
      exact this
    · intro hv
      have : v ∈ (fun w : ℕ → ℕ => fun i : Fin (n + 1) => w i) ⁻¹' s := hv
      rw [hs] at this; exact this
  rw [e w, e w', key]

lemma path_alive (x j : ℕ) : ∀ i ≤ j, path x j i = alive x i := by
  intro i hi; rw [path_apply, if_pos hi]; rfl

lemma path_late (x j i : ℕ) (hi : j < i) : path x j i = 0 := by
  rw [path_apply, if_neg (by omega)]

lemma stop_iff {τ : (ℕ → ℕ) → ℕ∞} (hτ : IsStopTime τ) (x j n : ℕ) (hn : n ≤ j) :
    τ (path x j) ≤ n ↔ τ (alive x) ≤ n :=
  stop_agree hτ (fun i hi => path_alive x j i (le_trans hi hn))

lemma stop_fin {τ : (ℕ → ℕ) → ℕ∞} (hτ : IsStopTime τ) (x j m : ℕ) (hm : τ (alive x) = m)
    (hmj : m ≤ j) : τ (path x j) = m := by
  apply le_antisymm
  · rw [stop_iff hτ x j m hmj, hm]
  · by_contra h
    push Not at h
    obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.mp (ne_top_of_lt h)
    rw [← hk] at h
    have hkm : k < m := by exact_mod_cast h
    have := (stop_iff hτ x j k (by omega)).mp (le_of_eq hk.symm)
    rw [hm] at this
    have : m ≤ k := by exact_mod_cast this
    omega

lemma reward_coe (τ : (ℕ → ℕ) → ℕ∞) (w : ℕ → ℕ) (m : ℕ) (h : τ w = m) :
    P0.reward τ w = gd (w m) := by
  unfold StationaryProblem.reward
  rw [h]
  simp [P0_c, P0_g, P0_beta]

lemma reward_top (τ : (ℕ → ℕ) → ℕ∞) (w : ℕ → ℕ) (h : τ w = ⊤) :
    P0.reward τ w = 0 := by
  unfold StationaryProblem.reward
  rw [h]
  rfl

lemma reward_nonneg (τ : (ℕ → ℕ) → ℕ∞) (w : ℕ → ℕ) : 0 ≤ P0.reward τ w := by
  rcases (em (τ w = ⊤)) with h | h
  · rw [reward_top τ w h]
  · obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp h
    rw [reward_coe τ w m hm.symm]; exact gd_nonneg _

lemma reward_late (σ : (ℕ → ℕ) → ℕ∞) (x j : ℕ) (h : ∀ n ≤ j, ¬ σ (path x j) ≤ n) :
    P0.reward σ (path x j) = 0 := by
  rcases (em (σ (path x j) = ⊤)) with h' | h'
  · exact reward_top σ _ h'
  · obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp h'
    rw [reward_coe σ _ m hm.symm]
    have : j < m := by
      by_contra hc
      exact h m (by omega) (le_of_eq hm.symm)
    rw [path_late x j m this, gd_zero]

lemma eI_nonneg {α : Type*} [MeasurableSpace α] (μ : Measure α) (f : α → ℝ) (hf : ∀ a, 0 ≤ f a) :
    erealIntegral μ (fun a => (f a : EReal)) = ((∫⁻ a, ENNReal.ofReal (f a) ∂μ : ENNReal) : EReal) := by
  unfold erealIntegral
  have h1 : ∀ a, (((f a : EReal)) ⊔ 0).toENNReal = ENNReal.ofReal (f a) := by
    intro a
    rw [sup_eq_left.mpr (by exact_mod_cast hf a)]
    rw [show ((f a : ℝ) : EReal) = ((ENNReal.ofReal (f a) : ENNReal) : EReal) by
      rw [EReal.coe_ennreal_ofReal, max_eq_left (hf a)], EReal.toENNReal_coe]
  have h2 : ∀ a, ((-(f a : EReal)) ⊔ 0).toENNReal = 0 := by
    intro a
    rw [sup_eq_right.mpr]
    · simp
    · rw [EReal.neg_le, neg_zero]; exact_mod_cast hf a
  simp only [h1, h2, lintegral_zero, EReal.coe_ennreal_zero, neg_zero, add_zero]

lemma ER_eq (τ : (ℕ → ℕ) → ℕ∞) (x : ℕ) :
    P0.EReward Prd τ x = ((∑' j, (2⁻¹ : ENNReal) ^ (j + 1) *
      ENNReal.ofReal (P0.reward τ (path x j)) : ENNReal) : EReal) := by
  unfold StationaryProblem.EReward
  rw [eI_nonneg _ _ (reward_nonneg τ), lint_Prd]

lemma gd_le_alive (x k : ℕ) : gd (nxt^[k] x) ≤ 2 ^ (x + k) := by
  rcases Nat.eq_zero_or_pos x with hx | hx
  · subst hx; rw [iter_nxt_zero, gd_zero]; positivity
  · rw [iter_nxt_ne k (by omega)]; unfold gd; linarith

lemma gd_le_self (x : ℕ) : gd x ≤ 2 ^ x := by unfold gd; linarith

lemma val_late (τ : (ℕ → ℕ) → ℕ∞) (x j : ℕ) (h : ∀ n ≤ j, ¬ τ (path x j) ≤ n) :
    gd (path x j (τ (path x j)).toNat) ≤ 2 ^ x := by
  rcases (em (τ (path x j) = ⊤)) with h' | h'
  · rw [h', ENat.toNat_top, path_apply, if_pos (Nat.zero_le _)]
    exact gd_le_self x
  · obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp h'
    rw [← hm, ENat.toNat_natCast]
    have : j < m := by
      by_contra hc
      exact h m (by omega) (le_of_eq hm.symm)
    rw [path_late x j m this, gd_zero]; positivity

lemma two_pow_mul (x m : ℕ) :
    ENNReal.ofReal ((2 : ℝ) ^ (x + m)) * (2⁻¹ : ENNReal) ^ m = ENNReal.ofReal ((2 : ℝ) ^ x) := by
  rw [pow_add, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (by norm_num) m,
    ENNReal.ofReal_ofNat, mul_assoc, ← mul_pow, ENNReal.mul_inv_cancel (by norm_num) (by norm_num),
    one_pow, mul_one]

lemma hB1 (x : ℕ) : ∃ C : ENNReal, C < ⊤ ∧ ∀ tau : (ℕ → ℕ) → ℕ∞, IsStopTime tau →
      (Prd x {w | tau w = ⊤} = 0) →
      ∫⁻ w, ENNReal.ofReal ((∑ k ∈ Finset.range ((tau w).toNat), P0.beta ^ k * max (P0.c (w k)) 0)
          + P0.beta ^ (tau w).toNat * max (P0.g (w (tau w).toNat)) 0) ∂(Prd x) ≤ C := by
  refine ⟨ENNReal.ofReal ((2 : ℝ) ^ x) + ENNReal.ofReal ((2 : ℝ) ^ x),
    ENNReal.add_lt_top.mpr ⟨ENNReal.ofReal_lt_top, ENNReal.ofReal_lt_top⟩, ?_⟩
  intro τ hτ _
  simp only [P0_beta, P0_c, P0_g, one_pow, max_self, mul_zero, Finset.sum_const_zero, zero_add,
    one_mul, max_eq_left (gd_nonneg _)]
  rw [lint_Prd]
  rcases (em (τ (alive x) = ⊤)) with htop | hfin
  · -- never stops along the surviving path
    have hb : ∀ j, (2⁻¹ : ENNReal) ^ (j + 1) * ENNReal.ofReal (gd (path x j (τ (path x j)).toNat))
        ≤ (2⁻¹ : ENNReal) ^ (j + 1) * ENNReal.ofReal ((2 : ℝ) ^ x) := by
      intro j
      gcongr
      apply val_late
      intro n hn hle
      rw [stop_iff hτ x j n hn, htop] at hle
      exact absurd hle (by simp)
    calc _ ≤ ∑' j, (2⁻¹ : ENNReal) ^ (j + 1) * ENNReal.ofReal ((2 : ℝ) ^ x) :=
          ENNReal.tsum_le_tsum hb
      _ = ENNReal.ofReal ((2 : ℝ) ^ x) := by rw [ENNReal.tsum_mul_right, geom, one_mul]
      _ ≤ _ := le_self_add
  · obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp hfin
    have hb : ∀ j, (2⁻¹ : ENNReal) ^ (j + 1) * ENNReal.ofReal (gd (path x j (τ (path x j)).toNat))
        ≤ (2⁻¹ : ENNReal) ^ (j + 1) * ENNReal.ofReal ((2 : ℝ) ^ x)
          + (if m ≤ j then (2⁻¹ : ENNReal) ^ (j + 1) else 0) * ENNReal.ofReal ((2 : ℝ) ^ (x + m)) := by
      intro j
      by_cases hmj : m ≤ j
      · rw [if_pos hmj, stop_fin hτ x j m hm.symm hmj, ENat.toNat_natCast, path_alive x j m hmj]
        refine le_trans ?_ le_add_self
        gcongr
        exact gd_le_alive x m
      · refine le_trans ?_ le_self_add
        gcongr
        apply val_late
        intro n hn hle
        rw [stop_iff hτ x j n hn, ← hm] at hle
        have : m ≤ n := by exact_mod_cast hle
        omega
    calc _ ≤ ∑' j, ((2⁻¹ : ENNReal) ^ (j + 1) * ENNReal.ofReal ((2 : ℝ) ^ x)
          + (if m ≤ j then (2⁻¹ : ENNReal) ^ (j + 1) else 0) * ENNReal.ofReal ((2 : ℝ) ^ (x + m))) :=
          ENNReal.tsum_le_tsum hb
      _ = _ := by
        rw [ENNReal.tsum_add, ENNReal.tsum_mul_right, ENNReal.tsum_mul_right, geom, one_mul, tail,
          mul_comm, two_pow_mul]

lemma hB2 (x : ℕ) (τ : (ℕ → ℕ) → ℕ∞) (hτ : IsStopTime τ) :
    P0.EReward Prd τ x ≤ liminf (fun n : ℕ => P0.EReward Prd (truncTime τ n) x) atTop := by
  rcases (em (τ (alive x) = ⊤)) with htop | hfin
  · have h0 : P0.EReward Prd τ x = 0 := by
      rw [ER_eq]
      have : ∀ j, P0.reward τ (path x j) = 0 := by
        intro j
        apply reward_late
        intro n hn hle
        rw [stop_iff hτ x j n hn, htop] at hle
        exact absurd hle (by simp)
      simp [this]
    rw [h0]
    exact le_liminf_of_le (by isBoundedDefault)
      (Eventually.of_forall fun n => by rw [ER_eq]; exact EReal.coe_ennreal_nonneg _)
  · obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp hfin
    have heq : ∀ n, m ≤ n → P0.EReward Prd (truncTime τ n) x = P0.EReward Prd τ x := by
      intro n hn
      rw [ER_eq, ER_eq]
      congr 2
      funext j
      congr 2
      by_cases hmj : m ≤ j
      · have h1 := stop_fin hτ x j m hm.symm hmj
        have h2 : truncTime τ n (path x j) = m := by
          unfold truncTime; rw [h1]; exact min_eq_left (by exact_mod_cast hn)
        rw [reward_coe _ _ m h1, reward_coe _ _ m h2]
      · have hl : ∀ n' ≤ j, ¬ τ (path x j) ≤ n' := by
          intro n' hn' hle
          rw [stop_iff hτ x j n' hn', ← hm] at hle
          have : m ≤ n' := by exact_mod_cast hle
          omega
        rw [reward_late τ x j hl, reward_late (truncTime τ n) x j]
        intro n' hn' hle
        unfold truncTime at hle
        rcases min_le_iff.mp hle with h | h
        · exact hl n' hn' h
        · have : n ≤ n' := by exact_mod_cast h
          omega
    exact le_liminf_of_le (by isBoundedDefault)
      (eventually_atTop.mpr ⟨m, fun n hn => le_of_eq (heq n hn).symm⟩)

lemma hB : P0.AssumptionB Prd := ⟨hB1, fun x τ hτ _ => hB2 x τ hτ⟩

/-! ## Hitting time of the cemetery and the failure of optimality -/

lemma hit_mem (S : Set ℕ) (w : ℕ → ℕ) (m : ℕ) (h : hitTime S w = m) : w m ∈ S := by
  unfold hitTime at h
  by_cases hne : {k : ℕ | w k ∈ S}.Nonempty
  · have hk := Nat.sInf_mem hne
    have e : sInf ((fun k : ℕ => (k : ℕ∞)) '' {k : ℕ | w k ∈ S}) = (sInf {k : ℕ | w k ∈ S} : ℕ) := by
      apply le_antisymm
      · exact sInf_le ⟨_, hk, rfl⟩
      · apply le_sInf
        rintro b ⟨k, hk', rfl⟩
        show ((sInf {k : ℕ | w k ∈ S} : ℕ) : ℕ∞) ≤ (k : ℕ∞)
        exact_mod_cast Nat.sInf_le hk'
    rw [e] at h
    have : sInf {k : ℕ | w k ∈ S} = m := by exact_mod_cast h
    rw [← this]; exact hk
  · rw [Set.not_nonempty_iff_eq_empty] at hne
    rw [hne, Set.image_empty, sInf_empty] at h
    exact absurd h (by simp)

lemma hit_le (S : Set ℕ) (w : ℕ → ℕ) (k : ℕ) (h : w k ∈ S) : hitTime S w ≤ k :=
  sInf_le ⟨k, h, rfl⟩

lemma hit_ge (S : Set ℕ) (w : ℕ → ℕ) (k : ℕ) (h : ∀ i < k, w i ∉ S) : (k : ℕ∞) ≤ hitTime S w := by
  apply le_sInf
  rintro b ⟨i, hi, rfl⟩
  have : k ≤ i := by
    by_contra hc
    exact h i (by omega) hi
  show (k : ℕ∞) ≤ (i : ℕ∞)
  exact_mod_cast this

lemma hfin0 (x : ℕ) : Prd x {w | hitTime ({0} : Set ℕ) w = ⊤} = 0 := by
  apply Prd_null
  intro j hj
  have := hit_le {0} (path x j) (j + 1) (by rw [path_late x j (j + 1) (by omega)]; rfl)
  rw [show hitTime ({0} : Set ℕ) (path x j) = ⊤ from hj] at this
  exact absurd this (by simp)

lemma ER_hit_zero (x : ℕ) : P0.EReward Prd (hitTime ({0} : Set ℕ)) x = 0 := by
  rw [ER_eq]
  have : ∀ j, P0.reward (hitTime ({0} : Set ℕ)) (path x j) = 0 := by
    intro j
    rcases (em (hitTime ({0} : Set ℕ) (path x j) = ⊤)) with h | h
    · exact reward_top _ _ h
    · obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp h
      rw [reward_coe _ _ m hm.symm]
      have := hit_mem {0} (path x j) m hm.symm
      rw [Set.mem_singleton_iff] at this
      rw [this, gd_zero]
  simp [this]

lemma stop_const0 : IsStopTime (fun _ : ℕ → ℕ => (0 : ℕ∞)) := by
  intro n
  simp only [zero_le, Set.setOf_true]
  exact MeasurableSet.univ

lemma ER_const0 (x : ℕ) : P0.EReward Prd (fun _ => (0 : ℕ∞)) x = ((gd x : ℝ) : EReal) := by
  rw [ER_eq]
  have : ∀ j, P0.reward (fun _ => (0 : ℕ∞)) (path x j) = gd x := by
    intro j
    rw [reward_coe _ _ 0 (by simp), path_apply, if_pos (Nat.zero_le _)]
    rfl
  simp only [this]
  rw [ENNReal.tsum_mul_right, geom, one_mul, EReal.coe_ennreal_ofReal, max_eq_left (gd_nonneg x)]

lemma Vstar_ge (x : ℕ) : ((gd x : ℝ) : EReal) ≤ P0.Vstar Prd x := by
  rw [← ER_const0 x]
  unfold StationaryProblem.Vstar
  exact le_iSup₂_of_le (fun _ => (0 : ℕ∞)) ⟨stop_const0, by simp⟩ le_rfl

lemma not_opt : ¬ P0.IsOptimal Prd (hitTime ({0} : Set ℕ)) := by
  rintro ⟨-, -, h⟩
  have h1 := h 1
  rw [ER_hit_zero] at h1
  have h2 := Vstar_ge 1
  rw [← h1] at h2
  have : gd 1 = 1 := by norm_num [gd]
  rw [this] at h2
  exact absurd h2 (by norm_num)

/-! ## Value iteration -/

lemma eI_QX (x : ℕ) (f : ℕ → ℝ) (hf : ∀ y, 0 ≤ f y) :
    erealIntegral (QXd x) (fun y => (f y : EReal)) = (((f (nxt x) + f 0) / 2 : ℝ) : EReal) := by
  rw [eI_nonneg _ _ hf, QXd, lintegral_add_measure, lintegral_smul_measure, lintegral_smul_measure,
    lintegral_dirac, lintegral_dirac]
  have h2 : (2⁻¹ : ENNReal) = ENNReal.ofReal (1 / 2) := by
    rw [one_div, ENNReal.ofReal_inv_of_pos (by norm_num), ENNReal.ofReal_ofNat]
  rw [smul_eq_mul, smul_eq_mul, h2, ← ENNReal.ofReal_mul (by norm_num),
    ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_add (by have := hf (nxt x); positivity)
      (by have := hf 0; positivity), EReal.coe_ennreal_ofReal, max_eq_left (by
        have := hf (nxt x); have := hf 0; positivity)]
  congr 1; ring

noncomputable def jn (n x : ℕ) : ℝ := if x = 0 then 0 else 2 ^ x - (1 / 2) ^ n

lemma jn_nonneg (n x : ℕ) : 0 ≤ jn n x := by
  unfold jn
  split_ifs
  · exact le_rfl
  · have h1 : (1 : ℝ) ≤ 2 ^ x := one_le_pow₀ (by norm_num)
    have h2 : ((1 : ℝ) / 2) ^ n ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    linarith

lemma emax (a b : ℝ) : max (a : EReal) (b : EReal) = ((max a b : ℝ) : EReal) := by
  rcases le_total a b with h | h
  · rw [max_eq_right h, max_eq_right (by exact_mod_cast h)]
  · rw [max_eq_left h, max_eq_left (by exact_mod_cast h)]

lemma T_coe (v : ℕ → ℝ) (hv : ∀ y, 0 ≤ v y) (x : ℕ) :
    P0.T (fun y => (v y : EReal)) x = ((max (gd x) ((v (nxt x) + v 0) / 2) : ℝ) : EReal) := by
  unfold StationaryProblem.T
  rw [P0_QX, eI_QX x v hv, P0_g, P0_c, P0_beta, EReal.coe_zero, EReal.coe_one, zero_add, one_mul,
    emax]

lemma J_eq : ∀ n, P0.J n = fun x => ((jn n x : ℝ) : EReal)
  | 0 => by
    funext x
    show ((gd x : ℝ) : EReal) = _
    unfold jn gd
    split_ifs with h
    · subst h; simp
    · simp
  | n + 1 => by
    funext x
    show P0.T (P0.J n) x = _
    rw [J_eq n, T_coe _ (jn_nonneg n)]
    congr 1
    unfold jn gd
    by_cases hx : x = 0
    · subst hx; simp [nxt_zero]
    · rw [nxt_ne hx]
      simp only [hx, if_false, show x + 1 ≠ 0 by omega, if_true]
      have h2 : ((1 : ℝ) / 2) ^ n ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
      rw [max_eq_right]
      · rw [pow_succ, pow_succ]; ring
      · rw [pow_succ]; nlinarith

noncomputable def jl (x : ℕ) : ℝ := if x = 0 then 0 else 2 ^ x

lemma jl_nonneg (x : ℕ) : 0 ≤ jl x := by unfold jl; split_ifs <;> positivity

lemma jn_le (n x : ℕ) : jn n x ≤ jl x := by
  unfold jn jl; split_ifs
  · exact le_rfl
  · have : (0 : ℝ) ≤ (1 / 2) ^ n := by positivity
    linarith

lemma jn_mono (x : ℕ) : Monotone (fun n => ((jn n x : ℝ) : EReal)) := by
  intro a b hab
  simp only [EReal.coe_le_coe_iff]
  unfold jn; split_ifs
  · exact le_rfl
  · have : ((1 : ℝ) / 2) ^ b ≤ (1 / 2) ^ a := pow_le_pow_of_le_one (by norm_num) (by norm_num) hab
    linarith

lemma iSup_jn (x : ℕ) : (⨆ n, ((jn n x : ℝ) : EReal)) = ((jl x : ℝ) : EReal) := by
  apply le_antisymm
  · exact iSup_le fun n => by exact_mod_cast jn_le n x
  · apply le_of_forall_lt
    intro c hc
    induction c using EReal.rec with
    | bot => exact lt_of_lt_of_le (EReal.bot_lt_coe _) (le_iSup (fun n => ((jn n x : ℝ) : EReal)) 0)
    | top => exact absurd hc (not_lt.mpr le_top)
    | coe r =>
      have hr : r < jl x := by exact_mod_cast hc
      by_cases hx : x = 0
      · have : jl x = 0 := by simp [jl, hx]
        have : r < jn 0 x := by simp [jn, hx]; linarith
        exact lt_of_lt_of_le (by exact_mod_cast this) (le_iSup (fun n => ((jn n x : ℝ) : EReal)) 0)
      · have hjl : jl x = 2 ^ x := by simp [jl, hx]
        obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (sub_pos.mpr hr) (by norm_num : (1 : ℝ) / 2 < 1)
        have : r < jn n x := by simp only [jn, hx, if_false]; rw [hjl] at hn; linarith
        exact lt_of_lt_of_le (by exact_mod_cast this) (le_iSup (fun n => ((jn n x : ℝ) : EReal)) n)

lemma Jlim_eq : P0.Jlim = fun x => ((jl x : ℝ) : EReal) := by
  funext x
  unfold StationaryProblem.Jlim
  have : ∀ n, P0.J n x = ((jn n x : ℝ) : EReal) := fun n => by rw [J_eq]
  simp only [this]
  exact iSup_jn x

lemma TJ (x : ℕ) : P0.T P0.Jlim x = P0.Jlim x := by
  rw [Jlim_eq, T_coe _ jl_nonneg]
  congr 1
  unfold jl gd
  by_cases hx : x = 0
  · subst hx; simp [nxt_zero]
  · rw [nxt_ne hx]
    simp only [hx, if_false, show x + 1 ≠ 0 by omega, if_true]
    rw [max_eq_right] <;> rw [pow_succ] <;> linarith

lemma maxim : P0.IsMaximizer ({0} : Set ℕ) P0.Jlim := by
  refine ⟨MeasurableSet.of_discrete, fun x => ?_⟩
  rw [TJ]
  unfold StationaryProblem.Tf
  by_cases hx : x = 0
  · subst hx
    rw [if_pos (Set.mem_singleton 0), Jlim_eq]
    simp [jl, P0_g, gd_zero]
  · rw [if_neg (show x ∉ ({0} : Set ℕ) from hx), P0_QX, Jlim_eq, eI_QX x jl jl_nonneg, P0_c, P0_beta, EReal.coe_zero,
      EReal.coe_one, zero_add, one_mul, nxt_ne hx]
    congr 1
    simp only [jl, hx, if_false, show x + 1 ≠ 0 by omega, if_true]
    rw [pow_succ]; ring

lemma stopset_eq : {y : ℕ | P0.Jlim y = (P0.g y : EReal)} = ({0} : Set ℕ) := by
  ext y
  rw [Jlim_eq, Set.mem_setOf_eq, Set.mem_singleton_iff, P0_g, EReal.coe_eq_coe_iff]
  unfold jl gd
  by_cases hy : y = 0
  · simp [hy]
  · simp only [hy, if_false]
    constructor
    · intro h; linarith
    · intro h; exact absurd h (by simp [hy])

/-! ## The truncated hitting rewards (for `G_f`) -/

lemma reward_zeros (σ : (ℕ → ℕ) → ℕ∞) : P0.reward σ zeros = 0 := by
  rcases (em (σ zeros = ⊤)) with h | h
  · exact reward_top _ _ h
  · obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp h
    rw [reward_coe _ _ m hm.symm]; exact gd_zero

lemma ER_trunc (n x : ℕ) :
    P0.EReward Prd (truncTime (hitTime ({0} : Set ℕ)) n) x = ((jn n x : ℝ) : EReal) := by
  rw [ER_eq]
  by_cases hx : x = 0
  · subst hx
    simp only [path_zero_state, reward_zeros, ENNReal.ofReal_zero, mul_zero, tsum_zero]
    simp [jn]
  · have hhit : ∀ j, hitTime ({0} : Set ℕ) (path x j) = ((j + 1 : ℕ) : ℕ∞) := by
      intro j
      apply le_antisymm
      · exact hit_le _ _ _ (by rw [path_late x j (j + 1) (by omega)]; rfl)
      · apply hit_ge
        intro i hi
        rw [path_apply, if_pos (by omega), iter_nxt_ne i hx, Set.mem_singleton_iff]
        omega
    have hterm : ∀ j, (2⁻¹ : ENNReal) ^ (j + 1) *
        ENNReal.ofReal (P0.reward (truncTime (hitTime ({0} : Set ℕ)) n) (path x j))
        = (if n ≤ j then (2⁻¹ : ENNReal) ^ (j + 1) else 0) *
          ENNReal.ofReal ((2 : ℝ) ^ (x + n) - 1) := by
      intro j
      by_cases hnj : n ≤ j
      · have ht : truncTime (hitTime ({0} : Set ℕ)) n (path x j) = n := by
          unfold truncTime; rw [hhit j]; exact min_eq_right (by exact_mod_cast (by omega : n ≤ j + 1))
        rw [reward_coe _ _ n ht, path_apply, if_pos hnj, iter_nxt_ne n hx, if_pos hnj]
        rfl
      · have ht : truncTime (hitTime ({0} : Set ℕ)) n (path x j) = ((j + 1 : ℕ) : ℕ∞) := by
          unfold truncTime; rw [hhit j]; exact min_eq_left (by exact_mod_cast (by omega : j + 1 ≤ n))
        rw [reward_coe _ _ _ ht, path_late x j (j + 1) (by omega), gd_zero, if_neg hnj]
        simp
    simp only [hterm]
    rw [ENNReal.tsum_mul_right, tail]
    have h2 : (2⁻¹ : ENNReal) ^ n = ENNReal.ofReal ((1 / 2) ^ n) := by
      rw [ENNReal.ofReal_pow (by norm_num), one_div, ENNReal.ofReal_inv_of_pos (by norm_num),
        ENNReal.ofReal_ofNat]
    have hpos : (0 : ℝ) ≤ (2 : ℝ) ^ (x + n) - 1 := by
      have : (1 : ℝ) ≤ 2 ^ (x + n) := one_le_pow₀ (by norm_num); linarith
    have hid : ((2 : ℝ) ^ (x + n) - 1) * (1 / 2) ^ n = 2 ^ x - (1 / 2) ^ n := by
      have : (2 : ℝ) ^ (x + n) * (1 / 2) ^ n = 2 ^ x := by
        rw [pow_add, mul_assoc, ← mul_pow]; norm_num
      rw [sub_mul, this, one_mul]
    rw [h2, mul_comm, ← ENNReal.ofReal_mul hpos, hid, EReal.coe_ennreal_ofReal,
      max_eq_left (by have := jn_nonneg n x; simpa [jn, hx] using this)]
    simp [jn, hx]

lemma Gf_eq (x : ℕ) : P0.Gf Prd ({0} : Set ℕ) x = P0.Jlim x := by
  unfold StationaryProblem.Gf StationaryProblem.ruleTime
  simp only [ER_trunc]
  rw [(tendsto_atTop_iSup (jn_mono x)).liminf_eq, iSup_jn, Jlim_eq]

/-! ## The three disproofs -/

theorem cor_10_2_6_false : ¬ (∀ {E : Type} [MeasurableSpace E] (P : StationaryProblem E)
    (Pr : E → Measure (ℕ → E)) (hPr : P.IsPathLaw Pr) (hB : P.AssumptionB Pr)
    (S : Set E) (hS : P.IsMaximizer S P.Jlim),
    (∀ B : P.BoundingFunction, P.beta * B.alpha < 1 →
      (∀ x : E, P.Gf Pr S x = P.Jlim x) ∧
      ((∀ x : E, Pr x {w | P.ruleTime S w = ⊤} = 0) → P.IsOptimal Pr (P.ruleTime S))) ∧
    ((∃ s : ℝ, s < 0 ∧ ∀ x : E, P.c x ≤ s) → P.beta = 1 → (∀ x : E, P.Gf Pr S x = P.Jlim x) →
      (∀ x : E, Pr x {w | P.ruleTime S w = ⊤} = 0) ∧ P.IsOptimal Pr (P.ruleTime S)) ∧
    ((∃ C : ℝ, ∀ x : E, P.Jlim x ≤ (P.g x : EReal) + (C : EReal)) →
      (∀ x : E, Pr x {w | P.ruleTime S w = ⊤} = 0) →
      P.IsOptimal Pr (P.ruleTime S) ∧ ∀ x : E, P.Gf Pr S x = P.Jlim x)) := by
  intro h
  have hbd : ∃ C : ℝ, ∀ x : ℕ, P0.Jlim x ≤ (P0.g x : EReal) + (C : EReal) := by
    refine ⟨1, fun x => ?_⟩
    rw [Jlim_eq, P0_g, ← EReal.coe_add, EReal.coe_le_coe_iff]
    unfold jl gd
    split_ifs <;> simp
  exact not_opt ((h P0 Prd hPr hB {0} maxim).2.2 hbd (fun x => hfin0 x)).1

theorem t_10_2_7_false : ¬ (∀ {E : Type} [MeasurableSpace E] (P : StationaryProblem E)
    (Pr : E → Measure (ℕ → E)) (hPr : P.IsPathLaw Pr) (hB : P.AssumptionB Pr)
    (S0 : Set E)
    (hS0 : S0 = {x : E | (P.c x : EReal) + (P.beta : EReal) *
      erealIntegral (P.QX x) (fun y => (P.g y : EReal)) ≤ (P.g x : EReal)})
    (hclosed : ∀ x ∈ S0, P.QX x S0 = 1),
    (P.IsMaximizer S0 P.Jlim ∧ ∀ n : ℕ, 1 ≤ n → P.IsMaximizer S0 (P.J n)) ∧
    ((∀ (N : ℕ) (x : E), P.EReward Pr (truncTime (hitTime S0) N) x = P.valueUpTo Pr N x) ∧
      ((∀ x : E, Pr x {w | hitTime S0 w = ⊤} = 0) → P.IsOptimal Pr (hitTime S0)))) := by
  intro h
  have hS : ({0} : Set ℕ) = {x : ℕ | (P0.c x : EReal) + (P0.beta : EReal) *
      erealIntegral (P0.QX x) (fun y => (P0.g y : EReal)) ≤ (P0.g x : EReal)} := by
    ext x
    rw [Set.mem_singleton_iff, Set.mem_setOf_eq, P0_QX,
      show (fun y => (P0.g y : EReal)) = fun y => ((gd y : ℝ) : EReal) from rfl,
      eI_QX x gd gd_nonneg, P0_c, P0_beta, P0_g, EReal.coe_zero, EReal.coe_one, zero_add, one_mul,
      EReal.coe_le_coe_iff]
    by_cases hx : x = 0
    · subst hx; simp [nxt_zero, gd_zero]
    · rw [nxt_ne hx]
      constructor
      · intro h'; exact absurd h' hx
      · intro h'
        exfalso
        unfold gd at h'
        rw [pow_succ] at h'
        simp only [pow_zero, sub_self, add_zero] at h'
        linarith
  have hcl : ∀ x ∈ ({0} : Set ℕ), P0.QX x {0} = 1 := by
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    rw [P0_QX]
    simp [QXd, nxt_zero, ENNReal.inv_two_add_inv_two]
  exact not_opt ((h P0 Prd hPr hB {0} hS hcl).2.2 (fun x => hfin0 x))

theorem t_10_2_3_false : ¬ (∀ {E : Type} [MeasurableSpace E] (P : StationaryProblem E)
    (Pr : E → Measure (ℕ → E)) (hPr : P.IsPathLaw Pr) (hB : P.AssumptionB Pr),
    (∃ d : E → EReal,
      (∀ x : E, Tendsto (fun n => P.d n x) atTop (𝓝 (d x))) ∧
      ({x : E | 0 ≤ d x} = ⋂ n : ℕ, P.stopSet n) ∧
      ({x : E | 0 ≤ d x} = {x : E | P.Jlim x = (P.g x : EReal)}) ∧
      P.IsMaximizer {x : E | 0 ≤ d x} P.Jlim) ∧
    ((∀ x : E, P.T (P.Gf Pr {y : E | P.Jlim y = (P.g y : EReal)}) x ≤
        P.Gf Pr {y : E | P.Jlim y = (P.g y : EReal)} x) →
      (∀ x : E, Pr x {w | P.ruleTime {y : E | P.Jlim y = (P.g y : EReal)} w = ⊤} = 0) →
      P.IsOptimal Pr (P.ruleTime {y : E | P.Jlim y = (P.g y : EReal)}) ∧
        ∀ x : E, P.Gf Pr {y : E | P.Jlim y = (P.g y : EReal)} x =
          P.EReward Pr (P.ruleTime {y : E | P.Jlim y = (P.g y : EReal)}) x)) := by
  intro h
  have h2 := (h P0 Prd hPr hB).2
  rw [stopset_eq] at h2
  have hG : P0.Gf Prd ({0} : Set ℕ) = P0.Jlim := funext Gf_eq
  have hT : ∀ x : ℕ, P0.T (P0.Gf Prd ({0} : Set ℕ)) x ≤ P0.Gf Prd ({0} : Set ℕ) x := by
    intro x; rw [hG, TJ]
  exact not_opt (h2 hT (fun x => hfin0 x)).1

end OSDbl

open OSDbl in
theorem solution : ¬ (∀ {E : Type} [MeasurableSpace E] (P : StationaryProblem E)
    (Pr : E → Measure (ℕ → E)) (hPr : P.IsPathLaw Pr) (hB : P.AssumptionB Pr),
    (∃ d : E → EReal,
      (∀ x : E, Tendsto (fun n => P.d n x) atTop (𝓝 (d x))) ∧
      ({x : E | 0 ≤ d x} = ⋂ n : ℕ, P.stopSet n) ∧
      ({x : E | 0 ≤ d x} = {x : E | P.Jlim x = (P.g x : EReal)}) ∧
      P.IsMaximizer {x : E | 0 ≤ d x} P.Jlim) ∧
    ((∀ x : E, P.T (P.Gf Pr {y : E | P.Jlim y = (P.g y : EReal)}) x ≤
        P.Gf Pr {y : E | P.Jlim y = (P.g y : EReal)} x) →
      (∀ x : E, Pr x {w | P.ruleTime {y : E | P.Jlim y = (P.g y : EReal)} w = ⊤} = 0) →
      P.IsOptimal Pr (P.ruleTime {y : E | P.Jlim y = (P.g y : EReal)}) ∧
        ∀ x : E, P.Gf Pr {y : E | P.Jlim y = (P.g y : EReal)} x =
          P.EReward Pr (P.ruleTime {y : E | P.Jlim y = (P.g y : EReal)}) x)) :=
  OSDbl.t_10_2_3_false
