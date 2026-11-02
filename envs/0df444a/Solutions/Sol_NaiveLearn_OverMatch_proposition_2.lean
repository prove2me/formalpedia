-- Prove2me | solution 1 for NaiveLearn.OverMatch.proposition_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T13:44:13.248074+00:00
-- url     : https://prove2.me/submissions/9f822df9-ba50-4f9a-ab77-95869021f02c

import Mathlib
import Definitions.Def_NaiveLearn_OverMatch_Model

open MeasureTheory ProbabilityTheory Filter Topology
open NaiveLearn.OverMatch

namespace NL6

lemma actOf_cases (σ : ℝ → ℝ) (u : unitInterval) (y : ℝ) :
    actOf σ u y = 0 ∨ actOf σ u y = 1 := by
  unfold actOf; split_ifs <;> simp

lemma actOf_mem (σ : ℝ → ℝ) (u : unitInterval) (y : ℝ) :
    actOf σ u y ∈ Set.Icc (0 : ℝ) 1 := by
  rcases actOf_cases σ u y with h | h <;> rw [h] <;> simp

lemma bel_succ {m : ℕ} (σ : ℝ → ℝ) (ε : ℝ) (W : Matrix (Fin m) (Fin m) ℝ)
    (x1 : Fin m → ℝ) (U : Coins m) (t : ℕ) (i : Fin m) :
    beliefAct σ ε W x1 U (t + 1) i =
      (1 - ε) * beliefAct σ ε W x1 U t i +
        ε * ∑ j, W i j * actOf σ (U t j) (beliefAct σ ε W x1 U t j) := by
  simp [beliefAct, Matrix.mulVec, dotProduct]

lemma wsum_mem {m : ℕ} (W : Matrix (Fin m) (Fin m) ℝ) (hW : W ∈ Matrix.rowStochastic ℝ (Fin m))
    (a : Fin m → ℝ) (ha : ∀ j, a j ∈ Set.Icc (0 : ℝ) 1) (i : Fin m) :
    ∑ j, W i j * a j ∈ Set.Icc (0 : ℝ) 1 := by
  constructor
  · exact Finset.sum_nonneg fun j _ =>
      mul_nonneg (Matrix.nonneg_of_mem_rowStochastic hW) (ha j).1
  · calc ∑ j, W i j * a j ≤ ∑ j, W i j * 1 := Finset.sum_le_sum fun j _ =>
          mul_le_mul_of_nonneg_left (ha j).2 (Matrix.nonneg_of_mem_rowStochastic hW)
      _ = 1 := by simp [Matrix.sum_row_of_mem_rowStochastic hW]

lemma bel_mem {m : ℕ} (σ : ℝ → ℝ) (ε : ℝ) (hε : ε ∈ Set.Ioc (0 : ℝ) 1)
    (W : Matrix (Fin m) (Fin m) ℝ) (hW : W ∈ Matrix.rowStochastic ℝ (Fin m))
    (x1 : Fin m → ℝ) (hx1 : ∀ i, x1 i ∈ Set.Icc (0 : ℝ) 1) (U : Coins m) :
    ∀ t i, beliefAct σ ε W x1 U t i ∈ Set.Icc (0 : ℝ) 1 := by
  intro t
  induction t with
  | zero => exact hx1
  | succ t ih =>
    intro i
    rw [bel_succ]
    have h1 := ih i
    have h2 := wsum_mem W hW (fun j => actOf σ (U t j) (beliefAct σ ε W x1 U t j))
      (fun j => actOf_mem σ (U t j) _) i
    obtain ⟨hε0, hε1⟩ := hε
    constructor
    · nlinarith [h1.1, h2.1]
    · nlinarith [h1.2, h2.2]

lemma bel_congr_sigma {m : ℕ} (σ σ' : ℝ → ℝ) (hσ : ∀ y ∈ Set.Icc (0 : ℝ) 1, σ y = σ' y)
    (ε : ℝ) (hε : ε ∈ Set.Ioc (0 : ℝ) 1)
    (W : Matrix (Fin m) (Fin m) ℝ) (hW : W ∈ Matrix.rowStochastic ℝ (Fin m))
    (x1 : Fin m → ℝ) (hx1 : ∀ i, x1 i ∈ Set.Icc (0 : ℝ) 1) (U : Coins m) :
    ∀ t, beliefAct σ ε W x1 U t = beliefAct σ' ε W x1 U t := by
  intro t
  induction t with
  | zero => rfl
  | succ t ih =>
    have hm := bel_mem σ ε hε W hW x1 hx1 U t
    have hact : (fun j => actOf σ (U t j) (beliefAct σ ε W x1 U t j)) =
        (fun j => actOf σ' (U t j) (beliefAct σ' ε W x1 U t j)) := by
      funext j
      rw [← ih]
      unfold actOf
      rw [hσ _ (hm j)]
    simp only [beliefAct]
    rw [hact, ih]

lemma bel_restart {m : ℕ} (σ : ℝ → ℝ) (ε : ℝ) (W : Matrix (Fin m) (Fin m) ℝ)
    (x1 : Fin m → ℝ) (U : Coins m) (N : ℕ) :
    ∀ k, beliefAct σ ε W x1 U (N + k) =
      beliefAct σ ε W (beliefAct σ ε W x1 U N) (fun t => U (N + t)) k := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [← Nat.add_assoc]
    simp only [beliefAct]
    rw [ih]

lemma bel_prefix {m : ℕ} (σ : ℝ → ℝ) (ε : ℝ) (W : Matrix (Fin m) (Fin m) ℝ)
    (x1 : Fin m → ℝ) (U U' : Coins m) (N : ℕ) (h : ∀ t < N, U t = U' t) :
    ∀ k ≤ N, beliefAct σ ε W x1 U k = beliefAct σ ε W x1 U' k := by
  intro k
  induction k with
  | zero => intro _; rfl
  | succ k ih =>
    intro hk
    simp only [beliefAct]
    rw [ih (by omega), h k (by omega)]

lemma actOf_meas (σ : ℝ → ℝ) (hσ : Measurable σ) :
    Measurable (fun q : unitInterval × ℝ => actOf σ q.1 q.2) := by
  unfold actOf
  refine Measurable.ite ?_ measurable_const measurable_const
  exact measurableSet_lt (measurable_subtype_coe.comp measurable_fst) (hσ.comp measurable_snd)

lemma bel_meas {m : ℕ} (σ : ℝ → ℝ) (hσ : Measurable σ) (ε : ℝ) (W : Matrix (Fin m) (Fin m) ℝ)
    (t : ℕ) : Measurable (fun q : (Fin m → ℝ) × Coins m => beliefAct σ ε W q.1 q.2 t) := by
  induction t with
  | zero => exact measurable_fst
  | succ t ih =>
    simp only [beliefAct]
    have ha : Measurable (fun q : (Fin m → ℝ) × Coins m =>
        fun j => actOf σ (q.2 t j) (beliefAct σ ε W q.1 q.2 t j)) := by
      refine measurable_pi_lambda _ fun j => ?_
      exact (actOf_meas σ hσ).comp (Measurable.prodMk
        ((measurable_pi_apply j).comp ((measurable_pi_apply t).comp measurable_snd))
        ((measurable_pi_apply j).comp ih))
    exact (ih.const_smul (1 - ε)).add ((Continuous.measurable (by fun_prop :
      Continuous (fun v : Fin m → ℝ => ε • W.mulVec v))).comp ha)


lemma coupling_up {m : ℕ} (p : ℝ) (σ : ℝ → ℝ) (hσup : ∀ x ∈ Set.Ioc p 1, x ≤ σ x)
    (ε : ℝ) (hε : ε ∈ Set.Ioc (0 : ℝ) 1)
    (W : Matrix (Fin m) (Fin m) ℝ) (hW : W ∈ Matrix.rowStochastic ℝ (Fin m))
    (x0 y0 : Fin m → ℝ) (hx0 : ∀ i, x0 i ∈ Set.Icc (0 : ℝ) 1) (hxy : ∀ i, y0 i ≤ x0 i)
    (V : Coins m) (hy : ∀ t i, p < beliefAct id ε W y0 V t i) :
    ∀ t i, beliefAct id ε W y0 V t i ≤ beliefAct σ ε W x0 V t i := by
  intro t
  induction t with
  | zero => exact hxy
  | succ t ih =>
    intro i
    rw [bel_succ, bel_succ]
    have hxm := bel_mem σ ε hε W hW x0 hx0 V t
    have hact : ∀ j, actOf id (V t j) (beliefAct id ε W y0 V t j) ≤
        actOf σ (V t j) (beliefAct σ ε W x0 V t j) := by
      intro j
      have h1 := hy t j
      have h2 := ih j
      have h3 : beliefAct σ ε W x0 V t j ≤ σ (beliefAct σ ε W x0 V t j) :=
        hσup _ ⟨lt_of_lt_of_le h1 h2, (hxm j).2⟩
      unfold actOf
      split_ifs with ha hb hb
      · exact le_rfl
      · exfalso; apply hb; simp only [id] at ha; linarith
      · norm_num
      · exact le_rfl
    have hsum : ∑ j, W i j * actOf id (V t j) (beliefAct id ε W y0 V t j) ≤
        ∑ j, W i j * actOf σ (V t j) (beliefAct σ ε W x0 V t j) :=
      Finset.sum_le_sum fun j _ =>
        mul_le_mul_of_nonneg_left (hact j) (Matrix.nonneg_of_mem_rowStochastic hW)
    obtain ⟨hε0, hε1⟩ := hε
    have := ih i
    nlinarith

lemma coupling_down {m : ℕ} (p : ℝ) (σ : ℝ → ℝ) (hσdn : ∀ x ∈ Set.Ico 0 p, σ x ≤ x)
    (ε : ℝ) (hε : ε ∈ Set.Ioc (0 : ℝ) 1)
    (W : Matrix (Fin m) (Fin m) ℝ) (hW : W ∈ Matrix.rowStochastic ℝ (Fin m))
    (x0 y0 : Fin m → ℝ) (hx0 : ∀ i, x0 i ∈ Set.Icc (0 : ℝ) 1) (hxy : ∀ i, x0 i ≤ y0 i)
    (V : Coins m) (hy : ∀ t i, beliefAct id ε W y0 V t i < p) :
    ∀ t i, beliefAct σ ε W x0 V t i ≤ beliefAct id ε W y0 V t i := by
  intro t
  induction t with
  | zero => exact hxy
  | succ t ih =>
    intro i
    rw [bel_succ, bel_succ]
    have hxm := bel_mem σ ε hε W hW x0 hx0 V t
    have hact : ∀ j, actOf σ (V t j) (beliefAct σ ε W x0 V t j) ≤
        actOf id (V t j) (beliefAct id ε W y0 V t j) := by
      intro j
      have h1 := hy t j
      have h2 := ih j
      have h3 : σ (beliefAct σ ε W x0 V t j) ≤ beliefAct σ ε W x0 V t j :=
        hσdn _ ⟨(hxm j).1, lt_of_le_of_lt h2 h1⟩
      unfold actOf
      split_ifs with ha hb hb
      · exact le_rfl
      · exfalso; apply hb; simp only [id]; linarith
      · norm_num
      · exact le_rfl
    have hsum : ∑ j, W i j * actOf σ (V t j) (beliefAct σ ε W x0 V t j) ≤
        ∑ j, W i j * actOf id (V t j) (beliefAct id ε W y0 V t j) :=
      Finset.sum_le_sum fun j _ =>
        mul_le_mul_of_nonneg_left (hact j) (Matrix.nonneg_of_mem_rowStochastic hW)
    obtain ⟨hε0, hε1⟩ := hε
    have := ih i
    nlinarith

lemma sigma_up (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) (σ : ℝ → ℝ)
    (hcont : ContinuousOn σ (Set.Icc 0 1)) (hmaps : Set.MapsTo σ (Set.Icc 0 1) (Set.Icc 0 1))
    (hgt : ∀ x ∈ Set.Ioo p 1, x < σ x) : ∀ x ∈ Set.Ioc p 1, x ≤ σ x := by
  rintro x ⟨hx1, hx2⟩
  rcases lt_or_eq_of_le hx2 with h | h
  · exact (hgt x ⟨hx1, h⟩).le
  · subst h
    have hc : ContinuousWithinAt σ (Set.Ioo p 1) 1 :=
      (hcont.continuousWithinAt ⟨zero_le_one, le_rfl⟩).mono
        (Set.Ioo_subset_Icc_self.trans (Set.Icc_subset_Icc hp0.le le_rfl))
    have ht : Tendsto σ (𝓝[<] (1 : ℝ)) (𝓝 (σ 1)) := by
      rw [← nhdsWithin_Ioo_eq_nhdsLT hx1]; exact hc.tendsto
    have hev : ∀ᶠ y in 𝓝[<] (1 : ℝ), y ≤ σ y := by
      filter_upwards [Ioo_mem_nhdsLT hx1] with y hy using (hgt y hy).le
    exact le_of_tendsto_of_tendsto (tendsto_nhdsWithin_of_tendsto_nhds tendsto_id) ht hev

lemma sigma_dn (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) (σ : ℝ → ℝ)
    (hcont : ContinuousOn σ (Set.Icc 0 1)) (hmaps : Set.MapsTo σ (Set.Icc 0 1) (Set.Icc 0 1))
    (hlt : ∀ x ∈ Set.Ioo 0 p, σ x < x) : ∀ x ∈ Set.Ico 0 p, σ x ≤ x := by
  rintro x ⟨hx1, hx2⟩
  rcases lt_or_eq_of_le hx1 with h | h
  · exact (hlt x ⟨h, hx2⟩).le
  · subst h
    have hc : ContinuousWithinAt σ (Set.Ioo 0 p) 0 :=
      (hcont.continuousWithinAt ⟨le_rfl, zero_le_one⟩).mono
        (Set.Ioo_subset_Icc_self.trans (Set.Icc_subset_Icc le_rfl hp1.le))
    have ht : Tendsto σ (𝓝[>] (0 : ℝ)) (𝓝 (σ 0)) := by
      rw [← nhdsWithin_Ioo_eq_nhdsGT hx2]; exact hc.tendsto
    have hev : ∀ᶠ y in 𝓝[>] (0 : ℝ), σ y ≤ y := by
      filter_upwards [Ioo_mem_nhdsGT hx2] with y hy using (hlt y hy).le
    exact le_of_tendsto_of_tendsto ht (tendsto_nhdsWithin_of_tendsto_nhds tendsto_id) hev


/-- Concatenate a block of `N` coin vectors with a coin sequence. -/
def join {m : ℕ} (N : ℕ) (q : (Fin N → Fin m → unitInterval) × Coins m) : Coins m :=
  fun t => if h : t < N then q.1 ⟨t, h⟩ else q.2 (t - N)

/-- Split a coin sequence into its first `N` coin vectors and the shifted remainder. -/
def split {m : ℕ} (N : ℕ) (U : Coins m) : (Fin N → Fin m → unitInterval) × Coins m :=
  (fun k => U k, fun t => U (N + t))

lemma join_split {m : ℕ} (N : ℕ) (U : Coins m) : join N (split N U) = U := by
  funext t
  unfold join split
  split_ifs with h
  · rfl
  · simp only; congr 1; omega

lemma measurable_join {m : ℕ} (N : ℕ) : Measurable (join (m := m) N) := by
  refine measurable_pi_lambda _ fun t => ?_
  unfold join
  by_cases h : t < N
  · simp only [h, dif_pos]
    exact (measurable_pi_apply _).comp measurable_fst
  · simp only [h, dif_neg, not_false_eq_true]
    exact (measurable_pi_apply _).comp measurable_snd

lemma measurable_split {m : ℕ} (N : ℕ) : Measurable (split (m := m) N) := by
  unfold split
  exact Measurable.prodMk (measurable_pi_lambda _ fun k => measurable_pi_apply _)
    (measurable_pi_lambda _ fun t => measurable_pi_apply _)

/-- The law of the coin vector of one period. -/
noncomputable abbrev cv (m : ℕ) : Measure (Fin m → unitInterval) :=
  Measure.pi (fun _ : Fin m => (volume : Measure unitInterval))

lemma map_join {m : ℕ} (N : ℕ) :
    ((Measure.pi fun _ : Fin N => cv m).prod (coinLaw m)).map (join N) = coinLaw m := by
  classical
  unfold coinLaw
  apply Measure.eq_infinitePi
  intro s t ht
  have hinj : Set.InjOn (fun j : ℕ => N + j) ((fun j : ℕ => N + j) ⁻¹' ↑s) :=
    fun a _ b _ hab => by simpa using hab
  set box1 : Set (Fin N → Fin m → unitInterval) :=
    Set.univ.pi (fun k : Fin N => if (k : ℕ) ∈ s then t k else Set.univ)
  set box2 : Set (Coins m) := Set.pi ↑(s.preimage (fun j : ℕ => N + j) hinj)
    (fun j => t (N + j))
  have hpre : join N ⁻¹' (Set.pi ↑s t) = box1 ×ˢ box2 := by
    ext ⟨a, V⟩
    simp only [Set.mem_preimage, Set.mem_pi, Finset.mem_coe, Set.mem_prod, box1, box2,
      Set.mem_univ, true_implies, Finset.mem_preimage]
    constructor
    · intro h
      refine ⟨fun k => ?_, fun j hj => ?_⟩
      · split_ifs with hk
        · have := h k hk
          unfold join at this
          simpa [k.2] using this
        · trivial
      · have := h (N + j) hj
        unfold join at this
        simpa using this
    · rintro ⟨h1, h2⟩ i hi
      unfold join
      split_ifs with hiN
      · have := h1 ⟨i, hiN⟩
        simpa [hi] using this
      · have := h2 (i - N) (by rw [show N + (i - N) = i by omega]; exact hi)
        rw [show N + (i - N) = i by omega] at this
        exact this
  rw [Measure.map_apply (measurable_join N) (MeasurableSet.pi s.countable_toSet
    (fun i _ => ht i)), hpre, Measure.prod_prod, Measure.pi_pi,
    Measure.infinitePi_pi _ (fun i _ => ht _)]
  have e1 : ∏ k : Fin N, (cv m) (if (k : ℕ) ∈ s then t k else Set.univ) =
      ∏ i ∈ s with i < N, (cv m) (t i) := by
    have : ∀ k : Fin N, (cv m) (if (k : ℕ) ∈ s then t k else Set.univ) =
        (fun i : ℕ => if i ∈ s then (cv m) (t i) else 1) k := by
      intro k; by_cases hk : (k : ℕ) ∈ s <;> simp [hk]
    rw [Finset.prod_congr rfl (fun k _ => this k), Fin.prod_univ_eq_prod_range
      (fun i : ℕ => if i ∈ s then (cv m) (t i) else 1) N, ← Finset.prod_filter]
    apply Finset.prod_congr _ (fun _ _ => rfl)
    ext i; simp [and_comm]
  have e2 : ∏ j ∈ s.preimage (fun j : ℕ => N + j) hinj, (cv m) (t (N + j)) =
      ∏ i ∈ s with ¬ i < N, (cv m) (t i) := by
    rw [Finset.prod_preimage' (fun j : ℕ => N + j) s hinj (fun i => (cv m) (t i))]
    apply Finset.prod_congr _ (fun _ _ => rfl)
    ext i
    simp only [Finset.mem_filter, Set.mem_range, not_lt]
    constructor
    · rintro ⟨h1, j, rfl⟩; exact ⟨h1, by omega⟩
    · rintro ⟨h1, h2⟩; exact ⟨h1, i - N, by omega⟩
  rw [e1, e2, Finset.prod_filter_mul_prod_filter_not]

/-- Markov splitting of the coin law at time `N`. -/
lemma coinLaw_split {m : ℕ} (N : ℕ) (S : Set ((Fin N → Fin m → unitInterval) × Coins m))
    (hS : MeasurableSet S) :
    coinLaw m (split N ⁻¹' S) = ((Measure.pi fun _ : Fin N => cv m).prod (coinLaw m)) S := by
  conv_lhs => rw [← map_join N]
  rw [Measure.map_apply (measurable_join N) ((measurable_split N) hS)]
  congr 1
  ext ⟨a, V⟩
  simp only [Set.mem_preimage]
  have : split N (join N (a, V)) = (a, V) := by
    unfold split join
    ext k
    · simp [k.2]
    · simp
  rw [this]


instance coinLaw_prob (m : ℕ) : IsProbabilityMeasure (coinLaw m) := by
  unfold coinLaw; infer_instance

lemma bel_join_indep {m : ℕ} (σ : ℝ → ℝ) (ε : ℝ) (W : Matrix (Fin m) (Fin m) ℝ)
    (x1 : Fin m → ℝ) (N : ℕ) (a : Fin N → Fin m → unitInterval) (V V' : Coins m) :
    beliefAct σ ε W x1 (join N (a, V)) N = beliefAct σ ε W x1 (join N (a, V')) N := by
  apply bel_prefix σ ε W x1 _ _ N _ N le_rfl
  intro t ht
  unfold join
  simp [ht]

lemma int_act {r : ℝ} (hr : r ∈ Set.Icc (0 : ℝ) 1) :
    ∫ u : unitInterval, actOf id u r = r := by
  have h1 : (fun u : unitInterval => actOf id u r) =
      (Set.Iio (⟨r, hr⟩ : unitInterval)).indicator 1 := by
    funext u
    by_cases h : (u : ℝ) < r
    · have hu : u ∈ Set.Iio (⟨r, hr⟩ : unitInterval) := h
      rw [Set.indicator_of_mem hu]
      simp only [actOf, id_eq, if_pos h, Pi.one_apply]
    · have hu : u ∉ Set.Iio (⟨r, hr⟩ : unitInterval) := h
      rw [Set.indicator_of_notMem hu]
      simp only [actOf, id_eq, if_neg h]
  rw [h1, integral_indicator_one measurableSet_Iio, measureReal_def, unitInterval.volume_Iio]
  exact ENNReal.toReal_ofReal hr.1

lemma actOf_id_meas (r : ℝ) : Measurable (fun u : unitInterval => actOf id u r) :=
  (actOf_meas id measurable_id).comp (Measurable.prodMk measurable_id measurable_const)

lemma wsum_mem' {m : ℕ} (W : Matrix (Fin m) (Fin m) ℝ) (hW : W ∈ Matrix.rowStochastic ℝ (Fin m))
    (a : Fin m → ℝ) (ha : ∀ j, a j ∈ Set.Icc (0 : ℝ) 1) (i : Fin m) :
    ∑ j, W i j * a j ∈ Set.Icc (0 : ℝ) 1 := by
  constructor
  · exact Finset.sum_nonneg fun j _ =>
      mul_nonneg (Matrix.nonneg_of_mem_rowStochastic hW) (ha j).1
  · calc ∑ j, W i j * a j ≤ ∑ j, W i j * 1 := Finset.sum_le_sum fun j _ =>
          mul_le_mul_of_nonneg_left (ha j).2 (Matrix.nonneg_of_mem_rowStochastic hW)
      _ = 1 := by simp [Matrix.sum_row_of_mem_rowStochastic hW]

lemma field_mem {m : ℕ} (σ : ℝ → ℝ) (hmaps : Set.MapsTo σ (Set.Icc 0 1) (Set.Icc 0 1))
    (W : Matrix (Fin m) (Fin m) ℝ) (hW : W ∈ Matrix.rowStochastic ℝ (Fin m))
    (v : Fin m → ℝ) (i : Fin m) :
    W.mulVec (fun j => σ (Set.projIcc (0 : ℝ) 1 zero_le_one (v j))) i ∈ Set.Icc (0 : ℝ) 1 :=
  wsum_mem' W hW _ (fun j => hmaps (Set.projIcc (0 : ℝ) 1 zero_le_one (v j)).2) i

lemma coord_deriv {m : ℕ} (σ : ℝ → ℝ) (W : Matrix (Fin m) (Fin m) ℝ) (z : ℝ → (Fin m → ℝ))
    (hz : IsODESolution (meanField σ W) z) (t : ℝ) (ht : 0 ≤ t) (i : Fin m) :
    HasDerivWithinAt (fun s => z s i)
      (W.mulVec (fun j => σ (Set.projIcc (0 : ℝ) 1 zero_le_one (z t j))) i - z t i)
      (Set.Ici t) t :=
  hasDerivWithinAt_pi.1 (hz.2 t ht) i

/-- The cube is forward invariant. -/
lemma cube_inv {m : ℕ} (σ : ℝ → ℝ) (hmaps : Set.MapsTo σ (Set.Icc 0 1) (Set.Icc 0 1))
    (W : Matrix (Fin m) (Fin m) ℝ) (hW : W ∈ Matrix.rowStochastic ℝ (Fin m))
    (z : ℝ → (Fin m → ℝ)) (hz : IsODESolution (meanField σ W) z)
    (hz0 : ∀ i, z 0 i ∈ Set.Icc (0 : ℝ) 1) :
    ∀ t, 0 ≤ t → ∀ i, z t i ∈ Set.Icc (0 : ℝ) 1 := by
  intro t ht i
  have hc : ContinuousOn (fun s => z s i) (Set.Icc 0 t) :=
    ((continuous_apply i).comp_continuousOn hz.1).mono Set.Icc_subset_Ici_self
  constructor
  · have := le_gronwallBound_of_liminf_deriv_right_le (f := fun s => -z s i)
      (f' := fun s => -(W.mulVec (fun j => σ (Set.projIcc (0 : ℝ) 1 zero_le_one (z s j))) i
        - z s i)) (δ := -z 0 i) (K := -1) (ε := 0) (a := 0) (b := t) hc.neg
      (fun s hs r hr => ((coord_deriv σ W z hz s hs.1 i).neg).liminf_right_slope_le hr) le_rfl
      (fun s hs => by
        have := (field_mem σ hmaps W hW (z s) i).1
        linarith) t ⟨ht, le_rfl⟩
    rw [gronwallBound_ε0] at this
    have h0 := (hz0 i).1
    have : -z t i ≤ 0 := this.trans (by
      have := Real.exp_pos (-1 * (t - 0)); nlinarith)
    linarith
  · have := le_gronwallBound_of_liminf_deriv_right_le (f := fun s => z s i - 1)
      (f' := fun s => W.mulVec (fun j => σ (Set.projIcc (0 : ℝ) 1 zero_le_one (z s j))) i
        - z s i) (δ := z 0 i - 1) (K := -1) (ε := 0) (a := 0) (b := t) (hc.sub continuousOn_const)
      (fun s hs r hr => ((coord_deriv σ W z hz s hs.1 i).sub_const 1).liminf_right_slope_le hr)
      le_rfl
      (fun s hs => by
        have := (field_mem σ hmaps W hW (z s) i).2
        linarith) t ⟨ht, le_rfl⟩
    rw [gronwallBound_ε0] at this
    have h0 := (hz0 i).2
    have : z t i - 1 ≤ 0 := this.trans (by
      have := Real.exp_pos (-1 * (t - 0)); nlinarith)
    linarith



/-- One-step integration with the whole past. -/
lemma one_step_past {m : ℕ} (t : ℕ) (F : (Fin t → Fin m → unitInterval) × (Fin m → unitInterval) → ℝ)
    (hF : Measurable F) (C : ℝ) (hFb : ∀ q, ‖F q‖ ≤ C) :
    ∫ U, F ((split t U).1, U t) ∂coinLaw m =
      ∫ U, (∫ u, F ((split t U).1, u) ∂cv m) ∂coinLaw m := by
  set P := (Measure.pi fun _ : Fin t => cv m).prod (coinLaw m)
  have hjt : ∀ (a : Fin t → Fin m → unitInterval) (V : Coins m), join t (a, V) t = V 0 := by
    intro a V; unfold join; simp
  have hsj : ∀ (a : Fin t → Fin m → unitInterval) (V : Coins m), (split t (join t (a, V))).1 = a := by
    intro a V; unfold split join; funext k; simp [k.2]
  have hr : Measurable (fun U : Coins m => (split t U).1) := (measurable_split t).fst
  have hGm : StronglyMeasurable (fun a : Fin t → Fin m → unitInterval => ∫ u, F (a, u) ∂cv m) :=
    hF.stronglyMeasurable.integral_prod_right'
  have hGb : ∀ a, ‖∫ u, F (a, u) ∂cv m‖ ≤ C := by
    intro a
    calc ‖∫ u, F (a, u) ∂cv m‖ ≤ ∫ u, ‖F (a, u)‖ ∂cv m := norm_integral_le_integral_norm _
      _ ≤ ∫ _u, C ∂cv m := integral_mono_of_nonneg (Eventually.of_forall fun _ => norm_nonneg _)
          (integrable_const C) (Eventually.of_forall fun u => hFb _)
      _ = C := by simp
  have e1 : ∫ U, F ((split t U).1, U t) ∂coinLaw m =
      ∫ q, F ((split t (join t q)).1, join t q t) ∂P := by
    conv_lhs => rw [← map_join t]
    rw [integral_map (measurable_join t).aemeasurable]
    exact (hF.comp (Measurable.prodMk hr (measurable_pi_apply t))).aestronglyMeasurable
  have e2 : ∫ U, (∫ u, F ((split t U).1, u) ∂cv m) ∂coinLaw m =
      ∫ q, (∫ u, F ((split t (join t q)).1, u) ∂cv m) ∂P := by
    conv_lhs => rw [← map_join t]
    rw [integral_map (measurable_join t).aemeasurable]
    exact (hGm.comp_measurable hr).aestronglyMeasurable
  rw [e1, e2]
  have hq1 : ∀ q : (Fin t → Fin m → unitInterval) × Coins m,
      F ((split t (join t q)).1, join t q t) = F (q.1, q.2 0) := by
    rintro ⟨a, V⟩; rw [hsj, hjt]
  have hq2 : ∀ q : (Fin t → Fin m → unitInterval) × Coins m,
      ∫ u, F ((split t (join t q)).1, u) ∂cv m = ∫ u, F (q.1, u) ∂cv m := by
    rintro ⟨a, V⟩; rw [hsj]
  simp_rw [hq1, hq2]
  have hint1 : Integrable (fun q : (Fin t → Fin m → unitInterval) × Coins m => F (q.1, q.2 0)) P := by
    refine Integrable.of_bound ?_ C (Eventually.of_forall fun q => hFb _)
    exact (hF.comp (Measurable.prodMk measurable_fst
      ((measurable_pi_apply 0).comp measurable_snd))).aestronglyMeasurable
  have hint2 : Integrable (fun q : (Fin t → Fin m → unitInterval) × Coins m =>
      ∫ u, F (q.1, u) ∂cv m) P := by
    refine Integrable.of_bound ?_ C (Eventually.of_forall fun q => hGb _)
    exact (hGm.comp_measurable measurable_fst).aestronglyMeasurable
  rw [integral_prod _ hint1, integral_prod _ hint2]
  congr 1
  funext a
  show ∫ y, F (a, y 0) ∂coinLaw m = ∫ _y, (∫ u, F (a, u) ∂cv m) ∂coinLaw m
  rw [integral_const, probReal_univ, one_smul]
  have hmap : (coinLaw m).map (fun V : Coins m => V 0) = cv m := by
    unfold coinLaw; exact Measure.infinitePi_map_eval _ 0
  rw [← hmap, integral_map (measurable_pi_apply 0).aemeasurable]
  exact (hF.comp (Measurable.prodMk measurable_const measurable_id)).aestronglyMeasurable


/-- The noise of period `k` in coordinate `i`. -/
noncomputable def xi {m : ℕ} (σ : ℝ → ℝ) (ε : ℝ) (W : Matrix (Fin m) (Fin m) ℝ) (x1 : Fin m → ℝ)
    (k : ℕ) (i : Fin m) (U : Coins m) : ℝ :=
  ∑ j, W i j * (actOf σ (U k j) (beliefAct σ ε W x1 U k j) - σ (beliefAct σ ε W x1 U k j))

/-- The accumulated noise. -/
noncomputable def Ssum {m : ℕ} (σ : ℝ → ℝ) (ε : ℝ) (W : Matrix (Fin m) (Fin m) ℝ)
    (x1 : Fin m → ℝ) (n : ℕ) (i : Fin m) (U : Coins m) : ℝ :=
  ∑ k ∈ Finset.range n, xi σ ε W x1 k i U

lemma xi_bound {m : ℕ} (σ : ℝ → ℝ) (hmaps : Set.MapsTo σ (Set.Icc 0 1) (Set.Icc 0 1)) (ε : ℝ)
    (hε : ε ∈ Set.Ioc (0 : ℝ) 1) (W : Matrix (Fin m) (Fin m) ℝ)
    (hW : W ∈ Matrix.rowStochastic ℝ (Fin m)) (x1 : Fin m → ℝ)
    (hx1 : ∀ i, x1 i ∈ Set.Icc (0 : ℝ) 1) (k : ℕ) (i : Fin m) (U : Coins m) :
    |xi σ ε W x1 k i U| ≤ 1 := by
  have hb := bel_mem σ ε hε W hW x1 hx1 U k
  unfold xi
  calc |∑ j, W i j * (actOf σ (U k j) (beliefAct σ ε W x1 U k j) - σ (beliefAct σ ε W x1 U k j))|
      ≤ ∑ j, |W i j * (actOf σ (U k j) (beliefAct σ ε W x1 U k j) -
          σ (beliefAct σ ε W x1 U k j))| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j, W i j * 1 := Finset.sum_le_sum fun j _ => by
        rw [abs_mul, abs_of_nonneg (Matrix.nonneg_of_mem_rowStochastic hW)]
        apply mul_le_mul_of_nonneg_left _ (Matrix.nonneg_of_mem_rowStochastic hW)
        have h1 := actOf_mem σ (U k j) (beliefAct σ ε W x1 U k j)
        have h2 := hmaps (hb j)
        rw [abs_le]; constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
    _ = 1 := by simp [Matrix.sum_row_of_mem_rowStochastic hW]

lemma Ssum_prefix {m : ℕ} (σ : ℝ → ℝ) (ε : ℝ) (W : Matrix (Fin m) (Fin m) ℝ)
    (x1 : Fin m → ℝ) (n : ℕ) (i : Fin m) (U U' : Coins m) (h : ∀ t < n, U t = U' t) :
    Ssum σ ε W x1 n i U = Ssum σ ε W x1 n i U' := by
  unfold Ssum xi
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [Finset.mem_range] at hk
  rw [bel_prefix σ ε W x1 U U' n h k hk.le, h k hk]

lemma join_agree {m : ℕ} (n : ℕ) (U V : Coins m) :
    ∀ t < n, join n ((split n U).1, V) t = U t := by
  intro t ht; unfold join split; simp [ht]

lemma xi_meas {m : ℕ} (σ : ℝ → ℝ) (hσ : Measurable σ) (ε : ℝ) (W : Matrix (Fin m) (Fin m) ℝ)
    (x1 : Fin m → ℝ) (k : ℕ) (i : Fin m) : Measurable (xi σ ε W x1 k i) := by
  unfold xi
  refine Finset.measurable_sum _ fun j _ => measurable_const.mul ?_
  have hb : Measurable (fun U : Coins m => beliefAct σ ε W x1 U k j) :=
    (measurable_pi_apply j).comp ((bel_meas σ hσ ε W k).comp
      (Measurable.prodMk measurable_const measurable_id))
  exact ((actOf_meas σ hσ).comp (Measurable.prodMk
    ((measurable_pi_apply j).comp (measurable_pi_apply k)) hb)).sub (hσ.comp hb)

lemma Ssum_meas {m : ℕ} (σ : ℝ → ℝ) (hσ : Measurable σ) (ε : ℝ) (W : Matrix (Fin m) (Fin m) ℝ)
    (x1 : Fin m → ℝ) (n : ℕ) (i : Fin m) : Measurable (Ssum σ ε W x1 n i) := by
  unfold Ssum
  exact Finset.measurable_sum _ fun k _ => xi_meas σ hσ ε W x1 k i

/-- `Ssum n` as a function of the first `n` coins. -/
lemma Ssum_past {m : ℕ} (σ : ℝ → ℝ) (ε : ℝ) (W : Matrix (Fin m) (Fin m) ℝ)
    (x1 : Fin m → ℝ) (n : ℕ) (i : Fin m) (U : Coins m) :
    Ssum σ ε W x1 n i U = Ssum σ ε W x1 n i (join n ((split n U).1, fun _ _ => 0)) :=
  (Ssum_prefix σ ε W x1 n i _ _ (fun t ht => (join_agree n U _ t ht).symm))

lemma bel_past {m : ℕ} (σ : ℝ → ℝ) (ε : ℝ) (W : Matrix (Fin m) (Fin m) ℝ)
    (x1 : Fin m → ℝ) (n : ℕ) (U : Coins m) :
    beliefAct σ ε W x1 U n = beliefAct σ ε W x1 (join n ((split n U).1, fun _ _ => 0)) n :=
  bel_prefix σ ε W x1 _ _ n (fun t ht => (join_agree n U _ t ht).symm) n le_rfl

/-- The noise has conditional mean zero given the past. -/
lemma xi_zero_mean {m : ℕ} (σ : ℝ → ℝ) (hσ : Measurable σ)
    (hmaps : Set.MapsTo σ (Set.Icc 0 1) (Set.Icc 0 1)) (ε : ℝ)
    (hε : ε ∈ Set.Ioc (0 : ℝ) 1) (W : Matrix (Fin m) (Fin m) ℝ)
    (hW : W ∈ Matrix.rowStochastic ℝ (Fin m)) (x1 : Fin m → ℝ)
    (hx1 : ∀ i, x1 i ∈ Set.Icc (0 : ℝ) 1) (k : ℕ) (i : Fin m)
    (G : (Fin k → Fin m → unitInterval) → ℝ) (hG : Measurable G) (C : ℝ) (hGb : ∀ a, |G a| ≤ C) :
    ∫ U, G ((split k U).1) * xi σ ε W x1 k i U ∂coinLaw m = 0 := by
  set V0 : Coins m := fun _ _ => 0
  set Φ : (Fin k → Fin m → unitInterval) → (Fin m → ℝ) :=
    fun a => beliefAct σ ε W x1 (join k (a, V0)) k
  have hΦ : Measurable Φ := (bel_meas σ hσ ε W k).comp (Measurable.prodMk measurable_const
    ((measurable_join k).comp (Measurable.prodMk measurable_id measurable_const)))
  have hΦmem : ∀ a j, Φ a j ∈ Set.Icc (0 : ℝ) 1 := fun a j =>
    bel_mem σ ε hε W hW x1 hx1 _ k j
  set F : (Fin k → Fin m → unitInterval) × (Fin m → unitInterval) → ℝ :=
    fun q => G q.1 * ∑ j, W i j * (actOf σ (q.2 j) (Φ q.1 j) - σ (Φ q.1 j))
  have hFm : Measurable F := by
    refine (hG.comp measurable_fst).mul (Finset.measurable_sum _ fun j _ =>
      measurable_const.mul ?_)
    have hb : Measurable (fun q : (Fin k → Fin m → unitInterval) × (Fin m → unitInterval) =>
        Φ q.1 j) := (measurable_pi_apply j).comp (hΦ.comp measurable_fst)
    exact ((actOf_meas σ hσ).comp (Measurable.prodMk
      ((measurable_pi_apply j).comp measurable_snd) hb)).sub (hσ.comp hb)
  have hC : 0 ≤ C := le_trans (abs_nonneg _) (hGb (fun _ _ => 0))
  have hFb : ∀ q, ‖F q‖ ≤ C := by
    intro q
    rw [Real.norm_eq_abs]
    simp only [F, abs_mul]
    have hs : |∑ j, W i j * (actOf σ (q.2 j) (Φ q.1 j) - σ (Φ q.1 j))| ≤ 1 := by
      calc _ ≤ ∑ j, |W i j * (actOf σ (q.2 j) (Φ q.1 j) - σ (Φ q.1 j))| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ j, W i j * 1 := Finset.sum_le_sum fun j _ => by
            rw [abs_mul, abs_of_nonneg (Matrix.nonneg_of_mem_rowStochastic hW)]
            apply mul_le_mul_of_nonneg_left _ (Matrix.nonneg_of_mem_rowStochastic hW)
            have h1 := actOf_mem σ (q.2 j) (Φ q.1 j)
            have h2 := hmaps (hΦmem q.1 j)
            rw [abs_le]; constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
        _ = 1 := by simp [Matrix.sum_row_of_mem_rowStochastic hW]
    calc |G q.1| * _ ≤ C * 1 := mul_le_mul (hGb _) hs (abs_nonneg _) hC
      _ = C := mul_one C
  have hlhs : ∀ U, G ((split k U).1) * xi σ ε W x1 k i U = F ((split k U).1, U k) := by
    intro U
    simp only [F, Φ, xi]
    rw [← bel_past σ ε W x1 k U]
  simp_rw [hlhs]
  rw [one_step_past k F hFm C hFb]
  have hinner : ∀ a, ∫ u, F (a, u) ∂cv m = 0 := by
    intro a
    simp only [F]
    rw [integral_const_mul]
    rw [integral_finsetSum]
    · have : ∀ j, ∫ u, W i j * (actOf σ (u j) (Φ a j) - σ (Φ a j)) ∂cv m = 0 := by
        intro j
        rw [integral_const_mul]
        have hint : Integrable (fun u : Fin m → unitInterval => actOf σ (u j) (Φ a j)) (cv m) := by
          refine Integrable.of_bound ((actOf_id_meas _).comp
            (measurable_pi_apply j)).aestronglyMeasurable 1 (Eventually.of_forall fun u => ?_)
          have h1 := actOf_mem σ (u j) (Φ a j)
          rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith [h1.1, h1.2]
        rw [integral_sub hint (integrable_const _), integral_const, probReal_univ, one_smul]
        have : ∫ u, actOf σ (u j) (Φ a j) ∂cv m = σ (Φ a j) := by
          rw [integral_comp_eval (μ := fun _ : Fin m => (volume : Measure unitInterval))
            (f := fun v : unitInterval => actOf σ v (Φ a j))
            (actOf_id_meas _).aestronglyMeasurable]
          exact int_act (hmaps (hΦmem a j))
        rw [this, sub_self, mul_zero]
      simp_rw [this, Finset.sum_const_zero, mul_zero]
    · intro j _
      refine Integrable.const_mul ?_ _
      refine Integrable.of_bound (((actOf_id_meas _).comp
            (measurable_pi_apply j)).sub measurable_const).aestronglyMeasurable 1
            (Eventually.of_forall fun u => ?_)
      have h1 := actOf_mem σ (u j) (Φ a j)
      have h2 := hmaps (hΦmem a j)
      rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
  simp_rw [hinner, integral_zero]


lemma Ssum_bound {m : ℕ} (σ : ℝ → ℝ) (hmaps : Set.MapsTo σ (Set.Icc 0 1) (Set.Icc 0 1)) (ε : ℝ)
    (hε : ε ∈ Set.Ioc (0 : ℝ) 1) (W : Matrix (Fin m) (Fin m) ℝ)
    (hW : W ∈ Matrix.rowStochastic ℝ (Fin m)) (x1 : Fin m → ℝ)
    (hx1 : ∀ i, x1 i ∈ Set.Icc (0 : ℝ) 1) (n : ℕ) (i : Fin m) (U : Coins m) :
    |Ssum σ ε W x1 n i U| ≤ n := by
  unfold Ssum
  calc |∑ k ∈ Finset.range n, xi σ ε W x1 k i U| ≤ ∑ k ∈ Finset.range n, |xi σ ε W x1 k i U| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ Finset.range n, (1 : ℝ) := Finset.sum_le_sum fun k _ =>
        xi_bound σ hmaps ε hε W hW x1 hx1 k i U
    _ = n := by simp

lemma cross_zero {m : ℕ} (σ : ℝ → ℝ) (hσ : Measurable σ)
    (hmaps : Set.MapsTo σ (Set.Icc 0 1) (Set.Icc 0 1)) (ε : ℝ)
    (hε : ε ∈ Set.Ioc (0 : ℝ) 1) (W : Matrix (Fin m) (Fin m) ℝ)
    (hW : W ∈ Matrix.rowStochastic ℝ (Fin m)) (x1 : Fin m → ℝ)
    (hx1 : ∀ i, x1 i ∈ Set.Icc (0 : ℝ) 1) (n : ℕ) (i : Fin m)
    (B : Set (Fin n → Fin m → unitInterval)) (hB : MeasurableSet B) :
    ∫ U, B.indicator 1 ((split n U).1) * (Ssum σ ε W x1 n i U * xi σ ε W x1 n i U)
      ∂coinLaw m = 0 := by
  set V0 : Coins m := fun _ _ => 0
  set G : (Fin n → Fin m → unitInterval) → ℝ :=
    fun a => B.indicator 1 a * Ssum σ ε W x1 n i (join n (a, V0))
  have hG : Measurable G := (measurable_one.indicator hB).mul ((Ssum_meas σ hσ ε W x1 n i).comp
    ((measurable_join n).comp (Measurable.prodMk measurable_id measurable_const)))
  have hGb : ∀ a, |G a| ≤ n := by
    intro a
    simp only [G, abs_mul]
    have h1 : |B.indicator (1 : (Fin n → Fin m → unitInterval) → ℝ) a| ≤ 1 := by
      by_cases ha : a ∈ B <;> simp [ha]
    have h2 := Ssum_bound σ hmaps ε hε W hW x1 hx1 n i (join n (a, V0))
    calc _ ≤ 1 * (n : ℝ) := mul_le_mul h1 h2 (abs_nonneg _) zero_le_one
      _ = n := one_mul _
  have := xi_zero_mean σ hσ hmaps ε hε W hW x1 hx1 n i G hG n hGb
  rw [← this]
  congr 1
  funext U
  simp only [G]
  rw [← Ssum_past σ ε W x1 n i U]
  ring

lemma Ssum_succ {m : ℕ} (σ : ℝ → ℝ) (ε : ℝ) (W : Matrix (Fin m) (Fin m) ℝ)
    (x1 : Fin m → ℝ) (n : ℕ) (i : Fin m) (U : Coins m) :
    Ssum σ ε W x1 (n + 1) i U = Ssum σ ε W x1 n i U + xi σ ε W x1 n i U := by
  unfold Ssum; rw [Finset.sum_range_succ]

lemma sq_submart {m : ℕ} (σ : ℝ → ℝ) (hσ : Measurable σ)
    (hmaps : Set.MapsTo σ (Set.Icc 0 1) (Set.Icc 0 1)) (ε : ℝ)
    (hε : ε ∈ Set.Ioc (0 : ℝ) 1) (W : Matrix (Fin m) (Fin m) ℝ)
    (hW : W ∈ Matrix.rowStochastic ℝ (Fin m)) (x1 : Fin m → ℝ)
    (hx1 : ∀ i, x1 i ∈ Set.Icc (0 : ℝ) 1) (i : Fin m) :
    Submartingale (fun n U => (Ssum σ ε W x1 n i U) ^ 2) (coinFiltration m) (coinLaw m) := by
  have hint : ∀ n, Integrable (fun U => (Ssum σ ε W x1 n i U) ^ 2) (coinLaw m) := by
    intro n
    refine Integrable.of_bound ((Ssum_meas σ hσ ε W x1 n i).pow_const 2).aestronglyMeasurable
      ((n : ℝ) ^ 2) (Eventually.of_forall fun U => ?_)
    have := Ssum_bound σ hmaps ε hε W hW x1 hx1 n i U
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    nlinarith [abs_nonneg (Ssum σ ε W x1 n i U), sq_abs (Ssum σ ε W x1 n i U)]
  refine submartingale_of_setIntegral_le_succ ?_ hint ?_
  · intro n
    show StronglyMeasurable[coinFiltration m n] (fun U => (Ssum σ ε W x1 n i U) ^ 2)
    set V0 : Coins m := fun _ _ => 0
    have hfun : (fun U => (Ssum σ ε W x1 n i U) ^ 2) =
        (fun a => (Ssum σ ε W x1 n i (join n (a, V0))) ^ 2) ∘
          (fun (U : Coins m) (s : Fin n) => U s) := by
      funext U
      simp only [Function.comp]
      rw [Ssum_past σ ε W x1 n i U]
      rfl
    rw [hfun]
    refine Measurable.stronglyMeasurable ?_
    exact (((Ssum_meas σ hσ ε W x1 n i).comp ((measurable_join n).comp
      (Measurable.prodMk measurable_id measurable_const))).pow_const 2).comp
      (comap_measurable _)
  · intro n s hs
    obtain ⟨B, hB, rfl⟩ := hs
    have hI : ∀ g : Coins m → ℝ, ∫ U in (fun (U : Coins m) (s : Fin n) => U s) ⁻¹' B, g U
        ∂coinLaw m = ∫ U, B.indicator 1 ((split n U).1) * g U ∂coinLaw m := by
      intro g
      have hmS : MeasurableSet ((fun (U : Coins m) (s : Fin n) => U s) ⁻¹' B) :=
        hB.preimage (measurable_split n).fst
      rw [← integral_indicator hmS]
      congr 1
      funext U
      by_cases hU : (split n U).1 ∈ B
      · rw [Set.indicator_of_mem (show U ∈ (fun (U : Coins m) (s : Fin n) => U s) ⁻¹' B from hU),
          Set.indicator_of_mem hU]; simp
      · rw [Set.indicator_of_notMem (show U ∉ (fun (U : Coins m) (s : Fin n) => U s) ⁻¹' B
          from hU), Set.indicator_of_notMem hU]; simp
    rw [hI, hI]
    have hexp : ∀ U, B.indicator 1 ((split n U).1) * (Ssum σ ε W x1 (n + 1) i U) ^ 2 =
        B.indicator 1 ((split n U).1) * (Ssum σ ε W x1 n i U) ^ 2 +
        2 * (B.indicator 1 ((split n U).1) * (Ssum σ ε W x1 n i U * xi σ ε W x1 n i U)) +
        B.indicator 1 ((split n U).1) * (xi σ ε W x1 n i U) ^ 2 := by
      intro U; rw [Ssum_succ]; ring
    simp_rw [hexp]
    have hind : Measurable (fun U : Coins m => B.indicator (1 : (Fin n → Fin m → unitInterval) → ℝ)
        ((split n U).1)) := (measurable_one.indicator hB).comp (measurable_split n).fst
    have hib : ∀ U, |B.indicator (1 : (Fin n → Fin m → unitInterval) → ℝ) ((split n U).1)| ≤ 1 :=
      fun U => by by_cases hU : (split n U).1 ∈ B <;> simp [hU]
    have i1 : Integrable (fun U => B.indicator 1 ((split n U).1) * (Ssum σ ε W x1 n i U) ^ 2)
        (coinLaw m) := (hint n).bdd_mul hind.aestronglyMeasurable
          (Eventually.of_forall fun U => by rw [Real.norm_eq_abs]; exact hib U)
    have hxi : Integrable (fun U => xi σ ε W x1 n i U) (coinLaw m) :=
      Integrable.of_bound (xi_meas σ hσ ε W x1 n i).aestronglyMeasurable 1
        (Eventually.of_forall fun U => by
          rw [Real.norm_eq_abs]; exact xi_bound σ hmaps ε hε W hW x1 hx1 n i U)
    have hS : Integrable (fun U => Ssum σ ε W x1 n i U * xi σ ε W x1 n i U) (coinLaw m) := by
      refine hxi.bdd_mul (Ssum_meas σ hσ ε W x1 n i).aestronglyMeasurable
        (c := n) (Eventually.of_forall fun U => ?_)
      rw [Real.norm_eq_abs]; exact Ssum_bound σ hmaps ε hε W hW x1 hx1 n i U
    have i2 : Integrable (fun U => 2 * (B.indicator 1 ((split n U).1) *
        (Ssum σ ε W x1 n i U * xi σ ε W x1 n i U))) (coinLaw m) :=
      (hS.bdd_mul hind.aestronglyMeasurable
        (Eventually.of_forall fun U => by rw [Real.norm_eq_abs]; exact hib U)).const_mul 2
    have i3 : Integrable (fun U => B.indicator 1 ((split n U).1) * (xi σ ε W x1 n i U) ^ 2)
        (coinLaw m) := by
      refine Integrable.of_bound (hind.mul ((xi_meas σ hσ ε W x1 n i).pow_const 2)).aestronglyMeasurable
        1 (Eventually.of_forall fun U => ?_)
      have h1 := hib U
      have h2 := xi_bound σ hmaps ε hε W hW x1 hx1 n i U
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg (xi σ ε W x1 n i U))]
      have hx2 := sq_abs (xi σ ε W x1 n i U)
      have hx3 := abs_nonneg (xi σ ε W x1 n i U)
      have : (xi σ ε W x1 n i U) ^ 2 ≤ 1 := by nlinarith
      calc _ ≤ 1 * 1 := mul_le_mul h1 this (sq_nonneg _) zero_le_one
        _ = 1 := one_mul 1
    have i12 : Integrable (fun U => B.indicator 1 ((split n U).1) * (Ssum σ ε W x1 n i U) ^ 2 +
        2 * (B.indicator 1 ((split n U).1) * (Ssum σ ε W x1 n i U * xi σ ε W x1 n i U)))
        (coinLaw m) := i1.add i2
    rw [integral_add i12 i3, integral_add i1 i2, integral_const_mul,
      cross_zero σ hσ hmaps ε hε W hW x1 hx1 n i B hB, mul_zero, add_zero]
    have : 0 ≤ ∫ U, B.indicator 1 ((split n U).1) * (xi σ ε W x1 n i U) ^ 2 ∂coinLaw m := by
      refine integral_nonneg fun U => mul_nonneg ?_ (sq_nonneg _)
      by_cases hU : (split n U).1 ∈ B <;> simp [hU]
    linarith

lemma meanField_lip {m : ℕ} (σ : ℝ → ℝ) (K : NNReal) (hσlip : LipschitzOnWith K σ (Set.Icc 0 1))
    (W : Matrix (Fin m) (Fin m) ℝ) (hW : W ∈ Matrix.rowStochastic ℝ (Fin m)) :
    LipschitzWith (K + 1) (meanField σ W) := by
  apply LipschitzWith.of_dist_le_mul
  intro z z'
  have hd0 : 0 ≤ dist z z' := dist_nonneg
  have hc : ∀ j, |σ (Set.projIcc (0 : ℝ) 1 zero_le_one (z j)) -
      σ (Set.projIcc (0 : ℝ) 1 zero_le_one (z' j))| ≤ K * dist z z' := by
    intro j
    have h1 := hσlip.dist_le_mul _ (Set.projIcc (0 : ℝ) 1 zero_le_one (z j)).2 _
      (Set.projIcc (0 : ℝ) 1 zero_le_one (z' j)).2
    rw [Real.dist_eq, Real.dist_eq] at h1
    have h2 := Set.abs_projIcc_sub_projIcc (a := (0 : ℝ)) (b := 1) zero_le_one
      (c := z j) (d := z' j)
    have h3 : |z j - z' j| ≤ dist z z' := by
      rw [← Real.dist_eq]; exact dist_le_pi_dist z z' j
    calc _ ≤ (K : ℝ) * |(Set.projIcc (0 : ℝ) 1 zero_le_one (z j) : ℝ) -
          (Set.projIcc (0 : ℝ) 1 zero_le_one (z' j) : ℝ)| := h1
      _ ≤ K * dist z z' := by
          apply mul_le_mul_of_nonneg_left (h2.trans h3) K.2
  refine (dist_pi_le_iff (by positivity)).2 fun i => ?_
  simp only [meanField, Pi.sub_apply, Matrix.mulVec, dotProduct, Real.dist_eq]
  have hsum : |∑ j, W i j * σ (Set.projIcc (0 : ℝ) 1 zero_le_one (z j)) -
      ∑ j, W i j * σ (Set.projIcc (0 : ℝ) 1 zero_le_one (z' j))| ≤ K * dist z z' := by
    rw [← Finset.sum_sub_distrib]
    calc _ ≤ ∑ j, |W i j * σ (Set.projIcc (0 : ℝ) 1 zero_le_one (z j)) -
          W i j * σ (Set.projIcc (0 : ℝ) 1 zero_le_one (z' j))| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j, W i j * (K * dist z z') := by
          apply Finset.sum_le_sum; intro j _
          rw [← mul_sub, abs_mul, abs_of_nonneg (Matrix.nonneg_of_mem_rowStochastic hW)]
          exact mul_le_mul_of_nonneg_left (hc j) (Matrix.nonneg_of_mem_rowStochastic hW)
      _ = K * dist z z' := by
          rw [← Finset.sum_mul, Matrix.sum_row_of_mem_rowStochastic hW, one_mul]
  have hzi : |z i - z' i| ≤ dist z z' := by
    rw [← Real.dist_eq]; exact dist_le_pi_dist z z' i
  calc _ = |(∑ j, W i j * σ (Set.projIcc (0 : ℝ) 1 zero_le_one (z j)) -
        ∑ j, W i j * σ (Set.projIcc (0 : ℝ) 1 zero_le_one (z' j))) - (z i - z' i)| := by
        congr 1; ring
    _ ≤ _ := abs_sub _ _
    _ ≤ K * dist z z' + dist z z' := add_le_add hsum hzi
    _ = ((K + 1 : NNReal) : ℝ) * dist z z' := by push_cast; ring


lemma second_bound {m : ℕ} (σ : ℝ → ℝ) (hσ : Measurable σ)
    (hmaps : Set.MapsTo σ (Set.Icc 0 1) (Set.Icc 0 1)) (ε : ℝ)
    (hε : ε ∈ Set.Ioc (0 : ℝ) 1) (W : Matrix (Fin m) (Fin m) ℝ)
    (hW : W ∈ Matrix.rowStochastic ℝ (Fin m)) (x1 : Fin m → ℝ)
    (hx1 : ∀ i, x1 i ∈ Set.Icc (0 : ℝ) 1) (i : Fin m) :
    ∀ n : ℕ, ∫ U, (Ssum σ ε W x1 n i U) ^ 2 ∂coinLaw m ≤ n := by
  intro n
  induction n with
  | zero => simp [Ssum]
  | succ n ih =>
    have hxi : Integrable (fun U => xi σ ε W x1 n i U) (coinLaw m) :=
      Integrable.of_bound (xi_meas σ hσ ε W x1 n i).aestronglyMeasurable 1
        (Eventually.of_forall fun U => by
          rw [Real.norm_eq_abs]; exact xi_bound σ hmaps ε hε W hW x1 hx1 n i U)
    have hS2 : Integrable (fun U => (Ssum σ ε W x1 n i U) ^ 2) (coinLaw m) :=
      Integrable.of_bound ((Ssum_meas σ hσ ε W x1 n i).pow_const 2).aestronglyMeasurable
        ((n : ℝ) ^ 2) (Eventually.of_forall fun U => by
          have := Ssum_bound σ hmaps ε hε W hW x1 hx1 n i U
          rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
          nlinarith [abs_nonneg (Ssum σ ε W x1 n i U), sq_abs (Ssum σ ε W x1 n i U)])
    have hSx : Integrable (fun U => 2 * (Ssum σ ε W x1 n i U * xi σ ε W x1 n i U)) (coinLaw m) :=
      (hxi.bdd_mul (Ssum_meas σ hσ ε W x1 n i).aestronglyMeasurable (c := n)
        (Eventually.of_forall fun U => by
          rw [Real.norm_eq_abs]; exact Ssum_bound σ hmaps ε hε W hW x1 hx1 n i U)).const_mul 2
    have hx2 : Integrable (fun U => (xi σ ε W x1 n i U) ^ 2) (coinLaw m) :=
      Integrable.of_bound ((xi_meas σ hσ ε W x1 n i).pow_const 2).aestronglyMeasurable 1
        (Eventually.of_forall fun U => by
          have h := xi_bound σ hmaps ε hε W hW x1 hx1 n i U
          have h2 := sq_abs (xi σ ε W x1 n i U)
          have h3 := abs_nonneg (xi σ ε W x1 n i U)
          rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
          nlinarith)
    have hexp : ∀ U, (Ssum σ ε W x1 (n + 1) i U) ^ 2 = (Ssum σ ε W x1 n i U) ^ 2 +
        2 * (Ssum σ ε W x1 n i U * xi σ ε W x1 n i U) + (xi σ ε W x1 n i U) ^ 2 := by
      intro U; rw [Ssum_succ]; ring
    simp_rw [hexp]
    have h12 : Integrable (fun U => (Ssum σ ε W x1 n i U) ^ 2 +
        2 * (Ssum σ ε W x1 n i U * xi σ ε W x1 n i U)) (coinLaw m) := hS2.add hSx
    rw [integral_add h12 hx2, integral_add hS2 hSx, integral_const_mul]
    have hc := cross_zero σ hσ hmaps ε hε W hW x1 hx1 n i Set.univ MeasurableSet.univ
    simp only [Set.indicator_univ, Pi.one_apply, one_mul] at hc
    rw [hc, mul_zero, add_zero]
    have : ∫ U, (xi σ ε W x1 n i U) ^ 2 ∂coinLaw m ≤ 1 := by
      calc ∫ U, (xi σ ε W x1 n i U) ^ 2 ∂coinLaw m ≤ ∫ _U, (1 : ℝ) ∂coinLaw m :=
            integral_mono hx2 (integrable_const _) (fun U => by
              have h := xi_bound σ hmaps ε hε W hW x1 hx1 n i U
              have h2 := sq_abs (xi σ ε W x1 n i U)
              have h3 := abs_nonneg (xi σ ε W x1 n i U)
              show (xi σ ε W x1 n i U) ^ 2 ≤ 1
              nlinarith)
        _ = 1 := by simp
    push_cast
    linarith

lemma noise_max {m : ℕ} (σ : ℝ → ℝ) (hσ : Measurable σ)
    (hmaps : Set.MapsTo σ (Set.Icc 0 1) (Set.Icc 0 1)) (ε : ℝ)
    (hε : ε ∈ Set.Ioc (0 : ℝ) 1) (W : Matrix (Fin m) (Fin m) ℝ)
    (hW : W ∈ Matrix.rowStochastic ℝ (Fin m)) (x1 : Fin m → ℝ)
    (hx1 : ∀ i, x1 i ∈ Set.Icc (0 : ℝ) 1) (i : Fin m) (N : ℕ) (lam : ℝ) (hlam : 0 < lam) :
    coinLaw m {U | ∃ k ≤ N, lam ≤ |Ssum σ ε W x1 k i U|} ≤ ENNReal.ofReal (N / lam ^ 2) := by
  have hsub := sq_submart σ hσ hmaps ε hε W hW x1 hx1 i
  have hnn : 0 ≤ (fun n U => (Ssum σ ε W x1 n i U) ^ 2) := fun n U => sq_nonneg _
  set c : NNReal := Real.toNNReal (lam ^ 2)
  have hcr : (c : ℝ) = lam ^ 2 := Real.coe_toNNReal _ (sq_nonneg _)
  have hmax := maximal_ineq hsub hnn (ε := c) N
  have hincl : {U | ∃ k ≤ N, lam ≤ |Ssum σ ε W x1 k i U|} ⊆
      {U | (c : ℝ) ≤ (Finset.range (N + 1)).sup' Finset.nonempty_range_add_one
        fun k => (Ssum σ ε W x1 k i U) ^ 2} := by
    rintro U ⟨k, hk, hlk⟩
    simp only [Set.mem_setOf_eq, hcr]
    refine le_trans ?_ (Finset.le_sup' (fun k => (Ssum σ ε W x1 k i U) ^ 2)
      (Finset.mem_range.2 (Nat.lt_succ_of_le hk)))
    nlinarith [abs_nonneg (Ssum σ ε W x1 k i U), sq_abs (Ssum σ ε W x1 k i U)]
  have hint : ∫ U in {U | (c : ℝ) ≤ (Finset.range (N + 1)).sup' Finset.nonempty_range_add_one
        fun k => (Ssum σ ε W x1 k i U) ^ 2}, (Ssum σ ε W x1 N i U) ^ 2 ∂coinLaw m ≤ N :=
    (setIntegral_le_integral (hsub.integrable N) (Eventually.of_forall fun U => sq_nonneg _)).trans
      (second_bound σ hσ hmaps ε hε W hW x1 hx1 i N)
  have h1 := hmax.trans (ENNReal.ofReal_le_ofReal hint)
  have hc0 : (c : ENNReal) ≠ 0 :=
    ENNReal.coe_ne_zero.2 (Real.toNNReal_pos.2 (by positivity)).ne'
  calc coinLaw m {U | ∃ k ≤ N, lam ≤ |Ssum σ ε W x1 k i U|}
      ≤ coinLaw m {U | (c : ℝ) ≤ (Finset.range (N + 1)).sup' Finset.nonempty_range_add_one
        fun k => (Ssum σ ε W x1 k i U) ^ 2} := measure_mono hincl
    _ ≤ ENNReal.ofReal N / c := by
        rw [ENNReal.le_div_iff_mul_le (Or.inl hc0) (Or.inl ENNReal.coe_ne_top), mul_comm]
        exact h1
    _ = ENNReal.ofReal (N / lam ^ 2) := by
        show ENNReal.ofReal N / ENNReal.ofReal (lam ^ 2) = _
        rw [ENNReal.ofReal_div_of_pos (by positivity)]


lemma field_bound {m : ℕ} (σ : ℝ → ℝ) (hmaps : Set.MapsTo σ (Set.Icc 0 1) (Set.Icc 0 1))
    (W : Matrix (Fin m) (Fin m) ℝ) (hW : W ∈ Matrix.rowStochastic ℝ (Fin m)) (v : Fin m → ℝ)
    (hv : ∀ i, v i ∈ Set.Icc (0 : ℝ) 1) : ‖meanField σ W v‖ ≤ 1 := by
  refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun i => ?_
  have h1 := field_mem σ hmaps W hW v i
  have h2 := hv i
  simp only [meanField, Pi.sub_apply, Real.norm_eq_abs, abs_le]
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

lemma det_bound {m : ℕ} (σ : ℝ → ℝ) (hmaps : Set.MapsTo σ (Set.Icc 0 1) (Set.Icc 0 1))
    (K : NNReal) (hlip : LipschitzOnWith K σ (Set.Icc 0 1)) (W : Matrix (Fin m) (Fin m) ℝ)
    (hW : W ∈ Matrix.rowStochastic ℝ (Fin m)) (ε : ℝ) (hε : ε ∈ Set.Ioc (0 : ℝ) 1)
    (x1 : Fin m → ℝ) (hx1 : ∀ i, x1 i ∈ Set.Icc (0 : ℝ) 1) (z : ℝ → (Fin m → ℝ))
    (hz : IsODESolution (meanField σ W) z) (hz0 : z 0 = x1) (U : Coins m) (N : ℕ) (Λ : ℝ)
    (hΛ : 0 ≤ Λ) (hS : ∀ k ≤ N, ∀ i, ε * |Ssum σ ε W x1 k i U| ≤ Λ) :
    ∀ n ≤ N, ‖beliefAct σ ε W x1 U n - z (n * ε)‖ ≤ (1 + ε * (K + 1)) ^ n * (Λ + ε) := by
  obtain ⟨hε0, hε1⟩ := hε
  set L : ℝ := (K : ℝ) + 1 with hL
  have hL0 : 0 ≤ L := by positivity
  set f := meanField σ W
  have hfL : LipschitzWith (K + 1) f := meanField_lip σ K hlip W hW
  have hfL' : ∀ u v, ‖f u - f v‖ ≤ L * ‖u - v‖ := by
    intro u v
    have := hfL.dist_le_mul u v
    rw [dist_eq_norm, dist_eq_norm] at this
    simpa [hL] using this
  have hzc := cube_inv σ hmaps W hW z hz (by rw [hz0]; exact hx1)
  have hxc := bel_mem σ ε ⟨hε0, hε1⟩ W hW x1 hx1 U
  -- (D1) z is 1-Lipschitz on [0, ∞)
  have hD1 : ∀ a b, 0 ≤ a → a ≤ b → ‖z b - z a‖ ≤ b - a := by
    intro a b ha hab
    have := norm_image_sub_le_of_norm_deriv_right_le_segment (f := z)
      (f' := fun s => f (z s)) (C := 1) (a := a) (b := b)
      (hz.1.mono (Set.Icc_subset_Ici_self.trans (Set.Ici_subset_Ici.2 ha)))
      (fun s hs => hz.2 s (by linarith [hs.1]))
      (fun s hs => field_bound σ hmaps W hW _ (hzc s (by linarith [hs.1]))) b ⟨hab, le_rfl⟩
    linarith
  -- (D2) local truncation error
  have hD2 : ∀ a, 0 ≤ a → ‖z (a + ε) - z a - ε • f (z a)‖ ≤ L * ε ^ 2 := by
    intro a ha
    set g : ℝ → (Fin m → ℝ) := fun s => z s - (s - a) • f (z a)
    have hgc : ContinuousOn g (Set.Icc a (a + ε)) :=
      ((hz.1.mono (Set.Icc_subset_Ici_self.trans (Set.Ici_subset_Ici.2 ha))).sub
        ((continuous_id.sub continuous_const).smul continuous_const).continuousOn)
    have hgd : ∀ s ∈ Set.Ico a (a + ε), HasDerivWithinAt g (f (z s) - f (z a)) (Set.Ici s) s := by
      intro s hs
      have h1 := hz.2 s (by linarith [hs.1])
      have h2 : HasDerivWithinAt (fun s : ℝ => (s - a) • f (z a)) ((1 : ℝ) • f (z a))
          (Set.Ici s) s := ((hasDerivAt_id' s).sub_const a).smul_const (f (z a)) |>.hasDerivWithinAt
      rw [one_smul] at h2
      exact h1.sub h2
    have := norm_image_sub_le_of_norm_deriv_right_le_segment hgc hgd (C := L * ε)
      (fun s hs => by
        calc ‖f (z s) - f (z a)‖ ≤ L * ‖z s - z a‖ := hfL' _ _
          _ ≤ L * ε := by
              apply mul_le_mul_of_nonneg_left _ hL0
              have := hD1 a s ha hs.1
              linarith [hs.2]) (a + ε) ⟨by linarith, le_rfl⟩
    have heq : g (a + ε) - g a = z (a + ε) - z a - ε • f (z a) := by
      simp only [g, sub_self, zero_smul, sub_zero, add_sub_cancel_left]
      abel
    rw [heq] at this
    calc _ ≤ L * ε * (a + ε - a) := this
      _ = L * ε ^ 2 := by ring
  -- the noise vector
  set S : ℕ → Fin m → ℝ := fun n i => Ssum σ ε W x1 n i U
  set ξ : ℕ → Fin m → ℝ := fun n i => xi σ ε W x1 n i U
  set x : ℕ → Fin m → ℝ := fun n => beliefAct σ ε W x1 U n
  have hstep : ∀ n, x (n + 1) = x n + ε • f (x n) + ε • ξ n := by
    intro n
    funext i
    simp only [x, ξ, f, Pi.add_apply, Pi.smul_apply, smul_eq_mul, meanField, Pi.sub_apply,
      Matrix.mulVec, dotProduct, xi]
    rw [bel_succ]
    have hp : ∀ j, (Set.projIcc (0 : ℝ) 1 zero_le_one (beliefAct σ ε W x1 U n j) : ℝ) =
        beliefAct σ ε W x1 U n j := fun j => by
      simp [Set.projIcc_of_mem zero_le_one (hxc n j)]
    simp only [hp, mul_sub, Finset.sum_sub_distrib]
    ring
  have hSs : ∀ n, S (n + 1) = S n + ξ n := by
    intro n; funext i; simp only [S, ξ, Pi.add_apply]; exact Ssum_succ σ ε W x1 n i U
  have hSb : ∀ n ≤ N, ‖ε • S n‖ ≤ Λ := by
    intro n hn
    refine (pi_norm_le_iff_of_nonneg hΛ).2 fun i => ?_
    rw [Pi.smul_apply, smul_eq_mul, Real.norm_eq_abs, abs_mul, abs_of_pos hε0]
    exact hS n hn i
  set e : ℕ → Fin m → ℝ := fun n => x n - z (n * ε) - ε • S n
  have he0 : e 0 = 0 := by
    simp only [e, x, S, Nat.cast_zero, zero_mul, hz0]
    funext i
    simp [beliefAct, Ssum]
  have hrec : ∀ n, e (n + 1) = e n + ε • (f (x n) - f (z (n * ε))) -
      (z (n * ε + ε) - z (n * ε) - ε • f (z (n * ε))) := by
    intro n
    simp only [e]
    rw [hstep, hSs, show ((n + 1 : ℕ) : ℝ) * ε = n * ε + ε by push_cast; ring]
    simp only [smul_add, smul_sub]
    abel
  have hmain : ∀ n ≤ N, ‖e n‖ ≤ ((1 + ε * L) ^ n - 1) * (Λ + ε) := by
    intro n
    induction n with
    | zero => intro _; simp [he0]
    | succ n ih =>
      intro hn
      have ihn := ih (by omega)
      have hxz : ‖x n - z (n * ε)‖ ≤ ‖e n‖ + Λ := by
        have : x n - z (n * ε) = e n + ε • S n := by simp only [e]; abel
        rw [this]
        exact (norm_add_le _ _).trans (add_le_add le_rfl (hSb n (by omega)))
      have hnε : 0 ≤ (n : ℝ) * ε := by positivity
      rw [hrec]
      calc ‖e n + ε • (f (x n) - f (z (n * ε))) - (z (n * ε + ε) - z (n * ε) -
            ε • f (z (n * ε)))‖
          ≤ ‖e n‖ + ‖ε • (f (x n) - f (z (n * ε)))‖ + ‖z (n * ε + ε) - z (n * ε) -
            ε • f (z (n * ε))‖ := by
            refine (norm_sub_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
        _ ≤ ‖e n‖ + ε * (L * (‖e n‖ + Λ)) + L * ε ^ 2 := by
            refine add_le_add (add_le_add le_rfl ?_) (hD2 _ hnε)
            rw [norm_smul, Real.norm_eq_abs, abs_of_pos hε0]
            exact mul_le_mul_of_nonneg_left ((hfL' _ _).trans
              (mul_le_mul_of_nonneg_left hxz hL0)) hε0.le
        _ = (1 + ε * L) * ‖e n‖ + ε * L * (Λ + ε) := by ring
        _ ≤ (1 + ε * L) * (((1 + ε * L) ^ n - 1) * (Λ + ε)) + ε * L * (Λ + ε) := by
            gcongr
        _ = ((1 + ε * L) ^ (n + 1) - 1) * (Λ + ε) := by ring
  intro n hn
  have hxz : ‖x n - z (n * ε)‖ ≤ ‖e n‖ + Λ := by
    have : x n - z (n * ε) = e n + ε • S n := by simp only [e]; abel
    rw [this]
    exact (norm_add_le _ _).trans (add_le_add le_rfl (hSb n hn))
  have := hmain n hn
  have hpow : 1 ≤ (1 + ε * L) ^ n := one_le_pow₀ (by nlinarith)
  calc ‖beliefAct σ ε W x1 U n - z (n * ε)‖ = ‖x n - z (n * ε)‖ := rfl
    _ ≤ ((1 + ε * L) ^ n - 1) * (Λ + ε) + Λ := by linarith
    _ ≤ (1 + ε * L) ^ n * (Λ + ε) := by nlinarith


lemma sigc_meas (σ : ℝ → ℝ) (hc : ContinuousOn σ (Set.Icc 0 1)) :
    Measurable (fun y => σ (Set.projIcc (0 : ℝ) 1 zero_le_one y)) := by
  apply Continuous.measurable
  exact hc.comp_continuous (continuous_subtype_val.comp continuous_projIcc)
    (fun y => (Set.projIcc (0 : ℝ) 1 zero_le_one y).2)

lemma sigc_eq (σ : ℝ → ℝ) : ∀ y ∈ Set.Icc (0 : ℝ) 1,
    σ y = (fun y => σ (Set.projIcc (0 : ℝ) 1 zero_le_one y)) y := by
  intro y hy
  simp [Set.projIcc_of_mem zero_le_one hy]


lemma z_lip {m : ℕ} (σ : ℝ → ℝ) (hmaps : Set.MapsTo σ (Set.Icc 0 1) (Set.Icc 0 1))
    (W : Matrix (Fin m) (Fin m) ℝ) (hW : W ∈ Matrix.rowStochastic ℝ (Fin m))
    (z : ℝ → (Fin m → ℝ)) (hz : IsODESolution (meanField σ W) z)
    (hz0 : ∀ i, z 0 i ∈ Set.Icc (0 : ℝ) 1) :
    ∀ a b, 0 ≤ a → a ≤ b → ‖z b - z a‖ ≤ b - a := by
  have hzc := cube_inv σ hmaps W hW z hz hz0
  intro a b ha hab
  have := norm_image_sub_le_of_norm_deriv_right_le_segment (f := z)
    (f' := fun s => meanField σ W (z s)) (C := 1) (a := a) (b := b)
    (hz.1.mono (Set.Icc_subset_Ici_self.trans (Set.Ici_subset_Ici.2 ha)))
    (fun s hs => hz.2 s (by linarith [hs.1]))
    (fun s hs => field_bound σ hmaps W hW _ (hzc s (by linarith [hs.1]))) b ⟨hab, le_rfl⟩
  linarith

lemma Ssum_congr_sigma {m : ℕ} (σ σ' : ℝ → ℝ) (hσ : ∀ y ∈ Set.Icc (0 : ℝ) 1, σ y = σ' y)
    (ε : ℝ) (hε : ε ∈ Set.Ioc (0 : ℝ) 1)
    (W : Matrix (Fin m) (Fin m) ℝ) (hW : W ∈ Matrix.rowStochastic ℝ (Fin m))
    (x1 : Fin m → ℝ) (hx1 : ∀ i, x1 i ∈ Set.Icc (0 : ℝ) 1) (n : ℕ) (i : Fin m) (U : Coins m) :
    Ssum σ ε W x1 n i U = Ssum σ' ε W x1 n i U := by
  unfold Ssum xi
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => ?_
  have hb := bel_congr_sigma σ σ' hσ ε hε W hW x1 hx1 U k
  have hm := bel_mem σ ε hε W hW x1 hx1 U k j
  rw [← hb]
  unfold actOf
  rw [hσ _ hm]

end NL6

open NL6 in
theorem solution {m : ℕ} (σ : ℝ → ℝ) (hσmaps : Set.MapsTo σ (Set.Icc 0 1) (Set.Icc 0 1))
    (K : NNReal) (hσlip : LipschitzOnWith K σ (Set.Icc 0 1))
    (W : Matrix (Fin m) (Fin m) ℝ) (hW : IsWeightMatrix W) :
    ∀ T : ℝ, 0 < T → ∀ η : ℝ, 0 < η → ∀ γ : ℝ, 0 < γ →
      ∃ ε0 : ℝ, 0 < ε0 ∧ ∀ ε ∈ Set.Ioo (0 : ℝ) ε0, ∀ x1 : Fin m → ℝ,
        (∀ i, x1 i ∈ Set.Icc (0 : ℝ) 1) →
        ∀ z : ℝ → (Fin m → ℝ), IsODESolution (meanField σ W) z → z 0 = x1 →
          coinLaw m {U | ∃ t ∈ Set.Icc (0 : ℝ) T,
              η < ‖z t - beliefAct σ ε W x1 U ⌊t / ε⌋₊‖} ≤ ENNReal.ofReal γ := by
  intro T hT η hη γ hγ
  set L : ℝ := (K : ℝ) + 1 with hL
  have hL0 : 0 ≤ L := by positivity
  set C := Real.exp (L * T) with hC
  have hC1 : 1 ≤ C := Real.one_le_exp (by positivity)
  set Λ := η / (2 * C) with hΛ
  have hΛ0 : 0 < Λ := by positivity
  have hCΛ : C * Λ = η / 2 := by simp only [hΛ]; field_simp
  set ε0 := min 1 (min (η / (2 * (1 + C))) (γ * Λ ^ 2 / ((m + 1) * (T + 1)))) with hε0
  have hε0pos : 0 < ε0 := lt_min one_pos (lt_min (by positivity) (by positivity))
  refine ⟨ε0, hε0pos, ?_⟩
  intro ε hε x1 hx1 z hz hz0
  have hεpos : 0 < ε := hε.1
  have hε1 : ε ≤ 1 := (hε.2.le.trans (min_le_left _ _))
  have hεη : ε ≤ η / (2 * (1 + C)) := hε.2.le.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hεγ : ε ≤ γ * Λ ^ 2 / ((m + 1) * (T + 1)) :=
    hε.2.le.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hεI : ε ∈ Set.Ioc (0 : ℝ) 1 := ⟨hεpos, hε1⟩
  set N := ⌊T / ε⌋₊ with hN
  have hNε : (N : ℝ) * ε ≤ T := by
    have := Nat.floor_le (div_nonneg hT.le hεpos.le) (a := T / ε)
    rw [le_div_iff₀ hεpos] at this; exact this
  set σc : ℝ → ℝ := fun y => σ (Set.projIcc (0 : ℝ) 1 zero_le_one y) with hσc
  have hσcm : Measurable σc := sigc_meas σ hσlip.continuousOn
  have hσcmaps : Set.MapsTo σc (Set.Icc 0 1) (Set.Icc 0 1) := fun y _ =>
    hσmaps (Set.projIcc (0 : ℝ) 1 zero_le_one y).2
  set A : Fin m → Set (Coins m) := fun i =>
    {U | ∃ k ≤ N, Λ / ε ≤ |Ssum σc ε W x1 k i U|}
  have hsub : {U | ∃ t ∈ Set.Icc (0 : ℝ) T, η < ‖z t - beliefAct σ ε W x1 U ⌊t / ε⌋₊‖} ⊆
      ⋃ i, A i := by
    intro U hU
    by_contra hcon
    simp only [Set.mem_iUnion, not_exists, A, Set.mem_setOf_eq, not_exists, not_and,
      not_le] at hcon
    obtain ⟨t, ht, hbad⟩ := hU
    have hS : ∀ k ≤ N, ∀ i, ε * |Ssum σ ε W x1 k i U| ≤ Λ := by
      intro k hk i
      rw [Ssum_congr_sigma σ σc (sigc_eq σ) ε hεI W hW.1 x1 hx1 k i U]
      have := hcon i k hk
      rw [lt_div_iff₀ hεpos] at this
      linarith
    set n := ⌊t / ε⌋₊
    have hnN : n ≤ N := Nat.floor_le_floor (div_le_div_of_nonneg_right ht.2 hεpos.le)
    have hnt : (n : ℝ) * ε ≤ t := by
      have := Nat.floor_le (div_nonneg ht.1 hεpos.le) (a := t / ε)
      rw [le_div_iff₀ hεpos] at this; exact this
    have htn : t < (n : ℝ) * ε + ε := by
      have := Nat.lt_floor_add_one (t / ε)
      rw [div_lt_iff₀ hεpos] at this; linarith
    have hdet := det_bound σ hσmaps K hσlip W hW.1 ε hεI x1 hx1 z hz hz0 U N Λ hΛ0.le hS n hnN
    have hpow : (1 + ε * (K + 1)) ^ n ≤ C := by
      calc (1 + ε * (K + 1)) ^ n ≤ (Real.exp (ε * L)) ^ n := by
            apply pow_le_pow_left₀ (by positivity)
            calc 1 + ε * ((K : ℝ) + 1) = ε * L + 1 := by rw [hL]; ring
              _ ≤ Real.exp (ε * L) := Real.add_one_le_exp _
        _ = Real.exp (n * ε * L) := by rw [← Real.exp_nat_mul]; ring_nf
        _ ≤ C := by
            have hnT : (n : ℝ) * ε ≤ T :=
              le_trans (mul_le_mul_of_nonneg_right (Nat.cast_le.2 hnN) hεpos.le) hNε
            have := mul_le_mul_of_nonneg_right hnT hL0
            exact Real.exp_le_exp.2 (by linarith)
    have hzl := z_lip σ hσmaps W hW.1 z hz (by rw [hz0]; exact hx1) (n * ε) t
      (by positivity) hnt
    have : ‖z t - beliefAct σ ε W x1 U n‖ ≤ η := by
      calc ‖z t - beliefAct σ ε W x1 U n‖ ≤ ‖z t - z (n * ε)‖ +
            ‖beliefAct σ ε W x1 U n - z (n * ε)‖ := by
            rw [norm_sub_rev (beliefAct σ ε W x1 U n) (z (n * ε))]
            exact norm_sub_le_norm_sub_add_norm_sub _ _ _
        _ ≤ (t - n * ε) + C * (Λ + ε) := add_le_add hzl
            (hdet.trans (mul_le_mul_of_nonneg_right hpow (by positivity)))
        _ ≤ η := by
            have h1 : ε * (1 + C) ≤ η / 2 := by
              rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 2)]
              have := hεη; rw [le_div_iff₀ (by positivity)] at this; linarith
            nlinarith
    linarith
  calc coinLaw m _ ≤ coinLaw m (⋃ i, A i) := measure_mono hsub
    _ ≤ ∑ i, coinLaw m (A i) := measure_iUnion_fintype_le _ _
    _ ≤ ∑ _i : Fin m, ENNReal.ofReal (N / (Λ / ε) ^ 2) := Finset.sum_le_sum fun i _ =>
        noise_max σc hσcm hσcmaps ε hεI W hW.1 x1 hx1 i N (Λ / ε) (by positivity)
    _ = ENNReal.ofReal (m * (N / (Λ / ε) ^ 2)) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
          ENNReal.ofReal_mul (Nat.cast_nonneg m), ENNReal.ofReal_natCast]
    _ ≤ ENNReal.ofReal γ := by
        apply ENNReal.ofReal_le_ofReal
        have hN' : (N : ℝ) / (Λ / ε) ^ 2 = N * ε * ε / Λ ^ 2 := by field_simp
        rw [hN']
        have h1 : (N : ℝ) * ε * ε / Λ ^ 2 ≤ T * ε / Λ ^ 2 := by
          apply div_le_div_of_nonneg_right _ (by positivity)
          nlinarith
        have h2 : (m : ℝ) * (T * ε / Λ ^ 2) ≤ γ := by
          rw [le_div_iff₀ (by positivity)] at hεγ
          rw [mul_div_assoc', div_le_iff₀ (by positivity)]
          have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
          nlinarith
        calc (m : ℝ) * (N * ε * ε / Λ ^ 2) ≤ m * (T * ε / Λ ^ 2) :=
              mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg m)
          _ ≤ γ := h2
