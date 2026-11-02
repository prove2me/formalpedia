-- Prove2me | solution 1 for NaiveLearn.OverMatch.theorem_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T14:01:52.494235+00:00
-- url     : https://prove2.me/submissions/ba1ab561-4e42-44e3-af06-7323364f6713

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

/-- Markov lower bound with a past event. -/
lemma markov_bound_past {m : ℕ} (σ : ℝ → ℝ) (hσ : Measurable σ) (ε : ℝ)
    (W : Matrix (Fin m) (Fin m) ℝ) (x1 : Fin m → ℝ) (N : ℕ)
    (B : Set (Fin N → Fin m → unitInterval)) (hB : MeasurableSet B)
    (Good : Set (Fin m → ℝ)) (hGood : MeasurableSet Good)
    (A : Set ((Fin m → ℝ) × Coins m)) (hA : MeasurableSet A) (c : ENNReal)
    (hc : ∀ y ∈ Good, c ≤ coinLaw m {V | (y, V) ∈ A}) :
    c * coinLaw m {U | (split N U).1 ∈ B ∧ beliefAct σ ε W x1 U N ∈ Good} ≤
      coinLaw m {U | (split N U).1 ∈ B ∧ beliefAct σ ε W x1 U N ∈ Good ∧
        (beliefAct σ ε W x1 U N, fun t => U (N + t)) ∈ A} := by
  set g : Coins m → (Fin m → ℝ) := fun U => beliefAct σ ε W x1 U N with hg
  have hgm : Measurable g :=
    (bel_meas σ hσ ε W N).comp (Measurable.prodMk measurable_const measurable_id)
  set S : Set ((Fin N → Fin m → unitInterval) × Coins m) :=
    {q | q.1 ∈ B ∧ g (join N q) ∈ Good ∧ (g (join N q), q.2) ∈ A}
  have hgj : Measurable (fun q : (Fin N → Fin m → unitInterval) × Coins m => g (join N q)) :=
    hgm.comp (measurable_join N)
  have hSm : MeasurableSet S :=
    (measurable_fst hB).inter ((hgj hGood).inter (hA.preimage (Measurable.prodMk hgj measurable_snd)))
  set S' : Set ((Fin N → Fin m → unitInterval) × Coins m) := {q | q.1 ∈ B ∧ g (join N q) ∈ Good}
  have hS'm : MeasurableSet S' := (measurable_fst hB).inter (hgj hGood)
  have hsj : ∀ U : Coins m, (split N U).1 = (split N U).1 := fun _ => rfl
  have e1 : split N ⁻¹' S = {U | (split N U).1 ∈ B ∧ beliefAct σ ε W x1 U N ∈ Good ∧
        (beliefAct σ ε W x1 U N, fun t => U (N + t)) ∈ A} := by
    ext U; simp only [S, Set.mem_preimage, Set.mem_setOf_eq, join_split]; rfl
  have e2 : split N ⁻¹' S' = {U | (split N U).1 ∈ B ∧ beliefAct σ ε W x1 U N ∈ Good} := by
    ext U; simp only [S', Set.mem_preimage, Set.mem_setOf_eq, join_split]; rfl
  let V0 : Coins m := fun _ _ => 0
  set h : (Fin N → Fin m → unitInterval) → (Fin m → ℝ) := fun a => g (join N (a, V0))
  have hhm : Measurable h := hgj.comp (Measurable.prodMk measurable_id measurable_const)
  have hgh : ∀ a V, g (join N (a, V)) = h a := fun a V => bel_join_indep σ ε W x1 N a V V0
  rw [← e1, ← e2, coinLaw_split N S hSm, coinLaw_split N S' hS'm,
    Measure.prod_apply hSm, Measure.prod_apply hS'm]
  set T : Set (Fin N → Fin m → unitInterval) := B ∩ h ⁻¹' Good
  have hTm : MeasurableSet T := hB.inter (hhm hGood)
  have hsec' : ∀ a, coinLaw m (Prod.mk a ⁻¹' S') = T.indicator (fun _ => 1) a := by
    intro a
    by_cases ha : a ∈ T
    · rw [Set.indicator_of_mem ha]
      have : Prod.mk a ⁻¹' S' = Set.univ := by
        ext V; simp only [S', Set.mem_preimage, Set.mem_setOf_eq, hgh, Set.mem_univ, iff_true]
        exact ⟨ha.1, ha.2⟩
      rw [this, measure_univ]
    · rw [Set.indicator_of_notMem ha]
      have : Prod.mk a ⁻¹' S' = ∅ := by
        ext V; simp only [S', Set.mem_preimage, Set.mem_setOf_eq, hgh, Set.mem_empty_iff_false,
          iff_false, not_and]
        exact fun h1 h2 => ha ⟨h1, h2⟩
      rw [this, measure_empty]
  simp_rw [hsec']
  rw [lintegral_indicator_const hTm, one_mul, ← lintegral_indicator_const hTm]
  refine lintegral_mono fun a => ?_
  by_cases ha : a ∈ T
  · rw [Set.indicator_of_mem ha]
    refine (hc _ ha.2).trans (measure_mono fun V hV => ?_)
    simp only [Set.mem_setOf_eq] at hV
    simp only [S, Set.mem_preimage, Set.mem_setOf_eq, hgh]
    exact ⟨ha.1, ha.2, hV⟩
  · rw [Set.indicator_of_notMem ha]; exact bot_le


lemma filtration_sup (m : ℕ) :
    (MeasurableSpace.pi : MeasurableSpace (Coins m)) ≤ ⨆ n, coinFiltration m n := by
  refine iSup_le fun t => ?_
  refine le_trans ?_ (le_iSup (fun n => (coinFiltration m n : MeasurableSpace (Coins m))) (t + 1))
  show MeasurableSpace.comap (fun U : Coins m => U t) inferInstance ≤
    MeasurableSpace.comap (fun (U : Coins m) (s : Fin (t + 1)) => U s) inferInstance
  have hc : (fun U : Coins m => U t) =
      (fun v : Fin (t + 1) → Fin m → unitInterval => v ⟨t, Nat.lt_succ_self t⟩) ∘
        (fun (U : Coins m) (s : Fin (t + 1)) => U s) := rfl
  rw [hc, ← MeasurableSpace.comap_comp]
  exact MeasurableSpace.comap_mono (measurable_pi_apply _).comap_le

/-- A zero-one argument: if from the region `R n` the event `A` has conditional probability at
least `c`, and every path outside `A` visits the regions infinitely often, then `A` is almost
sure. -/
lemma levy_lower {m : ℕ} (A : Set (Coins m)) (hA : MeasurableSet A) (R : ℕ → Set (Coins m))
    (hR : ∀ n, MeasurableSet[coinFiltration m n] (R n)) (c : ℝ) (hc : 0 < c)
    (hlow : ∀ n, ∀ B, MeasurableSet[coinFiltration m n] B →
      ENNReal.ofReal c * coinLaw m (B ∩ R n) ≤ coinLaw m (A ∩ (B ∩ R n)))
    (hvisit : ∀ U, U ∉ A → ∀ N, ∃ n ≥ N, U ∈ R n) : coinLaw m Aᶜ = 0 := by
  set μ := coinLaw m
  set f : Coins m → ℝ := A.indicator (fun _ => 1)
  have hfi : Integrable f μ := (integrable_const (1 : ℝ)).indicator hA
  set g : ℕ → Coins m → ℝ := fun n => μ[f | coinFiltration m n]
  have hstep : ∀ n, ∀ᵐ U ∂μ, U ∈ R n → c ≤ g n U := by
    intro n
    have hle := (coinFiltration m).le n
    set f1 : Coins m → ℝ := (R n).indicator (fun _ => c)
    have hf1m : StronglyMeasurable[coinFiltration m n] f1 :=
      (stronglyMeasurable_const.indicator (hR n))
    have hgm : StronglyMeasurable[coinFiltration m n] (g n) := stronglyMeasurable_condExp
    have hf1i : Integrable f1 μ := (integrable_const c).indicator (hle _ (hR n))
    have hgi : Integrable (g n) μ := integrable_condExp
    have key : f1 ≤ᵐ[μ.trim hle] g n := by
      refine ae_le_of_forall_setIntegral_le (hf1i.trim hle hf1m) (hgi.trim hle hgm) ?_
      intro s hs _
      rw [← setIntegral_trim hle hf1m hs, ← setIntegral_trim hle hgm hs,
        setIntegral_condExp hle hfi hs]
      have e1 : ∫ x in s, f1 x ∂μ = c * μ.real (s ∩ R n) := by
        rw [integral_indicator (hle _ (hR n)), Measure.restrict_restrict (hle _ (hR n)),
          integral_const, smul_eq_mul, mul_comm, Measure.real, Measure.restrict_apply_univ,
          Set.inter_comm]
        rfl
      have e2 : ∫ x in s, f x ∂μ = μ.real (A ∩ s) := by
        rw [integral_indicator hA, Measure.restrict_restrict hA, integral_const, smul_eq_mul,
          mul_one, Measure.real, Measure.restrict_apply_univ]
        rfl
      rw [e1, e2]
      have h1 := hlow n s hs
      have h2 : μ (A ∩ (s ∩ R n)) ≤ μ (A ∩ s) :=
        measure_mono (Set.inter_subset_inter_right _ Set.inter_subset_left)
      have h3 := ENNReal.toReal_mono (measure_ne_top _ _) (h1.trans h2)
      rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hc.le] at h3
      exact h3
    filter_upwards [ae_le_of_ae_le_trim key] with U hU hUR
    have := hU
    simp only [f1, Set.indicator_of_mem hUR] at this
    exact this
  have hlevy : ∀ᵐ U ∂μ, Tendsto (fun n => g n U) atTop (𝓝 (f U)) :=
    hfi.tendsto_ae_condExp ((stronglyMeasurable_const.indicator hA).mono (filtration_sup m))
  have hae : ∀ᵐ U ∂μ, U ∈ A := by
    filter_upwards [hlevy, ae_all_iff.2 hstep] with U hU hst
    by_contra hUA
    have hf0 : f U = 0 := Set.indicator_of_notMem hUA _
    rw [hf0] at hU
    obtain ⟨N, hN⟩ := eventually_atTop.1 (hU.eventually (gt_mem_nhds hc))
    obtain ⟨n, hn, hnR⟩ := hvisit U hUA N
    have := hst n hnR
    linarith [hN n hn]
  exact ae_iff.1 hae


/-- Eventual agreement of the process started at `y` with coins `V`. -/
def Agr {m : ℕ} (σ : ℝ → ℝ) (ε : ℝ) (W : Matrix (Fin m) (Fin m) ℝ) (y : Fin m → ℝ)
    (V : Coins m) : Prop :=
  ∃ t0 : ℕ, ∃ a : ℝ, (a = 0 ∨ a = 1) ∧ ∀ t ≥ t0, ∀ i, action σ ε W y V t i = a

/-- Designated actions: before time `M`, play `1` iff the belief is at least `θ`; afterwards
always `1`. -/
noncomputable def dact {m : ℕ} (θ : ℝ) (M t : ℕ) (d : Fin m → ℝ) : Fin m → ℝ :=
  fun i => if t < M then (if θ ≤ d i then 1 else 0) else 1

/-- Designated beliefs. -/
noncomputable def Dseq {m : ℕ} (ε : ℝ) (W : Matrix (Fin m) (Fin m) ℝ) (θ : ℝ) (M : ℕ)
    (y : Fin m → ℝ) : ℕ → (Fin m → ℝ)
  | 0 => y
  | t + 1 => (1 - ε) • Dseq ε W θ M y t + ε • W.mulVec (dact θ M t (Dseq ε W θ M y t))

lemma dact_cases {m : ℕ} (θ : ℝ) (M t : ℕ) (d : Fin m → ℝ) (i : Fin m) :
    dact θ M t d i = 0 ∨ dact θ M t d i = 1 := by
  unfold dact; split_ifs <;> simp

lemma Dseq_succ {m : ℕ} (ε : ℝ) (W : Matrix (Fin m) (Fin m) ℝ) (θ : ℝ) (M : ℕ)
    (y : Fin m → ℝ) (t : ℕ) (i : Fin m) :
    Dseq ε W θ M y (t + 1) i = (1 - ε) * Dseq ε W θ M y t i +
      ε * ∑ j, W i j * dact θ M t (Dseq ε W θ M y t) j := by
  simp [Dseq, Matrix.mulVec, dotProduct]

lemma Dseq_mem {m : ℕ} (ε : ℝ) (hε : ε ∈ Set.Ioc (0 : ℝ) 1) (W : Matrix (Fin m) (Fin m) ℝ)
    (hW : W ∈ Matrix.rowStochastic ℝ (Fin m)) (θ : ℝ) (M : ℕ) (y : Fin m → ℝ)
    (hy : ∀ i, y i ∈ Set.Icc (0 : ℝ) 1) : ∀ t i, Dseq ε W θ M y t i ∈ Set.Icc (0 : ℝ) 1 := by
  intro t
  induction t with
  | zero => exact hy
  | succ t ih =>
    intro i
    rw [Dseq_succ]
    have h1 := ih i
    have h2 := wsum_mem' W hW (dact θ M t (Dseq ε W θ M y t)) (fun j => by
      rcases dact_cases θ M t (Dseq ε W θ M y t) j with h | h <;> rw [h] <;> simp) i
    obtain ⟨hε0, hε1⟩ := hε
    constructor <;> nlinarith [h1.1, h1.2, h2.1, h2.2]

lemma Dseq_keep {m : ℕ} (ε : ℝ) (hε : ε ∈ Set.Ioc (0 : ℝ) 1) (W : Matrix (Fin m) (Fin m) ℝ)
    (hW : W ∈ Matrix.rowStochastic ℝ (Fin m)) (θ : ℝ) (hθ : 0 ≤ θ)
    (hdiag : ∀ i, θ ≤ ε * W i i) (M : ℕ) (y : Fin m → ℝ)
    (hy : ∀ i, y i ∈ Set.Icc (0 : ℝ) 1) (t : ℕ) (i : Fin m)
    (h : θ ≤ Dseq ε W θ M y t i) : θ ≤ Dseq ε W θ M y (t + 1) i := by
  rw [Dseq_succ]
  have hai : dact θ M t (Dseq ε W θ M y t) i = 1 := by
    unfold dact; split_ifs <;> simp_all
  have hsum : W i i ≤ ∑ j, W i j * dact θ M t (Dseq ε W θ M y t) j := by
    have := Finset.single_le_sum (f := fun j => W i j * dact θ M t (Dseq ε W θ M y t) j)
      (fun j _ => mul_nonneg (Matrix.nonneg_of_mem_rowStochastic hW) (by
        rcases dact_cases θ M t (Dseq ε W θ M y t) j with h | h <;> rw [h] <;> simp))
      (Finset.mem_univ i)
    simp only [hai, mul_one] at this
    exact this
  obtain ⟨hε0, hε1⟩ := hε
  have := hdiag i
  nlinarith

lemma Dseq_spread {m : ℕ} (ε : ℝ) (hε : ε ∈ Set.Ioc (0 : ℝ) 1) (W : Matrix (Fin m) (Fin m) ℝ)
    (hW : W ∈ Matrix.rowStochastic ℝ (Fin m)) (θ : ℝ)
    (hpos : ∀ i j, 0 < W i j → θ ≤ ε * W i j) (M : ℕ) (y : Fin m → ℝ)
    (hy : ∀ i, y i ∈ Set.Icc (0 : ℝ) 1) (t : ℕ) (i j : Fin m) (hij : 0 < W i j)
    (h : θ ≤ Dseq ε W θ M y t j) : θ ≤ Dseq ε W θ M y (t + 1) i := by
  rw [Dseq_succ]
  have haj : dact θ M t (Dseq ε W θ M y t) j = 1 := by
    unfold dact; split_ifs <;> simp_all
  have hsum : W i j ≤ ∑ k, W i k * dact θ M t (Dseq ε W θ M y t) k := by
    have := Finset.single_le_sum (f := fun k => W i k * dact θ M t (Dseq ε W θ M y t) k)
      (fun k _ => mul_nonneg (Matrix.nonneg_of_mem_rowStochastic hW) (by
        rcases dact_cases θ M t (Dseq ε W θ M y t) k with h | h <;> rw [h] <;> simp))
      (Finset.mem_univ j)
    simp only [haj, mul_one] at this
    exact this
  have hm := (Dseq_mem ε hε W hW θ M y hy t i).1
  obtain ⟨hε0, hε1⟩ := hε
  have := hpos i j hij
  nlinarith


lemma Dseq_path {m : ℕ} (ε : ℝ) (hε : ε ∈ Set.Ioc (0 : ℝ) 1) (W : Matrix (Fin m) (Fin m) ℝ)
    (hW : W ∈ Matrix.rowStochastic ℝ (Fin m)) (θ : ℝ)
    (hpos : ∀ i j, 0 < W i j → θ ≤ ε * W i j) (M : ℕ) (y : Fin m → ℝ)
    (hy : ∀ i, y i ∈ Set.Icc (0 : ℝ) 1) :
    letI := Matrix.toQuiver W
    ∀ (i c : Fin m) (P : Quiver.Path i c) (t : ℕ), θ ≤ Dseq ε W θ M y t c →
      θ ≤ Dseq ε W θ M y (t + P.length) i := by
  letI := Matrix.toQuiver W
  intro i c P
  induction P with
  | nil => intro t h; simpa using h
  | cons P e ih =>
    intro t h
    have h1 := Dseq_spread ε hε W hW θ hpos M y hy t _ _ e.down h
    have h2 := ih (t + 1) h1
    rw [Quiver.Path.length_cons]
    rwa [show t + (P.length + 1) = t + 1 + P.length by omega]

lemma Dseq_all {m : ℕ} (ε : ℝ) (hε : ε ∈ Set.Ioc (0 : ℝ) 1) (W : Matrix (Fin m) (Fin m) ℝ)
    (hW : IsWeightMatrix W) (θ : ℝ) (hθ : 0 ≤ θ)
    (hpos : ∀ i j, 0 < W i j → θ ≤ ε * W i j) :
    ∃ M : ℕ, ∀ y : Fin m → ℝ, (∀ i, y i ∈ Set.Icc (0 : ℝ) 1) → (∃ j, θ ≤ y j) →
      ∀ i, θ ≤ Dseq ε W θ M y M i := by
  letI := Matrix.toQuiver W
  choose P _ using hW.2.1.connected
  refine ⟨∑ i, ∑ j, (P i j).length, ?_⟩
  intro y hy ⟨j0, hj0⟩ i
  set M := ∑ i, ∑ j, (P i j).length
  have hdiag : ∀ i, θ ≤ ε * W i i := fun i => hpos i i (hW.2.2 i)
  have hL : (P i j0).length ≤ M := by
    have h1 : (P i j0).length ≤ ∑ j, (P i j).length :=
      Finset.single_le_sum (f := fun j => (P i j).length) (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ j0)
    have h2 : ∑ j, (P i j).length ≤ M :=
      Finset.single_le_sum (f := fun i => ∑ j, (P i j).length) (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ i)
    omega
  have hreach := Dseq_path ε hε W hW.1 θ hpos M y hy i j0 (P i j0) 0 (by simpa [Dseq] using hj0)
  rw [zero_add] at hreach
  have := Nat.le_induction (m := (P i j0).length) (P := fun n _ => θ ≤ Dseq ε W θ M y n i)
    hreach (fun n _ ih => Dseq_keep ε hε W hW.1 θ hθ hdiag M y hy n i ih) M hL
  exact this

lemma Dseq_tail {m : ℕ} (ε : ℝ) (W : Matrix (Fin m) (Fin m) ℝ)
    (hW : W ∈ Matrix.rowStochastic ℝ (Fin m)) (θ : ℝ) (M : ℕ) (y : Fin m → ℝ) (i : Fin m) :
    ∀ s : ℕ, 1 - Dseq ε W θ M y (M + s) i = (1 - ε) ^ s * (1 - Dseq ε W θ M y M i) := by
  intro s
  induction s with
  | zero => simp
  | succ s ih =>
    rw [← add_assoc, Dseq_succ]
    have hall : ∀ j, dact θ M (M + s) (Dseq ε W θ M y (M + s)) j = 1 := by
      intro j; unfold dact; simp
    simp only [hall, mul_one, Matrix.sum_row_of_mem_rowStochastic hW]
    have key : ∀ x : ℝ, 1 - ((1 - ε) * x + ε) = (1 - ε) * (1 - x) := by intro x; ring
    rw [key, ih, pow_succ]
    ring

lemma bel_eq_Dseq {m : ℕ} (σ : ℝ → ℝ) (ε : ℝ) (W : Matrix (Fin m) (Fin m) ℝ) (θ : ℝ) (M : ℕ)
    (y : Fin m → ℝ) (V : Coins m)
    (hV : ∀ t i, actOf σ (V t i) (Dseq ε W θ M y t i) = dact θ M t (Dseq ε W θ M y t) i) :
    ∀ t, beliefAct σ ε W y V t = Dseq ε W θ M y t := by
  intro t
  induction t with
  | zero => rfl
  | succ t ih =>
    simp only [beliefAct, Dseq]
    rw [ih, show (fun j => actOf σ (V t j) (Dseq ε W θ M y t j)) =
      dact θ M t (Dseq ε W θ M y t) from funext (hV t)]

lemma agr_of_Dseq {m : ℕ} (σ : ℝ → ℝ) (ε : ℝ) (W : Matrix (Fin m) (Fin m) ℝ) (θ : ℝ) (M : ℕ)
    (y : Fin m → ℝ) (V : Coins m)
    (hV : ∀ t i, actOf σ (V t i) (Dseq ε W θ M y t i) = dact θ M t (Dseq ε W θ M y t) i) :
    Agr σ ε W y V := by
  refine ⟨M, 1, Or.inr rfl, fun t ht i => ?_⟩
  unfold action
  rw [bel_eq_Dseq σ ε W θ M y V hV t, hV t i]
  unfold dact
  simp [not_lt.2 ht]


/-- The probability factor of the designated action. -/
noncomputable def pfac {m : ℕ} (σ : ℝ → ℝ) (ε : ℝ) (W : Matrix (Fin m) (Fin m) ℝ) (θ : ℝ)
    (M : ℕ) (y : Fin m → ℝ) (t : ℕ) (i : Fin m) : ℝ :=
  if dact θ M t (Dseq ε W θ M y t) i = 1 then σ (Dseq ε W θ M y t i)
  else 1 - σ (Dseq ε W θ M y t i)

lemma prob_gen {m : ℕ} (σ : ℝ → ℝ) (hmaps : Set.MapsTo σ (Set.Icc 0 1) (Set.Icc 0 1))
    (D : ℕ → Fin m → ℝ) (hD : ∀ t i, D t i ∈ Set.Icc (0 : ℝ) 1) (act : ℕ → Fin m → ℝ)
    (hact : ∀ t i, act t i = 0 ∨ act t i = 1) (n : ℕ) :
    coinLaw m {V | ∀ t < n, ∀ i, actOf σ (V t i) (D t i) = act t i} =
      ∏ t ∈ Finset.range n, ∏ i, ENNReal.ofReal
        (if act t i = 1 then σ (D t i) else 1 - σ (D t i)) := by
  have hmem : ∀ t i, σ (D t i) ∈ Set.Icc (0 : ℝ) 1 := fun t i => hmaps (hD t i)
  set r : ℕ → Fin m → unitInterval := fun t i => ⟨σ (D t i), hmem t i⟩
  set I : ℕ → Fin m → Set unitInterval := fun t i =>
    if act t i = 1 then Set.Iio (r t i) else Set.Ici (r t i)
  have hI : ∀ t i, MeasurableSet (I t i) := by
    intro t i; simp only [I]; split_ifs
    · exact measurableSet_Iio
    · exact measurableSet_Ici
  have hiff : ∀ t i (u : unitInterval), actOf σ u (D t i) = act t i ↔ u ∈ I t i := by
    intro t i u
    simp only [I, actOf]
    rcases hact t i with h | h
    · rw [h]
      simp only [zero_ne_one, if_false, Set.mem_Ici]
      constructor
      · intro h1; by_contra h2; push Not at h2
        have : (u : ℝ) < σ (D t i) := h2
        rw [if_pos this] at h1; norm_num at h1
      · intro h1
        have : ¬ (u : ℝ) < σ (D t i) := not_lt.2 h1
        rw [if_neg this]
    · rw [h]
      simp only [if_true, Set.mem_Iio]
      constructor
      · intro h1; by_contra h2
        have : ¬ (u : ℝ) < σ (D t i) := h2
        rw [if_neg this] at h1; norm_num at h1
      · intro h1
        have : (u : ℝ) < σ (D t i) := h1
        rw [if_pos this]
  have hset : {V : Coins m | ∀ t < n, ∀ i, actOf σ (V t i) (D t i) = act t i} =
      Set.pi (↑(Finset.range n)) (fun t => Set.univ.pi (I t)) := by
    ext V
    simp only [Set.mem_setOf_eq, Set.mem_pi, Finset.coe_range, Set.mem_Iio, Set.mem_univ,
      true_implies, hiff]
  rw [hset]
  unfold coinLaw
  rw [Measure.infinitePi_pi _ (fun t _ => MeasurableSet.univ_pi (hI t))]
  refine Finset.prod_congr rfl fun t _ => ?_
  rw [Measure.pi_pi]
  refine Finset.prod_congr rfl fun i _ => ?_
  simp only [I]
  split_ifs
  · rw [unitInterval.volume_Iio]
  · rw [unitInterval.volume_Ici]

lemma meas_gen {m : ℕ} (σ : ℝ → ℝ) (D : ℕ → Fin m → ℝ) (act : ℕ → Fin m → ℝ) (n : ℕ) :
    MeasurableSet {V : Coins m | ∀ t < n, ∀ i, actOf σ (V t i) (D t i) = act t i} := by
  have : {V : Coins m | ∀ t < n, ∀ i, actOf σ (V t i) (D t i) = act t i} =
      ⋂ t ∈ Finset.range n, ⋂ i, (fun V : Coins m => V t i) ⁻¹'
        {u | actOf σ u (D t i) = act t i} := by
    ext V; simp
  rw [this]
  refine MeasurableSet.biInter (Finset.range n).countable_toSet fun t _ =>
    MeasurableSet.iInter fun i => ?_
  refine ((measurable_pi_apply i).comp (measurable_pi_apply t)) ?_
  have hm : Measurable (fun u : unitInterval => actOf σ u (D t i)) := by
    unfold actOf
    exact Measurable.ite (measurableSet_lt measurable_subtype_coe measurable_const)
      measurable_const measurable_const
  exact hm (measurableSet_singleton _)

lemma bel_eq_gen {m : ℕ} (σ : ℝ → ℝ) (ε : ℝ) (W : Matrix (Fin m) (Fin m) ℝ)
    (y : Fin m → ℝ) (D : ℕ → Fin m → ℝ) (act : ℕ → Fin m → ℝ) (hD0 : D 0 = y)
    (hrec : ∀ t, D (t + 1) = (1 - ε) • D t + ε • W.mulVec (act t)) (V : Coins m)
    (hV : ∀ t i, actOf σ (V t i) (D t i) = act t i) :
    ∀ t, beliefAct σ ε W y V t = D t := by
  intro t
  induction t with
  | zero => exact hD0.symm
  | succ t ih =>
    simp only [beliefAct]
    rw [ih, hrec t, show (fun j => actOf σ (V t j) (D t j)) = act t from funext (hV t)]

/-- Probability of an infinite designated path. -/
lemma prob_path {m : ℕ} (σ : ℝ → ℝ) (hmaps : Set.MapsTo σ (Set.Icc 0 1) (Set.Icc 0 1))
    (D : ℕ → Fin m → ℝ) (hD : ∀ t i, D t i ∈ Set.Icc (0 : ℝ) 1) (act : ℕ → Fin m → ℝ)
    (hact : ∀ t i, act t i = 0 ∨ act t i = 1) (c : ℝ)
    (hc : ∀ n, ENNReal.ofReal c ≤ ∏ t ∈ Finset.range n, ∏ i, ENNReal.ofReal
        (if act t i = 1 then σ (D t i) else 1 - σ (D t i))) :
    ENNReal.ofReal c ≤ coinLaw m {V | ∀ t i, actOf σ (V t i) (D t i) = act t i} := by
  set E : ℕ → Set (Coins m) := fun n => {V | ∀ t < n, ∀ i, actOf σ (V t i) (D t i) = act t i}
  have hanti : Antitone E := by
    intro n n' hnn' V hV t ht i
    exact hV t (by omega) i
  have hInter : (⋂ n, E n) = {V | ∀ t i, actOf σ (V t i) (D t i) = act t i} := by
    ext V
    simp only [Set.mem_iInter, Set.mem_setOf_eq, E]
    exact ⟨fun h t i => h (t + 1) t (by omega) i, fun h n t _ i => h t i⟩
  have hlim := tendsto_measure_iInter_atTop (μ := coinLaw m)
    (fun n => (meas_gen σ D act n).nullMeasurableSet) hanti ⟨0, measure_ne_top _ _⟩
  rw [hInter] at hlim
  refine ge_of_tendsto hlim (Eventually.of_forall fun n => ?_)
  show ENNReal.ofReal c ≤ coinLaw m (E n)
  rw [prob_gen σ hmaps D hD act hact n]
  exact hc n

lemma prod_one_sub_ge (a : ℕ → ℝ) (ha : ∀ s, 0 ≤ a s ∧ a s ≤ 1) :
    ∀ n, 1 - ∑ s ∈ Finset.range n, a s ≤ ∏ s ∈ Finset.range n, (1 - a s) := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, Finset.prod_range_succ]
    have hP : 0 ≤ ∏ s ∈ Finset.range n, (1 - a s) :=
      Finset.prod_nonneg fun s _ => by linarith [(ha s).2]
    have hS : 0 ≤ ∑ s ∈ Finset.range n, a s := Finset.sum_nonneg fun s _ => (ha s).1
    obtain ⟨h1, h2⟩ := ha n
    rcases le_total (1 - ∑ s ∈ Finset.range n, a s) 0 with h | h
    · nlinarith [mul_nonneg hP (by linarith : (0 : ℝ) ≤ 1 - a n)]
    · nlinarith [mul_le_mul_of_nonneg_right ih (by linarith : (0 : ℝ) ≤ 1 - a n)]

lemma real_lower {m : ℕ} (p : ℕ → Fin m → ℝ) (hp : ∀ t i, 0 ≤ p t i ∧ p t i ≤ 1)
    (q : ℝ) (hq : 0 < q) (L : ℕ) (hP1 : ∀ t < L, ∀ i, q ≤ p t i) (ε : ℝ)
    (hε : ε ∈ Set.Ioc (0 : ℝ) 1) (b : ℝ) (hb0 : 0 ≤ b) (hb : m * b ≤ ε / 2)
    (hP2 : ∀ s i, 1 - b * (1 - ε) ^ s ≤ p (L + s) i) :
    ∀ n, q ^ (m * L) / 2 ≤ ∏ t ∈ Finset.range n, ∏ i, p t i := by
  intro n
  obtain ⟨hε0, hε1⟩ := hε
  set f : ℕ → ℝ := fun t => ∏ i, p t i
  have hf : ∀ t, 0 ≤ f t ∧ f t ≤ 1 := fun t =>
    ⟨Finset.prod_nonneg fun i _ => (hp t i).1, Finset.prod_le_one (fun i _ => (hp t i).1)
      (fun i _ => (hp t i).2)⟩
  have hdrop : ∏ t ∈ Finset.range (L + n), f t ≤ ∏ t ∈ Finset.range n, f t := by
    rw [show L + n = n + L by omega, Finset.prod_range_add]
    have h1 : ∏ t ∈ Finset.range L, f (n + t) ≤ 1 :=
      Finset.prod_le_one (fun t _ => (hf _).1) (fun t _ => (hf _).2)
    have h0 : 0 ≤ ∏ t ∈ Finset.range n, f t := Finset.prod_nonneg fun t _ => (hf t).1
    nlinarith
  refine le_trans ?_ hdrop
  rw [Finset.prod_range_add]
  have hA : q ^ (m * L) ≤ ∏ t ∈ Finset.range L, f t := by
    have : q ^ (m * L) = ∏ _t ∈ Finset.range L, q ^ m := by
      rw [Finset.prod_const, Finset.card_range, ← pow_mul]
    rw [this]
    refine Finset.prod_le_prod (fun t _ => by positivity) fun t ht => ?_
    have : q ^ m = ∏ _i : Fin m, q := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    rw [this]
    exact Finset.prod_le_prod (fun i _ => hq.le) fun i _ =>
      hP1 t (Finset.mem_range.1 ht) i
  have hgeo : ∀ n, ε * ∑ s ∈ Finset.range n, (1 - ε) ^ s ≤ 1 := by
    intro n
    have h := geom_sum_mul (1 - ε) n
    have hp : 0 ≤ (1 - ε) ^ n := pow_nonneg (by linarith) n
    nlinarith
  have hB : 1 / 2 ≤ ∏ s ∈ Finset.range n, f (L + s) := by
    set a : ℕ → ℝ := fun s => m * b * (1 - ε) ^ s
    have hpow1 : ∀ s, (1 - ε) ^ s ≤ 1 := fun s => pow_le_one₀ (by linarith) (by linarith)
    have hpow0 : ∀ s, 0 ≤ (1 - ε) ^ s := fun s => pow_nonneg (by linarith) s
    have hmb : (m : ℝ) * b ≤ 1 / 2 := by linarith
    have hmb0 : 0 ≤ (m : ℝ) * b := by positivity
    have ha : ∀ s, 0 ≤ a s ∧ a s ≤ 1 := fun s =>
      ⟨mul_nonneg hmb0 (hpow0 s), by nlinarith [hpow1 s, hpow0 s]⟩
    have hfa : ∀ s, 1 - a s ≤ f (L + s) := by
      intro s
      rcases Nat.eq_zero_or_pos m with hm | hm
      · subst hm
        have : f (L + s) = 1 := by simp [f]
        rw [this]; linarith [(ha s).1]
      have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
      have hbs : b * (1 - ε) ^ s ≤ 1 / 2 := by
        have : b ≤ 1 / 2 := by nlinarith
        nlinarith [hpow1 s, hpow0 s]
      have h1 : (1 - b * (1 - ε) ^ s) ^ m ≤ f (L + s) := by
        have : (1 - b * (1 - ε) ^ s) ^ m = ∏ _i : Fin m, (1 - b * (1 - ε) ^ s) := by
          rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
        rw [this]
        exact Finset.prod_le_prod (fun i _ => by linarith) fun i _ => hP2 s i
      have h2 := one_add_mul_le_pow (a := -(b * (1 - ε) ^ s))
        (by nlinarith [hpow0 s]) m
      have h3 : 1 - a s = 1 + m * -(b * (1 - ε) ^ s) := by simp only [a]; ring
      rw [h3]
      calc 1 + m * -(b * (1 - ε) ^ s) ≤ (1 + -(b * (1 - ε) ^ s)) ^ m := h2
        _ = (1 - b * (1 - ε) ^ s) ^ m := by ring
        _ ≤ f (L + s) := h1
    calc (1 : ℝ) / 2 ≤ 1 - ∑ s ∈ Finset.range n, a s := by
          have : ∑ s ∈ Finset.range n, a s = m * b * ∑ s ∈ Finset.range n, (1 - ε) ^ s := by
            simp only [a, Finset.mul_sum]
          rw [this]
          have h1 := hgeo n
          have h2 : 0 ≤ ∑ s ∈ Finset.range n, (1 - ε) ^ s := Finset.sum_nonneg fun s _ => hpow0 s
          have h3 : (m : ℝ) * b * ∑ s ∈ Finset.range n, (1 - ε) ^ s ≤ 1 / 2 := by
            calc (m : ℝ) * b * ∑ s ∈ Finset.range n, (1 - ε) ^ s
                ≤ ε / 2 * ∑ s ∈ Finset.range n, (1 - ε) ^ s :=
                  mul_le_mul_of_nonneg_right hb h2
              _ = (ε * ∑ s ∈ Finset.range n, (1 - ε) ^ s) / 2 := by ring
              _ ≤ 1 / 2 := by linarith
          linarith
      _ ≤ ∏ s ∈ Finset.range n, (1 - a s) := prod_one_sub_ge a ha n
      _ ≤ ∏ s ∈ Finset.range n, f (L + s) :=
          Finset.prod_le_prod (fun s _ => by linarith [(ha s).2]) fun s _ => hfa s
  have hA0 : 0 ≤ q ^ (m * L) := by positivity
  calc q ^ (m * L) / 2 = q ^ (m * L) * (1 / 2) := by ring
    _ ≤ (∏ t ∈ Finset.range L, f t) * ∏ s ∈ Finset.range n, f (L + s) :=
        mul_le_mul hA hB (by norm_num) (le_trans hA0 hA)


lemma path_lower {m : ℕ} (σ : ℝ → ℝ) (hmaps : Set.MapsTo σ (Set.Icc 0 1) (Set.Icc 0 1))
    (ε : ℝ) (hε : ε ∈ Set.Ioc (0 : ℝ) 1) (W : Matrix (Fin m) (Fin m) ℝ) (hW : IsWeightMatrix W)
    (θ : ℝ) (hθ0 : 0 < θ) (hpos : ∀ i j, 0 < W i j → θ ≤ ε * W i j)
    (q : ℝ) (hq : 0 < q) (hq1 : ∀ x ∈ Set.Icc θ 1, q ≤ σ x)
    (hq0 : ∀ x ∈ Set.Icc 0 θ, q ≤ 1 - σ x)
    (C δ : ℝ) (hC0 : 0 ≤ C) (hδ0 : 0 < δ) (hCδ : m * (C * δ) ≤ ε / 2)
    (hder : ∀ x ∈ Set.Icc (1 - δ) 1, 1 - σ x ≤ C * (1 - x)) :
    ∃ M : ℕ, ∃ c : ℝ, 0 < c ∧ ∀ y : Fin m → ℝ, (∀ i, y i ∈ Set.Icc (0 : ℝ) 1) →
      (∃ j, θ ≤ y j) → ∀ n, ENNReal.ofReal c ≤ ∏ t ∈ Finset.range n, ∏ i, ENNReal.ofReal
        (if dact θ M t (Dseq ε W θ M y t) i = 1 then σ (Dseq ε W θ M y t i)
          else 1 - σ (Dseq ε W θ M y t i)) := by
  obtain ⟨M, hM⟩ := Dseq_all ε hε W hW θ hθ0.le hpos
  obtain ⟨hε0, hε1⟩ := hε
  obtain ⟨k, hk⟩ : ∃ k : ℕ, (1 - ε) ^ k ≤ δ := by
    obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one hδ0 (by linarith : 1 - ε < 1)
    exact ⟨k, hk.le⟩
  refine ⟨M, q ^ (m * (M + k)) / 2, by positivity, ?_⟩
  intro y hy hj n
  set D := Dseq ε W θ M y
  have hD := Dseq_mem ε ⟨hε0, hε1⟩ W hW.1 θ M y hy
  have hdiag : ∀ i, θ ≤ ε * W i i := fun i => hpos i i (hW.2.2 i)
  have hMall := hM y hy hj
  have hkeep : ∀ t, M ≤ t → ∀ i, θ ≤ D t i := by
    intro t ht i
    exact Nat.le_induction (m := M) (P := fun n _ => θ ≤ D n i) (hMall i)
      (fun n _ ih => Dseq_keep ε ⟨hε0, hε1⟩ W hW.1 θ hθ0.le hdiag M y hy n i ih) t ht
  set p : ℕ → Fin m → ℝ := fun t i =>
    if dact θ M t (D t) i = 1 then σ (D t i) else 1 - σ (D t i)
  have hp : ∀ t i, 0 ≤ p t i ∧ p t i ≤ 1 := by
    intro t i
    have := hmaps (hD t i)
    simp only [p]; split_ifs <;> constructor <;> linarith [this.1, this.2]
  have hP1 : ∀ t < M + k, ∀ i, q ≤ p t i := by
    intro t ht i
    simp only [p, dact]
    by_cases htM : t < M
    · simp only [htM, if_true]
      by_cases hθD : θ ≤ D t i
      · simp only [hθD, if_true]; exact hq1 _ ⟨hθD, (hD t i).2⟩
      · simp only [hθD, if_false, zero_ne_one]
        exact hq0 _ ⟨(hD t i).1, (lt_of_not_ge hθD).le⟩
    · simp only [htM, if_false, if_true]
      exact hq1 _ ⟨hkeep t (le_of_not_gt htM) i, (hD t i).2⟩
  have hP2 : ∀ s i, 1 - C * δ * (1 - ε) ^ s ≤ p (M + k + s) i := by
    intro s i
    simp only [p, dact, show ¬ (M + k + s < M) by omega, if_false, if_true]
    have htail := Dseq_tail ε W hW.1 θ M y i (k + s)
    rw [← add_assoc] at htail
    have h1 : 1 - D (M + k + s) i ≤ δ * (1 - ε) ^ s := by
      rw [htail, pow_add]
      have h2 := hD M i
      have h3 : 0 ≤ (1 - ε) ^ s := pow_nonneg (by linarith) s
      have h4 : 0 ≤ (1 - ε) ^ k := pow_nonneg (by linarith) k
      calc (1 - ε) ^ k * (1 - ε) ^ s * (1 - D M i) ≤ (1 - ε) ^ k * (1 - ε) ^ s * 1 :=
            mul_le_mul_of_nonneg_left (by linarith [h2.1]) (mul_nonneg h4 h3)
        _ ≤ δ * (1 - ε) ^ s := by nlinarith
    have h5 : (1 - ε) ^ s ≤ 1 := pow_le_one₀ (by linarith) (by linarith)
    have h6 : 0 ≤ (1 - ε) ^ s := pow_nonneg (by linarith) s
    have hmem : D (M + k + s) i ∈ Set.Icc (1 - δ) 1 :=
      ⟨by nlinarith, (hD _ i).2⟩
    have := hder _ hmem
    nlinarith
  have := real_lower p hp q hq (M + k) hP1 ε ⟨hε0, hε1⟩ (C * δ) (by positivity) hCδ
    (fun s i => by simpa [mul_assoc] using hP2 s i) n
  show ENNReal.ofReal (q ^ (m * (M + k)) / 2) ≤
    ∏ t ∈ Finset.range n, ∏ i, ENNReal.ofReal (p t i)
  calc ENNReal.ofReal (q ^ (m * (M + k)) / 2)
      ≤ ENNReal.ofReal (∏ t ∈ Finset.range n, ∏ i, p t i) := ENNReal.ofReal_le_ofReal this
    _ = ∏ t ∈ Finset.range n, ENNReal.ofReal (∏ i, p t i) :=
        ENNReal.ofReal_prod_of_nonneg (fun t _ => Finset.prod_nonneg fun i _ => (hp t i).1)
    _ = ∏ t ∈ Finset.range n, ∏ i, ENNReal.ofReal (p t i) :=
        Finset.prod_congr rfl fun t _ =>
          ENNReal.ofReal_prod_of_nonneg (fun i _ => (hp t i).1)


lemma uniform_agr1 {m : ℕ} (σ : ℝ → ℝ) (hmaps : Set.MapsTo σ (Set.Icc 0 1) (Set.Icc 0 1))
    (ε : ℝ) (hε : ε ∈ Set.Ioc (0 : ℝ) 1) (W : Matrix (Fin m) (Fin m) ℝ) (hW : IsWeightMatrix W)
    (θ : ℝ) (hθ0 : 0 < θ) (hpos : ∀ i j, 0 < W i j → θ ≤ ε * W i j)
    (q : ℝ) (hq : 0 < q) (hq1 : ∀ x ∈ Set.Icc θ 1, q ≤ σ x)
    (hq0 : ∀ x ∈ Set.Icc 0 θ, q ≤ 1 - σ x)
    (C δ : ℝ) (hC0 : 0 ≤ C) (hδ0 : 0 < δ) (hCδ : m * (C * δ) ≤ ε / 2)
    (hder : ∀ x ∈ Set.Icc (1 - δ) 1, 1 - σ x ≤ C * (1 - x)) :
    ∃ c : ℝ, 0 < c ∧ ∀ y : Fin m → ℝ, (∀ i, y i ∈ Set.Icc (0 : ℝ) 1) →
      (∃ j, θ ≤ y j) → ENNReal.ofReal c ≤ coinLaw m {V | Agr σ ε W y V} := by
  obtain ⟨M, c, hc, hlow⟩ := path_lower σ hmaps ε hε W hW θ hθ0 hpos q hq hq1 hq0 C δ hC0 hδ0
    hCδ hder
  refine ⟨c, hc, fun y hy hj => ?_⟩
  refine le_trans (prob_path σ hmaps (Dseq ε W θ M y) (Dseq_mem ε hε W hW.1 θ M y hy)
    (fun t => dact θ M t (Dseq ε W θ M y t)) (fun t i => dact_cases θ M t _ i) c
    (hlow y hy hj)) (measure_mono fun V hV => agr_of_Dseq σ ε W θ M y V hV)

lemma uniform_agr0 {m : ℕ} (σ : ℝ → ℝ) (hmaps : Set.MapsTo σ (Set.Icc 0 1) (Set.Icc 0 1))
    (ε : ℝ) (hε : ε ∈ Set.Ioc (0 : ℝ) 1) (W : Matrix (Fin m) (Fin m) ℝ) (hW : IsWeightMatrix W)
    (θ : ℝ) (hθ0 : 0 < θ) (hpos : ∀ i j, 0 < W i j → θ ≤ ε * W i j)
    (q : ℝ) (hq : 0 < q) (hq1 : ∀ x ∈ Set.Icc 0 (1 - θ), q ≤ 1 - σ x)
    (hq0 : ∀ x ∈ Set.Icc (1 - θ) 1, q ≤ σ x)
    (C δ : ℝ) (hC0 : 0 ≤ C) (hδ0 : 0 < δ) (hCδ : m * (C * δ) ≤ ε / 2)
    (hder : ∀ x ∈ Set.Icc 0 δ, σ x ≤ C * x) :
    ∃ c : ℝ, 0 < c ∧ ∀ y : Fin m → ℝ, (∀ i, y i ∈ Set.Icc (0 : ℝ) 1) →
      (∃ j, y j ≤ 1 - θ) → ENNReal.ofReal c ≤ coinLaw m {V | Agr σ ε W y V} := by
  set σ' : ℝ → ℝ := fun x => 1 - σ (1 - x)
  have hmaps' : Set.MapsTo σ' (Set.Icc 0 1) (Set.Icc 0 1) := by
    intro x hx
    have := hmaps (show 1 - x ∈ Set.Icc (0 : ℝ) 1 from ⟨by linarith [hx.2], by linarith [hx.1]⟩)
    exact ⟨by simp only [σ']; linarith [this.2], by simp only [σ']; linarith [this.1]⟩
  obtain ⟨M, c, hc, hlow⟩ := path_lower σ' hmaps' ε hε W hW θ hθ0 hpos q hq
    (fun x hx => by
      have := hq1 (1 - x) ⟨by linarith [hx.2], by linarith [hx.1]⟩
      simp only [σ']; linarith)
    (fun x hx => by
      have := hq0 (1 - x) ⟨by linarith [hx.2], by linarith [hx.1]⟩
      simp only [σ']; linarith) C δ hC0 hδ0 hCδ
    (fun x hx => by
      have := hder (1 - x) ⟨by linarith [hx.2], by linarith [hx.1]⟩
      simp only [σ']; linarith)
  refine ⟨c, hc, fun y hy hj => ?_⟩
  set y' : Fin m → ℝ := fun i => 1 - y i
  have hy' : ∀ i, y' i ∈ Set.Icc (0 : ℝ) 1 := fun i =>
    ⟨by simp only [y']; linarith [(hy i).2], by simp only [y']; linarith [(hy i).1]⟩
  have hj' : ∃ j, θ ≤ y' j := by
    obtain ⟨j, hj⟩ := hj; exact ⟨j, by simp only [y']; linarith⟩
  set D' := Dseq ε W θ M y'
  set D0 : ℕ → Fin m → ℝ := fun t i => 1 - D' t i
  set act0 : ℕ → Fin m → ℝ := fun t i => 1 - dact θ M t (D' t) i
  have hD' := Dseq_mem ε hε W hW.1 θ M y' hy'
  have hD0 : ∀ t i, D0 t i ∈ Set.Icc (0 : ℝ) 1 := fun t i =>
    ⟨by simp only [D0]; linarith [(hD' t i).2], by simp only [D0]; linarith [(hD' t i).1]⟩
  have hact0 : ∀ t i, act0 t i = 0 ∨ act0 t i = 1 := by
    intro t i
    rcases dact_cases θ M t (D' t) i with h | h <;> simp only [act0, h] <;> norm_num
  have hfac : ∀ t i, (if act0 t i = 1 then σ (D0 t i) else 1 - σ (D0 t i)) =
      (if dact θ M t (D' t) i = 1 then σ' (D' t i) else 1 - σ' (D' t i)) := by
    intro t i
    rcases dact_cases θ M t (D' t) i with h | h
    · simp only [act0, D0, σ', h, sub_zero, if_true]
      simp
    · simp only [act0, D0, σ', h, sub_self, zero_ne_one, if_false, if_true]
  have hprob := prob_path σ hmaps D0 hD0 act0 hact0 c (fun n => by
    simp_rw [hfac]; exact hlow y' hy' hj' n)
  refine le_trans hprob (measure_mono fun V hV => ?_)
  have hrec : ∀ t, D0 (t + 1) = (1 - ε) • D0 t + ε • W.mulVec (act0 t) := by
    intro t
    funext i
    simp only [D0, act0, D', Pi.add_apply, Pi.smul_apply, smul_eq_mul, Matrix.mulVec,
      dotProduct, mul_sub, mul_one, Finset.sum_sub_distrib,
      Matrix.sum_row_of_mem_rowStochastic hW.1]
    rw [Dseq_succ]
    ring
  have hbel := bel_eq_gen σ ε W y D0 act0 (by funext i; simp [D0, D', Dseq, y']) hrec V hV
  refine ⟨M, 0, Or.inl rfl, fun t ht i => ?_⟩
  unfold action
  rw [hbel t, hV t i]
  simp [act0, dact, not_lt.2 ht]

lemma sigc_meas (σ : ℝ → ℝ) (hc : ContinuousOn σ (Set.Icc 0 1)) :
    Measurable (fun y => σ (Set.projIcc (0 : ℝ) 1 zero_le_one y)) := by
  apply Continuous.measurable
  exact hc.comp_continuous (continuous_subtype_val.comp continuous_projIcc)
    (fun y => (Set.projIcc (0 : ℝ) 1 zero_le_one y).2)

lemma sigc_eq (σ : ℝ → ℝ) : ∀ y ∈ Set.Icc (0 : ℝ) 1,
    σ y = (fun y => σ (Set.projIcc (0 : ℝ) 1 zero_le_one y)) y := by
  intro y hy
  simp [Set.projIcc_of_mem zero_le_one hy]


lemma join_agree {m : ℕ} (n : ℕ) (U V : Coins m) :
    ∀ t < n, join n ((split n U).1, V) t = U t := by
  intro t ht; unfold join split; simp [ht]

lemma bel_past {m : ℕ} (σ : ℝ → ℝ) (ε : ℝ) (W : Matrix (Fin m) (Fin m) ℝ)
    (x1 : Fin m → ℝ) (n : ℕ) (U : Coins m) :
    beliefAct σ ε W x1 U n = beliefAct σ ε W x1 (join n ((split n U).1, fun _ _ => 0)) n :=
  bel_prefix σ ε W x1 _ _ n (fun t ht => (join_agree n U _ t ht).symm) n le_rfl


lemma agr_restart {m : ℕ} (σ : ℝ → ℝ) (ε : ℝ) (W : Matrix (Fin m) (Fin m) ℝ)
    (x1 : Fin m → ℝ) (U : Coins m) (N : ℕ)
    (h : Agr σ ε W (beliefAct σ ε W x1 U N) (fun t => U (N + t))) : Agr σ ε W x1 U := by
  obtain ⟨t0, a, ha, hall⟩ := h
  refine ⟨N + t0, a, ha, fun t ht i => ?_⟩
  obtain ⟨s, rfl⟩ := Nat.exists_eq_add_of_le (show N ≤ t by omega)
  have := hall s (by omega) i
  unfold action at this ⊢
  rw [bel_restart σ ε W x1 U N s]
  exact this

lemma agr_congr_sigma {m : ℕ} (σ σ' : ℝ → ℝ) (hσ : ∀ y ∈ Set.Icc (0 : ℝ) 1, σ y = σ' y)
    (ε : ℝ) (hε : ε ∈ Set.Ioc (0 : ℝ) 1) (W : Matrix (Fin m) (Fin m) ℝ)
    (hW : W ∈ Matrix.rowStochastic ℝ (Fin m)) (y : Fin m → ℝ)
    (hy : ∀ i, y i ∈ Set.Icc (0 : ℝ) 1) (V : Coins m) :
    Agr σ ε W y V ↔ Agr σ' ε W y V := by
  have hact : ∀ t i, action σ ε W y V t i = action σ' ε W y V t i := by
    intro t i
    unfold action
    rw [← bel_congr_sigma σ σ' hσ ε hε W hW y hy V t]
    unfold actOf
    rw [hσ _ (bel_mem σ ε hε W hW y hy V t i)]
  unfold Agr
  simp only [hact]

lemma meas_agr_joint {m : ℕ} (σ : ℝ → ℝ) (hσ : Measurable σ) (ε : ℝ)
    (W : Matrix (Fin m) (Fin m) ℝ) :
    MeasurableSet {q : (Fin m → ℝ) × Coins m | Agr σ ε W q.1 q.2} := by
  have hact : ∀ t i, Measurable (fun q : (Fin m → ℝ) × Coins m => action σ ε W q.1 q.2 t i) := by
    intro t i
    unfold action
    exact (actOf_meas σ hσ).comp (Measurable.prodMk
      ((measurable_pi_apply i).comp ((measurable_pi_apply t).comp measurable_snd))
      ((measurable_pi_apply i).comp (bel_meas σ hσ ε W t)))
  have e : {q : (Fin m → ℝ) × Coins m | Agr σ ε W q.1 q.2} =
      ⋃ t0 : ℕ, ((⋂ t ∈ Set.Ici t0, ⋂ i, {q | action σ ε W q.1 q.2 t i = 0}) ∪
        (⋂ t ∈ Set.Ici t0, ⋂ i, {q | action σ ε W q.1 q.2 t i = 1})) := by
    ext q
    simp only [Agr, Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_union, Set.mem_iInter,
      Set.mem_Ici]
    constructor
    · rintro ⟨t0, a, ha, h⟩
      refine ⟨t0, ?_⟩
      rcases ha with rfl | rfl
      · exact Or.inl h
      · exact Or.inr h
    · rintro ⟨t0, h | h⟩
      · exact ⟨t0, 0, Or.inl rfl, h⟩
      · exact ⟨t0, 1, Or.inr rfl, h⟩
  rw [e]
  exact MeasurableSet.iUnion fun t0 => MeasurableSet.union
    (MeasurableSet.biInter (Set.to_countable _) fun t _ => MeasurableSet.iInter fun i =>
      hact t i (measurableSet_singleton 0))
    (MeasurableSet.biInter (Set.to_countable _) fun t _ => MeasurableSet.iInter fun i =>
      hact t i (measurableSet_singleton 1))


lemma agreement_main {m : ℕ} (σ : ℝ → ℝ) (hmaps : Set.MapsTo σ (Set.Icc 0 1) (Set.Icc 0 1))
    (hcont : ContinuousOn σ (Set.Icc 0 1)) (ε : ℝ) (hε : ε ∈ Set.Ioc (0 : ℝ) 1)
    (W : Matrix (Fin m) (Fin m) ℝ) (hW : W ∈ Matrix.rowStochastic ℝ (Fin m))
    (x1 : Fin m → ℝ) (hx1 : ∀ i, x1 i ∈ Set.Icc (0 : ℝ) 1)
    (Good : Set (Fin m → ℝ)) (hGood : MeasurableSet Good)
    (hGc : ∀ y ∈ Good, ∀ i, y i ∈ Set.Icc (0 : ℝ) 1)
    (c : ℝ) (hc0 : 0 < c) (hc : ∀ y ∈ Good, ENNReal.ofReal c ≤ coinLaw m {V | Agr σ ε W y V})
    (hvis : ∀ U, ¬ Agr σ ε W x1 U → ∀ N, ∃ n ≥ N, beliefAct σ ε W x1 U n ∈ Good) :
    EventualAgreement σ ε W x1 := by
  set σc : ℝ → ℝ := fun y => σ (Set.projIcc (0 : ℝ) 1 zero_le_one y)
  have hσc : Measurable σc := sigc_meas σ hcont
  have heqσ := sigc_eq σ
  set A : Set (Coins m) := {U | Agr σc ε W x1 U}
  set A' : Set ((Fin m → ℝ) × Coins m) := {q | Agr σc ε W q.1 q.2}
  have hA' : MeasurableSet A' := meas_agr_joint σc hσc ε W
  have hA : MeasurableSet A :=
    hA'.preimage (Measurable.prodMk measurable_const measurable_id)
  set R : ℕ → Set (Coins m) := fun n => {U | beliefAct σc ε W x1 U n ∈ Good}
  have hR : ∀ n, MeasurableSet[coinFiltration m n] (R n) := by
    intro n
    set V0 : Coins m := fun _ _ => 0
    have hh : Measurable (fun a : Fin n → Fin m → unitInterval =>
        beliefAct σc ε W x1 (join n (a, V0)) n) :=
      (bel_meas σc hσc ε W n).comp (Measurable.prodMk measurable_const
        ((measurable_join n).comp (Measurable.prodMk measurable_id measurable_const)))
    refine ⟨_, hh hGood, ?_⟩
    ext U
    simp only [Set.mem_preimage, Set.mem_setOf_eq, R]
    rw [bel_past σc ε W x1 n U]
    rfl
  have hlow : ∀ n, ∀ B, MeasurableSet[coinFiltration m n] B →
      ENNReal.ofReal c * coinLaw m (B ∩ R n) ≤ coinLaw m (A ∩ (B ∩ R n)) := by
    intro n B hB
    obtain ⟨B', hB', rfl⟩ := hB
    have hmk := markov_bound_past σc hσc ε W x1 n B' hB' Good hGood A' hA' (ENNReal.ofReal c)
      (fun y hy => by
        refine (hc y hy).trans (le_of_eq ?_)
        congr 1
        ext V
        exact agr_congr_sigma σ σc heqσ ε hε W hW y (hGc y hy) V)
    refine le_trans (le_of_eq ?_) (hmk.trans (measure_mono ?_))
    · rfl
    · rintro U ⟨h1, h2, h3⟩
      exact ⟨agr_restart σc ε W x1 U n h3, h1, h2⟩
  have hvisit : ∀ U, U ∉ A → ∀ N, ∃ n ≥ N, U ∈ R n := by
    intro U hU N
    have hU' : ¬ Agr σ ε W x1 U := fun h =>
      hU ((agr_congr_sigma σ σc heqσ ε hε W hW x1 hx1 U).1 h)
    obtain ⟨n, hn, hg⟩ := hvis U hU' N
    refine ⟨n, hn, ?_⟩
    show beliefAct σc ε W x1 U n ∈ Good
    rw [← bel_congr_sigma σ σc heqσ ε hε W hW x1 hx1 U n]
    exact hg
  have hzero := levy_lower A hA R hR c hc0 hlow hvisit
  have hae : ∀ᵐ U ∂coinLaw m, U ∈ A := ae_iff.2 hzero
  filter_upwards [hae] with U hU
  exact (agr_congr_sigma σ σc heqσ ε hε W hW x1 hx1 U).2 hU


lemma deriv_one (σ : ℝ → ℝ) (h1 : σ 1 = 1) (hd : DifferentiableWithinAt ℝ σ (Set.Icc 0 1) 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ Set.Icc (1 - δ) 1, 1 - σ x ≤ C * (1 - x) := by
  set d := derivWithin σ (Set.Icc 0 1) 1
  have hD := hd.hasDerivWithinAt
  rw [hasDerivWithinAt_iff_isLittleO] at hD
  have hb := hD.bound one_pos
  rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at hb
  obtain ⟨e, he, hP⟩ := hb
  refine ⟨|d| + 1, by positivity, min (e / 2) 1, lt_min (by linarith) one_pos, ?_⟩
  intro x hx
  have hx0 : 0 ≤ x := by linarith [hx.1, min_le_right (e / 2) 1]
  have hdist : dist x 1 < e := by
    rw [Real.dist_eq, abs_of_nonpos (by linarith [hx.2])]
    linarith [hx.1, min_le_left (e / 2) 1]
  have := hP hdist ⟨hx0, hx.2⟩
  rw [h1, Real.norm_eq_abs, Real.norm_eq_abs, smul_eq_mul, one_mul,
    abs_of_nonpos (by linarith [hx.2] : x - 1 ≤ 0)] at this
  have h2 := (abs_le.1 this).1
  have h3 : -((x - 1) * d) ≤ |d| * (1 - x) := by
    have : -((x - 1) * d) = (1 - x) * d := by ring
    rw [this, mul_comm]
    exact mul_le_mul_of_nonneg_right (le_abs_self d) (by linarith [hx.2])
  nlinarith

lemma deriv_zero (σ : ℝ → ℝ) (h0 : σ 0 = 0) (hd : DifferentiableWithinAt ℝ σ (Set.Icc 0 1) 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ Set.Icc 0 δ, σ x ≤ C * x := by
  set d := derivWithin σ (Set.Icc 0 1) 0
  have hD := hd.hasDerivWithinAt
  rw [hasDerivWithinAt_iff_isLittleO] at hD
  have hb := hD.bound one_pos
  rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at hb
  obtain ⟨e, he, hP⟩ := hb
  refine ⟨|d| + 1, by positivity, min (e / 2) 1, lt_min (by linarith) one_pos, ?_⟩
  intro x hx
  have hx1 : x ≤ 1 := by linarith [hx.2, min_le_right (e / 2) 1]
  have hdist : dist x 0 < e := by
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hx.1]
    linarith [hx.2, min_le_left (e / 2) 1]
  have := hP hdist ⟨hx.1, hx1⟩
  rw [h0, Real.norm_eq_abs, Real.norm_eq_abs, smul_eq_mul, one_mul, sub_zero, sub_zero,
    abs_of_nonneg hx.1] at this
  have h2 := (abs_le.1 this).2
  have h3 : x * d ≤ |d| * x := by
    rw [mul_comm]; exact mul_le_mul_of_nonneg_right (le_abs_self d) hx.1
  nlinarith

end NL6

open NL6 in
theorem solution (σ : ℝ → ℝ) (h0 : σ 0 = 0) (h1 : σ 1 = 1)
    (hint : ∀ x ∈ Set.Ioo (0 : ℝ) 1, σ x ∈ Set.Ioo (0 : ℝ) 1)
    (hcont : ContinuousOn σ (Set.Icc 0 1))
    (hdiff : DifferentiableWithinAt ℝ σ (Set.Icc 0 1) 0 ∨
      DifferentiableWithinAt ℝ σ (Set.Icc 0 1) 1) :
    ∀ (m : ℕ) (W : Matrix (Fin m) (Fin m) ℝ), IsWeightMatrix W →
      ∀ ε ∈ Set.Ioc (0 : ℝ) 1, ∀ x1 : Fin m → ℝ, (∀ i, x1 i ∈ Set.Icc (0 : ℝ) 1) →
        EventualAgreement σ ε W x1 := by
  intro m W hW ε hε x1 hx1
  have hmaps : Set.MapsTo σ (Set.Icc 0 1) (Set.Icc 0 1) := by
    intro x hx
    rcases eq_or_lt_of_le hx.1 with h | h
    · subst h; rw [h0]; exact ⟨le_rfl, zero_le_one⟩
    rcases eq_or_lt_of_le hx.2 with h' | h'
    · subst h'; rw [h1]; exact ⟨zero_le_one, le_rfl⟩
    exact Set.Ioo_subset_Icc_self (hint x ⟨h, h'⟩)
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    exact Eventually.of_forall fun U => ⟨0, 0, Or.inl rfl, fun t _ i => i.elim0⟩
  obtain ⟨hε0, hε1⟩ := hε
  -- the minimal positive weight
  set S := (Finset.univ : Finset (Fin m × Fin m)).filter (fun p => 0 < W p.1 p.2)
  have hSne : S.Nonempty := ⟨(⟨0, hm⟩, ⟨0, hm⟩), by simp [S, hW.2.2]⟩
  set wmin := S.inf' hSne (fun p => W p.1 p.2)
  have hwmin0 : 0 < wmin := by
    rw [Finset.lt_inf'_iff]; intro p hp; simp only [S, Finset.mem_filter] at hp; exact hp.2
  have hwmin_le : ∀ i j, 0 < W i j → wmin ≤ W i j := fun i j hij =>
    Finset.inf'_le _ (by simp [S, hij] : (i, j) ∈ S)
  have hW1 : ∀ i j, W i j ≤ 1 := by
    intro i j
    have := Finset.single_le_sum (f := fun k => W i k)
      (fun k _ => Matrix.nonneg_of_mem_rowStochastic hW.1) (Finset.mem_univ j)
    rwa [Matrix.sum_row_of_mem_rowStochastic hW.1] at this
  have hwmin1 : wmin ≤ 1 := (hwmin_le _ _ (hW.2.2 ⟨0, hm⟩)).trans (hW1 _ _)
  set θ := ε * wmin / 2 with hθ
  have hθ0 : 0 < θ := by positivity
  have hθh : θ ≤ 1 / 2 := by
    have : ε * wmin ≤ 1 := by nlinarith
    linarith
  have hpos : ∀ i j, 0 < W i j → θ ≤ ε * W i j := by
    intro i j hij
    have := hwmin_le i j hij
    have : ε * wmin ≤ ε * W i j := mul_le_mul_of_nonneg_left this hε0.le
    linarith
  have hεI : ε ∈ Set.Ioc (0 : ℝ) 1 := ⟨hε0, hε1⟩
  have hxm := bel_mem σ ε hεI W hW.1 x1 hx1
  -- minima of σ and 1 - σ on compact intervals
  have hmin : ∀ a b : ℝ, a ≤ b → Set.Icc a b ⊆ Set.Icc 0 1 → ∀ f : ℝ → ℝ,
      ContinuousOn f (Set.Icc 0 1) → (∀ x ∈ Set.Icc a b, 0 < f x) →
      ∃ q, 0 < q ∧ ∀ x ∈ Set.Icc a b, q ≤ f x := by
    intro a b hab hsub f hf hpos'
    obtain ⟨x0, hx0, hmin⟩ := isCompact_Icc.exists_isMinOn (Set.nonempty_Icc.2 hab)
      (hf.mono hsub)
    exact ⟨f x0, hpos' x0 hx0, fun x hx => hmin hx⟩
  have hσpos : ∀ x ∈ Set.Ioc (0 : ℝ) 1, 0 < σ x := by
    intro x hx
    rcases eq_or_lt_of_le hx.2 with h | h
    · subst h; rw [h1]; norm_num
    · exact (hint x ⟨hx.1, h⟩).1
  have hσlt : ∀ x ∈ Set.Ico (0 : ℝ) 1, σ x < 1 := by
    intro x hx
    rcases eq_or_lt_of_le hx.1 with h | h
    · subst h; rw [h0]; norm_num
    · exact (hint x ⟨h, hx.2⟩).2
  rcases hdiff with hd0 | hd1
  · -- differentiable at 0: absorption at the corner 0
    obtain ⟨qa, hqa, hqa'⟩ := hmin 0 (1 - θ) (by linarith) (Set.Icc_subset_Icc le_rfl (by linarith))
      (fun x => 1 - σ x) (continuousOn_const.sub hcont)
      (fun x hx => by have := hσlt x ⟨hx.1, by linarith [hx.2]⟩; linarith)
    obtain ⟨qb, hqb, hqb'⟩ := hmin (1 - θ) 1 (by linarith) (Set.Icc_subset_Icc (by linarith) le_rfl)
      σ hcont (fun x hx => hσpos x ⟨by linarith [hx.1], hx.2⟩)
    obtain ⟨C, hC0, δ0, hδ0, hder⟩ := deriv_zero σ h0 hd0
    set δ := min δ0 (ε / (2 * (m * C + 1)))
    have hδ : 0 < δ := lt_min hδ0 (by positivity)
    have hCδ : (m : ℝ) * (C * δ) ≤ ε / 2 := by
      have h1' : δ ≤ ε / (2 * (m * C + 1)) := min_le_right _ _
      have hmC : 0 ≤ (m : ℝ) * C := by positivity
      rw [le_div_iff₀ (by positivity)] at h1'
      nlinarith
    obtain ⟨c, hc0, hc⟩ := uniform_agr0 σ hmaps ε hεI W hW θ hθ0 hpos (min qa qb)
      (lt_min hqa hqb) (fun x hx => (min_le_left _ _).trans (hqa' x hx))
      (fun x hx => (min_le_right _ _).trans (hqb' x hx)) C δ hC0 hδ hCδ
      (fun x hx => hder x ⟨hx.1, hx.2.trans (min_le_left _ _)⟩)
    set Good : Set (Fin m → ℝ) := {y | (∀ i, y i ∈ Set.Icc (0 : ℝ) 1) ∧ ∃ j, y j ≤ 1 - θ}
    have hGood : MeasurableSet Good := by
      have : Good = (⋂ i, (fun y : Fin m → ℝ => y i) ⁻¹' Set.Icc 0 1) ∩
          ⋃ j, (fun y : Fin m → ℝ => y j) ⁻¹' Set.Iic (1 - θ) := by
        ext y; simp [Good]
      rw [this]
      exact (MeasurableSet.iInter fun i => measurableSet_Icc.preimage (measurable_pi_apply i)).inter
        (MeasurableSet.iUnion fun j => measurableSet_Iic.preimage (measurable_pi_apply j))
    refine agreement_main σ hmaps hcont ε hεI W hW.1 x1 hx1 Good hGood (fun y hy => hy.1) c hc0
      (fun y hy => hc y hy.1 hy.2) ?_
    intro U hU N
    by_contra hcon
    push Not at hcon
    apply hU
    refine ⟨N, 1, Or.inr rfl, fun t ht i => ?_⟩
    rcases actOf_cases σ (U t i) (beliefAct σ ε W x1 U t i) with h | h
    · exfalso
      have hnot := hcon (t + 1) (by omega)
      simp only [Good, Set.mem_setOf_eq, not_and, not_exists, not_le] at hnot
      have hlt := hnot (hxm U (t + 1)) i
      rw [bel_succ] at hlt
      have hsum : ∑ j, W i j * actOf σ (U t j) (beliefAct σ ε W x1 U t j) ≤ 1 - W i i := by
        have hle : ∀ j, W i j * actOf σ (U t j) (beliefAct σ ε W x1 U t j) ≤
            W i j * (1 - if j = i then 1 else 0) := by
          intro j
          have hWij : 0 ≤ W i j := Matrix.nonneg_of_mem_rowStochastic hW.1
          by_cases hji : j = i
          · subst hji; simp [h]
          · simp only [hji, if_false, sub_zero, mul_one]
            have := (actOf_mem σ (U t j) (beliefAct σ ε W x1 U t j)).2
            nlinarith
        calc _ ≤ ∑ j, W i j * (1 - if j = i then 1 else 0) := Finset.sum_le_sum fun j _ => hle j
          _ = 1 - W i i := by
            simp [mul_sub, Finset.sum_sub_distrib, Matrix.sum_row_of_mem_rowStochastic hW.1]
      have hxi := (hxm U t i).2
      have := hpos i i (hW.2.2 i)
      nlinarith
    · exact h
  · -- differentiable at 1: absorption at the corner 1
    obtain ⟨qa, hqa, hqa'⟩ := hmin θ 1 (by linarith) (Set.Icc_subset_Icc hθ0.le le_rfl)
      σ hcont (fun x hx => hσpos x ⟨by linarith [hx.1], hx.2⟩)
    obtain ⟨qb, hqb, hqb'⟩ := hmin 0 θ hθ0.le (Set.Icc_subset_Icc le_rfl (by linarith))
      (fun x => 1 - σ x) (continuousOn_const.sub hcont)
      (fun x hx => by have := hσlt x ⟨hx.1, by linarith [hx.2]⟩; linarith)
    obtain ⟨C, hC0, δ0, hδ0, hder⟩ := deriv_one σ h1 hd1
    set δ := min δ0 (ε / (2 * (m * C + 1)))
    have hδ : 0 < δ := lt_min hδ0 (by positivity)
    have hCδ : (m : ℝ) * (C * δ) ≤ ε / 2 := by
      have h1' : δ ≤ ε / (2 * (m * C + 1)) := min_le_right _ _
      have hmC : 0 ≤ (m : ℝ) * C := by positivity
      rw [le_div_iff₀ (by positivity)] at h1'
      nlinarith
    obtain ⟨c, hc0, hc⟩ := uniform_agr1 σ hmaps ε hεI W hW θ hθ0 hpos (min qa qb)
      (lt_min hqa hqb) (fun x hx => (min_le_left _ _).trans (hqa' x hx))
      (fun x hx => (min_le_right _ _).trans (hqb' x hx)) C δ hC0 hδ hCδ
      (fun x hx => hder x ⟨by linarith [hx.1, min_le_left δ0 (ε / (2 * (m * C + 1)))], hx.2⟩)
    set Good : Set (Fin m → ℝ) := {y | (∀ i, y i ∈ Set.Icc (0 : ℝ) 1) ∧ ∃ j, θ ≤ y j}
    have hGood : MeasurableSet Good := by
      have : Good = (⋂ i, (fun y : Fin m → ℝ => y i) ⁻¹' Set.Icc 0 1) ∩
          ⋃ j, (fun y : Fin m → ℝ => y j) ⁻¹' Set.Ici θ := by
        ext y; simp [Good]
      rw [this]
      exact (MeasurableSet.iInter fun i => measurableSet_Icc.preimage (measurable_pi_apply i)).inter
        (MeasurableSet.iUnion fun j => measurableSet_Ici.preimage (measurable_pi_apply j))
    refine agreement_main σ hmaps hcont ε hεI W hW.1 x1 hx1 Good hGood (fun y hy => hy.1) c hc0
      (fun y hy => hc y hy.1 hy.2) ?_
    intro U hU N
    by_contra hcon
    push Not at hcon
    apply hU
    refine ⟨N, 0, Or.inl rfl, fun t ht i => ?_⟩
    rcases actOf_cases σ (U t i) (beliefAct σ ε W x1 U t i) with h | h
    · exact h
    · exfalso
      have hnot := hcon (t + 1) (by omega)
      simp only [Good, Set.mem_setOf_eq, not_and, not_exists, not_le] at hnot
      have hlt := hnot (hxm U (t + 1)) i
      rw [bel_succ] at hlt
      have hsum : W i i ≤ ∑ j, W i j * actOf σ (U t j) (beliefAct σ ε W x1 U t j) := by
        have := Finset.single_le_sum (f := fun j => W i j * actOf σ (U t j) (beliefAct σ ε W x1 U t j))
          (fun j _ => mul_nonneg (Matrix.nonneg_of_mem_rowStochastic hW.1)
            (actOf_mem σ (U t j) _).1) (Finset.mem_univ i)
        rw [h, mul_one] at this
        exact this
      have hxi := (hxm U t i).1
      have := hpos i i (hW.2.2 i)
      nlinarith
