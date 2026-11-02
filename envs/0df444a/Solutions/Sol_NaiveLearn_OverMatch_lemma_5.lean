-- Prove2me | solution 1 for NaiveLearn.OverMatch.lemma_5
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T13:20:13.40094+00:00
-- url     : https://prove2.me/submissions/921e825a-3247-4f96-b730-f53cd4958c57

import Mathlib
import Definitions.Def_NaiveLearn_OverMatch_Model
import Theorems.Thm_NaiveLearn_OverMatch_lemma_2

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

lemma mu_pos {m : ℕ} (W : Matrix (Fin m) (Fin m) ℝ) (μ : Fin m → ℝ)
    (hW : IsWeightMatrix W) (hμ : IsCentrality W μ) : ∀ i, 0 < μ i := by
  obtain ⟨hμ0, hμ1, hμW⟩ := hμ
  have hpred : ∀ j k, μ j = 0 → 0 < W k j → μ k = 0 := by
    intro j k hj hkj
    have hcol : ∑ l, μ l * W l j = μ j := congrFun hμW j
    rw [hj] at hcol
    have hnn : ∀ l ∈ Finset.univ, 0 ≤ μ l * W l j := fun l _ =>
      mul_nonneg (hμ0 l) (Matrix.nonneg_of_mem_rowStochastic hW.1)
    have := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 hcol k (Finset.mem_univ _)
    rcases mul_eq_zero.1 this with h | h
    · exact h
    · linarith
  by_contra hcon
  push Not at hcon
  obtain ⟨i, hi⟩ := hcon
  have hi0 : μ i = 0 := le_antisymm hi (hμ0 i)
  letI := Matrix.toQuiver W
  have hpath : ∀ (k b : Fin m) (P : Quiver.Path k b), μ b = 0 → μ k = 0 := by
    intro k b P
    induction P with
    | nil => exact id
    | cons P e ih => exact fun hc => ih (hpred _ _ hc e.down)
  have hall : ∀ k, μ k = 0 := by
    intro k
    obtain ⟨P, _⟩ := hW.2.1.connected k i
    exact hpath k i P hi0
  have : ∑ k, μ k = 0 := Finset.sum_eq_zero fun k _ => hall k
  linarith

/-- One-step integration: the coin of period `t` is uniform and independent of the state at
time `t`. -/
lemma one_step {m : ℕ} (σ : ℝ → ℝ) (hσ : Measurable σ) (ε : ℝ) (W : Matrix (Fin m) (Fin m) ℝ)
    (x1 : Fin m → ℝ) (t : ℕ) (F : (Fin m → ℝ) × (Fin m → unitInterval) → ℝ)
    (hF : Measurable F) (C : ℝ) (hFb : ∀ q, ‖F q‖ ≤ C) :
    ∫ U, F (beliefAct σ ε W x1 U t, U t) ∂coinLaw m =
      ∫ U, (∫ u, F (beliefAct σ ε W x1 U t, u) ∂cv m) ∂coinLaw m := by
  set P := (Measure.pi fun _ : Fin t => cv m).prod (coinLaw m)
  set g : Coins m → (Fin m → ℝ) := fun U => beliefAct σ ε W x1 U t with hg
  have hgm : Measurable g :=
    (bel_meas σ hσ ε W t).comp (Measurable.prodMk measurable_const measurable_id)
  let V0 : Coins m := fun _ _ => 0
  set h : (Fin t → Fin m → unitInterval) → (Fin m → ℝ) := fun a => g (join t (a, V0))
  have hhm : Measurable h := (hgm.comp (measurable_join t)).comp
    (Measurable.prodMk measurable_id measurable_const)
  have hgh : ∀ a V, g (join t (a, V)) = h a := fun a V => bel_join_indep σ ε W x1 t a V V0
  have hjt : ∀ (a : Fin t → Fin m → unitInterval) (V : Coins m), join t (a, V) t = V 0 := by
    intro a V; unfold join; simp
  have hGm : StronglyMeasurable (fun y : Fin m → ℝ => ∫ u, F (y, u) ∂cv m) :=
    hF.stronglyMeasurable.integral_prod_right'
  have hGb : ∀ y, ‖∫ u, F (y, u) ∂cv m‖ ≤ C := by
    intro y
    calc ‖∫ u, F (y, u) ∂cv m‖ ≤ ∫ u, ‖F (y, u)‖ ∂cv m := norm_integral_le_integral_norm _
      _ ≤ ∫ _u, C ∂cv m := integral_mono_of_nonneg (Eventually.of_forall fun _ => norm_nonneg _)
          (integrable_const C) (Eventually.of_forall fun u => hFb _)
      _ = C := by simp
  have e1 : ∫ U, F (g U, U t) ∂coinLaw m = ∫ q, F (g (join t q), join t q t) ∂P := by
    conv_lhs => rw [← map_join t]
    rw [integral_map (measurable_join t).aemeasurable]
    exact (hF.comp (Measurable.prodMk hgm (measurable_pi_apply t))).aestronglyMeasurable
  have e2 : ∫ U, (∫ u, F (g U, u) ∂cv m) ∂coinLaw m =
      ∫ q, (∫ u, F (g (join t q), u) ∂cv m) ∂P := by
    conv_lhs => rw [← map_join t]
    rw [integral_map (measurable_join t).aemeasurable]
    exact (hGm.comp_measurable hgm).aestronglyMeasurable
  show ∫ U, F (g U, U t) ∂coinLaw m = ∫ U, (∫ u, F (g U, u) ∂cv m) ∂coinLaw m
  rw [e1, e2]
  simp_rw [hjt]
  have hint1 : Integrable (fun q : (Fin t → Fin m → unitInterval) × Coins m =>
      F (g (join t q), q.2 0)) P := by
    refine Integrable.of_bound ?_ C (Eventually.of_forall fun q => hFb _)
    exact (hF.comp (Measurable.prodMk (hgm.comp (measurable_join t))
      ((measurable_pi_apply 0).comp measurable_snd))).aestronglyMeasurable
  have hint2 : Integrable (fun q : (Fin t → Fin m → unitInterval) × Coins m =>
      ∫ u, F (g (join t q), u) ∂cv m) P := by
    refine Integrable.of_bound ?_ C (Eventually.of_forall fun q => hGb _)
    exact (hGm.comp_measurable (hgm.comp (measurable_join t))).aestronglyMeasurable
  rw [integral_prod _ hint1, integral_prod _ hint2]
  congr 1
  funext a
  simp only [hgh]
  rw [integral_const, probReal_univ, one_smul]
  · have hmap : (coinLaw m).map (fun V : Coins m => V 0) = cv m := by
      unfold coinLaw; exact Measure.infinitePi_map_eval _ 0
    rw [← hmap, integral_map (measurable_pi_apply 0).aemeasurable]
    exact (hF.comp (Measurable.prodMk measurable_const measurable_id)).aestronglyMeasurable


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

lemma int_act_coord {m : ℕ} (y : Fin m → ℝ) (hy : ∀ i, y i ∈ Set.Icc (0 : ℝ) 1) (i : Fin m) :
    ∫ u, actOf id (u i) (y i) ∂cv m = y i := by
  rw [integral_comp_eval (μ := fun _ : Fin m => (volume : Measure unitInterval))
    (f := fun v : unitInterval => actOf id v (y i)) (actOf_id_meas _).aestronglyMeasurable]
  exact int_act (hy i)

lemma act_sq (u : unitInterval) (r : ℝ) : actOf id u r * actOf id u r = actOf id u r := by
  rcases actOf_cases id u r with h | h <;> rw [h] <;> norm_num

lemma int_act_pair {m : ℕ} (y : Fin m → ℝ) (hy : ∀ i, y i ∈ Set.Icc (0 : ℝ) 1) (i j : Fin m) :
    ∫ u, actOf id (u i) (y i) * actOf id (u j) (y j) ∂cv m =
      y i * y j + (if i = j then y i * (1 - y i) else 0) := by
  by_cases hij : i = j
  · subst hij
    simp only [act_sq, if_true, int_act_coord y hy]
    ring
  · simp only [hij, if_false, add_zero]
    have hind := (iIndepFun_pi (μ := fun _ : Fin m => (volume : Measure unitInterval))
      (X := fun k v => actOf id v (y k)) (fun k => (actOf_id_meas _).aemeasurable)).indepFun hij
    have := hind.integral_fun_mul_eq_mul_integral
      ((actOf_id_meas _).comp (measurable_pi_apply i)).aestronglyMeasurable
      ((actOf_id_meas _).comp (measurable_pi_apply j)).aestronglyMeasurable
    rw [this]
    have e1 := int_act_coord y hy i
    have e2 := int_act_coord y hy j
    exact congrArg₂ (· * ·) e1 e2

lemma act_int {m : ℕ} (y : Fin m → ℝ) (i j : Fin m) :
    Integrable (fun u : Fin m → unitInterval => actOf id (u i) (y i) * actOf id (u j) (y j))
      (cv m) := by
  refine Integrable.of_bound ?_ 1 (Eventually.of_forall fun u => ?_)
  · exact (((actOf_id_meas _).comp (measurable_pi_apply i)).mul
      ((actOf_id_meas _).comp (measurable_pi_apply j))).aestronglyMeasurable
  · have h1 := actOf_mem id (u i) (y i)
    have h2 := actOf_mem id (u j) (y j)
    rw [Real.norm_eq_abs, abs_le]
    constructor <;> nlinarith [h1.1, h1.2, h2.1, h2.2]

lemma act_int1 {m : ℕ} (y : Fin m → ℝ) (i : Fin m) :
    Integrable (fun u : Fin m → unitInterval => actOf id (u i) (y i)) (cv m) := by
  refine Integrable.of_bound ((actOf_id_meas _).comp (measurable_pi_apply i)).aestronglyMeasurable
    1 (Eventually.of_forall fun u => ?_)
  have h1 := actOf_mem id (u i) (y i)
  rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith [h1.1, h1.2]

lemma int_S {m : ℕ} (μ : Fin m → ℝ) (y : Fin m → ℝ) (hy : ∀ i, y i ∈ Set.Icc (0 : ℝ) 1) :
    ∫ u, ∑ i, μ i * actOf id (u i) (y i) ∂cv m = ∑ i, μ i * y i := by
  rw [integral_finsetSum _ fun i _ => (act_int1 y i).const_mul (μ i)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_const_mul, int_act_coord y hy i]

lemma int_S2 {m : ℕ} (μ : Fin m → ℝ) (y : Fin m → ℝ) (hy : ∀ i, y i ∈ Set.Icc (0 : ℝ) 1) :
    ∫ u, (∑ i, μ i * actOf id (u i) (y i)) ^ 2 ∂cv m =
      (∑ i, μ i * y i) ^ 2 + ∑ i, μ i ^ 2 * (y i * (1 - y i)) := by
  have hexp : ∀ u : Fin m → unitInterval, (∑ i, μ i * actOf id (u i) (y i)) ^ 2 =
      ∑ i, ∑ j, μ i * μ j * (actOf id (u i) (y i) * actOf id (u j) (y j)) := by
    intro u
    rw [sq, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  simp_rw [hexp]
  rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
    (act_int y i j).const_mul _]
  simp_rw [fun i => integral_finsetSum _ fun j (_ : j ∈ Finset.univ) =>
    (act_int (m := m) y i j).const_mul (μ i * μ j)]
  simp_rw [integral_const_mul, int_act_pair y hy]
  simp only [mul_add, Finset.sum_add_distrib, mul_ite, mul_zero, Finset.sum_ite_eq,
    Finset.mem_univ, if_true]
  rw [sq, Finset.sum_mul_sum]
  congr 1
  · refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  · refine Finset.sum_congr rfl fun i _ => ?_
    ring


lemma musum_mem {m : ℕ} (μ : Fin m → ℝ) (hμ0 : ∀ i, 0 ≤ μ i) (hμ1 : ∑ i, μ i = 1)
    (a : Fin m → ℝ) (ha : ∀ i, a i ∈ Set.Icc (0 : ℝ) 1) : ∑ i, μ i * a i ∈ Set.Icc (0 : ℝ) 1 := by
  constructor
  · exact Finset.sum_nonneg fun i _ => mul_nonneg (hμ0 i) (ha i).1
  · calc ∑ i, μ i * a i ≤ ∑ i, μ i * 1 :=
          Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (ha i).2 (hμ0 i)
      _ = 1 := by simp [hμ1]

lemma drift {m : ℕ} (W : Matrix (Fin m) (Fin m) ℝ) (μ : Fin m → ℝ)
    (hμ : Matrix.vecMul μ W = μ) (ε : ℝ) (x1 : Fin m → ℝ) (U : Coins m) (t : ℕ) :
    ∑ i, μ i * beliefAct id ε W x1 U (t + 1) i =
      (1 - ε) * ∑ i, μ i * beliefAct id ε W x1 U t i +
        ε * ∑ j, μ j * actOf id (U t j) (beliefAct id ε W x1 U t j) := by
  have hcol : ∀ j, ∑ i, μ i * W i j = μ j := fun j => congrFun hμ j
  have key : ∑ i, ∑ j, μ i * W i j * actOf id (U t j) (beliefAct id ε W x1 U t j) =
      ∑ j, μ j * actOf id (U t j) (beliefAct id ε W x1 U t j) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Finset.sum_mul, hcol j]
  have expand : ∀ i, μ i * beliefAct id ε W x1 U (t + 1) i =
      (1 - ε) * (μ i * beliefAct id ε W x1 U t i) +
        ε * ∑ j, μ i * W i j * actOf id (U t j) (beliefAct id ε W x1 U t j) := by
    intro i
    have hsum : ∑ j, μ i * W i j * actOf id (U t j) (beliefAct id ε W x1 U t j) =
        μ i * ∑ j, W i j * actOf id (U t j) (beliefAct id ε W x1 U t j) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => mul_assoc _ _ _
    rw [bel_succ, hsum]
    ring
  rw [Finset.sum_congr rfl fun i _ => expand i, Finset.sum_add_distrib, ← Finset.mul_sum,
    ← Finset.mul_sum, key]

/-- Coordinatewise projection onto the cube. -/
noncomputable def proj {m : ℕ} (y : Fin m → ℝ) : Fin m → ℝ :=
  fun i => (Set.projIcc (0 : ℝ) 1 zero_le_one (y i) : ℝ)

lemma proj_mem {m : ℕ} (y : Fin m → ℝ) : ∀ i, proj y i ∈ Set.Icc (0 : ℝ) 1 :=
  fun i => (Set.projIcc (0 : ℝ) 1 zero_le_one (y i)).2

lemma proj_eq {m : ℕ} (y : Fin m → ℝ) (hy : ∀ i, y i ∈ Set.Icc (0 : ℝ) 1) : proj y = y := by
  funext i; simp [proj, Set.projIcc_of_mem zero_le_one (hy i)]

lemma proj_meas {m : ℕ} : Measurable (proj (m := m)) := by
  apply Continuous.measurable
  exact continuous_pi fun i => continuous_subtype_val.comp
    (continuous_projIcc.comp (continuous_apply i))

lemma second_moment {m : ℕ} (W : Matrix (Fin m) (Fin m) ℝ) (μ : Fin m → ℝ)
    (hW : IsWeightMatrix W) (hμ : IsCentrality W μ) (ε : ℝ) (hε : ε ∈ Set.Ioc (0 : ℝ) 1)
    (x1 : Fin m → ℝ) (hx1 : ∀ i, x1 i ∈ Set.Icc (0 : ℝ) 1) (t : ℕ) :
    ∫ U, (∑ i, μ i * beliefAct id ε W x1 U (t + 1) i) ^ 2 ∂coinLaw m =
      ∫ U, (∑ i, μ i * beliefAct id ε W x1 U t i) ^ 2 ∂coinLaw m +
        ε ^ 2 * ∫ U, ∑ i, μ i ^ 2 * (beliefAct id ε W x1 U t i *
          (1 - beliefAct id ε W x1 U t i)) ∂coinLaw m := by
  obtain ⟨hμ0, hμ1, hμW⟩ := hμ
  obtain ⟨hε0, hε1⟩ := hε
  have hxm := bel_mem id ε ⟨hε0, hε1⟩ W hW.1 x1 hx1
  set A : (Fin m → ℝ) → ℝ := fun y => ∑ i, μ i * proj y i
  set S : (Fin m → ℝ) → (Fin m → unitInterval) → ℝ :=
    fun y u => ∑ i, μ i * actOf id (u i) (proj y i)
  set F : (Fin m → ℝ) × (Fin m → unitInterval) → ℝ :=
    fun q => ((1 - ε) * A q.1 + ε * S q.1 q.2) ^ 2
  have hA : ∀ y, A y ∈ Set.Icc (0 : ℝ) 1 := fun y => musum_mem μ hμ0 hμ1 _ (proj_mem y)
  have hS : ∀ y u, S y u ∈ Set.Icc (0 : ℝ) 1 := fun y u =>
    musum_mem μ hμ0 hμ1 _ (fun i => actOf_mem id _ _)
  have hFb : ∀ q, ‖F q‖ ≤ 1 := by
    intro q
    have h1 := hA q.1
    have h2 := hS q.1 q.2
    have h3 : (1 - ε) * A q.1 + ε * S q.1 q.2 ∈ Set.Icc (0 : ℝ) 1 := by
      constructor <;> nlinarith [h1.1, h1.2, h2.1, h2.2]
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    nlinarith [h3.1, h3.2]
  have hFm : Measurable F := by
    have hAm : Measurable A := Finset.measurable_sum _ fun i _ =>
      measurable_const.mul ((measurable_pi_apply i).comp proj_meas)
    have hSm : Measurable (fun q : (Fin m → ℝ) × (Fin m → unitInterval) => S q.1 q.2) :=
      Finset.measurable_sum _ fun i _ => measurable_const.mul ((actOf_meas id measurable_id).comp
        (Measurable.prodMk ((measurable_pi_apply i).comp measurable_snd)
          ((measurable_pi_apply i).comp (proj_meas.comp measurable_fst))))
    exact (((measurable_const.mul (hAm.comp measurable_fst)).add
      (measurable_const.mul hSm))).pow_const 2
  have hL : ∀ U, (∑ i, μ i * beliefAct id ε W x1 U (t + 1) i) ^ 2 =
      F (beliefAct id ε W x1 U t, U t) := by
    intro U
    rw [drift W μ hμW ε x1 U t]
    simp only [F, A, S, proj_eq _ (hxm U t)]
  have hG : ∀ y, ∫ u, F (y, u) ∂cv m =
      A y ^ 2 + ε ^ 2 * ∑ i, μ i ^ 2 * (proj y i * (1 - proj y i)) := by
    intro y
    have hS1 : Integrable (fun u => S y u) (cv m) :=
      integrable_finsetSum _ fun i _ => (act_int1 (proj y) i).const_mul _
    have hS2 : Integrable (fun u => S y u ^ 2) (cv m) := by
      refine Integrable.of_bound ?_ 1 (Eventually.of_forall fun u => ?_)
      · exact (Finset.measurable_sum _ fun i _ => measurable_const.mul
          ((actOf_id_meas _).comp (measurable_pi_apply i))).pow_const 2 |>.aestronglyMeasurable
      · have := hS y u
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]; nlinarith [this.1, this.2]
    have hexp : ∀ u, F (y, u) = (1 - ε) ^ 2 * A y ^ 2 +
        (2 * (1 - ε) * ε * A y) * S y u + ε ^ 2 * S y u ^ 2 := by
      intro u; simp only [F]; ring
    have e1 : ∫ u, S y u ∂cv m = A y := int_S μ (proj y) (proj_mem y)
    have e2 : ∫ u, S y u ^ 2 ∂cv m = A y ^ 2 + ∑ i, μ i ^ 2 * (proj y i * (1 - proj y i)) :=
      int_S2 μ (proj y) (proj_mem y)
    calc ∫ u, F (y, u) ∂cv m = ∫ u, (((1 - ε) ^ 2 * A y ^ 2 +
          (2 * (1 - ε) * ε * A y) * S y u) + ε ^ 2 * S y u ^ 2) ∂cv m := by
          congr 1; funext u; exact hexp u
      _ = ∫ u, ((1 - ε) ^ 2 * A y ^ 2 + (2 * (1 - ε) * ε * A y) * S y u) ∂cv m +
          ∫ u, ε ^ 2 * S y u ^ 2 ∂cv m :=
          integral_add ((integrable_const _).add (hS1.const_mul _)) (hS2.const_mul _)
      _ = ((1 - ε) ^ 2 * A y ^ 2 + (2 * (1 - ε) * ε * A y) * ∫ u, S y u ∂cv m) +
          ε ^ 2 * ∫ u, S y u ^ 2 ∂cv m := by
          rw [integral_add (integrable_const _) (hS1.const_mul _), integral_const,
            integral_const_mul, integral_const_mul, probReal_univ, one_smul]
      _ = _ := by rw [e1, e2]; ring
  simp_rw [hL]
  rw [one_step id measurable_id ε W x1 t F hFm 1 hFb]
  simp_rw [hG]
  have hpe : ∀ U, proj (beliefAct id ε W x1 U t) = beliefAct id ε W x1 U t :=
    fun U => proj_eq _ (hxm U t)
  simp only [hpe]
  have hMi : Integrable (fun U => (∑ i, μ i * beliefAct id ε W x1 U t i) ^ 2) (coinLaw m) := by
    refine Integrable.of_bound ?_ 1 (Eventually.of_forall fun U => ?_)
    · exact ((Finset.measurable_sum _ fun i _ => measurable_const.mul
        ((measurable_pi_apply i).comp ((bel_meas id measurable_id ε W t).comp
          (Measurable.prodMk measurable_const measurable_id)))).pow_const 2).aestronglyMeasurable
    · have := musum_mem μ hμ0 hμ1 _ (hxm U t)
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]; nlinarith [this.1, this.2]
  have hQi : Integrable (fun U => ∑ i, μ i ^ 2 * (beliefAct id ε W x1 U t i *
      (1 - beliefAct id ε W x1 U t i))) (coinLaw m) := by
    refine integrable_finsetSum _ fun i _ => Integrable.const_mul ?_ _
    refine Integrable.of_bound ?_ 1 (Eventually.of_forall fun U => ?_)
    · have hb : Measurable (fun U : Coins m => beliefAct id ε W x1 U t i) :=
        (measurable_pi_apply i).comp ((bel_meas id measurable_id ε W t).comp
          (Measurable.prodMk measurable_const measurable_id))
      exact (hb.mul (measurable_const.sub hb)).aestronglyMeasurable
    · have := hxm U t i
      rw [Real.norm_eq_abs, abs_le]; constructor <;> nlinarith [this.1, this.2]
  simp only [A, hpe]
  rw [integral_add hMi (hQi.const_mul _), integral_const_mul]


lemma Q_tendsto {m : ℕ} (W : Matrix (Fin m) (Fin m) ℝ) (μ : Fin m → ℝ)
    (hW : IsWeightMatrix W) (hμ : IsCentrality W μ) (ε : ℝ) (hε : ε ∈ Set.Ioc (0 : ℝ) 1)
    (x1 : Fin m → ℝ) (hx1 : ∀ i, x1 i ∈ Set.Icc (0 : ℝ) 1) :
    ∀ᵐ U ∂coinLaw m, Tendsto (fun t => ∑ i, μ i ^ 2 * (beliefAct id ε W x1 U t i *
      (1 - beliefAct id ε W x1 U t i))) atTop (𝓝 0) := by
  set Q : ℕ → Coins m → ℝ := fun t U => ∑ i, μ i ^ 2 * (beliefAct id ε W x1 U t i *
      (1 - beliefAct id ε W x1 U t i)) with hQ
  set M2 : ℕ → ℝ := fun t => ∫ U, (∑ i, μ i * beliefAct id ε W x1 U t i) ^ 2 ∂coinLaw m
  have hxm := bel_mem id ε hε W hW.1 x1 hx1
  have hbm : ∀ t i, Measurable (fun U : Coins m => beliefAct id ε W x1 U t i) := fun t i =>
    (measurable_pi_apply i).comp ((bel_meas id measurable_id ε W t).comp
      (Measurable.prodMk measurable_const measurable_id))
  have hQm : ∀ t, Measurable (Q t) := fun t => Finset.measurable_sum _ fun i _ =>
    measurable_const.mul ((hbm t i).mul (measurable_const.sub (hbm t i)))
  have hQ0 : ∀ t U, 0 ≤ Q t U := fun t U => Finset.sum_nonneg fun i _ =>
    mul_nonneg (sq_nonneg _) (mul_nonneg (hxm U t i).1 (by linarith [(hxm U t i).2]))
  have hQ1 : ∀ t U, Q t U ≤ 1 := by
    intro t U
    calc Q t U ≤ ∑ i, μ i * 1 := Finset.sum_le_sum fun i _ => by
          have h1 := hxm U t i
          have hμi := hμ.1 i
          have hμle : μ i ≤ 1 := by
            have := Finset.single_le_sum (fun j _ => hμ.1 j) (Finset.mem_univ i)
            rw [hμ.2.1] at this; exact this
          have : beliefAct id ε W x1 U t i * (1 - beliefAct id ε W x1 U t i) ≤ 1 := by
            nlinarith [h1.1, h1.2]
          have : μ i ^ 2 ≤ μ i := by nlinarith
          nlinarith [mul_nonneg h1.1 (by linarith [h1.2] : (0:ℝ) ≤ 1 - beliefAct id ε W x1 U t i)]
      _ = 1 := by simp [hμ.2.1]
  have hQi : ∀ t, Integrable (Q t) (coinLaw m) := fun t =>
    Integrable.of_bound (hQm t).aestronglyMeasurable 1 (Eventually.of_forall fun U => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hQ0 t U)]; exact hQ1 t U)
  have hrec : ∀ n, M2 n = M2 0 + ε ^ 2 * ∑ t ∈ Finset.range n, ∫ U, Q t U ∂coinLaw m := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ, mul_add, ← add_assoc, ← ih]
      exact second_moment W μ hW hμ ε hε x1 hx1 n
  have hM2 : ∀ n, 0 ≤ M2 n ∧ M2 n ≤ 1 := by
    intro n
    have hb : ∀ U, (∑ i, μ i * beliefAct id ε W x1 U n i) ^ 2 ∈ Set.Icc (0 : ℝ) 1 := by
      intro U
      have := musum_mem μ hμ.1 hμ.2.1 _ (hxm U n)
      constructor <;> nlinarith [this.1, this.2]
    constructor
    · exact integral_nonneg fun U => (hb U).1
    · calc M2 n ≤ ∫ _U, (1 : ℝ) ∂coinLaw m := integral_mono_of_nonneg
            (Eventually.of_forall fun U => (hb U).1) (integrable_const _)
            (Eventually.of_forall fun U => (hb U).2)
        _ = 1 := by simp
  have hsum : ∀ n, ∑ t ∈ Finset.range n, ∫ U, Q t U ∂coinLaw m ≤ 1 / ε ^ 2 := by
    intro n
    have h := hrec n
    have h1 := hM2 n
    have h0 := hM2 0
    have hε2 : 0 < ε ^ 2 := by have := hε.1; positivity
    rw [le_div_iff₀ hε2]
    nlinarith
  have hlin : ∫⁻ U, ∑' t, ENNReal.ofReal (Q t U) ∂coinLaw m ≠ ⊤ := by
    rw [lintegral_tsum fun t => (hQm t).ennreal_ofReal.aemeasurable]
    have : ∀ t, ∫⁻ U, ENNReal.ofReal (Q t U) ∂coinLaw m =
        ENNReal.ofReal (∫ U, Q t U ∂coinLaw m) := fun t =>
      (ofReal_integral_eq_lintegral_ofReal (hQi t) (Eventually.of_forall (hQ0 t))).symm
    simp_rw [this]
    refine ne_top_of_le_ne_top (ENNReal.ofReal_ne_top (r := 1 / ε ^ 2)) ?_
    refine ENNReal.tsum_le_of_sum_range_le fun n => ?_
    rw [← ENNReal.ofReal_sum_of_nonneg fun t _ => integral_nonneg (hQ0 t)]
    exact ENNReal.ofReal_le_ofReal (hsum n)
  have hae : ∀ᵐ U ∂coinLaw m, ∑' t, ENNReal.ofReal (Q t U) ≠ ⊤ := by
    have := ae_lt_top (Measurable.ennreal_tsum fun t => (hQm t).ennreal_ofReal) hlin
    filter_upwards [this] with U hU using hU.ne
  filter_upwards [hae] with U hU
  have h1 := ENNReal.tendsto_atTop_zero_of_tsum_ne_top hU
  have h2 := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h1
  simp only [Function.comp_def, ENNReal.toReal_ofReal (hQ0 _ U), ENNReal.toReal_zero] at h2
  exact h2

/-- Doob's maximal inequality along the whole time axis. -/
lemma maximal_all {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (𝒢 : Filtration ℕ (inferInstance : MeasurableSpace Ω)) (f : ℕ → Ω → ℝ)
    (hsub : Submartingale f 𝒢 P) (hnonneg : 0 ≤ f) (a : ℝ) (ha : ∀ n, ∫ ω, f n ω ∂P ≤ a)
    (c : NNReal) : (c : ENNReal) * P {ω | ∃ k, (c : ℝ) ≤ f k ω} ≤ ENNReal.ofReal a := by
  set S : ℕ → Set Ω := fun n =>
    {ω | (c : ℝ) ≤ (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one fun k => f k ω}
  have hmono : Monotone S := by
    intro n n' hnn' ω hω
    simp only [S, Set.mem_setOf_eq] at hω ⊢
    refine hω.trans (Finset.sup'_mono _ ?_ _)
    intro k hk; simp only [Finset.mem_range] at hk ⊢; omega
  have hsub' : {ω | ∃ k, (c : ℝ) ≤ f k ω} ⊆ ⋃ n, S n := by
    rintro ω ⟨k, hk⟩
    refine Set.mem_iUnion.2 ⟨k, ?_⟩
    simp only [S, Set.mem_setOf_eq]
    exact hk.trans (Finset.le_sup' (fun k => f k ω) (Finset.mem_range.2 (Nat.lt_succ_self k)))
  have hbound : ∀ n, (c : ENNReal) * P (S n) ≤ ENNReal.ofReal a := by
    intro n
    refine (maximal_ineq hsub hnonneg n).trans (ENNReal.ofReal_le_ofReal ?_)
    refine le_trans ?_ (ha n)
    exact setIntegral_le_integral (hsub.integrable n) (Eventually.of_forall fun ω => hnonneg n ω)
  calc (c : ENNReal) * P {ω | ∃ k, (c : ℝ) ≤ f k ω} ≤ (c : ENNReal) * P (⋃ n, S n) :=
        mul_le_mul_right (measure_mono hsub') _
    _ = (c : ENNReal) * ⨆ n, P (S n) := by rw [hmono.measure_iUnion]
    _ = ⨆ n, (c : ENNReal) * P (S n) := ENNReal.mul_iSup _ _
    _ ≤ ENNReal.ofReal a := iSup_le hbound

end NL6

open NL6 in
theorem solution (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) {m : ℕ} (W : Matrix (Fin m) (Fin m) ℝ)
    (μ : Fin m → ℝ) (hW : IsWeightMatrix W) (hμ : IsCentrality W μ) :
    ∀ γ : ℝ, 0 < γ → ∃ η0 : ℝ, 0 < η0 ∧ ∀ η ∈ Set.Ioo (0 : ℝ) η0,
      ∀ ε ∈ Set.Ioc (0 : ℝ) 1, ∀ x1 : Fin m → ℝ, (∀ i, x1 i ∈ Set.Icc (0 : ℝ) 1) →
        ((∀ i, 1 - η < x1 i) →
          ENNReal.ofReal (1 - γ) ≤ coinLaw m {U |
            Tendsto (beliefAct id ε W x1 U) atTop (𝓝 1) ∧
              ∀ t i, p < beliefAct id ε W x1 U t i}) ∧
        ((∀ i, x1 i < η) →
          ENNReal.ofReal (1 - γ) ≤ coinLaw m {U |
            Tendsto (beliefAct id ε W x1 U) atTop (𝓝 0) ∧
              ∀ t i, beliefAct id ε W x1 U t i < p}) := by
  intro γ hγ
  have hpos := mu_pos W μ hW hμ
  have hne : (Finset.univ : Finset (Fin m)).Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    have := hμ.2.1
    rw [h, Finset.sum_empty] at this
    norm_num at this
  set μs := Finset.univ.inf' hne μ with hμs
  have hμs0 : 0 < μs := by
    rw [Finset.lt_inf'_iff]; exact fun i _ => hpos i
  have hμsle : ∀ i, μs ≤ μ i := fun i => Finset.inf'_le _ (Finset.mem_univ i)
  set c1 := μs * (1 - p)
  set c0 := μs * p
  have hc1 : 0 < c1 := mul_pos hμs0 (by linarith)
  have hc0 : 0 < c0 := mul_pos hμs0 hp0
  set c1n : NNReal := ⟨c1, hc1.le⟩ with hc1n
  set c0n : NNReal := ⟨c0, hc0.le⟩ with hc0n
  have hc1r : (c1n : ℝ) = c1 := rfl
  have hc0r : (c0n : ℝ) = c0 := rfl
  refine ⟨γ * min c1 c0, mul_pos hγ (lt_min hc1 hc0), ?_⟩
  intro η hη ε hε x1 hx1
  have hηc1 : η / c1 < γ := by
    rw [div_lt_iff₀ hc1]; nlinarith [hη.2, min_le_left c1 c0]
  have hηc0 : η / c0 < γ := by
    rw [div_lt_iff₀ hc0]; nlinarith [hη.2, min_le_right c1 c0]
  have hxm := bel_mem id ε hε W hW.1 x1 hx1
  set M : ℕ → Coins m → ℝ := fun t U => ∑ i, μ i * beliefAct id ε W x1 U t i with hMdef
  have hMart : Martingale M (coinFiltration m) (coinLaw m) := lemma_2 W μ hW hμ ε hε x1 hx1
  have hMb : ∀ t U, M t U ∈ Set.Icc (0 : ℝ) 1 := fun t U => musum_mem μ hμ.1 hμ.2.1 _ (hxm U t)
  have hMint : ∀ n, ∫ U, M n U ∂coinLaw m = ∑ i, μ i * x1 i := by
    intro n
    have h := hMart.setIntegral_eq (Nat.zero_le n) MeasurableSet.univ
    simp only [Measure.restrict_univ] at h
    rw [← h]
    simp [M, beliefAct]
  have hQ := Q_tendsto W μ hW hμ ε hε x1 hx1
  -- coordinatewise vanishing of x(1-x)
  have hcoord : ∀ U, Tendsto (fun t => ∑ i, μ i ^ 2 * (beliefAct id ε W x1 U t i *
      (1 - beliefAct id ε W x1 U t i))) atTop (𝓝 0) → ∀ i,
      Tendsto (fun t => beliefAct id ε W x1 U t i * (1 - beliefAct id ε W x1 U t i))
        atTop (𝓝 0) := by
    intro U hU i
    have hnn : ∀ t j, 0 ≤ μ j ^ 2 * (beliefAct id ε W x1 U t j *
        (1 - beliefAct id ε W x1 U t j)) := fun t j =>
      mul_nonneg (sq_nonneg _) (mul_nonneg (hxm U t j).1 (by linarith [(hxm U t j).2]))
    have hle : ∀ t, μ i ^ 2 * (beliefAct id ε W x1 U t i *
        (1 - beliefAct id ε W x1 U t i)) ≤ ∑ j, μ j ^ 2 * (beliefAct id ε W x1 U t j *
        (1 - beliefAct id ε W x1 U t j)) := fun t =>
      Finset.single_le_sum (fun j _ => hnn t j) (Finset.mem_univ i)
    have h1 : Tendsto (fun t => μ i ^ 2 * (beliefAct id ε W x1 U t i *
        (1 - beliefAct id ε W x1 U t i))) atTop (𝓝 0) :=
      tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hU (fun t => hnn t i) hle
    have hμi2 : 0 < μ i ^ 2 := by have := hpos i; positivity
    have h2 := h1.const_mul (1 / μ i ^ 2)
    rw [mul_zero] at h2
    refine h2.congr fun t => ?_
    have hμi : μ i ≠ 0 := (hpos i).ne'
    field_simp
  constructor
  · intro hx1η
    -- maximal inequality for 1 - M
    set f : ℕ → Coins m → ℝ := (fun _ _ => (1 : ℝ)) + -M with hf
    have hfmart : Martingale f (coinFiltration m) (coinLaw m) :=
      (martingale_const (coinFiltration m) (coinLaw m) (1 : ℝ)).add hMart.neg
    have hfnn : 0 ≤ f := fun t U => by
      simp only [hf, Pi.add_apply, Pi.neg_apply, Pi.zero_apply]; linarith [(hMb t U).2]
    have hfint : ∀ n, ∫ U, f n U ∂coinLaw m ≤ η := by
      intro n
      have : ∫ U, f n U ∂coinLaw m = 1 - ∫ U, M n U ∂coinLaw m := by
        simp only [hf, Pi.add_apply, Pi.neg_apply]
        have hi : Integrable (fun U => -M n U) (coinLaw m) := (hMart.integrable n).neg
        rw [integral_add (integrable_const (1 : ℝ)) hi, integral_neg,
          integral_const, probReal_univ, one_smul, sub_eq_add_neg]
      rw [this, hMint]
      have : ∑ i, μ i * (1 - η) ≤ ∑ i, μ i * x1 i := Finset.sum_le_sum fun i _ =>
        mul_le_mul_of_nonneg_left (hx1η i).le (hμ.1 i)
      rw [← Finset.sum_mul, hμ.2.1, one_mul] at this
      linarith
    have hmax := maximal_all (coinLaw m) (coinFiltration m) f hfmart.submartingale hfnn η hfint
      c1n
    set E := {U : Coins m | ∀ t i, p < beliefAct id ε W x1 U t i}
    have hbad : Eᶜ ⊆ {U | ∃ k, (c1n : ℝ) ≤ f k U} := by
      intro U hU
      simp only [E, Set.mem_compl_iff, Set.mem_setOf_eq, not_forall, not_lt] at hU
      obtain ⟨t, i, hti⟩ := hU
      refine ⟨t, ?_⟩
      simp only [hc1r, hf, Pi.add_apply, Pi.neg_apply, M]
      have hsplit : 1 - ∑ j, μ j * beliefAct id ε W x1 U t j =
          ∑ j, μ j * (1 - beliefAct id ε W x1 U t j) := by
        rw [Finset.sum_congr rfl fun j _ => mul_sub (μ j) 1 _, Finset.sum_sub_distrib]
        simp [hμ.2.1]
      have hge : μ i * (1 - beliefAct id ε W x1 U t i) ≤
          ∑ j, μ j * (1 - beliefAct id ε W x1 U t j) :=
        Finset.single_le_sum (f := fun j => μ j * (1 - beliefAct id ε W x1 U t j)) (fun j _ => mul_nonneg (hμ.1 j) (by linarith [(hxm U t j).2]))
          (Finset.mem_univ i)
      have : c1 ≤ μ i * (1 - beliefAct id ε W x1 U t i) := by
        simp only [c1]
        exact mul_le_mul (hμsle i) (by linarith) (by linarith) (hμ.1 i)
      linarith
    have hPbad : coinLaw m Eᶜ ≤ ENNReal.ofReal γ := by
      have h1 := (mul_le_mul_right (measure_mono hbad) _).trans hmax
      have hfin : coinLaw m Eᶜ ≠ ⊤ := measure_ne_top _ _
      have h2 := ENNReal.toReal_mono ENNReal.ofReal_ne_top h1
      rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hη.1.le, ENNReal.coe_toReal] at h2
      rw [← ENNReal.ofReal_toReal hfin]
      apply ENNReal.ofReal_le_ofReal
      rw [hc1r] at h2
      have : (coinLaw m Eᶜ).toReal ≤ η / c1 := by rw [le_div_iff₀ hc1]; linarith
      linarith
    have hEgood : ∀ᵐ U ∂coinLaw m, U ∈ E → U ∈ {U | Tendsto (beliefAct id ε W x1 U) atTop
        (𝓝 1) ∧ ∀ t i, p < beliefAct id ε W x1 U t i} := by
      filter_upwards [hQ] with U hU hUE
      refine ⟨?_, hUE⟩
      rw [tendsto_pi_nhds]
      intro i
      have hc := hcoord U hU i
      have hlim : Tendsto (fun t => 1 - beliefAct id ε W x1 U t i) atTop (𝓝 0) := by
        have h3 := hc.div_const p
        rw [zero_div] at h3
        refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h3
          (fun t => by linarith [(hxm U t i).2]) (fun t => ?_)
        have hx := hUE t i
        rw [le_div_iff₀ hp0]
        nlinarith [(hxm U t i).2]
      have := (tendsto_const_nhds (x := (1 : ℝ))).sub hlim
      simp only [sub_sub_cancel, sub_zero] at this
      simpa using this
    have hu : (1 : ENNReal) ≤ coinLaw m E + coinLaw m Eᶜ := by
      rw [← measure_univ (μ := coinLaw m), ← Set.union_compl_self E]
      exact measure_union_le _ _
    calc ENNReal.ofReal (1 - γ) = 1 - ENNReal.ofReal γ := by
          rw [ENNReal.ofReal_sub 1 hγ.le, ENNReal.ofReal_one]
      _ ≤ coinLaw m E := tsub_le_iff_right.2 (hu.trans (add_le_add le_rfl hPbad))
      _ ≤ _ := measure_mono_ae hEgood
  · intro hx1η
    have hfnn : 0 ≤ M := fun t U => (hMb t U).1
    have hfint : ∀ n, ∫ U, M n U ∂coinLaw m ≤ η := by
      intro n
      rw [hMint]
      have : ∑ i, μ i * x1 i ≤ ∑ i, μ i * η := Finset.sum_le_sum fun i _ =>
        mul_le_mul_of_nonneg_left (hx1η i).le (hμ.1 i)
      rw [← Finset.sum_mul, hμ.2.1, one_mul] at this
      linarith
    have hmax := maximal_all (coinLaw m) (coinFiltration m) M hMart.submartingale hfnn η hfint
      c0n
    set E := {U : Coins m | ∀ t i, beliefAct id ε W x1 U t i < p}
    have hbad : Eᶜ ⊆ {U | ∃ k, (c0n : ℝ) ≤ M k U} := by
      intro U hU
      simp only [E, Set.mem_compl_iff, Set.mem_setOf_eq, not_forall, not_lt] at hU
      obtain ⟨t, i, hti⟩ := hU
      refine ⟨t, ?_⟩
      simp only [hc0r, M]
      have hge : μ i * beliefAct id ε W x1 U t i ≤ ∑ j, μ j * beliefAct id ε W x1 U t j :=
        Finset.single_le_sum (f := fun j => μ j * beliefAct id ε W x1 U t j) (fun j _ => mul_nonneg (hμ.1 j) (hxm U t j).1) (Finset.mem_univ i)
      have : c0 ≤ μ i * beliefAct id ε W x1 U t i := by
        simp only [c0]
        exact mul_le_mul (hμsle i) hti hp0.le (hμ.1 i)
      linarith
    have hPbad : coinLaw m Eᶜ ≤ ENNReal.ofReal γ := by
      have h1 := (mul_le_mul_right (measure_mono hbad) _).trans hmax
      have hfin : coinLaw m Eᶜ ≠ ⊤ := measure_ne_top _ _
      have h2 := ENNReal.toReal_mono ENNReal.ofReal_ne_top h1
      rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hη.1.le, ENNReal.coe_toReal] at h2
      rw [← ENNReal.ofReal_toReal hfin]
      apply ENNReal.ofReal_le_ofReal
      rw [hc0r] at h2
      have : (coinLaw m Eᶜ).toReal ≤ η / c0 := by rw [le_div_iff₀ hc0]; linarith
      linarith
    have hEgood : ∀ᵐ U ∂coinLaw m, U ∈ E → U ∈ {U | Tendsto (beliefAct id ε W x1 U) atTop
        (𝓝 0) ∧ ∀ t i, beliefAct id ε W x1 U t i < p} := by
      filter_upwards [hQ] with U hU hUE
      refine ⟨?_, hUE⟩
      rw [tendsto_pi_nhds]
      intro i
      have hc := hcoord U hU i
      have h3 := hc.div_const (1 - p)
      rw [zero_div] at h3
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h3
        (fun t => (hxm U t i).1) (fun t => ?_)
      have hx := hUE t i
      rw [le_div_iff₀ (by linarith)]
      nlinarith [(hxm U t i).1]
    have hu : (1 : ENNReal) ≤ coinLaw m E + coinLaw m Eᶜ := by
      rw [← measure_univ (μ := coinLaw m), ← Set.union_compl_self E]
      exact measure_union_le _ _
    calc ENNReal.ofReal (1 - γ) = 1 - ENNReal.ofReal γ := by
          rw [ENNReal.ofReal_sub 1 hγ.le, ENNReal.ofReal_one]
      _ ≤ coinLaw m E := tsub_le_iff_right.2 (hu.trans (add_le_add le_rfl hPbad))
      _ ≤ _ := measure_mono_ae hEgood
