-- Prove2me | solution 1 for KellyStochasticNetworks.MigrationDynamics.stationary_time_reversal
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T12:27:02.307476+00:00
-- url     : https://prove2.me/submissions/95e20492-660e-4af1-ae41-88e183b12fd2

import Definitions.Def_KellyStochasticNetworks_MigrationDynamics_Process
import Mathlib

open MeasureTheory Filter Topology

set_option linter.unusedSectionVars false

namespace S202KR

open KellyStochasticNetworks KellyStochasticNetworks.MigrationDynamics

variable {Ω S : Type*} [MeasurableSpace Ω] [MeasurableSpace S] [MeasurableSingletonClass S]
  [Countable S] [DecidableEq S]

def MarkovProp (P : Measure Ω) (X : ℝ → Ω → S) (K : ℝ → S → S → ℝ) : Prop :=
  ∀ (n : ℕ) (t : Fin (n + 1) → ℝ) (x : Fin (n + 1) → S)
        (u : ℝ) (y : S), StrictMono t → t (Fin.last n) < u →
      (P {ω | (∀ i, X (t i) ω = x i) ∧ X u ω = y}).toReal =
        cylinder P X t x * K (u - t (Fin.last n)) (x (Fin.last n)) y

theorem pair_formula {P : Measure Ω} {X : ℝ → Ω → S} {K : ℝ → S → S → ℝ} {π : S → ℝ}
    (hmk : MarkovProp P X K) (hπ : ∀ t i, (P {ω | X t ω = i}).toReal = π i)
    (s h : ℝ) (hh : 0 < h) (k j : S) :
    (P {ω | X s ω = k ∧ X (s + h) ω = j}).toReal = π k * K h k j := by
  have := hmk 0 (fun _ => s) (fun _ => k) (s + h) j
    (fun a b hab => absurd hab (by rw [Fin.fin_one_eq_zero a, Fin.fin_one_eq_zero b]; simp))
    (by simp; linarith)
  have e1 : {ω | (∀ i : Fin (0 + 1), X s ω = k) ∧ X (s + h) ω = j} =
      {ω | X s ω = k ∧ X (s + h) ω = j} := by
    ext ω; simp
  rw [e1] at this
  rw [this]
  unfold MigrationDynamics.cylinder
  have e2 : {ω | ∀ i : Fin (0 + 1), X s ω = k} = {ω | X s ω = k} := by
    ext ω; simp
  rw [e2, hπ]
  congr 1; simp

theorem fwd_formula {P : Measure Ω} {X : ℝ → Ω → S} {K : ℝ → S → S → ℝ} {π : S → ℝ}
    (hmk : MarkovProp P X K) (hπ : ∀ t i, (P {ω | X t ω = i}).toReal = π i) :
    ∀ (m : ℕ) (s : Fin (m + 1) → ℝ) (z : Fin (m + 1) → S), StrictMono s →
      (P {ω | ∀ i, X (s i) ω = z i}).toReal =
        π (z 0) * ∏ i : Fin m, K (s i.succ - s i.castSucc) (z i.castSucc) (z i.succ) := by
  intro m
  induction m with
  | zero =>
    intro s z _
    have e2 : {ω | ∀ i : Fin (0 + 1), X (s i) ω = z i} = {ω | X (s 0) ω = z 0} := by
      ext ω; simp
    simp only [Finset.univ_eq_empty, Finset.prod_empty, mul_one]
    rw [e2]; exact hπ _ _
  | succ m ih =>
    intro s z hs
    have hset : {ω | ∀ i, X (s i) ω = z i} =
        {ω | (∀ i : Fin (m + 1), X ((s ∘ Fin.castSucc) i) ω = (z ∘ Fin.castSucc) i) ∧
          X (s (Fin.last (m + 1))) ω = z (Fin.last (m + 1))} := by
      ext ω; simp only [Set.mem_ofPred_eq, Function.comp]
      exact Fin.forall_fin_succ'
    rw [hset, hmk m (s ∘ Fin.castSucc) (z ∘ Fin.castSucc) _ _
      (hs.comp Fin.strictMono_castSucc) (hs (Fin.castSucc_lt_last _))]
    unfold MigrationDynamics.cylinder
    rw [ih _ _ (hs.comp Fin.strictMono_castSucc), Fin.prod_univ_castSucc]
    simp only [Function.comp, Fin.succ_castSucc, Fin.castSucc_zero, Fin.succ_last]
    ring

theorem cons_formula {P : Measure Ω} {X : ℝ → Ω → S} {K : ℝ → S → S → ℝ} {π : S → ℝ}
    (hmk : MarkovProp P X K) (hπ : ∀ t i, (P {ω | X t ω = i}).toReal = π i)
    (n : ℕ) (s : Fin (n + 1) → ℝ) (z : Fin (n + 1) → S) (a : ℝ) (b : S)
    (hs : StrictMono s) (ha : a < s 0) :
    (P {ω | ∀ i, X ((Fin.cons a s : Fin (n + 2) → ℝ) i) ω =
        (Fin.cons b z : Fin (n + 2) → S) i}).toReal * π (z 0) =
      π b * K (s 0 - a) b (z 0) * (P {ω | ∀ i, X (s i) ω = z i}).toReal := by
  have hcs : StrictMono (Fin.cons a s : Fin (n + 2) → ℝ) := by
    refine Fin.strictMono_iff_lt_succ.2 ?_
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa using ha
    · simp only [Fin.cons_succ, ← Fin.succ_castSucc]
      exact hs Fin.castSucc_lt_succ
  rw [fwd_formula hmk hπ _ _ _ hcs, fwd_formula hmk hπ _ _ _ hs, Fin.prod_univ_succ]
  simp only [Fin.cons_zero, Fin.castSucc_zero, Fin.succ_zero_eq_one, Fin.cons_one,
    ← Fin.succ_castSucc, Fin.cons_succ]
  ring


theorem rev_markov {P : Measure Ω} {X : ℝ → Ω → S} {K : ℝ → S → S → ℝ} {π : S → ℝ}
    (hmk : MarkovProp P X K) (hπ : ∀ t i, (P {ω | X t ω = i}).toReal = π i)
    (hpos : ∀ i, 0 < π i) :
    MarkovProp P (fun t => X (-t)) (fun h i j => π j * K h j i / π i) := by
  intro n t x u y ht hu
  set s' : Fin (n + 1) → ℝ := fun i => -t (Fin.rev i) with hs'
  set z' : Fin (n + 1) → S := fun i => x (Fin.rev i) with hz'
  have hs'm : StrictMono s' := by
    intro a b hab
    simp only [hs', neg_lt_neg_iff]
    exact ht (Fin.rev_lt_rev.2 hab)
  have ha : -u < s' 0 := by simp [hs']; linarith
  have key := cons_formula hmk hπ n s' z' (-u) y hs'm ha
  have e1 : {ω | (∀ i, (fun t => X (-t)) (t i) ω = x i) ∧ (fun t => X (-t)) u ω = y} =
      {ω | ∀ i, X ((Fin.cons (-u) s' : Fin (n + 2) → ℝ) i) ω =
        (Fin.cons y z' : Fin (n + 2) → S) i} := by
    ext ω
    simp only [Set.mem_ofPred_eq]
    constructor
    · rintro ⟨h1, h2⟩ i
      refine Fin.cases ?_ (fun j => ?_) i
      · simpa using h2
      · simp [hs', hz', h1]
    · intro h
      refine ⟨fun i => ?_, by simpa using h 0⟩
      have := h (Fin.rev i).succ
      simpa [hs', hz'] using this
  have e2 : MigrationDynamics.cylinder P (fun t => X (-t)) t x =
      (P {ω | ∀ i, X (s' i) ω = z' i}).toReal := by
    unfold MigrationDynamics.cylinder
    congr 2
    ext ω
    simp only [Set.mem_ofPred_eq, hs', hz']
    exact Fin.rev_surjective.forall (p := fun i => X (-t i) ω = x i)
  rw [e1, e2]
  have h0 : z' 0 = x (Fin.last n) := by simp [hz']
  have h1 : s' 0 - -u = u - t (Fin.last n) := by simp [hs']; ring
  rw [h0, h1] at key
  have hp := hpos (x (Fin.last n))
  field_simp
  linarith

theorem lfjp_neg {x : ℝ → S} (hx : LocallyFiniteJumpPath x) :
    LocallyFiniteJumpPath (fun t => x (-t)) := by
  obtain ⟨h1, h2⟩ := hx
  refine ⟨fun a b hab => ?_, fun t => ?_⟩
  · obtain ⟨D, hD⟩ := h1 (-b) (-a) (by linarith)
    refine ⟨D.image (fun d => -d), fun s t has hst htb hav => ?_⟩
    refine (hD (-t) (-s) (by linarith) (by linarith) (by linarith) (fun d hd hmem => ?_)).symm
    apply hav (-d) (Finset.mem_image.2 ⟨d, hd, rfl⟩)
    obtain ⟨m1, m2⟩ := hmem
    exact ⟨by linarith, by linarith⟩
  · obtain ⟨ε, hε, h | h⟩ := h2 (-t)
    · refine ⟨ε, hε, Or.inr fun u hu => h (-u) ⟨by linarith [hu.2], by linarith [hu.1]⟩⟩
    · refine ⟨ε, hε, Or.inl fun u hu => h (-u) ⟨by linarith [hu.2], by linarith [hu.1]⟩⟩

theorem finite_range {x : ℝ → S} (hx : LocallyFiniteJumpPath x) :
    ∃ V : Finset S, ∀ t ∈ Set.Icc (0 : ℝ) 1, x t ∈ V := by
  classical
  obtain ⟨D, hD⟩ := hx.1 0 1 one_pos
  set E : Finset ℝ := insert 0 (insert 1 D) with hE
  refine ⟨E.image x ∪ (E ×ˢ E).image (fun p => x ((p.1 + p.2) / 2)), fun t ht => ?_⟩
  by_cases htE : t ∈ E
  · exact Finset.mem_union_left _ (Finset.mem_image_of_mem _ htE)
  have hne1 : (E.filter (· ≤ t)).Nonempty := ⟨0, by simp [hE, ht.1]⟩
  have hne2 : (E.filter (t ≤ ·)).Nonempty := ⟨1, by simp [hE, ht.2]⟩
  set l := (E.filter (· ≤ t)).max' hne1 with hl
  set r := (E.filter (t ≤ ·)).min' hne2 with hr
  have hlmem := Finset.max'_mem _ hne1
  have hrmem := Finset.min'_mem _ hne2
  rw [← hl, Finset.mem_filter] at hlmem
  rw [← hr, Finset.mem_filter] at hrmem
  have hlt : l < t := lt_of_le_of_ne hlmem.2 (fun h => htE (h ▸ hlmem.1))
  have htr : t < r := lt_of_le_of_ne hrmem.2 (fun h => htE (h ▸ hrmem.1))
  have hl0 : 0 ≤ l := Finset.le_max' _ 0 (by simp [hE, ht.1])
  have hr1 : r ≤ 1 := Finset.min'_le _ 1 (by simp [hE, ht.2])
  have hgap : ∀ d ∈ D, d ∉ Set.Ioo l r := by
    intro d hd hdm
    have hdE : d ∈ E := by simp [hE, hd]
    rcases le_total d t with h | h
    · have : d ≤ l := Finset.le_max' _ d (Finset.mem_filter.2 ⟨hdE, h⟩)
      linarith [hdm.1]
    · have : r ≤ d := Finset.min'_le _ d (Finset.mem_filter.2 ⟨hdE, h⟩)
      linarith [hdm.2]
  have hxm : x t = x ((l + r) / 2) := by
    rcases le_total t ((l + r) / 2) with h | h
    · exact hD _ _ (by linarith) h (by linarith) (fun d hd hm =>
        hgap d hd ⟨by linarith [hm.1], by linarith [hm.2]⟩)
    · exact (hD _ _ (by linarith) h (by linarith) (fun d hd hm =>
        hgap d hd ⟨by linarith [hm.1], by linarith [hm.2]⟩)).symm
  rw [hxm]
  exact Finset.mem_union_right _ (Finset.mem_image.2 ⟨(l, r), Finset.mem_product.2 ⟨hlmem.1, hrmem.1⟩, rfl⟩)

theorem mset (T : Set S) : MeasurableSet T := (Set.to_countable T).measurableSet

theorem meas_T {P : Measure Ω} [IsFiniteMeasure P] {X : ℝ → Ω → S} {K : ℝ → S → S → ℝ}
    {π : S → ℝ} (hmeas : ∀ t, Measurable (X t))
    (hmk : MarkovProp P X K) (hπ : ∀ t i, (P {ω | X t ω = i}).toReal = π i)
    (s h : ℝ) (hh : 0 < h) (T : Set S) (j : S) :
    P {ω | X s ω ∈ T ∧ X (s + h) ω = j} =
      ∑' k, ENNReal.ofReal (T.indicator (fun k => π k * K h k j) k) := by
  have hU : {ω | X s ω ∈ T ∧ X (s + h) ω = j} =
      ⋃ k, ({ω | X s ω = k} ∩ {ω | X s ω ∈ T ∧ X (s + h) ω = j}) := by
    ext ω; simp
  rw [hU, measure_iUnion]
  · congr 1; ext k
    by_cases hk : k ∈ T
    · rw [Set.indicator_of_mem hk, ← pair_formula hmk hπ s h hh k j,
        ENNReal.ofReal_toReal (measure_ne_top _ _)]
      congr 1; ext ω; simp only [Set.mem_inter_iff, Set.mem_ofPred_eq]
      constructor
      · rintro ⟨h1, -, h2⟩; exact ⟨h1, h2⟩
      · rintro ⟨h1, h2⟩; exact ⟨h1, h1 ▸ hk, h2⟩
    · rw [Set.indicator_of_notMem hk, ENNReal.ofReal_zero]
      convert measure_empty (μ := P)
      ext ω; simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_empty_iff_false,
        iff_false, not_and]
      intro h1 h2; exact absurd (h1 ▸ h2) hk
  · intro a b hab
    exact Disjoint.mono Set.inter_subset_left Set.inter_subset_left
      (Set.disjoint_left.2 fun ω h1 h2 => hab (h1.symm.trans h2))
  · intro k
    exact (hmeas s (measurableSet_singleton k)).inter
      ((hmeas s (mset T)).inter (hmeas (s + h) (measurableSet_singleton j)))

theorem row_hasSum {P : Measure Ω} [IsProbabilityMeasure P] {X : ℝ → Ω → S}
    {K : ℝ → S → S → ℝ} {π : S → ℝ} (hmeas : ∀ t, Measurable (X t))
    (hmk : MarkovProp P X K) (hπ : ∀ t i, (P {ω | X t ω = i}).toReal = π i)
    (hπ0 : ∀ i, 0 ≤ π i) (hK : ∀ h, 0 ≤ h → ∀ i j, 0 ≤ K h i j)
    (h : ℝ) (hh : 0 < h) (j : S) :
    HasSum (fun k => π k * K h k j) (π j) := by
  have e := meas_T hmeas hmk hπ 0 h hh Set.univ j
  simp only [Set.indicator_univ, Set.mem_univ, true_and, zero_add] at e
  have hfin : ∑' k, ENNReal.ofReal (π k * K h k j) ≠ ⊤ := by
    rw [← e]; exact measure_ne_top _ _
  have h1 := ENNReal.hasSum_toReal hfin
  have h2 : (fun k => (ENNReal.ofReal (π k * K h k j)).toReal) = fun k => π k * K h k j := by
    ext k; exact ENNReal.toReal_ofReal (mul_nonneg (hπ0 k) (hK h hh.le k j))
  rw [h2] at h1
  have h3 : ∑' k, π k * K h k j = π j := by
    rw [← hπ h j, e, ENNReal.tsum_toReal_eq (fun _ => ENNReal.ofReal_ne_top), h2]
  exact h3 ▸ h1

theorem meas_T_real {P : Measure Ω} [IsProbabilityMeasure P] {X : ℝ → Ω → S}
    {K : ℝ → S → S → ℝ} {π : S → ℝ} (hmeas : ∀ t, Measurable (X t))
    (hmk : MarkovProp P X K) (hπ : ∀ t i, (P {ω | X t ω = i}).toReal = π i)
    (hπ0 : ∀ i, 0 ≤ π i) (hK : ∀ h, 0 ≤ h → ∀ i j, 0 ≤ K h i j)
    (s h : ℝ) (hh : 0 < h) (G : Finset S) (j : S) :
    P {ω | X s ω ∈ ((G : Set S)ᶜ) ∧ X (s + h) ω = j} =
      ENNReal.ofReal (π j - ∑ k ∈ G, π k * K h k j) := by
  rw [meas_T hmeas hmk hπ s h hh]
  have hs := row_hasSum hmeas hmk hπ hπ0 hK h hh j
  have h1 : HasSum ((G : Set S).indicator (fun k => π k * K h k j)) (∑ k ∈ G, π k * K h k j) := by
    have : HasSum ((G : Set S).indicator (fun k => π k * K h k j))
        (∑ b ∈ G, (G : Set S).indicator (fun k => π k * K h k j) b) :=
      hasSum_sum_of_ne_finset_zero (fun b hb => Set.indicator_of_notMem (by simpa using hb) _)
    convert this using 1
    exact Finset.sum_congr rfl fun b hb => (Set.indicator_of_mem (Finset.mem_coe.2 hb) (fun k => π k * K h k j)).symm
  have h2 := hs.sub h1
  have h3 : (fun b => π b * K h b j - (G : Set S).indicator (fun k => π k * K h k j) b) =
      ((G : Set S)ᶜ).indicator (fun k => π k * K h k j) := by
    ext b; by_cases hb : b ∈ (G : Set S) <;> simp [hb]
  rw [h3] at h2
  rw [← ENNReal.ofReal_tsum_of_nonneg, h2.tsum_eq]
  · intro k
    exact Set.indicator_nonneg (fun k _ => mul_nonneg (hπ0 k) (hK h hh.le k j)) k
  · exact h2.summable


noncomputable def δ (p : ℕ) : ℝ := ((2 : ℝ) ^ p)⁻¹

theorem δ_pos (p : ℕ) : 0 < δ p := by unfold δ; positivity

theorem δ_succ (p : ℕ) : δ (p + 1) = δ p / 2 := by
  unfold δ; rw [pow_succ, mul_inv]; ring

theorem δ_tendsto : Tendsto δ atTop (𝓝[>] 0) :=
  tendsto_nhdsWithin_iff.2 ⟨tendsto_inv_atTop_zero.comp
    (tendsto_pow_atTop_atTop_of_one_lt one_lt_two), Eventually.of_forall δ_pos⟩

def Aset (X : ℝ → Ω → S) (i : S) (F : Finset S) (p m : ℕ) : Set Ω :=
  {ω | X (m * δ p) ω ∈ ((↑(insert i F) : Set S)ᶜ) ∧ X (m * δ p + δ p) ω = i}

noncomputable def Ccount (X : ℝ → Ω → S) (i : S) (F : Finset S) (p : ℕ) (ω : Ω) : ENNReal :=
  ∑ m ∈ Finset.range (2 ^ p), (Aset X i F p m).indicator 1 ω

theorem Aset_meas {X : ℝ → Ω → S} (hmeas : ∀ t, Measurable (X t)) (i : S) (F : Finset S)
    (p m : ℕ) : MeasurableSet (Aset X i F p m) := by
  have := (hmeas (m * δ p) (mset ((↑(insert i F) : Set S)ᶜ))).inter
    (hmeas (m * δ p + δ p) (measurableSet_singleton i))
  convert this using 1
  ext ω; simp [Aset]

theorem Ccount_meas {X : ℝ → Ω → S} (hmeas : ∀ t, Measurable (X t)) (i : S) (F : Finset S)
    (p : ℕ) : Measurable (Ccount X i F p) := by
  unfold Ccount
  exact Finset.measurable_sum _ fun m _ => measurable_one.indicator (Aset_meas hmeas i F p m)

theorem lint_C {P : Measure Ω} [IsProbabilityMeasure P] {X : ℝ → Ω → S}
    {K : ℝ → S → S → ℝ} {π : S → ℝ} (hmeas : ∀ t, Measurable (X t))
    (hmk : MarkovProp P X K) (hπ : ∀ t i, (P {ω | X t ω = i}).toReal = π i)
    (hπ0 : ∀ i, 0 ≤ π i) (hK : ∀ h, 0 ≤ h → ∀ i j, 0 ≤ K h i j)
    (i : S) (F : Finset S) (p : ℕ) :
    ∫⁻ ω, Ccount X i F p ω ∂P =
      ENNReal.ofReal ((2 : ℝ) ^ p * (π i - ∑ k ∈ insert i F, π k * K (δ p) k i)) := by
  unfold Ccount
  rw [lintegral_finsetSum _ (fun m _ => measurable_one.indicator (Aset_meas hmeas i F p m))]
  have : ∀ m ∈ Finset.range (2 ^ p), ∫⁻ ω, (Aset X i F p m).indicator 1 ω ∂P =
      ENNReal.ofReal (π i - ∑ k ∈ insert i F, π k * K (δ p) k i) := by
    intro m _
    rw [lintegral_indicator_one (Aset_meas hmeas i F p m)]
    exact meas_T_real hmeas hmk hπ hπ0 hK _ _ (δ_pos p) _ i
  rw [Finset.sum_congr rfl this, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
    ENNReal.ofReal_mul (by positivity)]
  congr 1
  rw [ENNReal.ofReal_pow (by norm_num)]
  simp

theorem sum_range_two_mul {M : Type*} [AddCommMonoid M] (f : ℕ → M) (N : ℕ) :
    ∑ m ∈ Finset.range (2 * N), f m = ∑ m ∈ Finset.range N, (f (2 * m) + f (2 * m + 1)) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [show 2 * (N + 1) = 2 * N + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ,
      ih, Finset.sum_range_succ, add_assoc]

theorem Ccount_mono (X : ℝ → Ω → S) (i : S) :
    Monotone (fun p => Ccount X i ∅ p) := by
  refine monotone_nat_of_le_succ fun p ω => ?_
  simp only [Ccount]
  rw [pow_succ, mul_comm, sum_range_two_mul]
  refine Finset.sum_le_sum fun m _ => ?_
  by_cases hω : ω ∈ Aset X i ∅ p m
  · rw [Set.indicator_of_mem hω]
    have h1 : ((2 * m : ℕ) : ℝ) * δ (p + 1) = m * δ p := by
      rw [δ_succ]; push_cast; ring
    have h2 : ((2 * m + 1 : ℕ) : ℝ) * δ (p + 1) = m * δ p + δ p / 2 := by
      rw [δ_succ]; push_cast; ring
    have h3 : ((2 * m + 1 : ℕ) : ℝ) * δ (p + 1) + δ (p + 1) = m * δ p + δ p := by
      rw [δ_succ]; push_cast; ring
    have h4 : ((2 * m : ℕ) : ℝ) * δ (p + 1) + δ (p + 1) = m * δ p + δ p / 2 := by
      rw [δ_succ]; push_cast; ring
    simp only [Aset, Finset.insert_empty, Finset.coe_singleton, Set.mem_compl_iff,
      Set.mem_singleton_iff, Set.mem_ofPred_eq] at hω
    by_cases hc : X (m * δ p + δ p / 2) ω = i
    · have : ω ∈ Aset X i ∅ (p + 1) (2 * m) := by
        simp only [Aset, Set.mem_ofPred_eq]
        rw [h4, h1]
        simp only [Finset.insert_empty, Finset.coe_singleton, Set.mem_compl_iff,
          Set.mem_singleton_iff]
        exact ⟨hω.1, hc⟩
      rw [Set.indicator_of_mem this]
      exact le_self_add
    · have : ω ∈ Aset X i ∅ (p + 1) (2 * m + 1) := by
        simp only [Aset, Set.mem_ofPred_eq]
        rw [h3, h2]
        simp only [Finset.insert_empty, Finset.coe_singleton, Set.mem_compl_iff,
          Set.mem_singleton_iff]
        exact ⟨hc, hω.2⟩
      rw [Set.indicator_of_mem this]
      exact le_add_self
  · rw [Set.indicator_of_notMem hω]; exact bot_le

theorem Ccount_anti (X : ℝ → Ω → S) (i : S) (F : Finset S) (p : ℕ) (ω : Ω) :
    Ccount X i F p ω ≤ Ccount X i ∅ p ω := by
  unfold Ccount
  refine Finset.sum_le_sum fun m _ => Set.indicator_le_indicator_of_subset ?_ (fun _ => bot_le) ω
  intro ω' hω'
  simp only [Aset, Finset.coe_insert, Set.mem_compl_iff, Set.mem_insert_iff, Finset.mem_coe,
    not_or, Set.mem_ofPred_eq, Finset.insert_empty, Finset.coe_singleton,
    Set.mem_singleton_iff] at hω' ⊢
  exact ⟨hω'.1.1, hω'.2⟩

theorem Ccount_zero {X : ℝ → Ω → S} (i : S) (F : Finset S) (ω : Ω)
    (hF : ∀ t ∈ Set.Icc (0 : ℝ) 1, X t ω ∈ F) (p : ℕ) : Ccount X i F p ω = 0 := by
  unfold Ccount
  refine Finset.sum_eq_zero fun m hm => Set.indicator_of_notMem ?_ _
  intro hω
  have hm' : (m : ℝ) ≤ 2 ^ p := by
    have := (Finset.mem_range.1 hm).le
    exact_mod_cast this
  have ht : (m : ℝ) * δ p ∈ Set.Icc (0 : ℝ) 1 := by
    refine ⟨mul_nonneg (Nat.cast_nonneg _) (δ_pos p).le, ?_⟩
    unfold δ; rw [← div_eq_mul_inv, div_le_one (by positivity)]; exact hm'
  have := hF _ ht
  exact hω.1 (by simp [this])


theorem full_balance {P : Measure Ω} [IsProbabilityMeasure P] {X : ℝ → Ω → S}
    {K : ℝ → S → S → ℝ} {π : S → ℝ} {q : S → S → ℝ} (hmeas : ∀ t, Measurable (X t))
    (hmk : MarkovProp P X K) (hπ : ∀ t i, (P {ω | X t ω = i}).toReal = π i)
    (hπ0 : ∀ i, 0 ≤ π i) (hK : ∀ h, 0 ≤ h → ∀ i j, 0 ≤ K h i j)
    (hlim : ∀ i j, Tendsto (fun h : ℝ => (K h i j - if i = j then 1 else 0) / h)
      (nhdsWithin 0 (Set.Ioi 0)) (𝓝 (if i = j then -(∑' k, q i k) else q i j)))
    (hae : ∀ᵐ ω ∂P, LocallyFiniteJumpPath (fun t => X t ω))
    (hq0 : ∀ i j, 0 ≤ q i j) (hqd : ∀ i, q i i = 0) (i : S) :
    HasSum (fun k => π k * q k i) (π i * ∑' k, q i k) := by
  set Q := ∑' k, q i k with hQ
  set L : Finset S → ℝ := fun F => π i * Q - ∑ k ∈ F.erase i, π k * q k i with hL
  have hlimF : ∀ F : Finset S, Tendsto
      (fun p => (2 : ℝ) ^ p * (π i - ∑ k ∈ insert i F, π k * K (δ p) k i)) atTop (𝓝 (L F)) := by
    intro F
    have e : ∀ p, (2 : ℝ) ^ p * (π i - ∑ k ∈ insert i F, π k * K (δ p) k i) =
        -π i * ((K (δ p) i i - if i = i then 1 else 0) / δ p) -
          ∑ k ∈ F.erase i, π k * ((K (δ p) k i - if k = i then 1 else 0) / δ p) := by
      intro p
      have hins : insert i F = insert i (F.erase i) := by
        ext k; by_cases hk : k = i <;> simp [hk]
      rw [hins, Finset.sum_insert (Finset.notMem_erase i F)]
      have hs : ∑ k ∈ F.erase i, π k * ((K (δ p) k i - if k = i then 1 else 0) / δ p) =
          (2 : ℝ) ^ p * ∑ k ∈ F.erase i, π k * K (δ p) k i := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun k hk => ?_
        rw [if_neg (Finset.ne_of_mem_erase hk)]
        unfold δ; rw [div_inv_eq_mul]; ring
      rw [hs, if_pos rfl]
      unfold δ; rw [div_inv_eq_mul]; ring
    have h1 := ((hlim i i).comp δ_tendsto).const_mul (-π i)
    have h2 := tendsto_finsetSum (F.erase i)
      (fun k _ => ((hlim k i).comp δ_tendsto).const_mul (π k))
    have hlimeq : L F = (-π i * if i = i then -∑' (k : S), q i k else q i i) -
        ∑ c ∈ F.erase i, π c * (if c = i then -∑' (k : S), q c k else q c i) := by
      rw [if_pos rfl, Finset.sum_congr rfl fun k hk => by rw [if_neg (Finset.ne_of_mem_erase hk)]]
      simp only [hL, hQ]; ring
    rw [hlimeq]
    exact (h1.sub h2).congr (fun p => (e p).symm)
  have hsum : ∀ (h : ℝ), 0 < h → HasSum (fun k => π k * K h k i) (π i) :=
    fun h hh => row_hasSum hmeas hmk hπ hπ0 hK h hh i
  have hLnn : ∀ F, 0 ≤ L F := by
    intro F
    refine ge_of_tendsto' (hlimF F) fun p => mul_nonneg (by positivity) ?_
    have := sum_le_hasSum (insert i F) (fun k _ => mul_nonneg (hπ0 k) (hK _ (δ_pos p).le k i))
      (hsum (δ p) (δ_pos p))
    linarith
  have hfi : ∀ F : Finset S, ∑ k ∈ F.erase i, π k * q k i = ∑ k ∈ F, π k * q k i :=
    fun F => Finset.sum_erase F (by simp [hqd])
  have hsumm : Summable (fun k => π k * q k i) := by
    refine summable_of_sum_le (c := π i * Q) (fun k => mul_nonneg (hπ0 k) (hq0 k i)) fun F => ?_
    have := hLnn F
    simp only [hL, hfi] at this
    linarith
  have hle : ∑' k, π k * q k i ≤ π i * Q := by
    refine hsumm.tsum_le_of_sum_le fun F => ?_
    have := hLnn F
    simp only [hL, hfi] at this
    linarith
  -- the path argument
  set G : Finset S → Ω → ENNReal := fun F ω => ⨆ p, Ccount X i F p ω with hG
  have hGle : ∀ F, ENNReal.ofReal (L F) ≤ ∫⁻ ω, G F ω ∂P := by
    intro F
    refine le_of_tendsto' ((ENNReal.continuous_ofReal.tendsto _).comp (hlimF F)) fun p => ?_
    rw [Function.comp_apply, ← lint_C hmeas hmk hπ hπ0 hK i F p]
    exact lintegral_mono fun ω => le_iSup (fun p => Ccount X i F p ω) p
  have hGmeas : ∀ F, Measurable (G F) := fun F => Measurable.iSup fun p => Ccount_meas hmeas i F p
  have hGfin : ∫⁻ ω, G ∅ ω ∂P ≠ ⊤ := by
    simp only [hG]
    rw [lintegral_iSup (fun p => Ccount_meas hmeas i ∅ p) (Ccount_mono X i)]
    obtain ⟨M, hM⟩ := (hlimF ∅).bddAbove_range
    refine ne_top_of_le_ne_top (ENNReal.ofReal_ne_top (r := M)) (iSup_le fun p => ?_)
    rw [lint_C hmeas hmk hπ hπ0 hK i ∅ p]
    exact ENNReal.ofReal_le_ofReal (hM ⟨p, rfl⟩)
  have : Nonempty S := ⟨i⟩
  obtain ⟨e, he⟩ := exists_surjective_nat S
  set Fr : ℕ → Finset S := fun r => (Finset.range r).image e with hFr
  have hFr_mono : Monotone Fr := fun a b hab =>
    Finset.image_subset_image (Finset.range_subset_range.2 hab)
  have hcover : ∀ k, ∃ r, k ∈ Fr r := fun k =>
    ⟨(he k).choose + 1, Finset.mem_image.2
      ⟨_, Finset.mem_range.2 (Nat.lt_succ_self _), (he k).choose_spec⟩⟩
  have h_lim : ∀ᵐ ω ∂P, Tendsto (fun r => G (Fr r) ω) atTop (𝓝 0) := by
    filter_upwards [hae] with ω hω
    obtain ⟨V, hV⟩ := finite_range hω
    set r0 := V.sup (fun v => (he v).choose) + 1
    have hr0 : ∀ v ∈ V, v ∈ Fr r0 := fun v hv => Finset.mem_image.2
      ⟨_, Finset.mem_range.2 (Nat.lt_succ_of_le (Finset.le_sup (f := fun v => (he v).choose) hv)),
        (he v).choose_spec⟩
    refine tendsto_atTop_of_eventually_const (i₀ := r0) fun r hr => ?_
    simp only [hG]
    have : ∀ p, Ccount X i (Fr r) p ω = 0 := fun p =>
      Ccount_zero i (Fr r) ω (fun t ht => hFr_mono hr (hr0 _ (hV t ht))) p
    simp [this]
  have hDC := tendsto_lintegral_of_dominated_convergence (G ∅) (fun r => hGmeas (Fr r))
    (fun r => Eventually.of_forall fun ω => iSup_mono fun p => Ccount_anti X i (Fr r) p ω)
    hGfin h_lim
  simp only [lintegral_zero] at hDC
  have hLlim : Tendsto (fun r => L (Fr r)) atTop (𝓝 (π i * Q - ∑' k, π k * q k i)) := by
    refine tendsto_const_nhds.sub ?_
    simp only [hfi]
    exact hsumm.hasSum.comp (tendsto_atTop_finset_of_monotone hFr_mono hcover)
  have h0 := le_of_tendsto_of_tendsto ((ENNReal.continuous_ofReal.tendsto _).comp hLlim) hDC
    (Eventually.of_forall fun r => hGle (Fr r))
  have h00 := ENNReal.ofReal_eq_zero.1 (le_antisymm h0 bot_le)
  have heq : ∑' k, π k * q k i = π i * Q := le_antisymm hle (by linarith)
  exact heq ▸ hsumm.hasSum

end S202KR

open KellyStochasticNetworks KellyStochasticNetworks.MigrationDynamics MeasureTheory Filter in
theorem solution {Ω S : Type*} [MeasurableSpace Ω]
    [MeasurableSpace S] [MeasurableSingletonClass S] [Countable S] [DecidableEq S]
    (P : Measure Ω) (X : ℝ → Ω → S) (q : S → S → ℝ) (π : S → ℝ)
    (hX : IsMarkovProcess P X q) (hπ : HasStationaryLaw P X π) :
    IsMarkovProcess P (fun t => X (-t)) (KellyStochasticNetworks.reversedRates π q) ∧
    HasStationaryLaw P (fun t => X (-t)) π := by
  obtain ⟨hP, hmeas, hae, hq0, hqd, hqs, hirr, K, hK, hK0, hmk, hlim⟩ := hX
  obtain ⟨-, -, hpos, hπsum, hπt⟩ := hπ
  have hπ0 : ∀ i, 0 ≤ π i := fun i => (hpos i).le
  have hKnn : ∀ h, 0 ≤ h → ∀ i j, 0 ≤ K h i j := fun h hh i j => (hK h hh i).1 j
  have hfb : ∀ i, HasSum (fun k => π k * q k i) (π i * ∑' k, q i k) := fun i =>
    S202KR.full_balance hmeas hmk hπt hπ0 hKnn hlim hae hq0 hqd i
  have hrr : ∀ i j, reversedRates π q i j = π j * q j i / π i := fun _ _ => rfl
  have hrs : ∀ i, HasSum (reversedRates π q i) (∑' k, q i k) := by
    intro i
    have hs := (hfb i).div_const (π i)
    have hv : π i * (∑' k, q i k) / π i = ∑' k, q i k := by field_simp [(hpos i).ne']
    rw [hv] at hs
    exact hs
  refine ⟨⟨hP, fun t => hmeas (-t), ?_, ?_, ?_, ?_, ?_, ?_⟩,
    ⟨hP, fun t => hmeas (-t), hpos, hπsum, fun t i => hπt (-t) i⟩⟩
  · filter_upwards [hae] with ω hω using S202KR.lfjp_neg hω
  · intro i j; rw [hrr]; exact div_nonneg (mul_nonneg (hπ0 j) (hq0 j i)) (hπ0 i)
  · intro i; rw [hrr, hqd, mul_zero, zero_div]
  · intro i
    exact ⟨(hrs i).summable, by rw [(hrs i).tsum_eq]; exact (hqs i).2⟩
  · intro i j
    have h2 := Relation.reflTransGen_swap.2 (hirr j i)
    exact Relation.ReflTransGen.mono (fun a b (hab : 0 < q b a) => by
      rw [hrr]; exact div_pos (mul_pos (hpos b) hab) (hpos a)) _ _ h2
  · refine ⟨fun h i j => π j * K h j i / π i, ?_, ?_, ?_, ?_⟩
    · intro h hh i
      refine ⟨fun j => div_nonneg (mul_nonneg (hπ0 j) (hKnn h hh j i)) (hπ0 i), ?_⟩
      rcases hh.lt_or_eq with hh | hh
      · have := (S202KR.row_hasSum hmeas hmk hπt hπ0 hKnn h hh i).div_const (π i)
        rwa [div_self (hpos i).ne'] at this
      · subst hh
        have : (fun j => π j * K 0 j i / π i) = fun j => if j = i then (1 : ℝ) else 0 := by
          ext j; rw [hK0]; split_ifs with hj
          · subst hj; field_simp [(hpos j).ne']
          · simp
        show HasSum (fun j => π j * K 0 j i / π i) 1
        rw [this]; exact hasSum_ite_eq i 1
    · intro i j
      simp only [hK0]
      by_cases hij : i = j
      · subst hij; simp [(hpos i).ne']
      · simp [hij, Ne.symm hij]
    · exact S202KR.rev_markov hmk hπt hpos
    · intro i j
      by_cases hij : i = j
      · subst hij
        simp only [↓reduceIte]
        rw [(hrs i).tsum_eq]
        have := hlim i i
        simp only [↓reduceIte] at this
        refine this.congr' (Eventually.of_forall fun h => ?_)
        field_simp [(hpos i).ne']
      · simp only [if_neg hij]
        have := (hlim j i).const_mul (π j / π i)
        simp only [if_neg (Ne.symm hij)] at this
        rw [hrr]
        convert this using 1
        · ext h; field_simp [(hpos i).ne']; ring
        · field_simp [(hpos i).ne']
