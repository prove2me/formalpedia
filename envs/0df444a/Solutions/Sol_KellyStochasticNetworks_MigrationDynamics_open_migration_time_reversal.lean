-- Prove2me | solution 1 for KellyStochasticNetworks.MigrationDynamics.open_migration_time_reversal
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T07:45:21.499369+00:00
-- url     : https://prove2.me/submissions/1927bfc8-8e50-4b36-bafd-6afc8ea5215b

import Definitions.Def_KellyStochasticNetworks_MigrationDynamics_OpenProcess
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
theorem KM213.time_rev {Ω S : Type*} [MeasurableSpace Ω]
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


open MeasureTheory Filter Topology

namespace KM213

open KellyStochasticNetworks

variable {J : ℕ}

theorem Tin_eq (k : Fin J) (n : Fin J → ℕ) : Tin k n = Function.update n k (n k + 1) := by
  funext i; by_cases h : i = k
  · subst h; simp [Tin]
  · simp [Tin, h]

theorem Tout_Tin (a : Fin J) (n : Fin J → ℕ) : Tout a (Tin a n) = n := by
  funext i; by_cases h : i = a
  · subst h; simp [Tout, Tin]
  · simp [Tout, Tin, h]

theorem Tin_Tout (a : Fin J) (n : Fin J → ℕ) (h : 1 ≤ n a) : Tin a (Tout a n) = n := by
  funext i; by_cases hi : i = a
  · subst hi; simp [Tout, Tin]; omega
  · simp [Tout, Tin, hi]

theorem Tjk_eq (a b : Fin J) (hab : a ≠ b) (m : Fin J → ℕ) : Tjk a b m = Tin b (Tout a m) := by
  funext i; by_cases hi : i = a
  · subst hi; simp [Tjk, Tout, Tin, hab]
  · by_cases hib : i = b
    · subst hib; simp [Tjk, Tout, Tin, hi]
    · simp [Tjk, Tout, Tin, hi, hib]

theorem Tout_zero (a : Fin J) (n : Fin J → ℕ) (h : n a = 0) : Tout a n = n := by
  funext i; by_cases hi : i = a
  · subst hi; simp [Tout, h]
  · simp [Tout, hi]

theorem sum_Tin (k : Fin J) (n : Fin J → ℕ) : ∑ i, Tin k n i = ∑ i, n i + 1 := by
  rw [Tin_eq, Finset.sum_update_of_mem (Finset.mem_univ _)]
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ k)]
  simp [Finset.sdiff_singleton_eq_erase]; ring

theorem sum_Tout_le (a : Fin J) (n : Fin J → ℕ) : ∑ i, Tout a n i ≤ ∑ i, n i :=
  Finset.sum_le_sum fun i _ => by
    unfold Tout; split_ifs with h
    · subst h; omega
    · exact le_rfl

section rho
variable (α : Fin J → ℝ) (φ : Fin J → ℕ → ℝ)

noncomputable def rho (n : Fin J → ℕ) : ℝ := ∏ j, α j ^ n j / phiProd φ j (n j)

variable {α φ}

theorem phiProd_pos (hφpos : ∀ j r, 0 < r → 0 < φ j r) (j : Fin J) (m : ℕ) :
    0 < phiProd φ j m :=
  Finset.prod_pos fun r hr => hφpos j r (by simp at hr; omega)

theorem rho_pos (hα : ∀ j, 0 < α j) (hφpos : ∀ j r, 0 < r → 0 < φ j r) (n : Fin J → ℕ) :
    0 < rho α φ n :=
  Finset.prod_pos fun j _ => div_pos (pow_pos (hα j) _) (phiProd_pos hφpos j _)

theorem rho_Tin (hφpos : ∀ j r, 0 < r → 0 < φ j r) (k : Fin J) (n : Fin J → ℕ) :
    rho α φ (Tin k n) * φ k (n k + 1) = α k * rho α φ n := by
  unfold rho
  rw [Fintype.prod_eq_mul_prod_compl k, Fintype.prod_eq_mul_prod_compl k (fun j => α j ^ n j / _)]
  have hrest : ∏ j ∈ {k}ᶜ, α j ^ Tin k n j / phiProd φ j (Tin k n j) =
      ∏ j ∈ {k}ᶜ, α j ^ n j / phiProd φ j (n j) := by
    refine Finset.prod_congr rfl fun j hj => ?_
    have : j ≠ k := by simpa using hj
    simp [Tin, this]
  rw [hrest]
  have hk : Tin k n k = n k + 1 := by simp [Tin]
  rw [hk]
  have hpp : phiProd φ k (n k + 1) = phiProd φ k (n k) * φ k (n k + 1) := by
    unfold phiProd; rw [Finset.prod_Icc_succ_top (by omega)]
  rw [hpp]
  have h1 := phiProd_pos hφpos k (n k)
  have h2 := hφpos k (n k + 1) (by omega)
  field_simp
  ring

variable (lam : Fin J → Fin J → ℝ) (mu nu : Fin J → ℝ)

theorem term1 (hlamdiag : ∀ j, lam j j = 0) (hφ0 : ∀ j, φ j 0 = 0)
    (hφpos : ∀ j r, 0 < r → 0 < φ j r) (hα : ∀ j, 0 < α j) (a b : Fin J) (m n : Fin J → ℕ) :
    rho α φ m * (if n = Tjk a b m then lam a b * φ a (m a) else 0) =
      rho α φ n * (if m = Tjk b a n then α a * lam a b / α b * φ b (n b) else 0) := by
  by_cases hab : a = b
  · subst hab; simp [hlamdiag]
  by_cases h : ∃ p, m = Tin a p ∧ n = Tin b p
  · obtain ⟨p, rfl, rfl⟩ := h
    rw [if_pos (by rw [Tjk_eq a b hab, Tout_Tin]), if_pos (by rw [Tjk_eq b a (Ne.symm hab), Tout_Tin])]
    have ha : Tin a p a = p a + 1 := by simp [Tin]
    have hb : Tin b p b = p b + 1 := by simp [Tin]
    rw [ha, hb]
    have e1 := rho_Tin (α := α) hφpos a p
    have e2 := rho_Tin (α := α) hφpos b p
    have := hα b
    calc rho α φ (Tin a p) * (lam a b * φ a (p a + 1))
        = lam a b * (rho α φ (Tin a p) * φ a (p a + 1)) := by ring
      _ = lam a b * (α a * rho α φ p) := by rw [e1]
      _ = α a * lam a b / α b * (rho α φ (Tin b p) * φ b (p b + 1)) := by
          rw [e2]; field_simp
      _ = _ := by ring
  · push Not at h
    have hl : (if n = Tjk a b m then lam a b * φ a (m a) else 0) = 0 := by
      split_ifs with hn
      · by_cases hma : m a = 0
        · simp [hma, hφ0]
        · exfalso
          refine h (Tout a m) (Tin_Tout a m (by omega)).symm ?_
          rw [hn, Tjk_eq a b hab]
      · rfl
    have hr : (if m = Tjk b a n then α a * lam a b / α b * φ b (n b) else 0) = 0 := by
      split_ifs with hm
      · by_cases hnb : n b = 0
        · simp [hnb, hφ0]
        · exfalso
          refine h (Tout b n) ?_ (Tin_Tout b n (by omega)).symm
          rw [hm, Tjk_eq b a (Ne.symm hab)]
      · rfl
    rw [hl, hr]; simp

theorem term2 (hφ0 : ∀ j, φ j 0 = 0) (hφpos : ∀ j r, 0 < r → 0 < φ j r) (a : Fin J)
    (m n : Fin J → ℕ) :
    rho α φ m * (if n = Tout a m then mu a * φ a (m a) else 0) =
      rho α φ n * (if m = Tin a n then α a * mu a else 0) := by
  by_cases h : m = Tin a n
  · subst h
    rw [if_pos (Tout_Tin a n).symm, if_pos rfl]
    have ha : Tin a n a = n a + 1 := by simp [Tin]
    rw [ha]
    have e1 := rho_Tin (α := α) hφpos a n
    calc rho α φ (Tin a n) * (mu a * φ a (n a + 1))
        = mu a * (rho α φ (Tin a n) * φ a (n a + 1)) := by ring
      _ = _ := by rw [e1]; ring
  · rw [if_neg h]
    split_ifs with hn
    · by_cases hma : m a = 0
      · simp [hma, hφ0]
      · exfalso; exact h (by rw [hn, Tin_Tout a m (by omega)])
    · simp

theorem term3 (hφ0 : ∀ j, φ j 0 = 0) (hφpos : ∀ j r, 0 < r → 0 < φ j r) (hα : ∀ j, 0 < α j)
    (b : Fin J) (m n : Fin J → ℕ) :
    rho α φ m * (if n = Tin b m then nu b else 0) =
      rho α φ n * (if m = Tout b n then nu b / α b * φ b (n b) else 0) := by
  by_cases h : n = Tin b m
  · subst h
    rw [if_pos rfl, if_pos (Tout_Tin b m).symm]
    have hb : Tin b m b = m b + 1 := by simp [Tin]
    rw [hb]
    have e1 := rho_Tin (α := α) hφpos b m
    have := hα b
    calc rho α φ m * nu b = nu b / α b * (α b * rho α φ m) := by field_simp
      _ = _ := by rw [← e1]; ring
  · rw [if_neg h]
    split_ifs with hm
    · by_cases hnb : n b = 0
      · simp [hnb, hφ0]
      · exfalso; exact h (by rw [hm, Tin_Tout b n (by omega)])
    · simp

/-- reversed open migration rates -/
noncomputable def revLam (α : Fin J → ℝ) (lam : Fin J → Fin J → ℝ) : Fin J → Fin J → ℝ :=
  fun j k => α k * lam k j / α j

theorem rho_detailed (hlamdiag : ∀ j, lam j j = 0) (hφ0 : ∀ j, φ j 0 = 0)
    (hφpos : ∀ j r, 0 < r → 0 < φ j r) (hα : ∀ j, 0 < α j) (m n : Fin J → ℕ) :
    rho α φ m * openMigrationRates lam mu nu φ m n =
      rho α φ n * openMigrationRates (revLam α lam) (fun j => nu j / α j)
        (fun k => α k * mu k) φ n m := by
  unfold openMigrationRates closedMigrationRates
  simp only [mul_add, Finset.mul_sum]
  rw [Finset.sum_comm (f := fun j k => rho α φ n * (if m = Tjk j k n then revLam α lam j k * φ j (n j) else 0))]
  have h1 : ∀ a b, rho α φ m * (if n = Tjk a b m then lam a b * φ a (m a) else 0) =
      rho α φ n * (if m = Tjk b a n then revLam α lam b a * φ b (n b) else 0) :=
    fun a b => term1 lam hlamdiag hφ0 hφpos hα a b m n
  have h2 : ∀ a, rho α φ m * (if n = Tout a m then mu a * φ a (m a) else 0) =
      rho α φ n * (if m = Tin a n then α a * mu a else 0) := fun a => term2 mu hφ0 hφpos a m n
  have h3 : ∀ b, rho α φ m * (if n = Tin b m then nu b else 0) =
      rho α φ n * (if m = Tout b n then nu b / α b * φ b (n b) else 0) :=
    fun b => term3 nu hφ0 hφpos hα b m n
  simp only [h1, h2, h3]
  ring

end rho

/-- row sums of open migration rates -/
theorem rate_hasSum (lam : Fin J → Fin J → ℝ) (mu nu : Fin J → ℝ) (φ : Fin J → ℕ → ℝ)
    (n : Fin J → ℕ) :
    HasSum (openMigrationRates lam mu nu φ n)
      ((∑ j, ∑ k, lam j k * φ j (n j)) + (∑ j, mu j * φ j (n j)) + ∑ k, nu k) := by
  unfold openMigrationRates closedMigrationRates
  refine ((hasSum_sum fun j _ => hasSum_sum fun k _ => hasSum_ite_eq _ _).add
    (hasSum_sum fun j _ => hasSum_ite_eq _ _)).add (hasSum_sum fun k _ => hasSum_ite_eq _ _)
end KM213

set_option linter.unusedSectionVars false

namespace KM213

open KellyStochasticNetworks

variable {J : ℕ}

section traffic
variable (lam : Fin J → Fin J → ℝ) (mu nu : Fin J → ℝ) (φ : Fin J → ℕ → ℝ)

theorem pos_rate (hlam0 : ∀ j k, 0 ≤ lam j k) (hmu0 : ∀ j, 0 ≤ mu j) (hnu0 : ∀ j, 0 ≤ nu j)
    (hφ0 : ∀ j, φ j 0 = 0) (n m : Fin J → ℕ) (h : 0 < openMigrationRates lam mu nu φ n m) :
    (∃ a b, m = Tjk a b n ∧ 0 < lam a b ∧ 0 < n a) ∨ (∃ a, m = Tout a n ∧ 0 < mu a ∧ 0 < n a) ∨
      (∃ b, m = Tin b n ∧ 0 < nu b) := by
  by_contra hc
  have h1 : ∀ a b, m = Tjk a b n → 0 < lam a b → n a = 0 := fun a b e l => by
    by_contra hn; exact hc (Or.inl ⟨a, b, e, l, Nat.pos_of_ne_zero hn⟩)
  have h2 : ∀ a, m = Tout a n → 0 < mu a → n a = 0 := fun a e l => by
    by_contra hn; exact hc (Or.inr (Or.inl ⟨a, e, l, Nat.pos_of_ne_zero hn⟩))
  have h3 : ∀ b, m = Tin b n → ¬ 0 < nu b := fun b e l => hc (Or.inr (Or.inr ⟨b, e, l⟩))
  refine absurd h (not_lt.2 (le_of_eq ?_))
  unfold openMigrationRates closedMigrationRates
  rw [Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ => ?_,
    Finset.sum_eq_zero fun a _ => ?_, Finset.sum_eq_zero fun b _ => ?_]
  · simp
  · split_ifs with e
    · exact le_antisymm (not_lt.1 (h3 b e)) (hnu0 b)
    · rfl
  · split_ifs with e
    · by_cases l : 0 < mu a
      · simp [h2 a e l, hφ0]
      · simp [le_antisymm (not_lt.1 l) (hmu0 a)]
    · rfl
  · split_ifs with e
    · by_cases l : 0 < lam a b
      · simp [h1 a b e l, hφ0]
      · simp [le_antisymm (not_lt.1 l) (hlam0 a b)]
    · rfl

variable (hlam0 : ∀ j k, 0 ≤ lam j k) (hmu0 : ∀ j, 0 ≤ mu j) (hnu0 : ∀ j, 0 ≤ nu j)
    (hφ0 : ∀ j, φ j 0 = 0) (hlamdiag : ∀ j, lam j j = 0)
    (hirr : ∀ i j, Relation.ReflTransGen (fun a b => 0 < openMigrationRates lam mu nu φ a b) i j)
include hlam0 hmu0 hnu0 hφ0 hlamdiag hirr

theorem closed_empty (N : Finset (Fin J)) (hN : ∀ k ∈ N, mu k = 0 ∧ ∀ j ∉ N, lam k j = 0) :
    N = ∅ := by
  by_contra hne
  obtain ⟨k, hk⟩ := Finset.nonempty_iff_ne_empty.2 hne
  have inv : ∀ a b, Relation.ReflTransGen (fun a b => 0 < openMigrationRates lam mu nu φ a b) a b →
      (∃ l ∈ N, 0 < a l) → ∃ l ∈ N, 0 < b l := by
    intro a b hab ha
    induction hab with
    | refl => exact ha
    | @tail b c _ hbc ih =>
      obtain ⟨l, hl, hpos⟩ := ih
      rcases pos_rate lam mu nu φ hlam0 hmu0 hnu0 hφ0 b c hbc with
        ⟨a', b', rfl, hlab, hna⟩ | ⟨a', rfl, hmu, hna⟩ | ⟨b', rfl, hnu⟩
      · by_cases hla : l = a'
        · subst hla
          have hb : b' ∈ N := by
            by_contra hb; rw [(hN l hl).2 b' hb] at hlab; exact lt_irrefl _ hlab
          have hne' : b' ≠ l := by rintro rfl; rw [hlamdiag] at hlab; exact lt_irrefl _ hlab
          exact ⟨b', hb, by simp [Tjk, hne']⟩
        · refine ⟨l, hl, ?_⟩
          simp only [Tjk, hla, if_false]; split_ifs <;> omega
      · by_cases hla : l = a'
        · subst hla; rw [(hN l hl).1] at hmu; exact absurd hmu (lt_irrefl _)
        · exact ⟨l, hl, by simp [Tout, hla]; omega⟩
      · refine ⟨l, hl, ?_⟩
        simp only [Tin]; split_ifs <;> omega
  obtain ⟨l, _, hl⟩ := inv _ _ (hirr (Tin k (fun _ => 0)) (fun _ => 0)) ⟨k, hk, by simp [Tin]⟩
  exact lt_irrefl _ hl

theorem source_empty (Z : Finset (Fin J)) (hZ : ∀ j ∈ Z, nu j = 0 ∧ ∀ k ∉ Z, lam k j = 0) :
    Z = ∅ := by
  by_contra hne
  obtain ⟨j, hj⟩ := Finset.nonempty_iff_ne_empty.2 hne
  have inv : ∀ a b, Relation.ReflTransGen (fun a b => 0 < openMigrationRates lam mu nu φ a b) a b →
      (∀ l ∈ Z, a l = 0) → ∀ l ∈ Z, b l = 0 := by
    intro a b hab ha
    induction hab with
    | refl => exact ha
    | @tail b c _ hbc ih =>
      intro l hl
      rcases pos_rate lam mu nu φ hlam0 hmu0 hnu0 hφ0 b c hbc with
        ⟨a', b', rfl, hlab, hna⟩ | ⟨a', rfl, hmu, hna⟩ | ⟨b', rfl, hnu⟩
      · have hla : l ≠ a' := by rintro rfl; rw [ih l hl] at hna; exact lt_irrefl _ hna
        have hlb : l ≠ b' := by
          rintro rfl
          have ha' : a' ∈ Z := by
            by_contra ha'; rw [(hZ l hl).2 a' ha'] at hlab; exact lt_irrefl _ hlab
          rw [ih a' ha'] at hna; exact lt_irrefl _ hna
        simp [Tjk, hla, hlb, ih l hl]
      · have hla : l ≠ a' := by rintro rfl; rw [ih l hl] at hna; exact lt_irrefl _ hna
        simp [Tout, hla, ih l hl]
      · have hlb : l ≠ b' := by rintro rfl; rw [(hZ l hl).1] at hnu; exact lt_irrefl _ hnu
        simp [Tin, hlb, ih l hl]
  have := inv _ _ (hirr (fun _ => 0) (Tin j (fun _ => 0))) (fun _ _ => rfl) j hj
  simp [Tin] at this

theorem traffic_exists : ∃ α : Fin J → ℝ, (∀ j, 0 < α j) ∧ OpenTraffic lam mu nu α := by
  set A : Matrix (Fin J) (Fin J) ℝ :=
    Matrix.of fun j k => (if j = k then mu j + ∑ l, lam j l else 0) - lam k j with hAdef
  have hA : ∀ x j, (A.mulVec x) j = x j * (mu j + ∑ k, lam j k) - ∑ k, x k * lam k j := by
    intro x j
    simp only [hAdef, Matrix.mulVec, dotProduct, Matrix.of_apply, sub_mul, Finset.sum_sub_distrib,
      ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    rw [mul_comm]; congr 1; exact Finset.sum_congr rfl fun k _ => mul_comm _ _
  have NN : ∀ x : Fin J → ℝ, (∀ j, 0 ≤ (A.mulVec x) j) → ∀ j, 0 ≤ x j := by
    intro x hx
    by_contra hneg
    push Not at hneg
    obtain ⟨j0, hj0⟩ := hneg
    set N := Finset.univ.filter (fun j => x j < 0) with hNdef
    have hmemN : ∀ j, j ∈ N ↔ x j < 0 := fun j => by simp [hNdef]
    have hsum : 0 ≤ ∑ j ∈ N, (A.mulVec x) j := Finset.sum_nonneg fun j _ => hx j
    have hexp : ∀ j, (A.mulVec x) j = x j * mu j + (∑ k ∈ N, x j * lam j k + ∑ k ∈ Nᶜ, x j * lam j k)
        - (∑ k ∈ N, x k * lam k j + ∑ k ∈ Nᶜ, x k * lam k j) := by
      intro j
      rw [hA, Finset.sum_add_sum_compl, Finset.sum_add_sum_compl, mul_add, Finset.mul_sum]
    have hcomm : ∑ j ∈ N, ∑ k ∈ N, x j * lam j k = ∑ j ∈ N, ∑ k ∈ N, x k * lam k j :=
      Finset.sum_comm
    have hpos5 : 0 ≤ ∑ j ∈ N, ∑ k ∈ Nᶜ, x k * lam k j :=
      Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun k hk => by
        have : ¬ x k < 0 := by rw [← hmemN]; simpa using hk
        exact mul_nonneg (not_lt.1 this) (hlam0 k j)
    set T := ∑ j ∈ N, (x j * mu j + ∑ k ∈ Nᶜ, x j * lam j k) with hT
    have hle : ∑ j ∈ N, (A.mulVec x) j ≤ T := by
      simp only [hexp, Finset.sum_sub_distrib, Finset.sum_add_distrib, hT] at *
      linarith
    have hterm : ∀ j ∈ N, x j * mu j + ∑ k ∈ Nᶜ, x j * lam j k ≤ 0 := by
      intro j hj
      have hxj := (hmemN j).1 hj
      have : ∑ k ∈ Nᶜ, x j * lam j k ≤ 0 :=
        Finset.sum_nonpos fun k _ => mul_nonpos_of_nonpos_of_nonneg hxj.le (hlam0 j k)
      nlinarith [hmu0 j]
    have hT0 : T = 0 := le_antisymm (Finset.sum_nonpos hterm) (hsum.trans hle)
    have hall := (Finset.sum_eq_zero_iff_of_nonpos hterm).1 hT0
    have hNe := closed_empty lam mu nu φ hlam0 hmu0 hnu0 hφ0 hlamdiag hirr N (by
      intro k hk
      have hxk := (hmemN k).1 hk
      have h0 := hall k hk
      have hA1 : x k * mu k ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hxk.le (hmu0 k)
      have hA2 : ∑ l ∈ Nᶜ, x k * lam k l ≤ 0 :=
        Finset.sum_nonpos fun l _ => mul_nonpos_of_nonpos_of_nonneg hxk.le (hlam0 k l)
      have e1 : x k * mu k = 0 := by linarith
      have e2 : ∑ l ∈ Nᶜ, x k * lam k l = 0 := by linarith
      refine ⟨(mul_eq_zero.1 e1).resolve_left hxk.ne, fun j hj => ?_⟩
      have := (Finset.sum_eq_zero_iff_of_nonpos fun l _ =>
        mul_nonpos_of_nonpos_of_nonneg hxk.le (hlam0 k l)).1 e2 j (by simpa using hj)
      exact (mul_eq_zero.1 this).resolve_left hxk.ne)
    have : j0 ∈ N := (hmemN j0).2 hj0
    rw [hNe] at this; simp at this
  have hinj : Function.Injective (Matrix.toLin' A) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    rw [Matrix.toLin'_apply] at hx
    have h1 := NN x (fun j => by rw [hx]; rfl)
    have h2 := NN (-x) (fun j => by rw [Matrix.mulVec_neg, hx]; simp)
    funext j; have := h2 j; simp at this; exact le_antisymm this (h1 j)
  obtain ⟨α, hα⟩ := LinearMap.injective_iff_surjective.1 hinj nu
  rw [Matrix.toLin'_apply] at hα
  have hα0 := NN α (fun j => by rw [hα]; exact hnu0 j)
  have htr : ∀ j, α j * (mu j + ∑ k, lam j k) = nu j + ∑ k, α k * lam k j := by
    intro j; have := hA α j; rw [hα] at this; linarith
  refine ⟨α, ?_, htr⟩
  set Z := Finset.univ.filter (fun j => α j = 0) with hZdef
  have hZ := source_empty lam mu nu φ hlam0 hmu0 hnu0 hφ0 hlamdiag hirr Z (by
    intro j hj
    have hj0 : α j = 0 := by simpa [hZdef] using hj
    have h := htr j
    rw [hj0, zero_mul] at h
    have hs : 0 ≤ ∑ k, α k * lam k j := Finset.sum_nonneg fun k _ => mul_nonneg (hα0 k) (hlam0 k j)
    have e1 : nu j = 0 := by linarith [hnu0 j]
    have e2 : ∑ k, α k * lam k j = 0 := by linarith [hnu0 j]
    refine ⟨e1, fun k hk => ?_⟩
    have := (Finset.sum_eq_zero_iff_of_nonneg fun k _ => mul_nonneg (hα0 k) (hlam0 k j)).1 e2 k
      (Finset.mem_univ _)
    have hk0 : α k ≠ 0 := by simpa [hZdef] using hk
    exact (mul_eq_zero.1 this).resolve_left hk0)
  intro j
  rcases (hα0 j).lt_or_eq with h | h
  · exact h
  · exfalso
    have : j ∈ Z := by simp [hZdef, h.symm]
    rw [hZ] at this; simp at this

end traffic

end KM213

namespace KM213

open KellyStochasticNetworks

def box (J N : ℕ) : Finset (Fin J → ℕ) :=
  (Fintype.piFinset fun _ : Fin J => Finset.range (N + 1)).filter (fun m => ∑ i, m i ≤ N)

theorem mem_box {J N : ℕ} (m : Fin J → ℕ) : m ∈ box J N ↔ ∑ i, m i ≤ N := by
  simp only [box, Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_range]
  constructor
  · exact fun h => h.2
  · intro h; refine ⟨fun i => ?_, h⟩
    have := Finset.single_le_sum (f := m) (fun i _ => Nat.zero_le _) (Finset.mem_univ i)
    omega

theorem box_mono (J : ℕ) : Monotone (box J) := fun a b hab x hx => by
  rw [mem_box] at *; omega

variable {J : ℕ}

theorem sum_Tjk (a b : Fin J) (hab : a ≠ b) (n : Fin J → ℕ) (h : 1 ≤ n a) :
    ∑ i, Tjk a b n i = ∑ i, n i := by
  have e2 := sum_Tin a (Tout a n)
  rw [Tin_Tout a n h] at e2
  rw [Tjk_eq a b hab, sum_Tin, e2]

theorem Tjk_self (a : Fin J) (n : Fin J → ℕ) : Tjk a a n = Tout a n := by
  funext i; by_cases h : i = a
  · subst h; simp [Tjk, Tout]
  · simp [Tjk, Tout, h]

section flux
variable (lam : Fin J → Fin J → ℝ) (mu nu : Fin J → ℝ) (φ : Fin J → ℕ → ℝ)

theorem rate_out (hφ0 : ∀ j, φ j 0 = 0) (N : ℕ) (n m : Fin J → ℕ) (hn : ∑ i, n i ≤ N)
    (hm : m ∉ box J N) :
    openMigrationRates lam mu nu φ n m = ∑ k, (if m = Tin k n then nu k else 0) := by
  unfold openMigrationRates closedMigrationRates
  rw [Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ => ?_,
    Finset.sum_eq_zero fun a _ => ?_]
  · simp
  · split_ifs with e
    · exfalso; apply hm; rw [mem_box, e]; exact (sum_Tout_le a n).trans hn
    · rfl
  · split_ifs with e
    · by_cases hna : n a = 0
      · simp [hna, hφ0]
      · exfalso; apply hm; rw [mem_box, e]
        by_cases hab : a = b
        · subst hab; rw [Tjk_self]; exact (sum_Tout_le a n).trans hn
        · rw [sum_Tjk a b hab n (by omega)]; exact hn
    · rfl

theorem rate_out_zero (N : ℕ) (n m : Fin J → ℕ) (hn : ∑ i, n i < N) (hm : m ∉ box J N)
    (k : Fin J) : m ≠ Tin k n := by
  intro e; apply hm; rw [mem_box, e, sum_Tin]; omega

theorem out_le (hφ0 : ∀ j, φ j 0 = 0) (hnu0 : ∀ j, 0 ≤ nu j)
    (hq0 : ∀ n m, 0 ≤ openMigrationRates lam mu nu φ n m) (N : ℕ) (n : Fin J → ℕ)
    (hn : ∑ i, n i ≤ N) :
    ∑' m, (if m ∈ box J N then 0 else openMigrationRates lam mu nu φ n m) ≤
      if ∑ i, n i = N then ∑ k, nu k else 0 := by
  by_cases hN : ∑ i, n i = N
  · rw [if_pos hN]
    have hR : HasSum (fun m => ∑ k, (if m = Tin k n then nu k else 0)) (∑ k, nu k) :=
      hasSum_sum fun k _ => hasSum_ite_eq _ _
    rw [← hR.tsum_eq]
    refine Summable.tsum_le_tsum (fun m => ?_) ?_ hR.summable
    · split_ifs with hm
      · exact Finset.sum_nonneg fun k _ => by split_ifs; exacts [hnu0 k, le_rfl]
      · exact le_of_eq (rate_out lam mu nu φ hφ0 N n m hn hm)
    · refine Summable.of_nonneg_of_le (fun m => ?_) (fun m => ?_)
        (rate_hasSum lam mu nu φ n).summable
      · split_ifs; exacts [le_rfl, hq0 n m]
      · split_ifs; exacts [hq0 n m, le_rfl]
  · rw [if_neg hN]
    have : (fun m => if m ∈ box J N then 0 else openMigrationRates lam mu nu φ n m) =
        fun _ => 0 := by
      funext m
      split_ifs with hm
      · rfl
      · rw [rate_out lam mu nu φ hφ0 N n m hn hm]
        exact Finset.sum_eq_zero fun k _ =>
          if_neg (rate_out_zero N n m (lt_of_le_of_ne hn hN) hm k)
    rw [this, tsum_zero]

theorem Qstar_eq (α : Fin J → ℝ) (hα : ∀ j, 0 < α j) (htr : OpenTraffic lam mu nu α)
    (n : Fin J → ℕ) :
    (∑ j, ∑ k, revLam α lam j k * φ j (n j)) + (∑ j, nu j / α j * φ j (n j)) +
        ∑ k, α k * mu k =
      (∑ j, ∑ k, lam j k * φ j (n j)) + (∑ j, mu j * φ j (n j)) + ∑ k, nu k := by
  have hj : ∀ j, ∑ k, revLam α lam j k * φ j (n j) + nu j / α j * φ j (n j) =
      ∑ k, lam j k * φ j (n j) + mu j * φ j (n j) := by
    intro j
    simp only [revLam]
    rw [← Finset.sum_mul, ← Finset.sum_mul, ← add_mul, ← add_mul]
    congr 1
    rw [← Finset.sum_div, ← add_div, div_eq_iff (hα j).ne']
    linarith [htr j]
  have hsum : ∑ k, α k * mu k = ∑ k, nu k := by
    have := Finset.sum_congr rfl (fun j (_ : j ∈ Finset.univ) => htr j)
    simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum] at this
    have hc : ∑ j, ∑ k, α j * lam j k = ∑ j, ∑ k, α k * lam k j := Finset.sum_comm
    linarith
  have := Finset.sum_congr rfl (fun j (_ : j ∈ Finset.univ) => hj j)
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib] at this
  linarith

end flux

end KM213


open Filter Topology

namespace KM213

variable {S : Type*} [DecidableEq S]

/-- uniqueness of invariant measures, generic box version -/
theorem ratio_const (q : S → S → ℝ) (Q π ρ : S → ℝ) (hq0 : ∀ i j, 0 ≤ q i j)
    (hQ : ∀ i, HasSum (q i) (Q i)) (hπ : ∀ i, 0 < π i) (hρ : ∀ i, 0 < ρ i)
    (hfbπ : ∀ i, HasSum (fun j => π j * q j i) (π i * Q i))
    (hfbρ : ∀ i, HasSum (fun j => ρ j * q j i) (ρ i * Q i))
    (B : ℕ → Finset S) (hB : ∀ i, ∃ N0, ∀ N, N0 ≤ N → i ∈ B N) (ε : ℕ → ℝ)
    (hε : Tendsto ε atTop (𝓝 0))
    (hout : ∀ N, ∑ j ∈ B N, π j * (∑' i, if i ∈ B N then 0 else q j i) ≤ ε N)
    (hirr : ∀ i j, Relation.ReflTransGen (fun a b => 0 < q a b) i j) :
    ∀ i j, ρ i / π i = ρ j / π j := by
  set h : S → ℝ := fun i => ρ i / π i with hh
  -- key step: q j i > 0 → h i ≤ h j
  have key : ∀ i0 j, 0 < q j i0 → h i0 ≤ h j := by
    intro i0
    set c := h i0
    have hc : 0 < c := div_pos (hρ i0) (hπ i0)
    set f : S → ℝ := fun j => min (h j) c with hf
    have hπf : ∀ j, π j * f j ≤ ρ j := fun j => by
      have := min_le_left (h j) c
      calc π j * f j ≤ π j * h j := mul_le_mul_of_nonneg_left this (hπ j).le
        _ = ρ j := by simp only [hh]; field_simp [(hπ j).ne']
    have hfc : ∀ j, f j ≤ c := fun j => min_le_right _ _
    have hf0 : ∀ j, 0 ≤ f j := fun j => le_min (div_pos (hρ j) (hπ j)).le hc.le
    have hsf : ∀ i, Summable (fun j => π j * q j i * f j) := fun i =>
      Summable.of_nonneg_of_le (fun j => mul_nonneg (mul_nonneg (hπ j).le (hq0 j i)) (hf0 j))
        (fun j => mul_le_mul_of_nonneg_left (hfc j) (mul_nonneg (hπ j).le (hq0 j i)))
        ((hfbπ i).summable.mul_right c)
    set d : S → ℝ := fun i => π i * Q i * f i - ∑' j, π j * q j i * f j with hd
    have hQ0 : ∀ i, 0 ≤ Q i := fun i => (hQ i).nonneg fun j => hq0 i j
    have hd0 : ∀ i, 0 ≤ d i := by
      intro i
      have a1 : ∑' j, π j * q j i * f j ≤ ρ i * Q i := by
        rw [← (hfbρ i).tsum_eq]
        refine (hsf i).tsum_le_tsum (fun j => ?_) (hfbρ i).summable
        calc π j * q j i * f j = (π j * f j) * q j i := by ring
          _ ≤ ρ j * q j i := mul_le_mul_of_nonneg_right (hπf j) (hq0 j i)
      have a2 : ∑' j, π j * q j i * f j ≤ c * (π i * Q i) := by
        rw [← (hfbπ i).tsum_eq, ← tsum_mul_left]
        refine (hsf i).tsum_le_tsum (fun j => ?_) ((hfbπ i).summable.mul_left c)
        calc π j * q j i * f j ≤ π j * q j i * c :=
              mul_le_mul_of_nonneg_left (hfc j) (mul_nonneg (hπ j).le (hq0 j i))
          _ = _ := by ring
      have e : π i * Q i * f i = min (ρ i * Q i) (c * (π i * Q i)) := by
        simp only [hf, hh]
        rw [mul_min_of_nonneg _ _ (mul_nonneg (hπ i).le (hQ0 i))]
        congr 1
        · field_simp [(hπ i).ne']
        · ring
      simp only [hd]; rw [e]; linarith [le_min a1 a2]
    -- box estimate
    have hbox : ∀ N, ∑ i ∈ B N, d i ≤ c * ε N := by
      intro N
      set out : S → ℝ := fun j => ∑' i, if i ∈ B N then 0 else q j i with hout_def
      have hsplit : ∀ j, ∑ i ∈ B N, q j i = Q j - out j := by
        intro j
        have h1 : HasSum (fun i => if i ∈ B N then q j i else 0) (∑ i ∈ B N, q j i) := by
          have : HasSum (fun i => if i ∈ B N then q j i else 0)
              (∑ i ∈ B N, if i ∈ B N then q j i else 0) :=
            hasSum_sum_of_ne_finset_zero (fun b hb => by simp [hb])
          rwa [Finset.sum_congr rfl fun i (hi : i ∈ B N) => (if_pos hi : (if i ∈ B N then q j i else 0) = q j i)] at this
        have h2 := (hQ j).sub h1
        have : (fun i => q j i - if i ∈ B N then q j i else 0) =
            fun i => if i ∈ B N then 0 else q j i := by
          funext i; split_ifs <;> simp
        rw [this] at h2
        simp only [hout_def]; rw [h2.tsum_eq]; ring
      have hout0 : ∀ j, 0 ≤ out j := fun j =>
        tsum_nonneg fun i => by split_ifs; exacts [le_rfl, hq0 j i]
      have hswap : ∑ i ∈ B N, ∑' j, π j * q j i * f j = ∑' j, ∑ i ∈ B N, π j * q j i * f j :=
        (Summable.tsum_finsetSum fun i _ => hsf i).symm
      have hsum2 : Summable (fun j => ∑ i ∈ B N, π j * q j i * f j) :=
        summable_sum fun i _ => hsf i
      have hge : ∑ j ∈ B N, ∑ i ∈ B N, π j * q j i * f j ≤
          ∑' j, ∑ i ∈ B N, π j * q j i * f j :=
        hsum2.sum_le_tsum _ fun j _ => Finset.sum_nonneg fun i _ =>
          mul_nonneg (mul_nonneg (hπ j).le (hq0 j i)) (hf0 j)
      have hin : ∀ j, ∑ i ∈ B N, π j * q j i * f j = π j * f j * (Q j - out j) := by
        intro j; rw [← hsplit, Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by ring
      have hge' : ∑ j ∈ B N, π j * f j * (Q j - out j) ≤
          ∑' j, ∑ i ∈ B N, π j * q j i * f j := by
        rw [Finset.sum_congr rfl (fun j _ => (hin j).symm)]; exact hge
      have hdsum : ∑ i ∈ B N, d i = ∑ i ∈ B N, π i * Q i * f i -
          ∑ i ∈ B N, ∑' j, π j * q j i * f j := by
        simp only [hd, Finset.sum_sub_distrib]
      rw [hdsum, hswap]
      have hfin : ∑ i ∈ B N, π i * Q i * f i - ∑ j ∈ B N, π j * f j * (Q j - out j) =
          ∑ j ∈ B N, π j * f j * out j := by
        rw [← Finset.sum_sub_distrib]; exact Finset.sum_congr rfl fun j _ => by ring
      have hle2 : ∑ j ∈ B N, π j * f j * out j ≤ c * ∑ j ∈ B N, π j * out j := by
        rw [Finset.mul_sum]
        refine Finset.sum_le_sum fun j _ => ?_
        calc π j * f j * out j = f j * (π j * out j) := by ring
          _ ≤ c * (π j * out j) :=
            mul_le_mul_of_nonneg_right (hfc j) (mul_nonneg (hπ j).le (hout0 j))
      have h3 : ∑ j ∈ B N, π j * out j ≤ ε N := hout N
      have := mul_le_mul_of_nonneg_left h3 hc.le
      linarith
    have hdi0 : d i0 ≤ 0 := by
      obtain ⟨N0, hN0⟩ := hB i0
      have hlim : Tendsto (fun N => c * ε N) atTop (𝓝 0) := by
        simpa using hε.const_mul c
      refine ge_of_tendsto hlim (eventually_atTop.2 ⟨N0, fun N hN => ?_⟩)
      calc d i0 ≤ ∑ i ∈ B N, d i :=
            Finset.single_le_sum (fun i _ => hd0 i) (hN0 N hN)
        _ ≤ c * ε N := hbox N
    have hdz : d i0 = 0 := le_antisymm hdi0 (hd0 i0)
    -- consequence: all terms π j q j i0 (c - f j) vanish
    have hfi0 : f i0 = c := min_eq_right le_rfl
    have hz : HasSum (fun j => π j * q j i0 * (c - f j)) 0 := by
      have h1 := ((hfbπ i0).mul_left c).sub (hsf i0).hasSum
      have : c * (π i0 * Q i0) - ∑' j, π j * q j i0 * f j = 0 := by
        simp only [hd] at hdz; rw [hfi0] at hdz; linarith
      rw [this] at h1
      have e : (fun j => π j * q j i0 * (c - f j)) =
          fun b => c * (π b * q b i0) - π b * q b i0 * f b := by funext j; ring
      rw [e]; exact h1
    have hz' := (hasSum_zero_iff_of_nonneg fun j =>
      mul_nonneg (mul_nonneg (hπ j).le (hq0 j i0)) (sub_nonneg.2 (hfc j))).1 hz
    intro j hj
    have := congrFun hz' j
    simp only [Pi.zero_apply] at this
    have hne : π j * q j i0 ≠ 0 := (mul_pos (hπ j) hj).ne'
    have hfj : f j = c := by
      have := (mul_eq_zero.1 this).resolve_left hne; linarith
    have : c ≤ h j := by
      by_contra hlt; push Not at hlt
      have : f j = h j := min_eq_left hlt.le
      linarith
    exact this
  have path : ∀ a b, Relation.ReflTransGen (fun a b => 0 < q a b) a b → h b ≤ h a := by
    intro a b hab
    induction hab with
    | refl => exact le_rfl
    | tail _ hbc ih => exact (key _ _ hbc).trans ih
  intro i j
  exact le_antisymm (path _ _ (hirr j i)) (path _ _ (hirr i j))

end KM213

namespace KM213

open KellyStochasticNetworks KellyStochasticNetworks.MigrationDynamics MeasureTheory Filter Topology

theorem main {Ω : Type*} [MeasurableSpace Ω] {J : ℕ}
    (P : Measure Ω) (X : ℝ → Ω → (Fin J → ℕ))
    (hX : IsStationaryOpenMigration P X) :
    IsStationaryOpenMigration P (fun t => X (-t)) := by
  obtain ⟨hJ, M, π, hM, hπ⟩ := hX
  obtain ⟨hrevM, hrevπ⟩ := time_rev P X M.rate π hM hπ
  obtain ⟨hP, hmeas, hae, hq0, hqd, hqs, hirr, K, hK, hK0, hmk, hlim⟩ := hM
  obtain ⟨-, -, hpos, hπsum, hπt⟩ := hπ
  have hKnn : ∀ h, 0 ≤ h → ∀ i j, 0 ≤ K h i j := fun h hh i j => (hK h hh i).1 j
  have hfb : ∀ i, HasSum (fun k => π k * M.rate k i) (π i * ∑' k, M.rate i k) := fun i =>
    S202KR.full_balance hmeas hmk hπt (fun i => (hpos i).le) hKnn hlim hae hq0 hqd i
  have hrate : M.rate = openMigrationRates M.lam M.mu M.nu M.phi := rfl
  have hirr' : ∀ i j, Relation.ReflTransGen
      (fun a b => 0 < openMigrationRates M.lam M.mu M.nu M.phi a b) i j := hirr
  have hq0' : ∀ n m, 0 ≤ openMigrationRates M.lam M.mu M.nu M.phi n m := hq0
  obtain ⟨α, hα, htr⟩ := traffic_exists M.lam M.mu M.nu M.phi M.lam_nonneg M.mu_nonneg
    M.nu_nonneg M.phi_zero M.lam_diag hirr'
  set ρ := rho α M.phi with hρdef
  have hρpos : ∀ n, 0 < ρ n := rho_pos hα M.phi_pos
  set qs := openMigrationRates (revLam α M.lam) (fun j => M.nu j / α j)
    (fun k => α k * M.mu k) M.phi with hqs_def
  have hdet : ∀ m n, ρ m * M.rate m n = ρ n * qs n m := fun m n =>
    rho_detailed M.lam M.mu M.nu M.lam_diag M.phi_zero M.phi_pos hα m n
  have hQ : ∀ i, HasSum (M.rate i) (∑' k, M.rate i k) := fun i => (hqs i).1.hasSum
  have hfbρ : ∀ i, HasSum (fun j => ρ j * M.rate j i) (ρ i * ∑' k, M.rate i k) := by
    intro i
    have h1 := (rate_hasSum (revLam α M.lam) (fun j => M.nu j / α j)
      (fun k => α k * M.mu k) M.phi i).mul_left (ρ i)
    have hval : ∑' k, M.rate i k = _ := (rate_hasSum M.lam M.mu M.nu M.phi i).tsum_eq
    rw [hval, ← Qstar_eq M.lam M.mu M.nu M.phi α hα htr i]
    have e : (fun j => ρ j * M.rate j i) = fun j => ρ i * qs i j := funext fun j => hdet j i
    rw [e]; exact h1
  -- boxes
  set S : ℕ → ℝ := fun N => ∑ j ∈ box J N, π j with hSdef
  have hS : Tendsto S atTop (𝓝 1) :=
    hπsum.comp (tendsto_atTop_finset_of_monotone (box_mono J) fun x => ⟨∑ i, x i, by rw [mem_box]⟩)
  set ε : ℕ → ℝ := fun N => (∑ k, M.nu k) * (S (N + 1) - S N) with hεdef
  have hε : Tendsto ε atTop (𝓝 0) := by
    have h1 := ((hS.comp (tendsto_add_atTop_nat 1)).sub hS).const_mul (∑ k, M.nu k)
    simp only [sub_self, mul_zero] at h1
    exact h1
  have hB : ∀ i, ∃ N0, ∀ N, N0 ≤ N → i ∈ box J (N + 1) := fun i =>
    ⟨∑ k, i k, fun N hN => by rw [mem_box]; omega⟩
  have hout : ∀ N, ∑ j ∈ box J (N + 1), π j *
      (∑' i, if i ∈ box J (N + 1) then 0 else M.rate j i) ≤ ε N := by
    intro N
    have h1 : ∑ j ∈ box J (N + 1), π j *
        (∑' i, if i ∈ box J (N + 1) then 0 else M.rate j i) ≤
        ∑ j ∈ box J (N + 1), π j * (if ∑ i, j i = N + 1 then ∑ k, M.nu k else 0) :=
      Finset.sum_le_sum fun j hj => mul_le_mul_of_nonneg_left
        (out_le M.lam M.mu M.nu M.phi M.phi_zero M.nu_nonneg hq0' (N + 1) j ((mem_box j).1 hj))
        (hpos j).le
    have h2 : ∑ j ∈ box J (N + 1), π j * (if ∑ i, j i = N + 1 then ∑ k, M.nu k else 0) =
        (∑ k, M.nu k) * ∑ j ∈ box J (N + 1), (if ∑ i, j i = N + 1 then π j else 0) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by split_ifs <;> ring
    have hfilt : (box J (N + 1)).filter (fun j => ¬ ∑ i, j i = N + 1) = box J N := by
      ext x; simp only [Finset.mem_filter, mem_box]; omega
    have h3 : S (N + 1) = ∑ j ∈ box J (N + 1), (if ∑ i, j i = N + 1 then π j else 0) + S N := by
      simp only [hSdef]
      rw [← Finset.sum_filter_add_sum_filter_not (box J (N + 1)) (fun j => ∑ i, j i = N + 1),
        Finset.sum_filter, hfilt]
    have h4 : ε N = (∑ k, M.nu k) * ∑ j ∈ box J (N + 1), (if ∑ i, j i = N + 1 then π j else 0) := by
      simp only [hεdef]; rw [h3]; ring
    rw [h4, ← h2]; exact h1
  have hrat := ratio_const M.rate (fun i => ∑' k, M.rate i k) π ρ hq0 hQ hpos hρpos hfb hfbρ
    (fun N => box J (N + 1)) hB ε hε hout hirr
  let M' : MigrationData J :=
    { lam := revLam α M.lam
      mu := fun j => M.nu j / α j
      nu := fun k => α k * M.mu k
      phi := M.phi
      lam_nonneg := fun j k => div_nonneg (mul_nonneg (hα k).le (M.lam_nonneg k j)) (hα j).le
      lam_diag := fun j => by simp [revLam, M.lam_diag]
      mu_nonneg := fun j => div_nonneg (M.nu_nonneg j) (hα j).le
      nu_nonneg := fun k => mul_nonneg (hα k).le (M.mu_nonneg k)
      phi_zero := M.phi_zero
      phi_pos := M.phi_pos }
  have heq : reversedRates π M.rate = M'.rate := by
    funext n m
    show π m * M.rate m n / π n = qs n m
    have h1 := hrat m n
    have hπm : π m = ρ m * π n / ρ n := by
      have := hpos m; have := hpos n; have := hρpos m; have := hρpos n
      field_simp at h1 ⊢; linarith
    rw [hπm]
    have := hpos n; have := hρpos n
    field_simp
    linear_combination hdet m n
  exact ⟨hJ, M', π, heq ▸ hrevM, hrevπ⟩

end KM213

open KellyStochasticNetworks.MigrationDynamics MeasureTheory in
theorem solution {Ω : Type*} [MeasurableSpace Ω] {J : ℕ}
    (P : Measure Ω) (X : ℝ → Ω → (Fin J → ℕ))
    (hX : IsStationaryOpenMigration P X) :
    IsStationaryOpenMigration P (fun t => X (-t)) :=
  KM213.main P X hX
