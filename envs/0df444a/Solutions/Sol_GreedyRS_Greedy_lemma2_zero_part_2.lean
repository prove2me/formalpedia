-- Prove2me | solution 2 for GreedyRS.Greedy.lemma2_zero_part
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T13:03:58.12775+00:00
-- url     : https://prove2.me/submissions/d914ee3e-1c5f-4e6b-94e0-715dd831929e

import Mathlib
import Definitions.Def_GreedyRS_Greedy_Setting

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal

namespace A3GZ
open GreedyRS.Greedy

instance : IsProbabilityMeasure stdNormalSeq := by unfold stdNormalSeq; infer_instance

lemma indep : iIndepFun (fun j (z : ℕ → ℝ) => z j) stdNormalSeq :=
  iIndepFun_infinitePi (X := fun _ x => x) (fun _ => measurable_id)

lemma law (j : ℕ) : stdNormalSeq.map (fun z => z j) = gaussianReal 0 1 :=
  Measure.infinitePi_map_eval _ j

/-- `D k m z = ∑_{j<m} z (k+j)`. -/
noncomputable def D (k m : ℕ) (z : ℕ → ℝ) : ℝ := ∑ j ∈ Finset.range m, z (k + j)

lemma D_eq (k m : ℕ) : D k m = ∑ j ∈ Finset.Ico k (k + m), (fun z : ℕ → ℝ => z j) := by
  funext z
  simp only [D, Finset.sum_apply]
  rw [Finset.sum_Ico_eq_sum_range]; simp

lemma meas_D (k m : ℕ) : Measurable (D k m) := by
  unfold D; fun_prop

lemma law_D (k m : ℕ) : stdNormalSeq.map (D k m) = gaussianReal 0 m := by
  induction m with
  | zero =>
    have : D k 0 = fun _ => 0 := by funext z; simp [D]
    rw [this, Nat.cast_zero, gaussianReal_zero_var, Measure.map_const]; simp
  | succ m ih =>
    have hsplit : D k (m + 1) = D k m + (fun z : ℕ → ℝ => z (k + m)) := by
      funext z; simp [D, Finset.sum_range_succ]
    have hind : IndepFun (D k m) (fun z : ℕ → ℝ => z (k + m)) stdNormalSeq := by
      rw [D_eq]
      exact indep.indepFun_finsetSum_of_notMem (fun _ => measurable_pi_apply _) (by simp)
    rw [hsplit, gaussianReal_add_gaussianReal_of_indepFun hind ih (law _)]
    congr 1
    · simp
    · push_cast; ring

/-- `p = P(N(0,1) < -1) > 0`. -/
noncomputable def p : ℝ≥0∞ := gaussianReal 0 1 (Set.Iio (-1))

lemma p_pos : 0 < p := by
  unfold p
  apply pos_iff_ne_zero.2
  intro h
  have := gaussianReal_absolutelyContinuous' (0 : ℝ) (v := 1) one_ne_zero h
  simp at this

lemma prob_D (k m : ℕ) (hm : 1 ≤ m) :
    stdNormalSeq {z | D k m z < -Real.sqrt m} = p := by
  have hs : 0 < Real.sqrt m := Real.sqrt_pos.2 (by exact_mod_cast hm)
  have h1 : stdNormalSeq {z | D k m z < -Real.sqrt m} =
      gaussianReal 0 m (Set.Iio (-Real.sqrt m)) := by
    rw [← law_D k m, Measure.map_apply (meas_D k m) measurableSet_Iio]; rfl
  have h2 : gaussianReal 0 (m : ℝ≥0) = (gaussianReal 0 1).map (Real.sqrt m * ·) := by
    rw [gaussianReal_map_const_mul]
    congr 1
    · simp
    · ext; simp [Real.sq_sqrt (Nat.cast_nonneg m)]
  rw [h1, h2, Measure.map_apply (by fun_prop) measurableSet_Iio]
  unfold p; congr 1
  ext y; simp only [Set.mem_preimage, Set.mem_Iio]
  constructor
  · intro h; nlinarith
  · intro h; nlinarith

lemma freq_ge {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]
    {E : ℕ → Set α} (hE : ∀ n, MeasurableSet (E n)) {c : ℝ≥0∞} (h : ∀ n, c ≤ μ (E n)) :
    c ≤ μ {x | ∃ᶠ n in atTop, x ∈ E n} := by
  have hset : {x | ∃ᶠ n in atTop, x ∈ E n} = ⋂ M : ℕ, ⋃ n ≥ M, E n := by
    ext x; simp [frequently_atTop]
  rw [hset, Antitone.measure_iInter]
  · exact le_iInf fun M => (h M).trans (measure_mono (Set.subset_biUnion_of_mem (le_refl M)))
  · intro a b hab; exact Set.biUnion_mono (fun n hn => le_trans hab hn) (fun _ _ => le_rfl)
  · exact fun M => (MeasurableSet.biUnion (Set.to_countable _) fun n _ => hE n).nullMeasurableSet
  · exact ⟨0, measure_ne_top _ _⟩

/-- coordinate σ-algebras -/
def s (j : ℕ) : MeasurableSpace (ℕ → ℝ) :=
  MeasurableSpace.comap (fun z : ℕ → ℝ => z j) inferInstance

lemma s_le (j : ℕ) : s j ≤ (inferInstance : MeasurableSpace (ℕ → ℝ)) :=
  (measurable_pi_apply j).comap_le

lemma iIndep_s : iIndep s stdNormalSeq := (iIndepFun_iff_iIndep _ _ _).1 indep

lemma meas_D_of_le (mm : MeasurableSpace (ℕ → ℝ)) (k m : ℕ) (h : ∀ j < m, s (k + j) ≤ mm) :
    Measurable[mm] (D k m) := by
  letI := mm
  unfold D
  refine Finset.measurable_sum _ fun j hj => ?_
  exact Measurable.of_comap_le (h j (Finset.mem_range.1 hj))

def B (k : ℕ) : Set (ℕ → ℝ) :=
  {z | ∃ᶠ m in atTop, D k (m + 1) z < -Real.sqrt ((m + 1 : ℕ) : ℝ)}

lemma meas_B_of_le (mm : MeasurableSpace (ℕ → ℝ)) (k : ℕ) (h : ∀ j, s (k + j) ≤ mm) :
    MeasurableSet[mm] (B k) := by
  letI := mm
  have hset : B k = ⋂ M : ℕ, ⋃ m ≥ M, {z | D k (m + 1) z < -Real.sqrt ((m + 1 : ℕ) : ℝ)} := by
    ext x; simp [B, frequently_atTop]
  rw [hset]
  refine MeasurableSet.iInter fun M => MeasurableSet.biUnion (Set.to_countable _) fun m _ => ?_
  exact measurableSet_lt (meas_D_of_le mm k (m + 1) (fun j _ => h j)) measurable_const

def T : Set (ℕ → ℝ) := {z | ∃ᶠ k in atTop, z ∈ B k}

lemma T_tail : MeasurableSet[limsup s atTop] T := by
  rw [limsup_eq_iInf_iSup_of_nat, MeasurableSpace.measurableSet_iInf]
  intro n
  letI mm : MeasurableSpace (ℕ → ℝ) := ⨆ i ≥ n, s i
  have hB : ∀ k ≥ n, MeasurableSet[mm] (B k) := fun k hk =>
    meas_B_of_le mm k fun j => le_iSup₂ (f := fun i (_ : i ≥ n) => s i) (k + j) (by omega)
  have hset : T = ⋂ K : ℕ, ⋃ k ≥ max K n, B k := by
    ext x; simp only [T, Set.mem_setOf_eq, frequently_atTop, Set.mem_iInter, Set.mem_iUnion]
    constructor
    · intro h K; obtain ⟨k, hk, hx⟩ := h (max K n); exact ⟨k, hk, hx⟩
    · intro h K; obtain ⟨k, hk, hx⟩ := h K; exact ⟨k, le_trans (le_max_left _ _) hk, hx⟩
  rw [hset]
  exact MeasurableSet.iInter fun K => MeasurableSet.biUnion (Set.to_countable _)
    fun k hk => hB k (le_trans (le_max_right _ _) hk)

lemma meas_B (k : ℕ) : MeasurableSet (B k) := meas_B_of_le _ k fun j => s_le _

lemma meas_T : MeasurableSet T := by
  have : T = ⋂ K : ℕ, ⋃ k ≥ K, B k := by ext x; simp [T, frequently_atTop]
  rw [this]
  exact MeasurableSet.iInter fun K => MeasurableSet.biUnion (Set.to_countable _) fun k _ => meas_B k

lemma prob_T : stdNormalSeq T = 1 := by
  rcases measure_zero_or_one_of_measurableSet_limsup_atTop s_le iIndep_s T_tail with h | h
  · exfalso
    have hB : ∀ k, p ≤ stdNormalSeq (B k) := fun k =>
      freq_ge (E := fun m => {z | D k (m + 1) z < -Real.sqrt ((m + 1 : ℕ) : ℝ)})
        (fun m => measurableSet_lt (meas_D k _) measurable_const)
        (fun m => (prob_D k (m + 1) (by omega)).ge)
    have := freq_ge meas_B hB
    rw [show {x | ∃ᶠ n in atTop, x ∈ B n} = T from rfl, h] at this
    exact (p_pos.trans_le this).ne' rfl
  · exact h

lemma sum_split (z : ℕ → ℝ) (k m : ℕ) :
    ∑ j ∈ Finset.range (k + m), z j = ∑ j ∈ Finset.range k, z j + D k m z := by
  rw [Finset.sum_range_add]; rfl

/-- On `T`, partial sums are negative for arbitrarily large `n`. -/
lemma T_neg {z : ℕ → ℝ} (hz : z ∈ T) (K : ℕ) :
    ∃ n ≥ K, 1 ≤ n ∧ ∑ j ∈ Finset.range n, z j < 0 := by
  obtain ⟨k, -, hk⟩ := (frequently_atTop.1 hz) 0
  set S := ∑ j ∈ Finset.range k, z j
  obtain ⟨m, hm, hD⟩ := (frequently_atTop.1 hk) (K + ⌈S ^ 2⌉₊)
  refine ⟨k + (m + 1), by omega, by omega, ?_⟩
  rw [sum_split]
  have h1 : S ^ 2 ≤ ((m + 1 : ℕ) : ℝ) := by
    have := Nat.le_ceil (S ^ 2)
    have : (⌈S ^ 2⌉₊ : ℝ) ≤ m := by exact_mod_cast le_trans (Nat.le_add_left _ _) hm
    push_cast; linarith
  have h2 : S ≤ Real.sqrt ((m + 1 : ℕ) : ℝ) := by
    calc S ≤ |S| := le_abs_self S
    _ = Real.sqrt (S ^ 2) := (Real.sqrt_sq_eq_abs S).symm
    _ ≤ _ := Real.sqrt_le_sqrt h1
  linarith

lemma crossTime_lt_top_of_T {z : ℕ → ℝ} (hz : z ∈ T) : crossTime 0 1 z < ⊤ := by
  obtain ⟨n, -, hn1, hneg⟩ := T_neg hz 0
  have hz' : zbar z n < 0 := by
    unfold zbar
    exact div_neg_of_neg_of_pos hneg (by exact_mod_cast hn1)
  unfold crossTime
  exact lt_of_le_of_lt (iInf₂_le n ⟨hn1, hz'⟩) (ENat.coe_lt_top n)

lemma part1 : stdNormalSeq {z | crossTime 0 1 z < ⊤} = 1 :=
  le_antisymm prob_le_one (prob_T ▸ measure_mono fun _ hz => crossTime_lt_top_of_T hz)

/-- `A j = {N > j}`. -/
def A (j : ℕ) : Set (ℕ → ℝ) := {z | ∀ n, 1 ≤ n → n ≤ j → 0 ≤ D 0 n z}

lemma D0 (n : ℕ) (z : ℕ → ℝ) : D 0 n z = ∑ i ∈ Finset.range n, z i := by simp [D]

lemma zbar_neg_iff {z : ℕ → ℝ} {n : ℕ} (hn : 1 ≤ n) : zbar z n < 0 ↔ D 0 n z < 0 := by
  rw [D0]; unfold zbar
  have hpos : (0 : ℝ) < n := by exact_mod_cast hn
  constructor
  · intro h; by_contra h'; push_neg at h'
    have := div_nonneg h' hpos.le; linarith
  · intro h; exact div_neg_of_neg_of_pos h hpos

lemma lt_crossTime_iff (z : ℕ → ℝ) (j : ℕ) : (j : ℕ∞) < crossTime 0 1 z ↔ z ∈ A j := by
  unfold crossTime
  rw [← ENat.add_one_le_iff (ENat.coe_ne_top j)]
  simp only [le_iInf_iff]
  constructor
  · intro h n hn1 hnj
    by_contra hneg; push_neg at hneg
    have h2 := h n ⟨hn1, (zbar_neg_iff hn1).2 hneg⟩
    have : j + 1 ≤ n := by exact_mod_cast h2
    omega
  · rintro hA n ⟨hn1, hneg⟩
    have : ¬ n ≤ j := fun hnj => absurd (hA n hn1 hnj) (not_le.2 ((zbar_neg_iff hn1).1 hneg))
    exact_mod_cast (by omega : j + 1 ≤ n)

lemma meas_A_of_le (mm : MeasurableSpace (ℕ → ℝ)) (j : ℕ) (h : ∀ i < j, s i ≤ mm) :
    MeasurableSet[mm] (A j) := by
  letI := mm
  have hset : A j = ⋂ n : ℕ, ⋂ (_ : 1 ≤ n), ⋂ (_ : n ≤ j), {z | 0 ≤ D 0 n z} := by
    ext z; simp [A]
  rw [hset]
  refine MeasurableSet.iInter fun n => MeasurableSet.iInter fun _ => MeasurableSet.iInter fun hn => ?_
  exact measurableSet_le measurable_const (meas_D_of_le mm 0 n fun i hi => h _ (by omega))

lemma meas_A (j : ℕ) : MeasurableSet (A j) := meas_A_of_le _ j fun i _ => s_le i

lemma indep_A (j : ℕ) {β γ : Type*} [MeasurableSpace β] [MeasurableSpace γ]
    (f : (ℕ → ℝ) → β) (g : ℝ → γ)
    (hf : Measurable[⨆ i ∈ {i | i < j}, s i] f) (hg : Measurable g) :
    IndepFun f (fun z => g (z j)) stdNormalSeq := by
  rw [IndepFun_iff_Indep]
  have h := indep_iSup_of_disjoint s_le iIndep_s (S := {i | i < j}) (T := {j})
    (Set.disjoint_singleton_right.2 (by simp))
  refine indep_of_indep_of_le_right (indep_of_indep_of_le_left h hf.comap_le) ?_
  have : Measurable[⨆ i ∈ ({j} : Set ℕ), s i] (fun z : ℕ → ℝ => g (z j)) := by
    refine hg.comp ?_
    exact Measurable.of_comap_le (le_iSup₂ (f := fun i (_ : i ∈ ({j} : Set ℕ)) => s i) j rfl)
  exact this.comap_le

lemma measA_le (j : ℕ) : MeasurableSet[⨆ i ∈ {i | i < j}, s i] (A j) :=
  meas_A_of_le _ j fun i hi => le_iSup₂ (f := fun i (_ : i ∈ {i | i < j}) => s i) i hi

lemma enat_eq_tsum (N : ℕ∞) :
    (N : ℝ≥0∞) = ∑' j : ℕ, if (j : ℕ∞) < N then 1 else 0 := by
  induction N using ENat.recTopCoe with
  | top =>
    simp only [ENat.toENNReal_top, ENat.coe_lt_top, if_true]
    exact (ENNReal.tsum_const_eq_top_of_ne_zero one_ne_zero).symm
  | coe n =>
    rw [ENat.toENNReal_coe, tsum_eq_sum (s := Finset.range n)]
    · simp only [Nat.cast_lt, Finset.sum_boole, Nat.cast_id]
      rw [Finset.filter_true_of_mem (fun x hx => Finset.mem_range.1 hx)]; simp
    · intro j hj
      have : ¬ j < n := by simpa using hj
      rw [if_neg (by exact_mod_cast this)]

lemma Cn0_eq : Cn0 0 1 = ∑' j, stdNormalSeq (A j) := by
  have hpt : ∀ z, ((crossTime 0 1 z : ℕ∞) : ℝ≥0∞) = ∑' j : ℕ, (A j).indicator 1 z := by
    intro z; rw [enat_eq_tsum]; congr 1; funext j
    simp only [Set.indicator, Pi.one_apply, ← lt_crossTime_iff]
  unfold Cn0
  rw [lintegral_congr (fun z => hpt z), lintegral_tsum]
  · congr 1; funext j
    rw [lintegral_indicator_one (meas_A j)]
  · intro j
    exact (measurable_const.indicator (meas_A j)).aemeasurable

/-- the Wald summands -/
noncomputable def f (j : ℕ) (z : ℕ → ℝ) : ℝ := (A j).indicator (fun _ => (1 : ℝ)) z * z j

lemma meas_f (j : ℕ) : Measurable (f j) :=
  (measurable_const.indicator (meas_A j)).mul (measurable_pi_apply j)

lemma integral_coord (j : ℕ) : ∫ z, z j ∂stdNormalSeq = 0 := by
  have := integral_map (μ := stdNormalSeq) (φ := fun z : ℕ → ℝ => z j) (f := fun x : ℝ => x)
    (measurable_pi_apply j).aemeasurable aestronglyMeasurable_id
  rw [← this, law j]
  exact integral_id_gaussianReal

lemma integral_f (j : ℕ) : ∫ z, f j z ∂stdNormalSeq = 0 := by
  have hind : IndepFun ((A j).indicator (fun _ => (1 : ℝ))) (fun z : ℕ → ℝ => z j) stdNormalSeq :=
    indep_A j ((A j).indicator (fun _ => (1 : ℝ))) id
    (@Measurable.indicator _ _ _ _ _ _ _ (measurable_const) (measA_le j)) measurable_id
  unfold f
  rw [hind.integral_fun_mul_eq_mul_integral (measurable_const.indicator (meas_A j)).aestronglyMeasurable
    (measurable_pi_apply j).aestronglyMeasurable]
  rw [integral_coord, mul_zero]

noncomputable def c : ℝ≥0∞ := ∫⁻ x, ‖x‖ₑ ∂gaussianReal 0 1

lemma c_lt_top : c < ⊤ := by
  unfold c
  have : Integrable (fun x : ℝ => x) (gaussianReal 0 1) := by
    exact (memLp_id_gaussianReal 1).integrable le_rfl
  exact this.2

lemma lintegral_f (j : ℕ) : ∫⁻ z, ‖f j z‖ₑ ∂stdNormalSeq = stdNormalSeq (A j) * c := by
  have hind := indep_A j ((A j).indicator (fun _ => (1 : ℝ≥0∞))) (fun x : ℝ => ‖x‖ₑ)
    (@Measurable.indicator _ _ _ _ _ _ _ (measurable_const) (measA_le j)) measurable_enorm
  have heq : (fun z => ‖f j z‖ₑ) =
      (A j).indicator (fun _ => (1 : ℝ≥0∞)) * fun z => ‖z j‖ₑ := by
    funext z; simp only [f, Pi.mul_apply, Set.indicator]; split_ifs <;> simp
  rw [heq, lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun
    (measurable_const.indicator (meas_A j)) ((measurable_pi_apply j).enorm) hind]
  rw [lintegral_indicator_const (meas_A j), one_mul]
  congr 1
  unfold c
  rw [← law j, lintegral_map measurable_enorm (measurable_pi_apply j)]

lemma g_neg {z : ℕ → ℝ} (hz : z ∈ T) : ∑' j, f j z < 0 := by
  have hlt := crossTime_lt_top_of_T hz
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.1 hlt.ne
  have hA : ∀ j, z ∈ A j ↔ j < n := by
    intro j; rw [← lt_crossTime_iff, ← hn]; exact_mod_cast Iff.rfl
  have hfz : ∀ j, f j z = if j < n then z j else 0 := by
    intro j; simp only [f, Set.indicator, hA]; split_ifs <;> simp
  rw [tsum_eq_sum (s := Finset.range n)]
  swap
  · intro j hj; rw [hfz, if_neg (by simpa using hj)]
  rw [Finset.sum_congr rfl (fun j hj => by rw [hfz, if_pos (Finset.mem_range.1 hj)])]
  have hn1 : 1 ≤ n := by
    by_contra h0
    have : z ∈ A 0 := fun m hm1 hm0 => absurd (le_trans hm1 hm0) (by omega)
    have := (hA 0).1 this; omega
  have hnotA : z ∉ A n := fun h => absurd ((hA n).1 h) (lt_irrefl n)
  have hAprev : z ∈ A (n - 1) := (hA (n - 1)).2 (by omega)
  simp only [A, Set.mem_setOf_eq, not_forall, not_le] at hnotA
  obtain ⟨m, hm1, hmn, hneg⟩ := hnotA
  have hmeq : m = n := by
    by_contra hne
    have := hAprev m hm1 (by omega); linarith
  subst hmeq
  rw [← D0]; exact hneg

theorem zero_part : stdNormalSeq {z | crossTime 0 1 z < ⊤} = 1 ∧ Cn0 0 1 = ⊤ := by
  refine ⟨part1, ?_⟩
  by_contra hfin
  rw [Cn0_eq] at hfin
  have hsum : ∑' j, ∫⁻ z, ‖f j z‖ₑ ∂stdNormalSeq ≠ ⊤ := by
    simp_rw [lintegral_f]; rw [ENNReal.tsum_mul_right]; exact ENNReal.mul_ne_top hfin c_lt_top.ne
  have hint := integral_tsum (fun j => (meas_f j).aestronglyMeasurable) hsum
  simp_rw [integral_f, tsum_zero] at hint
  have hgi : Integrable (fun z => ∑' j, f j z) stdNormalSeq := by
    refine ⟨AEStronglyMeasurable.tsum (fun j => (meas_f j).aestronglyMeasurable), ?_⟩
    unfold HasFiniteIntegral
    calc ∫⁻ z, ‖∑' j, f j z‖ₑ ∂stdNormalSeq ≤ ∫⁻ z, ∑' j, ‖f j z‖ₑ ∂stdNormalSeq :=
          lintegral_mono fun z => enorm_tsum_le_tsum_enorm
    _ = ∑' j, ∫⁻ z, ‖f j z‖ₑ ∂stdNormalSeq :=
          lintegral_tsum (fun j => (meas_f j).enorm.aemeasurable)
    _ < ⊤ := lt_top_iff_ne_top.2 hsum
  have hpos : 0 < ∫ z, -(∑' j, f j z) ∂stdNormalSeq := by
    rw [integral_pos_iff_support_of_nonneg_ae (f := fun z => -(∑' j, f j z)) _ hgi.neg]
    · have : T ⊆ Function.support (fun z => -(∑' j, f j z)) := fun z hz => by
        simp only [Function.mem_support]; have := g_neg hz; linarith
      exact lt_of_lt_of_le (by rw [prob_T]; exact one_pos) (measure_mono this)
    · have hT : ∀ᵐ z ∂stdNormalSeq, z ∈ T := by
        rw [ae_iff]
        have := prob_compl_eq_zero_iff (meas_T) |>.2 prob_T
        exact this
      filter_upwards [hT] with z hz
      have := g_neg hz; simp only [Pi.zero_apply]; linarith
  rw [integral_neg, hint] at hpos
  simp at hpos

end A3GZ

open GreedyRS.Greedy in
theorem solution :
    stdNormalSeq {z | crossTime 0 1 z < ⊤} = 1 ∧ Cn0 0 1 = ⊤ :=
  A3GZ.zero_part

