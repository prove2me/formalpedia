-- Prove2me | solution 2 for GreedyRS.EFG.lemma4_crossing_time
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T13:10:34.298949+00:00
-- url     : https://prove2.me/submissions/8f8ddc35-c192-4901-a168-59f142e6a461

import Mathlib
import Definitions.Def_GreedyRS_EFG_Setting
import Theorems.Thm_GreedyRS_Budget_ec2_4_tail_sum_bound
import Theorems.Thm_GreedyRS_Budget_ec2_4_normal_tail_bound

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

namespace A3GZ
open GreedyRS.Greedy

lemma ct_le_n0 (x : ℝ) {n0 : ℕ} (hn0 : 1 ≤ n0) (z : ℕ → ℝ) : crossTime x 1 z ≤ crossTime x n0 z :=
  le_iInf₂ fun n h => iInf₂_le n ⟨le_trans hn0 h.1, h.2⟩

lemma ct_lt_top_of_T {x : ℝ} (hx : 0 ≤ x) (n0 : ℕ) {z : ℕ → ℝ} (hz : z ∈ T) :
    crossTime x n0 z < ⊤ := by
  obtain ⟨n, hnK, hn1, hneg⟩ := T_neg hz n0
  have hz' : zbar z n < x := by
    unfold zbar
    exact (div_neg_of_neg_of_pos hneg (by exact_mod_cast hn1)).trans_le hx
  unfold crossTime
  exact lt_of_le_of_lt (iInf₂_le n ⟨hnK, hz'⟩) (ENat.coe_lt_top n)

lemma prob_cross_one {x : ℝ} (hx : 0 ≤ x) (n0 : ℕ) :
    stdNormalSeq {z | crossTime x n0 z < ⊤} = 1 :=
  le_antisymm prob_le_one (prob_T ▸ measure_mono fun _ hz => ct_lt_top_of_T hx n0 hz)

lemma Cn0_zero_n0 {n0 : ℕ} (hn0 : 1 ≤ n0) : Cn0 0 n0 = ⊤ := by
  apply eq_top_iff.2
  rw [← zero_part.2]
  unfold Cn0
  exact lintegral_mono fun z => ENat.toENNReal_le.2 (ct_le_n0 0 hn0 z)

lemma Cn0_pos_lt_top {x : ℝ} (hx : 0 < x) {n0 : ℕ} (hn0 : 1 ≤ n0) : Cn0 x n0 < ⊤ := by
  refine lt_of_le_of_lt (GreedyRS.Budget.ec2_4_tail_sum_bound x hx n0 hn0) ?_
  refine ENNReal.add_lt_top.2 ⟨ENNReal.natCast_lt_top _, ?_⟩
  set r : ℝ := Real.exp (-x ^ 2 / 2)
  have hr0 : 0 ≤ r := (Real.exp_pos _).le
  have hr1 : r < 1 := Real.exp_lt_one_iff.2 (by have := sq_pos_of_pos hx; linarith)
  have hle : ∀ n : ℕ, ENNReal.ofReal (1 - Phi (Real.sqrt ((n0 + n : ℕ) : ℝ) * x)) ≤
      ENNReal.ofReal r ^ n := by
    intro n
    rw [← ENNReal.ofReal_pow hr0]
    apply ENNReal.ofReal_le_ofReal
    have hpos : 0 < Real.sqrt ((n0 + n : ℕ) : ℝ) * x :=
      mul_pos (Real.sqrt_pos.2 (by exact_mod_cast (by omega : 0 < n0 + n))) hx
    refine (GreedyRS.Budget.ec2_4_normal_tail_bound _ hpos).trans ?_
    rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg _), ← Real.exp_nat_mul]
    apply Real.exp_le_exp.2
    push_cast
    have : (1 : ℝ) ≤ n0 := by exact_mod_cast hn0
    nlinarith [sq_nonneg x]
  refine lt_of_le_of_lt (ENNReal.tsum_le_tsum hle) ?_
  rw [ENNReal.tsum_geometric]
  apply ENNReal.inv_lt_top.2
  apply tsub_pos_of_lt
  exact (ENNReal.ofReal_lt_one).2 hr1

/-- gaussian positivity -/
lemma gauss_pos {s : Set ℝ} (hs : 0 < volume s) (m : ℝ≥0) (hm : m ≠ 0) : 0 < gaussianReal 0 m s :=
  pos_iff_ne_zero.2 fun h => hs.ne' (gaussianReal_absolutelyContinuous' 0 hm h)

lemma prob_cross_pos {x : ℝ} {n0 : ℕ} (hn0 : 1 ≤ n0) :
    0 < stdNormalSeq {z | crossTime x n0 z < ⊤} := by
  have hsub : {z | D 0 n0 z < n0 * x} ⊆ {z | crossTime x n0 z < ⊤} := by
    intro z hz
    have hz' : zbar z n0 < x := by
      simp only [Set.mem_setOf_eq, D0] at hz
      unfold zbar
      have : (0 : ℝ) < n0 := by exact_mod_cast hn0
      rw [div_lt_iff₀ this]; linarith
    show crossTime x n0 z < ⊤
    unfold crossTime
    exact lt_of_le_of_lt (iInf₂_le n0 ⟨le_rfl, hz'⟩) (ENat.coe_lt_top n0)
  refine lt_of_lt_of_le ?_ (measure_mono hsub)
  have : stdNormalSeq {z | D 0 n0 z < n0 * x} = gaussianReal 0 n0 (Set.Iio (n0 * x)) := by
    rw [← law_D 0 n0, Measure.map_apply (meas_D 0 n0) measurableSet_Iio]; rfl
  rw [this]
  exact gauss_pos (by simp) _ (by exact_mod_cast (by omega : n0 ≠ 0))

/-- the "never crosses" event, for `x < 0` -/
def G (x : ℝ) (K : ℕ) : Set (ℕ → ℝ) := {z | ∀ m : ℕ, x * (m + K) ≤ D 1 m z}

def F (x : ℝ) (K : ℕ) : Set (ℕ → ℝ) := {z | -x * K ≤ z 0}

lemma meas_G_of_le (mm : MeasurableSpace (ℕ → ℝ)) (x : ℝ) (K : ℕ) (h : ∀ j, s (1 + j) ≤ mm) :
    MeasurableSet[mm] (G x K) := by
  letI := mm
  have hset : G x K = ⋂ m : ℕ, {z | x * (m + K) ≤ D 1 m z} := by ext z; simp [G]
  rw [hset]
  exact MeasurableSet.iInter fun m => measurableSet_le measurable_const
    (meas_D_of_le mm 1 m fun j _ => h j)

lemma slln : ∀ᵐ z ∂stdNormalSeq,
    Tendsto (fun n : ℕ => (n : ℝ)⁻¹ • (∑ i ∈ Finset.range n, z (1 + i))) atTop (nhds 0) := by
  have hint : Integrable (fun z : ℕ → ℝ => z (1 + 0)) stdNormalSeq := by
    have h1 : Integrable (fun x : ℝ => x) (stdNormalSeq.map (fun z => z (1 + 0))) := by
      rw [law]; exact (memLp_id_gaussianReal 1).integrable le_rfl
    exact (integrable_map_measure aestronglyMeasurable_id
      (measurable_pi_apply _).aemeasurable).1 h1
  have h := strong_law_ae (μ := stdNormalSeq) (fun i (z : ℕ → ℝ) => z (1 + i)) hint
    (fun i j hij => indep.indepFun (by omega))
    (fun i => ⟨(measurable_pi_apply _).aemeasurable, (measurable_pi_apply _).aemeasurable,
      by rw [law, law]⟩)
  have h0 : ∫ z, z (1 + 0) ∂stdNormalSeq = 0 := integral_coord _
  rw [h0] at h
  exact h

lemma exists_K {x : ℝ} (hx : x < 0) {z : ℕ → ℝ}
    (hz : Tendsto (fun n : ℕ => (n : ℝ)⁻¹ • (∑ i ∈ Finset.range n, z (1 + i))) atTop (nhds 0)) :
    ∃ K : ℕ, z ∈ G x K := by
  obtain ⟨M, hM⟩ := eventually_atTop.1 ((tendsto_order.1 hz).1 x hx)
  set C : ℝ := ∑ m ∈ Finset.range (M + 1), |D 1 m z|
  refine ⟨⌈C / (-x)⌉₊, fun m => ?_⟩
  have hK : C ≤ -x * ⌈C / (-x)⌉₊ := by
    have := Nat.le_ceil (C / (-x))
    rw [div_le_iff₀ (by linarith)] at this; linarith
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  by_cases hmM : m ≤ M
  · have h1 : |D 1 m z| ≤ C :=
      Finset.single_le_sum (f := fun m => |D 1 m z|) (fun _ _ => abs_nonneg _)
        (Finset.mem_range.2 (by omega))
    have h2 := neg_abs_le (D 1 m z)
    nlinarith
  · have h := hM m (by omega)
    simp only [smul_eq_mul] at h
    have hmpos : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
    rw [lt_inv_mul_iff₀ hmpos] at h
    have : D 1 m z = ∑ i ∈ Finset.range m, z (1 + i) := rfl
    have hC0 : 0 ≤ C := Finset.sum_nonneg fun _ _ => abs_nonneg _
    nlinarith

lemma exists_G_pos {x : ℝ} (hx : x < 0) : ∃ K, 0 < stdNormalSeq (G x K) := by
  by_contra hcon
  push_neg at hcon
  have hnull : stdNormalSeq (⋃ K, G x K) = 0 :=
    measure_iUnion_null fun K => le_antisymm (hcon K) zero_le
  have hae : ∀ᵐ z ∂stdNormalSeq, z ∈ ⋃ K, G x K := by
    filter_upwards [slln] with z hz
    exact Set.mem_iUnion.2 (exists_K hx hz)
  rw [ae_iff] at hae
  have : stdNormalSeq (⋃ K, G x K)ᶜ = 0 := hae
  have h1 := measure_union_le (μ := stdNormalSeq) (⋃ K, G x K) (⋃ K, G x K)ᶜ
  rw [Set.union_compl_self, measure_univ, hnull, this] at h1
  simp at h1

lemma FG_never {x : ℝ} (hx : x < 0) {K : ℕ} {z : ℕ → ℝ} (hF : z ∈ F x K) (hG : z ∈ G x K)
    (n0 : ℕ) : crossTime x n0 z = ⊤ := by
  unfold crossTime
  refine iInf₂_eq_top.2 fun n ⟨hn, hlt⟩ => ?_
  exfalso
  by_cases hn0 : n = 0
  · subst hn0; simp [zbar] at hlt; linarith
  have hsplit := sum_split z 1 (n - 1)
  rw [show 1 + (n - 1) = n by omega] at hsplit
  have hG' := hG (n - 1)
  simp only [F, Set.mem_setOf_eq] at hF
  have hpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  unfold zbar at hlt
  rw [div_lt_iff₀ hpos, hsplit] at hlt
  simp only [Finset.range_one, Finset.sum_singleton] at hlt
  have : ((n - 1 : ℕ) : ℝ) = n - 1 := by rw [Nat.cast_sub (by omega)]; simp
  rw [this] at hG'
  nlinarith

lemma neg_case {x : ℝ} (hx : x < 0) {n0 : ℕ} (hn0 : 1 ≤ n0) :
    stdNormalSeq {z | crossTime x n0 z < ⊤} < 1 ∧ Cn0 x n0 = ⊤ := by
  obtain ⟨K, hGpos⟩ := exists_G_pos hx
  have hFm : MeasurableSet[⨆ i ∈ ({0} : Set ℕ), s i] (F x K) :=
    measurableSet_Ici.preimage (Measurable.of_comap_le
      (le_iSup₂ (f := fun i (_ : i ∈ ({0} : Set ℕ)) => s i) 0 rfl))
  have hGm : MeasurableSet[⨆ i ∈ {i | 1 ≤ i}, s i] (G x K) :=
    meas_G_of_le _ x K fun j => le_iSup₂ (f := fun i (_ : i ∈ {i | 1 ≤ i}) => s i) (1 + j)
      (by simp)
  have hind := indep_iSup_of_disjoint s_le iIndep_s (S := {0}) (T := {i | 1 ≤ i})
    (Set.disjoint_singleton_left.2 (by simp))
  have hmul := (Indep_iff _ _ _).1 hind _ _ hFm hGm
  have hFpos : 0 < stdNormalSeq (F x K) := by
    have : stdNormalSeq (F x K) = gaussianReal 0 1 (Set.Ici (-x * K)) := by
      rw [← law 0, Measure.map_apply (measurable_pi_apply 0) measurableSet_Ici]; rfl
    rw [this]; exact gauss_pos (by simp) 1 one_ne_zero
  have hFG : 0 < stdNormalSeq (F x K ∩ G x K) := by
    rw [hmul]; exact ENNReal.mul_pos hFpos.ne' hGpos.ne'
  have hFGm : MeasurableSet (F x K ∩ G x K) :=
    (measurableSet_Ici.preimage (measurable_pi_apply 0)).inter
      (meas_G_of_le _ x K fun j => s_le _)
  constructor
  · have hsub : {z | crossTime x n0 z < ⊤} ⊆ (F x K ∩ G x K)ᶜ := by
      intro z hz hzFG
      have := FG_never hx hzFG.1 hzFG.2 n0
      simp only [Set.mem_setOf_eq, this, lt_self_iff_false] at hz
    refine lt_of_le_of_lt (measure_mono hsub) ?_
    rw [prob_compl_eq_one_sub hFGm]
    exact ENNReal.sub_lt_self ENNReal.one_ne_top one_ne_zero hFG.ne'
  · apply eq_top_iff.2
    unfold Cn0
    calc (⊤ : ℝ≥0∞) = ∫⁻ z, (F x K ∩ G x K).indicator (fun _ => ⊤) z ∂stdNormalSeq := by
          rw [lintegral_indicator_const hFGm, ENNReal.top_mul hFG.ne']
    _ ≤ _ := lintegral_mono fun z => by
          by_cases hz : z ∈ F x K ∩ G x K
          · rw [Set.indicator_of_mem hz, FG_never hx hz.1 hz.2 n0]; simp
          · rw [Set.indicator_of_notMem hz]; exact zero_le

end A3GZ

open GreedyRS.Greedy GreedyRS.EFG in
theorem solution (n0 : ℕ) (hn0 : 1 ≤ n0) :
    (∀ x : ℝ, 0 < x →
      GreedyRS.Greedy.stdNormalSeq {z | GreedyRS.Greedy.crossTime x n0 z < ⊤} = 1 ∧ GreedyRS.Greedy.Cn0 x n0 < ⊤) ∧
    (∀ x : ℝ, x < 0 →
      0 < GreedyRS.Greedy.stdNormalSeq {z | GreedyRS.Greedy.crossTime x n0 z < ⊤} ∧
      GreedyRS.Greedy.stdNormalSeq {z | GreedyRS.Greedy.crossTime x n0 z < ⊤} < 1 ∧ GreedyRS.Greedy.Cn0 x n0 = ⊤) ∧
    (GreedyRS.Greedy.stdNormalSeq {z | GreedyRS.Greedy.crossTime 0 n0 z < ⊤} = 1 ∧ GreedyRS.Greedy.Cn0 0 n0 = ⊤) :=
  ⟨fun x hx => ⟨A3GZ.prob_cross_one hx.le n0, A3GZ.Cn0_pos_lt_top hx hn0⟩,
   fun x hx => ⟨A3GZ.prob_cross_pos hn0, A3GZ.neg_case hx hn0⟩,
   ⟨A3GZ.prob_cross_one le_rfl n0, A3GZ.Cn0_zero_n0 hn0⟩⟩
