-- Prove2me | solution 1 for KallMayerSLP.Bonferroni.eq_3_15_boole_bonferroni
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-24T20:34:30.375735+00:00
-- url     : https://prove2.me/submissions/f2e37cdd-da1d-4291-b4bd-19f0e0d1188f

import Mathlib
import Definitions.Def_KallMayerSLP_Bonferroni_binomialMoment
import Definitions.Def_KallMayerSLP_Bonferroni_exceedanceEvent
import Definitions.Def_KallMayerSLP_Bonferroni_jointCDF
import Definitions.Def_KallMayerSLP_Bonferroni_lpMin
import Definitions.Def_KallMayerSLP_Bonferroni_lpMax
import Definitions.Def_KallMayerSLP_Bonferroni_vMinClosedForm
import Definitions.Def_KallMayerSLP_Bonferroni_vMaxClosedForm
import Definitions.Def_KallMayerSLP_Bonferroni_occurrenceCount

set_option autoImplicit false

open MeasureTheory KallMayerSLP.Bonferroni

namespace KallP

/-! ### PartL1 -/
/-- `ν` as a real function is a finite sum of indicators, hence measurable. -/
lemma L1_measurable_nu {Ω : Type*} [MeasurableSpace Ω] {r : ℕ} (B : Fin r → Set Ω)
    (hB : ∀ i, MeasurableSet (B i)) : Measurable (fun ω => (occurrenceCount B ω : ℝ)) := by
  have : (fun ω => (occurrenceCount B ω : ℝ)) =
      fun ω => ∑ i, (B i).indicator (fun _ => (1 : ℝ)) ω := by
    funext ω
    classical
    rw [occurrenceCount, Finset.card_filter, Nat.cast_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases h : ω ∈ B i <;> simp [h]
  rw [this]
  exact Finset.measurable_sum _ fun i _ => measurable_const.indicator (hB i)

lemma L1_meas_level {Ω : Type*} [MeasurableSpace Ω] {r : ℕ} (B : Fin r → Set Ω)
    (hB : ∀ i, MeasurableSet (B i)) (m : ℕ) : MeasurableSet {ω | occurrenceCount B ω = m} := by
  have : {ω | occurrenceCount B ω = m} =
      (fun ω => (occurrenceCount B ω : ℝ)) ⁻¹' {(m : ℝ)} := by
    ext ω; simp
  rw [this]
  exact L1_measurable_nu B hB (measurableSet_singleton _)

lemma L1_le {Ω : Type*} {r : ℕ} (B : Fin r → Set Ω) (ω : Ω) : occurrenceCount B ω ≤ r := by
  classical
  unfold occurrenceCount
  exact (Finset.card_filter_le _ _).trans (by simp)

lemma L1_point {Ω : Type*} {r : ℕ} (B : Fin r → Set Ω) (g : ℕ → ℝ) (hg : g 0 = 0) (ω : Ω) :
    g (occurrenceCount B ω) = ∑ i : Fin r,
      {ω | occurrenceCount B ω = (i : ℕ) + 1}.indicator (fun _ => g ((i : ℕ) + 1)) ω := by
  have hle := L1_le B ω
  rcases Nat.eq_zero_or_pos (occurrenceCount B ω) with h | h
  · rw [h, hg]; symm; apply Finset.sum_eq_zero; intro i _; simp [h]
  · obtain ⟨m, hm⟩ : ∃ m, occurrenceCount B ω = m + 1 := ⟨_, (Nat.succ_pred_eq_of_pos h).symm⟩
    have hmr : m < r := by omega
    rw [Finset.sum_eq_single ⟨m, hmr⟩]
    · simp [hm]
    · intro j _ hj
      simp only [Set.indicator_apply, Set.mem_ofPred_eq, hm]
      rw [if_neg]
      intro h'
      apply hj
      ext
      simp only
      omega
    · intro h; exact absurd (Finset.mem_univ _) h

lemma L1_integral {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ] {r : ℕ}
    (B : Fin r → Set Ω) (hB : ∀ i, MeasurableSet (B i)) (g : ℕ → ℝ) (hg : g 0 = 0) :
    ∫ ω, g (occurrenceCount B ω) ∂μ =
      ∑ i : Fin r, g ((i : ℕ) + 1) * μ.real {ω | occurrenceCount B ω = (i : ℕ) + 1} := by
  rw [show (fun ω => g (occurrenceCount B ω)) = fun ω => ∑ i : Fin r,
      {ω | occurrenceCount B ω = (i : ℕ) + 1}.indicator (fun _ => g ((i : ℕ) + 1)) ω
    from funext (L1_point B g hg)]
  rw [integral_finsetSum _ (fun i _ => (integrable_const _).indicator (L1_meas_level B hB _))]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_indicator_const _ (L1_meas_level B hB _), smul_eq_mul, mul_comm]

lemma L1_point_choose {Ω : Type*} {r : ℕ} (B : Fin r → Set Ω) (k : ℕ) (ω : Ω) :
    ∑ I ∈ Finset.powersetCard k (Finset.univ : Finset (Fin r)),
      (⋂ i ∈ I, B i).indicator (fun _ => (1 : ℝ)) ω = ((occurrenceCount B ω).choose k : ℝ) := by
  classical
  unfold occurrenceCount
  set S := Finset.univ.filter fun i => ω ∈ B i with hS
  have h1 : ∀ I : Finset (Fin r),
      (⋂ i ∈ I, B i).indicator (fun _ => (1 : ℝ)) ω = if I ⊆ S then 1 else 0 := by
    intro I
    simp [Set.indicator_apply, Finset.subset_iff, S]
  simp_rw [h1]
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one, ← Finset.card_powersetCard]
  congr 2
  ext I
  simp [Finset.mem_powersetCard, Finset.mem_filter, and_comm]

lemma L1_moment {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ] {r : ℕ}
    (B : Fin r → Set Ω) (hB : ∀ i, MeasurableSet (B i)) (k : ℕ) :
    binomialMoment μ B k = ∫ ω, ((occurrenceCount B ω).choose k : ℝ) ∂μ := by
  unfold binomialMoment
  have hm : ∀ I : Finset (Fin r), MeasurableSet (⋂ i ∈ I, B i) :=
    fun I => Finset.measurableSet_biInter I (fun i _ => hB i)
  rw [show (fun ω => ((occurrenceCount B ω).choose k : ℝ)) = fun ω =>
      ∑ I ∈ Finset.powersetCard k (Finset.univ : Finset (Fin r)),
        (⋂ i ∈ I, B i).indicator (fun _ => (1 : ℝ)) ω
    from funext fun ω => (L1_point_choose B k ω).symm]
  rw [integral_finsetSum _ (fun I _ => (integrable_const _).indicator (hm I))]
  refine Finset.sum_congr rfl fun I _ => ?_
  rw [integral_indicator_const _ (hm I), smul_eq_mul, mul_one]

/-- (L1) The distribution of the number of occurring events is a feasible point of (3.14) whose
objective value is the probability of the union. -/
theorem data_feasible {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {r : ℕ} (B : Fin r → Set Ω) (hB : ∀ i, MeasurableSet (B i)) :
    ∃ v : Fin r → ℝ, v ∈ lpFeasible r (binomialMoment μ B 1) (binomialMoment μ B 2) ∧
      ∑ i, v i = μ.real (⋃ i, B i) := by
  refine ⟨fun i => μ.real {ω | occurrenceCount B ω = (i : ℕ) + 1},
    ⟨?_, ?_, fun i => measureReal_nonneg⟩, ?_⟩
  · rw [L1_moment μ B hB 1, L1_integral μ B hB (fun m => (m.choose 1 : ℝ)) (by simp)]
    simp
  · rw [L1_moment μ B hB 2, L1_integral μ B hB (fun m => (m.choose 2 : ℝ)) (by simp)]
  · have h := L1_integral μ B hB (fun m => if m = 0 then (0 : ℝ) else 1) (by simp)
    simp only [Nat.add_one_ne_zero, if_false, one_mul] at h
    rw [← h]
    have hU : MeasurableSet (⋃ i, B i) := MeasurableSet.iUnion hB
    rw [← integral_indicator_one hU]
    refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
    classical
    simp only [Set.indicator_apply, Set.mem_iUnion, Pi.one_apply]
    by_cases h0 : occurrenceCount B ω = 0
    · rw [if_pos h0, if_neg]
      rintro ⟨i, hi⟩
      unfold occurrenceCount at h0
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff] at h0
      exact h0 (Finset.mem_univ i) hi
    · rw [if_neg h0, if_pos]
      unfold occurrenceCount at h0
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff] at h0
      push Not at h0
      obtain ⟨i, _, hi⟩ := h0
      exact ⟨i, hi⟩

/-- (L4) The exceedance events are measurable and the joint CDF is the complement of their
union. -/
theorem cdf_compl {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {r : ℕ} (ξ : Ω → Fin r → ℝ) (hξ : Measurable ξ) (x : Fin r → ℝ) :
    (∀ i, MeasurableSet (exceedanceEvent ξ x i)) ∧
      jointCDF μ ξ x = 1 - μ.real (⋃ i, exceedanceEvent ξ x i) := by
  have hm : ∀ i, MeasurableSet (exceedanceEvent ξ x i) := fun i =>
    measurableSet_lt measurable_const ((measurable_pi_apply i).comp hξ)
  refine ⟨hm, ?_⟩
  unfold jointCDF
  have : {ω | ∀ i, ξ ω i ≤ x i} = (⋃ i, exceedanceEvent ξ x i)ᶜ := by
    ext ω; simp [exceedanceEvent]
  rw [this, measureReal_compl (MeasurableSet.iUnion hm), probReal_univ]

/-! ### PartL2 -/
theorem L2_choose_cast (n : ℕ) : ((n + 1).choose 2 : ℝ) = ((n : ℝ) + 1) * (n : ℝ) / 2 := by
  rw [Nat.cast_choose_two]
  push_cast
  ring

/-- Every feasible objective value is at most `S₁ - (2/r) S₂`. -/
theorem L2_upper {r : ℕ} (hr : 1 ≤ r) {S₁ S₂ : ℝ} (v : Fin r → ℝ)
    (hv : v ∈ lpFeasible r S₁ S₂) : ∑ i, v i ≤ vMaxClosedForm r S₁ S₂ := by
  obtain ⟨h1, h2, h3⟩ := hv
  have hrpos : (0 : ℝ) < r := by exact_mod_cast hr
  have key : vMaxClosedForm r S₁ S₂ - ∑ i, v i =
      ∑ i : Fin r, v i * ((i : ℝ) * ((r : ℝ) - 1 - (i : ℝ)) / r) := by
    unfold vMaxClosedForm
    rw [← h1, ← h2, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [L2_choose_cast]
    field_simp
    ring
  have hnn : 0 ≤ ∑ i : Fin r, v i * ((i : ℝ) * ((r : ℝ) - 1 - (i : ℝ)) / r) := by
    refine Finset.sum_nonneg fun i _ => ?_
    have hi : (i : ℝ) + 1 ≤ r := by exact_mod_cast i.isLt
    have : 0 ≤ (i : ℝ) * ((r : ℝ) - 1 - (i : ℝ)) / r :=
      div_nonneg (mul_nonneg (Nat.cast_nonneg _) (by linarith)) hrpos.le
    exact mul_nonneg (h3 i) this
  linarith

/-- Consequences of feasibility used for the attaining point. -/
theorem L2_data_nonneg {r : ℕ} {S₁ S₂ : ℝ} (v : Fin r → ℝ)
    (hv : v ∈ lpFeasible r S₁ S₂) : 0 ≤ S₂ ∧ 2 * S₂ ≤ ((r : ℝ) - 1) * S₁ := by
  obtain ⟨h1, h2, h3⟩ := hv
  refine ⟨?_, ?_⟩
  · rw [← h2]
    exact Finset.sum_nonneg fun i _ => mul_nonneg (Nat.cast_nonneg _) (h3 i)
  · have key : ((r : ℝ) - 1) * S₁ - 2 * S₂ =
        ∑ i : Fin r, v i * (((i : ℝ) + 1) * ((r : ℝ) - 1 - (i : ℝ))) := by
      rw [← h1, ← h2, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [L2_choose_cast]
      ring
    have hnn : 0 ≤ ∑ i : Fin r, v i * (((i : ℝ) + 1) * ((r : ℝ) - 1 - (i : ℝ))) := by
      refine Finset.sum_nonneg fun i _ => ?_
      have hi : (i : ℝ) + 1 ≤ r := by exact_mod_cast i.isLt
      exact mul_nonneg (h3 i) (mul_nonneg (by positivity) (by linarith))
    linarith

/-- The upper bound is attained. -/
theorem L2_attained {r : ℕ} (hr : 1 ≤ r) {S₁ S₂ : ℝ} (hne : (lpFeasible r S₁ S₂).Nonempty) :
    vMaxClosedForm r S₁ S₂ ∈ lpObjectiveValues r S₁ S₂ := by
  obtain ⟨v, hv⟩ := hne
  obtain ⟨hS₂, hS⟩ := L2_data_nonneg v hv
  rcases Nat.lt_or_ge r 2 with hlt | hr2
  · obtain rfl : r = 1 := by omega
    refine ⟨v, hv, ?_⟩
    obtain ⟨h1, h2, _⟩ := hv
    simp only [Fin.sum_univ_one, Fin.val_zero] at h1 h2 ⊢
    norm_num at h1 h2
    unfold vMaxClosedForm
    rw [← h2, h1]
    norm_num
  · have hr' : (2 : ℝ) ≤ r := by exact_mod_cast hr2
    have hr1 : (0 : ℝ) < (r : ℝ) - 1 := by linarith
    have hrpos : (0 : ℝ) < r := by linarith
    set a : ℝ := S₁ - 2 * S₂ / ((r : ℝ) - 1) with ha
    set b : ℝ := 2 * S₂ / ((r : ℝ) * ((r : ℝ) - 1)) with hb
    let i0 : Fin r := ⟨0, by omega⟩
    let i1 : Fin r := ⟨r - 1, by omega⟩
    have hcast : ((r - 1 : ℕ) : ℝ) = (r : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega)]; simp
    let w : Fin r → ℝ := fun j => (if j = i0 then a else 0) + (if j = i1 then b else 0)
    have hsum : ∀ c : Fin r → ℝ, ∑ j, c j * w j = c i0 * a + c i1 * b := by
      intro c
      simp only [w, mul_add, mul_ite, mul_zero, Finset.sum_add_distrib, Finset.sum_ite_eq',
        Finset.mem_univ, if_true]
    have ha0 : 0 ≤ a := by
      rw [ha, sub_nonneg, div_le_iff₀ hr1]
      linarith
    have hb0 : 0 ≤ b := by
      rw [hb]; positivity
    refine ⟨w, ⟨?_, ?_, ?_⟩, ?_⟩
    · rw [hsum]
      simp only [i0, i1]
      rw [hcast, ha, hb]
      field_simp
      ring
    · rw [hsum]
      simp only [i0, i1]
      rw [L2_choose_cast, L2_choose_cast, hcast, hb]
      field_simp
      ring
    · intro j
      simp only [w]
      split_ifs <;> linarith
    · have := hsum (fun _ => 1)
      simp only [one_mul] at this
      show ∑ i, w i = _
      rw [this]
      unfold vMaxClosedForm
      rw [ha, hb]
      field_simp
      ring

/-- (L2) The maximization LP: every objective value is at most `S₁ - (2/r) S₂`, which is attained. -/
theorem lp_max {r : ℕ} (hr : 1 ≤ r) {S₁ S₂ : ℝ} (hne : (lpFeasible r S₁ S₂).Nonempty) :
    lpMax r S₁ S₂ = vMaxClosedForm r S₁ S₂ ∧
      ∀ y ∈ lpObjectiveValues r S₁ S₂, y ≤ vMaxClosedForm r S₁ S₂ := by
  have hub : ∀ y ∈ lpObjectiveValues r S₁ S₂, y ≤ vMaxClosedForm r S₁ S₂ := by
    rintro y ⟨v, hv, rfl⟩
    exact L2_upper hr v hv
  refine ⟨?_, hub⟩
  exact IsGreatest.csSup_eq ⟨L2_attained hr hne, hub⟩

/-! ### PartL3 -/
theorem L3_choose_two (i : ℕ) :
    (((i + 1).choose 2 : ℕ) : ℝ) = ((i : ℝ) + 1) * (i : ℝ) / 2 := by
  rw [Nat.cast_choose_two]; push_cast; ring

/-- Lower bound: for every natural `k ≥ 1` and every feasible point. -/
theorem L3_lower {r : ℕ} {S₁ S₂ : ℝ} (k : ℕ) (hk : 1 ≤ k) (v : Fin r → ℝ)
    (hv : v ∈ lpFeasible r S₁ S₂) :
    2 / ((k : ℝ) + 1) * S₁ - 2 / ((k : ℝ) * ((k : ℝ) + 1)) * S₂ ≤ ∑ i, v i := by
  obtain ⟨h1, h2, h0⟩ := hv
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
  rw [← h1, ← h2, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, ← sub_nonneg,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_nonneg
  intro i _
  rw [L3_choose_two]
  have hp : 0 ≤ (((i : ℕ) : ℝ) + 1 - k) * (((i : ℕ) : ℝ) - k) := by
    rcases le_or_gt k (i : ℕ) with h | h
    · have h' : (k : ℝ) ≤ ((i : ℕ) : ℝ) := by exact_mod_cast h
      apply mul_nonneg <;> linarith
    · have h' : ((i : ℕ) : ℝ) + 1 ≤ (k : ℝ) := by exact_mod_cast h
      apply mul_nonneg_of_nonpos_of_nonpos <;> linarith
  have heq : v i - (2 / ((k : ℝ) + 1) * ((((i : ℕ) : ℝ) + 1) * v i)
      - 2 / ((k : ℝ) * ((k : ℝ) + 1)) * (((((i : ℕ) : ℝ) + 1) * ((i : ℕ) : ℝ) / 2) * v i))
      = v i * ((((i : ℕ) : ℝ) + 1 - k) * (((i : ℕ) : ℝ) - k)) / ((k : ℝ) * ((k : ℝ) + 1)) := by
    field_simp
    ring
  rw [heq]
  apply div_nonneg (mul_nonneg (h0 i) hp)
  positivity

/-- From a feasible point: `0 ≤ S₂` and `2 S₂ ≤ (r - 1) S₁`. -/
theorem L3_bounds {r : ℕ} {S₁ S₂ : ℝ} (v : Fin r → ℝ) (hv : v ∈ lpFeasible r S₁ S₂) :
    0 ≤ S₂ ∧ 2 * S₂ ≤ ((r : ℝ) - 1) * S₁ := by
  obtain ⟨h1, h2, h0⟩ := hv
  constructor
  · rw [← h2]
    exact Finset.sum_nonneg fun i _ => mul_nonneg (by positivity) (h0 i)
  · rw [← h1, ← h2, Finset.mul_sum, Finset.mul_sum, ← sub_nonneg, ← Finset.sum_sub_distrib]
    apply Finset.sum_nonneg
    intro i _
    rw [L3_choose_two]
    have hi : ((i : ℕ) : ℝ) + 1 ≤ (r : ℝ) := by exact_mod_cast i.isLt
    have heq : ((r : ℝ) - 1) * ((((i : ℕ) : ℝ) + 1) * v i)
        - 2 * (((((i : ℕ) : ℝ) + 1) * ((i : ℕ) : ℝ) / 2) * v i)
        = (((i : ℕ) : ℝ) + 1) * ((r : ℝ) - 1 - ((i : ℕ) : ℝ)) * v i := by ring
    rw [heq]
    apply mul_nonneg (mul_nonneg (by positivity) (by linarith)) (h0 i)

/-- A point supported on two indices `a`, `b` (possibly with `y = 0`). -/
theorem L3_two_point {r : ℕ} (a : Fin r) (x : ℝ) (b : Fin r) (y : ℝ)
    (c : Fin r → ℝ) :
    ∑ j, c j * ((if j = a then x else 0) + (if j = b then y else 0)) = c a * x + c b * y := by
  simp [mul_add, Finset.sum_add_distrib, mul_ite]

theorem L3_one_point {r : ℕ} (a : Fin r) (x : ℝ) (c : Fin r → ℝ) :
    ∑ j, c j * (if j = a then x else 0) = c a * x := by
  simp [mul_ite]

theorem lp_min {r : ℕ} (hr : 1 ≤ r) {S₁ S₂ : ℝ} (hne : (lpFeasible r S₁ S₂).Nonempty)
    (hS₁ : 0 < S₁) :
    lpMin r S₁ S₂ = vMinClosedForm S₁ S₂ ∧
      ∀ y ∈ lpObjectiveValues r S₁ S₂, vMinClosedForm S₁ S₂ ≤ y := by
  have hlow : ∀ y ∈ lpObjectiveValues r S₁ S₂, vMinClosedForm S₁ S₂ ≤ y := by
    rintro y ⟨v, hv, rfl⟩
    exact L3_lower (kStar S₁ S₂) (by unfold kStar; omega) v hv
  refine ⟨?_, hlow⟩
  obtain ⟨v₀, hv₀⟩ := hne
  obtain ⟨hS₂, hS₂r⟩ := L3_bounds v₀ hv₀
  set q : ℝ := 2 * S₂ / S₁ with hq
  set n : ℕ := ⌊q⌋₊ with hn
  have hq0 : 0 ≤ q := by positivity
  have hnq : (n : ℝ) ≤ q := Nat.floor_le hq0
  have hqn : q < (n : ℝ) + 1 := Nat.lt_floor_add_one q
  have hqr : q ≤ (r : ℝ) - 1 := by
    rw [hq, div_le_iff₀ hS₁]; linarith
  have h2lo : (n : ℝ) * S₁ ≤ 2 * S₂ := by
    have := mul_le_mul_of_nonneg_right hnq hS₁.le
    rwa [hq, div_mul_cancel₀ _ hS₁.ne'] at this
  have h2hi : 2 * S₂ < ((n : ℝ) + 1) * S₁ := by
    have := mul_lt_mul_of_pos_right hqn hS₁
    rwa [hq, div_mul_cancel₀ _ hS₁.ne'] at this
  have hnr : n + 1 ≤ r := by
    have : (n : ℝ) + 1 ≤ r := by linarith
    exact_mod_cast this
  have hk : (kStar S₁ S₂ : ℝ) = (n : ℝ) + 1 := by
    simp [kStar, hn, hq]
  set x : ℝ := (((n : ℝ) + 1) * S₁ - 2 * S₂) / ((n : ℝ) + 1) with hx
  set y : ℝ := (2 * S₂ - (n : ℝ) * S₁) / ((n : ℝ) + 2) with hy
  have hx0 : 0 ≤ x := by rw [hx]; apply div_nonneg <;> [linarith; positivity]
  have hy0 : 0 ≤ y := by rw [hy]; apply div_nonneg <;> [linarith; positivity]
  have hsum : x + y = vMinClosedForm S₁ S₂ := by
    rw [vMinClosedForm, hk, hx, hy]
    field_simp
    ring
  have hE1 : ((n : ℝ) + 1) * x + ((n : ℝ) + 2) * y = S₁ := by
    rw [hx, hy]; field_simp; ring
  have hE2 : ((n : ℝ) + 1) * (n : ℝ) / 2 * x + ((n : ℝ) + 2) * ((n : ℝ) + 1) / 2 * y = S₂ := by
    rw [hx, hy]; field_simp; ring
  have hmem : vMinClosedForm S₁ S₂ ∈ lpObjectiveValues r S₁ S₂ := by
    rcases Nat.lt_or_ge (n + 1) r with hlt | hge
    · -- two indices `n` and `n + 1`
      let a : Fin r := ⟨n, by omega⟩
      let b : Fin r := ⟨n + 1, hlt⟩
      refine ⟨fun j => (if j = a then x else 0) + (if j = b then y else 0), ⟨?_, ?_, ?_⟩, ?_⟩
      · rw [L3_two_point a x b y (fun j => ((j : ℕ) : ℝ) + 1)]
        simp only [a, b]; push_cast; linarith
      · rw [L3_two_point a x b y (fun j => ((((j : ℕ) + 1).choose 2 : ℕ) : ℝ))]
        simp only [a, b]
        rw [L3_choose_two, L3_choose_two]; push_cast
        linarith
      · intro j
        dsimp only
        split_ifs <;> linarith
      · have := L3_two_point a x b y (fun _ => (1 : ℝ))
        simp only [one_mul] at this
        dsimp only
        rw [this, ← hsum]
    · -- `n + 1 = r`: then `y = 0`
      have hnr' : n + 1 = r := le_antisymm hnr hge
      have hrn : (r : ℝ) = (n : ℝ) + 1 := by exact_mod_cast hnr'.symm
      have hyz : y = 0 := by
        rw [hy]
        have : 2 * S₂ = (n : ℝ) * S₁ := by rw [hrn] at hS₂r; linarith
        rw [this, sub_self, zero_div]
      let a : Fin r := ⟨n, by omega⟩
      refine ⟨fun j => if j = a then x else 0, ⟨?_, ?_, ?_⟩, ?_⟩
      · rw [L3_one_point a x (fun j => ((j : ℕ) : ℝ) + 1)]
        simp only [a]; rw [hyz] at hE1; linarith
      · rw [L3_one_point a x (fun j => ((((j : ℕ) + 1).choose 2 : ℕ) : ℝ))]
        simp only [a]
        rw [L3_choose_two]; rw [hyz] at hE2; linarith
      · intro j
        dsimp only
        split_ifs <;> linarith
      · have := L3_one_point a x (fun _ => (1 : ℝ))
        simp only [one_mul] at this
        dsimp only
        rw [this, ← hsum, hyz, add_zero]
  exact (IsLeast.csInf_eq ⟨hmem, hlow⟩)

end KallP

open KallP

theorem solution {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {r : ℕ} (hr : 1 ≤ r) :
    (∀ B : Fin r → Set Ω, (∀ i, MeasurableSet (B i)) →
      lpMax r (binomialMoment μ B 1) (binomialMoment μ B 2) =
        vMaxClosedForm r (binomialMoment μ B 1) (binomialMoment μ B 2) ∧
      μ.real (⋃ i, B i) ≤ vMaxClosedForm r (binomialMoment μ B 1) (binomialMoment μ B 2) ∧
      (0 < binomialMoment μ B 1 →
        lpMin r (binomialMoment μ B 1) (binomialMoment μ B 2) =
          vMinClosedForm (binomialMoment μ B 1) (binomialMoment μ B 2) ∧
        vMinClosedForm (binomialMoment μ B 1) (binomialMoment μ B 2) ≤ μ.real (⋃ i, B i))) ∧
    (∀ ξ : Ω → Fin r → ℝ, Measurable ξ → ∀ x : Fin r → ℝ,
      1 - binomialMoment μ (exceedanceEvent ξ x) 1 +
          2 / (r : ℝ) * binomialMoment μ (exceedanceEvent ξ x) 2 ≤ jointCDF μ ξ x ∧
      (0 < binomialMoment μ (exceedanceEvent ξ x) 1 →
        jointCDF μ ξ x ≤
          1 - vMinClosedForm (binomialMoment μ (exceedanceEvent ξ x) 1)
                (binomialMoment μ (exceedanceEvent ξ x) 2))) := by
  have partA : ∀ B : Fin r → Set Ω, (∀ i, MeasurableSet (B i)) →
      lpMax r (binomialMoment μ B 1) (binomialMoment μ B 2) =
        vMaxClosedForm r (binomialMoment μ B 1) (binomialMoment μ B 2) ∧
      μ.real (⋃ i, B i) ≤ vMaxClosedForm r (binomialMoment μ B 1) (binomialMoment μ B 2) ∧
      (0 < binomialMoment μ B 1 →
        lpMin r (binomialMoment μ B 1) (binomialMoment μ B 2) =
          vMinClosedForm (binomialMoment μ B 1) (binomialMoment μ B 2) ∧
        vMinClosedForm (binomialMoment μ B 1) (binomialMoment μ B 2) ≤ μ.real (⋃ i, B i)) := by
    intro B hB
    obtain ⟨v, hv, hsum⟩ := data_feasible μ B hB
    have hmem : μ.real (⋃ i, B i) ∈ lpObjectiveValues r (binomialMoment μ B 1)
        (binomialMoment μ B 2) := ⟨v, hv, hsum⟩
    obtain ⟨hmax, hle⟩ := lp_max hr ⟨v, hv⟩
    refine ⟨hmax, hle _ hmem, fun hS => ?_⟩
    obtain ⟨hmin, hge⟩ := lp_min hr ⟨v, hv⟩ hS
    exact ⟨hmin, hge _ hmem⟩
  refine ⟨partA, fun ξ hξ x => ?_⟩
  obtain ⟨hmeas, hcdf⟩ := cdf_compl μ ξ hξ x
  obtain ⟨-, hub, hlb⟩ := partA (exceedanceEvent ξ x) hmeas
  refine ⟨?_, fun hS => ?_⟩
  · rw [hcdf]; unfold vMaxClosedForm at hub; linarith
  · rw [hcdf]; linarith [(hlb hS).2]
