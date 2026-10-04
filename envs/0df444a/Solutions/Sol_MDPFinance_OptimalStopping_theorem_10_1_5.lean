-- Prove2me | solution 1 for MDPFinance.OptimalStopping.theorem_10_1_5
-- status  : ACCEPTED   (disprove)
-- author  : @mrfancypants
-- created : 2026-10-03T19:35:42.260204+00:00
-- url     : https://prove2.me/submissions/ad0f2452-27c8-4ad6-96a6-97fd78640853

import Mathlib
import Definitions.Def_MDPFinance_OptimalStopping_Stationary

open MeasureTheory Filter Topology MDPFinance.OptimalStopping

namespace OS105Cex

noncomputable def μ1 : Measure ℕ :=
  Measure.sum fun k : ℕ => ((2 : ENNReal)⁻¹ ^ (k + 1)) • Measure.dirac (k + 1)

theorem μ1_univ : μ1 Set.univ = 1 := by
  unfold μ1
  rw [Measure.sum_apply _ MeasurableSet.univ]
  simp only [Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
  rw [show (fun k : ℕ => (2 : ENNReal)⁻¹ ^ (k + 1)) = fun k => 2⁻¹ * 2⁻¹ ^ k by
    funext k; rw [pow_succ, mul_comm]]
  rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric, ENNReal.one_sub_inv_two, inv_inv,
    ENNReal.inv_mul_cancel (by norm_num) (by norm_num)]

theorem μ1_zero : μ1 {0} = 0 := by
  unfold μ1
  rw [Measure.sum_apply _ (measurableSet_singleton 0)]
  simp

noncomputable def QXf (x : ℕ) : Measure ℕ := if x = 0 then μ1 else Measure.dirac x

instance (x : ℕ) : IsProbabilityMeasure (QXf x) := by
  unfold QXf
  split_ifs
  · exact ⟨μ1_univ⟩
  · infer_instance

noncomputable def P0 : StationaryProblem ℕ where
  QX := QXf
  QX_prob := fun x => inferInstance
  QX_meas := Measurable.of_discrete
  c := fun y => if y = 0 then 0 else (2 : ℝ) ^ y
  c_meas := Measurable.of_discrete
  g := fun y => if y = 0 then 0 else -(2 : ℝ) ^ y
  g_meas := Measurable.of_discrete
  beta := 1
  beta_mem := by norm_num

theorem ae_ne_zero (x : ℕ) : ∀ᵐ y ∂(QXf x), y ≠ 0 := by
  unfold QXf
  split_ifs with hx
  · exact measure_eq_zero_iff_ae_notMem.mp μ1_zero
  · rw [ae_dirac_iff (MeasurableSet.of_discrete)]
    exact hx

open Classical in
theorem cyl_abs (y : ℕ) (hy : y ≠ 0) : ∀ (m : ℕ) (B : ℕ → Set ℕ),
    P0.cyl m B y = if ∀ i < m, y ∈ B i then 1 else 0 := by
  intro m
  induction m with
  | zero => intro B; simp [StationaryProblem.cyl]
  | succ m ih =>
    intro B
    show ∫⁻ z in B 0, P0.cyl m (fun i => B (i + 1)) z ∂(QXf y) = _
    have hq : QXf y = Measure.dirac y := by unfold QXf; rw [if_neg hy]
    rw [hq, ← lintegral_indicator MeasurableSet.of_discrete, lintegral_dirac]
    by_cases h0 : y ∈ B 0
    · rw [Set.indicator_of_mem h0, ih]
      congr 1
      apply propext
      constructor
      · intro h i hi
        cases i with
        | zero => exact h0
        | succ i => exact h i (by omega)
      · intro h i hi
        exact h (i + 1) (by omega)
    · rw [Set.indicator_of_notMem h0, if_neg]
      intro h
      exact h0 (h 0 (by omega))

theorem cyl_gen (x : ℕ) (m : ℕ) (B : ℕ → Set ℕ) :
    P0.cyl (m + 1) B x = QXf x {y | ∀ i < m + 1, y ∈ B i} := by
  show ∫⁻ z in B 0, P0.cyl m (fun i => B (i + 1)) z ∂(QXf x) = _
  have hae : (fun z => P0.cyl m (fun i => B (i + 1)) z) =ᵐ[(QXf x).restrict (B 0)]
      {y | ∀ i < m, y ∈ B (i + 1)}.indicator 1 := by
    refine ae_restrict_of_ae ?_
    filter_upwards [ae_ne_zero x] with z hz
    rw [cyl_abs z hz]
    by_cases hc : ∀ i < m, z ∈ B (i + 1)
    · rw [if_pos hc, Set.indicator_of_mem (show z ∈ {y | ∀ i < m, y ∈ B (i + 1)} from hc)]; rfl
    · rw [if_neg hc, Set.indicator_of_notMem (show z ∉ {y | ∀ i < m, y ∈ B (i + 1)} from hc)]
  rw [lintegral_congr_ae hae, lintegral_indicator_one MeasurableSet.of_discrete,
    Measure.restrict_apply MeasurableSet.of_discrete]
  congr 1
  ext y
  simp only [Set.mem_inter_iff, Set.mem_setOf_eq]
  constructor
  · rintro ⟨h, h0⟩ i hi
    cases i with
    | zero => exact h0
    | succ i => exact h i (by omega)
  · intro h
    exact ⟨fun i hi => h (i + 1) (by omega), h 0 (by omega)⟩

def emb (x : ℕ) : ℕ → (ℕ → ℕ) := fun y i => if i = 0 then x else y

noncomputable def Pr0 (x : ℕ) : Measure (ℕ → ℕ) := (QXf x).map (emb x)

theorem hPr : P0.IsPathLaw Pr0 := by
  refine ⟨fun x => ?_, fun x m B hB => ?_⟩
  · unfold Pr0
    exact Measure.isProbabilityMeasure_map (Measurable.of_discrete (f := emb x)).aemeasurable
  have hS : MeasurableSet {w : ℕ → ℕ | ∀ i ≤ m, w i ∈ B i} := by
    have : {w : ℕ → ℕ | ∀ i ≤ m, w i ∈ B i} = ⋂ i ∈ Set.Iic m, (fun w : ℕ → ℕ => w i) ⁻¹' B i := by
      ext w; simp
    rw [this]
    exact MeasurableSet.biInter (Set.to_countable _) fun i _ => measurable_pi_apply i (hB i)
  unfold Pr0
  rw [Measure.map_apply Measurable.of_discrete hS]
  by_cases h0 : x ∈ B 0
  · rw [Set.indicator_of_mem h0]
    cases m with
    | zero =>
      have : emb x ⁻¹' {w : ℕ → ℕ | ∀ i ≤ 0, w i ∈ B i} = Set.univ := by
        ext y; simp [emb, h0]
      rw [this, measure_univ]
      rfl
    | succ m =>
      rw [cyl_gen]
      congr 1
      ext y
      simp only [Set.mem_preimage, Set.mem_setOf_eq, emb]
      constructor
      · intro h i hi
        have := h (i + 1) (by omega)
        simpa using this
      · intro h i hi
        cases i with
        | zero => simpa using h0
        | succ i => simpa using h i (by omega)
  · rw [Set.indicator_of_notMem h0]
    have : emb x ⁻¹' {w : ℕ → ℕ | ∀ i ≤ m, w i ∈ B i} = ∅ := by
      ext y
      simp only [Set.mem_preimage, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      intro h
      exact h0 (by simpa [emb] using h 0 (by omega))
    rw [this, measure_empty]

theorem eI_dirac (y : ℕ) (w : ℕ → EReal) : erealIntegral (Measure.dirac y) w = w y := by
  unfold erealIntegral
  rw [lintegral_dirac, lintegral_dirac]
  generalize w y = z
  induction z using EReal.rec with
  | bot => simp
  | top => simp
  | coe t =>
    rw [← EReal.coe_neg]
    have h1 : (((t : EReal) ⊔ 0).toENNReal : EReal) = ((max t 0 : ℝ) : EReal) := by
      rcases le_total t 0 with h | h
      · rw [sup_eq_right.mpr (by exact_mod_cast h), max_eq_right h]; simp
      · rw [sup_eq_left.mpr (by exact_mod_cast h), max_eq_left h]
        simp [EReal.coe_ennreal_ofReal, h]
    have h2 : ((((-t : ℝ) : EReal) ⊔ 0).toENNReal : EReal) = ((max (-t) 0 : ℝ) : EReal) := by
      rcases le_total (-t) 0 with h | h
      · rw [sup_eq_right.mpr (by exact_mod_cast h), max_eq_right h]; simp
      · rw [sup_eq_left.mpr (by exact_mod_cast h), max_eq_left h]
        simp [EReal.coe_ennreal_ofReal, h]
    rw [h1, h2, ← EReal.coe_neg, ← EReal.coe_add]
    congr 1
    rcases le_total t 0 with h | h
    · rw [max_eq_right h, max_eq_left (by linarith)]; ring
    · rw [max_eq_left h, max_eq_right (by linarith)]; ring

theorem lint_μ1 (f : ℕ → ENNReal) :
    ∫⁻ z, f z ∂μ1 = ∑' k : ℕ, (2 : ENNReal)⁻¹ ^ (k + 1) * f (k + 1) := by
  unfold μ1
  rw [lintegral_sum_measure]
  congr 1
  funext k
  rw [lintegral_smul_measure, lintegral_dirac]
  rfl

/-- `∑ 2^{-(k+1)} * ofReal (2^{k+1}) = ⊤`. -/
theorem tsum_top : ∑' k : ℕ, (2 : ENNReal)⁻¹ ^ (k + 1) * ENNReal.ofReal ((2 : ℝ) ^ (k + 1)) = ⊤ := by
  have : ∀ k : ℕ, (2 : ENNReal)⁻¹ ^ (k + 1) * ENNReal.ofReal ((2 : ℝ) ^ (k + 1)) = 1 := by
    intro k
    rw [ENNReal.ofReal_pow (by norm_num), ← mul_pow, ENNReal.ofReal_ofNat,
      ENNReal.inv_mul_cancel (by norm_num) (by norm_num), one_pow]
  simp only [this]
  exact ENNReal.tsum_const_eq_top_of_ne_zero one_ne_zero

theorem g_succ (k : ℕ) : P0.g (k + 1) = -(2 : ℝ) ^ (k + 1) := by
  show (if k + 1 = 0 then (0 : ℝ) else -(2 : ℝ) ^ (k + 1)) = _
  simp

theorem c_succ (k : ℕ) : P0.c (k + 1) = (2 : ℝ) ^ (k + 1) := by
  show (if k + 1 = 0 then (0 : ℝ) else (2 : ℝ) ^ (k + 1)) = _
  simp

theorem QX_succ (k : ℕ) : P0.QX (k + 1) = Measure.dirac (k + 1) := by
  show QXf (k + 1) = _
  unfold QXf; simp

theorem QX_zero : P0.QX 0 = μ1 := by
  show QXf 0 = _
  unfold QXf; simp

theorem J1_succ (k : ℕ) : P0.J 1 (k + 1) = 0 := by
  show max ((P0.g (k + 1) : ℝ) : EReal) (((P0.c (k + 1) : ℝ) : EReal) + ((1 : ℝ) : EReal) *
    erealIntegral (P0.QX (k + 1)) (P0.J 0)) = 0
  rw [QX_succ, eI_dirac]
  show max ((P0.g (k + 1) : ℝ) : EReal) (((P0.c (k + 1) : ℝ) : EReal) + ((1 : ℝ) : EReal) *
    ((P0.g (k + 1) : ℝ) : EReal)) = 0
  rw [g_succ, c_succ, EReal.coe_one, one_mul, ← EReal.coe_add]
  rw [show (2 : ℝ) ^ (k + 1) + -(2 : ℝ) ^ (k + 1) = 0 by ring]
  have : ((-(2 : ℝ) ^ (k + 1) : ℝ) : EReal) ≤ ((0 : ℝ) : EReal) := by
    have h2 : -(2 : ℝ) ^ (k + 1) ≤ 0 := neg_nonpos.mpr (by positivity)
    exact_mod_cast h2
  rw [max_eq_right this, EReal.coe_zero]

theorem d1_succ (k : ℕ) : P0.d 1 (k + 1) = ((-(2 : ℝ) ^ (k + 1) : ℝ) : EReal) := by
  show ((P0.g (k + 1) : ℝ) : EReal) - ((P0.c (k + 1) : ℝ) : EReal) - ((1 : ℝ) : EReal) *
    erealIntegral (P0.QX (k + 1)) (P0.J 0) = _
  rw [QX_succ, eI_dirac]
  show ((P0.g (k + 1) : ℝ) : EReal) - ((P0.c (k + 1) : ℝ) : EReal) - ((1 : ℝ) : EReal) *
    ((P0.g (k + 1) : ℝ) : EReal) = _
  rw [g_succ, c_succ, EReal.coe_one, one_mul, ← EReal.coe_sub, ← EReal.coe_sub]
  congr 1
  ring

theorem d1_zero : P0.d 1 0 = ⊤ := by
  show ((P0.g 0 : ℝ) : EReal) - ((P0.c 0 : ℝ) : EReal) - ((1 : ℝ) : EReal) *
    erealIntegral (P0.QX 0) (P0.J 0) = ⊤
  rw [QX_zero]
  have hg0 : P0.g 0 = 0 := by simp [P0]
  have hc0 : P0.c 0 = 0 := by simp [P0]
  have hI : erealIntegral μ1 (P0.J 0) = ⊥ := by
    unfold erealIntegral
    rw [lint_μ1, lint_μ1]
    have hpos : ∀ k : ℕ, ((P0.J 0 (k + 1)) ⊔ 0).toENNReal = 0 := by
      intro k
      show ((((P0.g (k + 1) : ℝ) : EReal)) ⊔ 0).toENNReal = 0
      have h2 : -(2 : ℝ) ^ (k + 1) ≤ 0 := neg_nonpos.mpr (by positivity)
      have h3 : ((-(2 : ℝ) ^ (k + 1) : ℝ) : EReal) ≤ 0 := by exact_mod_cast h2
      rw [g_succ, sup_eq_right.mpr h3]
      simp
    have hneg : ∀ k : ℕ, ((-(P0.J 0 (k + 1))) ⊔ 0).toENNReal = ENNReal.ofReal ((2 : ℝ) ^ (k + 1)) := by
      intro k
      show ((-(((P0.g (k + 1) : ℝ) : EReal))) ⊔ 0).toENNReal = _
      have h3 : (0 : EReal) ≤ (((2 : ℝ) ^ (k + 1) : ℝ) : EReal) := by
        exact_mod_cast (by positivity : (0 : ℝ) ≤ 2 ^ (k + 1))
      rw [g_succ, ← EReal.coe_neg, neg_neg, sup_eq_left.mpr h3]
      rfl
    simp only [hpos, hneg, mul_zero, tsum_zero, tsum_top]
    simp
  rw [hI, hg0, hc0, EReal.coe_one, one_mul]
  simp

theorem d2_zero : P0.d 2 0 = 0 := by
  show ((P0.g 0 : ℝ) : EReal) - ((P0.c 0 : ℝ) : EReal) - ((1 : ℝ) : EReal) *
    erealIntegral (P0.QX 0) (P0.J 1) = 0
  rw [QX_zero]
  have hg0 : P0.g 0 = 0 := by simp [P0]
  have hc0 : P0.c 0 = 0 := by simp [P0]
  have hI : erealIntegral μ1 (P0.J 1) = 0 := by
    unfold erealIntegral
    rw [lint_μ1, lint_μ1]
    simp [J1_succ]
  rw [hI, hg0, hc0]
  simp

theorem rhs_bot : P0.d 1 0 - (P0.beta : EReal) *
    erealIntegral (P0.QX 0) (fun y => max (-P0.d 1 y) 0) = ⊥ := by
  rw [QX_zero, d1_zero]
  have hI : erealIntegral μ1 (fun y => max (-P0.d 1 y) 0) = ⊤ := by
    unfold erealIntegral
    rw [lint_μ1, lint_μ1]
    have hpos : ∀ k : ℕ, ((max (-P0.d 1 (k + 1)) 0) ⊔ 0).toENNReal =
        ENNReal.ofReal ((2 : ℝ) ^ (k + 1)) := by
      intro k
      rw [d1_succ, ← EReal.coe_neg, neg_neg]
      have h0 : ((0 : ℝ) : EReal) ≤ (((2 : ℝ) ^ (k + 1) : ℝ) : EReal) := by
        exact_mod_cast (by positivity : (0 : ℝ) ≤ 2 ^ (k + 1))
      rw [max_eq_left (by simpa using h0), sup_eq_left.mpr (by simpa using h0)]
      rfl
    have hneg : ∀ k : ℕ, ((-(max (-P0.d 1 (k + 1)) 0)) ⊔ 0).toENNReal = 0 := by
      intro k
      have : -(max (-P0.d 1 (k + 1)) 0) ≤ 0 := by
        rw [EReal.neg_le, neg_zero]; exact le_max_right _ _
      rw [sup_eq_right.mpr this]
      simp
    simp only [hpos, hneg, mul_zero, tsum_zero, tsum_top]
    simp
  rw [hI]
  show (⊤ : EReal) - ((1 : ℝ) : EReal) * ⊤ = ⊥
  rw [EReal.coe_one, one_mul]
  simp

end OS105Cex

open OS105Cex in
theorem solution : ¬ (∀ {E : Type} [MeasurableSpace E] (P : StationaryProblem E) (N : ℕ)
    (Pr : E → Measure (ℕ → E)) (hPr : P.IsPathLaw Pr) (hBN : P.AssumptionBN Pr N),
    (∀ n : ℕ, n ≤ N → ∀ x : E, P.J n x = P.valueUpTo Pr n x) ∧
    (∀ (n : ℕ) (x : E), (P.g x : EReal) ≤ P.J n x ∧ P.J n x ≤ P.J (n + 1) x) ∧
    (∀ (n : ℕ) (x : E), 1 ≤ n →
      P.d (n + 1) x = P.d 1 x - (P.beta : EReal) * erealIntegral (P.QX x) (fun y => max (-P.d n y) 0)) ∧
    (P.stopSet 0 = Set.univ ∧
      (∀ n : ℕ, 1 ≤ n → P.stopSet n = {x : E | 0 ≤ P.d n x}) ∧
      (∀ n : ℕ, P.stopSet (n + 1) ⊆ P.stopSet n) ∧
      IsStopTime (hitTimeCapped (fun n => P.stopSet (N - n)) N) ∧
      ∀ x : E, P.EReward Pr (hitTimeCapped (fun n => P.stopSet (N - n)) N) x = P.J N x)) := by
  intro h
  have hBN : P0.AssumptionBN Pr0 0 := by
    intro x
    refine ⟨0, ENNReal.zero_lt_top, fun tau _ htau => ?_⟩
    have hz : ∀ w, ENNReal.ofReal ((∑ k ∈ Finset.range ((tau w).toNat),
        P0.beta ^ k * max (P0.c (w k)) 0) +
        P0.beta ^ (tau w).toNat * max (P0.g (w (tau w).toNat)) 0) = 0 := by
      intro w
      have h0 : tau w = 0 := by
        have := htau w
        simpa using this
      rw [h0]
      simp only [ENat.toNat_zero, Finset.range_zero, Finset.sum_empty, pow_zero, one_mul,
        zero_add]
      apply ENNReal.ofReal_eq_zero.mpr
      apply max_le _ le_rfl
      show (if w 0 = 0 then (0 : ℝ) else -(2 : ℝ) ^ (w 0)) ≤ 0
      split_ifs
      · exact le_rfl
      · exact neg_nonpos.mpr (by positivity)
    simp only [hz, lintegral_zero, le_refl]
  have H := (h P0 0 Pr0 hPr hBN).2.2.1 1 0 le_rfl
  rw [rhs_bot, d2_zero] at H
  exact absurd H (by simp)

#print axioms solution
