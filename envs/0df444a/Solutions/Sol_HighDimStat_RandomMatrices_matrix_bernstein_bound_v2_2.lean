-- Prove2me | solution 2 for HighDimStat.RandomMatrices.matrix_bernstein_bound_v2
-- status  : ACCEPTED   (disprove)
-- author  : @kmehltretter82
-- created : 2026-11-14T04:23:39.687282+00:00
-- url     : https://prove2.me/submissions/ed638038-ef32-4044-8e2e-9a25444fa76a

import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Probability.Independence.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Definitions.Def_HighDimStat_RandomMatrices_BernsteinConditionMatrix
import Definitions.Def_HighDimStat_RandomMatrices_matrixVariance
import Definitions.Def_HighDimStat_RandomMatrices_opNorm

open MeasureTheory ProbabilityTheory HighDimStat.RandomMatrices
open scoped ENNReal

noncomputable local instance instMeasMatrix {d : ℕ} :
    MeasurableSpace (Matrix (Fin d) (Fin d) ℝ) := by
  unfold Matrix; infer_instance

namespace MatrixBernsteinCounterexample

noncomputable section

/-! ### Part 1: `1 × 1` scalar-diagonal matrices and their spectral norm, rank, and Loewner order -/

def scalMat (c : ℝ) : Matrix (Fin 1) (Fin 1) ℝ :=
  Matrix.diagonal (fun _ : Fin 1 => c)

@[simp]
lemma scalMat_apply (c : ℝ) (i j : Fin 1) : scalMat c i j = c := by
  rw [Subsingleton.elim i j]
  simp [scalMat]

lemma scalMat_sub (a b : ℝ) : scalMat (a - b) = scalMat a - scalMat b := by
  ext i j; simp

lemma scalMat_smul (a b : ℝ) : a • scalMat b = scalMat (a * b) := by
  ext i j; simp

lemma scalMat_pow (c : ℝ) (j : ℕ) : scalMat c ^ j = scalMat (c ^ j) := by
  simp [scalMat, Matrix.diagonal_pow]

lemma scalMat_sum {ι : Type*} (s : Finset ι) (f : ι → ℝ) :
    (∑ i ∈ s, scalMat (f i)) = scalMat (∑ i ∈ s, f i) := by
  ext a b
  simp [Matrix.sum_apply]

lemma scalMat_isSymm (c : ℝ) : (scalMat c).IsSymm :=
  Matrix.isSymm_diagonal _

lemma scalMat_loewner {a b : ℝ} (hab : a ≤ b) : LoewnerLE (scalMat a) (scalMat b) := by
  unfold LoewnerLE
  rw [← scalMat_sub]
  exact Matrix.PosSemidef.diagonal fun _ => sub_nonneg.mpr hab

lemma opNorm_scalMat (c : ℝ) : opNorm (scalMat c) = |c| := by
  unfold opNorm
  have hclm : Matrix.toEuclideanCLM (𝕜 := ℝ) (scalMat c) =
      c • ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 1)) := by
    ext x i
    simp [Matrix.ofLp_toEuclideanCLM, scalMat, Matrix.mulVec_diagonal]
  have : Nontrivial (EuclideanSpace ℝ (Fin 1)) := by
    refine ⟨0, EuclideanSpace.single 0 (1 : ℝ), fun h => ?_⟩
    have h0 := congr_arg (fun v : EuclideanSpace ℝ (Fin 1) => v 0) h
    simp at h0
  rw [hclm, norm_smul, ContinuousLinearMap.norm_id, mul_one, Real.norm_eq_abs]

lemma rank_fin_one_le_one (M : Matrix (Fin 1) (Fin 1) ℝ) : Matrix.rank M ≤ 1 := by
  unfold Matrix.rank
  exact (Submodule.finrank_le _).trans (by simp)

/-! ### Part 2: Bernoulli product space `Fin n → Bool` -/

noncomputable def bernMeasure (p : ℝ) : Measure Bool :=
  ENNReal.ofReal p • Measure.dirac true + ENNReal.ofReal (1 - p) • Measure.dirac false

lemma bernMeasure_apply_true {p : ℝ} :
    bernMeasure p {true} = ENNReal.ofReal p := by
  simp [bernMeasure]

lemma bernMeasure_apply_false {p : ℝ} :
    bernMeasure p {false} = ENNReal.ofReal (1 - p) := by
  simp [bernMeasure]

lemma bernMeasure_isProb {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    IsProbabilityMeasure (bernMeasure p) := by
  refine ⟨?_⟩
  simp only [bernMeasure, Measure.coe_add, Measure.coe_smul, Pi.add_apply, Pi.smul_apply,
    Measure.dirac_apply' _ MeasurableSet.univ, Set.indicator_univ, Pi.one_apply, smul_eq_mul,
    mul_one]
  rw [← ENNReal.ofReal_add hp0 (by linarith)]
  norm_num

lemma integral_bernMeasure {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (g : Bool → ℝ) :
    ∫ b, g b ∂(bernMeasure p) = p * g true + (1 - p) * g false := by
  have h1 : Integrable g (ENNReal.ofReal p • Measure.dirac true) :=
    (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top
  have h2 : Integrable g (ENNReal.ofReal (1 - p) • Measure.dirac false) :=
    (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top
  unfold bernMeasure
  rw [integral_add_measure h1 h2, integral_smul_measure, integral_smul_measure,
    integral_dirac, integral_dirac, ENNReal.toReal_ofReal hp0,
    ENNReal.toReal_ofReal (by linarith), smul_eq_mul, smul_eq_mul]

noncomputable def prodBern (n : ℕ) (p : ℝ) : Measure (Fin n → Bool) :=
  Measure.pi (fun _ : Fin n => bernMeasure p)

lemma prodBern_isProb (n : ℕ) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    IsProbabilityMeasure (prodBern n p) := by
  have : IsProbabilityMeasure (bernMeasure p) := bernMeasure_isProb hp0 hp1
  unfold prodBern
  infer_instance

lemma integral_coord_prodBern {n : ℕ} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (i : Fin n) (g : Bool → ℝ) :
    ∫ ω, g (ω i) ∂(prodBern n p) = p * g true + (1 - p) * g false := by
  have : IsProbabilityMeasure (bernMeasure p) := bernMeasure_isProb hp0 hp1
  have hmp : MeasurePreserving (fun ω : Fin n → Bool => ω i) (prodBern n p) (bernMeasure p) :=
    MeasureTheory.measurePreserving_eval (fun _ : Fin n => bernMeasure p) i
  have haesm : AEStronglyMeasurable g (Measure.map (fun ω : Fin n → Bool => ω i) (prodBern n p)) :=
    (measurable_of_countable g).aestronglyMeasurable
  rw [← MeasureTheory.integral_map hmp.measurable.aemeasurable haesm, hmp.map_eq,
    integral_bernMeasure hp0 hp1]

def countTrue {n : ℕ} (ω : Fin n → Bool) : ℕ :=
  (Finset.univ.filter (fun i : Fin n => ω i = true)).card

lemma prodBern_singleton {n : ℕ} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (ω : Fin n → Bool) :
    prodBern n p {ω} =
      ENNReal.ofReal (p ^ countTrue ω * (1 - p) ^ (n - countTrue ω)) := by
  have : IsProbabilityMeasure (bernMeasure p) := bernMeasure_isProb hp0 hp1
  have hsing : ({ω} : Set (Fin n → Bool)) = Set.univ.pi (fun i : Fin n => {ω i}) := by
    ext ω'
    simp [funext_iff]
  rw [hsing, prodBern, Measure.pi_pi]
  have hsplit := (Finset.prod_filter_mul_prod_filter_not
    (Finset.univ : Finset (Fin n)) (fun i : Fin n => ω i = true)
    (fun i : Fin n => bernMeasure p {ω i})).symm
  rw [hsplit]
  have htrue : (∏ i ∈ Finset.univ.filter (fun i : Fin n => ω i = true), bernMeasure p {ω i}) =
      (ENNReal.ofReal p) ^ countTrue ω := by
    calc (∏ i ∈ Finset.univ.filter (fun i : Fin n => ω i = true), bernMeasure p {ω i})
        = ∏ _i ∈ Finset.univ.filter (fun i : Fin n => ω i = true), ENNReal.ofReal p := by
            refine Finset.prod_congr rfl fun i hi => ?_
            rw [(Finset.mem_filter.mp hi).2, bernMeasure_apply_true]
      _ = (ENNReal.ofReal p) ^ countTrue ω := by simp [countTrue]
  have hfalse_card :
      (Finset.univ.filter (fun i : Fin n => ¬ ω i = true)).card = n - countTrue ω := by
    have hsum := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin n)))
      (p := fun i : Fin n => ω i = true)
    simp only [Finset.card_univ, Fintype.card_fin] at hsum
    change countTrue ω + _ = n at hsum
    omega
  have hfalse : (∏ i ∈ Finset.univ.filter (fun i : Fin n => ¬ ω i = true), bernMeasure p {ω i}) =
      (ENNReal.ofReal (1 - p)) ^ (n - countTrue ω) := by
    calc (∏ i ∈ Finset.univ.filter (fun i : Fin n => ¬ ω i = true), bernMeasure p {ω i})
        = ∏ _i ∈ Finset.univ.filter (fun i : Fin n => ¬ ω i = true), ENNReal.ofReal (1 - p) := by
            refine Finset.prod_congr rfl fun i hi => ?_
            have hf : ω i = false := Bool.eq_false_iff.mpr (Finset.mem_filter.mp hi).2
            rw [hf, bernMeasure_apply_false]
      _ = (ENNReal.ofReal (1 - p)) ^ (n - countTrue ω) := by
            rw [Finset.prod_const, hfalse_card]
  rw [htrue, hfalse, ← ENNReal.ofReal_pow hp0, ← ENNReal.ofReal_pow (by linarith),
    ← ENNReal.ofReal_mul (pow_nonneg hp0 _)]

def exactSlice (n m : ℕ) : Finset (Fin n → Bool) :=
  Finset.univ.filter (fun ω : Fin n → Bool => countTrue ω = m)

lemma card_exactSlice (n m : ℕ) : (exactSlice n m).card = n.choose m := by
  have hbij : (exactSlice n m).card =
      ((Finset.univ : Finset (Fin n)).powersetCard m).card := by
    refine Finset.card_bij
      (fun ω _ => Finset.univ.filter (fun i : Fin n => ω i = true))
      (fun ω hω => ?_)
      (fun ω₁ _ ω₂ _ heq => ?_)
      (fun s hs => ?_)
    · rw [Finset.mem_powersetCard]
      exact ⟨Finset.subset_univ _, (Finset.mem_filter.mp hω).2⟩
    · ext i
      have hmem := Finset.ext_iff.mp heq i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hmem
      cases h1 : ω₁ i <;> cases h2 : ω₂ i <;> simp_all
    · refine ⟨fun i => decide (i ∈ s), ?_, ?_⟩
      · rw [exactSlice, Finset.mem_filter]
        refine ⟨Finset.mem_univ _, ?_⟩
        unfold countTrue
        have hfilt : (Finset.univ.filter (fun i : Fin n => decide (i ∈ s) = true)) = s := by
          ext i; simp
        rw [hfilt]
        exact (Finset.mem_powersetCard.mp hs).2
      · ext i; simp
  rw [hbij, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]

lemma prodBern_real_exactSlice {n m : ℕ} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (prodBern n p).real (exactSlice n m : Set (Fin n → Bool)) =
      (n.choose m : ℝ) * p ^ m * (1 - p) ^ (n - m) := by
  have hunion : (exactSlice n m : Set (Fin n → Bool)) = ⋃ ω ∈ exactSlice n m, ({ω} : Set _) := by
    ext ω; simp
  have hdisj : (exactSlice n m : Set (Fin n → Bool)).PairwiseDisjoint
      (fun ω : Fin n → Bool => ({ω} : Set (Fin n → Bool))) := by
    intro ω₁ _ ω₂ _ hne
    exact Set.disjoint_singleton.mpr hne
  have hmeas : ∀ ω ∈ exactSlice n m, MeasurableSet ({ω} : Set (Fin n → Bool)) :=
    fun ω _ => measurableSet_singleton ω
  have hval : prodBern n p (exactSlice n m : Set (Fin n → Bool)) =
      ENNReal.ofReal ((n.choose m : ℝ) * p ^ m * (1 - p) ^ (n - m)) := by
    rw [hunion, measure_biUnion_finset hdisj hmeas]
    have hcongr : ∑ ω ∈ exactSlice n m, prodBern n p {ω} =
        ∑ _ω ∈ exactSlice n m, ENNReal.ofReal (p ^ m * (1 - p) ^ (n - m)) := by
      refine Finset.sum_congr rfl fun ω hω => ?_
      rw [prodBern_singleton hp0 hp1 ω, (Finset.mem_filter.mp hω).2]
    rw [hcongr, Finset.sum_const, card_exactSlice, nsmul_eq_mul,
      ← ENNReal.ofReal_natCast,
      ← ENNReal.ofReal_mul (Nat.cast_nonneg _), mul_assoc]
  rw [Measure.real_def, hval, ENNReal.toReal_ofReal]
  exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hp0 _))
    (pow_nonneg (by linarith) _)

/-! ### Part 3: Unimodal binomial mode bound `bTerm n (m / n) m ≥ 1 / (n + 1)` -/

def bTerm (n : ℕ) (q : ℝ) (k : ℕ) : ℝ :=
  (n.choose k : ℝ) * q ^ k * (1 - q) ^ (n - k)

lemma choose_step_cast {n k : ℕ} (hk : k < n) :
    (n.choose (k + 1) : ℝ) * (k + 1 : ℝ) = (n.choose k : ℝ) * (n - k : ℝ) := by
  have hnat : n.choose (k + 1) * (k + 1) = n.choose k * (n - k) :=
    Nat.choose_succ_right_eq n k
  have hcast : ((n.choose (k + 1) * (k + 1) : ℕ) : ℝ) = ((n.choose k * (n - k) : ℕ) : ℝ) :=
    congr_arg Nat.cast hnat
  push_cast [Nat.le_of_lt hk] at hcast
  exact hcast

lemma bTerm_le_succ_of_lt_mode {n m k : ℕ} (hm0 : 0 < m) (hmn : m < n) (hk : k < m) :
    bTerm n ((m : ℝ) / (n : ℝ)) k ≤ bTerm n ((m : ℝ) / (n : ℝ)) (k + 1) := by
  set q : ℝ := (m : ℝ) / (n : ℝ)
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (lt_trans hm0 hmn)
  have hq0 : 0 ≤ q := div_nonneg (Nat.cast_nonneg m) hn_pos.le
  have h1q_pos : 0 < 1 - q := by
    dsimp [q]; rw [sub_pos, div_lt_one hn_pos]; exact_mod_cast hmn
  have hk_lt_n : k < n := lt_trans hk hmn
  have hsub : n - k = (n - (k + 1)) + 1 := by omega
  have hstep := choose_step_cast hk_lt_n
  have hineq : (k + 1 : ℝ) * (1 - q) ≤ (n - k : ℝ) * q := by
    dsimp [q]
    have h1 : 1 - (m : ℝ) / (n : ℝ) = ((n : ℝ) - (m : ℝ)) / (n : ℝ) := by
      field_simp [hn_pos.ne']
    rw [h1, ← mul_div_assoc, ← mul_div_assoc, div_le_div_iff_of_pos_right hn_pos]
    have hkm : (k + 1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hk
    nlinarith
  unfold bTerm
  rw [hsub, pow_succ (1 - q), pow_succ q]
  have hpos_common : 0 ≤ q ^ k * (1 - q) ^ (n - (k + 1)) :=
    mul_nonneg (pow_nonneg hq0 _) (pow_nonneg h1q_pos.le _)
  have hk1_pos : (0 : ℝ) < (k + 1 : ℝ) := by positivity
  suffices hmul : (k + 1 : ℝ) * ((n.choose k : ℝ) * q ^ k * ((1 - q) ^ (n - (k + 1)) * (1 - q))) ≤
      (k + 1 : ℝ) * ((n.choose (k + 1) : ℝ) * (q ^ k * q) * (1 - q) ^ (n - (k + 1))) by
    exact le_of_mul_le_mul_left hmul hk1_pos
  have hl : (k + 1 : ℝ) * ((n.choose k : ℝ) * q ^ k * ((1 - q) ^ (n - (k + 1)) * (1 - q))) =
      ((n.choose k : ℝ) * (q ^ k * (1 - q) ^ (n - (k + 1)))) * ((k + 1 : ℝ) * (1 - q)) := by ring
  have hr : (k + 1 : ℝ) * ((n.choose (k + 1) : ℝ) * (q ^ k * q) * (1 - q) ^ (n - (k + 1))) =
      ((n.choose (k + 1) : ℝ) * (k + 1 : ℝ)) * (q ^ k * (1 - q) ^ (n - (k + 1))) * q := by ring
  rw [hl, hr, hstep]
  have hr' : (n.choose k : ℝ) * (n - k : ℝ) * (q ^ k * (1 - q) ^ (n - (k + 1))) * q =
      ((n.choose k : ℝ) * (q ^ k * (1 - q) ^ (n - (k + 1)))) * ((n - k : ℝ) * q) := by ring
  rw [hr']
  exact mul_le_mul_of_nonneg_left hineq (mul_nonneg (Nat.cast_nonneg _) hpos_common)

lemma bTerm_succ_le_of_mode_le {n m k : ℕ} (hm0 : 0 < m) (hmn : m < n)
    (hmk : m ≤ k) (hkn : k < n) :
    bTerm n ((m : ℝ) / (n : ℝ)) (k + 1) ≤ bTerm n ((m : ℝ) / (n : ℝ)) k := by
  set q : ℝ := (m : ℝ) / (n : ℝ)
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (lt_trans hm0 hmn)
  have hq0 : 0 ≤ q := div_nonneg (Nat.cast_nonneg m) hn_pos.le
  have h1q_pos : 0 < 1 - q := by
    dsimp [q]; rw [sub_pos, div_lt_one hn_pos]; exact_mod_cast hmn
  have hsub : n - k = (n - (k + 1)) + 1 := by omega
  have hstep := choose_step_cast hkn
  have hineq : (n - k : ℝ) * q ≤ (k + 1 : ℝ) * (1 - q) := by
    dsimp [q]
    have h1 : 1 - (m : ℝ) / (n : ℝ) = ((n : ℝ) - (m : ℝ)) / (n : ℝ) := by
      field_simp [hn_pos.ne']
    rw [h1, ← mul_div_assoc, ← mul_div_assoc, div_le_div_iff_of_pos_right hn_pos]
    have hkm : (m : ℝ) ≤ (k : ℝ) := by exact_mod_cast hmk
    have hmn' : (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast hmn.le
    nlinarith
  unfold bTerm
  rw [hsub, pow_succ (1 - q), pow_succ q]
  have hpos_common : 0 ≤ q ^ k * (1 - q) ^ (n - (k + 1)) :=
    mul_nonneg (pow_nonneg hq0 _) (pow_nonneg h1q_pos.le _)
  have hk1_pos : (0 : ℝ) < (k + 1 : ℝ) := by positivity
  suffices hmul : (k + 1 : ℝ) * ((n.choose (k + 1) : ℝ) * (q ^ k * q) * (1 - q) ^ (n - (k + 1))) ≤
      (k + 1 : ℝ) * ((n.choose k : ℝ) * q ^ k * ((1 - q) ^ (n - (k + 1)) * (1 - q))) by
    exact le_of_mul_le_mul_left hmul hk1_pos
  have hr : (k + 1 : ℝ) * ((n.choose k : ℝ) * q ^ k * ((1 - q) ^ (n - (k + 1)) * (1 - q))) =
      ((n.choose k : ℝ) * (q ^ k * (1 - q) ^ (n - (k + 1)))) * ((k + 1 : ℝ) * (1 - q)) := by ring
  have hl : (k + 1 : ℝ) * ((n.choose (k + 1) : ℝ) * (q ^ k * q) * (1 - q) ^ (n - (k + 1))) =
      ((n.choose (k + 1) : ℝ) * (k + 1 : ℝ)) * (q ^ k * (1 - q) ^ (n - (k + 1))) * q := by ring
  rw [hl, hr, hstep]
  have hl' : (n.choose k : ℝ) * (n - k : ℝ) * (q ^ k * (1 - q) ^ (n - (k + 1))) * q =
      ((n.choose k : ℝ) * (q ^ k * (1 - q) ^ (n - (k + 1)))) * ((n - k : ℝ) * q) := by ring
  rw [hl']
  exact mul_le_mul_of_nonneg_left hineq (mul_nonneg (Nat.cast_nonneg _) hpos_common)

lemma bTerm_le_mode_of_le {n m : ℕ} (hm0 : 0 < m) (hmn : m < n) :
    ∀ d k : ℕ, k + d = m → bTerm n ((m : ℝ) / (n : ℝ)) k ≤ bTerm n ((m : ℝ) / (n : ℝ)) m
  | 0, k, hkd => by
      have hk : k = m := by omega
      subst hk; exact le_rfl
  | d + 1, k, hkd => by
      have hklt : k < m := by omega
      exact (bTerm_le_succ_of_lt_mode hm0 hmn hklt).trans
        (bTerm_le_mode_of_le hm0 hmn d (k + 1) (by omega))

lemma bTerm_le_mode_of_ge {n m : ℕ} (hm0 : 0 < m) (hmn : m < n) :
    ∀ d : ℕ, m + d ≤ n → bTerm n ((m : ℝ) / (n : ℝ)) (m + d) ≤ bTerm n ((m : ℝ) / (n : ℝ)) m
  | 0, _ => by simp
  | d + 1, hmd => by
      have hlt : m + d < n := by omega
      exact (bTerm_succ_le_of_mode_le hm0 hmn (Nat.le_add_right m d) hlt).trans
        (bTerm_le_mode_of_ge hm0 hmn d (by omega))

lemma bTerm_le_mode {n m k : ℕ} (hm0 : 0 < m) (hmn : m < n) (hkn : k ≤ n) :
    bTerm n ((m : ℝ) / (n : ℝ)) k ≤ bTerm n ((m : ℝ) / (n : ℝ)) m := by
  rcases le_or_gt k m with hkm | hmk
  · exact bTerm_le_mode_of_le hm0 hmn (m - k) k (by omega)
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hmk.le
    exact bTerm_le_mode_of_ge hm0 hmn d hkn

lemma one_div_le_bTerm_mode {n m : ℕ} (hm0 : 0 < m) (hmn : m < n) :
    1 / ((n : ℝ) + 1) ≤ bTerm n ((m : ℝ) / (n : ℝ)) m := by
  set q : ℝ := (m : ℝ) / (n : ℝ)
  have hsum : ∑ k ∈ Finset.range (n + 1), bTerm n q k = 1 := by
    have hbinom := (add_pow q (1 - q) n).symm
    have h1 : (q + (1 - q)) ^ n = 1 := by ring
    rw [h1] at hbinom
    refine (Finset.sum_congr rfl fun k _ => ?_).trans hbinom
    unfold bTerm; ring
  have hle : (1 : ℝ) ≤ ((n : ℝ) + 1) * bTerm n q m := by
    calc (1 : ℝ) = ∑ k ∈ Finset.range (n + 1), bTerm n q k := hsum.symm
      _ ≤ ∑ _k ∈ Finset.range (n + 1), bTerm n q m := by
            refine Finset.sum_le_sum fun k hk => ?_
            exact bTerm_le_mode hm0 hmn (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))
      _ = ((n : ℝ) + 1) * bTerm n q m := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
            push_cast; ring
  rw [div_le_iff₀ (by positivity)]
  linarith

lemma prodBern_real_exactSlice_ge {n m : ℕ} (hm0 : 0 < m) (hmn : m < n)
    {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    1 / ((n : ℝ) + 1) * (p / ((m : ℝ) / (n : ℝ))) ^ m *
        ((1 - p) / (1 - (m : ℝ) / (n : ℝ))) ^ (n - m) ≤
      (prodBern n p).real (exactSlice n m : Set (Fin n → Bool)) := by
  set q : ℝ := (m : ℝ) / (n : ℝ)
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (lt_trans hm0 hmn)
  have hq_pos : 0 < q := div_pos (by exact_mod_cast hm0) hn_pos
  have h1q_pos : 0 < 1 - q := by
    dsimp [q]; rw [sub_pos, div_lt_one hn_pos]; exact_mod_cast hmn
  rw [prodBern_real_exactSlice hp0 hp1]
  have hident : (n.choose m : ℝ) * p ^ m * (1 - p) ^ (n - m) =
      bTerm n q m * (p / q) ^ m * ((1 - p) / (1 - q)) ^ (n - m) := by
    unfold bTerm
    rw [div_pow p q m, div_pow (1 - p) (1 - q) (n - m)]
    have hqm_ne : q ^ m ≠ 0 := pow_ne_zero m hq_pos.ne'
    have h1qm_ne : (1 - q) ^ (n - m) ≠ 0 := pow_ne_zero (n - m) h1q_pos.ne'
    calc (n.choose m : ℝ) * p ^ m * (1 - p) ^ (n - m)
        = (n.choose m : ℝ) * (q ^ m * (p ^ m / q ^ m)) *
            ((1 - q) ^ (n - m) * ((1 - p) ^ (n - m) / (1 - q) ^ (n - m))) := by
            rw [mul_div_cancel₀ _ hqm_ne, mul_div_cancel₀ _ h1qm_ne]
      _ = (n.choose m : ℝ) * q ^ m * (1 - q) ^ (n - m) * (p ^ m / q ^ m) *
            ((1 - p) ^ (n - m) / (1 - q) ^ (n - m)) := by ring
  rw [hident]
  have hmode := one_div_le_bTerm_mode hm0 hmn
  have hfac : 0 ≤ (p / q) ^ m * ((1 - p) / (1 - q)) ^ (n - m) :=
    mul_nonneg (pow_nonneg (div_nonneg hp0 hq_pos.le) _)
      (pow_nonneg (div_nonneg (by linarith) h1q_pos.le) _)
  calc 1 / ((n : ℝ) + 1) * (p / q) ^ m * ((1 - p) / (1 - q)) ^ (n - m)
      = (1 / ((n : ℝ) + 1)) * ((p / q) ^ m * ((1 - p) / (1 - q)) ^ (n - m)) := by ring
    _ ≤ bTerm n q m * ((p / q) ^ m * ((1 - p) / (1 - q)) ^ (n - m)) :=
          mul_le_mul_of_nonneg_right hmode hfac
    _ = bTerm n q m * (p / q) ^ m * ((1 - p) / (1 - q)) ^ (n - m) := by ring

/-! ### Part 4: Negatively skewed Bernoulli matrix ensemble and violation at `n = 2,000,000` -/

def p₀ : ℝ := 1 / 40
def Mval : ℝ := 173 / 50
def aval : ℝ := 173 / 1950
def s2val : ℝ := 29929 / 97500
def deltaVal : ℝ := 173 / 3250

def valOfBool (b : Bool) : ℝ := if b then -Mval else aval

def Qmat {n : ℕ} (i : Fin n) (ω : Fin n → Bool) : Matrix (Fin 1) (Fin 1) ℝ :=
  scalMat (valOfBool (ω i))

lemma p₀_bounds : 0 ≤ p₀ ∧ p₀ ≤ 1 := by
  unfold p₀; constructor <;> norm_num

lemma Qmat_indep (n : ℕ) : iIndepFun (Qmat (n := n)) (prodBern n p₀) := by
  have : IsProbabilityMeasure (bernMeasure p₀) := bernMeasure_isProb p₀_bounds.1 p₀_bounds.2
  have hm : ∀ _i : Fin n, AEMeasurable (fun b : Bool => scalMat (valOfBool b)) (bernMeasure p₀) :=
    fun _ => (measurable_of_countable _).aemeasurable
  exact iIndepFun_pi hm

lemma Qmat_pow_integrable {n : ℕ} (i : Fin n) (j : ℕ) (r s : Fin 1) :
    Integrable (fun ω : Fin n → Bool => (Qmat i ω ^ j) r s) (prodBern n p₀) := by
  have : IsProbabilityMeasure (prodBern n p₀) := prodBern_isProb n p₀_bounds.1 p₀_bounds.2
  exact Integrable.of_finite

lemma Qmat_pow_expectation {n : ℕ} (i : Fin n) (j : ℕ) :
    matrixExpectation (fun ω : Fin n → Bool => Qmat i ω ^ j) (prodBern n p₀) =
      scalMat (p₀ * (-Mval) ^ j + (1 - p₀) * aval ^ j) := by
  ext r s
  simp only [matrixExpectation, Matrix.of_apply, Qmat, scalMat_pow, scalMat_apply]
  have heq := integral_coord_prodBern (n := n) p₀_bounds.1 p₀_bounds.2 i
    (fun b : Bool => (valOfBool b) ^ j)
  simpa [valOfBool] using heq

lemma Qmat_expectation_zero {n : ℕ} (i : Fin n) :
    matrixExpectation (Qmat (n := n) i) (prodBern n p₀) = 0 := by
  have h1 := Qmat_pow_expectation (n := n) i 1
  simp only [pow_one] at h1
  have h0 : p₀ * -Mval + (1 - p₀) * aval = 0 := by
    unfold p₀ Mval aval; norm_num
  rw [h1, h0]
  ext r s; simp

lemma Qmat_variance {n : ℕ} (i : Fin n) :
    matrixVariance (Qmat (n := n) i) (prodBern n p₀) = scalMat s2val := by
  unfold matrixVariance
  rw [Qmat_pow_expectation i 2, Qmat_expectation_zero i]
  have hs : p₀ * (-Mval) ^ 2 + (1 - p₀) * aval ^ 2 = s2val := by
    unfold p₀ Mval aval s2val; norm_num
  rw [hs]
  ext r s; simp

lemma moment_abs_bound_ge_four :
    ∀ k : ℕ, p₀ * Mval ^ (k + 4) + (1 - p₀) * aval ^ (k + 4) ≤
      1 / 2 * ((k + 4).factorial : ℝ) * s2val
  | 0 => by unfold p₀ Mval aval s2val; norm_num [Nat.factorial]
  | k + 1 => by
      have ih := moment_abs_bound_ge_four k
      have haM : aval ≤ Mval := by unfold aval Mval; norm_num
      have ha0 : 0 ≤ aval := by unfold aval; norm_num
      have hM0 : 0 ≤ Mval := by unfold Mval; norm_num
      have hstep_lhs :
          p₀ * Mval ^ (k + 5) + (1 - p₀) * aval ^ (k + 5) ≤
            Mval * (p₀ * Mval ^ (k + 4) + (1 - p₀) * aval ^ (k + 4)) := by
        have h1 : Mval ^ (k + 5) = Mval * Mval ^ (k + 4) := by ring
        have h2 : aval ^ (k + 5) = aval * aval ^ (k + 4) := by ring
        rw [h1, h2]
        have hle : aval * aval ^ (k + 4) ≤ Mval * aval ^ (k + 4) :=
          mul_le_mul_of_nonneg_right haM (pow_nonneg ha0 _)
        have hp1 : 0 ≤ 1 - p₀ := by unfold p₀; norm_num
        nlinarith
      have hMk : Mval ≤ (k + 5 : ℝ) := by
        unfold Mval
        have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
        linarith
      have hrhs_pos : 0 ≤ 1 / 2 * ((k + 4).factorial : ℝ) * s2val := by
        unfold s2val; positivity
      have hfac : ((k + 5).factorial : ℝ) = (k + 5 : ℝ) * ((k + 4).factorial : ℝ) := by
        have hf : (k + 5).factorial = (k + 4 + 1) * (k + 4).factorial := Nat.factorial_succ (k + 4)
        rw [hf]; push_cast; ring
      calc p₀ * Mval ^ (k + 5) + (1 - p₀) * aval ^ (k + 5)
          ≤ Mval * (p₀ * Mval ^ (k + 4) + (1 - p₀) * aval ^ (k + 4)) := hstep_lhs
        _ ≤ Mval * (1 / 2 * ((k + 4).factorial : ℝ) * s2val) :=
              mul_le_mul_of_nonneg_left ih hM0
        _ ≤ (k + 5 : ℝ) * (1 / 2 * ((k + 4).factorial : ℝ) * s2val) :=
              mul_le_mul_of_nonneg_right hMk hrhs_pos
        _ = 1 / 2 * ((k + 5).factorial : ℝ) * s2val := by rw [hfac]; ring

lemma Qmat_bernstein {n : ℕ} (i : Fin n) :
    BernsteinConditionMatrix (Qmat (n := n) i) (prodBern n p₀) 1 := by
  refine ⟨Filter.Eventually.of_forall fun _ => scalMat_isSymm _,
    fun j r s => Qmat_pow_integrable i j r s,
    Qmat_expectation_zero i, ?_⟩
  intro j hj
  rw [Qmat_pow_expectation i j, Qmat_variance i, one_pow, mul_one, scalMat_smul]
  refine scalMat_loewner ?_
  rcases eq_or_lt_of_le hj with rfl | hj4
  · unfold p₀ Mval aval s2val; norm_num [Nat.factorial]
  · obtain ⟨k, rfl⟩ : ∃ k : ℕ, j = k + 4 := ⟨j - 4, by omega⟩
    have hneg : (-Mval) ^ (k + 4) ≤ Mval ^ (k + 4) := by
      calc (-Mval) ^ (k + 4) ≤ |(-Mval) ^ (k + 4)| := le_abs_self _
        _ = |-Mval| ^ (k + 4) := abs_pow _ _
        _ = Mval ^ (k + 4) := by
            have hM : |-Mval| = Mval := by unfold Mval; norm_num
            rw [hM]
    have hp0_pos : 0 ≤ p₀ := p₀_bounds.1
    have hle : p₀ * (-Mval) ^ (k + 4) + (1 - p₀) * aval ^ (k + 4) ≤
        p₀ * Mval ^ (k + 4) + (1 - p₀) * aval ^ (k + 4) := by nlinarith
    exact hle.trans (moment_abs_bound_ge_four k)

lemma slice_subset_tail_event {N : ℕ} (hN : 0 < N) :
    (exactSlice (25 * N) N : Set (Fin (25 * N) → Bool)) ⊆
      {ω | deltaVal ≤ opNorm (∑ i : Fin (25 * N), Qmat i ω) / ((25 * N : ℕ) : ℝ)} := by
  intro ω hω
  have hcard : countTrue ω = N := (Finset.mem_filter.mp hω).2
  have hsum_val : ∑ i : Fin (25 * N), valOfBool (ω i) =
      (N : ℝ) * (-Mval) + (24 * (N : ℝ)) * aval := by
    have hsplit := (Finset.sum_filter_add_sum_filter_not
      (Finset.univ : Finset (Fin (25 * N))) (fun i => ω i = true)
      (fun i => valOfBool (ω i))).symm
    rw [hsplit]
    have htrue : ∑ i ∈ Finset.univ.filter (fun i => ω i = true), valOfBool (ω i) =
        (N : ℝ) * (-Mval) := by
      have hc : ∑ i ∈ Finset.univ.filter (fun i => ω i = true), valOfBool (ω i) =
          ∑ _i ∈ Finset.univ.filter (fun i => ω i = true), (-Mval) := by
        refine Finset.sum_congr rfl fun i hi => ?_
        rw [(Finset.mem_filter.mp hi).2]; rfl
      rw [hc, Finset.sum_const, nsmul_eq_mul]
      change (countTrue ω : ℝ) * (-Mval) = _
      rw [hcard]
    have hfalse_card :
        (Finset.univ.filter (fun i : Fin (25 * N) => ¬ ω i = true)).card = 24 * N := by
      have hsum := Finset.card_filter_add_card_filter_not
        (s := (Finset.univ : Finset (Fin (25 * N)))) (p := fun i => ω i = true)
      simp only [Finset.card_univ, Fintype.card_fin] at hsum
      change countTrue ω + _ = 25 * N at hsum
      omega
    have hfalse : ∑ i ∈ Finset.univ.filter (fun i => ¬ ω i = true), valOfBool (ω i) =
        (24 * (N : ℝ)) * aval := by
      have hc : ∑ i ∈ Finset.univ.filter (fun i => ¬ ω i = true), valOfBool (ω i) =
          ∑ _i ∈ Finset.univ.filter (fun i => ¬ ω i = true), aval := by
        refine Finset.sum_congr rfl fun i hi => ?_
        have hf : ω i = false := Bool.eq_false_iff.mpr (Finset.mem_filter.mp hi).2
        rw [hf]; rfl
      rw [hc, Finset.sum_const, hfalse_card, nsmul_eq_mul]
      push_cast; ring
    rw [htrue, hfalse]
  have hsum_mat : (∑ i : Fin (25 * N), Qmat i ω) =
      scalMat (-(((25 * N : ℕ) : ℝ) * deltaVal)) := by
    unfold Qmat
    rw [scalMat_sum, hsum_val]
    congr 1
    unfold Mval aval deltaVal
    push_cast
    ring
  simp only [Set.mem_ofPred, hsum_mat, opNorm_scalMat, abs_neg]
  have hn_pos : (0 : ℝ) < ((25 * N : ℕ) : ℝ) := by positivity
  have hd_pos : 0 < deltaVal := by unfold deltaVal; norm_num
  rw [abs_of_pos (mul_pos hn_pos hd_pos), mul_div_cancel_left₀ _ hn_pos.ne']

lemma exp_neg_le_inv_quartic {x : ℝ} (hx : 0 ≤ x) :
    Real.exp (-x) ≤ (1 + x + x ^ 2 / 2 + x ^ 3 / 6 + x ^ 4 / 24)⁻¹ := by
  have hsum := Real.sum_le_exp_of_nonneg hx 5
  have hpoly : ∑ i ∈ Finset.range 5, x ^ i / (i.factorial : ℝ) =
      1 + x + x ^ 2 / 2 + x ^ 3 / 6 + x ^ 4 / 24 := by
    simp [Finset.sum_range_succ, Nat.factorial]
  rw [hpoly] at hsum
  have hpos : 0 < 1 + x + x ^ 2 / 2 + x ^ 3 / 6 + x ^ 4 / 24 := by positivity
  rw [Real.exp_neg]
  exact inv_anti₀ hpos hsum

def x₀ : ℝ := 25 * deltaVal ^ 2 / (2 * (s2val + deltaVal))
def baseRatio : ℝ := (5 / 8 : ℝ) * (65 / 64 : ℝ) ^ 24

lemma numerical_core_gap :
    2 * (((25 * 80000 : ℕ) : ℝ) + 1) * Real.exp (-x₀) ^ 80000 <
      baseRatio ^ 80000 := by
  have hx0_nonneg : 0 ≤ x₀ := by unfold x₀ deltaVal s2val; positivity
  let P4 : ℝ := 1 + x₀ + x₀ ^ 2 / 2 + x₀ ^ 3 / 6 + x₀ ^ 4 / 24
  have hP4_pos : 0 < P4 := by dsimp [P4]; positivity
  have hexp_le : Real.exp (-x₀) ≤ P4⁻¹ := exp_neg_le_inv_quartic hx0_nonneg
  have hrat_gap : (1 + (1 / 2500 : ℝ)) ≤ baseRatio * P4 := by
    dsimp [P4]
    unfold baseRatio x₀ deltaVal s2val
    norm_num
  have h1 : (1 + (1 / 2500 : ℝ)) * P4⁻¹ ≤ baseRatio := by
    rw [← div_eq_mul_inv, div_le_iff₀ hP4_pos]
    exact hrat_gap
  have h2 : (1 + (1 / 2500 : ℝ)) * Real.exp (-x₀) ≤ (1 + (1 / 2500 : ℝ)) * P4⁻¹ :=
    mul_le_mul_of_nonneg_left hexp_le (by norm_num)
  have hstep : (1 + (1 / 2500 : ℝ)) * Real.exp (-x₀) ≤ baseRatio := h2.trans h1
  have hpow80000 : ((1 + (1 / 2500 : ℝ)) ^ 80000) * (Real.exp (-x₀) ^ 80000) ≤
      baseRatio ^ 80000 := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (mul_nonneg (by norm_num) (Real.exp_nonneg _)) hstep 80000
  have hbern2500 : (2 : ℝ) ≤ (1 + (1 / 2500 : ℝ)) ^ 2500 := by
    have hb := one_add_mul_le_pow (by norm_num : (-2 : ℝ) ≤ 1 / 2500) 2500
    have htwo : (1 : ℝ) + (2500 : ℕ) * (1 / 2500 : ℝ) = 2 := by norm_num
    rwa [htwo] at hb
  have hpow32 : (2 : ℝ) ^ 32 ≤ (1 + (1 / 2500 : ℝ)) ^ 80000 := by
    have h80 : (80000 : ℕ) = 2500 * 32 := by norm_num
    rw [h80, pow_mul]
    exact pow_le_pow_left₀ (by norm_num) hbern2500 32
  have hnum_lt : 2 * (((25 * 80000 : ℕ) : ℝ) + 1) < (2 : ℝ) ^ 32 := by norm_num
  have hexp_pos : 0 < Real.exp (-x₀) ^ 80000 := pow_pos (Real.exp_pos _) 80000
  calc 2 * (((25 * 80000 : ℕ) : ℝ) + 1) * Real.exp (-x₀) ^ 80000
      < (2 : ℝ) ^ 32 * Real.exp (-x₀) ^ 80000 :=
        mul_lt_mul_of_pos_right hnum_lt hexp_pos
    _ ≤ ((1 + (1 / 2500 : ℝ)) ^ 80000) * Real.exp (-x₀) ^ 80000 :=
        mul_le_mul_of_nonneg_right hpow32 hexp_pos.le
    _ ≤ baseRatio ^ 80000 := hpow80000

end

end MatrixBernsteinCounterexample

open MatrixBernsteinCounterexample

theorem solution :
    ¬ (∀ {n d : ℕ} {Ω : Type} [MeasurableSpace Ω] {Prob : Measure Ω}
      [IsProbabilityMeasure Prob] (Q : Fin n → Ω → Matrix (Fin d) (Fin d) ℝ)
      (b : ℝ) (_hb : 0 < b) (_hIndep : iIndepFun Q Prob)
      (_hBernstein : ∀ i, BernsteinConditionMatrix (Q i) Prob b)
      (δ : ℝ) (_hδ : 0 < δ),
      Prob.real {ω | δ ≤ opNorm (∑ i, Q i ω) / (n : ℝ)} ≤
        2 * (Matrix.rank (∑ i, matrixVariance (Q i) Prob) : ℝ) *
          Real.exp (-((n : ℝ) * δ ^ 2) /
            (2 * ((1 / (n : ℝ)) * opNorm (∑ i, matrixVariance (Q i) Prob) + b * δ)))) := by
  intro hall
  let n₀ : ℕ := 25 * 80000
  let m₀ : ℕ := 80000
  have : IsProbabilityMeasure (prodBern n₀ p₀) :=
    prodBern_isProb n₀ p₀_bounds.1 p₀_bounds.2
  have hδ : 0 < deltaVal := by unfold deltaVal; norm_num
  have hbound := hall (n := n₀) (d := 1) (Ω := Fin n₀ → Bool) (Prob := prodBern n₀ p₀)
    (Qmat (n := n₀)) 1 zero_lt_one (Qmat_indep n₀) (fun i => Qmat_bernstein i) deltaVal hδ
  have hvar_sum :
      (∑ i : Fin n₀, matrixVariance (Qmat i) (prodBern n₀ p₀)) =
        scalMat ((n₀ : ℝ) * s2val) := by
    calc (∑ i : Fin n₀, matrixVariance (Qmat i) (prodBern n₀ p₀))
        = ∑ _i : Fin n₀, scalMat s2val := Finset.sum_congr rfl fun i _ => Qmat_variance i
      _ = scalMat (∑ _i : Fin n₀, s2val) := scalMat_sum _ _
      _ = scalMat ((n₀ : ℝ) * s2val) := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hop_var :
      (1 / (n₀ : ℝ)) * opNorm (∑ i : Fin n₀, matrixVariance (Qmat i) (prodBern n₀ p₀)) =
        s2val := by
    rw [hvar_sum, opNorm_scalMat]
    have hnonneg : 0 ≤ (n₀ : ℝ) * s2val := by unfold s2val; positivity
    have hn_ne : (n₀ : ℝ) ≠ 0 := by dsimp [n₀]; norm_num
    rw [abs_of_nonneg hnonneg]
    field_simp [hn_ne]
  have hexp_eq :
      Real.exp (-((n₀ : ℝ) * deltaVal ^ 2) /
        (2 * ((1 / (n₀ : ℝ)) *
          opNorm (∑ i : Fin n₀, matrixVariance (Qmat i) (prodBern n₀ p₀)) + 1 * deltaVal))) =
        Real.exp (-x₀) ^ 80000 := by
    rw [hop_var]
    have harg : -((n₀ : ℝ) * deltaVal ^ 2) / (2 * (s2val + 1 * deltaVal)) =
        (80000 : ℕ) * (-x₀) := by
      dsimp [n₀]; unfold x₀; push_cast; ring
    rw [harg, Real.exp_nat_mul]
  have hrk : (Matrix.rank (∑ i : Fin n₀, matrixVariance (Qmat i) (prodBern n₀ p₀)) : ℝ) ≤ 1 := by
    exact_mod_cast rank_fin_one_le_one _
  have hrhs_le :
      2 * (Matrix.rank (∑ i : Fin n₀, matrixVariance (Qmat i) (prodBern n₀ p₀)) : ℝ) *
        Real.exp (-((n₀ : ℝ) * deltaVal ^ 2) /
          (2 * ((1 / (n₀ : ℝ)) *
            opNorm (∑ i : Fin n₀, matrixVariance (Qmat i) (prodBern n₀ p₀)) + 1 * deltaVal))) ≤
        2 * Real.exp (-x₀) ^ 80000 := by
    rw [hexp_eq]
    have hexp_nonneg : 0 ≤ Real.exp (-x₀) ^ 80000 := pow_nonneg (Real.exp_nonneg _) _
    nlinarith
  have hprob_le :
      (prodBern n₀ p₀).real (exactSlice n₀ m₀ : Set (Fin n₀ → Bool)) ≤
        2 * Real.exp (-x₀) ^ 80000 := by
    have hsub : (exactSlice n₀ m₀ : Set (Fin n₀ → Bool)) ⊆
        {ω | deltaVal ≤ opNorm (∑ i : Fin n₀, Qmat i ω) / (n₀ : ℝ)} :=
      slice_subset_tail_event (N := 80000) (by norm_num)
    exact (measureReal_mono hsub (measure_ne_top _ _)).trans (hbound.trans hrhs_le)
  have hslice_ge := prodBern_real_exactSlice_ge (n := n₀) (m := m₀)
    (by dsimp [m₀]; norm_num) (by dsimp [m₀, n₀]; norm_num) p₀_bounds.1 p₀_bounds.2
  have hlr :
      (p₀ / ((m₀ : ℝ) / (n₀ : ℝ))) ^ m₀ *
        ((1 - p₀) / (1 - (m₀ : ℝ) / (n₀ : ℝ))) ^ (n₀ - m₀) =
        baseRatio ^ 80000 := by
    have hr1 : p₀ / ((m₀ : ℝ) / (n₀ : ℝ)) = 5 / 8 := by
      dsimp [m₀, n₀]; unfold p₀; norm_num
    have hr2 : (1 - p₀) / (1 - (m₀ : ℝ) / (n₀ : ℝ)) = 65 / 64 := by
      dsimp [m₀, n₀]; unfold p₀; norm_num
    have hsub_nat : n₀ - m₀ = 24 * 80000 := by norm_num [m₀, n₀]
    have hm_eq : m₀ = 80000 := rfl
    unfold baseRatio
    rw [hr1, hr2, hsub_nat, hm_eq, pow_mul (65 / 64 : ℝ) 24 80000, ← mul_pow]
  have hlow :
      1 / ((n₀ : ℝ) + 1) * baseRatio ^ 80000 ≤ 2 * Real.exp (-x₀) ^ 80000 := by
    calc 1 / ((n₀ : ℝ) + 1) * baseRatio ^ 80000
        = 1 / ((n₀ : ℝ) + 1) * ((p₀ / ((m₀ : ℝ) / (n₀ : ℝ))) ^ m₀ *
            ((1 - p₀) / (1 - (m₀ : ℝ) / (n₀ : ℝ))) ^ (n₀ - m₀)) := by
            rw [hlr]
      _ = 1 / ((n₀ : ℝ) + 1) * (p₀ / ((m₀ : ℝ) / (n₀ : ℝ))) ^ m₀ *
            ((1 - p₀) / (1 - (m₀ : ℝ) / (n₀ : ℝ))) ^ (n₀ - m₀) := by
            rw [mul_assoc]
      _ ≤ (prodBern n₀ p₀).real (exactSlice n₀ m₀ : Set (Fin n₀ → Bool)) := hslice_ge
      _ ≤ 2 * Real.exp (-x₀) ^ 80000 := hprob_le
  have hn1_pos : 0 < (n₀ : ℝ) + 1 := by dsimp [n₀]; positivity
  have hcontra : baseRatio ^ 80000 ≤ 2 * ((n₀ : ℝ) + 1) * Real.exp (-x₀) ^ 80000 := by
    have hm := mul_le_mul_of_nonneg_left hlow hn1_pos.le
    rwa [← mul_assoc, mul_one_div_cancel hn1_pos.ne', one_mul,
      ← mul_assoc ((n₀ : ℝ) + 1) 2, mul_comm ((n₀ : ℝ) + 1) 2] at hm
  exact not_lt_of_ge hcontra numerical_core_gap
