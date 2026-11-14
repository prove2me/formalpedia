-- Prove2me | solution 1 for HighDimProb.Deviations.m_star_bound_v2
-- status  : ACCEPTED   (disprove)
-- author  : @kmehltretter82
-- created : 2026-11-14T03:47:24.105812+00:00
-- url     : https://prove2.me/submissions/ec04d8ec-c7b7-41cd-a855-bc0f16a1317d

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Probability.Independence.Basic
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Definitions.Def_HighDimProb_Deviations_IsIsotropic
import Definitions.Def_HighDimProb_Deviations_SubgaussianVectorNorm_v2
import Definitions.Def_HighDimProb_Deviations_GaussianWidth

open MeasureTheory ProbabilityTheory HighDimProb.Deviations
open scoped ENNReal NNReal RealInnerProductSpace

namespace MStarCounterexample

/-! ### Part 1: A Vitali subset of `(0, π)` that is not Lebesgue null-measurable -/

def ratSetoid : Setoid ℝ where
  r x y := ∃ q : ℚ, x - y = (q : ℝ)
  iseqv := {
    refl := fun x => ⟨0, by simp⟩
    symm := fun ⟨q, hq⟩ => ⟨-q, by push_cast; linarith⟩
    trans := fun ⟨q₁, h₁⟩ ⟨q₂, h₂⟩ => ⟨q₁ + q₂, by push_cast; linarith⟩
  }

lemma exists_rep_in_Ioo_pi (c : Quotient ratSetoid) :
    ∃ y ∈ Set.Ioo (0 : ℝ) Real.pi, Quotient.mk ratSetoid y = c := by
  rcases Quotient.exists_rep c with ⟨x, rfl⟩
  obtain ⟨q, hq₁, hq₂⟩ := exists_rat_btwn (sub_lt_self x Real.pi_pos)
  refine ⟨x - (q : ℝ), ⟨by linarith, by linarith⟩, ?_⟩
  exact Quotient.sound ⟨-q, by push_cast; ring⟩

noncomputable def vitaliRep (c : Quotient ratSetoid) : ℝ :=
  Classical.choose (exists_rep_in_Ioo_pi c)

lemma vitaliRep_mem (c : Quotient ratSetoid) :
    vitaliRep c ∈ Set.Ioo (0 : ℝ) Real.pi :=
  (Classical.choose_spec (exists_rep_in_Ioo_pi c)).1

lemma vitaliRep_mk (c : Quotient ratSetoid) :
    Quotient.mk ratSetoid (vitaliRep c) = c :=
  (Classical.choose_spec (exists_rep_in_Ioo_pi c)).2

def vitaliSet : Set ℝ := Set.range vitaliRep

lemma vitaliSet_subset_Ioo : vitaliSet ⊆ Set.Ioo (0 : ℝ) Real.pi := by
  rintro _ ⟨c, rfl⟩
  exact vitaliRep_mem c

def ratShifts : Set ℚ := {q : ℚ | -Real.pi < (q : ℝ) ∧ (q : ℝ) < Real.pi}

def shiftedVitali (q : ℚ) : Set ℝ := (fun x : ℝ => -(q : ℝ) + x) ⁻¹' vitaliSet

lemma mem_shiftedVitali_iff {q : ℚ} {x : ℝ} :
    x ∈ shiftedVitali q ↔ ∃ v ∈ vitaliSet, (q : ℝ) + v = x := by
  simp only [shiftedVitali, Set.mem_preimage]
  exact ⟨fun h => ⟨-(q : ℝ) + x, h, by ring⟩, fun ⟨v, hv, hxv⟩ => by
    have : -(q : ℝ) + x = v := by linarith
    rwa [this]⟩

lemma pairwiseDisjoint_shiftedVitali :
    ratShifts.PairwiseDisjoint shiftedVitali := by
  intro q₁ _ q₂ _ hne
  change Disjoint (shiftedVitali q₁) (shiftedVitali q₂)
  rw [Set.disjoint_left]
  intro x hx₁ hx₂
  rcases mem_shiftedVitali_iff.mp hx₁ with ⟨_, ⟨c₁, rfl⟩, h₁⟩
  rcases mem_shiftedVitali_iff.mp hx₂ with ⟨_, ⟨c₂, rfl⟩, h₂⟩
  have hdiff : vitaliRep c₁ - vitaliRep c₂ = ((q₂ - q₁ : ℚ) : ℝ) := by
    push_cast; linarith
  have hc : c₁ = c₂ := by
    rw [← vitaliRep_mk c₁, ← vitaliRep_mk c₂]
    exact Quotient.sound ⟨q₂ - q₁, hdiff⟩
  subst hc
  have hq : (q₁ : ℝ) = (q₂ : ℝ) := by linarith
  exact hne (Rat.cast_injective hq)

lemma Ioo_subset_biUnion_shiftedVitali :
    Set.Ioo (0 : ℝ) Real.pi ⊆ ⋃ q ∈ ratShifts, shiftedVitali q := by
  intro x hx
  let c := Quotient.mk ratSetoid x
  have hmk : Quotient.mk ratSetoid x = Quotient.mk ratSetoid (vitaliRep c) :=
    (vitaliRep_mk c).symm
  obtain ⟨q, hq⟩ := Quotient.exact hmk
  have hv := vitaliRep_mem c
  have hqs : q ∈ ratShifts := by
    refine ⟨?_, ?_⟩ <;> linarith [hx.1, hx.2, hv.1, hv.2]
  exact Set.mem_biUnion hqs (mem_shiftedVitali_iff.mpr ⟨vitaliRep c, ⟨c, rfl⟩, by linarith⟩)

lemma biUnion_shiftedVitali_subset_Ioo :
    (⋃ q ∈ ratShifts, shiftedVitali q) ⊆ Set.Ioo (-Real.pi) (2 * Real.pi) := by
  intro x hx
  rcases Set.mem_iUnion₂.mp hx with ⟨q, hq, hxq⟩
  rcases mem_shiftedVitali_iff.mp hxq with ⟨v, hv, rfl⟩
  have hv' := vitaliSet_subset_Ioo hv
  exact ⟨by linarith [hq.1, hv'.1], by linarith [hq.2, hv'.2]⟩

lemma ratShifts_infinite : ratShifts.Infinite := by
  refine Set.infinite_of_injective_forall_mem (f := fun n : ℕ => (1 : ℚ) / (n + 1)) ?_ ?_
  · intro a b hab
    have ha : (a : ℚ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero a
    have hb : (b : ℚ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero b
    have hmul : (a : ℚ) + 1 = (b : ℚ) + 1 := by
      field_simp [ha, hb] at hab
      linarith
    exact_mod_cast add_right_cancel hmul
  · intro n
    let r : ℝ := (((1 : ℚ) / (n + 1) : ℚ) : ℝ)
    have hpos : 0 < r := by
      dsimp [r]; push_cast; positivity
    have hle1 : r ≤ 1 := by
      dsimp [r]; push_cast
      rw [div_le_one (by positivity)]
      linarith
    exact ⟨by linarith [Real.pi_pos], by linarith [Real.two_le_pi]⟩

lemma not_nullMeasurableSet_vitaliSet : ¬ NullMeasurableSet vitaliSet volume := by
  intro hV
  have hcnt : ratShifts.Countable := Set.to_countable ratShifts
  have hnm_shift : ∀ q ∈ ratShifts, NullMeasurableSet (shiftedVitali q) volume := by
    intro q _
    exact hV.preimage (measurePreserving_add_left volume (-(q : ℝ))).quasiMeasurePreserving
  have haedisj : ratShifts.Pairwise (Function.onFun (AEDisjoint volume) shiftedVitali) :=
    fun q₁ h₁ q₂ h₂ hne => (pairwiseDisjoint_shiftedVitali h₁ h₂ hne).aedisjoint
  have hvol_shift : ∀ q : ℚ, volume (shiftedVitali q) = volume vitaliSet := fun q =>
    measure_preimage_add volume (-(q : ℝ)) vitaliSet
  have hunion_eq :
      volume (⋃ q ∈ ratShifts, shiftedVitali q) = ∑' _ : ratShifts, volume vitaliSet := by
    rw [measure_biUnion₀ hcnt haedisj hnm_shift]
    exact tsum_congr fun q => hvol_shift q.1
  have hlow : ENNReal.ofReal Real.pi ≤ volume (⋃ q ∈ ratShifts, shiftedVitali q) := by
    calc ENNReal.ofReal Real.pi
        = volume (Set.Ioo (0 : ℝ) Real.pi) := by rw [Real.volume_Ioo, sub_zero]
      _ ≤ volume (⋃ q ∈ ratShifts, shiftedVitali q) := measure_mono Ioo_subset_biUnion_shiftedVitali
  have hhigh : volume (⋃ q ∈ ratShifts, shiftedVitali q) ≤ ENNReal.ofReal (3 * Real.pi) := by
    calc volume (⋃ q ∈ ratShifts, shiftedVitali q)
        ≤ volume (Set.Ioo (-Real.pi) (2 * Real.pi)) := measure_mono biUnion_shiftedVitali_subset_Ioo
      _ = ENNReal.ofReal (3 * Real.pi) := by
          rw [Real.volume_Ioo]
          congr 1; ring
  rcases eq_or_ne (volume vitaliSet) 0 with h0 | hpos
  · rw [hunion_eq, h0, tsum_zero, nonpos_iff_eq_zero, ENNReal.ofReal_eq_zero] at hlow
    linarith [Real.pi_pos]
  · have : Infinite ratShifts := ratShifts_infinite.to_subtype
    have htop : (∑' _ : ratShifts, volume vitaliSet) = ⊤ :=
      ENNReal.tsum_const_eq_top_of_ne_zero hpos
    rw [hunion_eq, htop, top_le_iff] at hhigh
    exact ENNReal.ofReal_ne_top hhigh

/-! ### Part 2: Isotropic bounded sub-Gaussian vector on `(0, π)` -/

noncomputable def piProb : Measure ℝ :=
  (ENNReal.ofReal Real.pi)⁻¹ • volume.restrict (Set.Ioo (0 : ℝ) Real.pi)

lemma piProb_isProb : IsProbabilityMeasure piProb := by
  refine ⟨?_⟩
  simp only [piProb, Measure.smul_apply, Measure.restrict_apply_univ,
    Real.volume_Ioo, sub_zero, smul_eq_mul]
  exact ENNReal.inv_mul_cancel
    (ENNReal.ofReal_pos.mpr Real.pi_pos).ne' ENNReal.ofReal_ne_top

noncomputable def rowVec (θ : ℝ) : EuclideanSpace ℝ (Fin 2) :=
  (EuclideanSpace.equiv (Fin 2) ℝ).symm ![ -Real.sqrt 2 * Real.sin θ, Real.sqrt 2 * Real.cos θ ]

@[simp]
lemma rowVec_apply_zero (θ : ℝ) : rowVec θ 0 = -Real.sqrt 2 * Real.sin θ := rfl

@[simp]
lemma rowVec_apply_one (θ : ℝ) : rowVec θ 1 = Real.sqrt 2 * Real.cos θ := rfl

lemma inner_rowVec (θ : ℝ) (x : EuclideanSpace ℝ (Fin 2)) :
    ⟪rowVec θ, x⟫ = -Real.sqrt 2 * Real.sin θ * x 0 + Real.sqrt 2 * Real.cos θ * x 1 := by
  rw [PiLp.inner_apply, Fin.sum_univ_two]
  simp only [RCLike.inner_apply, conj_trivial, rowVec_apply_zero, rowVec_apply_one]
  ring

lemma norm_sq_eq_two (x : EuclideanSpace ℝ (Fin 2)) :
    ‖x‖ ^ 2 = x 0 ^ 2 + x 1 ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _),
    Fin.sum_univ_two]
  simp [Real.norm_eq_abs, sq_abs]

lemma inner_rowVec_sq (θ : ℝ) (x : EuclideanSpace ℝ (Fin 2)) :
    ⟪rowVec θ, x⟫ ^ 2 =
      2 * (x 0 ^ 2 * Real.sin θ ^ 2 + x 1 ^ 2 * Real.cos θ ^ 2 -
        2 * x 0 * x 1 * Real.sin θ * Real.cos θ) := by
  rw [inner_rowVec]
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  calc (-Real.sqrt 2 * Real.sin θ * x 0 + Real.sqrt 2 * Real.cos θ * x 1) ^ 2
      = Real.sqrt 2 ^ 2 *
          (x 0 ^ 2 * Real.sin θ ^ 2 + x 1 ^ 2 * Real.cos θ ^ 2 -
            2 * x 0 * x 1 * Real.sin θ * Real.cos θ) := by ring
    _ = 2 * (x 0 ^ 2 * Real.sin θ ^ 2 + x 1 ^ 2 * Real.cos θ ^ 2 -
          2 * x 0 * x 1 * Real.sin θ * Real.cos θ) := by rw [h2]

lemma rowVec_isotropic : IsIsotropic piProb rowVec := by
  have : IsProbabilityMeasure piProb := piProb_isProb
  intro x
  have hcont : Continuous (fun θ : ℝ => ⟪rowVec θ, x⟫ ^ 2) := by
    have hc : Continuous (fun θ : ℝ => ⟪rowVec θ, x⟫) := by
      simp_rw [inner_rowVec]; continuity
    exact hc.pow 2
  have hbdd : ∀ θ : ℝ, ‖⟪rowVec θ, x⟫ ^ 2‖ ≤ 2 * ‖x‖ ^ 2 := by
    intro θ
    have hcs : |⟪rowVec θ, x⟫| ≤ ‖rowVec θ‖ * ‖x‖ := abs_real_inner_le_norm _ _
    have hnorm : ‖rowVec θ‖ ^ 2 = 2 := by
      rw [norm_sq_eq_two, rowVec_apply_zero, rowVec_apply_one]
      have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
      have hsc := Real.sin_sq_add_cos_sq θ
      nlinarith
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    have hsq : ⟪rowVec θ, x⟫ ^ 2 ≤ (‖rowVec θ‖ * ‖x‖) ^ 2 :=
      sq_le_sq.mpr (by rwa [abs_of_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))])
    nlinarith
  have hint : Integrable (fun θ : ℝ => ⟪rowVec θ, x⟫ ^ 2) piProb :=
    Integrable.of_bound hcont.aestronglyMeasurable (2 * ‖x‖ ^ 2) (Filter.Eventually.of_forall hbdd)
  refine ⟨hint, ?_⟩
  let F : ℝ → ℝ := fun θ =>
    (x 0 ^ 2 + x 1 ^ 2) * θ + (x 1 ^ 2 - x 0 ^ 2) * (Real.sin θ * Real.cos θ) -
      2 * x 0 * x 1 * Real.sin θ ^ 2
  have hderiv : ∀ θ ∈ Set.uIcc (0 : ℝ) Real.pi, HasDerivAt F (⟪rowVec θ, x⟫ ^ 2) θ := by
    intro θ _
    have hd1 : HasDerivAt (fun t => (x 0 ^ 2 + x 1 ^ 2) * t) (x 0 ^ 2 + x 1 ^ 2) θ := by
      simpa using (hasDerivAt_id θ).const_mul (x 0 ^ 2 + x 1 ^ 2)
    have hd2 : HasDerivAt (fun t => (x 1 ^ 2 - x 0 ^ 2) * (Real.sin t * Real.cos t))
        ((x 1 ^ 2 - x 0 ^ 2) * (Real.cos θ * Real.cos θ + Real.sin θ * (-Real.sin θ))) θ :=
      ((Real.hasDerivAt_sin θ).mul (Real.hasDerivAt_cos θ)).const_mul (x 1 ^ 2 - x 0 ^ 2)
    have hd3 : HasDerivAt (fun t => 2 * x 0 * x 1 * Real.sin t ^ 2)
        (2 * x 0 * x 1 * (2 * Real.sin θ ^ (2 - 1) * Real.cos θ)) θ :=
      ((Real.hasDerivAt_sin θ).pow 2).const_mul (2 * x 0 * x 1)
    have hdf : HasDerivAt F
        (x 0 ^ 2 + x 1 ^ 2 +
          (x 1 ^ 2 - x 0 ^ 2) * (Real.cos θ * Real.cos θ + Real.sin θ * (-Real.sin θ)) -
          2 * x 0 * x 1 * (2 * Real.sin θ ^ (2 - 1) * Real.cos θ)) θ :=
      (hd1.add hd2).sub hd3
    refine hdf.congr_deriv ?_
    rw [inner_rowVec_sq]
    have hpow1 : Real.sin θ ^ (2 - 1) = Real.sin θ := pow_one _
    have hsc := Real.sin_sq_add_cos_sq θ
    rw [hpow1]
    calc x 0 ^ 2 + x 1 ^ 2 +
            (x 1 ^ 2 - x 0 ^ 2) * (Real.cos θ * Real.cos θ + Real.sin θ * -Real.sin θ) -
            2 * x 0 * x 1 * (2 * Real.sin θ * Real.cos θ)
        = (x 0 ^ 2 + x 1 ^ 2) * 1 +
            (x 1 ^ 2 - x 0 ^ 2) * (Real.cos θ ^ 2 - Real.sin θ ^ 2) -
            4 * x 0 * x 1 * Real.sin θ * Real.cos θ := by ring
      _ = (x 0 ^ 2 + x 1 ^ 2) * (Real.sin θ ^ 2 + Real.cos θ ^ 2) +
            (x 1 ^ 2 - x 0 ^ 2) * (Real.cos θ ^ 2 - Real.sin θ ^ 2) -
            4 * x 0 * x 1 * Real.sin θ * Real.cos θ := by rw [hsc]
      _ = 2 * (x 0 ^ 2 * Real.sin θ ^ 2 + x 1 ^ 2 * Real.cos θ ^ 2 -
            2 * x 0 * x 1 * Real.sin θ * Real.cos θ) := by ring
  have hint_iv : IntervalIntegrable (fun θ : ℝ => ⟪rowVec θ, x⟫ ^ 2) volume 0 Real.pi :=
    hcont.intervalIntegrable 0 Real.pi
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint_iv
  have hF : F Real.pi - F 0 = ‖x‖ ^ 2 * Real.pi := by
    simp only [F, Real.sin_pi, Real.sin_zero, norm_sq_eq_two]
    ring
  rw [hF, intervalIntegral.integral_of_le Real.pi_pos.le, integral_Ioc_eq_integral_Ioo] at hftc
  simp only [piProb, integral_smul_measure, ENNReal.toReal_inv,
    ENNReal.toReal_ofReal Real.pi_pos.le, smul_eq_mul]
  rw [hftc]
  field_simp [Real.pi_pos.ne']

lemma exp_half_le_two : Real.exp (1 / 2 : ℝ) ≤ 2 := by
  have h1 : (1 / 2 : ℝ) ≤ Real.exp (-1 / 2) := by
    have := Real.add_one_le_exp (-1 / 2 : ℝ)
    linarith
  have hpos : 0 < Real.exp (1 / 2 : ℝ) := Real.exp_pos _
  have hmul : Real.exp (1 / 2 : ℝ) * (1 / 2) ≤ Real.exp (1 / 2 : ℝ) * Real.exp (-1 / 2) :=
    mul_le_mul_of_nonneg_left h1 hpos.le
  have hexp0 : Real.exp (1 / 2 : ℝ) * Real.exp (-1 / 2) = 1 := by
    rw [← Real.exp_add]; norm_num
  linarith

lemma rowVec_subgaussian : subgaussianVectorNorm piProb rowVec ≤ (2 : ℝ≥0) := by
  have : IsProbabilityMeasure piProb := piProb_isProb
  unfold subgaussianVectorNorm
  refine iSup_le fun u => ?_
  unfold HighDimProb.Concentration.subgaussianNorm
  have h2pos : (0 : ℝ) < 2 := by norm_num
  have hcont : Continuous (fun θ : ℝ => Real.exp (⟪rowVec θ, u.1⟫ ^ 2 / (2 : ℝ) ^ 2)) := by
    have hc : Continuous (fun θ : ℝ => ⟪rowVec θ, u.1⟫) := by
      simp_rw [inner_rowVec]; continuity
    exact Real.continuous_exp.comp ((hc.pow 2).div_const _)
  have hle_half : ∀ θ : ℝ, ⟪rowVec θ, u.1⟫ ^ 2 / (2 : ℝ) ^ 2 ≤ 1 / 2 := by
    intro θ
    have hcs : |⟪rowVec θ, u.1⟫| ≤ ‖rowVec θ‖ * ‖u.1‖ := abs_real_inner_le_norm _ _
    have hnorm : ‖rowVec θ‖ ^ 2 = 2 := by
      rw [norm_sq_eq_two, rowVec_apply_zero, rowVec_apply_one]
      have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
      have hsc := Real.sin_sq_add_cos_sq θ
      nlinarith
    rw [u.2, mul_one] at hcs
    have hsq : ⟪rowVec θ, u.1⟫ ^ 2 ≤ 2 := by
      have hsq' : ⟪rowVec θ, u.1⟫ ^ 2 ≤ ‖rowVec θ‖ ^ 2 :=
        sq_le_sq.mpr (by rwa [abs_of_nonneg (norm_nonneg _)])
      rwa [hnorm] at hsq'
    linarith
  have hbdd : ∀ θ : ℝ, ‖Real.exp (⟪rowVec θ, u.1⟫ ^ 2 / (2 : ℝ) ^ 2)‖ ≤ 2 := by
    intro θ
    rw [Real.norm_of_nonneg (Real.exp_pos _).le]
    exact (Real.exp_le_exp.mpr (hle_half θ)).trans exp_half_le_two
  have hint : Integrable (fun θ : ℝ => Real.exp (⟪rowVec θ, u.1⟫ ^ 2 / (2 : ℝ) ^ 2)) piProb :=
    Integrable.of_bound hcont.aestronglyMeasurable 2 (Filter.Eventually.of_forall hbdd)
  have hint_le : ∫ θ, Real.exp (⟪rowVec θ, u.1⟫ ^ 2 / (2 : ℝ) ^ 2) ∂piProb ≤ 2 := by
    calc ∫ θ, Real.exp (⟪rowVec θ, u.1⟫ ^ 2 / (2 : ℝ) ^ 2) ∂piProb
        ≤ ∫ _ : ℝ, (2 : ℝ) ∂piProb :=
          integral_mono hint (integrable_const 2) fun θ =>
            (Real.exp_le_exp.mpr (hle_half θ)).trans exp_half_le_two
      _ = 2 := by simp
  refine (iInf_le _ (2 : ℝ)).trans <| (iInf_le _ h2pos).trans <|
    (iInf_le _ hint).trans <| (iInf_le _ hint_le).trans ?_
  simp

/-! ### Part 3: The bounded non-measurable set `T ⊂ ℝ²` and its slice diameters -/

noncomputable def unitRay (φ : ℝ) : EuclideanSpace ℝ (Fin 2) :=
  (EuclideanSpace.equiv (Fin 2) ℝ).symm ![ Real.cos φ, Real.sin φ ]

@[simp]
lemma unitRay_apply_zero (φ : ℝ) : unitRay φ 0 = Real.cos φ := rfl

@[simp]
lemma unitRay_apply_one (φ : ℝ) : unitRay φ 1 = Real.sin φ := rfl

lemma norm_unitRay (φ : ℝ) : ‖unitRay φ‖ = 1 := by
  have hsq : ‖unitRay φ‖ ^ 2 = 1 := by
    rw [norm_sq_eq_two, unitRay_apply_zero, unitRay_apply_one, add_comm]
    exact Real.sin_sq_add_cos_sq φ
  nlinarith [norm_nonneg (unitRay φ)]

def vitaliCone : Set (EuclideanSpace ℝ (Fin 2)) :=
  {(0 : EuclideanSpace ℝ (Fin 2))} ∪ (unitRay '' vitaliSet)

lemma mem_vitaliCone_norm_le_one {x : EuclideanSpace ℝ (Fin 2)} (hx : x ∈ vitaliCone) :
    ‖x‖ ≤ 1 := by
  rcases hx with rfl | ⟨φ, _, rfl⟩
  · simp
  · rw [norm_unitRay]

lemma vitaliCone_bounded : Bornology.IsBounded vitaliCone := by
  refine Metric.isBounded_closedBall (x := (0 : EuclideanSpace ℝ (Fin 2))) (r := 1) |>.subset ?_
  intro x hx
  rw [Metric.mem_closedBall, dist_zero_right]
  exact mem_vitaliCone_norm_le_one hx

lemma vitaliCone_width_real :
    ∃ w : ℝ, gaussianWidth vitaliCone = (w : EReal) := by
  let μ := stdGaussian (EuclideanSpace ℝ (Fin 2))
  have h0_mem : (0 : EuclideanSpace ℝ (Fin 2)) ∈ vitaliCone := Or.inl rfl
  let x₀ : vitaliCone := ⟨0, h0_mem⟩
  have hlow : (0 : EReal) ≤ gaussianWidth vitaliCone := by
    unfold gaussianWidth expSup
    let S₀ : {s : Finset vitaliCone // s.Nonempty} := ⟨{x₀}, Finset.singleton_nonempty x₀⟩
    refine le_trans ?_ (le_iSup _ S₀)
    simp [S₀, x₀]
  have hint_norm : Integrable (fun g : EuclideanSpace ℝ (Fin 2) => ‖g‖) μ :=
    IsGaussian.integrable_id.norm
  let M : ℝ := ∫ g, ‖g‖ ∂μ
  have hhigh : gaussianWidth vitaliCone ≤ (M : EReal) := by
    unfold gaussianWidth expSup
    refine iSup_le fun S => EReal.coe_le_coe_iff.mpr ?_
    have hcont_sup : Continuous (fun g : EuclideanSpace ℝ (Fin 2) =>
        S.1.sup' S.2 (fun x => ⟪g, x.1⟫)) := by
      rcases S with ⟨s, hs⟩
      induction hs using Finset.Nonempty.cons_induction with
      | singleton a =>
          simp only [Finset.sup'_singleton]
          exact continuous_id.inner continuous_const
      | cons a t hat hne ih =>
          simp_rw [Finset.sup'_cons hne]
          exact (continuous_id.inner continuous_const).sup ih
    have hpt : ∀ g : EuclideanSpace ℝ (Fin 2), |S.1.sup' S.2 (fun x => ⟪g, x.1⟫)| ≤ ‖g‖ := by
      intro g
      rw [abs_le]
      constructor
      · obtain ⟨x, hxS⟩ := S.2
        have hle : -‖g‖ ≤ ⟪g, x.1⟫ := by
          have := neg_abs_le ⟪g, x.1⟫
          have hcs := (abs_real_inner_le_norm g x.1).trans
            (mul_le_of_le_one_right (norm_nonneg g) (mem_vitaliCone_norm_le_one x.2))
          linarith
        exact hle.trans (Finset.le_sup' (fun y : vitaliCone => ⟪g, y.1⟫) hxS)
      · refine Finset.sup'_le S.2 _ fun x _ => ?_
        exact (real_inner_le_norm g x.1).trans
          (mul_le_of_le_one_right (norm_nonneg g) (mem_vitaliCone_norm_le_one x.2))
    have hint_sup : Integrable (fun g => S.1.sup' S.2 (fun x => ⟪g, x.1⟫)) μ :=
      hint_norm.mono' hcont_sup.aestronglyMeasurable
        (Filter.Eventually.of_forall fun g => by rw [Real.norm_eq_abs]; exact hpt g)
    exact integral_mono hint_sup hint_norm fun g => (le_abs_self _).trans (hpt g)
  have hne_bot : gaussianWidth vitaliCone ≠ ⊥ := by
    intro h; rw [h] at hlow; exact not_le_of_gt EReal.bot_lt_zero hlow
  have hne_top : gaussianWidth vitaliCone ≠ ⊤ := by
    intro h; rw [h] at hhigh; exact not_le_of_gt (EReal.coe_lt_top M) hhigh
  exact ⟨(gaussianWidth vitaliCone).toReal, (EReal.coe_toReal hne_top hne_bot).symm⟩

lemma inner_rowVec_unitRay {θ φ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) Real.pi)
    (hφ : φ ∈ Set.Ioo (0 : ℝ) Real.pi) :
    ⟪rowVec θ, unitRay φ⟫ = 0 ↔ φ = θ := by
  have heq : ⟪rowVec θ, unitRay φ⟫ = Real.sqrt 2 * Real.sin (φ - θ) := by
    rw [inner_rowVec, unitRay_apply_zero, unitRay_apply_one, Real.sin_sub]
    ring
  rw [heq, mul_eq_zero]
  have hs2 : Real.sqrt 2 ≠ 0 := by positivity
  simp only [hs2, false_or]
  constructor
  · intro hsin
    rcases lt_trichotomy φ θ with hlt | rfl | hgt
    · exfalso
      have hpos : 0 < Real.sin (θ - φ) :=
        Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [hθ.2, hφ.1])
      have : Real.sin (φ - θ) = -Real.sin (θ - φ) := by
        rw [← Real.sin_neg]; congr 1; ring
      linarith
    · rfl
    · exfalso
      have hpos : 0 < Real.sin (φ - θ) :=
        Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [hφ.2, hθ.1])
      linarith
  · rintro rfl
    simp

lemma slice_diam_eq_indicator {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) Real.pi) :
    Metric.diam (vitaliCone ∩ {x | ∀ i : Fin 1, ⟪(fun _ : Fin 1 => rowVec) i θ, x⟫ = 0}) =
      vitaliSet.indicator (fun _ => (1 : ℝ)) θ := by
  set K := vitaliCone ∩ {x | ∀ i : Fin 1, ⟪(fun _ : Fin 1 => rowVec) i θ, x⟫ = 0}
  by_cases hθV : θ ∈ vitaliSet
  · rw [Set.indicator_of_mem hθV]
    have hK_eq : K = {0, unitRay θ} := by
      ext x
      simp only [K, vitaliCone, Set.mem_inter_iff, Set.mem_union, Set.mem_singleton_iff,
        Set.mem_image, Set.mem_ofPred, Fin.forall_fin_one, Set.mem_insert_iff]
      constructor
      · rintro ⟨rfl | ⟨φ, hφV, rfl⟩, horth⟩
        · exact Or.inl rfl
        · right
          have hφ_eq := (inner_rowVec_unitRay hθ (vitaliSet_subset_Ioo hφV)).mp horth
          rw [hφ_eq]
      · rintro (rfl | rfl)
        · exact ⟨Or.inl rfl, inner_zero_right _⟩
        · exact ⟨Or.inr ⟨θ, hθV, rfl⟩, (inner_rowVec_unitRay hθ hθ).mpr rfl⟩
    rw [hK_eq]
    have hle : Metric.diam ({0, unitRay θ} : Set (EuclideanSpace ℝ (Fin 2))) ≤ 1 := by
      refine Metric.diam_le_of_forall_dist_le zero_le_one fun a ha b hb => ?_
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
      rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
      · simp
      · simp [dist_zero_left, norm_unitRay]
      · simp [dist_zero_right, norm_unitRay]
      · simp
    have hge : 1 ≤ Metric.diam ({0, unitRay θ} : Set (EuclideanSpace ℝ (Fin 2))) := by
      have hb : Bornology.IsBounded ({0, unitRay θ} : Set (EuclideanSpace ℝ (Fin 2))) :=
        (Set.toFinite _).isBounded
      calc (1 : ℝ) = dist (0 : EuclideanSpace ℝ (Fin 2)) (unitRay θ) := by
              rw [dist_zero_left, norm_unitRay]
        _ ≤ Metric.diam ({0, unitRay θ} : Set (EuclideanSpace ℝ (Fin 2))) :=
              Metric.dist_le_diam_of_mem hb (by simp) (by simp)
    linarith
  · rw [Set.indicator_of_notMem hθV]
    have hK_eq : K = {0} := by
      ext x
      simp only [K, vitaliCone, Set.mem_inter_iff, Set.mem_union, Set.mem_singleton_iff,
        Set.mem_image, Set.mem_ofPred, Fin.forall_fin_one]
      constructor
      · rintro ⟨rfl | ⟨φ, hφV, rfl⟩, horth⟩
        · rfl
        · exfalso
          have hφ_eq := (inner_rowVec_unitRay hθ (vitaliSet_subset_Ioo hφV)).mp horth
          exact hθV (hφ_eq ▸ hφV)
      · rintro rfl
        exact ⟨Or.inl rfl, inner_zero_right _⟩
    rw [hK_eq, Metric.diam_singleton]

lemma not_integrable_slice_diam :
    ¬ Integrable
      (fun θ => Metric.diam
        (vitaliCone ∩ {x | ∀ i : Fin 1, ⟪(fun _ : Fin 1 => rowVec) i θ, x⟫ = 0})) piProb := by
  intro hint
  have hcompl_zero : piProb (Set.Ioo (0 : ℝ) Real.pi)ᶜ = 0 := by
    simp [piProb, Measure.restrict_apply measurableSet_Ioo.compl]
  have hae : (fun θ => Metric.diam
      (vitaliCone ∩ {x | ∀ i : Fin 1, ⟪(fun _ : Fin 1 => rowVec) i θ, x⟫ = 0})) =ᵐ[piProb]
      vitaliSet.indicator (fun _ => (1 : ℝ)) := by
    rw [Filter.eventuallyEq_iff_exists_mem]
    refine ⟨Set.Ioo (0 : ℝ) Real.pi, ?_, fun θ hθ => slice_diam_eq_indicator hθ⟩
    rwa [mem_ae_iff]
  have haesm : AEStronglyMeasurable (vitaliSet.indicator (fun _ => (1 : ℝ))) piProb :=
    hint.aestronglyMeasurable.congr hae
  have hpre : vitaliSet.indicator (fun _ => (1 : ℝ)) ⁻¹' {(0 : ℝ)}ᶜ = vitaliSet := by
    ext θ
    by_cases h : θ ∈ vitaliSet <;> simp [h]
  have hnm_piProb : NullMeasurableSet vitaliSet piProb := by
    rw [← hpre]
    exact haesm.aemeasurable.nullMeasurable (isOpen_compl_singleton.measurableSet)
  have hc_ne : (ENNReal.ofReal Real.pi)⁻¹ ≠ 0 :=
    ENNReal.inv_ne_zero.mpr ENNReal.ofReal_ne_top
  have hnm_rest : NullMeasurableSet vitaliSet (volume.restrict (Set.Ioo (0 : ℝ) Real.pi)) :=
    (nullMeasurableSet_smul_measure_iff hc_ne).mp hnm_piProb
  have hnm_vol : NullMeasurableSet vitaliSet volume :=
    (nullMeasurableSet_restrict_of_subset vitaliSet_subset_Ioo).mp hnm_rest
  exact not_nullMeasurableSet_vitaliSet hnm_vol

end MStarCounterexample

open MStarCounterexample

theorem solution :
    ¬ (∃ C : ℝ, 0 < C ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        {m n : ℕ} (_hm : 0 < m) (A : Fin m → Ω → EuclideanSpace ℝ (Fin n)),
        iIndepFun A P →
        (∀ i, IsIsotropic P (A i)) →
        ∀ (K : ℝ≥0), (∀ i, subgaussianVectorNorm P (A i) ≤ K) →
        ∀ (T : Set (EuclideanSpace ℝ (Fin n))), Bornology.IsBounded T →
        ∀ (w : ℝ), gaussianWidth T = (w : EReal) →
          Integrable
              (fun ω => Metric.diam (T ∩ {x | ∀ i, inner (𝕜 := ℝ) (A i ω) x = 0})) P ∧
          ∫ ω, Metric.diam (T ∩ {x | ∀ i, inner (𝕜 := ℝ) (A i ω) x = 0}) ∂P ≤
            C * K ^ 2 * w / Real.sqrt (m : ℝ)) := by
  rintro ⟨C, _, hC⟩
  have : IsProbabilityMeasure piProb := piProb_isProb
  obtain ⟨w, hw⟩ := vitaliCone_width_real
  have hA_indep : iIndepFun (fun _ : Fin 1 => rowVec) piProb := iIndepFun.of_subsingleton
  have hres := hC piProb Nat.zero_lt_one (fun _ : Fin 1 => rowVec) hA_indep
    (fun _ => rowVec_isotropic) (2 : ℝ≥0) (fun _ => rowVec_subgaussian)
    vitaliCone vitaliCone_bounded w hw
  exact not_integrable_slice_diam hres.1
