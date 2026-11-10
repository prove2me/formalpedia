-- Prove2me | solution 1 for JiangALSOX.Dominance.kkt2
-- status  : ACCEPTED   (disprove)
-- author  : @kmehltretter82
-- created : 2026-11-09T11:50:48.599939+00:00
-- url     : https://prove2.me/submissions/442069fa-cd98-4648-952c-71dd0bdc3798

import Definitions.Def_JiangALSOX_Dominance_Certificates

open MeasureTheory
open scoped ENNReal
open JiangALSOX.Dominance

def xiK (k : ℕ) : (Set.univ : Set (Fin 1 → ℝ)) :=
  ⟨fun _ => (2 : ℝ) ^ (k + 1), Set.mem_univ _⟩

noncomputable def k2Measure : Measure (Set.univ : Set (Fin 1 → ℝ)) :=
  Measure.sum (fun k : ℕ => ((1 / 2 : ℝ≥0∞) ^ (k + 1)) • Measure.dirac (xiK k))

instance : IsProbabilityMeasure k2Measure := by
  refine ⟨?_⟩
  unfold k2Measure
  rw [Measure.sum_apply _ MeasurableSet.univ]
  have h1 : (fun k : ℕ => (((1 / 2 : ℝ≥0∞) ^ (k + 1)) • Measure.dirac (xiK k)) Set.univ) =
      fun k : ℕ => (2 : ℝ≥0∞)⁻¹ * ((2 : ℝ≥0∞)⁻¹) ^ k := by
    ext k
    simp [pow_succ']
  rw [h1, ENNReal.tsum_mul_left, ENNReal.tsum_geometric]
  have hsub : (1 : ℝ≥0∞) - 2⁻¹ = 2⁻¹ := by
    nth_rw 1 [← ENNReal.inv_two_add_inv_two]
    exact ENNReal.add_sub_cancel_right (by norm_num)
  rw [hsub, ENNReal.mul_inv_cancel (by norm_num) (by norm_num)]

@[reducible] noncomputable def k2Model : Model 0 1 0 where
  Ξ := Set.univ
  P := k2Measure
  gi := fun _ _ ξ => max (ξ.val 0) 1
  X := Set.univ
  C := ⊤
  c := 0
  ε := 1 / 2

def sCand : k2Model.Ξ → ℝ := fun ξ => max (ξ.val 0) 1

private lemma measurable_sCand : Measurable sCand :=
  ((measurable_pi_apply 0).comp measurable_subtype_coe).max measurable_const

private lemma loss_k2Model (x : Fin 0 → ℝ) (ξ : k2Model.Ξ) :
    loss k2Model x ξ = sCand ξ := by
  simp [loss, k2Model, sCand]

private lemma assumptions_k2Model : Assumptions k2Model := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change IsProbabilityMeasure k2Measure
    infer_instance
  · simp
  · simp
    norm_num
  · intro i x
    exact measurable_sCand
  · exact Filter.Eventually.of_forall (fun ξ _ =>
      ⟨convexOn_const _ convex_univ, lowerSemicontinuous_const⟩)
  · exact ⟨0, Set.mem_univ 0⟩
  · exact isClosed_univ
  · exact convex_univ
  · intro x _
    trivial
  · exact isClosed_univ
  · intro x _ _
    exact Subsingleton.elim x 0

private lemma feasible_cand : hingeFeasible k2Model 0 0 sCand := by
  refine ⟨Set.mem_univ 0, by simp, measurable_sCand, ?_⟩
  exact Filter.Eventually.of_forall (fun ξ => by
    rw [loss_k2Model]
    refine ⟨le_trans zero_le_one (le_max_right _ _), le_rfl⟩)

private lemma optimal_cand : hingeOptimal k2Model 0 0 sCand := by
  refine ⟨feasible_cand, ?_⟩
  intro y r hr
  unfold hingeObjective positiveExpectation
  refine EReal.coe_ennreal_le_coe_ennreal_iff.mpr (lintegral_mono_ae ?_)
  filter_upwards [hr.2.2.2] with ξ hξ
  rw [loss_k2Model] at hξ
  exact ENNReal.ofReal_le_ofReal hξ.2

private lemma sCand_xiK (k : ℕ) : sCand (xiK k) = (2 : ℝ) ^ (k + 1) := by
  unfold sCand xiK
  dsimp
  have h1 : (1 : ℝ) ≤ (2 : ℝ) ^ (k + 1) := by
    have : (1 : ℝ) = (2 : ℝ) ^ 0 := rfl
    rw [this]
    exact pow_le_pow_right₀ (by norm_num) (Nat.zero_le _)
  exact max_eq_left h1

theorem solution : ¬ (∀ {n m I : ℕ} (D : Model n m I) (hD : Assumptions D) (t : ℝ) (x : Fin n → ℝ) (s : D.Ξ → ℝ) (hfeas : hingeFeasible D t x s), hingeOptimal D t x s ↔ ∃ α μ π, hingeCertificate D t x s α μ π) := by
  intro H
  have hcert := (H k2Model assumptions_k2Model 0 0 sCand feasible_cand).mp optimal_cand
  rcases hcert with ⟨α, μ, π, _, _, _, ⟨h, ⟨a, hfa, _⟩, _⟩, hae, _, _⟩
  have hk_all : ∀ k : ℕ, α (xiK k) = 1 := by
    intro k
    have hk : μ (xiK k) + α (xiK k) = 1 ∧
        complementary (α (xiK k)) (sCand (xiK k) - loss k2Model 0 (xiK k)) ∧
        complementary (μ (xiK k)) (sCand (xiK k)) := by
      by_contra hnot
      have hzero : k2Measure {ξ : k2Model.Ξ | ¬ (μ ξ + α ξ = 1 ∧
          complementary (α ξ) (sCand ξ - loss k2Model 0 ξ) ∧ complementary (μ ξ) (sCand ξ))} = 0 :=
        ae_iff.mp hae
      have hle := Measure.le_sum (fun j : ℕ => ((1 / 2 : ℝ≥0∞) ^ (j + 1)) • Measure.dirac (xiK j)) k
        {ξ : k2Model.Ξ | ¬ (μ ξ + α ξ = 1 ∧
          complementary (α ξ) (sCand ξ - loss k2Model 0 ξ) ∧ complementary (μ ξ) (sCand ξ))}
      unfold k2Measure at hzero
      rw [hzero] at hle
      have hdirac : Measure.dirac (xiK k) {ξ : k2Model.Ξ | ¬ (μ ξ + α ξ = 1 ∧
          complementary (α ξ) (sCand ξ - loss k2Model 0 ξ) ∧ complementary (μ ξ) (sCand ξ))} = 1 :=
        Measure.dirac_apply_of_mem hnot
      simp only [Measure.smul_apply, hdirac, smul_eq_mul, mul_one, nonpos_iff_eq_zero] at hle
      have hne : ((1 / 2 : ℝ≥0∞) ^ (k + 1)) ≠ 0 := pow_ne_zero (k + 1) (by norm_num)
      exact hne hle
    have hcomp := hk.2.2.2.2
    rw [sCand_xiK] at hcomp
    have hpow_ne : ((2 : ℝ) ^ (k + 1)) ≠ 0 := by positivity
    have hmu : μ (xiK k) = 0 := (mul_eq_zero.mp hcomp).resolve_right hpow_ne
    linarith [hk.1]
  have hpos : positiveExpectation k2Model.P (fun ξ => α ξ * loss k2Model 0 ξ) = ⊤ := by
    unfold positiveExpectation
    change ∫⁻ ω, ENNReal.ofReal (α ω * loss k2Model 0 ω) ∂k2Measure = ⊤
    unfold k2Measure
    rw [lintegral_sum_measure]
    have hterm : (fun k : ℕ => ∫⁻ ω, ENNReal.ofReal (α ω * loss k2Model 0 ω)
        ∂(((1 / 2 : ℝ≥0∞) ^ (k + 1)) • Measure.dirac (xiK k))) = fun _ : ℕ => 1 := by
      ext k
      rw [lintegral_smul_measure, lintegral_dirac]
      dsimp
      rw [hk_all k, one_mul, loss_k2Model, sCand_xiK, ENNReal.ofReal_pow zero_le_two,
        ENNReal.ofReal_ofNat, ← mul_pow, one_div,
        ENNReal.inv_mul_cancel (by norm_num) (by norm_num), one_pow]
    rw [hterm]
    exact ENNReal.tsum_const_eq_top_of_ne_zero one_ne_zero
  have hneg : positiveExpectation k2Model.P (fun ω => -(α ω * loss k2Model 0 ω)) = 0 := by
    unfold positiveExpectation
    change ∫⁻ ω, ENNReal.ofReal (-(α ω * loss k2Model 0 ω)) ∂k2Measure = 0
    unfold k2Measure
    rw [lintegral_sum_measure]
    have hterm : (fun k : ℕ => ∫⁻ ω, ENNReal.ofReal (-(α ω * loss k2Model 0 ω))
        ∂(((1 / 2 : ℝ≥0∞) ^ (k + 1)) • Measure.dirac (xiK k))) = fun _ : ℕ => 0 := by
      ext k
      rw [lintegral_smul_measure, lintegral_dirac]
      dsimp
      rw [hk_all k, one_mul, loss_k2Model, sCand_xiK]
      have hle : -((2 : ℝ) ^ (k + 1)) ≤ 0 := neg_nonpos.mpr (by positivity)
      rw [ENNReal.ofReal_eq_zero.mpr hle, mul_zero]
    rw [hterm, tsum_zero]
  unfold weightedFunctional signedExpectation at hfa
  split_ifs at hfa with hcond
  rw [hpos, hneg] at hfa
  injection hfa with htop
  exact EReal.coe_ne_top a htop.symm
