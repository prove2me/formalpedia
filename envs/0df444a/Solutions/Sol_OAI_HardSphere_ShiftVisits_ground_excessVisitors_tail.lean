-- Prove2me | solution 1 for OAI.HardSphere.ShiftVisits.ground_excessVisitors_tail
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T20:24:50.690778+00:00
-- url     : https://prove2.me/submissions/82c38363-a838-43c6-b20e-7d116ffa86cc

import Mathlib
import Definitions.Def_HardSphere
import Definitions.Def_OAIQ054H002
import Theorems.Thm_OAI_HardSphere_IsGroundVector_groundPathLaw_probability
import Theorems.Thm_OAI_HardSphere_ground_product_one_add
import Theorems.Thm_OAI_HardSphere_weighted_count_penalty

section
-- module Solutions.OAIQ054_HS.HardSphere_Bridges_Index
attribute [-instance] _root_.OAI.HardSphere.Bridge.exposedBridgeKernel_markov _root_.OAI.HardSphere.Bridge.exposedPeriodSingle_finite _root_.OAI.HardSphere.Bridge.exposedTrialKernel_markov _root_.OAI.HardSphere.Bridge.instBorelSpaceContinuousMapElemRealTimePoint _root_.OAI.HardSphere.Bridge.instIsProbabilityMeasureNoiseLaw _root_.OAI.HardSphere.Bridge.instMeasurableSpaceContinuousMapElemRealTimePoint _root_.OAI.HardSphere.Bridge.parameterBridgeKernel_markov _root_.OAI.HardSphere.Bridge.parameterIndividualReference_finite _root_.OAI.HardSphere.Bridge.parameterTrialKernel_markov _root_.OAI.HardSphere.Bridge.trialKernel_markov _root_.OAI.HardSphere.Groups.cellPathReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Wiener.instIsProbabilityMeasureContinuousMapElemRealTimeBridgeLaw _root_.OAI.HardSphere.configurationPathBorel _root_.OAI.HardSphere.coordinateBridge_probability _root_.OAI.HardSphere.coordinateWiener_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
noncomputable section
open scoped BigOperators ComplexConjugate
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.Wiener

lemma coordinate_preserving (i : Index) :
    MeasurePreserving (fun ω : Noise ↦ ω i) law (gaussianReal 0 1) :=
  measurePreserving_eval_infinitePi _ _

lemma tent_nonneg (n : ℕ) (k : Fin (2 ^ n)) (t : ℝ) : 0 ≤ tent n k t :=
  le_max_left _ _

lemma tent_le_one (n : ℕ) (k : Fin (2 ^ n)) (t : ℝ) : tent n k t ≤ 1 := by
  unfold tent
  exact max_le (by norm_num) (by linarith [abs_nonneg ((2:ℝ)^(n+1)*t-(2*(k:ℝ)+1))])

lemma tent_positive_unique (n : ℕ) (k l : Fin (2 ^ n)) (t : ℝ)
    (hk : 0 < tent n k t) (hl : 0 < tent n l t) : k = l := by
  have hk' : |(2 : ℝ) ^ (n + 1) * t - (2 * (k : ℝ) + 1)| < 1 := by
    simpa only [tent, lt_max_iff, lt_self_iff_false, false_or, sub_pos] using hk
  have hl' : |(2 : ℝ) ^ (n + 1) * t - (2 * (l : ℝ) + 1)| < 1 := by
    simpa only [tent, lt_max_iff, lt_self_iff_false, false_or, sub_pos] using hl
  obtain ⟨hk1, hk2⟩ := abs_lt.mp hk'
  obtain ⟨hl1, hl2⟩ := abs_lt.mp hl'
  have hkl : (k : ℝ) < (l : ℝ) + 1 := by linarith
  have hlk : (l : ℝ) < (k : ℝ) + 1 := by linarith
  have hkl' : k.val < l.val + 1 := by exact_mod_cast hkl
  have hlk' : l.val < k.val + 1 := by exact_mod_cast hlk
  apply Fin.ext
  omega

lemma sum_tent_le_one (n : ℕ) (t : ℝ) : ∑ k, tent n k t ≤ 1 := by
  classical
  by_cases h : ∃ k, 0 < tent n k t
  · obtain ⟨k, hk⟩ := h
    rw [Finset.sum_eq_single k]
    · exact tent_le_one n k t
    · intro l _ hl
      exact le_antisymm (le_of_not_gt fun hp ↦ hl (tent_positive_unique n l k t hp hk))
        (tent_nonneg n l t)
    · simp
  · have hz : ∀ k, tent n k t = 0 := fun k ↦
      le_antisymm (le_of_not_gt fun hk ↦ h ⟨k, hk⟩) (tent_nonneg n k t)
    simp [hz]

lemma amplitude_nonneg (n : ℕ) : 0 ≤ amplitude n := by unfold amplitude; positivity

lemma norm_level_le (n : ℕ) (ω : Noise) {M : ℝ} (hM : 0 ≤ M)
    (hω : ∀ k : Fin (2 ^ n), |ω (.inr ⟨n, k⟩)| ≤ M) :
    ‖level n ω‖ ≤ amplitude n * M := by
  apply (ContinuousMap.norm_le _ (mul_nonneg (amplitude_nonneg n) hM)).2
  intro t
  simp only [level, ContinuousMap.smul_apply, ContinuousMap.sum_apply,
    smul_eq_mul, tentMap, ContinuousMap.coe_mk, Real.norm_eq_abs]
  rw [abs_mul, abs_of_nonneg (amplitude_nonneg n)]
  apply mul_le_mul_of_nonneg_left _ (amplitude_nonneg n)
  calc
    |∑ k, ω (.inr ⟨n, k⟩) * tent n k t| ≤
        ∑ k, |ω (.inr ⟨n, k⟩) * tent n k t| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ k, |ω (.inr ⟨n, k⟩)| * tent n k t := by
      simp_rw [abs_mul, abs_of_nonneg (tent_nonneg n _ t)]
    _ ≤ ∑ k, M * tent n k t := Finset.sum_le_sum fun k _ ↦
      mul_le_mul_of_nonneg_right (hω k) (tent_nonneg n k t)
    _ = M * ∑ k, tent n k t := (Finset.mul_sum ..).symm
    _ ≤ M * 1 := mul_le_mul_of_nonneg_left (sum_tent_le_one n t) hM
    _ = M := mul_one _

lemma moment_ne_top : moment ≠ ∞ := by
  exact ENNReal.pow_ne_top (memLp_id_gaussianReal' (μ := 0) (v := 1) 4 (by norm_num)).2.ne

lemma coordinate_tail (i : Index) {a : ℝ} (ha : 0 < a) :
    law {ω | a ≤ |ω i|} ≤ (ENNReal.ofReal a)⁻¹ ^ (4 : ℕ) * moment := by
  have hm := (memLp_id_gaussianReal' (μ := 0) (v := 1) 4 (by norm_num))
  have he : eLpNorm (fun ω : Noise ↦ ω i) 4 law =
      eLpNorm (id : ℝ → ℝ) 4 (gaussianReal 0 1) :=
    by simpa only [Function.comp_def, id_eq] using
      (eLpNorm_comp_measurePreserving (p := 4) (g := (id : ℝ → ℝ))
        hm.aestronglyMeasurable (coordinate_preserving i))
  have ht := meas_ge_le_mul_pow_eLpNorm_enorm law (p := 4) (by norm_num) (by norm_num)
    (f := fun ω : Noise ↦ ω i)
    ((coordinate_preserving i).measurable.aestronglyMeasurable)
    (ε := ENNReal.ofReal a) (ne_of_gt (ENNReal.ofReal_pos.mpr ha)) (fun h => absurd h (by simp))
  have hs : {ω : Noise | ENNReal.ofReal a ≤ ‖ω i‖ₑ} = {ω | a ≤ |ω i|} := by
    ext ω
    simp only [Set.mem_ofPred_eq, ← ofReal_norm, Real.norm_eq_abs]
    exact ENNReal.ofReal_le_ofReal_iff (abs_nonneg _)
  simpa only [Function.comp_def, id_eq, ENNReal.toReal_ofNat, ← ENNReal.rpow_natCast,
    Nat.cast_ofNat, he, hs, moment] using ht

lemma badLevel_bound (n : ℕ) :
    law (badLevel n) ≤ (ENNReal.ofReal (81/128 : ℝ)) ^ n * moment := by
  have hu : badLevel n = ⋃ k : Fin (2 ^ n), {ω | (4/3 : ℝ)^n ≤ |ω (.inr ⟨n, k⟩)|} := by
    ext ω; simp [badLevel]
  rw [hu]
  refine (measure_iUnion_fintype_le _ _).trans ?_
  calc
    _ ≤ ∑ _k : Fin (2 ^ n), (ENNReal.ofReal ((4/3 : ℝ)^n))⁻¹ ^ (4 : ℕ) * moment :=
      Finset.sum_le_sum fun k _ ↦ coordinate_tail _ (by positivity)
    _ = (ENNReal.ofReal (81/128 : ℝ))^n * moment := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
        Nat.cast_pow, Nat.cast_ofNat, ENNReal.ofReal_pow (by norm_num : (0:ℝ) ≤ 4/3),
        ENNReal.ofReal_div_of_pos (by norm_num : (0:ℝ) < 3), ENNReal.ofReal_ofNat,
        ← mul_assoc]
      rw [ENNReal.inv_pow, ← pow_mul, Nat.mul_comm n 4, pow_mul, ← mul_pow]
      have hq : (2 : ℝ≥0∞) * (4/3)⁻¹ ^ (4 : ℕ) = ENNReal.ofReal (81/128 : ℝ) := by
        have hreal : (2 : ℝ) * (4/3)⁻¹ ^ (4 : ℕ) = 81/128 := by norm_num
        rw [← hreal, ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2),
          ENNReal.ofReal_pow (by positivity), ENNReal.ofReal_inv_of_pos (by norm_num),
          ENNReal.ofReal_div_of_pos (by norm_num)]
        norm_num
      rw [hq]

lemma ae_eventually_coordinates_small : ∀ᵐ ω ∂law, ∀ᶠ n in atTop,
    ∀ k : Fin (2 ^ n), |ω (.inr ⟨n, k⟩)| < (4/3 : ℝ)^n := by
  have hs : (∑' n, law (badLevel n)) ≠ ∞ := by
    apply ne_top_of_le_ne_top _ (ENNReal.tsum_le_tsum badLevel_bound)
    rw [ENNReal.tsum_mul_right, ENNReal.tsum_geometric]
    apply ENNReal.mul_ne_top _ moment_ne_top
    simpa only [ENNReal.inv_ne_top] using
      (ne_of_gt (tsub_pos_of_lt (by rw [ENNReal.ofReal_lt_one]; norm_num : (ENNReal.ofReal (81/128 : ℝ)) < 1)))
  filter_upwards [ae_eventually_notMem hs] with ω hω
  filter_upwards [hω] with n hn
  simpa only [badLevel, Set.mem_ofPred_eq, not_exists, not_le] using hn

lemma decay_lt_one : (4/3 : ℝ) / Real.sqrt 2 < 1 := by
  have hp : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  rw [div_lt_one hp]
  nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]

lemma summable_level_bound : Summable (fun n : ℕ ↦ amplitude n * (4/3 : ℝ)^n) := by
  have h := (summable_geometric_of_lt_one (by positivity : 0 ≤ (4/3 : ℝ) / Real.sqrt 2)
    decay_lt_one).mul_left (1/2 : ℝ)
  have heq : (fun n : ℕ ↦ amplitude n * (4/3 : ℝ)^n) =
      (fun n : ℕ ↦ (1/2 : ℝ) * ((4/3 : ℝ) / Real.sqrt 2)^n) := by
    funext n
    simp only [amplitude, div_eq_mul_inv, mul_pow]
    ring
  rw [heq]
  exact h

lemma ae_summable_level : ∀ᵐ ω ∂law, Summable (fun n ↦ level n ω) := by
  filter_upwards [ae_eventually_coordinates_small] with ω hω
  apply summable_level_bound.of_norm_bounded_eventually_nat
  filter_upwards [hω] with n hn
  exact norm_level_le n ω (by positivity) (fun k ↦ (hn k).le)

open Complex in
lemma hasLaw_gaussian_of_ae_tendsto {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {X : ℕ → Ω → ℝ} {Y : Ω → ℝ}
    {m : ℕ → ℝ} {v : ℕ → ℝ≥0} {m₀ : ℝ} {v₀ : ℝ≥0}
    (hX : ∀ n, HasLaw (X n) (gaussianReal (m n) (v n)) P)
    (hY : ∀ᵐ ω ∂P, Tendsto (fun n ↦ X n ω) atTop (𝓝 (Y ω)))
    (hm : Tendsto m atTop (𝓝 m₀)) (hv : Tendsto v atTop (𝓝 v₀)) :
    HasLaw Y (gaussianReal m₀ v₀) P := by
  have hmY := aemeasurable_of_tendsto_metrizable_ae atTop (fun n ↦ (hX n).aemeasurable) hY
  refine ⟨hmY, Measure.ext_of_charFun (funext fun t ↦ ?_)⟩
  have : IsProbabilityMeasure (P.map Y) := by first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
  have hlim : Tendsto (fun n ↦ charFun (P.map (X n)) t) atTop
      (𝓝 (charFun (P.map Y) t)) := by
    have he (Z : Ω → ℝ) (hZ : AEMeasurable Z P) :
        charFun (P.map Z) t = ∫ ω, exp ((t * Z ω : ℝ) * I) ∂P := by
      rw [charFun_apply_real, integral_map hZ (by fun_prop)]
      simp only [ofReal_mul]
    simp_rw [he _ (hX _).aemeasurable, he _ hmY]
    apply tendsto_integral_of_dominated_convergence (fun _ ↦ (1 : ℝ))
    · intro n
      exact ((by fun_prop : Continuous (fun x : ℝ ↦ exp ((t * x : ℝ) * I))).measurable.comp_aemeasurable
        (hX n).aemeasurable).aestronglyMeasurable
    · exact integrable_const 1
    · intro n
      exact ae_of_all P fun ω ↦ le_of_eq (norm_exp_ofReal_mul_I _)
    · filter_upwards [hY] with ω hω
      exact continuous_exp.continuousAt.tendsto.comp
        ((continuous_ofReal.tendsto _ |>.comp (tendsto_const_nhds.mul hω)).mul_const I)
  have hlim' : Tendsto (fun n ↦ charFun (P.map (X n)) t) atTop
      (𝓝 (charFun (gaussianReal m₀ v₀) t)) := by
    simp_rw [(hX _).map_eq, charFun_gaussianReal]
    exact continuous_exp.continuousAt.tendsto.comp
      (((tendsto_const_nhds.mul (continuous_ofReal.tendsto _ |>.comp hm)).mul_const I).sub
        (((continuous_ofReal.tendsto _ |>.comp (NNReal.continuous_coe.tendsto _ |>.comp hv)).mul_const
          ((t : ℂ)^2)).div_const 2))
  exact tendsto_nhds_unique hlim hlim'

lemma hasLaw_centered_gaussian_sum {ι Ω : Type*} [Fintype ι] [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {X : ι → Ω → ℝ} {v : ι → ℝ≥0}
    (hX : ∀ i, HasLaw (X i) (gaussianReal 0 (v i)) P) (hind : iIndepFun X P) :
    HasLaw (fun ω ↦ ∑ i, X i ω) (gaussianReal 0 (∑ i, v i)) P := by
  classical
  have hg := hind.hasGaussianLaw_fun_sum (fun i ↦ (hX i).hasGaussianLaw)
  have hmean : ∫ ω, ∑ i, X i ω ∂P = 0 := by
    rw [integral_finsetSum _ (fun i _ ↦ (hX i).hasGaussianLaw.integrable)]
    simp only [(hX _).integral_eq, integral_id_gaussianReal, Finset.sum_const_zero]
  have hvar : Var[fun ω ↦ ∑ i, X i ω; P] = ∑ i, (v i : ℝ) := by
    have hh := IndepFun.variance_sum (s := Finset.univ)
      (fun i _ ↦ (hX i).hasGaussianLaw.memLp_two)
      (fun i _ j _ hij ↦ hind.indepFun hij)
    have he : (fun ω ↦ ∑ i, X i ω) = ∑ i, X i := by funext ω; simp
    rw [he]
    simpa only [(hX _).variance_eq, variance_id_gaussianReal] using hh
  refine ⟨hg.aemeasurable, ?_⟩
  rw [hg.map_eq_gaussianReal, hmean, hvar]
  simp only [← NNReal.coe_sum, Real.toNNReal_coe]

lemma sum_split_level (n : ℕ) (f : Fin (2^(n+1)) → ℝ) :
    ∑ k, f k = ∑ k, f (leftIndex n k) + ∑ k, f (rightIndex n k) := by
  let e : Fin (2^n + 2^n) ≃ Fin (2^(n+1)) :=
    finCongr (by simp [pow_succ, Nat.mul_two])
  rw [← Equiv.sum_comp e, Fin.sum_univ_add]
  rfl

lemma tent_left (n : ℕ) (k : Fin (2^n)) (s : ℝ) :
    tent (n+1) (leftIndex n k) s = tent n k (2*s) := by
  unfold tent leftIndex
  congr 3
  simp only [pow_succ]
  ring

lemma tent_right (n : ℕ) (k : Fin (2^n)) (s : ℝ) :
    tent (n+1) (rightIndex n k) s = tent n k (2*s-1) := by
  unfold tent rightIndex
  congr 3
  simp only [pow_succ, Nat.cast_add, Nat.cast_pow, Nat.cast_ofNat]
  ring

lemma tent_nonpos (n : ℕ) (k : Fin (2^n)) {s : ℝ} (hs : s ≤ 0) : tent n k s = 0 := by
  unfold tent
  apply max_eq_left
  have hpow : 0 ≤ (2:ℝ)^(n+1) := by positivity
  have hx : (2:ℝ)^(n+1)*s ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hpow hs
  rw [abs_of_nonpos (by linarith [show (0:ℝ) ≤ k by positivity])]
  linarith [show (0:ℝ) ≤ k by positivity]

lemma tent_ge_one (n : ℕ) (k : Fin (2^n)) {s : ℝ} (hs : 1 ≤ s) : tent n k s = 0 := by
  have hk : (k : ℝ) + 1 ≤ (2:ℝ)^n := by exact_mod_cast k.isLt
  have hp : 0 < (2:ℝ)^n := by positivity
  have hx : (2:ℝ)^n*2 ≤ (2:ℝ)^n*2*s := le_mul_of_one_le_right (by positivity) hs
  unfold tent
  simp only [pow_succ]
  rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ (2:ℝ)^n*2*s-(2*(k:ℝ)+1))]
  exact max_eq_left (by linarith)

lemma hatKernel_rec (n : ℕ) (s t : ℝ) :
    hatKernel (n+1) s t = hatKernel n (2*s) (2*t) + hatKernel n (2*s-1) (2*t-1) := by
  unfold hatKernel
  rw [sum_split_level]
  simp only [tent_left, tent_right]

lemma partialBridge_zero_left (n : ℕ) {s : ℝ} (hs : s ≤ 0 ∨ 1 ≤ s) (t : ℝ) :
    partialBridge n s t = 0 := by
  rcases hs with hs | hs <;> simp [partialBridge, hatKernel, tent_nonpos, tent_ge_one, hs]

lemma partialBridge_zero_right (n : ℕ) (s : ℝ) {t : ℝ} (ht : t ≤ 0 ∨ 1 ≤ t) :
    partialBridge n s t = 0 := by
  rcases ht with ht | ht <;> simp [partialBridge, hatKernel, tent_nonpos, tent_ge_one, ht]

lemma partialBridge_rec (n : ℕ) (s t : ℝ) :
    partialBridge (n+1) s t = (1/4 : ℝ) * tent 0 0 s * tent 0 0 t +
      (1/2 : ℝ)*(partialBridge n (2*s) (2*t) + partialBridge n (2*s-1) (2*t-1)) := by
  have h0 : hatKernel 0 s t = tent 0 0 s * tent 0 0 t := by
    simp [hatKernel]
  have hx : ∑ m ∈ Finset.range n, weight (m+1)*hatKernel (m+1) s t =
      (1/2 : ℝ)*(partialBridge n (2*s) (2*t) + partialBridge n (2*s-1) (2*t-1)) := by
    simp only [partialBridge, mul_add, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro m _
    rw [hatKernel_rec]
    simp only [weight, pow_succ]
    ring
  change (∑ m ∈ Finset.range (n+1), weight m * hatKernel m s t) = _
  rw [Finset.sum_range_succ', hx, h0]
  simp only [weight, pow_zero, mul_one]
  ring

lemma tent_zero_left {s : ℝ} (h0 : 0 ≤ s) (h1 : s ≤ 1/2) : tent 0 0 s = 2*s := by
  simp only [tent, pow_one, Fin.val_zero, Nat.cast_zero, mul_zero, zero_add]
  rw [abs_of_nonpos (by linarith), max_eq_right (by linarith)]
  ring

lemma tent_zero_right {s : ℝ} (h0 : 1/2 ≤ s) (h1 : s ≤ 1) : tent 0 0 s = 2*(1-s) := by
  simp only [tent, pow_one, Fin.val_zero, Nat.cast_zero, mul_zero, zero_add]
  rw [abs_of_nonneg (by linarith), max_eq_right (by linarith)]
  ring

lemma weight_step (n : ℕ) : weight (n+1) = (1/2 : ℝ)*weight n := by
  simp only [weight, pow_succ]
  ring

lemma abs_half_mul (x : ℝ) : |(1/2 : ℝ)*x| = (1/2 : ℝ)*|x| := by
  rw [abs_mul]
  norm_num

lemma partialBridge_error_ordered (n : ℕ) {s t : ℝ}
    (hs : 0 ≤ s) (ht : t ≤ 1) (hst : s ≤ t) :
    |partialBridge n s t - (s-s*t)| ≤ weight n := by
  induction n generalizing s t with
  | zero =>
      have hnn : 0 ≤ s-s*t := by nlinarith
      have hb : s-s*t ≤ (1/4 : ℝ) := by nlinarith [sq_nonneg (s-1/2)]
      simp only [partialBridge, Finset.range_zero, Finset.sum_empty, zero_sub,
        abs_neg, abs_of_nonneg hnn, weight, pow_zero, mul_one]
      exact hb
  | succ n ih =>
      rw [partialBridge_rec, weight_step]
      by_cases ht2 : t ≤ 1/2
      · have hs2 : s ≤ 1/2 := hst.trans ht2
        rw [tent_zero_left hs hs2, tent_zero_left (hs.trans hst) ht2,
          partialBridge_zero_left n (Or.inl (by linarith : 2*s-1 ≤ 0)), add_zero]
        have hh := ih (s := 2*s) (t := 2*t) (by linarith) (by linarith) (by linarith)
        calc
          _ = (1/2 : ℝ)*|partialBridge n (2*s) (2*t) - (2*s-(2*s)*(2*t))| := by
            rw [← abs_half_mul]
            congr 1
            ring
          _ ≤ _ := mul_le_mul_of_nonneg_left hh (by norm_num)
      · by_cases hs2 : 1/2 ≤ s
        · rw [tent_zero_right hs2 (hst.trans ht), tent_zero_right (hs2.trans hst) ht,
            partialBridge_zero_left n (Or.inr (by linarith : 1 ≤ 2*s)), zero_add]
          have hh := ih (s := 2*s-1) (t := 2*t-1) (by linarith) (by linarith) (by linarith)
          calc
            _ = (1/2 : ℝ)*|partialBridge n (2*s-1) (2*t-1) - ((2*s-1)-(2*s-1)*(2*t-1))| := by
              rw [← abs_half_mul]
              congr 1
              ring
            _ ≤ _ := mul_le_mul_of_nonneg_left hh (by norm_num)
        · rw [tent_zero_left hs (by linarith), tent_zero_right (by linarith) ht,
            partialBridge_zero_right n _ (Or.inr (by linarith : 1 ≤ 2*t)),
            partialBridge_zero_left n (Or.inl (by linarith : 2*s-1 ≤ 0))]
          have he : (1/4 : ℝ)*(2*s)*(2*(1-t)) + (1/2)*(0+0) - (s-s*t) = 0 := by ring
          rw [he, abs_zero]
          unfold weight
          positivity

end HardSphere.Wiener
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Bridges_PartialIndex
attribute [-instance] _root_.OAI.HardSphere.Bridge.exposedBridgeKernel_markov _root_.OAI.HardSphere.Bridge.exposedPeriodSingle_finite _root_.OAI.HardSphere.Bridge.exposedTrialKernel_markov _root_.OAI.HardSphere.Bridge.instBorelSpaceContinuousMapElemRealTimePoint _root_.OAI.HardSphere.Bridge.instIsProbabilityMeasureNoiseLaw _root_.OAI.HardSphere.Bridge.instMeasurableSpaceContinuousMapElemRealTimePoint _root_.OAI.HardSphere.Bridge.parameterBridgeKernel_markov _root_.OAI.HardSphere.Bridge.parameterIndividualReference_finite _root_.OAI.HardSphere.Bridge.parameterTrialKernel_markov _root_.OAI.HardSphere.Bridge.trialKernel_markov _root_.OAI.HardSphere.Groups.cellPathReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.configurationPathBorel _root_.OAI.HardSphere.coordinateBridge_probability _root_.OAI.HardSphere.coordinateWiener_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
noncomputable section
open scoped BigOperators ComplexConjugate
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.Wiener

lemma partialBridge_symm (n : ℕ) (s t : ℝ) : partialBridge n s t = partialBridge n t s := by
  simp only [partialBridge, hatKernel, mul_comm (tent _ _ s) (tent _ _ t)]

lemma partialBridge_error (n : ℕ) {s t : ℝ}
    (hs : s ∈ Set.Icc (0:ℝ) 1) (ht : t ∈ Set.Icc (0:ℝ) 1) :
    |partialBridge n s t - (min s t-s*t)| ≤ weight n := by
  rcases le_total s t with hst | hts
  · rw [min_eq_left hst]
    exact partialBridge_error_ordered n hs.1 ht.2 hst
  · rw [partialBridge_symm, min_eq_right hts, mul_comm s t]
    exact partialBridge_error_ordered n ht.1 hs.2 hts

lemma partialBridge_tendsto {s t : ℝ}
    (hs : s ∈ Set.Icc (0:ℝ) 1) (ht : t ∈ Set.Icc (0:ℝ) 1) :
    Filter.Tendsto (fun n ↦ partialBridge n s t) Filter.atTop (𝓝 (min s t-s*t)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (fun n ↦ norm_nonneg _) (fun n ↦ partialBridge_error n hs ht)
  change Filter.Tendsto (fun n ↦ weight n) Filter.atTop (𝓝 0)
  simpa only [weight, mul_zero] using
    (tendsto_const_nhds.mul
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ) ≤ 1/2)
        (by norm_num : (1/2:ℝ) < 1)) :
      Filter.Tendsto (fun n ↦ (1/4:ℝ)*(1/2:ℝ)^n) Filter.atTop (𝓝 ((1/4:ℝ)*0)))

lemma partialEmbed_injective (n : ℕ) : Function.Injective (partialEmbed n) := by
  intro i j hij
  cases i with
  | inl u =>
    cases j with
    | inl v => exact congrArg Sum.inl (Subsingleton.elim _ _)
    | inr j => cases hij
  | inr i =>
    cases j with
    | inl u => cases hij
    | inr j =>
      obtain ⟨m,k⟩ := i
      obtain ⟨l,q⟩ := j
      simp only [partialEmbed, Sum.inr.injEq] at hij
      cases m; cases l
      cases hij
      rfl

lemma partialPath_expansion (n : ℕ) (t : Time) (ω : Noise) :
    partialPath n ω t = ∑ i : PartialIndex n, coefficient n t i * ω (partialEmbed n i) := by
  simp only [Fintype.sum_sum_type, Fintype.sum_sigma, coefficient, partialEmbed,
    Fintype.sum_unique, partialPath, ContinuousMap.add_apply, ContinuousMap.smul_apply,
    ContinuousMap.coe_mk, smul_eq_mul, ContinuousMap.sum_apply, level, tentMap,
    ← Finset.mul_sum]
  rw [Fin.sum_univ_eq_sum_range (fun m ↦ ∑ k : Fin (2^m),
    amplitude m * tent m k t * ω (.inr ⟨m,k⟩)) n]
  congr 1
  · ring
  · apply Finset.sum_congr rfl
    intro m _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    ring

lemma coefficient_covariance (n : ℕ) (s t : ℝ) :
    ∑ i : PartialIndex n, coefficient n s i * coefficient n t i =
      s*t + partialBridge n s t := by
  have hamp (m : ℕ) : amplitude m ^ 2 = weight m := by
    have hs : (Real.sqrt 2)^2 = (2:ℝ) := Real.sq_sqrt (by norm_num)
    simp only [amplitude, mul_pow, weight]
    rw [← pow_mul, Nat.mul_comm m 2, pow_mul, inv_pow, hs]
    norm_num
  simp only [Fintype.sum_sum_type, Fintype.sum_sigma, coefficient, Fintype.sum_unique]
  rw [Fin.sum_univ_eq_sum_range (fun m ↦ ∑ k : Fin (2^m),
    amplitude m * tent m k s * (amplitude m * tent m k t)) n]
  congr 1
  unfold partialBridge
  apply Finset.sum_congr rfl
  intro m _
  rw [hatKernel, Finset.mul_sum, ← hamp]
  apply Finset.sum_congr rfl
  intro k _
  ring

lemma independent_coordinates : iIndepFun (fun i ω ↦ ω i) law :=
  iIndepFun_infinitePi (fun _ ↦ measurable_id)

lemma finite_coordinate_law (n : ℕ) (c : PartialIndex n → ℝ) :
    HasLaw (fun ω ↦ ∑ i, c i * ω (partialEmbed n i))
      (gaussianReal 0 (∑ i, NNReal.mk ((c i)^2) (sq_nonneg _))) law := by
  have hh (i : PartialIndex n) : HasLaw (fun ω ↦ c i * ω (partialEmbed n i))
      (gaussianReal 0 (NNReal.mk ((c i)^2) (sq_nonneg _))) law := by
    simpa only [mul_zero, mul_one] using
      gaussianReal_const_mul (coordinate_preserving (partialEmbed n i)).hasLaw (c i)
  exact hasLaw_centered_gaussian_sum hh
    ((independent_coordinates.precomp (partialEmbed_injective n)).comp
      (fun i x ↦ c i*x) (fun i ↦ by fun_prop))

lemma square_sum_covariance {ι κ : Type*} [Fintype ι] [Fintype κ]
    (c : ι → ℝ) (f : ι → κ → ℝ) :
    ∑ u, (∑ i, c i*f i u)^2 = ∑ i, ∑ j, c i*c j*(∑ u, f i u*f j u) := by
  simp only [pow_two, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro u _
  ring

lemma ae_partialPath_tendsto : ∀ᵐ ω ∂law,
    Tendsto (fun n ↦ partialPath n ω) atTop (𝓝 (path ω)) := by
  filter_upwards [ae_summable_level] with ω hω
  exact tendsto_const_nhds.add hω.hasSum.tendsto_sum_nat

lemma finite_projection_expansion {ι : Type*} [Fintype ι]
    (n : ℕ) (c : ι → ℝ) (t : ι → Time) (ω : Noise) :
    ∑ i, c i * partialPath n ω (t i) =
      ∑ u : PartialIndex n, (∑ i, c i * coefficient n (t i) u) * ω (partialEmbed n u) := by
  simp_rw [partialPath_expansion, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u _
  apply Finset.sum_congr rfl
  intro i _
  ring

lemma finite_projection_variance {ι : Type*} [Fintype ι]
    (n : ℕ) (c : ι → ℝ) (t : ι → Time) :
    ∑ u : PartialIndex n, (∑ i, c i * coefficient n (t i) u)^2 =
      ∑ i, ∑ j, c i*c j*((t i : ℝ)*(t j : ℝ)+partialBridge n (t i) (t j)) := by
  rw [square_sum_covariance]
  simp_rw [coefficient_covariance]

lemma finite_projection_law {ι : Type*} [Fintype ι]
    (n : ℕ) (c : ι → ℝ) (t : ι → Time) :
    HasLaw (fun ω ↦ ∑ i, c i * partialPath n ω (t i))
      (gaussianReal 0 (Real.toNNReal
        (∑ i, ∑ j, c i*c j*((t i : ℝ)*(t j : ℝ)+partialBridge n (t i) (t j))))) law := by
  have hh := finite_coordinate_law n (fun u ↦ ∑ i, c i * coefficient n (t i) u)
  simp_rw [finite_projection_expansion]
  convert hh using 2
  all_goals try with_reducible_and_instances rfl
  rw [← finite_projection_variance]
  change Real.toNNReal (∑ u : PartialIndex n,
    ((NNReal.mk ((∑ i, c i * coefficient n (t i) u)^2) (sq_nonneg _) : ℝ≥0) : ℝ)) = _
  rw [← NNReal.coe_sum, Real.toNNReal_coe]

lemma path_projection_law {ι : Type*} [Fintype ι]
    (c : ι → ℝ) (t : ι → Time) :
    HasLaw (fun ω ↦ ∑ i, c i * path ω (t i))
      (gaussianReal 0 (Real.toNNReal (∑ i, ∑ j, c i*c j*min (t i : ℝ) (t j : ℝ)))) law := by
  refine hasLaw_gaussian_of_ae_tendsto (fun n ↦ finite_projection_law n c t) ?_
    tendsto_const_nhds ?_
  · filter_upwards [ae_partialPath_tendsto] with ω hω
    apply tendsto_finsetSum
    intro i _
    exact tendsto_const_nhds.mul ((continuous_eval_const (t i)).tendsto _ |>.comp hω)
  · apply continuous_real_toNNReal.tendsto _ |>.comp
    apply tendsto_finsetSum
    intro i _
    apply tendsto_finsetSum
    intro j _
    have hh := ((tendsto_const_nhds (x := (t i : ℝ)*(t j : ℝ))).add
      (partialBridge_tendsto (t i).property (t j).property)).const_mul (c i*c j)
    convert hh using 1
    all_goals try with_reducible_and_instances rfl
    congr 1
    ring

lemma finite_linear_projection {ι : Type*} [Fintype ι] [DecidableEq ι]
    (L : (ι → ℝ) →L[ℝ] ℝ) (x : ι → ℝ) :
    L x = ∑ i, L (Pi.single i 1) * x i := by
  conv_lhs => rw [pi_eq_sum_univ' x]
  simp only [map_sum, map_smul, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i _
  ring

lemma finite_path_gaussian {ι : Type*} [Fintype ι] (t : ι → Time) :
    HasGaussianLaw (fun ω i ↦ path ω (t i)) law := by
  classical
  have hm : Measurable (fun ω i ↦ path ω (t i)) :=
    Measurable.of_eval fun coordinate ↦
      (continuous_eval_const (t coordinate)).measurable.comp measurable_path
  refine ⟨?_⟩
  apply isGaussian_of_map_eq_gaussianReal
  intro L
  refine ⟨0, Real.toNNReal (∑ i, ∑ j,
    L (Pi.single i 1)*L (Pi.single j 1)*min (t i : ℝ) (t j : ℝ)), ?_⟩
  rw [Measure.map_map L.continuous.measurable hm]
  convert (path_projection_law (fun i ↦ L (Pi.single i 1)) t).map_eq using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  funext ω
  exact finite_linear_projection L _

lemma path_eval_law (t : Time) :
    HasLaw (fun ω ↦ path ω t) (gaussianReal 0 (Real.toNNReal t.val)) law := by
  simpa using path_projection_law (fun _ : Unit ↦ (1:ℝ)) (fun _ ↦ t)

lemma path_variance (t : Time) : Var[fun ω ↦ path ω t; law] = t.val := by
  rw [(path_eval_law t).variance_eq, variance_id_gaussianReal, Real.coe_toNNReal _ t.property.1]

lemma path_add_law (s t : Time) :
    HasLaw (fun ω ↦ path ω s + path ω t)
      (gaussianReal 0 ((s:ℝ)+(t:ℝ)+2*min (s:ℝ) (t:ℝ)).toNNReal) law := by
  have hh := path_projection_law (fun _ : Bool ↦ (1:ℝ)) (fun b ↦ if b then s else t)
  simp only [Fintype.sum_bool, Bool.false_eq_true, ↓reduceIte, mul_one, one_mul, min_self] at hh
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  congr 1
  rw [min_comm (t:ℝ) (s:ℝ)]
  ring

lemma path_covariance (s t : Time) :
    cov[fun ω ↦ path ω s, fun ω ↦ path ω t; law] = min (s:ℝ) (t:ℝ) := by
  have hs : 0 ≤ (s:ℝ) := s.property.1
  have ht : 0 ≤ (t:ℝ) := t.property.1
  have hmin : 0 ≤ min (s:ℝ) (t:ℝ) := le_min hs ht
  have hvar := variance_fun_add (path_eval_law s).hasGaussianLaw.memLp_two
    (path_eval_law t).hasGaussianLaw.memLp_two
  rw [path_variance s, path_variance t, (path_add_law s t).variance_eq,
    variance_id_gaussianReal, Real.coe_toNNReal _ (by positivity)] at hvar
  linarith

lemma denseEval_embedding : MeasurableEmbedding denseEval := by
  apply Measurable.measurableEmbedding
  · exact Measurable.of_eval fun _ ↦ (continuous_eval_const _).measurable
  · intro f g h
    apply DFunLike.coe_injective
    exact (TopologicalSpace.denseRange_denseSeq Time).equalizer f.continuous g.continuous h

lemma continuous_path_law_ext {X Y : Noise → C(Time,ℝ)}
    (hX : Measurable X) (hY : Measurable Y)
    (h : ∀ {ι : Type} [Fintype ι] (c : ι → ℝ) (t : ι → Time),
      law.map (fun ω ↦ ∑ i, c i * X ω (t i)) =
        law.map (fun ω ↦ ∑ i, c i * Y ω (t i))) :
    law.map X = law.map Y := by
  apply denseEval_embedding.map_injective
  rw [Measure.map_map denseEval_embedding.measurable hX,
    Measure.map_map denseEval_embedding.measurable hY]
  apply (map_eq_iff_forall_finset_map_restrict_eq
    (denseEval_embedding.measurable.comp hX).aemeasurable
    (denseEval_embedding.measurable.comp hY).aemeasurable).mpr
  intro I
  apply Measure.ext_of_charFunDual
  funext L
  rw [charFunDual_eq_charFun_map_one, charFunDual_eq_charFun_map_one]
  congr 1
  have hXm : Measurable (fun ω ↦ I.restrict (fun x ↦ denseEval (X ω) x)) :=
    Measurable.of_eval fun coordinate ↦ (measurable_pi_apply coordinate.val).comp
      (denseEval_embedding.measurable.comp hX)
  have hYm : Measurable (fun ω ↦ I.restrict (fun x ↦ denseEval (Y ω) x)) :=
    Measurable.of_eval fun coordinate ↦ (measurable_pi_apply coordinate.val).comp
      (denseEval_embedding.measurable.comp hY)
  simp only [Function.comp_def, Finset.restrict_def] at hXm hYm ⊢
  rw [Measure.map_map L.continuous.measurable hXm,
    Measure.map_map L.continuous.measurable hYm]
  convert h (fun i : I ↦ L (Pi.single i 1))
    (fun i : I ↦ TopologicalSpace.denseSeq Time i.val) using 1 <;>
    congr 1 <;> funext ω <;> exact finite_linear_projection L _

end HardSphere.Wiener
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Bridges_PrefixMap
attribute [-instance] _root_.OAI.HardSphere.Bridge.exposedBridgeKernel_markov _root_.OAI.HardSphere.Bridge.exposedPeriodSingle_finite _root_.OAI.HardSphere.Bridge.exposedTrialKernel_markov _root_.OAI.HardSphere.Bridge.instBorelSpaceContinuousMapElemRealTimePoint _root_.OAI.HardSphere.Bridge.instIsProbabilityMeasureNoiseLaw _root_.OAI.HardSphere.Bridge.instMeasurableSpaceContinuousMapElemRealTimePoint _root_.OAI.HardSphere.Bridge.parameterBridgeKernel_markov _root_.OAI.HardSphere.Bridge.parameterIndividualReference_finite _root_.OAI.HardSphere.Bridge.parameterTrialKernel_markov _root_.OAI.HardSphere.Bridge.trialKernel_markov _root_.OAI.HardSphere.Groups.cellPathReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.configurationPathBorel _root_.OAI.HardSphere.coordinateBridge_probability _root_.OAI.HardSphere.coordinateWiener_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.Wiener

lemma prefixTime_le (u t : Time) : (prefixTime u t:ℝ) ≤ u := by
  change (u:ℝ)*(t:ℝ) ≤ u
  nlinarith [u.property.1,t.property.2]
lemma le_suffixTime (u t : Time) : (u:ℝ) ≤ suffixTime u t := by
  change (u:ℝ) ≤ (u:ℝ)+(1-(u:ℝ))*(t:ℝ)
  nlinarith [u.property.2,t.property.1]

lemma split_gaussian (u : Time) :
    IsGaussianProcess (Sum.elim (fun t ω ↦ prefixMap u (path ω) t)
      (fun t ω ↦ suffixMap u (path ω) t)) law := by
  classical
  constructor
  intro I
  let loc : Option I → Time := fun i ↦ i.elim u
    (fun j ↦ j.val.elim (prefixTime u) (suffixTime u))
  let ev (i : Option I) : (Option I → ℝ) →L[ℝ] ℝ := ContinuousLinearMap.proj i
  let L : (Option I → ℝ) →L[ℝ] (I → ℝ) :=
    ContinuousLinearMap.pi (fun i ↦ match i.val with
      | .inl _ => ev (some i)
      | .inr _ => ev (some i) - ev none)
  convert! (finite_path_gaussian loc).map_fun L using 1
  all_goals try with_reducible_and_instances rfl
  funext ω i
  cases hi : i.val <;> simp [L,loc,hi,ev]

lemma independent_split (u : Time) :
    IndepFun (fun ω ↦ prefixMap u (path ω)) (fun ω ↦ suffixMap u (path ω)) law := by
  have hc (s t : Time) :
      cov[fun ω ↦ prefixMap u (path ω) s, fun ω ↦ suffixMap u (path ω) t; law] = 0 := by
    simp only [prefixMap_apply,suffixMap_apply]
    rw [covariance_fun_sub_right
      (path_eval_law _).hasGaussianLaw.memLp_two
      (path_eval_law _).hasGaussianLaw.memLp_two
      (path_eval_law _).hasGaussianLaw.memLp_two,
      path_covariance,path_covariance,
      min_eq_left ((prefixTime_le u s).trans (le_suffixTime u t)),
      min_eq_left (prefixTime_le u s),sub_self]
  have hi := (split_gaussian u).indepFun_of_covariance_eq_zero
    (fun t ↦ ((continuous_eval_const t).measurable.comp
      ((prefixMap u).continuous.measurable.comp measurable_path)).aemeasurable)
    (fun t ↦ ((continuous_eval_const t).measurable.comp
      ((suffixMap u).continuous.measurable.comp measurable_path)).aemeasurable) hc
  have hid := hi.comp
    (Measurable.of_eval fun index ↦ measurable_pi_apply (TopologicalSpace.denseSeq Time index))
    (Measurable.of_eval fun index ↦ measurable_pi_apply (TopologicalSpace.denseSeq Time index))
  have hh := hid.comp denseEval_embedding.measurable_invFun denseEval_embedding.measurable_invFun
  convert hh using 1 <;> funext ω <;>
    exact (denseEval_embedding.leftInverse_invFun _).symm

lemma scaled_path_projection_law {ι : Type*} [Fintype ι]
    (r : ℝ) (hr : 0 ≤ r) (c : ι → ℝ) (t : ι → Time) :
    HasLaw (fun ω ↦ ∑ i, c i * (Real.sqrt r • path ω) (t i))
      (gaussianReal 0 (Real.toNNReal (r * ∑ i, ∑ j,
        c i*c j*min (t i:ℝ) (t j:ℝ)))) law := by
  have hh := path_projection_law (fun i ↦ c i * Real.sqrt r) t
  convert hh using 1
  · funext ω
    apply Finset.sum_congr rfl
    intro i _
    simp only [ContinuousMap.smul_apply,smul_eq_mul]
    ring
  · congr 1
    congr 1
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    calc
      r * (c i*c j*min (t i:ℝ) (t j:ℝ)) =
          Real.sqrt r ^ 2 * (c i*c j*min (t i:ℝ) (t j:ℝ)) := by rw [Real.sq_sqrt hr]
      _ = _ := by ring

lemma prefix_law (u : Time) :
    law.map (fun ω ↦ prefixMap u (path ω)) =
      law.map (fun ω ↦ Real.sqrt (u:ℝ) • path ω) := by
  apply continuous_path_law_ext (X := fun ω ↦ prefixMap u (path ω))
    (Y := fun ω ↦ Real.sqrt (u:ℝ) • path ω)
    ((prefixMap u).continuous.measurable.comp measurable_path)
    ((show Measurable (fun f : C(Time,ℝ) ↦ Real.sqrt (u:ℝ) • f) from
      (by fun_prop)).comp measurable_path)
  intro ι _ c t
  have h := path_projection_law c (fun i ↦ prefixTime u (t i))
  have hvar : (∑ i, ∑ j, c i*c j*min (prefixTime u (t i):ℝ) (prefixTime u (t j):ℝ)) =
      (u:ℝ)*∑ i, ∑ j, c i*c j*min (t i:ℝ) (t j:ℝ) := by
    simp only [prefixTime,ContinuousMap.coe_mk]
    simp_rw [← mul_min_of_nonneg _ _ u.property.1]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hvar] at h
  exact h.map_eq.trans (scaled_path_projection_law _ u.property.1 c t).map_eq.symm

lemma suffix_projection_algebra {ι : Type*} [Fintype ι]
    (u : Time) (c : ι → ℝ) (t : ι → Time) :
    let a : Option ι → ℝ := fun i ↦ i.elim (-∑ i, c i) c
    let v : Option ι → Time := fun i ↦ i.elim u (fun j ↦ suffixTime u (t j))
    (∑ i, ∑ j, a i*a j*min (v i:ℝ) (v j:ℝ)) =
      (1-(u:ℝ))*∑ i, ∑ j, c i*c j*min (t i:ℝ) (t j:ℝ) := by
  let A : ℝ := ∑ i, c i
  have hh : (∑ i, ∑ j, c i*c j*(u:ℝ)) = A*A*(u:ℝ) := by
    dsimp only [A]
    rw [Finset.sum_mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_mul]
  have h1 : (∑ i, (-A)*c i*(u:ℝ)) = -A*A*(u:ℝ) := by
    rw [← Finset.sum_mul, ← Finset.mul_sum]
  have h2 : (∑ i, c i*(-A)*(u:ℝ)) = -A*A*(u:ℝ) := by
    rw [← Finset.sum_mul, ← Finset.sum_mul]
    dsimp only [A]
    ring
  have h3 : (∑ i, ∑ j, c i*c j*((1-(u:ℝ))*min (t i:ℝ) (t j:ℝ))) =
      (1-(u:ℝ))*∑ i, ∑ j, c i*c j*min (t i:ℝ) (t j:ℝ) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  dsimp only
  simp only [Fintype.sum_option,Option.elim_none,Option.elim_some,
    min_self,min_eq_left (le_suffixTime u (t _)),min_eq_right (le_suffixTime u (t _))]
  have ht i j : min (suffixTime u (t i):ℝ) (suffixTime u (t j):ℝ) =
      (u:ℝ)+(1-(u:ℝ))*min (t i:ℝ) (t j:ℝ) := by
    change min ((u:ℝ)+(1-(u:ℝ))*(t i:ℝ)) ((u:ℝ)+(1-(u:ℝ))*(t j:ℝ)) = _
    rw [min_add_add_left,← mul_min_of_nonneg _ _ (sub_nonneg.mpr u.property.2)]
  simp_rw [ht,mul_add,Finset.sum_add_distrib]
  change (-A)*(-A)*(u:ℝ)+(∑ i,(-A)*c i*(u:ℝ))+
    ((∑ i,c i*(-A)*(u:ℝ))+((∑ i,∑ j,c i*c j*(u:ℝ))+_)) = _
  rw [hh,h1,h2,h3]
  ring

lemma suffix_law (u : Time) :
    law.map (fun ω ↦ suffixMap u (path ω)) =
      law.map (fun ω ↦ Real.sqrt (1-(u:ℝ)) • path ω) := by
  apply continuous_path_law_ext (X := fun ω ↦ suffixMap u (path ω))
    (Y := fun ω ↦ Real.sqrt (1-(u:ℝ)) • path ω)
    ((suffixMap u).continuous.measurable.comp measurable_path)
    ((show Measurable (fun f : C(Time,ℝ) ↦ Real.sqrt (1-(u:ℝ)) • f) from
      (by fun_prop)).comp measurable_path)
  intro ι _ c t
  have hh := path_projection_law (fun i : Option ι ↦ i.elim (-∑ i,c i) c)
    (fun i ↦ i.elim u (fun j ↦ suffixTime u (t j)))
  rw [suffix_projection_algebra] at hh
  have heq : (fun ω ↦ ∑ i, c i*suffixMap u (path ω) (t i)) =
      (fun ω ↦ ∑ i : Option ι, i.elim (-∑ i,c i) c *
        path ω (i.elim u (fun j ↦ suffixTime u (t j)))) := by
    funext ω
    simp only [Fintype.sum_option,Option.elim_none,Option.elim_some,suffixMap_apply,
      mul_sub,Finset.sum_sub_distrib,neg_mul,Finset.sum_mul]
    ring
  rw [heq, hh.map_eq,
    (scaled_path_projection_law _ (sub_nonneg.mpr u.property.2) c t).map_eq]

lemma split_path_law (u : Time) :
    law.map (fun ω ↦ (prefixMap u (path ω),suffixMap u (path ω))) =
      (wiener.map (fun f ↦ Real.sqrt (u:ℝ) • f)).prod
        (wiener.map (fun f ↦ Real.sqrt (1-(u:ℝ)) • f)) := by
  calc
    _ = (law.map (fun ω ↦ prefixMap u (path ω))).prod
        (law.map (fun ω ↦ suffixMap u (path ω))) := by
      simpa only [Function.comp_def] using (independent_split u).map_prod_eq_prod_map_map
        ((prefixMap u).continuous.measurable.comp measurable_path).aemeasurable
        ((suffixMap u).continuous.measurable.comp measurable_path).aemeasurable
    _ = _ := by
      rw [prefix_law,suffix_law]
      unfold wiener
      rw [Measure.map_map (show Measurable (fun f : C(Time,ℝ) ↦ Real.sqrt (u:ℝ) • f) from by fun_prop) measurable_path,
        Measure.map_map (show Measurable (fun f : C(Time,ℝ) ↦ Real.sqrt (1-(u:ℝ)) • f) from by fun_prop) measurable_path]
      rfl

end HardSphere.Wiener

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_FormDomain_Energy
attribute [-instance] _root_.OAI.HardSphere.Groups.labelOptionSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
noncomputable section
open scoped BigOperators ComplexConjugate
namespace HardSphere.Variational
variable {H J : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [Fintype J]

omit [InnerProductSpace ℂ H] in
lemma energy_nonneg (u : H × (J → H)) : 0 ≤ energy u :=
  Finset.sum_nonneg fun _ _ ↦ sq_nonneg _

lemma energy_smul (c : ℂ) (u : H × (J → H)) :
    energy (c • u) = ‖c‖ ^ 2 * energy u := by
  simp [energy, norm_smul, mul_pow, Finset.mul_sum]

theorem rayleigh (M : Submodule ℂ (H × (J → H))) (u : H × (J → H))
    (hmin : ∀ v ∈ M, ‖v.1‖ = 1 → energy u ≤ energy v)
    (v : H × (J → H)) (hv : v ∈ M) :
    energy u * ‖v.1‖ ^ 2 ≤ energy v := by
  by_cases hz : ‖v.1‖ = 0
  · simpa [hz] using energy_nonneg v
  · let c : ℂ := ((‖v.1‖ : ℂ))⁻¹
    have hc : ‖c‖ = ‖v.1‖⁻¹ := by simp [c, Complex.norm_real]
    have hv' : ‖(c • v).1‖ = 1 := by
      simp only [Prod.smul_fst, norm_smul, hc]
      exact inv_mul_cancel₀ hz
    have h := hmin (c • v) (M.smul_mem c hv) hv'
    rw [energy_smul, hc] at h
    calc
      energy u * ‖v.1‖ ^ 2 ≤ (‖v.1‖⁻¹ ^ 2 * energy v) * ‖v.1‖ ^ 2 :=
        mul_le_mul_of_nonneg_right h (sq_nonneg _)
      _ = energy v := by field_simp

lemma norm_add_real_smul_sq (x y : H) (t : ℝ) :
    ‖x + (t : ℂ) • y‖ ^ 2 =
      ‖x‖ ^ 2 + 2 * t * (inner ℂ x y).re + t ^ 2 * ‖y‖ ^ 2 := by
  rw [norm_add_sq (𝕜 := ℂ), inner_smul_right, norm_smul, mul_pow]
  simp [Complex.norm_real, sq_abs, mul_assoc]

lemma energy_add_real_smul (u v : H × (J → H)) (t : ℝ) :
    energy (u + (t : ℂ) • v) =
      energy u + 2 * t * (gradientPairing u v).re + t ^ 2 * energy v := by
  change (∑ i, ‖u.2 i + (t : ℂ) • v.2 i‖ ^ 2) = _
  simp_rw [norm_add_real_smul_sq]
  simp only [energy, gradientPairing, Finset.sum_add_distrib, Finset.mul_sum,
    Complex.re_sum]

lemma linear_term_zero {a b : ℝ} (ha : 0 ≤ a)
    (h : ∀ t : ℝ, 0 ≤ a * t ^ 2 + 2 * b * t) : b = 0 := by
  have hd : 0 < a + 1 := by linarith
  have hh := mul_nonneg (h (-b / (a + 1))) (sq_nonneg (a + 1))
  have heq : (a * (-b / (a + 1)) ^ 2 + 2 * b * (-b / (a + 1))) *
      (a + 1) ^ 2 = -(a + 2) * b ^ 2 := by
    field_simp
    ring
  rw [heq] at hh
  have hb := sq_nonneg b
  have hprod := mul_nonneg ha hb
  nlinarith

theorem ground_pairing (M : Submodule ℂ (H × (J → H)))
    (u : H × (J → H)) (hu : u ∈ M) (hnorm : ‖u.1‖ = 1)
    (hmin : ∀ v ∈ M, ‖v.1‖ = 1 → energy u ≤ energy v)
    (v : H × (J → H)) (hv : v ∈ M) :
    gradientPairing u v = (energy u : ℂ) * inner ℂ u.1 v.1 := by
  have hre (w : H × (J → H)) (hw : w ∈ M) :
      (gradientPairing u w).re = energy u * (inner ℂ u.1 w.1).re := by
    have ha : 0 ≤ energy w - energy u * ‖w.1‖ ^ 2 :=
      sub_nonneg.mpr (rayleigh M u hmin w hw)
    have hpoly (t : ℝ) : 0 ≤
        (energy w - energy u * ‖w.1‖ ^ 2) * t ^ 2 +
          2 * ((gradientPairing u w).re - energy u * (inner ℂ u.1 w.1).re) * t := by
      have h := rayleigh M u hmin (u + (t : ℂ) • w) (M.add_mem hu (M.smul_mem _ hw))
      rw [energy_add_real_smul] at h
      simp only [Prod.fst_add, Prod.smul_fst, norm_add_real_smul_sq, hnorm, one_pow] at h
      nlinarith
    exact sub_eq_zero.mp (linear_term_zero ha hpoly)
  have hI := hre (Complex.I • v) (M.smul_mem _ hv)
  have hr := hre v hv
  apply Complex.ext
  · simpa using hr
  · simpa [gradientPairing, inner_smul_right, ← Finset.mul_sum, Complex.mul_re,
      Complex.I_re, Complex.I_im, Complex.mul_im] using hI

end HardSphere.Variational

end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_FormDomain_EnergyParallelogram
attribute [-instance] _root_.OAI.HardSphere.Groups.labelOptionSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
noncomputable section
open scoped BigOperators ComplexConjugate
namespace HardSphere.Variational
variable {H J : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [Fintype J]

lemma energy_parallelogram (u v : H × (J → H)) :
    energy (u + v) + energy (u - v) = 2 * (energy u + energy v) := by
  change (∑ i, ‖u.2 i + v.2 i‖ ^ 2) + (∑ i, ‖u.2 i - v.2 i‖ ^ 2) = _
  rw [← Finset.sum_add_distrib]
  simp_rw [parallelogram_law_with_norm ℂ]
  simp only [energy, Finset.mul_sum, Finset.sum_add_distrib, mul_add]

theorem minimizer_eq_of_scalar_eq (M : Submodule ℂ (H × (J → H)))
    (u : H × (J → H)) (hu : u ∈ M) (hnorm : ‖u.1‖ = 1)
    (hmin : ∀ v ∈ M, ‖v.1‖ = 1 → energy u ≤ energy v)
    (v : H × (J → H)) (hv : v ∈ M) (hscalar : v.1 = u.1)
    (henergy : energy v ≤ energy u) : v = u := by
  have hnormsum : ‖(u + v).1‖ ^ 2 = 4 := by
    have he : (u + v).1 = (2 : ℂ) • u.1 := by simp [hscalar, two_smul]
    rw [he, norm_smul, hnorm]
    norm_num
  have hr := rayleigh M u hmin (u + v) (M.add_mem hu hv)
  rw [hnormsum] at hr
  have hd : energy (u - v) = 0 := by
    have hp := energy_parallelogram u v
    have hn := energy_nonneg (u - v)
    linarith
  apply Prod.ext hscalar
  funext i
  have hi : ‖u.2 i - v.2 i‖ ^ 2 ≤ energy (u - v) :=
    Finset.single_le_sum (fun j _ ↦ sq_nonneg ‖u.2 j - v.2 j‖) (Finset.mem_univ i)
  rw [hd] at hi
  have hz : ‖u.2 i - v.2 i‖ = 0 := by nlinarith [norm_nonneg (u.2 i - v.2 i)]
  exact (sub_eq_zero.mp (norm_eq_zero.mp hz)).symm

end HardSphere.Variational

end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_FormDomain_Basic
attribute [-instance] _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Rescaling.config_haar _root_.OAI.HardSphere.bridgeEndpointBase_finite _root_.OAI.HardSphere.configurationBorel _root_.OAI.HardSphere.configurationPathBorel _root_.OAI.HardSphere.configurationPathMeasurable _root_.OAI.HardSphere.coordinateBridge_probability _root_.OAI.HardSphere.coordinateWiener_probability _root_.OAI.HardSphere.endpointWeightedBase_sfinite _root_.OAI.HardSphere.freePathLaw_finite_deletion _root_.OAI.HardSphere.gaussianCoordinates_probability _root_.OAI.HardSphere.hilbertDomain_closed _root_.OAI.HardSphere.hilbertDomain_complete _root_.OAI.HardSphere.killedPathLaw_finite_deletion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
namespace HardSphere

lemma bosonic_iff_pullback {N : ℕ} {L : Length} (ψ : ScalarL2 N L) :
    bosonic ψ ↔ ∀ σ, permutationPullback σ ψ = ψ := by
  have hae (σ : Equiv.Perm (Fin N)) :
      (permutationPullback σ ψ : Configuration N L → ℂ) =ᵐ[volume]
        fun X ↦ ψ (permuteConfiguration σ X) :=
    Lp.coeFn_compMeasurePreserving ψ (measurePreserving_permute σ)
  constructor
  · intro h σ
    exact Lp.ext ((hae σ).trans (h σ))
  · intro h σ
    have hh := hae σ
    rw [h σ] at hh
    exact hh.symm

section

attribute [local instance] scalarL2_normedAddCommGroup scalarL2_module

@[simp] lemma mem_bosonicSubmodule {N : ℕ} {L : Length} {ψ : ScalarL2 N L} :
    ψ ∈ bosonicSubmodule N L ↔ bosonic ψ := by
  simp only [bosonicSubmodule, Submodule.mem_iInf, LinearMap.mem_ker,
    LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero]
  exact (bosonic_iff_pullback ψ).symm

end

@[simp] lemma mem_groundFormSubmodule {N : ℕ} {L : Length} {a : ℝ} {u : Jet N L} :
    u ∈ groundFormSubmodule N L a ↔ u ∈ dirichletDomain N L a ∧ bosonic u.1 := by
  simp [groundFormSubmodule]

end HardSphere

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_FirstVariation
attribute [-instance] _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Rescaling.config_haar _root_.OAI.HardSphere.bridgeEndpointBase_finite _root_.OAI.HardSphere.configurationBorel _root_.OAI.HardSphere.configurationPathBorel _root_.OAI.HardSphere.configurationPathMeasurable _root_.OAI.HardSphere.coordinateBridge_probability _root_.OAI.HardSphere.coordinateWiener_probability _root_.OAI.HardSphere.endpointWeightedBase_sfinite _root_.OAI.HardSphere.freePathLaw_finite_deletion _root_.OAI.HardSphere.gaussianCoordinates_probability _root_.OAI.HardSphere.hilbertDomain_closed _root_.OAI.HardSphere.hilbertDomain_complete _root_.OAI.HardSphere.killedPathLaw_finite_deletion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
namespace HardSphere

theorem IsGroundVector.first_variation {N : ℕ} {L : Length} {a : ℝ}
    {u : Jet N L} (hu : IsGroundVector N L a u) (v : Jet N L)
    (hv : v ∈ dirichletDomain N L a) (hb : bosonic v.1) :
    (∑ p : Direction N, inner ℂ (u.2 p) (v.2 p)) =
      (energy u : ℂ) * inner ℂ u.1 v.1 := by
  apply Variational.ground_pairing (groundFormSubmodule N L a) u
  · exact mem_groundFormSubmodule.mpr ⟨hu.1, hu.2.1⟩
  · exact hu.2.2.1
  · intro w hw hn
    exact hu.2.2.2 w (mem_groundFormSubmodule.mp hw).1
      (mem_groundFormSubmodule.mp hw).2 hn
  · exact mem_groundFormSubmodule.mpr ⟨hv, hb⟩

lemma SmoothTest.jet_permute {N : ℕ} {L : Length} {a : ℝ}
    (f : SmoothTest N L a) (σ : Equiv.Perm (Fin N)) :
    (f.permute σ).jet = permutationJet σ f.jet := by
  apply Prod.ext
  · apply Lp.ext
    exact (MemLp.coeFn_toLp (f.permute σ).memLp).trans
      ((Lp.coeFn_compMeasurePreserving f.jet.1 (measurePreserving_permute σ)).trans
        ((measurePreserving_permute σ).quasiMeasurePreserving.ae_eq_comp
          (MemLp.coeFn_toLp f.memLp))).symm
  · funext p
    apply Lp.ext
    have h := (measurePreserving_permute (L := L) σ).quasiMeasurePreserving.ae_eq_comp
      (MemLp.coeFn_toLp (f.partial_memLp (σ.symm p.1, p.2)))
    refine (MemLp.coeFn_toLp ((f.permute σ).partial_memLp p)).trans ?_
    change coordDerivative N L (f.toFun ∘ permuteConfiguration σ) p =ᵐ[volume] _
    rw [coordDerivative_permute]
    exact ((Lp.coeFn_compMeasurePreserving _ (measurePreserving_permute σ)).trans h).symm

lemma permutationJet_mem_domain {N : ℕ} {L : Length} {a : ℝ}
    (σ : Equiv.Perm (Fin N)) {u : Jet N L} (hu : u ∈ dirichletDomain N L a) :
    permutationJet σ u ∈ dirichletDomain N L a := by
  apply map_mem_closure (permutationJet σ).continuous hu
  rintro _ ⟨f, rfl⟩
  exact ⟨f.permute σ, f.jet_permute σ⟩

lemma energy_permutationJet {N : ℕ} {L : Length} (σ : Equiv.Perm (Fin N))
    (u : Jet N L) : energy (permutationJet σ u) = energy u := by
  change (∑ p : Direction N, ‖Lp.compMeasurePreserving _ (measurePreserving_permute σ)
    (u.2 (σ.symm p.1, p.2))‖ ^ 2) = _
  simp only [Lp.norm_compMeasurePreserving]
  exact Equiv.sum_comp (Equiv.prodCongr σ.symm (Equiv.refl (Fin 3)))
    (fun p ↦ ‖u.2 p‖ ^ 2)

end HardSphere

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Comparison_PermutationPullbackComp
attribute [-instance] _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Rescaling.config_haar _root_.OAI.HardSphere.bridgeEndpointBase_finite _root_.OAI.HardSphere.configurationBorel _root_.OAI.HardSphere.configurationPathBorel _root_.OAI.HardSphere.configurationPathMeasurable _root_.OAI.HardSphere.coordinateBridge_probability _root_.OAI.HardSphere.coordinateWiener_probability _root_.OAI.HardSphere.endpointWeightedBase_sfinite _root_.OAI.HardSphere.freePathLaw_finite_deletion _root_.OAI.HardSphere.gaussianCoordinates_probability _root_.OAI.HardSphere.hilbertDomain_closed _root_.OAI.HardSphere.hilbertDomain_complete _root_.OAI.HardSphere.killedPathLaw_finite_deletion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
noncomputable section
open scoped BigOperators ComplexConjugate
namespace HardSphere

lemma permutationPullback_comp {N : ℕ} {L : Length}
    (σ τ : Equiv.Perm (Fin N)) (ψ : ScalarL2 N L) :
    permutationPullback σ (permutationPullback τ ψ) = permutationPullback (σ * τ) ψ := by
  change Lp.compMeasurePreserving _ (measurePreserving_permute σ)
    (Lp.compMeasurePreserving _ (measurePreserving_permute τ) ψ) = _
  rw [← Lp.compMeasurePreserving_comp_apply]
  rfl

lemma inner_permutationPullback {N : ℕ} {L : Length} (σ : Equiv.Perm (Fin N))
    (ψ φ : ScalarL2 N L) :
    inner ℂ (permutationPullback σ ψ) (permutationPullback σ φ) = inner ℂ ψ φ :=
  (Lp.compMeasurePreservingₗᵢ ℂ _ (measurePreserving_permute σ)).inner_map_map ψ φ

lemma gradientPairing_permutationJet {N : ℕ} {L : Length}
    (σ : Equiv.Perm (Fin N)) (u v : Jet N L) :
    Variational.gradientPairing (permutationJet σ u) (permutationJet σ v) =
      Variational.gradientPairing u v := by
  change (∑ p : Direction N, inner ℂ (permutationPullback σ (u.2 (σ.symm p.1, p.2)))
    (permutationPullback σ (v.2 (σ.symm p.1, p.2)))) = _
  simp only [inner_permutationPullback]
  exact Equiv.sum_comp (Equiv.prodCongr σ.symm (Equiv.refl (Fin 3)))
    (fun p ↦ inner ℂ (u.2 p) (v.2 p))

theorem IsGroundVector.permutationInvariant {N : ℕ} {L : Length} {a : ℝ}
    {u : Jet N L} (hu : IsGroundVector N L a u) (σ : Equiv.Perm (Fin N)) :
    permutationJet σ u = u := by
  have hs : (permutationJet σ u).1 = u.1 := (bosonic_iff_pullback u.1).mp hu.2.1 σ
  have hv : permutationJet σ u ∈ groundFormSubmodule N L a := by
    rw [mem_groundFormSubmodule]
    exact ⟨permutationJet_mem_domain σ hu.1, hs ▸ hu.2.1⟩
  exact Variational.minimizer_eq_of_scalar_eq (groundFormSubmodule N L a) u
    (mem_groundFormSubmodule.mpr ⟨hu.1, hu.2.1⟩) hu.2.2.1
    (fun w hw hn ↦ hu.2.2.2 w (mem_groundFormSubmodule.mp hw).1
      (mem_groundFormSubmodule.mp hw).2 hn)
    (permutationJet σ u) hv hs (le_of_eq (energy_permutationJet σ u))

lemma bosonic_sum_permutationPullback {N : ℕ} {L : Length} (ψ : ScalarL2 N L) :
    bosonic (∑ σ : Equiv.Perm (Fin N), permutationPullback σ ψ) := by
  rw [bosonic_iff_pullback]
  intro τ
  simp only [map_sum, permutationPullback_comp]
  exact Equiv.sum_comp (Equiv.mulLeft τ) (fun σ ↦ permutationPullback σ ψ)

lemma gradientPairing_sum_right {N : ℕ} {L : Length} {I : Type*} [Fintype I]
    (u : Jet N L) (v : I → Jet N L) :
    Variational.gradientPairing u (∑ i, v i) =
      ∑ i, Variational.gradientPairing u (v i) := by
  simp only [Variational.gradientPairing, Prod.snd_sum, Finset.sum_apply, inner_sum]
  exact Finset.sum_comm

theorem IsGroundVector.full_first_variation {N : ℕ} {L : Length} {a : ℝ}
    {u : Jet N L} (hu : IsGroundVector N L a u) (v : Jet N L)
    (hv : v ∈ dirichletDomain N L a) :
    (∑ p : Direction N, inner ℂ (u.2 p) (v.2 p)) =
      (energy u : ℂ) * inner ℂ u.1 v.1 := by
  let w : Jet N L := ∑ σ : Equiv.Perm (Fin N), permutationJet σ v
  have hwd : w ∈ dirichletDomain N L a := by
    change w ∈ dirichletSubmodule N L a
    exact Submodule.sum_mem _ fun σ _ ↦ permutationJet_mem_domain σ hv
  have hwb : bosonic w.1 := by
    dsimp only [w]
    rw [Prod.fst_sum]
    exact bosonic_sum_permutationPullback v.1
  have hgp (σ : Equiv.Perm (Fin N)) :
      Variational.gradientPairing u (permutationJet σ v) = Variational.gradientPairing u v := by
    calc
      _ = Variational.gradientPairing (permutationJet σ u) (permutationJet σ v) := by
        rw [hu.permutationInvariant σ]
      _ = _ := gradientPairing_permutationJet σ u v
  have hip (σ : Equiv.Perm (Fin N)) :
      inner ℂ u.1 (permutationJet σ v).1 = inner ℂ u.1 v.1 := by
    calc
      _ = inner ℂ (permutationPullback σ u.1) (permutationPullback σ v.1) := by
        rw [(bosonic_iff_pullback u.1).mp hu.2.1 σ]; rfl
      _ = _ := inner_permutationPullback σ u.1 v.1
  have he := hu.first_variation w hwd hwb
  change Variational.gradientPairing u w = _ at he
  simp only [w, gradientPairing_sum_right, hgp, Prod.fst_sum, inner_sum, hip,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at he
  have hc : (Fintype.card (Equiv.Perm (Fin N)) : ℂ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  apply mul_left_cancel₀ hc
  change (Fintype.card (Equiv.Perm (Fin N)) : ℂ) * Variational.gradientPairing u v = _
  rw [he]
  ring

end HardSphere

end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_FormDomain_HilbertJet
attribute [-instance] _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Rescaling.config_haar _root_.OAI.HardSphere.bridgeEndpointBase_finite _root_.OAI.HardSphere.configurationBorel _root_.OAI.HardSphere.configurationPathBorel _root_.OAI.HardSphere.configurationPathMeasurable _root_.OAI.HardSphere.endpointWeightedBase_sfinite _root_.OAI.HardSphere.freePathLaw_finite_deletion _root_.OAI.HardSphere.killedPathLaw_finite_deletion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
noncomputable section
open scoped BigOperators ComplexConjugate
namespace HardSphere

attribute [local instance] scalarL2_addCommMonoid scalarL2_module scalarL2_completeSpace

lemma continuous_torusDistance (L : Length) : Continuous (fun p : Torus L × Torus L ↦ torusDistance L p.1 p.2) := by
  unfold torusDistance
  fun_prop

end HardSphere

end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_ConfigurationPath
attribute [-instance] _root_.OAI.HardSphere.Groups.labelOptionSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
noncomputable section
open scoped BigOperators ComplexConjugate
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators

namespace L2Multiplier
variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

lemma coe_clm (f : α → ℂ) (hf : MemLp f ∞ μ) (u : Lp ℂ 2 μ) :
    clm f hf u =ᵐ[μ] fun x ↦ f x * u x := coe_apply f hf u

lemma clm_mul (f g : α → ℂ) (hf : MemLp f ∞ μ) (hg : MemLp g ∞ μ)
    (u : Lp ℂ 2 μ) : clm (f * g) (hg.mul hf) u = clm f hf (clm g hg u) := by
  apply Lp.ext
  filter_upwards [coe_clm (f * g) (hg.mul hf) u, coe_clm f hf (clm g hg u),
    coe_clm g hg u] with x h1 h2 h3
  simp only [h1, h2, h3, Pi.mul_apply, mul_assoc]

lemma inner_clm_right (f : α → ℂ) (hf : MemLp f ∞ μ) (u v : Lp ℂ 2 μ) :
    inner ℂ u (clm f hf v) = inner ℂ (clm (fun x ↦ conj (f x)) hf.star u) v := by
  simp only [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [coe_clm f hf v, coe_clm (fun x ↦ conj (f x)) hf.star u] with x h1 h2
  simp only [h1, h2, RCLike.inner_apply, map_mul, starRingEnd_self_apply]
  ring

end L2Multiplier

end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Bridges_NormalizedPrefix
attribute [-instance] _root_.OAI.HardSphere.Bridge.exposedBridgeKernel_markov _root_.OAI.HardSphere.Bridge.exposedPeriodSingle_finite _root_.OAI.HardSphere.Bridge.exposedTrialKernel_markov _root_.OAI.HardSphere.Bridge.instBorelSpaceContinuousMapElemRealTimePoint _root_.OAI.HardSphere.Bridge.instIsProbabilityMeasureNoiseLaw _root_.OAI.HardSphere.Bridge.instMeasurableSpaceContinuousMapElemRealTimePoint _root_.OAI.HardSphere.Bridge.parameterBridgeKernel_markov _root_.OAI.HardSphere.Bridge.parameterIndividualReference_finite _root_.OAI.HardSphere.Bridge.parameterTrialKernel_markov _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Bridge.trialKernel_markov _root_.OAI.HardSphere.Groups.cellPathReference_probability _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Rescaling.config_haar _root_.OAI.HardSphere.bridgeEndpointBase_finite _root_.OAI.HardSphere.coordinateBridge_probability _root_.OAI.HardSphere.endpointWeightedBase_sfinite _root_.OAI.HardSphere.freePathLaw_finite_deletion _root_.OAI.HardSphere.gaussianCoordinates_probability _root_.OAI.HardSphere.killedPathLaw_finite_deletion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
namespace HardSphere
namespace Wiener

lemma normalized_split_preserving (u : Time) (hu : 0<(u:ℝ)) (hu' : (u:ℝ)<1) :
    MeasurePreserving (fun w : C(Time,ℝ) ↦ (normalizedPrefix u w,normalizedSuffix u w))
      wiener (wiener.prod wiener) := by
  have hm : Measurable (fun w : C(Time,ℝ) ↦ (prefixMap u w,suffixMap u w)) := by fun_prop
  have heq : wiener.map (fun w : C(Time,ℝ) ↦ (prefixMap u w,suffixMap u w)) =
      (wiener.map (fun f ↦ Real.sqrt (u:ℝ) • f)).prod
        (wiener.map (fun f ↦ Real.sqrt (1-(u:ℝ)) • f)) := by
    rw [wiener,Measure.map_map hm measurable_path]
    exact split_path_law u
  refine ⟨by fun_prop,?_⟩
  rw [Measure.map_prod_map _ _ (by fun_prop) (by fun_prop)] at heq
  have hh := congrArg (fun μ : Measure (C(Time,ℝ) × C(Time,ℝ)) ↦ μ.map
    (fun p ↦ ((Real.sqrt (u:ℝ))⁻¹ • p.1,(Real.sqrt (1-(u:ℝ)))⁻¹ • p.2))) heq
  rw [Measure.map_map (by fun_prop) hm, Measure.map_map (by fun_prop) (by fun_prop)] at hh
  simpa only [normalizedPrefix,normalizedSuffix,smul_apply,
    Function.comp_def,Prod.map,smul_smul,
    inv_mul_cancel₀ (ne_of_gt (Real.sqrt_pos.mpr hu)),
    inv_mul_cancel₀ (ne_of_gt (Real.sqrt_pos.mpr (sub_pos.mpr hu'))),
    one_smul,Prod.mk.eta,Measure.map_id'] using hh

end Wiener

open Wiener

lemma splitTime_pos (s t : ℝ) (hs : 0 < s) (ht : 0<t) : 0<(splitTime s t hs ht:ℝ) :=
  div_pos hs (add_pos hs ht)

lemma splitTime_lt_one (s t : ℝ) (hs : 0 < s) (ht : 0<t) : (splitTime s t hs ht:ℝ)<1 :=
  (div_lt_one (add_pos hs ht)).mpr (by linarith)

lemma sqrt_split_left (s t : ℝ) (hs : 0 < s) (ht : 0<t) :
    Real.sqrt (2*s) * (Real.sqrt (splitTime s t hs ht:ℝ))⁻¹ = Real.sqrt (2*(s+t)) := by
  have h : Real.sqrt (2*(s+t)) * Real.sqrt (splitTime s t hs ht:ℝ) = Real.sqrt (2*s) := by
    rw [← Real.sqrt_mul (by positivity)]
    congr 1
    change 2*(s+t)*(s/(s+t))=2*s
    field_simp
  rw [← h,mul_assoc,mul_inv_cancel₀ (ne_of_gt (Real.sqrt_pos.mpr (splitTime_pos s t hs ht))),mul_one]

lemma sqrt_split_right (s t : ℝ) (hs : 0 < s) (ht : 0<t) :
    Real.sqrt (2*t) * (Real.sqrt (1-(splitTime s t hs ht:ℝ)))⁻¹ = Real.sqrt (2*(s+t)) := by
  have h : Real.sqrt (2*(s+t)) * Real.sqrt (1-(splitTime s t hs ht:ℝ)) = Real.sqrt (2*t) := by
    rw [← Real.sqrt_mul (by positivity)]
    congr 1
    change 2*(s+t)*(1-s/(s+t))=2*t
    field_simp
    ring
  rw [← h,mul_assoc,mul_inv_cancel₀ (ne_of_gt (Real.sqrt_pos.mpr (sub_pos.mpr (splitTime_lt_one s t hs ht)))),mul_one]

lemma coordinateSplit_preserving (N : ℕ) (u : Time) (hu : 0<(u:ℝ)) (hu' : (u:ℝ)<1) :
    MeasurePreserving (fun w : CoordinatePaths N ↦
      (fun p ↦ normalizedPrefix u (w p), fun p ↦ normalizedSuffix u (w p)))
      (coordinateWiener N) ((coordinateWiener N).prod (coordinateWiener N)) := by
  have hm : Measurable (fun w : CoordinatePaths N ↦
      fun p ↦ (normalizedPrefix u (w p),normalizedSuffix u (w p))) := by fun_prop
  have h : MeasurePreserving (fun w : CoordinatePaths N ↦
      fun p ↦ (normalizedPrefix u (w p),normalizedSuffix u (w p)))
      (coordinateWiener N) (Measure.pi fun _ : Direction N ↦ wiener.prod wiener) := by
    refine ⟨hm,?_⟩
    unfold coordinateWiener
    rw [Measure.pi_map_pi (fun _ ↦ (normalized_split_preserving u hu hu').measurable.aemeasurable)]
    simp_rw [(normalized_split_preserving u hu hu').map_eq]
  exact (measurePreserving_arrowProdEquivProdArrow C(Time,ℝ) C(Time,ℝ) (Direction N)
    (fun _ ↦ wiener) (fun _ ↦ wiener)).comp h

lemma prefix_freeTrajectory (N : ℕ) (L : Length) (s t : ℝ) (hs : 0 < s) (ht : 0<t)
    (w : CoordinatePaths N) (X : Configuration N L) :
    configurationPrefix N L (splitTime s t hs ht) (freeTrajectory N L (s+t) w X) =
      freeTrajectory N L s (fun p ↦ normalizedPrefix (splitTime s t hs ht) (w p)) X := by
  ext v i j
  change X i j + ((Real.sqrt (2*(s+t))*w (i,j) (prefixTime _ v):ℝ):AddCircle L.val)=
    X i j + ((Real.sqrt (2*s)*((Real.sqrt (_:ℝ))⁻¹*w (i,j) (prefixTime _ v)):ℝ):AddCircle L.val)
  rw [← mul_assoc,sqrt_split_left]

lemma suffix_freeTrajectory (N : ℕ) (L : Length) (s t : ℝ) (hs : 0 < s) (ht : 0<t)
    (w : CoordinatePaths N) (X : Configuration N L) :
    configurationSuffix N L (splitTime s t hs ht) (freeTrajectory N L (s+t) w X) =
      freeTrajectory N L t (fun p ↦ normalizedSuffix (splitTime s t hs ht) (w p))
        (freeTrajectory N L (s+t) w X (splitTime s t hs ht)) := by
  ext v i j
  change X i j + ((Real.sqrt (2*(s+t))*w (i,j) (suffixTime _ v):ℝ):AddCircle L.val)=
    (X i j + ((Real.sqrt (2*(s+t))*w (i,j) _ :ℝ):AddCircle L.val))+
      ((Real.sqrt (2*t)*((Real.sqrt (1-(_:ℝ)))⁻¹*(w (i,j) (suffixTime _ v)-w (i,j) _)):ℝ):AddCircle L.val)
  rw [← mul_assoc,sqrt_split_right,mul_sub,AddCircle.coe_sub]
  abel

end HardSphere

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Bridges_WienerGaussian
attribute [-instance] _root_.OAI.HardSphere.Bridge.exposedBridgeKernel_markov _root_.OAI.HardSphere.Bridge.exposedPeriodSingle_finite _root_.OAI.HardSphere.Bridge.exposedTrialKernel_markov _root_.OAI.HardSphere.Bridge.instBorelSpaceContinuousMapElemRealTimePoint _root_.OAI.HardSphere.Bridge.instIsProbabilityMeasureNoiseLaw _root_.OAI.HardSphere.Bridge.instMeasurableSpaceContinuousMapElemRealTimePoint _root_.OAI.HardSphere.Bridge.parameterBridgeKernel_markov _root_.OAI.HardSphere.Bridge.parameterIndividualReference_finite _root_.OAI.HardSphere.Bridge.parameterTrialKernel_markov _root_.OAI.HardSphere.Bridge.trialKernel_markov _root_.OAI.HardSphere.Groups.cellPathReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.configurationPathBorel _root_.OAI.HardSphere.coordinateBridge_probability _root_.OAI.HardSphere.coordinateWiener_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open MeasureTheory Filter Set ProbabilityTheory
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.Wiener

lemma norm_tent_combination_le (n : ℕ) (c : Fin (2^n) → ℝ)
    (hc : ∀ k, |c k| ≤ 1) : ‖∑ k, c k • tentMap n k‖ ≤ 1 := by
  apply (ContinuousMap.norm_le _ (by norm_num)).mpr
  intro t
  simp only [ContinuousMap.sum_apply, ContinuousMap.smul_apply, smul_eq_mul, Real.norm_eq_abs]
  calc
    |∑ k, c k * tentMap n k t| ≤ ∑ k, |c k * tentMap n k t| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k, tent n k t := by
      apply Finset.sum_le_sum
      intro k _
      change |c k * tent n k t|≤_
      rw [abs_mul, abs_of_nonneg (tent_nonneg n k t)]
      simpa only [one_mul] using mul_le_mul_of_nonneg_right (hc k) (tent_nonneg n k t)
    _ ≤ 1 := sum_tent_le_one n t

lemma dual_tent_sum_abs_le (L : C(Time,ℝ) →L[ℝ] ℝ) (n : ℕ) :
    ∑ k, |L (tentMap n k)| ≤ ‖L‖ := by
  classical
  let c : Fin (2^n) → ℝ := fun k ↦ if 0 ≤ L (tentMap n k) then 1 else -1
  have hc : ∀ k, |c k|≤1 := by intro k; simp only [c]; split <;> norm_num
  have he : L (∑ k, c k • tentMap n k) = ∑ k, |L (tentMap n k)| := by
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro k _
    rw [map_smul]
    simp only [smul_eq_mul,c]
    split_ifs with h
    · simp [abs_of_nonneg h]
    · simp [abs_of_neg (lt_of_not_ge h)]
  calc
    ∑ k, |L (tentMap n k)| ≤ |L (∑ k, c k • tentMap n k)| := by rw [he]; exact le_abs_self _
    _ ≤ ‖L‖ * ‖∑ k, c k • tentMap n k‖ := L.le_opNorm _
    _ ≤ ‖L‖ * 1 := mul_le_mul_of_nonneg_left (norm_tent_combination_le n c hc) (L.opNorm_nonneg)
    _ = ‖L‖ := mul_one _

lemma dual_tent_sum_sq_le (L : C(Time,ℝ) →L[ℝ] ℝ) (n : ℕ) :
    ∑ k, L (tentMap n k)^2 ≤ ‖L‖^2 := by
  have h := dual_tent_sum_abs_le L n
  calc
    ∑ k, L (tentMap n k)^2 = ∑ k, |L (tentMap n k)|^2 := by simp
    _ ≤ (∑ k, |L (tentMap n k)|)^2 := by
      rw [sq, Finset.sum_mul_sum]
      apply Finset.sum_le_sum
      intro k _
      rw [sq]
      exact Finset.single_le_sum (f := fun j ↦ |L (tentMap n k)| * |L (tentMap n j)|)
        (fun j _ ↦ mul_nonneg (abs_nonneg _) (abs_nonneg _)) (Finset.mem_univ k)
    _ ≤ ‖L‖^2 := pow_le_pow_left₀ (Finset.sum_nonneg (fun _ _ ↦ abs_nonneg _)) h 2

lemma amplitude_sq (n : ℕ) : amplitude n ^ 2 = (1/4:ℝ)*(1/2:ℝ)^n := by
  simp only [amplitude,mul_pow]
  rw [←pow_mul,Nat.mul_comm n 2,pow_mul,inv_pow,Real.sq_sqrt (by norm_num : (0:ℝ)≤2)]
  norm_num

lemma dual_variance_summable (L : C(Time,ℝ) →L[ℝ] ℝ) :
    Summable (fun n ↦ amplitude n^2 * ∑ k, L (tentMap n k)^2) := by
  apply Summable.of_nonneg_of_le (fun n ↦ by positivity)
    (fun n ↦ mul_le_mul_of_nonneg_left (dual_tent_sum_sq_le L n) (sq_nonneg _))
  simp_rw [amplitude_sq]
  simpa only [mul_assoc, mul_left_comm, mul_comm] using
    (summable_geometric_of_lt_one (by norm_num : (0:ℝ)≤1/2) (by norm_num : (1/2:ℝ)<1)).mul_left ((1/4:ℝ)*‖L‖^2)

lemma dual_partialPath_expansion (L : C(Time,ℝ) →L[ℝ] ℝ) (n : ℕ) (ω : Noise) :
    L (partialPath n ω) = ∑ i, dualCoefficient L n i * ω (partialEmbed n i) := by
  simp only [Fintype.sum_sum_type,Fintype.sum_sigma,dualCoefficient,partialEmbed,
    Fintype.sum_unique,partialPath,map_add,map_smul,map_sum,level,smul_eq_mul]
  rw [Fin.sum_univ_eq_sum_range (fun m ↦ ∑ k : Fin (2^m), amplitude m * L (tentMap m k) * ω (.inr ⟨m,k⟩)) n]
  congr 1
  · change ω (.inl ()) * L linearPath = L linearPath * ω (.inl ())
    ring
  · apply Finset.sum_congr rfl
    intro m _
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    ring

lemma dual_partial_variance (L : C(Time,ℝ) →L[ℝ] ℝ) (n : ℕ) :
    (∑ i : PartialIndex n, dualCoefficient L n i ^ 2) =
      L linearPath ^ 2 + ∑ m ∈ Finset.range n, amplitude m^2 * ∑ k, L (tentMap m k)^2 := by
  simp only [Fintype.sum_sum_type,Fintype.sum_sigma,dualCoefficient,Fintype.sum_unique,mul_pow,←Finset.mul_sum]
  rw [Fin.sum_univ_eq_sum_range (fun m ↦ amplitude m^2 * ∑ k, L (tentMap m k)^2) n]

lemma dual_path_law (L : C(Time,ℝ) →L[ℝ] ℝ) :
    HasLaw (fun ω ↦ L (path ω))
      (gaussianReal 0 (Real.toNNReal (L linearPath^2 + ∑' n, amplitude n^2 * ∑ k, L (tentMap n k)^2))) law := by
  have hv : Tendsto (fun n ↦ Real.toNNReal (∑ i : PartialIndex n, dualCoefficient L n i ^2)) atTop
      (𝓝 (Real.toNNReal (L linearPath^2 + ∑' n, amplitude n^2 * ∑ k, L (tentMap n k)^2))) := by
    simp_rw [dual_partial_variance]
    exact continuous_real_toNNReal.tendsto _ |>.comp
      (tendsto_const_nhds.add ((dual_variance_summable L).hasSum.tendsto_sum_nat))
  apply hasLaw_gaussian_of_ae_tendsto (X := fun n ω ↦ L (partialPath n ω)) (m := fun _ ↦ 0)
    (v := fun n ↦ Real.toNNReal (∑ i : PartialIndex n, dualCoefficient L n i^2)) _ _ tendsto_const_nhds hv
  · intro n
    have h := finite_coordinate_law n (dualCoefficient L n)
    simp_rw [←dual_partialPath_expansion] at h
    convert h using 2
    all_goals try with_reducible_and_instances rfl
    rw [Real.toNNReal_sum_of_nonneg (fun i _ ↦ sq_nonneg (dualCoefficient L n i))]
    apply Finset.sum_congr rfl
    intro i _
    exact Real.toNNReal_of_nonneg (sq_nonneg _)
  · filter_upwards [ae_partialPath_tendsto] with ω hω
    exact L.continuous.tendsto _ |>.comp hω

instance wiener_isGaussian : IsGaussian wiener := by
  apply isGaussian_of_map_eq_gaussianReal
  intro L
  refine ⟨0,Real.toNNReal (L linearPath^2 + ∑' n, amplitude n^2 * ∑ k, L (tentMap n k)^2),?_⟩
  rw [wiener,Measure.map_map L.continuous.measurable measurable_path]
  exact (dual_path_law L).map_eq

theorem wiener_exists_integrable_exp_sq :
    ∃ c, 0 < c ∧ Integrable (fun w : C(Time,ℝ) ↦ Real.exp (c*‖w‖^2)) wiener :=
  IsGaussian.exists_integrable_exp_sq wiener

theorem wiener_norm_gaussian_tail :
    ∃ (c : ℝ) (M : ℝ≥0∞), 0 < c ∧ M<⊤ ∧ ∀ R : ℝ, 0≤R →
      wiener {w | R≤‖w‖} ≤ M * ENNReal.ofReal (Real.exp (-c*R^2)) := by
  obtain ⟨c,hc,hi⟩ := wiener_exists_integrable_exp_sq
  let M := ∫⁻ w : C(Time,ℝ), ENNReal.ofReal (Real.exp (c*‖w‖^2)) ∂wiener
  have hM : M<⊤ := by
    dsimp [M]
    rw [←ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall (fun _ ↦ (Real.exp_pos _).le))]
    exact ENNReal.ofReal_lt_top
  refine ⟨c,M,hc,hM,?_⟩
  intro R hR
  have hsub : {w : C(Time,ℝ) | R≤‖w‖} ⊆
      {w | ENNReal.ofReal (Real.exp (c*R^2))≤ENNReal.ofReal (Real.exp (c*‖w‖^2))} := by
    intro w hw
    apply ENNReal.ofReal_le_ofReal
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hR hw 2) hc.le)
  apply (measure_mono hsub).trans
  have hm : Measurable (fun w : C(Time,ℝ) ↦ ENNReal.ofReal (Real.exp (c*‖w‖^2))) := by fun_prop
  have hh := meas_ge_le_lintegral_div (μ := wiener) hm.aemeasurable
      (ne_of_gt (ENNReal.ofReal_pos.mpr (Real.exp_pos (c*R^2)))) ENNReal.ofReal_ne_top
  apply hh.trans_eq
  change M / ENNReal.ofReal (Real.exp (c*R^2)) = M * ENNReal.ofReal (Real.exp (-c*R^2))
  rw [div_eq_mul_inv,←ENNReal.ofReal_inv_of_pos (Real.exp_pos _),←Real.exp_neg]
  congr 3
  ring

end HardSphere.Wiener

end
end

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_CoordinateLine
attribute [-instance] _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Rescaling.config_haar _root_.OAI.HardSphere.bridgeEndpointBase_finite _root_.OAI.HardSphere.configurationBorel _root_.OAI.HardSphere.configurationPathBorel _root_.OAI.HardSphere.configurationPathMeasurable _root_.OAI.HardSphere.coordinateBridge_probability _root_.OAI.HardSphere.coordinateWiener_probability _root_.OAI.HardSphere.endpointWeightedBase_sfinite _root_.OAI.HardSphere.freePathLaw_finite_deletion _root_.OAI.HardSphere.gaussianCoordinates_probability _root_.OAI.HardSphere.hilbertDomain_closed _root_.OAI.HardSphere.hilbertDomain_complete _root_.OAI.HardSphere.killedPathLaw_finite_deletion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
namespace HardSphere

open scoped ComplexConjugate

lemma coordDerivative_conj {N : ℕ} {L : Length} {f : Configuration N L → ℂ}
    (hf : Differentiable ℝ (fun X : LiftedConfiguration N ↦ f (project N L X)))
    (p : Direction N) :
    coordDerivative N L (fun X ↦ conj (f X)) p = fun X ↦ conj (coordDerivative N L f p X) := by
  funext X
  unfold coordDerivative
  have h := Complex.conjCLE.toContinuousLinearMap.hasFDerivAt.comp (representative N L X)
    (hf _).hasFDerivAt
  exact congrArg (fun A : LiftedConfiguration N →L[ℝ] ℂ ↦
    A (Pi.single p.1 (Pi.single p.2 1))) h.fderiv

end HardSphere

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_NormSqIntegral
attribute [-instance] _root_.OAI.HardSphere.Groups.labelOptionSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
namespace IndicatorStrong
variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

lemma norm_sq_integral (f : Lp ℂ 2 μ) : ‖f‖^2 = ∫ x, ‖f x‖^2 ∂μ := by
  rw [@norm_sq_eq_re_inner ℂ, L2.inner_def, ← integral_re]
  · congr 1
    ext x
    simp only [inner_self_eq_norm_sq_to_K, RCLike.re_ofReal_pow]
  · exact L2.integrable_inner f f

end IndicatorStrong

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_SmoothMultiplier
attribute [-instance] _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Rescaling.config_haar _root_.OAI.HardSphere.bridgeEndpointBase_finite _root_.OAI.HardSphere.coordinateBridge_probability _root_.OAI.HardSphere.endpointWeightedBase_sfinite _root_.OAI.HardSphere.freePathLaw_finite_deletion _root_.OAI.HardSphere.gaussianCoordinates_probability _root_.OAI.HardSphere.killedPathLaw_finite_deletion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
namespace HardSphere

lemma SmoothTest.jet_multiply {N : ℕ} {L : Length} {a : ℝ}
    (f : SmoothMultiplier N L) (g : SmoothTest N L a) :
    (g.multiply f).jet = f.onJet g.jet := by
  apply Prod.ext
  · apply Lp.ext
    filter_upwards [MemLp.coeFn_toLp (g.multiply f).memLp, MemLp.coeFn_toLp g.memLp,
      L2Multiplier.coe_clm f.toFun f.memLp_top g.jet.1] with X h1 h2 h3
    change _ = (f.onScalar g.jet.1) X
    exact h1.trans (by simpa only [SmoothTest.multiply, Pi.mul_apply, SmoothTest.jet,
      SmoothMultiplier.onScalar, h2] using h3.symm)
  · funext p
    apply Lp.ext
    have hder := coordDerivative_mul (f.smooth.differentiable (by simp))
      (g.smooth.differentiable (by simp)) p
    filter_upwards [MemLp.coeFn_toLp ((g.multiply f).partial_memLp p),
      MemLp.coeFn_toLp g.memLp, MemLp.coeFn_toLp (g.partial_memLp p),
      L2Multiplier.coe_clm f.toFun f.memLp_top (g.jet.2 p),
      L2Multiplier.coe_clm _ (f.partial_memLp_top p) g.jet.1,
      Lp.coeFn_add (f.onScalar (g.jet.2 p))
        (L2Multiplier.clm _ (f.partial_memLp_top p) g.jet.1)] with X h1 h2 h3 h4 h5 h6
    change _ = (f.onScalar (g.jet.2 p) + L2Multiplier.clm _ (f.partial_memLp_top p) g.jet.1) X
    rw [h6, Pi.add_apply, SmoothMultiplier.onScalar, h4, h5]
    simp only [SmoothTest.jet]
    rw [h1]
    change coordDerivative N L (f.toFun * g.toFun) p X = _
    rw [hder]
    simp only [Pi.add_apply, Pi.mul_apply, h2, h3]
    ring

lemma SmoothMultiplier.onJet_mem_domain {N : ℕ} {L : Length} {a : ℝ}
    (f : SmoothMultiplier N L) {u : Jet N L} (hu : u ∈ dirichletDomain N L a) :
    f.onJet u ∈ dirichletDomain N L a := by
  apply map_mem_closure f.onJet.continuous hu
  rintro _ ⟨g, rfl⟩
  exact ⟨g.multiply f, g.jet_multiply f⟩

end HardSphere

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_InnerClmRealRight
attribute [-instance] _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Rescaling.config_haar _root_.OAI.HardSphere.bridgeEndpointBase_finite _root_.OAI.HardSphere.coordinateBridge_probability _root_.OAI.HardSphere.endpointWeightedBase_sfinite _root_.OAI.HardSphere.freePathLaw_finite_deletion _root_.OAI.HardSphere.gaussianCoordinates_probability _root_.OAI.HardSphere.killedPathLaw_finite_deletion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
open ProbabilityTheory
namespace L2Multiplier
open MeasureTheory
open scoped ComplexConjugate ENNReal
variable {α : Type*} [MeasurableSpace α] {μ : Measure α}
lemma inner_clm_real_right (f : α → ℂ) (hf : MemLp f ∞ μ)
    (hreal : ∀ x, conj (f x) = f x) (u v : Lp ℂ 2 μ) :
    inner ℂ u (clm f hf v) = inner ℂ (clm f hf u) v := by
  simpa only [show (fun x ↦ conj (f x)) = f from funext hreal] using
    inner_clm_right f hf u v

lemma clm_comm (f g : α → ℂ) (hf : MemLp f ∞ μ) (hg : MemLp g ∞ μ)
    (u : Lp ℂ 2 μ) : clm f hf (clm g hg u) = clm g hg (clm f hf u) := by
  rw [← clm_mul, ← clm_mul]
  congr 2
  exact mul_comm f g

end L2Multiplier
namespace HardSphere
open MeasureTheory Set Filter
open scoped ComplexConjugate ENNReal
lemma SmoothMultiplier.partial_real {N : ℕ} {L : Length} (f : SmoothMultiplier N L)
    (hf : ∀ X, conj (f.toFun X) = f.toFun X) (p : Direction N) (X : Configuration N L) :
    conj (coordDerivative N L f.toFun p X) = coordDerivative N L f.toFun p X := by
  have he : (fun X ↦ conj (f.toFun X)) = f.toFun := funext hf
  rw [← congrFun (coordDerivative_conj (f.smooth.differentiable (by simp)) p) X, he]

lemma SmoothMultiplier.inner_onScalar_right {N : ℕ} {L : Length}
    (f : SmoothMultiplier N L) (hf : ∀ X, conj (f.toFun X) = f.toFun X)
    (u v : ScalarL2 N L) : inner ℂ u (f.onScalar v) = inner ℂ (f.onScalar u) v :=
  L2Multiplier.inner_clm_real_right _ _ hf u v

lemma SmoothMultiplier.onScalar_derivativeScalar_comm {N : ℕ} {L : Length}
    (f : SmoothMultiplier N L) (p : Direction N) (u : ScalarL2 N L) :
    f.onScalar (f.derivativeScalar p u) = f.derivativeScalar p (f.onScalar u) :=
  L2Multiplier.clm_comm _ _ _ _ u

theorem IsGroundVector.smooth_multiplier_identity {N : ℕ} {L : Length} {a : ℝ}
    {u : Jet N L} (hu : IsGroundVector N L a u) (f : SmoothMultiplier N L)
    (hf : ∀ X, conj (f.toFun X) = f.toFun X) :
    energy (f.onJet u) - energy u * ‖f.onScalar u.1‖ ^ 2 =
      ∑ p : Direction N, ‖f.derivativeScalar p u.1‖ ^ 2 := by
  have hv := f.onJet_mem_domain (f.onJet_mem_domain hu.1)
  have he := hu.full_first_variation (f.onJet (f.onJet u)) hv
  have hnorm (x : ScalarL2 N L) : (inner ℂ x x).re = ‖x‖ ^ 2 :=
    (norm_sq_eq_re_inner (𝕜 := ℂ) x).symm
  have hpair (p : Direction N) :
      (inner ℂ (u.2 p) ((f.onJet (f.onJet u)).2 p)).re =
        ‖f.onScalar (u.2 p)‖ ^ 2 +
          2 * (inner ℂ (f.onScalar (u.2 p)) (f.derivativeScalar p u.1)).re := by
    rw [f.onJet_snd, f.onJet_snd, f.onJet_fst, map_add,
      inner_add_right, inner_add_right, ← f.onScalar_derivativeScalar_comm,
      f.inner_onScalar_right hf (u.2 p) (f.onScalar (u.2 p)),
      f.inner_onScalar_right hf (u.2 p) (f.derivativeScalar p u.1)]
    simp only [Complex.add_re, hnorm]
    ring
  have hs : (inner ℂ u.1 (f.onJet (f.onJet u)).1).re = ‖f.onScalar u.1‖ ^ 2 := by
    rw [f.onJet_fst, f.onJet_fst, f.inner_onScalar_right hf, hnorm]
  have her := congrArg Complex.re he
  simp only [Complex.re_sum, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero, hs, hpair] at her
  change (∑ p, ‖(f.onJet u).2 p‖ ^ 2) - energy u * ‖f.onScalar u.1‖ ^ 2 = _
  simp only [f.onJet_snd, norm_add_sq (𝕜 := ℂ)]
  rw [← her]
  change (∑ p, (‖f.onScalar (u.2 p)‖ ^ 2 +
      2 * (inner ℂ (f.onScalar (u.2 p)) (f.derivativeScalar p u.1)).re +
      ‖f.derivativeScalar p u.1‖ ^ 2)) -
    (∑ p, (‖f.onScalar (u.2 p)‖ ^ 2 +
      2 * (inner ℂ (f.onScalar (u.2 p)) (f.derivativeScalar p u.1)).re)) = _
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  ring

end HardSphere

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_CoeScalar
attribute [-instance] _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Rescaling.config_haar _root_.OAI.HardSphere.bridgeEndpointBase_finite _root_.OAI.HardSphere.coordinateBridge_probability _root_.OAI.HardSphere.endpointWeightedBase_sfinite _root_.OAI.HardSphere.freePathLaw_finite_deletion _root_.OAI.HardSphere.gaussianCoordinates_probability _root_.OAI.HardSphere.killedPathLaw_finite_deletion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
open ProbabilityTheory
namespace HardSphere
open MeasureTheory Set Filter
open scoped ComplexConjugate

lemma SmoothMultiplier.coe_onScalar {n : ℕ} {L : Length} (f : SmoothMultiplier n L) (u : ScalarL2 n L) :
    f.onScalar u =ᵐ[volume] fun X ↦ f.toFun X*u X := L2Multiplier.coe_clm _ _ _

lemma SmoothMultiplier.coe_derivativeScalar {n : ℕ} {L : Length} (f : SmoothMultiplier n L)
    (p : Direction n) (u : ScalarL2 n L) :
    f.derivativeScalar p u =ᵐ[volume] fun X ↦ coordDerivative n L f.toFun p X*u X :=
  L2Multiplier.coe_clm _ _ _

end HardSphere

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_LabelLift
attribute [-instance] _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Rescaling.config_haar _root_.OAI.HardSphere.bridgeEndpointBase_finite _root_.OAI.HardSphere.coordinateBridge_probability _root_.OAI.HardSphere.endpointWeightedBase_sfinite _root_.OAI.HardSphere.freePathLaw_finite_deletion _root_.OAI.HardSphere.gaussianCoordinates_probability _root_.OAI.HardSphere.killedPathLaw_finite_deletion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
open ProbabilityTheory
namespace HardSphere
open MeasureTheory Set Filter
open scoped ComplexConjugate

lemma SmoothMultiplier.partial_liftLabel {L : Length} (w : SmoothMultiplier 1 L)
    (n : ℕ) (i : Fin n) (p : Direction n) (X : Configuration n L) :
    coordDerivative n L (w.liftLabel n i).toFun p X=
      if p.1=i then coordDerivative 1 L w.toFun (0,p.2) (fun _ ↦ X i) else 0 := by
  classical
  have h := (w.smooth.differentiable (by simp)
    (labelLift n i (representative n L X))).hasFDerivAt.comp
    (representative n L X) (labelLift n i).hasFDerivAt
  change (fderiv ℝ ((fun Y : LiftedConfiguration 1 ↦ w.toFun (project 1 L Y)) ∘ labelLift n i)
    (representative n L X)) (Pi.single p.1 (Pi.single p.2 1))=_
  rw [h.fderiv,ContinuousLinearMap.comp_apply]
  by_cases hp : p.1=i
  · rw [ite_eq_left hp]
    have hd : labelLift n i (Pi.single p.1 (Pi.single p.2 1))=Pi.single 0 (Pi.single p.2 1) := by
      ext k j
      have hk : k=0 := Subsingleton.elim _ _
      subst k
      simp [labelLift,hp]
    rw [hd]
    rfl
  · rw [ite_eq_right hp]
    have hd : labelLift n i (Pi.single p.1 (Pi.single p.2 1))=0 := by
      ext k j
      simp [labelLift,Ne.symm hp]
    rw [hd,map_zero]

lemma SmoothMultiplier.partial_sum {S : Type*} [Fintype S] {n : ℕ} {L : Length}
    (w : S → SmoothMultiplier n L) (p : Direction n) (X : Configuration n L) :
    coordDerivative n L (SmoothMultiplier.sum w).toFun p X=∑ s, coordDerivative n L (w s).toFun p X := by
  unfold coordDerivative
  change (fderiv ℝ (fun Y ↦ ∑ s, (w s).toFun (project n L Y)) _) _ = _
  rw [fderiv_fun_sum (fun s _ ↦ (w s).smooth.differentiable (by simp) _),sum_apply]

end HardSphere

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_PartitionErrorIntegral
attribute [-instance] _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Rescaling.config_haar _root_.OAI.HardSphere.bridgeEndpointBase_finite _root_.OAI.HardSphere.coordinateBridge_probability _root_.OAI.HardSphere.endpointWeightedBase_sfinite _root_.OAI.HardSphere.freePathLaw_finite_deletion _root_.OAI.HardSphere.gaussianCoordinates_probability _root_.OAI.HardSphere.killedPathLaw_finite_deletion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
open ProbabilityTheory
open MeasureTheory Filter Set
open scoped ENNReal Topology
open MeasureTheory Set
open scoped ENNReal
namespace HardSphere
open MeasureTheory Set Filter
open scoped ComplexConjugate

lemma SmoothMultiplier.partition_error_integral {S : Type*} [Fintype S] {n : ℕ} {L : Length}
    (w : S → SmoothMultiplier n L) (u : ScalarL2 n L) :
    (∑ p : Direction n, ∑ s, ‖(w s).derivativeScalar p u‖^2)=
      ∫ X, (∑ p : Direction n, ∑ s, ‖coordDerivative n L (w s).toFun p X‖^2)*‖u X‖^2 := by
  simp_rw [IndicatorStrong.norm_sq_integral]
  have hi (p : Direction n) (s : S) :
      Integrable (fun X ↦ ‖((w s).derivativeScalar p u) X‖^2) volume :=
    (Lp.memLp _).integrable_norm_pow (by norm_num)
  simp_rw [← integral_finsetSum Finset.univ (fun s _ ↦ hi _ s)]
  rw [← integral_finsetSum Finset.univ (fun p _ ↦ integrable_finsetSum _ (fun s _ ↦ hi p s))]
  have hc : ∀ᵐ X ∂volume, ∀ p s, ((w s).derivativeScalar p u) X=
      coordDerivative n L (w s).toFun p X*u X :=
    ae_all_iff.mpr (fun p ↦ ae_all_iff.mpr (fun s ↦ (w s).coe_derivativeScalar p u))
  apply integral_congr_ae
  filter_upwards [hc] with X hX
  simp_rw [hX,norm_mul,mul_pow]
  simp only [Finset.sum_mul]

end HardSphere

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_SelectedEnergyAddCompl
attribute [-instance] _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Rescaling.config_haar _root_.OAI.HardSphere.bridgeEndpointBase_finite _root_.OAI.HardSphere.endpointWeightedBase_sfinite _root_.OAI.HardSphere.freePathLaw_finite_deletion _root_.OAI.HardSphere.killedPathLaw_finite_deletion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
open ProbabilityTheory
open MeasureTheory Filter Set
open scoped ENNReal Topology
open MeasureTheory Set
open scoped ENNReal

namespace HardSphere
open MeasureTheory Set Filter ContinuousLinearMap
open scoped Convolution NNReal

lemma lipschitz_spatialProject (L : Length) : LipschitzWith 1 (spatialProject L) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [NNReal.coe_one,one_mul]
  apply (dist_pi_le_iff (dist_nonneg : 0≤dist x y)).mpr
  intro j
  calc
    dist ((x j : ℝ) : AddCircle L.val) ((y j : ℝ) : AddCircle L.val)
      = ‖((x j-y j : ℝ) : AddCircle L.val)‖ := by rw [dist_eq_norm,QuotientAddGroup.mk_sub]
    _ ≤ ‖x j-y j‖ := QuotientAddGroup.norm_mk_le_norm
    _ ≤ dist x y := by rw [←dist_eq_norm]; exact dist_le_pi_dist x y j

lemma torusMollify_integrable (L : Length) (φ : ContDiffBump (0 : SpatialLift))
    (f : Torus L → ℝ) (hf : Continuous f) (x : Torus L) :
    Integrable (fun y : SpatialLift ↦ φ.normed volume y*f (x-spatialProject L y)) volume :=
  (φ.continuous_normed.mul (hf.comp (continuous_const.sub (continuous_spatialProject L)))).integrable_of_hasCompactSupport
    (φ.hasCompactSupport_normed.mul_right)

lemma torusMollify_lipschitz (L : Length) (φ : ContDiffBump (0 : SpatialLift))
    {f : Torus L → ℝ} {C : ℝ≥0} (hf : LipschitzWith C f) :
    LipschitzWith C (torusMollify L φ f) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [dist_eq_norm,torusMollify,torusMollify,← integral_sub
    (torusMollify_integrable L φ f hf.continuous x) (torusMollify_integrable L φ f hf.continuous y)]
  calc
    _ ≤ ∫ z : SpatialLift, φ.normed volume z*((C:ℝ)*dist x y) := by
      apply norm_integral_le_of_norm_le (φ.integrable_normed.mul_const _) (Eventually.of_forall ?_)
      intro z
      rw [←mul_sub,norm_mul,Real.norm_eq_abs,abs_of_nonneg (φ.nonneg_normed z)]
      apply mul_le_mul_of_nonneg_left _ (φ.nonneg_normed z)
      simpa only [←dist_eq_norm,dist_sub_right] using hf.dist_le_mul
        (x-spatialProject L z) (y-spatialProject L z)
    _ = (C:ℝ)*dist x y := by rw [integral_mul_const,φ.integral_normed,one_mul]

lemma torusMollify_approximation (L : Length) (φ : ContDiffBump (0 : SpatialLift))
    {f : Torus L → ℝ} {C : ℝ≥0} (hf : LipschitzWith C f) (x : Torus L) :
    dist (torusMollify L φ f x) (f x) ≤ (C:ℝ)*φ.rOut := by
  obtain ⟨z,hz⟩ : ∃ z : SpatialLift, spatialProject L z=x := by
    refine ⟨fun j ↦ ((AddCircle.equivIco L.val 0) (x j)).val,?_⟩
    ext j
    exact AddCircle.coe_equivIco
  rw [← hz,show torusMollify L φ f (spatialProject L z)=
    (φ.normed volume ⋆[lsmul ℝ ℝ,volume] (fun y ↦ f (spatialProject L y))) z from congrFun (torusMollify_lift L φ f) z]
  apply φ.dist_normed_convolution_le (hf.continuous.comp (continuous_spatialProject L)).aestronglyMeasurable
  intro y hy
  have hh : dist (f (spatialProject L y)) (f (spatialProject L z)) ≤ (C:ℝ)*dist y z := by
    simpa only [mul_one,Function.comp_apply] using (hf.comp (lipschitz_spatialProject L)).dist_le_mul y z
  exact hh.trans (mul_le_mul_of_nonneg_left (Metric.mem_ball.mp hy).le C.coe_nonneg)

end HardSphere

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_RealComp
attribute [-instance] _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Rescaling.config_haar _root_.OAI.HardSphere.bridgeEndpointBase_finite _root_.OAI.HardSphere.coordinateBridge_probability _root_.OAI.HardSphere.endpointWeightedBase_sfinite _root_.OAI.HardSphere.freePathLaw_finite_deletion _root_.OAI.HardSphere.gaussianCoordinates_probability _root_.OAI.HardSphere.killedPathLaw_finite_deletion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
open ProbabilityTheory
namespace HardSphere
open MeasureTheory Set Filter
open scoped ComplexConjugate

lemma SmoothMultiplier.partial_realComp {n : ℕ} {L : Length} (f : SmoothMultiplier n L)
    (φ : ℝ → ℝ) (hφ : ContDiff ℝ ((⊤:ℕ∞):WithTop ℕ∞) φ)
    (hf : ∀ X, conj (f.toFun X)=f.toFun X) (p : Direction n) (X : Configuration n L) :
    coordDerivative n L (f.realComp φ hφ).toFun p X=
      ((deriv φ (f.toFun X).re : ℝ) : ℂ)*coordDerivative n L f.toFun p X := by
  let R := representative n L X
  let v : LiftedConfiguration n := Pi.single p.1 (Pi.single p.2 (1:ℝ))
  have hline : HasDerivAt (fun t : ℝ ↦ R+t • v) v 0 := by
    simpa using ((hasDerivAt_id (0:ℝ)).smul_const v).const_add R
  have hdf := (f.smooth.differentiable (by simp) R).hasFDerivAt.comp_hasDerivAt_of_eq 0 hline (by simp)
  have hdφ := (hφ.differentiable (by simp) (f.toFun (project n L R)).re).hasDerivAt
  have hreal := Complex.reCLM.hasFDerivAt.comp_hasDerivAt 0 hdf
  have hchain := Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt 0 (hdφ.comp_of_eq 0 hreal (by simp))
  have hnew := ((f.realComp φ hφ).smooth.differentiable (by simp) R).hasFDerivAt.comp_hasDerivAt_of_eq
    0 hline (by simp)
  have he := hnew.unique hchain
  change coordDerivative n L (f.realComp φ hφ).toFun p X = _ at he
  simp only [Complex.ofRealCLM_apply,Complex.reCLM_apply] at he
  rw [show project n L R=X from project_representative n L X] at he
  have hder : ((coordDerivative n L f.toFun p X).re : ℂ)=coordDerivative n L f.toFun p X := by
    apply Complex.ext
    · rfl
    · have h := congrArg Complex.im (f.partial_real hf p X)
      simp only [Complex.conj_im] at h
      simp only [Complex.ofReal_im]
      linarith
  change _ = ((deriv φ (f.toFun X).re * (coordDerivative n L f.toFun p X).re : ℝ) : ℂ) at he
  rw [Complex.ofReal_mul,hder] at he
  exact he

end HardSphere

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Orbitals_Chi
attribute [-instance] _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Rescaling.config_haar _root_.OAI.HardSphere.bridgeEndpointBase_finite _root_.OAI.HardSphere.endpointWeightedBase_sfinite _root_.OAI.HardSphere.freePathLaw_finite_deletion _root_.OAI.HardSphere.killedPathLaw_finite_deletion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
open ProbabilityTheory
namespace HardSphere.CellOrbital
open MeasureTheory Set Filter PeriodicCutoff TightCutoff
open scoped ComplexConjugate

lemma dist_coord_le_torusDistance (L : Length) (x y : Torus L) (j : Fin 3) :
    dist (x j) (y j) ≤ torusDistance L x y := by
  calc
    _ = Real.sqrt (dist (x j) (y j)^2) := (Real.sqrt_sq (dist_nonneg)).symm
    _ ≤ _ := Real.sqrt_le_sqrt (Finset.single_le_sum
      (fun k _ ↦ sq_nonneg (dist (x k) (y k))) (Finset.mem_univ j))

end HardSphere.CellOrbital

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_EuclideanTorus
attribute [-instance] _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Rescaling.config_haar _root_.OAI.HardSphere.bridgeEndpointBase_finite _root_.OAI.HardSphere.coordinateBridge_probability _root_.OAI.HardSphere.endpointWeightedBase_sfinite _root_.OAI.HardSphere.freePathLaw_finite_deletion _root_.OAI.HardSphere.gaussianCoordinates_probability _root_.OAI.HardSphere.killedPathLaw_finite_deletion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
open ProbabilityTheory
open MeasureTheory Filter Set
open scoped ENNReal Topology
open MeasureTheory Set
open scoped ENNReal
namespace HardSphere
open MeasureTheory Set Filter ContinuousLinearMap
open scoped NNReal ComplexConjugate

lemma euclideanTorusPoint_dist (L : Length) (x y : Torus L) :
    dist (euclideanTorusPoint L x) (euclideanTorusPoint L y)=torusDistance L x y :=
  PiLp.dist_eq_of_L2 _ _

lemma spatialSiteDistance_nonneg (L : Length) (A : Finset (Torus L)) (x : Torus L) :
    0≤ spatialSiteDistance L A x := Metric.infDist_nonneg

lemma spatialSiteDistance_le (L : Length) (A : Finset (Torus L)) (x y : Torus L) (hy : y∈A) :
    spatialSiteDistance L A x≤torusDistance L x y := by
  rw [←euclideanTorusPoint_dist]
  exact Metric.infDist_le_dist_of_mem ⟨y,hy,rfl⟩

lemma spatialSiteDistance_attained (L : Length) (A : Finset (Torus L)) (hA : A.Nonempty) (x : Torus L) :
    ∃ y∈A, spatialSiteDistance L A x=torusDistance L x y := by
  have hc : IsCompact (euclideanTorusPoint L '' (A:Set (Torus L))) :=
    (A.finite_toSet.image _).isCompact
  obtain ⟨y,⟨z,hz,rfl⟩,he⟩ := hc.exists_infDist_eq_dist (by exact Set.Nonempty.image _ hA.to_set) (euclideanTorusPoint L x)
  exact ⟨z,hz,he.trans (euclideanTorusPoint_dist L x z)⟩

lemma smoothSpatialDistance_lipschitz (L : Length) (A : Finset (Torus L)) :
    LipschitzWith spatialMetricConstant (smoothSpatialDistance L A) :=
  torusMollify_lipschitz L _ (spatialSiteDistance_lipschitz L A)

lemma smoothSpatialDistance_approximation (L : Length) (A : Finset (Torus L)) (x : Torus L) :
    |smoothSpatialDistance L A x-spatialSiteDistance L A x|≤1 := by
  apply (torusMollify_approximation L spatialDistanceBump (spatialSiteDistance_lipschitz L A) x).trans
  change (spatialMetricConstant:ℝ)*(1/((spatialMetricConstant:ℝ)+1))≤1
  rw [mul_one_div,(div_le_one (by positivity : 0<(spatialMetricConstant:ℝ)+1))]
  linarith

lemma spatialDistanceMultiplier_apply (L : Length) (A : Finset (Torus L)) (X : Configuration 1 L) :
    (spatialDistanceMultiplier L A).toFun X=(smoothSpatialDistance L A (X 0):ℂ) := rfl

lemma spatialDistanceMultiplier_real (L : Length) (A : Finset (Torus L)) (X : Configuration 1 L) :
    conj ((spatialDistanceMultiplier L A).toFun X)=(spatialDistanceMultiplier L A).toFun X := by
  rw [spatialDistanceMultiplier_apply,Complex.conj_ofReal]

lemma spatialDistanceMultiplier_partial_bound (L : Length) (A : Finset (Torus L))
    (p : Direction 1) (X : Configuration 1 L) :
    ‖coordDerivative 1 L (spatialDistanceMultiplier L A).toFun p X‖≤ spatialMetricConstant := by
  have hLip : LipschitzWith spatialMetricConstant
      (fun Y : LiftedConfiguration 1 ↦ (spatialDistanceMultiplier L A).toFun (project 1 L Y)) := by
    apply LipschitzWith.of_dist_le_mul
    intro Y Z
    change dist ((smoothSpatialDistance L A (spatialProject L (Y 0))):ℂ)
      ((smoothSpatialDistance L A (spatialProject L (Z 0))):ℂ)≤_
    rw [dist_eq_norm,←Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs,←Real.dist_eq]
    apply ((smoothSpatialDistance_lipschitz L A).dist_le_mul _ _).trans
    apply mul_le_mul_of_nonneg_left _ spatialMetricConstant.coe_nonneg
    exact ((lipschitz_spatialProject L).dist_le_mul (Y 0) (Z 0)).trans
      (by simpa using dist_le_pi_dist Y Z 0)
  unfold coordDerivative
  apply (ContinuousLinearMap.le_opNorm _ _).trans
  have hv : ‖(Pi.single p.1 (Pi.single p.2 (1:ℝ)) : LiftedConfiguration 1)‖≤1 := by
    apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
    intro i
    by_cases hi : i=p.1
    · subst i
      simp only [Pi.single_eq_same]
      apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
      intro j
      by_cases hj : j=p.2
      · subst j; simp
      · simp [Pi.single_eq_of_ne hj]
    · simp [Pi.single_eq_of_ne hi]
  exact (mul_le_mul_of_nonneg_left hv (norm_nonneg _)).trans (by
    simpa only [mul_one] using norm_fderiv_le_of_lipschitz ℝ hLip)

end HardSphere

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_CenteredCircleLift
attribute [-instance] _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Rescaling.config_haar _root_.OAI.HardSphere.bridgeEndpointBase_finite _root_.OAI.HardSphere.endpointWeightedBase_sfinite _root_.OAI.HardSphere.freePathLaw_finite_deletion _root_.OAI.HardSphere.killedPathLaw_finite_deletion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
open ProbabilityTheory
open MeasureTheory Filter Set
open scoped ENNReal Topology
open MeasureTheory Set
open scoped ENNReal

namespace HardSphere
open MeasureTheory Set Filter

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nontrivial ι]

lemma torusDistance_triangle' (L : Length) (x y z : Torus L) :
    torusDistance L x z≤torusDistance L x y+torusDistance L y z := by
  simpa only [euclideanTorusPoint_dist] using dist_triangle
    (euclideanTorusPoint L x) (euclideanTorusPoint L y) (euclideanTorusPoint L z)

end HardSphere

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_RadiusLaw
attribute [-instance] _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Rescaling.config_haar _root_.OAI.HardSphere.bridgeEndpointBase_finite _root_.OAI.HardSphere.endpointWeightedBase_sfinite _root_.OAI.HardSphere.freePathLaw_finite_deletion _root_.OAI.HardSphere.killedPathLaw_finite_deletion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
open ProbabilityTheory
open MeasureTheory Filter Set
open scoped ENNReal Topology
open MeasureTheory Set
open scoped ENNReal

namespace HardSphere
open MeasureTheory Set Filter

lemma L2_bounded_weight_integrable {n : ℕ} {L : Length} (u : ScalarL2 n L)
    {v : Configuration n L → ℝ} {B : ℝ} (hv : Measurable v) (hb : ∀ X, |v X|≤B) :
    Integrable (fun X ↦ v X*‖u X‖^2) volume := by
  have hi := ((Lp.memLp u).integrable_norm_pow (by norm_num)).const_mul B
  apply hi.mono' (hv.mul ((Lp.stronglyMeasurable u).measurable.norm.pow_const 2)).aestronglyMeasurable
  exact Eventually.of_forall fun X ↦ by
    change ‖v X*‖u X‖^2‖≤B*‖u X‖^2
    rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg (sq_nonneg ‖u X‖)]
    exact mul_le_mul_of_nonneg_right (hb X) (sq_nonneg _)

lemma weightedSiteCount_nonneg {n : ℕ} (L : Length) (A : Finset (Torus L)) (X : Configuration n L) :
    0≤ weightedSiteCount L A X := by
  unfold weightedSiteCount
  split_ifs <;> positivity

lemma weightedSiteCount_le {n : ℕ} (L : Length) (A : Finset (Torus L)) (X : Configuration n L) :
    weightedSiteCount L A X≤(n:ℝ) := by
  unfold weightedSiteCount
  split_ifs
  · calc
      _ ≤ ∑ _i : Fin n, (1:ℝ) := Finset.sum_le_sum (fun i _ ↦ Real.exp_le_one_iff.mpr (neg_nonpos.mpr (spatialSiteDistance_nonneg L A _)))
      _ = _ := by simp
  · positivity

lemma weightedSiteCount_continuous {n : ℕ} (L : Length) (A : Finset (Torus L)) :
    Continuous (weightedSiteCount (n:=n) L A) := by
  unfold weightedSiteCount
  split_ifs
  · exact continuous_finsetSum _ (fun i _ ↦ Real.continuous_exp.comp
      (((spatialSiteDistance_lipschitz L A).continuous.comp (continuous_apply i)).neg))
  · exact continuous_const

end HardSphere

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_SmoothSiteWeight
attribute [-instance] _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Rescaling.config_haar _root_.OAI.HardSphere.bridgeEndpointBase_finite _root_.OAI.HardSphere.coordinateBridge_probability _root_.OAI.HardSphere.endpointWeightedBase_sfinite _root_.OAI.HardSphere.freePathLaw_finite_deletion _root_.OAI.HardSphere.gaussianCoordinates_probability _root_.OAI.HardSphere.killedPathLaw_finite_deletion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
open ProbabilityTheory
open MeasureTheory Filter Set
open scoped ENNReal Topology
open MeasureTheory Set
open scoped ENNReal
namespace HardSphere
open MeasureTheory Set Filter
open scoped ComplexConjugate

lemma smoothSiteWeight_pos (L : Length) (A : Finset (Torus L)) (x : Torus L) :
    0 < smoothSiteWeight L A x := Real.exp_pos _

lemma smoothSiteWeight_bounds (L : Length) (A : Finset (Torus L)) (x : Torus L) :
    Real.exp (-1)*Real.exp (-spatialSiteDistance L A x) ≤ smoothSiteWeight L A x ∧
    smoothSiteWeight L A x ≤ Real.exp 1*Real.exp (-spatialSiteDistance L A x) := by
  have h := abs_le.mp (smoothSpatialDistance_approximation L A x)
  constructor <;> rw [←Real.exp_add] <;> apply Real.exp_le_exp.mpr <;> linarith only [h.1,h.2]

lemma smoothSiteWeight_le (L : Length) (A : Finset (Torus L)) (x : Torus L) :
    smoothSiteWeight L A x ≤ Real.exp 1 := by
  apply (smoothSiteWeight_bounds L A x).2.trans
  exact mul_le_of_le_one_right (Real.exp_pos 1).le (Real.exp_le_one_iff.mpr (neg_nonpos.mpr (spatialSiteDistance_nonneg L A x)))

lemma smoothSiteWeightMultiplier_apply (L : Length) (A : Finset (Torus L)) (X : Configuration 1 L) :
    (smoothSiteWeightMultiplier L A).toFun X=(smoothSiteWeight L A (X 0):ℂ) := rfl

lemma smoothSiteWeight_continuous (L : Length) (A : Finset (Torus L)) : Continuous (smoothSiteWeight L A) :=
  Real.continuous_exp.comp (smoothSpatialDistance_lipschitz L A).continuous.neg

lemma smoothSiteWeight_partial_sq (L : Length) (A : Finset (Torus L)) (j : Fin 3) (x : Torus L) :
    ‖coordDerivative 1 L (smoothSiteWeightMultiplier L A).toFun (0,j) (fun _ ↦ x)‖^2 ≤
      ((spatialMetricConstant:ℝ)^2*Real.exp 1)*smoothSiteWeight L A x := by
  rw [smoothSiteWeightMultiplier,SmoothMultiplier.partial_realComp _ _ _ (spatialDistanceMultiplier_real L A)]
  have hd (t : ℝ) : deriv (fun t : ℝ ↦ Real.exp (-t)) t= -Real.exp (-t) := by
    simpa using (((hasDerivAt_id t).neg).exp).deriv
  rw [hd,norm_mul,mul_pow,Complex.norm_real,Real.norm_eq_abs,sq_abs]
  change (-smoothSiteWeight L A x)^2 * ‖coordDerivative 1 L (spatialDistanceMultiplier L A).toFun (0,j) (fun _ ↦ x)‖^2 ≤ _
  rw [neg_sq]
  have h := sq_le_sq₀ (norm_nonneg _) spatialMetricConstant.coe_nonneg |>.mpr
    (spatialDistanceMultiplier_partial_bound L A (0,j) (fun _ ↦ x))
  have hw := mul_le_mul_of_nonneg_left (smoothSiteWeight_le L A x) (smoothSiteWeight_pos L A x).le
  calc
    _ ≤ (smoothSiteWeight L A x)^2*(spatialMetricConstant:ℝ)^2 := mul_le_mul_of_nonneg_left h (sq_nonneg _)
    _ ≤ (Real.exp 1*smoothSiteWeight L A x)*(spatialMetricConstant:ℝ)^2 := by
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      nlinarith only [hw]
    _ = _ := by ring

lemma smoothWeightedCountMultiplier_apply (n : ℕ) (L : Length) (A : Finset (Torus L)) (X : Configuration n L) :
    (smoothWeightedCountMultiplier n L A).toFun X=(smoothWeightedCount L A X:ℂ) := by
  change (∑ i : Fin n, (smoothSiteWeightMultiplier L A).toFun (fun _ ↦ X i))=_
  simp_rw [smoothSiteWeightMultiplier_apply]
  exact (Complex.ofReal_sum _ _).symm

lemma smoothWeightedCountMultiplier_real (n : ℕ) (L : Length) (A : Finset (Torus L)) (X : Configuration n L) :
    conj ((smoothWeightedCountMultiplier n L A).toFun X)=(smoothWeightedCountMultiplier n L A).toFun X := by
  rw [smoothWeightedCountMultiplier_apply,Complex.conj_ofReal]

lemma smoothWeightedCount_nonneg {n : ℕ} (L : Length) (A : Finset (Torus L)) (X : Configuration n L) :
    0 ≤ smoothWeightedCount L A X := Finset.sum_nonneg (fun i _ ↦ (smoothSiteWeight_pos L A (X i)).le)

lemma smoothWeightedCount_le {n : ℕ} (L : Length) (A : Finset (Torus L)) (X : Configuration n L) :
    smoothWeightedCount L A X ≤ Real.exp 1*(n:ℝ) := by
  calc
    _ ≤ ∑ _i : Fin n, Real.exp 1 := Finset.sum_le_sum (fun i _ ↦ smoothSiteWeight_le L A (X i))
    _ = _ := by simp; ring

lemma smoothWeightedCount_bounds {n : ℕ} (L : Length) (A : Finset (Torus L)) (hA : A.Nonempty) (X : Configuration n L) :
    Real.exp (-1)*weightedSiteCount L A X ≤ smoothWeightedCount L A X ∧
    smoothWeightedCount L A X ≤ Real.exp 1*weightedSiteCount L A X := by
  simp only [weightedSiteCount,ite_eq_left hA,smoothWeightedCount,Finset.mul_sum]
  exact ⟨Finset.sum_le_sum (fun i _ ↦ (smoothSiteWeight_bounds L A (X i)).1),
    Finset.sum_le_sum (fun i _ ↦ (smoothSiteWeight_bounds L A (X i)).2)⟩

lemma smoothWeightedCount_continuous {n : ℕ} (L : Length) (A : Finset (Torus L)) :
    Continuous (smoothWeightedCount (n:=n) L A) :=
  continuous_finsetSum _ (fun i _ ↦ (smoothSiteWeight_continuous L A).comp (continuous_apply i))

lemma smoothWeightedCount_gradient {n : ℕ} (L : Length) (A : Finset (Torus L)) (X : Configuration n L) :
    (∑ p : Direction n, ‖coordDerivative n L (smoothWeightedCountMultiplier n L A).toFun p X‖^2) ≤
      (3*(spatialMetricConstant:ℝ)^2*Real.exp 1)*smoothWeightedCount L A X := by
  have hp (p : Direction n) : coordDerivative n L (smoothWeightedCountMultiplier n L A).toFun p X=
      coordDerivative 1 L (smoothSiteWeightMultiplier L A).toFun (0,p.2) (fun _ ↦ X p.1) := by
    classical
    rw [smoothWeightedCountMultiplier,SmoothMultiplier.partial_sum]
    simp_rw [SmoothMultiplier.partial_liftLabel]
    simp
  simp_rw [hp]
  rw [Fintype.sum_prod_type]
  calc
    _ ≤ ∑ i : Fin n, ∑ _j : Fin 3, ((spatialMetricConstant:ℝ)^2*Real.exp 1)*smoothSiteWeight L A (X i) := by
      exact Finset.sum_le_sum (fun i _ ↦ Finset.sum_le_sum (fun j _ ↦ smoothSiteWeight_partial_sq L A j (X i)))
    _ = _ := by
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,smoothWeightedCount,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring

end HardSphere

namespace HardSphere
open MeasureTheory Set Filter ProbabilityTheory

lemma groundPositionLaw_integral {n : ℕ} {L : Length} (u : Jet n L) (f : Configuration n L → ℝ) :
    (∫ X, f X ∂groundPositionLaw n L u)=∫ X, f X*‖u.1 X‖^2 := by
  rw [groundPositionLaw,integral_withDensity_eq_integral_toReal_smul
    (((Lp.stronglyMeasurable u.1).measurable.norm.pow_const 2).ennreal_ofReal)
    (Eventually.of_forall (fun _ ↦ ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (sq_nonneg _),smul_eq_mul,mul_comm]

lemma groundPositionLaw_probability {n : ℕ} {L : Length} (u : Jet n L) (hu : ‖u.1‖=1) :
    IsProbabilityMeasure (groundPositionLaw n L u) := by
  constructor
  rw [groundPositionLaw,withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ,
    ←ofReal_integral_eq_lintegral_ofReal
      ((Lp.memLp u.1).integrable_norm_pow (by norm_num : (2:ℕ)≠0))
      (Eventually.of_forall (fun X ↦ sq_nonneg ‖u.1 X‖)),←IndicatorStrong.norm_sq_integral,hu]
  norm_num

lemma bounded_mgf_integrable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    {F : Ω → ℝ} {B : ℝ} (hF : Measurable F) (hb : ∀ x, |F x| ≤B) (t : ℝ) :
    Integrable (fun x ↦ Real.exp (t*F x)) μ := by
  apply (integrable_const (Real.exp (|t| *B))).mono' (hF.const_mul t).exp.aestronglyMeasurable
  exact Eventually.of_forall (fun x ↦ by
    rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_exp.mpr
    calc
      t*F x ≤ |t*F x| := le_abs_self _
      _ = |t| *|F x| := abs_mul _ _
      _ ≤ |t| *B := mul_le_mul_of_nonneg_left (hb x) (abs_nonneg t))

lemma bounded_integrableExpSet {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    {F : Ω → ℝ} {B : ℝ} (hF : Measurable F) (hb : ∀ x, |F x| ≤B) :
    integrableExpSet F μ=univ := by
  ext t
  simp only [mem_univ,iff_true]
  exact bounded_mgf_integrable μ hF hb t

lemma bounded_cgf_le {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {F : Ω → ℝ} {B T C : ℝ} (hF : Measurable F) (hb : ∀ x, |F x| ≤B) (hT : 0≤T)
    (hd : ∀ t∈Icc 0 T, (∫ x, F x*Real.exp (t*F x) ∂μ)≤C*mgf F μ t) :
    ∀ t∈Icc 0 T, cgf F μ t≤C*t := by
  have hm (t : ℝ) : t∈interior (integrableExpSet F μ) := by rw [bounded_integrableExpSet μ hF hb,interior_univ]; trivial
  have hf : Differentiable ℝ (cgf F μ) := fun t ↦ (analyticAt_cgf (hm t)).differentiableAt
  have hd' (t : ℝ) (ht : t∈interior (Icc 0 T)) : deriv (cgf F μ) t≤C := by
    rw [deriv_cgf (hm t)]
    exact (div_le_iff₀ (mgf_pos (bounded_mgf_integrable μ hF hb t))).mpr (hd t (interior_subset ht))
  intro t ht
  have h := (convex_Icc (0:ℝ) T).image_sub_le_mul_sub_of_deriv_le hf.continuous.continuousOn
    hf.differentiableOn hd' 0 ⟨le_rfl,hT⟩ t ht ht.1
  simpa using h

end HardSphere

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_SpatialScalarSquare
attribute [-instance] _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Rescaling.config_haar _root_.OAI.HardSphere.bridgeEndpointBase_finite _root_.OAI.HardSphere.endpointWeightedBase_sfinite _root_.OAI.HardSphere.freePathLaw_finite_deletion _root_.OAI.HardSphere.killedPathLaw_finite_deletion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
open ProbabilityTheory
open MeasureTheory Filter Set
open scoped ENNReal Topology
open MeasureTheory Set
open scoped ENNReal
namespace HardSphere
open MeasureTheory Set Filter SphericalCoordinates
open scoped ENNReal

lemma weightedSiteCount_integrable {n : ℕ} (L : Length) (A : Finset (Torus L)) (u : ScalarL2 n L) :
    Integrable (fun X ↦ weightedSiteCount L A X*‖u X‖^2) volume :=
  L2_bounded_weight_integrable u (weightedSiteCount_continuous L A).measurable
    (fun X ↦ by rw [abs_of_nonneg (weightedSiteCount_nonneg L A X)]; exact weightedSiteCount_le L A X)

end HardSphere

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_ExpWeightedMultiplier
attribute [-instance] _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Rescaling.config_haar _root_.OAI.HardSphere.bridgeEndpointBase_finite _root_.OAI.HardSphere.coordinateBridge_probability _root_.OAI.HardSphere.endpointWeightedBase_sfinite _root_.OAI.HardSphere.freePathLaw_finite_deletion _root_.OAI.HardSphere.gaussianCoordinates_probability _root_.OAI.HardSphere.killedPathLaw_finite_deletion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
noncomputable section
open scoped BigOperators ComplexConjugate
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
noncomputable section
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
open ProbabilityTheory
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace HardSphere
open MeasureTheory Set Filter ProbabilityTheory
open scoped ComplexConjugate
noncomputable section

lemma expWeightedMultiplier_apply (n : ℕ) (L : Length) (A : Finset (Torus L)) (t : ℝ) (X : Configuration n L) :
    (expWeightedMultiplier n L A t).toFun X=(Real.exp (t*smoothWeightedCount L A X/2):ℂ) := by
  change (Real.exp (t*((smoothWeightedCountMultiplier n L A).toFun X).re/2):ℂ)=_
  rw [smoothWeightedCountMultiplier_apply,Complex.ofReal_re]

lemma expWeightedMultiplier_real (n : ℕ) (L : Length) (A : Finset (Torus L)) (t : ℝ) (X : Configuration n L) :
    conj ((expWeightedMultiplier n L A t).toFun X)=(expWeightedMultiplier n L A t).toFun X := by
  rw [expWeightedMultiplier_apply,Complex.conj_ofReal]

lemma expWeightedMultiplier_norm_sq (n : ℕ) (L : Length) (A : Finset (Torus L)) (t : ℝ) (X : Configuration n L) :
    ‖(expWeightedMultiplier n L A t).toFun X‖^2=Real.exp (t*smoothWeightedCount L A X) := by
  rw [expWeightedMultiplier_apply,Complex.norm_real,Real.norm_eq_abs,sq_abs,←Real.exp_nat_mul]
  congr 1
  ring

lemma expWeightedMultiplier_partial_sq (n : ℕ) (L : Length) (A : Finset (Torus L)) (t : ℝ)
    (p : Direction n) (X : Configuration n L) :
    ‖coordDerivative n L (expWeightedMultiplier n L A t).toFun p X‖^2=
      (t^2/4)*Real.exp (t*smoothWeightedCount L A X)*
        ‖coordDerivative n L (smoothWeightedCountMultiplier n L A).toFun p X‖^2 := by
  rw [expWeightedMultiplier,SmoothMultiplier.partial_realComp _ _ _ (smoothWeightedCountMultiplier_real n L A)]
  have hd (x : ℝ) : deriv (fun x : ℝ ↦ Real.exp (t*x/2)) x=(t/2)*Real.exp (t*x/2) := by
    simpa [mul_comm] using ((((hasDerivAt_id x).const_mul t).div_const 2).exp).deriv
  rw [hd,smoothWeightedCountMultiplier_apply,Complex.ofReal_re,norm_mul,mul_pow,
    Complex.norm_real,Real.norm_eq_abs,sq_abs,mul_pow,←Real.exp_nat_mul]
  congr 1
  congr 1
  · ring
  · congr 1; ring

lemma expWeightedMultiplier_gradient (n : ℕ) (L : Length) (A : Finset (Torus L)) (t : ℝ)
    (X : Configuration n L) :
    (∑ p : Direction n, ‖coordDerivative n L (expWeightedMultiplier n L A t).toFun p X‖^2)≤
      (t^2/4)*(3*(spatialMetricConstant:ℝ)^2*Real.exp 1)*
        (smoothWeightedCount L A X*Real.exp (t*smoothWeightedCount L A X)) := by
  simp_rw [expWeightedMultiplier_partial_sq,←Finset.mul_sum]
  apply (mul_le_mul_of_nonneg_left (smoothWeightedCount_gradient L A X)
    (by positivity : 0≤t^2/4*Real.exp (t*smoothWeightedCount L A X))).trans_eq
  ring

lemma SmoothMultiplier.error_integrable {n : ℕ} {L : Length} (f : SmoothMultiplier n L) (u : ScalarL2 n L) :
    Integrable (fun X ↦ (∑ p : Direction n, ‖coordDerivative n L f.toFun p X‖^2)*‖u X‖^2) volume := by
  have hi (p : Direction n) : Integrable (fun X ↦ ‖(f.derivativeScalar p u) X‖^2) volume :=
    (Lp.memLp _).integrable_norm_pow (by norm_num)
  apply (integrable_finsetSum Finset.univ (fun p _ ↦ hi p)).congr
  have hc : ∀ᵐ X ∂volume, ∀ p, (f.derivativeScalar p u) X=coordDerivative n L f.toFun p X*u X :=
    ae_all_iff.mpr (fun p ↦ f.coe_derivativeScalar p u)
  filter_upwards [hc] with X hX
  simp_rw [hX,norm_mul,mul_pow,Finset.sum_mul]

lemma SmoothMultiplier.error_integral {n : ℕ} {L : Length} (f : SmoothMultiplier n L) (u : ScalarL2 n L) :
    (∑ p : Direction n, ‖f.derivativeScalar p u‖^2)=
      ∫ X, (∑ p : Direction n, ‖coordDerivative n L f.toFun p X‖^2)*‖u X‖^2 := by
  simpa using SmoothMultiplier.partition_error_integral (fun _ : Unit ↦ f) u

lemma SmoothMultiplier.weighted_norm_integral {n : ℕ} {L : Length} (f : SmoothMultiplier n L)
    (u : ScalarL2 n L) (F : Configuration n L → ℝ) :
    (∫ X, F X*‖(f.onScalar u) X‖^2)=∫ X, F X*‖f.toFun X‖^2*‖u X‖^2 := by
  apply integral_congr_ae
  filter_upwards [f.coe_onScalar u] with X hX
  rw [hX,norm_mul,mul_pow,mul_assoc]

lemma expWeightedMultiplier_mass {n : ℕ} {L : Length} (A : Finset (Torus L)) (t : ℝ) (g : Jet n L) :
    ‖(expWeightedMultiplier n L A t).onScalar g.1‖^2=
      mgf (smoothWeightedCount L A) (groundPositionLaw n L g) t := by
  rw [IndicatorStrong.norm_sq_integral,mgf,groundPositionLaw_integral]
  apply integral_congr_ae
  filter_upwards [(expWeightedMultiplier n L A t).coe_onScalar g.1] with X hX
  rw [hX,norm_mul,mul_pow,expWeightedMultiplier_norm_sq]

lemma smoothWeightedCount_exp_integrable {n : ℕ} {L : Length} (A : Finset (Torus L)) (t : ℝ) (g : Jet n L) :
    Integrable (fun X ↦ (smoothWeightedCount L A X*Real.exp (t*smoothWeightedCount L A X))*‖g.1 X‖^2) volume := by
  let G := smoothWeightedCount (n:=n) L A
  let B := Real.exp 1*(n:ℝ)
  have hb (X : Configuration n L) : |G X| ≤ B := by
    rw [abs_of_nonneg (smoothWeightedCount_nonneg L A X)]
    exact smoothWeightedCount_le L A X
  apply L2_bounded_weight_integrable g.1
    ((smoothWeightedCount_continuous L A).measurable.mul
      (((smoothWeightedCount_continuous L A).measurable.const_mul t).exp))
  intro X
  change |G X*Real.exp (t*G X)| ≤ _
  rw [abs_mul,abs_of_pos (Real.exp_pos _)]
  exact mul_le_mul (hb X) (Real.exp_le_exp.mpr (calc
    t*G X ≤ |t*G X| := le_abs_self _
    _ = |t| *|G X| := abs_mul _ _
    _ ≤ |t| *B := mul_le_mul_of_nonneg_left (hb X) (abs_nonneg t)))
    (Real.exp_pos _).le (by dsimp [B]; positivity)

lemma expWeightedMultiplier_defect {n : ℕ} {L : Length} {r : ℝ} (A : Finset (Torus L)) (t : ℝ)
    {g : Jet n L} (hg : IsGroundVector n L r g) :
    energy ((expWeightedMultiplier n L A t).onJet g)-energy g*‖(expWeightedMultiplier n L A t).onScalar g.1‖^2≤
      (t^2/4)*(3*(spatialMetricConstant:ℝ)^2*Real.exp 1)*
        (∫ X, smoothWeightedCount L A X*Real.exp (t*smoothWeightedCount L A X) ∂groundPositionLaw n L g) := by
  rw [hg.smooth_multiplier_identity _ (expWeightedMultiplier_real n L A t),
    SmoothMultiplier.error_integral,groundPositionLaw_integral,←integral_const_mul]
  apply integral_mono ((expWeightedMultiplier n L A t).error_integrable g.1)
    ((smoothWeightedCount_exp_integrable A t g).const_mul _)
  intro X
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_right (expWeightedMultiplier_gradient n L A t X) (sq_nonneg ‖g.1 X‖)

end
end HardSphere

namespace HardSphere
open MeasureTheory Set Filter ProbabilityTheory
open scoped ComplexConjugate
noncomputable section

lemma exp_neg_one_mul_exp_one : Real.exp (-1)*Real.exp 1=1 := by rw [←Real.exp_add]; norm_num

lemma exp_one_mul_exp_neg_one : Real.exp 1*Real.exp (-1)=1 := by rw [mul_comm,exp_neg_one_mul_exp_one]

lemma smoothWeightedCount_lower_for_penalty {n : ℕ} (L : Length) (A : Finset (Torus L))
    (hA : A.Nonempty) (X : Configuration n L) :
    Real.exp (-1)*smoothWeightedCount L A X ≤ weightedSiteCount L A X := by
  have h := mul_le_mul_of_nonneg_left (smoothWeightedCount_bounds L A hA X).2 (Real.exp_pos (-1)).le
  rwa [←mul_assoc,exp_neg_one_mul_exp_one,one_mul] at h

lemma weightedSiteCount_le_smooth {n : ℕ} (L : Length) (A : Finset (Torus L))
    (hA : A.Nonempty) (X : Configuration n L) :
    weightedSiteCount L A X ≤ Real.exp 1*smoothWeightedCount L A X := by
  have h := mul_le_mul_of_nonneg_left (smoothWeightedCount_bounds L A hA X).1 (Real.exp_pos 1).le
  rwa [←mul_assoc,exp_one_mul_exp_neg_one,one_mul] at h

lemma expWeightedMultiplier_weight_integrable {n : ℕ} {L : Length} (A : Finset (Torus L))
    (t : ℝ) (g : Jet n L) :
    Integrable (fun X ↦ weightedSiteCount L A X*Real.exp (t*smoothWeightedCount L A X)*‖g.1 X‖^2) volume := by
  apply (weightedSiteCount_integrable L A ((expWeightedMultiplier n L A t).onScalar g.1)).congr
  filter_upwards [(expWeightedMultiplier n L A t).coe_onScalar g.1] with X hX
  rw [hX,norm_mul,mul_pow,expWeightedMultiplier_norm_sq,mul_assoc]

lemma expWeightedMultiplier_weight_lower {n : ℕ} {L : Length} (A : Finset (Torus L)) (hA : A.Nonempty)
    (t : ℝ) (g : Jet n L) :
    Real.exp (-1)*(∫ X, smoothWeightedCount L A X*Real.exp (t*smoothWeightedCount L A X) ∂groundPositionLaw n L g)≤
      ∫ X, weightedSiteCount L A X*‖((expWeightedMultiplier n L A t).onScalar g.1) X‖^2 := by
  rw [groundPositionLaw_integral,←integral_const_mul,SmoothMultiplier.weighted_norm_integral]
  simp_rw [expWeightedMultiplier_norm_sq]
  apply integral_mono ((smoothWeightedCount_exp_integrable A t g).const_mul _)
    (expWeightedMultiplier_weight_integrable A t g)
  intro X
  have h := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (smoothWeightedCount_lower_for_penalty L A hA X) (Real.exp_pos (t*smoothWeightedCount L A X)).le)
    (sq_nonneg ‖g.1 X‖)
  simpa only [mul_assoc] using h

end
end HardSphere

end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_KilledObservable
attribute [-instance] _root_.OAI.HardSphere.Bridge.exposedBridgeKernel_markov _root_.OAI.HardSphere.Bridge.exposedPeriodSingle_finite _root_.OAI.HardSphere.Bridge.exposedTrialKernel_markov _root_.OAI.HardSphere.Bridge.instBorelSpaceContinuousMapElemRealTimePoint _root_.OAI.HardSphere.Bridge.instIsProbabilityMeasureNoiseLaw _root_.OAI.HardSphere.Bridge.instMeasurableSpaceContinuousMapElemRealTimePoint _root_.OAI.HardSphere.Bridge.parameterBridgeKernel_markov _root_.OAI.HardSphere.Bridge.parameterIndividualReference_finite _root_.OAI.HardSphere.Bridge.parameterTrialKernel_markov _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Bridge.trialKernel_markov _root_.OAI.HardSphere.Groups.cellPathReference_probability _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Rescaling.config_haar _root_.OAI.HardSphere.Wiener.wiener_isGaussian _root_.OAI.HardSphere.bridgeEndpointBase_finite _root_.OAI.HardSphere.coordinateBridge_probability _root_.OAI.HardSphere.endpointWeightedBase_sfinite _root_.OAI.HardSphere.freePathLaw_finite_deletion _root_.OAI.HardSphere.gaussianCoordinates_probability _root_.OAI.HardSphere.killedPathLaw_finite_deletion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
namespace HardSphere
open Wiener
open scoped ComplexConjugate

lemma split_fixedTrajectory_measurable (N : ℕ) (L : Length) (s t : ℝ)
    (X : Configuration N L) :
    Measurable (fun p : CoordinatePaths N × CoordinatePaths N ↦
      (freeTrajectory N L s p.1 X,
        freeTrajectory N L t p.2 (freeTrajectory N L s p.1 X 1))) := by
  exact ((freeTrajectory_continuous N L s |>.comp (continuous_fst.prodMk continuous_const)).prodMk
    (freeTrajectory_continuous N L t |>.comp (continuous_snd.prodMk
      ((freeTrajectory_continuous N L s |>.comp (continuous_fst.prodMk continuous_const)).eval continuous_const)))).measurable

lemma split_fixedTrajectory (N : ℕ) (L : Length) (s t : ℝ) (hs : 0 < s) (ht : 0<t)
    (w : CoordinatePaths N) (X : Configuration N L) :
    (configurationPrefix N L (splitTime s t hs ht) (freeTrajectory N L (s+t) w X),
      configurationSuffix N L (splitTime s t hs ht) (freeTrajectory N L (s+t) w X)) =
      (freeTrajectory N L s (fun p ↦ normalizedPrefix (splitTime s t hs ht) (w p)) X,
        freeTrajectory N L t (fun p ↦ normalizedSuffix (splitTime s t hs ht) (w p))
          (freeTrajectory N L s (fun p ↦ normalizedPrefix (splitTime s t hs ht) (w p)) X 1)) := by
  apply Prod.ext
  · exact prefix_freeTrajectory N L s t hs ht w X
  · dsimp only [Prod.snd]
    rw [suffix_freeTrajectory N L s t hs ht]
    congr 1
    have heq := congrArg (fun ω : ConfigurationPath N L ↦ ω 1)
      (prefix_freeTrajectory N L s t hs ht w X)
    simpa only [configurationPrefix,ContinuousMap.comp_apply,prefixTime_one] using heq

end HardSphere

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_SmoothSpatialCountMgf
attribute [-instance] _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Rescaling.config_haar _root_.OAI.HardSphere.bridgeEndpointBase_finite _root_.OAI.HardSphere.coordinateBridge_probability _root_.OAI.HardSphere.endpointWeightedBase_sfinite _root_.OAI.HardSphere.freePathLaw_finite_deletion _root_.OAI.HardSphere.gaussianCoordinates_probability _root_.OAI.HardSphere.killedPathLaw_finite_deletion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
open ProbabilityTheory
open MeasureTheory Filter Set
open scoped ENNReal Topology
open MeasureTheory Set
open scoped ENNReal
namespace HardSphere
open MeasureTheory Set Filter ProbabilityTheory
open scoped ComplexConjugate

lemma smooth_spatial_count_mgf : ∃ C αstar : ℝ, 0 < C ∧ 0 < αstar ∧
    ∀ (n K : ℕ) (L : Length) (_hL : L.val=(K:ℝ)) (r D : ℝ),
      D=(n:ℝ)/L.val^3 → 1≤D → αstar≤D*r → 0 < r → 1≤L.val →
      (n:ℝ)*(2*Real.pi*r)^3≤L.val^3/2 →
    ∀ (g : Jet n L), IsGroundVector n L r g →
    ∀ (A : Finset (Torus L)), A.Nonempty → ∀ t∈Icc 0 (Real.exp 1),
      cgf (smoothWeightedCount L A) (groundPositionLaw n L g) t≤C*D*(A.card:ℝ)*t := by
  obtain ⟨C,hC,hp⟩ := weighted_count_penalty
  let e : ℝ := Real.exp 1
  let em : ℝ := Real.exp (-1)
  let H : ℝ := 3*(spatialMetricConstant:ℝ)^2*Real.exp 1
  let αstar : ℝ := 1+2*e^3*H
  have he : 0<e := Real.exp_pos _
  have hem : 0<em := Real.exp_pos _
  have hH : 0≤H := by dsimp [H]; positivity
  have hαstar : 0<αstar := by dsimp [αstar]; positivity
  have heem : e*em=1 := exp_one_mul_exp_neg_one
  have he3 : e^3*em=e^2 := by calc
    _ = e^2*(e*em) := by ring
    _ = e^2 := by rw [heem,mul_one]
  refine ⟨2*e*C,αstar,by positivity,hαstar,?_⟩
  intro n K L hL r D hDeq hD hα hr hsize hsmall g hg A hA
  let := groundPositionLaw_probability g hg.2.2.1
  have hα1 : 1≤D*r := by
    have h0 : 0≤2*e^3*H := by positivity
    dsimp [αstar] at hα
    linarith only [h0,hα]
  have hαpos : 0<D*r := zero_lt_one.trans_le hα1
  have hbG (X : Configuration n L) : |smoothWeightedCount L A X| ≤ e*(n:ℝ) := by
    rw [abs_of_nonneg (smoothWeightedCount_nonneg L A X)]
    exact smoothWeightedCount_le L A X
  apply bounded_cgf_le (groundPositionLaw n L g) (smoothWeightedCount_continuous L A).measurable hbG he.le
  intro t ht
  let f := expWeightedMultiplier n L A t
  let M := mgf (smoothWeightedCount L A) (groundPositionLaw n L g) t
  let R := ∫ X, smoothWeightedCount L A X*Real.exp (t*smoothWeightedCount L A X) ∂groundPositionLaw n L g
  have hR : 0≤R := integral_nonneg (fun X ↦ mul_nonneg (smoothWeightedCount_nonneg L A X) (Real.exp_pos _).le)
  have hpen := hp n K L hL r D hDeq hD hα1 hr hsize hsmall g hg A (f.onJet g) (f.onJet_mem_domain hg.1)
  have hlow := expWeightedMultiplier_weight_lower A hA t g
  have hdef := expWeightedMultiplier_defect A t hg
  change energy (f.onJet g)-energy g*‖f.onScalar g.1‖^2≤t^2/4*H*R at hdef
  change em*R≤∫ X, weightedSiteCount L A X*‖(f.onScalar g.1) X‖^2 at hlow
  change (D*r)*((∫ X, weightedSiteCount L A X*‖(f.onScalar g.1) X‖^2)-C*D*(A.card:ℝ)*‖f.onScalar g.1‖^2)≤
    energy (f.onJet g)-energy g*‖f.onScalar g.1‖^2 at hpen
  rw [show ‖f.onScalar g.1‖^2=M from expWeightedMultiplier_mass A t g] at hpen hdef
  have hbound : (D*r)*(em*R-C*D*(A.card:ℝ)*M)≤(t^2/4*H)*R := by
    have h := mul_le_mul_of_nonneg_left hlow hαpos.le
    nlinarith only [h,hpen,hdef]
  have ht2 : t^2≤e^2 := (sq_le_sq₀ ht.1 he.le).mpr ht.2
  have hαH : 2*e^3*H≤D*r := by
    dsimp [αstar] at hα
    linarith only [hα]
  have hαHem := mul_le_mul_of_nonneg_right hαH hem.le
  have heq : (2*e^3*H)*em=2*e^2*H := by
    calc
      _ = 2*H*(e^3*em) := by ring
      _ = _ := by rw [he3]; ring
  rw [heq] at hαHem
  have hc : t^2/4*H≤(D*r)*em/2 := by
    have htH := mul_le_mul_of_nonneg_right ht2 hH
    have hn : 0≤e^2*H := mul_nonneg (sq_nonneg _) hH
    nlinarith only [htH,hαHem,hn]
  have hmul := mul_le_mul_of_nonneg_right hc hR
  have hRbound : em*R≤2*(C*D*(A.card:ℝ))*M := by
    apply (mul_le_mul_iff_right₀ hαpos).mp
    nlinarith only [hbound,hmul]
  have h := mul_le_mul_of_nonneg_left hRbound he.le
  rw [←mul_assoc e em R,heem,one_mul] at h
  change R≤(2*e*C)*D*(A.card:ℝ)*M
  exact h.trans_eq (by ring)

theorem spatial_count_mgf : ∃ C αstar : ℝ, 0 < C ∧ 0 < αstar ∧
    ∀ (n K : ℕ) (L : Length) (_hL : L.val=(K:ℝ)) (r D : ℝ),
      D=(n:ℝ)/L.val^3 → 1≤D → αstar≤D*r → 0 < r → 1≤L.val →
      (n:ℝ)*(2*Real.pi*r)^3≤L.val^3/2 →
    ∀ (g : Jet n L), IsGroundVector n L r g →
    ∀ (A : Finset (Torus L)) (z : ℝ), 0≤z → z≤1 →
      Real.log (∫ X, Real.exp (z*weightedSiteCount L A X) ∂groundPositionLaw n L g)≤
        C*z*D*(A.card:ℝ) := by
  obtain ⟨C,αstar,hC,hαstar,hmgf⟩ := smooth_spatial_count_mgf
  refine ⟨C*Real.exp 1,αstar,by positivity,hαstar,?_⟩
  intro n K L hL r D hDeq hD hα hr hsize hsmall g hg A z hz hz'
  let := groundPositionLaw_probability g hg.2.2.1
  by_cases hA : A.Nonempty
  · have hbF (X : Configuration n L) : |weightedSiteCount L A X| ≤ (n:ℝ) := by
      rw [abs_of_nonneg (weightedSiteCount_nonneg L A X)]
      exact weightedSiteCount_le L A X
    have hbG (X : Configuration n L) : |smoothWeightedCount L A X| ≤ Real.exp 1*(n:ℝ) := by
      rw [abs_of_nonneg (smoothWeightedCount_nonneg L A X)]
      exact smoothWeightedCount_le L A X
    have hiF := bounded_mgf_integrable (groundPositionLaw n L g) (weightedSiteCount_continuous L A).measurable hbF z
    have hiG := bounded_mgf_integrable (groundPositionLaw n L g) (smoothWeightedCount_continuous L A).measurable hbG (Real.exp 1*z)
    have hlog : Real.log (∫ X, Real.exp (z*weightedSiteCount L A X) ∂groundPositionLaw n L g)≤
        cgf (smoothWeightedCount L A) (groundPositionLaw n L g) (Real.exp 1*z) := by
      apply Real.log_le_log (mgf_pos hiF)
      apply integral_mono hiF hiG
      intro X
      apply Real.exp_le_exp.mpr
      have h := mul_le_mul_of_nonneg_left (weightedSiteCount_le_smooth L A hA X) hz
      exact h.trans_eq (by ring)
    apply hlog.trans
    have ht : Real.exp 1*z∈Icc 0 (Real.exp 1) := ⟨mul_nonneg (Real.exp_pos _).le hz,
      by simpa using mul_le_mul_of_nonneg_left hz' (Real.exp_pos 1).le⟩
    exact (hmgf n K L hL r D hDeq hD hα hr hsize hsmall g hg A hA (Real.exp 1*z) ht).trans_eq (by ring)
  · have he : A=∅ := Finset.not_nonempty_iff_eq_empty.mp hA
    subst A
    simp [weightedSiteCount]

end HardSphere

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_PathBounds_VisitPacking
attribute [-instance] _root_.OAI.HardSphere.Bridge.exposedBridgeKernel_markov _root_.OAI.HardSphere.Bridge.exposedPeriodSingle_finite _root_.OAI.HardSphere.Bridge.exposedTrialKernel_markov _root_.OAI.HardSphere.Bridge.instBorelSpaceContinuousMapElemRealTimePoint _root_.OAI.HardSphere.Bridge.instIsProbabilityMeasureNoiseLaw _root_.OAI.HardSphere.Bridge.instMeasurableSpaceContinuousMapElemRealTimePoint _root_.OAI.HardSphere.Bridge.parameterBridgeKernel_markov _root_.OAI.HardSphere.Bridge.parameterIndividualReference_finite _root_.OAI.HardSphere.Bridge.parameterTrialKernel_markov _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Bridge.trialKernel_markov _root_.OAI.HardSphere.Groups.cellPathReference_probability _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Lattice.environmentMeasurableSpace _root_.OAI.HardSphere.Lattice.simplePathCountable _root_.OAI.HardSphere.Lattice.simplePathMeasurableSpace _root_.OAI.HardSphere.Rescaling.config_haar _root_.OAI.HardSphere.Wiener.wiener_isGaussian _root_.OAI.HardSphere.bridgeEndpointBase_finite _root_.OAI.HardSphere.coordinateBridge_probability _root_.OAI.HardSphere.endpointWeightedBase_sfinite _root_.OAI.HardSphere.freePathLaw_finite_deletion _root_.OAI.HardSphere.killedPathLaw_finite_deletion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.FreeVisits
open HardSphere.BathSlice HardSphere.Lattice HardSphere.CellOrbital

lemma card_packingBox (c : Fin 3 → ℝ) : (packingBox c).card=29^3 := by
  unfold packingBox
  rw [Pi.card_Icc]
  have hc (j : Fin 3) : (Finset.Icc (⌊c j-1/2⌋-14) (⌊c j-1/2⌋+14)).card=29 := by
    rw [Int.card_Icc]
    omega
  simp only [hc,Finset.prod_const,Finset.card_univ,Fintype.card_fin]

lemma site_packing_witness {K : ℕ} [NeZero K] (L : Length) (hL : L.val=(K:ℝ))
    (c : Fin 3 → ℝ) (v : DiscreteTorus K)
    (hv : ∀ j, dist (siteCenter L v j) ((c j:ℝ):AddCircle L.val)≤13) :
    ∃ z ∈ packingBox c, torusProjection K z=v := by
  let k : Vertex := fun j ↦ round (L.val⁻¹*((((v j).val:ℝ)+1/2)-c j))
  let z : Vertex := fun j ↦ ((v j).val:ℤ)-k j*(K:ℤ)
  refine ⟨z,?_,?_⟩
  · apply Finset.mem_Icc.mpr
    have hz (j : Fin 3) : ⌊c j-1/2⌋-14 ≤ z j ∧ z j ≤ ⌊c j-1/2⌋+14 := by
      have hd := hv j
      change dist ((((v j).val:ℝ)+1/2:ℝ):AddCircle L.val) ((c j:ℝ):AddCircle L.val)≤13 at hd
      rw [dist_eq_norm,←AddCircle.coe_sub,AddCircle.norm_eq] at hd
      have hd' : |(z j:ℝ)-(c j-1/2)|≤13 := by
        convert hd using 1
        all_goals try with_reducible_and_instances rfl
        dsimp [z,k]
        push_cast
        rw [hL]
        ring_nf
      have hl := Int.floor_le (c j-1/2)
      have hu := Int.lt_floor_add_one (c j-1/2)
      obtain ⟨h₁,h₂⟩ := abs_le.mp hd'
      constructor <;> (apply (Int.cast_le (R := ℝ)).mp; push_cast; linarith)
    exact ⟨fun j ↦ (hz j).1,fun j ↦ (hz j).2⟩
  · ext j
    simp [torusProjection,z]

lemma card_near_sites_le {K : ℕ} [NeZero K] (L : Length) (hL : L.val=(K:ℝ))
    (x : Torus L) (A : Finset (DiscreteTorus K))
    (hA : ∀ v∈A, ∀ j, dist (siteCenter L v j) (x j)≤13) : A.card≤29^3 := by
  classical
  let c : Fin 3 → ℝ := fun j ↦ (AddCircle.equivIco L.val 0 (x j)).val
  have hc (j : Fin 3) : ((c j:ℝ):AddCircle L.val)=x j := AddCircle.coe_equivIco
  have hsub : A ⊆ (packingBox c).image (torusProjection K) := by
    intro v hv
    obtain ⟨z,hz,he⟩ := site_packing_witness L hL c v (fun j ↦ by rw [hc]; exact hA v hv j)
    exact Finset.mem_image.mpr ⟨z,hz,he⟩
  exact (Finset.card_le_card hsub).trans ((Finset.card_image_le).trans (le_of_eq (card_packingBox c)))
end HardSphere.FreeVisits

namespace HardSphere
open MeasureTheory Wiener Set
attribute [local irreducible] torusDistance

lemma pathVisitsBall_isClosed {n : ℕ} (L : Length) (R : ℝ) (v : Torus L) (i : Fin n) :
    IsClosed {ω : ConfigurationPath n L | pathVisitsBall L R v i ω} := by
  have hc : Continuous (fun p : ConfigurationPath n L × Time ↦ torusDistance L (p.1 p.2 i) v) := by
    have he : Continuous (fun p : ConfigurationPath n L × Time ↦ p.1 p.2 i) :=
      (continuous_apply i).comp (continuous_eval : Continuous (fun p : ConfigurationPath n L × Time ↦ p.1 p.2))
    exact (continuous_torusDistance L).comp (he.prodMk continuous_const)
  have hs := isClosedMap_fst_of_compactSpace
    {p : ConfigurationPath n L × Time | torusDistance L (p.1 p.2 i) v ≤ R}
    (isClosed_le hc continuous_const)
  convert hs using 1
  all_goals try with_reducible_and_instances rfl
  ext ω
  simp only [pathVisitsBall,Set.mem_ofPred_eq,Set.mem_image,Prod.exists]
  constructor
  · rintro ⟨q,hq⟩
    exact ⟨ω,q,hq,rfl⟩
  · rintro ⟨ω',q,hq,rfl⟩
    exact ⟨q,hq⟩

lemma pathVisitedSites_measurable {S : Type*} {n : ℕ} (L : Length)
    (v : S → Torus L) (A : Finset S) (i : Fin n) :
    Measurable (fun ω : ConfigurationPath n L ↦ ((pathVisitedSites L v A i ω).card:ℝ)) := by
  classical
  simp only [pathVisitedSites,Finset.card_filter,Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero]
  apply Finset.measurable_sum
  intro a _
  exact Measurable.ite (pathVisitsBall_isClosed L 12 (v a) i).measurableSet
    measurable_const measurable_const

end HardSphere

namespace HardSphere.FreeVisits
open HardSphere.BathSlice HardSphere.Lattice HardSphere.CellOrbital HardSphere.Wiener

lemma visited_subset_near {n K : ℕ} [NeZero K] (L : Length) (A : Finset (DiscreteTorus K))
    (i : Fin n) (ω : ConfigurationPath n L) (x : Torus L)
    (hω : ∀ (u : Time) (j : Fin 3), dist (ω u i j) (x j)≤1) :
    ∀ v∈pathVisitedSites L (siteCenter L) A i ω, ∀ j, dist (siteCenter L v j) (x j)≤13 := by
  classical
  intro v hv j
  obtain ⟨_,u,hu⟩ := Finset.mem_filter.mp hv
  have hc := dist_coord_le_torusDistance L (ω u i) (siteCenter L v) j
  calc
    dist (siteCenter L v j) (x j) ≤ dist (siteCenter L v j) (ω u i j)+dist (ω u i j) (x j) := dist_triangle _ _ _
    _ ≤ 12+1 := add_le_add (by rw [dist_comm]; exact hc.trans hu) (hω u j)
    _ = 13 := by norm_num

lemma visited_card_le_of_short {n K : ℕ} [NeZero K] (L : Length) (hL : L.val=(K:ℝ))
    (A : Finset (DiscreteTorus K)) (i : Fin n) (ω : ConfigurationPath n L) (x : Torus L)
    (hω : ∀ (u : Time) (j : Fin 3), dist (ω u i j) (x j)≤1) :
    (pathVisitedSites L (siteCenter L) A i ω).card≤29^3 :=
  card_near_sites_le L hL x _ (visited_subset_near L A i ω x hω)

lemma visited_split {S : Type*} [DecidableEq S] {n : ℕ} (L : Length) (v : S → Torus L)
    (A : Finset S) (i : Fin n) (ω : ConfigurationPath n L)
    (u : Time) (hu : 0<(u:ℝ)) (hu' : (u:ℝ)<1) :
    pathVisitedSites L v A i ω = pathVisitedSites L v A i (configurationPrefix n L u ω) ∪
      pathVisitedSites L v A i (configurationSuffix n L u ω) := by
  classical
  ext a
  rw [Finset.mem_union]
  constructor
  · intro hav
    obtain ⟨ha,q,hq⟩ := Finset.mem_filter.mp hav
    by_cases hq' : (q:ℝ)≤u
    · let z : Time := ⟨(q:ℝ)/(u:ℝ),div_nonneg q.property.1 hu.le,(div_le_one hu).mpr hq'⟩
      have hz : prefixTime u z=q := by
        apply Subtype.ext
        change (u:ℝ)*((q:ℝ)/(u:ℝ))=(q:ℝ)
        field_simp
      exact Or.inl (Finset.mem_filter.mpr ⟨ha,z,by simpa only [configurationPrefix,ContinuousMap.comp_apply,hz] using hq⟩)
    · let z : Time := ⟨((q:ℝ)-(u:ℝ))/(1-(u:ℝ)),
          div_nonneg (sub_nonneg.mpr (le_of_not_ge hq')) (sub_pos.mpr hu').le,
          (div_le_one (sub_pos.mpr hu')).mpr (by linarith [q.property.2])⟩
      have hz : suffixTime u z=q := by
        apply Subtype.ext
        change (u:ℝ)+(1-(u:ℝ))*(((q:ℝ)-(u:ℝ))/(1-(u:ℝ)))=(q:ℝ)
        field_simp [ne_of_gt (sub_pos.mpr hu')]
        ring
      exact Or.inr (Finset.mem_filter.mpr ⟨ha,z,by simpa only [configurationSuffix,ContinuousMap.comp_apply,hz] using hq⟩)
  · rintro (hav|hav)
    · obtain ⟨ha,q,hq⟩ := Finset.mem_filter.mp hav
      exact Finset.mem_filter.mpr ⟨ha,prefixTime u q,hq⟩
    · obtain ⟨ha,q,hq⟩ := Finset.mem_filter.mp hav
      exact Finset.mem_filter.mpr ⟨ha,suffixTime u q,hq⟩

lemma visited_card_split_le {S : Type*} {n : ℕ} (L : Length) (v : S → Torus L)
    (A : Finset S) (i : Fin n) (ω : ConfigurationPath n L)
    (u : Time) (hu : 0<(u:ℝ)) (hu' : (u:ℝ)<1) :
    (pathVisitedSites L v A i ω).card ≤ (pathVisitedSites L v A i (configurationPrefix n L u ω)).card +
      (pathVisitedSites L v A i (configurationSuffix n L u ω)).card := by
  classical
  rw [visited_split L v A i ω u hu hu']
  exact Finset.card_union_le _ _

lemma freeTrajectory_coord_dist_le {n : ℕ} (L : Length) (t : ℝ) (w : CoordinatePaths n)
    (X : Configuration n L) (i : Fin n) (u : Time) (j : Fin 3) :
    dist (freeTrajectory n L t w X u i j) (X i j) ≤ Real.sqrt (2*t)*‖w (i,j)‖ := by
  change dist (X i j+((Real.sqrt (2*t)*w (i,j) u:ℝ):AddCircle L.val)) (X i j) ≤ _
  simp only [dist_eq_norm,add_sub_cancel_left]
  calc
    ‖((Real.sqrt (2*t)*w (i,j) u:ℝ):AddCircle L.val)‖ ≤ ‖Real.sqrt (2*t)*w (i,j) u‖ :=
      QuotientAddGroup.norm_mk_le_norm
    _ = Real.sqrt (2*t)*|w (i,j) u| := by rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg (Real.sqrt_nonneg _)]
    _ ≤ _ := mul_le_mul_of_nonneg_left (by simpa only [Real.norm_eq_abs] using ContinuousMap.norm_coe_le_norm (w (i,j)) u) (Real.sqrt_nonneg _)

lemma free_visited_card_le_of_norm {n K : ℕ} [NeZero K] (L : Length) (hL : L.val=(K:ℝ))
    (A : Finset (DiscreteTorus K)) (i : Fin n) (t : ℝ) (w : CoordinatePaths n)
    (X : Configuration n L) (hw : ∀ j, Real.sqrt (2*t)*‖w (i,j)‖≤1) :
    (pathVisitedSites L (siteCenter L) A i (freeTrajectory n L t w X)).card≤29^3 := by
  apply visited_card_le_of_short L hL A i _ (X i)
  exact fun u j ↦ (freeTrajectory_coord_dist_le L t w X i u j).trans (hw j)

end HardSphere.FreeVisits

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_PathBounds_FreeVisitProbability
attribute [-instance] _root_.OAI.HardSphere.Bridge.exposedBridgeKernel_markov _root_.OAI.HardSphere.Bridge.exposedPeriodSingle_finite _root_.OAI.HardSphere.Bridge.exposedTrialKernel_markov _root_.OAI.HardSphere.Bridge.instBorelSpaceContinuousMapElemRealTimePoint _root_.OAI.HardSphere.Bridge.instIsProbabilityMeasureNoiseLaw _root_.OAI.HardSphere.Bridge.instMeasurableSpaceContinuousMapElemRealTimePoint _root_.OAI.HardSphere.Bridge.parameterBridgeKernel_markov _root_.OAI.HardSphere.Bridge.parameterIndividualReference_finite _root_.OAI.HardSphere.Bridge.parameterTrialKernel_markov _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Bridge.trialKernel_markov _root_.OAI.HardSphere.Groups.cellPathReference_probability _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Lattice.environmentMeasurableSpace _root_.OAI.HardSphere.Lattice.simplePathCountable _root_.OAI.HardSphere.Lattice.simplePathMeasurableSpace _root_.OAI.HardSphere.Rescaling.config_haar _root_.OAI.HardSphere.Wiener.wiener_isGaussian _root_.OAI.HardSphere.bridgeEndpointBase_finite _root_.OAI.HardSphere.coordinateBridge_probability _root_.OAI.HardSphere.endpointWeightedBase_sfinite _root_.OAI.HardSphere.freePathLaw_finite_deletion _root_.OAI.HardSphere.gaussianCoordinates_probability _root_.OAI.HardSphere.killedPathLaw_finite_deletion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.FreeVisits
open HardSphere.BathSlice HardSphere.Lattice HardSphere.CellOrbital HardSphere.Wiener

lemma pathVisitedSites_card_measurable {S : Type*} {n : ℕ} (L : Length)
    (v : S → Torus L) (A : Finset S) (i : Fin n) :
    Measurable (fun ω : ConfigurationPath n L ↦ (pathVisitedSites L v A i ω).card) := by
  classical
  simp only [pathVisitedSites,Finset.card_filter]
  apply Finset.measurable_sum
  intro a _
  exact Measurable.ite (pathVisitsBall_isClosed L 12 (v a) i).measurableSet
    measurable_const measurable_const

lemma visitCount_measurable {n K : ℕ} (L : Length) (A : Finset (DiscreteTorus K)) (i : Fin n)
    (t : ℝ) (X : Configuration n L) : Measurable (visitCount L A i t X) :=
  (pathVisitedSites_card_measurable L (siteCenter L) A i).comp
    ((freeTrajectory_continuous n L t).comp (continuous_id.prodMk continuous_const)).measurable

lemma one_segment_visit_tail {c : ℝ} {M : ℝ≥0∞}
    (htail : ∀ R : ℝ, 0≤R → wiener {w | R≤‖w‖}≤M*ENNReal.ofReal (Real.exp (-c*R^2)))
    {n K : ℕ} [NeZero K] (L : Length) (hL : L.val=(K:ℝ))
    (A : Finset (DiscreteTorus K)) (i : Fin n) {t : ℝ} (ht : 0<t) (X : Configuration n L) :
    coordinateWiener n {w | 29^3<visitCount L A i t X w} ≤
      3*M*ENNReal.ofReal (Real.exp (-c/(2*t))) := by
  let R : ℝ := (Real.sqrt (2*t))⁻¹
  have hs : 0<Real.sqrt (2*t) := Real.sqrt_pos.mpr (by positivity)
  have hR : 0≤R := inv_nonneg.mpr hs.le
  have hsub : {w | 29^3<visitCount L A i t X w} ⊆
      ⋃ j : Fin 3, {w | R≤‖w (i,j)‖} := by
    intro w hw
    by_contra hnot
    have hn : ∀ j, ‖w (i,j)‖<R := by simpa only [Set.mem_iUnion,Set.mem_ofPred_eq,not_exists,not_le] using hnot
    have hb := free_visited_card_le_of_norm L hL A i t w X (fun j ↦ ?_)
    · exact (not_lt_of_ge hb) hw
    · calc
        Real.sqrt (2*t)*‖w (i,j)‖ ≤ Real.sqrt (2*t)*R := mul_le_mul_of_nonneg_left (hn j).le hs.le
        _ = 1 := mul_inv_cancel₀ (ne_of_gt hs)
  have he (j : Fin 3) : coordinateWiener n {w | R≤‖w (i,j)‖} = wiener {w | R≤‖w‖} := by
    exact (measurePreserving_eval (fun _ : Direction n ↦ wiener) (i,j)).measure_preimage
      (measurableSet_le measurable_const measurable_norm).nullMeasurableSet
  calc
    _ ≤ coordinateWiener n (⋃ j : Fin 3, {w | R≤‖w (i,j)‖}) := measure_mono hsub
    _ ≤ ∑' j : Fin 3, coordinateWiener n {w | R≤‖w (i,j)‖} := measure_iUnion_le _
    _ = 3 * wiener {w | R≤‖w‖} := by simp [he,tsum_fintype]
    _ ≤ 3*(M*ENNReal.ofReal (Real.exp (-c*R^2))) := mul_le_mul_right (htail R hR) _
    _ = _ := by
      dsimp [R]
      rw [inv_pow,Real.sq_sqrt (by positivity : 0≤2*t)]
      simp only [div_eq_mul_inv,mul_assoc]

lemma visit_count_split {n K : ℕ} (L : Length) (A : Finset (DiscreteTorus K)) (i : Fin n)
    {s t : ℝ} (hs : 0 < s) (ht : 0<t) (w : CoordinatePaths n) (X : Configuration n L) :
    visitCount L A i (s+t) X w ≤
      visitCount L A i s X (fun p ↦ normalizedPrefix (splitTime s t hs ht) (w p)) +
      visitCount L A i t
        (freeTrajectory n L s (fun p ↦ normalizedPrefix (splitTime s t hs ht) (w p)) X 1)
        (fun p ↦ normalizedSuffix (splitTime s t hs ht) (w p)) := by
  have hle := visited_card_split_le L (siteCenter L) A i (freeTrajectory n L (s+t) w X)
    (splitTime s t hs ht) (splitTime_pos s t hs ht) (splitTime_lt_one s t hs ht)
  have hp := congrArg Prod.fst (split_fixedTrajectory n L s t hs ht w X)
  have hq := congrArg Prod.snd (split_fixedTrajectory n L s t hs ht w X)
  dsimp only [Prod.fst,Prod.snd] at hp hq
  rw [hp,hq] at hle
  exact hle

attribute [local irreducible] freeTrajectory pathVisitedSites

lemma visit_tail_add {n K : ℕ} (L : Length) (A : Finset (DiscreteTorus K)) (i : Fin n)
    {s t : ℝ} (hs : 0 < s) (ht : 0<t) (a b : ℕ) (p q : ℝ≥0∞)
    (hsbound : ∀ X, coordinateWiener n {w | a<visitCount L A i s X w}≤p)
    (htbound : ∀ X, coordinateWiener n {w | b<visitCount L A i t X w}≤q)
    (X : Configuration n L) :
    coordinateWiener n {w | a+b<visitCount L A i (s+t) X w}≤p+q := by
  let u := splitTime s t hs ht
  let split : CoordinatePaths n → CoordinatePaths n × CoordinatePaths n := fun w ↦
    (fun p ↦ normalizedPrefix u (w p),fun p ↦ normalizedSuffix u (w p))
  let E₁ : Set (CoordinatePaths n × CoordinatePaths n) :=
    {p | a<visitCount L A i s X p.1}
  let E₂ : Set (CoordinatePaths n × CoordinatePaths n) :=
    {p | b<visitCount L A i t (freeTrajectory n L s p.1 X 1) p.2}
  have hE₁ : MeasurableSet E₁ := measurableSet_lt measurable_const
    ((visitCount_measurable L A i s X).comp measurable_fst)
  have hE₂ : MeasurableSet E₂ := by
    apply measurableSet_lt measurable_const
    exact (pathVisitedSites_card_measurable L (siteCenter L) A i).comp
      (measurable_snd.comp (split_fixedTrajectory_measurable n L s t X))
  have hsub : {w | a+b<visitCount L A i (s+t) X w} ⊆ split ⁻¹' (E₁∪E₂) := by
    intro w hw
    have hle := visit_count_split L A i hs ht w X
    change a<visitCount L A i s X (split w).1 ∨
      b<visitCount L A i t (freeTrajectory n L s (split w).1 X 1) (split w).2
    change a+b<visitCount L A i (s+t) X w at hw
    change visitCount L A i (s+t) X w ≤ visitCount L A i s X (split w).1 +
      visitCount L A i t (freeTrajectory n L s (split w).1 X 1) (split w).2 at hle
    omega
  have hp₁ : ((coordinateWiener n).prod (coordinateWiener n)) E₁≤p := by
    have he : E₁={w | a<visitCount L A i s X w} ×ˢ Set.univ := by ext v; simp [E₁]
    rw [he,Measure.prod_prod,measure_univ,mul_one]
    exact hsbound X
  have hp₂ : ((coordinateWiener n).prod (coordinateWiener n)) E₂≤q := by
    rw [Measure.prod_apply hE₂]
    calc
      _ ≤ ∫⁻ _w : CoordinatePaths n, q ∂coordinateWiener n := by
        apply lintegral_mono
        intro w
        exact htbound (freeTrajectory n L s w X 1)
      _ = q := by simp
  calc
    _ ≤ coordinateWiener n (split ⁻¹' (E₁∪E₂)) := measure_mono hsub
    _ = ((coordinateWiener n).prod (coordinateWiener n)) (E₁∪E₂) :=
      (coordinateSplit_preserving n u (splitTime_pos s t hs ht) (splitTime_lt_one s t hs ht)).measure_preimage
        (hE₁.union hE₂).nullMeasurableSet
    _ ≤ ((coordinateWiener n).prod (coordinateWiener n)) E₁ +
        ((coordinateWiener n).prod (coordinateWiener n)) E₂ := measure_union_le _ _
    _ ≤ p+q := add_le_add hp₁ hp₂

lemma n_segment_visit_tail {c : ℝ} {M : ℝ≥0∞}
    (htail : ∀ R : ℝ, 0≤R → wiener {w | R≤‖w‖}≤M*ENNReal.ofReal (Real.exp (-c*R^2)))
    {n K : ℕ} [NeZero K] (L : Length) (hL : L.val=(K:ℝ))
    (A : Finset (DiscreteTorus K)) (i : Fin n) {t : ℝ} (ht : 0<t) :
    ∀ k : ℕ, 0<k → ∀ X : Configuration n L,
      coordinateWiener n {w | 29^3*k<visitCount L A i ((k:ℝ)*t) X w} ≤
        (k:ℝ≥0∞)*(3*M*ENNReal.ofReal (Real.exp (-c/(2*t)))) := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base =>
    intro X
    simpa only [Nat.succ_eq_add_one,Nat.zero_add,Nat.cast_one,one_mul,mul_one] using one_segment_visit_tail htail L hL A i ht X
  | succ k hk ih =>
    intro X
    have hkt : 0<(k:ℝ)*t := mul_pos (by exact_mod_cast hk) ht
    have h := visit_tail_add L A i hkt ht (29^3*k) (29^3)
      ((k:ℝ≥0∞)*(3*M*ENNReal.ofReal (Real.exp (-c/(2*t)))))
      (3*M*ENNReal.ofReal (Real.exp (-c/(2*t)))) ih
      (fun X ↦ one_segment_visit_tail htail L hL A i ht X) X
    convert h using 1 <;> push_cast <;> ring_nf

lemma whole_time_visit_tail {c : ℝ} {M : ℝ≥0∞}
    (htail : ∀ R : ℝ, 0≤R → wiener {w | R≤‖w‖}≤M*ENNReal.ofReal (Real.exp (-c*R^2)))
    {n K : ℕ} [NeZero K] (L : Length) (hL : L.val=(K:ℝ))
    (A : Finset (DiscreteTorus K)) (i : Fin n) {t : ℝ} (ht : 0<t)
    (k : ℕ) (hk : 0<k) (X : Configuration n L) :
    coordinateWiener n {w | 29^3*k<visitCount L A i t X w} ≤
      (k:ℝ≥0∞)*(3*M*ENNReal.ofReal (Real.exp (-c*(k:ℝ)/(2*t)))) := by
  have hk' : (0:ℝ)<k := by exact_mod_cast hk
  have h := n_segment_visit_tail htail L hL A i (div_pos ht hk') k hk X
  have he : (k:ℝ)*(t/k)=t := mul_div_cancel₀ t (ne_of_gt hk')
  rw [he] at h
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  congr 3
  field_simp

end HardSphere.FreeVisits

end
end

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_PathBounds_ExpNatTail
attribute [-instance] _root_.OAI.HardSphere.Bridge.exposedBridgeKernel_markov _root_.OAI.HardSphere.Bridge.exposedPeriodSingle_finite _root_.OAI.HardSphere.Bridge.exposedTrialKernel_markov _root_.OAI.HardSphere.Bridge.instBorelSpaceContinuousMapElemRealTimePoint _root_.OAI.HardSphere.Bridge.instIsProbabilityMeasureNoiseLaw _root_.OAI.HardSphere.Bridge.instMeasurableSpaceContinuousMapElemRealTimePoint _root_.OAI.HardSphere.Bridge.parameterBridgeKernel_markov _root_.OAI.HardSphere.Bridge.parameterIndividualReference_finite _root_.OAI.HardSphere.Bridge.parameterTrialKernel_markov _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Bridge.trialKernel_markov _root_.OAI.HardSphere.Groups.cellPathReference_probability _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Lattice.environmentMeasurableSpace _root_.OAI.HardSphere.Lattice.simplePathCountable _root_.OAI.HardSphere.Lattice.simplePathMeasurableSpace _root_.OAI.HardSphere.Rescaling.config_haar _root_.OAI.HardSphere.bridgeEndpointBase_finite _root_.OAI.HardSphere.coordinateBridge_probability _root_.OAI.HardSphere.endpointWeightedBase_sfinite _root_.OAI.HardSphere.freePathLaw_finite_deletion _root_.OAI.HardSphere.gaussianCoordinates_probability _root_.OAI.HardSphere.killedPathLaw_finite_deletion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Set
open scoped ENNReal NNReal BigOperators
namespace HardSphere.FreeVisits

lemma exp_block_sum_bound (C J : ℕ) (hC : 0<C) {η : ℝ} (hη : 0≤η) :
    ENNReal.ofReal (Real.exp (η*(J:ℝ))) ≤ 1 + ∑' k : ℕ,
      if C*k<J then ENNReal.ofReal (Real.exp (η*(C:ℝ)*((k:ℝ)+1))) else 0 := by
  by_cases hJ : J=0
  · simp [hJ]
  · let k := (J-1)/C
    have hk : C*k<J := (Nat.mul_div_le (J-1) C).trans_lt (by omega)
    have hJle : J≤C*(k+1) := by
      have h:=Nat.lt_mul_div_succ (J-1) hC
      dsimp [k]
      omega
    have he : ENNReal.ofReal (Real.exp (η*(J:ℝ))) ≤
        ENNReal.ofReal (Real.exp (η*(C:ℝ)*((k:ℝ)+1))) := by
      apply ENNReal.ofReal_le_ofReal
      apply Real.exp_le_exp.mpr
      have hJle' : (J:ℝ)≤(C:ℝ)*((k:ℝ)+1) := by exact_mod_cast hJle
      nlinarith
    have hs : ENNReal.ofReal (Real.exp (η*(C:ℝ)*((k:ℝ)+1))) ≤ ∑' j : ℕ,
        if C*j<J then ENNReal.ofReal (Real.exp (η*(C:ℝ)*((j:ℝ)+1))) else 0 := by
      simpa only [ite_eq_left hk] using (ENNReal.le_tsum (f:=fun j : ℕ ↦ if C*j<J then
        ENNReal.ofReal (Real.exp (η*(C:ℝ)*((j:ℝ)+1))) else 0) k)
    exact he.trans (hs.trans le_add_self)

lemma weighted_exp_tail_le (C k : ℕ) (η : ℝ) :
    Real.exp (η*(C:ℝ)*((k:ℝ)+1)) * (k:ℝ) *
      Real.exp (-(η*(C:ℝ)+2)*(k:ℝ)) ≤
    Real.exp (η*(C:ℝ)) * Real.exp (-1)^k := by
  rw [← Real.exp_nat_mul]
  have hk : (k:ℝ)≤Real.exp (k:ℝ) := by have := Real.add_one_le_exp (k:ℝ); linarith
  calc
    _ = (k:ℝ)*Real.exp (η*(C:ℝ)-2*(k:ℝ)) := by
      rw [mul_right_comm,mul_comm _ (k:ℝ),←Real.exp_add]
      congr 2
      ring
    _ ≤ Real.exp (k:ℝ)*Real.exp (η*(C:ℝ)-2*(k:ℝ)) := mul_le_mul_of_nonneg_right hk (Real.exp_nonneg _)
    _ = _ := by rw [←Real.exp_add,←Real.exp_add]; congr 1; ring

lemma expTailBound_ne_top (C : ℕ) (η : ℝ) {a : ℝ≥0∞} (ha : a≠⊤) :
    expTailBound C η a≠⊤ := by
  have hr : ENNReal.ofReal (Real.exp (-1))<1 := by
    rw [ENNReal.ofReal_lt_one]
    exact Real.exp_lt_one_iff.mpr (by norm_num)
  exact ENNReal.add_ne_top.mpr ⟨by simp, ENNReal.mul_ne_top
    (ENNReal.add_ne_top.mpr ⟨ENNReal.ofReal_ne_top,ENNReal.mul_ne_top ENNReal.ofReal_ne_top ha⟩)
    (ENNReal.inv_ne_top.mpr (tsub_pos_iff_lt.mpr hr).ne')⟩

lemma lintegral_exp_nat_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (F : Ω → ℕ) (hF : Measurable F)
    (C : ℕ) (hC : 0<C) {η : ℝ} (hη : 0≤η) (a : ℝ≥0∞)
    (htail : ∀ k : ℕ, 0<k → μ {w | C*k<F w} ≤
      (k:ℝ≥0∞)*a*ENNReal.ofReal (Real.exp (-(η*(C:ℝ)+2)*(k:ℝ)))) :
    ∫⁻ w, ENNReal.ofReal (Real.exp (η*(F w:ℝ))) ∂μ ≤ expTailBound C η a := by
  classical
  let W : ℕ → Ω → ℝ≥0∞ := fun k ↦
    {w | C*k<F w}.indicator (fun _ ↦ ENNReal.ofReal (Real.exp (η*(C:ℝ)*((k:ℝ)+1))))
  have hW (k : ℕ) : Measurable (W k) := measurable_const.indicator
    (measurableSet_lt measurable_const hF)
  have hweight (index : ℕ) (sample : Ω) :
      W index sample = if C*index<F sample then
        ENNReal.ofReal (Real.exp (η*(C:ℝ)*((index:ℝ)+1))) else 0 := by
    by_cases hindex : C*index<F sample <;> simp [W,hindex]
  have hterm (k : ℕ) : (∫⁻ w,W k w ∂μ) ≤
      (ENNReal.ofReal (Real.exp (η*(C:ℝ)))+ENNReal.ofReal (Real.exp (η*(C:ℝ)))*a)*
        ENNReal.ofReal (Real.exp (-1))^k := by
    rw [show (∫⁻ w,W k w ∂μ) = ENNReal.ofReal (Real.exp (η*(C:ℝ)*((k:ℝ)+1))) * μ {w | C*k<F w} from
      lintegral_indicator_const (measurableSet_lt measurable_const hF) _]
    by_cases hk : k=0
    · subst k
      simpa only [Nat.cast_zero,zero_add,mul_one,pow_zero] using
        (mul_le_mul_right (prob_le_one (μ:=μ))
          (ENNReal.ofReal (Real.exp (η*(C:ℝ))))).trans (by simp)
    · have hb := htail k (Nat.pos_of_ne_zero hk)
      calc
        _ ≤ ENNReal.ofReal (Real.exp (η*(C:ℝ)*((k:ℝ)+1))) *
          ((k:ℝ≥0∞)*a*ENNReal.ofReal (Real.exp (-(η*(C:ℝ)+2)*(k:ℝ)))) := mul_le_mul_right hb _
        _ = a*ENNReal.ofReal (Real.exp (η*(C:ℝ)*((k:ℝ)+1))*(k:ℝ)*Real.exp (-(η*(C:ℝ)+2)*(k:ℝ))) := by
          simp only [ENNReal.ofReal_mul (Real.exp_nonneg _), ENNReal.ofReal_mul (mul_nonneg (Real.exp_nonneg _) (Nat.cast_nonneg k)),ENNReal.ofReal_natCast]
          ring
        _ ≤ a*ENNReal.ofReal (Real.exp (η*(C:ℝ))*Real.exp (-1)^k) :=
          mul_le_mul_right (ENNReal.ofReal_le_ofReal (weighted_exp_tail_le C k η)) _
        _ ≤ _ := by
          rw [ENNReal.ofReal_mul (Real.exp_nonneg _),ENNReal.ofReal_pow (Real.exp_nonneg _)]
          calc
            _ = (ENNReal.ofReal (Real.exp (η*(C:ℝ)))*a)*ENNReal.ofReal (Real.exp (-1))^k := by ring
            _ ≤ _ := by gcongr; exact le_add_self
  calc
    _ ≤ ∫⁻ w,1+∑' k,W k w ∂μ := lintegral_mono (fun w ↦ by
      simpa only [hweight] using exp_block_sum_bound C (F w) hC hη)
    _ = 1+∑' k,∫⁻ w,W k w ∂μ := by rw [lintegral_add_left measurable_const,lintegral_const,measure_univ,mul_one,lintegral_tsum (fun k ↦ (hW k).aemeasurable)]
    _ ≤ 1+∑' k,(ENNReal.ofReal (Real.exp (η*(C:ℝ)))+ENNReal.ofReal (Real.exp (η*(C:ℝ)))*a)*ENNReal.ofReal (Real.exp (-1))^k :=
      add_le_add_right (ENNReal.tsum_le_tsum hterm) _
    _ = _ := by rw [ENNReal.tsum_mul_left,ENNReal.tsum_geometric]; rfl

end HardSphere.FreeVisits

end

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.FreeVisits
open HardSphere.Wiener HardSphere.Lattice HardSphere.CellOrbital HardSphere.BathSlice
attribute [local irreducible] freeTrajectory pathVisitedSites

lemma visitWeight_measurable {n K : ℕ} (L : Length) (A : Finset (DiscreteTorus K)) (i : Fin n)
    (t η : ℝ) (X : Configuration n L) : Measurable (visitWeight L A i t η X) :=
  ((measurable_const.mul ((measurable_of_countable (fun k : ℕ ↦ (k:ℝ))).comp (visitCount_measurable L A i t X))).exp).ennreal_ofReal

lemma exp_nat_sum_le {a b c : ℕ} (h : a≤b+c) {η : ℝ} (hη : 0≤η) :
    ENNReal.ofReal (Real.exp (η*(a:ℝ))) ≤
      ENNReal.ofReal (Real.exp (η*(b:ℝ)))*ENNReal.ofReal (Real.exp (η*(c:ℝ))) := by
  rw [←ENNReal.ofReal_mul (Real.exp_nonneg _),←Real.exp_add]
  apply ENNReal.ofReal_le_ofReal
  apply Real.exp_le_exp.mpr
  have h' : (a:ℝ)≤(b:ℝ)+(c:ℝ) := by exact_mod_cast h
  nlinarith

lemma visit_moment_add {n K : ℕ} (L : Length) (A : Finset (DiscreteTorus K)) (i : Fin n)
    {s t η : ℝ} (hs : 0 < s) (ht : 0<t) (hη : 0≤η) (p q : ℝ≥0∞)
    (hsbound : ∀ X, ∫⁻ w,visitWeight L A i s η X w ∂coordinateWiener n ≤p)
    (htbound : ∀ X, ∫⁻ w,visitWeight L A i t η X w ∂coordinateWiener n ≤q)
    (X : Configuration n L) :
    ∫⁻ w,visitWeight L A i (s+t) η X w ∂coordinateWiener n ≤p*q := by
  let F : CoordinatePaths n × CoordinatePaths n → ℝ≥0∞ := fun w ↦
    visitWeight L A i s η X w.1 * visitWeight L A i t η (freeTrajectory n L s w.1 X 1) w.2
  have hG : Measurable (fun w : CoordinatePaths n × CoordinatePaths n ↦
      visitWeight L A i t η (freeTrajectory n L s w.1 X 1) w.2) := by
    change Measurable (fun w : CoordinatePaths n × CoordinatePaths n ↦
      ENNReal.ofReal (Real.exp (η*((pathVisitedSites L (siteCenter L) A i
        (freeTrajectory n L t w.2 (freeTrajectory n L s w.1 X 1))).card:ℝ))))
    exact (measurable_const.mul ((measurable_of_countable (fun k : ℕ ↦ (k:ℝ))).comp
      ((pathVisitedSites_card_measurable L (siteCenter L) A i).comp
        (measurable_snd.comp (split_fixedTrajectory_measurable n L s t X))))).exp.ennreal_ofReal
  have hF : Measurable F := ((visitWeight_measurable L A i s η X).comp measurable_fst).mul hG
  calc
    _ ≤ ∫⁻ w,F (fun p ↦ normalizedPrefix (splitTime s t hs ht) (w p),
          fun p ↦ normalizedSuffix (splitTime s t hs ht) (w p)) ∂coordinateWiener n :=
      lintegral_mono (fun w ↦ exp_nat_sum_le (visit_count_split L A i hs ht w X) hη)
    _ = ∫⁻ w,F w ∂(coordinateWiener n).prod (coordinateWiener n) :=
      (coordinateSplit_preserving n (splitTime s t hs ht)
        (splitTime_pos s t hs ht) (splitTime_lt_one s t hs ht)).lintegral_comp hF
    _ = ∫⁻ w₁,∫⁻ w₂,F (w₁,w₂) ∂coordinateWiener n ∂coordinateWiener n :=
      lintegral_prod _ hF.aemeasurable
    _ ≤ ∫⁻ w₁,visitWeight L A i s η X w₁*q ∂coordinateWiener n := by
      apply lintegral_mono
      intro w₁
      dsimp only [F]
      rw [lintegral_const_mul _ (visitWeight_measurable L A i t η _)]
      exact mul_le_mul_right (htbound _) _
    _ = (∫⁻ w,visitWeight L A i s η X w ∂coordinateWiener n)*q :=
      lintegral_mul_const _ (visitWeight_measurable L A i s η X)
    _ ≤ p*q := mul_le_mul_left (hsbound X) _

lemma n_segment_visit_moment {n K : ℕ} (L : Length) (A : Finset (DiscreteTorus K)) (i : Fin n)
    {t η : ℝ} (ht : 0<t) (hη : 0≤η) (B : ℝ≥0∞)
    (hbound : ∀ X, ∫⁻ w,visitWeight L A i t η X w ∂coordinateWiener n ≤ B) :
    ∀ k : ℕ, 0<k → ∀ X,
      ∫⁻ w,visitWeight L A i ((k:ℝ)*t) η X w ∂coordinateWiener n ≤ B^k := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base => simpa only [Nat.succ_eq_add_one,Nat.zero_add,Nat.cast_one,one_mul,pow_one] using hbound
  | succ k hk ih =>
    intro X
    have h := visit_moment_add L A i (mul_pos (by exact_mod_cast hk) ht) ht hη
      (B^k) B ih hbound X
    convert h using 1 <;> push_cast <;> ring_nf

lemma small_visit_moment {c : ℝ} (_hc : 0 < c) {M : ℝ≥0∞}
    (htail : ∀ R : ℝ, 0≤R → wiener {w | R≤‖w‖}≤M*ENNReal.ofReal (Real.exp (-c*R^2)))
    {n K : ℕ} [NeZero K] (L : Length) (hL : L.val=(K:ℝ))
    (A : Finset (DiscreteTorus K)) (i : Fin n) {η t : ℝ} (hη : 0≤η) (ht : 0<t)
    (htsmall : t ≤ c/(2*(η*(29^3:ℝ)+2))) (X : Configuration n L) :
    ∫⁻ w,visitWeight L A i t η X w ∂coordinateWiener n ≤ expTailBound (29^3) η (3*M) := by
  apply lintegral_exp_nat_le (coordinateWiener n) (visitCount L A i t X)
    (visitCount_measurable L A i t X) (29^3) (by norm_num) hη (3*M)
  intro k hk
  have he : η*(29^3:ℝ)+2 ≤ c/(2*t) := by
    apply (le_div_iff₀ (by positivity : 0<2*t)).mpr
    have h := (le_div_iff₀ (by positivity : 0<2*(η*(29^3:ℝ)+2))).mp htsmall
    nlinarith
  have hexp : -c*(k:ℝ)/(2*t) ≤ -(η*(29^3:ℝ)+2)*(k:ℝ) := by
    calc
      _ = -(c/(2*t))*(k:ℝ) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (neg_le_neg he) (Nat.cast_nonneg k)
  have hb := whole_time_visit_tail htail L hL A i ht k hk X
  apply hb.trans
  calc
    _ ≤ (k:ℝ≥0∞)*(3*M*ENNReal.ofReal (Real.exp (-(η*(29^3:ℝ)+2)*(k:ℝ)))) := by
      exact mul_le_mul_right (mul_le_mul_right (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr hexp)) _) _
    _ = _ := by norm_num only [Nat.cast_pow,Nat.cast_ofNat]; ring

theorem free_visit_moment (η₀ : ℝ) (hη₀ : 0≤η₀) :
    ∃ B : ℝ≥0∞, B<⊤ ∧ ∀ {n K : ℕ} [NeZero K], ∀ (L : Length), L.val=(K:ℝ) →
      ∀ (A : Finset (DiscreteTorus K)) (i : Fin n) (t η : ℝ),
        0<t → t≤2 → η≤η₀ → ∀ X : Configuration n L,
        ∫⁻ w,visitWeight L A i t η X w ∂coordinateWiener n ≤ B := by
  obtain ⟨c,M,hc,hM,htail⟩ := wiener_norm_gaussian_tail
  let τ : ℝ := c/(2*(η₀*(29^3:ℝ)+2))
  have hτ : 0<τ := div_pos hc (by positivity)
  obtain ⟨m,hm⟩ := exists_nat_gt (max 1 (2/τ))
  have hm1 : (1:ℝ) < m := (le_max_left _ _).trans_lt hm
  have hmpos : 0 < m := by exact_mod_cast (lt_trans (by norm_num : (0:ℝ)<1) hm1)
  have hmpos' : (0:ℝ) < m := by exact_mod_cast hmpos
  have hτm : 2≤τ*(m:ℝ) := by
    have h := (le_max_right _ _).trans hm.le
    have h' := (div_le_iff₀ hτ).mp h
    nlinarith
  let B := expTailBound (29^3) η₀ (3*M)
  have hB : B≠⊤ := expTailBound_ne_top _ _ (ENNReal.mul_ne_top (by simp) hM.ne)
  refine ⟨B^m,lt_top_iff_ne_top.mpr (ENNReal.pow_ne_top hB),?_⟩
  intro n K _ L hL A i t η ht ht2 hη X
  have hts : t/(m:ℝ)≤τ := (div_le_iff₀ hmpos').mpr (by nlinarith)
  have hs : ∀ X, ∫⁻ w,visitWeight L A i (t/(m:ℝ)) η₀ X w ∂coordinateWiener n ≤ B :=
    fun X ↦ small_visit_moment hc htail L hL A i hη₀ (div_pos ht hmpos') hts X
  have h := n_segment_visit_moment L A i (div_pos ht hmpos') hη₀ B hs m hmpos X
  have he : (m:ℝ)*(t/(m:ℝ))=t := mul_div_cancel₀ t (ne_of_gt hmpos')
  rw [he] at h
  apply le_trans _ h
  apply lintegral_mono
  intro w
  exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr
    (mul_le_mul_of_nonneg_right hη (Nat.cast_nonneg _)))

end HardSphere.FreeVisits

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_PathBounds_FreeVisitTravel
attribute [-instance] _root_.OAI.HardSphere.Bridge.exposedBridgeKernel_markov _root_.OAI.HardSphere.Bridge.exposedPeriodSingle_finite _root_.OAI.HardSphere.Bridge.exposedTrialKernel_markov _root_.OAI.HardSphere.Bridge.instBorelSpaceContinuousMapElemRealTimePoint _root_.OAI.HardSphere.Bridge.instIsProbabilityMeasureNoiseLaw _root_.OAI.HardSphere.Bridge.instMeasurableSpaceContinuousMapElemRealTimePoint _root_.OAI.HardSphere.Bridge.parameterBridgeKernel_markov _root_.OAI.HardSphere.Bridge.parameterIndividualReference_finite _root_.OAI.HardSphere.Bridge.parameterTrialKernel_markov _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Bridge.trialKernel_markov _root_.OAI.HardSphere.Groups.cellPathReference_probability _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Lattice.environmentMeasurableSpace _root_.OAI.HardSphere.Lattice.simplePathCountable _root_.OAI.HardSphere.Lattice.simplePathMeasurableSpace _root_.OAI.HardSphere.Rescaling.config_haar _root_.OAI.HardSphere.bridgeEndpointBase_finite _root_.OAI.HardSphere.coordinateBridge_probability _root_.OAI.HardSphere.endpointWeightedBase_sfinite _root_.OAI.HardSphere.freePathLaw_finite_deletion _root_.OAI.HardSphere.gaussianCoordinates_probability _root_.OAI.HardSphere.killedPathLaw_finite_deletion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.FreeVisits
open HardSphere.Wiener HardSphere.Lattice HardSphere.CellOrbital HardSphere.BathSlice

lemma torusDistance_le_three_of_coord (L : Length) (x y : Torus L) {B : ℝ}
    (hB : 0≤B) (h : ∀ j, dist (x j) (y j)≤B) : torusDistance L x y≤3*B := by
  apply Real.sqrt_le_iff.mpr
  constructor
  · positivity
  · have hs : ∑ j : Fin 3, dist (x j) (y j)^2 ≤ ∑ _j : Fin 3, B^2 :=
      Finset.sum_le_sum (fun j _ ↦ pow_le_pow_left₀ dist_nonneg (h j) 2)
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at hs
    norm_num at hs
    nlinarith [sq_nonneg B]

lemma freeTrajectory_dist_le {n : ℕ} (L : Length) {t R : ℝ} (ht : t≤2) (hR : 0≤R)
    (w : CoordinatePaths n) (X : Configuration n L) (i : Fin n)
    (hw : ∀ j, ‖w (i,j)‖≤R) (u : Time) :
    torusDistance L (freeTrajectory n L t w X u i) (X i)≤6*R := by
  have hs : Real.sqrt (2*t)≤2 := (Real.sqrt_le_iff).mpr ⟨by norm_num,by nlinarith⟩
  have hcoord (j : Fin 3) : dist (freeTrajectory n L t w X u i j) (X i j)≤2*R := by
    apply (freeTrajectory_coord_dist_le L t w X i u j).trans
    exact mul_le_mul hs (hw j) (norm_nonneg _) (by norm_num)
  have h := torusDistance_le_three_of_coord L _ _ (mul_nonneg (by norm_num) hR) hcoord
  nlinarith

attribute [local irreducible] freeTrajectory pathVisitedSites torusDistance

lemma visit_distance_le {n K : ℕ} (L : Length) (A : Finset (DiscreteTorus K))
    (i : Fin n) (t : ℝ) (X : Configuration n L) (w : CoordinatePaths n)
    (hw : 0<visitCount L A i t X w) :
    ∃ u : Time, visitStartDistance L A i X≤
      torusDistance L (freeTrajectory n L t w X u i) (X i)+12 := by
  classical
  obtain ⟨v,hv⟩ := Finset.card_pos.mp hw
  have hm : v∈A ∧ pathVisitsBall L 12 (siteCenter L v) i (freeTrajectory n L t w X) := by
    rw [pathVisitedSites] at hv
    exact Finset.mem_filter.mp hv
  obtain ⟨u,hu⟩ := hm.2
  have hd := spatialSiteDistance_le L (A.image (siteCenter L)) (X i) (siteCenter L v)
    (Finset.mem_image.mpr ⟨v,hm.1,rfl⟩)
  have htri := torusDistance_triangle' L (X i) (freeTrajectory n L t w X u i) (siteCenter L v)
  rw [torusDistance_comm L (X i) (freeTrajectory n L t w X u i)] at htri
  exact ⟨u,hd.trans (htri.trans (add_le_add le_rfl hu))⟩

lemma free_visit_travel_gaussian {c : ℝ} {M : ℝ≥0∞}
    (htail : ∀ R : ℝ, 0≤R → wiener {w | R≤‖w‖}≤M*ENNReal.ofReal (Real.exp (-c*R^2)))
    {n K : ℕ} (L : Length) (A : Finset (DiscreteTorus K)) (i : Fin n) {t : ℝ}
    (ht : t≤2) (X : Configuration n L) (hd : 24≤visitStartDistance L A i X) :
    coordinateWiener n {w | 0<visitCount L A i t X w} ≤
      3*M*ENNReal.ofReal (Real.exp (-c*(visitStartDistance L A i X)^2/576)) := by
  let d := visitStartDistance L A i X
  let R := d/24
  have hR : 0≤R := div_nonneg (by dsimp [d]; linarith) (by norm_num)
  have hsub : {w | 0<visitCount L A i t X w} ⊆ ⋃ j : Fin 3, {w | R≤‖w (i,j)‖} := by
    intro w hw
    by_contra hn
    have hw' : ∀ j, ‖w (i,j)‖≤R := by
      have h : ∀ j, ‖w (i,j)‖<R := by simpa only [Set.mem_iUnion,Set.mem_ofPred_eq,not_exists,not_le] using hn
      exact fun j ↦ (h j).le
    obtain ⟨u,hu⟩ := visit_distance_le L A i t X w hw
    have hdist := freeTrajectory_dist_le L ht hR w X i hw' u
    dsimp [R,d] at hdist
    linarith
  have he (j : Fin 3) : coordinateWiener n {w | R≤‖w (i,j)‖} = wiener {w | R≤‖w‖} :=
    (measurePreserving_eval (fun _ : Direction n ↦ wiener) (i,j)).measure_preimage
      (measurableSet_le measurable_const measurable_norm).nullMeasurableSet
  calc
    _ ≤ coordinateWiener n (⋃ j : Fin 3, {w | R≤‖w (i,j)‖}) := measure_mono hsub
    _ ≤ ∑' j : Fin 3, coordinateWiener n {w | R≤‖w (i,j)‖} := measure_iUnion_le _
    _ = 3*wiener {w | R≤‖w‖} := by simp [he,tsum_fintype]
    _ ≤ 3*(M*ENNReal.ofReal (Real.exp (-c*R^2))) := mul_le_mul_right (htail R hR) _
    _ = _ := by
      have he : -c*R^2 = -c*(visitStartDistance L A i X)^2/576 := by dsimp [R,d]; ring
      rw [he]; ac_rfl

theorem free_visit_travel : ∃ H : ℝ≥0∞, H<⊤ ∧
    ∀ {n K : ℕ} (L : Length) (A : Finset (DiscreteTorus K)) (i : Fin n)
      (t : ℝ), t≤2 → ∀ X : Configuration n L,
      coordinateWiener n {w | 0<visitCount L A i t X w} ≤
        H*ENNReal.ofReal (Real.exp (-3*visitStartDistance L A i X)) := by
  obtain ⟨c,M,hc,hM,htail⟩ := wiener_norm_gaussian_tail
  let H := ENNReal.ofReal (Real.exp 72)+3*M*ENNReal.ofReal (Real.exp (1296/c))
  have hH : H<⊤ := by dsimp [H]; finiteness
  refine ⟨H,hH,?_⟩
  intro n K L A i t ht X
  let d := visitStartDistance L A i X
  by_cases hd : 24≤d
  · apply (free_visit_travel_gaussian htail L A i ht X hd).trans
    have hexp : -c*d^2/576 ≤ 1296/c+(-3*d) := by
      have hs := sq_nonneg (c*d-864)
      apply (mul_le_mul_iff_left₀ hc).mp
      have he : c*(1296/c)=1296 := mul_div_cancel₀ _ (ne_of_gt hc)
      nlinarith
    have hbound := ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr hexp)
    rw [Real.exp_add,ENNReal.ofReal_mul (Real.exp_nonneg _)] at hbound
    calc
      _ ≤ (3*M*ENNReal.ofReal (Real.exp (1296/c)))*ENNReal.ofReal (Real.exp (-3*d)) := by
        exact (mul_le_mul_right hbound (3*M)).trans_eq (by ring)
      _ ≤ _ := by gcongr; exact le_add_self
  · have he : 1≤ENNReal.ofReal (Real.exp 72)*ENNReal.ofReal (Real.exp (-3*d)) := by
      rw [← ENNReal.ofReal_mul (Real.exp_nonneg _),←Real.exp_add]
      exact ENNReal.one_le_ofReal.mpr (Real.one_le_exp_iff.mpr (by linarith))
    exact (prob_le_one).trans (he.trans (by gcongr; exact le_self_add))

end HardSphere.FreeVisits

namespace HardSphere.FreeVisits
open HardSphere.Wiener HardSphere.Lattice HardSphere.CellOrbital HardSphere.BathSlice
attribute [local irreducible] freeTrajectory pathVisitedSites torusDistance

lemma lintegral_three_thirds {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {f g h : Ω → ℝ≥0∞} (hf : Measurable f) (hg : Measurable g) (hh : Measurable h) :
    (∫⁻ w, f w^(1/3:ℝ)*g w^(1/3:ℝ)*h w^(1/3:ℝ) ∂μ) ≤
    (∫⁻ w,f w ∂μ)^(1/3:ℝ)*(∫⁻ w,g w ∂μ)^(1/3:ℝ)*(∫⁻ w,h w ∂μ)^(1/3:ℝ) := by
  let F : Fin 3 → Ω → ℝ≥0∞ := ![f,g,h]
  have hF : ∀ i ∈ (Finset.univ : Finset (Fin 3)), AEMeasurable (F i) μ := by
    intro i _; fin_cases i <;> simp only [F] <;>
      first | exact hf.aemeasurable | exact hg.aemeasurable | exact hh.aemeasurable
  have H := ENNReal.lintegral_prod_norm_pow_le (μ:=μ) Finset.univ hF
    (p:=fun _ ↦ (1/3:ℝ)) (by norm_num) (by intros; norm_num)
  simpa [Fin.prod_univ_three,F] using H

lemma ofReal_exp_rpow {x p : ℝ} (hp : 0≤p) :
    ENNReal.ofReal (Real.exp x)^p = ENNReal.ofReal (Real.exp (x*p)) := by
  rw [ENNReal.ofReal_rpow_of_nonneg (Real.exp_nonneg _) hp,Real.exp_mul]

lemma indicator_one_third {Ω : Type*} (D : Set Ω) (w : Ω) :
    (D.indicator (fun _ ↦ (1:ℝ≥0∞)) w)^(1/3:ℝ) = D.indicator (fun _ ↦ 1) w := by
  classical
  by_cases hw : w∈D <;> simp [hw]

lemma exp_sub_one_le_mul_exp (x : ℝ) : Real.exp x-1≤x*Real.exp x := by
  have h := mul_le_mul_of_nonneg_right (Real.add_one_le_exp (-x)) (Real.exp_nonneg x)
  rw [←Real.exp_add] at h
  simp only [neg_add_cancel,Real.exp_zero] at h
  nlinarith

lemma visitDefect_le {n K : ℕ} (L : Length) (A : Finset (DiscreteTorus K)) (i : Fin n)
    (t : ℝ) {η η₀ : ℝ} (hη : 0≤η) (hηη : η≤η₀) (X : Configuration n L)
    (D : Set (CoordinatePaths n)) (w : CoordinatePaths n) :
    visitDefect L A i t η X D w ≤ ENNReal.ofReal η *
      (visitWeight L A i t (3*(η₀+1)) X w ^ (1/3:ℝ) *
      (D.indicator (fun _ ↦ (1:ℝ≥0∞)) w)^(1/3:ℝ) *
      ({w | 0<visitCount L A i t X w}.indicator (fun _ ↦ (1:ℝ≥0∞)) w) ^ (1/3:ℝ)) := by
  classical
  rw [indicator_one_third,indicator_one_third]
  by_cases hw : w∈D
  · by_cases hJ : 0<visitCount L A i t X w
    · have hJmem : w∈{w | 0<visitCount L A i t X w} := hJ
      simp only [Set.indicator_of_mem hw,Set.indicator_of_mem hJmem,mul_one]
      rw [visitWeight,ofReal_exp_rpow (by norm_num),←ENNReal.ofReal_mul hη]
      apply ENNReal.ofReal_le_ofReal
      simp only [ite_eq_left hw]
      set J : ℝ := (visitCount L A i t X w:ℝ)
      have hJe : J≤Real.exp J := by linarith [Real.add_one_le_exp J]
      have hJ0 : 0≤J := Nat.cast_nonneg _
      calc
        Real.exp (η*J)-1 ≤ (η*J)*Real.exp (η*J) := exp_sub_one_le_mul_exp _
        _ ≤ η*Real.exp J*Real.exp (η*J) := by gcongr
        _ = η*Real.exp ((η+1)*J) := by rw [mul_assoc,←Real.exp_add]; congr 2; ring
        _ ≤ η*Real.exp (3*(η₀+1)*J*(1/3)) := by
          apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hη
          nlinarith
    · have hJ0 : visitCount L A i t X w=0 := Nat.eq_zero_of_not_pos hJ
      simp [visitDefect,hw,hJ0]
  · simp [visitDefect,hw]

theorem free_visit_bound {η₀ : ℝ} (hη₀ : 0≤η₀) : ∃ C : ℝ≥0∞, C<⊤ ∧
    ∀ {n K : ℕ} [NeZero K] (L : Length), L.val=(K:ℝ) →
      ∀ (A : Finset (DiscreteTorus K)) (i : Fin n) {t η : ℝ}, 0<t → t≤2 →
      0≤η → η≤η₀ → ∀ (X : Configuration n L) (D : Set (CoordinatePaths n)),
      MeasurableSet D → ∀ ε : ℝ≥0∞, coordinateWiener n D≤ε →
      ∫⁻ w,visitDefect L A i t η X D w ∂coordinateWiener n ≤
        C*ENNReal.ofReal η*ε^(1/3:ℝ)*ENNReal.ofReal (Real.exp (-visitStartDistance L A i X)) := by
  obtain ⟨B,hB,hBM⟩ := free_visit_moment (3*(η₀+1)) (show 0≤3*(η₀+1) by positivity)
  obtain ⟨H,hH,hHT⟩ := free_visit_travel
  let C := B^(1/3:ℝ)*H^(1/3:ℝ)
  have hC : C<⊤ := ENNReal.mul_lt_top
    (ENNReal.rpow_lt_top_of_nonneg (by norm_num) hB.ne)
    (ENNReal.rpow_lt_top_of_nonneg (by norm_num) hH.ne)
  refine ⟨C,hC,?_⟩
  intro n K _ L hL A i t η ht ht2 hη hηη X D hD ε hε
  let V := {w | 0<visitCount L A i t X w}
  have hV : MeasurableSet V := measurableSet_lt measurable_const (visitCount_measurable L A i t X)
  let f := visitWeight L A i t (3*(η₀+1)) X
  let g := D.indicator (fun _ ↦ (1:ℝ≥0∞))
  let h := V.indicator (fun _ ↦ (1:ℝ≥0∞))
  have hf : Measurable f := visitWeight_measurable L A i t _ X
  have hg : Measurable g := measurable_const.indicator hD
  have hh : Measurable h := measurable_const.indicator hV
  have hm : Measurable (fun w ↦ f w^(1/3:ℝ)*g w^(1/3:ℝ)*h w^(1/3:ℝ)) :=
    ((hf.pow_const _).mul (hg.pow_const _)).mul (hh.pow_const _)
  have hfb : (∫⁻ w,f w ∂coordinateWiener n)≤B := hBM L hL A i t (3*(η₀+1)) ht ht2 le_rfl X
  have hgb : (∫⁻ w,g w ∂coordinateWiener n)≤ε := by
    change (∫⁻ w,D.indicator 1 w ∂coordinateWiener n)≤ε
    rw [lintegral_indicator_one hD]; exact hε
  have hhb : (∫⁻ w,h w ∂coordinateWiener n)≤H*ENNReal.ofReal (Real.exp (-3*visitStartDistance L A i X)) := by
    change (∫⁻ w,V.indicator 1 w ∂coordinateWiener n)≤_
    rw [lintegral_indicator_one hV]; exact hHT L A i t ht2 X
  calc
    _ ≤ ∫⁻ w,ENNReal.ofReal η*(f w^(1/3:ℝ)*g w^(1/3:ℝ)*h w^(1/3:ℝ)) ∂coordinateWiener n :=
      lintegral_mono (visitDefect_le L A i t hη hηη X D)
    _ = ENNReal.ofReal η*(∫⁻ w,f w^(1/3:ℝ)*g w^(1/3:ℝ)*h w^(1/3:ℝ) ∂coordinateWiener n) :=
      lintegral_const_mul _ hm
    _ ≤ ENNReal.ofReal η*((∫⁻ w,f w ∂coordinateWiener n)^(1/3:ℝ)*
        (∫⁻ w,g w ∂coordinateWiener n)^(1/3:ℝ)*(∫⁻ w,h w ∂coordinateWiener n)^(1/3:ℝ)) :=
      mul_le_mul_right (lintegral_three_thirds _ hf hg hh) _
    _ ≤ ENNReal.ofReal η*(B^(1/3:ℝ)*ε^(1/3:ℝ)*
        (H*ENNReal.ofReal (Real.exp (-3*visitStartDistance L A i X)))^(1/3:ℝ)) := by
      gcongr
    _ = _ := by
      rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num),ofReal_exp_rpow (by norm_num)]
      have he : -3*visitStartDistance L A i X*(1/3) = -visitStartDistance L A i X := by ring
      rw [he]; dsimp [C]; ring

end HardSphere.FreeVisits

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_PathBounds_SingleVisitDefect
attribute [-instance] _root_.OAI.HardSphere.Bridge.exposedBridgeKernel_markov _root_.OAI.HardSphere.Bridge.exposedPeriodSingle_finite _root_.OAI.HardSphere.Bridge.exposedTrialKernel_markov _root_.OAI.HardSphere.Bridge.instBorelSpaceContinuousMapElemRealTimePoint _root_.OAI.HardSphere.Bridge.instIsProbabilityMeasureNoiseLaw _root_.OAI.HardSphere.Bridge.instMeasurableSpaceContinuousMapElemRealTimePoint _root_.OAI.HardSphere.Bridge.parameterBridgeKernel_markov _root_.OAI.HardSphere.Bridge.parameterIndividualReference_finite _root_.OAI.HardSphere.Bridge.parameterTrialKernel_markov _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Bridge.trialKernel_markov _root_.OAI.HardSphere.Groups.cellPathReference_probability _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Lattice.environmentMeasurableSpace _root_.OAI.HardSphere.Lattice.simplePathCountable _root_.OAI.HardSphere.Lattice.simplePathMeasurableSpace _root_.OAI.HardSphere.Rescaling.config_haar _root_.OAI.HardSphere.bridgeEndpointBase_finite _root_.OAI.HardSphere.coordinateBridge_probability _root_.OAI.HardSphere.endpointWeightedBase_sfinite _root_.OAI.HardSphere.gaussianCoordinates_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.FreeVisits
open HardSphere.Wiener HardSphere.BathSlice HardSphere.Lattice HardSphere.CellOrbital
attribute [local irreducible] freeTrajectory pathVisitedSites torusDistance

lemma singleVisitDefect_measurable {K : ℕ} (L : Length) (A : Finset (DiscreteTorus K))
    (η : ℝ) {D : Set (ConfigurationPath 1 L)} (hD : MeasurableSet D) :
    Measurable (singleVisitDefect L A η D) := by
  classical
  exact ((measurable_const.mul ((pathVisitedSites_measurable L (siteCenter L) A 0).ite hD measurable_const)).exp.sub
    measurable_const).ennreal_ofReal

lemma free_single_defect_bound {η₀ : ℝ} (hη₀ : 0≤η₀) : ∃ C : ℝ, 0<C ∧
    ∀ {K : ℕ} [NeZero K] (L : Length), L.val=(K:ℝ) → ∀ A : Finset (DiscreteTorus K),
    ∀ {t η ε : ℝ}, 0<t → t≤2 → 0≤η → η≤η₀ → 0≤ε →
    ∀ D : Set (ConfigurationPath 1 L), MeasurableSet D →
    (∀ y : Torus L, coordinateWiener 1 {w | freeTrajectory 1 L t w (oneConfiguration y)∈D}≤ENNReal.ofReal ε) →
    ∀ y : Torus L,
      oneFreeExpectation t (singleVisitDefect L A η D) y ≤
      ENNReal.ofReal (C*η*ε^(1/3:ℝ)*Real.exp (-spatialSiteDistance L (A.image (siteCenter L)) y)) := by
  classical
  obtain ⟨C,hC,hbound⟩ := free_visit_bound hη₀
  refine ⟨C.toReal+1,by positivity,?_⟩
  intro K _ L hL A t η ε ht ht2 hη hηη hε D hD hprob y
  let E := {w : CoordinatePaths 1 | freeTrajectory 1 L t w (oneConfiguration y)∈D}
  have hE : MeasurableSet E := hD.preimage
    ((freeTrajectory_continuous 1 L t).measurable.comp (measurable_id.prodMk measurable_const))
  have H := hbound L hL A 0 ht ht2 hη hηη (oneConfiguration y) E hE (ENNReal.ofReal ε) (hprob y)
  have heq : oneFreeExpectation t (singleVisitDefect L A η D) y =
      ∫⁻ w,visitDefect L A 0 t η (oneConfiguration y) E w ∂coordinateWiener 1 := by
    rfl
  rw [heq]
  apply H.trans
  have hC' : C≤ENNReal.ofReal (C.toReal+1) := by
    calc
      C = ENNReal.ofReal C.toReal := (ENNReal.ofReal_toReal hC.ne).symm
      _ ≤ ENNReal.ofReal (C.toReal+1) := ENNReal.ofReal_le_ofReal (by linarith)
  calc
    C*ENNReal.ofReal η*ENNReal.ofReal ε^(1/3:ℝ)*
        ENNReal.ofReal (Real.exp (-visitStartDistance L A 0 (oneConfiguration y))) ≤
      ENNReal.ofReal (C.toReal+1)*ENNReal.ofReal η*ENNReal.ofReal ε^(1/3:ℝ)*
        ENNReal.ofReal (Real.exp (-visitStartDistance L A 0 (oneConfiguration y))) := by gcongr
    _ = _ := by
      rw [ENNReal.ofReal_rpow_of_nonneg hε (show 0≤(1/3:ℝ) by norm_num),
        ←ENNReal.ofReal_mul (show 0≤C.toReal+1 by positivity),
        ←ENNReal.ofReal_mul (show 0≤(C.toReal+1)*η by positivity),
        ←ENNReal.ofReal_mul (show 0≤(C.toReal+1)*η*ε^(1/3:ℝ) by positivity)]
      rfl

end HardSphere.FreeVisits

end
end

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_PathBounds_InteractingVisits
attribute [-instance] _root_.OAI.HardSphere.Bridge.exposedBridgeKernel_markov _root_.OAI.HardSphere.Bridge.exposedPeriodSingle_finite _root_.OAI.HardSphere.Bridge.exposedTrialKernel_markov _root_.OAI.HardSphere.Bridge.instBorelSpaceContinuousMapElemRealTimePoint _root_.OAI.HardSphere.Bridge.instIsProbabilityMeasureNoiseLaw _root_.OAI.HardSphere.Bridge.instMeasurableSpaceContinuousMapElemRealTimePoint _root_.OAI.HardSphere.Bridge.parameterBridgeKernel_markov _root_.OAI.HardSphere.Bridge.parameterIndividualReference_finite _root_.OAI.HardSphere.Bridge.parameterTrialKernel_markov _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Bridge.trialKernel_markov _root_.OAI.HardSphere.Groups.cellPathReference_probability _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Lattice.environmentMeasurableSpace _root_.OAI.HardSphere.Lattice.simplePathCountable _root_.OAI.HardSphere.Lattice.simplePathMeasurableSpace _root_.OAI.HardSphere.Rescaling.config_haar _root_.OAI.HardSphere.bridgeEndpointBase_finite _root_.OAI.HardSphere.coordinateBridge_probability _root_.OAI.HardSphere.endpointWeightedBase_sfinite _root_.OAI.HardSphere.gaussianCoordinates_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere
open Wiener
lemma spatial_count_mgf_enn : ∃ C αstar : ℝ, 0 < C ∧ 0 < αstar ∧
    ∀ (n K : ℕ) (L : Length), L.val=(K:ℝ) → ∀ (r D : ℝ),
      D=(n:ℝ)/L.val^3 → 1≤D → αstar≤D*r → 0 < r → 1≤L.val →
      (n:ℝ)*(2*Real.pi*r)^3≤L.val^3/2 →
    ∀ (g : Jet n L), IsGroundVector n L r g →
    ∀ (A : Finset (Torus L)) (z : ℝ), 0≤z → z≤1 →
      (∫⁻ X, ENNReal.ofReal (Real.exp (z*weightedSiteCount L A X)) ∂groundPositionLaw n L g)≤
        ENNReal.ofReal (Real.exp (C*z*D*(A.card:ℝ))) := by
  obtain ⟨C,αstar,hC,hα,h⟩ := spatial_count_mgf
  refine ⟨C,αstar,hC,hα,?_⟩
  intro n K L hL r D hDeq hD hαr hr hsize hs g hg A z hz hz1
  let := groundPositionLaw_probability g hg.2.2.1
  have hi := bounded_mgf_integrable (groundPositionLaw n L g)
    (weightedSiteCount_continuous L A).measurable
    (fun X ↦ (abs_of_nonneg (weightedSiteCount_nonneg L A X)).trans_le (weightedSiteCount_le L A X)) z
  rw [←ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall (fun X ↦ (Real.exp_pos _).le))]
  apply ENNReal.ofReal_le_ofReal
  have hp : 0<∫ X,Real.exp (z*weightedSiteCount L A X) ∂groundPositionLaw n L g := ProbabilityTheory.mgf_pos hi
  calc
    _ = Real.exp (Real.log (∫ X,Real.exp (z*weightedSiteCount L A X) ∂groundPositionLaw n L g)) := (Real.exp_log hp).symm
    _ ≤ _ := Real.exp_le_exp.mpr (h n K L hL r D hDeq hD hαr hr hsize hs g hg A z hz hz1)

namespace FreeVisits
open HardSphere.BathSlice HardSphere.Lattice HardSphere.CellOrbital
attribute [local irreducible] freeTrajectory pathVisitedSites torusDistance

lemma product_one_add_exp_le {n : ℕ} (L : Length) (A : Finset (Torus L))
    (hA : A.Nonempty) {z : ℝ} (hz : 0≤z) (X : Configuration n L) :
    (∏ i, (1+ENNReal.ofReal (z*Real.exp (-spatialSiteDistance L A (X i)))))≤
      ENNReal.ofReal (Real.exp (z*weightedSiteCount L A X)) := by
  classical
  simp only [weightedSiteCount,ite_eq_left hA,Finset.mul_sum,Real.exp_sum,
    ENNReal.ofReal_prod_of_nonneg (fun _ _ ↦ (Real.exp_pos _).le)]
  apply Finset.prod_le_prod'
  intro i _
  rw [←ENNReal.ofReal_one,←ENNReal.ofReal_add zero_le_one (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  linarith [Real.add_one_le_exp (z*Real.exp (-spatialSiteDistance L A (X i)))]

end FreeVisits
end HardSphere

end
end

section
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere
open Wiener BathSlice _root_.OAI.HardSphere.Lattice CellOrbital

lemma torusDistance_add (L : Length) (x y c : Torus L) :
    torusDistance L (x+c) (y+c)=torusDistance L x y := by
  unfold torusDistance
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  simp only [Pi.add_apply,dist_add_right]

lemma shiftPath_continuous {n : ℕ} {L : Length} (c : Torus L) : Continuous (shiftPath (n:=n) c) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  change Continuous (fun p : ConfigurationPath n L×Time ↦ fun i ↦ p.1 p.2 i+c)
  fun_prop

lemma shiftPath_free {n : ℕ} {L : Length} (c : Torus L) (t : ℝ) (w : CoordinatePaths n) (X : Configuration n L) :
    shiftPath c (freeTrajectory n L t w X)=freeTrajectory n L t w (fun i ↦ X i+c) := by
  ext s i j
  simp only [shiftPath,ContinuousMap.coe_mk,freeTrajectory,Pi.add_apply]
  abel

lemma spatialSiteDistance_add (L : Length) (A : Finset (Torus L)) (x c : Torus L) :
    spatialSiteDistance L (A.image (fun v ↦ v+c)) (x+c)=spatialSiteDistance L A x := by
  classical
  by_cases hA : A.Nonempty
  · obtain ⟨y,hy,he⟩ := spatialSiteDistance_attained L A hA x
    obtain ⟨z,hz,hf⟩ := spatialSiteDistance_attained L (A.image (fun v ↦ v+c)) (hA.image _) (x+c)
    obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hz
    apply le_antisymm
    · rw [he]
      have h := spatialSiteDistance_le L (A.image (fun v ↦ v+c)) (x+c) (y+c) (Finset.mem_image.mpr ⟨y,hy,rfl⟩)
      simpa only [torusDistance_add] using h
    · rw [hf,torusDistance_add]
      exact spatialSiteDistance_le L A x w hw
  · have := Finset.not_nonempty_iff_eq_empty.mp hA
    subst A
    simp [spatialSiteDistance]

namespace ShiftVisits
open FreeVisits
attribute [local instance] Classical.propDecidable

lemma shifted_visits {n K : ℕ} (L : Length) (c : Torus L) (A : Finset (DiscreteTorus K))
    (i : Fin n) (ω : ConfigurationPath n L) :
    pathVisitedSites L (siteCenter L) A i (shiftPath (-c) ω)=pathVisitedSites L (center L c) A i ω := by
  apply Finset.filter_congr
  intro v _
  unfold pathVisitsBall
  apply exists_congr
  intro s
  change (torusDistance L (ω s i+-c) (siteCenter L v)≤12) ↔ _
  have hd := torusDistance_add L (ω s i+-c) (siteCenter L v) c
  simp only [neg_add_cancel_right] at hd
  rw [←hd]
  rfl

lemma singleDefect_eq (L : Length) {K : ℕ} (c : Torus L) (A : Finset (DiscreteTorus K))
    (η : ℝ) (D : Set (ConfigurationPath 1 L)) (ω : ConfigurationPath 1 L) :
    singleDefect L c A η D ω=singleVisitDefect L A η ((shiftPath c)⁻¹' D) (shiftPath (-c) ω) := by
  simp only [singleDefect,singleVisitDefect,Set.mem_preimage,shiftPath_neg,shifted_visits]

lemma singleDefect_measurable (L : Length) {K : ℕ} (c : Torus L) (A : Finset (DiscreteTorus K))
    (η : ℝ) {D : Set (ConfigurationPath 1 L)} (hD : MeasurableSet D) :
    Measurable (singleDefect L c A η D) := by
  have he : singleDefect L c A η D=(singleVisitDefect L A η ((shiftPath c)⁻¹' D)) ∘ shiftPath (-c) :=
    funext (singleDefect_eq L c A η D)
  rw [he]
  exact (singleVisitDefect_measurable L A η (hD.preimage (shiftPath_continuous c).measurable)).comp
    (shiftPath_continuous (-c)).measurable

lemma singleDefect_reverse (L : Length) {K : ℕ} (c : Torus L) (A : Finset (DiscreteTorus K))
    (η : ℝ) {D : Set (ConfigurationPath 1 L)}
    (hD : ∀ω,reverseConfigurationPath 1 L ω∈D ↔ ω∈D) (ω : ConfigurationPath 1 L) :
    singleDefect L c A η D (reverseConfigurationPath 1 L ω)=singleDefect L c A η D ω := by
  simp only [singleDefect,hD,pathVisitedSites_reverse]

lemma free_single_defect_bound {η₀ : ℝ} (hη₀ : 0≤η₀) : ∃ C : ℝ,0<C ∧
    ∀ {K : ℕ} [NeZero K] (L : Length),L.val=(K:ℝ) → ∀ (c : Torus L) (A : Finset (DiscreteTorus K)),
    ∀ {t η ε : ℝ},0<t → t≤2 → 0≤η → η≤η₀ → 0≤ε →
    ∀ D : Set (ConfigurationPath 1 L),MeasurableSet D →
      (∀ y : Torus L,coordinateWiener 1 {w | freeTrajectory 1 L t w (oneConfiguration y)∈D}≤ENNReal.ofReal ε) →
    ∀ y : Torus L,oneFreeExpectation t (singleDefect L c A η D) y ≤
      ENNReal.ofReal (C*η*ε^(1/3:ℝ)*Real.exp (-spatialSiteDistance L (A.image (center L c)) y)) := by
  obtain ⟨C,hC,h⟩ := FreeVisits.free_single_defect_bound hη₀
  refine ⟨C,hC,?_⟩
  intro K _ L hL c A t η ε ht ht2 hη hη0 hε D hD hprob y
  let E := (shiftPath c)⁻¹' D
  have hE : MeasurableSet E := hD.preimage (shiftPath_continuous c).measurable
  have hp (z : Torus L) : coordinateWiener 1 {w | freeTrajectory 1 L t w (oneConfiguration z)∈E}≤ENNReal.ofReal ε := by
    have hh := hprob (z+c)
    change coordinateWiener 1 {w | freeTrajectory 1 L t w (fun _ ↦ z+c)∈D}≤ENNReal.ofReal ε at hh
    simpa only [E,mem_preimage,shiftPath_free,oneConfiguration] using hh
  have hh := h L hL A ht ht2 hη hη0 hε E hE hp (y+-c)
  have hf : oneFreeExpectation t (singleDefect L c A η D) y=
      oneFreeExpectation t (singleVisitDefect L A η E) (y+-c) := by
    apply lintegral_congr
    intro w
    rw [singleDefect_eq,shiftPath_free]
    rfl
  rw [hf]
  have hd : spatialSiteDistance L (A.image (center L c)) y=spatialSiteDistance L (A.image (siteCenter L)) (y+-c) := by
    have hh := spatialSiteDistance_add L (A.image (siteCenter L)) (y+-c) c
    change spatialSiteDistance L (A.image (fun v ↦ siteCenter L v+c)) y = _
    simpa only [Finset.image_image,Function.comp_def,neg_add_cancel_right] using hh
  rw [hd]
  exact hh

end ShiftVisits
end HardSphere

end
end

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_PathBounds_ShiftInteracting
attribute [-instance] _root_.OAI.HardSphere.Bridge.exposedBridgeKernel_markov _root_.OAI.HardSphere.Bridge.exposedPeriodSingle_finite _root_.OAI.HardSphere.Bridge.exposedTrialKernel_markov _root_.OAI.HardSphere.Bridge.instBorelSpaceContinuousMapElemRealTimePoint _root_.OAI.HardSphere.Bridge.instIsProbabilityMeasureNoiseLaw _root_.OAI.HardSphere.Bridge.instMeasurableSpaceContinuousMapElemRealTimePoint _root_.OAI.HardSphere.Bridge.parameterBridgeKernel_markov _root_.OAI.HardSphere.Bridge.parameterIndividualReference_finite _root_.OAI.HardSphere.Bridge.parameterTrialKernel_markov _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Bridge.trialKernel_markov _root_.OAI.HardSphere.Groups.cellPathReference_probability _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Lattice.environmentMeasurableSpace _root_.OAI.HardSphere.Lattice.simplePathCountable _root_.OAI.HardSphere.Lattice.simplePathMeasurableSpace _root_.OAI.HardSphere.Rescaling.config_haar _root_.OAI.HardSphere.bridgeEndpointBase_finite _root_.OAI.HardSphere.coordinateBridge_probability _root_.OAI.HardSphere.endpointWeightedBase_sfinite _root_.OAI.HardSphere.gaussianCoordinates_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.ShiftVisits
open HardSphere.Wiener HardSphere.Lattice HardSphere.CellOrbital HardSphere.BathSlice HardSphere.FreeVisits
attribute [local irreducible] freeTrajectory

lemma pathVisitedSites_onePathAt {n K : ℕ} (L : Length) (c : Torus L) (A : Finset (DiscreteTorus K))
    (i : Fin n) (ω : ConfigurationPath n L) :
    pathVisitedSites L (center L c) A 0 (onePathAt i ω)=pathVisitedSites L (center L c) A i ω := by
  simp only [pathVisitedSites,pathVisitsBall,onePathAt,oneConfiguration,ContinuousMap.coe_mk]
  rfl

lemma exp_defectiveTotalVisits {n K : ℕ} (L : Length) (c : Torus L) (A : Finset (DiscreteTorus K))
    (D : Set (ConfigurationPath 1 L)) {η : ℝ} (hη : 0≤η) (ω : ConfigurationPath n L) :
    ENNReal.ofReal (Real.exp (η*(defectiveTotalVisits L c A D ω : ℝ)))=
      ∏ i, (1+singleDefect L c A η D (onePathAt i ω)) := by
  classical
  simp only [defectiveTotalVisits,Nat.cast_sum,Finset.mul_sum,Real.exp_sum,
    ENNReal.ofReal_prod_of_nonneg (fun _ _ ↦ (Real.exp_pos _).le)]
  apply Finset.prod_congr rfl
  intro i _
  rw [singleDefect,pathVisitedSites_onePathAt]
  have hx : 0≤η*(if onePathAt i ω∈D then ((pathVisitedSites L (center L c) A i ω).card:ℝ) else 0) := by positivity
  have he : 0≤Real.exp (η*(if onePathAt i ω∈D then ((pathVisitedSites L (center L c) A i ω).card:ℝ) else 0))-1 := sub_nonneg.mpr (Real.one_le_exp_iff.mpr hx)
  simp only [Nat.cast_ite,Nat.cast_zero]
  rw [←ENNReal.ofReal_one,←ENNReal.ofReal_add zero_le_one he]
  congr 1
  ring

theorem interacting_visit_mgf {η₀ : ℝ} (hη₀ : 0≤η₀) :
    ∃ Cdel Cfree Csp αstar : ℝ,
      0<Cdel ∧ 0<Cfree ∧ 0<Csp ∧ 0<αstar ∧
    ∀ (n K : ℕ) [NeZero K] (L : Length), L.val=(K:ℝ) → ∀ r D : ℝ,
      D=(n:ℝ)/L.val^3 → 1≤D → αstar≤D*r → 0 < r →
      (n:ℝ)*(2*Real.pi*r)^3≤L.val^3/2 →
    ∀ (g : Jet n L), IsGroundVector n L r g →
    ∀ (c : Torus L) (A : Finset (DiscreteTorus K)) {t η ε : ℝ},
      0<t → t≤2 → 0≤η → η≤η₀ → 0≤ε →
    ∀ E : Set (ConfigurationPath 1 L), MeasurableSet E →
      (∀ω,reverseConfigurationPath 1 L ω∈E ↔ ω∈E) →
      (∀ y : Torus L, coordinateWiener 1 {w | freeTrajectory 1 L t w (oneConfiguration y)∈E}≤ENNReal.ofReal ε) →
      Real.exp (t*Cdel*D*r)*(Cfree*η*ε^(1/3:ℝ))≤1 →
      (∫⁻ ω, ENNReal.ofReal (Real.exp (η*(defectiveTotalVisits L c A E ω:ℝ)))
        ∂groundPathLaw n L r t g) ≤
        ENNReal.ofReal (Real.exp (Csp*(Real.exp (t*Cdel*D*r)*(Cfree*η*ε^(1/3:ℝ)))*D*(A.card:ℝ))) := by
  classical
  obtain ⟨Cdel,hCdel,hdel⟩ := ground_product_one_add
  obtain ⟨Cfree,hCfree,hfree⟩ := free_single_defect_bound hη₀
  obtain ⟨Csp,αstar,hCsp,hα,hsp⟩ := spatial_count_mgf_enn
  refine ⟨Cdel,Cfree,Csp,αstar,hCdel,hCfree,hCsp,hα,?_⟩
  intro n K inst L hL r D hDeq hD hαr hr hs g hg c A t η ε ht ht2 hη hη0 hε E hE hrev hprob hz1
  let z := Real.exp (t*Cdel*D*r)*(Cfree*η*ε^(1/3:ℝ))
  have hz : 0≤z := by positivity
  have hsize : 1≤L.val := by rw [hL]; exact_mod_cast (NeZero.pos K)
  let := hg.groundPathLaw_probability ht.le
  by_cases hA : A.Nonempty
  · let B := A.image (center L c)
    have hB : B.Nonempty := hA.image _
    have hDexp : t*Cdel*(n:ℝ)*r/L.val^3=t*Cdel*D*r := by rw [hDeq]; ring
    calc
      _ = ∫⁻ ω,∏i,(1+singleDefect L c A η E (onePathAt i ω)) ∂groundPathLaw n L r t g :=
        lintegral_congr (exp_defectiveTotalVisits L c A E hη)
      _ ≤ ∫⁻ X,∏i,(1+ENNReal.ofReal (Real.exp (t*Cdel*(n:ℝ)*r/L.val^3))*
          oneFreeExpectation t (singleDefect L c A η E) (X i)) ∂groundPositionLaw n L g :=
        hdel n L r t hr ht hs g hg _ (singleDefect_measurable L c A η hE) (singleDefect_reverse L c A η hrev)
      _ ≤ ∫⁻ X,ENNReal.ofReal (Real.exp (z*weightedSiteCount L B X)) ∂groundPositionLaw n L g := by
        apply lintegral_mono
        intro X
        apply le_trans _ (product_one_add_exp_le L B hB hz X)
        apply Finset.prod_le_prod'
        intro i _
        gcongr
        have H := hfree L hL c A ht ht2 hη hη0 hε E hE hprob (X i)
        calc
          _ ≤ ENNReal.ofReal (Real.exp (t*Cdel*(n:ℝ)*r/L.val^3))*
              ENNReal.ofReal (Cfree*η*ε^(1/3:ℝ)*Real.exp (-spatialSiteDistance L B (X i))) := by gcongr
          _ = _ := by rw [←ENNReal.ofReal_mul (Real.exp_nonneg _),hDexp]; congr 1; dsimp [z]; ring
      _ ≤ ENNReal.ofReal (Real.exp (Csp*z*D*(B.card:ℝ))) :=
        hsp n K L hL r D hDeq hD hαr hr hsize hs g hg B z hz hz1
      _ ≤ _ := by
        apply ENNReal.ofReal_le_ofReal
        apply Real.exp_le_exp.mpr
        have hc : (B.card:ℝ)≤(A.card:ℝ) := by exact_mod_cast Finset.card_image_le
        exact mul_le_mul_of_nonneg_left hc (by positivity)
  · have he : A=∅ := Finset.not_nonempty_iff_eq_empty.mp hA
    subst A
    simp [defectiveTotalVisits,pathVisitedSites]

end HardSphere.ShiftVisits

end
end

section
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.ShiftVisits
open HardSphere.Wiener HardSphere.BathSlice HardSphere.Lattice HardSphere.CellOrbital HardSphere.FreeVisits

lemma visitorCount_sum {n K : ℕ} (L : Length) (c : Torus L) (A : Finset (DiscreteTorus K))
    (E : Set (ConfigurationPath 1 L)) (ω : ConfigurationPath n L) :
    (∑v∈A,visitorCount L c E v ω)=defectiveTotalVisits L c A E ω := by
  classical
  simp only [visitorCount,Finset.card_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : onePathAt i ω∈E
  · simp only [hi,true_and,pathVisitedSites,ite_eq_left,Finset.card_filter]
  · simp only [hi,false_and,ite_false,Finset.sum_const_zero,pathVisitedSites]

lemma visitorCount_measurable {n K : ℕ} (L : Length) (c : Torus L) {E : Set (ConfigurationPath 1 L)}
    (hE : MeasurableSet E) (v : DiscreteTorus K) : Measurable (visitorCount (n:=n) L c E v) := by
  classical
  have he : visitorCount (n:=n) L c E v=(fun ω ↦ ∑i : Fin n, if onePathAt i ω∈E ∧ pathVisitsBall L 12 (center L c v) i ω then (1:ℕ) else 0) := by
    funext ω
    simp only [visitorCount,Finset.card_filter]
  rw [he]
  apply Finset.measurable_fun_sum
  intro i _
  have hi : MeasurableSet {ω : ConfigurationPath n L | onePathAt i ω∈E} := hE.preimage (onePathAt_continuous i).measurable
  exact measurable_const.ite (hi.inter (pathVisitsBall_isClosed L 12 (center L c v) i).measurableSet) measurable_const

lemma defectiveTotalVisits_measurable {n K : ℕ} (L : Length) (c : Torus L) (A : Finset (DiscreteTorus K))
    {E : Set (ConfigurationPath 1 L)} (hE : MeasurableSet E) : Measurable (defectiveTotalVisits (n:=n) L c A E) := by
  have he : defectiveTotalVisits (n:=n) L c A E=fun ω ↦ ∑v∈A,visitorCount L c E v ω := by
    funext ω; exact (visitorCount_sum L c A E ω).symm
  rw [he]
  exact Finset.measurable_fun_sum _ (fun v _ ↦ visitorCount_measurable L c hE v)

lemma joint_visitor_sum {n K : ℕ} (L : Length) (c : Torus L) (A : Finset (DiscreteTorus K))
    (E : Set (ConfigurationPath 1 L)) {H : ℝ} {ω : ConfigurationPath n L}
    (h : ∀v∈A,H≤(visitorCount L c E v ω:ℝ)) :
    H*(A.card:ℝ)≤(defectiveTotalVisits L c A E ω:ℝ) := by
  rw [←visitorCount_sum L c A E ω,Nat.cast_sum]
  have hs := Finset.sum_le_sum h
  simpa only [Finset.sum_const,nsmul_eq_mul,mul_comm] using hs

lemma joint_visitors_markov {n K : ℕ} (L : Length) (c : Torus L) (A : Finset (DiscreteTorus K))
    {E : Set (ConfigurationPath 1 L)} (hE : MeasurableSet E)
    (μ : Measure (ConfigurationPath n L)) {η H Q : ℝ} (hη : 0≤η)
    (hmgf : (∫⁻ω,ENNReal.ofReal (Real.exp (η*(defectiveTotalVisits L c A E ω:ℝ))) ∂μ)≤
      ENNReal.ofReal (Real.exp (Q*(A.card:ℝ)))) :
    μ {ω | ∀v∈A,H≤(visitorCount L c E v ω:ℝ)}≤ENNReal.ofReal (Real.exp ((Q-η*H)*(A.card:ℝ))) := by
  let F := fun ω : ConfigurationPath n L ↦ ENNReal.ofReal (Real.exp (η*(defectiveTotalVisits L c A E ω:ℝ)))
  have hc : Measurable (fun k : ℕ ↦ (k:ℝ)) := measurable_of_countable _
  have hF : Measurable F := ((measurable_const.mul (hc.comp (defectiveTotalVisits_measurable L c A hE))).exp).ennreal_ofReal
  have hp : ENNReal.ofReal (Real.exp (η*(H*(A.card:ℝ))))≠0 := ne_of_gt (ENNReal.ofReal_pos.mpr (Real.exp_pos _))
  have hm := meas_ge_le_lintegral_div (μ:=μ) hF.aemeasurable hp ENNReal.ofReal_ne_top
  calc
    _ ≤ μ {ω | ENNReal.ofReal (Real.exp (η*(H*(A.card:ℝ))))≤F ω} := by
      apply measure_mono
      intro ω hω
      apply ENNReal.ofReal_le_ofReal
      apply Real.exp_le_exp.mpr
      exact mul_le_mul_of_nonneg_left (joint_visitor_sum L c A E hω) hη
    _ ≤ _ := hm
    _ ≤ ENNReal.ofReal (Real.exp (Q*(A.card:ℝ)))/ENNReal.ofReal (Real.exp (η*(H*(A.card:ℝ)))) := ENNReal.div_le_div_right hmgf _
    _ = _ := by
      rw [←ENNReal.ofReal_div_of_pos (Real.exp_pos _),←Real.exp_sub]
      congr 2
      ring

end HardSphere.ShiftVisits

end
end

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_PathBounds_ShiftTails
attribute [-instance] _root_.OAI.HardSphere.Bridge.exposedBridgeKernel_markov _root_.OAI.HardSphere.Bridge.exposedPeriodSingle_finite _root_.OAI.HardSphere.Bridge.exposedTrialKernel_markov _root_.OAI.HardSphere.Bridge.instBorelSpaceContinuousMapElemRealTimePoint _root_.OAI.HardSphere.Bridge.instIsProbabilityMeasureNoiseLaw _root_.OAI.HardSphere.Bridge.instMeasurableSpaceContinuousMapElemRealTimePoint _root_.OAI.HardSphere.Bridge.parameterBridgeKernel_markov _root_.OAI.HardSphere.Bridge.parameterIndividualReference_finite _root_.OAI.HardSphere.Bridge.parameterTrialKernel_markov _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Bridge.trialKernel_markov _root_.OAI.HardSphere.Groups.cellPathReference_probability _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Lattice.environmentMeasurableSpace _root_.OAI.HardSphere.Lattice.simplePathCountable _root_.OAI.HardSphere.Lattice.simplePathMeasurableSpace _root_.OAI.HardSphere.Rescaling.config_haar _root_.OAI.HardSphere.bridgeEndpointBase_finite _root_.OAI.HardSphere.coordinateBridge_probability _root_.OAI.HardSphere.endpointWeightedBase_sfinite _root_.OAI.HardSphere.gaussianCoordinates_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.ShiftVisits
open Wiener PathCutoff BathSlice HardSphere.Lattice CellOrbital HardSphere.FreeVisits

theorem ground_excessVisitors_tail_oai :
    ∃ αstar : ℝ, 0<αstar ∧ ∀ αmax : ℝ, 0<αmax →
    ∃ H : ℝ, 0<H ∧ ∀ (n K : ℕ) [NeZero K] (L : Length), L.val=(K:ℝ) →
    ∀ r D : ℝ, D=(n:ℝ)/L.val^3 → 1≤D → αstar≤D*r → D*r≤αmax → 0 < r →
      (n:ℝ)*(2*Real.pi*r)^3≤L.val^3/2 →
    ∀ (g : Jet n L), IsGroundVector n L r g → ∀ (x₀ : Torus L) (A : Finset (DiscreteTorus K)) {t : ℝ},
      0<t → t≤2 →
      groundPathLaw n L r t g {ω | ∀v∈A,H*D≤(visitorCount L x₀ Set.univ v ω:ℝ)}≤
        ENNReal.ofReal (Real.exp (-(D*(A.card:ℝ)))) := by
  obtain ⟨Cd,Cf,Cs,α,hCd,hCf,hCs,hα,hm⟩ := interacting_visit_mgf (η₀:=1) (by norm_num)
  refine ⟨α,hα,?_⟩
  intro αmax hαmax
  let B := Real.exp (2*Cd*αmax)*Cf
  have hB : 0<B := by dsimp [B]; positivity
  let η := min 1 B⁻¹
  have hη : 0<η := lt_min (by norm_num) (inv_pos.mpr hB)
  have hη1 : η≤1 := min_le_left _ _
  have hb : B*η≤1 := by
    calc
      B*η≤B*B⁻¹ := mul_le_mul_of_nonneg_left (min_le_right _ _) hB.le
      _ = 1 := mul_inv_cancel₀ hB.ne'
  let H := (Cs+1)/η
  have hH : 0<H := div_pos (by linarith) hη
  refine ⟨H,hH,?_⟩
  intro n K inst L hL r D hDeq hD hαr hαup hr hs g hg x₀ A t ht ht2
  have hD0 : 0≤D := by linarith
  have hxp : t*Cd*D*r≤2*Cd*αmax := by
    calc
      t*Cd*D*r = (t*Cd)*(D*r) := by ring
      _ ≤ (t*Cd)*αmax := mul_le_mul_of_nonneg_left hαup (by positivity)
      _ ≤ (2*Cd)*αmax := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ht2 hCd.le) hαmax.le
  have hz : Real.exp (t*Cd*D*r)*(Cf*η*(1:ℝ)^(1/3:ℝ))≤1 := by
    simp only [Real.one_rpow,mul_one]
    calc
      _ ≤ Real.exp (2*Cd*αmax)*(Cf*η) := mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hxp) (by positivity)
      _ = B*η := by dsimp [B]; ring
      _ ≤ 1 := hb
  have hp (y : Torus L) : coordinateWiener 1 {w | freeTrajectory 1 L t w (oneConfiguration y)∈(Set.univ : Set (ConfigurationPath 1 L))}≤ENNReal.ofReal 1 := by simp
  have hh := hm n K L hL r D hDeq hD hαr hr hs g hg x₀ A ht ht2 hη.le hη1
    (by norm_num : (0:ℝ)≤1) Set.univ MeasurableSet.univ (fun _ ↦ Iff.rfl) hp hz
  have hj := joint_visitors_markov L x₀ A MeasurableSet.univ (groundPathLaw n L r t g) hη.le hh (H:=H*D)
  apply hj.trans
  apply ENNReal.ofReal_le_ofReal
  apply Real.exp_le_exp.mpr
  rw [←neg_mul]
  apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg A.card)
  have hhH : η*H=Cs+1 := mul_div_cancel₀ _ hη.ne'
  have he : Cs*(Real.exp (t*Cd*D*r)*(Cf*η*(1:ℝ)^(1/3:ℝ)))*D≤Cs*D := by
    exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hz hCs.le) hD0).trans_eq (by ring)
  change _≤ -D
  nlinarith

end HardSphere.ShiftVisits

end
end

end

end OAI
end

theorem solution : type_of% @OAI.HardSphere.ShiftVisits.ground_excessVisitors_tail_oai := @OAI.HardSphere.ShiftVisits.ground_excessVisitors_tail_oai
