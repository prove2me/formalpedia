-- Prove2me | solution 1 for OAI.HardSphere.Bridge.physical_failure_sum
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T20:02:43.571142+00:00
-- url     : https://prove2.me/submissions/31cbc751-92c5-4430-b45a-3d29625fffe0

import Mathlib
import Definitions.Def_HardSphere
import Definitions.Def_OAIQ054H002

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

lemma tent_at_zero (n : ℕ) (k : Fin (2 ^ n)) : tent n k 0 = 0 := by
  simp only [tent, mul_zero, zero_sub, abs_neg]
  rw [abs_of_nonneg (by positivity : (0:ℝ) ≤ 2 * (k:ℝ) + 1)]
  apply max_eq_left
  norm_num

lemma tent_at_one (n : ℕ) (k : Fin (2 ^ n)) : tent n k 1 = 0 := by
  have hk : (k : ℝ) + 1 ≤ (2:ℝ)^n := by exact_mod_cast k.isLt
  simp only [tent, mul_one, pow_succ]
  rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ (2:ℝ)^n*2-(2*(k:ℝ)+1))]
  exact max_eq_left (by linarith)

lemma level_at_zero (n : ℕ) (ω : Noise) : level n ω 0 = 0 := by
  simp [level, tentMap, tent_at_zero]

lemma level_at_one (n : ℕ) (ω : Noise) : level n ω 1 = 0 := by
  simp [level, tentMap, tent_at_one]

lemma path_at_zero (ω : Noise) : path ω 0 = 0 := by
  by_cases h : Summable (fun n ↦ level n ω)
  · simp only [path, ContinuousMap.add_apply, ContinuousMap.smul_apply, ContinuousMap.coe_mk,
      smul_eq_mul]
    change ω (.inl ()) * 0 + _ = 0
    rw [← ContinuousMap.tsum_apply h]
    simp [level_at_zero]
  · simp [path, tsum_eq_zero_of_not_summable h]

lemma path_at_one (ω : Noise) : path ω 1 = ω (.inl ()) := by
  by_cases h : Summable (fun n ↦ level n ω)
  · simp only [path, ContinuousMap.add_apply, ContinuousMap.smul_apply, ContinuousMap.coe_mk,
      smul_eq_mul]
    change ω (.inl ()) * 1 + _ = _
    rw [← ContinuousMap.tsum_apply h]
    simp [level_at_one]
  · simp [path, tsum_eq_zero_of_not_summable h]

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

lemma bridge_eq (ω : Noise) : bridge ω = ∑' n, level n ω := by
  simp only [bridge, bridgeMap, path, embedRest, Sum.elim_inl, zero_smul, zero_add]
  congr 1

lemma path_decomposition (ω : Noise) : path ω = ω (.inl ()) • linearPath + bridge ω := by
  rw [bridge_eq]
  rfl

lemma bridge_at_zero (ω : Noise) : bridge ω 0 = 0 := path_at_zero _
lemma bridge_at_one (ω : Noise) : bridge ω 1 = 0 := path_at_one _

lemma bridge_apply (ω : Noise) (t : Time) : bridge ω t = path ω t - t.val * path ω 1 := by
  have h := congrArg (fun f : C(Time,ℝ) ↦ f t) (path_decomposition ω)
  simp only [ContinuousMap.add_apply, ContinuousMap.smul_apply, linearPath,
    ContinuousMap.coe_mk, smul_eq_mul] at h
  rw [path_at_one]
  linarith

lemma bridge_projection_algebra {ι : Type*} [Fintype ι] (c : ι → ℝ) (t : ι → Time) :
    let a : Option ι → ℝ := fun i ↦ i.elim (-∑ i, c i*(t i:ℝ)) c
    let u : Option ι → Time := fun i ↦ i.elim 1 t
    (∑ i, ∑ j, a i*a j*min (u i:ℝ) (u j:ℝ)) =
      ∑ i, ∑ j, c i*c j*(min (t i:ℝ) (t j:ℝ) - (t i:ℝ)*(t j:ℝ)) := by
  let A : ℝ := ∑ i, c i*(t i:ℝ)
  have hh : (∑ i, ∑ j, c i*c j*((t i:ℝ)*(t j:ℝ))) = A*A := by
    dsimp only [A]
    rw [Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  have h1 : (∑ i, (-A)*c i*(t i:ℝ)) = -A*A := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have h2 : (∑ i, c i*(-A)*(t i:ℝ)) = -A*A := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  dsimp only
  simp only [Fintype.sum_option, Option.elim_none, Option.elim_some,
    show ((1:Time):ℝ) = 1 from rfl, min_self, min_eq_right (t _).property.2,
    min_eq_left (t _).property.2, mul_one]
  simp only [Finset.sum_add_distrib, mul_sub, Finset.sum_sub_distrib]
  change (-A)*(-A) + (∑ i, (-A)*c i*(t i:ℝ)) +
    ((∑ i, c i*(-A)*(t i:ℝ)) + _) = _
  rw [h1,h2,hh]
  ring

lemma bridge_projection_law {ι : Type*} [Fintype ι] (c : ι → ℝ) (t : ι → Time) :
    HasLaw (fun ω ↦ ∑ i, c i*bridge ω (t i))
      (gaussianReal 0 (Real.toNNReal (∑ i, ∑ j, c i*c j*
        (min (t i:ℝ) (t j:ℝ) - (t i:ℝ)*(t j:ℝ))))) law := by
  have h := path_projection_law (fun i : Option ι ↦ i.elim (-∑ i, c i*(t i:ℝ)) c)
    (fun i ↦ i.elim 1 t)
  rw [bridge_projection_algebra] at h
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  funext ω
  simp only [Fintype.sum_option, Option.elim_none, Option.elim_some, bridge_apply,
    mul_sub, Finset.sum_sub_distrib, neg_mul, Finset.sum_mul]
  simp only [mul_assoc]
  ring

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

end HardSphere.Wiener

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

end HardSphere.Wiener

end
end

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Bridges_BridgeResidual
attribute [-instance] _root_.OAI.HardSphere.Bridge.exposedBridgeKernel_markov _root_.OAI.HardSphere.Bridge.exposedPeriodSingle_finite _root_.OAI.HardSphere.Bridge.exposedTrialKernel_markov _root_.OAI.HardSphere.Bridge.instBorelSpaceContinuousMapElemRealTimePoint _root_.OAI.HardSphere.Bridge.instIsProbabilityMeasureNoiseLaw _root_.OAI.HardSphere.Bridge.instMeasurableSpaceContinuousMapElemRealTimePoint _root_.OAI.HardSphere.Bridge.parameterBridgeKernel_markov _root_.OAI.HardSphere.Bridge.parameterIndividualReference_finite _root_.OAI.HardSphere.Bridge.parameterTrialKernel_markov _root_.OAI.HardSphere.Bridge.trialKernel_markov _root_.OAI.HardSphere.Groups.cellPathReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Set Filter ProbabilityTheory
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.Wiener

lemma centerMap_path (ω : Noise) : centerMap (path ω)=bridge ω := by
  ext s
  simpa only [centerMap_apply] using (bridge_apply ω s).symm

lemma bridgeLaw_center : bridgeLaw=wiener.map centerMap := by
  rw [bridgeLaw,wiener,Measure.map_map centerMap.continuous.measurable measurable_path]
  congr 1
  funext ω
  exact (centerMap_path ω).symm

instance bridgeLaw_isGaussian : IsGaussian bridgeLaw := by
  rw [bridgeLaw_center]
  first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

lemma finite_bridge_gaussian {ι : Type*} [Fintype ι] (t : ι → Time) :
    HasGaussianLaw (fun ω i ↦ bridge ω (t i)) law := by
  classical
  let loc : Option ι → Time := fun i ↦ i.elim 1 t
  let L : (Option ι → ℝ) →L[ℝ] (ι → ℝ) := ContinuousLinearMap.pi
    (fun i ↦ ContinuousLinearMap.proj (some i) - (t i:ℝ) • ContinuousLinearMap.proj none)
  convert! (finite_path_gaussian loc).map_fun L using 1
  all_goals try with_reducible_and_instances rfl
  funext ω i
  simp [L,loc,bridge_apply]

lemma bridge_eval_law (t : Time) :
    HasLaw (fun ω ↦ bridge ω t) (gaussianReal 0 (Real.toNNReal ((t:ℝ)-(t:ℝ)^2))) law := by
  simpa only [Fintype.sum_unique,mul_one,one_mul,min_self,pow_two] using
    bridge_projection_law (fun _ : Unit ↦ (1:ℝ)) (fun _ ↦ t)

lemma bridge_covariance (s t : Time) :
    cov[fun ω ↦ bridge ω s,fun ω ↦ bridge ω t;law]=min (s:ℝ) (t:ℝ)-(s:ℝ)*(t:ℝ) := by
  have hp (v : Time) := (path_eval_law v).hasGaussianLaw.memLp_two
  simp only [bridge_apply]
  rw [covariance_fun_sub_fun_sub (hp s) ((hp 1).const_mul (s:ℝ)) (hp t) ((hp 1).const_mul (t:ℝ))]
  simp only [covariance_const_mul_left,covariance_const_mul_right,path_covariance]
  have hs : min (s:ℝ) (1:ℝ)=(s:ℝ) := min_eq_left s.property.2
  have ht : min (1:ℝ) (t:ℝ)=(t:ℝ) := min_eq_right t.property.2
  change min (s:ℝ) (t:ℝ)-(t:ℝ)*min (s:ℝ) 1-(s:ℝ)*min 1 (t:ℝ)+(t:ℝ)*((s:ℝ)*min (1:ℝ) 1)=_
  rw [hs,ht,min_self]
  ring

lemma bridgeRemainder_eq (u : Time) (ω : Noise) :
    bridgeRemainder u (bridge ω)=centerMap (suffixMap u (path ω)) := by
  ext s
  simp only [bridgeRemainder_apply,bridge_apply,centerMap_apply,suffixMap_apply]
  have he : suffixTime u 1=1 := by apply Subtype.ext; change (u:ℝ)+(1-(u:ℝ))*1=1; ring
  rw [he]
  change path ω (suffixTime u s)-((u:ℝ)+(1-(u:ℝ))*(s:ℝ))*path ω 1-
    (1-(s:ℝ))*(path ω u-(u:ℝ)*path ω 1)=_
  ring

lemma bridgeRemainder_law (u : Time) :
    law.map (fun ω ↦ bridgeRemainder u (bridge ω)) =
      bridgeLaw.map (fun β ↦ Real.sqrt (1-(u:ℝ)) • β) := by
  calc
    _ = (law.map (fun ω ↦ suffixMap u (path ω))).map centerMap := by
      rw [Measure.map_map (f:=fun ω ↦ suffixMap u (path ω)) centerMap.continuous.measurable
        ((suffixMap u).continuous.measurable.comp measurable_path)]
      congr 1
      funext ω
      exact bridgeRemainder_eq u ω
    _ = (law.map (fun ω ↦ Real.sqrt (1-(u:ℝ)) • path ω)).map centerMap := by rw [suffix_law]
    _ = _ := by
      rw [Measure.map_map (f:=fun ω ↦ Real.sqrt (1-(u:ℝ)) • path ω) centerMap.continuous.measurable
        ((show Continuous (fun w : C(Time,ℝ) ↦ Real.sqrt (1-(u:ℝ)) • w) from by fun_prop).measurable.comp measurable_path),bridgeLaw,
        Measure.map_map (by fun_prop) measurable_bridge]
      congr 1
      funext ω
      exact (centerMap.map_smul _ _).trans (congrArg (fun β ↦ Real.sqrt (1-(u:ℝ)) • β) (centerMap_path ω))

lemma bridgeRemainder_joint_gaussian (u : Time) :
    IsGaussianProcess (Sum.elim (fun _ : Unit ↦ fun ω ↦ bridge ω u)
      (fun s ω ↦ bridgeRemainder u (bridge ω) s)) law := by
  classical
  constructor
  intro I
  let loc : Option I → Time := fun i ↦ i.elim u (fun j ↦ j.val.elim (fun _ ↦ u) (suffixTime u))
  let ev (i : Option I) : (Option I → ℝ) →L[ℝ] ℝ := ContinuousLinearMap.proj i
  let L : (Option I → ℝ) →L[ℝ] (I → ℝ) := ContinuousLinearMap.pi
    (fun j ↦ match j.val with
      | .inl _ => ev (some j)
      | .inr s => ev (some j) - (1-(s:ℝ)) • ev none)
  convert! (finite_bridge_gaussian loc).map_fun L using 1
  all_goals try with_reducible_and_instances rfl
  funext ω j
  cases hj : j.val <;> simp [L,loc,ev,hj]

lemma bridgeRemainder_independent (u : Time) :
    IndepFun (fun ω ↦ bridge ω u) (fun ω ↦ bridgeRemainder u (bridge ω)) law := by
  have hc (_ : Unit) (s : Time) :
      cov[fun ω ↦ bridge ω u,fun ω ↦ bridgeRemainder u (bridge ω) s;law]=0 := by
    simp only [bridgeRemainder_apply]
    rw [covariance_fun_sub_right (bridge_eval_law u).hasGaussianLaw.memLp_two
      (bridge_eval_law _).hasGaussianLaw.memLp_two ((bridge_eval_law u).hasGaussianLaw.memLp_two.const_mul _),
      covariance_const_mul_right,bridge_covariance,bridge_covariance,min_self,min_eq_left (le_suffixTime u s)]
    change (u:ℝ)-(u:ℝ)*((u:ℝ)+(1-(u:ℝ))*(s:ℝ))-(1-(s:ℝ))*((u:ℝ)-(u:ℝ)*(u:ℝ))=0
    ring
  have hi := (bridgeRemainder_joint_gaussian u).indepFun_of_covariance_eq_zero
    (fun _ ↦ ((continuous_eval_const u).measurable.comp measurable_bridge).aemeasurable)
    (fun s ↦ ((continuous_eval_const s).measurable.comp ((bridgeRemainder u).continuous.measurable.comp measurable_bridge)).aemeasurable) hc
  have hid := hi.comp (measurable_pi_apply ())
    (Measurable.of_eval fun index ↦ measurable_pi_apply (TopologicalSpace.denseSeq Time index))
  have hh := hid.comp measurable_id denseEval_embedding.measurable_invFun
  convert hh using 1
  · rfl
  · funext ω
    exact (denseEval_embedding.leftInverse_invFun _).symm

end HardSphere.Wiener

namespace HardSphere
open Wiener

lemma bridge_endpoints : ∀ᵐ β ∂bridgeLaw, β (0:Time)=0 ∧ β (1:Time)=0 := by
  have hm : MeasurableSet {β : C(Time,ℝ) | β (0:Time)=0 ∧ β (1:Time)=0} :=
    ((isClosed_eq (continuous_eval_const (0:Time)) continuous_const).inter (isClosed_eq (continuous_eval_const (1:Time)) continuous_const)).measurableSet
  rw [bridgeLaw,ae_map_iff measurable_bridge.aemeasurable hm]
  exact ae_of_all _ (fun ω ↦ ⟨bridge_at_zero ω,bridge_at_one ω⟩)

end HardSphere

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Bridges_GaussianPacking
attribute [-instance] _root_.OAI.HardSphere.Bridge.exposedBridgeKernel_markov _root_.OAI.HardSphere.Bridge.exposedPeriodSingle_finite _root_.OAI.HardSphere.Bridge.exposedTrialKernel_markov _root_.OAI.HardSphere.Bridge.instBorelSpaceContinuousMapElemRealTimePoint _root_.OAI.HardSphere.Bridge.instIsProbabilityMeasurePointMidpointNoise _root_.OAI.HardSphere.Bridge.instMeasurableSpaceContinuousMapElemRealTimePoint _root_.OAI.HardSphere.Bridge.parameterBridgeKernel_markov _root_.OAI.HardSphere.Bridge.parameterIndividualReference_finite _root_.OAI.HardSphere.Bridge.parameterTrialKernel_markov _root_.OAI.HardSphere.Bridge.targetUniform_finite _root_.OAI.HardSphere.Bridge.trialKernel_markov _root_.OAI.HardSphere.Comparison.parameterTargetKernel_finite _root_.OAI.HardSphere.Groups.cellPathReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.GaussianPacking

lemma kernel_product (b : ℝ) (x : Point) : kernel b x=∏j,Real.exp (-b*x j^2) := by
  rw [kernel,square,Finset.mul_sum,Real.exp_sum]

lemma kernel_integrable {b : ℝ} (hb : 0<b) : Integrable (kernel b) volume := by
  rw [show kernel b = (fun x : Point ↦ ∏j,Real.exp (-b*x j^2)) from funext (kernel_product b)]
  exact Integrable.fintype_prod (fun _ ↦ integrable_exp_neg_mul_sq hb)

lemma kernel_integral (b : ℝ) : (∫x,kernel b x)=(Real.sqrt (Real.pi/b))^3 := by
  simp only [kernel_product]
  convert integral_fintype_prod_volume_eq_prod (fun (_ : Fin 3) (y : ℝ) ↦ Real.exp (-b*y^2)) using 1
  all_goals try with_reducible_and_instances rfl
  simp only [integral_gaussian,Finset.prod_const,Finset.card_univ,Fintype.card_fin]

lemma cube_real_volume (q : Point) {δ : ℝ} (hδ : 0≤δ) : volume.real (cube q δ)=(2*δ)^3 := by
  rw [Measure.real,cube,Real.volume_Icc_pi_toReal (by intro j; dsimp; linarith)]
  simp only [show ∀j,(q j+δ)-(q j-δ)=2*δ by intro j; ring,Finset.prod_const,Finset.card_univ,Fintype.card_fin]

lemma cube_coord {q y : Point} {δ : ℝ} (hy : y∈cube q δ) (j : Fin 3) :
    |y j-q j|≤δ := by
  rw [abs_le]
  constructor <;> have h1:=hy.1 j <;> have h2:=hy.2 j <;> dsimp at * <;> linarith

lemma square_triangle (x y : Point) : square (x+y)≤2*square x+2*square y := by
  simp only [square,Pi.add_apply]
  rw [Finset.mul_sum, Finset.mul_sum, ←Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro j hj
  nlinarith [sq_nonneg (x j-y j)]

lemma square_le_of_coord {x : Point} {δ : ℝ} (hδ : 0≤δ) (hx : ∀j,|x j|≤δ) :
    square x≤3*δ^2 := by
  unfold square
  calc
    _ ≤ ∑_j : Fin 3,δ^2 := Finset.sum_le_sum (fun j _ ↦ by simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hδ).mpr (hx j))
    _ = _ := by simp [Finset.sum_const]

lemma cube_kernel_lower {b δ : ℝ} (hb : 0≤b) (hδ : 0≤δ) (x q : Point)
    {y : Point} (hy : y∈cube q δ) :
    kernel b (x-q) ≤ Real.exp (3*b*δ^2)*kernel (b/2) (x-y) := by
  have ht : square (x-y)≤2*square (x-q)+6*δ^2 := by
    have he : x-y=(x-q)+(q-y) := by ext j; simp
    rw [he]
    apply (square_triangle _ _).trans
    have hx : square (q-y)≤3*δ^2 := square_le_of_coord hδ (fun j ↦ by
      simpa only [Pi.sub_apply,abs_sub_comm] using cube_coord hy j)
    linarith
  rw [kernel,kernel,←Real.exp_add]
  apply Real.exp_le_exp.mpr
  nlinarith [mul_le_mul_of_nonneg_left ht hb]

lemma cubes_disjoint {m : ℕ} (q : Fin m → Point) {ε δ : ℝ} (hε : 0<ε) (hδ : 0≤δ)
    (hδε : 4*δ≤ε) (hsep : ∀i j,i≠j → ε^2 ≤ square (q i-q j)) :
    Pairwise (fun i j ↦ Disjoint (cube (q i) δ) (cube (q j) δ)) := by
  intro i j hij
  apply disjoint_left.mpr
  intro y hyi hyj
  have hxy : square (q i-q j)≤3*(2*δ)^2 := square_le_of_coord (by positivity) (fun k ↦ by
    have h1:=cube_coord hyi k
    have h2:=cube_coord hyj k
    rw [abs_le] at h1 h2 ⊢
    change -(2*δ)≤q i k-q j k ∧ q i k-q j k≤2*δ
    constructor <;> linarith)
  have he := hsep i j hij
  have hd : (4*δ)^2≤ε^2 := (sq_le_sq₀ (by positivity) hε.le).mpr hδε
  nlinarith [sq_pos_of_pos hε]

lemma kernel_translate_integrable {b : ℝ} (hb : 0 < b) (x : Point) :
    Integrable (fun y ↦ kernel b (x-y)) volume :=
  (integrable_comp_sub_left (kernel b) x).mpr (kernel_integrable hb)

lemma sum_kernel_le {m : ℕ} (q : Fin m → Point) (x : Point)
    {b ε δ : ℝ} (hb : 0 < b) (hε : 0 < ε) (hδ : 0 < δ)
    (hδε : 4*δ ≤ ε) (hsep : ∀i j, i≠j → ε^2 ≤ square (q i-q j)) :
    (∑i,kernel b (x-q i)) ≤
      Real.exp (3*b*δ^2)*(Real.sqrt (Real.pi/(b/2)))^3/(2*δ)^3 := by
  have hi := kernel_translate_integrable (by positivity : 0 < b/2) x
  have hp := cubes_disjoint q hε hδ.le hδε hsep
  have hc (i : Fin m) : (2*δ)^3*kernel b (x-q i) ≤
      Real.exp (3*b*δ^2)*∫y in cube (q i) δ,kernel (b/2) (x-y) := by
    have hn : (∫y in cube (q i) δ, kernel b (x-q i)) ≤
        ∫y in cube (q i) δ,Real.exp (3*b*δ^2)*kernel (b/2) (x-y) := by
      apply integral_mono_ae (integrableOn_const (μ:=volume) (s:=cube (q i) δ) (C:=kernel b (x-q i)) (IsCompact.measure_lt_top isCompact_Icc).ne)
        ((hi.const_mul _).integrableOn)
      filter_upwards [ae_restrict_mem measurableSet_Icc] with y hy
      exact cube_kernel_lower hb.le hδ.le x (q i) hy
    simpa only [integral_const,measureReal_restrict_apply_univ,smul_eq_mul,
      cube_real_volume _ hδ.le,integral_const_mul] using hn
  have hs := Finset.sum_le_sum (fun i (_ : i∈Finset.univ) ↦ hc i)
  rw [←Finset.mul_sum,←Finset.mul_sum] at hs
  have heu : (∫y in ⋃i,cube (q i) δ,kernel (b/2) (x-y)) = ∑i,∫y in cube (q i) δ,kernel (b/2) (x-y) :=
    integral_iUnion_fintype (fun i ↦ (measurableSet_Icc : MeasurableSet (cube (q i) δ))) hp (fun _ ↦ hi.integrableOn)
  rw [←heu] at hs
  have hm : (∫y in ⋃i,cube (q i) δ,kernel (b/2) (x-y)) ≤
      (Real.sqrt (Real.pi/(b/2)))^3 := by
    apply (integral_mono_measure Measure.restrict_le_self
      (Eventually.of_forall (fun y ↦ (Real.exp_pos _).le)) hi).trans_eq
    exact (integral_sub_left_eq_self (kernel (b/2)) volume x).trans (kernel_integral _)
  have ht := hs.trans (mul_le_mul_of_nonneg_left hm (Real.exp_pos _).le)
  exact (le_div_iff₀ (by positivity : 0 < (2*δ)^3)).mpr (by simpa only [mul_comm] using ht)

end HardSphere.GaussianPacking

end
end

section
noncomputable section
open MeasureTheory MeasureTheory.Measure Set Filter ProbabilityTheory
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.Bridge
open Wiener GaussianPacking
lemma eval_measurable (s : Time) : Measurable (eval s) :=
  Measurable.of_eval fun coordinate ↦
    (continuous_eval_const s).measurable.comp (measurable_pi_apply coordinate)
lemma remainder_measurable (s : Time) : Measurable (remainder s) := by unfold remainder; fun_prop

lemma scalar_eval (s : Time) : bridgeLaw.map (fun β : C(Time,ℝ) ↦ β s)=gaussianReal 0 (variance s) := by
  rw [bridgeLaw,Measure.map_map (continuous_eval_const s).measurable measurable_bridge]
  exact (bridge_eval_law s).map_eq
lemma scalar_remainder (s : Time) : bridgeLaw.map (bridgeRemainder s)=
    bridgeLaw.map (fun β ↦ Real.sqrt (1-(s:ℝ)) • β) := by
  rw [bridgeLaw,Measure.map_map (bridgeRemainder s).continuous.measurable measurable_bridge]
  exact bridgeRemainder_law s
lemma scalar_joint (s : Time) : bridgeLaw.map (fun β : C(Time,ℝ) ↦ (β s,bridgeRemainder s β))=
    (gaussianReal 0 (variance s)).prod (bridgeLaw.map (fun β ↦ Real.sqrt (1-(s:ℝ)) • β)) := by
  rw [bridgeLaw,Measure.map_map (by fun_prop) measurable_bridge]
  simp only [Function.comp_def]
  have hj := (bridgeRemainder_independent s).map_prod_eq_prod_map_map
    (((continuous_eval_const s).measurable.comp measurable_bridge).aemeasurable)
    (((bridgeRemainder s).continuous.measurable.comp measurable_bridge).aemeasurable)
  simp only [Function.comp_def] at hj
  rw [(bridge_eval_law s).map_eq,bridgeRemainder_law] at hj
  exact hj

lemma eval_law (s : Time) : law.map (eval s)=Measure.pi (fun _ : Fin 3 ↦ gaussianReal 0 (variance s)) := by
  unfold law eval
  rw [Measure.pi_map_pi (fun _ ↦ (show Measurable (fun β : C(Time,ℝ) ↦ β s) from (continuous_eval_const s).measurable).aemeasurable)]
  simp_rw [scalar_eval]
lemma remainder_law (s : Time) : law.map (remainder s)=
    law.map (fun β : Noise ↦ fun j ↦ Real.sqrt (1-(s:ℝ)) • β j) := by
  unfold law remainder
  rw [Measure.pi_map_pi (fun _ ↦ (bridgeRemainder s).continuous.measurable.aemeasurable),
    Measure.pi_map_pi (fun _ ↦ (show Measurable (fun β : C(Time,ℝ) ↦ Real.sqrt (1-(s:ℝ)) • β) from by fun_prop).aemeasurable)]
  simp_rw [scalar_remainder]

lemma joint_law (s : Time) : law.map (fun β ↦ (eval s β,remainder s β))=
    (Measure.pi (fun _ : Fin 3 ↦ gaussianReal 0 (variance s))).prod (law.map (remainder s)) := by
  have hp := measurePreserving_arrowProdEquivProdArrow ℝ C(Time,ℝ) (Fin 3)
    (fun _ ↦ gaussianReal 0 (variance s)) (fun _ ↦ bridgeLaw.map (fun β ↦ Real.sqrt (1-(s:ℝ)) • β))
  have he : law.map (fun β : Noise ↦ fun j ↦ (β j s,bridgeRemainder s (β j)))=
      Measure.pi (fun _ : Fin 3 ↦ (gaussianReal 0 (variance s)).prod (bridgeLaw.map (fun β ↦ Real.sqrt (1-(s:ℝ)) • β))) := by
    unfold law
    rw [Measure.pi_map_pi (fun _ ↦ (show Measurable (fun β : C(Time,ℝ) ↦ (β s,bridgeRemainder s β)) from by fun_prop).aemeasurable)]
    simp_rw [scalar_joint]
  rw [remainder_law]
  have her : law.map (fun β : Noise ↦ fun j ↦ Real.sqrt (1-(s:ℝ)) • β j)=
      Measure.pi (fun _ : Fin 3 ↦ bridgeLaw.map (fun β ↦ Real.sqrt (1-(s:ℝ)) • β)) := by
    unfold law
    rw [Measure.pi_map_pi (fun _ ↦ (show Measurable (fun β : C(Time,ℝ) ↦ Real.sqrt (1-(s:ℝ)) • β) from by fun_prop).aemeasurable)]
  rw [her,←hp.map_eq,←he,Measure.map_map hp.measurable (by fun_prop)]
  rfl

lemma independent (s : Time) : IndepFun (eval s) (remainder s) law :=
  (indepFun_iff_map_prod_eq_prod_map_map (eval_measurable s).aemeasurable (remainder_measurable s).aemeasurable).mpr
    (by rw [eval_law]; exact joint_law s)

end HardSphere.Bridge

end
end

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Bridges_BridgeMoment
attribute [-instance] _root_.OAI.HardSphere.Bridge.exposedBridgeKernel_markov _root_.OAI.HardSphere.Bridge.exposedPeriodSingle_finite _root_.OAI.HardSphere.Bridge.exposedTrialKernel_markov _root_.OAI.HardSphere.Bridge.instBorelSpaceContinuousMapElemRealTimePoint _root_.OAI.HardSphere.Bridge.instMeasurableSpaceContinuousMapElemRealTimePoint _root_.OAI.HardSphere.Bridge.parameterBridgeKernel_markov _root_.OAI.HardSphere.Bridge.parameterIndividualReference_finite _root_.OAI.HardSphere.Bridge.parameterTrialKernel_markov _root_.OAI.HardSphere.Bridge.trialKernel_markov _root_.OAI.HardSphere.Groups.cellPathReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Set Filter ProbabilityTheory
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.Wiener

lemma integrable_normCube : Integrable (fun w : C(Time,ℝ) ↦ ‖w‖^3) wiener :=
  (IsGaussian.memLp_id wiener 3 (by norm_num)).integrable_norm_pow (by norm_num)
lemma normCubeMean_nonneg : 0≤normCubeMean := integral_nonneg (fun _ ↦ by positivity)

lemma prefix_wiener_law (u : Time) : wiener.map (prefixMap u)=wiener.map (fun w ↦ Real.sqrt (u:ℝ) • w) := by
  rw [wiener,Measure.map_map (prefixMap u).continuous.measurable measurable_path,
    Measure.map_map (by fun_prop) measurable_path]
  exact prefix_law u

lemma prefix_normCube_integrable (u : Time) :
    Integrable (fun w : C(Time,ℝ) ↦ ‖prefixMap u w‖^3) wiener :=
  ((IsGaussian.memLp_id wiener 3 (by norm_num)).continuousLinearMap_comp (prefixMap u)).integrable_norm_pow (by norm_num)

lemma prefix_normCube (u : Time) :
    ∫w : C(Time,ℝ),‖prefixMap u w‖^3 ∂wiener=(Real.sqrt (u:ℝ))^3*normCubeMean := by
  rw [←integral_map (f:=fun w : C(Time,ℝ) ↦ ‖w‖^3) (prefixMap u).continuous.measurable.aemeasurable (by fun_prop),prefix_wiener_law,
    integral_map (by fun_prop) (by fun_prop)]
  simp only [norm_smul,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _),mul_pow,integral_const_mul,normCubeMean]

lemma cube_add_le {a b : ℝ} (ha : 0≤a) (hb : 0≤b) : (a+b)^3≤4*(a^3+b^3) := by
  have hh : 0≤(a+b)*(a-b)^2 := mul_nonneg (add_nonneg ha hb) (sq_nonneg _)
  nlinarith

lemma prefix_center_norm (u : Time) (w : C(Time,ℝ)) :
    ‖prefixMap u (centerMap w)‖ ≤ ‖prefixMap u w‖+(u:ℝ)*‖w‖ := by
  apply (ContinuousMap.norm_le _ (add_nonneg (norm_nonneg _) (mul_nonneg u.property.1 (norm_nonneg _)))).mpr
  intro s
  simp only [prefixMap_apply,centerMap_apply]
  calc
    ‖w (prefixTime u s)-((prefixTime u s:Time):ℝ)*w 1‖ ≤ ‖w (prefixTime u s)‖+‖((prefixTime u s:Time):ℝ)*w 1‖ := norm_sub_le _ _
    _ ≤ ‖prefixMap u w‖+(u:ℝ)*‖w‖ := by
      apply add_le_add (ContinuousMap.norm_coe_le_norm (prefixMap u w) s)
      rw [norm_mul,Real.norm_eq_abs,abs_of_nonneg (prefixTime u s).property.1]
      apply mul_le_mul _ (ContinuousMap.norm_coe_le_norm w 1) (norm_nonneg _) u.property.1
      change (u:ℝ)*(s:ℝ)≤(u:ℝ)
      exact mul_le_of_le_one_right u.property.1 s.property.2

lemma prefix_bridge_normCube {u : Time} :
    ∫β : C(Time,ℝ),‖prefixMap u β‖^3 ∂bridgeLaw ≤ 8*(Real.sqrt (u:ℝ))^3*normCubeMean := by
  have hp : Integrable (fun w : C(Time,ℝ) ↦ ‖prefixMap u (centerMap w)‖^3) wiener :=
    ((IsGaussian.memLp_id wiener 3 (by norm_num)).continuousLinearMap_comp ((prefixMap u).comp centerMap)).integrable_norm_pow (by norm_num)
  have hq : Integrable (fun w : C(Time,ℝ) ↦ 4*(‖prefixMap u w‖^3+(u:ℝ)^3*‖w‖^3)) wiener :=
    ((prefix_normCube_integrable u).add (integrable_normCube.const_mul _)).const_mul _
  rw [bridgeLaw_center,integral_map centerMap.continuous.measurable.aemeasurable (by fun_prop)]
  calc
    _ ≤ ∫w : C(Time,ℝ),4*(‖prefixMap u w‖^3+(u:ℝ)^3*‖w‖^3) ∂wiener := by
      apply integral_mono hp hq
      intro w
      exact (pow_le_pow_left₀ (norm_nonneg _) (prefix_center_norm u w) 3).trans
        (by simpa only [mul_pow] using cube_add_le (norm_nonneg (prefixMap u w)) (mul_nonneg u.property.1 (norm_nonneg w)))
    _ = 4*((Real.sqrt (u:ℝ))^3*normCubeMean+(u:ℝ)^3*normCubeMean) := by
      rw [integral_const_mul,integral_add (prefix_normCube_integrable u) (integrable_normCube.const_mul _),
        integral_const_mul,prefix_normCube]
      rfl
    _ ≤ _ := by
      have hu : (u:ℝ) ≤ Real.sqrt (u:ℝ) := by
        apply Real.le_sqrt_of_sq_le
        simpa only [pow_two] using mul_le_of_le_one_right u.property.1 u.property.2
      have hh := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ u.property.1 hu 3) normCubeMean_nonneg
      linarith

end HardSphere.Wiener

end

noncomputable section
open MeasureTheory MeasureTheory.Measure Set Filter ProbabilityTheory
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.Bridge
open Wiener GaussianPacking

lemma prefixSize_nonneg (u : Time) (β : Noise) : 0≤prefixSize u β := Finset.sum_nonneg (fun _ _ ↦ norm_nonneg _)
lemma prefixSize_continuous (u : Time) : Continuous (prefixSize u) := by unfold prefixSize; fun_prop
lemma prefixSize_smul (u : Time) (c : ℝ) (β : Noise) :
    prefixSize u (fun j ↦ c • β j)=|c| *prefixSize u β := by
  simp only [prefixSize,map_smul,norm_smul,Real.norm_eq_abs,Finset.mul_sum]
lemma prefixSize_memLp (u : Time) : MemLp (prefixSize u) 3 law := by
  apply memLp_finsetSum
  intro j hj
  have h := ((IsGaussian.memLp_id bridgeLaw 3 (by norm_num)).continuousLinearMap_comp (prefixMap u)).norm
  exact h.comp_measurePreserving (measurePreserving_eval (fun _ : Fin 3 ↦ bridgeLaw) j)

lemma sum_three_cube (f : Fin 3 → ℝ) (hf : ∀j,0≤f j) : (∑j,f j)^3≤16*(∑j,f j^3) := by
  have h := cube_add_le (add_nonneg (hf 0) (hf 1)) (hf 2)
  have h' := cube_add_le (hf 0) (hf 1)
  simp only [Fin.sum_univ_three]
  nlinarith [pow_nonneg (hf 2) 3]

lemma prefixSize_cube_integrable (u : Time) : Integrable (fun β ↦ (prefixSize u β)^3) law := by
  simpa only [Real.norm_eq_abs,abs_of_nonneg (prefixSize_nonneg u _)] using
    (prefixSize_memLp u).integrable_norm_pow (by norm_num : (3:ℕ)≠0)

lemma prefixSize_cube_mean (u : Time) :
    ∫β,(prefixSize u β)^3 ∂law ≤ 384*(Real.sqrt (u:ℝ))^3*normCubeMean := by
  have hi j : Integrable (fun β : Noise ↦ ‖prefixMap u (β j)‖^3) law := by
    exact (((IsGaussian.memLp_id bridgeLaw 3 (by norm_num)).continuousLinearMap_comp (prefixMap u)).comp_measurePreserving
      (measurePreserving_eval (fun _ : Fin 3 ↦ bridgeLaw) j)).integrable_norm_pow (by norm_num : (3:ℕ)≠0)
  calc
    _ ≤ ∫β,16*(∑j,‖prefixMap u (β j)‖^3) ∂law := by
      apply integral_mono (prefixSize_cube_integrable u) ((integrable_finsetSum _ (fun j _ ↦ hi j)).const_mul _)
      intro β
      exact sum_three_cube _ (fun j ↦ norm_nonneg _)
    _ = 16*(∑j : Fin 3,∫β : C(Time,ℝ),‖prefixMap u β‖^3 ∂bridgeLaw) := by
      rw [integral_const_mul,integral_finsetSum _ (fun j _ ↦ hi j)]
      congr 1
      apply Finset.sum_congr rfl
      intro j hj
      have hm := measurePreserving_eval (fun _ : Fin 3 ↦ bridgeLaw) j
      rw [←hm.map_eq,integral_map hm.measurable.aemeasurable (show Continuous (fun β : C(Time,ℝ) ↦ ‖prefixMap u β‖^3) from (prefixMap u).continuous.norm.pow 3).aestronglyMeasurable]
      rfl
    _ ≤ 16*(∑_j : Fin 3,8*(Real.sqrt (u:ℝ))^3*normCubeMean) := by
      exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun _ _ ↦ prefix_bridge_normCube)) (by norm_num)
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]; ring

lemma remainder_prefix_memLp (s u : Time) : MemLp (prefixSize u) 3 (law.map (remainder s)) := by
  have hm : MemLp (fun β ↦ Real.sqrt (1-(s:ℝ))*prefixSize u β) 3 law := (prefixSize_memLp u).const_mul _
  rw [remainder_law]
  apply (memLp_map_measure_iff (g:=prefixSize u) (prefixSize_continuous u).aestronglyMeasurable
    (show Measurable (fun β : Noise ↦ fun j ↦ Real.sqrt (1-(s:ℝ)) • β j) from by fun_prop).aemeasurable).mpr
  simpa only [Function.comp_def,prefixSize_smul,abs_of_nonneg (Real.sqrt_nonneg _)] using hm

lemma remainder_prefix_mean (s u : Time) :
    ∫β,(prefixSize u β)^3 ∂law.map (remainder s) ≤
      384*(Real.sqrt (1-(s:ℝ)))^3*(Real.sqrt (u:ℝ))^3*normCubeMean := by
  rw [remainder_law,integral_map
    (show Measurable (fun β : Noise ↦ fun j ↦ Real.sqrt (1-(s:ℝ)) • β j) from by fun_prop).aemeasurable
    (show Continuous (fun β : Noise ↦ (prefixSize u β)^3) from (prefixSize_continuous u).pow 3).aestronglyMeasurable]
  simp only [prefixSize_smul,abs_of_nonneg (Real.sqrt_nonneg _),mul_pow,integral_const_mul]
  have hh:=mul_le_mul_of_nonneg_left (prefixSize_cube_mean u) (show 0≤(Real.sqrt (1-(s:ℝ)))^3 by positivity)
  calc
    _ ≤ _ := hh
    _ = _ := by ring

end HardSphere.Bridge

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Bridges_GaussianDensity
attribute [-instance] _root_.OAI.HardSphere.Bridge.exposedBridgeKernel_markov _root_.OAI.HardSphere.Bridge.exposedPeriodSingle_finite _root_.OAI.HardSphere.Bridge.exposedTrialKernel_markov _root_.OAI.HardSphere.Bridge.instBorelSpaceContinuousMapElemRealTimePoint _root_.OAI.HardSphere.Bridge.instIsProbabilityMeasurePointMidpointNoise _root_.OAI.HardSphere.Bridge.instMeasurableSpaceContinuousMapElemRealTimePoint _root_.OAI.HardSphere.Bridge.parameterBridgeKernel_markov _root_.OAI.HardSphere.Bridge.parameterIndividualReference_finite _root_.OAI.HardSphere.Bridge.parameterTrialKernel_markov _root_.OAI.HardSphere.Bridge.targetUniform_finite _root_.OAI.HardSphere.Bridge.trialKernel_markov _root_.OAI.HardSphere.Comparison.parameterTargetKernel_finite _root_.OAI.HardSphere.Groups.cellPathReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.vertexPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory MeasureTheory.Measure Set Filter ProbabilityTheory
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.GaussianPacking

lemma density_nonneg (b : ℝ) (x : Point) : 0 ≤ density b x := by unfold density kernel; positivity
lemma density_continuous (b : ℝ) : Continuous (density b) := by unfold density kernel square; fun_prop

lemma sum_density_le {m : ℕ} (q : Fin m → Point) (x : Point)
    {b ε δ : ℝ} (hb : 0<b) (hε : 0<ε) (hδ : 0<δ)
    (hδε : 4*δ≤ε) (hbd : b*δ^2≤1)
    (hsep : ∀i j, i≠j → ε^2 ≤ square (q i-q j)) :
    (∑i,density b (x-q i)) ≤ Real.exp 3*(Real.sqrt 2)^3/(2*δ)^3 := by
  have hs := mul_le_mul_of_nonneg_left (sum_kernel_le q x hb hε hδ hδε hsep)
    (show 0≤(Real.sqrt (b/Real.pi))^3 by positivity)
  have he : (Real.sqrt (b/Real.pi))^3*(Real.sqrt (Real.pi/(b/2)))^3=(Real.sqrt 2)^3 := by
    rw [←mul_pow,←Real.sqrt_mul (by positivity)]
    congr 2
    field_simp
  calc
    _ = (Real.sqrt (b/Real.pi))^3*(∑i,kernel b (x-q i)) := by simp only [density,Finset.mul_sum]
    _ ≤ _ := hs
    _ = Real.exp (3*b*δ^2)*(Real.sqrt 2)^3/(2*δ)^3 := by
      calc
        _ = Real.exp (3*b*δ^2)*((Real.sqrt (b/Real.pi))^3*(Real.sqrt (Real.pi/(b/2)))^3)/(2*δ)^3 := by ring
        _ = _ := by rw [he]
    _ ≤ _ := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (by nlinarith)) (by positivity)

lemma packingConstant_pos : 0<packingConstant := by unfold packingConstant; positivity

theorem density_packing {m : ℕ} (q : Fin m → Point) (x : Point)
    {b ε : ℝ} (hb : 0<b) (hε : 0<ε)
    (hsep : ∀i j,i≠j → ε^2 ≤ square (q i-q j)) :
    (∑i,density b (x-q i)) ≤ packingConstant*(ε⁻¹^3+(Real.sqrt b)^3) := by
  let δ := min (ε/4) (Real.sqrt b)⁻¹
  have hsb := Real.sqrt_pos.mpr hb
  have hd : 0<δ := lt_min (by positivity) (by positivity)
  have hde : 4*δ≤ε := by have ht:=min_le_left (ε/4) (Real.sqrt b)⁻¹; dsimp only [δ]; linarith
  have hdb : b*δ^2≤1 := by
    have ht := min_le_right (ε/4) (Real.sqrt b)⁻¹
    have hm : Real.sqrt b*δ≤1 := by
      have := mul_le_mul_of_nonneg_left ht hsb.le
      simpa only [mul_inv_cancel₀ hsb.ne'] using this
    have hm2 := (sq_le_sq₀ (by positivity : 0≤Real.sqrt b*δ) zero_le_one).mpr hm
    simpa only [mul_pow,Real.sq_sqrt hb.le,one_pow] using hm2
  have hh := sum_density_le q x hb hε hd hde hdb hsep
  apply hh.trans
  have hs : 0≤Real.exp 3*(Real.sqrt 2)^3 := by positivity
  have hbound : (2*δ)⁻¹^3 ≤ 8*(ε⁻¹^3+(Real.sqrt b)^3) := by
    by_cases ht : ε/4≤(Real.sqrt b)⁻¹
    · have he : δ=ε/4 := min_eq_left ht
      rw [he]
      have he' : (2*(ε/4))⁻¹=2*ε⁻¹ := by field_simp; ring
      rw [he',mul_pow]
      nlinarith [show 0≤(Real.sqrt b)^3 by positivity]
    · have he : δ=(Real.sqrt b)⁻¹ := min_eq_right (le_of_not_ge ht)
      rw [he,mul_inv_rev,inv_inv,mul_pow]
      calc
        _ ≤ (Real.sqrt b)^3*8 := mul_le_mul_of_nonneg_left (by norm_num) (by positivity)
        _ ≤ 8*(ε⁻¹^3+(Real.sqrt b)^3) := by
          rw [mul_comm ((Real.sqrt b)^3)]
          exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (by positivity)) (by norm_num)

  unfold packingConstant
  rw [div_eq_mul_inv,←inv_pow]
  nlinarith [mul_le_mul_of_nonneg_left hbound hs]

lemma gaussianDensity_nonneg (q : Point) (v : ℝ≥0) (x : Point) : 0≤gaussianDensity q v x :=
  Finset.prod_nonneg (fun _ _ ↦ gaussianPDFReal_nonneg _ _ _)
lemma gaussianDensity_integrable (q : Point) (v : ℝ≥0) : Integrable (gaussianDensity q v) volume :=
  Integrable.fintype_prod (fun j ↦ integrable_gaussianPDFReal (q j) v)

theorem gaussian_pi_density (q : Point) {v : ℝ≥0} (hv : v≠0) :
    Measure.pi (fun j : Fin 3 ↦ gaussianReal (q j) v)=
      (volume : Measure Point).withDensity (fun x ↦ ENNReal.ofReal (gaussianDensity q v x)) := by
  apply Measure.pi_eq
  intro s hs
  rw [withDensity_apply' _ _,←ofReal_integral_eq_lintegral_ofReal
    (gaussianDensity_integrable q v).restrict (Eventually.of_forall (gaussianDensity_nonneg q v))]
  change ENNReal.ofReal (∫x,gaussianDensity q v x ∂(Measure.pi (fun _ : Fin 3 ↦ (volume : Measure ℝ))).restrict (univ.pi s))=_
  rw [Measure.restrict_pi_pi]
  unfold gaussianDensity
  rw [integral_fintype_prod_eq_prod]
  simp_rw [gaussianReal_apply_eq_integral _ hv]
  exact ENNReal.ofReal_prod_of_nonneg (fun j _ ↦ integral_nonneg (gaussianPDFReal_nonneg (q j) v))

lemma gaussianDensity_eq (q x : Point) {v : ℝ≥0} (hv : v≠0) :
    gaussianDensity q v x=density ((2*(v:ℝ))⁻¹) (x-q) := by
  have hvp : 0<(v:ℝ) := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hv)
  unfold gaussianDensity gaussianPDFReal density
  rw [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,Fintype.card_fin]
  have he : (Real.sqrt (2*Real.pi*(v:ℝ)))⁻¹=Real.sqrt ((2*(v:ℝ))⁻¹/Real.pi) := by
    rw [←Real.sqrt_inv]
    congr 1
    field_simp
  rw [he]
  congr 1
  rw [kernel_product]
  apply Finset.prod_congr rfl
  intro j hj
  congr 1
  simp only [Pi.sub_apply]
  ring

lemma gaussian_pi_eq (q : Point) {v : ℝ≥0} (hv : v≠0) :
    Measure.pi (fun j : Fin 3 ↦ gaussianReal (q j) v)=
      (volume : Measure Point).withDensity (fun x ↦ ENNReal.ofReal (density ((2*(v:ℝ))⁻¹) (x-q))) := by
  rw [gaussian_pi_density q hv]
  congr 1
  funext x
  rw [gaussianDensity_eq q x hv]

end HardSphere.GaussianPacking

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Bridges_GaussianMixture
attribute [-instance] _root_.OAI.HardSphere.Bridge.exposedBridgeKernel_markov _root_.OAI.HardSphere.Bridge.exposedPeriodSingle_finite _root_.OAI.HardSphere.Bridge.exposedTrialKernel_markov _root_.OAI.HardSphere.Bridge.instIsProbabilityMeasurePointMidpointNoise _root_.OAI.HardSphere.Bridge.parameterBridgeKernel_markov _root_.OAI.HardSphere.Bridge.parameterIndividualReference_finite _root_.OAI.HardSphere.Bridge.parameterTrialKernel_markov _root_.OAI.HardSphere.Bridge.targetUniform_finite _root_.OAI.HardSphere.Comparison.parameterTargetKernel_finite _root_.OAI.HardSphere.Groups.cellPathReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open MeasureTheory MeasureTheory.Measure Set Filter ProbabilityTheory
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.GaussianPacking

lemma gaussian_sum_density {m : ℕ} (q : Fin m → Point) {v : ℝ≥0} (hv : v≠0) :
    (∑i,Measure.pi (fun j : Fin 3 ↦ gaussianReal (q i j) v))=
    (volume : Measure Point).withDensity (fun x ↦ ENNReal.ofReal (∑i,density ((2*(v:ℝ))⁻¹) (x-q i))) := by
  simp_rw [gaussian_pi_eq (q _) hv]
  have hm (i : Fin m) : Measurable (fun x : Point ↦ ENNReal.ofReal (density ((2*(v:ℝ))⁻¹) (x-q i))) :=
    ((density_continuous _).measurable.comp (measurable_id.sub measurable_const)).ennreal_ofReal
  have hw := withDensity_tsum (μ:=(volume : Measure Point)) hm
  rw [←Measure.sum_fintype,←hw]
  congr 1
  funext x
  rw [tsum_fintype]
  simp only [Finset.sum_apply]
  exact (ENNReal.ofReal_sum_of_nonneg (fun i _ ↦ density_nonneg _ _)).symm

lemma gaussian_sum_le {m : ℕ} (q : Fin m → Point) {v : ℝ≥0} (hv : v≠0)
    {ε : ℝ} (hε : 0<ε) (hsep : ∀i j,i≠j → ε^2 ≤ square (q i-q j)) :
    (∑i,Measure.pi (fun j : Fin 3 ↦ gaussianReal (q i j) v)) ≤
      ENNReal.ofReal (packingConstant*(ε⁻¹^3+(Real.sqrt ((2*(v:ℝ))⁻¹))^3)) • (volume : Measure Point) := by
  have hvp : 0<(v:ℝ) := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hv)
  rw [gaussian_sum_density q hv,←withDensity_const]
  exact withDensity_mono (Eventually.of_forall fun x ↦ ENNReal.ofReal_le_ofReal
    (density_packing q x (by positivity) hε hsep))

lemma scaled_separated {m : ℕ} (q : Fin m → Point) (u : Point) {a ε : ℝ}
    (ha : 0≤a) (hε : 0≤ε) (hsep : ∀i j,i≠j → ε^2 ≤ square (q i-q j)) :
    ∀i j,i≠j → (a*ε)^2 ≤ square ((fun k ↦ a*q i k+(1-a)*u k)-(fun k ↦ a*q j k+(1-a)*u k)) := by
  intro i j hij
  have he : square ((fun k ↦ a*q i k+(1-a)*u k)-(fun k ↦ a*q j k+(1-a)*u k))=a^2*square (q i-q j) := by
    unfold square
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    simp only [Pi.sub_apply]
    ring
  rw [he,mul_pow]
  exact mul_le_mul le_rfl (hsep i j hij) (pow_nonneg hε 2) (pow_nonneg ha 2)

end HardSphere.GaussianPacking

end
end

section
noncomputable section
open MeasureTheory MeasureTheory.Measure Set Filter ProbabilityTheory
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.Bridge
open Wiener GaussianPacking

lemma leg_continuous (t : ℝ) (y u : Point) : Continuous (leg t y u) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  change Continuous (fun p : Noise×Time ↦ fun j ↦ mean y u p.2 j+Real.sqrt (2*t)*p.1 j p.2)
  unfold mean
  fun_prop
lemma leg_eval_measurable (t : ℝ) (y u : Point) (s : Time) : Measurable (fun β ↦ leg t y u β s) :=
  (show Continuous (fun β : Noise ↦ leg t y u β s) from (continuous_eval_const s).comp (leg_continuous t y u)).measurable

lemma variance_val (s : Time) : (variance s : ℝ)=(s:ℝ)*(1-(s:ℝ)) := by
  have hp : 0≤(s:ℝ)-(s:ℝ)^2 := by nlinarith [s.property.1,s.property.2]
  rw [variance,Real.coe_toNNReal _ hp]
  ring
lemma legVariance_val {t : ℝ} (ht : 0≤t) (s : Time) : (legVariance t s : ℝ)=2*t*(s:ℝ)*(1-(s:ℝ)) := by
  change (Real.sqrt (2*t))^2*(variance s : ℝ)=_
  rw [Real.sq_sqrt (by positivity),variance_val]
  ring
lemma legVariance_pos {t : ℝ} (ht : 0<t) {s : Time} (hs : 0<(s:ℝ)) (hs1 : (s:ℝ)<1) :
    0<legVariance t s := by
  rw [←NNReal.coe_pos,legVariance_val ht.le]
  positivity

lemma position_law (t : ℝ) (y u : Point) (s : Time) :
    law.map (fun β ↦ leg t y u β s)=Measure.pi (fun j ↦ gaussianReal (mean y u s j) (legVariance t s)) := by
  have hs : HasLaw (fun β : C(Time,ℝ) ↦ β s) (gaussianReal 0 (variance s)) bridgeLaw :=
    ⟨(continuous_eval_const s).measurable.aemeasurable,scalar_eval s⟩
  unfold law
  change (Measure.pi (fun _ : Fin 3 ↦ bridgeLaw)).map
    (fun β j ↦ mean y u s j+Real.sqrt (2*t)*β j s)=_
  rw [Measure.pi_map_pi (f:=fun j (β : C(Time,ℝ)) ↦ mean y u s j+Real.sqrt (2*t)*β s)
    (fun j ↦ (gaussianReal_const_add (gaussianReal_const_mul hs (Real.sqrt (2*t))) (mean y u s j)).aemeasurable)]
  congr 1
  funext j
  simpa only [mul_zero,zero_add,legVariance] using
    (gaussianReal_const_add (gaussianReal_const_mul hs (Real.sqrt (2*t))) (mean y u s j)).map_eq

lemma position_independent (t : ℝ) (y u : Point) (s : Time) :
    IndepFun (fun β ↦ leg t y u β s) (remainder s) law := by
  have hi := (independent s).comp
    (show Measurable (fun x : Point ↦ fun j ↦ mean y u s j+Real.sqrt (2*t)*x j) from by fun_prop) measurable_id
  exact hi

lemma position_joint (t : ℝ) (y u : Point) (s : Time) :
    law.map (fun β ↦ (remainder s β,leg t y u β s))=
      (law.map (remainder s)).prod (Measure.pi (fun j ↦ gaussianReal (mean y u s j) (legVariance t s))) := by
  rw [(position_independent t y u s).symm.map_prod_eq_prod_map_map (remainder_measurable s).aemeasurable
    (leg_eval_measurable t y u s).aemeasurable,position_law]

lemma mean_separated {m : ℕ} (y : Fin m → Point) (u : Point) (s : Time) {ε : ℝ} (hε : 0≤ε)
    (hsep : ∀i j,i≠j → ε^2 ≤ square (y i-y j)) :
    ∀i j,i≠j → ((1-(s:ℝ))*ε)^2 ≤ square (mean (y i) u s-mean (y j) u s) := by
  unfold mean
  simpa only [sub_sub_cancel] using scaled_separated y u (a:=1-(s:ℝ)) (sub_nonneg.mpr s.property.2) hε hsep

end HardSphere.Bridge

end
end

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology
namespace HardSphere.Bridge
open Wiener GaussianPacking
lemma center_zero (β : C(Time,ℝ)) : center β 0=0 := by simp [center,linearPath]
lemma center_one (β : C(Time,ℝ)) : center β 1=0 := by simp [center,linearPath]
lemma center_eq {β : C(Time,ℝ)} (h0 : β 0=0) (h1 : β 1=0) : center β=β := by simp [center,h0,h1]
lemma pinned_continuous : Continuous pinned := continuous_pi (fun j ↦ center_continuous.comp (continuous_apply j))
lemma pinned_law : law.map pinned=law := by
  have h : pinned=ᵐ[law] id := by
    have hβ : ∀j : Fin 3,∀ᵐ β ∂law,(β j) 0=0 ∧ (β j) 1=0 := fun j ↦ by
      exact (measurePreserving_eval (fun _ : Fin 3 ↦ bridgeLaw) j).quasiMeasurePreserving.ae bridge_endpoints
    filter_upwards [ae_all_iff.mpr hβ] with β hβ
    funext j
    exact center_eq (hβ j).1 (hβ j).2
  rw [Measure.map_congr h,Measure.map_id]

lemma pinned_leg_zero (t : ℝ) (y u : Point) (β : Noise) : leg t y u (pinned β) 0=y := by
  ext j
  simp [leg,mean,pinned,center_zero]
lemma pinned_leg_one (t : ℝ) (y u : Point) (β : Noise) : leg t y u (pinned β) 1=u := by
  ext j
  simp [leg,mean,pinned,center_one]

end HardSphere.Bridge

end
end

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Bridges_BridgeNoise
attribute [-instance] _root_.OAI.HardSphere.Bridge.exposedBridgeKernel_markov _root_.OAI.HardSphere.Bridge.exposedPeriodSingle_finite _root_.OAI.HardSphere.Bridge.exposedTrialKernel_markov _root_.OAI.HardSphere.Bridge.instIsProbabilityMeasurePointMidpointNoise _root_.OAI.HardSphere.Bridge.parameterBridgeKernel_markov _root_.OAI.HardSphere.Bridge.parameterIndividualReference_finite _root_.OAI.HardSphere.Bridge.parameterTrialKernel_markov _root_.OAI.HardSphere.Bridge.targetUniform_finite _root_.OAI.HardSphere.Comparison.parameterTargetKernel_finite _root_.OAI.HardSphere.Groups.cellPathReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open MeasureTheory MeasureTheory.Measure Set Filter ProbabilityTheory
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.Bridge
open Wiener GaussianPacking

lemma fluctuation_continuous (t r : ℝ) (u : Time) : Continuous (fluctuation t r u) :=
  (prefixSize_continuous u).const_mul _
lemma fluctuation_nonneg {t r : ℝ} (hr : 0 ≤ r) (u : Time) (β : Noise) : 0≤fluctuation t r u β :=
  mul_nonneg (div_nonneg (Real.sqrt_nonneg _) hr) (prefixSize_nonneg u β)
lemma fluctuation_memLp (t r : ℝ) (s u : Time) : MemLp (fluctuation t r u) 3 (law.map (remainder s)) :=
  (remainder_prefix_memLp s u).const_mul _

lemma fluctuation_mean {t r : ℝ} (ht : 0≤t) (hr : 0 < r) (s u : Time)
    (hscale : t*(1-(s:ℝ))*(u:ℝ) ≤ r^2) :
    ∫β,(fluctuation t r u β)^3 ∂law.map (remainder s) ≤ 3072*normCubeMean := by
  let a := Real.sqrt (2*t)/r*Real.sqrt (1-(s:ℝ))*Real.sqrt (u:ℝ)
  have ha0 : 0≤a := by dsimp [a]; positivity
  have ha2 : a^2≤2 := by
    dsimp [a]
    rw [mul_pow,mul_pow,div_pow,Real.sq_sqrt (by positivity),Real.sq_sqrt (sub_nonneg.mpr s.property.2),Real.sq_sqrt u.property.1]
    rw [div_mul_eq_mul_div,div_mul_eq_mul_div]
    apply (div_le_iff₀ (sq_pos_of_pos hr)).mpr
    convert mul_le_mul_of_nonneg_left hscale (by norm_num : (0:ℝ)≤2) using 1
    all_goals try with_reducible_and_instances rfl
    ring
  have ha : a≤2 := by nlinarith
  have hb := mul_le_mul_of_nonneg_left (remainder_prefix_mean s u)
    (show 0≤(Real.sqrt (2*t)/r)^3 by positivity)
  simp only [fluctuation,mul_pow,integral_const_mul]
  calc
    _ ≤ _ := hb
    _ = 384*a^3*normCubeMean := by dsimp [a]; ring
    _ ≤ 3072*normCubeMean := by
      have hc := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ ha0 ha 3) normCubeMean_nonneg
      nlinarith

lemma prefix_norm_eval (u q : Time) (hq : (q:ℝ)≤(u:ℝ)) (β : C(Time,ℝ)) :
    ‖β q‖≤‖prefixMap u β‖ := by
  by_cases hu : (u:ℝ)=0
  · have hq0 : (q:ℝ)=0 := le_antisymm (hq.trans_eq hu) q.property.1
    have he : prefixTime u 0=q := Subtype.ext (by simp [prefixTime,hq0])
    simpa only [prefixMap_apply,he] using ContinuousMap.norm_coe_le_norm (prefixMap u β) 0
  · have hup : 0<(u:ℝ) := lt_of_le_of_ne u.property.1 (Ne.symm hu)
    let z : Time := ⟨(q:ℝ)/(u:ℝ),div_nonneg q.property.1 u.property.1,(div_le_one hup).mpr hq⟩
    have he : prefixTime u z=q := by apply Subtype.ext; dsimp [prefixTime,z]; field_simp
    simpa only [prefixMap_apply,he] using ContinuousMap.norm_coe_le_norm (prefixMap u β) z

lemma fluctuation_eval {t r : ℝ} (hr : 0 < r) (u q : Time) (hq : (q:ℝ)≤(u:ℝ)) (β : Noise) (j : Fin 3) :
    |Real.sqrt (2*t)*β j q| ≤ r*fluctuation t r u β := by
  have hp : ‖β j q‖≤prefixSize u β := (prefix_norm_eval u q hq (β j)).trans
    (Finset.single_le_sum (fun i _ ↦ norm_nonneg (prefixMap u (β i))) (Finset.mem_univ j))
  rw [abs_mul,abs_of_nonneg (Real.sqrt_nonneg _)]
  have he : r*fluctuation t r u β=Real.sqrt (2*t)*prefixSize u β := by unfold fluctuation; field_simp
  rw [he]
  exact mul_le_mul_of_nonneg_left hp (Real.sqrt_nonneg _)

end HardSphere.Bridge

end
end

section
noncomputable section
open MeasureTheory MeasureTheory.Measure Set Filter ProbabilityTheory
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.GaussianPacking

lemma cube_volume (q : Point) {δ : ℝ} (hδ : 0≤δ) :
    (volume : Measure Point) (cube q δ)=ENNReal.ofReal ((2*δ)^3) := by
  rw [←cube_real_volume q hδ,Measure.real,ENNReal.ofReal_toReal]
  exact (IsCompact.measure_lt_top isCompact_Icc).ne

lemma measurable_cube_event {Ω : Type*} [MeasurableSpace Ω] {R : Ω → ℝ}
    (hR : Measurable R) (c : Point) (r A : ℝ) :
    MeasurableSet {p : Ω×Point | p.2∈cube c (r*(A+R p.1))} := by
  apply Measurable.setOf
  have hm (j : Fin 3) : Measurable (fun p : Ω×Point ↦ p.2 j) := (measurable_pi_apply j).comp measurable_snd
  exact (Measurable.forall fun j ↦ (measurableSet_le (measurable_const.sub
    ((hR.comp measurable_fst).const_add A |>.const_mul r)) (hm j)).mem).and
    (Measurable.forall fun j ↦ (measurableSet_le (hm j) (measurable_const.add
      ((hR.comp measurable_fst).const_add A |>.const_mul r))).mem)

theorem collision_volume_bound {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) [IsProbabilityMeasure ν] (μ : Measure Point) [SFinite μ]
    {R : Ω → ℝ} (hR : Measurable R) (hR0 : ∀ω,0≤R ω) (hR3 : MemLp R 3 ν)
    (c : Point) {r A C : ℝ} (hr : 0 ≤ r) (hA : 0≤A) (hC : 0≤C)
    (hμ : μ ≤ ENNReal.ofReal C • (volume : Measure Point)) :
    (ν.prod μ) {p : Ω×Point | p.2∈cube c (r*(A+R p.1))} ≤
      ENNReal.ofReal (8*C*r^3*(∫ω,(A+R ω)^3 ∂ν)) := by
  have hInt : Integrable (fun ω ↦ (A+R ω)^3) ν := by
    have h := ((memLp_const A).add hR3).integrable_norm_pow (by norm_num : (3:ℕ)≠0)
    simpa only [Pi.add_apply,Real.norm_eq_abs,abs_of_nonneg (add_nonneg hA (hR0 _))] using h
  rw [Measure.prod_apply (measurable_cube_event hR c r A)]
  calc
    _ ≤ ∫⁻ω,ENNReal.ofReal C*(volume : Measure Point) (cube c (r*(A+R ω))) ∂ν := by
      apply lintegral_mono
      intro ω
      exact hμ (cube c (r*(A+R ω)))
    _ = ∫⁻ω,ENNReal.ofReal (8*C*r^3*(A+R ω)^3) ∂ν := by
      apply lintegral_congr
      intro ω
      have hp : 0≤R ω := hR0 ω
      rw [cube_volume c (by positivity),←ENNReal.ofReal_mul hC]
      congr 1
      ring
    _ = _ := by
      rw [←ofReal_integral_eq_lintegral_ofReal (hInt.const_mul _)
        (Eventually.of_forall fun ω ↦ by have hp:=hR0 ω; positivity),integral_const_mul]

theorem collision_cubic_bound {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) [IsProbabilityMeasure ν] (μ : Measure Point) [SFinite μ]
    {R : Ω → ℝ} (hR : Measurable R) (hR0 : ∀ω,0≤R ω) (hR3 : MemLp R 3 ν)
    (c : Point) {r A C : ℝ} (hr : 0 ≤ r) (hA : 0≤A) (hC : 0≤C)
    (hμ : μ ≤ ENNReal.ofReal C • (volume : Measure Point)) :
    (ν.prod μ) {p : Ω×Point | p.2∈cube c (r*(A+R p.1))} ≤
      ENNReal.ofReal (32*C*r^3*(A^3+∫ω,(R ω)^3 ∂ν)) := by
  apply (collision_volume_bound ν μ hR hR0 hR3 c hr hA hC hμ).trans
  apply ENNReal.ofReal_le_ofReal
  have hInt0 : Integrable (fun ω ↦ (R ω)^3) ν := by
    simpa only [Real.norm_eq_abs,abs_of_nonneg (hR0 _)] using hR3.integrable_norm_pow (by norm_num : (3:ℕ)≠0)
  have hInt : Integrable (fun ω ↦ (A+R ω)^3) ν := by
    simpa only [Pi.add_apply,Real.norm_eq_abs,abs_of_nonneg (add_nonneg hA (hR0 _))] using
      ((memLp_const A).add hR3).integrable_norm_pow (by norm_num : (3:ℕ)≠0)
  have hi : (∫ω,(A+R ω)^3 ∂ν) ≤ 4*(A^3+∫ω,R ω^3 ∂ν) := by
    have h := integral_mono hInt (((integrable_const (A^3)).add hInt0).const_mul 4)
      (fun ω ↦ Wiener.cube_add_le hA (hR0 ω))
    simpa only [Pi.add_apply,integral_const_mul,integral_add (integrable_const (A^3)) hInt0,
      integral_const,Measure.real,measure_univ,ENNReal.toReal_one,one_smul] using h
  nlinarith [mul_le_mul_of_nonneg_left hi (show 0≤8*C*r^3 by positivity)]

end HardSphere.GaussianPacking

end
end

section
noncomputable section
open MeasureTheory MeasureTheory.Measure Set Filter ProbabilityTheory
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.Bridge
open Wiener GaussianPacking

lemma leg_segment (t : ℝ) (y v : Point) (β : Noise) (s q : Time) (j : Fin 3) :
    leg t y v β (suffixTime s q) j=leg t y v β s j+
      (q:ℝ)*(v j-leg t y v β s j)+Real.sqrt (2*t)*remainder s β j q := by
  simp only [leg,ContinuousMap.coe_mk,mean,remainder,bridgeRemainder_apply]
  dsimp [suffixTime]
  ring

lemma segment_necessary {t r C A : ℝ} (hr : 0 < r) (hC : 0≤C) (y v : Point) (s w : Time)
    (c : Time → Point) (hA : ∀q : Time,(q:ℝ)≤(w:ℝ) → ‖c q-c 0‖ ≤ r*A)
    (hdrift : (w:ℝ)*C ≤ r) : segmentHit t y v s w c r C ⊆
      {β | leg t y v β s ∈ cube (c 0) (r*(2+A+fluctuation t r w (remainder s β)))} := by
  rintro β ⟨hc,q,hq,hh⟩
  have hb (j : Fin 3) : |leg t y v β s j-c 0 j| ≤ r*(2+A+fluctuation t r w (remainder s β)) := by
    have hi : |leg t y v β (suffixTime s q) j-c q j| ≤ r := (norm_le_pi_norm _ j).trans hh
    have ho : |c q j-c 0 j| ≤ r*A := (norm_le_pi_norm _ j).trans (hA q hq)
    have hd : |(q:ℝ)*(v j-leg t y v β s j)| ≤ r := by
      rw [abs_mul,abs_of_nonneg q.property.1,abs_sub_comm]
      exact (mul_le_mul_of_nonneg_left ((norm_le_pi_norm _ j).trans hc) q.property.1).trans
        ((mul_le_mul_of_nonneg_right hq hC).trans hdrift)
    have hn := fluctuation_eval (t:=t) hr w q hq (remainder s β) j
    have he : leg t y v β s j-c 0 j=
        ((leg t y v β (suffixTime s q) j-c q j)+(c q j-c 0 j))-
        (q:ℝ)*(v j-leg t y v β s j)-Real.sqrt (2*t)*remainder s β j q := by rw [leg_segment]; ring
    rw [he]
    calc
      _ ≤ (|leg t y v β (suffixTime s q) j-c q j|+|c q j-c 0 j|)+
          |(q:ℝ)*(v j-leg t y v β s j)|+|Real.sqrt (2*t)*remainder s β j q| :=
        (abs_sub _ _).trans (add_le_add ((abs_sub _ _).trans (add_le_add (abs_add_le _ _) le_rfl)) le_rfl)
      _ ≤ (r+r*A)+r+r*fluctuation t r w (remainder s β) := by gcongr
      _ = _ := by ring
  exact ⟨fun j ↦ by have h := (abs_le.mp (hb j)).1; dsimp; linarith,
    fun j ↦ by have h := (abs_le.mp (hb j)).2; dsimp; linarith⟩

lemma segment_sum_bound {m : ℕ} (y : Fin m → Point) (v : Point) (s w : Time)
    (c : Time → Point) {t r C A ε : ℝ} (ht : 0<t) (hr : 0 < r) (hC : 0≤C) (hA0 : 0≤A)
    (hs : 0<(s:ℝ)) (hs1 : (s:ℝ)<1) (hε : 0<ε)
    (hsep : ∀i j,i≠j → ε^2 ≤ square (y i-y j))
    (hA : ∀q : Time,(q:ℝ)≤(w:ℝ) → ‖c q-c 0‖ ≤ r*A)
    (hdrift : (w:ℝ)*C ≤ r) (hscale : t*(1-(s:ℝ))*(w:ℝ) ≤ r^2) :
    (∑i,law (segmentHit t (y i) v s w c r C)) ≤
      ENNReal.ofReal (32*(packingConstant*(((1-(s:ℝ))*ε)⁻¹^3+
        (Real.sqrt ((2*(legVariance t s:ℝ))⁻¹))^3))*r^3*((2+A)^3+3072*normCubeMean)) := by
  let ν := law.map (remainder s)
  let μ (i : Fin m) := Measure.pi (fun j : Fin 3 ↦ gaussianReal (mean (y i) v s j) (legVariance t s))
  let R := fluctuation t r w
  let E := {p : Noise×Point | p.2∈cube (c 0) (r*((2+A)+R p.1))}
  have hE : MeasurableSet E := measurable_cube_event (fluctuation_continuous t r w).measurable (c 0) r (2+A)
  have : IsProbabilityMeasure ν := Measure.isProbabilityMeasure_map (remainder_measurable s).aemeasurable
  have hu : (∑i,law (segmentHit t (y i) v s w c r C)) ≤ (ν.prod (∑i,μ i)) E := by
    rw [←Measure.sum_fintype,Measure.prod_sum_right,Measure.sum_fintype,Measure.finsetSum_apply]
    apply Finset.sum_le_sum
    intro i hi
    apply (measure_mono (segment_necessary hr hC (y i) v s w c hA hdrift)).trans_eq
    have he : {β | leg t (y i) v β s∈cube (c 0) (r*(2+A+R (remainder s β)))}=
        (fun β ↦ (remainder s β,leg t (y i) v β s))⁻¹' E := rfl
    rw [he,←Measure.map_apply ((remainder_measurable s).prodMk (leg_eval_measurable t (y i) v s)) hE,position_joint]
  have hμ := gaussian_sum_le (fun i ↦ mean (y i) v s) (legVariance_pos ht hs hs1).ne'
    (mul_pos (sub_pos.mpr hs1) hε) (mean_separated y v s hε.le hsep)
  have hb := collision_cubic_bound ν (∑i,μ i) (fluctuation_continuous t r w).measurable
    (fluctuation_nonneg hr.le w) (fluctuation_memLp t r s w) (c 0) hr.le (by positivity : 0≤2+A)
    (show 0≤packingConstant*(((1-(s:ℝ))*ε)⁻¹^3+(Real.sqrt ((2*(legVariance t s:ℝ))⁻¹))^3) from
      mul_nonneg packingConstant_pos.le (by positivity)) hμ
  apply hu.trans (hb.trans _)
  apply ENNReal.ofReal_le_ofReal
  apply mul_le_mul_of_nonneg_left (add_le_add le_rfl (fluctuation_mean ht.le hr s w hscale))
  exact mul_nonneg (mul_nonneg (by norm_num) (mul_nonneg packingConstant_pos.le (by positivity))) (by positivity)

end HardSphere.Bridge

end
end

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Bridges_IncrementMoment
attribute [-instance] _root_.OAI.HardSphere.Bridge.exposedBridgeKernel_markov _root_.OAI.HardSphere.Bridge.exposedPeriodSingle_finite _root_.OAI.HardSphere.Bridge.exposedTrialKernel_markov _root_.OAI.HardSphere.Bridge.parameterBridgeKernel_markov _root_.OAI.HardSphere.Bridge.parameterIndividualReference_finite _root_.OAI.HardSphere.Bridge.parameterTrialKernel_markov _root_.OAI.HardSphere.Groups.cellPathReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory MeasureTheory.Measure Set Filter ProbabilityTheory
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.Wiener

lemma suffix_wiener_law (s : Time) : wiener.map (suffixMap s)=wiener.map (fun β ↦ Real.sqrt (1-(s:ℝ)) • β) := by
  rw [wiener,Measure.map_map (suffixMap s).continuous.measurable measurable_path,
    Measure.map_map (by fun_prop) measurable_path]
  exact suffix_law s
lemma increment_wiener_mean (s u : Time) :
    ∫β : C(Time,ℝ),‖incrementMap s u β‖^3 ∂wiener =
      (Real.sqrt ((1-(s:ℝ))*(u:ℝ)))^3*normCubeMean := by
  change (∫β : C(Time,ℝ),‖prefixMap u (suffixMap s β)‖^3 ∂wiener)=_
  rw [←integral_map (f:=fun β : C(Time,ℝ) ↦ ‖prefixMap u β‖^3) (suffixMap s).continuous.measurable.aemeasurable (by fun_prop),suffix_wiener_law,
    integral_map (by fun_prop) (by fun_prop)]
  simp only [map_smul,norm_smul,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _),mul_pow,integral_const_mul]
  rw [prefix_normCube,Real.sqrt_mul (sub_nonneg.mpr s.property.2),mul_pow]
  ring

lemma increment_center_norm (s u : Time) (f : C(Time,ℝ)) :
    ‖incrementMap s u (centerMap f)‖≤‖incrementMap s u f‖+((1-(s:ℝ))*(u:ℝ))*‖f‖ := by
  apply (ContinuousMap.norm_le _ (add_nonneg (norm_nonneg _) (mul_nonneg (mul_nonneg (sub_nonneg.mpr s.property.2) u.property.1) (norm_nonneg _)))).mpr
  intro q
  have hs0 := sub_nonneg.mpr s.property.2
  have hu0 := u.property.1
  have hq0 := q.property.1
  have he : incrementMap s u (centerMap f) q=incrementMap s u f q-
      ((1-(s:ℝ))*(u:ℝ)*(q:ℝ))*f 1 := by
    simp only [incrementMap_apply,centerMap_apply]
    dsimp [suffixTime,prefixTime]
    ring
  rw [he]
  apply (norm_sub_le _ _).trans
  apply add_le_add (ContinuousMap.norm_coe_le_norm _ _)
  rw [norm_mul,Real.norm_eq_abs,abs_of_nonneg (by positivity)]
  apply mul_le_mul _ (ContinuousMap.norm_coe_le_norm f 1) (norm_nonneg _) (by positivity)
  exact mul_le_of_le_one_right (by positivity) q.property.2

lemma increment_bridge_mean (s u : Time) :
    ∫β : C(Time,ℝ),‖incrementMap s u β‖^3 ∂bridgeLaw ≤
      8*(Real.sqrt ((1-(s:ℝ))*(u:ℝ)))^3*normCubeMean := by
  let δ := (1-(s:ℝ))*(u:ℝ)
  have hd : 0≤δ := mul_nonneg (sub_nonneg.mpr s.property.2) u.property.1
  have hd1 : δ≤1 := by dsimp [δ]; nlinarith [s.property.1,s.property.2,u.property.1,u.property.2]
  have hp : Integrable (fun f : C(Time,ℝ) ↦ ‖incrementMap s u (centerMap f)‖^3) wiener :=
    ((IsGaussian.memLp_id wiener 3 (by norm_num)).continuousLinearMap_comp ((incrementMap s u).comp centerMap)).integrable_norm_pow (by norm_num)
  have hi : Integrable (fun f : C(Time,ℝ) ↦ ‖incrementMap s u f‖^3) wiener :=
    ((IsGaussian.memLp_id wiener 3 (by norm_num)).continuousLinearMap_comp (incrementMap s u)).integrable_norm_pow (by norm_num)
  rw [bridgeLaw_center,integral_map centerMap.continuous.measurable.aemeasurable (by fun_prop)]
  calc
    _ ≤ ∫f : C(Time,ℝ),4*(‖incrementMap s u f‖^3+δ^3*‖f‖^3) ∂wiener := by
      apply integral_mono hp ((hi.add (integrable_normCube.const_mul _)).const_mul _)
      intro f
      exact (pow_le_pow_left₀ (norm_nonneg _) (increment_center_norm s u f) 3).trans
        (by simpa only [mul_pow,Pi.add_apply,δ] using cube_add_le (norm_nonneg (incrementMap s u f)) (mul_nonneg hd (norm_nonneg f)))
    _ = 4*((Real.sqrt δ)^3*normCubeMean+δ^3*normCubeMean) := by
      rw [integral_const_mul,integral_add hi (integrable_normCube.const_mul _),integral_const_mul,increment_wiener_mean]
      rfl
    _ ≤ _ := by
      have hds : δ≤Real.sqrt δ := Real.le_sqrt_of_sq_le (by nlinarith)
      have hh := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hd hds 3) normCubeMean_nonneg
      change _ ≤ 8*(Real.sqrt δ)^3*normCubeMean
      linarith

end HardSphere.Wiener

namespace HardSphere.Bridge
open Wiener GaussianPacking

lemma incrementSize_nonneg (s u : Time) (β : Noise) : 0 ≤ incrementSize s u β := Finset.sum_nonneg (fun _ _ ↦ norm_nonneg _)
lemma incrementSize_continuous (s u : Time) : Continuous (incrementSize s u) := by unfold incrementSize; fun_prop
lemma incrementSize_memLp (s u : Time) : MemLp (incrementSize s u) 3 law := by
  apply memLp_finsetSum
  intro j hj
  have h := ((IsGaussian.memLp_id bridgeLaw 3 (by norm_num)).continuousLinearMap_comp (incrementMap s u)).norm
  exact h.comp_measurePreserving (measurePreserving_eval (fun _ : Fin 3 ↦ bridgeLaw) j)

lemma incrementSize_cube_integrable (s u : Time) : Integrable (fun β ↦ (incrementSize s u β)^3) law := by
  simpa only [Real.norm_eq_abs,abs_of_nonneg (incrementSize_nonneg s u _)] using
    (incrementSize_memLp s u).integrable_norm_pow (by norm_num : (3:ℕ)≠0)

lemma incrementSize_cube_mean (s u : Time) :
    ∫β,(incrementSize s u β)^3 ∂law  ≤  384*(Real.sqrt ((1-(s:ℝ))*(u:ℝ)))^3*normCubeMean := by
  have hi j : Integrable (fun β : Noise ↦ ‖incrementMap s u (β j)‖^3) law := by
    exact (((IsGaussian.memLp_id bridgeLaw 3 (by norm_num)).continuousLinearMap_comp (incrementMap s u)).comp_measurePreserving
      (measurePreserving_eval (fun _ : Fin 3 ↦ bridgeLaw) j)).integrable_norm_pow (by norm_num : (3:ℕ)≠0)
  calc
    _  ≤  ∫β,16*(∑j,‖incrementMap s u (β j)‖^3) ∂law := by
      apply integral_mono (incrementSize_cube_integrable s u) ((integrable_finsetSum _ (fun j _ ↦ hi j)).const_mul _)
      intro β
      exact sum_three_cube _ (fun j ↦ norm_nonneg _)
    _ = 16*(∑j : Fin 3,∫β : C(Time,ℝ),‖incrementMap s u β‖^3 ∂bridgeLaw) := by
      rw [integral_const_mul,integral_finsetSum _ (fun j _ ↦ hi j)]
      congr 1
      apply Finset.sum_congr rfl
      intro j hj
      have hm := measurePreserving_eval (fun _ : Fin 3 ↦ bridgeLaw) j
      rw [←hm.map_eq,integral_map hm.measurable.aemeasurable (show Continuous (fun β : C(Time,ℝ) ↦ ‖incrementMap s u β‖^3) from (incrementMap s u).continuous.norm.pow 3).aestronglyMeasurable]
      rfl
    _  ≤  16*(∑_j : Fin 3,8*(Real.sqrt ((1-(s:ℝ))*(u:ℝ)))^3*normCubeMean) := by
      exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun _ _ ↦ increment_bridge_mean s u)) (by norm_num)
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]; ring

lemma incrementFluctuation_continuous (t r : ℝ) (s w : Time) : Continuous (incrementFluctuation t r s w) :=
  (incrementSize_continuous s w).const_mul _
lemma incrementFluctuation_nonneg {t r : ℝ} (hr : 0 ≤ r) (s w : Time) (β : Noise) : 0 ≤ incrementFluctuation t r s w β :=
  mul_nonneg (div_nonneg (Real.sqrt_nonneg _) hr) (incrementSize_nonneg s w β)
lemma incrementFluctuation_memLp (t r : ℝ) (s w : Time) : MemLp (incrementFluctuation t r s w) 3 law :=
  (incrementSize_memLp s w).const_mul _

lemma incrementFluctuation_mean {t r : ℝ} (ht : 0 ≤ t) (hr : 0 < r) (s w : Time)
    (hscale : t*(1-(s:ℝ))*(w:ℝ) ≤ r^2) :
    ∫β,(incrementFluctuation t r s w β)^3 ∂law  ≤  3072*normCubeMean := by
  let a := Real.sqrt (2*t)/r*Real.sqrt ((1-(s:ℝ))*(w:ℝ))
  have hd : 0 ≤ (1-(s:ℝ))*(w:ℝ) := mul_nonneg (sub_nonneg.mpr s.property.2) w.property.1
  have ha0 : 0 ≤ a := by dsimp [a]; positivity
  have ha2 : a^2 ≤ 2 := by
    dsimp [a]
    rw [mul_pow,div_pow,Real.sq_sqrt (by positivity),Real.sq_sqrt hd,div_mul_eq_mul_div]
    apply (div_le_iff₀ (sq_pos_of_pos hr)).mpr
    convert mul_le_mul_of_nonneg_left hscale (by norm_num : (0:ℝ) ≤ 2) using 1
    all_goals try with_reducible_and_instances rfl
    ring
  have ha : a ≤ 2 := by nlinarith
  have hb := mul_le_mul_of_nonneg_left (incrementSize_cube_mean s w)
    (show 0 ≤ (Real.sqrt (2*t)/r)^3 by positivity)
  simp only [incrementFluctuation,mul_pow,integral_const_mul]
  calc
    _  ≤  _ := hb
    _ = 384*a^3*normCubeMean := by dsimp [a]; ring
    _  ≤  3072*normCubeMean := by
      have hc := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ ha0 ha 3) normCubeMean_nonneg
      nlinarith

lemma incrementFluctuation_eval {t r : ℝ} (hr : 0 < r) (s w q : Time) (hq : (q:ℝ) ≤ (w:ℝ)) (β : Noise) (j : Fin 3) :
    |Real.sqrt (2*t)*(β j (suffixTime s q)-β j s)| ≤ r*incrementFluctuation t r s w β := by
  have hp : ‖β j (suffixTime s q)-β j s‖ ≤ incrementSize s w β := (prefix_norm_eval w q hq (suffixMap s (β j))).trans
    (Finset.single_le_sum (fun i _ ↦ norm_nonneg (incrementMap s w (β i))) (Finset.mem_univ j))
  rw [abs_mul,abs_of_nonneg (Real.sqrt_nonneg _)]
  have he : r*incrementFluctuation t r s w β=Real.sqrt (2*t)*incrementSize s w β := by unfold incrementFluctuation; field_simp
  rw [he]
  exact mul_le_mul_of_nonneg_left hp (Real.sqrt_nonneg _)

end HardSphere.Bridge

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Bridges_AffineVolume
attribute [-instance] _root_.OAI.HardSphere.Bridge.exposedBridgeKernel_markov _root_.OAI.HardSphere.Bridge.exposedPeriodSingle_finite _root_.OAI.HardSphere.Bridge.exposedTrialKernel_markov _root_.OAI.HardSphere.Bridge.instIsProbabilityMeasurePointMidpointNoise _root_.OAI.HardSphere.Bridge.parameterBridgeKernel_markov _root_.OAI.HardSphere.Bridge.parameterIndividualReference_finite _root_.OAI.HardSphere.Bridge.parameterTrialKernel_markov _root_.OAI.HardSphere.Bridge.targetUniform_finite _root_.OAI.HardSphere.Comparison.parameterTargetKernel_finite _root_.OAI.HardSphere.Groups.cellPathReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory MeasureTheory.Measure Set Filter ProbabilityTheory
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.GaussianPacking

lemma affine_measurable (s : ℝ) (c : Point) : Measurable (affine s c) := by unfold affine; fun_prop
lemma affine_volume {s : ℝ} (hs : 0 < s) (c : Point) :
    (volume : Measure Point).map (affine s c)=ENNReal.ofReal (s⁻¹^3) • volume := by
  let F : Point →ₗ[ℝ] Point := s • LinearMap.id
  have hF : LinearMap.det F=s^3 := by simp [F,LinearMap.det_smul]
  have hFn : LinearMap.det F≠0 := by rw [hF]; positivity
  have he : affine s c=(fun x : Point ↦ x+c) ∘ F := rfl
  rw [he,←Measure.map_map (by fun_prop) F.continuous_of_finiteDimensional.measurable,
    Real.map_linearMap_volume_pi_eq_smul_volume_pi hFn,Measure.map_smul,
    (measurePreserving_add_right (volume : Measure Point) c).map_eq,hF]
  congr 2
  rw [abs_of_pos (by positivity),inv_pow]

lemma affine_restrict_le (B : Set Point) {s : ℝ} (hs : 0 < s) (c : Point) :
    ((volume : Measure Point).restrict B).map (affine s c) ≤ ENNReal.ofReal (s⁻¹^3) • volume := by
  rw [←affine_volume hs c]
  exact Measure.map_mono Measure.restrict_le_self (affine_measurable s c)

lemma affine_kernel_le {Ω : Type*} [MeasurableSpace Ω] (ν : Measure Ω) [SFinite ν]
    {c : Ω → Point} (hc : Measurable c) (B : Set Point) {s : ℝ} (hs : 0 < s) :
    (ν.prod ((volume : Measure Point).restrict B)).map (fun p ↦ (p.1,affine s (c p.1) p.2)) ≤
      ν.prod (ENNReal.ofReal (s⁻¹^3) • (volume : Measure Point)) := by
  have hm : Measurable (fun p : Ω×Point ↦ (p.1,affine s (c p.1) p.2)) := by
    apply measurable_fst.prodMk
    unfold affine
    exact Measurable.of_eval fun coordinate ↦
      ((measurable_pi_apply coordinate).comp measurable_snd |>.const_mul s).add
        ((measurable_pi_apply coordinate).comp (hc.comp measurable_fst))
  apply Measure.le_iff.mpr
  intro E hE
  rw [Measure.map_apply hm hE,Measure.prod_apply (hE.preimage hm),Measure.prod_apply hE]
  apply lintegral_mono
  intro ω
  have hsec : MeasurableSet {x : Point | (ω,x)∈E} := hE.preimage measurable_prodMk_left
  change ((volume : Measure Point).restrict B) ((affine s (c ω))⁻¹' {x | (ω,x)∈E}) ≤ _
  rw [←Measure.map_apply (affine_measurable s (c ω)) hsec]
  exact affine_restrict_le B hs (c ω) _

end HardSphere.GaussianPacking

namespace HardSphere.Bridge
open Wiener GaussianPacking

lemma leg_segment_increment (t : ℝ) (y v : Point) (β : Noise) (s q : Time) (j : Fin 3) :
    leg t y v β (suffixTime s q) j=leg t y v β s j+
      ((1-(s:ℝ))*(q:ℝ))*(v j-y j)+Real.sqrt (2*t)*(β j (suffixTime s q)-β j s) := by
  simp only [leg,ContinuousMap.coe_mk,mean]
  dsimp [suffixTime]
  ring

lemma uniform_segment_necessary {t r C A : ℝ} (hr : 0 < r) (hC : 0 ≤ C) (y : Point) (s w : Time)
    (c : Time → Point) (B : Set Point) (hB : ∀v∈B,‖v-y‖ ≤ C)
    (hA : ∀q : Time,(q:ℝ) ≤ (w:ℝ) → ‖c q-c 0‖ ≤ r*A)
    (hdrift : ((1-(s:ℝ))*(w:ℝ))*C ≤ r) : uniformSegmentHit t y s w c r B ⊆
      {p | leg t y p.2 p.1 s ∈ cube (c 0) (r*(2+A+incrementFluctuation t r s w p.1))} := by
  rintro p ⟨hp,q,hq,hh⟩
  have hc := hB p.2 hp
  have hs0 := sub_nonneg.mpr s.property.2
  have hb (j : Fin 3) : |leg t y p.2 p.1 s j-c 0 j| ≤ r*(2+A+incrementFluctuation t r s w p.1) := by
    have hi : |leg t y p.2 p.1 (suffixTime s q) j-c q j| ≤ r := (norm_le_pi_norm _ j).trans hh
    have ho : |c q j-c 0 j| ≤ r*A := (norm_le_pi_norm _ j).trans (hA q hq)
    have hd : |((1-(s:ℝ))*(q:ℝ))*(p.2 j-y j)| ≤ r := by
      rw [abs_mul,abs_of_nonneg (mul_nonneg hs0 q.property.1)]
      exact (mul_le_mul_of_nonneg_left ((norm_le_pi_norm _ j).trans hc) (mul_nonneg hs0 q.property.1)).trans
        ((mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hq hs0) hC).trans hdrift)
    have hn := incrementFluctuation_eval (t:=t) hr s w q hq p.1 j
    have he : leg t y p.2 p.1 s j-c 0 j=
        ((leg t y p.2 p.1 (suffixTime s q) j-c q j)+(c q j-c 0 j))-
        ((1-(s:ℝ))*(q:ℝ))*(p.2 j-y j)-Real.sqrt (2*t)*(p.1 j (suffixTime s q)-p.1 j s) := by
      rw [leg_segment_increment]; ring
    rw [he]
    calc
      _ ≤ (|leg t y p.2 p.1 (suffixTime s q) j-c q j|+|c q j-c 0 j|)+
          |((1-(s:ℝ))*(q:ℝ))*(p.2 j-y j)|+|Real.sqrt (2*t)*(p.1 j (suffixTime s q)-p.1 j s)| :=
        (abs_sub _ _).trans (add_le_add ((abs_sub _ _).trans (add_le_add (abs_add_le _ _) le_rfl)) le_rfl)
      _ ≤ (r+r*A)+r+r*incrementFluctuation t r s w p.1 := by gcongr
      _ = _ := by ring
  exact ⟨fun j ↦ by have h := (abs_le.mp (hb j)).1; dsimp; linarith,
    fun j ↦ by have h := (abs_le.mp (hb j)).2; dsimp; linarith⟩

lemma uniform_position_le (t : ℝ) (y : Point) (s : Time) (hs : 0<(s:ℝ)) (B : Set Point) :
    (law.prod ((volume : Measure Point).restrict B)).map (fun p ↦ (p.1,leg t y p.2 p.1 s)) ≤
      law.prod (ENNReal.ofReal ((s:ℝ)⁻¹^3) • (volume : Measure Point)) := by
  let cβ : Noise → Point := fun β j ↦ (1-(s:ℝ))*y j+Real.sqrt (2*t)*β j s
  have hc : Measurable cβ := by
    apply Continuous.measurable
    dsimp [cβ]
    fun_prop
  have he (p : Noise×Point) : affine (s:ℝ) (cβ p.1) p.2=leg t y p.2 p.1 s := by
    ext j
    simp only [affine,cβ,leg,ContinuousMap.coe_mk,mean]
    ring
  simpa only [he] using affine_kernel_le law hc B hs

lemma uniform_segment_bound (y : Point) (s w : Time) (c : Time → Point) (B : Set Point)
    {t r C A : ℝ} (ht : 0<t) (hr : 0 < r) (hC : 0 ≤ C) (hA0 : 0 ≤ A)
    (hs : 0<(s:ℝ)) (hB : ∀v∈B,‖v-y‖ ≤ C)
    (hA : ∀q : Time,(q:ℝ) ≤ (w:ℝ) → ‖c q-c 0‖ ≤ r*A)
    (hdrift : ((1-(s:ℝ))*(w:ℝ))*C ≤ r) (hscale : t*(1-(s:ℝ))*(w:ℝ) ≤ r^2) :
    (law.prod ((volume : Measure Point).restrict B)) (uniformSegmentHit t y s w c r B) ≤
      ENNReal.ofReal (32*(s:ℝ)⁻¹^3*r^3*((2+A)^3+3072*normCubeMean)) := by
  let E := {p : Noise×Point | p.2∈cube (c 0) (r*((2+A)+incrementFluctuation t r s w p.1))}
  have hE : MeasurableSet E := measurable_cube_event (incrementFluctuation_continuous t r s w).measurable (c 0) r (2+A)
  have hm : Measurable (fun p : Noise×Point ↦ (p.1,leg t y p.2 p.1 s)) := by
    apply measurable_fst.prodMk
    change Measurable (fun p : Noise×Point ↦ fun j ↦ (1-(s:ℝ))*y j+(s:ℝ)*p.2 j+Real.sqrt (2*t)*p.1 j s)
    fun_prop
  have hu := measure_mono (μ:=law.prod ((volume : Measure Point).restrict B)) (uniform_segment_necessary (t:=t) hr hC y s w c B hB hA hdrift)
  have he : {p : Noise×Point | leg t y p.2 p.1 s∈cube (c 0) (r*(2+A+incrementFluctuation t r s w p.1))}=
      (fun p : Noise×Point ↦ (p.1,leg t y p.2 p.1 s))⁻¹' E := rfl
  rw [he,←Measure.map_apply hm hE] at hu
  apply (hu.trans (uniform_position_le t y s hs B E)).trans
  have hμ : ENNReal.ofReal ((s:ℝ)⁻¹^3) • (volume : Measure Point) ≤ ENNReal.ofReal ((s:ℝ)⁻¹^3) • volume := le_rfl
  have hb := collision_cubic_bound law (ENNReal.ofReal ((s:ℝ)⁻¹^3) • (volume : Measure Point))
    (incrementFluctuation_continuous t r s w).measurable (incrementFluctuation_nonneg hr.le s w)
    (incrementFluctuation_memLp t r s w) (c 0) hr.le (by positivity : 0 ≤ 2+A) (by positivity : 0 ≤ (s:ℝ)⁻¹^3) hμ
  apply hb.trans
  apply ENNReal.ofReal_le_ofReal
  apply mul_le_mul_of_nonneg_left (add_le_add le_rfl (incrementFluctuation_mean ht.le hr s w hscale))
  positivity

end HardSphere.Bridge

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Bridges_SegmentMeasurable
attribute [-instance] _root_.OAI.HardSphere.Bridge.exposedBridgeKernel_markov _root_.OAI.HardSphere.Bridge.exposedPeriodSingle_finite _root_.OAI.HardSphere.Bridge.exposedTrialKernel_markov _root_.OAI.HardSphere.Bridge.instIsProbabilityMeasurePointMidpointNoise _root_.OAI.HardSphere.Bridge.parameterBridgeKernel_markov _root_.OAI.HardSphere.Bridge.parameterIndividualReference_finite _root_.OAI.HardSphere.Bridge.parameterTrialKernel_markov _root_.OAI.HardSphere.Bridge.targetUniform_finite _root_.OAI.HardSphere.Comparison.parameterTargetKernel_finite _root_.OAI.HardSphere.Groups.cellPathReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Set Filter ProbabilityTheory
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.Bridge
open Wiener GaussianPacking

lemma jointSegmentHit_closed (t : ℝ) (y : Point) (s w : Time) (c : C(Time,Point)) (r C : ℝ) :
    IsClosed (jointSegmentHit t y s w c r C) := by
  let E : Set ((Point×Noise)×Time) := {p | (p.2:ℝ)≤(w:ℝ) ∧
    ‖leg t y p.1.1 p.1.2 (suffixTime s p.2)-c p.2‖ ≤ r}
  have hE : IsClosed E := by
    apply IsClosed.inter
    · exact isClosed_le (continuous_subtype_val.comp continuous_snd) continuous_const
    · have hn : Continuous (fun p : (Point×Noise)×Time ↦ ‖leg t y p.1.1 p.1.2 (suffixTime s p.2)-c p.2‖) := by
        change Continuous (fun p : (Point×Noise)×Time ↦ ‖(fun j ↦
          (1-(suffixTime s p.2:ℝ))*y j+(suffixTime s p.2:ℝ)*p.1.1 j+
          Real.sqrt (2*t)*p.1.2 j (suffixTime s p.2))-c p.2‖)
        apply Continuous.norm
        apply Continuous.sub
        · apply continuous_pi
          intro j
          fun_prop
        · exact c.continuous.comp continuous_snd
      exact isClosed_le hn continuous_const
  have hp := isClosedMap_fst_of_compactSpace E hE
  have hc : IsClosed {p : Point×Noise | ‖leg t y p.1 p.2 s-p.1‖≤C} := by
    apply isClosed_le _ continuous_const
    change Continuous (fun p : Point×Noise ↦ ‖(fun j ↦ (1-(s:ℝ))*y j+(s:ℝ)*p.1 j+
      Real.sqrt (2*t)*p.2 j s)-p.1‖)
    fun_prop
  convert hc.inter hp using 1
  all_goals try with_reducible_and_instances rfl
  ext p
  simp only [jointSegmentHit,segmentHit,mem_ofPred_eq,Set.mem_inter_iff,mem_image,E]
  constructor
  · rintro ⟨h,q,hq,hh⟩
    exact ⟨h,⟨(p,q),⟨hq,hh⟩,rfl⟩⟩
  · rintro ⟨h,⟨⟨p',q⟩,⟨hq,hh⟩,hp⟩⟩
    dsimp at hp
    subst p'
    exact ⟨h,q,hq,hh⟩

lemma uniformSegmentHit_measurable (t : ℝ) (y : Point) (s w : Time) (c : C(Time,Point)) (r : ℝ)
    {B : Set Point} (hB : MeasurableSet B) : MeasurableSet (uniformSegmentHit t y s w c r B) := by
  let E : Set ((Noise×Point)×Time) := {p | (p.2:ℝ)≤(w:ℝ) ∧
    ‖leg t y p.1.2 p.1.1 (suffixTime s p.2)-c p.2‖ ≤ r}
  have hE : IsClosed E := by
    apply IsClosed.inter
    · exact isClosed_le (continuous_subtype_val.comp continuous_snd) continuous_const
    · have hn : Continuous (fun p : (Noise×Point)×Time ↦ ‖leg t y p.1.2 p.1.1 (suffixTime s p.2)-c p.2‖) := by
        change Continuous (fun p : (Noise×Point)×Time ↦ ‖(fun j ↦
          (1-(suffixTime s p.2:ℝ))*y j+(suffixTime s p.2:ℝ)*p.1.2 j+
          Real.sqrt (2*t)*p.1.1 j (suffixTime s p.2))-c p.2‖)
        apply Continuous.norm
        apply Continuous.sub
        · apply continuous_pi
          intro j
          fun_prop
        · exact c.continuous.comp continuous_snd
      exact isClosed_le hn continuous_const
  have hp := (isClosedMap_fst_of_compactSpace E hE).measurableSet
  convert (hB.preimage measurable_snd).inter hp using 1
  all_goals try with_reducible_and_instances rfl
  ext p
  simp only [uniformSegmentHit,mem_ofPred_eq,Set.mem_inter_iff,mem_image,E,mem_preimage]
  constructor
  · rintro ⟨h,q,hq,hh⟩
    exact ⟨h,⟨(p,q),⟨hq,hh⟩,rfl⟩⟩
  · rintro ⟨h,⟨⟨p',q⟩,⟨hq,hh⟩,hp⟩⟩
    dsimp at hp
    subst p'
    exact ⟨h,q,hq,hh⟩

end HardSphere.Bridge

end

noncomputable section
open Set
open scoped BigOperators
namespace HardSphere.Bridge

lemma inverse_sqrt_step {x h : ℝ} (hx : 0<x) (hh : 0<h) :
    h / ((x+h)*Real.sqrt (x+h)) ≤ 2*(1/Real.sqrt x-1/Real.sqrt (x+h)) := by
  have hX := Real.sqrt_pos.2 hx
  have hY := Real.sqrt_pos.2 (add_pos hx hh)
  have hXY := Real.sqrt_le_sqrt (le_add_of_nonneg_right hh.le : x≤x+h)
  have hxx := Real.sq_sqrt hx.le
  have hyy := Real.sq_sqrt (add_pos hx hh).le
  apply (div_le_iff₀ (mul_pos (add_pos hx hh) hY)).mpr
  field_simp
  have he : 2*(x+h)*(Real.sqrt (x+h)-Real.sqrt x)-h*Real.sqrt x=
      (Real.sqrt (x+h)-Real.sqrt x)^2*(2*Real.sqrt (x+h)+Real.sqrt x) := by
    calc
      _ = 2*(Real.sqrt (x+h))^2*(Real.sqrt (x+h)-Real.sqrt x)-
        ((Real.sqrt (x+h))^2-(Real.sqrt x)^2)*Real.sqrt x := by rw [hxx,hyy]; ring
      _ = _ := by ring
  have hp : 0 ≤ (Real.sqrt (x+h)-Real.sqrt x)^2*(2*Real.sqrt (x+h)+Real.sqrt x) := by positivity
  linarith

lemma singular_sum (n : ℕ) {x h : ℝ} (hx : 0<x) (hh : 0<h) :
    (∑k∈Finset.range n, h/((x+(k+1)*h)*Real.sqrt (x+(k+1)*h))) ≤
      2*(1/Real.sqrt x-1/Real.sqrt (x+n*h)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    have hp : 0<x+n*h := add_pos_of_pos_of_nonneg hx (by positivity)
    have hstep := inverse_sqrt_step hp hh
    have he : x+(n:ℝ)*h+h=x+((n:ℝ)+1)*h := by ring
    rw [he] at hstep
    push_cast
    exact (add_le_add ih hstep).trans_eq (by ring)

lemma singular_sum_bound (n : ℕ) {x h : ℝ} (hx : 0<x) (hh : 0<h) :
    (∑k∈Finset.range n, 1/((x+(k+1)*h)*Real.sqrt (x+(k+1)*h))) ≤
      2/(h*Real.sqrt x) := by
  have hs := singular_sum n hx hh
  have he : (∑k∈Finset.range n,h/((x+(k+1)*h)*Real.sqrt (x+(k+1)*h)))=
      h*(∑k∈Finset.range n,1/((x+(k+1)*h)*Real.sqrt (x+(k+1)*h))) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    ring
  rw [he] at hs
  have hs' : h*(∑k∈Finset.range n,1/((x+(k+1)*h)*Real.sqrt (x+(k+1)*h))) ≤ 2/Real.sqrt x := by
    apply hs.trans
    have hp : 0≤1/Real.sqrt (x+(n:ℝ)*h) := by positivity
    calc
      _ ≤ 2*(1/Real.sqrt x) := by linarith
      _ = _ := by ring
  rw [show 2/(h*Real.sqrt x)=(2/Real.sqrt x)/h by ring]
  apply (le_div_iff₀ hh).mpr
  simpa only [mul_comm] using hs'

end HardSphere.Bridge

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Bridges_SegmentSimplify
attribute [-instance] _root_.OAI.HardSphere.Bridge.exposedBridgeKernel_markov _root_.OAI.HardSphere.Bridge.exposedPeriodSingle_finite _root_.OAI.HardSphere.Bridge.exposedTrialKernel_markov _root_.OAI.HardSphere.Bridge.instIsProbabilityMeasurePointMidpointNoise _root_.OAI.HardSphere.Bridge.parameterBridgeKernel_markov _root_.OAI.HardSphere.Bridge.parameterIndividualReference_finite _root_.OAI.HardSphere.Bridge.parameterTrialKernel_markov _root_.OAI.HardSphere.Bridge.targetUniform_finite _root_.OAI.HardSphere.Comparison.parameterTargetKernel_finite _root_.OAI.HardSphere.Groups.cellPathReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Set Filter ProbabilityTheory
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.Bridge
open Wiener GaussianPacking

lemma hitConstant_pos : 0<hitConstant := by
  have hn : 0≤normCubeMean := integral_nonneg (fun _ ↦ by positivity)
  have hk := packingConstant_pos
  unfold hitConstant
  positivity

lemma cubic_noise_le {A : ℝ} (hA : 0≤A) :
    (2+A)^3+3072*normCubeMean ≤ (8+3072*normCubeMean)*(1+A)^3 := by
  have hn : 0≤normCubeMean := integral_nonneg (fun _ ↦ by positivity)
  have ha : (2+A)^3 ≤ (2*(1+A))^3 := pow_le_pow_left₀ (by linarith) (by linarith) 3
  have hb : 1≤(1+A)^3 := one_le_pow₀ (by linarith)
  have hc := mul_le_mul_of_nonneg_left hb (mul_nonneg (by norm_num : (0:ℝ)≤3072) hn)
  nlinarith

lemma inverse_density_le {t : ℝ} (ht : 0<t) {s : Time} (hs : 0<(s:ℝ)) (hs1 : (s:ℝ)≤1/2) :
    (Real.sqrt ((2*(legVariance t s:ℝ))⁻¹))^3 ≤ 1/((t*(s:ℝ))*Real.sqrt (t*(s:ℝ))) := by
  have hx : 0<t*(s:ℝ) := mul_pos ht hs
  have hv : t*(s:ℝ) ≤ 2*(legVariance t s:ℝ) := by
    rw [legVariance_val ht.le]
    have := mul_le_mul_of_nonneg_left hs1 (mul_nonneg ht.le hs.le)
    nlinarith
  have hvpos : 0<2*(legVariance t s:ℝ) := hx.trans_le hv
  have hle := Real.sqrt_le_sqrt (inv_anti₀ hx hv)
  apply (pow_le_pow_left₀ (Real.sqrt_nonneg _) hle 3).trans_eq
  rw [Real.sqrt_inv]
  have he := Real.sq_sqrt hx.le
  field_simp
  nlinarith [Real.sqrt_pos.mpr hx]

lemma packed_scale_le {ε : ℝ} (hε : 0<ε) {s : Time} (hs : (s:ℝ)≤1/2) :
    ((1-(s:ℝ))*ε)⁻¹^3 ≤ 8*ε⁻¹^3 := by
  have h : ε/2 ≤ (1-(s:ℝ))*ε := by nlinarith
  have hp : 0<ε/2 := by positivity
  have hi := inv_anti₀ hp h
  have hspos : 0<(1-(s:ℝ))*ε := hp.trans_le h
  have hc := pow_le_pow_left₀ (inv_nonneg.mpr hspos.le) hi 3
  have he : (ε/2)⁻¹^3=8*ε⁻¹^3 := by
    simp only [inv_div,div_pow]
    norm_num
    ring
  exact hc.trans_eq he

lemma segment_sum_simplified {m : ℕ} (y : Fin m → Point) (v : Point) (s w : Time)
    (c : Time → Point) {t r C A ε : ℝ} (ht : 0<t) (hr : 0 < r) (hC : 0≤C) (hA0 : 0≤A)
    (hs : 0<(s:ℝ)) (hs1 : (s:ℝ)≤1/2) (hε : 0<ε)
    (hsep : ∀i j,i≠j → ε^2 ≤ square (y i-y j))
    (hA : ∀q : Time,(q:ℝ)≤(w:ℝ) → ‖c q-c 0‖ ≤ r*A)
    (hdrift : (w:ℝ)*C ≤ r) (hscale : t*(1-(s:ℝ))*(w:ℝ) ≤ r^2) :
    (∑i,law (segmentHit t (y i) v s w c r C)) ≤
      ENNReal.ofReal (hitConstant*r^3*(1+A)^3*(ε⁻¹^3+1/((t*(s:ℝ))*Real.sqrt (t*(s:ℝ))))) := by
  have hslt : (s:ℝ)<1 := by linarith
  apply (segment_sum_bound y v s w c ht hr hC hA0 hs hslt hε hsep hA hdrift hscale).trans
  apply ENNReal.ofReal_le_ofReal
  have hden := add_le_add (packed_scale_le hε hs1) (inverse_density_le ht hs hs1)
  have hd0 : 0≤1/((t*(s:ℝ))*Real.sqrt (t*(s:ℝ))) := by positivity
  have he0 : 0≤ε⁻¹^3 := by positivity
  have hn := cubic_noise_le hA0
  have hn0 : 0≤(2+A)^3+3072*normCubeMean := by
    have : 0≤normCubeMean := integral_nonneg (fun _ ↦ by positivity)
    positivity
  have hnon : 0≤8+3072*normCubeMean := by
    have : 0≤normCubeMean := integral_nonneg (fun _ ↦ by positivity)
    positivity
  have hk := packingConstant_pos.le
  calc
    _ ≤ 32*(packingConstant*(8*ε⁻¹^3+1/((t*(s:ℝ))*Real.sqrt (t*(s:ℝ)))))*r^3*
        ((8+3072*normCubeMean)*(1+A)^3) := by
      apply mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hden packingConstant_pos.le) (by norm_num))
        (pow_nonneg hr.le _)) hn0 |>.trans
      exact mul_le_mul_of_nonneg_left hn (by positivity)
    _ ≤ _ := by
      unfold hitConstant
      have ha0 : 0≤(1+A)^3 := by positivity
      have hh : 32*(packingConstant*(8*ε⁻¹^3+1/((t*(s:ℝ))*Real.sqrt (t*(s:ℝ))))) ≤
          256*(packingConstant+1)*(ε⁻¹^3+1/((t*(s:ℝ))*Real.sqrt (t*(s:ℝ)))) := by
        nlinarith [mul_nonneg hk hd0]
      have hmul := mul_le_mul_of_nonneg_right hh (mul_nonneg (pow_nonneg hr.le 3) (mul_nonneg hnon ha0))
      simpa only [mul_assoc,mul_comm,mul_left_comm] using hmul

lemma joint_segment_sum_bound {m : ℕ} (y : Fin m → Point) (s w : Time)
    (c : C(Time,Point)) {t r C A ε : ℝ} (ht : 0<t) (hr : 0 < r) (hC : 0≤C) (hA0 : 0≤A)
    (hs : 0<(s:ℝ)) (hs1 : (s:ℝ)≤1/2) (hε : 0<ε)
    (hsep : ∀i j,i≠j → ε^2 ≤ square (y i-y j))
    (hA : ∀q : Time,(q:ℝ)≤(w:ℝ) → ‖c q-c 0‖ ≤ r*A)
    (hdrift : (w:ℝ)*C ≤ r) (hscale : t*(1-(s:ℝ))*(w:ℝ) ≤ r^2)
    {B : Set Point} (hB : (volume : Measure Point) B≤1) :
    (∑i,((volume.restrict B).prod law) (jointSegmentHit t (y i) s w c r C)) ≤
      ENNReal.ofReal (hitConstant*r^3*(1+A)^3*(ε⁻¹^3+1/((t*(s:ℝ))*Real.sqrt (t*(s:ℝ))))) := by
  have hE i := (jointSegmentHit_closed t (y i) s w c r C).measurableSet
  simp_rw [Measure.prod_apply (hE _)]
  rw [←lintegral_finsetSum Finset.univ (fun i _ ↦ measurable_measure_prodMk_left (hE i))]
  have hp := lintegral_mono (μ:=volume.restrict B) fun v ↦
    segment_sum_simplified y v s w c ht hr hC hA0 hs hs1 hε hsep hA hdrift hscale
  apply hp.trans
  rw [lintegral_const,Measure.restrict_apply_univ]
  calc
    _ ≤ _*1 := mul_le_mul' le_rfl hB
    _ = _ := mul_one _

lemma uniform_segment_simplified (y : Point) (s w : Time) (c : Time → Point) (B : Set Point)
    {t r C A : ℝ} (ht : 0<t) (hr : 0 < r) (hC : 0≤C) (hA0 : 0≤A)
    (hs : (1:ℝ)/2≤(s:ℝ)) (hB : ∀v∈B,‖v-y‖≤C)
    (hA : ∀q : Time,(q:ℝ)≤(w:ℝ) → ‖c q-c 0‖ ≤ r*A)
    (hdrift : ((1-(s:ℝ))*(w:ℝ))*C ≤ r) (hscale : t*(1-(s:ℝ))*(w:ℝ) ≤ r^2) :
    (law.prod ((volume : Measure Point).restrict B)) (uniformSegmentHit t y s w c r B) ≤
      ENNReal.ofReal (hitConstant*r^3*(1+A)^3) := by
  have hs0 : 0<(s:ℝ) := by linarith
  apply (uniform_segment_bound y s w c B ht hr hC hA0 hs0 hB hA hdrift hscale).trans
  apply ENNReal.ofReal_le_ofReal
  have hi : (s:ℝ)⁻¹^3≤8 := by
    have hh := pow_le_pow_left₀ (inv_nonneg.mpr hs0.le) (inv_anti₀ (by norm_num : (0:ℝ)<1/2) hs) 3
    norm_num at hh
    simpa only [inv_pow] using hh
  have hc := cubic_noise_le hA0
  have hN := normCubeMean_nonneg
  have hK := packingConstant_pos.le
  calc
    _ ≤ 32*8*r^3*((8+3072*normCubeMean)*(1+A)^3) := by gcongr
    _ ≤ _ := by
      unfold hitConstant
      have hp := mul_le_mul_of_nonneg_right (show (1:ℝ)≤packingConstant+1 by linarith)
        (show 0≤256*(8+3072*normCubeMean)*r^3*(1+A)^3 by positivity)
      norm_num only [show (32:ℝ)*8=256 by norm_num]
      simpa only [one_mul,mul_assoc,mul_comm,mul_left_comm] using hp

end HardSphere.Bridge

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
open scoped NNReal ComplexConjugate

lemma euclideanTorusPoint_dist (L : Length) (x y : Torus L) :
    dist (euclideanTorusPoint L x) (euclideanTorusPoint L y)=torusDistance L x y :=
  PiLp.dist_eq_of_L2 _ _

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
-- module Solutions.OAIQ054_HS.HardSphere_Cutoffs_PathDiameter
attribute [-instance] _root_.OAI.HardSphere.Bridge.exposedBridgeKernel_markov _root_.OAI.HardSphere.Bridge.exposedPeriodSingle_finite _root_.OAI.HardSphere.Bridge.exposedTrialKernel_markov _root_.OAI.HardSphere.Bridge.instBorelSpaceContinuousMapElemRealTimePoint _root_.OAI.HardSphere.Bridge.instIsProbabilityMeasureNoiseLaw _root_.OAI.HardSphere.Bridge.instMeasurableSpaceContinuousMapElemRealTimePoint _root_.OAI.HardSphere.Bridge.parameterBridgeKernel_markov _root_.OAI.HardSphere.Bridge.parameterIndividualReference_finite _root_.OAI.HardSphere.Bridge.parameterTrialKernel_markov _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Bridge.trialKernel_markov _root_.OAI.HardSphere.Groups.cellPathReference_probability _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Rescaling.config_haar _root_.OAI.HardSphere.Wiener.bridgeLaw_isGaussian _root_.OAI.HardSphere.Wiener.wiener_isGaussian _root_.OAI.HardSphere.bridgeEndpointBase_finite _root_.OAI.HardSphere.coordinateBridge_probability _root_.OAI.HardSphere.endpointWeightedBase_sfinite _root_.OAI.HardSphere.freePathLaw_finite_deletion _root_.OAI.HardSphere.killedPathLaw_finite_deletion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Set Filter ProbabilityTheory
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.PathCutoff
open Wiener
attribute [local irreducible] torusDistance freeTrajectory

lemma intervalDiameter_nonneg {L : Length} (a b : Time) (ω : ConfigurationPath 1 L) :
    0 ≤ intervalDiameter a b ω := norm_nonneg _

lemma intervalDistance_le {L : Length} (a b s q : Time) (ω : ConfigurationPath 1 L) :
    torusDistance L (ω (intervalTime a b s) 0) (ω (intervalTime a b q) 0) ≤ intervalDiameter a b ω := by
  exact (le_abs_self _).trans (ContinuousMap.norm_coe_le_norm (diameterMap a b ω) (s,q))

lemma intervalDiameter_le {L : Length} (a b : Time) (ω : ConfigurationPath 1 L) {R : ℝ} (hR : 0 ≤ R)
    (h : ∀ s q, torusDistance L (ω (intervalTime a b s) 0) (ω (intervalTime a b q) 0) ≤ R) :
    intervalDiameter a b ω ≤ R := by
  apply (ContinuousMap.norm_le _ hR).mpr
  intro p
  change |torusDistance L _ _| ≤ R
  rw [abs_of_nonneg (by unfold torusDistance; positivity)]
  exact h p.1 p.2

lemma intervalTime_reverse (a b s : Time) :
    reverseTime (intervalTime a b s)=intervalTime (reverseTime b) (reverseTime a) (reverseTime s) := by
  apply Subtype.ext
  change 1-((1-(s:ℝ))*(a:ℝ)+(s:ℝ)*(b:ℝ)) = (1-(1-(s:ℝ)))*(1-(b:ℝ))+(1-(s:ℝ))*(1-(a:ℝ))
  ring

lemma intervalDiameter_reverse {L : Length} (a b : Time) (ω : ConfigurationPath 1 L) :
    intervalDiameter a b (reverseConfigurationPath 1 L ω)=
      intervalDiameter (reverseTime b) (reverseTime a) ω := by
  apply le_antisymm
  · apply intervalDiameter_le _ _ _ (intervalDiameter_nonneg _ _ _)
    intro s q
    change torusDistance L (ω (reverseTime (intervalTime a b s)) 0)
      (ω (reverseTime (intervalTime a b q)) 0) ≤ _
    simp only [intervalTime_reverse]
    exact intervalDistance_le _ _ _ _ _
  · have hh : reverseTime (reverseTime a)=a := reverseTime_reverse _
    have hh' : reverseTime (reverseTime b)=b := reverseTime_reverse _
    apply intervalDiameter_le _ _ _ (intervalDiameter_nonneg _ _ _)
    intro s q
    have h := intervalDistance_le a b (reverseTime s) (reverseTime q) (reverseConfigurationPath 1 L ω)
    change torusDistance L (ω (reverseTime (intervalTime a b (reverseTime s))) 0)
      (ω (reverseTime (intervalTime a b (reverseTime q))) 0) ≤ _ at h
    simpa only [intervalTime_reverse,reverseTime_reverse] using h

end HardSphere.PathCutoff

namespace HardSphere.PathCutoff
open Wiener
attribute [local irreducible] torusDistance freeTrajectory

lemma meshTime_reverse {m : ℕ} (j : Fin m) (s : Time) :
    reverseTime (meshTime j s)=meshTime j.rev (reverseTime s) := by
  apply Subtype.ext
  have hm : (m:ℝ)≠0 := by exact_mod_cast (Nat.ne_of_gt j.pos)
  change 1-((j:ℝ)+(s:ℝ))/(m:ℝ)=((j.rev:ℝ)+(1-(s:ℝ)))/(m:ℝ)
  have hj : (j.rev:ℝ)=(m:ℝ)-1-(j:ℝ) := by
    rw [Fin.val_rev,Nat.cast_sub (by omega)]
    push_cast
    ring
  rw [hj]
  field_simp
  ring

lemma meshSegment_reverse {m : ℕ} {L : Length} (j : Fin m) (ω : ConfigurationPath 1 L) :
    meshSegment j (reverseConfigurationPath 1 L ω)=reverseConfigurationPath 1 L (meshSegment j.rev ω) := by
  ext s i k
  exact congrArg (fun u : Time ↦ ω u i k) (meshTime_reverse j s)

lemma mesh_sum_reverse {m : ℕ} {L : Length} (F : ConfigurationPath 1 L→ℝ)
    (hF : ∀ω,F (reverseConfigurationPath 1 L ω)=F ω) (ω : ConfigurationPath 1 L) :
    ∑ j : Fin m,F (meshSegment j (reverseConfigurationPath 1 L ω))=
    ∑ j : Fin m,F (meshSegment j ω) := by
  simp only [meshSegment_reverse,hF]
  exact Equiv.sum_comp (Fin.revPerm) (fun j : Fin m ↦ F (meshSegment j ω))

end HardSphere.PathCutoff

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Bridges_MeshLegHit
attribute [-instance] _root_.OAI.HardSphere.Bridge.exposedBridgeKernel_markov _root_.OAI.HardSphere.Bridge.exposedPeriodSingle_finite _root_.OAI.HardSphere.Bridge.exposedTrialKernel_markov _root_.OAI.HardSphere.Bridge.instIsProbabilityMeasurePointMidpointNoise _root_.OAI.HardSphere.Bridge.parameterBridgeKernel_markov _root_.OAI.HardSphere.Bridge.parameterIndividualReference_finite _root_.OAI.HardSphere.Bridge.parameterTrialKernel_markov _root_.OAI.HardSphere.Bridge.targetUniform_finite _root_.OAI.HardSphere.Comparison.parameterTargetKernel_finite _root_.OAI.HardSphere.Groups.cellPathReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Set Filter ProbabilityTheory
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.Bridge
open Wiener GaussianPacking

lemma combined_segment_sum_bound {m : ℕ} (y : Fin m→Point) (s w : Time)
    (c : C(Time,Point)) {t r C A ε : ℝ} (ht : 0<t) (hr : 0 < r) (hC : 0≤C) (hA0 : 0≤A)
    (hs : 0<(s:ℝ)) (hε : 0<ε)
    (hsep : ∀i j,i≠j→ε^2≤ square (y i-y j))
    (hA : ∀q : Time,(q:ℝ)≤(w:ℝ)→‖c q-c 0‖ ≤ r*A)
    (hdrift : (s:ℝ)≤1/2 → (w:ℝ)*C ≤ r)
    (hlatedrift : ((1-(s:ℝ))*(w:ℝ))*C ≤ r) (hscale : t*(1-(s:ℝ))*(w:ℝ) ≤ r^2)
    {B : Set Point} (hBm : MeasurableSet B) (hB : (volume : Measure Point) B≤1)
    (hBdist : ∀i v,v∈B→‖v-y i‖≤C) :
    (∑i,((volume.restrict B).prod law) (combinedSegmentHit t (y i) B s w c r C)) ≤
      ENNReal.ofReal (hitConstant*r^3*(1+A)^3*((ε⁻¹^3+(m:ℝ))+1/(t*(s:ℝ)*Real.sqrt (t*(s:ℝ))))) := by
  by_cases hs1 : (s:ℝ)≤1/2
  · simp only [combinedSegmentHit,ite_eq_left hs1]
    apply (joint_segment_sum_bound y s w c ht hr hC hA0 hs hs1 hε hsep hA (hdrift hs1) hscale hB).trans
    apply ENNReal.ofReal_le_ofReal
    have hm : (0:ℝ) ≤ m := Nat.cast_nonneg m
    have hc : 0≤hitConstant*r^3*(1+A)^3 := by have := hitConstant_pos; positivity
    exact mul_le_mul_of_nonneg_left (by linarith) hc
  · simp only [combinedSegmentHit,ite_eq_right hs1]
    have hb i : ((volume.restrict B).prod law) (Prod.swap ⁻¹' uniformSegmentHit t (y i) s w c r B) ≤
        ENNReal.ofReal (hitConstant*r^3*(1+A)^3) := by
      rw [←Measure.map_apply measurable_swap (uniformSegmentHit_measurable t (y i) s w c r hBm),Measure.prod_swap]
      exact uniform_segment_simplified (y i) s w c B ht hr hC hA0 (le_of_lt (lt_of_not_ge hs1)) (hBdist i) hA hlatedrift hscale
    apply (Finset.sum_le_sum (fun i _↦hb i)).trans
    rw [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    rw [←ENNReal.ofReal_natCast,←ENNReal.ofReal_mul (Nat.cast_nonneg m)]
    apply ENNReal.ofReal_le_ofReal
    have ha : 0≤hitConstant*r^3*(1+A)^3 := by have := hitConstant_pos; positivity
    have hh : (m:ℝ) ≤ (ε⁻¹^3+m)+1/(t*(s:ℝ)*Real.sqrt (t*(s:ℝ))) := by
      have hε0 : 0≤ε⁻¹^3 := by positivity
      have hd : 0≤1/(t*(s:ℝ)*Real.sqrt (t*(s:ℝ))) := by positivity
      linarith
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left hh ha

end HardSphere.Bridge

namespace HardSphere.Bridge
open Wiener PathCutoff GaussianPacking

lemma meshRemainder_pos {n : ℕ} (j : Fin n) : 0<(meshRemainder j:ℝ) := by
  have hj : (j:ℝ)<(n:ℝ) := by exact_mod_cast j.isLt
  exact one_div_pos.mpr (sub_pos.mpr hj)

lemma mesh_suffix_time {n : ℕ} (j : Fin n) (q : Time) :
    suffixTime (meshTime j 0) (prefixTime (meshRemainder j) q)=meshTime j q := by
  apply Subtype.ext
  have hn : (n:ℝ)≠0 := by exact_mod_cast (Nat.ne_of_gt j.pos)
  have hj : (n:ℝ)-(j:ℝ)≠0 := sub_ne_zero.mpr (by exact_mod_cast (Nat.ne_of_gt j.isLt))
  simp only [suffixTime,prefixTime,ContinuousMap.coe_mk,meshTime,meshRemainder,show ((0:Time):ℝ)=0 from rfl,add_zero]
  field_simp

lemma mesh_remaining {n : ℕ} (j : Fin n) :
    (1-(meshTime j 0:ℝ))*(meshRemainder j:ℝ)=1/(n:ℝ) := by
  have hn : (n:ℝ)≠0 := by exact_mod_cast (Nat.ne_of_gt j.pos)
  have hj : (n:ℝ)-(j:ℝ)≠0 := sub_ne_zero.mpr (by exact_mod_cast (Nat.ne_of_gt j.isLt))
  dsimp [meshTime,meshRemainder]
  field_simp
  ring

lemma mesh_covers {n : ℕ} (hn : 0<n) (s : Time) : ∃j : Fin n,∃q : Time,meshTime j q=s := by
  have hn' : (0:ℝ)<n := by exact_mod_cast hn
  by_cases hs : (s:ℝ)=1
  · let j : Fin n := ⟨n-1,by omega⟩
    refine ⟨j,1,Subtype.ext ?_⟩
    simp only [meshTime,j,show ((1:Time):ℝ)=1 from rfl,Nat.cast_sub (show 1≤n by omega),Nat.cast_one]
    rw [sub_add_cancel,div_self hn'.ne',hs]
  · have hs' : (s:ℝ)<1 := lt_of_le_of_ne s.property.2 hs
    let k : ℕ := ⌊(n:ℝ)*(s:ℝ)⌋₊
    have hk0 : (k:ℝ)≤(n:ℝ)*(s:ℝ) := Nat.floor_le (mul_nonneg hn'.le s.property.1)
    have hk1 : (n:ℝ)*(s:ℝ)<(k:ℝ)+1 := Nat.lt_floor_add_one _
    have hk : k<n := by
      have : (k:ℝ)<(n:ℝ) := hk0.trans_lt (by nlinarith)
      exact_mod_cast this
    let q : Time := ⟨(n:ℝ)*(s:ℝ)-(k:ℝ),⟨sub_nonneg.mpr hk0,by linarith⟩⟩
    refine ⟨⟨k,hk⟩,q,Subtype.ext ?_⟩
    dsimp [meshTime,q]
    field_simp
    ring

end HardSphere.Bridge

namespace HardSphere.Bridge
open Wiener GaussianPacking PathCutoff

lemma inverse_heat_tail (n k : ℕ) (hk : 0<k) {τ : ℝ} (hτ : 0<τ) :
    (∑j∈Finset.range n,1/(((k+j+1:ℕ):ℝ)*τ*Real.sqrt (((k+j+1:ℕ):ℝ)*τ)))≤
      2/(τ*Real.sqrt ((k:ℝ)*τ)) := by
  have hx : 0<(k:ℝ)*τ := mul_pos (by exact_mod_cast hk) hτ
  convert singular_sum_bound n hx hτ using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  funext j
  push_cast
  congr 2 <;> ring_nf

lemma mesh_hit_sum {m n : ℕ} (y : Fin m→Point) (I : Finset (Fin n))
    (c : Fin n→C(Time,Point)) (A : Fin n→ℝ) {t r C ε : ℝ}
    (ht : 0<t) (hr : 0 < r) (hC : 0≤C) (hε : 0<ε)
    (hsep : ∀i j,i≠j → ε^2 ≤ square (y i-y j))
    (hA0 : ∀j∈I,0≤A j) (hstart : ∀j∈I,0<(meshTime j 0:ℝ))
    (hA : ∀j∈I,∀q : Time,(q:ℝ)≤(meshRemainder j:ℝ) → ‖c j q-c j 0‖ ≤ r*A j)
    (hdrift : ∀j∈I,(meshTime j 0:ℝ)≤1/2 → (meshRemainder j:ℝ)*C ≤ r)
    (hlate : t/(n:ℝ) ≤ r^2) (hdrift' : C/(n:ℝ) ≤ r)
    {B : Set Point} (hBm : MeasurableSet B) (hB : (volume : Measure Point) B≤1)
    (hBdist : ∀i v,v∈B → ‖v-y i‖≤C) :
    (∑i,((volume.restrict B).prod law) (meshHitUnion I t (y i) B c r C))≤
      ENNReal.ofReal (hitConstant*r^3*((ε⁻¹^3+(m:ℝ))*(∑j∈I,(1+A j)^3)+
        ∑j∈I,(1+A j)^3/(t*(meshTime j 0:ℝ)*Real.sqrt (t*(meshTime j 0:ℝ))))) := by
  have hb i : ((volume.restrict B).prod law) (meshHitUnion I t (y i) B c r C)≤
      ∑j∈I,((volume.restrict B).prod law) (combinedSegmentHit t (y i) B (meshTime j 0) (meshRemainder j) (c j) r C) := by
    exact measure_biUnion_finset_le I _
  apply (Finset.sum_le_sum (fun i _↦hb i)).trans
  rw [Finset.sum_comm]
  have hj j (hj : j∈I) := combined_segment_sum_bound y (meshTime j 0) (meshRemainder j) (c j)
    ht hr hC (hA0 j hj) (hstart j hj) hε hsep (hA j hj) (hdrift j hj)
    (by rw [mesh_remaining]; simpa only [one_div,mul_comm,div_eq_mul_inv,mul_one] using hdrift')
    (by rw [mul_assoc,mesh_remaining]; simpa only [div_eq_mul_inv,one_div,one_mul] using hlate)
    hBm hB hBdist
  apply (Finset.sum_le_sum hj).trans_eq
  rw [←ENNReal.ofReal_sum_of_nonneg (fun j hj ↦ by
    have hh := hitConstant_pos; have ha := hA0 j hj; have hs := hstart j hj; positivity)]
  congr 1
  rw [Finset.mul_sum,←Finset.sum_add_distrib,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  ring

end HardSphere.Bridge

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Cutoffs_CubicMoment
attribute [-instance] _root_.OAI.HardSphere.Bridge.exposedBridgeKernel_markov _root_.OAI.HardSphere.Bridge.exposedPeriodSingle_finite _root_.OAI.HardSphere.Bridge.exposedTrialKernel_markov _root_.OAI.HardSphere.Bridge.instBorelSpaceContinuousMapElemRealTimePoint _root_.OAI.HardSphere.Bridge.instIsProbabilityMeasureNoiseLaw _root_.OAI.HardSphere.Bridge.instMeasurableSpaceContinuousMapElemRealTimePoint _root_.OAI.HardSphere.Bridge.parameterBridgeKernel_markov _root_.OAI.HardSphere.Bridge.parameterIndividualReference_finite _root_.OAI.HardSphere.Bridge.parameterTrialKernel_markov _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Bridge.trialKernel_markov _root_.OAI.HardSphere.Groups.cellPathReference_probability _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Rescaling.config_haar _root_.OAI.HardSphere.Wiener.bridgeLaw_isGaussian _root_.OAI.HardSphere.bridgeEndpointBase_finite _root_.OAI.HardSphere.coordinateBridge_probability _root_.OAI.HardSphere.endpointWeightedBase_sfinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open MeasureTheory Set Filter ProbabilityTheory
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.PathCutoff
open Wiener FreeVisits
attribute [local irreducible] torusDistance freeTrajectory

lemma diameterRatio_nonneg {L : Length} {r : ℝ} (hr : 0 ≤ r) (ω : ConfigurationPath 1 L) : 0≤diameterRatio r ω :=
  div_nonneg (intervalDiameter_nonneg 0 1 ω) hr
lemma cubicCost_nonneg {L : Length} {r : ℝ} (hr : 0 ≤ r) (ω : ConfigurationPath 1 L) : 0 ≤ cubicCost r ω := by
  unfold cubicCost
  have := diameterRatio_nonneg hr ω
  positivity
lemma cubicCost_reverse {L : Length} (r : ℝ) (ω : ConfigurationPath 1 L) :
    cubicCost r (reverseConfigurationPath 1 L ω)=cubicCost r ω := by
  unfold cubicCost diameterRatio
  rw [intervalDiameter_reverse]
  have h1 : reverseTime 1=0 := by apply Subtype.ext; norm_num [reverseTime]
  have h0 : reverseTime 0=1 := by apply Subtype.ext; norm_num [reverseTime]
  rw [h1,h0]

end HardSphere.PathCutoff

end
end

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Cutoffs_PathLift
attribute [-instance] _root_.OAI.HardSphere.Bridge.exposedBridgeKernel_markov _root_.OAI.HardSphere.Bridge.exposedPeriodSingle_finite _root_.OAI.HardSphere.Bridge.exposedTrialKernel_markov _root_.OAI.HardSphere.Bridge.instBorelSpaceContinuousMapElemRealTimePoint _root_.OAI.HardSphere.Bridge.instIsProbabilityMeasureNoiseLaw _root_.OAI.HardSphere.Bridge.instMeasurableSpaceContinuousMapElemRealTimePoint _root_.OAI.HardSphere.Bridge.parameterBridgeKernel_markov _root_.OAI.HardSphere.Bridge.parameterIndividualReference_finite _root_.OAI.HardSphere.Bridge.parameterTrialKernel_markov _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Bridge.trialKernel_markov _root_.OAI.HardSphere.Groups.cellPathReference_probability _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Rescaling.config_haar _root_.OAI.HardSphere.Wiener.bridgeLaw_isGaussian _root_.OAI.HardSphere.bridgeEndpointBase_finite _root_.OAI.HardSphere.coordinateBridge_probability _root_.OAI.HardSphere.endpointWeightedBase_sfinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open MeasureTheory Set Filter ProbabilityTheory
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.PathCutoff
open Wiener FreeVisits
attribute [local irreducible] torusDistance freeTrajectory

lemma exists_pathLift {L : Length} (ω : ConfigurationPath 1 L) : ∃ ζ, IsPathLift ω ζ := by
  have hx (j : Fin 3) : ∃ ζ : C(Time,ℝ), ∀ s, (ζ s : AddCircle L.val)=ω s 0 j := by
    let γ : C(Time,AddCircle L.val) := ⟨fun s ↦ ω s 0 j, by fun_prop⟩
    let x : ℝ := ((AddCircle.equivIco L.val 0) (γ 0)).val
    have h0 : γ 0=(x : AddCircle L.val) := AddCircle.coe_equivIco.symm
    obtain ⟨ζ,hζ,_⟩ := (AddCircle.isCoveringMap_coe L.val).exists_path_lifts γ x h0
    exact ⟨ζ,fun s ↦ congrFun hζ s⟩
  choose ζ hζ using hx
  exact ⟨ζ,hζ⟩

lemma liftDiff_coe {L : Length} {ω : ConfigurationPath 1 L} {ζ : EuclideanPath}
    (hζ : IsPathLift ω ζ) (j : Fin 3) (s q : Time) :
    ((ζ j s-ζ j q : ℝ) : AddCircle L.val)=ω s 0 j-ω q 0 j := by
  rw [AddCircle.coe_sub,hζ j s,hζ j q]

lemma liftDiff_lt_half_period {L : Length} {ω : ConfigurationPath 1 L} {ζ : EuclideanPath}
    (hζ : IsPathLift ω ζ) (a b : Time) (hsmall : intervalDiameter a b ω < L.val/2)
    (j : Fin 3) (s q : Time) :
    |ζ j (intervalTime a b s)-ζ j (intervalTime a b q)| < L.val/2 := by
  by_contra h
  have hf : Continuous (fun v ↦ |ζ j (intervalTime a b v)-ζ j (intervalTime a b q)|) :=
    (((ζ j).continuous.comp (intervalTime_continuous a b)).sub continuous_const).abs
  obtain ⟨v,hv⟩ := intermediate_value_univ q s hf ⟨by simp; exact div_nonneg L.property.le (by norm_num),
    le_of_not_gt h⟩
  dsimp only at hv
  have ha : |ζ j (intervalTime a b v)-ζ j (intervalTime a b q)| ≤ |L.val|/2 := by
    rw [hv,abs_of_pos L.property]
  have he := (AddCircle.norm_coe_eq_abs_iff L.val L.property.ne').mpr ha
  rw [liftDiff_coe hζ,← dist_eq_norm,hv] at he
  have hb := (CellOrbital.dist_coord_le_torusDistance L (ω (intervalTime a b v) 0)
    (ω (intervalTime a b q) 0) j).trans (intervalDistance_le a b v q ω)
  linarith

lemma liftDiff_norm_eq {L : Length} {ω : ConfigurationPath 1 L} {ζ : EuclideanPath}
    (hζ : IsPathLift ω ζ) (a b : Time) (hsmall : intervalDiameter a b ω < L.val/2)
    (j : Fin 3) (s q : Time) :
    dist (ω (intervalTime a b s) 0 j) (ω (intervalTime a b q) 0 j)=
      |ζ j (intervalTime a b s)-ζ j (intervalTime a b q)| := by
  have hle := (liftDiff_lt_half_period hζ a b hsmall j s q).le
  rw [← abs_of_pos L.property] at hle
  have he := (AddCircle.norm_coe_eq_abs_iff L.val L.property.ne').mpr hle
  simpa only [liftDiff_coe hζ,←dist_eq_norm] using he

end HardSphere.PathCutoff

end
end

section
noncomputable section
open MeasureTheory Set Filter ProbabilityTheory
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.PathCutoff
open Wiener FreeVisits
attribute [local irreducible] torusDistance freeTrajectory

lemma diameterRatio_reverse {L : Length} (r : ℝ) (ω : ConfigurationPath 1 L) :
    diameterRatio r (reverseConfigurationPath 1 L ω)=diameterRatio r ω := by
  unfold diameterRatio
  rw [intervalDiameter_reverse]
  simp [reverseTime]

lemma meshRegular_reverse {L : Length} (m : ℕ) (r R C : ℝ) (ω : ConfigurationPath 1 L) :
    MeshRegular m r R C (reverseConfigurationPath 1 L ω) ↔ MeshRegular m r R C ω := by
  unfold MeshRegular
  rw [mesh_sum_reverse _ (cubicCost_reverse r)]
  simp only [meshSegment_reverse,diameterRatio_reverse]
  constructor
  · rintro ⟨h,h'⟩
    exact ⟨fun j ↦ by simpa using h j.rev,h'⟩
  · rintro ⟨h,h'⟩
    exact ⟨fun j ↦ h j.rev,h'⟩

lemma endpointRegular_reverse {L : Length} (u : Time) (S : ℝ) (ω : ConfigurationPath 1 L) :
    EndpointRegular u S (reverseConfigurationPath 1 L ω) ↔ EndpointRegular u S ω := by
  unfold EndpointRegular
  rw [intervalDiameter_reverse,intervalDiameter_reverse,reverseTime_reverse]
  simpa only [reverseTime_zero,reverseTime_one] using (and_comm : (_ ∧ _) ↔ (_ ∧ _))

lemma regular_reverse {L : Length} (m : ℕ) (r R C : ℝ) (u : Time) (S : ℝ) (ω : ConfigurationPath 1 L) :
    Regular m r R C u S (reverseConfigurationPath 1 L ω) ↔ Regular m r R C u S ω := by
  exact and_congr (meshRegular_reverse m r R C ω) (endpointRegular_reverse u S ω)

end HardSphere.PathCutoff

end
end

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Bridges_BridgeStrongRegular
attribute [-instance] _root_.OAI.HardSphere.Bridge.exposedBridgeKernel_markov _root_.OAI.HardSphere.Bridge.exposedPeriodSingle_finite _root_.OAI.HardSphere.Bridge.exposedTrialKernel_markov _root_.OAI.HardSphere.Bridge.instIsProbabilityMeasurePointMidpointNoise _root_.OAI.HardSphere.Bridge.parameterBridgeKernel_markov _root_.OAI.HardSphere.Bridge.parameterIndividualReference_finite _root_.OAI.HardSphere.Bridge.parameterTrialKernel_markov _root_.OAI.HardSphere.Bridge.targetUniform_finite _root_.OAI.HardSphere.Comparison.parameterTargetKernel_finite _root_.OAI.HardSphere.Groups.cellPathReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.Bridge
open Wiener GaussianPacking PathCutoff

lemma trial_left (t : ℝ) (y z u : Point) (β : Noise×Noise) (s : Time) :
    trialPath t y z u β (prefixTime midpointTime s)=leg t y u (pinned β.1) s := by
  have hl : leftTime (prefixTime midpointTime s)=s := by
    apply Subtype.ext
    change min (2*((1/2:ℝ)*(s:ℝ))) 1=(s:ℝ)
    rw [show 2*((1/2:ℝ)*(s:ℝ))=(s:ℝ) by ring,min_eq_left s.property.2]
  have hr : reverseTime (rightTime (prefixTime midpointTime s))=1 := by
    apply Subtype.ext
    change 1-max (2*((1/2:ℝ)*(s:ℝ))-1) 0=1
    rw [max_eq_right (by linarith [s.property.2])]
    ring
  simp only [trialPath,ContinuousMap.coe_mk,hl,hr,pinned_leg_one,add_sub_cancel_right]

lemma trial_right (t : ℝ) (y z u : Point) (β : Noise×Noise) (s : Time) :
    trialPath t y z u β (suffixTime midpointTime s)=leg t z u (pinned β.2) (reverseTime s) := by
  have hl : leftTime (suffixTime midpointTime s)=1 := by
    apply Subtype.ext
    change min (2*((1/2:ℝ)+(1-1/2)*(s:ℝ))) 1=1
    rw [min_eq_right (by linarith [s.property.1])]
  have hr : rightTime (suffixTime midpointTime s)=s := by
    apply Subtype.ext
    change max (2*((1/2:ℝ)+(1-1/2)*(s:ℝ))-1) 0=(s:ℝ)
    rw [show 2*((1/2:ℝ)+(1-1/2)*(s:ℝ))-1=(s:ℝ) by ring,max_eq_left s.property.1]
  simp only [trialPath,ContinuousMap.coe_mk,hl,hr,pinned_leg_one]
  abel

lemma mesh_first_half {n : ℕ} (j : Fin n) (s : Time) :
    meshTime (j.castAdd n) s=prefixTime midpointTime (meshTime j s) := by
  apply Subtype.ext
  simp only [meshTime,Fin.val_castAdd,Nat.cast_add,prefixTime,midpointTime,ContinuousMap.coe_mk]
  ring

end HardSphere.Bridge

end
end

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Bridges_BridgeWindow
attribute [-instance] _root_.OAI.HardSphere.Bridge.exposedBridgeKernel_markov _root_.OAI.HardSphere.Bridge.exposedPeriodSingle_finite _root_.OAI.HardSphere.Bridge.exposedTrialKernel_markov _root_.OAI.HardSphere.Bridge.instIsProbabilityMeasurePointMidpointNoise _root_.OAI.HardSphere.Bridge.parameterBridgeKernel_markov _root_.OAI.HardSphere.Bridge.parameterIndividualReference_finite _root_.OAI.HardSphere.Bridge.parameterTrialKernel_markov _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Bridge.targetUniform_finite _root_.OAI.HardSphere.Comparison.parameterTargetKernel_finite _root_.OAI.HardSphere.Groups.cellPathReference_probability _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Rescaling.config_haar _root_.OAI.HardSphere.bridgeEndpointBase_finite _root_.OAI.HardSphere.endpointWeightedBase_sfinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open MeasureTheory Set Filter ProbabilityTheory
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.Bridge
open Wiener PathCutoff GaussianPacking

lemma torusDistance_nonnegative (L : Length) (x y : Torus L) : 0≤torusDistance L x y := Real.sqrt_nonneg _

lemma nearestLift_project (L : Length) (v : Point) (x : Torus L) :
    projectPoint L (nearestLift L v x)=x := by
  ext j
  simp only [projectPoint,nearestLift,AddCircle.coe_add,AddCircle.coe_equivIco,sub_add_cancel]

lemma nearestLift_coord (L : Length) (v : Point) (x : Torus L) (j : Fin 3) :
    |nearestLift L v x j-v j|=dist (x j) (projectPoint L v j) := by
  let z := (AddCircle.equivIco L.val (-L.val/2)) (x j-(v j : AddCircle L.val))
  have hz : |z.val|≤|L.val|/2 := by
    rw [abs_of_pos L.property,abs_le]
    exact ⟨by linarith [z.property.1],by linarith [z.property.2]⟩
  have he := (AddCircle.norm_coe_eq_abs_iff L.val L.property.ne').mpr hz
  rw [AddCircle.coe_equivIco,←dist_eq_norm] at he
  simpa only [nearestLift,add_sub_cancel_right] using he.symm

lemma nearestLift_bound (L : Length) (v : Point) (x : Torus L) {R : ℝ}
    (h : torusDistance L x (projectPoint L v)≤R) : ‖nearestLift L v x-v‖≤R := by
  apply (pi_norm_le_iff_of_nonneg ((torusDistance_nonnegative L x _).trans h)).mpr
  intro j
  change |nearestLift L v x j-v j|≤R
  rw [nearestLift_coord]
  exact (CellOrbital.dist_coord_le_torusDistance L _ _ j).trans h

lemma local_collision_lifts {L : Length} {v x c c₀ : Point}
    (hL : 50<L.val) (hx : ‖x-v‖≤10) (hc₀ : ‖c₀-v‖≤12) (hc : ‖c-c₀‖≤1)
    {r : ℝ} (hh : torusDistance L (projectPoint L x) (projectPoint L c) ≤ r) : ‖x-c‖ ≤ r := by
  have hr : 0 ≤ r := (torusDistance_nonnegative L _ _).trans hh
  apply (pi_norm_le_iff_of_nonneg hr).mpr
  intro j
  have hnorm : |x j-c j|≤23 := by
    have hxj := (norm_le_pi_norm (x-v) j).trans hx
    have hcj := (norm_le_pi_norm (c-c₀) j).trans hc
    have hc₀j := (norm_le_pi_norm (c₀-v) j).trans hc₀
    change |x j-v j|≤10 at hxj
    change |c j-c₀ j|≤1 at hcj
    change |c₀ j-v j|≤12 at hc₀j
    have he : x j-c j=(x j-v j)-(c₀ j-v j)-(c j-c₀ j) := by ring
    rw [he]
    exact ((abs_sub _ _).trans (add_le_add ((abs_sub _ _).trans (add_le_add hxj hc₀j)) hcj)).trans (by norm_num)
  have he := (AddCircle.norm_coe_eq_abs_iff L.val L.property.ne').mpr
    (show |x j-c j|≤|L.val|/2 by rw [abs_of_pos L.property]; linarith)
  rw [AddCircle.coe_sub,←dist_eq_norm] at he
  change |x j-c j| ≤ r
  rw [←he]
  exact (CellOrbital.dist_coord_le_torusDistance L (projectPoint L x) (projectPoint L c) j).trans hh

end HardSphere.Bridge

end
end

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Bridges_MeshCollision
attribute [-instance] _root_.OAI.HardSphere.Bridge.exposedBridgeKernel_markov _root_.OAI.HardSphere.Bridge.exposedPeriodSingle_finite _root_.OAI.HardSphere.Bridge.exposedTrialKernel_markov _root_.OAI.HardSphere.Bridge.parameterBridgeKernel_markov _root_.OAI.HardSphere.Bridge.parameterIndividualReference_finite _root_.OAI.HardSphere.Bridge.parameterTrialKernel_markov _root_.OAI.HardSphere.Groups.cellPathReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Set Filter ProbabilityTheory
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.Bridge
open Wiener GaussianPacking PathCutoff

lemma weighted_heat_tail {n k : ℕ} (I : Finset (Fin n)) (A : Fin n→ℝ)
    {τ M : ℝ} (hk : 0<k) (hτ : 0<τ) (hM : 0≤M)
    (hlow : ∀j∈I,k<j.val) (hA : ∀j∈I,A j≤M) :
    (∑j∈I,A j/((j:ℝ)*τ*Real.sqrt ((j:ℝ)*τ)))≤
      M*2/(τ*Real.sqrt ((k:ℝ)*τ)) := by
  have hn j (hj : j∈I) : 0<(j:ℝ)*τ :=
    mul_pos (by exact_mod_cast (lt_trans hk (hlow j hj))) hτ
  calc
    _ ≤ ∑j∈I,M*(1/((j:ℝ)*τ*Real.sqrt ((j:ℝ)*τ))) := Finset.sum_le_sum (fun j hj ↦ by
      rw [mul_one_div]
      exact div_le_div_of_nonneg_right (hA j hj) (by positivity))
    _ = M*(∑j∈I,1/((j:ℝ)*τ*Real.sqrt ((j:ℝ)*τ))) := (Finset.mul_sum _ _ _).symm
    _ ≤ M*(2/(τ*Real.sqrt ((k:ℝ)*τ))) := by
      apply mul_le_mul_of_nonneg_left _ hM
      let f (l : ℕ) : ℝ := 1/(((k+l+1:ℕ):ℝ)*τ*Real.sqrt (((k+l+1:ℕ):ℝ)*τ))
      have he : (∑j∈I,1/((j:ℝ)*τ*Real.sqrt ((j:ℝ)*τ)))=
          ∑l∈I.image (fun j ↦ j.val-k-1),f l := by
        rw [Finset.sum_image]
        · apply Finset.sum_congr rfl
          intro j hj
          have hj' := hlow j hj
          have ee : k+(j.val-k-1)+1=j.val := by omega
          simp only [f,ee]
        · intro i hi j hj he
          apply Fin.ext
          have hi' := hlow i hi
          have hj' := hlow j hj
          change i.val-k-1=j.val-k-1 at he
          omega
      rw [he]
      apply (Finset.sum_le_sum_of_subset_of_nonneg (t:=Finset.range n) ?_ ?_).trans
        (inverse_heat_tail n k hk hτ)
      · intro j hj
        obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hj
        exact Finset.mem_range.mpr (by omega)
      · intro j hj _
        positivity
    _ = _ := by ring

lemma mesh_tail_bound {n k : ℕ} (I : Finset (Fin n)) (A : Fin n→ℝ)
    {t R : ℝ} (hk : 0<k) (ht : 0<t) (hR : 0≤R)
    (hlow : ∀j∈I,k<j.val) (hA : ∀j∈I,A j≤R) (hA0 : ∀j∈I,0≤A j) :
    (∑j∈I,(1+A j)^3/(t*(meshTime j 0:ℝ)*Real.sqrt (t*(meshTime j 0:ℝ))))≤
      2*(1+R)^3/((t/(n:ℝ))*Real.sqrt ((k:ℝ)*(t/(n:ℝ)))) := by
  by_cases hn : 0<n
  · have htau : 0<t/(n:ℝ) := div_pos ht (by exact_mod_cast hn)
    have hh := weighted_heat_tail I (fun j ↦ (1+A j)^3) hk htau (show 0≤(1+R)^3 by positivity) hlow
      (fun j hj ↦ pow_le_pow_left₀ (by linarith [hA0 j hj]) (by linarith [hA j hj]) 3)
    convert hh using 1
    · apply Finset.sum_congr rfl
      intro j hj
      have he : t*(meshTime j 0:ℝ)=(j:ℝ)*(t/(n:ℝ)) := by simp only [meshTime,show ((0:Time):ℝ)=0 from rfl,add_zero]; ring
      rw [he]
    · ring
  · have hn0 : n=0 := by omega
    subst n
    have he : I=∅ := Finset.eq_empty_of_forall_notMem (fun j ↦ Fin.elim0 j)
    simp [he]

end HardSphere.Bridge

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Bridges_TrialCutoff
attribute [-instance] _root_.OAI.HardSphere.Bridge.exposedBridgeKernel_markov _root_.OAI.HardSphere.Bridge.exposedPeriodSingle_finite _root_.OAI.HardSphere.Bridge.exposedTrialKernel_markov _root_.OAI.HardSphere.Bridge.instIsProbabilityMeasurePointMidpointNoise _root_.OAI.HardSphere.Bridge.parameterBridgeKernel_markov _root_.OAI.HardSphere.Bridge.parameterIndividualReference_finite _root_.OAI.HardSphere.Bridge.parameterTrialKernel_markov _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Bridge.targetUniform_finite _root_.OAI.HardSphere.Comparison.parameterTargetKernel_finite _root_.OAI.HardSphere.Groups.cellPathReference_probability _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Rescaling.config_haar _root_.OAI.HardSphere.bridgeEndpointBase_finite _root_.OAI.HardSphere.endpointWeightedBase_sfinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.Bridge
open Wiener GaussianPacking PathCutoff

lemma trial_reverse (L : Length) (t : ℝ) (y z u : Point) (β : Noise×Noise) :
    reverseConfigurationPath 1 L (projectCurve L (trialPath t y z u β))=
      projectCurve L (trialPath t z y u β.swap) := by
  have h₁ (s : Time) : leftTime (reverseTime s)=reverseTime (rightTime s) := by
    apply Subtype.ext
    change min (2*(1-(s:ℝ))) 1=1-max (2*(s:ℝ)-1) 0
    by_cases hs : (s:ℝ)≤1/2
    · rw [min_eq_right (by linarith),max_eq_right (by linarith)]; ring
    · rw [min_eq_left (by linarith),max_eq_left (by linarith)]; ring
  have h₂ (s : Time) : reverseTime (rightTime (reverseTime s))=leftTime s := by
    rw [←h₁,reverseTime_reverse]
  apply ContinuousMap.ext
  intro s
  change (fun _ j ↦ ((leg t y u (pinned β.1) (leftTime (reverseTime s))+leg t z u (pinned β.2) (reverseTime (rightTime (reverseTime s)))-u) j : AddCircle L.val))=_
  simp only [h₁,h₂,projectCurve,trialPath,ContinuousMap.coe_mk,Prod.fst_swap,Prod.snd_swap]
  ext i j
  congr 1
  simp only [Pi.add_apply,Pi.sub_apply]
  ring

lemma prefix_or_suffix (s : Time) : (∃q : Time,prefixTime midpointTime q=s) ∨
    ∃q : Time,suffixTime midpointTime q=s := by
  by_cases hs : (s:ℝ)≤1/2
  · refine Or.inl ⟨⟨2*(s:ℝ),⟨by linarith [s.property.1],by linarith⟩⟩,?_⟩
    apply Subtype.ext
    change (1/2:ℝ)*(2*(s:ℝ))=(s:ℝ)
    ring
  · refine Or.inr ⟨⟨2*(s:ℝ)-1,⟨by linarith,by linarith [s.property.2]⟩⟩,?_⟩
    apply Subtype.ext
    change (1/2:ℝ)+(1-1/2)*(2*(s:ℝ)-1)=(s:ℝ)
    ring

lemma trialConfined_measurable (L : Length) (v : Point) : MeasurableSet {f | TrialConfined L v f} := by
  have he : {f | TrialConfined L v f}=⋂s : Time,{f : C(Time,Point) | ‖f s-v‖≤10 ∧ torusDistance L (projectPoint L (f s)) (projectPoint L v)≤10} := by ext f; simp [TrialConfined]
  rw [he]
  apply IsClosed.measurableSet
  apply isClosed_iInter
  intro s
  change IsClosed ({f : C(Time,Point) | ‖f s-v‖≤10} ∩ {f | torusDistance L (projectPoint L (f s)) (projectPoint L v)≤10})
  apply IsClosed.inter
  · exact isClosed_le ((continuous_eval_const s).sub continuous_const).norm continuous_const
  · apply isClosed_le _ continuous_const
    unfold torusDistance projectPoint
    fun_prop

lemma trialCutoff_measurable (L : Length) (n : ℕ) (r R C : ℝ) (w : Time) (S : ℝ) (v : Point) :
    MeasurableSet {f | TrialCutoff L n r R C w S v f} :=
  ((regular_measurable (n+n) r R C (prefixTime midpointTime w) S).preimage (projectCurve_continuous L).measurable).inter (trialConfined_measurable L v)

end HardSphere.Bridge

end
end

section
noncomputable section
open MeasureTheory Set Filter ProbabilityTheory
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.Bridge
open Wiener PathCutoff GaussianPacking

lemma mesh_interval_time {n : ℕ} (j : Fin n) (q : Time) :
    intervalTime (meshTime j 0) (meshTime j 1) q=meshTime j q := by
  apply Subtype.ext
  dsimp [intervalTime,meshTime]
  ring

lemma prefix_representation (w q : Time) (hw : 0<(w:ℝ)) (hq : (q:ℝ)≤(w:ℝ)) :
    ∃u : Time,prefixTime w u=q := by
  refine ⟨⟨(q:ℝ)/(w:ℝ),⟨div_nonneg q.property.1 hw.le,(div_le_one hw).mpr hq⟩⟩,?_⟩
  apply Subtype.ext
  change (w:ℝ)*((q:ℝ)/(w:ℝ))=(q:ℝ)
  exact mul_div_cancel₀ _ hw.ne'

lemma meshLocalLift_zero {L : Length} {n : ℕ} (ω : ConfigurationPath 1 L) (ζ : EuclideanPath)
    (v : Point) (j : Fin n) : meshLocalLift ω ζ v j 0=nearestLift L v (ω (meshTime j 0) 0) := by
  ext k
  simp [meshLocalLift,suffixTime_zero]

lemma meshLocalLift_project {L : Length} {n : ℕ} {ω : ConfigurationPath 1 L} {ζ : EuclideanPath}
    (hζ : IsPathLift ω ζ) (v : Point) (j : Fin n) (q : Time) :
    projectPoint L (meshLocalLift ω ζ v j q)=ω (suffixTime (meshTime j 0) q) 0 := by
  ext k
  change ((ζ k _-ζ k _+nearestLift L v _ k : ℝ) : AddCircle L.val)=_
  rw [AddCircle.coe_add,AddCircle.coe_sub,hζ,hζ]
  have hh := congrFun (nearestLift_project L v (ω (meshTime j 0) 0)) k
  change ((nearestLift L v (ω (meshTime j 0) 0) k:ℝ):AddCircle L.val)=_ at hh
  rw [hh,sub_add_cancel]

lemma meshLocalLift_increment {L : Length} {n : ℕ} {ω : ConfigurationPath 1 L} {ζ : EuclideanPath}
    (hζ : IsPathLift ω ζ) (v : Point) (j : Fin n) {δ : ℝ}
    (hδ : δ< L.val/2) (hd : intervalDiameter (meshTime j 0) (meshTime j 1) ω≤δ)
    (q : Time) (hq : (q:ℝ)≤(meshRemainder j:ℝ)) :
    ‖meshLocalLift ω ζ v j q-meshLocalLift ω ζ v j 0‖≤δ := by
  obtain ⟨u,rfl⟩ := prefix_representation _ q (meshRemainder_pos j) hq
  have hd0 : 0≤δ := (intervalDiameter_nonneg _ _ _).trans hd
  apply (pi_norm_le_iff_of_nonneg hd0).mpr
  intro k
  change |(_- _ + _)-(_- _ + _)|≤δ
  simp only [suffixTime_zero,mesh_suffix_time,sub_self,zero_add,add_sub_cancel_right]
  have hh := liftDiff_norm_eq hζ (meshTime j 0) (meshTime j 1) (hd.trans_lt hδ) k u 0
  simp only [mesh_interval_time] at hh
  rw [←hh]
  have hi : torusDistance L (ω (meshTime j u) 0) (ω (meshTime j 0) 0)≤δ := by
    have h := intervalDistance_le (meshTime j 0) (meshTime j 1) u 0 ω
    simp only [mesh_interval_time] at h
    exact h.trans hd
  exact (CellOrbital.dist_coord_le_torusDistance L _ _ k).trans hi

lemma mesh_torus_hit_local {L : Length} {n : ℕ} {ω : ConfigurationPath 1 L} {ζ : EuclideanPath}
    (hζ : IsPathLift ω ζ) (v x : Point) (j : Fin n) (q : Time) {δ r : ℝ}
    (hL : 50< L.val) (hδ : δ≤1) (hd : intervalDiameter (meshTime j 0) (meshTime j 1) ω≤δ)
    (hx : ‖x-v‖≤10) (hxT : torusDistance L (projectPoint L x) (projectPoint L v)≤10)
    (hr : r≤1) (hit : torusDistance L (projectPoint L x) (ω (meshTime j q) 0)≤ r) :
    torusDistance L (ω (meshTime j 0) 0) (projectPoint L v)≤12 ∧
    ‖x-meshLocalLift ω ζ v j (prefixTime (meshRemainder j) q)‖≤ r := by
  have hos : torusDistance L (ω (meshTime j 0) 0) (ω (meshTime j q) 0)≤δ := by
    have h := intervalDistance_le (meshTime j 0) (meshTime j 1) 0 q ω
    simp only [mesh_interval_time] at h
    exact h.trans hd
  have hn : torusDistance L (ω (meshTime j 0) 0) (projectPoint L v)≤12 := by
    have h1 := torusDistance_triangle' L (ω (meshTime j 0) 0) (ω (meshTime j q) 0) (projectPoint L v)
    have h2 := torusDistance_triangle' L (ω (meshTime j q) 0) (projectPoint L x) (projectPoint L v)
    rw [torusDistance_comm L (ω (meshTime j q) 0) (projectPoint L x)] at h2
    linarith
  refine ⟨hn,?_⟩
  have hc := meshLocalLift_increment hζ v j (show δ< L.val/2 by linarith) hd (prefixTime (meshRemainder j) q)
    (show (prefixTime (meshRemainder j) q:ℝ)≤(meshRemainder j:ℝ) by
      change (meshRemainder j:ℝ)*(q:ℝ)≤(meshRemainder j:ℝ)
      nlinarith [q.property.2,(meshRemainder j).property.1])
  apply local_collision_lifts hL hx (c₀:=meshLocalLift ω ζ v j 0)
    (by rw [meshLocalLift_zero]; exact nearestLift_bound L v _ hn) (hc.trans hδ)
  simpa only [meshLocalLift_project hζ,mesh_suffix_time] using hit

end HardSphere.Bridge

end
end

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Bridges_CollisionBudget
attribute [-instance] _root_.OAI.HardSphere.Bridge.exposedBridgeKernel_markov _root_.OAI.HardSphere.Bridge.exposedPeriodSingle_finite _root_.OAI.HardSphere.Bridge.exposedTrialKernel_markov _root_.OAI.HardSphere.Bridge.instIsProbabilityMeasurePointMidpointNoise _root_.OAI.HardSphere.Bridge.parameterBridgeKernel_markov _root_.OAI.HardSphere.Bridge.parameterIndividualReference_finite _root_.OAI.HardSphere.Bridge.parameterTrialKernel_markov _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Bridge.targetUniform_finite _root_.OAI.HardSphere.Comparison.parameterTargetKernel_finite _root_.OAI.HardSphere.Groups.cellPathReference_probability _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Rescaling.config_haar _root_.OAI.HardSphere.bridgeEndpointBase_finite _root_.OAI.HardSphere.endpointWeightedBase_sfinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.Bridge
open Wiener GaussianPacking PathCutoff

lemma mesh_collision_budget {m n k : ℕ} {t r ε Creg R h : ℝ}
    (hn : 0<n) (ht : 0<t) (hr : 0 < r) (hε : 0<ε) (hCreg : 0≤Creg) (hR : 0≤R) (hh : 0<h)
    (hnscale : (n:ℝ)*r^2≤2*t) (hk : h/4≤(k:ℝ)*(t/(n:ℝ))) :
    hitConstant*r^3*((ε⁻¹^3+(m:ℝ))*(2*Creg*(n:ℝ))+
      2*(1+R)^3/((t/(n:ℝ))*Real.sqrt ((k:ℝ)*(t/(n:ℝ))))) ≤
    hitConstant*(4*Creg*t*r*(ε⁻¹^3+(m:ℝ))+8*r*(1+R)^3/Real.sqrt h) := by
  have hn' : 0<(n:ℝ) := by exact_mod_cast hn
  have hs : 0<Real.sqrt h := Real.sqrt_pos.mpr hh
  have hk' : 0<(k:ℝ)*(t/(n:ℝ)) := lt_of_lt_of_le (by positivity) hk
  have hv : Real.sqrt h/2≤Real.sqrt ((k:ℝ)*(t/(n:ℝ))) := by
    have h := Real.sqrt_le_sqrt hk
    rw [Real.sqrt_div hh.le] at h
    rw [show Real.sqrt 4=2 by norm_num] at h
    exact h
  have hroot : Real.sqrt h≤2*Real.sqrt ((k:ℝ)*(t/(n:ℝ))) := by linarith
  have hmain : r^3*((ε⁻¹^3+(m:ℝ))*(2*Creg*(n:ℝ)))≤4*Creg*t*r*(ε⁻¹^3+(m:ℝ)) := by
    have hmul := mul_le_mul_of_nonneg_right hnscale (show 0≤2*Creg*r*(ε⁻¹^3+(m:ℝ)) by positivity)
    nlinarith
  have htail : r^3*(2*(1+R)^3/((t/(n:ℝ))*Real.sqrt ((k:ℝ)*(t/(n:ℝ)))))≤8*r*(1+R)^3/Real.sqrt h := by
    rw [←mul_div_assoc]
    apply (div_le_div_iff₀ (mul_pos (div_pos ht hn') (Real.sqrt_pos.mpr hk')) hs).mpr
    have hb : (n:ℝ)*r^2*Real.sqrt h ≤ 4*t*Real.sqrt ((k:ℝ)*(t/(n:ℝ))) := calc
      _ ≤ (n:ℝ)*r^2*(2*Real.sqrt ((k:ℝ)*(t/(n:ℝ)))) :=
        mul_le_mul_of_nonneg_left hroot (by positivity)
      _ ≤ 2*t*(2*Real.sqrt ((k:ℝ)*(t/(n:ℝ)))) :=
        mul_le_mul_of_nonneg_right hnscale (by positivity)
      _ = _ := by ring
    have hmul := mul_le_mul_of_nonneg_right hb (show 0≤2*r*(1+R)^3 by positivity)
    apply (mul_le_mul_iff_right₀ hn').mp
    convert hmul using 1 <;> field_simp
    ring

  have hc := hitConstant_pos.le
  nlinarith

end HardSphere.Bridge

end
end

section
noncomputable section
open MeasureTheory Set Filter ProbabilityTheory
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.Bridge
open Wiener PathCutoff GaussianPacking

lemma torusLegHit_subset {L : Length} {n : ℕ} (hn : 0< n) (I : Finset (Fin n))
    (t : ℝ) (y v : Point) (B : Set Point) (ω : ConfigurationPath 1 L) (ζ : EuclideanPath)
    (hζ : IsPathLift ω ζ) {r C h : ℝ} (hL : 50< L.val) (hr : r≤1)
    (hdiam : ∀j∈I,intervalDiameter (meshTime j 0) (meshTime j 1) ω≤1)
    (hI : ∀j : Fin n,∀q : Time,h≤(meshTime j q:ℝ) → j∈I) :
    torusLegHit t y v B ω r C h⊆meshHitUnion I t y B (meshLocalLift ω ζ v) r C := by
  rintro ⟨u,β⟩ ⟨hu,hconf,hconf',s,hs,hit⟩
  obtain ⟨j,q,hq⟩ := mesh_covers hn s
  have hj : j∈I := hI j q (by simpa only [hq] using hs)
  have hh := (mesh_torus_hit_local hζ v (leg t y u β (meshTime j q)) j q hL
    (le_refl 1) (hdiam j hj) (hconf (meshTime j q)).1 (hconf (meshTime j q)).2 hr
    (by simpa only [hq] using hit)).2
  change (u,β)∈⋃j∈I,combinedSegmentHit t y B (meshTime j 0) (meshRemainder j) (meshLocalLift ω ζ v j) r C
  refine mem_iUnion.mpr ⟨j,mem_iUnion.mpr ⟨hj,?_⟩⟩
  by_cases hearly : (meshTime j 0:ℝ)≤1/2
  · simp only [combinedSegmentHit,ite_eq_left hearly,jointSegmentHit,mem_ofPred_eq,segmentHit]
    exact ⟨hconf' _,prefixTime (meshRemainder j) q,prefixTime_le _ _,by simpa only [mesh_suffix_time] using hh⟩
  · simp only [combinedSegmentHit,ite_eq_right hearly,mem_preimage,uniformSegmentHit,mem_ofPred_eq,Prod.swap_prod_mk]
    exact ⟨hu,prefixTime (meshRemainder j) q,prefixTime_le _ _,by simpa only [mesh_suffix_time] using hh⟩

lemma torusLegHit_sum {L : Length} {m n k : ℕ} (hn : 0< n) (hk : 0< k)
    (y : Fin m→Point) (v : Point) (I : Finset (Fin n)) (ω : ConfigurationPath 1 L) (A : Fin n→ℝ)
    {t r C ε h R J : ℝ}
    (hL : 50< L.val) (ht : 0< t) (hr : 0< r) (hr1 : r≤1) (hC : 0≤ C) (hε : 0<ε) (hR : 0≤ R)
    (hsep : ∀i j,i≠j → ε^2≤ square (y i-y j))
    (hI : ∀j : Fin n,∀q : Time,h≤(meshTime j q:ℝ) → j∈I)
    (hlow : ∀j∈I,k< j.val)
    (hA0 : ∀j∈I,0≤ A j) (hAmax : ∀j∈I,A j≤ R) (hAsum : (∑j∈I,(1+A j)^3)≤ J)
    (hsmall : ∀j∈I,r*A j≤1)
    (hdiam : ∀j∈I,intervalDiameter (meshTime j 0) (meshTime j 1) ω≤ r*A j)
    (hdrift : ∀j∈I,(meshTime j 0:ℝ)≤1/2 → (meshRemainder j:ℝ)*C≤ r)
    (hlate : t/(n:ℝ)≤ r^2) (hdrift' : C/(n:ℝ)≤ r)
    {B : Set Point} (hBm : MeasurableSet B) (hB : (volume : Measure Point) B≤1)
    (hBdist : ∀i u,u∈B → ‖u-y i‖≤ C) :
    (∑i,((volume.restrict B).prod law) (torusLegHit t (y i) v B ω r C h))≤
      ENNReal.ofReal (hitConstant*r^3*((ε⁻¹^3+(m:ℝ))*J+
        2*(1+R)^3/((t/(n:ℝ))*Real.sqrt ((k:ℝ)*(t/(n:ℝ)))))) := by
  obtain ⟨ζ,hζ⟩ := exists_pathLift ω
  have hstart j (hj : j∈I) : 0<(meshTime j 0:ℝ) := by
    change 0<((j:ℝ)+0)/(n:ℝ)
    exact div_pos (by exact_mod_cast (lt_trans hk (hlow j hj))) (by exact_mod_cast hn)
  apply (Finset.sum_le_sum (fun i _ ↦ measure_mono (torusLegHit_subset hn I t (y i) v B ω ζ hζ hL hr1
    (fun j hj ↦ (hdiam j hj).trans (hsmall j hj)) hI))).trans
  apply (mesh_hit_sum y I (meshLocalLift ω ζ v) A ht hr hC hε hsep hA0 hstart
    (fun j hj q hq ↦ meshLocalLift_increment hζ v j (by linarith [hsmall j hj]) (hdiam j hj) q hq)
    hdrift hlate hdrift' hBm hB hBdist).trans
  apply ENNReal.ofReal_le_ofReal
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg hitConstant_pos.le (pow_nonneg hr.le _))
  exact add_le_add (mul_le_mul_of_nonneg_left hAsum (by positivity))
    (mesh_tail_bound I A hk ht hR hlow hAmax hA0)

end HardSphere.Bridge

end
end

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.Bridge
open Wiener GaussianPacking PathCutoff

lemma mesh_endpoint_index {n : ℕ} (j : Fin n) (q : Time) {t h : ℝ}
    (ht : 0< t) (hh : 2*(t/(n:ℝ))≤ h) (hs : h/t≤(meshTime j q:ℝ)) :
    h/(2*t)≤(meshTime j 0:ℝ) := by
  have hn : (0:ℝ)< n := by exact_mod_cast j.pos
  have hs' : h*(n:ℝ)≤ t*((j:ℝ)+(q:ℝ)) := by
    change h/t≤((j:ℝ)+(q:ℝ))/(n:ℝ) at hs
    simpa only [mul_comm t] using (div_le_div_iff₀ ht hn).mp hs
  have hh' : 2*t≤ h*(n:ℝ) := by
    have := (div_le_iff₀ hn).mp (show 2*t/(n:ℝ)≤ h by simpa [mul_div_assoc] using hh)
    linarith
  change h/(2*t)≤((j:ℝ)+0)/(n:ℝ)
  rw [add_zero]
  apply (div_le_div_iff₀ (by positivity : 0<2*t) hn).mpr
  have hq := q.property.2
  nlinarith

lemma endpointIndex_pos {n : ℕ} {t h : ℝ} (ht : 0< t)
    (hlarge : 8*t≤(n:ℝ)*h) : 0< endpointIndex n t h := by
  apply Nat.floor_pos.mpr
  apply (le_div_iff₀ (by positivity : 0<4*t)).mpr
  linarith
lemma endpointIndex_gap {n : ℕ} (j : Fin n) {t h : ℝ} (ht : 0< t) (hh : 0< h)
    (hj : h/(2*t)≤(meshTime j 0:ℝ)) : endpointIndex n t h< j.val := by
  have hn : (0:ℝ)< n := by exact_mod_cast j.pos
  have hk := Nat.floor_le (show 0≤(n:ℝ)*h/(4*t) by positivity)
  have hj' : h*(n:ℝ)≤(j:ℝ)*(2*t) := by
    change h/(2*t)≤((j:ℝ)+0)/(n:ℝ) at hj
    rw [add_zero] at hj
    exact (div_le_div_iff₀ (by positivity : 0<2*t) hn).mp hj
  have hc : (endpointIndex n t h:ℝ)<(j:ℝ) := by
    apply lt_of_le_of_lt hk
    apply (div_lt_iff₀ (by positivity : 0<4*t)).mpr
    nlinarith
  exact_mod_cast hc
lemma endpointIndex_scale {n : ℕ} (hn : 0< n) {t h : ℝ} (ht : 0< t)
    (hlarge : 8*t≤(n:ℝ)*h) : h/8≤(endpointIndex n t h:ℝ)*(t/(n:ℝ)) := by
  have hn' : (0:ℝ)< n := by exact_mod_cast hn
  have hk : (n:ℝ)*h/(4*t)<(endpointIndex n t h:ℝ)+1 := Nat.lt_floor_add_one _
  have hk' := (div_lt_iff₀ (by positivity : 0<4*t)).mp hk
  rw [←mul_div_assoc]
  apply (le_div_iff₀ hn').mpr
  change h/8*(n:ℝ)≤(endpointIndex n t h:ℝ)*t
  nlinarith

end HardSphere.Bridge

end
end

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Bridges_PhysicalLegCollision
attribute [-instance] _root_.OAI.HardSphere.Bridge.exposedBridgeKernel_markov _root_.OAI.HardSphere.Bridge.exposedPeriodSingle_finite _root_.OAI.HardSphere.Bridge.exposedTrialKernel_markov _root_.OAI.HardSphere.Bridge.instIsProbabilityMeasurePointMidpointNoise _root_.OAI.HardSphere.Bridge.parameterBridgeKernel_markov _root_.OAI.HardSphere.Bridge.parameterIndividualReference_finite _root_.OAI.HardSphere.Bridge.parameterTrialKernel_markov _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Bridge.targetUniform_finite _root_.OAI.HardSphere.Comparison.parameterTargetKernel_finite _root_.OAI.HardSphere.Groups.cellPathReference_probability _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Rescaling.config_haar _root_.OAI.HardSphere.bridgeEndpointBase_finite _root_.OAI.HardSphere.endpointWeightedBase_sfinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.Bridge
open Wiener GaussianPacking PathCutoff

lemma meshInterval_diameter {L : Length} {n : ℕ} (j : Fin n) (ω : ConfigurationPath 1 L) :
    intervalDiameter (meshTime j 0) (meshTime j 1) ω=intervalDiameter 0 1 (meshSegment j ω) := by
  unfold intervalDiameter
  congr 1
  ext p
  change torusDistance L (ω (intervalTime (meshTime j 0) (meshTime j 1) p.1) 0)
    (ω (intervalTime (meshTime j 0) (meshTime j 1) p.2) 0)=_
  simp only [mesh_interval_time,meshSegment]
  have he (s : Time) : intervalTime 0 1 s=s := by apply Subtype.ext; simp [intervalTime]
  simp only [diameterMap,ContinuousMap.coe_mk,he]

lemma meshRemainder_early_bound {n : ℕ} (j : Fin n) (hj : (meshTime j 0:ℝ)≤1/2) :
    (meshRemainder j:ℝ)≤2/(n:ℝ) := by
  have hn : (0:ℝ)<n := by exact_mod_cast j.pos
  have h := mesh_remaining j
  have hnon := (meshRemainder j).property.1
  have hh := mul_le_mul_of_nonneg_right (show (1:ℝ)/2≤1-(meshTime j 0:ℝ) by linarith) hnon
  rw [h] at hh
  have he : (2:ℝ)/(n:ℝ)=2*(1/(n:ℝ)) := by ring
  rw [he]
  linarith

lemma physical_leg_collision {L : Length} {m n : ℕ} (hn : 0<n)
    (y : Fin m→Point) (v : Point) (ω : ConfigurationPath 1 L)
    {t r C ε h R Creg : ℝ}
    (hL : 50<L.val) (ht : 0<t) (hr : 0 < r) (hr1 : r≤1) (hC : 0≤C) (hε : 0<ε)
    (hR : 0≤R) (hCreg : 0≤Creg) (hh : 0<h)
    (hsep : ∀i j,i≠j → ε^2≤ square (y i-y j))
    (hreg : MeshRegular n r R Creg ω) (hsmall : r*R≤1)
    (hτr : t/(n:ℝ) ≤ r^2) (hnscale : (n:ℝ)*r^2≤2*t)
    (hwindow : 2*(t/(n:ℝ))≤h) (hlarge : 8*t≤(n:ℝ)*h) (hdrift : 2*C/(n:ℝ) ≤ r)
    {B : Set Point} (hBm : MeasurableSet B) (hB : (volume : Measure Point) B≤1)
    (hBdist : ∀i u,u∈B → ‖u-y i‖≤C) :
    (∑i,((volume.restrict B).prod law) (torusLegHit t (y i) v B ω r C (h/t)))≤
      ENNReal.ofReal (hitConstant*(4*Creg*t*r*(ε⁻¹^3+(m:ℝ))+8*r*(1+R)^3/Real.sqrt (h/2))) := by
  classical
  let I : Finset (Fin n) := Finset.univ.filter (fun j ↦ h/(2*t)≤(meshTime j 0:ℝ))
  let A : Fin n→ℝ := fun j ↦ diameterRatio r (meshSegment j ω)
  have hI j (hj : j∈I) : h/(2*t)≤(meshTime j 0:ℝ) := (Finset.mem_filter.mp hj).2
  have hA0 j : 0≤A j := diameterRatio_nonneg hr.le _
  have hAsum : (∑j∈I,(1+A j)^3)≤2*Creg*(n:ℝ) := by
    apply (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun j _ _ ↦ by have := hA0 j; positivity)).trans
    exact hreg.2.trans (by nlinarith)
  have hdi j : intervalDiameter (meshTime j 0) (meshTime j 1) ω ≤ r*A j := by
    rw [meshInterval_diameter]
    dsimp [A,diameterRatio]
    rw [mul_div_cancel₀ _ hr.ne']
  have hd1 : C/(n:ℝ) ≤ r := (div_le_div_of_nonneg_right (by linarith : C≤2*C) (by positivity)).trans hdrift
  have hh' := torusLegHit_sum hn (endpointIndex_pos ht hlarge) y v I ω A hL ht hr hr1 hC hε hR hsep
    (fun j q hq ↦ Finset.mem_filter.mpr ⟨Finset.mem_univ _,mesh_endpoint_index j q ht hwindow hq⟩)
    (fun j hj ↦ endpointIndex_gap j ht hh (hI j hj))
    (fun j _ ↦ hA0 j) (fun j _ ↦ hreg.1 j) hAsum
    (fun j _ ↦ (mul_le_mul_of_nonneg_left (hreg.1 j) hr.le).trans hsmall)
    (fun j _ ↦ hdi j)
    (fun j _ hj ↦ (mul_le_mul_of_nonneg_right (meshRemainder_early_bound j hj) hC).trans (by simpa [div_mul_eq_mul_div] using hdrift))
    hτr hd1 hBm hB hBdist
  apply hh'.trans
  apply ENNReal.ofReal_le_ofReal
  apply mesh_collision_budget hn ht hr hε hCreg hR (by positivity) hnscale
  have hs := endpointIndex_scale hn ht hlarge
  simpa only [div_div,show (2:ℝ)*4=8 by norm_num] using hs

end HardSphere.Bridge

end
end

section
noncomputable section
open Set MeasureTheory ProbabilityTheory
namespace HardSphere.Bridge
open Wiener PathCutoff

lemma interval_start_displacement {L : Length} (ω : ConfigurationPath 1 L) (w s : Time)
    (hs : (s:ℝ)≤(w:ℝ)) :
    torusDistance L (ω s 0) (ω 0 0)≤ intervalDiameter 0 w ω := by
  by_cases hw : (w:ℝ)=0
  · have hs0 : s=0 := Subtype.ext (by simpa using le_antisymm (hs.trans_eq hw) s.property.1)
    rw [hs0]
    have he : torusDistance L (ω 0 0) (ω 0 0)=0 := by simp [torusDistance]
    rw [he]
    exact intervalDiameter_nonneg _ _ _
  have hwpos : 0<(w:ℝ) := lt_of_le_of_ne w.property.1 (Ne.symm hw)
  let q : Time := ⟨(s:ℝ)/(w:ℝ),⟨div_nonneg s.property.1 w.property.1,(div_le_one hwpos).mpr hs⟩⟩
  have hq : intervalTime 0 w q=s := by
    apply Subtype.ext
    change (1-(s:ℝ)/(w:ℝ))*0+((s:ℝ)/(w:ℝ))*(w:ℝ)=(s:ℝ)
    simp only [mul_zero,zero_add,div_mul_cancel₀ _ hw]
  simpa only [hq,intervalTime_zero] using intervalDistance_le 0 w q 0 ω

lemma no_collision_endpoint_window {L : Length} {r S : ℝ} (ω ζ : ConfigurationPath 1 L)
    (w : Time) (hω : intervalDiameter 0 w ω≤ S) (hζ : intervalDiameter 0 w ζ≤ S)
    (hsep : r+2*S< torusDistance L (ω 0 0) (ζ 0 0))
    (s : Time) (hs : (s:ℝ)≤(w:ℝ)) :
    r< torusDistance L (ω s 0) (ζ s 0) := by
  have h₁ := (interval_start_displacement ω w s hs).trans hω
  have h₂ := (interval_start_displacement ζ w s hs).trans hζ
  have ht₁ := torusDistance_triangle' L (ω 0 0) (ω s 0) (ζ 0 0)
  have ht₂ := torusDistance_triangle' L (ω s 0) (ζ s 0) (ζ 0 0)
  rw [torusDistance_comm L (ω 0 0) (ω s 0)] at ht₁
  linarith

lemma collision_after_window {L : Length} {r S : ℝ} (ω ζ : ConfigurationPath 1 L)
    (w : Time) (hω : intervalDiameter 0 w ω≤ S) (hζ : intervalDiameter 0 w ζ≤ S)
    (hsep : r+2*S< torusDistance L (ω 0 0) (ζ 0 0))
    (s : Time) (hit : torusDistance L (ω s 0) (ζ s 0)≤ r) :
    (w:ℝ)<(s:ℝ) := by
  by_contra hn
  exact (not_lt_of_ge hit) (no_collision_endpoint_window ω ζ w hω hζ hsep s (le_of_not_gt hn))

end HardSphere.Bridge

end
end

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.Bridge
open Wiener GaussianPacking PathCutoff

lemma prefix_mesh_half {L : Length} {n : ℕ} (j : Fin n) (ω : ConfigurationPath 1 L) :
    meshSegment j (configurationPrefix 1 L midpointTime ω)=meshSegment (j.castAdd n) ω := by
  apply ContinuousMap.ext
  intro s
  simp only [meshSegment,configurationPrefix,ContinuousMap.coe_mk,ContinuousMap.comp_apply,mesh_first_half]

lemma prefix_mesh_regular {L : Length} {n : ℕ} {r R C : ℝ} (hr : 0 ≤ r) (ω : ConfigurationPath 1 L)
    (h : MeshRegular (n+n) r R C ω) :
    MeshRegular n r R (2*C) (configurationPrefix 1 L midpointTime ω) := by
  constructor
  · intro j
    rw [prefix_mesh_half]
    exact h.1 (j.castAdd n)
  · simp_rw [prefix_mesh_half]
    have hs := h.2
    rw [Fin.sum_univ_add] at hs
    have hn : 0≤∑j : Fin n,cubicCost r (meshSegment (j.natAdd n) ω) :=
      Finset.sum_nonneg (fun j _ ↦ cubicCost_nonneg hr _)
    push_cast at hs
    nlinarith

lemma prefix_window_diameter {L : Length} (ω : ConfigurationPath 1 L) (w : Time) :
    intervalDiameter 0 w (configurationPrefix 1 L midpointTime ω)=
      intervalDiameter 0 (prefixTime midpointTime w) ω := by
  apply congrArg norm
  apply ContinuousMap.ext
  intro p
  have he (s : Time) : prefixTime midpointTime (intervalTime 0 w s)=intervalTime 0 (prefixTime midpointTime w) s := by
    apply Subtype.ext
    simp [prefixTime,intervalTime,midpointTime]
    ring
  change torusDistance L (ω (prefixTime midpointTime (intervalTime 0 w p.1)) 0)
    (ω (prefixTime midpointTime (intervalTime 0 w p.2)) 0)=_
  rw [he,he]
  rfl

lemma trial_initial_projection (L : Length) (t : ℝ) (y z u : Point) (β : Noise×Noise) :
    configurationPrefix 1 L midpointTime (projectCurve L (trialPath t y z u β))=
      projectCurve L (leg t y u (pinned β.1)) := by
  apply ContinuousMap.ext
  intro s
  simp only [configurationPrefix,projectCurve,ContinuousMap.coe_mk,ContinuousMap.comp_apply,trial_left]

lemma trial_hit_first {L : Length} {n : ℕ} {t r R C S : ℝ}
    (y z u v : Point) (B : Set Point) (β : Noise×Noise) (w q : Time) (ω : ConfigurationPath 1 L)
    (hu : u∈B) (huv : ‖u-v‖≤3)
    (hf : TrialCutoff L n r R C w S v (trialPath t y z u β))
    (hω : EndpointRegular (prefixTime midpointTime w) S ω)
    (hsep : r+2*S<torusDistance L (projectPoint L y) (ω 0 0))
    (hit : torusDistance L (projectPoint L (trialPath t y z u β (prefixTime midpointTime q)))
      (ω (prefixTime midpointTime q) 0) ≤ r) :
    (u,pinned β.1)∈torusLegHit t y v B (configurationPrefix 1 L midpointTime ω) r 13 (w:ℝ) := by
  have htreg : intervalDiameter 0 w (projectCurve L (leg t y u (pinned β.1)))≤S := by
    rw [←trial_initial_projection,prefix_window_diameter]
    exact hf.1.2.1
  have how : intervalDiameter 0 w (configurationPrefix 1 L midpointTime ω)≤S := by
    rw [prefix_window_diameter]
    exact hω.1
  have hs := collision_after_window (projectCurve L (leg t y u (pinned β.1)))
    (configurationPrefix 1 L midpointTime ω) w htreg how
    (by simpa only [projectCurve,configurationPrefix,ContinuousMap.coe_mk,ContinuousMap.comp_apply,pinned_leg_zero,
      show prefixTime midpointTime 0=0 by apply Subtype.ext; simp [prefixTime]] using hsep) q
    (by simpa only [trial_left,projectCurve,configurationPrefix,ContinuousMap.coe_mk,ContinuousMap.comp_apply] using hit)
  refine ⟨hu,?_,?_,q,hs.le,?_⟩
  · intro s
    simpa only [trial_left] using hf.2 (prefixTime midpointTime s)
  · intro s
    have hc := (hf.2 (prefixTime midpointTime s)).1
    rw [trial_left] at hc
    have hvu : ‖v-u‖≤3 := by simpa only [norm_sub_rev] using huv
    exact (norm_sub_le_norm_sub_add_norm_sub (leg t y u (pinned β.1) s) v u).trans (by linarith)
  · simpa only [trial_left,configurationPrefix,ContinuousMap.coe_mk,ContinuousMap.comp_apply] using hit

lemma reverse_suffix_midpoint (q : Time) :
    reverseTime (suffixTime midpointTime q)=prefixTime midpointTime (reverseTime q) := by
  apply Subtype.ext
  change 1-((1/2:ℝ)+(1-1/2)*(q:ℝ))=(1/2)*(1-(q:ℝ))
  ring

lemma trialCutoff_reverse {L : Length} {n : ℕ} {t r R C S : ℝ}
    (y z u v : Point) (β : Noise×Noise) (w : Time) :
    TrialCutoff L n r R C w S v (trialPath t z y u β.swap) ↔
    TrialCutoff L n r R C w S v (trialPath t y z u β) := by
  have hf : ∀s : Time,trialPath t z y u β.swap s=trialPath t y z u β (reverseTime s) := by
    intro s
    have hs := congrArg (fun ω : ConfigurationPath 1 L ↦ ω s 0) (trial_reverse L t y z u β)

    have h₁ : leftTime (reverseTime s)=reverseTime (rightTime s) := by
      apply Subtype.ext
      change min (2*(1-(s:ℝ))) 1=1-max (2*(s:ℝ)-1) 0
      by_cases hh : (s:ℝ)≤1/2
      · rw [min_eq_right (by linarith),max_eq_right (by linarith)]; ring
      · rw [min_eq_left (by linarith),max_eq_left (by linarith)]; ring
    have h₂ : reverseTime (rightTime (reverseTime s))=leftTime s := by
      apply Subtype.ext
      change 1-max (2*(1-(s:ℝ))-1) 0=min (2*(s:ℝ)) 1
      by_cases hh : (s:ℝ)≤1/2
      · rw [max_eq_left (by linarith),min_eq_left (by linarith)]; ring
      · rw [max_eq_right (by linarith),min_eq_right (by linarith)]; ring
    simp only [trialPath,ContinuousMap.coe_mk,h₁,h₂,Prod.fst_swap,Prod.snd_swap]
    abel
  change (_ ∧ _) ↔ (_ ∧ _)
  rw [←trial_reverse,regular_reverse]
  apply and_congr_right
  intro _
  unfold TrialConfined
  constructor
  · intro h s
    simpa only [hf,reverseTime_reverse] using h (reverseTime s)
  · intro h s
    rw [hf]
    exact h (reverseTime s)

lemma trial_hit_cases {L : Length} {n : ℕ} {t r R C S : ℝ}
    (y z u v : Point) (B : Set Point) (β : Noise×Noise) (w : Time) (ω : ConfigurationPath 1 L)
    (hu : u∈B) (huv : ‖u-v‖≤3)
    (hf : TrialCutoff L n r R C w S v (trialPath t y z u β))
    (hω : EndpointRegular (prefixTime midpointTime w) S ω)
    (hy : r+2*S<torusDistance L (projectPoint L y) (ω 0 0))
    (hz : r+2*S<torusDistance L (projectPoint L z) (ω 1 0))
    (hit : ∃s : Time,torusDistance L (projectPoint L (trialPath t y z u β s)) (ω s 0) ≤ r) :
    (u,pinned β.1)∈torusLegHit t y v B (configurationPrefix 1 L midpointTime ω) r 13 (w:ℝ) ∨
    (u,pinned β.2)∈torusLegHit t z v B (configurationPrefix 1 L midpointTime (reverseConfigurationPath 1 L ω)) r 13 (w:ℝ) := by
  obtain ⟨s,hs⟩ := hit
  rcases prefix_or_suffix s with ⟨q,rfl⟩|⟨q,rfl⟩
  · exact Or.inl (trial_hit_first y z u v B β w q ω hu huv hf hω hy hs)
  · apply Or.inr
    apply trial_hit_first z y u v B β.swap w (reverseTime q) (reverseConfigurationPath 1 L ω) hu huv
      ((trialCutoff_reverse y z u v β w).mpr hf) ((endpointRegular_reverse _ _ _).mpr hω)
      (by simpa only [reverseConfigurationPath,ContinuousMap.coe_mk,ContinuousMap.comp_apply,reverseTime_zero] using hz)
    have ht : reverseTime (prefixTime midpointTime (reverseTime q))=suffixTime midpointTime q := by
      rw [←reverse_suffix_midpoint,reverseTime_reverse]
    simpa only [trial_left,Prod.fst_swap,trial_right,reverseConfigurationPath,ContinuousMap.coe_mk,ContinuousMap.comp_apply,ht] using hs

end HardSphere.Bridge

end
end

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Bridges_TrialHitMeasure
attribute [-instance] _root_.OAI.HardSphere.Bridge.exposedBridgeKernel_markov _root_.OAI.HardSphere.Bridge.exposedPeriodSingle_finite _root_.OAI.HardSphere.Bridge.exposedTrialKernel_markov _root_.OAI.HardSphere.Bridge.instIsProbabilityMeasurePointMidpointNoise _root_.OAI.HardSphere.Bridge.parameterBridgeKernel_markov _root_.OAI.HardSphere.Bridge.parameterIndividualReference_finite _root_.OAI.HardSphere.Bridge.parameterTrialKernel_markov _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Bridge.targetUniform_finite _root_.OAI.HardSphere.Comparison.parameterTargetKernel_finite _root_.OAI.HardSphere.Groups.cellPathReference_probability _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Rescaling.config_haar _root_.OAI.HardSphere.bridgeEndpointBase_finite _root_.OAI.HardSphere.endpointWeightedBase_sfinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.Bridge
open Wiener GaussianPacking PathCutoff

lemma trialCutoffHit_le {L : Length} {n : ℕ} {t r R C S : ℝ}
    (y z v : Point) (B : Set Point) (w : Time) (ω : ConfigurationPath 1 L)
    (hB : ∀u∈B,‖u-v‖≤3) (hω : EndpointRegular (prefixTime midpointTime w) S ω)
    (hy : r+2*S<torusDistance L (projectPoint L y) (ω 0 0))
    (hz : r+2*S<torusDistance L (projectPoint L z) (ω 1 0)) :
    ((volume.restrict B).prod (law.prod law)) (trialCutoffHit n t r R C S y z v B w ω)≤
      ((volume.restrict B).prod law) (torusLegHit t y v B (configurationPrefix 1 L midpointTime ω) r 13 (w:ℝ))+
      ((volume.restrict B).prod law) (torusLegHit t z v B (configurationPrefix 1 L midpointTime (reverseConfigurationPath 1 L ω)) r 13 (w:ℝ)) := by
  let A := torusLegHit t y v B (configurationPrefix 1 L midpointTime ω) r 13 (w:ℝ)
  let D := torusLegHit t z v B (configurationPrefix 1 L midpointTime (reverseConfigurationPath 1 L ω)) r 13 (w:ℝ)
  let f : Point×(Noise×Noise)→Point×Noise := fun p ↦ (p.1,pinned p.2.1)
  let g : Point×(Noise×Noise)→Point×Noise := fun p ↦ (p.1,pinned p.2.2)
  have hpin : MeasurePreserving pinned law law := ⟨pinned_continuous.measurable,pinned_law⟩
  have hf : MeasurePreserving f ((volume.restrict B).prod (law.prod law)) ((volume.restrict B).prod law) :=
    (MeasurePreserving.id _).prod (hpin.comp (measurePreserving_fst (μ:=law) (ν:=law)))
  have hg : MeasurePreserving g ((volume.restrict B).prod (law.prod law)) ((volume.restrict B).prod law) :=
    (MeasurePreserving.id _).prod (hpin.comp (measurePreserving_snd (μ:=law) (ν:=law)))
  have hsub : trialCutoffHit n t r R C S y z v B w ω⊆f⁻¹' A∪g⁻¹' D := by
    rintro ⟨u,β⟩ ⟨hu,hcut,hit⟩
    exact trial_hit_cases y z u v B β w ω hu (hB u hu) hcut hω hy hz hit
  apply ((measure_mono hsub).trans (measure_union_le _ _)).trans
  exact add_le_add (hf.measure_preimage_le A) (hg.measure_preimage_le D)

lemma physical_trial_collision {L : Length} {m n : ℕ} (hn : 0<n)
    (y z : Fin m→Point) (v : Point) (ω : ConfigurationPath 1 L)
    {t r ε h R Creg S : ℝ} (w : Time)
    (hL : 50<L.val) (ht : 0<t) (hr : 0 < r) (hr1 : r≤1) (hε : 0<ε)
    (hR : 0≤R) (hCreg : 0≤Creg) (hh : 0<h) (hw : (w:ℝ)=h/t)
    (hsepY : ∀i j,i≠j → ε^2≤ square (y i-y j))
    (hsepZ : ∀i j,i≠j → ε^2≤ square (z i-z j))
    (hreg : Regular (n+n) r R Creg (prefixTime midpointTime w) S ω) (hsmall : r*R≤1)
    (hτr : t/(n:ℝ) ≤ r^2) (hnscale : (n:ℝ)*r^2≤2*t)
    (hwindow : 2*(t/(n:ℝ))≤h) (hlarge : 8*t≤(n:ℝ)*h) (hdrift : 2*13/(n:ℝ) ≤ r)
    {B : Set Point} (hBm : MeasurableSet B) (hB : (volume : Measure Point) B≤1)
    (hBv : ∀u∈B,‖u-v‖≤3)
    (hBY : ∀i u,u∈B → ‖u-y i‖≤13) (hBZ : ∀i u,u∈B → ‖u-z i‖≤13)
    (hy : ∀i,r+2*S<torusDistance L (projectPoint L (y i)) (ω 0 0))
    (hz : ∀i,r+2*S<torusDistance L (projectPoint L (z i)) (ω 1 0)) :
    (∑i,((volume.restrict B).prod (law.prod law)) (trialCutoffHit n t r R Creg S (y i) (z i) v B w ω))≤
      2*ENNReal.ofReal (hitConstant*(8*Creg*t*r*(ε⁻¹^3+(m:ℝ))+8*r*(1+R)^3/Real.sqrt (h/2))) := by
  classical
  apply (Finset.sum_le_sum (fun i _ ↦ trialCutoffHit_le (y i) (z i) v B w ω hBv hreg.2 (hy i) (hz i))).trans
  rw [Finset.sum_add_distrib]
  have h₁ := physical_leg_collision hn y v (configurationPrefix 1 L midpointTime ω) hL ht hr hr1
    (by norm_num : (0:ℝ)≤13) hε hR (by positivity : 0≤2*Creg) hh hsepY
    (prefix_mesh_regular hr.le ω hreg.1) hsmall hτr hnscale hwindow hlarge hdrift hBm hB hBY
  have h₂ := physical_leg_collision hn z v (configurationPrefix 1 L midpointTime (reverseConfigurationPath 1 L ω)) hL ht hr hr1
    (by norm_num : (0:ℝ)≤13) hε hR (by positivity : 0≤2*Creg) hh hsepZ
    (prefix_mesh_regular hr.le _ ((meshRegular_reverse _ _ _ _ _).mpr hreg.1)) hsmall hτr hnscale hwindow hlarge hdrift hBm hB hBZ
  rw [hw]
  convert add_le_add h₁ h₂ using 1
  all_goals try with_reducible_and_instances rfl
  ring_nf

end HardSphere.Bridge

end
end

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Bridges_PhysicalSuccess
attribute [-instance] _root_.OAI.HardSphere.Bridge.exposedBridgeKernel_markov _root_.OAI.HardSphere.Bridge.exposedPeriodSingle_finite _root_.OAI.HardSphere.Bridge.exposedTrialKernel_markov _root_.OAI.HardSphere.Bridge.instIsProbabilityMeasurePointMidpointNoise _root_.OAI.HardSphere.Bridge.parameterBridgeKernel_markov _root_.OAI.HardSphere.Bridge.parameterIndividualReference_finite _root_.OAI.HardSphere.Bridge.parameterTrialKernel_markov _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Bridge.targetUniform_finite _root_.OAI.HardSphere.Comparison.parameterTargetKernel_finite _root_.OAI.HardSphere.Groups.cellPathReference_probability _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Rescaling.config_haar _root_.OAI.HardSphere.bridgeEndpointBase_finite _root_.OAI.HardSphere.endpointWeightedBase_sfinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.Bridge
open Wiener GaussianPacking PathCutoff
attribute [local irreducible] torusDistance

lemma trialCollision_closed {L : Length} (r : ℝ) (ω : ConfigurationPath 1 L) :
    IsClosed {f | TrialCollision r ω f} := by
  let E : Set (C(Time,Point)×Time) := {p | torusDistance L (projectPoint L (p.1 p.2)) (ω p.2 0) ≤ r}
  have hE : IsClosed E := by
    apply isClosed_le _ continuous_const
    apply (torusDistance_continuous_pair L).comp (f := fun p : C(Time,Point)×Time ↦
      (projectPoint L (p.1 p.2),ω p.2 0))
    apply Continuous.prodMk
    · change Continuous (fun p : C(Time,Point)×Time ↦ fun j : Fin 3 ↦ (p.1 p.2 j:AddCircle L.val))
      fun_prop
    · exact (continuous_apply 0).comp (ω.continuous.comp continuous_snd)
  convert isClosedMap_fst_of_compactSpace E hE using 1
  all_goals try with_reducible_and_instances rfl
  ext f
  simp only [TrialCollision,mem_ofPred_eq,mem_image,E]
  exact ⟨fun ⟨s,hs⟩ ↦ ⟨(f,s),hs,rfl⟩,fun ⟨⟨g,s⟩,hs,hg⟩ ↦ by
    change g=f at hg
    subst g
    exact ⟨s,hs⟩⟩

lemma trialCutoffHit_measurable {L : Length} (n : ℕ) (t r R C S : ℝ) (y z v : Point)
    {B : Set Point} (hB : MeasurableSet B) (w : Time) (ω : ConfigurationPath 1 L) :
    MeasurableSet (trialCutoffHit n t r R C S y z v B w ω) := by
  have hm := (trialPath_continuous t y z).measurable
  exact (hB.preimage measurable_fst).inter
    (((trialCutoff_measurable L n r R C w S v).preimage hm).inter
      ((trialCollision_closed r ω).measurableSet.preimage hm))

lemma trialCutoffHit_integral {L : Length} (n : ℕ) (t r R C S : ℝ) (y z v : Point)
    {B : Set Point} (hB : MeasurableSet B) (w : Time) (ω : ConfigurationPath 1 L) :
    (∫⁻u in B,trialKernel t y z u {f | TrialCutoff L n r R C w S v f ∧ TrialCollision r ω f})=
      ((volume.restrict B).prod (law.prod law)) (trialCutoffHit n t r R C S y z v B w ω) := by
  rw [Measure.prod_apply (trialCutoffHit_measurable n t r R C S y z v hB w ω)]
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_mem hB] with u hu
  have hm : Measurable (trialPath t y z u) := ((trialPath_continuous t y z).comp (continuous_const.prodMk continuous_id)).measurable
  have hA : MeasurableSet {f | TrialCutoff L n r R C w S v f ∧ TrialCollision r ω f} :=
    (trialCutoff_measurable L n r R C w S v).inter (trialCollision_closed r ω).measurableSet
  rw [trialKernel_apply,Measure.map_apply hm hA]
  congr 1
  ext β
  simp only [mem_preimage,mem_ofPred_eq,trialCutoffHit,TrialCollision,hu,true_and]

end HardSphere.Bridge

end
end

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.Bridge
open Wiener GaussianPacking PathCutoff

lemma physical_trial_collision_fintype {L : Length} {ι : Type*} [Fintype ι] {n : ℕ} (hn : 0<n)
    (y z : ι→Point) (v : Point) (ω : ConfigurationPath 1 L)
    {t r ε h R Creg S : ℝ} (w : Time)
    (hL : 50<L.val) (ht : 0<t) (hr : 0 < r) (hr1 : r≤1) (hε : 0<ε)
    (hR : 0≤R) (hCreg : 0≤Creg) (hh : 0<h) (hw : (w:ℝ)=h/t)
    (hsepY : ∀i j,i≠j → ε^2≤ square (y i-y j))
    (hsepZ : ∀i j,i≠j → ε^2≤ square (z i-z j))
    (hreg : Regular (n+n) r R Creg (prefixTime midpointTime w) S ω) (hsmall : r*R≤1)
    (hτr : t/(n:ℝ) ≤ r^2) (hnscale : (n:ℝ)*r^2≤2*t)
    (hwindow : 2*(t/(n:ℝ))≤h) (hlarge : 8*t≤(n:ℝ)*h) (hdrift : 2*13/(n:ℝ) ≤ r)
    {B : Set Point} (hBm : MeasurableSet B) (hB : (volume : Measure Point) B≤1)
    (hBv : ∀u∈B,‖u-v‖≤3)
    (hBY : ∀i u,u∈B → ‖u-y i‖≤13) (hBZ : ∀i u,u∈B → ‖u-z i‖≤13)
    (hy : ∀i,r+2*S<torusDistance L (projectPoint L (y i)) (ω 0 0))
    (hz : ∀i,r+2*S<torusDistance L (projectPoint L (z i)) (ω 1 0)) :
    (∑i,((volume.restrict B).prod (law.prod law)) (trialCutoffHit n t r R Creg S (y i) (z i) v B w ω))≤
      2*ENNReal.ofReal (hitConstant*(8*Creg*t*r*(ε⁻¹^3+(Fintype.card ι:ℝ))+8*r*(1+R)^3/Real.sqrt (h/2))) := by
  classical
  let e := (Fintype.equivFin ι).symm
  have hp := physical_trial_collision hn (fun i ↦ y (e i)) (fun i ↦ z (e i)) v ω w hL ht hr hr1 hε
    hR hCreg hh hw (fun i j hij ↦ hsepY (e i) (e j) (e.injective.ne hij))
    (fun i j hij ↦ hsepZ (e i) (e j) (e.injective.ne hij)) hreg hsmall hτr hnscale hwindow hlarge hdrift
    hBm hB hBv (fun i ↦ hBY (e i)) (fun i ↦ hBZ (e i)) (fun i ↦ hy (e i)) (fun i ↦ hz (e i))
  let f : ι → ℝ≥0∞ := fun i ↦ ((volume.restrict B).prod (law.prod law))
    (trialCutoffHit n t r R Creg S (y i) (z i) v B w ω)
  change (∑ i, f (e i)) ≤ _ at hp
  rw [e.sum_comp] at hp
  exact hp

lemma physical_trial_collision_subset {L : Length} {m n : ℕ} (hn : 0<n) (I : Finset (Fin m))
    (y z : Fin m→Point) (v : Point) (ω : ConfigurationPath 1 L)
    {t r ε h R Creg S : ℝ} (w : Time)
    (hL : 50<L.val) (ht : 0<t) (hr : 0 < r) (hr1 : r≤1) (hε : 0<ε)
    (hR : 0≤R) (hCreg : 0≤Creg) (hh : 0<h) (hw : (w:ℝ)=h/t)
    (hsepY : ∀i j,i≠j → ε^2≤ square (y i-y j))
    (hsepZ : ∀i j,i≠j → ε^2≤ square (z i-z j))
    (hreg : Regular (n+n) r R Creg (prefixTime midpointTime w) S ω) (hsmall : r*R≤1)
    (hτr : t/(n:ℝ) ≤ r^2) (hnscale : (n:ℝ)*r^2≤2*t)
    (hwindow : 2*(t/(n:ℝ))≤h) (hlarge : 8*t≤(n:ℝ)*h) (hdrift : 2*13/(n:ℝ) ≤ r)
    {B : Set Point} (hBm : MeasurableSet B) (hB : (volume : Measure Point) B≤1)
    (hBv : ∀u∈B,‖u-v‖≤3)
    (hBY : ∀i u,u∈B → ‖u-y i‖≤13) (hBZ : ∀i u,u∈B → ‖u-z i‖≤13)
    (hy : ∀i∈I,r+2*S<torusDistance L (projectPoint L (y i)) (ω 0 0))
    (hz : ∀i∈I,r+2*S<torusDistance L (projectPoint L (z i)) (ω 1 0)) :
    (∑i∈I,((volume.restrict B).prod (law.prod law)) (trialCutoffHit n t r R Creg S (y i) (z i) v B w ω))≤
      2*ENNReal.ofReal (hitConstant*(8*Creg*t*r*(ε⁻¹^3+(m:ℝ))+8*r*(1+R)^3/Real.sqrt (h/2))) := by
  classical
  have hp := physical_trial_collision_fintype (ι:=I) hn (fun i ↦ y i) (fun i ↦ z i) v ω w hL ht hr hr1 hε
    hR hCreg hh hw (fun i j hij ↦ hsepY i j (fun he ↦ hij (Subtype.ext he)))
    (fun i j hij ↦ hsepZ i j (fun he ↦ hij (Subtype.ext he))) hreg hsmall hτr hnscale hwindow hlarge hdrift
    hBm hB hBv (fun i ↦ hBY i) (fun i ↦ hBZ i) (fun i ↦ hy i i.property) (fun i ↦ hz i i.property)
  let f : Fin m → ℝ≥0∞ := fun i ↦ ((volume.restrict B).prod (law.prod law))
    (trialCutoffHit n t r R Creg S (y i) (z i) v B w ω)
  change (∑ i : I, f i) ≤ _ at hp
  rw [Fintype.card_coe,Finset.sum_coe_sort] at hp
  apply hp.trans
  apply mul_le_mul_right
  apply ENNReal.ofReal_le_ofReal
  have hcard : (I.card:ℝ) ≤ m := by exact_mod_cast (Finset.card_le_card (Finset.subset_univ I)).trans_eq (by simp)
  have hk := hitConstant_pos.le
  gcongr

end HardSphere.Bridge

end
end

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Bridges_SupplyIntegral
attribute [-instance] _root_.OAI.HardSphere.Bridge.exposedBridgeKernel_markov _root_.OAI.HardSphere.Bridge.exposedPeriodSingle_finite _root_.OAI.HardSphere.Bridge.exposedTrialKernel_markov _root_.OAI.HardSphere.Bridge.instIsProbabilityMeasurePointMidpointNoise _root_.OAI.HardSphere.Bridge.parameterBridgeKernel_markov _root_.OAI.HardSphere.Bridge.parameterIndividualReference_finite _root_.OAI.HardSphere.Bridge.parameterTrialKernel_markov _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Bridge.targetUniform_finite _root_.OAI.HardSphere.Comparison.parameterTargetKernel_finite _root_.OAI.HardSphere.Groups.cellPathReference_probability _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Rescaling.config_haar _root_.OAI.HardSphere.bridgeEndpointBase_finite _root_.OAI.HardSphere.endpointWeightedBase_sfinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.Bridge
open Wiener GaussianPacking PathCutoff
attribute [local irreducible] torusDistance
attribute [local instance] Classical.propDecidable

lemma trial_no_collision_far {L : Length} {n : ℕ} {r R C S : ℝ} {w : Time} {v : Point}
    {f : C(Time,Point)} (hf : TrialCutoff L n r R C w S v f) (hr : r≤1)
    (ω : ConfigurationPath 1 L) (hω : ∀s,12<torusDistance L (ω s 0) (projectPoint L v)) :
    ¬TrialCollision r ω f := by
  rintro ⟨s,hs⟩
  have htri := torusDistance_triangle' L (ω s 0) (projectPoint L (f s)) (projectPoint L v)
  have hd := (hf.2 s).2
  rw [torusDistance_comm L (ω s 0) (projectPoint L (f s))] at htri
  linarith [hω s]

lemma failure_except_le {L : Length} {N : ℕ} (n : ℕ) (t r R C S : ℝ)
    (w : Time) (y z v u : Point) (ω : Fin N → ConfigurationPath 1 L) (i : Fin N)
    (J : Finset (Fin N)) (hfar : ∀j,j∉J → ∀f,TrialCutoff L n r R C w S v f → ¬TrialCollision r (ω j) f) :
    trialKernel t y z u (SuccessExcept n r R C S w v ω i)ᶜ≤
      trialKernel t y z u {f | ¬TrialCutoff L n r R C w S v f}+
      ∑j∈J, if j=i then 0 else trialKernel t y z u {f | TrialCutoff L n r R C w S v f ∧ TrialCollision r (ω j) f} := by
  let E := fun j ↦ if j=i then (∅ : Set C(Time,Point)) else {f | TrialCutoff L n r R C w S v f ∧ TrialCollision r (ω j) f}
  have hsub : (SuccessExcept n r R C S w v ω i)ᶜ⊆
      {f | ¬TrialCutoff L n r R C w S v f} ∪ ⋃j∈J,E j := by
    intro f hf
    by_cases hc : TrialCutoff L n r R C w S v f
    · right
      have hh : ¬∀j,j≠i → ¬TrialCollision r (ω j) f := fun h ↦ hf ⟨hc,h⟩
      push Not at hh
      obtain ⟨j,hji,hj⟩ := hh
      have hJ : j∈J := by by_contra hn; exact hfar j hn f hc hj
      exact mem_iUnion.mpr ⟨j,mem_iUnion.mpr ⟨hJ,by simp [E,hji,hc,hj]⟩⟩
    · exact Or.inl hc
  apply (measure_mono hsub).trans
  apply (measure_union_le _ _).trans
  apply add_le_add le_rfl
  have h := measure_biUnion_finset_le J E (μ:=trialKernel t y z u)
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  funext index
  by_cases hji : index=i <;> simp [E,hji]

lemma failure_integral_sum {L : Length} {N m : ℕ} (n : ℕ) (t r R C S : ℝ) (w : Time)
    (y z : Fin m → Point) (v : Point) (ω : Fin N → ConfigurationPath 1 L) (label : Fin m → Fin N)
    (J : Finset (Fin N)) {B : Set Point} (hB : MeasurableSet B) (hBvol : volume B≤1)
    (hfar : ∀j,j∉J → ∀f,TrialCutoff L n r R C w S v f → ¬TrialCollision r (ω j) f)
    (δ ζ : ℝ≥0∞)
    (hcut : ∀i u,u∈B → trialKernel t (y i) (z i) u {f | ¬TrialCutoff L n r R C w S v f}≤δ)
    (hhit : ∀j∈J, (∑i∈Finset.univ.filter (fun i ↦ j≠label i),
      ((volume.restrict B).prod (law.prod law)) (trialCutoffHit n t r R C S (y i) (z i) v B w (ω j)))≤ζ) :
    (∑i,∫⁻u in B,trialKernel t (y i) (z i) u (SuccessExcept n r R C S w v ω (label i))ᶜ)≤
      (m:ℝ≥0∞)*δ+(J.card:ℝ≥0∞)*ζ := by
  classical
  let H := fun i j ↦ ((volume.restrict B).prod (law.prod law))
      (trialCutoffHit n t r R C S (y i) (z i) v B w (ω j))
  have hi (i : Fin m) : (∫⁻u in B,trialKernel t (y i) (z i) u (SuccessExcept n r R C S w v ω (label i))ᶜ)≤
      δ+∑j∈J,if j=label i then 0 else H i j := by
    apply (lintegral_mono fun u ↦ failure_except_le n t r R C S w (y i) (z i) v u ω (label i) J hfar).trans
    have hcm : MeasurableSet {f | ¬TrialCutoff L n r R C w S v f} := (trialCutoff_measurable L n r R C w S v).compl
    rw [lintegral_add_left ((trialKernel t (y i) (z i)).measurable_coe hcm)]
    apply add_le_add
    · calc
        _ ≤ ∫⁻_ in B,δ := lintegral_mono_ae (by filter_upwards [ae_restrict_mem hB] with u hu using hcut i u hu)
        _ = δ*volume B := by simp
        _ ≤ δ := by simpa using mul_le_mul_right hBvol δ
    · rw [lintegral_finsetSum' J]
      · apply Finset.sum_le_sum
        intro j hj
        by_cases hji : j=label i
        · simp [hji]
        · simp only [hji,ite_false]
          exact le_of_eq (trialCutoffHit_integral n t r R C S (y i) (z i) v hB w (ω j))
      · intro j hj
        by_cases hji : j=label i
        · simp only [hji,ite_true]; exact measurable_const.aemeasurable
        · simp only [hji,ite_false]
          exact ((trialKernel t (y i) (z i)).measurable_coe
            ((trialCutoff_measurable L n r R C w S v).inter (trialCollision_closed r (ω j)).measurableSet)).aemeasurable
  apply (Finset.sum_le_sum (fun i _ ↦ hi i)).trans
  rw [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Finset.sum_comm]
  apply add_le_add le_rfl
  calc
    _ = ∑j∈J,∑i∈Finset.univ.filter (fun i ↦ j≠label i),H i j := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro i _
      by_cases hji : j=label i <;> simp [hji]
    _ ≤ ∑_j∈J,ζ := Finset.sum_le_sum (fun j hj ↦ hhit j hj)
    _ = _ := by simp [nsmul_eq_mul]

lemma physical_failure_sum_oai {L : Length} {N m n : ℕ} (hn : 0<n)
    (y z : Fin m → Point) (v : Point) (ω : Fin N → ConfigurationPath 1 L)
    (label : Fin m → Fin N) (J : Finset (Fin N))
    {t r ε h R C S : ℝ} (w : Time)
    (hL : 50<L.val) (ht : 0<t) (hr : 0 < r) (hr1 : r≤1) (hε : 0<ε)
    (hR : 0≤R) (hC : 0≤C) (hh : 0<h) (hw : (w:ℝ)=h/t)
    (hsepY : ∀i j,i≠j → ε^2≤ square (y i-y j))
    (hsepZ : ∀i j,i≠j → ε^2≤ square (z i-z j))
    (hreg : ∀j∈J,Regular (n+n) r R C (prefixTime midpointTime w) S (ω j))
    (hsmall : r*R≤1) (hτr : t/(n:ℝ) ≤ r^2) (hnscale : (n:ℝ)*r^2≤2*t)
    (hwindow : 2*(t/(n:ℝ))≤h) (hlarge : 8*t≤(n:ℝ)*h) (hdrift : 2*13/(n:ℝ) ≤ r)
    {B : Set Point} (hB : MeasurableSet B) (hBvol : volume B≤1)
    (hBv : ∀u∈B,‖u-v‖≤3)
    (hBY : ∀i u,u∈B → ‖u-y i‖≤13) (hBZ : ∀i u,u∈B → ‖u-z i‖≤13)
    (hy : ∀j∈J,∀i,j≠label i → r+2*S<torusDistance L (projectPoint L (y i)) (ω j 0 0))
    (hz : ∀j∈J,∀i,j≠label i → r+2*S<torusDistance L (projectPoint L (z i)) (ω j 1 0))
    (hfar : ∀j,j∉J → ∀s,12<torusDistance L (ω j s 0) (projectPoint L v))
    (δ : ℝ≥0∞)
    (hcut : ∀i u,u∈B → trialKernel t (y i) (z i) u {f | ¬TrialCutoff L n r R C w S v f}≤δ) :
    (∑i,∫⁻u in B,trialKernel t (y i) (z i) u (SuccessExcept n r R C S w v ω (label i))ᶜ)≤
      (m:ℝ≥0∞)*δ+(J.card:ℝ≥0∞)*(2*ENNReal.ofReal
        (hitConstant*(8*C*t*r*(ε⁻¹^3+(m:ℝ))+8*r*(1+R)^3/Real.sqrt (h/2)))) := by
  refine failure_integral_sum n t r R C S w y z v ω label J hB hBvol
    (fun j hj f hf ↦ trial_no_collision_far hf hr1 (ω j) (hfar j hj)) δ _ hcut ?_
  intro j hj
  apply physical_trial_collision_subset hn (Finset.univ.filter (fun i ↦ j≠label i)) y z v (ω j) w
    hL ht hr hr1 hε hR hC hh hw hsepY hsepZ (hreg j hj) hsmall hτr hnscale hwindow hlarge hdrift
    hB hBvol hBv hBY hBZ
  · exact fun i hi ↦ hy j hj i (Finset.mem_filter.mp hi).2
  · exact fun i hi ↦ hz j hj i (Finset.mem_filter.mp hi).2

end HardSphere.Bridge

end
end

end

end OAI
end

theorem solution : type_of% @OAI.HardSphere.Bridge.physical_failure_sum_oai := @OAI.HardSphere.Bridge.physical_failure_sum_oai
