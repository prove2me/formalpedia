-- Prove2me | solution 1 for OAI.HardSphere.Groups.canonical_supply_counts
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T20:08:07.981701+00:00
-- url     : https://prove2.me/submissions/a4558953-4eb5-45cc-9bf4-624d81b600ee

import Mathlib
import Definitions.Def_HardSphere
import Definitions.Def_OAIQ054H002
import Theorems.Thm_OAI_HardSphere_Bridge_physical_failure_sum

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

lemma prefix_wiener_law (u : Time) : wiener.map (prefixMap u)=wiener.map (fun w ↦ Real.sqrt (u:ℝ) • w) := by
  rw [wiener,Measure.map_map (prefixMap u).continuous.measurable measurable_path,
    Measure.map_map (by fun_prop) measurable_path]
  exact prefix_law u

end HardSphere.Wiener

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Bridges_GaussianDensity
attribute [-instance] _root_.OAI.HardSphere.Groups.labelOptionSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory MeasureTheory.Measure Set Filter ProbabilityTheory
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.GaussianPacking

lemma packingConstant_pos : 0<packingConstant := by unfold packingConstant; positivity

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
namespace HardSphere.Bridge
open Wiener GaussianPacking

lemma leg_continuous (t : ℝ) (y u : Point) : Continuous (leg t y u) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  change Continuous (fun p : Noise×Time ↦ fun j ↦ mean y u p.2 j+Real.sqrt (2*t)*p.1 j p.2)
  unfold mean
  fun_prop

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
attribute [-instance] _root_.OAI.HardSphere.Bridge.exposedBridgeKernel_markov _root_.OAI.HardSphere.Bridge.exposedPeriodSingle_finite _root_.OAI.HardSphere.Bridge.exposedTrialKernel_markov _root_.OAI.HardSphere.Bridge.parameterBridgeKernel_markov _root_.OAI.HardSphere.Bridge.parameterIndividualReference_finite _root_.OAI.HardSphere.Bridge.parameterTrialKernel_markov _root_.OAI.HardSphere.Groups.cellPathReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite
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

end HardSphere.Wiener

namespace HardSphere.Bridge
open Wiener GaussianPacking

lemma incrementSize_nonneg (s u : Time) (β : Noise) : 0 ≤ incrementSize s u β := Finset.sum_nonneg (fun _ _ ↦ norm_nonneg _)
lemma incrementSize_continuous (s u : Time) : Continuous (incrementSize s u) := by unfold incrementSize; fun_prop
lemma incrementFluctuation_continuous (t r : ℝ) (s w : Time) : Continuous (incrementFluctuation t r s w) :=
  (incrementSize_continuous s w).const_mul _
lemma incrementFluctuation_nonneg {t r : ℝ} (hr : 0 ≤ r) (s w : Time) (β : Noise) : 0 ≤ incrementFluctuation t r s w β :=
  mul_nonneg (div_nonneg (Real.sqrt_nonneg _) hr) (incrementSize_nonneg s w β)

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

namespace HardSphere.Bridge
open Wiener GaussianPacking

lemma leg_segment_increment (t : ℝ) (y v : Point) (β : Noise) (s q : Time) (j : Fin 3) :
    leg t y v β (suffixTime s q) j=leg t y v β s j+
      ((1-(s:ℝ))*(q:ℝ))*(v j-y j)+Real.sqrt (2*t)*(β j (suffixTime s q)-β j s) := by
  simp only [leg,ContinuousMap.coe_mk,mean]
  dsimp [suffixTime]
  ring

end HardSphere.Bridge

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Bridges_SegmentSimplify
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
open Wiener GaussianPacking

lemma hitConstant_pos : 0<hitConstant := by
  have hn : 0≤normCubeMean := integral_nonneg (fun _ ↦ by positivity)
  have hk := packingConstant_pos
  unfold hitConstant
  positivity

end HardSphere.Bridge

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Bridges_NormalizedPrefix
attribute [-instance] _root_.OAI.HardSphere.Bridge.exposedBridgeKernel_markov _root_.OAI.HardSphere.Bridge.exposedPeriodSingle_finite _root_.OAI.HardSphere.Bridge.exposedTrialKernel_markov _root_.OAI.HardSphere.Bridge.instBorelSpaceContinuousMapElemRealTimePoint _root_.OAI.HardSphere.Bridge.instIsProbabilityMeasureNoiseLaw _root_.OAI.HardSphere.Bridge.instMeasurableSpaceContinuousMapElemRealTimePoint _root_.OAI.HardSphere.Bridge.parameterBridgeKernel_markov _root_.OAI.HardSphere.Bridge.parameterIndividualReference_finite _root_.OAI.HardSphere.Bridge.parameterTrialKernel_markov _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Bridge.trialKernel_markov _root_.OAI.HardSphere.Groups.cellPathReference_probability _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Rescaling.config_haar _root_.OAI.HardSphere.Wiener.bridgeLaw_isGaussian _root_.OAI.HardSphere.Wiener.wiener_isGaussian _root_.OAI.HardSphere.bridgeEndpointBase_finite _root_.OAI.HardSphere.coordinateBridge_probability _root_.OAI.HardSphere.endpointWeightedBase_sfinite _root_.OAI.HardSphere.freePathLaw_finite_deletion _root_.OAI.HardSphere.gaussianCoordinates_probability _root_.OAI.HardSphere.killedPathLaw_finite_deletion
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

lemma mesh_firstTime {m : ℕ} (hm : 0 < m) (s : Time) :
    meshTime (0:Fin (m+1)) s=prefixTime (splitTime 1 (m:ℝ) (by norm_num) (by exact_mod_cast hm)) s := by
  apply Subtype.ext
  simp only [meshTime,Fin.val_zero,Nat.cast_zero,zero_add,prefixTime,ContinuousMap.coe_mk,splitTime,Nat.cast_add,Nat.cast_one]
  ring

lemma mesh_nextTime {m : ℕ} (hm : 0 < m) (j : Fin m) (s : Time) :
    meshTime j.succ s=suffixTime (splitTime 1 (m:ℝ) (by norm_num) (by exact_mod_cast hm)) (meshTime j s) := by
  apply Subtype.ext
  have hm' : (m:ℝ)≠0 := by exact_mod_cast (Nat.ne_of_gt hm)
  have hm1 : (1:ℝ)+m≠0 := by positivity
  simp only [meshTime,Fin.val_succ,suffixTime,ContinuousMap.coe_mk,splitTime,Nat.cast_add,Nat.cast_one]
  field_simp
  ring

lemma meshSegment_first {m : ℕ} {L : Length} (hm : 0 < m) (ω : ConfigurationPath 1 L) :
    meshSegment (0:Fin (m+1)) ω=configurationPrefix 1 L (splitTime 1 (m:ℝ) (by norm_num) (by exact_mod_cast hm)) ω := by
  ext s i j
  exact congrArg (fun u : Time ↦ ω u i j) (mesh_firstTime hm s)

lemma meshSegment_next {m : ℕ} {L : Length} (hm : 0 < m) (j : Fin m) (ω : ConfigurationPath 1 L) :
    meshSegment j.succ ω=meshSegment j (configurationSuffix 1 L (splitTime 1 (m:ℝ) (by norm_num) (by exact_mod_cast hm)) ω) := by
  ext s i k
  exact congrArg (fun u : Time ↦ ω u i k) (mesh_nextTime hm j s)

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
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_KilledObservable
attribute [-instance] _root_.OAI.HardSphere.Bridge.exposedBridgeKernel_markov _root_.OAI.HardSphere.Bridge.exposedPeriodSingle_finite _root_.OAI.HardSphere.Bridge.exposedTrialKernel_markov _root_.OAI.HardSphere.Bridge.instBorelSpaceContinuousMapElemRealTimePoint _root_.OAI.HardSphere.Bridge.instIsProbabilityMeasureNoiseLaw _root_.OAI.HardSphere.Bridge.instMeasurableSpaceContinuousMapElemRealTimePoint _root_.OAI.HardSphere.Bridge.parameterBridgeKernel_markov _root_.OAI.HardSphere.Bridge.parameterIndividualReference_finite _root_.OAI.HardSphere.Bridge.parameterTrialKernel_markov _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Bridge.trialKernel_markov _root_.OAI.HardSphere.Groups.cellPathReference_probability _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Rescaling.config_haar _root_.OAI.HardSphere.Wiener.bridgeLaw_isGaussian _root_.OAI.HardSphere.Wiener.wiener_isGaussian _root_.OAI.HardSphere.bridgeEndpointBase_finite _root_.OAI.HardSphere.coordinateBridge_probability _root_.OAI.HardSphere.endpointWeightedBase_sfinite _root_.OAI.HardSphere.freePathLaw_finite_deletion _root_.OAI.HardSphere.gaussianCoordinates_probability _root_.OAI.HardSphere.killedPathLaw_finite_deletion
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
-- module Solutions.OAIQ054_HS.HardSphere_Cutoffs_MeshMoment
attribute [-instance] _root_.OAI.HardSphere.Bridge.exposedBridgeKernel_markov _root_.OAI.HardSphere.Bridge.exposedPeriodSingle_finite _root_.OAI.HardSphere.Bridge.exposedTrialKernel_markov _root_.OAI.HardSphere.Bridge.instBorelSpaceContinuousMapElemRealTimePoint _root_.OAI.HardSphere.Bridge.instIsProbabilityMeasureNoiseLaw _root_.OAI.HardSphere.Bridge.instMeasurableSpaceContinuousMapElemRealTimePoint _root_.OAI.HardSphere.Bridge.parameterBridgeKernel_markov _root_.OAI.HardSphere.Bridge.parameterIndividualReference_finite _root_.OAI.HardSphere.Bridge.parameterTrialKernel_markov _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Bridge.trialKernel_markov _root_.OAI.HardSphere.Groups.cellPathReference_probability _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Rescaling.config_haar _root_.OAI.HardSphere.Wiener.bridgeLaw_isGaussian _root_.OAI.HardSphere.Wiener.wiener_isGaussian _root_.OAI.HardSphere.bridgeEndpointBase_finite _root_.OAI.HardSphere.coordinateBridge_probability _root_.OAI.HardSphere.endpointWeightedBase_sfinite _root_.OAI.HardSphere.freePathLaw_finite_deletion _root_.OAI.HardSphere.gaussianCoordinates_probability _root_.OAI.HardSphere.killedPathLaw_finite_deletion
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

lemma meshProduct_measurable {L : Length} (m : ℕ) {F : ConfigurationPath 1 L → ℝ≥0∞}
    (hF : Measurable F) : Measurable (meshProduct m F) := by
  unfold meshProduct
  exact Finset.measurable_prod _ (fun j _ ↦ hF.comp (meshSegment_continuous L j).measurable)

lemma splitTime_mul {τ : ℝ} (hτ : 0<τ) {m : ℕ} (hm : 0 < m) :
    splitTime τ ((m:ℝ)*τ) hτ (mul_pos (by exact_mod_cast hm) hτ)=
      splitTime 1 (m:ℝ) (by norm_num) (by exact_mod_cast hm) := by
  apply Subtype.ext
  change τ/(τ+(m:ℝ)*τ)=1/(1+(m:ℝ))
  have hτ' := ne_of_gt hτ
  have hm' : (1:ℝ)+(m:ℝ)≠0 := by positivity
  field_simp

lemma meshProduct_succ {L : Length} {m : ℕ} (hm : 0 < m) (F : ConfigurationPath 1 L → ℝ≥0∞)
    {τ : ℝ} (hτ : 0<τ) (ω : ConfigurationPath 1 L) :
    meshProduct (m+1) F ω =
      F (configurationPrefix 1 L (splitTime τ ((m:ℝ)*τ) hτ (mul_pos (by exact_mod_cast hm) hτ)) ω)*
      meshProduct m F (configurationSuffix 1 L (splitTime τ ((m:ℝ)*τ) hτ (mul_pos (by exact_mod_cast hm) hτ)) ω) := by
  rw [splitTime_mul hτ hm]
  simp only [meshProduct,Fin.prod_univ_succ,meshSegment_first hm,meshSegment_next hm]

lemma meshProduct_free_bound {L : Length} (F : ConfigurationPath 1 L → ℝ≥0∞) (hF : Measurable F)
    {τ : ℝ} (hτ : 0<τ) (B : ℝ≥0∞)
    (hB : ∀ X : Configuration 1 L, ∫⁻w,F (freeTrajectory 1 L τ w X) ∂coordinateWiener 1 ≤ B) :
    ∀ m : ℕ, 0 < m → ∀ X : Configuration 1 L,
      ∫⁻w, meshProduct m F (freeTrajectory 1 L ((m:ℝ)*τ) w X) ∂coordinateWiener 1 ≤ B^m := by
  intro m hm
  induction m, hm using Nat.le_induction with
  | base => simpa using hB
  | succ m hm ih =>
    intro X
    let u := splitTime τ ((m:ℝ)*τ) hτ (mul_pos (by exact_mod_cast hm) hτ)
    let G : CoordinatePaths 1 × CoordinatePaths 1 → ℝ≥0∞ := fun w ↦
      F (freeTrajectory 1 L τ w.1 X) *
      meshProduct m F (freeTrajectory 1 L ((m:ℝ)*τ) w.2 (freeTrajectory 1 L τ w.1 X 1))
    have hfirst : Measurable (fun w : CoordinatePaths 1 × CoordinatePaths 1 ↦ F (freeTrajectory 1 L τ w.1 X)) :=
      hF.comp ((freeTrajectory_continuous 1 L τ).comp (continuous_fst.prodMk continuous_const)).measurable
    have hsecond : Measurable (fun w : CoordinatePaths 1 × CoordinatePaths 1 ↦
        meshProduct m F (freeTrajectory 1 L ((m:ℝ)*τ) w.2 (freeTrajectory 1 L τ w.1 X 1))) :=
      (meshProduct_measurable m hF).comp
        (measurable_snd.comp (split_fixedTrajectory_measurable 1 L τ ((m:ℝ)*τ) X))
    have hG : Measurable G := hfirst.mul hsecond
    have he (w : CoordinatePaths 1) :
        meshProduct (m+1) F (freeTrajectory 1 L (((m+1:ℕ):ℝ)*τ) w X)=
        G (fun p ↦ normalizedPrefix u (w p), fun p ↦ normalizedSuffix u (w p)) := by
      have hmul : (((m+1:ℕ):ℝ)*τ)=τ+(m:ℝ)*τ := by push_cast; ring
      rw [hmul,meshProduct_succ hm F hτ]
      have hp := congrArg Prod.fst (split_fixedTrajectory 1 L τ ((m:ℝ)*τ) hτ (mul_pos (by exact_mod_cast hm) hτ) w X)
      have hq := congrArg Prod.snd (split_fixedTrajectory 1 L τ ((m:ℝ)*τ) hτ (mul_pos (by exact_mod_cast hm) hτ) w X)
      dsimp only [Prod.fst,Prod.snd] at hp hq
      rw [hp,hq]
    calc
      _ = ∫⁻w,G (fun p ↦ normalizedPrefix u (w p),fun p ↦ normalizedSuffix u (w p)) ∂coordinateWiener 1 := lintegral_congr he
      _ = ∫⁻w,G w ∂(coordinateWiener 1).prod (coordinateWiener 1) :=
        (coordinateSplit_preserving 1 u (splitTime_pos _ _ _ _) (splitTime_lt_one _ _ _ _)).lintegral_comp hG
      _ = ∫⁻w₁,∫⁻w₂,G (w₁,w₂) ∂coordinateWiener 1 ∂coordinateWiener 1 := lintegral_prod _ hG.aemeasurable
      _ ≤ ∫⁻w₁,F (freeTrajectory 1 L τ w₁ X)*B^m ∂coordinateWiener 1 := by
        apply lintegral_mono
        intro w₁
        dsimp only [G]
        have hmeas : Measurable (fun w₂ : CoordinatePaths 1 ↦
            meshProduct m F (freeTrajectory 1 L ((m:ℝ)*τ) w₂ (freeTrajectory 1 L τ w₁ X 1))) :=
          (meshProduct_measurable m hF).comp
            ((freeTrajectory_continuous 1 L ((m:ℝ)*τ)).comp (continuous_id.prodMk continuous_const)).measurable
        rw [lintegral_const_mul _ hmeas]
        exact mul_le_mul_right (ih _) _
      _ = (∫⁻w₁,F (freeTrajectory 1 L τ w₁ X) ∂coordinateWiener 1)*B^m :=
        lintegral_mul_const _ (hF.comp ((freeTrajectory_continuous 1 L τ).comp (continuous_id.prodMk continuous_const)).measurable)
      _ ≤ B*B^m := mul_le_mul_left (hB X) _
      _ = B^(m+1) := by rw [pow_succ]; exact mul_comm _ _

end HardSphere.PathCutoff

namespace HardSphere.PathCutoff
open Wiener
attribute [local irreducible] torusDistance freeTrajectory

lemma meshSum_measurable {L : Length} (m : ℕ) {F : ConfigurationPath 1 L → ℝ≥0∞}
    (hF : Measurable F) : Measurable (meshSum m F) := by
  unfold meshSum
  exact Finset.measurable_sum _ (fun j _ ↦ hF.comp (meshSegment_continuous L j).measurable)

lemma meshSum_succ {L : Length} {m : ℕ} (hm : 0 < m) (F : ConfigurationPath 1 L → ℝ≥0∞)
    {τ : ℝ} (hτ : 0<τ) (ω : ConfigurationPath 1 L) :
    meshSum (m+1) F ω =
      F (configurationPrefix 1 L (splitTime τ ((m:ℝ)*τ) hτ (mul_pos (by exact_mod_cast hm) hτ)) ω)+
      meshSum m F (configurationSuffix 1 L (splitTime τ ((m:ℝ)*τ) hτ (mul_pos (by exact_mod_cast hm) hτ)) ω) := by
  rw [splitTime_mul hτ hm]
  simp only [meshSum,Fin.sum_univ_succ,meshSegment_first hm,meshSegment_next hm]

lemma meshSum_free_bound {L : Length} (F : ConfigurationPath 1 L → ℝ≥0∞) (hF : Measurable F)
    {τ : ℝ} (hτ : 0<τ) (B : ℝ≥0∞)
    (hB : ∀ X : Configuration 1 L, ∫⁻w,F (freeTrajectory 1 L τ w X) ∂coordinateWiener 1 ≤ B) :
    ∀ m : ℕ, 0 < m → ∀ X : Configuration 1 L,
      ∫⁻w, meshSum m F (freeTrajectory 1 L ((m:ℝ)*τ) w X) ∂coordinateWiener 1 ≤ (m:ℝ≥0∞)*B := by
  intro m hm
  induction m, hm using Nat.le_induction with
  | base => simpa using hB
  | succ m hm ih =>
    intro X
    let u := splitTime τ ((m:ℝ)*τ) hτ (mul_pos (by exact_mod_cast hm) hτ)
    let G : CoordinatePaths 1 × CoordinatePaths 1 → ℝ≥0∞ := fun w ↦
      F (freeTrajectory 1 L τ w.1 X) +
      meshSum m F (freeTrajectory 1 L ((m:ℝ)*τ) w.2 (freeTrajectory 1 L τ w.1 X 1))
    have hfirst : Measurable (fun w : CoordinatePaths 1 × CoordinatePaths 1 ↦ F (freeTrajectory 1 L τ w.1 X)) :=
      hF.comp ((freeTrajectory_continuous 1 L τ).comp (continuous_fst.prodMk continuous_const)).measurable
    have hsecond : Measurable (fun w : CoordinatePaths 1 × CoordinatePaths 1 ↦
        meshSum m F (freeTrajectory 1 L ((m:ℝ)*τ) w.2 (freeTrajectory 1 L τ w.1 X 1))) :=
      (meshSum_measurable m hF).comp
        (measurable_snd.comp (split_fixedTrajectory_measurable 1 L τ ((m:ℝ)*τ) X))
    have hG : Measurable G := hfirst.add hsecond
    have he (w : CoordinatePaths 1) :
        meshSum (m+1) F (freeTrajectory 1 L (((m+1:ℕ):ℝ)*τ) w X)=
        G (fun p ↦ normalizedPrefix u (w p), fun p ↦ normalizedSuffix u (w p)) := by
      have hmul : (((m+1:ℕ):ℝ)*τ)=τ+(m:ℝ)*τ := by push_cast; ring
      rw [hmul,meshSum_succ hm F hτ]
      have hp := congrArg Prod.fst (split_fixedTrajectory 1 L τ ((m:ℝ)*τ) hτ (mul_pos (by exact_mod_cast hm) hτ) w X)
      have hq := congrArg Prod.snd (split_fixedTrajectory 1 L τ ((m:ℝ)*τ) hτ (mul_pos (by exact_mod_cast hm) hτ) w X)
      dsimp only [Prod.fst,Prod.snd] at hp hq
      rw [hp,hq]
    calc
      _ = ∫⁻w,G (fun p ↦ normalizedPrefix u (w p),fun p ↦ normalizedSuffix u (w p)) ∂coordinateWiener 1 := lintegral_congr he
      _ = ∫⁻w,G w ∂(coordinateWiener 1).prod (coordinateWiener 1) :=
        (coordinateSplit_preserving 1 u (splitTime_pos _ _ _ _) (splitTime_lt_one _ _ _ _)).lintegral_comp hG
      _ = ∫⁻w₁,∫⁻w₂,G (w₁,w₂) ∂coordinateWiener 1 ∂coordinateWiener 1 := lintegral_prod _ hG.aemeasurable
      _ ≤ ∫⁻w₁,F (freeTrajectory 1 L τ w₁ X)+(m:ℝ≥0∞)*B ∂coordinateWiener 1 := by
        apply lintegral_mono
        intro w₁
        dsimp only [G]
        have hmeas : Measurable (fun w₂ : CoordinatePaths 1 ↦
            meshSum m F (freeTrajectory 1 L ((m:ℝ)*τ) w₂ (freeTrajectory 1 L τ w₁ X 1))) :=
          (meshSum_measurable m hF).comp
            ((freeTrajectory_continuous 1 L ((m:ℝ)*τ)).comp (continuous_id.prodMk continuous_const)).measurable
        rw [lintegral_add_left measurable_const,lintegral_const,measure_univ,mul_one]
        exact add_le_add le_rfl (ih _)
      _ = (∫⁻w₁,F (freeTrajectory 1 L τ w₁ X) ∂coordinateWiener 1)+(m:ℝ≥0∞)*B := by
        have hmeas : Measurable (fun w : CoordinatePaths 1 ↦ F (freeTrajectory 1 L τ w X)) := hF.comp ((freeTrajectory_continuous 1 L τ).comp (continuous_id.prodMk continuous_const)).measurable
        rw [lintegral_add_left hmeas,lintegral_const,measure_univ,mul_one]
      _ ≤ B+(m:ℝ≥0∞)*B := add_le_add (hB X) le_rfl
      _ = ((m+1:ℕ):ℝ≥0∞)*B := by push_cast; ring

end HardSphere.PathCutoff

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_PathBounds_VisitPacking
attribute [-instance] _root_.OAI.HardSphere.Bridge.exposedBridgeKernel_markov _root_.OAI.HardSphere.Bridge.exposedPeriodSingle_finite _root_.OAI.HardSphere.Bridge.exposedTrialKernel_markov _root_.OAI.HardSphere.Bridge.instBorelSpaceContinuousMapElemRealTimePoint _root_.OAI.HardSphere.Bridge.instIsProbabilityMeasureNoiseLaw _root_.OAI.HardSphere.Bridge.instMeasurableSpaceContinuousMapElemRealTimePoint _root_.OAI.HardSphere.Bridge.parameterBridgeKernel_markov _root_.OAI.HardSphere.Bridge.parameterIndividualReference_finite _root_.OAI.HardSphere.Bridge.parameterTrialKernel_markov _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Bridge.trialKernel_markov _root_.OAI.HardSphere.Groups.cellPathReference_probability _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Rescaling.config_haar _root_.OAI.HardSphere.Wiener.bridgeLaw_isGaussian _root_.OAI.HardSphere.Wiener.wiener_isGaussian _root_.OAI.HardSphere.bridgeEndpointBase_finite _root_.OAI.HardSphere.coordinateBridge_probability _root_.OAI.HardSphere.endpointWeightedBase_sfinite _root_.OAI.HardSphere.freePathLaw_finite_deletion _root_.OAI.HardSphere.killedPathLaw_finite_deletion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology BigOperators

namespace HardSphere.FreeVisits
open HardSphere.BathSlice HardSphere.Lattice HardSphere.CellOrbital HardSphere.Wiener

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

end HardSphere.FreeVisits

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_PathBounds_FreeVisitTravel
attribute [-instance] _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Rescaling.config_haar _root_.OAI.HardSphere.bridgeEndpointBase_finite _root_.OAI.HardSphere.endpointWeightedBase_sfinite _root_.OAI.HardSphere.freePathLaw_finite_deletion _root_.OAI.HardSphere.killedPathLaw_finite_deletion
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

attribute [local irreducible] freeTrajectory pathVisitedSites torusDistance

end HardSphere.FreeVisits

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Cutoffs_MeshEvents
attribute [-instance] _root_.OAI.HardSphere.Bridge.exposedBridgeKernel_markov _root_.OAI.HardSphere.Bridge.exposedPeriodSingle_finite _root_.OAI.HardSphere.Bridge.exposedTrialKernel_markov _root_.OAI.HardSphere.Bridge.instBorelSpaceContinuousMapElemRealTimePoint _root_.OAI.HardSphere.Bridge.instIsProbabilityMeasureNoiseLaw _root_.OAI.HardSphere.Bridge.instMeasurableSpaceContinuousMapElemRealTimePoint _root_.OAI.HardSphere.Bridge.parameterBridgeKernel_markov _root_.OAI.HardSphere.Bridge.parameterIndividualReference_finite _root_.OAI.HardSphere.Bridge.parameterTrialKernel_markov _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Bridge.trialKernel_markov _root_.OAI.HardSphere.Groups.cellPathReference_probability _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Rescaling.config_haar _root_.OAI.HardSphere.Wiener.bridgeLaw_isGaussian _root_.OAI.HardSphere.bridgeEndpointBase_finite _root_.OAI.HardSphere.coordinateBridge_probability _root_.OAI.HardSphere.endpointWeightedBase_sfinite _root_.OAI.HardSphere.gaussianCoordinates_probability
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

lemma meshEvent_measurable {L : Length} (m : ℕ) {E : Set (ConfigurationPath 1 L)} (hE : MeasurableSet E) :
    MeasurableSet (meshEvent m E) := by
  simp only [meshEvent,ofPred_exists]
  exact MeasurableSet.iUnion (fun j ↦ hE.preimage (meshSegment_continuous L j).measurable)

lemma meshEvent_free_bound {L : Length} (m : ℕ) (hm : 0 < m) {E : Set (ConfigurationPath 1 L)}
    (hE : MeasurableSet E) {τ : ℝ} (hτ : 0<τ) (p : ℝ≥0∞)
    (hp : ∀ X : Configuration 1 L, coordinateWiener 1 {w | freeTrajectory 1 L τ w X ∈ E} ≤ p)
    (X : Configuration 1 L) :
    coordinateWiener 1 {w | freeTrajectory 1 L ((m:ℝ)*τ) w X ∈ meshEvent m E} ≤ (m:ℝ≥0∞)*p := by
  let F : ConfigurationPath 1 L → ℝ≥0∞ := E.indicator (fun _ ↦ 1)
  have hF : Measurable F := measurable_const.indicator hE
  have hB (Y : Configuration 1 L) : ∫⁻ w,F (freeTrajectory 1 L τ w Y) ∂coordinateWiener 1 ≤ p := by
    have hEv : MeasurableSet {w | freeTrajectory 1 L τ w Y ∈ E} :=
      hE.preimage ((freeTrajectory_continuous 1 L τ).comp (continuous_id.prodMk continuous_const)).measurable
    change ∫⁻ w,({w | freeTrajectory 1 L τ w Y ∈ E}.indicator (fun _ ↦ 1)) w ∂coordinateWiener 1 ≤ p
    simpa only [lintegral_indicator_const hEv,one_mul] using hp Y
  have hEv : MeasurableSet {w | freeTrajectory 1 L ((m:ℝ)*τ) w X ∈ meshEvent m E} :=
    (meshEvent_measurable m hE).preimage ((freeTrajectory_continuous 1 L ((m:ℝ)*τ)).comp (continuous_id.prodMk continuous_const)).measurable
  calc
    _ = ∫⁻w,({w | freeTrajectory 1 L ((m:ℝ)*τ) w X ∈ meshEvent m E}.indicator (fun _ ↦ (1:ℝ≥0∞))) w ∂coordinateWiener 1 :=
      by rw [lintegral_indicator_const hEv,one_mul]
    _ ≤ ∫⁻w,meshSum m F (freeTrajectory 1 L ((m:ℝ)*τ) w X) ∂coordinateWiener 1 := by
      apply lintegral_mono
      intro w
      by_cases hw : freeTrajectory 1 L ((m:ℝ)*τ) w X ∈ meshEvent m E
      · rw [Set.indicator_of_mem (show w ∈ {w | freeTrajectory 1 L ((m:ℝ)*τ) w X ∈ meshEvent m E} from hw)]
        obtain ⟨j,hj⟩ := hw
        have hle := Finset.single_le_sum (f := fun j : Fin m ↦ F (meshSegment j (freeTrajectory 1 L ((m:ℝ)*τ) w X)))
          (fun _ _ ↦ bot_le) (Finset.mem_univ j)
        simpa only [F,meshSum,Set.indicator_of_mem hj] using hle
      · rw [Set.indicator_of_notMem (show w ∉ {w | freeTrajectory 1 L ((m:ℝ)*τ) w X ∈ meshEvent m E} from hw)]
        exact bot_le
    _ ≤ (m:ℝ≥0∞)*p := meshSum_free_bound F hF hτ p hB m hm X

end HardSphere.PathCutoff

end
end

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators
namespace HardSphere.PathCutoff

lemma exp_cap_le {x B : ℝ} (hB : 0 < B) (hx : 0 ≤ x) :
    Real.exp (min x B/B)  ≤  1+(Real.exp 1-1)*x/B := by
  have h0 : 0 ≤ min x B/B := div_nonneg (le_min hx hB.le) hB.le
  have h1 : min x B/B ≤ 1 := (div_le_one hB).mpr (min_le_right _ _)
  have h := convexOn_exp.2 (Set.mem_univ (0:ℝ)) (Set.mem_univ (1:ℝ))
    (sub_nonneg.mpr h1) h0 (by ring : 1-min x B/B+min x B/B=1)
  simp only [smul_eq_mul,mul_zero,mul_one,zero_add,Real.exp_zero] at h
  calc
    Real.exp (min x B/B) ≤ 1+(Real.exp 1-1)*(min x B)/B := by
      convert h using 1
      all_goals try with_reducible_and_instances rfl
      ring
    _  ≤  1+(Real.exp 1-1)*x/B := by
      gcongr
      · exact sub_nonneg.mpr (by simp)
      · exact min_le_left _ _

lemma exp_cap_integral {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {X : Ω→ℝ} (hX : Integrable X μ) (hX0 : ∀ᵐω ∂μ,0 ≤ X ω) {B : ℝ} (hB : 0 < B) :
    ∫⁻ω, ENNReal.ofReal (Real.exp (min (X ω) B/B)) ∂μ  ≤
      ENNReal.ofReal (Real.exp ((Real.exp 1-1)*(∫ω,X ω ∂μ)/B)) := by
  have hi : Integrable (fun ω ↦ 1+(Real.exp 1-1)*X ω/B) μ :=
    (integrable_const 1).add ((hX.const_mul _).div_const _)
  calc
    _  ≤  ∫⁻ω,ENNReal.ofReal (1+(Real.exp 1-1)*X ω/B) ∂μ := by
      apply lintegral_mono_ae
      filter_upwards [hX0] with ω hω
      exact ENNReal.ofReal_le_ofReal (exp_cap_le hB hω)
    _ = ENNReal.ofReal (1+(Real.exp 1-1)*(∫ω,X ω ∂μ)/B) := by
      rw [←ofReal_integral_eq_lintegral_ofReal hi]
      · congr 1
        rw [integral_add (integrable_const _) ((hX.const_mul _).div_const _),integral_const,
          integral_div,integral_const_mul,probReal_univ,one_smul]
      · filter_upwards [hX0] with ω hω
        have he : 0 ≤ Real.exp 1-1 := sub_nonneg.mpr (by simp)
        positivity
    _  ≤  _ := ENNReal.ofReal_le_ofReal (by linarith [Real.add_one_le_exp ((Real.exp 1-1)*(∫ω,X ω ∂μ)/B)])

end HardSphere.PathCutoff

end
end

section
noncomputable section
open MeasureTheory Set Filter ProbabilityTheory
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.PathCutoff
open Wiener FreeVisits BathSlice
attribute [local irreducible] torusDistance freeTrajectory

lemma noiseSize_nonneg (w : CoordinatePaths 1) : 0 ≤ noiseSize w :=
  Finset.sum_nonneg (fun _ _ ↦ norm_nonneg _)
lemma noiseSize_coord (w : CoordinatePaths 1) (j : Fin 3) : ‖w (0,j)‖ ≤ noiseSize w :=
  by
    change ‖w (0,j)‖ ≤ ∑ i : Fin 3, ‖w (0,i)‖
    exact Finset.single_le_sum (fun i _ ↦ norm_nonneg (w (0,i))) (Finset.mem_univ j)

lemma free_diameter_le (L : Length) (t : ℝ) (w : CoordinatePaths 1) (y : Torus L) {R : ℝ}
    (hR : 0 ≤ R) (hw : ∀ j, ‖w (0,j)‖ ≤ R) :
    intervalDiameter 0 1 (freeTrajectory 1 L t w (oneConfiguration y)) ≤ 6*Real.sqrt (2*t)*R := by
  have hd (s : Time) : torusDistance L (freeTrajectory 1 L t w (oneConfiguration y) s 0) y ≤
      3*(Real.sqrt (2*t)*R) := by
    apply torusDistance_le_three_of_coord L _ _ (by positivity)
    intro j
    apply (freeTrajectory_coord_dist_le L t w (oneConfiguration y) 0 s j).trans
    exact mul_le_mul_of_nonneg_left (hw j) (Real.sqrt_nonneg _)
  apply intervalDiameter_le _ _ _ (by positivity)
  intro s q
  have htri := torusDistance_triangle' L
    (freeTrajectory 1 L t w (oneConfiguration y) (intervalTime 0 1 s) 0) y
    (freeTrajectory 1 L t w (oneConfiguration y) (intervalTime 0 1 q) 0)
  rw [torusDistance_comm L y] at htri
  linarith [hd (intervalTime 0 1 s), hd (intervalTime 0 1 q)]

lemma free_diameter_noise (L : Length) {t r : ℝ} (hr : 0 < r) (ht : t ≤ r^2)
    (w : CoordinatePaths 1) (y : Torus L) :
    intervalDiameter 0 1 (freeTrajectory 1 L t w (oneConfiguration y))/r ≤ 12*noiseSize w := by
  have hs : Real.sqrt (2*t) ≤ 2*r := Real.sqrt_le_iff.mpr ⟨by positivity,by nlinarith [sq_nonneg r]⟩
  have h := free_diameter_le L t w y (noiseSize_nonneg w) (noiseSize_coord w)
  apply (div_le_iff₀ hr).mpr
  have hh := mul_le_mul_of_nonneg_right hs (show 0 ≤ 6*noiseSize w from mul_nonneg (by norm_num) (noiseSize_nonneg w))
  nlinarith

lemma noiseSize_memLp (p : ℝ≥0∞) (hp : p≠⊤) : MemLp noiseSize p (coordinateWiener 1) := by
  unfold noiseSize
  apply memLp_finsetSum
  intro j _
  exact ((IsGaussian.memLp_id wiener p hp).norm).comp_measurePreserving
    (measurePreserving_eval (fun _ : Direction 1 ↦ wiener) (0,j))

lemma integrable_cubicNoise : Integrable (fun w : CoordinatePaths 1 ↦ (1+12*noiseSize w)^3) (coordinateWiener 1) := by
  have h0 : MemLp (fun _ : CoordinatePaths 1 ↦ (1:ℝ)) (3:ℝ≥0∞) (coordinateWiener 1) := memLp_const 1
  have h1 := (noiseSize_memLp 3 (by norm_num)).const_mul 12
  have h : MemLp (fun w : CoordinatePaths 1 ↦ 1+12*noiseSize w) (3:ℝ≥0∞) (coordinateWiener 1) := h0.add h1
  have hi := h.integrable_norm_pow (by norm_num : (3:ℕ)≠0)
  have hpos (w : CoordinatePaths 1) : 0 ≤ 1+12*noiseSize w := by have := noiseSize_nonneg w; positivity
  simpa only [Real.norm_eq_abs, abs_of_nonneg (hpos _)] using hi

end HardSphere.PathCutoff

end
end

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Cutoffs_CubicMoment
attribute [-instance] _root_.OAI.HardSphere.Bridge.exposedBridgeKernel_markov _root_.OAI.HardSphere.Bridge.exposedPeriodSingle_finite _root_.OAI.HardSphere.Bridge.exposedTrialKernel_markov _root_.OAI.HardSphere.Bridge.instBorelSpaceContinuousMapElemRealTimePoint _root_.OAI.HardSphere.Bridge.instIsProbabilityMeasureNoiseLaw _root_.OAI.HardSphere.Bridge.instMeasurableSpaceContinuousMapElemRealTimePoint _root_.OAI.HardSphere.Bridge.parameterBridgeKernel_markov _root_.OAI.HardSphere.Bridge.parameterIndividualReference_finite _root_.OAI.HardSphere.Bridge.parameterTrialKernel_markov _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Bridge.trialKernel_markov _root_.OAI.HardSphere.Groups.cellPathReference_probability _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Rescaling.config_haar _root_.OAI.HardSphere.Wiener.bridgeLaw_isGaussian _root_.OAI.HardSphere.bridgeEndpointBase_finite _root_.OAI.HardSphere.coordinateBridge_probability _root_.OAI.HardSphere.endpointWeightedBase_sfinite _root_.OAI.HardSphere.gaussianCoordinates_probability
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

lemma free_cubicCost_le {L : Length} {r t : ℝ} (hr : 0 < r) (ht : t ≤ r^2)
    (w : CoordinatePaths 1) (X : Configuration 1 L) :
    cubicCost r (freeTrajectory 1 L t w X) ≤ (1+12*noiseSize w)^3 := by
  have hX : X=oneConfiguration (X 0) := by ext i j; have hi : i=0 := Subsingleton.elim _ _; subst i; rfl
  have h := free_diameter_noise L hr ht w (X 0)
  rw [←hX] at h
  unfold cubicCost diameterRatio
  exact pow_le_pow_left₀ (by have := intervalDiameter_nonneg 0 1 (freeTrajectory 1 L t w X); positivity) (add_le_add le_rfl h) 3

lemma free_cubicCost_integrable {L : Length} {r t : ℝ} (hr : 0 < r) (ht : t ≤ r^2)
    (X : Configuration 1 L) :
    Integrable (fun w ↦ cubicCost r (freeTrajectory 1 L t w X)) (coordinateWiener 1) := by
  apply integrable_cubicNoise.mono'
    (((cubicCost_continuous L r).comp ((freeTrajectory_continuous 1 L t).comp
      (continuous_id.prodMk continuous_const))).aestronglyMeasurable)
  exact ae_of_all _ (fun w ↦ by
    change ‖cubicCost r (freeTrajectory 1 L t w X)‖ ≤ _
    rw [Real.norm_eq_abs,abs_of_nonneg (cubicCost_nonneg hr.le _)]
    exact free_cubicCost_le hr ht w X)

lemma cubicMean_nonneg : 0 ≤ cubicMean := integral_nonneg (fun w ↦ by have := noiseSize_nonneg w; positivity)

lemma free_cubicMean_le {L : Length} {r t : ℝ} (hr : 0 < r) (ht : t ≤ r^2) (X : Configuration 1 L) :
    ∫w,cubicCost r (freeTrajectory 1 L t w X) ∂coordinateWiener 1 ≤ cubicMean :=
  integral_mono (free_cubicCost_integrable hr ht X) integrable_cubicNoise (fun w ↦ free_cubicCost_le hr ht w X)

lemma cappedWeight_measurable {L : Length} (r B : ℝ) : Measurable (cappedWeight (L:=L) r B) :=
  (Real.continuous_exp.comp (((cubicCost_continuous L r).min continuous_const).div_const B)).measurable.ennreal_ofReal

lemma meanCost_nonneg : 0 ≤ meanCost := by
  unfold meanCost
  have he : 0≤Real.exp 1-1 := by have := Real.add_one_le_exp 1; linarith
  exact mul_nonneg he cubicMean_nonneg

lemma free_cap_moment {L : Length} {r t B : ℝ} (hr : 0 < r) (ht : t ≤ r^2) (hB : 0<B)
    (X : Configuration 1 L) :
    ∫⁻w,cappedWeight r B (freeTrajectory 1 L t w X) ∂coordinateWiener 1 ≤
      ENNReal.ofReal (Real.exp (meanCost/B)) := by
  apply (exp_cap_integral (coordinateWiener 1) (free_cubicCost_integrable hr ht X)
    (ae_of_all _ (fun _ ↦ cubicCost_nonneg hr.le _)) hB).trans
  apply ENNReal.ofReal_le_ofReal
  apply Real.exp_le_exp.mpr
  unfold meanCost
  apply div_le_div_of_nonneg_right _ hB.le
  apply mul_le_mul_of_nonneg_left (free_cubicMean_le hr ht X)
  have := Real.add_one_le_exp 1
  linarith

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

lemma capSum_continuous {L : Length} (m : ℕ) (r B : ℝ) : Continuous (capSum (L:=L) m r B) := by
  unfold capSum
  exact continuous_finsetSum _ (fun j _ ↦ ((cubicCost_continuous L r).comp (meshSegment_continuous L j)).min continuous_const)

lemma cap_product_eq {L : Length} (m : ℕ) (r B : ℝ) (ω : ConfigurationPath 1 L) :
    meshProduct m (cappedWeight r B) ω=ENNReal.ofReal (Real.exp (capSum m r B ω/B)) := by
  simp only [meshProduct,cappedWeight,capSum,Finset.sum_div,Real.exp_sum,
    ENNReal.ofReal_prod_of_nonneg (fun _ _ ↦ Real.exp_nonneg _)]

lemma orig_exp_pow (x : ℝ) (m : ℕ) :
    (ENNReal.ofReal (Real.exp x))^m=ENNReal.ofReal (Real.exp ((m:ℝ)*x)) := by
  rw [←ENNReal.ofReal_pow (Real.exp_nonneg x),←Real.exp_nat_mul]

lemma mesh_cap_moment {L : Length} {r τ B : ℝ} (hr : 0 < r) (hτ : 0<τ) (hτr : τ ≤ r^2) (hB : 0<B)
    (m : ℕ) (hm : 0 < m) (X : Configuration 1 L) :
    ∫⁻w,ENNReal.ofReal (Real.exp (capSum m r B (freeTrajectory 1 L ((m:ℝ)*τ) w X)/B)) ∂coordinateWiener 1 ≤
      ENNReal.ofReal (Real.exp ((m:ℝ)*meanCost/B)) := by
  have h := meshProduct_free_bound (cappedWeight r B) (cappedWeight_measurable r B) hτ
    (ENNReal.ofReal (Real.exp (meanCost/B))) (fun Y ↦ free_cap_moment hr hτr hB Y) m hm X
  simpa only [cap_product_eq,orig_exp_pow,mul_div_assoc] using h

lemma mesh_cap_tail {L : Length} {r τ B : ℝ} (hr : 0 < r) (hτ : 0<τ) (hτr : τ ≤ r^2) (hB : 0<B)
    (m : ℕ) (hm : 0 < m) (X : Configuration 1 L) :
    coordinateWiener 1 {w | (meanCost+1)*(m:ℝ) ≤ capSum m r B (freeTrajectory 1 L ((m:ℝ)*τ) w X)} ≤
      ENNReal.ofReal (Real.exp (-(m:ℝ)/B)) := by
  let F : CoordinatePaths 1 → ℝ≥0∞ := fun w ↦
    ENNReal.ofReal (Real.exp (capSum m r B (freeTrajectory 1 L ((m:ℝ)*τ) w X)/B))
  let v : ℝ≥0∞ := ENNReal.ofReal (Real.exp (((meanCost+1)*(m:ℝ))/B))
  have hF : Measurable F :=
    (Real.continuous_exp.comp (((capSum_continuous m r B).comp ((freeTrajectory_continuous 1 L ((m:ℝ)*τ)).comp
      (continuous_id.prodMk continuous_const))).div_const B)).measurable.ennreal_ofReal
  have hv : v≠0 := ENNReal.ofReal_ne_zero_iff.mpr (Real.exp_pos _)
  have hv' : v≠⊤ := ENNReal.ofReal_ne_top
  have hsub : {w | (meanCost+1)*(m:ℝ) ≤ capSum m r B (freeTrajectory 1 L ((m:ℝ)*τ) w X)} ⊆ {w | v ≤ F w} := by
    intro w hw
    exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (div_le_div_of_nonneg_right hw hB.le))
  calc
    _ ≤ coordinateWiener 1 {w | v ≤ F w} := measure_mono hsub
    _ ≤ (∫⁻w,F w ∂coordinateWiener 1)/v := meas_ge_le_lintegral_div hF.aemeasurable hv hv'
    _ ≤ ENNReal.ofReal (Real.exp ((m:ℝ)*meanCost/B))/v :=
      ENNReal.div_le_div_right (mesh_cap_moment hr hτ hτr hB m hm X) v
    _ = ENNReal.ofReal (Real.exp (-(m:ℝ)/B)) := by
      dsimp only [v]
      rw [←ENNReal.ofReal_div_of_pos (Real.exp_pos _),←Real.exp_sub]
      congr 2
      ring

end HardSphere.PathCutoff

end
end

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Cutoffs_DiameterTail
attribute [-instance] _root_.OAI.HardSphere.Bridge.exposedBridgeKernel_markov _root_.OAI.HardSphere.Bridge.exposedPeriodSingle_finite _root_.OAI.HardSphere.Bridge.exposedTrialKernel_markov _root_.OAI.HardSphere.Bridge.instBorelSpaceContinuousMapElemRealTimePoint _root_.OAI.HardSphere.Bridge.instIsProbabilityMeasureNoiseLaw _root_.OAI.HardSphere.Bridge.instMeasurableSpaceContinuousMapElemRealTimePoint _root_.OAI.HardSphere.Bridge.parameterBridgeKernel_markov _root_.OAI.HardSphere.Bridge.parameterIndividualReference_finite _root_.OAI.HardSphere.Bridge.parameterTrialKernel_markov _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Bridge.trialKernel_markov _root_.OAI.HardSphere.Groups.cellPathReference_probability _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Rescaling.config_haar _root_.OAI.HardSphere.Wiener.bridgeLaw_isGaussian _root_.OAI.HardSphere.bridgeEndpointBase_finite _root_.OAI.HardSphere.coordinateBridge_probability _root_.OAI.HardSphere.endpointWeightedBase_sfinite _root_.OAI.HardSphere.gaussianCoordinates_probability
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

lemma free_diameterRatio_tail {c : ℝ} {M : ℝ≥0∞}
    (htail : ∀ R : ℝ, 0≤R → wiener {w | R≤‖w‖} ≤ M*ENNReal.ofReal (Real.exp (-c*R^2)))
    {L : Length} {r τ R : ℝ} (hr : 0 < r) (hτr : τ ≤ r^2) (hR : 0≤R)
    (X : Configuration 1 L) :
    coordinateWiener 1 {w | R<diameterRatio r (freeTrajectory 1 L τ w X)} ≤
      3*M*ENNReal.ofReal (Real.exp (-c*(R/36)^2)) := by
  have hX : X=oneConfiguration (X 0) := by ext i j; have hi : i=0 := Subsingleton.elim _ _; subst i; rfl
  have hsub : {w | R<diameterRatio r (freeTrajectory 1 L τ w X)} ⊆
      ⋃j : Fin 3,{w | R/36≤‖w (0,j)‖} := by
    intro w hw
    by_contra hn
    have hnorm : ∀j : Fin 3, ‖w (0,j)‖<R/36 := by
      simpa only [Set.mem_iUnion,Set.mem_ofPred_eq,not_exists,not_le] using hn
    have hsum : noiseSize w ≤ R/12 := by
      unfold noiseSize
      calc
        _ ≤ ∑j : Fin 3, R/36 := Finset.sum_le_sum (fun j _ ↦ (hnorm j).le)
        _ = R/12 := by simp only [Finset.sum_const,Finset.card_fin,nsmul_eq_mul]; ring
    have hd := free_diameter_noise L hr hτr w (X 0)
    rw [←hX] at hd
    change R < intervalDiameter 0 1 (freeTrajectory 1 L τ w X)/r at hw
    linarith
  have he (j : Fin 3) : coordinateWiener 1 {w | R/36≤‖w (0,j)‖} = wiener {w | R/36≤‖w‖} :=
    (measurePreserving_eval (fun _ : Direction 1 ↦ wiener) (0,j)).measure_preimage
      (measurableSet_le measurable_const measurable_norm).nullMeasurableSet
  calc
    _ ≤ coordinateWiener 1 (⋃j : Fin 3,{w | R/36≤‖w (0,j)‖}) := measure_mono hsub
    _ ≤ ∑'j : Fin 3,coordinateWiener 1 {w | R/36≤‖w (0,j)‖} := measure_iUnion_le _
    _ = 3*wiener {w | R/36≤‖w‖} := by simp [he,tsum_fintype]
    _ ≤ 3*(M*ENNReal.ofReal (Real.exp (-c*(R/36)^2))) := mul_le_mul_right (htail _ (by positivity)) _
    _ = _ := by ring

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

lemma capSum_eq_of_max {L : Length} (m : ℕ) {r R : ℝ} (hr : 0 ≤ r)
    (ω : ConfigurationPath 1 L) (hmax : ∀j : Fin m, diameterRatio r (meshSegment j ω) ≤ R) :
    capSum m r ((1+R)^3) ω=∑j : Fin m,cubicCost r (meshSegment j ω) := by
  unfold capSum
  apply Finset.sum_congr rfl
  intro j _
  apply min_eq_left
  unfold cubicCost
  exact pow_le_pow_left₀ (by linarith [diameterRatio_nonneg hr (meshSegment j ω)]) (by linarith [hmax j]) 3

lemma mesh_irregular_sub {L : Length} {m : ℕ} {r R : ℝ} (hr : 0 ≤ r) :
    {ω : ConfigurationPath 1 L | ¬MeshRegular m r R (meanCost+1) ω} ⊆
      meshEvent m {ω | R < diameterRatio r ω} ∪
      {ω | (meanCost+1)*(m:ℝ) ≤ capSum m r ((1+R)^3) ω} := by
  intro ω hω
  by_cases hmax : ∀j : Fin m, diameterRatio r (meshSegment j ω) ≤ R
  · right
    change (meanCost+1)*(m:ℝ) ≤ capSum m r ((1+R)^3) ω
    rw [capSum_eq_of_max m hr ω hmax]
    have hn : (meanCost+1)*(m:ℝ) < ∑j : Fin m,cubicCost r (meshSegment j ω) := by
      exact lt_of_not_ge (fun h ↦ hω ⟨hmax,h⟩)
    exact hn.le
  · left
    simpa only [meshEvent,Set.mem_ofPred_eq,not_forall,not_le] using hmax

lemma free_mesh_regular_tail {c : ℝ} {M : ℝ≥0∞}
    (htail : ∀ R : ℝ, 0 ≤ R → wiener {w | R ≤ ‖w‖} ≤ M*ENNReal.ofReal (Real.exp (-c*R^2)))
    {L : Length} {r τ R : ℝ} (hr : 0 < r) (hτ : 0 < τ) (hτr : τ ≤ r^2) (hR : 0 ≤ R)
    (m : ℕ) (hm : 0 < m) (X : Configuration 1 L) :
    coordinateWiener 1 {w | ¬MeshRegular m r R (meanCost+1) (freeTrajectory 1 L ((m:ℝ)*τ) w X)} ≤
      (m:ℝ≥0∞)*(3*M*ENNReal.ofReal (Real.exp (-c*(R/36)^2)))+
      ENNReal.ofReal (Real.exp (-(m:ℝ)/((1+R)^3))) := by
  have hB : 0 < (1+R)^3 := by positivity
  have hp := meshEvent_free_bound (L:=L) m hm
    (measurableSet_lt measurable_const (diameterRatio_continuous L r).measurable) hτ
    (3*M*ENNReal.ofReal (Real.exp (-c*(R/36)^2)))
    (fun Y ↦ free_diameterRatio_tail htail hr hτr hR Y) X
  calc
    _ ≤ coordinateWiener 1 ({w | freeTrajectory 1 L ((m:ℝ)*τ) w X ∈ meshEvent m {ω | R < diameterRatio r ω}} ∪
      {w | (meanCost+1)*(m:ℝ) ≤ capSum m r ((1+R)^3) (freeTrajectory 1 L ((m:ℝ)*τ) w X)}) :=
      measure_mono (fun w hw ↦ mesh_irregular_sub hr.le hw)
    _ ≤ _ := (measure_union_le _ _).trans (add_le_add hp (mesh_cap_tail hr hτ hτr hB m hm X))

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

lemma liftedDiameter_eq {L : Length} {ω : ConfigurationPath 1 L} {ζ : EuclideanPath}
    (hζ : IsPathLift ω ζ) (a b : Time) (hsmall : intervalDiameter a b ω < L.val/2) :
    liftedDiameter a b ζ=intervalDiameter a b ω := by
  unfold liftedDiameter intervalDiameter
  congr 1
  ext p
  change Real.sqrt (∑j, (ζ j (intervalTime a b p.1)-ζ j (intervalTime a b p.2))^2)=
    torusDistance L _ _
  simp only [torusDistance,liftDiff_norm_eq hζ a b hsmall,sq_abs]

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

lemma intervalDiameter_le_lifted {L : Length} {ω : ConfigurationPath 1 L} {ζ : EuclideanPath}
    (hζ : IsPathLift ω ζ) (a b : Time) : intervalDiameter a b ω ≤ liftedDiameter a b ζ := by
  apply intervalDiameter_le a b ω (norm_nonneg _)
  intro s q
  have hfirst : torusDistance L (ω (intervalTime a b s) 0) (ω (intervalTime a b q) 0) ≤
      liftedDiameterMap a b ζ (s,q) := by
    unfold torusDistance liftedDiameterMap
    apply Real.sqrt_le_sqrt
    apply Finset.sum_le_sum
    intro j _
    have hle : dist (ω (intervalTime a b s) 0 j) (ω (intervalTime a b q) 0 j) ≤
        |ζ j (intervalTime a b s)-ζ j (intervalTime a b q)| := by
      rw [dist_eq_norm,←liftDiff_coe hζ]
      exact QuotientAddGroup.norm_mk_le_norm
    have hh := pow_le_pow_left₀ dist_nonneg hle 2
    simpa only [sq_abs] using hh
  exact hfirst.trans ((le_abs_self _).trans (ContinuousMap.norm_coe_le_norm (liftedDiameterMap a b ζ) (s,q)))

lemma meshSegment_lift {L : Length} {m : ℕ} {ω : ConfigurationPath 1 L} {ζ : EuclideanPath}
    (hζ : IsPathLift ω ζ) (j : Fin m) :
    IsPathLift (meshSegment j ω) (fun k ↦ (ζ k).comp ⟨meshTime j,meshTime_continuous j⟩) := by
  intro k s
  exact hζ k _

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

lemma mesh_lift_diameter {L : Length} {m : ℕ} {ω : ConfigurationPath 1 L} {ζ : EuclideanPath}
    (hζ : IsPathLift ω ζ) {r R : ℝ} (hr : 0 < r) (hR : R*r < L.val/2)
    (hmax : ∀j : Fin m,diameterRatio r (meshSegment j ω) ≤ R) (j : Fin m) :
    liftedDiameter 0 1 (fun k ↦ (ζ k).comp ⟨meshTime j,meshTime_continuous j⟩)=
      intervalDiameter 0 1 (meshSegment j ω) := by
  apply liftedDiameter_eq (meshSegment_lift hζ j)
  exact ((div_le_iff₀ hr).mp (hmax j)).trans_lt hR

end HardSphere.PathCutoff

end
end

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Bridges_BridgeHighMoment
attribute [-instance] _root_.OAI.HardSphere.Bridge.exposedBridgeKernel_markov _root_.OAI.HardSphere.Bridge.exposedPeriodSingle_finite _root_.OAI.HardSphere.Bridge.exposedTrialKernel_markov _root_.OAI.HardSphere.Bridge.parameterBridgeKernel_markov _root_.OAI.HardSphere.Bridge.parameterIndividualReference_finite _root_.OAI.HardSphere.Bridge.parameterTrialKernel_markov _root_.OAI.HardSphere.Groups.cellPathReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite
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
namespace HardSphere.Wiener

lemma normPowerMean_nonneg (p : ℕ) : 0≤normPowerMean p := integral_nonneg (fun _ ↦ by positivity)
lemma integrable_normPower (p : ℕ) (hp : p≠0) : Integrable (fun w : C(Time,ℝ) ↦ ‖w‖^p) wiener :=
  (IsGaussian.memLp_id wiener p (by simp)).integrable_norm_pow hp

lemma loose_add_pow {a b : ℝ} (ha : 0≤a) (hb : 0≤b) (p : ℕ) :
    (a+b)^p≤2^p*(a^p+b^p) := by
  calc
    _ ≤ (2*max a b)^p := pow_le_pow_left₀ (add_nonneg ha hb) (by linarith [le_max_left a b,le_max_right a b]) p
    _ = 2^p*(max a b)^p := mul_pow _ _ _
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      rcases le_total a b with hab|hba
      · rw [max_eq_right hab]
        exact le_add_of_nonneg_left (pow_nonneg ha _)
      · rw [max_eq_left hba]
        exact le_add_of_nonneg_right (pow_nonneg hb _)

lemma prefix_normPower (u : Time) (p : ℕ) :
    ∫w : C(Time,ℝ),‖prefixMap u w‖^p ∂wiener=(Real.sqrt (u:ℝ))^p*normPowerMean p := by
  rw [←integral_map (f:=fun w : C(Time,ℝ) ↦ ‖w‖^p) (prefixMap u).continuous.measurable.aemeasurable (by fun_prop),prefix_wiener_law,
    integral_map (by fun_prop) (by fun_prop)]
  simp only [norm_smul,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _),mul_pow,integral_const_mul,normPowerMean]

lemma increment_wiener_power (s u : Time) (p : ℕ) :
    ∫β : C(Time,ℝ),‖incrementMap s u β‖^p ∂wiener =
      (Real.sqrt ((1-(s:ℝ))*(u:ℝ)))^p*normPowerMean p := by
  change (∫β : C(Time,ℝ),‖prefixMap u (suffixMap s β)‖^p ∂wiener)=_
  rw [←integral_map (f:=fun β : C(Time,ℝ) ↦ ‖prefixMap u β‖^p) (suffixMap s).continuous.measurable.aemeasurable (by fun_prop),suffix_wiener_law,
    integral_map (by fun_prop) (by fun_prop)]
  simp only [map_smul,norm_smul,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _),mul_pow,integral_const_mul]
  rw [prefix_normPower,Real.sqrt_mul (sub_nonneg.mpr s.property.2),mul_pow]
  ring

lemma increment_bridge_power (s u : Time) (p : ℕ) (hp : p≠0) :
    ∫β : C(Time,ℝ),‖incrementMap s u β‖^p ∂bridgeLaw ≤
      2^(p+1)*(Real.sqrt ((1-(s:ℝ))*(u:ℝ)))^p*normPowerMean p := by
  let δ := (1-(s:ℝ))*(u:ℝ)
  have hd : 0≤δ := mul_nonneg (sub_nonneg.mpr s.property.2) u.property.1
  have hd1 : δ≤1 := by dsimp [δ]; nlinarith [s.property.1,s.property.2,u.property.1,u.property.2]
  have hi₁ : Integrable (fun f : C(Time,ℝ) ↦ ‖incrementMap s u (centerMap f)‖^p) wiener :=
    ((IsGaussian.memLp_id wiener p (by simp)).continuousLinearMap_comp ((incrementMap s u).comp centerMap)).integrable_norm_pow hp
  have hi₂ : Integrable (fun f : C(Time,ℝ) ↦ ‖incrementMap s u f‖^p) wiener :=
    ((IsGaussian.memLp_id wiener p (by simp)).continuousLinearMap_comp (incrementMap s u)).integrable_norm_pow hp
  rw [bridgeLaw_center,integral_map centerMap.continuous.measurable.aemeasurable (by fun_prop)]
  calc
    _ ≤ ∫f : C(Time,ℝ),2^p*(‖incrementMap s u f‖^p+δ^p*‖f‖^p) ∂wiener := by
      apply integral_mono hi₁ ((hi₂.add ((integrable_normPower p hp).const_mul _)).const_mul _)
      intro f
      exact (pow_le_pow_left₀ (norm_nonneg _) (increment_center_norm s u f) p).trans
        (by simpa only [Pi.add_apply,mul_pow,δ] using loose_add_pow (norm_nonneg (incrementMap s u f)) (mul_nonneg hd (norm_nonneg f)) p)
    _ = 2^p*((Real.sqrt δ)^p*normPowerMean p+δ^p*normPowerMean p) := by
      rw [integral_const_mul,integral_add hi₂ ((integrable_normPower p hp).const_mul _),integral_const_mul,increment_wiener_power]
      rfl
    _ ≤ _ := by
      have hds : δ≤Real.sqrt δ := Real.le_sqrt_of_sq_le (by nlinarith)
      have hh := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hd hds p) (normPowerMean_nonneg p)
      calc
        _ ≤ 2^p*((Real.sqrt δ)^p*normPowerMean p+(Real.sqrt δ)^p*normPowerMean p) := by gcongr
        _ = _ := by rw [pow_succ]; ring

end HardSphere.Wiener

end
end

section
noncomputable section
open MeasureTheory Set Filter ProbabilityTheory
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.Bridge
open Wiener GaussianPacking
lemma sum_three_power (f : Fin 3→ℝ) (hf : ∀j,0≤f j) (p : ℕ) :
    (∑j,f j)^p≤3^p*(∑j,f j^p) := by
  obtain ⟨i,hi,hmax⟩ := Finset.exists_max_image Finset.univ f (Finset.univ_nonempty : (Finset.univ : Finset (Fin 3)).Nonempty)
  have hsum : (∑j,f j)≤3*f i := by
    calc
      _ ≤ ∑_j : Fin 3,f i := Finset.sum_le_sum (fun j hj ↦ hmax j hj)
      _ = _ := by simp [nsmul_eq_mul]
  calc
    _ ≤ (3*f i)^p := pow_le_pow_left₀ (Finset.sum_nonneg (fun j _ ↦ hf j)) hsum p
    _ = 3^p*(f i)^p := mul_pow _ _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left (Finset.single_le_sum (fun j _ ↦ pow_nonneg (hf j) p) hi) (by positivity)

lemma incrementSize_memLp_power (s u : Time) (p : ℕ) : MemLp (incrementSize s u) p law := by
  apply memLp_finsetSum
  intro j hj
  have h := ((IsGaussian.memLp_id bridgeLaw p (by simp)).continuousLinearMap_comp (incrementMap s u)).norm
  exact h.comp_measurePreserving (measurePreserving_eval (fun _ : Fin 3 ↦ bridgeLaw) j)

lemma incrementSize_power_mean (s u : Time) (p : ℕ) (hp : p≠0) :
    ∫β,(incrementSize s u β)^p ∂law ≤
      (3^p*3*2^(p+1))*(Real.sqrt ((1-(s:ℝ))*(u:ℝ)))^p*normPowerMean p := by
  have hi j : Integrable (fun β : Noise ↦ ‖incrementMap s u (β j)‖^p) law := by
    exact (((IsGaussian.memLp_id bridgeLaw p (by simp)).continuousLinearMap_comp (incrementMap s u)).comp_measurePreserving
      (measurePreserving_eval (fun _ : Fin 3 ↦ bridgeLaw) j)).integrable_norm_pow hp
  have hsum : Integrable (fun β ↦ (incrementSize s u β)^p) law := by
    simpa only [Real.norm_eq_abs,abs_of_nonneg (incrementSize_nonneg s u _)] using
      (incrementSize_memLp_power s u p).integrable_norm_pow hp
  calc
    _ ≤ ∫β,3^p*(∑j,‖incrementMap s u (β j)‖^p) ∂law := by
      apply integral_mono hsum ((integrable_finsetSum _ (fun j _ ↦ hi j)).const_mul _)
      intro β
      exact sum_three_power _ (fun j ↦ norm_nonneg _) p
    _ = 3^p*(∑j : Fin 3,∫β : C(Time,ℝ),‖incrementMap s u β‖^p ∂bridgeLaw) := by
      rw [integral_const_mul,integral_finsetSum _ (fun j _ ↦ hi j)]
      congr 1
      apply Finset.sum_congr rfl
      intro j hj
      have hm := measurePreserving_eval (fun _ : Fin 3 ↦ bridgeLaw) j
      rw [←hm.map_eq,integral_map hm.measurable.aemeasurable (show Continuous (fun β : C(Time,ℝ) ↦ ‖incrementMap s u β‖^p) from (incrementMap s u).continuous.norm.pow p).aestronglyMeasurable]
      rfl
    _ ≤ 3^p*(∑_j : Fin 3,2^(p+1)*(Real.sqrt ((1-(s:ℝ))*(u:ℝ)))^p*normPowerMean p) := by
      exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun _ _ ↦ increment_bridge_power s u p hp)) (by positivity)
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]; ring

end HardSphere.Bridge

end
end

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.Bridge
open Wiener GaussianPacking PathCutoff

lemma liftedDiameter_coord_le (ζ : EuclideanPath) (a b : Time) {R : ℝ} (hR : 0≤R)
    (h : ∀j s q,|ζ j (intervalTime a b s)-ζ j (intervalTime a b q)|≤R) :
    liftedDiameter a b ζ≤3*R := by
  apply (ContinuousMap.norm_le _ (by positivity)).mpr
  intro p
  change |Real.sqrt (∑j,(ζ j (intervalTime a b p.1)-ζ j (intervalTime a b p.2))^2)|≤3*R
  rw [abs_of_nonneg (Real.sqrt_nonneg _)]
  apply (Real.sqrt_le_iff).mpr
  refine ⟨by positivity,?_⟩
  have hs : (∑j,(ζ j (intervalTime a b p.1)-ζ j (intervalTime a b p.2))^2)≤3*R^2 := by
    calc
      _ ≤ ∑_j : Fin 3,R^2 := Finset.sum_le_sum (fun j _ ↦ by nlinarith [h j p.1 p.2,abs_nonneg (ζ j (intervalTime a b p.1)-ζ j (intervalTime a b p.2)),sq_abs (ζ j (intervalTime a b p.1)-ζ j (intervalTime a b p.2))])
      _ = _ := by simp
  nlinarith [sq_nonneg R]

end HardSphere.Bridge

end
end

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Bridges_BridgeWiener
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

lemma rawNoise_preserving : MeasurePreserving rawNoise (coordinateWiener 1)
    (Measure.pi (fun _ : Fin 3 ↦ wiener)) := by
  convert measurePreserving_piCongrLeft (fun _ : Fin 3 ↦ wiener)
    (Equiv.uniqueProd (Fin 3) (Fin 1)) using 1
  · ext w j s
    rfl
  · rfl
lemma centeredNoise_preserving : MeasurePreserving centeredNoise (coordinateWiener 1) law := by
  have hm : Measurable (fun β : Noise ↦ fun j ↦ centerMap (β j)) := by fun_prop
  have he : (Measure.pi (fun _ : Fin 3 ↦ wiener)).map (fun β : Noise ↦ fun j ↦ centerMap (β j))=law := by
    rw [Measure.pi_map_pi (fun _ ↦ centerMap.continuous.measurable.aemeasurable)]
    simp only [←bridgeLaw_center,law]
  exact (show MeasurePreserving (fun β : Noise ↦ fun j ↦ centerMap (β j)) _ law from ⟨hm,he⟩).comp rawNoise_preserving

lemma lifted_coord_le (ζ : EuclideanPath) (a b s q : Time) (i : Fin 3) :
    |ζ i (intervalTime a b s)-ζ i (intervalTime a b q)|≤liftedDiameter a b ζ := by
  have hsq : (ζ i (intervalTime a b s)-ζ i (intervalTime a b q))^2≤
      ∑j,(ζ j (intervalTime a b s)-ζ j (intervalTime a b q))^2 :=
    Finset.single_le_sum (fun j _ ↦ sq_nonneg (ζ j (intervalTime a b s)-ζ j (intervalTime a b q))) (Finset.mem_univ i)
  have h := Real.sqrt_le_sqrt hsq
  rw [Real.sqrt_sq_eq_abs] at h
  exact h.trans ((le_abs_self _).trans
    (ContinuousMap.norm_coe_le_norm (liftedDiameterMap a b ζ) (s,q)))

lemma centeredNoise_eval (w : CoordinatePaths 1) (j : Fin 3) (s : Time) :
    centeredNoise w j s=w (0,j) s-(s:ℝ)*w (0,j) 1 := by simp [centeredNoise,rawNoise]

end HardSphere.Bridge

end
end

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.Bridge
open Wiener GaussianPacking PathCutoff

lemma rawPath_lift (L : Length) (t : ℝ) (y : Point) (w : CoordinatePaths 1) :
    IsPathLift (freeTrajectory 1 L t w (fun _ j ↦ (y j:AddCircle L.val))) (rawPath t y w) := by
  intro j s
  change ((y j+Real.sqrt (2*t)*w (0,j) s:ℝ):AddCircle L.val)=_
  simp only [AddCircle.coe_add,freeTrajectory,ContinuousMap.coe_mk]

lemma mesh_time_dist {n : ℕ} (j : Fin n) (s q : Time) :
    |(meshTime j s:ℝ)-(meshTime j q:ℝ)|≤1/(n:ℝ) := by
  have hn : (0:ℝ)<n := by exact_mod_cast j.pos
  change |((j:ℝ)+(s:ℝ))/(n:ℝ)-((j:ℝ)+(q:ℝ))/(n:ℝ)|≤_
  rw [←sub_div,show (j:ℝ)+(s:ℝ)-((j:ℝ)+(q:ℝ))=(s:ℝ)-(q:ℝ) by ring,abs_div,abs_of_pos hn]
  apply div_le_div_of_nonneg_right _ hn.le
  exact abs_le.mpr ⟨by linarith [s.property.1,q.property.2],by linarith [s.property.2,q.property.1]⟩

lemma centered_leg_mesh_coord {n : ℕ} (j : Fin n) {t r C B : ℝ} (hr : 0 < r)
    (y u : Point) (w : CoordinatePaths 1) (hdis : ‖u-y‖≤C) (hw : ∀i,‖w (0,i)‖≤B)
    (hdrift : (C+Real.sqrt (2*t)*B)/(n:ℝ) ≤ r) (i : Fin 3) (s q : Time) :
    |leg t y u (centeredNoise w) (meshTime j s) i-leg t y u (centeredNoise w) (meshTime j q) i|≤
      liftedDiameter 0 1 (fun k ↦ (rawPath t y w k).comp ⟨meshTime j,meshTime_continuous j⟩)+r := by
  by_cases htime : s = q
  · rw [htime, sub_self, abs_zero]
    exact add_nonneg (norm_nonneg _) hr.le
  have hn : (0:ℝ)<n := by exact_mod_cast j.pos
  have hbase := lifted_coord_le (fun k ↦ (rawPath t y w k).comp ⟨meshTime j,meshTime_continuous j⟩) 0 1 s q i
  have hi : |u i-y i-Real.sqrt (2*t)*w (0,i) 1|≤C+Real.sqrt (2*t)*B := by
    apply (abs_sub _ _).trans
    rw [abs_mul,abs_of_nonneg (Real.sqrt_nonneg _)]
    apply add_le_add ((norm_le_pi_norm (u-y) i).trans hdis)
    exact mul_le_mul_of_nonneg_left ((ContinuousMap.norm_coe_le_norm _ 1).trans (hw i)) (Real.sqrt_nonneg _)
  have hinc := mul_le_mul (mesh_time_dist j s q) hi (abs_nonneg _) (by positivity : 0≤1/(n:ℝ))
  have he : 1/(n:ℝ)*(C+Real.sqrt (2*t)*B)=(C+Real.sqrt (2*t)*B)/(n:ℝ) := by ring
  rw [he] at hinc
  have hs : intervalTime 0 1 s=s := by apply Subtype.ext; simp [intervalTime]
  have hq : intervalTime 0 1 q=q := by apply Subtype.ext; simp [intervalTime]
  simp only [hs,hq,ContinuousMap.comp_apply,ContinuousMap.coe_mk,rawPath] at hbase
  have hel : leg t y u (centeredNoise w) (meshTime j s) i-leg t y u (centeredNoise w) (meshTime j q) i=
    ((y i+Real.sqrt (2*t)*w (0,i) (meshTime j s))-(y i+Real.sqrt (2*t)*w (0,i) (meshTime j q)))+
    ((meshTime j s:ℝ)-(meshTime j q:ℝ))*(u i-y i-Real.sqrt (2*t)*w (0,i) 1) := by
    simp only [leg,ContinuousMap.coe_mk,centeredNoise_eval,mean]
    ring
  rw [hel]
  apply (abs_add_le _ _).trans
  rw [abs_mul]
  exact add_le_add hbase (hinc.trans hdrift)

lemma centered_leg_mesh_diameter {n : ℕ} (j : Fin n) {t r C B : ℝ} (hr : 0 < r)
    (y u : Point) (w : CoordinatePaths 1) (hdis : ‖u-y‖≤C) (hw : ∀i,‖w (0,i)‖≤B)
    (hdrift : (C+Real.sqrt (2*t)*B)/(n:ℝ) ≤ r) :
    liftedDiameter 0 1 (fun k ↦ (pathCoordinates (leg t y u (centeredNoise w)) k).comp ⟨meshTime j,meshTime_continuous j⟩)/r≤
      3*(1+liftedDiameter 0 1 (fun k ↦ (rawPath t y w k).comp ⟨meshTime j,meshTime_continuous j⟩)/r) := by
  apply (div_le_iff₀ hr).mpr
  have hh := liftedDiameter_coord_le
    (fun k ↦ (pathCoordinates (leg t y u (centeredNoise w)) k).comp ⟨meshTime j,meshTime_continuous j⟩) 0 1
    (by unfold liftedDiameter; positivity : 0≤liftedDiameter 0 1 (fun k ↦ (rawPath t y w k).comp ⟨meshTime j,meshTime_continuous j⟩)+r)
    (fun i s q ↦ centered_leg_mesh_coord j hr y u w hdis hw hdrift i (intervalTime 0 1 s) (intervalTime 0 1 q))
  exact hh.trans_eq (by field_simp; ring)

end HardSphere.Bridge

end
end

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Bridges_BridgeAverage
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

lemma liftedDiameter_continuous (a b : Time) : Continuous (liftedDiameter a b) := by
  apply Continuous.norm
  apply ContinuousMap.continuous_of_continuous_uncurry
  change Continuous (fun p : EuclideanPath×(Time×Time) ↦ Real.sqrt (∑j,(p.1 j (intervalTime a b p.2.1)-p.1 j (intervalTime a b p.2.2))^2))
  have hi := intervalTime_continuous a b
  fun_prop

lemma legCost_continuous {n : ℕ} (j : Fin n) (t r : ℝ) (y u : Point) : Continuous (legCost t r y u j) := by
  have hζ : Continuous (fun β : Noise ↦ fun i : Fin 3 ↦ (pathCoordinates (leg t y u β) i).comp ⟨meshTime j,meshTime_continuous j⟩) := by
    apply continuous_pi
    intro i
    apply ContinuousMap.continuous_of_continuous_uncurry
    change Continuous (fun p : Noise×Time ↦ leg t y u p.1 (meshTime j p.2) i)
    have hl := leg_continuous t y u
    have hj := meshTime_continuous j
    fun_prop
  exact (continuous_const.add (((liftedDiameter_continuous 0 1).comp hζ).div_const r)).pow 3

end HardSphere.Bridge

end
end

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Bridges_BridgeStrongRegular
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

lemma legMeshRegular_measurable (n : ℕ) (t r R C : ℝ) (y u : Point) :
    MeasurableSet {β | LegMeshRegular n t r R C y u β} := by
  have he : {β | LegMeshRegular n t r R C y u β} = ((⋂j : Fin n,{β | legMeshRatio t r y u j β≤R}) ∩
    {β | (∑j : Fin n,legCost t r y u j β)≤C*(n:ℝ)}) := by ext β; simp [LegMeshRegular]
  rw [he]
  apply MeasurableSet.inter
  · apply MeasurableSet.iInter
    intro j
    apply measurableSet_le _ measurable_const
    unfold legMeshRatio
    have hζ : Continuous (fun β : Noise ↦ fun i : Fin 3 ↦
        (pathCoordinates (leg t y u β) i).comp ⟨meshTime j,meshTime_continuous j⟩) := by
      apply continuous_pi; intro i
      apply ContinuousMap.continuous_of_continuous_uncurry
      change Continuous (fun p : Noise×Time ↦ leg t y u p.1 (meshTime j p.2) i)
      have hl := leg_continuous t y u
      have hj := meshTime_continuous j
      fun_prop
    exact (((liftedDiameter_continuous 0 1).comp hζ).div_const r).measurable
  · exact measurableSet_le (Finset.measurable_fun_sum _ (fun j _ ↦ (legCost_continuous j t r y u).measurable)) measurable_const

lemma strong_mesh_of_free (L : Length) (n : ℕ) {t r R B C Creg : ℝ} (hr : 0 < r)
    (y u : Point) (w : CoordinatePaths 1) (hdis : ‖u-y‖≤C) (hw : ∀i,‖w (0,i)‖≤B)
    (hdrift : (C+Real.sqrt (2*t)*B)/(n:ℝ) ≤ r) (hsmall : R*r<L.val/2)
    (hfree : MeshRegular n r R Creg (freeTrajectory 1 L t w (fun _ j ↦ (y j:AddCircle L.val)))) :
    LegMeshRegular n t r (3*(1+R)) (64*Creg) y u (centeredNoise w) := by
  have he (j : Fin n) := mesh_lift_diameter (rawPath_lift L t y w) hr hsmall hfree.1 j
  have hd (j : Fin n) : legMeshRatio t r y u j (centeredNoise w)≤
      3*(1+diameterRatio r (meshSegment j (freeTrajectory 1 L t w (fun _ j ↦ (y j:AddCircle L.val))))) := by
    have h := centered_leg_mesh_diameter j hr y u w hdis hw hdrift
    rw [he j] at h
    exact h
  constructor
  · intro j
    exact (hd j).trans (by linarith [hfree.1 j])
  · calc
      _ ≤ ∑j : Fin n,64*cubicCost r (meshSegment j (freeTrajectory 1 L t w (fun _ j ↦ (y j:AddCircle L.val)))) := by
        apply Finset.sum_le_sum
        intro j _
        have hnon : 0≤legMeshRatio t r y u j (centeredNoise w) := div_nonneg (norm_nonneg _) hr.le
        have h := pow_le_pow_left₀ (by linarith : 0≤1+legMeshRatio t r y u j (centeredNoise w))
          (show 1+legMeshRatio t r y u j (centeredNoise w)≤4*(1+diameterRatio r (meshSegment j (freeTrajectory 1 L t w (fun _ j ↦ (y j:AddCircle L.val))))) by
            have hn := diameterRatio_nonneg hr.le (meshSegment j (freeTrajectory 1 L t w (fun _ j ↦ (y j:AddCircle L.val))))
            linarith [hd j]) 3
        simpa only [mul_pow,show (4:ℝ)^3=64 by norm_num,legCost,cubicCost,legMeshRatio] using h
      _ = 64*(∑j : Fin n,cubicCost r (meshSegment j (freeTrajectory 1 L t w (fun _ j ↦ (y j:AddCircle L.val))))) := (Finset.mul_sum ..).symm
      _ ≤ 64*(Creg*(n:ℝ)) := mul_le_mul_of_nonneg_left hfree.2 (by norm_num)
      _ = _ := by ring

lemma raw_norm_tail {c B : ℝ} {M : ℝ≥0∞} (hB : 0≤B)
    (htail : ∀R : ℝ,0≤R → wiener {w | R≤‖w‖}≤M*ENNReal.ofReal (Real.exp (-c*R^2))) :
    coordinateWiener 1 {w | ¬∀i : Fin 3,‖w (0,i)‖≤B}≤3*(M*ENNReal.ofReal (Real.exp (-c*B^2))) := by
  have he : {w : CoordinatePaths 1 | ¬∀i : Fin 3,‖w (0,i)‖≤B} = ⋃i : Fin 3,{w | B<‖w (0,i)‖} := by ext w; simp
  rw [he]
  apply (measure_iUnion_fintype_le _ _).trans
  calc
    _ ≤ ∑_i : Fin 3,M*ENNReal.ofReal (Real.exp (-c*B^2)) := by
      apply Finset.sum_le_sum
      intro i _
      have hm := measurePreserving_eval (fun _ : Direction 1 ↦ wiener) (0,i)
      have hset : MeasurableSet {f : C(Time,ℝ) | B<‖f‖} := measurableSet_lt measurable_const (by fun_prop)
      change (Measure.pi fun _ : Direction 1 ↦ wiener) ((Function.eval (0,i)) ⁻¹' {f : C(Time,ℝ) | B<‖f‖})≤_
      rw [hm.measure_preimage hset.nullMeasurableSet]
      exact (measure_mono (show {f : C(Time,ℝ) | B<‖f‖}⊆{f | B≤‖f‖} from by intro f hf; change B<‖f‖ at hf; change B≤‖f‖; exact le_of_lt hf)).trans (htail B hB)
    _ = _ := by simp [nsmul_eq_mul]

lemma strong_leg_mesh_tail {c : ℝ} {M : ℝ≥0∞}
    (htail : ∀ R : ℝ,0≤R → wiener {w | R≤‖w‖}≤M*ENNReal.ofReal (Real.exp (-c*R^2)))
    (L : Length) (n : ℕ) (hn : 0<n) {t r R B C : ℝ}
    (ht : 0<t) (hr : 0 < r) (hτr : t/(n:ℝ) ≤ r^2) (hR : 0≤R) (hB : 0≤B)
    (y u : Point) (hdis : ‖u-y‖≤C)
    (hdrift : (C+Real.sqrt (2*t)*B)/(n:ℝ) ≤ r) (hsmall : R*r<L.val/2) :
    law {β | ¬LegMeshRegular n t r (3*(1+R)) (64*(meanCost+1)) y u β}≤
      (n:ℝ≥0∞)*(3*M*ENNReal.ofReal (Real.exp (-c*(R/36)^2)))+
        ENNReal.ofReal (Real.exp (-(n:ℝ)/((1+R)^3)))+
        3*(M*ENNReal.ofReal (Real.exp (-c*B^2))) := by
  have hn' : (0:ℝ)<n := by exact_mod_cast hn
  have he : MeasurableSet {β | ¬LegMeshRegular n t r (3*(1+R)) (64*(meanCost+1)) y u β} := (legMeshRegular_measurable n t r (3*(1+R)) (64*(meanCost+1)) y u).compl
  rw [←centeredNoise_preserving.measure_preimage he.nullMeasurableSet]
  have hsub : centeredNoise ⁻¹' {β | ¬LegMeshRegular n t r (3*(1+R)) (64*(meanCost+1)) y u β} ⊆
      {w | ¬MeshRegular n r R (meanCost+1) (freeTrajectory 1 L t w (fun _ j ↦ (y j:AddCircle L.val)))} ∪
      {w | ¬∀i : Fin 3,‖w (0,i)‖≤B} := by
    intro w hw
    by_contra hn
    have hh := not_or.mp hn
    exact hw (strong_mesh_of_free L n hr y u w hdis (not_not.mp hh.2) hdrift hsmall (not_not.mp hh.1))
  have hfree := free_mesh_regular_tail htail hr (div_pos ht hn') hτr hR n hn (fun _ j ↦ (y j:AddCircle L.val))
  rw [mul_div_cancel₀ _ (ne_of_gt hn')] at hfree
  exact ((measure_mono hsub).trans (measure_union_le _ _)).trans (add_le_add hfree (raw_norm_tail hB htail))

end HardSphere.Bridge

end
end

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.Bridge
open Wiener GaussianPacking PathCutoff

lemma projectCurve_lift (L : Length) (f : C(Time,Point)) : IsPathLift (projectCurve L f) (pathCoordinates f) := by
  intro j s
  rfl

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
lemma mesh_second_half {n : ℕ} (j : Fin n) (s : Time) :
    meshTime (j.natAdd n) s=suffixTime midpointTime (meshTime j s) := by
  apply Subtype.ext
  have hn : (n:ℝ)≠0 := by exact_mod_cast (Nat.ne_of_gt j.pos)
  simp only [meshTime,Fin.val_natAdd,Nat.cast_add,suffixTime,midpointTime,ContinuousMap.coe_mk]
  field_simp [hn]
  ring

lemma trial_mesh_left (L : Length) {n : ℕ} (j : Fin n) (t : ℝ) (y z u : Point) (β : Noise×Noise) :
    meshSegment (j.castAdd n) (projectCurve L (trialPath t y z u β))=
      meshSegment j (projectCurve L (leg t y u (pinned β.1))) := by
  apply ContinuousMap.ext
  intro s
  simp only [meshSegment,ContinuousMap.coe_mk,projectCurve,mesh_first_half,trial_left]

lemma trial_mesh_right (L : Length) {n : ℕ} (j : Fin n) (t : ℝ) (y z u : Point) (β : Noise×Noise) :
    meshSegment (j.natAdd n) (projectCurve L (trialPath t y z u β))=
      meshSegment j (reverseConfigurationPath 1 L (projectCurve L (leg t z u (pinned β.2)))) := by
  apply ContinuousMap.ext
  intro s
  simp only [meshSegment,ContinuousMap.coe_mk,projectCurve,mesh_second_half,trial_right]
  rfl

lemma project_leg_mesh_regular (L : Length) {n : ℕ} {t r R C : ℝ} (hr : 0 < r)
    (y u : Point) (β : Noise) (h : LegMeshRegular n t r R C y u β) :
    MeshRegular n r R C (projectCurve L (leg t y u β)) := by
  have hd (j : Fin n) : diameterRatio r (meshSegment j (projectCurve L (leg t y u β)))≤legMeshRatio t r y u j β :=
    div_le_div_of_nonneg_right (intervalDiameter_le_lifted (meshSegment_lift (projectCurve_lift L (leg t y u β)) j) 0 1) hr.le
  constructor
  · intro j
    exact (hd j).trans (h.1 j)
  · apply le_trans (Finset.sum_le_sum (fun j _ ↦ ?_)) h.2
    change (1+diameterRatio r (meshSegment j (projectCurve L (leg t y u β))))^3 ≤ (1+legMeshRatio t r y u j β)^3
    exact pow_le_pow_left₀ (by linarith [diameterRatio_nonneg hr.le (meshSegment j (projectCurve L (leg t y u β)))]) (by linarith [hd j]) 3

lemma trial_mesh_regular (L : Length) {n : ℕ} {t r R C : ℝ} (hr : 0 < r)
    (y z u : Point) (β : Noise×Noise)
    (h₁ : LegMeshRegular n t r R C y u (pinned β.1))
    (h₂ : LegMeshRegular n t r R C z u (pinned β.2)) :
    MeshRegular (n+n) r R C (projectCurve L (trialPath t y z u β)) := by
  have hl := project_leg_mesh_regular L hr y u (pinned β.1) h₁
  have hrr := project_leg_mesh_regular L hr z u (pinned β.2) h₂
  have hright := (meshRegular_reverse (L:=L) n r R C _).mpr hrr
  constructor
  · refine (Fin.forall_fin_add (fun j : Fin (n+n) ↦ diameterRatio r (meshSegment j (projectCurve L (trialPath t y z u β)))≤R)).mpr ?_
    constructor
    · intro j
      rw [trial_mesh_left]
      exact hl.1 j
    · intro j
      rw [trial_mesh_right]
      exact hright.1 j
  · rw [Fin.sum_univ_add]
    simp_rw [trial_mesh_left,trial_mesh_right]
    have h := add_le_add hl.2 hright.2
    simpa only [Nat.cast_add,mul_add] using h

end HardSphere.Bridge

end
end

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Thermodynamics_BridgeScaleTail
attribute [-instance] _root_.OAI.HardSphere.Bridge.exposedBridgeKernel_markov _root_.OAI.HardSphere.Bridge.exposedPeriodSingle_finite _root_.OAI.HardSphere.Bridge.exposedTrialKernel_markov _root_.OAI.HardSphere.Bridge.parameterBridgeKernel_markov _root_.OAI.HardSphere.Bridge.parameterIndividualReference_finite _root_.OAI.HardSphere.Bridge.parameterTrialKernel_markov _root_.OAI.HardSphere.Groups.cellPathReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite
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

lemma scaleMoment_nonneg (p : ℕ) {t r : ℝ} (hr : 0≤ r) (s w : Time) : 0≤ scaleMoment p t r s w := by
  unfold scaleMoment
  exact mul_nonneg
    (mul_nonneg (by positivity) (pow_nonneg (div_nonneg (Real.sqrt_nonneg _) hr) p))
    (normPowerMean_nonneg p)
lemma incrementFluctuation_scale_mean {t r : ℝ} (ht : 0≤ t) (hr : 0< r)
    (s w : Time) (p : ℕ) (hp : p≠0) :
    ∫β,(incrementFluctuation t r s w β)^p ∂law≤ scaleMoment p t r s w := by
  simp only [incrementFluctuation,mul_pow,integral_const_mul]
  calc
    _ ≤ (Real.sqrt (2*t)/r)^p*((3^p*3*2^(p+1))*(Real.sqrt ((1-(s:ℝ))*(w:ℝ)))^p*normPowerMean p) :=
      mul_le_mul_of_nonneg_left (incrementSize_power_mean s w p hp) (by positivity)
    _ = _ := by
      unfold scaleMoment
      rw [show 2*t*(1-(s:ℝ))*(w:ℝ)=(2*t)*((1-(s:ℝ))*(w:ℝ)) by ring,Real.sqrt_mul (show 0≤2*t by positivity)]
      simp only [mul_pow,div_pow]
      ring

lemma incrementFluctuation_scale_tail {t r R : ℝ} (ht : 0≤ t) (hr : 0< r) (hR : 0< R)
    (s w : Time) (p : ℕ) (hp : p≠0) :
    law {β | R≤ incrementFluctuation t r s w β}≤ ENNReal.ofReal (scaleMoment p t r s w)/(ENNReal.ofReal R)^p := by
  have hi : Integrable (fun β ↦ (incrementFluctuation t r s w β)^p) law := by
    unfold incrementFluctuation
    simp only [mul_pow]
    have h := (incrementSize_memLp_power s w p).integrable_norm_pow hp
    simp only [Real.norm_eq_abs,abs_of_nonneg (incrementSize_nonneg s w _)] at h
    exact h.const_mul _
  have hm := ((incrementFluctuation_continuous t r s w).pow p).measurable.ennreal_ofReal
  have h := meas_ge_le_lintegral_div (μ:=law) hm.aemeasurable
    (ne_of_gt (ENNReal.ofReal_pos.mpr (pow_pos hR p))) ENNReal.ofReal_ne_top
  apply (measure_mono (show {β | R≤ incrementFluctuation t r s w β}⊆
      {β | ENNReal.ofReal (R^p)≤ ENNReal.ofReal ((incrementFluctuation t r s w β)^p)} from
    fun β hβ ↦ ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ hR.le hβ p))).trans
  apply h.trans
  rw [ENNReal.ofReal_pow hR.le]
  apply ENNReal.div_le_div_right
  change (∫⁻β,ENNReal.ofReal ((incrementFluctuation t r s w β)^p) ∂law)≤ _
  rw [←ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ (fun β ↦ pow_nonneg (incrementFluctuation_nonneg hr.le s w β) p))]
  exact ENNReal.ofReal_le_ofReal (incrementFluctuation_scale_mean ht hr s w p hp)

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
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.Bridge
open Wiener GaussianPacking PathCutoff

lemma leg_window_coord {t S C : ℝ} (hS : 0< S) (hC : 0≤ C) (y u : Point)
    (hdis : ‖u-y‖≤ C) (β : Noise) (w q : Time) (hq : (q:ℝ)≤(w:ℝ)) (i : Fin 3) :
    |leg t y u β q i-leg t y u β 0 i|≤
      (w:ℝ)*C+S*incrementFluctuation t S 0 w β := by
  have he : suffixTime 0 q=q := by apply Subtype.ext; simp [suffixTime]
  have hd : |(q:ℝ)*(u i-y i)|≤(w:ℝ)*C := by
    rw [abs_mul,abs_of_nonneg q.property.1]
    exact (mul_le_mul_of_nonneg_left ((norm_le_pi_norm (u-y) i).trans hdis) q.property.1).trans
      (mul_le_mul_of_nonneg_right hq hC)
  have hn := incrementFluctuation_eval (t:=t) hS 0 w q hq β i
  rw [he] at hn
  have hl := leg_segment_increment t y u β 0 q i
  rw [he] at hl
  simp only [show ((0:Time):ℝ)=0 from rfl,sub_zero,one_mul] at hl
  rw [hl,show leg t y u β 0 i+(q:ℝ)*(u i-y i)+Real.sqrt (2*t)*(β i q-β i 0)-leg t y u β 0 i=(q:ℝ)*(u i-y i)+Real.sqrt (2*t)*(β i q-β i 0) by ring]
  exact (abs_add_le _ _).trans (add_le_add hd hn)

lemma leg_window_diameter {t S C : ℝ} (hS : 0< S) (hC : 0≤ C) (y u : Point)
    (hdis : ‖u-y‖≤ C) (β : Noise) (w : Time) :
    liftedDiameter 0 w (pathCoordinates (leg t y u β))≤
      6*((w:ℝ)*C+S*incrementFluctuation t S 0 w β) := by
  have hR : 0≤(w:ℝ)*C+S*incrementFluctuation t S 0 w β :=
    add_nonneg (mul_nonneg w.property.1 hC) (mul_nonneg hS.le (incrementFluctuation_nonneg hS.le 0 w β))
  have hw (q : Time) : (intervalTime 0 w q:ℝ)≤(w:ℝ) := by
    change (1-(q:ℝ))*0+(q:ℝ)*(w:ℝ)≤(w:ℝ)
    nlinarith [q.property.2,w.property.1]
  have h := liftedDiameter_coord_le (pathCoordinates (leg t y u β)) 0 w
    (mul_nonneg (by norm_num : (0:ℝ)≤2) hR) (fun i s q ↦ by
      have hs := leg_window_coord (t:=t) hS hC y u hdis β w (intervalTime 0 w s) (hw s) i
      have hq := leg_window_coord (t:=t) hS hC y u hdis β w (intervalTime 0 w q) (hw q) i
      change |leg t y u β (intervalTime 0 w s) i-leg t y u β (intervalTime 0 w q) i|≤_
      have he : leg t y u β (intervalTime 0 w s) i-leg t y u β (intervalTime 0 w q) i=
        (leg t y u β (intervalTime 0 w s) i-leg t y u β 0 i)-(leg t y u β (intervalTime 0 w q) i-leg t y u β 0 i) := by ring
      rw [he]
      exact (abs_sub _ _).trans (by linarith))
  linarith

lemma leg_window_tail {t S C : ℝ} (ht : 0≤ t) (hS : 0< S) (hC : 0≤ C) (y u : Point)
    (hdis : ‖u-y‖≤ C) (w : Time) (hdrift : (w:ℝ)*C≤ S/12) (p : ℕ) (hp : p≠0) :
    law {β | S≤ liftedDiameter 0 w (pathCoordinates (leg t y u β))}≤
      ENNReal.ofReal (scaleMoment p t S 0 w)/(ENNReal.ofReal (1/12:ℝ))^p := by
  apply (measure_mono (show {β | S≤ liftedDiameter 0 w (pathCoordinates (leg t y u β))}⊆
    {β | (1/12:ℝ)≤ incrementFluctuation t S 0 w β} from ?_)).trans
    (incrementFluctuation_scale_tail ht hS (by norm_num) 0 w p hp)
  intro β hβ
  have h := leg_window_diameter (t:=t) hS hC y u hdis β w
  change S≤_ at hβ
  change (1/12:ℝ)≤ incrementFluctuation t S 0 w β
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

lemma exists_pathLift_at {L : Length} (ω : ConfigurationPath 1 L) (y : Point)
    (hy : projectPoint L y=ω 0 0) : ∃ζ : EuclideanPath,IsPathLift ω ζ ∧ (fun j ↦ ζ j 0)=y := by
  have hx (j : Fin 3) : ∃ ζ : C(Time,ℝ),(∀s,(ζ s : AddCircle L.val)=ω s 0 j) ∧ ζ 0=y j := by
    let γ : C(Time,AddCircle L.val) := ⟨fun s ↦ ω s 0 j,by fun_prop⟩
    have h0 : γ 0=(y j : AddCircle L.val) := (congrFun hy j).symm
    obtain ⟨ζ,hζ,hζ0⟩ := (AddCircle.isCoveringMap_coe L.val).exists_path_lifts γ (y j) h0
    exact ⟨ζ,(fun s ↦ congrFun hζ s),hζ0⟩
  choose ζ hζ using hx
  exact ⟨ζ,fun j s ↦ (hζ j).1 s,funext (fun j ↦ (hζ j).2)⟩

end HardSphere.Bridge

end
end

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.Bridge
open Wiener GaussianPacking PathCutoff

lemma leg_confined_of_fluctuation (L : Length) (t : ℝ) (y u v : Point) (β : Noise)
    (hy : ‖y-v‖≤3) (hu : ‖u-v‖≤3) (hzero : ∀j,β j 0=0)
    (hnoise : incrementFluctuation t 1 0 1 β≤1/3) (s : Time) :
    ‖leg t y u β s-v‖≤10 ∧
      torusDistance L (projectPoint L (leg t y u β s)) (projectPoint L v)≤10 := by
  have hc (j : Fin 3) : |leg t y u β s j-v j|≤10/3 := by
    have hn := incrementFluctuation_eval (t:=t) (by norm_num : (0:ℝ)<1) 0 1 s s.property.2 β j
    have hs : suffixTime 0 s=s := by apply Subtype.ext; simp [suffixTime]
    rw [hs,hzero j,sub_zero,one_mul] at hn
    have hyj : |y j-v j|≤3 := (norm_le_pi_norm (y-v) j).trans hy
    have huj : |u j-v j|≤3 := (norm_le_pi_norm (u-v) j).trans hu
    have hm : |(1-(s:ℝ))*(y j-v j)+(s:ℝ)*(u j-v j)|≤3 := by
      apply (abs_add_le _ _).trans
      rw [abs_mul,abs_mul,abs_of_nonneg (sub_nonneg.mpr s.property.2),abs_of_nonneg s.property.1]
      have h₁ := mul_le_mul_of_nonneg_left hyj (sub_nonneg.mpr s.property.2)
      have h₂ := mul_le_mul_of_nonneg_left huj s.property.1
      linarith
    change |(1-(s:ℝ))*y j+(s:ℝ)*u j+Real.sqrt (2*t)*β j s-v j|≤10/3
    rw [show (1-(s:ℝ))*y j+(s:ℝ)*u j+Real.sqrt (2*t)*β j s-v j=
      ((1-(s:ℝ))*(y j-v j)+(s:ℝ)*(u j-v j))+Real.sqrt (2*t)*β j s by ring]
    exact (abs_add_le _ _).trans (by linarith)
  constructor
  · apply (pi_norm_le_iff_of_nonneg (by norm_num : (0:ℝ)≤10)).mpr
    intro j
    exact (hc j).trans (by norm_num)
  · unfold torusDistance
    apply (Real.sqrt_le_iff).mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ ∑ _j : Fin 3, (10/3:ℝ)^2 := by
        apply Finset.sum_le_sum
        intro j _
        apply (sq_le_sq₀ dist_nonneg (by norm_num : (0:ℝ)≤10/3)).mpr
        rw [dist_eq_norm, ← AddCircle.coe_sub]
        exact (QuotientAddGroup.norm_mk_le_norm (m := leg t y u β s j-v j)).trans
          (by simpa only [Real.norm_eq_abs] using hc j)
      _ ≤ (10:ℝ)^2 := by norm_num

end HardSphere.Bridge

end
end

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

lemma trial_initial_diameter (L : Length) (t : ℝ) (y z u : Point) (β : Noise×Noise) (w : Time) :
    intervalDiameter 0 (prefixTime midpointTime w) (projectCurve L (trialPath t y z u β))=
      intervalDiameter 0 w (projectCurve L (leg t y u (pinned β.1))) := by
  apply congrArg norm
  apply ContinuousMap.ext
  intro p
  have he (s : Time) : intervalTime 0 (prefixTime midpointTime w) s=prefixTime midpointTime (intervalTime 0 w s) := by
    apply Subtype.ext
    simp [intervalTime,prefixTime,midpointTime]
    ring
  change torusDistance L ((projectCurve L (trialPath t y z u β)) (intervalTime 0 (prefixTime midpointTime w) p.1) 0)
    ((projectCurve L (trialPath t y z u β)) (intervalTime 0 (prefixTime midpointTime w) p.2) 0)=_
  simp only [he,projectCurve,ContinuousMap.coe_mk,trial_left]
  rfl

lemma trial_endpoint_regular (L : Length) (t : ℝ) (y z u : Point) (β : Noise×Noise) (w : Time) {S : ℝ}
    (h₁ : liftedDiameter 0 w (pathCoordinates (leg t y u (pinned β.1)))≤S)
    (h₂ : liftedDiameter 0 w (pathCoordinates (leg t z u (pinned β.2)))≤S) :
    EndpointRegular (prefixTime midpointTime w) S (projectCurve L (trialPath t y z u β)) := by
  constructor
  · rw [trial_initial_diameter]
    exact (intervalDiameter_le_lifted (projectCurve_lift L _) 0 w).trans h₁
  · have h := trial_initial_diameter L t z y u β.swap w
    rw [←trial_reverse,intervalDiameter_reverse] at h
    simp only [reverseTime_zero,Prod.fst_swap] at h
    rw [h]
    exact (intervalDiameter_le_lifted (projectCurve_lift L _) 0 w).trans h₂

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

lemma trial_confined (L : Length) (t : ℝ) (y z u v : Point) (β : Noise×Noise)
    (hy : ‖y-v‖≤3) (hz : ‖z-v‖≤3) (hu : ‖u-v‖≤3)
    (h₁ : incrementFluctuation t 1 0 1 (pinned β.1)≤1/3)
    (h₂ : incrementFluctuation t 1 0 1 (pinned β.2)≤1/3) :
    TrialConfined L v (trialPath t y z u β) := by
  intro s
  rcases prefix_or_suffix s with ⟨q,rfl⟩|⟨q,rfl⟩
  · rw [trial_left]
    exact leg_confined_of_fluctuation L t y u v (pinned β.1) hy hu (fun _ ↦ center_zero _) h₁ q
  · rw [trial_right]
    exact leg_confined_of_fluctuation L t z u v (pinned β.2) hz hu (fun _ ↦ center_zero _) h₂ (reverseTime q)

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

lemma trial_cutoff_of_legs (L : Length) {n : ℕ} {t r R C S : ℝ} (hr : 0 < r)
    (y z u v : Point) (β : Noise×Noise) (w : Time)
    (hy : ‖y-v‖≤3) (hz : ‖z-v‖≤3) (hu : ‖u-v‖≤3)
    (hm₁ : LegMeshRegular n t r R C y u (pinned β.1))
    (hm₂ : LegMeshRegular n t r R C z u (pinned β.2))
    (hw₁ : liftedDiameter 0 w (pathCoordinates (leg t y u (pinned β.1)))≤S)
    (hw₂ : liftedDiameter 0 w (pathCoordinates (leg t z u (pinned β.2)))≤S)
    (hc₁ : incrementFluctuation t 1 0 1 (pinned β.1)≤1/3)
    (hc₂ : incrementFluctuation t 1 0 1 (pinned β.2)≤1/3) :
    TrialCutoff L n r R C w S v (trialPath t y z u β) :=
  ⟨⟨trial_mesh_regular L hr y z u β hm₁ hm₂,trial_endpoint_regular L t y z u β w hw₁ hw₂⟩,
    trial_confined L t y z u v β hy hz hu hc₁ hc₂⟩

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

lemma leg_lift_diameter_continuous (t : ℝ) (y u : Point) (w : Time) :
    Continuous (fun β : Noise ↦ liftedDiameter 0 w (pathCoordinates (leg t y u β))) := by
  apply (liftedDiameter_continuous 0 w).comp
  apply continuous_pi
  intro i
  apply ContinuousMap.continuous_of_continuous_uncurry
  change Continuous (fun p : Noise×Time ↦ leg t y u p.1 p.2 i)
  have hl := leg_continuous t y u
  fun_prop

lemma goodLeg_measurable (n : ℕ) (t r R C S : ℝ) (y u : Point) (w : Time) :
    MeasurableSet {β | GoodLeg n t r R C S y u w β} :=
  (legMeshRegular_measurable n t r R C y u).inter
    ((measurableSet_le (leg_lift_diameter_continuous t y u w).measurable measurable_const).inter
      (measurableSet_le (incrementFluctuation_continuous t 1 0 1).measurable measurable_const))

lemma leg_failure_le (n : ℕ) (t r R C S : ℝ) (y u : Point) (w : Time) :
    law {β | ¬GoodLeg n t r R C S y u w β} ≤
      law {β | ¬LegMeshRegular n t r R C y u β}+
      law {β | S≤liftedDiameter 0 w (pathCoordinates (leg t y u β))}+
      law {β | (1/3:ℝ)≤ incrementFluctuation t 1 0 1 β} := by
  apply (measure_mono (show {β | ¬GoodLeg n t r R C S y u w β}⊆
    ({β | ¬LegMeshRegular n t r R C y u β} ∪ {β | S≤liftedDiameter 0 w (pathCoordinates (leg t y u β))}) ∪
      {β | (1/3:ℝ)≤ incrementFluctuation t 1 0 1 β} from ?_)).trans
  · exact (measure_union_le _ _).trans (add_le_add (measure_union_le _ _) le_rfl)
  intro β hβ
  by_contra hn
  have hh := not_or.mp hn
  have hm := not_or.mp hh.1
  exact hβ ⟨not_not.mp hm.1,(le_of_not_ge hm.2),le_of_not_ge hh.2⟩

lemma trial_cutoff_failure (L : Length) (n : ℕ) {t r R C S : ℝ} (hr : 0 < r)
    (y z u v : Point) (w : Time) (hy : ‖y-v‖≤3) (hz : ‖z-v‖≤3) (hu : ‖u-v‖≤3) :
    trialKernel t y z u {f | ¬TrialCutoff L n r R C w S v f}≤
      law {β | ¬GoodLeg n t r R C S y u w β}+
      law {β | ¬GoodLeg n t r R C S z u w β} := by
  have hcut : MeasurableSet {f | ¬TrialCutoff L n r R C w S v f} := (trialCutoff_measurable L n r R C w S v).compl
  have hm : Measurable (trialPath t y z u) := ((trialPath_continuous t y z).comp (continuous_const.prodMk continuous_id)).measurable
  rw [trialKernel_apply,Measure.map_apply hm hcut]
  let P := {β | ¬GoodLeg n t r R C S y u w β}
  let Q := {β | ¬GoodLeg n t r R C S z u w β}
  have hp : MeasurableSet P := (goodLeg_measurable n t r R C S y u w).compl
  have hq : MeasurableSet Q := (goodLeg_measurable n t r R C S z u w).compl
  have hpre : (trialPath t y z u) ⁻¹' {f | ¬TrialCutoff L n r R C w S v f}⊆
      (fun β : Noise×Noise ↦ pinned β.1) ⁻¹' P ∪ (fun β : Noise×Noise ↦ pinned β.2) ⁻¹' Q := by
    intro β hβ
    by_contra hn
    have hh := not_or.mp hn
    have h₁ : GoodLeg n t r R C S y u w (pinned β.1) := not_not.mp hh.1
    have h₂ : GoodLeg n t r R C S z u w (pinned β.2) := not_not.mp hh.2
    exact hβ (trial_cutoff_of_legs L hr y z u v β w hy hz hu h₁.1 h₂.1 h₁.2.1 h₂.2.1 h₁.2.2 h₂.2.2)
  have hpin : MeasurePreserving pinned law law := ⟨pinned_continuous.measurable,pinned_law⟩
  have h₁ := hpin.comp (measurePreserving_fst (μ:=law) (ν:=law))
  have h₂ := hpin.comp (measurePreserving_snd (μ:=law) (ν:=law))
  exact ((measure_mono hpre).trans (measure_union_le _ _)).trans_eq
    (congrArg₂ (·+·) (h₁.measure_preimage hp.nullMeasurableSet) (h₂.measure_preimage hq.nullMeasurableSet))

lemma trial_cutoff_physical_tail {c : ℝ} {M : ℝ≥0∞}
    (htail : ∀R : ℝ,0≤R → wiener {β | R≤‖β‖}≤M*ENNReal.ofReal (Real.exp (-c*R^2)))
    (L : Length) (n : ℕ) (hn : 0<n) {t r R B C S : ℝ}
    (ht : 0<t) (hr : 0 < r) (hτr : t/(n:ℝ) ≤ r^2) (hR : 0≤R) (hB : 0≤B) (hC : 0≤C) (hS : 0<S)
    (y z u v : Point) (w : Time) (p : ℕ) (hp : p≠0)
    (hy : ‖y-v‖≤3) (hz : ‖z-v‖≤3) (hu : ‖u-v‖≤3)
    (hdu : ‖u-y‖≤C) (hdz : ‖u-z‖≤C)
    (hdrift : (C+Real.sqrt (2*t)*B)/(n:ℝ) ≤ r) (hsmall : R*r<L.val/2)
    (hwindow : (w:ℝ)*C≤S/12) :
    trialKernel t y z u {f | ¬TrialCutoff L n r (3*(1+R)) (64*(meanCost+1)) w S v f}≤
      2*((n:ℝ≥0∞)*(3*M*ENNReal.ofReal (Real.exp (-c*(R/36)^2)))+
        ENNReal.ofReal (Real.exp (-(n:ℝ)/((1+R)^3)))+
        3*(M*ENNReal.ofReal (Real.exp (-c*B^2)))+
        ENNReal.ofReal (scaleMoment p t S 0 w)/(ENNReal.ofReal (1/12:ℝ))^p+
        ENNReal.ofReal (scaleMoment p t 1 0 1)/(ENNReal.ofReal (1/3:ℝ))^p) := by
  apply (trial_cutoff_failure L n hr y z u v w hy hz hu).trans
  have h (x : Point) (hx : ‖u-x‖≤C) := (leg_failure_le n t r (3*(1+R)) (64*(meanCost+1)) S x u w).trans
    (add_le_add (add_le_add (strong_leg_mesh_tail htail L n hn ht hr hτr hR hB x u hx hdrift hsmall)
      (leg_window_tail ht.le hS hC x u hx w hwindow p hp))
      (incrementFluctuation_scale_tail (r:=1) (R:=1/3) ht.le (by norm_num) (by norm_num) 0 1 p hp))
  exact (add_le_add (h y hdu) (h z hdz)).trans_eq (by rw [two_mul])

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

end HardSphere.Bridge

end
end

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Bridges_ConfinedLift
attribute [-instance] _root_.OAI.HardSphere.Bridge.exposedBridgeKernel_markov _root_.OAI.HardSphere.Bridge.exposedPeriodSingle_finite _root_.OAI.HardSphere.Bridge.exposedTrialKernel_markov _root_.OAI.HardSphere.Bridge.parameterBridgeKernel_markov _root_.OAI.HardSphere.Bridge.parameterIndividualReference_finite _root_.OAI.HardSphere.Bridge.parameterTrialKernel_markov _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Bridge.targetUniform_finite _root_.OAI.HardSphere.Comparison.parameterTargetKernel_finite _root_.OAI.HardSphere.Groups.cellPathReference_probability _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Rescaling.config_haar _root_.OAI.HardSphere.bridgeEndpointBase_finite _root_.OAI.HardSphere.endpointWeightedBase_sfinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology
namespace HardSphere.Bridge
open Wiener PathCutoff GaussianPacking
attribute [local irreducible] torusDistance

lemma intervalTime_full (s : Time) : intervalTime 0 1 s=s := by
  apply Subtype.ext
  simp [intervalTime]

lemma tube_diameter {L : Length} (ω : ConfigurationPath 1 L) (c : Torus L)
    (hc : ∀s : Time,torusDistance L (ω s 0) c≤10) : intervalDiameter 0 1 ω≤20 := by
  apply intervalDiameter_le _ _ _ (by norm_num)
  intro s q
  simp only [intervalTime_full]
  have htri := torusDistance_triangle' L (ω s 0) c (ω q 0)
  rw [torusDistance_comm L c] at htri
  linarith [hc s,hc q]

lemma lift_norm_increment {L : Length} (hL : 50<L.val) (f : C(Time,Point))
    (hd : intervalDiameter 0 1 (projectCurve L f)≤20) (s : Time) :
    ‖f s-f 0‖≤20 := by
  apply (pi_norm_le_iff_of_nonneg (by norm_num : (0:ℝ)≤20)).mpr
  intro j
  have he := liftDiff_norm_eq (projectCurve_lift L f) 0 1 (hd.trans_lt (by linarith)) j s 0
  simp only [intervalTime_full] at he
  change dist (projectPoint L (f s) j) (projectPoint L (f 0) j)=|f s j-f 0 j| at he
  change |f s j-f 0 j|≤20
  rw [←he]
  have hd' := intervalDistance_le 0 1 s 0 (projectCurve L f)
  simp only [intervalTime_full] at hd'
  exact (CellOrbital.dist_coord_le_torusDistance L _ _ j).trans (hd'.trans hd)

lemma scalar_dist_eq {L : Length} (x y : ℝ) (h : |x-y|≤L.val/2) :
    dist (x : AddCircle L.val) (y : AddCircle L.val)=|x-y| := by
  have he := (AddCircle.norm_coe_eq_abs_iff L.val L.property.ne').mpr
    (show |x-y|≤|L.val|/2 by simpa only [abs_of_pos L.property] using h)
  simpa only [AddCircle.coe_sub,dist_eq_norm] using he

lemma local_norm_le_torus {L : Length} (hL : 50<L.val) (x v : Point)
    (hx : ‖x-v‖≤23) : ‖x-v‖≤torusDistance L (projectPoint L x) (projectPoint L v) := by
  apply (pi_norm_le_iff_of_nonneg (torusDistance_nonnegative _ _ _)).mpr
  intro j
  have hb : ‖(x-v) j‖≤23 := (norm_le_pi_norm (x-v) j).trans hx
  have hbound : |x j-v j|≤23 := hb
  have he : dist (projectPoint L x j) (projectPoint L v j)=|x j-v j| :=
    scalar_dist_eq (x j) (v j) (by linarith)
  change |x j-v j|≤_
  rw [←he]
  exact CellOrbital.dist_coord_le_torusDistance L _ _ j

lemma confined_lift {L : Length} (hL : 50<L.val) (v : Point) (f : C(Time,Point))
    (h0 : ‖f 0-v‖≤3)
    (hc : ∀s : Time,torusDistance L (projectPoint L (f s)) (projectPoint L v)≤10) :
    TrialConfined L v f := by
  have hd := tube_diameter (projectCurve L f) (projectPoint L v) hc
  intro s
  refine ⟨?_,hc s⟩
  have hin := lift_norm_increment hL f hd s
  have h23 : ‖f s-v‖≤23 := by
    have htri := norm_sub_le (f s - f 0) (v - f 0)
    have he : f s-v = (f s-f 0)-(v-f 0) := by abel
    have hev : ‖v-f 0‖=‖f 0-v‖ := norm_sub_rev _ _
    rw [←he,hev] at htri
    linarith
  exact (local_norm_le_torus hL (f s) v h23).trans (hc s)

end HardSphere.Bridge

end
end

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Orbitals_CenteredCell
attribute [-instance] _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Rescaling.config_haar _root_.OAI.HardSphere.bridgeEndpointBase_finite _root_.OAI.HardSphere.endpointWeightedBase_sfinite _root_.OAI.HardSphere.freePathLaw_finite_deletion _root_.OAI.HardSphere.killedPathLaw_finite_deletion
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
namespace HardSphere.CellOrbital
open MeasureTheory Set Filter
noncomputable section

lemma centered_rep_abs (L : Length) (x : AddCircle L.val) :
    |((AddCircle.equivIco L.val (-L.val/2)) x).val|=‖x‖ := by
  let t := (AddCircle.equivIco L.val (-L.val/2)) x
  have ht : |t.val| ≤ |L.val|/2 := by
    rw [abs_of_pos L.property,abs_le]
    constructor <;> linarith [t.property.1,t.property.2]
  have he := (AddCircle.norm_coe_eq_abs_iff L.val L.property.ne').mpr ht
  rw [AddCircle.coe_equivIco] at he
  exact he.symm

end
end HardSphere.CellOrbital

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
-- module Solutions.OAIQ054_HS.HardSphere_PathBounds_VisitCounts
attribute [-instance] _root_.OAI.HardSphere.Bridge.exposedBridgeKernel_markov _root_.OAI.HardSphere.Bridge.exposedPeriodSingle_finite _root_.OAI.HardSphere.Bridge.exposedTrialKernel_markov _root_.OAI.HardSphere.Bridge.instBorelSpaceContinuousMapElemRealTimePoint _root_.OAI.HardSphere.Bridge.instIsProbabilityMeasureNoiseLaw _root_.OAI.HardSphere.Bridge.instMeasurableSpaceContinuousMapElemRealTimePoint _root_.OAI.HardSphere.Bridge.parameterBridgeKernel_markov _root_.OAI.HardSphere.Bridge.parameterIndividualReference_finite _root_.OAI.HardSphere.Bridge.parameterTrialKernel_markov _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Bridge.trialKernel_markov _root_.OAI.HardSphere.Groups.cellPathReference_probability _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Rescaling.config_haar _root_.OAI.HardSphere.Wiener.bridgeLaw_isGaussian _root_.OAI.HardSphere.bridgeEndpointBase_finite _root_.OAI.HardSphere.coordinateBridge_probability _root_.OAI.HardSphere.endpointWeightedBase_sfinite
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
namespace HardSphere.Groups
open Wiener CellOrbital PathCutoff FreeVisits
attribute [local instance] Classical.propDecidable

lemma centeredCell_distance {L : Length} {c x : Torus L} (hx : x∈centeredCell L c) :
    torusDistance L x c≤1 := by
  have hd (j : Fin 3) : dist (x j) (c j)≤(1/2:ℝ) := by
    rw [dist_eq_norm,←centered_rep_abs]
    exact abs_le.mpr ⟨by linarith [(hx j).1], (hx j).2.le⟩
  unfold torusDistance
  apply Real.sqrt_le_one.mpr
  calc
    _ ≤ ∑ _j : Fin 3,(1/4:ℝ) := Finset.sum_le_sum (fun j _ ↦ by nlinarith [dist_nonneg (x:=x j) (y:=c j),hd j])
    _ ≤ 1 := by norm_num

lemma smallDiameter_distance {L : Length} (ω : ConfigurationPath 1 L)
    (h : intervalDiameter 0 1 ω≤1) (s q : Time) : torusDistance L (ω s 0) (ω q 0)≤1 := by
  have hh := (intervalDistance_le 0 1 s q ω).trans h
  simpa only [intervalTime_zero_one] using hh

lemma eligible_of_not_discarded {N K : ℕ} [Nontrivial (Fin N)] {L : Length}
    (m : ℕ) (r R C S s₀ : ℝ) (u : Time) (v : Fin 3→Fin K) (ω : ConfigurationPath N L)
    (hreg : ∀i,pathVisitsBall L 12 (gridCenter L v) i ω→Regular m r R C u S (onePathAt i ω))
    (i : Fin N) (hy : ω 0 i∈centeredCell L (gridCenter L v))
    (hY : i∉localCloseLabels L s₀ (gridCenter L v) (ω 0))
    (hZ : i∉localCloseLabels L s₀ (gridCenter L v) (ω 1))
    (hshort : i∉longVisitors (gridCenter L v) ω) : Eligible m r R C S s₀ u v i ω := by
  have hyc := centeredCell_distance hy
  have hv : pathVisitsBall L 12 (gridCenter L v) i ω := ⟨0,by linarith⟩
  have hsmall : intervalDiameter 0 1 (onePathAt i ω)≤1 := by
    by_contra! h
    exact hshort (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hv,h⟩)
  have hd (s : Time) : torusDistance L (ω s i) (ω 0 i)≤1 := smallDiameter_distance (onePathAt i ω) hsmall s 0
  have hc (s : Time) : torusDistance L (ω s i) (gridCenter L v)≤2 := by
    have hh := torusDistance_triangle' L (ω s i) (ω 0 i) (gridCenter L v)
    linarith [hd s]
  have hNY : s₀<nearestParticleDistance L (ω 0) i := by
    by_contra! hh
    apply hY
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,by linarith,hh⟩
  have hNZ : s₀<nearestParticleDistance L (ω 1) i := by
    by_contra! hh
    apply hZ
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,by linarith [hc 1],hh⟩
  refine ⟨⟨hy,by linarith [hc 1],?_⟩,hreg i hv,?_⟩
  · intro j hji
    exact ⟨hNY.trans_le (nearestParticleDistance_le L (ω 0) i j hji),
      hNZ.trans_le (nearestParticleDistance_le L (ω 1) i j hji)⟩
  · intro s
    exact (hc s).trans (by norm_num)

lemma certificate_eligible_count {N K : ℕ} [Nontrivial (Fin N)] {L : Length}
    (m : ℕ) (r R C S s₀ ell θ H D : ℝ) (u : Time) (v : Fin 3→Fin K)
    (ω : ConfigurationPath N L) (h : Certificate m r R C S s₀ ell θ H D u v ω) :
    (ell-3*θ)*D≤((eligibleList m r R C S s₀ u v ω).card:ℝ) := by
  let E := eligibleList m r R C S s₀ u v ω
  let A := localCloseLabels L s₀ (gridCenter L v) (ω 0)
  let B := localCloseLabels L s₀ (gridCenter L v) (ω 1)
  let T := longVisitors (gridCenter L v) ω
  have hsub : Finset.univ.filter (fun i ↦ ω 0 i∈centeredCell L (gridCenter L v))⊆((E∪A)∪B)∪T := by
    intro i hi
    by_cases he : i∈E
    · simp [he]
    by_cases ha : i∈A
    · simp [ha]
    by_cases hb : i∈B
    · simp [hb]
    by_cases ht : i∈T
    · simp [ht]
    exfalso
    exact he (Finset.mem_filter.mpr ⟨Finset.mem_univ _,eligible_of_not_discarded m r R C S s₀ u v ω
      h.regular i (Finset.mem_filter.mp hi).2 ha hb ht⟩)
  have hcard : centeredCount L (gridCenter L v) (ω 0)≤E.card+A.card+B.card+T.card := by
    apply (Finset.card_le_card hsub).trans
    exact (Finset.card_union_le _ _).trans (Nat.add_le_add_right
      ((Finset.card_union_le _ _).trans (Nat.add_le_add_right (Finset.card_union_le _ _) _)) _)
  have hc : (centeredCount L (gridCenter L v) (ω 0):ℝ)≤(E.card:ℝ)+(A.card:ℝ)+(B.card:ℝ)+(T.card:ℝ) := by exact_mod_cast hcard
  have h1 := h.low
  have h2 := h.closeY
  have h3 := h.closeZ
  have h4 := h.long
  change _≤(E.card:ℝ)
  change (A.card:ℝ)<θ*D at h2
  change (B.card:ℝ)<θ*D at h3
  change (T.card:ℝ)<θ*D at h4
  nlinarith

end HardSphere.Groups

end
end

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Allocation_CertificateMeasurable
attribute [-instance] _root_.OAI.HardSphere.Bridge.exposedBridgeKernel_markov _root_.OAI.HardSphere.Bridge.exposedPeriodSingle_finite _root_.OAI.HardSphere.Bridge.exposedTrialKernel_markov _root_.OAI.HardSphere.Bridge.parameterBridgeKernel_markov _root_.OAI.HardSphere.Bridge.parameterIndividualReference_finite _root_.OAI.HardSphere.Bridge.parameterTrialKernel_markov _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Bridge.targetUniform_finite _root_.OAI.HardSphere.Comparison.parameterTargetKernel_finite _root_.OAI.HardSphere.Groups.cellPathReference_probability _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Rescaling.config_haar _root_.OAI.HardSphere.bridgeEndpointBase_finite _root_.OAI.HardSphere.endpointWeightedBase_sfinite
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
namespace HardSphere.Groups
open Wiener PathCutoff CellOrbital BathSlice

lemma regular_mono_constants {L : Length} {m : ℕ} {r R C R' C' S : ℝ} {u : Time}
    {ω : ConfigurationPath 1 L} (hR : R≤R') (hC : C≤C')
    (h : Regular m r R C u S ω) : Regular m r R' C' u S ω := by
  refine ⟨⟨fun j ↦ (h.1.1 j).trans hR,?_⟩,h.2⟩
  exact h.1.2.trans (mul_le_mul_of_nonneg_right hC (Nat.cast_nonneg _))

end HardSphere.Groups

end
end

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology
namespace HardSphere.Groups
open Wiener Bridge GaussianPacking PathCutoff CellOrbital

lemma projection_square_distance (L : Length) (x y : Point) :
    (torusDistance L (projectPoint L x) (projectPoint L y))^2 ≤ square (x-y) := by
  rw [torusDistance,Real.sq_sqrt (Finset.sum_nonneg (fun _ _ ↦ sq_nonneg _))]
  unfold square
  apply Finset.sum_le_sum
  intro j _
  have h : dist (projectPoint L x j) (projectPoint L y j) ≤ |x j-y j| := by
    rw [dist_eq_norm]
    change ‖(x j:AddCircle L.val)-(y j:AddCircle L.val)‖ ≤ _
    rw [←AddCircle.coe_sub]
    exact QuotientAddGroup.norm_mk_le_norm
  simpa only [Pi.sub_apply,sq_abs] using pow_le_pow_left₀ dist_nonneg h 2

lemma eligible_near_lift {N K : ℕ} {L : Length} (hL : 50<L.val)
    (m : ℕ) (r R C S s₀ : ℝ) (u : Time) (v : Fin 3 → Fin K)
    (c : Point) (hc : projectPoint L c=gridCenter L v)
    (i : Fin N) (ω : ConfigurationPath N L) (hi : Eligible m r R C S s₀ u v i ω) :
    ∃f : C(Time,Point),projectCurve L f=onePathAt i ω ∧
      ‖f 0-c‖ ≤ 1 ∧ ‖f 1-c‖ ≤ 3 ∧ TrialConfined L c f := by
  let y := nearestLift L c (ω 0 i)
  have hyc : ‖y-c‖ ≤ 1 := nearestLift_bound L c (ω 0 i) (by rw [hc]; exact centeredCell_distance hi.1.1)
  obtain ⟨ζ,hζ,hζ0⟩ := exists_pathLift_at (onePathAt i ω) y (nearestLift_project L c (ω 0 i))
  let f : C(Time,Point) := ⟨fun s j ↦ ζ j s,by fun_prop⟩
  have hf : projectCurve L f=onePathAt i ω := by
    ext s k j
    fin_cases k
    exact hζ j s
  have hf0 : f 0=y := hζ0
  have hp (s : Time) : projectPoint L (f s)=ω s i := by
    exact congrArg (fun g : ConfigurationPath 1 L ↦ g s 0) hf
  have hconf := confined_lift hL c f (by rw [hf0]; exact hyc.trans (by norm_num))
    (fun s ↦ by rw [hp,hc]; exact hi.2.2 s)
  refine ⟨f,hf,by rw [hf0]; exact hyc,?_,hconf⟩
  have hl := local_norm_le_torus hL (f 1) c ((hconf 1).1.trans (by norm_num))
  have he : projectPoint L (f 1)=ω 1 i := by
    have hh := congrArg (fun g : ConfigurationPath 1 L ↦ g 1 0) hf
    exact hh
  rw [he,hc] at hl
  exact hl.trans hi.1.2.1

end HardSphere.Groups

end
end

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Allocation_CertificateTrialGeometry
attribute [-instance] _root_.OAI.HardSphere.Bridge.exposedBridgeKernel_markov _root_.OAI.HardSphere.Bridge.exposedPeriodSingle_finite _root_.OAI.HardSphere.Bridge.exposedTrialKernel_markov _root_.OAI.HardSphere.Bridge.parameterBridgeKernel_markov _root_.OAI.HardSphere.Bridge.parameterIndividualReference_finite _root_.OAI.HardSphere.Bridge.parameterTrialKernel_markov _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Bridge.targetUniform_finite _root_.OAI.HardSphere.Comparison.parameterTargetKernel_finite _root_.OAI.HardSphere.Groups.cellPathReference_probability _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Rescaling.config_haar _root_.OAI.HardSphere.bridgeEndpointBase_finite _root_.OAI.HardSphere.endpointWeightedBase_sfinite
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
namespace HardSphere.Groups
open Wiener Bridge GaussianPacking PathCutoff CellOrbital FreeVisits
attribute [local instance] Classical.propDecidable

lemma certificate_trial_geometry {N K m : ℕ} [Nontrivial (Fin N)] {L : Length}
    (hL : 50 < L.val) (q : ℕ) (r R C S s₀ ell θ H D : ℝ) (hs₀ : 0 ≤ s₀)
    (u : Time) (v : Fin 3→Fin K) (c : Point) (hc : projectPoint L c=gridCenter L v)
    (ω : ConfigurationPath N L) (cert : Certificate q r R C S s₀ ell θ H D u v ω)
    (label : Fin m→Fin N) (hinj : Function.Injective label)
    (hel : ∀i,Eligible q r R C S s₀ u v (label i) ω) (hiso : r+2*S < s₀) :
    ∃y z : Fin m→Point,
      (∀i,projectPoint L (y i)=ω 0 (label i)) ∧
      (∀i,projectPoint L (z i)=ω 1 (label i)) ∧
      (∀i,‖y i-c‖ ≤ 3) ∧ (∀i,‖z i-c‖ ≤ 3) ∧
      (∀i j,i≠j → s₀^2 ≤ square (y i-y j)) ∧
      (∀i j,i≠j → s₀^2 ≤ square (z i-z j)) ∧
      ((visitors (gridCenter L v) ω).card:ℝ) ≤ H*D ∧
      (∀j∈visitors (gridCenter L v) ω,Regular q r R C u S (onePathAt j ω)) ∧
      (∀j∈visitors (gridCenter L v) ω,∀i,j≠label i →
        r+2*S < torusDistance L (projectPoint L (y i)) (onePathAt j ω 0 0)) ∧
      (∀j∈visitors (gridCenter L v) ω,∀i,j≠label i →
        r+2*S < torusDistance L (projectPoint L (z i)) (onePathAt j ω 1 0)) ∧
      (∀j,j∉visitors (gridCenter L v) ω → ∀s,
        12 < torusDistance L (onePathAt j ω s 0) (projectPoint L c)) := by
  choose f hf hfY hfZ hfC using (fun i ↦ eligible_near_lift hL q r R C S s₀ u v c hc (label i) ω (hel i))
  have hp (i : Fin m) (s : Time) : projectPoint L (f i s)=ω s (label i) :=
    congrArg (fun g : ConfigurationPath 1 L ↦ g s 0) (hf i)
  refine ⟨(fun i ↦ f i 0),(fun i ↦ f i 1),(fun i ↦ hp i 0),(fun i ↦ hp i 1),
    (fun i ↦ (hfY i).trans (by norm_num)),hfZ,?_,?_,cert.visit,?_,?_,?_,?_⟩
  · intro i j hij
    have hji : label j≠label i := by intro hh; exact hij (hinj hh.symm)
    have hd := ((hel i).1.2.2 (label j) hji).1
    have hh := projection_square_distance L (f i 0) (f j 0)
    rw [hp,hp] at hh
    exact (pow_le_pow_left₀ hs₀ hd.le 2).trans hh
  · intro i j hij
    have hji : label j≠label i := by intro hh; exact hij (hinj hh.symm)
    have hd := ((hel i).1.2.2 (label j) hji).2
    have hh := projection_square_distance L (f i 1) (f j 1)
    rw [hp,hp] at hh
    exact (pow_le_pow_left₀ hs₀ hd.le 2).trans hh
  · intro j hj
    exact cert.regular j (Finset.mem_filter.mp hj).2
  · intro j _ i hji
    rw [hp]
    exact hiso.trans ((hel i).1.2.2 j hji).1
  · intro j _ i hji
    rw [hp]
    exact hiso.trans ((hel i).1.2.2 j hji).2
  · intro j hj s
    rw [hc]
    by_contra! hh
    exact hj (Finset.mem_filter.mpr ⟨Finset.mem_univ _,⟨s,hh⟩⟩)

lemma eligible_in_visitors {N K : ℕ} {L : Length}
    (q : ℕ) (r R C S s₀ : ℝ) (u : Time) (v : Fin 3→Fin K)
    (ω : ConfigurationPath N L) {i : Fin N} (hi : Eligible q r R C S s₀ u v i ω) :
    i∈visitors (gridCenter L v) ω := by
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _,⟨0,?_⟩⟩
  have hh := centeredCell_distance hi.1.1
  linarith

lemma eligible_list_size {N K m : ℕ} [Nontrivial (Fin N)] {L : Length}
    (q : ℕ) (r R C S s₀ ell θ H D : ℝ) (hD : 0 ≤ D) (hθ : θ ≤ ell/6)
    (u : Time) (v : Fin 3→Fin K) (ω : ConfigurationPath N L)
    (cert : Certificate q r R C S s₀ ell θ H D u v ω)
    (label : Fin m→Fin N) (hinj : Function.Injective label)
    (himage : Finset.univ.image label=eligibleList q r R C S s₀ u v ω) :
    ell*D/2 ≤ (m:ℝ) ∧ (m:ℝ) ≤ H*D ∧
      ∀i,Eligible q r R C S s₀ u v (label i) ω := by
  have hel (i : Fin m) : Eligible q r R C S s₀ u v (label i) ω := by
    apply (Finset.mem_filter.mp (show label i∈eligibleList q r R C S s₀ u v ω from ?_)).2
    rw [←himage]
    exact Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩
  have hcard : (eligibleList q r R C S s₀ u v ω).card=m := by
    rw [←himage,Finset.card_image_of_injective _ hinj,Finset.card_univ,Fintype.card_fin]
  have hlo := certificate_eligible_count q r R C S s₀ ell θ H D u v ω cert
  rw [hcard] at hlo
  have hsub : eligibleList q r R C S s₀ u v ω⊆visitors (gridCenter L v) ω := by
    intro i hi
    exact eligible_in_visitors q r R C S s₀ u v ω (Finset.mem_filter.mp hi).2
  have hhi := Finset.card_le_card hsub
  rw [hcard] at hhi
  have hhi' : (m:ℝ) ≤ ((visitors (gridCenter L v) ω).card:ℝ) := by exact_mod_cast hhi
  refine ⟨?_,hhi'.trans cert.visit,hel⟩
  have hh := mul_le_mul_of_nonneg_right hθ hD
  nlinarith

end HardSphere.Groups

end
end

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Bridges_Geometry
attribute [-instance] _root_.OAI.HardSphere.Groups.labelOptionSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open Filter MeasureTheory
open scoped Topology
namespace HardSphere.Bridge

lemma power_div_identity {D : ℝ} (hD : 0 < D) (p : ℝ) :
    D^p/D = D^(p-1) := by
  rw [Real.rpow_sub hD,Real.rpow_one]

lemma source_geometry_eventually {A b t : ℝ} (hA : 0 < A) (hb : 0 < b) (ht : 0 < t) :
    ∀ᶠ D : ℝ in atTop,
      1 ≤ D ∧ A/D ≤ 1 ∧ (A/D)^2 ≤ t ∧
      (A/D)*D^(1/12:ℝ) ≤ 1 ∧ 2*A^2 ≤ D ∧ 8*A^2 ≤ D ∧
      26*(A/D) ≤ t ∧ (13+Real.sqrt (2*t)*D^(1/12:ℝ))*(A/D) ≤ t ∧
      (D⁻¹/t)*13 ≤ (b*D^(-(1/3):ℝ)/8)/12 ∧
      3*(1+D^(1/12:ℝ)/6) ≤ D^(1/12:ℝ) ∧
      A/D+2*(b*D^(-(1/3):ℝ)/8) < b*D^(-(1/3):ℝ) := by
  have h1 : Tendsto (fun D : ℝ ↦ A/D) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv] using tendsto_inv_atTop_zero.const_mul A
  have h2 : Tendsto (fun D : ℝ ↦ A*D^(-(11/12):ℝ)) atTop (𝓝 0) := by
    simpa using (tendsto_rpow_neg_atTop (by norm_num : (0:ℝ) < 11/12)).const_mul A
  have h3 : Tendsto (fun D : ℝ ↦ 13*(A/D)+Real.sqrt (2*t)*(A*D^(-(11/12):ℝ))) atTop (𝓝 0) := by
    simpa using (h1.const_mul 13).add (h2.const_mul (Real.sqrt (2*t)))
  have h4 : Tendsto (fun D : ℝ ↦ D^(-(2/3):ℝ)) atTop (𝓝 0) :=
    tendsto_rpow_neg_atTop (by norm_num)
  have h5 : Tendsto (fun D : ℝ ↦ D^(1/12:ℝ)) atTop atTop :=
    tendsto_rpow_atTop (by norm_num)
  filter_upwards [eventually_ge_atTop (1:ℝ),h1.eventually (gt_mem_nhds (by norm_num : (0:ℝ) < 1)),
    (h1.pow 2).eventually (gt_mem_nhds (by simpa using ht)),
    h2.eventually (gt_mem_nhds (by norm_num : (0:ℝ) < 1)),
    eventually_ge_atTop (8*A^2),
    (h1.const_mul 26).eventually (gt_mem_nhds (by simpa using ht)),
    h3.eventually (gt_mem_nhds ht),
    h4.eventually (gt_mem_nhds (by positivity : (0:ℝ) < b*t/(96*13))),
    h5.eventually (eventually_ge_atTop (6:ℝ)),
    h4.eventually (gt_mem_nhds (by positivity : (0:ℝ) < 3*b/(4*A)))] with D hD hd1 hd2 hd3 hd4 hd5 hd6 hd7 hd8 hd9
  have hDp : 0 < D := zero_lt_one.trans_le hD
  have hp : (A/D)*D^(1/12:ℝ)=A*D^(-(11/12):ℝ) := by
    calc
      _ = A*(D^(1/12:ℝ)/D) := by ring
      _ = _ := by rw [power_div_identity hDp]; norm_num
  have hq : D⁻¹ = D^(-(2/3):ℝ)*D^(-(1/3):ℝ) := by
    rw [←Real.rpow_add hDp]
    norm_num [Real.rpow_neg_one]
  refine ⟨hD,hd1.le,hd2.le,by rw [hp]; exact hd3.le,by nlinarith,hd4,hd5.le,?_,?_,by linarith,?_⟩
  · have he : (13+Real.sqrt (2*t)*D^(1/12:ℝ))*(A/D)=
        13*(A/D)+Real.sqrt (2*t)*(A*D^(-(11/12):ℝ)) := by rw [←hp]; ring
    rw [he]
    exact hd6.le
  · have hh := (lt_div_iff₀ (by norm_num : (0:ℝ) < 96*13)).mp hd7
    rw [hq]
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ ht).mpr
    have hmul := mul_le_mul_of_nonneg_right hh.le (by positivity : 0 ≤ D^(-(1/3):ℝ))
    nlinarith
  · have hh := (lt_div_iff₀ (by positivity : (0:ℝ) < 4*A)).mp hd9
    have hmul := mul_lt_mul_of_pos_right hh (by positivity : 0 < D^(-(1/3):ℝ))
    rw [div_eq_mul_inv,hq]
    nlinarith

lemma source_trial_geometry {A b t : ℝ} (hA : 0 < A) (hb : 0 < b) (ht : 0 < t) :
    ∀ᶠ D : ℝ in atTop, ∀α : ℝ,0 < α → α ≤ A →
      let r := α/D
      let n := ⌈t/r^2⌉₊
      1 ≤ D ∧ 0 < n ∧ r ≤ 1 ∧ r*D^(1/12:ℝ) ≤ 1 ∧
      t/(n:ℝ) ≤ r^2 ∧ (n:ℝ)*r^2 ≤ 2*t ∧
      0 ≤ D⁻¹/t ∧ D⁻¹/t ≤ 1 ∧
      2*(t/(n:ℝ)) ≤ D⁻¹ ∧ 8*t ≤ (n:ℝ)*D⁻¹ ∧
      2*13/(n:ℝ) ≤ r ∧ (13+Real.sqrt (2*t)*D^(1/12:ℝ))/(n:ℝ) ≤ r ∧
      (D⁻¹/t)*13 ≤ (b*D^(-(1/3):ℝ)/8)/12 ∧
      3*(1+D^(1/12:ℝ)/6) ≤ D^(1/12:ℝ) ∧
      r+2*(b*D^(-(1/3):ℝ)/8) < b*D^(-(1/3):ℝ) := by
  filter_upwards [source_geometry_eventually hA hb ht,eventually_ge_atTop t⁻¹] with D h hd
  rcases h with ⟨hD,hA1,hAsq,hAR,hD2,hD8,h26,hQ,hwin,hrelax,hiso⟩
  intro α hα hαA
  dsimp only
  let r := α/D
  let n := ⌈t/r^2⌉₊
  have hDp : 0 < D := zero_lt_one.trans_le hD
  have hr : 0 < r := by dsimp [r]; positivity
  have hrA : r ≤ A/D := div_le_div_of_nonneg_right hαA hDp.le
  have hn : 0 < n := Nat.ceil_pos.mpr (by positivity : 0 < t/r^2)
  have hnp : 0 < (n:ℝ) := by exact_mod_cast hn
  have hnr : t ≤ (n:ℝ)*r^2 := by
    have hh := (div_le_iff₀ (sq_pos_of_pos hr)).mp (Nat.le_ceil (t/r^2))
    exact hh
  have hτ : t/(n:ℝ) ≤ r^2 := (div_le_iff₀ hnp).mpr (by nlinarith [hnr])
  have hrs : r^2 ≤ t := (pow_le_pow_left₀ hr.le hrA 2).trans hAsq
  have hup : (n:ℝ)*r^2 ≤ 2*t := by
    have hh := mul_le_mul_of_nonneg_right (Nat.ceil_lt_add_one (by positivity : 0 ≤ t/r^2)).le (sq_nonneg r)
    have he : (t/r^2+1)*r^2=t+r^2 := by field_simp
    rw [he] at hh
    nlinarith
  have hsq : r^2 ≤ D⁻¹/8 := by
    calc
      _ ≤ (A/D)^2 := pow_le_pow_left₀ hr.le hrA 2
      _ ≤ (1/8)/D := by
        apply (le_div_iff₀ hDp).mpr
        have he : (A/D)^2*D=A^2/D := by field_simp
        rw [he]
        exact (div_le_iff₀ hDp).mpr (by linarith)
      _ = _ := by ring
  have htime : D⁻¹/t ≤ 1 := by
    apply (div_le_iff₀ ht).mpr
    simp only [one_mul]
    rw [←one_div]
    apply (div_le_iff₀ hDp).mpr
    have hh := mul_le_mul_of_nonneg_left hd ht.le
    simpa [mul_inv_cancel₀ ht.ne'] using hh
  have hsmall : r*D^(1/12:ℝ) ≤ 1 := (mul_le_mul_of_nonneg_right hrA (by positivity)).trans hAR
  have hdr : 26/(n:ℝ) ≤ r := by
    apply (div_le_iff₀ hnp).mpr
    have hh : 26*r ≤ t := (mul_le_mul_of_nonneg_left hrA (by norm_num)).trans h26
    nlinarith
  have hdr' : (13+Real.sqrt (2*t)*D^(1/12:ℝ))/(n:ℝ) ≤ r := by
    apply (div_le_iff₀ hnp).mpr
    have hq : 0 ≤ 13+Real.sqrt (2*t)*D^(1/12:ℝ) := by positivity
    have hh := (mul_le_mul_of_nonneg_left hrA hq).trans hQ
    nlinarith
  refine ⟨hD,hn,hrA.trans hA1,hsmall,hτ,hup,by positivity,htime,?_,?_,?_,hdr',hwin,hrelax,?_⟩
  · change 2*(t/(n:ℝ)) ≤ D⁻¹
    nlinarith [inv_pos.mpr hDp]
  · change 8*t ≤ (n:ℝ)*D⁻¹
    have hh := mul_le_mul_of_nonneg_left hsq hnp.le
    nlinarith
  · change 2*13/(n:ℝ) ≤ r
    convert hdr using 1
    all_goals try with_reducible_and_instances rfl
    norm_num
  · change r+2*(b*D^(-(1/3):ℝ)/8) < b*D^(-(1/3):ℝ)
    linarith

end HardSphere.Bridge

end
end

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Bridges_NumericalSupply
attribute [-instance] _root_.OAI.HardSphere.Groups.labelOptionSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open Filter MeasureTheory
open scoped Topology
namespace HardSphere.Bridge

lemma separation_inverse_cube {D b : ℝ} (hD : 0 < D) :
    ((b*D^(-(1/3):ℝ))⁻¹)^3=b⁻¹^3*D := by
  have hp : ((D^(-(1/3):ℝ))⁻¹)^3 = D := by
    rw [←Real.rpow_neg hD.le,←Real.rpow_natCast,←Real.rpow_mul hD.le]
    norm_num
  rw [mul_inv,mul_pow,hp]

lemma boundary_ratio_le {D : ℝ} (hD : 1 ≤ D) :
    D⁻¹*(1+D^(1/12:ℝ))^3/Real.sqrt (D⁻¹/2)  ≤  8*Real.sqrt 2*D^(-(1/4):ℝ) := by
  have hDp : 0 < D := zero_lt_one.trans_le hD
  have hR : 1 ≤ D^(1/12:ℝ) := Real.one_le_rpow hD (by norm_num)
  have hcube : (1+D^(1/12:ℝ))^3 ≤ 8*D^(1/4:ℝ) := by
    calc
      _  ≤  (2*D^(1/12:ℝ))^3 := pow_le_pow_left₀ (by positivity) (by linarith) 3
      _ = _ := by
        have hp : (D^(1/12:ℝ))^3 = D^(1/4:ℝ) := by
          rw [←Real.rpow_natCast,←Real.rpow_mul hDp.le]
          norm_num
        rw [mul_pow,hp]
        norm_num
  have hs : Real.sqrt (D⁻¹)=D^(-(1/2):ℝ) := by
    rw [Real.sqrt_inv,Real.sqrt_eq_rpow,Real.rpow_neg hDp.le]
  calc
    _ = (1+D^(1/12:ℝ))^3*(D⁻¹/Real.sqrt (D⁻¹))*Real.sqrt 2 := by
      rw [Real.sqrt_div (inv_nonneg.mpr hDp.le)]
      simp only [div_eq_mul_inv,mul_inv,inv_inv]
      ring
    _ = (1+D^(1/12:ℝ))^3*D^(-(1/2):ℝ)*Real.sqrt 2 := by rw [Real.div_sqrt,hs]
    _  ≤  (8*D^(1/4:ℝ))*D^(-(1/2):ℝ)*Real.sqrt 2 := by gcongr
    _ = _ := by
      rw [mul_assoc (8:ℝ),←Real.rpow_add hDp]
      norm_num
      ring

lemma collision_error_majorant {D b A H C t α m : ℝ}
    (hD : 1 ≤ D) (hb : 0 < b) (hA : 0 ≤ A) (hH : 0 ≤ H) (hC : 0 ≤ C) (ht : 0 ≤ t)
    (hα : 0 ≤ α) (hαA : α ≤ A) (hm : 0 ≤ m) (hmH : m ≤ H*D) :
    8*C*t*(α/D)*(((b*D^(-(1/3):ℝ))⁻¹)^3+m)+
      8*(α/D)*(1+D^(1/12:ℝ))^3/Real.sqrt (D⁻¹/2)  ≤
        8*C*t*A*(b⁻¹^3+H)+64*A*Real.sqrt 2*D^(-(1/4):ℝ) := by
  have hDp : 0 < D := zero_lt_one.trans_le hD
  rw [separation_inverse_cube hDp]
  apply add_le_add
  · calc
      _  ≤  8*C*t*(A/D)*(b⁻¹^3*D+H*D) := by
        have hαD := div_nonneg hα hDp.le
        gcongr
      _ = _ := by field_simp
  · calc
      _  ≤  8*(A/D)*(1+D^(1/12:ℝ))^3/Real.sqrt (D⁻¹/2) := by gcongr
      _ = (8*A)*(D⁻¹*(1+D^(1/12:ℝ))^3/Real.sqrt (D⁻¹/2)) := by ring
      _  ≤  (8*A)*(8*Real.sqrt 2*D^(-(1/4):ℝ)) := mul_le_mul_of_nonneg_left (boundary_ratio_le hD) (by positivity)
      _ = _ := by ring

theorem collision_error_small {b A H C J ε : ℝ}
    (hb : 0 < b) (hA : 0 < A) (hH : 0 < H) (hC : 0 < C) (hJ : 0 < J) (hε : 0 < ε) :
    ∃ t₀ : ℝ, 0 < t₀  ∧  ∀ t : ℝ, 0 < t  →  t ≤ t₀  →  ∃ D₀ : ℝ, 1 ≤ D₀  ∧
    ∀ D α m : ℝ, D₀ ≤ D  →  0 ≤ α  →  α ≤ A  →  0 ≤ m  →  m ≤ H*D  →
      J*(8*C*t*(α/D)*(((b*D^(-(1/3):ℝ))⁻¹)^3+m)+
        8*(α/D)*(1+D^(1/12:ℝ))^3/Real.sqrt (D⁻¹/2))  ≤  ε := by
  let Q := 8*C*A*(b⁻¹^3+H)
  have hQ : 0 < Q := by dsimp [Q]; positivity
  refine ⟨ε/(2*J*Q),by positivity,?_⟩
  intro t ht htt
  have hl : Tendsto (fun D:ℝ  ↦  J*(64*A*Real.sqrt 2*D^(-(1/4):ℝ))) atTop (𝓝 0) := by
    simpa using ((tendsto_rpow_neg_atTop (by norm_num : (0:ℝ) < 1/4)).const_mul (64*A*Real.sqrt 2)).const_mul J
  obtain ⟨D₀,hD₀⟩ := eventually_atTop.1 (hl.eventually (gt_mem_nhds (by positivity : (0:ℝ) < ε/2)))
  refine ⟨max 1 D₀,le_max_left _ _,?_⟩
  intro D α m hDD hα hαA hm hmH
  have hD : 1 ≤ D := (le_max_left _ _).trans hDD
  have hd := hD₀ D ((le_max_right _ _).trans hDD)
  have hsmall : J*(8*C*t*A*(b⁻¹^3+H)) ≤ ε/2 := by
    have hh := (le_div_iff₀ (by positivity : 0 < 2*J*Q)).mp htt
    dsimp [Q] at hh
    nlinarith
  have he := mul_le_mul_of_nonneg_left (collision_error_majorant hD hb hA.le hH.le hC.le ht.le hα hαA hm hmH) hJ.le
  nlinarith

end HardSphere.Bridge

end
end

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Allocation_TargetSupply
attribute [-instance] _root_.OAI.HardSphere.Groups.labelOptionSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators
namespace HardSphere.Comparison
variable {U X : Type*} [MeasurableSpace U] [MeasurableSpace X]

lemma failure_large_of_success_small (P : Measure X) [IsProbabilityMeasure P]
    (S : Set X) (hS : MeasurableSet S) {a b : ℝ≥0∞} (hab : a+b≤1)
    (hsmall : P S<a) : b≤P Sᶜ := by
  by_contra! hb
  have hsum : P S+P Sᶜ=1 := by simpa using measure_add_measure_compl (μ:=P) hS
  have hlt := ENNReal.add_lt_add hsmall hb
  rw [hsum] at hlt
  exact (not_lt_of_ge hab) hlt

lemma bad_target_mass (μ : Measure U) (κ : Kernel U X) [IsMarkovKernel κ]
    (S : Set X) (hS : MeasurableSet S) {a b : ℝ≥0∞} (hab : a+b≤1) :
    b*μ {u | κ u S<a}≤∫⁻u,κ u Sᶜ ∂μ := by
  apply le_trans _ (mul_meas_ge_le_lintegral (κ.measurable_coe hS.compl) b)
  apply mul_le_mul_right
  apply measure_mono
  exact fun u hu ↦ failure_large_of_success_small (κ u) S hS hab hu

lemma good_target_mass_of_failure (μ : Measure U) [IsProbabilityMeasure μ]
    (κ : Kernel U X) [IsMarkovKernel κ] (S : Set X) (hS : MeasurableSet S)
    (hf : (∫⁻u,κ u Sᶜ ∂μ)≤ENNReal.ofReal (1/1000:ℝ)) :
    ENNReal.ofReal (99/100:ℝ)≤μ {u | ENNReal.ofReal (9/10:ℝ)≤κ u S} := by
  have hab : ENNReal.ofReal (9/10:ℝ)+ENNReal.ofReal (1/10:ℝ)≤1 := by
    rw [←ENNReal.ofReal_add (by norm_num : (0:ℝ)≤9/10) (by norm_num : (0:ℝ)≤1/10)]
    norm_num
  have h := (bad_target_mass μ κ S hS hab).trans hf
  have hbad : μ {u | κ u S<ENNReal.ofReal (9/10:ℝ)}≤ENNReal.ofReal (1/100:ℝ) := by
    calc
      _ = ENNReal.ofReal 10*(ENNReal.ofReal (1/10:ℝ)*μ {u | κ u S<ENNReal.ofReal (9/10:ℝ)}) := by
        rw [←mul_assoc,←ENNReal.ofReal_mul (by norm_num : (0:ℝ)≤10)]; norm_num
      _ ≤ ENNReal.ofReal 10*ENNReal.ofReal (1/1000:ℝ) := mul_le_mul_right h _
      _ = _ := by rw [←ENNReal.ofReal_mul (by norm_num : (0:ℝ)≤10)]; norm_num
  have hT : MeasurableSet {u | ENNReal.ofReal (9/10:ℝ)≤κ u S} := measurableSet_le measurable_const (κ.measurable_coe hS)
  have he : μ {u | ENNReal.ofReal (9/10:ℝ)≤κ u S}+μ {u | κ u S<ENNReal.ofReal (9/10:ℝ)}=1 := by
    simpa only [Set.compl_ofPred,not_le,measure_univ] using measure_add_measure_compl (μ:=μ) hT
  apply (ENNReal.toReal_le_toReal ENNReal.ofReal_ne_top (measure_ne_top _ _)).mp
  have her := congrArg ENNReal.toReal he
  rw [ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)] at her
  have hbadr := (ENNReal.toReal_le_toReal (measure_ne_top _ _) ENNReal.ofReal_ne_top).mpr hbad
  norm_num at her hbadr ⊢
  linarith

lemma seven_target_count {m : ℕ} (score : Fin m→Fin 7→ℝ)
    (h0 : ∀i w,0 ≤ score i w)
    (hscore : ∀w, (∑i,score i w)≤(m:ℝ)/70000) :
    ((Finset.univ.filter (fun i ↦ ∃w, (1/1000:ℝ) < score i w)).card:ℝ)≤(m:ℝ)/10 := by
  classical
  let bad : Finset (Fin m) := Finset.univ.filter (fun i ↦ ∃w, (1/1000:ℝ) < score i w)
  have hlower : (bad.card:ℝ)*(1/1000)≤∑i,∑w,score i w := by
    calc
      _ = ∑_i∈bad,(1/1000:ℝ) := by simp
      _ ≤ ∑i∈bad,∑w,score i w := by
        apply Finset.sum_le_sum
        intro i hi
        obtain ⟨w,hw⟩ := (Finset.mem_filter.mp hi).2
        exact hw.le.trans (Finset.single_le_sum (fun j _ ↦ h0 i j) (Finset.mem_univ w))
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun i _ _ ↦ Finset.sum_nonneg (fun w _ ↦ h0 i w))
  have hupper : (∑i,∑w,score i w)≤(m:ℝ)/10000 := by
    rw [Finset.sum_comm]
    calc
      _ ≤ ∑_w : Fin 7,(m:ℝ)/70000 := Finset.sum_le_sum (fun w _ ↦ hscore w)
      _ = _ := by simp; ring
  change (bad.card:ℝ)≤(m:ℝ)/10
  linarith

end HardSphere.Comparison

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

lemma successExcept_measurable {L : Length} {N : ℕ} (n : ℕ) (r R C S : ℝ) (w : Time) (v : Point)
    (ω : Fin N → ConfigurationPath 1 L) (i : Fin N) :
    MeasurableSet (SuccessExcept n r R C S w v ω i) := by
  have h : MeasurableSet {f | ∀j,j≠i → ¬TrialCollision r (ω j) f} := by
    simp only [ofPred_forall]
    exact MeasurableSet.iInter fun j ↦ MeasurableSet.iInter fun _ ↦ (trialCollision_closed r (ω j)).measurableSet.compl
  exact (trialCutoff_measurable L n r R C w S v).inter h

end HardSphere.Bridge

end
end

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Cutoffs_Mesh
attribute [-instance] _root_.OAI.HardSphere.Groups.labelOptionSpace
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
namespace HardSphere.PathCutoff

lemma sourceMesh_bounds {t r D αmin αmax : ℝ}
    (ht : 0<t) (hr : 0 < r) (hD : 1≤D) (hαmin : 0<αmin)
    (hl : αmin≤D*r) (hu : D*r≤αmax) :
    (2*t/αmax^2)*D^2≤(sourceMesh t r:ℝ) ∧
    (sourceMesh t r:ℝ)≤(2*t/αmin^2+2)*D^2 := by
  have hDp : 0<D := by linarith
  have hαmax : 0<αmax := hαmin.trans_le (hl.trans hu)
  have hsq₁ : αmin^2≤D^2*r^2 := by nlinarith [sq_nonneg (D*r-αmin)]
  have hsq₂ : D^2*r^2≤αmax^2 := by nlinarith [sq_nonneg (αmax-D*r)]
  have hlo' : (t/αmax^2)*D^2≤t/r^2 := by
    apply (le_div_iff₀ (sq_pos_of_pos hr)).mpr
    calc
      _ = t*(D^2*r^2)/αmax^2 := by ring
      _ ≤ t*αmax^2/αmax^2 := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hsq₂ ht.le) (sq_nonneg _)
      _ = t := by field_simp
  have hhi : t/r^2≤(t/αmin^2)*D^2 := by
    apply (div_le_iff₀ (sq_pos_of_pos hr)).mpr
    have hh : t*αmin^2≤t*(D^2*r^2) := mul_le_mul_of_nonneg_left hsq₁ ht.le
    have hh' := (le_div_iff₀ (sq_pos_of_pos hαmin)).mpr hh
    convert hh' using 1 <;> first | rfl | ring
  have hnlo := Nat.le_ceil (t/r^2)
  have hnhi := (Nat.ceil_lt_add_one (show 0≤t/r^2 by positivity)).le
  simp only [sourceMesh,Nat.cast_mul,Nat.cast_ofNat]
  have hDsq : 1≤D^2 := by nlinarith
  constructor
  · calc
      _ = 2*((t/αmax^2)*D^2) := by ring
      _ ≤ 2*(⌈t/r^2⌉₊:ℝ) := mul_le_mul_of_nonneg_left (hlo'.trans hnlo) (by norm_num)
  · calc
      _ ≤ 2*(t/r^2+1) := mul_le_mul_of_nonneg_left hnhi (by norm_num)
      _ ≤ 2*((t/αmin^2)*D^2+D^2) := by gcongr
      _ = _ := by ring
end HardSphere.PathCutoff

end
end

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Thermodynamics_CutoffAsymptotics
attribute [-instance] _root_.OAI.HardSphere.Groups.labelOptionSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Filter
open scoped Topology
namespace HardSphere.PathCutoff

lemma stretched_exp_decay (p : ℝ) {b q : ℝ} (hb : 0<b) (hq : 0<q) :
    Tendsto (fun D:ℝ ↦ D^p*Real.exp (-b*D^q)) atTop (𝓝 0) := by
  have ht := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (p/q) b hb).comp
    (tendsto_rpow_atTop hq)
  apply ht.congr'
  filter_upwards [eventually_ge_atTop (0:ℝ)] with D hD
  dsimp
  rw [←Real.rpow_mul hD]
  congr 2
  field_simp

end HardSphere.PathCutoff

end

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology
namespace HardSphere.PathCutoff

lemma regularScale_denominator {D : ℝ} (hD : 1≤D) :
    (1+D^(1/12:ℝ))^3≤8*D := by
  have hD0 : 0<D := lt_of_lt_of_le zero_lt_one hD
  have hp : 1≤D^(1/12:ℝ) := Real.one_le_rpow hD (by norm_num)
  have hsum : 1+D^(1/12:ℝ)≤2*D^(1/12:ℝ) := by linarith
  have hp3 : (D^(1/12:ℝ))^3=D^(1/4:ℝ) := by
    rw [←Real.rpow_natCast,←Real.rpow_mul hD0.le]
    norm_num
  calc
    _ ≤ (2*D^(1/12:ℝ))^3 := pow_le_pow_left₀ (by positivity) hsum 3
    _ = 8*D^(1/4:ℝ) := by rw [mul_pow,hp3]; norm_num
    _ ≤ 8*D := by
      gcongr
      simpa using Real.rpow_le_rpow_of_exponent_le hD (by norm_num : (1/4:ℝ)≤1)

end HardSphere.PathCutoff

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Thermodynamics_TrialScale
attribute [-instance] _root_.OAI.HardSphere.Bridge.exposedBridgeKernel_markov _root_.OAI.HardSphere.Bridge.exposedPeriodSingle_finite _root_.OAI.HardSphere.Bridge.exposedTrialKernel_markov _root_.OAI.HardSphere.Bridge.parameterBridgeKernel_markov _root_.OAI.HardSphere.Bridge.parameterIndividualReference_finite _root_.OAI.HardSphere.Bridge.parameterTrialKernel_markov _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Bridge.targetUniform_finite _root_.OAI.HardSphere.Comparison.parameterTargetKernel_finite _root_.OAI.HardSphere.Groups.cellPathReference_probability _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Rescaling.config_haar _root_.OAI.HardSphere.bridgeEndpointBase_finite _root_.OAI.HardSphere.endpointWeightedBase_sfinite
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
namespace HardSphere.Bridge
open Wiener GaussianPacking PathCutoff

lemma scaleMoment_two {t r : ℝ} (ht : 0 ≤ t) (w : Time) :
    scaleMoment 2 t r 0 w = 432*t*(w:ℝ)/r^2*normPowerMean 2 := by
  have hw : 0 ≤ (w:ℝ) := w.property.1
  unfold scaleMoment
  simp only [show ((0:Time):ℝ)=0 from rfl,sub_zero,mul_one,div_pow]
  rw [Real.sq_sqrt (by positivity : 0 ≤ 2*t*(w:ℝ))]
  ring

lemma source_window_moment {D b t : ℝ} (hD : 0 < D) (ht : 0 ≤ t)
    (w : Time) (hw : t*(w:ℝ)=D⁻¹) :
    scaleMoment 2 t (b*D^(-(1/3):ℝ)/8) 0 w =
      27648*b⁻¹^2*D^(-(1/3):ℝ)*normPowerMean 2 := by
  rw [scaleMoment_two ht]
  have hp : (D^(-(1/3):ℝ))^2=D^(-(2/3):ℝ) := by
    rw [←Real.rpow_natCast,←Real.rpow_mul hD.le]
    norm_num
  have he : D⁻¹/(D^(-(1/3):ℝ))^2=D^(-(1/3):ℝ) := by
    rw [hp,←Real.rpow_neg_one,←Real.rpow_sub hD]
    norm_num
  calc
    _ = 27648*b⁻¹^2*(D⁻¹/(D^(-(1/3):ℝ))^2)*normPowerMean 2 := by
      rw [div_pow,mul_pow]
      simp only [div_eq_mul_inv,mul_inv,inv_pow]
      rw [show 432*t*(w:ℝ)=432*D⁻¹ by rw [mul_assoc,hw]]
      ring
    _ = _ := by rw [he]

lemma trialCutoff_mono_constants {L : Length} {n : ℕ} {r R C R' C' S : ℝ}
    {w : Time} {v : Point} {f : C(Time,Point)} (hR : R ≤ R') (hC : C ≤ C')
    (h : TrialCutoff L n r R C w S v f) : TrialCutoff L n r R' C' w S v f :=
  ⟨Groups.regular_mono_constants hR hC h.1,h.2⟩

lemma scalarTrialRemainder_decay (Cn M b : ℝ) {c a : ℝ}
    (hc : 0 < c) (ha : 0 < a) :
    Tendsto (scalarTrialRemainder Cn M c a b) atTop (𝓝 0) := by
  have h₁ := (stretched_exp_decay 2 (by positivity : (0:ℝ) < c/46656)
    (by norm_num : (0:ℝ) < 1/6)).const_mul (Cn*(3*M))
  have h₂ := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 0 (a/8) (by positivity)
  have h₃ := (stretched_exp_decay 0 hc (by norm_num : (0:ℝ) < 1/6)).const_mul (3*M)
  have h₄ := (tendsto_rpow_neg_atTop (by norm_num : (0:ℝ) < 1/3)).const_mul
    (3981312*b⁻¹^2*normPowerMean 2)
  convert ((h₁.add h₂).add h₃).add h₄ using 1
  · funext D
    simp only [scalarTrialRemainder,Real.rpow_two,Real.rpow_zero,one_mul]
    ring
  · ring_nf

end HardSphere.Bridge

end
end

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Bridges_TrialScalarBound
attribute [-instance] _root_.OAI.HardSphere.Bridge.exposedBridgeKernel_markov _root_.OAI.HardSphere.Bridge.exposedPeriodSingle_finite _root_.OAI.HardSphere.Bridge.exposedTrialKernel_markov _root_.OAI.HardSphere.Bridge.parameterBridgeKernel_markov _root_.OAI.HardSphere.Bridge.parameterIndividualReference_finite _root_.OAI.HardSphere.Bridge.parameterTrialKernel_markov _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Bridge.targetUniform_finite _root_.OAI.HardSphere.Comparison.parameterTargetKernel_finite _root_.OAI.HardSphere.Groups.cellPathReference_probability _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Rescaling.config_haar _root_.OAI.HardSphere.bridgeEndpointBase_finite _root_.OAI.HardSphere.endpointWeightedBase_sfinite
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
namespace HardSphere.Bridge
open Wiener GaussianPacking PathCutoff

lemma trial_scalar_bound {D Cn M c a b t : ℝ} {n : ℕ}
    (hD : 1 ≤ D) (hM : 0 ≤ M) (hc : 0 ≤ c) (ha : 0 ≤ a) (ht : 0 ≤ t)
    (hnlo : a*D^2 ≤ (n:ℝ)) (hnhi : (n:ℝ) ≤ Cn*D^2)
    (w : Time) (hw : t*(w:ℝ)=D⁻¹) :
    (n:ℝ)*(3*M*Real.exp (-c*((D^(1/12:ℝ)/6)/36)^2))+
      Real.exp (-(n:ℝ)/((1+D^(1/12:ℝ)/6)^3))+
      3*(M*Real.exp (-c*(D^(1/12:ℝ))^2))+
      scaleMoment 2 t (b*D^(-(1/3):ℝ)/8) 0 w/(1/12:ℝ)^2+
      scaleMoment 2 t 1 0 1/(1/3:ℝ)^2 ≤
      scalarTrialRemainder Cn M c a b D+3888*t*normPowerMean 2 := by
  obtain ⟨rate, rfl⟩ : ∃ rate : ℝ, rate^2 = c := ⟨Real.sqrt c, Real.sq_sqrt hc⟩
  have hDp : 0 < D := zero_lt_one.trans_le hD
  have hRD : 0 ≤ D^(1/12:ℝ) := Real.rpow_nonneg hDp.le _
  have hp : (D^(1/12:ℝ))^2=D^(1/6:ℝ) := by
    rw [←Real.rpow_natCast,←Real.rpow_mul hDp.le]
    norm_num
  have hs : ((D^(1/12:ℝ)/6)/36)^2=D^(1/6:ℝ)/46656 := by
    rw [div_pow,div_pow,hp]
    ring
  have hden : 0 < (1+D^(1/12:ℝ)/6)^3 := by positivity
  have hdenb : (1+D^(1/12:ℝ)/6)^3 ≤ 8*D := by
    exact (pow_le_pow_left₀ (by positivity) (by linarith :
      1+D^(1/12:ℝ)/6 ≤ 1+D^(1/12:ℝ)) 3).trans (regularScale_denominator hD)
  have hexp : Real.exp (-(n:ℝ)/((1+D^(1/12:ℝ)/6)^3)) ≤ Real.exp (-(a/8)*D) := by
    have hh : a/8*D ≤ (n:ℝ)/((1+D^(1/12:ℝ)/6)^3) := by
      apply (le_div_iff₀ hden).mpr
      calc
        _ ≤ (a/8*D)*(8*D) := mul_le_mul_of_nonneg_left hdenb (by positivity)
        _ = a*D^2 := by ring
        _ ≤ _ := hnlo
    apply Real.exp_le_exp.mpr
    rw [neg_div]
    linarith
  rw [hs,hp,source_window_moment hDp ht w hw,scaleMoment_two ht]
  simp only [show ((1:Time):ℝ)=1 from rfl,mul_one,one_pow,div_one]
  have hfirst : (n:ℝ)*(3*M*Real.exp (-rate^2*(D^(1/6:ℝ)/46656))) ≤
      Cn*D^2*(3*M)*Real.exp (-(rate^2/46656)*D^(1/6:ℝ)) := by
    have hh := mul_le_mul_of_nonneg_right hnhi (by positivity : 0 ≤ 3*M*Real.exp (-rate^2*(D^(1/6:ℝ)/46656)))
    simpa only [show -rate^2*(D^(1/6:ℝ)/46656)=-(rate^2/46656)*D^(1/6:ℝ) by ring,mul_assoc] using hh
  unfold scalarTrialRemainder
  norm_num only [div_pow,one_pow] at *
  linarith

end HardSphere.Bridge

end
end

section
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.Bridge
open Wiener GaussianPacking PathCutoff

lemma trial_remainder_small {ε : ℝ} (hε : 0 < ε) :
    ∃t₀ : ℝ,0 < t₀ ∧ ∀t : ℝ,0 < t → t ≤ t₀ →
    ∀Cn M c a b : ℝ,0 < c → 0 < a → ∃D₀ : ℝ,1 ≤ D₀ ∧ ∀D : ℝ,D₀ ≤ D →
      2*(scalarTrialRemainder Cn M c a b D+3888*t*normPowerMean 2) ≤ ε := by
  have hn := normPowerMean_nonneg 2
  let Q := 3888*(normPowerMean 2+1)
  have hQ : 0 < Q := by dsimp [Q]; positivity
  refine ⟨ε/(4*Q),by positivity,?_⟩
  intro t ht htt Cn M c a b hc ha
  obtain ⟨D₀,hD₀⟩ := eventually_atTop.1 ((scalarTrialRemainder_decay Cn M b hc ha).eventually
    (gt_mem_nhds (by positivity : (0:ℝ) < ε/4)))
  refine ⟨max 1 D₀,le_max_left _ _,?_⟩
  intro D hD
  have hd := hD₀ D ((le_max_right _ _).trans hD)
  have hsmall : t*Q ≤ ε/4 := by
    have hh := (le_div_iff₀ (by positivity : 0 < 4*Q)).mp htt
    nlinarith
  dsimp [Q] at hsmall
  nlinarith

lemma sourceHalf_bounds {t r D A B : ℝ} (ht : 0 < t) (hr : 0 < r)
    (hD : 1 ≤ D) (hA : 0 < A) (hl : A ≤ D*r) (hu : D*r ≤ B) :
    (t/B^2)*D^2 ≤ (⌈t/r^2⌉₊:ℝ) ∧
      (⌈t/r^2⌉₊:ℝ) ≤ (t/A^2+1)*D^2 := by
  have hh := sourceMesh_bounds ht hr hD hA hl hu
  simp only [sourceMesh,Nat.cast_mul,Nat.cast_ofNat] at hh
  ring_nf at hh ⊢
  constructor <;> linarith [hh.1,hh.2]

end HardSphere.Bridge

end
end

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.Bridge
open Wiener GaussianPacking PathCutoff Comparison
attribute [local instance] Classical.propDecidable

lemma full_success_count {L : Length} {N m : ℕ} (n : ℕ) (t r R C S : ℝ) (w : Time)
    (y z : Fin m → Point) (v : Point) (ω : Fin N → ConfigurationPath 1 L)
    (label : Fin m → Fin N) (B : Fin 7 → Set Point)
    (hB : ∀j,MeasurableSet (B j)) (hvol : ∀j,volume (B j)=1)
    (herror : ∀j, (∑i,∫⁻u in B j,trialKernel t (y i) (z i) u
      (SuccessExcept n r R C S w v ω (label i))ᶜ)≤ENNReal.ofReal ((m:ℝ)/70000)) :
    ((Finset.univ.filter (fun i ↦ ¬StrongExcept n t r R C S w (y i) (z i) v ω (label i) B)).card:ℝ)≤(m:ℝ)/10 := by
  classical
  let f : Fin m → Fin 7 → ℝ≥0∞ := fun i j ↦ ∫⁻u in B j,
    trialKernel t (y i) (z i) u (SuccessExcept n r R C S w v ω (label i))ᶜ
  have hf_le (i : Fin m) (j : Fin 7) : f i j≤1 := by
    calc
      _ ≤ ∫⁻_ in B j,(1:ℝ≥0∞) := lintegral_mono (fun _ ↦ prob_le_one)
      _ = _ := by simp [hvol]
  have hf_fin (i : Fin m) (j : Fin 7) : f i j≠⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top (hf_le i j)
  have hsum (j : Fin 7) : (∑i,(f i j).toReal)≤(m:ℝ)/70000 := by
    rw [←ENNReal.toReal_sum (fun i _ ↦ hf_fin i j)]
    have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top (herror j)
    simpa only [f,ENNReal.toReal_ofReal (by positivity : 0≤(m:ℝ)/70000)] using hh
  have hc := seven_target_count (fun i j ↦ (f i j).toReal) (fun _ _ ↦ ENNReal.toReal_nonneg) hsum
  have hsub : Finset.univ.filter (fun i ↦ ¬StrongExcept n t r R C S w (y i) (z i) v ω (label i) B)⊆
      Finset.univ.filter (fun i ↦ ∃j,(1/1000:ℝ)<(f i j).toReal) := by
    intro i hi
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ i,?_⟩
    by_contra! hn
    have hg : StrongExcept n t r R C S w (y i) (z i) v ω (label i) B := by
      intro j
      let _ : IsProbabilityMeasure (volume.restrict (B j)) :=
        ⟨by rw [Measure.restrict_apply' (hB j), Set.univ_inter, hvol]⟩
      apply good_target_mass_of_failure _ _ _ (successExcept_measurable n r R C S w v ω (label i))
      change f i j≤ENNReal.ofReal (1/1000:ℝ)
      apply (ENNReal.toReal_le_toReal (hf_fin i j) ENNReal.ofReal_ne_top).mp
      simpa using hn j
    exact (Finset.mem_filter.mp hi).2 hg
  exact (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans hc

end HardSphere.Bridge

end
end

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Thermodynamics_SupplyCalibration
attribute [-instance] _root_.OAI.HardSphere.Groups.labelOptionSpace
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
namespace HardSphere.Bridge
open Wiener GaussianPacking PathCutoff

lemma supply_error_calibration {ell H D δ E : ℝ} {m j : ℕ}
    (hell : 0 < ell) (hH : 0 < H) (hD : 0 ≤ D) (hδ : 0 ≤ δ) (hE : 0 ≤ E)
    (hm : ell*D/2 ≤ (m:ℝ)) (hj : (j:ℝ) ≤ H*D)
    (hδsmall : δ ≤ 1/140000) (hEsmall : (4*H*hitConstant/ell)*E ≤ 1/140000) :
    (m:ℝ≥0∞)*ENNReal.ofReal δ+(j:ℝ≥0∞)*(2*ENNReal.ofReal (hitConstant*E)) ≤
      ENNReal.ofReal ((m:ℝ)/70000) := by
  have hh : 0 ≤ hitConstant := hitConstant_pos.le
  have he : 2*(j:ℝ)*(hitConstant*E) ≤ (m:ℝ)/140000 := by
    have h₁ : 2*(j:ℝ)*(hitConstant*E) ≤ 2*(H*D)*(hitConstant*E) := by gcongr
    have h₂ : 2*(H*D)*(hitConstant*E) = (ell*D/2)*((4*H*hitConstant/ell)*E) := by field_simp; ring
    have h₃ := mul_le_mul_of_nonneg_left hEsmall (show 0 ≤ ell*D/2 by positivity)
    rw [←h₂] at h₃
    nlinarith
  have hd := mul_le_mul_of_nonneg_left hδsmall (show 0 ≤ (m:ℝ) by positivity)
  have hfin : (m:ℝ)*δ+(j:ℝ)*(2*(hitConstant*E)) ≤ (m:ℝ)/70000 := by nlinarith
  have hx := ENNReal.ofReal_le_ofReal hfin
  simpa (disch := positivity) only [ENNReal.ofReal_add,ENNReal.ofReal_mul,
    ENNReal.ofReal_natCast,ENNReal.ofReal_ofNat] using hx

theorem source_supply_error_small {ell b A H C : ℝ}
    (hell : 0 < ell) (hb : 0 < b) (hA : 0 < A) (hH : 0 < H) (hC : 0 < C) :
    ∃ t₀ : ℝ,0<t₀ ∧ ∀ t : ℝ,0<t → t≤t₀ →
    ∀ Cn M c a : ℝ,0 < c → 0<a → ∃D₀ : ℝ,1≤D₀ ∧
    ∀ D α : ℝ,∀m j : ℕ,D₀≤D → 0≤α → α≤A →
      ell*D/2≤(m:ℝ) → (m:ℝ)≤H*D → (j:ℝ)≤H*D →
      (m:ℝ≥0∞)*ENNReal.ofReal (2*(scalarTrialRemainder Cn M c a b D+3888*t*normPowerMean 2))+
      (j:ℝ≥0∞)*(2*ENNReal.ofReal (hitConstant*(
        8*C*t*(α/D)*(((b*D^(-(1/3):ℝ))⁻¹)^3+(m:ℝ))+
        8*(α/D)*(1+D^(1/12:ℝ))^3/Real.sqrt (D⁻¹/2))))≤ENNReal.ofReal ((m:ℝ)/70000) := by
  have hhit : 0 < hitConstant := hitConstant_pos
  obtain ⟨t₁,ht₁,htail⟩ := trial_remainder_small (by norm_num : (0:ℝ)<1/140000)
  obtain ⟨t₂,ht₂,hcoll⟩ := collision_error_small hb hA hH hC
    (by positivity : 0 < 4*H*hitConstant/ell) (by norm_num : (0:ℝ)<1/140000)
  refine ⟨min t₁ t₂,lt_min ht₁ ht₂,?_⟩
  intro t ht htt Cn M c a hc ha
  obtain ⟨D₁,hD₁,hd₁⟩ := htail t ht (htt.trans (min_le_left _ _)) Cn M c a b hc ha
  obtain ⟨D₂,hD₂,hd₂⟩ := hcoll t ht (htt.trans (min_le_right _ _))
  refine ⟨max D₁ D₂,hD₁.trans (le_max_left _ _),?_⟩
  intro D α m j hD hα hαA hm hmH hj
  have hDp : 1≤D := hD₁.trans ((le_max_left _ _).trans hD)
  have herr := hd₁ D ((le_max_left _ _).trans hD)
  have hcol := hd₂ D α (m:ℝ) ((le_max_right _ _).trans hD) hα hαA (by positivity) hmH
  have hEn : 0≤8*C*t*(α/D)*(((b*D^(-(1/3):ℝ))⁻¹)^3+(m:ℝ))+
      8*(α/D)*(1+D^(1/12:ℝ))^3/Real.sqrt (D⁻¹/2) := by positivity

  have hδ : (0:ℝ) ≤ max 0 (2*(scalarTrialRemainder Cn M c a b D+3888*t*normPowerMean 2)) := le_max_left _ _
  have hδs : max 0 (2*(scalarTrialRemainder Cn M c a b D+3888*t*normPowerMean 2))≤1/140000 := max_le (by norm_num) herr
  have he := supply_error_calibration hell hH (zero_le_one.trans hDp) hδ hEn hm hj hδs hcol
  simpa only [ENNReal.ofReal_max,ENNReal.ofReal_zero,max_eq_right (show (0:ℝ≥0∞)≤_ from zero_le)] using he

end HardSphere.Bridge

end
end

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Bridges_PhysicalTrialTail
attribute [-instance] _root_.OAI.HardSphere.Bridge.exposedBridgeKernel_markov _root_.OAI.HardSphere.Bridge.exposedPeriodSingle_finite _root_.OAI.HardSphere.Bridge.exposedTrialKernel_markov _root_.OAI.HardSphere.Bridge.parameterBridgeKernel_markov _root_.OAI.HardSphere.Bridge.parameterIndividualReference_finite _root_.OAI.HardSphere.Bridge.parameterTrialKernel_markov _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Bridge.targetUniform_finite _root_.OAI.HardSphere.Comparison.parameterTargetKernel_finite _root_.OAI.HardSphere.Groups.cellPathReference_probability _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Rescaling.config_haar _root_.OAI.HardSphere.bridgeEndpointBase_finite _root_.OAI.HardSphere.endpointWeightedBase_sfinite
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
namespace HardSphere.Bridge
open Wiener GaussianPacking PathCutoff

lemma physical_trial_scalar_tail {c M : ℝ} (hM : 0 ≤ M) (hc : 0 ≤ c)
    (htail : ∀R : ℝ,0 ≤ R → wiener {β | R ≤ ‖β‖} ≤
      ENNReal.ofReal M*ENNReal.ofReal (Real.exp (-c*R^2)))
    (L : Length) (n : ℕ) (hn : 0 < n) {t r D Cn a b C : ℝ}
    (ht : 0 < t) (hr : 0 < r) (hD : 1 ≤ D) (hb : 0 < b) (hC : 0 ≤ C)
    (ha : 0 ≤ a) (hnlo : a*D^2 ≤ (n:ℝ)) (hnhi : (n:ℝ) ≤ Cn*D^2)
    (hτr : t/(n:ℝ) ≤ r^2) (y z u v : Point) (w : Time)
    (hw : t*(w:ℝ)=D⁻¹) (hy : ‖y-v‖ ≤ 3) (hz : ‖z-v‖ ≤ 3) (hu : ‖u-v‖ ≤ 3)
    (hdu : ‖u-y‖ ≤ C) (hdz : ‖u-z‖ ≤ C)
    (hdrift : (C+Real.sqrt (2*t)*D^(1/12:ℝ))/(n:ℝ) ≤ r)
    (hsmall : (D^(1/12:ℝ)/6)*r < L.val/2)
    (hwindow : (w:ℝ)*C ≤ (b*D^(-(1/3):ℝ)/8)/12)
    (hrelax : 3*(1+D^(1/12:ℝ)/6) ≤ D^(1/12:ℝ)) :
    trialKernel t y z u {f | ¬TrialCutoff L n r (D^(1/12:ℝ))
      (64*(meanCost+1)) w (b*D^(-(1/3):ℝ)/8) v f} ≤
      ENNReal.ofReal (2*(scalarTrialRemainder Cn M c a b D+3888*t*normPowerMean 2)) := by
  have hDp : 0 < D := zero_lt_one.trans_le hD
  have hm := trial_cutoff_physical_tail htail L n hn ht hr hτr
    (by positivity : 0 ≤ D^(1/12:ℝ)/6) (by positivity : 0 ≤ D^(1/12:ℝ)) hC
    (by positivity : 0 < b*D^(-(1/3):ℝ)/8) y z u v w 2 (by norm_num)
    hy hz hu hdu hdz hdrift hsmall hwindow
  have hsub : {f | ¬TrialCutoff L n r (D^(1/12:ℝ))
      (64*(meanCost+1)) w (b*D^(-(1/3):ℝ)/8) v f} ⊆
      {f | ¬TrialCutoff L n r (3*(1+D^(1/12:ℝ)/6))
      (64*(meanCost+1)) w (b*D^(-(1/3):ℝ)/8) v f} := by
    intro f hf hh
    exact hf (trialCutoff_mono_constants hrelax le_rfl hh)
  apply ((measure_mono hsub).trans hm).trans
  have hs := trial_scalar_bound (b:=b) hD hM hc ha ht.le hnlo hnhi w hw
  apply le_trans _ (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hs (by norm_num : (0:ℝ) ≤ 2)))
  rw [ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2)]
  simp only [ENNReal.ofReal_ofNat]
  apply mul_le_mul' le_rfl
  have hw0 := scaleMoment_nonneg 2 (t:=t) (by positivity : 0 ≤ b*D^(-(1/3):ℝ)/8) 0 w
  have h10 := scaleMoment_nonneg 2 (t:=t) (by norm_num : (0:ℝ) ≤ 1) 0 1
  simp (disch := positivity) only [ENNReal.ofReal_add,ENNReal.ofReal_mul,
    ENNReal.ofReal_div_of_pos,ENNReal.ofReal_pow,ENNReal.ofReal_natCast,
    ENNReal.ofReal_ofNat,le_refl]

end HardSphere.Bridge

end
end

section
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.Bridge
open Wiener GaussianPacking PathCutoff
attribute [local instance] Classical.propDecidable

theorem physical_useful_list {ell b A H : ℝ}
    (hell : 0 < ell) (hb : 0 < b) (hA : 0 < A) (hH : 0 < H) :
    ∃t₀ : ℝ,0 < t₀  ∧  ∀t : ℝ,0 < t  →  t ≤ t₀  →
    ∀Cn M c a : ℝ,0 ≤ M  →  0 < c  →  0 < a  →
    (∀R : ℝ,0 ≤ R  →  wiener {β | R ≤ ‖β‖} ≤ ENNReal.ofReal M*ENNReal.ofReal (Real.exp (-c*R^2)))  →
    ∃D₀ : ℝ,1 ≤ D₀  ∧  ∀D α : ℝ,D₀ ≤ D  →  0 < α  →  α ≤ A  →
    ∀(L : Length) (N m n : ℕ), 0 < n  →  50 < L.val  →  ell*D/2 ≤ (m:ℝ)  →  (m:ℝ) ≤ H*D  →
    ∀(y z : Fin m → Point) (v : Point) (ω : Fin N → ConfigurationPath 1 L)
      (label : Fin m → Fin N) (J : Finset (Fin N)) (w : Time) (B : Fin 7 → Set Point),
    (J.card:ℝ) ≤ H*D  →  a*D^2 ≤ (n:ℝ)  →  (n:ℝ) ≤ Cn*D^2  →
    (α/D) ≤ 1  →  (α/D)*D^(1/12:ℝ) ≤ 1  →  t/(n:ℝ) ≤ (α/D)^2  →  (n:ℝ)*(α/D)^2 ≤ 2*t  →
    t*(w:ℝ)=D⁻¹  →  2*(t/(n:ℝ)) ≤ D⁻¹  →  8*t ≤ (n:ℝ)*D⁻¹  →  2*13/(n:ℝ) ≤ α/D  →
    (13+Real.sqrt (2*t)*D^(1/12:ℝ))/(n:ℝ) ≤ α/D  →
    (w:ℝ)*13 ≤ (b*D^(-(1/3):ℝ)/8)/12  →  3*(1+D^(1/12:ℝ)/6) ≤ D^(1/12:ℝ)  →
    (∀i,‖y i-v‖ ≤ 3)  →  (∀i,‖z i-v‖ ≤ 3)  →
    (∀i j,i≠j  →  (b*D^(-(1/3):ℝ))^2 ≤ square (y i-y j))  →
    (∀i j,i≠j  →  (b*D^(-(1/3):ℝ))^2 ≤ square (z i-z j))  →
    (∀j∈J,Regular (n+n) (α/D) (D^(1/12:ℝ)) (64*(meanCost+1))
      (prefixTime midpointTime w) (b*D^(-(1/3):ℝ)/8) (ω j))  →
    (∀j∈J,∀i,j≠label i  →  α/D+2*(b*D^(-(1/3):ℝ)/8) < torusDistance L (projectPoint L (y i)) (ω j 0 0))  →
    (∀j∈J,∀i,j≠label i  →  α/D+2*(b*D^(-(1/3):ℝ)/8) < torusDistance L (projectPoint L (z i)) (ω j 1 0))  →
    (∀j,j∉J  →  ∀s,12 < torusDistance L (ω j s 0) (projectPoint L v))  →
    (∀j,MeasurableSet (B j))  →  (∀j,volume (B j)=1)  →  (∀j u,u∈B j  →  ‖u-v‖ ≤ 3)  →
    ((Finset.univ.filter (fun i ↦ ¬StrongExcept n t (α/D) (D^(1/12:ℝ)) (64*(meanCost+1))
      (b*D^(-(1/3):ℝ)/8) w (y i) (z i) v ω (label i) B)).card:ℝ) ≤ (m:ℝ)/10 := by
  have hC : 0 < 64*(meanCost+1) := by have := meanCost_nonneg; positivity
  obtain ⟨t₀,ht₀,hs⟩ := source_supply_error_small hell hb hA hH hC
  refine ⟨t₀,ht₀,?_⟩
  intro t ht htt Cn M c a hM hc ha htail
  obtain ⟨D₀,hD₀,hd⟩ := hs t ht htt Cn M c a hc ha
  refine ⟨D₀,hD₀,?_⟩
  intro D α hDD hα hαA L N m n hn hL hm hmH y z v ω label J w B hj hnlo hnhi
    hr1 hsmall hτ hnscale hw hwindow hlarge hdrift hdrift' hwin hrelax hy hz hsepY hsepZ
    hreg hisoY hisoZ hfar hB hBvol hBv
  have hD : 1 ≤ D := hD₀.trans hDD
  have hDp : 0 < D := zero_lt_one.trans_le hD
  have hr : 0 < α/D := by positivity
  have hwd : (w:ℝ)=D⁻¹/t := (eq_div_iff ht.ne').mpr (by nlinarith [hw])
  have hdistance (p : Point) (hp : ‖p-v‖ ≤ 3) (j : Fin 7) (u : Point) (hu : u∈B j) : ‖u-p‖ ≤ 13 := by
    have hh := norm_sub_le (u-v) (p-v)
    have he : (u-v)-(p-v)=u-p := by abel
    rw [he] at hh
    linarith [hBv j u hu]
  apply full_success_count n t (α/D) (D^(1/12:ℝ)) (64*(meanCost+1))
    (b*D^(-(1/3):ℝ)/8) w y z v ω label B hB hBvol
  intro j
  apply (physical_failure_sum hn y z v ω label J w hL ht hr hr1
    (by positivity) (by positivity) hC.le (by positivity : 0 < D⁻¹) hwd hsepY hsepZ hreg
    hsmall hτ hnscale hwindow hlarge hdrift (hB j) (hBvol j).le (hBv j)
    (fun i u hu ↦ hdistance (y i) (hy i) j u hu)
    (fun i u hu ↦ hdistance (z i) (hz i) j u hu) hisoY hisoZ hfar _ ?_).trans
  · exact hd D α m J.card hDD hα.le hαA hm hmH hj
  · intro i u hu
    apply physical_trial_scalar_tail hM hc.le htail L n hn ht hr hD hb (by norm_num : (0:ℝ) ≤ 13)
      ha.le hnlo hnhi hτ (y i) (z i) u v w hw (hy i) (hz i) (hBv j u hu)
      (hdistance (y i) (hy i) j u hu) (hdistance (z i) (hz i) j u hu) hdrift' _ hwin hrelax
    have hrr : 0 ≤ D^(1/12:ℝ) := by positivity
    nlinarith

end HardSphere.Bridge

end
end

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Allocation_PhysicalDatum
attribute [-instance] _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Rescaling.config_haar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators
namespace HardSphere.Groups
open Wiener Bridge Sampling Comparison GaussianPacking PathCutoff CellOrbital
attribute [local instance] Classical.propDecidable

lemma anchorPoint_project {K : ℕ} (L : Length) (v : Fin 3 → Fin K) :
    projectPoint L (anchorPoint v)=gridCenter L v := rfl

attribute [local irreducible] TrialCollision

end HardSphere.Groups
end
end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Allocation_NearLift
attribute [-instance] _root_.OAI.HardSphere.Bridge.exposedPeriodSingle_finite _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Bridge.targetUniform_finite _root_.OAI.HardSphere.Comparison.parameterTargetKernel_finite _root_.OAI.HardSphere.Groups.cellPathReference_probability _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Rescaling.config_haar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.Groups
open Wiener Bridge GaussianPacking PathCutoff CellOrbital

lemma nearestLift_eq_of_near {L : Length} (hL : 50<L.val) (c y : Point)
    (hy : ‖y-c‖≤3) : nearestLift L c (projectPoint L y)=y := by
  ext j
  have hj : |y j-c j|≤3 := (norm_le_pi_norm (y-c) j).trans hy
  have hmem : y j-c j∈Set.Ico (-L.val/2) (-L.val/2+L.val) := by
    rw [abs_le] at hj
    constructor <;> linarith
  change ((AddCircle.equivIco L.val (-L.val/2)) ((y j:AddCircle L.val)-(c j:AddCircle L.val))).val+c j=y j
  rw [←AddCircle.coe_sub,AddCircle.equivIco_coe_eq hmem]
  simp

lemma near_lift_unique {L : Length} (hL : 50<L.val) (c y : Point) (x : Torus L)
    (hp : projectPoint L y=x) (hy : ‖y-c‖≤3) : y=nearestLift L c x := by
  subst x
  exact (nearestLift_eq_of_near hL c y hy).symm

attribute [local instance] Classical.propDecidable

theorem canonical_certificate_useful_list {ell b Alo A H : ℝ}
    (hell : 0 < ell) (hb : 0 < b) (hAlo : 0 < Alo) (hA : 0 < A) (hH : 0 < H) :
    ∃t₀ : ℝ,0 < t₀ ∧ ∀t : ℝ,0 < t → t ≤ t₀ →
    ∃D₀ : ℝ,1 ≤ D₀ ∧ ∀D α : ℝ,D₀ ≤ D → Alo ≤ α → α ≤ A →
    ∀(N K m n : ℕ) [Nontrivial (Fin N)] (L : Length),50 < L.val →
    n=⌈t/(α/D)^2⌉₊ → ∀(w : Time),t*(w:ℝ)=D⁻¹ →
    ∀(θ : ℝ),θ ≤ ell/6 →
    ∀(v : Fin 3→Fin K) (c : Point),projectPoint L c=gridCenter L v →
    ∀(ω : ConfigurationPath N L),
    Certificate (n+n) (α/D) (D^(1/12:ℝ)) (64*(meanCost+1))
      (b*D^(-(1/3):ℝ)/8) (b*D^(-(1/3):ℝ)) ell θ H D (prefixTime midpointTime w) v ω →
    ∀(label : Fin m→Fin N),Function.Injective label →
    Finset.univ.image label=eligibleList (n+n) (α/D) (D^(1/12:ℝ)) (64*(meanCost+1))
      (b*D^(-(1/3):ℝ)/8) (b*D^(-(1/3):ℝ)) (prefixTime midpointTime w) v ω →
    ∀(B : Fin 7→Set Point),(∀j,MeasurableSet (B j)) → (∀j,volume (B j)=1) →
      (∀j u,u∈B j → ‖u-c‖ ≤ 3) →
    ((Finset.univ.filter (fun i ↦ ¬StrongExcept n t (α/D) (D^(1/12:ℝ)) (64*(meanCost+1))
      (b*D^(-(1/3):ℝ)/8) w (nearestLift L c (ω 0 (label i))) (nearestLift L c (ω 1 (label i)))
      c (fun j ↦ onePathAt j ω) (label i) B)).card:ℝ) ≤ (m:ℝ)/10 := by
  obtain ⟨cG,MG,hcG,hMG,htail⟩ := wiener_norm_gaussian_tail
  have htail' (R : ℝ) (hR : 0 ≤ R) :
      wiener {β | R ≤ ‖β‖} ≤ ENNReal.ofReal MG.toReal*ENNReal.ofReal (Real.exp (-cG*R^2)) := by
    rw [ENNReal.ofReal_toReal hMG.ne]
    exact htail R hR
  obtain ⟨t₀,ht₀,hs⟩ := physical_useful_list hell hb hA hH
  refine ⟨t₀,ht₀,?_⟩
  intro t ht htt
  obtain ⟨D₁,hD₁,hs⟩ := hs t ht htt (t/Alo^2+1) MG.toReal cG (t/A^2)
    ENNReal.toReal_nonneg hcG (by positivity) htail'
  obtain ⟨D₂,hgeom⟩ := eventually_atTop.1 (source_trial_geometry hA hb ht)
  refine ⟨max D₁ D₂,hD₁.trans (le_max_left _ _),?_⟩
  intro D α hDD hαlo hαA N K m n _ L hL hn w hw θ hθ v c hc ω cert label hinj himage B hB hBvol hBv
  subst n
  have h1 : D₁ ≤ D := (le_max_left _ _).trans hDD
  have h2 : D₂ ≤ D := (le_max_right _ _).trans hDD
  have hα := hAlo.trans_le hαlo
  rcases hgeom D h2 α hα hαA with
    ⟨hD,hn,hr1,hsmall,hτ,hnscale,hw0,hw1,hwindow,hlarge,hdrift,hdrift',hwin,hrelax,hiso⟩
  have hDp : 0 < D := zero_lt_one.trans_le hD
  have hr : 0 < α/D := by positivity
  have hDa : D*(α/D)=α := by field_simp
  have hbnd := sourceHalf_bounds ht hr hD hAlo
    (show Alo ≤ D*(α/D) by rw [hDa]; exact hαlo)
    (show D*(α/D) ≤ A by rw [hDa]; exact hαA)
  obtain ⟨hm,hmH,hel⟩ := eligible_list_size _ _ _ _ _ _ ell θ H D hDp.le hθ _ v ω cert label hinj himage
  obtain ⟨y,z,hyp,hzp,hy,hz,hsepY,hsepZ,hj,hreg,hisoY,hisoZ,hfar⟩ :=
    certificate_trial_geometry hL _ _ _ _ _ _ ell θ H D (by positivity) _ v c hc ω cert label hinj hel hiso
  have hwd : (w:ℝ)=D⁻¹/t := (eq_div_iff ht.ne').mpr (by nlinarith [hw])
  have ey : y=(fun i ↦ nearestLift L c (ω 0 (label i))) := by
    funext i
    exact near_lift_unique hL c (y i) (ω 0 (label i)) (hyp i) (hy i)
  have ez : z=(fun i ↦ nearestLift L c (ω 1 (label i))) := by
    funext i
    exact near_lift_unique hL c (z i) (ω 1 (label i)) (hzp i) (hz i)
  have hmain := hs D α h1 hα hαA L N m _ hn hL hm hmH y z c (fun j ↦ onePathAt j ω) label
    (visitors (gridCenter L v) ω) w B hj hbnd.1 hbnd.2 hr1 hsmall hτ hnscale hw
    hwindow hlarge hdrift hdrift' (by rw [hwd]; exact hwin) hrelax hy hz hsepY hsepZ
    hreg hisoY hisoZ hfar hB hBvol hBv
  simpa only [ey,ez] using hmain

end HardSphere.Groups
end
end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Allocation_PhysicalTargets
attribute [-instance] _root_.OAI.HardSphere.Bridge.exposedPeriodSingle_finite _root_.OAI.HardSphere.Bridge.targetUniform_finite _root_.OAI.HardSphere.Comparison.parameterTargetKernel_finite _root_.OAI.HardSphere.Groups.cellPathReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.vertexPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators
namespace HardSphere.Groups
open Wiener Bridge Sampling Comparison GaussianPacking PathCutoff CellOrbital
attribute [local instance] Classical.propDecidable

lemma unitTarget_radius (c u : Point) (hu : u∈unitTarget c) : ‖u-c‖≤1/2 := by
  apply (pi_norm_le_iff_of_nonneg (by norm_num : (0:ℝ)≤1/2)).mpr
  intro j
  have hj := hu j (Set.mem_univ j)
  change |u j-c j|≤1/2
  rw [abs_le]
  constructor <;> linarith [hj.1,hj.2]

lemma targetStep_radius (j : Fin 7) : ‖targetStep j‖≤1 := by
  apply (pi_norm_le_iff_of_nonneg (by norm_num : (0:ℝ)≤1)).mpr
  intro k
  unfold targetStep
  change |(if j.val=0 then (0:Point) else fun k ↦
    if k.val=(j.val-1)/2 then (if (j.val-1)%2=0 then 1 else -1) else 0) k|≤1
  split_ifs <;> norm_num
  all_goals split_ifs <;> norm_num

lemma targetCell_radius (c : Point) (j : Fin 7) (u : Point)
    (hu : u∈unitTarget (c+targetStep j)) : ‖u-c‖≤3 := by
  have H := norm_add_le (u-(c+targetStep j)) (targetStep j)
  have he : u-(c+targetStep j)+targetStep j = u-c := by abel
  rw [he] at H
  linarith [unitTarget_radius (c+targetStep j) u hu,targetStep_radius j]

end HardSphere.Groups
end
end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Allocation_PhysicalSupply
attribute [-instance] _root_.OAI.HardSphere.Bridge.exposedPeriodSingle_finite _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Bridge.targetUniform_finite _root_.OAI.HardSphere.Comparison.parameterTargetKernel_finite _root_.OAI.HardSphere.Groups.cellPathReference_probability _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Rescaling.config_haar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal BigOperators
namespace HardSphere.Groups
open Wiener Bridge Sampling Comparison GaussianPacking PathCutoff CellOrbital
attribute [local instance] Classical.propDecidable

theorem canonical_supply_counts_oai {ell b Alo A H : ℝ}
    (hell : 0<ell) (hb : 0<b) (hAlo : 0<Alo) (hA : 0<A) (hH : 0<H) :
    ∃t₀ : ℝ,0<t₀ ∧ ∀t : ℝ,0<t → t≤t₀ →
    ∃D₀ : ℝ,1≤D₀ ∧ ∀D α : ℝ,D₀≤D → Alo≤α → α≤A →
    ∀(N K n : ℕ) [Nontrivial (Fin N)] (L : Length),50<L.val →
    n=⌈t/(α/D)^2⌉₊ → ∀w : Time,t*(w:ℝ)=D⁻¹ →
    ∀θ : ℝ,θ≤ell/6 → ∀v : Fin 3→Fin K,∀ω : ConfigurationPath N L,
    Certificate (n+n) (α/D) (D^(1/12:ℝ)) (64*(meanCost+1))
      (b*D^(-(1/3):ℝ)/8) (b*D^(-(1/3):ℝ)) ell θ H D (prefixTime midpointTime w) v ω →
    let E := eligibleList (n+n) (α/D) (D^(1/12:ℝ)) (64*(meanCost+1))
      (b*D^(-(1/3):ℝ)/8) (b*D^(-(1/3):ℝ)) (prefixTime midpointTime w) v ω
    ell*D/2≤(E.card:ℝ) ∧ 10*(E∩fullFailure n t (α/D) (D^(1/12:ℝ))
      (64*(meanCost+1)) (b*D^(-(1/3):ℝ)/8) w v ω).card≤E.card := by
  obtain ⟨t₀,ht₀,hs⟩ := canonical_certificate_useful_list hell hb hAlo hA hH
  refine ⟨t₀,ht₀,?_⟩
  intro t ht htt
  obtain ⟨D₀,hD₀,hs⟩ := hs t ht htt
  refine ⟨D₀,hD₀,?_⟩
  intro D α hD hαlo hαhi N K n _ L hL hn w hw θ hθ v ω hc
  let E := eligibleList (n+n) (α/D) (D^(1/12:ℝ)) (64*(meanCost+1))
      (b*D^(-(1/3):ℝ)/8) (b*D^(-(1/3):ℝ)) (prefixTime midpointTime w) v ω
  let e := (E.equivFinOfCardEq rfl).symm
  let f : Fin E.card → Fin N := fun k ↦ (e k).val
  have hinj : Function.Injective f := fun i j h ↦ e.injective (Subtype.ext h)
  have himage : Finset.univ.image f=E := by
    ext i
    constructor
    · intro hi
      obtain ⟨k,_,rfl⟩ := Finset.mem_image.mp hi
      exact (e k).property
    · intro hi
      exact Finset.mem_image.mpr ⟨e.symm ⟨i,hi⟩,Finset.mem_univ _,by simp [f]⟩
  have hh := hs D α hD hαlo hαhi N K E.card n L hL hn w hw θ hθ v (anchorPoint v)
    (anchorPoint_project L v) ω hc f hinj himage
    (fun j ↦ unitTarget (anchorPoint v+targetStep j))
    (fun j ↦ unitTarget_measurable _) (fun j ↦ unitTarget_volume _) (targetCell_radius (anchorPoint v))
  have hlo := (eligible_list_size (n+n) (α/D) (D^(1/12:ℝ)) (64*(meanCost+1))
      (b*D^(-(1/3):ℝ)/8) (b*D^(-(1/3):ℝ)) ell θ H D
      (by linarith) hθ (prefixTime midpointTime w) v ω hc f hinj himage).1
  refine ⟨hlo,?_⟩
  let B := fullFailure n t (α/D) (D^(1/12:ℝ)) (64*(meanCost+1)) (b*D^(-(1/3):ℝ)/8) w v ω
  have he : (Finset.univ.filter fun k ↦ f k∈B).image f=E∩B := by
    ext i
    constructor
    · intro hi
      obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp hi
      exact Finset.mem_inter.mpr ⟨(e k).property,(Finset.mem_filter.mp hk).2⟩
    · intro hi
      obtain ⟨hiE,hiB⟩ := Finset.mem_inter.mp hi
      obtain ⟨k,_,rfl⟩ := Finset.mem_image.mp (himage.symm ▸ hiE)
      exact Finset.mem_image.mpr ⟨k,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hiB⟩,rfl⟩
  have hcard := congrArg Finset.card he
  rw [Finset.card_image_of_injective _ hinj] at hcard
  have hbnd : ((E∩B).card:ℝ)≤(E.card:ℝ)/10 := by
    rw [←hcard]
    simpa only [B,fullFailure,Finset.mem_filter,Finset.mem_univ,true_and] using hh
  have hreal : (10:ℝ)*((E∩B).card:ℝ)≤(E.card:ℝ) := by linarith
  exact_mod_cast hreal

end HardSphere.Groups
end
end

end OAI
end

theorem solution : type_of% @OAI.HardSphere.Groups.canonical_supply_counts_oai := @OAI.HardSphere.Groups.canonical_supply_counts_oai
