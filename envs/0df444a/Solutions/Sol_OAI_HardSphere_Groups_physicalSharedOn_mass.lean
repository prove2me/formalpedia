-- Prove2me | solution 1 for OAI.HardSphere.Groups.physicalSharedOn_mass
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T20:16:56.255826+00:00
-- url     : https://prove2.me/submissions/436ba8c8-3ff5-478f-80af-bce0a7677f88

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
-- module Solutions.OAIQ054_HS.HardSphere_Bridges_ReverseTime
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
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
namespace HardSphere.Wiener

lemma endpoint_shift_projection_algebra {ι : Type*} [Fintype ι] (c : ι → ℝ) (t : ι → Time) :
    let a : Option ι → ℝ := fun i ↦ i.elim (-∑ i,c i) c
    let v : Option ι → Time := fun i ↦ i.elim 1 t
    (∑ i,∑ j,a i*a j*min (v i:ℝ) (v j:ℝ)) =
      ∑ i,∑ j,c i*c j*(min (t i:ℝ) (t j:ℝ)-(t i:ℝ)-(t j:ℝ)+1) := by
  let A : ℝ := ∑ i,c i
  let B : ℝ := ∑ i,c i*(t i:ℝ)
  have h1 : (∑ i, (-A)*c i*(t i:ℝ)) = -A*B := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have h2 : (∑ i, c i*(-A)*(t i:ℝ)) = -A*B := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have h3 : (∑ i, ∑ j, c i*c j*(t i:ℝ)) = A*B := by
    dsimp only [A,B]
    rw [Finset.sum_mul_sum,Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  have h4 : (∑ i, ∑ j, c i*c j*(t j:ℝ)) = A*B := by
    dsimp only [A,B]
    rw [Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  have h5 : (∑ i, ∑ j, c i*c j) = A*A := (Finset.sum_mul_sum _ _ _ _).symm
  dsimp only
  simp only [Fintype.sum_option,Option.elim_none,Option.elim_some,
    show ((1:Time):ℝ) = 1 from rfl, min_self,min_eq_right (t _).property.2,
    min_eq_left (t _).property.2,mul_one,mul_add,mul_sub,Finset.sum_add_distrib,
    Finset.sum_sub_distrib]
  change (-A)*(-A)+(∑ i,c i*(-A)*(t i:ℝ))+
    ((∑ i,(-A)*c i*(t i:ℝ))+_) = _
  rw [h1,h2,h3,h4,h5]
  ring

lemma reverseIncrements_law :
    law.map (fun ω ↦ reverseIncrements (path ω)) = wiener := by
  apply continuous_path_law_ext (reverseIncrements.continuous.measurable.comp measurable_path)
    measurable_path
  intro ι _ c t
  have h := path_projection_law (fun i : Option ι ↦ i.elim (-∑ i,c i) c)
    (fun i ↦ i.elim 1 (fun j ↦ reverseTime (t j)))
  rw [endpoint_shift_projection_algebra] at h
  have hv i j : min (reverseTime (t i):ℝ) (reverseTime (t j):ℝ) -
      (reverseTime (t i):ℝ) - (reverseTime (t j):ℝ) +1 = min (t i:ℝ) (t j:ℝ) := by
    change min (1-(t i:ℝ)) (1-(t j:ℝ)) - (1-(t i:ℝ)) - (1-(t j:ℝ))+1 = _
    rcases le_total (t i:ℝ) (t j:ℝ) with hij|hji
    · rw [min_eq_right (by linarith), min_eq_left hij]; ring
    · rw [min_eq_left (by linarith), min_eq_right hji]; ring
  simp_rw [hv] at h
  have heq : (fun ω ↦ ∑ i,c i*reverseIncrements (path ω) (t i)) =
      (fun ω ↦ ∑ i : Option ι,i.elim (-∑ i,c i) c *
        path ω (i.elim 1 (fun j ↦ reverseTime (t j)))) := by
    funext ω
    simp only [Fintype.sum_option,Option.elim_none,Option.elim_some,reverseIncrements_apply,
      mul_sub,Finset.sum_sub_distrib,neg_mul,Finset.sum_mul]
    ring
  change Measure.map (fun ω ↦ ∑ i,c i*reverseIncrements (path ω) (t i)) law = _
  rw [heq,h.map_eq,(path_projection_law c t).map_eq]

end HardSphere.Wiener

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
attribute [-instance] _root_.OAI.HardSphere.Bridge.exposedBridgeKernel_markov _root_.OAI.HardSphere.Bridge.exposedPeriodSingle_finite _root_.OAI.HardSphere.Bridge.exposedTrialKernel_markov _root_.OAI.HardSphere.Bridge.instBorelSpaceContinuousMapElemRealTimePoint _root_.OAI.HardSphere.Bridge.instIsProbabilityMeasurePointMidpointNoise _root_.OAI.HardSphere.Bridge.instMeasurableSpaceContinuousMapElemRealTimePoint _root_.OAI.HardSphere.Bridge.parameterBridgeKernel_markov _root_.OAI.HardSphere.Bridge.parameterIndividualReference_finite _root_.OAI.HardSphere.Bridge.parameterTrialKernel_markov _root_.OAI.HardSphere.Bridge.targetUniform_finite _root_.OAI.HardSphere.Bridge.trialKernel_markov _root_.OAI.HardSphere.Comparison.parameterTargetKernel_finite _root_.OAI.HardSphere.Groups.cellPathReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.vertexPair_finite
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

end HardSphere.GaussianPacking

end
end

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

lemma trial_midpoint (t : ℝ) (y z u : Point) (β : Noise×Noise) : trialPath t y z u β midpointTime=u := by
  have hl : leftTime midpointTime=1 := by ext; norm_num [leftTime,midpointTime]
  have hr : reverseTime (rightTime midpointTime)=1 := by ext; norm_num [rightTime,midpointTime,reverseTime]
  simp only [trialPath,ContinuousMap.coe_mk,hl,hr,pinned_leg_one,add_sub_cancel_right]

end HardSphere.Bridge

end
end

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Bridges_BridgeSplit
attribute [-instance] _root_.OAI.HardSphere.Bridge.exposedBridgeKernel_markov _root_.OAI.HardSphere.Bridge.exposedPeriodSingle_finite _root_.OAI.HardSphere.Bridge.exposedTrialKernel_markov _root_.OAI.HardSphere.Bridge.instBorelSpaceContinuousMapElemRealTimePoint _root_.OAI.HardSphere.Bridge.instIsProbabilityMeasureNoiseLaw _root_.OAI.HardSphere.Bridge.instMeasurableSpaceContinuousMapElemRealTimePoint _root_.OAI.HardSphere.Bridge.parameterBridgeKernel_markov _root_.OAI.HardSphere.Bridge.parameterIndividualReference_finite _root_.OAI.HardSphere.Bridge.parameterTrialKernel_markov _root_.OAI.HardSphere.Bridge.trialKernel_markov _root_.OAI.HardSphere.Groups.cellPathReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite
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

lemma bridgePrefix_eq (u : Time) (ω : Noise) :
    bridgePrefix u (bridge ω)=centerMap (prefixMap u (path ω)) := by
  ext s
  simp only [bridgePrefix_apply,bridge_apply,centerMap_apply,prefixMap_apply]
  have he : prefixTime u 1=u := by ext; simp [prefixTime]
  rw [he]
  change path ω (prefixTime u s)-((u:ℝ)*(s:ℝ))*path ω 1-
    (s:ℝ)*(path ω u-(u:ℝ)*path ω 1)=_
  ring

lemma bridgePrefix_law (u : Time) :
    law.map (fun ω ↦ bridgePrefix u (bridge ω))=
      bridgeLaw.map (fun β ↦ Real.sqrt (u:ℝ) • β) := by
  calc
    _ = (law.map (fun ω ↦ prefixMap u (path ω))).map centerMap := by
      rw [Measure.map_map (f:=fun ω ↦ prefixMap u (path ω)) centerMap.continuous.measurable
        ((prefixMap u).continuous.measurable.comp measurable_path)]
      congr 1
      funext ω
      exact bridgePrefix_eq u ω
    _ = _ := by
      rw [prefix_law,Measure.map_map (f:=fun ω ↦ Real.sqrt (u:ℝ) • path ω) centerMap.continuous.measurable ((show Continuous (fun w : C(Time,ℝ) ↦ Real.sqrt (u:ℝ) • w) from by fun_prop).measurable.comp measurable_path),
        bridgeLaw,Measure.map_map (by fun_prop) measurable_bridge]
      congr 1
      funext ω
      exact (centerMap.map_smul _ _).trans (congrArg (fun β ↦ Real.sqrt (u:ℝ) • β) (centerMap_path ω))

lemma prefixRemainder_gaussian (u : Time) :
    IsGaussianProcess (Sum.elim (fun s ω ↦ prefixMap u (bridge ω) s)
      (fun s ω ↦ bridgeRemainder u (bridge ω) s)) law := by
  classical
  constructor
  intro I
  let loc : Option I → Time := fun i ↦ i.elim u
    (fun j ↦ j.val.elim (prefixTime u) (suffixTime u))
  let ev (i : Option I) : (Option I → ℝ) →L[ℝ] ℝ := ContinuousLinearMap.proj i
  let L : (Option I → ℝ) →L[ℝ] (I → ℝ) := ContinuousLinearMap.pi
    (fun j ↦ match j.val with
      | .inl _ => ev (some j)
      | .inr s => ev (some j) - (1-(s:ℝ)) • ev none)
  convert! (finite_bridge_gaussian loc).map_fun L using 1
  all_goals try with_reducible_and_instances rfl
  funext ω j
  cases hj : j.val <;> simp [L,loc,ev,hj]

lemma prefixRemainder_independent (u : Time) :
    IndepFun (fun ω ↦ prefixMap u (bridge ω)) (fun ω ↦ bridgeRemainder u (bridge ω)) law := by
  have hc (a s : Time) :
      cov[fun ω ↦ prefixMap u (bridge ω) a,fun ω ↦ bridgeRemainder u (bridge ω) s;law]=0 := by
    simp only [prefixMap_apply,bridgeRemainder_apply]
    rw [covariance_fun_sub_right (bridge_eval_law _).hasGaussianLaw.memLp_two
      (bridge_eval_law _).hasGaussianLaw.memLp_two ((bridge_eval_law u).hasGaussianLaw.memLp_two.const_mul _),
      covariance_const_mul_right,bridge_covariance,bridge_covariance,
      min_eq_left ((prefixTime_le u a).trans (le_suffixTime u s)),min_eq_left (prefixTime_le u a)]
    change (u:ℝ)*(a:ℝ)-((u:ℝ)*(a:ℝ))*((u:ℝ)+(1-(u:ℝ))*(s:ℝ))-
      (1-(s:ℝ))*((u:ℝ)*(a:ℝ)-((u:ℝ)*(a:ℝ))*(u:ℝ))=0
    ring
  have hi := (prefixRemainder_gaussian u).indepFun_of_covariance_eq_zero
    (fun s ↦ ((continuous_eval_const s).measurable.comp ((prefixMap u).continuous.measurable.comp measurable_bridge)).aemeasurable)
    (fun s ↦ ((continuous_eval_const s).measurable.comp ((bridgeRemainder u).continuous.measurable.comp measurable_bridge)).aemeasurable) hc
  have hid := hi.comp
    (Measurable.of_eval fun n ↦ measurable_pi_apply (TopologicalSpace.denseSeq Time n))
    (Measurable.of_eval fun n ↦ measurable_pi_apply (TopologicalSpace.denseSeq Time n))
  have hh := hid.comp denseEval_embedding.measurable_invFun denseEval_embedding.measurable_invFun
  convert hh using 1 <;> funext ω <;> exact (denseEval_embedding.leftInverse_invFun _).symm

lemma prefixValue_gaussian (u : Time) :
    IsGaussianProcess (Sum.elim (fun _ : Unit ↦ fun ω ↦ bridge ω u)
      (fun s ω ↦ bridgePrefix u (bridge ω) s)) law := by
  classical
  constructor
  intro I
  let loc : Option I → Time := fun i ↦ i.elim u
    (fun j ↦ j.val.elim (fun _ ↦ u) (prefixTime u))
  let ev (i : Option I) : (Option I → ℝ) →L[ℝ] ℝ := ContinuousLinearMap.proj i
  let L : (Option I → ℝ) →L[ℝ] (I → ℝ) := ContinuousLinearMap.pi
    (fun j ↦ match j.val with
      | .inl _ => ev (some j)
      | .inr s => ev (some j) - (s:ℝ) • ev none)
  convert! (finite_bridge_gaussian loc).map_fun L using 1
  all_goals try with_reducible_and_instances rfl
  funext ω j
  cases hj : j.val <;> simp [L,loc,ev,hj]

lemma prefixValue_independent (u : Time) :
    IndepFun (fun ω ↦ bridge ω u) (fun ω ↦ bridgePrefix u (bridge ω)) law := by
  have hc (_ : Unit) (s : Time) :
      cov[fun ω ↦ bridge ω u,fun ω ↦ bridgePrefix u (bridge ω) s;law]=0 := by
    simp only [bridgePrefix_apply]
    rw [covariance_fun_sub_right (bridge_eval_law _).hasGaussianLaw.memLp_two
      (bridge_eval_law _).hasGaussianLaw.memLp_two ((bridge_eval_law u).hasGaussianLaw.memLp_two.const_mul _),
      covariance_const_mul_right,bridge_covariance,bridge_covariance,
      min_eq_right (prefixTime_le u s),min_self]
    change (u:ℝ)*(s:ℝ)-(u:ℝ)*((u:ℝ)*(s:ℝ))-
      (s:ℝ)*((u:ℝ)-(u:ℝ)*(u:ℝ))=0
    ring
  have hi := (prefixValue_gaussian u).indepFun_of_covariance_eq_zero
    (fun _ ↦ ((continuous_eval_const u).measurable.comp measurable_bridge).aemeasurable)
    (fun s ↦ ((continuous_eval_const s).measurable.comp ((bridgePrefix u).continuous.measurable.comp measurable_bridge)).aemeasurable) hc
  have hid := hi.comp (measurable_pi_apply ())
    (Measurable.of_eval fun n ↦ measurable_pi_apply (TopologicalSpace.denseSeq Time n))
  have hh := hid.comp measurable_id denseEval_embedding.measurable_invFun
  convert hh using 1
  · rfl
  · funext ω
    exact (denseEval_embedding.leftInverse_invFun _).symm

lemma bridge_three_law (u : Time) :
    bridgeLaw.map (fun β ↦ ((β u,bridgePrefix u β),bridgeRemainder u β))=
      ((gaussianReal 0 (Real.toNNReal ((u:ℝ)-(u:ℝ)^2))).prod
        (bridgeLaw.map (fun β ↦ Real.sqrt (u:ℝ) • β))).prod
        (bridgeLaw.map (fun β ↦ Real.sqrt (1-(u:ℝ)) • β)) := by
  have hi := (prefixRemainder_independent u).comp
    (show Measurable (fun f : C(Time,ℝ) ↦ (f 1,centerMap f)) from by fun_prop) measurable_id
  have he : (fun ω ↦ (prefixMap u (bridge ω) 1,centerMap (prefixMap u (bridge ω))))=
      (fun ω ↦ (bridge ω u,bridgePrefix u (bridge ω))) := by
    funext ω
    apply Prod.ext
    · simp only [prefixMap_apply]
      congr 1
      apply Subtype.ext
      simp [prefixTime]
    · rfl
  simp only [Function.comp_def,id_eq] at hi
  rw [he] at hi
  rw [bridgeLaw,Measure.map_map (by fun_prop) measurable_bridge]
  simp only [Function.comp_def]
  have hh := hi.map_prod_eq_prod_map_map
    ((((continuous_eval_const u).measurable.comp measurable_bridge).prodMk
      ((bridgePrefix u).continuous.measurable.comp measurable_bridge)).aemeasurable)
    (((bridgeRemainder u).continuous.measurable.comp measurable_bridge).aemeasurable)
  simp only [Function.comp_def] at hh
  rw [hh]
  have hp := (prefixValue_independent u).map_prod_eq_prod_map_map
    ((continuous_eval_const u).measurable.comp measurable_bridge).aemeasurable
    ((bridgePrefix u).continuous.measurable.comp measurable_bridge).aemeasurable
  simp only [Function.comp_def] at hp
  rw [hp,(bridge_eval_law u).map_eq,bridgePrefix_law,bridgeRemainder_law]
  rfl

end HardSphere.Wiener

end
end

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Bridges_BridgeAssemble
attribute [-instance] _root_.OAI.HardSphere.Bridge.exposedBridgeKernel_markov _root_.OAI.HardSphere.Bridge.exposedPeriodSingle_finite _root_.OAI.HardSphere.Bridge.exposedTrialKernel_markov _root_.OAI.HardSphere.Bridge.parameterBridgeKernel_markov _root_.OAI.HardSphere.Bridge.parameterIndividualReference_finite _root_.OAI.HardSphere.Bridge.parameterTrialKernel_markov _root_.OAI.HardSphere.Bridge.targetUniform_finite _root_.OAI.HardSphere.Comparison.parameterTargetKernel_finite _root_.OAI.HardSphere.Groups.cellPathReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite
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
open Bridge (leftTime rightTime midpointTime leftTime_continuous rightTime_continuous)

lemma assembleBridge_continuous : Continuous assembleBridge := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  change Continuous (fun p : ((ℝ×C(Time,ℝ))×C(Time,ℝ))×Time ↦
    ((leftTime p.2:ℝ)-(rightTime p.2:ℝ))*p.1.1.1+
      p.1.1.2 (leftTime p.2)+p.1.2 (rightTime p.2))
  have hl := leftTime_continuous
  have hr := rightTime_continuous
  fun_prop

lemma assembleBridge_split (β : C(Time,ℝ)) (h0 : β 0=0) (h1 : β 1=0) :
    assembleBridge ((β midpointTime,bridgePrefix midpointTime β),bridgeRemainder midpointTime β)=β := by
  ext s
  simp only [assembleBridge,ContinuousMap.coe_mk,bridgePrefix_apply,bridgeRemainder_apply]
  by_cases hs0 : s=0
  · subst s
    simp [leftTime,rightTime,prefixTime,suffixTime,h0]
  by_cases hs1 : s=1
  · subst s
    norm_num [leftTime,rightTime,prefixTime,suffixTime,midpointTime,h1]
  by_cases hs : (s:ℝ)≤1/2
  · have hr : rightTime s=0 := by apply Subtype.ext; simp only [rightTime]; exact max_eq_right (by linarith)
    have hl : (leftTime s:ℝ)=2*(s:ℝ) := min_eq_left (by linarith)
    have hp : prefixTime midpointTime (leftTime s)=s := by apply Subtype.ext; change (1/2:ℝ)*(leftTime s:ℝ)=(s:ℝ); rw [hl]; ring
    have he : suffixTime midpointTime (0:Time)=midpointTime := by apply Subtype.ext; simp [suffixTime]
    rw [hr,hp,he]
    change _+_+(β midpointTime-(1-(0:ℝ))*β midpointTime)=_
    simp only [show ((0:Time):ℝ)=0 from rfl]
    ring
  · have hl : leftTime s=1 := by apply Subtype.ext; simp only [leftTime]; exact min_eq_right (by linarith)
    have hr : (rightTime s:ℝ)=2*(s:ℝ)-1 := max_eq_left (by linarith)
    have hp : prefixTime midpointTime (1:Time)=midpointTime := by apply Subtype.ext; simp [prefixTime]
    have he : suffixTime midpointTime (rightTime s)=s := by
      apply Subtype.ext
      change (1/2:ℝ)+(1-1/2)*(rightTime s:ℝ)=(s:ℝ)
      rw [hr]
      ring
    rw [hl,hp,he]
    change ((1:ℝ)-(rightTime s:ℝ))*β midpointTime+(β midpointTime-1*β midpointTime)+_= _
    ring

lemma bridge_midpoint_disintegration :
    (((gaussianReal 0 (Real.toNNReal (1/4:ℝ))).prod
      (bridgeLaw.map (fun β ↦ Real.sqrt (1/2:ℝ) • β))).prod
      (bridgeLaw.map (fun β ↦ Real.sqrt (1/2:ℝ) • β))).map assembleBridge=bridgeLaw := by
  have he := bridge_three_law midpointTime
  norm_num [midpointTime] at he
  norm_num only [Real.sqrt_div,Real.sqrt_one,one_div]
  rw [←he,Measure.map_map assembleBridge_continuous.measurable (by fun_prop)]
  have ha : assembleBridge ∘ (fun β ↦ ((β midpointTime,bridgePrefix midpointTime β),bridgeRemainder midpointTime β))=ᵐ[bridgeLaw] id := by
    filter_upwards [HardSphere.bridge_endpoints] with β hβ
    exact assembleBridge_split β hβ.1 hβ.2
  change bridgeLaw.map (assembleBridge ∘ (fun β ↦ ((β midpointTime,bridgePrefix midpointTime β),bridgeRemainder midpointTime β)))=bridgeLaw
  rw [Measure.map_congr ha,Measure.map_id]

end HardSphere.Wiener

end
end

section
noncomputable section
open MeasureTheory Set Filter ProbabilityTheory
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.Wiener

lemma center_reverse (ω : Noise) :
    centerMap (reverseIncrements (path ω))=bridgeReverse (bridge ω) := by
  ext s
  simp only [centerMap_apply,reverseIncrements_apply,bridgeReverse,ContinuousMap.compCLM_apply,
    ContinuousMap.comp_apply,bridge_apply]
  have hr : reverseTime 1=0 := by ext; norm_num [reverseTime]
  rw [hr,path_at_zero]
  change path ω (reverseTime s)-path ω 1-(s:ℝ)*(0-path ω 1)=
    path ω (reverseTime s)-(1-(s:ℝ))*path ω 1
  ring

lemma bridgeReverse_preserving : MeasurePreserving bridgeReverse bridgeLaw bridgeLaw := by
  refine ⟨bridgeReverse.continuous.measurable,?_⟩
  have hm := congrArg (fun μ : Measure C(Time,ℝ) ↦ μ.map centerMap) reverseIncrements_law
  rw [Measure.map_map (f:=fun ω ↦ reverseIncrements (path ω)) centerMap.continuous.measurable
    (reverseIncrements.continuous.measurable.comp measurable_path),←bridgeLaw_center] at hm
  rw [bridgeLaw,Measure.map_map bridgeReverse.continuous.measurable measurable_bridge]
  convert hm using 1
  · congr 1
    funext ω
    exact (center_reverse ω).symm
  · rfl

end HardSphere.Wiener

end
end

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.Bridge
open Wiener GaussianPacking

lemma assembleNoise_continuous : Continuous assembleNoise := by
  apply continuous_pi
  intro j
  exact assembleBridge_continuous.comp (by fun_prop)

lemma scalar_assemble_law :
    (((gaussianReal 0 (Real.toNNReal (1/4:ℝ))).prod bridgeLaw).prod bridgeLaw).map
      (fun p ↦ assembleBridge ((p.1.1,Real.sqrt (1/2:ℝ) • p.1.2),Real.sqrt (1/2:ℝ) • p.2))=bridgeLaw := by
  have hs : MeasurePreserving (fun β : C(Time,ℝ) ↦ Real.sqrt (1/2:ℝ) • β) bridgeLaw
      (bridgeLaw.map (fun β ↦ Real.sqrt (1/2:ℝ) • β)) := ⟨by fun_prop,rfl⟩
  have hp := ((MeasurePreserving.id (gaussianReal 0 (Real.toNNReal (1/4:ℝ)))).prod hs).prod hs
  have hm := congrArg (fun μ : Measure ((ℝ×C(Time,ℝ))×C(Time,ℝ)) ↦ μ.map assembleBridge) hp.map_eq
  rw [Measure.map_map assembleBridge_continuous.measurable hp.measurable] at hm
  exact hm.trans bridge_midpoint_disintegration

lemma assembleNoise_preserving :
    MeasurePreserving assembleNoise ((midpointNoise.prod law).prod law) law := by
  refine ⟨assembleNoise_continuous.measurable,?_⟩
  let g : Measure ℝ := gaussianReal 0 (Real.toNNReal (1/4:ℝ))
  let b := bridgeLaw
  have h₁ := measurePreserving_arrowProdEquivProdArrow ℝ C(Time,ℝ) (Fin 3) (fun _ ↦ g) (fun _ ↦ b)
  have h₂ := measurePreserving_arrowProdEquivProdArrow (ℝ×C(Time,ℝ)) C(Time,ℝ) (Fin 3)
    (fun _ ↦ g.prod b) (fun _ ↦ b)
  have ht := (h₁.prod (MeasurePreserving.id (Measure.pi (fun _ : Fin 3 ↦ b)))).comp h₂
  change (((Measure.pi (fun _ : Fin 3 ↦ g)).prod (Measure.pi (fun _ : Fin 3 ↦ b))).prod
    (Measure.pi (fun _ : Fin 3 ↦ b))).map assembleNoise=Measure.pi (fun _ : Fin 3 ↦ b)
  rw [←ht.map_eq,Measure.map_map assembleNoise_continuous.measurable ht.measurable]
  change (Measure.pi (fun _ : Fin 3 ↦ (g.prod b).prod b)).map
    (fun p j ↦ assembleBridge (((p j).1.1,Real.sqrt (1/2:ℝ) • (p j).1.2),Real.sqrt (1/2:ℝ) • (p j).2))=_
  rw [Measure.pi_map_pi (fun _ ↦ (show Measurable (fun p : (ℝ×C(Time,ℝ))×C(Time,ℝ) ↦
    assembleBridge ((p.1.1,Real.sqrt (1/2:ℝ) • p.1.2),Real.sqrt (1/2:ℝ) • p.2)) from
      assembleBridge_continuous.measurable.comp (by fun_prop)).aemeasurable)]
  simp_rw [show (g.prod b).prod b=(((gaussianReal 0 (Real.toNNReal (1/4:ℝ))).prod bridgeLaw).prod bridgeLaw) from rfl,
    scalar_assemble_law]
  rfl

lemma reverseNoise_continuous : Continuous reverseNoise := by unfold reverseNoise; fun_prop
lemma reverseNoise_preserving : MeasurePreserving reverseNoise law law := by
  refine ⟨reverseNoise_continuous.measurable,?_⟩
  unfold law reverseNoise
  rw [Measure.pi_map_pi (fun _ ↦ bridgeReverse.continuous.measurable.aemeasurable)]
  simp_rw [bridgeReverse_preserving.map_eq]

lemma left_add_right (s : Time) : (leftTime s:ℝ)+(rightTime s:ℝ)=2*(s:ℝ) := by
  change min (2*(s:ℝ)) 1+max (2*(s:ℝ)-1) 0=_
  by_cases h : 2*(s:ℝ)≤1
  · rw [min_eq_left h,max_eq_right (by linarith)]; ring
  · rw [min_eq_right (le_of_not_ge h),max_eq_left (by linarith)]; ring

lemma trial_assemble (t : ℝ) (ht : 0≤t) (y z v : Point) (β γ : Noise) :
    trialPath t y z (midpointPoint t y z v) (β,γ)=
      leg (2*t) y z (assembleNoise ((v,pinned β),reverseNoise (pinned γ))) := by
  ext s j
  simp only [trialPath,leg,ContinuousMap.coe_mk,mean,Pi.add_apply,Pi.sub_apply,
    assembleNoise,assembleBridge,ContinuousMap.smul_apply,smul_eq_mul,reverseNoise,
    bridgeReverse,ContinuousMap.compCLM_apply,ContinuousMap.comp_apply,midpointPoint]
  have hs := left_add_right s
  have hr : (reverseTime (rightTime s):ℝ)=1-(rightTime s:ℝ) := rfl
  have hmul : Real.sqrt (4*t)*Real.sqrt (1/2:ℝ)=Real.sqrt (2*t) := by
    rw [←Real.sqrt_mul (by positivity)]
    congr 1
    ring
  rw [show 2*(2*t)=4*t by ring,hr]
  rw [←hmul]
  have hs' : (s:ℝ)=((leftTime s:ℝ)+(rightTime s:ℝ))/2 := by linarith
  rw [hs']
  ring

end HardSphere.Bridge

end
end

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Bridges_BridgeReference
attribute [-instance] _root_.OAI.HardSphere.Bridge.exposedBridgeKernel_markov _root_.OAI.HardSphere.Bridge.exposedPeriodSingle_finite _root_.OAI.HardSphere.Bridge.exposedTrialKernel_markov _root_.OAI.HardSphere.Bridge.parameterBridgeKernel_markov _root_.OAI.HardSphere.Bridge.parameterIndividualReference_finite _root_.OAI.HardSphere.Bridge.parameterTrialKernel_markov _root_.OAI.HardSphere.Bridge.targetUniform_finite _root_.OAI.HardSphere.Comparison.parameterTargetKernel_finite _root_.OAI.HardSphere.Groups.cellPathReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite
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
open Wiener GaussianPacking

lemma midpointPoint_continuous (t : ℝ) (y z : Point) : Continuous (midpointPoint t y z) := by
  unfold midpointPoint
  fun_prop

instance midpointLaw_probability (t : ℝ) (y z : Point) : IsProbabilityMeasure (midpointLaw t y z) := by
  unfold midpointLaw
  exact Measure.isProbabilityMeasure_map (midpointPoint_continuous t y z).measurable.aemeasurable

lemma trial_product (μ : Measure Point) [SFinite μ] (t : ℝ) (y z : Point) :
    (μ.compProd (trialKernel t y z)).map Prod.snd=
      (μ.prod (law.prod law)).map (fun p ↦ trialPath t y z p.1 p.2) := by
  ext B hB
  rw [Measure.map_apply measurable_snd hB,Measure.compProd_apply (hB.preimage measurable_snd),
    Measure.map_apply (trialPath_continuous t y z).measurable hB,
    Measure.prod_apply (hB.preimage (trialPath_continuous t y z).measurable)]
  apply lintegral_congr
  intro u
  change (trialKernel t y z u) B = (law.prod law) ((fun p ↦ trialPath t y z u p) ⁻¹' B)
  rw [trialKernel_apply]
  have hm : Continuous (trialPath t y z u) := (trialPath_continuous t y z).comp (continuous_const.prodMk continuous_id)
  exact Measure.map_apply hm.measurable hB

lemma full_bridge_midpoint {t : ℝ} (ht : 0≤t) (y z : Point) :
    ((midpointLaw t y z).compProd (trialKernel t y z)).map Prod.snd=
      law.map (leg (2*t) y z) := by
  rw [trial_product]
  have hpin : MeasurePreserving pinned law law := ⟨pinned_continuous.measurable,pinned_law⟩
  have hn := ((MeasurePreserving.id midpointNoise).prod hpin).prod (reverseNoise_preserving.comp hpin)
  have ha := assembleNoise_preserving.comp hn
  have hl := congrArg (fun μ : Measure Noise ↦ μ.map (leg (2*t) y z)) ha.map_eq
  rw [Measure.map_map (leg_continuous (2*t) y z).measurable ha.measurable] at hl
  have hm : MeasurePreserving (midpointPoint t y z) midpointNoise (midpointLaw t y z) :=
    ⟨(midpointPoint_continuous t y z).measurable,rfl⟩
  have hp := hm.prod (MeasurePreserving.id (law.prod law))
  have he := congrArg (fun μ : Measure (Point×(Noise×Noise)) ↦ μ.map (fun p ↦ trialPath t y z p.1 p.2)) hp.map_eq
  rw [Measure.map_map (trialPath_continuous t y z).measurable hp.measurable] at he
  rw [←he,← Measure.prodAssoc_prod (μ := midpointNoise) (ν := law) (τ := law),
    Measure.map_map ((trialPath_continuous t y z).measurable.comp hp.measurable) MeasurableEquiv.prodAssoc.measurable]
  convert hl using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  funext p
  exact trial_assemble t ht y z p.1.1 p.1.2 p.2

lemma midpointLaw_gaussian {t : ℝ} (ht : 0≤t) (y z : Point) :
    midpointLaw t y z=Measure.pi (fun j : Fin 3 ↦ gaussianReal ((y j+z j)/2) (Real.toNNReal t)) := by
  unfold midpointLaw midpointNoise midpointPoint
  rw [Measure.pi_map_pi (fun _ ↦ (by fun_prop : Measurable (fun v : ℝ ↦ (_ : ℝ)+Real.sqrt (4*t)*v)).aemeasurable)]
  congr 1
  funext j
  have h : HasLaw id (gaussianReal 0 (Real.toNNReal (1/4:ℝ))) (gaussianReal 0 (Real.toNNReal (1/4:ℝ))) := ⟨measurable_id.aemeasurable,Measure.map_id⟩
  have he := (gaussianReal_const_add (gaussianReal_const_mul h (Real.sqrt (4*t))) ((y j+z j)/2)).map_eq
  simp only [mul_zero,zero_add] at he
  change _ = _ at he
  change (Measure.map (fun v ↦ (y j+z j)/2+Real.sqrt (4*t)*v) _) = _
  simp only [id_eq] at he
  rw [he]
  apply congrArg (gaussianReal ((y j+z j)/2))
  apply NNReal.coe_injective
  simp only [NNReal.coe_mul,NNReal.coe_mk,Real.coe_toNNReal _ ht,
    Real.coe_toNNReal _ (show 0≤(1/4:ℝ) by norm_num),Real.sq_sqrt (show 0≤4*t by positivity)]
  ring

end HardSphere.Bridge

end
end

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.GaussianPacking

lemma densityLower_pos {b : ℝ} (hb : 0<b) (C : ℝ) : 0<densityLower b C := by
  unfold densityLower
  exact mul_pos (pow_pos (Real.sqrt_pos.mpr (div_pos hb Real.pi_pos)) _) (Real.exp_pos _)

lemma density_lower {b C : ℝ} (hb : 0≤b) (hC : 0≤C) (x : Point) (hx : ‖x‖≤C) :
    densityLower b C≤density b x := by
  have hs : square x≤3*C^2 := by
    unfold square
    calc
      _ ≤ ∑_j : Fin 3,C^2 := Finset.sum_le_sum (fun j _ ↦ by
        have h := (norm_le_pi_norm x j).trans hx
        simpa only [Real.norm_eq_abs,sq_abs] using (sq_le_sq₀ (norm_nonneg (x j)) hC).mpr h)
      _ = _ := by simp
  unfold density densityLower kernel
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by nlinarith)) (by positivity)

lemma gaussian_dominates_local {v : ℝ≥0} (hv : v≠0) (q : Point) {C : ℝ} (hC : 0≤C)
    {B : Set Point} (hB : MeasurableSet B) (hbound : ∀x∈B,‖x-q‖≤C) :
    ENNReal.ofReal (densityLower ((2*(v:ℝ))⁻¹) C) • (volume.restrict B) ≤
      Measure.pi (fun j : Fin 3 ↦ gaussianReal (q j) v) := by
  rw [gaussian_pi_eq q hv]
  apply Measure.le_iff.mpr
  intro A hA
  rw [Measure.smul_apply,smul_eq_mul,Measure.restrict_apply hA,
    withDensity_apply _ hA]
  calc
    _ = ∫⁻x in A∩B,ENNReal.ofReal (densityLower ((2*(v:ℝ))⁻¹) C) := by simp [lintegral_const]
    _ ≤ ∫⁻x in A∩B,ENNReal.ofReal (density ((2*(v:ℝ))⁻¹) (x-q)) := by
      apply setLIntegral_mono' (hA.inter hB)
      intro x hx
      exact ENNReal.ofReal_le_ofReal (density_lower (by positivity) hC (x-q) (hbound x hx.2))
    _ ≤ _ := lintegral_mono_set inter_subset_left

end HardSphere.GaussianPacking

end
end

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Kernels_TrialKernel
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
open scoped ENNReal
namespace HardSphere.Comparison
variable {U X Y : Type*} [MeasurableSpace U] [MeasurableSpace X] [MeasurableSpace Y]

lemma successKernel_apply (κ : Kernel U X) (S : Set X) (hS : MeasurableSet S) (u : U) :
    successKernel κ S hS u=(κ u S)⁻¹ • (κ u).restrict S := rfl

lemma successKernel_mass_le (κ : Kernel U X) [IsFiniteKernel κ] (S : Set X) (hS : MeasurableSet S) (u : U) :
    successKernel κ S hS u univ ≤ 1 := by
  simp only [successKernel_apply,Measure.smul_apply,Measure.restrict_apply_univ,smul_eq_mul]
  exact ENNReal.inv_mul_le_one _

instance successKernel_finite (κ : Kernel U X) [IsFiniteKernel κ] (S : Set X) (hS : MeasurableSet S) :
    IsFiniteKernel (successKernel κ S hS) := ⟨1,by simp,successKernel_mass_le κ S hS⟩

lemma successKernel_mass (κ : Kernel U X) [IsFiniteKernel κ] (S : Set X) (hS : MeasurableSet S)
    {u : U} (h : 0<κ u S) : successKernel κ S hS u univ=1 := by
  simp only [successKernel_apply,Measure.smul_apply,Measure.restrict_apply_univ,smul_eq_mul]
  exact ENNReal.inv_mul_cancel h.ne' (measure_ne_top _ _)

lemma pairedFactor_mass (μ : Measure U) [IsProbabilityMeasure μ]
    (κ : Kernel U X) (η : Kernel U Y) [IsFiniteKernel κ] [IsFiniteKernel η]
    (S : Set X) (T : Set Y) (hS : MeasurableSet S) (hT : MeasurableSet T)
    (hκ : ∀ᵐ u ∂μ,0<κ u S) (hη : ∀ᵐ u ∂μ,0<η u T) :
    pairedFactor μ κ η S T hS hT univ=1 := by
  rw [pairedFactor,Measure.compProd_apply MeasurableSet.univ]
  have hea : (fun u ↦ ((successKernel κ S hS).prod (successKernel η T hT)) u
      ((fun p : X×Y ↦ (u,p))⁻¹' univ))=ᵐ[μ] fun _ ↦ 1 := by
    filter_upwards [hκ,hη] with u hu hv
    simp only [preimage_univ,Kernel.prod_apply]
    rw [show (Set.univ : Set (X×Y))=(Set.univ:Set X)×ˢ(Set.univ:Set Y) from Set.univ_prod_univ.symm,
      Measure.prod_prod,successKernel_mass κ S hS hu,successKernel_mass η T hT hv,one_mul]
  rw [lintegral_congr_ae hea]
  simp

lemma pairedFactor_fst (μ : Measure U) [SFinite μ]
    (κ : Kernel U X) (η : Kernel U Y) [IsFiniteKernel κ] [IsFiniteKernel η]
    (S : Set X) (T : Set Y) (hS : MeasurableSet S) (hT : MeasurableSet T)
    (hη : ∀ᵐ u ∂μ,0<η u T) :
    (pairedFactor μ κ η S T hS hT).map (fun p ↦ (p.1,p.2.1))=
      μ.compProd (successKernel κ S hS) := by
  have hm : Measurable (fun p : U×(X×Y) ↦ (p.1,p.2.1)) := by fun_prop
  ext B hB
  rw [Measure.map_apply hm hB,
    pairedFactor,Measure.compProd_apply (hB.preimage hm),
    Measure.compProd_apply hB]
  apply lintegral_congr_ae
  filter_upwards [hη] with u hu
  rw [Kernel.prod_apply]
  have he : (fun p : X×Y ↦ (u,p))⁻¹' ((fun p : U×(X×Y) ↦ (p.1,p.2.1))⁻¹' B)=
      ((fun x : X ↦ (u,x))⁻¹' B)×ˢ(univ : Set Y) := by ext p; simp
  rw [he,Measure.prod_prod,successKernel_mass η T hT hu,mul_one]

lemma pairedFactor_snd (μ : Measure U) [SFinite μ]
    (κ : Kernel U X) (η : Kernel U Y) [IsFiniteKernel κ] [IsFiniteKernel η]
    (S : Set X) (T : Set Y) (hS : MeasurableSet S) (hT : MeasurableSet T)
    (hκ : ∀ᵐ u ∂μ,0<κ u S) :
    (pairedFactor μ κ η S T hS hT).map (fun p ↦ (p.1,p.2.2))=
      μ.compProd (successKernel η T hT) := by
  have hm : Measurable (fun p : U×(X×Y) ↦ (p.1,p.2.2)) := by fun_prop
  ext B hB
  rw [Measure.map_apply hm hB,
    pairedFactor,Measure.compProd_apply (hB.preimage hm),
    Measure.compProd_apply hB]
  apply lintegral_congr_ae
  filter_upwards [hκ] with u hu
  rw [Kernel.prod_apply]
  have he : (fun p : X×Y ↦ (u,p))⁻¹' ((fun p : U×(X×Y) ↦ (p.1,p.2.2))⁻¹' B)=
      (univ : Set X)×ˢ((fun y : Y ↦ (u,y))⁻¹' B) := by ext p; simp
  rw [he,Measure.prod_prod,successKernel_mass κ S hS hu,one_mul]

lemma successKernel_absolutelyContinuous (κ : Kernel U X) (S : Set X)
    (hS : MeasurableSet S) (u : U) : successKernel κ S hS u ≪ κ u := by
  rw [successKernel_apply]
  exact Measure.smul_absolutelyContinuous.trans (Measure.restrict_le_self.absolutelyContinuous)

lemma pairedFactor_midpoint {E : Type*} [MeasurableSpace E] [MeasurableEq E]
    (μ : Measure U) [SFinite μ] (κ : Kernel U X) (η : Kernel U Y)
    [IsFiniteKernel κ] [IsFiniteKernel η] (π : X→E) (σ : Y→E) (uval : U→E)
    (hπ : Measurable π) (hσ : Measurable σ) (huval : Measurable uval)
    (S : Set X) (T : Set Y) (hS : MeasurableSet S) (hT : MeasurableSet T)
    (hκ : ∀ᵐ u ∂μ,∀ᵐ x ∂κ u,π x=uval u)
    (hη : ∀ᵐ u ∂μ,∀ᵐ y ∂η u,σ y=uval u) :
    ∀ᵐ p ∂pairedFactor μ κ η S T hS hT,π p.2.1=uval p.1 ∧ σ p.2.2=uval p.1 := by
  rw [pairedFactor,Measure.ae_compProd_iff (by measurability)]
  filter_upwards [hκ,hη] with u hu hv
  rw [Kernel.prod_apply]
  apply (Measure.ae_prod_iff_ae_ae (by measurability)).mpr
  filter_upwards [(successKernel_absolutelyContinuous κ S hS u).ae_le hu] with x hx
  filter_upwards [(successKernel_absolutelyContinuous η T hT u).ae_le hv] with y hy
  exact ⟨hx,hy⟩

end HardSphere.Comparison

end
end

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Kernels_KernelDensity
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
open scoped ENNReal NNReal
namespace HardSphere.Comparison
variable {U X : Type*} [MeasurableSpace U] [MeasurableSpace X]

lemma successKernel_restrict_le (κ : Kernel U X) [IsFiniteKernel κ] (S : Set X) (hS : MeasurableSet S)
    {u : U} {c : ℝ≥0∞} (hc : c≤κ u S) :
    successKernel κ S hS u ≤ c⁻¹ • (κ u).restrict S := by
  rw [successKernel_apply]
  intro B
  simp only [Measure.smul_apply,smul_eq_mul]
  exact mul_le_mul_left (ENNReal.inv_le_inv.mpr hc) _

lemma successful_marginal_le (μ ν : Measure U) [SFinite μ] [SFinite ν]
    (κ : Kernel U X) [IsFiniteKernel κ] (S : Set X) (hS : MeasurableSet S)
    {c A : ℝ≥0∞} (hμ : μ≤A • ν) (hc : ∀ᵐu ∂μ,c≤κ u S) :
    (μ.compProd (successKernel κ S hS)).map Prod.snd ≤
      (c⁻¹*A) • (((ν.compProd κ).map Prod.snd).restrict S) := by
  apply Measure.le_iff.mpr
  intro B hB
  rw [Measure.map_apply measurable_snd hB,Measure.compProd_apply (hB.preimage measurable_snd),
    Measure.smul_apply,smul_eq_mul,Measure.restrict_apply hB,
    Measure.map_apply measurable_snd (hB.inter hS),Measure.compProd_apply ((hB.inter hS).preimage measurable_snd)]
  calc
    _ ≤ ∫⁻u,c⁻¹*(κ u (B∩S)) ∂μ := by
      apply lintegral_mono_ae
      filter_upwards [hc] with u hu
      change successKernel κ S hS u B≤_
      simpa only [preimage_preimage,preimage_id,Measure.smul_apply,smul_eq_mul,Measure.restrict_apply hB] using
        successKernel_restrict_le κ S hS hu B
    _ = c⁻¹*(∫⁻u,κ u (B∩S) ∂μ) := lintegral_const_mul _ (κ.measurable_coe (hB.inter hS))
    _ ≤ c⁻¹*(∫⁻u,κ u (B∩S) ∂A • ν) := mul_le_mul_right (lintegral_mono' hμ le_rfl) _
    _ = _ := by rw [lintegral_smul_measure]; simp only [smul_eq_mul]; rw [mul_assoc]; rfl

lemma normalizer_positive_of_uniform_success (μ ν : Measure U) [IsProbabilityMeasure μ] [SFinite ν]
    (κ : Kernel U X) [IsFiniteKernel κ] (S : Set X) (hS : MeasurableSet S)
    {c A : ℝ≥0∞} (hc0 : 0 < c) (hA : A≠⊤) (hμ : μ≤A • ν)
    (hc : ∀ᵐu ∂μ,c≤κ u S) : 0<((ν.compProd κ).map Prod.snd) S := by
  rw [Measure.map_apply measurable_snd hS,Measure.compProd_apply (hS.preimage measurable_snd)]
  have h₁ : c≤∫⁻u,κ u S ∂μ := by
    calc
      _ = ∫⁻_u,c ∂μ := by simp
      _ ≤ _ := lintegral_mono_ae hc
  have h₂ : (∫⁻u,κ u S ∂μ)≤A*(∫⁻u,κ u S ∂ν) := by
    convert lintegral_mono' hμ (f:=fun u ↦ κ u S) le_rfl using 1
    all_goals try with_reducible_and_instances rfl
    rw [lintegral_smul_measure,smul_eq_mul]
  change 0<(∫⁻u,κ u S ∂ν)
  exact (ENNReal.div_pos hc0.ne' hA).trans_le (ENNReal.div_le_of_le_mul' (h₁.trans h₂))

lemma restricted_le_normalized (P : Measure X) [IsProbabilityMeasure P] (S : Set X) :
    P.restrict S≤(P S)⁻¹ • P.restrict S := by
  intro B
  rw [Measure.smul_apply,smul_eq_mul]
  have hi : (1:ℝ≥0∞)≤(P S)⁻¹ := by
    simpa using ENNReal.inv_le_inv.mpr (prob_le_one (μ:=P) (s:=S))
  simpa using mul_le_mul_left hi (P.restrict S B)

lemma successful_marginal_le_reference (μ ν : Measure U) [SFinite μ] [IsProbabilityMeasure ν]
    (κ : Kernel U X) [IsMarkovKernel κ] (S : Set X) (hS : MeasurableSet S)
    {c A : ℝ≥0∞} (hμ : μ≤A • ν) (hc : ∀ᵐu ∂μ,c≤κ u S) :
    (μ.compProd (successKernel κ S hS)).map Prod.snd ≤
      (c⁻¹*A) • ((((ν.compProd κ).map Prod.snd) S)⁻¹ • (((ν.compProd κ).map Prod.snd).restrict S)) := by
  have := successful_marginal_le μ ν κ S hS hμ hc
  refine this.trans ?_
  intro B
  simpa only [Measure.smul_apply,smul_eq_mul] using mul_le_mul_right (restricted_le_normalized ((ν.compProd κ).map Prod.snd) S B) (c⁻¹*A)

end HardSphere.Comparison

end
end

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Kernels_ParameterSuccess
attribute [-instance] _root_.OAI.HardSphere.Groups.labelOptionSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace HardSphere.Comparison

lemma exists_bounded_auxiliary_kernel {X Z : Type*} [MeasurableSpace X] [MeasurableSpace Z]
    [StandardBorelSpace Z] [Nonempty Z] (P : Measure X) [IsProbabilityMeasure P]
    (ρ : Measure (X×Z)) [IsProbabilityMeasure ρ] {G : ℝ≥0∞} (hG : G≠⊤)
    (hρ : ρ.fst≤G • P) :
    ∃ κ : Kernel X Z,IsFiniteKernel κ ∧ P.compProd κ=ρ ∧
      (∀x,κ x univ≤G) ∧ (∫⁻x,κ x univ ∂P)=1 := by
  have hac : ρ.fst ≪ P := (Measure.absolutelyContinuous_of_le hρ).trans Measure.smul_absolutelyContinuous
  have hbd : ∀ᵐx ∂P,ρ.fst.rnDeriv P x≤G := by
    apply ae_le_of_forall_setLIntegral_le_of_sigmaFinite (ρ.fst.measurable_rnDeriv P)
    intro S hS hSf
    simpa only [lintegral_const,Measure.restrict_apply_univ,smul_eq_mul,Measure.smul_apply]
      using (Measure.setLIntegral_rnDeriv_le (μ:=ρ.fst) (ν:=P) S).trans (hρ S)
  let f : X→ℝ≥0∞ := fun x ↦ min (ρ.fst.rnDeriv P x) G
  have hfm : Measurable f := (ρ.fst.measurable_rnDeriv P).min measurable_const
  have hfe : f=ᵐ[P]ρ.fst.rnDeriv P := hbd.mono (fun x hx ↦ min_eq_left hx)
  have hw : P.withDensity f=ρ.fst := (withDensity_congr_ae hfe).trans (Measure.withDensity_rnDeriv_eq _ _ hac)
  let κ := ρ.condKernel.withDensity (fun x _ ↦ f x)
  have hκ : IsFiniteKernel κ := Kernel.isFiniteKernel_withDensity_of_bounded _ hG (fun x _ ↦ min_le_right _ _)
  let _ := hκ
  have hκeq (x : X) : κ x=f x • ρ.condKernel x := by
    change ρ.condKernel.withDensity (fun (x : X) (_ : Z) ↦ f x) x = _
    rw [Kernel.withDensity_apply _ (show Measurable (Function.uncurry (fun (x : X) (_ : Z) ↦ f x)) from hfm.comp measurable_fst)]
    exact withDensity_const _
  have hmass (x : X) : κ x univ=f x := by rw [hκeq]; simp
  have hjoint : P.compProd κ=ρ := by
    rw [←ρ.disintegrate ρ.condKernel,←hw]
    ext S hS
    rw [Measure.compProd_apply hS,Measure.compProd_apply hS,
      lintegral_withDensity_eq_lintegral_mul _ hfm (Kernel.measurable_kernel_prodMk_left hS)]
    apply lintegral_congr
    intro x
    rw [hκeq,Measure.smul_apply,smul_eq_mul]
    rfl
  refine ⟨κ,hκ,hjoint,fun x ↦ ?_,?_⟩
  · rw [hmass]; exact min_le_right _ _
  · have hu := congrArg (fun μ : Measure (X×Z) ↦ μ univ) hjoint
    simpa only [Measure.compProd_apply MeasurableSet.univ,preimage_univ,measure_univ] using hu

end HardSphere.Comparison

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Kernels_TrialObserved
attribute [-instance] _root_.OAI.HardSphere.Bridge.exposedBridgeKernel_markov _root_.OAI.HardSphere.Bridge.exposedPeriodSingle_finite _root_.OAI.HardSphere.Bridge.exposedTrialKernel_markov _root_.OAI.HardSphere.Bridge.instIsProbabilityMeasurePointMidpointNoise _root_.OAI.HardSphere.Bridge.midpointLaw_probability _root_.OAI.HardSphere.Bridge.parameterBridgeKernel_markov _root_.OAI.HardSphere.Bridge.parameterIndividualReference_finite _root_.OAI.HardSphere.Bridge.parameterTrialKernel_markov _root_.OAI.HardSphere.Bridge.targetUniform_finite _root_.OAI.HardSphere.Comparison.parameterTargetKernel_finite _root_.OAI.HardSphere.Groups.cellPathReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace HardSphere.Comparison
open Bridge Wiener GaussianPacking

lemma trialKernel_midpoint (t : ℝ) (y z u : Point) :
    ∀ᵐ ω ∂trialKernel t y z u,ω midpointTime=u := by
  rw [trialKernel_apply]
  apply (ae_map_iff ((trialPath_continuous t y z).measurable.comp
    (measurable_const.prodMk measurable_id)).aemeasurable (measurableSet_eq_fun ((continuous_eval_const midpointTime).measurable : Measurable (fun ω : C(Time,Point) ↦ ω midpointTime)) measurable_const)).mpr
  exact ae_of_all _ (fun β ↦ trial_midpoint t y z u β)

lemma paired_trial_midpoint (μ : Measure Point) [SFinite μ] (t : ℝ) (y z y' z' : Point)
    (S T : Set C(Time,Point)) (hS : MeasurableSet S) (hT : MeasurableSet T) :
    ∀ᵐ p ∂pairedFactor μ (trialKernel t y z) (trialKernel t y' z') S T hS hT,
      p.2.1 midpointTime=p.1 ∧ p.2.2 midpointTime=p.1 := by
  apply pairedFactor_midpoint μ (trialKernel t y z) (trialKernel t y' z')
    (fun ω ↦ ω midpointTime) (fun ω ↦ ω midpointTime) id
    (continuous_eval_const midpointTime).measurable (continuous_eval_const midpointTime).measurable measurable_id
  · exact ae_of_all _ (trialKernel_midpoint t y z)
  · exact ae_of_all _ (trialKernel_midpoint t y' z')

end HardSphere.Comparison

end
end

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Bridges_LocalReference
attribute [-instance] _root_.OAI.HardSphere.Bridge.exposedBridgeKernel_markov _root_.OAI.HardSphere.Bridge.exposedPeriodSingle_finite _root_.OAI.HardSphere.Bridge.exposedTrialKernel_markov _root_.OAI.HardSphere.Bridge.parameterBridgeKernel_markov _root_.OAI.HardSphere.Bridge.parameterIndividualReference_finite _root_.OAI.HardSphere.Bridge.parameterTrialKernel_markov _root_.OAI.HardSphere.Bridge.targetUniform_finite _root_.OAI.HardSphere.Comparison.parameterTargetKernel_finite _root_.OAI.HardSphere.Groups.cellPathReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite
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
open Wiener GaussianPacking Comparison

lemma targetUniform_probability {A : Set Point} (hA0 : volume A≠0) (hAfinite : volume A≠⊤) : IsProbabilityMeasure (targetUniform A) := by
  constructor
  simp only [targetUniform,Measure.smul_apply,Measure.restrict_apply_univ,smul_eq_mul]
  exact ENNReal.inv_mul_cancel hA0 hAfinite

lemma midpointLower_pos {t : ℝ} (ht : 0<t) (C : ℝ) : 0 < midpointLower t C :=
  ENNReal.ofReal_pos.mpr (densityLower_pos (by positivity) C)
lemma midpointLower_ne_top (t C : ℝ) : midpointLower t C≠⊤ := ENNReal.ofReal_ne_top

lemma targetUniform_le_midpoint {t C : ℝ} (ht : 0<t) (hC : 0≤C) (y z : Point)
    {A : Set Point} (hA : MeasurableSet A) (hbound : ∀x∈A,‖x-(fun j ↦ (y j+z j)/2)‖≤C) :
    targetUniform A≤((volume A)⁻¹*(midpointLower t C)⁻¹) • midpointLaw t y z := by
  have h := gaussian_dominates_local (v:=Real.toNNReal t) (by simpa [Real.toNNReal_eq_zero] using not_le.mpr ht)
    (fun j ↦ (y j+z j)/2) hC hA hbound
  rw [←midpointLaw_gaussian ht.le y z,Real.coe_toNNReal t ht.le] at h
  change midpointLower t C • volume.restrict A ≤ midpointLaw t y z at h
  have hd0 := ne_of_gt (midpointLower_pos ht C)
  intro B
  have hh := mul_le_mul_right (h B) ((volume A)⁻¹*(midpointLower t C)⁻¹)
  have he : (volume A)⁻¹*(midpointLower t C)⁻¹*midpointLower t C=(volume A)⁻¹ := by
    rw [mul_assoc,ENNReal.inv_mul_cancel hd0 (midpointLower_ne_top t C),mul_one]
  simpa only [targetUniform,Measure.smul_apply,smul_eq_mul,←mul_assoc,he] using hh

lemma physical_trial_le_reference {t C : ℝ} (ht : 0<t) (hC : 0≤C) (y z : Point)
    {A : Set Point} (hA : MeasurableSet A) (hAfinite : volume A≠⊤)
    (hbound : ∀x∈A,‖x-(fun j ↦ (y j+z j)/2)‖≤C)
    (S : Set C(Time,Point)) (hS : MeasurableSet S) {c : ℝ≥0∞}
    (hc : ∀ᵐu ∂targetUniform A,c≤trialKernel t y z u S) :
    ((targetUniform A).compProd (successKernel (trialKernel t y z) S hS)).map Prod.snd ≤
      (c⁻¹*((volume A)⁻¹*(midpointLower t C)⁻¹)) • individualReference t y z S := by
  let : IsFiniteMeasure (volume.restrict A) := ⟨by simp [hAfinite.lt_top]⟩
  let : IsFiniteMeasure (targetUniform A) := by
    by_cases h0 : volume A=0
    · have hz : targetUniform A=0 := by simp [targetUniform,Measure.restrict_eq_zero.mpr h0]
      rw [hz]
      first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
    · let : IsProbabilityMeasure (targetUniform A) := targetUniform_probability h0 hAfinite
      first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
  have h := successful_marginal_le_reference (targetUniform A) (midpointLaw t y z)
    (trialKernel t y z) S hS (targetUniform_le_midpoint ht hC y z hA hbound) hc
  simpa only [full_bridge_midpoint ht.le,individualReference] using h

end HardSphere.Bridge

end
end

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology
namespace HardSphere.Bridge
open Wiener GaussianPacking Comparison

lemma individualReference_probability {t C : ℝ} (ht : 0<t) (hC : 0≤C) (y z : Point)
    {A : Set Point} (hA : MeasurableSet A) (hA0 : volume A≠0) (hAfinite : volume A≠⊤)
    (hbound : ∀u∈A,‖u-(fun j ↦ (y j+z j)/2)‖≤C)
    (S : Set C(Time,Point)) (hS : MeasurableSet S) {c : ℝ≥0∞} (hc0 : 0 < c)
    (hc : ∀ᵐu ∂targetUniform A,c≤trialKernel t y z u S) :
    IsProbabilityMeasure (individualReference t y z S) := by
  let _ : IsProbabilityMeasure (targetUniform A) := targetUniform_probability hA0 hAfinite
  have hp := normalizer_positive_of_uniform_success (targetUniform A) (midpointLaw t y z)
    (trialKernel t y z) S hS hc0 (ENNReal.mul_ne_top (ENNReal.inv_ne_top.mpr hA0)
      (ENNReal.inv_ne_top.mpr (midpointLower_pos ht C).ne'))
    (targetUniform_le_midpoint ht hC y z hA hbound) hc
  rw [full_bridge_midpoint ht.le y z] at hp
  let _ : IsProbabilityMeasure (law.map (leg (2*t) y z)) := Measure.isProbabilityMeasure_map (leg_continuous (2*t) y z).measurable.aemeasurable
  constructor
  simp only [individualReference,Measure.smul_apply,Measure.restrict_apply_univ,smul_eq_mul]
  exact ENNReal.inv_mul_cancel hp.ne' (measure_ne_top _ _)

lemma pairedTrialLaw_probability (t : ℝ) (y z y' z' : Point) (A : Set Point)
    (hA0 : volume A≠0) (hAfinite : volume A≠⊤)
    (S T : Set C(Time,Point)) (hS : MeasurableSet S) (hT : MeasurableSet T)
    (hκ : ∀ᵐu ∂targetUniform A,0<trialKernel t y z u S)
    (hη : ∀ᵐu ∂targetUniform A,0<trialKernel t y' z' u T) :
    IsProbabilityMeasure (pairedTrialLaw t y z y' z' A S T hS hT) := by
  let _ : IsProbabilityMeasure (targetUniform A) := targetUniform_probability hA0 hAfinite
  let _ : IsProbabilityMeasure (pairedFactor (targetUniform A) (trialKernel t y z) (trialKernel t y' z') S T hS hT) :=
    ⟨pairedFactor_mass _ _ _ _ _ _ _ hκ hη⟩
  unfold pairedTrialLaw
  first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

lemma pairedTrialLaw_fst (t : ℝ) (y z y' z' : Point) (A : Set Point)
    (hA0 : volume A≠0) (hAfinite : volume A≠⊤)
    (S T : Set C(Time,Point)) (hS : MeasurableSet S) (hT : MeasurableSet T)
    (hη : ∀ᵐu ∂targetUniform A,0<trialKernel t y' z' u T) :
    (pairedTrialLaw t y z y' z' A S T hS hT).fst=
      ((targetUniform A).compProd (successKernel (trialKernel t y z) S hS)).map Prod.snd := by
  let _ : IsProbabilityMeasure (targetUniform A) := targetUniform_probability hA0 hAfinite
  have h := congrArg (fun μ : Measure (Point×C(Time,Point)) ↦ μ.map Prod.snd)
    (pairedFactor_fst (targetUniform A) (trialKernel t y z) (trialKernel t y' z') S T hS hT hη)
  rw [Measure.map_map measurable_snd (by fun_prop)] at h
  unfold pairedTrialLaw Measure.fst
  rw [Measure.map_map measurable_fst (by fun_prop)]
  exact h

lemma pairedTrialLaw_midpoint (t : ℝ) (y z y' z' : Point) (A : Set Point)
    (hA0 : volume A≠0) (hAfinite : volume A≠⊤)
    (S T : Set C(Time,Point)) (hS : MeasurableSet S) (hT : MeasurableSet T) :
    ∀ᵐp ∂pairedTrialLaw t y z y' z' A S T hS hT,
      p.1 midpointTime=p.2.1 ∧ p.2.2 midpointTime=p.2.1 := by
  let _ : IsProbabilityMeasure (targetUniform A) := targetUniform_probability hA0 hAfinite
  rw [pairedTrialLaw]
  apply (ae_map_iff (by fun_prop) (by measurability)).mpr
  exact paired_trial_midpoint (targetUniform A) t y z y' z' S T hS hT

end HardSphere.Bridge

end
end

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Bridges_PhysicalSuccess
attribute [-instance] _root_.OAI.HardSphere.Bridge.exposedBridgeKernel_markov _root_.OAI.HardSphere.Bridge.exposedPeriodSingle_finite _root_.OAI.HardSphere.Bridge.exposedTrialKernel_markov _root_.OAI.HardSphere.Bridge.instIsProbabilityMeasurePointMidpointNoise _root_.OAI.HardSphere.Bridge.midpointLaw_probability _root_.OAI.HardSphere.Bridge.parameterBridgeKernel_markov _root_.OAI.HardSphere.Bridge.parameterIndividualReference_finite _root_.OAI.HardSphere.Bridge.parameterTrialKernel_markov _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Bridge.targetUniform_finite _root_.OAI.HardSphere.Comparison.parameterTargetKernel_finite _root_.OAI.HardSphere.Groups.cellPathReference_probability _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Rescaling.config_haar _root_.OAI.HardSphere.bridgeEndpointBase_finite _root_.OAI.HardSphere.endpointWeightedBase_sfinite
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
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_LocalCheck
attribute [-instance] _root_.OAI.HardSphere.Comparison.instFintypeFrozenCheckIndex _root_.OAI.HardSphere.Comparison.proposalKernel_finite _root_.OAI.HardSphere.Groups.labelOptionSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
open MeasureTheory Function Set Filter
open scoped ENNReal BigOperators
namespace HardSphere.Comparison

variable {ι : Type*} [DecidableEq ι] {X : ι → Type*}
  [∀ i, MeasurableSpace (X i)]

variable {C : Type*} [Fintype C] (checks : C → LocalCheck X)

lemma measurableSet_retainedEvent (s : Finset ι) : MeasurableSet (retainedEvent checks s) := by
  classical
  have heq : retainedEvent checks s =
      ⋂ c, if (checks c).support ⊆ s then {x | (checks c).pass x} else Set.univ := by
    ext x
    simp [retainedEvent]
  rw [heq]
  apply MeasurableSet.iInter
  intro c
  split_ifs
  · exact (checks c).measurable_pass
  · exact MeasurableSet.univ

lemma measurableSet_insertionEvent (s : Finset ι) (i : ι) :
    MeasurableSet (insertionEvent checks s i) := by
  classical
  have heq : insertionEvent checks s i =
      ⋂ c, if (checks c).support ⊆ insert i s ∧ ¬ (checks c).support ⊆ s then
        {x | (checks c).pass x} else Set.univ := by
    ext x
    simp [insertionEvent, and_imp]
  rw [heq]
  apply MeasurableSet.iInter
  intro c
  split_ifs
  · exact (checks c).measurable_pass
  · exact MeasurableSet.univ

omit [Fintype C] in
lemma retainedEvent_insert (s : Finset ι) (i : ι) :
    retainedEvent checks (insert i s) =
      retainedEvent checks s ∩ insertionEvent checks s i := by
  classical
  ext x
  constructor
  · intro h
    exact ⟨fun c hc ↦ h c (hc.trans (Finset.subset_insert _ _)), fun c hc _ ↦ h c hc⟩
  · rintro ⟨hs, hi⟩ c hc
    by_cases hold : (checks c).support ⊆ s
    · exact hs c hold
    · exact hi c hc hold

omit [Fintype C] in
lemma retainedEvent_update {s : Finset ι} {i : ι} (hi : i ∉ s)
    (x : ∀ j, X j) (y : X i) :
    Function.update x i y ∈ retainedEvent checks s ↔ x ∈ retainedEvent checks s := by
  apply forall_congr'
  intro c
  apply imp_congr_right
  intro hc
  apply (checks c).depends
  intro j hj
  exact Function.update_of_ne (ne_of_mem_of_not_mem (hc hj) hi) y x

lemma measurable_checkWeight (s : Finset ι) : Measurable (checkWeight checks s) :=
  measurable_const.indicator (measurableSet_retainedEvent checks s)

end HardSphere.Comparison

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Bridges_JointCollision
attribute [-instance] _root_.OAI.HardSphere.Bridge.exposedBridgeKernel_markov _root_.OAI.HardSphere.Bridge.exposedPeriodSingle_finite _root_.OAI.HardSphere.Bridge.exposedTrialKernel_markov _root_.OAI.HardSphere.Bridge.instIsProbabilityMeasurePointMidpointNoise _root_.OAI.HardSphere.Bridge.midpointLaw_probability _root_.OAI.HardSphere.Bridge.parameterBridgeKernel_markov _root_.OAI.HardSphere.Bridge.parameterIndividualReference_finite _root_.OAI.HardSphere.Bridge.parameterTrialKernel_markov _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Bridge.targetUniform_finite _root_.OAI.HardSphere.Comparison.parameterTargetKernel_finite _root_.OAI.HardSphere.Groups.cellPathReference_probability _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Rescaling.config_haar _root_.OAI.HardSphere.bridgeEndpointBase_finite _root_.OAI.HardSphere.endpointWeightedBase_sfinite
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
open Wiener GaussianPacking Comparison

variable {I : Type*} [DecidableEq I] {L : Length}
  (S : I→Set C(Time,Point))

lemma physicalPairCheck_symmetric (r : ℝ) (f g : C(Time,Point)) :
    TrialCollision (L:=L) r (projectCurve L g) f ↔ TrialCollision r (projectCurve L f) g := by
  unfold TrialCollision
  apply exists_congr
  intro s
  change torusDistance L (projectPoint L (f s)) (projectPoint L (g s)) ≤ r ↔
    torusDistance L (projectPoint L (g s)) (projectPoint L (f s)) ≤ r
  rw [torusDistance_comm]

end HardSphere.Bridge

end
end

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Comparison_FiberNormalize
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
open scoped ENNReal
namespace HardSphere.Comparison
variable {W V : Type*} [MeasurableSpace W] [MeasurableSpace V]

lemma fiberRestrict_apply (κ : Kernel W V) [IsSFiniteKernel κ] {C : Set (W×V)}
    (hC : MeasurableSet C) (w : W) :
    fiberRestrict κ C w=(κ w).restrict {v | (w,v)∈C} := by
  have hm : Measurable (Function.uncurry (fun w : W ↦ fun v : V ↦ C.indicator (fun _ ↦ (1 : ℝ≥0∞)) (w,v))) := by
    change Measurable (C.indicator (fun _ ↦ (1 : ℝ≥0∞)))
    exact measurable_const.indicator hC
  rw [fiberRestrict,Kernel.withDensity_apply _ hm]
  have he : (fun v ↦ C.indicator (fun _ ↦ (1 : ℝ≥0∞)) (w,v))=
      {v | (w,v)∈C}.indicator (fun _ ↦ (1 : ℝ≥0∞)) := rfl
  rw [he]
  have hs : MeasurableSet {v : V | (w,v)∈C} := hC.preimage (measurable_const.prodMk measurable_id)
  exact withDensity_indicator_one hs

lemma fiberNormalize_mass (κ : Kernel W V) [IsFiniteKernel κ] {C : Set (W×V)}
    (hC : MeasurableSet C) {w : W} (hw : 0<κ w {v | (w,v)∈C}) :
    fiberNormalize κ C w univ=1 := by
  change ((fiberRestrict κ C w univ)⁻¹ • fiberRestrict κ C w) univ=1
  rw [fiberRestrict_apply κ hC,Measure.smul_apply,smul_eq_mul,Measure.restrict_apply_univ]
  exact ENNReal.inv_mul_cancel hw.ne' (measure_ne_top _ _)

end HardSphere.Comparison

end
end

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Kernels_FiniteKernelPi
attribute [-instance] _root_.OAI.HardSphere.Groups.labelOptionSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace HardSphere.Comparison

lemma finiteKernelPi_apply {α ι : Type*} [MeasurableSpace α] [Fintype ι]
    {β : ι → Type*} [∀ i, MeasurableSpace (β i)]
    (κ : ∀ i, Kernel α (β i)) [∀ i, IsFiniteKernel (κ i)] (a : α) :
    finiteKernelPi κ a = Measure.pi (fun i ↦ κ i a) :=
  (exists_kernel_pi β κ).choose_spec.2 a

end HardSphere.Comparison

end
end
end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_AuxiliaryChecks
attribute [-instance] _root_.OAI.HardSphere.Comparison.instFintypeFrozenCheckIndex _root_.OAI.HardSphere.Comparison.proposalKernel_finite _root_.OAI.HardSphere.Groups.labelOptionSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
open MeasureTheory Function Set Filter
open scoped ENNReal BigOperators
namespace HardSphere.Comparison
open ProbabilityTheory

section ConditionalNormalizers
variable {ι : Type*} [DecidableEq ι] {X : ι → Type*}
  [∀ i, MeasurableSpace (X i)] {C : Type*} [Fintype C]
  (checks : C → LocalCheck X)

omit [Fintype C] in
lemma insertion_integral_lower_on {μ : ∀ i, Measure (X i)} {a : ℝ≥0∞}
    {r : Finset ι} (hcompat : UniformInsertionOn checks μ a r)
    {s : Finset ι} {i : ι} (hir : i ∈ r) (hi : i ∉ s) (x : ∀ i, X i) :
    a * checkWeight checks s x ≤
      ∫⁻ y, checkWeight checks (insert i s) (Function.update x i y) ∂μ i := by
  classical
  by_cases hx : x ∈ retainedEvent checks s
  · have heq : (fun y ↦ checkWeight checks (insert i s) (Function.update x i y)) =
        fun y ↦ (insertionEvent checks s i).indicator (fun _ ↦ (1 : ℝ≥0∞))
          (Function.update x i y) := by
      funext y
      have hu := (retainedEvent_update checks hi x y).2 hx
      simp [checkWeight, retainedEvent_insert, Set.indicator_apply, hu]
    rw [heq]
    simpa [checkWeight, hx] using hcompat i hir s hi x
  · simp [checkWeight, hx]

lemma partialNormalizer_insert_lower {μ : ∀ i, Measure (X i)}
    [∀ i, SigmaFinite (μ i)] {a : ℝ≥0∞} {r : Finset ι}
    (hcompat : UniformInsertionOn checks μ a r) {s o : Finset ι} {i : ι}
    (hir : i ∈ r) (hi : i ∉ s ∪ o) (x : ∀ i, X i) :
    a * partialNormalizer checks μ s o x ≤
      partialNormalizer checks μ (insert i s) o x := by
  have his : i ∉ s := fun h ↦ hi (Finset.mem_union_left o h)
  rw [partialNormalizer, partialNormalizer, Finset.insert_union,
    lmarginal_insert' _ (measurable_checkWeight checks _) his]
  calc
    a * lmarginal μ s (checkWeight checks (s ∪ o)) x =
        lmarginal μ s (fun x ↦ a * checkWeight checks (s ∪ o) x) x := by
      dsimp [lmarginal]
      exact (lintegral_const_mul a ((measurable_checkWeight checks (s ∪ o)).comp
        (measurable_updateFinset (x := x) (s := s)))).symm
    _ ≤ _ := lmarginal_mono (insertion_integral_lower_on checks hcompat hir hi) x

lemma partialNormalizer_union_lower {μ : ∀ i, Measure (X i)}
    [∀ i, SigmaFinite (μ i)] {a : ℝ≥0∞} {r : Finset ι}
    (hcompat : UniformInsertionOn checks μ a r)
    (s t o : Finset ι) (htr : t ⊆ r) (hto : Disjoint (s ∪ o) t)
    (x : ∀ i, X i) :
    a ^ t.card * partialNormalizer checks μ s o x ≤
      partialNormalizer checks μ (s ∪ t) o x := by
  induction t using Finset.induction_on with
  | empty => simp
  | @insert i t hit ih =>
    have hino : i ∉ s ∪ o := (Finset.disjoint_insert_right.mp hto).1
    have hto' := (Finset.disjoint_insert_right.mp hto).2
    have hiu : i ∉ (s ∪ t) ∪ o := by
      simp only [Finset.mem_union, not_or] at hino ⊢
      exact ⟨⟨hino.1, hit⟩, hino.2⟩
    calc
      a ^ (insert i t).card * partialNormalizer checks μ s o x =
          a * (a ^ t.card * partialNormalizer checks μ s o x) := by
        rw [Finset.card_insert_of_notMem hit, pow_succ]
        ac_rfl
      _ ≤ a * partialNormalizer checks μ (s ∪ t) o x :=
        mul_le_mul_right (ih ((Finset.subset_insert _ _).trans htr) hto') a
      _ ≤ partialNormalizer checks μ (insert i (s ∪ t)) o x :=
        partialNormalizer_insert_lower checks hcompat (htr (Finset.mem_insert_self _ _)) hiu x
      _ = _ := by rw [Finset.union_insert]

lemma partialNormalizer_pos {μ : ∀ i, Measure (X i)} [∀ i, SigmaFinite (μ i)]
    {a : ℝ≥0∞} (ha : 0 < a) {s o : Finset ι}
    (hcompat : UniformInsertionOn checks μ a s) (hso : Disjoint s o)
    (x : ∀ i, X i) (hx : x ∈ retainedEvent checks o) :
    0 < partialNormalizer checks μ s o x := by
  have h := partialNormalizer_union_lower checks hcompat ∅ s o (Finset.Subset.refl s)
    (by simpa using hso.symm) x
  simp only [partialNormalizer, Finset.empty_union, lmarginal_empty, checkWeight,
    Set.indicator_of_mem hx, mul_one] at h
  exact lt_of_lt_of_le (by positivity) h

end ConditionalNormalizers

end HardSphere.Comparison
end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Collisions_Insertion
attribute [-instance] _root_.OAI.HardSphere.Comparison.instFintypeFrozenCheckIndex _root_.OAI.HardSphere.Comparison.proposalKernel_finite _root_.OAI.HardSphere.Groups.labelOptionSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators
namespace HardSphere.Comparison
variable {ι C : Type*} [Fintype ι] [Fintype C] [DecidableEq ι]
  {X : ι → Type*} [∀i,MeasurableSpace (X i)]

omit [Fintype ι] in
lemma uniformInsertionOn_of_check_failures (checks : C → LocalCheck X)
    (μ : ∀i,Measure (X i)) [∀i,IsProbabilityMeasure (μ i)]
    (p : ι → C → ℝ≥0∞) (a : ℝ≥0∞) (r : Finset ι)
    (hfail : ∀i∈r, ∀c, i∈(checks c).support → ∀x : ∀j,X j,
      μ i {y | ¬(checks c).pass (Function.update x i y)} ≤ p i c)
    (htotal : ∀i∈r,a+(∑c∈Finset.univ.filter (fun c ↦ i∈(checks c).support),p i c) ≤ 1) :
    UniformInsertionOn checks μ a r := by
  classical
  intro i hir s hi x
  let B : Set (X i) := {y | Function.update x i y ∈ insertionEvent checks s i}
  have hm : Measurable (fun y : X i ↦ Function.update x i y) := by
    fun_prop
  have hB : MeasurableSet B := (measurableSet_insertionEvent checks s i).preimage hm
  have hsub : Bᶜ ⊆ ⋃c∈Finset.univ.filter (fun c ↦ i∈(checks c).support),
      {y | ¬(checks c).pass (Function.update x i y)} := by
    intro y hy
    classical
    simp only [B,Set.mem_compl_iff,Set.mem_ofPred_eq,insertionEvent] at hy
    push Not at hy
    rcases hy with ⟨c,hc,hcs,hp⟩
    have hci : i∈(checks c).support := by
      by_contra hn
      apply hcs
      intro j hj
      have h := hc hj
      rcases Finset.mem_insert.mp h with he|hs
      · subst j; contradiction
      · exact hs
    exact mem_iUnion.2 ⟨c,mem_iUnion.2 ⟨by simp [hci],hp⟩⟩
  have hb : μ i Bᶜ ≤ ∑c∈Finset.univ.filter (fun c ↦ i∈(checks c).support),p i c := by
    apply (measure_mono hsub).trans
    apply (measure_biUnion_finset_le _ _).trans
    exact Finset.sum_le_sum fun c hc ↦ hfail i hir c (Finset.mem_filter.mp hc).2 x
  have hadd : a+μ i Bᶜ ≤ μ i B+μ i Bᶜ := by
    rw [measure_add_measure_compl hB]
    exact (add_le_add_right hb a).trans (by simpa using htotal i hir)
  have ha : a≤μ i B := (ENNReal.add_le_add_iff_right (measure_ne_top _ _)).mp hadd
  have he : (fun y ↦ (insertionEvent checks s i).indicator (fun _ ↦ (1 : ℝ≥0∞)) (Function.update x i y))=
      B.indicator (fun _ ↦ (1 : ℝ≥0∞)) := by funext y; simp [B,Set.indicator_apply]
  rw [he,lintegral_indicator hB]
  simpa using ha

end HardSphere.Comparison

end
end

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Conditioning_RestrictedMeasure
attribute [-instance] _root_.OAI.HardSphere.Groups.labelOptionSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace HardSphere.Comparison
variable {X : Type*} [MeasurableSpace X]

lemma subtypeConditional_map (P : Measure X) {S : Set X} (hS : MeasurableSet S) :
    (subtypeConditional P S).map (Subtype.val:S→X)=(P S)⁻¹ • P.restrict S := by
  rw [subtypeConditional,Measure.map_smul, map_comap_subtype_coe hS]

end HardSphere.Comparison

end
end

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Bridges_PhysicalInsertion
attribute [-instance] _root_.OAI.HardSphere.Bridge.exposedBridgeKernel_markov _root_.OAI.HardSphere.Bridge.exposedPeriodSingle_finite _root_.OAI.HardSphere.Bridge.exposedTrialKernel_markov _root_.OAI.HardSphere.Bridge.parameterBridgeKernel_markov _root_.OAI.HardSphere.Bridge.parameterIndividualReference_finite _root_.OAI.HardSphere.Bridge.parameterTrialKernel_markov _root_.OAI.HardSphere.Bridge.targetUniform_finite _root_.OAI.HardSphere.Comparison.parameterTargetKernel_finite _root_.OAI.HardSphere.Groups.cellPathReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite
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
open Wiener GaussianPacking PathCutoff Comparison

lemma referenceOn_map (t : ℝ) (y z : Point) {S : Set C(Time,Point)} (hS : MeasurableSet S) :
    (referenceOn t y z S).map Subtype.val=individualReference t y z S :=
  subtypeConditional_map _ hS

end HardSphere.Bridge

end
end

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Bridges_ConfinedLift
attribute [-instance] _root_.OAI.HardSphere.Bridge.exposedBridgeKernel_markov _root_.OAI.HardSphere.Bridge.exposedPeriodSingle_finite _root_.OAI.HardSphere.Bridge.exposedTrialKernel_markov _root_.OAI.HardSphere.Bridge.parameterBridgeKernel_markov _root_.OAI.HardSphere.Bridge.parameterIndividualReference_finite _root_.OAI.HardSphere.Bridge.parameterTrialKernel_markov _root_.OAI.HardSphere.Bridge.targetUniform_finite _root_.OAI.HardSphere.Comparison.parameterTargetKernel_finite _root_.OAI.HardSphere.Groups.cellPathReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite
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

lemma leg_translate (t : ℝ) (y z c : Point) (β : Noise) :
    leg t (y+c) (z+c) β=leg t y z β+ContinuousMap.const _ c := by
  ext s j
  change (1-(s:ℝ))*(y j+c j)+(s:ℝ)*(z j+c j)+Real.sqrt (2*t)*β j s=
    ((1-(s:ℝ))*y j+(s:ℝ)*z j+Real.sqrt (2*t)*β j s)+c j
  ring

end HardSphere.Bridge

end
end

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Conditioning_ConditionTransport
attribute [-instance] _root_.OAI.HardSphere.Comparison.conditioned_finite _root_.OAI.HardSphere.Groups.labelOptionSpace
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
namespace HardSphere.Comparison
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
lemma conditioned_map_preimage (μ : Measure X) (f : X→Y) (hf : Measurable f)
    {S : Set Y} (hS : MeasurableSet S) :
    (conditionedMeasure μ (f⁻¹' S)).map f=conditionedMeasure (μ.map f) S := by
  unfold conditionedMeasure
  rw [Measure.map_smul,Measure.map_apply hf hS]
  congr 1
  ext B hB
  rw [Measure.map_apply hf hB,Measure.restrict_apply (hB.preimage hf),
    Measure.restrict_apply hB,Measure.map_apply hf (hB.inter hS)]
  rfl

end HardSphere.Comparison

end
end

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_GridAlignment
attribute [-instance] _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Lattice.environmentMeasurableSpace _root_.OAI.HardSphere.Lattice.simplePathCountable _root_.OAI.HardSphere.Lattice.simplePathMeasurableSpace _root_.OAI.HardSphere.Rescaling.config_haar _root_.OAI.HardSphere.bridgeEndpointBase_finite _root_.OAI.HardSphere.endpointWeightedBase_sfinite
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
open Classical
namespace HardSphere.Groups
open CellOrbital BathSlice HardSphere.Lattice ShiftVisits

lemma gridSite_injective {K : ℕ} [NeZero K] : Function.Injective (gridSite (K:=K)) := by
  intro v w h
  funext j
  apply Fin.ext
  have hh := congrArg (fun f : DiscreteTorus K ↦ (f j).val) h
  simpa only [gridSite,ZMod.val_natCast_of_lt (v j).isLt,ZMod.val_natCast_of_lt (w j).isLt] using hh

end HardSphere.Groups

end
end

section
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.Groups
open HardSphere.Lattice HardSphere.FreeVisits HardSphere.CellOrbital
attribute [local instance] Classical.propDecidable

lemma card_rangePackingBox (c : Fin 3→ℝ) : (rangePackingBox c).card=49^3 := by
  unfold rangePackingBox
  rw [Pi.card_Icc]
  have h (j : Fin 3) : (Finset.Icc (⌊c j⌋-24) (⌊c j⌋+24)).card=49 := by rw [Int.card_Icc]; omega
  simp only [h,Finset.prod_const,Finset.card_univ,Fintype.card_fin]

lemma grid_packing_witness {K : ℕ} [NeZero K] (L : Length) (hL : L.val=(K:ℝ))
    (c : Fin 3→ℝ) (v : Fin 3→Fin K)
    (hv : ∀j,dist (gridCenter L v j) ((c j:ℝ):AddCircle L.val)≤23) :
    ∃z∈rangePackingBox c,torusProjection K z=gridSite v := by
  let k : Vertex := fun j ↦ round (L.val⁻¹*((v j).val-c j))
  let z : Vertex := fun j ↦ ((v j).val:ℤ)-k j*(K:ℤ)
  refine ⟨z,?_,?_⟩
  · apply Finset.mem_Icc.mpr
    have hz (j : Fin 3) : ⌊c j⌋-24≤z j ∧ z j≤⌊c j⌋+24 := by
      have hd := hv j
      change dist (((v j).val:ℝ):AddCircle L.val) ((c j:ℝ):AddCircle L.val)≤23 at hd
      rw [dist_eq_norm,←AddCircle.coe_sub,AddCircle.norm_eq] at hd
      have hd' : |(z j:ℝ)-c j|≤23 := by
        convert hd using 1
        all_goals try with_reducible_and_instances rfl
        dsimp [z,k]
        push_cast
        rw [hL]
        ring_nf
      have hl := Int.floor_le (c j)
      have hu := Int.lt_floor_add_one (c j)
      obtain ⟨h₁,h₂⟩ := abs_le.mp hd'
      constructor <;> (apply (Int.cast_le (R:=ℝ)).mp; push_cast; linarith)
    exact ⟨fun j ↦ (hz j).1,fun j ↦ (hz j).2⟩
  · ext j
    simp [torusProjection,z,gridSite]

lemma card_near_grid_le {K : ℕ} [NeZero K] (L : Length) (hL : L.val=(K:ℝ))
    (x : Torus L) (A : Finset (Fin 3→Fin K))
    (hA : ∀v∈A,torusDistance L (gridCenter L v) x≤23) : A.card≤49^3 := by
  let c : Fin 3→ℝ := fun j ↦ (AddCircle.equivIco L.val 0 (x j)).val
  have hc (j : Fin 3) : ((c j:ℝ):AddCircle L.val)=x j := AddCircle.coe_equivIco
  have hsub : A.image gridSite⊆(rangePackingBox c).image (torusProjection K) := by
    intro v hv
    obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hv
    obtain ⟨z,hz,he⟩ := grid_packing_witness L hL c w (fun j ↦ by
      rw [hc]
      exact (dist_coord_le_torusDistance L (gridCenter L w) x j).trans (hA w hw))
    exact Finset.mem_image.mpr ⟨z,hz,he⟩
  have hh : (A.image gridSite).card≤49^3 :=
    (Finset.card_le_card hsub).trans (Finset.card_image_le.trans (card_rangePackingBox c).le)
  rwa [Finset.card_image_of_injective A gridSite_injective] at hh

lemma card_near_labels {I : Type*} [Fintype I] {K : ℕ} [NeZero K]
    (L : Length) (hL : L.val=(K:ℝ)) (anchor : I→Fin 3→Fin K) (M : ℕ)
    (hm : ∀v,(Finset.univ.filter (fun i : I ↦ anchor i=v)).card≤M) (x : Torus L) :
    (Finset.univ.filter (fun i : I ↦ torusDistance L (gridCenter L (anchor i)) x≤23)).card≤49^3*M := by
  let A : Finset (Fin 3→Fin K) := Finset.univ.filter (fun v ↦ torusDistance L (gridCenter L v) x≤23)
  let S : Finset I := Finset.univ.filter (fun i ↦ torusDistance L (gridCenter L (anchor i)) x≤23)
  have hs : ∀i∈S,anchor i∈A := by intro i hi; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp hi).2⟩
  have hcard := Finset.card_eq_sum_card_fiberwise hs
  change S.card≤_
  rw [hcard]
  calc
    _ ≤ ∑_v∈A,M := Finset.sum_le_sum (fun v _ ↦ (Finset.card_le_card (by
      intro i hi
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp hi).2⟩)).trans (hm v))
    _ = A.card*M := by simp
    _ ≤ 49^3*M := Nat.mul_le_mul_right _ (card_near_grid_le L hL x A (fun v hv ↦ (Finset.mem_filter.mp hv).2))

end HardSphere.Groups

end
end

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Kernels_ExposedPhysicalPair
attribute [-instance] _root_.OAI.HardSphere.Bridge.exposedBridgeKernel_markov _root_.OAI.HardSphere.Bridge.exposedPeriodSingle_finite _root_.OAI.HardSphere.Bridge.parameterBridgeKernel_markov _root_.OAI.HardSphere.Bridge.parameterIndividualReference_finite _root_.OAI.HardSphere.Bridge.targetUniform_finite _root_.OAI.HardSphere.Comparison.parameterTargetKernel_finite _root_.OAI.HardSphere.Groups.cellPathReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite
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
open Wiener GaussianPacking Comparison
variable {E : Type*} [MeasurableSpace E]

lemma parameterTrialSuccess_apply (t : ℝ) (y z : E→Point) (hy : Measurable y) (hz : Measurable z)
    (S : Set (E×C(Time,Point))) (hS : MeasurableSet S) (e : E) (u : Point) :
    parameterSuccessKernel (parameterTrialKernel t y z hy hz) (exposedSuccess S)
      (exposedSuccess_measurable hS) (e,u)=
    successKernel (trialKernel t (y e) (z e)) (Prod.mk e ⁻¹' S)
      (hS.preimage measurable_prodMk_left) u := by
  rw [parameterSuccessKernel_apply,successKernel_apply,parameterTrialKernel_apply]
  rfl

lemma exposedPairedTrialKernel_apply (Q : Kernel E Point) [IsFiniteKernel Q] (t : ℝ)
    (y z y' z' : E→Point) (hy : Measurable y) (hz : Measurable z)
    (hy' : Measurable y') (hz' : Measurable z')
    (S T : Set (E×C(Time,Point))) (hS : MeasurableSet S) (hT : MeasurableSet T) (e : E) :
    exposedPairedTrialKernel Q t y z y' z' hy hz hy' hz' S T hS hT e=
      (pairedFactor (Q e) (trialKernel t (y e) (z e)) (trialKernel t (y' e) (z' e))
        (Prod.mk e ⁻¹' S) (Prod.mk e ⁻¹' T)
        (hS.preimage measurable_prodMk_left) (hT.preimage measurable_prodMk_left)).map
        (fun p ↦ (p.2.1,(p.1,p.2.2))) := by
  rw [exposedPairedTrialKernel,Kernel.map_apply _ (by fun_prop)]
  congr 1
  ext B hB
  rw [parameterPairedKernel,Kernel.compProd_apply hB,pairedFactor,Measure.compProd_apply hB]
  apply lintegral_congr
  intro u
  rw [Kernel.prod_apply,Kernel.prod_apply,parameterTrialSuccess_apply,parameterTrialSuccess_apply] <;> assumption

lemma exposedPairedTrialKernel_physical (Q : Kernel E Point) [IsFiniteKernel Q] (t : ℝ)
    (y z y' z' : E→Point) (hy : Measurable y) (hz : Measurable z)
    (hy' : Measurable y') (hz' : Measurable z')
    (S T : Set (E×C(Time,Point))) (hS : MeasurableSet S) (hT : MeasurableSet T)
    (A : E→Set Point) (hQ : ∀e,Q e=targetUniform (A e)) (e : E) :
    exposedPairedTrialKernel Q t y z y' z' hy hz hy' hz' S T hS hT e=
      pairedTrialLaw t (y e) (z e) (y' e) (z' e) (A e)
        (Prod.mk e ⁻¹' S) (Prod.mk e ⁻¹' T)
        (hS.preimage measurable_prodMk_left) (hT.preimage measurable_prodMk_left) := by
  rw [exposedPairedTrialKernel_apply,hQ]
  rfl

end HardSphere.Bridge

end
end

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Bridges_ExposedReference
attribute [-instance] _root_.OAI.HardSphere.Bridge.exposedPeriodSingle_finite _root_.OAI.HardSphere.Bridge.targetUniform_finite _root_.OAI.HardSphere.Comparison.parameterTargetKernel_finite _root_.OAI.HardSphere.Groups.cellPathReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite
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
open Wiener GaussianPacking Comparison
variable {E : Type*} [MeasurableSpace E]

lemma exposedBridgeKernel_apply (t : ℝ) (y z : Point) :
    exposedBridgeKernel t (y,z)=law.map (leg t y z) := by
  rw [exposedBridgeKernel,Kernel.map_apply _ (leg_all_continuous t).measurable,
    Kernel.prod_apply,Kernel.deterministic_apply,Kernel.const_apply,Measure.dirac_prod,
    Measure.map_map (leg_all_continuous t).measurable
      (measurable_const.prodMk measurable_id : Measurable (Prod.mk (id (y,z))))]
  rfl

lemma parameterBridgeKernel_apply (t : ℝ) (y z : E→Point) (hy : Measurable y) (hz : Measurable z) (e : E) :
    parameterBridgeKernel t y z hy hz e=law.map (leg t (y e) (z e)) := exposedBridgeKernel_apply _ _ _

lemma parameterIndividualReference_apply (t : ℝ) (y z : E→Point) (hy : Measurable y) (hz : Measurable z)
    (S : Set (E×C(Time,Point))) (hS : MeasurableSet S) (e : E) :
    parameterIndividualReference t y z hy hz S hS e=individualReference t (y e) (z e) (Prod.mk e ⁻¹' S) := by
  rw [parameterIndividualReference,parameterSuccessKernel_apply,parameterBridgeKernel_apply]
  rfl

end HardSphere.Bridge

end
end

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Bridges_PairedMarginal
attribute [-instance] _root_.OAI.HardSphere.Bridge.exposedBridgeKernel_markov _root_.OAI.HardSphere.Bridge.exposedPeriodSingle_finite _root_.OAI.HardSphere.Bridge.exposedTrialKernel_markov _root_.OAI.HardSphere.Bridge.parameterBridgeKernel_markov _root_.OAI.HardSphere.Bridge.parameterIndividualReference_finite _root_.OAI.HardSphere.Bridge.parameterTrialKernel_markov _root_.OAI.HardSphere.Bridge.targetUniform_finite _root_.OAI.HardSphere.Comparison.parameterTargetKernel_finite _root_.OAI.HardSphere.Groups.cellPathReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite
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
open Wiener GaussianPacking PathCutoff Comparison

lemma pairedTrialLaw_other (t : ℝ) (y z y' z' : Point) (A : Set Point)
    (hA0 : volume A≠0) (hAfinite : volume A≠⊤)
    (S T : Set C(Time,Point)) (hS : MeasurableSet S) (hT : MeasurableSet T)
    (hκ : ∀ᵐu ∂targetUniform A,0<trialKernel t y z u S) :
    (pairedTrialLaw t y z y' z' A S T hS hT).map (fun p ↦ p.2.2)=
      ((targetUniform A).compProd (successKernel (trialKernel t y' z') T hT)).map Prod.snd := by
  let _ : IsProbabilityMeasure (targetUniform A) := targetUniform_probability hA0 hAfinite
  have h := congrArg (fun μ : Measure (Point×C(Time,Point)) ↦ μ.map Prod.snd)
    (pairedFactor_snd (targetUniform A) (trialKernel t y z) (trialKernel t y' z') S T hS hT hκ)
  rw [Measure.map_map measurable_snd (by fun_prop)] at h
  unfold pairedTrialLaw
  rw [Measure.map_map (by fun_prop) (by fun_prop)]
  exact h

lemma pairedTrialLaw_marginals {t C C' : ℝ} (ht : 0<t) (hC : 0≤C) (hC' : 0≤C')
    (y z y' z' : Point) {A : Set Point} (hA : MeasurableSet A)
    (hA0 : volume A≠0) (hAfinite : volume A≠⊤)
    (hb : ∀u∈A,‖u-(fun j ↦ (y j+z j)/2)‖≤C)
    (hb' : ∀u∈A,‖u-(fun j ↦ (y' j+z' j)/2)‖≤C')
    (S T : Set C(Time,Point)) (hS : MeasurableSet S) (hT : MeasurableSet T)
    {c d : ℝ≥0∞} (hc0 : 0 < c) (hd0 : 0<d)
    (hc : ∀ᵐu ∂targetUniform A,c≤trialKernel t y z u S)
    (hd : ∀ᵐu ∂targetUniform A,d≤trialKernel t y' z' u T) :
    (pairedTrialLaw t y z y' z' A S T hS hT).fst≤
      (c⁻¹*((volume A)⁻¹*(midpointLower t C)⁻¹)) • individualReference t y z S ∧
    (pairedTrialLaw t y z y' z' A S T hS hT).map (fun p ↦ p.2.2)≤
      (d⁻¹*((volume A)⁻¹*(midpointLower t C')⁻¹)) • individualReference t y' z' T := by
  constructor
  · rw [pairedTrialLaw_fst t y z y' z' A hA0 hAfinite S T hS hT (hd.mono (fun _ h ↦ hd0.trans_le h))]
    exact physical_trial_le_reference ht hC y z hA hAfinite hb S hS hc
  · rw [pairedTrialLaw_other t y z y' z' A hA0 hAfinite S T hS hT (hc.mono (fun _ h ↦ hc0.trans_le h))]
    exact physical_trial_le_reference ht hC' y' z' hA hAfinite hb' T hT hd

end HardSphere.Bridge

end
end

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Conditioning_SupportedPair
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
open scoped ENNReal
namespace HardSphere.Comparison
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

lemma supportedPair_map (ρ : Measure (X×Y)) {S : Set X} {T : Set Y}
    (hS : MeasurableSet S) (hT : MeasurableSet T) (hρ : ∀ᵐp ∂ρ,p.1∈S ∧ p.2∈T) :
    (supportedPair ρ S T).map (Prod.map Subtype.val Subtype.val)=ρ := by
  rw [supportedPair,((MeasurableEmbedding.subtype_coe hS).prodMap
    (MeasurableEmbedding.subtype_coe hT)).map_comap]
  apply Measure.restrict_eq_self_of_ae_mem
  filter_upwards [hρ] with p hp
  exact ⟨(⟨p.1,hp.1⟩,⟨p.2,hp.2⟩),rfl⟩

lemma supportedPair_probability (ρ : Measure (X×Y)) [IsProbabilityMeasure ρ]
    {S : Set X} {T : Set Y} (hS : MeasurableSet S) (hT : MeasurableSet T)
    (hρ : ∀ᵐp ∂ρ,p.1∈S ∧ p.2∈T) : IsProbabilityMeasure (supportedPair ρ S T) := by
  constructor
  have h := congrArg (fun μ : Measure (X×Y) ↦ μ univ) (supportedPair_map ρ hS hT hρ)
  simpa only [Measure.map_apply (by fun_prop : Measurable (Prod.map (Subtype.val:S→X) (Subtype.val:T→Y)))
    MeasurableSet.univ,preimage_univ,measure_univ] using h

lemma map_le_reflect {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    {f : A→B} (hf : MeasurableEmbedding f) {μ ν : Measure A}
    (h : μ.map f≤ν.map f) : μ≤ν := by
  apply Measure.le_iff.mpr
  intro C hC
  have hh := h (f '' C)
  simpa only [hf.map_apply,hf.injective.preimage_image] using hh

lemma supportedPair_fst (ρ : Measure (X×Y)) {S : Set X} {T : Set Y}
    (hS : MeasurableSet S) (hT : MeasurableSet T) (hρ : ∀ᵐp ∂ρ,p.1∈S ∧ p.2∈T) :
    (supportedPair ρ S T).fst.map Subtype.val=ρ.fst := by
  have h := congrArg (fun μ : Measure (X×Y) ↦ μ.fst) (supportedPair_map ρ hS hT hρ)
  rw [Measure.fst,Measure.map_map measurable_fst (by fun_prop)] at h
  rw [Measure.fst,Measure.map_map measurable_subtype_coe measurable_fst]
  exact h

lemma supportedPair_snd (ρ : Measure (X×Y)) {S : Set X} {T : Set Y}
    (hS : MeasurableSet S) (hT : MeasurableSet T) (hρ : ∀ᵐp ∂ρ,p.1∈S ∧ p.2∈T) :
    (supportedPair ρ S T).snd.map Subtype.val=ρ.snd := by
  have h := congrArg (fun μ : Measure (X×Y) ↦ μ.snd) (supportedPair_map ρ hS hT hρ)
  rw [Measure.snd,Measure.map_map measurable_snd (by fun_prop)] at h
  rw [Measure.snd,Measure.map_map measurable_subtype_coe measurable_snd]
  exact h

lemma supportedPair_fst_le (ρ : Measure (X×Y)) {S : Set X} {T : Set Y}
    (hS : MeasurableSet S) (hT : MeasurableSet T) (hρ : ∀ᵐp ∂ρ,p.1∈S ∧ p.2∈T)
    (P : Measure S) {G : ℝ≥0∞} (hP : ρ.fst≤G • P.map Subtype.val) :
    (supportedPair ρ S T).fst≤G • P := by
  apply map_le_reflect (MeasurableEmbedding.subtype_coe hS)
  rw [supportedPair_fst ρ hS hT hρ,Measure.map_smul]
  exact hP

lemma supportedPair_snd_le (ρ : Measure (X×Y)) {S : Set X} {T : Set Y}
    (hS : MeasurableSet S) (hT : MeasurableSet T) (hρ : ∀ᵐp ∂ρ,p.1∈S ∧ p.2∈T)
    (P : Measure T) {G : ℝ≥0∞} (hP : ρ.snd≤G • P.map Subtype.val) :
    (supportedPair ρ S T).snd≤G • P := by
  apply map_le_reflect (MeasurableEmbedding.subtype_coe hT)
  rw [supportedPair_snd ρ hS hT hρ,Measure.map_smul]
  exact hP

lemma supported_of_marginals (ρ : Measure (X×Y)) {S : Set X} {T : Set Y}
    (hS : MeasurableSet S) (hT : MeasurableSet T) (P : Measure S) (Q : Measure T)
    {G H : ℝ≥0∞} (hP : ρ.fst≤G • P.map Subtype.val) (hQ : ρ.snd≤H • Q.map Subtype.val) :
    ∀ᵐp ∂ρ,p.1∈S ∧ p.2∈T := by
  have hp0 : (P.map Subtype.val) Sᶜ=0 := by
    rw [Measure.map_apply measurable_subtype_coe hS.compl]
    have he : (Subtype.val:S→X) ⁻¹' Sᶜ=∅ := by ext x; simp only [mem_preimage,mem_compl_iff,x.property,not_true,mem_empty_iff_false]
    rw [he,measure_empty]
  have hq0 : (Q.map Subtype.val) Tᶜ=0 := by
    rw [Measure.map_apply measurable_subtype_coe hT.compl]
    have he : (Subtype.val:T→Y) ⁻¹' Tᶜ=∅ := by ext x; simp only [mem_preimage,mem_compl_iff,x.property,not_true,mem_empty_iff_false]
    rw [he,measure_empty]
  have hpa : ∀ᵐx ∂ρ.fst,x∈S := by
    rw [ae_iff]
    change ρ.fst Sᶜ=0
    exact le_antisymm (by simpa only [Measure.smul_apply,smul_eq_mul,hp0,mul_zero] using hP Sᶜ) bot_le
  have hqa : ∀ᵐy ∂ρ.snd,y∈T := by
    rw [ae_iff]
    change ρ.snd Tᶜ=0
    exact le_antisymm (by simpa only [Measure.smul_apply,smul_eq_mul,hq0,mul_zero] using hQ Tᶜ) bot_le
  have hp' : ∀ᵐp ∂ρ,p.1∈S := (ae_map_iff measurable_fst.aemeasurable hS).mp hpa
  have hq' : ∀ᵐp ∂ρ,p.2∈T := (ae_map_iff measurable_snd.aemeasurable hT).mp hqa
  exact hp'.and hq'

end HardSphere.Comparison

end
end

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Bridges_PeriodShift
attribute [-instance] _root_.OAI.HardSphere.Bridge.exposedBridgeKernel_markov _root_.OAI.HardSphere.Bridge.exposedPeriodSingle_finite _root_.OAI.HardSphere.Bridge.exposedTrialKernel_markov _root_.OAI.HardSphere.Bridge.parameterBridgeKernel_markov _root_.OAI.HardSphere.Bridge.parameterIndividualReference_finite _root_.OAI.HardSphere.Bridge.parameterTrialKernel_markov _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Bridge.targetUniform_finite _root_.OAI.HardSphere.Comparison.conditioned_finite _root_.OAI.HardSphere.Comparison.parameterTargetKernel_finite _root_.OAI.HardSphere.Groups.cellPathReference_probability _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Rescaling.config_haar _root_.OAI.HardSphere.bridgeEndpointBase_finite _root_.OAI.HardSphere.endpointWeightedBase_sfinite
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
open Wiener GaussianPacking PathCutoff Comparison

lemma shiftPath_cancel (c : Point) (f : C(Time,Point)) : shiftPath (-c) (shiftPath c f)=f := by
  ext s j
  change (f s j+c j)+(-c j)=f s j
  ring

lemma projectPoint_shift {L : Length} (c : Point) (hc : projectPoint L c=0) (v : Point) :
    projectPoint L (v+c)=projectPoint L v := by
  ext j
  change (((v j+c j):ℝ):AddCircle L.val)=_
  rw [AddCircle.coe_add]
  have h := congrFun hc j
  change ((c j:ℝ):AddCircle L.val)=0 at h
  rw [h,add_zero]

lemma trialPath_shift (t : ℝ) (y z u c : Point) (β : Noise×Noise) :
    trialPath t (y+c) (z+c) (u+c) β=shiftPath c (trialPath t y z u β) := by
  ext s j
  change (leg t (y+c) (u+c) (pinned β.1) (leftTime s) j +
    leg t (z+c) (u+c) (pinned β.2) (reverseTime (rightTime s)) j)-(u j+c j)=_
  rw [leg_translate,leg_translate]
  change ((leg t y u (pinned β.1) (leftTime s) j+c j)+
    (leg t z u (pinned β.2) (reverseTime (rightTime s)) j+c j))-(u j+c j)=_
  change _=((leg t y u (pinned β.1) (leftTime s) j+
    leg t z u (pinned β.2) (reverseTime (rightTime s)) j)-u j)+c j
  ring

lemma trialKernel_shift (t : ℝ) (y z u c : Point) :
    (trialKernel t y z u).map (shiftPath c)=trialKernel t (y+c) (z+c) (u+c) := by
  have hm : Measurable (trialPath t y z u) :=
    ((trialPath_continuous t y z).comp (continuous_const.prodMk continuous_id)).measurable
  rw [trialKernel_apply,trialKernel_apply,Measure.map_map (shiftPath_continuous c).measurable hm]
  congr 1
  funext β
  exact (trialPath_shift t y z u c β).symm

lemma individualReference_shift (t : ℝ) (y z c : Point)
    (S T : Set C(Time,Point)) (hT : MeasurableSet T)
    (hST : ∀f,shiftPath c f∈T ↔ f∈S) :
    (individualReference t y z S).map (shiftPath c)=
      individualReference t (y+c) (z+c) T := by
  have he : S=(shiftPath c)⁻¹' T := by ext f;exact (hST f).symm
  change (conditionedMeasure (law.map (leg (2*t) y z)) S).map (shiftPath c)=_
  rw [he,conditioned_map_preimage _ _ (shiftPath_continuous c).measurable hT,
    Measure.map_map (shiftPath_continuous c).measurable (leg_continuous ..).measurable]
  congr 1
  congr 1
  funext β
  exact (leg_translate (2*t) y z c β).symm

end HardSphere.Bridge

end
end

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Bridges_PhysicalPair
attribute [-instance] _root_.OAI.HardSphere.Bridge.exposedPeriodSingle_finite _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Bridge.targetUniform_finite _root_.OAI.HardSphere.Comparison.parameterTargetKernel_finite _root_.OAI.HardSphere.Groups.cellPathReference_probability _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Rescaling.config_haar _root_.OAI.HardSphere.bridgeEndpointBase_finite _root_.OAI.HardSphere.endpointWeightedBase_sfinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology
namespace HardSphere.Bridge
open Wiener GaussianPacking PathCutoff Comparison

lemma individualReference_unshift (t : ℝ) (y z c : Point)
    (S T : Set C(Time,Point)) (hT : MeasurableSet T)
    (hST : ∀f, shiftPath c f ∈ T ↔ f ∈ S) :
    (individualReference t (y+c) (z+c) T).map (shiftPath (-c)) =
      individualReference t y z S := by
  rw [←individualReference_shift t y z c S T hT hST,
    Measure.map_map (shiftPath_continuous (-c)).measurable (shiftPath_continuous c).measurable]
  have he : shiftPath (-c) ∘ shiftPath c = id := by
    funext f
    exact shiftPath_cancel c f
  rw [he, Measure.map_id]

variable {E : Type*} [MeasurableSpace E]

lemma exposedPeriodPair_apply (Q : Kernel E Point) [IsFiniteKernel Q] (t : ℝ)
    (y z y' z' : E → Point) (hy : Measurable y) (hz : Measurable z)
    (hy' : Measurable y') (hz' : Measurable z') (c : Point)
    (S U : Set (E × C(Time,Point))) (hS : MeasurableSet S) (hU : MeasurableSet U)
    (A : E → Set Point) (hQ : ∀e, Q e=targetUniform (A e)) (e : E) :
    exposedPeriodPair Q t y z y' z' hy hz hy' hz' c S U hS hU e =
      (pairedTrialLaw t (y e) (z e) (y' e+c) (z' e+c) (A e)
        (Prod.mk e ⁻¹' S) (Prod.mk e ⁻¹' U)
        (hS.preimage measurable_prodMk_left) (hU.preimage measurable_prodMk_left)).map
          (fun p ↦ (p.1, shiftPath (-c) p.2.2)) := by
  have hm : Measurable (fun p : C(Time,Point) × (Point × C(Time,Point)) ↦
      (p.1, shiftPath (-c) p.2.2)) :=
    measurable_fst.prodMk ((shiftPath_continuous (-c)).measurable.comp
      (measurable_snd.comp measurable_snd))
  rw [exposedPeriodPair, Kernel.map_apply _ hm,
    exposedPairedTrialKernel_physical Q t y z (fun e ↦ y' e+c) (fun e ↦ z' e+c)
      hy hz (hy'.add measurable_const) (hz'.add measurable_const) S U hS hU A hQ]

lemma exposedPeriodPair_physical {L : Length} (Q : Kernel E Point) [IsFiniteKernel Q]
    {t C : ℝ} (ht : 0<t) (hC : 0≤C)
    (y z y' z' : E → Point) (hy : Measurable y) (hz : Measurable z)
    (hy' : Measurable y') (hz' : Measurable z') (c : Point) (hc : projectPoint L c=0)
    (S T U : Set (E × C(Time,Point))) (hS : MeasurableSet S)
    (hT : MeasurableSet T) (hU : MeasurableSet U)
    (hTU : ∀e f, (e,shiftPath c f)∈U ↔ (e,f)∈T)
    (A : E → Set Point) (hQ : ∀e, Q e=targetUniform (A e))
    (hA : ∀e, MeasurableSet (A e)) (hAf : ∀e, volume (A e)≠⊤)
    {a b : ℝ≥0∞} (ha : 0<a) (hb : 0<b) (hvol : ∀e, a≤volume (A e))
    (hbound : ∀e u, u∈A e → ‖u-(fun j ↦ (y e j+z e j)/2)‖≤C)
    (hbound' : ∀e u, u∈A e → ‖u-(fun j ↦ ((y' e+c) j+(z' e+c) j)/2)‖≤C)
    (hfirst : ∀e, ∀ᵐu ∂targetUniform (A e), b≤trialKernel t (y e) (z e) u (Prod.mk e ⁻¹' S))
    (hsecond : ∀e, ∀ᵐu ∂targetUniform (A e), b≤trialKernel t (y' e+c) (z' e+c) u (Prod.mk e ⁻¹' U)) :
    let ρ := exposedPeriodPair Q t y z y' z' hy hz hy' hz' c S U hS hU
    let P := parameterIndividualReference t y z hy hz S hS
    let P' := parameterIndividualReference t y' z' hy' hz' T hT
    let G := b⁻¹*(a⁻¹*(midpointLower t C)⁻¹)
    IsMarkovKernel ρ ∧ IsMarkovKernel P ∧ IsMarkovKernel P' ∧
      (∀e, (ρ e).fst≤G • P e ∧ (ρ e).snd≤G • P' e) ∧
      (∀e, ∀ᵐp ∂ρ e,
        projectPoint L (p.1 midpointTime)=projectPoint L (p.2 midpointTime)) := by
  dsimp only
  let ρ := exposedPeriodPair Q t y z y' z' hy hz hy' hz' c S U hS hU
  let μ := parameterIndividualReference t y z hy hz S hS
  let ν := parameterIndividualReference t y' z' hy' hz' T hT
  let G := b⁻¹*(a⁻¹*(midpointLower t C)⁻¹)
  have hA0 (e : E) : volume (A e)≠0 := (ha.trans_le (hvol e)).ne'
  have hμ (e : E) : IsProbabilityMeasure (μ e) := by
    rw [show μ e=individualReference t (y e) (z e) (Prod.mk e ⁻¹' S) from
      parameterIndividualReference_apply ..]
    exact individualReference_probability ht hC (y e) (z e) (hA e) (hA0 e) (hAf e)
      (hbound e) _ (hS.preimage measurable_prodMk_left) hb (hfirst e)
  have hν (e : E) : IsProbabilityMeasure (ν e) := by
    rw [show ν e=individualReference t (y' e) (z' e) (Prod.mk e ⁻¹' T) from
      parameterIndividualReference_apply ..,
      ←individualReference_unshift t (y' e) (z' e) c (Prod.mk e ⁻¹' T) (Prod.mk e ⁻¹' U)
        (hU.preimage measurable_prodMk_left) (hTU e)]
    let _ := individualReference_probability ht hC (y' e+c) (z' e+c) (hA e)
      (hA0 e) (hAf e) (hbound' e) _ (hU.preimage measurable_prodMk_left) hb (hsecond e)
    first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
  have hm : Measurable (fun p : C(Time,Point) × (Point × C(Time,Point)) ↦
      (p.1, shiftPath (-c) p.2.2)) :=
    measurable_fst.prodMk ((shiftPath_continuous (-c)).measurable.comp
      (measurable_snd.comp measurable_snd))
  have hp (e : E) : IsProbabilityMeasure (pairedTrialLaw t (y e) (z e) (y' e+c) (z' e+c)
      (A e) (Prod.mk e ⁻¹' S) (Prod.mk e ⁻¹' U)
      (hS.preimage measurable_prodMk_left) (hU.preimage measurable_prodMk_left)) :=
    pairedTrialLaw_probability t (y e) (z e) (y' e+c) (z' e+c) (A e)
      (hA0 e) (hAf e) _ _ (hS.preimage measurable_prodMk_left)
      (hU.preimage measurable_prodMk_left)
      ((hfirst e).mono (fun _ hu ↦ hb.trans_le hu))
      ((hsecond e).mono (fun _ hu ↦ hb.trans_le hu))
  have hρ (e : E) : IsProbabilityMeasure (ρ e) := by
    rw [show ρ e = _ from exposedPeriodPair_apply Q t y z y' z' hy hz hy' hz' c S U hS hU A hQ e]
    let _ := hp e
    first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
  refine ⟨⟨hρ⟩,⟨hμ⟩,⟨hν⟩,?_,?_⟩
  · intro e
    obtain ⟨h₁,h₂⟩ := pairedTrialLaw_marginals ht hC hC (y e) (z e) (y' e+c) (z' e+c)
      (hA e) (hA0 e) (hAf e) (hbound e) (hbound' e) _ _
      (hS.preimage measurable_prodMk_left) (hU.preimage measurable_prodMk_left)
      hb hb (hfirst e) (hsecond e)
    have hf : (ρ e).fst = (pairedTrialLaw t (y e) (z e) (y' e+c) (z' e+c)
      (A e) (Prod.mk e ⁻¹' S) (Prod.mk e ⁻¹' U)
      (hS.preimage measurable_prodMk_left) (hU.preimage measurable_prodMk_left)).fst := by
      rw [show ρ e = _ from exposedPeriodPair_apply Q t y z y' z' hy hz hy' hz' c S U hS hU A hQ e,
        Measure.fst, Measure.map_map measurable_fst hm]
      rfl
    have hs : (ρ e).snd = ((pairedTrialLaw t (y e) (z e) (y' e+c) (z' e+c)
      (A e) (Prod.mk e ⁻¹' S) (Prod.mk e ⁻¹' U)
      (hS.preimage measurable_prodMk_left) (hU.preimage measurable_prodMk_left)).map
        (fun p ↦ p.2.2)).map (shiftPath (-c)) := by
      rw [show ρ e = _ from exposedPeriodPair_apply Q t y z y' z' hy hz hy' hz' c S U hS hU A hQ e,
        Measure.snd, Measure.map_map measurable_snd hm,
        Measure.map_map (shiftPath_continuous (-c)).measurable (by fun_prop)]
      rfl
    constructor
    · rw [hf, parameterIndividualReference_apply]
      apply h₁.trans
      intro B
      simp only [Measure.smul_apply, smul_eq_mul]
      gcongr
      exact hvol e
    · rw [hs, parameterIndividualReference_apply]
      have H := Measure.map_mono h₂ (shiftPath_continuous (-c)).measurable
      rw [Measure.map_smul,
        individualReference_unshift t (y' e) (z' e) c
        (Prod.mk e ⁻¹' T) (Prod.mk e ⁻¹' U) (hU.preimage measurable_prodMk_left) (hTU e)] at H
      apply H.trans
      intro B
      simp only [Measure.smul_apply, smul_eq_mul]
      gcongr
      exact hvol e
  · intro e
    rw [show ρ e = _ from exposedPeriodPair_apply Q t y z y' z' hy hz hy' hz' c S U hS hU A hQ e]
    apply (ae_map_iff hm.aemeasurable (by measurability)).mpr
    filter_upwards [pairedTrialLaw_midpoint t (y e) (z e) (y' e+c) (z' e+c) (A e)
      (hA0 e) (hAf e) (Prod.mk e ⁻¹' S) (Prod.mk e ⁻¹' U)
      (hS.preimage measurable_prodMk_left) (hU.preimage measurable_prodMk_left)] with p hmid
    have hc' : projectPoint L (-c)=0 := by
      ext j
      change (((-c j):ℝ):AddCircle L.val)=0
      rw [AddCircle.coe_neg]
      have h := congrFun hc j
      change ((c j:ℝ):AddCircle L.val)=0 at h
      rw [h,neg_zero]
    change projectPoint L (p.1 midpointTime)=projectPoint L (p.2.2 midpointTime+(-c))
    rw [projectPoint_shift (-c) hc',hmid.1,hmid.2]

end HardSphere.Bridge
end
end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Conditioning_ReferenceResample
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
open scoped ENNReal
namespace HardSphere.Comparison
variable {I C R : Type*} [Fintype I] [DecidableEq I] [Fintype C] [Fintype R]
  {X Z : I→Type*} [∀i,MeasurableSpace (X i)] [∀i,MeasurableSpace (Z i)]

omit [Fintype I] in
lemma measurable_proposalEvent (checks : C→LocalCheck (fun i ↦ X i×Z i))
    (s o : Finset I) (z : ∀i,Z i) : MeasurableSet (proposalEvent checks s o z) := by
  apply (measurableSet_retainedEvent checks (s∪o)).preimage
  apply Measurable.of_eval
  intro i
  by_cases hi : i∈s
  · simpa only [Function.updateFinset,dite_eq_left hi,Function.comp_def] using
      (measurable_pi_apply (⟨i,hi⟩:s)).comp (measurable_snd : Measurable (Prod.snd : (∀i,X i)×(∀i:s,X i×Z i)→_))
  · simpa only [Function.updateFinset,dite_eq_right hi,Function.comp_def] using
      (((measurable_pi_apply i).comp (measurable_fst : Measurable (Prod.fst : (∀i,X i)×(∀i:s,X i×Z i)→_))).prodMk measurable_const)

end HardSphere.Comparison

end
end

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Allocation_CoarsePhysical
attribute [-instance] _root_.OAI.HardSphere.Bridge.exposedPeriodSingle_finite _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Bridge.targetUniform_finite _root_.OAI.HardSphere.Comparison.parameterTargetKernel_finite _root_.OAI.HardSphere.Groups.cellPathReference_probability _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Rescaling.config_haar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology
namespace HardSphere.Groups
open Wiener Bridge Sampling Comparison GaussianPacking PathCutoff CellOrbital
attribute [local instance] Classical.propDecidable

lemma datumIndividualReference_apply {N K M G : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (m : ℕ) (r R C S t : ℝ) (u : Time) (i : Fin N)
    (d : PhysicalDatum N K M G L) :
    datumIndividualReference hL g m r R C S t u i d=
      individualReference t (datumStart hL d i) (datumEnd hL d i)
        (Prod.mk d ⁻¹' datumPermitted hL g m r R C S u i) :=
  parameterIndividualReference_apply ..

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
-- module Solutions.OAIQ054_HS.HardSphere_Comparison_ParameterTarget
attribute [-instance] _root_.OAI.HardSphere.Bridge.exposedBridgeKernel_markov _root_.OAI.HardSphere.Bridge.exposedPeriodSingle_finite _root_.OAI.HardSphere.Bridge.exposedTrialKernel_markov _root_.OAI.HardSphere.Bridge.parameterBridgeKernel_markov _root_.OAI.HardSphere.Bridge.parameterIndividualReference_finite _root_.OAI.HardSphere.Bridge.parameterTrialKernel_markov _root_.OAI.HardSphere.Bridge.targetUniform_finite _root_.OAI.HardSphere.Groups.cellPathReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.vertexPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace HardSphere.Comparison
open HardSphere.Bridge HardSphere.Wiener HardSphere.GaussianPacking
variable {E : Type*} [MeasurableSpace E]

lemma parameterTargetKernel_apply {B : Set Point} (hB : volume B ≠ ⊤)
    (A : Set (E×Point)) (hA : MeasurableSet A)
    (hAB : ∀e,Prod.mk e ⁻¹' A ⊆ B) (e : E) :
    parameterTargetKernel hB A hA e=targetUniform (Prod.mk e ⁻¹' A) := by
  let : IsFiniteMeasure (volume.restrict B) := ⟨by simpa using hB.lt_top⟩
  have hs := hA.preimage (@measurable_prodMk_left E Point _ _ e)
  change ((volume.restrict B) (Prod.mk e ⁻¹' A))⁻¹ •
    (volume.restrict B).restrict (Prod.mk e ⁻¹' A)=_
  rw [Measure.restrict_apply hs,inter_eq_left.mpr (hAB e),
    Measure.restrict_restrict hs,inter_eq_left.mpr (hAB e)]
  rfl

end HardSphere.Comparison

end
end

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology
namespace HardSphere.Comparison
variable {E U X Y : Type*} [MeasurableSpace E] [MeasurableSpace U]
  [MeasurableSpace X] [MeasurableSpace Y]

lemma probability_inter_98 (μ : Measure U) [IsProbabilityMeasure μ]
    {s t : Set U} (_hs : MeasurableSet s) (ht : MeasurableSet t)
    (hsm : ENNReal.ofReal (99/100:ℝ)≤μ s) (htm : ENNReal.ofReal (99/100:ℝ)≤μ t) :
    ENNReal.ofReal (49/50:ℝ)≤μ (s∩t) := by
  have he := congrArg ENNReal.toReal (measure_union_add_inter (μ:=μ) s ht)
  rw [ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _),
    ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)] at he
  have hu : (μ (s∪t)).toReal≤1 := by
    exact_mod_cast ENNReal.toReal_mono ENNReal.one_ne_top (prob_le_one : μ (s∪t)≤1)
  have hsr := ENNReal.toReal_mono (measure_ne_top _ _) hsm
  have htr := ENNReal.toReal_mono (measure_ne_top _ _) htm
  apply (ENNReal.toReal_le_toReal ENNReal.ofReal_ne_top (measure_ne_top _ _)).mp
  norm_num at hsr htr ⊢
  linarith

end HardSphere.Comparison

end
end

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Allocation_PhysicalVertex
attribute [-instance] _root_.OAI.HardSphere.Bridge.exposedPeriodSingle_finite _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Bridge.targetUniform_finite _root_.OAI.HardSphere.Groups.cellPathReference_probability _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Rescaling.config_haar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology
namespace HardSphere.Bridge
open Wiener GaussianPacking Comparison

lemma exposedPeriodPair_at {E : Type*} [MeasurableSpace E] {L : Length}
    (Q : Kernel E Point) [IsFiniteKernel Q] {t C : ℝ} (ht : 0<t) (hC : 0≤C)
    (y z y' z' : E→Point) (hy : Measurable y) (hz : Measurable z)
    (hy' : Measurable y') (hz' : Measurable z') (c : Point) (hc : projectPoint L c=0)
    (S T U : Set (E×C(Time,Point))) (hS : MeasurableSet S)
    (hT : MeasurableSet T) (hU : MeasurableSet U)
    (hTU : ∀e f,(e,shiftPath c f)∈U ↔ (e,f)∈T)
    (A : E→Set Point) (hQ : ∀e,Q e=targetUniform (A e)) (e : E)
    (hA : MeasurableSet (A e)) (hAf : volume (A e)≠⊤) {a b : ℝ≥0∞}
    (ha : 0<a) (hb : 0<b) (hvol : a≤volume (A e))
    (hbound : ∀u∈A e,‖u-(fun j ↦ (y e j+z e j)/2)‖≤C)
    (hbound' : ∀u∈A e,‖u-(fun j ↦ ((y' e+c) j+(z' e+c) j)/2)‖≤C)
    (hfirst : ∀ᵐu ∂targetUniform (A e),b≤trialKernel t (y e) (z e) u (Prod.mk e ⁻¹' S))
    (hsecond : ∀ᵐu ∂targetUniform (A e),b≤trialKernel t (y' e+c) (z' e+c) u (Prod.mk e ⁻¹' U)) :
    let ρ := exposedPeriodPair Q t y z y' z' hy hz hy' hz' c S U hS hU
    let P := parameterIndividualReference t y z hy hz S hS
    let P' := parameterIndividualReference t y' z' hy' hz' T hT
    let G := b⁻¹*(a⁻¹*(midpointLower t C)⁻¹)
    IsProbabilityMeasure (ρ e) ∧ IsProbabilityMeasure (P e) ∧ IsProbabilityMeasure (P' e) ∧
      (ρ e).fst≤G • P e ∧ (ρ e).snd≤G • P' e ∧
      (∀ᵐp ∂ρ e,projectPoint L (p.1 midpointTime)=projectPoint L (p.2 midpointTime)) := by
  dsimp only
  let Q₀ := Kernel.const Unit (Q e)
  let S₀ : Set (Unit×C(Time,Point)) := Prod.snd ⁻¹' (Prod.mk e ⁻¹' S)
  let T₀ : Set (Unit×C(Time,Point)) := Prod.snd ⁻¹' (Prod.mk e ⁻¹' T)
  let U₀ : Set (Unit×C(Time,Point)) := Prod.snd ⁻¹' (Prod.mk e ⁻¹' U)
  have hs : MeasurableSet S₀ := (hS.preimage measurable_prodMk_left).preimage measurable_snd
  have ht' : MeasurableSet T₀ := (hT.preimage measurable_prodMk_left).preimage measurable_snd
  have hu : MeasurableSet U₀ := (hU.preimage measurable_prodMk_left).preimage measurable_snd
  have htu : ∀q f,(q,shiftPath c f)∈U₀ ↔ (q,f)∈T₀ := fun _ f ↦ hTU e f
  have hq : ∀q : Unit,Q₀ q=targetUniform (A e) := fun _ ↦ hQ e
  obtain ⟨hp,hm,hn,hdom,hmid⟩ := exposedPeriodPair_physical Q₀ ht hC
    (fun _ ↦ y e) (fun _ ↦ z e) (fun _ ↦ y' e) (fun _ ↦ z' e)
    measurable_const measurable_const measurable_const measurable_const c hc
    S₀ T₀ U₀ hs ht' hu htu (fun _ ↦ A e) hq (fun _ ↦ hA) (fun _ ↦ hAf)
    ha hb (fun _ ↦ hvol) (fun _ ↦ hbound) (fun _ ↦ hbound')
    (fun _ ↦ hfirst) (fun _ ↦ hsecond)
  let ρ₀ := exposedPeriodPair Q₀ t (fun _ ↦ y e) (fun _ ↦ z e)
    (fun _ ↦ y' e) (fun _ ↦ z' e) measurable_const measurable_const
    measurable_const measurable_const c S₀ U₀ hs hu
  have he : ρ₀ ()=exposedPeriodPair Q t y z y' z' hy hz hy' hz' c S U hS hU e := by
    rw [exposedPeriodPair_apply Q t y z y' z' hy hz hy' hz' c S U hS hU A hQ e]
    exact exposedPeriodPair_apply Q₀ t _ _ _ _ _ _ _ _ c S₀ U₀ hs hu (fun _ ↦ A e) hq ()
  have hme : parameterIndividualReference t (fun _ : Unit ↦ y e) (fun _ ↦ z e)
      measurable_const measurable_const S₀ hs ()=parameterIndividualReference t y z hy hz S hS e := by
    rw [parameterIndividualReference_apply,parameterIndividualReference_apply]
    rfl
  have hne : parameterIndividualReference t (fun _ : Unit ↦ y' e) (fun _ ↦ z' e)
      measurable_const measurable_const T₀ ht' ()=parameterIndividualReference t y' z' hy' hz' T hT e := by
    rw [parameterIndividualReference_apply,parameterIndividualReference_apply]
    rfl
  have hf := hdom ()
  have hi := hmid ()
  change (ρ₀ ()).fst≤_ ∧ (ρ₀ ()).snd≤_ at hf
  change ∀ᵐp ∂ρ₀ (),_ at hi
  rw [he,hme,hne] at hf
  rw [he] at hi
  refine ⟨?_,?_,?_,hf.1,hf.2,hi⟩
  · rw [←he]; exact hp.isProbabilityMeasure ()
  · rw [←hme]; exact hm.isProbabilityMeasure ()
  · rw [←hne]; exact hn.isProbabilityMeasure ()

end HardSphere.Bridge

namespace HardSphere.Groups
open Wiener Bridge Sampling Comparison GaussianPacking PathCutoff CellOrbital
attribute [local instance] Classical.propDecidable

lemma datumAccessible_endpoints {N K M G : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (m : ℕ) (t r R C S : ℝ) (u : Time) (i : Fin N)
    (d : PhysicalDatum N K M G L) (hi : datumAccessible hL g m t r R C S u i d) :
    ‖datumStart hL d i-anchorPoint (datumHome hL d i)‖≤10 ∧
    ‖datumEnd hL d i-anchorPoint (datumHome hL d i)‖≤10 := by
  have ha : 0<volume (Prod.mk d ⁻¹' datumTarget hL g m t r R C S u i 0) :=
    lt_of_lt_of_le (by norm_num) (hi 0)
  obtain ⟨U,hU⟩ := nonempty_of_measure_ne_zero ha.ne'
  have hs : 0<trialKernel t (datumStart hL d i) (datumEnd hL d i) U
      (Prod.mk d ⁻¹' datumPermitted hL g m r R C S u i) :=
    lt_of_lt_of_le (by norm_num : (0:ℝ≥0∞)<ENNReal.ofReal (9/10:ℝ)) hU.2
  obtain ⟨f,hf⟩ := nonempty_of_measure_ne_zero hs.ne'
  exact ⟨by rw [←hf.2.2.1.1]; exact (hf.2.1 0).1,
    by rw [←hf.2.2.1.2]; exact (hf.2.1 1).1⟩

lemma midpoint_bound (v y z U : Point) (hy : ‖y-v‖≤10) (hz : ‖z-v‖≤10)
    (hU : ‖U-v‖≤3) : ‖U-(fun j ↦ (y j+z j)/2)‖≤13 := by
  apply (pi_norm_le_iff_of_nonneg (by norm_num : (0:ℝ)≤13)).mpr
  intro j
  have hyj := (pi_norm_le_iff_of_nonneg (by norm_num : (0:ℝ)≤10)).mp hy j
  have hzj := (pi_norm_le_iff_of_nonneg (by norm_num : (0:ℝ)≤10)).mp hz j
  have huj := (pi_norm_le_iff_of_nonneg (by norm_num : (0:ℝ)≤3)).mp hU j
  change |y j-v j|≤10 at hyj
  change |z j-v j|≤10 at hzj
  change |U j-v j|≤3 at huj
  change |U j-(y j+z j)/2|≤13
  rw [abs_le] at hyj hzj huj ⊢
  constructor <;> linarith

lemma unitTarget_sub (v c U : Point) : U-c∈unitTarget v ↔ U∈unitTarget (v+c) := by
  simp only [unitTarget,mem_pi,mem_univ,forall_const,mem_Ico,Pi.sub_apply,Pi.add_apply]
  constructor <;> intro h j <;> specialize h j <;> constructor <;> linarith [h.1,h.2]

lemma routeCellPeriod_chart {K : ℕ} (v w : Fin 3→Fin K) (j : Fin 7) :
    anchorPoint w+targetStep j+routeCellPeriod v w j=anchorPoint v := by
  unfold routeCellPeriod
  abel

lemma vertexTarget_subset {N K M G : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (m : ℕ) (t r R C S : ℝ) (u : Time) (i i' : Fin N)
    (v w : Fin 3→Fin K) (j : Fin 7) (d : PhysicalDatum N K M G L) :
    Prod.mk d ⁻¹' vertexTarget hL g m t r R C S u i i' v w j ⊆ unitTarget (anchorPoint v) :=
  fun _ h ↦ h.1.2

lemma vertexTarget_volume {N K M G : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (m : ℕ) (t r R C S : ℝ) (u : Time) (i i' : Fin N)
    (v w : Fin 3→Fin K) (j : Fin 7) (d : PhysicalDatum N K M G L)
    (hv : datumHome hL d i=v) (hw : datumHome hL d i'=w)
    (hi : datumAccessible hL g m t r R C S u i d)
    (hi' : datumAccessible hL g m t r R C S u i' d) :
    ENNReal.ofReal (49/50:ℝ)≤volume
      (Prod.mk d ⁻¹' vertexTarget hL g m t r R C S u i i' v w j) := by
  let B := unitTarget (anchorPoint v)
  let A := Prod.mk d ⁻¹' datumTarget hL g m t r R C S u i 0
  let T := (fun U : Point ↦ U-routeCellPeriod v w j) ⁻¹'
    (Prod.mk d ⁻¹' datumTarget hL g m t r R C S u i' j)
  have hA : MeasurableSet A := (datumTarget_measurable hL g m t r R C S u i 0).preimage measurable_prodMk_left
  have hT : MeasurableSet T := ((datumTarget_measurable hL g m t r R C S u i' j).preimage
    measurable_prodMk_left).preimage (measurable_id.sub measurable_const)
  have hAB : A⊆B := by
    intro U hU
    have h := hU.1
    simpa [hv,targetStep,B] using h
  have hTB : T⊆B := by
    intro U hU
    have h := hU.1
    rw [hw,unitTarget_sub,routeCellPeriod_chart] at h
    exact h
  have htvol : volume T=volume (Prod.mk d ⁻¹' datumTarget hL g m t r R C S u i' j) := by
    exact (measurePreserving_add_right volume (-routeCellPeriod v w j)).measure_preimage
      ((datumTarget_measurable hL g m t r R C S u i' j).preimage measurable_prodMk_left).nullMeasurableSet
  let : IsProbabilityMeasure (volume.restrict B) := ⟨by
    rw [Measure.restrict_apply_univ,unitTarget_volume]⟩
  have ha : ENNReal.ofReal (99/100:ℝ)≤(volume.restrict B) A := by
    rw [Measure.restrict_apply hA,inter_eq_left.mpr hAB]
    exact hi 0
  have ht : ENNReal.ofReal (99/100:ℝ)≤(volume.restrict B) T := by
    rw [Measure.restrict_apply hT,inter_eq_left.mpr hTB,htvol]
    exact hi' j
  have H := probability_inter_98 (volume.restrict B) hA hT ha ht
  rw [Measure.restrict_apply (hA.inter hT)] at H
  convert H using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  ext U
  simp only [vertexTarget,mem_preimage,mem_inter_iff,mem_prod,mem_univ,true_and,A,T,B]
  tauto

lemma shiftedDatumPermitted_equiv {N K M G : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (m : ℕ) (r R C S : ℝ) (u : Time) (i : Fin N) (c : Point)
    (d : PhysicalDatum N K M G L) (f : C(Time,Point)) :
    (d,Bridge.shiftPath c f)∈shiftedDatumPermitted hL g m r R C S u i c ↔
      (d,f)∈datumPermitted hL g m r R C S u i := by
  simp only [shiftedDatumPermitted,mem_preimage,Bridge.shiftPath_cancel]

lemma datumSuccess_shift {N K M G : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (m : ℕ) (t r R C S : ℝ) (u : Time) (i : Fin N) (c : Point)
    (d : PhysicalDatum N K M G L) (U : Point) :
    trialKernel t (datumStart hL d i+c) (datumEnd hL d i+c) U
      (Prod.mk d ⁻¹' shiftedDatumPermitted hL g m r R C S u i c)=
    datumSuccess hL g m t r R C S u i (d,U-c) := by
  have H := trialKernel_shift t (datumStart hL d i) (datumEnd hL d i) (U-c) c
  rw [sub_add_cancel] at H
  rw [←H,Measure.map_apply (Bridge.shiftPath_continuous c).measurable
    ((shiftedDatumPermitted_measurable hL g m r R C S u i c).preimage measurable_prodMk_left)]
  congr 1
  ext f
  exact shiftedDatumPermitted_equiv hL g m r R C S u i c d f

theorem vertexPair_physical {N K M G : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (m : ℕ) (t r R C S : ℝ) (ht : 0<t) (u : Time) (i i' : Fin N)
    (v w : Fin 3→Fin K) (j : Fin 7) (hc : projectPoint L (routeCellPeriod v w j)=0)
    (d : PhysicalDatum N K M G L) (hv : datumHome hL d i=v) (hw : datumHome hL d i'=w)
    (hi : datumAccessible hL g m t r R C S u i d)
    (hi' : datumAccessible hL g m t r R C S u i' d) :
    let ρ := vertexPair hL g m t r R C S u i i' v w j d
    let P := datumIndividualReference hL g m r R C S t u i d
    let P' := datumIndividualReference hL g m r R C S t u i' d
    IsProbabilityMeasure ρ ∧ IsProbabilityMeasure P ∧ IsProbabilityMeasure P' ∧
      ρ.fst≤vertexDensityBound t • P ∧ ρ.snd≤vertexDensityBound t • P' ∧
      (∀ᵐp ∂ρ,projectPoint L (p.1 midpointTime)=projectPoint L (p.2 midpointTime)) := by
  dsimp only
  let A := fun d : PhysicalDatum N K M G L ↦
    Prod.mk d ⁻¹' vertexTarget hL g m t r R C S u i i' v w j
  have hA : MeasurableSet (A d) :=
    (vertexTarget_measurable hL g m t r R C S u i i' v w j).preimage measurable_prodMk_left
  have hAf : volume (A d)≠⊤ := ne_top_of_le_ne_top
    (by rw [unitTarget_volume]; exact ENNReal.one_ne_top)
    (measure_mono (vertexTarget_subset hL g m t r R C S u i i' v w j d))
  have hmem : ∀ᵐU ∂targetUniform (A d),U∈A d :=
    Measure.ae_smul_measure (ae_restrict_mem hA) _
  have hei := datumAccessible_endpoints hL g m t r R C S u i d hi
  have hei' := datumAccessible_endpoints hL g m t r R C S u i' d hi'
  apply exposedPeriodPair_at _ ht (by norm_num : (0:ℝ)≤13)
    (fun d ↦ datumStart hL d i) (fun d ↦ datumEnd hL d i)
    (fun d ↦ datumStart hL d i') (fun d ↦ datumEnd hL d i')
    (datumStart_measurable hL i) (datumEnd_measurable hL i)
    (datumStart_measurable hL i') (datumEnd_measurable hL i')
    (routeCellPeriod v w j) hc (datumPermitted hL g m r R C S u i)
    (datumPermitted hL g m r R C S u i')
    (shiftedDatumPermitted hL g m r R C S u i' (routeCellPeriod v w j))
    (datumPermitted_measurable hL g m r R C S u i)
    (datumPermitted_measurable hL g m r R C S u i')
    (shiftedDatumPermitted_measurable hL g m r R C S u i' (routeCellPeriod v w j))
    (shiftedDatumPermitted_equiv hL g m r R C S u i' (routeCellPeriod v w j))
    A (parameterTargetKernel_apply _ _ _ (vertexTarget_subset hL g m t r R C S u i i' v w j)) d
    hA hAf (by norm_num : (0:ℝ≥0∞)<ENNReal.ofReal (49/50:ℝ))
    (by norm_num : (0:ℝ≥0∞)<ENNReal.ofReal (9/10:ℝ))
    (vertexTarget_volume hL g m t r R C S u i i' v w j d hv hw hi hi')
  · intro U hU
    exact midpoint_bound _ _ _ U hei.1 hei.2
      (targetCell_radius _ 0 U hU.2.1.1)
  · intro U hU
    have H := midpoint_bound _ _ _ (U-routeCellPeriod v w j) hei'.1 hei'.2
      (targetCell_radius _ j _ hU.2.2.1)
    convert H using 1
    all_goals try with_reducible_and_instances rfl
    congr 1
    ext k
    change U k-((datumStart hL d i' k+routeCellPeriod v w j k)+
      (datumEnd hL d i' k+routeCellPeriod v w j k))/2=
      (U k-routeCellPeriod v w j k)-(datumStart hL d i' k+datumEnd hL d i' k)/2
    ring
  · filter_upwards [hmem] with U hU
    exact hU.2.1.2
  · filter_upwards [hmem] with U hU
    rw [datumSuccess_shift]
    exact hU.2.2.2

end HardSphere.Groups
end
end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Allocation_PhysicalRouteGeometry
attribute [-instance] _root_.OAI.HardSphere.Bridge.exposedPeriodSingle_finite _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Bridge.targetUniform_finite _root_.OAI.HardSphere.Groups.cellPathReference_probability _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Rescaling.config_haar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
namespace HardSphere.Groups
open Wiener Bridge Sampling Comparison GaussianPacking PathCutoff CellOrbital HardSphere.Lattice

lemma self_routeCellPeriod {K : ℕ} {L : Length} (v : Fin 3→Fin K) :
    projectPoint L (routeCellPeriod v v 0)=0 := by
  simp only [routeCellPeriod,targetStep,Fin.val_zero,↓reduceIte,add_zero,sub_self]
  rfl

end HardSphere.Groups
end
end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Bridges_PhysicalEndpoint
attribute [-instance] _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Bridge.targetUniform_finite _root_.OAI.HardSphere.Groups.cellPathReference_probability _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Rescaling.config_haar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
namespace HardSphere.Bridge
open Wiener Comparison GaussianPacking
variable {E : Type*} [MeasurableSpace E]

lemma exposedPeriodSingle_apply (Q : Kernel E Point) [IsFiniteKernel Q] (t : ℝ)
    (y z : E→Point) (hy : Measurable y) (hz : Measurable z) (c : Point)
    (S : Set (E×C(Time,Point))) (hS : MeasurableSet S) (e : E) :
    exposedPeriodSingle Q t y z hy hz c S hS e =
      ((Q e).compProd (successKernel (trialKernel t (y e+c) (z e+c))
        (Prod.mk e ⁻¹' S) (hS.preimage measurable_prodMk_left))).map
        (fun p ↦ (shiftPath (-c) p.2,p.1)) := by
  rw [exposedPeriodSingle,Kernel.map_apply _ (by fun_prop)]
  congr 1
  ext B hB
  rw [Kernel.compProd_apply hB,Measure.compProd_apply hB]
  apply lintegral_congr
  intro U
  rw [parameterTrialSuccess_apply]
  exact hS

lemma successJoint_fst (μ : Measure Point) [SFinite μ] (t : ℝ) (y z : Point)
    (S : Set C(Time,Point)) (hS : MeasurableSet S)
    (hp : ∀ᵐU ∂μ,0<trialKernel t y z U S) :
    (μ.compProd (successKernel (trialKernel t y z) S hS)).fst=μ := by
  ext B hB
  rw [Measure.fst_apply hB,Measure.compProd_apply (hB.preimage measurable_fst)]
  calc
    _ = ∫⁻U,B.indicator (fun _ ↦ (1:ℝ≥0∞)) U ∂μ := by
      apply lintegral_congr_ae
      filter_upwards [hp] with U hU
      by_cases h : U∈B
      · simp only [Set.indicator_of_mem h]
        rw [show (fun x : C(Time,Point) ↦ (U,x)) ⁻¹' (Prod.fst ⁻¹' B)=univ by
          ext x; simp [h]]
        exact successKernel_mass _ S hS hU
      · rw [show (fun x : C(Time,Point) ↦ (U,x)) ⁻¹' (Prod.fst ⁻¹' B)=∅ by
          ext x; simp [h]]
        simp [h]
    _ = μ B := by rw [lintegral_indicator hB]; simp

lemma exposedPeriodSingle_physical {L : Length} (Q : Kernel E Point) [IsFiniteKernel Q]
    {t C : ℝ} (ht : 0<t) (hC : 0≤C)
    (y z : E→Point) (hy : Measurable y) (hz : Measurable z) (c : Point)
    (hc : projectPoint L c=0) (S T : Set (E×C(Time,Point)))
    (hS : MeasurableSet S) (hT : MeasurableSet T)
    (hst : ∀e f,(e,shiftPath c f)∈T ↔ (e,f)∈S)
    (e : E) (A B : Set Point) (hQ : Q e=targetUniform A)
    (hA : MeasurableSet A) (hAf : volume A≠⊤) (hAB : A⊆B) (hBvol : volume B=1)
    {a b : ℝ≥0∞} (ha : 0<a) (hb : 0<b) (hvol : a≤volume A)
    (hbound : ∀U∈A,‖U-(fun k ↦ ((y e+c) k+(z e+c) k)/2)‖≤C)
    (hs : ∀ᵐU ∂targetUniform A,b≤trialKernel t (y e+c) (z e+c) U (Prod.mk e ⁻¹' T)) :
    let ρ := exposedPeriodSingle Q t y z hy hz c T hT e
    let P := parameterIndividualReference t y z hy hz S hS e
    IsProbabilityMeasure ρ ∧ IsProbabilityMeasure P ∧
      ρ.fst≤(b⁻¹*(a⁻¹*(midpointLower t C)⁻¹)) • P ∧
      ρ.snd≤a⁻¹ • targetUniform B ∧
      (∀ᵐp ∂ρ,projectPoint L (p.1 midpointTime)=projectPoint L p.2) := by
  dsimp only
  have hA0 : volume A≠0 := (ha.trans_le hvol).ne'
  let := targetUniform_probability hA0 hAf
  let μ := (targetUniform A).compProd (successKernel (trialKernel t (y e+c) (z e+c))
    (Prod.mk e ⁻¹' T) (hT.preimage measurable_prodMk_left))
  have hp : ∀ᵐU ∂targetUniform A,0<trialKernel t (y e+c) (z e+c) U (Prod.mk e ⁻¹' T) :=
    hs.mono fun _ h ↦ hb.trans_le h
  have hf : μ.fst=targetUniform A := successJoint_fst _ _ _ _ _ _ hp
  have hm : IsProbabilityMeasure μ := ⟨by
    have H := congrArg (fun ν : Measure Point ↦ ν univ) hf
    simpa only [Measure.fst_apply MeasurableSet.univ,preimage_univ,measure_univ] using H⟩
  let := hm
  have hmap : Measurable (fun p : Point×C(Time,Point) ↦ (shiftPath (-c) p.2,p.1)) := by fun_prop
  have hr : exposedPeriodSingle Q t y z hy hz c T hT e=
      μ.map (fun p ↦ (shiftPath (-c) p.2,p.1)) := by
    rw [exposedPeriodSingle_apply,hQ]
  have href := individualReference_unshift t (y e) (z e) c (Prod.mk e ⁻¹' S)
    (Prod.mk e ⁻¹' T) (hT.preimage measurable_prodMk_left) (hst e)
  have hP : IsProbabilityMeasure (parameterIndividualReference t y z hy hz S hS e) := by
    rw [parameterIndividualReference_apply,←href]
    let := individualReference_probability ht hC (y e+c) (z e+c) hA hA0 hAf hbound
      (Prod.mk e ⁻¹' T) (hT.preimage measurable_prodMk_left) hb hs
    first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
  refine ⟨?_,hP,?_,?_,?_⟩
  · rw [hr]
    first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
  · have HD := physical_trial_le_reference ht hC (y e+c) (z e+c) hA hAf hbound
      (Prod.mk e ⁻¹' T) (hT.preimage measurable_prodMk_left) hs
    have HD' := Measure.map_mono HD (shiftPath_continuous (-c)).measurable
    rw [Measure.map_smul,href] at HD'
    rw [hr,Measure.fst,Measure.map_map measurable_fst hmap,parameterIndividualReference_apply]
    apply (show μ.map (fun p ↦ shiftPath (-c) p.2)≤
      (b⁻¹*((volume A)⁻¹*(midpointLower t C)⁻¹)) • individualReference t (y e) (z e)
        (Prod.mk e ⁻¹' S) by
      convert HD' using 1
      all_goals try with_reducible_and_instances rfl
      rw [Measure.map_map (shiftPath_continuous (-c)).measurable measurable_snd]
      rfl).trans
    intro D
    simp only [Measure.smul_apply,smul_eq_mul]
    exact mul_le_mul' (mul_le_mul' le_rfl
      (mul_le_mul' (ENNReal.inv_le_inv.mpr hvol) le_rfl)) le_rfl
  · rw [hr,Measure.snd,Measure.map_map measurable_snd hmap]
    change μ.fst≤_
    rw [hf]
    simp only [targetUniform,hBvol,inv_one,one_smul]
    intro D
    simp only [Measure.smul_apply,smul_eq_mul]
    exact mul_le_mul' (ENNReal.inv_le_inv.mpr hvol) (Measure.restrict_mono_set _ hAB D)
  · rw [hr]
    apply (ae_map_iff hmap.aemeasurable (by measurability)).mpr
    have HH : ∀ᵐp ∂μ,p.2 midpointTime=p.1 := by
      apply Measure.ae_compProd_of_ae_ae (measurableSet_eq_fun
        ((continuous_eval_const midpointTime).measurable.comp measurable_snd) measurable_fst)
      apply ae_of_all
      intro U
      exact (successKernel_absolutelyContinuous _ _ _ U).ae_le (trialKernel_midpoint t (y e+c) (z e+c) U)
    filter_upwards [HH] with p hp
    have hc' : projectPoint L (-c)=0 := by
      ext j
      change (((-c j):ℝ):AddCircle L.val)=0
      rw [AddCircle.coe_neg]
      have h := congrFun hc j
      change ((c j:ℝ):AddCircle L.val)=0 at h
      rw [h,neg_zero]
    change projectPoint L (p.2 midpointTime+(-c))=projectPoint L p.1
    rw [projectPoint_shift (-c) hc',hp]

end HardSphere.Bridge

namespace HardSphere.Groups
open Wiener Bridge Sampling Comparison GaussianPacking PathCutoff CellOrbital
attribute [local instance] Classical.propDecidable

lemma endpointTarget_subset {N K M G : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (m : ℕ) (t r R C S : ℝ) (u : Time) (i : Fin N)
    (v w : Fin 3→Fin K) (j : Fin 7) (d : PhysicalDatum N K M G L) :
    Prod.mk d ⁻¹' endpointTarget hL g m t r R C S u i v w j ⊆ unitTarget (anchorPoint v) :=
  fun _ h ↦ h.1.2

lemma endpointTarget_volume {N K M G : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (m : ℕ) (t r R C S : ℝ) (u : Time) (i : Fin N)
    (v w : Fin 3→Fin K) (j : Fin 7) (d : PhysicalDatum N K M G L)
    (hw : datumHome hL d i=w) (hi : datumAccessible hL g m t r R C S u i d) :
    ENNReal.ofReal (49/50:ℝ)≤volume (Prod.mk d ⁻¹' endpointTarget hL g m t r R C S u i v w j) := by
  have he : Prod.mk d ⁻¹' endpointTarget hL g m t r R C S u i v w j=
      (fun U ↦ U-routeCellPeriod v w j) ⁻¹' (Prod.mk d ⁻¹' datumTarget hL g m t r R C S u i j) := by
    ext U
    constructor
    · exact fun h ↦ h.2
    · intro h
      refine ⟨⟨mem_univ _,?_⟩,h⟩
      have H := h.1
      rw [hw,unitTarget_sub,routeCellPeriod_chart] at H
      exact H
  rw [he]
  have hvol : volume ((fun U ↦ U-routeCellPeriod v w j) ⁻¹'
      (Prod.mk d ⁻¹' datumTarget hL g m t r R C S u i j))=
      volume (Prod.mk d ⁻¹' datumTarget hL g m t r R C S u i j) :=
    (measurePreserving_add_right volume (-routeCellPeriod v w j)).measure_preimage
      ((datumTarget_measurable hL g m t r R C S u i j).preimage measurable_prodMk_left).nullMeasurableSet
  rw [hvol]
  exact (by norm_num : ENNReal.ofReal (49/50:ℝ)≤ENNReal.ofReal (99/100:ℝ)).trans (hi j)

theorem endpointPair_physical {N K M G : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (m : ℕ) (t r R C S : ℝ) (ht : 0<t) (u : Time) (i : Fin N)
    (v w : Fin 3→Fin K) (j : Fin 7) (hc : projectPoint L (routeCellPeriod v w j)=0)
    (d : PhysicalDatum N K M G L) (hw : datumHome hL d i=w)
    (hi : datumAccessible hL g m t r R C S u i d) :
    let ρ := endpointPair hL g m t r R C S u i v w j d
    let P := datumIndividualReference hL g m r R C S t u i d
    IsProbabilityMeasure ρ ∧ IsProbabilityMeasure P ∧
      ρ.fst≤vertexDensityBound t • P ∧
      ρ.snd≤(ENNReal.ofReal (49/50:ℝ))⁻¹ • targetUniform (unitTarget (anchorPoint v)) ∧
      (∀ᵐp ∂ρ,projectPoint L (p.1 midpointTime)=projectPoint L p.2) := by
  dsimp only
  let A := Prod.mk d ⁻¹' endpointTarget hL g m t r R C S u i v w j
  have hA : MeasurableSet A :=
    (endpointTarget_measurable hL g m t r R C S u i v w j).preimage measurable_prodMk_left
  have hAB := endpointTarget_subset hL g m t r R C S u i v w j d
  have hAf : volume A≠⊤ := ne_top_of_le_ne_top
    (by rw [unitTarget_volume]; exact ENNReal.one_ne_top) (measure_mono hAB)
  have hmem : ∀ᵐU ∂targetUniform A,U∈A := Measure.ae_smul_measure (ae_restrict_mem hA) _
  have hei := datumAccessible_endpoints hL g m t r R C S u i d hi
  apply exposedPeriodSingle_physical _ ht (by norm_num : (0:ℝ)≤13)
    (fun d ↦ datumStart hL d i) (fun d ↦ datumEnd hL d i)
    (datumStart_measurable hL i) (datumEnd_measurable hL i) (routeCellPeriod v w j) hc
    (datumPermitted hL g m r R C S u i)
    (shiftedDatumPermitted hL g m r R C S u i (routeCellPeriod v w j))
    (datumPermitted_measurable hL g m r R C S u i)
    (shiftedDatumPermitted_measurable hL g m r R C S u i (routeCellPeriod v w j))
    (shiftedDatumPermitted_equiv hL g m r R C S u i (routeCellPeriod v w j)) d
    A (unitTarget (anchorPoint v))
    (parameterTargetKernel_apply _ _ _ (endpointTarget_subset hL g m t r R C S u i v w j) d)
    hA hAf hAB (unitTarget_volume _) (by norm_num : (0:ℝ≥0∞)<ENNReal.ofReal (49/50:ℝ))
    (by norm_num : (0:ℝ≥0∞)<ENNReal.ofReal (9/10:ℝ))
    (endpointTarget_volume hL g m t r R C S u i v w j d hw hi)
  · intro U hU
    have H := midpoint_bound _ _ _ (U-routeCellPeriod v w j) hei.1 hei.2
      (targetCell_radius _ j _ hU.2.1)
    convert H using 1
    all_goals try with_reducible_and_instances rfl
    congr 1
    ext k
    change U k-((datumStart hL d i k+routeCellPeriod v w j k)+
      (datumEnd hL d i k+routeCellPeriod v w j k))/2=
      (U k-routeCellPeriod v w j k)-(datumStart hL d i k+datumEnd hL d i k)/2
    ring
  · filter_upwards [hmem] with U hU
    rw [datumSuccess_shift]
    exact hU.2.2

end HardSphere.Groups
end
end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Allocation_PhysicalRouteFactors
attribute [-instance] _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Bridge.targetUniform_finite _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Rescaling.config_haar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
namespace HardSphere.Groups
open Wiener Bridge Sampling Comparison GaussianPacking PathCutoff CellOrbital

lemma vertex_le_routeDensity (t : ℝ) : vertexDensityBound t ≤ routeDensityBound t := le_max_right _ _
lemma endpoint_le_routeDensity (t : ℝ) :
    (ENNReal.ofReal (49/50:ℝ))⁻¹ ≤ routeDensityBound t := by
  apply le_trans _ (le_max_left _ _)
  rw [←ENNReal.ofReal_inv_of_pos (by norm_num : (0:ℝ)<49/50)]
  norm_num

lemma encodeFirstEndpoint_measurable : Measurable encodeFirstEndpoint :=
  measurable_fst.prodMk (pointAsPath_measurable.comp measurable_snd)
lemma encodeLastEndpoint_measurable : Measurable encodeLastEndpoint :=
  (pointAsPath_measurable.comp measurable_snd).prodMk measurable_fst

lemma encoded_endpoint_physical {N K M G : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (m : ℕ) (t r R C S : ℝ) (ht : 0<t) (u : Time) (i : Fin N)
    (v w : Fin 3→Fin K) (j : Fin 7) (hc : projectPoint L (routeCellPeriod v w j)=0)
    (d : PhysicalDatum N K M G L) (hw : datumHome hL d i=w)
    (hi : datumAccessible hL g m t r R C S u i d) :
    let ρ := endpointPair hL g m t r R C S u i v w j d
    let P := datumIndividualReference hL g m r R C S t u i d
    let ρ₀ := ρ.map encodeFirstEndpoint
    let ρ₁ := ρ.map encodeLastEndpoint
    IsProbabilityMeasure ρ₀ ∧ IsProbabilityMeasure ρ₁ ∧ IsProbabilityMeasure P ∧
      ρ₀.fst ≤ routeDensityBound t • P ∧ ρ₀.snd ≤ routeDensityBound t • cellPathReference v ∧
      ρ₁.fst ≤ routeDensityBound t • cellPathReference v ∧ ρ₁.snd ≤ routeDensityBound t • P ∧
      (∀ᵐp ∂ρ₀,projectPoint L (p.1 midpointTime)=projectPoint L (p.2 midpointTime)) ∧
      (∀ᵐp ∂ρ₁,projectPoint L (p.1 midpointTime)=projectPoint L (p.2 midpointTime)) := by
  dsimp only
  obtain ⟨hρ,hP,hfst,hsnd,hmid⟩ := endpointPair_physical hL g m t r R C S ht u i v w j hc d hw hi
  let ρ := endpointPair hL g m t r R C S u i v w j d
  have : IsProbabilityMeasure ρ := hρ
  have F : (ρ.map encodeFirstEndpoint).fst=ρ.fst := by
    rw [Measure.fst,Measure.map_map measurable_fst encodeFirstEndpoint_measurable]
    rfl
  have HS : (ρ.map encodeFirstEndpoint).snd=ρ.snd.map pointAsPath := by
    rw [Measure.snd,Measure.map_map measurable_snd encodeFirstEndpoint_measurable,
      Measure.snd,Measure.map_map pointAsPath_measurable measurable_snd]
    rfl
  have F' : (ρ.map encodeLastEndpoint).fst=ρ.snd.map pointAsPath := by
    rw [Measure.fst,Measure.map_map measurable_fst encodeLastEndpoint_measurable,
      Measure.snd,Measure.map_map pointAsPath_measurable measurable_snd]
    rfl
  have HS' : (ρ.map encodeLastEndpoint).snd=ρ.fst := by
    rw [Measure.snd,Measure.map_map measurable_snd encodeLastEndpoint_measurable]
    rfl
  have HB : ρ.snd.map pointAsPath ≤ routeDensityBound t • cellPathReference v := by
    have H := Measure.map_mono hsnd pointAsPath_measurable
    rw [Measure.map_smul] at H
    exact H.trans (by dsimp only [cellPathReference]; gcongr; exact endpoint_le_routeDensity t)
  have HP : ρ.fst ≤ routeDensityBound t • datumIndividualReference hL g m r R C S t u i d :=
    hfst.trans (by gcongr; exact vertex_le_routeDensity t)
  refine ⟨(Measure.isProbabilityMeasure_map encodeFirstEndpoint_measurable.aemeasurable),(Measure.isProbabilityMeasure_map encodeLastEndpoint_measurable.aemeasurable),hP,?_,?_,?_,?_,?_,?_⟩
  · rw [F];exact HP
  · rw [HS];exact HB
  · rw [F'];exact HB
  · rw [HS'];exact HP
  · rw [ae_map_iff encodeFirstEndpoint_measurable.aemeasurable (by measurability)]
    exact hmid
  · rw [ae_map_iff encodeLastEndpoint_measurable.aemeasurable (by measurability)]
    filter_upwards [hmid] with p hp
    exact hp.symm

theorem physicalRouteFactor_physical {N K M G n : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (m : ℕ) (t r R C S : ℝ) (ht : 0<t) (u : Time)
    (labels : Fin (n+1)↪Fin N) (v : Fin (n+2)→(Fin 3→Fin K))
    (steps : Fin (n+1)→Fin 7)
    (hc : ∀k,projectPoint L (routeCellPeriod (v k.succ) (v k.castSucc) (steps k))=0)
    (d : PhysicalDatum N K M G L)
    (hhome : ∀k,datumHome hL d (labels k)=v k.castSucc)
    (haccess : ∀k,datumAccessible hL g m t r R C S u (labels k) d)
    (k : Fin (n+2)) :
    let ρ := physicalRouteFactor hL g m t r R C S u labels v steps k d
    let P := routeFirstReference hL g m t r R C S u labels v k d
    let Q := routeSecondReference hL g m t r R C S u labels v k d
    IsProbabilityMeasure ρ ∧ IsProbabilityMeasure P ∧ IsProbabilityMeasure Q ∧
      ρ.fst ≤ routeDensityBound t • P ∧ ρ.snd ≤ routeDensityBound t • Q ∧
      (∀ᵐp ∂ρ,projectPoint L (p.1 midpointTime)=projectPoint L (p.2 midpointTime)) := by
  dsimp only
  by_cases h0 : k.val=0
  · have hk : k=0 := Fin.ext h0
    subst k
    have H := encoded_endpoint_physical hL g m t r R C S ht u (labels 0) (v 0) (v 0) 0
      (self_routeCellPeriod (v 0)) d (hhome 0) (haccess 0)
    simp only [physicalRouteFactor,routeFirstReference,routeSecondReference,Fin.val_zero,
      Nat.zero_lt_succ,↓reduceDIte,Kernel.map_apply _ encodeFirstEndpoint_measurable]
    exact ⟨H.1,H.2.2.1,(by first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)),H.2.2.2.1,H.2.2.2.2.1,H.2.2.2.2.2.2.2.1⟩
  · by_cases hk : k.val<n+1
    · let i : Fin (n+1) := ⟨k.val,hk⟩
      let j : Fin (n+1) := ⟨k.val-1,by omega⟩
      have hi : i.castSucc=k := Fin.ext rfl
      have hj : j.succ=k := Fin.ext (by dsimp [j];omega)
      have he : projectPoint L (routeCellPeriod (v k) (v j.castSucc) (steps j))=0 := by
        simpa only [hj] using hc j
      obtain ⟨hρ,hP,hQ,hF,hS,hmid⟩ := vertexPair_physical hL g m t r R C S ht u
        (labels i) (labels j) (v k) (v j.castSucc) (steps j) he d
        (by simpa only [hi] using hhome i) (hhome j) (haccess i) (haccess j)
      simp only [physicalRouteFactor,routeFirstReference,routeSecondReference,dite_eq_right h0,dite_eq_left hk]
      exact ⟨hρ,hP,hQ,hF.trans (by gcongr;exact vertex_le_routeDensity t),
        hS.trans (by gcongr;exact vertex_le_routeDensity t),hmid⟩
    · have he : k=Fin.last (n+1) := Fin.ext (by simp only [Fin.val_last];omega)
      subst k
      have H := encoded_endpoint_physical hL g m t r R C S ht u (labels (Fin.last n))
        (v (Fin.last (n+1))) (v (Fin.last n).castSucc) (steps (Fin.last n))
        (hc (Fin.last n)) d (hhome (Fin.last n)) (haccess (Fin.last n))
      have hl : (⟨(n+1)-1,by omega⟩ : Fin (n+1))=Fin.last n := Fin.ext (by simp)
      simp only [physicalRouteFactor,routeFirstReference,routeSecondReference,
        Fin.val_last,Nat.add_one_ne_zero,Nat.lt_irrefl,↓reduceDIte,hl,Kernel.map_apply _ encodeLastEndpoint_measurable]
      exact ⟨H.2.1,(by first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)),H.2.2.1,H.2.2.2.2.2.1,H.2.2.2.2.2.2.1,H.2.2.2.2.2.2.2.2⟩

end HardSphere.Groups
end
end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Conditioning_RoutePartition
attribute [-instance] _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
namespace HardSphere.Comparison
variable {J : Type*}

lemma routePermutation_label {d : ℕ} (labels : Fin d↪J) (i : Fin d) :
    routePermutation labels (some (labels i))=routeEmbedding labels i.succ := by
  rw [←routeEmbedding_castSucc labels i]
  change (finRotate (d+1)).viaEmbedding (routeEmbedding labels) _=_
  rw [Equiv.Perm.viaEmbedding_apply]
  congr 1
  exact finRotate_of_lt i.isLt

lemma routePermutation_star (d : ℕ) (labels : Fin (d+1)↪J) :
    routePermutation labels none=some (labels 0) := by
  rw [←routeEmbedding_last labels]
  change (finRotate (d+1+1)).viaEmbedding (routeEmbedding labels) _=_
  rw [Equiv.Perm.viaEmbedding_apply,finRotate_last]
  exact routeEmbedding_castSucc labels 0

lemma routeSlots_exact {d : ℕ} [DecidableEq J] (labels : Fin d↪J) :
    routeSlots labels=insert none (Finset.univ.image (fun i ↦ some (labels i))) := by
  ext x
  simp only [routeSlots,Finset.mem_map,Finset.mem_univ,true_and,Finset.mem_insert,Finset.mem_image]
  constructor
  · rintro ⟨i,rfl⟩
    by_cases hi : i.val<d
    · exact Or.inr ⟨⟨i.val,hi⟩,by change _=(if h : i.val<d then _ else _);rw [dite_eq_left hi]⟩
    · exact Or.inl (by change (if h : i.val<d then _ else _)=_;rw [dite_eq_right hi])
  · rintro (rfl|⟨i,rfl⟩)
    · exact ⟨Fin.last d,routeEmbedding_last labels⟩
    · exact ⟨i.castSucc,routeEmbedding_castSucc labels i⟩

end HardSphere.Comparison

end
end

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Conditioning_PhysicalRoute
attribute [-instance] _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Bridge.targetUniform_finite _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Rescaling.config_haar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
namespace HardSphere.Comparison
variable {J : Type*}

lemma routeEmbedding_position {d : ℕ} (labels : Fin d↪J) (i : routeSlots labels) :
    routeEmbedding labels (routePosition labels i)=i.val :=
  (Finset.mem_map.mp i.property).choose_spec.2

lemma routePermutation_symm_first {n : ℕ} (labels : Fin (n+1)↪J) :
    (routePermutation labels).symm (routeEmbedding labels 0)=none := by
  apply (routePermutation labels).injective
  rw [Equiv.apply_symm_apply,routePermutation_star]
  exact routeEmbedding_castSucc labels 0

lemma routePermutation_symm_later {n : ℕ} (labels : Fin (n+1)↪J)
    (k : Fin (n+2)) (hk : k.val≠0) :
    (routePermutation labels).symm (routeEmbedding labels k)=
      some (labels ⟨k.val-1,by omega⟩) := by
  apply (routePermutation labels).injective
  rw [Equiv.apply_symm_apply,routePermutation_label]
  congr 1
  exact Fin.ext (by simp only [Fin.val_succ];omega)

end HardSphere.Comparison
namespace HardSphere.Groups
open Wiener Bridge Sampling Comparison GaussianPacking PathCutoff CellOrbital
variable {J : Type*}

lemma physicalSlot_first {N K M G n : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (m : ℕ) (t r R C S : ℝ) (u : Time)
    (particle : J↪Fin N) (labels : Fin (n+1)↪J) (v : Fin (n+2)→(Fin 3→Fin K))
    (k : Fin (n+2)) (d : PhysicalDatum N K M G L) :
    physicalSlotReference hL g m t r R C S u particle (v (Fin.last (n+1)))
      (routeEmbedding labels k) d=routeFirstReference hL g m t r R C S u (labels.trans particle) v k d := by
  by_cases hk : k.val<n+1
  · have he : routeEmbedding labels k=some (labels ⟨k.val,hk⟩) := routeEmbedding_castSucc labels ⟨k.val,hk⟩
    rw [he]
    simp only [routeFirstReference,dite_eq_left hk,physicalSlotReference,Function.Embedding.trans_apply]
  · have he : k=Fin.last (n+1) := Fin.ext (by simp only [Fin.val_last];omega)
    subst k
    rw [routeEmbedding_last]
    simp only [routeFirstReference,Fin.val_last,lt_self_iff_false,↓reduceDIte,physicalSlotReference,Kernel.const_apply]

lemma physicalSlot_second {N K M G n : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (m : ℕ) (t r R C S : ℝ) (u : Time)
    (particle : J↪Fin N) (labels : Fin (n+1)↪J) (v : Fin (n+2)→(Fin 3→Fin K))
    (k : Fin (n+2)) (d : PhysicalDatum N K M G L) :
    physicalSlotReference hL g m t r R C S u particle (v 0)
      ((routePermutation labels).symm (routeEmbedding labels k)) d=
      routeSecondReference hL g m t r R C S u (labels.trans particle) v k d := by
  by_cases hk : k.val=0
  · have he : k=0 := Fin.ext hk
    subst k
    rw [routePermutation_symm_first]
    simp only [routeSecondReference,Fin.val_zero,↓reduceDIte,physicalSlotReference,Kernel.const_apply]
  · rw [routePermutation_symm_later labels k hk]
    simp only [routeSecondReference,dite_eq_right hk,physicalSlotReference,Function.Embedding.trans_apply]

theorem physicalSelectedFactor_physical {N K M G n : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (m : ℕ) (t r R C S : ℝ) (ht : 0<t) (u : Time)
    (particle : J↪Fin N) (labels : Fin (n+1)↪J) (v : Fin (n+2)→(Fin 3→Fin K))
    (steps : Fin (n+1)→Fin 7)
    (hc : ∀k,projectPoint L (routeCellPeriod (v k.succ) (v k.castSucc) (steps k))=0)
    (d : PhysicalDatum N K M G L)
    (hhome : ∀k,datumHome hL d (particle (labels k))=v k.castSucc)
    (haccess : ∀k,datumAccessible hL g m t r R C S u (particle (labels k)) d)
    (i : routeSlots labels) :
    let ρ := physicalSelectedFactor hL g m t r R C S u particle labels v steps i d
    let P := physicalSlotReference hL g m t r R C S u particle (v (Fin.last (n+1))) i d
    let Q := physicalSlotReference hL g m t r R C S u particle (v 0) ((routePermutation labels).symm i) d
    IsProbabilityMeasure ρ ∧ IsProbabilityMeasure P ∧ IsProbabilityMeasure Q ∧
      ρ.fst ≤ routeDensityBound t • P ∧ ρ.snd ≤ routeDensityBound t • Q ∧
      (∀ᵐp ∂ρ,projectPoint L (p.1 midpointTime)=projectPoint L (p.2 midpointTime)) := by
  dsimp only [physicalSelectedFactor]
  rw [←routeEmbedding_position labels i,physicalSlot_first,physicalSlot_second]
  exact physicalRouteFactor_physical hL g m t r R C S ht u (labels.trans particle) v steps hc d hhome haccess _

end HardSphere.Groups
end
end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_DependentChecks
attribute [-instance] _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Comparison.instFintypeFrozenCheckIndex _root_.OAI.HardSphere.Comparison.proposalKernel_finite _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Rescaling.config_haar _root_.OAI.HardSphere.bridgeEndpointBase_finite _root_.OAI.HardSphere.endpointWeightedBase_sfinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators
namespace HardSphere.Comparison
variable {I E P : Type*} [Fintype I] [DecidableEq I] [Fintype E] [MeasurableSpace P]
  {V : I→Type*} [∀i,MeasurableSpace (V i)]
  (avoid : P→P→Prop) (hm : MeasurableSet {p : P×P | avoid p.1 p.2})
  (left right : E→I) (hdiff : ∀e,left e≠right e)
  (getL : (e:E)→V (left e)→P) (getR : (e:E)→V (right e)→P)
  (hL : ∀e,Measurable (getL e)) (hR : ∀e,Measurable (getR e))

include hdiff in
omit [Fintype I] in
lemma dependent_insertion (μ : ∀i,Measure (V i)) [∀i,IsProbabilityMeasure (μ i)]
    (p : I→E→ℝ≥0∞) (a : ℝ≥0∞) (U : Finset I)
    (hleft : ∀e,left e∈U→∀g : V (right e),μ (left e) {f | ¬avoid (getL e f) (getR e g)}≤p (left e) e)
    (hright : ∀e,right e∈U→∀f : V (left e),μ (right e) {g | ¬avoid (getL e f) (getR e g)}≤p (right e) e)
    (htotal : ∀i∈U,a+(∑e∈Finset.univ.filter
      (fun e ↦ i∈(dependentCheck avoid hm left right getL getR hL hR e).support),p i e)≤1) :
    UniformInsertionOn (dependentCheck avoid hm left right getL getR hL hR) μ a U := by
  apply uniformInsertionOn_of_check_failures _ μ p a U _ htotal
  intro i hi e he x
  have hie : i=left e ∨ i=right e := by simpa [dependentCheck] using he
  rcases hie with hh|hh
  · subst i
    simpa only [dependentCheck,Function.update_self,Function.update_of_ne (hdiff e).symm] using hleft e hi (x (right e))
  · subst i
    simpa only [dependentCheck,Function.update_self,Function.update_of_ne (hdiff e)] using hright e hi (x (left e))

end HardSphere.Comparison

end
end

section
noncomputable section
open MeasureTheory Set
open scoped ENNReal BigOperators
namespace HardSphere.Comparison
attribute [local instance] Classical.propDecidable
variable {I E B : Type*} [Fintype I] [DecidableEq I] [Fintype E]
  [Fintype B] [DecidableEq B]

omit [Fintype I] in
lemma card_incident_edge_le (left right : E → I) (color : E → B)
    (hinj : Function.Injective (fun e ↦ (color e,(left e,right e))))
    (i : I) (T : Finset I)
    (hnear : ∀e,left e=i → right e∈T)
    (hnear' : ∀e,right e=i → left e∈T) :
    (Finset.univ.filter (fun e ↦ left e=i ∨ right e=i)).card ≤ Fintype.card B*(2*T.card) := by
  classical
  let Q := (({i}:Finset I) ×ˢ T)∪(T ×ˢ {i})
  have hs : (Finset.univ.filter (fun e ↦ left e=i ∨ right e=i)).image
      (fun e ↦ (color e,(left e,right e)))⊆(Finset.univ : Finset B) ×ˢ Q := by
    intro p hp
    obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp hp
    apply Finset.mem_product.mpr
    refine ⟨Finset.mem_univ _,?_⟩
    rcases (Finset.mem_filter.mp he).2 with hh|hh
    · exact Finset.mem_union_left _ (Finset.mem_product.mpr ⟨Finset.mem_singleton.mpr hh,hnear e hh⟩)
    · exact Finset.mem_union_right _ (Finset.mem_product.mpr ⟨hnear' e hh,Finset.mem_singleton.mpr hh⟩)
  have hq : Q.card ≤ 2*T.card := by
    apply (Finset.card_union_le _ _).trans
    simp only [Finset.card_product,Finset.card_singleton,one_mul,mul_one]
    omega
  have hcard := Finset.card_le_card hs
  rw [Finset.card_image_of_injective _ hinj,Finset.card_product,Finset.card_univ] at hcard
  exact hcard.trans (Nat.mul_le_mul_left _ hq)

end HardSphere.Comparison
namespace HardSphere.Groups
open Comparison HardSphere.CellOrbital
attribute [local instance] Classical.propDecidable

lemma physical_incident_degree {I E B : Type*} [Fintype I] [DecidableEq I] [Fintype E]
    [Fintype B] [DecidableEq B] {K : ℕ} [NeZero K] (L : Length) (hL : L.val=(K:ℝ))
    (anchor : I → Fin 3 → Fin K) (M : ℕ)
    (hm : ∀v,(Finset.univ.filter (fun i : I ↦ anchor i=v)).card ≤ M)
    (left right : E → I) (color : E → B)
    (hinj : Function.Injective (fun e ↦ (color e,(left e,right e))))
    (hnear : ∀e,torusDistance L (gridCenter L (anchor (left e))) (gridCenter L (anchor (right e))) ≤ 23)
    (i : I) :
    (Finset.univ.filter (fun e ↦ left e=i ∨ right e=i)).card ≤ Fintype.card B*(2*(49^3*M)) := by
  let T := Finset.univ.filter (fun j : I ↦ torusDistance L (gridCenter L (anchor j)) (gridCenter L (anchor i)) ≤ 23)
  have hcard := card_incident_edge_le left right color hinj i T (by
    intro e he
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,?_⟩
    simpa only [he,torusDistance_comm L (gridCenter L (anchor i))] using hnear e) (by
    intro e he
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,by simpa only [he] using hnear e⟩)
  exact hcard.trans (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (card_near_labels L hL anchor M hm _)))

end HardSphere.Groups

end
end

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Bridges_PhysicalFactorChecks
attribute [-instance] _root_.OAI.HardSphere.Bridge.exposedBridgeKernel_markov _root_.OAI.HardSphere.Bridge.exposedPeriodSingle_finite _root_.OAI.HardSphere.Bridge.exposedTrialKernel_markov _root_.OAI.HardSphere.Bridge.instIsProbabilityMeasurePointMidpointNoise _root_.OAI.HardSphere.Bridge.midpointLaw_probability _root_.OAI.HardSphere.Bridge.parameterBridgeKernel_markov _root_.OAI.HardSphere.Bridge.parameterIndividualReference_finite _root_.OAI.HardSphere.Bridge.parameterTrialKernel_markov _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Bridge.targetUniform_finite _root_.OAI.HardSphere.Comparison.instFintypeFrozenCheckIndex _root_.OAI.HardSphere.Comparison.parameterTargetKernel_finite _root_.OAI.HardSphere.Comparison.proposalKernel_finite _root_.OAI.HardSphere.Groups.cellPathReference_probability _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Rescaling.config_haar _root_.OAI.HardSphere.bridgeEndpointBase_finite _root_.OAI.HardSphere.endpointWeightedBase_sfinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open MeasureTheory Set ProbabilityTheory
open scoped ENNReal BigOperators Topology
namespace HardSphere.Bridge
open Wiener GaussianPacking Comparison CellOrbital Groups
attribute [local instance] Classical.propDecidable

lemma normalized_marginal_collision {X : Type*} [MeasurableSpace X]
    {L : Length} {S : Set C(Time,Point)} (μ : Measure X) (P : Measure S)
    (f : X → S) (hf : Measurable f) {G q : ℝ≥0∞} (hdom : μ.map f ≤ G • P)
    (r : ℝ) (g : C(Time,Point))
    (hq : P {u | TrialCollision (L:=L) r (projectCurve L g) u.val} ≤ q) :
    μ {x | TrialCollision (L:=L) r (projectCurve L g) (f x).val} ≤ G*q := by
  have hm : MeasurableSet {u : S | TrialCollision (L:=L) r (projectCurve L g) u.val} :=
    (trialCollision_closed r (projectCurve L g)).measurableSet.preimage measurable_subtype_coe
  have h := hdom {u | TrialCollision (L:=L) r (projectCurve L g) u.val}
  rw [Measure.map_apply hf hm,Measure.smul_apply,smul_eq_mul] at h
  exact h.trans (mul_le_mul' le_rfl hq)

variable {I J E : Type*} [Fintype I] [DecidableEq I] [Fintype J] [Fintype E]
  {L : Length} {V : I → Type*} [∀i,MeasurableSpace (V i)]
  (allowed : J → Set C(Time,Point))
  (owner : Bool → J → I) (howner : ∀b,Function.Injective (owner b))
  (color : E → Bool) (labelL labelR : E → J) (hdiff : ∀e,labelL e ≠ labelR e)
  (path : ∀b j,V (owner b j) → allowed j) (hpath : ∀b j,Measurable (path b j))

omit [Fintype I] [Fintype J] in
include howner hdiff in
lemma factorPath_insertion (r : ℝ) (μ : ∀i,Measure (V i)) [∀i,IsProbabilityMeasure (μ i)]
    (P : ∀j,Measure (allowed j)) (G q a : ℝ≥0∞) (D : ℕ) (U : Finset I)
    (hdom : ∀b j,owner b j∈U → (μ (owner b j)).map (path b j) ≤ G • P j)
    (hq : ∀j k,j≠k → ∀g : allowed k,P j {f | TrialCollision (L:=L) r (projectCurve L g.val) f.val} ≤ q)
    (hdegree : ∀i∈U,(Finset.univ.filter (fun e ↦ owner (color e) (labelL e)=i ∨ owner (color e) (labelR e)=i)).card ≤ D)
    (hsmall : a+(D:ℝ≥0∞)*(G*q) ≤ 1) :
    UniformInsertionOn (factorPathCheck (L:=L) allowed owner color labelL labelR path hpath r) μ a U := by
  apply dependent_insertion _ _ _ _ (fun e ↦ fun h ↦ hdiff e (howner (color e) h))
    _ _ _ _ μ (fun _ _ ↦ G*q) a U
  · intro e he g
    simpa only [not_not] using normalized_marginal_collision (μ _) (P _) _ (hpath _ _)
      (hdom _ _ he) r (path (color e) (labelR e) g).val (hq _ _ (hdiff e) _)
  · intro e he f
    have h := normalized_marginal_collision (μ _) (P _) _ (hpath _ _)
      (hdom _ _ he) r (path (color e) (labelL e) f).val (hq _ _ (hdiff e).symm _)
    have hh : {g | ¬¬TrialCollision (L:=L) r (projectCurve L (path (color e) (labelR e) g).val)
        (path (color e) (labelL e) f).val}=
      {g | TrialCollision (L:=L) r (projectCurve L (path (color e) (labelL e) f).val)
        (path (color e) (labelR e) g).val} := by
      ext g
      simp only [mem_ofPred_eq,not_not]
      exact physicalPairCheck_symmetric r _ _
    rw [hh]
    exact h
  · intro i hi
    have hd := hdegree i hi
    have he : (Finset.univ.filter (fun e ↦ i∈(factorPathCheck (L:=L) allowed owner color labelL labelR path hpath r e).support))=
        Finset.univ.filter (fun e ↦ owner (color e) (labelL e)=i ∨ owner (color e) (labelR e)=i) := by
      ext e
      simp only [Finset.mem_filter,Finset.mem_univ,true_and,factorPathCheck,dependentCheck,Finset.mem_insert,Finset.mem_singleton]
      exact or_congr eq_comm eq_comm
    change a+(∑_e∈Finset.univ.filter (fun e ↦ i∈(factorPathCheck (L:=L) allowed owner color labelL labelR path hpath r e).support),G*q) ≤ 1
    rw [he,Finset.sum_const, nsmul_eq_mul]
    exact (add_le_add le_rfl (mul_le_mul' (by exact_mod_cast hd) le_rfl)).trans hsmall

end HardSphere.Bridge

end
end

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_SparseChecks
attribute [-instance] _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Rescaling.config_haar _root_.OAI.HardSphere.bridgeEndpointBase_finite _root_.OAI.HardSphere.endpointWeightedBase_sfinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators
namespace HardSphere.Groups
open Wiener
attribute [local irreducible] torusDistance

lemma incident_centers_close {I : Type*} {L : Length} (anchor center : I→Torus L)
    (owner : I→I) (hcenter : ∀i,torusDistance L (anchor i) (center (owner i))≤1)
    (i j : I) (hij : torusDistance L (anchor i) (anchor j)≤21) :
    torusDistance L (center (owner i)) (center (owner j))≤23 := by
  have h₁ := torusDistance_triangle' L (center (owner i)) (anchor i) (center (owner j))
  have h₂ := torusDistance_triangle' L (anchor i) (anchor j) (center (owner j))
  rw [torusDistance_comm L (center (owner i)) (anchor i)] at h₁
  linarith [hcenter i,hcenter j]

end HardSphere.Groups

end
end

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Bridges_PhysicalSparse
attribute [-instance] _root_.OAI.HardSphere.Bridge.exposedBridgeKernel_markov _root_.OAI.HardSphere.Bridge.exposedPeriodSingle_finite _root_.OAI.HardSphere.Bridge.exposedTrialKernel_markov _root_.OAI.HardSphere.Bridge.instIsProbabilityMeasurePointMidpointNoise _root_.OAI.HardSphere.Bridge.midpointLaw_probability _root_.OAI.HardSphere.Bridge.parameterBridgeKernel_markov _root_.OAI.HardSphere.Bridge.parameterIndividualReference_finite _root_.OAI.HardSphere.Bridge.parameterTrialKernel_markov _root_.OAI.HardSphere.Bridge.targetUniform_finite _root_.OAI.HardSphere.Comparison.instFintypeFrozenCheckIndex _root_.OAI.HardSphere.Comparison.parameterTargetKernel_finite _root_.OAI.HardSphere.Comparison.proposalKernel_finite _root_.OAI.HardSphere.Groups.cellPathReference_probability _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Rescaling.config_haar _root_.OAI.HardSphere.bridgeEndpointBase_finite _root_.OAI.HardSphere.endpointWeightedBase_sfinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators
namespace HardSphere.Bridge
open Wiener GaussianPacking Comparison Groups CellOrbital
attribute [local instance] Classical.propDecidable
variable {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
  {L : Length} {V : I → Type*} [∀i,MeasurableSpace (V i)]

lemma physicalSparseChecks_degree {K : ℕ} [NeZero K] (hL : L.val=(K:ℝ))
    (anchor : J → Torus L) (center : I → Fin 3 → Fin K)
    (M : ℕ) (hm : ∀v,(Finset.univ.filter (fun i : I ↦ center i=v)).card≤M)
    (owner : Bool → J → I) (howner : ∀b,Function.Injective (owner b))
    (hcenter : ∀b j,torusDistance L (anchor j) (gridCenter L (center (owner b j)))≤1)
    (i : I) :
    (Finset.univ.filter (fun e : physicalEdges anchor ↦ owner e.1 e.2.val.1=i ∨ owner e.1 e.2.val.2=i)).card≤4*(49^3*M) := by
  have hinj : Function.Injective (fun e : physicalEdges anchor ↦
      (e.1,(owner e.1 e.2.val.1,owner e.1 e.2.val.2))) := by
    rintro ⟨b,⟨⟨j,k⟩,h⟩⟩ ⟨b',⟨⟨j',k'⟩,h'⟩⟩ he
    have hb : b=b' := congrArg Prod.fst he
    subst b'
    have hj : j=j' := howner b (congrArg (fun p ↦ p.2.1) he)
    have hk : k=k' := howner b (congrArg (fun p ↦ p.2.2) he)
    subst j';subst k';rfl
  have hn : ∀e : physicalEdges anchor,
      torusDistance L (gridCenter L (center (owner e.1 e.2.val.1)))
        (gridCenter L (center (owner e.1 e.2.val.2)))≤23 := by
    intro e
    exact incident_centers_close anchor (fun j ↦ gridCenter L (center (owner e.1 j))) id
      (hcenter e.1) e.2.val.1 e.2.val.2 e.2.property.2
  have hd := physical_incident_degree L hL center M hm
    (fun e : physicalEdges anchor ↦ owner e.1 e.2.val.1)
    (fun e : physicalEdges anchor ↦ owner e.1 e.2.val.2) Prod.fst hinj hn i
  simp only [Fintype.card_bool] at hd
  omega

lemma physicalSparseChecks_insertion {K : ℕ} [NeZero K] (hL : L.val=(K:ℝ))
    (r : ℝ) (anchor : J → Torus L) (center : I → Fin 3 → Fin K)
    (M : ℕ) (hm : ∀v,(Finset.univ.filter (fun i : I ↦ center i=v)).card≤M)
    (allowed : J → Set C(Time,Point))
    (owner : Bool → J → I) (howner : ∀b,Function.Injective (owner b))
    (hcenter : ∀b j,torusDistance L (anchor j) (gridCenter L (center (owner b j)))≤1)
    (path : ∀b j,V (owner b j) → allowed j) (hpath : ∀b j,Measurable (path b j))
    (μ : ∀i,Measure (V i)) [∀i,IsProbabilityMeasure (μ i)]
    (P : ∀j,Measure (allowed j)) (G q a : ℝ≥0∞) (U : Finset I)
    (hdom : ∀b j,owner b j∈U → (μ (owner b j)).map (path b j)≤G • P j)
    (hq : ∀j k,j≠k → ∀g : allowed k,P j {f | TrialCollision r (projectCurve L g.val) f.val}≤q)
    (hsmall : a+(4*(49^3*M):ℕ)*(G*q)≤1) :
    UniformInsertionOn (physicalSparseChecks r anchor allowed owner path hpath) μ a U := by
  have hd : ∀i∈U,(Finset.univ.filter (fun e : physicalEdges anchor ↦
      owner e.1 e.2.val.1=i ∨ owner e.1 e.2.val.2=i)).card≤4*(49^3*M) := by
    intro i _
    exact physicalSparseChecks_degree hL anchor center M hm owner howner hcenter i
  exact factorPath_insertion (L:=L) allowed owner howner
    (fun e : physicalEdges anchor ↦ e.1)
    (fun e : physicalEdges anchor ↦ e.2.val.1)
    (fun e : physicalEdges anchor ↦ e.2.val.2)
    (fun e : physicalEdges anchor ↦ e.2.property.1) path hpath r μ P G q a
    (4*(49^3*M)) U hdom hq hd hsmall

end HardSphere.Bridge

end
end

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace HardSphere.Bridge
open Wiener GaussianPacking Comparison
attribute [local instance] Classical.propDecidable
variable {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
  {L : Length} {X : I → Type*} [∀i,MeasurableSpace (X i)]

omit [Fintype I] [DecidableEq I] in
lemma fiberEquiv_pi {i j : I} (h : i=j) (x : ∀i,X i) : fiberEquiv h (x i)=x j := by
  subst j
  rfl

variable (σ : Equiv.Perm I) (S : Finset I) (hfix : ∀i,i∉S → σ i=i)
omit [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] in
lemma routeOwner_injective (label : J → I) (hlabel : Function.Injective label) (b : Bool) :
    Function.Injective (routeOwner σ label b) := by
  cases b
  · exact hlabel
  · exact σ.injective.comp hlabel

omit [Fintype I] [Fintype J] [DecidableEq J] in
lemma routeChecks_primary (r : ℝ) (anchor : J → Torus L) (allowed : J → Set C(Time,Point))
    (label : J → I) (get : ∀j,X (label j) → allowed j) (hg : ∀j,Measurable (get j))
    (u : Finset I) (p : ∀i,X i×X (σ.symm i))
    (hp : p∈retainedEvent (routeChecks σ S hfix r anchor allowed label get hg) u) :
    (fun i ↦ (p i).1)∈retainedEvent (primaryChecks r anchor allowed label get hg) u := by
  intro e he
  exact hp (false,e.2) he

omit [Fintype I] [Fintype J] [DecidableEq J] in
lemma routePath_unselected (allowed : J → Set C(Time,Point)) (label : J → I)
    (get : ∀j,X (label j) → allowed j) (j : J) (hj : label j∉S)
    (p : ∀i,X i×X (σ.symm i)) :
    routePath σ S hfix allowed label get true j (p (routeOwner σ label true j))=
      get j (p (label j)).1 := by
  simp only [routePath,dite_eq_right hj]
  exact congrArg (get j) (fiberEquiv_pi (hfix (label j) hj) (fun i ↦ (p i).1))

omit [Fintype I] [Fintype J] [DecidableEq J] in
lemma routeChecks_outside (r : ℝ) (anchor : J → Torus L) (allowed : J → Set C(Time,Point))
    (label : J → I) (get : ∀j,X (label j) → allowed j) (hg : ∀j,Measurable (get j))
    (o : Finset I) (hso : Disjoint S o) (p : ∀i,X i×X (σ.symm i))
    (hp : (fun i ↦ (p i).1)∈retainedEvent (primaryChecks r anchor allowed label get hg) o) :
    p∈retainedEvent (routeChecks σ S hfix r anchor allowed label get hg) o := by
  intro e he
  rcases e with ⟨b,⟨⟨j,k⟩,hjk,hnear⟩⟩
  cases b
  · exact hp (false,⟨(j,k),hjk,hnear⟩) he
  · have hj : label j∉S := by
      intro hs
      exact Finset.disjoint_left.mp hso ((move_mem_iff σ S hfix (label j)).mpr hs)
        (he (by simp [routeChecks,physicalSparseChecks,factorPathCheck,dependentCheck,routeOwner]))
    have hk : label k∉S := by
      intro hs
      exact Finset.disjoint_left.mp hso ((move_mem_iff σ S hfix (label k)).mpr hs)
        (he (by simp [routeChecks,physicalSparseChecks,factorPathCheck,dependentCheck,routeOwner]))
    have he' : (primaryChecks r anchor allowed label get hg (false,⟨(j,k),hjk,hnear⟩)).support⊆o := by
      simpa [routeChecks,primaryChecks,physicalSparseChecks,factorPathCheck,dependentCheck,routeOwner,
        hfix (label j) hj,hfix (label k) hk] using he
    have hh := hp (false,⟨(j,k),hjk,hnear⟩) he'
    change ¬TrialCollision r (projectCurve L (routePath σ S hfix allowed label get true k
      (p (routeOwner σ label true k))).val) (routePath σ S hfix allowed label get true j
      (p (routeOwner σ label true j))).val
    rw [routePath_unselected σ S hfix allowed label get j hj,
      routePath_unselected σ S hfix allowed label get k hk]
    exact hh

end HardSphere.Bridge

end
end

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Bridges_ReversePair
attribute [-instance] _root_.OAI.HardSphere.Bridge.exposedBridgeKernel_markov _root_.OAI.HardSphere.Bridge.exposedPeriodSingle_finite _root_.OAI.HardSphere.Bridge.exposedTrialKernel_markov _root_.OAI.HardSphere.Bridge.parameterBridgeKernel_markov _root_.OAI.HardSphere.Bridge.parameterIndividualReference_finite _root_.OAI.HardSphere.Bridge.parameterTrialKernel_markov _root_.OAI.HardSphere.Bridge.targetUniform_finite _root_.OAI.HardSphere.Comparison.parameterTargetKernel_finite _root_.OAI.HardSphere.Groups.cellPathReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace HardSphere.Bridge
open Comparison Wiener GaussianPacking
variable {I : Type*} [Fintype I] [DecidableEq I] {X : I→Type*}
  [∀i,MeasurableSpace (X i)]

omit [Fintype I] in
lemma partialReversePairs_selected (σ : Equiv.Perm I) (s : Finset I)
    (hf : ∀i,i∉s→σ i=i) (p : ∀i,X i×X (σ.symm i)) (j : I) (hj : j∈s) :
    partialReversePairs σ s hf p j=
      (fiberEquiv (σ.symm_apply_apply j) (p (σ j)).2,(p (σ j)).1) := by
  change partialReverseFactor σ s hf j (p (σ j))=_
  simp only [partialReverseFactor,dite_eq_left hj,reverseFactor]
  rfl
omit [Fintype I] in
lemma partialReversePairs_outside_fst (σ : Equiv.Perm I) (s : Finset I)
    (hf : ∀i,i∉s→σ i=i) (p : ∀i,X i×X (σ.symm i)) (j : I) (hj : j∉s) :
    (partialReversePairs σ s hf p j).1=(p j).1 := by
  change (partialReverseFactor σ s hf j (p (σ j))).1=_
  simp only [partialReverseFactor,dite_eq_right hj]
  change fiberEquiv (hf j hj) (p (σ j)).1=(p j).1
  exact fiberEquiv_pi (hf j hj) (fun i ↦ (p i).1)

variable {J : Type*} [Fintype J] [DecidableEq J]
omit [Fintype I] [Fintype J] [DecidableEq J] in
lemma partialReverse_primary_path (σ : Equiv.Perm I) (s : Finset I)
    (hf : ∀i,i∉s→σ i=i) (allowed : J→Set C(Time,Point))
    (label : J→I) (get : ∀j,X (label j)→allowed j)
    (p : ∀i,X i×X (σ.symm i)) (j : J) :
    get j (partialReversePairs σ s hf p (label j)).1=
      routePath σ s hf allowed label get true j (p (routeOwner σ label true j)) := by
  by_cases hj : label j∈s
  · rw [partialReversePairs_selected σ s hf p _ hj]
    simp only [routePath,dite_eq_left hj]
    rfl
  · rw [partialReversePairs_outside_fst σ s hf p _ hj,
      routePath_unselected σ s hf allowed label get j hj]

end HardSphere.Bridge

end
end

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Bridges_SelectedReverse
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
open scoped ENNReal
namespace HardSphere.Bridge
open Comparison Wiener GaussianPacking
variable {I : Type*} [Fintype I] [DecidableEq I] {X : I→Type*}
  [∀i,MeasurableSpace (X i)]

omit [Fintype I] in
lemma partialReverse_update (σ : Equiv.Perm I) (s : Finset I) (hf : ∀i,i∉s→σ i=i)
    (b : ∀i,X i×X (σ.symm i)) (p : ∀i:s,X i×X (σ.symm i)) :
    partialReversePairs σ s hf (Function.updateFinset b s p)=
      Function.updateFinset (partialReversePairs σ s hf b) s (reverseSelected σ s hf p) := by
  funext j
  by_cases hj : j∈s
  · rw [partialReversePairs_selected σ s hf _ j hj]
    have hj' : σ j∈s := (move_mem_iff σ s hf j).mpr hj
    simp only [Function.updateFinset,dite_eq_left hj,dite_eq_left hj']
    rfl
  · have hj' : σ j∉s := fun h ↦ hj ((move_mem_iff σ s hf j).mp h)
    simp only [Function.updateFinset,dite_eq_right hj]
    change partialReverseFactor σ s hf j (Function.updateFinset b s p (σ j))=_
    simp only [Function.updateFinset,dite_eq_right hj']
    rfl

end HardSphere.Bridge

end
end

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Conditioning_SharedRoute
attribute [-instance] _root_.OAI.HardSphere.Groups.labelOptionSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace HardSphere.Comparison
open HardSphere.Bridge
attribute [local instance] Classical.propDecidable

variable {E I : Type*} [MeasurableSpace E] [Fintype I] [DecidableEq I]
  {X : I→Type*} [∀i,MeasurableSpace (X i)]

omit [Fintype I] in
lemma ambientFirst_measurable (s : Finset I) (σ : Equiv.Perm I) :
    Measurable (ambientFirst (X:=X) s σ) :=
  measurable_updateFinset'.comp (measurable_fst.prodMk
    (Measurable.of_eval (fun i ↦ measurable_fst.comp ((measurable_pi_apply i).comp measurable_snd))))

omit [Fintype I] in
lemma ambientSecond_measurable (s : Finset I) (σ : Equiv.Perm I) (hf : ∀i,i∉s→σ i=i) :
    Measurable (ambientSecond (X:=X) s σ hf) :=
  measurable_updateFinset'.comp (measurable_fst.prodMk
    (Measurable.of_eval (fun i ↦ measurable_fst.comp ((measurable_pi_apply i).comp
      ((reverseSelected σ s hf).measurable.comp measurable_snd)))))

omit [Fintype I] in
lemma ambientRefreshEvent_measurable (s : Finset I) (σ : Equiv.Perm I)
    (hf : ∀i,i∉s→σ i=i) (A : Set (E×(∀i,X i))) (hA : MeasurableSet A) :
    MeasurableSet (ambientRefreshEvent s σ hf A) := by
  exact (hA.preimage (measurable_fst.fst.prodMk ((ambientFirst_measurable s σ).comp
    (measurable_fst.snd.prodMk measurable_snd)))).inter
    (hA.preimage (measurable_fst.fst.prodMk ((ambientSecond_measurable s σ hf).comp
      (measurable_fst.snd.prodMk measurable_snd))))

omit [Fintype I] in
lemma ambientSharedKernel_mass (s : Finset I) (σ : Equiv.Perm I) (hf : ∀i,i∉s→σ i=i)
    (ξ : Kernel E (∀i,X i)) [IsFiniteKernel ξ]
    (ρ : ∀i:s,Kernel E (X i×X (σ.symm i))) [∀i,IsFiniteKernel (ρ i)]
    (A : Set (E×(∀i,X i))) (hA : MeasurableSet A) (e : E)
    (hp : ∀ᵐx ∂ξ e,0<(Measure.pi fun i ↦ ρ i e)
      {p | (e,ambientFirst s σ (x,p))∈A ∧ (e,ambientSecond s σ hf (x,p))∈A}) :
    ambientSharedKernel s σ hf ξ ρ A e univ=ξ e univ := by
  rw [ambientSharedKernel,Kernel.compProd_apply MeasurableSet.univ]
  simp only [preimage_univ]
  calc
    _ = ∫⁻_x,1 ∂ξ e := by
      apply lintegral_congr_ae
      filter_upwards [hp] with x hx
      apply fiberNormalize_mass _ (ambientRefreshEvent_measurable s σ hf A hA)
      simpa only [Kernel.comap_apply,finiteKernelPi_apply,ambientRefreshEvent,mem_ofPred_eq] using hx
    _ = _ := by simp

end HardSphere.Comparison
end
end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Allocation_PhysicalPrimary
attribute [-instance] _root_.OAI.HardSphere.Bridge.targetUniform_finite _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Rescaling.config_haar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
namespace HardSphere.Groups
open Wiener Bridge Sampling Comparison GaussianPacking PathCutoff CellOrbital
variable {J : Type*} [Fintype J] [DecidableEq J]

omit [Fintype J] [DecidableEq J] in
lemma physicalSlotAllowed_measurable {N K M G : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (m : ℕ) (r R C S : ℝ) (u : Time)
    (particle : J→Fin N) (d : PhysicalDatum N K M G L) (i : Option J) :
    MeasurableSet (physicalSlotAllowed hL g m r R C S u particle d i) := by
  cases i with
  | none => exact MeasurableSet.univ
  | some i => exact (datumPermitted_measurable hL g m r R C S u (particle i)).preimage measurable_prodMk_left

omit [Fintype J] [DecidableEq J] in
lemma physicalSlotOn_map {N K M G : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (m : ℕ) (t r R C S : ℝ) (u : Time)
    (particle : J→Fin N) (v : Fin 3→Fin K) (d : PhysicalDatum N K M G L) (i : Option J) :
    (physicalSlotOn hL g m t r R C S u particle v d i).map Subtype.val=
      physicalSlotReference hL g m t r R C S u particle v i d := by
  cases i with
  | none =>
    change (subtypeConditional (cellPathReference v) (univ : Set C(Time,Point))).map
      Subtype.val=cellPathReference v
    rw [subtypeConditional_map _ MeasurableSet.univ,measure_univ,inv_one,
      one_smul,Measure.restrict_univ]
  | some i =>
    change (referenceOn t (datumStart hL d (particle i)) (datumEnd hL d (particle i))
      (Prod.mk d ⁻¹' datumPermitted hL g m r R C S u (particle i))).map Subtype.val=
      datumIndividualReference hL g m r R C S t u (particle i) d
    rw [referenceOn_map _ _ _ ((datumPermitted_measurable hL g m r R C S u (particle i)).preimage
      measurable_prodMk_left),datumIndividualReference_apply]

instance physicalSlotOn_finite {N K M G : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (m : ℕ) (t r R C S : ℝ) (u : Time)
    (particle : J→Fin N) (v : Fin 3→Fin K) (d : PhysicalDatum N K M G L) (i : Option J) :
    IsFiniteMeasure (physicalSlotOn hL g m t r R C S u particle v d i) := by
  have hm := physicalSlotOn_map hL g m t r R C S u particle v d i
  have : IsFiniteMeasure ((physicalSlotOn hL g m t r R C S u particle v d i).map Subtype.val) := by
    rw [hm]; infer_instance
  exact Measure.isFiniteMeasure_of_map measurable_subtype_coe.aemeasurable

omit [Fintype J] [DecidableEq J] in
lemma physicalSlotOn_probability {N K M G : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (m : ℕ) (t r R C S : ℝ) (u : Time)
    (particle : J→Fin N) (v : Fin 3→Fin K) (d : PhysicalDatum N K M G L) (i : Option J)
    [IsProbabilityMeasure (physicalSlotReference hL g m t r R C S u particle v i d)] :
    IsProbabilityMeasure (physicalSlotOn hL g m t r R C S u particle v d i) := by
  have : IsProbabilityMeasure ((physicalSlotOn hL g m t r R C S u particle v d i).map Subtype.val) := by
    rw [physicalSlotOn_map]; infer_instance
  exact Measure.isProbabilityMeasure_of_map (Subtype.val : _ → _)

end HardSphere.Groups
end
end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Allocation_PhysicalSupported
attribute [-instance] _root_.OAI.HardSphere.Bridge.targetUniform_finite _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Rescaling.config_haar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
namespace HardSphere.Groups
open Wiener Bridge Sampling Comparison GaussianPacking PathCutoff CellOrbital
variable {J : Type*} [Fintype J] [DecidableEq J]

instance physicalSlotAllowed_borel {N K M G : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (m : ℕ) (r R C S : ℝ) (u : Time)
    (particle : J→Fin N) (d : PhysicalDatum N K M G L) (i : Option J) :
    StandardBorelSpace (physicalSlotAllowed hL g m r R C S u particle d i) :=
  (physicalSlotAllowed_measurable hL g m r R C S u particle d i).standardBorel

lemma routeDensityBound_ne_top {t : ℝ} (ht : 0<t) : routeDensityBound t≠⊤ := by
  have ha : (ENNReal.ofReal (9/10:ℝ))≠0 := by positivity
  have hb : (ENNReal.ofReal (49/50:ℝ))≠0 := by positivity
  have hc := (midpointLower_pos ht 13).ne'
  simp only [routeDensityBound,ne_eq,max_eq_top]
  exact not_or.mpr ⟨by norm_num,ENNReal.mul_ne_top (ENNReal.inv_ne_top.mpr ha)
    (ENNReal.mul_ne_top (ENNReal.inv_ne_top.mpr hb) (ENNReal.inv_ne_top.mpr hc))⟩

lemma one_le_routeDensityBound (t : ℝ) : 1 ≤ routeDensityBound t :=
  le_trans (by norm_num) (le_max_left _ _)

omit [Fintype J] [DecidableEq J] in
theorem physicalSelectedOn_physical {N K M G n : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (m : ℕ) (t r R C S : ℝ) (ht : 0<t) (u : Time)
    (particle : J↪Fin N) (labels : Fin (n+1)↪J) (v : Fin (n+2)→(Fin 3→Fin K))
    (steps : Fin (n+1)→Fin 7)
    (hc : ∀k,projectPoint L (routeCellPeriod (v k.succ) (v k.castSucc) (steps k))=0)
    (d : PhysicalDatum N K M G L)
    (hhome : ∀k,datumHome hL d (particle (labels k))=v k.castSucc)
    (haccess : ∀k,datumAccessible hL g m t r R C S u (particle (labels k)) d)
    (i : routeSlots labels) :
    let ρ := physicalSelectedOn hL g m t r R C S u particle labels v steps d i
    let P := physicalSlotOn hL g m t r R C S u particle (v (Fin.last (n+1))) d i
    let Q := physicalSlotOn hL g m t r R C S u particle (v 0) d ((routePermutation labels).symm i)
    IsProbabilityMeasure ρ ∧ IsProbabilityMeasure P ∧ IsProbabilityMeasure Q ∧
      ρ.fst ≤ routeDensityBound t • P ∧ ρ.snd ≤ routeDensityBound t • Q ∧
      ρ.map (Prod.map Subtype.val Subtype.val)=
        physicalSelectedFactor hL g m t r R C S u particle labels v steps i d := by
  dsimp only
  obtain ⟨hp,hP,hQ,hfst,hsnd,-⟩ := physicalSelectedFactor_physical
    hL g m t r R C S ht u particle labels v steps hc d hhome haccess i
  let := hp
  let := hP
  let := hQ
  rw [←physicalSlotOn_map hL g m t r R C S u particle (v (Fin.last (n+1))) d i] at hfst
  rw [←physicalSlotOn_map hL g m t r R C S u particle (v 0) d ((routePermutation labels).symm i)] at hsnd
  have hS := physicalSlotAllowed_measurable hL g m r R C S u particle d i
  have hT := physicalSlotAllowed_measurable hL g m r R C S u particle d ((routePermutation labels).symm i)
  have hsupp := supported_of_marginals _ hS hT _ _ hfst hsnd
  exact ⟨supportedPair_probability _ hS hT hsupp,
    physicalSlotOn_probability hL g m t r R C S u particle _ d i,
    physicalSlotOn_probability hL g m t r R C S u particle _ d _,
    supportedPair_fst_le _ hS hT hsupp _ hfst,
    supportedPair_snd_le _ hS hT hsupp _ hsnd,
    supportedPair_map _ hS hT hsupp⟩

end HardSphere.Groups
end
end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_SharedIdentities
attribute [-instance] _root_.OAI.HardSphere.Bridge.exposedPeriodSingle_finite _root_.OAI.HardSphere.Bridge.targetUniform_finite _root_.OAI.HardSphere.Comparison.parameterTargetKernel_finite _root_.OAI.HardSphere.Groups.cellPathReference_probability _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotAllowed_borel _root_.OAI.HardSphere.Groups.physicalSlotOn_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Rescaling.config_haar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace HardSphere.Comparison
open HardSphere.Bridge HardSphere.Wiener HardSphere.GaussianPacking
attribute [local instance] Classical.propDecidable
variable {E I : Type*} [MeasurableSpace E] [Fintype I] [DecidableEq I]
  {X Y : I→Type*} [∀i,MeasurableSpace (X i)] [∀i,MeasurableSpace (Y i)]

variable {J : Type*} [Fintype J] [DecidableEq J] {L : HardSphere.Length}

omit [Fintype I] [∀i,MeasurableSpace (X i)] in
lemma ambientFirst_updated (s : Finset I) (σ : Equiv.Perm I)
    (x : ∀i,X i) (z : ∀i,X (σ.symm i)) (p : ∀i:s,X i×X (σ.symm i)) :
    (fun i ↦ (Function.updateFinset (fun i ↦ (x i,z i)) s p i).1)=
      ambientFirst s σ (x,p) := by
  funext i
  by_cases hi : i∈s
  · simp only [ambientFirst,Function.updateFinset,dite_eq_left hi]
  · simp only [ambientFirst,Function.updateFinset,dite_eq_right hi]

omit [Fintype I] in
lemma ambientSecond_updated (s : Finset I) (σ : Equiv.Perm I) (hσ : ∀i,i∉s→σ i=i)
    (x : ∀i,X i) (z : ∀i,X (σ.symm i)) (p : ∀i:s,X i×X (σ.symm i)) :
    (fun i ↦ (partialReversePairs σ s hσ (Function.updateFinset (fun i ↦ (x i,z i)) s p) i).1)=
      ambientSecond s σ hσ (x,p) := by
  rw [partialReverse_update]
  funext i
  by_cases hi : i∈s
  · simp only [ambientSecond,Function.updateFinset,dite_eq_left hi]
  · simp only [ambientSecond,Function.updateFinset,dite_eq_right hi,
      partialReversePairs_outside_fst σ s hσ _ i hi]

omit [Fintype J] [DecidableEq J] in
lemma routeChecks_both (σ : Equiv.Perm I) (s : Finset I) (hσ : ∀i,i∉s→σ i=i)
    (r : ℝ) (anchor : J→HardSphere.Torus L) (allowed : J→Set C(Time,Point))
    (label : J→I) (get : ∀j,X (label j)→allowed j) (hg : ∀j,Measurable (get j))
    (p : ∀i,X i×X (σ.symm i)) :
    p∈retainedEvent (routeChecks σ s hσ r anchor allowed label get hg) Finset.univ ↔
      (fun i ↦ (p i).1)∈retainedEvent (primaryChecks r anchor allowed label get hg) Finset.univ ∧
      (fun i ↦ (partialReversePairs σ s hσ p i).1)∈
        retainedEvent (primaryChecks r anchor allowed label get hg) Finset.univ := by
  constructor
  · intro hp
    refine ⟨routeChecks_primary σ s hσ r anchor allowed label get hg _ p hp,?_⟩
    intro e _
    rcases e with ⟨b,e⟩
    change ¬TrialCollision r
      (projectCurve L (get e.val.2 (partialReversePairs σ s hσ p (label e.val.2)).1).val)
      (get e.val.1 (partialReversePairs σ s hσ p (label e.val.1)).1).val
    rw [partialReverse_primary_path σ s hσ allowed label get p e.val.2,
      partialReverse_primary_path σ s hσ allowed label get p e.val.1]
    exact hp (true,e) (Finset.subset_univ _)
  · rintro ⟨hp,hq⟩ ⟨b,e⟩ _
    cases b
    · exact hp (false,e) (Finset.subset_univ _)
    · have h := hq (false,e) (Finset.subset_univ _)
      change ¬TrialCollision r
        (projectCurve L (get e.val.2 (partialReversePairs σ s hσ p (label e.val.2)).1).val)
        (get e.val.1 (partialReversePairs σ s hσ p (label e.val.1)).1).val at h
      rw [partialReverse_primary_path σ s hσ allowed label get p e.val.2,
      partialReverse_primary_path σ s hσ allowed label get p e.val.1] at h
      exact h

omit [Fintype J] [DecidableEq J] in
lemma ambient_proposalEvent (σ : Equiv.Perm I) (s : Finset I) (hσ : ∀i,i∉s→σ i=i)
    (r : ℝ) (anchor : J→HardSphere.Torus L) (allowed : J→Set C(Time,Point))
    (label : J→I) (get : ∀j,X (label j)→allowed j) (hg : ∀j,Measurable (get j))
    (z : ∀i,X (σ.symm i)) :
    {p : (∀i,X i)×(∀i:s,X i×X (σ.symm i)) |
      ambientFirst s σ p∈retainedEvent (primaryChecks r anchor allowed label get hg) Finset.univ ∧
      ambientSecond s σ hσ p∈retainedEvent (primaryChecks r anchor allowed label get hg) Finset.univ} =
    proposalEvent (routeChecks σ s hσ r anchor allowed label get hg) s (Finset.univ\s) z := by
  ext p
  simp only [proposalEvent,mem_ofPred_eq,Finset.union_sdiff_of_subset (Finset.subset_univ s)]
  rw [routeChecks_both,ambientFirst_updated,ambientSecond_updated]

end HardSphere.Comparison
end
end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Bridges_RouteAuxiliary
attribute [-instance] _root_.OAI.HardSphere.Groups.labelOptionSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace HardSphere.Bridge
open Comparison
attribute [local instance] Classical.propDecidable
variable {I : Type*} [Fintype I] [DecidableEq I] {X : I→Type*}
  [∀i,MeasurableSpace (X i)]

omit [Fintype I] [DecidableEq I] in
lemma fiberEquiv_map (μ : ∀i,Measure (X i)) {i j : I} (h : i=j) :
    (μ i).map (fiberEquiv h)=μ j := by
  subst j
  exact Measure.map_id

omit [Fintype I] [DecidableEq I] in
lemma reverseFactor_fst (σ : Equiv.Perm I) (j : I)
    (ρ : Measure (X (σ j)×X (σ.symm (σ j)))) :
    (ρ.map (reverseFactor σ j)).fst=ρ.snd.map (fiberEquiv (σ.symm_apply_apply j)) := by
  rw [Measure.fst,Measure.snd,Measure.map_map measurable_fst (reverseFactor σ j).measurable,
    Measure.map_map (fiberEquiv (σ.symm_apply_apply j)).measurable measurable_snd]
  rfl

omit [Fintype I] [DecidableEq I] in
lemma exists_two_auxiliary (σ : Equiv.Perm I)
    (μ ν : ∀i,Measure (X i)) [∀i,IsProbabilityMeasure (μ i)] [∀i,IsProbabilityMeasure (ν i)]
    [∀i,StandardBorelSpace (X i)]
    (ρ : ∀i,Measure (X i×X (σ.symm i))) [∀i,IsProbabilityMeasure (ρ i)]
    {G : ℝ≥0∞} (hG : G≠⊤)
    (hfst : ∀i,(ρ i).fst≤G • μ i) (hsnd : ∀i,(ρ i).snd≤G • ν (σ.symm i)) :
    ∃ (κ : ∀i,Kernel (X i) (X (σ.symm i))) (η : ∀i,Kernel (X i) (X (σ i))),
      (∀i,IsFiniteKernel (κ i)) ∧ (∀i,IsFiniteKernel (η i)) ∧
      (∀i,(μ i).compProd (κ i)=ρ i) ∧
      (∀i,(ν i).compProd (η i)=(ρ (σ i)).map (reverseFactor σ i)) ∧
      (∀i x,κ i x univ≤G) ∧ (∀i x,η i x univ≤G) ∧
      (∀i,∫⁻x,κ i x univ ∂μ i=1) ∧ (∀i,∫⁻x,η i x univ ∂ν i=1) := by
  let : ∀i,Nonempty (X i) := fun i ↦ nonempty_of_isProbabilityMeasure (μ i)
  have hκ := fun i ↦ exists_bounded_auxiliary_kernel (μ i) (ρ i) hG (hfst i)
  choose κ hκf hκe hκb hκm using hκ
  have hη : ∀i,∃ η : Kernel (X i) (X (σ i)),IsFiniteKernel η ∧
      (ν i).compProd η=(ρ (σ i)).map (reverseFactor σ i) ∧
      (∀x,η x univ≤G) ∧ (∫⁻x,η x univ ∂ν i)=1 := by
    intro i
    have : IsProbabilityMeasure ((ρ (σ i)).map (reverseFactor σ i)) :=
      (Measure.isProbabilityMeasure_map_iff
        (reverseFactor σ i).measurable.aemeasurable).mpr inferInstance
    apply exists_bounded_auxiliary_kernel _ _ hG
    rw [reverseFactor_fst]
    have hh := Measure.map_mono (hsnd (σ i)) (fiberEquiv (σ.symm_apply_apply i)).measurable
    rwa [Measure.map_smul G,
      fiberEquiv_map] at hh
  choose η hηf hηe hηb hηm using hη
  exact ⟨κ,η,hκf,hηf,hκe,hηe,hκb,hηb,hκm,hηm⟩

omit [Fintype I] in
lemma extendSelectedPair_selected (σ : Equiv.Perm I) (s : Finset I)
    (μ ν : ∀i,Measure (X i)) (ρ : ∀i:s,Measure (X i×X (σ.symm i))) (i : s) :
    extendSelectedPair σ s μ ν ρ i=ρ i := by simp [extendSelectedPair,i.property]

omit [Fintype I] in
lemma extendSelectedPair_bounds (σ : Equiv.Perm I) (s : Finset I)
    (μ ν : ∀i,Measure (X i)) [∀i,IsProbabilityMeasure (μ i)] [∀i,IsProbabilityMeasure (ν i)]
    (ρ : ∀i:s,Measure (X i×X (σ.symm i))) {G : ℝ≥0∞} (hG : 1≤G)
    (hfst : ∀i,(ρ i).fst≤G • μ i) (hsnd : ∀i,(ρ i).snd≤G • ν (σ.symm i)) (i : I) :
    (extendSelectedPair σ s μ ν ρ i).fst≤G • μ i ∧
    (extendSelectedPair σ s μ ν ρ i).snd≤G • ν (σ.symm i) := by
  unfold extendSelectedPair
  split
  · exact ⟨hfst _,hsnd _⟩
  · rw [Measure.fst_prod,Measure.snd_prod]
    constructor <;> intro A
    · simpa only [Measure.smul_apply,smul_eq_mul,one_mul] using (mul_le_mul' hG (le_refl (μ i A)))
    · simpa only [Measure.smul_apply,smul_eq_mul,one_mul] using (mul_le_mul' hG (le_refl (ν (σ.symm i) A)))

end HardSphere.Bridge
end
end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Allocation_PhysicalLikelihood
attribute [-instance] _root_.OAI.HardSphere.Bridge.targetUniform_finite _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Rescaling.config_haar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
namespace HardSphere.Groups
open Wiener Bridge Sampling Comparison GaussianPacking PathCutoff CellOrbital
variable {J : Type*} [Fintype J] [DecidableEq J]

omit [Fintype J] [DecidableEq J] in
lemma physicalOn_probability {N K M G : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (m : ℕ) (t r R C S : ℝ) (u : Time)
    (particle : J→Fin N) (v : Fin 3→Fin K) (d : PhysicalDatum N K M G L)
    (hp : ∀j,IsProbabilityMeasure (datumIndividualReference hL g m r R C S t u (particle j) d))
    (i : Option J) : IsProbabilityMeasure (physicalSlotOn hL g m t r R C S u particle v d i) := by
  have : IsProbabilityMeasure (physicalSlotReference hL g m t r R C S u particle v i d) := by
    cases i with
    | none => exact inferInstanceAs (IsProbabilityMeasure (cellPathReference v))
    | some i => exact hp i
  exact physicalSlotOn_probability hL g m t r R C S u particle v d i

omit [Fintype J] in
theorem physical_auxiliary_exists {N K M G n : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (m : ℕ) (t r R C S : ℝ) (ht : 0<t) (u : Time)
    (particle : J↪Fin N) (labels : Fin (n+1)↪J) (v : Fin (n+2)→(Fin 3→Fin K))
    (steps : Fin (n+1)→Fin 7)
    (hc : ∀k,projectPoint L (routeCellPeriod (v k.succ) (v k.castSucc) (steps k))=0)
    (d : PhysicalDatum N K M G L)
    (hhome : ∀k,datumHome hL d (particle (labels k))=v k.castSucc)
    (haccess : ∀k,datumAccessible hL g m t r R C S u (particle (labels k)) d)
    (hp : ∀j,IsProbabilityMeasure (datumIndividualReference hL g m r R C S t u (particle j) d)) :
    let X : Option J → Type := fun i ↦ physicalSlotAllowed hL g m r R C S u particle d i
    let σ := routePermutation labels
    let μ := physicalSlotOn hL g m t r R C S u particle (v (Fin.last (n+1))) d
    let ν := physicalSlotOn hL g m t r R C S u particle (v 0) d
    let ρ := physicalSelectedOn hL g m t r R C S u particle labels v steps d
    ∃ (κ : ∀i,Kernel (X i) (X (σ.symm i))) (η : ∀i,Kernel (X i) (X (σ i))),
      (∀i,IsFiniteKernel (κ i)) ∧ (∀i,IsFiniteKernel (η i)) ∧
      (∀i:routeSlots labels,(μ i).compProd (κ i)=ρ i) ∧
      (∀i,((μ (σ i)).compProd (κ (σ i))).map (reverseFactor (X:=X) σ i)=(ν i).compProd (η i)) ∧
      (∀i x,κ i x univ ≤ routeDensityBound t) ∧ (∀i x,η i x univ ≤ routeDensityBound t) ∧
      (∀i,∫⁻x,κ i x univ ∂μ i=1) ∧ (∀i,∫⁻x,η i x univ ∂ν i=1) := by
  dsimp only
  let X : Option J → Type := fun i ↦ physicalSlotAllowed hL g m r R C S u particle d i
  let σ := routePermutation labels
  let s := routeSlots labels
  let μ := physicalSlotOn hL g m t r R C S u particle (v (Fin.last (n+1))) d
  let ν := physicalSlotOn hL g m t r R C S u particle (v 0) d
  let ρ := physicalSelectedOn hL g m t r R C S u particle labels v steps d
  have : ∀i,IsProbabilityMeasure (μ i) := physicalOn_probability hL g m t r R C S u particle _ d hp
  have : ∀i,IsProbabilityMeasure (ν i) := physicalOn_probability hL g m t r R C S u particle _ d hp
  have hρ := physicalSelectedOn_physical hL g m t r R C S ht u particle labels v steps hc d hhome haccess
  have : ∀i,IsProbabilityMeasure (ρ i) := fun i ↦ (hρ i).1
  let ρ' := extendSelectedPair σ s μ ν ρ
  have hh := extendSelectedPair_bounds σ s μ ν ρ (one_le_routeDensityBound t)
    (fun i ↦ (hρ i).2.2.2.1) (fun i ↦ (hρ i).2.2.2.2.1)
  obtain ⟨κ,η,hκf,hηf,hκe,hηe,hκb,hηb,hκm,hηm⟩ := exists_two_auxiliary σ μ ν ρ'
    (routeDensityBound_ne_top ht) (fun i ↦ (hh i).1) (fun i ↦ (hh i).2)
  refine ⟨κ,η,hκf,hηf,?_,?_,hκb,hηb,hκm,hηm⟩
  · intro i
    exact (hκe i).trans (extendSelectedPair_selected σ s μ ν ρ i)
  · intro i
    rw [hκe,hηe]

end HardSphere.Groups
end
end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Allocation_RouteCenters
attribute [-instance] _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotAllowed_borel _root_.OAI.HardSphere.Groups.physicalSlotOn_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Rescaling.config_haar _root_.OAI.HardSphere.bridgeEndpointBase_finite _root_.OAI.HardSphere.endpointWeightedBase_sfinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
namespace HardSphere.Groups
open Comparison CellOrbital
attribute [local instance] Classical.propDecidable
variable {J : Type*} [Fintype J] [DecidableEq J]

omit [Fintype J] [DecidableEq J] in
lemma routeEmbedding_center {K n : ℕ} (home : J→Fin 3→Fin K)
    (labels : Fin n↪J) (v : Fin (n+1)→Fin 3→Fin K)
    (hh : ∀i,home (labels i)=v i.castSucc) (i : Fin (n+1)) :
    slotCenter home (v (Fin.last n)) (routeEmbedding labels i)=v i := by
  by_cases hi : i.val<n
  · have he : i=(⟨i.val,hi⟩ : Fin n).castSucc := Fin.ext rfl
    rw [he,routeEmbedding_castSucc]
    exact hh _
  · have he : i=Fin.last n := Fin.ext (by simp only [Fin.val_last]; omega)
    rw [he,routeEmbedding_last]
    rfl

omit [Fintype J] [DecidableEq J] in
lemma route_two_center_bounds {K n : ℕ} {L : Length}
    (home : J→Fin 3→Fin K) (labels : Fin (n+1)↪J)
    (v : Fin (n+2)→Fin 3→Fin K)
    (hh : ∀i,home (labels i)=v i.castSucc)
    (ha : ∀i : Fin (n+1),torusDistance L (gridCenter L (v i.castSucc))
      (gridCenter L (v i.succ))≤1) :
    (∀j,torusDistance L (gridCenter L (home j))
      (gridCenter L (slotCenter home (v (Fin.last (n+1))) (routePermutation labels (some j))))≤1) ∧
    (∀j,torusDistance L (gridCenter L (home j))
      (gridCenter L (slotCenter home (v 0) ((routePermutation labels).symm (some j))))≤1) := by
  have hf : ∀j,torusDistance L (gridCenter L (home j))
      (gridCenter L (slotCenter home (v (Fin.last (n+1))) (routePermutation labels (some j))))≤1 := by
    intro j
    by_cases hj : ∃i,labels i=j
    · obtain ⟨i,rfl⟩ := hj
      rw [routePermutation_label,routeEmbedding_center home labels v hh,hh i]
      exact ha i
    · have hnot : some j∉routeSlots labels := by
        rw [routeSlots_exact]
        simp only [Finset.mem_insert,Option.some_ne_none,Finset.mem_image,Finset.mem_univ,
          true_and,false_or,not_exists]
        intro i hi
        exact hj ⟨i,Option.some.inj hi⟩
      rw [routePermutation_fixed labels _ hnot]
      change torusDistance L (gridCenter L (home j)) (gridCenter L (home j))≤1
      simp [torusDistance]
  refine ⟨hf,?_⟩
  intro j
  cases he : (routePermutation labels).symm (some j) with
  | none =>
    have hj : j=labels 0 := by
      have hh' := congrArg (routePermutation labels) he
      rw [Equiv.apply_symm_apply,routePermutation_star] at hh'
      exact Option.some.inj hh'
    rw [hj,hh 0]
    change torusDistance L (gridCenter L (v 0)) (gridCenter L (v 0))≤1
    simp [torusDistance]
  | some k =>
    have hek : routePermutation labels (some k)=some j := by
      rw [←he,Equiv.apply_symm_apply]
    have hk := hf k
    rw [hek] at hk
    change torusDistance L (gridCenter L (home j)) (gridCenter L (home k))≤1
    change torusDistance L (gridCenter L (home k)) (gridCenter L (home j))≤1 at hk
    rw [torusDistance_comm]
    exact hk

lemma slotCenter_fiber {K : ℕ} (home : J→Fin 3→Fin K) (v : Fin 3→Fin K)
    (M : ℕ) (hm : ∀w,(Finset.univ.filter (fun j ↦ home j=w)).card≤M) (w : Fin 3→Fin K) :
    (Finset.univ.filter (fun i ↦ slotCenter home v i=w)).card≤M+1 := by
  have hs : Finset.univ.filter (fun i ↦ slotCenter home v i=w) ⊆
      insert none ((Finset.univ.filter (fun j ↦ home j=w)).image some) := by
    intro i hi
    cases i with
    | none => exact Finset.mem_insert_self _ _
    | some j =>
      exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨j,Finset.mem_filter.mpr
        ⟨Finset.mem_univ _,(Finset.mem_filter.mp hi).2⟩,rfl⟩)
  exact (Finset.card_le_card hs).trans ((Finset.card_insert_le _ _).trans
    (Nat.add_le_add_right (Finset.card_image_le.trans (hm w)) 1))

end HardSphere.Groups
end
end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Bridges_RouteInsertion
attribute [-instance] _root_.OAI.HardSphere.Bridge.exposedBridgeKernel_markov _root_.OAI.HardSphere.Bridge.exposedPeriodSingle_finite _root_.OAI.HardSphere.Bridge.exposedTrialKernel_markov _root_.OAI.HardSphere.Bridge.parameterBridgeKernel_markov _root_.OAI.HardSphere.Bridge.parameterIndividualReference_finite _root_.OAI.HardSphere.Bridge.parameterTrialKernel_markov _root_.OAI.HardSphere.Bridge.targetUniform_finite _root_.OAI.HardSphere.Comparison.parameterTargetKernel_finite _root_.OAI.HardSphere.Groups.cellPathReference_probability _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotAllowed_borel _root_.OAI.HardSphere.Groups.physicalSlotOn_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Rescaling.config_haar _root_.OAI.HardSphere.bridgeEndpointBase_finite _root_.OAI.HardSphere.endpointWeightedBase_sfinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace HardSphere.Bridge
open Wiener GaussianPacking Comparison Groups CellOrbital
attribute [local instance] Classical.propDecidable
variable {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
  {L : Length} {X : I → Type*} [∀i,MeasurableSpace (X i)]
lemma route_insertion {K : ℕ} [NeZero K] (hL : L.val=(K:ℝ))
    (r : ℝ) (anchor : J→Torus L) (center : I→Fin 3→Fin K)
    (M : ℕ) (hm : ∀v,(Finset.univ.filter (fun i : I ↦ center i=v)).card≤M)
    (allowed : J→Set C(Time,Point)) (label : J→I) (hl : Function.Injective label)
    (get : ∀j,X (label j)→allowed j) (hg : ∀j,Measurable (get j))
    (σ : Equiv.Perm I) (S : Finset I) (hfix : ∀i,i∉S → σ i=i)
    (hc : ∀b j,torusDistance L (anchor j) (gridCenter L (center (routeOwner σ label b j)))≤1)
    (ν : ∀i,Measure (X i×X (σ.symm i))) [∀i,IsProbabilityMeasure (ν i)]
    (P : ∀j,Measure (allowed j)) (G q a : ℝ≥0∞)
    (hdom : ∀b j,routeOwner σ label b j∈S → (ν (routeOwner σ label b j)).map
      (routePath σ S hfix allowed label get b j)≤G • P j)
    (hq : ∀j k,j≠k → ∀g : allowed k,P j {f | TrialCollision r (projectCurve L g.val) f.val}≤q)
    (hsmall : a+(4*(49^3*M):ℕ)*(G*q)≤1) :
    UniformInsertionOn (routeChecks σ S hfix r anchor allowed label get hg) ν a S := by
  unfold routeChecks
  exact physicalSparseChecks_insertion (V:=fun i ↦ X i×X (σ.symm i)) hL r anchor center M hm allowed (routeOwner σ label)
    (routeOwner_injective σ label hl) hc (routePath σ S hfix allowed label get)
    (routePath_measurable σ S hfix allowed label get hg) ν P G q a S hdom hq hsmall

end HardSphere.Bridge

end
end

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Bridges_RouteMass
attribute [-instance] _root_.OAI.HardSphere.Bridge.exposedPeriodSingle_finite _root_.OAI.HardSphere.Bridge.targetUniform_finite _root_.OAI.HardSphere.Comparison.parameterTargetKernel_finite _root_.OAI.HardSphere.Groups.cellPathReference_probability _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotAllowed_borel _root_.OAI.HardSphere.Groups.physicalSlotOn_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Rescaling.config_haar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace HardSphere.Bridge
open Wiener GaussianPacking Comparison Groups CellOrbital
attribute [local instance] Classical.propDecidable
variable {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
  {L : Length} {X : I→Type*} [∀i,MeasurableSpace (X i)]

lemma route_acceptance_pos (σ : Equiv.Perm I) (s : Finset I)
    (hσ : ∀i,i∉s→σ i=i) (r : ℝ) (anchor : J→Torus L)
    (allowed : J→Set C(Time,Point)) (label : J→I)
    (get : ∀j,X (label j)→allowed j) (hg : ∀j,Measurable (get j))
    (ν : ∀i,Measure (X i×X (σ.symm i))) [∀i,IsFiniteMeasure (ν i)]
    (a : ℝ≥0∞) (ha : 0<a)
    (hi : UniformInsertionOn (routeChecks σ s hσ r anchor allowed label get hg) ν a s)
    (x : ∀i,X i) (z : ∀i,X (σ.symm i))
    (hx : x∈retainedEvent (primaryChecks r anchor allowed label get hg) Finset.univ) :
    0<(Measure.pi fun i:s ↦ ν i)
      {p | ambientFirst s σ (x,p)∈retainedEvent (primaryChecks r anchor allowed label get hg) Finset.univ ∧
        ambientSecond s σ hσ (x,p)∈retainedEvent (primaryChecks r anchor allowed label get hg) Finset.univ} := by
  let C := routeChecks σ s hσ r anchor allowed label get hg
  have hso : Disjoint s (Finset.univ\s) := Finset.disjoint_left.mpr (fun _ hi hj ↦ (Finset.mem_sdiff.mp hj).2 hi)
  have ho : (fun i ↦ (x i,z i))∈retainedEvent C (Finset.univ\s) :=
    routeChecks_outside σ s hσ r anchor allowed label get hg _ hso _
      (fun e he ↦ hx e (Finset.subset_univ _))
  have hp := partialNormalizer_pos C ha hi hso (fun i ↦ (x i,z i)) ho
  have he := congrArg (fun A ↦ Prod.mk x ⁻¹' A)
    (ambient_proposalEvent σ s hσ r anchor allowed label get hg z)
  change 0<(Measure.pi fun i:s ↦ ν i) (Prod.mk x ⁻¹'
    {p | ambientFirst s σ p∈retainedEvent (primaryChecks r anchor allowed label get hg) Finset.univ ∧
      ambientSecond s σ hσ p∈retainedEvent (primaryChecks r anchor allowed label get hg) Finset.univ})
  rw [he]
  have hm := (measurable_proposalEvent C s (Finset.univ\s) z).preimage (measurable_prodMk_left (x:=x))
  change 0 < ∫⁻ proposal, (Prod.mk x ⁻¹' proposalEvent C s (Finset.univ\s) z).indicator
    (fun _ ↦ (1 : ℝ≥0∞)) proposal ∂(Measure.pi fun i:s ↦ ν i) at hp
  simpa only [lintegral_indicator_fun_one hm] using hp

theorem route_shared_mass (σ : Equiv.Perm I) (s : Finset I)
    (hσ : ∀i,i∉s→σ i=i) (r : ℝ) (anchor : J→Torus L)
    (allowed : J→Set C(Time,Point)) (label : J→I)
    (get : ∀j,X (label j)→allowed j) (hg : ∀j,Measurable (get j))
    (μ : ∀i,Measure (X i)) [∀i,IsProbabilityMeasure (μ i)]
    (ν : ∀i,Measure (X i×X (σ.symm i))) [∀i,IsFiniteMeasure (ν i)]
    (a : ℝ≥0∞) (ha : 0<a)
    (hi : UniformInsertionOn (routeChecks σ s hσ r anchor allowed label get hg) ν a s)
    (z : ∀i,X (σ.symm i)) :
    let A := retainedEvent (primaryChecks r anchor allowed label get hg) Finset.univ
    let P := conditionedMeasure (Measure.pi μ) A
    ambientSharedKernel s σ hσ (Kernel.const Unit P)
      (fun i ↦ Kernel.const Unit (ν i)) (Prod.snd ⁻¹' A) () univ = P univ := by
  dsimp only
  apply ambientSharedKernel_mass
  · exact (measurableSet_retainedEvent _ _).preimage measurable_snd
  · have hm := ae_restrict_mem (μ:=Measure.pi μ) (measurableSet_retainedEvent
      (primaryChecks r anchor allowed label get hg) Finset.univ)
    have hx := Measure.ae_smul_measure hm
      ((Measure.pi μ) (retainedEvent (primaryChecks r anchor allowed label get hg) Finset.univ))⁻¹
    filter_upwards [hx] with x hx
    exact route_acceptance_pos σ s hσ r anchor allowed label get hg ν a ha hi x z hx

end HardSphere.Bridge
end
end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Bridges_RouteMarginals
attribute [-instance] _root_.OAI.HardSphere.Bridge.targetUniform_finite _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Rescaling.config_haar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
namespace HardSphere.Bridge
open Wiener GaussianPacking Comparison Groups
variable {I J : Type*} [Fintype I] [DecidableEq I]
  {X : I→Type*} [∀i,MeasurableSpace (X i)]

omit [Fintype I] [DecidableEq I] in
lemma fiberEquiv_map_measure (μ : ∀i,Measure (X i)) {i j : I} (h : i=j) :
    (μ i).map (fiberEquiv h)=μ j := by
  subst j
  change (μ i).map id=μ i
  exact Measure.map_id

omit [Fintype I] in
theorem routePath_marginal_le (σ : Equiv.Perm I) (s : Finset I)
    (hf : ∀i,i∉s→σ i=i) (allowed : J→Set C(Time,Point)) (label : J→I)
    (get : ∀j,X (label j)→allowed j) (hg : ∀j,Measurable (get j))
    (μ ν : ∀i,Measure (X i)) (ρ : ∀i,Measure (X i×X (σ.symm i)))
    (G : ℝ≥0∞) (heq : ∀j,μ (label j)=ν (label j))
    (hl : ∀i∈s,(ρ i).fst≤G • μ i) (hr : ∀i∈s,(ρ i).snd≤G • ν (σ.symm i))
    (b : Bool) (j : J) (hs : routeOwner σ label b j∈s) :
    (ρ (routeOwner σ label b j)).map (routePath σ s hf allowed label get b j)≤
      G • (μ (label j)).map (get j) := by
  cases b
  · change (ρ (label j)).map (fun p ↦ get j p.1)≤_
    have hh := (Measure.map_mono (f:=get j) (hl _ hs) (hg j)).trans_eq
      (Measure.map_smul _ _ _)
    simpa only [Measure.fst,Measure.map_map (hg j) measurable_fst,Function.comp_def] using hh
  · have hj : label j∈s := (move_mem_iff σ s hf (label j)).mp hs
    simp only [routePath,dite_eq_left hj]
    have hm : Measurable (fun p : X (σ.symm (σ (label j))) ↦
        get j (fiberEquiv (σ.symm_apply_apply (label j)) p)) :=
      (hg j).comp (fiberEquiv _).measurable
    have hmap := Measure.map_mono (f:=(fun p : X (σ.symm (σ (label j))) ↦
      get j (fiberEquiv (σ.symm_apply_apply (label j)) p))) (hr _ hs) hm
    rw [Measure.map_smul G] at hmap
    have hc : (ν (σ.symm (σ (label j)))).map (fun p ↦
        get j (fiberEquiv (σ.symm_apply_apply (label j)) p))=(μ (label j)).map (get j) := by
      calc
        _ = ((ν (σ.symm (σ (label j)))).map (fiberEquiv (σ.symm_apply_apply (label j)))).map (get j) :=
          (Measure.map_map (hg j) (fiberEquiv _).measurable).symm
        _ = _ := by rw [fiberEquiv_map_measure,←heq j]
    rw [hc] at hmap
    change (ρ (σ (label j))).map (fun p ↦ get j (fiberEquiv (σ.symm_apply_apply (label j)) p.2))≤_
    rw [Measure.snd,Measure.map_map hm measurable_snd] at hmap
    exact hmap

end HardSphere.Bridge
end
end

section

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
namespace HardSphere.Bridge
open Wiener Comparison GaussianPacking
variable {I : Type*} [Fintype I] [DecidableEq I]
  {X : I→Type*} [∀i,MeasurableSpace (X i)]

omit [Fintype I] [DecidableEq I] in
lemma reverseFactor_snd (σ : Equiv.Perm I) (j : I)
    (ρ : Measure (X (σ j)×X (σ.symm (σ j)))) :
    (ρ.map (reverseFactor σ j)).snd=ρ.fst := by
  rw [Measure.snd,Measure.fst,Measure.map_map measurable_snd (reverseFactor σ j).measurable]
  rfl

omit [Fintype I] in
lemma reverse_pair_bounds (σ : Equiv.Perm I) (s : Finset I)
    (hf : ∀i,i∉s→σ i=i) (μ ν : ∀i,Measure (X i))
    (ρ : ∀i,Measure (X i×X (σ.symm i))) (θ : ∀i,Measure (X i×X (σ i)))
    (G : ℝ≥0∞) (he : ∀i∈s,(ρ (σ i)).map (reverseFactor σ i)=θ i)
    (hl : ∀i∈s,(ρ i).fst≤G • μ i) (hr : ∀i∈s,(ρ i).snd≤G • ν (σ.symm i)) :
    (∀i∈s,(θ i).fst≤G • ν i) ∧ (∀i∈s,(θ i).snd≤G • μ (σ i)) := by
  constructor
  · intro i hi
    rw [←he i hi,reverseFactor_fst]
    have hh := Measure.map_mono (hr _ ((move_mem_iff σ s hf i).mpr hi))
      (fiberEquiv (σ.symm_apply_apply i)).measurable
    rwa [Measure.map_smul,
      fiberEquiv_map_measure] at hh
  · intro i hi
    rw [←he i hi,reverseFactor_snd]
    exact hl _ ((move_mem_iff σ s hf i).mpr hi)
end HardSphere.Bridge

namespace HardSphere.Groups
open Wiener Bridge Sampling Comparison GaussianPacking PathCutoff CellOrbital
variable {J : Type*} [Fintype J] [DecidableEq J]
attribute [local instance] Classical.propDecidable

omit [Fintype J] in
lemma route_selected_accessible {N K M G n : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (m : ℕ) (t r R C S : ℝ) (u : Time)
    (particle : J→Fin N) (labels : Fin n↪J) (d : PhysicalDatum N K M G L)
    (ha : ∀k,datumAccessible hL g m t r R C S u (particle (labels k)) d)
    (j : J) (h : some j∈routeSlots labels) :
    datumAccessible hL g m t r R C S u (particle j) d := by
  rw [routeSlots_exact] at h
  rcases Finset.mem_insert.mp h with h|h
  · contradiction
  · obtain ⟨i,_,he⟩ := Finset.mem_image.mp h
    rw [←Option.some.inj he]
    exact ha i

omit [Fintype J] in
theorem physical_auxiliary_path_bounds {N K M G n : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (m : ℕ) (t r R C S : ℝ) (ht : 0<t) (u : Time)
    (particle : J↪Fin N) (labels : Fin (n+1)↪J) (v : Fin (n+2)→(Fin 3→Fin K))
    (steps : Fin (n+1)→Fin 7)
    (hc : ∀k,projectPoint L (routeCellPeriod (v k.succ) (v k.castSucc) (steps k))=0)
    (d : PhysicalDatum N K M G L)
    (hhome : ∀k,datumHome hL d (particle (labels k))=v k.castSucc)
    (haccess : ∀k,datumAccessible hL g m t r R C S u (particle (labels k)) d)
    (κ : ∀i,Kernel (physicalSlotAllowed hL g m r R C S u particle d i)
      (physicalSlotAllowed hL g m r R C S u particle d ((routePermutation labels).symm i)))
    [∀i,IsFiniteKernel (κ i)]
    (η : ∀i,Kernel (physicalSlotAllowed hL g m r R C S u particle d i)
      (physicalSlotAllowed hL g m r R C S u particle d (routePermutation labels i)))
    [∀i,IsFiniteKernel (η i)]
    (he : ∀i:routeSlots labels,
      (physicalSlotOn hL g m t r R C S u particle (v (Fin.last (n+1))) d i).compProd (κ i)=
        physicalSelectedOn hL g m t r R C S u particle labels v steps d i)
    (hr : ∀i:routeSlots labels,
      ((physicalSlotOn hL g m t r R C S u particle (v (Fin.last (n+1))) d (routePermutation labels i)).compProd
        (κ (routePermutation labels i))).map (reverseFactor (X:=fun i ↦ physicalSlotAllowed hL g m r R C S u particle d i)
          (routePermutation labels) i)=
      (physicalSlotOn hL g m t r R C S u particle (v 0) d i).compProd (η i)) :
    let σ := routePermutation labels
    let s := routeSlots labels
    let A := fun j ↦ physicalSlotAllowed hL g m r R C S u particle d (some j)
    let μ := physicalSlotOn hL g m t r R C S u particle (v (Fin.last (n+1))) d
    let ν := physicalSlotOn hL g m t r R C S u particle (v 0) d
    (∀b j,routeOwner σ some b j∈s→
      ((μ (routeOwner σ some b j)).compProd (κ (routeOwner σ some b j))).map
        (routePath (X:=fun i ↦ physicalSlotAllowed hL g m r R C S u particle d i) σ s (routePermutation_fixed labels) A some (fun _ f ↦ f) b j)≤
      routeDensityBound t • μ (some j)) ∧
    (∀b j,routeOwner σ.symm some b j∈s→
      ((ν (routeOwner σ.symm some b j)).compProd (η (routeOwner σ.symm some b j))).map
        (routePath (X:=fun i ↦ physicalSlotAllowed hL g m r R C S u particle d i) σ.symm s (reverse_fix σ s (routePermutation_fixed labels)) A some (fun _ f ↦ f) b j)≤
      routeDensityBound t • ν (some j)) := by
  dsimp only
  let X : Option J → Type := fun i ↦ physicalSlotAllowed hL g m r R C S u particle d i
  let σ := routePermutation labels
  let s := routeSlots labels
  let μ := physicalSlotOn hL g m t r R C S u particle (v (Fin.last (n+1))) d
  let ν := physicalSlotOn hL g m t r R C S u particle (v 0) d
  let ρ := fun i ↦ (μ i).compProd (κ i)
  let θ := fun i ↦ (ν i).compProd (η i)
  have hl : ∀i∈s,(ρ i).fst ≤ routeDensityBound t • μ i := by
    intro i hi
    change ((μ i).compProd (κ i)).fst≤_
    rw [he ⟨i,hi⟩]
    exact (physicalSelectedOn_physical hL g m t r R C S ht u particle labels v steps hc d hhome haccess ⟨i,hi⟩).2.2.2.1
  have hs : ∀i∈s,(ρ i).snd ≤ routeDensityBound t • ν (σ.symm i) := by
    intro i hi
    change ((μ i).compProd (κ i)).snd≤_
    rw [he ⟨i,hi⟩]
    exact (physicalSelectedOn_physical hL g m t r R C S ht u particle labels v steps hc d hhome haccess ⟨i,hi⟩).2.2.2.2.1
  have hb := reverse_pair_bounds σ s (routePermutation_fixed labels) μ ν ρ θ (routeDensityBound t)
    (fun i hi ↦ hr ⟨i,hi⟩) hl hs
  constructor
  · intro b j hj
    simpa only [μ,ν,ρ,θ,σ,s,Measure.map_id'] using routePath_marginal_le (X:=X) σ s (routePermutation_fixed labels)
      (fun j ↦ physicalSlotAllowed hL g m r R C S u particle d (some j)) some (fun _ f ↦ f) (fun _ ↦ measurable_id) μ ν ρ
      (routeDensityBound t) (fun _ ↦ rfl) hl hs b j hj
  · intro b j hj
    simpa only [μ,ν,ρ,θ,σ,s,Measure.map_id',Equiv.symm_symm] using routePath_marginal_le (X:=X) σ.symm s
      (reverse_fix σ s (routePermutation_fixed labels)) (fun j ↦ physicalSlotAllowed hL g m r R C S u particle d (some j)) some
      (fun _ f ↦ f) (fun _ ↦ measurable_id) ν μ θ (routeDensityBound t)
      (fun _ ↦ rfl) hb.1 hb.2 b j hj

end HardSphere.Groups
end
end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Collisions_PhysicalCollisionReference
attribute [-instance] _root_.OAI.HardSphere.Bridge.targetUniform_finite _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Rescaling.config_haar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
namespace HardSphere.Groups
open Wiener Bridge Sampling Comparison GaussianPacking PathCutoff CellOrbital
attribute [local instance] Classical.propDecidable
variable {J : Type*} [DecidableEq J]

omit [DecidableEq J] in
lemma physicalCollisionReference_eq {N K M G : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (m : ℕ) (t r R C S : ℝ) (u : Time)
    (particle : J→Fin N) (d : PhysicalDatum N K M G L) (j : J)
    (ha : datumAccessible hL g m t r R C S u (particle j) d) (v : Fin 3→Fin K) :
    physicalCollisionReference hL g m t r R C S u particle d j=
      physicalSlotOn hL g m t r R C S u particle v d (some j) := by
  change (if datumAccessible hL g m t r R C S u (particle j) d then _ else _) = _
  rw [ite_eq_left ha]
  rfl

lemma routeOwner_mem_real {n : ℕ} (labels : Fin n↪J) (b : Bool) (j : J)
    (h : routeOwner (routePermutation labels) some b j∈routeSlots labels) :
    some j∈routeSlots labels := by
  cases b
  · exact h
  · exact (move_mem_iff _ _ (routePermutation_fixed labels) _).mp h

lemma reverse_routeOwner_mem_real {n : ℕ} (labels : Fin n↪J) (b : Bool) (j : J)
    (h : routeOwner (routePermutation labels).symm some b j∈routeSlots labels) :
    some j∈routeSlots labels := by
  cases b
  · exact h
  · exact (move_mem_iff _ _ (reverse_fix _ _ (routePermutation_fixed labels)) _).mp h

theorem physical_auxiliary_collision_bounds {N K M G n : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (m : ℕ) (t r R C S : ℝ) (ht : 0 < t) (u : Time)
    (particle : J↪Fin N) (labels : Fin (n+1)↪J) (v : Fin (n+2)→(Fin 3→Fin K))
    (steps : Fin (n+1)→Fin 7)
    (hc : ∀k,projectPoint L (routeCellPeriod (v k.succ) (v k.castSucc) (steps k))=0)
    (d : PhysicalDatum N K M G L)
    (hhome : ∀k,datumHome hL d (particle (labels k))=v k.castSucc)
    (haccess : ∀k,datumAccessible hL g m t r R C S u (particle (labels k)) d)
    (κ : ∀i,Kernel (physicalSlotAllowed hL g m r R C S u particle d i)
      (physicalSlotAllowed hL g m r R C S u particle d ((routePermutation labels).symm i)))
    [∀i,IsFiniteKernel (κ i)]
    (η : ∀i,Kernel (physicalSlotAllowed hL g m r R C S u particle d i)
      (physicalSlotAllowed hL g m r R C S u particle d (routePermutation labels i)))
    [∀i,IsFiniteKernel (η i)]
    (he : ∀i:routeSlots labels,
      (physicalSlotOn hL g m t r R C S u particle (v (Fin.last (n+1))) d i).compProd (κ i)=
        physicalSelectedOn hL g m t r R C S u particle labels v steps d i)
    (hr : ∀i:routeSlots labels,
      ((physicalSlotOn hL g m t r R C S u particle (v (Fin.last (n+1))) d (routePermutation labels i)).compProd
        (κ (routePermutation labels i))).map (reverseFactor (X:=fun i ↦ physicalSlotAllowed hL g m r R C S u particle d i)
          (routePermutation labels) i)=
      (physicalSlotOn hL g m t r R C S u particle (v 0) d i).compProd (η i)) :
    let σ := routePermutation labels
    let s := routeSlots labels
    let A := fun j ↦ physicalSlotAllowed hL g m r R C S u particle d (some j)
    let μ := physicalSlotOn hL g m t r R C S u particle (v (Fin.last (n+1))) d
    let ν := physicalSlotOn hL g m t r R C S u particle (v 0) d
    (∀b j,routeOwner σ some b j∈s→
      ((μ (routeOwner σ some b j)).compProd (κ (routeOwner σ some b j))).map
        (routePath (X:=fun i ↦ physicalSlotAllowed hL g m r R C S u particle d i) σ s (routePermutation_fixed labels) A some (fun _ f ↦ f) b j)≤
      routeDensityBound t • physicalCollisionReference hL g m t r R C S u particle d j) ∧
    (∀b j,routeOwner σ.symm some b j∈s→
      ((ν (routeOwner σ.symm some b j)).compProd (η (routeOwner σ.symm some b j))).map
        (routePath (X:=fun i ↦ physicalSlotAllowed hL g m r R C S u particle d i) σ.symm s (reverse_fix σ s (routePermutation_fixed labels)) A some (fun _ f ↦ f) b j)≤
      routeDensityBound t • physicalCollisionReference hL g m t r R C S u particle d j) := by
  dsimp only
  obtain ⟨h₀,h₁⟩ := physical_auxiliary_path_bounds hL g m t r R C S ht u particle labels v steps hc d hhome haccess κ η he hr
  constructor
  · intro b j hj
    rw [physicalCollisionReference_eq hL g m t r R C S u particle d j
      (route_selected_accessible hL g m t r R C S u particle labels d haccess j
        (routeOwner_mem_real labels b j hj)) (v (Fin.last (n+1)))]
    exact h₀ b j hj
  · intro b j hj
    rw [physicalCollisionReference_eq hL g m t r R C S u particle d j
      (route_selected_accessible hL g m t r R C S u particle labels d haccess j
        (reverse_routeOwner_mem_real labels b j hj)) (v 0)]
    exact h₁ b j hj

end HardSphere.Groups
end
end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Allocation_PhysicalRouteMass
attribute [-instance] _root_.OAI.HardSphere.Bridge.targetUniform_finite _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Rescaling.config_haar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
namespace HardSphere.Groups
open Wiener Bridge Sampling Comparison GaussianPacking PathCutoff CellOrbital
attribute [local instance] Classical.propDecidable
variable {J : Type*} [Fintype J] [DecidableEq J]

omit [Fintype J] [DecidableEq J] in
lemma physical_owner_centers {N K M G n : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (particle : J→Fin N) (labels : Fin (n+1)↪J) (v : Fin (n+2)→(Fin 3→Fin K))
    (d : PhysicalDatum N K M G L)
    (hhome : ∀k,datumHome hL d (particle (labels k))=v k.castSucc)
    (hneigh : ∀k : Fin (n+1),torusDistance L (gridCenter L (v k.castSucc)) (gridCenter L (v k.succ))≤1) :
    ∀b j,torusDistance L (projectPoint L (anchorPoint (datumHome hL d (particle j))))
      (gridCenter L (slotCenter (fun j ↦ datumHome hL d (particle j)) (v (Fin.last (n+1)))
        (routeOwner (routePermutation labels) some b j)))≤1 := by
  intro b j
  cases b
  · change torusDistance L (gridCenter L (datumHome hL d (particle j)))
      (gridCenter L (datumHome hL d (particle j)))≤1
    simp [torusDistance]
  · exact (route_two_center_bounds (fun j ↦ datumHome hL d (particle j)) labels v hhome hneigh).1 j

lemma physical_forward_insertion {N K M G n : ℕ} [NeZero K] {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (m : ℕ) (t r R C S : ℝ) (u : Time)
    (particle : J↪Fin N) (labels : Fin (n+1)↪J) (v : Fin (n+2)→(Fin 3→Fin K))
    (d : PhysicalDatum N K M G L)
    (hhome : ∀k,datumHome hL d (particle (labels k))=v k.castSucc)
    (hneigh : ∀k : Fin (n+1),torusDistance L (gridCenter L (v k.castSucc)) (gridCenter L (v k.succ))≤1)
    (hm : ∀w,(Finset.univ.filter (fun j ↦ datumHome hL d (particle j)=w)).card≤M)
    (ν : ∀i,Measure (physicalSlotAllowed hL g m r R C S u particle d i ×
      physicalSlotAllowed hL g m r R C S u particle d ((routePermutation labels).symm i)))
    [∀i,IsProbabilityMeasure (ν i)] (q a : ℝ≥0∞)
    (hd : ∀b j,routeOwner (routePermutation labels) some b j∈routeSlots labels→
      (ν (routeOwner (routePermutation labels) some b j)).map
        (routePath (X:=fun i ↦ physicalSlotAllowed hL g m r R C S u particle d i) (routePermutation labels) (routeSlots labels) (routePermutation_fixed labels)
          (fun j ↦ physicalSlotAllowed hL g m r R C S u particle d (some j)) some (fun _ f ↦ f) b j)≤
        routeDensityBound t • physicalCollisionReference hL g m t r R C S u particle d j)
    (hq : ∀ j k, j ≠ k → ∀f : physicalSlotAllowed hL g m r R C S u particle d (some k),
      physicalCollisionReference hL g m t r R C S u particle d j
        {p | TrialCollision r (projectCurve L f.val) p.val}≤q)
    (hsmall : a+(4*(49^3*(M+1)):ℕ)*(routeDensityBound t*q)≤1) :
    UniformInsertionOn (routeChecks (X:=fun i ↦ physicalSlotAllowed hL g m r R C S u particle d i) (routePermutation labels) (routeSlots labels) (routePermutation_fixed labels)
      r (fun j ↦ projectPoint L (anchorPoint (datumHome hL d (particle j))))
      (fun j ↦ physicalSlotAllowed hL g m r R C S u particle d (some j)) some (fun _ f ↦ f) (fun _ ↦ measurable_id))
      ν a (routeSlots labels) := by
  exact route_insertion (X:=fun i ↦ physicalSlotAllowed hL g m r R C S u particle d i) hL r _ (slotCenter (fun j ↦ datumHome hL d (particle j)) (v (Fin.last (n+1)))) (M+1)
    (slotCenter_fiber _ _ M hm) _ some (Option.some_injective _) (fun _ f ↦ f) (fun _ ↦ measurable_id)
    _ _ (routePermutation_fixed labels) (physical_owner_centers hL particle labels v d hhome hneigh) ν
    (physicalCollisionReference hL g m t r R C S u particle d) (routeDensityBound t) q a hd hq hsmall

lemma physicalSharedOn_mass_of {N K M G n : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (m : ℕ) (t r R C S : ℝ) (u : Time)
    (particle : J↪Fin N) (labels : Fin (n+1)↪J) (v : Fin (n+2)→(Fin 3→Fin K))
    (steps : Fin (n+1)→Fin 7) (d : PhysicalDatum N K M G L)
    (hp : ∀j,IsProbabilityMeasure (datumIndividualReference hL g m r R C S t u (particle j) d))
    (ν : ∀i,Measure (physicalSlotAllowed hL g m r R C S u particle d i ×
      physicalSlotAllowed hL g m r R C S u particle d ((routePermutation labels).symm i)))
    [∀i,IsProbabilityMeasure (ν i)]
    (he : ∀i:routeSlots labels,ν i=physicalSelectedOn hL g m t r R C S u particle labels v steps d i)
    (a : ℝ≥0∞) (ha : 0<a)
    (hi : UniformInsertionOn (routeChecks (X:=fun i ↦ physicalSlotAllowed hL g m r R C S u particle d i)
      (routePermutation labels) (routeSlots labels) (routePermutation_fixed labels)
      r (fun j ↦ projectPoint L (anchorPoint (datumHome hL d (particle j))))
      (fun j ↦ physicalSlotAllowed hL g m r R C S u particle d (some j)) some (fun _ f ↦ f) (fun _ ↦ measurable_id))
      ν a (routeSlots labels)) :
    physicalSharedOn hL g m t r R C S u particle labels v steps d univ=
      physicalOnPrimary hL g m t r R C S u particle (v (Fin.last (n+1))) d univ := by
  let X : Option J→Type := fun i ↦ physicalSlotAllowed hL g m r R C S u particle d i
  let σ := routePermutation labels
  let s := routeSlots labels
  let μ := physicalSlotOn hL g m t r R C S u particle (v (Fin.last (n+1))) d
  have : ∀i,IsProbabilityMeasure (μ i) := physicalOn_probability hL g m t r R C S u particle _ d hp
  let z : ∀i,X (σ.symm i) := fun i ↦ Classical.choice (nonempty_of_isProbabilityMeasure (μ (σ.symm i)))
  have H := route_shared_mass (X:=X) σ s (routePermutation_fixed labels) r
    (fun j ↦ projectPoint L (anchorPoint (datumHome hL d (particle j))))
    (fun j ↦ physicalSlotAllowed hL g m r R C S u particle d (some j)) some
    (fun _ f ↦ f) (fun _ ↦ measurable_id) μ ν a ha hi z
  have hρ : (fun i:s ↦ Kernel.const Unit (ν i))=
      (fun i:s ↦ Kernel.const Unit (physicalSelectedOn hL g m t r R C S u particle labels v steps d i)) := by
    funext i
    rw [he i]
  dsimp only at H
  simp only [hρ] at H
  exact H

theorem physicalSharedOn_mass_oai {N K M G n : ℕ} [NeZero K] {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (m : ℕ) (t r R C S : ℝ) (ht : 0<t) (u : Time)
    (particle : J↪Fin N) (labels : Fin (n+1)↪J) (v : Fin (n+2)→(Fin 3→Fin K))
    (steps : Fin (n+1)→Fin 7)
    (hc : ∀k,projectPoint L (routeCellPeriod (v k.succ) (v k.castSucc) (steps k))=0)
    (d : PhysicalDatum N K M G L)
    (hhome : ∀k,datumHome hL d (particle (labels k))=v k.castSucc)
    (haccess : ∀k,datumAccessible hL g m t r R C S u (particle (labels k)) d)
    (hneigh : ∀k : Fin (n+1),torusDistance L (gridCenter L (v k.castSucc)) (gridCenter L (v k.succ))≤1)
    (hm : ∀w,(Finset.univ.filter (fun j ↦ datumHome hL d (particle j)=w)).card≤M)
    (hp : ∀j,IsProbabilityMeasure (datumIndividualReference hL g m r R C S t u (particle j) d))
    (q a : ℝ≥0∞) (ha : 0<a)
    (hq : ∀ j k, j ≠ k → ∀f : physicalSlotAllowed hL g m r R C S u particle d (some k),
      physicalCollisionReference hL g m t r R C S u particle d j
        {p | TrialCollision r (projectCurve L f.val) p.val}≤q)
    (hsmall : a+(4*(49^3*(M+1)):ℕ)*(routeDensityBound t*q)≤1) :
    physicalSharedOn hL g m t r R C S u particle labels v steps d univ=
      physicalOnPrimary hL g m t r R C S u particle (v (Fin.last (n+1))) d univ := by
  let X : Option J→Type := fun i ↦ physicalSlotAllowed hL g m r R C S u particle d i
  let σ := routePermutation labels
  let s := routeSlots labels
  let μ := physicalSlotOn hL g m t r R C S u particle (v (Fin.last (n+1))) d
  let anchor := fun j ↦ projectPoint L (anchorPoint (datumHome hL d (particle j)))
  let allowed := fun j ↦ physicalSlotAllowed hL g m r R C S u particle d (some j)
  have : ∀i,IsProbabilityMeasure (μ i) := physicalOn_probability hL g m t r R C S u particle _ d hp
  obtain ⟨κ,η,hκf,hηf,he,hr,hκb,hηb,hκm,hηm⟩ := physical_auxiliary_exists
    hL g m t r R C S ht u particle labels v steps hc d hhome haccess hp
  have : ∀i,IsFiniteKernel (κ i) := hκf
  have : ∀i,IsFiniteKernel (η i) := hηf
  let ν := fun i ↦ (μ i).compProd (κ i)
  have : ∀i,IsProbabilityMeasure (ν i) := fun i ↦ ⟨by
    rw [Measure.compProd_apply MeasurableSet.univ]
    simpa using hκm i⟩
  have hd := (physical_auxiliary_collision_bounds hL g m t r R C S ht u
    particle labels v steps hc d hhome haccess κ η he (fun i ↦ hr i)).1
  have hi := physical_forward_insertion hL g m t r R C S u particle labels v d hhome hneigh hm ν q a hd hq hsmall
  exact physicalSharedOn_mass_of hL g m t r R C S u particle labels v steps d hp ν he a ha hi

end HardSphere.Groups
end
end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.HardSphere.Groups.physicalSharedOn_mass_oai.{u_1} := @OAI.HardSphere.Groups.physicalSharedOn_mass_oai.{u_1}
