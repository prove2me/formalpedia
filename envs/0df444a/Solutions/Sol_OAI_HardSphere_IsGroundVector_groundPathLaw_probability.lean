-- Prove2me | solution 1 for OAI.HardSphere.IsGroundVector.groundPathLaw_probability
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T20:24:26.610105+00:00
-- url     : https://prove2.me/submissions/f6995c3e-8bba-4afb-91c3-b17c205f12ca

import Mathlib
import Definitions.Def_HardSphere
import Definitions.Def_OAIQ054H002
import Theorems.Thm_OAI_HardSphere_killedLaplace_graph

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

lemma level_at_zero (n : ℕ) (ω : Noise) : level n ω 0 = 0 := by
  simp [level, tentMap, tent_at_zero]

lemma path_at_zero (ω : Noise) : path ω 0 = 0 := by
  by_cases h : Summable (fun n ↦ level n ω)
  · simp only [path, ContinuousMap.add_apply, ContinuousMap.smul_apply, ContinuousMap.coe_mk,
      smul_eq_mul]
    change ω (.inl ()) * 0 + _ = 0
    rw [← ContinuousMap.tsum_apply h]
    simp [level_at_zero]
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
-- module Solutions.OAIQ054_HS.HardSphere_Bridges_Moment8
attribute [-instance] _root_.OAI.HardSphere.Bridge.exposedBridgeKernel_markov _root_.OAI.HardSphere.Bridge.exposedPeriodSingle_finite _root_.OAI.HardSphere.Bridge.exposedTrialKernel_markov _root_.OAI.HardSphere.Bridge.instBorelSpaceContinuousMapElemRealTimePoint _root_.OAI.HardSphere.Bridge.instIsProbabilityMeasureNoiseLaw _root_.OAI.HardSphere.Bridge.instMeasurableSpaceContinuousMapElemRealTimePoint _root_.OAI.HardSphere.Bridge.parameterBridgeKernel_markov _root_.OAI.HardSphere.Bridge.parameterIndividualReference_finite _root_.OAI.HardSphere.Bridge.parameterTrialKernel_markov _root_.OAI.HardSphere.Bridge.trialKernel_markov _root_.OAI.HardSphere.Groups.cellPathReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Wiener.instIsProbabilityMeasureContinuousMapElemRealTimeBridgeLaw _root_.OAI.HardSphere.configurationPathBorel _root_.OAI.HardSphere.coordinateBridge_probability _root_.OAI.HardSphere.coordinateWiener_probability
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
namespace HardSphere.Wiener

lemma moment8_ne_top : moment8 ≠ ∞ :=
  ENNReal.pow_ne_top (memLp_id_gaussianReal' (μ := 0) (v := 1) 8 (by norm_num)).2.ne

lemma coordinate_tail8 (i : Index) {a : ℝ} (ha : 0 < a) :
    law {ω | a ≤ |ω i|} ≤ (ENNReal.ofReal a)⁻¹ ^ (8 : ℕ) * moment8 := by
  have hm := memLp_id_gaussianReal' (μ := 0) (v := 1) 8 (by norm_num)
  have he : eLpNorm (fun ω : Noise ↦ ω i) 8 law =
      eLpNorm (id : ℝ → ℝ) 8 (gaussianReal 0 1) := by
    simpa only [Function.comp_def, id_eq] using
      (eLpNorm_comp_measurePreserving (p := 8) (g := (id : ℝ → ℝ))
        hm.aestronglyMeasurable (coordinate_preserving i))
  have ht := meas_ge_le_mul_pow_eLpNorm_enorm law (p := 8) (by norm_num) (by norm_num)
    (f := fun noise : Noise ↦ noise i)
    ((coordinate_preserving i).measurable.aestronglyMeasurable)
    (ε := ENNReal.ofReal a) (ne_of_gt (ENNReal.ofReal_pos.mpr ha)) (fun h => absurd h (by simp))
  have hs : {ω : Noise | ENNReal.ofReal a ≤ ‖ω i‖ₑ} = {ω | a ≤ |ω i|} := by
    ext ω
    simp only [Set.mem_ofPred_eq, ← ofReal_norm, Real.norm_eq_abs]
    exact ENNReal.ofReal_le_ofReal_iff (abs_nonneg _)
  simpa only [Function.comp_def, id_eq, ENNReal.toReal_ofNat, ← ENNReal.rpow_natCast,
    Nat.cast_ofNat, he, hs, moment8] using ht

lemma normMultiplier_pos : 0 < normMultiplier := by
  have h : 0 ≤ ∑' n : ℕ, amplitude n * (4/3:ℝ)^n :=
    tsum_nonneg fun n ↦ mul_nonneg (amplitude_nonneg n) (by positivity)
  unfold normMultiplier
  linarith

lemma norm_path_of_coordinate_bounds (ω : Noise) {B : ℝ} (hB : 0 ≤ B)
    (h0 : |ω (.inl ())| ≤ B)
    (h : ∀ n k, |ω (.inr ⟨n,k⟩)| ≤ B*(4/3:ℝ)^n) :
    ‖path ω‖ ≤ B*normMultiplier := by
  have hn : ‖(⟨fun t : Time ↦ t.val, continuous_subtype_val⟩ : C(Time,ℝ))‖ ≤ 1 := by
    apply (ContinuousMap.norm_le _ (by norm_num : (0:ℝ)≤1)).2
    intro t
    simpa only [ContinuousMap.coe_mk,Real.norm_eq_abs,abs_of_nonneg t.property.1] using t.property.2
  have ht : ‖∑' n, level n ω‖ ≤ B*(∑' n : ℕ, amplitude n*(4/3:ℝ)^n) := by
    apply tsum_of_norm_bounded (summable_level_bound.hasSum.mul_left B)
    intro n
    exact (norm_level_le n ω (mul_nonneg hB (by positivity)) (h n)).trans_eq (by ring)
  calc
    ‖path ω‖ ≤ ‖ω (.inl ()) • (⟨fun t : Time ↦ t.val, continuous_subtype_val⟩ : C(Time,ℝ))‖ + ‖∑' n, level n ω‖ := norm_add_le _ _
    _ ≤ B*1+B*(∑' n : ℕ, amplitude n*(4/3:ℝ)^n) := by
      apply add_le_add _ ht
      rw [norm_smul]
      exact mul_le_mul h0 hn (norm_nonneg _) hB
    _ = B*normMultiplier := by unfold normMultiplier; ring

lemma scaled_badLevel_bound (n : ℕ) {B : ℝ} (hB : 0 < B) :
    law {ω | ∃ k : Fin (2^n), B*(4/3:ℝ)^n ≤ |ω (.inr ⟨n,k⟩)|} ≤
      (ENNReal.ofReal B)⁻¹^8 * ((2:ℝ≥0∞)*(4/3)⁻¹^8)^n * moment8 := by
  have hu : {ω : Noise | ∃ k : Fin (2^n), B*(4/3:ℝ)^n ≤ |ω (.inr ⟨n,k⟩)|} =
      ⋃ k : Fin (2^n), {ω | B*(4/3:ℝ)^n ≤ |ω (.inr ⟨n,k⟩)|} := by ext ω; simp
  rw [hu]
  refine (measure_iUnion_fintype_le _ _).trans ?_
  calc
    _ ≤ ∑ _k : Fin (2^n), (ENNReal.ofReal (B*(4/3:ℝ)^n))⁻¹^8*moment8 :=
      Finset.sum_le_sum fun k _ ↦ coordinate_tail8 _ (by positivity)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
        Nat.cast_pow, Nat.cast_ofNat, ENNReal.ofReal_mul hB.le,
        ENNReal.ofReal_pow (by norm_num : (0:ℝ)≤4/3),
        ENNReal.ofReal_div_of_pos (by norm_num : (0:ℝ)<3), ENNReal.ofReal_ofNat]
      rw [ENNReal.mul_inv (Or.inl (by simpa using hB)) (Or.inl ENNReal.ofReal_ne_top),
        mul_pow, ENNReal.inv_pow, ← pow_mul, Nat.mul_comm n 8, pow_mul]
      simp only [mul_pow]
      ring

lemma norm_wiener_tail8 {B : ℝ} (hB : 0 < B) :
    wiener {w | B*normMultiplier < ‖w‖} ≤
      (ENNReal.ofReal B)⁻¹^8 *
        ((1+ (1-(2:ℝ≥0∞)*(4/3)⁻¹^8)⁻¹)*moment8) := by
  rw [wiener,Measure.map_apply measurable_path (measurableSet_lt measurable_const measurable_norm)]
  have hsub : path ⁻¹' {w | B*normMultiplier < ‖w‖} ⊆
      {ω | B≤|ω (.inl ())|} ∪
        ⋃ n : ℕ, {ω | ∃ k : Fin (2^n), B*(4/3:ℝ)^n ≤ |ω (.inr ⟨n,k⟩)|} := by
    intro ω hω
    by_contra hc
    have hc' := not_or.mp hc
    have h0 : |ω (.inl ())| ≤ B := (lt_of_not_ge hc'.1).le
    have hn : ∀ n k, |ω (.inr ⟨n,k⟩)| ≤ B*(4/3:ℝ)^n := by
      intro n k
      by_contra hh
      apply hc'.2
      exact Set.mem_iUnion.mpr ⟨n,⟨k,(lt_of_not_ge hh).le⟩⟩
    exact (not_lt_of_ge (norm_path_of_coordinate_bounds ω hB.le h0 hn)) hω
  calc
    _ ≤ law ({ω | B≤|ω (.inl ())|} ∪
        ⋃ n : ℕ, {ω | ∃ k : Fin (2^n), B*(4/3:ℝ)^n ≤ |ω (.inr ⟨n,k⟩)|}) := measure_mono hsub
    _ ≤ law {ω | B≤|ω (.inl ())|} +
        ∑' n : ℕ, law {ω | ∃ k : Fin (2^n), B*(4/3:ℝ)^n ≤ |ω (.inr ⟨n,k⟩)|} :=
      (measure_union_le _ _).trans (add_le_add_right (measure_iUnion_le _) _)
    _ ≤ (ENNReal.ofReal B)⁻¹^8*moment8 +
        ∑' n : ℕ, (ENNReal.ofReal B)⁻¹^8*((2:ℝ≥0∞)*(4/3)⁻¹^8)^n*moment8 := by
      exact add_le_add (coordinate_tail8 _ hB) (ENNReal.tsum_le_tsum fun n ↦ scaled_badLevel_bound n hB)
    _ = _ := by
      rw [ENNReal.tsum_mul_right,ENNReal.tsum_mul_left,ENNReal.tsum_geometric]
      ring

lemma norm_wiener_tail_constant_finite :
    (1+(1-(2:ℝ≥0∞)*(4/3)⁻¹^8)⁻¹)*moment8 ≠ ∞ := by
  apply ENNReal.mul_ne_top _ moment8_ne_top
  apply ENNReal.add_ne_top.mpr
  refine ⟨by simp,?_⟩
  rw [ENNReal.inv_ne_top]
  apply ne_of_gt
  apply tsub_pos_of_lt
  have he : (2:ℝ≥0∞)*(4/3)⁻¹^8 = ENNReal.ofReal ((2:ℝ)*(4/3)⁻¹^8) := by
    rw [ENNReal.ofReal_mul (by norm_num : (0:ℝ)≤2),
      ENNReal.ofReal_pow (by positivity),
      ENNReal.ofReal_inv_of_pos (by norm_num : (0:ℝ)<4/3),
      ENNReal.ofReal_div_of_pos (by norm_num : (0:ℝ)<3)]
    norm_num
  rw [he,ENNReal.ofReal_lt_one]
  norm_num

end HardSphere.Wiener

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

lemma wiener_projection_law {ι : Type*} [Fintype ι]
    (c : ι → ℝ) (t : ι → Time) :
    HasLaw (fun ω : C(Time,ℝ) ↦ ∑ i, c i * ω (t i))
      (gaussianReal 0 (Real.toNNReal (∑ i, ∑ j, c i*c j*min (t i : ℝ) (t j : ℝ)))) wiener := by
  have hm : Measurable (fun ω : C(Time,ℝ) ↦ ∑ i, c i * ω (t i)) :=
    (continuous_finsetSum _ fun i _ ↦ continuous_const.mul (continuous_eval_const (t i))).measurable
  refine ⟨hm.aemeasurable, ?_⟩
  rw [wiener, Measure.map_map hm measurable_path]
  exact (path_projection_law c t).map_eq

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
attribute [-instance] _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Rescaling.config_haar _root_.OAI.HardSphere.bridgeEndpointBase_finite _root_.OAI.HardSphere.configurationBorel _root_.OAI.HardSphere.configurationPathBorel _root_.OAI.HardSphere.configurationPathMeasurable _root_.OAI.HardSphere.coordinateBridge_probability _root_.OAI.HardSphere.coordinateWiener_probability _root_.OAI.HardSphere.endpointWeightedBase_sfinite _root_.OAI.HardSphere.freePathLaw_finite_deletion _root_.OAI.HardSphere.gaussianCoordinates_probability _root_.OAI.HardSphere.killedPathLaw_finite_deletion
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

lemma hilbertJet_inner {N : ℕ} {L : Length} (u v : HilbertJet N L) :
    inner ℂ u v = inner ℂ (hilbertJetEquiv N L u).1 (hilbertJetEquiv N L v).1 +
      ∑ p : Direction N, inner ℂ ((hilbertJetEquiv N L u).2 p) ((hilbertJetEquiv N L v).2 p) := by
  rw [PiLp.inner_apply,Fintype.sum_option]
  rfl

lemma scalarEmbedding_norm_le (N : ℕ) (L : Length) (a : ℝ) : ‖scalarEmbedding N L a‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro u
  simpa [scalarEmbedding] using PiLp.norm_apply_le (u : HilbertJet N L) none

lemma formResolvent_isPositive (N : ℕ) (L : Length) (a : ℝ) :
    (formResolvent N L a).IsPositive := by
  simpa [formResolvent] using
    ContinuousLinearMap.isPositive_adjoint_comp_self (scalarEmbedding N L a).adjoint

lemma formResolvent_norm_le_one (N : ℕ) (L : Length) (a : ℝ) :
    ‖formResolvent N L a‖ ≤ 1 := by
  have ha : ‖(scalarEmbedding N L a).adjoint‖ = ‖scalarEmbedding N L a‖ :=
    ContinuousLinearMap.adjoint.norm_map _
  have hadj : ‖(scalarEmbedding N L a).adjoint‖ ≤ 1 := by
    rw [ha]
    exact scalarEmbedding_norm_le N L a
  calc
    _ ≤ ‖scalarEmbedding N L a‖ * ‖(scalarEmbedding N L a).adjoint‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 1*1 := mul_le_mul (scalarEmbedding_norm_le N L a)
      hadj (ContinuousLinearMap.opNorm_nonneg _) zero_le_one
    _ = 1 := one_mul 1

lemma IsGroundVector.resolvent_eigenvector {N : ℕ} {L : Length} {a : ℝ}
    {u : Jet N L} (hu : IsGroundVector N L a u) :
    formResolvent N L a u.1 = ((1+(energy u:ℂ))⁻¹) • u.1 := by
  let ug : hilbertDomain N L a := ⟨(hilbertJetEquiv N L).symm u, by
    change hilbertJetEquiv N L ((hilbertJetEquiv N L).symm u) ∈ dirichletSubmodule N L a
    simpa using hu.1⟩
  have hE : 0 ≤ energy u := Finset.sum_nonneg fun _ _ ↦ sq_nonneg _
  have hne : 1+(energy u:ℂ) ≠ 0 := by
    have hreal : (1:ℝ)+energy u ≠ 0 := ne_of_gt (by linarith)
    exact_mod_cast hreal
  have heq : (scalarEmbedding N L a).adjoint u.1 = ((1+(energy u:ℂ))⁻¹) • ug := by
    apply ext_inner_right ℂ
    intro v
    rw [ContinuousLinearMap.adjoint_inner_left]
    rw [inner_smul_left ug v ((1+(energy u:ℂ))⁻¹)]
    have hv : hilbertJetEquiv N L (v : HilbertJet N L) ∈ dirichletDomain N L a := v.property
    have hg : inner ℂ ug v = (1+(energy u:ℂ))*inner ℂ u.1 (scalarEmbedding N L a v) := by
      change inner ℂ (ug : HilbertJet N L) (v : HilbertJet N L) = _
      rw [hilbertJet_inner]
      have hgu : hilbertJetEquiv N L (ug : HilbertJet N L) = u := by simp [ug]
      rw [hgu,hu.full_first_variation _ hv]
      change inner ℂ u.1 (scalarEmbedding N L a v) + (energy u:ℂ)*inner ℂ u.1 (scalarEmbedding N L a v) = _
      ring
    rw [hg]
    simp only [map_inv₀,map_add,map_one,Complex.conj_ofReal]
    rw [← mul_assoc,inv_mul_cancel₀ hne,one_mul]
  change scalarEmbedding N L a ((scalarEmbedding N L a).adjoint u.1) = _
  rw [heq,map_smul]
  congr 1

end HardSphere

end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_ConfigurationPath
attribute [-instance] _root_.OAI.HardSphere.Bridge.exposedBridgeKernel_markov _root_.OAI.HardSphere.Bridge.exposedPeriodSingle_finite _root_.OAI.HardSphere.Bridge.exposedTrialKernel_markov _root_.OAI.HardSphere.Bridge.instBorelSpaceContinuousMapElemRealTimePoint _root_.OAI.HardSphere.Bridge.instIsProbabilityMeasureNoiseLaw _root_.OAI.HardSphere.Bridge.instMeasurableSpaceContinuousMapElemRealTimePoint _root_.OAI.HardSphere.Bridge.parameterBridgeKernel_markov _root_.OAI.HardSphere.Bridge.parameterIndividualReference_finite _root_.OAI.HardSphere.Bridge.parameterTrialKernel_markov _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Bridge.trialKernel_markov _root_.OAI.HardSphere.Groups.cellPathReference_probability _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Rescaling.config_haar _root_.OAI.HardSphere.Wiener.instIsProbabilityMeasureContinuousMapElemRealTimeBridgeLaw _root_.OAI.HardSphere.bridgeEndpointBase_finite _root_.OAI.HardSphere.coordinateBridge_probability _root_.OAI.HardSphere.endpointWeightedBase_sfinite _root_.OAI.HardSphere.freePathLaw_finite_deletion _root_.OAI.HardSphere.killedPathLaw_finite_deletion
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

end L2Multiplier

namespace HardSphere
open Wiener
open scoped ComplexConjugate

lemma endpointPull_ae (N : ℕ) (L : Length) (t : ℝ) (s : Time) (f : ScalarL2 N L) :
    endpointPull N L t s f =ᵐ[freePathLaw N L t] fun ω ↦ f (ω s) :=
  Lp.coeFn_compMeasurePreserving f (freePathLaw_marginal N L t s)

lemma avoidanceMultiplier_ae (N : ℕ) (L : Length) (a t : ℝ) (f : FreePathL2 N L t) :
    avoidanceMultiplier N L a t f =ᵐ[freePathLaw N L t] (staysAllowed N L a).indicator f := by
  filter_upwards [L2Multiplier.coe_clm _ (avoidanceIndicator_memLp N L a t) f] with ω hω
  rw [avoidanceMultiplier, hω]
  by_cases h : ω ∈ staysAllowed N L a <;> simp [h]

lemma avoidanceMultiplier_contraction (N : ℕ) (L : Length) (a t : ℝ) (f : FreePathL2 N L t) :
    ‖avoidanceMultiplier N L a t f‖ ≤ ‖f‖ := by
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [avoidanceMultiplier_ae N L a t f] with ω hω
  rw [hω]
  by_cases h : ω ∈ staysAllowed N L a <;> simp [h]

lemma avoidanceMultiplier_norm_le (N : ℕ) (L : Length) (a t : ℝ) :
    ‖avoidanceMultiplier N L a t‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  simpa only [one_mul] using avoidanceMultiplier_contraction N L a t

lemma killedTransition_pairing (N : ℕ) (L : Length) (a t : ℝ) (f g : ScalarL2 N L) :
    inner ℂ f (killedTransition N L a t g) =
      ∫ ω, conj (f (ω 0)) * g (ω 1) ∂killedPathLaw N L a t := by
  rw [killedTransition,ContinuousLinearMap.comp_apply,ContinuousLinearMap.adjoint_inner_right]
  rw [L2.inner_def]
  change (∫ ω, inner ℂ (endpointPull N L t 0 f ω)
    (avoidanceMultiplier N L a t (endpointPull N L t 1 g) ω) ∂freePathLaw N L t) = _
  rw [killedPathLaw, ← integral_indicator (staysAllowed_open N L a).measurableSet]
  apply integral_congr_ae
  filter_upwards [endpointPull_ae N L t 0 f,endpointPull_ae N L t 1 g,
    avoidanceMultiplier_ae N L a t (endpointPull N L t 1 g)] with ω hf hg ha
  rw [hf,ha]
  by_cases h : ω ∈ staysAllowed N L a
  · simp only [Set.indicator_of_mem h,hg,RCLike.inner_apply,mul_comm]
  · simp only [Set.indicator_of_notMem h,inner_zero_right]

lemma killedTransition_norm_le (N : ℕ) (L : Length) (a t : ℝ) :
    ‖killedTransition N L a t‖ ≤ 1 := by
  unfold killedTransition
  calc
    _ ≤ ‖(endpointPull N L t 0).toContinuousLinearMap.adjoint‖ *
        (‖avoidanceMultiplier N L a t‖ * ‖(endpointPull N L t 1).toContinuousLinearMap‖) :=
      (ContinuousLinearMap.opNorm_comp_le _ _).trans
        (mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _))
    _ ≤ 1* (1*1) := by
      rw [ContinuousLinearMap.adjoint.norm_map]
      exact mul_le_mul (LinearIsometry.norm_toContinuousLinearMap_le _) (mul_le_mul
        (avoidanceMultiplier_norm_le N L a t) (LinearIsometry.norm_toContinuousLinearMap_le _)
        (norm_nonneg _) zero_le_one) (by positivity) zero_le_one
    _ = 1 := by norm_num

lemma killedTransition_apply_contraction (N : ℕ) (L : Length) (a t : ℝ) (g : ScalarL2 N L) :
    ‖killedTransition N L a t g‖ ≤ ‖g‖ := by
  simpa only [one_mul] using (ContinuousLinearMap.le_opNorm (killedTransition N L a t) g).trans
    (mul_le_mul_of_nonneg_right (killedTransition_norm_le N L a t) (norm_nonneg g))

end HardSphere

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

lemma staysAllowed_split (N : ℕ) (L : Length) (a : ℝ) (u : Time)
    (hu : 0<(u:ℝ)) (hu' : (u:ℝ)<1) (ω : ConfigurationPath N L) :
    ω∈staysAllowed N L a ↔
      configurationPrefix N L u ω ∈ staysAllowed N L a ∧
      configurationSuffix N L u ω ∈ staysAllowed N L a := by
  simp only [staysAllowed,Set.mem_ofPred_eq,Set.range_subset_iff]
  change (∀ v,ω v∈allowed N L a) ↔
    (∀ v,ω (prefixTime u v)∈allowed N L a) ∧ (∀ v,ω (suffixTime u v)∈allowed N L a)
  constructor
  · intro h
    exact ⟨fun v ↦ h _,fun v ↦ h _⟩
  · rintro ⟨h₁,h₂⟩ v
    by_cases hv : (v:ℝ)≤u
    · let z : Time := ⟨(v:ℝ)/(u:ℝ),div_nonneg v.property.1 hu.le,(div_le_one hu).mpr hv⟩
      have hz : prefixTime u z=v := by
        apply Subtype.ext
        change (u:ℝ)*((v:ℝ)/(u:ℝ))=(v:ℝ)
        field_simp
      simpa only [hz] using h₁ z
    · let z : Time := ⟨((v:ℝ)-(u:ℝ))/(1-(u:ℝ)),
          div_nonneg (sub_nonneg.mpr (le_of_not_ge hv)) (sub_pos.mpr hu').le,
          (div_le_one (sub_pos.mpr hu')).mpr (by linarith [v.property.2])⟩
      have hz : suffixTime u z=v := by
        apply Subtype.ext
        change (u:ℝ)+(1-(u:ℝ))*(((v:ℝ)-(u:ℝ))/(1-(u:ℝ)))=(v:ℝ)
        field_simp [ne_of_gt (sub_pos.mpr hu')]
        ring
      simpa only [hz] using h₂ z

end HardSphere

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

lemma reverseIncrements_preserving : MeasurePreserving reverseIncrements wiener wiener := by
  refine ⟨reverseIncrements.continuous.measurable, ?_⟩
  unfold wiener
  rw [Measure.map_map reverseIncrements.continuous.measurable measurable_path]
  exact reverseIncrements_law

end HardSphere.Wiener

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Fourier_ArgumentAdd
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
namespace HardSphere.FreeFourier

lemma gaussian_character (L : ℝ) (n : ℤ) (t : ℝ) (ht : 0 ≤ t) :
    (∫ x : ℝ, fourier n ((Real.sqrt (2*t) * x : ℝ) : AddCircle L)
      ∂gaussianReal 0 1) = (Real.exp (-t * (2*Real.pi*n/L)^2) : ℂ) := by
  have h := charFun_gaussianReal (μ := 0) (v := 1) ((2*Real.pi*n/L)*Real.sqrt (2*t))
  rw [charFun_apply_real] at h
  have he (x : ℝ) : fourier n ((Real.sqrt (2*t)*x : ℝ) : AddCircle L) =
      Complex.exp (((2*Real.pi*n/L)*Real.sqrt (2*t)*x : ℝ) * Complex.I) := by
    rw [fourier_coe_apply]
    push_cast
    congr 1
    ring
  simp_rw [he]
  simp only [Complex.ofReal_mul] at h ⊢
  rw [h, Complex.ofReal_exp]
  congr 1
  have hs := Real.sq_sqrt (show 0 ≤ 2*t by positivity)
  push_cast at hs ⊢
  simp only [mul_zero, zero_mul, one_mul, zero_sub]
  rw [mul_pow]
  norm_cast at hs
  have hs' : (Real.sqrt (2*t) : ℂ)^2 = 2*t := by exact_mod_cast hs
  rw [hs']
  ring
end HardSphere.FreeFourier

namespace HardSphere
open Wiener ProbabilityTheory
open scoped ComplexConjugate

lemma configurationCharacter_norm (N : ℕ) (L : Length) (k : Direction N → ℤ)
    (X : Configuration N L) : ‖configurationCharacter N L k X‖ = 1 := by
  simp only [configurationCharacter, ContinuousMap.coe_mk, norm_prod, fourier_apply,
    Circle.norm_coe, Finset.prod_const_one]

lemma wiener_endpoint_law : HasLaw (fun w : C(Time,ℝ) ↦ w 1) (gaussianReal 0 1) wiener := by
  simpa using wiener_projection_law (ι := Unit) (fun _ ↦ (1:ℝ)) (fun _ ↦ (1:Time))

lemma wiener_character (L : Length) (n : ℤ) (t : ℝ) (ht : 0 ≤ t) :
    (∫ w : C(Time,ℝ), fourier n ((Real.sqrt (2*t)*w 1 : ℝ) : AddCircle L.val) ∂wiener) =
      (Real.exp (-t*(2*Real.pi*n/L.val)^2) : ℂ) := by
  have hcont : Continuous (fun x : ℝ ↦ fourier n ((Real.sqrt (2*t)*x : ℝ) : AddCircle L.val)) := by
    fun_prop
  exact (wiener_endpoint_law.integral_comp hcont.aestronglyMeasurable).trans
    (FreeFourier.gaussian_character L.val n t ht)

lemma fourierEnergy_nonneg (N : ℕ) (L : Length) (k : Direction N → ℤ) :
    0 ≤ fourierEnergy N L k := Finset.sum_nonneg fun _ _ ↦ sq_nonneg _

lemma freeTrajectory_character_integral (N : ℕ) (L : Length) (k : Direction N → ℤ)
    (t : ℝ) (ht : 0 ≤ t) (X : Configuration N L) :
    (∫ w, configurationCharacter N L k (freeTrajectory N L t w X 1) ∂coordinateWiener N) =
      configurationCharacter N L k X * (Real.exp (-t * fourierEnergy N L k) : ℂ) := by
  have hpoint (w : CoordinatePaths N) :
      configurationCharacter N L k (freeTrajectory N L t w X 1) =
        configurationCharacter N L k X *
          ∏ p : Direction N, fourier (k p) ((Real.sqrt (2*t)*w p 1 : ℝ) : AddCircle L.val) := by
    simp only [configurationCharacter, freeTrajectory, ContinuousMap.coe_mk,
      FreeFourier.argument_add, Finset.prod_mul_distrib]
  simp_rw [hpoint]
  rw [integral_const_mul]
  congr 1
  rw [coordinateWiener, integral_fintype_prod_eq_prod
    (fun p (w : C(Time,ℝ)) ↦ fourier (k p) ((Real.sqrt (2*t)*w 1 : ℝ) : AddCircle L.val))]
  simp_rw [wiener_character L _ t ht]
  rw [← Complex.ofReal_prod, ← Real.exp_sum]
  congr 2
  simp only [fourierEnergy, Nat.cast_ofNat, Finset.mul_sum]

end HardSphere

namespace HardSphere
open scoped ComplexConjugate
open Submodule Algebra

lemma configurationCharacter_add (N : ℕ) (L : Length) (k l : Direction N → ℤ)
    (X : Configuration N L) :
    configurationCharacter N L (k+l) X =
      configurationCharacter N L k X * configurationCharacter N L l X := by
  simp only [configurationCharacter, Pi.add_apply, fourier_add, ContinuousMap.coe_mk,
    Finset.prod_mul_distrib]

lemma configurationCharacter_zero (N : ℕ) (L : Length) :
    configurationCharacter N L (0 : Direction N → ℤ) = 1 := by
  ext X
  simp only [configurationCharacter, Pi.zero_apply, fourier_zero, Finset.prod_const_one,
    ContinuousMap.coe_mk, ContinuousMap.one_apply]

lemma configurationCharacter_single (N : ℕ) (L : Length) (p : Direction N)
    (X : Configuration N L) :
    configurationCharacter N L (Pi.single p 1) X = fourier 1 (X p.1 p.2) := by
  classical
  change (∏ q : Direction N, fourier ((Pi.single p 1 : Direction N → ℤ) q) (X q.1 q.2)) = _
  rw [Finset.prod_eq_single p]
  · simp
  · intro q _ hqp
    simp only [Pi.single_eq_of_ne hqp, fourier_zero]
  · simp

lemma characterAlgebra_eq_span (N : ℕ) (L : Length) :
    (characterAlgebra N L).toSubalgebra.toSubmodule =
      span ℂ (range (configurationCharacter N L)) := by
  apply adjoin_eq_span_of_subset
  refine .trans (fun x ↦ Submonoid.closure_induction (fun _ ↦ id) ⟨0, ?_⟩ ?_) subset_span
  · exact configurationCharacter_zero N L
  · rintro _ _ _ _ ⟨k,rfl⟩ ⟨l,rfl⟩
    exact ⟨k+l,ContinuousMap.ext fun X ↦ configurationCharacter_add N L k l X⟩

lemma characterAlgebra_separates (N : ℕ) (L : Length) :
    (characterAlgebra N L).SeparatesPoints := by
  classical
  intro X Y hXY
  obtain ⟨i,hi⟩ := Function.ne_iff.mp hXY
  obtain ⟨j,hj⟩ := Function.ne_iff.mp hi
  refine ⟨_, ⟨configurationCharacter N L (Pi.single (i,j) 1),
    subset_adjoin ⟨Pi.single (i,j) 1,rfl⟩,rfl⟩, ?_⟩
  dsimp only
  rw [configurationCharacter_single, configurationCharacter_single, fourier_one, fourier_one]
  exact fun h ↦ hj (AddCircle.injective_toCircle L.property.ne' (Circle.coe_injective h))

lemma character_span_dense (N : ℕ) (L : Length) :
    (span ℂ (range (configurationCharacter N L))).topologicalClosure = ⊤ := by
  rw [← characterAlgebra_eq_span]
  exact congrArg (Subalgebra.toSubmodule ∘ StarSubalgebra.toSubalgebra)
    (ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints _
      (characterAlgebra_separates N L))

lemma characterL2_ae (N : ℕ) (L : Length) (k : Direction N → ℤ) :
    characterL2 N L k =ᵐ[volume] configurationCharacter N L k :=
  ContinuousMap.coeFn_toLp volume _

lemma characterL2_span_dense (N : ℕ) (L : Length) :
    (span ℂ (range (characterL2 N L))).topologicalClosure = ⊤ := by
  convert (ContinuousMap.toLp_denseRange ℂ (volume : Measure (Configuration N L)) ℂ
    (show (2:ℝ≥0∞) ≠ ∞ by norm_num)).topologicalClosure_map_submodule
      (character_span_dense N L) using 1
  all_goals try with_reducible_and_instances rfl
  rw [map_span]
  unfold characterL2
  rw [range_comp']
  rfl

end HardSphere

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Operators_FreeTransition
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
open Wiener ProbabilityTheory
open scoped ComplexConjugate

lemma wiener_initial_zero : ∀ᵐ w : C(Time,ℝ) ∂wiener, w 0 = 0 := by
  rw [wiener, ae_map_iff measurable_path.aemeasurable
    (isClosed_eq (continuous_eval_const (0:Time)) continuous_const).measurableSet]
  exact Filter.Eventually.of_forall path_at_zero

lemma coordinateWiener_initial_zero (N : ℕ) :
    ∀ᵐ w ∂coordinateWiener N, ∀ p, w p 0 = 0 := by
  apply ae_all_iff.mpr
  intro p
  exact (measurePreserving_eval (fun _ : Direction N ↦ wiener) p).quasiMeasurePreserving.ae wiener_initial_zero

lemma freeTrajectory_initial_ae (N : ℕ) (L : Length) (t : ℝ) :
    ∀ᵐ w ∂coordinateWiener N, ∀ X, freeTrajectory N L t w X 0 = X := by
  filter_upwards [coordinateWiener_initial_zero N] with w hw X
  ext i j
  simp only [freeTrajectory, ContinuousMap.coe_mk, hw (i,j), mul_zero,
    QuotientAddGroup.mk_zero, add_zero]

lemma freeTransition_pairing (N : ℕ) (L : Length) (t : ℝ) (f g : ScalarL2 N L) :
    inner ℂ f (freeTransition N L t g) =
      ∫ ω, conj (f (ω 0)) * g (ω 1) ∂freePathLaw N L t := by
  rw [freeTransition, ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right,
    L2.inner_def]
  apply integral_congr_ae
  filter_upwards [endpointPull_ae N L t 0 f, endpointPull_ae N L t 1 g] with ω hf hg
  change inner ℂ ((endpointPull N L t 0) f ω) ((endpointPull N L t 1) g ω) = _
  rw [hf,hg,RCLike.inner_apply,mul_comm]

lemma freeTransition_continuous_pairing (N : ℕ) (L : Length) (t : ℝ)
    (f g : C(Configuration N L,ℂ)) :
    inner ℂ (ContinuousMap.toLp 2 volume ℂ f)
      (freeTransition N L t (ContinuousMap.toLp 2 volume ℂ g)) =
      ∫ ω, conj (f (ω 0)) * g (ω 1) ∂freePathLaw N L t := by
  rw [freeTransition_pairing]
  apply integral_congr_ae
  filter_upwards [(freePathLaw_marginal N L t 0).quasiMeasurePreserving.ae (ContinuousMap.coeFn_toLp (𝕜 := ℂ) (p := 2) volume f),
    (freePathLaw_marginal N L t 1).quasiMeasurePreserving.ae (ContinuousMap.coeFn_toLp (𝕜 := ℂ) (p := 2) volume g)] with ω hf hg
  rw [hf,hg]

lemma integrable_free_character (N : ℕ) (L : Length) (t : ℝ)
    (f : C(Configuration N L,ℂ)) (k : Direction N → ℤ) :
    Integrable (fun p : CoordinatePaths N × Configuration N L ↦
      conj (f p.2) * configurationCharacter N L k (freeTrajectory N L t p.1 p.2 1))
      ((coordinateWiener N).prod volume) := by
  have hc : Continuous (fun p : CoordinatePaths N × Configuration N L ↦
      conj (f p.2) * configurationCharacter N L k (freeTrajectory N L t p.1 p.2 1)) := by
    exact (f.continuous.comp continuous_snd).star.mul
      ((configurationCharacter N L k).continuous.comp
        ((freeTrajectory_continuous N L t).eval continuous_const))
  refine (integrable_const ‖f‖).mono' hc.aestronglyMeasurable ?_
  exact Filter.Eventually.of_forall fun p ↦ by
    rw [norm_mul, RCLike.norm_conj, configurationCharacter_norm, mul_one]
    exact f.norm_coe_le_norm p.2

lemma freeTransition_character_pairing (N : ℕ) (L : Length) (t : ℝ) (ht : 0 ≤ t)
    (f : C(Configuration N L,ℂ)) (k : Direction N → ℤ) :
    inner ℂ (ContinuousMap.toLp 2 volume ℂ f) (freeTransition N L t (characterL2 N L k)) =
      (Real.exp (-t * fourierEnergy N L k) : ℂ) *
        inner ℂ (ContinuousMap.toLp 2 volume ℂ f) (characterL2 N L k) := by
  change inner ℂ _ (freeTransition N L t (ContinuousMap.toLp 2 volume ℂ _)) = _
  rw [freeTransition_continuous_pairing, freePathLaw]
  have hc : Continuous (fun ω : ConfigurationPath N L ↦
      conj (f (ω 0)) * configurationCharacter N L k (ω 1)) := by fun_prop
  rw [integral_map (freeTrajectory_continuous N L t).measurable.aemeasurable
    hc.aestronglyMeasurable]
  have hzero : (fun p : CoordinatePaths N × Configuration N L ↦
      conj (f (freeTrajectory N L t p.1 p.2 0)) *
        configurationCharacter N L k (freeTrajectory N L t p.1 p.2 1)) =ᵐ[
        (coordinateWiener N).prod volume]
      (fun p ↦ conj (f p.2) * configurationCharacter N L k (freeTrajectory N L t p.1 p.2 1)) := by
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae (freeTrajectory_initial_ae N L t)] with p hp
    rw [hp]
  rw [integral_congr_ae hzero, integral_prod_symm _ (integrable_free_character N L t f k)]
  simp_rw [integral_const_mul, freeTrajectory_character_integral N L k t ht]
  rw [show (∫ X, conj (f X) * (configurationCharacter N L k X *
      (Real.exp (-t*fourierEnergy N L k) : ℂ))) =
      (Real.exp (-t*fourierEnergy N L k) : ℂ) *
        ∫ X, conj (f X) * configurationCharacter N L k X by
    rw [← integral_const_mul]; congr 1; ext X; ring]
  congr 1
  rw [characterL2, ContinuousMap.inner_toLp]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun X ↦ mul_comm _ _

lemma freeTransition_character (N : ℕ) (L : Length) (t : ℝ) (ht : 0 ≤ t)
    (k : Direction N → ℤ) :
    freeTransition N L t (characterL2 N L k) =
      (Real.exp (-t * fourierEnergy N L k) : ℂ) • characterL2 N L k := by
  apply ext_inner_left ℂ
  intro f
  have hd := ContinuousMap.toLp_denseRange ℂ (volume : Measure (Configuration N L)) ℂ
    (show (2:ℝ≥0∞) ≠ ∞ by norm_num)
  have hc : IsClosed {f : ScalarL2 N L |
      inner ℂ f (freeTransition N L t (characterL2 N L k)) =
        inner ℂ f ((Real.exp (-t * fourierEnergy N L k) : ℂ) • characterL2 N L k)} :=
    isClosed_eq (continuous_id.inner continuous_const) (continuous_id.inner continuous_const)
  have hz : ∀ f : C(Configuration N L,ℂ),
      inner ℂ (ContinuousMap.toLp 2 volume ℂ f) (freeTransition N L t (characterL2 N L k)) =
        inner ℂ (ContinuousMap.toLp 2 volume ℂ f)
          ((Real.exp (-t * fourierEnergy N L k) : ℂ) • characterL2 N L k) := by
    intro f
    rw [freeTransition_character_pairing N L t ht, inner_smul_right]
  exact (hc.closure_subset_iff.mpr (Set.range_subset_iff.mpr hz)) (hd f)

end HardSphere

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_KilledObservable
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
open Wiener
open scoped ComplexConjugate

lemma integrable_killedAverage_pairing (N : ℕ) (L : Length) (a t : ℝ)
    (f : C(Configuration N L,ℂ)) {g : Configuration N L → ℂ} (hg : Measurable g)
    {C : ℝ} (hC : 0≤C) (hgC : ∀ X, ‖g X‖≤C) :
    Integrable (fun p : CoordinatePaths N × Configuration N L ↦
      conj (f p.2) * killedObservable N L a g (freeTrajectory N L t p.1 p.2))
      ((coordinateWiener N).prod volume) := by
  refine (integrable_const (‖f‖*C)).mono' ?_ ?_
  · exact (((f.continuous.comp continuous_snd).star.measurable).mul
      ((killedObservable_measurable N L a hg).comp
        (freeTrajectory_continuous N L t).measurable)).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun p ↦ by
      rw [norm_mul,RCLike.norm_conj]
      exact mul_le_mul (f.norm_coe_le_norm p.2)
        (killedObservable_bound N L a hC hgC _) (norm_nonneg _) (norm_nonneg _)

lemma killedTransition_bounded_pairing (N : ℕ) (L : Length) (a t : ℝ)
    (f : C(Configuration N L,ℂ)) {g : Configuration N L → ℂ} (hg : Measurable g)
    (hgLp : MemLp g 2 (volume : Measure (Configuration N L)))
    {C : ℝ} (hC : 0≤C) (hgC : ∀ X, ‖g X‖≤C) :
    inner ℂ (ContinuousMap.toLp 2 volume ℂ f) (killedTransition N L a t (hgLp.toLp g)) =
      ∫ X, conj (f X) * killedAverage N L a t g X := by
  rw [killedTransition_pairing,killedPathLaw,← integral_indicator (staysAllowed_open N L a).measurableSet]
  have he : (staysAllowed N L a).indicator (fun ω : ConfigurationPath N L ↦
      conj (ContinuousMap.toLp 2 volume ℂ f (ω 0)) * hgLp.toLp g (ω 1)) =ᵐ[freePathLaw N L t]
      (fun ω ↦ conj (f (ω 0)) * killedObservable N L a g ω) := by
    filter_upwards [(freePathLaw_marginal N L t 0).quasiMeasurePreserving.ae
        (ContinuousMap.coeFn_toLp (𝕜 := ℂ) (p := 2) volume f),
      (freePathLaw_marginal N L t 1).quasiMeasurePreserving.ae hgLp.coeFn_toLp] with ω hf hg'
    by_cases ha : ω∈staysAllowed N L a
    · simp only [Set.indicator_of_mem ha,killedObservable,hf,hg']
    · simp only [Set.indicator_of_notMem ha,killedObservable,mul_zero]
  rw [integral_congr_ae he,freePathLaw]
  have hm : Measurable (fun ω : ConfigurationPath N L ↦
      conj (f (ω 0)) * killedObservable N L a g ω) := by
    exact (f.continuous.comp (continuous_eval_const (0:Time))).star.measurable.mul
      (killedObservable_measurable N L a hg)
  rw [integral_map (freeTrajectory_continuous N L t).measurable.aemeasurable hm.aestronglyMeasurable]
  have hzero : (fun p : CoordinatePaths N × Configuration N L ↦
      conj (f (freeTrajectory N L t p.1 p.2 0)) * killedObservable N L a g (freeTrajectory N L t p.1 p.2)) =ᵐ[
        (coordinateWiener N).prod volume]
      (fun p ↦ conj (f p.2) * killedObservable N L a g (freeTrajectory N L t p.1 p.2)) := by
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae (freeTrajectory_initial_ae N L t)] with p hp
    rw [hp]
  rw [integral_congr_ae hzero,integral_prod_symm _ (integrable_killedAverage_pairing N L a t f hg hC hgC)]
  simp_rw [integral_const_mul]
  rfl

lemma killedTransition_bounded (N : ℕ) (L : Length) (a t : ℝ)
    {g : Configuration N L → ℂ} (hg : Measurable g)
    (hgLp : MemLp g 2 (volume : Measure (Configuration N L)))
    {C : ℝ} (hC : 0≤C) (hgC : ∀ X, ‖g X‖≤C) :
    killedTransition N L a t (hgLp.toLp g) =
      (killedAverage_memLp N L a t hg hC hgC).toLp (killedAverage N L a t g) := by
  apply ext_inner_left ℂ
  intro f
  have hd := ContinuousMap.toLp_denseRange ℂ (volume : Measure (Configuration N L)) ℂ
    (show (2:ℝ≥0∞) ≠ ∞ by norm_num)
  have hc : IsClosed {f : ScalarL2 N L |
      inner ℂ f (killedTransition N L a t (hgLp.toLp g)) =
        inner ℂ f ((killedAverage_memLp N L a t hg hC hgC).toLp (killedAverage N L a t g))} :=
    isClosed_eq (continuous_id.inner continuous_const) (continuous_id.inner continuous_const)
  apply hc.closure_subset_iff.mpr ?_ (hd f)
  rintro _ ⟨f,rfl⟩
  change inner ℂ _ _ = inner ℂ _ _
  rw [killedTransition_bounded_pairing N L a t f hg hgLp hC hgC,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [ContinuousMap.coeFn_toLp (𝕜 := ℂ) (p := 2) volume f,
    (killedAverage_memLp N L a t hg hC hgC).coeFn_toLp] with X hf hX
  rw [RCLike.inner_apply,hf,hX,mul_comm]

lemma splitObservable_measurable (N : ℕ) (L : Length) (a : ℝ)
    {g : Configuration N L → ℂ} (hg : Measurable g) :
    Measurable (splitObservable N L a g) := by
  exact Measurable.ite ((staysAllowed_open N L a).measurableSet.preimage measurable_fst)
    ((killedObservable_measurable N L a hg).comp measurable_snd) measurable_const

lemma splitObservable_bound (N : ℕ) (L : Length) (a : ℝ)
    {g : Configuration N L → ℂ} {C : ℝ} (hC : 0≤C) (hgC : ∀ X, ‖g X‖≤C)
    (p : ConfigurationPath N L × ConfigurationPath N L) :
    ‖splitObservable N L a g p‖≤C := by
  by_cases h : p.1∈staysAllowed N L a
  · simpa only [splitObservable,ite_eq_left h] using killedObservable_bound N L a hC hgC p.2
  · simpa only [splitObservable,ite_eq_right h,norm_zero] using hC

lemma killedObservable_split (N : ℕ) (L : Length) (a : ℝ)
    (g : Configuration N L → ℂ) (u : Time) (hu : 0<(u:ℝ)) (hu' : (u:ℝ)<1)
    (ω : ConfigurationPath N L) :
    killedObservable N L a g ω = splitObservable N L a g
      (configurationPrefix N L u ω,configurationSuffix N L u ω) := by
  have he := staysAllowed_split N L a u hu hu' ω
  have hend : configurationSuffix N L u ω 1=ω 1 := by
    simp only [configurationSuffix,ContinuousMap.comp_apply,suffixTime_one]
  by_cases hp : configurationPrefix N L u ω∈staysAllowed N L a
  · by_cases hq : configurationSuffix N L u ω∈staysAllowed N L a
    · simp [killedObservable,splitObservable,hp,hq,he.mpr ⟨hp,hq⟩,hend]
    · have h : ω∉staysAllowed N L a := fun h ↦ hq (he.mp h).2
      simp [killedObservable,splitObservable,h,hp,hq]
  · have h : ω∉staysAllowed N L a := fun h ↦ hp (he.mp h).1
    simp [killedObservable,splitObservable,h,hp]

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

lemma killedAverage_add (N : ℕ) (L : Length) (a s t : ℝ) (hs : 0 < s) (ht : 0<t)
    {g : Configuration N L → ℂ} (hg : Measurable g) {C : ℝ}
    (hC : 0≤C) (hgC : ∀ X, ‖g X‖≤C) (X : Configuration N L) :
    killedAverage N L a (s+t) g X =
      killedAverage N L a s (killedAverage N L a t g) X := by
  let F : CoordinatePaths N × CoordinatePaths N → ℂ := fun p ↦
    splitObservable N L a g (freeTrajectory N L s p.1 X,
      freeTrajectory N L t p.2 (freeTrajectory N L s p.1 X 1))
  have hm : Measurable F := (splitObservable_measurable N L a hg).comp
    (split_fixedTrajectory_measurable N L s t X)
  have hb : ∀ p, ‖F p‖≤C := fun p ↦ splitObservable_bound N L a hC hgC _
  have hi : Integrable F ((coordinateWiener N).prod (coordinateWiener N)) :=
    (integrable_const C).mono' hm.aestronglyMeasurable (Filter.Eventually.of_forall hb)
  have hsplit := coordinateSplit_preserving N (splitTime s t hs ht)
    (splitTime_pos s t hs ht) (splitTime_lt_one s t hs ht)
  calc
    _ = ∫ w, F (fun p ↦ normalizedPrefix (splitTime s t hs ht) (w p),
          fun p ↦ normalizedSuffix (splitTime s t hs ht) (w p)) ∂coordinateWiener N := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun w ↦ by
        dsimp only []
        rw [killedObservable_split N L a g (splitTime s t hs ht)
          (splitTime_pos s t hs ht) (splitTime_lt_one s t hs ht),split_fixedTrajectory]
    _ = ∫ p, F p ∂(coordinateWiener N).prod (coordinateWiener N) := by
      rw [← hsplit.map_eq,integral_map hsplit.measurable.aemeasurable hm.aestronglyMeasurable]
    _ = ∫ w, ∫ w', F (w,w') ∂coordinateWiener N ∂coordinateWiener N := integral_prod _ hi
    _ = _ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun w ↦ by
        change (∫ w', splitObservable N L a g
          (freeTrajectory N L s w X,freeTrajectory N L t w' (freeTrajectory N L s w X 1))
            ∂coordinateWiener N) =
          killedObservable N L a (killedAverage N L a t g) (freeTrajectory N L s w X)
        by_cases h : freeTrajectory N L s w X∈staysAllowed N L a
        · simp only [splitObservable,ite_eq_left h,killedObservable,Set.indicator_of_mem h]
          rfl
        · simp only [splitObservable,ite_eq_right h,killedObservable,Set.indicator_of_notMem h,integral_zero]

end HardSphere

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Bridges_WienerStart
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
open Wiener

lemma wiener_start_zero : ∀ᵐ w ∂wiener, w (0:Time)=0 := by
  rw [wiener, ae_map_iff measurable_path.aemeasurable
    ((isClosed_eq (continuous_eval_const (0:Time)) continuous_const).measurableSet)]
  exact Eventually.of_forall path_at_zero

lemma coordinateWiener_start_zero (N : ℕ) :
    ∀ᵐ w ∂coordinateWiener N, ∀ p, w p (0:Time)=0 := by
  rw [ae_all_iff]
  intro p
  exact (measurePreserving_eval (fun _ : Direction N ↦ wiener) p).quasiMeasurePreserving.ae wiener_start_zero

lemma freeTrajectory_time_continuous (N : ℕ) (L : Length)
    (w : CoordinatePaths N) (X : Configuration N L) :
    Continuous (fun t : ℝ ↦ freeTrajectory N L t w X) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  unfold Function.uncurry
  change Continuous (fun p : ℝ × Time ↦ fun i j ↦
    X i j + ((Real.sqrt (2*p.1)*w (i,j) p.2 : ℝ) : AddCircle L.val))
  fun_prop

lemma freeTrajectory_start (N : ℕ) (L : Length) (t : ℝ)
    {w : CoordinatePaths N} (hw : ∀ p, w p (0:Time)=0) (X : Configuration N L) :
    freeTrajectory N L t w X 0=X := by
  ext i j
  simp [freeTrajectory,hw]

lemma freeTrajectory_allowed_eventually (N : ℕ) (L : Length) (a : ℝ)
    (w : CoordinatePaths N) {X : Configuration N L} (hX : X∈allowed N L a) :
    ∀ᶠ t : ℝ in 𝓝 0, freeTrajectory N L t w X∈staysAllowed N L a := by
  have hc := (freeTrajectory_time_continuous N L w X).continuousAt (x := 0)
  apply hc.preimage_mem_nhds
  apply (staysAllowed_open N L a).mem_nhds
  rw [freeTrajectory_zero]
  rintro _ ⟨t,rfl⟩
  exact hX

lemma killedObservable_tendsto_zero (N : ℕ) (L : Length) (a : ℝ)
    (g : C(Configuration N L,ℂ)) {w : CoordinatePaths N}
    (hw : ∀ p, w p (0:Time)=0) (X : Configuration N L) :
    Tendsto (fun t : ℝ ↦ killedObservable N L a g (freeTrajectory N L t w X))
      (𝓝 0) (𝓝 ((allowed N L a).indicator g X)) := by
  by_cases hX : X∈allowed N L a
  · rw [Set.indicator_of_mem hX]
    have ht := (g.continuous.comp ((continuous_eval_const (1:Time)).comp
      (freeTrajectory_time_continuous N L w X))).tendsto (0:ℝ)
    simp only [Function.comp_def, freeTrajectory_zero, ContinuousMap.const_apply] at ht
    apply ht.congr'
    filter_upwards [freeTrajectory_allowed_eventually N L a w hX] with t ht
    simp only [killedObservable,Set.indicator_of_mem ht]
  · rw [Set.indicator_of_notMem hX]
    convert (tendsto_const_nhds : Tendsto (fun _ : ℝ ↦ (0:ℂ)) (𝓝 0) (𝓝 0)) using 1
    all_goals try with_reducible_and_instances rfl
    funext t
    apply Set.indicator_of_notMem
    intro h
    exact hX ((freeTrajectory_start N L t hw X) ▸ h (Set.mem_range_self 0))

lemma killedAverage_tendsto_zero (N : ℕ) (L : Length) (a : ℝ)
    (g : C(Configuration N L,ℂ)) (X : Configuration N L) :
    Tendsto (fun t : ℝ ↦ killedAverage N L a t g X)
      (𝓝 0) (𝓝 ((allowed N L a).indicator g X)) := by
  have h := tendsto_integral_filter_of_dominated_convergence (fun _ ↦ ‖g‖)
    (μ := coordinateWiener N)
    (F := fun t w ↦ killedObservable N L a g (freeTrajectory N L t w X))
    (f := fun _ ↦ (allowed N L a).indicator g X)
    (Eventually.of_forall fun t ↦ ((killedObservable_measurable N L a g.continuous.measurable).comp
      ((freeTrajectory_continuous N L t).comp (continuous_id.prodMk continuous_const)).measurable).aestronglyMeasurable)
    (Eventually.of_forall fun _ ↦ Eventually.of_forall fun _ ↦
      killedObservable_bound N L a (norm_nonneg g) g.norm_coe_le_norm _)
    (integrable_const _)
    ((coordinateWiener_start_zero N).mono fun w hw ↦ killedObservable_tendsto_zero N L a g hw X)
  simpa only [killedAverage,integral_const,measureReal_def,measure_univ,ENNReal.toReal_one,one_smul] using h

end HardSphere

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Comparison_LaplaceIntegrand
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
namespace HardSphere
open MeasureTheory Set Filter
open scoped Topology
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

lemma semigroup_increment_bound (K : ℝ → E→L[ℂ] E)
    (hadd : ∀ s t, 0 ≤ s → 0 ≤ t → K (s+t)=(K s).comp (K t))
    (hnorm : ∀ t, 0 ≤ t → ∀ f, ‖K t f‖≤‖f‖)
    (f : E) {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    ‖K t f-K s f‖≤‖K |t-s| f-K 0 f‖ := by
  have step : ∀ {u v : ℝ}, 0 ≤ u → u ≤ v →
      ‖K v f-K u f‖≤‖K (v-u) f-K 0 f‖ := by
    intro u v hu huv
    have hv : K v=(K u).comp (K (v-u)) := by
      convert hadd u (v-u) hu (sub_nonneg.mpr huv) using 1
      all_goals try with_reducible_and_instances rfl
      congr 1
      ring
    have hz : (K u).comp (K 0)=K u := by simpa using (hadd u 0 hu (le_refl 0)).symm
    have hze := congrArg (fun A : E→L[ℂ] E ↦ A f) hz
    change K u (K 0 f)=K u f at hze
    rw [hv,ContinuousLinearMap.comp_apply,← hze,← map_sub]
    exact hnorm u hu _
  rcases le_total s t with hst | hts
  · simpa only [abs_of_nonneg (sub_nonneg.mpr hst)] using step hs hst
  · rw [norm_sub_rev,abs_sub_comm,abs_of_nonneg (sub_nonneg.mpr hts)]
    exact step ht hts

lemma semigroup_continuousOn (K : ℝ → E→L[ℂ] E)
    (hadd : ∀ s t, 0 ≤ s → 0 ≤ t → K (s+t)=(K s).comp (K t))
    (hnorm : ∀ t, 0 ≤ t → ∀ f, ‖K t f‖≤‖f‖)
    (hzero : ∀ f, Tendsto (fun t ↦ K t f) (𝓝 0) (𝓝 (K 0 f))) (f : E) :
    ContinuousOn (fun t ↦ K t f) (Ici 0) := by
  intro t ht
  apply Metric.continuousWithinAt_iff.mpr
  intro ε hε
  obtain ⟨δ,hδ,hd⟩ := Metric.tendsto_nhds_nhds.mp (hzero f) ε hε
  refine ⟨δ,hδ,fun s hs hst ↦ ?_⟩
  rw [dist_eq_norm]
  apply lt_of_le_of_lt (semigroup_increment_bound K hadd hnorm f ht hs)
  rw [← dist_eq_norm]
  apply hd
  simpa only [Real.dist_eq,sub_zero,abs_abs] using hst

lemma semigroup_clamped_continuous (K : ℝ → E→L[ℂ] E)
    (hadd : ∀ s t, 0 ≤ s → 0 ≤ t → K (s+t)=(K s).comp (K t))
    (hnorm : ∀ t, 0 ≤ t → ∀ f, ‖K t f‖≤‖f‖)
    (hzero : ∀ f, Tendsto (fun t ↦ K t f) (𝓝 0) (𝓝 (K 0 f))) (f : E) :
    Continuous (fun t : ℝ ↦ K (max 0 t) f) :=
  (semigroup_continuousOn K hadd hnorm hzero f).comp_continuous
    (continuous_const.max continuous_id) (fun _ ↦ show max 0 _ ∈ Ici 0 from le_max_left (0:ℝ) _)

lemma laplaceIntegrand_integrable (K : ℝ → E→L[ℂ] E)
    (hc : ∀ f, Continuous (fun t : ℝ ↦ K (max 0 t) f))
    (hnorm : ∀ t, 0 ≤ t → ∀ f, ‖K t f‖≤‖f‖) (f : E) (a : ℝ) :
    IntegrableOn (laplaceIntegrand K f) (Ioi a) := by
  apply ((integrableOn_exp_neg_Ioi a).mul_const ‖f‖).mono'
    (((Real.continuous_exp.comp continuous_neg).smul (hc f)).aestronglyMeasurable)
  exact Eventually.of_forall (fun t ↦ by
    change ‖Real.exp (-t) • K (max 0 t) f‖≤_
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
    exact mul_le_mul_of_nonneg_left (hnorm _ (le_max_left _ _) f) (Real.exp_nonneg _))

lemma integral_Ioi_add (F : ℝ → E) (a h : ℝ) :
    (∫ t in Ioi a, F (t+h))=∫ t in Ioi (a+h), F t := by
  have hm := (measurePreserving_add_right (volume : Measure ℝ) h).restrict_preimage
    (measurableSet_Ioi (a := a+h))
  have hs : (fun t : ℝ ↦ t+h) ⁻¹' Ioi (a+h)=Ioi a := by ext t; simp
  rw [hs] at hm
  exact hm.integral_comp (Homeomorph.addRight h).measurableEmbedding F

variable [CompleteSpace E]

lemma semigroupLaplace_shift (K : ℝ → E→L[ℂ] E)
    (hadd : ∀ s t, 0 ≤ s → 0 ≤ t → K (s+t)=(K s).comp (K t))
    (hc : ∀ f, Continuous (fun t : ℝ ↦ K (max 0 t) f))
    (hnorm : ∀ t, 0 ≤ t → ∀ f, ‖K t f‖≤‖f‖) (f : E) {h : ℝ} (hh : 0 ≤ h) :
    K h (semigroupLaplace K f)=Real.exp h •
      (semigroupLaplace K f-∫ s in (0:ℝ)..h, laplaceIntegrand K f s) := by
  have hi := laplaceIntegrand_integrable K hc hnorm f 0
  have he : K h (semigroupLaplace K f)=
      Real.exp h • ∫ s in Ioi (0:ℝ), laplaceIntegrand K f (s+h) := by
    rw [semigroupLaplace,← (K h).integral_comp_comm hi,← integral_smul]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro s hs
    have hs0 : 0 ≤ s := le_of_lt hs
    have hsh : 0 ≤ s+h := add_nonneg hs0 hh
    dsimp only [laplaceIntegrand]
    rw [max_eq_right hs0,max_eq_right hsh,(K h).map_smul_of_tower,
      show s+h=h+s from add_comm s h,hadd h s hh hs0,ContinuousLinearMap.comp_apply,smul_smul]
    congr 1
    rw [← Real.exp_add]
    congr 1
    ring
  rw [he,integral_Ioi_add,zero_add]
  congr 1
  have hsplit := intervalIntegral.integral_interval_add_Ioi hi
    (laplaceIntegrand_integrable K hc hnorm f h)
  exact eq_sub_of_add_eq' hsplit

lemma semigroupLaplace_project (K : ℝ → E→L[ℂ] E)
    (hadd : ∀ s t, 0 ≤ s → 0 ≤ t → K (s+t)=(K s).comp (K t))
    (hc : ∀ f, Continuous (fun t : ℝ ↦ K (max 0 t) f))
    (hnorm : ∀ t, 0 ≤ t → ∀ f, ‖K t f‖≤‖f‖) (f : E) :
    K 0 (semigroupLaplace K f)=semigroupLaplace K f := by
  simpa using semigroupLaplace_shift K hadd hc hnorm f (le_refl 0)

lemma semigroupLaplace_difference_tendsto (K : ℝ → E→L[ℂ] E)
    (hadd : ∀ s t, 0 ≤ s → 0 ≤ t → K (s+t)=(K s).comp (K t))
    (hc : ∀ f, Continuous (fun t : ℝ ↦ K (max 0 t) f))
    (hnorm : ∀ t, 0 ≤ t → ∀ f, ‖K t f‖≤‖f‖) (f : E) :
    Tendsto (fun h : ℝ ↦ h⁻¹ • (semigroupLaplace K f-K h (semigroupLaplace K f)))
      (𝓝[>] 0) (𝓝 (K 0 f-semigroupLaplace K f)) := by
  have hiC : Continuous (laplaceIntegrand K f) :=
    (Real.continuous_exp.comp continuous_neg).smul (hc f)
  have hd := intervalIntegral.integral_hasDerivAt_right
    (f := laplaceIntegrand K f) (a := 0) (b := 0)
    (by simp) (hiC.stronglyMeasurableAtFilter volume (𝓝 0)) hiC.continuousAt
  have hder := (Real.hasDerivAt_exp 0).smul
    ((hasDerivAt_const (0:ℝ) (semigroupLaplace K f)).sub hd)
  have hval : laplaceIntegrand K f 0=K 0 f := by simp [laplaceIntegrand]
  change HasDerivAt (fun h : ℝ ↦ Real.exp h •
      (semigroupLaplace K f-∫ s in (0:ℝ)..h, laplaceIntegrand K f s))
    (Real.exp 0 • (0-laplaceIntegrand K f 0)+Real.exp 0 •
      (semigroupLaplace K f-∫ s in (0:ℝ)..0, laplaceIntegrand K f s)) 0 at hder
  simp only [Real.exp_zero,intervalIntegral.integral_same,sub_zero,hval,zero_sub,one_smul] at hder
  have hlim := hder.neg.tendsto_slope_zero.mono_left
    (nhdsWithin_mono 0 (show Ioi (0:ℝ) ⊆ {0}ᶜ from fun h hh ↦ ne_of_gt hh))
  have hl : -(-K 0 f+semigroupLaplace K f)=K 0 f-semigroupLaplace K f := by module
  rw [hl] at hlim
  apply hlim.congr'
  filter_upwards [eventually_mem_nhdsWithin] with h hh
  change h⁻¹ • (-(Real.exp (0+h) •
    (semigroupLaplace K f-∫ s in (0:ℝ)..(0+h), laplaceIntegrand K f s)) -
    -(Real.exp 0 • (semigroupLaplace K f-∫ s in (0:ℝ)..0, laplaceIntegrand K f s)))=_
  rw [zero_add,Real.exp_zero,intervalIntegral.integral_same,sub_zero,one_smul,
    semigroupLaplace_shift K hadd hc hnorm f (le_of_lt hh)]
  module

lemma semigroupLaplace_difference_tendsto_complex (K : ℝ → E→L[ℂ] E)
    (hadd : ∀ s t, 0 ≤ s → 0 ≤ t → K (s+t)=(K s).comp (K t))
    (hc : ∀ f, Continuous (fun t : ℝ ↦ K (max 0 t) f))
    (hnorm : ∀ t, 0 ≤ t → ∀ f, ‖K t f‖≤‖f‖) (f : E) :
    Tendsto (fun h : ℝ ↦ (h⁻¹ : ℂ) • (semigroupLaplace K f-K h (semigroupLaplace K f)))
      (𝓝[>] 0) (𝓝 (K 0 f-semigroupLaplace K f)) := by
  have hh := semigroupLaplace_difference_tendsto K hadd hc hnorm f
  apply hh.congr
  intro h
  rw [← IsScalarTower.algebraMap_smul ℂ h⁻¹
    (semigroupLaplace K f-K h (semigroupLaplace K f))]
  change ((h⁻¹:ℝ):ℂ) • (semigroupLaplace K f-K h (semigroupLaplace K f)) = _
  rw [Complex.ofReal_inv]

end HardSphere

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

lemma continuous_coordinateLine {N : ℕ} {L : Length}
    (X : Configuration N L) (p : Direction N) : Continuous (coordinateLine X p) := by
  unfold coordinateLine
  apply Continuous.add continuous_const
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  by_cases hi : i = p.1 <;> by_cases hj : j = p.2 <;>
    simp only [Pi.single_apply, hi, hj, ↓reduceIte]
  · exact continuous_id
  all_goals exact continuous_const

lemma integral_partial_coordinateLine {N : ℕ} {L : Length} {f : Configuration N L → ℂ}
    (hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun X : LiftedConfiguration N ↦ f (project N L X)))
    (X : Configuration N L) (p : Direction N) :
    (∫ t : AddCircle L.val, coordDerivative N L f p (coordinateLine X p t)) = 0 := by
  rw [← AddCircle.intervalIntegral_preimage L.val 0]
  have hcont : Continuous (fun t : ℝ ↦
      coordDerivative N L f p (coordinateLine X p (t : AddCircle L.val))) :=
    (continuous_coordDerivative hf p).comp
      ((continuous_coordinateLine X p).comp (AddCircle.continuous_mk' L.val))
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ ↦ hasDerivAt_coordinateLine (hf.differentiable (by simp)) X p t)
    (hcont.intervalIntegrable _ _)]
  rw [zero_add, AddCircle.coe_period, AddCircle.coe_zero, sub_self]

lemma integral_coordDerivative {N : ℕ} {L : Length} {f : Configuration N L → ℂ}
    (hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun X : LiftedConfiguration N ↦ f (project N L X))) (p : Direction N) :
    (∫ X : Configuration N L, coordDerivative N L f p X) = 0 := by
  let : BorelSpace (Configuration N L) := Pi.borelSpace
  have hcont : Continuous (fun z : AddCircle L.val × Configuration N L ↦
      coordDerivative N L f p (coordinateLine z.2 p z.1)) := by
    apply (continuous_coordDerivative hf p).comp
    unfold coordinateLine
    apply Continuous.add continuous_snd
    apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    by_cases hi : i = p.1 <;> by_cases hj : j = p.2 <;>
      simp [hi, hj, continuous_const, continuous_fst]
  have hint : Integrable (fun z : AddCircle L.val × Configuration N L ↦
      coordDerivative N L f p (coordinateLine z.2 p z.1)) (volume.prod volume) := by
    exact integrableOn_univ.mp (hcont.continuousOn.integrableOn_compact isCompact_univ)
  have hswap := integral_integral_swap
    (f := fun t X ↦ coordDerivative N L f p (coordinateLine X p t)) hint
  have hcir := integral_partial_coordinateLine hf
  simp_rw [hcir] at hswap
  simp only [integral_zero] at hswap
  let : (volume : Measure (Torus L)).IsAddLeftInvariant := by
    rw [volume_pi]
    exact Measure.pi.isAddLeftInvariant _
  let : (volume : Measure (Configuration N L)).IsAddLeftInvariant := by
    rw [volume_pi]
    exact Measure.pi.isAddLeftInvariant _
  let : (volume : Measure (Configuration N L)).IsAddRightInvariant :=
    IsAddLeftInvariant.isAddRightInvariant
  have hc : ∀ t : AddCircle L.val,
      (∫ X : Configuration N L, coordDerivative N L f p (coordinateLine X p t)) =
        ∫ X : Configuration N L, coordDerivative N L f p X := fun t ↦
    integral_add_right_eq_self _ _
  simp_rw [hc] at hswap
  have hvol : (volume (univ : Set (AddCircle L.val))).toReal = L.val := by
    rw [AddCircle.measure_univ, ENNReal.toReal_ofReal L.property.le]
  simp only [integral_const, Measure.real, hvol, Complex.real_smul] at hswap
  exact (mul_eq_zero.mp hswap).resolve_left (Complex.ofReal_ne_zero.mpr L.property.ne')

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

lemma integral_integration_by_parts {N : ℕ} {L : Length}
    {f g : Configuration N L → ℂ}
    (hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun X : LiftedConfiguration N ↦ f (project N L X)))
    (hg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun X : LiftedConfiguration N ↦ g (project N L X))) (p : Direction N) :
    (∫ X, conj (f X) * coordDerivative N L g p X) +
      (∫ X, conj (coordDerivative N L f p X) * g X) = 0 := by
  have hconj := Complex.conjCLE.contDiff.comp hf
  have h := integral_coordDerivative (f := (fun X ↦ conj (f X)) * g)
    (hconj.mul hg) p
  rw [coordDerivative_mul (hconj.differentiable (by simp)) (hg.differentiable (by simp)),
    coordDerivative_conj (hf.differentiable (by simp))] at h
  have hfg : Integrable (fun X ↦ conj (f X) * coordDerivative N L g p X) := by
    exact integrableOn_univ.mp
      ((((continuous_of_continuous_lift hf.continuous).star).mul
        (continuous_coordDerivative hg p)).continuousOn.integrableOn_compact isCompact_univ)
  have hgf : Integrable (fun X ↦ g X * conj (coordDerivative N L f p X)) := by
    exact integrableOn_univ.mp
      (((continuous_of_continuous_lift hg.continuous).mul
        (continuous_coordDerivative hf p).star).continuousOn.integrableOn_compact isCompact_univ)
  simp only [Pi.add_apply, Pi.mul_apply] at h
  rw [integral_add hfg hgf] at h
  simpa only [Pi.mul_apply, mul_comm (g _)] using h

section

attribute [local instance] OAI.HardSphere.configurationProductBorel
lemma SmoothTest.weak_derivative {N : ℕ} {L : Length} {a : ℝ}
    (u : SmoothTest N L a) (f : smoothAlgebra N L) (p : Direction N) :
    inner ℂ (ContinuousMap.toLp 2 volume ℂ f.val) (u.jet.2 p) +
      inner ℂ (ContinuousMap.toLp 2 volume ℂ (smoothPartial f p)) u.jet.1 = 0 := by
  rw [L2.inner_def, L2.inner_def]
  have h₁ : (∫ X, inner ℂ ((ContinuousMap.toLp 2 volume ℂ f.val) X) ((u.jet.2 p) X)) =
      ∫ X, conj (f.val X) * coordDerivative N L u.toFun p X := by
    apply integral_congr_ae
    filter_upwards [ContinuousMap.coeFn_toLp (𝕜 := ℂ) (p := 2) volume f.val, (u.partial_memLp p).coeFn_toLp]
      with X hX hY
    change inner ℂ _ ((u.partial_memLp p).toLp _ X) = _
    rw [hX, hY, RCLike.inner_apply, mul_comm]
  have h₂ : (∫ X, inner ℂ ((ContinuousMap.toLp 2 volume ℂ (smoothPartial f p)) X) (u.jet.1 X)) =
      ∫ X, conj (coordDerivative N L f.val p X) * u.toFun X := by
    apply integral_congr_ae
    filter_upwards [ContinuousMap.coeFn_toLp (𝕜 := ℂ) (p := 2) volume (smoothPartial f p), u.memLp.coeFn_toLp]
      with X hX hY
    change inner ℂ _ (u.memLp.toLp _ X) = _
    rw [hX, hY, RCLike.inner_apply, mul_comm]
    rfl
  rw [h₁, h₂]
  exact integral_integration_by_parts f.property u.smooth p

lemma weak_derivative {N : ℕ} {L : Length} {a : ℝ} {u : Jet N L}
    (hu : u ∈ dirichletDomain N L a) (f : smoothAlgebra N L) (p : Direction N) :
    inner ℂ (ContinuousMap.toLp 2 volume ℂ f.val) (u.2 p) +
      inner ℂ (ContinuousMap.toLp 2 volume ℂ (smoothPartial f p)) u.1 = 0 := by
  have hc : IsClosed {v : Jet N L |
      inner ℂ (ContinuousMap.toLp 2 volume ℂ f.val) (v.2 p) +
      inner ℂ (ContinuousMap.toLp 2 volume ℂ (smoothPartial f p)) v.1 = 0} :=
    isClosed_eq ((continuous_const.inner ((continuous_apply p).comp continuous_snd)).add
      (continuous_const.inner continuous_fst)) continuous_const
  exact closure_minimal (by rintro _ ⟨v, rfl⟩; exact v.weak_derivative f p) hc hu

end

end HardSphere

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_HeatScalar
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
namespace HardSphere

lemma cfc_eigen_apply {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] (T : E →L[ℂ] E) (hT : IsSelfAdjoint T)
    (f : ℝ → ℝ) (hf : Continuous f) (r : ℝ) (hd : DifferentiableAt ℝ f r)
    (u : E) (hu : T u = r • u) :
    cfc (p := IsSelfAdjoint) f T u = f r • u := by
  have hg : Continuous (dslope f r) := by
    rw [← continuousOn_univ]
    exact (continuousOn_dslope (s := Set.univ) (Filter.univ_mem)).mpr ⟨hf.continuousOn,hd⟩
  have heq : (fun x ↦ dslope f r x * (x-r) + f r) = f := by
    funext x
    have hh := sub_smul_dslope f r x
    simp only [smul_eq_mul] at hh
    rw [mul_comm,hh,sub_add_cancel]
  have hcalc : cfc (p := IsSelfAdjoint) f T = cfc (p := IsSelfAdjoint) (dslope f r) T * (T - algebraMap ℝ (E →L[ℂ] E) r) +
      algebraMap ℝ (E →L[ℂ] E) (f r) := by
    conv_lhs => rw [← heq]
    rw [cfc_add T (fun x ↦ dslope f r x * (x-r)) (fun _ ↦ f r)
        (hg.mul (continuous_id.sub continuous_const)).continuousOn continuousOn_const,
      cfc_mul (dslope f r) (fun x ↦ x-r) T hg.continuousOn (continuous_id.sub continuous_const).continuousOn,
      cfc_sub (fun x ↦ x) (fun _ ↦ r) T continuous_id.continuousOn continuousOn_const,
      cfc_id' ℝ T hT,cfc_const r T hT,cfc_const (f r) T hT]
  rw [hcalc]
  simp only [add_apply,mul_apply_eq_comp,
    sub_apply,ContinuousLinearMap.algebraMap_apply,hu,sub_self,map_zero,zero_add]

lemma heatScalar_smooth (t : ℝ) : ContDiff ℝ 1 (heatScalar t) := by
  unfold heatScalar
  exact contDiff_const.mul (expNegInvGlue.contDiff.comp (contDiff_id.div_const t))

lemma heatScalar_of_pos {t x : ℝ} (ht : 0 < t) (hx : 0 < x) :
    heatScalar t x = Real.exp (t - t/x) := by
  unfold heatScalar expNegInvGlue
  rw [ite_eq_right (not_le.mpr (div_pos hx ht)),← Real.exp_add]
  congr 1
  field_simp
  ring

lemma heatScalar_resolvent {t E : ℝ} (ht : 0 < t) (hE : 0 ≤ E) :
    heatScalar t (1+E)⁻¹ = Real.exp (-t*E) := by
  rw [heatScalar_of_pos ht (inv_pos.mpr (by linarith))]
  congr 1
  rw [div_inv_eq_mul]
  ring

end HardSphere

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Fourier_CharacterDerivativeFactor
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
open scoped ComplexConjugate

lemma character_smoothPartial (N : ℕ) (L : Length) (k : Direction N → ℤ) (p : Direction N) :
    smoothPartial ⟨configurationCharacter N L k,configurationCharacter_smooth N L k⟩ p =
      characterDerivativeFactor L (k p) • configurationCharacter N L k := by
  ext X
  exact configurationCharacter_partial N L k p X

lemma character_weak_derivative {N : ℕ} {L : Length} {a : ℝ} {u : Jet N L}
    (hu : u∈dirichletDomain N L a) (k : Direction N → ℤ) (p : Direction N) :
    inner ℂ (characterL2 N L k) (u.2 p) =
      -conj (characterDerivativeFactor L (k p)) * inner ℂ (characterL2 N L k) u.1 := by
  have h := weak_derivative hu ⟨configurationCharacter N L k,configurationCharacter_smooth N L k⟩ p
  rw [character_smoothPartial,map_smul,inner_smul_left] at h
  change inner ℂ (characterL2 N L k) (u.2 p) +
    conj (characterDerivativeFactor L (k p)) * inner ℂ (characterL2 N L k) u.1 = 0 at h
  linear_combination h

lemma characterTest_jet (N : ℕ) (L : Length) (a : ℝ) (ha : a<0) (k : Direction N → ℤ) :
    (characterTest N L a ha k).jet=
      (characterL2 N L k,fun p ↦ characterDerivativeFactor L (k p) • characterL2 N L k) := by
  apply Prod.ext
  · apply Lp.ext
    exact (characterTest N L a ha k).memLp.coeFn_toLp.trans (characterL2_ae N L k).symm
  · funext p
    apply Lp.ext
    filter_upwards [(characterTest N L a ha k).partial_memLp p |>.coeFn_toLp,
      Lp.coeFn_smul (characterDerivativeFactor L (k p)) (characterL2 N L k),characterL2_ae N L k] with X h₁ h₂ h₃
    change ((characterTest N L a ha k).partial_memLp p).toLp _ X = _
    rw [h₁,h₂]
    change coordDerivative N L (configurationCharacter N L k) p X =
      characterDerivativeFactor L (k p) * (characterL2 N L k) X
    rw [h₃]
    exact configurationCharacter_partial N L k p X

lemma character_factor_square (L : Length) (n : ℤ) :
    -(conj (characterDerivativeFactor L n))^2 = ((2*Real.pi*n/L.val)^2:ℝ) := by
  simp only [characterDerivativeFactor,Nat.cast_ofNat,map_div₀,map_mul,map_ofNat,Complex.conj_ofReal,
    Complex.conj_I,Complex.ofReal_pow,Complex.ofReal_div,Complex.ofReal_mul,Complex.ofReal_ofNat,map_intCast,Complex.ofReal_intCast]
  ring_nf
  simp only [Complex.I_sq]
  ring

lemma character_form_pairing (N : ℕ) (L : Length) (a : ℝ) (ha : a<0)
    (k : Direction N → ℤ) {v : Jet N L} (hv : v∈dirichletDomain N L a) :
    Variational.gradientPairing (characterTest N L a ha k).jet v =
      (fourierEnergy N L k:ℂ) * inner ℂ (characterL2 N L k) v.1 := by
  rw [characterTest_jet]
  change (∑ p : Direction N, inner ℂ (characterDerivativeFactor L (k p) • characterL2 N L k) (v.2 p)) = _
  simp_rw [inner_smul_left,character_weak_derivative hv]
  have hterm (p : Direction N) :
      conj (characterDerivativeFactor L (k p)) *
        (-conj (characterDerivativeFactor L (k p)) * inner ℂ (characterL2 N L k) v.1) =
      (((2*Real.pi*k p/L.val)^2:ℝ):ℂ)*inner ℂ (characterL2 N L k) v.1 := by
    rw [← character_factor_square]
    ring
  simp_rw [hterm]
  rw [← Finset.sum_mul]
  simp only [fourierEnergy,Nat.cast_ofNat,Complex.ofReal_sum]

lemma character_resolvent (N : ℕ) (L : Length) (a : ℝ) (ha : a<0) (k : Direction N → ℤ) :
    formResolvent N L a (characterL2 N L k) =
      ((1+(fourierEnergy N L k:ℂ))⁻¹) • characterL2 N L k := by
  let u := (characterTest N L a ha k).jet
  have hu : u∈dirichletDomain N L a := subset_closure ⟨characterTest N L a ha k,rfl⟩
  have huf : u.1=characterL2 N L k := congrArg Prod.fst (characterTest_jet N L a ha k)
  let ug : hilbertDomain N L a := ⟨(hilbertJetEquiv N L).symm u,by
    change hilbertJetEquiv N L ((hilbertJetEquiv N L).symm u) ∈ dirichletSubmodule N L a
    simpa using hu⟩
  have hE := fourierEnergy_nonneg N L k
  have hne : 1+(fourierEnergy N L k:ℂ) ≠ 0 := by
    have hreal : (1:ℝ)+fourierEnergy N L k ≠ 0 := ne_of_gt (by linarith)
    exact_mod_cast hreal
  have heq : (scalarEmbedding N L a).adjoint (characterL2 N L k) =
      ((1+(fourierEnergy N L k:ℂ))⁻¹) • ug := by
    apply ext_inner_right ℂ
    intro v
    rw [ContinuousLinearMap.adjoint_inner_left]
    rw [inner_smul_left ug v ((1+(fourierEnergy N L k:ℂ))⁻¹)]
    have hv : hilbertJetEquiv N L (v : HilbertJet N L) ∈ dirichletDomain N L a := v.property
    have hg : inner ℂ ug v = (1+(fourierEnergy N L k:ℂ))*
        inner ℂ (characterL2 N L k) (scalarEmbedding N L a v) := by
      change inner ℂ (ug : HilbertJet N L) (v : HilbertJet N L) = _
      rw [hilbertJet_inner]
      have hgu : hilbertJetEquiv N L (ug : HilbertJet N L) = u := by simp [ug]
      rw [hgu,huf]
      have hh := character_form_pairing N L a ha k hv
      change (∑ p : Direction N, inner ℂ (u.2 p)
        ((hilbertJetEquiv N L (v : HilbertJet N L)).2 p)) = _ at hh
      rw [hh]
      change inner ℂ (characterL2 N L k) (scalarEmbedding N L a v) +
        (fourierEnergy N L k:ℂ)*inner ℂ (characterL2 N L k) (scalarEmbedding N L a v) = _
      ring
    rw [hg]
    simp only [map_inv₀,map_add,map_one,Complex.conj_ofReal]
    rw [← mul_assoc,inv_mul_cancel₀ hne,one_mul]
  change scalarEmbedding N L a ((scalarEmbedding N L a).adjoint (characterL2 N L k)) = _
  rw [heq,map_smul]
  congr 1

lemma character_formHeat (N : ℕ) (L : Length) (a : ℝ) (ha : a<0) {t : ℝ}
    (ht : 0<t) (k : Direction N → ℤ) :
    formHeat N L a t (characterL2 N L k) =
      (Real.exp (-t*fourierEnergy N L k):ℂ) • characterL2 N L k := by
  have hh : formResolvent N L a (characterL2 N L k) =
      ((1+fourierEnergy N L k)⁻¹:ℝ) • characterL2 N L k := by
    rw [← IsScalarTower.algebraMap_smul ℂ ((1+fourierEnergy N L k)⁻¹:ℝ) (characterL2 N L k)]
    change formResolvent N L a (characterL2 N L k) = (((1+fourierEnergy N L k)⁻¹:ℝ):ℂ) • _
    simpa only [Complex.ofReal_inv,Complex.ofReal_add,Complex.ofReal_one] using
      character_resolvent N L a ha k
  rw [formHeat,cfc_eigen_apply _ (formResolvent_isPositive N L a).isSelfAdjoint _
    (heatScalar_smooth t).continuous _ ((heatScalar_smooth t).differentiable (by norm_num)).differentiableAt _ hh,
    heatScalar_resolvent ht (fourierEnergy_nonneg N L k)]
  exact (IsScalarTower.algebraMap_smul ℂ _ _).symm

lemma freeTransition_eq_formHeat (N : ℕ) (L : Length) (a : ℝ) (ha : a<0) {t : ℝ}
    (ht : 0<t) : freeTransition N L t = formHeat N L a t := by
  apply ContinuousLinearMap.ext_on (s := Set.range (characterL2 N L))
  · exact Submodule.dense_iff_topologicalClosure_eq_top.mpr (characterL2_span_dense N L)
  · rintro _ ⟨k,rfl⟩
    rw [freeTransition_character N L t ht.le,character_formHeat N L a ha ht]

end HardSphere

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Orbitals_StrongContractionLimitDense
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
namespace HardSphere
lemma strong_contraction_limit_of_dense {E F ι : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] {l : Filter ι} (A : ι → E →L[ℂ] E) (B : E →L[ℂ] E)
    (hA : ∀ t u, ‖A t u‖≤‖u‖) (hB : ∀ u, ‖B u‖≤‖u‖)
    (f : F → E) (hf : DenseRange f)
    (ht : ∀ y, Tendsto (fun t ↦ A t (f y)) l (𝓝 (B (f y)))) (u : E) :
    Tendsto (fun t ↦ A t u) l (𝓝 (B u)) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨y,hy⟩ := hf.exists_dist_lt u (show 0<ε/3 by positivity)
  filter_upwards [(Metric.tendsto_nhds.mp (ht y)) (ε/3) (by positivity)] with t ht
  have h1 : dist (A t u) (A t (f y))≤dist u (f y) := by
    simpa only [dist_eq_norm,map_sub] using hA t (u-f y)
  have h2 : dist (B (f y)) (B u)≤dist (f y) u := by
    simpa only [dist_eq_norm,map_sub] using hB (f y-u)
  have htriangle := dist_triangle4 (A t u) (A t (f y)) (B (f y)) (B u)
  rw [dist_comm (f y) u] at h2
  linarith
end HardSphere

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Cutoffs_RegularizationWeight
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
noncomputable section
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
namespace HardSphere
open scoped Topology
open ContinuousLinearMap

section
variable {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
  [InnerProductSpace ℂ E] [InnerProductSpace ℂ F] [CompleteSpace E] [CompleteSpace F] [Nontrivial F]

attribute [local instance] OAI.HardSphere.scalarOperatorRealAlgebraRegularizedLift
lemma positive_contraction_spectrum {R : F →L[ℂ] F} (hR : R.IsPositive) (hRn : ‖R‖≤1) :
    spectrum ℝ R⊆Set.Icc (0:ℝ) 1 := by
  intro x hx
  refine ⟨spectrum_nonneg_of_nonneg ((ContinuousLinearMap.nonneg_iff_isPositive _).mpr hR) hx,?_⟩
  have hb : |x|≤‖R‖ := by simpa only [Real.norm_eq_abs] using spectrum.norm_le_norm_of_mem hx
  exact (le_abs_self x).trans (hb.trans hRn)

end
end HardSphere

end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_NormSqLpIntegral
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
namespace HardSphere

lemma norm_sq_toLp_eq_integral {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f : α → ℂ} (hf : MemLp f 2 μ) :
    ‖hf.toLp f‖^2=∫ x, ‖f x‖^2 ∂μ := by
  rw [norm_sq_eq_re_inner (𝕜 := ℂ),L2.inner_def,← integral_re]
  · apply integral_congr_ae
    filter_upwards [hf.coeFn_toLp] with x hx
    rw [hx,inner_self_eq_norm_sq]
  · exact L2.integrable_inner _ _

lemma bounded_toLp_tendsto {α ι : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsFiniteMeasure μ] {l : Filter ι} [l.IsCountablyGenerated]
    {F : ι → α → ℂ} {f : α → ℂ} (hF : ∀ t, MemLp (F t) 2 μ) (hf : MemLp f 2 μ)
    {C : ℝ} (_hC : 0≤C) (hFb : ∀ t x, ‖F t x‖≤C) (hfb : ∀ x, ‖f x‖≤C)
    (ht : ∀ᵐ x ∂μ, Tendsto (fun t ↦ F t x) l (𝓝 (f x))) :
    Tendsto (fun t ↦ (hF t).toLp (F t)) l (𝓝 (hf.toLp f)) := by
  have H : Tendsto (fun t ↦ ∫ x, ‖F t x-f x‖^2 ∂μ) l (𝓝 0) := by
    have h := tendsto_integral_filter_of_dominated_convergence (fun _ ↦ (2*C)^2)
      (l := l) (F := fun t x ↦ ‖F t x-f x‖^2) (f := fun _ ↦ (0:ℝ))
      (Eventually.of_forall fun t ↦ ((hF t).aestronglyMeasurable.sub hf.aestronglyMeasurable).norm.pow 2)
      (Eventually.of_forall fun t ↦ Eventually.of_forall fun x ↦ by
        rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
        apply pow_le_pow_left₀ (norm_nonneg _)
        exact (norm_sub_le _ _).trans (by linarith [hFb t x,hfb x]))
      (integrable_const _) ?_
    · simpa only [integral_zero] using h
    · filter_upwards [ht] with x hx
      simpa using ((hx.sub (tendsto_const_nhds (x := f x))).norm.pow 2)
  rw [tendsto_iff_dist_tendsto_zero]
  have hsq : ∀ t, (dist ((hF t).toLp (F t)) (hf.toLp f))^2=
      ∫ x, ‖F t x-f x‖^2 ∂μ := by
    intro t
    rw [dist_eq_norm,← MemLp.toLp_sub (hF t) hf]
    exact norm_sq_toLp_eq_integral _
  have hroot := Real.continuous_sqrt.continuousAt.tendsto.comp H
  simpa only [Function.comp_def,← hsq,Real.sqrt_sq (dist_nonneg),Real.sqrt_zero] using hroot

end HardSphere

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_KilledAverage
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
open Wiener

lemma killedAverage_zero (N : ℕ) (L : Length) (a : ℝ)
    (g : Configuration N L → ℂ) (X : Configuration N L) :
    killedAverage N L a 0 g X=(allowed N L a).indicator g X := by
  have h : ∀ w : CoordinatePaths N,
      killedObservable N L a g (freeTrajectory N L 0 w X)=(allowed N L a).indicator g X := by
    intro w
    rw [freeTrajectory_zero]
    by_cases hX : X∈allowed N L a
    · have ha : ContinuousMap.const Time X∈staysAllowed N L a := by
        rintro _ ⟨t,rfl⟩
        exact hX
      simp only [killedObservable,Set.indicator_of_mem ha,ContinuousMap.const_apply,
        Set.indicator_of_mem hX]
    · have ha : ContinuousMap.const Time X∉staysAllowed N L a :=
        fun h ↦ hX (h (Set.mem_range_self (0:Time)))
      simp only [killedObservable,Set.indicator_of_notMem ha,Set.indicator_of_notMem hX]
  simp only [killedAverage,h,integral_const,measureReal_def,measure_univ,ENNReal.toReal_one,one_smul]

lemma killedTransition_tendsto_zero_continuous (N : ℕ) (L : Length) (a : ℝ)
    (g : C(Configuration N L,ℂ)) :
    Tendsto (fun t : ℝ ↦ killedTransition N L a t (ContinuousMap.toLp 2 volume ℂ g))
      (𝓝 0) (𝓝 (killedTransition N L a 0 (ContinuousMap.toLp 2 volume ℂ g))) := by
  have hgLp : MemLp (fun X ↦ g X) 2 (volume : Measure (Configuration N L)) :=
    MemLp.of_bound g.continuous.measurable.aestronglyMeasurable ‖g‖
      (Eventually.of_forall g.norm_coe_le_norm)
  have hge : ContinuousMap.toLp 2 volume ℂ g = hgLp.toLp g := by
    apply Lp.ext
    exact (ContinuousMap.coeFn_toLp (𝕜 := ℂ) (p := 2) volume g).trans hgLp.coeFn_toLp.symm
  have hEq : ∀ t, killedTransition N L a t (ContinuousMap.toLp 2 volume ℂ g)=
      (killedAverage_memLp N L a t g.continuous.measurable (norm_nonneg g)
        g.norm_coe_le_norm).toLp (killedAverage N L a t g) := by
    intro t
    rw [hge]
    exact killedTransition_bounded N L a t g.continuous.measurable
      hgLp (norm_nonneg g) g.norm_coe_le_norm
  simp_rw [hEq]
  apply bounded_toLp_tendsto _ _ (norm_nonneg g)
    (fun t X ↦ killedAverage_bound N L a t (norm_nonneg g) g.norm_coe_le_norm X)
    (fun X ↦ killedAverage_bound N L a 0 (norm_nonneg g) g.norm_coe_le_norm X)
  apply Eventually.of_forall
  intro X
  rw [killedAverage_zero]
  exact killedAverage_tendsto_zero N L a g X

lemma killedTransition_tendsto_zero (N : ℕ) (L : Length) (a : ℝ) (f : ScalarL2 N L) :
    Tendsto (fun t : ℝ ↦ killedTransition N L a t f) (𝓝 0)
      (𝓝 (killedTransition N L a 0 f)) := by
  exact strong_contraction_limit_of_dense (fun t ↦ killedTransition N L a t)
    (killedTransition N L a 0) (fun t ↦ killedTransition_apply_contraction N L a t)
    (killedTransition_apply_contraction N L a 0)
    (fun g : C(Configuration N L,ℂ) ↦ ContinuousMap.toLp 2 volume ℂ g)
    (ContinuousMap.toLp_denseRange ℂ volume ℂ (by norm_num : (2:ℝ≥0∞)≠∞))
    (killedTransition_tendsto_zero_continuous N L a) f

end HardSphere

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Conditioning_ReverseConfigurationPath
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
open Wiener
open scoped ComplexConjugate

lemma staysAllowed_reverse (N : ℕ) (L : Length) (a : ℝ) :
    reverseConfigurationPath N L ⁻¹' staysAllowed N L a = staysAllowed N L a := by
  ext ω
  change (Set.range (reverseConfigurationPath N L ω) ⊆ allowed N L a) ↔
    (Set.range ω ⊆ allowed N L a)
  have hr : Set.range (reverseConfigurationPath N L ω) = Set.range ω := by
    change Set.range (ω ∘ reverseTime) = Set.range ω
    exact (Function.Involutive.surjective reverseTime_reverse).range_comp ω
  rw [hr]

lemma coordinateReverse_preserving (N : ℕ) :
    MeasurePreserving (fun w : CoordinatePaths N ↦ fun p ↦ reverseIncrements (w p))
      (coordinateWiener N) (coordinateWiener N) := by
  refine ⟨Measurable.of_eval fun p ↦ reverseIncrements.continuous.measurable.comp (measurable_pi_apply p), ?_⟩
  unfold coordinateWiener
  rw [Measure.pi_map_pi (fun _ ↦ reverseIncrements.continuous.measurable.aemeasurable)]
  simp_rw [reverseIncrements_preserving.map_eq]

lemma reverse_freeTrajectory (N : ℕ) (L : Length) (t : ℝ) (w : CoordinatePaths N)
    (X : Configuration N L) :
    reverseConfigurationPath N L (freeTrajectory N L t w X) =
      freeTrajectory N L t (fun p ↦ reverseIncrements (w p))
        (freeTrajectory N L t w X 1) := by
  ext s i j
  change X i j + ((Real.sqrt (2*t)*w (i,j) (reverseTime s) : ℝ) : AddCircle L.val) =
    (X i j + ((Real.sqrt (2*t)*w (i,j) 1 : ℝ) : AddCircle L.val)) +
      ((Real.sqrt (2*t)*(w (i,j) (reverseTime s)-w (i,j) 1) : ℝ) : AddCircle L.val)
  rw [mul_sub,AddCircle.coe_sub]
  abel

lemma reverse_freePath_preserving (N : ℕ) (L : Length) (t : ℝ) :
    MeasurePreserving (reverseConfigurationPath N L) (freePathLaw N L t) (freePathLaw N L t) := by
  let : (volume : Measure (Torus L)).IsAddLeftInvariant := by
    rw [volume_pi]
    exact Measure.pi.isAddLeftInvariant _
  let : (volume : Measure (Configuration N L)).IsAddLeftInvariant := by
    rw [volume_pi]
    exact Measure.pi.isAddLeftInvariant _
  let : (volume : Measure (Configuration N L)).IsAddRightInvariant :=
    IsAddLeftInvariant.isAddRightInvariant
  have hm : Measurable (fun p : CoordinatePaths N × Configuration N L ↦
      freeTrajectory N L t p.1 p.2 1) :=
    ((freeTrajectory_continuous N L t).eval continuous_const).measurable
  have hskew := (coordinateReverse_preserving N).skew_product hm
    (Filter.Eventually.of_forall (fun w : CoordinatePaths N ↦
      map_add_right_eq_self (volume : Measure (Configuration N L))
        (fun i j ↦ ((Real.sqrt (2*t) * w (i,j) 1 : ℝ) : AddCircle L.val))))
  refine ⟨(reverseConfigurationPath_continuous N L).measurable, ?_⟩
  unfold freePathLaw
  rw [Measure.map_map (reverseConfigurationPath_continuous N L).measurable
    (freeTrajectory_continuous N L t).measurable]
  have heq : (reverseConfigurationPath N L ∘
      (fun p : CoordinatePaths N × Configuration N L ↦ freeTrajectory N L t p.1 p.2)) =
      (fun p : CoordinatePaths N × Configuration N L ↦ freeTrajectory N L t p.1 p.2) ∘
        (fun p ↦ (fun q ↦ reverseIncrements (p.1 q), freeTrajectory N L t p.1 p.2 1)) := by
    funext p
    exact reverse_freeTrajectory N L t p.1 p.2
  change MeasurePreserving
    (fun p : CoordinatePaths N × Configuration N L ↦
      (fun q ↦ reverseIncrements (p.1 q), freeTrajectory N L t p.1 p.2 1))
    ((coordinateWiener N).prod volume) ((coordinateWiener N).prod volume) at hskew
  rw [heq, ← Measure.map_map (freeTrajectory_continuous N L t).measurable hskew.measurable,
    hskew.map_eq]

lemma reverse_killedPath_preserving (N : ℕ) (L : Length) (a t : ℝ) :
    MeasurePreserving (reverseConfigurationPath N L) (killedPathLaw N L a t)
      (killedPathLaw N L a t) := by
  refine ⟨(reverseConfigurationPath_continuous N L).measurable,?_⟩
  unfold killedPathLaw
  conv_rhs => rw [← (reverse_freePath_preserving N L t).map_eq]
  rw [Measure.restrict_map (reverseConfigurationPath_continuous N L).measurable
    (staysAllowed_open N L a).measurableSet, staysAllowed_reverse]

lemma killedTransition_selfAdjoint (N : ℕ) (L : Length) (a t : ℝ) :
    IsSelfAdjoint (killedTransition N L a t) := by
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
  intro f g
  change inner ℂ (killedTransition N L a t f) g = inner ℂ f (killedTransition N L a t g)
  rw [← inner_conj_symm, killedTransition_pairing, ← integral_conj, killedTransition_pairing]
  have h := (reverse_killedPath_preserving N L a t).integral_comp
    (reversePathEquiv N L).measurableEmbedding
    (fun ω : ConfigurationPath N L ↦ conj (f (ω 0)) * g (ω 1))
  rw [← h]
  apply integral_congr_ae
  filter_upwards [] with ω
  simp only [map_mul,starRingEnd_self_apply,reverseConfigurationPath_apply,reverseTime_zero,
    reverseTime_one]
  ring

end HardSphere

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Operators_KilledTransitionAdd
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
namespace HardSphere
open Wiener
open scoped ComplexConjugate

theorem killedTransition_add (N : ℕ) (L : Length) (a s t : ℝ) (hs : 0 < s) (ht : 0<t) :
    killedTransition N L a (s+t) = killedTransition N L a s ∘L killedTransition N L a t := by
  have hd := ContinuousMap.toLp_denseRange ℂ (volume : Measure (Configuration N L)) ℂ
    (show (2:ℝ≥0∞) ≠ ∞ by norm_num)
  apply ContinuousLinearMap.ext
  intro g
  change killedTransition N L a (s+t) g = killedTransition N L a s (killedTransition N L a t g)
  have hc : IsClosed {g : ScalarL2 N L | killedTransition N L a (s+t) g =
      killedTransition N L a s (killedTransition N L a t g)} :=
    isClosed_eq (ContinuousLinearMap.continuous _) ((ContinuousLinearMap.continuous _).comp
      (ContinuousLinearMap.continuous _))
  apply hc.closure_subset_iff.mpr ?_ (hd g)
  rintro _ ⟨g,rfl⟩
  change killedTransition N L a (s+t) (ContinuousMap.toLp 2 volume ℂ g) =
    killedTransition N L a s (killedTransition N L a t (ContinuousMap.toLp 2 volume ℂ g))
  have hgLp : MemLp (fun X ↦ g X) 2 (volume : Measure (Configuration N L)) :=
    MemLp.of_bound g.continuous.measurable.aestronglyMeasurable ‖g‖
      (Filter.Eventually.of_forall g.norm_coe_le_norm)
  have hge : ContinuousMap.toLp 2 volume ℂ g = hgLp.toLp g := by
    apply Lp.ext
    exact (ContinuousMap.coeFn_toLp (𝕜 := ℂ) (p := 2) volume g).trans hgLp.coeFn_toLp.symm
  rw [hge,killedTransition_bounded N L a (s+t) g.continuous.measurable hgLp (norm_nonneg _) g.norm_coe_le_norm,
    killedTransition_bounded N L a t g.continuous.measurable hgLp (norm_nonneg _) g.norm_coe_le_norm,
    killedTransition_bounded N L a s (killedAverage_measurable N L a t g.continuous.measurable)
      (killedAverage_memLp N L a t g.continuous.measurable (norm_nonneg _) g.norm_coe_le_norm)
      (norm_nonneg g) (killedAverage_bound N L a t (norm_nonneg _) g.norm_coe_le_norm)]
  apply MemLp.toLp_congr
  exact Filter.Eventually.of_forall (killedAverage_add N L a s t hs ht g.continuous.measurable
    (norm_nonneg _) g.norm_coe_le_norm)

end HardSphere

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Operators_KilledTransitionContinuousAe
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
namespace HardSphere
lemma killedTransition_continuous_ae (N : ℕ) (L : Length) (a t : ℝ)
    (g : C(Configuration N L,ℂ)) :
    killedTransition N L a t (ContinuousMap.toLp 2 volume ℂ g) =ᵐ[volume]
      killedAverage N L a t g := by
  have hgLp : MemLp (fun X ↦ g X) 2 (volume : Measure (Configuration N L)) :=
    MemLp.of_bound g.continuous.measurable.aestronglyMeasurable ‖g‖
      (Eventually.of_forall g.norm_coe_le_norm)
  have hge : ContinuousMap.toLp 2 volume ℂ g = hgLp.toLp g := by
    apply Lp.ext
    exact (ContinuousMap.coeFn_toLp (𝕜 := ℂ) (p := 2) volume g).trans hgLp.coeFn_toLp.symm
  rw [hge,killedTransition_bounded N L a t g.continuous.measurable
    hgLp (norm_nonneg g) g.norm_coe_le_norm]
  exact MemLp.coeFn_toLp _

end HardSphere

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_AllowedProjection
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
open Wiener ContinuousLinearMap
open scoped ComplexConjugate

lemma killedAverage_zero_of_not_allowed (N : ℕ) (L : Length) (a t : ℝ)
    (g : Configuration N L→ℂ) {X : Configuration N L} (hX : X∉allowed N L a) :
    killedAverage N L a t g X=0 := by
  apply integral_eq_zero_of_ae
  filter_upwards [coordinateWiener_start_zero N] with w hw
  have hn : freeTrajectory N L t w X∉staysAllowed N L a := by
    intro h
    have h0 := h (Set.mem_range_self (0:Time))
    rw [freeTrajectory_start N L t hw X] at h0
    exact hX h0
  exact Set.indicator_of_notMem hn _

lemma allowedProjection_ae (N : ℕ) (L : Length) (a : ℝ) (f : ScalarL2 N L) :
    allowedProjection N L a f =ᵐ[volume] (allowed N L a).indicator f := by
  filter_upwards [L2Multiplier.coe_clm ((allowed N L a).indicator (fun _ ↦ (1:ℂ)))
    ((memLp_top_const (1:ℂ)).indicator (isOpen_allowed N L a).measurableSet) f] with X hX
  change (L2Multiplier.clm _ _ f) X=_
  rw [hX]
  by_cases h : X∈allowed N L a <;> simp [h]

lemma killedTransition_zero (N : ℕ) (L : Length) (a : ℝ) :
    killedTransition N L a 0=allowedProjection N L a := by
  apply ContinuousLinearMap.ext_on (s := Set.range (ContinuousMap.toLp 2 volume ℂ))
  · exact (ContinuousMap.toLp_denseRange ℂ volume ℂ (by norm_num : (2:ℝ≥0∞)≠∞)).mono
      (Submodule.subset_span)
  · rintro _ ⟨g,rfl⟩
    apply Lp.ext
    filter_upwards [killedTransition_continuous_ae N L a 0 g,
      allowedProjection_ae N L a (ContinuousMap.toLp 2 volume ℂ g),
      ContinuousMap.coeFn_toLp (𝕜 := ℂ) (p := 2) volume g] with X h1 h2 h3
    rw [h1,killedAverage_zero,h2]
    by_cases h : X∈allowed N L a
    · simpa only [Set.indicator_of_mem h] using h3.symm
    · simp only [Set.indicator_of_notMem h]

lemma allowedProjection_killedTransition (N : ℕ) (L : Length) (a t : ℝ) :
    (allowedProjection N L a).comp (killedTransition N L a t)=killedTransition N L a t := by
  apply ContinuousLinearMap.ext_on (s := Set.range (ContinuousMap.toLp 2 volume ℂ))
  · exact (ContinuousMap.toLp_denseRange ℂ volume ℂ (by norm_num : (2:ℝ≥0∞)≠∞)).mono
      (Submodule.subset_span)
  · rintro _ ⟨g,rfl⟩
    apply Lp.ext
    filter_upwards [killedTransition_continuous_ae N L a t g,
      allowedProjection_ae N L a (killedTransition N L a t (ContinuousMap.toLp 2 volume ℂ g))]
      with X h1 h2
    change (allowedProjection N L a (killedTransition N L a t (ContinuousMap.toLp 2 volume ℂ g))) X=_
    rw [h2]
    by_cases h : X∈allowed N L a
    · exact Set.indicator_of_mem h _
    · rw [Set.indicator_of_notMem h,h1,killedAverage_zero_of_not_allowed N L a t g h]

lemma killedTransition_allowedProjection (N : ℕ) (L : Length) (a t : ℝ) :
    (killedTransition N L a t).comp (allowedProjection N L a)=killedTransition N L a t := by
  have he := congrArg ContinuousLinearMap.adjoint (allowedProjection_killedTransition N L a t)
  rw [adjoint_comp,← killedTransition_zero N L a,
    (killedTransition_selfAdjoint N L a 0).adjoint_eq,
    (killedTransition_selfAdjoint N L a t).adjoint_eq] at he
  simpa only [killedTransition_zero] using he

lemma killedTransition_add_nonneg (N : ℕ) (L : Length) (a s t : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t) :
    killedTransition N L a (s+t)=(killedTransition N L a s).comp (killedTransition N L a t) := by
  rcases hs.eq_or_lt with hs | hs
  · rw [← hs,zero_add,killedTransition_zero,allowedProjection_killedTransition]
  rcases ht.eq_or_lt with ht | ht
  · rw [← ht,add_zero,killedTransition_zero,killedTransition_allowedProjection]
  exact killedTransition_add N L a s t hs ht

end HardSphere

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Operators_FreeResolventDenseRange
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
open ContinuousLinearMap Filter
open scoped Topology

lemma freeResolvent_denseRange (N : ℕ) (L : Length) (a : ℝ) (ha : a<0) :
    DenseRange (formResolvent N L a) := by
  change Dense (Set.range (formResolvent N L a))
  change Dense ((formResolvent N L a).range : Set (ScalarL2 N L))
  apply Submodule.dense_iff_topologicalClosure_eq_top.mpr
  apply top_unique
  rw [← characterL2_span_dense N L]
  apply Submodule.topologicalClosure_mono
  apply Submodule.span_le.mpr
  rintro _ ⟨k,rfl⟩
  refine ⟨(1+(fourierEnergy N L k:ℂ)) • characterL2 N L k,?_⟩
  change formResolvent N L a ((1+(fourierEnergy N L k:ℂ)) • characterL2 N L k)=_
  rw [map_smul,character_resolvent N L a ha k,smul_smul,mul_inv_cancel₀,one_smul]
  have hreal : (1:ℝ)+fourierEnergy N L k≠0 := ne_of_gt (by linarith [fourierEnergy_nonneg N L k])
  exact_mod_cast hreal

end HardSphere

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Comparison_KilledLaplace
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
namespace HardSphere
open MeasureTheory Set Filter
open scoped Topology

lemma killedTransition_clamped_continuous (N : ℕ) (L : Length) (a : ℝ) (f : ScalarL2 N L) :
    Continuous (fun t : ℝ ↦ killedTransition N L a (max 0 t) f) :=
  semigroup_clamped_continuous (killedTransition N L a) (killedTransition_add_nonneg N L a)
    (fun t _ ↦ killedTransition_apply_contraction N L a t) (killedTransition_tendsto_zero N L a) f

lemma killedLaplace_difference_tendsto (N : ℕ) (L : Length) (a : ℝ) (f : ScalarL2 N L) :
    Tendsto (fun h : ℝ ↦ (h⁻¹:ℂ) • (killedLaplace N L a f-killedTransition N L a h (killedLaplace N L a f)))
      (𝓝[>] 0) (𝓝 (allowedProjection N L a f-killedLaplace N L a f)) := by
  simpa only [killedLaplace,killedTransition_zero] using semigroupLaplace_difference_tendsto_complex
    (killedTransition N L a) (killedTransition_add_nonneg N L a)
    (killedTransition_clamped_continuous N L a)
    (fun t _ ↦ killedTransition_apply_contraction N L a t) f

end HardSphere

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_GeneratorScalar
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
noncomputable section
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
open ProbabilityTheory
namespace HardSphere
open ContinuousLinearMap Filter
open scoped Topology

lemma heatScalar_eq_exp {t x : ℝ} (ht : 0<t) (hx : 0<x) :
    heatScalar t x=Real.exp (-t*(x⁻¹-1)) := by
  rw [heatScalar_of_pos ht hx]
  congr 1
  field_simp
  ring

lemma generatorScalar_bounds {t x : ℝ} (ht : 0<t) (hx : x∈Set.Icc (0:ℝ) 1) :
    0≤generatorScalar t x ∧ generatorScalar t x≤1-x := by
  rcases eq_or_lt_of_le hx.1 with hzero | hx0
  · subst x
    simp [generatorScalar]
  have hq : 0≤x⁻¹-1 := sub_nonneg.mpr ((one_le_inv₀ hx0).mpr hx.2)
  have hh : heatScalar t x=Real.exp (-t*(x⁻¹-1)) := heatScalar_eq_exp ht hx0
  have he1 : Real.exp (-t*(x⁻¹-1))≤1 := by
    simpa using Real.exp_le_exp.mpr (neg_nonpos.mpr (mul_nonneg ht.le hq))
  have he2 := Real.add_one_le_exp (-t*(x⁻¹-1))
  have hid : t⁻¹*x*(t*(x⁻¹-1))=1-x := by field_simp
  rw [generatorScalar,hh]
  constructor
  · positivity
  · calc
      _ ≤ t⁻¹*x*(t*(x⁻¹-1)) := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ = _ := hid

lemma generatorScalar_range_error {t x : ℝ} (ht : 0<t) (hx : x∈Set.Icc (0:ℝ) 1) :
    |(generatorScalar t x-(1-x))*x|≤t := by
  have hg := generatorScalar_bounds ht hx
  rcases eq_or_lt_of_le hx.1 with hz | hx0
  · subst x
    simpa using ht.le
  let y := t*(x⁻¹-1)
  have hy : 0≤y := mul_nonneg ht.le (sub_nonneg.mpr ((one_le_inv₀ hx0).mpr hx.2))
  have hyx : y*x=t*(1-x) := by dsimp [y]; field_simp
  rw [abs_of_nonpos (mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hg.2) hx.1)]
  by_cases hy1 : y≤1
  · have he := Real.abs_exp_sub_one_sub_id_le (x := -y) (by simpa only [abs_neg,abs_of_nonneg hy] using hy1)
    have herr : -(generatorScalar t x-(1-x))*x = x^2*t⁻¹*(Real.exp (-y)-1+y) := by
      rw [generatorScalar,heatScalar_eq_exp ht hx0]
      dsimp [y]
      field_simp
      ring
    have heq : x^2*t⁻¹*y^2=t*(1-x)^2 := by
      have ht0 := ht.ne'
      calc
        _ = t⁻¹*(y*x)^2 := by ring
        _ = t⁻¹*(t*(1-x))^2 := by rw [hyx]
        _ = _ := by field_simp
    calc
      _ = -(generatorScalar t x-(1-x))*x := by ring
      _ = _ := herr
      _ ≤ x^2*t⁻¹*y^2 := mul_le_mul_of_nonneg_left
        (by simpa only [sub_neg_eq_add,neg_sq] using (le_abs_self _).trans he) (by positivity)
      _ = t*(1-x)^2 := heq
      _ ≤ t := by nlinarith [mul_nonneg ht.le (mul_nonneg hx.1 (sub_nonneg.mpr hx.2))]
  · have hy1' : 1≤y := le_of_lt (lt_of_not_ge hy1)
    have hxt : x≤t := by nlinarith [mul_le_mul_of_nonneg_right hy1' hx.1]
    nlinarith [mul_nonneg hg.1 hx.1,sq_nonneg x]

section
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [CompleteSpace F] [Nontrivial F]

lemma generatorScalar_continuous (t : ℝ) : Continuous (generatorScalar t) :=
  (continuous_const.mul continuous_id).mul (continuous_const.sub (heatScalar_smooth t).continuous)

attribute [local instance] OAI.HardSphere.instAlgebraRealContinuousLinearMapComplexId_solutions_1
omit [Nontrivial F] in
lemma generatorOperator_eq {R : F →L[ℂ] F} (hRp : R.IsPositive) (t : ℝ) :
    generatorOperator R t = t⁻¹ • ((1-cfc (p := IsSelfAdjoint) (heatScalar t) R)*R) := by
  have hf : generatorScalar t = fun x : ℝ ↦ t⁻¹*((1-heatScalar t x)*x) := by
    funext x; dsimp [generatorScalar]; ring
  have hhc := (heatScalar_smooth t).continuous
  rw [generatorOperator,hf,
    cfc_const_mul t⁻¹ (fun x:ℝ ↦ (1-heatScalar t x)*x) R
      ((continuous_const.sub hhc).mul continuous_id).continuousOn,
    cfc_mul (fun x:ℝ ↦ 1-heatScalar t x) (fun x:ℝ ↦ x) R
      (continuous_const.sub hhc).continuousOn continuous_id.continuousOn,
    cfc_sub (fun _:ℝ ↦ 1) (heatScalar t) R continuousOn_const hhc.continuousOn,
    cfc_const 1 R hRp.isSelfAdjoint,cfc_id' ℝ R hRp.isSelfAdjoint]
  simp only [map_one]

lemma generatorOperator_norm_le {R : F →L[ℂ] F} (hRp : R.IsPositive) (hRn : ‖R‖≤1)
    {t : ℝ} (ht : 0<t) : ‖generatorOperator R t‖≤1 := by
  apply norm_cfc_le zero_le_one
  intro x hx
  have hs := positive_contraction_spectrum hRp hRn hx
  have hg := generatorScalar_bounds ht hs
  simpa only [Real.norm_eq_abs,abs_of_nonneg hg.1] using hg.2.trans (by linarith [hs.1])

lemma one_sub_positive_contraction_norm_le {R : F →L[ℂ] F} (hRp : R.IsPositive) (hRn : ‖R‖≤1) :
    ‖1-R‖≤1 := by
  have he : (1:F→L[ℂ] F)-R=cfc (p := IsSelfAdjoint) (fun x:ℝ ↦ 1-x) R := by
    rw [cfc_sub (fun _:ℝ ↦ 1) (fun x:ℝ ↦ x) R continuousOn_const continuous_id.continuousOn,
      cfc_const 1 R hRp.isSelfAdjoint,cfc_id' ℝ R hRp.isSelfAdjoint]
    simp only [map_one]
  rw [he]
  apply norm_cfc_le zero_le_one
  intro x hx
  have hs := positive_contraction_spectrum hRp hRn hx
  simpa only [Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr hs.2)] using (show 1-x≤1 by linarith [hs.1])

lemma generatorOperator_range_error {R : F →L[ℂ] F} (hRp : R.IsPositive) (hRn : ‖R‖≤1)
    {t : ℝ} (ht : 0<t) : ‖(generatorOperator R t-(1-R))*R‖≤t := by
  have he : (generatorOperator R t-(1-R))*R =
      cfc (p := IsSelfAdjoint) (fun x:ℝ ↦ (generatorScalar t x-(1-x))*x) R := by
    rw [cfc_mul (fun x:ℝ ↦ generatorScalar t x-(1-x)) (fun x:ℝ ↦ x) R
      (((generatorScalar_continuous t).sub (continuous_const.sub continuous_id)).continuousOn)
        continuous_id.continuousOn,
      cfc_sub (generatorScalar t) (fun x:ℝ ↦ 1-x) R (generatorScalar_continuous t).continuousOn
        (continuous_const.sub continuous_id).continuousOn,
      cfc_sub (fun _:ℝ ↦ 1) (fun x:ℝ ↦ x) R continuousOn_const continuous_id.continuousOn,
      cfc_const 1 R hRp.isSelfAdjoint,cfc_id' ℝ R hRp.isSelfAdjoint]
    simp only [generatorOperator,map_one]
  rw [he]
  exact norm_cfc_le ht.le (fun x hx ↦ by
    simpa only [Real.norm_eq_abs] using generatorScalar_range_error ht (positive_contraction_spectrum hRp hRn hx))

lemma generatorOperator_tendsto {ι : Type*} {l : Filter ι} {d : ι→ℝ}
    (hd : ∀ i, 0<d i) (ht : Tendsto d l (𝓝 0))
    {R : F →L[ℂ] F} (hRp : R.IsPositive) (hRn : ‖R‖≤1) (hRd : DenseRange R) (f : F) :
    Tendsto (fun i ↦ generatorOperator R (d i) f) l (𝓝 ((1-R) f)) := by
  have hC (i : ι) (u : F) : ‖generatorOperator R (d i) u‖≤‖u‖ := by
    exact (le_opNorm _ _).trans (by simpa only [one_mul] using
      (mul_le_mul_of_nonneg_right (generatorOperator_norm_le hRp hRn (hd i)) (norm_nonneg u)))
  have hRange : ∀ u : F, Tendsto (fun i ↦ generatorOperator R (d i) (R u)) l (𝓝 ((1-R) (R u))) := by
    intro u
    rw [← tendsto_sub_nhds_zero_iff,tendsto_zero_iff_norm_tendsto_zero]
    apply squeeze_zero' (g := fun i ↦ d i*‖u‖) (Eventually.of_forall fun _ ↦ norm_nonneg _) ?_ ?_
    · exact Eventually.of_forall fun i ↦ by
        change ‖((generatorOperator R (d i)-(1-R))*R) u‖≤_
        exact (le_opNorm _ _).trans (mul_le_mul_of_nonneg_right
          (generatorOperator_range_error hRp hRn (hd i)) (norm_nonneg u))
    · simpa using ht.mul_const ‖u‖
  have hB (u : F) : ‖(1-R) u‖≤‖u‖ := by
    exact (le_opNorm _ _).trans (by simpa only [one_mul] using
      (mul_le_mul_of_nonneg_right (one_sub_positive_contraction_norm_le hRp hRn) (norm_nonneg u)))
  exact strong_contraction_limit_of_dense (fun i ↦ generatorOperator R (d i)) (1-R) hC hB R hRd hRange f

lemma heat_difference_resolvent_tendsto {ι : Type*} {l : Filter ι} {d : ι→ℝ}
    (hd : ∀ i, 0<d i) (ht : Tendsto d l (𝓝 0))
    {R : F →L[ℂ] F} (hRp : R.IsPositive) (hRn : ‖R‖≤1) (hRd : DenseRange R) (f : F) :
    Tendsto (fun i ↦ ((d i)⁻¹ : ℂ) • (R f-cfc (p := IsSelfAdjoint) (heatScalar (d i)) R (R f)))
      l (𝓝 (f-R f)) := by
  have h := generatorOperator_tendsto hd ht hRp hRn hRd f
  simp only [generatorOperator_eq hRp,smul_apply,mul_apply_eq_comp,
    sub_apply,one_apply_eq_self,
    RCLike.real_smul_eq_coe_smul (K := ℂ),RCLike.ofReal_inv] at h
  exact h

end
end HardSphere

end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Conditioning_PartialAlgebra
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
open MeasureTheory Set Filter ContinuousLinearMap
open scoped Topology

lemma smooth_form_pairing {N : ℕ} {L : Length} {a : ℝ} {v : Jet N L}
    (hv : v∈dirichletDomain N L a) (f : smoothAlgebra N L) :
    (∑ p : Direction N, inner ℂ (ContinuousMap.toLp 2 volume ℂ (smoothPartial f p)) (v.2 p))=
      inner ℂ (smoothLaplacian f) v.1 := by
  rw [smoothLaplacian,inner_neg_left,sum_inner]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro p _
  exact eq_neg_of_add_eq_zero_left (weak_derivative hv (partialAlgebra f p) p)

lemma SmoothTest.scalar_toLp {N : ℕ} {L : Length} {a : ℝ} (f : SmoothTest N L a) :
    f.jet.1=ContinuousMap.toLp 2 volume ℂ f.asSmooth.val := by
  apply Lp.ext
  exact f.memLp.coeFn_toLp.trans (ContinuousMap.coeFn_toLp (𝕜 := ℂ) (p := 2) volume f.asSmooth.val).symm

lemma SmoothTest.derivative_toLp {N : ℕ} {L : Length} {a : ℝ} (f : SmoothTest N L a)
    (p : Direction N) : f.jet.2 p=ContinuousMap.toLp 2 volume ℂ (smoothPartial f.asSmooth p) := by
  apply Lp.ext
  exact (f.partial_memLp p).coeFn_toLp.trans
    (ContinuousMap.coeFn_toLp (𝕜 := ℂ) (p := 2) volume (smoothPartial f.asSmooth p)).symm

lemma SmoothTest.form_pairing {N : ℕ} {L : Length} {a b : ℝ} (f : SmoothTest N L a)
    {v : Jet N L} (hv : v∈dirichletDomain N L b) :
    (∑ p : Direction N, inner ℂ (f.jet.2 p) (v.2 p))=inner ℂ (smoothLaplacian f.asSmooth) v.1 := by
  simp_rw [f.derivative_toLp]
  exact smooth_form_pairing hv f.asSmooth

lemma SmoothTest.free_resolvent {N : ℕ} {L : Length} {a : ℝ} (f : SmoothTest N L a) :
    formResolvent N L (-1) (f.jet.1+smoothLaplacian f.asSmooth)=f.jet.1 := by
  let ug : hilbertDomain N L (-1) := ⟨(hilbertJetEquiv N L).symm f.jet,by
    change hilbertJetEquiv N L ((hilbertJetEquiv N L).symm f.jet)∈dirichletDomain N L (-1)
    rw [ContinuousLinearEquiv.apply_symm_apply]
    exact subset_closure ⟨f.freeTest,rfl⟩⟩
  have heq : (scalarEmbedding N L (-1)).adjoint (f.jet.1+smoothLaplacian f.asSmooth)=ug := by
    apply ext_inner_right ℂ
    intro v
    rw [adjoint_inner_left,inner_add_left]
    change _=inner ℂ (ug : HilbertJet N L) (v : HilbertJet N L)
    rw [hilbertJet_inner]
    have hgu : hilbertJetEquiv N L (ug : HilbertJet N L)=f.jet := by simp [ug]
    rw [hgu]
    congr 1
    exact (f.form_pairing v.property).symm
  change scalarEmbedding N L (-1) ((scalarEmbedding N L (-1)).adjoint _)=_
  rw [heq]
  change (hilbertJetEquiv N L ((hilbertJetEquiv N L).symm f.jet)).1=f.jet.1
  rw [ContinuousLinearEquiv.apply_symm_apply]

lemma SmoothTest.free_generator {N : ℕ} {L : Length} {a : ℝ} (f : SmoothTest N L a)
    {ι : Type*} {l : Filter ι} {d : ι→ℝ} (hd : ∀ i,0<d i) (ht : Tendsto d l (𝓝 0)) :
    Tendsto (fun i ↦ ((d i)⁻¹ : ℂ) • (f.jet.1-freeTransition N L (d i) f.jet.1))
      l (𝓝 (smoothLaplacian f.asSmooth)) := by
  rcases subsingleton_or_nontrivial (ScalarL2 N L) with h | h
  · convert tendsto_const_nhds (x := smoothLaplacian f.asSmooth) using 1
    all_goals try with_reducible_and_instances rfl
  have hlim := heat_difference_resolvent_tendsto hd ht (formResolvent_isPositive N L (-1))
    (formResolvent_norm_le_one N L (-1)) (freeResolvent_denseRange N L (-1) (by norm_num))
    (f.jet.1+smoothLaplacian f.asSmooth)
  simp only [f.free_resolvent] at hlim
  change Tendsto (fun i ↦ ((d i)⁻¹:ℂ) • (f.jet.1-formHeat N L (-1) (d i) f.jet.1))
    l (𝓝 (f.jet.1+smoothLaplacian f.asSmooth-f.jet.1)) at hlim
  simp_rw [← freeTransition_eq_formHeat N L (-1) (by norm_num) (hd _)] at hlim
  simpa only [add_sub_cancel_left] using hlim

end HardSphere

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Orbitals_FieldApply
attribute [-instance] _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Rescaling.config_haar _root_.OAI.HardSphere.bridgeEndpointBase_finite _root_.OAI.HardSphere.configurationBorel _root_.OAI.HardSphere.configurationPathBorel _root_.OAI.HardSphere.configurationPathMeasurable _root_.OAI.HardSphere.coordinateBridge_probability _root_.OAI.HardSphere.coordinateWiener_probability _root_.OAI.HardSphere.endpointWeightedBase_sfinite _root_.OAI.HardSphere.freePathLaw_finite_deletion _root_.OAI.HardSphere.gaussianCoordinates_probability _root_.OAI.HardSphere.hilbertDomain_closed _root_.OAI.HardSphere.hilbertDomain_complete _root_.OAI.HardSphere.killedPathLaw_finite_deletion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal BigOperators

namespace L2Contraction
variable {α E F G : Type*} [MeasurableSpace α] {μ : Measure α}
  [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedAddCommGroup G]

lemma unifIntegrable_of_domination {ι : Type*} {p : ℝ≥0∞}
    {f : ι → α → E} {b : α → F} (hp : 1 ≤ p) (hp' : p ≠ ∞) (hb : MemLp b p μ)
    (hf_meas : ∀ index, AEStronglyMeasurable (f index) μ)
    (hbound : ∀ n, ∀ᵐ x ∂μ, ‖f n x‖ ≤ ‖b x‖) : UnifIntegrable f p μ := by
  intro ε hε
  obtain ⟨δ, hδ, hi⟩ := unifIntegrable_const (ι := ι) hp hp' hb hε
  refine ⟨δ, hδ, fun index region hregion hμs ↦ le_trans ?_ (hi index region hregion hμs)⟩
  refine eLpNorm_mono_ae ?_
  filter_upwards [hbound index] with x hx
  by_cases hxr : x ∈ region <;> simp [Set.indicator, hxr, hx]

lemma tendsto_toLp_of_domination [IsFiniteMeasure μ]
    {f : ℕ → α → E} {g : α → E} {b : α → F}
    (hf : ∀ n, MemLp (f n) 2 μ) (hg : MemLp g 2 μ) (hb : MemLp b 2 μ)
    (hbound : ∀ n, ∀ᵐ x ∂μ, ‖f n x‖ ≤ ‖b x‖)
    (hl : ∀ᵐ x ∂μ, Tendsto (fun n ↦ f n x) atTop (𝓝 (g x))) :
    Tendsto (fun n ↦ (hf n).toLp (f n)) atTop (𝓝 (hg.toLp g)) := by
  apply (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' f hf g hg).2
  exact tendsto_Lp_finite_of_tendsto_ae (by norm_num) (by norm_num)
    (fun n ↦ (hf n).aestronglyMeasurable) hg
    (unifIntegrable_of_domination (by norm_num) (by norm_num) hb
      (fun index ↦ (hf index).aestronglyMeasurable) hbound) hl

section Field
variable [NormedSpace ℝ E] [NormedSpace ℝ F]
    (A : α → E →L[ℝ] F) (hA : AEStronglyMeasurable A μ)
    (hbound : ∀ᵐ x ∂μ, ‖A x‖ ≤ 1)
include hA hbound

lemma coe_fieldApply (v : Lp E 2 μ) :
    fieldApply A hA hbound v =ᵐ[μ] fun x ↦ A x (v x) :=
  MemLp.coeFn_toLp _

lemma norm_fieldApply_le (v : Lp E 2 μ) : ‖fieldApply A hA hbound v‖ ≤ ‖v‖ := by
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [coe_fieldApply A hA hbound v, hbound] with x hx hb
  rw [hx]
  exact (A x).le_opNorm (v x) |>.trans (by nlinarith [norm_nonneg (v x)])

lemma fieldApply_sub (v w : Lp E 2 μ) :
    fieldApply A hA hbound (v - w) = fieldApply A hA hbound v - fieldApply A hA hbound w := by
  apply Lp.ext
  filter_upwards [coe_fieldApply A hA hbound (v - w), coe_fieldApply A hA hbound v,
    coe_fieldApply A hA hbound w, Lp.coeFn_sub v w,
    Lp.coeFn_sub (fieldApply A hA hbound v) (fieldApply A hA hbound w)] with x h1 h2 h3 h4 h5
  simp only [h1, h4, Pi.sub_apply, map_sub, h5, h2, h3]

lemma norm_fieldApply_sub_le (v w : Lp E 2 μ) :
    ‖fieldApply A hA hbound v - fieldApply A hA hbound w‖ ≤ ‖v - w‖ := by
  rw [← fieldApply_sub]
  exact norm_fieldApply_le A hA hbound _
end Field

variable [NormedSpace ℝ E] [NormedSpace ℝ F]

lemma tendsto_fieldApply_fixed [IsFiniteMeasure μ]
    (A : G → E →L[ℝ] F) (hA : Continuous A) (hb : ∀ z, ‖A z‖ ≤ 1)
    (u : ℕ → Lp G 2 μ) (u₀ : Lp G 2 μ)
    (hu : ∀ᵐ x ∂μ, Tendsto (fun n ↦ u n x) atTop (𝓝 (u₀ x))) (v : Lp E 2 μ) :
    Tendsto (fun n ↦ fieldApply (fun x ↦ A (u n x)) (coeff_meas A hA (u n))
      (Eventually.of_forall (fun x ↦ hb (u n x))) v) atTop
      (𝓝 (fieldApply (fun x ↦ A (u₀ x)) (coeff_meas A hA u₀)
        (Eventually.of_forall (fun x ↦ hb (u₀ x))) v)) := by
  apply tendsto_toLp_of_domination _ _ (Lp.memLp v)
  · intro n
    exact Eventually.of_forall fun x ↦ (A (u n x)).le_opNorm (v x) |>.trans
      (by nlinarith [norm_nonneg (v x), hb (u n x)])
  · filter_upwards [hu] with x hx
    exact ((ContinuousLinearMap.apply ℝ F (v x)).continuous.tendsto _).comp
      (hA.continuousAt.tendsto.comp hx)

lemma tendsto_fieldApply [IsFiniteMeasure μ]
    (A : G → E →L[ℝ] F) (hA : Continuous A) (hb : ∀ z, ‖A z‖ ≤ 1)
    (u : ℕ → Lp G 2 μ) (u₀ : Lp G 2 μ)
    (hu : ∀ᵐ x ∂μ, Tendsto (fun n ↦ u n x) atTop (𝓝 (u₀ x)))
    (v : ℕ → Lp E 2 μ) (v₀ : Lp E 2 μ) (hv : Tendsto v atTop (𝓝 v₀)) :
    Tendsto (fun n ↦ fieldApply (fun x ↦ A (u n x)) (coeff_meas A hA (u n))
      (Eventually.of_forall (fun x ↦ hb (u n x))) (v n)) atTop
      (𝓝 (fieldApply (fun x ↦ A (u₀ x)) (coeff_meas A hA u₀)
        (Eventually.of_forall (fun x ↦ hb (u₀ x))) v₀)) := by
  have hdiff : Tendsto (fun n ↦
      fieldApply (fun x ↦ A (u n x)) (coeff_meas A hA (u n))
        (Eventually.of_forall (fun x ↦ hb (u n x))) (v n) -
      fieldApply (fun x ↦ A (u n x)) (coeff_meas A hA (u n))
        (Eventually.of_forall (fun x ↦ hb (u n x))) v₀) atTop (𝓝 0) := by
    apply squeeze_zero_norm (fun n ↦ norm_fieldApply_sub_le _ _ _ (v n) v₀)
    simpa using (hv.sub_const v₀).norm
  simpa only [sub_add_cancel, zero_add] using
    hdiff.add (tendsto_fieldApply_fixed A hA hb u u₀ hu v₀)

end L2Contraction

namespace HardSphere

namespace SmoothContraction
variable (f : SmoothContraction)

lemma coe_onScalar {N : ℕ} {L : Length} (u : ScalarL2 N L) :
    f.onScalar u =ᵐ[volume] fun X ↦ f.toFun (u X) := f.lipschitz.coeFn_compLp f.zero u

lemma coe_onPartial {N : ℕ} {L : Length} (u v : ScalarL2 N L) :
    f.onPartial u v =ᵐ[volume] fun X ↦ fderiv ℝ f.toFun (u X) (v X) :=
  L2Contraction.coe_fieldApply _ _ _ v

lemma jet_composeTest {N : ℕ} {L : Length} {a : ℝ}
    (g : SmoothTest N L a) : (f.composeTest g).jet = f.onJet g.jet := by
  apply Prod.ext
  · apply Lp.ext
    filter_upwards [(f.composeTest g).memLp.coeFn_toLp, f.coe_onScalar g.jet.1,
      g.memLp.coeFn_toLp] with X h1 h2 h3
    change g.jet.1 X = g.toFun X at h3
    change (f.composeTest g).jet.1 X = f.toFun (g.toFun X) at h1
    change (f.composeTest g).jet.1 X = f.onScalar g.jet.1 X
    rw [h1, h2, h3]
  · funext p
    apply Lp.ext
    filter_upwards [(f.composeTest g).partial_memLp p |>.coeFn_toLp,
      f.coe_onPartial g.jet.1 (g.jet.2 p), g.memLp.coeFn_toLp,
      (g.partial_memLp p).coeFn_toLp] with X h1 h2 h3 h4
    change (f.composeTest g).jet.2 p X = coordDerivative N L (f.toFun ∘ g.toFun) p X at h1
    change g.jet.1 X = g.toFun X at h3
    change g.jet.2 p X = coordDerivative N L g.toFun p X at h4
    change (f.composeTest g).jet.2 p X = f.onPartial g.jet.1 (g.jet.2 p) X
    rw [h1, h2]
    rw [f.coordDerivative_comp g p, h3, h4]

lemma onJet_mem_domain {N : ℕ} {L : Length} {a : ℝ} {u : Jet N L}
    (hu : u ∈ dirichletDomain N L a) : f.onJet u ∈ dirichletDomain N L a := by
  obtain ⟨v, hv, hl⟩ := mem_closure_iff_seq_limit.mp hu
  choose g hg using hv
  have hl' : Tendsto (fun n ↦ (g n).jet) atTop (𝓝 u) := by simpa only [hg] using hl
  have hs := (continuous_fst.tendsto u).comp hl'
  obtain ⟨ns, hns, hae⟩ := (tendstoInMeasure_of_tendsto_Lp hs).exists_seq_tendsto_ae
  have hlim : Tendsto (fun n ↦ (f.composeTest (g (ns n))).jet) atTop (𝓝 (f.onJet u)) := by
    simp only [f.jet_composeTest]
    apply Tendsto.prodMk_nhds
    · exact (f.lipschitz.continuous_compLp f.zero).continuousAt.tendsto.comp
        (hs.comp hns.tendsto_atTop)
    · apply tendsto_pi_nhds.mpr
      intro p
      apply L2Contraction.tendsto_fieldApply _ f.derivative_continuous f.derivative_le
        _ u.1 hae _ (u.2 p)
      exact ((continuous_apply p).tendsto u.2).comp
        ((continuous_snd.tendsto u).comp (hl'.comp hns.tendsto_atTop))
  exact isClosed_closure.mem_of_tendsto hlim
    (Eventually.of_forall fun n ↦ subset_closure ⟨f.composeTest (g (ns n)), rfl⟩)

end SmoothContraction
end HardSphere

open scoped RealInnerProductSpace

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Cutoffs_Regularize
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
open scoped Topology ENNReal BigOperators
open scoped RealInnerProductSpace
namespace ComplexRegularization

lemma tendsto_regularize (z : ℂ) {e : ℕ → ℝ} (he : Tendsto e atTop (𝓝 0)) :
    Tendsto (fun n ↦ regularize (e n) z) atTop (𝓝 (‖z‖ : ℂ)) := by
  have h : Tendsto (fun n ↦ Real.sqrt (‖z‖ ^ 2 + e n ^ 2) - e n) atTop (𝓝 ‖z‖) := by
    have h := (((tendsto_const_nhds (x := ‖z‖ ^ 2)).add (he.pow 2)).sqrt.sub he)
    simpa using h

  exact Complex.continuous_ofReal.tendsto _ |>.comp h

end ComplexRegularization

namespace HardSphere
open ComplexRegularization

lemma coe_modulusScalar {N : ℕ} {L : Length} (u : ScalarL2 N L) :
    modulusScalar u =ᵐ[volume] fun X ↦ (‖u X‖ : ℂ) :=
  modulus_lipschitz.coeFn_compLp (by simp) u

lemma tendsto_regularization_partial {N : ℕ} {L : Length} (u v : ScalarL2 N L) :
    Tendsto (fun n ↦ (regularization (regularizationScale n) (regularizationScale_pos n)).onPartial u v)
      atTop (𝓝 (modulusPartial u v)) := by
  refine L2Contraction.tendsto_toLp_of_domination
    (fun n ↦ L2Contraction.field_memLp _
      (L2Contraction.coeff_meas _ (regularization _ (regularizationScale_pos n)).derivative_continuous u)
      (Eventually.of_forall fun X ↦ (regularization _ (regularizationScale_pos n)).derivative_le (u X)) v)
    (L2Contraction.field_memLp _ (modulusCoefficient_meas u)
      (Eventually.of_forall fun X ↦ differential_le 0 (u X)) v)
    (Lp.memLp v) ?_ ?_
  · intro n
    apply Eventually.of_forall
    intro X
    change ‖fderiv ℝ (regularize (regularizationScale n)) (u X) (v X)‖ ≤ ‖v X‖
    rw [fderiv_eq (regularizationScale_pos n)]
    exact differential_apply_le _ _ _
  · apply Eventually.of_forall
    intro X
    change Tendsto (fun n ↦ fderiv ℝ (regularize (regularizationScale n)) (u X) (v X))
      atTop (𝓝 (differential 0 (u X) (v X)))
    simp only [fderiv_eq (regularizationScale_pos _)]
    exact ((ContinuousLinearMap.apply ℝ ℂ (v X)).continuous.tendsto _).comp
      (tendsto_differential (u X) tendsto_regularizationScale)

lemma tendsto_regularization_scalar {N : ℕ} {L : Length} (u : ScalarL2 N L) :
    Tendsto (fun n ↦ (regularization (regularizationScale n) (regularizationScale_pos n)).onScalar u)
      atTop (𝓝 (modulusScalar u)) := by
  have he (f : ℂ → ℂ) (hf : LipschitzWith 1 f) (h0 : f 0 = 0) :
      hf.compLp h0 u = (hf.comp_memLp h0 (Lp.memLp u)).toLp (f ∘ u) := by
    apply Lp.ext
    exact (hf.coeFn_compLp h0 u).trans (MemLp.coeFn_toLp _).symm
  simp only [SmoothContraction.onScalar, modulusScalar, he]
  refine L2Contraction.tendsto_toLp_of_domination
    (fun n ↦ (regularization _ (regularizationScale_pos n)).lipschitz.comp_memLp
      (regularization _ (regularizationScale_pos n)).zero (Lp.memLp u))
    (modulus_lipschitz.comp_memLp (by simp) (Lp.memLp u)) (Lp.memLp u) ?_ ?_
  · intro n
    apply Eventually.of_forall
    intro X
    have h := (regularization (regularizationScale n) (regularizationScale_pos n)).lipschitz.norm_sub_le
      (u X) 0
    simpa only [SmoothContraction.zero, sub_zero, NNReal.coe_one, one_mul, Function.comp_apply] using h
  · exact Eventually.of_forall fun X ↦ tendsto_regularize (u X) tendsto_regularizationScale

lemma tendsto_regularization_jet {N : ℕ} {L : Length} (u : Jet N L) :
    Tendsto (fun n ↦ (regularization (regularizationScale n) (regularizationScale_pos n)).onJet u)
      atTop (𝓝 (modulusJet u)) :=
  (tendsto_regularization_scalar u.1).prodMk_nhds
    (tendsto_pi_nhds.mpr fun p ↦ tendsto_regularization_partial u.1 (u.2 p))

lemma modulusJet_mem_domain {N : ℕ} {L : Length} {a : ℝ} {u : Jet N L}
    (hu : u ∈ dirichletDomain N L a) : modulusJet u ∈ dirichletDomain N L a :=
  isClosed_closure.mem_of_tendsto (tendsto_regularization_jet u)
    (Eventually.of_forall fun n ↦
      (regularization (regularizationScale n) (regularizationScale_pos n)).onJet_mem_domain hu)

lemma norm_modulusScalar {N : ℕ} {L : Length} (u : ScalarL2 N L) :
    ‖modulusScalar u‖ = ‖u‖ := by
  have he : ∀ᵐ X ∂volume, ‖modulusScalar u X‖ = ‖u X‖ := by
    filter_upwards [coe_modulusScalar u] with X hX
    simp [hX]
  exact le_antisymm (Lp.norm_le_norm_of_ae_le (he.mono fun _ hx ↦ hx.le))
    (Lp.norm_le_norm_of_ae_le (he.mono fun _ hx ↦ hx.ge))

lemma energy_modulusJet_le {N : ℕ} {L : Length} (u : Jet N L) :
    energy (modulusJet u) ≤ energy u := by
  apply Finset.sum_le_sum
  intro p _
  apply pow_le_pow_left₀ (norm_nonneg _) _ 2
  exact L2Contraction.norm_fieldApply_le _ (modulusCoefficient_meas u.1)
    (Eventually.of_forall fun X ↦ differential_le 0 (u.1 X)) (u.2 p)

lemma bosonic_modulusScalar {N : ℕ} {L : Length} {u : ScalarL2 N L}
    (hu : bosonic u) : bosonic (modulusScalar u) := by
  intro σ
  have hp : MeasurePreserving (fun X : Configuration N L ↦ fun i ↦ X (σ i)) volume volume := by
    have h := volume_measurePreserving_piCongrLeft (fun _ : Fin N ↦ Torus L) σ.symm
    convert h using 1
    all_goals try with_reducible_and_instances rfl
    funext X i
    simp [MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply]
  have hae := hp.quasiMeasurePreserving.ae_eq_comp (coe_modulusScalar u)
  filter_upwards [hae, coe_modulusScalar u, hu σ] with X h1 h2 h3
  change modulusScalar u (fun i ↦ X (σ i)) = (‖u (fun i ↦ X (σ i))‖ : ℂ) at h1
  rw [h1, h2, h3]

lemma IsGroundVector.modulus {N : ℕ} {L : Length} {a : ℝ} {u : Jet N L}
    (hu : IsGroundVector N L a u) : IsGroundVector N L a (modulusJet u) := by
  refine ⟨modulusJet_mem_domain hu.1, bosonic_modulusScalar hu.2.1, ?_, ?_⟩
  · exact (norm_modulusScalar u.1).trans hu.2.2.1
  · intro v hv hb hn
    exact (energy_modulusJet_le u).trans (hu.2.2.2 v hv hb hn)

lemma IsGroundVector.energy_modulus {N : ℕ} {L : Length} {a : ℝ} {u : Jet N L}
    (hu : IsGroundVector N L a u) : energy (modulusJet u) = energy u :=
  le_antisymm (energy_modulusJet_le u)
    (hu.2.2.2 _ hu.modulus.1 hu.modulus.2.1 hu.modulus.2.2.1)

end HardSphere

end
end
end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_PathBounds_PathTailConstant
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
open ProbabilityTheory
namespace HardSphere
open Wiener

lemma staysAllowed_of_neg (N : ℕ) (L : Length) {a : ℝ} (ha : a<0) :
    staysAllowed N L a=Set.univ := by
  ext ω
  simp only [staysAllowed,Set.mem_ofPred_eq,Set.mem_univ,iff_true]
  rw [allowed_of_neg N L ha]
  exact Set.subset_univ _

lemma killedObservable_of_neg (N : ℕ) (L : Length) {a : ℝ} (ha : a<0)
    (g : Configuration N L → ℂ) (ω : ConfigurationPath N L) :
    killedObservable N L a g ω=g (ω 1) := by
  simp only [killedObservable,staysAllowed_of_neg N L ha,Set.indicator_univ]

lemma killedTransition_of_neg (N : ℕ) (L : Length) {a : ℝ} (ha : a<0) (t : ℝ) :
    killedTransition N L a t=freeTransition N L t := by
  apply ContinuousLinearMap.ext
  intro g
  apply ext_inner_left ℂ
  intro f
  rw [killedTransition_pairing,freeTransition_pairing]
  simp only [killedPathLaw,staysAllowed_of_neg N L ha,Measure.restrict_univ]

lemma freeTrajectory_dist_le (N : ℕ) (L : Length) (t : ℝ)
    {w : CoordinatePaths N} {B : ℝ} (hB : 0≤B)
    (hw : ∀ p, ‖w p‖≤B) (X : Configuration N L) (s u : Time) :
    dist (freeTrajectory N L t w X s) (freeTrajectory N L t w X u) ≤
      2*Real.sqrt (2*t)*B := by
  have hC : 0≤2*Real.sqrt (2*t)*B := by positivity
  apply (dist_pi_le_iff hC).mpr
  intro i
  apply (dist_pi_le_iff hC).mpr
  intro j
  change dist (X i j+((Real.sqrt (2*t)*w (i,j) s : ℝ):AddCircle L.val))
    (X i j+((Real.sqrt (2*t)*w (i,j) u : ℝ):AddCircle L.val))≤_
  rw [dist_add_left,dist_eq_norm,← QuotientAddGroup.mk_sub]
  calc
    _ ≤ ‖Real.sqrt (2*t)*w (i,j) s-Real.sqrt (2*t)*w (i,j) u‖ :=
      QuotientAddGroup.norm_mk_le_norm
    _ = Real.sqrt (2*t)*‖w (i,j) s-w (i,j) u‖ := by
      rw [← mul_sub,norm_mul,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _)]
    _ ≤ Real.sqrt (2*t)*(B+B) := by
      apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
      exact (norm_sub_le _ _).trans (add_le_add
        ((w (i,j)).norm_coe_le_norm s |>.trans (hw (i,j)))
        ((w (i,j)).norm_coe_le_norm u |>.trans (hw (i,j))))
    _ = _ := by ring

lemma killedObservable_eq_of_small_path (N : ℕ) (L : Length) (a t : ℝ)
    (g : Configuration N L → ℂ) {δ B : ℝ} (hB : 0≤B)
    (hδ : Metric.cthickening δ (tsupport g) ⊆ allowed N L a)
    (ht : 2*Real.sqrt (2*t)*B≤δ)
    {w : CoordinatePaths N} (hw : ∀ p, ‖w p‖≤B) (X : Configuration N L) :
    killedObservable N L a g (freeTrajectory N L t w X)=g (freeTrajectory N L t w X 1) := by
  by_cases hg : g (freeTrajectory N L t w X 1)=0
  · simp only [killedObservable]
    by_cases he : freeTrajectory N L t w X∈staysAllowed N L a
    · simp only [Set.indicator_of_mem he]
    · simp only [Set.indicator_of_notMem he,hg]
  · have hs : freeTrajectory N L t w X 1∈tsupport g := subset_closure hg
    have he : freeTrajectory N L t w X∈staysAllowed N L a := by
      rintro _ ⟨s,rfl⟩
      apply hδ
      exact Metric.mem_cthickening_of_dist_le _ _ _ _ hs
        ((freeTrajectory_dist_le N L t hB hw X s 1).trans ht)
    simp only [killedObservable,Set.indicator_of_mem he]

lemma coordinateWiener_tail8 (N : ℕ) {B : ℝ} (hB : 0<B) :
    coordinateWiener N {w | ∃ p, B*normMultiplier<‖w p‖} ≤
      (Fintype.card (Direction N):ℝ≥0∞)*(ENNReal.ofReal B)⁻¹^8 *
        ((1+(1-(2:ℝ≥0∞)*(4/3)⁻¹^8)⁻¹)*moment8) := by
  have he : {w : CoordinatePaths N | ∃ p, B*normMultiplier<‖w p‖} =
      ⋃ p : Direction N, {w | B*normMultiplier<‖w p‖} := by ext w; simp
  rw [he]
  refine (measure_iUnion_fintype_le _ _).trans ?_
  calc
    _ = ∑ _p : Direction N, wiener {w | B*normMultiplier<‖w‖} := by
      apply Finset.sum_congr rfl
      intro p _
      exact (measurePreserving_eval (fun _ : Direction N ↦ wiener) p).measure_preimage
        (measurableSet_lt measurable_const measurable_norm).nullMeasurableSet
    _ ≤ ∑ _p : Direction N, (ENNReal.ofReal B)⁻¹^8 *
        ((1+(1-(2:ℝ≥0∞)*(4/3)⁻¹^8)⁻¹)*moment8) :=
      Finset.sum_le_sum fun _ _ ↦ norm_wiener_tail8 hB
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_assoc]

lemma killedAverage_free_bound (N : ℕ) (L : Length) (a t : ℝ)
    (g : C(Configuration N L,ℂ)) {δ B : ℝ} (hB : 0<B)
    (hδ : Metric.cthickening δ (tsupport g) ⊆ allowed N L a)
    (ht : 2*Real.sqrt (2*t)*(B*normMultiplier)≤δ) (X : Configuration N L) :
    ‖killedAverage N L a t g X-killedAverage N L (-1) t g X‖ ≤
      ‖g‖*(coordinateWiener N).real {w | ∃ p, B*normMultiplier<‖w p‖} := by
  let E : Set (CoordinatePaths N) := {w | ∃ p, B*normMultiplier<‖w p‖}
  have hE : MeasurableSet E := by
    have he : E = ⋃ p : Direction N, {w : CoordinatePaths N | B*normMultiplier<‖w p‖} := by ext w; simp [E]
    rw [he]
    apply MeasurableSet.iUnion
    intro p
    exact measurableSet_lt measurable_const (measurable_pi_apply p |>.norm)
  have hi (b : ℝ) : Integrable (fun w : CoordinatePaths N ↦
      killedObservable N L b g (freeTrajectory N L t w X)) (coordinateWiener N) := by
    apply (integrable_const ‖g‖).mono'
    · exact ((killedObservable_measurable N L b g.continuous.measurable).comp
        ((freeTrajectory_continuous N L t).comp (continuous_id.prodMk continuous_const)).measurable).aestronglyMeasurable
    · exact Eventually.of_forall fun _ ↦ killedObservable_bound N L b (norm_nonneg g) g.norm_coe_le_norm _
  rw [killedAverage,killedAverage,← integral_sub (hi a) (hi (-1))]
  calc
    _ ≤ ∫ w, E.indicator (fun _ ↦ ‖g‖) w ∂coordinateWiener N := by
      apply norm_integral_le_of_norm_le
      · exact (integrable_const ‖g‖).indicator hE
      · filter_upwards [] with w
        rw [killedObservable_of_neg N L (by norm_num : (-1:ℝ)<0)]
        by_cases he : w∈E
        · rw [Set.indicator_of_mem he]
          by_cases ha : freeTrajectory N L t w X∈staysAllowed N L a
          · simp only [killedObservable,Set.indicator_of_mem ha,sub_self,norm_zero]
            exact norm_nonneg g
          · simp only [killedObservable,Set.indicator_of_notMem ha,zero_sub,norm_neg]
            exact g.norm_coe_le_norm _
        · rw [Set.indicator_of_notMem he]
          have hw : ∀ p, ‖w p‖≤B*normMultiplier := by
            intro p
            exact le_of_not_gt fun h ↦ he ⟨p,h⟩
          rw [killedObservable_eq_of_small_path N L a t g
            (mul_nonneg hB.le normMultiplier_pos.le) hδ ht hw X,sub_self,norm_zero]
    _ = _ := by rw [integral_indicator_const _ hE]; simp only [smul_eq_mul,mul_comm]; rfl

lemma pathTailConstant_nonneg (N : ℕ) : 0 ≤ pathTailConstant N := ENNReal.toReal_nonneg

lemma coordinateWiener_tail8_real (N : ℕ) {B : ℝ} (hB : 0<B) :
    (coordinateWiener N).real {w | ∃ p, B*normMultiplier<‖w p‖} ≤
      pathTailConstant N * B⁻¹^8 := by
  have hfin : (Fintype.card (Direction N) : ℝ≥0∞) * (ENNReal.ofReal B)⁻¹^8 *
      ((1+(1-(2:ℝ≥0∞)*(4/3)⁻¹^8)⁻¹)*moment8) ≠ ∞ := by
    apply ENNReal.mul_ne_top _ norm_wiener_tail_constant_finite
    apply ENNReal.mul_ne_top (ENNReal.natCast_ne_top _)
    apply ENNReal.pow_ne_top
    rw [ENNReal.inv_ne_top]
    simpa using hB
  have h := ENNReal.toReal_mono hfin (coordinateWiener_tail8 N hB)
  simpa only [Measure.real,ENNReal.toReal_mul,ENNReal.toReal_pow,ENNReal.toReal_inv,
    ENNReal.toReal_ofReal hB.le, pathTailConstant,mul_assoc,mul_left_comm,mul_comm] using h

lemma killedAverage_free_order4 (N : ℕ) (L : Length) (a : ℝ)
    (g : C(Configuration N L,ℂ)) {δ : ℝ} (hδpos : 0<δ)
    (hδ : Metric.cthickening δ (tsupport g) ⊆ allowed N L a)
    {t : ℝ} (ht : 0<t) (X : Configuration N L) :
    ‖killedAverage N L a t g X-killedAverage N L (-1) t g X‖ ≤
      (‖g‖*pathTailConstant N*(2*normMultiplier/δ)^8*16)*t^4 := by
  let B : ℝ := δ/(2*Real.sqrt (2*t)*normMultiplier)
  have hs : 0<Real.sqrt (2*t) := Real.sqrt_pos.2 (by positivity)
  have hB : 0<B := div_pos hδpos (mul_pos (mul_pos (by norm_num) hs) normMultiplier_pos)
  have hBt : 2*Real.sqrt (2*t)*(B*normMultiplier)≤δ := by
    dsimp [B]
    have hn := normMultiplier_pos.ne'
    field_simp
    exact le_rfl
  calc
    _ ≤ ‖g‖*(coordinateWiener N).real {w | ∃ p, B*normMultiplier<‖w p‖} :=
      killedAverage_free_bound N L a t g hB hδ hBt X
    _ ≤ ‖g‖*(pathTailConstant N*B⁻¹^8) :=
      mul_le_mul_of_nonneg_left (coordinateWiener_tail8_real N hB) (norm_nonneg g)
    _ = _ := by
      have hsq := Real.sq_sqrt (by positivity : 0≤2*t)
      dsimp [B]
      rw [inv_div]
      calc
        _ = ‖g‖ * pathTailConstant N * (2 * normMultiplier / δ)^8 *
            (Real.sqrt (2*t)^2)^4 := by ring
        _ = _ := by rw [hsq]; ring

lemma killedTransition_continuous_ae_core (N : ℕ) (L : Length) (a t : ℝ)
    (g : C(Configuration N L,ℂ)) :
    killedTransition N L a t (ContinuousMap.toLp 2 volume ℂ g) =ᵐ[volume]
      killedAverage N L a t g := by
  have hgLp : MemLp (fun X ↦ g X) 2 (volume : Measure (Configuration N L)) :=
    MemLp.of_bound g.continuous.measurable.aestronglyMeasurable ‖g‖
      (Eventually.of_forall g.norm_coe_le_norm)
  have hge : ContinuousMap.toLp 2 volume ℂ g = hgLp.toLp g := by
    apply Lp.ext
    exact (ContinuousMap.coeFn_toLp (𝕜 := ℂ) (p := 2) volume g).trans hgLp.coeFn_toLp.symm
  rw [hge,killedTransition_bounded N L a t g.continuous.measurable
    hgLp (norm_nonneg g) g.norm_coe_le_norm]
  exact MemLp.coeFn_toLp _

lemma killedTransition_free_order4 (N : ℕ) (L : Length) (a : ℝ)
    (g : C(Configuration N L,ℂ)) (hg : tsupport g⊆allowed N L a) :
    ∃ C : ℝ, 0≤C ∧ ∀ t : ℝ, 0<t →
      ‖killedTransition N L a t (ContinuousMap.toLp 2 volume ℂ g)-
        freeTransition N L t (ContinuousMap.toLp 2 volume ℂ g)‖ ≤ C*t^4 := by
  obtain ⟨δ,hδpos,hδ⟩ := (isClosed_tsupport g).isCompact.exists_cthickening_subset_open
    (isOpen_allowed N L a) hg
  let C0 : ℝ := ‖g‖*pathTailConstant N*(2*normMultiplier/δ)^8*16
  have hC0 : 0≤C0 := by
    have hp := pathTailConstant_nonneg N
    dsimp [C0]
    positivity
  let M : ℝ := (measureUnivNNReal (volume : Measure (Configuration N L)) : ℝ) ^ (2:ℝ≥0∞).toReal⁻¹
  have hM : 0≤M := Real.rpow_nonneg (NNReal.coe_nonneg _) _
  refine ⟨M*C0,mul_nonneg hM hC0,?_⟩
  intro t ht
  rw [← killedTransition_of_neg N L (by norm_num : (-1:ℝ)<0)]
  have hb : ∀ᵐ X ∂(volume : Measure (Configuration N L)),
      ‖(killedTransition N L a t (ContinuousMap.toLp 2 volume ℂ g)-
        killedTransition N L (-1) t (ContinuousMap.toLp 2 volume ℂ g)) X‖≤C0*t^4 := by
    filter_upwards [Lp.coeFn_sub (killedTransition N L a t (ContinuousMap.toLp 2 volume ℂ g))
      (killedTransition N L (-1) t (ContinuousMap.toLp 2 volume ℂ g)),
      killedTransition_continuous_ae_core N L a t g,killedTransition_continuous_ae_core N L (-1) t g] with X hsub ha hb
    rw [hsub,Pi.sub_apply,ha,hb]
    exact killedAverage_free_order4 N L a g hδpos hδ ht X
  exact (Lp.norm_le_of_ae_bound (mul_nonneg hC0 (by positivity)) hb).trans_eq (by dsimp [M]; ring)

lemma killedTransition_free_firstOrder (N : ℕ) (L : Length) (a : ℝ)
    (g : C(Configuration N L,ℂ)) (hg : tsupport g⊆allowed N L a) :
    Tendsto (fun t : ℝ ↦ (t⁻¹:ℝ) •
      (killedTransition N L a t (ContinuousMap.toLp 2 volume ℂ g)-
        freeTransition N L t (ContinuousMap.toLp 2 volume ℂ g)))
      (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨C,hC,hb⟩ := killedTransition_free_order4 N L a g hg
  rw [tendsto_zero_iff_norm_tendsto_zero]
  apply squeeze_zero' (g := fun t : ℝ ↦ C*t^3) (Eventually.of_forall fun t ↦ norm_nonneg _) ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with t ht
    have ht' : 0<t := ht
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr ht')]
    calc
      _ ≤ t⁻¹*(C*t^4) := mul_le_mul_of_nonneg_left (hb t ht') (by positivity)
      _ = C*t^3 := by field_simp
  · have h := (tendsto_const_nhds (x := C)).mul
      ((tendsto_id : Tendsto (fun t : ℝ ↦ t) (𝓝 0) (𝓝 0)).pow 3)
    simpa using h.mono_left nhdsWithin_le_nhds

end HardSphere

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_PositiveTimeSeqTendsto
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
open MeasureTheory Set Filter ContinuousLinearMap
open scoped Topology

lemma positiveTimeSeq_tendsto :
    Tendsto (fun n : ℕ ↦ 1/((n:ℝ)+1)) atTop (𝓝[>] 0) :=
  tendsto_nhdsWithin_iff.mpr ⟨tendsto_one_div_add_atTop_nhds_zero_nat,
    Eventually.of_forall fun _ ↦ by simp only [mem_Ioi]; positivity⟩

lemma SmoothTest.killed_generator {N : ℕ} {L : Length} {a : ℝ} (f : SmoothTest N L a) :
    Tendsto (fun n : ℕ ↦ (((1/((n:ℝ)+1))⁻¹:ℝ):ℂ) •
      (f.jet.1-killedTransition N L a (1/((n:ℝ)+1)) f.jet.1))
      atTop (𝓝 (smoothLaplacian f.asSmooth)) := by
  have ht := positiveTimeSeq_tendsto
  have hb := (killedTransition_free_firstOrder N L a f.asSmooth.val f.support_allowed).comp ht
  rw [← f.scalar_toLp] at hb
  have hf := f.free_generator (fun n : ℕ ↦ by positivity : ∀ n : ℕ,0<1/((n:ℝ)+1))
    tendsto_one_div_add_atTop_nhds_zero_nat
  simp only [RCLike.real_smul_eq_coe_smul (K := ℂ),RCLike.ofReal_inv] at hb
  have h := hf.sub hb
  simp only [sub_zero] at h
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  funext n
  dsimp only [Function.comp_apply]
  simp only [Complex.ofReal_inv]
  module

lemma SmoothTest.allowedProjection {N : ℕ} {L : Length} {a : ℝ} (f : SmoothTest N L a) :
    allowedProjection N L a f.jet.1=f.jet.1 := by
  apply Lp.ext
  filter_upwards [allowedProjection_ae N L a f.jet.1,f.memLp.coeFn_toLp] with X hP hf
  rw [hP]
  by_cases hX : X∈allowed N L a
  · rw [Set.indicator_of_mem hX]
  · rw [Set.indicator_of_notMem hX]
    change 0=f.memLp.toLp f.toFun X
    rw [hf]
    exact (image_eq_zero_of_notMem_tsupport (fun hs ↦ hX (f.support_allowed hs))).symm

lemma SmoothTest.killedLaplace_pairing {N : ℕ} {L : Length} {a : ℝ} (g : SmoothTest N L a)
    (f : ScalarL2 N L) :
    inner ℂ (smoothLaplacian g.asSmooth) (killedLaplace N L a f)=
      inner ℂ g.jet.1 f-inner ℂ g.jet.1 (killedLaplace N L a f) := by
  let u := killedLaplace N L a f
  have hL := g.killed_generator.inner (𝕜 := ℂ) (tendsto_const_nhds (x := u))
  have hR := (tendsto_const_nhds (x := g.jet.1)).inner (𝕜 := ℂ)
    ((killedLaplace_difference_tendsto N L a f).comp positiveTimeSeq_tendsto)
  have he (n : ℕ) : inner ℂ ((((1/((n:ℝ)+1))⁻¹:ℝ):ℂ) •
      (g.jet.1-killedTransition N L a (1/((n:ℝ)+1)) g.jet.1)) u=
      inner ℂ g.jet.1 ((((1/((n:ℝ)+1))⁻¹:ℝ):ℂ) • (u-killedTransition N L a (1/((n:ℝ)+1)) u)) := by
    rw [inner_smul_left,inner_smul_right,inner_sub_left,inner_sub_right]
    have hs : inner ℂ ((killedTransition N L a (1/((n:ℝ)+1))) g.jet.1) u =
        inner ℂ g.jet.1 ((killedTransition N L a (1/((n:ℝ)+1))) u) :=
      (isSelfAdjoint_iff_isSymmetric.mp (killedTransition_selfAdjoint N L a (1/((n:ℝ)+1)))) g.jet.1 u
    rw [hs]
    simp only [Complex.conj_ofReal]
  simp_rw [he] at hL
  simp only [Complex.ofReal_inv] at hL
  have hh := tendsto_nhds_unique hL hR
  rw [inner_sub_right] at hh
  have hp : inner ℂ g.jet.1 (HardSphere.allowedProjection N L a f)=inner ℂ g.jet.1 f := by
    rw [← killedTransition_zero]
    have hs : inner ℂ (killedTransition N L a 0 g.jet.1) f=
        inner ℂ g.jet.1 (killedTransition N L a 0 f) :=
      (isSelfAdjoint_iff_isSymmetric.mp (killedTransition_selfAdjoint N L a 0)) g.jet.1 f
    rw [← hs]
    rw [killedTransition_zero,g.allowedProjection]
  exact hh.trans (by rw [hp])

lemma killedLaplace_variational {N : ℕ} {L : Length} {a : ℝ} (f : ScalarL2 N L)
    {u : hilbertDomain N L a} (hu : scalarEmbedding N L a u=killedLaplace N L a f)
    {v : Jet N L} (hv : v∈dirichletDomain N L a) :
    inner ℂ v.1 (hilbertJetEquiv N L (u : HilbertJet N L)).1+
      (∑ p : Direction N,inner ℂ (v.2 p) ((hilbertJetEquiv N L (u : HilbertJet N L)).2 p))=
      inner ℂ v.1 f := by
  have hc : IsClosed {w : Jet N L | inner ℂ w.1 (hilbertJetEquiv N L (u : HilbertJet N L)).1+
      (∑ p : Direction N,inner ℂ (w.2 p) ((hilbertJetEquiv N L (u : HilbertJet N L)).2 p))=
      inner ℂ w.1 f} := by
    apply isClosed_eq
    · fun_prop
    · fun_prop
  apply closure_minimal (t := {w : Jet N L | _}) ?_ hc hv
  rintro _ ⟨g,rfl⟩
  change inner ℂ g.jet.1 (hilbertJetEquiv N L (u : HilbertJet N L)).1+
    (∑ p : Direction N,inner ℂ (g.jet.2 p) ((hilbertJetEquiv N L (u : HilbertJet N L)).2 p))=_
  have hp := g.form_pairing u.property
  change (∑ p : Direction N,inner ℂ (g.jet.2 p) ((hilbertJetEquiv N L (u : HilbertJet N L)).2 p))=
    inner ℂ (smoothLaplacian g.asSmooth) (scalarEmbedding N L a u) at hp
  rw [hp,hu]
  change inner ℂ g.jet.1 (scalarEmbedding N L a u)+_=_
  rw [hu,g.killedLaplace_pairing]
  abel

lemma killedLaplace_eq_formResolvent (N : ℕ) (L : Length) (a : ℝ) (f : ScalarL2 N L) :
    killedLaplace N L a f=formResolvent N L a f := by
  obtain ⟨u,hu,_⟩ := killedLaplace_graph N L a f
  have he : u=(scalarEmbedding N L a).adjoint f := by
    apply ext_inner_left ℂ
    intro v
    rw [adjoint_inner_right]
    change inner ℂ (v : HilbertJet N L) (u : HilbertJet N L)=_
    rw [hilbertJet_inner]
    exact killedLaplace_variational f hu v.property
  rw [← hu,he]
  rfl

end HardSphere

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Operators_SemigroupLaplaceDerivWithin
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
open ProbabilityTheory
namespace HardSphere
open MeasureTheory Set Filter
open scoped Topology
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

lemma semigroupLaplace_hasDerivWithinAt (K : ℝ → E→L[ℂ] E)
    (hadd : ∀ s t, 0 ≤ s → 0 ≤ t → K (s+t)=(K s).comp (K t))
    (hc : ∀ f, Continuous (fun t : ℝ ↦ K (max 0 t) f))
    (hnorm : ∀ t, 0 ≤ t → ∀ f, ‖K t f‖≤‖f‖) (f : E) {t : ℝ} (ht : 0 ≤ t) :
    HasDerivWithinAt (fun s : ℝ ↦ K s (semigroupLaplace K f))
      (K t (semigroupLaplace K f)-K t f) (Ici 0) t := by
  have hiC : Continuous (laplaceIntegrand K f) :=
    (Real.continuous_exp.comp continuous_neg).smul (hc f)
  have hd := intervalIntegral.integral_hasDerivAt_right
    (f := laplaceIntegrand K f) (a := 0) (b := t)
    (hiC.intervalIntegrable 0 t) (hiC.stronglyMeasurableAtFilter volume (𝓝 t)) hiC.continuousAt
  have hder := (Real.hasDerivAt_exp t).smul
    ((hasDerivAt_const t (semigroupLaplace K f)).sub hd)
  have heq : EqOn (fun s : ℝ ↦ Real.exp s •
      (semigroupLaplace K f-∫ z in (0:ℝ)..s,laplaceIntegrand K f z))
      (fun s ↦ K s (semigroupLaplace K f)) (Ici 0) :=
    fun s hs ↦ (semigroupLaplace_shift K hadd hc hnorm f hs).symm
  have hv : Real.exp t • (0-laplaceIntegrand K f t)+
      Real.exp t • (semigroupLaplace K f-∫ z in (0:ℝ)..t,laplaceIntegrand K f z)=
      K t (semigroupLaplace K f)-K t f := by
    rw [← semigroupLaplace_shift K hadd hc hnorm f ht,zero_sub,smul_neg,
      laplaceIntegrand,max_eq_right ht,smul_smul,← Real.exp_add,add_neg_cancel,
      Real.exp_zero,one_smul]
    abel
  change HasDerivAt (fun s : ℝ ↦ Real.exp s •
      (semigroupLaplace K f-∫ z in (0:ℝ)..s,laplaceIntegrand K f z))
    (Real.exp t • (0-laplaceIntegrand K f t)+
      Real.exp t • (semigroupLaplace K f-∫ z in (0:ℝ)..t,laplaceIntegrand K f z)) t at hder
  rw [hv] at hder
  exact hder.hasDerivWithinAt.congr (fun s hs ↦ (heq hs).symm) (heq ht).symm

lemma semigroupLaplace_eigenvector (K : ℝ → E→L[ℂ] E)
    (hadd : ∀ s t, 0 ≤ s → 0 ≤ t → K (s+t)=(K s).comp (K t))
    (hc : ∀ f, Continuous (fun t : ℝ ↦ K (max 0 t) f))
    (hnorm : ∀ t, 0 ≤ t → ∀ f, ‖K t f‖≤‖f‖) (f : E)
    {r : ℝ} (hr : 0 < r) (he : semigroupLaplace K f=r • f)
    {t : ℝ} (ht : 0 ≤ t) : K t f=Real.exp ((1-r⁻¹)*t) • f := by
  have hz : K 0 f=f := by
    have hh := semigroupLaplace_project K hadd hc hnorm f
    rw [he,(K 0).map_smul_of_tower] at hh
    exact (smul_right_injective E (ne_of_gt hr)) hh
  have hd (s : ℝ) (hs : 0 ≤ s) : HasDerivWithinAt (fun x : ℝ ↦ K x f)
      ((1-r⁻¹) • K s f) (Ici 0) s := by
    have h := (semigroupLaplace_hasDerivWithinAt K hadd hc hnorm f hs).const_smul r⁻¹
    simp only [he,ContinuousLinearMap.map_smul_of_tower] at h
    change HasDerivWithinAt (fun x : ℝ ↦ r⁻¹ • (r • K x f))
       (r⁻¹ • (r • K s f-K s f)) (Ici 0) s at h
    simp only [smul_sub,smul_smul,inv_mul_cancel₀ (ne_of_gt hr),one_smul] at h
    convert h using 1
    all_goals try with_reducible_and_instances rfl
    module
  let F : ℝ → E := fun x ↦ Real.exp ((r⁻¹-1)*x) • K x f
  have hFcont : ContinuousOn F (Ici 0) := by
    have h : ContinuousOn (fun x : ℝ ↦ Real.exp ((r⁻¹-1)*x) • K (max 0 x) f) (Ici 0) :=
      ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).smul (hc f)).continuousOn
    exact h.congr (fun s hs ↦ by simp only [F,max_eq_right (show 0 ≤ s from hs)])
  have hdF (s : ℝ) (hs : 0 ≤ s) : HasDerivWithinAt F 0 (Ici 0) s := by
    have h := (((hasDerivAt_id s).const_mul (r⁻¹-1)).exp.hasDerivWithinAt).smul (hd s hs)
    convert h using 1
    · rfl
    · module
  have hconst := constant_of_has_deriv_right_zero
    (hFcont.mono (Icc_subset_Ici_self : Icc (0:ℝ) t ⊆ Ici 0))
    (fun s hs ↦ (hdF s hs.1).mono (Ici_subset_Ici.mpr hs.1))
  have heF : Real.exp ((r⁻¹-1)*t) • K t f=f := by
    simpa only [F,mul_zero,Real.exp_zero,one_smul,hz] using hconst t ⟨ht,le_refl _⟩
  calc
    K t f=Real.exp ((1-r⁻¹)*t) • (Real.exp ((r⁻¹-1)*t) • K t f) := by
      rw [smul_smul,← Real.exp_add,show (1-r⁻¹)*t+(r⁻¹-1)*t=0 by ring,
        Real.exp_zero,one_smul]
    _ = _ := by rw [heF]

end HardSphere

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_KilledEigenvector
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
namespace HardSphere
open MeasureTheory Set Filter ContinuousLinearMap
open scoped Topology

lemma IsGroundVector.killed_eigenvector {N : ℕ} {L : Length} {a : ℝ} {u : Jet N L}
    (hu : IsGroundVector N L a u) {t : ℝ} (ht : 0 ≤ t) :
    killedTransition N L a t u.1=(Real.exp (-t*energy u):ℂ) • u.1 := by
  have hE : 0 ≤ energy u := Finset.sum_nonneg fun _ _ ↦ sq_nonneg _
  have he : semigroupLaplace (killedTransition N L a) u.1=((1+energy u)⁻¹:ℝ) • u.1 := by
    change killedLaplace N L a u.1=_
    rw [killedLaplace_eq_formResolvent]
    rw [← IsScalarTower.algebraMap_smul ℂ ((1+energy u)⁻¹:ℝ) u.1]
    change formResolvent N L a u.1=(((1+energy u)⁻¹:ℝ):ℂ) • u.1
    simpa only [Complex.ofReal_inv,Complex.ofReal_add,Complex.ofReal_one] using hu.resolvent_eigenvector
  have hh := semigroupLaplace_eigenvector (killedTransition N L a)
    (killedTransition_add_nonneg N L a) (killedTransition_clamped_continuous N L a)
    (fun t _ ↦ killedTransition_apply_contraction N L a t) u.1 (by positivity) he ht
  simp only [inv_inv] at hh
  rw [show (1-(1+energy u))*t= -t*energy u by ring] at hh
  exact hh.trans (IsScalarTower.algebraMap_smul ℂ _ _).symm

end HardSphere

end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_GroundPathWeight
attribute [-instance] _root_.OAI.HardSphere.Bridge.exposedBridgeKernel_markov _root_.OAI.HardSphere.Bridge.exposedPeriodSingle_finite _root_.OAI.HardSphere.Bridge.exposedTrialKernel_markov _root_.OAI.HardSphere.Bridge.instBorelSpaceContinuousMapElemRealTimePoint _root_.OAI.HardSphere.Bridge.instIsProbabilityMeasureNoiseLaw _root_.OAI.HardSphere.Bridge.instMeasurableSpaceContinuousMapElemRealTimePoint _root_.OAI.HardSphere.Bridge.parameterBridgeKernel_markov _root_.OAI.HardSphere.Bridge.parameterIndividualReference_finite _root_.OAI.HardSphere.Bridge.parameterTrialKernel_markov _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Bridge.trialKernel_markov _root_.OAI.HardSphere.Groups.cellPathReference_probability _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Rescaling.config_haar _root_.OAI.HardSphere.bridgeEndpointBase_finite _root_.OAI.HardSphere.coordinateBridge_probability _root_.OAI.HardSphere.endpointWeightedBase_sfinite _root_.OAI.HardSphere.freePathLaw_finite_deletion _root_.OAI.HardSphere.gaussianCoordinates_probability _root_.OAI.HardSphere.killedPathLaw_finite_deletion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal BigOperators
open scoped RealInnerProductSpace
namespace HardSphere
open MeasureTheory Wiener Set Filter
open scoped ComplexConjugate
noncomputable section
variable {N : ℕ} {L : Length} {a t : ℝ}

lemma integrable_norm_endpoints (N : ℕ) (L : Length) (a t : ℝ)
    (f g : ScalarL2 N L) (s v : Time) :
    Integrable (fun ω : ConfigurationPath N L ↦ ‖f (ω s)‖*‖g (ω v)‖)
      (killedPathLaw N L a t) := by
  exact (((Lp.memLp f).comp_measurePreserving (freePathLaw_marginal N L t s)).norm.integrable_mul
    ((Lp.memLp g).comp_measurePreserving (freePathLaw_marginal N L t v)).norm).restrict

lemma modulus_killed_pairing (f g : ScalarL2 N L) :
    inner ℂ (modulusScalar f) (killedTransition N L a t (modulusScalar g)) =
      ((∫ ω : ConfigurationPath N L, ‖f (ω 0)‖*‖g (ω 1)‖ ∂killedPathLaw N L a t):ℝ) := by
  rw [killedTransition_pairing,← integral_complex_ofReal]
  apply integral_congr_ae
  filter_upwards [((freePathLaw_marginal N L t 0).quasiMeasurePreserving.ae_eq_comp
      (coe_modulusScalar f)).filter_mono (ae_mono Measure.restrict_le_self),
    ((freePathLaw_marginal N L t 1).quasiMeasurePreserving.ae_eq_comp
      (coe_modulusScalar g)).filter_mono (ae_mono Measure.restrict_le_self)] with ω hf hg
  dsimp only [Function.comp_def] at hf hg
  rw [hf,hg,Complex.conj_ofReal,Complex.ofReal_mul]

lemma IsGroundVector.integral_norm_endpoints {u : Jet N L} (hu : IsGroundVector N L a u)
    (ht : 0 ≤ t) :
    (∫ ω : ConfigurationPath N L, ‖u.1 (ω 0)‖*‖u.1 (ω 1)‖ ∂killedPathLaw N L a t)=
      Real.exp (-t*energy u) := by
  apply Complex.ofReal_injective
  rw [← modulus_killed_pairing,show modulusScalar u.1=(modulusJet u).1 from rfl,
    hu.modulus.killed_eigenvector ht,inner_smul_right,inner_self_eq_norm_sq_to_K,
    hu.modulus.2.2.1,RCLike.ofReal_one,one_pow,mul_one,hu.energy_modulus]

lemma groundPathWeight_nonneg (u : Jet N L) (t : ℝ) (ω : ConfigurationPath N L) :
    0 ≤ groundPathWeight u t ω := by
  unfold groundPathWeight
  positivity

lemma groundPathWeight_integrable (u : Jet N L) (a t : ℝ) :
    Integrable (groundPathWeight u t) (killedPathLaw N L a t) :=
  (integrable_norm_endpoints N L a t u.1 u.1 0 1).const_mul _

lemma IsGroundVector.integral_groundPathWeight {u : Jet N L} (hu : IsGroundVector N L a u)
    (ht : 0 ≤ t) : ∫ ω, groundPathWeight u t ω ∂killedPathLaw N L a t=1 := by
  simp only [groundPathWeight,integral_const_mul]
  rw [hu.integral_norm_endpoints ht,← Real.exp_add,
    show t*energy u+ -t*energy u=0 by ring,Real.exp_zero]

lemma IsGroundVector.groundPathLaw_probability_oai {u : Jet N L} (hu : IsGroundVector N L a u)
    (ht : 0 ≤ t) : IsProbabilityMeasure (groundPathLaw N L a t u) := by
  constructor
  rw [groundPathLaw,withDensity_apply _ MeasurableSet.univ,setLIntegral_univ,
    ← ofReal_integral_eq_lintegral_ofReal (groundPathWeight_integrable u a t)
      (Eventually.of_forall (groundPathWeight_nonneg u t)),hu.integral_groundPathWeight ht,
    ENNReal.ofReal_one]

end
end HardSphere

end
end
end

end OAI
end

theorem solution : type_of% @OAI.HardSphere.IsGroundVector.groundPathLaw_probability_oai := @OAI.HardSphere.IsGroundVector.groundPathLaw_probability_oai
