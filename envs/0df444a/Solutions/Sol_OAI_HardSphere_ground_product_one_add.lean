-- Prove2me | solution 1 for OAI.HardSphere.ground_product_one_add
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T20:31:14.533274+00:00
-- url     : https://prove2.me/submissions/bf9c5cec-d7ba-4243-a362-93dae3a837c2

import Mathlib
import Definitions.Def_HardSphere
import Definitions.Def_OAIQ054H002
import Theorems.Thm_OAI_HardSphere_killedTransition_norm_le_of_energy

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
-- module Solutions.OAIQ054_HS.HardSphere_Cutoffs_Failure
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
namespace SineProduct

lemma one_failure_le {I : Type*} [DecidableEq I] (s : Finset I) (h : I → ℝ)
    (h0 : ∀ i∈s, 0≤h i) (h1 : ∀ i∈s, h i≤1) :
    (∑ i∈s, (1-h i)*∏ j∈s.erase i, h j)+(∏ i∈s, h i)≤1 := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    have hp : ∀ i∈s, 0≤h i := fun i hi ↦ h0 i (Finset.mem_insert_of_mem hi)
    have hq : ∀ i∈s, h i≤1 := fun i hi ↦ h1 i (Finset.mem_insert_of_mem hi)
    have hh := ih hp hq
    have hn : 0≤∑ i∈s, (1-h i)*∏ j∈s.erase i,h j := by
      apply Finset.sum_nonneg
      intro i hi
      exact mul_nonneg (sub_nonneg.mpr (hq i hi))
        (Finset.prod_nonneg fun j hj ↦ hp j (Finset.mem_of_mem_erase hj))
    have he : (∑ i∈insert a s, (1-h i)*∏ j∈(insert a s).erase i, h j)=
        (1-h a)*(∏ j∈s,h j)+h a*(∑ i∈s, (1-h i)*∏ j∈s.erase i,h j) := by
      rw [Finset.sum_insert ha,Finset.erase_insert ha,Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      have hia : i≠a := fun he ↦ ha (he ▸ hi)
      rw [Finset.erase_insert_of_ne hia.symm,Finset.prod_insert (by simp [ha])]
      ring
    rw [he,Finset.prod_insert ha]
    nlinarith [mul_le_mul_of_nonneg_right (h1 a (Finset.mem_insert_self a s)) hn]

lemma coefficients_sq_le {I : Type*} [DecidableEq I] (s : Finset I) (θ : I → ℝ) :
    ∑ i∈s, (Real.cos (θ i)*∏ j∈s.erase i,Real.sin (θ j))^2≤1 := by
  have h := one_failure_le s (fun i ↦ Real.sin (θ i)^2) (fun _ _ ↦ sq_nonneg _)
    (fun i _ ↦ by nlinarith [Real.sin_sq_add_cos_sq (θ i),sq_nonneg (Real.cos (θ i))])
  have he : (∑ i∈s, (1-Real.sin (θ i)^2)*∏ j∈s.erase i,Real.sin (θ j)^2)=
      ∑ i∈s, (Real.cos (θ i)*∏ j∈s.erase i,Real.sin (θ j))^2 := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [mul_pow,← Finset.prod_pow]
    congr 1
    nlinarith [Real.sin_sq_add_cos_sq (θ i)]
  rw [he] at h
  exact le_trans (le_add_of_nonneg_right (Finset.prod_nonneg fun _ _ ↦ sq_nonneg _)) h

lemma contraction_sq {I : Type*} [DecidableEq I] (s : Finset I) (θ d : I → ℝ) :
    (∑ i∈s, (Real.cos (θ i)*∏ j∈s.erase i,Real.sin (θ j))*d i)^2≤∑ i∈s,d i^2 := by
  exact (Finset.sum_mul_sq_le_sq_mul_sq s _ d).trans (by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right (coefficients_sq_le s θ)
      (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _))

lemma fderiv_sq_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {I : Type*} [DecidableEq I] (s : Finset I) (θ : I → E → ℝ) (x v : E)
    (hd : ∀ i∈s, DifferentiableAt ℝ (θ i) x) :
    (fderiv ℝ (fun y ↦ ∏ i∈s,Real.sin (θ i y)) x v)^2≤
      ∑ i∈s,(fderiv ℝ (θ i) x v)^2 := by
  have hp := HasFDerivAt.finsetProd (u := s) (fun i hi ↦ (hd i hi).hasFDerivAt.sin)
  rw [hp.fderiv,sum_apply]
  simp only [smul_apply,smul_eq_mul]
  convert contraction_sq s (fun i ↦ θ i x) (fun i ↦ fderiv ℝ (θ i) x v) using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  ring

end SineProduct

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Cutoffs_ChordLift
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
namespace PeriodicCutoff

variable (L : ℝ) [hL : Fact (0<L)]

lemma chord_continuous : Continuous (chord L) := by
  apply (QuotientAddGroup.isOpenMap_coe.isQuotientMap (AddCircle.continuous_mk' L) QuotientAddGroup.mk_surjective).continuous_iff.mpr
  simpa only [Function.comp_def,chord_coe] using (chordLift_smooth L).continuous

lemma chordLift_derivative (x : ℝ) : HasDerivAt (chordLift L)
    (2*(L/Real.pi*Real.sin (Real.pi/L*x))*Real.cos (Real.pi/L*x)) x := by
  have h := (((hasDerivAt_id x).const_mul (Real.pi/L)).sin.const_mul (L/Real.pi)).pow 2
  apply h.congr_deriv
  dsimp
  field_simp [ne_of_gt hL.out, Real.pi_ne_zero]

lemma chordLift_derivative_sq_le (x : ℝ) :
    (deriv (chordLift L) x)^2 ≤ 4*chordLift L x := by
  rw [(chordLift_derivative L x).deriv]
  have hc : Real.cos (Real.pi/L*x)^2 ≤ 1 := by
    nlinarith [Real.sin_sq_add_cos_sq (Real.pi/L*x),sq_nonneg (Real.sin (Real.pi/L*x))]
  simpa only [chordLift] using (show
    (2*(L/Real.pi*Real.sin (Real.pi/L*x))*Real.cos (Real.pi/L*x))^2≤
      4*(L/Real.pi*Real.sin (Real.pi/L*x))^2 by
        nlinarith [mul_le_mul_of_nonneg_left hc (sq_nonneg (2*(L/Real.pi*Real.sin (Real.pi/L*x))))])

lemma centered_representative (x : AddCircle L) :
    ∃ t : ℝ, (t : AddCircle L)=x ∧ |t|≤L/2 ∧ ‖x‖=|t| := by
  let t := (AddCircle.equivIco L (-L/2) x).val
  have ht : (t : AddCircle L)=x := AddCircle.coe_equivIco
  have hb : |t|≤L/2 := by
    apply abs_le.mpr
    constructor
    · simpa only [neg_div] using (AddCircle.equivIco L (-L/2) x).property.1
    · have hu := (AddCircle.equivIco L (-L/2) x).property.2
      dsimp [t]
      linarith
  exact ⟨t,ht,hb,ht ▸ ((AddCircle.norm_coe_eq_abs_iff L (ne_of_gt hL.out)).mpr
    (by simpa only [abs_of_pos hL.out] using hb))⟩

lemma chord_nonneg (x : AddCircle L) : 0 ≤ chord L x := by
  obtain ⟨t,rfl,_,_⟩ := centered_representative L x
  exact sq_nonneg _

lemma chord_le_norm_sq (x : AddCircle L) : chord L x≤‖x‖^2 := by
  obtain ⟨t,rfl,ht,hx⟩ := centered_representative L x
  rw [chord_coe,hx]
  have h : |L/Real.pi*Real.sin (Real.pi/L*t)|≤|t| := by
    rw [abs_mul,abs_of_pos (div_pos hL.out Real.pi_pos)]
    calc
      L/Real.pi*|Real.sin (Real.pi/L*t)|≤L/Real.pi*|Real.pi/L*t| :=
        mul_le_mul_of_nonneg_left Real.abs_sin_le_abs (le_of_lt (div_pos hL.out Real.pi_pos))
      _ = |t| := by
        rw [abs_mul,abs_of_pos (div_pos Real.pi_pos hL.out)]
        field_simp [ne_of_gt hL.out, Real.pi_ne_zero]
  dsimp [chordLift]
  calc
    _ = |L/Real.pi*Real.sin (Real.pi/L*t)|^2 := (sq_abs _).symm
    _ ≤ |t|^2 := (sq_le_sq₀ (abs_nonneg _) (abs_nonneg _)).mpr h

lemma norm_sq_le_chord (x : AddCircle L) : ‖x‖^2≤(Real.pi/2)^2*chord L x := by
  obtain ⟨t,rfl,ht,hx⟩ := centered_representative L x
  have ha : |Real.pi/L*t|≤Real.pi/2 := by
    rw [abs_mul,abs_of_pos (div_pos Real.pi_pos hL.out)]
    calc
      Real.pi/L*|t|≤Real.pi/L*(L/2) := mul_le_mul_of_nonneg_left ht (le_of_lt (div_pos Real.pi_pos hL.out))
      _ = Real.pi/2 := by field_simp [ne_of_gt hL.out, Real.pi_ne_zero]
  have hb : |t|≤Real.pi/2*|L/Real.pi*Real.sin (Real.pi/L*t)| := by
    have h := mul_le_mul_of_nonneg_left (Real.mul_abs_le_abs_sin ha)
      (show 0≤L/2 from (div_pos hL.out (by norm_num)).le)
    simp only [abs_mul,abs_of_pos (div_pos Real.pi_pos hL.out)] at h
    rw [abs_mul,abs_of_pos (div_pos hL.out Real.pi_pos)]
    have he : L/2*(2/Real.pi*(Real.pi/L*|t|))=|t| := by
      field_simp [ne_of_gt hL.out, Real.pi_ne_zero]
    rw [he] at h
    convert h using 1 <;> first | rfl | (field_simp [ne_of_gt hL.out, Real.pi_ne_zero])
  rw [chord_coe,hx]
  dsimp [chordLift]
  calc
    _ ≤ (Real.pi/2*|L/Real.pi*Real.sin (Real.pi/L*t)|)^2 :=
      (sq_le_sq₀ (abs_nonneg _) (mul_nonneg (by positivity) (abs_nonneg _))).mpr hb
    _ = _ := by rw [mul_pow,sq_abs]

end PeriodicCutoff

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Operators_TransitionDerivative
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
namespace PeriodicCutoff

lemma transition_derivative (x : ℝ) :
    HasDerivAt Real.smoothTransition (deriv Real.smoothTransition x) x :=
  ((Real.smoothTransition.contDiff (n := 1)).differentiable (by norm_num) x).hasDerivAt

lemma transition_deriv_eq_zero {x : ℝ} (hx : x∉Icc (0:ℝ) 1) :
    deriv Real.smoothTransition x=0 := by
  have he : (Real.smoothTransition =ᶠ[𝓝 x] fun _ ↦ (Real.smoothTransition x)) := by
    rcases not_and_or.mp hx with h | h
    · have hx : x<0 := lt_of_not_ge h
      filter_upwards [isOpen_Iio.mem_nhds hx] with y hy
      rw [Real.smoothTransition.zero_of_nonpos hy.le,Real.smoothTransition.zero_of_nonpos hx.le]
    · have hx : 1<x := lt_of_not_ge h
      filter_upwards [isOpen_Ioi.mem_nhds hx] with y hy
      rw [Real.smoothTransition.one_of_one_le hy.le,Real.smoothTransition.one_of_one_le hx.le]
  exact ((hasDerivAt_const x (Real.smoothTransition x)).congr_of_eventuallyEq he).deriv

lemma exists_transition_bound : ∃ M : ℝ, 0<M ∧ ∀ x : ℝ, |deriv Real.smoothTransition x|≤M := by
  obtain ⟨C,hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
    ((Real.smoothTransition.contDiff (n := 2)).continuous_deriv (by norm_num)).continuousOn
      (s := Icc (0:ℝ) 1)
  refine ⟨max C 1,lt_of_lt_of_le zero_lt_one (le_max_right _ _),fun x ↦ ?_⟩
  by_cases hx : x∈Icc (0:ℝ) 1
  · exact (hC x hx).trans (le_max_left _ _)
  · rw [transition_deriv_eq_zero hx,abs_zero]
    exact (zero_le_one : (0:ℝ)≤1).trans (le_max_right _ _)

end PeriodicCutoff

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Cutoffs_ThreeTorus
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
namespace PeriodicCutoff
variable (L : ℝ) [hL : Fact (0<L)]

omit hL in
lemma box_measurable (R : ℝ) (x : ThreeTorus L) : MeasurableSet (box L R x) :=
  MeasurableSet.univ_pi (fun _ ↦ measurableSet_closedBall)

lemma box_volume_le {R : ℝ} (hR : 0≤R) (x : ThreeTorus L) :
    volume.real (box L R x)≤(2*R)^3 := by
  have he : volume (box L R x)=ENNReal.ofReal (min L (2*R))^3 := by
    rw [volume_pi,box,Measure.pi_pi]
    simp_rw [AddCircle.volume_closedBall]
    simp
  rw [measureReal_def,he,ENNReal.toReal_pow,ENNReal.toReal_ofReal
    (le_min hL.out.le (mul_nonneg (by norm_num) hR))]
  exact pow_le_pow_left₀ (le_min hL.out.le (mul_nonneg (by norm_num) hR)) (min_le_right _ _) 3

lemma pairQ_continuous : Continuous (fun p : ThreeTorus L × ThreeTorus L ↦ pairQ L p.1 p.2) := by
  unfold pairQ
  apply continuous_finsetSum
  intro j _
  exact (chord_continuous L).comp (by fun_prop)

lemma pairQ_le (y x : ThreeTorus L) : pairQ L y x≤∑ j : Fin 3,dist (y j) (x j)^2 := by
  apply Finset.sum_le_sum
  intro j _
  simpa only [dist_eq_norm] using chord_le_norm_sq L (y j-x j)

lemma not_mem_box_pairQ {r : ℝ} (hr : 0 < r) {y x : ThreeTorus L}
    (hx : y∉box L (Real.pi*r) x) : 4*r^2<pairQ L y x := by
  obtain ⟨j,hj⟩ : ∃ j, Real.pi*r<dist (y j) (x j) := by
    by_contra! hn
    exact hx (by simpa only [box,Set.mem_univ_pi,Metric.mem_closedBall] using hn)
  have hq := norm_sq_le_chord L (y j-x j)
  have hs : chord L (y j-x j)≤pairQ L y x :=
    Finset.single_le_sum (fun i _ ↦ chord_nonneg L (y i-x i)) (Finset.mem_univ j)
  rw [← dist_eq_norm] at hq
  have hd2 : (Real.pi*r)^2<dist (y j) (x j)^2 :=
    (sq_lt_sq₀ (mul_nonneg Real.pi_pos.le hr.le) dist_nonneg).mpr hj
  nlinarith [mul_le_mul_of_nonneg_left hs (sq_nonneg (Real.pi/2)),sq_pos_of_pos Real.pi_pos]

lemma angle_zero {r : ℝ} (hr : 0 < r) {y x : ThreeTorus L} (hq : pairQ L y x≤2*r^2) :
    angle L r y x=0 := by
  unfold angle
  rw [Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hq) (by positivity)),mul_zero]

lemma angle_one {r : ℝ} (hr : 0 < r) {y x : ThreeTorus L} (hq : 4*r^2≤pairQ L y x) :
    angle L r y x=Real.pi/2 := by
  unfold angle
  rw [Real.smoothTransition.one_of_one_le ((le_div_iff₀ (by positivity)).mpr (by nlinarith)),mul_one]

lemma angle_one_outside {r : ℝ} (hr : 0 < r) {y x : ThreeTorus L}
    (hx : y∉box L (Real.pi*r) x) : angle L r y x=Real.pi/2 :=
  angle_one L hr (not_mem_box_pairQ L hr hx).le

omit hL in
lemma angleLift_derivative (r : ℝ) (z : Fin 3 → ℝ → ℝ)
    (d : Fin 3 → ℝ) (t : ℝ) (hd : ∀ j, HasDerivAt (z j) (d j) t) :
    HasDerivAt (fun s ↦ angleLift L r (fun j ↦ z j s))
      (∑ j : Fin 3, anglePartial L r (fun k ↦ z k t) j*d j) t := by
  have hc j := ((chordLift_smooth L).differentiable (by simp) (z j t)).hasDerivAt.comp t (hd j)
  have hq := HasDerivAt.fun_sum (u := (Finset.univ : Finset (Fin 3))) (fun j _ ↦ hc j)
  have h := ((transition_derivative ((qLift L (fun j ↦ z j t)-2*r^2)/(2*r^2))).comp t
    ((hq.sub_const (2*r^2)).div_const (2*r^2))).const_mul (Real.pi/2)
  apply h.congr_deriv
  dsimp [anglePartial,angleFactor]
  calc
    _ = (Real.pi/(4*r^2)*deriv Real.smoothTransition ((qLift L (fun j ↦ z j t)-2*r^2)/(2*r^2)))*
        ∑ j : Fin 3, deriv (chordLift L) (z j t)*d j := by ring
    _ = _ := by rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro j _; ring

omit hL in
lemma chordLift_le_qLift (z : Fin 3 → ℝ) (j : Fin 3) : chordLift L (z j)≤qLift L z :=
  Finset.single_le_sum (fun k _ ↦ sq_nonneg (L/Real.pi*Real.sin (Real.pi/L*z k))) (Finset.mem_univ j)

omit hL in
lemma angleFactor_eq_zero {r : ℝ} (hr : 0 < r) {z : Fin 3 → ℝ}
    (hz : qLift L z∉Icc (2*r^2) (4*r^2)) : angleFactor L r z=0 := by
  have ht : (qLift L z-2*r^2)/(2*r^2)∉Icc (0:ℝ) 1 := by
    intro hc
    apply hz
    have h0 := (le_div_iff₀ (show 0<2*r^2 by positivity)).mp hc.1
    have h1 := (div_le_iff₀ (show 0<2*r^2 by positivity)).mp hc.2
    constructor <;> nlinarith
  simp only [angleFactor,transition_deriv_eq_zero ht,mul_zero]

omit hL in
lemma anglePartial_eq_zero {r : ℝ} (hr : 0 < r) {z : Fin 3 → ℝ}
    (hz : qLift L z∉Icc (2*r^2) (4*r^2)) (j : Fin 3) : anglePartial L r z j=0 := by
  rw [anglePartial,angleFactor_eq_zero L hr hz,zero_mul]

lemma anglePartial_sq_le {r M : ℝ} (hr : 0 < r) (hM : 0≤M)
    (hb : ∀ t : ℝ, |deriv Real.smoothTransition t|≤M) (z : Fin 3 → ℝ) (j : Fin 3) :
    anglePartial L r z j^2 ≤ Real.pi^2*M^2/r^2 := by
  by_cases hz : qLift L z∈Icc (2*r^2) (4*r^2)
  · have hc : (deriv (chordLift L) (z j))^2≤16*r^2 := by
      have hs := chordLift_le_qLift L z j
      have hd := chordLift_derivative_sq_le L (z j)
      nlinarith [hz.2]
    have ht : (deriv Real.smoothTransition ((qLift L z-2*r^2)/(2*r^2)))^2≤M^2 := by
      rw [← sq_abs (deriv Real.smoothTransition _)]
      exact (sq_le_sq₀ (abs_nonneg _) hM).mpr (hb _)
    calc
      _ = (Real.pi/(4*r^2))^2*((deriv Real.smoothTransition ((qLift L z-2*r^2)/(2*r^2)))^2*
          (deriv (chordLift L) (z j))^2) := by dsimp [anglePartial,angleFactor]; ring
      _ ≤ (Real.pi/(4*r^2))^2*(M^2*(16*r^2)) := by gcongr
      _ = _ := by field_simp [hr.ne']; ring
  · rw [anglePartial_eq_zero L hr hz j,zero_pow (by norm_num)]
    positivity

end PeriodicCutoff

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

theorem IsGroundVector.rayleigh {N : ℕ} {L : Length} {a : ℝ}
    {u : Jet N L} (hu : IsGroundVector N L a u) (v : Jet N L)
    (hv : v ∈ dirichletDomain N L a) (hb : bosonic v.1) :
    energy u * ‖v.1‖ ^ 2 ≤ energy v := by
  exact Variational.rayleigh (groundFormSubmodule N L a) u
    (fun w hw hn ↦ hu.2.2.2 w (mem_groundFormSubmodule.mp hw).1
      (mem_groundFormSubmodule.mp hw).2 hn) v
    (mem_groundFormSubmodule.mpr ⟨hv, hb⟩)

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

end HardSphere

end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_CoordinateLineConsSucc
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
namespace HardSphere
open MeasureTheory Set Filter
open scoped ComplexConjugate

lemma coordinateLine_cons_succ {n : ℕ} {L : Length} (x : Torus L)
    (Y : Configuration n L) (i : Fin n) (j : Fin 3) (t : AddCircle L.val) :
    coordinateLine (Fin.cons x Y) (i.succ,j) t=Fin.cons x (coordinateLine Y (i,j) t) := by
  funext k q
  refine Fin.cases ?_ (fun k ↦ ?_) k
  · simp [coordinateLine]
  · by_cases h : k=i
    · subst k; simp [coordinateLine]
    · simp [coordinateLine,Pi.single_eq_of_ne h,Pi.single_eq_of_ne (fun e ↦ h (Fin.succ_injective _ e))]

lemma SmoothMultiplier.hasDerivAt_fiberIntegral {n : ℕ} {L : Length}
    (f : SmoothMultiplier (n+1) L) (Y : Configuration n L) (i : Fin n) (j : Fin 3) :
    HasDerivAt (fun t : ℝ ↦ ∫ x : Torus L,
      f.toFun (Fin.cons x (coordinateLine Y (i,j) (t : AddCircle L.val))))
      (∫ x : Torus L, coordDerivative (n+1) L f.toFun (i.succ,j) (Fin.cons x Y)) 0 := by
  let F : ℝ → Torus L → ℂ := fun t x ↦
    f.toFun (Fin.cons x (coordinateLine Y (i,j) (t : AddCircle L.val)))
  let D : ℝ → Torus L → ℂ := fun t x ↦
    coordDerivative (n+1) L f.toFun (i.succ,j)
      (Fin.cons x (coordinateLine Y (i,j) (t : AddCircle L.val)))
  have cF (t) : Continuous (F t) :=
    (continuous_of_continuous_lift f.smooth.continuous).comp
      ((continuous_id : Continuous (id : Torus L → Torus L)).finCons
        (continuous_const : Continuous (fun _ : Torus L ↦ coordinateLine Y (i,j) (t : AddCircle L.val))))
  have cD (t) : Continuous (D t) :=
    (continuous_coordDerivative f.smooth (i.succ,j)).comp
      ((continuous_id : Continuous (id : Torus L → Torus L)).finCons
        (continuous_const : Continuous (fun _ : Torus L ↦ coordinateLine Y (i,j) (t : AddCircle L.val))))
  let d : C(Configuration (n+1) L,ℂ) :=
    ⟨_,continuous_coordDerivative f.smooth (i.succ,j)⟩
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := F) (F' := D) (μ := (volume : Measure (Torus L))) (s := Set.univ) (x₀ := 0)
    (bound := fun _ ↦ ‖d‖) univ_mem
    (Eventually.of_forall fun t ↦ (cF t).aestronglyMeasurable)
    ((cF 0).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
    (cD 0).aestronglyMeasurable
    (Eventually.of_forall fun x t _ ↦ d.norm_coe_le_norm _)
    (integrable_const _) (Eventually.of_forall fun x t _ ↦ by
      have hh := hasDerivAt_coordinateLine (f.smooth.differentiable (by simp))
        (Fin.cons x Y) (i.succ,j) t
      simpa only [coordinateLine_cons_succ] using hh)
  simpa only [F,D,Complex.ofReal_zero,AddCircle.coe_zero,coordinateLine,Pi.single_zero,add_zero] using h.2

lemma SmoothMultiplier.insertion_orthogonal {n : ℕ} {L : Length}
    (f : SmoothMultiplier (n+1) L)
    (hr : ∀ X, conj (f.toFun X)=f.toFun X)
    (hn : ∀ Y : Configuration n L, ∫ x : Torus L, ‖f.toFun (Fin.cons x Y)‖^2=1)
    (i : Fin n) (j : Fin 3) (Y : Configuration n L) :
    ∫ x : Torus L, conj (f.toFun (Fin.cons x Y))*
      coordDerivative (n+1) L f.toFun (i.succ,j) (Fin.cons x Y)=0 := by
  have he (X) : f.toFun X*f.toFun X = ((‖f.toFun X‖^2 : ℝ) : ℂ) := by
    calc
      _ = f.toFun X*conj (f.toFun X) := by rw [hr]
      _ = _ := by rw [Complex.mul_conj,Complex.sq_norm]
  have hc (Y) : (∫ x : Torus L, (f.mul f).toFun (Fin.cons x Y))=1 := by
    simp only [SmoothMultiplier.mul,Pi.mul_apply,he]
    rw [integral_complex_ofReal,hn,Complex.ofReal_one]
  have h := (f.mul f).hasDerivAt_fiberIntegral Y i j
  simp only [hc] at h
  have hz := h.unique (hasDerivAt_const (0:ℝ) (1:ℂ))
  have hd := coordDerivative_mul (f.smooth.differentiable (by simp))
    (f.smooth.differentiable (by simp)) (i.succ,j)
  change (∫ x : Torus L, coordDerivative (n+1) L (f.toFun*f.toFun) (i.succ,j) (Fin.cons x Y))=0 at hz
  rw [hd] at hz
  have hfactor : (∫ x : Torus L,
      (f.toFun * coordDerivative (n+1) L f.toFun (i.succ,j) +
        f.toFun * coordDerivative (n+1) L f.toFun (i.succ,j)) (Fin.cons x Y))=
      (2:ℂ)*(∫ x : Torus L, conj (f.toFun (Fin.cons x Y))*
      coordDerivative (n+1) L f.toFun (i.succ,j) (Fin.cons x Y)) := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    exact Eventually.of_forall fun x ↦ by simp only [Pi.add_apply,Pi.mul_apply,hr]; ring
  rw [hfactor] at hz
  exact (mul_eq_zero.mp hz).resolve_left (by norm_num)

end HardSphere

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_PathBounds_ConfigurationTailLp
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
open MeasureTheory Set Filter
open scoped ComplexConjugate
noncomputable section

lemma coe_configurationTailCLM {n : ℕ} {L : Length} (u : ScalarL2 n L) :
    configurationTailCLM n L u =ᵐ[volume] fun X ↦ u (Fin.tail X) := coe_configurationTailLp u

end
end HardSphere

namespace HardSphere
open MeasureTheory Set Filter
open scoped ComplexConjugate
noncomputable section

lemma coe_insertionScalar {n : ℕ} {L : Length} (f : SmoothMultiplier (n+1) L) (u : ScalarL2 n L) :
    f.insertionScalar u =ᵐ[volume] fun X ↦ f.toFun X*u (Fin.tail X) := by
  filter_upwards [coe_configurationTailCLM u,L2Multiplier.coe_clm f.toFun f.memLp_top (configurationTailCLM n L u)]
    with X h1 h2
  exact h2.trans (by rw [h1])

lemma coe_insertionJet_zero {n : ℕ} {L : Length} (f : SmoothMultiplier (n+1) L)
    (u : Jet n L) (j : Fin 3) :
    (f.insertionJet u).2 (0,j) =ᵐ[volume]
      fun X ↦ coordDerivative (n+1) L f.toFun (0,j) X*u.1 (Fin.tail X) := by
  change (f.insertionScalar 0+L2Multiplier.clm _ (f.partial_memLp_top (0,j))
    (configurationTailCLM n L u.1)) =ᵐ[volume] _
  rw [map_zero,zero_add]
  filter_upwards [coe_configurationTailCLM u.1,
    L2Multiplier.coe_clm _ (f.partial_memLp_top (0,j)) (configurationTailCLM n L u.1)] with X h1 h2
  exact h2.trans (by rw [h1])

lemma coe_insertionJet_succ {n : ℕ} {L : Length} (f : SmoothMultiplier (n+1) L)
    (u : Jet n L) (i : Fin n) (j : Fin 3) :
    (f.insertionJet u).2 (i.succ,j) =ᵐ[volume]
      fun X ↦ f.toFun X*u.2 (i,j) (Fin.tail X)+
        coordDerivative (n+1) L f.toFun (i.succ,j) X*u.1 (Fin.tail X) := by
  change (f.insertionScalar (u.2 (i,j))+L2Multiplier.clm _ (f.partial_memLp_top (i.succ,j))
    (configurationTailCLM n L u.1)) =ᵐ[volume] _
  filter_upwards [coe_insertionScalar f (u.2 (i,j)),coe_configurationTailCLM u.1,
    L2Multiplier.coe_clm _ (f.partial_memLp_top (i.succ,j)) (configurationTailCLM n L u.1),
    Lp.coeFn_add (f.insertionScalar (u.2 (i,j)))
      (L2Multiplier.clm _ (f.partial_memLp_top (i.succ,j)) (configurationTailCLM n L u.1))]
      with X h1 h2 h3 h4
  rw [h4,Pi.add_apply,h1,h3,h2]

lemma SmoothTest.jet_insert {n : ℕ} {L : Length} {a : ℝ} (g : SmoothTest n L a)
    (f : SmoothMultiplier (n+1) L) (hc : InsertionClearance a f) :
    (g.insert f hc).jet=f.insertionJet g.jet := by
  apply Prod.ext
  · apply Lp.ext
    filter_upwards [MemLp.coeFn_toLp (g.insert f hc).memLp,
      (configurationTail_quasiPreserving n L).ae_eq_comp (MemLp.coeFn_toLp g.memLp),
      coe_insertionScalar f g.jet.1] with X h1 h2 h3
    dsimp only [Function.comp_def] at h2
    change ((g.insert f hc).jet.1) X=(f.insertionScalar g.jet.1) X
    rw [h3]
    dsimp only [SmoothTest.jet]
    rw [h1,h2]
    rfl
  · funext p
    rcases p with ⟨i,j⟩
    refine Fin.cases ?_ (fun k ↦ ?_) i
    · apply Lp.ext
      filter_upwards [MemLp.coeFn_toLp ((g.insert f hc).partial_memLp (0,j)),
        (configurationTail_quasiPreserving n L).ae_eq_comp (MemLp.coeFn_toLp g.memLp),
        coe_insertionJet_zero f g.jet j] with X h1 h2 h3
      dsimp only [Function.comp_def] at h2
      rw [h3]
      dsimp only [SmoothTest.jet]
      rw [h1]
      change coordDerivative (n+1) L (f.toFun*(fun X ↦ g.toFun (Fin.tail X))) (0,j) X=_
      rw [coordDerivative_mul (f.smooth.differentiable (by simp))
        ((smooth_tail g.smooth).differentiable (by simp)),
        coordDerivative_tail_zero (g.smooth.differentiable (by simp))]
      simp only [Pi.add_apply,Pi.mul_apply,Pi.zero_apply,mul_zero,zero_add,h2]
      ring
    · apply Lp.ext
      filter_upwards [MemLp.coeFn_toLp ((g.insert f hc).partial_memLp (k.succ,j)),
        (configurationTail_quasiPreserving n L).ae_eq_comp (MemLp.coeFn_toLp g.memLp),
        (configurationTail_quasiPreserving n L).ae_eq_comp (MemLp.coeFn_toLp (g.partial_memLp (k,j))),
        coe_insertionJet_succ f g.jet k j] with X h1 h2 h3 h4
      dsimp only [Function.comp_def] at h2 h3
      rw [h4]
      dsimp only [SmoothTest.jet]
      rw [h1]
      change coordDerivative (n+1) L (f.toFun*(fun X ↦ g.toFun (Fin.tail X))) (k.succ,j) X=_
      rw [coordDerivative_mul (f.smooth.differentiable (by simp))
        ((smooth_tail g.smooth).differentiable (by simp)),
        coordDerivative_tail_succ (g.smooth.differentiable (by simp))]
      simp only [Pi.add_apply,Pi.mul_apply,h2,h3]
      ring

lemma SmoothMultiplier.insertionJet_mem_domain {n : ℕ} {L : Length} {a : ℝ}
    (f : SmoothMultiplier (n+1) L) (hc : InsertionClearance a f)
    {u : Jet n L} (hu : u∈dirichletDomain n L a) :
    f.insertionJet u∈dirichletDomain (n+1) L a := by
  apply map_mem_closure f.insertionJet.continuous hu
  rintro _ ⟨g,rfl⟩
  exact ⟨g.insert f hc,g.jet_insert f hc⟩

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
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_TorusLiftBox
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
open MeasureTheory Set Filter
open scoped ComplexConjugate
noncomputable section

lemma SmoothMultiplier.normalization_real {n : ℕ} {L : Length} (f : SmoothMultiplier (n+1) L)
    (hr : ∀ X, conj (f.toFun X)=f.toFun X) (hp : ∀ Y, 0<f.fiberMass Y) (X) :
    conj ((f.normalization hr hp).toFun X)=(f.normalization hr hp).toFun X := by
  change conj (f.toFun X/(Real.sqrt (f.fiberMass (Fin.tail X)) : ℂ))=_
  rw [map_div₀,Complex.conj_ofReal,hr]
  rfl

lemma SmoothMultiplier.normalization_norm {n : ℕ} {L : Length} (f : SmoothMultiplier (n+1) L)
    (hr : ∀ X, conj (f.toFun X)=f.toFun X) (hp : ∀ Y, 0<f.fiberMass Y) (Y : Configuration n L) :
    ∫ x : Torus L, ‖(f.normalization hr hp).toFun (Fin.cons x Y)‖^2=1 := by
  change (∫ x : Torus L, ‖f.toFun (Fin.cons x Y)/(Real.sqrt (f.fiberMass Y) : ℂ)‖^2)=1
  simp only [norm_div,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _),div_pow,Real.sq_sqrt (hp Y).le]
  rw [integral_div]
  exact div_self (hp Y).ne'

lemma SmoothMultiplier.normalization_clearance {n : ℕ} {L : Length} {a : ℝ}
    (f : SmoothMultiplier (n+1) L) (hr : ∀ X, conj (f.toFun X)=f.toFun X)
    (hp : ∀ Y, 0<f.fiberMass Y) (hc : InsertionClearance a f) :
    InsertionClearance a (f.normalization hr hp) := by
  apply Set.Subset.trans (b := tsupport f.toFun) _ hc
  change tsupport (fun X ↦ f.toFun X/(Real.sqrt (f.fiberMass (Fin.tail X)) : ℂ))⊆_
  simp only [div_eq_mul_inv]
  exact tsupport_mul_subset_left

lemma integral_norm_add_sq_orthogonal {A : Type*} [TopologicalSpace A] [CompactSpace A]
    [MeasurableSpace A] [BorelSpace A] [SecondCountableTopology A]
    {μ : Measure A} [IsFiniteMeasure μ] {f g : A → ℂ} (hf : Continuous f) (hg : Continuous g)
    (ho : ∫ x, conj (f x)*g x ∂μ=0) :
    ∫ x, ‖f x+g x‖^2 ∂μ=(∫ x, ‖f x‖^2 ∂μ)+(∫ x, ‖g x‖^2 ∂μ) := by
  have hi {E : Type} [NormedAddCommGroup E] {h : A → E} (hc : Continuous h) : Integrable h μ :=
    hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have he (x : A) : ‖f x+g x‖^2=‖f x‖^2+2*(conj (f x)*g x).re+‖g x‖^2 := by
    simpa only [RCLike.inner_apply',RCLike.re_to_complex] using @norm_add_sq ℂ ℂ _ _ _ (f x) (g x)
  simp_rw [he]
  have hf2 : Integrable (fun x ↦ ‖f x‖^2) μ := hi (hf.norm.pow 2)
  have hg2 : Integrable (fun x ↦ ‖g x‖^2) μ := hi (hg.norm.pow 2)
  have hcross : Integrable (fun x ↦ conj (f x)*g x) μ := hi ((Complex.continuous_conj.comp hf).mul hg)
  have hre : Integrable (fun x ↦ 2*(conj (f x)*g x).re) μ := hcross.re.const_mul 2
  have hRe : (∫ x, (conj (f x)*g x).re ∂μ)=(∫ x, conj (f x)*g x ∂μ).re := by
    simpa only [RCLike.re_to_complex] using integral_re hcross
  rw [integral_add (f := fun x ↦ ‖f x‖^2+2*(conj (f x)*g x).re)
      (g := fun x ↦ ‖g x‖^2) (hf2.add hre) hg2, integral_add hf2 hre, integral_const_mul,
    hRe,ho]
  simp

lemma SmoothMultiplier.fiber_derivative_mul_tail_le {n : ℕ} {L : Length}
    (g : SmoothMultiplier (n+1) L) (r : SmoothMultiplier n L)
    (hr : ∀ X, conj (g.toFun X)=g.toFun X)
    (hn : ∀ Y : Configuration n L, ∫ x : Torus L, ‖g.toFun (Fin.cons x Y)‖^2=1)
    (p : Direction (n+1)) (Y : Configuration n L) :
    ‖r.toFun Y‖^2 * (∫ x : Torus L, ‖coordDerivative (n+1) L g.toFun p (Fin.cons x Y)‖^2) ≤
      ∫ x : Torus L, ‖coordDerivative (n+1) L (fun X ↦ g.toFun X*r.toFun (Fin.tail X)) p
        (Fin.cons x Y)‖^2 := by
  have hd := coordDerivative_mul (g := fun X : Configuration (n+1) L ↦ r.toFun (Fin.tail X))
    (g.smooth.differentiable (by simp))
    ((smooth_tail r.smooth).differentiable (by simp)) p
  have hc : Continuous (fun x : Torus L ↦ (Fin.cons x Y : Configuration (n+1) L)) :=
    (continuous_id : Continuous (id : Torus L → Torus L)).finCons
      (continuous_const : Continuous (fun _ : Torus L ↦ Y))
  have hg := (continuous_of_continuous_lift g.smooth.continuous).comp hc
  have hdg := (continuous_coordDerivative g.smooth p).comp hc
  have hs := r.smooth.differentiable (by simp)
  rcases p with ⟨i,j⟩
  induction i using Fin.cases with
  | zero =>
    simp only [coordDerivative_tail_zero hs j,mul_zero,zero_add] at hd
    rw [show (fun X ↦ g.toFun X*r.toFun (Fin.tail X))=g.toFun*(fun X ↦ r.toFun (Fin.tail X)) from rfl,hd]
    simp only [Pi.mul_apply,Fin.tail_cons,norm_mul,mul_pow]
    rw [integral_const_mul]
  | succ k =>
    have he := g.insertion_orthogonal hr hn k j Y
    have ho : (∫ x : Torus L,
        conj (g.toFun (Fin.cons x Y)*coordDerivative n L r.toFun (k,j) Y)*
          (r.toFun Y*coordDerivative (n+1) L g.toFun (k.succ,j) (Fin.cons x Y)))=0 := by
      calc
        _ = (conj (coordDerivative n L r.toFun (k,j) Y)*r.toFun Y)*
            ∫ x : Torus L, conj (g.toFun (Fin.cons x Y))*
              coordDerivative (n+1) L g.toFun (k.succ,j) (Fin.cons x Y) := by
          rw [← integral_const_mul]
          apply integral_congr_ae
          exact Eventually.of_forall fun x ↦ by simp only [map_mul]; ring
        _ = 0 := by rw [he,mul_zero]
    have heq := integral_norm_add_sq_orthogonal (hg.mul continuous_const) (continuous_const.mul hdg) ho
    simp only [Pi.mul_apply,Function.comp_def] at heq
    have hd' := coordDerivative_mul (g := fun X : Configuration (n+1) L ↦ r.toFun (Fin.tail X))
      (g.smooth.differentiable (by simp))
      ((smooth_tail r.smooth).differentiable (by simp)) (k.succ,j)
    rw [coordDerivative_tail_succ hs k j] at hd'
    rw [show (fun X ↦ g.toFun X*r.toFun (Fin.tail X))=g.toFun*(fun X ↦ r.toFun (Fin.tail X)) from rfl,hd']
    simp only [Pi.mul_apply,Pi.add_apply,Fin.tail_cons]
    rw [heq]
    simp only [norm_mul,mul_pow]
    rw [integral_const_mul]
    exact le_add_of_nonneg_left (integral_nonneg fun x ↦ mul_nonneg (sq_nonneg _) (sq_nonneg _))

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
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_RawAngleLift
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
open PeriodicCutoff
open scoped ComplexConjugate

lemma rawCutoff_real (n : ℕ) (L : Length) (r : ℝ) (X : Configuration (n+1) L) :
    conj ((rawCutoff n L r).toFun X)=(rawCutoff n L r).toFun X := Complex.conj_ofReal _

lemma rawCutoff_norm_sq (n : ℕ) (L : Length) (r : ℝ) (X : Configuration (n+1) L) :
    ‖(rawCutoff n L r).toFun X‖^2=rawCutoffReal n L r X^2 := by
  change ‖(rawCutoffReal n L r X : ℂ)‖^2=_
  rw [Complex.norm_real,Real.norm_eq_abs,sq_abs]

lemma rawCutoff_clearance (n : ℕ) (L : Length) {r : ℝ} (hr : 0 < r) :
    InsertionClearance r (rawCutoff n L r) := by
  intro X hX i
  have hs : tsupport (rawCutoff n L r).toFun ⊆
      {X | 2*r^2≤pairQ L.val (X 0) (X i.succ)} := by
    have hc : Continuous (fun X : Configuration (n+1) L ↦ pairQ L.val (X 0) (X i.succ)) :=
      by
        have hp : Continuous (fun X : Configuration (n+1) L ↦ (X 0,X i.succ)) := by fun_prop
        exact (pairQ_continuous L.val).comp hp
    apply closure_minimal ?_ (isClosed_le continuous_const hc)
    intro R hR
    by_contra hn
    have hz : (rawCutoff n L r).toFun R=0 := by
      change ((∏ k : Fin n,Real.sin (angle L.val r (R 0) (R k.succ)) : ℝ) : ℂ)=0
      rw [Finset.prod_eq_zero (Finset.mem_univ i)
        (by rw [angle_zero L.val hr (not_le.mp hn).le,Real.sin_zero]),Complex.ofReal_zero]
    exact hR hz
  have hQ : 2*r^2≤pairQ L.val (X 0) (X i.succ) := hs hX
  have he : torusDistance L (X 0) (X i.succ)^2=
      ∑ j : Fin 3,dist (X 0 j) (X i.succ j)^2 := Real.sq_sqrt (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _)
  have hl := pairQ_le L.val (X 0) (X i.succ)
  have hd : 0≤torusDistance L (X 0) (X i.succ) := Real.sqrt_nonneg _
  nlinarith [sq_pos_of_pos hr]

end HardSphere

namespace HardSphere
open PeriodicCutoff

lemma torus_volume_real (L : Length) : volume.real (Set.univ : Set (Torus L))=L.val^3 := by
  rw [measureReal_def,volume_pi,Measure.pi_univ]
  simp only [AddCircle.measure_univ,Finset.prod_const,Finset.card_univ,Fintype.card_fin,
    ENNReal.toReal_pow,ENNReal.toReal_ofReal L.property.le]

lemma rawCutoff_mass_pointwise (n : ℕ) (L : Length) {r : ℝ} (hr : 0 < r)
    (y : Torus L) (Y : Configuration n L) :
    1≤‖(rawCutoff n L r).toFun (Fin.cons y Y)‖^2+
      ∑ i : Fin n, (box L.val (Real.pi*r) (Y i)).indicator (fun _ ↦ (1:ℝ)) y := by
  rw [rawCutoff_norm_sq]
  have hb (i : Fin n) : 0≤(box L.val (Real.pi*r) (Y i)).indicator (fun _ ↦ (1:ℝ)) y :=
    Set.indicator_nonneg (fun _ _ ↦ zero_le_one) _
  by_cases hh : ∃ i, y∈box L.val (Real.pi*r) (Y i)
  · obtain ⟨i,hi⟩ := hh
    have hs := Finset.single_le_sum (f := fun i : Fin n ↦
      (box L.val (Real.pi*r) (Y i)).indicator (fun _ ↦ (1:ℝ)) y) (fun i _ ↦ hb i) (Finset.mem_univ i)
    rw [Set.indicator_of_mem hi] at hs
    exact hs.trans (le_add_of_nonneg_left (sq_nonneg _))
  · have ha (i : Fin n) : angle L.val r y (Y i)=Real.pi/2 :=
      angle_one_outside L.val hr (fun hi ↦ hh ⟨i,hi⟩)
    have he : rawCutoffReal n L r (Fin.cons y Y)=1 := by
      simp only [rawCutoffReal,Fin.cons_zero,Fin.cons_succ,ha,Real.sin_pi_div_two,Finset.prod_const_one]
    rw [he,one_pow]
    exact le_add_of_nonneg_right (Finset.sum_nonneg (fun i _ ↦ hb i))

lemma rawCutoff_mass_lower (n : ℕ) (L : Length) {r : ℝ} (hr : 0 < r)
    (Y : Configuration n L) : L.val^3-(n:ℝ)*(2*Real.pi*r)^3≤(rawCutoff n L r).fiberMass Y := by
  have hc : Continuous (fun y : Torus L ↦ ‖(rawCutoff n L r).toFun (Fin.cons y Y)‖^2) :=
    (((continuous_of_continuous_lift (rawCutoff n L r).smooth.continuous).comp
      ((continuous_id : Continuous (id : Torus L → Torus L)).finCons
        (continuous_const : Continuous (fun _ : Torus L ↦ Y)))).norm).pow 2
  have hf : Integrable (fun y : Torus L ↦ ‖(rawCutoff n L r).toFun (Fin.cons y Y)‖^2) volume :=
    hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hi (i : Fin n) : Integrable ((box L.val (Real.pi*r) (Y i)).indicator (fun _ ↦ (1:ℝ))) volume :=
    (integrable_const (1:ℝ)).indicator (box_measurable L.val _ _)
  have hh := integral_mono (integrable_const (1:ℝ)) (hf.add (integrable_finsetSum (Finset.univ : Finset (Fin n)) (fun i _ ↦ hi i)))
    (fun y ↦ rawCutoff_mass_pointwise n L hr y Y)
  dsimp only [Pi.add_apply] at hh
  rw [integral_const,smul_eq_mul,mul_one,torus_volume_real,
    integral_add hf (integrable_finsetSum (Finset.univ : Finset (Fin n)) (fun i _ ↦ hi i)),
    integral_finsetSum (Finset.univ : Finset (Fin n)) (fun i _ ↦ hi i)] at hh
  have hv : (∑ i : Fin n, ∫ y : Torus L, (box L.val (Real.pi*r) (Y i)).indicator (fun _ ↦ (1:ℝ)) y)≤
      (n:ℝ)*(2*Real.pi*r)^3 := by
    calc
      _ = ∑ i : Fin n, volume.real (box L.val (Real.pi*r) (Y i)) := by
        apply Finset.sum_congr rfl
        intro i _
        exact integral_indicator_one (box_measurable L.val _ _)
      _ ≤ ∑ i : Fin n, (2*(Real.pi*r))^3 := Finset.sum_le_sum (fun i _ ↦ box_volume_le L.val (by positivity) (Y i))
      _ = _ := by simp [mul_assoc]
  change L.val^3-(n:ℝ)*(2*Real.pi*r)^3≤∫ y : Torus L, ‖(rawCutoff n L r).toFun (Fin.cons y Y)‖^2
  linarith

lemma rawAngleLift_fderiv (n : ℕ) (L : Length) (r : ℝ) (i : Fin n)
    (R v : LiftedConfiguration (n+1)) :
    fderiv ℝ (rawAngleLift n L r i) R v =
      ∑ j : Fin 3, anglePartial L.val r (R 0-R i.succ) j*(v 0 j-v i.succ j) := by
  have hd : HasDerivAt (fun t : ℝ ↦ R+t • v) v 0 := by
    simpa using ((hasDerivAt_id (0:ℝ)).smul_const v).const_add R
  have hf := (((rawAngleLift_smooth n L r i).differentiable (by simp)) R).hasFDerivAt.comp_hasDerivAt_of_eq 0 hd (by simp)
  have ha := angleLift_derivative L.val r
    (fun j t ↦ (R 0 j+t*v 0 j)-(R i.succ j+t*v i.succ j))
    (fun j ↦ v 0 j-v i.succ j) 0 (fun j ↦ by
      convert (((hasDerivAt_id (0:ℝ)).mul_const (v 0 j)).const_add (R 0 j)).sub
        (((hasDerivAt_id (0:ℝ)).mul_const (v i.succ j)).const_add (R i.succ j)) using 1 <;> first | rfl | simp only [one_mul])
  have he : (rawAngleLift n L r i ∘ fun t : ℝ ↦ R+t • v)=
      (fun t : ℝ ↦ angleLift L.val r (fun j ↦ (R 0 j+t*v 0 j)-(R i.succ j+t*v i.succ j))) := rfl
  rw [he] at hf
  convert hf.unique ha using 1
  all_goals try with_reducible_and_instances rfl
  simp only [zero_mul,add_zero]
  rfl

lemma rawAngleLift_fderiv_coord (n : ℕ) (L : Length) (r : ℝ) (i : Fin n)
    (R : LiftedConfiguration (n+1)) (p : Direction (n+1)) :
    fderiv ℝ (rawAngleLift n L r i) R (Pi.single p.1 (Pi.single p.2 1)) =
      ((if p.1=0 then (1:ℝ) else 0)-(if p.1=i.succ then 1 else 0))*
        anglePartial L.val r (R 0-R i.succ) p.2 := by
  rw [rawAngleLift_fderiv]
  by_cases h0 : p.1=0 <;> by_cases hi : p.1=i.succ
  · exact False.elim (Fin.succ_ne_zero i (hi.symm.trans h0))
  · simp [h0,Pi.single_apply,eq_comm,Finset.sum_ite_eq',mul_comm]
  · simp [hi,Pi.single_apply,eq_comm,Finset.sum_ite_eq',mul_comm]
  · simp [h0,hi,Ne.symm h0,Ne.symm hi]

lemma rawCutoff_derivative_sq_le (n : ℕ) (L : Length) (r : ℝ)
    (X : Configuration (n+1) L) (p : Direction (n+1)) :
    ‖coordDerivative (n+1) L (rawCutoff n L r).toFun p X‖^2≤
      ∑ i : Fin n, (fderiv ℝ (rawAngleLift n L r i) (representative (n+1) L X)
        (Pi.single p.1 (Pi.single p.2 1)))^2 := by
  let R := representative (n+1) L X
  let v : LiftedConfiguration (n+1) := Pi.single p.1 (Pi.single p.2 1)
  have he : (fun Y : LiftedConfiguration (n+1) ↦ (rawCutoff n L r).toFun (project (n+1) L Y))=
      Complex.ofRealCLM ∘ (fun Y : LiftedConfiguration (n+1) ↦ ∏ i : Fin n, Real.sin (rawAngleLift n L r i Y)) := by
    funext Y
    change (rawCutoffReal n L r (project (n+1) L Y) : ℂ)=_
    simp only [rawCutoffReal,angle_project,Function.comp_apply,Complex.ofRealCLM_apply]
  have hd := (rawCutoffReal_smooth n L r).differentiable (by simp)
  simp only [rawCutoffReal,angle_project] at hd
  change ‖fderiv ℝ (fun Y ↦ (rawCutoff n L r).toFun (project (n+1) L Y)) R v‖^2≤_
  rw [he,fderiv_comp R Complex.ofRealCLM.differentiableAt (hd R),Complex.ofRealCLM.fderiv]
  simp only [ContinuousLinearMap.comp_apply,Complex.ofRealCLM_apply,Complex.norm_real,Real.norm_eq_abs,sq_abs]
  exact SineProduct.fderiv_sq_le Finset.univ (rawAngleLift n L r) R v
    (fun i _ ↦ (rawAngleLift_smooth n L r i).differentiable (by simp) R)

end HardSphere

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Comparison_RawAngleLiftSumSquares
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
open PeriodicCutoff

lemma rawAngleLift_sum_squares (n : ℕ) (L : Length) (r : ℝ) (i : Fin n)
    (R : LiftedConfiguration (n+1)) :
    (∑ p : Direction (n+1), (fderiv ℝ (rawAngleLift n L r i) R
      (Pi.single p.1 (Pi.single p.2 1)))^2)=
      2*∑ j : Fin 3, anglePartial L.val r (R 0-R i.succ) j^2 := by
  simp only [rawAngleLift_fderiv_coord]
  rw [Fintype.sum_prod_type,Fin.sum_univ_succ]
  simp only [Fin.succ_ne_zero,Ne.symm (Fin.succ_ne_zero i),ite_true,ite_false,sub_zero,one_mul,
    Fin.succ_inj,zero_sub,neg_mul,neg_sq]
  have he : (∑ k : Fin n, ∑ j : Fin 3,
      ((if k=i then (1:ℝ) else 0)*anglePartial L.val r (R 0-R i.succ) j)^2)=
      ∑ j : Fin 3, anglePartial L.val r (R 0-R i.succ) j^2 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    simp
  rw [he]
  ring

lemma pairQ_representative (n : ℕ) (L : Length) (i : Fin n) (X : Configuration (n+1) L) :
    pairQ L.val (X 0) (X i.succ)=qLift L.val
      (representative (n+1) L X 0-representative (n+1) L X i.succ) := by
  calc
    _ = pairQ L.val (project (n+1) L (representative (n+1) L X) 0)
      (project (n+1) L (representative (n+1) L X) i.succ) := by rw [project_representative]
    _ = _ := pairQ_coe L.val _ _

lemma rawAngleLift_gradient_le (n : ℕ) (L : Length) {r M : ℝ} (hr : 0 < r) (hM : 0≤M)
    (hb : ∀ t : ℝ, |deriv Real.smoothTransition t|≤M)
    (i : Fin n) (X : Configuration (n+1) L) :
    (∑ p : Direction (n+1), (fderiv ℝ (rawAngleLift n L r i) (representative (n+1) L X)
      (Pi.single p.1 (Pi.single p.2 1)))^2)≤
      (6*Real.pi^2*M^2/r^2)*(box L.val (Real.pi*r) (X i.succ)).indicator (fun _ ↦ (1:ℝ)) (X 0) := by
  rw [rawAngleLift_sum_squares]
  by_cases hx : X 0∈box L.val (Real.pi*r) (X i.succ)
  · rw [Set.indicator_of_mem hx,mul_one]
    have hh := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin 3)))
      (fun j _ ↦ anglePartial_sq_le L.val hr hM hb
        (representative (n+1) L X 0-representative (n+1) L X i.succ) j)
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at hh
    calc
      _ ≤ 2*((3:ℝ)*(Real.pi^2*M^2/r^2)) := mul_le_mul_of_nonneg_left hh (by norm_num)
      _ = _ := by ring
  · rw [Set.indicator_of_notMem hx,mul_zero]
    have hq := not_mem_box_pairQ L.val hr hx
    rw [pairQ_representative] at hq
    have hz : qLift L.val (representative (n+1) L X 0-representative (n+1) L X i.succ)∉Icc (2*r^2) (4*r^2) :=
      fun hs ↦ (not_lt.mpr hs.2) hq
    simp [anglePartial_eq_zero L.val hr hz]

lemma rawCutoff_gradient_le (n : ℕ) (L : Length) {r M : ℝ} (hr : 0 < r) (hM : 0≤M)
    (hb : ∀ t : ℝ, |deriv Real.smoothTransition t|≤M) (X : Configuration (n+1) L) :
    (∑ p : Direction (n+1), ‖coordDerivative (n+1) L (rawCutoff n L r).toFun p X‖^2)≤
      (6*Real.pi^2*M^2/r^2)*∑ i : Fin n,
        (box L.val (Real.pi*r) (X i.succ)).indicator (fun _ ↦ (1:ℝ)) (X 0) := by
  calc
    _ ≤ ∑ p : Direction (n+1), ∑ i : Fin n,
        (fderiv ℝ (rawAngleLift n L r i) (representative (n+1) L X)
          (Pi.single p.1 (Pi.single p.2 1)))^2 :=
      Finset.sum_le_sum fun p _ ↦ rawCutoff_derivative_sq_le n L r X p
    _ = ∑ i : Fin n, ∑ p : Direction (n+1),
        (fderiv ℝ (rawAngleLift n L r i) (representative (n+1) L X)
          (Pi.single p.1 (Pi.single p.2 1)))^2 := by rw [Finset.sum_comm]
    _ ≤ ∑ i : Fin n, (6*Real.pi^2*M^2/r^2)*
        (box L.val (Real.pi*r) (X i.succ)).indicator (fun _ ↦ (1:ℝ)) (X 0) :=
      Finset.sum_le_sum fun i _ ↦ rawAngleLift_gradient_le n L hr hM hb i X
    _ = _ := (Finset.mul_sum ..).symm

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
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_IntegralConfigurationCons
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

lemma integral_configuration_cons {n : ℕ} {L : Length} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (F : Configuration (n+1) L → E)
    (hF : Integrable F volume) :
    ∫ X, F X = ∫ Y : Configuration n L, ∫ x : Torus L, F (Fin.cons x Y) := by
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) ↦ Torus L) 0
  have he := (volume_preserving_piFinSuccAbove (fun _ : Fin (n+1) ↦ Torus L) 0).symm
  have hi := (he.integrable_comp_emb e.symm.measurableEmbedding).mpr hF
  rw [← he.integral_comp' F]
  simp only [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
    Equiv.coe_fn_mk, Fin.insertNth_zero', Function.comp_def] at hi ⊢
  exact integral_prod_symm _ hi

lemma coe_weightedTail {n : ℕ} {L : Length} (h : Configuration (n+1) L → ℂ)
    (hh : MemLp h ∞ volume) (u : ScalarL2 n L) :
    L2Multiplier.clm h hh (configurationTailCLM n L u) =ᵐ[volume] fun X ↦ h X*u (Fin.tail X) := by
  filter_upwards [coe_configurationTailCLM u,
    L2Multiplier.coe_clm h hh (configurationTailCLM n L u)] with X h1 h2
  exact h2.trans (by rw [h1])

lemma weightedTail_pairing {n : ℕ} {L : Length}
    (f g : Configuration (n+1) L → ℂ) (hf : MemLp f ∞ volume) (hg : MemLp g ∞ volume)
    (u v : ScalarL2 n L) :
    inner ℂ (L2Multiplier.clm f hf (configurationTailCLM n L u))
      (L2Multiplier.clm g hg (configurationTailCLM n L v)) =
      ∫ Y : Configuration n L, (conj (u Y)*v Y)*
        ∫ x : Torus L, conj (f (Fin.cons x Y))*g (Fin.cons x Y) := by
  have hfm : MemLp (fun X : Configuration (n+1) L ↦ f X*u (Fin.tail X)) 2 volume :=
    (memLp_configurationTail (Lp.memLp u)).mul hf
  have hgm : MemLp (fun X : Configuration (n+1) L ↦ g X*v (Fin.tail X)) 2 volume :=
    (memLp_configurationTail (Lp.memLp v)).mul hg
  have hi : Integrable (fun X : Configuration (n+1) L ↦
      conj (f X*u (Fin.tail X))*(g X*v (Fin.tail X))) volume := by
    have h := (hfm.inner_const (𝕜 := ℂ) (1:ℂ)).integrable_mul hgm
    exact h.congr (Eventually.of_forall fun X ↦ by
      dsimp only [Pi.mul_apply]
      rw [RCLike.inner_apply,one_mul])
  rw [L2.inner_def]
  calc
    _ = ∫ X : Configuration (n+1) L, conj (f X*u (Fin.tail X))*(g X*v (Fin.tail X)) := by
      apply integral_congr_ae
      filter_upwards [coe_weightedTail f hf u,coe_weightedTail g hg v] with X h1 h2
      simp only [h1,h2,RCLike.inner_apply']
    _ = ∫ Y : Configuration n L, ∫ x : Torus L,
        conj (f (Fin.cons x Y)*u Y)*(g (Fin.cons x Y)*v Y) := by
      simpa only [Fin.tail_cons] using integral_configuration_cons _ hi
    _ = _ := by
      apply integral_congr_ae
      exact Eventually.of_forall fun Y ↦ by
        dsimp only
        rw [← integral_const_mul]
        apply integral_congr_ae
        exact Eventually.of_forall fun x ↦ by simp only [map_mul]; ring

lemma norm_weightedTail_sq {n : ℕ} {L : Length}
    (f : Configuration (n+1) L → ℂ) (hf : MemLp f ∞ volume) (u : ScalarL2 n L) :
    ‖L2Multiplier.clm f hf (configurationTailCLM n L u)‖^2 =
      ∫ Y : Configuration n L, ‖u Y‖^2 * ∫ x : Torus L, ‖f (Fin.cons x Y)‖^2 := by
  have hm : MemLp (fun X : Configuration (n+1) L ↦ f X*u (Fin.tail X)) 2 volume :=
    (memLp_configurationTail (Lp.memLp u)).mul hf
  rw [IndicatorStrong.norm_sq_integral]
  calc
    _ = ∫ X : Configuration (n+1) L, ‖f X*u (Fin.tail X)‖^2 := by
      exact integral_congr_ae ((coe_weightedTail f hf u).mono fun _ h ↦ by dsimp only at h ⊢; rw [h])
    _ = ∫ Y : Configuration n L, ∫ x : Torus L, ‖f (Fin.cons x Y)*u Y‖^2 := by
      simpa only [Fin.tail_cons] using integral_configuration_cons _ (hm.integrable_norm_pow (by decide : (2:ℕ)≠0))
    _ = _ := by
      apply integral_congr_ae
      exact Eventually.of_forall fun Y ↦ by
        dsimp only
        rw [← integral_const_mul]
        apply integral_congr_ae
        exact Eventually.of_forall fun x ↦ by dsimp only; rw [norm_mul,mul_pow,mul_comm]

lemma SmoothMultiplier.norm_insertionScalar_sq {n : ℕ} {L : Length}
    (f : SmoothMultiplier (n+1) L)
    (hn : ∀ Y : Configuration n L, ∫ x : Torus L, ‖f.toFun (Fin.cons x Y)‖^2=1)
    (u : ScalarL2 n L) : ‖f.insertionScalar u‖^2=‖u‖^2 := by
  rw [SmoothMultiplier.insertionScalar,ContinuousLinearMap.comp_apply,SmoothMultiplier.onScalar,
    norm_weightedTail_sq,IndicatorStrong.norm_sq_integral]
  simp only [hn,mul_one]

lemma SmoothMultiplier.norm_insertionScalar {n : ℕ} {L : Length}
    (f : SmoothMultiplier (n+1) L)
    (hn : ∀ Y : Configuration n L, ∫ x : Torus L, ‖f.toFun (Fin.cons x Y)‖^2=1)
    (u : ScalarL2 n L) : ‖f.insertionScalar u‖=‖u‖ :=
  (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp (f.norm_insertionScalar_sq hn u)

lemma SmoothMultiplier.insertion_cross_zero {n : ℕ} {L : Length}
    (f : SmoothMultiplier (n+1) L) (p : Direction (n+1))
    (ho : ∀ Y : Configuration n L, ∫ x : Torus L,
      conj (f.toFun (Fin.cons x Y))*coordDerivative (n+1) L f.toFun p (Fin.cons x Y)=0)
    (u v : ScalarL2 n L) :
    inner ℂ (f.insertionScalar u)
      (L2Multiplier.clm _ (f.partial_memLp_top p) (configurationTailCLM n L v))=0 := by
  rw [SmoothMultiplier.insertionScalar,ContinuousLinearMap.comp_apply,SmoothMultiplier.onScalar,
    weightedTail_pairing]
  simp only [ho,mul_zero,integral_zero]

end HardSphere

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_FormDomain_EnergyInsertionJet
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

lemma SmoothMultiplier.energy_insertionJet {n : ℕ} {L : Length}
    (f : SmoothMultiplier (n+1) L)
    (hn : ∀ Y : Configuration n L, ∫ x : Torus L, ‖f.toFun (Fin.cons x Y)‖^2=1)
    (ho : ∀ (i : Fin n) (j : Fin 3) (Y : Configuration n L), ∫ x : Torus L,
      conj (f.toFun (Fin.cons x Y))*coordDerivative (n+1) L f.toFun (i.succ,j) (Fin.cons x Y)=0)
    (u : Jet n L) :
    energy (f.insertionJet u)=energy u + ∑ p : Direction (n+1),
      ‖L2Multiplier.clm _ (f.partial_memLp_top p) (configurationTailCLM n L u.1)‖^2 := by
  have hz (j : Fin 3) : (f.insertionJet u).2 (0,j)=
      L2Multiplier.clm _ (f.partial_memLp_top (0,j)) (configurationTailCLM n L u.1) := by
    change f.insertionScalar 0 + _ = _
    rw [map_zero,zero_add]
    rfl
  have hs (i : Fin n) (j : Fin 3) : ‖(f.insertionJet u).2 (i.succ,j)‖^2=
      ‖u.2 (i,j)‖^2+
      ‖L2Multiplier.clm _ (f.partial_memLp_top (i.succ,j)) (configurationTailCLM n L u.1)‖^2 := by
    change ‖f.insertionScalar (u.2 (i,j)) +
      L2Multiplier.clm _ (f.partial_memLp_top (i.succ,j)) (configurationTailCLM n L u.1)‖^2 = _
    rw [@norm_add_sq ℂ, f.insertion_cross_zero (i.succ,j) (ho i j),map_zero,
      mul_zero,add_zero,f.norm_insertionScalar hn]
  unfold energy
  simp only [Fintype.sum_prod_type,Fin.sum_univ_succ,hz,hs,Finset.sum_add_distrib]
  ring

lemma SmoothMultiplier.insertion_derivative_integrable {n : ℕ} {L : Length}
    (f : SmoothMultiplier (n+1) L) (u : ScalarL2 n L) (p : Direction (n+1)) :
    Integrable (fun Y : Configuration n L ↦ ‖u Y‖^2 *
      ∫ x : Torus L, ‖coordDerivative (n+1) L f.toFun p (Fin.cons x Y)‖^2) volume := by
  have hm := ((memLp_configurationTail (Lp.memLp u)).mul (f.partial_memLp_top p)).integrable_norm_pow
    (by decide : (2:ℕ)≠0)
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) ↦ Torus L) 0
  have he := (volume_preserving_piFinSuccAbove (fun _ : Fin (n+1) ↦ Torus L) 0).symm
  have hi := (he.integrable_comp_emb e.symm.measurableEmbedding).mpr hm
  simp only [MeasurableEquiv.piFinSuccAbove_symm_apply,Fin.insertNthEquiv,
    Equiv.coe_fn_mk,Fin.insertNth_zero',Function.comp_def,Pi.mul_apply,Fin.tail_cons] at hi
  convert hi.integral_prod_right using 1
  all_goals try with_reducible_and_instances rfl
  funext Y
  rw [← integral_const_mul]
  apply integral_congr_ae
  exact Eventually.of_forall fun x ↦ by dsimp only; rw [norm_mul,mul_pow,mul_comm]

lemma SmoothMultiplier.energy_insertionJet_integral {n : ℕ} {L : Length}
    (f : SmoothMultiplier (n+1) L)
    (hn : ∀ Y : Configuration n L, ∫ x : Torus L, ‖f.toFun (Fin.cons x Y)‖^2=1)
    (ho : ∀ (i : Fin n) (j : Fin 3) (Y : Configuration n L), ∫ x : Torus L,
      conj (f.toFun (Fin.cons x Y))*coordDerivative (n+1) L f.toFun (i.succ,j) (Fin.cons x Y)=0)
    (u : Jet n L) :
    energy (f.insertionJet u)=energy u + ∫ Y : Configuration n L,
      ‖u.1 Y‖^2 * ∑ p : Direction (n+1), ∫ x : Torus L,
        ‖coordDerivative (n+1) L f.toFun p (Fin.cons x Y)‖^2 := by
  rw [f.energy_insertionJet hn ho]
  simp_rw [norm_weightedTail_sq,Finset.mul_sum]
  rw [integral_finsetSum _ (fun p _ ↦ f.insertion_derivative_integrable u.1 p)]

lemma SmoothMultiplier.energy_insertionJet_le {n : ℕ} {L : Length}
    (f : SmoothMultiplier (n+1) L)
    (hn : ∀ Y : Configuration n L, ∫ x : Torus L, ‖f.toFun (Fin.cons x Y)‖^2=1)
    (ho : ∀ (i : Fin n) (j : Fin 3) (Y : Configuration n L), ∫ x : Torus L,
      conj (f.toFun (Fin.cons x Y))*coordDerivative (n+1) L f.toFun (i.succ,j) (Fin.cons x Y)=0)
    (C : ℝ) (hC : ∀ Y : Configuration n L,
      ∑ p : Direction (n+1), ∫ x : Torus L, ‖coordDerivative (n+1) L f.toFun p (Fin.cons x Y)‖^2≤C)
    (u : Jet n L) : energy (f.insertionJet u)≤energy u + C*‖u.1‖^2 := by
  rw [f.energy_insertionJet_integral hn ho,IndicatorStrong.norm_sq_integral,← integral_const_mul]
  apply add_le_add_right
  apply integral_mono
  · simpa only [Finset.mul_sum] using integrable_finsetSum _
      (fun p _ ↦ f.insertion_derivative_integrable u.1 p)
  · exact (Lp.memLp u.1).integrable_norm_pow (by decide : (2:ℕ)≠0) |>.const_mul C
  · intro Y
    simpa only [mul_comm C] using mul_le_mul_of_nonneg_left (hC Y) (sq_nonneg ‖u.1 Y‖)

end HardSphere

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Collisions_NormalizedInsertion
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

lemma SmoothMultiplier.normalized_insertion {n : ℕ} {L : Length} {a C : ℝ}
    (f : SmoothMultiplier (n+1) L) (hc : InsertionClearance a f)
    (hr : ∀ X, conj (f.toFun X)=f.toFun X)
    (hn : ∀ Y : Configuration n L, ∫ x : Torus L, ‖f.toFun (Fin.cons x Y)‖^2=1)
    (hC : ∀ Y : Configuration n L,
      ∑ p : Direction (n+1), ∫ x : Torus L, ‖coordDerivative (n+1) L f.toFun p (Fin.cons x Y)‖^2≤C)
    {u : Jet n L} (hu : u∈dirichletDomain n L a) :
    f.insertionJet u∈dirichletDomain (n+1) L a ∧
      ‖(f.insertionJet u).1‖=‖u.1‖ ∧ energy (f.insertionJet u)≤energy u+C*‖u.1‖^2 := by
  refine ⟨f.insertionJet_mem_domain hc hu,?_,?_⟩
  · exact f.norm_insertionScalar hn u.1
  · exact f.energy_insertionJet_le hn (f.insertion_orthogonal hr hn) C hC u
end HardSphere

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_NormalizationDerivative
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

lemma SmoothMultiplier.normalization_derivative_le {n : ℕ} {L : Length}
    (f : SmoothMultiplier (n+1) L) (hr : ∀ X, conj (f.toFun X)=f.toFun X)
    (hp : ∀ Y, 0<f.fiberMass Y) (p : Direction (n+1)) (Y : Configuration n L) :
    f.fiberMass Y * (∫ x : Torus L,
      ‖coordDerivative (n+1) L (f.normalization hr hp).toFun p (Fin.cons x Y)‖^2) ≤
      ∫ x : Torus L, ‖coordDerivative (n+1) L f.toFun p (Fin.cons x Y)‖^2 := by
  have he : (fun X ↦ (f.normalization hr hp).toFun X *
      (f.massRoot hr hp).toFun (Fin.tail X))=f.toFun := by
    funext X
    exact div_mul_cancel₀ _ (Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (hp _)).ne')
  have hh := (f.normalization hr hp).fiber_derivative_mul_tail_le (f.massRoot hr hp)
    (f.normalization_real hr hp) (f.normalization_norm hr hp) p Y
  rw [he] at hh
  have hn : ‖(f.massRoot hr hp).toFun Y‖^2=f.fiberMass Y := by
    change ‖(Real.sqrt (f.fiberMass Y) : ℂ)‖^2=_
    rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _),Real.sq_sqrt (hp Y).le]
  rwa [hn] at hh

lemma SmoothMultiplier.insertion_from_raw {n : ℕ} {L : Length} {a C z : ℝ}
    (f : SmoothMultiplier (n+1) L) (hc : InsertionClearance a f)
    (hr : ∀ X, conj (f.toFun X)=f.toFun X) (hz : 0<z)
    (hZ : ∀ Y : Configuration n L, z≤f.fiberMass Y)
    (hC : ∀ Y : Configuration n L,
      ∑ p : Direction (n+1), ∫ x : Torus L, ‖coordDerivative (n+1) L f.toFun p (Fin.cons x Y)‖^2≤C)
    {u : Jet n L} (hu : u∈dirichletDomain n L a) :
    ∃ v : Jet (n+1) L, v∈dirichletDomain (n+1) L a ∧
      ‖v.1‖=‖u.1‖ ∧ energy v≤energy u+(C/z)*‖u.1‖^2 := by
  have hp : ∀ Y, 0<f.fiberMass Y := fun Y ↦ hz.trans_le (hZ Y)
  refine ⟨(f.normalization hr hp).insertionJet u,?_⟩
  refine (f.normalization hr hp).normalized_insertion (f.normalization_clearance hr hp hc)
    (f.normalization_real hr hp) (f.normalization_norm hr hp) ?_ hu
  intro Y
  rw [le_div_iff₀ hz,mul_comm]
  calc
    z * ∑ p : Direction (n+1), ∫ x : Torus L,
        ‖coordDerivative (n+1) L (f.normalization hr hp).toFun p (Fin.cons x Y)‖^2 ≤
      f.fiberMass Y * ∑ p : Direction (n+1), ∫ x : Torus L,
        ‖coordDerivative (n+1) L (f.normalization hr hp).toFun p (Fin.cons x Y)‖^2 := by
      apply mul_le_mul_of_nonneg_right (hZ Y)
      exact Finset.sum_nonneg fun p _ ↦ integral_nonneg fun x ↦ sq_nonneg _
    _ ≤ ∑ p : Direction (n+1), ∫ x : Torus L,
        ‖coordDerivative (n+1) L f.toFun p (Fin.cons x Y)‖^2 := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum fun p _ ↦ f.normalization_derivative_le hr hp p Y
    _ ≤ C := hC Y

end HardSphere

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_FormDomain_RawCutoffGradientIntegral
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
open PeriodicCutoff

lemma rawCutoff_gradient_integral_le (n : ℕ) (L : Length) {r M : ℝ} (hr : 0 < r) (hM : 0≤M)
    (hb : ∀ t : ℝ, |deriv Real.smoothTransition t|≤M) (Y : Configuration n L) :
    (∑ p : Direction (n+1), ∫ y : Torus L,
      ‖coordDerivative (n+1) L (rawCutoff n L r).toFun p (Fin.cons y Y)‖^2)≤
      48*Real.pi^5*M^2*(n:ℝ)*r := by
  have hf (p : Direction (n+1)) : Integrable (fun y : Torus L ↦
      ‖coordDerivative (n+1) L (rawCutoff n L r).toFun p (Fin.cons y Y)‖^2) volume := by
    have hc : Continuous (fun y : Torus L ↦
        ‖coordDerivative (n+1) L (rawCutoff n L r).toFun p (Fin.cons y Y)‖^2) :=
      (((continuous_coordDerivative (rawCutoff n L r).smooth p).comp
        ((continuous_id : Continuous (id : Torus L → Torus L)).finCons
          (continuous_const : Continuous (fun _ : Torus L ↦ Y)))).norm).pow 2
    exact hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hi (i : Fin n) : Integrable ((box L.val (Real.pi*r) (Y i)).indicator (fun _ ↦ (1:ℝ))) volume :=
    (integrable_const (1:ℝ)).indicator (box_measurable L.val _ _)
  have hh := integral_mono (integrable_finsetSum Finset.univ (fun p _ ↦ hf p))
    ((integrable_finsetSum Finset.univ (fun i _ ↦ hi i)).const_mul (6*Real.pi^2*M^2/r^2))
    (fun y : Torus L ↦ rawCutoff_gradient_le n L hr hM hb (Fin.cons y Y))
  rw [integral_finsetSum _ (fun p _ ↦ hf p),integral_const_mul,
    integral_finsetSum _ (fun i _ ↦ hi i)] at hh
  have hv : (∑ i : Fin n, ∫ y : Torus L, (box L.val (Real.pi*r) (Y i)).indicator (fun _ ↦ (1:ℝ)) y)≤
      (n:ℝ)*(2*Real.pi*r)^3 := by
    calc
      _ = ∑ i : Fin n, volume.real (box L.val (Real.pi*r) (Y i)) := by
        apply Finset.sum_congr rfl
        intro i _
        exact integral_indicator_one (box_measurable L.val _ _)
      _ ≤ ∑ i : Fin n, (2*(Real.pi*r))^3 := Finset.sum_le_sum (fun i _ ↦ box_volume_le L.val (by positivity) (Y i))
      _ = _ := by simp [mul_assoc]
  calc
    _ ≤ (6*Real.pi^2*M^2/r^2)*∑ i : Fin n, ∫ y : Torus L,
        (box L.val (Real.pi*r) (Y i)).indicator (fun _ ↦ (1:ℝ)) y := hh
    _ ≤ (6*Real.pi^2*M^2/r^2)*((n:ℝ)*(2*Real.pi*r)^3) :=
      mul_le_mul_of_nonneg_left hv (by positivity)
    _ = _ := by field_simp [hr.ne']; ring

lemma uniform_insertion : ∃ C : ℝ, 0<C ∧ ∀ (n : ℕ) (L : Length) (r : ℝ), 0 < r →
    (n:ℝ)*(2*Real.pi*r)^3≤L.val^3/2 →
    ∀ u : Jet n L, u∈dirichletDomain n L r →
      ∃ v : Jet (n+1) L, v∈dirichletDomain (n+1) L r ∧
        ‖v.1‖=‖u.1‖ ∧ energy v≤energy u+(C*(n:ℝ)*r/L.val^3)*‖u.1‖^2 := by
  obtain ⟨M,hM,hb⟩ := exists_transition_bound
  refine ⟨96*Real.pi^5*M^2,by positivity,fun n L r hr hs u hu ↦ ?_⟩
  have hL := L.property
  have hZ (Y : Configuration n L) : L.val^3/2≤(rawCutoff n L r).fiberMass Y := by
    linarith [rawCutoff_mass_lower n L hr Y]
  obtain ⟨v,hv,hn,he⟩ := (rawCutoff n L r).insertion_from_raw
    (rawCutoff_clearance n L hr) (rawCutoff_real n L r) (show 0<L.val^3/2 by positivity)
    hZ (rawCutoff_gradient_integral_le n L hr hM.le hb) hu
  refine ⟨v,hv,hn,?_⟩
  convert he using 1
  all_goals try with_reducible_and_instances rfl
  congr 2
  ring

end HardSphere

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

end HardSphere

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Operators_Regularize
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
namespace HilbertRegularization
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma hasFDerivAt {ε : ℝ} (hε : 0<ε) (z : E) :
    HasFDerivAt (regularize ε) (differential ε z) z := by
  have hn : ‖z‖^2+ε^2≠0 := by positivity
  have h := Complex.ofRealCLM.hasFDerivAt.comp z
    ((((hasStrictFDerivAt_norm_sq z).hasFDerivAt.add_const (ε^2)).sqrt hn).sub_const ε)
  have hd : differential ε z = Complex.ofRealCLM.comp
      ((1/(2*Real.sqrt (‖z‖^2+ε^2))) • (2 • innerSL ℝ z)) := by
    ext w
    simp [differential,two_smul,div_eq_mul_inv,mul_inv_rev]
    ring
  rw [hd]
  exact h

omit [InnerProductSpace ℝ E] in
lemma sqroot_ge_norm (ε : ℝ) (z : E) : ‖z‖≤Real.sqrt (‖z‖^2+ε^2) :=
  (Real.le_sqrt (norm_nonneg _) (by positivity)).mpr (by nlinarith [sq_nonneg ε])

lemma differential_apply_le (ε : ℝ) (z w : E) : ‖differential ε z w‖≤‖w‖ := by
  by_cases hz : z=0
  · simp [hz,differential]
  have hp : 0<Real.sqrt (‖z‖^2+ε^2) :=
    lt_of_lt_of_le (norm_pos_iff.mpr hz) (sqroot_ge_norm ε z)
  simp only [differential,smul_apply,ContinuousLinearMap.comp_apply,norm_smul,
    Complex.ofRealCLM_apply,Complex.norm_real,Real.norm_eq_abs,abs_inv,abs_of_pos hp,innerSL_apply_apply]
  change _*‖inner ℝ z w‖≤_
  apply le_trans (mul_le_mul_of_nonneg_left (norm_inner_le_norm (𝕜 := ℝ) z w) (by positivity :
    0≤(Real.sqrt (‖z‖^2+ε^2))⁻¹))
  rw [← div_eq_inv_mul,div_le_iff₀ hp]
  simpa only [mul_comm] using mul_le_mul_of_nonneg_right (sqroot_ge_norm ε z) (norm_nonneg w)

lemma differential_le (ε : ℝ) (z : E) : ‖differential ε z‖≤1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro w
  simpa only [one_mul] using differential_apply_le ε z w

lemma fderiv_eq {ε : ℝ} (hε : 0<ε) (z : E) :
    fderiv ℝ (regularize ε) z=differential ε z := (hasFDerivAt hε z).fderiv

lemma lipschitz {ε : ℝ} (hε : 0<ε) : LipschitzWith 1 (regularize (E := E) ε) :=
  lipschitzWith_of_nnnorm_fderiv_le ((smooth hε).differentiable (by simp))
    (fun z ↦ by rw [fderiv_eq hε]; exact NNReal.coe_le_coe.mp (differential_le ε z))

lemma norm_le {ε : ℝ} (hε : 0<ε) (z : E) : ‖regularize ε z‖≤‖z‖ := by
  simpa only [zero hε.le,sub_zero,NNReal.coe_one,one_mul] using
    (lipschitz hε).norm_sub_le z 0

omit [InnerProductSpace ℝ E] in
lemma tendsto_regularize (z : E) {e : ℕ → ℝ} (he : Tendsto e atTop (𝓝 0)) :
    Tendsto (fun n ↦ regularize (e n) z) atTop (𝓝 (‖z‖ : ℂ)) := by
  have h : Tendsto (fun n ↦ Real.sqrt (‖z‖^2+e n^2)-e n) atTop (𝓝 ‖z‖) := by
    have h := (((tendsto_const_nhds (x := ‖z‖^2)).add (he.pow 2)).sqrt.sub he)
    simpa only [zero_pow (by norm_num : 2≠0),add_zero,sub_zero,Real.sqrt_sq (norm_nonneg _)] using h
  exact Complex.continuous_ofReal.continuousAt.tendsto.comp h

end HilbertRegularization

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_TestVector
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
open ProbabilityTheory
namespace HardSphere
section

variable {N : ℕ} {L : Length} {a : ℝ} {I : Type*} [Fintype I]

lemma testVector_continuous (F : I → SmoothTest N L a) : Continuous (testVector F) :=
  continuous_of_continuous_lift (testVector_smooth F).continuous

lemma testVector_derivative (F : I → SmoothTest N L a) (X : Configuration N L) (p : Direction N) (i : I) :
    (fderiv ℝ (fun R : LiftedConfiguration N ↦ testVector F (project N L R)) (representative N L X)
      (Pi.single p.1 (Pi.single p.2 1))) i = coordDerivative N L (F i).toFun p X := by
  have hF := (testVector_smooth F).differentiable (by simp) (representative N L X)
  have hi := ((PiLp.hasFDerivAt_apply (𝕜 := ℝ) 2
    (testVector F (project N L (representative N L X))) i).comp (representative N L X) hF.hasFDerivAt).fderiv
  exact (congrArg (fun d ↦ d (Pi.single p.1 (Pi.single p.2 1))) hi).symm

lemma rmsTest_derivative_le (F : I → SmoothTest N L a) {ε : ℝ} (hε : 0<ε)
    (X : Configuration N L) (p : Direction N) :
    ‖coordDerivative N L (SmoothTest.rms F hε).toFun p X‖^2≤
      ∑ i : I, ‖coordDerivative N L (F i).toFun p X‖^2 := by
  have he : (fun R : LiftedConfiguration N ↦ (SmoothTest.rms F hε).toFun (project N L R))=
      HilbertRegularization.regularize ε ∘ (fun R ↦ testVector F (project N L R)) := rfl
  change ‖fderiv ℝ (fun R ↦ (SmoothTest.rms F hε).toFun (project N L R)) (representative N L X)
    (Pi.single p.1 (Pi.single p.2 1))‖^2≤_
  rw [he,fderiv_comp _ ((HilbertRegularization.smooth hε).differentiable (by simp)).differentiableAt
    ((testVector_smooth F).differentiable (by simp)).differentiableAt,
    HilbertRegularization.fderiv_eq hε,ContinuousLinearMap.comp_apply,project_representative]
  calc
    _ ≤ ‖fderiv ℝ (fun R ↦ testVector F (project N L R)) (representative N L X)
        (Pi.single p.1 (Pi.single p.2 1))‖^2 :=
      pow_le_pow_left₀ (norm_nonneg _) (HilbertRegularization.differential_apply_le ε _ _) 2
    _ = _ := by rw [EuclideanSpace.norm_sq_eq]; simp only [testVector_derivative]

end

variable {N : ℕ} {L : Length} {a : ℝ} {I : Type*} [Fintype I]

lemma rmsTest_energy_le (F : I → SmoothTest N L a) {ε : ℝ} (hε : 0<ε) :
    energy (SmoothTest.rms F hε).jet ≤ ∑ i,energy (F i).jet := by
  classical
  change (∑ p, ‖(SmoothTest.rms F hε).jet.2 p‖^2)≤∑ i,∑ p,‖(F i).jet.2 p‖^2
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro p _
  simp only [SmoothTest.jet,norm_sq_toLp_eq_integral]
  rw [← integral_finsetSum (f := fun i X ↦ ‖coordDerivative N L (F i).toFun p X‖^2) Finset.univ (fun i _ ↦ ((F i).continuous_partial p).norm.pow 2 |>.integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _))]
  apply integral_mono
  · exact ((SmoothTest.rms F hε).continuous_partial p).norm.pow 2 |>.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  · exact (continuous_finsetSum _ (fun i _ ↦ ((F i).continuous_partial p).norm.pow 2)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  · intro X
    exact rmsTest_derivative_le F hε X p

lemma rmsTest_norm_limit (F : I → SmoothTest N L a) {e : ℕ → ℝ}
    (he : ∀ k,0<e k) (he0 : Tendsto e atTop (𝓝 0)) :
    Tendsto (fun k ↦ ‖(SmoothTest.rms F (he k)).jet.1‖^2) atTop
      (𝓝 (∑ i,‖(F i).jet.1‖^2)) := by
  classical
  have hint : Integrable (fun X ↦ ‖testVector F X‖^2) (volume : Measure (Configuration N L)) :=
    ((testVector_continuous F).norm.pow 2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hlim := tendsto_integral_of_dominated_convergence (fun X ↦ ‖testVector F X‖^2)
    (fun k ↦ ((SmoothTest.rms F (he k)).continuous.norm.pow 2).aestronglyMeasurable)
    hint (fun k ↦ ae_of_all _ (fun X ↦ by
      rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
      exact pow_le_pow_left₀ (norm_nonneg _) (HilbertRegularization.norm_le (he k) (testVector F X)) 2))
    (ae_of_all _ (fun X ↦ (HilbertRegularization.tendsto_regularize (testVector F X) he0).norm.pow 2))
  have hI : (∫ X : Configuration N L, ‖(‖testVector F X‖ : ℂ)‖^2) =
      ∑ i,‖(F i).jet.1‖^2 := by
    simp only [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (norm_nonneg _)]
    simp only [EuclideanSpace.norm_sq_eq,testVector]
    rw [integral_finsetSum (f := fun i X ↦ ‖(F i).toFun X‖^2) Finset.univ (fun i _ ↦ ((F i).continuous.norm.pow 2).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _))]
    simp only [SmoothTest.jet,norm_sq_toLp_eq_integral]
  rw [hI] at hlim
  simp only [SmoothTest.jet,norm_sq_toLp_eq_integral,SmoothTest.rms,rmsTestFun] at hlim ⊢
  exact hlim
end HardSphere

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_FormDomain_RmsPermuteFunBosonic
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
open ProbabilityTheory
namespace HardSphere
variable {N : ℕ} {L : Length} {a : ℝ}

lemma rmsPermute_fun_bosonic (f : SmoothTest N L a) (ε : ℝ) (τ : Equiv.Perm (Fin N))
    (X : Configuration N L) :
    rmsTestFun (fun σ ↦ f.permute σ) ε (permuteConfiguration τ X)=
      rmsTestFun (fun σ ↦ f.permute σ) ε X := by
  unfold rmsTestFun HilbertRegularization.regularize
  have hsum : ‖testVector (fun σ ↦ f.permute σ) (permuteConfiguration τ X)‖^2=
      ‖testVector (fun σ ↦ f.permute σ) X‖^2 := by
    simp only [EuclideanSpace.norm_sq_eq,testVector,SmoothTest.permute,Function.comp_apply]
    exact Equiv.sum_comp (Equiv.mulLeft τ) (fun σ ↦ ‖f.toFun (permuteConfiguration σ X)‖^2)
  rw [hsum]

lemma rmsPermute_bosonic (f : SmoothTest N L a) {ε : ℝ} (hε : 0<ε) :
    bosonic (SmoothTest.rms (fun σ ↦ f.permute σ) hε).jet.1 := by
  intro τ
  let g := SmoothTest.rms (fun σ ↦ f.permute σ) hε
  have hg : (g.jet.1 : Configuration N L → ℂ)=ᵐ[volume] g.toFun := g.memLp.coeFn_toLp
  have hgt := (measurePreserving_permute τ).quasiMeasurePreserving.ae_eq_comp hg
  filter_upwards [hgt,hg] with X hX hY
  exact hX.trans ((rmsPermute_fun_bosonic f ε τ X).trans hY.symm)

lemma IsGroundVector.rayleigh_smooth_all {u : Jet N L} (hu : IsGroundVector N L a u)
    (f : SmoothTest N L a) : energy u*‖f.jet.1‖^2≤energy f.jet := by
  classical
  let e : ℕ → ℝ := fun k ↦ 1/((k:ℝ)+1)
  have he (k) : 0<e k := by dsimp [e]; positivity
  have he0 : Tendsto e atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hle (k : ℕ) : energy u*‖(SmoothTest.rms (fun σ ↦ f.permute σ) (he k)).jet.1‖^2≤
      ∑ σ : Equiv.Perm (Fin N), energy (f.permute σ).jet :=
    (hu.rayleigh _ (subset_closure (Set.mem_range_self _)) (rmsPermute_bosonic f (he k))).trans
      (rmsTest_energy_le _ (he k))
  have hl := le_of_tendsto ((rmsTest_norm_limit (fun σ ↦ f.permute σ) he he0).const_mul (energy u))
    (Eventually.of_forall hle)
  have hn (σ : Equiv.Perm (Fin N)) : ‖(f.permute σ).jet.1‖=‖f.jet.1‖ := by
    rw [f.jet_permute]
    exact Lp.norm_compMeasurePreserving _ _
  simp only [hn] at hl
  simp only [SmoothTest.jet_permute,energy_permutationJet,Finset.sum_const,Finset.card_univ,nsmul_eq_mul] at hl
  have hc : 0<(Fintype.card (Equiv.Perm (Fin N)) : ℝ) := by exact_mod_cast Fintype.card_pos
  nlinarith

lemma IsGroundVector.rayleigh_all {u : Jet N L} (hu : IsGroundVector N L a u)
    (v : Jet N L) (hv : v∈dirichletDomain N L a) : energy u*‖v.1‖^2≤energy v := by
  have hc : IsClosed {w : Jet N L | energy u*‖w.1‖^2≤energy w} := by
    apply isClosed_le (continuous_const.mul (continuous_fst.norm.pow 2))
    exact continuous_finsetSum _ (fun p _ ↦ ((continuous_apply p).comp continuous_snd).norm.pow 2)
  apply closure_minimal ?_ hc hv
  rintro _ ⟨f,rfl⟩
  exact hu.rayleigh_smooth_all f
end HardSphere

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Collisions_IteratedInsertion
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

lemma iterated_insertion (C : ℝ) (_hC : 0<C)
    (hins : ∀ (n : ℕ) (L : Length) (r : ℝ), 0 < r →
      (n:ℝ)*(2*Real.pi*r)^3≤L.val^3/2 →
      ∀ u : Jet n L, u∈dirichletDomain n L r →
      ∃ v : Jet (n+1) L, v∈dirichletDomain (n+1) L r ∧
        ‖v.1‖=‖u.1‖ ∧ energy v≤energy u+(C*(n:ℝ)*r/L.val^3)*‖u.1‖^2)
    (n m : ℕ) (L : Length) {r : ℝ} (hr : 0 < r)
    (hs : ((n+m:ℕ):ℝ)*(2*Real.pi*r)^3≤L.val^3/2)
    (u : Jet n L) (hu : u∈dirichletDomain n L r) :
    ∃ v : Jet (n+m) L, v∈dirichletDomain (n+m) L r ∧ ‖v.1‖=‖u.1‖ ∧
      energy v≤energy u+(∑ j∈Finset.range m,C*((n+j:ℕ):ℝ)*r/L.val^3)*‖u.1‖^2 := by
  induction m with
  | zero => exact ⟨u,hu,rfl,by simp⟩
  | succ m ih =>
    have hs' : ((n+m:ℕ):ℝ)*(2*Real.pi*r)^3≤L.val^3/2 := by
      exact (mul_le_mul_of_nonneg_right
        (show ((n+m:ℕ):ℝ)≤((n+(m+1):ℕ):ℝ) by exact_mod_cast Nat.le_succ (n+m))
        (by positivity)).trans hs
    obtain ⟨v,hv,hn,he⟩ := ih hs'
    obtain ⟨w,hw,hnw,hew⟩ := hins (n+m) L r hr hs' v hv
    refine ⟨w,hw,hnw.trans hn,?_⟩
    rw [hn] at hew
    rw [Finset.sum_range_succ]
    nlinarith

lemma ground_energy_removal : ∃ C : ℝ, 0<C ∧
    ∀ (n m : ℕ) (L : Length) (r : ℝ), 0 < r →
    ((n+m:ℕ):ℝ)*(2*Real.pi*r)^3≤L.val^3/2 →
    ∀ u : Jet (n+m) L, IsGroundVector (n+m) L r u →
    ∀ v : Jet n L, v∈dirichletDomain n L r →
      (energy u-C*(m:ℝ)*((n+m:ℕ):ℝ)*r/L.val^3)*‖v.1‖^2≤energy v := by
  obtain ⟨C,hC,hins⟩ := uniform_insertion
  refine ⟨C,hC,fun n m L r hr hs u hu v hv ↦ ?_⟩
  have hL : 0<L.val := L.property
  obtain ⟨w,hw,hn,he⟩ := iterated_insertion C hC hins n m L hr hs v hv
  have hmin := hu.rayleigh_all w hw
  rw [hn] at hmin
  have hsum : (∑ j∈Finset.range m,C*((n+j:ℕ):ℝ)*r/L.val^3)≤
      C*(m:ℝ)*((n+m:ℕ):ℝ)*r/L.val^3 := by
    calc
      _ ≤ ∑ _j∈Finset.range m,C*((n+m:ℕ):ℝ)*r/L.val^3 := by
        apply Finset.sum_le_sum
        intro j hj
        apply div_le_div_of_nonneg_right _ (by positivity)
        apply mul_le_mul_of_nonneg_right _ hr.le
        apply mul_le_mul_of_nonneg_left _ hC.le
        exact_mod_cast Nat.add_le_add_left (Nat.le_of_lt (Finset.mem_range.mp hj)) n
      _ = _ := by simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul]; ring
  have := mul_le_mul_of_nonneg_right hsum (sq_nonneg ‖v.1‖)
  nlinarith
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

end HardSphere

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Cutoffs_Regularize
attribute [-instance] _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Rescaling.config_haar _root_.OAI.HardSphere.bridgeEndpointBase_finite _root_.OAI.HardSphere.configurationBorel _root_.OAI.HardSphere.configurationPathBorel _root_.OAI.HardSphere.configurationPathMeasurable _root_.OAI.HardSphere.endpointWeightedBase_sfinite _root_.OAI.HardSphere.freePathLaw_finite_deletion _root_.OAI.HardSphere.hilbertDomain_closed _root_.OAI.HardSphere.hilbertDomain_complete _root_.OAI.HardSphere.killedPathLaw_finite_deletion
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
open ComplexRegularization

lemma coe_modulusScalar {N : ℕ} {L : Length} (u : ScalarL2 N L) :
    modulusScalar u =ᵐ[volume] fun X ↦ (‖u X‖ : ℂ) :=
  modulus_lipschitz.coeFn_compLp (by simp) u

lemma norm_modulusScalar {N : ℕ} {L : Length} (u : ScalarL2 N L) :
    ‖modulusScalar u‖ = ‖u‖ := by
  have he : ∀ᵐ X ∂volume, ‖modulusScalar u X‖ = ‖u X‖ := by
    filter_upwards [coe_modulusScalar u] with X hX
    simp [hX]
  exact le_antisymm (Lp.norm_le_norm_of_ae_le (he.mono fun _ hx ↦ hx.le))
    (Lp.norm_le_norm_of_ae_le (he.mono fun _ hx ↦ hx.ge))

end HardSphere

end
end
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

end HardSphere

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Operators_FormResolventNormEnergy
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
open ContinuousLinearMap

lemma bath_heat_bound : ∃ C : ℝ, 0<C ∧
    ∀ (n m : ℕ) (L : Length) (r t : ℝ), 0 < r → 0<t →
    ((n+m:ℕ):ℝ)*(2*Real.pi*r)^3≤L.val^3/2 →
    ∀ u : Jet (n+m) L, IsGroundVector (n+m) L r u →
      ‖killedTransition n L r t‖≤
        Real.exp (-t*(energy u-C*(m:ℝ)*((n+m:ℕ):ℝ)*r/L.val^3)) := by
  obtain ⟨C,hC,hrem⟩ := ground_energy_removal
  exact ⟨C,hC,fun n m L r t hr ht hs u hu ↦
    killedTransition_norm_le_of_energy ht (hrem n m L r hr hs u hu)⟩
end HardSphere

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

lemma groundPathWeight_measurable (u : Jet N L) (t : ℝ) : Measurable (groundPathWeight u t) := by
  exact measurable_const.mul (((Lp.stronglyMeasurable u.1).measurable.comp
    (continuous_eval_const (0:Time)).measurable).norm.mul
    (((Lp.stronglyMeasurable u.1).measurable.comp (continuous_eval_const (1:Time)).measurable).norm))

end
end HardSphere

end
end
end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_JoinConfiguration
attribute [-instance] _root_.OAI.HardSphere.Bridge.exposedBridgeKernel_markov _root_.OAI.HardSphere.Bridge.exposedPeriodSingle_finite _root_.OAI.HardSphere.Bridge.exposedTrialKernel_markov _root_.OAI.HardSphere.Bridge.instBorelSpaceContinuousMapElemRealTimePoint _root_.OAI.HardSphere.Bridge.instIsProbabilityMeasureNoiseLaw _root_.OAI.HardSphere.Bridge.instMeasurableSpaceContinuousMapElemRealTimePoint _root_.OAI.HardSphere.Bridge.parameterBridgeKernel_markov _root_.OAI.HardSphere.Bridge.parameterIndividualReference_finite _root_.OAI.HardSphere.Bridge.parameterTrialKernel_markov _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Bridge.trialKernel_markov _root_.OAI.HardSphere.Groups.cellPathReference_probability _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Rescaling.config_haar _root_.OAI.HardSphere.Wiener.instIsProbabilityMeasureContinuousMapElemRealTimeBridgeLaw _root_.OAI.HardSphere.bridgeEndpointBase_finite _root_.OAI.HardSphere.coordinateBridge_probability _root_.OAI.HardSphere.endpointWeightedBase_sfinite _root_.OAI.HardSphere.freePathLaw_finite_deletion _root_.OAI.HardSphere.gaussianCoordinates_probability _root_.OAI.HardSphere.killedPathLaw_finite_deletion
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
noncomputable section

lemma splitConfiguration_continuous (m n : ℕ) (L : Length) :
    Continuous (splitConfiguration m n L) := by unfold splitConfiguration; fun_prop

lemma joinConfiguration_preserving (m n : ℕ) (L : Length) :
    MeasurePreserving (joinConfiguration m n L)
      ((volume : Measure (Configuration m L)).prod volume) volume := by
  have h := (volume_measurePreserving_piCongrLeft (fun _ : Fin (m+n) ↦ Torus L)
    (finSumFinEquiv (m:=m) (n:=n))).comp
    (volume_measurePreserving_sumPiEquivProdPi_symm (fun _ : Fin m ⊕ Fin n ↦ Torus L))
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  try rfl
  funext p i
  induction i using Fin.addCases <;> simp [joinConfiguration,MeasurableEquiv.coe_piCongrLeft,
    MeasurableEquiv.coe_sumPiEquivProdPi_symm,Equiv.piCongrLeft_apply,Equiv.sumPiEquivProdPi_symm_apply]

lemma joinConfigurationPath_continuous (m n : ℕ) (L : Length) :
    Continuous (joinConfigurationPath m n L) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  exact (joinConfiguration_continuous m n L).comp
    ((continuous_fst.fst.eval continuous_snd).prodMk
      (continuous_fst.snd.eval continuous_snd))

lemma splitConfigurationPath_continuous (m n : ℕ) (L : Length) :
    Continuous (splitConfigurationPath m n L) := by
  apply Continuous.prodMk
  all_goals
    apply ContinuousMap.continuous_of_continuous_uncurry
    apply continuous_pi
    intro i
    change Continuous (fun p : ConfigurationPath (m+n) L × Time ↦ p.1 p.2 _)
    exact (continuous_apply _).comp (continuous_fst.eval continuous_snd)

lemma measurePreserving_shuffle {A B C D : Type*} [MeasurableSpace A] [MeasurableSpace B]
    [MeasurableSpace C] [MeasurableSpace D] (μ : Measure A) (ν : Measure B)
    (ξ : Measure C) (ζ : Measure D) [SFinite μ] [SFinite ν] [SFinite ξ] [SFinite ζ] :
    MeasurePreserving (fun p : (A×B)×(C×D) ↦ ((p.1.1,p.2.1),(p.1.2,p.2.2)))
      ((μ.prod ν).prod (ξ.prod ζ)) ((μ.prod ξ).prod (ν.prod ζ)) := by
  have h1 := measurePreserving_prodAssoc μ ν (ξ.prod ζ)
  have h2 := (MeasurePreserving.id μ).prod (measurePreserving_prodAssoc ν ξ ζ).symm
  have h3 := (MeasurePreserving.id μ).prod
    ((Measure.measurePreserving_swap (μ:=ν) (ν:=ξ)).prod (MeasurePreserving.id ζ))
  have h4 := (MeasurePreserving.id μ).prod (measurePreserving_prodAssoc ξ ν ζ)
  have h5 := (measurePreserving_prodAssoc μ ξ (ν.prod ζ)).symm
  exact h5.comp (h4.comp (h3.comp (h2.comp h1)))

lemma joinCoordinatePaths_preserving (m n : ℕ) :
    MeasurePreserving (joinCoordinatePaths m n)
      ((coordinateWiener m).prod (coordinateWiener n)) (coordinateWiener (m+n)) := by
  convert (measurePreserving_piCongrLeft (fun _ : Direction (m+n) ↦ wiener)
    (directionSumEquiv m n)).comp
    (measurePreserving_sumPiEquivProdPi_symm (fun _ : Direction m ⊕ Direction n ↦ wiener)) using 1 <;> try rfl
  funext p d
  simp [joinCoordinatePaths,MeasurableEquiv.coe_piCongrLeft,
    MeasurableEquiv.coe_sumPiEquivProdPi_symm,Equiv.piCongrLeft_apply,Equiv.sumPiEquivProdPi_symm_apply]
  cases (directionSumEquiv m n).symm d <;> rfl

lemma freeTrajectory_join (m n : ℕ) (L : Length) (t : ℝ)
    (w : CoordinatePaths m × CoordinatePaths n) (X : Configuration m L × Configuration n L) :
    freeTrajectory (m+n) L t (joinCoordinatePaths m n w) (joinConfiguration m n L X)=
      joinConfigurationPath m n L (freeTrajectory m L t w.1 X.1,freeTrajectory n L t w.2 X.2) := by
  ext s i j
  induction i using Fin.addCases <;>
    simp [freeTrajectory,joinConfigurationPath,joinConfiguration,joinCoordinatePaths,directionSumEquiv]

lemma joinConfigurationPath_preserving (m n : ℕ) (L : Length) (t : ℝ) :
    MeasurePreserving (joinConfigurationPath m n L)
      ((freePathLaw m L t).prod (freePathLaw n L t)) (freePathLaw (m+n) L t) := by
  refine ⟨(joinConfigurationPath_continuous m n L).measurable,?_⟩
  have hj := ((joinCoordinatePaths_preserving m n).prod (joinConfiguration_preserving m n L)).comp
    (measurePreserving_shuffle (coordinateWiener m) (volume : Measure (Configuration m L))
      (coordinateWiener n) (volume : Measure (Configuration n L)))
  simp only [freePathLaw,Measure.map_prod_map _ _ (freeTrajectory_continuous m L t).measurable
    (freeTrajectory_continuous n L t).measurable]
  rw [Measure.map_map (joinConfigurationPath_continuous m n L).measurable
    ((freeTrajectory_continuous m L t).measurable.prodMap (freeTrajectory_continuous n L t).measurable)]
  rw [← hj.map_eq,Measure.map_map (freeTrajectory_continuous (m+n) L t).measurable hj.measurable]
  congr 1
  funext p
  exact (freeTrajectory_join m n L t (p.1.1,p.2.1) (p.1.2,p.2.2)).symm

lemma staysAllowed_join_subset_bath (m n : ℕ) (L : Length) (a : ℝ) :
    joinConfigurationPath m n L ⁻¹' staysAllowed (m+n) L a ⊆
      Prod.snd ⁻¹' staysAllowed n L a := by
  rintro ⟨ω,η⟩ h x ⟨s,rfl⟩ i j hij
  have hh := h ⟨s,rfl⟩ (Fin.natAdd m i) (Fin.natAdd m j) (by simpa using hij)
  simpa [joinConfigurationPath,joinConfiguration] using hh
end
end HardSphere

end
end
end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_SliceNormSq
attribute [-instance] _root_.OAI.HardSphere.Bridge.exposedBridgeKernel_markov _root_.OAI.HardSphere.Bridge.exposedPeriodSingle_finite _root_.OAI.HardSphere.Bridge.exposedTrialKernel_markov _root_.OAI.HardSphere.Bridge.instBorelSpaceContinuousMapElemRealTimePoint _root_.OAI.HardSphere.Bridge.instIsProbabilityMeasureNoiseLaw _root_.OAI.HardSphere.Bridge.instMeasurableSpaceContinuousMapElemRealTimePoint _root_.OAI.HardSphere.Bridge.parameterBridgeKernel_markov _root_.OAI.HardSphere.Bridge.parameterIndividualReference_finite _root_.OAI.HardSphere.Bridge.parameterTrialKernel_markov _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Bridge.trialKernel_markov _root_.OAI.HardSphere.Groups.cellPathReference_probability _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Rescaling.config_haar _root_.OAI.HardSphere.bridgeEndpointBase_finite _root_.OAI.HardSphere.coordinateBridge_probability _root_.OAI.HardSphere.endpointWeightedBase_sfinite _root_.OAI.HardSphere.freePathLaw_finite_deletion _root_.OAI.HardSphere.killedPathLaw_finite_deletion
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
noncomputable section

lemma killed_endpoint_quadratic {N : ℕ} {L : Length} (a t : ℝ) (f g : ScalarL2 N L) :
    (∫ ω : ConfigurationPath N L, ‖f (ω 0)‖*‖g (ω 1)‖ ∂killedPathLaw N L a t) ≤
      (‖killedTransition N L a t‖/2)*(‖f‖^2+‖g‖^2) := by
  have h := re_inner_le_norm (𝕜:=ℂ) (modulusScalar f) (killedTransition N L a t (modulusScalar g))
  change (inner ℂ (modulusScalar f) (killedTransition N L a t (modulusScalar g))).re ≤ _ at h
  rw [modulus_killed_pairing,Complex.ofReal_re,norm_modulusScalar] at h
  have hh := (killedTransition N L a t).le_opNorm (modulusScalar g)
  rw [norm_modulusScalar] at hh
  have hmul := mul_le_mul_of_nonneg_left hh (norm_nonneg f)
  have hAM := mul_nonneg (norm_nonneg (killedTransition N L a t)) (sq_nonneg (‖f‖-‖g‖))
  nlinarith

lemma killed_endpoint_quadratic_function {N : ℕ} {L : Length} (a t : ℝ)
    {f g : Configuration N L → ℂ} (hf : MemLp f 2 volume) (hg : MemLp g 2 volume) :
    (∫⁻ ω : ConfigurationPath N L, ENNReal.ofReal (‖f (ω 0)‖*‖g (ω 1)‖)
      ∂killedPathLaw N L a t) ≤
      ENNReal.ofReal (‖killedTransition N L a t‖/2)*
        (ENNReal.ofReal (∫ x, ‖f x‖^2 ∂volume)+ENNReal.ofReal (∫ x, ‖g x‖^2 ∂volume)) := by
  let F := hf.toLp f
  let G := hg.toLp g
  have heq : (fun ω : ConfigurationPath N L ↦ ‖F (ω 0)‖*‖G (ω 1)‖) =ᵐ[killedPathLaw N L a t]
      (fun ω ↦ ‖f (ω 0)‖*‖g (ω 1)‖) := by
    filter_upwards [((freePathLaw_marginal N L t 0).quasiMeasurePreserving.ae_eq_comp
        (MemLp.coeFn_toLp hf)).filter_mono (ae_mono Measure.restrict_le_self),
      ((freePathLaw_marginal N L t 1).quasiMeasurePreserving.ae_eq_comp
        (MemLp.coeFn_toLp hg)).filter_mono (ae_mono Measure.restrict_le_self)] with ω hF hG
    simp only [Function.comp_def] at hF hG
    rw [show F (ω 0)=f (ω 0) from hF,show G (ω 1)=g (ω 1) from hG]
  have hnf : ‖F‖^2=∫ x, ‖f x‖^2 ∂volume := by
    rw [IndicatorStrong.norm_sq_integral]
    exact integral_congr_ae ((MemLp.coeFn_toLp hf).fun_comp (fun z : ℂ ↦ ‖z‖^2))
  have hng : ‖G‖^2=∫ x, ‖g x‖^2 ∂volume := by
    rw [IndicatorStrong.norm_sq_integral]
    exact integral_congr_ae ((MemLp.coeFn_toLp hg).fun_comp (fun z : ℂ ↦ ‖z‖^2))
  have heql := lintegral_congr_ae (heq.fun_comp ENNReal.ofReal)
  simp only [Function.comp_def] at heql
  rw [← heql,
    ← ofReal_integral_eq_lintegral_ofReal (integrable_norm_endpoints N L a t F G 0 1)
      (Eventually.of_forall fun _ ↦ mul_nonneg (norm_nonneg _) (norm_nonneg _)),
    ← hnf,← hng,← ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _),
    ← ENNReal.ofReal_mul (div_nonneg (norm_nonneg _) (by norm_num))]
  exact ENNReal.ofReal_le_ofReal (killed_endpoint_quadratic a t F G)

lemma sliceNormSq_measurable {m n : ℕ} {L : Length} (u : ScalarL2 (m+n) L) :
    Measurable (sliceNormSq u) := by
  have h : StronglyMeasurable (fun p : Configuration m L × Configuration n L ↦
      ‖u (joinConfiguration m n L p)‖^2) :=
    (((Lp.stronglyMeasurable u).comp_measurable (joinConfiguration_continuous m n L).measurable).norm).pow 2
  exact h.integral_prod_right'.measurable

lemma memLp_slice_ae {m n : ℕ} {L : Length} (u : ScalarL2 (m+n) L) :
    ∀ᵐ y : Configuration m L ∂volume,
      MemLp (fun x : Configuration n L ↦ u (joinConfiguration m n L (y,x))) 2 volume := by
  have h := ((Lp.memLp u).comp_measurePreserving (joinConfiguration_preserving m n L)).integrable_norm_pow
    (show (2:ℕ)≠0 by norm_num)
  filter_upwards [h.prod_right_ae] with y hy
  apply (memLp_two_iff_integrable_sq_norm _).mpr hy
  exact (Lp.stronglyMeasurable u).comp_measurable
    ((joinConfiguration_continuous m n L).measurable.comp measurable_prodMk_left) |>.aestronglyMeasurable

lemma bath_slice_quadratic_ae {m n : ℕ} {L : Length} (u : ScalarL2 (m+n) L) (a t : ℝ) :
    ∀ᵐ ω : ConfigurationPath m L ∂freePathLaw m L t,
      (∫⁻ η : ConfigurationPath n L,
        ENNReal.ofReal (‖u (joinConfiguration m n L (ω 0,η 0))‖*
          ‖u (joinConfiguration m n L (ω 1,η 1))‖) ∂killedPathLaw n L a t) ≤
        ENNReal.ofReal (‖killedTransition n L a t‖/2)*
          (ENNReal.ofReal (sliceNormSq u (ω 0))+ENNReal.ofReal (sliceNormSq u (ω 1))) := by
  filter_upwards [(freePathLaw_marginal m L t 0).quasiMeasurePreserving.ae (memLp_slice_ae u),
    (freePathLaw_marginal m L t 1).quasiMeasurePreserving.ae (memLp_slice_ae u)] with ω h0 h1
  exact killed_endpoint_quadratic_function a t h0 h1
end
end HardSphere

end
end
end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Orbitals_FreePathLawFiniteDeletion
attribute [-instance] _root_.OAI.HardSphere.Bridge.exposedBridgeKernel_markov _root_.OAI.HardSphere.Bridge.exposedPeriodSingle_finite _root_.OAI.HardSphere.Bridge.exposedTrialKernel_markov _root_.OAI.HardSphere.Bridge.instBorelSpaceContinuousMapElemRealTimePoint _root_.OAI.HardSphere.Bridge.instIsProbabilityMeasureNoiseLaw _root_.OAI.HardSphere.Bridge.instMeasurableSpaceContinuousMapElemRealTimePoint _root_.OAI.HardSphere.Bridge.parameterBridgeKernel_markov _root_.OAI.HardSphere.Bridge.parameterIndividualReference_finite _root_.OAI.HardSphere.Bridge.parameterTrialKernel_markov _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Bridge.trialKernel_markov _root_.OAI.HardSphere.Groups.cellPathReference_probability _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Rescaling.config_haar _root_.OAI.HardSphere.bridgeEndpointBase_finite _root_.OAI.HardSphere.coordinateBridge_probability _root_.OAI.HardSphere.endpointWeightedBase_sfinite
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
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal BigOperators
namespace HardSphere
open MeasureTheory Wiener Set Filter
noncomputable section

lemma selected_reversal_integral {m n : ℕ} {L : Length} (u : ScalarL2 (m+n) L) (t : ℝ)
    {h : ConfigurationPath m L → ℝ≥0∞} (hh : Measurable h)
    (hrev : ∀ ω, h (reverseConfigurationPath m L ω)=h ω) :
    (∫⁻ ω : ConfigurationPath m L, h ω*ENNReal.ofReal (sliceNormSq u (ω 1)) ∂freePathLaw m L t)=
      ∫⁻ ω : ConfigurationPath m L, h ω*ENNReal.ofReal (sliceNormSq u (ω 0)) ∂freePathLaw m L t := by
  have hmeas : Measurable (fun ω : ConfigurationPath m L ↦ h ω*ENNReal.ofReal (sliceNormSq u (ω 0))) :=
    hh.mul (((sliceNormSq_measurable u).comp (continuous_eval_const (0:Time)).measurable).ennreal_ofReal)
  simpa only [reverseConfigurationPath_apply,reverseTime_zero,hrev] using
    (reverse_freePath_preserving m L t).lintegral_comp hmeas

lemma deleted_path_integral_le {m n : ℕ} {L : Length} (u : ScalarL2 (m+n) L) (a t : ℝ)
    {h : ConfigurationPath m L → ℝ≥0∞} (hh : Measurable h)
    (hrev : ∀ ω, h (reverseConfigurationPath m L ω)=h ω) :
    (∫⁻ ω : ConfigurationPath (m+n) L,
      h (splitConfigurationPath m n L ω).1*ENNReal.ofReal (‖u (ω 0)‖*‖u (ω 1)‖)
      ∂killedPathLaw (m+n) L a t) ≤
      ENNReal.ofReal ‖killedTransition n L a t‖*
        ∫⁻ ω : ConfigurationPath m L, h ω*ENNReal.ofReal (sliceNormSq u (ω 0)) ∂freePathLaw m L t := by
  let F : ConfigurationPath (m+n) L → ℝ≥0∞ := fun ω ↦
    h (splitConfigurationPath m n L ω).1*ENNReal.ofReal (‖u (ω 0)‖*‖u (ω 1)‖)
  let G : ConfigurationPath m L × ConfigurationPath n L → ℝ≥0∞ := fun p ↦
    h p.1*ENNReal.ofReal (‖u (joinConfiguration m n L (p.1 0,p.2 0))‖*
      ‖u (joinConfiguration m n L (p.1 1,p.2 1))‖)
  have hu := (Lp.stronglyMeasurable u).measurable
  have hF : Measurable F := by
    exact (hh.comp ((splitConfigurationPath_continuous m n L).measurable.fst)).mul
      (((hu.comp (continuous_eval_const (0:Time)).measurable).norm.mul
        (hu.comp (continuous_eval_const (1:Time)).measurable).norm).ennreal_ofReal)
  have hG : Measurable G := by
    simpa only [F,G,Function.comp_def,split_joinConfigurationPath,joinConfigurationPath_apply]
      using hF.comp (joinConfigurationPath_continuous m n L).measurable
  have hS0 : Measurable (fun ω : ConfigurationPath m L ↦ h ω*ENNReal.ofReal (sliceNormSq u (ω 0))) :=
    hh.mul (((sliceNormSq_measurable u).comp (continuous_eval_const (0:Time)).measurable).ennreal_ofReal)
  have hS1 : Measurable (fun ω : ConfigurationPath m L ↦ h ω*ENNReal.ofReal (sliceNormSq u (ω 1))) :=
    hh.mul (((sliceNormSq_measurable u).comp (continuous_eval_const (1:Time)).measurable).ennreal_ofReal)
  have hj := (joinConfigurationPath_preserving m n L t).restrict_preimage
    (staysAllowed_open (m+n) L a).measurableSet
  have hd : ((freePathLaw m L t).prod (freePathLaw n L t)).restrict
      (joinConfigurationPath m n L ⁻¹' staysAllowed (m+n) L a) ≤
      (freePathLaw m L t).prod (killedPathLaw n L a t) := by
    calc
      _ ≤ ((freePathLaw m L t).prod (freePathLaw n L t)).restrict
          (Set.univ ×ˢ staysAllowed n L a) :=
        Measure.restrict_mono_set _ fun p hp ↦
          ⟨mem_univ _,staysAllowed_join_subset_bath m n L a hp⟩
      _ = _ := by rw [← Measure.prod_restrict,Measure.restrict_univ]; rfl
  have hq := bath_slice_quadratic_ae u a t
  calc
    _ = ∫⁻ p, G p ∂((freePathLaw m L t).prod (freePathLaw n L t)).restrict
        (joinConfigurationPath m n L ⁻¹' staysAllowed (m+n) L a) := by
      symm
      simpa only [F,G,killedPathLaw,split_joinConfigurationPath,joinConfigurationPath_apply] using
        hj.lintegral_comp hF
    _ ≤ ∫⁻ p, G p ∂((freePathLaw m L t).prod (killedPathLaw n L a t)) :=
      lintegral_mono' hd le_rfl
    _ = ∫⁻ ω : ConfigurationPath m L, h ω*(∫⁻ η : ConfigurationPath n L,
        ENNReal.ofReal (‖u (joinConfiguration m n L (ω 0,η 0))‖*
          ‖u (joinConfiguration m n L (ω 1,η 1))‖) ∂killedPathLaw n L a t) ∂freePathLaw m L t := by
      rw [lintegral_prod _ hG.aemeasurable]
      apply lintegral_congr
      intro ω
      dsimp only [G]
      exact lintegral_const_mul _ (by
        apply Measurable.ennreal_ofReal
        apply Measurable.mul
        all_goals
          apply Measurable.norm
          apply hu.comp
          exact (joinConfiguration_continuous m n L).measurable.comp
            (measurable_const.prodMk (continuous_eval_const _).measurable))
    _ ≤ ∫⁻ ω : ConfigurationPath m L, h ω*(ENNReal.ofReal (‖killedTransition n L a t‖/2)*
        (ENNReal.ofReal (sliceNormSq u (ω 0))+ENNReal.ofReal (sliceNormSq u (ω 1)))) ∂freePathLaw m L t := by
      apply lintegral_mono_ae
      filter_upwards [hq] with ω hω
      exact mul_le_mul_right hω _
    _ = ENNReal.ofReal (‖killedTransition n L a t‖/2)*
        ((∫⁻ ω : ConfigurationPath m L, h ω*ENNReal.ofReal (sliceNormSq u (ω 0)) ∂freePathLaw m L t)+
         (∫⁻ ω : ConfigurationPath m L, h ω*ENNReal.ofReal (sliceNormSq u (ω 1)) ∂freePathLaw m L t)) := by
      calc
        _ = ∫⁻ ω : ConfigurationPath m L, ENNReal.ofReal (‖killedTransition n L a t‖/2)*
            (h ω*ENNReal.ofReal (sliceNormSq u (ω 0))+h ω*ENNReal.ofReal (sliceNormSq u (ω 1)))
            ∂freePathLaw m L t := by
          apply lintegral_congr
          intro ω
          rw [← mul_add,mul_left_comm]
        _ = _ := by
          calc
            _ = ENNReal.ofReal (‖killedTransition n L a t‖/2)*
                (∫⁻ ω : ConfigurationPath m L,
                  h ω*ENNReal.ofReal (sliceNormSq u (ω 0))+
                    h ω*ENNReal.ofReal (sliceNormSq u (ω 1)) ∂freePathLaw m L t) :=
              lintegral_const_mul _ (hS0.add hS1)
            _ = _ := by rw [lintegral_add_left hS0]
    _ = _ := by
      rw [selected_reversal_integral u t hh hrev,mul_add,← add_mul,
        ← ENNReal.ofReal_add (div_nonneg (norm_nonneg _) (by norm_num))
          (div_nonneg (norm_nonneg _) (by norm_num)),add_halves]
end
end HardSphere

end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_FreePathExpectation
attribute [-instance] _root_.OAI.HardSphere.Bridge.exposedBridgeKernel_markov _root_.OAI.HardSphere.Bridge.exposedPeriodSingle_finite _root_.OAI.HardSphere.Bridge.exposedTrialKernel_markov _root_.OAI.HardSphere.Bridge.instBorelSpaceContinuousMapElemRealTimePoint _root_.OAI.HardSphere.Bridge.instIsProbabilityMeasureNoiseLaw _root_.OAI.HardSphere.Bridge.instMeasurableSpaceContinuousMapElemRealTimePoint _root_.OAI.HardSphere.Bridge.parameterBridgeKernel_markov _root_.OAI.HardSphere.Bridge.parameterIndividualReference_finite _root_.OAI.HardSphere.Bridge.parameterTrialKernel_markov _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Bridge.trialKernel_markov _root_.OAI.HardSphere.Groups.cellPathReference_probability _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Rescaling.config_haar _root_.OAI.HardSphere.bridgeEndpointBase_finite _root_.OAI.HardSphere.coordinateBridge_probability _root_.OAI.HardSphere.endpointWeightedBase_sfinite _root_.OAI.HardSphere.gaussianCoordinates_probability
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
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal BigOperators
namespace HardSphere
open MeasureTheory Wiener Set Filter
noncomputable section

lemma freePathExpectation_measurable {m : ℕ} {L : Length} (t : ℝ)
    {h : ConfigurationPath m L → ℝ≥0∞} (hh : Measurable h) :
    Measurable (freePathExpectation t h) :=
  (hh.comp (freeTrajectory_continuous m L t).measurable).lintegral_prod_left'

lemma selected_start_integral {m n : ℕ} {L : Length} (u : ScalarL2 (m+n) L) (t : ℝ)
    {h : ConfigurationPath m L → ℝ≥0∞} (hh : Measurable h) :
    (∫⁻ ω : ConfigurationPath m L, h ω*ENNReal.ofReal (sliceNormSq u (ω 0)) ∂freePathLaw m L t)=
      ∫⁻ y : Configuration m L, freePathExpectation t h y*ENNReal.ofReal (sliceNormSq u y) ∂volume := by
  have hmeas : Measurable (fun ω : ConfigurationPath m L ↦
      h ω*ENNReal.ofReal (sliceNormSq u (ω 0))) := hh.mul (((sliceNormSq_measurable u).comp
    (continuous_eval_const (0:Time)).measurable).ennreal_ofReal)
  rw [freePathLaw,lintegral_map hmeas (freeTrajectory_continuous m L t).measurable]
  have heq : (fun p : CoordinatePaths m × Configuration m L ↦
      h (freeTrajectory m L t p.1 p.2)*ENNReal.ofReal (sliceNormSq u (freeTrajectory m L t p.1 p.2 0)))
      =ᵐ[(coordinateWiener m).prod volume] (fun p ↦
      h (freeTrajectory m L t p.1 p.2)*ENNReal.ofReal (sliceNormSq u p.2)) := by
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae (freeTrajectory_initial_ae m L t)] with p hp
    rw [hp p.2]
  have hp : Measurable (fun p : CoordinatePaths m × Configuration m L ↦
      h (freeTrajectory m L t p.1 p.2)*ENNReal.ofReal (sliceNormSq u p.2)) :=
    (hh.comp (freeTrajectory_continuous m L t).measurable).mul
      ((sliceNormSq_measurable u).comp measurable_snd).ennreal_ofReal
  rw [lintegral_congr_ae heq,lintegral_prod_symm _ hp.aemeasurable]
  apply lintegral_congr
  intro y
  simpa only [freePathExpectation] using lintegral_mul_const (μ:=coordinateWiener m)
    (ENNReal.ofReal (sliceNormSq u y)) (show Measurable (fun w : CoordinatePaths m ↦
    h (freeTrajectory m L t w y)) from hh.comp ((freeTrajectory_continuous m L t).measurable.comp
      (measurable_id.prodMk measurable_const)))

lemma slice_mass_integral {m n : ℕ} {L : Length} (u : Jet (m+n) L)
    {H : Configuration m L → ℝ≥0∞} (hH : Measurable H) :
    (∫⁻ y : Configuration m L, H y*ENNReal.ofReal (sliceNormSq u.1 y) ∂volume)=
      ∫⁻ X : Configuration (m+n) L, H (splitConfiguration m n L X).1 ∂groundPositionLaw (m+n) L u := by
  have hu := (Lp.stronglyMeasurable u.1).measurable
  have hmH : Measurable (fun X : Configuration (m+n) L ↦ H (splitConfiguration m n L X).1) :=
    hH.comp (splitConfiguration_continuous m n L).measurable.fst
  rw [groundPositionLaw,lintegral_withDensity_eq_lintegral_mul volume
    (hu.norm.pow_const 2).ennreal_ofReal hmH]
  have hD : Measurable (fun X : Configuration (m+n) L ↦
      ENNReal.ofReal (‖u.1 X‖^2)*H (splitConfiguration m n L X).1) :=
    (hu.norm.pow_const 2).ennreal_ofReal.mul hmH
  have hJ : Measurable (fun p : Configuration m L × Configuration n L ↦
      ENNReal.ofReal (‖u.1 (joinConfiguration m n L p)‖^2)*H p.1) :=
    (((hu.comp (joinConfiguration_continuous m n L).measurable).norm.pow_const 2).ennreal_ofReal).mul
      (hH.comp measurable_fst)
  have hj := (joinConfiguration_preserving m n L).lintegral_comp hD
  simp only [split_joinConfiguration] at hj
  simp only [Pi.mul_apply]
  rw [← hj,lintegral_prod _ hJ.aemeasurable]
  apply lintegral_congr_ae
  filter_upwards [memLp_slice_ae u.1] with y hy
  have hyM : Measurable (fun x : Configuration n L ↦
      ENNReal.ofReal (‖u.1 (joinConfiguration m n L (y,x))‖^2)) :=
    (((hu.comp (joinConfiguration_continuous m n L).measurable).comp
      (measurable_const.prodMk measurable_id)).norm.pow_const 2).ennreal_ofReal
  rw [sliceNormSq,ofReal_integral_eq_lintegral_ofReal
    (hy.integrable_norm_pow (show (2:ℕ)≠0 by norm_num)) (Eventually.of_forall fun _ ↦ sq_nonneg _)]
  rw [← lintegral_const_mul _ hyM]
  apply lintegral_congr
  intro x
  exact mul_comm _ _

lemma selected_start_ground_integral {m n : ℕ} {L : Length} (u : Jet (m+n) L) (t : ℝ)
    {h : ConfigurationPath m L → ℝ≥0∞} (hh : Measurable h) :
    (∫⁻ ω : ConfigurationPath m L, h ω*ENNReal.ofReal (sliceNormSq u.1 (ω 0)) ∂freePathLaw m L t)=
      ∫⁻ X : Configuration (m+n) L,
        freePathExpectation t h (splitConfiguration m n L X).1 ∂groundPositionLaw (m+n) L u := by
  rw [selected_start_integral u.1 t hh]
  exact slice_mass_integral u (freePathExpectation_measurable t hh)

lemma groundPathLaw_deletion : ∃ C : ℝ, 0<C ∧
    ∀ (m n : ℕ) (L : Length) (r t : ℝ), 0 < r → 0<t →
    ((m+n:ℕ):ℝ)*(2*Real.pi*r)^3≤L.val^3/2 →
    ∀ u : Jet (m+n) L, IsGroundVector (m+n) L r u →
    ∀ h : ConfigurationPath m L → ℝ≥0∞, Measurable h →
    (∀ ω, h (reverseConfigurationPath m L ω)=h ω) →
      (∫⁻ ω : ConfigurationPath (m+n) L, h (splitConfigurationPath m n L ω).1
        ∂groundPathLaw (m+n) L r t u) ≤
      ENNReal.ofReal (Real.exp (t*C*(m:ℝ)*((m+n:ℕ):ℝ)*r/L.val^3))*
        ∫⁻ X : Configuration (m+n) L,
          freePathExpectation t h (splitConfiguration m n L X).1 ∂groundPositionLaw (m+n) L u := by
  obtain ⟨C,hC,hbath⟩ := bath_heat_bound
  refine ⟨C,hC,?_⟩
  intro m n L r t hr ht hs u hu h hh hrev
  have hb := hbath n m
  rw [Nat.add_comm n m] at hb
  have hb' := hb L r t hr ht hs u hu
  have hm := deleted_path_integral_le u.1 r t hh hrev
  rw [selected_start_ground_integral u t hh] at hm
  have hmH : Measurable (fun ω : ConfigurationPath (m+n) L ↦ h (splitConfigurationPath m n L ω).1) :=
    hh.comp (splitConfigurationPath_continuous m n L).measurable.fst
  have hend : Measurable (fun ω : ConfigurationPath (m+n) L ↦
      ENNReal.ofReal (‖u.1 (ω 0)‖*‖u.1 (ω 1)‖)) := by
    have hu := (Lp.stronglyMeasurable u.1).measurable
    exact ((hu.comp (continuous_eval_const (0:Time)).measurable).norm.mul
      (hu.comp (continuous_eval_const (1:Time)).measurable).norm).ennreal_ofReal
  rw [groundPathLaw,lintegral_withDensity_eq_lintegral_mul _
    (groundPathWeight_measurable u t).ennreal_ofReal hmH]
  simp only [Pi.mul_apply,groundPathWeight,ENNReal.ofReal_mul (Real.exp_pos _).le]
  calc
    _ = ENNReal.ofReal (Real.exp (t*energy u))*
        ∫⁻ ω : ConfigurationPath (m+n) L,
          h (splitConfigurationPath m n L ω).1*ENNReal.ofReal (‖u.1 (ω 0)‖*‖u.1 (ω 1)‖)
          ∂killedPathLaw (m+n) L r t := by
      rw [← lintegral_const_mul _ (show Measurable (fun ω : ConfigurationPath (m+n) L ↦
        h (splitConfigurationPath m n L ω).1*ENNReal.ofReal (‖u.1 (ω 0)‖*‖u.1 (ω 1)‖)) from hmH.mul hend)]
      apply lintegral_congr
      intro ω
      ac_rfl
    _ ≤ ENNReal.ofReal (Real.exp (t*energy u))*(ENNReal.ofReal ‖killedTransition n L r t‖*
        ∫⁻ X : Configuration (m+n) L,
          freePathExpectation t h (splitConfiguration m n L X).1 ∂groundPositionLaw (m+n) L u) :=
      mul_le_mul_right hm _
    _ ≤ ENNReal.ofReal (Real.exp (t*energy u))*ENNReal.ofReal
        (Real.exp (-t*(energy u-C*(m:ℝ)*((m+n:ℕ):ℝ)*r/L.val^3)))*
        ∫⁻ X : Configuration (m+n) L,
          freePathExpectation t h (splitConfiguration m n L X).1 ∂groundPositionLaw (m+n) L u := by
      rw [← mul_assoc]
      exact mul_le_mul_left (mul_le_mul_right (ENNReal.ofReal_le_ofReal hb') _) _
    _ = _ := by
      rw [← ENNReal.ofReal_mul (Real.exp_pos _).le,← Real.exp_add]
      congr 3
      ring
end
end HardSphere

end
end
end

section
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere
open Wiener

lemma oneFreeExpectation_measurable {L : Length} (t : ℝ)
    {h : ConfigurationPath 1 L → ℝ≥0∞} (hh : Measurable h) : Measurable (oneFreeExpectation t h) := by
  exact (freePathExpectation_measurable t hh).comp (by unfold oneConfiguration; fun_prop)

lemma pathProduct_measurable {n : ℕ} {L : Length} (S : Finset (Fin n))
    {h : ConfigurationPath 1 L → ℝ≥0∞} (hh : Measurable h) :
    Measurable (fun ω : ConfigurationPath n L ↦ ∏ i∈S, h (onePathAt i ω)) := by
  exact Finset.measurable_prod S fun i _ ↦ hh.comp (onePathAt_continuous i).measurable

lemma free_product_expectation {n : ℕ} {L : Length} (t : ℝ)
    {h : ConfigurationPath 1 L → ℝ≥0∞} (hh : Measurable h) (X : Configuration n L) :
    freePathExpectation t (fun ω : ConfigurationPath n L ↦ ∏ i, h (onePathAt i ω)) X=
      ∏ i,oneFreeExpectation t h (X i) := by
  induction n with
  | zero => simp [freePathExpectation]
  | succ n ih =>
    change (∫⁻ w : CoordinatePaths (n+1), ∏ i, h (onePathAt i (freeTrajectory (n+1) L t w X))
      ∂coordinateWiener (n+1))=_
    let Xm := (splitConfiguration n 1 L X).1
    let X1 := (splitConfiguration n 1 L X).2
    have hXm : Measurable (fun w : CoordinatePaths n ↦
        ∏ i, h (onePathAt i (freeTrajectory n L t w Xm))) :=
      (pathProduct_measurable Finset.univ hh).comp
        ((freeTrajectory_continuous n L t).measurable.comp (measurable_id.prodMk measurable_const))
    have hX1 : Measurable (fun w : CoordinatePaths 1 ↦ h (freeTrajectory 1 L t w X1)) :=
      hh.comp ((freeTrajectory_continuous 1 L t).measurable.comp (measurable_id.prodMk measurable_const))
    have hfull : Measurable (fun w : CoordinatePaths (n+1) ↦
        ∏ i, h (onePathAt i (freeTrajectory (n+1) L t w X))) :=
      (pathProduct_measurable Finset.univ hh).comp
        ((freeTrajectory_continuous (n+1) L t).measurable.comp (measurable_id.prodMk measurable_const))
    rw [←(joinCoordinatePaths_preserving n 1).lintegral_comp hfull]
    have he (w : CoordinatePaths n × CoordinatePaths 1) :
        freeTrajectory (n+1) L t (joinCoordinatePaths n 1 w) X=
          joinConfigurationPath n 1 L (freeTrajectory n L t w.1 Xm,freeTrajectory 1 L t w.2 X1) := by
      rw [←freeTrajectory_join,join_splitConfiguration]
    simp only [he,Fin.prod_univ_add,onePathAt_join_left,onePathAt_join_right,
      Fin.prod_univ_one,onePathAt_single]
    rw [lintegral_prod_mul hXm.aemeasurable hX1.aemeasurable]
    change freePathExpectation t (fun ω : ConfigurationPath n L ↦ ∏ i,h (onePathAt i ω)) Xm *
      freePathExpectation t h X1 = _
    rw [ih]
    congr 1
    change freePathExpectation t h X1 = freePathExpectation t h (oneConfiguration (X (Fin.natAdd n 0)))
    congr 1
    funext i
    have hi : i=0 := Subsingleton.elim _ _
    subst i
    rfl

end HardSphere

end
end

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_PathPermutation
attribute [-instance] _root_.OAI.HardSphere.Bridge.exposedBridgeKernel_markov _root_.OAI.HardSphere.Bridge.exposedPeriodSingle_finite _root_.OAI.HardSphere.Bridge.exposedTrialKernel_markov _root_.OAI.HardSphere.Bridge.instBorelSpaceContinuousMapElemRealTimePoint _root_.OAI.HardSphere.Bridge.instIsProbabilityMeasureNoiseLaw _root_.OAI.HardSphere.Bridge.instMeasurableSpaceContinuousMapElemRealTimePoint _root_.OAI.HardSphere.Bridge.parameterBridgeKernel_markov _root_.OAI.HardSphere.Bridge.parameterIndividualReference_finite _root_.OAI.HardSphere.Bridge.parameterTrialKernel_markov _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Bridge.trialKernel_markov _root_.OAI.HardSphere.Groups.cellPathReference_probability _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Rescaling.config_haar _root_.OAI.HardSphere.bridgeEndpointBase_finite _root_.OAI.HardSphere.coordinateBridge_probability _root_.OAI.HardSphere.endpointWeightedBase_sfinite _root_.OAI.HardSphere.freePathLaw_finite_deletion _root_.OAI.HardSphere.gaussianCoordinates_probability _root_.OAI.HardSphere.killedPathLaw_finite_deletion
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

lemma permuteConfigurationPath_continuous {n : ℕ} {L : Length} (σ : Equiv.Perm (Fin n)) :
    Continuous (permuteConfigurationPath (L:=L) σ) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  change Continuous (fun p : ConfigurationPath n L × Time ↦ fun i ↦ p.1 p.2 (σ i))
  fun_prop

lemma permuteCoordinatePaths_preserving {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    MeasurePreserving (permuteCoordinatePaths σ) (coordinateWiener n) (coordinateWiener n) := by
  have h := measurePreserving_piCongrLeft (fun _ : Direction n ↦ wiener)
    (σ.symm.prodCongr (Equiv.refl (Fin 3)))
  convert h using 1 <;> try rfl
  funext w p
  simp [permuteCoordinatePaths,MeasurableEquiv.coe_piCongrLeft,Equiv.piCongrLeft_apply_eq_cast]
  rfl

lemma permute_freePath_preserving {n : ℕ} (L : Length) (t : ℝ) (σ : Equiv.Perm (Fin n)) :
    MeasurePreserving (permuteConfigurationPath σ) (freePathLaw n L t) (freePathLaw n L t) := by
  refine ⟨(permuteConfigurationPath_continuous σ).measurable,?_⟩
  have h := (permuteCoordinatePaths_preserving σ).prod (measurePreserving_permute (L:=L) σ)
  rw [freePathLaw,Measure.map_map (permuteConfigurationPath_continuous σ).measurable
    (freeTrajectory_continuous n L t).measurable]
  conv_rhs => rw [←h.map_eq]
  rw [Measure.map_map (freeTrajectory_continuous n L t).measurable h.measurable]
  rfl

lemma permute_staysAllowed {n : ℕ} (L : Length) (r : ℝ) (σ : Equiv.Perm (Fin n)) :
    permuteConfigurationPath σ ⁻¹' staysAllowed n L r = staysAllowed n L r := by
  ext ω
  simp only [Set.mem_preimage,staysAllowed,Set.mem_ofPred_eq,Set.range_subset_iff]
  constructor
  · intro h s
    exact (allowed_permute σ (ω s)).mp (h s)
  · intro h s
    exact (allowed_permute σ (ω s)).mpr (h s)

lemma permute_killedPath_preserving {n : ℕ} (L : Length) (r t : ℝ) (σ : Equiv.Perm (Fin n)) :
    MeasurePreserving (permuteConfigurationPath σ) (killedPathLaw n L r t) (killedPathLaw n L r t) := by
  have h := (permute_freePath_preserving L t σ).restrict_preimage (staysAllowed_open n L r).measurableSet
  rw [permute_staysAllowed] at h
  exact h

lemma measurePreserving_weighted_ae_invariant {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {R : α → α} (hR : MeasurePreserving R μ μ)
    (w : α → ℝ≥0∞) (hw : Measurable w) (hi : (fun x ↦ w (R x)) =ᵐ[μ] w) :
    MeasurePreserving R (μ.withDensity w) (μ.withDensity w) := by
  refine ⟨hR.measurable,Measure.ext fun S hS ↦ ?_⟩
  rw [Measure.map_apply hR.measurable hS,withDensity_apply _ (hS.preimage hR.measurable),
    withDensity_apply _ hS,←lintegral_indicator (hS.preimage hR.measurable),←lintegral_indicator hS]
  calc
    _ = ∫⁻ x, (S.indicator w) (R x) ∂μ := by
      apply lintegral_congr_ae
      filter_upwards [hi] with x hx
      by_cases h : R x∈S
      · simp only [Set.indicator_of_mem h,Set.indicator_of_mem (show x∈R ⁻¹' S from h),hx]
      · simp only [Set.indicator_of_notMem h,Set.indicator_of_notMem (show x∉R ⁻¹' S from h)]
    _ = _ := hR.lintegral_comp (hw.indicator hS)

lemma groundPositionLaw_permute {n : ℕ} {L : Length} (u : Jet n L) (hb : bosonic u.1)
    (σ : Equiv.Perm (Fin n)) :
    MeasurePreserving (permuteConfiguration σ) (groundPositionLaw n L u) (groundPositionLaw n L u) := by
  apply measurePreserving_weighted_ae_invariant (measurePreserving_permute σ) _
    ((Lp.stronglyMeasurable u.1).measurable.norm.pow_const 2).ennreal_ofReal
  filter_upwards [hb σ] with X hX
  change ENNReal.ofReal (‖u.1 (fun i ↦ X (σ i))‖^2)=ENNReal.ofReal (‖u.1 X‖^2)
  rw [hX]

lemma groundPathLaw_permute {n : ℕ} {L : Length} (u : Jet n L) (hb : bosonic u.1)
    (r t : ℝ) (σ : Equiv.Perm (Fin n)) :
    MeasurePreserving (permuteConfigurationPath σ) (groundPathLaw n L r t u) (groundPathLaw n L r t u) := by
  apply measurePreserving_weighted_ae_invariant (permute_killedPath_preserving L r t σ) _
    (groundPathWeight_measurable u t).ennreal_ofReal
  have hp (s : Time) := (((freePathLaw_marginal n L t s).quasiMeasurePreserving.ae_eq_comp
    (hb σ)).filter_mono (ae_mono (Measure.restrict_le_self (s:=staysAllowed n L r))))
  filter_upwards [hp 0,hp 1] with ω h0 h1
  simp only [Function.comp_def] at h0 h1
  change ENNReal.ofReal (Real.exp (t*energy u)*(‖u.1 (fun i ↦ ω 0 (σ i))‖*
    ‖u.1 (fun i ↦ ω 1 (σ i))‖))=ENNReal.ofReal (Real.exp (t*energy u)*(‖u.1 (ω 0)‖*‖u.1 (ω 1)‖))
  rw [h0,h1]

end HardSphere

end
end

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Orbitals_SelectedDeletion
attribute [-instance] _root_.OAI.HardSphere.Bridge.exposedBridgeKernel_markov _root_.OAI.HardSphere.Bridge.exposedPeriodSingle_finite _root_.OAI.HardSphere.Bridge.exposedTrialKernel_markov _root_.OAI.HardSphere.Bridge.instBorelSpaceContinuousMapElemRealTimePoint _root_.OAI.HardSphere.Bridge.instIsProbabilityMeasureNoiseLaw _root_.OAI.HardSphere.Bridge.instMeasurableSpaceContinuousMapElemRealTimePoint _root_.OAI.HardSphere.Bridge.parameterBridgeKernel_markov _root_.OAI.HardSphere.Bridge.parameterIndividualReference_finite _root_.OAI.HardSphere.Bridge.parameterTrialKernel_markov _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Bridge.trialKernel_markov _root_.OAI.HardSphere.Groups.cellPathReference_probability _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Rescaling.config_haar _root_.OAI.HardSphere.bridgeEndpointBase_finite _root_.OAI.HardSphere.coordinateBridge_probability _root_.OAI.HardSphere.endpointWeightedBase_sfinite _root_.OAI.HardSphere.gaussianCoordinates_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open scoped BigOperators
namespace HardSphere

lemma selectedPermutation_prod {m n : ℕ} (S : Finset (Fin (m+n))) (hS : S.card=m)
    {M : Type*} [CommMonoid M] (f : Fin (m+n) → M) :
    (∏ i : Fin m,f (selectedPermutation S hS (Fin.castAdd n i)))=∏i∈S,f i := by
  classical
  have he (i : Fin m) : selectedPermutation S hS (Fin.castAdd n i)=((S.equivFinOfCardEq hS).symm i).val := by
    simp [selectedPermutation]
  simp only [he]
  exact ((S.equivFinOfCardEq hS).symm.prod_comp (fun i : S ↦ f i.val)).trans (Finset.prod_coe_sort S f)

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
open Wiener

lemma selected_product_deletion : ∃ C : ℝ, 0<C ∧
    ∀ (N : ℕ) (L : Length) (r t : ℝ), 0 < r → 0<t →
    (N:ℝ)*(2*Real.pi*r)^3≤L.val^3/2 →
    ∀ u : Jet N L, IsGroundVector N L r u →
    ∀ h : ConfigurationPath 1 L → ℝ≥0∞, Measurable h →
    (∀ ω,h (reverseConfigurationPath 1 L ω)=h ω) →
    ∀ S : Finset (Fin N),
      (∫⁻ ω : ConfigurationPath N L, ∏i∈S,h (onePathAt i ω) ∂groundPathLaw N L r t u) ≤
      ENNReal.ofReal (Real.exp (t*C*(S.card:ℝ)*(N:ℝ)*r/L.val^3))*
        ∫⁻ X : Configuration N L, ∏i∈S,oneFreeExpectation t h (X i) ∂groundPositionLaw N L u := by
  classical
  obtain ⟨C,hC,hdel⟩ := groundPathLaw_deletion
  refine ⟨C,hC,?_⟩
  intro N L r t hr ht hs u hu h hh hrev S
  have hc : S.card≤N := by simpa using Finset.card_le_univ S
  obtain ⟨n,hn⟩ := Nat.exists_eq_add_of_le hc
  generalize hm : S.card=m at hn
  subst N
  let σ := selectedPermutation S hm
  let H : ConfigurationPath m L → ℝ≥0∞ := fun ω ↦ ∏i,h (onePathAt i ω)
  have hH : Measurable H := pathProduct_measurable Finset.univ hh
  have hHrev (ω : ConfigurationPath m L) : H (reverseConfigurationPath m L ω)=H ω := by
    simp only [H,onePathAt_reverse,hrev]
  have hD := hdel m n L r t hr ht hs u hu H hH hHrev
  have hexp : (∫⁻ ω : ConfigurationPath (m+n) L,H (splitConfigurationPath m n L ω).1
      ∂groundPathLaw (m+n) L r t u)=
      ∫⁻ ω : ConfigurationPath (m+n) L,∏i∈S,h (onePathAt i ω) ∂groundPathLaw (m+n) L r t u := by
    have hp := (groundPathLaw_permute u hu.2.1 r t σ).lintegral_comp
      (hH.comp (splitConfigurationPath_continuous m n L).measurable.fst)
    simp only [Function.comp_def] at hp
    rw [←hp]
    apply lintegral_congr
    intro ω
    simp only [H,onePathAt_split_left,onePathAt_permute]
    exact selectedPermutation_prod S hm (fun i ↦ h (onePathAt i ω))
  have hF (X : Configuration (m+n) L) :
      freePathExpectation t H (splitConfiguration m n L X).1=
        ∏i:Fin m,oneFreeExpectation t h (X (Fin.castAdd n i)) :=
    free_product_expectation t hh _
  have hM : Measurable (fun X : Configuration (m+n) L ↦
      ∏i:Fin m,oneFreeExpectation t h (X (Fin.castAdd n i))) :=
    Finset.measurable_prod Finset.univ fun i _ ↦ (oneFreeExpectation_measurable t hh).comp (measurable_pi_apply _)
  have hpos : (∫⁻ X : Configuration (m+n) L,
      freePathExpectation t H (splitConfiguration m n L X).1 ∂groundPositionLaw (m+n) L u)=
      ∫⁻ X : Configuration (m+n) L,∏i∈S,oneFreeExpectation t h (X i) ∂groundPositionLaw (m+n) L u := by
    simp only [hF]
    rw [←(groundPositionLaw_permute u hu.2.1 σ).lintegral_comp hM]
    apply lintegral_congr
    intro X
    exact selectedPermutation_prod S hm (fun i ↦ oneFreeExpectation t h (X i))
  rw [hexp,hpos] at hD
  simpa only [hm] using hD

lemma ground_product_one_add_oai : ∃ C : ℝ, 0<C ∧
    ∀ (N : ℕ) (L : Length) (r t : ℝ), 0 < r → 0<t →
    (N:ℝ)*(2*Real.pi*r)^3≤L.val^3/2 →
    ∀ u : Jet N L, IsGroundVector N L r u →
    ∀ h : ConfigurationPath 1 L → ℝ≥0∞, Measurable h →
    (∀ ω,h (reverseConfigurationPath 1 L ω)=h ω) →
      (∫⁻ ω : ConfigurationPath N L, ∏i, (1+h (onePathAt i ω)) ∂groundPathLaw N L r t u) ≤
        ∫⁻ X : Configuration N L, ∏i,(1+ENNReal.ofReal (Real.exp (t*C*(N:ℝ)*r/L.val^3))*
          oneFreeExpectation t h (X i)) ∂groundPositionLaw N L u := by
  classical
  obtain ⟨C,hC,hdel⟩ := selected_product_deletion
  refine ⟨C,hC,?_⟩
  intro N L r t hr ht hs u hu h hh hrev
  let a : ℝ≥0∞ := ENNReal.ofReal (Real.exp (t*C*(N:ℝ)*r/L.val^3))
  have ha (S : Finset (Fin N)) :
      ENNReal.ofReal (Real.exp (t*C*(S.card:ℝ)*(N:ℝ)*r/L.val^3))=a^S.card := by
    rw [show t*C*(S.card:ℝ)*(N:ℝ)*r/L.val^3=(S.card:ℝ)*(t*C*(N:ℝ)*r/L.val^3) by ring,
      Real.exp_nat_mul,ENNReal.ofReal_pow (Real.exp_nonneg _)]
  have hb (S : Finset (Fin N)) : Measurable (fun X : Configuration N L ↦
      ∏i∈S,a*oneFreeExpectation t h (X i)) :=
    Finset.measurable_prod S fun i _ ↦ measurable_const.mul
      ((oneFreeExpectation_measurable t hh).comp (measurable_pi_apply i))
  simp only [Finset.prod_one_add]
  rw [lintegral_finsetSum _ (fun S _ ↦ pathProduct_measurable S hh),
    lintegral_finsetSum _ (fun S _ ↦ hb S)]
  apply Finset.sum_le_sum
  intro S _
  calc
    _ ≤ a^S.card*∫⁻ X : Configuration N L,∏i∈S,oneFreeExpectation t h (X i)
        ∂groundPositionLaw N L u := by simpa only [ha] using hdel N L r t hr ht hs u hu h hh hrev S
    _ = ∫⁻ X : Configuration N L,∏i∈S,a*oneFreeExpectation t h (X i) ∂groundPositionLaw N L u := by
      have hM : Measurable (fun X : Configuration N L ↦ ∏i∈S,oneFreeExpectation t h (X i)) :=
        Finset.measurable_prod S fun i _ ↦ (oneFreeExpectation_measurable t hh).comp (measurable_pi_apply i)
      rw [←lintegral_const_mul _ hM]
      apply lintegral_congr
      intro X
      simp only [Finset.prod_mul_distrib,Finset.prod_const]

end HardSphere

end
end

end

end OAI
end

theorem solution : type_of% @OAI.HardSphere.ground_product_one_add_oai := @OAI.HardSphere.ground_product_one_add_oai
