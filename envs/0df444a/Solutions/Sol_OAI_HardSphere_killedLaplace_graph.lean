-- Prove2me | solution 1 for OAI.HardSphere.killedLaplace_graph
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T20:32:21.442537+00:00
-- url     : https://prove2.me/submissions/d19d142a-57cb-4fc2-88f3-3cf5bacd4038

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

lemma allowed_antitone (N : ℕ) (L : Length) : Antitone (allowed N L) := by
  intro a b hab X hX i j hij
  exact lt_of_le_of_lt hab (hX i j hij)

lemma innerRadius_gt (a : ℝ) (n : ℕ) : a < innerRadius a n := by
  unfold innerRadius
  have : 0 < 1 / ((n:ℝ)+1) := by positivity
  linarith

lemma innerRadius_antitone (a : ℝ) : Antitone (innerRadius a) := by
  intro m n hmn
  unfold innerRadius
  apply add_le_add le_rfl
  apply one_div_le_one_div_of_le (by positivity)
  exact_mod_cast Nat.add_le_add_right hmn 1

lemma innerRadius_tendsto (a : ℝ) : Tendsto (innerRadius a) atTop (𝓝 a) := by
  change Tendsto (fun n : ℕ ↦ a + 1 / ((n:ℝ)+1)) atTop (𝓝 a)
  simpa only [add_zero] using (tendsto_const_nhds (x := a)).add (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))

lemma iUnion_allowed_innerRadius (N : ℕ) (L : Length) (a : ℝ) :
    (⋃ n, allowed N L (innerRadius a n)) = allowed N L a := by
  apply Subset.antisymm
  · exact iUnion_subset fun n ↦ allowed_antitone N L (innerRadius_gt a n).le
  · intro X hX
    have h : ∀ i j : Fin N, ∀ᶠ n in atTop, i < j → innerRadius a n < torusDistance L (X i) (X j) := by
      intro i j
      by_cases hij : i < j
      · exact ((innerRadius_tendsto a).eventually (gt_mem_nhds (hX i j hij))).mono fun _ hn _ ↦ hn
      · exact Filter.Eventually.of_forall fun _ h ↦ (hij h).elim
    have hh : ∀ᶠ n in atTop, ∀ i j : Fin N, i < j → innerRadius a n < torusDistance L (X i) (X j) := by
      exact Filter.eventually_all.mpr fun i ↦ Filter.eventually_all.mpr (h i)
    obtain ⟨n, hn⟩ := hh.exists
    exact mem_iUnion.mpr ⟨n,hn⟩

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
namespace HardSphere
open Wiener

lemma staysAllowed_antitone (N : ℕ) (L : Length) : Antitone (staysAllowed N L) := by
  intro a b hab f hf
  exact hf.trans (allowed_antitone N L hab)

lemma staysAllowed_innerRadius (N : ℕ) (L : Length) (a : ℝ) :
    (⋃ n, staysAllowed N L (innerRadius a n)) = staysAllowed N L a := by
  apply Set.Subset.antisymm
  · exact iUnion_subset fun n ↦ staysAllowed_antitone N L (innerRadius_gt a n).le
  · intro f hf
    have hcompact : IsCompact (Set.range f) := isCompact_range f.continuous
    obtain ⟨n,hn⟩ := hcompact.elim_directed_cover (fun n ↦ allowed N L (innerRadius a n))
      (fun n ↦ isOpen_allowed N L _) (by rw [iUnion_allowed_innerRadius]; exact hf)
      (fun m n ↦ ⟨max m n,allowed_antitone N L (innerRadius_antitone a (le_max_left _ _)),
        allowed_antitone N L (innerRadius_antitone a (le_max_right _ _))⟩)
    exact mem_iUnion.mpr ⟨n,hn⟩

end HardSphere

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

omit [CompleteSpace E] in
lemma semigroupLaplace_norm_le (K : ℝ → E→L[ℂ] E)
    (hc : ∀ f, Continuous (fun t : ℝ ↦ K (max 0 t) f))
    (hnorm : ∀ t, 0 ≤ t → ∀ f, ‖K t f‖≤‖f‖) (f : E) :
    ‖semigroupLaplace K f‖≤‖f‖ := by
  calc
    _ ≤ ∫ t in Ioi (0:ℝ), ‖laplaceIntegrand K f t‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ t in Ioi (0:ℝ), Real.exp (-t)*‖f‖ := by
      apply integral_mono_ae (laplaceIntegrand_integrable K hc hnorm f 0).norm
        ((integrableOn_exp_neg_Ioi 0).mul_const ‖f‖)
      exact Eventually.of_forall (fun t ↦ by
        dsimp only [laplaceIntegrand]
        rw [norm_smul,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
        exact mul_le_mul_of_nonneg_left (hnorm _ (le_max_left _ _) f) (Real.exp_nonneg _))
    _ = ‖f‖ := by rw [integral_mul_const,integral_exp_neg_Ioi_zero,one_mul]

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

lemma semigroupLaplace_norm_sub_le (K : ℝ → E→L[ℂ] E)
    (hadd : ∀ s t, 0 ≤ s → 0 ≤ t → K (s+t)=(K s).comp (K t))
    (hc : ∀ f, Continuous (fun t : ℝ ↦ K (max 0 t) f))
    (hnorm : ∀ t, 0 ≤ t → ∀ f, ‖K t f‖≤‖f‖) (f : E) {h : ℝ}
    (hh : 0 ≤ h) (hh1 : h ≤ 1) :
    ‖semigroupLaplace K f-K h (semigroupLaplace K f)‖≤
      (2*Real.exp 1)*h*‖f‖ := by
  have hexp : Real.exp h-1≤Real.exp 1*h := by
    have hm := mul_le_mul_of_nonneg_left (Real.add_one_le_exp (-h)) (Real.exp_nonneg h)
    rw [← Real.exp_add,add_neg_cancel,Real.exp_zero] at hm
    have hm2 := mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hh1) hh
    nlinarith
  have he1 : 1≤Real.exp h := by simpa using Real.exp_le_exp.mpr hh
  have hi : ‖∫ s in (0:ℝ)..h, laplaceIntegrand K f s‖≤h*‖f‖ := by
    have hb : ∀ s ∈ Set.uIoc (0:ℝ) h, ‖laplaceIntegrand K f s‖≤‖f‖ := by
      intro s hs
      rw [Set.uIoc_of_le hh] at hs
      dsimp only [laplaceIntegrand]
      rw [max_eq_right (le_of_lt hs.1),norm_smul,Real.norm_eq_abs,
        abs_of_pos (Real.exp_pos _)]
      calc
        _ ≤ Real.exp (-s)*‖f‖ := mul_le_mul_of_nonneg_left
          (hnorm s (le_of_lt hs.1) f) (Real.exp_nonneg _)
        _ ≤ 1*‖f‖ := mul_le_mul_of_nonneg_right (by
          simpa using Real.exp_le_exp.mpr (neg_nonpos.mpr (le_of_lt hs.1))) (norm_nonneg _)
        _ = ‖f‖ := one_mul _
    simpa only [sub_zero,abs_of_nonneg hh,mul_comm] using
      intervalIntegral.norm_integral_le_of_norm_le_const hb
  rw [semigroupLaplace_shift K hadd hc hnorm f hh]
  have heq : semigroupLaplace K f-Real.exp h •
      (semigroupLaplace K f-∫ s in (0:ℝ)..h, laplaceIntegrand K f s)=
      (1-Real.exp h) • semigroupLaplace K f+
        Real.exp h • ∫ s in (0:ℝ)..h, laplaceIntegrand K f s := by module
  rw [heq]
  calc
    _ ≤ ‖(1-Real.exp h) • semigroupLaplace K f‖+
      ‖Real.exp h • ∫ s in (0:ℝ)..h, laplaceIntegrand K f s‖ := norm_add_le _ _
    _ = (Real.exp h-1)*‖semigroupLaplace K f‖+
      Real.exp h*‖∫ s in (0:ℝ)..h, laplaceIntegrand K f s‖ := by
      rw [norm_smul,norm_smul,Real.norm_eq_abs,Real.norm_eq_abs,
        abs_of_nonpos (by linarith),abs_of_pos (Real.exp_pos _)]
      ring
    _ ≤ (Real.exp 1*h)*‖f‖+Real.exp 1*(h*‖f‖) := by
      apply add_le_add
      · exact mul_le_mul hexp (semigroupLaplace_norm_le K hc hnorm f)
          (norm_nonneg _) (by positivity)
      · exact mul_le_mul (Real.exp_le_exp.mpr hh1) hi (norm_nonneg _) (Real.exp_nonneg _)
    _ = _ := by ring

omit [CompleteSpace E] in
lemma laplaceIntegrand_eq_complex (K : ℝ → E→L[ℂ] E) (f : E) (t : ℝ) :
    laplaceIntegrand K f t = (Real.exp (-t) : ℂ) • K (max 0 t) f := by
  exact RCLike.real_smul_eq_coe_smul (K := ℂ) _ _

end HardSphere

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_AvoidanceReflectionNorm
attribute [-instance] _root_.OAI.HardSphere.Bridge.exposedBridgeKernel_markov _root_.OAI.HardSphere.Bridge.exposedPeriodSingle_finite _root_.OAI.HardSphere.Bridge.exposedTrialKernel_markov _root_.OAI.HardSphere.Bridge.instBorelSpaceContinuousMapElemRealTimePoint _root_.OAI.HardSphere.Bridge.instIsProbabilityMeasureNoiseLaw _root_.OAI.HardSphere.Bridge.instMeasurableSpaceContinuousMapElemRealTimePoint _root_.OAI.HardSphere.Bridge.parameterBridgeKernel_markov _root_.OAI.HardSphere.Bridge.parameterIndividualReference_finite _root_.OAI.HardSphere.Bridge.parameterTrialKernel_markov _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Bridge.trialKernel_markov _root_.OAI.HardSphere.Groups.cellPathReference_probability _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Rescaling.config_haar _root_.OAI.HardSphere.bridgeEndpointBase_finite _root_.OAI.HardSphere.coordinateBridge_probability _root_.OAI.HardSphere.endpointWeightedBase_sfinite _root_.OAI.HardSphere.freePathLaw_finite_deletion _root_.OAI.HardSphere.killedPathLaw_finite_deletion
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

lemma avoidance_reflection_norm (N : ℕ) (L : Length) (a t : ℝ) (f : FreePathL2 N L t) :
    ‖(2:ℂ) • avoidanceMultiplier N L a t f-f‖≤‖f‖ := by
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [Lp.coeFn_sub ((2:ℂ) • avoidanceMultiplier N L a t f) f,
    Lp.coeFn_smul (2:ℂ) (avoidanceMultiplier N L a t f),
    avoidanceMultiplier_ae N L a t f] with ω hsub hsmul hf
  rw [hsub,Pi.sub_apply,hsmul,Pi.smul_apply,hf]
  by_cases h : ω∈staysAllowed N L a
  · simp only [Set.indicator_of_mem h,smul_eq_mul]
    convert le_refl ‖f ω‖ using 1
    all_goals try with_reducible_and_instances rfl
    congr 1
    ring
  · simp only [Set.indicator_of_notMem h,smul_zero,zero_sub,norm_neg,le_refl]

lemma free_deficit_le_twice_killed (N : ℕ) (L : Length) (a t : ℝ) (f : ScalarL2 N L) :
    ‖f‖^2-(inner ℂ f (freeTransition N L t f)).re ≤
      2*(‖f‖^2-(inner ℂ f (killedTransition N L a t f)).re) := by
  have h := re_inner_le_norm (𝕜 := ℂ) (endpointPull N L t 0 f)
    ((2:ℂ) • avoidanceMultiplier N L a t (endpointPull N L t 1 f)-endpointPull N L t 1 f)
  have hb := avoidance_reflection_norm N L a t (endpointPull N L t 1 f)
  have hn0 := (endpointPull N L t 0).norm_map f
  have hn1 := (endpointPull N L t 1).norm_map f
  have hi0 : inner ℂ (endpointPull N L t 0 f) (endpointPull N L t 1 f) =
      inner ℂ f (freeTransition N L t f) := by
    rw [freeTransition,ContinuousLinearMap.comp_apply,ContinuousLinearMap.adjoint_inner_right]
    rfl
  have hi1 : inner ℂ (endpointPull N L t 0 f)
      (avoidanceMultiplier N L a t (endpointPull N L t 1 f)) =
        inner ℂ f (killedTransition N L a t f) := by
    rw [killedTransition,ContinuousLinearMap.comp_apply,ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.adjoint_inner_right]
    rfl
  rw [inner_sub_right,inner_smul_right,hi0,hi1] at h
  change (2 * inner ℂ f (killedTransition N L a t f)-inner ℂ f (freeTransition N L t f)).re≤_ at h
  rw [Complex.sub_re,Complex.mul_re] at h
  norm_num at h
  simp only [LinearIsometry.norm_map] at hb
  have hmul := mul_le_mul_of_nonneg_left hb (norm_nonneg f)
  nlinarith

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

lemma coordinateCharacter_smooth {N : ℕ} {L : Length} (p : Direction N) :
    coordinateCharacter p ∈ smoothAlgebra N L := by
  change ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
    (fun X : LiftedConfiguration N ↦ fourier 1 (X p.1 p.2 : AddCircle L.val))
  simp_rw [fourier_coe_apply]
  exact Complex.contDiff_exp.comp
    ((((contDiff_const.mul contDiff_const).mul contDiff_const).mul contDiff_const).mul
      (Complex.ofRealCLM.contDiff.comp (contDiff_apply_apply ℝ ℝ p.1 p.2)) |>.div_const _)

lemma smoothAlgebra_separatesPoints (N : ℕ) (L : Length) :
    (smoothAlgebra N L).SeparatesPoints := by
  intro X Y hXY
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hXY
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hi
  refine ⟨_, ⟨coordinateCharacter (i,j), coordinateCharacter_smooth (i,j), rfl⟩, ?_⟩
  change fourier 1 (X i j) ≠ fourier 1 (Y i j)
  rw [fourier_one, fourier_one]
  intro he
  apply hj
  exact AddCircle.injective_toCircle L.property.ne' (Subtype.ext he)

lemma smoothAlgebra_dense (N : ℕ) (L : Length) :
    Dense (smoothAlgebra N L : Set C(Configuration N L, ℂ)) := by
  have hh := ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints
    (smoothAlgebra N L) (smoothAlgebra_separatesPoints N L)
  rw [dense_iff_closure_eq]
  exact congrArg (fun A : StarSubalgebra ℂ C(Configuration N L, ℂ) ↦ (A : Set C(Configuration N L, ℂ))) hh

lemma smoothAlgebra_toLp_dense (N : ℕ) (L : Length) :
    DenseRange (fun f : smoothAlgebra N L ↦
      ContinuousMap.toLp 2 volume ℂ (f : C(Configuration N L, ℂ))) := by
  exact (ContinuousMap.toLp_denseRange ℂ volume ℂ (by simp : (2 : ℝ≥0∞) ≠ ∞)).comp
    (smoothAlgebra_dense N L).denseRange_val (ContinuousMap.toLp 2 volume ℂ).continuous

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

lemma derivative_zero_of_scalar_zero {N : ℕ} {L : Length} {a : ℝ} {u : Jet N L}
    (hu : u ∈ dirichletDomain N L a) (hz : u.1 = 0) : u.2 = 0 := by
  funext p
  apply (inner_self_eq_zero (𝕜 := ℂ)).mp
  refine (smoothAlgebra_toLp_dense N L).induction_on
    (p := fun w ↦ inner ℂ w (u.2 p) = 0) (u.2 p)
    (isClosed_eq (continuous_id.inner continuous_const) continuous_const) ?_
  intro f
  have h := weak_derivative hu f p
  simpa only [hz, inner_zero_right, add_zero] using h

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

lemma heatScalar_zero (t : ℝ) : heatScalar t 0 = 0 := by simp [heatScalar]

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

lemma regularization_denom_pos {δ x : ℝ} (hδ : 0<δ) (hx : x∈Set.Icc (0:ℝ) 1) :
    0<δ+(1-δ)*x := by
  have he : δ+(1-δ)*x=δ*(1-x)+x := by ring
  rw [he]
  by_cases h : x=0
  · simp [h,hδ]
  · exact add_pos_of_nonneg_of_pos (mul_nonneg hδ.le (sub_nonneg.mpr hx.2))
      (lt_of_le_of_ne hx.1 (Ne.symm h))

lemma regularization_weight_continuous {δ : ℝ} (hδ : 0<δ) :
    ContinuousOn (regularizationWeight δ) (Set.Icc (0:ℝ) 1) := by
  apply (continuous_const.add (continuous_const.mul continuous_id)).continuousOn.inv₀
  exact fun x hx ↦ ne_of_gt (regularization_denom_pos hδ hx)

lemma regularization_energy_bound {δ x : ℝ} (hδ : 0<δ) (hx : x∈Set.Icc (0:ℝ) 1) :
    x*(regularizationWeight δ x)^2 ≤ 1+δ⁻¹*(1-heatScalar δ x) := by
  by_cases hx0 : x=0
  · simp only [hx0,zero_mul,heatScalar_zero,sub_zero,mul_one]
    positivity
  have hxp : 0<x := lt_of_le_of_ne hx.1 (Ne.symm hx0)
  let e : ℝ := x⁻¹-1
  have he0 : 0≤e := by
    dsimp [e]
    exact sub_nonneg.mpr ((one_le_inv₀ hxp).mpr hx.2)
  have hd : 0<1+δ*e := by positivity
  have hexp : Real.exp (-δ*e)≤(1+δ*e)⁻¹ := by
    rw [neg_mul,Real.exp_neg]
    exact inv_anti₀ hd (by simpa [add_comm] using Real.add_one_le_exp (δ*e))
  have hh : heatScalar δ x=Real.exp (-δ*e) := by
    rw [heatScalar_of_pos hδ hxp]
    congr 1
    dsimp [e]
    field_simp
    ring
  have he : x*(regularizationWeight δ x)^2=(1+e)/(1+δ*e)^2 := by
    dsimp [regularizationWeight,e]
    field_simp
    ring
  rw [he,hh]
  have hden : 1≤1+δ*e := by linarith [mul_nonneg hδ.le he0]
  calc
    _ ≤ (1+e)/(1+δ*e) := div_le_div_of_nonneg_left (by positivity) hd (by nlinarith)
    _ ≤ 1+e/(1+δ*e) := by
      apply (div_le_iff₀ hd).mpr
      rw [add_mul,div_mul_cancel₀ _ hd.ne']
      nlinarith
    _ = 1+δ⁻¹*(1-(1+δ*e)⁻¹) := by field_simp; ring
    _ ≤ _ := add_le_add_right (mul_le_mul_of_nonneg_left (sub_le_sub_left hexp _) (inv_nonneg.mpr hδ.le)) _

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

lemma regularized_lift_norm_sq (A : E →L[ℂ] F) (hA : ‖A‖≤1) {δ : ℝ}
    (hδ : 0<δ) (f : F) :
    let R := A.comp A.adjoint
    let W := cfc (p := IsSelfAdjoint) (regularizationWeight δ) R
    ‖A.adjoint (W f)‖^2 ≤
      ‖f‖^2+δ⁻¹*(‖f‖^2-(inner ℂ f ((cfc (p := IsSelfAdjoint) (heatScalar δ) R) f)).re) := by
  intro R W
  have hRp : R.IsPositive := by
    simpa [R] using isPositive_adjoint_comp_self A.adjoint
  have hRn : ‖R‖≤1 := by
    exact (opNorm_comp_le _ _).trans (by rw [adjoint.norm_map]; nlinarith [norm_nonneg A])
  have hspec := positive_contraction_spectrum hRp hRn
  have hw := (regularization_weight_continuous hδ).mono hspec
  have hW : IsSelfAdjoint W := IsSelfAdjoint.cfc
  have hnorm : ‖A.adjoint (W f)‖^2 = (inner ℂ f
      ((cfc (p := IsSelfAdjoint) (fun x ↦ x*(regularizationWeight δ x)^2) R) f)).re := by
    rw [norm_sq_eq_re_inner (𝕜 := ℂ)]
    have he : cfc (p := IsSelfAdjoint) (fun x ↦ x*(regularizationWeight δ x)^2) R = W*R*W := by
      calc
        _ = cfc (p := IsSelfAdjoint) (fun x ↦ regularizationWeight δ x*x*regularizationWeight δ x) R := by
          congr 1
          funext x
          ring
        _ = _ := by
          rw [cfc_mul (fun x:ℝ ↦ regularizationWeight δ x*x) (regularizationWeight δ) R (hw.mul continuous_id.continuousOn) hw,
            cfc_mul (regularizationWeight δ) (fun x:ℝ ↦ x) R hw continuous_id.continuousOn,cfc_id' ℝ R hRp.isSelfAdjoint]
    rw [he,mul_apply_eq_comp,mul_apply_eq_comp]
    change (inner ℂ (A.adjoint (W f)) (A.adjoint (W f))).re = _
    rw [adjoint_inner_left]
    change (inner ℂ (W f) (R (W f))).re = _
    rw [← adjoint_inner_right W f (R (W f)),hW.adjoint_eq]
  have hle : cfc (p := IsSelfAdjoint) (fun x ↦ x*(regularizationWeight δ x)^2) R ≤
      cfc (p := IsSelfAdjoint) (fun x ↦ 1+δ⁻¹*(1-heatScalar δ x)) R :=
    cfc_mono (fun x hx ↦ regularization_energy_bound hδ (hspec hx))
      (continuous_id.continuousOn.mul (hw.pow 2))
      (continuousOn_const.add (continuousOn_const.mul
        (continuousOn_const.sub (heatScalar_smooth δ).continuous.continuousOn)))
  have hp := (ContinuousLinearMap.le_def _ _).mp hle |>.re_inner_nonneg_right f
  have heval : cfc (p := IsSelfAdjoint) (fun x ↦ 1+δ⁻¹*(1-heatScalar δ x)) R =
      1+δ⁻¹ • (1-cfc (p := IsSelfAdjoint) (heatScalar δ) R) := by
    have hh := (heatScalar_smooth δ).continuous.continuousOn (s := spectrum ℝ R)
    rw [cfc_add (a := R) (fun _ : ℝ ↦ 1) (fun x:ℝ ↦ δ⁻¹*(1-heatScalar δ x)) continuousOn_const (continuousOn_const.mul (continuousOn_const.sub hh)),
      cfc_mul (fun _ : ℝ ↦ δ⁻¹) (fun x:ℝ ↦ 1-heatScalar δ x) R continuousOn_const (continuousOn_const.sub hh),
      cfc_sub (fun _ : ℝ ↦ 1) (heatScalar δ) R continuousOn_const hh,
      cfc_const 1 R hRp.isSelfAdjoint,cfc_const δ⁻¹ R hRp.isSelfAdjoint]
    simp only [Algebra.algebraMap_eq_smul_one,one_smul,smul_mul_assoc,one_mul]
  change 0≤(inner ℂ f ((cfc (p := IsSelfAdjoint) (fun x ↦ 1+δ⁻¹*(1-heatScalar δ x)) R-
    cfc (p := IsSelfAdjoint) (fun x ↦ x*(regularizationWeight δ x)^2) R) f)).re at hp
  rw [sub_apply,inner_sub_right,Complex.sub_re,heval,add_apply,smul_apply,sub_apply,
    one_apply_eq_self,inner_add_right,Complex.add_re] at hp
  have hself : (inner ℂ f f).re=‖f‖^2 := (norm_sq_eq_re_inner (𝕜 := ℂ) f).symm
  have hi : (inner ℂ f (δ⁻¹ • (f-(cfc (p := IsSelfAdjoint) (heatScalar δ) R) f))).re =
      δ⁻¹*(‖f‖^2-(inner ℂ f ((cfc (p := IsSelfAdjoint) (heatScalar δ) R) f)).re) := by
    rw [RCLike.real_smul_eq_coe_smul (K := ℂ),inner_smul_real_right,inner_sub_right,Complex.real_smul,Complex.mul_re,Complex.sub_re]
    simp only [Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero,hself]
  rw [hi,hself,← hnorm] at hp
  linarith
end
end HardSphere

namespace HardSphere
open ContinuousLinearMap Filter
open scoped Topology

lemma regularization_scalar_mem {δ x : ℝ} (hδ : 0<δ) (hx : x∈Set.Icc (0:ℝ) 1) :
    x*regularizationWeight δ x∈Set.Icc (0:ℝ) 1 := by
  have hd := regularization_denom_pos hδ hx
  change 0≤x*(δ+(1-δ)*x)⁻¹ ∧ x*(δ+(1-δ)*x)⁻¹≤1
  rw [← div_eq_mul_inv,div_le_one hd]
  exact ⟨div_nonneg hx.1 hd.le,by nlinarith [mul_nonneg hδ.le (sub_nonneg.mpr hx.2)]⟩

lemma regularization_error_bound {δ x : ℝ} (hδ : 0<δ) (hx : x∈Set.Icc (0:ℝ) 1) :
    |(x*regularizationWeight δ x-1)*x|≤δ := by
  have hs := regularization_scalar_mem hδ hx
  have he : (x*regularizationWeight δ x-1)*x = -δ*(1-x)*(x*regularizationWeight δ x) := by
    have hd := regularization_denom_pos hδ hx
    dsimp [regularizationWeight]
    have hi : (δ+(1-δ)*x)*(δ+(1-δ)*x)⁻¹=1 := mul_inv_cancel₀ hd.ne'
    nlinarith only [congrArg (fun y:ℝ ↦ y*x) hi]
  rw [he,abs_mul,abs_mul,abs_neg,abs_of_pos hδ,abs_of_nonneg (sub_nonneg.mpr hx.2),abs_of_nonneg hs.1]
  calc
    _ ≤ δ*1*1 := mul_le_mul (mul_le_mul_of_nonneg_left (by linarith [hx.1] : 1-x≤1) hδ.le)
      hs.2 hs.1 (by positivity)
    _ = δ := by ring

section
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [CompleteSpace F] [Nontrivial F]

lemma regularizationOperator_norm_le {R : F →L[ℂ] F} (hRp : R.IsPositive) (hRn : ‖R‖≤1)
    {δ : ℝ} (hδ : 0<δ) : ‖regularizationOperator R δ‖≤1 := by
  apply norm_cfc_le zero_le_one
  intro x hx
  have hs := regularization_scalar_mem hδ (positive_contraction_spectrum hRp hRn hx)
  simpa only [Real.norm_eq_abs,abs_of_nonneg hs.1] using hs.2

attribute [local instance] OAI.HardSphere.instAlgebraRealContinuousLinearMapComplexId_solutions
lemma regularizationOperator_eq {R : F →L[ℂ] F} (hRp : R.IsPositive) (hRn : ‖R‖≤1)
    {δ : ℝ} (hδ : 0<δ) :
    regularizationOperator R δ = R*cfc (p := IsSelfAdjoint) (regularizationWeight δ) R := by
  rw [regularizationOperator,cfc_mul (fun x:ℝ ↦ x) (regularizationWeight δ) R
    continuous_id.continuousOn ((regularization_weight_continuous hδ).mono
      (positive_contraction_spectrum hRp hRn)),cfc_id' ℝ R hRp.isSelfAdjoint]

lemma regularizationOperator_range_error {R : F →L[ℂ] F} (hRp : R.IsPositive) (hRn : ‖R‖≤1)
    {δ : ℝ} (hδ : 0<δ) : ‖(regularizationOperator R δ-1)*R‖≤δ := by
  have hw := (regularization_weight_continuous hδ).mono (positive_contraction_spectrum hRp hRn)
  have he : (regularizationOperator R δ-1)*R =
      cfc (p := IsSelfAdjoint) (fun x ↦ (x*regularizationWeight δ x-1)*x) R := by
    rw [cfc_mul (fun x:ℝ ↦ x*regularizationWeight δ x-1) (fun x:ℝ ↦ x) R
      ((continuous_id.continuousOn.mul hw).sub continuousOn_const) continuous_id.continuousOn,
      cfc_sub (fun x:ℝ ↦ x*regularizationWeight δ x) (fun _:ℝ ↦ 1) R
        (continuous_id.continuousOn.mul hw) continuousOn_const,
      cfc_const 1 R hRp.isSelfAdjoint,cfc_id' ℝ R hRp.isSelfAdjoint]
    simp only [map_one,regularizationOperator]
  rw [he]
  exact norm_cfc_le hδ.le (fun x hx ↦ by
    simpa only [Real.norm_eq_abs] using regularization_error_bound hδ (positive_contraction_spectrum hRp hRn hx))

lemma regularizationOperator_tendsto {ι : Type*} {l : Filter ι} {d : ι→ℝ}
    (hd : ∀ i, 0<d i) (ht : Tendsto d l (𝓝 0))
    {R : F →L[ℂ] F} (hRp : R.IsPositive) (hRn : ‖R‖≤1) (hRd : DenseRange R) (f : F) :
    Tendsto (fun i ↦ regularizationOperator R (d i) f) l (𝓝 f) := by
  have hC (i : ι) (u : F) : ‖regularizationOperator R (d i) u‖≤‖u‖ := by
    exact (le_opNorm _ _).trans (by simpa only [one_mul] using
      (mul_le_mul_of_nonneg_right (regularizationOperator_norm_le hRp hRn (hd i)) (norm_nonneg u)))
  have hRange : ∀ u : F, Tendsto (fun i ↦ regularizationOperator R (d i) (R u)) l (𝓝 (R u)) := by
    intro u
    rw [← tendsto_sub_nhds_zero_iff, tendsto_zero_iff_norm_tendsto_zero]
    apply squeeze_zero' (g := fun i ↦ d i*‖u‖) (Eventually.of_forall fun _ ↦ norm_nonneg _) ?_ ?_
    · exact Eventually.of_forall fun i ↦ by
        change ‖((regularizationOperator R (d i)-1)*R) u‖≤_
        exact (le_opNorm _ _).trans (mul_le_mul_of_nonneg_right
          (regularizationOperator_range_error hRp hRn (hd i)) (norm_nonneg u))
    · simpa using ht.mul_const ‖u‖
  have h := strong_contraction_limit_of_dense (fun i ↦ regularizationOperator R (d i))
    (ContinuousLinearMap.id ℂ F) hC (by simp) R hRd hRange f
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

lemma killedTransition_support (N : ℕ) (L : Length) (a t : ℝ) (f : ScalarL2 N L) :
    ∀ᵐ X ∂(volume : Measure (Configuration N L)), X∉allowed N L a → killedTransition N L a t f X=0 := by
  have he := congrArg (fun A : ScalarL2 N L→L[ℂ] ScalarL2 N L ↦ A f)
    (allowedProjection_killedTransition N L a t)
  change allowedProjection N L a (killedTransition N L a t f)=killedTransition N L a t f at he
  filter_upwards [allowedProjection_ae N L a (killedTransition N L a t f)] with X hX
  rw [he] at hX
  intro hn
  rw [hX,Set.indicator_of_notMem hn]

lemma killedTransition_add_nonneg (N : ℕ) (L : Length) (a s t : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t) :
    killedTransition N L a (s+t)=(killedTransition N L a s).comp (killedTransition N L a t) := by
  rcases hs.eq_or_lt with hs | hs
  · rw [← hs,zero_add,killedTransition_zero,allowedProjection_killedTransition]
  rcases ht.eq_or_lt with ht | ht
  · rw [← ht,add_zero,killedTransition_zero,killedTransition_allowedProjection]
  exact killedTransition_add N L a s t hs ht

end HardSphere

namespace HardSphere

lemma exists_bounded_lift_of_tendsto {E F ι : Type*}
    [NormedAddCommGroup E] [NormedAddCommGroup F]
    [InnerProductSpace ℂ E] [InnerProductSpace ℂ F]
    [CompleteSpace E] [CompleteSpace F]
    {l : Filter ι} [l.NeBot] (A : E →L[ℂ] F) (f : ι → E)
    {C : ℝ} (hb : ∀ i, ‖f i‖≤C) {u : F}
    (hu : Tendsto (fun i ↦ A (f i)) l (𝓝 u)) :
    ∃ x : E, ‖x‖≤C ∧ A x=u := by
  let φ : ι → WeakDual ℂ E := fun i ↦ (InnerProductSpace.toDual ℂ E (f i)).toWeakDual
  have hφ : ∀ i, φ i∈WeakDual.toStrongDual ⁻¹' Metric.closedBall 0 C := by
    intro i
    simpa only [Set.mem_preimage,Metric.mem_closedBall,dist_zero_right,φ,
      StrongDual.toStrongDual_toWeakDual,(InnerProductSpace.toDual ℂ E).norm_map] using hb i
  obtain ⟨ψ,hψ,hcluster⟩ := (WeakDual.isCompact_closedBall (0 : StrongDual ℂ E) C).exists_mapClusterPt
    (show Filter.map φ l≤𝓟 (WeakDual.toStrongDual ⁻¹' Metric.closedBall 0 C) from
      Filter.le_principal_iff.mpr (Filter.eventually_map.mpr (Eventually.of_forall hφ)))
  let x : E := (InnerProductSpace.toDual ℂ E).symm ψ.toStrongDual
  refine ⟨x,?_,?_⟩
  · change ‖(InnerProductSpace.toDual ℂ E).symm ψ.toStrongDual‖≤C
    simpa only [Set.mem_preimage,Metric.mem_closedBall,dist_zero_right,
      (InnerProductSpace.toDual ℂ E).symm.norm_map] using hψ
  · apply ext_inner_right ℂ
    intro v
    have hv : Tendsto (fun d : WeakDual ℂ E ↦ d (A.adjoint v))
        (Filter.map φ l) (𝓝 (inner ℂ u v)) := by
      rw [tendsto_map'_iff]
      have h := hu.inner (𝕜 := ℂ) (tendsto_const_nhds (x := v))
      simpa only [Function.comp_def,φ,StrongDual.toWeakDual_apply,
        InnerProductSpace.toDual_apply_apply,ContinuousLinearMap.adjoint_inner_right] using h
    have hct := hcluster.map (WeakDual.eval_continuous (A.adjoint v)).continuousAt hv
    have he : ψ (A.adjoint v)=inner ℂ u v := by
      exact eq_of_nhds_neBot hct
    simpa only [x,← WeakDual.toStrongDual_apply,← InnerProductSpace.toDual_symm_apply,
      ContinuousLinearMap.adjoint_inner_right] using he

end HardSphere

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_GraphLiftHeatBound
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
open ContinuousLinearMap Filter
open scoped Topology
variable {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
  [InnerProductSpace ℂ E] [InnerProductSpace ℂ F] [CompleteSpace E] [CompleteSpace F] [Nontrivial F]

attribute [local instance] OAI.HardSphere.graphLiftHeatBoundRealAlgebra
lemma exists_graph_lift_of_heat_bound (A : E →L[ℂ] F) (hA : ‖A‖≤1)
    (hdense : DenseRange (A.comp A.adjoint)) (u : F) (C : ℝ)
    (hb : ∀ n : ℕ, (1 / ((n:ℝ)+1))⁻¹ *
      (‖u‖^2-(inner ℂ u ((cfc (p := IsSelfAdjoint) (heatScalar (1/((n:ℝ)+1)))
        (A.comp A.adjoint)) u)).re) ≤ C) :
    ∃ v : E, A v=u ∧ ‖v‖^2≤‖u‖^2+C := by
  let d : ℕ→ℝ := fun n ↦ 1/((n:ℝ)+1)
  have hd (n : ℕ) : 0<d n := by dsimp [d]; positivity
  let R := A.comp A.adjoint
  let v : ℕ→E := fun n ↦ A.adjoint ((cfc (p := IsSelfAdjoint) (regularizationWeight (d n)) R) u)
  have hv (n : ℕ) : ‖v n‖^2≤‖u‖^2+C :=
    (regularized_lift_norm_sq A hA (hd n) u).trans (add_le_add_right (hb n) _)
  have hB : 0≤‖u‖^2+C := (sq_nonneg ‖v 0‖).trans (hv 0)
  have hRp : R.IsPositive := by simpa [R] using isPositive_adjoint_comp_self A.adjoint
  have hRn : ‖R‖≤1 := (opNorm_comp_le _ _).trans (by rw [adjoint.norm_map]; nlinarith [norm_nonneg A])
  have ht : Tendsto (fun n ↦ A (v n)) atTop (𝓝 u) := by
    have hh := regularizationOperator_tendsto hd tendsto_one_div_add_atTop_nhds_zero_nat hRp hRn hdense u
    convert hh using 1
    all_goals try with_reducible_and_instances rfl
    funext n
    rw [regularizationOperator_eq hRp hRn (hd n)]
    rfl
  obtain ⟨w,hw,hwu⟩ := exists_bounded_lift_of_tendsto A v
    (C := Real.sqrt (‖u‖^2+C)) (fun n ↦ (Real.le_sqrt (norm_nonneg _) hB).mpr (hv n)) ht
  refine ⟨w,hwu,?_⟩
  calc
    ‖w‖^2 ≤ (Real.sqrt (‖u‖^2+C))^2 := pow_le_pow_left₀ (norm_nonneg _) hw 2
    _ = _ := Real.sq_sqrt hB

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

lemma free_graph_lift_of_heat_bound (N : ℕ) (L : Length) (a : ℝ) (ha : a<0)
    (u : ScalarL2 N L) (C : ℝ)
    (hb : ∀ n : ℕ, (1/((n:ℝ)+1))⁻¹ *
      (‖u‖^2-(inner ℂ u (freeTransition N L (1/((n:ℝ)+1)) u)).re)≤C) :
    ∃ v : hilbertDomain N L a, scalarEmbedding N L a v=u ∧ ‖v‖^2≤‖u‖^2+C := by
  rcases subsingleton_or_nontrivial (ScalarL2 N L) with h | h
  · have := h
    refine ⟨0,Subsingleton.elim _ _,?_⟩
    have hz : u=0 := Subsingleton.elim _ _
    simpa [hz] using hb 0
  have := h
  apply exists_graph_lift_of_heat_bound (scalarEmbedding N L a) (scalarEmbedding_norm_le N L a)
    (freeResolvent_denseRange N L a ha) u C
  intro n
  have ht : 0<1/((n:ℝ)+1) := by positivity
  simpa only [formHeat,formResolvent] using
    (show (1/((n:ℝ)+1))⁻¹ * (‖u‖^2-(inner ℂ u
      (formHeat N L a (1/((n:ℝ)+1)) u)).re)≤C by
        rw [← freeTransition_eq_formHeat N L a ha ht]
        exact hb n)

end HardSphere

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Comparison_KilledLaplace
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
open MeasureTheory Set Filter
open scoped Topology

lemma killedTransition_clamped_continuous (N : ℕ) (L : Length) (a : ℝ) (f : ScalarL2 N L) :
    Continuous (fun t : ℝ ↦ killedTransition N L a (max 0 t) f) :=
  semigroup_clamped_continuous (killedTransition N L a) (killedTransition_add_nonneg N L a)
    (fun t _ ↦ killedTransition_apply_contraction N L a t) (killedTransition_tendsto_zero N L a) f

lemma killedLaplace_norm_le (N : ℕ) (L : Length) (a : ℝ) (f : ScalarL2 N L) :
    ‖killedLaplace N L a f‖≤‖f‖ :=
  semigroupLaplace_norm_le (killedTransition N L a) (killedTransition_clamped_continuous N L a)
    (fun t _ ↦ killedTransition_apply_contraction N L a t) f

lemma killedLaplace_norm_sub_le (N : ℕ) (L : Length) (a : ℝ) (f : ScalarL2 N L)
    {h : ℝ} (hh : 0 ≤ h) (hh1 : h ≤ 1) :
    ‖killedLaplace N L a f-killedTransition N L a h (killedLaplace N L a f)‖≤
      (2*Real.exp 1)*h*‖f‖ :=
  semigroupLaplace_norm_sub_le (killedTransition N L a) (killedTransition_add_nonneg N L a)
    (killedTransition_clamped_continuous N L a)
    (fun t _ ↦ killedTransition_apply_contraction N L a t) f hh hh1

lemma killedLaplace_support (N : ℕ) (L : Length) (a : ℝ) (f : ScalarL2 N L) :
    ∀ᵐ X ∂(volume : Measure (Configuration N L)), X∉allowed N L a → killedLaplace N L a f X=0 := by
  have he := semigroupLaplace_project (killedTransition N L a) (killedTransition_add_nonneg N L a)
    (killedTransition_clamped_continuous N L a)
    (fun t _ ↦ killedTransition_apply_contraction N L a t) f
  simpa only [killedLaplace,he] using killedTransition_support N L a 0 (killedLaplace N L a f)

lemma killedLaplace_free_energy_bound (N : ℕ) (L : Length) (a : ℝ) (f : ScalarL2 N L)
    {h : ℝ} (hh : 0 < h) (hh1 : h ≤ 1) :
    h⁻¹ * (‖killedLaplace N L a f‖^2-(inner ℂ (killedLaplace N L a f)
      (freeTransition N L h (killedLaplace N L a f))).re)≤4*Real.exp 1*‖f‖^2 := by
  let u := killedLaplace N L a f
  have hb := free_deficit_le_twice_killed N L a h u
  have hi : ‖u‖^2-(inner ℂ u (killedTransition N L a h u)).re≤
      ‖u‖*‖u-killedTransition N L a h u‖ := by
    have hinner := re_inner_le_norm (𝕜 := ℂ) u (u-killedTransition N L a h u)
    change (inner ℂ u (u-killedTransition N L a h u)).re≤_ at hinner
    rw [inner_sub_right,Complex.sub_re] at hinner
    have he : (inner ℂ u u).re=‖u‖^2 := (norm_sq_eq_re_inner (𝕜 := ℂ) u).symm
    rw [he] at hinner
    exact hinner
  have hc := mul_le_mul (killedLaplace_norm_le N L a f)
    (killedLaplace_norm_sub_le N L a f hh.le hh1)
    (norm_nonneg _) (norm_nonneg _)
  have hd : ‖u‖^2-(inner ℂ u (freeTransition N L h u)).re≤
      4*Real.exp 1*h*‖f‖^2 := by
    nlinarith [hb,hi,hc]
  have hm := mul_le_mul_of_nonneg_left hd (inv_nonneg.mpr hh.le)
  calc
    _ ≤ h⁻¹*(4*Real.exp 1*h*‖f‖^2) := hm
    _ = _ := by field_simp

lemma killedLaplace_free_graph (N : ℕ) (L : Length) (a : ℝ) (f : ScalarL2 N L) :
    ∃ v : hilbertDomain N L (-1), scalarEmbedding N L (-1) v=killedLaplace N L a f ∧
      ‖v‖^2≤‖killedLaplace N L a f‖^2+4*Real.exp 1*‖f‖^2 := by
  apply free_graph_lift_of_heat_bound N L (-1) (by norm_num)
  intro n
  apply killedLaplace_free_energy_bound N L a f
  · positivity
  · apply (div_le_one (by positivity : (0:ℝ)<(n:ℝ)+1)).mpr
    linarith [Nat.cast_nonneg (α := ℝ) n]

end HardSphere

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
-- module Solutions.OAIQ054_HS.HardSphere_Cutoffs_SmoothCutoff
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
open scoped Topology

lemma exists_smooth_cutoff (N : ℕ) (L : Length) {K U : Set (Configuration N L)}
    (hK : IsClosed K) (hU : IsOpen U) (hKU : K⊆U) :
    ∃ f : SmoothMultiplier N L, Set.EqOn f.toFun 1 K ∧ tsupport f.toFun⊆U := by
  obtain ⟨c,hc0,hc1,_⟩ := exists_continuous_zero_one_of_isClosed hU.isClosed_compl hK
    (Set.disjoint_left.mpr (fun X hX hKX ↦ hX (hKU hKX)))
  let C : C(Configuration N L,ℂ) := ⟨fun X ↦ (c X:ℂ),Complex.continuous_ofReal.comp c.continuous⟩
  obtain ⟨g,hg⟩ := (smoothAlgebra_dense N L).denseRange_val.exists_dist_lt C
    (show (0:ℝ)<1/8 by norm_num)
  have hclose (X : Configuration N L) : |(g.val X).re-c X|<1/8 := by
    have he := (ContinuousMap.dist_apply_le_dist (f := g.val) (g := C) X).trans_lt
      (show dist g.val C<1/8 from by rwa [dist_comm])
    have hh := (Complex.abs_re_le_norm (g.val X-C X)).trans_lt
      (show ‖g.val X-C X‖<1/8 from by simpa only [dist_eq_norm] using he)
    simpa only [Complex.sub_re,Complex.ofReal_re,C,ContinuousMap.coe_mk] using hh
  have hgSmooth : ContDiff ℝ ((⊤:ℕ∞):WithTop ℕ∞)
      (fun X : LiftedConfiguration N ↦ g.val (project N L X)) := g.property
  let f : Configuration N L→ℂ := fun X ↦ (Real.smoothTransition (2*(g.val X).re-1/2):ℂ)
  have hs : ContDiff ℝ ((⊤:ℕ∞):WithTop ℕ∞) (fun X : LiftedConfiguration N ↦ f (project N L X)) :=
    Complex.ofRealCLM.contDiff.comp (Real.smoothTransition.contDiff.comp
      ((contDiff_const.mul (Complex.reCLM.contDiff.comp hgSmooth)).sub contDiff_const))
  let m : SmoothMultiplier N L := {
    toFun := f
    smooth := hs
    memLp_top := (continuous_of_continuous_lift hs.continuous).memLp_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
    partial_memLp_top := fun p ↦ (continuous_coordDerivative hs p).memLp_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _) }
  refine ⟨m,?_,?_⟩
  · intro X hX
    have hx := hclose X
    have hc : c X=1 := hc1 hX
    have hl : 1≤2*(g.val X).re-1/2 := by rw [hc] at hx; linarith [(abs_lt.mp hx).1]
    change (Real.smoothTransition (2*(g.val X).re-1/2):ℂ)=1
    rw [Real.smoothTransition.one_of_one_le hl,Complex.ofReal_one]
  · have hc : tsupport f⊆{X | 1/4≤(g.val X).re} := by
      apply closure_minimal ?_ (isClosed_le continuous_const (Complex.continuous_re.comp g.val.continuous))
      intro X hX
      by_contra h
      change ¬1/4≤(g.val X).re at h
      have hz : f X=0 := by
        dsimp [f]
        rw [Real.smoothTransition.zero_of_nonpos (by linarith [not_le.mp h]),Complex.ofReal_zero]
      exact hX hz
    intro X hX
    have hh := hc hX
    change 1/4≤(g.val X).re at hh
    by_contra hn
    have hc : c X=0 := hc0 hn
    have hh' := hclose X
    rw [hc,sub_zero] at hh'
    linarith [(abs_lt.mp hh').2]

end HardSphere

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_FormDomain_DirichletScalarInjective
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

lemma dirichlet_scalar_injective {N : ℕ} {L : Length} {a : ℝ} {u v : Jet N L}
    (hu : u∈dirichletDomain N L a) (hv : v∈dirichletDomain N L a) (he : u.1=v.1) : u=v := by
  have hz := derivative_zero_of_scalar_zero
    (show u-v∈dirichletDomain N L a from (dirichletSubmodule N L a).sub_mem hu hv)
    (show (u-v).1=0 by simp only [Prod.fst_sub,he,sub_self])
  apply Prod.ext he
  apply sub_eq_zero.mp
  exact hz

lemma SmoothMultiplier.onJet_mem_domain_of_support {N : ℕ} {L : Length} {a b : ℝ}
    (f : SmoothMultiplier N L) (hf : tsupport f.toFun⊆allowed N L a)
    {u : Jet N L} (hu : u∈dirichletDomain N L b) : f.onJet u∈dirichletDomain N L a := by
  apply map_mem_closure f.onJet.continuous hu
  rintro _ ⟨g,rfl⟩
  let h : SmoothTest N L a := {g.multiply f with
    support_allowed := tsupport_mul_subset_left.trans hf }
  exact ⟨h,g.jet_multiply f⟩

lemma dirichletDomain_of_closed_support {N : ℕ} {L : Length} {a b : ℝ}
    (hΩ : IsOpen (allowed N L a)) {K : Set (Configuration N L)}
    (hK : IsClosed K) (hKΩ : K⊆allowed N L a) {u : Jet N L}
    (hu : u∈dirichletDomain N L b)
    (hz : ∀ᵐ X ∂(volume : Measure (Configuration N L)), X∉K → u.1 X=0) :
    u∈dirichletDomain N L a := by
  obtain ⟨f,hf1,hfs⟩ := exists_smooth_cutoff N L hK hΩ hKΩ
  have he : (f.onJet u).1=u.1 := by
    apply Lp.ext
    filter_upwards [L2Multiplier.coe_clm f.toFun f.memLp_top u.1,hz] with X hc hz
    change (f.onScalar u.1) X=u.1 X
    rw [SmoothMultiplier.onScalar,hc]
    by_cases h : X∈K
    · rw [hf1 h,Pi.one_apply,one_mul]
    · rw [hz h,mul_zero]
  have heq := dirichlet_scalar_injective (f.onJet_mem_domain hu) hu he
  rw [← heq]
  exact f.onJet_mem_domain_of_support hfs hu

end HardSphere

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_NormSqIntegral
attribute [-instance] _root_.OAI.HardSphere.Bridge.exposedBridgeKernel_markov _root_.OAI.HardSphere.Bridge.exposedPeriodSingle_finite _root_.OAI.HardSphere.Bridge.exposedTrialKernel_markov _root_.OAI.HardSphere.Bridge.instBorelSpaceContinuousMapElemRealTimePoint _root_.OAI.HardSphere.Bridge.instIsProbabilityMeasureNoiseLaw _root_.OAI.HardSphere.Bridge.instMeasurableSpaceContinuousMapElemRealTimePoint _root_.OAI.HardSphere.Bridge.parameterBridgeKernel_markov _root_.OAI.HardSphere.Bridge.parameterIndividualReference_finite _root_.OAI.HardSphere.Bridge.parameterTrialKernel_markov _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Bridge.trialKernel_markov _root_.OAI.HardSphere.Groups.cellPathReference_probability _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Rescaling.config_haar _root_.OAI.HardSphere.Wiener.instIsProbabilityMeasureContinuousMapElemRealTimeBridgeLaw _root_.OAI.HardSphere.bridgeEndpointBase_finite _root_.OAI.HardSphere.coordinateBridge_probability _root_.OAI.HardSphere.endpointWeightedBase_sfinite _root_.OAI.HardSphere.freePathLaw_finite_deletion _root_.OAI.HardSphere.killedPathLaw_finite_deletion
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

lemma tendsto_L2_of_norm_dominated {F : ℕ → Lp ℂ 2 μ} {f : Lp ℂ 2 μ}
    (b : α → ℝ) (hb : Integrable b μ)
    (hbound : ∀ n, ∀ᵐ x ∂μ, ‖(F n - f) x‖^2 ≤ b x)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun n ↦ (F n - f) x) atTop (𝓝 0)) :
    Tendsto F atTop (𝓝 f) := by
  have hs : Tendsto (fun n ↦ ‖F n - f‖^2) atTop (𝓝 0) := by
    simp_rw [norm_sq_integral]
    have hi := tendsto_integral_of_dominated_convergence b
      (fun n ↦ (show AEStronglyMeasurable (fun x ↦ ‖(F n - f) x‖^2) μ from (Lp.aestronglyMeasurable (F n - f)).norm.pow 2)) hb
      (fun n ↦ (hbound n).mono fun x hx ↦ by simpa only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (‖(F n - f) x‖))] using hx)
      (hlim.mono fun x hx ↦ by simpa using hx.norm.pow 2)
    simpa using hi
  have hn : Tendsto (fun n ↦ ‖F n - f‖) atTop (𝓝 0) := by
    simpa only [Function.comp_def, Real.sqrt_sq_eq_abs, abs_norm, Real.sqrt_zero] using
      Real.continuous_sqrt.continuousAt.tendsto.comp hs
  exact tendsto_iff_norm_sub_tendsto_zero.mpr hn

lemma indicator_tendsto {S : ℕ → Set α} (hS : ∀ n, MeasurableSet (S n))
    (hmono : Monotone S) (f : Lp ℂ 2 μ) :
    Tendsto (fun n ↦ ((Lp.memLp f).indicator (hS n)).toLp ((S n).indicator f))
      atTop (𝓝 (((Lp.memLp f).indicator (MeasurableSet.iUnion hS)).toLp ((⋃ n, S n).indicator f))) := by
  let F n := ((Lp.memLp f).indicator (hS n)).toLp ((S n).indicator f)
  let g := ((Lp.memLp f).indicator (MeasurableSet.iUnion hS)).toLp ((⋃ n, S n).indicator f)
  have hF n : F n =ᵐ[μ] (S n).indicator f := MemLp.coeFn_toLp _
  have hg : g =ᵐ[μ] (⋃ n, S n).indicator f := MemLp.coeFn_toLp _
  apply tendsto_L2_of_norm_dominated (fun x ↦ ‖f x‖^2)
    ((Lp.memLp f).integrable_norm_pow (by norm_num))
  · intro n
    filter_upwards [Lp.coeFn_sub (F n) g, hF n, hg] with x hx hfx hgx
    rw [hx, Pi.sub_apply, hfx, hgx]
    by_cases hn : x ∈ S n
    · have hu : x ∈ ⋃ n, S n := mem_iUnion.mpr ⟨n,hn⟩
      simp [hn,hu]
    · by_cases hu : x ∈ ⋃ n, S n <;> simp [hn,hu]
  · filter_upwards [ae_all_iff.mpr (fun n ↦ Lp.coeFn_sub (F n) g), ae_all_iff.mpr hF, hg]
      with x hx hfx hgx
    have heq n : (F n - g) x = (S n).indicator f x - (⋃ n, S n).indicator f x := by
      rw [hx n,Pi.sub_apply,hfx n,hgx]
    change Tendsto (fun n ↦ (F n - g) x) atTop (𝓝 (0:ℂ))
    simp_rw [heq]
    by_cases hu : x ∈ ⋃ n, S n
    · obtain ⟨n,hn⟩ := mem_iUnion.mp hu
      apply tendsto_const_nhds.congr'
      filter_upwards [eventually_ge_atTop n] with m hm
      simp [hmono hm hn, hu]
    · simpa only [Set.indicator_of_notMem hu, sub_zero] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (0:ℂ)) atTop (𝓝 0)).congr'
          (Filter.Eventually.of_forall fun n ↦ by
            rw [Set.indicator_of_notMem (fun h ↦ hu (mem_iUnion.mpr ⟨n,h⟩))])

end IndicatorStrong

namespace HardSphere
open Wiener

lemma avoidanceMultiplier_innerRadius_tendsto (N : ℕ) (L : Length) (a t : ℝ)
    (f : FreePathL2 N L t) :
    Tendsto (fun n ↦ avoidanceMultiplier N L (innerRadius a n) t f) atTop
      (𝓝 (avoidanceMultiplier N L a t f)) := by
  have h := IndicatorStrong.indicator_tendsto
    (fun n ↦ (staysAllowed_open N L (innerRadius a n)).measurableSet)
    (fun m n hmn ↦ staysAllowed_antitone N L (innerRadius_antitone a hmn)) f
  simp only [staysAllowed_innerRadius] at h
  have heq (b : ℝ) : avoidanceMultiplier N L b t f =
      ((Lp.memLp f).indicator (staysAllowed_open N L b).measurableSet).toLp
        ((staysAllowed N L b).indicator f) := by
    apply Lp.ext
    exact (avoidanceMultiplier_ae N L b t f).trans (MemLp.coeFn_toLp _).symm
  simp_rw [← heq] at h
  exact h

lemma killedTransition_innerRadius_tendsto (N : ℕ) (L : Length) (a t : ℝ)
    (f : ScalarL2 N L) :
    Tendsto (fun n ↦ killedTransition N L (innerRadius a n) t f) atTop
      (𝓝 (killedTransition N L a t f)) := by
  exact ((endpointPull N L t 0).toContinuousLinearMap.adjoint.continuous.tendsto _).comp
    (avoidanceMultiplier_innerRadius_tendsto N L a t (endpointPull N L t 1 f))

end HardSphere

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_BufferedAllowed
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
open MeasureTheory Set Filter
open scoped Topology

lemma killedLaplace_innerRadius_tendsto (N : ℕ) (L : Length) (a : ℝ) (f : ScalarL2 N L) :
    Tendsto (fun n ↦ killedLaplace N L (innerRadius a n) f) atTop (𝓝 (killedLaplace N L a f)) := by
  apply tendsto_integral_of_dominated_convergence (fun t : ℝ ↦ Real.exp (-t)*‖f‖)
  · intro n
    exact (laplaceIntegrand_integrable (killedTransition N L (innerRadius a n))
      (killedTransition_clamped_continuous N L (innerRadius a n))
      (fun t _ ↦ killedTransition_apply_contraction N L (innerRadius a n) t) f 0).aestronglyMeasurable
  · exact (integrableOn_exp_neg_Ioi 0).mul_const ‖f‖
  · intro n
    apply Eventually.of_forall
    intro t
    rw [laplaceIntegrand_eq_complex]
    rw [norm_smul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
    exact mul_le_mul_of_nonneg_left (killedTransition_apply_contraction N L (innerRadius a n) _ f)
      (Real.exp_nonneg _)
  · apply Eventually.of_forall
    intro t
    simp_rw [laplaceIntegrand_eq_complex]
    exact tendsto_const_nhds.smul (killedTransition_innerRadius_tendsto N L a (max 0 t) f)

lemma bufferedAllowed_closed (N : ℕ) (L : Length) (b : ℝ) : IsClosed (bufferedAllowed N L b) := by
  let P := {p : Fin N × Fin N // p.1 < p.2}
  have he : bufferedAllowed N L b = ⋂ p : P,
      {X : Configuration N L | b≤torusDistance L (X p.1.1) (X p.1.2)} := by
    ext X
    simp only [bufferedAllowed,mem_ofPred_eq,mem_iInter]
    exact ⟨fun h p ↦ h _ _ p.2,fun h i j hij ↦ h ⟨(i,j),hij⟩⟩
  rw [he]
  apply isClosed_iInter
  intro p
  have hc : Continuous (fun X : Configuration N L ↦ torusDistance L (X p.1.1) (X p.1.2)) := by
    unfold torusDistance
    fun_prop
  exact isClosed_le continuous_const hc

lemma allowed_subset_buffered (N : ℕ) (L : Length) (b : ℝ) :
    allowed N L b⊆bufferedAllowed N L b := fun _ h i j hij ↦ (h i j hij).le

lemma bufferedAllowed_subset (N : ℕ) (L : Length) {a b : ℝ} (hab : a<b) :
    bufferedAllowed N L b⊆allowed N L a := fun _ h i j hij ↦ hab.trans_le (h i j hij)

lemma killedLaplace_buffered_graph (N : ℕ) (L : Length) {a b : ℝ} (hab : a<b) (f : ScalarL2 N L) :
    ∃ v : hilbertDomain N L a, scalarEmbedding N L a v=killedLaplace N L b f ∧
      ‖v‖^2≤(1+4*Real.exp 1)*‖f‖^2 := by
  obtain ⟨u,hu,hub⟩ := killedLaplace_free_graph N L b f
  have hj : hilbertJetEquiv N L (u : HilbertJet N L)∈dirichletDomain N L a := by
    apply dirichletDomain_of_closed_support (isOpen_allowed N L a)
      (bufferedAllowed_closed N L b) (bufferedAllowed_subset N L hab) u.property
    have he : (hilbertJetEquiv N L (u : HilbertJet N L)).1=killedLaplace N L b f := hu
    change ∀ᵐ X ∂(volume : Measure (Configuration N L)), X∉bufferedAllowed N L b →
      (hilbertJetEquiv N L (u : HilbertJet N L)).1 X=0
    rw [he]
    filter_upwards [killedLaplace_support N L b f] with X hX
    intro hn
    exact hX (fun ha ↦ hn (allowed_subset_buffered N L b ha))
  let v : hilbertDomain N L a := ⟨u.val,hj⟩
  refine ⟨v,hu,?_⟩
  have hn := killedLaplace_norm_le N L b f
  change ‖u‖^2≤_
  nlinarith [norm_nonneg (killedLaplace N L b f),norm_nonneg f]

lemma killedLaplace_graph_oai (N : ℕ) (L : Length) (a : ℝ) (f : ScalarL2 N L) :
    ∃ v : hilbertDomain N L a, scalarEmbedding N L a v=killedLaplace N L a f ∧
      ‖v‖^2≤(1+4*Real.exp 1)*‖f‖^2 := by
  choose v hv hb using fun n ↦ killedLaplace_buffered_graph N L (innerRadius_gt a n) f
  let C := (1+4*Real.exp 1)*‖f‖^2
  have hC : 0≤C := by dsimp [C]; positivity
  have hvb : ∀ n, ‖v n‖≤Real.sqrt C := by
    intro n
    exact (Real.le_sqrt (norm_nonneg _) hC).mpr (hb n)
  have ht : Tendsto (fun n ↦ scalarEmbedding N L a (v n)) atTop (𝓝 (killedLaplace N L a f)) := by
    simp_rw [hv]
    exact killedLaplace_innerRadius_tendsto N L a f
  obtain ⟨u,hub,hu⟩ := exists_bounded_lift_of_tendsto (scalarEmbedding N L a) v hvb ht
  refine ⟨u,hu,?_⟩
  calc
    ‖u‖^2 ≤ (Real.sqrt C)^2 := sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _) |>.mpr hub
    _ = C := Real.sq_sqrt hC

end HardSphere

open ProbabilityTheory

end

end OAI
end

theorem solution : type_of% @OAI.HardSphere.killedLaplace_graph_oai := @OAI.HardSphere.killedLaplace_graph_oai
