-- Prove2me | solution 1 for GittinsUCB.Patient.explore_then_commit
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T08:00:17.491837+00:00
-- url     : https://prove2.me/submissions/c1f31529-4640-4bbd-9aba-48ad5671cf14

import Mathlib
import Definitions.Def_GittinsUCB_Patient_Model
open MeasureTheory ProbabilityTheory Filter Asymptotics NNReal
open GittinsUCB.Patient

namespace GittinsETCAux

instance (μ : ℝ) (σ2 σW2 : ℝ≥0) : IsProbabilityMeasure (model μ σ2 σW2) := by
  unfold model; infer_instance

lemma integrable_gauss_id : Integrable (fun x : ℝ => x) (gaussianReal 0 1) :=
  (memLp_id_gaussianReal 1).integrable le_rfl

lemma integrable_theta (σW2 : ℝ≥0) : Integrable (θ : Ω → ℝ) (model 0 1 σW2) := by
  unfold model θ
  exact integrable_gauss_id.comp_fst _

lemma measurable_R (t : ℕ) : Measurable (R t) :=
  measurable_fst.add ((measurable_pi_apply t).comp measurable_snd)

lemma rewardSigma_le (t : ℕ) : rewardSigma t ≤ (inferInstance : MeasurableSpace Ω) := by
  unfold rewardSigma
  apply Measurable.comap_le
  exact measurable_pi_lambda _ (fun s => measurable_R s)

lemma measurableSet_ge {τ : Ω → ℕ∞} (hτ : IsRetirementTime τ) (t : ℕ) :
    MeasurableSet {ω | (t : ℕ∞) ≤ τ ω} := by
  cases t with
  | zero => simp
  | succ n =>
    have h : {ω | ((n + 1 : ℕ) : ℕ∞) ≤ τ ω} = {ω | τ ω ≤ (n : ℕ∞)}ᶜ := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_compl_iff, not_le, Nat.cast_add, Nat.cast_one]
      exact ENat.add_one_le_iff (ENat.coe_ne_top n)
    rw [h]
    exact (rewardSigma_le n _ (hτ.1 n)).compl

/-- Pointwise facts about the stopped reward with constant reward `θ`. -/
lemma summand_bound (γ lam : ℝ) (hγ0 : 0 < γ) (τ : Ω → ℕ∞) (ω : Ω) (t : ℕ) :
    ‖(if (t : ℕ∞) ≤ τ ω then γ ^ t * (θ ω - lam) else 0)‖ ≤ γ ^ t * |θ ω - lam| := by
  split_ifs
  · rw [Real.norm_eq_abs, abs_mul, abs_of_pos (pow_pos hγ0 t)]
  · simp; positivity

lemma summable_summand (γ lam : ℝ) (hγ0 : 0 < γ) (hγ1 : γ < 1) (τ : Ω → ℕ∞) (ω : Ω) :
    Summable (fun t : ℕ => if (t : ℕ∞) ≤ τ ω then γ ^ t * (θ ω - lam) else 0) :=
  Summable.of_norm_bounded ((summable_geometric_of_lt_one hγ0.le hγ1).mul_right _)
    (summand_bound γ lam hγ0 τ ω)

lemma stoppedReward_le (γ lam : ℝ) (hγ0 : 0 < γ) (hγ1 : γ < 1) (τ : Ω → ℕ∞) (ω : Ω) :
    stoppedReward γ lam (fun _ => θ) τ ω ≤
      (θ ω - lam) + γ / (1 - γ) * max (θ ω - lam) 0 := by
  unfold stoppedReward
  have hs := summable_summand γ lam hγ0 hγ1 τ ω
  rw [hs.tsum_eq_zero_add]
  have h0 : (if ((0 : ℕ) : ℕ∞) ≤ τ ω then γ ^ 0 * (θ ω - lam) else 0) = θ ω - lam := by
    simp
  rw [h0]
  have hgeo : Summable (fun n : ℕ => γ * max (θ ω - lam) 0 * γ ^ n) :=
    (summable_geometric_of_lt_one hγ0.le hγ1).mul_left _
  have hle : (∑' n : ℕ, (if ((n + 1 : ℕ) : ℕ∞) ≤ τ ω then γ ^ (n + 1) * (θ ω - lam) else 0)) ≤
      ∑' n : ℕ, γ * max (θ ω - lam) 0 * γ ^ n := by
    refine Summable.tsum_mono ((_root_.summable_nat_add_iff 1).mpr hs) hgeo (fun n => ?_)
    have hp : 0 < γ ^ (n + 1) := pow_pos hγ0 _
    split_ifs
    · rw [pow_succ]
      have := le_max_left (θ ω - lam) 0
      have h2 : γ ^ n * γ * (θ ω - lam) ≤ γ ^ n * γ * max (θ ω - lam) 0 :=
        mul_le_mul_of_nonneg_left this (by positivity)
      linarith
    · have := le_max_right (θ ω - lam) 0
      positivity
  rw [_root_.tsum_mul_left, tsum_geometric_of_lt_one hγ0.le hγ1] at hle
  have e : γ * max (θ ω - lam) 0 * (1 - γ)⁻¹ = γ / (1 - γ) * max (θ ω - lam) 0 := by
    field_simp
  linarith

lemma integrable_stoppedReward (γ lam : ℝ) (hγ0 : 0 < γ) (hγ1 : γ < 1) (σW2 : ℝ≥0)
    {τ : Ω → ℕ∞} (hτ : IsRetirementTime τ) :
    Integrable (stoppedReward γ lam (fun _ => θ) τ) (model 0 1 σW2) := by
  have hθ : Measurable (θ : Ω → ℝ) := measurable_fst
  have hmeas_t : ∀ t : ℕ, Measurable
      (fun ω : Ω => if (t : ℕ∞) ≤ τ ω then γ ^ t * (θ ω - lam) else 0) := by
    intro t
    exact Measurable.ite (measurableSet_ge hτ t) (measurable_const.mul (hθ.sub_const _))
      measurable_const
  have hmeas : Measurable (stoppedReward γ lam (fun _ => θ) τ) := by
    unfold stoppedReward
    refine measurable_of_tendsto_metrizable (fun n => Finset.measurable_sum (Finset.range n)
      (fun t _ => hmeas_t t)) ?_
    rw [tendsto_pi_nhds]
    intro ω
    exact (summable_summand γ lam hγ0 hγ1 τ ω).hasSum.tendsto_sum_nat
  have hθint : Integrable (θ : Ω → ℝ) (model 0 1 σW2) := integrable_theta σW2
  refine Integrable.mono' ((hθint.sub (integrable_const lam)).abs.mul_const (1 - γ)⁻¹)
    hmeas.aestronglyMeasurable (Eventually.of_forall fun ω => ?_)
  unfold stoppedReward
  have hg : HasSum (fun t : ℕ => γ ^ t * |θ ω - lam|) (|θ ω - lam| * (1 - γ)⁻¹) := by
    have := (hasSum_geometric_of_lt_one hγ0.le hγ1).mul_right (|θ ω - lam|)
    simpa [mul_comm] using this
  exact tsum_of_norm_bounded hg (summand_bound γ lam hγ0 τ ω)

/-- Closed form of the posterior-mean recursion. -/
lemma postMean_closed (μ0 s : ℝ) (hs : 0 < s) (t : ℕ) (ω : Ω) :
    postMean μ0 1 s t ω = postVar 1 s t * (μ0 + (∑ i ∈ Finset.range t, R i ω) / s) := by
  induction t with
  | zero => simp [postMean, postVar]
  | succ n ih =>
    have hv : 0 < 1 / (1 : ℝ) + (n : ℝ) / s := by positivity
    have hv' : 0 < 1 / (1 : ℝ) + ((n + 1 : ℕ) : ℝ) / s := by positivity
    simp only [postMean, ih, Finset.sum_range_succ]
    simp only [postVar] at hv hv' ⊢
    field_simp
    push_cast
    ring

/-- The sum of the first `L` noises is `N(0, L σ²)`. -/
lemma law_sum (s : ℝ≥0) (L : ℕ) :
    (Measure.infinitePi (fun _ : ℕ => gaussianReal 0 s)).map
      (fun w : ℕ → ℝ => ∑ i ∈ Finset.range L, w i) = gaussianReal 0 ((L : ℝ≥0) * s) := by
  induction L with
  | zero =>
    simp [gaussianReal_zero_var]
  | succ n ih =>
    have hind : iIndepFun (fun (i : ℕ) (w : ℕ → ℝ) => w i)
        (Measure.infinitePi (fun _ : ℕ => gaussianReal 0 s)) :=
      iIndepFun_infinitePi (X := fun _ (x : ℝ) => x) (fun _ => measurable_id)
    have h2 := hind.indepFun_finsetSum_of_notMem (fun i => measurable_pi_apply i)
      (Finset.notMem_range_self (n := n))
    have hX : (Measure.infinitePi (fun _ : ℕ => gaussianReal 0 s)).map (fun w : ℕ → ℝ => w n) =
        gaussianReal 0 s := Measure.infinitePi_map_eval _ n
    have hS : (Measure.infinitePi (fun _ : ℕ => gaussianReal 0 s)).map
        (∑ i ∈ Finset.range n, fun (w : ℕ → ℝ) => w i) = gaussianReal 0 ((n : ℝ≥0) * s) := by
      rw [← ih]; congr 1; funext w; simp
    have := gaussianReal_add_gaussianReal_of_indepFun h2 hS hX
    have e : (∑ i ∈ Finset.range n, fun (w : ℕ → ℝ) => w i) + (fun w : ℕ → ℝ => w n) =
        fun w : ℕ → ℝ => ∑ i ∈ Finset.range (n + 1), w i := by
      funext w; simp [Finset.sum_range_succ]
    rw [e] at this
    rw [this]
    congr 1
    · simp
    · push_cast; ring


end GittinsETCAux

open GittinsETCAux in
theorem solution (σW2 : ℝ≥0) (hW : 0 < σW2)
    (γ lam : ℝ) (hγ0 : 0 < γ) (hγ1 : γ < 1)
    (L : ℕ) (hL : 2 ≤ L) :
    (-(∑ t ∈ Finset.range L, γ ^ t * lam) +
      γ ^ L / (1 - γ) *
        ∫ ω, max (postMean 0 1 (σW2 : ℝ) L ω - lam) 0
          ∂(model 0 1 σW2) ≤ value σW2 γ lam 0 1) ∧
    (0 ≤ lam →
      -(L : ℝ) * lam + γ ^ L / (1 - γ) *
        ∫ ω, max (postMean 0 1 (σW2 : ℝ) L ω - lam) 0
          ∂(model 0 1 σW2) ≤ value σW2 γ lam 0 1) := by
  set s : ℝ := (σW2 : ℝ) with hs
  have hs0 : 0 < s := by rw [hs]; exact_mod_cast hW
  set m : Ω → ℝ := postMean 0 1 s L with hm
  set k : ℝ := (L : ℝ) / s with hk
  have hk0 : 0 ≤ k := by positivity
  set v : ℝ := postVar 1 s L with hv
  have hvk : v = 1 / (1 + k) := by rw [hv, hk]; unfold postVar; simp
  set a : ℝ := v * k with ha
  set b : ℝ := v / s with hb
  have h1a : 1 - a = v := by rw [ha, hvk]; field_simp; ring
  set S : (ℕ → ℝ) → ℝ := fun w => ∑ i ∈ Finset.range L, w i with hSdef
  have hSm : Measurable S := Finset.measurable_sum _ (fun i _ => measurable_pi_apply i)
  have hpt : ∀ ω : Ω, m ω = a * ω.1 + b * S ω.2 := by
    intro ω
    rw [hm, postMean_closed 0 s hs0 L ω]
    have hR : ∑ i ∈ Finset.range L, R i ω = (L : ℝ) * ω.1 + S ω.2 := by
      simp [R, hSdef, Finset.sum_add_distrib]
    rw [hR, ha, hb, hk, ← hv]
    field_simp
    ring
  set P := model 0 1 σW2 with hPdef
  have hmodel : P = (gaussianReal 0 1).prod (Measure.infinitePi (fun _ : ℕ => gaussianReal 0 σW2)) := rfl
  -- Gaussian structure of `(θ, S)`
  have hlawX : P.map (fun ω : Ω => ω.1) = gaussianReal 0 1 := by
    rw [hmodel, Measure.map_fst_prod]; simp
  have hlawY : P.map (fun ω : Ω => S ω.2) = gaussianReal 0 ((L : ℝ≥0) * σW2) := by
    rw [hmodel, show (fun ω : Ω => S ω.2) = S ∘ Prod.snd from rfl,
      ← Measure.map_map hSm measurable_snd, Measure.map_snd_prod, ← law_sum σW2 L]
    simp [hSdef]
  have hX : HasGaussianLaw (fun ω : Ω => ω.1) P := ⟨by rw [hlawX]; infer_instance⟩
  have hY : HasGaussianLaw (fun ω : Ω => S ω.2) P := ⟨by rw [hlawY]; infer_instance⟩
  have hXY : IndepFun (fun ω : Ω => ω.1) (fun ω : Ω => S ω.2) P := by
    rw [hmodel]
    exact indepFun_prod (X := fun x : ℝ => x) (Y := S) measurable_id hSm
  have hjoint := IndepFun.hasGaussianLaw hX hY hXY
  set U : Ω → ℝ := fun ω => (1 - a) * ω.1 - b * S ω.2 with hU
  set V : Ω → ℝ := fun ω => a * ω.1 + b * S ω.2 with hV
  have hUV : HasGaussianLaw (fun ω => (U ω, V ω)) P := by
    let Lm : ℝ × ℝ →L[ℝ] ℝ × ℝ :=
      ((1 - a) • ContinuousLinearMap.fst ℝ ℝ ℝ - b • ContinuousLinearMap.snd ℝ ℝ ℝ).prod
        (a • ContinuousLinearMap.fst ℝ ℝ ℝ + b • ContinuousLinearMap.snd ℝ ℝ ℝ)
    have := hjoint.map_fun Lm
    have e : (fun ω => (U ω, V ω)) = (fun ω : Ω => Lm (ω.1, S ω.2)) := by
      funext ω; simp [Lm, hU, hV]
    rw [e]; exact this
  have hXm := hX.memLp_two
  have hYm := hY.memLp_two
  have hvarX : cov[fun ω : Ω => ω.1, fun ω : Ω => ω.1; P] = 1 := by
    rw [covariance_self hX.aemeasurable]
    have := variance_map (μ := P) (X := id) (Y := fun ω : Ω => ω.1) (by fun_prop) hX.aemeasurable
    rw [hlawX, variance_id_gaussianReal] at this
    simpa using this.symm
  have hvarY : cov[fun ω : Ω => S ω.2, fun ω : Ω => S ω.2; P] = (L : ℝ) * s := by
    rw [covariance_self hY.aemeasurable]
    have := variance_map (μ := P) (X := id) (Y := fun ω : Ω => S ω.2) (by fun_prop) hY.aemeasurable
    rw [hlawY, variance_id_gaussianReal] at this
    simpa using this.symm
  have hcXY : cov[fun ω : Ω => ω.1, fun ω : Ω => S ω.2; P] = 0 :=
    hXY.covariance_eq_zero hXm hYm
  have hcYX : cov[fun ω : Ω => S ω.2, fun ω : Ω => ω.1; P] = 0 := by
    rw [covariance_comm]; exact hcXY
  have hVm : MemLp V 2 P := (hXm.const_mul a).add (hYm.const_mul b)
  have hcov : cov[U, V; P] = 0 := by
    have e1 : cov[U, V; P] = (1 - a) * cov[fun ω : Ω => ω.1, V; P] -
        b * cov[fun ω : Ω => S ω.2, V; P] := by
      rw [hU, covariance_fun_sub_left (hXm.const_mul _) (hYm.const_mul _) hVm,
        covariance_const_mul_left, covariance_const_mul_left]
    have hVeq : V = (fun ω : Ω => a * ω.1) + (fun ω : Ω => b * S ω.2) := rfl
    have e2 : cov[fun ω : Ω => ω.1, V; P] = a * 1 + b * 0 := by
      rw [hVeq, covariance_add_right hXm (hXm.const_mul _) (hYm.const_mul _),
        covariance_const_mul_right, covariance_const_mul_right, hvarX, hcXY]
    have e3 : cov[fun ω : Ω => S ω.2, V; P] = a * 0 + b * ((L : ℝ) * s) := by
      rw [hVeq, covariance_add_right hYm (hXm.const_mul _) (hYm.const_mul _),
        covariance_const_mul_right, covariance_const_mul_right, hvarY, hcYX]
    rw [e1, e2, e3, h1a, ha, hb, hk]
    field_simp
    ring
  have hind : IndepFun U V P := hUV.indepFun_of_covariance_eq_zero hcov
  -- means
  have hXint : Integrable (fun ω : Ω => ω.1) P := hX.integrable
  have hYint : Integrable (fun ω : Ω => S ω.2) P := hY.integrable
  have hmeanX : ∫ ω, ω.1 ∂P = 0 := by
    have h := integral_map (μ := P) (φ := fun ω : Ω => ω.1) (f := fun x : ℝ => x)
      hX.aemeasurable aestronglyMeasurable_id
    rw [hlawX, integral_id_gaussianReal] at h
    exact h.symm
  have hmeanY : ∫ ω, S ω.2 ∂P = 0 := by
    have h := integral_map (μ := P) (φ := fun ω : Ω => S ω.2) (f := fun x : ℝ => x)
      hY.aemeasurable aestronglyMeasurable_id
    rw [hlawY, integral_id_gaussianReal] at h
    exact h.symm
  have hUint : Integrable U P := (hXint.const_mul _).sub (hYint.const_mul _)
  have hmeanU : ∫ ω, U ω ∂P = 0 := by
    rw [hU, integral_sub (hXint.const_mul _) (hYint.const_mul _), integral_const_mul,
      integral_const_mul, hmeanX, hmeanY]
    ring
  -- the indicator of commitment
  set I : Ω → ℝ := fun ω => if lam ≤ m ω then 1 else 0 with hI
  have hmmeas : Measurable m := by
    have : m = fun ω : Ω => a * ω.1 + b * S ω.2 := funext hpt
    rw [this]
    exact ((measurable_const_mul a).comp measurable_fst).add
      ((measurable_const_mul b).comp (hSm.comp measurable_snd))
  have hg : Measurable (fun x : ℝ => if lam ≤ x then (1 : ℝ) else 0) :=
    Measurable.ite measurableSet_Ici measurable_const measurable_const
  have hImeas : Measurable I := hg.comp hmmeas
  have hIf : ∀ f : Ω → ℝ, Integrable f P → Integrable (fun ω => I ω * f ω) P := by
    intro f hf
    refine Integrable.mono' hf.norm (hImeas.aestronglyMeasurable.mul hf.aestronglyMeasurable)
      (Eventually.of_forall fun ω => ?_)
    rw [hI]
    simp only
    split_ifs <;> simp
  have hVm' : V = m := by funext ω; rw [hpt]
  have hkey : ∫ ω, I ω * (θ ω - m ω) ∂P = 0 := by
    have hUeq : ∀ ω, θ ω - m ω = U ω := by
      intro ω; rw [hpt]; simp only [hU, θ]; ring
    simp_rw [hUeq]
    have hIV : I = (fun x : ℝ => if lam ≤ x then (1 : ℝ) else 0) ∘ V := by
      rw [hVm']; rfl
    have hind' : IndepFun I U P := by
      rw [hIV]
      exact (hind.comp measurable_id hg).symm
    rw [hind'.integral_fun_mul_eq_mul_integral hImeas.aestronglyMeasurable
      hUint.aestronglyMeasurable, hmeanU, mul_zero]
  -- measurability with respect to the reward filtration
  have hmeasR : ∀ t i, i < t + 1 → Measurable[rewardSigma t] (R i) := by
    intro t i hi
    unfold rewardSigma
    exact (measurable_pi_apply (⟨i, hi⟩ : Fin (t + 1))).comp
      (comap_measurable (fun ω (s : Fin (t + 1)) => R s ω))
  have hmσ : ∀ t, L ≤ t + 1 → Measurable[rewardSigma t] m := by
    intro t ht
    have : m = fun ω => postVar 1 s L * (0 + (∑ i ∈ Finset.range L, R i ω) / s) := by
      funext ω; rw [hm, postMean_closed 0 s hs0 L ω]
    rw [this]
    refine Measurable.const_mul (Measurable.const_add (Measurable.div_const ?_ _) _) _
    exact Finset.measurable_sum _ (fun i hi => hmeasR t i (by
      have := Finset.mem_range.mp hi; omega))
  -- the explore-then-commit retirement time
  set τ : Ω → ℕ∞ := fun ω => if m ω < lam then ((L - 1 : ℕ) : ℕ∞) else ⊤ with hτdef
  have hτ : IsRetirementTime τ := by
    refine ⟨fun t => ?_, fun ω => ?_⟩
    · by_cases ht : L ≤ t + 1
      · have e : {ω | τ ω ≤ (t : ℕ∞)} = m ⁻¹' Set.Iio lam := by
          ext ω
          simp only [hτdef, Set.mem_setOf_eq, Set.mem_preimage, Set.mem_Iio]
          split_ifs with h
          · simp only [h, iff_true]; exact_mod_cast (by omega : L - 1 ≤ t)
          · simp [h]
        rw [e]; exact hmσ t ht measurableSet_Iio
      · have e : {ω | τ ω ≤ (t : ℕ∞)} = ∅ := by
          ext ω
          simp only [hτdef, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
          split_ifs with h
          · intro hle
            have : L - 1 ≤ t := by exact_mod_cast hle
            omega
          · simp
        rw [e]; exact @MeasurableSet.empty _ (rewardSigma t)
    · simp only [hτdef]
      split_ifs
      · exact_mod_cast (by omega : 1 ≤ L - 1)
      · exact le_top
  -- pointwise form of the stopped reward
  have hpoint : ∀ ω, stoppedReward γ lam (fun _ => θ) τ ω =
      ∑ t ∈ Finset.range L, γ ^ t * (θ ω - lam) +
        γ ^ L / (1 - γ) * (I ω * (θ ω - lam)) := by
    intro ω
    unfold stoppedReward
    by_cases h : m ω < lam
    · have hτω : τ ω = ((L - 1 : ℕ) : ℕ∞) := by simp [hτdef, h]
      have hIω : I ω = 0 := by simp [hI, not_le.mpr h]
      rw [hIω, zero_mul, mul_zero, add_zero, hτω]
      rw [tsum_eq_sum (s := Finset.range L)]
      · refine Finset.sum_congr rfl (fun t ht => ?_)
        have : t ≤ L - 1 := by have := Finset.mem_range.mp ht; omega
        rw [if_pos (by exact_mod_cast this)]
      · intro t ht
        have : ¬ t ≤ L - 1 := by have := Finset.mem_range.not.mp ht; omega
        rw [if_neg (by exact_mod_cast this)]
    · have hτω : τ ω = ⊤ := by simp [hτdef, h]
      have hIω : I ω = 1 := by simp [hI, not_lt.mp h]
      rw [hIω, one_mul, hτω]
      simp only [le_top, if_true]
      have hsum : Summable (fun t : ℕ => γ ^ t * (θ ω - lam)) :=
        (summable_geometric_of_lt_one hγ0.le hγ1).mul_right _
      rw [← hsum.sum_add_tsum_nat_add L]
      congr 1
      have e : ∀ t : ℕ, γ ^ (t + L) * (θ ω - lam) = γ ^ L * (θ ω - lam) * γ ^ t := by
        intro t; rw [pow_add]; ring
      simp_rw [e]
      rw [_root_.tsum_mul_left, tsum_geometric_of_lt_one hγ0.le hγ1]
      field_simp
  -- integrating
  have hθint : Integrable (θ : Ω → ℝ) P := integrable_theta σW2
  have hmint : Integrable m P := by
    have : m = fun ω : Ω => a * ω.1 + b * S ω.2 := funext hpt
    rw [this]; exact (hXint.const_mul _).add (hYint.const_mul _)
  have hθ0 : ∫ ω, θ ω ∂P = 0 := hmeanX
  have hsubI : Integrable (fun ω => θ ω - lam) P := hθint.sub (integrable_const lam)
  have hsubm : Integrable (fun ω => θ ω - m ω) P := hθint.sub hmint
  have hsubml : Integrable (fun ω => m ω - lam) P := hmint.sub (integrable_const lam)
  have hA : ∫ ω, ∑ t ∈ Finset.range L, γ ^ t * (θ ω - lam) ∂P =
      -(∑ t ∈ Finset.range L, γ ^ t * lam) := by
    rw [integral_finsetSum _ (fun t _ => hsubI.const_mul _)]
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl (fun t _ => ?_)
    rw [integral_const_mul, integral_sub (f := fun ω => θ ω) (g := fun _ => lam) hθint
      (integrable_const lam), hθ0]
    simp
  have hsplit : ∫ ω, I ω * (θ ω - lam) ∂P =
      ∫ ω, max (postMean 0 1 (σW2 : ℝ) L ω - lam) 0 ∂P := by
    have e : ∀ ω, I ω * (θ ω - lam) = I ω * (θ ω - m ω) + I ω * (m ω - lam) := by
      intro ω; ring
    simp_rw [e]
    rw [integral_add (f := fun ω => I ω * (θ ω - m ω)) (g := fun ω => I ω * (m ω - lam))
      (hIf _ hsubm) (hIf _ hsubml),
      hkey, zero_add]
    refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
    simp only [hI]
    split_ifs with h
    · rw [one_mul, max_eq_left (by linarith)]
    · rw [zero_mul, max_eq_right (by linarith)]
  have hint_tau : ∫ ω, stoppedReward γ lam (fun _ => θ) τ ω ∂P =
      -(∑ t ∈ Finset.range L, γ ^ t * lam) +
        γ ^ L / (1 - γ) * ∫ ω, max (postMean 0 1 (σW2 : ℝ) L ω - lam) 0 ∂P := by
    simp_rw [hpoint]
    have h1 : Integrable (fun ω => ∑ t ∈ Finset.range L, γ ^ t * (θ ω - lam)) P :=
      integrable_finsetSum _ (fun t _ => hsubI.const_mul _)
    have h2 : Integrable (fun ω => γ ^ L / (1 - γ) * (I ω * (θ ω - lam))) P :=
      (hIf _ hsubI).const_mul _
    rw [integral_add h1 h2, hA, integral_const_mul, hsplit]
  -- the value dominates this policy
  have hmaxint : Integrable (fun ω => max (θ ω - lam) 0) P :=
    (hθint.sub (integrable_const lam)).sup (integrable_const 0)
  have hbdd : BddAbove (Set.range fun τ' : {τ : Ω → ℕ∞ // IsRetirementTime τ} =>
      ∫ ω, stoppedReward γ lam (fun _ => θ) τ'.1 ω ∂P) := by
    refine ⟨∫ ω, ((θ ω - lam) + γ / (1 - γ) * max (θ ω - lam) 0) ∂P, ?_⟩
    rintro _ ⟨τ', rfl⟩
    exact integral_mono (integrable_stoppedReward γ lam hγ0 hγ1 σW2 τ'.2)
      ((hθint.sub (integrable_const lam)).add (hmaxint.const_mul _))
      (fun ω => stoppedReward_le γ lam hγ0 hγ1 τ'.1 ω)
  have hle : ∫ ω, stoppedReward γ lam (fun _ => θ) τ ω ∂P ≤ value σW2 γ lam 0 1 := by
    unfold value
    exact le_ciSup (f := fun τ' : {τ : Ω → ℕ∞ // IsRetirementTime τ} =>
      ∫ ω, stoppedReward γ lam (fun _ => θ) τ'.1 ω ∂P) hbdd ⟨τ, hτ⟩
  rw [hint_tau] at hle
  refine ⟨hle, fun hlam0 => ?_⟩
  have hsum : ∑ t ∈ Finset.range L, γ ^ t * lam ≤ (L : ℝ) * lam := by
    calc ∑ t ∈ Finset.range L, γ ^ t * lam ≤ ∑ t ∈ Finset.range L, lam :=
          Finset.sum_le_sum (fun t _ => by
            have : γ ^ t ≤ 1 := pow_le_one₀ hγ0.le hγ1.le
            nlinarith)
      _ = (L : ℝ) * lam := by simp
  linarith
