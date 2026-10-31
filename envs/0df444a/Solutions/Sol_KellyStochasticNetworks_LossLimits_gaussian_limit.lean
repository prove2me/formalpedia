-- Prove2me | solution 1 for KellyStochasticNetworks.LossLimits.gaussian_limit
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T05:11:54.009733+00:00
-- url     : https://prove2.me/submissions/488bcab0-3b4d-4783-99b6-0e97c5299b59
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_KellyStochasticNetworks_LossLimits_Laws
import Definitions.Def_KellyStochasticNetworks_LossLimits_Gaussian
import Theorems.Thm_KellyStochasticNetworks_LossLimits_fluctuation_exp_moment_bound
import Theorems.Thm_KellyStochasticNetworks_LossLimits_fluctuation_charFun_limit
import Theorems.Thm_KellyStochasticNetworks_LossLimits_product_law_normalized
import Theorems.Thm_KellyStochasticNetworks_LossLimits_blocking_mode_limit

open MeasureTheory Filter Topology
open scoped BoundedContinuousFunction

namespace GLRed

/-- Truncation at level `K`. -/
noncomputable def trunc (K t : ℝ) : ℝ := max (-K) (min t K)

lemma trunc_cont (K : ℝ) : Continuous (trunc K) := by
  unfold trunc; fun_prop

lemma abs_trunc_le {K : ℝ} (hK : 0 ≤ K) (t : ℝ) : |trunc K t| ≤ K := by
  unfold trunc
  rw [abs_le]; constructor
  · exact le_max_left _ _
  · exact max_le (by linarith) (min_le_right _ _)

lemma abs_sub_trunc_le {K : ℝ} (hK : 0 < K) (t : ℝ) : |t - trunc K t| ≤ t ^ 2 / K := by
  unfold trunc
  have h2 : 0 ≤ t ^ 2 / K := by positivity
  rcases le_or_gt (|t|) K with h | h
  · rw [abs_le] at h
    have : max (-K) (min t K) = t := by
      rw [min_eq_left h.2, max_eq_right h.1]
    rw [this]; simpa using h2
  · have hK' : |t| ≤ t ^ 2 / K := by
      rw [le_div_iff₀ hK, ← sq_abs]
      nlinarith [abs_nonneg t]
    rcases le_or_gt 0 t with ht | ht
    · rw [abs_of_nonneg ht] at h hK'
      have : max (-K) (min t K) = K := by
        rw [min_eq_right h.le, max_eq_right (by linarith)]
      rw [this, abs_of_nonneg (by linarith)]; linarith
    · rw [abs_of_neg ht] at h hK'
      have : max (-K) (min t K) = -K := by
        rw [min_eq_left (by linarith), max_eq_left (by linarith)]
      rw [this, abs_of_neg (by linarith)]; linarith

/-- Uniform integrability transfer: weak convergence plus a uniform second-moment bound gives
integrability in the limit and convergence of the integrals. -/
lemma ui_limit {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    (μ : ℕ → Measure X) (γ : Measure X) [IsProbabilityMeasure γ]
    (hprob : ∀ᶠ N in atTop, IsProbabilityMeasure (μ N))
    (hW : ∀ f : X → ℝ, Continuous f → Bornology.IsBounded (Set.range f) →
      Tendsto (fun N => ∫ u, f u ∂(μ N)) atTop (𝓝 (∫ u, f u ∂γ)))
    (g : X → ℝ) (hg : Continuous g)
    (hint : ∀ᶠ N in atTop, Integrable (fun u => g u ^ 2) (μ N))
    (M : ℝ) (hM : ∀ᶠ N in atTop, ∫ u, g u ^ 2 ∂(μ N) ≤ M) :
    Integrable g γ ∧ Tendsto (fun N => ∫ u, g u ∂(μ N)) atTop (𝓝 (∫ u, g u ∂γ)) := by
  -- bounded truncations of g^2
  have hmin : ∀ K : ℝ, 0 ≤ K → ∫ u, min (g u ^ 2) K ∂γ ≤ M := by
    intro K hK
    have hc : Continuous (fun u => min (g u ^ 2) K) := by fun_prop
    have hb : Bornology.IsBounded (Set.range (fun u => min (g u ^ 2) K)) := by
      rw [Metric.isBounded_iff_subset_closedBall 0]
      refine ⟨K, ?_⟩
      rintro _ ⟨u, rfl⟩
      simp only [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs]
      rw [abs_le]; constructor
      · have := sq_nonneg (g u); exact le_min (by linarith) (by linarith)
      · exact min_le_right _ _
    refine le_of_tendsto (hW _ hc hb) ?_
    filter_upwards [hprob, hint, hM] with N hp hi hm
    refine le_trans (integral_mono_of_nonneg ?_ hi ?_) hm
    · exact Eventually.of_forall (fun u => le_min (sq_nonneg _) hK)
    · exact Eventually.of_forall (fun u => min_le_left _ _)
  -- integrability of g^2 under γ
  have hg2meas : Measurable (fun u => g u ^ 2) := (hg.pow 2).measurable
  have hlint : ∫⁻ u, ENNReal.ofReal (g u ^ 2) ∂γ ≤ ENNReal.ofReal M := by
    have hmono : Monotone (fun (k : ℕ) (u : X) => ENNReal.ofReal (min (g u ^ 2) k)) := by
      intro a b hab u
      exact ENNReal.ofReal_le_ofReal (min_le_min_left _ (by exact_mod_cast hab))
    have hsup : (fun u => ENNReal.ofReal (g u ^ 2)) ≤
        fun u => ⨆ k : ℕ, ENNReal.ofReal (min (g u ^ 2) k) := by
      intro u
      obtain ⟨k, hk⟩ := exists_nat_ge (g u ^ 2)
      refine le_iSup_of_le k ?_
      exact ENNReal.ofReal_le_ofReal (le_min le_rfl hk)
    refine le_trans (lintegral_mono hsup) ?_
    rw [lintegral_iSup (fun k => by
      exact ENNReal.measurable_ofReal.comp (hg2meas.min measurable_const)) hmono]
    refine iSup_le (fun k => ?_)
    have hcont : Continuous (fun u => min (g u ^ 2) (k : ℝ)) := by fun_prop
    have hbdd : ∀ u, ‖min (g u ^ 2) (k : ℝ)‖ ≤ k := by
      intro u; rw [Real.norm_eq_abs, abs_le]; constructor
      · have := sq_nonneg (g u); have : (0:ℝ) ≤ k := Nat.cast_nonneg k
        exact le_trans (by linarith) (le_min (sq_nonneg _) this)
      · exact min_le_right _ _
    have hI : Integrable (fun u => min (g u ^ 2) (k : ℝ)) γ :=
      Integrable.of_bound hcont.aestronglyMeasurable k (Eventually.of_forall hbdd)
    rw [← ofReal_integral_eq_lintegral_ofReal hI
      (Eventually.of_forall fun u => le_min (sq_nonneg _) (Nat.cast_nonneg k))]
    exact ENNReal.ofReal_le_ofReal (hmin k (Nat.cast_nonneg k))
  have hI2 : Integrable (fun u => g u ^ 2) γ := by
    refine ⟨hg2meas.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun u => sq_nonneg _)]
    exact lt_of_le_of_lt hlint ENNReal.ofReal_lt_top
  have hγM : ∫ u, g u ^ 2 ∂γ ≤ M := by
    have := ofReal_integral_eq_lintegral_ofReal hI2 (Eventually.of_forall fun u => sq_nonneg _)
    rw [← this] at hlint
    have hM0 : 0 ≤ M := by
      have := hmin 0 le_rfl
      have h0 : ∫ u, min (g u ^ 2) (0:ℝ) ∂γ = 0 := by
        have : (fun u => min (g u ^ 2) (0:ℝ)) = fun _ => 0 := by
          funext u; exact min_eq_right (sq_nonneg _)
        rw [this]; simp
      linarith
    exact (ENNReal.ofReal_le_ofReal_iff hM0).1 hlint
  have hIg : Integrable g γ := by
    refine Integrable.mono' (hI2.add (integrable_const (1:ℝ))) hg.aestronglyMeasurable ?_
    refine Eventually.of_forall (fun u => ?_)
    show ‖g u‖ ≤ g u ^ 2 + 1
    rw [Real.norm_eq_abs]
    nlinarith [abs_nonneg (g u), sq_abs (g u)]
  refine ⟨hIg, ?_⟩
  -- epsilon argument
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hM0 : 0 ≤ M := le_trans (integral_nonneg fun u => sq_nonneg (g u)) hγM
  set K : ℝ := 3 * (M + 1) / ε + 1 with hKdef
  have hKpos : 0 < K := by positivity
  have hKε : (M + 1) / K < ε / 3 := by
    rw [div_lt_iff₀ hKpos]
    rw [hKdef]
    have : ε / 3 * (3 * (M + 1) / ε + 1) = (M + 1) + ε / 3 := by
      field_simp
    rw [this]; linarith
  have htc : Continuous (fun u => trunc K (g u)) := (trunc_cont K).comp hg
  have htb : Bornology.IsBounded (Set.range (fun u => trunc K (g u))) := by
    rw [Metric.isBounded_iff_subset_closedBall 0]
    refine ⟨K, ?_⟩
    rintro _ ⟨u, rfl⟩
    simpa [Real.norm_eq_abs] using abs_trunc_le hKpos.le (g u)
  have hT := hW _ htc htb
  rw [Metric.tendsto_atTop] at hT
  obtain ⟨N1, hN1⟩ := hT (ε / 3) (by positivity)
  obtain ⟨N2, hN2⟩ := eventually_atTop.1 (hprob.and (hint.and hM))
  refine ⟨max N1 N2, fun N hN => ?_⟩
  obtain ⟨hp, hi, hm⟩ := hN2 N (le_of_max_le_right hN)
  have hdist := hN1 N (le_of_max_le_left hN)
  have hIgN : Integrable g (μ N) := by
    refine Integrable.mono' (hi.add (integrable_const (1:ℝ))) hg.aestronglyMeasurable ?_
    refine Eventually.of_forall (fun u => ?_)
    show ‖g u‖ ≤ g u ^ 2 + 1
    rw [Real.norm_eq_abs]
    nlinarith [abs_nonneg (g u), sq_abs (g u)]
  have hItN : Integrable (fun u => trunc K (g u)) (μ N) :=
    Integrable.of_bound htc.aestronglyMeasurable K
      (Eventually.of_forall fun u => by simpa [Real.norm_eq_abs] using abs_trunc_le hKpos.le (g u))
  have hItγ : Integrable (fun u => trunc K (g u)) γ :=
    Integrable.of_bound htc.aestronglyMeasurable K
      (Eventually.of_forall fun u => by simpa [Real.norm_eq_abs] using abs_trunc_le hKpos.le (g u))
  have e1 : |∫ u, g u ∂(μ N) - ∫ u, trunc K (g u) ∂(μ N)| ≤ M / K := by
    rw [← integral_sub hIgN hItN]
    refine le_trans (abs_integral_le_integral_abs) ?_
    calc ∫ u, |g u - trunc K (g u)| ∂(μ N) ≤ ∫ u, g u ^ 2 / K ∂(μ N) := by
          refine integral_mono_of_nonneg (Eventually.of_forall fun u => abs_nonneg _)
            (hi.div_const K) (Eventually.of_forall fun u => abs_sub_trunc_le hKpos _)
      _ = (∫ u, g u ^ 2 ∂(μ N)) / K := integral_div _ _
      _ ≤ M / K := by gcongr
  have e2 : |∫ u, g u ∂γ - ∫ u, trunc K (g u) ∂γ| ≤ M / K := by
    rw [← integral_sub hIg hItγ]
    refine le_trans (abs_integral_le_integral_abs) ?_
    calc ∫ u, |g u - trunc K (g u)| ∂γ ≤ ∫ u, g u ^ 2 / K ∂γ := by
          refine integral_mono_of_nonneg (Eventually.of_forall fun u => abs_nonneg _)
            (hI2.div_const K) (Eventually.of_forall fun u => abs_sub_trunc_le hKpos _)
      _ = (∫ u, g u ^ 2 ∂γ) / K := integral_div _ _
      _ ≤ M / K := by gcongr
  have hMK : M / K < ε / 3 := lt_of_le_of_lt (by gcongr; linarith) hKε
  rw [Real.dist_eq] at hdist ⊢
  have := abs_sub_le (∫ u, g u ∂(μ N)) (∫ u, trunc K (g u) ∂(μ N)) (∫ u, g u ∂γ)
  have := abs_sub_le (∫ u, trunc K (g u) ∂(μ N)) (∫ u, trunc K (g u) ∂γ) (∫ u, g u ∂γ)
  rw [abs_sub_comm (∫ u, g u ∂γ)] at e2
  linarith

end GLRed

namespace GLRed
open KellyStochasticNetworks.LossLimits

/-- sign vector attached to a Boolean pattern -/
def sgn {R : ℕ} (σ : Fin R → Bool) (r : Fin R) : ℝ := if σ r then 1 else -1

lemma monomial_sq_le {R : ℕ} (k : Fin R → ℕ) (u : Fin R → ℝ) :
    monomial k u ^ 2 ≤ ((∑ r, 2 * k r).factorial : ℝ) *
      ∑ σ : Fin R → Bool, Real.exp (∑ r, sgn σ r * u r) := by
  set S := ∑ r, |u r| with hS
  set p := ∑ r, 2 * k r with hp
  have hS0 : 0 ≤ S := Finset.sum_nonneg (fun r _ => abs_nonneg _)
  have h1 : monomial k u ^ 2 ≤ S ^ p := by
    unfold monomial
    rw [← Finset.prod_pow, hp, ← Finset.prod_pow_eq_pow_sum]
    refine Finset.prod_le_prod (fun r _ => by positivity) (fun r _ => ?_)
    rw [← pow_mul, mul_comm (k r) 2, pow_mul, ← sq_abs (u r), ← pow_mul]
    exact pow_le_pow_left₀ (abs_nonneg _)
      (Finset.single_le_sum (f := fun r => |u r|) (fun r _ => abs_nonneg _) (Finset.mem_univ r)) _
  have h2 : S ^ p ≤ (p.factorial : ℝ) * Real.exp S := by
    have := Real.pow_div_factorial_le_exp S hS0 p
    rw [div_le_iff₀ (by exact_mod_cast Nat.factorial_pos p : (0:ℝ) < p.factorial)] at this
    linarith [mul_comm (Real.exp S) (p.factorial : ℝ)]
  have h3 : Real.exp S ≤ ∑ σ : Fin R → Bool, Real.exp (∑ r, sgn σ r * u r) := by
    let σ0 : Fin R → Bool := fun r => decide (0 ≤ u r)
    have : S = ∑ r, sgn σ0 r * u r := by
      rw [hS]; refine Finset.sum_congr rfl (fun r _ => ?_)
      simp only [sgn, σ0]
      by_cases h : 0 ≤ u r
      · simp [h, abs_of_nonneg h]
      · simp [h, abs_of_neg (lt_of_not_ge h)]
    rw [this]
    exact Finset.single_le_sum (f := fun σ => Real.exp (∑ r, sgn σ r * u r))
      (fun σ _ => (Real.exp_pos _).le) (Finset.mem_univ σ0)
  calc monomial k u ^ 2 ≤ S ^ p := h1
    _ ≤ (p.factorial : ℝ) * Real.exp S := h2
    _ ≤ _ := by gcongr

lemma monomial_cont {R : ℕ} (k : Fin R → ℕ) : Continuous (monomial k) := by
  unfold monomial; fun_prop

section main
variable {J R : ℕ} (A : Fin J → Fin R → ℕ)
    (νN : ℕ → Fin R → ℝ) (CN : ℕ → Fin J → ℕ)
    (ν : Fin R → ℝ) (C : Fin J → ℝ)

lemma occ_prob (hscale : Scaling A νN CN ν C) {N : ℕ} (hN : 0 < N) :
    IsProbabilityMeasure (occupancyLaw A (νN N) (CN N)) :=
  (product_law_normalized A (νN N) (CN N) (hscale.rates_pos N hN)).2.2.2.1

lemma fl_prob (hscale : Scaling A νN CN ν C) {N : ℕ} (hN : 0 < N) :
    IsProbabilityMeasure (fluctuationLaw A νN CN N) := by
  have := occ_prob A νN CN ν C hscale hN
  unfold fluctuationLaw
  exact Measure.isProbabilityMeasure_map (measurable_of_countable _).aemeasurable

lemma residual_cont (B : Fin J → ℝ) (x : Fin R → ℝ) : Continuous (gaussianResidual A B x) := by
  unfold gaussianResidual
  fun_prop

instance gauss_prob (B : Fin J → ℝ) (x : Fin R → ℝ) :
    IsProbabilityMeasure (conditionedGaussian A B x) := by
  unfold conditionedGaussian
  exact Measure.isProbabilityMeasure_map (residual_cont A B x).measurable.aemeasurable

lemma weak_conv (hscale : Scaling A νN CN ν C) (hslack : strictSlack A ν C)
    (f : (Fin R → ℝ) → ℝ) (hf : Continuous f) (hb : Bornology.IsBounded (Set.range f)) :
    Tendsto (fun N => ∫ u, f u ∂(fluctuationLaw A νN CN N)) atTop
      (𝓝 (∫ u, f u ∂(conditionedGaussian A (blocking A ν C) (mode A ν C)))) := by
  set γ := conditionedGaussian A (blocking A ν C) (mode A ν C) with hγ
  let e := EuclideanSpace.equiv (Fin R) ℝ
  have he : Measurable e.symm := e.symm.continuous.measurable
  let P : ℕ → ProbabilityMeasure (EuclideanSpace ℝ (Fin R)) := fun N =>
    ⟨(fluctuationLaw A νN CN (N + 1)).map e.symm, by
      have := fl_prob A νN CN ν C hscale (Nat.succ_pos N)
      exact Measure.isProbabilityMeasure_map he.aemeasurable⟩
  let P0 : ProbabilityMeasure (EuclideanSpace ℝ (Fin R)) :=
    ⟨γ.map e.symm, Measure.isProbabilityMeasure_map he.aemeasurable⟩
  have hcf : ∀ (m : Measure (Fin R → ℝ)) (t : EuclideanSpace ℝ (Fin R)),
      charFun (m.map e.symm) t =
        ∫ u, Complex.exp (Complex.I * ∑ r, ((e t) r : ℂ) * (u r : ℂ)) ∂m := by
    intro m t
    rw [charFun_apply, integral_map he.aemeasurable (by fun_prop)]
    congr 1; funext u
    congr 1
    rw [PiLp.inner_apply]
    push_cast
    rw [mul_comm]
    congr 1
    refine Finset.sum_congr rfl (fun r _ => ?_)
    simp [e, mul_comm]
  have hPt : Tendsto P atTop (𝓝 P0) := by
    rw [ProbabilityMeasure.tendsto_iff_tendsto_charFun]
    intro t
    simp only [P, P0, ProbabilityMeasure.coe_mk, hcf]
    exact (fluctuation_charFun_limit A νN CN ν C hscale hslack (e t)).comp
      (tendsto_add_atTop_nat 1)
  rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto] at hPt
  obtain ⟨K, hK⟩ := (Metric.isBounded_iff).1 hb
  let F : EuclideanSpace ℝ (Fin R) →ᵇ ℝ :=
    BoundedContinuousFunction.mkOfBound ⟨fun x => f (e x), hf.comp e.continuous⟩ K
      (fun x y => hK ⟨e x, rfl⟩ ⟨e y, rfl⟩)
  have h1 := hPt F
  have hFi : ∀ m : Measure (Fin R → ℝ), ∫ x, F x ∂(m.map e.symm) = ∫ u, f u ∂m := by
    intro m
    rw [integral_map he.aemeasurable F.continuous.aestronglyMeasurable]
    rfl
  simp only [P, P0, ProbabilityMeasure.coe_mk, hFi] at h1
  exact (tendsto_add_atTop_iff_nat 1).1 h1

lemma mono_int_sq (hscale : Scaling A νN CN ν C) (hslack : strictSlack A ν C)
    (k : Fin R → ℕ) {N : ℕ} (hN : 0 < N) :
    Integrable (fun u => monomial k u ^ 2) (fluctuationLaw A νN CN N) := by
  have hI : Integrable (fun u => ((∑ r, 2 * k r).factorial : ℝ) *
      ∑ σ : Fin R → Bool, Real.exp (∑ r, sgn σ r * u r)) (fluctuationLaw A νN CN N) := by
    refine Integrable.const_mul ?_ _
    refine integrable_finsetSum _ (fun σ _ => ?_)
    exact (fluctuation_exp_moment_bound A νN CN ν C hscale hslack (sgn σ)).1 N hN
  refine Integrable.mono' hI ((monomial_cont k).pow 2).aestronglyMeasurable ?_
  refine Eventually.of_forall (fun u => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact monomial_sq_le k u

lemma mono_bound (hscale : Scaling A νN CN ν C) (hslack : strictSlack A ν C)
    (k : Fin R → ℕ) : ∃ M : ℝ, ∀ᶠ N in atTop,
      ∫ u, monomial k u ^ 2 ∂(fluctuationLaw A νN CN N) ≤ M := by
  have h := fun σ : Fin R → Bool =>
    (fluctuation_exp_moment_bound A νN CN ν C hscale hslack (sgn σ)).2
  choose M hM using h
  refine ⟨((∑ r, 2 * k r).factorial : ℝ) * ∑ σ, M σ, ?_⟩
  have hall : ∀ᶠ N in atTop, ∀ σ : Fin R → Bool,
      ∫ u, Real.exp (∑ r, sgn σ r * u r) ∂(fluctuationLaw A νN CN N) ≤ M σ :=
    Filter.eventually_all.2 hM
  filter_upwards [hall, eventually_gt_atTop 0] with N hN hN0
  have hint : ∀ σ : Fin R → Bool, Integrable (fun u => Real.exp (∑ r, sgn σ r * u r))
      (fluctuationLaw A νN CN N) := fun σ =>
    (fluctuation_exp_moment_bound A νN CN ν C hscale hslack (sgn σ)).1 N hN0
  calc ∫ u, monomial k u ^ 2 ∂(fluctuationLaw A νN CN N)
      ≤ ∫ u, ((∑ r, 2 * k r).factorial : ℝ) *
          ∑ σ : Fin R → Bool, Real.exp (∑ r, sgn σ r * u r) ∂(fluctuationLaw A νN CN N) := by
        refine integral_mono (mono_int_sq A νN CN ν C hscale hslack k hN0) ?_
          (fun u => monomial_sq_le k u)
        exact (integrable_finsetSum _ (fun σ _ => hint σ)).const_mul _
    _ = ((∑ r, 2 * k r).factorial : ℝ) *
          ∑ σ : Fin R → Bool, ∫ u, Real.exp (∑ r, sgn σ r * u r) ∂(fluctuationLaw A νN CN N) := by
        rw [integral_const_mul, integral_finsetSum _ (fun σ _ => hint σ)]
    _ ≤ _ := by
        gcongr with σ
        exact hN σ

lemma moments (hscale : Scaling A νN CN ν C) (hslack : strictSlack A ν C)
    (k : Fin R → ℕ) :
    (∀ N, 0 < N → Integrable (monomial k) (fluctuationLaw A νN CN N)) ∧
    Integrable (monomial k) (conditionedGaussian A (blocking A ν C) (mode A ν C)) ∧
    Tendsto (fun N => ∫ u, monomial k u ∂(fluctuationLaw A νN CN N))
      atTop (𝓝 (∫ u, monomial k u ∂(conditionedGaussian A (blocking A ν C) (mode A ν C)))) := by
  have hN : ∀ N, 0 < N → Integrable (monomial k) (fluctuationLaw A νN CN N) := by
    intro N hN
    have := fl_prob A νN CN ν C hscale hN
    refine Integrable.mono' ((mono_int_sq A νN CN ν C hscale hslack k hN).add
      (integrable_const (1:ℝ))) (monomial_cont k).aestronglyMeasurable ?_
    refine Eventually.of_forall (fun u => ?_)
    show ‖monomial k u‖ ≤ monomial k u ^ 2 + 1
    rw [Real.norm_eq_abs]
    nlinarith [abs_nonneg (monomial k u), sq_abs (monomial k u)]
  obtain ⟨M, hM⟩ := mono_bound A νN CN ν C hscale hslack k
  have := ui_limit (fun N => fluctuationLaw A νN CN N)
    (conditionedGaussian A (blocking A ν C) (mode A ν C))
    (by filter_upwards [eventually_gt_atTop 0] with N hN0
        exact fl_prob A νN CN ν C hscale hN0)
    (fun f hf hb => weak_conv A νN CN ν C hscale hslack f hf hb)
    (monomial k) (monomial_cont k)
    (by filter_upwards [eventually_gt_atTop 0] with N hN0
        exact mono_int_sq A νN CN ν C hscale hslack k hN0) M hM
  exact ⟨hN, this.1, this.2⟩

lemma monomial_single {R : ℕ} (r : Fin R) (u : Fin R → ℝ) :
    monomial (Pi.single r 1) u = u r := by
  unfold monomial
  rw [Finset.prod_eq_single r]
  · simp
  · intro s _ hs; simp [hs]
  · intro h; exact absurd (Finset.mem_univ r) h

lemma mean_occ (hscale : Scaling A νN CN ν C) (hslack : strictSlack A ν C) (r : Fin R) :
    (∀ N, 0 < N → Integrable (fun n : Fin R → ℕ => (n r : ℝ))
        (occupancyLaw A (νN N) (CN N))) ∧
      Tendsto (fun N => (∫ n, (n r : ℝ) ∂(occupancyLaw A (νN N) (CN N))) / N)
        atTop (𝓝 (mode A ν C r)) := by
  obtain ⟨hint, -, hlim⟩ := moments A νN CN ν C hscale hslack (Pi.single r 1)
  have hfun : monomial (Pi.single r 1) = fun u => u r := funext (monomial_single r)
  rw [hfun] at hint hlim
  set xN : ℕ → Fin R → ℝ := fun N => mode A (νN N) (fun j => (CN N j : ℝ)) with hxN
  set φ : ℕ → (Fin R → ℕ) → (Fin R → ℝ) :=
    fun N n r => ((n r : ℝ) - xN N r) / Real.sqrt N with hφ
  have hmap : ∀ N, fluctuationLaw A νN CN N = (occupancyLaw A (νN N) (CN N)).map (φ N) := by
    intro N; rfl
  have hφi : ∀ N, 0 < N → Integrable (fun n => φ N n r) (occupancyLaw A (νN N) (CN N)) := by
    intro N hN
    have h := hint N hN
    rw [hmap N] at h
    exact (integrable_map_measure (continuous_apply r).aestronglyMeasurable
      (measurable_of_countable _).aemeasurable).1 h
  have hrepr : ∀ N : ℕ, 0 < N → ∀ n : Fin R → ℕ,
      (n r : ℝ) = Real.sqrt N * φ N n r + xN N r := by
    intro N hN n
    have hs : Real.sqrt N ≠ 0 := by positivity
    simp only [hφ]; field_simp; ring
  have hint2 : ∀ N, 0 < N → Integrable (fun n : Fin R → ℕ => (n r : ℝ))
      (occupancyLaw A (νN N) (CN N)) := by
    intro N hN
    have := occ_prob A νN CN ν C hscale hN
    have h2 := ((hφi N hN).const_mul (Real.sqrt N)).add (integrable_const (xN N r))
    refine h2.congr (Eventually.of_forall fun n => ?_)
    simp only [Pi.add_apply]
    rw [hrepr N hN n]
  refine ⟨hint2, ?_⟩
  have heq : ∀ N, 0 < N → (∫ n, (n r : ℝ) ∂(occupancyLaw A (νN N) (CN N))) / N =
      xN N r / N + (Real.sqrt N)⁻¹ * ∫ u, u r ∂(fluctuationLaw A νN CN N) := by
    intro N hN
    have := occ_prob A νN CN ν C hscale hN
    have hs : Real.sqrt N ≠ 0 := by positivity
    have hint3 : ∫ u, u r ∂(fluctuationLaw A νN CN N) =
        ∫ n, φ N n r ∂(occupancyLaw A (νN N) (CN N)) := by
      rw [hmap N, integral_map (measurable_of_countable _).aemeasurable
        (continuous_apply r).aestronglyMeasurable]
    rw [hint3]
    have : ∫ n, (n r : ℝ) ∂(occupancyLaw A (νN N) (CN N)) =
        Real.sqrt N * ∫ n, φ N n r ∂(occupancyLaw A (νN N) (CN N)) + xN N r := by
      rw [integral_congr_ae (Eventually.of_forall fun n => hrepr N hN n),
        integral_add ((hφi N hN).const_mul _) (integrable_const _), integral_const_mul,
        integral_const]
      simp
    rw [this]
    have hN'' : (N:ℝ) = Real.sqrt (N:ℝ) ^ 2 := (Real.sq_sqrt (Nat.cast_nonneg _)).symm
    generalize hsdef : Real.sqrt (N:ℝ) = s at hs hN'' ⊢
    rw [hN'']
    field_simp
    ring
  have h1 : Tendsto (fun N => xN N r / N) atTop (𝓝 (mode A ν C r)) :=
    (tendsto_pi_nhds.1 (blocking_mode_limit A νN CN ν C hscale hslack).2) r
  have h2 : Tendsto (fun N : ℕ => (Real.sqrt N)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
  have h3 := h1.add (h2.mul hlim)
  rw [zero_mul, add_zero] at h3
  refine h3.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with N hN
  exact (heq N hN).symm

end main
end GLRed

open KellyStochasticNetworks.LossLimits in
theorem solution {J R : ℕ} (A : Fin J → Fin R → ℕ)
    (νN : ℕ → Fin R → ℝ) (CN : ℕ → Fin J → ℕ)
    (ν : Fin R → ℝ) (C : Fin J → ℝ)
    (hscale : Scaling A νN CN ν C) (hslack : strictSlack A ν C) :
    let γ := conditionedGaussian A (blocking A ν C) (mode A ν C)
    (∀ f : (Fin R → ℝ) → ℝ, Continuous f → Bornology.IsBounded (Set.range f) →
      Tendsto (fun N => ∫ u, f u ∂(fluctuationLaw A νN CN N))
        atTop (𝓝 (∫ u, f u ∂γ))) ∧
    (∀ k : Fin R → ℕ,
      (∀ N, 0 < N → Integrable (monomial k) (fluctuationLaw A νN CN N)) ∧
      Integrable (monomial k) γ ∧
      Tendsto (fun N => ∫ u, monomial k u ∂(fluctuationLaw A νN CN N))
        atTop (𝓝 (∫ u, monomial k u ∂γ))) ∧
    (∀ r, (∀ N, 0 < N → Integrable (fun n : Fin R → ℕ => (n r : ℝ))
        (occupancyLaw A (νN N) (CN N))) ∧
      Tendsto (fun N => (∫ n, (n r : ℝ) ∂(occupancyLaw A (νN N) (CN N))) / N)
        atTop (𝓝 (mode A ν C r))) := by
  intro γ
  exact ⟨fun f hf hb => GLRed.weak_conv A νN CN ν C hscale hslack f hf hb,
    fun k => GLRed.moments A νN CN ν C hscale hslack k,
    fun r => GLRed.mean_occ A νN CN ν C hscale hslack r⟩
