-- Prove2me | solution 1 for OAI.ThreeTorus.exists_signal_reflected_geometry_state
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T12:15:51.934857+00:00
-- url     : https://prove2.me/submissions/2670fc30-c829-4c40-9f0c-6116ab365cd8

import Mathlib
import Definitions.Def_ThreeTorus
import Definitions.Def_OAIQ13Tt000
import Theorems.Thm_OAI_ThreeTorus_exact_quantile_passage

section
-- module Solutions.OAIQ13_TT.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : p) :
    (if p then a else b) = a := if_pos h
theorem ite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : ¬p) :
    (if p then a else b) = b := if_neg h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ13_TT.ThreeTorus_Cutoffs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Smooth cylinder cutoffs, circle periodization, and regularity of covering lifts. -/

section

/-! Smooth compact supported cutoffs on the actual real-frequency/slow-circle
cylinder, used for the disjoint stationary images in the passage lemma. -/
noncomputable section
open Set Function Filter Topology
open scoped Topology Manifold
namespace ThreeTorus

/-- A compactly supported Euclidean cutoff, equal to one on a neighborhood
of the prescribed compact set, not merely on the set itself. -/
lemma compact_smooth_cutoff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {K U : Set E} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ f : E → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f ∧ HasCompactSupport f ∧
      tsupport f ⊆ U ∧ (∀ x, 0 ≤ f x ∧ f x ≤ 1) ∧
      ∀ x ∈ K, f =ᶠ[𝓝 x] 1 := by
  obtain ⟨O,hO,hKO,hOc⟩ := exists_isOpen_superset_and_isCompact_closure hK
  obtain ⟨V,hV,hKV,hVU⟩ := hK.exists_isOpen_closure_subset
    ((hU.inter hO).mem_nhdsSet.mpr (subset_inter hKU hKO))
  have hcV : IsCompact (closure V) := hOc.of_isClosed_subset isClosed_closure
    (fun x hx => subset_closure (hVU hx).2)
  obtain ⟨W,hW,hKW,hWV⟩ := hK.exists_isOpen_closure_subset (hV.mem_nhdsSet.mpr hKV)
  obtain ⟨f,hf,hfr,hfs,hf1⟩ := exists_contMDiff_support_eq_eq_one_iff
    (I := 𝓘(ℝ,E)) (n := (⊤ : ℕ∞)) hV isClosed_closure hWV
  refine ⟨f,hf.contDiff,?_,?_,?_,?_⟩
  · simpa only [HasCompactSupport, tsupport, hfs] using hcV
  · rw [tsupport, hfs]
    intro x hx
    exact (hVU hx).1
  · intro x
    exact hfr (mem_range_self x)
  · intro x hx
    filter_upwards [hW.mem_nhds (hKW hx)] with y hy
    exact (hf1 y).mp (subset_closure hy)

/-- Compact support away from the zero frequency leaves finitely many
nonzero angular indices at every positive integral scale. -/
lemma cylinder_cutoff_finite_indices {χ : ℝ × UnitAddCircle → ℝ}
    (hc : HasCompactSupport χ) (hzero : ∀ a, χ (0,a) = 0) (n : ℕ) (hn : 0 < n) :
    ∃ S : Finset ℤ, (0:ℤ) ∉ S ∧ ∀ j ∉ S, ∀ a, χ ((j:ℝ)/n,a) = 0 := by
  classical
  obtain ⟨R,hR⟩ := (hc.image continuous_fst).isBounded.exists_norm_le
  obtain ⟨N,hN⟩ := exists_nat_gt ((n:ℝ)*R)
  refine ⟨(Finset.Icc (-(N:ℤ)) N).erase 0,Finset.notMem_erase _ _,?_⟩
  intro j hj a
  by_contra ha
  have hj0 : j ≠ 0 := by intro hz; subst j; simp [hzero] at ha
  have hb : |(j:ℝ)/(n:ℝ)| ≤ R :=
    hR _ (mem_image_of_mem Prod.fst (subset_tsupport χ ha))
  have hn' : (0:ℝ) < n := by exact_mod_cast hn
  rw [abs_div,abs_of_pos hn'] at hb
  have hjN : |(j:ℝ)| < N := ((div_le_iff₀ hn').mp hb).trans_lt (by nlinarith)
  apply hj
  rw [Finset.mem_erase,Finset.mem_Icc]
  exact ⟨hj0,by exact_mod_cast (abs_le.mp hjN.le)⟩

end ThreeTorus
end
end

end OAI
end

section
-- module Solutions.OAIQ13_TT.ThreeTorus_PositiveLaws
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Positive Fourier laws, compact integral differentiation, affine densities, and prime-sieve signal laws. -/

noncomputable section
open MeasureTheory Filter Set Complex
open scoped Topology SchwartzMap FourierTransform Real
open scoped Topology
open MeasureTheory Set
open scoped ENNReal Topology
open Set Function Filter
open scoped Topology NNReal
open MeasureTheory Filter Set
open MeasureTheory Set Function
open scoped Topology ENNReal
open scoped Topology BigOperators

noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace ThreeTorus

/-- Compact-parameter differentiation, used by the exact passage near epsilon=0. -/
lemma hasFDerivAt_compact_integral
    {E : Type} {G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
    {F : E × ℝ → G} (hF : ContDiff ℝ 1 F) (a b : ℝ) (x : E) :
    HasFDerivAt (fun y => ∫ t in a..b, F (y,t))
      (∫ t in a..b, (fderiv ℝ F (x,t)).comp (ContinuousLinearMap.inl ℝ E ℝ)) x := by
  let D : E × ℝ → E →L[ℝ] G := fun p =>
    (fderiv ℝ F p).comp (ContinuousLinearMap.inl ℝ E ℝ)
  have hD : Continuous D := hF.continuous_fderiv (by norm_num) |>.clm_comp continuous_const
  obtain ⟨C,hC⟩ := ((isCompact_closedBall x 1).prod (isCompact_uIcc (a := a) (b := b))).exists_bound_of_continuousOn hD.continuousOn
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le''
    (F := fun y t => F (y,t)) (F' := fun y t => D (y,t))
    (bound := fun _ => C) (Metric.closedBall_mem_nhds x (by norm_num : (0:ℝ)<1)) ?_ ?_ ?_ ?_
    intervalIntegrable_const ?_
  · exact Eventually.of_forall (fun y => (hF.continuous.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable)
  · exact (hF.continuous.comp (continuous_const.prodMk continuous_id)).intervalIntegrable _ _
  · exact (hD.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_uIoc] with t ht
    intro y hy
    exact hC (y,t) ⟨hy,uIoc_subset_uIcc ht⟩
  · exact Eventually.of_forall (fun t y _ => by
      simpa [D,Function.comp_def] using ((hF.differentiable one_ne_zero ((ContinuousLinearMap.inl ℝ E ℝ) y+(0,t))).hasFDerivAt).comp y
        ((ContinuousLinearMap.inl ℝ E ℝ).hasFDerivAt.add_const (0,t)))

/-- Smooth parameter integration over a fixed compact interval. -/
lemma contDiff_compact_integral
    {E : Type} {G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
    (n : ℕ) {F : E × ℝ → G} (hF : ContDiff ℝ n F) (a b : ℝ) :
    ContDiff ℝ n (fun y => ∫ t in a..b, F (y,t)) := by
  induction n generalizing G with
  | zero =>
    apply contDiff_zero.mpr
    exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (show Continuous (Function.uncurry (fun y t => F (y,t))) from hF.continuous) a b
  | succ n ih =>
    let D : E × ℝ → E →L[ℝ] G := fun p =>
      (fderiv ℝ F p).comp (ContinuousLinearMap.inl ℝ E ℝ)
    have hD : ContDiff ℝ n D := (hF.fderiv_right (by simp)).clm_comp contDiff_const
    have hder (x : E) := hasFDerivAt_compact_integral (hF.of_le (by exact_mod_cast Nat.succ_pos n)) a b x
    rw [show ((n+1 : ℕ) : WithTop ℕ∞) = (n : WithTop ℕ∞)+1 by simp, contDiff_succ_iff_fderiv]
    refine ⟨fun x => (hder x).differentiableAt, ?_, ?_⟩
    · simp
    · have heq : fderiv ℝ (fun y => ∫ t in a..b, F (y,t)) =
          fun y => ∫ t in a..b, D (y,t) := by
        funext y
        exact (hder y).fderiv
      rw [heq]
      exact ih hD

lemma smooth_compact_integral
    {E : Type} {G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
    {F : E × ℝ → G} (hF : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F) (a b : ℝ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y => ∫ t in a..b, F (y,t)) := by
  rw [contDiff_infty]
  intro n
  exact contDiff_compact_integral n (hF.of_le (by exact_mod_cast (le_top : (n : ℕ∞) ≤ ⊤))) a b

/-! The positive Fourier law. The sinc and averaged
baseline below are exactly those of the manuscript, including the scale and
normalization. -/
open scoped FourierTransform Convolution

lemma sinc_eq_integral_cos (x : ℝ) :
    Real.sinc x = ∫ t in (0 : ℝ)..1, Real.cos (x*t) := by
  by_cases hx : x = 0
  · simp [hx]
  · rw [intervalIntegral.integral_comp_mul_left _ hx,integral_cos]
    simp only [mul_zero,mul_one,Real.sin_zero,sub_zero,smul_eq_mul]
    rw [Real.sinc_of_ne_zero hx]
    ring

lemma smooth_sinc : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Real.sinc := by
  rw [show Real.sinc = (fun x => ∫ t in (0 : ℝ)..1, Real.cos (x*t)) from
    funext sinc_eq_integral_cos]
  exact smooth_compact_integral (F := fun p : ℝ × ℝ => Real.cos (p.1*p.2)) (by fun_prop) 0 1

lemma signalSinc_nonneg {α : ℝ} (hα : 0 ≤ α) (R : ℝ) : 0 ≤ signalSinc α R :=
  mul_nonneg hα (sq_nonneg _)

lemma smooth_signalSinc (α : ℝ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (signalSinc α) := by
  exact contDiff_const.mul ((smooth_sinc.comp (by fun_prop)).pow 2)

lemma smooth_signalBaseline (α : ℝ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (signalBaseline α) := by
  apply contDiff_const.mul
  exact smooth_compact_integral (F := fun p : ℝ × ℝ => signalSinc α (p.1-p.2))
    ((smooth_signalSinc α).comp (by fun_prop)) _ _

lemma sinc_sq_le (x : ℝ) : Real.sinc x ^ 2 ≤ 1 := by
  simpa only [sq_abs,one_pow] using
    (sq_le_sq₀ (abs_nonneg (Real.sinc x)) (by norm_num : (0:ℝ) ≤ 1)).2 (Real.abs_sinc_le_one x)

lemma sin_sq_le_one (x : ℝ) : Real.sin x ^ 2 ≤ 1 := by
  simpa only [sq_abs,one_pow] using
    (sq_le_sq₀ (abs_nonneg (Real.sin x)) (by norm_num : (0:ℝ) ≤ 1)).2 (Real.abs_sin_le_one x)

lemma sinc_sq_mul_sq_le (x : ℝ) : Real.sinc x ^ 2 * x^2 ≤ 1 := by
  by_cases hx : x = 0
  · simp [hx]
  · rw [Real.sinc_of_ne_zero hx]
    field_simp
    exact sin_sq_le_one x

lemma signalSinc_decay {α : ℝ} (hα : 0 < α) (R : ℝ) :
    signalSinc α R ≤ (α + (Real.pi^2*α)⁻¹) * (1+R^2)⁻¹ := by
  have ha : Real.pi^2*α > 0 := by positivity
  have hsmall : signalSinc α R ≤ α :=
    mul_le_of_le_one_right hα.le (sinc_sq_le _)
  have hlarge : signalSinc α R * R^2 ≤ (Real.pi^2*α)⁻¹ := by
    have := sinc_sq_mul_sq_le (Real.pi*α*R)
    rw [← one_div]
    apply (le_div_iff₀ ha).2
    dsimp [signalSinc]
    nlinarith
  have hd : 0 < 1+R^2 := by positivity
  rw [← div_eq_mul_inv,le_div_iff₀ hd]
  nlinarith

lemma integrable_signalSinc {α : ℝ} (hα : 0 < α) : Integrable (signalSinc α) := by
  apply (integrable_inv_one_add_sq.const_mul (α + (Real.pi^2*α)⁻¹)).mono'
    (smooth_signalSinc α).continuous.aestronglyMeasurable
  filter_upwards [] with R
  rw [Real.norm_eq_abs,abs_of_nonneg (signalSinc_nonneg hα.le R)]
  exact signalSinc_decay hα R

lemma signalAverageRadius_pos {α : ℝ} (hα : 0 < α) : 0 < signalAverageRadius α := by
  dsimp [signalAverageRadius]
  positivity

lemma signalSinc_denominator {α : ℝ} (hα : 0 < α) (R : ℝ) :
    signalSinc α R * (Real.pi^2*α*R^2) = Real.sin (Real.pi*α*R)^2 := by
  by_cases hR : R = 0
  · simp [hR]
  · dsimp [signalSinc]
    rw [Real.sinc_of_ne_zero (by positivity : Real.pi*α*R ≠ 0)]
    field_simp

lemma integral_sin_sq_pi (x : ℝ) :
    ∫ t in x..x+Real.pi, Real.sin t^2 = Real.pi/2 := by
  rw [integral_sin_sq,Real.sin_add_pi,Real.cos_add_pi]
  ring

lemma signal_sin_sq_average {α : ℝ} (hα : 0 < α) (R : ℝ) :
    ∫ t in -signalAverageRadius α..signalAverageRadius α,
      Real.sin (Real.pi*α*(R-t))^2 = signalAverageRadius α := by
  rw [intervalIntegral.integral_comp_sub_left (fun u => Real.sin (Real.pi*α*u)^2) R]
  rw [intervalIntegral.integral_comp_mul_left (fun v => Real.sin v^2)
    (mul_ne_zero Real.pi_ne_zero hα.ne')]
  have hh : Real.pi*α*(R- -signalAverageRadius α) =
      Real.pi*α*(R-signalAverageRadius α)+Real.pi := by
    dsimp [signalAverageRadius]
    field_simp
    ring
  rw [hh,integral_sin_sq_pi,smul_eq_mul]
  dsimp [signalAverageRadius]
  field_simp

lemma signalBaseline_nonneg {α : ℝ} (hα : 0 < α) (R : ℝ) :
    0 ≤ signalBaseline α R := by
  apply mul_nonneg (by dsimp [signalAverageRadius]; positivity)
  apply intervalIntegral.integral_nonneg (by linarith [signalAverageRadius_pos hα])
  intro t _
  exact signalSinc_nonneg hα.le (R-t)

/-- The averaging interval has exactly one sine-square period.  In fact the
manuscript's lower tail estimate holds at every point, including the origin. -/
lemma signalBaseline_lower {α : ℝ} (hα : 0 < α) (R : ℝ) :
    1 / (2*Real.pi^2*α*(|R|+signalAverageRadius α)^2) ≤ signalBaseline α R := by
  let a := signalAverageRadius α
  have ha : 0 < a := signalAverageRadius_pos hα
  have hκ : 0 < Real.pi^2*α*(|R|+a)^2 := by positivity
  have hp : 0 < Real.pi^2*α := by positivity
  have hi :
      a ≤ (Real.pi^2*α*(|R|+a)^2) * ∫ t in -a..a, signalSinc α (R-t) := by
    calc
      a = ∫ t in -a..a, Real.sin (Real.pi*α*(R-t))^2 := (signal_sin_sq_average hα R).symm
      _ ≤ _ := ?_
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_mono_on (by linarith)
      ((by fun_prop : Continuous (fun t => Real.sin (Real.pi*α*(R-t))^2)).intervalIntegrable _ _)
      (by exact (continuous_const.mul
        ((smooth_signalSinc α).continuous.comp (by fun_prop))).intervalIntegrable _ _)
    intro t ht
    have ht' : |t| ≤ a := abs_le.mpr ⟨ht.1,ht.2⟩
    have hdist : |R-t| ≤ |R|+a := (abs_sub R t).trans (by linarith)
    have hs : (R-t)^2 ≤ (|R|+a)^2 := by
      simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) (by positivity)).2 hdist
    rw [← signalSinc_denominator hα (R-t)]
    nlinarith [mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hs hp.le)
      (signalSinc_nonneg hα.le (R-t))]
  rw [div_le_iff₀ (by positivity : 0 < 2*Real.pi^2*α*(|R|+signalAverageRadius α)^2)]
  dsimp [signalBaseline]
  change 1 ≤ ((2*a)⁻¹ * ∫ t in -a..a, signalSinc α (R-t)) *
    (2*Real.pi^2*α*(|R|+a)^2)
  field_simp
  nlinarith

lemma shifted_quadratic_bound {a R t : ℝ} (ha : 0 ≤ a) (ht : |t| ≤ a) :
    1+R^2 ≤ 2*(1+a^2)*(1+(R-t)^2) := by
  have ht2 : t^2 ≤ a^2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) ha).2 ht
  nlinarith [sq_nonneg (R-2*t),mul_nonneg (sq_nonneg a) (sq_nonneg (R-t))]

lemma signalBaseline_upper {α : ℝ} (hα : 0 < α) (R : ℝ) :
    signalBaseline α R ≤
      (α+(Real.pi^2*α)⁻¹)* (2*(1+(signalAverageRadius α)^2))* (1+R^2)⁻¹ := by
  let a := signalAverageRadius α
  let C := α+(Real.pi^2*α)⁻¹
  have ha : 0 < a := signalAverageRadius_pos hα
  have hC : 0 < C := by dsimp [C]; positivity
  have hi : (∫ t in -a..a, signalSinc α (R-t)) ≤
      (2*a) * (C * (2*(1+a^2))* (1+R^2)⁻¹) := by
    calc
      _ ≤ ∫ _t in -a..a, C * (2*(1+a^2))* (1+R^2)⁻¹ := by
        apply intervalIntegral.integral_mono_on (by linarith)
          (((smooth_signalSinc α).continuous.comp (by fun_prop)).intervalIntegrable _ _)
          intervalIntegrable_const
        intro t ht
        have hs := shifted_quadratic_bound (R := R) ha.le (abs_le.mpr ⟨ht.1,ht.2⟩)
        have hd : 0 < 1+(R-t)^2 := by positivity
        have hD : 0 < 1+R^2 := by positivity
        calc
          signalSinc α (R-t) ≤ C*(1+(R-t)^2)⁻¹ := signalSinc_decay hα (R-t)
          _ ≤ C*(2*(1+a^2))*(1+R^2)⁻¹ := by
            rw [← div_eq_mul_inv,← div_eq_mul_inv]
            apply (div_le_div_iff₀ hd hD).2
            nlinarith
      _ = _ := by rw [intervalIntegral.integral_const]; simp only [smul_eq_mul]; ring
  dsimp [signalBaseline]
  change (2*a)⁻¹ * _ ≤ C*(2*(1+a^2))*(1+R^2)⁻¹
  rw [inv_mul_le_iff₀ (by positivity : 0 < 2*a)]
  exact hi

lemma integrable_signalBaseline {α : ℝ} (hα : 0 < α) : Integrable (signalBaseline α) := by
  apply (integrable_inv_one_add_sq.const_mul
    ((α+(Real.pi^2*α)⁻¹)*(2*(1+(signalAverageRadius α)^2)))).mono'
    (smooth_signalBaseline α).continuous.aestronglyMeasurable
  filter_upwards [] with R
  rw [Real.norm_eq_abs,abs_of_nonneg (signalBaseline_nonneg hα R)]
  exact signalBaseline_upper hα R

/-! Exact Fourier support, without assuming an interval inversion formula. -/

lemma integrable_signalBox (α : ℝ) : Integrable (signalBox α) := by
  exact (integrableOn_const (isCompact_Icc.measure_ne_top) :
    IntegrableOn (fun _ : ℝ => (1 : ℂ)) (Icc (-α/2) (α/2))).integrable_indicator measurableSet_Icc

lemma fourier_const_mul (c : ℂ) (f : ℝ → ℂ) (v : ℝ) :
    𝓕 (fun x => c*f x) v = c*𝓕 f v := by
  simp only [Real.fourier_real_eq,Circle.smul_def,smul_eq_mul]
  rw [← integral_const_mul]
  congr 1
  funext x
  ring

lemma fourier_signalBox {α : ℝ} (hα : 0 < α) (v : ℝ) :
    𝓕 (signalBox α) v = (α * Real.sinc (Real.pi*α*v) : ℝ) := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  simp only [smul_eq_mul]
  have heq : (fun x : ℝ => Complex.exp (↑(-2*Real.pi*x*v)*Complex.I)*signalBox α x) =
      (Icc (-α/2) (α/2)).indicator (fun x => Complex.exp (↑(-2*Real.pi*x*v)*Complex.I)) := by
    funext x
    by_cases hx : x ∈ Icc (-α/2) (α/2) <;> simp [signalBox,Set.indicator,hx]
  rw [heq,integral_indicator measurableSet_Icc,integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith : -α/2 ≤ α/2)]
  by_cases hv : v = 0
  · simp [hv,intervalIntegral.integral_const]
    ring
  · let c : ℝ := -2*Real.pi*v
    have hc : c ≠ 0 := by dsimp [c]; positivity
    have he : (fun x : ℝ => Complex.exp (↑(-2*Real.pi*x*v)*Complex.I)) =
        (fun x => Complex.exp (↑(c*x)*Complex.I)) := by
      funext x
      congr 1
      dsimp [c]
      push_cast
      ring
    rw [he,intervalIntegral.integral_comp_mul_left (fun x => Complex.exp (↑x*Complex.I)) hc]
    rw [show c*(-α/2) = -(c*(α/2)) by ring,integral_exp_mul_I_eq_sinc]
    rw [show c*(α/2) = -(Real.pi*α*v) by dsimp [c]; ring,Real.sinc_neg]
    dsimp [c]
    simp only [Complex.ofReal_inv,Complex.ofReal_mul,Complex.ofReal_neg,
      Complex.ofReal_ofNat]
    have hvC : (v : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hv
    field_simp [hvC]

lemma signalBox_convolution {α : ℝ} (_hα : 0 < α) (v : ℝ) :
    (signalBox α ⋆[ContinuousLinearMap.mul ℂ ℂ] signalBox α) v =
      (max (α-|v|) 0 : ℝ) := by
  rw [convolution_def]
  change (∫ t : ℝ, signalBox α t * signalBox α (v-t)) = _
  let l := max (-α/2) (v-α/2)
  let u := min (α/2) (v+α/2)
  have heq : (fun t => signalBox α t * signalBox α (v-t)) =
      (Icc l u).indicator (fun _ : ℝ => (1 : ℂ)) := by
    funext t
    have hm : t ∈ Icc l u ↔ t ∈ Icc (-α/2) (α/2) ∧ v-t ∈ Icc (-α/2) (α/2) := by
      dsimp [l,u]
      simp only [mem_Icc,max_le_iff,le_min_iff]
      constructor
      · rintro ⟨⟨h1,h2⟩,h3,h4⟩
        exact ⟨⟨h1,h3⟩,by constructor <;> linarith⟩
      · rintro ⟨⟨h1,h2⟩,h3,h4⟩
        exact ⟨⟨h1,by linarith⟩,h2,by linarith⟩
    by_cases h₁ : t ∈ Icc (-α/2) (α/2) <;>
      by_cases h₂ : v-t ∈ Icc (-α/2) (α/2) <;>
      simp [signalBox,Set.indicator,hm,h₁,h₂]
  rw [heq,integral_indicator measurableSet_Icc,setIntegral_const,Real.volume_real_Icc]
  simp only [Complex.real_smul,mul_one]
  congr 1
  dsimp [l,u]
  by_cases hv : 0 ≤ v
  · rw [abs_of_nonneg hv,min_eq_left (by linarith),show max (-α/2) (v-α/2) = v-α/2 from max_eq_right (by linarith)]
    congr 1
    ring
  · rw [abs_of_nonpos (le_of_not_ge hv),min_eq_right (by linarith),show max (-α/2) (v-α/2) = -α/2 from max_eq_left (by linarith)]
    congr 1
    ring

lemma signalTriangle_eq_convolution {α : ℝ} (hα : 0 < α) :
    signalTriangle α = fun v => (α : ℂ)⁻¹ *
      (signalBox α ⋆[ContinuousLinearMap.mul ℂ ℂ] signalBox α) v := by
  funext v
  rw [signalBox_convolution hα]
  simp [signalTriangle,div_eq_mul_inv,mul_comm]

lemma integrable_signalTriangle {α : ℝ} (hα : 0 < α) : Integrable (signalTriangle α) := by
  rw [signalTriangle_eq_convolution hα]
  exact ((integrable_signalBox α).integrable_convolution
    (ContinuousLinearMap.mul ℂ ℂ) (integrable_signalBox α)).const_mul _

lemma continuous_signalTriangle (α : ℝ) : Continuous (signalTriangle α) := by
  fun_prop [signalTriangle]

lemma fourier_signalTriangle {α : ℝ} (hα : 0 < α) (R : ℝ) :
    𝓕 (signalTriangle α) R = (signalSinc α R : ℝ) := by
  rw [signalTriangle_eq_convolution hα,fourier_const_mul,
    Real.fourier_mul_convolution_eq (integrable_signalBox α) (integrable_signalBox α),
    fourier_signalBox hα]
  dsimp [signalSinc]
  push_cast
  field_simp

lemma fourierInv_signalSinc {α : ℝ} (hα : 0 < α) :
    𝓕⁻ (fun R => (signalSinc α R : ℂ)) = signalTriangle α := by
  have heq : 𝓕 (signalTriangle α) = (fun R => (signalSinc α R : ℂ)) :=
    funext (fourier_signalTriangle hα)
  rw [← heq]
  exact (continuous_signalTriangle α).fourierInv_fourier_eq (integrable_signalTriangle hα)
    (by rw [heq]; exact (integrable_signalSinc hα).ofReal)

lemma fourier_signalSinc {α : ℝ} (hα : 0 < α) (v : ℝ) :
    𝓕 (fun R => (signalSinc α R : ℂ)) v = signalTriangle α v := by
  have h := congrFun (fourierInv_signalSinc hα) (-v)
  rw [Real.fourierInv_eq_fourier_neg,neg_neg] at h
  simpa only [signalTriangle,abs_neg] using h

lemma signalBaseline_eq_convolution {α : ℝ} (hα : 0 < α) :
    (fun R => (signalBaseline α R : ℂ)) = fun R => ((2*signalAverageRadius α : ℝ) : ℂ)⁻¹ *
      (signalBox (2*signalAverageRadius α) ⋆[ContinuousLinearMap.mul ℂ ℂ]
        (fun x => (signalSinc α x : ℂ))) R := by
  funext R
  have ha : 0 < signalAverageRadius α := signalAverageRadius_pos hα
  rw [convolution_def]
  change ↑(signalBaseline α R) = _ * ∫ t, signalBox (2*signalAverageRadius α) t * ↑(signalSinc α (R-t))
  have heq : (fun t => signalBox (2*signalAverageRadius α) t * (signalSinc α (R-t) : ℂ)) =
      (Icc (-signalAverageRadius α) (signalAverageRadius α)).indicator
        (fun t => (signalSinc α (R-t) : ℂ)) := by
    funext t
    have hl : -(2*signalAverageRadius α)/2 = -signalAverageRadius α := by ring
    have hu : 2*signalAverageRadius α/2 = signalAverageRadius α := by ring
    by_cases ht : t ∈ Icc (-signalAverageRadius α) (signalAverageRadius α) <;>
      simp [signalBox,hl,hu,Set.indicator,ht]
  rw [heq,integral_indicator measurableSet_Icc,integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith : -signalAverageRadius α ≤ signalAverageRadius α),
    intervalIntegral.integral_ofReal]
  simp only [signalBaseline,Complex.ofReal_mul,Complex.ofReal_inv]

lemma fourier_signalBaseline {α : ℝ} (hα : 0 < α) (v : ℝ) :
    𝓕 (fun R => (signalBaseline α R : ℂ)) v =
      (Real.sinc (Real.pi*(2*signalAverageRadius α)*v) : ℂ)*signalTriangle α v := by
  rw [signalBaseline_eq_convolution hα,fourier_const_mul]
  have hc := Real.fourier_mul_convolution_eq
    (integrable_signalBox (2*signalAverageRadius α)) (integrable_signalSinc hα).ofReal v
  change 𝓕 (signalBox (2*signalAverageRadius α) ⋆[ContinuousLinearMap.mul ℂ ℂ]
    (fun x => (signalSinc α x : ℂ))) v = _ at hc
  rw [hc,fourier_signalBox (mul_pos (by norm_num) (signalAverageRadius_pos hα)) v]
  have hs := fourier_signalSinc hα v
  change 𝓕 (fun x => (signalSinc α x : ℂ)) v = signalTriangle α v at hs
  erw [hs]
  have ha : (2*signalAverageRadius α : ℝ) ≠ 0 := (mul_pos (by norm_num) (signalAverageRadius_pos hα)).ne'
  have haC : ((2*signalAverageRadius α : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ha
  have ha0 : (signalAverageRadius α : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (signalAverageRadius_pos hα).ne'
  push_cast
  field_simp [ha0]

lemma integral_signalBaseline {α : ℝ} (hα : 0 < α) : ∫ R, signalBaseline α R = 1 := by
  have h := fourier_signalBaseline hα 0
  simp [Real.fourier_real_eq,signalTriangle,max_eq_left hα.le,hα.ne'] at h
  apply Complex.ofReal_injective
  calc
    ((∫ R, signalBaseline α R : ℝ) : ℂ) = ∫ R, (signalBaseline α R : ℂ) :=
      (integral_ofReal (𝕜 := ℂ)).symm
    _ = (1 : ℂ) := h
    _ = ((1 : ℝ) : ℂ) := rfl

lemma signalBaseline_fourier_support {α v : ℝ} (hα : 0 < α) (hv : α ≤ |v|) :
    𝓕 (fun R => (signalBaseline α R : ℂ)) v = 0 := by
  rw [fourier_signalBaseline hα]
  simp [signalTriangle,max_eq_right (sub_nonpos.mpr hv)]

theorem signalBaseline_quadratic_tails {α : ℝ} (hα : 0 < α) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ R : ℝ,
      c/(1+R^2) ≤ signalBaseline α R ∧ signalBaseline α R ≤ C/(1+R^2) := by
  let a := signalAverageRadius α
  have ha : 0 < a := signalAverageRadius_pos hα
  let c := (4*Real.pi^2*α*(1+a^2))⁻¹
  let C := (α+(Real.pi^2*α)⁻¹)*(2*(1+a^2))
  refine ⟨c,C,by dsimp [c]; positivity,by dsimp [C]; positivity,fun R => ⟨?_,?_⟩⟩
  · apply le_trans ?_ (signalBaseline_lower hα R)
    change c/(1+R^2) ≤ 1/(2*Real.pi^2*α*(|R|+a)^2)
    have hD : 0 < 2*Real.pi^2*α*(|R|+a)^2 := by positivity
    have hbig : (|R|+a)^2 ≤ 2*(1+a^2)*(1+R^2) := by
      nlinarith [sq_nonneg (|R|-a),sq_abs R,mul_nonneg (sq_nonneg a) (sq_nonneg R)]
    have hp : 0 < 2*Real.pi^2*α := by positivity
    dsimp [c]
    rw [← one_div,div_div]
    apply one_div_le_one_div_of_le hD
    nlinarith [mul_le_mul_of_nonneg_left hbig hp.le]
  · exact (signalBaseline_upper hα R).trans_eq (by dsimp [C,a]; rw [div_eq_mul_inv])

open scoped ComplexConjugate

lemma fourier_hermitian_real (d : ℝ → ℂ) (hd : ∀ v, d (-v) = conj (d v)) (R : ℝ) :
    conj (𝓕 d R) = 𝓕 d R := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  simp only [smul_eq_mul]
  rw [← integral_conj]
  calc
    (∫ v : ℝ, conj (Complex.exp (↑(-2*Real.pi*v*R)*Complex.I)*d v)) =
        ∫ v : ℝ, Complex.exp (↑(-2*Real.pi*(-v)*R)*Complex.I)*d (-v) := by
      apply integral_congr_ae
      filter_upwards [] with v
      rw [map_mul,← Complex.exp_conj,hd]
      congr 2
      simp only [map_mul,Complex.conj_ofReal,Complex.conj_I]
      push_cast
      ring
    _ = ∫ v : ℝ, Complex.exp (↑(-2*Real.pi*v*R)*Complex.I)*d v :=
      integral_neg_eq_self (fun v : ℝ => Complex.exp (↑(-2*Real.pi*v*R)*Complex.I)*d v) volume

lemma signalInverse_complex {d : ℝ → ℂ} (hd : ∀ v, d (-v) = conj (d v)) (R : ℝ) :
    (signalInverse d R : ℂ) = 𝓕 d R :=
  Complex.conj_eq_iff_re.mp (fourier_hermitian_real d hd R)

lemma signalInverse_contDiff {d : ℝ → ℂ} (hd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) d)
    (hc : HasCompactSupport d) : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (signalInverse d) := by
  let f := hc.toSchwartzMap hd
  exact Complex.reCLM.contDiff.comp ((𝓕 f).smooth ⊤)

lemma signalInverse_integrable {d : ℝ → ℂ} (hd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) d)
    (hc : HasCompactSupport d) : Integrable (signalInverse d) := by
  let f := hc.toSchwartzMap hd
  exact Complex.reCLM.integrable_comp (𝓕 f).integrable

lemma signalInverse_inversion {d : ℝ → ℂ} (hd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) d)
    (hc : HasCompactSupport d) (hreal : ∀ v, d (-v) = conj (d v)) :
    𝓕⁻ (fun R => (signalInverse d R : ℂ)) = d := by
  have heq : (fun R => (signalInverse d R : ℂ)) = 𝓕 d :=
    funext (signalInverse_complex hreal)
  rw [heq]
  let f := hc.toSchwartzMap hd
  exact hd.continuous.fourierInv_fourier_eq (f.integrable) (𝓕 f).integrable

lemma integral_signalInverse {d : ℝ → ℂ} (hd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) d)
    (hc : HasCompactSupport d) (hreal : ∀ v, d (-v) = conj (d v)) (h0 : d 0 = 0) :
    ∫ R, signalInverse d R = 0 := by
  have h := congrFun (signalInverse_inversion hd hc hreal) 0
  simp [Real.fourierInv_eq,h0] at h
  apply Complex.ofReal_injective
  calc
    ((∫ R, signalInverse d R : ℝ) : ℂ) = ∫ R, (signalInverse d R : ℂ) :=
      (integral_ofReal (𝕜 := ℂ)).symm
    _ = 0 := h
    _ = ((0 : ℝ) : ℂ) := rfl

lemma signalInverse_quadratic_bound {d : ℝ → ℂ} (hd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) d)
    (hc : HasCompactSupport d) : ∃ G : ℝ, 0 ≤ G ∧ ∀ R, (1+R^2)*|signalInverse d R| ≤ G := by
  let f := hc.toSchwartzMap hd
  let g := 𝓕 f
  refine ⟨SchwartzMap.seminorm ℂ 0 0 g + SchwartzMap.seminorm ℂ 2 0 g,by positivity,?_⟩
  intro R
  have h0 := g.norm_le_seminorm ℂ R
  have h2 := g.norm_pow_mul_le_seminorm ℂ 2 R
  have hr : |signalInverse d R| ≤ ‖g R‖ := Complex.abs_re_le_norm (g R)
  rw [Real.norm_eq_abs,sq_abs] at h2
  nlinarith [sq_nonneg R,mul_le_mul_of_nonneg_left hr (sq_nonneg R)]

lemma conj_stdAddChar {P : ℕ} [NeZero P] (h : ZMod P) :
    conj (ZMod.stdAddChar h) = ZMod.stdAddChar (-h) := by
  rw [ZMod.stdAddChar_apply,ZMod.stdAddChar_apply,AddChar.map_neg_eq_inv,
    Circle.coe_inv_eq_conj]

lemma conj_signalRamanujanC {P : ℕ} [NeZero P] (h : ZMod P) :
    conj (signalRamanujanC P h) = signalRamanujanC P h := by
  classical
  simp only [signalRamanujanC,map_sum,conj_stdAddChar,neg_neg]
  exact Fintype.sum_equiv (Equiv.neg ((ZMod P)ˣ)) _ _ (by
    intro u
    simp [Equiv.neg_apply,Units.val_neg,neg_mul])

lemma signalRamanujan_complex {P : ℕ} [NeZero P] (h : ZMod P) :
    (signalRamanujan P h : ℂ) = signalRamanujanC P h :=
  Complex.conj_eq_iff_re.mp (conj_signalRamanujanC h)

lemma signalRamanujan_bound {P : ℕ} [NeZero P] (h : ZMod P) :
    |signalRamanujan P h| ≤ Fintype.card (ZMod P)ˣ := by
  apply (Complex.abs_re_le_norm (signalRamanujanC P h)).trans
  calc
    ‖signalRamanujanC P h‖ ≤ ∑ u : (ZMod P)ˣ, ‖ZMod.stdAddChar (-(u.val*h))‖ :=
      norm_sum_le _ _
    _ = Fintype.card (ZMod P)ˣ := by simp [ZMod.stdAddChar_apply,Circle.norm_coe]

lemma sum_stdAddChar_mul {P : ℕ} [NeZero P] (k : ZMod P) :
    ∑ h : ZMod P, ZMod.stdAddChar (k*h) = if k = 0 then (P : ℂ) else 0 := by
  classical
  split_ifs with hk
  · simp [hk]
  · exact AddChar.sum_eq_zero_of_ne_one (ZMod.isPrimitive_stdAddChar P hk)

lemma signalRamanujan_selector {P : ℕ} [NeZero P] (k : ZMod P) :
    ∑ h : ZMod P, signalRamanujanC P h * ZMod.stdAddChar (k*h) =
      if IsUnit k then (P : ℂ) else 0 := by
  classical
  simp only [signalRamanujanC,Finset.sum_mul]
  rw [Finset.sum_comm]
  have heq (u : (ZMod P)ˣ) : ∑ h : ZMod P,
      ZMod.stdAddChar (-(u.val*h))*ZMod.stdAddChar (k*h) =
        if u.val = k then (P : ℂ) else 0 := by
    simp_rw [← AddChar.map_add_eq_mul,show ∀ h : ZMod P, -(u.val*h)+k*h = (k-u.val)*h by intro; ring]
    rw [sum_stdAddChar_mul]
    simp [sub_eq_zero,eq_comm]
  simp_rw [heq]
  split_ifs with hk
  · rw [Finset.sum_eq_single hk.unit]
    · simp
    · intro u _ hne
      simp only [ite_eq_right_iff]
      intro hu
      exfalso
      exact hne (Units.ext (hu.trans hk.unit_spec.symm))
    · simp
  · apply Finset.sum_eq_zero
    intro u _
    rw [ite_eq_right]
    intro hu
    exact hk (hu ▸ u.isUnit)

lemma signalJoint_smooth {α : ℝ} (_hα : 0 < α) (γ : ℝ) {d : ℝ → ℂ}
    (hd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) d) (hc : HasCompactSupport d)
    (P : ℕ) [NeZero P] (h : ZMod P) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (signalJoint α γ d P h) := by
  exact ((smooth_signalBaseline α).add
    (contDiff_const.mul (signalInverse_contDiff hd hc))).div_const _

lemma signalJoint_integrable {α : ℝ} (hα : 0 < α) (γ : ℝ) {d : ℝ → ℂ}
    (hd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) d) (hc : HasCompactSupport d)
    (P : ℕ) [NeZero P] (h : ZMod P) : Integrable (signalJoint α γ d P h) :=
  ((integrable_signalBaseline hα).add
    ((signalInverse_integrable hd hc).const_mul (γ*signalRamanujan P h))).div_const _

lemma integral_signalJoint {α : ℝ} (hα : 0 < α) (γ : ℝ) {d : ℝ → ℂ}
    (hd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) d) (hc : HasCompactSupport d)
    (hr : ∀ v, d (-v) = conj (d v)) (h0 : d 0 = 0)
    (P : ℕ) [NeZero P] (h : ZMod P) : ∫ R, signalJoint α γ d P h R = 1/P := by
  simp only [signalJoint]
  rw [integral_div,integral_add (integrable_signalBaseline hα)
    ((signalInverse_integrable hd hc).const_mul _),integral_const_mul,
    integral_signalBaseline hα,integral_signalInverse hd hc hr h0]
  ring

lemma fourier_add_integrable {f g : ℝ → ℂ} (hf : Integrable f) (hg : Integrable g) (v : ℝ) :
    𝓕 (fun x => f x+g x) v = 𝓕 f v+𝓕 g v := by
  simp only [Real.fourier_eq,smul_add]
  rw [integral_add ((Real.fourierIntegral_convergent_iff v).2 hf)
    ((Real.fourierIntegral_convergent_iff v).2 hg)]

lemma fourierInv_add_integrable {f g : ℝ → ℂ} (hf : Integrable f) (hg : Integrable g) (v : ℝ) :
    𝓕⁻ (fun x => f x+g x) v = 𝓕⁻ f v+𝓕⁻ g v := by
  simp only [Real.fourierInv_eq_fourier_neg,fourier_add_integrable hf hg]

lemma fourierInv_const_mul (c : ℂ) (f : ℝ → ℂ) (v : ℝ) :
    𝓕⁻ (fun x => c*f x) v = c*𝓕⁻ f v := by
  simp only [Real.fourierInv_eq_fourier_neg,fourier_const_mul]

lemma fourierInv_signalJoint {α : ℝ} (hα : 0 < α) (γ : ℝ) {d : ℝ → ℂ}
    (hd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) d) (hc : HasCompactSupport d)
    (hr : ∀ v, d (-v) = conj (d v)) (P : ℕ) [NeZero P] (h : ZMod P) (v : ℝ) :
    𝓕⁻ (fun R => (signalJoint α γ d P h R : ℂ)) v =
      (P : ℂ)⁻¹ * (𝓕⁻ (fun R => (signalBaseline α R : ℂ)) v+
        (γ : ℂ)*signalRamanujanC P h*d v) := by
  have heq : (fun R => (signalJoint α γ d P h R : ℂ)) =
      fun R => (P : ℂ)⁻¹*((signalBaseline α R : ℂ)+
        ((γ : ℂ)*signalRamanujanC P h)*(signalInverse d R : ℂ)) := by
    funext R
    simp only [signalJoint,div_eq_mul_inv,Complex.ofReal_mul,Complex.ofReal_add,
      Complex.ofReal_inv,Complex.ofReal_natCast,signalRamanujan_complex]
    ring
  rw [heq,fourierInv_const_mul]
  erw [fourierInv_add_integrable
    (integrable_signalBaseline hα).ofReal (((signalInverse_integrable hd hc).ofReal).const_mul _),
    fourierInv_const_mul,signalInverse_inversion hd hc hr]
  rfl

/-- Exact positive-exponent joint Fourier transform, not a conditional moment assumption. -/
theorem signalJoint_fourier {α : ℝ} (hα : 0 < α) (γ : ℝ) {d : ℝ → ℂ}
    (hd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) d) (hc : HasCompactSupport d)
    (hr : ∀ v, d (-v) = conj (d v)) (P : ℕ) [NeZero P] (v : ℝ) (k : ZMod P) :
    ∑ h : ZMod P, (𝓕⁻ (fun R => (signalJoint α γ d P h R : ℂ)) v)*
      ZMod.stdAddChar (k*h) =
      (if k = 0 then 𝓕⁻ (fun R => (signalBaseline α R : ℂ)) v else 0)+
      (if IsUnit k then (γ : ℂ)*d v else 0) := by
  classical
  simp_rw [fourierInv_signalJoint hα γ hd hc hr]
  calc
    _ = (P : ℂ)⁻¹ * ((𝓕⁻ (fun R => (signalBaseline α R : ℂ)) v)*
          (∑ h : ZMod P, ZMod.stdAddChar (k*h))+
        (γ : ℂ)*d v*(∑ h : ZMod P, signalRamanujanC P h*ZMod.stdAddChar (k*h))) := by
      simp only [mul_add,add_mul,Finset.mul_sum,Finset.sum_add_distrib]
      congr 1
      all_goals apply Finset.sum_congr rfl; intro h _; ring
    _ = _ := by
      rw [sum_stdAddChar_mul,signalRamanujan_selector]
      have hP : (P : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne P
      split_ifs <;> field_simp [hP] <;> ring

/-- Small strengths give the actual positive law, with the source's quantitative
    two-sided domination. The choice is independent of the angular scale B. -/
theorem signalJoint_positive_strength {α : ℝ} (hα : 0 < α) {d : ℝ → ℂ}
    (hd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) d) (hc : HasCompactSupport d)
    (P : ℕ) [NeZero P] :
    ∃ γ₀ : ℝ, 0 < γ₀ ∧ ∀ γ : ℝ, 0 ≤ γ → γ ≤ γ₀ →
      (∀ h : ZMod P, ∀ R : ℝ, signalBaseline α R/(2*P) ≤ signalJoint α γ d P h R ∧
        signalJoint α γ d P h R ≤ 3*signalBaseline α R/(2*P)) ∧
      ∀ v : ℝ, 2*γ*‖d v‖ ≤ 1/2 := by
  obtain ⟨c,C,hc0,_hC,htail⟩ := signalBaseline_quadratic_tails hα
  obtain ⟨G,hG,hgb⟩ := signalInverse_quadratic_bound hd hc
  let Cu : ℝ := Fintype.card (ZMod P)ˣ
  have hCu : 0 ≤ Cu := by dsimp [Cu]; positivity
  let f := hc.toSchwartzMap hd
  let D := SchwartzMap.seminorm ℂ 0 0 f
  have hD : 0 ≤ D := apply_nonneg (SchwartzMap.seminorm ℂ 0 0) f
  have hdD (v : ℝ) : ‖d v‖ ≤ D := f.norm_le_seminorm ℂ v
  let γ₀ := min (c/(2*(Cu*G+1))) (1/(4*(D+1)))
  have hCG : 0 < Cu*G+1 := by positivity
  refine ⟨γ₀,by dsimp [γ₀]; positivity,fun γ hγ hγ₀ => ⟨?_,?_⟩⟩
  · intro h R
    have hsmall : γ*(Cu*G+1) ≤ c/2 := by
      have hh := hγ₀.trans (min_le_left (c/(2*(Cu*G+1))) (1/(4*(D+1))))
      have hh' := (le_div_iff₀ (by positivity : 0 < 2*(Cu*G+1))).mp hh
      nlinarith
    have hgb' := hgb R
    have hcb := signalRamanujan_bound h
    have hb : |γ*signalRamanujan P h*signalInverse d R| ≤ signalBaseline α R/2 := by
      have hprod : (1+R^2)*|γ*signalRamanujan P h*signalInverse d R| ≤ γ*Cu*G := by
        rw [abs_mul,abs_mul,abs_of_nonneg hγ]
        calc
          _ = γ*|signalRamanujan P h| *((1+R^2)*|signalInverse d R| ) := by ring
          _ ≤ γ*Cu*G := by gcongr
      have ht := (htail R).1
      have hpos : 0 < 1+R^2 := by positivity
      have ht' := (div_le_iff₀ hpos).mp ht
      nlinarith
    have hP : (0 : ℝ) < P := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne P)
    obtain ⟨hl,hu⟩ := abs_le.mp hb
    dsimp [signalJoint]
    constructor
    · rw [div_le_div_iff₀ (by positivity : 0 < 2*(P : ℝ)) hP]
      nlinarith
    · rw [div_le_div_iff₀ hP (by positivity : 0 < 2*(P : ℝ))]
      nlinarith
  · intro v
    have hh := hγ₀.trans (min_le_right (c/(2*(Cu*G+1))) (1/(4*(D+1))))
    have hh' := (le_div_iff₀ (by positivity : 0 < 4*(D+1))).mp hh
    have hbd := mul_le_mul_of_nonneg_left (hdD v) hγ
    nlinarith

lemma dvd_signalPrimeProduct {p L : ℕ} (hp : p.Prime) (hL : p ≤ L) :
    p ∣ signalPrimeProduct L := by
  exact Finset.dvd_prod_of_mem (fun p : ℕ => p)
    (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),hp⟩)

lemma signal_sieve_no_unit {L ℓ : ℕ} (hℓ : 2 ≤ ℓ) (hL : ℓ ≤ L)
    (m : ZMod (signalPrimeProduct L)) : ¬ IsUnit ((ℓ : ZMod (signalPrimeProduct L))*m) := by
  intro h
  have hu := (ZMod.isUnit_iff_coprime ℓ (signalPrimeProduct L)).mp
    (isUnit_of_mul_isUnit_left h)
  have hp := Nat.minFac_prime (n := ℓ) (by omega)
  exact (Nat.not_coprime_of_dvd_of_dvd hp.one_lt (Nat.minFac_dvd ℓ)
    (dvd_signalPrimeProduct hp ((Nat.minFac_le (by omega)).trans hL))) hu

/-- The exact ideal integer moments, with only the first nonzero harmonic. -/
theorem signalJoint_sieved_moments {α b D x : ℝ} (hα : 0 < α) (hαb : α < b)
    (hb : 0 < b) (hx : b ≤ |x|) {L : ℕ} (hL : D/b < L)
    {d : ℝ → ℂ} (hd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) d)
    (hc : HasCompactSupport d) (hr : ∀ v, d (-v) = conj (d v))
    (hs : Function.support d ⊆ Icc (-D) D) (γ : ℝ)
    (m : ZMod (signalPrimeProduct L)) (ℓ : ℕ) (hℓ : 1 ≤ ℓ) :
    ∑ h : ZMod (signalPrimeProduct L),
      (𝓕⁻ (fun R => (signalJoint α γ d (signalPrimeProduct L) h R : ℂ))) (ℓ*x)*
        ZMod.stdAddChar (((ℓ : ZMod (signalPrimeProduct L))*m)*h) =
      if ℓ = 1 ∧ IsUnit m then (γ : ℂ)*d x else 0 := by
  rw [signalJoint_fourier hα γ hd hc hr]
  have hℓr : (1 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
  have hav : α ≤ |(ℓ : ℝ)*x| := by
    rw [abs_mul,abs_of_nonneg (Nat.cast_nonneg ℓ)]
    nlinarith [abs_nonneg x]
  have hbase : 𝓕⁻ (fun R => (signalBaseline α R : ℂ)) ((ℓ : ℝ)*x) = 0 := by
    rw [Real.fourierInv_eq_fourier_neg]
    exact signalBaseline_fourier_support hα (by simpa only [abs_neg] using hav)
  rw [hbase]
  simp only [ite_self,zero_add]
  by_cases he : ℓ = 1
  · subst ℓ
    simp
  · rw [ite_eq_right (show ¬ (ℓ = 1 ∧ IsUnit m) from fun h => he h.1)]
    by_cases hd0 : d ((ℓ : ℝ)*x) = 0
    · simp [hd0]
    · have hv := hs hd0
      have ha : |(ℓ : ℝ)*x| ≤ D := abs_le.mpr hv
      rw [abs_mul,abs_of_nonneg (Nat.cast_nonneg ℓ)] at ha
      have hbound : (ℓ : ℝ) < L := by
        have hcL := (div_lt_iff₀ hb).mp hL
        nlinarith
      have hℓL : ℓ ≤ L := (by exact_mod_cast hbound : ℓ < L).le
      rw [ite_eq_right (signal_sieve_no_unit (by omega) hℓL m)]

/-- All choices of the positive-law construction precede the angular scale.
    The interval support used below is the exact compact support condition on d. -/
theorem exists_signal_positive_law {b D : ℝ} (hb : 0 < b)
    {d : ℝ → ℂ} (hd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) d)
    (hc : HasCompactSupport d) (hr : ∀ v, d (-v) = conj (d v))
    (h0 : d 0 = 0) (hs : Function.support d ⊆ Icc (-D) D) :
    ∃ α : ℝ, ∃ L : ℕ, ∃ γ₀ : ℝ,
      0 < α ∧ α < b/2 ∧ 2 ≤ L ∧ D/b < L ∧ 0 < γ₀ ∧
      ∀ γ : ℝ, 0 < γ → γ ≤ γ₀ →
        (∀ h : ZMod (signalPrimeProduct L),
          ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (signalJoint α γ d (signalPrimeProduct L) h) ∧
          Integrable (signalJoint α γ d (signalPrimeProduct L) h) ∧
          (∫ R, signalJoint α γ d (signalPrimeProduct L) h R) = 1/(signalPrimeProduct L) ∧
          ∀ R, signalBaseline α R/(2*(signalPrimeProduct L)) ≤
              signalJoint α γ d (signalPrimeProduct L) h R ∧
            signalJoint α γ d (signalPrimeProduct L) h R ≤
              3*signalBaseline α R/(2*(signalPrimeProduct L))) ∧
        (∀ v, 2*γ*‖d v‖ ≤ 1/2) ∧
        ∀ x, b ≤ |x| → ∀ m : ZMod (signalPrimeProduct L), ∀ ℓ : ℕ, 1 ≤ ℓ →
          ∑ h : ZMod (signalPrimeProduct L),
            (𝓕⁻ (fun R => (signalJoint α γ d (signalPrimeProduct L) h R : ℂ))) (ℓ*x)*
              ZMod.stdAddChar (((ℓ : ZMod (signalPrimeProduct L))*m)*h) =
            if ℓ = 1 ∧ IsUnit m then (γ : ℂ)*d x else 0 := by
  obtain ⟨L,hL⟩ := exists_nat_gt (max 2 (D/b))
  have hL2 : 2 ≤ L := by
    have hh : (2 : ℝ) < L := (le_max_left _ _).trans_lt hL
    exact_mod_cast hh.le
  have hLD : D/b < L := (le_max_right _ _).trans_lt hL
  have hα : 0 < b/4 := by positivity
  obtain ⟨γ₀,hγ₀,hγ⟩ := signalJoint_positive_strength hα hd hc (signalPrimeProduct L)
  refine ⟨b/4,L,γ₀,hα,by linarith,hL2,hLD,hγ₀,?_⟩
  intro γ hγpos hγle
  obtain ⟨hbound,hdBound⟩ := hγ γ hγpos.le hγle
  refine ⟨?_,hdBound,?_⟩
  · intro h
    exact ⟨signalJoint_smooth hα γ hd hc _ h,signalJoint_integrable hα γ hd hc _ h,
      integral_signalJoint hα γ hd hc hr h0 _ h,hbound h⟩
  · intro x hx m ℓ hℓ
    exact signalJoint_sieved_moments hα (by linarith) hb hx hLD hd hc hr hs γ m ℓ hℓ

end ThreeTorus

noncomputable section
open MeasureTheory Set Filter
open scoped Topology FourierTransform
namespace ThreeTorus

lemma integrable_affineDensity {q : ℝ → ℝ} (hq : Integrable q) {a : ℝ}
    (ha : a ≠ 0) (b : ℝ) : Integrable (affineDensity q a b) := by
  exact ((integrable_comp_mul_left_iff (fun x => q (x+b)) ha).2
    (hq.comp_add_right b)).const_mul a

lemma integral_affineDensity {q : ℝ → ℝ} {a : ℝ} (ha : 0 < a) (b : ℝ) :
    (∫ y, affineDensity q a b y) = ∫ y, q y := by
  unfold affineDensity
  rw [integral_const_mul,Measure.integral_comp_mul_left (fun y => q (y+b)) a,
    integral_add_right_eq_self]
  simp only [smul_eq_mul,abs_of_pos (inv_pos.mpr ha)]
  field_simp

lemma fourierInv_affineDensity {q : ℝ → ℝ} {a : ℝ} (ha : 0 < a) (b v : ℝ) :
    𝓕⁻ (fun y => (affineDensity q a b y : ℂ)) v =
      Complex.exp ((-2*Real.pi*(v*b/a) : ℝ)*Complex.I)*
        𝓕⁻ (fun y => (q y : ℂ)) (v/a) := by
  simp only [Real.fourierInv_eq_fourier_neg,Real.fourier_real_eq_integral_exp_smul,
    smul_eq_mul]
  let f : ℝ → ℂ := fun x =>
    Complex.exp (((2*Real.pi*v/a)*x : ℝ)*Complex.I)*(q x : ℂ)
  have hf : ∀ y : ℝ,
      Complex.exp (((-2*Real.pi*y*(-v)) : ℝ)*Complex.I)*
        (affineDensity q a b y : ℂ) =
      (a : ℂ)*(Complex.exp ((-2*Real.pi*(v*b/a) : ℝ)*Complex.I)*f (a*y+b)) := by
    intro y
    have hex : (-2*Real.pi*y*(-v)) =
        -2*Real.pi*(v*b/a)+(2*Real.pi*v/a)*(a*y+b) := by
      field_simp [ha.ne']
      ring
    dsimp only [affineDensity,f]
    rw [hex,Complex.ofReal_add,add_mul,Complex.exp_add]
    simp only [Complex.ofReal_mul]
    ring
  simp_rw [hf]
  rw [integral_const_mul,integral_const_mul,Measure.integral_comp_mul_left (fun y => f (y+b)) a,
    integral_add_right_eq_self]
  simp only [abs_of_pos (inv_pos.mpr ha),Complex.real_smul,Complex.ofReal_inv]
  have hg : (fun y : ℝ => Complex.exp (((-2*Real.pi*y*(-(v/a))) : ℝ)*Complex.I)*
      (q y : ℂ)) = f := by
    funext y
    dsimp [f]
    congr 2
    ring_nf
  rw [hg]
  field_simp [show (a : ℂ) ≠ 0 from Complex.ofReal_ne_zero.mpr ha.ne']

lemma affine_square_bound (a b y : ℝ) :
    1+(a*y+b)^2 ≤ (1+2*a^2+2*b^2)*(1+y^2) := by
  nlinarith [sq_nonneg (a*y-b),sq_nonneg a,sq_nonneg y,
    mul_nonneg (sq_nonneg b) (sq_nonneg y)]

lemma affineDensity_quadratic_tails {q : ℝ → ℝ} {a c C : ℝ}
    (ha : 0 < a) (hc : 0 < c) (hC : 0 < C)
    (hq : ∀ y, c/(1+y^2) ≤ q y ∧ q y ≤ C/(1+y^2)) (b : ℝ) :
    ∃ c' C' : ℝ, 0 < c' ∧ 0 < C' ∧ ∀ y,
      c'/(1+y^2) ≤ affineDensity q a b y ∧
      affineDensity q a b y ≤ C'/(1+y^2) := by
  let K := 1+2*a^2+2*b^2
  let K' := 1+2*(a⁻¹)^2+2*(-b/a)^2
  have hK : 0 < K := by dsimp [K]; positivity
  have hK' : 0 < K' := by dsimp [K']; positivity
  refine ⟨a*c/K,a*C*K',by positivity,by positivity,fun y => ⟨?_,?_⟩⟩
  · have hbnd := affine_square_bound a b y
    have hp : 0 < 1+y^2 := by positivity
    have hp' : 0 < 1+(a*y+b)^2 := by positivity
    have he : a*c/K/(1+y^2) ≤ a*(c/(1+(a*y+b)^2)) := by
      rw [div_div,← mul_div_assoc]
      exact div_le_div_of_nonneg_left (by positivity) hp' (by simpa [K] using hbnd)
    exact he.trans (mul_le_mul_of_nonneg_left (hq _).1 ha.le)
  · have hbnd := affine_square_bound a⁻¹ (-b/a) (a*y+b)
    have he : a⁻¹*(a*y+b)+ -b/a = y := by field_simp [ha.ne']; ring
    rw [he] at hbnd
    have hp : 0 < 1+y^2 := by positivity
    have hp' : 0 < 1+(a*y+b)^2 := by positivity
    apply (mul_le_mul_of_nonneg_left (hq _).2 ha.le).trans
    rw [← mul_div_assoc,div_le_div_iff₀ hp' hp]
    have hh := mul_le_mul_of_nonneg_left hbnd (show 0 ≤ a*C by positivity)
    dsimp [K'] at *
    nlinarith

end ThreeTorus

noncomputable section
open MeasureTheory Set Filter
open scoped Topology FourierTransform
namespace ThreeTorus

lemma finite_sum_quadratic_tails {ι : Type*} [Fintype ι] [Nonempty ι]
    {q : ι → ℝ → ℝ}
    (hq : ∀ i, ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ y,
      c/(1+y^2) ≤ q i y ∧ q i y ≤ C/(1+y^2)) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ y,
      c/(1+y^2) ≤ ∑ i, q i y ∧ ∑ i, q i y ≤ C/(1+y^2) := by
  classical
  choose c C hc hC hbound using hq
  refine ⟨∑ i, c i,∑ i, C i,
    Finset.sum_pos (fun i _ => hc i) Finset.univ_nonempty,
    Finset.sum_pos (fun i _ => hC i) Finset.univ_nonempty,?_⟩
  intro y
  constructor
  · rw [Finset.sum_div]
    exact Finset.sum_le_sum fun i _ => (hbound i y).1
  · rw [Finset.sum_div]
    exact Finset.sum_le_sum fun i _ => (hbound i y).2

lemma signalJitter_affine (α γ : ℝ) (d : ℝ → ℂ) (P : ℕ) [NeZero P]
    (B c y : ℝ) :
    signalJitter α γ d P B c y =
      ∑ h : ZMod P, affineDensity (signalJoint α γ d P h) (c*B) (-B*h.val/P) y := by
  classical
  simp only [signalJitter,Finset.mul_sum,affineDensity]
  apply Finset.sum_congr rfl
  intro h _
  congr 2
  ring

lemma signalJitter_smooth {α : ℝ} (hα : 0 < α) (γ : ℝ) {d : ℝ → ℂ}
    (hd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) d) (hc : HasCompactSupport d)
    (P : ℕ) [NeZero P] (B c : ℝ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (signalJitter α γ d P B c) := by
  classical
  apply contDiff_const.mul
  apply ContDiff.sum
  intro h _
  exact (signalJoint_smooth hα γ hd hc P h).comp (by fun_prop)

lemma signalJitter_integrable {α B c : ℝ} (hα : 0 < α) (hB : 0 < B) (hc : 0 < c)
    (γ : ℝ) {d : ℝ → ℂ} (hd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) d)
    (hcomp : HasCompactSupport d) (P : ℕ) [NeZero P] :
    Integrable (signalJitter α γ d P B c) := by
  simp only [show signalJitter α γ d P B c = fun y =>
    ∑ h : ZMod P, affineDensity (signalJoint α γ d P h) (c*B) (-B*h.val/P) y from
      funext (signalJitter_affine α γ d P B c)]
  exact integrable_finsetSum _ (fun h _ => integrable_affineDensity
    (signalJoint_integrable hα γ hd hcomp P h) (mul_pos hc hB).ne' _)

lemma integral_signalJitter {α B c : ℝ} (hα : 0 < α) (hB : 0 < B) (hc : 0 < c)
    (γ : ℝ) {d : ℝ → ℂ} (hd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) d)
    (hcomp : HasCompactSupport d) (hr : ∀ v, d (-v) = starRingEnd ℂ (d v))
    (h0 : d 0 = 0) (P : ℕ) [NeZero P] :
    (∫ y, signalJitter α γ d P B c y) = 1 := by
  simp_rw [signalJitter_affine]
  rw [integral_finsetSum _ (fun h _ => integrable_affineDensity
    (signalJoint_integrable hα γ hd hcomp P h) (mul_pos hc hB).ne' _)]
  simp_rw [integral_affineDensity (mul_pos hc hB),integral_signalJoint hα γ hd hcomp hr h0]
  simp [ZMod.card P,NeZero.ne P]

lemma signalJitter_quadratic_tails {α B c γ : ℝ} (hα : 0 < α) (hB : 0 < B)
    (hc : 0 < c) {d : ℝ → ℂ} (P : ℕ) [NeZero P]
    (hbound : ∀ h R, signalBaseline α R/(2*P) ≤ signalJoint α γ d P h R ∧
      signalJoint α γ d P h R ≤ 3*signalBaseline α R/(2*P)) :
    ∃ a A : ℝ, 0 < a ∧ 0 < A ∧ ∀ y,
      a/(1+y^2) ≤ signalJitter α γ d P B c y ∧
      signalJitter α γ d P B c y ≤ A/(1+y^2) := by
  obtain ⟨a,A,ha,hA,hq⟩ := signalBaseline_quadratic_tails hα
  have hP : (0 : ℝ) < P := Nat.cast_pos.mpr (NeZero.pos P)
  have ht (h : ZMod P) : ∀ y, (a/(2*P))/(1+y^2) ≤ signalJoint α γ d P h y ∧
      signalJoint α γ d P h y ≤ (3*A/(2*P))/(1+y^2) := by
    intro y
    constructor
    · have hh := div_le_div_of_nonneg_right (hq y).1 (show 0 ≤ 2*(P:ℝ) by positivity)
      have hh' : a/(2*P)/(1+y^2) ≤ signalBaseline α y/(2*P) := by
        convert hh using 1 <;> first | rfl | ring
      exact hh'.trans (hbound h y).1
    · have hh := div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hq y).2 (show 0 ≤ (3:ℝ) by norm_num))
        (show 0 ≤ 2*(P:ℝ) by positivity)
      exact (hbound h y).2.trans (by convert hh using 1; ring)
  obtain ⟨a',A',ha',hA',hbnd⟩ := finite_sum_quadratic_tails
    (fun h : ZMod P => affineDensity_quadratic_tails (mul_pos hc hB)
      (show 0 < a/(2*P) by positivity) (show 0 < 3*A/(2*P) by positivity) (ht h)
      (-B*h.val/P))
  exact ⟨a',A',ha',hA',fun y => by simpa only [signalJitter_affine] using hbnd y⟩

lemma signalJitter_pos {α B c γ : ℝ} (hα : 0 < α) (hB : 0 < B)
    (hc : 0 < c) {d : ℝ → ℂ} (P : ℕ) [NeZero P]
    (hbound : ∀ h R, signalBaseline α R/(2*P) ≤ signalJoint α γ d P h R ∧
      signalJoint α γ d P h R ≤ 3*signalBaseline α R/(2*P)) (y : ℝ) :
    0 < signalJitter α γ d P B c y := by
  obtain ⟨a,A,ha,_hA,hbnd⟩ := signalJitter_quadratic_tails hα hB hc P hbound
  exact lt_of_lt_of_le (by positivity : 0 < a/(1+y^2)) (hbnd y).1

lemma fourierInv_finsetSum {ι : Type*} (S : Finset ι) {f : ι → ℝ → ℂ}
    (hf : ∀ i ∈ S, Integrable (f i)) (v : ℝ) :
    𝓕⁻ (fun y => ∑ i ∈ S, f i y) v = ∑ i ∈ S, 𝓕⁻ (f i) v := by
  simp only [Real.fourierInv_eq_fourier_neg,Real.fourier_eq,Finset.smul_sum]
  exact integral_finsetSum S (fun i hi => (Real.fourierIntegral_convergent_iff (-v)).2 (hf i hi))

lemma signalJitter_fourierInv {α B c : ℝ} (hα : 0 < α) (hB : 0 < B) (hc : 0 < c)
    (γ : ℝ) {d : ℝ → ℂ} (hd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) d)
    (hcomp : HasCompactSupport d) (P : ℕ) [NeZero P] (v : ℝ) :
    𝓕⁻ (fun y => (signalJitter α γ d P B c y : ℂ)) v =
      ∑ h : ZMod P, Complex.exp ((2*Real.pi*(v*h.val/(c*P)) : ℝ)*Complex.I)*
        𝓕⁻ (fun y => (signalJoint α γ d P h y : ℂ)) (v/(c*B)) := by
  classical
  have he : (fun y => (signalJitter α γ d P B c y : ℂ)) = fun y =>
      ∑ h : ZMod P, (affineDensity (signalJoint α γ d P h) (c*B) (-B*h.val/P) y : ℂ) := by
    funext y
    rw [signalJitter_affine]
    push_cast
    rfl
  rw [he]
  erw [fourierInv_finsetSum _ (fun h _ =>
    (integrable_affineDensity (signalJoint_integrable hα γ hd hcomp P h)
      (mul_pos hc hB).ne' _).ofReal)]
  apply Finset.sum_congr rfl
  intro h _
  erw [fourierInv_affineDensity (mul_pos hc hB)]
  congr 3
  field_simp [hB.ne',hc.ne',show (P : ℝ) ≠ 0 from Nat.cast_ne_zero.mpr (NeZero.ne P)]

lemma signal_character (P : ℕ) [NeZero P] (n : ℤ) (h : ZMod P) :
    ZMod.stdAddChar ((n : ZMod P)*h) =
      Complex.exp ((2*Real.pi*((n:ℝ)*h.val/P) : ℝ)*Complex.I) := by
  have he := ZMod.stdAddChar_coe (N := P) (n*(h.val:ℤ))
  simp only [Int.cast_mul,Int.cast_natCast,ZMod.natCast_zmod_val] at he
  rw [he]
  push_cast
  congr 1
  ring

lemma signalJitter_integer_moments {α B c : ℝ} (hα : 0 < α) (hB : 0 < B) (hc : 0 < c)
    (γ : ℝ) {d : ℝ → ℂ} (hd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) d)
    (hcomp : HasCompactSupport d) (P : ℕ) [NeZero P] (n : ℤ) :
    𝓕⁻ (fun y => (signalJitter α γ d P B c y : ℂ)) ((n:ℝ)*c) =
      ∑ h : ZMod P, (𝓕⁻ (fun y => (signalJoint α γ d P h y : ℂ))) ((n:ℝ)/B)*
        ZMod.stdAddChar ((n : ZMod P)*h) := by
  rw [signalJitter_fourierInv hα hB hc γ hd hcomp]
  have he : (n:ℝ)*c/(c*B) = (n:ℝ)/B := by field_simp
  rw [he]
  apply Finset.sum_congr rfl
  intro h _
  rw [signal_character,mul_comm]
  congr 3
  field_simp

lemma signalJitter_sieved_moments {α B c b D : ℝ}
    (hα : 0 < α) (hαb : α < b) (hB : 0 < B) (hc : 0 < c) (hb : 0 < b)
    {L : ℕ} (hL : D/b < L) (γ : ℝ) {d : ℝ → ℂ}
    (hd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) d) (hcomp : HasCompactSupport d)
    (hr : ∀ v, d (-v) = starRingEnd ℂ (d v))
    (hs : Function.support d ⊆ Icc (-D) D) (m : ℤ) (hm : b ≤ |(m:ℝ)/B|)
    (ℓ : ℕ) (hℓ : 1 ≤ ℓ) :
    𝓕⁻ (fun y => (signalJitter α γ d (signalPrimeProduct L) B c y : ℂ))
      ((ℓ:ℝ)*(m:ℝ)*c) =
      if ℓ = 1 ∧ IsUnit (m : ZMod (signalPrimeProduct L)) then (γ : ℂ)*d ((m:ℝ)/B) else 0 := by
  have he := signalJitter_integer_moments hα hB hc γ hd hcomp (signalPrimeProduct L)
    ((ℓ:ℤ)*m)
  push_cast at he
  rw [he]
  have hh := signalJoint_sieved_moments hα hαb hb hm hL hd hcomp hr hs γ
    (m : ZMod (signalPrimeProduct L)) ℓ hℓ
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  congr 2
  ring_nf

end ThreeTorus

noncomputable section
open MeasureTheory Set Filter Asymptotics
open scoped Topology FourierTransform
namespace ThreeTorus

lemma integral_scaledDensity {q : ℝ → ℝ} {s : ℝ} (hs : s ≠ 0) :
    (∫ y, scaledDensity q s y) = ∫ y, q y := by
  simp only [scaledDensity,div_eq_mul_inv]
  rw [integral_const_mul,Measure.integral_comp_mul_right]
  simp only [inv_inv,smul_eq_mul]
  field_simp

lemma fourierInv_scaledDensity {q : ℝ → ℝ} {s : ℝ} (hs : s ≠ 0) (v : ℝ) :
    𝓕⁻ (fun y => (scaledDensity q s y : ℂ)) v =
      𝓕⁻ (fun y => (q y : ℂ)) (v*s) := by
  simp only [Real.fourierInv_eq_fourier_neg,Real.fourier_real_eq_integral_exp_smul,
    smul_eq_mul]
  let f : ℝ → ℂ := fun x => Complex.exp (((-2*Real.pi*x*(-(v*s))) : ℝ)*Complex.I)*(q x : ℂ)
  have he : ∀ y : ℝ,
      Complex.exp (((-2*Real.pi*y*(-v)) : ℝ)*Complex.I)*(scaledDensity q s y : ℂ) =
        ((|s| : ℝ) : ℂ)⁻¹*f (s⁻¹*y) := by
    intro y
    have harg : -2*Real.pi*(s⁻¹*y)*(-(v*s)) = -2*Real.pi*y*(-v) := by
      field_simp [hs]
    dsimp only [f,scaledDensity]
    rw [harg]
    simp only [div_eq_mul_inv,Complex.ofReal_mul,Complex.ofReal_inv]
    rw [mul_comm s⁻¹ y]
    ring
  simp_rw [he]
  rw [integral_const_mul,Measure.integral_comp_mul_left]
  simp only [inv_inv,Complex.real_smul]
  have hsC : ((|s| : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (abs_ne_zero.mpr hs)
  field_simp
  apply integral_congr_ae
  filter_upwards [] with x
  dsimp only [f]
  congr 3
  ring_nf

lemma fourier_scaledDensity {q : ℝ → ℝ} {s : ℝ} (hs : s ≠ 0) (v : ℝ) :
    𝓕 (fun y => (scaledDensity q s y : ℂ)) v = 𝓕 (fun y => (q y : ℂ)) (v*s) := by
  have hh := fourierInv_scaledDensity (q := q) hs (-v)
  simpa only [Real.fourierInv_eq_fourier_neg,neg_neg,neg_mul,neg_neg] using hh

lemma scaledDensity_quadratic_bound {q : ℝ → ℝ} {C s : ℝ} (hC : 0 ≤ C) (hs : s ≠ 0)
    (hq : ∀ y, |q y| ≤ C/(1+y^2)) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ y, |scaledDensity q s y| ≤ D/(1+y^2) := by
  let K := 1+2*s^2
  have hK : 0 < K := by dsimp [K]; positivity
  refine ⟨|s|⁻¹*C*K,by positivity,fun y => ?_⟩
  have hsq : y^2 = s^2*(y/s)^2 := by field_simp
  have hbnd : 1+y^2 ≤ K*(1+(y/s)^2) := by
    dsimp [K]
    nlinarith [sq_nonneg s,sq_nonneg (y/s)]
  calc
    |scaledDensity q s y| = |s|⁻¹*|q (y/s)| := by
      simp only [scaledDensity,abs_mul,abs_inv,abs_abs]
    _ ≤ |s|⁻¹*(C/(1+(y/s)^2)) := mul_le_mul_of_nonneg_left (hq _) (by positivity)
    _ ≤ (|s|⁻¹*C*K)/(1+y^2) := by
      rw [← mul_div_assoc,div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [mul_le_mul_of_nonneg_left hbnd (show 0 ≤ |s|⁻¹*C by positivity)]

lemma quadratic_norm_isBigO {f : ℝ → ℂ} {C : ℝ} (hC : 0 ≤ C)
    (hf : ∀ y, ‖f y‖ ≤ C/(1+y^2)) :
    f =O[cocompact ℝ] (fun y : ℝ => |y| ^ (-(2:ℝ))) := by
  apply IsBigO.of_bound C
  filter_upwards [(isCompact_Icc (a := (-1:ℝ)) (b := 1)).compl_mem_cocompact] with y hy
  have h0 : y ≠ 0 := by intro h; subst y; simp at hy
  have hsq : 0 < y^2 := sq_pos_of_ne_zero h0
  have hr : |y| ^ (-(2:ℝ)) = (y^2)⁻¹ := by
    rw [Real.rpow_neg (abs_nonneg y),Real.rpow_two,sq_abs]
  rw [hr,Real.norm_eq_abs,abs_of_nonneg (by positivity),← div_eq_mul_inv]
  exact (hf y).trans (div_le_div_of_nonneg_left hC hsq (by nlinarith))

lemma fourierInv_real_neg (q : ℝ → ℝ) (v : ℝ) :
    𝓕⁻ (fun y => (q y : ℂ)) (-v) = starRingEnd ℂ (𝓕⁻ (fun y => (q y : ℂ)) v) := by
  simp only [Real.fourierInv_eq_fourier_neg,Real.fourier_real_eq_integral_exp_smul,
    smul_eq_mul,← integral_conj]
  apply integral_congr_ae
  filter_upwards [] with y
  simp only [map_mul,Complex.conj_ofReal,← Complex.exp_conj,Complex.conj_I]
  congr 2
  push_cast
  ring

lemma periodization_three_modes {q : ℝ → ℝ} (hq : Continuous q) {C : ℝ} (hC : 0 ≤ C)
    (hbnd : ∀ y, |q y| ≤ C/(1+y^2)) (a : ℂ)
    (hmom : ∀ n : ℤ, 𝓕⁻ (fun y => (q y : ℂ)) (n:ℝ) =
      if n = 0 then 1 else if n = 1 then a else if n = -1 then starRingEnd ℂ a else 0)
    (x : ℝ) :
    ∑' n : ℤ, (q (x+n) : ℂ) = 1 + 2*((a * fourier (-1) (x : UnitAddCircle)).re : ℂ) := by
  have hF (n : ℤ) : 𝓕 (fun y => (q y : ℂ)) (n:ℝ) =
      if n = 0 then 1 else if n = 1 then starRingEnd ℂ a else if n = -1 then a else 0 := by
    have hh := hmom (-n)
    simp only [Int.cast_neg,Real.fourierInv_eq_fourier_neg,neg_neg] at hh
    rw [hh]
    by_cases h0 : n = 0
    · simp [h0]
    by_cases h1 : n = 1
    · simp [h1]
    by_cases hn1 : n = -1
    · simp [hn1]
    have hh1 : -n ≠ 1 := by omega
    have hh2 : -n ≠ -1 := by omega
    simp [h0,h1,hn1,hh1,hh2]
  have hs : Summable (fun n : ℤ => 𝓕 (fun y => (q y : ℂ)) (n:ℝ)) := by
    apply summable_of_ne_finset_zero (s := {-1,0,1})
    intro n hn
    simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at hn
    simp [hF,hn.1,hn.2.1,hn.2.2]
  have hh := Real.tsum_eq_tsum_fourier_of_rpow_decay_of_summable
    (Complex.continuous_ofReal.comp hq) (b := 2) (by norm_num)
    (quadratic_norm_isBigO hC (fun y => by
      simpa only [Function.comp_apply,Complex.norm_real,Real.norm_eq_abs] using hbnd y)) hs x
  simp only [Function.comp_def] at hh
  erw [hh]
  rw [tsum_eq_sum (s := {-1,0,1}) (fun n hn => by
    simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at hn
    simp [hF,hn.1,hn.2.1,hn.2.2])]
  simp only [Finset.sum_insert,Finset.sum_singleton,show (-1 : ℤ) ∉ ({0,1} : Finset ℤ) by decide,
    show (0 : ℤ) ∉ ({1} : Finset ℤ) by decide,not_false_eq_true,hF]
  norm_num only [fourier_zero,Int.reduceNeg,Int.reduceEq,ite_true,ite_false,one_mul,mul_one]
  rw [fourier_neg]
  have he : a * starRingEnd ℂ (fourier 1 (x : UnitAddCircle)) +
      starRingEnd ℂ a * fourier 1 (x : UnitAddCircle) =
      2*((a * starRingEnd ℂ (fourier 1 (x : UnitAddCircle))).re : ℂ) := by
    simpa only [map_mul,starRingEnd_self_apply,Complex.ofReal_mul,Complex.ofReal_ofNat] using
      Complex.add_conj (a * starRingEnd ℂ (fourier 1 (x : UnitAddCircle)))
  linear_combination he

/-- A compact Fourier bandwidth supplies a shared finite series near any nonzero scale. -/
lemma periodization_scaled_finite {q : ℝ → ℝ} (hq : Continuous q)
    {C : ℝ} (hC : 0 ≤ C) (hbnd : ∀ y, |q y| ≤ C/(1+y^2))
    {D ε : ℝ} (hε : 0 < ε) (hF : ∀ v, D < |v| → 𝓕 (fun y => (q y : ℂ)) v = 0)
    {N : ℕ} (hN : D < N*ε) {s : ℝ} (hs : ε ≤ |s|) (x : ℝ) :
    ∑' n : ℤ, (scaledDensity q s (x+n) : ℂ) =
      ∑ n ∈ Finset.Icc (-(N:ℤ)) N,
        𝓕 (fun y => (q y : ℂ)) ((n:ℝ)*s)*fourier n (x : UnitAddCircle) := by
  have hs0 : s ≠ 0 := by intro hh; simp [hh] at hs; linarith
  obtain ⟨C',hC',hbound⟩ := scaledDensity_quadratic_bound hC hs0 hbnd
  have hcont : Continuous (scaledDensity q s) :=
    continuous_const.mul (hq.comp (continuous_id.div_const _))
  have hband (n : ℤ) (hn : n ∉ Finset.Icc (-(N:ℤ)) N) :
      𝓕 (fun y => (q y : ℂ)) ((n:ℝ)*s) = 0 := by
    apply hF
    have hn' : (N : ℝ) < |(n:ℝ)| := by
      by_contra! hab
      have hle := abs_le.mp hab
      apply hn
      exact Finset.mem_Icc.mpr ⟨by exact_mod_cast hle.1,by exact_mod_cast hle.2⟩
    rw [abs_mul]
    exact hN.trans_le (mul_le_mul (le_of_lt hn') hs hε.le (abs_nonneg _))
  have hsumm : Summable (fun n : ℤ => 𝓕 (fun y => (scaledDensity q s y : ℂ)) (n:ℝ)) := by
    apply summable_of_ne_finset_zero (s := Finset.Icc (-(N:ℤ)) N)
    intro n hn
    rw [fourier_scaledDensity hs0]
    exact hband n hn
  have he := Real.tsum_eq_tsum_fourier_of_rpow_decay_of_summable
    (Complex.continuous_ofReal.comp hcont) (b := 2) (by norm_num)
    (quadratic_norm_isBigO hC' (fun y => by
      simpa only [Function.comp_apply,Complex.norm_real,Real.norm_eq_abs] using hbound y)) hsumm x
  simp only [Function.comp_def] at he
  erw [he]
  simp_rw [fourier_scaledDensity hs0]
  exact tsum_eq_sum (fun n hn => by rw [hband n hn,zero_mul])

lemma periodization_scaled_tendstoUniformly {q : ℝ → ℝ} (hq : Continuous q)
    (hqi : Integrable q) {C : ℝ} (hC : 0 ≤ C) (hbnd : ∀ y, |q y| ≤ C/(1+y^2))
    {D : ℝ} (hF : ∀ v, D < |v| → 𝓕 (fun y => (q y : ℂ)) v = 0)
    {s₀ : ℝ} (hs₀ : s₀ ≠ 0) :
    TendstoUniformly (fun s x => ∑' n : ℤ, (scaledDensity q s (x+n) : ℂ))
      (fun x => ∑' n : ℤ, (scaledDensity q s₀ (x+n) : ℂ)) (𝓝 s₀) := by
  let ε := |s₀|/2
  have hε : 0 < ε := by dsimp [ε]; positivity
  obtain ⟨N,hN⟩ := exists_nat_gt (D/ε)
  have hN' : D < (N:ℝ)*ε := (div_lt_iff₀ hε).mp hN
  let S := Finset.Icc (-(N:ℤ)) N
  let F : ℝ → ℂ := 𝓕 (fun y => (q y : ℂ))
  have hFc : Continuous F := VectorFourier.fourierIntegral_continuous
    Real.continuous_fourierChar continuous_inner hqi.ofReal
  let G : ℝ → UnitAddCircle → ℂ := fun s x => ∑ n ∈ S, F ((n:ℝ)*s)*fourier n x
  have hGc : Continuous ↿G := by
    change Continuous (fun p : ℝ × UnitAddCircle => ∑ n ∈ S, F ((n:ℝ)*p.1)*fourier n p.2)
    apply continuous_finsetSum _
    intro n _
    exact (hFc.comp (continuous_const.mul continuous_fst)).mul
      ((fourier n).continuous.comp continuous_snd)
  have hu := Continuous.tendstoUniformly G hGc s₀
  have hnear : ∀ᶠ s : ℝ in 𝓝 s₀, ε ≤ |s| := by
    have hh : ε < |s₀| := by dsimp [ε]; linarith [abs_pos.mpr hs₀]
    exact ((continuous_abs.tendsto s₀).eventually (eventually_gt_nhds hh)).mono
      (fun _ h => h.le)
  have hs₀' : ε ≤ |s₀| := by dsimp [ε]; linarith [abs_nonneg s₀]
  apply Metric.tendstoUniformly_iff.mpr
  intro δ hδ
  filter_upwards [Metric.tendstoUniformly_iff.mp hu δ hδ,hnear] with s hs hs'
  intro x
  rw [periodization_scaled_finite hq hC hbnd hε hF hN' hs' x,
    periodization_scaled_finite hq hC hbnd hε hF hN' hs₀' x]
  exact hs (x : UnitAddCircle)

lemma fourierInv_real_zero (q : ℝ → ℝ) :
    𝓕⁻ (fun y => (q y : ℂ)) 0 = ((∫ y, q y : ℝ) : ℂ) := by
  simp only [Real.fourierInv_eq_fourier_neg,Real.fourier_real_eq_integral_exp_smul,
    neg_zero,mul_zero,Complex.ofReal_zero,zero_mul,Complex.exp_zero,one_smul]
  exact integral_ofReal

lemma fourierInv_real_int_moments {q : ℝ → ℝ} (hmass : (∫ y, q y) = 1) (a : ℂ)
    (hpos : ∀ ℓ : ℕ, 1 ≤ ℓ → 𝓕⁻ (fun y => (q y : ℂ)) (ℓ:ℝ) = if ℓ = 1 then a else 0)
    (n : ℤ) :
    𝓕⁻ (fun y => (q y : ℂ)) (n:ℝ) =
      if n = 0 then 1 else if n = 1 then a else if n = -1 then starRingEnd ℂ a else 0 := by
  by_cases h0 : n = 0
  · rw [h0,Int.cast_zero,ite_eq_left rfl,fourierInv_real_zero,hmass,Complex.ofReal_one]
  rcases lt_or_gt_of_ne h0 with hn | hn
  · have hneg : 0 ≤ -n := by omega
    let k := (-n).toNat
    have hk : (k : ℤ) = -n := Int.toNat_of_nonneg hneg
    have hkpos : 1 ≤ k := by omega
    have hnk : n = -(k : ℤ) := by omega
    rw [hnk,Int.cast_neg,Int.cast_natCast,fourierInv_real_neg,hpos k hkpos]
    by_cases hk1 : k = 1
    · simp [hk1]
    · have hk0 : k ≠ 0 := by omega
      have hn1 : -(k:ℤ) ≠ 1 := by omega
      have hnm1 : -(k:ℤ) ≠ -1 := by omega
      simp [hk1,hk0,hn1,hnm1]
  · lift n to ℕ using hn.le with k hk
    have hkpos : 1 ≤ k := by omega
    rw [Int.cast_natCast,hpos k hkpos]
    by_cases hk1 : k = 1
    · simp [hk1]
    · have hk0 : k ≠ 0 := by omega
      have hkn1 : (k:ℤ) ≠ -1 := by omega
      simp [hk1,hk0,hkn1]

end ThreeTorus

namespace ThreeTorus

lemma signalJitter_fourierInv_support {α B c D : ℝ} (hα : 0 < α) (hB : 0 < B)
    (hc : 0 < c) (hαD : α ≤ D) (γ : ℝ) {d : ℝ → ℂ}
    (hd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) d) (hcomp : HasCompactSupport d)
    (hr : ∀ v, d (-v) = starRingEnd ℂ (d v))
    (hs : Function.support d ⊆ Icc (-D) D) (P : ℕ) [NeZero P] {v : ℝ}
    (hv : c*B*D < |v|) :
    𝓕⁻ (fun y => (signalJitter α γ d P B c y : ℂ)) v = 0 := by
  rw [signalJitter_fourierInv hα hB hc γ hd hcomp]
  have hdiv : D < |v/(c*B)| := by
    rw [abs_div,abs_of_pos (mul_pos hc hB),lt_div_iff₀ (mul_pos hc hB)]
    nlinarith
  apply Finset.sum_eq_zero
  intro h _
  rw [fourierInv_signalJoint hα γ hd hcomp hr]
  have hbase : 𝓕⁻ (fun y => (signalBaseline α y : ℂ)) (v/(c*B)) = 0 := by
    rw [Real.fourierInv_eq_fourier_neg]
    exact signalBaseline_fourier_support hα (by simpa only [abs_neg] using hαD.trans hdiv.le)
  have hd0 : d (v/(c*B)) = 0 := by
    apply Function.notMem_support.mp
    intro hn
    have hh := hs hn
    exact (not_le_of_gt hdiv) (abs_le.mpr ⟨hh.1,hh.2⟩)
  rw [hbase,hd0,mul_zero,add_zero,mul_zero,mul_zero]

lemma signalJitter_scale_cancel {α γ : ℝ} (d : ℝ → ℂ) (P : ℕ) [NeZero P]
    (B : ℝ) {c : ℝ} (hc : 0 < c) (m y : ℝ) :
    scaledDensity (signalJitter α γ d P B c) (m*c) y =
      scaledDensity (signalJitter α γ d P B 1) m y := by
  simp only [scaledDensity,signalJitter,abs_mul,abs_of_pos hc,mul_inv_rev,one_mul]
  by_cases hm : m = 0
  · simp [hm]
  have he : c*(y/(m*c)) = y/m := by field_simp
  rw [he]
  field_simp

lemma signalJitter_periodic_ideal {α B c b D : ℝ}
    (hα : 0 < α) (hαb : α < b) (hB : 0 < B) (hc : 0 < c) (hb : 0 < b)
    {L : ℕ} (hL : D/b < L) (γ : ℝ) {d : ℝ → ℂ}
    (hd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) d) (hcomp : HasCompactSupport d)
    (hr : ∀ v, d (-v) = starRingEnd ℂ (d v)) (h0 : d 0 = 0)
    (hs : Function.support d ⊆ Icc (-D) D) (m : ℤ) (hm : b ≤ |(m:ℝ)/B|)
    (hbound : ∀ h R, signalBaseline α R/(2*signalPrimeProduct L) ≤
        signalJoint α γ d (signalPrimeProduct L) h R ∧
      signalJoint α γ d (signalPrimeProduct L) h R ≤
        3*signalBaseline α R/(2*signalPrimeProduct L)) (y : ℝ) :
    ∑' k : ℤ, (scaledDensity (signalJitter α γ d (signalPrimeProduct L) B c)
      ((m:ℝ)*c) (y+k) : ℂ) =
      1 + 2*((((if IsUnit (m : ZMod (signalPrimeProduct L)) then (γ:ℂ)*d ((m:ℝ)/B) else 0) *
        fourier (-1) (y : UnitAddCircle)).re) : ℂ) := by
  have hm0 : (m:ℝ) ≠ 0 := by intro hh; rw [hh,zero_div,abs_zero] at hm; linarith
  have hmc : (m:ℝ)*c ≠ 0 := mul_ne_zero hm0 hc.ne'
  obtain ⟨a,A,_ha,hA,hbnd⟩ := signalJitter_quadratic_tails hα hB hc
    (signalPrimeProduct L) hbound
  have hqb : ∀ y, |signalJitter α γ d (signalPrimeProduct L) B c y| ≤ A/(1+y^2) := by
    intro y
    rw [abs_of_pos (signalJitter_pos hα hB hc _ hbound y)]
    exact (hbnd y).2
  obtain ⟨C,hC,hCb⟩ := scaledDensity_quadratic_bound hA.le hmc hqb
  have hcq : Continuous (scaledDensity (signalJitter α γ d (signalPrimeProduct L) B c)
      ((m:ℝ)*c)) := continuous_const.mul
    ((signalJitter_smooth hα γ hd hcomp _ B c).continuous.comp (continuous_id.div_const _))
  apply periodization_three_modes hcq hC hCb
  apply fourierInv_real_int_moments
  · rw [integral_scaledDensity hmc,integral_signalJitter hα hB hc γ hd hcomp hr h0]
  · intro ℓ hℓ
    erw [fourierInv_scaledDensity hmc]
    have he : (ℓ:ℝ)*((m:ℝ)*c) = (ℓ:ℝ)*(m:ℝ)*c := by ring
    rw [he,signalJitter_sieved_moments hα hαb hB hc hb hL γ hd hcomp hr hs m hm ℓ hℓ]
    split_ifs <;> simp_all

end ThreeTorus

namespace ThreeTorus

/-- The finite-c approximation is uniform on every fixed old speed range.
The exact ideal law is independent of c after scaling, as required in section 3. -/
lemma periodization_scaled_uniform_perturbation {q : ℝ → ℝ} (hq : Continuous q)
    (hqi : Integrable q) {C : ℝ} (hC : 0 ≤ C) (hbnd : ∀ y, |q y| ≤ C/(1+y^2))
    {D : ℝ} (hF : ∀ v, D < |v| → 𝓕 (fun y => (q y : ℂ)) v = 0)
    {s₀ : ℝ} (hs₀ : s₀ ≠ 0) (V : ℝ) :
    ∀ ε > 0, ∀ᶠ c : ℝ in atTop, ∀ v : ℝ, |v| ≤ V → ∀ y : ℝ,
      dist (∑' n : ℤ, (scaledDensity q (s₀*(1+v/c)) (y+n) : ℂ))
        (∑' n : ℤ, (scaledDensity q s₀ (y+n) : ℂ)) < ε := by
  intro ε hε
  obtain ⟨δ,hδ,hd⟩ := Metric.eventually_nhds_iff.mp
    (Metric.tendstoUniformly_iff.mp
      (periodization_scaled_tendstoUniformly hq hqi hC hbnd hF hs₀) ε hε)
  filter_upwards [eventually_gt_atTop (|s₀| * |V|/δ+1)] with c hc
  intro v hv y
  have hc0 : 0 < c := lt_trans (by positivity) hc
  have hv' : |v| ≤ |V| := hv.trans (le_abs_self V)
  have hnear : dist (s₀*(1+v/c)) s₀ < δ := by
    rw [Real.dist_eq,show s₀*(1+v/c)-s₀ = s₀*v/c by ring,
      abs_div,abs_mul,abs_of_pos hc0]
    apply (div_lt_iff₀ hc0).mpr
    have hh : |s₀| * |V| < δ*c := by
      have h := (div_lt_iff₀ hδ).mp (lt_trans (lt_add_one _) hc)
      nlinarith
    exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left hv' (abs_nonneg _)) hh
  simpa only [dist_comm] using hd hnear y

end ThreeTorus

namespace ThreeTorus

/-- The actual finite-c signal law, uniform in the bounded old speed and in
all phases. The modulus and strength are the exact fixed ones of the manuscript. -/
lemma signalJitter_periodic_approximation {α B b D : ℝ}
    (hα : 0 < α) (hαb : α < b) (hαD : α ≤ D) (hB : 0 < B) (hb : 0 < b)
    {L : ℕ} (hL : D/b < L) (γ : ℝ) {d : ℝ → ℂ}
    (hd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) d) (hcomp : HasCompactSupport d)
    (hr : ∀ v, d (-v) = starRingEnd ℂ (d v)) (h0 : d 0 = 0)
    (hs : Function.support d ⊆ Icc (-D) D) (m : ℤ) (hm : b ≤ |(m:ℝ)/B|)
    (hbound : ∀ h R, signalBaseline α R/(2*signalPrimeProduct L) ≤
        signalJoint α γ d (signalPrimeProduct L) h R ∧
      signalJoint α γ d (signalPrimeProduct L) h R ≤
        3*signalBaseline α R/(2*signalPrimeProduct L)) (V : ℝ) :
    ∀ ε > 0, ∀ᶠ c : ℝ in atTop, ∀ v : ℝ, |v| ≤ V → ∀ y : ℝ,
      dist (∑' k : ℤ, (scaledDensity (signalJitter α γ d (signalPrimeProduct L) B c)
        ((m:ℝ)*(c+v)) (y+k) : ℂ))
      (1 + 2*((((if IsUnit (m : ZMod (signalPrimeProduct L)) then (γ:ℂ)*d ((m:ℝ)/B) else 0) *
        fourier (-1) (y : UnitAddCircle)).re) : ℂ)) < ε := by
  have hm0 : (m:ℝ) ≠ 0 := by intro hh; rw [hh,zero_div,abs_zero] at hm; linarith
  obtain ⟨a,A,_ha,hA,hbnd⟩ := signalJitter_quadratic_tails hα hB zero_lt_one
    (signalPrimeProduct L) hbound
  have hqb : ∀ y, |signalJitter α γ d (signalPrimeProduct L) B 1 y| ≤ A/(1+y^2) := by
    intro y
    rw [abs_of_pos (signalJitter_pos hα hB zero_lt_one _ hbound y)]
    exact (hbnd y).2
  have hF : ∀ v, B*D < |v| →
      𝓕 (fun y => (signalJitter α γ d (signalPrimeProduct L) B 1 y : ℂ)) v = 0 := by
    intro v hv
    have hh := signalJitter_fourierInv_support hα hB zero_lt_one hαD γ hd hcomp hr hs
      (signalPrimeProduct L) (v := -v) (by simpa only [one_mul,abs_neg] using hv)
    simpa only [Real.fourierInv_eq_fourier_neg,neg_neg] using hh
  intro ε hε
  have he := periodization_scaled_uniform_perturbation
    (signalJitter_smooth hα γ hd hcomp _ B 1).continuous
    (signalJitter_integrable hα hB zero_lt_one γ hd hcomp _)
    hA.le hqb hF hm0 V ε hε
  filter_upwards [he,eventually_gt_atTop (0:ℝ)] with c hc hc0
  intro v hv y
  have hscale : (m:ℝ)*(c+v) = ((m:ℝ)*(1+v/c))*c := by field_simp
  simp_rw [hscale,signalJitter_scale_cancel d (signalPrimeProduct L) B hc0]
  have hideal := signalJitter_periodic_ideal hα hαb hB zero_lt_one hb hL γ hd hcomp hr h0 hs
    m hm hbound y
  simp only [mul_one] at hideal
  rw [← hideal]
  exact hc v hv y

end ThreeTorus

end

end

end

end

end

end OAI
end

section
-- module Solutions.OAIQ13_TT.ThreeTorus_Twists
attribute [-instance] _root_.OAI.ThreeTorus.tripleVolume_regular
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Product torus, exact angular packets, all integer twist iterates, and measure-preserving passage charts. -/

noncomputable section
open MeasureTheory Filter Set Complex
open scoped Topology SchwartzMap FourierTransform Real
open scoped Topology

noncomputable section
open MeasureTheory Set
open scoped ENNReal Topology

namespace ThreeTorus

lemma passage_conjugacy (H σ : UnitAddCircle → UnitAddCircle) (x : TripleTorus) :
    passageChart H (passageMap H σ ((passageChart H).symm x)) = passageTwist σ x := by
  simp only [passageChart, passageMap, passageTwist, circleThetaShear, circleCycle,
    Equiv.trans_apply, Equiv.symm_trans_apply]
  ext <;> simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]

lemma measurePreserving_circleCycle :
    MeasurePreserving circleCycle tripleVolume tripleVolume := by
  exact (measurePreserving_prodAssoc AddCircle.haarAddCircle AddCircle.haarAddCircle
    AddCircle.haarAddCircle).comp Measure.measurePreserving_swap

lemma measurePreserving_fiberTranslate {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [SFinite μ] {g : Ω → UnitAddCircle} (hg : Measurable g) :
    MeasurePreserving (fun p : Ω × UnitAddCircle => (p.1,p.2+g p.1))
      (μ.prod AddCircle.haarAddCircle) (μ.prod AddCircle.haarAddCircle) := by
  exact (MeasurePreserving.id μ).skew_product (measurable_snd.add (hg.comp measurable_fst))
    (Filter.Eventually.of_forall (fun x => (measurePreserving_add_right AddCircle.haarAddCircle (g x)).map_eq))

lemma measurePreserving_circleThetaShear {H : UnitAddCircle → UnitAddCircle} (hH : Measurable H) :
    MeasurePreserving (circleThetaShear H) tripleVolume tripleVolume := by
  exact Measure.measurePreserving_swap.comp
    ((measurePreserving_fiberTranslate (AddCircle.haarAddCircle.prod AddCircle.haarAddCircle)
      (hH.comp measurable_fst)).comp Measure.measurePreserving_swap)

lemma measurePreserving_passageChart {H : UnitAddCircle → UnitAddCircle} (hH : Measurable H) :
    MeasurePreserving (passageChart H) tripleVolume tripleVolume :=
  measurePreserving_circleCycle.comp (measurePreserving_circleThetaShear hH.neg)

lemma passageChart_inverse_measurable {H : UnitAddCircle → UnitAddCircle} (hH : Measurable H) :
    Measurable (passageChart H).symm := by
  change Measurable (fun x : TripleTorus => (x.2.2-(-H x.1),x.1,x.2.1))
  exact (measurable_snd.snd.sub (hH.comp measurable_fst).neg).prodMk
    (measurable_fst.prodMk measurable_snd.fst)

lemma measurePreserving_passageChart_inverse {H : UnitAddCircle → UnitAddCircle} (hH : Measurable H) :
    MeasurePreserving (passageChart H).symm tripleVolume tripleVolume := by
  let e : TripleTorus ≃ᵐ TripleTorus :=
    { toEquiv := passageChart H
      measurable_toFun := (measurePreserving_passageChart hH).measurable
      measurable_invFun := passageChart_inverse_measurable hH }
  exact MeasurePreserving.symm e (measurePreserving_passageChart hH)

lemma passage_as_conjugate (H σ : UnitAddCircle → UnitAddCircle) :
    (passageMap H σ : TripleTorus → TripleTorus) =
      (passageChart H).symm ∘ passageTwist σ ∘ passageChart H := by
  funext x
  have hh := passage_conjugacy H σ (passageChart H x)
  simpa only [Equiv.symm_apply_apply, Function.comp_apply] using
    congrArg (passageChart H).symm hh

lemma measurePreserving_passageMap {H σ : UnitAddCircle → UnitAddCircle}
    (hH : Measurable H) (hσ : Measurable σ) :
    MeasurePreserving (passageMap H σ) tripleVolume tripleVolume := by
  rw [passage_as_conjugate]
  exact (measurePreserving_passageChart_inverse hH).comp
    ((measurePreserving_circleThetaShear hσ).comp (measurePreserving_passageChart hH))

end ThreeTorus

end

end

end OAI
end

section
-- module Solutions.OAIQ13_TT.ThreeTorus_Geometry
attribute [-instance] _root_.OAI.ThreeTorus.tripleVolume_regular
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Torus coordinate equivalence, smooth passage geometry, and all-jet passage convergence. -/

section

/-! Torus coordinate equivalence and retained passage geometry. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal Topology

noncomputable section
open MeasureTheory Set
open scoped Topology
namespace ThreeTorus

lemma torusTriple_apply (x : Torus) : torusTriple x = (x 0,x 1,x 2) := rfl

lemma torusTriple_symm_apply (x : TripleTorus) : torusTriple.symm x = ![x.1,x.2.1,x.2.2] := by
  ext i
  fin_cases i <;> rfl

lemma torusPassage_apply (h s : UnitAddCircle → UnitAddCircle) (x : Torus) :
    torusPassage h s x = ![x 0+h (x 1+s (x 2))-h (x 1),x 1+s (x 2),x 2] := by
  rw [torusPassage,Equiv.trans_apply,Equiv.trans_apply]
  rw [show torusTriple.toEquiv x = (x 0,x 1,x 2) from rfl]
  exact torusTriple_symm_apply _

lemma torusPassage_symm_apply (h s : UnitAddCircle → UnitAddCircle) (x : Torus) :
    (torusPassage h s).symm x = ![x 0-h (x 1)+h (x 1-s (x 2)),x 1-s (x 2),x 2] := by
  change torusTriple.symm ((passageMap h s).symm (torusTriple x)) = _
  rw [torusTriple_apply,torusTriple_symm_apply]
  rfl

lemma measurePreserving_torusPassage {h s : UnitAddCircle → UnitAddCircle}
    (hh : Measurable h) (hs : Measurable s) : MeasurePreserving (torusPassage h s) μ μ := by
  exact (MeasurePreserving.symm torusTriple measurePreserving_torusTriple).comp
    ((measurePreserving_passageMap hh hs).comp measurePreserving_torusTriple)

lemma contDiff_passageLift {h s : ℝ → ℝ}
    (hh : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) h)
    (hs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) s) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (passageLift h s) := by
  apply contDiff_pi.mpr
  intro i
  fin_cases i
  · exact ((contDiff_apply ℝ ℝ 0).add (hh.comp ((contDiff_apply ℝ ℝ 1).add (hs.comp (contDiff_apply ℝ ℝ 2))))).sub
      (hh.comp (contDiff_apply ℝ ℝ 1))
  · exact (contDiff_apply ℝ ℝ 1).add (hs.comp (contDiff_apply ℝ ℝ 2))
  · exact contDiff_apply ℝ ℝ 2

lemma contDiff_passageInverseLift {h s : ℝ → ℝ}
    (hh : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) h)
    (hs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) s) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (passageInverseLift h s) := by
  apply contDiff_pi.mpr
  intro i
  fin_cases i
  · exact ((contDiff_apply ℝ ℝ 0).sub (hh.comp (contDiff_apply ℝ ℝ 1))).add
      (hh.comp ((contDiff_apply ℝ ℝ 1).sub (hs.comp (contDiff_apply ℝ ℝ 2))))
  · exact (contDiff_apply ℝ ℝ 1).sub (hs.comp (contDiff_apply ℝ ℝ 2))
  · exact contDiff_apply ℝ ℝ 2

lemma smooth_torusPassage {h s : UnitAddCircle → UnitAddCircle} {H S : ℝ → ℝ}
    (hh : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) H)
    (hs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) S)
    (hH : ∀ x : ℝ, h (x : UnitAddCircle) = (H x : UnitAddCircle))
    (hS : ∀ x : ℝ, s (x : UnitAddCircle) = (S x : UnitAddCircle)) :
    Smooth (torusPassage h s) := by
  intro x
  refine ⟨Set.univ,isOpen_univ,Set.mem_univ x,passageLift H S,
    (contDiff_passageLift hh hs).contDiffOn,?_⟩
  intro y _
  rw [torusPassage_apply]
  ext i
  fin_cases i <;> simp only [project,passageLift,hS,← AddCircle.coe_add,hH,← AddCircle.coe_sub] <;> rfl

lemma smooth_torusPassage_symm {h s : UnitAddCircle → UnitAddCircle} {H S : ℝ → ℝ}
    (hh : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) H)
    (hs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) S)
    (hH : ∀ x : ℝ, h (x : UnitAddCircle) = (H x : UnitAddCircle))
    (hS : ∀ x : ℝ, s (x : UnitAddCircle) = (S x : UnitAddCircle)) :
    Smooth (torusPassage h s).symm := by
  intro x
  refine ⟨Set.univ,isOpen_univ,Set.mem_univ x,passageInverseLift H S,
    (contDiff_passageInverseLift hh hs).contDiffOn,?_⟩
  intro y _
  rw [torusPassage_symm_apply]
  ext i
  fin_cases i <;> simp only [project,passageInverseLift,hS,← AddCircle.coe_sub,hH,← AddCircle.coe_add] <;> rfl

end ThreeTorus

noncomputable section
open MeasureTheory Set Function
open scoped Topology
namespace ThreeTorus

lemma continuous_periodic_lift {X : Type*} [TopologicalSpace X] {f : ℝ → X}
    (hf : Function.Periodic f 1) (hc : Continuous f) : Continuous hf.lift := by
  exact hc.quotient_lift _

lemma circlePrimitive_coe {v : ℝ → ℝ} (hv : Function.Periodic v 1)
    (hc : Continuous v) {k : ℤ} (hk : (∫ t in 0..1, v t) = k) (x : ℝ) :
    circlePrimitive hv hc hk (x:UnitAddCircle) = (↑(∫ t in 0..x, v t):UnitAddCircle) := rfl

lemma continuous_circlePrimitive {v : ℝ → ℝ} (hv : Function.Periodic v 1)
    (hc : Continuous v) {k : ℤ} (hk : (∫ t in 0..1, v t) = k) :
    Continuous (circlePrimitive hv hc hk) := by
  exact continuous_periodic_lift _ ((AddCircle.continuous_mk' 1).comp
    (intervalIntegral.differentiable_integral_of_continuous hc).continuous)

lemma circleSpeed_coe {s : ℝ → ℝ} (hs : Function.Periodic s 1) (x : ℝ) :
    circleSpeed hs (x:UnitAddCircle) = (s x:UnitAddCircle) := rfl

lemma continuous_circleSpeed {s : ℝ → ℝ} (hs : Function.Periodic s 1) (hc : Continuous s) :
    Continuous (circleSpeed hs) := by
  exact (AddCircle.continuous_mk' 1).comp (continuous_periodic_lift hs hc)

/-- Global C-infinity, inverse C-infinity, and exact Haar preservation for the
manuscript passage, without assuming any geometric conclusion. -/
lemma primitive_passage_properties {v s : ℝ → ℝ}
    (hv : Function.Periodic v 1) (hs : Function.Periodic s 1)
    (hvc : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) v)
    (hsc : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) s)
    {k : ℤ} (hk : (∫ t in 0..1, v t) = k) :
    let T := torusPassage (circlePrimitive hv hvc.continuous hk) (circleSpeed hs)
    Smooth T ∧ Smooth T.symm ∧ MeasurePreserving T μ μ := by
  exact ⟨smooth_torusPassage (contDiff_real_primitive hvc) hsc
      (circlePrimitive_coe hv hvc.continuous hk) (circleSpeed_coe hs),
    smooth_torusPassage_symm (contDiff_real_primitive hvc) hsc
      (circlePrimitive_coe hv hvc.continuous hk) (circleSpeed_coe hs),
    measurePreserving_torusPassage (continuous_circlePrimitive hv hvc.continuous hk).measurable
      (continuous_circleSpeed hs hsc.continuous).measurable⟩

end ThreeTorus

noncomputable section
open MeasureTheory Set Function
open scoped Topology
namespace ThreeTorus

/-- The bounded winding correction; no subsequence of passage integers is needed. -/
lemma passage_rounding (A : ℝ) {N : ℕ} (hN : 0 < N) :
    ∃ d : ℝ, ∃ k : ℤ, |d| ≤ (N:ℝ)⁻¹ ∧ (N:ℝ)*(A+d) = k := by
  let k : ℤ := ⌊(N:ℝ)*A⌋
  let d : ℝ := ((k:ℝ)-(N:ℝ)*A)/(N:ℝ)
  have hn : (0:ℝ) < N := by exact_mod_cast hN
  refine ⟨d,k,?_,?_⟩
  · have hk1 : (k:ℝ) ≤ (N:ℝ)*A := Int.floor_le _
    have hk2 : (N:ℝ)*A-1 ≤ (k:ℝ) := (Int.sub_one_lt_floor _).le
    dsimp [d]
    rw [abs_div,abs_of_pos hn,abs_of_nonpos (sub_nonpos.mpr hk1),← one_div]
    exact div_le_div_of_nonneg_right (by linarith) hn.le
  · dsimp [d]
    field_simp
    ring

lemma passage_rounded_slope {v : ℝ → ℝ}
    (hv : Function.Periodic v 1) (hc : Continuous v) (N : ℕ) (d : ℝ) {k : ℤ}
    (hk : (N:ℝ)*((∫ t in 0..1, v t)+d) = k) :
    Function.Periodic (fun x => (N:ℝ)*(v x+d)) 1 ∧
    (∫ t in 0..1, (N:ℝ)*(v t+d)) = k := by
  constructor
  · intro x
    dsimp only
    rw [hv x]
  · rw [intervalIntegral.integral_const_mul,
      intervalIntegral.integral_add (hc.intervalIntegrable _ _) intervalIntegrable_const]
    simpa using hk

lemma passage_speed_smooth {J : ℝ → ℝ}
    (hJ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) J) (N : ℕ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x => (N:ℝ)⁻¹+(N:ℝ)⁻¹^2*J x) := by fun_prop

end ThreeTorus

noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace ThreeTorus

lemma iteratedFDeriv_slice
    {P E G : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    {F : P × E → G} {n : ℕ} (hF : ContDiff ℝ n F) (p : P) (x : E) :
    iteratedFDeriv ℝ n (fun y => F (p,y)) x =
      (iteratedFDeriv ℝ n F (p,x)).compContinuousLinearMap
        (fun _ => ContinuousLinearMap.inr ℝ P E) := by
  have hh : ContDiff ℝ n (fun q : P × E => F ((p,0)+q)) :=
    hF.comp (contDiff_const.add contDiff_id)
  have he := (ContinuousLinearMap.inr ℝ P E).iteratedFDeriv_comp_right hh x (le_refl (n:WithTop ℕ∞))
  simpa only [Function.comp_def,ContinuousLinearMap.inr_apply,
    Prod.mk_add_mk,add_zero,zero_add,iteratedFDeriv_comp_add_left] using he

lemma continuous_iteratedFDeriv_slice
    {P E G : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    {F : P × E → G} {n : ℕ} (hF : ContDiff ℝ n F) :
    Continuous (fun q : P × E => iteratedFDeriv ℝ n (fun y => F (q.1,y)) q.2) := by
  simp_rw [iteratedFDeriv_slice hF]
  exact (ContinuousMultilinearMap.compContinuousLinearMapL
    (fun _ : Fin n => ContinuousLinearMap.inr ℝ P E)).continuous.comp
      hF.continuous_iteratedFDeriv'

/-- Joint smoothness gives convergence in every C^k seminorm on compact sets. -/
lemma smooth_parameter_jets_tendsto
    {P E G : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [ProperSpace P]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    {F : P × E → G} (hF : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F)
    (p : P) {K : Set E} (hK : IsCompact K) (n : ℕ) :
    TendstoUniformlyOn (fun a x => iteratedFDeriv ℝ n (fun y => F (a,y)) x)
      (fun x => iteratedFDeriv ℝ n (fun y => F (p,y)) x) (𝓝 p) K := by
  have hc := continuous_iteratedFDeriv_slice (hF.of_le
    (by exact_mod_cast (le_top : (n:ℕ∞) ≤ ⊤)))
  have hu := ((isCompact_closedBall p 1).prod hK).uniformContinuousOn_of_continuous hc.continuousOn
  have ht := UniformContinuousOn.tendstoUniformlyOn
    (F := fun a x => iteratedFDeriv ℝ n (fun y => F (a,y)) x)
    hu (by simp : p ∈ Metric.closedBall p (1:ℝ))
  simpa only [nhdsWithin_eq_nhds.mpr (Metric.closedBall_mem_nhds p (by norm_num : (0:ℝ)<1))] using ht

end ThreeTorus

noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace ThreeTorus

lemma smooth_passageFamily {v J : ℝ → ℝ}
    (hv : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) v)
    (hJ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) J) (r : ℝ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : (ℝ × ℝ) × Cover => passageFamily v J r q.1 q.2) := by
  have hc : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : ((ℝ × ℝ) × Cover) × ℝ =>
        v (q.1.2 1+q.2*(r*q.1.1.1*(1+q.1.1.1*J (q.1.2 2))))+q.1.1.2) := by
    fun_prop
  have hi := smooth_compact_integral hc 0 1
  apply contDiff_pi.mpr
  intro i
  fin_cases i
  · change ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun q : (ℝ × ℝ) × Cover =>
      q.2 0+r*(1+q.1.1*J (q.2 2))*(∫ t in (0:ℝ)..1,
        v (q.2 1+t*(r*q.1.1*(1+q.1.1*J (q.2 2))))+q.1.2))
    exact (by fun_prop : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun q : (ℝ × ℝ) × Cover => q.2 0)).add
      ((by fun_prop : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun q : (ℝ × ℝ) × Cover => r*(1+q.1.1*J (q.2 2)))).mul hi)
  · change ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun q : (ℝ × ℝ) × Cover =>
      q.2 1+r*q.1.1*(1+q.1.1*J (q.2 2)))
    fun_prop
  · change ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun q : (ℝ × ℝ) × Cover => q.2 2)
    fun_prop

lemma passageFamily_zero (v J : ℝ → ℝ) (r : ℝ) :
    passageFamily v J r (0,0) = fun x : Cover => ![x 0+r*v (x 1),x 1,x 2] := by
  funext x
  simp [passageFamily]

lemma passageFamily_increment {v J : ℝ → ℝ} (hv : Continuous v)
    {N : ℕ} (hN : 0 < N) (d r u a : ℝ) :
    (∫ t in 0..u+r*((N:ℝ)⁻¹+(N:ℝ)⁻¹^2*J a), (N:ℝ)*(v t+d))
      -(∫ t in 0..u, (N:ℝ)*(v t+d)) =
    r*(1+(N:ℝ)⁻¹*J a)*(∫ t in (0:ℝ)..1,
      v (u+t*(r*(N:ℝ)⁻¹*(1+(N:ℝ)⁻¹*J a)))+d) := by
  have hn : (N:ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hi : ∀ a b : ℝ, IntervalIntegrable (fun t => (N:ℝ)*(v t+d)) volume a b :=
    fun a b => (continuous_const.mul (hv.add continuous_const)).intervalIntegrable a b
  rw [← intervalIntegral.integral_add_adjacent_intervals (hi 0 u) (hi u _), add_sub_cancel_left]
  rw [intervalIntegral.integral_const_mul]
  have hs : r*((N:ℝ)⁻¹+(N:ℝ)⁻¹^2*J a) = r*(N:ℝ)⁻¹*(1+(N:ℝ)⁻¹*J a) := by ring
  rw [hs]
  have he := intervalIntegral.smul_integral_comp_add_mul (fun t => v t+d)
    (a := (0:ℝ)) (b := 1) (r*(N:ℝ)⁻¹*(1+(N:ℝ)⁻¹*J a)) u
  simp only [smul_eq_mul,mul_zero,add_zero,mul_one] at he
  rw [← he]
  have hf : (fun t => v (u+t*(r*(N:ℝ)⁻¹*(1+(N:ℝ)⁻¹*J a)))+d) =
      (fun t => v (u+r*(N:ℝ)⁻¹*(1+(N:ℝ)⁻¹*J a)*t)+d) := by
    funext t
    rw [mul_comm t]
  rw [hf]
  field_simp

/-- The passage and inverse are specializations of the same smooth family. -/
lemma passageLift_eq_family {v J : ℝ → ℝ} (hv : Continuous v)
    {N : ℕ} (hN : 0 < N) (d : ℝ) :
    passageLift (fun u => ∫ t in 0..u, (N:ℝ)*(v t+d))
      (fun a => (N:ℝ)⁻¹+(N:ℝ)⁻¹^2*J a) = passageFamily v J 1 ((N:ℝ)⁻¹,d) ∧
    passageInverseLift (fun u => ∫ t in 0..u, (N:ℝ)*(v t+d))
      (fun a => (N:ℝ)⁻¹+(N:ℝ)⁻¹^2*J a) = passageFamily v J (-1) ((N:ℝ)⁻¹,d) := by
  have h1 (u a : ℝ) := passageFamily_increment (J := J) hv hN d 1 u a
  have h2 (u a : ℝ) := passageFamily_increment (J := J) hv hN d (-1) u a
  constructor
  · funext x i
    fin_cases i
    · dsimp [passageLift,passageFamily]
      simp only [one_mul] at h1 ⊢
      linarith [h1 (x 1) (x 2)]
    · dsimp [passageLift,passageFamily]
      ring
    · rfl
  · funext x i
    fin_cases i
    · dsimp [passageInverseLift,passageFamily]
      simp only [neg_one_mul,← sub_eq_add_neg] at h2 ⊢
      linarith [h2 (x 1) (x 2)]
    · dsimp [passageInverseLift,passageFamily]
      ring
    · rfl

lemma passage_parameters_tendsto {d : ℕ → ℝ}
    (hd : ∀ N : ℕ, 0 < N → |d N| ≤ (N:ℝ)⁻¹) :
    Tendsto (fun N : ℕ => ((N:ℝ)⁻¹,d N)) atTop (𝓝 (0,0)) := by
  have hn : Tendsto (fun N : ℕ => (N:ℝ)⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hnd : Tendsto d atTop (𝓝 0) := by
    apply squeeze_zero_norm' ?_ hn
    filter_upwards [eventually_gt_atTop (0:ℕ)] with N hN
    exact hd N hN
  exact hn.prodMk_nhds hnd

/-- All spatial derivatives of each sign of the passage converge uniformly on
any fixed compact set. This is genuine C-infinity convergence, not C-zero. -/
lemma passage_Cinfty_limit {v J : ℝ → ℝ}
    (hv : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) v)
    (hJ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) J)
    {d : ℕ → ℝ} (hd : ∀ N : ℕ, 0 < N → |d N| ≤ (N:ℝ)⁻¹)
    (r : ℝ) {K : Set Cover} (hK : IsCompact K) (n : ℕ) :
    TendstoUniformlyOn
      (fun (N : ℕ) x => iteratedFDeriv ℝ n (passageFamily v J r ((N:ℝ)⁻¹,d N)) x)
      (fun x => iteratedFDeriv ℝ n (fun y : Cover => ![y 0+r*v (y 1),y 1,y 2]) x)
      atTop K := by
  have ht := smooth_parameter_jets_tendsto (smooth_passageFamily hv hJ r) (0,0) hK n
  simp only [passageFamily_zero] at ht
  intro U hU
  exact (passage_parameters_tendsto hd).eventually (ht U hU)

end ThreeTorus
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
-- module Solutions.OAIQ13_TT.ThreeTorus_Jitter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Cumulative distribution, smooth quantile inverse, and positive smooth neutral jitter laws. -/

noncomputable section
open MeasureTheory Filter Set Complex
open scoped Topology SchwartzMap FourierTransform Real
open scoped Topology
open MeasureTheory Set
open scoped ENNReal Topology
open Set Function Filter
open scoped Topology NNReal
open MeasureTheory Filter Set
open MeasureTheory Set Function
open scoped Topology ENNReal
open scoped Topology BigOperators
open MeasureTheory Set Filter
open scoped Topology FourierTransform
open MeasureTheory Set Filter Asymptotics

/-! Approximation of a positive smooth law.
The cumulative distribution and its local smooth inverse are constructed from
the positive smooth density, not assumed as an additional hypothesis. -/
noncomputable section
open MeasureTheory Set Filter Function
open scoped Topology
namespace ThreeTorus

lemma cumulative_sub (ρ : ℝ → ℝ) (hi : Integrable ρ) (x y : ℝ) :
    cumulative ρ y - cumulative ρ x = ∫ t in x..y, ρ t :=
  intervalIntegral.integral_Iic_sub_Iic hi.integrableOn hi.integrableOn

lemma cumulative_eq_primitive (ρ : ℝ → ℝ) (hi : Integrable ρ) :
    cumulative ρ = fun y => cumulative ρ 0 + ∫ t in 0..y, ρ t := by
  funext y
  linarith [cumulative_sub ρ hi 0 y]

lemma hasDerivAt_cumulative {ρ : ℝ → ℝ} (hc : Continuous ρ) (hi : Integrable ρ) (y : ℝ) :
    HasDerivAt (cumulative ρ) (ρ y) y := by
  rw [cumulative_eq_primitive ρ hi]
  convert (intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 y)
    hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt).const_add
      (cumulative ρ 0) using 1
  all_goals try with_reducible_and_instances rfl

lemma contDiff_cumulative {ρ : ℝ → ℝ}
    (hρ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ρ) (hi : Integrable ρ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (cumulative ρ) := by
  rw [contDiff_infty_iff_deriv]
  refine ⟨fun y => (hasDerivAt_cumulative hρ.continuous hi y).differentiableAt, ?_⟩
  have hd : deriv (cumulative ρ) = ρ := funext fun y =>
    (hasDerivAt_cumulative hρ.continuous hi y).deriv
  rw [hd]
  exact hρ

lemma strictMono_cumulative {ρ : ℝ → ℝ} (hc : Continuous ρ) (hi : Integrable ρ)
    (hp : ∀ y, 0 < ρ y) : StrictMono (cumulative ρ) :=
  strictMono_of_hasDerivAt_pos (hasDerivAt_cumulative hc hi) hp

lemma cumulative_atBot {ρ : ℝ → ℝ} :
    Tendsto (cumulative ρ) atBot (𝓝 0) :=
  tendsto_integral_Iic_zero tendsto_id

lemma cumulative_atTop {ρ : ℝ → ℝ} (hi : Integrable ρ) (hm : ∫ y, ρ y = 1) :
    Tendsto (cumulative ρ) atTop (𝓝 1) := by
  change Tendsto (fun y : ℝ => ∫ x in Iic y, ρ x) atTop (𝓝 1)
  simpa only [hm, id_eq] using
    (aecover_Iic (μ := (volume : Measure ℝ)) tendsto_id).integral_tendsto_of_countably_generated hi

lemma cumulative_mem_Ioo {ρ : ℝ → ℝ} (hc : Continuous ρ) (hi : Integrable ρ)
    (hp : ∀ y, 0 < ρ y) (hm : ∫ y, ρ y = 1) (y : ℝ) :
    cumulative ρ y ∈ Ioo (0 : ℝ) 1 := by
  have hs := strictMono_cumulative hc hi hp
  constructor
  · exact (hs.monotone.le_of_tendsto cumulative_atBot (y-1)).trans_lt
      (hs (by linarith : y-1 < y))
  · exact (hs (by linarith : y < y+1)).trans_le
      (hs.monotone.ge_of_tendsto (cumulative_atTop hi hm) (y+1))

lemma range_cumulative {ρ : ℝ → ℝ} (hc : Continuous ρ) (hi : Integrable ρ)
    (hp : ∀ y, 0 < ρ y) (hm : ∫ y, ρ y = 1) :
    range (cumulative ρ) = Ioo (0 : ℝ) 1 := by
  apply Subset.antisymm
  · rintro _ ⟨y,rfl⟩
    exact cumulative_mem_Ioo hc hi hp hm y
  · intro z hz
    obtain ⟨a,ha⟩ := (cumulative_atBot.eventually (gt_mem_nhds hz.1)).exists
    obtain ⟨b,hb⟩ := ((cumulative_atTop hi hm).eventually (lt_mem_nhds hz.2)).exists
    exact intermediate_value_univ a b
      (continuous_iff_continuousAt.mpr fun y => (hasDerivAt_cumulative hc hi y).continuousAt)
      ⟨ha.le,hb.le⟩

lemma cumulative_quantile {ρ : ℝ → ℝ} (hc : Continuous ρ) (hi : Integrable ρ)
    (hp : ∀ y, 0 < ρ y) (hm : ∫ y, ρ y = 1) {a : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) :
    cumulative ρ (quantile ρ a) = a := by
  apply invFun_eq
  change a ∈ range (cumulative ρ)
  rw [range_cumulative hc hi hp hm]
  exact ha

lemma contDiffAt_invFun_of_deriv_ne_zero {F : ℝ → ℝ}
    (hF : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F) (hinj : Injective F)
    {x d : ℝ} (hd : HasDerivAt F d x) (hd0 : d ≠ 0) :
    ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (invFun F) (F x) := by
  let e := hF.contDiffAt.toOpenPartialHomeomorph F (hd.hasFDerivAt_equiv hd0) (by simp)
  have hx : x ∈ e.source := hF.contDiffAt.mem_toOpenPartialHomeomorph_source
    (hd.hasFDerivAt_equiv hd0) (by simp)
  have he : (e : ℝ → ℝ) = F := rfl
  have hy : F x ∈ e.target := by simpa only [he] using e.map_source hx
  have hs : e.symm (F x) = x := by simpa only [he] using e.left_inv hx
  have hi : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) e.symm (F x) := by
    apply e.contDiffAt_symm_deriv hd0 hy
    · simpa only [he, hs] using hd
    · simpa only [he, hs] using hF.contDiffAt (x := x)
  apply hi.congr_of_eventuallyEq
  filter_upwards [e.open_target.mem_nhds hy] with y hy'
  apply hinj
  have hr : F (e.symm y) = y := by simpa only [he] using e.right_inv hy'
  rw [invFun_eq ⟨e.symm y,hr⟩, hr]

lemma contDiffOn_quantile {ρ : ℝ → ℝ}
    (hρ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ρ) (hi : Integrable ρ)
    (hp : ∀ y, 0 < ρ y) (hm : ∫ y, ρ y = 1) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (quantile ρ) (Ioo (0 : ℝ) 1) := by
  intro a ha
  have hh := contDiffAt_invFun_of_deriv_ne_zero (contDiff_cumulative hρ hi)
    (strictMono_cumulative hρ.continuous hi hp).injective
    (hasDerivAt_cumulative hρ.continuous hi (quantile ρ a)) (hp _).ne'
  rw [cumulative_quantile hρ.continuous hi hp hm ha] at hh
  exact hh.contDiffWithinAt

lemma hasDerivAt_quantile {ρ : ℝ → ℝ}
    (hρ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ρ) (hi : Integrable ρ)
    (hp : ∀ y, 0 < ρ y) (hm : ∫ y, ρ y = 1) {a : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (quantile ρ) (ρ (quantile ρ a))⁻¹ a := by
  apply HasDerivAt.of_local_left_inverse
    ((contDiffOn_quantile hρ hi hp hm).contDiffAt (isOpen_Ioo.mem_nhds ha)).continuousAt
    (hasDerivAt_cumulative hρ.continuous hi _) (hp _).ne'
  filter_upwards [isOpen_Ioo.mem_nhds ha] with y hy
  exact cumulative_quantile hρ.continuous hi hp hm hy

lemma contDiff_periodize {f : ℝ → ℝ}
    (hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f) (hc : HasCompactSupport f) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (periodize f) := by
  classical
  rw [contDiff_iff_contDiffAt]
  intro x
  obtain ⟨R,hR⟩ := hc.isBounded.exists_norm_le
  obtain ⟨N,hN⟩ := exists_nat_gt (R + |x| + 1)
  let s : Finset ℤ := Finset.Icc (-(N : ℤ)) N
  have hs : ∀ᶠ y in 𝓝 x, support (fun k : ℤ => f (y+k)) ⊆ (s : Set ℤ) := by
    filter_upwards [Metric.ball_mem_nhds x (by norm_num : (0 : ℝ) < 1)] with y hy
    intro k hk
    have hy' : |y| < |x| + 1 := by
      have := abs_add_le (y-x) x
      have hy'' : |y-x| < 1 := hy
      simpa only [sub_add_cancel] using this.trans_lt (by linarith : |y-x|+|x| < |x|+1)
    have hk' : |y+(k : ℝ)| ≤ R := by
      simpa only [Real.norm_eq_abs] using hR (y+k) (subset_tsupport f hk)
    have hz : |(k : ℝ)| < (N : ℝ) := calc
      |(k : ℝ)| = |(y+k)-y| := by congr 1; ring
      _ ≤ |y+k| + |y| := abs_sub _ _
      _ < ↑N := by linarith
    have hh : -(N : ℝ) ≤ (k : ℝ) ∧ (k : ℝ) ≤ ↑N := (abs_le.mp hz.le)
    show k ∈ Finset.Icc (-(N : ℤ)) N
    rw [Finset.mem_Icc]
    exact_mod_cast hh
  have hh : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y => ∑ k ∈ s, f (y+k)) :=
    ContDiff.sum fun k _ => hf.comp (contDiff_id.add contDiff_const)
  apply hh.contDiffAt.congr_of_eventuallyEq
  filter_upwards [hs] with y hy
  exact finsum_eq_sum_of_support_subset _ hy

lemma periodize_eq_on_unit {f : ℝ → ℝ} (hs : support f ⊆ Ioo (0 : ℝ) 1)
    {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) : periodize f x = f x := by
  unfold periodize
  convert finsum_eq_single (fun k : ℤ => f (x+k)) 0 ?_ using 1
  · simp
  · intro k hk
    by_contra hn
    have hh := hs (show x+(k : ℝ) ∈ support f from hn)
    have h1 : (-1 : ℝ) < (k : ℝ) := by linarith [hx.2, hh.1]
    have h2 : (k : ℝ) < (1 : ℝ) := by linarith [hx.1, hh.2]
    have h1' : (-1 : ℤ) < k := by exact_mod_cast h1
    have h2' : k < (1 : ℤ) := by exact_mod_cast h2
    omega

lemma contDiff_cutoff_quantile {ρ ξ : ℝ → ℝ}
    (hρ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ρ) (hi : Integrable ρ)
    (hp : ∀ y, 0 < ρ y) (hm : ∫ y, ρ y = 1)
    (hξ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ξ)
    (hs : tsupport ξ ⊆ Ioo (0 : ℝ) 1) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun a => ξ a * quantile ρ a) := by
  rw [contDiff_iff_contDiffAt]
  intro a
  by_cases ha : a ∈ tsupport ξ
  · exact hξ.contDiffAt.mul ((contDiffOn_quantile hρ hi hp hm).contDiffAt
      (isOpen_Ioo.mem_nhds (hs ha)))
  · apply (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
    filter_upwards [notMem_tsupport_iff_eventuallyEq.mp ha] with b hb
    simp only [Pi.zero_apply] at hb
    simp only [hb, zero_mul]

lemma lawJitter_smooth {ρ : ℝ → ℝ} {δ : ℝ} (c : LawCutoffs δ)
    (hρ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ρ) (hi : Integrable ρ)
    (hp : ∀ y, 0 < ρ y) (hm : ∫ y, ρ y = 1) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (lawJitter ρ c) :=
  contDiff_periodize (contDiff_cutoff_quantile hρ hi hp hm c.ξ_smooth c.ξ_support)
    c.ξ_compact.mul_right

lemma lawJitter_eq_quantile {ρ : ℝ → ℝ} {δ : ℝ} (c : LawCutoffs δ)
    (hδ : 0 < δ) {a : ℝ} (ha : a ∈ Icc δ (1-δ)) :
    lawJitter ρ c a = quantile ρ a := by
  rw [lawJitter, periodize_eq_on_unit, c.ξ_one a ha, one_mul]
  · exact (support_mul_subset_left _ _).trans ((subset_tsupport _).trans c.ξ_support)
  · constructor <;> linarith [ha.1,ha.2]

lemma lawJitter_deriv_pos {ρ : ℝ → ℝ} {δ : ℝ} (c : LawCutoffs δ)
    (hρ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ρ) (hi : Integrable ρ)
    (hp : ∀ y, 0 < ρ y) (hm : ∫ y, ρ y = 1) (hδ : 0 < δ)
    {a : ℝ} (ha : a ∈ Ioo δ (1-δ)) :
    HasDerivAt (lawJitter ρ c) (ρ (quantile ρ a))⁻¹ a ∧
      0 < (ρ (quantile ρ a))⁻¹ := by
  refine ⟨?_, inv_pos.mpr (hp _)⟩
  apply (hasDerivAt_quantile hρ hi hp hm
    (show a ∈ Ioo (0 : ℝ) 1 from ⟨by linarith [ha.1], by linarith [ha.2]⟩)).congr_of_eventuallyEq
  filter_upwards [isOpen_Ioo.mem_nhds ha] with b hb
  exact lawJitter_eq_quantile c hδ ⟨hb.1.le,hb.2.le⟩

lemma lawPsi_smooth {δ : ℝ} (c : LawCutoffs δ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (lawPsi c) :=
  contDiff_periodize c.ψ_smooth c.ψ_compact

end ThreeTorus

namespace ThreeTorus
open Set Function MeasureTheory
open scoped Topology

lemma neutralCircleCutoff_coe {δ : ℝ} (c : LawCutoffs δ) (a : ℝ) :
    neutralCircleCutoff c (a : UnitAddCircle) = lawPsi c a := rfl

lemma continuous_neutralCircleCutoff {δ : ℝ} (c : LawCutoffs δ) :
    Continuous (neutralCircleCutoff c) :=
by
  apply Continuous.quotient_lift
  exact (lawPsi_smooth c).continuous

end ThreeTorus

end

end

end OAI
end

section
-- module Solutions.OAIQ13_TT.ThreeTorus_PassageMass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual Fourier passage coefficients, branch Jacobians, rounding removal, and integrated stationary mass. -/

noncomputable section
open MeasureTheory Filter Set Complex
open scoped Topology SchwartzMap FourierTransform Real
open scoped Topology
open MeasureTheory Set
open scoped ENNReal Topology

namespace ThreeTorus

lemma continuous_fourierCoeff_param {Ω : Type*} [TopologicalSpace Ω]
    [FirstCountableTopology Ω] [LocallyCompactSpace Ω]
    {f : Ω → UnitAddCircle → ℂ} (hf : Continuous f.uncurry) (j : ℤ) :
    Continuous (fun a => fourierCoeff (f a) j) := by
  have hh : Continuous (fun p : Ω × UnitAddCircle => fourier (-j) p.2*f p.1 p.2) :=
    ((fourier (-j)).continuous.comp continuous_snd).mul hf
  simpa only [fourierCoeff,smul_eq_mul,setIntegral_univ] using
    (continuous_parametric_integral_of_continuous (μ := AddCircle.haarAddCircle)
      (f := fun a θ => fourier (-j) θ*f a θ) hh isCompact_univ)

lemma continuous_passageFourierInput {m : ℤ} {H : UnitAddCircle → UnitAddCircle}
    {A : UnitAddCircle × UnitAddCircle → ℂ} (hH : Continuous H) (hA : Continuous A) :
    Continuous (passageFourierInput m H A).uncurry := by
  exact (hA.comp continuous_swap).mul ((fourier m).continuous.comp (hH.comp continuous_snd))

lemma continuous_exactPassageCoeff {m : ℤ} {H : UnitAddCircle → UnitAddCircle}
    {A : UnitAddCircle × UnitAddCircle → ℂ} (hH : Continuous H) (hA : Continuous A) (j : ℤ) :
    Continuous (exactPassageCoeff m H A j) :=
  continuous_fourierCoeff_param (continuous_passageFourierInput hH hA) j

end ThreeTorus

namespace ThreeTorus

open Function

lemma branchDensity_on {I : Set ℝ} {J g D q : ℝ → ℝ}
    (hg : ∀ x ∈ I, g (J x) = x) {x : ℝ} (hx : x ∈ I) :
    branchDensity I J g D q (J x) = q x/|D x| := by
  simp only [branchDensity,indicator_of_mem (mem_image_of_mem J hx),hg x hx]

lemma contDiffAt_invFunOn_of_deriv_ne_zero {J : ℝ → ℝ} {I : Set ℝ}
    (hJ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) J)
    (hIo : IsOpen I) (hinj : InjOn J I) {x d : ℝ} (hx : x ∈ I)
    (hd : HasDerivAt J d x) (hd0 : d ≠ 0) :
    ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (invFunOn J I) (J x) := by
  let e := hJ.contDiffAt.toOpenPartialHomeomorph J (hd.hasFDerivAt_equiv hd0) (by simp)
  have he : (e : ℝ → ℝ) = J := rfl
  have hxs : x ∈ e.source := hJ.contDiffAt.mem_toOpenPartialHomeomorph_source
    (hd.hasFDerivAt_equiv hd0) (by simp)
  have hyt : J x ∈ e.target := by simpa only [he] using e.map_source hxs
  have hix : e.symm (J x) = x := by simpa only [he] using e.left_inv hxs
  have hi : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) e.symm (J x) := by
    apply e.contDiffAt_symm_deriv hd0 hyt
    · simpa only [he,hix] using hd
    · simpa only [he,hix] using hJ.contDiffAt (x := x)
  have hnear : ∀ᶠ y in 𝓝 (J x), e.symm y ∈ I := by
    apply hi.continuousAt.eventually
    change I ∈ 𝓝 (e.symm (J x))
    rw [hix]
    exact hIo.mem_nhds hx
  apply hi.congr_of_eventuallyEq
  filter_upwards [e.open_target.mem_nhds hyt,hnear] with y hy hyI
  have hr : J (e.symm y) = y := by simpa only [he] using e.right_inv hy
  have hp := invFunOn_pos (show y ∈ J '' I from ⟨e.symm y,hyI,hr⟩)
  exact hinj hp.1 hyI (hp.2.trans hr.symm)

lemma isOpen_image_of_deriv_ne_zero {J : ℝ → ℝ} {I : Set ℝ}
    (hJ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) J)
    (hIo : IsOpen I) (hd : ∀ x ∈ I, deriv J x ≠ 0) : IsOpen (J '' I) := by
  apply isOpen_iff_mem_nhds.mpr
  rintro y ⟨x,hx,rfl⟩
  have hdx := (hJ.differentiable (by simp) x).hasDerivAt
  let e := hJ.contDiffAt.toOpenPartialHomeomorph J (hdx.hasFDerivAt_equiv (hd x hx)) (by simp)
  have he : (e : ℝ → ℝ) = J := rfl
  have hxs : x ∈ e.source := hJ.contDiffAt.mem_toOpenPartialHomeomorph_source
    (hdx.hasFDerivAt_equiv (hd x hx)) (by simp)
  have hyt : J x ∈ e.target := by simpa only [he] using e.map_source hxs
  have hix : e.symm (J x) = x := by simpa only [he] using e.left_inv hxs
  have hnear : ∀ᶠ y in 𝓝 (J x), e.symm y ∈ I := by
    apply (e.continuousAt_symm hyt).eventually
    change I ∈ 𝓝 (e.symm (J x))
    rw [hix]
    exact hIo.mem_nhds hx
  filter_upwards [e.open_target.mem_nhds hyt,hnear] with y hy hyI
  exact ⟨e.symm y,hyI,by simpa only [he] using e.right_inv hy⟩

lemma branchFamily_congr_branch {Ω : Type*} {C I : Set ℝ} {J : ℝ → ℝ} {F : ℝ × Ω → ℝ}
    (hIC : I ⊆ C) (hinj : InjOn J C) (hs : support F ⊆ I ×ˢ univ) :
    branchFamily C J F = branchFamily I J F := by
  classical
  funext p
  have him : J '' I ⊆ J '' C := image_mono hIC
  by_cases hp : p.1 ∈ J '' C
  · have hc := invFunOn_pos hp
    by_cases hpi : p.1 ∈ J '' I
    · have hi := invFunOn_pos hpi
      have hinv : invFunOn J C p.1 = invFunOn J I p.1 :=
        hinj hc.1 (hIC hi.1) (hc.2.trans hi.2.symm)
      simp [branchFamily,hp,hpi,hinv]
    · have hz : F (invFunOn J C p.1,p.2) = 0 := by
        by_contra hn
        exact hpi ⟨_, (hs hn).1, hc.2⟩
      simp [branchFamily,hp,hpi,hz]
  · have hpi : p.1 ∉ J '' I := fun h => hp (him h)
    simp [branchFamily,hp,hpi]

open scoped NNReal

end ThreeTorus

namespace ThreeTorus
open Function
open scoped ComplexConjugate

lemma exactPassageCoeff_neg (m : ℤ) (H : UnitAddCircle → UnitAddCircle)
    (A : UnitAddCircle × UnitAddCircle → ℂ) (j : ℤ) (a : UnitAddCircle) :
    exactPassageCoeff (-m) H (fun x => conj (A x)) j a =
      conj (exactPassageCoeff m H A (-j) a) := by
  unfold exactPassageCoeff fourierCoeff passageFourierInput
  rw [← integral_conj]
  apply integral_congr_ae
  filter_upwards [] with θ
  simp only [smul_eq_mul, neg_neg, map_mul, fourier_neg]

end ThreeTorus

end

end OAI
end

section
-- module Solutions.OAIQ13_TT.ThreeTorus_PassageDensity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Unfolded and folded retained densities, branch kernels, residue sampling, and spectral limits. -/

noncomputable section
open MeasureTheory Filter Set Complex
open scoped Topology SchwartzMap FourierTransform Real
open scoped Topology
open MeasureTheory Set
open scoped ENNReal Topology

noncomputable section
open MeasureTheory Set
open scoped Topology
namespace ThreeTorus

lemma circle_integral_lift (o : ℝ) (q : UnitAddCircle → ℝ) :
    (∫ x, circleDensityLift o q x) = ∫ a, q a ∂AddCircle.haarAddCircle := by
  rw [circleDensityLift,integral_indicator measurableSet_Ioc]
  have h := AddCircle.integral_preimage 1 o q
  simpa [AddCircle.volume_eq_smul_haarAddCircle] using h

lemma integrable_circleDensityLift {q : UnitAddCircle → ℝ}
    (hq : Integrable q AddCircle.haarAddCircle) (o : ℝ) :
    Integrable (circleDensityLift o q) := by
  have hmp : MeasurePreserving (fun x : ℝ => (x : UnitAddCircle))
      (volume.restrict (Ioc o (o+1))) AddCircle.haarAddCircle := by
    simpa [AddCircle.volume_eq_smul_haarAddCircle] using AddCircle.measurePreserving_mk 1 o
  have hi : IntegrableOn (fun x : ℝ => q (x : UnitAddCircle)) (Ioc o (o+1)) :=
    (hmp.integrable_comp hq.aestronglyMeasurable).2 hq
  exact hi.integrable_indicator measurableSet_Ioc

/-- Lifting a circle density on one period commutes with every measurable
spectral pushforward. This includes the actual jitter, not just polynomial tests. -/
lemma circleDensityLift_pushforward {Y : Type*} [MeasurableSpace Y]
    {q : UnitAddCircle → ℝ} (hq : Integrable q AddCircle.haarAddCircle)
    {T : UnitAddCircle → Y} (hT : Measurable T) (o : ℝ) :
    ((volume : Measure ℝ).withDensityᵥ (circleDensityLift o q)).map
      (fun x : ℝ => T (x : UnitAddCircle)) =
    (AddCircle.haarAddCircle.withDensityᵥ q).map T := by
  have hTm : Measurable (fun x : ℝ => T (x : UnitAddCircle)) := hT.comp AddCircle.measurable_mk'
  ext s hs
  rw [VectorMeasure.map_apply _ hTm hs,VectorMeasure.map_apply _ hT hs,
    withDensityᵥ_apply (integrable_circleDensityLift hq o) (hTm hs),
    withDensityᵥ_apply hq (hT hs)]
  rw [← integral_indicator (hTm hs),← integral_indicator (hT hs)]
  rw [← circle_integral_lift o ((T ⁻¹' s).indicator q)]
  congr 1
  funext x
  by_cases hx : x ∈ Ioc o (o+1) <;> by_cases hxs : T (x : UnitAddCircle) ∈ s <;>
    simp [circleDensityLift,hx,hxs]

lemma circleDensityLift_eq {q : UnitAddCircle → ℝ} {q₀ : ℝ → ℝ} {o : ℝ}
    (he : ∀ x ∈ Ioc o (o+1), q (x : UnitAddCircle) = q₀ x)
    (hs : Function.support q₀ ⊆ Ioc o (o+1)) : circleDensityLift o q = q₀ := by
  funext x
  by_cases hx : x ∈ Ioc o (o+1)
  · simp [circleDensityLift,hx,he x hx]
  · have hzero : q₀ x = 0 := by by_contra hn; exact hx (hs hn)
    simp [circleDensityLift,hx,hzero]

lemma integrable_branchDensity {I : Set ℝ} {J g D q : ℝ → ℝ}
    (hI : MeasurableSet I) (himage : MeasurableSet (J '' I))
    (hJ : ∀ x ∈ I, HasDerivWithinAt J (D x) I x) (hinj : InjOn J I)
    (hg : ∀ x ∈ I, g (J x) = x) (hD : ∀ x ∈ I, D x ≠ 0)
    (hq : IntegrableOn q I) : Integrable (branchDensity I J g D q) := by
  have he : IntegrableOn (branchDensity I J g D q) (J '' I) := by
    rw [integrableOn_image_iff_integrableOn_abs_deriv_smul hI hJ hinj]
    apply hq.congr (ae_restrict_of_forall_mem hI (fun x hx => ?_))
    rw [smul_eq_mul,branchDensity_on hg hx]
    field_simp [abs_ne_zero.mpr (hD x hx)]
  have hs : (J '' I).indicator (branchDensity I J g D q) = branchDensity I J g D q := by
    funext y
    by_cases hy : y ∈ J '' I
    · exact indicator_of_mem hy _
    · simp [hy,branchDensity]
  simpa only [hs] using he.integrable_indicator himage

/-- Exact pushforward of the old squared coefficient on a branch. The only
inverse assumptions are the ordinary left-inverse identities on that branch. -/
lemma branchDensity_pushforward {I : Set ℝ} {J g D q : ℝ → ℝ}
    (hI : MeasurableSet I) (himage : MeasurableSet (J '' I)) (hJm : Measurable J)
    (hJ : ∀ x ∈ I, HasDerivWithinAt J (D x) I x) (hinj : InjOn J I)
    (hg : ∀ x ∈ I, g (J x) = x) (hD : ∀ x ∈ I, D x ≠ 0)
    (hq : Integrable q) (hqs : Function.support q ⊆ I) :
    ((volume : Measure ℝ).withDensityᵥ q).map J =
      (volume : Measure ℝ).withDensityᵥ (branchDensity I J g D q) := by
  have hK := integrable_branchDensity hI himage hJ hinj hg hD hq.integrableOn
  ext s hs
  rw [VectorMeasure.map_apply _ hJm hs,withDensityᵥ_apply hq (hJm hs),withDensityᵥ_apply hK hs]
  rw [← integral_indicator (hJm hs),← integral_indicator hs]
  have hleft : (∫ x, (J ⁻¹' s).indicator q x) = ∫ x in I, (J ⁻¹' s).indicator q x := by
    symm
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    have hqx : q x = 0 := by
      by_contra hh
      exact hx (hqs hh)
    by_cases hxs : x ∈ J ⁻¹' s <;> simp [hxs,hqx]
  have hright : (∫ y, s.indicator (branchDensity I J g D q) y) =
      ∫ y in J '' I, s.indicator (branchDensity I J g D q) y := by
    symm
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro y hy
    by_cases hys : y ∈ s <;> simp [hys,branchDensity,hy]
  rw [hleft,hright,integral_image_eq_integral_abs_deriv_smul hI hJ hinj]
  apply setIntegral_congr_fun hI
  intro x hx
  dsimp only
  rw [smul_eq_mul]
  by_cases hxs : J x ∈ s
  · rw [indicator_of_mem (show x ∈ J ⁻¹' s from hxs),indicator_of_mem hxs,branchDensity_on hg hx]
    field_simp [abs_ne_zero.mpr (hD x hx)]
  · rw [indicator_of_notMem (show x ∉ J ⁻¹' s from hxs),indicator_of_notMem hxs,mul_zero]

lemma density_map_congr_support {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure X} {f : X → ℝ} (hf : Integrable f μ)
    {T₁ T₂ : X → Y} (h₁ : Measurable T₁) (h₂ : Measurable T₂)
    (he : ∀ x, f x ≠ 0 → T₁ x = T₂ x) :
    (μ.withDensityᵥ f).map T₁ = (μ.withDensityᵥ f).map T₂ := by
  classical
  ext s hs
  rw [VectorMeasure.map_apply _ h₁ hs,VectorMeasure.map_apply _ h₂ hs,
    withDensityᵥ_apply hf (h₁ hs),withDensityᵥ_apply hf (h₂ hs),
    ← integral_indicator (h₁ hs),← integral_indicator (h₂ hs)]
  congr 1
  funext x
  change (if T₁ x ∈ s then f x else 0) = (if T₂ x ∈ s then f x else 0)
  by_cases hx : f x = 0
  · simp [hx]
  · rw [he x hx]

/-- The branch-Jacobian formula on the actual circle. The global periodic
jitter need not be injective; only the good arc bearing the weight is used. -/
lemma circle_branch_pushforward {q : UnitAddCircle → ℝ} {q₀ J₀ g D : ℝ → ℝ}
    {J : UnitAddCircle → ℝ} {o : ℝ} {I : Set ℝ}
    (hq : Integrable q AddCircle.haarAddCircle)
    (hq₀ : ∀ x ∈ Ioc o (o+1), q (x : UnitAddCircle) = q₀ x)
    (hq₀s : Function.support q₀ ⊆ Ioc o (o+1)) (hqs : Function.support q₀ ⊆ I)
    (hj : Measurable J) (hj₀ : Measurable J₀)
    (hJe : ∀ x ∈ I, J (x : UnitAddCircle) = J₀ x)
    (hI : MeasurableSet I) (himage : MeasurableSet (J₀ '' I))
    (hJ : ∀ x ∈ I, HasDerivWithinAt J₀ (D x) I x) (hinj : InjOn J₀ I)
    (hg : ∀ x ∈ I, g (J₀ x) = x) (hD : ∀ x ∈ I, D x ≠ 0) :
    (AddCircle.haarAddCircle.withDensityᵥ q).map J =
      (volume : Measure ℝ).withDensityᵥ (branchDensity I J₀ g D q₀) := by
  have hlift := circleDensityLift_eq hq₀ hq₀s
  have hi : Integrable q₀ := by rw [← hlift]; exact integrable_circleDensityLift hq o
  rw [← circleDensityLift_pushforward hq hj o,hlift]
  rw [density_map_congr_support (T₁ := fun x : ℝ => J (x : UnitAddCircle)) hi (hj.comp AddCircle.measurable_mk') hj₀
    (fun x hx => hJe x (hqs hx))]
  exact branchDensity_pushforward hI himage hj₀ hJ hinj hg hD hi hqs

/-- Exact Jacobian cancellation in the unfolded output frequency t=(j+y)/N. -/
lemma temporalFrequency_pushforward {q : ℝ → ℝ} (hq : Integrable q)
    {n : ℝ} (hn : 0 < n) (j : ℝ) :
    ((volume : Measure ℝ).withDensityᵥ (fun y => n⁻¹*q y)).map (fun y => (j+y)/n) =
      (volume : Measure ℝ).withDensityᵥ (fun t => q (n*t-j)) := by
  have hmap : Measurable (fun y : ℝ => (j+y)/n) := by fun_prop
  have hq' : Integrable (fun t => q (n*t-j)) := by
    simpa only [sub_eq_add_neg] using
      (integrable_comp_mul_left_iff (fun x => q (x+ -j)) hn.ne').2 (hq.comp_add_right (-j))
  ext s hs
  rw [VectorMeasure.map_apply _ hmap hs,withDensityᵥ_apply (hq.const_mul n⁻¹) (hmap hs),
    withDensityᵥ_apply hq' hs,integral_const_mul]
  let F : ℝ → ℝ := ((fun y : ℝ => (j+y)/n) ⁻¹' s).indicator q
  have he : (fun t => F (n*t-j)) = s.indicator (fun t => q (n*t-j)) := by
    funext t
    by_cases ht : t ∈ s <;> simp [F,ht,hn.ne']
  rw [← integral_indicator (hmap hs),← integral_indicator hs,← he]
  change n⁻¹*(∫ y, F y) = ∫ t, F (n*t-j)
  rw [Measure.integral_comp_mul_left (fun x => F (x-j)) n,integral_sub_right_eq_self]
  simp only [smul_eq_mul,abs_of_pos (inv_pos.mpr hn)]

/-- Pushforward through a fixed smooth jitter followed by the output affine frequency.
This is the exact (not weak or asymptotic) density appearing in the passage. -/
lemma temporalFrequency_pushforward_comp {X : Type*} [MeasurableSpace X]
    {μ : Measure X} {W : X → ℝ} {q : ℝ → ℝ} {J : X → ℝ}
    (hW : Integrable W μ) (hq : Integrable q) (hJ : Measurable J)
    (hpush : (μ.withDensityᵥ W).map J = (volume : Measure ℝ).withDensityᵥ q)
    {n : ℝ} (hn : 0 < n) (j : ℝ) :
    (μ.withDensityᵥ (fun a => n⁻¹*W a)).map (fun a => (j+J a)/n) =
      (volume : Measure ℝ).withDensityᵥ (fun t => q (n*t-j)) := by
  have haf : Measurable (fun y : ℝ => (j+y)/n) := by fun_prop
  have hcomp (v : VectorMeasure X ℝ) :
      v.map (fun a => (j+J a)/n) = (v.map J).map (fun y : ℝ => (j+y)/n) := by
    ext s hs
    have hcompm : Measurable (fun a => (j+J a)/n) := haf.comp hJ
    rw [VectorMeasure.map_apply _ hcompm hs,
      VectorMeasure.map_apply _ haf hs,VectorMeasure.map_apply _ hJ (haf hs)]
    rfl
  rw [hcomp]
  have he : μ.withDensityᵥ (fun a => n⁻¹*W a) = n⁻¹ • μ.withDensityᵥ W := by
    ext s hs
    rw [withDensityᵥ_apply (hW.const_mul _) hs,smul_apply,withDensityᵥ_apply hW hs,
      integral_const_mul,smul_eq_mul]
  have heq : (volume : Measure ℝ).withDensityᵥ (fun y => n⁻¹*q y) =
      n⁻¹ • (volume : Measure ℝ).withDensityᵥ q := by
    ext s hs
    rw [withDensityᵥ_apply (hq.const_mul _) hs,smul_apply,withDensityᵥ_apply hq hs,
      integral_const_mul,smul_eq_mul]
  rw [he,VectorMeasure.map_smul,hpush,← heq]
  exact temporalFrequency_pushforward hq hn j

lemma scaledBranchKernel_eq {I : Set ℝ} (J g D q : ℝ → ℝ) {s : ℝ} (hs : s ≠ 0) (y : ℝ) :
    branchDensity I (fun x => s*J x) (fun y => g (y/s)) (fun x => s*D x) q y =
      scaledBranchKernel I J g D q s y := by
  classical
  have he : y ∈ (fun x => s*J x) '' I ↔ y/s ∈ J '' I := by
    constructor
    · rintro ⟨x,hx,hxy⟩
      exact ⟨x,hx,by rw [← hxy]; field_simp⟩
    · rintro ⟨x,hx,hxy⟩
      exact ⟨x,hx,by change s*J x = y; rw [hxy]; field_simp⟩
  by_cases hy : y/s ∈ J '' I
  · simp only [branchDensity,scaledBranchKernel,indicator_of_mem hy,
      indicator_of_mem (he.mpr hy),abs_mul]
    ring
  · simp only [branchDensity,scaledBranchKernel,indicator_of_notMem hy,
      indicator_of_notMem (fun h => hy (he.mp h)),mul_zero]

lemma integrable_scaledBranchKernel {I : Set ℝ} {J g D q : ℝ → ℝ}
    (hq : Integrable (branchDensity I J g D q)) {s : ℝ} (hs : s ≠ 0) :
    Integrable (scaledBranchKernel I J g D q s) :=
  ((integrable_comp_div_iff _ hs).2 hq).const_mul _

/-- The exact branch kernel in the new temporal coordinate, on the torus.
Only the good arc need be injective, as in the geometric passage. -/
lemma circle_mode_pushforward {q : UnitAddCircle → ℝ} {q₀ J₀ g D : ℝ → ℝ}
    {J : UnitAddCircle → ℝ} {o : ℝ} {I : Set ℝ}
    (hq : Integrable q AddCircle.haarAddCircle)
    (hq₀ : ∀ x ∈ Ioc o (o+1), q (x : UnitAddCircle) = q₀ x)
    (hq₀s : Function.support q₀ ⊆ Ioc o (o+1)) (hqs : Function.support q₀ ⊆ I)
    (hj : Measurable J) (hj₀ : Measurable J₀)
    (hJe : ∀ x ∈ I, J (x : UnitAddCircle) = J₀ x)
    (hI : MeasurableSet I) (himage : MeasurableSet (J₀ '' I))
    (hJ : ∀ x ∈ I, HasDerivWithinAt J₀ (D x) I x) (hinj : InjOn J₀ I)
    (hg : ∀ x ∈ I, g (J₀ x) = x) (hD : ∀ x ∈ I, D x ≠ 0)
    {s n : ℝ} (hs : s ≠ 0) (hn : 0 < n) (j : ℝ) :
    (AddCircle.haarAddCircle.withDensityᵥ (fun a => n⁻¹*q a)).map
        (fun a => (j+s*J a)/n) =
      (volume : Measure ℝ).withDensityᵥ
        (fun t => scaledBranchKernel I J₀ g D q₀ s (n*t-j)) := by
  have hqi : Integrable q₀ := by
    rw [← circleDensityLift_eq hq₀ hq₀s]
    exact integrable_circleDensityLift hq o
  have hK := integrable_branchDensity hI himage hJ hinj hg hD hqi.integrableOn
  have hsim : MeasurableSet ((fun x => s*J₀ x) '' I) := by
    have he : (fun x => s*J₀ x) '' I = (fun y : ℝ => s*y) '' (J₀ '' I) := by
      rw [image_image]
    rw [he]
    exact (Homeomorph.mulLeft₀ s hs).measurableEmbedding.measurableSet_image.mpr himage
  have hp := circle_branch_pushforward (g := fun y => g (y/s)) hq hq₀ hq₀s hqs
    (measurable_const.mul hj) (measurable_const.mul hj₀)
    (fun x hx => congrArg (fun y => s*y) (hJe x hx)) hI hsim
    (fun x hx => (hJ x hx).const_mul s)
    (fun x hx y hy he => hinj hx hy (mul_left_cancel₀ hs he))
    (fun x hx => show g (s*J₀ x/s) = x by simpa [hs] using hg x hx)
    (fun x hx => mul_ne_zero hs (hD x hx))
  have he : branchDensity I (fun x => s*J₀ x) (fun y => g (y/s)) (fun x => s*D x) q₀ =
      scaledBranchKernel I J₀ g D q₀ s := funext (scaledBranchKernel_eq _ _ _ _ hs)
  change (AddCircle.haarAddCircle.withDensityᵥ q).map (fun a => s*J a) =
    (volume : Measure ℝ).withDensityᵥ
      (branchDensity I (fun x => s*J₀ x) (fun y => g (y/s)) (fun x => s*D x) q₀) at hp
  rw [he] at hp
  exact temporalFrequency_pushforward_comp hq (integrable_scaledBranchKernel hK hs)
    (measurable_const.mul hj) hp hn j

lemma integrable_unfoldedModeDensity {I : Set ℝ} {J g D q₀ : ℝ → ℝ}
    (hI : MeasurableSet I) (himage : MeasurableSet (J '' I))
    (hJ : ∀ x ∈ I, HasDerivWithinAt J (D x) I x) (hinj : InjOn J I)
    (hg : ∀ x ∈ I, g (J x) = x) (hD : ∀ x ∈ I, D x ≠ 0)
    (hq : Integrable q₀) {n j : ℝ} (hn : 0 < n) (hj : j ≠ 0) :
    Integrable (unfoldedModeDensity I J g D q₀ n j) := by
  have hi := integrable_scaledBranchKernel
    (integrable_branchDensity hI himage hJ hinj hg hD (hq.const_mul n).integrableOn)
    (div_ne_zero hj hn.ne')
  change Integrable (fun t => scaledBranchKernel I J g D (fun a => n*q₀ a) (j/n) (n*t-j))
  simpa only [sub_eq_add_neg] using
    (integrable_comp_mul_left_iff (fun x =>
      scaledBranchKernel I J g D (fun a => n*q₀ a) (j/n) (x+ -j)) hn.ne').2
      (hi.comp_add_right (-j))

/-- Exact density of an actual circle mode before any stationary approximation. -/
lemma unfoldedModeDensity_pushforward {q : UnitAddCircle → ℝ} {q₀ J₀ g D : ℝ → ℝ}
    {J : UnitAddCircle → ℝ} {o : ℝ} {I : Set ℝ}
    (hq : Integrable q AddCircle.haarAddCircle)
    (hq₀ : ∀ x ∈ Ioc o (o+1), q (x : UnitAddCircle) = q₀ x)
    (hq₀s : Function.support q₀ ⊆ Ioc o (o+1)) (hqs : Function.support q₀ ⊆ I)
    (hj : Measurable J) (hj₀ : Measurable J₀)
    (hJe : ∀ x ∈ I, J (x : UnitAddCircle) = J₀ x)
    (hI : MeasurableSet I) (himage : MeasurableSet (J₀ '' I))
    (hJ : ∀ x ∈ I, HasDerivWithinAt J₀ (D x) I x) (hinj : InjOn J₀ I)
    (hg : ∀ x ∈ I, g (J₀ x) = x) (hD : ∀ x ∈ I, D x ≠ 0)
    {n j : ℝ} (hn : 0 < n) (hjn : j ≠ 0) :
    (AddCircle.haarAddCircle.withDensityᵥ q).map
        (fun a => (j+(j/n)*J a)/n) =
      (volume : Measure ℝ).withDensityᵥ (unfoldedModeDensity I J₀ g D q₀ n j) := by
  have hsupp (L : Set ℝ) (hh : Function.support q₀ ⊆ L) :
      Function.support (fun a => n*q₀ a) ⊆ L := by
    intro x hx
    apply hh
    intro hz
    exact hx (by simp only [hz,mul_zero])
  have hp := circle_mode_pushforward (q := fun a => n*q a) (q₀ := fun a => n*q₀ a)
    (s := j/n) (hq.const_mul n) (fun x hx => congrArg (fun y => n*y) (hq₀ x hx))
    (hsupp _ hq₀s) (hsupp _ hqs) hj hj₀ hJe hI himage hJ hinj hg hD
    (div_ne_zero hjn hn.ne') hn j
  change _ = (volume : Measure ℝ).withDensityᵥ
    (fun t => scaledBranchKernel I J₀ g D (fun a => n*q₀ a) (j/n) (n*t-j))
  simpa only [← mul_assoc,inv_mul_cancel₀ hn.ne',one_mul] using hp

end ThreeTorus

noncomputable section
open Set Function Filter
open scoped Topology NNReal
noncomputable section
open MeasureTheory Filter Set
open scoped Topology NNReal

namespace ThreeTorus
open Function Set MeasureTheory Filter
open scoped Topology

lemma stationaryWeight_family_of_branch {Ω : Type*} {C I : Set ℝ}
    {J : ℝ → ℝ} {A : Ω → ℝ → ℂ}
    (hIC : I ⊆ C) (hi : InjOn J C) (hs : ∀ a, support (A a) ⊆ I) :
    (fun p : ℝ × Ω => stationaryWeight C J (A p.2) p.1) =
      branchFamily I J (fun p : ℝ × Ω => ‖A p.2 p.1‖^2) := by
  have he (C : Set ℝ) :
      (fun p : ℝ × Ω => stationaryWeight C J (A p.2) p.1) =
      branchFamily C J (fun p : ℝ × Ω => ‖A p.2 p.1‖^2) := by
    funext p
    simp only [stationaryWeight,branchDensity,branchFamily]
    split_ifs with h <;> simp [h]
  rw [he]
  apply branchFamily_congr_branch hIC hi
  intro p hp
  refine ⟨hs p.2 ?_,mem_univ _⟩
  intro hz
  apply hp
  simp [hz]

end ThreeTorus

namespace ThreeTorus
open Function Set MeasureTheory Filter
open scoped Topology

lemma retainedCircleWeight_integrable {ψ : UnitAddCircle → ℝ}
    {χ : ℝ → UnitAddCircle → ℝ} {c : ℕ → ℤ → UnitAddCircle → ℂ}
    (hψ : Continuous ψ) (hχ : Continuous χ.uncurry) (hc : ∀ n j, Continuous (c n j))
    (n : ℕ) (j : ℤ) :
    Integrable (retainedCircleWeight ψ χ c n j) AddCircle.haarAddCircle := by
  apply Continuous.integrable_of_hasCompactSupport _ (HasCompactSupport.of_compactSpace _)
  exact ((hψ.pow 2).mul ((hχ.comp (continuous_const.prodMk continuous_id)).pow 2)).mul
    ((hc n j).norm.pow 2)

end ThreeTorus

namespace ThreeTorus
open Function Set MeasureTheory Filter
open scoped Topology

lemma scaled_speed_good_branch {V : ℝ → ℝ} {m : ℤ} {l u R : ℝ}
    (hm : m ≠ 0) (hR : 0 < R)
    (hV : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) V)
    (hd : ∀ x ∈ Icc (l-2*R) (u+2*R), 0 < deriv V x) :
    InjOn (fun x => (m:ℝ)*V x) (Icc (l-R) (u+R)) ∧
      ∀ x ∈ Ioo (l-R) (u+R), deriv (fun x => (m:ℝ)*V x) x ≠ 0 := by
  have hsub : Icc (l-R) (u+R) ⊆ Icc (l-2*R) (u+2*R) := by
    intro x hx
    exact ⟨by linarith [hx.1],by linarith [hx.2]⟩
  have hi : InjOn V (Icc (l-R) (u+R)) :=
    (strictMonoOn_of_deriv_pos (convex_Icc _ _) hV.continuous.continuousOn
      (fun x hx => hd x (hsub (interior_subset hx)))).injOn
  have hm' : (m:ℝ) ≠ 0 := by exact_mod_cast hm
  refine ⟨?_,?_⟩
  · intro x hx y hy he
    exact hi hx hy (mul_left_cancel₀ hm' he)
  · intro x hx
    rw [deriv_const_mul _ (hV.differentiable (by simp) x)]
    exact mul_ne_zero hm' (hd x (hsub (Ioo_subset_Icc_self hx))).ne'

end ThreeTorus

namespace ThreeTorus
open Function Set MeasureTheory Filter
open scoped Topology

lemma stationaryWeight_support_subset {C K : Set ℝ} {J : ℝ → ℝ} {A : ℝ → ℂ}
    (hA : support A ⊆ K) : support (stationaryWeight C J A) ⊆ J '' K := by
  classical
  intro s hs
  have hsC : s ∈ J '' C := by
    by_contra hn
    exact hs (by simp [stationaryWeight,branchDensity,hn])
  have hp := invFunOn_pos hsC
  refine ⟨invFunOn J C s,hA ?_,hp.2⟩
  intro hz
  exact hs (by simp [stationaryWeight,branchDensity,hsC,show A (invFunOn J C s) = 0 from hz])

end ThreeTorus

noncomputable section
open MeasureTheory Set Function
open scoped Topology ENNReal
namespace ThreeTorus

lemma measurable_periodizedReal {q : ℝ → ℝ} (hq : Measurable q) :
    Measurable (periodizedReal q) := by
  exact Measurable.tsum (fun k => hq.comp (measurable_id.add_const (k:ℝ)))

lemma measurable_foldCircleDensity {q : ℝ → ℝ} (hq : Measurable q) :
    Measurable (foldCircleDensity q) := by
  exact ((measurable_periodizedReal hq).comp measurable_subtype_coe).comp
    (AddCircle.measurableEquivIoc 1 0).measurable

lemma foldCircleDensity_coe {q : ℝ → ℝ} {x : ℝ} (hx : x ∈ Ioc 0 1) :
    foldCircleDensity q (x : UnitAddCircle) = periodizedReal q x := by
  exact AddCircle.liftIoc_coe_apply (by simpa using hx)

lemma integral_real_eq_lattice (q : ℝ → ℝ) (hq : Integrable q) :
    (∫ x, q x) = ∑' k : ℤ, ∫ x in Ioc (0:ℝ) 1, q (x+k) := by
  have h := (isAddFundamentalDomain_Ioc (by norm_num : (0:ℝ)<1) 0).integral_eq_tsum'' q hq
  rw [← intUnitEquiv.tsum_eq] at h
  have he (k : ℤ) (x : ℝ) : intUnitEquiv k +ᵥ x = x+(k:ℝ) := by
    change (k • (1:ℝ))+x = x+(k:ℝ)
    simp [add_comm]
  simpa only [he,zero_add] using h

lemma lintegral_real_eq_lattice (q : ℝ → ℝ≥0∞) :
    (∫⁻ x, q x) = ∑' k : ℤ, ∫⁻ x in Ioc (0:ℝ) 1, q (x+k) := by
  have h := (isAddFundamentalDomain_Ioc (by norm_num : (0:ℝ)<1) 0).lintegral_eq_tsum'' q
  rw [← intUnitEquiv.tsum_eq] at h
  have he (k : ℤ) (x : ℝ) : intUnitEquiv k +ᵥ x = x+(k:ℝ) := by
    change (k • (1:ℝ))+x = x+(k:ℝ)
    simp [add_comm]
  simpa only [he,zero_add] using h

lemma integrableOn_periodizedReal {q : ℝ → ℝ} (hm : Measurable q) (hq : Integrable q) :
    IntegrableOn (periodizedReal q) (Ioc 0 1) := by
  refine ⟨(measurable_periodizedReal hm).aestronglyMeasurable,?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  calc
    (∫⁻ x in Ioc (0:ℝ) 1, ‖periodizedReal q x‖ₑ) ≤
        ∫⁻ x in Ioc (0:ℝ) 1, ∑' k : ℤ, ‖q (x+k)‖ₑ :=
      lintegral_mono (fun x => enorm_tsum_le_tsum_enorm)
    _ = ∑' k : ℤ, ∫⁻ x in Ioc (0:ℝ) 1, ‖q (x+k)‖ₑ :=
      lintegral_tsum (fun k => (hm.comp (measurable_id.add_const (k:ℝ))).enorm.aemeasurable)
    _ = ∫⁻ x, ‖q x‖ₑ := (lintegral_real_eq_lattice (fun x => ‖q x‖ₑ)).symm
    _ < ∞ := hq.hasFiniteIntegral

lemma integral_periodizedReal {q : ℝ → ℝ} (hm : Measurable q) (hq : Integrable q) :
    (∫ x in Ioc (0:ℝ) 1, periodizedReal q x) = ∫ x, q x := by
  change (∫ x in Ioc (0:ℝ) 1, ∑' k : ℤ, q (x+k)) = ∫ x, q x
  rw [integral_tsum]
  · exact (integral_real_eq_lattice q hq).symm
  · exact fun k => (hm.comp (measurable_id.add_const (k:ℝ))).aestronglyMeasurable
  · rw [← lintegral_real_eq_lattice (fun x => ‖q x‖ₑ)]
    exact hq.hasFiniteIntegral.ne

lemma integrable_foldCircleDensity {q : ℝ → ℝ} (hm : Measurable q) (hq : Integrable q) :
    Integrable (foldCircleDensity q) AddCircle.haarAddCircle := by
  have hp : MeasurePreserving (fun x : ℝ => (x:UnitAddCircle))
      (volume.restrict (Ioc (0:ℝ) 1)) AddCircle.haarAddCircle := by
    simpa [AddCircle.volume_eq_smul_haarAddCircle] using AddCircle.measurePreserving_mk 1 0
  apply (hp.integrable_comp (measurable_foldCircleDensity hm).aestronglyMeasurable).1
  exact (integrableOn_periodizedReal hm hq).congr
    (ae_restrict_of_forall_mem measurableSet_Ioc (fun x hx => (foldCircleDensity_coe hx).symm))

lemma integral_foldCircleDensity {q : ℝ → ℝ} (hm : Measurable q) (hq : Integrable q) :
    (∫ a, foldCircleDensity q a ∂AddCircle.haarAddCircle) = ∫ x, q x := by
  have he := AddCircle.integral_preimage 1 0 (foldCircleDensity q)
  simp only [zero_add,AddCircle.volume_eq_smul_haarAddCircle,ENNReal.ofReal_one,
    one_smul] at he
  rw [← he]
  exact (setIntegral_congr_fun measurableSet_Ioc (fun x hx => foldCircleDensity_coe hx)).trans
    (integral_periodizedReal hm hq)

lemma quotient_add_int (x : ℝ) (k : ℤ) : ((x+k : ℝ):UnitAddCircle) = (x:UnitAddCircle) := by
  have h : ((k:ℝ):UnitAddCircle) = 0 :=
    (AddCircle.coe_eq_zero_iff 1).2 ⟨k,by simp⟩
  rw [AddCircle.coe_add,h,add_zero]

lemma foldCircleDensity_indicator (q : ℝ → ℝ) (s : Set UnitAddCircle) :
    foldCircleDensity (((fun x : ℝ => (x:UnitAddCircle)) ⁻¹' s).indicator q) =
      s.indicator (foldCircleDensity q) := by
  classical
  funext a
  let x : ℝ := (AddCircle.equivIoc 1 0 a).1
  have hx : x ∈ Ioc (0:ℝ) 1 := by simpa using (AddCircle.equivIoc 1 0 a).2
  have ha : (x:UnitAddCircle) = a := (AddCircle.equivIoc 1 0).symm_apply_apply a
  rw [← ha]
  by_cases hs : (x:UnitAddCircle) ∈ s
  · simp only [indicator_of_mem hs,foldCircleDensity_coe hx,periodizedReal]
    apply tsum_congr
    intro k
    exact indicator_of_mem (by simpa only [mem_preimage,quotient_add_int] using hs) q
  · simp only [indicator_of_notMem hs,foldCircleDensity_coe hx,periodizedReal]
    have hz (k : ℤ) : (((fun x : ℝ => (x:UnitAddCircle)) ⁻¹' s).indicator q) (x+k) = 0 :=
      indicator_of_notMem (by simpa only [mem_preimage,quotient_add_int] using hs) q
    simp only [hz,tsum_zero]

/-- Folding is exactly pushforward under the quotient, not a replacement kernel. -/
lemma foldCircleDensity_pushforward {q : ℝ → ℝ} (hm : Measurable q) (hq : Integrable q) :
    ((volume : Measure ℝ).withDensityᵥ q).map (fun x : ℝ => (x:UnitAddCircle)) =
      AddCircle.haarAddCircle.withDensityᵥ (foldCircleDensity q) := by
  ext s hs
  rw [VectorMeasure.map_apply _ AddCircle.measurable_mk' hs,
    withDensityᵥ_apply hq (AddCircle.measurable_mk' hs),
    withDensityᵥ_apply (integrable_foldCircleDensity hm hq) hs,
    ← integral_indicator (AddCircle.measurable_mk' hs),← integral_indicator hs]
  rw [← foldCircleDensity_indicator]
  exact (integral_foldCircleDensity (hm.indicator (AddCircle.measurable_mk' hs))
    (hq.indicator (AddCircle.measurable_mk' hs))).symm

lemma periodizedReal_add_int (q : ℝ → ℝ) (x : ℝ) (j : ℤ) :
    periodizedReal q (x+j) = periodizedReal q x := by
  have h := (Equiv.addLeft j).tsum_eq (fun k : ℤ => q (x+k))
  change (∑' k : ℤ, q (x+(j:ℝ)+(k:ℝ))) = ∑' k : ℤ, q (x+(k:ℝ))
  rw [← h]
  apply tsum_congr
  intro k
  congr 1
  change x+(j:ℝ)+(k:ℝ) = x+((j+k:ℤ):ℝ)
  simp only [Int.cast_add,add_assoc]

/-- The displayed lattice formula holds for every real representative. -/
lemma foldCircleDensity_coe_all (q : ℝ → ℝ) (x : ℝ) :
    foldCircleDensity q (x:UnitAddCircle) = ∑' k : ℤ, q (x+k) := by
  let y : ℝ := (AddCircle.equivIoc 1 0 (x:UnitAddCircle)).1
  have hy : y ∈ Ioc (0:ℝ) 1 := by simpa using (AddCircle.equivIoc 1 0 (x:UnitAddCircle)).2
  have hxy : (y:UnitAddCircle) = (x:UnitAddCircle) :=
    (AddCircle.equivIoc 1 0).symm_apply_apply (x:UnitAddCircle)
  have hz : ((y-x:ℝ):UnitAddCircle) = 0 := by rw [AddCircle.coe_sub,hxy,sub_self]
  obtain ⟨k,hk⟩ := (AddCircle.coe_eq_zero_iff 1).1 hz
  have he : y = x+(k:ℝ) := by simpa only [zsmul_eq_mul,mul_one] using eq_add_of_sub_eq' hk.symm
  rw [← hxy,foldCircleDensity_coe hy,he,periodizedReal_add_int]
  rfl

end ThreeTorus

namespace ThreeTorus
open MeasureTheory Set Function Filter
open scoped Topology

lemma measurable_branchDensity_smooth {I : Set ℝ} {J q : ℝ → ℝ}
    (hJ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) J) (hIo : IsOpen I)
    (hinj : InjOn J I) (hd : ∀ x ∈ I, deriv J x ≠ 0) (hq : Measurable q) :
    Measurable (branchDensity I J (invFunOn J I) (deriv J) q) := by
  classical
  let S := J '' I
  let g := S.piecewise (invFunOn J I) (fun _ => 0)
  have hS : IsOpen S := isOpen_image_of_deriv_ne_zero hJ hIo hd
  have hgi : ContinuousOn (invFunOn J I) S := by
    rintro y ⟨x,hx,rfl⟩
    exact (contDiffAt_invFunOn_of_deriv_ne_zero hJ hIo hinj hx
      ((hJ.differentiable (by simp) x).hasDerivAt) (hd x hx)).continuousAt.continuousWithinAt
  have hg : Measurable g := hgi.measurable_piecewise continuous_const.continuousOn hS.measurableSet
  have he : branchDensity I J (invFunOn J I) (deriv J) q =
      S.indicator (fun y => q (g y)/|deriv J (g y)|) := by
    funext y
    by_cases hy : y ∈ S
    · change S.indicator (fun y => q (invFunOn J I y)/|deriv J (invFunOn J I y)|) y = _
      simp [g,hy]
    · change S.indicator (fun y => q (invFunOn J I y)/|deriv J (invFunOn J I y)|) y = _
      simp only [indicator_of_notMem hy]
  rw [he]
  have hD : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (deriv J) := hJ.deriv'
  exact ((hq.comp hg).div ((hD.continuous.measurable.comp hg).abs)).indicator hS.measurableSet

lemma measurable_circleDensityLift {q : UnitAddCircle → ℝ} (hq : Measurable q) (o : ℝ) :
    Measurable (circleDensityLift o q) :=
  (hq.comp AddCircle.measurable_mk').indicator measurableSet_Ioc

lemma measurable_unfoldedModeDensity {I : Set ℝ} {J q : ℝ → ℝ}
    (hJ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) J) (hIo : IsOpen I)
    (hinj : InjOn J I) (hd : ∀ x ∈ I, deriv J x ≠ 0) (hq : Measurable q) (n j : ℝ) :
    Measurable (unfoldedModeDensity I J (invFunOn J I) (deriv J) q n j) := by
  have hm := measurable_branchDensity_smooth hJ hIo hinj hd (hq.const_mul n)
  unfold unfoldedModeDensity scaledBranchKernel
  exact (hm.comp ((measurable_const.mul measurable_id).sub_const j |>.div_const (j/n))).const_mul |j/n|⁻¹

end ThreeTorus

namespace ThreeTorus
open MeasureTheory Set Function Filter
open scoped Topology

lemma vectorMeasure_map_comp {X Y Z E : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSpace Z] [AddCommMonoid E] [TopologicalSpace E]
    (ν : VectorMeasure X E) {f : X → Y} {g : Y → Z} (hf : Measurable f) (hg : Measurable g) :
    (ν.map f).map g = ν.map (g ∘ f) := by
  ext s hs
  rw [VectorMeasure.map_apply _ hg hs,VectorMeasure.map_apply _ hf (hg hs),
    VectorMeasure.map_apply _ (hg.comp hf) hs]
  rfl

/-- The folded expression is the density of the actual mode spectral map
j(1+J/n)/n modulo one. Thus the circle limit is a spectral-density statement. -/
lemma foldedModeDensity_pushforward {q : UnitAddCircle → ℝ} {q₀ J₀ : ℝ → ℝ}
    {J : UnitAddCircle → ℝ} {o : ℝ} {I : Set ℝ}
    (hq : Integrable q AddCircle.haarAddCircle) (hqm : Measurable q₀)
    (hq₀ : ∀ x ∈ Ioc o (o+1), q (x : UnitAddCircle) = q₀ x)
    (hq₀s : support q₀ ⊆ Ioc o (o+1)) (hqs : support q₀ ⊆ I)
    (hj : Measurable J) (hJ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) J₀)
    (hJe : ∀ x ∈ I, J (x : UnitAddCircle) = J₀ x)
    (hIo : IsOpen I) (hinj : InjOn J₀ I) (hd : ∀ x ∈ I, deriv J₀ x ≠ 0)
    {n j : ℝ} (hn : 0 < n) (hjn : j ≠ 0) :
    (AddCircle.haarAddCircle.withDensityᵥ q).map
        (fun a => (((j+(j/n)*J a)/n : ℝ) : UnitAddCircle)) =
      AddCircle.haarAddCircle.withDensityᵥ
        (foldCircleDensity (unfoldedModeDensity I J₀ (invFunOn J₀ I) (deriv J₀) q₀ n j)) := by
  have hqi : Integrable q₀ := by
    rw [← circleDensityLift_eq hq₀ hq₀s]
    exact integrable_circleDensityLift hq o
  have hD : ∀ x ∈ I, HasDerivWithinAt J₀ (deriv J₀ x) I x :=
    fun x _ => (hJ.differentiable (by simp) x).hasDerivAt.hasDerivWithinAt
  have hp := unfoldedModeDensity_pushforward hq hq₀ hq₀s hqs hj hJ.continuous.measurable hJe
    hIo.measurableSet (isOpen_image_of_deriv_ne_zero hJ hIo hd).measurableSet hD hinj
    (fun _ hx => hinj.leftInvOn_invFunOn hx) hd hn hjn
  have h := congrArg (fun ν : VectorMeasure ℝ ℝ => ν.map (fun t : ℝ => (t:UnitAddCircle))) hp
  have hf : Measurable (fun a => (j+(j/n)*J a)/n) :=
    (measurable_const.add (hj.const_mul _)).div_const n
  have hg : Measurable (fun t : ℝ => (t:UnitAddCircle)) := AddCircle.measurable_mk'
  rw [vectorMeasure_map_comp _ hf hg] at h
  rw [foldCircleDensity_pushforward
    (measurable_unfoldedModeDensity hJ hIo hinj hd hqm n j)
    (integrable_unfoldedModeDensity hIo.measurableSet
      (isOpen_image_of_deriv_ne_zero hJ hIo hd).measurableSet hD hinj
      (fun _ hx => hinj.leftInvOn_invFunOn hx) hd hqi hn hjn)] at h
  exact h

end ThreeTorus

end

end

end

end

end

end OAI
end

section
-- module Solutions.OAIQ13_TT.ThreeTorus_Transmission
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Law averaging and weighted errors, folded packet transmission, and concrete signal-circle comparison. -/

noncomputable section
open MeasureTheory Filter Set Complex
open scoped Topology SchwartzMap FourierTransform Real
open scoped Topology
open MeasureTheory Set
open scoped ENNReal Topology
open Set Function Filter
open scoped Topology NNReal
open MeasureTheory Filter Set
open MeasureTheory Set Function
open scoped Topology ENNReal
open scoped Topology BigOperators
open MeasureTheory Set Filter
open scoped Topology FourierTransform
open MeasureTheory Set Filter Asymptotics
open MeasureTheory Set Filter Function

namespace ThreeTorus
open MeasureTheory Set Filter Function
open scoped Topology BigOperators FourierTransform

lemma lawJitter_injOn {ρ : ℝ → ℝ} {δ : ℝ} (c : LawCutoffs δ)
    (hρ : Continuous ρ) (hi : Integrable ρ) (hp : ∀ y, 0 < ρ y)
    (hm : ∫ y, ρ y = 1) (hδ : 0 < δ) : InjOn (lawJitter ρ c) (Ioo δ (1-δ)) := by
  intro a ha b hb he
  rw [lawJitter_eq_quantile c hδ ⟨ha.1.le,ha.2.le⟩,
    lawJitter_eq_quantile c hδ ⟨hb.1.le,hb.2.le⟩] at he
  have he' := congrArg (cumulative ρ) he
  rwa [cumulative_quantile hρ hi hp hm ⟨by linarith [ha.1],by linarith [ha.2]⟩,
    cumulative_quantile hρ hi hp hm ⟨by linarith [hb.1],by linarith [hb.2]⟩] at he'

end ThreeTorus

namespace ThreeTorus
open MeasureTheory Set Filter Function
open scoped Topology BigOperators FourierTransform

lemma continuous_quantileCircleJitter {δ : ℝ} {ρ : ℝ → ℝ} (c : LawCutoffs δ)
    (hρ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ρ) (hi : Integrable ρ)
    (hp : ∀ y, 0 < ρ y) (hm : ∫ y, ρ y = 1) : Continuous (quantileCircleJitter ρ c) := by
  apply Continuous.quotient_lift
  exact (lawJitter_smooth c hρ hi hp hm).continuous

end ThreeTorus

namespace ThreeTorus
open MeasureTheory Set Filter Function
open scoped Topology BigOperators FourierTransform

lemma continuous_signalCircleModel (P : ℕ) (γ B : ℝ) (d : ℝ → ℂ) (m : ℤ) :
    Continuous (signalCircleModel P γ B d m) := by
  unfold signalCircleModel
  fun_prop

lemma signalCircleModel_uniform_on_weight {α B b D : ℝ}
    (hα : 0 < α) (hαb : α < b) (hαD : α ≤ D) (hB : 0 < B) (hb : 0 < b)
    {L : ℕ} (hL : D/b < L) (γ : ℝ) {d : ℝ → ℂ}
    (hd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) d) (hcomp : HasCompactSupport d)
    (hr : ∀ v, d (-v) = starRingEnd ℂ (d v)) (h0 : d 0 = 0)
    (hs : Function.support d ⊆ Icc (-D) D) (m : ℤ) (hm : b ≤ |(m:ℝ)/B|)
    (hbound : ∀ h R, signalBaseline α R/(2*signalPrimeProduct L) ≤
        signalJoint α γ d (signalPrimeProduct L) h R ∧
      signalJoint α γ d (signalPrimeProduct L) h R ≤
        3*signalBaseline α R/(2*signalPrimeProduct L))
    {φ : ℝ → ℝ} {K C : Set ℝ} {A : ℝ → ℂ}
    (hA : support A ⊆ K) {V₀ : ℝ} (hV : ∀ x ∈ K, |φ x| ≤ V₀) :
    ∀ ε > 0, ∀ᶠ c : ℝ in atTop,
      ∀ s ∈ support (stationaryWeight C (fun x => (m:ℝ)*(c+φ x)) A), ∀ y,
      |foldCircleDensity (scaledDensity (signalJitter α γ d (signalPrimeProduct L) B c) s) y-
        signalCircleModel (signalPrimeProduct L) γ B d m y| ≤ ε := by
  classical
  intro ε hε
  filter_upwards [signalJitter_periodic_approximation hα hαb hαD hB hb hL γ hd hcomp hr
    h0 hs m hm hbound V₀ ε hε] with c hc
  intro s hs y
  obtain ⟨x,hx,rfl⟩ := stationaryWeight_support_subset hA hs
  induction y using Quotient.inductionOn with | h y =>
    have ht := hc (φ x) (hV x hx) y
    rw [← Complex.ofReal_tsum] at ht
    let a : ℂ := (if IsUnit (m : ZMod (signalPrimeProduct L)) then
      (γ:ℂ)*d ((m:ℝ)/B) else 0)*fourier (-1) (y:UnitAddCircle)
    have he : (1 : ℂ)+2*(a.re : ℂ) =
        (signalCircleModel (signalPrimeProduct L) γ B d m (y:UnitAddCircle) : ℂ) := by
      norm_num [signalCircleModel, a]
    change dist _ ((1 : ℂ)+2*(a.re : ℂ)) < ε at ht
    rw [he,Complex.isometry_ofReal.dist_eq,Real.dist_eq] at ht
    simpa only [foldCircleDensity_coe_all,periodizedReal] using ht.le

/-- All the analytic prerequisites of the actual signal law, including mass one,
are consequences of the explicit positive joint law. -/
lemma signalJitter_law_regular {α B c D γ : ℝ}
    (hα : 0 < α) (hB : 0 < B) (hc : 0 < c) (hαD : α ≤ D)
    {d : ℝ → ℂ} (hd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) d)
    (hcomp : HasCompactSupport d) (hr : ∀ v, d (-v) = starRingEnd ℂ (d v))
    (h0 : d 0 = 0) (hs : Function.support d ⊆ Icc (-D) D) (P : ℕ) [NeZero P]
    (hbound : ∀ h R, signalBaseline α R/(2*P) ≤ signalJoint α γ d P h R ∧
      signalJoint α γ d P h R ≤ 3*signalBaseline α R/(2*P)) :
    let ρ := signalJitter α γ d P B c
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ρ ∧ Integrable ρ ∧
      (∀ y, 0 < ρ y) ∧ (∫ y, ρ y = 1) ∧
      ∃ C > 0, (∀ y, |ρ y| ≤ C/(1+y^2)) ∧
        ∀ v, c*B*D < |v| → 𝓕 (fun y => (ρ y : ℂ)) v = 0 := by
  dsimp only
  obtain ⟨a,C,_ha,hC,hCb⟩ := signalJitter_quadratic_tails hα hB hc P hbound
  refine ⟨signalJitter_smooth hα γ hd hcomp P B c,
    signalJitter_integrable hα hB hc γ hd hcomp P,
    signalJitter_pos hα hB hc P hbound,?_,C,hC,?_,?_⟩
  · exact integral_signalJitter hα hB hc γ hd hcomp hr h0 P
  · intro y
    rw [abs_of_pos (signalJitter_pos hα hB hc P hbound y)]
    exact (hCb y).2
  · intro v hv
    have ht := signalJitter_fourierInv_support hα hB hc hαD γ hd hcomp hr hs P
      (v := -v) (by simpa only [abs_neg] using hv)
    simpa only [Real.fourierInv_eq_fourier_neg,neg_neg] using ht

end ThreeTorus

end

end OAI
end

section
-- module Solutions.OAIQ13_TT.ThreeTorus_RetainedPackets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Literal retained passage vectors, spectral identities, regularity, old marginals, and quantitative cutoff losses. -/

section

noncomputable section
open MeasureTheory Set Filter
open scoped Topology

noncomputable section
open MeasureTheory Set Function Filter
open scoped Topology

noncomputable section
open Set Function Filter
open scoped Topology
namespace ThreeTorus

/-- The second support separation in the manuscript uses cutoffs in frequency
alone, as opposed to the first passage's frequency/slow-coordinate cutoffs. -/
theorem finite_disjoint_frequency_cutoffs {ι : Type*} [Finite ι]
    (K U : ι → Set ℝ) (hK : ∀ i, IsCompact (K i)) (hU : ∀ i, IsOpen (U i))
    (hKU : ∀ i, K i ⊆ U i) (hdisj : Pairwise (Disjoint on K)) :
    ∃ χ : ι → ℝ → ℝ,
      (∀ i, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (χ i) ∧ HasCompactSupport (χ i) ∧
        tsupport (χ i) ⊆ U i ∧ (∀ s, 0 ≤ χ i s ∧ χ i s ≤ 1) ∧
        ∀ s ∈ K i, χ i =ᶠ[𝓝 s] 1) ∧
      Pairwise (fun i j => Disjoint (tsupport (χ i)) (tsupport (χ j))) := by
  have hd : Pairwise (fun i j => Disjoint (𝓝ˢ (K i)) (𝓝ˢ (K j))) :=
    fun i j hij => disjoint_nhdsSet_nhdsSet (hK i).isClosed (hK j).isClosed (hdisj hij)
  obtain ⟨O,hO,hOd⟩ := hd.exists_mem_filter_of_disjoint
  have hv i : K i ⊆ interior (O i) ∩ U i :=
    subset_inter (subset_interior_iff_mem_nhdsSet.mpr (hO i)) (hKU i)
  choose χ hχ using fun i => compact_smooth_cutoff (hK i)
    (isOpen_interior.inter (hU i)) (hv i)
  refine ⟨χ,fun i => ⟨(hχ i).1,(hχ i).2.1,(hχ i).2.2.1.trans inter_subset_right,
    (hχ i).2.2.2⟩,?_⟩
  intro i j hij
  exact (hOd hij).mono ((hχ i).2.2.1.trans (inter_subset_left.trans interior_subset))
    ((hχ j).2.2.1.trans (inter_subset_left.trans interior_subset))

lemma compactSupport_frequency_cylinder {χ : ℝ → ℝ} (hc : HasCompactSupport χ) :
    HasCompactSupport (fun p : ℝ × UnitAddCircle => χ p.1) := by
  apply (hc.prod isCompact_univ).of_isClosed_subset isClosed_closure
  apply closure_minimal _ ((isClosed_tsupport χ).prod isClosed_univ)
  intro p hp
  exact ⟨subset_tsupport χ hp,mem_univ _⟩

end ThreeTorus

noncomputable section
open MeasureTheory Set Filter Function
open scoped Topology
namespace ThreeTorus
namespace CompactParameter

/-- Compact-parameter differentiation, used by the exact passage near epsilon=0. -/
lemma hasFDerivAt_compact_integral
    {E : Type} {G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
    {F : E × ℝ → G} (hF : ContDiff ℝ 1 F) (a b : ℝ) (x : E) :
    HasFDerivAt (fun y => ∫ t in a..b, F (y,t))
      (∫ t in a..b, (fderiv ℝ F (x,t)).comp (ContinuousLinearMap.inl ℝ E ℝ)) x := by
  let D : E × ℝ → E →L[ℝ] G := fun p =>
    (fderiv ℝ F p).comp (ContinuousLinearMap.inl ℝ E ℝ)
  have hD : Continuous D := hF.continuous_fderiv (by norm_num) |>.clm_comp continuous_const
  obtain ⟨C,hC⟩ := ((isCompact_closedBall x 1).prod (isCompact_uIcc (a := a) (b := b))).exists_bound_of_continuousOn hD.continuousOn
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le''
    (F := fun y t => F (y,t)) (F' := fun y t => D (y,t))
    (bound := fun _ => C) (Metric.closedBall_mem_nhds x (by norm_num : (0:ℝ)<1)) ?_ ?_ ?_ ?_
    intervalIntegrable_const ?_
  · exact Eventually.of_forall (fun y => (hF.continuous.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable)
  · exact (hF.continuous.comp (continuous_const.prodMk continuous_id)).intervalIntegrable _ _
  · exact (hD.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_uIoc] with t ht
    intro y hy
    exact hC (y,t) ⟨hy,uIoc_subset_uIcc ht⟩
  · exact Eventually.of_forall (fun t y _ => by
      simpa [D,Function.comp_def] using ((hF.differentiable one_ne_zero ((ContinuousLinearMap.inl ℝ E ℝ) y+(0,t))).hasFDerivAt).comp y
        ((ContinuousLinearMap.inl ℝ E ℝ).hasFDerivAt.add_const (0,t)))

/-- Smooth parameter integration over a fixed compact interval. -/
lemma contDiff_compact_integral
    {E : Type} {G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
    (n : ℕ) {F : E × ℝ → G} (hF : ContDiff ℝ n F) (a b : ℝ) :
    ContDiff ℝ n (fun y => ∫ t in a..b, F (y,t)) := by
  induction n generalizing G with
  | zero =>
    apply contDiff_zero.mpr
    exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (show Continuous (Function.uncurry (fun y t => F (y,t))) from hF.continuous) a b
  | succ n ih =>
    let D : E × ℝ → E →L[ℝ] G := fun p =>
      (fderiv ℝ F p).comp (ContinuousLinearMap.inl ℝ E ℝ)
    have hD : ContDiff ℝ n D := (hF.fderiv_right (by simp)).clm_comp contDiff_const
    have hder (x : E) := hasFDerivAt_compact_integral (hF.of_le (by exact_mod_cast Nat.succ_pos n)) a b x
    rw [show ((n+1 : ℕ) : WithTop ℕ∞) = (n : WithTop ℕ∞)+1 by simp, contDiff_succ_iff_fderiv]
    refine ⟨fun x => (hder x).differentiableAt, ?_, ?_⟩
    · simp
    · have heq : fderiv ℝ (fun y => ∫ t in a..b, F (y,t)) =
          fun y => ∫ t in a..b, D (y,t) := by
        funext y
        exact (hder y).fderiv
      rw [heq]
      exact ih hD

lemma smooth_compact_integral
    {E : Type} {G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
    {F : E × ℝ → G} (hF : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F) (a b : ℝ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y => ∫ t in a..b, F (y,t)) := by
  rw [contDiff_infty]
  intro n
  exact contDiff_compact_integral n (hF.of_le (by exact_mod_cast (le_top : (n : ℕ∞) ≤ ⊤))) a b

end CompactParameter

/-- Smoothness of a Fourier coefficient in an arbitrary finite-dimensional
parameter, obtained from a compact interval integral of the literal lift. -/
lemma smooth_fourierCoeff_param {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {f : E → UnitAddCircle → ℂ}
    (hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : E × ℝ => f p.1 (p.2 : UnitAddCircle))) (j : ℤ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x => fourierCoeff (f x) j) := by
  have hchar : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : E × ℝ => (fourier (-j) (p.2 : UnitAddCircle) : ℂ)) := by
    simp only [fourier_coe_apply, Complex.ofReal_one, div_one]
    exact (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp contDiff_snd)).cexp
  have h := CompactParameter.smooth_compact_integral (hchar.mul hf) 0 1
  have he (x : E) : fourierCoeff (f x) j =
      ∫ t in (0:ℝ)..1, (fourier (-j) (t : UnitAddCircle) : ℂ) * f x t := by
    simpa only [one_div_one,one_smul,zero_add,smul_eq_mul] using
      fourierCoeff_eq_intervalIntegral (f x) j 0
  simpa only [he] using h

lemma smooth_fourier_lift (m : ℤ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x : ℝ => (fourier m (x : UnitAddCircle) : ℂ)) := by
  simp only [fourier_coe_apply,Complex.ofReal_one,div_one]
  exact (contDiff_const.mul Complex.ofRealCLM.contDiff).cexp

/-- Smoothness of the exact old-amplitude coefficients; no stationary-phase
approximation replaces these coefficients. -/
lemma smooth_exactPassageCoeff {m : ℤ} {H : UnitAddCircle → UnitAddCircle}
    {Hl : ℝ → ℝ} {A : UnitAddCircle × UnitAddCircle → ℂ}
    (hHl : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Hl)
    (hH : ∀ t : ℝ, H (t : UnitAddCircle) = (Hl t : UnitAddCircle))
    (hA : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : ℝ × ℝ => A (p.1,p.2))) (j : ℤ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun a : ℝ => exactPassageCoeff m H A j a) := by
  apply smooth_fourierCoeff_param
  change ContDiff ℝ _ (fun p : ℝ × ℝ => A (p.2,p.1)*fourier m (H p.2))
  simp_rw [hH]
  exact (hA.comp (contDiff_snd.prodMk contDiff_fst)).mul ((smooth_fourier_lift m).comp (hHl.comp contDiff_snd))

/-- The new amplitudes retained by the passage lie in the same smooth packet
class needed for its next use. -/
lemma smooth_retained_amplitude {m j : ℤ} {H : UnitAddCircle → UnitAddCircle}
    {Hl : ℝ → ℝ} {A : UnitAddCircle × UnitAddCircle → ℂ}
    {χ : ℝ × UnitAddCircle → ℝ} {ψ : UnitAddCircle → ℝ} (s : ℝ)
    (hHl : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Hl)
    (hH : ∀ t : ℝ, H (t : UnitAddCircle) = (Hl t : UnitAddCircle))
    (hA : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × ℝ => A (p.1,p.2)))
    (hχ : CylinderSmooth χ)
    (hψ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun a : ℝ => ψ a)) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × ℝ =>
      (χ (s,p.1):ℂ)*(ψ p.1:ℂ)*exactPassageCoeff m H A j p.1*fourier m (p.2:UnitAddCircle)) := by
  have hc : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : ℝ × ℝ => χ (s,(p.1:UnitAddCircle))) :=
    hχ.comp (contDiff_const.prodMk contDiff_fst)
  exact (((Complex.ofRealCLM.contDiff.comp hc).mul (Complex.ofRealCLM.contDiff.comp (hψ.comp contDiff_fst))).mul
    ((smooth_exactPassageCoeff hHl hH hA j).comp contDiff_fst)).mul
      ((smooth_fourier_lift m).comp contDiff_snd)

end ThreeTorus

noncomputable section
open MeasureTheory Set Function Filter
open scoped Topology ENNReal
namespace ThreeTorus

/-- A nonnegative integrable density identity proved with signed vector
measures is the identical ordinary measure identity. -/
lemma positive_density_map_of_vectorMeasure
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure X} {ν : Measure Y} {f : X → Y} {q : X → ℝ} {p : Y → ℝ}
    (hf : Measurable f) (hq : Integrable q μ) (hp : Integrable p ν)
    (hq0 : ∀ x, 0 ≤ q x) (hp0 : ∀ y, 0 ≤ p y)
    (he : (μ.withDensityᵥ q).map f = ν.withDensityᵥ p) :
    (μ.withDensity (fun x => ENNReal.ofReal (q x))).map f =
      ν.withDensity (fun y => ENNReal.ofReal (p y)) := by
  ext s hs
  rw [Measure.map_apply hf hs,withDensity_apply _ (hf hs),withDensity_apply _ hs]
  rw [← ofReal_integral_eq_lintegral_ofReal hq.integrableOn (Eventually.of_forall hq0),
    ← ofReal_integral_eq_lintegral_ofReal hp.integrableOn (Eventually.of_forall hp0)]
  congr 1
  have h := congrArg (fun v : VectorMeasure Y ℝ => v s) he
  simpa only [VectorMeasure.map_apply _ hf hs,withDensityᵥ_apply hq (hf hs),
    withDensityᵥ_apply hp hs] using h

lemma branchDensity_nonneg {I : Set ℝ} {J g D q : ℝ → ℝ}
    (hq : ∀ t, 0 ≤ q t) (y : ℝ) : 0 ≤ branchDensity I J g D q y := by
  classical
  simp only [branchDensity,Set.indicator_apply]
  split_ifs
  · exact div_nonneg (hq _) (abs_nonneg _)
  · rfl

lemma unfoldedModeDensity_nonneg {I : Set ℝ} {J g D q : ℝ → ℝ}
    (hq : ∀ t, 0 ≤ q t) {n : ℝ} (hn : 0 ≤ n) (j t : ℝ) :
    0 ≤ unfoldedModeDensity I J g D q n j t := by
  unfold unfoldedModeDensity scaledBranchKernel
  exact mul_nonneg (inv_nonneg.mpr (abs_nonneg _))
    (branchDensity_nonneg (fun a => mul_nonneg hn (hq a)) _)

lemma foldCircleDensity_nonneg {q : ℝ → ℝ} (hq : ∀ t, 0 ≤ q t) (z : UnitAddCircle) :
    0 ≤ foldCircleDensity q z := by
  unfold foldCircleDensity periodizedReal
  exact tsum_nonneg (fun k => hq _)

lemma retainedAmplitude_norm_sq (ψ : UnitAddCircle → ℝ) (χ : ℝ → UnitAddCircle → ℝ)
    (m : ℤ) (H : ℕ → UnitAddCircle → UnitAddCircle)
    (A : UnitAddCircle × UnitAddCircle → ℂ) (n : ℕ) (j : ℤ)
    (p : UnitAddCircle × UnitAddCircle) :
    ‖retainedAmplitude ψ χ m H A n j p‖^2 =
      retainedCircleWeight ψ χ (fun n j => exactPassageCoeff m (H n) A j) n j p.1 := by
  simp only [retainedAmplitude,norm_mul,show ‖fourier m p.2‖ = 1 from Circle.norm_coe _,
    mul_one,mul_pow,Complex.norm_real,Real.norm_eq_abs,sq_abs,retainedCircleWeight]

lemma retainedAmplitude_modulus (ψ : UnitAddCircle → ℝ) (χ : ℝ → UnitAddCircle → ℝ)
    (m : ℤ) (H : ℕ → UnitAddCircle → UnitAddCircle)
    (A : UnitAddCircle × UnitAddCircle → ℂ) (n : ℕ) (j : ℤ) (a b : UnitAddCircle) :
    ‖retainedAmplitude ψ χ m H A n j (a,b)‖ =
      ‖retainedAmplitude ψ χ m H A n j (a,0)‖ := by
  simp only [retainedAmplitude,norm_mul,show ‖fourier m b‖ = 1 from Circle.norm_coe _,
    show ‖fourier m (0:UnitAddCircle)‖ = 1 from Circle.norm_coe _]

-- The same elementary identity used in the supplied whitening proof.
lemma map_withDensity_comp {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) {ζ : X → Y} {w : Y → ℝ≥0∞}
    (hζ : Measurable ζ) (hw : Measurable w) :
    (μ.withDensity (w ∘ ζ)).map ζ = (μ.map ζ).withDensity w := by
  ext s hs
  rw [Measure.map_apply hζ hs, withDensity_apply _ (hζ hs), withDensity_apply _ hs]
  rw [← lintegral_indicator (hζ hs), ← lintegral_indicator hs,
    lintegral_map (hw.indicator hs) hζ]
  apply lintegral_congr
  intro x
  rfl

/-- If a coefficient's modulus is independent of its spare coordinate, its
literal packet spectral measure is the single-coordinate weighted image. -/
lemma packetSpectralMeasure_of_modulus
    {φ : UnitAddCircle → UnitAddCircle} (hφ : Measurable φ) {j : ℤ}
    {B : UnitAddCircle × UnitAddCircle → ℂ} {q : UnitAddCircle → ℝ}
    (hq : Measurable q) (hB : ∀ p, ‖B p‖^2 = q p.1) :
    packetSpectralMeasure φ j B =
      (AddCircle.haarAddCircle.withDensity (fun a => ENNReal.ofReal (q a))).map
        (fun a => j • φ a) := by
  unfold packetSpectralMeasure
  have he : (fun p : UnitAddCircle × UnitAddCircle => ENNReal.ofReal (‖B p‖^2)) =
      (fun a => ENNReal.ofReal (q a)) ∘ Prod.fst := funext (fun p => congrArg _ (hB p))
  rw [he]
  change Measure.map ((fun a => j • φ a) ∘ Prod.fst) _ = _
  rw [← Measure.map_map (show Measurable (fun a => j • φ a) from hφ.const_smul j) measurable_fst,
    map_withDensity_comp slowVolume measurable_fst hq.ennreal_ofReal]
  simp only [slowVolume,Measure.map_fst_prod,measure_univ,one_smul]

lemma retainedCircleWeight_nonneg (ψ : UnitAddCircle → ℝ) (χ : ℝ → UnitAddCircle → ℝ)
    (c : ℕ → ℤ → UnitAddCircle → ℂ) (n : ℕ) (j : ℤ) (a : UnitAddCircle) :
    0 ≤ retainedCircleWeight ψ χ c n j a := by unfold retainedCircleWeight; positivity

lemma circleDensityLift_nonneg {q : UnitAddCircle → ℝ} (hq : ∀ a, 0 ≤ q a)
    (o x : ℝ) : 0 ≤ circleDensityLift o q x := by
  classical
  simp only [circleDensityLift,Set.indicator_apply]
  split_ifs
  · exact hq _
  · rfl

/-- The folded branch is the ordinary (positive) spectral density, not just
an identity of signed integrals. -/
lemma positive_foldedModeDensity_pushforward {q : UnitAddCircle → ℝ} {q₀ J₀ : ℝ → ℝ}
    {J : UnitAddCircle → ℝ} {o : ℝ} {I : Set ℝ}
    (hq : Integrable q AddCircle.haarAddCircle) (hqm : Measurable q₀)
    (hq0 : ∀ a, 0 ≤ q a) (hq00 : ∀ x, 0 ≤ q₀ x)
    (hq₀ : ∀ x ∈ Ioc o (o+1), q (x : UnitAddCircle) = q₀ x)
    (hq₀s : support q₀ ⊆ Ioc o (o+1)) (hqs : support q₀ ⊆ I)
    (hj : Measurable J) (hJ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) J₀)
    (hJe : ∀ x ∈ I, J (x : UnitAddCircle) = J₀ x)
    (hIo : IsOpen I) (hinj : InjOn J₀ I) (hd : ∀ x ∈ I, deriv J₀ x ≠ 0)
    {n j : ℝ} (hn : 0 < n) (hjn : j ≠ 0) :
    (AddCircle.haarAddCircle.withDensity (fun a => ENNReal.ofReal (q a))).map
        (fun a => (((j+(j/n)*J a)/n : ℝ) : UnitAddCircle)) =
      AddCircle.haarAddCircle.withDensity
        (fun z => ENNReal.ofReal
          (foldCircleDensity (unfoldedModeDensity I J₀ (invFunOn J₀ I) (deriv J₀) q₀ n j) z)) := by
  have hqi : Integrable q₀ := by
    rw [← circleDensityLift_eq hq₀ hq₀s]
    exact integrable_circleDensityLift hq o
  have hD : ∀ x ∈ I, HasDerivWithinAt J₀ (deriv J₀ x) I x :=
    fun x _ => (hJ.differentiable (by simp) x).hasDerivAt.hasDerivWithinAt
  have hmi := measurable_unfoldedModeDensity hJ hIo hinj hd hqm n j
  have hii := integrable_unfoldedModeDensity hIo.measurableSet
    (isOpen_image_of_deriv_ne_zero hJ hIo hd).measurableSet hD hinj
    (fun _ hx => hinj.leftInvOn_invFunOn hx) hd hqi hn hjn
  exact positive_density_map_of_vectorMeasure
    (AddCircle.measurable_mk'.comp ((measurable_const.add (hj.const_mul _)).div_const n))
    hq (integrable_foldCircleDensity hmi hii) hq0
    (foldCircleDensity_nonneg (unfoldedModeDensity_nonneg hq00 hn.le j))
    (foldedModeDensity_pushforward hq hqm hq₀ hq₀s hqs hj hJ hJe hIo hinj hd hn hjn)

lemma passage_speed_mode (J : UnitAddCircle → ℝ) (n : ℝ) (j : ℤ) (a : UnitAddCircle) :
    j • (((1+J a/n)/n : ℝ) : UnitAddCircle) =
      ((((j:ℝ)+((j:ℝ)/n)*J a)/n : ℝ) : UnitAddCircle) := by
  rw [← AddCircle.coe_zsmul]
  congr 1
  simp only [zsmul_eq_mul]
  ring

/-- Any coefficient with the actual retained modulus has the displayed
nonnegative folded density under the actual new twist. -/
lemma packetSpectralMeasure_new_speed {q : UnitAddCircle → ℝ} {q₀ J₀ : ℝ → ℝ}
    {J : UnitAddCircle → ℝ} {o : ℝ} {I : Set ℝ}
    {B : UnitAddCircle × UnitAddCircle → ℂ}
    (hq : Integrable q AddCircle.haarAddCircle) (hqmeas : Measurable q) (hqm : Measurable q₀)
    (hB : ∀ p, ‖B p‖^2 = q p.1) (hq00 : ∀ x, 0 ≤ q₀ x)
    (hq₀ : ∀ x ∈ Ioc o (o+1), q (x : UnitAddCircle) = q₀ x)
    (hq₀s : support q₀ ⊆ Ioc o (o+1)) (hqs : support q₀ ⊆ I)
    (hj : Measurable J) (hJ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) J₀)
    (hJe : ∀ x ∈ I, J (x : UnitAddCircle) = J₀ x)
    (hIo : IsOpen I) (hinj : InjOn J₀ I) (hd : ∀ x ∈ I, deriv J₀ x ≠ 0)
    {n : ℝ} {j : ℤ} (hn : 0 < n) (hjn : j ≠ 0) :
    packetSpectralMeasure (fun a => (((1+J a/n)/n:ℝ):UnitAddCircle)) j B =
      AddCircle.haarAddCircle.withDensity
        (fun z => ENNReal.ofReal
          (foldCircleDensity (unfoldedModeDensity I J₀ (invFunOn J₀ I) (deriv J₀) q₀ n j) z)) := by
  have hσ : Measurable (fun a => (((1+J a/n)/n:ℝ):UnitAddCircle)) :=
    AddCircle.measurable_mk'.comp ((measurable_const.add (hj.div_const n)).div_const n)
  rw [packetSpectralMeasure_of_modulus hσ hqmeas hB]
  simp_rw [passage_speed_mode]
  exact positive_foldedModeDensity_pushforward hq hqm
    (fun a => (hB (a,0)) ▸ sq_nonneg _) hq00 hq₀ hq₀s hqs hj hJ hJe hIo hinj hd hn
    (by exact_mod_cast hjn)

/-- Density identity for the literal retained coefficient used by the passage.
The only support hypothesis is that the cutoff lies on the chosen good branch. -/
lemma retainedAmplitude_spectralDensity
    {ψ : UnitAddCircle → ℝ} {χ : ℝ → UnitAddCircle → ℝ}
    {m : ℤ} {H : ℕ → UnitAddCircle → UnitAddCircle} {A : UnitAddCircle × UnitAddCircle → ℂ}
    {J : UnitAddCircle → ℝ} {J₀ : ℝ → ℝ} {o : ℝ} {I : Set ℝ}
    (hψ : Continuous ψ) (hχ : Continuous χ.uncurry)
    (hH : ∀ n, Continuous (H n)) (hA : Continuous A)
    (hψs : ∀ x ∈ Ioc o (o+1), ψ (x:UnitAddCircle) ≠ 0 → x ∈ I)
    (hj : Measurable J) (hJ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) J₀)
    (hJe : ∀ x ∈ I, J (x:UnitAddCircle) = J₀ x)
    (hIo : IsOpen I) (hinj : InjOn J₀ I) (hd : ∀ x ∈ I, deriv J₀ x ≠ 0)
    {n : ℕ} {j : ℤ} (hn : 0 < n) (hjn : j ≠ 0) :
    packetSpectralMeasure (fun a => (((1+J a/n)/n:ℝ):UnitAddCircle)) j
      (retainedAmplitude ψ χ m H A n j) =
      AddCircle.haarAddCircle.withDensity (fun z => ENNReal.ofReal
        (foldCircleDensity (unfoldedModeDensity I J₀ (invFunOn J₀ I) (deriv J₀)
          (circleDensityLift o (retainedCircleWeight ψ χ
            (fun n j => exactPassageCoeff m (H n) A j) n j)) n j) z)) := by
  let C n j := exactPassageCoeff m (H n) A j
  let q := retainedCircleWeight ψ χ C n j
  have hC n j : Continuous (C n j) := continuous_exactPassageCoeff (hH n) hA j
  have hq : Continuous q :=
    ((hψ.pow 2).mul ((hχ.comp (continuous_const.prodMk continuous_id)).pow 2)).mul
      ((hC n j).norm.pow 2)
  have hqs : support (circleDensityLift o q) ⊆ Ioc o (o+1) ∩ I := by
    intro x hx
    have hxI : x ∈ Ioc o (o+1) := by
      by_contra hh
      exact hx (by simp [circleDensityLift,hh])
    refine ⟨hxI,hψs x hxI ?_⟩
    intro hz
    exact hx (by simp [circleDensityLift,hxI,q,retainedCircleWeight,hz])
  exact packetSpectralMeasure_new_speed
    (retainedCircleWeight_integrable hψ hχ hC n j) hq.measurable
    (measurable_circleDensityLift hq.measurable o)
    (retainedAmplitude_norm_sq ψ χ m H A n j)
    (circleDensityLift_nonneg (retainedCircleWeight_nonneg ψ χ C n j) o)
    (fun _ hx => by simp only [circleDensityLift,indicator_of_mem hx]; rfl)
    (hqs.trans inter_subset_left) (hqs.trans inter_subset_right)
    hj hJ hJe hIo hinj hd (by exact_mod_cast hn) hjn

end ThreeTorus
end
end
end
end
end
end

section

/-! Exact spectral identity for the literal retained packet vector. This closes
 the interface between the previously proved coefficient-density estimates and
 the actual Koopman correlations, without an abstract density hypothesis. -/
noncomputable section
open MeasureTheory Set Function Filter
open scoped Topology BigOperators
namespace ThreeTorus

lemma foldCircleDensity_add_ae {q r : ℝ → ℝ} (hq : Measurable q) (hr : Measurable r)
    (hqi : Integrable q) (hri : Integrable r) :
    foldCircleDensity (fun x => q x+r x) =ᵐ[AddCircle.haarAddCircle]
      fun z => foldCircleDensity q z+foldCircleDensity r z := by
  apply (integrable_foldCircleDensity (hq.add hr) (hqi.add hri)).ae_eq_of_withDensityᵥ_eq
    ((integrable_foldCircleDensity hq hqi).add (integrable_foldCircleDensity hr hri))
  rw [← foldCircleDensity_pushforward (hq.add hr) (hqi.add hri),
    withDensityᵥ_add hqi hri,
    withDensityᵥ_add (integrable_foldCircleDensity hq hqi) (integrable_foldCircleDensity hr hri)]
  have he := map_add (VectorMeasure.mapGm (fun x : ℝ => (x:UnitAddCircle)))
    (volume.withDensityᵥ q) (volume.withDensityᵥ r)
  change (volume.withDensityᵥ q+volume.withDensityᵥ r).map _ =
    (volume.withDensityᵥ q).map _+(volume.withDensityᵥ r).map _ at he
  rw [he,foldCircleDensity_pushforward hq hqi,foldCircleDensity_pushforward hr hri]

lemma foldCircleDensity_finsetSum_ae {ι : Type*} (S : Finset ι) (q : ι → ℝ → ℝ)
    (hq : ∀ i ∈ S, Measurable (q i)) (hqi : ∀ i ∈ S, Integrable (q i)) :
    foldCircleDensity (fun x => ∑ i ∈ S, q i x) =ᵐ[AddCircle.haarAddCircle]
      fun z => ∑ i ∈ S, foldCircleDensity (q i) z := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    filter_upwards [] with z
    simp [foldCircleDensity,periodizedReal,AddCircle.liftIoc,Set.domRestrict]
  | @insert i S hi ih =>
    simp only [Finset.sum_insert hi]
    have hh := foldCircleDensity_add_ae (hq i (Finset.mem_insert_self i S))
      (Finset.measurable_sum S (fun j hj => hq j (Finset.mem_insert_of_mem hj)))
      (hqi i (Finset.mem_insert_self i S))
      (integrable_finsetSum S (fun j hj => hqi j (Finset.mem_insert_of_mem hj)))
    have ht := ih (fun j hj => hq j (Finset.mem_insert_of_mem hj))
      (fun j hj => hqi j (Finset.mem_insert_of_mem hj))
    filter_upwards [hh,ht] with z hz ht
    rw [hz,ht]

end ThreeTorus
end
end

section

/-! Smoothness at the edge of the good arc is essential: the actual retained
spectral densities must be valid smooth inputs to the next stage. -/
noncomputable section
open MeasureTheory Set Function Filter
open scoped Topology BigOperators
namespace ThreeTorus

lemma support_branchDensity_subset {J q : ℝ → ℝ} {I : Set ℝ} :
    support (branchDensity I J (invFunOn J I) (deriv J) q) ⊆ J '' tsupport q := by
  intro y hy
  have hyI : y ∈ J '' I := by
    by_contra hh
    exact hy (by simp [branchDensity,hh])
  have hx := invFunOn_pos hyI
  refine ⟨invFunOn J I y,subset_tsupport q ?_,hx.2⟩
  intro hq
  exact hy (by simp [branchDensity,hyI,hq])

lemma branchDensity_compact {J q : ℝ → ℝ} {I : Set ℝ}
    (hJ : Continuous J) (hq : HasCompactSupport q) :
    HasCompactSupport (branchDensity I J (invFunOn J I) (deriv J) q) := by
  apply HasCompactSupport.intro (hq.image hJ)
  intro y hy
  exact notMem_support.mp (fun hh => hy (support_branchDensity_subset hh))

lemma branchDensity_smooth {J q : ℝ → ℝ} {I : Set ℝ}
    (hJ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) J) (hIo : IsOpen I)
    (hinj : InjOn J I) (hd : ∀ x ∈ I, deriv J x ≠ 0)
    (hq : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) q) (hc : HasCompactSupport q)
    (hs : tsupport q ⊆ I) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (branchDensity I J (invFunOn J I) (deriv J) q) := by
  classical
  let g := invFunOn J I
  have hM : IsCompact (J '' tsupport q) := hc.image hJ.continuous
  have hD : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (deriv J) := hJ.deriv'
  rw [contDiff_iff_contDiffAt]
  intro y
  by_cases hy : y ∈ J '' tsupport q
  · obtain ⟨x,hx,rfl⟩ := hy
    have hxI := hs hx
    have hyI : J x ∈ J '' I := mem_image_of_mem J hxI
    have hg := contDiffAt_invFunOn_of_deriv_ne_zero hJ hIo hinj hxI
      ((hJ.differentiable (by simp) x).hasDerivAt) (hd x hxI)
    have hge : g (J x) = x := hinj (invFunOn_pos hyI).1 hxI (invFunOn_pos hyI).2
    have hden : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun y => |deriv J (g y)|) (J x) :=
      (contDiffAt_abs (by simpa only [hge] using hd x hxI)).comp (J x)
        (hD.contDiffAt.comp (J x) hg)
    have hquot := (hq.contDiffAt.comp (J x) hg).div hden
      (by simpa only [hge] using abs_ne_zero.mpr (hd x hxI))
    apply hquot.congr_of_eventuallyEq
    filter_upwards [(isOpen_image_of_deriv_ne_zero hJ hIo hd).mem_nhds hyI] with z hz
    simp only [branchDensity,indicator_of_mem hz,g]
    rfl
  · apply (contDiffAt_const (c := (0:ℝ))).congr_of_eventuallyEq
    filter_upwards [hM.isClosed.isOpen_compl.mem_nhds hy] with z hz
    exact notMem_support.mp (fun hh => hz (support_branchDensity_subset hh))

lemma unfoldedModeDensity_smooth {J q : ℝ → ℝ} {I : Set ℝ}
    (hJ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) J) (hIo : IsOpen I)
    (hinj : InjOn J I) (hd : ∀ x ∈ I, deriv J x ≠ 0)
    (hq : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) q) (hc : HasCompactSupport q)
    (hs : tsupport q ⊆ I) (n j : ℝ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (unfoldedModeDensity I J (invFunOn J I) (deriv J) q n j) := by
  have hmul : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x => n*q x) := contDiff_const.mul hq
  have hcs : HasCompactSupport (fun x => n*q x) := hc.mul_left
  have hs' : tsupport (fun x => n*q x) ⊆ I := tsupport_mul_subset_right.trans hs
  have hh := branchDensity_smooth hJ hIo hinj hd hmul hcs hs' 
  unfold unfoldedModeDensity scaledBranchKernel
  exact contDiff_const.mul (hh.comp ((contDiff_const.mul contDiff_id).sub contDiff_const |>.div_const _))

lemma unfoldedModeDensity_compact {J q : ℝ → ℝ} {I : Set ℝ}
    (hJ : Continuous J) (hc : HasCompactSupport q) {n j : ℝ} (hn : n ≠ 0) (hj : j ≠ 0) :
    HasCompactSupport (unfoldedModeDensity I J (invFunOn J I) (deriv J) q n j) := by
  have hh := branchDensity_compact (I := I) hJ (hc.mul_left (f := fun _ => n))
  let e : ℝ ≃ₜ ℝ := (Homeomorph.mulLeft₀ n hn).trans (Homeomorph.addRight (-j))
  let e' : ℝ ≃ₜ ℝ := e.trans (Homeomorph.mulRight₀ (n/j) (div_ne_zero hn hj))
  have he (t : ℝ) : e' t = (n*t-j)/(j/n) := by
    dsimp [e',e]
    field_simp
    ring
  have hc' := hh.comp_homeomorph e'
  have heq : unfoldedModeDensity I J (invFunOn J I) (deriv J) q n j =
      fun t => |j/n|⁻¹ * branchDensity I J (invFunOn J I) (deriv J) (fun x => n*q x) (e' t) := by
    funext t
    rw [he]
    rfl
  rw [heq]
  exact hc'.mul_left

lemma periodizedReal_eq_periodize {q : ℝ → ℝ} (hc : HasCompactSupport q) :
    periodizedReal q = periodize q := by
  funext x
  obtain ⟨R,hR⟩ := hc.isBounded.exists_norm_le
  obtain ⟨N,hN⟩ := exists_nat_gt (R+|x|+1)
  have hs : support (fun k : ℤ => q (x+k)) ⊆ (Finset.Icc (-(N:ℤ)) N : Set ℤ) := by
    intro k hk
    have hr := hR (x+k) (subset_tsupport q hk)
    have hh : |(k:ℝ)| < N := by
      have ha := abs_sub_le (x+(k:ℝ)) 0 x
      simp only [sub_zero,zero_sub,abs_neg,add_sub_cancel_left,Real.norm_eq_abs] at hr ha
      linarith
    have hab := abs_lt.mp hh
    simp only [Finset.mem_coe,Finset.mem_Icc]
    constructor
    · exact_mod_cast (by linarith : -(N:ℝ) ≤ (k:ℝ))
    · exact_mod_cast (by linarith : (k:ℝ) ≤ (N:ℝ))
  exact tsum_eq_finsum ((Finset.finite_toSet _).subset hs)

lemma foldCircleDensity_smooth_lift {q : ℝ → ℝ}
    (hq : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) q) (hc : HasCompactSupport q) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x : ℝ => foldCircleDensity q (x:UnitAddCircle)) := by
  have he : (fun x : ℝ => foldCircleDensity q (x:UnitAddCircle)) = periodize q := by
    funext x
    rw [foldCircleDensity_coe_all]
    exact congrFun (periodizedReal_eq_periodize hc) x
  rw [he]
  exact contDiff_periodize hq hc

lemma realRetainedWeight_support (ψ₀ : ℝ → ℝ) (χ : ℝ → UnitAddCircle → ℝ)
    (m : ℤ) (H : ℕ → UnitAddCircle → UnitAddCircle)
    (A : UnitAddCircle × UnitAddCircle → ℂ) (n : ℕ) (j : ℤ) :
    tsupport (realRetainedWeight ψ₀ χ m H A n j) ⊆ tsupport ψ₀ := by
  apply closure_mono
  intro x hx hz
  exact hx (by simp [realRetainedWeight,hz])

lemma realRetainedWeight_compact {ψ₀ : ℝ → ℝ} (hc : HasCompactSupport ψ₀)
    (χ : ℝ → UnitAddCircle → ℝ) (m : ℤ) (H : ℕ → UnitAddCircle → UnitAddCircle)
    (A : UnitAddCircle × UnitAddCircle → ℂ) (n : ℕ) (j : ℤ) :
    HasCompactSupport (realRetainedWeight ψ₀ χ m H A n j) :=
  hc.of_isClosed_subset isClosed_closure (realRetainedWeight_support ψ₀ χ m H A n j)

lemma realRetainedWeight_smooth {ψ₀ : ℝ → ℝ} {χ : ℝ → UnitAddCircle → ℝ}
    {m : ℤ} {H : ℕ → UnitAddCircle → UnitAddCircle} {Hl : ℕ → ℝ → ℝ}
    {A : UnitAddCircle × UnitAddCircle → ℂ}
    (hψ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ₀)
    (hχ : CylinderSmooth χ.uncurry)
    (hHl : ∀ n, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Hl n))
    (hH : ∀ n (t : ℝ), H n (t:UnitAddCircle) = (Hl n t:UnitAddCircle))
    (hA : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × ℝ => A (p.1,p.2)))
    (n : ℕ) (j : ℤ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (realRetainedWeight ψ₀ χ m H A n j) := by
  have hχ' : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x : ℝ => χ ((j:ℝ)/n) x) := hχ.comp (contDiff_const.prodMk contDiff_id)
  exact ((hψ.pow 2).mul (hχ'.pow 2)).mul
    ((smooth_exactPassageCoeff (hHl n) (hH n) hA j).norm_sq (𝕜 := ℂ))

lemma retainedWeight_lift_eq {ψ : UnitAddCircle → ℝ} {ψ₀ : ℝ → ℝ}
    (χ : ℝ → UnitAddCircle → ℝ) (m : ℤ) (H : ℕ → UnitAddCircle → UnitAddCircle)
    (A : UnitAddCircle × UnitAddCircle → ℂ) (n : ℕ) (j : ℤ)
    (he : ∀ x ∈ Ioc (0:ℝ) (0+1), ψ (x:UnitAddCircle) = ψ₀ x)
    (hs : tsupport ψ₀ ⊆ Ioc (0:ℝ) (0+1)) :
    circleDensityLift 0 (retainedCircleWeight ψ χ
      (fun n j => exactPassageCoeff m (H n) A j) n j) =
      realRetainedWeight ψ₀ χ m H A n j := by
  apply circleDensityLift_eq
  · intro x hx
    simp only [retainedCircleWeight,realRetainedWeight,he x hx]
  · exact (subset_tsupport _).trans ((realRetainedWeight_support ψ₀ χ m H A n j).trans hs)

/-- Actual retained densities are smooth at all branch edges, including their
zero set. This supplies the next passage's regularity; it is not an assumption
that the density is already smooth. -/
theorem exactRetainedPacketDensity_smooth_lift
    {I : Set ℝ} {J : ℝ → ℝ} {ψ : UnitAddCircle → ℝ} {ψ₀ : ℝ → ℝ}
    {χ : ℝ → UnitAddCircle → ℝ} {m : ℤ}
    {H : ℕ → UnitAddCircle → UnitAddCircle} {Hl : ℕ → ℝ → ℝ}
    {A : UnitAddCircle × UnitAddCircle → ℂ} {S : Finset ℤ} {n : ℕ}
    (hJ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) J) (hIo : IsOpen I)
    (hinj : InjOn J I) (hd : ∀ x ∈ I, deriv J x ≠ 0)
    (hψ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ₀) (hc : HasCompactSupport ψ₀)
    (he : ∀ x ∈ Ioc (0:ℝ) (0+1), ψ (x:UnitAddCircle) = ψ₀ x)
    (hs : tsupport ψ₀ ⊆ Ioc (0:ℝ) (0+1) ∩ I)
    (hχ : CylinderSmooth χ.uncurry)
    (hHl : ∀ n, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Hl n))
    (hH : ∀ n (t : ℝ), H n (t:UnitAddCircle) = (Hl n t:UnitAddCircle))
    (hA : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × ℝ => A (p.1,p.2)))
    (hn : 0 < n) (hS : ∀ j ∈ S, j ≠ 0) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x : ℝ => exactRetainedPacketDensity I J ψ χ m H A S n x) := by
  unfold exactRetainedPacketDensity
  simp_rw [retainedWeight_lift_eq χ m H A n _ he (hs.trans inter_subset_left)]
  apply foldCircleDensity_smooth_lift
  · apply ContDiff.sum
    intro j hj
    exact unfoldedModeDensity_smooth hJ hIo hinj hd
      (realRetainedWeight_smooth hψ hχ hHl hH hA n j)
      (realRetainedWeight_compact hc χ m H A n j)
      ((realRetainedWeight_support ψ₀ χ m H A n j).trans (hs.trans inter_subset_right)) n j
  · have hh (j : ℤ) (hj : j ∈ S) : HasCompactSupport
        (unfoldedModeDensity I J (invFunOn J I) (deriv J)
          (realRetainedWeight ψ₀ χ m H A n j) n j) :=
      unfoldedModeDensity_compact hJ.continuous
        (realRetainedWeight_compact hc χ m H A n j)
        (by exact_mod_cast hn.ne') (by exact_mod_cast hS j hj)
    convert HasCompactSupport.finset_sum hh using 1
    all_goals try with_reducible_and_instances rfl
    first | rfl | (funext time; simp only [Finset.sum_apply])

end ThreeTorus
end
end

section

/-! Identification of the reference stationary marginal with the actual old
packet spectrum. In particular integer carrier speeds do not change it. -/
noncomputable section
open MeasureTheory Set Function Filter
open scoped Topology BigOperators
namespace ThreeTorus

lemma positive_circle_branch_fold
    {q : UnitAddCircle → ℝ} {q₀ J₀ : ℝ → ℝ}
    {J : UnitAddCircle → ℝ} {o : ℝ} {I : Set ℝ}
    (hq : Integrable q AddCircle.haarAddCircle) (hqm : Measurable q₀)
    (hq0 : ∀ a, 0 ≤ q a) (hq00 : ∀ x, 0 ≤ q₀ x)
    (hq₀ : ∀ x ∈ Ioc o (o+1), q (x:UnitAddCircle) = q₀ x)
    (hq₀s : support q₀ ⊆ Ioc o (o+1)) (hqs : support q₀ ⊆ I)
    (hj : Measurable J) (hJ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) J₀)
    (hJe : ∀ x ∈ I, J (x:UnitAddCircle) = J₀ x)
    (hIo : IsOpen I) (hinj : InjOn J₀ I) (hd : ∀ x ∈ I, deriv J₀ x ≠ 0) :
    (AddCircle.haarAddCircle.withDensity (fun a => ENNReal.ofReal (q a))).map
        (fun a => (J a:UnitAddCircle)) =
      AddCircle.haarAddCircle.withDensity (fun z => ENNReal.ofReal
        (foldCircleDensity (branchDensity I J₀ (invFunOn J₀ I) (deriv J₀) q₀) z)) := by
  let w := branchDensity I J₀ (invFunOn J₀ I) (deriv J₀) q₀
  have hqi : Integrable q₀ := by
    rw [← circleDensityLift_eq hq₀ hq₀s]
    exact integrable_circleDensityLift hq o
  have hD : ∀ x ∈ I, HasDerivWithinAt J₀ (deriv J₀ x) I x :=
    fun x _ => (hJ.differentiable (by simp) x).hasDerivAt.hasDerivWithinAt
  have hIm := (isOpen_image_of_deriv_ne_zero hJ hIo hd).measurableSet
  have hwi : Integrable w := integrable_branchDensity hIo.measurableSet hIm hD hinj
    (fun _ hx => hinj.leftInvOn_invFunOn hx) hd hqi.integrableOn
  have hwm : Measurable w := measurable_branchDensity_smooth hJ hIo hinj hd hqm
  have hmap := circle_branch_pushforward hq hq₀ hq₀s hqs hj hJ.continuous.measurable hJe
    hIo.measurableSet hIm hD hinj (fun _ hx => hinj.leftInvOn_invFunOn hx) hd
  apply positive_density_map_of_vectorMeasure (AddCircle.measurable_mk'.comp hj) hq
    (integrable_foldCircleDensity hwm hwi) hq0
    (foldCircleDensity_nonneg (branchDensity_nonneg hq00))
  rw [← foldCircleDensity_pushforward hwm hwi,← hmap]
  exact (vectorMeasure_map_comp _ hj AddCircle.measurable_mk').symm

lemma stationaryWeight_change_branch {A : ℝ → ℂ} {J : ℝ → ℝ} {C I : Set ℝ}
    (hIC : I ⊆ C) (hi : InjOn J C) (hs : support A ⊆ I) :
    stationaryWeight C J A = stationaryWeight I J A := by
  have h := stationaryWeight_family_of_branch (Ω := Unit) hIC hi (fun _ => hs)
  funext s
  have hh := congrFun h (s,())
  exact hh

/-- The density of a literal old angular packet, not an abstract probability
model. The integer speed carrier vanishes on the temporal circle. -/
theorem oldPacket_spectralDensity_of_modulus
    {A : UnitAddCircle × UnitAddCircle → ℂ} {A₀ : ℝ → ℂ}
    {v : UnitAddCircle → ℝ} {V : ℝ → ℝ} {m c : ℤ} {o : ℝ} {C I : Set ℝ}
    (hA : Continuous A) (hA₀ : Continuous A₀)
    (hmod : ∀ u a, ‖A (u,a)‖ = ‖A (u,0)‖)
    (hAe : ∀ x ∈ Ioc o (o+1), A ((x:UnitAddCircle),0) = A₀ x)
    (has : support A₀ ⊆ Ioc o (o+1)) (hAs : support A₀ ⊆ I)
    (hv : Measurable v) (hV : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) V)
    (hVe : ∀ x ∈ I, v (x:UnitAddCircle) = V x)
    (hIo : IsOpen I) (hIC : I ⊆ C) (hinj : InjOn (fun x => (m:ℝ)*V x) C)
    (hd : ∀ x ∈ I, deriv (fun x => (m:ℝ)*V x) x ≠ 0) :
    packetSpectralMeasure (fun a => ((v a-c:ℝ):UnitAddCircle)) m A =
      AddCircle.haarAddCircle.withDensity (fun z => ENNReal.ofReal
        (foldCircleDensity (stationaryWeight C (fun x => (m:ℝ)*V x) A₀) z)) := by
  have hqc : Continuous (fun u : UnitAddCircle => ‖A (u,0)‖^2) :=
    ((hA.comp (continuous_id.prodMk continuous_const)).norm.pow 2)
  have hps := packetSpectralMeasure_of_modulus
    (φ := fun a => (((v a-(c:ℝ)) : ℝ):UnitAddCircle)) (j := m) (B := A)
    (q := fun u => ‖A (u,0)‖^2)
    (AddCircle.measurable_mk'.comp (hv.sub measurable_const)) hqc.measurable
    (fun p => by rw [hmod])
  rw [hps]
  have hmode (a : UnitAddCircle) : m • ((v a-c:ℝ):UnitAddCircle) = ((m:ℝ)*v a:UnitAddCircle) := by
    rw [← AddCircle.coe_zsmul]
    simp only [zsmul_eq_mul]
    rw [mul_sub]
    have he : ((m:ℝ)*(c:ℝ):UnitAddCircle) = 0 := by
      rw [← Int.cast_mul]
      exact (AddCircle.coe_eq_zero_iff 1).mpr ⟨m*c,by simp⟩
    rw [AddCircle.coe_sub,he,sub_zero]
  simp_rw [hmode]
  rw [stationaryWeight_change_branch hIC hinj hAs]
  apply positive_circle_branch_fold (q₀ := fun x => ‖A₀ x‖^2)
    (hqc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
    ((hA₀.norm.pow 2).measurable) (fun _ => sq_nonneg _) (fun _ => sq_nonneg _)
    (fun x hx => by rw [hAe x hx])
    (by intro x hx; apply has; intro hz; apply hx; simp [hz])
    (by intro x hx; apply hAs; intro hz; apply hx; simp [hz])
    (hv.const_mul (m:ℝ)) (contDiff_const.mul hV) (fun x hx => by rw [hVe x hx])
    hIo (hinj.mono hIC) hd

end ThreeTorus
end
end

end OAI
end

section
-- module Solutions.OAIQ13_TT.ThreeTorus_PassageFamilies
attribute [-instance] _root_.OAI.ThreeTorus.tripleVolume_regular
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Rounded common primitives, neutral and quantile families, exact indices, signal passages, and support tracking. -/

section

/-! The exact family of passage primitives used by the analytic estimates is
constructed from a periodic speed. The rounding is chosen before any jitter.
No smoothness or perturbation conclusion is assumed. -/
noncomputable section
open MeasureTheory Set Function Filter
open scoped Topology
namespace ThreeTorus

lemma deriv_real_primitive {V : ℝ → ℝ} (hV : Continuous V) :
    deriv (fun x => ∫ t in 0..x, V t) = V := by
  funext x
  exact (intervalIntegral.integral_hasDerivAt_right (hV.intervalIntegrable 0 x)
    hV.aestronglyMeasurable.stronglyMeasurableAtFilter hV.continuousAt).deriv

/-- One integer-rounded primitive sequence works for every later choice of jitter.
In particular the estimates for a finite list can all use exactly this sequence. -/
theorem exists_rounded_primitive_family {V : ℝ → ℝ}
    (hp : Periodic V 1) (hV : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) V) :
    ∃ Δ : ℕ → ℝ, ∃ H : ℕ → UnitAddCircle → UnitAddCircle,
      (∀ n, 0 < n → |Δ n| ≤ (n:ℝ)⁻¹) ∧ Tendsto Δ atTop (𝓝 0) ∧
      (∀ n, Continuous (H n)) ∧
      (∀ n (x : ℝ), H n (x:UnitAddCircle) =
        ((n:ℝ)*((∫ t in 0..x, V t)+Δ n*x):UnitAddCircle)) ∧
      ∀ J : ℝ → ℝ, ∀ hJp : Periodic J 1,
        ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) J →
        let σ := fun (n : ℕ) (a : UnitAddCircle) => (((1+hJp.lift a/(n:ℝ))/(n:ℝ):ℝ):UnitAddCircle)
        (∀ n, Smooth (torusPassage (H n) (σ n)) ∧
          Smooth (torusPassage (H n) (σ n)).symm ∧
          MeasurePreserving (torusPassage (H n) (σ n)) μ μ) ∧
        (∀ n, 0 < n → ∀ x : Cover,
          torusPassage (H n) (σ n) (project x) =
            project (passageFamily V J 1 ((n:ℝ)⁻¹,Δ n) x) ∧
          (torusPassage (H n) (σ n)).symm (project x) =
            project (passageFamily V J (-1) ((n:ℝ)⁻¹,Δ n) x)) ∧
        ∀ r : ℝ, ∀ K : Set Cover, IsCompact K → ∀ d : ℕ,
          TendstoUniformlyOn
            (fun (n : ℕ) x => iteratedFDeriv ℝ d (passageFamily V J r ((n:ℝ)⁻¹,Δ n)) x)
            (fun x => iteratedFDeriv ℝ d (fun y : Cover => ![y 0+r*V (y 1),y 1,y 2]) x)
            atTop K := by
  classical
  have hr : ∀ n : ℕ, ∃ d : ℝ, ∃ k : ℤ,
      (0 < n → |d| ≤ (n:ℝ)⁻¹) ∧ (n:ℝ)*((∫ t in 0..1, V t)+d) = k := by
    intro n
    by_cases hn : 0 < n
    · obtain ⟨d,k,hd,hk⟩ := passage_rounding (∫ t in 0..1, V t) hn
      exact ⟨d,k,fun _ => hd,hk⟩
    · have he : n = 0 := Nat.eq_zero_of_not_pos hn
      subst n
      exact ⟨0,0,by simp⟩
  choose Δ k hΔ hk using hr
  have hsp (n : ℕ) : Periodic (fun x => (n:ℝ)*(V x+Δ n)) 1 :=
    (passage_rounded_slope hp hV.continuous n (Δ n) (hk n)).1
  have hsi (n : ℕ) : (∫ t in 0..1, (n:ℝ)*(V t+Δ n)) = k n :=
    (passage_rounded_slope hp hV.continuous n (Δ n) (hk n)).2
  have hsc (n : ℕ) : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x => (n:ℝ)*(V x+Δ n)) :=
    contDiff_const.mul (hV.add contDiff_const)
  let H n := circlePrimitive (hsp n) (hsc n).continuous (hsi n)
  have hHe (n : ℕ) (x : ℝ) : H n (x:UnitAddCircle) =
      ((n:ℝ)*((∫ t in 0..x, V t)+Δ n*x):UnitAddCircle) := by
    rw [show H n (x:UnitAddCircle) = (((∫ t in 0..x, (n:ℝ)*(V t+Δ n)):ℝ):UnitAddCircle) from rfl]
    congr 1
    rw [intervalIntegral.integral_const_mul,
      intervalIntegral.integral_add (hV.continuous.intervalIntegrable 0 x) intervalIntegrable_const]
    simp only [intervalIntegral.integral_const,sub_zero,smul_eq_mul]
    ring
  refine ⟨Δ,H,hΔ,(continuous_snd.tendsto (0,0)).comp (passage_parameters_tendsto hΔ),
    fun n => continuous_circlePrimitive (hsp n) (hsc n).continuous (hsi n),hHe,?_⟩
  intro J hJp hJ
  let σ := fun (n : ℕ) (a : UnitAddCircle) => (((1+hJp.lift a/(n:ℝ))/(n:ℝ):ℝ):UnitAddCircle)
  have htsp (n : ℕ) : Periodic (fun a => (n:ℝ)⁻¹+(n:ℝ)⁻¹^2*J a) 1 := by
    intro a
    dsimp only
    rw [hJp a]
  have hσ (n : ℕ) : σ n = circleSpeed (htsp n) := by
    funext a
    induction a using QuotientAddGroup.induction_on with
    | H a =>
      change (((1+J a/(n:ℝ))/(n:ℝ):ℝ):UnitAddCircle) =
        ((((n:ℝ)⁻¹+(n:ℝ)⁻¹^2*J a):ℝ):UnitAddCircle)
      congr 1
      simp only [div_eq_mul_inv]
      ring
  refine ⟨?_,?_,?_⟩
  · intro n
    change Smooth (torusPassage (H n) (σ n)) ∧
      Smooth (torusPassage (H n) (σ n)).symm ∧
      MeasurePreserving (torusPassage (H n) (σ n)) μ μ
    rw [hσ]
    exact primitive_passage_properties (hsp n) (htsp n) (hsc n) (passage_speed_smooth hJ n) (hsi n)
  · intro n hn x
    change torusPassage (H n) (σ n) (project x) =
        project (passageFamily V J 1 ((n:ℝ)⁻¹,Δ n) x) ∧
      (torusPassage (H n) (σ n)).symm (project x) =
        project (passageFamily V J (-1) ((n:ℝ)⁻¹,Δ n) x)
    rw [hσ]
    have Hlift (u : ℝ) : H n (u:UnitAddCircle) =
        (((∫ t in 0..u, (n:ℝ)*(V t+Δ n)):ℝ):UnitAddCircle) := rfl
    have hgraphs : torusPassage (H n) (circleSpeed (htsp n)) (project x) =
          project (passageLift (fun u => ∫ t in 0..u, (n:ℝ)*(V t+Δ n))
            (fun a => (n:ℝ)⁻¹+(n:ℝ)⁻¹^2*J a) x) ∧
        (torusPassage (H n) (circleSpeed (htsp n))).symm (project x) =
          project (passageInverseLift (fun u => ∫ t in 0..u, (n:ℝ)*(V t+Δ n))
            (fun a => (n:ℝ)⁻¹+(n:ℝ)⁻¹^2*J a) x) := by
      constructor
      · rw [torusPassage_apply]
        ext i
        fin_cases i <;> simp only [project,passageLift,circleSpeed_coe,
          ← AddCircle.coe_add,Hlift,← AddCircle.coe_sub] <;> rfl
      · rw [torusPassage_symm_apply]
        ext i
        fin_cases i <;> simp only [project,passageInverseLift,circleSpeed_coe,
          ← AddCircle.coe_add,Hlift,← AddCircle.coe_sub] <;> rfl
    rw [(passageLift_eq_family (J := J) hV.continuous hn (Δ n)).1,
      (passageLift_eq_family (J := J) hV.continuous hn (Δ n)).2] at hgraphs
    exact hgraphs
  · intro r K hK d
    exact passage_Cinfty_limit hV hJ hΔ r hK d

end ThreeTorus
end
end

section

/-! Removing the identically zero retained modes does not alter either the
physical vector or its literal temporal density. This bridges the asymptotic
finite-retention producer and the exact finite index separations. -/
noncomputable section
open MeasureTheory Set Function Filter
open scoped Topology BigOperators
namespace ThreeTorus

lemma sum_eq_of_zero_off {α M : Type*} [DecidableEq α] [AddCommMonoid M]
    (f : α → M) (S T : Finset α)
    (hS : ∀ j, j ∉ S → f j = 0) (hT : ∀ j, j ∉ T → f j = 0) :
    ∑ j ∈ S, f j = ∑ j ∈ T, f j := by
  have eS : ∑ j ∈ S ∩ T, f j = ∑ j ∈ S, f j := by
    apply Finset.sum_subset Finset.inter_subset_left
    intro j hj hn
    exact hT j (fun ht => hn (Finset.mem_inter.mpr ⟨hj,ht⟩))
  have eT : ∑ j ∈ S ∩ T, f j = ∑ j ∈ T, f j := by
    apply Finset.sum_subset Finset.inter_subset_right
    intro j hj hn
    exact hS j (fun hs => hn (Finset.mem_inter.mpr ⟨hs,hj⟩))
  exact eS.symm.trans eT

lemma retainedPassage_eq_of_cover (m : ℤ) (H : UnitAddCircle → UnitAddCircle)
    (A : UnitAddCircle × UnitAddCircle → ℂ) (S T : Finset ℤ)
    (χ : ℤ → UnitAddCircle → ℝ) (ψ : UnitAddCircle → ℝ)
    (hS : ∀ j, j ∉ S → ∀ a, χ j a = 0) (hT : ∀ j, j ∉ T → ∀ a, χ j a = 0) :
    retainedPassage m H A S χ ψ = retainedPassage m H A T χ ψ := by
  funext x
  apply sum_eq_of_zero_off
  · intro j hj
    simp [hS j hj]
  · intro j hj
    simp [hT j hj]

lemma exactRetainedPacketDensity_eq_of_cover
    (I : Set ℝ) (J₀ : ℝ → ℝ) (ψ : UnitAddCircle → ℝ)
    (χ : ℝ → UnitAddCircle → ℝ) (m : ℤ) (H : ℕ → UnitAddCircle → UnitAddCircle)
    (A : UnitAddCircle × UnitAddCircle → ℂ) (S T : Finset ℤ) (n : ℕ)
    (hS : ∀ j, j ∉ S → ∀ a, χ ((j:ℝ)/n) a = 0)
    (hT : ∀ j, j ∉ T → ∀ a, χ ((j:ℝ)/n) a = 0) :
    exactRetainedPacketDensity I J₀ ψ χ m H A S n =
      exactRetainedPacketDensity I J₀ ψ χ m H A T n := by
  unfold exactRetainedPacketDensity
  congr 1
  funext t
  apply sum_eq_of_zero_off
  · intro j hj
    simp [unfoldedModeDensity,scaledBranchKernel,branchDensity,
      circleDensityLift,retainedCircleWeight,hS j hj]
  · intro j hj
    simp [unfoldedModeDensity,scaledBranchKernel,branchDensity,
      circleDensityLift,retainedCircleWeight,hT j hj]

/-- The exact finite sampling set, with no identically zero extra modes. -/
theorem cylinder_cutoff_exact_indices {ι : Type*}
    (χ : ι → ℝ → UnitAddCircle → ℝ)
    (hc : ∀ i, HasCompactSupport (χ i).uncurry) (hz : ∀ i a, χ i 0 a = 0) :
    ∃ S : ℕ → ι → Finset ℤ,
      (∀ n i j, j ∈ S n i → j ≠ 0) ∧
      ∀ n, 0 < n → ∀ i j, j ∈ S n i ↔ ∃ a, χ i ((j:ℝ)/n) a ≠ 0 := by
  classical
  have hex (n : ℕ) (i : ι) : ∃ S : Finset ℤ,
      (∀ j ∈ S, j ≠ 0) ∧
      (0 < n → ∀ j, j ∈ S ↔ ∃ a, χ i ((j:ℝ)/n) a ≠ 0) := by
    by_cases hn : 0 < n
    · obtain ⟨S,hS,hS'⟩ := cylinder_cutoff_finite_indices (hc i) (hz i) n hn
      refine ⟨S.filter (fun j => ∃ a, χ i ((j:ℝ)/n) a ≠ 0),?_,?_⟩
      · intro j hj hz
        subst j
        exact hS (Finset.mem_filter.mp hj).1
      · intro _ j
        constructor
        · exact fun hj => (Finset.mem_filter.mp hj).2
        · intro hj
          refine Finset.mem_filter.mpr ⟨?_,hj⟩
          by_contra hh
          obtain ⟨a,ha⟩ := hj
          exact ha (hS' j hh a)
    · exact ⟨∅,by simp,fun hh => (hn hh).elim⟩
  choose S hS hSe using hex
  exact ⟨S,hS,fun n hn i => hSe n i hn⟩

end ThreeTorus
end
end

section

/-! Closure of the literal output coefficient class under a passage.
The next passage uses these very coefficients, rather than new placeholders. -/
noncomputable section
open MeasureTheory Set Function Filter
open scoped Topology BigOperators
namespace ThreeTorus

lemma retainedRealCore_smooth {ψ₀ : ℝ → ℝ} {χ : ℝ → UnitAddCircle → ℝ}
    {m : ℤ} {H : UnitAddCircle → UnitAddCircle} {Hl : ℝ → ℝ}
    {A : UnitAddCircle × UnitAddCircle → ℂ}
    (hψ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ₀) (hχ : CylinderSmooth χ.uncurry)
    (hHl : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Hl)
    (hH : ∀ t : ℝ, H (t:UnitAddCircle) = (Hl t:UnitAddCircle))
    (hA : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × ℝ => A (p.1,p.2)))
    (s : ℝ) (j : ℤ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (retainedRealCore ψ₀ χ m H A s j) := by
  have hχ' : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun u : ℝ => χ s (u:UnitAddCircle)) :=
    hχ.comp (contDiff_const.prodMk contDiff_id)
  exact ((Complex.ofRealCLM.contDiff.comp hψ).mul
    (Complex.ofRealCLM.contDiff.comp hχ')).mul (smooth_exactPassageCoeff hHl hH hA j)

lemma retainedRealAmplitude_support (ψ₀ : ℝ → ℝ) (χ : ℝ → UnitAddCircle → ℝ)
    (m : ℤ) (H : UnitAddCircle → UnitAddCircle)
    (A : UnitAddCircle × UnitAddCircle → ℂ) (s : ℝ) (j : ℤ) (b : UnitAddCircle) :
    support (retainedRealAmplitude ψ₀ χ m H A s j b) ⊆ support ψ₀ := by
  intro u hu hz
  exact hu (by simp [retainedRealAmplitude,retainedRealCore,hz])

/-- Every analytic lift condition required by the next stationary-phase
passage follows from the smooth real core and the spare character. -/
lemma retainedRealAmplitude_regular {C : ℝ → ℂ}
    (hC : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) C) (m : ℤ) :
    (∀ b : UnitAddCircle, ContDiff ℝ 2 (fun u : ℝ => C u*fourier m b)) ∧
    Continuous (fun p : UnitAddCircle × ℝ => C p.2*fourier m p.1) ∧
    Continuous (fun p : UnitAddCircle × ℝ => deriv (fun u : ℝ => C u*fourier m p.1) p.2) ∧
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : ℝ × ℝ => C p.1*fourier m (p.2:UnitAddCircle)) := by
  refine ⟨fun _ => (hC.mul contDiff_const).of_le (by exact WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤)),
    (hC.continuous.comp continuous_snd).mul ((fourier m).continuous.comp continuous_fst),?_,
    (hC.comp contDiff_fst).mul ((smooth_fourier_lift m).comp contDiff_snd)⟩
  have hD : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (deriv C) :=
    (contDiff_infty_iff_deriv.mp hC).2
  have he (p : UnitAddCircle × ℝ) : deriv (fun u : ℝ => C u*fourier m p.1) p.2 =
      deriv C p.2*fourier m p.1 := deriv_mul_const (hC.differentiable (by simp) p.2) _
  simp_rw [he]
  exact (hD.continuous.comp continuous_snd).mul ((fourier m).continuous.comp continuous_fst)

lemma retainedRealAmplitude_matches {ψ : UnitAddCircle → ℝ} {ψ₀ : ℝ → ℝ}
    (χ : ℝ → UnitAddCircle → ℝ) (m : ℤ) (H : ℕ → UnitAddCircle → UnitAddCircle)
    (A : UnitAddCircle × UnitAddCircle → ℂ) (n : ℕ) (j : ℤ) {o : ℝ}
    (he : ∀ u ∈ Ioc o (o+1), ψ (u:UnitAddCircle) = ψ₀ u) :
    ∀ b u, u ∈ Ioc o (o+1) →
      retainedAmplitude ψ χ m H A n j ((u:UnitAddCircle),b) =
        retainedRealAmplitude ψ₀ χ m (H n) A ((j:ℝ)/n) j b u := by
  intro b u hu
  simp only [retainedAmplitude,retainedRealAmplitude,retainedRealCore,he u hu]

lemma retainedAmplitude_smooth_lift
    {ψ : UnitAddCircle → ℝ} {χ : ℝ → UnitAddCircle → ℝ}
    {m : ℤ} {H : ℕ → UnitAddCircle → UnitAddCircle} {Hl : ℕ → ℝ → ℝ}
    {A : UnitAddCircle × UnitAddCircle → ℂ}
    (hψ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun u : ℝ => ψ u))
    (hχ : CylinderSmooth χ.uncurry)
    (hHl : ∀ n, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Hl n))
    (hH : ∀ n (t : ℝ), H n (t:UnitAddCircle) = (Hl n t:UnitAddCircle))
    (hA : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × ℝ => A (p.1,p.2)))
    (n : ℕ) (j : ℤ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : ℝ × ℝ => retainedAmplitude ψ χ m H A n j (p.1,p.2)) := by
  have hs := smooth_retained_amplitude (m := m) (j := j) ((j:ℝ)/n) (hHl n) (hH n) hA hχ hψ
  convert hs using 1
  all_goals try with_reducible_and_instances rfl
  funext p
  dsimp [retainedAmplitude]
  ring

end ThreeTorus

namespace ThreeTorus
open Set

/-- The buffered real integration interval can always be fixed before the
next passage integer, even when all the coefficients are zero. -/
lemma compact_inside_buffered_interval {K : Set ℝ} {a b : ℝ}
    (hK : IsCompact K) (hab : a < b) (hKI : K ⊆ Ioo a b) :
    ∃ l u R : ℝ, a < l ∧ l < u ∧ u < b ∧ 0 < R ∧
      K ⊆ Ioc l u ∧ Icc (l-2*R) (u+2*R) ⊆ Ioo a b := by
  let K' := insert ((a+b)/2) K
  have hc : IsCompact K' := hK.insert _
  have hsub : K' ⊆ Ioo a b := by
    intro x hx
    rcases mem_insert_iff.mp hx with rfl | hx
    · constructor <;> linarith
    · exact hKI hx
  obtain ⟨x,hx,hmin⟩ := hc.exists_isMinOn (insert_nonempty _ _) continuous_id.continuousOn
  obtain ⟨y,hy,hmax⟩ := hc.exists_isMaxOn (insert_nonempty _ _) continuous_id.continuousOn
  have hx' := hsub hx
  have hy' := hsub hy
  have hxy : x ≤ y := hmin hy
  let l := (a+x)/2
  let u := (y+b)/2
  have hal : a < l := by dsimp [l]; linarith [hx'.1]
  have hlu : l < u := by dsimp [l,u]; linarith [hx'.1,hy'.2]
  have hub : u < b := by dsimp [u]; linarith [hy'.2]
  let R := min (l-a) (b-u)/4
  have hR : 0 < R := div_pos (lt_min (sub_pos.mpr hal) (sub_pos.mpr hub)) (by norm_num)
  have hR₁ : 4*R ≤ l-a := by dsimp [R]; linarith [min_le_left (l-a) (b-u)]
  have hR₂ : 4*R ≤ b-u := by dsimp [R]; linarith [min_le_right (l-a) (b-u)]
  refine ⟨l,u,R,hal,hlu,hub,hR,?_,?_⟩
  · intro z hz
    have hz' : z ∈ K' := mem_insert_of_mem _ hz
    have hminz := hmin hz'
    have hmaxz := hmax hz'
    constructor <;> dsimp [l,u] at * <;> linarith
  · intro z hz
    constructor <;> linarith [hz.1,hz.2]

end ThreeTorus
end
end

section

/-! A concrete closed class for finite passage iteration.  The constructor
below uses the literal retained amplitudes; it does not postulate a next
packet state or any of its analytic regularity. -/
noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators
namespace ThreeTorus

lemma smooth_new_speed {J : ℝ → ℝ}
    (hJ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) J) (n : ℕ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun u => (1+J u/n)/n) :=
  (contDiff_const.add (hJ.div_const _)).div_const _

lemma positive_deriv_new_speed {J : ℝ → ℝ} {n : ℕ} {x : ℝ}
    (hn : 0 < n) (hd : 0 < deriv J x) :
    0 < deriv (fun u => (1+J u/n)/n) x := by
  simpa only [deriv_div_const,deriv_const_add] using
    div_pos (div_pos hd (show (0:ℝ)<n by exact_mod_cast hn)) (show (0:ℝ)<n by exact_mod_cast hn)

/-- A neutral or quantile passage produces a valid input family for the next
passage, with all real lifts supported in one common compact good interval.
The jitter may be arbitrarily broad. The constructor works at EVERY positive
passage integer, independently of the spectral/physical approximation bounds. -/
theorem literal_output_packets {ι : Type*} [Fintype ι]
    (m : ι → ℤ) (A : ι → UnitAddCircle × UnitAddCircle → ℂ)
    (H : ℕ → UnitAddCircle → UnitAddCircle) (Hl : ℕ → ℝ → ℝ)
    (χ : ι → ℝ → UnitAddCircle → ℝ) (S : ι → Finset ℤ)
    (hS : ∀ i j, j ∈ S i → j ≠ 0)
    (hAc : ∀ i, Continuous (A i))
    (hAs : ∀ i, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × ℝ => A i (p.1,p.2)))
    (hχ : ∀ i, CylinderSmooth (χ i).uncurry) (hχc : ∀ i, Continuous (χ i).uncurry)
    (hHc : ∀ n, Continuous (H n))
    (hHl : ∀ n, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Hl n))
    (hHe : ∀ n (x : ℝ), H n (x:UnitAddCircle) = (Hl n x:UnitAddCircle))
    {δ : ℝ} (c : LawCutoffs δ) (hδ : 0 < δ) (hδ' : δ < 1/8)
    {J : ℝ → ℝ} (hpJ : Periodic J 1) (hJ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) J)
    (hdJ : ∀ x ∈ Ioo δ (1-δ), 0 < deriv J x) {n : ℕ} (hn : 0 < n) :
    ∃ F : PassagePackets (PassageOutputIndex S),
      (∀ i, F.m i = i.2.val) ∧
      (∀ i, F.A i = retainedAmplitude (neutralCircleCutoff c) (χ i.1) (m i.1) H (A i.1) n i.2.val) ∧
      (∀ i, F.A₀ i = retainedRealAmplitude c.ψ (χ i.1) (m i.1) (H n) (A i.1)
        ((i.2.val:ℝ)/n) i.2.val) ∧
      F.V = (fun x => (1+J x/n)/n) ∧ F.o = 0 ∧
      δ < F.l ∧ F.u < 1-δ ∧ F.SpareIndependent := by
  obtain ⟨l,u,R,hδl,hlu,huδ,hR,hKI,hbuffer⟩ := compact_inside_buffered_interval
    c.ψ_compact (by linarith : δ < 1-δ) c.ψ_support
  let ψ := neutralCircleCutoff c
  have hψs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : ℝ => ψ x) := by
    simp only [ψ,neutralCircleCutoff_coe]
    exact contDiff_periodize c.ψ_smooth c.ψ_compact
  have hψe : ∀ x ∈ Ioc (0:ℝ) (0+1), ψ (x:UnitAddCircle) = c.ψ x := by
    intro x hx
    rw [show ψ (x:UnitAddCircle) = lawPsi c x from neutralCircleCutoff_coe c x]
    exact periodize_eq_on_unit ((subset_tsupport c.ψ).trans
      (c.ψ_support.trans (by intro z hz; constructor <;> linarith [hz.1,hz.2]))) ⟨hx.1.le,by simpa using hx.2⟩
  let A' (i : PassageOutputIndex S) := retainedAmplitude ψ (χ i.1) (m i.1) H (A i.1) n i.2.val
  let A₀' (i : PassageOutputIndex S) := retainedRealAmplitude c.ψ (χ i.1) (m i.1) (H n) (A i.1)
    ((i.2.val:ℝ)/n) i.2.val
  have hcore (i : PassageOutputIndex S) := retainedRealCore_smooth (m := m i.1) c.ψ_smooth (hχ i.1)
    (hHl n) (hHe n) (hAs i.1) ((i.2.val:ℝ)/n) i.2.val
  have hreg (i : PassageOutputIndex S) := retainedRealAmplitude_regular (hcore i) (m i.1)
  have hA' i : Continuous (A' i) := by
    dsimp [A',retainedAmplitude]
    exact (((Complex.continuous_ofReal.comp ((continuous_neutralCircleCutoff c).comp continuous_fst)).mul
      (Complex.continuous_ofReal.comp ((hχc i.1).comp (continuous_const.prodMk continuous_fst)))).mul
      ((continuous_exactPassageCoeff (hHc n) (hAc i.1) _).comp continuous_fst)).mul
      ((fourier (m i.1)).continuous.comp continuous_snd)
  let F : PassagePackets (PassageOutputIndex S) := {
    m := fun i => i.2.val
    nonzero := fun i => hS i.1 i.2.val i.2.property
    A := A'
    A₀ := A₀'
    o := 0
    l := l
    u := u
    R := R
    lo := hδ.le.trans hδl.le
    uo := by linarith
    lu := hlu.le
    Rpos := hR
    lift_matches := fun i => retainedRealAmplitude_matches (χ i.1) (m i.1) H (A i.1) n i.2.val hψe
    two := fun i => (hreg i).1
    continuous_lift := fun i => (hreg i).2.1
    continuous_deriv := fun i => (hreg i).2.2.1
    smooth_lift := fun i => (hreg i).2.2.2
    support_lift := fun i a => (retainedRealAmplitude_support _ _ _ _ _ _ _ a).trans
      ((subset_tsupport c.ψ).trans hKI)
    continuous_amplitude := hA'
    smooth_amplitude := fun i => retainedAmplitude_smooth_lift hψs (hχ i.1) hHl hHe (hAs i.1) n i.2.val
    V := fun x => (1+J x/n)/n
    periodic := fun x => by dsimp; rw [hpJ x]
    smooth_speed := smooth_new_speed hJ n
    positive_deriv := fun x hx => positive_deriv_new_speed hn (hdJ x (hbuffer hx)) }
  refine ⟨F,fun _ => rfl,fun _ => rfl,fun _ => rfl,rfl,rfl,hδl,huδ,?_,?_⟩
  · intro i a x
    dsimp [F,A₀',retainedRealAmplitude]
    simp only [norm_mul, Circle.norm_coe]
  · intro i v a
    exact retainedAmplitude_modulus ψ (χ i.1) (m i.1) H (A i.1) n i.2.val v a

lemma output_index_injective {ι : Type*} {S : ι → Finset ℤ}
    (hd : Pairwise (fun i j => Disjoint (S i) (S j))) :
    Injective (fun i : PassageOutputIndex S => i.2.val) := by
  intro i j he
  have hij : i.1 = j.1 := by
    by_contra h
    exact Finset.disjoint_left.mp (hd h) i.2.property (by simpa only [he] using j.2.property)
  cases i with
  | mk i k =>
    cases j with
    | mk j l =>
      dsimp at hij he
      subst j
      exact congrArg (Sigma.mk i) (Subtype.ext he)

end ThreeTorus
end
end

section

/-! A finite quantile passage, using one and the same rounded primitive and
literal finite retained Fourier coefficients for all physical and spectral
conclusions. The law and all finite input data precede the final integer. -/
noncomputable section
open MeasureTheory Set Function Filter
open scoped Topology BigOperators FourierTransform
namespace ThreeTorus

theorem exists_simultaneous_quantile_passage {ι : Type*} [Fintype ι]
    {A : ι → UnitAddCircle × UnitAddCircle → ℂ} {A₀ : ι → UnitAddCircle → ℝ → ℂ}
    {V : ℝ → ℝ} {m : ι → ℤ} {o l u R : ℝ}
    (hm : ∀ i, m i ≠ 0)
    (hA : ∀ i a x, x ∈ Ioc o (o+1) → A i ((x : UnitAddCircle),a) = A₀ i a x)
    (hA₀ : ∀ i a, ContDiff ℝ 2 (A₀ i a)) (hAc : ∀ i, Continuous (A₀ i).uncurry)
    (hAd : ∀ i, Continuous (fun p : UnitAddCircle × ℝ => deriv (A₀ i p.1) p.2))
    (hAr : ∀ i, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : ℝ × ℝ => A₀ i (p.2 : UnitAddCircle) p.1))
    (hsupp : ∀ i a, support (A₀ i a) ⊆ Ioc l u)
    (hlo : o ≤ l) (huo : u ≤ o+1) (hlu : l ≤ u) (hR : 0 < R)
    (hpV : Periodic V 1) (hV : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) V)
    (hdV : ∀ x ∈ Icc (l-2*R) (u+2*R), 0 < deriv V x)
    (h0 : ∀ i, 0 ∉ (fun x => (m i:ℝ)*V x) '' Icc l u)
    (hAcont : ∀ i, Continuous (A i))
    (hAs : ∀ i, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × ℝ => A i (p.1,p.2)))
    (hmod : ∀ i a x, ‖A₀ i a x‖ = ‖A₀ i 0 x‖)
    (hmodA : ∀ i u a, ‖A i (u,a)‖ = ‖A i (u,0)‖)
    {ρ : ℝ → ℝ} (hρ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ρ) (hi : Integrable ρ)
    (hp : ∀ y, 0 < ρ y) (hρm : ∫ y, ρ y = 1)
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ y, |ρ y| ≤ C/(1+y^2)) {D : ℝ}
    (hF : ∀ v, D < |v| → 𝓕 (fun y => (ρ y : ℂ)) v = 0)
    {δ : ℝ} (c : LawCutoffs δ) (hδ : 0 < δ) (hδ' : δ < 1/8)
    {χ : ι → ℝ → UnitAddCircle → ℝ}
    (hχs : ∀ i, CylinderSmooth (χ i).uncurry)
    (hχc : ∀ i, Continuous (χ i).uncurry) (hcχ : ∀ i, HasCompactSupport (χ i).uncurry)
    (hzχ : ∀ i a, χ i 0 a = 0) (hχ : ∀ i s a, 0 ≤ χ i s a ∧ χ i s a ≤ 1)
    (hχW : ∀ i s a, stationaryWeight (Icc (l-R) (u+R)) (fun x => (m i:ℝ)*V x)
      (A₀ i a) s ≠ 0 → χ i s a = 1)
    {g : ι → UnitAddCircle → ℝ} (hg : ∀ i, Continuous (g i)) {ε : ℝ}
    (hideal : ∀ i, ∀ s ∈ support (stationaryWeight (Icc (l-R) (u+R))
      (fun x => (m i:ℝ)*V x) (A₀ i 0)),
      ∀ y, |foldCircleDensity (scaledDensity ρ s) y-g i y| ≤ ε) :
    ∃ Δ : ℕ → ℝ, ∃ H : ℕ → UnitAddCircle → UnitAddCircle,
      (∀ n, 0 < n → |Δ n| ≤ (n:ℝ)⁻¹) ∧ Tendsto Δ atTop (𝓝 0) ∧
      (∀ n, Continuous (H n)) ∧
      (∀ n (x : ℝ), H n (x:UnitAddCircle) =
        ((n:ℝ)*((∫ t in 0..x, V t)+Δ n*x):UnitAddCircle)) ∧
      let ψ := neutralCircleCutoff c
      let J := quantileCircleJitter ρ c
      let J₀ := lawJitter ρ c
      let σ := fun (n : ℕ) a => (((1+J a/n)/n:ℝ):UnitAddCircle)
      (∀ n, Smooth (torusPassage (H n) (σ n)) ∧
        Smooth (torusPassage (H n) (σ n)).symm ∧
        MeasurePreserving (torusPassage (H n) (σ n)) μ μ) ∧
      (∀ n, 0 < n → ∀ x : Cover,
        torusPassage (H n) (σ n) (project x) =
          project (passageFamily V J₀ 1 ((n:ℝ)⁻¹,Δ n) x) ∧
        (torusPassage (H n) (σ n)).symm (project x) =
          project (passageFamily V J₀ (-1) ((n:ℝ)⁻¹,Δ n) x)) ∧
      (∀ r : ℝ, ∀ K : Set Cover, IsCompact K → ∀ d : ℕ,
        TendstoUniformlyOn
          (fun (n : ℕ) x => iteratedFDeriv ℝ d (passageFamily V J₀ r ((n:ℝ)⁻¹,Δ n)) x)
          (fun x => iteratedFDeriv ℝ d (fun y : Cover => ![y 0+r*V (y 1),y 1,y 2]) x)
          atTop K) ∧
      ∃ S : ℕ → ι → Finset ℤ,
        (∀ n, 0 < n → ∀ i j, j ∈ S n i → j ≠ 0) ∧
        (∀ n, 0 < n → ∀ i j, j ∉ S n i → ∀ a, χ i ((j:ℝ)/n) a = 0) ∧
        (∀ n, 0 < n → ∀ i j, j ∈ S n i ↔ ∃ a, χ i ((j:ℝ)/n) a ≠ 0) ∧
        ∀ η : ℝ, 0 < η → ∀ᶠ n : ℕ in atTop,
          0 < n ∧ ∀ i,
          let f := retainedPassage (m i) (H n) (A i) (S n i) (fun j => χ i ((j:ℝ)/n)) ψ
          let p := exactRetainedPacketDensity (Ioo δ (1-δ)) J₀ ψ (χ i) (m i) H (A i) (S n i) n
          let w := stationaryWeight (Icc (l-R) (u+R)) (fun x => (m i:ℝ)*V x) (A₀ i 0)
          (∫ x : TripleTorus, ‖packet (m i) (A i) x-f (passageChart (H n) x)‖^2 ∂tripleVolume) <
            8*δ*(∫ u, ‖A i (u,0)‖^2 ∂AddCircle.haarAddCircle)+η ∧
          (∫ z, |p z-foldCircleDensity w z*g i ((n:ℤ) • z)| ∂AddCircle.haarAddCircle) <
            (∫ s, w s)*(4*δ+ε)+η ∧
          ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : ℝ => p x) ∧
          (∀ k : ℤ, (∫ x : TripleTorus, starRingEnd ℂ (f x)*f (twistIter (σ n) k x) ∂tripleVolume) =
            ∫ z, (p z:ℂ)*fourier k z ∂AddCircle.haarAddCircle) ∧
          (∀ j u a, ‖retainedAmplitude ψ (χ i) (m i) H (A i) n j (u,a)‖ =
            ‖retainedAmplitude ψ (χ i) (m i) H (A i) n j (u,0)‖) := by
  classical
  obtain ⟨Δ,H,hΔ,hΔt,hHc,hHe,hgeo⟩ := exists_rounded_primitive_family hpV hV
  have hPr : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x => ∫ t in 0..x, V t) :=
    contDiff_real_primitive hV
  have hPV : deriv (fun x => ∫ t in 0..x, V t) = V := deriv_real_primitive hV.continuous
  obtain ⟨hg,hgraph,hlimit⟩ := hgeo (lawJitter ρ c) (periodize_periodic _)
    (lawJitter_smooth c hρ hi hp hρm)
  obtain ⟨T,hTN,hTE⟩ := cylinder_cutoff_exact_indices χ hcχ hzχ
  have hTZ n (hn : 0 < n) i j (hj : j ∉ T n i) a : χ i ((j:ℝ)/n) a = 0 := by
    by_contra hh
    exact hj ((hTE n hn i j).mpr ⟨a,hh⟩)
  refine ⟨Δ,H,hΔ,hΔt,hHc,hHe,hg,hgraph,hlimit,T,fun n _ i => hTN n i,hTZ,hTE,?_⟩
  intro η hη
  have hpass i := exact_quantile_passage (hm i) hHe (hA i) (hA₀ i) (hAc i) (hAd i)
    (hAr i) (hsupp i) hlo huo hlu hR hPr hV hPV hdV (h0 i) hHc (hAcont i) hΔt
    (hmod i) (hmodA i) (hAs i) hρ hi hp hρm hC hb hF c hδ hδ'
    (hχs i) (hχc i) (hcχ i) (hzχ i) (hχ i) (hχW i) (hg := ‹∀ i, Continuous (g i)› i)
    (hideal i) hη
  choose S hSN hST hgood using hpass
  have hgall := (Filter.eventually_all).mpr hgood
  filter_upwards [eventually_gt_atTop (0:ℕ),hgall] with n hn hall
  refine ⟨hn,fun i => ?_⟩
  have ef := retainedPassage_eq_of_cover (m i) (H n) (A i) (S i n) (T n i)
    (fun j => χ i ((j:ℝ)/n)) (neutralCircleCutoff c) (hST i n hn) (hTZ n hn i)
  have ep := exactRetainedPacketDensity_eq_of_cover (Ioo δ (1-δ)) (lawJitter ρ c)
    (neutralCircleCutoff c) (χ i) (m i) H (A i) (S i n) (T n i) n (hST i n hn) (hTZ n hn i)
  simpa only [ef,ep] using hall i

end ThreeTorus
end
end

section

/-! All law and finite-family uniformity hypotheses of the actual quantile
passage are discharged by the source's explicit positive signal law. Its
modulus and strength bound precede every future scale and packet family. -/
noncomputable section
open MeasureTheory Set Function Filter
open scoped Topology BigOperators FourierTransform
namespace ThreeTorus

universe u

theorem exists_signal_family_law
    {b D : ℝ} (hb : 0 < b) (hbD : b < D)
    {d : ℝ → ℂ} (hd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) d)
    (hdc : HasCompactSupport d) (hdr : ∀ v, d (-v) = starRingEnd ℂ (d v))
    (hd0 : d 0 = 0) (hds : support d ⊆ Icc (-D) D) :
    ∃ α : ℝ, ∃ L : ℕ, ∃ γ₀ : ℝ,
      0 < α ∧ α < b/2 ∧ 2 ≤ L ∧ D/b < L ∧ 0 < γ₀ ∧
      ∀ γ : ℝ, 0 < γ → γ ≤ γ₀ →
      (∀ v, 2*γ*‖d v‖ ≤ 1/2) ∧
      ∀ (ι : Type u) [Fintype ι], ∀ B : ℝ, 0 < B → ∀ m : ι → ℤ, (∀ i, b ≤ |(m i:ℝ)/B|) →
      ∀ φ : ℝ → ℝ, Continuous φ → ∀ K : Set ℝ, IsCompact K →
      ∀ A : ι → ℝ → ℂ, (∀ i, support (A i) ⊆ K) → ∀ C₀ : Set ℝ,
      ∀ ε : ℝ, 0 < ε → ∀ᶠ c : ℝ in atTop,
        0 < c ∧
        let ρ := signalJitter α γ d (signalPrimeProduct L) B c
        ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ρ ∧ Integrable ρ ∧
        (∀ y, 0 < ρ y) ∧ (∫ y, ρ y = 1) ∧
        (∃ C > 0, (∀ y, |ρ y| ≤ C/(1+y^2)) ∧
          ∀ v, c*B*D < |v| → 𝓕 (fun y => (ρ y : ℂ)) v = 0) ∧
        ∀ i, ∀ s ∈ support (stationaryWeight C₀ (fun x => (m i:ℝ)*(c+φ x)) (A i)),
          ∀ y, |foldCircleDensity (scaledDensity ρ s) y-
            signalCircleModel (signalPrimeProduct L) γ B d (m i) y| ≤ ε := by
  obtain ⟨α,L,γ₀,hα,hαb,hL,hLD,hγ₀,hγ⟩ := exists_signal_positive_law hb hd hdc hdr hd0 hds
  refine ⟨α,L,γ₀,hα,hαb,hL,hLD,hγ₀,?_⟩
  intro γ hγp hγs
  obtain ⟨hlaw,hdb,_⟩ := hγ γ hγp hγs
  refine ⟨hdb,?_⟩
  intro ι inst B hB m hm φ hφ K hK A hA C₀ ε hε
  obtain ⟨V₀,hV₀⟩ := (hK.image hφ).isBounded.exists_norm_le
  have hV x (hx : x ∈ K) : |φ x| ≤ V₀ := hV₀ _ (mem_image_of_mem φ hx)
  have hbound h R := (hlaw h).2.2.2 R
  have hαb' : α < b := by linarith
  have hαD : α ≤ D := (hαb'.trans hbD).le
  have hf i := signalCircleModel_uniform_on_weight hα hαb' hαD hB hb hLD γ hd hdc hdr hd0 hds
    (C := C₀) (m i) (hm i) hbound (hA i) hV ε hε
  have hall := (Filter.eventually_all).mpr hf
  filter_upwards [eventually_gt_atTop (0:ℝ),hall] with c hc hcmodel
  refine ⟨hc,?_⟩
  obtain ⟨hρ,hρi,hρp,hρm,C,hC,hCb,hCF⟩ := signalJitter_law_regular hα hB hc hαD hd hdc hdr
    hd0 hds (signalPrimeProduct L) hbound
  exact ⟨hρ,hρi,hρp,hρm,⟨C,hC,hCb,hCF⟩,hcmodel⟩

end ThreeTorus
end
end

section

noncomputable section
open Set Function Filter
open scoped Topology
namespace ThreeTorus

/-- The integral carrier can meet every additional lower bound, as required
when the signal strength and approximation tolerance are selected first. -/
theorem eventually_integral_speed_separation {ι X : Type*} [Finite ι]
    [TopologicalSpace X] [CompactSpace X] (m : ι → ℤ) (φ : X → ℝ)
    (hm : ∀ i, m i ≠ 0) (hφ : Continuous φ) :
    ∀ᶠ c : ℕ in Filter.atTop, 0 < c ∧
      (∀ i x, (m i : ℝ) * ((c:ℝ) + φ x) ≠ 0) ∧
      (∀ i j x y, (m i : ℝ) * ((c:ℝ) + φ x) =
        (m j : ℝ) * ((c:ℝ) + φ y) → m i = m j) := by
  obtain ⟨R,hR⟩ := (isCompact_range hφ).isBounded.exists_norm_le
  obtain ⟨D,hD⟩ := (Set.finite_range (fun i => (m i : ℝ))).isCompact.isBounded.exists_norm_le
  let B := max R 0
  let M := max D 0
  have hB : 0 ≤ B := le_max_right _ _
  have hM : 0 ≤ M := le_max_right _ _
  have hφB x : |φ x| ≤ B := (hR _ (mem_range_self x)).trans (le_max_left _ _)
  have hmM i : |(m i : ℝ)| ≤ M := (hD _ (mem_range_self i)).trans (le_max_left _ _)
  have hct := (tendsto_natCast_atTop_atTop : Filter.Tendsto (fun c : ℕ => (c:ℝ))
    Filter.atTop Filter.atTop).eventually (Filter.eventually_gt_atTop (2*M*B+B+1))
  filter_upwards [hct] with c hc
  have hMB : 0 ≤ M*B := mul_nonneg hM hB
  have hcB : B < (c:ℝ) := by nlinarith
  have hcp : (0:ℝ) < c := hB.trans_lt hcB
  refine ⟨by exact_mod_cast hcp,?_,?_⟩
  · intro i x
    apply mul_ne_zero (by exact_mod_cast hm i)
    have ht := (abs_le.mp (hφB x)).1
    linarith
  · intro i j x y he
    by_contra hij
    have hd : 1 ≤ |((m i-m j : ℤ):ℝ)| := by
      exact_mod_cast Int.one_le_abs (sub_ne_zero.mpr hij)
    have he' : ((m i:ℝ)-(m j:ℝ))*(c:ℝ) = (m j:ℝ)*φ y-(m i:ℝ)*φ x := by
      nlinarith [he]
    have hh : |(m j:ℝ)*φ y-(m i:ℝ)*φ x| ≤ 2*M*B := calc
      _ ≤ |(m j:ℝ)*φ y|+|(m i:ℝ)*φ x| := abs_sub _ _
      _ = |(m j:ℝ)| *|φ y|+|(m i:ℝ)| *|φ x| := by rw [abs_mul,abs_mul]
      _ ≤ M*B+M*B := add_le_add
        (mul_le_mul (hmM j) (hφB y) (abs_nonneg _) hM)
        (mul_le_mul (hmM i) (hφB x) (abs_nonneg _) hM)
      _ = 2*M*B := by ring
    rw [← he',abs_mul,abs_of_pos hcp] at hh
    simp only [Int.cast_sub] at hd
    nlinarith

end ThreeTorus
end
end

section

/-! A genuine signal passage, not an abstract transmission oracle. The signal
prime modulus and strength bound precede all packet scales; one sufficiently
large integral carrier fixes the explicit positive law, and the SAME literal
retained coefficients satisfy geometry, physical and spectral conclusions. -/
noncomputable section
open MeasureTheory Set Function Filter
open scoped Topology BigOperators FourierTransform
namespace ThreeTorus

universe u

theorem exists_actual_signal_family
    {b D : ℝ} (hb : 0 < b) (hbD : b < D)
    {d : ℝ → ℂ} (hd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) d)
    (hdc : HasCompactSupport d) (hdr : ∀ v, d (-v) = starRingEnd ℂ (d v))
    (hd0 : d 0 = 0) (hds : support d ⊆ Icc (-D) D) :
    ∃ α : ℝ, ∃ L : ℕ, ∃ γ₀ : ℝ,
      0 < α ∧ α < b/2 ∧ 2 ≤ L ∧ D/b < L ∧ 0 < γ₀ ∧
      ∀ γ : ℝ, 0 < γ → γ ≤ γ₀ →
      (∀ v, 2*γ*‖d v‖ ≤ 1/2) ∧
      ∀ (ι : Type u) [Fintype ι], ∀ (B : ℝ), 0 < B → ∀ (m : ι → ℤ), (∀ i, b ≤ |(m i:ℝ)/B|) →
      ∀ (A : ι → UnitAddCircle × UnitAddCircle → ℂ)
        (A₀ : ι → UnitAddCircle → ℝ → ℂ) (φ : ℝ → ℝ) (o l u R : ℝ),
      (∀ i a x, x ∈ Ioc o (o+1) → A i ((x : UnitAddCircle),a) = A₀ i a x) →
      (∀ i a, ContDiff ℝ 2 (A₀ i a)) → (∀ i, Continuous (A₀ i).uncurry) →
      (∀ i, Continuous (fun p : UnitAddCircle × ℝ => deriv (A₀ i p.1) p.2)) →
      (∀ i, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun p : ℝ × ℝ => A₀ i (p.2 : UnitAddCircle) p.1)) →
      (∀ i a, support (A₀ i a) ⊆ Ioc l u) →
      o ≤ l → u ≤ o+1 → l ≤ u → 0 < R →
      Periodic φ 1 → ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ →
      (∀ x ∈ Icc (l-2*R) (u+2*R), 0 < deriv φ x) →
      (∀ i, Continuous (A i)) →
      (∀ i, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × ℝ => A i (p.1,p.2))) →
      (∀ i a x, ‖A₀ i a x‖ = ‖A₀ i 0 x‖) →
      (∀ i u a, ‖A i (u,a)‖ = ‖A i (u,0)‖) →
      ∀ ε : ℝ, 0 < ε → ∀ᶠ C : ℕ in atTop,
        0 < C ∧
        (∀ i j x y, (m i:ℝ)*((C:ℝ)+φ x) = (m j:ℝ)*((C:ℝ)+φ y) → m i = m j) ∧
        ∀ δ : ℝ, ∀ c : LawCutoffs δ, 0 < δ → δ < 1/8 →
        ∀ χ : ι → ℝ → UnitAddCircle → ℝ,
        (∀ i, CylinderSmooth (χ i).uncurry) →
        (∀ i, Continuous (χ i).uncurry) → (∀ i, HasCompactSupport (χ i).uncurry) →
        (∀ i a, χ i 0 a = 0) → (∀ i s a, 0 ≤ χ i s a ∧ χ i s a ≤ 1) →
        (∀ i s a, stationaryWeight (Icc (l-R) (u+R))
          (fun x => (m i:ℝ)*((C:ℝ)+φ x)) (A₀ i a) s ≠ 0 → χ i s a = 1) →
        ActualQuantileFamily A A₀ (fun x => (C:ℝ)+φ x) m l u R
          (signalJitter α γ d (signalPrimeProduct L) B C) c χ
          (fun i => signalCircleModel (signalPrimeProduct L) γ B d (m i)) ε := by
  obtain ⟨α,L,γ₀,hα,hαb,hL,hLD,hγ₀,hγ⟩ :=
    exists_signal_family_law hb hbD hd hdc hdr hd0 hds
  refine ⟨α,L,γ₀,hα,hαb,hL,hLD,hγ₀,?_⟩
  intro γ hγp hγs
  obtain ⟨hdb,hlaw⟩ := hγ γ hγp hγs
  refine ⟨hdb,?_⟩
  intro ι inst B hB m hm A A₀ φ o l u R hA hA₀ hAc hAd hAr hsupp hlo huo hlu hR
    hpφ hφ hdφ hAcont hAs hmod hmodA ε hε
  have hmn i : m i ≠ 0 := by
    intro hz
    have hh := hm i
    simp only [hz,Int.cast_zero,zero_div,abs_zero] at hh
    linarith
  have hφcircle : Continuous hpφ.lift := by
    apply Continuous.quotient_lift
    exact hφ.continuous
  have hsep := eventually_integral_speed_separation m hpφ.lift hmn hφcircle
  have hρ := (tendsto_natCast_atTop_atTop : Tendsto (fun C : ℕ => (C:ℝ)) atTop atTop).eventually
    (hlaw ι B hB m hm φ hφ.continuous (Icc l u) isCompact_Icc (fun i => A₀ i 0)
      (fun i => (hsupp i 0).trans Ioc_subset_Icc_self) (Icc (l-R) (u+R)) ε hε)
  filter_upwards [hsep,hρ] with C hsepC hρC
  obtain ⟨_hCp,hρs,hρi,hρp,hρm,⟨C₁,hC₁,hC₁b,hρF⟩,hideal⟩ := hρC
  refine ⟨hsepC.1,fun i j x y => hsepC.2.2 i j (x:UnitAddCircle) (y:UnitAddCircle),?_⟩
  intro δ c hδ hδ' χ hχs hχc hcχ hzχ hχ hχW
  have hpV : Periodic (fun x => (C:ℝ)+φ x) 1 := fun x => by
    change (C:ℝ)+φ (x+1) = (C:ℝ)+φ x
    rw [hpφ x]
  have hV : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x => (C:ℝ)+φ x) :=
    contDiff_const.add hφ
  have hdV x (hx : x ∈ Icc (l-2*R) (u+2*R)) :
      0 < deriv (fun x => (C:ℝ)+φ x) x := by
    simpa only [deriv_const_add] using hdφ x hx
  have h0 i : 0 ∉ (fun x => (m i:ℝ)*((C:ℝ)+φ x)) '' Icc l u := by
    rintro ⟨x,_hx,he⟩
    exact hsepC.2.1 i (x:UnitAddCircle) he
  refine ⟨hρs,hρi,hρp,hρm,?_⟩
  exact exists_simultaneous_quantile_passage hmn hA hA₀ hAc hAd hAr hsupp hlo huo hlu hR
    hpV hV hdV h0 hAcont hAs hmod hmodA hρs hρi hρp hρm hC₁.le hC₁b hρF
    c hδ hδ' hχs hχc hcχ hzχ hχ hχW
    (fun i => continuous_signalCircleModel (signalPrimeProduct L) γ B d (m i)) hideal

end ThreeTorus
end
end

section

/-! Exact support tracking for the literal passage cutoffs.  The cutoffs are
chosen before the passage integer.  Every retained point is linked to a point
of the old support, so temporal tracking is not inferred from weak convergence.
The integral carrier disappears on the actual temporal circle. -/
noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators
namespace ThreeTorus

/-- Scalar cutoffs with an arbitrarily small stationary-image enlargement,
exactly disjoint angular ranges, and the required identity on the true weights. -/
theorem tracked_frequency_cutoffs {ι : Type*} [Finite ι]
    (m : ι → ℤ) (V : ℝ → ℝ) (K : ι → Set ℝ)
    (hV : Continuous V) (hK : ∀ i, IsCompact (K i))
    (h0 : ∀ i, 0 ∉ (fun x => (m i:ℝ)*V x) '' K i)
    (hsep : Pairwise (fun i j => Disjoint ((fun x => (m i:ℝ)*V x) '' K i)
      ((fun x => (m j:ℝ)*V x) '' K j)))
    {η : ℝ} (hη : 0 < η) :
    ∃ χ : ι → ℝ → ℝ,
      (∀ i, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (χ i) ∧ HasCompactSupport (χ i) ∧
        χ i 0 = 0 ∧ (∀ s, 0 ≤ χ i s ∧ χ i s ≤ 1) ∧
        (∀ s ∈ (fun x => (m i:ℝ)*V x) '' K i, χ i =ᶠ[𝓝 s] 1) ∧
        (∀ s ∈ tsupport (χ i), ∃ x ∈ K i, |s-(m i:ℝ)*V x| < η) ∧
        ∀ (C : Set ℝ) (A : ℝ → ℂ), support A ⊆ K i →
          ∀ s, stationaryWeight C (fun x => (m i:ℝ)*V x) A s ≠ 0 → χ i s = 1) ∧
      Pairwise (fun i j => Disjoint (tsupport (χ i)) (tsupport (χ j))) := by
  let E i := (fun x => (m i:ℝ)*V x) '' K i
  let O i := Metric.thickening η (E i) ∩ ({0}:Set ℝ)ᶜ
  have hE i : IsCompact (E i) := (hK i).image (continuous_const.mul hV)
  have hO i : IsOpen (O i) := Metric.isOpen_thickening.inter isOpen_compl_singleton
  have hEO i : E i ⊆ O i := fun s hs =>
    ⟨Metric.self_subset_thickening hη _ hs,fun he => h0 i (show 0 ∈ E i from he ▸ hs)⟩
  obtain ⟨χ,hχ,hd⟩ := finite_disjoint_frequency_cutoffs E O hE hO hEO hsep
  refine ⟨χ,fun i => ⟨(hχ i).1,(hχ i).2.1,?_,(hχ i).2.2.2.1,
    (hχ i).2.2.2.2,?_,?_⟩,hd⟩
  · by_contra hz
    exact ((hχ i).2.2.1 (subset_tsupport (χ i) hz)).2 rfl
  · intro s hs
    obtain ⟨z,⟨x,hx,rfl⟩,hz⟩ := Metric.mem_thickening_iff.mp (((hχ i).2.2.1 hs).1)
    exact ⟨x,hx,by simpa only [Real.dist_eq] using hz⟩
  · intro C A hA s hs
    exact ((hχ i).2.2.2.2 s (stationaryWeight_support_subset hA hs)).self_of_nhds

lemma circle_dist_le_real (x y : ℝ) :
    dist (x:UnitAddCircle) (y:UnitAddCircle) ≤ |x-y| := by
  rw [dist_eq_norm,← AddCircle.coe_sub]
  exact QuotientAddGroup.norm_mk_le_norm

lemma integral_carrier_circle (m c : ℤ) (v : ℝ) :
    ((m:ℝ)*((c:ℝ)+v):UnitAddCircle) = ((m:ℝ)*v:UnitAddCircle) := by
  rw [mul_add,AddCircle.coe_add]
  have he : ((m:ℝ)*(c:ℝ):UnitAddCircle) = 0 := by
    rw [← Int.cast_mul]
    exact (AddCircle.coe_eq_zero_iff 1).mpr ⟨m*c,by simp⟩
  rw [he,zero_add]

/-- The temporal displacement uses the SAME old support point as the index
location.  A large jitter changes only the final lower bound on `n`. -/
lemma passage_temporal_drift {s v J η : ℝ} {m c : ℤ} {n : ℕ}
    (hn : 0 < n) (hs : |s-(m:ℝ)*((c:ℝ)+v)| ≤ η) :
    dist ((s+s*J/n:ℝ):UnitAddCircle) ((m:ℝ)*v:UnitAddCircle) ≤
      η+|s| *|J|/n := by
  rw [← integral_carrier_circle m c v]
  apply (circle_dist_le_real _ _).trans
  calc
    |s+s*J/n-(m:ℝ)*((c:ℝ)+v)| = |(s-(m:ℝ)*((c:ℝ)+v))+s*J/n| := by congr 1; ring
    _ ≤ |s-(m:ℝ)*((c:ℝ)+v)|+|s*J/n| := abs_add_le _ _
    _ ≤ η+|s| *|J|/n := by
      rw [abs_div,abs_mul,abs_of_pos (show (0:ℝ)<n by exact_mod_cast hn)]
      exact add_le_add hs le_rfl

lemma passage_index_drift {s v c B D P η : ℝ} {m : ℤ}
    (hc : 0 < c) (hB : 0 < B) (hD : |(m:ℝ)/B| ≤ D) (hP : |v| ≤ P)
    (hs : |s-(m:ℝ)*(c+v)| ≤ η) :
    |s/(c*B)-(m:ℝ)/B| ≤ D*P/c+η/(c*B) := by
  have hBn : B ≠ 0 := ne_of_gt hB
  have hcn : c ≠ 0 := ne_of_gt hc
  have he : s/(c*B)-(m:ℝ)/B = ((m:ℝ)/B)*v/c+(s-(m:ℝ)*(c+v))/(c*B) := by
    field_simp
    ring
  have hPn : 0 ≤ P := (abs_nonneg _).trans hP
  rw [he]
  calc
    _ ≤ |((m:ℝ)/B)*v/c|+|(s-(m:ℝ)*(c+v))/(c*B)| := abs_add_le _ _
    _ = |(m:ℝ)/B| *|v|/c+|s-(m:ℝ)*(c+v)|/(c*B) := by
      simp only [abs_div,abs_mul,abs_of_pos hc,abs_of_pos hB]
    _ ≤ D*P/c+η/(c*B) := add_le_add
      (div_le_div_of_nonneg_right (mul_le_mul hD hP (abs_nonneg _) ((abs_nonneg _).trans hD)) hc.le)
      (div_le_div_of_nonneg_right hs (mul_pos hc hB).le)

lemma passage_retained_size {s v c P η : ℝ} {m : ℤ}
    (hc : 0 ≤ c) (hP : |v| ≤ P) (hs : |s-(m:ℝ)*(c+v)| ≤ η) :
    |s| ≤ |(m:ℝ)| *(c+P)+η := by
  calc
    |s| = |(m:ℝ)*(c+v)+(s-(m:ℝ)*(c+v))| := by congr 1; ring
    _ ≤ |(m:ℝ)*(c+v)|+|s-(m:ℝ)*(c+v)| := abs_add_le _ _
    _ ≤ |(m:ℝ)| *(c+P)+η := by
      apply add_le_add _ hs
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left ((abs_add_le c v).trans (by rw [abs_of_nonneg hc]; linarith))
        (abs_nonneg _)

end ThreeTorus
end
end

end OAI
end

section
-- module Solutions.OAIQ13_TT.ThreeTorus_PacketStates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Closed finite packet states, canonical densities, residue reindexing, anchors, reflection, clipping, and state tracking. -/

section

/-! Concrete finite-packet input data and the support bookkeeping used by
iteration. Field regularity is inherited from literal amplitudes. -/
noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators
namespace ThreeTorus

namespace PassagePackets
variable {ι : Type*} (F : PassagePackets ι)

lemma core_subset (i : ι) : F.core i ⊆ Icc F.l F.u :=
  closure_minimal ((F.support_lift i 0).trans Ioc_subset_Icc_self) isClosed_Icc

lemma core_compact (i : ι) : IsCompact (F.core i) :=
  isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) (F.core_subset i)

lemma support_subset_core (hmod : F.SpareIndependent) (i : ι) (a : UnitAddCircle) :
    support (F.A₀ i a) ⊆ F.core i := by
  intro x hx
  apply subset_tsupport _
  intro hz
  apply hx
  apply norm_eq_zero.mp
  rw [hmod.1 i a x,hz,norm_zero]

lemma amplitude_bound [Finite ι] : ∃ B : ℝ, 0 ≤ B ∧ ∀ i p, ‖F.A i p‖^2 ≤ B := by
  classical
  have hb i := (isCompact_range ((F.continuous_amplitude i).norm.pow 2)).isBounded.exists_norm_le
  choose B hB using hb
  obtain ⟨C,hC⟩ := (Set.finite_range B).isCompact.isBounded.exists_norm_le
  refine ⟨max C 0,le_max_right _ _,fun i p => ?_⟩
  have h₁ := hB i _ (mem_range_self p)
  have h₂ := hC _ (mem_range_self i)
  exact (le_abs_self _).trans (h₁.trans ((le_abs_self _).trans (h₂.trans (le_max_left _ _))))

lemma carrier_spare (c : ℤ) (hmod : F.SpareIndependent) :
    (F.carrier c).SpareIndependent := hmod

lemma carrier_circle (c : ℤ) (x : ℝ) :
    ((F.carrier c).V x:UnitAddCircle) = (F.V x:UnitAddCircle) := by
  change (((c:ℝ)+F.V x:ℝ):UnitAddCircle) = _
  rw [AddCircle.coe_add]
  have hc : ((c:ℝ):UnitAddCircle) = 0 :=
    (AddCircle.coe_eq_zero_iff 1).mpr ⟨c,by simp⟩
  rw [hc,zero_add]

end PassagePackets
end ThreeTorus
end
end

section

/-! Canonical smooth density of a literal passage-state packet.  These are
computed from the actual amplitude and speed; no spectral property is a field. -/
noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators
namespace ThreeTorus

lemma continuous_density_unique {p q : UnitAddCircle → ℝ}
    (hp : Continuous p) (hq : Continuous q) (hp0 : ∀ z, 0 ≤ p z) (hq0 : ∀ z, 0 ≤ q z)
    (he : AddCircle.haarAddCircle.withDensity (fun z => ENNReal.ofReal (p z)) =
      AddCircle.haarAddCircle.withDensity (fun z => ENNReal.ofReal (q z))) : p = q := by
  apply (Continuous.ae_eq_iff_eq AddCircle.haarAddCircle hp hq).mp
  have hh := (withDensity_eq_iff_of_sigmaFinite
    hp.measurable.ennreal_ofReal.aemeasurable hq.measurable.ennreal_ofReal.aemeasurable).mp he
  filter_upwards [hh] with z hz
  have hh := congrArg ENNReal.toReal hz
  simpa only [ENNReal.toReal_ofReal (hp0 z), ENNReal.toReal_ofReal (hq0 z)] using hh

lemma foldCircleDensity_finsetSum_eq {ι : Type*} (S : Finset ι) (q : ι → ℝ → ℝ)
    (hq : ∀ i ∈ S, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (q i))
    (hc : ∀ i ∈ S, HasCompactSupport (q i)) :
    foldCircleDensity (fun x => ∑ i ∈ S, q i x) =
      fun z => ∑ i ∈ S, foldCircleDensity (q i) z := by
  have hqS : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x => ∑ i ∈ S, q i x) := ContDiff.sum hq
  have hcS : HasCompactSupport (fun x => ∑ i ∈ S, q i x) := by
    convert HasCompactSupport.finset_sum hc using 1
    all_goals try with_reducible_and_instances rfl
    funext point
    simp only [Finset.sum_apply]
  apply (Continuous.ae_eq_iff_eq AddCircle.haarAddCircle
    (continuous_of_continuous_lift (foldCircleDensity_smooth_lift hqS hcS).continuous)
    (continuous_finsetSum _ (fun i hi => continuous_of_continuous_lift
      (foldCircleDensity_smooth_lift (hq i hi) (hc i hi)).continuous))).mp
  exact foldCircleDensity_finsetSum_ae S q
    (fun i hi => (hq i hi).continuous.measurable)
    (fun i hi => (hq i hi).continuous.integrable_of_hasCompactSupport (hc i hi))

namespace PassagePackets
variable {ι : Type*} (F : PassagePackets ι)

lemma weight_nonneg (i : ι) (s : ℝ) : 0 ≤ F.weight i s :=
  branchDensity_nonneg (fun _ => sq_nonneg _) s

lemma density_nonneg (i : ι) (z : UnitAddCircle) : 0 ≤ F.density i z :=
  foldCircleDensity_nonneg (F.weight_nonneg i) z

lemma smooth_zero_lift (i : ι) : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (F.A₀ i 0) := by
  simpa only [Function.comp_def, AddCircle.coe_zero] using
    (F.smooth_lift i).comp (show ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x : ℝ => (x,(0:ℝ))) from contDiff_id.prodMk contDiff_const)

lemma weight_regular (i : ι) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (F.weight i) ∧ HasCompactSupport (F.weight i) := by
  let q := fun x => ‖F.A₀ i 0 x‖^2
  have hqs : tsupport q ⊆ F.core i := by
    apply closure_mono
    intro x hx hz
    exact hx (by simp [q,hz])
  have hqc : HasCompactSupport q := (F.core_compact i).of_isClosed_subset isClosed_closure hqs
  have hs : tsupport q ⊆ Ioo (F.l-F.R) (F.u+F.R) := by
    intro x hx
    have hh := F.core_subset i (hqs hx)
    constructor <;> linarith [F.Rpos,hh.1,hh.2]
  have has : support (F.A₀ i 0) ⊆ Ioo (F.l-F.R) (F.u+F.R) := by
    intro x hx
    have hh := F.support_lift i 0 hx
    constructor <;> linarith [F.Rpos,hh.1,hh.2]
  have hb := scaled_speed_good_branch (F.nonzero i) F.Rpos F.smooth_speed F.positive_deriv
  have he := stationaryWeight_change_branch Ioo_subset_Icc_self hb.1 has
  change ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
    (stationaryWeight _ _ _) ∧ HasCompactSupport (stationaryWeight _ _ _)
  rw [he]
  exact ⟨branchDensity_smooth (contDiff_const.mul F.smooth_speed) isOpen_Ioo
    (hb.1.mono Ioo_subset_Icc_self) hb.2 ((F.smooth_zero_lift i).norm_sq (𝕜 := ℂ)) hqc hs,
    branchDensity_compact (continuous_const.mul F.smooth_speed.continuous) hqc⟩

lemma density_smooth (i : ι) : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
    (fun x : ℝ => F.density i (x:UnitAddCircle)) :=
  foldCircleDensity_smooth_lift (F.weight_regular i).1 (F.weight_regular i).2

lemma density_continuous (i : ι) : Continuous (F.density i) :=
  continuous_of_continuous_lift (F.density_smooth i).continuous

lemma speed_continuous : Continuous F.periodic.lift := by
  apply Continuous.quotient_lift
  exact F.smooth_speed.continuous

/-- The canonical density is the spectral measure of the actual angular packet. -/
theorem density_spectral (hmod : F.SpareIndependent) (i : ι) :
    packetSpectralMeasure (fun u => (F.periodic.lift u:UnitAddCircle)) (F.m i) (F.A i) =
      AddCircle.haarAddCircle.withDensity (fun z => ENNReal.ofReal (F.density i z)) := by
  have hb := scaled_speed_good_branch (F.nonzero i) F.Rpos F.smooth_speed F.positive_deriv
  have hs : support (F.A₀ i 0) ⊆ Ioo (F.l-F.R) (F.u+F.R) := by
    intro x hx
    have hh := F.support_lift i 0 hx
    constructor <;> linarith [F.Rpos,hh.1,hh.2]
  have he := oldPacket_spectralDensity_of_modulus (m := F.m i) (c := 0) (v := F.periodic.lift)
    (F.continuous_amplitude i) (F.smooth_zero_lift i).continuous (hmod.2 i)
    (F.lift_matches i 0) ((F.support_lift i 0).trans (by
      intro x hx; exact ⟨lt_of_le_of_lt F.lo hx.1, hx.2.trans F.uo⟩)) hs
    F.speed_continuous.measurable F.smooth_speed (fun _ _ => rfl)
    isOpen_Ioo Ioo_subset_Icc_self hb.1 hb.2
  simpa only [Int.cast_zero,sub_zero,density,weight] using he

lemma density_carrier (hmod : F.SpareIndependent) (c : ℤ) (i : ι) :
    (F.carrier c).density i = F.density i := by
  apply continuous_density_unique ((F.carrier c).density_continuous i) (F.density_continuous i)
    ((F.carrier c).density_nonneg i) (F.density_nonneg i)
  rw [← (F.carrier c).density_spectral (F.carrier_spare c hmod) i,← F.density_spectral hmod i]
  congr 1
  funext z
  obtain ⟨x,rfl⟩ := Quotient.mk_surjective z
  exact F.carrier_circle c x

end PassagePackets
end ThreeTorus
end
end

section

/-! Exact identification of the canonical density of an iterated packet state
with the literal finite density already controlled by the passage estimates. -/
noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators
namespace ThreeTorus

lemma exactRetainedPacketDensity_nonneg (I : Set ℝ) (J : ℝ → ℝ) (ψ : UnitAddCircle → ℝ)
    (χ : ℝ → UnitAddCircle → ℝ) (m : ℤ) (H : ℕ → UnitAddCircle → UnitAddCircle)
    (A : UnitAddCircle × UnitAddCircle → ℂ) (S : Finset ℤ) (n : ℕ) (z : UnitAddCircle) :
    0 ≤ exactRetainedPacketDensity I J ψ χ m H A S n z := by
  apply foldCircleDensity_nonneg
  intro t
  apply Finset.sum_nonneg
  intro j _hj
  exact unfoldedModeDensity_nonneg
    (circleDensityLift_nonneg (retainedCircleWeight_nonneg ψ χ _ n j) 0) (Nat.cast_nonneg n) j t

lemma exactRetainedPacketDensity_singleton (I : Set ℝ) (J : ℝ → ℝ) (ψ : UnitAddCircle → ℝ)
    (χ : ℝ → UnitAddCircle → ℝ) (m : ℤ) (H : ℕ → UnitAddCircle → UnitAddCircle)
    (A : UnitAddCircle × UnitAddCircle → ℂ) (j : ℤ) (n : ℕ) :
    exactRetainedPacketDensity I J ψ χ m H A {j} n =
      foldCircleDensity (unfoldedModeDensity I J (invFunOn J I) (deriv J)
        (circleDensityLift 0 (retainedCircleWeight ψ χ
          (fun n j => exactPassageCoeff m (H n) A j) n j)) n j) := by
  simp only [exactRetainedPacketDensity,Finset.sum_singleton]

lemma exactRetainedPacketDensity_sum_singletons
    {I : Set ℝ} {J : ℝ → ℝ} {ψ : UnitAddCircle → ℝ} {ψ₀ : ℝ → ℝ}
    {χ : ℝ → UnitAddCircle → ℝ} {m : ℤ}
    {H : ℕ → UnitAddCircle → UnitAddCircle} {Hl : ℕ → ℝ → ℝ}
    {A : UnitAddCircle × UnitAddCircle → ℂ} {S : Finset ℤ} {n : ℕ}
    (hJ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) J) (hIo : IsOpen I)
    (hinj : InjOn J I) (hd : ∀ x ∈ I, deriv J x ≠ 0)
    (hψ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ₀) (hc : HasCompactSupport ψ₀)
    (he : ∀ x ∈ Ioc (0:ℝ) (0+1), ψ (x:UnitAddCircle) = ψ₀ x)
    (hs : tsupport ψ₀ ⊆ Ioc (0:ℝ) (0+1) ∩ I)
    (hχ : CylinderSmooth χ.uncurry)
    (hHl : ∀ n, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Hl n))
    (hH : ∀ n (t : ℝ), H n (t:UnitAddCircle) = (Hl n t:UnitAddCircle))
    (hA : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × ℝ => A (p.1,p.2)))
    (hn : 0 < n) (hS : ∀ j ∈ S, j ≠ 0) :
    exactRetainedPacketDensity I J ψ χ m H A S n =
      fun z => ∑ j ∈ S, exactRetainedPacketDensity I J ψ χ m H A {j} n z := by
  unfold exactRetainedPacketDensity
  simp only [Finset.sum_singleton]
  simp_rw [retainedWeight_lift_eq χ m H A n _ he (hs.trans inter_subset_left)]
  apply foldCircleDensity_finsetSum_eq
  · intro j _hj
    exact unfoldedModeDensity_smooth hJ hIo hinj hd
      (realRetainedWeight_smooth hψ hχ hHl hH hA n j)
      (realRetainedWeight_compact hc χ m H A n j)
      ((realRetainedWeight_support ψ₀ χ m H A n j).trans (hs.trans inter_subset_right)) n j
  · intro j hj
    exact unfoldedModeDensity_compact hJ.continuous
      (realRetainedWeight_compact hc χ m H A n j)
      (by exact_mod_cast hn.ne') (by exact_mod_cast hS j hj)

lemma exactRetainedPacketDensity_filtered_singletons
    {I : Set ℝ} {J : ℝ → ℝ} {ψ : UnitAddCircle → ℝ} {ψ₀ : ℝ → ℝ}
    {χ : ℝ → UnitAddCircle → ℝ} {m : ℤ}
    {H : ℕ → UnitAddCircle → UnitAddCircle} {Hl : ℕ → ℝ → ℝ}
    {A : UnitAddCircle × UnitAddCircle → ℂ} {S : Finset ℤ} {n : ℕ}
    (hJ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) J) (hIo : IsOpen I)
    (hinj : InjOn J I) (hd : ∀ x ∈ I, deriv J x ≠ 0)
    (hψ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ₀) (hc : HasCompactSupport ψ₀)
    (he : ∀ x ∈ Ioc (0:ℝ) (0+1), ψ (x:UnitAddCircle) = ψ₀ x)
    (hs : tsupport ψ₀ ⊆ Ioc (0:ℝ) (0+1) ∩ I)
    (hχ : CylinderSmooth χ.uncurry)
    (hHl : ∀ n, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Hl n))
    (hH : ∀ n (t : ℝ), H n (t:UnitAddCircle) = (Hl n t:UnitAddCircle))
    (hA : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × ℝ => A (p.1,p.2)))
    (hn : 0 < n) (hS : ∀ j ∈ S, j ≠ 0) (E : ℤ → Prop) [DecidablePred E] :
    exactRetainedPacketDensity I J ψ χ m H A (S.filter E) n =
      fun z => ∑ j : ↥S, if E j.val then
        exactRetainedPacketDensity I J ψ χ m H A {j.val} n z else 0 := by
  rw [exactRetainedPacketDensity_sum_singletons hJ hIo hinj hd hψ hc he hs hχ hHl hH hA hn
    (fun j hj => hS j (Finset.mem_filter.mp hj).1)]
  funext z
  rw [Finset.sum_filter]
  exact (Finset.sum_coe_sort S (fun j => if E j then
    exactRetainedPacketDensity I J ψ χ m H A {j} n z else 0)).symm

/-- Pointwise, not just a.e., identity of a literal output packet's canonical
density. The hypotheses below are only smooth lifts and the displayed literal
coefficient/speed identities; no new spectral law is assumed. -/
theorem literal_packet_canonical_density {ι : Type*} (F : PassagePackets ι)
    (hmod : F.SpareIndependent) (i : ι)
    {I : Set ℝ} {J : UnitAddCircle → ℝ} {J₀ : ℝ → ℝ}
    {ψ : UnitAddCircle → ℝ} {ψ₀ : ℝ → ℝ} {χ : ℝ → UnitAddCircle → ℝ}
    {m j : ℤ} {n : ℕ} {H : ℕ → UnitAddCircle → UnitAddCircle} {Hl : ℕ → ℝ → ℝ}
    {A : UnitAddCircle × UnitAddCircle → ℂ}
    (hm : F.m i = j) (hamp : F.A i = retainedAmplitude ψ χ m H A n j)
    (hspeed : ∀ a, (F.periodic.lift a:UnitAddCircle) = (((1+J a/n)/n:ℝ):UnitAddCircle))
    (hJc : Continuous J) (hJ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) J₀)
    (hJe : ∀ x ∈ I, J (x:UnitAddCircle) = J₀ x)
    (hIo : IsOpen I) (hinj : InjOn J₀ I) (hd : ∀ x ∈ I, deriv J₀ x ≠ 0)
    (hψc : Continuous ψ) (hψ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ₀)
    (hc : HasCompactSupport ψ₀)
    (he : ∀ x ∈ Ioc (0:ℝ) (0+1), ψ (x:UnitAddCircle) = ψ₀ x)
    (hs : tsupport ψ₀ ⊆ Ioc (0:ℝ) (0+1) ∩ I)
    (hχc : Continuous χ.uncurry) (hχ : CylinderSmooth χ.uncurry)
    (hHc : ∀ n, Continuous (H n))
    (hHl : ∀ n, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Hl n))
    (hH : ∀ n (t : ℝ), H n (t:UnitAddCircle) = (Hl n t:UnitAddCircle))
    (hAc : Continuous A)
    (hA : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × ℝ => A (p.1,p.2)))
    (hn : 0 < n) :
    F.density i = exactRetainedPacketDensity I J₀ ψ χ m H A {j} n := by
  have hj : j ≠ 0 := hm ▸ F.nonzero i
  have hps := exactRetainedPacketDensity_smooth_lift (m := m) hJ hIo hinj hd hψ hc he hs hχ hHl hH hA hn
    (S := {j}) (fun k hk => by simpa only [Finset.mem_singleton.mp hk] using hj)
  apply continuous_density_unique (F.density_continuous i)
    (continuous_of_continuous_lift hps.continuous) (F.density_nonneg i)
    (exactRetainedPacketDensity_nonneg I J₀ ψ χ m H A {j} n)
  rw [← F.density_spectral hmod i,hm,hamp,show
    (fun a => (F.periodic.lift a:UnitAddCircle)) =
      (fun a => (((1+J a/n)/n:ℝ):UnitAddCircle)) from funext hspeed,
    exactRetainedPacketDensity_singleton]
  exact retainedAmplitude_spectralDensity hψc hχc hHc hAc
    (fun x hx hp => (hs (subset_tsupport ψ₀ (by rwa [he x hx] at hp))).2)
    hJc.measurable hJ hJe hIo hinj hd hn hj

end ThreeTorus
end
end

section

/-! Conjugation symmetry survives the literal retained coefficients. Smooth
cutoffs can be made reflection-compatible by a product, without losing the
already constructed exact disjointness of their supports. -/
noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ComplexConjugate
namespace ThreeTorus

lemma retainedAmplitude_reflect (ψ : UnitAddCircle → ℝ) (χ : ℝ → UnitAddCircle → ℝ)
    (m : ℤ) (H : ℕ → UnitAddCircle → UnitAddCircle)
    (A : UnitAddCircle × UnitAddCircle → ℂ) (n : ℕ) (j : ℤ) (p : UnitAddCircle × UnitAddCircle) :
    retainedAmplitude ψ (fun s a => χ (-s) a) (-m) H (fun x => conj (A x)) n j p =
      conj (retainedAmplitude ψ χ m H A n (-j) p) := by
  simp only [retainedAmplitude,exactPassageCoeff_neg,Int.cast_neg,neg_div,map_mul,
    Complex.conj_ofReal,fourier_neg]

end ThreeTorus
end
end

section

/-! Actual conjugation data, invariant cutoff choices, and canonical spectral
reflection. No symmetry of an approximate model is substituted for reality of
the packets. -/
noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ComplexConjugate
namespace ThreeTorus
namespace PassagePackets
variable {ι : Type*} (F : PassagePackets ι)

variable {F}

lemma Reflection.involutive {τ : ι → ι} (h : F.Reflection τ) (hi : Injective F.m) :
    Involutive τ := fun i => hi (by rw [h.index,h.index,neg_neg])

lemma Reflection.core {τ : ι → ι} (h : F.Reflection τ) (i : ι) :
    F.core (τ i) = F.core i := by
  unfold PassagePackets.core tsupport
  congr 1
  ext x
  simp only [mem_support,h.lift,map_ne_zero]

end PassagePackets

/-- Reflection-compatible, exactly disjoint cutoffs with the full tracking
and stationary identity used by the actual neutral and signal producers. -/
theorem tracked_symmetric_cutoffs_fixed_carrier {ι : Type*} [Finite ι]
    (F : PassagePackets ι) (hi : Injective F.m) (hmod : F.SpareIndependent)
    {τ : ι → ι} (hr : F.Reflection τ) {c : ℕ}
    (hc : 0 < c ∧ (∀ i x, (F.m i:ℝ)*((c:ℝ)+F.periodic.lift x) ≠ 0) ∧
      ∀ i j x y, (F.m i:ℝ)*((c:ℝ)+F.periodic.lift x) =
        (F.m j:ℝ)*((c:ℝ)+F.periodic.lift y) → F.m i = F.m j)
    {η : ℝ} (hη : 0 < η) :
    0 < c ∧ ∃ χ : ι → ℝ → ℝ,
      (∀ i, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (χ i) ∧ HasCompactSupport (χ i) ∧
        χ i 0 = 0 ∧ (∀ s, 0 ≤ χ i s ∧ χ i s ≤ 1) ∧
        (∀ s ∈ tsupport (χ i), ∃ x ∈ F.core i, |s-(F.m i:ℝ)*((c:ℝ)+F.V x)| < η) ∧
        ∀ (C : Set ℝ) a s, stationaryWeight C
          (fun x => (F.m i:ℝ)*((c:ℝ)+F.V x)) (F.A₀ i a) s ≠ 0 → χ i s = 1) ∧
      Pairwise (fun i j => Disjoint (tsupport (χ i)) (tsupport (χ j))) ∧
      (∀ i s, χ (τ i) s = χ i (-s)) := by
  have hzero i : 0 ∉ (fun x => (F.m i:ℝ)*((c:ℝ)+F.V x)) '' F.core i := by
    rintro ⟨x,_hx,he⟩
    exact hc.2.1 i (x:UnitAddCircle) he
  have hsep : Pairwise (fun i j => Disjoint
      ((fun x => (F.m i:ℝ)*((c:ℝ)+F.V x)) '' F.core i)
      ((fun x => (F.m j:ℝ)*((c:ℝ)+F.V x)) '' F.core j)) := by
    intro i j hij
    rw [Set.disjoint_left]
    rintro s ⟨x,_hx,rfl⟩ ⟨y,_hy,he⟩
    exact hij (hi (hc.2.2 i j (x:UnitAddCircle) (y:UnitAddCircle) he.symm))
  obtain ⟨χ,hχ,hd⟩ := tracked_frequency_cutoffs F.m (fun x => (c:ℝ)+F.V x) F.core
    (continuous_const.add F.smooth_speed.continuous) F.core_compact hzero hsep hη
  let ψ : ι → ℝ → ℝ := fun i s => χ i s*χ (τ i) (-s)
  have hsub i : tsupport (ψ i) ⊆ tsupport (χ i) := tsupport_mul_subset_left
  refine ⟨hc.1,ψ,fun i => ⟨(hχ i).1.mul ((hχ (τ i)).1.comp contDiff_neg),
    (hχ i).2.1.mul_right,?_,?_,?_,?_⟩,?_,?_⟩
  · simp only [ψ,(hχ i).2.2.1,zero_mul]
  · intro s
    exact ⟨mul_nonneg ((hχ i).2.2.2.1 s).1 ((hχ (τ i)).2.2.2.1 (-s)).1,
      (mul_le_mul ((hχ i).2.2.2.1 s).2 ((hχ (τ i)).2.2.2.1 (-s)).2
        ((hχ (τ i)).2.2.2.1 (-s)).1 zero_le_one).trans (by norm_num)⟩
  · intro s hs
    exact (hχ i).2.2.2.2.2.1 s (hsub i hs)
  · intro C a s hs
    have hsi := stationaryWeight_support_subset (F.support_subset_core hmod i a) hs
    obtain ⟨x,hx,hxs⟩ := hsi
    have hre : -s ∈ (fun x => (F.m (τ i):ℝ)*((c:ℝ)+F.V x)) '' F.core (τ i) := by
      refine ⟨x,(hr.core i).symm ▸ hx,?_⟩
      simp only [hr.index,Int.cast_neg,neg_mul,hxs]
    have hleft := (hχ i).2.2.2.2.2.2 C (F.A₀ i a) (F.support_subset_core hmod i a) s hs
    have hright := ((hχ (τ i)).2.2.2.2.1 (-s) hre).self_of_nhds
    change χ (τ i) (-s) = 1 at hright
    simp only [ψ,hleft,hright,one_mul]
  · intro i j hij
    exact (hd hij).mono (hsub i) (hsub j)
  · intro i s
    simp only [ψ,hr.involutive hi i,neg_neg,mul_comm]

end ThreeTorus
end
end

section

noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators
namespace ThreeTorus
namespace PassagePackets
variable {ι : Type*} (F : PassagePackets ι)

lemma weight_integrable (i : ι) : Integrable (F.weight i) :=
  (F.weight_regular i).1.continuous.integrable_of_hasCompactSupport (F.weight_regular i).2

lemma density_mass (i : ι) :
    (∫ z, F.density i z ∂AddCircle.haarAddCircle) = ∫ s, F.weight i s :=
  integral_foldCircleDensity (F.weight_regular i).1.continuous.measurable (F.weight_integrable i)

lemma weight_mass_carrier (hmod : F.SpareIndependent) (c : ℤ) (i : ι) :
    (∫ s, (F.carrier c).weight i s) = ∫ s, F.weight i s := by
  rw [← (F.carrier c).density_mass i,F.density_carrier hmod c i,F.density_mass i]

lemma weight_mass_bound [Finite ι] : ∃ B : ℝ, 0 ≤ B ∧ ∀ i, (∫ s, F.weight i s) ≤ B := by
  obtain ⟨B,hB⟩ := (Set.finite_range (fun i => ∫ s, F.weight i s)).isCompact.isBounded.exists_norm_le
  exact ⟨max B 0,le_max_right _ _,fun i => (le_abs_self _).trans
    ((hB _ (mem_range_self i)).trans (le_max_left _ _))⟩

end PassagePackets
end ThreeTorus
end
end

section

/-! Support tracking for the actual next packets. Canonical density support
is linked to a genuine old-amplitude point; the same point controls both
normalized angular indices and temporal frequencies. -/
noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators
namespace ThreeTorus

namespace PassagePackets
variable {ι : Type*} (F : PassagePackets ι)

lemma speed_bound : ∃ P : ℝ, 0 ≤ P ∧ ∀ x, |F.V x| ≤ P := by
  obtain ⟨P,hP⟩ := (isCompact_range F.speed_continuous).isBounded.exists_norm_le
  exact ⟨max P 0,le_max_right _ _,fun x =>
    (hP _ (mem_range_self (x:UnitAddCircle))).trans (le_max_left _ _)⟩

lemma angular_bound [Finite ι] : ∃ M : ℝ, 0 ≤ M ∧ ∀ i, |(F.m i:ℝ)| ≤ M := by
  obtain ⟨M,hM⟩ := (Set.finite_range (fun i => (F.m i:ℝ))).isCompact.isBounded.exists_norm_le
  exact ⟨max M 0,le_max_right _ _,fun i => (hM _ (mem_range_self i)).trans (le_max_left _ _)⟩

end PassagePackets

lemma periodic_real_bound {J : ℝ → ℝ} (hs : Continuous J) (hp : Periodic J 1) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x, |J x| ≤ B := by
  have hc : Continuous hp.lift := by
    apply Continuous.quotient_lift
    exact hs
  obtain ⟨B,hB⟩ := (isCompact_range hc).isBounded.exists_norm_le
  exact ⟨max B 0,le_max_right _ _,fun x =>
    (hB _ (mem_range_self (x:UnitAddCircle))).trans (le_max_left _ _)⟩

/-- The tracked frequency cutoff already controls every retained index, including
zero-amplitude packets. The temporal inequality holds for every new speed point. -/
theorem literal_output_tracking {ι : Type*} {F : PassagePackets ι}
    {S : ι → Finset ℤ} {G : PassagePackets (PassageOutputIndex S)}
    {χ : ι → ℝ → ℝ} {c n : ℕ} {B D P M Q τ : ℝ} {J : ℝ → ℝ}
    (hc : 0 < c) (hn : 0 < n) (hB : 0 < B)
    (hD : ∀ i, |(F.m i:ℝ)/B| ≤ D) (hP : ∀ x, |F.V x| ≤ P)
    (hM : ∀ i, |(F.m i:ℝ)| ≤ M) (hQ : ∀ x, |J x| ≤ Q)
    (hS : ∀ i j, j ∈ S i → χ i ((j:ℝ)/n) ≠ 0)
    (hχ : ∀ i s, s ∈ tsupport (χ i) → ∃ x ∈ F.core i,
      |s-(F.m i:ℝ)*((c:ℝ)+F.V x)| < τ)
    (hm : ∀ i, G.m i = i.2.val) (hV : G.V = fun x => (1+J x/n)/n) :
    ∀ i, ∃ x ∈ F.core i.1,
      |(G.m i:ℝ)/((n:ℝ)*c*B)-(F.m i.1:ℝ)/B| ≤ D*P/c+τ/((c:ℝ)*B) ∧
      ∀ y, dist ((G.m i:ℝ)*G.V y:UnitAddCircle)
        ((F.m i.1:ℝ)*F.V x:UnitAddCircle) ≤ τ+(M*((c:ℝ)+P)+τ)*Q/n := by
  intro i
  obtain ⟨x,hx,htrack⟩ := hχ i.1 _ (subset_tsupport _ (hS i.1 i.2.val i.2.property))
  have hcR : 0 < (c:ℝ) := by exact_mod_cast hc
  have hnR : 0 < (n:ℝ) := by exact_mod_cast hn
  have hP0 : 0 ≤ P := (abs_nonneg _).trans (hP 0)
  have hs := passage_retained_size hcR.le (hP x) htrack.le
  have hsM : |(i.2.val:ℝ)/n| ≤ M*((c:ℝ)+P)+τ := hs.trans (by
    gcongr
    exact hM i.1)
  refine ⟨x,hx,?_,?_⟩
  · rw [hm i]
    have heq : (i.2.val:ℝ)/((n:ℝ)*c*B) = ((i.2.val:ℝ)/n)/((c:ℝ)*B) := by ring
    rw [heq]
    exact passage_index_drift hcR hB (hD i.1) (hP x) htrack.le
  · intro y
    rw [hm i,hV]
    have heq : (i.2.val:ℝ)*((1+J y/n)/n) = (i.2.val:ℝ)/n+((i.2.val:ℝ)/n)*J y/n := by ring
    rw [heq]
    have ht := passage_temporal_drift (J := J y) (c := (c:ℤ)) hn (by
      simpa only [Int.cast_natCast] using htrack.le)
    apply ht.trans
    exact add_le_add le_rfl (div_le_div_of_nonneg_right
      (mul_le_mul hsM (hQ y) (abs_nonneg _) ((abs_nonneg _).trans hsM)) hnR.le)

/-- Large carrier first, small cutoff enlargement second, and final integer
last. The bounded jitter only affects this LAST choice. -/
lemma support_drift_budgets {D P M B e : ℝ} (hB : 0 < B) (he : 0 < e) :
    ∀ᶠ c : ℕ in atTop, 0 < c ∧ ∀ τ : ℝ, 0 < τ → τ < e/2 →
      D*P/c+τ/((c:ℝ)*B) < e ∧
      ∀ Q : ℝ, ∀ᶠ n : ℕ in atTop, 0 < n ∧ τ+(M*((c:ℝ)+P)+τ)*Q/n < e := by
  have hlim : Tendsto (fun c : ℕ => D*P/(c:ℝ)+(e/2)/((c:ℝ)*B)) atTop (𝓝 0) := by
    have hc := tendsto_natCast_atTop_atTop (R := ℝ)
    have h₁ : Tendsto (fun c : ℕ => D*P/(c:ℝ)) atTop (𝓝 0) := tendsto_const_nhds.div_atTop hc
    have h₂ : Tendsto (fun c : ℕ => (e/2)/((c:ℝ)*B)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (hc.atTop_mul_const hB)
    simpa using h₁.add h₂
  filter_upwards [eventually_gt_atTop (0:ℕ),hlim.eventually (gt_mem_nhds he)] with c hc hh
  refine ⟨hc,fun τ _hτ hτe => ⟨?_,?_⟩⟩
  · have hcR : 0 < (c:ℝ) := by exact_mod_cast hc
    exact (add_le_add_right (div_le_div_of_nonneg_right hτe.le (mul_pos hcR hB).le) _).trans_lt hh
  · intro Q
    have hlimn : Tendsto (fun n : ℕ => τ+(M*((c:ℝ)+P)+τ)*Q/(n:ℝ)) atTop (𝓝 τ) := by
      simpa using tendsto_const_nhds.add
        (tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop (R := ℝ)) :
          Tendsto (fun n : ℕ => (M*((c:ℝ)+P)+τ)*Q/(n:ℝ)) atTop (𝓝 0))
    exact (eventually_gt_atTop (0:ℕ)).and (hlimn.eventually (gt_mem_nhds (by linarith)))

end ThreeTorus
end
end

end OAI
end

section
-- module Solutions.OAIQ13_TT.ThreeTorus_TrackedPackets
attribute [-instance] _root_.OAI.ThreeTorus.tripleVolume_regular
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Refresh and residue estimates, physical aggregates, tracked producers, pair/color aggregates, and colored states. -/

section

/-! Physical vectors and spectral densities grouped by their actual source
packet. No spectral data is chosen independently of the literal amplitudes. -/
noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators
namespace ThreeTorus

lemma outputVector_eq_retained {ι : Type*} {S : ι → Finset ℤ}
    (F : PassagePackets ι) (G : PassagePackets (PassageOutputIndex S))
    (ψ : UnitAddCircle → ℝ) (χ : ι → ℝ → UnitAddCircle → ℝ)
    (H : ℕ → UnitAddCircle → UnitAddCircle) (n : ℕ)
    (hm : ∀ i, G.m i = i.2.val)
    (hA : ∀ i, G.A i = retainedAmplitude ψ (χ i.1) (F.m i.1) H (F.A i.1) n i.2.val)
    (i : ι) :
    outputVector G i = retainedPassage (F.m i) (H n) (F.A i) (S i)
      (fun j => χ i ((j:ℝ)/n)) ψ := by
  funext x
  unfold outputVector
  simp_rw [hm,hA]
  exact Finset.sum_coe_sort (S i) (fun j =>
    packet j (retainedAmplitude ψ (χ i) (F.m i) H (F.A i) n j) x)

end ThreeTorus
end
end

section

/-! A finite colored state and a pair record containing the two ACTUAL
smooth volume-preserving passage families. The existence theorem is derived
from the concrete neutral/signal producers, not supplied as an oracle. -/
noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators
namespace ThreeTorus

attribute [instance] ColoredState.finite

end ThreeTorus
end
end

end OAI
end

section
-- module Solutions.OAIQ13_TT.ThreeTorus_SymmetricPackets
attribute [-instance] _root_.OAI.ThreeTorus.tripleVolume_regular
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Reflected neutral and signal producers, symmetric colors, physical control, and grouped cutoffs. -/

section

/-! The actual retained family, including its real compactly supported lifts,
preserves conjugation, with the literal inherited parent on its finite indices. -/
noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ComplexConjugate
namespace ThreeTorus

lemma retainedRealAmplitude_reflect (ψ : ℝ → ℝ) (χ : ℝ → UnitAddCircle → ℝ)
    (m : ℤ) (H : UnitAddCircle → UnitAddCircle)
    (A : UnitAddCircle × UnitAddCircle → ℂ) (s : ℝ) (j : ℤ) (a : UnitAddCircle) (x : ℝ) :
    retainedRealAmplitude ψ (fun s a => χ (-s) a) (-m) H (fun p => conj (A p)) s j a x =
      conj (retainedRealAmplitude ψ χ m H A (-s) (-j) a x) := by
  simp only [retainedRealAmplitude,retainedRealCore,exactPassageCoeff_neg,
    map_mul,Complex.conj_ofReal,fourier_neg]

lemma literal_output_reflection {ι : Type*} (F : PassagePackets ι)
    {τ : ι → ι} (hr : F.Reflection τ)
    (ψ : UnitAddCircle → ℝ) (ψ₀ : ℝ → ℝ) (χ : ι → ℝ → UnitAddCircle → ℝ)
    (H : ℕ → UnitAddCircle → UnitAddCircle) (n : ℕ) (S : ι → Finset ℤ)
    (hs : ∀ i j, j ∈ S (τ i) ↔ -j ∈ S i)
    (hχ : ∀ i s a, χ (τ i) s a = χ i (-s) a)
    (G : PassagePackets (PassageOutputIndex S))
    (hGm : ∀ i, G.m i = i.2.val)
    (hGA : ∀ i, G.A i = retainedAmplitude ψ (χ i.1) (F.m i.1) H (F.A i.1) n i.2.val)
    (hGA₀ : ∀ i, G.A₀ i = retainedRealAmplitude ψ₀ (χ i.1) (F.m i.1) (H n) (F.A i.1)
      ((i.2.val:ℝ)/n) i.2.val) :
    ∃ τG : PassageOutputIndex S → PassageOutputIndex S,
      (∀ i, (τG i).1 = τ i.1) ∧ G.Reflection τG := by
  let τG := reflectedOutputIndex τ S hs
  have hχ' i : χ (τ i) = fun s a => χ i (-s) a := funext (fun s => funext (hχ i s))
  have hA i : F.A (τ i) = fun p => conj (F.A i p) := funext (hr.amplitude i)
  refine ⟨τG,fun _ => rfl,⟨?_,?_,?_⟩⟩
  · intro i
    simp only [hGm,τG,reflectedOutputIndex]
  · intro i p
    rw [hGA,hGA]
    change retainedAmplitude ψ (χ (τ i.1)) (F.m (τ i.1)) H (F.A (τ i.1)) n (-i.2.val) p = _
    rw [hχ',hr.index,hA,retainedAmplitude_reflect,neg_neg]
  · intro i a x
    rw [hGA₀,hGA₀]
    change retainedRealAmplitude ψ₀ (χ (τ i.1)) (F.m (τ i.1)) (H n) (F.A (τ i.1))
      (((-i.2.val:ℤ):ℝ)/n) (-i.2.val) a x = _
    rw [hχ',hr.index,hA,retainedRealAmplitude_reflect]
    simp only [Int.cast_neg,neg_div,neg_neg]

lemma scalar_exact_indices_reflect {ι : Type*} {τ : ι → ι}
    {χ : ι → ℝ → ℝ} (hχ : ∀ i s, χ (τ i) s = χ i (-s))
    {S : ι → Finset ℤ} {n : ℕ} (he : ∀ i j, j ∈ S i ↔ χ i ((j:ℝ)/n) ≠ 0) :
    ∀ i j, j ∈ S (τ i) ↔ -j ∈ S i := by
  intro i j
  rw [he,he,hχ]
  simp only [Int.cast_neg,neg_div]

end ThreeTorus
end
end

section

/-! Uniform-before-all-future-packet-types signal producer, with actual
conjugate amplitudes and compact lifts preserved, not only model symmetry. -/
noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators
namespace ThreeTorus
universe u

theorem exists_signal_state_reflected_family
    {b D : ℝ} (hb : 0 < b) (hbD : b < D)
    {d : ℝ → ℂ} (hd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) d)
    (hdc : HasCompactSupport d) (hdr : ∀ v, d (-v) = starRingEnd ℂ (d v))
    (hd0 : d 0 = 0) (hds : support d ⊆ Icc (-D) D) :
    ∃ α : ℝ, ∃ L : ℕ, ∃ γ₀ : ℝ,
      0 < α ∧ α < b/2 ∧ 2 ≤ L ∧ D/b < L ∧ 0 < γ₀ ∧
      ∀ γ : ℝ, 0 < γ → γ ≤ γ₀ →
      (∀ v, 2*γ*‖d v‖ ≤ 1/2) ∧
      ∀ (ι : Type u) [Fintype ι], ∀ (F : PassagePackets ι),
      Injective F.m → F.SpareIndependent → ∀ τref : ι → ι, F.Reflection τref → ∀ B : ℝ, 0 < B →
      (∀ i, b ≤ |(F.m i:ℝ)/B|) →
      ∀ ε τ κ : ℝ, 0 < ε → 0 < τ → 0 < κ →
      ∀ᶠ c : ℕ in atTop, 0 < c ∧
      ∃ δ : ℝ, ∃ cut : LawCutoffs δ, ∃ χ : ι → ℝ → ℝ,
      ∃ Δ : ℕ → ℝ, ∃ H : ℕ → UnitAddCircle → UnitAddCircle,
      0 < δ ∧ δ < 1/8 ∧ δ < κ ∧
      (∀ i, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (χ i) ∧ HasCompactSupport (χ i) ∧
        χ i 0 = 0 ∧ (∀ s, 0 ≤ χ i s ∧ χ i s ≤ 1) ∧
        ∀ s ∈ tsupport (χ i), ∃ x ∈ F.core i,
          |s-(F.m i:ℝ)*((c:ℝ)+F.V x)| < τ) ∧
      Pairwise (fun i j => Disjoint (tsupport (χ i)) (tsupport (χ j))) ∧
      (∀ n, 0 < n → |Δ n| ≤ (n:ℝ)⁻¹) ∧ Tendsto Δ atTop (𝓝 0) ∧
      (∀ n, Continuous (H n)) ∧
      (∀ n (x : ℝ), H n (x:UnitAddCircle) =
        ((n:ℝ)*((∫ t in 0..x, (c:ℝ)+F.V t)+Δ n*x):UnitAddCircle)) ∧
      let ρ := signalJitter α γ d (signalPrimeProduct L) B c
      let ψ := neutralCircleCutoff cut
      let J := quantileCircleJitter ρ cut
      let J₀ := lawJitter ρ cut
      let σ := fun (n : ℕ) a => (((1+J a/n)/n:ℝ):UnitAddCircle)
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ρ ∧ Integrable ρ ∧
      (∀ y, 0 < ρ y) ∧ (∫ y, ρ y = 1) ∧
      (∀ n, Smooth (torusPassage (H n) (σ n)) ∧ Smooth (torusPassage (H n) (σ n)).symm ∧
        MeasurePreserving (torusPassage (H n) (σ n)) μ μ) ∧
      (∀ n, 0 < n → ∀ x : Cover,
        torusPassage (H n) (σ n) (project x) =
          project (passageFamily (fun t => (c:ℝ)+F.V t) J₀ 1 ((n:ℝ)⁻¹,Δ n) x) ∧
        (torusPassage (H n) (σ n)).symm (project x) =
          project (passageFamily (fun t => (c:ℝ)+F.V t) J₀ (-1) ((n:ℝ)⁻¹,Δ n) x)) ∧
      (∀ r : ℝ, ∀ K : Set Cover, IsCompact K → ∀ e : ℕ,
        TendstoUniformlyOn
          (fun (n : ℕ) x => iteratedFDeriv ℝ e
            (passageFamily (fun t => (c:ℝ)+F.V t) J₀ r ((n:ℝ)⁻¹,Δ n)) x)
          (fun x => iteratedFDeriv ℝ e (fun y : Cover => ![y 0+r*((c:ℝ)+F.V (y 1)),y 1,y 2]) x)
          atTop K) ∧
      ∃ S : ℕ → ι → Finset ℤ,
        (∀ n, 0 < n → Pairwise (fun i j => Disjoint (S n i) (S n j))) ∧
        (∀ n, 0 < n → ∀ i j, j ∈ S n i ↔ χ i ((j:ℝ)/n) ≠ 0) ∧
        ∀ᶠ n : ℕ in atTop, 0 < n ∧
          (∀ i,
            let f := retainedPassage (F.m i) (H n) (F.A i) (S n i) (fun j _ => χ i ((j:ℝ)/n)) ψ
            let p := exactRetainedPacketDensity (Ioo δ (1-δ)) J₀ ψ (fun s _ => χ i s)
              (F.m i) H (F.A i) (S n i) n
            (∫ x : TripleTorus, ‖packet (F.m i) (F.A i) x-f (passageChart (H n) x)‖^2
              ∂tripleVolume) < ε ∧
            (∫ z, |p z-F.density i z*signalCircleModel (signalPrimeProduct L) γ B d
              (F.m i) ((n:ℤ) • z)| ∂AddCircle.haarAddCircle) < ε ∧
            (∀ k : ℤ, (∫ x : TripleTorus, starRingEnd ℂ (f x)*f (twistIter (σ n) k x) ∂tripleVolume) =
              ∫ z, (p z:ℂ)*fourier k z ∂AddCircle.haarAddCircle)) ∧
          ∃ G : PassagePackets (PassageOutputIndex (S n)),
            Injective G.m ∧ G.SpareIndependent ∧
            G.V = (fun x => (1+J₀ x/n)/n) ∧
            (∀ i, G.m i = i.2.val) ∧
            (∀ i, G.A i = retainedAmplitude ψ (fun s _ => χ i.1 s) (F.m i.1) H (F.A i.1) n i.2.val) ∧
            (∀ i, G.density i = exactRetainedPacketDensity (Ioo δ (1-δ)) J₀ ψ
              (fun s _ => χ i.1 s) (F.m i.1) H (F.A i.1) {i.2.val} n) ∧
            (∀ i (E : ℤ → Prop) [DecidablePred E],
              exactRetainedPacketDensity (Ioo δ (1-δ)) J₀ ψ
                (fun s _ => χ i s) (F.m i) H (F.A i) ((S n i).filter E) n =
              fun z => ∑ j : ↥(S n i), if E j.val then G.density ⟨i,j⟩ z else 0) ∧
            ∃ τG : PassageOutputIndex (S n) → PassageOutputIndex (S n),
              (∀ i, (τG i).1 = τref i.1) ∧ G.Reflection τG ∧ G.GoodArc δ := by
  classical
  obtain ⟨α,L,γ₀,hα,hαb,hL,hLD,hγ₀,hγ⟩ := exists_actual_signal_family hb hbD hd hdc hdr hd0 hds
  refine ⟨α,L,γ₀,hα,hαb,hL,hLD,hγ₀,?_⟩
  intro γ hγp hγs
  obtain ⟨hdb,hsignal⟩ := hγ γ hγp hγs
  refine ⟨hdb,?_⟩
  intro ι inst F hi hmod τref hr B hB hm ε τ κ hε hτ hκ
  obtain ⟨M,hM,hAM⟩ := F.amplitude_bound
  obtain ⟨W,hW,hWM⟩ := F.weight_mass_bound
  let K := M+W+1
  have hK : 0 < K := by dsimp [K]; positivity
  have hMK : M ≤ K := by dsimp [K]; linarith
  have hWK : W ≤ K := by dsimp [K]; linarith
  let ε₀ := ε/(8*K)
  have hε₀ : 0 < ε₀ := div_pos hε (by positivity)
  obtain ⟨δ,hδ,hδall⟩ := exists_between (lt_min (lt_min (by norm_num : (0:ℝ)<1/8)
    (div_pos hε (show 0 < 32*K by positivity))) hκ)
  have hδhi := hδall.trans_le (min_le_left _ _)
  have hδκ := hδall.trans_le (min_le_right _ _)
  have hδ' : δ < 1/8 := hδhi.trans_le (min_le_left _ _)
  have hδK : 32*δ*K < ε := by
    have hh := (lt_div_iff₀ (show 0 < 32*K by positivity)).mp (hδhi.trans_le (min_le_right _ _))
    nlinarith
  have hδM : 8*δ*M < ε/4 := by nlinarith [mul_le_mul_of_nonneg_left hMK hδ.le]
  have hε₀K : ε₀*K = ε/8 := by dsimp [ε₀]; field_simp
  have hcoef : 0 ≤ 4*δ+ε₀ := by positivity
  have hCK : K*(4*δ+ε₀) < ε/4 := by nlinarith
  let cut := lawCutoffs δ hδ hδ'
  have hsignal' := hsignal ι B hB F.m hm F.A F.A₀ F.V F.o F.l F.u F.R
    F.lift_matches F.two F.continuous_lift F.continuous_deriv F.smooth_lift F.support_lift
    F.lo F.uo F.lu F.Rpos F.periodic F.smooth_speed F.positive_deriv
    F.continuous_amplitude F.smooth_amplitude hmod.1 hmod.2 ε₀ hε₀
  filter_upwards [eventually_integral_speed_separation F.m F.periodic.lift F.nonzero F.speed_continuous,hsignal'] with c hc hs
  obtain ⟨hcp,χ,hχ,hdisj,hχsym⟩ := tracked_symmetric_cutoffs_fixed_carrier F hi hmod hr hc hτ
  let Fc := F.carrier (c:ℤ)
  let X : ι → ℝ → UnitAddCircle → ℝ := fun i s _ => χ i s
  have hXs i : CylinderSmooth (X i).uncurry := by
    change ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × ℝ => χ i p.1)
    exact (hχ i).1.comp contDiff_fst
  have hXc i : Continuous (X i).uncurry := (hχ i).1.continuous.comp continuous_fst
  have hXcompact i : HasCompactSupport (X i).uncurry := compactSupport_frequency_cylinder (hχ i).2.1
  have hXzero i (a : UnitAddCircle) : X i 0 a = 0 := (hχ i).2.2.1
  have hXbound i s (a : UnitAddCircle) : 0 ≤ X i s a ∧ X i s a ≤ 1 := (hχ i).2.2.2.1 s
  have hXW i s a : stationaryWeight (Icc (F.l-F.R) (F.u+F.R))
      (fun x => (F.m i:ℝ)*((c:ℝ)+F.V x)) (F.A₀ i a) s ≠ 0 → X i s a = 1 :=
    (hχ i).2.2.2.2.2 _ a s
  obtain ⟨hρs,hρi,hρp,hρm,Δ,H,hΔ,hΔt,hHc,hHe,hgeo,hgraph,hlimit,S,hSN,_hST,hTE,hgood⟩ :=
    hs.2.2 δ cut hδ hδ' X hXs hXc hXcompact hXzero hXbound hXW
  have hTE' n (hn : 0 < n) i j : j ∈ S n i ↔ χ i ((j:ℝ)/n) ≠ 0 := by
    simpa only [X,exists_const] using hTE n hn i j
  have hSd n (hn : 0 < n) : Pairwise (fun i j => Disjoint (S n i) (S n j)) := by
    intro i j hij
    rw [Finset.disjoint_left]
    intro k hki hkj
    exact Set.disjoint_left.mp (hdisj hij)
      (subset_tsupport _ ((hTE' n hn i k).mp hki)) (subset_tsupport _ ((hTE' n hn j k).mp hkj))
  refine ⟨hcp,δ,cut,χ,Δ,H,hδ,hδ',hδκ,?_,hdisj,hΔ,hΔt,hHc,hHe,hρs,hρi,hρp,hρm,hgeo,hgraph,hlimit,S,hSd,hTE',?_⟩
  · exact fun i => ⟨(hχ i).1,(hχ i).2.1,(hχ i).2.2.1,(hχ i).2.2.2.1,(hχ i).2.2.2.2.1⟩
  have hsmall : 0 < ε/4 := by positivity
  filter_upwards [hgood (ε/4) hsmall] with n hn
  have hn0 := hn.1
  refine ⟨hn0,?_,?_⟩
  · intro i
    have hh := hn.2 i
    dsimp only at hh ⊢
    have hden : foldCircleDensity (stationaryWeight (Icc (F.l-F.R) (F.u+F.R))
        (fun x => (F.m i:ℝ)*((c:ℝ)+F.V x)) (F.A₀ i 0)) = F.density i := by
      simpa only [Fc,PassagePackets.carrier,Int.cast_natCast,PassagePackets.density,
        PassagePackets.weight] using F.density_carrier hmod (c:ℤ) i
    have hmass : (∫ s, stationaryWeight (Icc (F.l-F.R) (F.u+F.R))
        (fun x => (F.m i:ℝ)*((c:ℝ)+F.V x)) (F.A₀ i 0) s)*(4*δ+ε₀) < ε/4 := by
      have he := F.weight_mass_carrier hmod (c:ℤ) i
      dsimp only [PassagePackets.weight,PassagePackets.carrier] at he
      simp only [Int.cast_natCast] at he
      rw [he]
      exact (mul_le_mul_of_nonneg_right ((hWM i).trans hWK) hcoef).trans_lt hCK
    have hAint : Integrable (fun u : UnitAddCircle => ‖F.A i (u,0)‖^2) AddCircle.haarAddCircle :=
      (((F.continuous_amplitude i).comp (continuous_id.prodMk continuous_const)).norm.pow 2).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
    have hMint : (∫ u, ‖F.A i (u,0)‖^2 ∂AddCircle.haarAddCircle) ≤ M := by
      calc
        _ ≤ ∫ _u : UnitAddCircle, M ∂AddCircle.haarAddCircle := integral_mono hAint (integrable_const _) (fun u => hAM i (u,0))
        _ = M := by simp
    rw [hden] at hh
    refine ⟨lt_trans hh.1 ?_,lt_trans hh.2.1 (by linarith),hh.2.2.2.1⟩
    have hhM := mul_le_mul_of_nonneg_left hMint (show 0 ≤ 8*δ by positivity)
    linarith
  · let ρ := signalJitter α γ d (signalPrimeProduct L) B c
    let Hl (n : ℕ) (x : ℝ) := (n:ℝ)*((∫ t in 0..x, (c:ℝ)+F.V t)+Δ n*x)
    have hHl n : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Hl n) :=
      contDiff_const.mul ((contDiff_real_primitive (contDiff_const.add F.smooth_speed)).add
        (contDiff_const.mul contDiff_id))
    have hJs := lawJitter_smooth cut hρs hρi hρp hρm
    have hJd x (hx : x ∈ Ioo δ (1-δ)) : 0 < deriv (lawJitter ρ cut) x := by
      obtain ⟨he,hp⟩ := lawJitter_deriv_pos cut hρs hρi hρp hρm hδ hx
      rwa [he.deriv]
    obtain ⟨G,hGm,hGA,hGA₀,hGV,hGo,hGl,hGu,hGmod⟩ := literal_output_packets
      F.m F.A H Hl X (S n) (hSN n hn0) F.continuous_amplitude F.smooth_amplitude
      hXs hXc hHc hHl hHe cut hδ hδ' (periodize_periodic _) hJs hJd hn0
    have heψ : ∀ x ∈ Ioc (0:ℝ) (0+1), neutralCircleCutoff cut (x:UnitAddCircle) = cut.ψ x := by
      intro x hx
      rw [neutralCircleCutoff_coe]
      exact periodize_eq_on_unit ((subset_tsupport cut.ψ).trans
        (cut.ψ_support.trans (by intro z hz; constructor <;> linarith [hz.1,hz.2]))) ⟨hx.1.le,by simpa using hx.2⟩
    have hsψ : tsupport cut.ψ ⊆ Ioc (0:ℝ) (0+1) ∩ Ioo δ (1-δ) := by
      intro x hx
      have hh := cut.ψ_support hx
      exact ⟨⟨by linarith [hh.1],by linarith [hh.2]⟩,hh⟩
    have hGden (i : PassageOutputIndex (S n)) : G.density i =
        exactRetainedPacketDensity (Ioo δ (1-δ)) (lawJitter ρ cut) (neutralCircleCutoff cut)
          (X i.1) (F.m i.1) H (F.A i.1) {i.2.val} n := by
      apply literal_packet_canonical_density G hGmod i (hGm i) (hGA i) ?_
        (continuous_quantileCircleJitter cut hρs hρi hρp hρm) hJs (fun _ _ => rfl)
        isOpen_Ioo (lawJitter_injOn cut hρs.continuous hρi hρp hρm hδ)
        (fun x hx => (hJd x hx).ne') (continuous_neutralCircleCutoff cut) cut.ψ_smooth cut.ψ_compact
        heψ hsψ (hXc i.1) (hXs i.1) hHc hHl hHe (F.continuous_amplitude i.1)
        (F.smooth_amplitude i.1) hn0
      intro a
      obtain ⟨x,rfl⟩ := Quotient.mk_surjective a
      change (G.V x:UnitAddCircle) = _
      rw [hGV]
      rfl
    refine ⟨G,?_,hGmod,hGV,hGm,hGA,hGden,?_,?_⟩
    · have he : G.m = fun i : PassageOutputIndex (S n) => i.2.val := funext hGm
      rw [he]
      exact output_index_injective (hSd n hn0)
    · intro i E inst
      simp_rw [hGden]
      exact exactRetainedPacketDensity_filtered_singletons hJs isOpen_Ioo (lawJitter_injOn cut hρs.continuous hρi hρp hρm hδ)
        (fun x hx => (hJd x hx).ne') cut.ψ_smooth cut.ψ_compact heψ hsψ (hXs i)
        hHl hHe (F.smooth_amplitude i) hn0 (hSN n hn0 i) E

    · obtain ⟨τG,hτG,hrG⟩ := literal_output_reflection F hr (neutralCircleCutoff cut) cut.ψ X H n (S n)
        (scalar_exact_indices_reflect hχsym (hTE' n hn0)) (fun i s _ => hχsym i s)
        G hGm hGA hGA₀
      refine ⟨τG,hτG,hrG,hGo,hGl,hGu,?_⟩
      intro x hx
      rw [hGV]
      exact positive_deriv_new_speed hn0 (hJd x hx)

end ThreeTorus
end
end

section

/-! Actual transmission with support-linked tracking and its smooth geometric
family. Its positive strength precedes every later finite literal packet list. -/
noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators
namespace ThreeTorus
universe u

theorem exists_signal_reflected_tracked_family
    {b D : ℝ} (hb : 0 < b) (hbD : b < D)
    {d : ℝ → ℂ} (hd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) d)
    (hdc : HasCompactSupport d) (hdr : ∀ v, d (-v) = starRingEnd ℂ (d v))
    (hd0 : d 0 = 0) (hds : support d ⊆ Icc (-D) D) :
    ∃ α : ℝ, ∃ L : ℕ, ∃ γ₀ : ℝ,
      0 < α ∧ α < b/2 ∧ 2 ≤ L ∧ D/b < L ∧ 0 < γ₀ ∧
      ∀ γ : ℝ, 0 < γ → γ ≤ γ₀ →
      (∀ v, 2*γ*‖d v‖ ≤ 1/2) ∧
      ∀ (ι : Type u) [Fintype ι], ∀ (F : PassagePackets ι),
      Injective F.m → F.SpareIndependent → ∀ τref : ι → ι, F.Reflection τref → ∀ B : ℝ, 0 < B →
      (∀ i, b ≤ |(F.m i:ℝ)/B|) →
      ∀ ε η κ : ℝ, 0 < ε → 0 < η → 0 < κ →
      ∃ c : ℕ, 0 < c ∧ ∃ δ : ℝ, ∃ cut : LawCutoffs δ,
      ∃ Δ : ℕ → ℝ, ∃ H : ℕ → UnitAddCircle → UnitAddCircle,
      0 < δ ∧ δ < 1/8 ∧ δ < κ ∧
      (∀ n, 0 < n → |Δ n| ≤ (n:ℝ)⁻¹) ∧ Tendsto Δ atTop (𝓝 0) ∧
      (∀ n, Continuous (H n)) ∧
      (∀ n (x : ℝ), H n (x:UnitAddCircle) =
        ((n:ℝ)*((∫ t in 0..x, (c:ℝ)+F.V t)+Δ n*x):UnitAddCircle)) ∧
      let ρ := signalJitter α γ d (signalPrimeProduct L) B c
      let J := quantileCircleJitter ρ cut
      let J₀ := lawJitter ρ cut
      let σ := fun (n : ℕ) a => (((1+J a/n)/n:ℝ):UnitAddCircle)
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ρ ∧ Integrable ρ ∧
      (∀ y, 0 < ρ y) ∧ (∫ y, ρ y = 1) ∧
      (∀ n, Smooth (torusPassage (H n) (σ n)) ∧ Smooth (torusPassage (H n) (σ n)).symm ∧
        MeasurePreserving (torusPassage (H n) (σ n)) μ μ) ∧
      (∀ n, 0 < n → ∀ x : Cover,
        torusPassage (H n) (σ n) (project x) =
          project (passageFamily (fun t => (c:ℝ)+F.V t) J₀ 1 ((n:ℝ)⁻¹,Δ n) x) ∧
        (torusPassage (H n) (σ n)).symm (project x) =
          project (passageFamily (fun t => (c:ℝ)+F.V t) J₀ (-1) ((n:ℝ)⁻¹,Δ n) x)) ∧
      (∀ r : ℝ, ∀ K : Set Cover, IsCompact K → ∀ e : ℕ,
        TendstoUniformlyOn
          (fun (n : ℕ) x => iteratedFDeriv ℝ e
            (passageFamily (fun t => (c:ℝ)+F.V t) J₀ r ((n:ℝ)⁻¹,Δ n)) x)
          (fun x => iteratedFDeriv ℝ e (fun y : Cover => ![y 0+r*((c:ℝ)+F.V (y 1)),y 1,y 2]) x)
          atTop K) ∧
      ∃ S : ℕ → ι → Finset ℤ, ∀ᶠ n : ℕ in atTop, 0 < n ∧
        ∃ G : PassagePackets (PassageOutputIndex (S n)),
          Injective G.m ∧ G.SpareIndependent ∧
          G.V = (fun x => (1+J₀ x/n)/n) ∧ (∀ i, G.m i = i.2.val) ∧
          (∀ i,
            (∫ x : TripleTorus, ‖packet (F.m i) (F.A i) x-
              outputVector G i (passageChart (H n) x)‖^2 ∂tripleVolume) < ε ∧
            (∫ z, |outputDensity G i z-F.density i z*signalCircleModel
              (signalPrimeProduct L) γ B d (F.m i) ((n:ℤ) • z)| ∂phaseHaar) < ε) ∧
          (∀ i, ∃ x ∈ F.core i.1,
            |(G.m i:ℝ)/((n:ℝ)*c*B)-(F.m i.1:ℝ)/B| < η ∧
            ∀ y, dist ((G.m i:ℝ)*G.V y:UnitAddCircle)
              ((F.m i.1:ℝ)*F.V x:UnitAddCircle) < η) ∧
          ∃ τG : PassageOutputIndex (S n) → PassageOutputIndex (S n),
            (∀ i, (τG i).1 = τref i.1) ∧ G.Reflection τG ∧ G.GoodArc δ := by
  classical
  obtain ⟨α,L,γ₀,hα,hαb,hL,hLD,hγ₀,hfamily⟩ := exists_signal_state_reflected_family hb hbD hd hdc hdr hd0 hds
  refine ⟨α,L,γ₀,hα,hαb,hL,hLD,hγ₀,?_⟩
  intro γ hγp hγs
  obtain ⟨hdb,hstate⟩ := hfamily γ hγp hγs
  refine ⟨hdb,?_⟩
  intro ι inst F hi hmod τref hr B hB hm ε η κ hε hη hκ
  obtain ⟨P,_hP,hPV⟩ := F.speed_bound
  obtain ⟨M,_hM,hMm⟩ := F.angular_bound
  have hD i : |(F.m i:ℝ)/B| ≤ M/B := by
    rw [abs_div,abs_of_pos hB]
    exact div_le_div_of_nonneg_right (hMm i) hB.le
  let τ := η/4
  have hτ : 0 < τ := by dsimp [τ]; positivity
  have hτη : τ < η/2 := by dsimp [τ]; linarith
  obtain ⟨c,hc,hbud⟩ := ((hstate ι F hi hmod τref hr B hB hm ε τ κ hε hτ hκ).and
    (support_drift_budgets (D := M/B) (P := P) (M := M) hB hη)).exists
  obtain ⟨hcp,δ,cut,χ,Δ,H,hδ,hδ',hδκ,hχ,_hχd,hΔ,hΔt,hHc,hHe,
    hρs,hρi,hρp,hρm,hgeo,hgraph,hlimit,S,_hSd,hS,hgood⟩ := hc
  have hb := hbud.2 τ hτ hτη
  obtain ⟨R,_hR,hRJ⟩ := periodic_real_bound (lawJitter_smooth cut hρs hρi hρp hρm).continuous
    (periodize_periodic _)
  refine ⟨c,hcp,δ,cut,Δ,H,hδ,hδ',hδκ,hΔ,hΔt,hHc,hHe,hρs,hρi,hρp,hρm,hgeo,hgraph,hlimit,S,?_⟩
  filter_upwards [hgood,hb.2 R] with n hn hnb
  obtain ⟨hnp,haul,G,hGi,hGmod,hGV,hGm,hGA,_hGden,hgroup,hreflect⟩ := hn
  refine ⟨hnp,G,hGi,hGmod,hGV,hGm,?_,?_,hreflect⟩
  · intro i
    have hv := outputVector_eq_retained F G (neutralCircleCutoff cut) (fun i s _ => χ i s)
      H n hGm hGA i
    have hp : exactRetainedPacketDensity (Ioo δ (1-δ))
        (lawJitter (signalJitter α γ d (signalPrimeProduct L) B c) cut)
        (neutralCircleCutoff cut) (fun s _ => χ i s) (F.m i) H (F.A i) (S n i) n =
        outputDensity G i := by
      have hh := hgroup i (fun _ => True)
      change _ = fun z => ∑ j : ↥(S n i), G.density ⟨i,j⟩ z
      simpa only [Finset.filter_true,ite_true] using hh
    have hh := haul i
    dsimp only at hh
    rw [← hv,hp] at hh
    exact ⟨hh.1,hh.2.1⟩
  · intro i
    obtain ⟨x,hx,ha,ht⟩ := literal_output_tracking hcp hnp hB hD hPV hMm hRJ
      (fun i j hj => (hS n hnp i j).mp hj) (fun i => (hχ i).2.2.2.2) hGm hGV i
    exact ⟨x,hx,ha.trans_lt hb.1,fun y => (ht y).trans_lt hnb.2⟩

end ThreeTorus
end
end

section

/-! Unconditional constructors of the tracked geometric state data. -/
noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators
namespace ThreeTorus
universe u

theorem exists_signal_reflected_geometry_state_oai
    {b D : ℝ} (hb : 0 < b) (hbD : b < D)
    {d : ℝ → ℂ} (hd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) d)
    (hdc : HasCompactSupport d) (hdr : ∀ v, d (-v) = starRingEnd ℂ (d v))
    (hd0 : d 0 = 0) (hds : support d ⊆ Icc (-D) D) :
    ∃ L : ℕ, ∃ γ₀ : ℝ, 2 ≤ L ∧ D/b < L ∧ 0 < γ₀ ∧
      ∀ γ : ℝ, 0 < γ → γ ≤ γ₀ →
      (∀ v, 2*γ*‖d v‖ ≤ 1/2) ∧
      ∀ (ι : Type u) [Fintype ι], ∀ (F : PassagePackets ι),
      Injective F.m → F.SpareIndependent → ∀ τref : ι → ι, F.Reflection τref → ∀ B : ℝ, 0 < B →
      (∀ i, b ≤ |(F.m i:ℝ)/B|) →
      ∀ ε η κ : ℝ, 0 < ε → 0 < η → 0 < κ →
      ∃ g : PassageGeometryFamily F.V, ∃ S : ℕ → ι → Finset ℤ,
        ∀ᶠ n : ℕ in atTop, 0 < n ∧ ∃ G : PassagePackets (PassageOutputIndex (S n)),
          Injective G.m ∧ G.SpareIndependent ∧
          G.V = (fun x => (1+g.J₀ x/n)/n) ∧ (∀ i, G.m i = i.2.val) ∧
          (∀ i,
            (∫ x : TripleTorus, ‖packet (F.m i) (F.A i) x-
              outputVector G i (passageChart (g.H n) x)‖^2 ∂tripleVolume) < ε ∧
            (∫ z, |outputDensity G i z-F.density i z*signalCircleModel
              (signalPrimeProduct L) γ B d (F.m i) ((n:ℤ) • z)| ∂phaseHaar) < ε) ∧
          StateTracks F G Sigma.fst B (g.scale B n) η ∧
        ∃ τG : PassageOutputIndex (S n) → PassageOutputIndex (S n),
          (∀ i, (τG i).1 = τref i.1) ∧ G.Reflection τG ∧
          ∃ δ : ℝ, 0 < δ ∧ δ < 1/8 ∧ δ < κ ∧ G.GoodArc δ := by
  obtain ⟨α,L,γ₀,_hα,_hαb,hL,hLD,hγ₀,hfamily⟩ := exists_signal_reflected_tracked_family hb hbD hd hdc hdr hd0 hds
  refine ⟨L,γ₀,hL,hLD,hγ₀,?_⟩
  intro γ hγp hγs
  obtain ⟨hdb,hstate⟩ := hfamily γ hγp hγs
  refine ⟨hdb,?_⟩
  intro ι inst F hi hmod τref hr B hB hm ε η κ hε hη hκ
  obtain ⟨c,hc,δ,cut,Δ,H,hδ,hδ',hδκ,hΔ,hΔt,hHc,hHe,
    hρs,hρi,hρp,hρm,hgeo,hgraph,hlimit,S,hgood⟩ := hstate ι F hi hmod τref hr B hB hm ε η κ hε hη hκ
  let ρ := signalJitter α γ d (signalPrimeProduct L) B c
  let g : PassageGeometryFamily F.V :=
    ⟨c,hc,Δ,H,quantileCircleJitter ρ cut,lawJitter ρ cut,(fun _ => rfl),
      continuous_quantileCircleJitter cut hρs hρi hρp hρm,hΔ,hΔt,hHc,hHe,hgeo,hgraph,hlimit⟩
  refine ⟨g,S,?_⟩
  filter_upwards [hgood] with n hn
  obtain ⟨hnp,G,hGi,hGmod,hGV,hGm,herr,htrack,τG,hτG,hrG,hgoodG⟩ := hn
  exact ⟨hnp,G,hGi,hGmod,hGV,hGm,herr,htrack,τG,hτG,hrG,δ,hδ,hδ',hδκ,hgoodG⟩

end ThreeTorus
end
end

end OAI
end

theorem solution.{u} : type_of% @OAI.ThreeTorus.exists_signal_reflected_geometry_state_oai.{u} := @OAI.ThreeTorus.exists_signal_reflected_geometry_state_oai.{u}
