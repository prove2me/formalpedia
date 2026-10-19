-- Prove2me | solution 1 for OAI.HenonLaneEmden.WeakPDE.potential_constant
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-19T01:39:11.918061+00:00
-- url     : https://prove2.me/submissions/b63400fb-465b-4e7b-98bf-ee27f300d9ee

import Mathlib
import Definitions.Def_OAIQWHLE000
import Theorems.Thm_OAI_HenonLaneEmden_WeakPDE_harmonic_distribution_nonneg_constant

section
-- module Solutions.OAIQW_HenonLaneEmden.WeakForm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE uE2

section WeakForm



open Set Filter Topology MeasureTheory
open scoped ContDiff
namespace HenonLaneEmden.WeakPDE
variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

lemma integrable_mul_compact {f g : E → ℝ} (hg : HasCompactSupport g)
    (hf : ContinuousOn f (tsupport g)) (hgc : ContinuousOn g (tsupport g)) :
    Integrable (fun x => f x*g x) := by
  apply (integrableOn_iff_integrable_of_support_subset ?_).mp
    ((hf.mul hgc).integrableOn_compact hg)
  intro x hx
  apply subset_tsupport g
  exact (mul_ne_zero_iff.mp hx).2

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma tsupport_dir_subset (f : E → ℝ) (e : E) : tsupport (dir f e) ⊆ tsupport f :=
  tsupport_fderiv_apply_subset ℝ e

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma compactSupport_dir {f : E → ℝ} (hf : HasCompactSupport f) (e : E) :
    HasCompactSupport (dir f e) := hf.fderiv_apply ℝ e

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma contDiffOn_dir {f : E → ℝ} {s : Set E} {k : ℕ∞ω}
    (hf : ContDiffOn ℝ (k+1) f s) (hs : IsOpen s) (e : E) :
    ContDiffOn ℝ k (dir f e) s :=
  (hf.fderiv_of_isOpen hs le_rfl).clm_apply contDiffOn_const

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma differentiableAt_dir {f : E → ℝ} {s : Set E}
    (hf : ContDiffOn ℝ 2 f s) (hs : IsOpen s) {x : E} (hx : x ∈ s) (e : E) :
    DifferentiableAt ℝ (dir f e) x := by
  have hc : ContDiffOn ℝ 1 (dir f e) s := contDiffOn_dir hf hs e
  exact (hc.contDiffAt (hs.mem_nhds hx)).differentiableAt (by norm_num)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma dir_dir {f : E → ℝ} {s : Set E} (hf : ContDiffOn ℝ 2 f s)
    (hs : IsOpen s) {x : E} (hx : x ∈ s) (e : E) :
    dir (dir f e) e x = iteratedFDeriv ℝ 2 f x ![e,e] := by
  have hd : DifferentiableAt ℝ (fderiv ℝ f) x :=
    ((hf.fderiv_of_isOpen hs (m := 1) (by norm_num)).contDiffAt
      (hs.mem_nhds hx)).differentiableAt (by norm_num)
  rw [← bilinearIteratedFDerivTwo_eq_iteratedFDeriv]
  change (fderiv ℝ (fun y => (fderiv ℝ f y) e) x) e = ((fderiv ℝ (fderiv ℝ f) x) e) e
  rw [fderiv_clm_apply hd (differentiableAt_const e)]
  simp

lemma integral_laplacian_test {u φ : E → ℝ} {s : Set E} (hs : IsOpen s)
    (hu : ContDiffOn ℝ 2 u s) (hφ : ContDiff ℝ 2 φ) (hφc : HasCompactSupport φ)
    (hφs : tsupport φ ⊆ s) :
    (∫ x, u x * Laplacian.laplacian φ x) = ∫ x, Laplacian.laplacian u x * φ x := by
  have hφon : ContDiffOn ℝ 2 φ univ := hφ.contDiffOn
  have hφ1 (e : E) : ContDiff ℝ 1 (dir φ e) := by
    exact contDiffOn_univ.mp (contDiffOn_dir hφon isOpen_univ e)
  have hu1 (e : E) : ContDiffOn ℝ 1 (dir u e) s := contDiffOn_dir hu hs e
  have hi1 (e : E) : Integrable (fun x => dir u e x * φ x) :=
    integrable_mul_compact hφc ((hu1 e).continuousOn.mono hφs) hφ.continuous.continuousOn
  have hi2 (e : E) : Integrable (fun x => dir u e x * dir φ e x) :=
    integrable_mul_compact (compactSupport_dir hφc e)
      ((hu1 e).continuousOn.mono ((tsupport_dir_subset φ e).trans hφs))
      (hφ1 e).continuous.continuousOn
  have hi3 (e : E) : Integrable (fun x => dir (dir u e) e x * φ x) := by
    have hc : ContinuousOn (dir (dir u e) e) s :=
      (contDiffOn_dir (k := 0) (by simpa using hu1 e) hs e).continuousOn
    exact integrable_mul_compact hφc (hc.mono hφs) hφ.continuous.continuousOn
  have hi4 (e : E) : Integrable (fun x => u x * dir φ e x) :=
    integrable_mul_compact (compactSupport_dir hφc e)
      (hu.continuousOn.mono ((tsupport_dir_subset φ e).trans hφs))
      (hφ1 e).continuous.continuousOn
  have hi5 (e : E) : Integrable (fun x => u x * dir (dir φ e) e x) := by
    have hc : Continuous (dir (dir φ e) e) := by
      exact (show ContDiff ℝ 0 (dir (dir φ e) e) from
        contDiffOn_univ.mp (contDiffOn_dir (hφ1 e).contDiffOn isOpen_univ e)).continuous
    exact integrable_mul_compact (compactSupport_dir (compactSupport_dir hφc e) e)
      (hu.continuousOn.mono (((tsupport_dir_subset (dir φ e) e).trans
        (tsupport_dir_subset φ e)).trans hφs)) hc.continuousOn
  have hidentity (e : E) : (∫ x, u x * dir (dir φ e) e x) =
      ∫ x, dir (dir u e) e x * φ x := by
    have hA := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := volume)
      (f := u) (g := dir φ e) (v := e) (hi2 e) (hi5 e) (hi4 e)
      (fun x hx => (hu.contDiffAt (hs.mem_nhds (hφs (tsupport_dir_subset φ e hx)))).differentiableAt
        (by norm_num))
      (fun x _ => (hφ1 e).differentiable (by norm_num) x)
    have hB := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := volume)
      (f := dir u e) (g := φ) (v := e) (hi3 e) (hi2 e) (hi1 e)
      (fun x hx => differentiableAt_dir hu hs (hφs hx) e)
      (fun x _ => hφ.differentiable (by norm_num) x)
    change (∫ x, u x * dir (dir φ e) e x) = -(∫ x, dir u e x * dir φ e x) at hA
    change (∫ x, dir u e x * dir φ e x) = -(∫ x, dir (dir u e) e x * φ x) at hB
    rw [hA,hB,neg_neg]
  have hleft (x : E) : u x * Laplacian.laplacian φ x =
      ∑ i, u x * dir (dir φ (stdOrthonormalBasis ℝ E i)) (stdOrthonormalBasis ℝ E i) x := by
    rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_stdOrthonormalBasis]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [dir_dir hφon isOpen_univ (mem_univ x)]
  have hright (x : E) : Laplacian.laplacian u x * φ x =
      ∑ i, dir (dir u (stdOrthonormalBasis ℝ E i)) (stdOrthonormalBasis ℝ E i) x * φ x := by
    by_cases hx : x ∈ tsupport φ
    · rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_stdOrthonormalBasis]
      simp only [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      rw [dir_dir hu hs (hφs hx)]
    · simp [image_eq_zero_of_notMem_tsupport hx]
  simp_rw [hleft,hright]
  rw [integral_finsetSum _ (fun i _ => hi5 _), integral_finsetSum _ (fun i _ => hi3 _)]
  exact Finset.sum_congr rfl fun i _ => hidentity _

end HenonLaneEmden.WeakPDE

namespace HenonLaneEmden.WeakPDE

lemma ibp_compact_on {f f' φ : ℝ → ℝ} {s : Set ℝ}
    (hf : ContinuousOn f s) (hf' : ContinuousOn f' s)
    (hd : ∀ x ∈ s, HasDerivAt f (f' x) x)
    (hφ : ContDiff ℝ 1 φ) (hc : HasCompactSupport φ) (hs : tsupport φ ⊆ s) :
    (∫ x, f x * deriv φ x) = -(∫ x, f' x * φ x) := by
  have hdc : Continuous (deriv φ) := hφ.continuous_deriv le_rfl
  exact integral_mul_deriv_eq_deriv_mul_of_integrable
    (fun x hx => hd x (hs hx)) (fun x _ => (hφ.differentiable one_ne_zero x).hasDerivAt)
    (integrable_mul_compact hc.deriv (hf.mono ((tsupport_deriv_subset (f := φ)).trans hs))
      hdc.continuousOn)
    (integrable_mul_compact hc (hf'.mono hs) hφ.continuous.continuousOn)
    (integrable_mul_compact hc (hf.mono hs) hφ.continuous.continuousOn)

lemma weighted_second_ibp {u u' u'' φ : ℝ → ℝ} {s : Set ℝ} (k : ℕ)
    (hu : ContinuousOn u s) (hu' : ContinuousOn u' s) (hu'' : ContinuousOn u'' s)
    (hdu : ∀ x ∈ s, HasDerivAt u (u' x) x)
    (hdu' : ∀ x ∈ s, HasDerivAt u' (u'' x) x)
    (hφ : ContDiff ℝ 2 φ) (hc : HasCompactSupport φ) (hs : tsupport φ ⊆ s) :
    (∫ r, u r * (r^k * deriv (deriv φ) r + (k:ℝ)*r^(k-1)*deriv φ r)) =
      ∫ r, (r^k * u'' r + (k:ℝ)*r^(k-1)*u' r)*φ r := by
  have hφ' : ContDiff ℝ 1 (deriv φ) := hφ.deriv'
  have hA : ContinuousOn (fun r : ℝ => r^k * u r) s := continuousOn_id.pow k |>.mul hu
  have hA' : ContinuousOn (fun r : ℝ => r^k*u' r+(k:ℝ)*r^(k-1)*u r) s := by
    fun_prop
  have hAd : ∀ r ∈ s, HasDerivAt (fun x : ℝ => x^k*u x)
      (r^k*u' r+(k:ℝ)*r^(k-1)*u r) r := by
    intro r hr
    convert! ((hasDerivAt_id r).pow k).mul (hdu r hr) using 1
    simp only [Pi.pow_apply, id_eq, mul_one]
    ring
  have hB : ContinuousOn (fun r : ℝ => r^k*u' r) s := continuousOn_id.pow k |>.mul hu'
  have hB' : ContinuousOn (fun r : ℝ => r^k*u'' r+(k:ℝ)*r^(k-1)*u' r) s := by
    fun_prop
  have hBd : ∀ r ∈ s, HasDerivAt (fun x : ℝ => x^k*u' x)
      (r^k*u'' r+(k:ℝ)*r^(k-1)*u' r) r := by
    intro r hr
    convert! ((hasDerivAt_id r).pow k).mul (hdu' r hr) using 1
    simp only [Pi.pow_apply, id_eq, mul_one]
    ring
  have h1 := ibp_compact_on hA hA' hAd hφ' hc.deriv ((tsupport_deriv_subset (f := φ)).trans hs)
  have h2 := ibp_compact_on hB hB' hBd (hφ.of_le (by norm_num)) hc hs
  have hiA := integrable_mul_compact hc.deriv.deriv
    (hA.mono (((tsupport_deriv_subset (f := deriv φ)).trans (tsupport_deriv_subset (f := φ))).trans hs))
    (hφ'.continuous_deriv le_rfl).continuousOn
  have hiC : Integrable (fun r : ℝ => ((k:ℝ)*r^(k-1)*u r)*deriv φ r) := by
    apply integrable_mul_compact hc.deriv _ hφ'.continuous.continuousOn
    exact ((continuousOn_const.mul (continuousOn_id.pow (k-1))).mul hu).mono
      ((tsupport_deriv_subset (f := φ)).trans hs)
  have hiB := integrable_mul_compact hc.deriv
    (hB.mono ((tsupport_deriv_subset (f := φ)).trans hs)) hφ'.continuous.continuousOn
  calc
    _ = (∫ r, (r^k*u r)*deriv (deriv φ) r) +
        ∫ r, ((k:ℝ)*r^(k-1)*u r)*deriv φ r := by
      rw [← integral_add hiA hiC]
      congr 1; funext r; ring
    _ = -(∫ r, (r^k*u' r+(k:ℝ)*r^(k-1)*u r)*deriv φ r) +
        ∫ r, ((k:ℝ)*r^(k-1)*u r)*deriv φ r := by rw [h1]
    _ = -(∫ r, (r^k*u' r)*deriv φ r) := by
      simp_rw [add_mul]
      rw [integral_add hiB hiC]
      ring
    _ = _ := by rw [h2,neg_neg]

end HenonLaneEmden.WeakPDE

namespace HenonLaneEmden.WeakPDE
lemma radial_ode_of_weak {u u' u'' w : ℝ → ℝ} (k : ℕ)
    (hu : ContinuousOn u (Ioi 0)) (hu' : ContinuousOn u' (Ioi 0))
    (hu'' : ContinuousOn u'' (Ioi 0)) (hw : ContinuousOn w (Ioi 0))
    (hdu : ∀ r > 0, HasDerivAt u (u' r) r)
    (hdu' : ∀ r > 0, HasDerivAt u' (u'' r) r)
    (hweak : ∀ φ : ℝ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ Ioi 0 →
      (∫ r, u r * (r^k*deriv (deriv φ) r+(k:ℝ)*r^(k-1)*deriv φ r)) =
        ∫ r, r^k*w r*φ r) :
    ∀ r > 0, r^k*u'' r+(k:ℝ)*r^(k-1)*u' r = r^k*w r := by
  let F : ℝ → ℝ := fun r => r^k*u'' r+(k:ℝ)*r^(k-1)*u' r-r^k*w r
  have hFc : ContinuousOn F (Ioi 0) := by unfold F; fun_prop
  have hae : ∀ᵐ r, r ∈ Ioi (0:ℝ) → F r = 0 := by
    apply isOpen_Ioi.ae_eq_zero_of_integral_contDiff_smul_eq_zero
      (hFc.locallyIntegrableOn measurableSet_Ioi)
    intro φ hφ hc hs
    have htest := weighted_second_ibp k hu hu' hu'' hdu hdu' (hφ.of_le (by exact WithTop.coe_le_coe.mpr le_top)) hc hs
    have hi1 : Integrable (fun r => (r^k*u'' r+(k:ℝ)*r^(k-1)*u' r)*φ r) := by
      apply integrable_mul_compact hc _ hφ.continuous.continuousOn
      have hp : ContinuousOn (fun r : ℝ => r^k*u'' r+(k:ℝ)*r^(k-1)*u' r) (Ioi 0) := by fun_prop
      exact hp.mono hs
    have hi2 : Integrable (fun r => r^k*w r*φ r) :=
      integrable_mul_compact hc (((continuousOn_id.pow k).mul hw).mono hs) hφ.continuous.continuousOn
    calc
      (∫ r, φ r • F r) = (∫ r, (r^k*u'' r+(k:ℝ)*r^(k-1)*u' r)*φ r) -
          ∫ r, r^k*w r*φ r := by
        rw [← integral_sub hi1 hi2]
        congr 1; funext r; simp only [smul_eq_mul,F]; ring
      _ = 0 := by rw [← htest, hweak φ hφ hc hs,sub_self]
  have hae' : F =ᵐ[volume.restrict (Ioi (0:ℝ))] (fun _ => 0) := by
    exact (ae_restrict_iff' measurableSet_Ioi).mpr hae
  have heq := Measure.eqOn_open_of_ae_eq hae' isOpen_Ioi hFc continuousOn_const
  intro r hr
  exact sub_eq_zero.mp (heq hr)
end HenonLaneEmden.WeakPDE

namespace HenonLaneEmden.WeakPDE
variable {E : Type uE2} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

lemma continuousOn_laplacian {u : E → ℝ} {s : Set E} (hs : IsOpen s)
    (hu : ContDiffOn ℝ 2 u s) : ContinuousOn (Laplacian.laplacian u) s := by
  have hsum : ContinuousOn (fun x => ∑ i, dir (dir u (stdOrthonormalBasis ℝ E i))
      (stdOrthonormalBasis ℝ E i) x) s := by
    apply continuousOn_finsetSum
    intro i _
    exact (contDiffOn_dir (k := 0) (contDiffOn_dir hu hs _) hs _).continuousOn
  apply hsum.congr
  intro x hx
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_stdOrthonormalBasis]
  apply Finset.sum_congr rfl
  intro i _
  exact (dir_dir hu hs hx _).symm

lemma laplacian_zero_of_notMem_tsupport {u : E → ℝ} {x : E} (hx : x ∉ tsupport u) :
    Laplacian.laplacian u x = 0 := by
  rw [(InnerProductSpace.laplacian_congr_nhds (notMem_tsupport_iff_eventuallyEq.mp hx)).self_of_nhds,
    InnerProductSpace.laplacian_eq_iteratedFDeriv_stdOrthonormalBasis]
  simp

lemma tsupport_laplacian_subset (u : E → ℝ) : tsupport (Laplacian.laplacian u) ⊆ tsupport u := by
  apply closure_minimal _ (isClosed_tsupport u)
  intro x hx
  by_contra hn
  exact hx (laplacian_zero_of_notMem_tsupport hn)

lemma compactSupport_laplacian {u : E → ℝ} (hu : HasCompactSupport u) :
    HasCompactSupport (Laplacian.laplacian u) :=
  hu.of_isClosed_subset (isClosed_tsupport _) (tsupport_laplacian_subset _)

lemma continuous_laplacian {u : E → ℝ} (hu : ContDiff ℝ 2 u) :
    Continuous (Laplacian.laplacian u) := by
  rw [← continuousOn_univ]
  exact continuousOn_laplacian isOpen_univ hu.contDiffOn
end HenonLaneEmden.WeakPDE

end WeakForm

end OAI
end

section
-- module Solutions.OAIQW_HenonLaneEmden.RadialCalculus
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE uE2 uE3

section RadialCalculus

open Set Filter Topology MeasureTheory
open scoped ContDiff

open Set Filter Topology
open scoped RealInnerProductSpace ContDiff

namespace HenonLaneEmden.RadialCalculus
variable {E : Type uE2} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma hasFDerivAt_norm_real {x : E} (hx : x ≠ 0) :
    HasFDerivAt (fun y : E => ‖y‖) (‖x‖⁻¹ • innerSL ℝ x) x := by
  have hd := (hasStrictFDerivAt_norm_sq x).hasFDerivAt.sqrt (pow_ne_zero 2 (norm_ne_zero_iff.mpr hx))
  simp only [Real.sqrt_sq (norm_nonneg _)] at hd
  refine hd.congr_fderiv ?_
  ext v
  simp only [smul_apply, smul_eq_mul]
  field_simp
  ring

lemma hasFDerivAt_profile_norm {h : ℝ → ℝ} {h' : ℝ} {x : E}
    (hx : x ≠ 0) (hh : HasDerivAt h h' ‖x‖) :
    HasFDerivAt (fun y : E => h ‖y‖) ((h'/‖x‖) • innerSL ℝ x) x := by
  have hd := hh.comp_hasFDerivAt x (hasFDerivAt_norm_real hx)
  convert! hd using 1
  ext v
  simp only [smul_apply, smul_eq_mul]
  ring

lemma second_profile_norm {h h' : ℝ → ℝ} {h'' : ℝ} {x : E}
    (hx : x ≠ 0) (hh : ∀ r > 0, HasDerivAt h (h' r) r)
    (hh' : HasDerivAt h' h'' ‖x‖) (e : E) :
    iteratedFDeriv ℝ 2 (fun y : E => h ‖y‖) x ![e,e] =
      ((h''*‖x‖-h' ‖x‖)/‖x‖^3)*⟪x,e⟫^2+(h' ‖x‖/‖x‖)*‖e‖^2 := by
  have hr : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  have heq : fderiv ℝ (fun y : E => h ‖y‖) =ᶠ[𝓝 x]
      (fun y => (h' ‖y‖ / ‖y‖) • innerSL ℝ y) := by
    filter_upwards [isOpen_compl_singleton.mem_nhds hx] with y hy
    exact (hasFDerivAt_profile_norm hy (hh _ (norm_pos_iff.mpr hy))).fderiv
  have hc := hasFDerivAt_profile_norm hx (hh'.div (hasDerivAt_id _) hr)
  have hd := hc.smul (innerSL ℝ (E := E)).hasFDerivAt
  change HasFDerivAt (fun y : E => (h' ‖y‖ / ‖y‖) • innerSL ℝ y) _ x at hd
  rw [← bilinearIteratedFDerivTwo_eq_iteratedFDeriv]
  unfold bilinearIteratedFDerivTwo
  rw [heq.fderiv_eq, hd.fderiv]
  simp [ContinuousLinearMap.smulRight_apply]
  change h' ‖x‖ / ‖x‖ * ⟪e,e⟫ +
    ((h''*‖x‖-h' ‖x‖)/‖x‖^2/‖x‖*⟪x,e⟫)*⟪x,e⟫ = _
  rw [real_inner_self_eq_norm_sq]
  field_simp
  ring

variable [FiniteDimensional ℝ E]
lemma laplacian_profile_norm {h h' : ℝ → ℝ} {h'' : ℝ} {x : E}
    (hx : x ≠ 0) (hh : ∀ r > 0, HasDerivAt h (h' r) r)
    (hh' : HasDerivAt h' h'' ‖x‖) :
    Laplacian.laplacian (fun y : E => h ‖y‖) x =
      h''+((Module.finrank ℝ E:ℝ)-1)/‖x‖*h' ‖x‖ := by
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_stdOrthonormalBasis]
  simp_rw [second_profile_norm hx hh hh', (stdOrthonormalBasis ℝ E).norm_eq_one,
    one_pow, mul_one, Finset.sum_add_distrib, ← Finset.mul_sum]
  have hsum : (∑ i, ⟪x,stdOrthonormalBasis ℝ E i⟫^2) = ‖x‖^2 := by
    simpa only [Real.norm_eq_abs, sq_abs] using (stdOrthonormalBasis ℝ E).sum_sq_norm_inner_left x
  rw [hsum]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp [norm_ne_zero_iff.mpr hx]
  ring

end HenonLaneEmden.RadialCalculus
open Set Filter Topology
open scoped ContDiff
namespace HenonLaneEmden.RadialCalculus
variable {E : Type uE3} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

omit [InnerProductSpace ℝ E] in
lemma radial_tsupport {h : ℝ → ℝ} :
    tsupport (fun x : E => h ‖x‖) ⊆ (fun x : E => ‖x‖) ⁻¹' tsupport h :=
  tsupport_comp_subset_preimage h continuous_norm

omit [InnerProductSpace ℝ E] in
lemma radial_tsupport_off_origin {h : ℝ → ℝ} (hs : tsupport h ⊆ Ioi 0) :
    tsupport (fun x : E => h ‖x‖) ⊆ ({0}ᶜ : Set E) := by
  intro x hx
  have hpos := hs (radial_tsupport hx)
  exact norm_pos_iff.mp hpos

lemma radial_contDiff {h : ℝ → ℝ} {k : ℕ∞ω}
    (hh : ContDiff ℝ k h) (hs : tsupport h ⊆ Ioi 0) :
    ContDiff ℝ k (fun x : E => h ‖x‖) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x = 0
  · have hn : x ∉ tsupport (fun y : E => h ‖y‖) := by
      intro hy
      exact radial_tsupport_off_origin hs hy hx
    exact contDiffAt_const.congr_of_eventuallyEq (notMem_tsupport_iff_eventuallyEq.mp hn)
  · exact hh.contDiffAt.comp x (contDiffAt_norm ℝ hx)

variable [FiniteDimensional ℝ E]
lemma radial_compactSupport {h : ℝ → ℝ} (hh : HasCompactSupport h) :
    HasCompactSupport (fun x : E => h ‖x‖) := by
  obtain ⟨R,hR⟩ := hh.isBounded.exists_norm_le
  apply (isCompact_closedBall (0:E) R).of_isClosed_subset (isClosed_tsupport _)
  intro x hx
  simpa [Metric.mem_closedBall, dist_zero_right] using hR ‖x‖ (radial_tsupport hx)

end HenonLaneEmden.RadialCalculus

end RadialCalculus

end OAI
end

section
-- module Solutions.OAIQW_HenonLaneEmden.Polar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE

section Polar

open Set Filter Topology MeasureTheory
open scoped ContDiff
open Set Filter Topology
open scoped RealInnerProductSpace ContDiff
open Set Filter Topology
open scoped ContDiff

open Set MeasureTheory MeasureTheory.Measure
open scoped ENNReal
noncomputable section
namespace HenonLaneEmden.Polar
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]
  (μ : Measure E) [μ.IsAddHaarMeasure]

omit [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E] in
lemma polar_inverse (x : ({0}ᶜ : Set E)) :
    (((homeomorphUnitSphereProd E) x).2 : ℝ) •
      (((homeomorphUnitSphereProd E) x).1 : E) = x.1 :=
  congrArg Subtype.val ((homeomorphUnitSphereProd E).symm_apply_apply x)

lemma integral_polar_prod (f : E → ℝ) :
    ∫ x, f x ∂μ = ∫ z : Metric.sphere (0:E) 1 × Ioi (0:ℝ),
      f (z.2.1 • z.1.1) ∂μ.toSphere.prod (volumeIoiPow (Module.finrank ℝ E-1)) := by
  calc
    _ = ∫ x : ({0}ᶜ : Set E), f x.1 ∂μ.comap Subtype.val := by
      rw [integral_subtype_comap (measurableSet_singleton _).compl,
        restrict_compl_singleton]
    _ = _ := by
      simpa only [Function.comp_def, homeomorphUnitSphereProd_symm_apply_coe, polar_inverse] using μ.measurePreserving_homeomorphUnitSphereProd.integral_comp
        (Homeomorph.measurableEmbedding _) (f ∘ Subtype.val ∘ (homeomorphUnitSphereProd E).symm)

lemma integrable_polar_prod (f : E → ℝ) :
    Integrable f μ ↔ Integrable (fun z : Metric.sphere (0:E) 1 × Ioi (0:ℝ) =>
      f (z.2.1 • z.1.1)) (μ.toSphere.prod (volumeIoiPow (Module.finrank ℝ E-1))) := by
  conv_lhs => rw [← restrict_compl_singleton (μ := μ) 0, ← IntegrableOn,
    integrableOn_iff_comap_subtypeVal (by measurability)]
  simpa only [Function.comp_def, homeomorphUnitSphereProd_symm_apply_coe, polar_inverse] using μ.measurePreserving_homeomorphUnitSphereProd.integrable_comp_emb
    (Homeomorph.measurableEmbedding _) (g := f ∘ Subtype.val ∘ (homeomorphUnitSphereProd E).symm)

lemma integral_polar_radius (f : E → ℝ) (hf : Integrable f μ) :
    ∫ x, f x ∂μ = ∫ r : Ioi (0:ℝ),
      (∫ θ : Metric.sphere (0:E) 1, f (r.1 • θ.1) ∂μ.toSphere)
      ∂volumeIoiPow (Module.finrank ℝ E-1) := by
  rw [integral_polar_prod]
  exact integral_prod_symm _ ((integrable_polar_prod μ f).mp hf)

lemma integral_polar (f : E → ℝ) (hf : Integrable f μ) :
    ∫ x, f x ∂μ = ∫ r in Ioi (0:ℝ), r^(Module.finrank ℝ E-1) *
      (∫ θ : Metric.sphere (0:E) 1, f (r • θ.1) ∂μ.toSphere) := by
  rw [integral_polar_radius μ f hf, volumeIoiPow]
  simp only [ENNReal.ofReal]
  rw [integral_withDensity_eq_integral_smul]
  · rw [integral_subtype_comap measurableSet_Ioi
      (fun r : ℝ => Real.toNNReal (r^(Module.finrank ℝ E-1)) •
        ∫ θ : Metric.sphere (0:E) 1, f (r • θ.1) ∂μ.toSphere)]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro r hr
    simp [NNReal.smul_def, Real.coe_toNNReal _ (pow_nonneg hr.le _)]
  · exact (measurable_subtype_coe.pow_const _).real_toNNReal

end HenonLaneEmden.Polar

end
end Polar

end OAI
end

section
-- module Solutions.OAIQW_HenonLaneEmden.SphereMean
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uS uE uE2

section SphereMean

open Set Filter Topology MeasureTheory
open scoped ContDiff
open Set Filter Topology
open scoped RealInnerProductSpace ContDiff
open Set Filter Topology
open scoped ContDiff
open Set MeasureTheory MeasureTheory.Measure
open scoped ENNReal
noncomputable section

open Set Filter Topology MeasureTheory

namespace HenonLaneEmden.SphereCalculus
variable {S : Type uS} [TopologicalSpace S] [CompactSpace S] [MeasurableSpace S]
  [BorelSpace S] (μ : Measure S) [IsFiniteMeasure μ]

omit [CompactSpace S] [MeasurableSpace S] [BorelSpace S] in
lemma slice_continuous {F : ℝ × S → ℝ} {s : Set ℝ}
    (hF : ContinuousOn F (s ×ˢ univ)) {x : ℝ} (hx : x ∈ s) :
    Continuous (fun θ => F (x,θ)) := by
  rw [← continuousOn_univ]
  exact hF.comp (continuous_const.prodMk continuous_id).continuousOn (fun _ _ => ⟨hx,mem_univ _⟩)

lemma hasDerivAt_integral_compact {F F' : ℝ × S → ℝ} {s : Set ℝ}
    (hs : IsOpen s) (hF : ContinuousOn F (s ×ˢ univ))
    (hF' : ContinuousOn F' (s ×ˢ univ))
    (hderiv : ∀ x ∈ s, ∀ θ, HasDerivAt (fun y => F (y,θ)) (F' (x,θ)) x)
    {x : ℝ} (hx : x ∈ s) :
    HasDerivAt (fun y => ∫ θ, F (y,θ) ∂μ) (∫ θ, F' (x,θ) ∂μ) x := by
  obtain ⟨ε,hε,hεs⟩ := Metric.mem_nhds_iff.mp (hs.mem_nhds hx)
  let K : Set (ℝ × S) := Metric.closedBall x (ε/2) ×ˢ univ
  have hK : IsCompact K := (isCompact_closedBall x (ε/2)).prod isCompact_univ
  have hKs : K ⊆ s ×ˢ univ := by
    intro z hz
    refine ⟨hεs ?_,mem_univ _⟩
    exact lt_of_le_of_lt (Metric.mem_closedBall.mp hz.1) (by linarith)
  obtain ⟨C,hC⟩ := hK.exists_bound_of_continuousOn (hF'.mono hKs)
  have hmeas : ∀ᶠ y in 𝓝 x, AEStronglyMeasurable (fun θ => F (y,θ)) μ := by
    filter_upwards [hs.mem_nhds hx] with y hy
    exact (slice_continuous hF hy).aestronglyMeasurable
  have hint : Integrable (fun θ => F (x,θ)) μ :=
    (slice_continuous hF hx).integrable_of_hasCompactSupport (.of_compactSpace _)
  have hmeas' : AEStronglyMeasurable (fun θ => F' (x,θ)) μ :=
    (slice_continuous hF' hx).aestronglyMeasurable
  apply (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := μ) (F := fun r θ => F (r,θ)) (F' := fun r θ => F' (r,θ))
    (s := Metric.closedBall x (ε/2)) (bound := fun _ => C)
    (Metric.closedBall_mem_nhds x (by linarith))
    hmeas hint hmeas' _ (integrable_const C) _).2
  · exact Filter.Eventually.of_forall fun θ y hy => hC (y,θ) ⟨hy,mem_univ _⟩
  · exact Filter.Eventually.of_forall fun θ y hy => hderiv y (hKs (show (y,θ) ∈ K from ⟨hy,mem_univ _⟩)).1 θ

end HenonLaneEmden.SphereCalculus

namespace HenonLaneEmden.SphereCalculus
variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [Nontrivial E]
  [MeasurableSpace E] [BorelSpace E] in
lemma sphere_ne_zero (θ : UnitSphere E) : (θ : E) ≠ 0 := by
  have hn : ‖(θ:E)‖ = 1 := by simpa only [Metric.mem_sphere, dist_zero_right] using θ.property
  intro h; simp [h] at hn

omit [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
lemma smul_sphere_ne_zero {r : ℝ} (hr : 0 < r) (θ : UnitSphere E) : r • (θ:E) ≠ 0 :=
  smul_ne_zero hr.ne' (sphere_ne_zero θ)

omit [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
lemma continuous_mean_integrand {u : E → ℝ}
    (hu : ContDiffOn ℝ 2 u ({0}ᶜ : Set E)) :
    ContinuousOn (fun z : ℝ × UnitSphere E => u (z.1 • z.2.1)) (Ioi 0 ×ˢ univ) := by
  exact hu.continuousOn.comp
    (continuous_fst.smul continuous_snd.subtype_val).continuousOn
    (fun z hz => smul_sphere_ne_zero hz.1 z.2)

omit [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
lemma continuous_meanD_integrand {u : E → ℝ}
    (hu : ContDiffOn ℝ 2 u ({0}ᶜ : Set E)) :
    ContinuousOn (fun z : ℝ × UnitSphere E => fderiv ℝ u (z.1 • z.2.1) z.2.1)
      (Ioi 0 ×ˢ univ) := by
  have hc := (hu.fderiv_of_isOpen isOpen_compl_singleton (m := 1) (by norm_num)).continuousOn
  exact (hc.comp (continuous_fst.smul continuous_snd.subtype_val).continuousOn
    (fun z hz => smul_sphere_ne_zero hz.1 z.2)).clm_apply
      continuous_snd.subtype_val.continuousOn

omit [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
lemma continuous_meanDD_integrand {u : E → ℝ}
    (hu : ContDiffOn ℝ 2 u ({0}ᶜ : Set E)) :
    ContinuousOn (fun z : ℝ × UnitSphere E => fderiv ℝ (fderiv ℝ u)
      (z.1 • z.2.1) z.2.1 z.2.1) (Ioi 0 ×ˢ univ) := by
  have hc := ((hu.fderiv_of_isOpen isOpen_compl_singleton (m := 1) (by norm_num)).fderiv_of_isOpen
    isOpen_compl_singleton (m := 0) (by norm_num)).continuousOn
  exact ((hc.comp (continuous_fst.smul continuous_snd.subtype_val).continuousOn
    (fun z hz => smul_sphere_ne_zero hz.1 z.2)).clm_apply
      continuous_snd.subtype_val.continuousOn).clm_apply continuous_snd.subtype_val.continuousOn

omit [Nontrivial E] in
lemma continuousOn_mean {u : E → ℝ} (hu : ContDiffOn ℝ 2 u ({0}ᶜ : Set E)) :
    ContinuousOn (mean u) (Ioi 0) := by
  exact continuousOn_integral_of_compact_support isCompact_univ
    (continuous_mean_integrand hu) (fun _ _ _ h => (h (mem_univ _)).elim)

omit [Nontrivial E] in
lemma continuousOn_meanD {u : E → ℝ} (hu : ContDiffOn ℝ 2 u ({0}ᶜ : Set E)) :
    ContinuousOn (meanD u) (Ioi 0) := by
  exact continuousOn_integral_of_compact_support isCompact_univ
    (continuous_meanD_integrand hu) (fun _ _ _ h => (h (mem_univ _)).elim)

omit [Nontrivial E] in
lemma continuousOn_meanDD {u : E → ℝ} (hu : ContDiffOn ℝ 2 u ({0}ᶜ : Set E)) :
    ContinuousOn (meanDD u) (Ioi 0) := by
  exact continuousOn_integral_of_compact_support isCompact_univ
    (continuous_meanDD_integrand hu) (fun _ _ _ h => (h (mem_univ _)).elim)

omit [Nontrivial E] in
lemma continuous_mean {u : E → ℝ} (hu : Continuous u) : Continuous (mean u) := by
  rw [← continuousOn_univ]
  exact continuousOn_integral_of_compact_support isCompact_univ
    (hu.comp (continuous_fst.smul continuous_snd.subtype_val)).continuousOn
    (fun _ _ _ h => (h (mem_univ _)).elim)

omit [Nontrivial E] in
lemma mean_zero (u : E → ℝ) : mean u 0 = ((volume : Measure E).toSphere univ).toReal * u 0 := by
  simp only [mean, zero_smul, integral_const, smul_eq_mul, Measure.real]

omit [Nontrivial E] in
lemma hasDerivAt_mean {u : E → ℝ} (hu : ContDiffOn ℝ 2 u ({0}ᶜ : Set E))
    {r : ℝ} (hr : 0 < r) : HasDerivAt (mean u) (meanD u r) r := by
  apply hasDerivAt_integral_compact (volume : Measure E).toSphere isOpen_Ioi
    (continuous_mean_integrand hu) (continuous_meanD_integrand hu) _ hr
  intro s hs θ
  have hd := (hu.contDiffAt (isOpen_compl_singleton.mem_nhds
    (smul_sphere_ne_zero hs θ))).differentiableAt (by norm_num)
  convert! hd.hasFDerivAt.comp_hasDerivAt s ((hasDerivAt_id s).smul_const (θ:E)) using 1
  simp only [one_smul]

omit [Nontrivial E] in
lemma hasDerivAt_meanD {u : E → ℝ} (hu : ContDiffOn ℝ 2 u ({0}ᶜ : Set E))
    {r : ℝ} (hr : 0 < r) : HasDerivAt (meanD u) (meanDD u r) r := by
  apply hasDerivAt_integral_compact (volume : Measure E).toSphere isOpen_Ioi
    (continuous_meanD_integrand hu) (continuous_meanDD_integrand hu) _ hr
  intro s hs θ
  have hd := ((hu.fderiv_of_isOpen isOpen_compl_singleton (m := 1) (by norm_num)).contDiffAt
    (isOpen_compl_singleton.mem_nhds (smul_sphere_ne_zero hs θ))).differentiableAt (by norm_num)
  have h1 : HasDerivAt (fun y : ℝ => fderiv ℝ u (y • (θ:E)))
      (fderiv ℝ (fderiv ℝ u) (s • (θ:E)) (θ:E)) s := by
    convert! hd.hasFDerivAt.comp_hasDerivAt s
      ((hasDerivAt_id s).smul_const (θ:E)) using 1
    simp only [one_smul]
  convert! h1.clm_apply (hasDerivAt_const s (θ:E)) using 1
  simp only [map_zero, add_zero]

end HenonLaneEmden.SphereCalculus

end
end SphereMean

end OAI
end

section
-- module Solutions.OAIQW_HenonLaneEmden.SphereFlux
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE uE2

section SphereFlux

open Set Filter Topology MeasureTheory
open scoped ContDiff
open Set Filter Topology
open scoped RealInnerProductSpace ContDiff
open Set Filter Topology
open scoped ContDiff
open Set MeasureTheory MeasureTheory.Measure
open scoped ENNReal
open Set Filter Topology MeasureTheory
noncomputable section


namespace HenonLaneEmden.SphereCalculus
open HenonLaneEmden.RadialCalculus HenonLaneEmden.WeakPDE
variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]

omit [Nontrivial E] in
lemma continuousOn_mean_source {w : E → ℝ} (hw : ContinuousOn w ({0}ᶜ : Set E)) :
    ContinuousOn (mean w) (Ioi 0) := by
  apply continuousOn_integral_of_compact_support isCompact_univ
  · exact hw.comp (continuous_fst.smul continuous_snd.subtype_val).continuousOn
      (fun z hz => smul_sphere_ne_zero hz.1 z.2)
  · exact fun _ _ _ h => (h (mem_univ _)).elim

omit [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
lemma norm_smul_sphere {r : ℝ} (hr : 0 ≤ r) (θ : UnitSphere E) : ‖r • (θ:E)‖ = r := by
  have ht : ‖(θ:E)‖ = 1 := by simpa only [Metric.mem_sphere,dist_zero_right] using θ.property
  simp [norm_smul,Real.norm_eq_abs,abs_of_nonneg hr,ht]

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
lemma radial_jacobian (k : ℕ) {r : ℝ} (hr : r ≠ 0) (a b : ℝ) :
    r^k*(a+(k:ℝ)/r*b)=r^k*a+(k:ℝ)*r^(k-1)*b := by
  cases k with
  | zero => simp
  | succ k => simp only [Nat.add_sub_cancel,pow_succ]; field_simp

lemma radial_weak_identity {u w : E → ℝ}
    (hu : ContDiffOn ℝ 2 u ({0}ᶜ : Set E))
    (hw : ContinuousOn w ({0}ᶜ : Set E))
    (heq : ∀ x ≠ 0, Laplacian.laplacian u x = w x)
    (φ : ℝ → ℝ) (hφ : ContDiff ℝ 2 φ) (hc : HasCompactSupport φ)
    (hs : tsupport φ ⊆ Ioi 0) :
    (∫ r, mean u r * (r^(Module.finrank ℝ E-1)*deriv (deriv φ) r+
          ((Module.finrank ℝ E-1 : ℕ):ℝ)*r^(Module.finrank ℝ E-2)*deriv φ r)) =
      ∫ r, r^(Module.finrank ℝ E-1)*mean w r*φ r := by
  let ψ : E → ℝ := fun x => φ ‖x‖
  have hψ : ContDiff ℝ 2 ψ := radial_contDiff hφ hs
  have hψc : HasCompactSupport ψ := radial_compactSupport hc
  have hψs : tsupport ψ ⊆ ({0}ᶜ : Set E) := radial_tsupport_off_origin hs
  have hi1 : Integrable (fun x => u x * Laplacian.laplacian ψ x) :=
    integrable_mul_compact (compactSupport_laplacian hψc)
      (hu.continuousOn.mono ((tsupport_laplacian_subset ψ).trans hψs))
      (continuous_laplacian hψ).continuousOn
  have hi2 : Integrable (fun x => w x * ψ x) :=
    integrable_mul_compact hψc (hw.mono hψs) hψ.continuous.continuousOn
  have htest : (∫ x, u x * Laplacian.laplacian ψ x) = ∫ x, w x*ψ x := by
    rw [integral_laplacian_test isOpen_compl_singleton hu hψ hψc hψs]
    congr 1; funext x
    by_cases hx : x ∈ tsupport ψ
    · rw [heq x (hψs hx)]
    · simp [image_eq_zero_of_notMem_tsupport hx]
  have hn : 1 ≤ Module.finrank ℝ E := Module.finrank_pos
  have hcast : ((Module.finrank ℝ E-1:ℕ):ℝ) = (Module.finrank ℝ E:ℝ)-1 := by
    rw [Nat.cast_sub hn]; norm_num
  have hφ' := hφ.differentiable_deriv_two
  have hlap {r : ℝ} (hr : 0 < r) (θ : UnitSphere E) : Laplacian.laplacian ψ (r • (θ:E)) =
      deriv (deriv φ) r+((Module.finrank ℝ E-1:ℕ):ℝ)/r*deriv φ r := by
    rw [laplacian_profile_norm (smul_sphere_ne_zero hr θ)
      (fun s _ => (hφ.differentiable (by norm_num) s).hasDerivAt)
      (hφ' _).hasDerivAt, norm_smul_sphere hr.le, ← hcast]
  have hp1 := Polar.integral_polar (volume : Measure E)
    (fun x => u x * Laplacian.laplacian ψ x) hi1
  have hp2 := Polar.integral_polar (volume : Measure E) (fun x => w x*ψ x) hi2
  rw [hp1,hp2] at htest
  have hleft : (∫ r in Ioi (0:ℝ), r^(Module.finrank ℝ E-1) *
      ∫ θ : UnitSphere E, u (r • θ.1)*Laplacian.laplacian ψ (r • θ.1)
        ∂(volume : Measure E).toSphere) =
      ∫ r, mean u r*(r^(Module.finrank ℝ E-1)*deriv (deriv φ) r+
        ((Module.finrank ℝ E-1:ℕ):ℝ)*r^(Module.finrank ℝ E-2)*deriv φ r) := by
    calc
      _ = ∫ r in Ioi (0:ℝ), mean u r*(r^(Module.finrank ℝ E-1)*deriv (deriv φ) r+
          ((Module.finrank ℝ E-1:ℕ):ℝ)*r^(Module.finrank ℝ E-2)*deriv φ r) := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro r hr
        simp_rw [hlap hr]
        rw [integral_mul_const]
        change r^(Module.finrank ℝ E-1)*(mean u r*_)=_
        rw [← mul_assoc, mul_comm _ (mean u r), mul_assoc, radial_jacobian _ hr.ne']
        congr 3
      _ = _ := setIntegral_eq_integral_of_forall_compl_eq_zero (fun r hr => by
        have h1 : deriv φ r = 0 := image_eq_zero_of_notMem_tsupport (fun h =>
          hr (hs (tsupport_deriv_subset h)))
        have h2 : deriv (deriv φ) r = 0 := image_eq_zero_of_notMem_tsupport (fun h =>
          hr (hs (tsupport_deriv_subset (tsupport_deriv_subset h))))
        simp [h1,h2])
  have hright : (∫ r in Ioi (0:ℝ), r^(Module.finrank ℝ E-1) *
      ∫ θ : UnitSphere E, w (r • θ.1)*ψ (r • θ.1) ∂(volume : Measure E).toSphere) =
      ∫ r, r^(Module.finrank ℝ E-1)*mean w r*φ r := by
    calc
      _ = ∫ r in Ioi (0:ℝ), r^(Module.finrank ℝ E-1)*mean w r*φ r := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro r hr
        simp_rw [ψ,norm_smul_sphere hr.le]
        rw [integral_mul_const]
        exact (mul_assoc _ _ _).symm
      _ = _ := setIntegral_eq_integral_of_forall_compl_eq_zero (fun r hr => by
        simp [image_eq_zero_of_notMem_tsupport (fun h => hr (hs h))])
  rw [hleft,hright] at htest
  exact htest

lemma mean_laplacian_ode {u w : E → ℝ}
    (hu : ContDiffOn ℝ 2 u ({0}ᶜ : Set E))
    (hw : ContinuousOn w ({0}ᶜ : Set E))
    (heq : ∀ x ≠ 0, Laplacian.laplacian u x = w x) {r : ℝ} (hr : 0 < r) :
    r^(Module.finrank ℝ E-1)*meanDD u r+
      ((Module.finrank ℝ E-1:ℕ):ℝ)*r^(Module.finrank ℝ E-2)*meanD u r =
        r^(Module.finrank ℝ E-1)*mean w r := by
  have hwk := radial_ode_of_weak (Module.finrank ℝ E-1)
    (continuousOn_mean hu) (continuousOn_meanD hu) (continuousOn_meanDD hu)
    (continuousOn_mean_source hw) (fun r hr => hasDerivAt_mean hu hr)
    (fun r hr => hasDerivAt_meanD hu hr)
    (fun φ hφ hc hs => by
      simpa only [Nat.sub_sub] using radial_weak_identity hu hw heq φ
        (hφ.of_le (by exact WithTop.coe_le_coe.mpr le_top)) hc hs) r hr
  simpa only [Nat.sub_sub] using hwk

end HenonLaneEmden.SphereCalculus

end
end SphereFlux

end OAI
end

section
-- module Solutions.OAIQW_HenonLaneEmden.RadialODE
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE uE2

section RadialODE

open Set Filter Topology MeasureTheory
open scoped ContDiff
open Set Filter Topology
open scoped RealInnerProductSpace ContDiff
open Set Filter Topology
open scoped ContDiff
open Set MeasureTheory MeasureTheory.Measure
open scoped ENNReal
open Set Filter Topology MeasureTheory
noncomputable section


open Set Filter Topology

open MeasureTheory

namespace HenonLaneEmden.SphereCalculus
variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]

omit [Nontrivial E] in
lemma continuous_meanD_global {u : E → ℝ} (hu : ContDiff ℝ 2 u) : Continuous (meanD u) := by
  rw [← continuousOn_univ]
  apply continuousOn_integral_of_compact_support isCompact_univ
    (s := (univ : Set ℝ))
  · exact (((hu.continuous_fderiv (by norm_num)).comp
      (continuous_fst.smul continuous_snd.subtype_val)).clm_apply
      continuous_snd.subtype_val).continuousOn
  · exact fun _ _ _ h => (h (mem_univ _)).elim

end HenonLaneEmden.SphereCalculus

end
end RadialODE

end OAI
end

section
-- module Solutions.OAIQW_HenonLaneEmden.WeakOrigin
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE uE2

section WeakOrigin

open Set Filter Topology MeasureTheory
open scoped ContDiff
open Set Filter Topology
open scoped RealInnerProductSpace ContDiff
open Set Filter Topology
open scoped ContDiff
open Set MeasureTheory MeasureTheory.Measure
open scoped ENNReal
open Set Filter Topology MeasureTheory
open Set Filter Topology
open MeasureTheory
noncomputable section


namespace HenonLaneEmden.WeakPDE
variable {E : Type uE2} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

lemma laplacian_dilation {f : E → ℝ} (hf : ContDiff ℝ 2 f) (R : ℝ) (x : E) :
    Laplacian.laplacian (fun y => f (R • y)) x = R^2*Laplacian.laplacian f (R • x) := by
  simp only [InnerProductSpace.laplacian_eq_iteratedFDeriv_stdOrthonormalBasis]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [iteratedFDeriv_comp_const_smul R hf]
  simp [smul_eq_mul]

end HenonLaneEmden.WeakPDE

end
end WeakOrigin

end OAI
end

section
-- module Solutions.OAIQW_HenonLaneEmden.Mollification
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE uE2 uι uE3

section Mollification

open Set Filter Topology MeasureTheory
open scoped ContDiff
open Set Filter Topology
open scoped RealInnerProductSpace ContDiff
open Set Filter Topology
open scoped ContDiff
open Set MeasureTheory MeasureTheory.Measure
open scoped ENNReal
open Set Filter Topology MeasureTheory
open Set Filter Topology
open MeasureTheory
noncomputable section


open scoped Convolution
namespace HenonLaneEmden.WeakPDE
variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

omit [MeasurableSpace E] [BorelSpace E] in
lemma laplacian_translate (f : E → ℝ) (a x : E) :
    Laplacian.laplacian (fun y => f (a+y)) x = Laplacian.laplacian f (a+x) := by
  simp only [InnerProductSpace.laplacian_eq_iteratedFDeriv_stdOrthonormalBasis,
    iteratedFDeriv_comp_add_left]

omit [MeasurableSpace E] [BorelSpace E] in
lemma laplacian_reflect {f : E → ℝ} (hf : ContDiff ℝ 2 f) (a x : E) :
    Laplacian.laplacian (fun y => f (a-y)) x = Laplacian.laplacian f (a-x) := by
  have hh : (fun y => f (a-y)) = (fun y => (fun z => f (a+z)) ((-1:ℝ) • y)) := by
    ext y; simp [sub_eq_add_neg]
  have hfa : ContDiff ℝ 2 (fun z => f (a+z)) := hf.comp (contDiff_const.add contDiff_id)
  rw [hh,laplacian_dilation hfa,laplacian_translate]
  simp [sub_eq_add_neg]
end HenonLaneEmden.WeakPDE

end
end Mollification

end OAI
end

section
-- module Solutions.OAIQW_HenonLaneEmden.FundamentalSolution
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE

section FundamentalSolution

open Set Filter Topology MeasureTheory
open scoped ContDiff
open Set Filter Topology
open scoped RealInnerProductSpace ContDiff
open Set Filter Topology
open scoped ContDiff
open Set MeasureTheory MeasureTheory.Measure
open scoped ENNReal
open Set Filter Topology MeasureTheory
open Set Filter Topology
open MeasureTheory
open scoped Convolution
open Set Filter Topology
open MeasureTheory Set Filter Topology
open scoped ContDiff
noncomputable section


namespace HenonLaneEmden.WeakPDE
variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
open SphereCalculus

omit [Nontrivial E] in
lemma locallyIntegrable_newtonKernel (hn : 1 ≤ Module.finrank ℝ E) :
    LocallyIntegrable (fun x : E => ‖x‖^(2-(Module.finrank ℝ E:ℝ))) := by
  apply locallyIntegrable_of_norm_le_rpow hn (α := (Module.finrank ℝ E:ℝ)-2) (C := 1)
    (by linarith) _ (measurable_norm.pow_const _).aestronglyMeasurable
  filter_upwards [] with x
  rw [Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg (norm_nonneg x) _),one_mul]
  rw [show -((Module.finrank ℝ E:ℝ)-2) = 2-(Module.finrank ℝ E:ℝ) by ring]

lemma kernel_integral_polar (hn : 3 ≤ Module.finrank ℝ E) {w : E → ℝ}
    (hw : Continuous w) (hwc : HasCompactSupport w) :
    (∫ x : E, ‖x‖^(2-(Module.finrank ℝ E:ℝ))*w x) = ∫ r in Ioi (0:ℝ), r*mean w r := by
  have hi := (locallyIntegrable_newtonKernel (by omega : 1 ≤ Module.finrank ℝ E)).integrable_smul_right_of_hasCompactSupport hw hwc
  change Integrable (fun x : E => ‖x‖^(2-(Module.finrank ℝ E:ℝ))*w x) volume at hi
  rw [Polar.integral_polar volume _ hi]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro r hr
  simp_rw [norm_smul_sphere hr.le,integral_const_mul]
  change r^(Module.finrank ℝ E-1)*(r^(2-(Module.finrank ℝ E:ℝ))*mean w r) = r*mean w r
  rw [← mul_assoc]
  congr 1
  rw [← Real.rpow_natCast,← Real.rpow_add hr]
  have hc : ((Module.finrank ℝ E-1:ℕ):ℝ)+(2-(Module.finrank ℝ E:ℝ)) = 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ Module.finrank ℝ E),Nat.cast_one]
    ring
  rw [hc,Real.rpow_one]

lemma mean_ode_global (hn : 2 ≤ Module.finrank ℝ E) {φ : E → ℝ} (hφ : ContDiff ℝ 2 φ)
    {r : ℝ} (hr : 0 < r) :
    r*meanDD φ r+((Module.finrank ℝ E:ℝ)-1)*meanD φ r = r*mean (Laplacian.laplacian φ) r := by
  have h := mean_laplacian_ode hφ.contDiffOn (continuous_laplacian hφ).continuousOn
    (fun _ _ => rfl) hr
  have hp : r^(Module.finrank ℝ E-1) = r^(Module.finrank ℝ E-2)*r := by
    rw [show Module.finrank ℝ E-1 = Module.finrank ℝ E-2+1 by omega,pow_succ]
  rw [hp,Nat.cast_sub (by omega : 1 ≤ Module.finrank ℝ E),Nat.cast_one] at h
  apply mul_left_cancel₀ (pow_ne_zero (Module.finrank ℝ E-2) hr.ne')
  nlinarith [h]

omit [Nontrivial E] in
lemma mean_at_large_zero {φ : E → ℝ} {R : ℝ}
    (hR : 0 < R) (hbound : ∀ x ∈ tsupport φ, ‖x‖ < R) {r : ℝ} (hr : R ≤ r) :
    mean φ r = 0 ∧ meanD φ r = 0 ∧ mean (Laplacian.laplacian φ) r = 0 := by
  have hs (θ : UnitSphere E) : r • (θ:E) ∉ tsupport φ := by
    intro hx
    have hh := hbound _ hx
    rw [norm_smul_sphere (hR.le.trans hr)] at hh
    linarith
  refine ⟨?_,?_,?_⟩
  · unfold mean
    have he : (fun θ : UnitSphere E => φ (r • (θ:E))) = 0 := by
      ext θ
      exact image_eq_zero_of_notMem_tsupport (hs θ)
    rw [he]
    exact integral_zero _ _
  · unfold meanD
    simp_rw [fderiv_of_notMem_tsupport ℝ (hs _),_root_.zero_apply]
    exact integral_zero _ _
  · unfold mean
    simp_rw [laplacian_zero_of_notMem_tsupport (hs _)]
    exact integral_zero _ _

lemma integral_kernel_laplacian (hn : 3 ≤ Module.finrank ℝ E) {φ : E → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hφc : HasCompactSupport φ) :
    (∫ x : E, ‖x‖^(2-(Module.finrank ℝ E:ℝ))*Laplacian.laplacian φ x) =
      -((Module.finrank ℝ E:ℝ)-2)*((volume : Measure E).toSphere univ).toReal*φ 0 := by
  obtain ⟨R,hR,hbound⟩ := hφc.isBounded.exists_pos_norm_lt
  rw [kernel_integral_polar hn (continuous_laplacian hφ) (compactSupport_laplacian hφc)]
  rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi Ioc_subset_Ioi_self (s := Ioc 0 R)
    (fun r hr => by
      have hRr : R ≤ r := le_of_not_gt (fun h => hr.2 ⟨hr.1,h.le⟩)
      rw [(mean_at_large_zero hR hbound hRr).2.2,mul_zero])]
  rw [← intervalIntegral.integral_of_le hR.le]
  let H (r : ℝ) := r*meanD φ r+((Module.finrank ℝ E:ℝ)-2)*mean φ r
  have hH : Continuous H := (continuous_id.mul (continuous_meanD_global hφ)).add ((continuous_mean hφ.continuous).const_mul _)
  have hHd (r : ℝ) (hr : r ∈ Ioo 0 R) : HasDerivAt H (r*mean (Laplacian.laplacian φ) r) r := by
    convert! (((hasDerivAt_id r).mul (hasDerivAt_meanD hφ.contDiffOn hr.1)).add
      ((hasDerivAt_mean hφ.contDiffOn hr.1).const_mul ((Module.finrank ℝ E:ℝ)-2))) using 1
    simp only [id_eq,one_mul]
    nlinarith [mean_ode_global (by omega) hφ hr.1]
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hR.le hH.continuousOn hHd
    ((continuous_id.mul (continuous_mean (continuous_laplacian hφ))).intervalIntegrable _ _)]
  obtain ⟨h0,h1,_⟩ := mean_at_large_zero hR hbound le_rfl
  dsimp [H]
  rw [h0,h1,mean_zero]
  ring
end HenonLaneEmden.WeakPDE

end
end FundamentalSolution

end OAI
end

section
-- module Solutions.OAIQW_HenonLaneEmden.NewtonPotential
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE uE2 uE3 uE4

section NewtonPotential

open Set Filter Topology MeasureTheory
open scoped ContDiff
open Set Filter Topology
open scoped RealInnerProductSpace ContDiff
open Set Filter Topology
open scoped ContDiff
open Set MeasureTheory MeasureTheory.Measure
open scoped ENNReal
open Set Filter Topology MeasureTheory
open Set Filter Topology
open MeasureTheory
open scoped Convolution
open Set Filter Topology
open MeasureTheory Set Filter Topology
open scoped ContDiff
noncomputable section


namespace HenonLaneEmden.WeakPDE
variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]

omit [Nontrivial E] in
lemma measurable_kernel_source {g : E → ℝ} (hg : Measurable g) :
    Measurable (fun z : E × E => ‖z.1-z.2‖^(2-(Module.finrank ℝ E:ℝ))*g z.2) :=
  ((measurable_fst.sub measurable_snd).norm.pow_const _).mul (hg.comp measurable_snd)

omit [Nontrivial E] in
lemma measurable_rawPotential {g : E → ℝ} (hg : Measurable g) : Measurable (rawPotential g) :=
  (measurable_kernel_source hg).stronglyMeasurable.integral_prod_right'.measurable

omit [Nontrivial E] in
lemma rawPotential_nonneg {g : E → ℝ} (hg : ∀ x, 0 ≤ g x) (x : E) : 0 ≤ rawPotential g x :=
  integral_nonneg fun y => mul_nonneg (Real.rpow_nonneg (norm_nonneg _) _) (hg y)

omit [Nontrivial E] in
lemma locallyIntegrable_rawPotential {g U : E → ℝ} (hg : Measurable g) (hgp : ∀ x, 0 ≤ g x)
    (hU : LocallyIntegrable U) (hbound : ∀ x, rawPotential g x ≤ U x) :
    LocallyIntegrable (rawPotential g) := by
  apply hU.mono (measurable_rawPotential hg).aestronglyMeasurable
  filter_upwards [] with x
  rw [Real.norm_eq_abs,abs_of_nonneg (rawPotential_nonneg hgp x)]
  exact (hbound x).trans (le_abs_self _)

lemma integral_kernel_laplacian_translate (hn : 3 ≤ Module.finrank ℝ E) {φ : E → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hφc : HasCompactSupport φ) (y : E) :
    (∫ x : E, ‖x-y‖^(2-(Module.finrank ℝ E:ℝ))*Laplacian.laplacian φ x) =
      -((Module.finrank ℝ E:ℝ)-2)*((volume : Measure E).toSphere univ).toReal*φ y := by
  have hh := integral_kernel_laplacian hn (hφ.comp (contDiff_const.sub contDiff_id))
    (hφc.comp_homeomorph (Homeomorph.subLeft y))
  simp only [Function.comp_def,id_eq,sub_zero] at hh
  simp_rw [laplacian_reflect hφ] at hh
  have he := integral_sub_left_eq_self (μ := volume)
    (fun x : E => ‖x-y‖^(2-(Module.finrank ℝ E:ℝ))*Laplacian.laplacian φ x) y
  simp only [sub_sub_cancel_left,norm_neg] at he
  exact he ▸ hh

lemma rawPotential_weak_equation (hn : 3 ≤ Module.finrank ℝ E) {g : E → ℝ}
    (hg : Measurable g) (hgp : ∀ x, 0 ≤ g x)
    (hki : ∀ x, Integrable (fun y => ‖x-y‖^(2-(Module.finrank ℝ E:ℝ))*g y))
    (hP : LocallyIntegrable (rawPotential g)) {φ : E → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hφc : HasCompactSupport φ) :
    (∫ x, rawPotential g x*Laplacian.laplacian φ x) =
      -((Module.finrank ℝ E:ℝ)-2)*((volume : Measure E).toSphere univ).toReal*(∫ x, g x*φ x) := by
  let F (z : E × E) := ‖z.1-z.2‖^(2-(Module.finrank ℝ E:ℝ))*g z.2*Laplacian.laplacian φ z.1
  have hFm : Measurable F := (measurable_kernel_source hg).mul ((continuous_laplacian hφ).measurable.comp measurable_fst)
  have hi : Integrable F (volume.prod volume) := by
    apply (integrable_prod_iff hFm.aestronglyMeasurable).mpr
    refine ⟨Eventually.of_forall fun x => (hki x).mul_const (Laplacian.laplacian φ x),?_⟩
    have hpint := hP.integrable_smul_right_of_hasCompactSupport (continuous_laplacian hφ).norm
      (compactSupport_laplacian hφc).norm
    convert hpint using 1
    ext x
    simp only [F,norm_mul,Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg (norm_nonneg (x- _)) _),abs_of_nonneg (hgp _)]
    rw [integral_mul_const]
    rfl
  calc
    _ = ∫ x, ∫ y, F (x,y) := by simp only [F,integral_mul_const,rawPotential]
    _ = ∫ y, ∫ x, F (x,y) := integral_integral_swap hi
    _ = ∫ y, g y*(-((Module.finrank ℝ E:ℝ)-2)*((volume : Measure E).toSphere univ).toReal*φ y) := by
      apply integral_congr_ae
      filter_upwards [] with y
      have hf : (fun x => F (x,y)) = fun x => g y*(‖x-y‖^(2-(Module.finrank ℝ E:ℝ))*Laplacian.laplacian φ x) := by ext x; dsimp [F]; ring
      rw [hf,integral_const_mul,integral_kernel_laplacian_translate hn hφ hφc]
    _ = _ := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with y
      ring
end HenonLaneEmden.WeakPDE

namespace HenonLaneEmden.WeakPDE
variable {E : Type uE4} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]

lemma potential_constant_core (hn : 3 ≤ Module.finrank ℝ E) {u g : E → ℝ}
    (hu : Continuous u) (hg : Measurable g) (hgp : ∀ x, 0 ≤ g x)
    (hki : ∀ x, Integrable (fun y => ‖x-y‖^(2-(Module.finrank ℝ E:ℝ))*g y))
    (hlower : ∀ x, rawPotential g x ≤ ((Module.finrank ℝ E:ℝ)-2)*
      ((volume : Measure E).toSphere univ).toReal*u x)
    (heq : ∀ (φ : E → ℝ), ContDiff ℝ 2 φ → HasCompactSupport φ →
      (∫ y, u y*Laplacian.laplacian φ y) = -(∫ y, g y*φ y)) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ᵐ x, ((Module.finrank ℝ E:ℝ)-2)*
      ((volume : Measure E).toSphere univ).toReal*u x = rawPotential g x+c := by
  let D := ((Module.finrank ℝ E:ℝ)-2)*((volume : Measure E).toSphere univ).toReal
  have hP : LocallyIntegrable (rawPotential g) :=
    locallyIntegrable_rawPotential hg hgp (hu.const_mul D).locallyIntegrable hlower
  let h (x : E) := D*u x-rawPotential g x
  have hh : LocallyIntegrable h := (hu.const_mul D).locallyIntegrable.sub hP
  have hharm (φ : E → ℝ) (hφ : ContDiff ℝ 2 φ) (hφc : HasCompactSupport φ) :
      (∫ x, h x*Laplacian.laplacian φ x) = 0 := by
    have h1 := (hu.locallyIntegrable (μ := volume)).integrable_smul_right_of_hasCompactSupport (continuous_laplacian hφ)
      (compactSupport_laplacian hφc)
    have h2 := hP.integrable_smul_right_of_hasCompactSupport (continuous_laplacian hφ)
      (compactSupport_laplacian hφc)
    simp only [smul_eq_mul] at h1 h2
    have hf : (fun x => h x*Laplacian.laplacian φ x) =
        fun x => D*(u x*Laplacian.laplacian φ x)-rawPotential g x*Laplacian.laplacian φ x := by ext x; dsimp [h]; ring
    rw [hf,integral_sub (h1.const_mul D) h2,integral_const_mul,heq φ hφ hφc,
      rawPotential_weak_equation hn hg hgp hki hP hφ hφc]
    dsimp [D]; ring
  obtain ⟨c,hc,hceq⟩ := harmonic_distribution_nonneg_constant (by omega) hh
    (fun x => sub_nonneg.mpr (hlower x)) hharm
  refine ⟨c,hc,?_⟩
  filter_upwards [hceq] with x hx
  change D*u x-rawPotential g x = c at hx
  change D*u x = rawPotential g x+c
  exact sub_eq_iff_eq_add'.mp hx

lemma potential_constant_oai (hn : 3 ≤ Module.finrank ℝ E) {u g : E → ℝ}
    (hu : Continuous u) (hg : Measurable g) (hgp : ∀ x, 0 ≤ g x)
    (hki : ∀ x, Integrable (fun y => ‖x-y‖^(2-(Module.finrank ℝ E:ℝ))*g y))
    (hlower : ∀ x, (∫ y, ‖x-y‖^(2-(Module.finrank ℝ E:ℝ))*g y) ≤ ((Module.finrank ℝ E:ℝ)-2)*
      ((volume : Measure E).toSphere univ).toReal*u x)
    (heq : ∀ (φ : E → ℝ), ContDiff ℝ 2 φ → HasCompactSupport φ →
      (∫ y, u y*Laplacian.laplacian φ y) = -(∫ y, g y*φ y)) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ᵐ x, ((Module.finrank ℝ E:ℝ)-2)*
      ((volume : Measure E).toSphere univ).toReal*u x =
        (∫ y, ‖x-y‖^(2-(Module.finrank ℝ E:ℝ))*g y)+c :=
  potential_constant_core hn hu hg hgp hki hlower heq

end HenonLaneEmden.WeakPDE

end
end NewtonPotential

end OAI
end

theorem solution.{uE4} : type_of% @OAI.HenonLaneEmden.WeakPDE.potential_constant_oai.{uE4} := @OAI.HenonLaneEmden.WeakPDE.potential_constant_oai.{uE4}
