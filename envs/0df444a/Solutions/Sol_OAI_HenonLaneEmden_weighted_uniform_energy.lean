-- Prove2me | solution 1 for OAI.HenonLaneEmden.weighted_uniform_energy
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-19T01:46:29.180878+00:00
-- url     : https://prove2.me/submissions/61501c6b-e63f-4656-8f7e-93c7cefc50a0

import Mathlib
import Definitions.Def_HenonEmden
import Definitions.Def_OAIQWHLE000
import Theorems.Thm_OAI_HenonLaneEmden_WeakPDE_potential_constant
import Theorems.Thm_OAI_HenonLaneEmden_WeakPDE_weak_newton_lower
import Theorems.Thm_OAI_HenonLaneEmden_localization_relative
import Theorems.Thm_OAI_HenonLaneEmden_pressure_relative

section
-- module Solutions.OAIQW_HenonLaneEmden.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. -/
section OAICompat434
theorem ite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : ¬p) :
    (if p then a else b) = b := if_neg h
end OAICompat434

end OAI
end

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

lemma mean_pos {u : E → ℝ} (hu : Continuous u) (hp : ∀ x, 0 < u x) (r : ℝ) :
    0 < mean u r := by
  unfold mean
  apply (integral_pos_iff_support_of_nonneg (fun θ : UnitSphere E => (hp (r • θ.1)).le) ?_).mpr
  · have heq : Function.support (fun θ : UnitSphere E => u (r • θ.1)) = univ := by
      ext θ; simp [Function.mem_support, (hp _).ne']
    rw [heq]
    exact (Measure.measure_univ_pos.mpr (Measure.toSphere_ne_zero (volume : Measure E)))
  · exact (hu.comp (continuous_const.smul continuous_subtype_val)).integrable_of_hasCompactSupport
      (.of_compactSpace _)

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

namespace HenonLaneEmden.SphereCalculus
variable {E : Type uE2} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]

lemma mean_pos_off_origin {w : E → ℝ} (hw : ContinuousOn w ({0}ᶜ : Set E))
    (hp : ∀ x ≠ 0, 0 < w x) {r : ℝ} (hr : 0 < r) : 0 < mean w r := by
  have hp' (θ : UnitSphere E) : 0 < w (r • θ.1) := hp _ (smul_sphere_ne_zero hr θ)
  have hc : Continuous (fun θ : UnitSphere E => w (r • θ.1)) := by
    rw [← continuousOn_univ]
    apply hw.comp (continuous_const.smul continuous_subtype_val).continuousOn
    exact fun θ _ => smul_sphere_ne_zero hr θ
  unfold mean
  apply (integral_pos_iff_support_of_nonneg (fun θ => (hp' θ).le)
    (hc.integrable_of_hasCompactSupport (.of_compactSpace _))).mpr
  have heq : Function.support (fun θ : UnitSphere E => w (r • θ.1)) = univ := by
    ext θ; simp [Function.mem_support,(hp' θ).ne']
  rw [heq]
  exact Measure.measure_univ_pos.mpr (Measure.toSphere_ne_zero (volume : Measure E))

omit [Nontrivial E] in
lemma mean_neg (w : E → ℝ) (r : ℝ) : mean (fun x => -w x) r = -mean w r := by
  exact integral_neg _

lemma hasDerivAt_mean_flux {u w : E → ℝ}
    (hu : ContDiffOn ℝ 2 u ({0}ᶜ : Set E))
    (hw : ContinuousOn w ({0}ᶜ : Set E))
    (heq : ∀ x ≠ 0, -Laplacian.laplacian u x = w x) {r : ℝ} (hr : 0 < r) :
    HasDerivAt (fun s => s^(Module.finrank ℝ E-1)*meanD u s)
      (-(r^(Module.finrank ℝ E-1)*mean w r)) r := by
  have ho := mean_laplacian_ode hu hw.neg (fun x hx => (neg_eq_iff_eq_neg.mp (heq x hx))) hr
  simp only [Pi.neg_def,mean_neg] at ho
  have hd := ((hasDerivAt_id r).pow (Module.finrank ℝ E-1)).mul (hasDerivAt_meanD hu hr)
  convert! hd using 1
  simp only [mul_one,Nat.sub_sub, id_eq, Pi.pow_apply, Nat.reduceAdd]
  linarith
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
namespace HenonLaneEmden.RadialODE
lemma pow_le_self {k : ℕ} (hk : 1 ≤ k) {r : ℝ} (hr : 0 ≤ r) (hr1 : r ≤ 1) : r^k ≤ r := by
  calc r^k ≤ r^1 := pow_le_pow_of_le_one hr hr1 hk
       _ = r := pow_one r

lemma sample_flux {U V : ℝ → ℝ} {k : ℕ} (hk : 1 ≤ k)
    (hU : ContinuousOn U (Ici 0)) (hV : ∀ r > 0, HasDerivAt U (V r) r)
    {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) :
    ∃ c ∈ Ioo 0 r, |c^k * V c| ≤ |U r-U 0| := by
  obtain ⟨c,hc,hd⟩ := exists_hasDerivAt_eq_slope U V hr (hU.mono (Icc_subset_Ici_self))
    (fun x hx => hV x hx.1)
  refine ⟨c,hc,?_⟩
  rw [hd,sub_zero,← mul_div_assoc,abs_div,abs_mul,abs_of_pos (pow_pos hc.1 k),abs_of_pos hr]
  apply (div_le_iff₀ hr).mpr
  have hp : c^k ≤ r := (pow_le_self hk hc.1.le (hc.2.le.trans hr1)).trans hc.2.le
  nlinarith [abs_nonneg (U r-U 0)]

lemma flux_nonpos {U V : ℝ → ℝ} {k : ℕ} (hk : 1 ≤ k)
    (hU : ContinuousOn U (Ici 0)) (hV : ∀ r > 0, HasDerivAt U (V r) r)
    (hF : AntitoneOn (fun r => r^k*V r) (Ioi 0)) {r : ℝ} (hr : 0 < r) :
    r^k*V r ≤ 0 := by
  have hl : Tendsto (fun s => |U s-U 0|) (𝓝[>] 0) (𝓝 0) := by
    have hc : Tendsto U (𝓝[>] 0) (𝓝 (U 0)) := (hU 0 (by simp)).mono Ioi_subset_Ici_self
    simpa using (hc.sub_const (U 0)).abs
  apply ge_of_tendsto hl
  filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hr),
    mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (zero_lt_one : (0:ℝ)<1))] with s hs hsr hs1
  obtain ⟨c,hc,hsamp⟩ := sample_flux hk hU hV hs hs1.le
  exact (hF hc.1 hr (hc.2.le.trans hsr.le)).trans ((le_abs_self _).trans hsamp)

end HenonLaneEmden.RadialODE

open MeasureTheory

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
variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
omit [FiniteDimensional ℝ E] in
lemma dir_mul {f g : E → ℝ} {x : E}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) (e : E) :
    dir (fun y => f y*g y) e x = dir f e x*g x+f x*dir g e x := by
  unfold dir
  change (fderiv ℝ (f*g) x) e = _
  rw [fderiv_mul hf hg]
  simp [smul_eq_mul]
  ring

omit [FiniteDimensional ℝ E] in
lemma dir_dir_mul {f g : E → ℝ} (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g) (e x : E) :
    dir (dir (fun y => f y*g y) e) e x =
      dir (dir f e) e x*g x+2*(dir f e x*dir g e x)+f x*dir (dir g e) e x := by
  have heq : dir (fun y => f y*g y) e = fun y => dir f e y*g y+f y*dir g e y := by
    ext y; exact dir_mul (hf.differentiable (by norm_num) y) (hg.differentiable (by norm_num) y) e
  rw [heq]
  have hdf := differentiableAt_dir hf.contDiffOn isOpen_univ (mem_univ x) e
  have hdg := differentiableAt_dir hg.contDiffOn isOpen_univ (mem_univ x) e
  have hfx := hf.differentiable (by norm_num) x
  have hgx := hg.differentiable (by norm_num) x
  change (fderiv ℝ (dir f e*g+f*dir g e) x) e = _
  rw [fderiv_add (hdf.mul hgx) (hfx.mul hdg),_root_.add_apply]
  change dir (fun y => dir f e y*g y) e x+dir (fun y => f y*dir g e y) e x = _
  rw [dir_mul hdf hgx,dir_mul hfx hdg]
  ring

lemma laplacian_mul {f g : E → ℝ} (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g) (x : E) :
    Laplacian.laplacian (fun y => f y*g y) x =
      Laplacian.laplacian f x*g x+f x*Laplacian.laplacian g x+
        2*∑ i, dir f (stdOrthonormalBasis ℝ E i) x*dir g (stdOrthonormalBasis ℝ E i) x := by
  simp only [InnerProductSpace.laplacian_eq_iteratedFDeriv_stdOrthonormalBasis]
  simp_rw [← dir_dir (hf.mul hg).contDiffOn isOpen_univ (mem_univ x),
    dir_dir_mul hf hg,← dir_dir hf.contDiffOn isOpen_univ (mem_univ x),
    ← dir_dir hg.contDiffOn isOpen_univ (mem_univ x)]
  simp only [Finset.sum_add_distrib,Finset.sum_mul,Finset.mul_sum]
  ring
end HenonLaneEmden.WeakPDE

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

omit [FiniteDimensional ℝ E] in
lemma dir_dilation (f : E → ℝ) (R : ℝ) (x e : E) :
    dir (fun y => f (R • y)) e x = R*dir f e (R • x) := by
  unfold dir
  rw [fderiv_comp_smul]
  simp

lemma continuous_laplacian_dilation_mul {φ ξ : E → ℝ} (hφ : ContDiff ℝ 2 φ) (hξ : ContDiff ℝ 2 ξ) :
    Continuous (fun z : ℝ × E => Laplacian.laplacian (fun y => φ (z.1 • y)*ξ y) z.2) := by
  have hid (R : ℝ) (x : E) : Laplacian.laplacian (fun y => φ (R • y)*ξ y) x =
      R^2*Laplacian.laplacian φ (R • x)*ξ x+φ (R • x)*Laplacian.laplacian ξ x+
        2*∑ i, (R*dir φ (stdOrthonormalBasis ℝ E i) (R • x))*dir ξ (stdOrthonormalBasis ℝ E i) x := by
    have hh : ContDiff ℝ 2 (fun y => φ (R • y)) := hφ.comp (contDiff_const.smul contDiff_id)
    rw [laplacian_mul hh hξ,
      laplacian_dilation hφ]
    simp_rw [dir_dilation]
  simp_rw [hid]
  have hφlap := continuous_laplacian hφ
  have hξlap := continuous_laplacian hξ
  have hφd (e : E) : Continuous (dir φ e) :=
    (contDiffOn_univ.mp (contDiffOn_dir (k := 1) hφ.contDiffOn isOpen_univ e)).continuous
  have hξd (e : E) : Continuous (dir ξ e) :=
    (contDiffOn_univ.mp (contDiffOn_dir (k := 1) hξ.contDiffOn isOpen_univ e)).continuous
  fun_prop

variable [MeasurableSpace E] [BorelSpace E]
lemma continuous_cutoff_error {u φ ξ : E → ℝ} (hu : Continuous u)
    (hφ : ContDiff ℝ 2 φ) (hξ : ContDiff ℝ 2 ξ) (hξc : HasCompactSupport ξ) :
    Continuous (fun R : ℝ => ∫ y : E, u (R • y)*Laplacian.laplacian (fun z => φ (R • z)*ξ z) y) := by
  rw [← continuousOn_univ]
  apply continuousOn_integral_of_compact_support hξc
  · exact ((hu.comp (continuous_fst.smul continuous_snd)).mul
      (continuous_laplacian_dilation_mul hφ hξ)).continuousOn
  · intro R y _ hy
    have hh : y ∉ tsupport (fun z => φ (R • z)*ξ z) := fun h => hy (tsupport_mul_subset_right h)
    rw [laplacian_zero_of_notMem_tsupport hh,mul_zero]
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

lemma convolve_def (f g : E → ℝ) (x : E) : convolve f g x = ∫ y, f y*g (x-y) := rfl

lemma contDiff_convolve {f g : E → ℝ} (hf : LocallyIntegrable f)
    (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g) : ContDiff ℝ 2 (convolve f g) :=
  hgc.contDiff_convolution_right (ContinuousLinearMap.mul ℝ ℝ) hf hg

lemma dir_convolve {f g : E → ℝ} (hf : LocallyIntegrable f)
    (hg : ContDiff ℝ 1 g) (hgc : HasCompactSupport g) (e x : E) :
    dir (convolve f g) e x = convolve f (dir g e) x := by
  unfold dir convolve
  rw [(hgc.hasFDerivAt_convolution_right (ContinuousLinearMap.mul ℝ ℝ) hf hg x).fderiv]
  exact convolution_precompR_apply (ContinuousLinearMap.mul ℝ ℝ) hf (hgc.fderiv ℝ)
    (hg.continuous_fderiv one_ne_zero) x e

end HenonLaneEmden.WeakPDE

end
end Mollification

end OAI
end

section
-- module Solutions.OAIQW_HenonLaneEmden.Sources
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Sources

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
noncomputable section


open MeasureTheory Set Filter Topology
open scoped ContDiff
namespace HenonLaneEmden

lemma source_off_zero {n : ℕ} (u : Space n → ℝ) (q B : ℝ) {x : Space n} (hx : x ≠ 0) :
    source u q B x = ‖x‖^B*(u x)^q := ite_eq_right hx

lemma measurable_source {n : ℕ} {u : Space n → ℝ} (hu : Continuous u) (q B : ℝ) :
    Measurable (source u q B) :=
  Measurable.ite (measurableSet_singleton 0) measurable_const
    ((measurable_norm.pow_const B).mul (hu.measurable.pow_const q))

lemma source_nonneg {n : ℕ} {u : Space n → ℝ} (hu : ∀ x, 0 ≤ u x) (q B : ℝ) (x : Space n) :
    0 ≤ source u q B x := by
  unfold source
  split_ifs
  · exact le_rfl
  · exact mul_nonneg (Real.rpow_nonneg (norm_nonneg _) _) (Real.rpow_nonneg (hu x) _)

lemma source_pos {n : ℕ} {u : Space n → ℝ} (hu : ∀ x, 0 < u x) (q B : ℝ) {x : Space n}
    (hx : x ≠ 0) : 0 < source u q B x := by
  rw [source_off_zero u q B hx]
  exact mul_pos (Real.rpow_pos_of_pos (norm_pos_iff.mpr hx) _) (Real.rpow_pos_of_pos (hu x) _)

lemma regular_source {n : ℕ} {u : Space n → ℝ} (hu : ContDiffOn ℝ 2 u ({0}ᶜ : Set (Space n)))
    (hupos : ∀ x, 0 < u x) (q B : ℝ) : ContDiffOn ℝ 2 (source u q B) ({0}ᶜ : Set (Space n)) := by
  apply ((contDiffOn_id.norm ℝ (fun x hx => by simpa using hx)).rpow_const_of_ne
    (fun x hx => norm_ne_zero_iff.mpr (by simpa using hx))).mul
      (hu.rpow_const_of_ne (fun x _ => ne_of_gt (hupos x))) |>.congr
  intro x hx
  exact source_off_zero u q B (by simpa using hx)

lemma locallyIntegrable_source {n : ℕ} (hn : 1 ≤ n) {u : Space n → ℝ}
    (hu : Continuous u) (hupos : ∀ x, 0 < u x) (q B : ℝ) (hB : -(n : ℝ) < B) :
    LocallyIntegrable (source u q B) volume := by
  have hdim : 1 ≤ Module.finrank ℝ (Space n) := by simpa using hn
  have : Nontrivial (Space n) := Module.nontrivial_of_finrank_pos (R := ℝ) (by omega)
  have hpow : LocallyIntegrable (fun x : Space n => ‖x‖^B) volume := by
    apply locallyIntegrable_of_norm_le_rpow hdim (α := -B) (C := 1) ?_ ?_
      (measurable_norm.pow_const B).aestronglyMeasurable
    · simp only [finrank_euclideanSpace_fin]
      linarith
    · filter_upwards [] with x
      simp [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg x) B)]
  have hc : Continuous (fun x => (u x)^q) := hu.rpow_const (fun x => Or.inl (ne_of_gt (hupos x)))
  apply (hpow.mul_continuous hc).congr
  filter_upwards [ae_iff.mpr (show volume {x : Space n | ¬ x ≠ 0} = 0 by simp)] with x hx
  exact (source_off_zero u q B hx).symm

lemma IsSolution.weak_u_off_origin {n : ℕ} {p q A B : ℝ} {u v : Space n → ℝ}
    (h : IsSolution n p q A B u v) {φ : Space n → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hφc : HasCompactSupport φ) (hφ0 : 0 ∉ tsupport φ) :
    (∫ x, u x * Laplacian.laplacian φ x) = -(∫ x, source v p A x * φ x) := by
  have hφs : tsupport φ ⊆ ({0}ᶜ : Set (Space n)) := by
    intro x hx
    simpa using fun hzero : x = 0 => hφ0 (hzero ▸ hx)
  rw [WeakPDE.integral_laplacian_test isClosed_singleton.isOpen_compl h.regular_u hφ hφc hφs,
    ← integral_neg]
  apply integral_congr_ae
  filter_upwards [] with x
  by_cases hx : x ∈ tsupport φ
  · have hx0 : x ≠ 0 := by simpa using hφs hx
    have he : -(Laplacian.laplacian u) x = ‖x‖^A*(v x)^p := h.equation_u x hx0
    rw [source_off_zero v p A hx0, ← he]
    ring
  · simp [image_eq_zero_of_notMem_tsupport hx]

end HenonLaneEmden

end
end Sources

end OAI
end

section
-- module Solutions.OAIQW_HenonLaneEmden.OriginBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section OriginBounds

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


namespace HenonLaneEmden.RadialODE
lemma impossible_two_dimensional {U V W : ℝ → ℝ}
    (hU : ContinuousOn U (Ici 0)) (hV : ∀ r > 0, HasDerivAt U (V r) r)
    (hF : ∀ r > 0, HasDerivAt (fun s => s*V s) (-r*W r) r)
    (hp : ∀ r > 0, 0 < U r) (hW : ∀ r > 0, 0 < W r) : False := by
  have ha : StrictAntiOn (fun s => s*V s) (Ioi 0) := by
    apply strictAntiOn_of_hasDerivWithinAt_neg (convex_Ioi 0)
      (fun r hr => (hF r hr).continuousAt.continuousWithinAt)
      (fun r hr => (hF r (by simpa using hr)).hasDerivWithinAt)
    intro r hr
    have hr0 : 0 < r := by simpa using hr
    exact mul_neg_of_neg_of_pos (neg_neg_of_pos hr0) (hW r hr0)
  have hf1 : 1*V 1 ≤ 0 := by
    simpa using flux_nonpos (k := 1) (by rfl) hU hV (by simpa using ha.antitoneOn)
      (r := 1) zero_lt_one
  have hf2 : 2*V 2 < 0 := lt_of_lt_of_le (ha (by norm_num) (by norm_num) (by norm_num)) hf1
  let c : ℝ := -(2*V 2)
  have hc : 0 < c := neg_pos.mpr hf2
  have hcomp : AntitoneOn (fun r => U r+c*Real.log r) (Ici 2) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici 2)
    · intro r hr
      change 2 ≤ r at hr
      exact ((hV r (by linarith [hr])).continuousAt.add
        ((Real.continuousAt_log (by linarith [hr])).const_mul c)).continuousWithinAt
    · intro r hr
      have hr0 : 0 < r := by simp only [interior_Ici,mem_Ioi] at hr; linarith
      exact ((hV r hr0).add ((Real.hasDerivAt_log hr0.ne').const_mul c)).hasDerivWithinAt
    · intro r hr
      have hr2 : 2 < r := by simpa using hr
      have hr0 : 0 < r := by linarith
      have hle : r*V r ≤ 2*V 2 := ha.antitoneOn (by norm_num) hr0 hr2.le
      change V r+c*r⁻¹ ≤ 0
      have hdiv : V r ≤ (2*V 2)/r := (le_div_iff₀ hr0).mpr (by nlinarith [hle])
      rw [div_eq_mul_inv] at hdiv
      dsimp [c]
      nlinarith
  have hbound : ∀ᶠ r : ℝ in atTop, c*Real.log r ≤ U 2+c*Real.log 2 := by
    filter_upwards [eventually_ge_atTop (2:ℝ)] with r hr
    have hh := hcomp (by simp) hr hr
    have hp' := hp r (by linarith)
    linarith
  have hlim := Real.tendsto_log_atTop.const_mul_atTop hc
  have hconst := tendsto_atTop_mono' atTop hbound hlim
  exact not_tendsto_atTop_of_tendsto_nhds tendsto_const_nhds hconst
end HenonLaneEmden.RadialODE

namespace HenonLaneEmden
open SphereCalculus
lemma IsSolution.not_two_dimensional {p q A B : ℝ} {u v : Space 2 → ℝ}
    (h : IsSolution 2 p q A B u v) : False := by
  have hw : ContinuousOn (source v p A) ({0}ᶜ : Set (Space 2)) :=
    (regular_source h.regular_v h.positive_v p A).continuousOn
  have heq : ∀ x ≠ 0, -Laplacian.laplacian u x = source v p A x := by
    intro x hx; rw [source_off_zero v p A hx]; exact h.equation_u x hx
  exact RadialODE.impossible_two_dimensional (continuous_mean h.continuous_u).continuousOn
    (fun r hr => hasDerivAt_mean h.regular_u hr)
    (fun r hr => by simpa using hasDerivAt_mean_flux h.regular_u hw heq hr)
    (fun r _ => mean_pos h.continuous_u h.positive_u r)
    (fun r hr => mean_pos_off_origin hw (fun x hx => source_pos h.positive_v p A hx) hr)
end HenonLaneEmden

namespace HenonLaneEmden.RadialODE
lemma impossible_log_derivative_near_zero {U V : ℝ → ℝ} {c R : ℝ}
    (hc : 0 < c) (hR : 0 < R) (hU : ContinuousOn U (Ici 0))
    (hV : ∀ r > 0, HasDerivAt U (V r) r)
    (hbound : ∀ r ∈ Ioo 0 R, V r ≤ -c/r) : False := by
  let H : ℝ → ℝ := fun r => U r+c*Real.log r
  have hanti : AntitoneOn H (Ioo 0 R) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ioo 0 R)
    · intro r hr
      exact ((hV r hr.1).continuousAt.add
        ((Real.continuousAt_log hr.1.ne').const_mul c)).continuousWithinAt
    · intro r hr
      have hr' : r ∈ Ioo 0 R := interior_subset hr
      exact ((hV r hr'.1).add ((Real.hasDerivAt_log hr'.1.ne').const_mul c)).hasDerivWithinAt
    · intro r hr
      have hh := hbound r (interior_subset hr)
      change V r+c*r⁻¹ ≤ 0
      rw [div_eq_mul_inv,neg_mul] at hh
      linarith
  have hlimU : Tendsto U (𝓝[>] 0) (𝓝 (U 0)) := (hU 0 (by simp)).mono Ioi_subset_Ici_self
  have hlim : Tendsto H (𝓝[>] 0) atBot := hlimU.add_atBot
    (Real.tendsto_log_nhdsGT_zero.const_mul_atBot hc)
  have hconst : Tendsto (fun _ : ℝ => H (R/2)) (𝓝[>] 0) atBot := by
    apply tendsto_atBot_mono' _ _ hlim
    filter_upwards [self_mem_nhdsWithin,mem_nhdsWithin_of_mem_nhds
      (Iio_mem_nhds (half_pos hR))] with r hr hrR
    exact hanti ⟨hr,hrR.trans (half_lt_self hR)⟩ ⟨half_pos hR,half_lt_self hR⟩ hrR.le
  exact not_tendsto_nhds_of_tendsto_atBot hconst _ tendsto_const_nhds

lemma impossible_source_inverse_square {U V W : ℝ → ℝ} {k : ℕ} (hk : 1 ≤ k)
    (hU : ContinuousOn U (Ici 0)) (hV : ∀ r > 0, HasDerivAt U (V r) r)
    (hF : ∀ r > 0, HasDerivAt (fun s => s^k*V s) (-(r^k*W r)) r)
    (hW : ∀ r > 0, 0 ≤ W r) {c R : ℝ} (hc : 0 < c) (hR : 0 < R)
    (hbound : ∀ r ∈ Ioo 0 R, c/r^2 ≤ W r) : False := by
  have ha : AntitoneOn (fun s => s^k*V s) (Ioi 0) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ioi 0)
      (fun r hr => (hF r hr).continuousAt.continuousWithinAt)
      (fun r hr => (hF r (by simpa using hr)).hasDerivWithinAt)
    intro r hr
    have hr0 : 0 < r := by simpa using hr
    exact neg_nonpos.mpr (mul_nonneg (pow_nonneg hr0.le k) (hW r hr0))
  have hneg : ∀ r > 0, r^k*V r ≤ 0 := fun r hr => flux_nonpos hk hU hV ha hr
  apply impossible_log_derivative_near_zero (c := c/2^(k+1)) (div_pos hc (by positivity)) hR hU hV
  intro r hr
  have hhalf : 0 < r/2 := half_pos hr.1
  obtain ⟨s,hs,he⟩ := exists_hasDerivAt_eq_slope (fun t => t^k*V t)
    (fun t => -(t^k*W t)) (half_lt_self hr.1)
    (fun t ht => (hF t (hhalf.trans_le ht.1)).continuousAt.continuousWithinAt)
    (fun t ht => hF t (hhalf.trans ht.1))
  have hs0 : 0 < s := hhalf.trans hs.1
  have hwr : c/r^2 ≤ W s := by
    have hsr2 : s^2 ≤ r^2 := pow_le_pow_left₀ hs0.le hs.2.le 2
    exact (div_le_div_of_nonneg_left hc.le (sq_pos_of_pos hs0) hsr2).trans
      (hbound s ⟨hs0,hs.2.trans hr.2⟩)
  have hpow : (r/2)^k ≤ s^k := pow_le_pow_left₀ hhalf.le hs.1.le k
  have hprod : (r/2)^k*(c/r^2) ≤ s^k*W s := mul_le_mul hpow hwr
    (div_nonneg hc.le (sq_nonneg r)) (pow_nonneg hs0.le k)
  have hfeq : -(s^k*W s)*(r-r/2) = r^k*V r-(r/2)^k*V (r/2) :=
    (eq_div_iff (sub_pos.mpr (half_lt_self hr.1)).ne').mp he
  have hid : (r/2)^k*(c/r^2)*(r-r/2) = r^k*((c/2^(k+1))/r) := by
    rw [div_pow,pow_succ]
    field_simp
    ring
  have hest : r^k*V r ≤ -(r^k*((c/2^(k+1))/r)) := by
    have hmul := mul_le_mul_of_nonneg_right hprod (sub_pos.mpr (half_lt_self hr.1)).le
    rw [hid] at hmul
    have hn := hneg (r/2) hhalf
    nlinarith
  have hdiv : V r ≤ -((c/2^(k+1))/r) :=
    (mul_le_mul_iff_right₀ (pow_pos hr.1 k)).mp (by nlinarith [hest])
  simpa only [neg_div] using hdiv
end HenonLaneEmden.RadialODE

namespace HenonLaneEmden
open SphereCalculus
lemma source_mean_factor {n : ℕ} {u : Space n → ℝ} (q B : ℝ) {r : ℝ} (hr : 0 < r) :
    mean (source u q B) r = r^B * mean (fun x => (u x)^q) r := by
  unfold mean
  simp_rw [source_off_zero u q B (smul_sphere_ne_zero hr _),norm_smul_sphere hr.le]
  exact integral_const_mul (r^B) _

lemma source_mean_lower_near_zero {n : ℕ} (hn : 1 ≤ n) {u : Space n → ℝ}
    (hu : Continuous u) (hp : ∀ x, 0 < u x) (q B : ℝ) :
    ∃ c > 0, ∃ R > 0, R ≤ 1 ∧ ∀ r ∈ Ioo 0 R, c*r^B ≤ mean (source u q B) r := by
  have : Nontrivial (Space n) := Module.nontrivial_of_finrank_pos (R := ℝ) (by simp only [finrank_euclideanSpace_fin]; omega)
  let a : Space n → ℝ := fun x => (u x)^q
  have ha : Continuous a := hu.rpow_const (fun x => Or.inl (hp x).ne')
  have ha0 : 0 < mean a 0 := mean_pos ha (fun x => Real.rpow_pos_of_pos (hp x) q) 0
  have he : ∀ᶠ r in 𝓝 (0:ℝ), mean a 0/2 < mean a r :=
    (continuous_mean ha).continuousAt (Ioi_mem_nhds (half_lt_self ha0))
  obtain ⟨δ,hδ,hnear⟩ := Metric.eventually_nhds_iff.mp he
  refine ⟨mean a 0/2,half_pos ha0,min δ 1,lt_min hδ zero_lt_one,min_le_right _ _,?_⟩
  intro r hr
  rw [source_mean_factor q B hr.1]
  have hh : mean a 0/2 ≤ mean a r := (hnear (by
    simpa [Real.dist_eq,abs_of_pos hr.1] using hr.2.trans_le (min_le_left δ 1))).le
  simpa only [mul_comm] using mul_le_mul_of_nonneg_left hh (Real.rpow_nonneg hr.1.le B)

lemma IsSolution.first_weight_gt_neg_two {n : ℕ} (hn : 2 ≤ n) {p q A B : ℝ}
    {u v : Space n → ℝ} (h : IsSolution n p q A B u v) : -2 < A := by
  have : Nontrivial (Space n) := Module.nontrivial_of_finrank_pos (R := ℝ) (by
    simp only [finrank_euclideanSpace_fin]; omega)
  by_contra hA
  have hA' : A ≤ -2 := le_of_not_gt hA
  obtain ⟨c,hc,R,hR,hR1,hbound⟩ := source_mean_lower_near_zero (by omega) h.continuous_v h.positive_v p A
  have hw : ContinuousOn (source v p A) ({0}ᶜ : Set (Space n)) :=
    (regular_source h.regular_v h.positive_v p A).continuousOn
  have heq : ∀ x ≠ 0, -Laplacian.laplacian u x = source v p A x := by
    intro x hx; rw [source_off_zero v p A hx]; exact h.equation_u x hx
  apply RadialODE.impossible_source_inverse_square (k := n-1) (by omega)
    (continuous_mean h.continuous_u).continuousOn (fun r hr => hasDerivAt_mean h.regular_u hr)
    (fun r hr => by simpa using hasDerivAt_mean_flux h.regular_u hw heq hr)
    (fun r hr => (mean_pos_off_origin hw (fun x hx => source_pos h.positive_v p A hx) hr).le)
    hc hR
  intro r hr
  have hpow := Real.rpow_le_rpow_of_exponent_ge hr.1 (hr.2.le.trans hR1) hA'
  have hpow' : (r^2)⁻¹ ≤ r^A := by
    simpa only [Real.rpow_neg hr.1.le,Real.rpow_two] using hpow
  have hh : c/r^2 ≤ c*r^A := by
    simpa only [div_eq_mul_inv] using mul_le_mul_of_nonneg_left hpow' hc.le
  exact hh.trans (hbound r hr)

end HenonLaneEmden

end
end OriginBounds

end OAI
end

section
-- module Solutions.OAIQW_HenonLaneEmden.Distribution
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE uE2

section Distribution

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
variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

lemma cutoff_laplacian_integral_scale {u φ ξ : E → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hξ : ContDiff ℝ 2 ξ) {R : ℝ} (hR : 0 < R) :
    (∫ x : E, u x*Laplacian.laplacian (fun y => φ y*ξ (R⁻¹ • y)) x) =
      R^(Module.finrank ℝ E)*(R⁻¹)^2*
        ∫ y : E, u (R • y)*Laplacian.laplacian (fun z => φ (R • z)*ξ z) y := by
  have hF : ContDiff ℝ 2 (fun z : E => φ (R • z)*ξ z) :=
    (hφ.comp (contDiff_const.smul contDiff_id)).mul hξ
  have hid : (fun y : E => φ y*ξ (R⁻¹ • y)) =
      (fun y : E => (fun z => φ (R • z)*ξ z) (R⁻¹ • y)) := by
    ext y
    simp [smul_smul,ne_of_gt hR]
  have hh (x : E) : Laplacian.laplacian (fun y => φ y*ξ (R⁻¹ • y)) (R • x) =
      (R⁻¹)^2*Laplacian.laplacian (fun z => φ (R • z)*ξ z) x := by
    rw [hid,laplacian_dilation hF]
    simp [smul_smul,ne_of_gt hR]
  have hc := Measure.integral_comp_smul_of_nonneg volume
    (fun x => u x*Laplacian.laplacian (fun y => φ y*ξ (R⁻¹ • y)) x) R (hR := hR.le)
  simp only [hh,smul_eq_mul] at hc
  have hC : (∫ x, u (R • x)*((R⁻¹)^2*Laplacian.laplacian (fun z => φ (R • z)*ξ z) x)) =
      (R⁻¹)^2*(∫ x, u (R • x)*Laplacian.laplacian (fun z => φ (R • z)*ξ z) x) := by
    simp_rw [← mul_assoc,mul_comm (u (R • _)) ((R⁻¹)^2),mul_assoc]
    exact integral_const_mul _ _
  rw [hC] at hc
  have hn : R^(Module.finrank ℝ E) ≠ 0 := pow_ne_zero _ (ne_of_gt hR)
  calc
    _ = R^Module.finrank ℝ E * ((R^Module.finrank ℝ E)⁻¹ *
      ∫ x, u x*Laplacian.laplacian (fun y => φ y*ξ (R⁻¹ • y)) x) := by field_simp
    _ = _ := by rw [← hc]; ring

lemma cutoff_laplacian_integral_tendsto_zero {u φ ξ : E → ℝ}
    (hn : 3 ≤ Module.finrank ℝ E) (hu : Continuous u)
    (hφ : ContDiff ℝ 2 φ) (hξ : ContDiff ℝ 2 ξ) (hξc : HasCompactSupport ξ) :
    Tendsto (fun R : ℝ => ∫ x : E, u x*Laplacian.laplacian (fun y => φ y*ξ (R⁻¹ • y)) x)
      (𝓝[>] 0) (𝓝 0) := by
  have heq : ∀ᶠ R : ℝ in 𝓝[>] 0, (∫ x : E, u x*Laplacian.laplacian (fun y => φ y*ξ (R⁻¹ • y)) x) =
      R^(Module.finrank ℝ E-2)*∫ y : E, u (R • y)*Laplacian.laplacian (fun z => φ (R • z)*ξ z) y := by
    filter_upwards [self_mem_nhdsWithin] with R hR
    rw [cutoff_laplacian_integral_scale hφ hξ hR]
    congr 1
    rw [inv_pow]
    have hp := pow_sub₀ R (ne_of_gt hR) (show 2 ≤ Module.finrank ℝ E by omega)
    exact hp.symm
  apply Tendsto.congr' (Filter.EventuallyEq.symm heq)
  have hpow : Tendsto (fun R : ℝ => R^(Module.finrank ℝ E-2)) (𝓝[>] 0) (𝓝 0) := by
    have := (continuous_pow (Module.finrank ℝ E-2) : Continuous (fun R : ℝ => R^(Module.finrank ℝ E-2))).tendsto 0
    simpa [show Module.finrank ℝ E-2 ≠ 0 by omega] using this.mono_left nhdsWithin_le_nhds
  simpa using hpow.mul ((continuous_cutoff_error hu hφ hξ hξc).tendsto 0 |>.mono_left nhdsWithin_le_nhds)
end HenonLaneEmden.WeakPDE

namespace HenonLaneEmden.WeakPDE
variable {E : Type uE2} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

omit [MeasurableSpace E] [BorelSpace E] in
lemma bump_dilation_eventually_zero (ξ : ContDiffBump (0 : E)) {x : E} (hx : x ≠ 0) :
    (fun R : ℝ => ξ (R⁻¹ • x)) =ᶠ[𝓝[>] 0] 0 := by
  have he : 0 < ‖x‖ / ξ.rOut := div_pos (norm_pos_iff.mpr hx) ξ.rOut_pos
  filter_upwards [self_mem_nhdsWithin, (eventually_lt_nhds he).filter_mono nhdsWithin_le_nhds] with R hR hlt
  apply ξ.zero_of_le_dist
  rw [dist_zero_right,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hR),← div_eq_inv_mul]
  apply (le_div_iff₀ hR).mpr
  simpa only [mul_comm] using (le_of_lt ((lt_div_iff₀ ξ.rOut_pos).mp hlt))

lemma cutoff_source_integral_tendsto_zero [Nontrivial E] {g φ : E → ℝ}
    (hg : LocallyIntegrable g) (hφ : Continuous φ) (hφc : HasCompactSupport φ)
    (ξ : ContDiffBump (0 : E)) :
    Tendsto (fun R : ℝ => ∫ x : E, g x*(φ x*ξ (R⁻¹ • x))) (𝓝[>] 0) (𝓝 0) := by
  have hi : Integrable (fun x => g x*φ x) :=
    hg.integrable_smul_right_of_hasCompactSupport hφ hφc
  have hc (R : ℝ) : Continuous (fun x : E => ξ (R⁻¹ • x)) :=
    ξ.continuous.comp (continuous_const.smul continuous_id)
  have lim := tendsto_integral_filter_of_dominated_convergence
    (μ := volume) (l := 𝓝[>] (0 : ℝ)) (F := fun R x => g x*(φ x*ξ (R⁻¹ • x)))
    (f := fun _ => (0 : ℝ)) (fun x => ‖g x*φ x‖)
    (Eventually.of_forall fun R => by
      rw [show (fun x => g x*(φ x*ξ (R⁻¹ • x))) =
        ((fun x => g x*φ x)*(fun x => ξ (R⁻¹ • x))) by ext x; simp only [Pi.mul_apply]; ring]
      exact hi.aestronglyMeasurable.mul (hc R).aestronglyMeasurable)
    (Eventually.of_forall fun R => Eventually.of_forall fun x => by
      rw [← mul_assoc,norm_mul]
      exact mul_le_of_le_one_right (norm_nonneg _) (by
        rw [Real.norm_eq_abs,abs_of_nonneg ξ.nonneg]; exact ξ.le_one))
    hi.norm ?_
  · simpa using lim
  filter_upwards [ae_iff.mpr (show volume {x : E | ¬ x ≠ 0} = 0 by simp)] with x hx
  apply tendsto_const_nhds.congr'
  filter_upwards [bump_dilation_eventually_zero ξ hx] with R hR
  simp [hR]

omit [MeasurableSpace E] [BorelSpace E] in
lemma cutoff_test_off_origin {φ : E → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hφc : HasCompactSupport φ) (ξ : ContDiffBump (0 : E)) {R : ℝ} (_hR : 0 < R) :
    ContDiff ℝ 2 (fun x => φ x-φ x*ξ (R⁻¹ • x)) ∧
    HasCompactSupport (fun x => φ x-φ x*ξ (R⁻¹ • x)) ∧
    0 ∉ tsupport (fun x => φ x-φ x*ξ (R⁻¹ • x)) := by
  refine ⟨hφ.sub (hφ.mul (ξ.contDiff.comp (contDiff_const.smul contDiff_id))),
    hφc.sub (hφc.mul_right), ?_⟩
  apply notMem_tsupport_iff_eventuallyEq.mpr
  have ht : Tendsto (fun x : E => R⁻¹ • x) (𝓝 0) (𝓝 0) := by
    have h : Continuous (fun x : E => R⁻¹ • x) := continuous_const.smul continuous_id
    have ht := h.tendsto 0
    change Tendsto (fun x : E => R⁻¹ • x) (𝓝 0) (𝓝 (R⁻¹ • (0:E))) at ht
    simpa only [smul_zero] using ht
  have he := ξ.eventuallyEq_one.comp_tendsto ht
  filter_upwards [he] with x hx
  change ξ (R⁻¹ • x) = 1 at hx
  simp [hx]

lemma distributional_extension (hn : 3 ≤ Module.finrank ℝ E) {u g : E → ℝ}
    (hu : Continuous u) (hg : LocallyIntegrable g)
    (heq : ∀ (φ : E → ℝ), ContDiff ℝ 2 φ → HasCompactSupport φ → 0 ∉ tsupport φ →
      (∫ x, u x*Laplacian.laplacian φ x) = -(∫ x, g x*φ x))
    {φ : E → ℝ} (hφ : ContDiff ℝ 2 φ) (hφc : HasCompactSupport φ) :
    (∫ x, u x*Laplacian.laplacian φ x) = -(∫ x, g x*φ x) := by
  have : Nontrivial E := (Module.finrank_pos_iff (R := ℝ)).mp (by omega)
  let ξ : ContDiffBump (0 : E) := ⟨1,2,by norm_num,by norm_num⟩
  have hi : Integrable (fun x => g x*φ x) :=
    hg.integrable_smul_right_of_hasCompactSupport hφ.continuous hφc
  have hui : Integrable (fun x => u x*Laplacian.laplacian φ x) :=
    integrable_mul_compact (compactSupport_laplacian hφc) hu.continuousOn (continuous_laplacian hφ).continuousOn
  have hevent : ∀ᶠ R : ℝ in 𝓝[>] 0,
      (∫ x, u x*Laplacian.laplacian φ x) -
        (∫ x, u x*Laplacian.laplacian (fun y => φ y*ξ (R⁻¹ • y)) x) =
        -(∫ x, g x*φ x) + (∫ x, g x*(φ x*ξ (R⁻¹ • x))) := by
    filter_upwards [self_mem_nhdsWithin] with R hR
    have hχ : ContDiff ℝ 2 (fun x => φ x*ξ (R⁻¹ • x)) :=
      hφ.mul (ξ.contDiff.comp (contDiff_const.smul contDiff_id))
    have hχc : HasCompactSupport (fun x => φ x*ξ (R⁻¹ • x)) := hφc.mul_right
    have hχi : Integrable (fun x => u x*Laplacian.laplacian (fun y => φ y*ξ (R⁻¹ • y)) x) :=
      integrable_mul_compact (compactSupport_laplacian hχc) hu.continuousOn (continuous_laplacian hχ).continuousOn
    have hgi : Integrable (fun x => g x*(φ x*ξ (R⁻¹ • x))) :=
      hg.integrable_smul_right_of_hasCompactSupport hχ.continuous hχc
    obtain ⟨hψ,hψc,hψ0⟩ := cutoff_test_off_origin hφ hφc ξ hR
    have HH := heq _ hψ hψc hψ0
    have hid (x : E) : Laplacian.laplacian (fun y => φ y-φ y*ξ (R⁻¹ • y)) x =
        Laplacian.laplacian φ x-Laplacian.laplacian (fun y => φ y*ξ (R⁻¹ • y)) x :=
      hφ.contDiffAt.laplacian_sub hχ.contDiffAt
    simp_rw [hid,mul_sub] at HH
    rw [integral_sub hui hχi,integral_sub hi hgi] at HH
    linarith
  have hlim1 := (tendsto_const_nhds (x := ∫ x, u x*Laplacian.laplacian φ x)).sub (cutoff_laplacian_integral_tendsto_zero hn hu hφ ξ.contDiff ξ.hasCompactSupport)
  have hlim2 := (tendsto_const_nhds (x := -(∫ x, g x*φ x))).add (cutoff_source_integral_tendsto_zero hg hφ.continuous hφc ξ)
  have HH := tendsto_nhds_unique hlim1 (hlim2.congr' (Filter.EventuallyEq.symm hevent))
  simpa only [sub_zero,add_zero] using HH
end HenonLaneEmden.WeakPDE

end
end Distribution

end OAI
end

section
-- module Solutions.OAIQW_HenonLaneEmden.NewtonBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section NewtonBounds

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


namespace HenonLaneEmden
open WeakPDE

lemma IsSolution.dimension_ge_three {n : ℕ} (hn : 2 ≤ n) {p q A B : ℝ}
    {u v : Space n → ℝ} (h : IsSolution n p q A B u v) : 3 ≤ n := by
  by_contra hn3
  have hn2 : n = 2 := by omega
  subst n
  exact h.not_two_dimensional

lemma IsSolution.source_g_locallyIntegrable {n : ℕ} (hn : 2 ≤ n) {p q A B : ℝ}
    {u v : Space n → ℝ} (h : IsSolution n p q A B u v) : LocallyIntegrable (source v p A) :=
  locallyIntegrable_source (by omega) h.continuous_v h.positive_v p A (by
    have hA := h.first_weight_gt_neg_two hn
    have hnreal : (2:ℝ) ≤ n := by exact_mod_cast hn
    linarith)

lemma IsSolution.source_f_locallyIntegrable {n : ℕ} (hn : 2 ≤ n) {p q A B : ℝ}
    {u v : Space n → ℝ} (h : IsSolution n p q A B u v) : LocallyIntegrable (source u q B) :=
  h.swap.source_g_locallyIntegrable hn

lemma IsSolution.weak_u {n : ℕ} (hn : 2 ≤ n) {p q A B : ℝ}
    {u v : Space n → ℝ} (h : IsSolution n p q A B u v) {φ : Space n → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hφc : HasCompactSupport φ) :
    (∫ x, u x*Laplacian.laplacian φ x) = -(∫ x, source v p A x*φ x) :=
  distributional_extension (by simpa using h.dimension_ge_three hn) h.continuous_u
    (h.source_g_locallyIntegrable hn) (fun _ hψ hψc hψ0 => h.weak_u_off_origin hψ hψc hψ0) hφ hφc

lemma sphereArea_pos {n : ℕ} (hn : 1 ≤ n) : 0 < sphereArea n := by
  have : Nontrivial (Space n) := Module.nontrivial_of_finrank_pos (R := ℝ) (by simp only [finrank_euclideanSpace_fin]; omega)
  apply ENNReal.toReal_pos
  · exact (Measure.measure_univ_pos.mpr (Measure.toSphere_ne_zero volume)).ne'
  · exact measure_ne_top _ _

lemma newtonDenom_pos {n : ℕ} (hn : 3 ≤ n) : 0 < newtonDenom n := by
  apply mul_pos _ (sphereArea_pos (by omega))
  have hnreal : (3:ℝ) ≤ n := by exact_mod_cast hn
  linarith

lemma IsSolution.newton_lower_u {n : ℕ} (hn : 2 ≤ n) {p q A B : ℝ}
    {u v : Space n → ℝ} (h : IsSolution n p q A B u v) (x : Space n) :
    (∫⁻ y, ENNReal.ofReal (‖x-y‖^(2-(n:ℝ))*source v p A y)) ≤ ENNReal.ofReal (newtonDenom n*u x) := by
  have : Nontrivial (Space n) := Module.nontrivial_of_finrank_pos (R := ℝ) (by simp; omega)
  simpa only [finrank_euclideanSpace_fin,newtonDenom,sphereArea] using
    weak_newton_lower (by simpa using h.dimension_ge_three hn) h.continuous_u
      (h.source_g_locallyIntegrable hn) (regular_source h.regular_v h.positive_v p A).continuousOn
      (fun y => (h.positive_u y).le) (source_nonneg (fun y => (h.positive_v y).le) p A)
      (fun _ hφ hφc => h.weak_u hn hφ hφc) x

lemma IsSolution.kernel_g_integrable {n : ℕ} (hn : 2 ≤ n) {p q A B : ℝ}
    {u v : Space n → ℝ} (h : IsSolution n p q A B u v) (x : Space n) :
    Integrable (fun y => ‖x-y‖^(2-(n:ℝ))*source v p A y) := by
  refine ⟨(((continuous_const.sub continuous_id).norm.measurable.pow_const _).mul
    (measurable_source h.continuous_v p A)).aestronglyMeasurable,?_⟩
  apply (hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun y =>
    mul_nonneg (Real.rpow_nonneg (norm_nonneg (x-y)) _) (source_nonneg (fun z => (h.positive_v z).le) p A y))).mpr
  exact lt_of_le_of_lt (h.newton_lower_u hn x) ENNReal.ofReal_lt_top
end HenonLaneEmden

end
end NewtonBounds

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
lemma rawPotential_nonneg {g : E → ℝ} (hg : ∀ x, 0 ≤ g x) (x : E) : 0 ≤ rawPotential g x :=
  integral_nonneg fun y => mul_nonneg (Real.rpow_nonneg (norm_nonneg _) _) (hg y)

end HenonLaneEmden.WeakPDE

namespace HenonLaneEmden.WeakPDE
variable {E : Type uE4} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]

lemma potential_constant_raw (hn : 3 ≤ Module.finrank ℝ E) {u g : E → ℝ}
    (hu : Continuous u) (hg : Measurable g) (hgp : ∀ x, 0 ≤ g x)
    (hki : ∀ x, Integrable (fun y => ‖x-y‖^(2-(Module.finrank ℝ E:ℝ))*g y))
    (hlower : ∀ x, rawPotential g x ≤ ((Module.finrank ℝ E:ℝ)-2)*
      ((volume : Measure E).toSphere univ).toReal*u x)
    (heq : ∀ (φ : E → ℝ), ContDiff ℝ 2 φ → HasCompactSupport φ →
      (∫ y, u y*Laplacian.laplacian φ y) = -(∫ y, g y*φ y)) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ᵐ x, ((Module.finrank ℝ E:ℝ)-2)*
      ((volume : Measure E).toSphere univ).toReal*u x = rawPotential g x+c :=
  potential_constant hn hu hg hgp hki hlower heq
end HenonLaneEmden.WeakPDE

end
end NewtonPotential

end OAI
end

section
-- module Solutions.OAIQW_HenonLaneEmden.SourceMass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE

section SourceMass

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


namespace HenonLaneEmden
open WeakPDE
lemma IsSolution.rawPotential_lower_u {n : ℕ} (hn : 2 ≤ n) {p q A B : ℝ}
    {u v : Space n → ℝ} (h : IsSolution n p q A B u v) (x : Space n) :
    rawPotential (source v p A) x ≤ newtonDenom n*u x := by
  have hp : ∀ y, 0 ≤ ‖x-y‖^(2-(n:ℝ))*source v p A y := fun y =>
    mul_nonneg (Real.rpow_nonneg (norm_nonneg _) _) (source_nonneg (fun z => (h.positive_v z).le) p A y)
  have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top (h.newton_lower_u hn x)
  rw [ENNReal.toReal_ofReal (mul_nonneg (newtonDenom_pos (h.dimension_ge_three hn)).le (h.positive_u x).le),
    ← integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall hp) (h.kernel_g_integrable hn x).aestronglyMeasurable] at hh
  simpa only [rawPotential,finrank_euclideanSpace_fin] using hh

lemma IsSolution.potential_constant_u {n : ℕ} (hn : 2 ≤ n) {p q A B : ℝ}
    {u v : Space n → ℝ} (h : IsSolution n p q A B u v) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ᵐ x, newtonDenom n*u x = rawPotential (source v p A) x+c := by
  have : Nontrivial (Space n) := Module.nontrivial_of_finrank_pos (R := ℝ) (by simp; omega)
  simpa only [finrank_euclideanSpace_fin,newtonDenom,sphereArea] using
    potential_constant_raw (by simpa using h.dimension_ge_three hn) h.continuous_u
      (measurable_source h.continuous_v p A) (source_nonneg (fun y => (h.positive_v y).le) p A)
      (by simpa only [finrank_euclideanSpace_fin] using h.kernel_g_integrable hn)
      (by simpa only [finrank_euclideanSpace_fin,newtonDenom,sphereArea] using h.rawPotential_lower_u hn)
      (fun _ hφ hφc => h.weak_u hn hφ hφc)
end HenonLaneEmden

namespace HenonLaneEmden.WeakPDE
open scoped Pointwise
variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]

lemma rawPotential_ball_lower (hn : 3 ≤ Module.finrank ℝ E) {g : E → ℝ}
    (hg : LocallyIntegrable g) (hp : ∀ x, 0 ≤ g x)
    (hki : ∀ x, Integrable (fun y => ‖x-y‖^(2-(Module.finrank ℝ E:ℝ))*g y))
    {R : ℝ} (_hR : 0 < R) {x : E} (hx : x ∈ Metric.closedBall (0:E) R) :
    (2*R)^(2-(Module.finrank ℝ E:ℝ))*(∫ y in Metric.ball (0:E) R, g y) ≤ rawPotential g x := by
  have hgi : IntegrableOn g (Metric.ball (0:E) R) :=
    (hg.integrableOn_isCompact (isCompact_closedBall (0:E) R)).mono_set Metric.ball_subset_closedBall
  have h1 : (2*R)^(2-(Module.finrank ℝ E:ℝ))*(∫ y in Metric.ball (0:E) R, g y) ≤
      ∫ y in Metric.ball (0:E) R, ‖x-y‖^(2-(Module.finrank ℝ E:ℝ))*g y := by
    rw [← integral_const_mul]
    apply integral_mono_ae (hgi.const_mul _) (hki x).integrableOn
    filter_upwards [ae_restrict_mem measurableSet_ball,
      ae_restrict_of_ae (ae_iff.mpr (show volume {y : E | ¬ y ≠ x} = 0 by simp))] with y hy hyx
    apply mul_le_mul_of_nonneg_right _ (hp y)
    apply Real.rpow_le_rpow_of_nonpos (norm_pos_iff.mpr (sub_ne_zero.mpr (Ne.symm hyx)))
    · have hh := norm_sub_le x y
      have hx' : ‖x‖ ≤ R := by simpa using hx
      have hy' : ‖y‖ < R := by simpa using hy
      linarith
    · have hnreal : (3:ℝ) ≤ Module.finrank ℝ E := by exact_mod_cast hn
      linarith
  exact h1.trans (setIntegral_le_integral (hki x)
    (Eventually.of_forall fun y => mul_nonneg (Real.rpow_nonneg (norm_nonneg _) _) (hp y)))

omit [Nontrivial E] in
lemma ball_integral_dilation (f : E → ℝ) {R : ℝ} (hR : 0 < R) :
    (∫ x in Metric.ball (0:E) R, f x) = R^(Module.finrank ℝ E)*
      (∫ x in Metric.ball (0:E) 1, f (R • x)) := by
  have hs : R • Metric.ball (0:E) 1 = Metric.ball (0:E) R := by
    ext x
    rw [mem_smul_set_iff_inv_smul_mem₀ hR.ne']
    simp only [Metric.mem_ball,dist_zero_right,norm_smul,Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hR)]
    rw [inv_mul_lt_iff₀ hR,mul_one]
  have hh := Measure.setIntegral_comp_smul_of_pos volume f (Metric.ball (0:E) 1) hR
  rw [hs,smul_eq_mul] at hh
  rw [hh,mul_inv_cancel_left₀ (pow_ne_zero _ hR.ne')]

omit [Nontrivial E] in
lemma locallyIntegrable_norm_power (hn : 1 ≤ Module.finrank ℝ E) (a : ℝ)
    (ha : -(Module.finrank ℝ E:ℝ) < a) : LocallyIntegrable (fun x : E => ‖x‖^a) := by
  apply locallyIntegrable_of_norm_le_rpow hn (α := -a) (C := 1) ?_ ?_
    (measurable_norm.pow_const a).aestronglyMeasurable
  · linarith
  · filter_upwards [] with x
    simp [Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg (norm_nonneg x) a)]

omit [Nontrivial E] in
lemma integral_weight_ball_scaling (a : ℝ) {R : ℝ} (hR : 0 < R) :
    (∫ x in Metric.ball (0:E) R, ‖x‖^a) =
      R^((Module.finrank ℝ E:ℝ)+a)*(∫ x in Metric.ball (0:E) 1, ‖x‖^a) := by
  rw [ball_integral_dilation _ hR]
  simp only [norm_smul,Real.norm_eq_abs,abs_of_pos hR,Real.mul_rpow hR.le (norm_nonneg _),integral_const_mul]
  rw [← mul_assoc,← Real.rpow_natCast,← Real.rpow_add hR]

lemma integral_weight_ball_pos (hn : 1 ≤ Module.finrank ℝ E) (a : ℝ)
    (ha : -(Module.finrank ℝ E:ℝ) < a) {R : ℝ} (hR : 0 < R) :
    0 < ∫ x in Metric.ball (0:E) R, ‖x‖^a := by
  have hi : IntegrableOn (fun x : E => ‖x‖^a) (Metric.ball (0:E) R) :=
    ((locallyIntegrable_norm_power hn a ha).integrableOn_isCompact (isCompact_closedBall (0:E) R)).mono_set Metric.ball_subset_closedBall
  apply integral_pos_iff_support_of_nonneg_ae (Eventually.of_forall fun x => Real.rpow_nonneg (norm_nonneg x) a) hi |>.mpr
  have hz : ({0}ᶜ : Set E) ⊆ Function.support (fun x : E => ‖x‖^a) := by
    intro x hx
    exact ne_of_gt (Real.rpow_pos_of_pos (norm_pos_iff.mpr hx) a)
  apply lt_of_lt_of_le _ (measure_mono hz)
  rw [Measure.restrict_apply (measurableSet_singleton _).compl,
    inter_comm]
  change 0 < volume (Metric.ball (0:E) R \ {0})
  rw [measure_sdiff_null (by simp)]
  exact Metric.measure_ball_pos volume (0:E) hR
end HenonLaneEmden.WeakPDE

namespace HenonLaneEmden
open WeakPDE

lemma ballConstant_pos {n : ℕ} (hn : 3 ≤ n) : 0 < ballConstant n :=
  div_pos (Real.rpow_pos_of_pos (by norm_num) _) (newtonDenom_pos hn)

lemma weightMass_pos {n : ℕ} (hn : 3 ≤ n) {B : ℝ} (hB : -2 < B) : 0 < weightMass n B := by
  have : Nontrivial (Space n) := Module.nontrivial_of_finrank_pos (R := ℝ) (by simp; omega)
  apply integral_weight_ball_pos (by simpa using (show 1 ≤ n by omega)) B _ zero_lt_one
  simp only [finrank_euclideanSpace_fin]
  have hnreal : (3:ℝ) ≤ n := by exact_mod_cast hn
  linarith

lemma lowerMass_eq {n : ℕ} (u : Space n → ℝ) (q B : ℝ) {R : ℝ} (hR : 0 < R) :
    lowerMass u q B R = ballConstant n*R^(2-(n:ℝ))*sourceMass u q B R := by
  dsimp [lowerMass,ballConstant]
  rw [Real.mul_rpow (by norm_num) hR.le]
  ring

lemma IsSolution.lowerMass_g_le {n : ℕ} (hn : 2 ≤ n) {p q A B : ℝ}
    {u v : Space n → ℝ} (h : IsSolution n p q A B u v) {R : ℝ} (hR : 0 < R)
    {x : Space n} (hx : x ∈ Metric.closedBall (0:Space n) R) : lowerMass v p A R ≤ u x := by
  have : Nontrivial (Space n) := Module.nontrivial_of_finrank_pos (R := ℝ) (by simp; omega)
  have hh := rawPotential_ball_lower (by simpa using h.dimension_ge_three hn)
    (h.source_g_locallyIntegrable hn) (source_nonneg (fun y => (h.positive_v y).le) p A)
    (by simpa only [finrank_euclideanSpace_fin] using h.kernel_g_integrable hn) hR hx
  have hl := hh.trans (h.rawPotential_lower_u hn x)
  rw [lowerMass,div_mul_eq_mul_div]
  apply (div_le_iff₀ (newtonDenom_pos (h.dimension_ge_three hn))).mpr
  simpa only [finrank_euclideanSpace_fin,sourceMass,mul_comm (u x)] using hl

lemma integral_source_ge_lower {n : ℕ} (hn : 3 ≤ n) {u : Space n → ℝ} {q B R M : ℝ}
    (hu : Continuous u) (hup : ∀ x, 0 < u x) (hq : 0 ≤ q) (hB : -2 < B)
    (hR : 0 < R) (hM : 0 ≤ M) (hbound : ∀ x ∈ Metric.ball (0:Space n) R, M ≤ u x) :
    M^q*R^((n:ℝ)+B)*weightMass n B ≤ sourceMass u q B R := by
  have : Nontrivial (Space n) := Module.nontrivial_of_finrank_pos (R := ℝ) (by simp; omega)
  have hBn : -(n:ℝ) < B := by
    have hnreal : (3:ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hdim : 1 ≤ Module.finrank ℝ (Space n) := by simp; omega
  have hi : IntegrableOn (source u q B) (Metric.ball (0:Space n) R) :=
    ((locallyIntegrable_source (by omega) hu hup q B hBn).integrableOn_isCompact (isCompact_closedBall _ R)).mono_set Metric.ball_subset_closedBall
  have hw : IntegrableOn (fun x : Space n => ‖x‖^B) (Metric.ball (0:Space n) R) :=
    ((locallyIntegrable_norm_power hdim B (by simpa using hBn)).integrableOn_isCompact (isCompact_closedBall _ R)).mono_set Metric.ball_subset_closedBall
  have hscale : R^((n:ℝ)+B)*weightMass n B = ∫ x in Metric.ball (0:Space n) R, ‖x‖^B := by
    simpa only [weightMass,finrank_euclideanSpace_fin] using (integral_weight_ball_scaling (E := Space n) B hR).symm
  rw [mul_assoc,hscale]
  rw [← integral_const_mul]
  apply integral_mono_ae (hw.const_mul _) hi
  filter_upwards [ae_restrict_mem measurableSet_ball,
    ae_restrict_of_ae (ae_iff.mpr (show volume {x : Space n | ¬ x ≠ 0} = 0 by simp))] with x hx hx0
  rw [source_off_zero u q B hx0,mul_comm]
  exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hM (hbound x hx) hq) (Real.rpow_nonneg (norm_nonneg _) _)

end HenonLaneEmden

end
end SourceMass

end OAI
end

section
-- module Solutions.OAIQW_HenonLaneEmden.ProductBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section ProductBounds

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


namespace HenonLaneEmden
open WeakPDE
lemma IsSolution.no_positive_lower_bound_u {n : ℕ} (hn : 2 ≤ n) {p q A B : ℝ}
    {u v : Space n → ℝ} (h : IsSolution n p q A B u v) (hq : 0 < q)
    {M : ℝ} (hM : 0 < M) (hbound : ∀ x, M ≤ u x) : False := by
  have hn3 := h.dimension_ge_three hn
  have hB := h.swap.first_weight_gt_neg_two hn
  have hc := ballConstant_pos hn3
  have hw := weightMass_pos hn3 hB
  have hb (R : ℝ) (hR : 0 < R) :
      ballConstant n*weightMass n B*M^q*R^(2+B) ≤ v 0 := by
    have hh := integral_source_ge_lower hn3 h.continuous_u h.positive_u hq.le hB hR hM.le
      (fun x _ => hbound x)
    have hh' := mul_le_mul_of_nonneg_left hh
      (mul_nonneg hc.le (Real.rpow_nonneg hR.le (2-(n:ℝ))))
    have he : R^(2+B) = R^(2-(n:ℝ))*R^((n:ℝ)+B) := by
      rw [← Real.rpow_add hR]; congr 1; ring
    have hl : ballConstant n*weightMass n B*M^q*R^(2+B) ≤ lowerMass u q B R := by
      rw [lowerMass_eq _ _ _ hR,he]
      nlinarith only [hh']
    exact hl.trans (h.swap.lowerMass_g_le hn hR (by simpa using hR.le))
  have ht : Tendsto (fun R : ℝ => ballConstant n*weightMass n B*M^q*R^(2+B)) atTop atTop :=
    (tendsto_rpow_atTop (show 0 < 2+B by linarith)).const_mul_atTop
      (mul_pos (mul_pos hc hw) (Real.rpow_pos_of_pos hM q))
  obtain ⟨R,hR,hgt⟩ := ((eventually_gt_atTop (0:ℝ)).and
    (ht.eventually (eventually_gt_atTop (v 0)))).exists
  exact (not_lt_of_ge (hb R hR)) hgt

lemma IsSolution.potential_u_ae {n : ℕ} (hn : 2 ≤ n) {p q A B : ℝ}
    {u v : Space n → ℝ} (h : IsSolution n p q A B u v) (hq : 0 < q) :
    ∀ᵐ x, newtonDenom n*u x = rawPotential (source v p A) x := by
  obtain ⟨c,hc,hceq⟩ := h.potential_constant_u hn
  have hc0 : c = 0 := by
    by_contra hh
    have hcp : 0 < c := lt_of_le_of_ne hc (Ne.symm hh)
    have hD := newtonDenom_pos (h.dimension_ge_three hn)
    have hb : ∀ᵐ x, c/newtonDenom n ≤ u x := by
      filter_upwards [hceq] with x hx
      apply (div_le_iff₀ hD).mpr
      have hp := rawPotential_nonneg (source_nonneg (fun y => (h.positive_v y).le) p A) x
      nlinarith only [hx,hp]
    have heq : (fun x => max (c/newtonDenom n) (u x)) = u :=
      Measure.eq_of_ae_eq (hb.mono fun _ hx => max_eq_right hx)
        (continuous_const.max h.continuous_u) h.continuous_u
    exact h.no_positive_lower_bound_u hn hq (div_pos hcp hD)
      (fun x => max_eq_right_iff.mp (congrFun heq x))
  simpa only [hc0,add_zero] using hceq
end HenonLaneEmden

end
end ProductBounds

end OAI
end

section
-- module Solutions.OAIQW_HenonLaneEmden.PotentialContinuity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE

section PotentialContinuity

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

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
lemma rpow_kernel_shift_bound {a r : ℝ} (ha : a ≤ 0) (hr : 0 < r) {x x₀ y : E}
    (hx : ‖x-x₀‖ < r/2) (hy : r ≤ ‖x₀-y‖) :
    ‖x-y‖^a ≤ (1/2:ℝ)^a*‖x₀-y‖^a := by
  have ht := norm_sub_le (x₀-x) (y-x)
  simp only [sub_sub_sub_cancel_right, norm_sub_rev y x] at ht
  rw [norm_sub_rev x₀ x] at ht
  have hp : 0 < ‖x₀-y‖/2 := by linarith
  have hl : ‖x₀-y‖/2 ≤ ‖x-y‖ := by linarith
  have hh := Real.rpow_le_rpow_of_nonpos hp hl ha
  have he : ‖x₀-y‖/2 = (1/2:ℝ)*‖x₀-y‖ := by ring
  rwa [he,Real.mul_rpow (by norm_num) (norm_nonneg _)] at hh

omit [Nontrivial E] in
lemma continuousAt_far_rawPotential (hn : 3 ≤ Module.finrank ℝ E) {g : E → ℝ}
    (hg : Measurable g) (hgp : ∀ y, 0 ≤ g y) {x₀ : E} {r : ℝ} (hr : 0 < r)
    (hzero : ∀ y ∈ Metric.ball x₀ r, g y = 0)
    (hi : Integrable (fun y => ‖x₀-y‖^(2-(Module.finrank ℝ E:ℝ))*g y)) :
    ContinuousAt (rawPotential g) x₀ := by
  let a := 2-(Module.finrank ℝ E:ℝ)
  have ha : a ≤ 0 := by
    have hd : (3:ℝ) ≤ Module.finrank ℝ E := by exact_mod_cast hn
    dsimp [a]; linarith
  apply continuousAt_of_dominated (bound := fun y => (1/2:ℝ)^a*(‖x₀-y‖^a*g y))
  · exact Eventually.of_forall fun x =>
      (((measurable_const.sub measurable_id).norm.pow_const a).mul hg).aestronglyMeasurable
  · filter_upwards [Metric.ball_mem_nhds x₀ (half_pos hr)] with x hx
    apply Eventually.of_forall
    intro y
    by_cases hy : y ∈ Metric.ball x₀ r
    · simp [hzero y hy]
    · have hyr : r ≤ ‖x₀-y‖ := by
        have hy' : ¬ ‖y-x₀‖ < r := by simpa only [Metric.mem_ball,dist_eq_norm] using hy
        simpa only [norm_sub_rev] using le_of_not_gt hy'
      have hxr : ‖x-x₀‖ < r/2 := by simpa only [Metric.mem_ball,dist_eq_norm] using hx
      rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (Real.rpow_nonneg (norm_nonneg _) _) (hgp y))]
      exact (mul_le_mul_of_nonneg_right (rpow_kernel_shift_bound ha hr hxr hyr) (hgp y)).trans_eq (mul_assoc _ _ _)
  · exact hi.const_mul _
  · apply Eventually.of_forall
    intro y
    by_cases hy : y = x₀
    · subst y
      have hg0 := hzero x₀ (Metric.mem_ball_self hr)
      simp only [hg0,mul_zero]
      exact continuousAt_const
    · exact (((continuousAt_id.sub continuousAt_const).norm).rpow_const
        (Or.inl (norm_ne_zero_iff.mpr (sub_ne_zero.mpr (Ne.symm hy))))).mul continuousAt_const

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
lemma continuous_mul_cutoff {g ξ : E → ℝ} {s : Set E} (hs : IsOpen s)
    (hg : ContinuousOn g s) (hξ : Continuous ξ) (hξs : tsupport ξ ⊆ s) :
    Continuous (fun y => ξ y*g y) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  by_cases hx : x ∈ tsupport ξ
  · exact hξ.continuousAt.mul (hg.continuousAt (hs.mem_nhds (hξs hx)))
  · apply (continuousAt_const (y := (0:ℝ))).congr_of_eventuallyEq
    filter_upwards [(isClosed_tsupport ξ).isOpen_compl.mem_nhds hx] with y hy
    simp only [image_eq_zero_of_notMem_tsupport hy,zero_mul]

omit [Nontrivial E] in
lemma rawPotential_integrable_cutoff {g ξ : E → ℝ} (hg : Measurable g) (hgp : ∀ x, 0 ≤ g x)
    (hξ : Measurable ξ) (hξp : ∀ x, 0 ≤ ξ x) (hξ1 : ∀ x, ξ x ≤ 1) {x : E}
    (hi : Integrable (fun y => ‖x-y‖^(2-(Module.finrank ℝ E:ℝ))*g y)) :
    Integrable (fun y => ‖x-y‖^(2-(Module.finrank ℝ E:ℝ))*(ξ y*g y)) := by
  apply hi.mono' ((((measurable_const.sub measurable_id).norm.pow_const _).mul (hξ.mul hg)).aestronglyMeasurable)
  apply Eventually.of_forall
  intro y
  change ‖‖x-y‖^(2-(Module.finrank ℝ E:ℝ))*(ξ y*g y)‖ ≤ _
  rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (Real.rpow_nonneg (norm_nonneg _) _) (mul_nonneg (hξp y) (hgp y)))]
  exact mul_le_mul_of_nonneg_left ((mul_le_mul_of_nonneg_right (hξ1 y) (hgp y)).trans_eq (one_mul _))
    (Real.rpow_nonneg (norm_nonneg _) _)

omit [Nontrivial E] in
lemma continuousOn_rawPotential (hn : 3 ≤ Module.finrank ℝ E) {g : E → ℝ} {s : Set E}
    (hg : Measurable g) (hgp : ∀ x, 0 ≤ g x) (hs : IsOpen s) (hgc : ContinuousOn g s)
    (hi : ∀ x, Integrable (fun y => ‖x-y‖^(2-(Module.finrank ℝ E:ℝ))*g y)) :
    ContinuousOn (rawPotential g) s := by
  intro x₀ hx₀
  obtain ⟨r,hr,hrs⟩ := Metric.mem_nhds_iff.mp (hs.mem_nhds hx₀)
  let ξ : ContDiffBump x₀ := ⟨r/4,r/2,by linarith,by linarith⟩
  have hξs : tsupport ξ ⊆ s := by
    apply Subset.trans (by rw [ξ.tsupport_eq] : tsupport ξ ⊆ Metric.closedBall x₀ ξ.rOut)
    intro y hy
    apply hrs
    have hy' : dist y x₀ ≤ r/2 := hy
    change dist y x₀ < r
    linarith
  let g₀ : E → ℝ := fun y => ξ y*g y
  let g₁ : E → ℝ := fun y => (1-ξ y)*g y
  have hg₀c : Continuous g₀ := continuous_mul_cutoff hs hgc ξ.continuous hξs
  have hg₀k : HasCompactSupport g₀ := ξ.hasCompactSupport.mul_right
  have hK : LocallyIntegrable (fun y : E => ‖y‖^(2-(Module.finrank ℝ E:ℝ))) :=
    locallyIntegrable_norm_power (by omega) _ (by linarith)
  have hlocal : Continuous (rawPotential g₀) := by
    have hh := hg₀k.continuous_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ) hg₀c hK
    convert hh using 1
    ext x
    simp only [rawPotential,convolution_def,ContinuousLinearMap.lsmul_apply,smul_eq_mul,mul_comm (g₀ _)]
  have hg₁m : Measurable g₁ := (measurable_const.sub ξ.continuous.measurable).mul hg
  have hg₁p : ∀ y, 0 ≤ g₁ y := fun y => mul_nonneg (sub_nonneg.mpr (ξ.le_one (x := y))) (hgp y)
  have hi₀ (x : E) := rawPotential_integrable_cutoff hg hgp ξ.continuous.measurable
    (fun _ => ξ.nonneg) (fun _ => ξ.le_one) (hi x)
  have hi₁ (x : E) : Integrable (fun y => ‖x-y‖^(2-(Module.finrank ℝ E:ℝ))*((1-ξ y)*g y)) := by
    simpa only [Pi.sub_apply] using rawPotential_integrable_cutoff hg hgp
      (measurable_const.sub ξ.continuous.measurable) (fun y => sub_nonneg.mpr (ξ.le_one (x := y)))
      (fun y => by change 1-ξ y ≤ 1; linarith [ξ.nonneg (x := y)]) (hi x)
  have hfar : ContinuousAt (rawPotential g₁) x₀ := by
    apply continuousAt_far_rawPotential hn hg₁m hg₁p (r := r/4) (by linarith) ?_ (hi₁ x₀)
    intro y hy
    have heq : ξ y = 1 := ξ.one_of_mem_closedBall (Metric.ball_subset_closedBall hy)
    simp [g₁,heq]
  have heq : rawPotential g = fun x => rawPotential g₀ x+rawPotential g₁ x := by
    ext x
    change (∫ y, ‖x-y‖^(2-(Module.finrank ℝ E:ℝ))*g y) =
      (∫ y, ‖x-y‖^(2-(Module.finrank ℝ E:ℝ))*(ξ y*g y)) +
      (∫ y, ‖x-y‖^(2-(Module.finrank ℝ E:ℝ))*((1-ξ y)*g y))
    rw [← integral_add (hi₀ x) (hi₁ x)]
    apply integral_congr_ae
    apply Eventually.of_forall
    intro y
    dsimp [g₀,g₁]
    ring
  rw [heq]
  exact (hlocal.continuousAt.add hfar).continuousWithinAt
end HenonLaneEmden.WeakPDE

namespace HenonLaneEmden
open WeakPDE
lemma IsSolution.potential_u {n : ℕ} (hn : 2 ≤ n) {p q A B : ℝ}
    {u v : Space n → ℝ} (h : IsSolution n p q A B u v) (hq : 0 < q)
    {x : Space n} (hx : x ≠ 0) :
    newtonDenom n*u x = rawPotential (source v p A) x := by
  apply Measure.eqOn_open_of_ae_eq (ae_restrict_of_ae (h.potential_u_ae hn hq))
    isOpen_compl_singleton (continuous_const.mul h.continuous_u).continuousOn ?_ hx
  apply continuousOn_rawPotential (by simpa using h.dimension_ge_three hn)
    (measurable_source h.continuous_v p A) (source_nonneg (fun y => (h.positive_v y).le) p A)
    isOpen_compl_singleton
  · exact (regular_source h.regular_v h.positive_v p A).continuousOn
  · simpa only [finrank_euclideanSpace_fin] using h.kernel_g_integrable hn
end HenonLaneEmden

end
end PotentialContinuity

end OAI
end

section
-- module Solutions.OAIQW_HenonLaneEmden.Cutoff
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE

section Cutoff

open MeasureTheory Set Metric Filter Topology
noncomputable section
namespace HenonLaneEmden.Cutoff

lemma hasDerivAt_posPow {k : ℕ} (hk : 2 ≤ k) (r : ℝ) :
    HasDerivAt (posPow k) ((k:ℝ)*(max r 0)^(k-1)) r := by
  rcases lt_trichotomy r 0 with hr|rfl|hr
  · have he : posPow k =ᶠ[𝓝 r] (fun _ => (0:ℝ)) := by
      filter_upwards [eventually_lt_nhds hr] with t ht
      simp [posPow,max_eq_right ht.le,show k ≠ 0 by omega]
    simpa [max_eq_right hr.le,show k-1 ≠ 0 by omega] using
      (hasDerivAt_const r (0:ℝ)).congr_of_eventuallyEq he
  · have hleft : HasDerivWithinAt (posPow k) 0 (Iic (0:ℝ)) 0 := by
      apply (hasDerivWithinAt_const 0 (Iic (0:ℝ)) (0:ℝ)).congr
      · intro t ht; simp [posPow,max_eq_right (mem_Iic.mp ht),show k ≠ 0 by omega]
      · simp [posPow,show k ≠ 0 by omega]
    have hright : HasDerivWithinAt (posPow k) 0 (Ici (0:ℝ)) 0 := by
      have hp : HasDerivWithinAt (fun t : ℝ => t^k) 0 (Ici (0:ℝ)) 0 := by
        simpa [show k-1 ≠ 0 by omega] using (hasDerivAt_pow k (0:ℝ)).hasDerivWithinAt (s := Ici (0:ℝ))
      apply hp.congr
      · intro t ht; simp [posPow,max_eq_left (mem_Ici.mp ht)]
      · simp [posPow]
    have hh := hleft.union hright
    rw [Iic_union_Ici,hasDerivWithinAt_univ] at hh
    simpa [show k-1 ≠ 0 by omega] using hh
  · have he : posPow k =ᶠ[𝓝 r] (fun t => t^k) := by
      filter_upwards [eventually_gt_nhds hr] with t ht
      simp [posPow,max_eq_left ht.le]
    simpa [max_eq_left hr.le] using (hasDerivAt_pow k r).congr_of_eventuallyEq he

lemma N_ge_two (n : ℕ) : 2 ≤ N n := by unfold N; omega
lemma N_ge_three {n : ℕ} (hn : 1 ≤ n) : 3 ≤ N n := by unfold N; omega

lemma continuous_etaProfile (n : ℕ) : Continuous (etaProfile n) := by
  unfold etaProfile posPow; fun_prop
lemma continuous_derivativeProfile (n : ℕ) : Continuous (derivativeProfile n) := by
  unfold derivativeProfile baseProfile posPow; fun_prop
lemma continuous_wProfile (n : ℕ) : Continuous (wProfile n) := by
  unfold wProfile; exact continuous_id.neg.mul (continuous_derivativeProfile n)

lemma hasDerivAt_etaProfile (n : ℕ) (r : ℝ) :
    HasDerivAt (etaProfile n) (derivativeProfile n r) r := by
  have h1 := (hasDerivAt_posPow (by omega : 2 ≤ 3) (r-1)).comp r
    ((hasDerivAt_id r).sub_const 1)
  have h2 := (hasDerivAt_posPow (N_ge_two n) (1-posPow 3 (r-1))).comp r (h1.const_sub 1)
  apply h2.congr_deriv
  simp only [derivativeProfile,baseProfile,Nat.cast_ofNat,mul_one,Nat.reduceSub]
  ring

lemma baseProfile_nonneg (r : ℝ) : 0 ≤ baseProfile r := le_max_right _ _
lemma baseProfile_outer {r : ℝ} (hr : 2 ≤ r) : baseProfile r = 0 := by
  have hp : 1 ≤ (max (r-1) 0)^3 := one_le_pow₀ (by linarith [le_max_left (r-1) 0])
  exact max_eq_right (by dsimp [posPow]; linarith)
lemma derivativeProfile_outer (n : ℕ) {r : ℝ} (hr : 2 ≤ r) : derivativeProfile n r = 0 := by
  simp [derivativeProfile,baseProfile_outer hr,show N n-1 ≠ 0 by have := N_ge_two n; omega]
lemma derivativeProfile_nonpos (n : ℕ) (r : ℝ) : derivativeProfile n r ≤ 0 := by
  have hb := baseProfile_nonneg r
  unfold derivativeProfile
  exact neg_nonpos.mpr (by positivity)
lemma wProfile_nonneg (n : ℕ) {r : ℝ} (hr : 0 ≤ r) : 0 ≤ wProfile n r :=
  mul_nonneg_of_nonpos_of_nonpos (neg_nonpos.mpr hr) (derivativeProfile_nonpos n r)

lemma continuous_secondProfile (n : ℕ) : Continuous (secondProfile n) := by
  unfold secondProfile baseProfile posPow; fun_prop

lemma hasDerivAt_derivativeProfile {n : ℕ} (hn : 1 ≤ n) (r : ℝ) :
    HasDerivAt (derivativeProfile n) (secondProfile n r) r := by
  have hN := N_ge_three hn
  have h1 := (hasDerivAt_posPow (by omega : 2 ≤ 3) (r-1)).comp r
    ((hasDerivAt_id r).sub_const 1)
  have h2 := (hasDerivAt_posPow (by omega : 2 ≤ N n-1) (1-posPow 3 (r-1))).comp r
    (h1.const_sub 1)
  have h3 := (hasDerivAt_posPow (by omega : 2 ≤ 2) (r-1)).comp r
    ((hasDerivAt_id r).sub_const 1)
  have hh := ((h3.const_mul (3*(N n:ℝ))).mul h2).neg
  apply hh.congr_deriv
  simp only [Function.comp_def, id_eq, posPow,Nat.cast_ofNat,mul_one,Nat.reduceSub,pow_one,
    show N n-1-1 = N n-2 by omega]
  rw [Nat.cast_sub (by omega : 1 ≤ N n)]
  simp only [Nat.cast_one,secondProfile,baseProfile,posPow]
  ring

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

omit [InnerProductSpace ℝ E] in
lemma continuous_eta (n : ℕ) : Continuous (eta n : E → ℝ) :=
  (continuous_etaProfile n).comp continuous_norm
omit [InnerProductSpace ℝ E] in
lemma eta_eq_one {n : ℕ} {x : E} (hx : ‖x‖ ≤ 1) : eta n x = 1 := by
  simp [eta,etaProfile,posPow,max_eq_right (by linarith : ‖x‖-1 ≤ 0)]
omit [InnerProductSpace ℝ E] in
lemma eta_eq_zero {n : ℕ} {x : E} (hx : 2 ≤ ‖x‖) : eta n x = 0 := by
  have hs : 1 ≤ (max (‖x‖-1) 0)^3 := by
    exact one_le_pow₀ (by linarith [le_max_left (‖x‖-1) 0])
  simp [eta,etaProfile,posPow,max_eq_right (by linarith : 1-(max (‖x‖-1) 0)^3 ≤ 0),
    show N n ≠ 0 by have := N_ge_two n; omega]

lemma hasFDerivAt_eta (n : ℕ) (x : E) :
    HasFDerivAt (eta n) ((derivativeProfile n ‖x‖/‖x‖) • innerSL ℝ x) x := by
  by_cases hx : x = 0
  · subst x
    have he : (eta n : E → ℝ) =ᶠ[𝓝 0] (fun _ => (1:ℝ)) := by
      filter_upwards [Metric.ball_mem_nhds (0:E) (by norm_num : (0:ℝ)<1)] with y hy
      exact eta_eq_one (mem_ball_zero_iff.mp hy).le
    simpa using (hasFDerivAt_const (1:ℝ) (0:E)).congr_of_eventuallyEq he
  · exact RadialCalculus.hasFDerivAt_profile_norm hx (hasDerivAt_etaProfile n ‖x‖)

lemma w_eq_profile (n : ℕ) (x : E) : w n x = wProfile n ‖x‖ := by
  rw [w,(hasFDerivAt_eta n x).fderiv]
  simp only [smul_apply,innerSL_apply_apply,smul_eq_mul,real_inner_self_eq_norm_sq,wProfile]
  by_cases hx : x = 0
  · subst x; simp
  · have hn := norm_ne_zero_iff.mpr hx
    field_simp

lemma continuous_w (n : ℕ) : Continuous (w n : E → ℝ) := by
  rw [show (w n : E → ℝ) = fun x => wProfile n ‖x‖ from funext (w_eq_profile n)]
  exact (continuous_wProfile n).comp continuous_norm

end HenonLaneEmden.Cutoff
end
end Cutoff

end OAI
end

section
-- module Solutions.OAIQW_HenonLaneEmden.AdaptiveCaps
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE

section AdaptiveCaps

open MeasureTheory Set Metric NormedSpace
noncomputable section
namespace HenonLaneEmden.AdaptiveCap
open Cutoff CapWeights

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]
  (μ : Measure E) [μ.IsAddHaarMeasure]

omit [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E] in
lemma w_nonneg (n : ℕ) (x : E) : 0 ≤ w n x := by
  rw [w_eq_profile]; exact wProfile_nonneg n (norm_nonneg x)
omit [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E] in
lemma w_outer (n : ℕ) {x : E} (hx : 2 ≤ ‖x‖) : w n x = 0 := by
  rw [w_eq_profile,wProfile,derivativeProfile_outer n hx,mul_zero]

end HenonLaneEmden.AdaptiveCap
end
end AdaptiveCaps

end OAI
end

section
-- module Solutions.OAIQW_HenonLaneEmden.Energy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Energy
open MeasureTheory Set Filter Topology Metric
open scoped ENNReal
namespace HenonLaneEmden

lemma energyDensity_eq_source_mul {n : ℕ} {u : Space n → ℝ}
    (hu : ∀ x, 0 < u x) (q B : ℝ) {x : Space n} (hx : x ≠ 0) :
    energyDensity u q B x = source u q B x * u x := by
  rw [energyDensity,source_off_zero _ _ _ hx,Real.rpow_add (hu x),Real.rpow_one,mul_assoc]

lemma IsSolution.energy_locallyIntegrable {n : ℕ} (hn : 2 ≤ n) {p q A B : ℝ}
    {u v : Space n → ℝ} (h : IsSolution n p q A B u v) :
    LocallyIntegrable (energyDensity u q B) := by
  have : Nontrivial (Space n) := Module.nontrivial_of_finrank_pos (R := ℝ) (by simp; omega)
  have hi := (h.source_f_locallyIntegrable hn).mul_continuous h.continuous_u
  apply hi.congr
  filter_upwards [ae_iff.mpr (by simp : volume {x : Space n | ¬ x ≠ 0} = 0)] with x hx
  exact (energyDensity_eq_source_mul h.positive_u q B hx).symm

end HenonLaneEmden
end Energy

end OAI
end

section
-- module Solutions.OAIQW_HenonLaneEmden.Interaction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Interaction

open MeasureTheory Set Filter Topology Metric
open scoped ENNReal
noncomputable section
namespace HenonLaneEmden
open LayerTonelli

lemma newtonKernel_nonneg {n : ℕ} (hn : 3 ≤ n) (z : Space n × Space n) :
    0 ≤ newtonKernel n z :=
  mul_nonneg (inv_nonneg.mpr (newtonDenom_pos hn).le) (Real.rpow_nonneg (norm_nonneg _) _)

lemma IsSolution.newton_potential_u {n : ℕ} (hn : 2 ≤ n) {p q A B : ℝ}
    {u v : Space n → ℝ} (h : IsSolution n p q A B u v) (hq : 0 < q)
    {x : Space n} (hx : x ≠ 0) :
    potential volume (fun z => ENNReal.ofReal (newtonKernel n z)) (source v p A) x =
      ENNReal.ofReal (u x) := by
  have hd := newtonDenom_pos (h.dimension_ge_three hn)
  have hgm := measurable_source h.continuous_v p A
  unfold potential newtonKernel
  simp_rw [ENNReal.ofReal_mul (inv_nonneg.mpr hd.le),mul_left_comm (ENNReal.ofReal (source v p A _))]
  rw [lintegral_const_mul _ (by fun_prop)]
  have hi := ofReal_integral_eq_lintegral_ofReal (h.kernel_g_integrable hn x)
    (ae_of_all _ fun y => mul_nonneg (Real.rpow_nonneg (norm_nonneg _) _)
      (source_nonneg (fun y => (h.positive_v y).le) p A y))
  have he : (∫⁻ y, ENNReal.ofReal (source v p A y)*ENNReal.ofReal (‖x-y‖^(2-(n:ℝ)))) =
      ENNReal.ofReal (newtonDenom n*u x) := by
    rw [h.potential_u hn hq hx]
    simp only [WeakPDE.rawPotential,finrank_euclideanSpace_fin]
    rw [hi]
    apply lintegral_congr
    intro y
    rw [ENNReal.ofReal_mul (Real.rpow_nonneg (norm_nonneg _) _),mul_comm]
  rw [he,← ENNReal.ofReal_mul (inv_nonneg.mpr hd.le)]
  congr 1
  field_simp

lemma IsSolution.newton_potential_u_ae {n : ℕ} (hn : 2 ≤ n) {p q A B : ℝ}
    {u v : Space n → ℝ} (h : IsSolution n p q A B u v) (hq : 0 < q) :
    ∀ᵐ x, potential volume (fun z => ENNReal.ofReal (newtonKernel n z)) (source v p A) x =
      ENNReal.ofReal (u x) := by
  have : Nontrivial (Space n) := Module.nontrivial_of_finrank_pos (R := ℝ) (by simp; omega)
  filter_upwards [ae_iff.mpr (by simp : volume {x : Space n | ¬ x ≠ 0}=0)] with x hx
  exact h.newton_potential_u hn hq hx

lemma lintegral_interaction {n : ℕ} {f g : Space n → ℝ}
    (hf : Measurable f) (hg : Measurable g) {F : Space n × Space n → ℝ≥0∞}
    (hF : Measurable F) :
    (∫⁻ z, F z ∂interaction f g) =
      ∫⁻ z, ENNReal.ofReal (f z.1)*ENNReal.ofReal (g z.2)*ENNReal.ofReal (newtonKernel n z)*F z ∂volume.prod volume :=
  lintegral_withDensity_eq_lintegral_mul _ (by fun_prop [measurable_newtonKernel]) hF

lemma lintegral_interaction_left {n : ℕ} {f g : Space n → ℝ}
    (hf : Measurable f) (hg : Measurable g) {F : Space n → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ z, F z.1 ∂interaction f g) = ∫⁻ x, ENNReal.ofReal (f x)*F x*
      potential volume (fun z => ENNReal.ofReal (newtonKernel n z)) g x := by
  rw [lintegral_interaction hf hg (by fun_prop),lintegral_prod _ (by fun_prop [measurable_newtonKernel])]
  apply lintegral_congr
  intro x
  have he (y : Space n) :
      ENNReal.ofReal (f x)*ENNReal.ofReal (g y)*ENNReal.ofReal (newtonKernel n (x,y))*F x =
      (ENNReal.ofReal (f x)*F x)*(ENNReal.ofReal (g y)*ENNReal.ofReal (newtonKernel n (x,y))) := by ring
  simp_rw [he]
  rw [lintegral_const_mul _ (by fun_prop [measurable_newtonKernel])]
  rfl

lemma IsSolution.interaction_left {n : ℕ} (hn : 2 ≤ n) {p q A B : ℝ}
    {u v : Space n → ℝ} (h : IsSolution n p q A B u v) (hq : 0 < q)
    {F : Space n → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ z, F z.1 ∂interaction (source u q B) (source v p A)) =
      ∫⁻ x, ENNReal.ofReal (source u q B x*u x)*F x := by
  rw [lintegral_interaction_left (measurable_source h.continuous_u q B) (measurable_source h.continuous_v p A) hF]
  apply lintegral_congr_ae
  filter_upwards [h.newton_potential_u_ae hn hq] with x hx
  rw [hx,ENNReal.ofReal_mul (source_nonneg (fun x => (h.positive_u x).le) q B x)]
  ring

end HenonLaneEmden
end
end Interaction

end OAI
end

section
-- module Solutions.OAIQW_HenonLaneEmden.PairPressure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE uE2 uE3 uE4

section PairPressure

open MeasureTheory Set Metric
open scoped ENNReal InnerProductSpace
noncomputable section
namespace HenonLaneEmden
open LineCoordinates

lemma directionalFactor_bounds {E : Type uE3} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (e : sphere (0:E) 1) (z : E × E) : 0 ≤ directionalFactor e z ∧ directionalFactor e z ≤ 1 := by
  have hh : |inner ℝ (e:E) (z.1-z.2)| ≤ ‖z.1-z.2‖ := by
    simpa only [norm_unit,one_mul] using abs_real_inner_le_norm (e:E) (z.1-z.2)
  refine ⟨by unfold directionalFactor; positivity,?_⟩
  unfold directionalFactor
  by_cases hz : z.1-z.2=0
  · simp [hz]
  · apply (div_le_one (sq_pos_of_pos (norm_pos_iff.mpr hz))).mpr
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) (norm_nonneg _)).mpr hh

end HenonLaneEmden
end
end PairPressure

end OAI
end

section
-- module Solutions.OAIQW_HenonLaneEmden.WeightedEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section WeightedEnergy

open MeasureTheory Set Metric
open scoped ENNReal
noncomputable section
namespace HenonLaneEmden
open Cutoff AdaptiveCap

lemma compactSupport_of_outer_zero {n : ℕ} {F : Space n → ℝ}
    (hF : ∀ x, 2 ≤ ‖x‖ → F x=0) : HasCompactSupport F := by
  apply HasCompactSupport.intro (K := closedBall 0 2) (isCompact_closedBall _ _)
  intro x hx
  exact hF x (not_lt.mp (fun hh => hx (mem_closedBall_zero_iff.mpr hh.le)))

lemma compactSupport_eta (n : ℕ) : HasCompactSupport (eta n : Space n → ℝ) :=
  compactSupport_of_outer_zero (fun _ hx => eta_eq_zero hx)
lemma compactSupport_w (n : ℕ) : HasCompactSupport (w n : Space n → ℝ) :=
  compactSupport_of_outer_zero (fun _ hx => w_outer n hx)

lemma IsSolution.integrable_source_energy_weight {n : ℕ} (hn : 2 ≤ n) {p q A B : ℝ}
    {u v χ : Space n → ℝ} (h : IsSolution n p q A B u v)
    (hχ : Continuous χ) (hχc : HasCompactSupport χ) :
    Integrable (fun x => χ x*source u q B x*u x) := by
  have hl := ((h.source_f_locallyIntegrable hn).mul_continuous h.continuous_u).mul_continuous hχ
  have hi := hl.integrableOn_isCompact hχc
  apply (integrableOn_iff_integrable_of_support_subset ?_).mp
    (hi.congr_fun (fun x _ => by ring) (isClosed_tsupport χ).measurableSet)
  intro x hx
  apply subset_tsupport χ
  intro hz
  exact hx (by simp [hz])

lemma weightedEnergyN_nonneg {n : ℕ} {χ u : Space n → ℝ} {q B : ℝ}
    (hχ : ∀ x, 0 ≤ χ x) (hu : ∀ x, 0 ≤ u x) : 0 ≤ weightedEnergy χ u q B := by
  exact integral_nonneg (fun x => mul_nonneg (mul_nonneg (hχ x) (source_nonneg hu q B x)) (hu x))

lemma IsSolution.weightedEnergyN_eq {n : ℕ} (hn : 2 ≤ n) {p q A B : ℝ}
    {u v χ : Space n → ℝ} (h : IsSolution n p q A B u v)
    (hχ : Continuous χ) (hχc : HasCompactSupport χ) (hχ0 : ∀ x, 0 ≤ χ x) :
    weightedEnergyN χ u q B = ENNReal.ofReal (weightedEnergy χ u q B) := by
  exact (ofReal_integral_eq_lintegral_ofReal (h.integrable_source_energy_weight hn hχ hχc)
    (ae_of_all _ fun x => mul_nonneg (mul_nonneg (hχ0 x)
      (source_nonneg (fun y => (h.positive_u y).le) q B x)) (h.positive_u x).le)).symm

end HenonLaneEmden
end
end WeightedEnergy

end OAI
end

section
-- module Solutions.OAIQW_HenonLaneEmden.RadialGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE uE2 uE3 uE4 uE5

section RadialGeometry

open MeasureTheory Set Metric NormedSpace
open scoped ENNReal InnerProductSpace
noncomputable section
namespace HenonLaneEmden
open Cutoff AdaptiveCap CapWeights

lemma radialFactor_eq {E : Type uE3} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {x : E} (hx : x ≠ 0) (y : E) :
    radialFactor (x,y)=directionalFactor (direction x hx) (x,y) := by
  simp only [radialFactor,directionalFactor,direction,NormedSpace.normalize,real_inner_smul_left,mul_pow,
    div_eq_mul_inv,mul_inv_rev,inv_pow]
  ring

lemma radialFactor_bounds {E : Type uE4} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (z : E × E) :
    0 ≤ radialFactor z ∧ radialFactor z ≤ 1 := by
  by_cases hx : z.1 = 0
  · simp [radialFactor,hx]
  · rw [radialFactor_eq hx]
    exact directionalFactor_bounds _ _

end HenonLaneEmden
end
end RadialGeometry

end OAI
end

section
-- module Solutions.OAIQW_HenonLaneEmden.NearLocalization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE uE2

section NearLocalization

open Set Metric
open scoped InnerProductSpace
noncomputable section
namespace HenonLaneEmden
open Cutoff AdaptiveCap

@[fun_prop] lemma measurable_fluxFactor (n : ℕ) : Measurable (fluxFactor n : Space n × Space n → ℝ) := by
  unfold fluxFactor X
  have hη := (continuous_eta n (E := Space n)).measurable
  fun_prop

lemma eta_nonneg {E : Type uE} [NormedAddCommGroup E] (n : ℕ) (x : E) : 0 ≤ eta n x :=
  pow_nonneg (baseProfile_nonneg ‖x‖) _

end HenonLaneEmden
end
end NearLocalization

end OAI
end

section
-- module Solutions.OAIQW_HenonLaneEmden.RealInteraction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section RealInteraction

open MeasureTheory Set Filter Topology Metric
open scoped ENNReal
noncomputable section
namespace HenonLaneEmden

lemma interaction_density_finite {n : ℕ} (f g : Space n → ℝ) :
    ∀ᵐ z : Space n × Space n ∂volume.prod volume,
      ENNReal.ofReal (f z.1)*ENNReal.ofReal (g z.2)*ENNReal.ofReal (newtonKernel n z) < ⊤ := by
  exact ae_of_all _ fun z => ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top) ENNReal.ofReal_lt_top

lemma integrable_interaction_iff {n : ℕ} (hn : 3 ≤ n) {f g : Space n → ℝ}
    (hf : Measurable f) (hg : Measurable g) (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, 0 ≤ g x)
    (F : Space n × Space n → ℝ) :
    Integrable F (interaction f g) ↔ Integrable (fun z => f z.1*g z.2*newtonKernel n z*F z) (volume.prod volume) := by
  rw [interaction,integrable_withDensity_iff_integrable_smul' (by fun_prop) (interaction_density_finite f g)]
  simp only [ENNReal.toReal_mul,ENNReal.toReal_ofReal (hf0 _),ENNReal.toReal_ofReal (hg0 _),
    ENNReal.toReal_ofReal (newtonKernel_nonneg hn _),smul_eq_mul]

lemma integral_interaction {n : ℕ} (hn : 3 ≤ n) {f g : Space n → ℝ}
    (hf : Measurable f) (hg : Measurable g) (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, 0 ≤ g x)
    (F : Space n × Space n → ℝ) :
    (∫ z, F z ∂interaction f g) = ∫ z, f z.1*g z.2*newtonKernel n z*F z ∂volume.prod volume := by
  rw [interaction,integral_withDensity_eq_integral_toReal_smul (by fun_prop) (interaction_density_finite f g)]
  simp only [ENNReal.toReal_mul,ENNReal.toReal_ofReal (hf0 _),ENNReal.toReal_ofReal (hg0 _),
    ENNReal.toReal_ofReal (newtonKernel_nonneg hn _),smul_eq_mul]

end HenonLaneEmden
end
end RealInteraction

end OAI
end

section
-- module Solutions.OAIQW_HenonLaneEmden.InteractionBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uα

section InteractionBounds

open MeasureTheory Set Metric
open scoped ENNReal
noncomputable section
namespace HenonLaneEmden
open Cutoff

lemma integrable_integral_le_of_lintegral_le {α : Type uα} [MeasurableSpace α] {μ : Measure α}
    {F : α → ℝ} (hF : Measurable F) (hF0 : ∀ x, 0 ≤ F x) {C : ℝ} (hC : 0 ≤ C)
    (hb : (∫⁻ x, ENNReal.ofReal (F x) ∂μ) ≤ ENNReal.ofReal C) :
    Integrable F μ ∧ (∫ x, F x ∂μ) ≤ C := by
  have hf : (∫⁻ x, ENNReal.ofReal (F x) ∂μ) ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hb
  refine ⟨(lintegral_ofReal_ne_top_iff_integrable hF.aestronglyMeasurable (ae_of_all _ hF0)).mp hf,?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ hF0) hF.aestronglyMeasurable]
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hb).trans_eq (ENNReal.toReal_ofReal hC)

lemma IsSolution.lintegral_weight_left {n : ℕ} (hn : 2 ≤ n) {p q A B : ℝ}
    {u v χ : Space n → ℝ} (h : IsSolution n p q A B u v) (hq : 0 < q)
    (hχ : Continuous χ) (hχc : HasCompactSupport χ) (hχ0 : ∀ x, 0 ≤ χ x) :
    (∫⁻ z, ENNReal.ofReal (χ z.1) ∂interaction (source u q B) (source v p A)) =
      ENNReal.ofReal (weightedEnergy χ u q B) := by
  rw [h.interaction_left hn hq hχ.measurable.ennreal_ofReal,← h.weightedEnergyN_eq hn hχ hχc hχ0]
  unfold weightedEnergyN
  apply lintegral_congr
  intro x
  rw [← ENNReal.ofReal_mul (mul_nonneg (source_nonneg (fun x => (h.positive_u x).le) q B x) (h.positive_u x).le)]
  congr 1; ring

lemma IsSolution.weight_left {n : ℕ} (hn : 2 ≤ n) {p q A B : ℝ}
    {u v χ : Space n → ℝ} (h : IsSolution n p q A B u v) (hq : 0 < q)
    (hχ : Continuous χ) (hχc : HasCompactSupport χ) (hχ0 : ∀ x, 0 ≤ χ x) :
    Integrable (fun z => χ z.1) (interaction (source u q B) (source v p A)) ∧
    (∫ z, χ z.1 ∂interaction (source u q B) (source v p A)) = weightedEnergy χ u q B := by
  have he := h.lintegral_weight_left hn hq hχ hχc hχ0
  refine ⟨(integrable_integral_le_of_lintegral_le (hχ.measurable.comp measurable_fst) (fun z => hχ0 z.1)
    (weightedEnergyN_nonneg hχ0 (fun x => (h.positive_u x).le)) he.le).1,?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ (fun z : Space n × Space n => hχ0 z.1)) (hχ.measurable.comp measurable_fst).aestronglyMeasurable,he,
    ENNReal.toReal_ofReal (weightedEnergyN_nonneg hχ0 (fun x => (h.positive_u x).le))]

end HenonLaneEmden
end
end InteractionBounds

end OAI
end

section
-- module Solutions.OAIQW_HenonLaneEmden.Gradients
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE uE2 uE3 uE4 uE5 uE6

section Gradients
open Set Filter Topology MeasureTheory MeasureTheory.Measure
open scoped RealInnerProductSpace ContDiff ENNReal Convolution Pointwise
noncomputable section
open HenonLaneEmden.RadialCalculus HenonLaneEmden.WeakPDE HenonLaneEmden.SphereCalculus

namespace HenonLaneEmden.WeakPDE
variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma hasFDerivAt_kernel {x : E} (hx : x ≠ 0) :
    HasFDerivAt (fun y : E => ‖y‖^(2-(Module.finrank ℝ E:ℝ)))
      (((2-(Module.finrank ℝ E:ℝ))*‖x‖^(-(Module.finrank ℝ E:ℝ))) • innerSL ℝ x) x := by
  have hr := norm_pos_iff.mpr hx
  have hd := RadialCalculus.hasFDerivAt_profile_norm hx
    (Real.hasDerivAt_rpow_const (p := 2-(Module.finrank ℝ E:ℝ)) (Or.inl hr.ne'))
  convert hd using 1
  congr 1
  rw [mul_div_assoc]
  congr 1
  calc
    _ = ‖x‖^(2-(Module.finrank ℝ E:ℝ)-1-1) := by congr 1; ring
    _ = _ := by rw [Real.rpow_sub hr,Real.rpow_one]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma dir_kernel {e x : E} (hx : x ≠ 0) :
    dir (fun y : E => ‖y‖^(2-(Module.finrank ℝ E:ℝ))) e x = kernelDir e x := by
  rw [dir,(hasFDerivAt_kernel hx).fderiv]
  rfl

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma kernelDir_bound (e x : E) :
    |kernelDir e x| ≤ |2-(Module.finrank ℝ E:ℝ)| *‖e‖*‖x‖^(1-(Module.finrank ℝ E:ℝ)) := by
  by_cases hx : x = 0
  · simp only [hx,kernelDir,inner_zero_left,mul_zero,abs_zero,norm_zero]
    positivity
  have hr := norm_pos_iff.mpr hx
  unfold kernelDir
  rw [abs_mul,abs_mul,abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
  have he : ‖x‖^(-(Module.finrank ℝ E:ℝ))*‖x‖ = ‖x‖^(1-(Module.finrank ℝ E:ℝ)) := by
    calc
      _ = ‖x‖^(-(Module.finrank ℝ E:ℝ)+1) := by rw [Real.rpow_add hr,Real.rpow_one]
      _ = _ := by congr 1; ring
  calc
    _ ≤ (|2-(Module.finrank ℝ E:ℝ)| *‖x‖^(-(Module.finrank ℝ E:ℝ)))*(‖x‖*‖e‖) :=
      mul_le_mul_of_nonneg_left (abs_real_inner_le_norm x e) (by positivity)
    _ = |2-(Module.finrank ℝ E:ℝ)| *‖e‖*(‖x‖^(-(Module.finrank ℝ E:ℝ))*‖x‖) := by ring
    _ = _ := by rw [he]

lemma measurable_kernelDir (e : E) : Measurable (kernelDir e) :=
  (measurable_const.mul (measurable_norm.pow_const _)).mul (by fun_prop)

lemma locallyIntegrable_kernelDir (hn : 1 ≤ Module.finrank ℝ E) (e : E) :
    LocallyIntegrable (kernelDir e) := by
  apply locallyIntegrable_of_norm_le_rpow hn
    (α := (Module.finrank ℝ E:ℝ)-1) (C := |2-(Module.finrank ℝ E:ℝ)| *‖e‖) (by linarith)
    ?_ (measurable_kernelDir e).aestronglyMeasurable
  apply Eventually.of_forall
  intro x
  simpa only [Real.norm_eq_abs,neg_sub] using kernelDir_bound e x

lemma integral_kernel_dir_off_zero (hn : 1 ≤ Module.finrank ℝ E) {φ : E → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hc : HasCompactSupport φ) (h0 : 0 ∉ tsupport φ) (e : E) :
    (∫ x, ‖x‖^(2-(Module.finrank ℝ E:ℝ))*dir φ e x) = -(∫ x, kernelDir e x*φ x) := by
  have hK := locallyIntegrable_newtonKernel hn
  have hdφ : Continuous (dir φ e) := (contDiffOn_univ.mp
    (contDiffOn_dir (k := 1) hφ.contDiffOn isOpen_univ e)).continuous
  have hi := (locallyIntegrable_kernelDir hn e).integrable_smul_right_of_hasCompactSupport hφ.continuous hc
  have heq : (fun x => dir (fun y : E => ‖y‖^(2-(Module.finrank ℝ E:ℝ))) e x*φ x) =
      (fun x => kernelDir e x*φ x) := by
    ext x
    by_cases hx : x = 0
    · simp [hx,image_eq_zero_of_notMem_tsupport h0]
    · rw [dir_kernel hx]
  have hh := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (μ := volume) (v := e) (f := fun x : E => ‖x‖^(2-(Module.finrank ℝ E:ℝ))) (g := φ)
    (by change Integrable (fun x => dir (fun y : E => ‖y‖^(2-(Module.finrank ℝ E:ℝ))) e x*φ x); rw [heq]; exact hi)
    (hK.integrable_smul_right_of_hasCompactSupport hdφ (compactSupport_dir hc e))
    (hK.integrable_smul_right_of_hasCompactSupport hφ.continuous hc)
    (fun x hx => (hasFDerivAt_kernel (fun he => h0 (he ▸ hx))).differentiableAt)
    (fun x _ => hφ.differentiable (by norm_num) x)
  change (∫ x, ‖x‖^(2-(Module.finrank ℝ E:ℝ))*dir φ e x) = -(∫ x, dir (fun y : E => ‖y‖^(2-(Module.finrank ℝ E:ℝ))) e x*φ x) at hh
  rwa [heq] at hh
end HenonLaneEmden.WeakPDE

namespace HenonLaneEmden.WeakPDE
variable {E : Type uE2} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]

lemma kernel_cutoff_derivative_tendsto_zero (hn : 1 ≤ Module.finrank ℝ E) {φ : E → ℝ}
    (hφ : Continuous φ) (hc : HasCompactSupport φ) (ξ : ContDiffBump (0:E)) (e : E) :
    Tendsto (fun R : ℝ => ∫ x : E, ‖x‖^(2-(Module.finrank ℝ E:ℝ))*φ x*
      (R⁻¹*dir ξ e (R⁻¹ • x))) (𝓝[>] 0) (𝓝 0) := by
  have hdξ : Continuous (dir ξ e) := (contDiffOn_univ.mp
    (contDiffOn_dir (k := 1) (ξ.contDiff.of_le (by exact WithTop.coe_le_coe.mpr le_top)).contDiffOn isOpen_univ e)).continuous
  obtain ⟨M,hM⟩ := (compactSupport_dir ξ.hasCompactSupport e).exists_bound_of_continuous hdξ
  have hM0 : 0 ≤ M := (norm_nonneg (dir ξ e 0)).trans (hM 0)
  have hi : Integrable (fun x : E => ‖x‖^(1-(Module.finrank ℝ E:ℝ))*φ x) :=
    (locallyIntegrable_norm_power hn _ (by linarith)).integrable_smul_right_of_hasCompactSupport hφ hc
  have hlim := tendsto_integral_filter_of_dominated_convergence
    (μ := volume) (l := 𝓝[>] (0:ℝ))
    (F := fun (R : ℝ) (x : E) => ‖x‖^(2-(Module.finrank ℝ E:ℝ))*φ x*(R⁻¹*dir ξ e (R⁻¹ • x)))
    (f := fun _ => (0:ℝ)) (fun x => (M*ξ.rOut)*‖‖x‖^(1-(Module.finrank ℝ E:ℝ))*φ x‖)
    (Eventually.of_forall fun R => by
      exact (((measurable_norm.pow_const _).mul hφ.measurable).mul
        (measurable_const.mul (hdξ.measurable.comp (measurable_const.smul measurable_id)))).aestronglyMeasurable)
    ?_ (hi.norm.const_mul (M*ξ.rOut)) ?_
  · simpa only [integral_zero] using hlim
  · filter_upwards [self_mem_nhdsWithin] with R hR
    filter_upwards [ae_iff.mpr (show volume {x : E | ¬ x ≠ 0} = 0 by simp)] with x hx
    by_cases hd : dir ξ e (R⁻¹ • x) = 0
    · simp only [hd,mul_zero,norm_zero]
      exact mul_nonneg (mul_nonneg hM0 ξ.rOut_pos.le) (norm_nonneg _)
    have hs := tsupport_dir_subset (ξ : E → ℝ) e (subset_tsupport _ hd)
    rw [ξ.tsupport_eq] at hs
    have hnorm : R⁻¹*‖x‖ ≤ ξ.rOut := by
      simpa only [Metric.mem_closedBall,dist_zero_right,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr (show 0 < R from hR))] using hs
    have hrx := norm_pos_iff.mpr hx
    have hb : R⁻¹ ≤ ξ.rOut/‖x‖ := (le_div_iff₀ hrx).mpr hnorm
    have hh : |R⁻¹*dir ξ e (R⁻¹ • x)| ≤ M*ξ.rOut/‖x‖ := by
      rw [abs_mul,abs_of_pos (inv_pos.mpr hR)]
      have hm' : |dir ξ e (R⁻¹ • x)| ≤ M := by simpa only [Real.norm_eq_abs] using hM (R⁻¹ • x)
      calc
        _ ≤ R⁻¹*M := mul_le_mul_of_nonneg_left hm' (inv_pos.mpr hR).le
        _ ≤ (ξ.rOut/‖x‖)*M := mul_le_mul_of_nonneg_right hb hM0
        _ = _ := by ring
    rw [norm_mul,Real.norm_eq_abs (R⁻¹*_),norm_mul,Real.norm_eq_abs (‖x‖^_),abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
    apply (mul_le_mul_of_nonneg_left hh (mul_nonneg (Real.rpow_nonneg (norm_nonneg _) _) (norm_nonneg _))).trans_eq
    rw [norm_mul,Real.norm_eq_abs (‖x‖^_),abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
    have he : ‖x‖^(2-(Module.finrank ℝ E:ℝ))/‖x‖ = ‖x‖^(1-(Module.finrank ℝ E:ℝ)) := by
      calc
        _ = ‖x‖^(2-(Module.finrank ℝ E:ℝ)-1) := by rw [Real.rpow_sub hrx (2-(Module.finrank ℝ E:ℝ)) 1,Real.rpow_one]
        _ = _ := by congr 1; ring
    calc
      _ = (M*ξ.rOut)*(‖x‖^(2-(Module.finrank ℝ E:ℝ))/‖x‖)*‖φ x‖ := by ring
      _ = _ := by rw [he]; ring
  · filter_upwards [ae_iff.mpr (show volume {x : E | ¬ x ≠ 0} = 0 by simp)] with x hx
    have he : 0 < ‖x‖/ξ.rOut := div_pos (norm_pos_iff.mpr hx) ξ.rOut_pos
    apply tendsto_const_nhds.congr'
    filter_upwards [self_mem_nhdsWithin,(eventually_lt_nhds he).filter_mono nhdsWithin_le_nhds] with R hR hlt
    have hs : R⁻¹ • x ∉ tsupport (ξ : E → ℝ) := by
      rw [ξ.tsupport_eq,Metric.mem_closedBall,dist_zero_right,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hR)]
      apply not_le_of_gt
      rw [← div_eq_inv_mul]
      apply (lt_div_iff₀ hR).mpr
      simpa only [mul_comm] using (lt_div_iff₀ ξ.rOut_pos).mp hlt
    simp only [dir,fderiv_of_notMem_tsupport ℝ hs,_root_.zero_apply,mul_zero]
end HenonLaneEmden.WeakPDE

namespace HenonLaneEmden.WeakPDE
variable {E : Type uE3} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]

lemma kernel_dir_cutoff_tendsto_zero (hn : 1 ≤ Module.finrank ℝ E) {φ : E → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hc : HasCompactSupport φ) (ξ : ContDiffBump (0:E)) (e : E) :
    Tendsto (fun R : ℝ => ∫ x : E, ‖x‖^(2-(Module.finrank ℝ E:ℝ))*
      dir (fun y => φ y*ξ (R⁻¹ • y)) e x) (𝓝[>] 0) (𝓝 0) := by
  have hK := locallyIntegrable_newtonKernel hn
  have hdφ : Continuous (dir φ e) := (contDiffOn_univ.mp
    (contDiffOn_dir (k := 1) hφ.contDiffOn isOpen_univ e)).continuous
  have hdξ : Continuous (dir ξ e) := (contDiffOn_univ.mp
    (contDiffOn_dir (k := 1) (ξ.contDiff.of_le (by exact WithTop.coe_le_coe.mpr le_top)).contDiffOn isOpen_univ e)).continuous
  have heq (R : ℝ) : (∫ x : E, ‖x‖^(2-(Module.finrank ℝ E:ℝ))*dir (fun y => φ y*ξ (R⁻¹ • y)) e x) =
      (∫ x : E, ‖x‖^(2-(Module.finrank ℝ E:ℝ))*(dir φ e x*ξ (R⁻¹ • x))) +
      (∫ x : E, ‖x‖^(2-(Module.finrank ℝ E:ℝ))*φ x*(R⁻¹*dir ξ e (R⁻¹ • x))) := by
    have hξR : Differentiable ℝ (fun y : E => ξ (R⁻¹ • y)) :=
      ((ξ.contDiff : ContDiff ℝ 2 ξ).comp (contDiff_const.smul contDiff_id)).differentiable (by norm_num)
    simp_rw [dir_mul (hφ.differentiable (by norm_num) _) (hξR _) e,dir_dilation,mul_add,← mul_assoc]
    apply integral_add
    · simpa only [smul_eq_mul, Pi.mul_apply, Function.comp_apply, Pi.smul_apply, id_eq, mul_assoc] using
        hK.integrable_smul_right_of_hasCompactSupport
          (hdφ.mul (ξ.continuous.comp (continuous_id.const_smul R⁻¹))) (compactSupport_dir hc e).mul_right
    · simpa only [smul_eq_mul, Pi.mul_apply, Function.comp_apply, Pi.smul_apply, id_eq, mul_assoc] using
        hK.integrable_smul_right_of_hasCompactSupport
          (hφ.continuous.mul ((continuous_const : Continuous (fun _ : E => R⁻¹)).mul
            (hdξ.comp (continuous_id.const_smul R⁻¹)))) hc.mul_right
  simp_rw [heq]
  simpa only [add_zero] using (cutoff_source_integral_tendsto_zero hK hdφ (compactSupport_dir hc e) ξ).add
    (kernel_cutoff_derivative_tendsto_zero hn hφ.continuous hc ξ e)

lemma integral_kernel_dir (hn : 1 ≤ Module.finrank ℝ E) {φ : E → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hc : HasCompactSupport φ) (e : E) :
    (∫ x, ‖x‖^(2-(Module.finrank ℝ E:ℝ))*dir φ e x) = -(∫ x, kernelDir e x*φ x) := by
  let ξ : ContDiffBump (0:E) := ⟨1,2,by norm_num,by norm_num⟩
  have hK := locallyIntegrable_newtonKernel hn
  have hD := locallyIntegrable_kernelDir hn e
  have hdφ : Continuous (dir φ e) := (contDiffOn_univ.mp
    (contDiffOn_dir (k := 1) hφ.contDiffOn isOpen_univ e)).continuous
  have hiK := hK.integrable_smul_right_of_hasCompactSupport hdφ (compactSupport_dir hc e)
  have hiD := hD.integrable_smul_right_of_hasCompactSupport hφ.continuous hc
  have hevent : ∀ᶠ R : ℝ in 𝓝[>] 0,
      (∫ x, ‖x‖^(2-(Module.finrank ℝ E:ℝ))*dir φ e x) -
        (∫ x, ‖x‖^(2-(Module.finrank ℝ E:ℝ))*dir (fun y => φ y*ξ (R⁻¹ • y)) e x) =
        -(∫ x, kernelDir e x*φ x)+(∫ x, kernelDir e x*(φ x*ξ (R⁻¹ • x))) := by
    filter_upwards [self_mem_nhdsWithin] with R hR
    obtain ⟨hψ,hψc,hψ0⟩ := cutoff_test_off_origin hφ hc ξ hR
    have hh := integral_kernel_dir_off_zero hn hψ hψc hψ0 e
    have hχ : ContDiff ℝ 2 (fun y : E => φ y*ξ (R⁻¹ • y)) :=
      hφ.mul (ξ.contDiff.comp (contDiff_const.smul contDiff_id))
    have hχc : HasCompactSupport (fun y : E => φ y*ξ (R⁻¹ • y)) := hc.mul_right
    have hdχ : Continuous (dir (fun y : E => φ y*ξ (R⁻¹ • y)) e) := (contDiffOn_univ.mp
      (contDiffOn_dir (k := 1) hχ.contDiffOn isOpen_univ e)).continuous
    have hiχK := hK.integrable_smul_right_of_hasCompactSupport hdχ (compactSupport_dir hχc e)
    have hiχD := hD.integrable_smul_right_of_hasCompactSupport hχ.continuous hχc
    simp only [smul_eq_mul] at hiK hiD hiχK hiχD
    have hid (x : E) : dir (fun y => φ y-φ y*ξ (R⁻¹ • y)) e x =
        dir φ e x-dir (fun y => φ y*ξ (R⁻¹ • y)) e x := by
      unfold dir
      exact congrArg (fun L : E →L[ℝ] ℝ => L e)
        ((hφ.differentiable (by norm_num) x).hasFDerivAt.sub
          (hχ.differentiable (by norm_num) x).hasFDerivAt).fderiv
    simp_rw [hid,mul_sub] at hh
    rw [integral_sub hiK hiχK,integral_sub hiD hiχD] at hh
    linarith
  have hlim₁ := (tendsto_const_nhds (x := ∫ x, ‖x‖^(2-(Module.finrank ℝ E:ℝ))*dir φ e x)).sub
    (kernel_dir_cutoff_tendsto_zero hn hφ hc ξ e)
  have hlim₂ := (tendsto_const_nhds (x := -(∫ x, kernelDir e x*φ x))).add
    (cutoff_source_integral_tendsto_zero hD hφ.continuous hc ξ)
  simpa only [sub_zero,add_zero] using tendsto_nhds_unique hlim₁ (hlim₂.congr' (hevent.mono fun _ hh => hh.symm))
end HenonLaneEmden.WeakPDE

namespace HenonLaneEmden.WeakPDE
variable {E : Type uE4} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma kernelDir_shift_bound (hn : 3 ≤ Module.finrank ℝ E) {r : ℝ} (hr : 0 < r)
    {x x₀ y : E} (hx : ‖x-x₀‖ < r/2) (hy : r ≤ ‖x₀-y‖) (e : E) :
    |kernelDir e (x-y)| ≤ (|2-(Module.finrank ℝ E:ℝ)| *‖e‖*(2/r)*(1/2:ℝ)^(2-(Module.finrank ℝ E:ℝ)))*
      ‖x₀-y‖^(2-(Module.finrank ℝ E:ℝ)) := by
  have ht := norm_sub_le (x₀-x) (y-x)
  simp only [sub_sub_sub_cancel_right,norm_sub_rev y x,norm_sub_rev x₀ x] at ht
  have hl : r/2 ≤ ‖x-y‖ := by linarith
  have hp : 0 < ‖x-y‖ := lt_of_lt_of_le (half_pos hr) hl
  have ha : 2-(Module.finrank ℝ E:ℝ) ≤ 0 := by
    have hh : (3:ℝ) ≤ Module.finrank ℝ E := by exact_mod_cast hn
    linarith
  have he : ‖x-y‖^(1-(Module.finrank ℝ E:ℝ)) = ‖x-y‖^(2-(Module.finrank ℝ E:ℝ))/‖x-y‖ := by
    calc
      _ = ‖x-y‖^(2-(Module.finrank ℝ E:ℝ)-1) := by congr 1; ring
      _ = _ := by rw [Real.rpow_sub hp,Real.rpow_one]
  have hh : ‖x-y‖^(1-(Module.finrank ℝ E:ℝ)) ≤
      (2/r)*((1/2:ℝ)^(2-(Module.finrank ℝ E:ℝ))*‖x₀-y‖^(2-(Module.finrank ℝ E:ℝ))) := by
    rw [he,div_eq_inv_mul]
    apply mul_le_mul
    · have h := one_div_le_one_div_of_le (half_pos hr) hl
      simpa only [one_div,inv_div] using h
    · exact rpow_kernel_shift_bound ha hr hx hy
    · positivity
    · positivity
  exact (kernelDir_bound e (x-y)).trans ((mul_le_mul_of_nonneg_left hh (by positivity)).trans_eq (by ring))

lemma hasLineDerivAt_far_rawPotential (hn : 3 ≤ Module.finrank ℝ E) {g : E → ℝ}
    (hg : Measurable g) (hgp : ∀ y, 0 ≤ g y) {x₀ : E} {r : ℝ} (hr : 0 < r)
    (hzero : ∀ y ∈ Metric.ball x₀ r, g y = 0)
    (hi : Integrable (fun y => ‖x₀-y‖^(2-(Module.finrank ℝ E:ℝ))*g y)) (e : E) :
    Integrable (fun y => kernelDir e (x₀-y)*g y) ∧
      HasLineDerivAt ℝ (rawPotential g) (∫ y, kernelDir e (x₀-y)*g y) x₀ e := by
  let C := |2-(Module.finrank ℝ E:ℝ)| *‖e‖*(2/r)*(1/2:ℝ)^(2-(Module.finrank ℝ E:ℝ))
  let s : Set ℝ := {t | ‖t • e‖ < r/2}
  have hs : s ∈ 𝓝 (0:ℝ) := by
    apply IsOpen.mem_nhds (isOpen_lt (continuous_id.smul continuous_const).norm continuous_const)
    simpa [s] using half_pos hr
  have hDmeas : Measurable (fun y : E => kernelDir e (x₀-y)*g y) :=
    ((measurable_kernelDir e).comp (measurable_const.sub measurable_id)).mul hg
  have hh := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := (volume : Measure E)) (F := fun (t : ℝ) (y : E) => ‖(x₀+t • e)-y‖^(2-(Module.finrank ℝ E:ℝ))*g y)
    (F' := fun (t : ℝ) (y : E) => kernelDir e ((x₀+t • e)-y)*g y)
    (bound := fun y => C*(‖x₀-y‖^(2-(Module.finrank ℝ E:ℝ))*g y)) hs
    (Eventually.of_forall fun t => (((measurable_const.sub measurable_id).norm.pow_const _).mul hg).aestronglyMeasurable)
    (by simpa using hi)
    (by simpa only [zero_smul, add_zero] using hDmeas.aestronglyMeasurable)
    ?_ (hi.const_mul C) ?_
  · simpa only [zero_smul,add_zero,HasLineDerivAt,rawPotential] using hh
  · apply Eventually.of_forall
    intro y t ht
    by_cases hy : y ∈ Metric.ball x₀ r
    · simp only [hzero y hy,mul_zero,norm_zero,le_refl]
    have hyr : r ≤ ‖x₀-y‖ := by
      have hy' : ¬ ‖y-x₀‖ < r := by simpa only [Metric.mem_ball,dist_eq_norm] using hy
      simpa only [norm_sub_rev] using le_of_not_gt hy'
    have htx : ‖(x₀+t • e)-x₀‖ < r/2 := by simpa only [s,Set.mem_ofPred_eq,add_sub_cancel_left] using ht
    rw [norm_mul,Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg (hgp y)]
    exact (mul_le_mul_of_nonneg_right (kernelDir_shift_bound hn hr htx hyr e) (hgp y)).trans_eq (mul_assoc _ _ _)
  · apply Eventually.of_forall
    intro y t ht
    by_cases hy : y ∈ Metric.ball x₀ r
    · simp only [hzero y hy,mul_zero]
      exact hasDerivAt_const t 0
    have hyr : r ≤ ‖x₀-y‖ := by
      have hy' : ¬ ‖y-x₀‖ < r := by simpa only [Metric.mem_ball,dist_eq_norm] using hy
      simpa only [norm_sub_rev] using le_of_not_gt hy'
    have hne : (x₀+t • e)-y ≠ 0 := by
      intro he
      have he' : y = x₀+t • e := (sub_eq_zero.mp he).symm
      rw [he',norm_sub_rev,add_sub_cancel_left] at hyr
      linarith [show ‖t • e‖ < r/2 from ht]
    have haff : HasDerivAt (fun t : ℝ => (x₀+t • e)-y) e t := by
      simpa using (((hasDerivAt_id t).smul_const e).const_add x₀).sub_const y
    have hd := ((hasFDerivAt_kernel hne).comp_hasDerivAt t haff).mul_const (g y)
    simpa only [_root_.smul_apply,innerSL_apply_apply,smul_eq_mul,kernelDir,Function.comp_apply] using hd
end HenonLaneEmden.WeakPDE

namespace HenonLaneEmden.WeakPDE
variable {E : Type uE5} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]

omit [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
lemma contDiff_mul_cutoff {g ξ : E → ℝ} {s : Set E} {k : ℕ∞ω} (hs : IsOpen s)
    (hg : ContDiffOn ℝ k g s) (hξ : ContDiff ℝ k ξ) (hξs : tsupport ξ ⊆ s) :
    ContDiff ℝ k (fun y => ξ y*g y) := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  by_cases hx : x ∈ tsupport ξ
  · exact hξ.contDiffAt.mul (hg.contDiffAt (hs.mem_nhds (hξs hx)))
  · apply (contDiffAt_const (c := (0:ℝ))).congr_of_eventuallyEq
    filter_upwards [(isClosed_tsupport ξ).isOpen_compl.mem_nhds hx] with y hy
    simp only [image_eq_zero_of_notMem_tsupport hy,zero_mul]

omit [Nontrivial E] in
lemma rawPotential_eq_convolve (g : E → ℝ) : rawPotential g = convolve (fun y : E => ‖y‖^(2-(Module.finrank ℝ E:ℝ))) g := by
  ext x
  rw [rawPotential,convolve_def,← integral_sub_left_eq_self (fun y : E => ‖y‖^(2-(Module.finrank ℝ E:ℝ))*g (x-y)) volume x]
  simp only [sub_sub_cancel]

omit [Nontrivial E] in
lemma integrable_kernelDir_local (hn : 1 ≤ Module.finrank ℝ E) {g : E → ℝ}
    (hg : Continuous g) (hc : HasCompactSupport g) (e x : E) :
    Integrable (fun y => kernelDir e (x-y)*g y) := by
  have hh := (locallyIntegrable_kernelDir hn e).integrable_smul_right_of_hasCompactSupport
    (hg.comp (continuous_const.sub continuous_id)) (hc.comp_homeomorph (Homeomorph.subLeft x))
  have hi := (Measure.measurePreserving_sub_left volume x).integrable_comp hh.aestronglyMeasurable
  apply hi.mpr hh |>.congr
  exact Eventually.of_forall fun y => by simp only [Function.comp_apply,Pi.sub_apply,id_eq,sub_sub_cancel,smul_eq_mul]

lemma dir_rawPotential_local (hn : 1 ≤ Module.finrank ℝ E) {g : E → ℝ}
    (hg : ContDiff ℝ 2 g) (hc : HasCompactSupport g) (e x : E) :
    dir (rawPotential g) e x = ∫ y, kernelDir e (x-y)*g y := by
  let φ : E → ℝ := fun z => g (x-z)
  have hφ : ContDiff ℝ 2 φ := hg.comp (contDiff_const.sub contDiff_id)
  have hφc : HasCompactSupport φ := hc.comp_homeomorph (Homeomorph.subLeft x)
  have hdφ (z : E) : dir φ e z = -dir g e (x-z) := by
    unfold dir φ
    have hd := (hg.differentiable (by norm_num) (x-z)).hasFDerivAt.comp z
      ((hasFDerivAt_id z).const_sub x)
    have hfd : fderiv ℝ (fun z => g (x-z)) z = _ := hd.fderiv
    rw [hfd]
    simp
  have hh := integral_kernel_dir hn hφ hφc e
  simp_rw [hdφ,mul_neg,integral_neg] at hh
  have hh' := neg_injective hh
  rw [rawPotential_eq_convolve,dir_convolve (locallyIntegrable_newtonKernel hn) (hg.of_le (by norm_num)) hc,convolve_def,hh']
  rw [← integral_sub_left_eq_self (fun z => kernelDir e z*g (x-z)) volume x]
  simp only [sub_sub_cancel]

lemma hasLineDerivAt_rawPotential_local (hn : 1 ≤ Module.finrank ℝ E) {g : E → ℝ}
    (hg : ContDiff ℝ 2 g) (hc : HasCompactSupport g) (e x : E) :
    HasLineDerivAt ℝ (rawPotential g) (∫ y, kernelDir e (x-y)*g y) x e := by
  have hd : Differentiable ℝ (rawPotential g) := by
    rw [rawPotential_eq_convolve]
    exact (contDiff_convolve (locallyIntegrable_newtonKernel hn) hg hc).differentiable (by norm_num)
  rw [← dir_rawPotential_local hn hg hc]
  exact (hd x).hasFDerivAt.hasLineDerivAt e
end HenonLaneEmden.WeakPDE

namespace HenonLaneEmden.WeakPDE
variable {E : Type uE6} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]

lemma hasLineDerivAt_rawPotential (hn : 3 ≤ Module.finrank ℝ E) {g : E → ℝ} {s : Set E}
    (hg : Measurable g) (hgp : ∀ x, 0 ≤ g x) (hs : IsOpen s) (hgc : ContDiffOn ℝ 2 g s)
    (hi : ∀ x, Integrable (fun y => ‖x-y‖^(2-(Module.finrank ℝ E:ℝ))*g y))
    {x₀ : E} (hx₀ : x₀ ∈ s) (e : E) :
    Integrable (fun y => kernelDir e (x₀-y)*g y) ∧
      HasLineDerivAt ℝ (rawPotential g) (∫ y, kernelDir e (x₀-y)*g y) x₀ e := by
  obtain ⟨r,hr,hrs⟩ := Metric.mem_nhds_iff.mp (hs.mem_nhds hx₀)
  let ξ : ContDiffBump x₀ := ⟨r/4,r/2,by linarith,by linarith⟩
  have hξs : tsupport ξ ⊆ s := by
    apply Subset.trans (by rw [ξ.tsupport_eq] : tsupport ξ ⊆ Metric.closedBall x₀ ξ.rOut)
    intro y hy
    apply hrs
    have hy' : dist y x₀ ≤ r/2 := hy
    change dist y x₀ < r
    linarith
  let g₀ : E → ℝ := fun y => ξ y*g y
  let g₁ : E → ℝ := fun y => (1-ξ y)*g y
  have hg₀c : ContDiff ℝ 2 g₀ := contDiff_mul_cutoff hs hgc ξ.contDiff hξs
  have hg₀k : HasCompactSupport g₀ := ξ.hasCompactSupport.mul_right
  have hg₁m : Measurable g₁ := (measurable_const.sub ξ.continuous.measurable).mul hg
  have hg₁p : ∀ y, 0 ≤ g₁ y := fun y => mul_nonneg (sub_nonneg.mpr (ξ.le_one (x := y))) (hgp y)
  have hi₀ (x : E) := rawPotential_integrable_cutoff hg hgp ξ.continuous.measurable
    (fun _ => ξ.nonneg) (fun _ => ξ.le_one) (hi x)
  have hi₁ (x : E) : Integrable (fun y => ‖x-y‖^(2-(Module.finrank ℝ E:ℝ))*((1-ξ y)*g y)) := by
    simpa only [Pi.sub_apply] using rawPotential_integrable_cutoff hg hgp
      (measurable_const.sub ξ.continuous.measurable) (fun y => sub_nonneg.mpr (ξ.le_one (x := y)))
      (fun y => by change 1-ξ y ≤ 1; linarith [ξ.nonneg (x := y)]) (hi x)
  obtain ⟨hd₁,hfar⟩ := hasLineDerivAt_far_rawPotential hn hg₁m hg₁p (r := r/4) (by linarith)
    (by intro y hy
        have heq : ξ y = 1 := ξ.one_of_mem_closedBall (Metric.ball_subset_closedBall hy)
        simp [g₁,heq]) (hi₁ x₀) e
  have hd₀ := integrable_kernelDir_local (by omega : 1 ≤ Module.finrank ℝ E) hg₀c.continuous hg₀k e x₀
  have heqD : (fun y => kernelDir e (x₀-y)*g y) =
      (fun y => kernelDir e (x₀-y)*g₀ y+kernelDir e (x₀-y)*g₁ y) := by
    funext y; dsimp [g₀,g₁]; ring
  refine ⟨?_,?_⟩
  · rw [heqD]
    exact hd₀.add hd₁
  have heq : rawPotential g = fun x => rawPotential g₀ x+rawPotential g₁ x := by
    ext x
    change (∫ y, ‖x-y‖^(2-(Module.finrank ℝ E:ℝ))*g y) =
      (∫ y, ‖x-y‖^(2-(Module.finrank ℝ E:ℝ))*(ξ y*g y)) +
      (∫ y, ‖x-y‖^(2-(Module.finrank ℝ E:ℝ))*((1-ξ y)*g y))
    rw [← integral_add (hi₀ x) (hi₁ x)]
    apply integral_congr_ae
    exact Eventually.of_forall fun y => by ring
  rw [heq,heqD,integral_add hd₀ hd₁]
  exact (hasLineDerivAt_rawPotential_local (by omega) hg₀c hg₀k e x₀).add hfar
end HenonLaneEmden.WeakPDE

namespace HenonLaneEmden
open WeakPDE
lemma IsSolution.gradient_u {n : ℕ} (hn : 2 ≤ n) {p q A B : ℝ}
    {u v : Space n → ℝ} (h : IsSolution n p q A B u v) (hq : 0 < q)
    {x : Space n} (hx : x ≠ 0) (e : Space n) :
    Integrable (fun y => kernelDir e (x-y)*source v p A y) ∧
      newtonDenom n*dir u e x = ∫ y, kernelDir e (x-y)*source v p A y := by
  have : Nontrivial (Space n) := Module.nontrivial_of_finrank_pos (R := ℝ) (by simp; omega)
  obtain ⟨hi,hd⟩ := hasLineDerivAt_rawPotential (by simpa using h.dimension_ge_three hn)
    (measurable_source h.continuous_v p A) (source_nonneg (fun y => (h.positive_v y).le) p A)
    isOpen_compl_singleton (regular_source h.regular_v h.positive_v p A)
    (by simpa only [finrank_euclideanSpace_fin] using h.kernel_g_integrable hn) hx e
  refine ⟨hi,?_⟩
  have hu := (h.regular_u.contDiffAt (isOpen_compl_singleton.mem_nhds hx)).differentiableAt (by norm_num)
  have hd' : HasLineDerivAt ℝ (fun y => newtonDenom n*u y) (newtonDenom n*dir u e x) x e := by
    simpa only [dir,_root_.smul_apply,smul_eq_mul] using (hu.hasFDerivAt.const_mul (newtonDenom n)).hasLineDerivAt e
  apply hd'.unique
  apply hd.congr_of_eventuallyEq
  filter_upwards [isOpen_compl_singleton.mem_nhds hx] with y hy
  exact h.potential_u hn hq hy
end HenonLaneEmden
end
end Gradients

end OAI
end

section
-- module Solutions.OAIQW_HenonLaneEmden.VirialCalculus
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section VirialCalculus

open MeasureTheory Set Filter Topology Metric
open scoped InnerProductSpace
noncomputable section
namespace HenonLaneEmden
open WeakPDE RadialCalculus

lemma regular_energyDensity {n : ℕ} {u : Space n → ℝ}
    (hu : ContDiffOn ℝ 2 u ({0}ᶜ : Set (Space n))) (hup : ∀ x, 0 < u x) (q B : ℝ) :
    ContDiffOn ℝ 2 (energyDensity u q B) ({0}ᶜ : Set (Space n)) := by
  exact ((contDiffOn_id.norm ℝ (fun x hx => by simpa using hx)).rpow_const_of_ne
    (fun x hx => norm_ne_zero_iff.mpr (by simpa using hx))).mul
      (hu.rpow_const_of_ne (fun x _ => ne_of_gt (hup x)))

lemma dir_energyDensity {n : ℕ} {u : Space n → ℝ}
    (hu : ContDiffOn ℝ 2 u ({0}ᶜ : Set (Space n))) (hup : ∀ x, 0 < u x)
    (q B : ℝ) {x : Space n} (hx : x ≠ 0) (e : Space n) :
    dir (energyDensity u q B) e x =
      B*inner ℝ x e/‖x‖^2*energyDensity u q B x+(q+1)*source u q B x*dir u e x := by
  have hr : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have huD := (hu.contDiffAt (isOpen_compl_singleton.mem_nhds hx)).differentiableAt (by norm_num)
  have hrD := hasFDerivAt_profile_norm hx (Real.hasDerivAt_rpow_const (p := B) (Or.inl hr.ne'))
  have hpD := huD.hasFDerivAt.rpow_const (p := q+1) (Or.inl (hup x).ne')
  have hD := hrD.mul hpD
  change HasFDerivAt (energyDensity u q B) _ x at hD
  rw [dir,hD.fderiv]
  simp only [add_apply,smul_apply,innerSL_apply_apply,smul_eq_mul]
  rw [show q+1-1=q by ring,source_off_zero _ _ _ hx]
  unfold energyDensity dir
  rw [Real.rpow_sub hr,Real.rpow_one]
  field_simp
  ring

end HenonLaneEmden
end
end VirialCalculus

end OAI
end

section
-- module Solutions.OAIQW_HenonLaneEmden.RadialIntegration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section RadialIntegration

open MeasureTheory Set Filter Topology Metric
open scoped InnerProductSpace
noncomputable section
namespace HenonLaneEmden
open WeakPDE

lemma sum_inner_mul_dir {n : ℕ} (F : Space n → ℝ) (x : Space n) :
    ∑ i : Fin n, inner ℝ (EuclideanSpace.basisFun (Fin n) ℝ i) x *
      dir F (EuclideanSpace.basisFun (Fin n) ℝ i) x = dir F x x := by
  let b := EuclideanSpace.basisFun (Fin n) ℝ
  have he := congrArg (fderiv ℝ F x) (b.sum_repr' x)
  simpa only [map_sum,map_smul,smul_eq_mul,dir] using he

lemma integral_radial_test {n : ℕ} {F θ : Space n → ℝ}
    (hF : ContDiffOn ℝ 1 F ({0}ᶜ : Set (Space n)))
    (hθ : ContDiff ℝ 1 θ) (hθc : HasCompactSupport θ) (hθ0 : 0 ∉ tsupport θ) :
    (∫ x, F x*((n:ℝ)*θ x+dir θ x x)) = -(∫ x, θ x*dir F x x) := by
  let b := EuclideanSpace.basisFun (Fin n) ℝ
  let φ (i : Fin n) (x : Space n) := θ x*inner ℝ (b i) x
  have hφ (i : Fin n) : ContDiff ℝ 1 (φ i) := hθ.mul ((innerSL ℝ (b i)).contDiff)
  have hφs (i : Fin n) : tsupport (φ i) ⊆ tsupport θ := tsupport_mul_subset_left
  have hφc (i : Fin n) : HasCompactSupport (φ i) := hθc.mul_right
  have hs : tsupport θ ⊆ ({0}ᶜ : Set (Space n)) := by
    intro x hx
    simp only [mem_compl_iff,mem_singleton_iff]
    intro he; subst x; exact hθ0 hx
  have hφD (i : Fin n) : Continuous (dir (φ i) (b i)) :=
    (contDiffOn_univ.mp (contDiffOn_dir (k := 0) (hφ i).contDiffOn isOpen_univ (b i))).continuous
  have hFD (i : Fin n) : ContinuousOn (dir F (b i)) ({0}ᶜ : Set (Space n)) :=
    (contDiffOn_dir (k := 0) hF isOpen_compl_singleton (b i)).continuousOn
  have hiL (i : Fin n) : Integrable (fun x => F x*dir (φ i) (b i) x) :=
    integrable_mul_compact (compactSupport_dir (hφc i) (b i))
      (hF.continuousOn.mono ((tsupport_dir_subset _ _).trans ((hφs i).trans hs))) (hφD i).continuousOn
  have hiR (i : Fin n) : Integrable (fun x => dir F (b i) x*φ i x) :=
    integrable_mul_compact (hφc i) ((hFD i).mono ((hφs i).trans hs)) (hφ i).continuous.continuousOn
  have hiP (i : Fin n) : Integrable (fun x => F x*φ i x) :=
    integrable_mul_compact (hφc i) (hF.continuousOn.mono ((hφs i).trans hs)) (hφ i).continuous.continuousOn
  have hI (i : Fin n) : (∫ x, F x*dir (φ i) (b i) x) = -(∫ x, dir F (b i) x*φ i x) := by
    exact integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := volume) (f := F) (g := φ i) (v := b i)
      (hiR i) (hiL i) (hiP i)
      (fun x hx => (hF.contDiffAt (isOpen_compl_singleton.mem_nhds (hs (hφs i hx)))).differentiableAt (by norm_num))
      (fun x _ => (hφ i).differentiable (by norm_num) x)
  have hφeq (i : Fin n) (x : Space n) : dir (φ i) (b i) x =
      inner ℝ (b i) x*dir θ (b i) x+θ x := by
    have hh := ((hθ.differentiable (by norm_num) x).hasFDerivAt).mul ((innerSL ℝ (b i)).hasFDerivAt)
    change HasFDerivAt (φ i) _ x at hh
    rw [dir,hh.fderiv]
    simp only [add_apply,smul_apply,smul_eq_mul,innerSL_apply_apply,b.inner_eq_ite,ite_true,mul_one,dir]
    ring
  have hL (x : Space n) : (∑ i : Fin n, F x*dir (φ i) (b i) x) = F x*((n:ℝ)*θ x+dir θ x x) := by
    simp_rw [hφeq,mul_add]
    rw [Finset.sum_add_distrib,← Finset.mul_sum,show (∑ i : Fin n, inner ℝ (b i) x*dir θ (b i) x) = dir θ x x from sum_inner_mul_dir θ x]
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    ring
  have hR (x : Space n) : (∑ i : Fin n, dir F (b i) x*φ i x) = θ x*dir F x x := by
    simp only [φ]
    simp_rw [show ∀ i : Fin n, dir F (b i) x*(θ x*inner ℝ (b i) x) = θ x*(inner ℝ (b i) x*dir F (b i) x) from fun _ => by ring]
    rw [← Finset.mul_sum,sum_inner_mul_dir]
  calc
    _ = ∫ x, ∑ i : Fin n, F x*dir (φ i) (b i) x := by simp_rw [hL]
    _ = ∑ i : Fin n, ∫ x, F x*dir (φ i) (b i) x := integral_finsetSum _ (fun i _ => hiL i)
    _ = ∑ i : Fin n, -(∫ x, dir F (b i) x*φ i x) := by simp_rw [hI]
    _ = -(∫ x, ∑ i : Fin n, dir F (b i) x*φ i x) := by rw [integral_finsetSum _ (fun i _ => hiR i),Finset.sum_neg_distrib]
    _ = _ := by simp_rw [hR]

end HenonLaneEmden
end
end RadialIntegration

end OAI
end

section
-- module Solutions.OAIQW_HenonLaneEmden.CutoffSmooth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE

section CutoffSmooth

open MeasureTheory Set Filter Topology Metric
noncomputable section
namespace HenonLaneEmden.Cutoff

lemma contDiff_etaProfile {n : ℕ} (hn : 1 ≤ n) : ContDiff ℝ 2 (etaProfile n) := by
  have hd : deriv (etaProfile n) = derivativeProfile n := funext (fun r => (hasDerivAt_etaProfile n r).deriv)
  rw [show (2 : WithTop ℕ∞) = 1+1 by norm_num,contDiff_succ_iff_deriv]
  refine ⟨fun r => (hasDerivAt_etaProfile n r).differentiableAt, by simp, ?_⟩
  rw [hd,contDiff_one_iff_deriv]
  refine ⟨fun r => (hasDerivAt_derivativeProfile hn r).differentiableAt, ?_⟩
  convert continuous_secondProfile n using 1
  exact funext (fun r => (hasDerivAt_derivativeProfile hn r).deriv)

lemma contDiff_eta {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {n : ℕ} (hn : 1 ≤ n) : ContDiff ℝ 2 (eta n : E → ℝ) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x = 0
  · subst x
    apply contDiffAt_const.congr_of_eventuallyEq
    filter_upwards [Metric.ball_mem_nhds (0:E) (by norm_num : (0:ℝ)<1)] with y hy
    exact eta_eq_one (mem_ball_zero_iff.mp hy).le
  · exact (contDiff_etaProfile hn).contDiffAt.comp _ (contDiffAt_norm ℝ hx)

end HenonLaneEmden.Cutoff
end
end CutoffSmooth

end OAI
end

section
-- module Solutions.OAIQW_HenonLaneEmden.WeightedVirial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section WeightedVirial

open MeasureTheory Set Filter Topology Metric
open scoped InnerProductSpace
noncomputable section
namespace HenonLaneEmden
open WeakPDE Cutoff

lemma continuousOn_radialDir {n : ℕ} {u : Space n → ℝ}
    (hu : ContDiffOn ℝ 1 u ({0}ᶜ : Set (Space n))) :
    ContinuousOn (fun x => dir u x x) ({0}ᶜ : Set (Space n)) :=
  (hu.continuousOn_fderiv_of_isOpen isOpen_compl_singleton le_rfl).clm_apply continuousOn_id

lemma weighted_virial_off_origin {n : ℕ} {u θ : Space n → ℝ}
    (hu : ContDiffOn ℝ 2 u ({0}ᶜ : Set (Space n))) (hup : ∀ x, 0 < u x)
    (q B : ℝ) (hθ : ContDiff ℝ 1 θ) (hθc : HasCompactSupport θ) (hθ0 : 0 ∉ tsupport θ) :
    (∫ x, energyDensity u q B x*((n+B)*θ x+dir θ x x)) =
      -(q+1)*(∫ x, θ x*source u q B x*dir u x x) := by
  have hF := regular_energyDensity hu hup q B
  have hs : tsupport θ ⊆ ({0}ᶜ : Set (Space n)) := by
    intro x hx
    simp only [mem_compl_iff,mem_singleton_iff]
    intro he; subst x; exact hθ0 hx
  have hθc' : HasCompactSupport (fun x => B*θ x) := hθc.mul_left
  have hiFθ : Integrable (fun x => energyDensity u q B x*θ x) :=
    integrable_mul_compact hθc (hF.continuousOn.mono hs) hθ.continuous.continuousOn
  have hiG : Integrable (fun x => θ x*source u q B x*dir u x x) := by
    have hc := (regular_source hu hup q B).continuousOn.mul (continuousOn_radialDir (hu.of_le (by norm_num)))
    exact (integrable_mul_compact hθc (hc.mono hs) hθ.continuous.continuousOn).congr
      (ae_of_all _ (fun _ => by dsimp only [Pi.mul_apply]; ring))
  have hiFD : Integrable (fun x => θ x*dir (energyDensity u q B) x x) := by
    exact (integrable_mul_compact hθc ((continuousOn_radialDir (hF.of_le (by norm_num))).mono hs)
      hθ.continuous.continuousOn).congr (ae_of_all _ (fun _ => mul_comm _ _))
  have hpoint (x : Space n) : θ x*dir (energyDensity u q B) x x =
      B*(energyDensity u q B x*θ x)+(q+1)*(θ x*source u q B x*dir u x x) := by
    by_cases hx : x ∈ tsupport θ
    · have hx0 := hs hx
      have hr := norm_ne_zero_iff.mpr hx0
      rw [dir_energyDensity hu hup q B hx0,real_inner_self_eq_norm_sq]
      field_simp
    · rw [image_eq_zero_of_notMem_tsupport hx]
      ring
  have hrad := integral_radial_test (hF.of_le (by norm_num)) hθ hθc hθ0
  have hiL : Integrable (fun x => energyDensity u q B x*((n:ℝ)*θ x+dir θ x x)) := by
    have hc : Continuous (fun x : Space n => (n:ℝ)*θ x+dir θ x x) := (continuous_const.mul hθ.continuous).add ((hθ.continuous_fderiv (by norm_num)).clm_apply continuous_id)
    have hk : HasCompactSupport (fun x => (n:ℝ)*θ x+dir θ x x) := by
      apply HasCompactSupport.intro hθc
      intro x hx
      rw [image_eq_zero_of_notMem_tsupport hx]
      have hd : fderiv ℝ θ x = 0 := fderiv_of_notMem_tsupport ℝ hx
      simp [dir,hd]
    have hsub : tsupport (fun x => (n:ℝ)*θ x+dir θ x x) ⊆ tsupport θ := by
      apply closure_minimal _ (isClosed_tsupport θ)
      intro x hx
      contrapose! hx
      simp only [Function.mem_support,not_not]
      rw [image_eq_zero_of_notMem_tsupport hx]
      have hd : fderiv ℝ θ x = 0 := fderiv_of_notMem_tsupport ℝ hx
      simp [dir,hd]
    exact integrable_mul_compact hk (hF.continuousOn.mono (hsub.trans hs)) hc.continuousOn
  have hsumF := integral_add hiL (hiFθ.const_mul B)
  have hsumG := integral_add (hiFθ.const_mul B) (hiG.const_mul (q+1))
  simp_rw [hpoint] at hrad
  rw [hsumG,integral_const_mul,integral_const_mul] at hrad
  calc
    _ = (∫ x, energyDensity u q B x*((n:ℝ)*θ x+dir θ x x))+
        B*(∫ x, energyDensity u q B x*θ x) := by
      rw [← integral_const_mul,← hsumF]
      apply integral_congr_ae
      exact ae_of_all _ (fun x => by ring)
    _ = _ := by linarith

end HenonLaneEmden
end
end WeightedVirial

end OAI
end

section
-- module Solutions.OAIQW_HenonLaneEmden.OriginCutoff
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE

section OriginCutoff

open MeasureTheory Set Filter Topology Metric
open scoped InnerProductSpace
noncomputable section
namespace HenonLaneEmden
open WeakPDE Cutoff

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma compact_radialDir {ψ : E → ℝ} (hψ : HasCompactSupport ψ) :
    HasCompactSupport (fun x => dir ψ x x) := by
  apply HasCompactSupport.intro hψ
  intro x hx
  simp only [dir,fderiv_of_notMem_tsupport ℝ hx,zero_apply]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma compact_dilation_eventually_zero {ψ : E → ℝ} (hψ : HasCompactSupport ψ)
    {x : E} (hx : x ≠ 0) :
    (fun R : ℝ => ψ (R⁻¹ • x)) =ᶠ[𝓝[>] 0] 0 := by
  obtain ⟨M,hM⟩ := hψ.isBounded.exists_norm_le
  have he : 0 < ‖x‖/(max M 0+1) := div_pos (norm_pos_iff.mpr hx) (by positivity)
  filter_upwards [self_mem_nhdsWithin,(eventually_lt_nhds he).filter_mono nhdsWithin_le_nhds] with R hR hlt
  apply image_eq_zero_of_notMem_tsupport
  intro hs
  have hh := hM _ hs
  rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hR),← div_eq_inv_mul] at hh
  have hb : R*M < ‖x‖ := by
    have hr : R*(max M 0+1) < ‖x‖ := (lt_div_iff₀ (by positivity : 0 < max M 0+1)).mp hlt
    exact (mul_le_mul_of_nonneg_left (by linarith [le_max_left M 0] : M ≤ max M 0+1) hR.le).trans_lt hr
  exact (not_le_of_gt hb) (by nlinarith [(div_le_iff₀ hR).mp hh])

lemma integral_mul_dilation_tendsto_zero [Nontrivial E] {G ψ : E → ℝ}
    (hG : Integrable G) (hψ : Continuous ψ) (hψc : HasCompactSupport ψ) :
    Tendsto (fun R : ℝ => ∫ x, G x*ψ (R⁻¹ • x)) (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨M,hM⟩ := hψc.exists_bound_of_continuous hψ
  have hh := tendsto_integral_filter_of_dominated_convergence (μ := volume) (l := 𝓝[>] (0:ℝ))
    (F := fun R x => G x*ψ (R⁻¹ • x)) (f := fun _ => (0:ℝ)) (fun x => M*‖G x‖)
    (Eventually.of_forall fun R => hG.aestronglyMeasurable.mul
      (hψ.comp (continuous_const.smul continuous_id)).aestronglyMeasurable)
    (Eventually.of_forall fun R => ae_of_all _ fun x => by
      rw [norm_mul]; exact (mul_le_mul_of_nonneg_left (hM _) (norm_nonneg _)).trans_eq (mul_comm _ _))
    (hG.norm.const_mul M) ?_
  · simpa only [integral_zero] using hh
  filter_upwards [ae_iff.mpr (show volume {x : E | ¬x ≠ 0}=0 by simp)] with x hx
  apply tendsto_const_nhds.congr'
  filter_upwards [compact_dilation_eventually_zero hψc hx] with R hR
  simp [hR]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma radialDir_dilation {ψ : E → ℝ} (hψ : Differentiable ℝ ψ) (R : ℝ) (x : E) :
    dir (fun y => ψ (R⁻¹ • y)) x x = dir ψ (R⁻¹ • x) (R⁻¹ • x) := by
  have hh := (hψ (R⁻¹ • x)).hasFDerivAt.comp x
    ((hasFDerivAt_id x).const_smul R⁻¹)
  change HasFDerivAt (fun y => ψ (R⁻¹ • y)) _ x at hh
  rw [dir,hh.fderiv]
  rfl

end HenonLaneEmden
end
end OriginCutoff

end OAI
end

section
-- module Solutions.OAIQW_HenonLaneEmden.KernelBalls
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE

section KernelBalls

open MeasureTheory Set Metric
open scoped ENNReal
noncomputable section
namespace HenonLaneEmden.WeakPDE
variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma shifted_ball_indicator (a r : ℝ) (x y : E) :
    (ball x r).indicator (fun y => ‖x-y‖^a) y =
      (ball (0:E) r).indicator (fun z => ‖z‖^a) (x-y) := by
  by_cases hy : y ∈ ball x r
  · rw [indicator_of_mem hy,indicator_of_mem]
    simpa only [mem_ball,dist_zero_right,dist_eq_norm,sub_zero,norm_sub_rev x y] using hy
  · rw [indicator_of_notMem hy,indicator_of_notMem]
    simpa only [mem_ball,dist_zero_right,dist_eq_norm,sub_zero,norm_sub_rev x y] using hy

lemma integrable_shifted_power_ball (hn : 1 ≤ Module.finrank ℝ E) {a : ℝ}
    (ha : -(Module.finrank ℝ E:ℝ) < a) (r : ℝ) (x : E) :
    Integrable ((ball x r).indicator (fun y => ‖x-y‖^a)) := by
  have hi : IntegrableOn (fun z : E => ‖z‖^a) (ball 0 r) :=
    ((locallyIntegrable_norm_power hn a ha).integrableOn_isCompact (isCompact_closedBall 0 r)).mono_set ball_subset_closedBall
  have hI := hi.integrable_indicator measurableSet_ball
  simpa only [Function.comp_def,← shifted_ball_indicator] using
    (Measure.measurePreserving_sub_left volume x).integrable_comp hI.aestronglyMeasurable |>.mpr hI

lemma integral_shifted_power_ball (a : ℝ) {r : ℝ} (hr : 0 < r) (x : E) :
    (∫ y, (ball x r).indicator (fun y => ‖x-y‖^a) y) =
      r^((Module.finrank ℝ E:ℝ)+a)*(∫ z in ball (0:E) 1, ‖z‖^a) := by
  simp_rw [shifted_ball_indicator]
  rw [integral_sub_left_eq_self (fun z => (ball (0:E) r).indicator (fun z => ‖z‖^a) z) volume x,
    integral_indicator measurableSet_ball,integral_weight_ball_scaling a hr]

lemma rpow_half_double_bound {r s : ℝ} (hr : 0 < r) (hs : r/2 ≤ s) (hs' : s ≤ 2*r) (A : ℝ) :
    s^A ≤ (2:ℝ)^|A| * r^A := by
  have hs0 : 0 < s := by linarith
  by_cases hA : 0 ≤ A
  · calc
      _ ≤ (2*r)^A := Real.rpow_le_rpow hs0.le hs' hA
      _ = _ := by rw [Real.mul_rpow (by norm_num) hr.le,abs_of_nonneg hA]
  · have hA' : A ≤ 0 := (not_le.mp hA).le
    calc
      _ ≤ (r/2)^A := Real.rpow_le_rpow_of_nonpos (by positivity) hs hA'
      _ = _ := by
        rw [Real.div_rpow hr.le (by norm_num),abs_of_nonpos hA',Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2),div_eq_mul_inv,mul_comm]

end HenonLaneEmden.WeakPDE
end
end KernelBalls

end OAI
end

section
-- module Solutions.OAIQW_HenonLaneEmden.RadialKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section RadialKernel

open MeasureTheory Set Metric
open scoped ENNReal InnerProductSpace
noncomputable section
namespace HenonLaneEmden
open WeakPDE

lemma source_near_radial_bound {n : ℕ} {v : Space n → ℝ} (hv : Continuous v)
    (hvp : ∀ x, 0 < v x) {p : ℝ} (hp : 0 < p) (A : ℝ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x : Space n, 0 < ‖x‖ → ‖x‖ ≤ 2 →
      ∀ y : Space n, ‖x-y‖ < ‖x‖/2 → source v p A y ≤ M*‖x‖^A := by
  obtain ⟨C,hC⟩ := (isCompact_closedBall (0:Space n) 3).exists_bound_of_continuousOn hv.continuousOn
  let C' := max C 1
  refine ⟨C'^p*(2:ℝ)^|A|,by positivity,?_⟩
  intro x hx hx2 y hy
  have hnorm : ‖y‖ ≤ ‖x‖+‖x-y‖ := by
    simpa only [show x+(y-x)=y by abel,norm_sub_rev x y] using norm_add_le x (y-x)
  have hnorm' : ‖x‖ ≤ ‖y‖+‖x-y‖ := by
    simpa only [show y+(x-y)=x by abel] using norm_add_le y (x-y)
  have hy0 : 0 < ‖y‖ := by linarith
  have hy3 : y ∈ closedBall (0:Space n) 3 := mem_closedBall_zero_iff.mpr (by linarith)
  have hvC : v y ≤ C' := (le_abs_self _).trans ((hC y hy3).trans (le_max_left _ _))
  have hvpow : (v y)^p ≤ C'^p := Real.rpow_le_rpow (hvp y).le hvC hp.le
  rw [source_off_zero v p A (norm_ne_zero_iff.mp hy0.ne')]
  have hweight := WeakPDE.rpow_half_double_bound hx (by linarith : ‖x‖/2 ≤ ‖y‖) (by linarith : ‖y‖ ≤ 2*‖x‖) A
  exact (mul_le_mul hweight hvpow (Real.rpow_nonneg (hvp y).le p) (by positivity)).trans_eq (by ring)

lemma radial_kernel_far_bound {n : ℕ} {x y : Space n} (hx : 0 < ‖x‖)
    (hy : ‖x‖/2 ≤ ‖x-y‖) :
    |kernelDir x (x-y)| ≤ 2*|2-(n:ℝ)| *‖x-y‖^(2-(n:ℝ)) := by
  have hs : 0 < ‖x-y‖ := lt_of_lt_of_le (half_pos hx) hy
  have he : ‖x-y‖^(1-(n:ℝ)) = ‖x-y‖^(2-(n:ℝ))/‖x-y‖ := by
    calc
      _ = ‖x-y‖^(2-(n:ℝ)-1) := by congr 1; ring
      _ = _ := by rw [Real.rpow_sub hs,Real.rpow_one]
  have hb := kernelDir_bound x (x-y)
  simp only [finrank_euclideanSpace_fin] at hb
  rw [he] at hb
  refine hb.trans ?_
  have hr : ‖x‖/‖x-y‖ ≤ 2 := (div_le_iff₀ hs).mpr (by linarith)
  calc
    _ = (‖x‖/‖x-y‖)*(|2-(n:ℝ)| *‖x-y‖^(2-(n:ℝ))) := by ring
    _ ≤ 2*(|2-(n:ℝ)| *‖x-y‖^(2-(n:ℝ))) := mul_le_mul_of_nonneg_right hr (by positivity)
    _ = _ := by ring

end HenonLaneEmden
end
end RadialKernel

end OAI
end

section
-- module Solutions.OAIQW_HenonLaneEmden.RadialGradient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section RadialGradient

open MeasureTheory Set Filter Topology Metric
open scoped ENNReal InnerProductSpace
noncomputable section
namespace HenonLaneEmden
open WeakPDE

lemma IsSolution.radial_kernel_absolute_bounded {n : ℕ} (hn : 2 ≤ n) {p q A B : ℝ}
    {u v : Space n → ℝ} (h : IsSolution n p q A B u v) (hp : 0 < p) (hq : 0 < q) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : Space n, x ≠ 0 → ‖x‖ ≤ 2 →
      (∫ y, |kernelDir x (x-y)*source v p A y|) ≤ C := by
  have hn3 := h.dimension_ge_three hn
  have hd := (newtonDenom_pos hn3).le
  have hn1 : 1 ≤ Module.finrank ℝ (Space n) := by simp; omega
  have hA := h.first_weight_gt_neg_two hn
  obtain ⟨M,hM,hnear⟩ := source_near_radial_bound h.continuous_v h.positive_v hp A
  obtain ⟨U,hU⟩ := (isCompact_closedBall (0:Space n) 2).exists_bound_of_continuousOn h.continuous_u.continuousOn
  let J : ℝ := ∫ z : Space n in ball 0 1, ‖z‖^(1-(n:ℝ))
  have hJ : 0 ≤ J := integral_nonneg (fun _ => Real.rpow_nonneg (norm_nonneg _) _)
  let C : ℝ := |2-(n:ℝ)| *M*2^(A+2)*J+2*|2-(n:ℝ)| *newtonDenom n*max U 0
  refine ⟨C,by dsimp [C]; positivity,?_⟩
  intro x hx hx2
  have hr := norm_pos_iff.mpr hx
  let H : Space n → ℝ := (ball x (‖x‖/2)).indicator (fun y => ‖x-y‖^(1-(n:ℝ)))
  have hiH : Integrable H := integrable_shifted_power_ball hn1 (by simp only [finrank_euclideanSpace_fin]; linarith) _ _
  have hH (y : Space n) : 0 ≤ H y := indicator_nonneg (fun y _ => Real.rpow_nonneg (norm_nonneg _) _) y
  have hS (y : Space n) := source_nonneg (fun y => (h.positive_v y).le) p A y
  have hdom (y : Space n) : |kernelDir x (x-y)*source v p A y| ≤
      (|2-(n:ℝ)| *‖x‖*(M*‖x‖^A))*H y+
      (2*|2-(n:ℝ)|)*(‖x-y‖^(2-(n:ℝ))*source v p A y) := by
    rw [abs_mul,abs_of_nonneg (hS y)]
    by_cases hy : ‖x-y‖ < ‖x‖/2
    · have hy' : y ∈ ball x (‖x‖/2) := by simpa only [mem_ball,dist_eq_norm,norm_sub_rev] using hy
      have hk := kernelDir_bound x (x-y)
      simp only [finrank_euclideanSpace_fin] at hk
      have hh := mul_le_mul hk (hnear x hr hx2 y hy) (hS y) (by positivity)
      rw [show H y=‖x-y‖^(1-(n:ℝ)) from indicator_of_mem hy' _]
      nlinarith [mul_nonneg (by positivity : 0 ≤ 2*|2-(n:ℝ)|) (mul_nonneg (Real.rpow_nonneg (norm_nonneg (x-y)) (2-(n:ℝ))) (hS y))]
    · have hk := mul_le_mul_of_nonneg_right (radial_kernel_far_bound hr (le_of_not_gt hy)) (hS y)
      have hzero : H y=0 := indicator_of_notMem (by simpa only [mem_ball,dist_eq_norm,norm_sub_rev] using hy) _
      rw [hzero,mul_zero,zero_add]
      simpa only [mul_assoc] using hk
  have hi := (h.gradient_u hn hq hx x).1.norm
  simp only [Real.norm_eq_abs] at hi
  have hh := integral_mono hi ((hiH.const_mul _).add ((h.kernel_g_integrable hn x).const_mul _)) hdom
  simp only [Pi.add_apply] at hh
  rw [integral_add (hiH.const_mul _) ((h.kernel_g_integrable hn x).const_mul _),integral_const_mul,integral_const_mul] at hh
  have heH : (∫ y, H y) = ‖x‖/2*J := by
    simpa only [finrank_euclideanSpace_fin,show (n:ℝ)+(1-(n:ℝ))=1 by ring,Real.rpow_one] using
      integral_shifted_power_ball (1-(n:ℝ)) (half_pos hr) x
  have heP : (∫ y, ‖x-y‖^(2-(n:ℝ))*source v p A y) = newtonDenom n*u x := by
    simpa only [rawPotential,finrank_euclideanSpace_fin] using (h.potential_u hn hq hx).symm
  rw [heH,heP] at hh
  have hpower : ‖x‖*‖x‖^A*‖x‖ = ‖x‖^(A+2) := by
    rw [show A+2=A+1+1 by ring,Real.rpow_add hr,Real.rpow_add hr,Real.rpow_one]
    ring
  have hpowle : ‖x‖^(A+2) ≤ (2:ℝ)^(A+2) := Real.rpow_le_rpow hr.le hx2 (by linarith)
  have huU : u x ≤ max U 0 := (le_abs_self _).trans ((hU x (mem_closedBall_zero_iff.mpr hx2)).trans (le_max_left _ _))
  have hbound1 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpowle (mul_nonneg (abs_nonneg (2-(n:ℝ))) hM)) hJ
  have hbound2 := mul_le_mul_of_nonneg_left huU (by positivity : 0 ≤ 2*|2-(n:ℝ)| *newtonDenom n)
  have hrw : (|2-(n:ℝ)| *‖x‖*(M*‖x‖^A))*(‖x‖/2*J) = (|2-(n:ℝ)| *M*‖x‖^(A+2)*J)/2 := by
    rw [← hpower]; ring
  rw [hrw] at hh
  dsimp [C]
  nlinarith [mul_nonneg (mul_nonneg (mul_nonneg (abs_nonneg (2-(n:ℝ))) hM) (Real.rpow_nonneg (norm_nonneg x) (A+2))) hJ]

end HenonLaneEmden
end
end RadialGradient

end OAI
end

section
-- module Solutions.OAIQW_HenonLaneEmden.RadialJoint
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section RadialJoint

open MeasureTheory Set Filter Topology Metric
open scoped ENNReal InnerProductSpace
noncomputable section
namespace HenonLaneEmden
open WeakPDE Cutoff

lemma IsSolution.integrable_joint_radial_gradient {n : ℕ} (hn : 2 ≤ n) {p q A B : ℝ}
    {u v : Space n → ℝ} (h : IsSolution n p q A B u v) (hp : 0 < p) (hq : 0 < q) :
    Integrable (fun z : Space n × Space n =>
      eta n z.1*source u q B z.1*(kernelDir z.1 (z.1-z.2)*source v p A z.2)) (volume.prod volume) := by
  have : Nontrivial (Space n) := (Module.finrank_pos_iff (R := ℝ)).mp (by simp; omega)
  have hfm := measurable_source h.continuous_u q B
  have hgm := measurable_source h.continuous_v p A
  have hηm := (continuous_eta n (E := Space n)).measurable
  have hm : Measurable (fun z : Space n × Space n =>
      eta n z.1*source u q B z.1*(kernelDir z.1 (z.1-z.2)*source v p A z.2)) := by fun_prop
  have hz : ∀ᵐ x : Space n, x ≠ 0 := ae_iff.mpr (by simp)
  apply (integrable_prod_iff hm.aestronglyMeasurable).mpr
  constructor
  · filter_upwards [hz] with x hx
    exact ((h.gradient_u hn hq hx x).1.const_mul _)
  · obtain ⟨C,hC,hbound⟩ := h.radial_kernel_absolute_bounded hn hp hq
    have hi : Integrable (fun x => C*(eta n x*source u q B x)) :=
      ((h.source_f_locallyIntegrable hn).integrable_smul_left_of_hasCompactSupport
        (continuous_eta n) (compactSupport_eta n)).const_mul C
    apply hi.mono' hm.stronglyMeasurable.norm.integral_prod_right.aestronglyMeasurable
    filter_upwards [hz] with x hx
    have hs := source_nonneg (fun y => (h.positive_u y).le) q B x
    have ht : 0 ≤ eta n x*source u q B x := mul_nonneg
      (pow_nonneg (baseProfile_nonneg ‖x‖) (N n) : 0 ≤ eta n x) hs
    have he (y : Space n) : ‖eta n x*source u q B x*(kernelDir x (x-y)*source v p A y)‖ =
        (eta n x*source u q B x)*|kernelDir x (x-y)*source v p A y| := by
      rw [norm_mul,Real.norm_eq_abs,abs_of_nonneg ht,Real.norm_eq_abs]
    simp_rw [he]
    rw [integral_const_mul,Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg ht (integral_nonneg (fun y => abs_nonneg _)))]
    by_cases hx2 : ‖x‖ ≤ 2
    · exact (mul_le_mul_of_nonneg_left (hbound x hx hx2) ht).trans_eq (mul_comm _ _)
    · rw [eta_eq_zero (le_of_not_ge hx2)]; simp

lemma IsSolution.integrable_eta_source_radialDir {n : ℕ} (hn : 2 ≤ n) {p q A B : ℝ}
    {u v : Space n → ℝ} (h : IsSolution n p q A B u v) (hp : 0 < p) (hq : 0 < q) :
    Integrable (fun x => eta n x*source u q B x*dir u x x) := by
  have : Nontrivial (Space n) := (Module.finrank_pos_iff (R := ℝ)).mp (by simp; omega)
  have hi := (h.integrable_joint_radial_gradient hn hp hq).integral_prod_left.const_mul ((newtonDenom n)⁻¹)
  apply hi.congr
  filter_upwards [ae_iff.mpr (show volume {x : Space n | ¬x ≠ 0}=0 by simp)] with x hx
  rw [integral_const_mul]
  have hg := (h.gradient_u hn hq hx x).2
  rw [← hg]
  field_simp [ne_of_gt (newtonDenom_pos (h.dimension_ge_three hn))]

lemma IsSolution.integral_eta_source_radialDir {n : ℕ} (hn : 2 ≤ n) {p q A B : ℝ}
    {u v : Space n → ℝ} (h : IsSolution n p q A B u v) (hp : 0 < p) (hq : 0 < q) :
    (∫ x, eta n x*source u q B x*dir u x x) = (newtonDenom n)⁻¹*
      ∫ z : Space n × Space n, eta n z.1*source u q B z.1*
        (kernelDir z.1 (z.1-z.2)*source v p A z.2) ∂volume.prod volume := by
  have : Nontrivial (Space n) := (Module.finrank_pos_iff (R := ℝ)).mp (by simp; omega)
  rw [integral_prod _ (h.integrable_joint_radial_gradient hn hp hq),← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [ae_iff.mpr (show volume {x : Space n | ¬x ≠ 0}=0 by simp)] with x hx
  rw [integral_const_mul,← (h.gradient_u hn hq hx x).2]
  field_simp [ne_of_gt (newtonDenom_pos (h.dimension_ge_three hn))]

end HenonLaneEmden
end
end RadialJoint

end OAI
end

section
-- module Solutions.OAIQW_HenonLaneEmden.OriginVirial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section OriginVirial

open MeasureTheory Set Filter Topology Metric
open scoped InnerProductSpace
noncomputable section
namespace HenonLaneEmden
open WeakPDE Cutoff

lemma integrable_mul_dilation {n : ℕ} {G ψ : Space n → ℝ}
    (hG : Integrable G) (hψ : Continuous ψ) (hψc : HasCompactSupport ψ) (R : ℝ) :
    Integrable (fun x => G x*ψ (R⁻¹ • x)) := by
  obtain ⟨M,hM⟩ := hψc.exists_bound_of_continuous hψ
  exact hG.mul_bdd (hψ.comp (continuous_id.const_smul (R⁻¹))).aestronglyMeasurable
    (ae_of_all _ fun x => hM _)

lemma radialDir_inner_cutoff {n : ℕ} (ξ : ContDiffBump (0:Space n)) (R : ℝ) (x : Space n) :
    dir (fun y => eta n y-eta n y*ξ (R⁻¹ • y)) x x =
      -w n x*(1-ξ (R⁻¹ • x))-eta n x*dir ξ (R⁻¹ • x) (R⁻¹ • x) := by
  have hξ : ContDiff ℝ 2 (ξ : Space n → ℝ) := ξ.contDiff
  have hξdiff := hξ.differentiable (by norm_num)
  have hηd := (hasFDerivAt_eta n x).differentiableAt
  have hξd : Differentiable ℝ (fun y : Space n => ξ (R⁻¹ • y)) :=
    hξdiff.comp (differentiable_id.const_smul (R⁻¹))
  have he : dir (fun y => eta n y-eta n y*ξ (R⁻¹ • y)) x x =
      dir (eta n) x x-dir (fun y => eta n y*ξ (R⁻¹ • y)) x x := by
    have hm : DifferentiableAt ℝ (fun y => eta n y*ξ (R⁻¹ • y)) x := hηd.mul (hξd x)
    unfold dir
    rw [show (fun y => eta n y-eta n y*ξ (R⁻¹ • y)) = eta n-(fun y => eta n y*ξ (R⁻¹ • y)) by rfl,
      fderiv_sub hηd hm]
    rfl
  rw [he,dir_mul hηd (hξd x),radialDir_dilation hξdiff]
  simp only [w,dir]
  ring

lemma IsSolution.weighted_virial {n : ℕ} (hn : 2 ≤ n) {p q A B : ℝ}
    {u v : Space n → ℝ} (h : IsSolution n p q A B u v) (hp : 0 < p) (hq : 0 < q) :
    ((n:ℝ)+B)*weightedEnergy (eta n) u q B-weightedEnergy (w n) u q B =
      -(q+1)*(∫ x, eta n x*source u q B x*dir u x x) := by
  have : Nontrivial (Space n) := (Module.finrank_pos_iff (R := ℝ)).mp (by simp; omega)
  let ξ : ContDiffBump (0:Space n) := ⟨1,2,by norm_num,by norm_num⟩
  let ψ (x : Space n) := dir ξ x x
  have hψ : Continuous ψ := ((ξ.contDiff : ContDiff ℝ 2 (ξ : Space n → ℝ)).continuous_fderiv (by norm_num)).clm_apply continuous_id
  have hψc : HasCompactSupport ψ := compact_radialDir ξ.hasCompactSupport
  let G (x : Space n) := energyDensity u q B x*(((n:ℝ)+B)*eta n x-w n x)
  let H (x : Space n) := energyDensity u q B x*eta n x
  let J (x : Space n) := eta n x*source u q B x*dir u x x
  have hG : Integrable G := (h.energy_locallyIntegrable hn).integrable_smul_right_of_hasCompactSupport
    ((continuous_const.mul (continuous_eta n)).sub (continuous_w n))
    (((compactSupport_eta n).mul_left).sub (compactSupport_w n))
  have hH : Integrable H := (h.energy_locallyIntegrable hn).integrable_smul_right_of_hasCompactSupport
    (continuous_eta n) (compactSupport_eta n)
  have hJ : Integrable J := h.integrable_eta_source_radialDir hn hp hq
  have he : ∀ᶠ R : ℝ in 𝓝[>] 0,
      ((∫ x, G x)-(∫ x, G x*ξ (R⁻¹ • x)))-(∫ x, H x*ψ (R⁻¹ • x)) =
        -(q+1)*((∫ x, J x)-(∫ x, J x*ξ (R⁻¹ • x))) := by
    filter_upwards [self_mem_nhdsWithin] with R hR
    obtain ⟨hθ,hθc,hθ0⟩ := cutoff_test_off_origin (contDiff_eta (by omega : 1 ≤ n)) (compactSupport_eta n) ξ hR
    have hh := weighted_virial_off_origin h.regular_u h.positive_u q B (hθ.of_le (by norm_num)) hθc hθ0
    have hL : (∫ x, energyDensity u q B x*(((n:ℝ)+B)*(eta n x-eta n x*ξ (R⁻¹ • x))+
        dir (fun y => eta n y-eta n y*ξ (R⁻¹ • y)) x x)) =
        ((∫ x, G x)-(∫ x, G x*ξ (R⁻¹ • x)))-(∫ x,H x*ψ (R⁻¹ • x)) := by
      have hsub : Integrable (fun x => G x-G x*ξ (R⁻¹ • x)) :=
        hG.sub (integrable_mul_dilation hG ξ.continuous ξ.hasCompactSupport R)
      rw [← integral_sub hG (integrable_mul_dilation hG ξ.continuous ξ.hasCompactSupport R),
        ← integral_sub hsub (integrable_mul_dilation hH hψ hψc R)]
      apply integral_congr_ae
      exact ae_of_all _ fun x => by dsimp only; rw [radialDir_inner_cutoff]; dsimp only [G,H,ψ]; ring
    have hR' : (∫ x, (eta n x-eta n x*ξ (R⁻¹ • x))*source u q B x*dir u x x) =
        (∫ x, J x)-(∫ x,J x*ξ (R⁻¹ • x)) := by
      rw [← integral_sub hJ (integrable_mul_dilation hJ ξ.continuous ξ.hasCompactSupport R)]
      apply integral_congr_ae
      exact ae_of_all _ fun x => by dsimp only [J]; ring
    rwa [hL,hR'] at hh
  have hlimL := ((tendsto_const_nhds (x := ∫ x,G x)).sub (integral_mul_dilation_tendsto_zero hG ξ.continuous ξ.hasCompactSupport)).sub
    (integral_mul_dilation_tendsto_zero hH hψ hψc)
  have hlimR := ((tendsto_const_nhds (x := ∫ x,J x)).sub (integral_mul_dilation_tendsto_zero hJ ξ.continuous ξ.hasCompactSupport)).const_mul (-(q+1))
  have hh : (∫ x, G x) = -(q+1)*(∫ x,J x) := by
    simpa only [sub_zero] using tendsto_nhds_unique hlimL (hlimR.congr' (he.mono fun _ hR => hR.symm))
  rw [← hh]
  have hiη := h.integrable_source_energy_weight hn (continuous_eta n) (compactSupport_eta n)
  have hiw := h.integrable_source_energy_weight hn (continuous_w n) (compactSupport_w n)
  rw [weightedEnergy,weightedEnergy,← integral_const_mul,← integral_sub (hiη.const_mul _) hiw]
  apply integral_congr_ae
  filter_upwards [ae_iff.mpr (show volume {x : Space n | ¬x ≠ 0}=0 by simp)] with x hx
  dsimp only [G]
  rw [energyDensity_eq_source_mul h.positive_u q B hx]
  ring

end HenonLaneEmden
end
end OriginVirial

end OAI
end

section
-- module Solutions.OAIQW_HenonLaneEmden.SymmetricVirial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section SymmetricVirial

open MeasureTheory Set Filter Topology Metric
open scoped ENNReal InnerProductSpace
noncomputable section
namespace HenonLaneEmden
open WeakPDE Cutoff

lemma radial_gradient_pair {n : ℕ} (x y : Space n) :
    (newtonDenom n)⁻¹*(eta n x*kernelDir x (x-y)+eta n y*kernelDir y (y-x)) =
      (2-(n:ℝ))*newtonKernel n (x,y)*fluxFactor n (x,y) := by
  by_cases hxy : x=y
  · subst y
    simp only [sub_self,kernelDir,inner_zero_left,mul_zero,zero_add,fluxFactor,zero_div]
  have hr : 0 < ‖x-y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxy)
  have he : ‖x-y‖^(-(n:ℝ)) = ‖x-y‖^(2-(n:ℝ))/‖x-y‖^2 := by
    rw [← Real.rpow_two,← Real.rpow_sub hr]
    congr 1; ring
  simp only [kernelDir,finrank_euclideanSpace_fin,norm_sub_rev y x,he,newtonKernel,fluxFactor,X,
    inner_sub_right,real_inner_smul_right]
  rw [show y-x=-(x-y) by abel,inner_neg_left]
  ring

lemma IsSolution.integrable_fluxFactor {n : ℕ} (hn : 2 ≤ n) {p q A B : ℝ}
    {u v : Space n → ℝ} (h : IsSolution n p q A B u v) (hp : 0 < p) (hq : 0 < q) :
    Integrable (fluxFactor n) (interaction (source u q B) (source v p A)) := by
  have hn3 := h.dimension_ge_three hn
  have hfm := measurable_source h.continuous_u q B
  have hgm := measurable_source h.continuous_v p A
  have hf0 := source_nonneg (fun x => (h.positive_u x).le) q B
  have hg0 := source_nonneg (fun x => (h.positive_v x).le) p A
  apply (integrable_interaction_iff hn3 hfm hgm hf0 hg0 _).mpr
  have hi := ((h.integrable_joint_radial_gradient hn hp hq).add
    (h.swap.integrable_joint_radial_gradient hn hq hp).swap).const_mul ((newtonDenom n)⁻¹/(2-(n:ℝ)))
  apply hi.congr
  exact ae_of_all _ (fun z => by
    dsimp only [Function.comp_def,Prod.swap,Pi.add_apply]
    have he := radial_gradient_pair z.1 z.2
    have hn0 : 2-(n:ℝ) ≠ 0 := by
      have hh : (3:ℝ) ≤ n := by exact_mod_cast hn3
      linarith
    have hh := congrArg (fun a : ℝ => source u q B z.1*source v p A z.2*a/(2-(n:ℝ))) he
    field_simp [hn0] at hh ⊢
    nlinarith [hh])

lemma IsSolution.integral_radial_pair {n : ℕ} (hn : 2 ≤ n) {p q A B : ℝ}
    {u v : Space n → ℝ} (h : IsSolution n p q A B u v) (hp : 0 < p) (hq : 0 < q) :
    (∫ x, eta n x*source u q B x*dir u x x)+(∫ x, eta n x*source v p A x*dir v x x) =
      (2-(n:ℝ))*(∫ z, fluxFactor n z ∂interaction (source u q B) (source v p A)) := by
  rw [h.integral_eta_source_radialDir hn hp hq,h.swap.integral_eta_source_radialDir hn hq hp,
    ← integral_prod_swap (fun z : Space n × Space n => eta n z.1*source v p A z.1*
        (kernelDir z.1 (z.1-z.2)*source u q B z.2))]
  have hi := (h.swap.integrable_joint_radial_gradient hn hq hp).swap
  simp only [Function.comp_def] at hi
  rw [← mul_add,← integral_add (h.integrable_joint_radial_gradient hn hp hq) hi]
  rw [integral_interaction (h.dimension_ge_three hn) (measurable_source h.continuous_u q B)
    (measurable_source h.continuous_v p A) (source_nonneg (fun x => (h.positive_u x).le) q B)
    (source_nonneg (fun x => (h.positive_v x).le) p A),← integral_const_mul,← integral_const_mul]
  apply integral_congr_ae
  exact ae_of_all _ (fun z => by
    dsimp only [Prod.swap]
    have he := congrArg (fun a : ℝ => source u q B z.1*source v p A z.2*a) (radial_gradient_pair z.1 z.2)
    nlinarith [he])

lemma IsSolution.symmetric_virial {n : ℕ} (hn : 2 ≤ n) {p q A B : ℝ}
    {u v : Space n → ℝ} (h : IsSolution n p q A B u v) (hp : 0 < p) (hq : 0 < q) :
    ((n:ℝ)+B)/(q+1)*weightedEnergy (eta n) u q B+
      ((n:ℝ)+A)/(p+1)*weightedEnergy (eta n) v p A-
      ((q+1)⁻¹*weightedEnergy (w n) u q B+(p+1)⁻¹*weightedEnergy (w n) v p A) =
      ((n:ℝ)-2)*(∫ z, fluxFactor n z ∂interaction (source u q B) (source v p A)) := by
  have hf := h.weighted_virial hn hp hq
  have hg := h.swap.weighted_virial hn hq hp
  have hpair := h.integral_radial_pair hn hp hq
  have hp1 : p+1 ≠ 0 := by positivity
  have hq1 : q+1 ≠ 0 := by positivity
  field_simp
  linear_combination (p+1)*hf+(q+1)*hg-(p+1)*(q+1)*hpair

end HenonLaneEmden
end
end SymmetricVirial

end OAI
end

section
-- module Solutions.OAIQW_HenonLaneEmden.LocalizationIntegral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section LocalizationIntegral

open MeasureTheory Set Metric
open scoped ENNReal
noncomputable section
namespace HenonLaneEmden
open Cutoff

@[fun_prop] lemma measurable_localError (n : ℕ) : Measurable (localError : Space n × Space n → ℝ) := by
  unfold localError
  have hη := (continuous_eta n (E := Space n)).measurable
  have hw := (continuous_w n (E := Space n)).measurable
  fun_prop

end HenonLaneEmden
end
end LocalizationIntegral

end OAI
end

section
-- module Solutions.OAIQW_HenonLaneEmden.AngularBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section AngularBounds

open MeasureTheory Set Metric
open scoped ENNReal
noncomputable section
namespace HenonLaneEmden
open Cutoff AdaptiveCap SpatialComponents

lemma IsSolution.integrable_radialWeight {n : ℕ} (hn : 2 ≤ n) {p q A B : ℝ}
    {u v : Space n → ℝ} (h : IsSolution n p q A B u v) (hq : 0 < q) :
    Integrable (fun z : Space n × Space n => w n z.1*radialFactor z) (interaction (source u q B) (source v p A)) := by
  have hi := (h.weight_left hn hq (continuous_w n) (compactSupport_w n) (w_nonneg n)).1
  apply hi.mono' (((continuous_w n).measurable.comp measurable_fst).mul (measurable_radialFactor n)).aestronglyMeasurable
  exact ae_of_all _ (fun z => by
    dsimp only [Function.comp_def,Pi.mul_apply]
    rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (w_nonneg n _) (radialFactor_bounds z).1)]
    exact mul_le_of_le_one_right (w_nonneg n _) (radialFactor_bounds z).2)

end HenonLaneEmden
end
end AngularBounds

end OAI
end

section
-- module Solutions.OAIQW_HenonLaneEmden.RelativeLocalization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section RelativeLocalization

open MeasureTheory Set Metric
noncomputable section
namespace HenonLaneEmden
open Cutoff

lemma IsSolution.localQ_identity {n : ℕ} (hn : 2 ≤ n) {p q A B : ℝ}
    {u v : Space n → ℝ} (h : IsSolution n p q A B u v) (hp : 0 < p) (hq : 0 < q) :
    localQ (source u q B) (source v p A) =
      (∫ z, fluxFactor n z ∂interaction (source u q B) (source v p A))-weightedEnergy (eta n) u q B+
        (∫ z : Space n × Space n, w n z.1*radialFactor z ∂interaction (source u q B) (source v p A)) := by
  have hη := h.weight_left hn hq (continuous_eta n) (compactSupport_eta n) (eta_nonneg n)
  have hi : Integrable (fun z : Space n × Space n => fluxFactor n z-eta n z.1) _ :=
    (h.integrable_fluxFactor hn hp hq).sub hη.1
  rw [localQ,integral_add hi (h.integrable_radialWeight hn hq),
    integral_sub (h.integrable_fluxFactor hn hp hq) hη.1,hη.2]

lemma IsSolution.closing_identity {n : ℕ} (hn : 2 ≤ n) {p q A B : ℝ}
    {u v : Space n → ℝ} (h : IsSolution n p q A B u v) (hp : 0 < p) (hq : 0 < q) :
    (((n:ℝ)+B)/(q+1)-((n:ℝ)-2))*weightedEnergy (eta n) u q B+
      (((n:ℝ)+A)/(p+1))*weightedEnergy (eta n) v p A =
        (q+1)⁻¹*weightedEnergy (w n) u q B+(p+1)⁻¹*weightedEnergy (w n) v p A-
        radialPressure (source u q B) (source v p A)+((n:ℝ)-2)*localQ (source u q B) (source v p A) := by
  have hh := h.symmetric_virial hn hp hq
  rw [h.localQ_identity hn hp hq,radialPressure]
  nlinarith [hh]

end HenonLaneEmden
end
end RelativeLocalization

end OAI
end

section
-- module Solutions.OAIQW_HenonLaneEmden.UniformEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section UniformEnergy

open MeasureTheory Set Metric
open scoped ENNReal
noncomputable section
namespace HenonLaneEmden
open Cutoff

lemma weighted_uniform_energy_oai {n : ℕ} (hn : 3 ≤ n) {p q A B : ℝ} (hp : 0 < p) (hq : 0 < q)
    (hsub : Subcritical n p q A B) : ∃ C : ℝ, 0 ≤ C ∧
      ∀ u v : Space n → ℝ, IsSolution n p q A B u v →
        weightedEnergy (eta n) u q B+weightedEnergy (eta n) v p A ≤ C := by
  let c₁ := ((n:ℝ)+B)/(q+1)-((n:ℝ)-2)
  let c₂ := ((n:ℝ)+A)/(p+1)
  let γ := c₁+c₂
  have hγ : 0 < γ := by dsimp [γ,c₁,c₂]; unfold Subcritical at hsub; linarith
  have hn2 : 0 ≤ (n:ℝ)-2 := by
    have hn' : (3:ℝ) ≤ n := by exact_mod_cast hn
    linarith
  let K := (n:ℝ)-2+|(c₁-c₂)/2|
  have hK : 0 ≤ K := add_nonneg hn2 (abs_nonneg _)
  let ε := γ/(4*(1+K))
  have hε : 0 < ε := div_pos hγ (by positivity)
  have hεeq : (1+K)*ε=γ/4 := by
    dsimp [ε]
    field_simp
  obtain ⟨CP,hCP,hP⟩ := pressure_relative hn hp hq hε
  obtain ⟨CL,hCL,hL⟩ := localization_relative (by omega : 2 ≤ n) hp hq hε
  refine ⟨4*(CP+K*CL)/γ,by positivity,?_⟩
  intro u v h
  let Ef := weightedEnergy (eta n) u q B
  let Eg := weightedEnergy (eta n) v p A
  let Q := localQ (source u q B) (source v p A)
  let T := (q+1)⁻¹*weightedEnergy (w n) u q B+(p+1)⁻¹*weightedEnergy (w n) v p A-
      radialPressure (source u q B) (source v p A)
  have hEid : c₁*Ef+c₂*Eg=T+((n:ℝ)-2)*Q := h.closing_identity (by omega) hp hq
  have hT : T ≤ ε*(Ef+Eg)+CP := hP u v h
  have hQ : |Q|+|Ef-Eg| ≤ ε*(Ef+Eg)+CL := hL u v h
  have hcomb : γ/2*(Ef+Eg)=T+((n:ℝ)-2)*Q-((c₁-c₂)/2)*(Ef-Eg) := by
    dsimp only [γ]
    nlinarith [hEid]
  have hneg : -((c₁-c₂)/2)*(Ef-Eg) ≤ |(c₁-c₂)/2| *|Ef-Eg| := by
    simpa only [abs_mul,neg_mul] using neg_le_abs (((c₁-c₂)/2)*(Ef-Eg))
  have herror : ((n:ℝ)-2)*Q-((c₁-c₂)/2)*(Ef-Eg) ≤ K*(|Q|+|Ef-Eg|) := by
    have h1 := mul_le_mul_of_nonneg_left (le_abs_self Q) hn2
    have h2 := mul_nonneg hn2 (abs_nonneg (Ef-Eg))
    have h3 := mul_nonneg (abs_nonneg ((c₁-c₂)/2)) (abs_nonneg Q)
    dsimp only [K]
    nlinarith [h1,hneg,h2,h3]
  have hclose : γ/2*(Ef+Eg) ≤ (1+K)*ε*(Ef+Eg)+CP+K*CL := by
    have hmul := mul_le_mul_of_nonneg_left hQ hK
    nlinarith [hcomb,herror,hT,hmul]
  rw [hεeq] at hclose
  apply (le_div_iff₀ hγ).mpr
  change (Ef+Eg)*γ ≤ 4*(CP+K*CL)
  nlinarith [hclose]

end HenonLaneEmden
end
end UniformEnergy

end OAI
end

theorem solution : type_of% @OAI.HenonLaneEmden.weighted_uniform_energy_oai := @OAI.HenonLaneEmden.weighted_uniform_energy_oai
