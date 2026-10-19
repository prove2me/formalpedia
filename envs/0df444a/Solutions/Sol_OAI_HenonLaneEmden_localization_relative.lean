-- Prove2me | solution 1 for OAI.HenonLaneEmden.localization_relative
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-19T01:41:47.367611+00:00
-- url     : https://prove2.me/submissions/8bb1c617-9069-4b24-a14f-cf4251aebd23

import Mathlib
import Definitions.Def_HenonEmden
import Definitions.Def_OAIQWHLE000
import Theorems.Thm_OAI_HenonLaneEmden_WeakPDE_potential_constant
import Theorems.Thm_OAI_HenonLaneEmden_WeakPDE_weak_newton_lower

section
-- module Solutions.OAIQW_HenonLaneEmden.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : p) :
    (if p then a else b) = a := if_pos h
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
-- module Solutions.OAIQW_HenonLaneEmden.Scaling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE

section Scaling

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
noncomputable section

open Set Filter Topology
namespace HenonLaneEmden


lemma alpha_pos {p q A B : ℝ} (hp : 0 < p) (hA : -2 < A) (hB : -2 < B)
    (hpq : 1 < p*q) : 0 < alpha p q A B := by
  apply div_pos _ (sub_pos.mpr hpq)
  exact add_pos (by linarith) (mul_pos hp (by linarith))

end HenonLaneEmden

end
end Scaling

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

lemma IsSolution.sourceMass_g_pos {n : ℕ} (hn : 2 ≤ n) {p q A B : ℝ}
    {u v : Space n → ℝ} (h : IsSolution n p q A B u v) {R : ℝ} (hR : 0 < R) :
    0 < sourceMass v p A R := by
  have : Nontrivial (Space n) := Module.nontrivial_of_finrank_pos (R := ℝ) (by simp; omega)
  have hi : IntegrableOn (source v p A) (Metric.ball (0:Space n) R) :=
    ((h.source_g_locallyIntegrable hn).integrableOn_isCompact (isCompact_closedBall _ R)).mono_set Metric.ball_subset_closedBall
  apply (integral_pos_iff_support_of_nonneg_ae (Eventually.of_forall (source_nonneg (fun x => (h.positive_v x).le) p A)) hi).mpr
  have hz : ({0}ᶜ : Set (Space n)) ⊆ Function.support (source v p A) := fun x hx =>
    ne_of_gt (source_pos h.positive_v p A hx)
  apply lt_of_lt_of_le _ (measure_mono hz)
  rw [Measure.restrict_apply (measurableSet_singleton _).compl,inter_comm]
  change 0 < volume (Metric.ball (0:Space n) R \ {0})
  rw [measure_sdiff_null (by simp)]
  exact Metric.measure_ball_pos volume _ hR

lemma IsSolution.lowerMass_g_pos {n : ℕ} (hn : 2 ≤ n) {p q A B : ℝ}
    {u v : Space n → ℝ} (h : IsSolution n p q A B u v) {R : ℝ} (hR : 0 < R) :
    0 < lowerMass v p A R := by
  rw [lowerMass_eq _ _ _ hR]
  exact mul_pos (mul_pos (ballConstant_pos (h.dimension_ge_three hn)) (Real.rpow_pos_of_pos hR _))
    (h.sourceMass_g_pos hn hR)

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

lemma IsSolution.lowerMass_g_coupling {n : ℕ} (hn : 2 ≤ n) {p q A B : ℝ}
    {u v : Space n → ℝ} (h : IsSolution n p q A B u v) (hp : 0 < p)
    {R : ℝ} (hR : 0 < R) :
    ballConstant n*weightMass n A*R^(2+A)*(lowerMass u q B R)^p ≤ lowerMass v p A R := by
  have hh := integral_source_ge_lower (h.dimension_ge_three hn) h.continuous_v h.positive_v hp.le
    (h.first_weight_gt_neg_two hn) hR (h.swap.lowerMass_g_pos hn hR).le
    (fun x hx => h.swap.lowerMass_g_le hn hR (Metric.ball_subset_closedBall hx))
  have hmul := mul_le_mul_of_nonneg_left hh
    (mul_nonneg (ballConstant_pos (h.dimension_ge_three hn)).le (Real.rpow_nonneg hR.le (2-(n:ℝ))))
  conv_rhs => rw [lowerMass_eq _ _ _ hR]
  have he : R^(2+A) = R^(2-(n:ℝ))*R^((n:ℝ)+A) := by rw [← Real.rpow_add hR]; congr 1; ring
  calc
    _ = ballConstant n*R^(2-(n:ℝ)) * (lowerMass u q B R ^ p * R ^ ((n:ℝ) + A) * weightMass n A) := by rw [he]; ring
    _ ≤ _ := hmul
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
lemma coupled_power_lower {U V c d R a b p q : ℝ}
    (hU : 0 < U) (_hV : 0 < V) (hc : 0 < c) (hd : 0 < d) (hR : 0 < R)
    (hp : 0 < p) (h1 : c*R^a*V^p ≤ U) (h2 : d*R^b*U^q ≤ V) :
    c*d^p*R^(a+p*b) ≤ U^(1-p*q) := by
  have hh := Real.rpow_le_rpow (by positivity : 0 ≤ d*R^b*U^q) h2 hp.le
  have hh' := (mul_le_mul_of_nonneg_left hh (mul_nonneg hc.le (Real.rpow_nonneg hR.le a))).trans h1
  have he : c*R^a*(d*R^b*U^q)^p = c*d^p*R^(a+p*b)*U^(p*q) := by
    rw [Real.mul_rpow (by positivity) (Real.rpow_nonneg hU.le q),
      Real.mul_rpow hd.le (Real.rpow_nonneg hR.le b),
      ← Real.rpow_mul hR.le,← Real.rpow_mul hU.le,Real.rpow_add hR]
    simp only [mul_comm b p,mul_comm q p]
    ring
  rw [he] at hh'
  rw [Real.rpow_sub hU,Real.rpow_one]
  exact (le_div_iff₀ (Real.rpow_pos_of_pos hU (p*q))).mpr hh'

lemma no_small_product_coupled {U V : ℝ → ℝ} {c d a b p q M : ℝ}
    (hc : 0 < c) (hd : 0 < d) (ha : 0 < a) (hb : 0 < b) (hp : 0 < p)
    (hU : ∀ R > 0, 0 < U R) (hV : ∀ R > 0, 0 < V R)
    (h1 : ∀ R > 0, c*R^a*(V R)^p ≤ U R)
    (h2 : ∀ R > 0, d*R^b*(U R)^q ≤ V R)
    (hbound : ∀ R > 0, U R ≤ M) : 1 < p*q := by
  by_contra hh
  have hpq : p*q ≤ 1 := le_of_not_gt hh
  have hK : 0 < c*d^p := mul_pos hc (Real.rpow_pos_of_pos hd p)
  have hB : ∀ R > 0, c*d^p*R^(a+p*b) ≤ M^(1-p*q) := by
    intro R hR
    exact (coupled_power_lower (hU R hR) (hV R hR) hc hd hR hp (h1 R hR) (h2 R hR)).trans
      (Real.rpow_le_rpow (hU R hR).le (hbound R hR) (by linarith))
  have ht : Tendsto (fun R : ℝ => c*d^p*R^(a+p*b)) atTop atTop :=
    (tendsto_rpow_atTop (add_pos ha (mul_pos hp hb))).const_mul_atTop hK
  obtain ⟨R,hR,hgt⟩ := ((eventually_gt_atTop (0:ℝ)).and
    (ht.eventually (eventually_gt_atTop (M^(1-p*q))))).exists
  exact (not_lt_of_ge (hB R hR)) hgt

lemma coupled_upper_one {U V c d p q : ℝ}
    (hU : 0 < U) (hV : 0 < V) (hc : 0 < c) (hd : 0 < d)
    (hp : 0 < p) (hpq : 1 < p*q) (h1 : c*V^p ≤ U) (h2 : d*U^q ≤ V) :
    U ≤ (c*d^p)^(1/(1-p*q)) := by
  have hh := coupled_power_lower (a := 0) (b := 0) (R := 1) hU hV hc hd zero_lt_one hp
    (by simpa using h1) (by simpa using h2)
  simp only [Real.one_rpow,mul_one] at hh
  have hK : 0 < c*d^p := mul_pos hc (Real.rpow_pos_of_pos hd p)
  simpa only [one_div] using (Real.le_rpow_inv_iff_of_neg hU hK (show 1-p*q < 0 by linarith)).mpr hh
end HenonLaneEmden

namespace HenonLaneEmden
open WeakPDE
lemma IsSolution.product_gt_one {n : ℕ} (hn : 2 ≤ n) {p q A B : ℝ}
    {u v : Space n → ℝ} (h : IsSolution n p q A B u v) (hp : 0 < p) (hq : 0 < q) : 1 < p*q := by
  have hn3 := h.dimension_ge_three hn
  have hA := h.first_weight_gt_neg_two hn
  have hB := h.swap.first_weight_gt_neg_two hn
  apply no_small_product_coupled (U := lowerMass v p A) (V := lowerMass u q B)
    (M := u 0) (mul_pos (ballConstant_pos hn3) (weightMass_pos hn3 hA))
    (mul_pos (ballConstant_pos hn3) (weightMass_pos hn3 hB))
    (show 0 < 2+A by linarith) (show 0 < 2+B by linarith) hp
    (fun _ hR => h.lowerMass_g_pos hn hR) (fun _ hR => h.swap.lowerMass_g_pos hn hR)
    (fun _ hR => h.lowerMass_g_coupling hn hp hR)
  · exact fun R hR => h.swap.lowerMass_g_coupling hn hq hR
  · intro R hR
    exact h.lowerMass_g_le hn hR (by simpa using hR.le)
end HenonLaneEmden

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
-- module Solutions.OAIQW_HenonLaneEmden.MassGrowth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section MassGrowth

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

lemma sourceConstant_pos {n : ℕ} (hn : 3 ≤ n) {p q A B : ℝ} (hA : -2 < A) (hB : -2 < B) :
    0 < sourceConstant n p q A B := by
  exact div_pos (Real.rpow_pos_of_pos
    (mul_pos (mul_pos (ballConstant_pos hn) (weightMass_pos hn hA))
      (Real.rpow_pos_of_pos (mul_pos (ballConstant_pos hn) (weightMass_pos hn hB)) p)) _)
    (ballConstant_pos hn)

lemma IsSolution.sourceMass_g_upper {n : ℕ} (hn : 2 ≤ n) {p q A B : ℝ}
    {u v : Space n → ℝ} (h : IsSolution n p q A B u v) (hp : 0 < p) (hq : 0 < q)
    {R : ℝ} (hR : 0 < R) :
    sourceMass v p A R ≤ sourceConstant n p q A B * R^((n:ℝ)-2-alpha p q A B) := by
  have hn3 := h.dimension_ge_three hn
  have hA := h.first_weight_gt_neg_two hn
  have hB := h.swap.first_weight_gt_neg_two hn
  have hpq := h.product_gt_one hn hp hq
  let c := ballConstant n*weightMass n A
  let d := ballConstant n*weightMass n B
  have hc : 0 < c := mul_pos (ballConstant_pos hn3) (weightMass_pos hn3 hA)
  have hd : 0 < d := mul_pos (ballConstant_pos hn3) (weightMass_pos hn3 hB)
  have hu := coupled_upper_one (h.lowerMass_g_pos hn hR) (h.swap.lowerMass_g_pos hn hR)
    (mul_pos hc (Real.rpow_pos_of_pos hR (2+A)))
    (mul_pos hd (Real.rpow_pos_of_pos hR (2+B))) hp hpq
    (h.lowerMass_g_coupling hn hp hR) (h.swap.lowerMass_g_coupling hn hq hR)
  have hexp : (2+A+p*(2+B))*(1/(1-p*q)) = -alpha p q A B := by
    unfold alpha
    field_simp [ne_of_gt (show 0 < p*q-1 by linarith), ne_of_lt (show 1-p*q < 0 by linarith)]
    ring
  have he : ((c*R^(2+A))*(d*R^(2+B))^p)^(1/(1-p*q)) =
      (c*d^p)^(1/(1-p*q))*R^(-alpha p q A B) := by
    rw [Real.mul_rpow hd.le (Real.rpow_nonneg hR.le (2+B)),← Real.rpow_mul hR.le]
    have hinner : c*R^(2+A)*(d^p*R^((2+B)*p)) = c*d^p*R^(2+A+p*(2+B)) := by
      conv_rhs => rw [Real.rpow_add hR (2+A) (p*(2+B))]
      rw [mul_comm (2+B) p]; ring
    rw [hinner,Real.mul_rpow (mul_nonneg hc.le (Real.rpow_nonneg hd.le p))
      (Real.rpow_nonneg hR.le _),← Real.rpow_mul hR.le,hexp]
  rw [he,lowerMass_eq _ _ _ hR] at hu
  have hfactor : ballConstant n*R^(2-(n:ℝ)) *
      (sourceConstant n p q A B * R^((n:ℝ)-2-alpha p q A B)) =
      (c*d^p)^(1/(1-p*q))*R^(-alpha p q A B) := by
    unfold sourceConstant
    change ballConstant n*R^(2-(n:ℝ))*((c*d^p)^(1/(1-p*q))/ballConstant n * R^((n:ℝ)-2-alpha p q A B)) = _
    rw [show R^(-alpha p q A B) = R^(2-(n:ℝ))*R^((n:ℝ)-2-alpha p q A B) by
      rw [← Real.rpow_add hR]; congr 1; ring]
    field_simp [ne_of_gt (ballConstant_pos hn3)]
  rw [← hfactor] at hu
  exact (mul_le_mul_iff_right₀ (mul_pos (ballConstant_pos hn3) (Real.rpow_pos_of_pos hR _))).mp hu
end HenonLaneEmden

end
end MassGrowth

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

lemma continuous_gapProfile : Continuous gapProfile := by unfold gapProfile; fun_prop
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

lemma gapProfile_nonneg (r : ℝ) : 0 ≤ gapProfile r :=
  le_min (by norm_num) (le_max_right _ _)
lemma gapProfile_le_one (r : ℝ) : gapProfile r ≤ 1 := min_le_left _ _
lemma baseProfile_nonneg (r : ℝ) : 0 ≤ baseProfile r := le_max_right _ _
lemma baseProfile_le_one (r : ℝ) : baseProfile r ≤ 1 := by
  apply max_le _ (by norm_num)
  have hp : 0 ≤ posPow 3 (r-1) := pow_nonneg (le_max_right _ _) _
  linarith
lemma gapProfile_inner {r : ℝ} (hr : r ≤ 1) : gapProfile r = 1 := by
  unfold gapProfile
  rw [min_eq_left]
  exact le_trans (by linarith) (le_max_left _ _)
lemma baseProfile_inner {r : ℝ} (hr : r ≤ 1) : baseProfile r = 1 := by
  simp [baseProfile,posPow,max_eq_right (by linarith : r-1 ≤ 0)]
lemma gapProfile_outer {r : ℝ} (hr : 2 ≤ r) : gapProfile r = 0 := by
  simp [gapProfile,max_eq_right (by linarith : 2-r ≤ 0)]
lemma baseProfile_outer {r : ℝ} (hr : 2 ≤ r) : baseProfile r = 0 := by
  have hp : 1 ≤ (max (r-1) 0)^3 := one_le_pow₀ (by linarith [le_max_left (r-1) 0])
  exact max_eq_right (by dsimp [posPow]; linarith)
lemma gapProfile_middle {r : ℝ} (hr : 1 ≤ r) (hr' : r ≤ 2) : gapProfile r = 2-r := by
  unfold gapProfile
  rw [max_eq_left (by linarith),min_eq_right (by linarith)]
lemma baseProfile_middle {r : ℝ} (hr : 1 ≤ r) (hr' : r ≤ 2) :
    baseProfile r = (2-r)*(1+(r-1)+(r-1)^2) := by
  have hp : (r-1)^3 ≤ 1 := pow_le_one₀ (by linarith) (by linarith)
  unfold baseProfile posPow
  rw [max_eq_left (by linarith : 0 ≤ r-1),max_eq_left (by linarith)]
  ring
lemma base_gap_bounds (r : ℝ) : gapProfile r ≤ baseProfile r ∧ baseProfile r ≤ 3*gapProfile r := by
  by_cases h1 : r ≤ 1
  · rw [gapProfile_inner h1,baseProfile_inner h1]; norm_num
  by_cases h2 : 2 ≤ r
  · rw [gapProfile_outer h2,baseProfile_outer h2]; norm_num
  have hr : 1 ≤ r := (not_le.mp h1).le
  have hr' : r ≤ 2 := (not_le.mp h2).le
  rw [gapProfile_middle hr hr',baseProfile_middle hr hr']
  have hs : (r-1)^2 ≤ 1 := pow_le_one₀ (by linarith) (by linarith)
  constructor
  · nlinarith [mul_nonneg (by linarith : 0 ≤ 2-r) (by positivity : 0 ≤ (r-1)^2)]
  · nlinarith [mul_nonneg (by linarith : 0 ≤ 2-r) (by linarith : 0 ≤ 2-((r-1)+(r-1)^2))]
lemma etaProfile_eq_power (n : ℕ) (r : ℝ) : etaProfile n r = (baseProfile r)^(N n) := rfl
lemma etaProfile_bounds (n : ℕ) (r : ℝ) :
    (gapProfile r)^(N n) ≤ etaProfile n r ∧ etaProfile n r ≤ 3^(N n)*(gapProfile r)^(N n) := by
  rw [etaProfile_eq_power,← mul_pow]
  exact ⟨pow_le_pow_left₀ (gapProfile_nonneg r) (base_gap_bounds r).1 _,
    pow_le_pow_left₀ (baseProfile_nonneg r) (base_gap_bounds r).2 _⟩
lemma derivativeProfile_inner (n : ℕ) {r : ℝ} (hr : r ≤ 1) : derivativeProfile n r = 0 := by
  simp [derivativeProfile,max_eq_right (by linarith : r-1 ≤ 0)]
lemma derivativeProfile_outer (n : ℕ) {r : ℝ} (hr : 2 ≤ r) : derivativeProfile n r = 0 := by
  simp [derivativeProfile,baseProfile_outer hr,show N n-1 ≠ 0 by have := N_ge_two n; omega]
lemma derivativeProfile_nonpos (n : ℕ) (r : ℝ) : derivativeProfile n r ≤ 0 := by
  have hb := baseProfile_nonneg r
  unfold derivativeProfile
  exact neg_nonpos.mpr (by positivity)
lemma wProfile_nonneg (n : ℕ) {r : ℝ} (hr : 0 ≤ r) : 0 ≤ wProfile n r :=
  mul_nonneg_of_nonpos_of_nonpos (neg_nonpos.mpr hr) (derivativeProfile_nonpos n r)
lemma derivativeProfile_bound (n : ℕ) (r : ℝ) :
    |derivativeProfile n r| ≤ 3*(N n:ℝ)*3^(N n-1)*(gapProfile r)^(N n-1) := by
  have hb := baseProfile_nonneg r
  have hg := gapProfile_nonneg r
  by_cases h1 : r ≤ 1
  · rw [derivativeProfile_inner n h1,abs_zero]; positivity
  by_cases h2 : 2 ≤ r
  · rw [derivativeProfile_outer n h2,abs_zero]; positivity
  have hs : (max (r-1) 0)^2 ≤ 1 := by
    rw [max_eq_left (by linarith : 0 ≤ r-1)]
    exact pow_le_one₀ (by linarith) (by linarith)
  rw [abs_of_nonpos (derivativeProfile_nonpos n r),derivativeProfile,neg_neg]
  calc
    _ ≤ 3*(N n:ℝ)*1*(3*gapProfile r)^(N n-1) := by
      gcongr
      exact (base_gap_bounds r).2
    _ = _ := by rw [mul_pow]; ring
lemma wProfile_bound (n : ℕ) {r : ℝ} (_hr : 0 ≤ r) :
    wProfile n r ≤ 6*(N n:ℝ)*3^(N n-1)*(gapProfile r)^(N n-1) := by
  have hg := gapProfile_nonneg r
  by_cases h2 : 2 ≤ r
  · simp only [wProfile,derivativeProfile_outer n h2,mul_zero]; positivity
  calc
    _ = r*|derivativeProfile n r| := by rw [abs_of_nonpos (derivativeProfile_nonpos n r),wProfile]; ring
    _ ≤ 2*(3*(N n:ℝ)*3^(N n-1)*(gapProfile r)^(N n-1)) := by
      gcongr
      · exact le_of_lt (not_le.mp h2)
      · exact derivativeProfile_bound n r
    _ = _ := by ring

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

lemma secondProfile_inner (n : ℕ) {r : ℝ} (hr : r ≤ 1) : secondProfile n r = 0 := by
  simp [secondProfile,max_eq_right (by linarith : r-1 ≤ 0)]
lemma secondProfile_outer {n : ℕ} (hn : 1 ≤ n) {r : ℝ} (hr : 2 ≤ r) :
    secondProfile n r = 0 := by
  have := N_ge_three hn
  simp [secondProfile,baseProfile_outer hr,show N n-1 ≠ 0 by omega,
    show N n-2 ≠ 0 by omega]

lemma secondProfile_bound {n : ℕ} (hn : 1 ≤ n) (r : ℝ) :
    |secondProfile n r| ≤ (6*(N n:ℝ)+9*(N n:ℝ)*(N n-1))*
      3^(N n-2)*(gapProfile r)^(N n-2) := by
  have hN := N_ge_three hn
  have hn0 : (0:ℝ) ≤ N n-1 := by
    have : (3:ℝ) ≤ N n := by exact_mod_cast hN
    linarith
  have hb := baseProfile_nonneg r
  have hg := gapProfile_nonneg r
  by_cases h1 : r ≤ 1
  · rw [secondProfile_inner n h1,abs_zero]; positivity
  by_cases h2 : 2 ≤ r
  · rw [secondProfile_outer hn h2,abs_zero]; positivity
  have hs0 : 0 ≤ max (r-1) 0 := le_max_right _ _
  have hs1 : max (r-1) 0 ≤ 1 := by apply max_le <;> linarith
  have hs4 : (max (r-1) 0)^4 ≤ 1 := pow_le_one₀ hs0 hs1
  have hp := pow_le_pow_of_le_one hb (baseProfile_le_one r) (by omega : N n-2 ≤ N n-1)
  have hp' := pow_le_pow_left₀ hb (base_gap_bounds r).2 (N n-2)
  calc
    _ ≤ 6*(N n:ℝ)*max (r-1) 0*(baseProfile r)^(N n-1) +
        9*(N n:ℝ)*(N n-1)*(max (r-1) 0)^4*(baseProfile r)^(N n-2) := by
      unfold secondProfile
      calc
        _ ≤ |-6*(N n:ℝ)*max (r-1) 0*(baseProfile r)^(N n-1)| +
            |9*(N n:ℝ)*(N n-1)*(max (r-1) 0)^4*(baseProfile r)^(N n-2)| := abs_add_le _ _
        _ = _ := by
          rw [abs_of_nonpos (by
            have hp : 0 ≤ 6*(N n:ℝ)*max (r-1) 0*(baseProfile r)^(N n-1) := by positivity
            nlinarith),abs_of_nonneg (by positivity)]
          ring
    _ ≤ 6*(N n:ℝ)*1*((3*gapProfile r)^(N n-2)) +
        9*(N n:ℝ)*(N n-1)*1*((3*gapProfile r)^(N n-2)) := by
      gcongr
      exact hp.trans hp'
    _ = _ := by rw [mul_pow]; ring

lemma lipschitz_gapProfile : LipschitzWith 1 gapProfile := by
  have hh : LipschitzWith 1 (fun r : ℝ => 2-r) := by
    apply LipschitzWith.of_dist_le_mul
    intro r s
    simp only [NNReal.coe_one,one_mul,Real.dist_eq]
    rw [show (2-r)-(2-s) = -(r-s) by ring,abs_neg]
  exact (hh.max_const 0).const_min 1

lemma gapProfile_oscillation (r s : ℝ) : |gapProfile r-gapProfile s| ≤ |r-s| := by
  simpa only [Real.dist_eq,NNReal.coe_one,one_mul] using lipschitz_gapProfile.dist_le_mul r s

lemma constants_nonneg (n : ℕ) : 0 ≤ derivativeConstant n ∧ 0 ≤ secondConstant n ∧ 0 ≤ wDerivativeConstant n := by
  have hn : (0:ℝ) ≤ N n-1 := by
    have : (2:ℝ) ≤ N n := by exact_mod_cast N_ge_two n
    linarith
  dsimp [derivativeConstant,secondConstant,wDerivativeConstant]
  constructor
  · positivity
  constructor <;> positivity

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

omit [InnerProductSpace ℝ E] in
lemma continuous_d : Continuous (d : E → ℝ) := continuous_gapProfile.comp continuous_norm
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
-- module Solutions.OAIQW_HenonLaneEmden.CutoffOscillation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE

section CutoffOscillation

open Set Metric
noncomputable section
namespace HenonLaneEmden.Cutoff

variable {E : Type uE} [NormedAddCommGroup E]

lemma d_nonneg (x : E) : 0 ≤ d x := gapProfile_nonneg _
lemma d_le_one (x : E) : d x ≤ 1 := gapProfile_le_one _
lemma d_pos_iff (x : E) : 0 < d x ↔ ‖x‖ < 2 := by
  simp only [d,gapProfile,lt_min_iff,lt_max_iff,lt_self_iff_false,or_false]
  constructor
  · intro h; linarith [h.2]
  · intro h; constructor <;> linarith

lemma d_oscillation (x y : E) : |d x-d y| ≤ dist x y := by
  exact (gapProfile_oscillation ‖x‖ ‖y‖).trans (by simpa only [dist_eq_norm] using abs_norm_sub_norm_le x y)

lemma norm_segment_gap {x y : E} {D : ℝ} (hD : d x+dist x y ≤ D)
    {t : ℝ} (ht : t ∈ uIcc ‖x‖ ‖y‖) : 0 ≤ t ∧ gapProfile t ≤ D := by
  refine ⟨le_trans (le_min (norm_nonneg _) (norm_nonneg _)) ht.1,?_⟩
  have hdist : |t-‖x‖| ≤ |‖y‖-‖x‖| := by
    exact (abs_sub_le_iff.mpr ⟨by
      have hmax : max ‖x‖ ‖y‖ ≤ ‖x‖+|‖y‖-‖x‖| := by
        apply max_le
        · linarith [abs_nonneg (‖y‖-‖x‖)]
        · linarith [le_abs_self (‖y‖-‖x‖)]
      linarith [ht.2]
    ,by
      have hmin : ‖x‖-|‖y‖-‖x‖| ≤ min ‖x‖ ‖y‖ := by
        apply le_min
        · linarith [abs_nonneg (‖y‖-‖x‖)]
        · linarith [neg_abs_le (‖y‖-‖x‖)]
      linarith [ht.1]⟩)
  have hn : |‖y‖-‖x‖| ≤ dist x y := by
    simpa only [dist_comm x y,dist_eq_norm] using abs_norm_sub_norm_le y x
  have hg := (abs_le.mp (gapProfile_oscillation t ‖x‖)).2
  change gapProfile t ≤ D
  change gapProfile ‖x‖+dist x y ≤ D at hD
  linarith

end HenonLaneEmden.Cutoff
end
end CutoffOscillation

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
lemma w_inner (n : ℕ) {x : E} (hx : ‖x‖ ≤ 1) : w n x = 0 := by
  rw [w_eq_profile,wProfile,derivativeProfile_inner n hx,mul_zero]
omit [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E] in
lemma w_outer (n : ℕ) {x : E} (hx : 2 ≤ ‖x‖) : w n x = 0 := by
  rw [w_eq_profile,wProfile,derivativeProfile_outer n hx,mul_zero]

end HenonLaneEmden.AdaptiveCap
end
end AdaptiveCaps

end OAI
end

section
-- module Solutions.OAIQW_HenonLaneEmden.Tails
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE

section Tails

open MeasureTheory Set Filter
open scoped ENNReal
namespace HenonLaneEmden.UniformTail

lemma dyadic_power_identity {R : ℝ} (hR : 0 < R) (a s C : ℝ) (k : ℕ) :
    (R*2^k)^(-a) * (C*(R*2^(k+1))^s) =
      (C*2^s*R^(s-a)) * (2^(s-a))^k := by
  rw [show (2:ℝ)^(k+1) = 2*2^k by rw [pow_succ]; ring,
    show R*(2*2^k) = (2*R)*2^k by ring,
    Real.mul_rpow hR.le (by positivity),Real.mul_rpow (by positivity) (by positivity),
    Real.mul_rpow (by norm_num) hR.le,
    ← Real.rpow_pow_comm (by norm_num : (0:ℝ) ≤ 2) (-a) k,
    ← Real.rpow_pow_comm (by norm_num : (0:ℝ) ≤ 2) s k]
  rw [show R^(s-a) = R^(-a)*R^s by rw [← Real.rpow_add hR]; congr 1; ring,
    show (2:ℝ)^(s-a) = 2^(-a)*2^s by rw [← Real.rpow_add (by norm_num : (0:ℝ)<2)]; congr 1; ring,
    mul_pow]
  ring

variable {E : Type uE} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]

/-- A nonnegative measure having polynomial centered ball growth has a uniform
inverse-power tail whenever the decay exponent exceeds the growth exponent.
The proof uses a geometric majorant, not subtraction of divergent potentials. -/
lemma lintegral_norm_rpow_compl_ball_le (μ : Measure E) {C R a s : ℝ}
    (hC : 0 ≤ C) (hR : 0 < R) (ha : 0 ≤ a) (hs : s < a)
    (hball : ∀ r > 0, μ (Metric.ball (0:E) r) ≤ ENNReal.ofReal (C*r^s)) :
    (∫⁻ y in (Metric.ball (0:E) R)ᶜ, ENNReal.ofReal (‖y‖^(-a)) ∂μ) ≤
      ENNReal.ofReal (C*2^s*R^(s-a)/(1-2^(s-a))) := by
  let F : ℕ → E → ℝ≥0∞ := fun k => (Metric.ball (0:E) (R*2^(k+1))).indicator
    (fun _ => ENNReal.ofReal ((R*2^k)^(-a)))
  have hF : ∀ k, Measurable (F k) := fun k => measurable_const.indicator measurableSet_ball
  have hpoint : ∀ y : E, (Metric.ball (0:E) R)ᶜ.indicator
      (fun y => ENNReal.ofReal (‖y‖^(-a))) y ≤ ∑' k, F k y := by
    intro y
    by_cases hy : y ∈ (Metric.ball (0:E) R)ᶜ
    · have hny : R ≤ ‖y‖ := by simpa only [mem_compl_iff,Metric.mem_ball,dist_zero_right,not_lt] using hy
      obtain ⟨k,hk₁,hk₂⟩ := exists_nat_pow_near ((le_div_iff₀ hR).mpr (by simpa using hny))
        (by norm_num : (1:ℝ)<2)
      have hklo : R*2^k ≤ ‖y‖ := by nlinarith [(le_div_iff₀ hR).mp hk₁]
      have hkhi : ‖y‖ < R*2^(k+1) := by nlinarith [(div_lt_iff₀ hR).mp hk₂]
      have hym : y ∈ Metric.ball (0:E) (R*2^(k+1)) := by simpa [Metric.mem_ball,dist_zero_right] using hkhi
      rw [indicator_of_mem hy]
      apply le_trans _ (ENNReal.le_tsum k)
      dsimp only [F]
      rw [indicator_of_mem hym]
      exact ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow_of_nonpos (by positivity) hklo (neg_nonpos.mpr ha))
    · simp only [indicator_of_notMem hy,zero_le]
  have hgeom : 0 ≤ (2:ℝ)^(s-a) := Real.rpow_nonneg (by norm_num) _
  have hgeomlt : (2:ℝ)^(s-a) < 1 := by
    exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (sub_neg.mpr hs)
  have hsumm : Summable (fun k : ℕ => (C*2^s*R^(s-a))*((2:ℝ)^(s-a))^k) :=
    (summable_geometric_of_abs_lt_one (by rwa [abs_of_nonneg hgeom])).mul_left _
  calc
    _ = ∫⁻ y, (Metric.ball (0:E) R)ᶜ.indicator (fun y => ENNReal.ofReal (‖y‖^(-a))) y ∂μ :=
      (lintegral_indicator measurableSet_ball.compl _).symm
    _ ≤ ∫⁻ y, ∑' k, F k y ∂μ := lintegral_mono hpoint
    _ = ∑' k, ∫⁻ y, F k y ∂μ := lintegral_tsum (fun k => (hF k).aemeasurable)
    _ ≤ ∑' k : ℕ, ENNReal.ofReal ((R*2^k)^(-a)) * ENNReal.ofReal (C*(R*2^(k+1))^s) := by
      apply ENNReal.tsum_le_tsum; intro k
      dsimp only [F]
      rw [lintegral_indicator measurableSet_ball,setLIntegral_const]
      gcongr
      exact hball _ (by positivity)
    _ = ∑' k : ℕ, ENNReal.ofReal ((C*2^s*R^(s-a))*((2:ℝ)^(s-a))^k) := by
      apply tsum_congr; intro k
      rw [← ENNReal.ofReal_mul (by positivity),dyadic_power_identity hR]
    _ = ENNReal.ofReal (∑' k : ℕ, (C*2^s*R^(s-a))*((2:ℝ)^(s-a))^k) :=
      (ENNReal.ofReal_tsum_of_nonneg (fun k => by positivity) hsumm).symm
    _ = _ := by
      rw [tsum_mul_left,tsum_geometric_of_abs_lt_one (by rwa [abs_of_nonneg hgeom]),div_eq_mul_inv]

end HenonLaneEmden.UniformTail
end Tails

end OAI
end

section
-- module Solutions.OAIQW_HenonLaneEmden.UniformBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE

section UniformBounds

open MeasureTheory Set Filter
open scoped ENNReal
namespace HenonLaneEmden.UniformTail

variable {E : Type uE} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]

omit [MeasurableSpace E] [BorelSpace E] in
lemma shifted_rpow_le {a : ℝ} (ha : 0 ≤ a) {x y : E} {R : ℝ}
    (hx : ‖x‖ ≤ R) (hy : 2*R ≤ ‖y‖) (hy0 : 0 < ‖y‖) :
    ‖x-y‖^(-a) ≤ 2^a*‖y‖^(-a) := by
  have hlo : ‖y‖/2 ≤ ‖x-y‖ := by
    have ht := norm_sub_norm_le y x
    rw [norm_sub_rev y x] at ht
    linarith
  have hh := Real.rpow_le_rpow_of_nonpos (by positivity : 0 < ‖y‖/2) hlo (neg_nonpos.mpr ha)
  calc
    _ ≤ (‖y‖/2)^(-a) := hh
    _ = 2^a*‖y‖^(-a) := by
      rw [Real.div_rpow (norm_nonneg _) (by norm_num),Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2)]
      rw [div_inv_eq_mul,mul_comm]

lemma uniform_shifted_tail (μ : Measure E) {C a s : ℝ} (hC : 0 ≤ C)
    (ha : 0 ≤ a) (hs : s < a)
    (hball : ∀ r > 0, μ (Metric.ball (0:E) r) ≤ ENNReal.ofReal (C*r^s)) :
    ∀ x : E, ‖x‖ ≤ 4 →
      (∫⁻ y in (Metric.ball (0:E) 8)ᶜ, ENNReal.ofReal (‖x-y‖^(-a)) ∂μ) ≤
        ENNReal.ofReal (2^a*(C*2^s*8^(s-a)/(1-2^(s-a)))) := by
  let T := C*2^s*8^(s-a)/(1-2^(s-a))
  intro x hx
  calc
    _ ≤ ∫⁻ y in (Metric.ball (0:E) 8)ᶜ, ENNReal.ofReal (2^a) * ENNReal.ofReal (‖y‖^(-a)) ∂μ := by
      apply setLIntegral_mono' measurableSet_ball.compl
      intro y hy
      have hy' : 8 ≤ ‖y‖ := by simpa only [mem_compl_iff,Metric.mem_ball,dist_zero_right,not_lt] using hy
      rw [← ENNReal.ofReal_mul (by positivity)]
      exact ENNReal.ofReal_le_ofReal (shifted_rpow_le ha hx (by linarith) (by linarith))
    _ = ENNReal.ofReal (2^a) * ∫⁻ y in (Metric.ball (0:E) 8)ᶜ, ENNReal.ofReal (‖y‖^(-a)) ∂μ := by
      rw [lintegral_const_mul'' _ (by fun_prop)]
    _ ≤ ENNReal.ofReal (2^a) * ENNReal.ofReal T := by
      gcongr
      exact lintegral_norm_rpow_compl_ball_le μ hC (by norm_num) ha hs hball
    _ = ENNReal.ofReal (2^a*T) := (ENNReal.ofReal_mul (by positivity)).symm


lemma tailNumber_nonneg {C a s : ℝ} (hC : 0 ≤ C) (hs : s < a) :
    0 ≤ tailNumber C a s := by
  unfold tailNumber
  apply mul_nonneg (by positivity)
  apply div_nonneg (by positivity)
  exact sub_nonneg.mpr (Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (sub_nonpos.mpr hs.le))

lemma truncated_potential_bound (μ : Measure E) {C a s : ℝ} (hC : 0 ≤ C)
    (ha : 0 ≤ a) (hs : s < a)
    (hball : ∀ r > 0, μ (Metric.ball (0:E) r) ≤ ENNReal.ofReal (C*r^s))
    {x : E} (hx : ‖x‖ ≤ 4) {l : ℝ} (hl : 0 < l) (hl1 : l ≤ 1) :
    (∫⁻ y in {y | l ≤ ‖x-y‖}, ENNReal.ofReal (‖x-y‖^(-a)) ∂μ) ≤
      ENNReal.ofReal ((C*8^s+tailNumber C a s)*l^(-a)) := by
  let S : Set E := {y | l ≤ ‖x-y‖}
  have hS : MeasurableSet S := measurableSet_le measurable_const (by fun_prop)
  have hpoint (y : E) :
      S.indicator (fun y => ENNReal.ofReal (‖x-y‖^(-a))) y ≤
        (Metric.ball (0:E) 8).indicator (fun _ => ENNReal.ofReal (l^(-a))) y +
        (Metric.ball (0:E) 8)ᶜ.indicator (fun y => ENNReal.ofReal (‖x-y‖^(-a))) y := by
    by_cases hy : y ∈ S
    · rw [indicator_of_mem hy]
      by_cases hy8 : y ∈ Metric.ball (0:E) 8
      · rw [indicator_of_mem hy8,indicator_of_notMem (not_not.mpr hy8),add_zero]
        exact ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow_of_nonpos hl hy (neg_nonpos.mpr ha))
      · rw [indicator_of_notMem hy8,indicator_of_mem hy8,zero_add]
    · rw [indicator_of_notMem hy]; exact zero_le
  have ht := uniform_shifted_tail μ hC ha hs hball x hx
  have hpow : 1 ≤ l^(-a) := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hl hl1 (neg_nonpos.mpr ha)
  calc
    _ = ∫⁻ y, S.indicator (fun y => ENNReal.ofReal (‖x-y‖^(-a))) y ∂μ :=
      (lintegral_indicator hS _).symm
    _ ≤ ∫⁻ y, (Metric.ball (0:E) 8).indicator (fun _ => ENNReal.ofReal (l^(-a))) y +
        (Metric.ball (0:E) 8)ᶜ.indicator (fun y => ENNReal.ofReal (‖x-y‖^(-a))) y ∂μ := lintegral_mono hpoint
    _ = ENNReal.ofReal (l^(-a))*μ (Metric.ball (0:E) 8) +
        ∫⁻ y in (Metric.ball (0:E) 8)ᶜ, ENNReal.ofReal (‖x-y‖^(-a)) ∂μ := by
      rw [lintegral_add_left (measurable_const.indicator measurableSet_ball),
        lintegral_indicator measurableSet_ball,lintegral_indicator measurableSet_ball.compl,setLIntegral_const]
    _ ≤ ENNReal.ofReal (l^(-a))*ENNReal.ofReal (C*8^s)+ENNReal.ofReal (tailNumber C a s) := by
      apply add_le_add _ ht
      gcongr
      exact hball 8 (by norm_num)
    _ = ENNReal.ofReal (l^(-a)*(C*8^s)+tailNumber C a s) := by
      rw [← ENNReal.ofReal_mul (by positivity),← ENNReal.ofReal_add (by positivity) (tailNumber_nonneg hC hs)]
    _ ≤ _ := ENNReal.ofReal_le_ofReal (by nlinarith [mul_le_mul_of_nonneg_left hpow (tailNumber_nonneg hC hs)])

end HenonLaneEmden.UniformTail

namespace HenonLaneEmden
open UniformTail

lemma IsSolution.sourceMeasure_ball {n : ℕ} (hn : 2 ≤ n) {p q A B : ℝ}
    {u v : Space n → ℝ} (h : IsSolution n p q A B u v) (R : ℝ) :
    sourceMeasure v p A (Metric.ball (0:Space n) R) = ENNReal.ofReal (sourceMass v p A R) := by
  rw [sourceMeasure,withDensity_apply _ measurableSet_ball]
  exact (ofReal_integral_eq_lintegral_ofReal
    (((h.source_g_locallyIntegrable hn).integrableOn_isCompact (isCompact_closedBall _ R)).mono_set
      Metric.ball_subset_closedBall)
    (Eventually.of_forall (source_nonneg (fun y => (h.positive_v y).le) p A))).symm

lemma lintegral_sourceMeasure {n : ℕ} {u : Space n → ℝ} (hu : Continuous u) (q B : ℝ)
    {F : Space n → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ y, F y ∂sourceMeasure u q B) = ∫⁻ y, ENNReal.ofReal (source u q B y)*F y :=
  lintegral_withDensity_eq_lintegral_mul volume (measurable_source hu q B).ennreal_ofReal hF

lemma IsSolution.uniform_g_truncated {n : ℕ} (hn : 2 ≤ n) {p q A B : ℝ}
    {u v : Space n → ℝ} (h : IsSolution n p q A B u v) (hp : 0 < p) (hq : 0 < q)
    {x : Space n} (hx : ‖x‖ ≤ 4) {l : ℝ} (hl : 0 < l) (hl1 : l ≤ 1) :
    (∫⁻ y in {y | l ≤ ‖x-y‖}, ENNReal.ofReal (‖x-y‖^(2-(n:ℝ))) ∂sourceMeasure v p A) ≤
      ENNReal.ofReal ((sourceConstant n p q A B*8^((n:ℝ)-2-alpha p q A B)+uniformTailConstant n p q A B)*l^(2-(n:ℝ))) := by
  have hn3 := h.dimension_ge_three hn
  have hn3' : (3:ℝ) ≤ n := by exact_mod_cast hn3
  have hA := h.first_weight_gt_neg_two hn
  have hB := h.swap.first_weight_gt_neg_two hn
  have ha := alpha_pos hp hA hB (h.product_gt_one hn hp hq)
  simpa only [neg_sub,uniformTailConstant] using
    truncated_potential_bound (sourceMeasure v p A) (sourceConstant_pos hn3 hA hB).le
      (show 0 ≤ (n:ℝ)-2 by linarith)
      (show (n:ℝ)-2-alpha p q A B < (n:ℝ)-2 by linarith)
      (fun R hR => by rw [h.sourceMeasure_ball hn]; exact ENNReal.ofReal_le_ofReal (h.sourceMass_g_upper hn hp hq hR)) hx hl hl1

end HenonLaneEmden
end UniformBounds

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

lemma newtonKernel_symm (n : ℕ) (x y : Space n) :
    newtonKernel n (x,y)=newtonKernel n (y,x) := by
  simp only [newtonKernel,norm_sub_rev x y]
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

lemma lintegral_interaction_right {n : ℕ} {f g : Space n → ℝ}
    (hf : Measurable f) (hg : Measurable g) {F : Space n → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ z, F z.2 ∂interaction f g) = ∫⁻ y, ENNReal.ofReal (g y)*F y*
      potential volume (fun z => ENNReal.ofReal (newtonKernel n z)) f y := by
  rw [lintegral_interaction hf hg (by fun_prop),← lintegral_prod_swap]
  change (∫⁻ z : Space n × Space n, ENNReal.ofReal (f z.2)*ENNReal.ofReal (g z.1)*
    ENNReal.ofReal (newtonKernel n (z.2,z.1))*F z.1 ∂volume.prod volume) = _
  simp_rw [newtonKernel_symm n _ _]
  have he (z : Space n × Space n) :
      ENNReal.ofReal (f z.2)*ENNReal.ofReal (g z.1)*ENNReal.ofReal (newtonKernel n (z.1,z.2))*F z.1 =
      ENNReal.ofReal (g z.1)*ENNReal.ofReal (f z.2)*ENNReal.ofReal (newtonKernel n z)*F z.1 := by ring
  simp_rw [he]
  rw [← lintegral_interaction hg hf (by fun_prop)]
  exact lintegral_interaction_left hg hf hF

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

lemma IsSolution.interaction_right {n : ℕ} (hn : 2 ≤ n) {p q A B : ℝ}
    {u v : Space n → ℝ} (h : IsSolution n p q A B u v) (hp : 0 < p)
    {F : Space n → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ z, F z.2 ∂interaction (source u q B) (source v p A)) =
      ∫⁻ y, ENNReal.ofReal (source v p A y*v y)*F y := by
  rw [lintegral_interaction_right (measurable_source h.continuous_u q B) (measurable_source h.continuous_v p A) hF]
  apply lintegral_congr_ae
  filter_upwards [h.swap.newton_potential_u_ae hn hp] with y hy
  rw [hy,ENNReal.ofReal_mul (source_nonneg (fun x => (h.positive_v x).le) p A y)]
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
-- module Solutions.OAIQW_HenonLaneEmden.CutoffTaylor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE

section CutoffTaylor

open Set Metric
noncomputable section
namespace HenonLaneEmden.Cutoff

lemma derivativeProfile_oscillation {n : ℕ} (hn : 1 ≤ n) {r s D : ℝ}
    (hseg : ∀ t ∈ uIcc r s, gapProfile t ≤ D) :
    |derivativeProfile n s-derivativeProfile n r| ≤ secondConstant n*D^(N n-2)*|s-r| := by
  have hh := (convex_uIcc r s).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun t _ => (hasDerivAt_derivativeProfile hn t).hasDerivWithinAt)
    (show ∀ t ∈ uIcc r s, ‖secondProfile n t‖ ≤ secondConstant n*D^(N n-2) from by
      intro t ht
      rw [Real.norm_eq_abs]
      exact (secondProfile_bound hn t).trans
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (gapProfile_nonneg t) (hseg t ht) _) (constants_nonneg n).2.1))
    left_mem_uIcc right_mem_uIcc
  simpa only [Real.norm_eq_abs] using hh

lemma etaProfile_oscillation (n : ℕ) {r s D : ℝ}
    (hseg : ∀ t ∈ uIcc r s, gapProfile t ≤ D) :
    |etaProfile n s-etaProfile n r| ≤ derivativeConstant n*D^(N n-1)*|s-r| := by
  have hh := (convex_uIcc r s).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun t _ => (hasDerivAt_etaProfile n t).hasDerivWithinAt)
    (show ∀ t ∈ uIcc r s, ‖derivativeProfile n t‖ ≤ derivativeConstant n*D^(N n-1) from by
      intro t ht
      rw [Real.norm_eq_abs]
      exact (derivativeProfile_bound n t).trans
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (gapProfile_nonneg t) (hseg t ht) _) (constants_nonneg n).1))
    left_mem_uIcc right_mem_uIcc
  simpa only [Real.norm_eq_abs] using hh

lemma abs_sub_left_le_of_mem_uIcc {r s t : ℝ} (ht : t ∈ uIcc r s) : |t-r| ≤ |s-r| := by
  rcases le_total r s with h | h
  · rw [uIcc_of_le h] at ht
    rw [abs_of_nonneg (sub_nonneg.mpr ht.1),abs_of_nonneg (sub_nonneg.mpr h)]
    linarith [ht.2]
  · rw [uIcc_of_ge h] at ht
    rw [abs_of_nonpos (sub_nonpos.mpr ht.2),abs_of_nonpos (sub_nonpos.mpr h)]
    linarith [ht.1]

lemma etaProfile_taylor {n : ℕ} (hn : 1 ≤ n) {r s D : ℝ} (hD : 0 ≤ D)
    (hseg : ∀ t ∈ uIcc r s, gapProfile t ≤ D) :
    |etaProfile n s-etaProfile n r-derivativeProfile n r*(s-r)| ≤
      secondConstant n*D^(N n-2)*(s-r)^2 := by
  let F (t : ℝ) := etaProfile n t-derivativeProfile n r*t
  have hF (t) : HasDerivAt F (derivativeProfile n t-derivativeProfile n r) t := by
    convert (hasDerivAt_etaProfile n t).sub ((hasDerivAt_id t).const_mul (derivativeProfile n r)) using 1 <;> first | rfl | simp only [mul_one]
  have hh := (convex_uIcc r s).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun t _ => (hF t).hasDerivWithinAt)
    (show ∀ t ∈ uIcc r s, ‖derivativeProfile n t-derivativeProfile n r‖ ≤ secondConstant n*D^(N n-2)*|s-r| from by
      intro t ht
      rw [Real.norm_eq_abs]
      exact (derivativeProfile_oscillation hn (fun z hz => hseg z (uIcc_subset_uIcc_left ht hz))).trans
        (mul_le_mul_of_nonneg_left (abs_sub_left_le_of_mem_uIcc ht)
          (mul_nonneg (constants_nonneg n).2.1 (pow_nonneg hD _))))
    left_mem_uIcc right_mem_uIcc
  simpa only [F,Real.norm_eq_abs,show etaProfile n s-derivativeProfile n r*s-(etaProfile n r-derivativeProfile n r*r) =
    etaProfile n s-etaProfile n r-derivativeProfile n r*(s-r) by ring,mul_assoc,← sq, sq_abs] using hh

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
omit [InnerProductSpace ℝ E] in
lemma eta_oscillation (n : ℕ) {x y : E} {D : ℝ} (hD : 0 ≤ D)
    (hxy : d x+dist x y ≤ D) :
    |eta n y-eta n x| ≤ derivativeConstant n*D^(N n-1)*dist x y := by
  have hh := etaProfile_oscillation n (fun t ht => (norm_segment_gap hxy ht).2)
  exact hh.trans (mul_le_mul_of_nonneg_left
    (by simpa only [dist_comm x y,dist_eq_norm] using abs_norm_sub_norm_le y x)
    (mul_nonneg (constants_nonneg n).1 (pow_nonneg hD _)))

end HenonLaneEmden.Cutoff
end
end CutoffTaylor

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
-- module Solutions.OAIQW_HenonLaneEmden.RadialTaylor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE

section RadialTaylor

open MeasureTheory Set Metric NormedSpace
open scoped ENNReal InnerProductSpace
noncomputable section
namespace HenonLaneEmden
open Cutoff

lemma norm_radial_error {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {x : E} (hx : (1:ℝ)/2 ≤ ‖x‖) (y : E) :
    |(‖x‖-‖y‖)-inner ℝ x (x-y)/‖x‖| ≤ ‖x-y‖^2 := by
  have hr : 0 < ‖x‖ := by linarith
  have hid := norm_sub_sq_real x y
  have hI : inner ℝ x (x-y) = ‖x‖^2-inner ℝ x y := by
    rw [inner_sub_right,real_inner_self_eq_norm_sq]
  have hs : (‖x‖-‖y‖)^2 ≤ ‖x-y‖^2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg (‖x‖-‖y‖)) (norm_nonneg (x-y))).mpr (abs_norm_sub_norm_le x y)
  have he : (‖x‖-‖y‖)-inner ℝ x (x-y)/‖x‖ = (‖x‖*(‖x‖-‖y‖)-inner ℝ x (x-y))/‖x‖ := by
    field_simp
  rw [he,abs_div,abs_of_pos hr,div_le_iff₀ hr,hI]
  apply abs_le.mpr
  constructor <;> nlinarith [sq_nonneg (‖x‖-‖y‖),mul_le_mul_of_nonneg_right hx (sq_nonneg ‖x-y‖)]

lemma eta_radial_taylor {n : ℕ} (hn : 1 ≤ n) {x : Space n} (hx : (1:ℝ)/2 ≤ ‖x‖)
    (y : Space n) {D : ℝ} (hD : 0 ≤ D) (hseg : ∀ t ∈ uIcc ‖x‖ ‖y‖, gapProfile t ≤ D) :
    |eta n x-eta n y-derivativeProfile n ‖x‖*inner ℝ x (x-y)/‖x‖| ≤
      (secondConstant n*D^(N n-2)+derivativeConstant n*D^(N n-1))*‖x-y‖^2 := by
  have hs := etaProfile_taylor hn hD hseg
  have hnrm := norm_radial_error hx y
  have hp := (derivativeProfile_bound n ‖x‖).trans
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (gapProfile_nonneg _) (hseg _ left_mem_uIcc) _) (constants_nonneg n).1)
  have hsq : (‖y‖-‖x‖)^2 ≤ ‖x-y‖^2 := by
    simpa only [sq_abs,norm_sub_rev y x] using
      (sq_le_sq₀ (abs_nonneg (‖y‖-‖x‖)) (norm_nonneg (y-x))).mpr (abs_norm_sub_norm_le y x)
  have hs' : |eta n x-eta n y-derivativeProfile n ‖x‖*(‖x‖-‖y‖)| ≤ secondConstant n*D^(N n-2)*‖x-y‖^2 := by
    have hh := hs.trans (mul_le_mul_of_nonneg_left hsq (mul_nonneg (constants_nonneg n).2.1 (pow_nonneg hD _)))
    rw [show eta n x-eta n y-derivativeProfile n ‖x‖*(‖x‖-‖y‖) =
      -(etaProfile n ‖y‖-etaProfile n ‖x‖-derivativeProfile n ‖x‖*(‖y‖-‖x‖)) by unfold eta; ring,abs_neg]
    exact hh
  have he : eta n x-eta n y-derivativeProfile n ‖x‖*inner ℝ x (x-y)/‖x‖ =
      (eta n x-eta n y-derivativeProfile n ‖x‖*(‖x‖-‖y‖))+
      derivativeProfile n ‖x‖*((‖x‖-‖y‖)-inner ℝ x (x-y)/‖x‖) := by ring
  rw [he]
  exact (abs_add_le _ _).trans ((add_le_add hs'
    ((by rw [abs_mul]; exact mul_le_mul hp hnrm (abs_nonneg _) (mul_nonneg (constants_nonneg n).1 (pow_nonneg hD _)) :
      |derivativeProfile n ‖x‖*((‖x‖-‖y‖)-inner ℝ x (x-y)/‖x‖)| ≤
        derivativeConstant n*D^(N n-1)*‖x-y‖^2))).trans_eq (by ring))

lemma flux_linearization_identity {n : ℕ} {x y : Space n} (hx : x ≠ 0) (hxy : x ≠ y) :
    fluxFactor n (x,y)-eta n x+w n x*radialFactor (x,y) =
      (eta n x-eta n y-derivativeProfile n ‖x‖*inner ℝ x (x-y)/‖x‖)*
        inner ℝ (x-y) y/‖x-y‖^2-derivativeProfile n ‖x‖*inner ℝ x (x-y)/‖x‖ := by
  have hr : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  have hd : ‖x-y‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hxy)
  have hI : inner ℝ (x-y) x = inner ℝ x (x-y) := real_inner_comm _ _
  have hJ : inner ℝ (x-y) y = inner ℝ x (x-y)-‖x-y‖^2 := by
    have he : inner ℝ (x-y) (x-y) = inner ℝ (x-y) x-inner ℝ (x-y) y := inner_sub_right _ _ _
    rw [real_inner_self_eq_norm_sq,hI] at he; linarith
  simp only [fluxFactor,X,inner_sub_right,real_inner_smul_right,radialFactor,w_eq_profile,wProfile]
  rw [hI,hJ]
  simp only [inner_sub_right]
  field_simp
  ring

end HenonLaneEmden
end
end RadialTaylor

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

lemma eta_gap_bounds {E : Type uE2} [NormedAddCommGroup E] (n : ℕ) (x : E) :
    d x^(N n) ≤ eta n x ∧ eta n x ≤ 3^(N n)*d x^(N n) := etaProfile_bounds n ‖x‖

lemma pairGap_bounds {n : ℕ} (z : Space n × Space n) : 0 ≤ pairGap z ∧ pairGap z ≤ 1 :=
  ⟨(d_nonneg z.1).trans (le_max_left _ _),max_le (d_le_one z.1) (d_le_one z.2)⟩
lemma pairGap_power_le {n : ℕ} (z : Space n × Space n) :
    pairGap z^(N n) ≤ eta n z.1+eta n z.2 := by
  rcases le_total (d z.1) (d z.2) with h | h
  · rw [pairGap,max_eq_right h]
    exact (eta_gap_bounds n z.2).1.trans (le_add_of_nonneg_left (eta_nonneg n z.1))
  · rw [pairGap,max_eq_left h]
    exact (eta_gap_bounds n z.1).1.trans (le_add_of_nonneg_right (eta_nonneg n z.2))

lemma close_pair_gaps {n : ℕ} {δ : ℝ} (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1/4)
    {x y : Space n} (hs : 0 < pairGap (x,y)) (hxy : ‖x-y‖ ≤ δ*pairGap (x,y)^(m n)) :
    0 < d x ∧ 0 < d y ∧ d x+dist x y ≤ 2*pairGap (x,y) ∧ ‖x-y‖ ≤ δ*pairGap (x,y) := by
  have hb := pairGap_bounds (x,y)
  have hp : pairGap (x,y)^(m n) ≤ pairGap (x,y) := by
    simpa only [pow_one] using pow_le_pow_of_le_one hb.1 hb.2 (by simp [m] : 1 ≤ m n)
  have hL := hxy.trans (mul_le_mul_of_nonneg_left hp hδ)
  have hd := abs_le.mp (d_oscillation x y)
  rw [dist_eq_norm] at hd
  have hmax : pairGap (x,y) = d x ∨ pairGap (x,y) = d y := max_choice _ _
  have hx := le_max_left (d x) (d y)
  have hy := le_max_right (d x) (d y)
  change d x ≤ pairGap (x,y) at hx
  change d y ≤ pairGap (x,y) at hy
  have hm : δ*pairGap (x,y) ≤ pairGap (x,y)/4 := by nlinarith
  refine ⟨?_,?_,?_,hL⟩
  · rcases hmax with h | h <;> nlinarith
  · rcases hmax with h | h <;> nlinarith
  · rw [dist_eq_norm]; linarith

lemma close_power_bound {n j : ℕ} {s δ L : ℝ} (hs : 0 ≤ s) (hs1 : s ≤ 1)
    (hδ : 0 ≤ δ) (hL : L ≤ δ*s^(m n)) (hj : j ≤ N n) (hjm : N n ≤ j+m n) :
    (2*s)^j*L ≤ 2^(N n)*δ*s^(N n) := by
  rw [mul_pow]
  calc
    _ ≤ (2^j*s^j)*(δ*s^(m n)) := mul_le_mul_of_nonneg_left hL (by positivity)
    _ = 2^j*δ*s^(j+m n) := by rw [pow_add]; ring
    _ ≤ 2^(N n)*δ*s^(N n) := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) hj) hδ
      · exact pow_le_pow_of_le_one hs hs1 hjm
      · positivity
      · positivity

lemma flux_close_estimate {n : ℕ} (hn : 1 ≤ n) {x y : Space n} (hx : (1:ℝ)/2 ≤ ‖x‖)
    (hy : ‖y‖ ≤ 2) (hxy : x ≠ y) {D : ℝ} (hD : 0 ≤ D)
    (hseg : ∀ t ∈ uIcc ‖x‖ ‖y‖, gapProfile t ≤ D) :
    |fluxFactor n (x,y)-eta n x+w n x*radialFactor (x,y)| ≤
      (2*secondConstant n*D^(N n-2)+3*derivativeConstant n*D^(N n-1))*‖x-y‖ := by
  obtain ⟨hDc,hSc,hWc⟩ := constants_nonneg n
  have hr : 0 < ‖x‖ := by linarith
  have hL : 0 < ‖x-y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxy)
  have hD1 : |derivativeProfile n ‖x‖| ≤ derivativeConstant n*D^(N n-1) :=
    (derivativeProfile_bound n ‖x‖).trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (gapProfile_nonneg _) (hseg _ left_mem_uIcc) _) (constants_nonneg n).1)
  have hJ : |inner ℝ (x-y) y| ≤ 2*‖x-y‖ :=
    (abs_real_inner_le_norm _ _).trans (by nlinarith [norm_nonneg (x-y)])
  have hI : |inner ℝ x (x-y)| ≤ ‖x‖*‖x-y‖ := abs_real_inner_le_norm _ _
  have he := eta_radial_taylor hn hx y hD hseg
  rw [flux_linearization_identity (norm_pos_iff.mp hr) hxy]
  apply (abs_sub_le _ 0 _).trans
  simp only [sub_zero,zero_sub,abs_neg,abs_div,abs_mul,abs_of_nonneg (norm_nonneg x),abs_of_nonneg (sq_nonneg ‖x-y‖)]
  have hfirst : |eta n x-eta n y-derivativeProfile n ‖x‖*inner ℝ x (x-y)/‖x‖| *
      |inner ℝ (x-y) y|/‖x-y‖^2 ≤
      2*(secondConstant n*D^(N n-2)+derivativeConstant n*D^(N n-1))*‖x-y‖ := by
    apply (div_le_iff₀ (sq_pos_of_pos hL)).mpr
    have hh := mul_le_mul he hJ (abs_nonneg _) (by positivity)
    nlinarith [hh]
  have hsecond : |derivativeProfile n ‖x‖| *|inner ℝ x (x-y)|/‖x‖ ≤ derivativeConstant n*D^(N n-1)*‖x-y‖ := by
    apply (div_le_iff₀ hr).mpr
    have hh := mul_le_mul hD1 hI (abs_nonneg _) (by positivity)
    nlinarith [hh]
  linarith

lemma localError_close {n : ℕ} (hn : 1 ≤ n) {δ : ℝ} (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1/4)
    {x y : Space n} (hs : 0 < pairGap (x,y)) (hxy : ‖x-y‖ ≤ δ*pairGap (x,y)^(m n)) (hne : x ≠ y) :
    localError (x,y) ≤ closeConstant n*δ*(eta n x+eta n y) := by
  obtain ⟨hxpos,hypos,hseg,hL⟩ := close_pair_gaps hδ hδ1 hs hxy
  have hs0 := pairGap_bounds (x,y)
  obtain ⟨hDc,hSc,hWc⟩ := constants_nonneg n
  have hC : 0 ≤ closeConstant n := by unfold closeConstant; positivity
  by_cases hx : ‖x‖ ≤ 1/2
  · have hy : ‖y‖ ≤ 1 := by
      have hh := norm_le_norm_add_norm_sub x y
      have hm : δ*pairGap (x,y) ≤ 1/4 := mul_le_of_le_one_right hδ (hs0.2) |>.trans hδ1
      linarith
    have hx1 : ‖x‖ ≤ 1 := by linarith
    have hflux : fluxFactor n (x,y)=1 := by
      simp only [fluxFactor,X,eta_eq_one hx1,eta_eq_one hy,one_smul,real_inner_self_eq_norm_sq]
      exact div_self (ne_of_gt (sq_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hne))))
    simp only [localError,hflux,eta_eq_one hx1,eta_eq_one hy,w_inner n hx1,zero_mul,
      sub_self,add_zero,abs_zero]
    positivity
  · have hD : 0 ≤ 2*pairGap (x,y) := by positivity
    have hf := flux_close_estimate hn (le_of_not_ge hx) ((d_pos_iff y).mp hypos).le hne hD
      (fun _ ht => (norm_segment_gap hseg ht).2)
    have he := eta_oscillation n hD hseg
    rw [abs_sub_comm,dist_eq_norm] at he
    have hN := N_ge_two n
    have hP := close_power_bound hs0.1 hs0.2 hδ hxy (by omega : N n-2 ≤ N n) (by simp [m]; omega : N n ≤ N n-2+m n)
    have hP' := close_power_bound hs0.1 hs0.2 hδ hxy (by omega : N n-1 ≤ N n) (by simp [m]; omega : N n ≤ N n-1+m n)
    unfold localError
    calc
      _ ≤ (2*secondConstant n)*((2*pairGap (x,y))^(N n-2)*‖x-y‖)+
        (4*derivativeConstant n)*((2*pairGap (x,y))^(N n-1)*‖x-y‖) := by linarith
      _ ≤ (2*secondConstant n+4*derivativeConstant n)*(2^(N n)*δ*pairGap (x,y)^(N n)) := by
        have hh := mul_le_mul_of_nonneg_left hP (by positivity : 0 ≤ 2*secondConstant n)
        have hh' := mul_le_mul_of_nonneg_left hP' (by positivity : 0 ≤ 4*derivativeConstant n)
        nlinarith
      _ = closeConstant n*δ*pairGap (x,y)^(N n) := by unfold closeConstant; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (pairGap_power_le (x,y)) (mul_nonneg hC hδ)

end HenonLaneEmden
end
end NearLocalization

end OAI
end

section
-- module Solutions.OAIQW_HenonLaneEmden.FarInteraction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section FarInteraction

open MeasureTheory Set Metric
open scoped ENNReal
noncomputable section
namespace HenonLaneEmden
open Cutoff

@[fun_prop] lemma measurable_farWeight (n : ℕ) (δ j : ℝ) : Measurable (farWeight (n:=n) δ j) := by
  unfold farWeight
  have hd : Continuous (fun z : Space n × Space n => d z.1) := continuous_d.comp continuous_fst
  have ht : Continuous (fun z : Space n × Space n => δ*d z.1^(m n)) := continuous_const.mul (hd.pow _)
  have hs : Continuous (fun z : Space n × Space n => ‖z.1-z.2‖) := (continuous_fst.sub continuous_snd).norm
  exact (hd.measurable.pow_const j).ite ((isOpen_lt continuous_const hd).measurableSet.inter
    (isClosed_le ht hs).measurableSet) measurable_const

lemma farWeight_nonneg {n : ℕ} (δ j : ℝ) (z : Space n × Space n) : 0 ≤ farWeight δ j z := by
  unfold farWeight; split_ifs
  · exact Real.rpow_nonneg (d_nonneg z.1) j
  · exact le_rfl

lemma far_power_bound {n : ℕ} {δ r j : ℝ} (hδ : 0 < δ) (hr : 0 < r) (hr1 : r ≤ 1)
    (hj : 0 ≤ j+(m n:ℝ)*(2-(n:ℝ))) :
    r^j*(δ*r^(m n))^(2-(n:ℝ)) ≤ δ^(2-(n:ℝ)) := by
  rw [Real.mul_rpow hδ.le (pow_nonneg hr.le _),← Real.rpow_natCast r (m n),← Real.rpow_mul hr.le,
    mul_left_comm,← Real.rpow_add hr]
  exact mul_le_of_le_one_right (by positivity) (Real.rpow_le_one hr.le hr1 hj)

lemma IsSolution.truncated_newton_bound {n : ℕ} (hn : 2 ≤ n) {p q A B : ℝ}
    {u v : Space n → ℝ} (h : IsSolution n p q A B u v) (hp : 0 < p) (hq : 0 < q)
    {x : Space n} (hx : ‖x‖ ≤ 4) {l : ℝ} (hl : 0 < l) (hl1 : l ≤ 1) :
    (∫⁻ y in {y | l ≤ ‖x-y‖}, ENNReal.ofReal (source v p A y)*ENNReal.ofReal (newtonKernel n (x,y))) ≤
      ENNReal.ofReal ((newtonDenom n)⁻¹*(sourceConstant n p q A B*8^((n:ℝ)-2-alpha p q A B)+
        uniformTailConstant n p q A B)*l^(2-(n:ℝ))) := by
  have hd := newtonDenom_pos (h.dimension_ge_three hn)
  have hgm := measurable_source h.continuous_v p A
  have hs : MeasurableSet {y : Space n | l ≤ ‖x-y‖} := (isClosed_le continuous_const (continuous_const.sub continuous_id).norm).measurableSet
  have he : (∫⁻ y in {y | l ≤ ‖x-y‖}, ENNReal.ofReal (‖x-y‖^(2-(n:ℝ))) ∂sourceMeasure v p A) =
      ∫⁻ y in {y | l ≤ ‖x-y‖}, ENNReal.ofReal (source v p A y)*ENNReal.ofReal (‖x-y‖^(2-(n:ℝ))) := by
    rw [← lintegral_indicator hs,lintegral_sourceMeasure h.continuous_v p A (by fun_prop)]
    rw [← lintegral_indicator hs]
    apply lintegral_congr
    intro y
    by_cases hy : l ≤ ‖x-y‖ <;> simp [hy]
  simp_rw [newtonKernel,ENNReal.ofReal_mul (inv_nonneg.mpr hd.le),mul_left_comm (ENNReal.ofReal (source v p A _))]
  rw [lintegral_const_mul _ (by fun_prop),← he]
  have hh := mul_le_mul (le_refl (ENNReal.ofReal ((newtonDenom n)⁻¹))) (h.uniform_g_truncated hn hp hq hx hl hl1) bot_le bot_le
  convert hh using 1 <;> first | rfl | (rw [← ENNReal.ofReal_mul (inv_nonneg.mpr hd.le)]; congr 1; ring)

lemma truncatedConstant_nonneg (n : ℕ) (p q A B : ℝ) : 0 ≤ truncatedConstant n p q A B := le_max_right _ _
lemma farConstant_nonneg {n : ℕ} (p q A B : ℝ) {δ : ℝ} (hδ : 0 ≤ δ) : 0 ≤ farConstant n p q A B δ := by
  unfold farConstant
  exact mul_nonneg (mul_nonneg (truncatedConstant_nonneg _ _ _ _ _) (Real.rpow_nonneg hδ _)) (le_max_right _ _)

lemma IsSolution.far_inner_bound {n : ℕ} (hn : 2 ≤ n) {p q A B δ j : ℝ}
    {u v : Space n → ℝ} (h : IsSolution n p q A B u v) (hp : 0 < p) (hq : 0 < q)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hj : 0 ≤ j+(m n:ℝ)*(2-(n:ℝ))) (x : Space n) :
    (∫⁻ y, ENNReal.ofReal (source v p A y)*ENNReal.ofReal (newtonKernel n (x,y))*
      ENNReal.ofReal (farWeight δ j (x,y))) ≤
      (ball (0:Space n) 2).indicator (fun _ => ENNReal.ofReal (truncatedConstant n p q A B*δ^(2-(n:ℝ)))) x := by
  have hgm := measurable_source h.continuous_v p A
  by_cases hx : 0 < d x
  · have hx2 : x ∈ ball (0:Space n) 2 := mem_ball_zero_iff.mpr ((d_pos_iff x).mp hx)
    rw [indicator_of_mem hx2]
    let l := δ*d x^(m n)
    have hl : 0 < l := mul_pos hδ (pow_pos hx _)
    have hl1 : l ≤ 1 := (mul_le_of_le_one_left (pow_nonneg hx.le _) hδ1).trans
      (pow_le_one₀ hx.le (d_le_one x))
    have hs : MeasurableSet {y : Space n | l ≤ ‖x-y‖} :=
      (isClosed_le continuous_const (continuous_const.sub continuous_id).norm).measurableSet
    have he : (∫⁻ y, ENNReal.ofReal (source v p A y)*ENNReal.ofReal (newtonKernel n (x,y))*
        ENNReal.ofReal (farWeight δ j (x,y))) =
        ENNReal.ofReal (d x^j)*(∫⁻ y in {y | l ≤ ‖x-y‖},
          ENNReal.ofReal (source v p A y)*ENNReal.ofReal (newtonKernel n (x,y))) := by
      rw [← lintegral_const_mul _ (by fun_prop),← lintegral_indicator hs]
      apply lintegral_congr
      intro y
      by_cases hy : l ≤ ‖x-y‖ <;> simp [farWeight,hx,hy,l]
      ring
    rw [he]
    have hb := (h.truncated_newton_bound hn hp hq (by have hh := mem_ball_zero_iff.mp hx2; linarith) hl hl1).trans
      (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (le_max_left _ 0) (Real.rpow_nonneg hl.le (2-(n:ℝ)))))
    have hh := mul_le_mul (le_refl (ENNReal.ofReal (d x^j))) hb bot_le bot_le
    apply hh.trans
    rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hx.le j)]
    apply ENNReal.ofReal_le_ofReal
    convert mul_le_mul_of_nonneg_left (far_power_bound hδ hx (d_le_one x) hj)
      (truncatedConstant_nonneg n p q A B) using 1 <;> first | rfl | (dsimp [truncatedConstant,l]; ring)
  · have hx2 : x ∉ ball (0:Space n) 2 := by simpa only [mem_ball_zero_iff,← d_pos_iff x] using hx
    simp only [farWeight,hx,false_and,ite_false,ENNReal.ofReal_zero,mul_zero,lintegral_zero,
      indicator_of_notMem hx2]
    exact le_rfl

lemma IsSolution.far_interaction_bound {n : ℕ} (hn : 2 ≤ n) {p q A B δ j : ℝ}
    {u v : Space n → ℝ} (h : IsSolution n p q A B u v) (hp : 0 < p) (hq : 0 < q)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hj : 0 ≤ j+(m n:ℝ)*(2-(n:ℝ))) :
    (∫⁻ z, ENNReal.ofReal (farWeight δ j z) ∂interaction (source u q B) (source v p A)) ≤
      ENNReal.ofReal (farConstant n p q A B δ) := by
  have hfm := measurable_source h.continuous_u q B
  have hgm := measurable_source h.continuous_v p A
  rw [lintegral_interaction hfm hgm (by fun_prop),lintegral_prod _ (by fun_prop)]
  have heq (x : Space n) : (∫⁻ y, ENNReal.ofReal (source u q B x)*
      (ENNReal.ofReal (source v p A y)*(ENNReal.ofReal (newtonKernel n (x,y))*ENNReal.ofReal (farWeight δ j (x,y))))) =
      ENNReal.ofReal (source u q B x)*(∫⁻ y,
      ENNReal.ofReal (source v p A y)*(ENNReal.ofReal (newtonKernel n (x,y))*ENNReal.ofReal (farWeight δ j (x,y)))) :=
    lintegral_const_mul _ (by fun_prop)
  simp_rw [mul_assoc,heq]
  have hb := lintegral_mono (μ := volume) (fun x => mul_le_mul (le_refl (ENNReal.ofReal (source u q B x)))
    (h.far_inner_bound hn hp hq hδ hδ1 hj x) bot_le bot_le)
  simp only [mul_assoc] at hb
  apply hb.trans
  have he : (∫⁻ x, ENNReal.ofReal (source u q B x)*(ball (0:Space n) 2).indicator
      (fun _ => ENNReal.ofReal (truncatedConstant n p q A B*δ^(2-(n:ℝ)))) x) =
      ENNReal.ofReal (truncatedConstant n p q A B*δ^(2-(n:ℝ)))*sourceMeasure u q B (ball 0 2) := by
    rw [← lintegral_sourceMeasure h.continuous_u q B (measurable_const.indicator measurableSet_ball),
      lintegral_indicator measurableSet_ball,setLIntegral_const]
  rw [he,h.swap.sourceMeasure_ball hn]
  have hm := (h.swap.sourceMass_g_upper hn hq hp (by norm_num : (0:ℝ) < 2)).trans (le_max_left _ 0)
  exact (mul_le_mul (le_refl _) (ENNReal.ofReal_le_ofReal hm) bot_le bot_le).trans_eq
    (by rw [← ENNReal.ofReal_mul (mul_nonneg (truncatedConstant_nonneg _ _ _ _ _) (Real.rpow_nonneg hδ.le _))]; rfl)

lemma lintegral_interaction_swap {n : ℕ} {f g : Space n → ℝ}
    (hf : Measurable f) (hg : Measurable g) {F : Space n × Space n → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ z, F z.swap ∂interaction f g) = ∫⁻ z, F z ∂interaction g f := by
  change (∫⁻ z, (F ∘ Prod.swap) z ∂interaction f g) = _
  rw [lintegral_interaction hf hg (hF.comp measurable_swap),lintegral_interaction hg hf hF,← lintegral_prod_swap]
  apply lintegral_congr
  intro z
  change ENNReal.ofReal (f z.2)*ENNReal.ofReal (g z.1)*ENNReal.ofReal (newtonKernel n (z.2,z.1))*F z = _
  rw [newtonKernel_symm n z.2 z.1]
  ring

end HenonLaneEmden
end
end FarInteraction

end OAI
end

section
-- module Solutions.OAIQW_HenonLaneEmden.FarLocalization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section FarLocalization

open MeasureTheory Set Metric
open scoped InnerProductSpace
noncomputable section
namespace HenonLaneEmden
open Cutoff AdaptiveCap

lemma norm_X_bound {n : ℕ} (x : Space n) : ‖X n x‖ ≤ 2*eta n x := by
  by_cases hx : ‖x‖ ≤ 2
  · rw [X,norm_smul,Real.norm_eq_abs,abs_of_nonneg (eta_nonneg n x)]
    nlinarith [eta_nonneg n x]
  · simp only [X,eta_eq_zero (le_of_not_ge hx),zero_smul,norm_zero,mul_zero,le_refl]

lemma fluxFactor_bound {n : ℕ} (x y : Space n) :
    |fluxFactor n (x,y)| ≤ 2*(eta n x+eta n y)/‖x-y‖ := by
  by_cases hxy : x=y
  · subst y
    simp only [fluxFactor,sub_self,inner_zero_left,zero_div,abs_zero,norm_zero,div_zero,le_refl]
  have hL : 0 < ‖x-y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxy)
  rw [fluxFactor,abs_div,abs_of_nonneg (sq_nonneg ‖x-y‖),div_le_div_iff₀ (sq_pos_of_pos hL) hL]
  have hh := (abs_real_inner_le_norm (x-y) (X n x-X n y)).trans
    (mul_le_mul_of_nonneg_left (norm_sub_le _ _) (norm_nonneg _))
  have hm := add_le_add (norm_X_bound x) (norm_X_bound y)
  have hh' := mul_le_mul_of_nonneg_left hm (norm_nonneg (x-y))
  nlinarith [mul_le_mul_of_nonneg_right (hh.trans hh') (norm_nonneg (x-y))]

lemma localError_rough {n : ℕ} (x y : Space n) :
    localError (x,y) ≤ (2*eta n x/‖x-y‖+2*eta n x+w n x)+
      (2*eta n y/‖x-y‖+2*eta n y+w n y) := by
  have hηx := eta_nonneg n x
  have hηy := eta_nonneg n y
  have hwx := w_nonneg n x
  have hwy := w_nonneg n y
  have hD := radialFactor_bounds (x,y)
  have hh : |fluxFactor n (x,y)-eta n x+w n x*radialFactor (x,y)| ≤ |fluxFactor n (x,y)|+eta n x+w n x := by
    have hs : |fluxFactor n (x,y)-eta n x| ≤ |fluxFactor n (x,y)|+eta n x := by
      simpa only [sub_zero,zero_sub,abs_neg,abs_of_nonneg hηx] using abs_sub_le (fluxFactor n (x,y)) 0 (eta n x)
    have hw : |w n x*radialFactor (x,y)| ≤ w n x := by
      rw [abs_of_nonneg (mul_nonneg hwx hD.1)]
      exact mul_le_of_le_one_right hwx hD.2
    exact (abs_add_le _ _).trans (by linarith)
  have he : |eta n x-eta n y| ≤ eta n x+eta n y := by
    simpa only [sub_zero,zero_sub,abs_neg,abs_of_nonneg hηx,abs_of_nonneg hηy] using abs_sub_le (eta n x) 0 (eta n y)
  have hf := fluxFactor_bound x y
  unfold localError
  rw [mul_add,add_div] at hf
  linarith

lemma endpoint_far_bound {n : ℕ} {δ : ℝ} (hδ : 0 < δ) {x y : Space n} (hne : x ≠ y)
    (hfar : 0 < d x → δ*d x^(m n) ≤ ‖x-y‖) :
    2*eta n x/‖x-y‖+2*eta n x+w n x ≤ farLocalConstant n*
      (farWeight δ (N n-1:ℕ) (x,y)+δ⁻¹*farWeight δ ((N n:ℝ)-(m n:ℝ)) (x,y)) := by
  have hd := d_nonneg x
  have hN := N_ge_two n
  have hC : 0 ≤ derivativeConstant n := (constants_nonneg n).1
  by_cases hx : 0 < d x
  · have hf := hfar hx
    simp only [farWeight,ite_eq_left (show 0 < d x ∧ δ*d x^(m n) ≤ ‖x-y‖ from ⟨hx,hf⟩),Real.rpow_natCast]
    have hη := (eta_gap_bounds n x).2
    have hw : w n x ≤ 2*derivativeConstant n*d x^(N n-1) := by
      convert wProfile_bound n (norm_nonneg x) using 1
      · exact w_eq_profile n x
      · dsimp [derivativeConstant,d]; ring
    have hpow : d x^(N n) ≤ d x^(N n-1) := pow_le_pow_of_le_one hd (d_le_one x) (by omega)
    have hη' : eta n x ≤ 3^(N n)*d x^(N n-1) := hη.trans (mul_le_mul_of_nonneg_left hpow (by positivity))
    have hL : 0 < ‖x-y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
    have hηL : 2*eta n x/‖x-y‖ ≤ 2*3^(N n)*δ⁻¹*d x^((N n:ℝ)-(m n:ℝ)) := by
      have hh := div_le_div₀ (by positivity : 0 ≤ 2*(3^(N n)*d x^(N n))) (show 2*eta n x ≤ 2*(3^(N n)*d x^(N n)) by linarith)
        (mul_pos hδ (pow_pos hx _)) hf
      apply hh.trans_eq
      rw [Real.rpow_sub hx,Real.rpow_natCast,Real.rpow_natCast]
      field_simp
    have hp0 : 0 ≤ δ⁻¹*d x^((N n:ℝ)-(m n:ℝ)) := mul_nonneg (inv_nonneg.mpr hδ.le) (Real.rpow_nonneg hd _)
    unfold farLocalConstant
    have hm := mul_nonneg hC hp0
    nlinarith [hηL,hw,hη']
  · have hx2 : 2 ≤ ‖x‖ := not_lt.mp (fun hh => hx ((d_pos_iff x).mpr hh))
    simp only [eta_eq_zero hx2,w_outer n hx2,mul_zero,zero_div,farWeight,hx,false_and,
      ite_false,add_zero,le_refl]

lemma far_pair_endpoint {n : ℕ} {δ : ℝ} (hδ : 0 ≤ δ) {x y : Space n}
    (hf : ¬(0 < pairGap (x,y) ∧ ‖x-y‖ ≤ δ*pairGap (x,y)^(m n))) :
    (0 < d x → δ*d x^(m n) ≤ ‖x-y‖) ∧ (0 < d y → δ*d y^(m n) ≤ ‖x-y‖) := by
  have hsx : d x ≤ pairGap (x,y) := le_max_left _ _
  have hsy : d y ≤ pairGap (x,y) := le_max_right _ _
  constructor
  · intro hx
    have hs := hx.trans_le hsx
    exact (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (d_nonneg x) hsx _) hδ).trans
      (le_of_lt (not_le.mp (fun hL => hf ⟨hs,hL⟩)))
  · intro hy
    have hs := hy.trans_le hsy
    exact (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (d_nonneg y) hsy _) hδ).trans
      (le_of_lt (not_le.mp (fun hL => hf ⟨hs,hL⟩)))

lemma localError_far {n : ℕ} {δ : ℝ} (hδ : 0 < δ) {x y : Space n} (hne : x ≠ y)
    (hf : ¬(0 < pairGap (x,y) ∧ ‖x-y‖ ≤ δ*pairGap (x,y)^(m n))) :
    localError (x,y) ≤ farLocalConstant n*
      (farWeight δ (N n-1:ℕ) (x,y)+δ⁻¹*farWeight δ ((N n:ℝ)-(m n:ℝ)) (x,y)+
      farWeight δ (N n-1:ℕ) (y,x)+δ⁻¹*farWeight δ ((N n:ℝ)-(m n:ℝ)) (y,x)) := by
  obtain ⟨hx,hy⟩ := far_pair_endpoint hδ.le hf
  have hh := endpoint_far_bound hδ hne hx
  have hh' := endpoint_far_bound hδ hne.symm (fun hy' => by simpa only [norm_sub_rev y x] using hy hy')
  rw [norm_sub_rev y x] at hh'
  exact (localError_rough x y).trans ((add_le_add hh hh').trans_eq (by ring))

end HenonLaneEmden
end
end FarLocalization

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

lemma interaction_ae_ne {n : ℕ} (hn : 1 ≤ n) (f g : Space n → ℝ) :
    ∀ᵐ z : Space n × Space n ∂interaction f g, z.1 ≠ z.2 := by
  have : Nontrivial (Space n) := (Module.finrank_pos_iff (R := ℝ)).mp (by simp; omega)
  apply ae_iff.mpr
  apply withDensity_absolutelyContinuous (volume.prod volume) _
  apply ae_iff.mp
  apply (Measure.ae_prod_iff_ae_ae (by measurability)).mpr
  exact ae_of_all _ fun x => ae_iff.mpr (by simp)

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

lemma IsSolution.lintegral_weight_right {n : ℕ} (hn : 2 ≤ n) {p q A B : ℝ}
    {u v χ : Space n → ℝ} (h : IsSolution n p q A B u v) (hp : 0 < p)
    (hχ : Continuous χ) (hχc : HasCompactSupport χ) (hχ0 : ∀ x, 0 ≤ χ x) :
    (∫⁻ z, ENNReal.ofReal (χ z.2) ∂interaction (source u q B) (source v p A)) =
      ENNReal.ofReal (weightedEnergy χ v p A) := by
  rw [h.interaction_right hn hp hχ.measurable.ennreal_ofReal,← h.swap.weightedEnergyN_eq hn hχ hχc hχ0]
  unfold weightedEnergyN
  apply lintegral_congr
  intro x
  rw [← ENNReal.ofReal_mul (mul_nonneg (source_nonneg (fun x => (h.positive_v x).le) p A x) (h.positive_v x).le)]
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

lemma IsSolution.weight_right {n : ℕ} (hn : 2 ≤ n) {p q A B : ℝ}
    {u v χ : Space n → ℝ} (h : IsSolution n p q A B u v) (hp : 0 < p)
    (hχ : Continuous χ) (hχc : HasCompactSupport χ) (hχ0 : ∀ x, 0 ≤ χ x) :
    Integrable (fun z => χ z.2) (interaction (source u q B) (source v p A)) ∧
    (∫ z, χ z.2 ∂interaction (source u q B) (source v p A)) = weightedEnergy χ v p A := by
  have he := h.lintegral_weight_right hn hp hχ hχc hχ0
  refine ⟨(integrable_integral_le_of_lintegral_le (hχ.measurable.comp measurable_snd) (fun z => hχ0 z.2)
    (weightedEnergyN_nonneg hχ0 (fun x => (h.positive_v x).le)) he.le).1,?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ (fun z : Space n × Space n => hχ0 z.2)) (hχ.measurable.comp measurable_snd).aestronglyMeasurable,he,
    ENNReal.toReal_ofReal (weightedEnergyN_nonneg hχ0 (fun x => (h.positive_v x).le))]

lemma IsSolution.farWeight_bound {n : ℕ} (hn : 2 ≤ n) {p q A B δ j : ℝ}
    {u v : Space n → ℝ} (h : IsSolution n p q A B u v) (hp : 0 < p) (hq : 0 < q)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hj : 0 ≤ j+(m n:ℝ)*(2-(n:ℝ))) :
    Integrable (farWeight δ j) (interaction (source u q B) (source v p A)) ∧
    (∫ z, farWeight δ j z ∂interaction (source u q B) (source v p A)) ≤ farConstant n p q A B δ :=
  integrable_integral_le_of_lintegral_le (by fun_prop) (farWeight_nonneg δ j) (farConstant_nonneg p q A B hδ.le)
    (h.far_interaction_bound hn hp hq hδ hδ1 hj)

lemma IsSolution.farWeight_swap_bound {n : ℕ} (hn : 2 ≤ n) {p q A B δ j : ℝ}
    {u v : Space n → ℝ} (h : IsSolution n p q A B u v) (hp : 0 < p) (hq : 0 < q)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hj : 0 ≤ j+(m n:ℝ)*(2-(n:ℝ))) :
    Integrable (fun z => farWeight δ j z.swap) (interaction (source u q B) (source v p A)) ∧
    (∫ z, farWeight δ j z.swap ∂interaction (source u q B) (source v p A)) ≤ farConstant n q p B A δ := by
  apply integrable_integral_le_of_lintegral_le ((measurable_farWeight n δ j).comp measurable_swap) (fun z => farWeight_nonneg δ j z.swap)
    (farConstant_nonneg q p B A hδ.le)
  simp only [Function.comp_def]
  rw [lintegral_interaction_swap (measurable_source h.continuous_u q B)
    (measurable_source h.continuous_v p A) (measurable_farWeight n δ j).ennreal_ofReal]
  exact h.swap.far_interaction_bound hn hq hp hδ hδ1 hj

lemma cutoff_far_exponents (n : ℕ) :
    0 ≤ ((N n-1:ℕ):ℝ)+(m n:ℝ)*(2-(n:ℝ)) ∧
    0 ≤ ((N n:ℝ)-(m n:ℝ))+(m n:ℝ)*(2-(n:ℝ)) ∧
    0 ≤ ((N n-n:ℕ):ℝ)+(m n:ℝ)*(2-(n:ℝ)) := by
  have hN : 1 ≤ N n := by have := N_ge_two n; omega
  have hNn : n ≤ N n := by unfold N; omega
  rw [Nat.cast_sub hN,Nat.cast_sub hNn]
  simp only [N,m,k,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one]
  constructor <;> (try constructor) <;> nlinarith [Nat.cast_nonneg (α:=ℝ) n]

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

end HenonLaneEmden
end
end RadialJoint

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
lemma localError_nonneg {n : ℕ} (z : Space n × Space n) : 0 ≤ localError z := add_nonneg (abs_nonneg _) (abs_nonneg _)
lemma closeConstant_nonneg (n : ℕ) : 0 ≤ closeConstant n := by
  obtain ⟨hD,hS,hW⟩ := constants_nonneg n
  unfold closeConstant; positivity
lemma farLocalConstant_nonneg (n : ℕ) : 0 ≤ farLocalConstant n := by
  have := (constants_nonneg n).1
  unfold farLocalConstant; positivity

lemma localFarSum_nonneg {n : ℕ} {δ : ℝ} (hδ : 0 ≤ δ) (z : Space n × Space n) : 0 ≤ localFarSum δ z := by
  unfold localFarSum
  exact add_nonneg (add_nonneg (add_nonneg (farWeight_nonneg _ _ _) (mul_nonneg (inv_nonneg.mpr hδ)
    (farWeight_nonneg _ _ _))) (farWeight_nonneg _ _ _)) (mul_nonneg (inv_nonneg.mpr hδ) (farWeight_nonneg _ _ _))
lemma localError_global {n : ℕ} (hn : 1 ≤ n) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1/4)
    {z : Space n × Space n} (hne : z.1 ≠ z.2) :
    localError z ≤ closeConstant n*δ*(eta n z.1+eta n z.2)+farLocalConstant n*localFarSum δ z := by
  by_cases hc : 0 < pairGap z ∧ ‖z.1-z.2‖ ≤ δ*pairGap z^(m n)
  · exact (localError_close hn hδ.le hδ1 hc.1 hc.2 hne).trans
      (le_add_of_nonneg_right (mul_nonneg (farLocalConstant_nonneg n) (localFarSum_nonneg hδ.le z)))
  · exact (localError_far hδ hne hc).trans
      (le_add_of_nonneg_left (mul_nonneg (mul_nonneg (closeConstant_nonneg n) hδ.le)
        (add_nonneg (eta_nonneg n _) (eta_nonneg n _))))

lemma localizationConstant_nonneg {n : ℕ} (p q A B : ℝ) {δ : ℝ} (hδ : 0 ≤ δ) :
    0 ≤ localizationConstant n p q A B δ := by
  unfold localizationConstant
  exact mul_nonneg (mul_nonneg (farLocalConstant_nonneg n) (by positivity))
    (add_nonneg (farConstant_nonneg _ _ _ _ hδ) (farConstant_nonneg _ _ _ _ hδ))

lemma IsSolution.localFarSum_bound {n : ℕ} (hn : 2 ≤ n) {p q A B δ : ℝ}
    {u v : Space n → ℝ} (h : IsSolution n p q A B u v) (hp : 0 < p) (hq : 0 < q)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    Integrable (localFarSum δ) (interaction (source u q B) (source v p A)) ∧
    (∫ z, localFarSum δ z ∂interaction (source u q B) (source v p A)) ≤
      (1+δ⁻¹)*(farConstant n p q A B δ+farConstant n q p B A δ) := by
  have h1 := h.farWeight_bound hn hp hq hδ hδ1 (cutoff_far_exponents n).1
  have h2 := h.farWeight_bound hn hp hq hδ hδ1 (cutoff_far_exponents n).2.1
  have h3 := h.farWeight_swap_bound hn hp hq hδ hδ1 (cutoff_far_exponents n).1
  have h4 := h.farWeight_swap_bound hn hp hq hδ hδ1 (cutoff_far_exponents n).2.1
  have h12 : Integrable (fun z => farWeight δ (N n-1:ℕ) z+δ⁻¹*farWeight δ ((N n:ℝ)-(m n:ℝ)) z) _ := h1.1.add (h2.1.const_mul _)
  have h123 : Integrable (fun z => farWeight δ (N n-1:ℕ) z+δ⁻¹*farWeight δ ((N n:ℝ)-(m n:ℝ)) z+farWeight δ (N n-1:ℕ) z.swap) _ := h12.add h3.1
  refine ⟨h123.add (h4.1.const_mul _),?_⟩
  unfold localFarSum
  rw [integral_add h123 (h4.1.const_mul _),
    integral_add h12 h3.1,integral_add h1.1 (h2.1.const_mul _),
    integral_const_mul,integral_const_mul]
  have hh := add_le_add (add_le_add (add_le_add h1.2 (mul_le_mul_of_nonneg_left h2.2 (inv_nonneg.mpr hδ.le))) h3.2)
    (mul_le_mul_of_nonneg_left h4.2 (inv_nonneg.mpr hδ.le))
  exact hh.trans_eq (by ring)

lemma IsSolution.localError_bound {n : ℕ} (hn : 2 ≤ n) {p q A B δ : ℝ}
    {u v : Space n → ℝ} (h : IsSolution n p q A B u v) (hp : 0 < p) (hq : 0 < q)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1/4) :
    Integrable localError (interaction (source u q B) (source v p A)) ∧
    (∫ z, localError z ∂interaction (source u q B) (source v p A)) ≤
      closeConstant n*δ*(weightedEnergy (eta n) u q B+weightedEnergy (eta n) v p A)+localizationConstant n p q A B δ := by
  have hηf := h.weight_left hn hq (continuous_eta n) (compactSupport_eta n) (eta_nonneg n)
  have hηg := h.weight_right hn hp (continuous_eta n) (compactSupport_eta n) (eta_nonneg n)
  have hfar := h.localFarSum_bound hn hp hq hδ (by linarith)
  have hηi : Integrable (fun z : Space n × Space n => eta n z.1+eta n z.2) _ := hηf.1.add hηg.1
  have hi : Integrable (fun z : Space n × Space n => closeConstant n*δ*(eta n z.1+eta n z.2)+farLocalConstant n*localFarSum δ z) _ :=
    (hηi.const_mul _).add (hfar.1.const_mul _)
  have hb : ∀ᵐ z ∂interaction (source u q B) (source v p A), localError z ≤
      closeConstant n*δ*(eta n z.1+eta n z.2)+farLocalConstant n*localFarSum δ z :=
    (interaction_ae_ne (by omega : 1 ≤ n) _ _).mono (fun _ hz => localError_global (by omega) hδ hδ1 hz)
  have he : Integrable localError (interaction (source u q B) (source v p A)) := hi.mono'
    (measurable_localError n).aestronglyMeasurable (hb.mono (fun z hz => by
      simpa only [Real.norm_eq_abs,abs_of_nonneg (localError_nonneg z)] using hz))
  refine ⟨he,(integral_mono_ae he hi hb).trans ?_⟩
  rw [integral_add (hηi.const_mul _) (hfar.1.const_mul _),integral_const_mul,
    integral_const_mul,integral_add hηf.1 hηg.1,hηf.2,hηg.2]
  calc
    _ ≤ closeConstant n*δ*(weightedEnergy (eta n) u q B+weightedEnergy (eta n) v p A)+
        farLocalConstant n*((1+δ⁻¹)*(farConstant n p q A B δ+farConstant n q p B A δ)) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left hfar.2 (farLocalConstant_nonneg n))
    _ = _ := by unfold localizationConstant; ring

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

lemma IsSolution.local_errors_le {n : ℕ} (hn : 2 ≤ n) {p q A B : ℝ}
    {u v : Space n → ℝ} (h : IsSolution n p q A B u v) (hp : 0 < p) (hq : 0 < q) :
    |localQ (source u q B) (source v p A)|+|weightedEnergy (eta n) u q B-weightedEnergy (eta n) v p A| ≤
      ∫ z, localError z ∂interaction (source u q B) (source v p A) := by
  have hηf := h.weight_left hn hq (continuous_eta n) (compactSupport_eta n) (eta_nonneg n)
  have hηg := h.weight_right hn hp (continuous_eta n) (compactSupport_eta n) (eta_nonneg n)
  have hi : Integrable (fun z : Space n × Space n => fluxFactor n z-eta n z.1+w n z.1*radialFactor z) _ :=
    ((h.integrable_fluxFactor hn hp hq).sub hηf.1).add (h.integrable_radialWeight hn hq)
  have hj : Integrable (fun z : Space n × Space n => eta n z.1-eta n z.2) _ := hηf.1.sub hηg.1
  unfold localQ localError
  rw [integral_add hi.abs hj.abs,← hηf.2,← hηg.2,← integral_sub hηf.1 hηg.1]
  exact add_le_add abs_integral_le_integral_abs abs_integral_le_integral_abs

lemma localization_relative_oai {n : ℕ} (hn : 2 ≤ n) {p q A B ε : ℝ} (hp : 0 < p) (hq : 0 < q)
    (hε : 0 < ε) : ∃ C : ℝ, 0 ≤ C ∧ ∀ u v : Space n → ℝ, IsSolution n p q A B u v →
      |localQ (source u q B) (source v p A)|+|weightedEnergy (eta n) u q B-weightedEnergy (eta n) v p A| ≤
        ε*(weightedEnergy (eta n) u q B+weightedEnergy (eta n) v p A)+C := by
  let δ := min (1/4) (ε/(closeConstant n+1))
  have hC := closeConstant_nonneg n
  have hden : 0 < closeConstant n+1 := by linarith
  have hδ : 0 < δ := lt_min (by norm_num) (div_pos hε hden)
  have hδ1 : δ ≤ 1/4 := min_le_left _ _
  have hδε : closeConstant n*δ ≤ ε := by
    have hh := (le_div_iff₀ hden).mp (min_le_right (1/4) (ε/(closeConstant n+1)))
    change δ*(closeConstant n+1) ≤ ε at hh
    nlinarith
  refine ⟨localizationConstant n p q A B δ,localizationConstant_nonneg p q A B hδ.le,?_⟩
  intro u v h
  have he := (h.local_errors_le hn hp hq).trans (h.localError_bound hn hp hq hδ hδ1).2
  have hE : 0 ≤ weightedEnergy (eta n) u q B+weightedEnergy (eta n) v p A :=
    add_nonneg (weightedEnergyN_nonneg (eta_nonneg n) (fun x => (h.positive_u x).le))
      (weightedEnergyN_nonneg (eta_nonneg n) (fun x => (h.positive_v x).le))
  exact he.trans (add_le_add (mul_le_mul_of_nonneg_right hδε hE) le_rfl)

end HenonLaneEmden
end
end RelativeLocalization

end OAI
end

theorem solution : type_of% @OAI.HenonLaneEmden.localization_relative_oai := @OAI.HenonLaneEmden.localization_relative_oai
