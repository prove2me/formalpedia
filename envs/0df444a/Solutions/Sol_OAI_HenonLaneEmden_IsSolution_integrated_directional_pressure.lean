-- Prove2me | solution 1 for OAI.HenonLaneEmden.IsSolution.integrated_directional_pressure
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-19T01:41:02.196983+00:00
-- url     : https://prove2.me/submissions/a93fd532-91fc-4f88-9007-1e7dfe30eeba

import Mathlib
import Definitions.Def_HenonEmden
import Definitions.Def_OAIQWHLE000
import Theorems.Thm_OAI_HenonLaneEmden_SpatialComponents_IsSolution_pressure_comparison
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
theorem dite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : p) :
    (if hp : p then a hp else b hp) = a h := dif_pos h
theorem dite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : ¬p) :
    (if hp : p then a hp else b hp) = b h := dif_neg h
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

lemma lintegral_polar_prod (f : E → ℝ≥0∞) :
    ∫⁻ x, f x ∂μ = ∫⁻ z : Metric.sphere (0:E) 1 × Ioi (0:ℝ),
      f (z.2.1 • z.1.1) ∂μ.toSphere.prod (volumeIoiPow (Module.finrank ℝ E-1)) := by
  calc
    _ = ∫⁻ x : ({0}ᶜ : Set E), f x.1 ∂μ.comap Subtype.val := by
      rw [lintegral_subtype_comap (measurableSet_singleton _).compl,
        restrict_compl_singleton]
    _ = _ := by
      simpa only [Function.comp_def, homeomorphUnitSphereProd_symm_apply_coe, polar_inverse] using μ.measurePreserving_homeomorphUnitSphereProd.lintegral_comp_emb
        (Homeomorph.measurableEmbedding _) (f ∘ Subtype.val ∘ (homeomorphUnitSphereProd E).symm)

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

lemma source_zero {n : ℕ} (u : Space n → ℝ) (q B : ℝ) : source u q B 0 = 0 := by simp [source]

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
-- module Solutions.OAIQW_HenonLaneEmden.CapGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE

section CapGeometry

open MeasureTheory MeasureTheory.Measure Set Metric
open scoped ENNReal Pointwise
noncomputable section
namespace HenonLaneEmden.CapGeometry

lemma volumeIoiPow_band_bounds (k : ℕ) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    ENNReal.ofReal (a^k*(b-a)) ≤ volumeIoiPow k (band a b) ∧
    volumeIoiPow k (band a b) ≤ ENNReal.ofReal (b^k*(b-a)) := by
  have hband : MeasurableSet (band a b) := (measurable_subtype_coe measurableSet_Ioo)
  have he : Subtype.val '' band a b = Ioo a b := by
    ext x
    constructor
    · rintro ⟨r,hr,rfl⟩; exact hr
    · intro hx; exact ⟨⟨x,ha.trans_lt hx.1⟩,hx,rfl⟩
  rw [volumeIoiPow,withDensity_apply _ hband,
    setLIntegral_subtype measurableSet_Ioi _ (fun r : ℝ => ENNReal.ofReal (r^k)),he]
  have hconst (c : ℝ) (hc : 0 ≤ c) :
      (∫⁻ _ in Ioo a b, ENNReal.ofReal c) = ENNReal.ofReal (c*(b-a)) := by
    rw [lintegral_const,Measure.restrict_apply_univ,Real.volume_Ioo,← ENNReal.ofReal_mul hc]
  constructor
  · rw [← hconst (a^k) (pow_nonneg ha k)]
    apply setLIntegral_mono' measurableSet_Ioo
    intro x hx
    exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ ha hx.1.le k)
  · rw [← hconst (b^k) (pow_nonneg (ha.trans hab) k)]
    apply setLIntegral_mono' measurableSet_Ioo
    intro x hx
    exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (ha.trans hx.1.le) hx.2.le k)

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]
  (μ : Measure E) [μ.IsAddHaarMeasure]

lemma polar_rectangle_le {S : Set (sphere (0:E) 1)} {I : Set (Ioi (0:ℝ))} {A : Set E}
    (hS : MeasurableSet S) (hI : MeasurableSet I) (hA : MeasurableSet A)
    (h : ∀ e ∈ S, ∀ r ∈ I, r.1 • e.1 ∈ A) :
    μ.toSphere S * volumeIoiPow (Module.finrank ℝ E-1) I ≤ μ A := by
  rw [← Measure.prod_prod]
  have he : μ A = ∫⁻ z : sphere (0:E) 1 × Ioi (0:ℝ), A.indicator (fun _ => (1:ℝ≥0∞))
      (z.2.1 • z.1.1) ∂μ.toSphere.prod (volumeIoiPow (Module.finrank ℝ E-1)) := by
    rw [← Polar.lintegral_polar_prod μ,lintegral_indicator hA,lintegral_one,Measure.restrict_apply_univ]
  have hr : (μ.toSphere.prod (volumeIoiPow (Module.finrank ℝ E-1))) (S ×ˢ I) =
      ∫⁻ z, (S ×ˢ I).indicator (fun _ => (1:ℝ≥0∞)) z
        ∂μ.toSphere.prod (volumeIoiPow (Module.finrank ℝ E-1)) := by
    rw [lintegral_indicator (hS.prod hI),lintegral_one,Measure.restrict_apply_univ]
  rw [he,hr]
  apply lintegral_mono
  intro z
  by_cases hz : z ∈ S ×ˢ I
  · simp only [indicator_of_mem hz,indicator_of_mem (h z.1 hz.1 z.2 hz.2),le_refl]
  · simp only [indicator_of_notMem hz,zero_le]

lemma measure_le_polar_rectangle {S : Set (sphere (0:E) 1)} {I : Set (Ioi (0:ℝ))} {A : Set E}
    (hS : MeasurableSet S) (hI : MeasurableSet I) (hA : MeasurableSet A)
    (h : ∀ e r, r.1 • e.1 ∈ A → e ∈ S ∧ r ∈ I) :
    μ A ≤ μ.toSphere S * volumeIoiPow (Module.finrank ℝ E-1) I := by
  rw [← Measure.prod_prod]
  have he : μ A = ∫⁻ z : sphere (0:E) 1 × Ioi (0:ℝ), A.indicator (fun _ => (1:ℝ≥0∞))
      (z.2.1 • z.1.1) ∂μ.toSphere.prod (volumeIoiPow (Module.finrank ℝ E-1)) := by
    rw [← Polar.lintegral_polar_prod μ,lintegral_indicator hA,lintegral_one,Measure.restrict_apply_univ]
  have hr : (μ.toSphere.prod (volumeIoiPow (Module.finrank ℝ E-1))) (S ×ˢ I) =
      ∫⁻ z, (S ×ˢ I).indicator (fun _ => (1:ℝ≥0∞)) z
        ∂μ.toSphere.prod (volumeIoiPow (Module.finrank ℝ E-1)) := by
    rw [lintegral_indicator (hS.prod hI),lintegral_one,Measure.restrict_apply_univ]
  rw [he,hr]
  apply lintegral_mono
  intro z
  by_cases hz : z.2.1 • z.1.1 ∈ A
  · have hz' : z ∈ S ×ˢ I := h z.1 z.2 hz
    simp only [indicator_of_mem hz,indicator_of_mem hz',le_refl]
  · simp only [indicator_of_notMem hz,zero_le]

omit [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E] in
lemma norm_unit (e : sphere (0:E) 1) : ‖(e:E)‖ = 1 := by
  simpa only [mem_sphere,dist_zero_right] using e.2

omit [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E] in
lemma polar_unit_distance (e θ : sphere (0:E) 1) {r : ℝ} (hr : 0 ≤ r) :
    |r-1| ≤ ‖r • (e:E) - (θ:E)‖ ∧
    dist e θ ≤ 2 * ‖r • (e:E) - (θ:E)‖ := by
  have hn : ‖r • (e:E)‖ = r := by rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hr,norm_unit,mul_one]
  have hab : |r-1| ≤ ‖r • (e:E) - (θ:E)‖ := by
    simpa only [hn,norm_unit] using abs_norm_sub_norm_le (r • (e:E)) (θ:E)
  refine ⟨hab,?_⟩
  have heq : ‖(e:E)-r • (e:E)‖ = |r-1| := by
    have hev : (e:E)-r • (e:E) = (1-r) • (e:E) := by rw [sub_smul,one_smul]
    rw [hev,norm_smul,Real.norm_eq_abs,norm_unit,mul_one,abs_sub_comm]
  have hh := dist_triangle (e:E) (r • (e:E)) (θ:E)
  simp only [dist_eq_norm] at hh
  rw [heq] at hh
  rw [Subtype.dist_eq,dist_eq_norm]
  linarith

lemma cap_lower_product (θ : sphere (0:E) 1) {l : ℝ} (hl : 0 < l) (hl1 : l ≤ 1) :
    μ (ball (θ:E) (l/4)) ≤ μ.toSphere (ball θ l) *
      ENNReal.ofReal (2^(Module.finrank ℝ E-1)*l) := by
  have ha : 0 ≤ 1-l/4 := by linarith
  have hb : 1-l/4 ≤ 1+l/4 := by linarith
  have hgeom := measure_le_polar_rectangle μ (S := ball θ l)
    (I := band (1-l/4) (1+l/4)) measurableSet_ball
    (measurable_subtype_coe measurableSet_Ioo) measurableSet_ball (A := ball (θ:E) (l/4)) (by
      intro e r hr
      have hd : ‖r.1 • (e:E)-(θ:E)‖ < l/4 := by simpa only [mem_ball,dist_eq_norm] using hr
      have hh := polar_unit_distance e θ r.2.le
      constructor
      · change dist e θ < l
        linarith [hh.2]
      · change 1-l/4 < r.1 ∧ r.1 < 1+l/4
        have har : |r.1-1| < l/4 := hh.1.trans_lt hd
        obtain ⟨hlo,hhi⟩ := abs_lt.mp har
        constructor <;> linarith)
  apply hgeom.trans
  gcongr
  apply (volumeIoiPow_band_bounds _ ha hb).2.trans
  apply ENNReal.ofReal_le_ofReal
  have hp : (1+l/4)^(Module.finrank ℝ E-1) ≤ 2^(Module.finrank ℝ E-1) :=
    pow_le_pow_left₀ (by linarith) (by linarith) _
  calc
    (1+l/4)^(Module.finrank ℝ E-1)*((1+l/4)-(1-l/4)) =
        (1+l/4)^(Module.finrank ℝ E-1)*(l/2) := by ring
    _ ≤ 2^(Module.finrank ℝ E-1)*(l/2) := by gcongr
    _ ≤ _ := by gcongr; linarith

lemma cap_upper_product (θ : sphere (0:E) 1) {l : ℝ} (hl : 0 < l) (hl1 : l ≤ 1) :
    μ.toSphere (ball θ l) * ENNReal.ofReal ((1/2:ℝ)^(Module.finrank ℝ E-1)*(l/2)) ≤
      μ (ball (θ:E) (2*l)) := by
  have ha : 0 ≤ 1-l/2 := by linarith
  have hb : 1-l/2 ≤ 1 := by linarith
  have hgeom := polar_rectangle_le μ (S := ball θ l)
    (I := band (1-l/2) 1) measurableSet_ball
    (measurable_subtype_coe measurableSet_Ioo) measurableSet_ball (A := ball (θ:E) (2*l)) (by
      intro e he r hr
      have hd : ‖(e:E)-(θ:E)‖ < l := by simpa only [mem_ball,Subtype.dist_eq,dist_eq_norm] using he
      have hr1 : r.1 < 1 := hr.2
      have hrl : 1-l/2 < r.1 := hr.1
      have heq : ‖r.1 • (e:E)-(e:E)‖ = 1-r.1 := by
        have hev : r.1 • (e:E)-(e:E) = (r.1-1) • (e:E) := by rw [sub_smul,one_smul]
        rw [hev,norm_smul,Real.norm_eq_abs,norm_unit,mul_one,abs_of_neg (by linarith)]
        ring
      have hh := dist_triangle (r.1 • (e:E)) (e:E) (θ:E)
      simp only [dist_eq_norm] at hh
      rw [heq] at hh
      rw [mem_ball,dist_eq_norm]
      linarith)
  apply le_trans _ hgeom
  gcongr
  apply le_trans _ (volumeIoiPow_band_bounds _ ha hb).1
  apply ENNReal.ofReal_le_ofReal
  have hp : (1/2:ℝ)^(Module.finrank ℝ E-1) ≤ (1-l/2)^(Module.finrank ℝ E-1) :=
    pow_le_pow_left₀ (by norm_num) (by linarith) _
  have heq : 1-(1-l/2) = l/2 := by ring
  rw [heq]
  gcongr

lemma cap_real_bounds (θ : sphere (0:E) 1) {l : ℝ} (hl : 0 < l) (hl1 : l ≤ 1) :
    (μ (ball (0:E) 1)).toReal / (4^Module.finrank ℝ E * 2^(Module.finrank ℝ E-1)) *
        l^(Module.finrank ℝ E-1) ≤ (μ.toSphere (ball θ l)).toReal ∧
    (μ.toSphere (ball θ l)).toReal ≤
      4^Module.finrank ℝ E * (μ (ball (0:E) 1)).toReal * l^(Module.finrank ℝ E-1) := by
  have hn : Module.finrank ℝ E-1+1 = Module.finrank ℝ E :=
    Nat.sub_add_cancel (Module.finrank_pos : 0 < Module.finrank ℝ E)
  have hbf : μ (ball (0:E) 1) ≠ ⊤ := (isBounded_ball.measure_lt_top (μ := μ)).ne
  have hcf : μ.toSphere (ball θ l) ≠ ⊤ := measure_ne_top _ _
  have hlo := cap_lower_product μ θ hl hl1
  rw [μ.addHaar_ball _ (by positivity)] at hlo
  have hlor := ENNReal.toReal_mono (ENNReal.mul_ne_top hcf ENNReal.ofReal_ne_top) hlo
  simp only [ENNReal.toReal_mul,ENNReal.toReal_ofReal (show 0 ≤ (l/4)^Module.finrank ℝ E by positivity),
    ENNReal.toReal_ofReal (show 0 ≤ (2:ℝ)^(Module.finrank ℝ E-1)*l by positivity)] at hlor
  have hhi := cap_upper_product μ θ hl hl1
  rw [μ.addHaar_ball _ (by positivity)] at hhi
  have hhir := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hbf) hhi
  simp only [ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (show 0 ≤ (2*l)^Module.finrank ℝ E by positivity),
    ENNReal.toReal_ofReal (show 0 ≤ (1/2:ℝ)^(Module.finrank ℝ E-1)*(l/2) by positivity)] at hhir
  have hlpow : l^Module.finrank ℝ E = l^(Module.finrank ℝ E-1)*l := by
    nth_rw 1 [← hn]; rw [pow_succ]
  have h2pow : (2:ℝ)^Module.finrank ℝ E = 2^(Module.finrank ℝ E-1)*2 := by
    nth_rw 1 [← hn]; rw [pow_succ]
  have h4pow : (4:ℝ)^Module.finrank ℝ E = (2^Module.finrank ℝ E)^2 := by
    rw [← pow_mul, mul_comm _ 2,pow_mul]; norm_num
  constructor
  · rw [div_pow,hlpow] at hlor
    have h4 : (0:ℝ) < 4^Module.finrank ℝ E := by positivity
    have h2 : (0:ℝ) < 2^(Module.finrank ℝ E-1) := by positivity
    have hs : (μ (ball (0:E) 1)).toReal * l^(Module.finrank ℝ E-1) * l ≤
        (μ.toSphere (ball θ l)).toReal * (2^(Module.finrank ℝ E-1)*l) * 4^Module.finrank ℝ E := by
      apply (div_le_iff₀ h4).mp
      simpa only [div_mul_eq_mul_div,mul_comm,mul_left_comm,mul_assoc] using hlor
    have hh : (μ (ball (0:E) 1)).toReal * l^(Module.finrank ℝ E-1) ≤
        (μ.toSphere (ball θ l)).toReal * (4^Module.finrank ℝ E * 2^(Module.finrank ℝ E-1)) := by
      apply (mul_le_mul_iff_left₀ hl).mp
      simpa only [mul_comm,mul_left_comm,mul_assoc] using hs
    calc
      _ = ((μ (ball (0:E) 1)).toReal * l^(Module.finrank ℝ E-1)) /
          (4^Module.finrank ℝ E * 2^(Module.finrank ℝ E-1)) := by ring
      _ ≤ _ := (div_le_iff₀ (mul_pos h4 h2)).mpr hh
  · apply (mul_le_mul_iff_left₀ (show 0 < (1/2:ℝ)^(Module.finrank ℝ E-1)*(l/2) by positivity)).mp
    calc
      _ ≤ (2*l)^Module.finrank ℝ E * (μ (ball (0:E) 1)).toReal := hhir
      _ = (4^Module.finrank ℝ E * (μ (ball (0:E) 1)).toReal * l^(Module.finrank ℝ E-1)) *
          ((1/2:ℝ)^(Module.finrank ℝ E-1)*(l/2)) := by
        rw [mul_pow,hlpow,h4pow,h2pow,div_pow]
        field_simp
        ring

omit [BorelSpace E] [Nontrivial E] in
lemma cap_constants_pos :
    0 < (μ (ball (0:E) 1)).toReal / (4^Module.finrank ℝ E * 2^(Module.finrank ℝ E-1)) ∧
    0 < (4:ℝ)^Module.finrank ℝ E * (μ (ball (0:E) 1)).toReal := by
  have hp : 0 < (μ (ball (0:E) 1)).toReal :=
    ENNReal.toReal_pos (ne_of_gt (Metric.measure_ball_pos μ 0 (by norm_num)))
      (isBounded_ball.measure_lt_top (μ := μ)).ne
  constructor <;> positivity

end HenonLaneEmden.CapGeometry
end
end CapGeometry

end OAI
end

section
-- module Solutions.OAIQW_HenonLaneEmden.CapWeights
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uT

section CapWeights

open MeasureTheory Set Metric
open scoped ENNReal
noncomputable section
namespace HenonLaneEmden.CapWeights

variable {T : Type uT} [MetricSpace T]

lemma profile_nonneg (θ : T) (l : ℝ) (e : T) : 0 ≤ profile θ l e := le_max_right _ _
lemma profile_le_one (θ : T) {l : ℝ} (hl : 0 < l) (e : T) : profile θ l e ≤ 1 := by
  unfold profile
  apply max_le _ (by norm_num)
  linarith [div_nonneg (dist_nonneg (x := e) (y := θ)) hl.le]
lemma profile_eq_zero {θ e : T} {l : ℝ} (hl : 0 < l) (he : e ∉ ball θ l) :
    profile θ l e = 0 := by
  unfold profile
  apply max_eq_right
  have hh : l ≤ dist e θ := not_lt.mp he
  have hr : 1 ≤ dist e θ/l := (le_div_iff₀ hl).mpr (by simpa using hh)
  linarith
lemma profile_half {θ e : T} {l : ℝ} (hl : 0 < l) (he : e ∈ ball θ (l/2)) :
    1/2 ≤ profile θ l e := by
  apply le_trans _ (le_max_left _ _)
  have hh : dist e θ/l < 1/2 := (div_lt_iff₀ hl).mpr (by simpa [div_eq_mul_inv,mul_comm] using he)
  linarith
lemma continuous_profile (θ : T) (l : ℝ) : Continuous (profile θ l) := by
  unfold profile
  fun_prop

lemma profile_as_div (θ : T) {l : ℝ} (hl : 0 < l) (e : T) :
    profile θ l e = max (l-dist e θ) 0/l := by
  unfold profile
  rw [← max_div_div_right hl.le,zero_div]
  congr 1
  field_simp [ne_of_gt hl]

lemma profile_center_oscillation {θ θ' e : T} {l : ℝ} (hl : 0 < l) :
    |profile θ l e-profile θ' l e| ≤ dist θ θ'/l := by
  unfold profile
  calc
    _ ≤ |(1-dist e θ/l)-(1-dist e θ'/l)| := abs_max_sub_max_le_abs _ _ _
    _ = |dist e θ-dist e θ'|/l := by
      rw [show (1-dist e θ/l)-(1-dist e θ'/l) = -(dist e θ-dist e θ')/l by ring,
        abs_div,abs_neg,abs_of_pos hl]
    _ ≤ _ := div_le_div_of_nonneg_right (by simpa only [dist_comm e] using abs_dist_sub_le θ θ' e) hl.le

lemma profile_radial_oscillation {θ e : T} {l l' : ℝ} (hl : 0 < l) (hl' : 0 < l') :
    |profile θ l e-profile θ l' e| ≤ 2*|l-l'|/l := by
  let a := max (l-dist e θ) 0
  let b := max (l'-dist e θ) 0
  have hab : |a-b| ≤ |l-l'| := by
    simpa only [sub_sub_sub_cancel_right] using abs_max_sub_max_le_abs (l-dist e θ) (l'-dist e θ) 0
  have heq : profile θ l e-profile θ l' e = (a-b)/l+(l'-l)/l*profile θ l' e := by
    rw [profile_as_div _ hl,profile_as_div _ hl']
    dsimp [a,b]
    field_simp [ne_of_gt hl,ne_of_gt hl']
    ring
  rw [heq]
  calc
    _ ≤ |(a-b)/l|+|(l'-l)/l*profile θ l' e| := abs_add_le _ _
    _ = |a-b|/l+|l-l'|/l*profile θ l' e := by
      rw [abs_mul,abs_div,abs_div,abs_of_pos hl,abs_sub_comm l',
        abs_of_nonneg (profile_nonneg _ _ _)]
    _ ≤ |l-l'|/l+|l-l'|/l*1 := by
      gcongr
      exact profile_le_one _ hl' _
    _ = _ := by ring

lemma profile_oscillation {θ θ' e : T} {l l' : ℝ} (hl : 0 < l) (hl' : 0 < l') :
    |profile θ l e-profile θ' l' e| ≤ (dist θ θ'+2*|l-l'|)/l := by
  calc
    _ ≤ |profile θ l e-profile θ' l e|+|profile θ' l e-profile θ' l' e| := abs_sub_le _ _ _
    _ ≤ dist θ θ'/l+2*|l-l'|/l := add_le_add (profile_center_oscillation hl) (profile_radial_oscillation hl hl')
    _ = _ := by ring

variable [MeasurableSpace T] [BorelSpace T] (σ : Measure T) [IsFiniteMeasure σ] [CompactSpace T]

lemma integrable_profile (θ : T) (l : ℝ) : Integrable (profile θ l) σ := by
  have hh := (continuous_profile θ l).continuousOn.integrableOn_compact (μ := σ) isCompact_univ
  simpa only [integrableOn_univ] using hh

omit [BorelSpace T] [IsFiniteMeasure σ] [CompactSpace T] in
lemma normalizer_nonneg (θ : T) (l : ℝ) : 0 ≤ normalizer σ θ l :=
  integral_nonneg (profile_nonneg θ l)

lemma normalizer_bounds (θ : T) {l : ℝ} (hl : 0 < l) :
    (σ (ball θ (l/2))).toReal/2 ≤ normalizer σ θ l ∧
    normalizer σ θ l ≤ (σ (ball θ l)).toReal := by
  have hlo (e : T) : (ball θ (l/2)).indicator (fun _ => (1/2:ℝ)) e ≤ profile θ l e := by
    by_cases he : e ∈ ball θ (l/2)
    · rw [indicator_of_mem he]; exact profile_half hl he
    · rw [indicator_of_notMem he]; exact profile_nonneg _ _ _
  have hhi (e : T) : profile θ l e ≤ (ball θ l).indicator (fun _ => (1:ℝ)) e := by
    by_cases he : e ∈ ball θ l
    · rw [indicator_of_mem he]; exact profile_le_one _ hl _
    · rw [indicator_of_notMem he,profile_eq_zero hl he]
  constructor
  · have hh := integral_mono ((integrable_const (1/2:ℝ)).indicator measurableSet_ball)
      (integrable_profile σ θ l) hlo
    simpa only [integral_indicator measurableSet_ball,integral_const,Measure.real,Measure.restrict_apply_univ,
      smul_eq_mul,one_mul,div_eq_mul_inv,normalizer] using hh
  · have hh := integral_mono (integrable_profile σ θ l)
      ((integrable_const (1:ℝ)).indicator measurableSet_ball) hhi
    simpa only [integral_indicator measurableSet_ball,integral_const,Measure.real,Measure.restrict_apply_univ,
      smul_eq_mul,one_mul,mul_one,normalizer] using hh

omit [BorelSpace T] [IsFiniteMeasure σ] [CompactSpace T] in
lemma integral_normalized {θ : T} {l : ℝ} (hZ : normalizer σ θ l ≠ 0) :
    (∫ e, normalized σ θ l e ∂σ) = 1 := by
  unfold normalized
  rw [integral_div,← normalizer,div_self hZ]

omit [BorelSpace T] [IsFiniteMeasure σ] [CompactSpace T] in
lemma normalized_nonneg (θ : T) (l : ℝ) (e : T) : 0 ≤ normalized σ θ l e :=
  div_nonneg (profile_nonneg _ _ _) (normalizer_nonneg σ _ _)

omit [BorelSpace T] [IsFiniteMeasure σ] [CompactSpace T] in
lemma normalized_le_inv (θ : T) {l : ℝ} (hl : 0 < l) (e : T) :
    normalized σ θ l e ≤ (normalizer σ θ l)⁻¹ := by
  simpa only [one_div,normalized] using div_le_div_of_nonneg_right (profile_le_one θ hl e)
    (normalizer_nonneg σ θ l)

lemma normalizer_oscillation {θ θ' : T} {l l' : ℝ} (hl : 0 < l) (hl' : 0 < l')
    {Q : ℝ} (hQ : (dist θ θ'+2*|l-l'|)/l ≤ Q) :
    |normalizer σ θ l-normalizer σ θ' l'| ≤
      Q*((σ (ball θ l)).toReal+(σ (ball θ' l')).toReal) := by
  have hQ0 : 0 ≤ Q := (div_nonneg (by positivity) hl.le).trans hQ
  let F := (ball θ l).indicator (fun _ => Q)
  let G := (ball θ' l').indicator (fun _ => Q)
  have hF : Integrable F σ := (integrable_const Q).indicator measurableSet_ball
  have hG : Integrable G σ := (integrable_const Q).indicator measurableSet_ball
  have hpt (e : T) : |profile θ l e-profile θ' l' e| ≤ F e+G e := by
    have hh := (profile_oscillation (θ := θ) (θ' := θ') (e := e) hl hl').trans hQ
    by_cases he : e ∈ ball θ l <;> by_cases he' : e ∈ ball θ' l'
    · simp only [F,G,indicator_of_mem he,indicator_of_mem he']; linarith
    · simpa only [F,G,indicator_of_mem he,indicator_of_notMem he',add_zero] using hh
    · simpa only [F,G,indicator_of_notMem he,indicator_of_mem he',zero_add] using hh
    · simp only [F,G,indicator_of_notMem he,indicator_of_notMem he',
        profile_eq_zero hl he,profile_eq_zero hl' he',sub_self,abs_zero,add_zero,le_refl]
  calc
    _ = |∫ e, profile θ l e-profile θ' l' e ∂σ| := by
      rw [integral_sub (integrable_profile σ _ _) (integrable_profile σ _ _)]; rfl
    _ ≤ ∫ e, |profile θ l e-profile θ' l' e| ∂σ := abs_integral_le_integral_abs
    _ ≤ ∫ e, F e+G e ∂σ := integral_mono
      ((integrable_profile σ _ _).sub (integrable_profile σ _ _)).abs (hF.add hG) hpt
    _ = _ := by
      rw [integral_add hF hG]
      simp only [F,G,integral_indicator measurableSet_ball,integral_const,Measure.real,
        Measure.restrict_apply_univ,smul_eq_mul]
      ring

lemma normalized_oscillation {θ θ' : T} {l l' L U Q : ℝ}
    (hl : 0 < l) (hl' : 0 < l') (hL : 0 < L)
    (hZ : L ≤ normalizer σ θ l) (hZ' : L ≤ normalizer σ θ' l')
    (hU : (σ (ball θ l)).toReal+(σ (ball θ' l')).toReal ≤ U)
    (hQ : (dist θ θ'+2*|l-l'|)/l ≤ Q) (e : T) :
    |normalized σ θ l e-normalized σ θ' l' e| ≤ (1/L+U/L^2)*Q := by
  have hQ0 : 0 ≤ Q := (div_nonneg (by positivity) hl.le).trans hQ
  have hU0 : 0 ≤ U := (add_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg).trans hU
  have hp := (profile_oscillation (θ := θ) (θ' := θ') (e := e) hl hl').trans hQ
  have hz := (normalizer_oscillation σ hl hl' hQ).trans (mul_le_mul_of_nonneg_left hU hQ0)
  have hz0 : 0 < normalizer σ θ l := hL.trans_le hZ
  have hz0' : 0 < normalizer σ θ' l' := hL.trans_le hZ'
  have he : normalized σ θ l e-normalized σ θ' l' e =
      (profile θ l e-profile θ' l' e)/normalizer σ θ l +
      profile θ' l' e*(normalizer σ θ' l'-normalizer σ θ l)/
        (normalizer σ θ l*normalizer σ θ' l') := by
    unfold normalized
    field_simp [ne_of_gt hz0,ne_of_gt hz0']
    ring
  rw [he]
  calc
    _ ≤ |(profile θ l e-profile θ' l' e)/normalizer σ θ l|+
        |profile θ' l' e*(normalizer σ θ' l'-normalizer σ θ l)/(normalizer σ θ l*normalizer σ θ' l')| := abs_add_le _ _
    _ = |profile θ l e-profile θ' l' e|/normalizer σ θ l+
        profile θ' l' e*|normalizer σ θ l-normalizer σ θ' l'|/
          (normalizer σ θ l*normalizer σ θ' l') := by
      rw [abs_div,abs_div,abs_mul,abs_of_pos hz0,abs_of_pos (mul_pos hz0 hz0'),
        abs_of_nonneg (profile_nonneg _ _ _),abs_sub_comm (normalizer σ θ' l')]
    _ ≤ Q/L+1*(Q*U)/(L*L) := by
      gcongr
      exact profile_le_one _ hl' _
    _ = _ := by ring

end HenonLaneEmden.CapWeights
end
end CapWeights

end OAI
end

section
-- module Solutions.OAIQW_HenonLaneEmden.SphereCaps
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE

section SphereCaps

open MeasureTheory Set Metric
open scoped ENNReal
noncomputable section
namespace HenonLaneEmden.CapWeights

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]
  (μ : Measure E) [μ.IsAddHaarMeasure]

omit [BorelSpace E] [Nontrivial E] in
lemma constants_positive : 0 < lowerConstant μ ∧ 0 < upperConstant μ := by
  obtain ⟨hc,hC⟩ := CapGeometry.cap_constants_pos μ
  exact ⟨div_pos hc (by positivity),hC⟩

lemma sphere_normalizer_bounds (θ : sphere (0:E) 1) {l : ℝ} (hl : 0 < l) (hl1 : l ≤ 1) :
    lowerConstant μ*l^(Module.finrank ℝ E-1) ≤ normalizer μ.toSphere θ l ∧
    normalizer μ.toSphere θ l ≤ upperConstant μ*l^(Module.finrank ℝ E-1) := by
  have hb := normalizer_bounds μ.toSphere θ hl
  have hlo := (CapGeometry.cap_real_bounds μ θ (by linarith : 0 < l/2) (by linarith : l/2 ≤ 1)).1
  have hhi := (CapGeometry.cap_real_bounds μ θ hl hl1).2
  refine ⟨?_,hb.2.trans hhi⟩
  have hn : Module.finrank ℝ E-1+1 = Module.finrank ℝ E :=
    Nat.sub_add_cancel (Module.finrank_pos : 0 < Module.finrank ℝ E)
  apply le_trans _ hb.1
  convert div_le_div_of_nonneg_right hlo (by norm_num : (0:ℝ) ≤ 2) using 1
  unfold lowerConstant
  have h2 : (2:ℝ)^Module.finrank ℝ E = 2^(Module.finrank ℝ E-1)*2 := by
    nth_rw 1 [← hn]; rw [pow_succ]
  rw [div_pow,h2]
  ring

lemma sphere_normalizer_pos (θ : sphere (0:E) 1) {l : ℝ} (hl : 0 < l) (hl1 : l ≤ 1) :
    0 < normalizer μ.toSphere θ l :=
  (mul_pos (constants_positive μ).1 (pow_pos hl _)).trans_le (sphere_normalizer_bounds μ θ hl hl1).1

/-- Oscillation of a normalized cap with comparable radii, uniformly in directions. -/
lemma sphere_normalized_oscillation
    {θ θ' : sphere (0:E) 1} {l l' ρ : ℝ} (hρ : 0 < ρ)
    (hl : ρ/2 ≤ l) (hl' : ρ/2 ≤ l') (hlU : l ≤ 2*ρ) (hlU' : l' ≤ 2*ρ)
    (hl1 : l ≤ 1) (hl1' : l' ≤ 1) (e : sphere (0:E) 1) :
    |normalized μ.toSphere θ l e-normalized μ.toSphere θ' l' e| ≤
      (2/(lowerConstant μ/2^(Module.finrank ℝ E-1))+
        2*(2^(Module.finrank ℝ E)*upperConstant μ)/(lowerConstant μ/2^(Module.finrank ℝ E-1))^2)*
      (dist θ θ'+2*|l-l'|)/ρ^(Module.finrank ℝ E) := by
  let d := Module.finrank ℝ E-1
  let c := lowerConstant μ/2^d
  let C := 2^(Module.finrank ℝ E)*upperConstant μ
  have hc : 0 < c := div_pos (constants_positive μ).1 (by positivity)
  have hC : 0 < C := mul_pos (by positivity) (constants_positive μ).2
  have hl0 : 0 < l := (half_pos hρ).trans_le hl
  have hl0' : 0 < l' := (half_pos hρ).trans_le hl'
  have hZ (θ : sphere (0:E) 1) {l : ℝ} (hl : ρ/2 ≤ l) (hl1 : l ≤ 1) :
      c*ρ^d ≤ normalizer μ.toSphere θ l := by
    apply le_trans _ (sphere_normalizer_bounds μ θ ((half_pos hρ).trans_le hl) hl1).1
    calc
      _ = lowerConstant μ*(ρ/2)^d := by rw [div_pow]; dsimp [c]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (half_pos hρ).le hl d) (constants_positive μ).1.le
  have hmu (θ : sphere (0:E) 1) {l : ℝ} (hl0 : 0 < l) (hlU : l ≤ 2*ρ) (hl1 : l ≤ 1) :
      (μ.toSphere (ball θ l)).toReal ≤ upperConstant μ*(2*ρ)^d := by
    exact (CapGeometry.cap_real_bounds μ θ hl0 hl1).2.trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hl0.le hlU d) (constants_positive μ).2.le)
  have hμ : (μ.toSphere (ball θ l)).toReal+(μ.toSphere (ball θ' l')).toReal ≤ C*ρ^d := by
    apply le_trans (add_le_add (hmu θ hl0 hlU hl1) (hmu θ' hl0' hlU' hl1'))
    have hn : d+1 = Module.finrank ℝ E := Nat.sub_add_cancel (Module.finrank_pos : 0 < Module.finrank ℝ E)
    apply le_of_eq
    dsimp [C]
    rw [← hn,pow_succ,mul_pow]
    ring
  have hparam : (dist θ θ'+2*|l-l'|)/l ≤ 2*(dist θ θ'+2*|l-l'|)/ρ := by
    calc
      _ ≤ (dist θ θ'+2*|l-l'|)/(ρ/2) := div_le_div_of_nonneg_left (by positivity) (half_pos hρ) hl
      _ = _ := by ring
  have hh := normalized_oscillation μ.toSphere hl0 hl0' (mul_pos hc (pow_pos hρ d))
    (hZ θ hl hl1) (hZ θ' hl' hl1') hμ hparam e
  apply hh.trans
  have hn : d+1 = Module.finrank ℝ E := Nat.sub_add_cancel (Module.finrank_pos : 0 < Module.finrank ℝ E)
  apply le_of_eq
  change (1/(c*ρ^d)+C*ρ^d/(c*ρ^d)^2)*(2*(dist θ θ'+2*|l-l'|)/ρ) =
    (2/c+2*C/c^2)*(dist θ θ'+2*|l-l'|)/ρ^(Module.finrank ℝ E)
  rw [← hn,pow_succ]
  field_simp [ne_of_gt hc,ne_of_gt hρ]
  ring

end HenonLaneEmden.CapWeights
end
end SphereCaps

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

lemma hasDerivAt_wProfile {n : ℕ} (hn : 1 ≤ n) (r : ℝ) :
    HasDerivAt (wProfile n) (wDerivativeProfile n r) r := by
  exact ((hasDerivAt_id r).neg.mul (hasDerivAt_derivativeProfile hn r)).congr_deriv (by
    simp only [wDerivativeProfile,Pi.neg_apply,id_eq]; ring)

lemma constants_nonneg (n : ℕ) : 0 ≤ derivativeConstant n ∧ 0 ≤ secondConstant n ∧ 0 ≤ wDerivativeConstant n := by
  have hn : (0:ℝ) ≤ N n-1 := by
    have : (2:ℝ) ≤ N n := by exact_mod_cast N_ge_two n
    linarith
  dsimp [derivativeConstant,secondConstant,wDerivativeConstant]
  constructor
  · positivity
  constructor <;> positivity

lemma wDerivativeProfile_bound {n : ℕ} (hn : 1 ≤ n) {r : ℝ} (hr : 0 ≤ r) :
    |wDerivativeProfile n r| ≤ wDerivativeConstant n*(gapProfile r)^(N n-2) := by
  have hN := N_ge_three hn
  have hc := constants_nonneg n
  have hg := gapProfile_nonneg r
  by_cases h2 : 2 ≤ r
  · simp only [wDerivativeProfile,derivativeProfile_outer n h2,secondProfile_outer hn h2,
      neg_zero,mul_zero,sub_zero,abs_zero]
    exact mul_nonneg hc.2.2 (pow_nonneg hg _)
  have hp := pow_le_pow_of_le_one hg (gapProfile_le_one r) (by omega : N n-2 ≤ N n-1)
  calc
    _ ≤ |derivativeProfile n r|+r*|secondProfile n r| := by
      unfold wDerivativeProfile
      simpa only [sub_zero,zero_sub,abs_neg,abs_mul,abs_of_nonneg hr] using abs_sub_le (-derivativeProfile n r) 0 (r*secondProfile n r)
    _ ≤ derivativeConstant n*(gapProfile r)^(N n-2)+
        2*(secondConstant n*(gapProfile r)^(N n-2)) := by
      apply add_le_add
      · exact (derivativeProfile_bound n r).trans (mul_le_mul_of_nonneg_left hp hc.1)
      · apply mul_le_mul (by linarith) (secondProfile_bound hn r) (abs_nonneg _) (by norm_num)
    _ = _ := by unfold wDerivativeConstant; ring

lemma wProfile_oscillation {n : ℕ} (hn : 1 ≤ n) {r s D : ℝ} (_hD : 0 ≤ D)
    (hseg : ∀ t ∈ uIcc r s, 0 ≤ t ∧ gapProfile t ≤ D) :
    |wProfile n s-wProfile n r| ≤ wDerivativeConstant n*D^(N n-2)*|s-r| := by
  have hh := (convex_uIcc r s).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun t _ => (hasDerivAt_wProfile hn t).hasDerivWithinAt)
    (show ∀ t ∈ uIcc r s, ‖wDerivativeProfile n t‖ ≤ wDerivativeConstant n*D^(N n-2) from by
      intro t ht
      rw [Real.norm_eq_abs]
      exact (wDerivativeProfile_bound hn (hseg t ht).1).trans
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (gapProfile_nonneg t) (hseg t ht).2 _) (constants_nonneg n).2.2))
    left_mem_uIcc right_mem_uIcc
  simpa only [Real.norm_eq_abs] using hh

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

omit [InnerProductSpace ℝ E] in
lemma continuous_d : Continuous (d : E → ℝ) := continuous_gapProfile.comp continuous_norm
omit [InnerProductSpace ℝ E] in
lemma eta_eq_one {n : ℕ} {x : E} (hx : ‖x‖ ≤ 1) : eta n x = 1 := by
  simp [eta,etaProfile,posPow,max_eq_right (by linarith : ‖x‖-1 ≤ 0)]

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

variable [InnerProductSpace ℝ E]
lemma w_oscillation {n : ℕ} (hn : 1 ≤ n) {x y : E} {D : ℝ} (hD : 0 ≤ D)
    (hxy : d x+dist x y ≤ D) :
    |w n y-w n x| ≤ wDerivativeConstant n*D^(N n-2)*dist x y := by
  rw [w_eq_profile,w_eq_profile]
  have hh := wProfile_oscillation hn hD (fun _ ht => norm_segment_gap hxy ht)
  have hn' : |‖y‖-‖x‖| ≤ dist x y := by
    simpa only [dist_comm x y,dist_eq_norm] using abs_norm_sub_norm_le y x
  exact hh.trans (mul_le_mul_of_nonneg_left hn' (mul_nonneg (constants_nonneg n).2.2 (pow_nonneg hD _)))

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
omit [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E] [μ.IsAddHaarMeasure] in
lemma weight_nonneg (κ : ℝ) (e : sphere (0:E) 1) (x : E) : 0 ≤ weight μ κ e x := by
  unfold weight
  split_ifs
  · exact mul_nonneg (w_nonneg _ _) (normalized_nonneg _ _ _ _)
  · rfl
omit [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E] [μ.IsAddHaarMeasure] in
lemma weight_inner (κ : ℝ) (e : sphere (0:E) 1) {x : E} (hx : ‖x‖ ≤ 1) :
    weight μ κ e x = 0 := by
  unfold weight
  split_ifs <;> simp [w_inner _ hx]
omit [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E] [μ.IsAddHaarMeasure] in
lemma weight_outer (κ : ℝ) (e : sphere (0:E) 1) {x : E} (hx : 2 ≤ ‖x‖) :
    weight μ κ e x = 0 := by
  unfold weight
  split_ifs <;> simp [w_outer _ hx]

lemma integral_weight {κ : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1) (x : E) :
    (∫ e, weight μ κ e x ∂μ.toSphere) = w (Module.finrank ℝ E) x := by
  by_cases hx : x ≠ 0 ∧ 0 < d x
  · simp only [weight,dite_eq_left hx,integral_const_mul]
    rw [integral_normalized _ (ne_of_gt (sphere_normalizer_pos μ _ (mul_pos hκ hx.2)
      ((mul_le_of_le_one_left (d_nonneg x) hκ1).trans (d_le_one x)))),mul_one]
  · have hw : w (Module.finrank ℝ E) x = 0 := by
      by_cases hx0 : x = 0
      · subst x; exact w_inner _ (by simp)
      · exact w_outer _ (not_lt.mp (fun hh => hx ⟨hx0,(d_pos_iff x).mpr hh⟩))
    simp only [weight,dite_eq_right hx,integral_zero,hw]

omit [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E] in
lemma normalize_dist_le {x y : E} (hx : 1/2 ≤ ‖x‖) (hy : 1/2 ≤ ‖y‖) :
    dist (NormedSpace.normalize x) (NormedSpace.normalize y) ≤ 4*dist x y := by
  have hx0 : ‖x‖ ≠ 0 := ne_of_gt (by linarith)
  have hy0 : y ≠ 0 := norm_ne_zero_iff.mp (ne_of_gt (by linarith : 0 < ‖y‖))
  have he : NormedSpace.normalize x-NormedSpace.normalize y =
      ‖x‖⁻¹ • (x-y) + ((‖y‖-‖x‖)/‖x‖) • NormedSpace.normalize y := by
    rw [NormedSpace.normalize,NormedSpace.normalize,smul_sub,smul_smul]
    have hr : (‖y‖-‖x‖)/‖x‖*‖y‖⁻¹ = ‖x‖⁻¹-‖y‖⁻¹ := by
      field_simp [hx0,norm_ne_zero_iff.mpr hy0]
    rw [hr,sub_smul]
    abel
  rw [dist_eq_norm,he]
  calc
    _ ≤ ‖‖x‖⁻¹ • (x-y)‖+‖((‖y‖-‖x‖)/‖x‖) • NormedSpace.normalize y‖ := norm_add_le _ _
    _ = (dist x y+|‖y‖-‖x‖|)/‖x‖ := by
      rw [norm_smul,norm_smul,NormedSpace.norm_normalize hy0,mul_one,Real.norm_eq_abs,
        Real.norm_eq_abs,abs_inv,abs_of_nonneg (norm_nonneg x),abs_div,
        abs_of_nonneg (norm_nonneg x),← dist_eq_norm]
      ring
    _ ≤ (dist x y+dist x y)/‖x‖ := by
      apply div_le_div_of_nonneg_right _ (norm_nonneg x)
      gcongr
      simpa only [dist_comm x y,dist_eq_norm] using abs_norm_sub_norm_le y x
    _ ≤ (dist x y+dist x y)/(1/2) := div_le_div_of_nonneg_left (by positivity) (by norm_num) hx
    _ = _ := by ring

omit [BorelSpace E] [Nontrivial E] in
lemma boundConstant_nonneg {κ : ℝ} (hκ : 0 ≤ κ) : 0 ≤ boundConstant μ κ := by
  unfold boundConstant
  exact div_nonneg (by positivity) (mul_nonneg (constants_positive μ).1.le (pow_nonneg hκ _))

lemma weight_bound {κ : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1) (e : sphere (0:E) 1) (x : E) :
    weight μ κ e x ≤ boundConstant μ κ * (d x)^(N (Module.finrank ℝ E)-Module.finrank ℝ E) := by
  let n := Module.finrank ℝ E
  have hn : 1 ≤ n := Module.finrank_pos
  by_cases hx : x ≠ 0 ∧ 0 < d x
  · rw [weight,dite_eq_left hx]
    have hrad : κ*d x ≤ 1 := (mul_le_of_le_one_left (d_nonneg x) hκ1).trans (d_le_one x)
    have hb := (sphere_normalizer_bounds μ (direction x hx.1) (mul_pos hκ hx.2) hrad).1
    have hc : 0 < lowerConstant μ*κ^(n-1) := mul_pos (constants_positive μ).1 (pow_pos hκ _)
    have hpow : n-1+(N n-n) = N n-1 := by dsimp [N]; omega
    calc
      _ ≤ (6*(N n:ℝ)*3^(N n-1)*(d x)^(N n-1)) *
          (1/(lowerConstant μ*(κ*d x)^(n-1))) := by
        apply mul_le_mul
        · rw [w_eq_profile]; exact wProfile_bound n (norm_nonneg x)
        · exact (normalized_le_inv μ.toSphere _ (mul_pos hκ hx.2) e).trans
            (by simpa only [one_div] using one_div_le_one_div_of_le (mul_pos (constants_positive μ).1 (pow_pos (mul_pos hκ hx.2) _)) hb)
        · exact normalized_nonneg _ _ _ _
        · exact mul_nonneg (by positivity) (pow_nonneg (d_nonneg x) _)
      _ = _ := by
        have hdPow : (d x)^(N n-1) = (d x)^(n-1)*(d x)^(N n-n) := by rw [← hpow,pow_add]
        rw [hdPow,mul_pow]
        unfold boundConstant
        change _ = (6*(N n:ℝ)*3^(N n-1))/(lowerConstant μ*κ^(n-1))*(d x)^(N n-n)
        field_simp [ne_of_gt (constants_positive μ).1,ne_of_gt hκ,ne_of_gt hx.2]
  · rw [weight,dite_eq_right hx]
    exact mul_nonneg (boundConstant_nonneg μ hκ.le) (pow_nonneg (d_nonneg x) _)

end HenonLaneEmden.AdaptiveCap
end
end AdaptiveCaps

end OAI
end

section
-- module Solutions.OAIQW_HenonLaneEmden.CapOscillation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE

section CapOscillation

open MeasureTheory Set Metric
noncomputable section
namespace HenonLaneEmden.AdaptiveCap
open Cutoff CapWeights
variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]
  (μ : Measure E) [μ.IsAddHaarMeasure]

omit [BorelSpace E] [Nontrivial E] in
lemma oscillationConstant_nonneg {κ : ℝ} (hκ : 0 ≤ κ) : 0 ≤ oscillationConstant μ κ := by
  obtain ⟨hc,hC⟩ := constants_positive μ
  have hd := (constants_nonneg (Module.finrank ℝ E)).2.2
  dsimp [oscillationConstant,normalizedOscConstant]
  positivity

lemma normalized_close_oscillation {κ : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1)
    {x y : E} (hx : x ≠ 0) (hy : y ≠ 0) (hd : 0 < d x)
    (hxy : dist x y ≤ d x/2) (hnx : 1/2 ≤ ‖x‖) (hny : 1/2 ≤ ‖y‖)
    (e : sphere (0:E) 1) :
    |normalized μ.toSphere (direction x hx) (κ*d x) e-
        normalized μ.toSphere (direction y hy) (κ*d y) e| ≤
      normalizedOscConstant μ*6*dist x y/(κ*d x)^(Module.finrank ℝ E) := by
  have hg := abs_le.mp (d_oscillation x y)
  have hcomp : d x/2 ≤ d y ∧ d y ≤ 2*d x := by constructor <;> linarith
  have hr := sphere_normalized_oscillation μ (mul_pos hκ hd)
    (l := κ*d x) (l' := κ*d y) (by nlinarith [mul_pos hκ hd])
    (by nlinarith [mul_le_mul_of_nonneg_left hcomp.1 hκ.le])
    (by nlinarith [mul_pos hκ hd])
    (by nlinarith [mul_le_mul_of_nonneg_left hcomp.2 hκ.le])
    ((mul_le_of_le_one_left (d_nonneg x) hκ1).trans (d_le_one x))
    ((mul_le_of_le_one_left (d_nonneg y) hκ1).trans (d_le_one y)) e
    (θ := direction x hx) (θ' := direction y hy)
  change _ ≤ normalizedOscConstant μ*(dist (direction x hx) (direction y hy)+2*|κ*d x-κ*d y|)/(κ*d x)^Module.finrank ℝ E at hr
  apply hr.trans
  apply div_le_div_of_nonneg_right _ (pow_nonneg (mul_pos hκ hd).le _)
  have hc : 0 ≤ normalizedOscConstant μ := by
    obtain ⟨hc,hC⟩ := constants_positive μ; unfold normalizedOscConstant; positivity
  have hdir : dist (direction x hx) (direction y hy) ≤ 4*dist x y := normalize_dist_le hnx hny
  have hrad : |κ*d x-κ*d y| ≤ dist x y := by
    rw [← mul_sub,abs_mul,abs_of_pos hκ]
    exact (mul_le_mul_of_nonneg_left (d_oscillation x y) hκ.le).trans
      (by nlinarith [dist_nonneg (x := x) (y := y)])
  nlinarith

lemma weight_close_oscillation {κ : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1)
    {x y : E} (hd : 0 < d x) (hxy : dist x y ≤ d x/2) (e : sphere (0:E) 1) :
    |weight μ κ e x-weight μ κ e y| ≤
      oscillationConstant μ κ*(d x)^(N (Module.finrank ℝ E)-Module.finrank ℝ E-1)*dist x y := by
  let n := Module.finrank ℝ E
  have hn : 1 ≤ n := Module.finrank_pos
  have hc := constants_positive μ
  have hg := abs_le.mp (d_oscillation x y)
  have hdy : 0 < d y := by linarith
  have hdyU : d y ≤ 2*d x := by linarith
  have hdist : dist x y ≤ 1/2 := by linarith [d_le_one x]
  by_cases hboth : ‖x‖ ≤ 1 ∧ ‖y‖ ≤ 1
  · rw [weight_inner μ κ e hboth.1,weight_inner μ κ e hboth.2,sub_self,abs_zero]
    exact mul_nonneg (mul_nonneg (oscillationConstant_nonneg μ hκ.le) (pow_nonneg hd.le _)) dist_nonneg
  have hnxy : 1/2 ≤ ‖x‖ ∧ 1/2 ≤ ‖y‖ := by
    have hnorm : |‖x‖-‖y‖| ≤ dist x y := by simpa only [dist_eq_norm] using abs_norm_sub_norm_le x y
    have hh := abs_le.mp hnorm
    push Not at hboth
    by_cases hx : ‖x‖ ≤ 1
    · have hy := hboth hx; constructor <;> linarith
    · push Not at hx; constructor <;> linarith
  have hx0 : x ≠ 0 := norm_ne_zero_iff.mp (ne_of_gt (by linarith [hnxy.1] : 0 < ‖x‖))
  have hy0 : y ≠ 0 := norm_ne_zero_iff.mp (ne_of_gt (by linarith [hnxy.2] : 0 < ‖y‖))
  let cₓ := normalized μ.toSphere (direction x hx0) (κ*d x) e
  let cᵧ := normalized μ.toSphere (direction y hy0) (κ*d y) e
  have hcx : 0 ≤ cₓ := normalized_nonneg _ _ _ _
  have hcy : 0 ≤ cᵧ := normalized_nonneg _ _ _ _
  have hcl : cₓ ≤ 1/(lowerConstant μ*(κ*d x)^(n-1)) := by
    exact (normalized_le_inv μ.toSphere _ (mul_pos hκ hd) e).trans (by
      simpa only [one_div] using one_div_le_one_div_of_le
        (mul_pos hc.1 (pow_pos (mul_pos hκ hd) _))
        (sphere_normalizer_bounds μ (direction x hx0) (mul_pos hκ hd)
          ((mul_le_of_le_one_left (d_nonneg x) hκ1).trans (d_le_one x))).1)
  have hco := normalized_close_oscillation μ hκ hκ1 hx0 hy0 hd hxy hnxy.1 hnxy.2 e
  have hwo : |w n x-w n y| ≤ wDerivativeConstant n*(2*d x)^(N n-2)*dist x y := by
    rw [abs_sub_comm]
    exact w_oscillation hn (by positivity) (by linarith)
  have hwy : w n y ≤ (6*(N n:ℝ)*3^(N n-1))*(2*d x)^(N n-1) := by
    rw [w_eq_profile]
    exact (wProfile_bound n (norm_nonneg y)).trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (d_nonneg y) hdyU _) (by positivity))
  rw [weight,dite_eq_left ⟨hx0,hd⟩,weight,dite_eq_left ⟨hy0,hdy⟩]
  change |w n x*cₓ-w n y*cᵧ| ≤ _
  calc
    _ ≤ |w n x-w n y| *cₓ+w n y*|cₓ-cᵧ| := by
      rw [show w n x*cₓ-w n y*cᵧ = (w n x-w n y)*cₓ+w n y*(cₓ-cᵧ) by ring]
      simpa only [abs_mul,abs_of_nonneg hcx,abs_of_nonneg (w_nonneg n y)] using abs_add_le ((w n x-w n y)*cₓ) (w n y*(cₓ-cᵧ))
    _ ≤ (wDerivativeConstant n*(2*d x)^(N n-2)*dist x y)*
        (1/(lowerConstant μ*(κ*d x)^(n-1))) +
        ((6*(N n:ℝ)*3^(N n-1))*(2*d x)^(N n-1))*
          (normalizedOscConstant μ*6*dist x y/(κ*d x)^n) := by
      apply add_le_add
      · exact mul_le_mul hwo hcl hcx (by have hh := (constants_nonneg n).2.2; positivity)
      · exact mul_le_mul hwy hco (abs_nonneg _) (by positivity)
    _ = _ := by
      have hN2 : N n-2 = (n-1)+(N n-n-1) := by dsimp [N]; omega
      have hN1 : N n-1 = n+(N n-n-1) := by dsimp [N]; omega
      have hd2 : (d x)^(N n-2) = (d x)^(n-1)*(d x)^(N n-n-1) := by rw [hN2,pow_add]
      have hd1 : (d x)^(N n-1) = (d x)^n*(d x)^(N n-n-1) := by rw [hN1,pow_add]
      simp only [mul_pow]
      rw [hd2,hd1]
      unfold oscillationConstant
      change _ = (wDerivativeConstant n*2^(N n-2)/(lowerConstant μ*κ^(n-1))+
        (6*(N n:ℝ)*3^(N n-1))*2^(N n-1)*normalizedOscConstant μ*6/κ^n)*(d x)^(N n-n-1)*dist x y
      field_simp [ne_of_gt hc.1,ne_of_gt hκ,ne_of_gt hd]

end HenonLaneEmden.AdaptiveCap
end
end CapOscillation

end OAI
end

section
-- module Solutions.OAIQW_HenonLaneEmden.CapContinuity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE

section CapContinuity

open MeasureTheory Set Metric Filter Topology
noncomputable section
namespace HenonLaneEmden.AdaptiveCap
open Cutoff CapWeights
variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]
  (μ : Measure E) [μ.IsAddHaarMeasure]

lemma continuous_weight {κ : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1) (e : sphere (0:E) 1) :
    Continuous (weight μ κ e) := by
  rw [continuous_iff_continuousAt]
  intro x
  by_cases hd : 0 < d x
  · rw [Metric.continuousAt_iff]
    intro ε hε
    let C := oscillationConstant μ κ*(d x)^(N (Module.finrank ℝ E)-Module.finrank ℝ E-1)
    have hC : 0 ≤ C := mul_nonneg (oscillationConstant_nonneg μ hκ.le) (pow_nonneg hd.le _)
    have hC1 : 0 < C+1 := by linarith
    refine ⟨min (d x/2) (ε/(C+1)),lt_min (half_pos hd) (div_pos hε hC1),?_⟩
    intro y hy
    have hdist : dist x y < ε/(C+1) := by simpa only [dist_comm x y] using (lt_min_iff.mp hy).2
    have hh := weight_close_oscillation μ hκ hκ1 hd (y := y)
      (by simpa only [dist_comm] using (lt_min_iff.mp hy).1.le) e
    change |weight μ κ e x-weight μ κ e y| ≤ C*dist x y at hh
    rw [Real.dist_eq,abs_sub_comm]
    have hb : (C+1)*dist x y < ε := by simpa only [mul_comm] using (lt_div_iff₀ hC1).mp hdist
    have hr := dist_nonneg (x := x) (y := y)
    nlinarith
  · have hd0 : d x = 0 := le_antisymm (not_lt.mp hd) (d_nonneg x)
    have hx : 2 ≤ ‖x‖ := not_lt.mp (fun hh => hd ((d_pos_iff x).mpr hh))
    have hN : N (Module.finrank ℝ E)-Module.finrank ℝ E ≠ 0 := by unfold N; omega
    have hcont : Continuous (fun y : E => boundConstant μ κ*(d y)^(N (Module.finrank ℝ E)-Module.finrank ℝ E)) :=
      continuous_const.mul (continuous_d.pow _)
    have ht : Tendsto (fun y : E => boundConstant μ κ*(d y)^(N (Module.finrank ℝ E)-Module.finrank ℝ E))
        (𝓝 x) (𝓝 0) := by simpa only [hd0,zero_pow hN,mul_zero] using hcont.tendsto x
    change Tendsto _ (𝓝 x) (𝓝 (weight μ κ e x))
    rw [weight_outer μ κ e hx]
    exact squeeze_zero (weight_nonneg μ κ e) (weight_bound μ hκ hκ1 e) ht

omit [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E] [μ.IsAddHaarMeasure] in
lemma continuous_weight_direction (κ : ℝ) (x : E) :
    Continuous (fun e : sphere (0:E) 1 => weight μ κ e x) := by
  by_cases hx : x ≠ 0 ∧ 0 < d x
  · simp only [weight,dite_eq_left hx,normalized]
    exact continuous_const.mul ((continuous_profile _ _).div_const _)
  · simp only [weight,dite_eq_right hx]; exact continuous_const

lemma measurable_weight {κ : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1) :
    Measurable (fun z : sphere (0:E) 1 × E => weight μ κ z.1 z.2) := by
  have hh : Measurable (fun z : E × sphere (0:E) 1 => weight μ κ z.2 z.1) :=
    measurable_uncurry_of_continuous_of_measurable (continuous_weight μ hκ hκ1)
      (fun x => (continuous_weight_direction μ κ x).measurable)
  exact hh.comp measurable_swap

lemma weight_le_constant {κ : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1) (e : sphere (0:E) 1) (x : E) :
    weight μ κ e x ≤ boundConstant μ κ := by
  apply (weight_bound μ hκ hκ1 e x).trans
  have hp := pow_le_one₀ (d_nonneg x) (d_le_one x) (n := N (Module.finrank ℝ E)-Module.finrank ℝ E)
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hp (boundConstant_nonneg μ hκ.le)

end HenonLaneEmden.AdaptiveCap
end
end CapContinuity

end OAI
end

section
-- module Solutions.OAIQW_HenonLaneEmden.Components
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uX

section Components
open MeasureTheory Set Filter Topology
open scoped ENNReal
open Classical
namespace HenonLaneEmden.LineComponents

variable {X : Type uX} [TopologicalSpace X]

omit [TopologicalSpace X] in
lemma segmentInside_iff_mem_component {U : Set (X × ℝ)} {p : X} {r : ℝ}
    (hp : (p,0) ∈ U) :
    SegmentInside U p r ↔ r ∈ connectedComponentIn {s : ℝ | (p,s) ∈ U} 0 := by
  constructor
  · intro h
    exact isPreconnected_uIcc.subset_connectedComponentIn left_mem_uIcc h right_mem_uIcc
  · intro hr s hs
    have hp' : 0 ∈ connectedComponentIn {s : ℝ | (p,s) ∈ U} 0 := mem_connectedComponentIn hp
    exact connectedComponentIn_subset {s : ℝ | (p,s) ∈ U} 0
      (isPreconnected_connectedComponentIn.ordConnected.uIcc_subset hp' hr hs)

omit [TopologicalSpace X] in
lemma segmentInside_zero {U : Set (X × ℝ)} {p : X} :
    SegmentInside U p 0 ↔ (p,0) ∈ U := by simp [SegmentInside]

omit [TopologicalSpace X] in
lemma segmentInside_base {U : Set (X × ℝ)} {p : X} {r : ℝ}
    (h : SegmentInside U p r) : (p,0) ∈ U := h 0 left_mem_uIcc

lemma isOpen_segmentInside {U : Set (X × ℝ)} (hU : IsOpen U) (r : ℝ) :
    IsOpen {p : X | SegmentInside U p r} := by
  rw [isOpen_iff_mem_nhds]
  intro p hp
  have hprod : ({p} : Set X) ×ˢ uIcc 0 r ⊆ U := by
    rintro ⟨q,s⟩ ⟨hq,hs⟩
    obtain rfl := mem_singleton_iff.mp hq
    exact hp s hs
  obtain ⟨V,W,hV,-,hpV,hsegW,hVW⟩ :=
    generalized_tube_lemma isCompact_singleton isCompact_uIcc hU hprod
  exact Filter.mem_of_superset (hV.mem_nhds (singleton_subset_iff.mp hpV))
    (fun q hq s hs => hVW ⟨hq,hsegW hs⟩)

lemma isOpen_section {U : Set (X × ℝ)} (hU : IsOpen U) (p : X) :
    IsOpen {s : ℝ | (p,s) ∈ U} := hU.preimage (continuous_const.prodMk continuous_id)

omit [TopologicalSpace X] in
lemma componentInf_le_base {U : Set (X × ℝ)} (value : X × ℝ → ℝ) {p : X}
    (hp : (p,0) ∈ U) : componentInf U value p ≤ ENNReal.ofReal (value (p,0)) := by
  have h := iInf_le (fun r : ℚ => if SegmentInside U p (r : ℝ)
    then ENNReal.ofReal (value (p,(r : ℝ))) else ⊤) 0
  simpa [componentInf, segmentInside_zero, hp] using h

omit [TopologicalSpace X] in
lemma componentWeight_le_base {U : Set (X × ℝ)} (h d : X × ℝ → ℝ) (δ : ℝ) (p : X) :
    componentWeight U h d δ p ≤ ENNReal.ofReal (h (p,0)) := by
  unfold componentWeight
  split_ifs with hp
  · exact componentInf_le_base h hp.1
  · exact bot_le

/-- The rational infimum equals the infimum over the genuine open component. -/
lemma componentInf_eq_component {U : Set (X × ℝ)} (hU : IsOpen U)
    {value : X × ℝ → ℝ} {p : X} (hp : (p,0) ∈ U)
    (hv : Continuous (fun s : ℝ => value (p,s))) :
    componentInf U value p =
      ⨅ s ∈ connectedComponentIn {s : ℝ | (p,s) ∈ U} 0, ENNReal.ofReal (value (p,s)) := by
  let C := connectedComponentIn {s : ℝ | (p,s) ∈ U} 0
  have hC : IsOpen C := (isOpen_section hU p).connectedComponentIn
  have hclosed : IsClosed {s : ℝ | componentInf U value p ≤ ENNReal.ofReal (value (p,s))} :=
    isClosed_le continuous_const (ENNReal.continuous_ofReal.comp hv)
  have hdense : C ⊆ closure (range ((↑) : ℚ → ℝ) ∩ C) :=
    by simpa [inter_comm] using Rat.denseRange_cast.open_subset_closure_inter hC
  have hle : ∀ s ∈ C, componentInf U value p ≤ ENNReal.ofReal (value (p,s)) := by
    intro s hs
    apply closure_minimal (t := {s : ℝ | componentInf U value p ≤ ENNReal.ofReal (value (p,s))})
      ?_ hclosed (hdense hs)
    rintro z ⟨⟨r,rfl⟩,hr⟩
    have hin := (segmentInside_iff_mem_component hp).mpr hr
    have h := iInf_le (fun r : ℚ => if SegmentInside U p (r : ℝ)
      then ENNReal.ofReal (value (p,(r : ℝ))) else ⊤) r
    simpa only [Set.mem_ofPred_eq, componentInf, ite_eq_left hin] using h
  apply le_antisymm
  · exact le_iInf fun s => le_iInf fun hs => hle s hs
  · unfold componentInf
    apply le_iInf
    intro r
    split_ifs with hr
    · exact iInf_le_of_le (r : ℝ) (iInf_le_of_le ((segmentInside_iff_mem_component hp).mp hr) le_rfl)
    · exact le_top

/-- Exceeding a nonnegative forward offset is precisely the compact-segment
condition. Openness is needed to replace membership of the endpoint by strict
inequality of the exit distance. -/
lemma lt_forwardExit_iff {U : Set (X × ℝ)} (hU : IsOpen U) {p : X} {r : ℝ}
    (hr : 0 ≤ r) : ENNReal.ofReal r < forwardExit U p ↔ SegmentInside U p r := by
  unfold forwardExit
  rw [lt_iSup_iff]
  constructor
  · rintro ⟨q,hq⟩
    split_ifs at hq with hin
    · have hrq := (ENNReal.ofReal_lt_ofReal_iff_of_nonneg hr).mp hq
      intro s hs
      apply hin s
      rw [uIcc_of_le (hr.trans hrq.le), mem_Icc]
      rw [uIcc_of_le hr, mem_Icc] at hs
      exact ⟨hs.1, hs.2.trans hrq.le⟩
    · exact (not_lt_zero hq).elim
  · intro hin
    have hp := segmentInside_base hin
    have hrC := (segmentInside_iff_mem_component hp).mp hin
    have hopen := (isOpen_section hU p).connectedComponentIn (x := 0)
    obtain ⟨a,b,hab,hsub⟩ := mem_nhds_iff_exists_Ioo_subset.mp (hopen.mem_nhds hrC)
    obtain ⟨q,hrq,hqb⟩ := exists_rat_btwn hab.2
    have hqC := hsub ⟨hab.1.trans hrq,hqb⟩
    refine ⟨q, ?_⟩
    rw [ite_eq_left ((segmentInside_iff_mem_component hp).mpr hqC)]
    exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg hr).mpr hrq

omit [TopologicalSpace X] in
lemma segmentInside_reflect {U : Set (X × ℝ)} {p : X} {r : ℝ} :
    SegmentInside {z : X × ℝ | (z.1,-z.2) ∈ U} p r ↔ SegmentInside U p (-r) := by
  constructor <;> intro h s hs
  · have hm : -s ∈ uIcc 0 r := by
      simp only [mem_uIcc] at hs ⊢
      rcases hs with hs | hs
      · right; constructor <;> linarith
      · left; constructor <;> linarith
    simpa using h (-s) hm
  · have hm : -s ∈ uIcc 0 (-r) := by
      simp only [mem_uIcc] at hs ⊢
      rcases hs with hs | hs
      · right; constructor <;> linarith
      · left; constructor <;> linarith
    simpa using h (-s) hm

lemma lt_backwardExit_iff {U : Set (X × ℝ)} (hU : IsOpen U) {p : X} {r : ℝ}
    (hr : 0 ≤ r) : ENNReal.ofReal r < backwardExit U p ↔ SegmentInside U p (-r) := by
  have hV : IsOpen {z : X × ℝ | (z.1,-z.2) ∈ U} :=
    hU.preimage (continuous_fst.prodMk continuous_snd.neg)
  have heq : backwardExit U p = forwardExit {z : X × ℝ | (z.1,-z.2) ∈ U} p := by
    simp only [backwardExit, forwardExit, segmentInside_reflect]
  rw [heq, lt_forwardExit_iff hV hr, segmentInside_reflect]

lemma forwardExit_pos {U : Set (X × ℝ)} (hU : IsOpen U) {p : X}
    (hp : (p,0) ∈ U) : 0 < forwardExit U p := by
  simpa using (lt_forwardExit_iff hU (p := p) (r := 0) le_rfl).mpr
    (segmentInside_zero.mpr hp)

lemma backwardExit_pos {U : Set (X × ℝ)} (hU : IsOpen U) {p : X}
    (hp : (p,0) ∈ U) : 0 < backwardExit U p := by
  simpa using (lt_backwardExit_iff hU (p := p) (r := 0) le_rfl).mpr
    (by simpa using (segmentInside_zero (p := p)).mpr hp)

lemma component_eq_Ioo {U : Set (X × ℝ)} (hU : IsOpen U) {p : X}
    (hp : (p,0) ∈ U) (hf : forwardExit U p ≠ ⊤) (hb : backwardExit U p ≠ ⊤) :
    connectedComponentIn {s : ℝ | (p,s) ∈ U} 0 =
      Ioo (-(backwardExit U p).toReal) (forwardExit U p).toReal := by
  have hfp : 0 < (forwardExit U p).toReal := ENNReal.toReal_pos (forwardExit_pos hU hp).ne' hf
  have hbp : 0 < (backwardExit U p).toReal := ENNReal.toReal_pos (backwardExit_pos hU hp).ne' hb
  ext r
  rw [← segmentInside_iff_mem_component hp, mem_Ioo]
  by_cases hr : 0 ≤ r
  · rw [← lt_forwardExit_iff hU hr, ENNReal.ofReal_lt_iff_lt_toReal hr hf]
    exact ⟨fun h => ⟨by linarith,h⟩, fun h => h.2⟩
  · have hnr : 0 ≤ -r := by linarith
    have he := lt_backwardExit_iff hU (p := p) hnr
    rw [neg_neg] at he
    rw [← he, ENNReal.ofReal_lt_iff_lt_toReal hnr hb]
    constructor
    · intro h; constructor <;> linarith
    · intro h; linarith [h.1]

lemma volume_component {U : Set (X × ℝ)} (hU : IsOpen U) {p : X}
    (hp : (p,0) ∈ U) (hfin : componentLength U p ≠ ⊤) :
    volume (connectedComponentIn {s : ℝ | (p,s) ∈ U} 0) = componentLength U p := by
  have hf : forwardExit U p ≠ ⊤ := by
    exact (ENNReal.add_ne_top.mp hfin).1
  have hb : backwardExit U p ≠ ⊤ := by
    exact (ENNReal.add_ne_top.mp hfin).2
  rw [component_eq_Ioo hU hp hf hb, Real.volume_Ioo, sub_neg_eq_add]
  rw [ENNReal.ofReal_add (ENNReal.toReal_nonneg) (ENNReal.toReal_nonneg),
    ENNReal.ofReal_toReal hf, ENNReal.ofReal_toReal hb]
  rfl

section Measurability
variable [MeasurableSpace X] [BorelSpace X]

lemma measurable_forwardExit {U : Set (X × ℝ)} (hU : IsOpen U) : Measurable (forwardExit U) := by
  apply Measurable.iSup
  intro r
  exact Measurable.ite (isOpen_segmentInside hU (r : ℝ)).measurableSet
    measurable_const measurable_const

lemma measurable_backwardExit {U : Set (X × ℝ)} (hU : IsOpen U) : Measurable (backwardExit U) := by
  apply Measurable.iSup
  intro r
  exact Measurable.ite (isOpen_segmentInside hU (-(r : ℝ))).measurableSet
    measurable_const measurable_const

lemma measurable_componentLength {U : Set (X × ℝ)} (hU : IsOpen U) :
    Measurable (componentLength U) :=
  (measurable_forwardExit hU).add (measurable_backwardExit hU)

lemma measurable_componentInf {U : Set (X × ℝ)} (hU : IsOpen U)
    {value : X × ℝ → ℝ} (hvalue : Measurable value) : Measurable (componentInf U value) := by
  apply Measurable.iInf
  intro r
  exact Measurable.ite (isOpen_segmentInside hU (r : ℝ)).measurableSet
    ((hvalue.comp (measurable_id.prodMk measurable_const)).ennreal_ofReal) measurable_const

lemma measurable_componentWeight {U : Set (X × ℝ)} (hU : IsOpen U)
    {h d : X × ℝ → ℝ} (hh : Measurable h) (hd : Measurable d) (δ : ℝ) :
    Measurable (componentWeight U h d δ) := by
  apply Measurable.ite _ (measurable_componentInf hU hh) measurable_const
  apply MeasurableSet.inter
  · exact (hU.preimage (continuous_id.prodMk continuous_const)).measurableSet
  · apply MeasurableSet.inter
    · exact (measurable_componentLength hU (measurableSet_singleton ⊤)).compl
    · exact measurableSet_le (measurable_componentLength hU)
        (measurable_const.mul (measurable_componentInf hU hd))

end Measurability
end HenonLaneEmden.LineComponents
end Components

end OAI
end

section
-- module Solutions.OAIQW_HenonLaneEmden.ComponentWeights
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uX uP

section ComponentWeights
open MeasureTheory Set Filter Topology
open scoped ENNReal
open Classical
namespace HenonLaneEmden.LineComponents
variable {X : Type uX} [TopologicalSpace X]

omit [TopologicalSpace X] in
lemma forwardExit_le_volume_component {U : Set (X × ℝ)} {p : X}
    (_hp : (p,0) ∈ U) :
    forwardExit U p ≤ volume (connectedComponentIn {s : ℝ | (p,s) ∈ U} 0) := by
  unfold forwardExit
  apply iSup_le
  intro r
  split_ifs with hr
  · by_cases hpos : 0 ≤ (r : ℝ)
    · have hs : uIcc 0 (r : ℝ) ⊆ connectedComponentIn {s : ℝ | (p,s) ∈ U} 0 :=
        isPreconnected_uIcc.subset_connectedComponentIn left_mem_uIcc hr
      have hv := measure_mono (μ := (volume : Measure ℝ)) hs
      simpa only [uIcc_of_le hpos,Real.volume_Icc,sub_zero] using hv
    · simp only [ENNReal.ofReal_eq_zero.mpr (le_of_not_ge hpos),zero_le]
  · exact bot_le

omit [TopologicalSpace X] in
lemma backwardExit_le_volume_component {U : Set (X × ℝ)} {p : X}
    (_hp : (p,0) ∈ U) :
    backwardExit U p ≤ volume (connectedComponentIn {s : ℝ | (p,s) ∈ U} 0) := by
  unfold backwardExit
  apply iSup_le
  intro r
  split_ifs with hr
  · by_cases hpos : 0 ≤ (r : ℝ)
    · have hs : uIcc 0 (-(r : ℝ)) ⊆ connectedComponentIn {s : ℝ | (p,s) ∈ U} 0 :=
        isPreconnected_uIcc.subset_connectedComponentIn left_mem_uIcc hr
      have hv := measure_mono (μ := (volume : Measure ℝ)) hs
      simpa only [uIcc_of_ge (neg_nonpos.mpr hpos),Real.volume_Icc,zero_sub,neg_neg] using hv
    · simp only [ENNReal.ofReal_eq_zero.mpr (le_of_not_ge hpos),zero_le]
  · exact bot_le

/-- The rational exit construction gives the genuine Lebesgue length, including
unbounded components, not merely the finite case. -/
lemma volume_component_all {U : Set (X × ℝ)} (hU : IsOpen U) {p : X}
    (hp : (p,0) ∈ U) :
    volume (connectedComponentIn {s : ℝ | (p,s) ∈ U} 0) = componentLength U p := by
  by_cases hfin : componentLength U p ≠ ⊤
  · exact volume_component hU hp hfin
  · have ht : componentLength U p = ⊤ := not_ne_iff.mp hfin
    rw [ht]
    by_contra hv
    apply hfin
    exact ENNReal.add_ne_top.mpr
      ⟨ne_top_of_le_ne_top hv (forwardExit_le_volume_component hp),
       ne_top_of_le_ne_top hv (backwardExit_le_volume_component hp)⟩

lemma setInf_le {f : ℝ → ℝ} {I : Set ℝ} {x : ℝ} (hx : x ∈ I) :
    setInf f I ≤ ENNReal.ofReal (f x) :=
  iInf_le_of_le x (iInf_le_of_le hx le_rfl)

lemma setWeight_le {h d : ℝ → ℝ} {δ : ℝ} {I : Set ℝ} {x : ℝ} (hx : x ∈ I) :
    setWeight h d δ I ≤ ENNReal.ofReal (h x) := by
  unfold setWeight
  split_ifs
  · exact setInf_le hx
  · exact bot_le

lemma setWeight_ne_top {h d : ℝ → ℝ} {δ : ℝ} {I : Set ℝ} :
    setWeight h d δ I ≠ ⊤ := by
  unfold setWeight
  split_ifs with hI
  · obtain ⟨x,hx⟩ := hI.1
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top (setInf_le hx)
  · exact ENNReal.zero_ne_top

lemma setWeight_eq_zero_of_empty (h d : ℝ → ℝ) (δ : ℝ) :
    setWeight h d δ ∅ = 0 := by simp [setWeight]

lemma componentWeight_eq_setWeight {U : Set (X × ℝ)} (hU : IsOpen U)
    {h d : X × ℝ → ℝ} {p : X} (hh : Continuous (fun s => h (p,s)))
    (hd : Continuous (fun s => d (p,s))) (δ : ℝ) :
    componentWeight U h d δ p = setWeight (fun s => h (p,s)) (fun s => d (p,s)) δ
      (connectedComponentIn {s | (p,s) ∈ U} 0) := by
  by_cases hp : (p,0) ∈ U
  · have hne : (connectedComponentIn {s | (p,s) ∈ U} 0).Nonempty :=
      ⟨0,mem_connectedComponentIn hp⟩
    simp only [componentWeight,setWeight,hp,hne,true_and,volume_component_all hU hp,
      componentInf_eq_component hU hp hh,componentInf_eq_component hU hp hd,setInf]
  · simp only [componentWeight,hp,false_and,ite_false,
      connectedComponentIn_eq_empty (show 0 ∉ {s | (p,s) ∈ U} from hp),
      setWeight_eq_zero_of_empty]

end HenonLaneEmden.LineComponents
end ComponentWeights

end OAI
end

section
-- module Solutions.OAIQW_HenonLaneEmden.Angular
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE

section Angular

open MeasureTheory MeasureTheory.Measure Set Metric
open scoped ENNReal Pointwise
noncomputable section

namespace HenonLaneEmden
/-- With value zero assigned at the origin, the positive source subgraph is
open jointly in spatial location and positive level. -/
lemma isOpen_source_subgraph {n : ℕ} {u : Space n → ℝ}
    (hu : ContDiffOn ℝ 2 u ({0}ᶜ : Set (Space n))) (hup : ∀ x, 0 < u x) (q B : ℝ) :
    IsOpen {z : Space n × ℝ | 0 < z.2 ∧ z.2 < source u q B z.1} := by
  rw [isOpen_iff_mem_nhds]
  intro z hz
  have hx : z.1 ≠ 0 := by
    intro he
    simpa [he,source_zero] using hz.1.trans hz.2
  have hc : ContinuousAt (source u q B) z.1 :=
    (regular_source hu hup q B).continuousOn.continuousAt (isClosed_singleton.isOpen_compl.mem_nhds hx)
  exact (continuousAt_const.eventually_lt continuousAt_snd hz.1).and
    (continuousAt_snd.eventually_lt (hc.comp continuousAt_fst) hz.2)

end HenonLaneEmden
end
end Angular

end OAI
end

section
-- module Solutions.OAIQW_HenonLaneEmden.SpatialComponents
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE

section SpatialComponents

open MeasureTheory Set Metric
noncomputable section
namespace HenonLaneEmden.SpatialComponents
open Cutoff AdaptiveCap LineComponents
variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]
  (μ : Measure E) [μ.IsAddHaarMeasure]

omit [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E] in
lemma isOpen_lineLayer {f : E → ℝ} (hf : IsOpen {z : E × ℝ | 0 < z.2 ∧ z.2 < f z.1}) :
    IsOpen (lineLayer f) := by
  exact hf.preimage (show Continuous (fun z : (sphere (0:E) 1 × (E × ℝ)) × ℝ =>
    (z.1.2.1+z.2 • z.1.1.1,z.1.2.2)) by fun_prop)

lemma measurable_lineWeight {f : E → ℝ} (hf : IsOpen {z : E × ℝ | 0 < z.2 ∧ z.2 < f z.1})
    {κ : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1) (δ : ℝ) :
    Measurable (lineWeight μ f κ δ) := by
  unfold lineWeight
  apply Measurable.ennreal_toReal
  apply measurable_componentWeight (isOpen_lineLayer hf)
  · exact (measurable_weight μ hκ hκ1).comp
      (show Measurable (fun z : (sphere (0:E) 1 × (E × ℝ)) × ℝ =>
        (z.1.1,z.1.2.1+z.2 • z.1.1.1)) by fun_prop)
  · exact continuous_d.measurable.comp
      (show Measurable (fun z : (sphere (0:E) 1 × (E × ℝ)) × ℝ =>
        z.1.2.1+z.2 • z.1.1.1) by fun_prop)

omit [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E] [μ.IsAddHaarMeasure] in
lemma lineWeight_nonneg (f : E → ℝ) (κ δ : ℝ) (p : sphere (0:E) 1 × (E × ℝ)) :
    0 ≤ lineWeight μ f κ δ p := ENNReal.toReal_nonneg

omit [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E] [μ.IsAddHaarMeasure] in
lemma lineWeight_le (f : E → ℝ) (κ δ : ℝ) (p : sphere (0:E) 1 × (E × ℝ)) :
    lineWeight μ f κ δ p ≤ weight μ κ p.1 p.2.1 := by
  have he := componentWeight_le_base
    (U := lineLayer f) (fun z => weight μ κ z.1.1 (z.1.2.1+z.2 • z.1.1.1))
    (fun z => d (z.1.2.1+z.2 • z.1.1.1)) δ p
  have hr := ENNReal.toReal_mono ENNReal.ofReal_ne_top he
  simpa only [lineWeight,zero_smul,add_zero,ENNReal.toReal_ofReal (weight_nonneg μ _ _ _)] using hr

lemma lineWeight_eq_setWeight {f : E → ℝ}
    (hf : IsOpen {z : E × ℝ | 0 < z.2 ∧ z.2 < f z.1})
    {κ : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1) (δ : ℝ) (e : sphere (0:E) 1)
    (x : E) (t : ℝ) :
    lineWeight μ f κ δ (e,x,t) =
      (setWeight (fun s => weight μ κ e (x+s • (e:E))) (fun s => d (x+s • (e:E))) δ
        (connectedComponentIn {s | 0 < t ∧ t < f (x+s • (e:E))} 0)).toReal := by
  have hh : Continuous (fun s : ℝ => weight μ κ e (x+s • (e:E))) :=
    (continuous_weight μ hκ hκ1 e).comp (by fun_prop)
  have hd : Continuous (fun s : ℝ => d (x+s • (e:E))) := continuous_d.comp (by fun_prop)
  exact congrArg ENNReal.toReal (componentWeight_eq_setWeight (isOpen_lineLayer hf)
    (p := (e,x,t))
    (h := fun z => weight μ κ z.1.1 (z.1.2.1+z.2 • z.1.1.1))
    (d := fun z => d (z.1.2.1+z.2 • z.1.1.1)) hh hd δ)

omit [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E] in
lemma dist_line (e : sphere (0:E) 1) (x : E) (s t : ℝ) :
    dist (x+s • (e:E)) (x+t • (e:E)) = dist s t := by
  have hn : ‖(e:E)‖ = 1 := by simpa only [mem_sphere,dist_zero_right] using e.2
  rw [dist_eq_norm,show x+s • (e:E)-(x+t • (e:E)) = (s-t) • (e:E) by module,
    norm_smul,hn,mul_one,Real.norm_eq_abs,Real.dist_eq]

end HenonLaneEmden.SpatialComponents
end
end SpatialComponents

end OAI
end

section
-- module Solutions.OAIQW_HenonLaneEmden.Endpoints
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uP uP2 uP3 uP4 uP5 uP6 uP7 uP8

section Endpoints

open Set MeasureTheory Filter Topology
open scoped ENNReal
open Classical
namespace HenonLaneEmden.LineComponents

/-- Components are closed relative to the original set. -/
lemma closure_component_inter_subset {U : Set ℝ} {x : ℝ} (hx : x ∈ U) :
    closure (connectedComponentIn U x) ∩ U ⊆ connectedComponentIn U x := by
  intro y hy
  have hpre : IsPreconnected (insert y (connectedComponentIn U x)) :=
    isPreconnected_connectedComponentIn.subset_closure (subset_insert _ _)
      (insert_subset_iff.mpr ⟨hy.1,subset_closure⟩)
  have hsub := hpre.subset_connectedComponentIn
    (mem_insert_of_mem _ (mem_connectedComponentIn hx))
    (insert_subset_iff.mpr ⟨hy.2,connectedComponentIn_subset U x⟩)
  exact hsub (mem_insert _ _)

lemma component_endpoints_frontier {U : Set ℝ} {x a b : ℝ} (hx : x ∈ U)
    (he : connectedComponentIn U x = Ioo a b) : a ∈ frontier U ∧ b ∈ frontier U := by
  have hxI := mem_connectedComponentIn hx
  rw [he] at hxI
  have hab : a < b := lt_trans hxI.1 hxI.2
  have hac : a ∈ closure (connectedComponentIn U x) := by rw [he,closure_Ioo hab.ne]; exact ⟨le_rfl,hab.le⟩
  have hbc : b ∈ closure (connectedComponentIn U x) := by rw [he,closure_Ioo hab.ne]; exact ⟨hab.le,le_rfl⟩
  have haU : a ∉ U := by
    intro ha
    have hh := closure_component_inter_subset hx ⟨hac,ha⟩
    rw [he] at hh
    exact (lt_irrefl a) hh.1
  have hbU : b ∉ U := by
    intro hb
    have hh := closure_component_inter_subset hx ⟨hbc,hb⟩
    rw [he] at hh
    exact (lt_irrefl b) hh.2
  exact ⟨⟨closure_mono (connectedComponentIn_subset U x) hac,
      fun ha => haU (interior_subset ha)⟩,
    ⟨closure_mono (connectedComponentIn_subset U x) hbc,
      fun hb => hbU (interior_subset hb)⟩⟩

lemma value_eq_level_at_endpoint {f : ℝ → ℝ} {O : Set ℝ} {t x a b : ℝ}
    (hx : x ∈ {s | s ∈ O ∧ t < f s})
    (he : connectedComponentIn {s | s ∈ O ∧ t < f s} x = Ioo a b)
    {y : ℝ} (hy : y=a ∨ y=b) (hyO : y ∈ O) (hf : ContinuousAt f y) : f y = t := by
  have hfront := component_endpoints_frontier hx he
  have hyfront : y ∈ frontier {s | s ∈ O ∧ t < f s} := hy.elim (fun h => h ▸ hfront.1) (fun h => h ▸ hfront.2)
  have hxI := mem_connectedComponentIn hx
  rw [he] at hxI
  have hab : a < b := lt_trans hxI.1 hxI.2
  have hyc : y ∈ closure (connectedComponentIn {s | s ∈ O ∧ t < f s} x) := by
    rw [he,closure_Ioo hab.ne]
    rcases hy with rfl | rfl <;> exact ⟨by linarith,by linarith⟩
  have hynot : y ∉ {s | s ∈ O ∧ t < f s} := by
    intro h
    have hm := closure_component_inter_subset hx ⟨hyc,h⟩
    rw [he] at hm
    rcases hy with rfl | rfl <;> linarith [hm.1,hm.2]
  apply le_antisymm
  · exact le_of_not_gt (fun h => hynot ⟨hyO,h⟩)
  · have hmem := _root_.mem_closure_image hf hyc
    have hsub : f '' connectedComponentIn {s | s ∈ O ∧ t < f s} x ⊆ Ici t := by
      rintro _ ⟨s,hs,rfl⟩
      exact (connectedComponentIn_subset _ _ hs).2.le
    exact (closure_minimal hsub isClosed_Ici) hmem

lemma setWeight_le_on_closure {h d : ℝ → ℝ} {δ : ℝ} {I : Set ℝ}
    (hh : Continuous h) (hn : ∀ x ∈ I, 0 ≤ h x) {y : ℝ} (hy : y ∈ closure I) :
    (setWeight h d δ I).toReal ≤ h y := by
  have hs : I ⊆ {x | (setWeight h d δ I).toReal ≤ h x} := by
    intro x hx
    exact (ENNReal.toReal_le_toReal setWeight_ne_top ENNReal.ofReal_ne_top).mpr (setWeight_le hx)
      |>.trans_eq (ENNReal.toReal_ofReal (hn x hx))
  exact (closure_minimal hs (isClosed_le continuous_const hh)) hy

lemma endpoints_distance_bound {h d : ℝ → ℝ} {δ x a b : ℝ} {I : Set ℝ}
    (he : I = Ioo a b) (hx : x ∈ I) (hδ : 0 ≤ δ) (hd : 0 ≤ d x)
    (hw : 0 < (setWeight h d δ I).toReal) :
    |a-x| ≤ 2*δ*d x ∧ |b-x| ≤ 2*δ*d x := by
  have hxI : a < x ∧ x < b := by simpa [he] using hx
  have htest : I.Nonempty ∧ volume I ≠ ⊤ ∧ volume I ≤ ENNReal.ofReal (2*δ)*setInf d I := by
    unfold setWeight at hw
    split_ifs at hw with htest
    · exact htest
    · simp at hw
  have hv : volume I ≤ ENNReal.ofReal (2*δ)*ENNReal.ofReal (d x) := htest.2.2.trans (by
    gcongr
    exact setInf_le hx)
  rw [he,Real.volume_Ioo,← ENNReal.ofReal_mul (by positivity : 0 ≤ 2*δ)] at hv
  have hlen : b-a ≤ 2*δ*d x := (ENNReal.ofReal_le_ofReal_iff (by positivity : 0 ≤ 2*δ*d x)).mp hv
  rw [abs_of_neg (by linarith : a-x<0),abs_of_pos (by linarith : 0<b-x)]
  constructor <;> linarith

end HenonLaneEmden.LineComponents
end Endpoints

end OAI
end

section
-- module Solutions.OAIQW_HenonLaneEmden.LayerRecovery
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section LayerRecovery
open MeasureTheory Set Filter Topology
namespace HenonLaneEmden.WeightedLayers

lemma source_root {w u q : ℝ} (hw : 0 < w) (hu : 0 < u) (hq : 0 < q) :
    (w*u^q)^(1/q) = w^(1/q)*u := by
  rw [Real.mul_rpow hw.le (Real.rpow_nonneg hu.le _), ← Real.rpow_mul hu.le]
  have h : q*(1/q) = 1 := by field_simp
  rw [h, Real.rpow_one]

lemma weighted_layer_identity {w u q : ℝ} (hw : 0 < w) (hu : 0 < u) (hq : 0 < q) :
    (∫ t in 0..w*u^q, (u-(t/w)^(1/q))) = w*u^(q+1)/(q+1) := by
  have hq' : 0 < 1/q := one_div_pos.mpr hq
  have hf : 0 < w*u^q := mul_pos hw (Real.rpow_pos_of_pos hu _)
  have hr : IntervalIntegrable (fun t : ℝ => t^(1/q)) volume 0 (w*u^q) :=
    intervalIntegral.intervalIntegrable_rpow' (by linarith)
  have heq : (∫ t in 0..w*u^q, (u-(t/w)^(1/q))) =
      (∫ t in 0..w*u^q, (u-t^(1/q)/w^(1/q))) := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le hf.le] at ht
    dsimp only
    rw [Real.div_rpow ht.1 hw.le]
  rw [heq, intervalIntegral.integral_sub (continuous_const.intervalIntegrable ..) (hr.div_const _),
    intervalIntegral.integral_const, intervalIntegral.integral_div,
    integral_rpow (Or.inl (by linarith : -1 < 1/q)),
    Real.zero_rpow (ne_of_gt (by linarith : 0 < 1/q+1)), sub_zero,
    sub_zero, smul_eq_mul]
  rw [Real.rpow_add hf, Real.rpow_one, source_root hw hu hq,
    Real.rpow_add hu, Real.rpow_one]
  have hw' : w^(1/q) ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hw _)
  have hq0 : q ≠ 0 := ne_of_gt hq
  have hq1 : q+1 ≠ 0 := by linarith
  field_simp [hw', hq0, hq1]
  ring

lemma layer_root_bounds {w u q t : ℝ} (hw : 0 < w) (hu : 0 < u) (hq : 0 < q)
    (ht : 0 ≤ t) (htf : t ≤ w*u^q) :
    0 ≤ (t/w)^(1/q) ∧ (t/w)^(1/q) ≤ u := by
  constructor
  · exact Real.rpow_nonneg (div_nonneg ht hw.le) _
  · have htw : t/w ≤ u^q := (div_le_iff₀ hw).mpr (by simpa [mul_comm] using htf)
    have hroot := Real.rpow_le_rpow (div_nonneg ht hw.le) htw (one_div_nonneg.mpr hq.le)
    rw [← Real.rpow_mul hu.le] at hroot
    have h : q*(1/q) = 1 := by field_simp
    rwa [h, Real.rpow_one] at hroot

/-- The exact scalar recovery inequality before integration. -/
lemma pressure_recovery_pointwise {h χ u τ endpoint error : ℝ}
    (hχ : 0 ≤ χ) (hχh : χ ≤ h) (hτ : 0 ≤ τ)
    (hend : |endpoint-τ| ≤ error*u) :
    h*(u-τ)-χ*(u-endpoint) ≤ (h-χ)*u+error*h*u := by
  have hhu : 0 ≤ error*u := le_trans (abs_nonneg _) hend
  have he := (abs_le.mp hend).2
  have hmul := mul_le_mul_of_nonneg_left he hχ
  have hmul' := mul_le_mul_of_nonneg_right hχh hhu
  have htail := mul_nonneg (sub_nonneg.mpr hχh) hτ
  nlinarith

end HenonLaneEmden.WeightedLayers
end LayerRecovery

end OAI
end

section
-- module Solutions.OAIQW_HenonLaneEmden.WeightedEndpoints
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE

section WeightedEndpoints

open MeasureTheory Set Metric
noncomputable section
namespace HenonLaneEmden.WeightedLayers

lemma rpow_annulus_bound {r : ℝ} (hr : r ∈ Icc (1:ℝ) 2) (s : ℝ) : r^s ≤ 2^|s| := by
  have hr0 : 0 ≤ r := by linarith [hr.1]
  calc
    _ ≤ r^|s| := Real.rpow_le_rpow_of_exponent_le hr.1 (le_abs_self s)
    _ ≤ _ := Real.rpow_le_rpow hr0 hr.2 (abs_nonneg s)

lemma rpow_annulus_lipschitz {r r' : ℝ} (hr : r ∈ Icc (1:ℝ) 2)
    (hr' : r' ∈ Icc (1:ℝ) 2) (s : ℝ) :
    |r'^s-r^s| ≤ (|s| *2^|s-1|)*|r'-r| := by
  have hd (x : ℝ) (hx : x ∈ Icc (1:ℝ) 2) := Real.hasStrictDerivAt_rpow_const_of_ne
    (ne_of_gt (show 0 < x by linarith [hx.1])) s |>.hasDerivAt
  have hh := (convex_Icc (1:ℝ) 2).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun x hx => (hd x hx).hasDerivWithinAt)
    (show ∀ x ∈ Icc (1:ℝ) 2, ‖s*x^(s-1)‖ ≤ |s| *2^|s-1| from by
      intro x hx
      rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg (Real.rpow_nonneg (by linarith [hx.1]) _)]
      exact mul_le_mul_of_nonneg_left (rpow_annulus_bound hx (s-1)) (abs_nonneg s)) hr hr'
  simpa only [Real.norm_eq_abs] using hh

lemma rpow_annulus_relative {r r' : ℝ} (hr : r ∈ Icc (1:ℝ) 2)
    (hr' : r' ∈ Icc (1:ℝ) 2) (s : ℝ) :
    |r'^s-r^s| ≤ (|s| *2^|s-1| *2^|s|)*|r'-r| *r^s := by
  have hr0 : 0 < r := by linarith [hr.1]
  have hp : 1 ≤ 2^|s| *r^s := by
    have hh := mul_le_mul_of_nonneg_right (rpow_annulus_bound hr (-s)) (Real.rpow_nonneg hr0.le s)
    rw [abs_neg,← Real.rpow_add hr0,neg_add_cancel,Real.rpow_zero] at hh
    exact hh
  calc
    _ ≤ (|s| *2^|s-1|)*|r'-r| := rpow_annulus_lipschitz hr hr' s
    _ ≤ (|s| *2^|s-1|)*|r'-r| *(2^|s| *r^s) := by
      exact le_mul_of_one_le_right (by positivity) hp
    _ = _ := by ring

lemma layer_root_radial {r t : ℝ} (hr : 0 < r) (ht : 0 ≤ t) (q B : ℝ) :
    (t/r^B)^(1/q) = t^(1/q)*r^(-B/q) := by
  rw [Real.div_rpow ht (Real.rpow_nonneg hr.le _),← Real.rpow_mul hr.le,
    show -B/q = -(B*(1/q)) by ring,Real.rpow_neg hr.le,div_eq_mul_inv]

lemma source_level_root {n : ℕ} {u : Space n → ℝ} {q B t : ℝ}
    (hq : 0 < q) (hu : ∀ x, 0 < u x) {x : Space n} (hx : x ≠ 0)
    (ht : source u q B x = t) : u x = (t/‖x‖^B)^(1/q) := by
  rw [← ht,source_off_zero _ _ _ hx,mul_div_cancel_left₀ _
    (ne_of_gt (Real.rpow_pos_of_pos (norm_pos_iff.mpr hx) _)),← Real.rpow_mul (hu x).le]
  have he : q*(1/q) = 1 := by field_simp
  rw [he,Real.rpow_one]

lemma radial_layer_endpoint_error {E : Type uE} [NormedAddCommGroup E]
    {x y : E} (hx : ‖x‖ ∈ Icc (1:ℝ) 2) (hy : ‖y‖ ∈ Icc (1:ℝ) 2)
    {q B t : ℝ} (ht : 0 ≤ t) :
    |(t/‖y‖^B)^(1/q)-(t/‖x‖^B)^(1/q)| ≤
      (|-B/q| *2^|-B/q-1| *2^|-B/q|)*dist y x*(t/‖x‖^B)^(1/q) := by
  have hx0 : 0 < ‖x‖ := by linarith [hx.1]
  have hy0 : 0 < ‖y‖ := by linarith [hy.1]
  rw [layer_root_radial hx0 ht,layer_root_radial hy0 ht,← mul_sub,abs_mul,
    abs_of_nonneg (Real.rpow_nonneg ht _)]
  have hh := rpow_annulus_relative hx hy (-B/q)
  have hh' := hh.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (abs_norm_sub_norm_le y x) (by positivity))
    (Real.rpow_nonneg hx0.le (-B/q)))
  calc
    _ ≤ t^(1/q)*((|-B/q| *2^|-B/q-1| *2^|-B/q|)*‖y-x‖*‖x‖^(-B/q)) :=
      mul_le_mul_of_nonneg_left hh' (Real.rpow_nonneg ht _)
    _ = _ := by rw [dist_eq_norm]; ring

lemma average_endpoint_error {a b τ ε : ℝ}
    (ha : |a-τ| ≤ ε) (hb : |b-τ| ≤ ε) : |(a+b)/2-τ| ≤ ε := by
  have hh := abs_add_le (a-τ) (b-τ)
  rw [show (a+b)/2-τ = ((a-τ)+(b-τ))/2 by ring,abs_div]
  norm_num
  linarith

end HenonLaneEmden.WeightedLayers
end
end WeightedEndpoints

end OAI
end

section
-- module Solutions.OAIQW_HenonLaneEmden.SpatialEndpoints
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE

section SpatialEndpoints

open MeasureTheory Set Metric
noncomputable section
namespace HenonLaneEmden.SpatialComponents
open Cutoff AdaptiveCap LineComponents WeightedLayers
variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]
  (μ : Measure E) [μ.IsAddHaarMeasure]

omit [Nontrivial E] in
lemma measurable_lowerPoint {f : E → ℝ} (hf : IsOpen {z : E × ℝ | 0 < z.2 ∧ z.2 < f z.1}) :
    Measurable (lowerPoint f) :=
  measurable_snd.fst.add (((measurable_backwardExit (isOpen_lineLayer hf)).ennreal_toReal.neg).smul measurable_fst.subtype_val)
omit [Nontrivial E] in
lemma measurable_upperPoint {f : E → ℝ} (hf : IsOpen {z : E × ℝ | 0 < z.2 ∧ z.2 < f z.1}) :
    Measurable (upperPoint f) :=
  measurable_snd.fst.add (((measurable_forwardExit (isOpen_lineLayer hf)).ennreal_toReal).smul measurable_fst.subtype_val)

omit [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E] [μ.IsAddHaarMeasure] in
lemma positive_lineWeight_base {f : E → ℝ} {κ δ : ℝ} {p : sphere (0:E) 1 × (E × ℝ)}
    (hχ : 0 < lineWeight μ f κ δ p) :
    0 < p.2.2 ∧ p.2.2 < f p.2.1 ∧ componentLength (lineLayer f) p ≠ ⊤ := by
  unfold lineWeight componentWeight at hχ
  split_ifs at hχ with hh
  · have hb := hh.1
    simp only [lineLayer,Set.mem_ofPred_eq,zero_smul,add_zero] at hb
    exact ⟨hb.1,hb.2,hh.2.1⟩
  · simp at hχ

lemma endpoint_spec {f : E → ℝ}
    (hf : IsOpen {z : E × ℝ | 0 < z.2 ∧ z.2 < f z.1})
    (hfc : ∀ y ≠ 0, ContinuousAt f y) {κ δ : ℝ}
    (hκ : 0 < κ) (hκ1 : κ ≤ 1) (hδ : 0 ≤ δ)
    {p : sphere (0:E) 1 × (E × ℝ)} (hχ : 0 < lineWeight μ f κ δ p)
    {s : ℝ} (hs : s=lowerOffset f p ∨ s=upperOffset f p) :
    1 < ‖p.2.1+s • p.1.1‖ ∧ ‖p.2.1+s • p.1.1‖ < 2 ∧
      f (p.2.1+s • p.1.1)=p.2.2 ∧ dist (p.2.1+s • p.1.1) p.2.1 ≤ 2*δ*d p.2.1 := by
  obtain ⟨ht,htf,hfin⟩ := positive_lineWeight_base μ hχ
  let U := {s : ℝ | 0 < p.2.2 ∧ p.2.2 < f (p.2.1+s • p.1.1)}
  have hp : (p,0) ∈ lineLayer f := by simpa only [lineLayer,Set.mem_ofPred_eq,zero_smul,add_zero] using And.intro ht htf
  have he : connectedComponentIn U 0 = Ioo (lowerOffset f p) (upperOffset f p) :=
    component_eq_Ioo (isOpen_lineLayer hf) hp (ENNReal.add_ne_top.mp hfin).1 (ENNReal.add_ne_top.mp hfin).2
  have h0 : 0 ∈ U := hp
  have h0I := mem_connectedComponentIn h0
  have hab : lowerOffset f p < upperOffset f p := by
    rw [he] at h0I
    exact h0I.1.trans h0I.2
  have hsc : s ∈ closure (connectedComponentIn U 0) := by
    rw [he,closure_Ioo hab.ne]
    rcases hs with rfl | rfl <;> exact ⟨by linarith,by linarith⟩
  have hwe : lineWeight μ f κ δ p = (setWeight (fun r => weight μ κ p.1 (p.2.1+r • p.1.1))
      (fun r => d (p.2.1+r • p.1.1)) δ (connectedComponentIn U 0)).toReal :=
    lineWeight_eq_setWeight μ hf hκ hκ1 δ p.1 p.2.1 p.2.2
  have hle := setWeight_le_on_closure (d := fun r => d (p.2.1+r • p.1.1)) (δ := δ)
    ((continuous_weight μ hκ hκ1 p.1).comp (show Continuous (fun r : ℝ => p.2.1+r • p.1.1) by fun_prop))
    (fun r _ => weight_nonneg μ κ p.1 _) hsc
  simp only [Function.comp_def] at hle
  rw [← hwe] at hle
  have hw : 0 < weight μ κ p.1 (p.2.1+s • p.1.1) := hχ.trans_le hle
  have h1 : 1 < ‖p.2.1+s • p.1.1‖ := by
    by_contra hh
    rw [weight_inner μ κ p.1 (not_lt.mp hh)] at hw
    exact lt_irrefl _ hw
  have h2 : ‖p.2.1+s • p.1.1‖ < 2 := by
    by_contra hh
    rw [weight_outer μ κ p.1 (not_lt.mp hh)] at hw
    exact lt_irrefl _ hw
  have hy0 : p.2.1+s • p.1.1 ≠ 0 := norm_ne_zero_iff.mp (by linarith)
  have hval : f (p.2.1+s • p.1.1)=p.2.2 :=
    value_eq_level_at_endpoint (O := {r : ℝ | 0 < p.2.2}) h0 he hs ht
      ((hfc _ hy0).comp (f := fun r : ℝ => p.2.1+r • p.1.1) (show ContinuousAt (fun r : ℝ => p.2.1+r • p.1.1) s by fun_prop))
  have hdist := endpoints_distance_bound he (mem_connectedComponentIn h0) hδ
    (d_nonneg (p.2.1+(0:ℝ) • p.1.1)) (by rw [← hwe]; exact hχ)
  simp only [zero_smul,add_zero,sub_zero] at hdist
  have hd : |s| ≤ 2*δ*d p.2.1 := hs.elim (fun hh => hh ▸ hdist.1) (fun hh => hh ▸ hdist.2)
  refine ⟨h1,h2,hval,?_⟩
  have hd' := dist_line p.1 p.2.1 s 0
  simp only [zero_smul,add_zero,Real.dist_eq,sub_zero] at hd'
  exact hd'.trans_le hd

end HenonLaneEmden.SpatialComponents
end
end SpatialEndpoints

end OAI
end

section
-- module Solutions.OAIQW_HenonLaneEmden.SourceEndpoints
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section SourceEndpoints

open MeasureTheory Set Metric
noncomputable section
namespace HenonLaneEmden.SpatialComponents
open Cutoff AdaptiveCap WeightedLayers

lemma endpointConstant_nonneg (q B : ℝ) : 0 ≤ endpointConstant q B := by
  unfold endpointConstant; positivity

lemma source_endpoint_error {n : ℕ} (hn : 1 ≤ n) {u : Space n → ℝ} {q B κ δ : ℝ}
    (hu : ContDiffOn ℝ 2 u ({0}ᶜ : Set (Space n))) (hup : ∀ x, 0 < u x)
    (hq : 0 < q) (hκ : 0 < κ) (hκ1 : κ ≤ 1) (hδ : 0 ≤ δ)
    {z : sphere (0:Space n) 1 × (Space n × ℝ)}
    (hχ : 0 < lineWeight volume (source u q B) κ δ z) :
    |endpointAverage u (source u q B) z-(z.2.2/‖z.2.1‖^B)^(1/q)| ≤
      endpointConstant q B*δ*d z.2.1*u z.2.1 := by
  have : Nontrivial (Space n) := Module.nontrivial_of_finrank_pos (R := ℝ) (by simp; omega)
  have hf := isOpen_source_subgraph hu hup q B
  have hfc (y : Space n) (hy : y ≠ 0) : ContinuousAt (source u q B) y :=
    (regular_source hu hup q B).continuousOn.continuousAt (isClosed_singleton.isOpen_compl.mem_nhds hy)
  have hb := positive_lineWeight_base volume hχ
  have hw : 0 < weight volume κ z.1 z.2.1 := hχ.trans_le (lineWeight_le volume _ κ δ z)
  have hx1 : 1 < ‖z.2.1‖ := by
    by_contra hh
    rw [weight_inner volume κ z.1 (not_lt.mp hh)] at hw
    exact lt_irrefl _ hw
  have hx2 : ‖z.2.1‖ < 2 := by
    by_contra hh
    rw [weight_outer volume κ z.1 (not_lt.mp hh)] at hw
    exact lt_irrefl _ hw
  have hx0 : z.2.1 ≠ 0 := norm_ne_zero_iff.mp (by linarith)
  have hroot := layer_root_bounds (Real.rpow_pos_of_pos (norm_pos_iff.mpr hx0) B)
    (hup z.2.1) hq hb.1.le (by rw [← source_off_zero _ _ _ hx0]; exact hb.2.1.le)
  have he (s : ℝ) (hs : s=lowerOffset (source u q B) z ∨ s=upperOffset (source u q B) z) :
      |u (z.2.1+s • z.1.1)-(z.2.2/‖z.2.1‖^B)^(1/q)| ≤
        endpointConstant q B*δ*d z.2.1*u z.2.1 := by
    obtain ⟨hy1,hy2,hlev,hdist⟩ := endpoint_spec volume hf hfc hκ hκ1 hδ hχ hs
    have hy0 : z.2.1+s • z.1.1 ≠ 0 := norm_ne_zero_iff.mp (by linarith)
    rw [source_level_root hq hup hy0 hlev]
    have hh := radial_layer_endpoint_error (q := q) (B := B) ⟨hx1.le,hx2.le⟩ ⟨hy1.le,hy2.le⟩ hb.1.le
    calc
      _ ≤ (|-B/q| *2^|-B/q-1| *2^|-B/q|)*dist (z.2.1+s • z.1.1) z.2.1*
          (z.2.2/‖z.2.1‖^B)^(1/q) := hh
      _ ≤ (|-B/q| *2^|-B/q-1| *2^|-B/q|)*(2*δ*d z.2.1)*u z.2.1 := by
        have hd0 := d_nonneg z.2.1
        exact mul_le_mul (mul_le_mul_of_nonneg_left hdist (by positivity)) hroot.2 hroot.1 (by positivity)
      _ = _ := by unfold endpointConstant; ring
  exact average_endpoint_error (he _ (Or.inl rfl)) (he _ (Or.inr rfl))

end HenonLaneEmden.SpatialComponents
end
end SourceEndpoints

end OAI
end

section
-- module Solutions.OAIQW_HenonLaneEmden.Tonelli
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE

section Tonelli

open MeasureTheory Set Function
open scoped ENNReal
namespace HenonLaneEmden.LayerTonelli

variable {E : Type uE} [MeasurableSpace E]

lemma measurableSet_sourceSubgraph {f : E → ℝ} (hf : Measurable f) :
    MeasurableSet (sourceSubgraph f) :=
  (measurableSet_lt measurable_const measurable_snd).inter
    (measurableSet_lt measurable_snd (hf.comp measurable_fst))

lemma lintegral_layerMeasure (μ : Measure E) [SFinite μ] {f : E → ℝ}
    (hf : Measurable f) {F : E × ℝ → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ z, F z ∂layerMeasure μ f = ∫⁻ x, ∫⁻ t in Ioo 0 (f x), F (x,t) ∂volume ∂μ := by
  rw [layerMeasure,← lintegral_indicator (measurableSet_sourceSubgraph hf),
    lintegral_prod _ (hF.indicator (measurableSet_sourceSubgraph hf)).aemeasurable]
  apply lintegral_congr
  intro x
  rw [← lintegral_indicator measurableSet_Ioo]
  apply lintegral_congr
  intro t
  simp only [indicator,sourceSubgraph,mem_Ioo,mem_ofPred]

lemma lintegral_layerMeasure_fst (μ : Measure E) [SFinite μ] {f : E → ℝ}
    (hf : Measurable f) {F : E → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ z, F z.1 ∂layerMeasure μ f = ∫⁻ x, ENNReal.ofReal (f x)*F x ∂μ := by
  rw [lintegral_layerMeasure μ hf (F := fun z => F z.1) (by fun_prop)]
  apply lintegral_congr
  intro x
  simp only [lintegral_const,Measure.restrict_apply_univ,Real.volume_Ioo,sub_zero,mul_comm]

lemma lintegral_layer_kernel (μ : Measure E) [SFinite μ] {g : E → ℝ}
    {k : E × E → ℝ≥0∞} (hg : Measurable g) (hk : Measurable k) (x : E) :
    ∫⁻ y, k (x,y.1) ∂layerMeasure μ g = potential μ k g x :=
  lintegral_layerMeasure_fst μ hg (hk.comp (measurable_const.prodMk measurable_id))

/-- This is the Tonelli recovery at an arbitrary measurable selected endpoint.
The selected point depends only on the first layer, never on the second layer. -/
lemma lintegral_pair_endpoint (μ : Measure E) [SFinite μ] {f g : E → ℝ}
    {k : E × E → ℝ≥0∞} {a : E × ℝ → ℝ≥0∞} {endpoint : E × ℝ → E}
    (hg : Measurable g) (hk : Measurable k) (ha : Measurable a) (he : Measurable endpoint) :
    ∫⁻ z, a z.1*k (endpoint z.1,z.2.1) ∂(layerMeasure μ f).prod (layerMeasure μ g) =
      ∫⁻ z, a z*potential μ k g (endpoint z) ∂layerMeasure μ f := by
  rw [lintegral_prod (fun z : (E × ℝ) × (E × ℝ) => a z.1*k (endpoint z.1,z.2.1)) (by fun_prop)]
  apply lintegral_congr
  intro z
  change (∫⁻ y : E × ℝ, a z*k (endpoint z,y.1) ∂layerMeasure μ g) = _
  rw [lintegral_const_mul _ (show Measurable (fun y : E × ℝ => k (endpoint z,y.1)) by fun_prop),
    lintegral_layer_kernel μ hg hk]

lemma lintegral_pair_position (μ : Measure E) [SFinite μ] {f g : E → ℝ}
    {k : E × E → ℝ≥0∞} {a : E × ℝ → ℝ≥0∞}
    (hg : Measurable g) (hk : Measurable k) (ha : Measurable a) :
    ∫⁻ z, a z.1*k (z.1.1,z.2.1) ∂(layerMeasure μ f).prod (layerMeasure μ g) =
      ∫⁻ z, a z*potential μ k g z.1 ∂layerMeasure μ f :=
  lintegral_pair_endpoint μ hg hk ha measurable_fst

/-- Integrating any spatial nonnegative pair function over the two sets of
levels gives exactly the interaction with both source densities. -/
lemma lintegral_pair_spatial (μ : Measure E) [SFinite μ] {f g : E → ℝ}
    {F : E × E → ℝ≥0∞} (hf : Measurable f) (hg : Measurable g) (hF : Measurable F) :
    ∫⁻ z, F (z.1.1,z.2.1) ∂(layerMeasure μ f).prod (layerMeasure μ g) =
      ∫⁻ z, ENNReal.ofReal (f z.1)*ENNReal.ofReal (g z.2)*F z ∂μ.prod μ := by
  calc
    _ = ∫⁻ x : E × ℝ, ∫⁻ y : E × ℝ, F (x.1,y.1) ∂layerMeasure μ g ∂layerMeasure μ f := by
      exact lintegral_prod _ (by fun_prop)
    _ = ∫⁻ x : E × ℝ, ∫⁻ y : E, ENNReal.ofReal (g y)*F (x.1,y) ∂μ ∂layerMeasure μ f := by
      apply lintegral_congr
      intro x
      exact lintegral_layerMeasure_fst μ hg (F := fun y => F (x.1,y)) (by fun_prop)
    _ = ∫⁻ x : E, ENNReal.ofReal (f x)*(∫⁻ y : E, ENNReal.ofReal (g y)*F (x,y) ∂μ) ∂μ := by
      exact lintegral_layerMeasure_fst μ hf
        (F := fun x => ∫⁻ y : E, ENNReal.ofReal (g y)*F (x,y) ∂μ)
        ((show Measurable (fun z : E × E => ENNReal.ofReal (g z.2)*F z) by fun_prop).lintegral_prod_right)
    _ = ∫⁻ z : E × E, ENNReal.ofReal (f z.1)*ENNReal.ofReal (g z.2)*F z ∂μ.prod μ := by
      rw [lintegral_prod _ (by fun_prop)]
      apply lintegral_congr
      intro x
      rw [← lintegral_const_mul _ (show Measurable (fun y => ENNReal.ofReal (g y)*F (x,y)) by fun_prop)]
      apply lintegral_congr
      intro y
      exact (mul_assoc _ _ _).symm

end HenonLaneEmden.LayerTonelli
end Tonelli

end OAI
end

section
-- module Solutions.OAIQW_HenonLaneEmden.PressureRecovery
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE uZ

section PressureRecovery

open MeasureTheory Set
open scoped ENNReal
namespace HenonLaneEmden.LayerTonelli
variable {E : Type uE} [MeasurableSpace E]

lemma lintegral_pair_endpoint_right (μ : Measure E) [SFinite μ] {f g : E → ℝ}
    {k : E × E → ℝ≥0∞} {b : E × ℝ → ℝ≥0∞} {endpoint : E × ℝ → E}
    (hf : Measurable f) (hk : Measurable k) (hs : ∀ x y, k (x,y) = k (y,x))
    (hb : Measurable b) (he : Measurable endpoint) :
    ∫⁻ z, b z.2*k (z.1.1,endpoint z.2) ∂(layerMeasure μ f).prod (layerMeasure μ g) =
      ∫⁻ z, b z*potential μ k f (endpoint z) ∂layerMeasure μ g := by
  rw [← lintegral_prod_swap]
  simp only [Prod.swap]
  simp_rw [hs _ (endpoint _)]
  exact lintegral_pair_endpoint μ hf hk hb he

lemma lintegral_pair_position_right (μ : Measure E) [SFinite μ] {f g : E → ℝ}
    {k : E × E → ℝ≥0∞} {b : E × ℝ → ℝ≥0∞}
    (hf : Measurable f) (hk : Measurable k) (hs : ∀ x y, k (x,y) = k (y,x))
    (hb : Measurable b) :
    ∫⁻ z, b z.2*k (z.1.1,z.2.1) ∂(layerMeasure μ f).prod (layerMeasure μ g) =
      ∫⁻ z, b z*potential μ k f z.1 ∂layerMeasure μ g :=
  lintegral_pair_endpoint_right μ hf hk hs hb measurable_fst

lemma lintegral_pair_weight_sum (μ : Measure E) [SFinite μ] {f g : E → ℝ}
    {k : E × E → ℝ≥0∞} {a b : E × ℝ → ℝ≥0∞}
    (hf : Measurable f) (hg : Measurable g) (hk : Measurable k)
    (hs : ∀ x y, k (x,y) = k (y,x)) (ha : Measurable a) (hb : Measurable b) :
    ∫⁻ z, (a z.1+b z.2)*k (z.1.1,z.2.1) ∂(layerMeasure μ f).prod (layerMeasure μ g) =
      (∫⁻ z, a z*potential μ k g z.1 ∂layerMeasure μ f) +
      ∫⁻ z, b z*potential μ k f z.1 ∂layerMeasure μ g := by
  simp_rw [add_mul]
  rw [lintegral_add_left (by fun_prop),lintegral_pair_position μ hg hk ha,
    lintegral_pair_position_right μ hf hk hs hb]

end HenonLaneEmden.LayerTonelli

namespace HenonLaneEmden.LayerPressure
open LineComponents LayerTonelli IntervalGeometry
variable {Z : Type uZ} [NormedAddCommGroup Z] [MeasurableSpace Z] [BorelSpace Z]
  [SecondCountableTopology Z]

/-- Finite cancellation is used only after the endpoint contributions have
been proved finite. -/
lemma pressure_cancellation {U V R P M Q L T : ℝ≥0∞} (hV : V ≠ ⊤)
    (hcomp : U ≤ V+P+M) (hrec : R+V ≤ U+L+T) (hmis : M ≤ Q+L) :
    R ≤ P+Q+2*L+T := by
  apply (ENNReal.add_le_add_iff_right hV).mp
  calc
    R+V ≤ U+L+T := hrec
    _ ≤ (V+P+M)+L+T := by gcongr
    _ ≤ (V+P+(Q+L))+L+T := by gcongr
    _ = (P+Q+2*L+T)+V := by ring

end HenonLaneEmden.LayerPressure
end PressureRecovery

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

lemma lintegral_interaction {n : ℕ} {f g : Space n → ℝ}
    (hf : Measurable f) (hg : Measurable g) {F : Space n × Space n → ℝ≥0∞}
    (hF : Measurable F) :
    (∫⁻ z, F z ∂interaction f g) =
      ∫⁻ z, ENNReal.ofReal (f z.1)*ENNReal.ofReal (g z.2)*ENNReal.ofReal (newtonKernel n z)*F z ∂volume.prod volume :=
  lintegral_withDensity_eq_lintegral_mul _ (by fun_prop [measurable_newtonKernel]) hF

end HenonLaneEmden
end
end Interaction

end OAI
end

section
-- module Solutions.OAIQW_HenonLaneEmden.RootRecovery
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section RootRecovery

open MeasureTheory Set Metric
open scoped ENNReal
noncomputable section
namespace HenonLaneEmden.WeightedLayers

lemma weighted_layer_identity_ennreal {w u q : ℝ} (hw : 0 < w) (hu : 0 < u) (hq : 0 < q) :
    (∫⁻ t in Ioo 0 (w*u^q), ENNReal.ofReal (u-(t/w)^(1/q))) =
      ENNReal.ofReal ((w*u^q*u)/(q+1)) := by
  have hf : 0 < w*u^q := mul_pos hw (Real.rpow_pos_of_pos hu _)
  have hc : Continuous (fun t : ℝ => u-(t/w)^(1/q)) := by
    apply continuous_const.sub
    exact (continuous_id.div_const w).rpow_const (fun _ => Or.inr (one_div_nonneg.mpr hq.le))
  have hi : IntegrableOn (fun t : ℝ => u-(t/w)^(1/q)) (Ioo 0 (w*u^q)) :=
    (hc.integrableOn_Icc).mono_set Ioo_subset_Icc_self
  rw [← ofReal_integral_eq_lintegral_ofReal hi]
  · rw [← integral_Ioc_eq_integral_Ioo,← intervalIntegral.integral_of_le hf.le,
      weighted_layer_identity hw hu hq,Real.rpow_add hu,Real.rpow_one,mul_assoc]
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    exact sub_nonneg.mpr (layer_root_bounds hw hu hq ht.1.le ht.2.le).2

end HenonLaneEmden.WeightedLayers
namespace HenonLaneEmden.SpatialComponents
open Cutoff AdaptiveCap WeightedLayers LayerTonelli

lemma sourceRoot_bounds {n : ℕ} {u : Space n → ℝ} {q B : ℝ}
    (hu : ∀ x, 0 < u x) (hq : 0 < q) {z : Space n × ℝ}
    (hz : 0 < z.2 ∧ z.2 < source u q B z.1) :
    0 ≤ sourceRoot q B z ∧ sourceRoot q B z ≤ u z.1 := by
  have hx : z.1 ≠ 0 := by
    intro hx; rw [hx,source_zero] at hz; linarith [hz.1,hz.2]
  exact layer_root_bounds (Real.rpow_pos_of_pos (norm_pos_iff.mpr hx) B) (hu _) hq hz.1.le
    (by rw [← source_off_zero _ _ _ hx]; exact hz.2.le)

lemma lintegral_source_residual {n : ℕ} {u : Space n → ℝ} {q B : ℝ}
    (hu : ∀ x, 0 < u x) (hq : 0 < q) (x : Space n) :
    (∫⁻ t in Ioo 0 (source u q B x), ENNReal.ofReal (u x-sourceRoot q B (x,t))) =
      ENNReal.ofReal (source u q B x*u x/(q+1)) := by
  by_cases hx : x=0
  · simp [hx,source_zero]
  · rw [source_off_zero _ _ _ hx]
    exact weighted_layer_identity_ennreal (Real.rpow_pos_of_pos (norm_pos_iff.mpr hx) B) (hu _) hq

lemma source_pressure_recovery_pointwise {n : ℕ} (hn : 1 ≤ n) {u : Space n → ℝ} {q B κ δ : ℝ}
    (hu : ContDiffOn ℝ 2 u ({0}ᶜ : Set (Space n))) (hup : ∀ x, 0 < u x)
    (hq : 0 < q) (hκ : 0 < κ) (hκ1 : κ ≤ 1) (hδ : 0 ≤ δ)
    (e : sphere (0:Space n) 1) {z : Space n × ℝ}
    (hz : 0 < z.2 ∧ z.2 < source u q B z.1) :
    ENNReal.ofReal (weight volume κ e z.1*(u z.1-sourceRoot q B z))+
      ENNReal.ofReal (lineWeight volume (source u q B) κ δ (e,z)*endpointAverage u (source u q B) (e,z)) ≤
    ENNReal.ofReal (lineWeight volume (source u q B) κ δ (e,z)*u z.1)+
      ENNReal.ofReal ((weight volume κ e z.1-lineWeight volume (source u q B) κ δ (e,z))*u z.1)+
      ENNReal.ofReal (endpointConstant q B*δ*d z.1*weight volume κ e z.1*u z.1) := by
  have hnχ := lineWeight_nonneg volume (source u q B) κ δ (e,z)
  have hleh := lineWeight_le volume (source u q B) κ δ (e,z)
  have hh := weight_nonneg volume κ e z.1
  have hu0 : 0 ≤ u z.1 := (hup _).le
  have he : 0 ≤ endpointAverage u (source u q B) (e,z) := by
    exact div_nonneg (add_nonneg (hup _).le (hup _).le) (by norm_num)
  have hr := sourceRoot_bounds hup hq hz
  rw [← ENNReal.ofReal_add (mul_nonneg hh (sub_nonneg.mpr hr.2)) (mul_nonneg hnχ he),
    ← ENNReal.ofReal_add (mul_nonneg hnχ (hup _).le) (mul_nonneg (sub_nonneg.mpr hleh) (hup _).le),
    ← ENNReal.ofReal_add (add_nonneg (mul_nonneg hnχ (hup _).le) (mul_nonneg (sub_nonneg.mpr hleh) (hup _).le))
      (by have hc := endpointConstant_nonneg q B; have hd := d_nonneg z.1; positivity)]
  apply ENNReal.ofReal_le_ofReal
  by_cases hχ : 0 < lineWeight volume (source u q B) κ δ (e,z)
  · have hs := source_endpoint_error hn hu hup hq hκ hκ1 hδ hχ
    have hp := pressure_recovery_pointwise hnχ hleh hr.1 hs
    change _ ≤ _ at hp
    dsimp only [sourceRoot] at *
    nlinarith
  · have hzero := le_antisymm (not_lt.mp hχ) hnχ
    rw [hzero]
    have hc := endpointConstant_nonneg q B
    have hd := d_nonneg z.1
    have htail : 0 ≤ endpointConstant q B*δ*d z.1*weight volume κ e z.1*u z.1 := by positivity
    nlinarith [mul_nonneg hh hr.1]

end HenonLaneEmden.SpatialComponents
end
end RootRecovery

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

lemma compactSupport_weight {n : ℕ} (κ : ℝ) (e : sphere (0:Space n) 1) :
    HasCompactSupport (weight volume κ e) :=
  compactSupport_of_outer_zero (fun _ hx => weight_outer volume κ e hx)

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

lemma IsSolution.weightedEnergyN_finite {n : ℕ} (hn : 2 ≤ n) {p q A B : ℝ}
    {u v χ : Space n → ℝ} (h : IsSolution n p q A B u v)
    (hχ : Continuous χ) (hχc : HasCompactSupport χ) : weightedEnergyN χ u q B ≠ ⊤ :=
  (h.integrable_source_energy_weight hn hχ hχc).lintegral_lt_top.ne

end HenonLaneEmden
end
end WeightedEnergy

end OAI
end

section
-- module Solutions.OAIQW_HenonLaneEmden.IntegratedRecovery
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section IntegratedRecovery

open MeasureTheory Set Metric
open scoped ENNReal
noncomputable section
namespace HenonLaneEmden.SpatialComponents
open Cutoff AdaptiveCap LayerTonelli

lemma lintegral_weight_layer {n : ℕ} {u : Space n → ℝ} {q B : ℝ}
    (hu : Measurable u) (hu0 : ∀ x, 0 ≤ u x) (hf : Measurable (source u q B))
    {χ : Space n → ℝ} (hχ : Measurable χ) (_hχ0 : ∀ x, 0 ≤ χ x) :
    (∫⁻ z, ENNReal.ofReal (χ z.1*u z.1) ∂layerMeasure volume (source u q B)) =
      weightedEnergyN χ u q B := by
  rw [lintegral_layerMeasure_fst volume hf (F := fun x => ENNReal.ofReal (χ x*u x)) (by fun_prop)]
  apply lintegral_congr
  intro x
  rw [← ENNReal.ofReal_mul (source_nonneg hu0 q B x)]
  congr 1
  ring

lemma lintegral_pressure_root {n : ℕ} {u : Space n → ℝ} {q B : ℝ}
    (hu : Measurable u) (hup : ∀ x, 0 < u x) (hq : 0 < q) (hf : Measurable (source u q B))
    {χ : Space n → ℝ} (hχ : Measurable χ) (hχ0 : ∀ x, 0 ≤ χ x) :
    (∫⁻ z, ENNReal.ofReal (χ z.1*(u z.1-sourceRoot q B z)) ∂layerMeasure volume (source u q B)) =
      ENNReal.ofReal (1/(q+1))*weightedEnergyN χ u q B := by
  rw [lintegral_layerMeasure volume hf (by fun_prop)]
  simp_rw [ENNReal.ofReal_mul (hχ0 _)]
  have he (x : Space n) : (∫⁻ t in Ioo 0 (source u q B x), ENNReal.ofReal (χ x)*
      ENNReal.ofReal (u x-sourceRoot q B (x,t))) =
      ENNReal.ofReal (1/(q+1))*ENNReal.ofReal (χ x*source u q B x*u x) := by
    rw [lintegral_const_mul _ (by fun_prop),lintegral_source_residual hup hq,
      ← ENNReal.ofReal_mul (hχ0 x),← ENNReal.ofReal_mul (one_div_nonneg.mpr (by linarith : 0 ≤ q+1))]
    congr 1
    ring
  simp_rw [he]
  exact lintegral_const_mul _ (by fun_prop)

lemma IsSolution_endpointIntegral_bound {n : ℕ} (hn : 2 ≤ n) {p q A B κ δ : ℝ}
    {u v : Space n → ℝ} (h : IsSolution n p q A B u v) (hq : 0 < q)
    (hκ : 0 < κ) (hκ1 : κ ≤ 1) (hδ : 0 ≤ δ) (e : sphere (0:Space n) 1) :
    endpointIntegral u (source u q B) κ δ e ≤
      ENNReal.ofReal (1+endpointConstant q B*δ)*weightedEnergyN (weight volume κ e) u q B := by
  have : Nontrivial (Space n) := Module.nontrivial_of_finrank_pos (R := ℝ) (by simp; omega)
  have huM := h.continuous_u.measurable
  have hfM := measurable_source h.continuous_u q B
  have hm := (continuous_weight volume hκ hκ1 e).measurable
  have hd : Measurable (d : Space n → ℝ) := continuous_d.measurable
  have hc := endpointConstant_nonneg q B
  have hpoint (z : Space n × ℝ) (hz : z ∈ sourceSubgraph (source u q B)) :
      lineWeight volume (source u q B) κ δ (e,z)*endpointAverage u (source u q B) (e,z) ≤
      (1+endpointConstant q B*δ)*(weight volume κ e z.1*u z.1) := by
    have hχ := lineWeight_nonneg volume (source u q B) κ δ (e,z)
    have hh := weight_nonneg volume κ e z.1
    have hu0 := (h.positive_u z.1).le
    by_cases hpos : 0 < lineWeight volume (source u q B) κ δ (e,z)
    · have he := (abs_le.mp (source_endpoint_error (by omega) h.regular_u h.positive_u hq hκ hκ1 hδ hpos)).2
      have hr := (sourceRoot_bounds h.positive_u hq hz).2
      change sourceRoot q B z ≤ u z.1 at hr
      have hε : endpointConstant q B*δ*d z.1*u z.1 ≤ endpointConstant q B*δ*u z.1 := by
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (d_le_one z.1) (mul_nonneg hc hδ)) hu0 |>.trans_eq (by ring)
      have hle : endpointAverage u (source u q B) (e,z) ≤ (1+endpointConstant q B*δ)*u z.1 := by
        change endpointAverage u (source u q B) (e,z)-sourceRoot q B z ≤ _ at he
        nlinarith
      calc
        _ ≤ lineWeight volume (source u q B) κ δ (e,z)*((1+endpointConstant q B*δ)*u z.1) :=
          mul_le_mul_of_nonneg_left hle hχ
        _ ≤ weight volume κ e z.1*((1+endpointConstant q B*δ)*u z.1) :=
          mul_le_mul_of_nonneg_right (lineWeight_le volume _ _ _ _) (by positivity)
        _ = _ := by ring
    · rw [le_antisymm (not_lt.mp hpos) hχ,zero_mul]
      positivity
  calc
    _ ≤ ∫⁻ z, ENNReal.ofReal ((1+endpointConstant q B*δ)*(weight volume κ e z.1*u z.1))
        ∂layerMeasure volume (source u q B) := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem (measurableSet_sourceSubgraph hfM)] with z hz
      exact ENNReal.ofReal_le_ofReal (hpoint z hz)
    _ = _ := by
      simp_rw [ENNReal.ofReal_mul (show 0 ≤ 1+endpointConstant q B*δ by positivity)]
      rw [lintegral_const_mul _ (by fun_prop),lintegral_weight_layer h.continuous_u.measurable
        (fun x => (h.positive_u x).le) hfM hm (weight_nonneg volume κ e)]

lemma IsSolution_endpointIntegral_finite {n : ℕ} (hn : 2 ≤ n) {p q A B κ δ : ℝ}
    {u v : Space n → ℝ} (h : IsSolution n p q A B u v) (hq : 0 < q)
    (hκ : 0 < κ) (hκ1 : κ ≤ 1) (hδ : 0 ≤ δ) (e : sphere (0:Space n) 1) :
    endpointIntegral u (source u q B) κ δ e ≠ ⊤ := by
  have : Nontrivial (Space n) := Module.nontrivial_of_finrank_pos (R := ℝ) (by simp; omega)
  exact ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    (h.weightedEnergyN_finite hn (continuous_weight volume hκ hκ1 e) (compactSupport_weight κ e)))
    (IsSolution_endpointIntegral_bound hn h hq hκ hκ1 hδ e)

lemma IsSolution_integrated_pressure_recovery {n : ℕ} (hn : 2 ≤ n) {p q A B κ δ : ℝ}
    {u v : Space n → ℝ} (h : IsSolution n p q A B u v) (hq : 0 < q)
    (hκ : 0 < κ) (hκ1 : κ ≤ 1) (hδ : 0 ≤ δ) (e : sphere (0:Space n) 1) :
    ENNReal.ofReal (1/(q+1))*weightedEnergyN (weight volume κ e) u q B+
      endpointIntegral u (source u q B) κ δ e ≤
      positionIntegral u (source u q B) κ δ e+lossIntegral u (source u q B) κ δ e+
      ENNReal.ofReal (endpointConstant q B*δ)*weightedEnergyN (fun x => d x*weight volume κ e x) u q B := by
  have : Nontrivial (Space n) := Module.nontrivial_of_finrank_pos (R := ℝ) (by simp; omega)
  have huM := h.continuous_u.measurable
  have hfM := measurable_source h.continuous_u q B
  have hf := isOpen_source_subgraph h.regular_u h.positive_u q B
  have hm := (continuous_weight volume hκ hκ1 e).measurable
  have hmχ : Measurable (fun z : Space n × ℝ => lineWeight volume (source u q B) κ δ (e,z)) :=
    (measurable_lineWeight volume hf hκ hκ1 δ).comp (measurable_const.prodMk measurable_id)
  have hlo := measurable_lowerPoint hf
  have hhi := measurable_upperPoint hf
  have hd : Measurable (d : Space n → ℝ) := continuous_d.measurable
  have hc := endpointConstant_nonneg q B
  have hrec := lintegral_mono_ae (μ := layerMeasure volume (source u q B)) (show ∀ᵐ z ∂layerMeasure volume (source u q B),
      ENNReal.ofReal (weight volume κ e z.1*(u z.1-sourceRoot q B z))+
        ENNReal.ofReal (lineWeight volume (source u q B) κ δ (e,z)*endpointAverage u (source u q B) (e,z)) ≤
      ENNReal.ofReal (lineWeight volume (source u q B) κ δ (e,z)*u z.1)+
        ENNReal.ofReal ((weight volume κ e z.1-lineWeight volume (source u q B) κ δ (e,z))*u z.1)+
        ENNReal.ofReal (endpointConstant q B*δ*d z.1*weight volume κ e z.1*u z.1) from by
    filter_upwards [ae_restrict_mem (measurableSet_sourceSubgraph hfM)] with z hz
    exact source_pressure_recovery_pointwise (by omega) h.regular_u h.positive_u hq hκ hκ1 hδ e hz)
  rw [lintegral_add_left (by fun_prop),lintegral_add_left (by fun_prop),lintegral_add_left (by fun_prop),
    lintegral_pressure_root huM h.positive_u hq hfM hm (weight_nonneg volume κ e)] at hrec
  change _ ≤ positionIntegral u (source u q B) κ δ e+lossIntegral u (source u q B) κ δ e+_ at hrec
  convert hrec using 1
  congr 1
  have he (z : Space n × ℝ) : ENNReal.ofReal (endpointConstant q B*δ*d z.1*weight volume κ e z.1*u z.1) =
      ENNReal.ofReal (endpointConstant q B*δ)*ENNReal.ofReal ((d z.1*weight volume κ e z.1)*u z.1) := by
    rw [← ENNReal.ofReal_mul (mul_nonneg hc hδ)]; congr 1; ring
  simp_rw [he]
  rw [lintegral_const_mul _ (by fun_prop),
    lintegral_weight_layer huM (fun x => (h.positive_u x).le) hfM (by fun_prop)
      (fun x => mul_nonneg (d_nonneg x) (weight_nonneg volume κ e x))]

end HenonLaneEmden.SpatialComponents
end
end IntegratedRecovery

end OAI
end

section
-- module Solutions.OAIQW_HenonLaneEmden.PDEPressure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section PDEPressure

open MeasureTheory Set Metric
open scoped ENNReal
noncomputable section
namespace HenonLaneEmden
open LayerTonelli

lemma lintegral_pair_interaction {n : ℕ} {f g : Space n → ℝ}
    (hf : Measurable f) (hg : Measurable g) {F : Space n × Space n → ℝ≥0∞}
    (hF : Measurable F) :
    (∫⁻ z, F (z.1.1,z.2.1)*ENNReal.ofReal (newtonKernel n (z.1.1,z.2.1))
       ∂(layerMeasure volume f).prod (layerMeasure volume g)) = ∫⁻ z, F z ∂interaction f g := by
  rw [lintegral_pair_spatial volume hf hg (F := fun z => F z*ENNReal.ofReal (newtonKernel n z)) (by fun_prop [measurable_newtonKernel,measurable_directionalFactor]),
    lintegral_interaction hf hg hF]
  apply lintegral_congr
  intro z
  ring

end HenonLaneEmden
end
end PDEPressure

end OAI
end

section
-- module Solutions.OAIQW_HenonLaneEmden.PressureMismatch
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section PressureMismatch

open MeasureTheory Set Metric
open scoped ENNReal
noncomputable section
namespace HenonLaneEmden.SpatialComponents
open Cutoff AdaptiveCap LayerTonelli

lemma weighted_potential_loss {n : ℕ} (hn : 2 ≤ n) {p q A B : ℝ}
    {u v : Space n → ℝ} (h : IsSolution n p q A B u v) (hq : 0 < q)
    (κ δ : ℝ) (e : sphere (0:Space n) 1) (z : Space n × ℝ) :
    ENNReal.ofReal (weight volume κ e z.1-lineWeight volume (source u q B) κ δ (e,z))*
        potential volume (fun z => ENNReal.ofReal (newtonKernel n z)) (source v p A) z.1 =
      ENNReal.ofReal ((weight volume κ e z.1-lineWeight volume (source u q B) κ δ (e,z))*u z.1) := by
  have hnχ := sub_nonneg.mpr (lineWeight_le volume (source u q B) κ δ (e,z))
  by_cases hx : z.1 = 0
  · have hh : weight volume κ e z.1 = 0 := weight_inner volume κ e (by simp [hx])
    have hχ : lineWeight volume (source u q B) κ δ (e,z) = 0 :=
      le_antisymm ((lineWeight_le volume _ _ _ _).trans_eq hh) (lineWeight_nonneg volume _ _ _ _)
    simp [hh,hχ]
  · rw [h.newton_potential_u hn hq hx,ENNReal.ofReal_mul hnχ]

lemma IsSolution_pairMismatch_bound {n : ℕ} (hn : 3 ≤ n) {p q A B κ δ : ℝ}
    {u v : Space n → ℝ} (h : IsSolution n p q A B u v) (hp : 0 < p) (hq : 0 < q)
    (hκ : 0 < κ) (hκ1 : κ ≤ 1) (e : sphere (0:Space n) 1) :
    pairMismatchIntegral (source u q B) (source v p A) κ δ e ≤
      capMismatchIntegral (source u q B) (source v p A) κ e+
      (lossIntegral u (source u q B) κ δ e+lossIntegral v (source v p A) κ δ e) := by
  have : Nontrivial (Space n) := Module.nontrivial_of_finrank_pos (R := ℝ) (by simp; omega)
  have hf := isOpen_source_subgraph h.regular_u h.positive_u q B
  have hg := isOpen_source_subgraph h.regular_v h.positive_v p A
  have hfM := measurable_source h.continuous_u q B
  have hgM := measurable_source h.continuous_v p A
  have hm1 : Measurable (fun z : Space n × ℝ => lineWeight volume (source u q B) κ δ (e,z)) :=
    (measurable_lineWeight volume hf hκ hκ1 δ).comp (measurable_const.prodMk measurable_id)
  have hm2 : Measurable (fun z : Space n × ℝ => lineWeight volume (source v p A) κ δ (e,z)) :=
    (measurable_lineWeight volume hg hκ hκ1 δ).comp (measurable_const.prodMk measurable_id)
  have hh : Measurable (weight volume κ e : Space n → ℝ) := (continuous_weight volume hκ hκ1 e).measurable
  let lf (z : Space n × ℝ) := weight volume κ e z.1-lineWeight volume (source u q B) κ δ (e,z)
  let lg (z : Space n × ℝ) := weight volume κ e z.1-lineWeight volume (source v p A) κ δ (e,z)
  have hlf (z) : 0 ≤ lf z := sub_nonneg.mpr (lineWeight_le volume _ _ _ _)
  have hlg (z) : 0 ≤ lg z := sub_nonneg.mpr (lineWeight_le volume _ _ _ _)
  have hlfM : Measurable lf := by unfold lf; fun_prop
  have hlgM : Measurable lg := by unfold lg; fun_prop
  have hpoint (z : (Space n × ℝ) × (Space n × ℝ)) :
      ENNReal.ofReal (|lineWeight volume (source u q B) κ δ (e,z.1)-lineWeight volume (source v p A) κ δ (e,z.2)| *
        newtonKernel n (z.1.1,z.2.1)) ≤
      ENNReal.ofReal (|weight volume κ e z.1.1-weight volume κ e z.2.1|)*ENNReal.ofReal (newtonKernel n (z.1.1,z.2.1))+
        (ENNReal.ofReal (lf z.1)+ENNReal.ofReal (lg z.2))*ENNReal.ofReal (newtonKernel n (z.1.1,z.2.1)) := by
    rw [← add_mul,← ENNReal.ofReal_add (hlf _) (hlg _),← ENNReal.ofReal_add (abs_nonneg _) (add_nonneg (hlf _) (hlg _)),
      ← ENNReal.ofReal_mul (add_nonneg (abs_nonneg _) (add_nonneg (hlf _) (hlg _)))]
    apply ENNReal.ofReal_le_ofReal
    apply mul_le_mul_of_nonneg_right _ (newtonKernel_nonneg hn _)
    apply abs_le.mpr
    have h1 := le_abs_self (weight volume κ e z.1.1-weight volume κ e z.2.1)
    have h2 := neg_le_abs (weight volume κ e z.1.1-weight volume κ e z.2.1)
    dsimp [lf,lg] at *
    have h3 := lineWeight_le volume (source u q B) κ δ (e,z.1)
    have h4 := lineWeight_le volume (source v p A) κ δ (e,z.2)
    constructor <;> linarith
  calc
    _ ≤ ∫⁻ z, ENNReal.ofReal (|weight volume κ e z.1.1-weight volume κ e z.2.1|)*ENNReal.ofReal (newtonKernel n (z.1.1,z.2.1))+
        (ENNReal.ofReal (lf z.1)+ENNReal.ofReal (lg z.2))*ENNReal.ofReal (newtonKernel n (z.1.1,z.2.1))
        ∂(layerMeasure volume (source u q B)).prod (layerMeasure volume (source v p A)) := lintegral_mono hpoint
    _ = _ := by
      rw [lintegral_add_left (by fun_prop [measurable_newtonKernel]),
        lintegral_pair_interaction hfM hgM (F := fun z => ENNReal.ofReal (|weight volume κ e z.1-weight volume κ e z.2|)) (by fun_prop),
        lintegral_pair_weight_sum volume hfM hgM (measurable_newtonKernel n).ennreal_ofReal
          (fun x y => congrArg ENNReal.ofReal (newtonKernel_symm n x y)) hlfM.ennreal_ofReal hlgM.ennreal_ofReal]
      dsimp only [lf,lg]
      simp_rw [weighted_potential_loss (by omega) h hq κ δ e,weighted_potential_loss (by omega) h.swap hp κ δ e]
      rfl

end HenonLaneEmden.SpatialComponents
end
end PressureMismatch

end OAI
end

section
-- module Solutions.OAIQW_HenonLaneEmden.DirectionalPressure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section DirectionalPressure

open MeasureTheory Set Metric
open scoped ENNReal
noncomputable section
namespace HenonLaneEmden.SpatialComponents
open Cutoff AdaptiveCap LayerPressure

lemma IsSolution_directional_pressure {n : ℕ} (hn : 3 ≤ n) {p q A B κ δ : ℝ}
    {u v : Space n → ℝ} (h : IsSolution n p q A B u v) (hp : 0 < p) (hq : 0 < q)
    (hκ : 0 < κ) (hκ1 : κ ≤ 1) (hδ : 0 ≤ δ) (e : sphere (0:Space n) 1) :
    ENNReal.ofReal (1/(q+1))*weightedEnergyN (weight volume κ e) u q B+
      ENNReal.ofReal (1/(p+1))*weightedEnergyN (weight volume κ e) v p A ≤
      capPressureIntegral (source u q B) (source v p A) κ e+
      capMismatchIntegral (source u q B) (source v p A) κ e+
      2*(lossIntegral u (source u q B) κ δ e+lossIntegral v (source v p A) κ δ e)+
      (ENNReal.ofReal (endpointConstant q B*δ)*weightedEnergyN (fun x => d x*weight volume κ e x) u q B+
      ENNReal.ofReal (endpointConstant p A*δ)*weightedEnergyN (fun x => d x*weight volume κ e x) v p A) := by
  apply pressure_cancellation
    (ENNReal.add_ne_top.mpr ⟨IsSolution_endpointIntegral_finite (by omega) h hq hκ hκ1 hδ e,
      IsSolution_endpointIntegral_finite (by omega) h.swap hp hκ hκ1 hδ e⟩)
    (IsSolution_pressure_comparison hn h hp hq hκ hκ1 hδ e) _
    (IsSolution_pairMismatch_bound hn h hp hq hκ hκ1 e)
  have hf := IsSolution_integrated_pressure_recovery (by omega : 2 ≤ n) h hq hκ hκ1 hδ e
  have hg := IsSolution_integrated_pressure_recovery (by omega : 2 ≤ n) h.swap hp hκ hκ1 hδ e
  convert add_le_add hf hg using 1 <;> first | rfl | ac_rfl

end HenonLaneEmden.SpatialComponents
end
end DirectionalPressure

end OAI
end

section
-- module Solutions.OAIQW_HenonLaneEmden.AngularPressure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section AngularPressure

open MeasureTheory Set Metric
open scoped ENNReal InnerProductSpace
noncomputable section
namespace HenonLaneEmden
open Cutoff AdaptiveCap LayerTonelli

lemma integrable_cap_weight {n : ℕ} (hn : 1 ≤ n) {κ : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1) (x : Space n) :
    Integrable (fun e : sphere (0:Space n) 1 => weight volume κ e x) volume.toSphere := by
  have : Nontrivial (Space n) := Module.nontrivial_of_finrank_pos (R := ℝ) (by simp; omega)
  exact (integrable_const (boundConstant volume κ)).mono' (continuous_weight_direction volume κ x).aestronglyMeasurable
    (ae_of_all _ (fun e => by rw [Real.norm_eq_abs,abs_of_nonneg (weight_nonneg volume _ _ _)]; exact weight_le_constant volume hκ hκ1 e x))

lemma lintegral_cap_weight {n : ℕ} (hn : 1 ≤ n) {κ : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1) (x : Space n) :
    (∫⁻ e : sphere (0:Space n) 1, ENNReal.ofReal (weight volume κ e x) ∂volume.toSphere) =
      ENNReal.ofReal (w n x) := by
  have : Nontrivial (Space n) := Module.nontrivial_of_finrank_pos (R := ℝ) (by simp; omega)
  rw [← ofReal_integral_eq_lintegral_ofReal (integrable_cap_weight hn hκ hκ1 x)
    (ae_of_all _ (fun e => weight_nonneg volume κ e x)),integral_weight volume hκ hκ1]
  simp only [finrank_euclideanSpace_fin]

lemma lintegral_angular_weight {n : ℕ} (hn : 1 ≤ n) {κ : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1)
    {F : Space n → ℝ} (hF : Measurable F) :
    (∫⁻ e : sphere (0:Space n) 1, ∫⁻ x, ENNReal.ofReal (weight volume κ e x)*ENNReal.ofReal (F x) ∂volume
      ∂volume.toSphere) = ∫⁻ x, ENNReal.ofReal (w n x)*ENNReal.ofReal (F x) := by
  have : Nontrivial (Space n) := Module.nontrivial_of_finrank_pos (R := ℝ) (by simp; omega)
  have hM := (measurable_weight volume hκ hκ1).ennreal_ofReal.mul (hF.comp measurable_snd).ennreal_ofReal
  rw [lintegral_lintegral_swap hM.aemeasurable]
  apply lintegral_congr
  intro x
  rw [lintegral_mul_const _ (continuous_weight_direction volume κ x).measurable.ennreal_ofReal,
    lintegral_cap_weight hn hκ hκ1]

lemma lintegral_angular_energy {n : ℕ} (hn : 1 ≤ n) {κ : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1)
    {u : Space n → ℝ} (hu : Continuous u) (q B : ℝ) :
    (∫⁻ e : sphere (0:Space n) 1, weightedEnergyN (weight volume κ e) u q B ∂volume.toSphere) =
      weightedEnergyN (w n) u q B := by
  unfold weightedEnergyN
  simp_rw [mul_assoc,ENNReal.ofReal_mul (weight_nonneg volume κ _ _)]
  simp_rw [ENNReal.ofReal_mul (w_nonneg n _)]
  exact lintegral_angular_weight hn hκ hκ1 ((measurable_source hu q B).mul hu.measurable)

end HenonLaneEmden
end
end AngularPressure

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

end HenonLaneEmden
end
end FarInteraction

end OAI
end

section
-- module Solutions.OAIQW_HenonLaneEmden.AngularMeasurability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section AngularMeasurability

open MeasureTheory Set Metric
open scoped ENNReal
noncomputable section
namespace HenonLaneEmden
open Cutoff AdaptiveCap SpatialComponents LayerTonelli

lemma measurable_cap_energy {n : ℕ} (hn : 1 ≤ n) {κ : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1)
    {u : Space n → ℝ} (hu : Continuous u) (q B : ℝ) :
    Measurable (fun e : sphere (0:Space n) 1 => weightedEnergyN (weight volume κ e) u q B) := by
  have : Nontrivial (Space n) := Module.nontrivial_of_finrank_pos (R := ℝ) (by simp; omega)
  have hm : Measurable (fun z : sphere (0:Space n) 1 × Space n =>
      ENNReal.ofReal (weight volume κ z.1 z.2*source u q B z.2*u z.2)) :=
    (((measurable_weight volume hκ hκ1).mul ((measurable_source hu q B).comp measurable_snd)).mul
      (hu.measurable.comp measurable_snd)).ennreal_ofReal
  exact hm.lintegral_prod_right

lemma measurable_cap_d_energy {n : ℕ} (hn : 1 ≤ n) {κ : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1)
    {u : Space n → ℝ} (hu : Continuous u) (q B : ℝ) :
    Measurable (fun e : sphere (0:Space n) 1 => weightedEnergyN (fun x => d x*weight volume κ e x) u q B) := by
  have : Nontrivial (Space n) := Module.nontrivial_of_finrank_pos (R := ℝ) (by simp; omega)
  have hm : Measurable (fun z : sphere (0:Space n) 1 × Space n =>
      ENNReal.ofReal ((d z.2*weight volume κ z.1 z.2)*source u q B z.2*u z.2)) :=
    (((((continuous_d (E := Space n)).measurable.comp measurable_snd).mul (measurable_weight volume hκ hκ1)).mul
      ((measurable_source hu q B).comp measurable_snd)).mul (hu.measurable.comp measurable_snd)).ennreal_ofReal
  exact hm.lintegral_prod_right

lemma measurable_cap_pressure {n : ℕ} (hn : 1 ≤ n) {κ : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1) (f g : Space n → ℝ) :
    Measurable (capPressureIntegral f g κ) := by
  have : Nontrivial (Space n) := Module.nontrivial_of_finrank_pos (R := ℝ) (by simp; omega)
  have hm : Measurable (fun z : sphere (0:Space n) 1 × (Space n × Space n) =>
      ENNReal.ofReal (((n:ℝ)-2)*weight volume κ z.1 z.2.1*directionalFactor z.1 z.2)) := by
    have hw : Measurable (fun z : sphere (0:Space n) 1 × (Space n × Space n) => weight volume κ z.1 z.2.1) :=
      (measurable_weight (volume : Measure (Space n)) hκ hκ1).comp (measurable_fst.prodMk measurable_snd.fst)
    unfold directionalFactor
    fun_prop
  exact hm.lintegral_prod_right

lemma measurable_cap_mismatch {n : ℕ} (hn : 1 ≤ n) {κ : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1) (f g : Space n → ℝ) :
    Measurable (capMismatchIntegral f g κ) := by
  have : Nontrivial (Space n) := Module.nontrivial_of_finrank_pos (R := ℝ) (by simp; omega)
  have hw := measurable_weight (volume : Measure (Space n)) hκ hκ1
  have hm : Measurable (fun z : sphere (0:Space n) 1 × (Space n × Space n) =>
      ENNReal.ofReal (|weight volume κ z.1 z.2.1-weight volume κ z.1 z.2.2|)) :=
    ((hw.comp (measurable_fst.prodMk measurable_snd.fst)).sub
      (hw.comp (measurable_fst.prodMk measurable_snd.snd))).abs.ennreal_ofReal
  exact hm.lintegral_prod_right

lemma measurable_cap_loss {n : ℕ} (hn : 1 ≤ n) {κ δ : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1) {f u : Space n → ℝ}
    (hu : Measurable u) (hfo : IsOpen {z : Space n × ℝ | 0 < z.2 ∧ z.2 < f z.1}) :
    Measurable (lossIntegral u f κ δ) := by
  have : Nontrivial (Space n) := Module.nontrivial_of_finrank_pos (R := ℝ) (by simp; omega)
  have hm : Measurable (fun z : sphere (0:Space n) 1 × (Space n × ℝ) =>
      ENNReal.ofReal ((weight volume κ z.1 z.2.1-lineWeight volume f κ δ z)*u z.2.1)) :=
    ((((measurable_weight volume hκ hκ1).comp (measurable_fst.prodMk measurable_snd.fst)).sub
      (measurable_lineWeight volume hfo hκ hκ1 δ)).mul (hu.comp measurable_snd.fst)).ennreal_ofReal
  exact hm.lintegral_prod_right

lemma lintegral_angular_d_energy {n : ℕ} (hn : 1 ≤ n) {κ : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1)
    {u : Space n → ℝ} (hu : Continuous u) (q B : ℝ) :
    (∫⁻ e : sphere (0:Space n) 1, weightedEnergyN (fun x => d x*weight volume κ e x) u q B ∂volume.toSphere) =
      weightedEnergyN (fun x => d x*w n x) u q B := by
  unfold weightedEnergyN
  have h1 (e : sphere (0:Space n) 1) (x : Space n) :
      (d x*weight volume κ e x)*source u q B x*u x=weight volume κ e x*(d x*source u q B x*u x) := by ring
  have h2 (x : Space n) : (d x*w n x)*source u q B x*u x=w n x*(d x*source u q B x*u x) := by ring
  simp_rw [h1,h2,ENNReal.ofReal_mul (weight_nonneg volume κ _ _),ENNReal.ofReal_mul (w_nonneg n _)]
  exact lintegral_angular_weight hn hκ hκ1
    (((continuous_d (E := Space n)).measurable.mul (measurable_source hu q B)).mul hu.measurable)

end HenonLaneEmden
end
end AngularMeasurability

end OAI
end

section
-- module Solutions.OAIQW_HenonLaneEmden.IntegratedPressure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uα

section IntegratedPressure

open MeasureTheory Set Metric
open scoped ENNReal
noncomputable section
namespace HenonLaneEmden
open Cutoff AdaptiveCap SpatialComponents LayerTonelli

lemma integrate_pressure_sum {α : Type uα} [MeasurableSpace α] {μ : Measure α}
    {F G P Q L J D H : α → ℝ≥0∞} (hF : Measurable F) (hG : Measurable G)
    (hP : Measurable P) (hQ : Measurable Q) (hL : Measurable L) (hJ : Measurable J)
    (hD : Measurable D) (hH : Measurable H) {a b c d : ℝ≥0∞}
    (hh : ∀ x, a*F x+b*G x ≤ P x+Q x+2*(L x+J x)+(c*D x+d*H x)) :
    a*(∫⁻ x, F x ∂μ)+b*(∫⁻ x, G x ∂μ) ≤
      (∫⁻ x, P x ∂μ)+(∫⁻ x, Q x ∂μ)+2*((∫⁻ x, L x ∂μ)+(∫⁻ x, J x ∂μ))+
        (c*(∫⁻ x, D x ∂μ)+d*(∫⁻ x, H x ∂μ)) := by
  have hPQ : Measurable (fun x => P x+Q x) := hP.add hQ
  have hLJ : Measurable (fun x => L x+J x) := hL.add hJ
  have hAll : Measurable (fun x => P x+Q x+2*(L x+J x)) := hPQ.add (hLJ.const_mul 2)
  have hb := lintegral_mono (μ := μ) hh
  rw [lintegral_add_left (hF.const_mul a),lintegral_const_mul _ hF,lintegral_const_mul _ hG,
    lintegral_add_left hAll,
    lintegral_add_left hPQ,lintegral_add_left hP,
    lintegral_const_mul _ hLJ,lintegral_add_left hL,
    lintegral_add_left (hD.const_mul c),lintegral_const_mul _ hD,lintegral_const_mul _ hH] at hb
  exact hb

lemma IsSolution.integrated_directional_pressure_oai {n : ℕ} (hn : 3 ≤ n) {p q A B κ δ : ℝ}
    {u v : Space n → ℝ} (h : IsSolution n p q A B u v) (hp : 0 < p) (hq : 0 < q)
    (hκ : 0 < κ) (hκ1 : κ ≤ 1) (hδ : 0 ≤ δ) :
    ENNReal.ofReal (1/(q+1))*weightedEnergyN (w n) u q B+
      ENNReal.ofReal (1/(p+1))*weightedEnergyN (w n) v p A ≤
      (∫⁻ e : sphere (0:Space n) 1, capPressureIntegral (source u q B) (source v p A) κ e ∂volume.toSphere)+
      (∫⁻ e : sphere (0:Space n) 1, capMismatchIntegral (source u q B) (source v p A) κ e ∂volume.toSphere)+
      2*((∫⁻ e : sphere (0:Space n) 1, lossIntegral u (source u q B) κ δ e ∂volume.toSphere)+
        (∫⁻ e : sphere (0:Space n) 1, lossIntegral v (source v p A) κ δ e ∂volume.toSphere))+
      (ENNReal.ofReal (endpointConstant q B*δ)*weightedEnergyN (fun x => d x*w n x) u q B+
      ENNReal.ofReal (endpointConstant p A*δ)*weightedEnergyN (fun x => d x*w n x) v p A) := by
  have hn1 : 1 ≤ n := by omega
  have hb := integrate_pressure_sum (μ := (volume : Measure (Space n)).toSphere)
    (measurable_cap_energy hn1 hκ hκ1 h.continuous_u q B)
    (measurable_cap_energy hn1 hκ hκ1 h.continuous_v p A)
    (measurable_cap_pressure hn1 hκ hκ1 _ _) (measurable_cap_mismatch hn1 hκ hκ1 _ _)
    (measurable_cap_loss hn1 hκ hκ1 h.continuous_u.measurable (isOpen_source_subgraph h.regular_u h.positive_u q B))
    (measurable_cap_loss hn1 hκ hκ1 h.continuous_v.measurable (isOpen_source_subgraph h.regular_v h.positive_v p A))
    (measurable_cap_d_energy hn1 hκ hκ1 h.continuous_u q B)
    (measurable_cap_d_energy hn1 hκ hκ1 h.continuous_v p A)
    (IsSolution_directional_pressure hn h hp hq hκ hκ1 hδ)
  rw [lintegral_angular_energy hn1 hκ hκ1 h.continuous_u,
    lintegral_angular_energy hn1 hκ hκ1 h.continuous_v,
    lintegral_angular_d_energy hn1 hκ hκ1 h.continuous_u,
    lintegral_angular_d_energy hn1 hκ hκ1 h.continuous_v] at hb
  exact hb

end HenonLaneEmden
end
end IntegratedPressure

end OAI
end

theorem solution : type_of% @OAI.HenonLaneEmden.IsSolution.integrated_directional_pressure_oai := @OAI.HenonLaneEmden.IsSolution.integrated_directional_pressure_oai
