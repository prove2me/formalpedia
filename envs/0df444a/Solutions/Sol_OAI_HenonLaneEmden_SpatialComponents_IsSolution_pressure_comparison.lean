-- Prove2me | solution 1 for OAI.HenonLaneEmden.SpatialComponents.IsSolution_pressure_comparison
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-19T01:41:24.797365+00:00
-- url     : https://prove2.me/submissions/254cd815-6855-4827-b9c9-7d6772968fc3

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
theorem dite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : p) :
    (if hp : p then a hp else b hp) = a h := dif_pos h
theorem dite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : ¬p) :
    (if hp : p then a hp else b hp) = b h := dif_neg h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQW_HenonLaneEmden.LineCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE

section LineCoordinates

open MeasureTheory Set Metric
open scoped InnerProductSpace
noncomputable section
namespace HenonLaneEmden.LineCoordinates

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma norm_join_sq (e : sphere (0:E) 1) (z : transverse e) (s : ℝ) :
    ‖(z:E)+s • (e:E)‖^2 = ‖z‖^2+s^2 := by
  simpa only [isometry_apply,WithLp.toLp_fst,WithLp.toLp_snd,Real.norm_eq_abs,sq_abs] using
    congrArg (fun t : ℝ => t^2) ((isometry e).norm_map (WithLp.toLp 2 (z,s))) |>.trans
      (WithLp.prod_norm_sq_eq_of_L2 (WithLp.toLp 2 (z,s)))

variable [MeasurableSpace E] [BorelSpace E]

lemma measurePreserving [FiniteDimensional ℝ E] (e : sphere (0:E) 1) :
    MeasurePreserving (measurableEquiv e) (volume.prod volume) volume := by
  exact (isometry e).measurePreserving.comp (WithLp.volume_preserving_toLp (transverse e) ℝ)

lemma continuous_measurableEquiv (e : sphere (0:E) 1) : Continuous (measurableEquiv e) := by
  change Continuous (fun z : transverse e × ℝ => (z.1:E)+z.2 • (e:E))
  fun_prop

lemma distance_sq (e : sphere (0:E) 1) (z z' : transverse e × ℝ) :
    dist (measurableEquiv e z) (measurableEquiv e z')^2 = ‖z.1-z'.1‖^2+(z.2-z'.2)^2 := by
  rw [dist_eq_norm]
  have he : measurableEquiv e z-measurableEquiv e z' = ((z.1-z'.1 : transverse e):E)+(z.2-z'.2) • (e:E) := by
    simp only [measurableEquiv_apply,Submodule.coe_sub,sub_smul]; abel
  rw [he,norm_join_sq]

lemma parallel (e : sphere (0:E) 1) (z : transverse e × ℝ) (s : ℝ) :
    measurableEquiv e (z.1,z.2+s) = measurableEquiv e z+s • (e:E) := by
  simp only [measurableEquiv_apply,add_smul]; abel

omit [MeasurableSpace E] [BorelSpace E] in
lemma transverse_nontrivial [FiniteDimensional ℝ E] (h : 2 ≤ Module.finrank ℝ E)
    (e : sphere (0:E) 1) : Nontrivial (transverse e) := by
  apply (Module.finrank_pos_iff (R := ℝ)).mp
  have he : (e:E) ≠ 0 := norm_ne_zero_iff.mp (by rw [norm_unit]; norm_num)
  have hh := (ℝ ∙ (e:E)).finrank_add_finrank_orthogonal
  rw [finrank_span_singleton he] at hh
  change 0 < Module.finrank ℝ ((ℝ ∙ (e:E))ᗮ)
  omega

end HenonLaneEmden.LineCoordinates
end
end LineCoordinates

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

lemma isOpen_shiftedLayer {U : Set ℝ} (hU : IsOpen U) : IsOpen (shiftedLayer U) :=
  hU.preimage (continuous_fst.add continuous_snd)

lemma image_relative_component {U : Set ℝ} {x : ℝ} (hx : x ∈ U) :
    (fun r : ℝ => x+r) '' connectedComponentIn {r : ℝ | (x,r) ∈ shiftedLayer U} 0 =
      connectedComponentIn U x := by
  let H := Homeomorph.addLeft x
  have hs : H '' {r : ℝ | (x,r) ∈ shiftedLayer U} = U := by
    change H '' H ⁻¹' U = U
    exact image_preimage_eq U H.surjective
  have hzero : 0 ∈ {r : ℝ | (x,r) ∈ shiftedLayer U} := by simpa [shiftedLayer] using hx
  have hh := H.image_connectedComponentIn hzero
  rw [hs] at hh
  change (fun r : ℝ => x+r) '' connectedComponentIn {r : ℝ | (x,r) ∈ shiftedLayer U} 0 =
    connectedComponentIn U (x+0) at hh
  simpa only [add_zero] using hh

lemma shifted_componentInf_eq {U : Set ℝ} (hU : IsOpen U) {x : ℝ} (hx : x ∈ U)
    {f : ℝ → ℝ} (hf : Continuous f) :
    componentInf (shiftedLayer U) (fun z => f (z.1+z.2)) x =
      ⨅ y ∈ connectedComponentIn U x, ENNReal.ofReal (f y) := by
  rw [componentInf_eq_component (isOpen_shiftedLayer hU) (by simpa [shiftedLayer] using hx)
    (hf.comp (continuous_const.add continuous_id)), ← image_relative_component hx, iInf_image]

lemma shifted_componentLength_eq {U : Set ℝ} (hU : IsOpen U) {x : ℝ} (hx : x ∈ U) :
    componentLength (shiftedLayer U) x = volume (connectedComponentIn U x) := by
  rw [← volume_component_all (isOpen_shiftedLayer hU) (by simpa [shiftedLayer] using hx),
      ← image_relative_component hx]
  have hm := measure_preimage_add volume x
    ((fun r : ℝ => x+r) '' connectedComponentIn {r : ℝ | (x,r) ∈ shiftedLayer U} 0)
  rw [preimage_image_eq _ (by intro a b hab; linarith : Function.Injective (fun r : ℝ => x+r))] at hm
  exact hm


/-- A connected real set of finite length is bounded; this rules out every
unbounded line-component case without choosing fictitious infinite endpoints. -/
lemma bounded_of_connected_volume_ne_top {I : Set ℝ} (hc : IsConnected I)
    (hv : volume I ≠ ⊤) : BddBelow I ∧ BddAbove I := by
  obtain ⟨x,hx⟩ := hc.nonempty
  constructor
  · by_contra h
    have hs : Iio x ⊆ I := by
      intro z hz
      obtain ⟨y,hy,hyz⟩ := not_bddBelow_iff.mp h z
      exact hc.Icc_subset hy hx ⟨hyz.le,hz.le⟩
    have hm := measure_mono (μ := (volume : Measure ℝ)) hs
    rw [Real.volume_Iio] at hm
    exact hv (top_le_iff.mp hm)
  · by_contra h
    have hs : Ioi x ⊆ I := by
      intro z hz
      obtain ⟨y,hy,hzy⟩ := not_bddAbove_iff.mp h z
      exact hc.Icc_subset hx hy ⟨hz.le,hzy.le⟩
    have hm := measure_mono (μ := (volume : Measure ℝ)) hs
    rw [Real.volume_Ioi] at hm
    exact hv (top_le_iff.mp hm)

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

lemma setWeight_pos_bounded {h d : ℝ → ℝ} {δ : ℝ} {I : Set ℝ}
    (hc : IsConnected I) (hp : 0 < (setWeight h d δ I).toReal) :
    BddBelow I ∧ BddAbove I := by
  apply bounded_of_connected_volume_ne_top hc
  unfold setWeight at hp
  split_ifs at hp with hI
  · exact hI.2.1
  · simp only [ENNReal.toReal_zero,lt_self_iff_false] at hp

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

lemma shifted_componentWeight_eq {U : Set ℝ} (hU : IsOpen U)
    {h d : ℝ → ℝ} (hh : Continuous h) (hd : Continuous d) (δ x : ℝ) :
    componentWeight (shiftedLayer U) (fun z => h (z.1+z.2))
      (fun z => d (z.1+z.2)) δ x = setWeight h d δ (connectedComponentIn U x) := by
  by_cases hx : x ∈ U
  · have hne : (connectedComponentIn U x).Nonempty := ⟨x,mem_connectedComponentIn hx⟩
    have hpx : (x,0) ∈ shiftedLayer U := by simpa [shiftedLayer] using hx
    simp only [componentWeight,setWeight,hpx,hne,true_and,
      shifted_componentLength_eq hU hx,shifted_componentInf_eq hU hx hh,
      shifted_componentInf_eq hU hx hd,setInf]
  · simp [componentWeight,shiftedLayer,hx,connectedComponentIn_eq_empty hx,setWeight]

section Parameter
variable {P : Type uP} [TopologicalSpace P]

lemma isOpen_relativeLayer {U : Set (P × ℝ)} (hU : IsOpen U) : IsOpen (relativeLayer U) :=
  hU.preimage ((continuous_fst.fst).prodMk (continuous_fst.snd.add continuous_snd))

lemma relative_componentWeight_eq {U : Set (P × ℝ)} (hU : IsOpen U)
    {h d : P × ℝ → ℝ} (hh : Continuous h) (hd : Continuous d) (δ : ℝ) (p : P × ℝ) :
    componentWeight (relativeLayer U) (fun z => h (z.1.1,z.1.2+z.2))
      (fun z => d (z.1.1,z.1.2+z.2)) δ p =
    setWeight (fun s => h (p.1,s)) (fun s => d (p.1,s)) δ
      (connectedComponentIn {s | (p.1,s) ∈ U} p.2) := by
  have he := shifted_componentWeight_eq (isOpen_section hU p.1)
    (h := fun s => h (p.1,s)) (d := fun s => d (p.1,s))
    (hh.comp (continuous_const.prodMk continuous_id))
    (hd.comp (continuous_const.prodMk continuous_id)) δ p.2
  simpa only [componentWeight,componentLength,forwardExit,backwardExit,componentInf,
    SegmentInside,relativeLayer,shiftedLayer,Set.mem_ofPred] using he


variable [MeasurableSpace P] [BorelSpace P]
lemma measurable_parametric_setWeight {U : Set (P × ℝ)} (hU : IsOpen U)
    {h d : P × ℝ → ℝ} (hh : Continuous h) (hd : Continuous d) (δ : ℝ) :
    Measurable (fun p : P × ℝ =>
      setWeight (fun s => h (p.1,s)) (fun s => d (p.1,s)) δ
        (connectedComponentIn {s | (p.1,s) ∈ U} p.2)) := by
  have he : (fun p : P × ℝ =>
      setWeight (fun s => h (p.1,s)) (fun s => d (p.1,s)) δ
        (connectedComponentIn {s | (p.1,s) ∈ U} p.2)) =
      componentWeight (relativeLayer U) (fun z => h (z.1.1,z.1.2+z.2))
        (fun z => d (z.1.1,z.1.2+z.2)) δ := by
    funext p
    exact (relative_componentWeight_eq hU hh hd δ p).symm
  rw [he]
  exact measurable_componentWeight (isOpen_relativeLayer hU)
    (hh.measurable.comp (measurable_fst.fst.prodMk (measurable_fst.snd.add measurable_snd)))
    (hd.measurable.comp (measurable_fst.fst.prodMk (measurable_fst.snd.add measurable_snd))) δ

end Parameter

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
-- module Solutions.OAIQW_HenonLaneEmden.Intervals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Intervals
open MeasureTheory Set Filter Topology
namespace HenonLaneEmden.IntervalGeometry


lemma primitive_hasDerivAt {k : ℝ → ℝ} (hk : Continuous k) (x : ℝ) :
    HasDerivAt (fun s => ∫ t in (0 : ℝ)..s, k t) (k x) x :=
  intervalIntegral.integral_hasDerivAt_right (hk.intervalIntegrable _ _)
    hk.aestronglyMeasurable.stronglyMeasurableAtFilter hk.continuousAt

lemma segmentIntegral_eq_primitive {k : ℝ → ℝ} (hk : Continuous k) (r x : ℝ) :
    segmentIntegral k r x = (∫ t in (0 : ℝ)..x + r, k t) -
      (∫ t in (0 : ℝ)..x - r, k t) := by
  unfold segmentIntegral
  have h := intervalIntegral.integral_add_adjacent_intervals
    (hk.intervalIntegrable (μ := volume) 0 (x - r)) (hk.intervalIntegrable (x - r) (x + r))
  linarith

lemma segmentIntegral_hasDerivAt {k : ℝ → ℝ} (hk : Continuous k) (r x : ℝ) :
    HasDerivAt (segmentIntegral k r) (k (x + r) - k (x - r)) x := by
  have h₁ := (primitive_hasDerivAt hk (x + r)).comp x ((hasDerivAt_id x).add_const r)
  have h₂ := (primitive_hasDerivAt hk (x - r)).comp x ((hasDerivAt_id x).sub_const r)
  have heq : segmentIntegral k r = (fun y =>
      (∫ t in (0 : ℝ)..y + r, k t) - (∫ t in (0 : ℝ)..y - r, k t)) :=
    funext (segmentIntegral_eq_primitive hk r)
  rw [heq]
  convert h₁.sub h₂ using 1 <;> first | rfl | simp only [mul_one]

lemma segmentIntegral_continuous {k : ℝ → ℝ} (hk : Continuous k) (r : ℝ) :
    Continuous (segmentIntegral k r) :=
  continuous_iff_continuousAt.mpr (fun x => (segmentIntegral_hasDerivAt hk r x).continuousAt)

lemma segmentIntegral_even {k : ℝ → ℝ} (heven : ∀ x, k (-x) = k x) (r x : ℝ) :
    segmentIntegral k r (-x) = segmentIntegral k r x := by
  unfold segmentIntegral
  have h := intervalIntegral.integral_comp_neg (a := x-r) (b := x+r) k
  simp only [heven] at h
  rw [show -x - r = -(x + r) by ring, show -x + r = -(x - r) by ring]
  exact h.symm

lemma segmentIntegral_antitoneOn {k : ℝ → ℝ} (hk : Continuous k)
    (hanti : ∀ {x y : ℝ}, |x| ≤ |y| → k y ≤ k x) {r : ℝ} (hr : 0 ≤ r) :
    AntitoneOn (segmentIntegral k r) (Ici 0) := by
  apply antitoneOn_of_deriv_nonpos (convex_Ici 0) (segmentIntegral_continuous hk r).continuousOn
  · exact fun x _ => (segmentIntegral_hasDerivAt hk r x).differentiableAt.differentiableWithinAt
  · intro x hx
    rw [(segmentIntegral_hasDerivAt hk r x).deriv]
    apply sub_nonpos.mpr
    apply hanti
    have hx' : 0 ≤ x := le_of_lt (by simpa only [interior_Ici, mem_Ioi] using hx)
    rw [abs_of_nonneg (add_nonneg hx' hr)]
    exact abs_le.mpr ⟨by linarith, by linarith⟩

lemma segmentIntegral_abs {k : ℝ → ℝ} (heven : ∀ x, k (-x) = k x) (r x : ℝ) :
    segmentIntegral k r |x| = segmentIntegral k r x := by
  rcases le_or_gt 0 x with hx | hx
  · rw [abs_of_nonneg hx]
  · rw [abs_of_neg hx]
    exact segmentIntegral_even heven r x

lemma segmentIntegral_antitone_abs {k : ℝ → ℝ} (hk : Continuous k)
    (heven : ∀ x, k (-x) = k x)
    (hanti : ∀ {x y : ℝ}, |x| ≤ |y| → k y ≤ k x)
    {r : ℝ} (hr : 0 ≤ r) {x y : ℝ} (hxy : |x| ≤ |y|) :
    segmentIntegral k r y ≤ segmentIntegral k r x := by
  rw [← segmentIntegral_abs heven r y, ← segmentIntegral_abs heven r x]
  exact segmentIntegral_antitoneOn hk hanti hr (abs_nonneg x) (abs_nonneg y) hxy

lemma integral_translate_eq_segment (k : ℝ → ℝ) (c d x : ℝ) :
    (∫ y in c..d, k (x - y)) =
      segmentIntegral k ((d-c)/2) (x-(c+d)/2) := by
  rw [intervalIntegral.integral_comp_sub_left]
  unfold segmentIntegral
  congr 1 <;> ring

/-- The drift of the two interval midpoints has the opposite sign to the
    integrated endpoint difference of a symmetric decreasing kernel. -/
lemma midpoint_endpoint_sign {k : ℝ → ℝ} (hk : Continuous k)
    (heven : ∀ x, k (-x) = k x)
    (hanti : ∀ {x y : ℝ}, |x| ≤ |y| → k y ≤ k x)
    {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d) :
    ((a+b)/2-(c+d)/2) * (∫ y in c..d, (k (b-y)-k (a-y))) ≤ 0 := by
  have hkb : Continuous (fun y : ℝ => k (b-y)) := hk.comp (continuous_const.sub continuous_id)
  have hka : Continuous (fun y : ℝ => k (a-y)) := hk.comp (continuous_const.sub continuous_id)
  rw [intervalIntegral.integral_sub (hkb.intervalIntegrable c d) (hka.intervalIntegrable c d)]
  rw [integral_translate_eq_segment k c d b, integral_translate_eq_segment k c d a]
  have hr : 0 ≤ (d-c)/2 := by linarith
  rcases le_or_gt 0 ((a+b)/2-(c+d)/2) with hm | hm
  · apply mul_nonpos_of_nonneg_of_nonpos hm
    apply sub_nonpos.mpr
    apply segmentIntegral_antitone_abs hk heven hanti hr
    rw [← sq_le_sq]
    nlinarith
  · apply mul_nonpos_of_nonpos_of_nonneg hm.le
    apply sub_nonneg.mpr
    apply segmentIntegral_antitone_abs hk heven hanti hr
    rw [← sq_le_sq]
    nlinarith




lemma base_pos {l : ℝ} (hl : 0 < l) (x : ℝ) : 0 < l ^ 2 + x ^ 2 := by
  positivity

lemma kernel_nonneg (n : ℕ) {l c : ℝ} (hc : 0 ≤ c) (h : ℝ) :
    0 ≤ kernel n l c h := by
  unfold kernel
  positivity

lemma kernel_even (n : ℕ) (l c h : ℝ) : kernel n l c (-h) = kernel n l c h := by
  simp [kernel]

lemma kernel_continuous (n : ℕ) {l : ℝ} (hl : 0 < l) (c : ℝ) :
    Continuous (kernel n l c) := by
  apply continuous_const.mul
  exact (continuous_const.add (continuous_id.pow 2)).rpow_const
    (fun x => Or.inl (ne_of_gt (base_pos hl x)))

lemma kernel_hasDerivAt (n : ℕ) {l : ℝ} (hl : 0 < l) (c h : ℝ) :
    HasDerivAt (kernel n l c)
      (-((n : ℝ) - 2) * h / (l ^ 2 + h ^ 2) * kernel n l c h) h := by
  have hd := ((((hasDerivAt_id h).pow 2).const_add (l ^ 2)).rpow_const (p := (2 - (n : ℝ)) / 2)
    (Or.inl (ne_of_gt (base_pos hl h)))).const_mul c
  convert hd using 1 <;> try rfl
  simp only [kernel, id_eq, Pi.pow_apply, Nat.cast_ofNat, Nat.reduceSub,
    pow_one, mul_one, Real.rpow_sub (base_pos hl h), Real.rpow_one]
  field_simp
  ring

lemma kernel_antitone_abs (n : ℕ) (hn : 3 ≤ n) {l c : ℝ} (hl : 0 < l)
    (hc : 0 ≤ c) {x y : ℝ} (hxy : |x| ≤ |y|) : kernel n l c y ≤ kernel n l c x := by
  apply mul_le_mul_of_nonneg_left _ hc
  apply Real.rpow_le_rpow_of_nonpos (base_pos hl x)
  · have hsq : x ^ 2 ≤ y ^ 2 := by simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg x) hxy 2
    linarith
  · have hn' : (3 : ℝ) ≤ n := by exact_mod_cast hn
    linarith




lemma boxIntegral_congr (a b c d : ℝ) {F G : ℝ → ℝ → ℝ}
    (h : ∀ x y, F x y = G x y) : boxIntegral a b c d F = boxIntegral a b c d G := by
  have heq : F = G := funext (fun x => funext (h x))
  rw [heq]

lemma boxIntegral_add (a b c d : ℝ) {F G : ℝ → ℝ → ℝ}
    (hF : Continuous F.uncurry) (hG : Continuous G.uncurry) :
    boxIntegral a b c d (fun x y => F x y + G x y) =
      boxIntegral a b c d F + boxIntegral a b c d G := by
  unfold boxIntegral
  simp_rw [intervalIntegral.integral_add
    ((hF.uncurry_left _).intervalIntegrable c d) ((hG.uncurry_left _).intervalIntegrable c d)]
  exact intervalIntegral.integral_add
    ((intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hF c d).intervalIntegrable a b)
    ((intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hG c d).intervalIntegrable a b)

lemma boxIntegral_sub (a b c d : ℝ) {F G : ℝ → ℝ → ℝ}
    (hF : Continuous F.uncurry) (hG : Continuous G.uncurry) :
    boxIntegral a b c d (fun x y => F x y - G x y) =
      boxIntegral a b c d F - boxIntegral a b c d G := by
  unfold boxIntegral
  simp_rw [intervalIntegral.integral_sub
    ((hF.uncurry_left _).intervalIntegrable c d) ((hG.uncurry_left _).intervalIntegrable c d)]
  exact intervalIntegral.integral_sub
    ((intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hF c d).intervalIntegrable a b)
    ((intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hG c d).intervalIntegrable a b)

lemma boxIntegral_const_mul (a b c d t : ℝ) (F : ℝ → ℝ → ℝ) :
    boxIntegral a b c d (fun x y => t * F x y) = t * boxIntegral a b c d F := by
  simp only [boxIntegral, intervalIntegral.integral_const_mul]

lemma boxIntegral_swap (a b c d : ℝ) {F : ℝ → ℝ → ℝ}
    (hF : Continuous F.uncurry) :
    boxIntegral a b c d F = boxIntegral c d a b (fun y x => F x y) := by
  apply intervalIntegral_intervalIntegral_swap
  exact (ContinuousOn.integrableOn_compact
    (isCompact_uIcc.prod isCompact_uIcc) hF.continuousOn).mono_set
      (Set.prod_mono uIoc_subset_uIcc uIoc_subset_uIcc)

lemma boxIntegral_nonneg {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d)
    {F : ℝ → ℝ → ℝ} (hF : ∀ x y, 0 ≤ F x y) : 0 ≤ boxIntegral a b c d F := by
  apply intervalIntegral.integral_nonneg hab
  intro x _
  exact intervalIntegral.integral_nonneg hcd (fun y _ => hF x y)

lemma endpoint_defect {k k' : ℝ → ℝ} (hk : Continuous k) (hk' : Continuous k')
    (hderiv : ∀ x, HasDerivAt k (k' x) x) (a b y : ℝ) :
    (∫ x in a..b, k (x-y)) - (b-a) * ((k (a-y) + k (b-y))/2) =
      -(∫ x in a..b, (x-(a+b)/2) * k' (x-y)) := by
  have hkxy : Continuous (fun x : ℝ => k (x-y)) := hk.comp (continuous_id.sub continuous_const)
  have hk'xy : Continuous (fun x : ℝ => k' (x-y)) := hk'.comp (continuous_id.sub continuous_const)
  have hdkxy (x : ℝ) : HasDerivAt (fun x : ℝ => k (x-y)) (k' (x-y)) x := by
    convert (hderiv (x-y)).comp x ((hasDerivAt_id x).sub_const y) using 1 <;>
      first | rfl | simp only [mul_one]
  have hparts := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    (u := fun x : ℝ => x-(a+b)/2) (v := fun x : ℝ => k (x-y))
    (u' := fun _ => 1) (v' := fun x => k' (x-y))
    (continuous_id.sub continuous_const).continuousOn hkxy.continuousOn
    (fun x _ => (hasDerivAt_id x).sub_const ((a+b)/2)) (fun x _ => hdkxy x)
    (continuous_const.intervalIntegrable a b) (hk'xy.intervalIntegrable a b)
  simp only [one_mul] at hparts
  linarith [hparts]

lemma endpoint_defect_right {k k' : ℝ → ℝ} (hk : Continuous k) (hk' : Continuous k')
    (hderiv : ∀ x, HasDerivAt k (k' x) x) (c d x : ℝ) :
    (∫ y in c..d, k (x-y)) - (d-c) * ((k (x-c) + k (x-d))/2) =
      ∫ y in c..d, (y-(c+d)/2) * k' (x-y) := by
  have hkxy : Continuous (fun y : ℝ => k (x-y)) := hk.comp (continuous_const.sub continuous_id)
  have hk'xy : Continuous (fun y : ℝ => -k' (x-y)) := (hk'.comp (continuous_const.sub continuous_id)).neg
  have hdkxy (y : ℝ) : HasDerivAt (fun y : ℝ => k (x-y)) (-k' (x-y)) y := by
    convert (hderiv (x-y)).comp y ((hasDerivAt_id y).const_sub x) using 1 <;>
      first | rfl | simp only [mul_neg, mul_one]
  have hparts := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    (u := fun y : ℝ => y-(c+d)/2) (v := fun y : ℝ => k (x-y))
    (u' := fun _ => 1) (v' := fun y => -k' (x-y))
    (continuous_id.sub continuous_const).continuousOn hkxy.continuousOn
    (fun y _ => (hasDerivAt_id y).sub_const ((c+d)/2)) (fun y _ => hdkxy y)
    (continuous_const.intervalIntegrable c d) (hk'xy.intervalIntegrable c d)
  simp only [one_mul, mul_neg, intervalIntegral.integral_neg] at hparts
  linarith [hparts]

lemma box_endpoint_defect_left {k k' : ℝ → ℝ} (hk : Continuous k) (hk' : Continuous k')
    (hderiv : ∀ x, HasDerivAt k (k' x) x) (a b c d : ℝ) :
    boxIntegral a b c d (fun x y => k (x-y) - (k (a-y)+k (b-y))/2) =
      boxIntegral a b c d (fun x y => -((x-(a+b)/2)*k' (x-y))) := by
  rw [boxIntegral_swap a b c d (by fun_prop),
    boxIntegral_swap a b c d (by fun_prop)]
  unfold boxIntegral
  apply intervalIntegral.integral_congr
  intro y _
  dsimp only
  have hkxy : Continuous (fun x : ℝ => k (x-y)) := hk.comp (continuous_id.sub continuous_const)
  rw [intervalIntegral.integral_sub (g := fun _ : ℝ => (k (a-y)+k (b-y))/2) (hkxy.intervalIntegrable a b)
    (continuous_const.intervalIntegrable a b), intervalIntegral.integral_const,
    intervalIntegral.integral_neg, smul_eq_mul]
  exact endpoint_defect hk hk' hderiv a b y

lemma box_endpoint_defect_right {k k' : ℝ → ℝ} (hk : Continuous k) (hk' : Continuous k')
    (hderiv : ∀ x, HasDerivAt k (k' x) x) (a b c d : ℝ) :
    boxIntegral a b c d (fun x y => k (x-y) - (k (x-c)+k (x-d))/2) =
      boxIntegral a b c d (fun x y => (y-(c+d)/2)*k' (x-y)) := by
  unfold boxIntegral
  apply intervalIntegral.integral_congr
  intro x _
  dsimp only
  have hkxy : Continuous (fun y : ℝ => k (x-y)) := hk.comp (continuous_const.sub continuous_id)
  rw [intervalIntegral.integral_sub (g := fun _ : ℝ => (k (x-c)+k (x-d))/2) (hkxy.intervalIntegrable c d)
    (continuous_const.intervalIntegrable c d), intervalIntegral.integral_const, smul_eq_mul]
  exact endpoint_defect_right hk hk' hderiv c d x

lemma box_midpoint_identity {k k' : ℝ → ℝ} (hk : Continuous k) (hk' : Continuous k')
    (hderiv : ∀ x, HasDerivAt k (k' x) x) (a b c d : ℝ) :
    boxIntegral a b c d (fun x y => 2*k (x-y) - (k (a-y)+k (b-y))/2 -
      (k (x-c)+k (x-d))/2) =
    boxIntegral a b c d (fun x y => -(x-y-((a+b)/2-(c+d)/2))*k' (x-y)) := by
  calc
    _ = boxIntegral a b c d (fun x y =>
        (k (x-y) - (k (a-y)+k (b-y))/2) + (k (x-y) - (k (x-c)+k (x-d))/2)) := by
          apply boxIntegral_congr; intros; ring
    _ = boxIntegral a b c d (fun x y => k (x-y) - (k (a-y)+k (b-y))/2) +
        boxIntegral a b c d (fun x y => k (x-y) - (k (x-c)+k (x-d))/2) :=
          boxIntegral_add a b c d (by fun_prop) (by fun_prop)
    _ = boxIntegral a b c d (fun x y => -((x-(a+b)/2)*k' (x-y))) +
        boxIntegral a b c d (fun x y => (y-(c+d)/2)*k' (x-y)) := by
          rw [box_endpoint_defect_left hk hk' hderiv, box_endpoint_defect_right hk hk' hderiv]
    _ = boxIntegral a b c d (fun x y =>
        -((x-(a+b)/2)*k' (x-y)) + (y-(c+d)/2)*k' (x-y)) :=
          (boxIntegral_add a b c d (by fun_prop) (by fun_prop)).symm
    _ = _ := by apply boxIntegral_congr; intros; ring


lemma box_integral_derivative {k k' : ℝ → ℝ} (hk' : Continuous k')
    (hderiv : ∀ x, HasDerivAt k (k' x) x) (a b c d : ℝ) :
    boxIntegral a b c d (fun x y => k' (x-y)) =
      ∫ y in c..d, (k (b-y)-k (a-y)) := by
  rw [boxIntegral_swap a b c d (by fun_prop)]
  unfold boxIntegral
  apply intervalIntegral.integral_congr
  intro y _
  dsimp only
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro x _
    convert (hderiv (x-y)).comp x ((hasDerivAt_id x).sub_const y) using 1 <;>
      first | rfl | simp only [mul_one]
  · exact (hk'.comp (continuous_id.sub continuous_const)).intervalIntegrable a b

lemma box_midpoint_sign {k k' : ℝ → ℝ} (hk : Continuous k) (hk' : Continuous k')
    (hderiv : ∀ x, HasDerivAt k (k' x) x)
    (heven : ∀ x, k (-x) = k x)
    (hanti : ∀ {x y : ℝ}, |x| ≤ |y| → k y ≤ k x)
    {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d) :
    ((a+b)/2-(c+d)/2) * boxIntegral a b c d (fun x y => k' (x-y)) ≤ 0 := by
  rw [box_integral_derivative hk' hderiv]
  exact midpoint_endpoint_sign hk heven hanti hab hcd

/-- General interval comparison before substituting the Newton kernel. -/
lemma box_endpoint_comparison {k k' : ℝ → ℝ} (hk : Continuous k) (hk' : Continuous k')
    (hderiv : ∀ x, HasDerivAt k (k' x) x)
    (heven : ∀ x, k (-x) = k x)
    (hanti : ∀ {x y : ℝ}, |x| ≤ |y| → k y ≤ k x)
    {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d) :
    boxIntegral a b c d (fun x y => 2*k (x-y) - (k (a-y)+k (b-y))/2 -
      (k (x-c)+k (x-d))/2) ≤
      boxIntegral a b c d (fun x y => -(x-y)*k' (x-y)) := by
  rw [box_midpoint_identity hk hk' hderiv]
  have hsplit : boxIntegral a b c d
      (fun x y => -(x-y-((a+b)/2-(c+d)/2))*k' (x-y)) =
      boxIntegral a b c d (fun x y => -(x-y)*k' (x-y)) +
      ((a+b)/2-(c+d)/2) * boxIntegral a b c d (fun x y => k' (x-y)) := by
    calc
      _ = boxIntegral a b c d (fun x y => -(x-y)*k' (x-y) +
          ((a+b)/2-(c+d)/2)*k' (x-y)) := by
            apply boxIntegral_congr; intros; ring
      _ = _ := by
        rw [boxIntegral_add a b c d (by fun_prop) (by fun_prop), boxIntegral_const_mul]
  rw [hsplit]
  linarith [box_midpoint_sign hk hk' hderiv heven hanti hab hcd]

lemma kernel_derivative_continuous (n : ℕ) {l : ℝ} (hl : 0 < l) (c : ℝ) :
    Continuous (fun h : ℝ => -((n : ℝ)-2)*h/(l^2+h^2)*kernel n l c h) := by
  apply Continuous.mul _ (kernel_continuous n hl c)
  exact (continuous_const.mul continuous_id).div
    (continuous_const.add (continuous_id.pow 2)) (fun x => ne_of_gt (base_pos hl x))

/-- The two unweighted endpoint defects are controlled by the directional interaction. -/
lemma newton_endpoint_comparison (n : ℕ) (hn : 3 ≤ n) {l C a b c d : ℝ}
    (hl : 0 < l) (hC : 0 ≤ C) (hab : a ≤ b) (hcd : c ≤ d) :
    boxIntegral a b c d (fun x y => 2*kernel n l C (x-y) -
      (kernel n l C (a-y)+kernel n l C (b-y))/2 -
      (kernel n l C (x-c)+kernel n l C (x-d))/2) ≤
      ((n : ℝ)-2)*boxIntegral a b c d
        (fun x y => (x-y)^2/(l^2+(x-y)^2)*kernel n l C (x-y)) := by
  have h := box_endpoint_comparison (kernel_continuous n hl C)
    (kernel_derivative_continuous n hl C) (kernel_hasDerivAt n hl C)
    (kernel_even n l C) (fun hxy => kernel_antitone_abs n hn hl hC hxy) hab hcd
  calc
    _ ≤ _ := h
    _ = _ := by
      rw [← boxIntegral_const_mul]
      apply boxIntegral_congr
      intro x y
      ring

lemma weighted_scalar_comparison {K EI EJ T cI cJ : ℝ}
    (hEI : 0 ≤ EI) (hEJ : 0 ≤ EJ) (hI : 0 ≤ cI) (hJ : 0 ≤ cJ)
    (hpair : 2*K-EI-EJ ≤ T) :
    (cI+cJ)*K ≤ cI*EI+cJ*EJ+min cI cJ*T+|cI-cJ| * K := by
  rcases le_total cI cJ with hij | hji
  · rw [min_eq_left hij, abs_of_nonpos (sub_nonpos.mpr hij)]
    have h := mul_le_mul_of_nonneg_left hpair hI
    have h' := mul_nonneg (sub_nonneg.mpr hij) hEJ
    nlinarith
  · rw [min_eq_right hji, abs_of_nonneg (sub_nonneg.mpr hji)]
    have h := mul_le_mul_of_nonneg_left hpair hJ
    have h' := mul_nonneg (sub_nonneg.mpr hji) hEI
    nlinarith

/-- Weighted interval comparison, with finite endpoints.  The normalizing
constant `C` may be instantiated by `1 / ((n-2) * area(S^(n-1)))`. -/
lemma bounded_weighted_interval_comparison (n : ℕ) (hn : 3 ≤ n)
    {l C a b c d cI cJ : ℝ} (hl : 0 < l) (hC : 0 ≤ C)
    (hab : a ≤ b) (hcd : c ≤ d) (hcI : 0 ≤ cI) (hcJ : 0 ≤ cJ) :
    (cI+cJ) * boxIntegral a b c d (fun x y => kernel n l C (x-y)) ≤
      cI * boxIntegral a b c d (fun _ y => (kernel n l C (a-y)+kernel n l C (b-y))/2) +
      cJ * boxIntegral a b c d (fun x _ => (kernel n l C (x-c)+kernel n l C (x-d))/2) +
      (((n : ℝ)-2)*min cI cJ) * boxIntegral a b c d
        (fun x y => (x-y)^2/(l^2+(x-y)^2)*kernel n l C (x-y)) +
      |cI-cJ| * boxIntegral a b c d (fun x y => kernel n l C (x-y)) := by
  have hk := kernel_continuous n hl C
  have hcomp := newton_endpoint_comparison n hn hl hC hab hcd
  rw [boxIntegral_sub a b c d (by fun_prop) (by fun_prop),
      boxIntegral_sub a b c d (by fun_prop) (by fun_prop), boxIntegral_const_mul] at hcomp
  have hEI : 0 ≤ boxIntegral a b c d
      (fun _ y => (kernel n l C (a-y)+kernel n l C (b-y))/2) := by
    apply boxIntegral_nonneg hab hcd
    intro x y
    exact div_nonneg (add_nonneg (kernel_nonneg n hC (a-y)) (kernel_nonneg n hC (b-y))) (by norm_num)
  have hEJ : 0 ≤ boxIntegral a b c d
      (fun x _ => (kernel n l C (x-c)+kernel n l C (x-d))/2) := by
    apply boxIntegral_nonneg hab hcd
    intro x y
    exact div_nonneg (add_nonneg (kernel_nonneg n hC (x-c)) (kernel_nonneg n hC (x-d))) (by norm_num)
  have hw := weighted_scalar_comparison hEI hEJ hcI hcJ hcomp
  nlinarith [hw]


lemma ofReal_boxIntegral {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d)
    {F : ℝ → ℝ → ℝ} (hF : Continuous F.uncurry) (hpos : ∀ x y, 0 ≤ F x y) :
    ENNReal.ofReal (boxIntegral a b c d F) =
      ∫⁻ x in Ioo a b, ∫⁻ y in Ioo c d, ENNReal.ofReal (F x y) := by
  simp only [Measure.restrict_congr_set (Ioo_ae_eq_Ioc (μ := volume))]
  unfold boxIntegral
  rw [intervalIntegral.integral_of_le hab]
  rw [ofReal_integral_eq_lintegral_ofReal]
  · apply lintegral_congr
    intro x
    rw [intervalIntegral.integral_of_le hcd]
    exact ofReal_integral_eq_lintegral_ofReal
      (by
        change IntegrableOn (F x) (Ioc c d) volume
        exact ((hF.uncurry_left x).intervalIntegrable c d).1)
      (Filter.Eventually.of_forall (hpos x))
  · change IntegrableOn _ (Ioc a b) volume
    exact ((intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hF c d).intervalIntegrable a b).1
  · exact Filter.Eventually.of_forall fun x =>
      intervalIntegral.integral_nonneg hcd (fun y _ => hpos x y)

lemma bounded_weighted_interval_lintegral (n : ℕ) (hn : 3 ≤ n)
    {l C a b c d cI cJ : ℝ} (hl : 0 < l) (hC : 0 ≤ C)
    (hab : a ≤ b) (hcd : c ≤ d) (hcI : 0 ≤ cI) (hcJ : 0 ≤ cJ) :
    (∫⁻ x in Ioo a b, ∫⁻ y in Ioo c d,
      ENNReal.ofReal ((cI+cJ)*kernel n l C (x-y))) ≤
    ∫⁻ x in Ioo a b, ∫⁻ y in Ioo c d,
      ENNReal.ofReal (cI*((kernel n l C (a-y)+kernel n l C (b-y))/2) +
        cJ*((kernel n l C (x-c)+kernel n l C (x-d))/2) +
        (((n:ℝ)-2)*min cI cJ*((x-y)^2/(l^2+(x-y)^2))+|cI-cJ|)*kernel n l C (x-y)) := by
  have hk := kernel_continuous n hl C
  have hD : Continuous (fun z : ℝ × ℝ => (z.1-z.2)^2/(l^2+(z.1-z.2)^2)) :=
    ((continuous_fst.sub continuous_snd).pow 2).div
      (continuous_const.add ((continuous_fst.sub continuous_snd).pow 2))
      (fun z => ne_of_gt (base_pos hl (z.1-z.2)))
  have hpc (x y : ℝ) : 0 ≤ (x-y)^2/(l^2+(x-y)^2) :=
    div_nonneg (sq_nonneg _) (base_pos hl _).le
  have hn' : 0 ≤ (n : ℝ)-2 := by exact_mod_cast (show 0 ≤ (n : ℤ)-2 by omega)
  have hleft : ∀ x y, 0 ≤ (cI+cJ)*kernel n l C (x-y) :=
    fun x y => mul_nonneg (add_nonneg hcI hcJ) (kernel_nonneg n hC _)
  have hright (x y : ℝ) : 0 ≤ cI*((kernel n l C (a-y)+kernel n l C (b-y))/2) +
        cJ*((kernel n l C (x-c)+kernel n l C (x-d))/2) +
        (((n:ℝ)-2)*min cI cJ*((x-y)^2/(l^2+(x-y)^2))+|cI-cJ|)*kernel n l C (x-y) := by
    apply add_nonneg
    · apply add_nonneg
      · exact mul_nonneg hcI (div_nonneg
          (add_nonneg (kernel_nonneg n hC _) (kernel_nonneg n hC _)) (by norm_num))
      · exact mul_nonneg hcJ (div_nonneg
          (add_nonneg (kernel_nonneg n hC _) (kernel_nonneg n hC _)) (by norm_num))
    · exact mul_nonneg (add_nonneg
        (mul_nonneg (mul_nonneg hn' (le_min hcI hcJ)) (hpc x y)) (abs_nonneg _))
        (kernel_nonneg n hC _)
  rw [← ofReal_boxIntegral hab hcd (by fun_prop (disch := positivity)) hleft,
      ← ofReal_boxIntegral hab hcd (by fun_prop (disch := positivity)) hright]
  apply ENNReal.ofReal_le_ofReal
  have heq : boxIntegral a b c d (fun x y =>
      cI*((kernel n l C (a-y)+kernel n l C (b-y))/2) +
      cJ*((kernel n l C (x-c)+kernel n l C (x-d))/2) +
      (((n:ℝ)-2)*min cI cJ*((x-y)^2/(l^2+(x-y)^2))+|cI-cJ|)*kernel n l C (x-y)) =
      cI * boxIntegral a b c d (fun _ y => (kernel n l C (a-y)+kernel n l C (b-y))/2) +
      cJ * boxIntegral a b c d (fun x _ => (kernel n l C (x-c)+kernel n l C (x-d))/2) +
      (((n:ℝ)-2)*min cI cJ) * boxIntegral a b c d
        (fun x y => (x-y)^2/(l^2+(x-y)^2)*kernel n l C (x-y)) +
      |cI-cJ| * boxIntegral a b c d (fun x y => kernel n l C (x-y)) := by
    calc
      _ = boxIntegral a b c d (fun x y =>
          (cI*((kernel n l C (a-y)+kernel n l C (b-y))/2) +
           cJ*((kernel n l C (x-c)+kernel n l C (x-d))/2) +
           (((n:ℝ)-2)*min cI cJ)*((x-y)^2/(l^2+(x-y)^2)*kernel n l C (x-y))) +
           |cI-cJ| *kernel n l C (x-y)) := by
        apply boxIntegral_congr; intros; ring
      _ = _ := by
        rw [boxIntegral_add a b c d (by fun_prop (disch := positivity)) (by fun_prop (disch := positivity)),
          boxIntegral_add a b c d (by fun_prop (disch := positivity)) (by fun_prop (disch := positivity)),
          boxIntegral_add a b c d (by fun_prop (disch := positivity)) (by fun_prop (disch := positivity))]
        simp only [boxIntegral_const_mul]
  rw [heq, boxIntegral_const_mul]
  exact bounded_weighted_interval_comparison n hn hl hC hab hcd hcI hcJ

end HenonLaneEmden.IntervalGeometry
end Intervals

end OAI
end

section
-- module Solutions.OAIQW_HenonLaneEmden.LayerPressure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section LayerPressure


open Set MeasureTheory
open scoped ENNReal NNReal Topology

namespace HenonLaneEmden.LayerPressure

lemma component_nonempty {U I : Set ℝ} (hI : I ∈ components U) : I.Nonempty := by
  obtain ⟨x,hx,rfl⟩ := hI
  exact ⟨x, mem_connectedComponentIn hx⟩

lemma component_open {U I : Set ℝ} (hU : IsOpen U) (hI : I ∈ components U) : IsOpen I := by
  obtain ⟨x,hx,rfl⟩ := hI
  exact hU.connectedComponentIn

lemma component_connected {U I : Set ℝ} (hI : I ∈ components U) : IsConnected I := by
  obtain ⟨x,hx,rfl⟩ := hI
  exact ⟨⟨x,mem_connectedComponentIn hx⟩,isPreconnected_connectedComponentIn⟩

lemma component_identify {U I : Set ℝ} (hI : I ∈ components U) {x : ℝ} (hx : x ∈ I) :
    connectedComponentIn U x = I := by
  obtain ⟨y,hy,rfl⟩ := hI
  exact (connectedComponentIn_eq hx).symm

lemma components_disjoint (U : Set ℝ) : (components U).PairwiseDisjoint id := by
  intro I hI J hJ hne
  change Disjoint I J
  rw [Set.disjoint_left]
  intro x hxI hxJ
  exact hne ((component_identify hI hxI).symm.trans (component_identify hJ hxJ))

lemma components_countable {U : Set ℝ} (hU : IsOpen U) : (components U).Countable :=
  (components_disjoint U).countable_of_isOpen (fun _ h => component_open hU h)
    (fun _ h => component_nonempty h)

lemma biUnion_components (U : Set ℝ) : (⋃ I ∈ components U, I) = U := by
  apply subset_antisymm
  · apply iUnion₂_subset
    intro I hI
    obtain ⟨x,hx,rfl⟩ := hI
    exact connectedComponentIn_subset U x
  · intro x hx
    exact mem_iUnion₂.mpr ⟨connectedComponentIn U x,⟨x,hx,rfl⟩,mem_connectedComponentIn hx⟩

/-- Nonnegative integration can be summed over two line-layer component families
without any integrability or finiteness assumption on either side. -/
lemma lintegral_layer_comparison {U V : Set ℝ} (hU : IsOpen U) (hV : IsOpen V)
    (F G : ℝ × ℝ → ℝ≥0∞)
    (h : ∀ I ∈ components U, ∀ J ∈ components V,
      (∫⁻ z in I ×ˢ J, F z) ≤ ∫⁻ z in I ×ˢ J, G z) :
    (∫⁻ z in U ×ˢ V, F z) ≤ ∫⁻ z in U ×ˢ V, G z := by
  let C : Set (Set ℝ × Set ℝ) := components U ×ˢ components V
  let S : Set ℝ × Set ℝ → Set (ℝ × ℝ) := fun p => p.1 ×ˢ p.2
  have hC : C.Countable := (components_countable hU).prod (components_countable hV)
  have hop : ∀ p ∈ C, MeasurableSet (S p) := by
    intro p hp
    exact (component_open hU hp.1).measurableSet.prod (component_open hV hp.2).measurableSet
  have hdis : C.PairwiseDisjoint S := by
    intro p hp q hq hpq
    change Disjoint (S p) (S q)
    rw [Set.disjoint_left]
    rintro ⟨x,y⟩ hxp hxq
    apply hpq
    apply Prod.ext
    · exact (component_identify hp.1 hxp.1).symm.trans (component_identify hq.1 hxq.1)
    · exact (component_identify hp.2 hxp.2).symm.trans (component_identify hq.2 hxq.2)
  have heq : (⋃ p ∈ C, S p) = U ×ˢ V := by
    ext z
    simp only [mem_iUnion, mem_prod, C, S]
    constructor
    · rintro ⟨⟨I,J⟩,⟨hI,hJ⟩,hzI,hzJ⟩
      exact ⟨by rw [← biUnion_components U]; exact mem_iUnion₂.mpr ⟨I,hI,hzI⟩,
        by rw [← biUnion_components V]; exact mem_iUnion₂.mpr ⟨J,hJ,hzJ⟩⟩
    · rintro ⟨hzU,hzV⟩
      rw [← biUnion_components U] at hzU
      rw [← biUnion_components V] at hzV
      obtain ⟨I,hI,hzI⟩ := mem_iUnion₂.mp hzU
      obtain ⟨J,hJ,hzJ⟩ := mem_iUnion₂.mp hzV
      exact ⟨(I,J),⟨hI,hJ⟩,hzI,hzJ⟩
  rw [← heq,lintegral_biUnion hC hop hdis F,lintegral_biUnion hC hop hdis G]
  exact ENNReal.tsum_le_tsum fun p => h p.val.1 p.property.1 p.val.2 p.property.2

lemma open_connected_eq_Ioo {I : Set ℝ} (hop : IsOpen I) (hcon : IsConnected I)
    (hlo : BddBelow I) (hhi : BddAbove I) : I = Ioo (sInf I) (sSup I) := by
  apply subset_antisymm
  · intro x hx
    obtain ⟨a,b,hab,hsub⟩ := mem_nhds_iff_exists_Ioo_subset.mp (hop.mem_nhds hx)
    have hm : (a+x)/2 ∈ I := hsub ⟨by linarith [hab.1], by linarith [hab.1,hab.2]⟩
    have hp : (x+b)/2 ∈ I := hsub ⟨by linarith [hab.1,hab.2], by linarith [hab.2]⟩
    exact ⟨lt_of_le_of_lt (csInf_le hlo hm) (by linarith [hab.1]),
      lt_of_lt_of_le (by linarith [hab.2]) (le_csSup hhi hp)⟩
  · exact hcon.Ioo_csInf_csSup_subset hlo hhi

open IntervalGeometry

/-- The interval comparison stated directly on a product of two open components.
The endpoint values on an unbounded component are immaterial because its weight
is zero. All integrands are nonnegative extended values. -/
lemma component_pair_comparison (n : ℕ) (hn : 3 ≤ n)
    {I J : Set ℝ} (hopI : IsOpen I) (hopJ : IsOpen J)
    (hconI : IsConnected I) (hconJ : IsConnected J)
    {l C cI cJ : ℝ} (hl : 0 < l) (hC : 0 ≤ C) (hcI : 0 ≤ cI) (hcJ : 0 ≤ cJ)
    (hbI : 0 < cI → BddBelow I ∧ BddAbove I)
    (hbJ : 0 < cJ → BddBelow J ∧ BddAbove J) :
    (∫⁻ z in I ×ˢ J, ENNReal.ofReal ((cI+cJ)*kernel n l C (z.1-z.2))) ≤
    ∫⁻ z in I ×ˢ J, ENNReal.ofReal
      (cI*((kernel n l C (sInf I-z.2)+kernel n l C (sSup I-z.2))/2) +
       cJ*((kernel n l C (z.1-sInf J)+kernel n l C (z.1-sSup J))/2) +
       (((n:ℝ)-2)*min cI cJ*((z.1-z.2)^2/(l^2+(z.1-z.2)^2))+|cI-cJ|)*
         kernel n l C (z.1-z.2)) := by
  by_cases hzI : cI = 0
  · subst cI
    apply lintegral_mono; intro z
    apply ENNReal.ofReal_le_ofReal
    simp only [zero_add, zero_mul, mul_zero, min_eq_left hcJ, zero_sub, abs_neg, abs_of_nonneg hcJ]
    exact le_add_of_nonneg_left (mul_nonneg hcJ (div_nonneg
      (add_nonneg (kernel_nonneg n hC _) (kernel_nonneg n hC _)) (by norm_num)))
  by_cases hzJ : cJ = 0
  · subst cJ
    apply lintegral_mono; intro z
    apply ENNReal.ofReal_le_ofReal
    simp only [add_zero, zero_mul, min_eq_right hcI, mul_zero, zero_add, sub_zero, abs_of_nonneg hcI]
    exact le_add_of_nonneg_left (mul_nonneg hcI (div_nonneg
      (add_nonneg (kernel_nonneg n hC _) (kernel_nonneg n hC _)) (by norm_num)))
  obtain ⟨hloI,hhiI⟩ := hbI (lt_of_le_of_ne hcI (Ne.symm hzI))
  obtain ⟨hloJ,hhiJ⟩ := hbJ (lt_of_le_of_ne hcJ (Ne.symm hzJ))
  have heqI := open_connected_eq_Ioo hopI hconI hloI hhiI
  have heqJ := open_connected_eq_Ioo hopJ hconJ hloJ hhiJ
  have ha : sInf I ≤ sSup I := csInf_le_csSup hconI.nonempty hloI hhiI
  have hb : sInf J ≤ sSup J := csInf_le_csSup hconJ.nonempty hloJ hhiJ
  have hk := kernel_continuous n hl C
  have hD : Continuous (fun z : ℝ × ℝ => (z.1-z.2)^2/(l^2+(z.1-z.2)^2)) :=
    ((continuous_fst.sub continuous_snd).pow 2).div
      (continuous_const.add ((continuous_fst.sub continuous_snd).pow 2))
      (fun z => ne_of_gt (base_pos hl (z.1-z.2)))
  have hcL : Continuous (fun z : ℝ × ℝ => (cI+cJ)*kernel n l C (z.1-z.2)) := by fun_prop
  have hcR : Continuous (fun z : ℝ × ℝ =>
      cI*((kernel n l C (sInf I-z.2)+kernel n l C (sSup I-z.2))/2) +
       cJ*((kernel n l C (z.1-sInf J)+kernel n l C (z.1-sSup J))/2) +
       (((n:ℝ)-2)*min cI cJ*((z.1-z.2)^2/(l^2+(z.1-z.2)^2))+|cI-cJ|)*
         kernel n l C (z.1-z.2)) := by fun_prop
  rw [show (volume : Measure (ℝ × ℝ)) = volume.prod volume from rfl,
    ← Measure.prod_restrict, lintegral_prod _ hcL.measurable.ennreal_ofReal.aemeasurable,
    lintegral_prod _ hcR.measurable.ennreal_ofReal.aemeasurable]
  simpa only [← heqI, ← heqJ] using
    (bounded_weighted_interval_lintegral n hn hl hC ha hb hcI hcJ)

/-- Weighted interval comparison summed over two general open line layers.  The
coefficients are arbitrary nonnegative component-constant weights, with positive
weight permitted only on bounded components. -/
lemma open_layer_comparison (n : ℕ) (hn : 3 ≤ n)
    {U V : Set ℝ} (hU : IsOpen U) (hV : IsOpen V)
    (c d : Set ℝ → ℝ) {l C : ℝ} (hl : 0 < l) (hC : 0 ≤ C)
    (hc : ∀ I ∈ components U, 0 ≤ c I) (hd : ∀ J ∈ components V, 0 ≤ d J)
    (hbc : ∀ I ∈ components U, 0 < c I → BddBelow I ∧ BddAbove I)
    (hbd : ∀ J ∈ components V, 0 < d J → BddBelow J ∧ BddAbove J) :
    (∫⁻ z in U ×ˢ V, ENNReal.ofReal
      ((c (connectedComponentIn U z.1)+d (connectedComponentIn V z.2))*kernel n l C (z.1-z.2))) ≤
    ∫⁻ z in U ×ˢ V, ENNReal.ofReal
      (c (connectedComponentIn U z.1)*
        ((kernel n l C (sInf (connectedComponentIn U z.1)-z.2)+
          kernel n l C (sSup (connectedComponentIn U z.1)-z.2))/2) +
       d (connectedComponentIn V z.2)*
        ((kernel n l C (z.1-sInf (connectedComponentIn V z.2))+
          kernel n l C (z.1-sSup (connectedComponentIn V z.2)))/2) +
       (((n:ℝ)-2)*min (c (connectedComponentIn U z.1)) (d (connectedComponentIn V z.2))*
         ((z.1-z.2)^2/(l^2+(z.1-z.2)^2))+
         |c (connectedComponentIn U z.1)-d (connectedComponentIn V z.2)|)*
         kernel n l C (z.1-z.2)) := by
  apply lintegral_layer_comparison hU hV
  intro I hI J hJ
  have hm : MeasurableSet (I ×ˢ J) :=
    (component_open hU hI).measurableSet.prod (component_open hV hJ).measurableSet
  have hp := component_pair_comparison n hn (component_open hU hI) (component_open hV hJ)
    (component_connected hI) (component_connected hJ) hl hC (hc I hI) (hd J hJ)
    (hbc I hI) (hbd J hJ)
  convert hp using 1
  · apply setLIntegral_congr_fun hm
    intro z hz
    dsimp only
    rw [component_identify hI hz.1, component_identify hJ hz.2]
  · apply setLIntegral_congr_fun hm
    intro z hz
    dsimp only
    rw [component_identify hI hz.1, component_identify hJ hz.2]

open LineComponents

lemma lineWeight_nonneg (U : Set ℝ) (h d : ℝ → ℝ) (δ x : ℝ) :
    0 ≤ lineWeight U h d δ x := ENNReal.toReal_nonneg

lemma lineWeight_le {U : Set ℝ} {h d : ℝ → ℝ} {δ x : ℝ}
    (hx : x ∈ U) (hh : 0 ≤ h x) : lineWeight U h d δ x ≤ h x := by
  have he := ENNReal.toReal_mono ENNReal.ofReal_ne_top (setWeight_le (h := h) (d := d)
    (δ := δ) (mem_connectedComponentIn hx))
  simpa only [lineWeight,ENNReal.toReal_ofReal hh] using he

/-- The actual capped component weights satisfy the summed nonnegative layer
comparison of equation (layer-pair), still before integrations over levels and
transverse variables. No boundedness of either whole layer is assumed. -/
lemma weighted_source_layer_comparison (n : ℕ) (hn : 3 ≤ n)
    {U V : Set ℝ} (hU : IsOpen U) (hV : IsOpen V)
    (h₁ h₂ d₁ d₂ : ℝ → ℝ) (δ : ℝ) {l C : ℝ} (hl : 0 < l) (hC : 0 ≤ C)
    (hh₁ : ∀ x ∈ U, 0 ≤ h₁ x) :
    (∫⁻ z in U ×ˢ V, ENNReal.ofReal
      ((lineWeight U h₁ d₁ δ z.1+lineWeight V h₂ d₂ δ z.2)*kernel n l C (z.1-z.2))) ≤
    ∫⁻ z in U ×ˢ V, ENNReal.ofReal
      (lineWeight U h₁ d₁ δ z.1*leftAverage U (kernel n l C) z.1 z.2 +
       lineWeight V h₂ d₂ δ z.2*rightAverage V (kernel n l C) z.1 z.2 +
       (((n:ℝ)-2)*h₁ z.1*((z.1-z.2)^2/(l^2+(z.1-z.2)^2))+
         |lineWeight U h₁ d₁ δ z.1-lineWeight V h₂ d₂ δ z.2|)*kernel n l C (z.1-z.2)) := by
  have hh := open_layer_comparison n hn hU hV
    (fun I => (setWeight h₁ d₁ δ I).toReal) (fun J => (setWeight h₂ d₂ δ J).toReal) hl hC
    (fun _ _ => ENNReal.toReal_nonneg) (fun _ _ => ENNReal.toReal_nonneg)
    (fun _ hI hpos => setWeight_pos_bounded (component_connected hI) hpos)
    (fun _ hJ hpos => setWeight_pos_bounded (component_connected hJ) hpos)
  apply hh.trans
  apply lintegral_mono_ae
  filter_upwards [ae_restrict_mem (hU.measurableSet.prod hV.measurableSet)] with z hz
  apply ENNReal.ofReal_le_ofReal
  dsimp only [lineWeight,leftAverage,rightAverage]
  apply add_le_add_right
  apply mul_le_mul_of_nonneg_right _ (kernel_nonneg n hC _)
  apply add_le_add_left
  apply mul_le_mul_of_nonneg_right _ (div_nonneg (sq_nonneg _) (base_pos hl _).le)
  apply mul_le_mul_of_nonneg_left _ (by
    have hn' : (3:ℝ) ≤ n := by exact_mod_cast hn
    linarith)
  exact (min_le_left _ _).trans (lineWeight_le hz.1 (hh₁ z.1 hz.1))

end HenonLaneEmden.LayerPressure
end LayerPressure

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

lemma measurable_lowerEndpoint {P : Type uP3} [TopologicalSpace P] [MeasurableSpace P]
    [BorelSpace P] {U : Set (P × ℝ)} (hU : IsOpen U) : Measurable (lowerEndpoint U) :=
  measurable_snd.sub (measurable_backwardExit (isOpen_relativeLayer hU)).ennreal_toReal
lemma measurable_upperEndpoint {P : Type uP4} [TopologicalSpace P] [MeasurableSpace P]
    [BorelSpace P] {U : Set (P × ℝ)} (hU : IsOpen U) : Measurable (upperEndpoint U) :=
  measurable_snd.add (measurable_forwardExit (isOpen_relativeLayer hU)).ennreal_toReal

lemma relative_component_eq_Ioo {P : Type uP5} [TopologicalSpace P]
    {U : Set (P × ℝ)} (hU : IsOpen U) {p : P × ℝ} (hp : p ∈ U)
    (hfin : componentLength (relativeLayer U) p ≠ ⊤) :
    connectedComponentIn {s | (p.1,s) ∈ U} p.2 =
      Ioo (lowerEndpoint U p) (upperEndpoint U p) := by
  have hp0 : (p,0) ∈ relativeLayer U := by simpa [relativeLayer] using hp
  have he := component_eq_Ioo (isOpen_relativeLayer hU) hp0
    (ENNReal.add_ne_top.mp hfin).1 (ENNReal.add_ne_top.mp hfin).2
  have him := image_relative_component (U := {s | (p.1,s) ∈ U}) (x := p.2) hp
  have hsets : {r : ℝ | (p,r) ∈ relativeLayer U} =
      {r : ℝ | (p.2,r) ∈ shiftedLayer {s | (p.1,s) ∈ U}} := rfl
  rw [hsets] at he
  rw [← him,he]
  ext s
  constructor
  · rintro ⟨r,hr,rfl⟩
    constructor <;> dsimp [lowerEndpoint,upperEndpoint] <;> linarith [hr.1,hr.2]
  · intro hs
    refine ⟨s-p.2,?_,by ring⟩
    constructor <;> dsimp [lowerEndpoint,upperEndpoint] at hs <;> linarith [hs.1,hs.2]

lemma relative_endpoints_eq {P : Type uP6} [TopologicalSpace P]
    {U : Set (P × ℝ)} (hU : IsOpen U) {p : P × ℝ} (hp : p ∈ U)
    (hfin : componentLength (relativeLayer U) p ≠ ⊤) :
    lowerEndpoint U p = sInf (connectedComponentIn {s | (p.1,s) ∈ U} p.2) ∧
    upperEndpoint U p = sSup (connectedComponentIn {s | (p.1,s) ∈ U} p.2) := by
  have he := relative_component_eq_Ioo hU hp hfin
  have hpI := mem_connectedComponentIn (F := {s | (p.1,s) ∈ U}) hp
  rw [he] at hpI
  rw [he,csInf_Ioo (lt_trans hpI.1 hpI.2),csSup_Ioo (lt_trans hpI.1 hpI.2)]
  exact ⟨rfl,rfl⟩

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

lemma relative_componentLength_eq {P : Type uP7} [TopologicalSpace P]
    {U : Set (P × ℝ)} (hU : IsOpen U) {p : P × ℝ} (hp : p ∈ U) :
    componentLength (relativeLayer U) p =
      volume (connectedComponentIn {s | (p.1,s) ∈ U} p.2) := by
  have he := shifted_componentLength_eq (isOpen_section hU p.1) hp
  simpa only [componentLength,forwardExit,backwardExit,SegmentInside,relativeLayer,
    shiftedLayer,Set.mem_ofPred] using he

lemma relative_endpoints_eq_of_weight_pos {P : Type uP8} [TopologicalSpace P]
    {U : Set (P × ℝ)} (hU : IsOpen U) {p : P × ℝ} (hp : p ∈ U)
    {h d : ℝ → ℝ} {δ : ℝ}
    (hw : 0 < (setWeight h d δ (connectedComponentIn {s | (p.1,s) ∈ U} p.2)).toReal) :
    lowerEndpoint U p = sInf (connectedComponentIn {s | (p.1,s) ∈ U} p.2) ∧
    upperEndpoint U p = sSup (connectedComponentIn {s | (p.1,s) ∈ U} p.2) := by
  apply relative_endpoints_eq hU hp
  rw [relative_componentLength_eq hU hp]
  unfold setWeight at hw
  split_ifs at hw with hh
  · exact hh.2.1
  · simp at hw

end HenonLaneEmden.LineComponents
end Endpoints

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
open Cutoff AdaptiveCap LineComponents
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

lemma measurable_potential (μ : Measure E) [SFinite μ] {k : E × E → ℝ≥0∞}
    {g : E → ℝ} (hk : Measurable k) (hg : Measurable g) :
    Measurable (potential μ k g) :=
  ((hg.comp measurable_snd).ennreal_ofReal.mul hk).lintegral_prod_right

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

lemma lintegral_pair_endpoint_average (μ : Measure E) [SFinite μ] {f g : E → ℝ}
    {k : E × E → ℝ≥0∞} {a : E × ℝ → ℝ≥0∞} {lo hi : E × ℝ → E}
    (hg : Measurable g) (hk : Measurable k) (ha : Measurable a)
    (hlo : Measurable lo) (hhi : Measurable hi) :
    ∫⁻ z, a z.1*((k (lo z.1,z.2.1)+k (hi z.1,z.2.1))/2)
        ∂(layerMeasure μ f).prod (layerMeasure μ g) =
      ∫⁻ z, a z*((potential μ k g (lo z)+potential μ k g (hi z))/2)
        ∂layerMeasure μ f := by
  simp only [ENNReal.div_eq_inv_mul,mul_add]
  simp_rw [← mul_assoc]
  rw [lintegral_add_left]
  · rw [lintegral_add_left]
    · congr 1
      · exact lintegral_pair_endpoint μ hg hk (ha.mul_const _) hlo
      · exact lintegral_pair_endpoint μ hg hk (ha.mul_const _) hhi
    · exact (ha.mul_const _).mul ((measurable_potential μ hk hg).comp hlo)
  · exact ((ha.comp measurable_fst).mul_const _).mul
      (hk.comp ((hlo.comp measurable_fst).prodMk measurable_snd.fst))

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
-- module Solutions.OAIQW_HenonLaneEmden.MeasureShuffle
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uA uB uC uD

section MeasureShuffle

open MeasureTheory
open scoped ENNReal
namespace HenonLaneEmden.LayerTonelli

variable {A : Type uA} {B : Type uB} {C : Type uC} {D : Type uD} [MeasurableSpace A] [MeasurableSpace B]
  [MeasurableSpace C] [MeasurableSpace D]

lemma lintegral_prod_prod_shuffle (μ : Measure A) (ν : Measure B) (ρ : Measure C) (σ : Measure D)
    [SFinite μ] [SFinite ν] [SFinite ρ] [SFinite σ]
    {F : (A × B) × (C × D) → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ z, F z ∂(μ.prod ν).prod (ρ.prod σ)) =
      ∫⁻ z : (A × C) × (B × D), F ((z.1.1,z.2.1),(z.1.2,z.2.2))
        ∂(μ.prod ρ).prod (ν.prod σ) := by
  calc
    _ = ∫⁻ a, ∫⁻ b, ∫⁻ c, ∫⁻ d, F ((a,b),(c,d)) ∂σ ∂ρ ∂ν ∂μ := by
      rw [lintegral_prod _ hF.aemeasurable,
        lintegral_prod (fun z : A × B => ∫⁻ y : C × D, F (z,y) ∂ρ.prod σ) (by fun_prop)]
      apply lintegral_congr; intro a
      apply lintegral_congr; intro b
      exact lintegral_prod _ (by fun_prop)
    _ = ∫⁻ a, ∫⁻ c, ∫⁻ b, ∫⁻ d, F ((a,b),(c,d)) ∂σ ∂ν ∂ρ ∂μ := by
      apply lintegral_congr; intro a
      exact lintegral_lintegral_swap (by fun_prop)
    _ = _ := by
      rw [lintegral_prod (fun z : (A × C) × (B × D) => F ((z.1.1,z.2.1),(z.1.2,z.2.2))) (by fun_prop),
        lintegral_prod (fun z : A × C => ∫⁻ y : B × D, F ((z.1,y.1),(z.2,y.2)) ∂ν.prod σ) (by fun_prop)]
      apply lintegral_congr; intro a
      apply lintegral_congr; intro c
      exact (lintegral_prod (fun z : B × D => F ((a,z.1),(c,z.2))) (by fun_prop)).symm

end HenonLaneEmden.LayerTonelli
end MeasureShuffle

end OAI
end

section
-- module Solutions.OAIQW_HenonLaneEmden.LayerSplit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uZ uA uB uC uA2 uB2 uC2 uA3 uB3 uC3

section LayerSplit

open MeasureTheory Set
open scoped ENNReal
namespace HenonLaneEmden.LayerTonelli

variable {Z : Type uZ} [MeasurableSpace Z]

lemma measurePreserving_tripleSwap {A : Type uA3} {B : Type uB3} {C : Type uC3} [MeasurableSpace A]
    [MeasurableSpace B] [MeasurableSpace C] (μ : Measure A) (ν : Measure B) (ρ : Measure C)
    [SFinite ν] [SFinite ρ] [SFinite μ] :
    MeasurePreserving (tripleSwap : (A × B) × C ≃ᵐ (A × C) × B)
      ((μ.prod ν).prod ρ) ((μ.prod ρ).prod ν) := by
  exact ((MeasurePreserving.symm MeasurableEquiv.prodAssoc
    (measurePreserving_prodAssoc μ ρ ν)).comp
    ((MeasurePreserving.id μ).prod (Measure.measurePreserving_swap (μ := ν) (ν := ρ)))).comp
    (measurePreserving_prodAssoc μ ν ρ)

lemma measurableSet_parameterLayer {f : Z × ℝ → ℝ} (hf : Measurable f) :
    MeasurableSet (parameterLayer f) :=
  (measurableSet_lt measurable_const measurable_fst.snd).inter
    (measurableSet_lt measurable_fst.snd (hf.comp (measurable_fst.fst.prodMk measurable_snd)))

lemma measurePreserving_layer_tripleSwap (μ : Measure Z) [SFinite μ]
    {f : Z × ℝ → ℝ} (hf : Measurable f) :
    MeasurePreserving (tripleSwap : (Z × ℝ) × ℝ ≃ᵐ (Z × ℝ) × ℝ)
      (layerMeasure (μ.prod volume) f) (parameterLayerMeasure μ f) := by
  exact (measurePreserving_tripleSwap μ volume volume).restrict_preimage
    (measurableSet_parameterLayer hf)

/-- After permuting the real position and level coordinates, every pair layer
integral is the iterated nonnegative integral over two transverse/level parameters
and then the two real line layers. This is valid before proving finiteness. -/
lemma lintegral_pair_layer_split (μ : Measure Z) [SFinite μ]
    {f g : Z × ℝ → ℝ} (hf : Measurable f) (hg : Measurable g)
    {F : ((Z × ℝ) × ℝ) × ((Z × ℝ) × ℝ) → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ z, F z ∂(layerMeasure (μ.prod volume) f).prod (layerMeasure (μ.prod volume) g)) =
      ∫⁻ p : (Z × ℝ) × (Z × ℝ),
        ∫⁻ s : ℝ × ℝ in {s | (p.1,s) ∈ parameterLayer f} ×ˢ {s | (p.2,s) ∈ parameterLayer g},
          F (((p.1.1,s.1),p.1.2),((p.2.1,s.2),p.2.2))
        ∂volume.prod volume ∂(μ.prod volume).prod (μ.prod volume) := by
  let V := parameterLayer f ×ˢ parameterLayer g
  let G : ((Z × ℝ) × ℝ) × ((Z × ℝ) × ℝ) → ℝ≥0∞ :=
    fun z => F (((z.1.1.1,z.1.2),z.1.1.2),((z.2.1.1,z.2.2),z.2.1.2))
  have hG : Measurable G := by fun_prop
  have hV : MeasurableSet V := (measurableSet_parameterLayer hf).prod (measurableSet_parameterLayer hg)
  calc
    _ = ∫⁻ z, G z ∂(parameterLayerMeasure μ f).prod (parameterLayerMeasure μ g) := by
      exact ((measurePreserving_layer_tripleSwap μ hf).prod
        (measurePreserving_layer_tripleSwap μ hg)).lintegral_comp hG
    _ = ∫⁻ z, V.indicator G z ∂((μ.prod volume).prod volume).prod ((μ.prod volume).prod volume) := by
      rw [parameterLayerMeasure,parameterLayerMeasure,Measure.prod_restrict]
      exact (lintegral_indicator hV G).symm
    _ = ∫⁻ z : ((Z × ℝ) × (Z × ℝ)) × (ℝ × ℝ),
        V.indicator G ((z.1.1,z.2.1),(z.1.2,z.2.2))
        ∂((μ.prod volume).prod (μ.prod volume)).prod (volume.prod volume) :=
      lintegral_prod_prod_shuffle _ _ _ _ (hG.indicator hV)
    _ = _ := by
      rw [lintegral_prod _ (by fun_prop)]
      apply lintegral_congr
      intro p
      have hset : MeasurableSet ({s | (p.1,s) ∈ parameterLayer f} ×ˢ {s | (p.2,s) ∈ parameterLayer g}) :=
        ((measurableSet_parameterLayer hf).preimage measurable_prodMk_left).prod
          ((measurableSet_parameterLayer hg).preimage measurable_prodMk_left)
      rw [← lintegral_indicator hset]
      apply lintegral_congr; intro s
      rfl

end HenonLaneEmden.LayerTonelli
end LayerSplit

end OAI
end

section
-- module Solutions.OAIQW_HenonLaneEmden.LayerAssembly
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uZ

section LayerAssembly

open MeasureTheory Set
open scoped ENNReal
namespace HenonLaneEmden.LayerPressure
open LineComponents IntervalGeometry LayerTonelli

variable {Z : Type uZ} [NormedAddCommGroup Z] [MeasurableSpace Z] [BorelSpace Z] [SecondCountableTopology Z]


omit [SecondCountableTopology Z] in
lemma measurable_sourceWeight {f h d : Z × ℝ → ℝ} (hf : IsOpen (parameterLayer f))
    (hh : Continuous h) (hd : Continuous d) (δ : ℝ) : Measurable (sourceWeight f h d δ) := by
  let h' : (Z × ℝ) × ℝ → ℝ := fun z => h (z.1.1,z.2)
  let d' : (Z × ℝ) × ℝ → ℝ := fun z => d (z.1.1,z.2)
  have hh' : Continuous h' := hh.comp (continuous_fst.fst.prodMk continuous_snd)
  have hd' : Continuous d' := hd.comp (continuous_fst.fst.prodMk continuous_snd)
  have he : Measurable (fun p : (Z × ℝ) × ℝ =>
      (setWeight (fun s => h' (p.1,s)) (fun s => d' (p.1,s)) δ
        (connectedComponentIn {s | (p.1,s) ∈ parameterLayer f} p.2)).toReal) :=
    (measurable_parametric_setWeight hf hh' hd' δ).ennreal_toReal
  have hem := he.comp (tripleSwap : (Z × ℝ) × ℝ ≃ᵐ (Z × ℝ) × ℝ).measurable
  unfold sourceWeight lineWeight
  simpa only [Function.comp_def,tripleSwap_apply,h',d'] using hem

omit [SecondCountableTopology Z] in
lemma measurable_sourceLower {f : Z × ℝ → ℝ} (hf : IsOpen (parameterLayer f)) :
    Measurable (sourceLower f) := by
  exact measurable_fst.fst.prodMk ((measurable_lowerEndpoint hf).comp
    (measurable_fst.fst.prodMk measurable_snd |>.prodMk measurable_fst.snd))
omit [SecondCountableTopology Z] in
lemma measurable_sourceUpper {f : Z × ℝ → ℝ} (hf : IsOpen (parameterLayer f)) :
    Measurable (sourceUpper f) := by
  exact measurable_fst.fst.prodMk ((measurable_upperEndpoint hf).comp
    (measurable_fst.fst.prodMk measurable_snd |>.prodMk measurable_fst.snd))

lemma measurable_splitKernel (n : ℕ) (C : ℝ) : Measurable (splitKernel (Z := Z) n C) := by
  unfold splitKernel kernel
  fun_prop
lemma measurable_splitDirection : Measurable (splitDirection (Z := Z)) := by
  unfold splitDirection
  fun_prop

lemma measurable_pairLeft (n : ℕ) (C : ℝ) {f g h d : Z × ℝ → ℝ}
    (hf : IsOpen (parameterLayer f)) (hg : IsOpen (parameterLayer g))
    (hh : Continuous h) (hd : Continuous d) (δ : ℝ) : Measurable (pairLeft n C f g h d δ) := by
  unfold pairLeft
  have hχf := measurable_sourceWeight hf hh hd δ
  have hχg := measurable_sourceWeight hg hh hd δ
  have hk := measurable_splitKernel (Z := Z) n C
  fun_prop

lemma measurable_pairRight (n : ℕ) (C : ℝ) {f g h d : Z × ℝ → ℝ}
    (hf : IsOpen (parameterLayer f)) (hg : IsOpen (parameterLayer g))
    (hh : Continuous h) (hd : Continuous d) (δ : ℝ) : Measurable (pairRight n C f g h d δ) := by
  unfold pairRight
  have hχf := measurable_sourceWeight hf hh hd δ
  have hχg := measurable_sourceWeight hg hh hd δ
  have hlof := measurable_sourceLower hf
  have hlog := measurable_sourceLower hg
  have hhif := measurable_sourceUpper hf
  have hhig := measurable_sourceUpper hg
  have hk := measurable_splitKernel (Z := Z) n C
  have hD := measurable_splitDirection (Z := Z)
  fun_prop

omit [MeasurableSpace Z] [BorelSpace Z] [SecondCountableTopology Z] in
lemma weighted_leftAverage_eq {f h d : Z × ℝ → ℝ} (hf : IsOpen (parameterLayer f))
    (δ : ℝ) {p : Z × ℝ} {s : ℝ} (hs : (p,s) ∈ parameterLayer f)
    (k : ℝ → ℝ) (y : ℝ) :
    lineWeight {s | (p,s) ∈ parameterLayer f} (fun s => h (p.1,s)) (fun s => d (p.1,s)) δ s *
      leftAverage {s | (p,s) ∈ parameterLayer f} k s y =
    lineWeight {s | (p,s) ∈ parameterLayer f} (fun s => h (p.1,s)) (fun s => d (p.1,s)) δ s *
      ((k (lowerEndpoint (parameterLayer f) (p,s)-y)+k (upperEndpoint (parameterLayer f) (p,s)-y))/2) := by
  by_cases hz : lineWeight {s | (p,s) ∈ parameterLayer f} (fun s => h (p.1,s))
      (fun s => d (p.1,s)) δ s = 0
  · rw [hz,zero_mul,zero_mul]
  · have he := relative_endpoints_eq_of_weight_pos hf hs
      (lt_of_le_of_ne (lineWeight_nonneg _ _ _ _ _) (Ne.symm hz))
    simp only [leftAverage,he.1,he.2]

omit [MeasurableSpace Z] [BorelSpace Z] [SecondCountableTopology Z] in
lemma weighted_rightAverage_eq {g h d : Z × ℝ → ℝ} (hg : IsOpen (parameterLayer g))
    (δ : ℝ) {p : Z × ℝ} {s : ℝ} (hs : (p,s) ∈ parameterLayer g)
    (k : ℝ → ℝ) (x : ℝ) :
    lineWeight {s | (p,s) ∈ parameterLayer g} (fun s => h (p.1,s)) (fun s => d (p.1,s)) δ s *
      rightAverage {s | (p,s) ∈ parameterLayer g} k x s =
    lineWeight {s | (p,s) ∈ parameterLayer g} (fun s => h (p.1,s)) (fun s => d (p.1,s)) δ s *
      ((k (x-lowerEndpoint (parameterLayer g) (p,s))+k (x-upperEndpoint (parameterLayer g) (p,s)))/2) := by
  by_cases hz : lineWeight {s | (p,s) ∈ parameterLayer g} (fun s => h (p.1,s))
      (fun s => d (p.1,s)) δ s = 0
  · rw [hz,zero_mul,zero_mul]
  · have he := relative_endpoints_eq_of_weight_pos hg hs
      (lt_of_le_of_ne (lineWeight_nonneg _ _ _ _ _) (Ne.symm hz))
    simp only [rightAverage,he.1,he.2]

omit [MeasurableSpace Z] [BorelSpace Z] [SecondCountableTopology Z] in
lemma pair_line_comparison (n : ℕ) (hn : 3 ≤ n) {C : ℝ} (hC : 0 ≤ C)
    {f g h d : Z × ℝ → ℝ} (hf : IsOpen (parameterLayer f)) (hg : IsOpen (parameterLayer g))
    (hhn : ∀ x, 0 ≤ h x) (δ : ℝ) (p : (Z × ℝ) × (Z × ℝ)) (hp : p.1.1 ≠ p.2.1) :
    (∫⁻ s : ℝ × ℝ in {s | (p.1,s) ∈ parameterLayer f} ×ˢ {s | (p.2,s) ∈ parameterLayer g},
      ENNReal.ofReal (pairLeft n C f g h d δ (((p.1.1,s.1),p.1.2),((p.2.1,s.2),p.2.2)))) ≤
    ∫⁻ s : ℝ × ℝ in {s | (p.1,s) ∈ parameterLayer f} ×ˢ {s | (p.2,s) ∈ parameterLayer g},
      ENNReal.ofReal (pairRight n C f g h d δ (((p.1.1,s.1),p.1.2),((p.2.1,s.2),p.2.2))) := by
  have hfo := isOpen_section hf p.1
  have hgo := isOpen_section hg p.2
  have hl : 0 < ‖p.1.1-p.2.1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hp)
  have hh := weighted_source_layer_comparison n hn hfo hgo
    (fun s => h (p.1.1,s)) (fun s => h (p.2.1,s))
    (fun s => d (p.1.1,s)) (fun s => d (p.2.1,s)) δ hl hC (fun x _ => hhn _)
  change (∫⁻ s in _, ENNReal.ofReal _) ≤ _ at hh
  convert hh using 1
  · rfl
  · apply setLIntegral_congr_fun (hfo.measurableSet.prod hgo.measurableSet)
    intro s hs
    unfold pairRight splitKernel splitDirection sourceLower sourceUpper sourceWeight
    dsimp only
    rw [weighted_leftAverage_eq hf δ hs.1,weighted_rightAverage_eq hg δ hs.2]

lemma ae_distinct_transverse (μ : Measure Z) [SFinite μ] [NullSingletonClass μ] :
    ∀ᵐ p : (Z × ℝ) × (Z × ℝ) ∂(μ.prod volume).prod (μ.prod volume), p.1.1 ≠ p.2.1 := by
  apply (Measure.ae_prod_iff_ae_ae (by measurability)).mpr
  apply ae_of_all
  intro x
  apply (Measure.ae_prod_iff_ae_ae (by measurability)).mpr
  filter_upwards [μ.ae_ne x.1] with z hz
  exact ae_of_all _ (fun _ => Ne.symm hz)

/-- The globally integrated nonnegative interval comparison. No source,
endpoint, or energy integrability is assumed; all terms are still extended values. -/
lemma global_nonnegative_pressure (μ : Measure Z) [SFinite μ] [NullSingletonClass μ]
    (n : ℕ) (hn : 3 ≤ n) {C : ℝ} (hC : 0 ≤ C)
    {f g h d : Z × ℝ → ℝ} (hf : Measurable f) (hg : Measurable g)
    (hfo : IsOpen (parameterLayer f)) (hgo : IsOpen (parameterLayer g))
    (hh : Continuous h) (hd : Continuous d) (hhn : ∀ x, 0 ≤ h x) (δ : ℝ) :
    (∫⁻ z, ENNReal.ofReal (pairLeft n C f g h d δ z)
      ∂(layerMeasure (μ.prod volume) f).prod (layerMeasure (μ.prod volume) g)) ≤
    ∫⁻ z, ENNReal.ofReal (pairRight n C f g h d δ z)
      ∂(layerMeasure (μ.prod volume) f).prod (layerMeasure (μ.prod volume) g) := by
  rw [lintegral_pair_layer_split μ hf hg (measurable_pairLeft n C hfo hgo hh hd δ).ennreal_ofReal,
    lintegral_pair_layer_split μ hf hg (measurable_pairRight n C hfo hgo hh hd δ).ennreal_ofReal]
  apply lintegral_mono_ae
  filter_upwards [ae_distinct_transverse μ] with p hp
  exact pair_line_comparison n hn hC hfo hgo hhn δ p hp

end HenonLaneEmden.LayerPressure
end LayerAssembly

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

lemma lintegral_pair_endpoint_average_right (μ : Measure E) [SFinite μ] {f g : E → ℝ}
    {k : E × E → ℝ≥0∞} {b : E × ℝ → ℝ≥0∞} {lo hi : E × ℝ → E}
    (hf : Measurable f) (hk : Measurable k) (hs : ∀ x y, k (x,y) = k (y,x))
    (hb : Measurable b) (hlo : Measurable lo) (hhi : Measurable hi) :
    ∫⁻ z, b z.2*((k (z.1.1,lo z.2)+k (z.1.1,hi z.2))/2)
        ∂(layerMeasure μ f).prod (layerMeasure μ g) =
      ∫⁻ z, b z*((potential μ k f (lo z)+potential μ k f (hi z))/2)
        ∂layerMeasure μ g := by
  rw [← lintegral_prod_swap]
  change (∫⁻ z, b z.1*((k (z.2.1,lo z.1)+k (z.2.1,hi z.1))/2)
    ∂(layerMeasure μ g).prod (layerMeasure μ f)) = _
  simp_rw [hs _ (lo _),hs _ (hi _)]
  exact lintegral_pair_endpoint_average μ hf hk hb hlo hhi

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
-- module Solutions.OAIQW_HenonLaneEmden.SpatialPressure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uX uY uX2 uY2 uX3 uY3 uX4 uY4 uE

section SpatialPressure

open MeasureTheory Set Metric
open scoped ENNReal InnerProductSpace
noncomputable section
namespace HenonLaneEmden.LineComponents

lemma forwardExit_congr_section {X : Type uX} {Y : Type uY} {U : Set (X × ℝ)} {V : Set (Y × ℝ)}
    {x : X} {y : Y} (he : ∀ s, (x,s) ∈ U ↔ (y,s) ∈ V) :
    forwardExit U x = forwardExit V y := by
  classical
  unfold forwardExit SegmentInside
  simp_rw [he]
lemma backwardExit_congr_section {X : Type uX2} {Y : Type uY2} {U : Set (X × ℝ)} {V : Set (Y × ℝ)}
    {x : X} {y : Y} (he : ∀ s, (x,s) ∈ U ↔ (y,s) ∈ V) :
    backwardExit U x = backwardExit V y := by
  classical
  unfold backwardExit SegmentInside
  simp_rw [he]
lemma componentInf_congr_section {X : Type uX3} {Y : Type uY3} {U : Set (X × ℝ)} {V : Set (Y × ℝ)}
    {x : X} {y : Y} {f : X × ℝ → ℝ} {g : Y × ℝ → ℝ}
    (he : ∀ s, (x,s) ∈ U ↔ (y,s) ∈ V) (hv : ∀ s, f (x,s)=g (y,s)) :
    componentInf U f x = componentInf V g y := by
  classical
  unfold componentInf SegmentInside
  simp_rw [he,hv]
lemma componentWeight_congr_section {X : Type uX4} {Y : Type uY4} {U : Set (X × ℝ)} {V : Set (Y × ℝ)}
    {x : X} {y : Y} {h d : X × ℝ → ℝ} {h' d' : Y × ℝ → ℝ}
    (he : ∀ s, (x,s) ∈ U ↔ (y,s) ∈ V) (hh : ∀ s, h (x,s)=h' (y,s))
    (hd : ∀ s, d (x,s)=d' (y,s)) (δ : ℝ) :
    componentWeight U h d δ x = componentWeight V h' d' δ y := by
  classical
  rw [componentWeight,componentWeight,componentLength,componentLength,
    forwardExit_congr_section he,backwardExit_congr_section he,
    componentInf_congr_section he hh,componentInf_congr_section he hd,he 0]

end HenonLaneEmden.LineComponents
namespace HenonLaneEmden.SpatialComponents
open Cutoff AdaptiveCap LineComponents LineCoordinates LayerTonelli
variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]

omit [Nontrivial E] in
lemma measurePreserving_coordinateLayer (e : sphere (0:E) 1) {f : E → ℝ} (hf : Measurable f) :
    MeasurePreserving (coordinateLayerEquiv e)
      (layerMeasure (volume.prod volume) (f ∘ measurableEquiv e)) (layerMeasure volume f) := by
  exact ((measurePreserving e).prod (MeasurePreserving.id volume)).restrict_preimage
    (measurableSet_sourceSubgraph hf)

omit [FiniteDimensional ℝ E] [Nontrivial E] in
lemma coordinate_layer_open (e : sphere (0:E) 1) {f : E → ℝ}
    (hf : IsOpen {z : E × ℝ | 0 < z.2 ∧ z.2 < f z.1}) :
    IsOpen (parameterLayer (f ∘ measurableEquiv e)) := by
  exact hf.preimage (show Continuous (fun z : (transverse e × ℝ) × ℝ =>
    (measurableEquiv e (z.1.1,z.2),z.1.2)) by
      exact ((continuous_measurableEquiv e).comp (continuous_fst.fst.prodMk continuous_snd)).prodMk continuous_fst.snd)

lemma coordinate_sourceWeight (e : sphere (0:E) 1) {f : E → ℝ}
    (hf : IsOpen {z : E × ℝ | 0 < z.2 ∧ z.2 < f z.1})
    {κ : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1) (δ : ℝ) (a : (transverse e × ℝ) × ℝ) :
    LayerPressure.sourceWeight (f ∘ measurableEquiv e) (weight volume κ e ∘ measurableEquiv e)
        (d ∘ measurableEquiv e) δ a =
      lineWeight volume f κ δ (e,measurableEquiv e a.1,a.2) := by
  have hhh : Continuous (fun p : (transverse e × ℝ) × ℝ => weight volume κ e (measurableEquiv e (p.1.1,p.2))) :=
    ((continuous_weight volume hκ hκ1 e).comp (continuous_measurableEquiv e)).comp (continuous_fst.fst.prodMk continuous_snd)
  have hdd : Continuous (fun p : (transverse e × ℝ) × ℝ => d (measurableEquiv e (p.1.1,p.2))) :=
    (continuous_d.comp (continuous_measurableEquiv e)).comp (continuous_fst.fst.prodMk continuous_snd)
  unfold LayerPressure.sourceWeight LayerPressure.lineWeight
  have hre := relative_componentWeight_eq (coordinate_layer_open e hf) hhh hdd δ ((a.1.1,a.2),a.1.2)
  dsimp only at hre
  refine (congrArg ENNReal.toReal hre).symm.trans ?_
  unfold lineWeight
  congr 1
  apply componentWeight_congr_section
  · intro s
    simp only [relativeLayer,parameterLayer,lineLayer,mem_ofPred_eq,Function.comp_apply,parallel]
  · intro s
    simp only [parallel]
  · intro s
    simp only [parallel]

omit [FiniteDimensional ℝ E] [Nontrivial E] in
lemma coordinate_sourceLower (e : sphere (0:E) 1) (f : E → ℝ) (a : (transverse e × ℝ) × ℝ) :
    measurableEquiv e (LayerPressure.sourceLower (f ∘ measurableEquiv e) a) =
      lowerPoint f (e,measurableEquiv e a.1,a.2) := by
  have he : backwardExit (relativeLayer (parameterLayer (f ∘ measurableEquiv e))) ((a.1.1,a.2),a.1.2) =
      backwardExit (lineLayer f) (e,measurableEquiv e a.1,a.2) := by
    apply backwardExit_congr_section
    intro s
    simp only [relativeLayer,parameterLayer,lineLayer,mem_ofPred_eq,Function.comp_apply,parallel]
  unfold LayerPressure.sourceLower lowerEndpoint lowerPoint lowerOffset
  rw [he]
  simpa only [sub_eq_add_neg] using parallel e a.1 (-(backwardExit (lineLayer f) (e,measurableEquiv e a.1,a.2)).toReal)

omit [FiniteDimensional ℝ E] [Nontrivial E] in
lemma coordinate_sourceUpper (e : sphere (0:E) 1) (f : E → ℝ) (a : (transverse e × ℝ) × ℝ) :
    measurableEquiv e (LayerPressure.sourceUpper (f ∘ measurableEquiv e) a) =
      upperPoint f (e,measurableEquiv e a.1,a.2) := by
  have he : forwardExit (relativeLayer (parameterLayer (f ∘ measurableEquiv e))) ((a.1.1,a.2),a.1.2) =
      forwardExit (lineLayer f) (e,measurableEquiv e a.1,a.2) := by
    apply forwardExit_congr_section
    intro s
    simp only [relativeLayer,parameterLayer,lineLayer,mem_ofPred_eq,Function.comp_apply,parallel]
  unfold LayerPressure.sourceUpper upperEndpoint upperPoint upperOffset
  rw [he]
  exact parallel e a.1 ((forwardExit (lineLayer f) (e,measurableEquiv e a.1,a.2)).toReal)

end HenonLaneEmden.SpatialComponents
end
end SpatialPressure

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

lemma coordinate_kernel {n : ℕ} (e : sphere (0:Space n) 1) (z z' : transverse e × ℝ) :
    LayerPressure.splitKernel n (newtonDenom n)⁻¹ (z,z') =
      newtonKernel n (measurableEquiv e z,measurableEquiv e z') := by
  unfold LayerPressure.splitKernel IntervalGeometry.kernel newtonKernel
  rw [← distance_sq,dist_eq_norm,← Real.rpow_natCast,← Real.rpow_mul (norm_nonneg _)]
  congr 2
  ring

lemma coordinate_direction {E : Type uE4} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] (e : sphere (0:E) 1) (z z' : transverse e × ℝ) :
    LayerPressure.splitDirection (z,z') = directionalFactor e (measurableEquiv e z,measurableEquiv e z') := by
  have hi : inner ℝ (e:E) (measurableEquiv e z-measurableEquiv e z') = z.2-z'.2 := by
    simp only [measurableEquiv_apply,inner_sub_right,inner_add_right,inner_smul_right,
      inner_transverse,real_inner_self_eq_norm_sq,norm_unit,one_pow,mul_one,zero_add]
  unfold LayerPressure.splitDirection directionalFactor
  rw [hi,← distance_sq,dist_eq_norm]

namespace SpatialComponents
open Cutoff AdaptiveCap LineComponents LayerTonelli

lemma measurable_spatialPairLeft {n : ℕ} (hn : 1 ≤ n) {f g : Space n → ℝ}
    (hf : IsOpen {z : Space n × ℝ | 0 < z.2 ∧ z.2 < f z.1})
    (hg : IsOpen {z : Space n × ℝ | 0 < z.2 ∧ z.2 < g z.1})
    {κ : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1) (δ : ℝ) (e : sphere (0:Space n) 1) :
    Measurable (spatialPairLeft f g κ δ e) := by
  have : Nontrivial (Space n) := Module.nontrivial_of_finrank_pos (R := ℝ) (by simp; omega)
  have hm1 := measurable_lineWeight volume hf hκ hκ1 δ
  have hm2 := measurable_lineWeight volume hg hκ hκ1 δ
  unfold spatialPairLeft
  fun_prop

lemma measurable_spatialPairRight {n : ℕ} (hn : 1 ≤ n) {f g : Space n → ℝ}
    (hf : IsOpen {z : Space n × ℝ | 0 < z.2 ∧ z.2 < f z.1})
    (hg : IsOpen {z : Space n × ℝ | 0 < z.2 ∧ z.2 < g z.1})
    {κ : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1) (δ : ℝ) (e : sphere (0:Space n) 1) :
    Measurable (spatialPairRight f g κ δ e) := by
  have : Nontrivial (Space n) := Module.nontrivial_of_finrank_pos (R := ℝ) (by simp; omega)
  have hm1 := measurable_lineWeight volume hf hκ hκ1 δ
  have hm2 := measurable_lineWeight volume hg hκ hκ1 δ
  have hlo1 := measurable_lowerPoint hf
  have hlo2 := measurable_lowerPoint hg
  have hhi1 := measurable_upperPoint hf
  have hhi2 := measurable_upperPoint hg
  have hh := (continuous_weight volume hκ hκ1 e).measurable
  unfold spatialPairRight
  fun_prop

lemma spatial_global_nonnegative_pressure {n : ℕ} (hn : 3 ≤ n) {f g : Space n → ℝ}
    (hf : Measurable f) (hg : Measurable g)
    (hfo : IsOpen {z : Space n × ℝ | 0 < z.2 ∧ z.2 < f z.1})
    (hgo : IsOpen {z : Space n × ℝ | 0 < z.2 ∧ z.2 < g z.1})
    {κ : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1) (δ : ℝ) (e : sphere (0:Space n) 1) :
    (∫⁻ z, ENNReal.ofReal (spatialPairLeft f g κ δ e z)
      ∂(layerMeasure volume f).prod (layerMeasure volume g)) ≤
    ∫⁻ z, ENNReal.ofReal (spatialPairRight f g κ δ e z)
      ∂(layerMeasure volume f).prod (layerMeasure volume g) := by
  have : Nontrivial (Space n) := Module.nontrivial_of_finrank_pos (R := ℝ) (by simp; omega)
  have : Nontrivial (transverse e) := transverse_nontrivial (by simp; omega) e
  have hp := LayerPressure.global_nonnegative_pressure (volume : Measure (transverse e)) n hn
    (inv_nonneg.mpr (newtonDenom_pos hn).le) (hf.comp (measurableEquiv e).measurable)
    (hg.comp (measurableEquiv e).measurable) (coordinate_layer_open e hfo) (coordinate_layer_open e hgo)
    ((continuous_weight volume hκ hκ1 e).comp (continuous_measurableEquiv e))
    (continuous_d.comp (continuous_measurableEquiv e))
    (fun x => weight_nonneg volume κ e (measurableEquiv e x)) δ
  have hmp := (measurePreserving_coordinateLayer e hf).prod (measurePreserving_coordinateLayer e hg)
  rw [← hmp.lintegral_comp (measurable_spatialPairLeft (by omega) hfo hgo hκ hκ1 δ e).ennreal_ofReal,
    ← hmp.lintegral_comp (measurable_spatialPairRight (by omega) hfo hgo hκ hκ1 δ e).ennreal_ofReal]
  convert hp using 1
  · apply lintegral_congr
    intro z
    congr 1
    simp only [LayerPressure.pairLeft,spatialPairLeft,coordinate_sourceWeight e hfo hκ hκ1,
      coordinate_sourceWeight e hgo hκ hκ1,coordinate_kernel]
    rfl
  · apply lintegral_congr
    intro z
    congr 1
    simp only [LayerPressure.pairRight,spatialPairRight,coordinate_sourceWeight e hfo hκ hκ1,
      coordinate_sourceWeight e hgo hκ hκ1,coordinate_kernel,coordinate_direction,
      coordinate_sourceLower,coordinate_sourceUpper,Function.comp_apply]
    rfl

end SpatialComponents
end HenonLaneEmden
end
end PairPressure

end OAI
end

section
-- module Solutions.OAIQW_HenonLaneEmden.PairRecovery
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section PairRecovery

open MeasureTheory Set Metric
open scoped ENNReal
noncomputable section
namespace HenonLaneEmden.SpatialComponents
open Cutoff AdaptiveCap LayerTonelli

lemma weighted_potential_position {n : ℕ} (hn : 2 ≤ n) {p q A B : ℝ}
    {u v : Space n → ℝ} (h : IsSolution n p q A B u v) (hq : 0 < q)
    (κ δ : ℝ) (e : sphere (0:Space n) 1) (z : Space n × ℝ) :
    ENNReal.ofReal (lineWeight volume (source u q B) κ δ (e,z))*
        potential volume (fun z => ENNReal.ofReal (newtonKernel n z)) (source v p A) z.1 =
      ENNReal.ofReal (lineWeight volume (source u q B) κ δ (e,z)*u z.1) := by
  have hnχ := lineWeight_nonneg volume (source u q B) κ δ (e,z)
  by_cases hχ : 0 < lineWeight volume (source u q B) κ δ (e,z)
  · have hb := positive_lineWeight_base volume hχ
    have hx : z.1 ≠ 0 := by
      intro hx; rw [hx,source_zero] at hb; linarith [hb.1,hb.2.1]
    rw [h.newton_potential_u hn hq hx,ENNReal.ofReal_mul hnχ]
  · rw [le_antisymm (not_lt.mp hχ) hnχ]
    simp

lemma weighted_potential_endpoint {n : ℕ} (hn : 2 ≤ n) {p q A B κ δ : ℝ}
    {u v : Space n → ℝ} (h : IsSolution n p q A B u v) (hq : 0 < q)
    (hκ : 0 < κ) (hκ1 : κ ≤ 1) (hδ : 0 ≤ δ)
    (e : sphere (0:Space n) 1) (z : Space n × ℝ) :
    ENNReal.ofReal (lineWeight volume (source u q B) κ δ (e,z))*
        ((potential volume (fun z => ENNReal.ofReal (newtonKernel n z)) (source v p A) (lowerPoint (source u q B) (e,z))+
          potential volume (fun z => ENNReal.ofReal (newtonKernel n z)) (source v p A) (upperPoint (source u q B) (e,z)))/2) =
      ENNReal.ofReal (lineWeight volume (source u q B) κ δ (e,z)*endpointAverage u (source u q B) (e,z)) := by
  have : Nontrivial (Space n) := Module.nontrivial_of_finrank_pos (R := ℝ) (by simp; omega)
  have hnχ := lineWeight_nonneg volume (source u q B) κ δ (e,z)
  by_cases hχ : 0 < lineWeight volume (source u q B) κ δ (e,z)
  · have hf := isOpen_source_subgraph h.regular_u h.positive_u q B
    have hfc (y : Space n) (hy : y ≠ 0) : ContinuousAt (source u q B) y :=
      (regular_source h.regular_u h.positive_u q B).continuousOn.continuousAt (isOpen_compl_singleton.mem_nhds hy)
    have hlo := (endpoint_spec volume hf hfc hκ hκ1 hδ hχ (Or.inl rfl)).1
    have hhi := (endpoint_spec volume hf hfc hκ hκ1 hδ hχ (Or.inr rfl)).1
    have hlo0 : lowerPoint (source u q B) (e,z) ≠ 0 := norm_ne_zero_iff.mp (by change ‖z.1+_ • (e:Space n)‖ ≠ 0; linarith)
    have hhi0 : upperPoint (source u q B) (e,z) ≠ 0 := norm_ne_zero_iff.mp (by change ‖z.1+_ • (e:Space n)‖ ≠ 0; linarith)
    rw [h.newton_potential_u hn hq hlo0,h.newton_potential_u hn hq hhi0]
    unfold endpointAverage
    rw [ENNReal.ofReal_mul hnχ,ENNReal.ofReal_div_of_pos (by norm_num),
      ENNReal.ofReal_add (h.positive_u _).le (h.positive_u _).le,ENNReal.ofReal_ofNat]
  · rw [le_antisymm (not_lt.mp hχ) hnχ]
    simp

lemma IsSolution_pairLeft_recovery {n : ℕ} (hn : 2 ≤ n) {p q A B κ δ : ℝ}
    {u v : Space n → ℝ} (h : IsSolution n p q A B u v) (hp : 0 < p) (hq : 0 < q)
    (hκ : 0 < κ) (hκ1 : κ ≤ 1) (e : sphere (0:Space n) 1) :
    (∫⁻ z, ENNReal.ofReal (spatialPairLeft (source u q B) (source v p A) κ δ e z)
      ∂(layerMeasure volume (source u q B)).prod (layerMeasure volume (source v p A))) =
      positionIntegral u (source u q B) κ δ e+positionIntegral v (source v p A) κ δ e := by
  have : Nontrivial (Space n) := Module.nontrivial_of_finrank_pos (R := ℝ) (by simp; omega)
  have hf := isOpen_source_subgraph h.regular_u h.positive_u q B
  have hg := isOpen_source_subgraph h.regular_v h.positive_v p A
  have hfM := measurable_source h.continuous_u q B
  have hgM := measurable_source h.continuous_v p A
  have hm1 : Measurable (fun z : Space n × ℝ => lineWeight volume (source u q B) κ δ (e,z)) :=
    (measurable_lineWeight volume hf hκ hκ1 δ).comp (measurable_const.prodMk measurable_id)
  have hm2 : Measurable (fun z : Space n × ℝ => lineWeight volume (source v p A) κ δ (e,z)) :=
    (measurable_lineWeight volume hg hκ hκ1 δ).comp (measurable_const.prodMk measurable_id)
  unfold spatialPairLeft
  simp_rw [ENNReal.ofReal_mul (add_nonneg (lineWeight_nonneg volume _ _ _ _) (lineWeight_nonneg volume _ _ _ _)),
    ENNReal.ofReal_add (lineWeight_nonneg volume _ _ _ _) (lineWeight_nonneg volume _ _ _ _)]
  rw [lintegral_pair_weight_sum volume hfM hgM (measurable_newtonKernel n).ennreal_ofReal
    (fun x y => congrArg ENNReal.ofReal (newtonKernel_symm n x y)) hm1.ennreal_ofReal hm2.ennreal_ofReal]
  simp_rw [weighted_potential_position hn h hq κ δ e,weighted_potential_position hn h.swap hp κ δ e]
  rfl

end HenonLaneEmden.SpatialComponents
end
end PairRecovery

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

namespace SpatialComponents
open Cutoff AdaptiveCap LayerPressure

lemma IsSolution_pairRight_recovery {n : ℕ} (hn : 3 ≤ n) {p q A B κ δ : ℝ}
    {u v : Space n → ℝ} (h : IsSolution n p q A B u v) (hp : 0 < p) (hq : 0 < q)
    (hκ : 0 < κ) (hκ1 : κ ≤ 1) (hδ : 0 ≤ δ) (e : sphere (0:Space n) 1) :
    (∫⁻ z, ENNReal.ofReal (spatialPairRight (source u q B) (source v p A) κ δ e z)
      ∂(layerMeasure volume (source u q B)).prod (layerMeasure volume (source v p A))) =
      (endpointIntegral u (source u q B) κ δ e+endpointIntegral v (source v p A) κ δ e)+
      capPressureIntegral (source u q B) (source v p A) κ e+
      pairMismatchIntegral (source u q B) (source v p A) κ δ e := by
  have : Nontrivial (Space n) := Module.nontrivial_of_finrank_pos (R := ℝ) (by simp; omega)
  have hf := isOpen_source_subgraph h.regular_u h.positive_u q B
  have hg := isOpen_source_subgraph h.regular_v h.positive_v p A
  have hfM := measurable_source h.continuous_u q B
  have hgM := measurable_source h.continuous_v p A
  have hm1 : Measurable (fun z : Space n × ℝ => lineWeight volume (source u q B) κ δ (e,z)) :=
    (measurable_lineWeight volume hf hκ hκ1 δ).comp (measurable_const.prodMk measurable_id)
  have hm2 : Measurable (fun z : Space n × ℝ => lineWeight volume (source v p A) κ δ (e,z)) :=
    (measurable_lineWeight volume hg hκ hκ1 δ).comp (measurable_const.prodMk measurable_id)
  have hlo1 : Measurable (fun z : Space n × ℝ => lowerPoint (source u q B) (e,z)) :=
    (measurable_lowerPoint hf).comp (measurable_const.prodMk measurable_id)
  have hhi1 : Measurable (fun z : Space n × ℝ => upperPoint (source u q B) (e,z)) :=
    (measurable_upperPoint hf).comp (measurable_const.prodMk measurable_id)
  have hlo2 : Measurable (fun z : Space n × ℝ => lowerPoint (source v p A) (e,z)) :=
    (measurable_lowerPoint hg).comp (measurable_const.prodMk measurable_id)
  have hhi2 : Measurable (fun z : Space n × ℝ => upperPoint (source v p A) (e,z)) :=
    (measurable_upperPoint hg).comp (measurable_const.prodMk measurable_id)
  have hh : Measurable (weight volume κ e : Space n → ℝ) := (continuous_weight volume hκ hκ1 e).measurable
  have hn2 : 0 ≤ (n:ℝ)-2 := by exact_mod_cast (show (2:ℝ) ≤ n by exact_mod_cast (show 2 ≤ n by omega)) |> sub_nonneg.mpr
  have he (z : (Space n × ℝ) × (Space n × ℝ)) :
      ENNReal.ofReal (spatialPairRight (source u q B) (source v p A) κ δ e z) =
        ENNReal.ofReal (lineWeight volume (source u q B) κ δ (e,z.1))*
          ((ENNReal.ofReal (newtonKernel n (lowerPoint (source u q B) (e,z.1),z.2.1))+
            ENNReal.ofReal (newtonKernel n (upperPoint (source u q B) (e,z.1),z.2.1)))/2)+
        ENNReal.ofReal (lineWeight volume (source v p A) κ δ (e,z.2))*
          ((ENNReal.ofReal (newtonKernel n (z.1.1,lowerPoint (source v p A) (e,z.2)))+
            ENNReal.ofReal (newtonKernel n (z.1.1,upperPoint (source v p A) (e,z.2))))/2)+
        ENNReal.ofReal (((n:ℝ)-2)*weight volume κ e z.1.1*directionalFactor e (z.1.1,z.2.1))*
          ENNReal.ofReal (newtonKernel n (z.1.1,z.2.1))+
        ENNReal.ofReal (|lineWeight volume (source u q B) κ δ (e,z.1)-lineWeight volume (source v p A) κ δ (e,z.2)| *
          newtonKernel n (z.1.1,z.2.1)) := by
    have hk := newtonKernel_nonneg hn
    have hχ := lineWeight_nonneg (μ := (volume : Measure (Space n)))
    have hh0 := weight_nonneg (μ := (volume : Measure (Space n)))
    have hd := (directionalFactor_bounds e (z.1.1,z.2.1)).1
    have hχ1 := hχ (source u q B) κ δ (e,z.1)
    have hχ2 := hχ (source v p A) κ δ (e,z.2)
    have hh1 := hh0 κ e z.1.1
    have hk0 := hk (z.1.1,z.2.1)
    have hk1 := hk (lowerPoint (source u q B) (e,z.1),z.2.1)
    have hk2 := hk (upperPoint (source u q B) (e,z.1),z.2.1)
    have hk3 := hk (z.1.1,lowerPoint (source v p A) (e,z.2))
    have hk4 := hk (z.1.1,upperPoint (source v p A) (e,z.2))
    unfold spatialPairRight
    rw [add_mul]
    rw [ENNReal.ofReal_add (by positivity) (by positivity),
      ENNReal.ofReal_add (by positivity) (by positivity),
      ENNReal.ofReal_add (by positivity) (by positivity)]
    rw [ENNReal.ofReal_mul (hχ _ _ _ _),ENNReal.ofReal_mul (hχ _ _ _ _),
      ENNReal.ofReal_div_of_pos (show (0:ℝ)<2 by norm_num),
      ENNReal.ofReal_div_of_pos (show (0:ℝ)<2 by norm_num),
      ENNReal.ofReal_add (hk _) (hk _),ENNReal.ofReal_add (hk _) (hk _),
      ENNReal.ofReal_mul (mul_nonneg (mul_nonneg hn2 (hh0 _ _ _)) hd),ENNReal.ofReal_ofNat]
    ring
  have hm1' := measurable_lineWeight volume hf hκ hκ1 δ
  have hm2' := measurable_lineWeight volume hg hκ hκ1 δ
  have hlo1' := measurable_lowerPoint hf
  have hhi1' := measurable_upperPoint hf
  have hlo2' := measurable_lowerPoint hg
  have hhi2' := measurable_upperPoint hg
  have hh' := measurable_weight (volume : Measure (Space n)) hκ hκ1
  simp_rw [he]
  rw [lintegral_add_left (by fun_prop [measurable_newtonKernel,measurable_directionalFactor]),lintegral_add_left (by fun_prop [measurable_newtonKernel,measurable_directionalFactor]),lintegral_add_left (by fun_prop [measurable_newtonKernel,measurable_directionalFactor]),
    lintegral_pair_endpoint_average volume hgM (measurable_newtonKernel n).ennreal_ofReal hm1.ennreal_ofReal hlo1 hhi1,
    lintegral_pair_endpoint_average_right volume hfM (measurable_newtonKernel n).ennreal_ofReal
      (fun x y => congrArg ENNReal.ofReal (newtonKernel_symm n x y)) hm2.ennreal_ofReal hlo2 hhi2,
    lintegral_pair_interaction hfM hgM (F := fun z => ENNReal.ofReal (((n:ℝ)-2)*weight volume κ e z.1*directionalFactor e z)) (by fun_prop [measurable_newtonKernel,measurable_directionalFactor])]
  simp_rw [weighted_potential_endpoint (by omega) h hq hκ hκ1 hδ e,
    weighted_potential_endpoint (by omega) h.swap hp hκ hκ1 hδ e]
  rfl

lemma IsSolution_pressure_comparison_oai {n : ℕ} (hn : 3 ≤ n) {p q A B κ δ : ℝ}
    {u v : Space n → ℝ} (h : IsSolution n p q A B u v) (hp : 0 < p) (hq : 0 < q)
    (hκ : 0 < κ) (hκ1 : κ ≤ 1) (hδ : 0 ≤ δ) (e : sphere (0:Space n) 1) :
    positionIntegral u (source u q B) κ δ e+positionIntegral v (source v p A) κ δ e ≤
      (endpointIntegral u (source u q B) κ δ e+endpointIntegral v (source v p A) κ δ e)+
      capPressureIntegral (source u q B) (source v p A) κ e+
      pairMismatchIntegral (source u q B) (source v p A) κ δ e := by
  rw [← IsSolution_pairLeft_recovery (by omega) h hp hq hκ hκ1,
    ← IsSolution_pairRight_recovery hn h hp hq hκ hκ1 hδ]
  exact spatial_global_nonnegative_pressure hn (measurable_source h.continuous_u q B)
    (measurable_source h.continuous_v p A) (isOpen_source_subgraph h.regular_u h.positive_u q B)
    (isOpen_source_subgraph h.regular_v h.positive_v p A) hκ hκ1 δ e

end SpatialComponents
end HenonLaneEmden
end
end PDEPressure

end OAI
end

theorem solution : type_of% @OAI.HenonLaneEmden.SpatialComponents.IsSolution_pressure_comparison_oai := @OAI.HenonLaneEmden.SpatialComponents.IsSolution_pressure_comparison_oai
