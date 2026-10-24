-- Prove2me | solution 1 for OAI.Bernoulli.DeSilvaJerison.U_upper_lipschitz_comparison
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-23T21:36:18.885507+00:00
-- url     : https://prove2.me/submissions/0bcdcfce-e2c9-4de7-88c5-2e3c9c01d56d

import Mathlib
import Definitions.Def_BernoulliNonflatInSeven
import Definitions.Def_OAIQWBNS000
import Theorems.Thm_OAI_Bernoulli_DeSilvaJerison_upperFlux_primitive_bound

section
-- module Solutions.OAIQW_BernoulliCone.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. -/
section OAICompat434
theorem dite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : p) :
    (if hp : p then a hp else b hp) = a h := dif_pos h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQW_BernoulliCone.SobolevCalculus
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uα uE uF uK uι

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology ContDiff

namespace Bernoulli
open scoped _root_.Bernoulli

namespace Test

variable {d : ℕ} {D : Set (Space d)} {φ : Space d → ℝ}

theorem continuous_gradient (hφ : Test D φ) : Continuous (gradient φ) := by
  exact (InnerProductSpace.toDual ℝ (Space d)).symm.continuous.comp
    (hφ.1.continuous_fderiv (by simp))

theorem compact_gradient (hφ : Test D φ) : HasCompactSupport (gradient φ) := by
  exact (hφ.2.1.fderiv ℝ).comp_left (map_zero (InnerProductSpace.toDual ℝ (Space d)).symm)

theorem memLp (hφ : Test D φ) : MemLp φ 2 (volume.restrict D) := by
  exact MemLp.mono_measure Measure.restrict_le_self
    (hφ.1.continuous.memLp_of_hasCompactSupport hφ.2.1)

theorem memLp_gradient (hφ : Test D φ) :
    MemLp (gradient φ) 2 (volume.restrict D) := by
  exact MemLp.mono_measure Measure.restrict_le_self
    (hφ.continuous_gradient.memLp_of_hasCompactSupport hφ.compact_gradient)

theorem eq_zero_outside (hφ : Test D φ) {x : Space d} (hx : x ∉ D) : φ x = 0 := by
  by_contra h
  exact hx (hφ.2.2 (subset_tsupport φ (by exact h)))

end Test

section SobolevLinear
variable {d : ℕ} {D : Set (Space d)}
variable {u v : Space d → ℝ} {G V : Space d → Space d}

lemma memLp_inner_const (hG : MemLp G 2 (volume.restrict D)) (h : Space d) :
    MemLp (fun x => inner ℝ (G x) h) 2 (volume.restrict D) := by
  apply hG.of_le_mul (c := ‖h‖) (hG.aestronglyMeasurable.inner aestronglyMeasurable_const)
  exact Filter.Eventually.of_forall (fun x => by
    simpa [mul_comm] using (norm_inner_le_norm (𝕜 := ℝ) (G x) h))

lemma Test.memLp_directional {φ : Space d → ℝ} (hφ : Test D φ) (h : Space d) :
    MemLp (fun x => (fderiv ℝ φ x) h) 2 (volume.restrict D) := by
  simpa only [inner_gradient_left] using memLp_inner_const hφ.memLp_gradient h

lemma integrable_deriv_product (hu : MemLp u 2 (volume.restrict D))
    {φ : Space d → ℝ} (hφ : Test D φ) (h : Space d) :
    Integrable (fun x => u x * (fderiv ℝ φ x) h) (volume.restrict D) := by
  exact hu.integrable_mul (hφ.memLp_directional h)

lemma integrable_inner_test (hG : MemLp G 2 (volume.restrict D))
    {φ : Space d → ℝ} (hφ : Test D φ) (h : Space d) :
    Integrable (fun x => inner ℝ (G x) h * φ x) (volume.restrict D) := by
  exact (memLp_inner_const hG h).integrable_mul hφ.memLp

lemma H1.add (hu : H1 D u G) (hv : H1 D v V) :
    H1 D (fun x => u x + v x) (fun x => G x + V x) := by
  refine ⟨hu.1.add hv.1, hu.2.1.add hv.2.1, ?_⟩
  intro φ hφ h
  simp_rw [add_mul, inner_add_left]
  rw [integral_add (integrable_deriv_product hu.1 hφ h)
      (integrable_deriv_product hv.1 hφ h)]
  simp_rw [add_mul]
  rw [integral_add (integrable_inner_test hu.2.1 hφ h)
      (integrable_inner_test hv.2.1 hφ h), hu.2.2 φ hφ h, hv.2.2 φ hφ h]
  ring

lemma H1.const_smul (hu : H1 D u G) (t : ℝ) :
    H1 D (fun x => t * u x) (fun x => t • G x) := by
  refine ⟨hu.1.const_mul t, hu.2.1.const_smul t, ?_⟩
  intro φ hφ h
  simp_rw [real_inner_smul_left, mul_assoc]
  rw [integral_const_mul, integral_const_mul, hu.2.2 φ hφ h]
  ring

end SobolevLinear

section Variations
variable {d : ℕ} {D : Set (Space d)}

lemma integrable_phase {μ : Measure (Space d)} [IsFiniteMeasure μ]
    {u : Space d → ℝ} (hu : AEStronglyMeasurable u μ) :
    Integrable (fun x => if 0 < u x then (1 : ℝ) else 0) μ := by
  have hm : Measurable (fun t : ℝ => if 0 < t then (1 : ℝ) else 0) :=
    Measurable.ite measurableSet_Ioi measurable_const measurable_const
  apply (integrable_const (1 : ℝ)).mono'
    (hm.comp_aemeasurable hu.aemeasurable).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun x => by
    change ‖(if 0 < u x then (1 : ℝ) else 0)‖ ≤ 1
    split_ifs <;> norm_num)

end Variations

end Bernoulli

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology Convolution

namespace Bernoulli
open scoped _root_.Bernoulli
namespace LipschitzSobolev
variable {d : ℕ} {u : Space d → ℝ} {K : NNReal}

lemma measurable_gradient : Measurable (gradient u) := by
  exact (InnerProductSpace.toDual ℝ (Space d)).symm.continuous.measurable.comp
    (measurable_fderiv ℝ u)

lemma norm_gradient_le (hu : LipschitzWith K u) (x : Space d) :
    ‖gradient u x‖ ≤ K := by
  simpa only [gradient, LinearIsometryEquiv.norm_map] using
    norm_fderiv_le_of_lipschitz ℝ (x₀ := x) hu

lemma weakGradient (hu : LipschitzWith K u) (D : Set (Space d)) :
    WeakGradient D u (gradient u) := by
  intro φ hφ h
  have hφdiff := hφ.1.differentiable (by simp)
  obtain ⟨C, hφlip⟩ := hφ.1.lipschitzWith_of_hasCompactSupport hφ.2.1 (by simp)
  have heq := hu.integral_lineDeriv_mul_eq (μ := volume) hφlip hφ.2.1 h
  have hleft : (fun x => lineDeriv ℝ u x h * φ x) =ᵐ[volume]
      (fun x => inner ℝ (gradient u x) h * φ x) := by
    filter_upwards [hu.ae_differentiableAt] with x hx
    rw [hx.lineDeriv_eq_fderiv, inner_gradient_left]
  have hright : (fun x => lineDeriv ℝ φ x (-h) * u x) =
      (fun x => -(u x * (fderiv ℝ φ x) h)) := by
    funext x
    rw [(hφdiff x).lineDeriv_eq_fderiv, map_neg]
    ring
  rw [integral_congr_ae hleft, hright, integral_neg] at heq
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
      have hne : x ∉ tsupport φ := fun hx' => hx (hφ.2.2 hx')
      rw [fderiv_of_notMem_tsupport ℝ hne, zero_apply, mul_zero]),
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
      rw [hφ.eq_zero_outside hx, mul_zero])]
  linarith

lemma h1_ball (hu : LipschitzWith K u) (c : Space d) (r : ℝ) :
    H1 (Metric.ball c r) u (gradient u) := by
  let : IsFiniteMeasure (volume.restrict (Metric.ball c r)) :=
    isFiniteMeasure_restrict.mpr measure_ball_lt_top.ne
  refine ⟨?_, ?_, weakGradient hu _⟩
  · apply MemLp.of_bound hu.continuous.aestronglyMeasurable (‖u c‖ + K * max r 0)
    filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
    calc ‖u x‖ ≤ ‖u c‖ + ‖u x - u c‖ := norm_le_insert' _ _
      _ ≤ ‖u c‖ + K * dist x c := by
        gcongr
        simpa only [dist_eq_norm] using hu.norm_sub_le x c
      _ ≤ ‖u c‖ + K * max r 0 := by
        gcongr
        exact (Metric.mem_ball.mp hx).le.trans (le_max_left _ _)
  · exact MemLp.of_bound measurable_gradient.aestronglyMeasurable K
      (Filter.Eventually.of_forall (norm_gradient_le hu))

end LipschitzSobolev
end Bernoulli

namespace Bernoulli
open scoped _root_.Bernoulli

lemma H1.sub {d : ℕ} {D : Set (Space d)} {u v : Space d → ℝ}
    {G V : Space d → Space d} (hu : H1 D u G) (hv : H1 D v V) :
    H1 D (fun x => u x - v x) (fun x => G x - V x) := by
  simpa only [neg_one_mul, neg_one_smul, sub_eq_add_neg] using hu.add (hv.const_smul (-1))

end Bernoulli

open scoped Manifold
namespace Bernoulli
open scoped _root_.Bernoulli
lemma exists_cutoff {d : ℕ} {K D : Set (Space d)} (hK : IsCompact K)
    (hD : IsOpen D) (hKD : K ⊆ D) :
    ∃ φ : Space d → ℝ, ContDiff ℝ ∞ φ ∧ HasCompactSupport φ ∧ tsupport φ ⊆ D ∧
      (∀ᶠ x in 𝓝ˢ K, φ x = 1) ∧ (∀ x, 0 ≤ φ x ∧ φ x ≤ 1) := by
  obtain ⟨δ, hδ, hδD⟩ := hK.exists_thickening_subset_open hD hKD
  have hki : K ⊆ interior (Metric.cthickening (δ/2) K) := by
    exact (Metric.self_subset_thickening (half_pos hδ) _).trans
      (Metric.thickening_subset_interior_cthickening _ _)
  obtain ⟨φ, hφ1, hφ0, hφb⟩ := exists_contMDiffMap_one_nhds_of_subset_interior
    (𝓘(ℝ, Space d)) (n := ⊤) hK.isClosed hki
  refine ⟨φ, φ.contMDiff.contDiff, HasCompactSupport.intro (hK.cthickening) hφ0, ?_, hφ1, hφb⟩
  have hs : tsupport (φ : Space d → ℝ) ⊆ Metric.cthickening (δ/2) K := by
    apply closure_minimal _ Metric.isClosed_cthickening
    intro x hx
    by_contra hn
    exact hx (hφ0 x hn)
  exact hs.trans ((Metric.cthickening_subset_thickening' hδ (by linarith) _).trans hδD)
end Bernoulli

end
end
end

end OAI
end

section
-- module Solutions.OAIQW_BernoulliCone.LowerSupport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE uι

section
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology ContDiff

noncomputable section
open Set Filter Finset
open scoped Topology
namespace Bernoulli.DeSilvaJerison

lemma root_unique {t : ℝ} (ht : t ∈ Ico (0 : ℝ) 1) (hf : f t = 0) : t = t7 := by
  exact f_strictAnti.injOn ht ⟨t7_pos.le,t7_lt_one⟩ (hf.trans f_t7.symm)

lemma fp_t7 : fp t7 = -1 / (t7 * (1-t7^2)^3) := by
  have h := f_relation ⟨by linarith [t7_pos],t7_lt_one⟩
  rw [f_t7,sub_zero] at h
  calc
    fp t7 = (-1 / (1-t7^2)^3) / t7 :=
      (eq_div_iff (ne_of_gt t7_pos)).mpr (by rw [mul_comm]; exact h)
    _ = _ := by rw [div_div, mul_comm]

lemma c7_eq : c7 = 1 / (t7^2 * (1-t7^2)^5) := by
  have ht : t7≠0 := ne_of_gt t7_pos
  have hd : 1-t7^2≠0 := ne_of_gt (show 0<1-t7^2 by nlinarith [t7_pos,t7_lt_one])
  rw [c7,fp_t7]
  field_simp

lemma p_le_one (t : ℝ) : p t ≤ 1 := by
  rw [p, ← f_zero]
  apply f_strictAnti.antitoneOn ⟨le_rfl,by norm_num⟩
    ⟨le_min (abs_nonneg _) t7_pos.le, (min_le_right _ _).trans_lt t7_lt_one⟩
  exact le_min (abs_nonneg _) t7_pos.le

lemma exists_lipschitz_p : ∃ K : NNReal, LipschitzWith K p := by
  have hc : ContDiffOn ℝ 1 f (Icc 0 t7) := by
    intro t ht
    exact (contDiffAt_f ⟨by linarith [ht.1],ht.2.trans_lt t7_lt_one⟩).contDiffWithinAt
  obtain ⟨K,hK⟩ := hc.exists_lipschitzOnWith (by norm_num) (convex_Icc 0 t7) isCompact_Icc
  have hclip : LipschitzWith 1 (fun t : ℝ => min |t| t7) := by
    simpa only [Real.norm_eq_abs] using ((lipschitzWith_one_norm : LipschitzWith 1 (fun t : ℝ => ‖t‖)).min_const t7)
  refine ⟨K, LipschitzWith.of_dist_le_mul (fun x y => ?_)⟩
  have hm (t : ℝ) : min |t| t7 ∈ Icc 0 t7 :=
    ⟨le_min (abs_nonneg _) t7_pos.le, min_le_right _ _⟩
  exact (hK.dist_le_mul _ (hm x) _ (hm y)).trans (by
    have hh := hclip.dist_le_mul x y
    norm_num at hh
    exact mul_le_mul_of_nonneg_left hh K.coe_nonneg)

lemma κ_sq : κ^2 * c7 = 1 := by
  rw [κ, inv_pow, Real.sq_sqrt c7_pos.le]
  exact inv_mul_cancel₀ (ne_of_gt c7_pos)

end Bernoulli.DeSilvaJerison

/-! The concrete seven-dimensional cone belonging to the De Silva–Jerison profile.
These are actual function/Sobolev constructions, not an assumption of minimality. -/
namespace Bernoulli.DeSilvaJerison

lemma Z_le_norm (x : Space 7) : Z x ≤ ‖x‖ := by
  calc Z x ≤ ‖x‖ * 1 := mul_le_mul_of_nonneg_left (p_le_one _) (norm_nonneg x)
    _ = _ := mul_one _

lemma coordinate_le_norm (x : Space 7) : |x 6| ≤ ‖x‖ := by
  simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le x (6 : Fin 7)

lemma angular_estimate {x y : Space 7} (hx : x≠0) (hy : y≠0) :
    ‖y‖ * |x 6/‖x‖ - y 6/‖y‖| ≤ 2*‖x-y‖ := by
  have hr : 0<‖x‖ := norm_pos_iff.mpr hx
  have hs : 0<‖y‖ := norm_pos_iff.mpr hy
  have hq : |x 6/‖x‖| ≤ 1 := by
    rw [abs_div,abs_of_pos hr]
    exact (div_le_one hr).mpr (coordinate_le_norm x)
  have hxy : |x 6-y 6| ≤ ‖x-y‖ := by
    simpa only [PiLp.sub_apply] using coordinate_le_norm (x-y)
  calc
    ‖y‖ * |x 6/‖x‖ - y 6/‖y‖| =
        |(‖y‖-‖x‖)*(x 6/‖x‖) + (x 6-y 6)| := by
      rw [← abs_of_pos hs, ← abs_mul]
      congr 1
      rw [abs_of_pos hs]
      field_simp
      ring
    _ ≤ |‖y‖-‖x‖| * |x 6/‖x‖| + |x 6-y 6| := by
      simpa only [abs_mul] using abs_add_le ((‖y‖-‖x‖)*(x 6/‖x‖)) (x 6-y 6)
    _ ≤ |‖y‖-‖x‖| * 1 + ‖x-y‖ := by gcongr
    _ ≤ ‖x-y‖ + ‖x-y‖ := by
      rw [mul_one]
      gcongr
      simpa only [norm_sub_rev] using abs_norm_sub_norm_le y x
    _ = _ := by ring

lemma exists_lipschitz_Z : ∃ K : NNReal, LipschitzWith K Z := by
  obtain ⟨K,hK⟩ := exists_lipschitz_p
  refine ⟨1+2*K, LipschitzWith.of_dist_le_mul (fun x y => ?_)⟩
  simp only [dist_eq_norm, Real.norm_eq_abs, NNReal.coe_add, NNReal.coe_mul,
    NNReal.coe_one, NNReal.coe_ofNat]
  by_cases hx : x=0
  · subst x
    rw [Z_zero,zero_sub,abs_neg,abs_of_nonneg (Z_nonneg y),zero_sub,norm_neg]
    exact (Z_le_norm y).trans (by nlinarith [K.coe_nonneg,norm_nonneg y])
  by_cases hy : y=0
  · subst y
    rw [Z_zero,sub_zero,abs_of_nonneg (Z_nonneg x),sub_zero]
    exact (Z_le_norm x).trans (by nlinarith [K.coe_nonneg,norm_nonneg x])
  have hpd : |p (x 6/‖x‖)-p (y 6/‖y‖)| ≤ K * |x 6/‖x‖- y 6/‖y‖| := by
    simpa only [Real.dist_eq] using hK.dist_le_mul (x 6/‖x‖) (y 6/‖y‖)
  have hpb : |p (x 6/‖x‖)| ≤ 1 := by
    rw [abs_of_nonneg (p_nonneg _)]
    exact p_le_one _
  calc
    |Z x-Z y| = |(‖x‖-‖y‖)*p (x 6/‖x‖) + ‖y‖*(p (x 6/‖x‖)-p (y 6/‖y‖))| := by
      unfold Z
      congr 1
      ring
    _ ≤ |‖x‖-‖y‖| * |p (x 6/‖x‖)| + ‖y‖* |p (x 6/‖x‖)-p (y 6/‖y‖)| := by
      simpa only [abs_mul, abs_of_nonneg (norm_nonneg y)] using
        abs_add_le ((‖x‖-‖y‖)*p (x 6/‖x‖)) (‖y‖*(p (x 6/‖x‖)-p (y 6/‖y‖)))
    _ ≤ |‖x‖-‖y‖| * 1 + ‖y‖*(K* |x 6/‖x‖-y 6/‖y‖|) := by gcongr
    _ = |‖x‖-‖y‖| + K*(‖y‖* |x 6/‖x‖-y 6/‖y‖|) := by ring
    _ ≤ ‖x-y‖ + K*(2*‖x-y‖) := by
      exact add_le_add (abs_norm_sub_norm_le x y)
        (mul_le_mul_of_nonneg_left (angular_estimate hx hy) K.coe_nonneg)
    _ = _ := by ring

lemma exists_lipschitz_U : ∃ K : NNReal, LipschitzWith K U := by
  obtain ⟨K,hK⟩ := exists_lipschitz_Z
  exact ⟨‖κ‖₊*K, (lipschitzWith_smul κ).comp hK⟩

lemma U_continuous : Continuous U := exists_lipschitz_U.choose_spec.continuous

end Bernoulli.DeSilvaJerison

/-! Euclidean calculus for the actual De Silva–Jerison axisymmetric construction.
No free-boundary or variational conclusion is built into these definitions. -/
noncomputable section
open Set Filter Finset
open scoped Topology ContDiff Laplacian
namespace Bernoulli.Axisymmetric
variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma radial_norm {x : E} (hx : x≠0) : ‖radial x‖=1 := by
  rw [radial,norm_smul,Real.norm_eq_abs,abs_inv,abs_norm,inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx)]

lemma radial_inner (x e : E) : inner ℝ (radial x) e = inner ℝ x e / ‖x‖ := by
  simp only [radial,real_inner_smul_left,div_eq_mul_inv,mul_comm]

lemma norm_sq_polarGradient {e x : E} (he : ‖e‖=1) (hx : x≠0) (a b : ℝ) :
    ‖polarGradient e x a b‖^2 = a^2 + (1-(inner ℝ x e / ‖x‖)^2)*b^2 := by
  have hn : inner ℝ (radial x) (radial x)=1 := by
    rw [real_inner_self_eq_norm_sq,radial_norm hx]; norm_num
  have het : inner ℝ e e=1 := by rw [real_inner_self_eq_norm_sq,he]; norm_num
  have hrev : inner ℝ e (radial x) = inner ℝ x e / ‖x‖ :=
    (real_inner_comm e (radial x)).symm.trans (radial_inner x e)
  rw [←real_inner_self_eq_norm_sq]
  simp only [polarGradient,inner_add_left,inner_add_right,inner_sub_left,inner_sub_right,
    real_inner_smul_left,real_inner_smul_right,hn,het,hrev,radial_inner]
  ring

lemma gradient_lift_norm_sq [CompleteSpace E] {φ : ℝ → ℝ} {φ₁ : ℝ}
    (e x : E) (α : ℝ) (he : ‖e‖=1) (hx : x≠0)
    (hφ : HasDerivAt φ φ₁ (inner ℝ x e / ‖x‖)) :
    ‖gradient (lift e α φ) x‖^2 = (‖x‖^α / ‖x‖)^2 *
      ((α*φ (inner ℝ x e / ‖x‖))^2+(1-(inner ℝ x e / ‖x‖)^2)*φ₁^2) := by
  rw [(hasGradientAt_lift e x α hx hφ).gradient,norm_smul,mul_pow]
  rw [norm_sq_polarGradient he hx]
  simp only [Real.norm_eq_abs,sq_abs]

end Bernoulli.Axisymmetric

namespace Bernoulli.DeSilvaJerison
open Axisymmetric InnerProductSpace
open scoped Laplacian ContDiff

lemma fp_neg_arg (t : ℝ) : fp (-t)= -fp t := by
  simp only [fp,neg_sq,A_neg]
  ring

lemma f_zero_at_boundary {t : ℝ} (ht : |t|=t7) : f t=0 := by
  rw [←f_abs,ht,f_t7]

lemma fp_sq_at_boundary {t : ℝ} (ht : |t|=t7) : (fp t)^2=(fp t7)^2 := by
  have h : (fp |t|)^2=(fp t)^2 := by
    rcases le_total 0 t with h|h
    · rw [abs_of_nonneg h]
    · rw [abs_of_nonpos h,fp_neg_arg,neg_sq]
  rw [ht] at h
  exact h.symm

lemma signed_gradient_norm_sq {x : Space 7} (hx : x≠0) (ha : |angle x|<1) :
    ‖gradient Zsigned x‖^2=(f (angle x))^2+(1-(angle x)^2)*(fp (angle x))^2 := by
  have ha' : |inner ℝ x axis/‖x‖|<1 := by simpa only [inner_axis,angle] using ha
  have hh := gradient_lift_norm_sq axis x 1 axis_norm hx (hasDerivAt_f (abs_lt.mp ha'))
  simpa only [Zsigned,inner_axis,angle,Real.rpow_one,div_self (norm_ne_zero_iff.mpr hx),one_pow,one_mul] using hh

/-- Exact slope-squared c7 on the boundary of the unnormalized cone. -/
lemma Zsigned_boundary_slope {x : Space 7} (hx : x≠0) (ha : |angle x|=t7) :
    ‖gradient Zsigned x‖^2=c7 := by
  rw [signed_gradient_norm_sq hx (ha.trans_lt t7_lt_one),f_zero_at_boundary ha,
    fp_sq_at_boundary ha]
  have hs : (angle x)^2=t7^2 := by rw [←sq_abs,ha]
  simp only [hs,zero_pow (by norm_num : 2≠0),zero_add,c7]

end Bernoulli.DeSilvaJerison

namespace Bernoulli.DeSilvaJerison
open scoped BigOperators

lemma f_series_lower (n:ℕ) {t:ℝ} (ht:0≤t) (ht1:t<1) :
    (8-25*t^2+15*(t^2)^2)/(8*(1-t^2)^2)
      -15/8*t^2*(B n (t^2)+(t^2)^n/(1-t^2)) ≤ f t := by
  have ha := (A_series_bounds n ht ht1).2
  have hp := mul_le_mul_of_nonneg_left ha (show (0:ℝ)≤15/8*t from by positivity)
  unfold f
  convert! sub_le_sub_left hp ((8-25*t^2+15*t^4)/(8*(1-t^2)^2)) using 1
  ring

lemma fp_series_upper (n:ℕ) {t:ℝ} (ht:0≤t) (ht1:t<1) :
    fp t ≤ -t*(1/(1-t^2)^3+5/4/(1-t^2)^2+15/8/(1-t^2)+15/8*B n (t^2)) := by
  have ha := (A_series_bounds n ht ht1).1
  unfold fp
  have hp := mul_le_mul_of_nonneg_left ha (show (0:ℝ)≤15/8 from by norm_num)
  convert! sub_le_sub_left hp (-t/(1-t^2)^3-5/4*t/(1-t^2)^2-15/8*t/(1-t^2)) using 1
  ring

end Bernoulli.DeSilvaJerison

noncomputable section
open scoped BigOperators

namespace Bernoulli.DeSilvaJerison

lemma fp_strictAnti : StrictAntiOn fp (Ico (0:ℝ) 1) := by
  apply strictAntiOn_of_deriv_neg (convex_Ico 0 1)
  · intro t ht
    exact (hasDerivAt_fp ⟨by linarith [ht.1],ht.2⟩).continuousAt.continuousWithinAt
  · intro t ht
    rw [interior_Ico] at ht
    rw [(hasDerivAt_fp ⟨by linarith [ht.1],ht.2⟩).deriv]
    have hp : 0<1-t^2 := by nlinarith [ht.1,ht.2]
    exact div_neg_of_neg_of_pos (by norm_num) (pow_pos hp 4)

end Bernoulli.DeSilvaJerison

end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQW_BernoulliCone.CylindricalCalculus
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE

section
noncomputable section
open Set Filter Finset
open scoped Topology ContDiff Laplacian
namespace Bernoulli.Cylindrical
open ScalarLaplacian
variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
theorem transverse_inner [FiniteDimensional ℝ E] (e x:E) (he:‖e‖=1) : inner ℝ (transverse e x) e=0 := by
  simp [transverse,axis,inner_sub_left,real_inner_smul_left,he]
end Bernoulli.Cylindrical

end
end

end OAI
end

section
-- module Solutions.OAIQW_BernoulliCone.UpperSupport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Filter Finset
open scoped Topology ContDiff Laplacian
namespace Bernoulli.DeSilvaJerison.UpperAlgebra

lemma identity_lo (x:ℝ) :
    17734/1000*denominator (729/2500+171/2500*x)-
      numerator (729/2500+171/2500*x) (flo (729/2500+171/2500*x))=bern_lo x := by
  unfold denominator numerator flo bern_lo
  ring
lemma bound_lo {u:ℝ} (hl:729/2500≤u) (hr:u≤9/25) :
    numerator u (flo u) ≤ 17734/1000*denominator u := by
  let x:ℝ := (u-729/2500)/(171/2500)
  have hx:0≤x := by dsimp [x]; linarith
  have hx1:x≤1 := by dsimp [x]; linarith
  have he:u=729/2500+171/2500*x := by dsimp [x]; ring
  have hh:0≤bern_lo x := by
    have hy:0≤1-x:=sub_nonneg.mpr hx1
    unfold bern_lo
    positivity
  have hid:=identity_lo x
  rw [←he] at hid
  linarith

lemma identity_hi (x:ℝ) :
    17734/1000*denominator (729/2500+171/2500*x)-
      numerator (729/2500+171/2500*x) (fhi (729/2500+171/2500*x))=bern_hi x := by
  unfold denominator numerator fhi bern_hi
  ring
lemma bound_hi {u:ℝ} (hl:729/2500≤u) (hr:u≤9/25) :
    numerator u (fhi u) ≤ 17734/1000*denominator u := by
  let x:ℝ := (u-729/2500)/(171/2500)
  have hx:0≤x := by dsimp [x]; linarith
  have hx1:x≤1 := by dsimp [x]; linarith
  have he:u=729/2500+171/2500*x := by dsimp [x]; ring
  have hh:0≤bern_hi x := by
    have hy:0≤1-x:=sub_nonneg.mpr hx1
    unfold bern_hi
    positivity
  have hid:=identity_hi x
  rw [←he] at hid
  linarith
end Bernoulli.DeSilvaJerison.UpperAlgebra

namespace Bernoulli.DeSilvaJerison

lemma qSup_eq {t:ℝ} (ht:|t|<1) : qSup t=gSup1 t/gSup t := by
  have hd:1-t^2≠0 := by obtain ⟨h1,h2⟩:=abs_lt.mp ht; nlinarith
  have hp:1+t^2≠0 := by positivity
  unfold qSup gSup gSup1
  field_simp

lemma hasDerivAt_qSup {t:ℝ} (ht:|t|<1) : HasDerivAt qSup (qSup1 t) t := by
  have hd:1-t^2≠0 := by obtain ⟨h1,h2⟩:=abs_lt.mp ht; nlinarith
  have hp:1+t^2≠0 := by positivity
  have hT:=(hasDerivAt_id t).pow 2
  convert! ((((hasDerivAt_id t).const_mul 2).mul ((hasDerivAt_const t (3:ℝ)).add hT)).div
    (((hasDerivAt_const t (1:ℝ)).sub hT).mul ((hasDerivAt_const t (1:ℝ)).add hT))
    (mul_ne_zero hd hp)) using 1
  norm_num only [qSup1,qSup,id_eq,pow_one,Pi.add_apply,Pi.sub_apply,Pi.mul_apply,Pi.pow_apply]
  field_simp [hd,hp]
  ring

lemma hasDerivAt_GSup {t:ℝ} (ht:t∈Ioo (-1:ℝ) 1) :
    HasDerivAt GSup (2*((5*t-(1-t^2)*qSup t)*(fp t-f t*qSup t)^2-
      3*f t*(fp t-4*f t*qSup t))) t := by
  have hh:=(((hasDerivAt_f ht).pow 2).const_mul 9).add
    (((hasDerivAt_const t (1:ℝ)).sub ((hasDerivAt_id t).pow 2)).mul
      (((hasDerivAt_fp ht).sub ((hasDerivAt_f ht).mul (hasDerivAt_qSup (abs_lt.mpr ht)))).pow 2))
  have hd:1-t^2≠0 := by nlinarith [ht.1,ht.2]
  have hR:=f_relation ht
  have hODE:(1-t^2)*(-6/(1-t^2)^4)=6*t*fp t-6*f t := by
    field_simp at hR ⊢
    nlinarith
  convert! hh using 1
  norm_num only [id_eq,pow_one,Pi.add_apply,Pi.sub_apply,Pi.mul_apply,Pi.pow_apply]
  have hF : -6/(1-t^2)^4=(6*t*fp t-6*f t)/(1-t^2) := by
    apply (eq_div_iff hd).mpr
    nlinarith [hODE]
  rw [hF]
  unfold qSup1
  field_simp [hd]
  ring

lemma upper_endpoint_bounds : -1/8≤f (27/50) ∧ fp (1/2)≤-4 := by
  constructor
  · have hh:=f_series_lower 6 (t:=27/50) (by norm_num) (by norm_num)
    norm_num [B,Finset.sum_range_succ] at hh ⊢
    linarith
  · have hh:=fp_series_upper 1 (t:=1/2) (by norm_num) (by norm_num)
    norm_num [B,Finset.sum_range_succ] at hh ⊢
    linarith

lemma qSup_small {t:ℝ} (h0:0≤t) (hb:t≤27/50) :
    0≤qSup t ∧ qSup t≤4 ∧ 5*t≤(1-t^2)*qSup t := by
  have hd:0<1-t^2:=by nlinarith
  have hp:0<1+t^2:=by positivity
  have hu:t^2≤729/2500 := by nlinarith
  constructor
  · unfold qSup; positivity
  constructor
  · rw [qSup,div_le_iff₀ (mul_pos hd hp)]
    have h1:2*t*(3+t^2)≤(27/25:ℝ)*(3+729/2500) := by
      exact mul_le_mul (by linarith) (by linarith) (by positivity) (by norm_num)
    have h2:(1-t^2)*(1+t^2)≥1-(729/2500:ℝ)^2 := by nlinarith [sq_nonneg (t^2-729/2500)]
    nlinarith
  · have he:(1-t^2)*qSup t-5*t=t*(1-3*t^2)/(1+t^2) := by
      unfold qSup
      field_simp [ne_of_gt hd,ne_of_gt hp]
      ring
    have hz:0≤1-3*t^2 := by nlinarith
    have hh:0≤t*(1-3*t^2)/(1+t^2) := by positivity
    linarith

end Bernoulli.DeSilvaJerison

namespace Bernoulli.DeSilvaJerison

lemma c7_lower : 17734/1000≤c7 := by
  have hl:t7^2≤(517331/1000000:ℝ)^2 := by nlinarith [t7_bounds.2,t7_pos]
  have hu:1-t7^2≤1-(517330/1000000:ℝ)^2 := by nlinarith [t7_bounds.1,t7_pos]
  have hd:0<1-t7^2 := by nlinarith [t7_pos,t7_lt_one]
  have hp:=pow_le_pow_left₀ hd.le hu 5
  have hm:=mul_le_mul hl hp (by positivity : (0:ℝ)≤(1-t7^2)^5) (by norm_num)
  rw [c7_eq]
  apply (le_div_iff₀ (mul_pos (sq_pos_of_pos t7_pos) (pow_pos hd 5))).mpr
  nlinarith

lemma numerator_scaled_bounds {t:ℝ} (hl:0≤t) (hr:t<1) :
    UpperAlgebra.flo (t^2) ≤ 8*(1-t^2)^2*f t ∧
      8*(1-t^2)^2*f t≤UpperAlgebra.fhi (t^2) := by
  have hd:0<1-t^2:=by nlinarith
  have hL:=f_series_lower 6 hl hr
  have hU: f t≤(8-25*t^2+15*(t^2)^2)/(8*(1-t^2)^2)-15/8*t^2*B 6 (t^2) := by
    have hh := mul_le_mul_of_nonneg_left (A_series_bounds 6 hl hr).1 (show (0:ℝ)≤15/8*t by positivity)
    unfold f
    have hp : (t^2)^2=t^4 := by ring
    rw [hp]
    linear_combination hh
  constructor
  · have he:UpperAlgebra.flo (t^2)/(8*(1-t^2)^2)=
        (8-25*t^2+15*(t^2)^2)/(8*(1-t^2)^2)-15/8*t^2*(B 6 (t^2)+(t^2)^6/(1-t^2)) := by
      unfold UpperAlgebra.flo B
      norm_num [Finset.sum_range_succ]
      field_simp [ne_of_gt hd]
      ring
    rw [←he] at hL
    exact (div_le_iff₀ (by positivity)).mp hL |>.trans_eq (mul_comm _ _)
  · have he:UpperAlgebra.fhi (t^2)/(8*(1-t^2)^2)=
        (8-25*t^2+15*(t^2)^2)/(8*(1-t^2)^2)-15/8*t^2*B 6 (t^2) := by
      unfold UpperAlgebra.fhi B
      norm_num [Finset.sum_range_succ]
      field_simp [ne_of_gt hd]
      ring
    rw [←he] at hU
    simpa only [mul_comm] using (le_div_iff₀ (by positivity)).mp hU

lemma quadratic_bound {A B C L H X R:ℝ} (hA:0≤A) (hXL:L≤X) (hXH:X≤H)
    (hL:A*L^2+B*L+C≤R) (hH:A*H^2+B*H+C≤R) :
    A*X^2+B*X+C≤R := by
  by_cases he:L=H
  · have hx:X=L:=by linarith
    simpa only [hx] using hL
  have hLH:0<H-L:=by have:=lt_of_le_of_ne (hXL.trans hXH) he; linarith
  have hp:=mul_nonneg hA (mul_nonneg (sub_nonneg.mpr hXL) (sub_nonneg.mpr hXH))
  have heq:(H-X)*(A*L^2+B*L+C)+(X-L)*(A*H^2+B*H+C)-
      (H-L)*(A*X^2+B*X+C)=(H-L)*(A*((X-L)*(H-X))) := by ring
  have hlo:=mul_le_mul_of_nonneg_left hL (sub_nonneg.mpr hXH)
  have hhi:=mul_le_mul_of_nonneg_left hH (sub_nonneg.mpr hXL)
  have hs:(H-L)*(A*X^2+B*X+C)≤(H-L)*R := by
    nlinarith [mul_nonneg hLH.le hp]
  exact (mul_le_mul_iff_right₀ hLH).mp (by simpa only [mul_comm] using hs)

lemma GSup_numerator {t:ℝ} (ht:0<t) (hr:t<1) :
    GSup t * UpperAlgebra.denominator (t^2) =
      UpperAlgebra.numerator (t^2) (8*(1-t^2)^2*f t) := by
  have hd:1-t^2≠0:=by nlinarith
  have hp:1+t^2≠0:=by positivity
  have hR:=f_relation (show t∈Ioo (-1:ℝ) 1 from ⟨by linarith,hr⟩)
  have he:fp t=(f t-1/(1-t^2)^3)/t := by
    apply (eq_div_iff ht.ne').mpr
    linear_combination hR
  rw [GSup,he]
  unfold qSup UpperAlgebra.denominator UpperAlgebra.numerator
  field_simp [hd,hp,ht.ne']
  ring

end Bernoulli.DeSilvaJerison
namespace Bernoulli.DeSilvaJerison

lemma capHP_end : capHP (3/4)=capAmplitude/6-3125/768 := by
  have hh:=f_relation (t:=3/5) (by norm_num)
  rw [capHP,capAngle_end,capRadius_end,capAmplitude]
  norm_num at hh ⊢
  linear_combination (16/15)*hh

end Bernoulli.DeSilvaJerison

noncomputable section

namespace Bernoulli.DeSilvaJerison

lemma capH_nonneg {s:ℝ} (hs:|s|≤3/4) :0≤capH s := by
  have hh:=capH_antitone (show (|s|:ℝ)∈Set.Ici 0 from abs_nonneg s) (by norm_num : (3/4:ℝ)∈Set.Ici 0) hs
  rw [capH_end] at hh
  rcases le_total 0 s with hp|hn
  · simpa only [abs_of_nonneg hp] using hh
  · simpa only [abs_of_nonpos hn,capH_even] using hh

end Bernoulli.DeSilvaJerison

namespace Bernoulli.DeSilvaJerison

lemma capP_bounds : 3884/10000≤capP ∧ capP≤3886/10000 := by
  have hh:=capB_bounds
  unfold capB at hh
  constructor <;> linarith [hh.1,hh.2]

end Bernoulli.DeSilvaJerison
end
end
end

end OAI
end

section
-- module Solutions.OAIQW_BernoulliCone.CapGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Filter
open scoped Topology ContDiff Laplacian
namespace Bernoulli.DeSilvaJerison

lemma capHP_sq_abs (s:ℝ) : (capHP |s|)^2=(capHP s)^2 := by
  rcases le_total 0 s with h|h
  · rw [abs_of_nonneg h]
  · rw [abs_of_nonpos h,capHP_odd,neg_sq]
lemma capH_boundary {s:ℝ} (hs:|s|=3/4) : capH s=0 := by
  rw [←capH_abs,hs,capH_end]
lemma capHP_sq_boundary {s:ℝ} (hs:|s|=3/4) : (capHP s)^2=(capHP (3/4))^2 := by
  rw [←capHP_sq_abs,hs]

/-- Constant free-boundary slope of the actual cylindrical cap, including the
transverse axis. The result is for the genuine Euclidean gradient. -/
theorem smoothCap_boundary_gradient {x:Space 7} (hx:Cylindrical.radiusSq axis x≤1)
    (hs:|Cylindrical.axis axis x/CapAlgebra.V (Cylindrical.radiusSq axis x) capB|=3/4) :
    ‖gradient smoothCap x‖^2=capC^2*(capHP (3/4))^2 := by
  let q:=Cylindrical.radiusSq axis x
  let a:=Cylindrical.axis axis x
  let V:=CapAlgebra.V q capB
  let H:=CapAlgebra.H q capB
  let s:=a/V
  have hq:0≤q:=Cylindrical.radiusSq_nonneg axis x axis_norm
  have hv:0<V:= (CapAlgebra.V_bounds hq hx capB_bounds.1 capB_bounds.2).1
  have hh:0<H:=CapAlgebra.H_pos hq
  have hs2 : s^2=9/16 := by nlinarith only [sq_abs s,hs]
  have hz : capH s=0 := capH_boundary hs
  have hp : (capHP s)^2=(capHP (3/4))^2 := capHP_sq_boundary hs
  have hg:=gradient_smoothCap hx
  dsimp only at hg
  change gradient smoothCap x=(2*CapAlgebra.Y1 q capB capC*capH s) • Cylindrical.transverse axis x+
    (CapAlgebra.Y q capB capC*capHP s) •
      (V⁻¹ • axis+(-a*CapAlgebra.D q capB/V^2) • Cylindrical.transverse axis x) at hg
  rw [hz] at hg
  simp only [mul_zero,zero_smul,zero_add] at hg
  have horth:inner ℝ axis (Cylindrical.transverse axis x)=0 := by
    rw [real_inner_comm,Cylindrical.transverse_inner axis x axis_norm]
  rw [hg,norm_smul,Real.norm_eq_abs,mul_pow,sq_abs,norm_add_sq_real]
  simp only [norm_smul,Real.norm_eq_abs,mul_pow,sq_abs,axis_norm,mul_one,
    real_inner_smul_left,real_inner_smul_right,horth,mul_zero,add_zero,
    Cylindrical.transverse_sq axis x axis_norm]
  change (CapAlgebra.Y q capB capC)^2*(capHP s)^2*
    ((V⁻¹)^2+(-a*CapAlgebra.D q capB/V^2)^2*q)=_
  have he : ((V⁻¹)^2+(-a*CapAlgebra.D q capB/V^2)^2*q)=H/V^2 := by
    have hhdef : H=1+9/16*q*(CapAlgebra.D q capB)^2:=rfl
    have ha2 : a^2=9/16*V^2 := by
      dsimp only [s] at hs2
      field_simp at hs2
      nlinarith only [hs2]
    field_simp
    rw [ha2,hhdef]
    ring
  rw [he,hp]
  unfold CapAlgebra.Y
  change (capC*V/Real.sqrt H)^2*(capHP (3/4))^2*(H/V^2)=_
  rw [div_pow,mul_pow,Real.sq_sqrt hh.le]
  field_simp

end Bernoulli.DeSilvaJerison

end
end

end OAI
end

section
-- module Solutions.OAIQW_BernoulliCone.OuterGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Filter
open scoped Topology ContDiff Laplacian
namespace Bernoulli.DeSilvaJerison
open Axisymmetric

lemma hasDerivAt_gSup1 {t:ℝ} (ht:|t|<1) : HasDerivAt gSup1 (gSup2 t) t := by
  have hd:1-t^2≠0 := by obtain ⟨h1,h2⟩:=abs_lt.mp ht; nlinarith
  convert! ((((hasDerivAt_id t).const_mul 2).mul
    ((hasDerivAt_const t (3:ℝ)).add ((hasDerivAt_id t).pow 2))).div
      (((hasDerivAt_const t (1:ℝ)).sub ((hasDerivAt_id t).pow 2)).pow 3)
        (pow_ne_zero 3 hd)) using 1
  norm_num only [gSup1,gSup2,id_eq,pow_one,Pi.add_apply,Pi.sub_apply,Pi.pow_apply,Pi.mul_apply]
  field_simp [hd]
  ring
end Bernoulli.DeSilvaJerison

end
end

end OAI
end

section
-- module Solutions.OAIQW_BernoulliCone.StrictSlope
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Filter
open scoped Topology ContDiff Laplacian
namespace Bernoulli.DeSilvaJerison
lemma GSup_neg_deriv {t:ℝ} (hl:t7≤t) (hr:t≤27/50) : deriv GSup t<0 := by
  have ht0:0≤t:=t7_pos.le.trans hl
  have ht1:t<1:=by linarith
  have hI:t∈Ioo (-1:ℝ) 1:=⟨by linarith,ht1⟩
  have hf0:f t≤0 := by
    have hh:=f_strictAnti.antitoneOn ⟨t7_pos.le,t7_lt_one⟩ ⟨ht0,ht1⟩ hl
    simpa only [f_t7] using hh
  have hf:-1/8≤f t := upper_endpoint_bounds.1.trans
    (f_strictAnti.antitoneOn ⟨ht0,ht1⟩ (by norm_num) hr)
  have hp:fp t≤-4 := (fp_strictAnti.antitoneOn (by norm_num) ⟨ht0,ht1⟩
    (by linarith [t7_bounds.1])).trans upper_endpoint_bounds.2
  obtain ⟨hq0,hq4,hqL⟩:=qSup_small ht0 hr
  have hm:=mul_le_mul_of_nonneg_left hq4 (show 0≤-f t by linarith)
  have hB:fp t-4*f t*qSup t≤0 := by nlinarith
  have hc : 5*t-(1-t^2)*qSup t<0 := by
    have hu : t^2≤729/2500 := by nlinarith
    have hd : 1-t^2≠0 := by nlinarith
    have he : (1-t^2)*qSup t-5*t=t*(1-3*t^2)/(1+t^2) := by
      unfold qSup
      field_simp [hd,show 1+t^2≠0 by positivity]
      ring
    have hpos : 0<t*(1-3*t^2)/(1+t^2) :=
      div_pos (mul_pos (t7_pos.trans_le hl) (by linarith)) (by positivity)
    linarith
  have hbb : fp t-f t*qSup t<0 := by nlinarith
  rw [(hasDerivAt_GSup hI).deriv]
  have hh1 := mul_neg_of_neg_of_pos hc (sq_pos_of_ne_zero (ne_of_lt hbb))
  have hh2 := mul_nonneg_of_nonpos_of_nonpos hf0 hB
  nlinarith

lemma GSup_near_lt {t:ℝ} (hl:t7<t) (hr:t≤27/50) : GSup t<c7 := by
  have hanti:StrictAntiOn GSup (Icc t7 (27/50)) := by
    apply strictAntiOn_of_deriv_neg (convex_Icc _ _)
    · intro x hx
      exact (hasDerivAt_GSup ⟨by linarith [hx.1,t7_pos],by linarith [hx.2]⟩).continuousAt.continuousWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      exact GSup_neg_deriv hx.1.le hx.2.le
  have he:GSup t7=c7 := by simp [GSup,f_t7,c7]
  rw [←he]
  exact hanti ⟨le_rfl,by linarith [t7_bounds.2]⟩ ⟨hl.le,hr⟩ hl

lemma c7_lower_strict : 17734/1000<c7 := by
  have hl:t7^2≤(517331/1000000:ℝ)^2 := by nlinarith [t7_bounds.2,t7_pos]
  have hu:1-t7^2≤1-(517330/1000000:ℝ)^2 := by nlinarith [t7_bounds.1,t7_pos]
  have hd:0<1-t7^2 := by nlinarith [t7_pos,t7_lt_one]
  have hp:=pow_le_pow_left₀ hd.le hu 5
  have hm:=mul_le_mul hl hp (by positivity : (0:ℝ)≤(1-t7^2)^5) (by norm_num)
  rw [c7_eq]
  apply (lt_div_iff₀ (mul_pos (sq_pos_of_pos t7_pos) (pow_pos hd 5))).mpr
  nlinarith

lemma GSup_far_lt {t:ℝ} (hl:27/50≤t) (hr:t≤3/5) : GSup t<c7 := by
  have ht:0<t:=by linarith
  have ht1:t<1:=by linarith
  have hd:0<1-t^2:=by nlinarith
  have hul:729/2500≤t^2:=by nlinarith
  have hur:t^2≤9/25:=by nlinarith
  obtain ⟨hL,hH⟩:=numerator_scaled_bounds ht.le ht1
  have hplo:=UpperAlgebra.bound_lo hul hur
  have hphi:=UpperAlgebra.bound_hi hul hur
  have identity (F:ℝ) : UpperAlgebra.numerator (t^2) F =
      (9*t^2*(1-t^2)*(1+t^2)^2+(1-6*t^2-3*(t^2)^2)^2)*F^2+
        (-16*(1-6*t^2-3*(t^2)^2)*(1+t^2))*F+64*(1+t^2)^2 := by
    unfold UpperAlgebra.numerator
    ring
  simp only [identity] at hplo hphi
  have hA:0≤9*t^2*(1-t^2)*(1+t^2)^2+(1-6*t^2-3*(t^2)^2)^2:=by positivity
  have hh:=quadratic_bound hA hL hH hplo hphi
  rw [←identity,←GSup_numerator ht ht1] at hh
  have hden:0<UpperAlgebra.denominator (t^2):=by unfold UpperAlgebra.denominator; positivity
  exact ((mul_le_mul_iff_left₀ hden).mp hh).trans_lt c7_lower_strict

theorem GSup_lt_c7 {t:ℝ} (hl:t7<t) (hr:t≤3/5) : GSup t<c7 := by
  by_cases h:t≤27/50
  · exact GSup_near_lt hl h
  · exact GSup_far_lt (le_of_lt (lt_of_not_ge h)) hr
end Bernoulli.DeSilvaJerison

end
end

end OAI
end

section
-- module Solutions.OAIQW_BernoulliCone.UpperSeam
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE

section
noncomputable section
open Set Filter
open scoped Topology ContDiff Laplacian
namespace Bernoulli.DeSilvaJerison
lemma cap_boundary_slope_lt : capC^2*(capHP (3/4))^2<c7 := by
  have hp := capP_bounds
  have ha := capAmplitude_bounds
  have hs : capP^2≤(3886/10000:ℝ)^2 := by nlinarith [hp.1,hp.2]
  have hq : 0≤3125/768-capAmplitude/6 := by linarith [ha.2]
  have hq1 : (3125/768-capAmplitude/6)^2≤(3125/768-(289237/1000000)/6:ℝ)^2 := by
    nlinarith [ha.1]
  rw [capC_sq,capHP_end]
  have hprod := mul_le_mul (show 1+9/16*capP^2≤1+9/16*(3886/10000:ℝ)^2 by linarith)
    hq1 (sq_nonneg _) (by positivity : (0:ℝ)≤1+9/16*(3886/10000:ℝ)^2)
  nlinarith only [hprod,c7_lower]
lemma smoothCap_boundary_slope_lt {x:Space 7} (hx:Cylindrical.radiusSq axis x≤1)
    (hs:|Cylindrical.axis axis x/CapAlgebra.V (Cylindrical.radiusSq axis x) capB|=3/4) :
    ‖gradient smoothCap x‖^2<c7 := by
  rw [smoothCap_boundary_gradient hx hs]
  exact cap_boundary_slope_lt

end Bernoulli.DeSilvaJerison

end
end

end OAI
end

section
-- module Solutions.OAIQW_BernoulliCone.UpperFamily
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE

section
noncomputable section
open Set Filter
open scoped Topology ContDiff Laplacian
namespace Bernoulli.DeSilvaJerison
lemma outerSigned_cylindrical {x:Space 7} (hq:0<Cylindrical.radiusSq axis x) :
    let r:=Real.sqrt (Cylindrical.radiusSq axis x)
    let s:=Cylindrical.axis axis x/r
    outerSigned x=r*capH s+capAmplitude*((Cylindrical.radiusSq axis x)⁻¹-r)*(1+2*s^2) := by
  dsimp only
  let q:=Cylindrical.radiusSq axis x
  let r:=Real.sqrt q
  let a:=Cylindrical.axis axis x
  have hr:0<r:=Real.sqrt_pos.mpr hq
  have hr2:r^2=q:=Real.sq_sqrt hq.le
  let y:=r⁻¹ • x
  have hy:Cylindrical.radiusSq axis y=1 := by
    rw [Cylindrical.radiusSq_smul]
    change (r⁻¹)^2*q=1
    rw [←hr2]; field_simp
  have hay:Cylindrical.axis axis y=a/r := by rw [Cylindrical.axis_smul]; dsimp [a]; ring
  have he:=outerSigned_at_seam hy
  rw [outerSigned,Zsigned_smul x (inv_pos.mpr hr),KSup_smul hq (inv_pos.mpr hr),hay] at he
  change r⁻¹*Zsigned x+capAmplitude*( (r⁻¹)^(-2:ℤ)*KSup x)=capH (a/r) at he
  norm_num only [zpow_neg,zpow_ofNat,inv_inv] at he
  rw [outerSigned,KSup_cylindrical hq]
  rw [KSup_cylindrical hq] at he
  change Zsigned x+capAmplitude*((q+2*a^2)/q^2)=r*capH (a/r)+capAmplitude*(q⁻¹-r)*(1+2*(a/r)^2)
  change r⁻¹*Zsigned x+capAmplitude*((r⁻¹^2)⁻¹*((q+2*a^2)/q^2))=capH (a/r) at he
  rw [←he,←hr2]
  field_simp
  ring

lemma capH_nonneg_iff (s:ℝ) : 0≤capH s ↔ |s|≤3/4 := by
  constructor
  · intro hs
    by_contra hn
    have hh:=capH_strictAnti (show (3/4:ℝ)∈Ici 0 by norm_num) (abs_nonneg s) (lt_of_not_ge hn)
    rw [capH_end,capH_abs] at hh
    linarith
  · exact capH_nonneg
lemma outer_nonnegative_sector {x:Space 7} (hq:1≤Cylindrical.radiusSq axis x) (hp:0≤outerSigned x) :
    |Cylindrical.axis axis x/Real.sqrt (Cylindrical.radiusSq axis x)|≤3/4 := by
  have hqp:0<Cylindrical.radiusSq axis x:=by linarith
  have hr:1≤Real.sqrt (Cylindrical.radiusSq axis x):= (Real.le_sqrt (by norm_num) hqp.le).mpr (by simpa)
  have hqi:(Cylindrical.radiusSq axis x)⁻¹≤1 := inv_le_one_of_one_le₀ hq
  have hs:capAmplitude*((Cylindrical.radiusSq axis x)⁻¹-Real.sqrt (Cylindrical.radiusSq axis x))*
      (1+2*(Cylindrical.axis axis x/Real.sqrt (Cylindrical.radiusSq axis x))^2)≤0 :=
    mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos capAmplitude_pos.le (by linarith)) (by positivity)
  rw [outerSigned_cylindrical hqp] at hp
  have hh:0≤capH (Cylindrical.axis axis x/Real.sqrt (Cylindrical.radiusSq axis x)) := by
    apply nonneg_of_mul_nonneg_right (show 0≤Real.sqrt (Cylindrical.radiusSq axis x)*capH
      (Cylindrical.axis axis x/Real.sqrt (Cylindrical.radiusSq axis x)) by linarith) (by positivity)
  exact (capH_nonneg_iff _).mp hh
lemma outer_nonnegative_angle {x:Space 7} (hq:1≤Cylindrical.radiusSq axis x) (hp:0≤outerSigned x) : |angle x|≤3/5 := by
  have hqp:0<Cylindrical.radiusSq axis x:=by linarith
  have hx: x≠0:=(radiusSq_pos_data hqp).1
  have hr:0<Real.sqrt (Cylindrical.radiusSq axis x):=Real.sqrt_pos.mpr hqp
  have hh:=outer_nonnegative_sector hq hp
  rw [abs_div,abs_of_pos hr,div_le_iff₀ hr] at hh
  have hsq:=Real.sq_sqrt hqp.le
  have hn:0<‖x‖:=norm_pos_iff.mpr hx
  rw [angle,abs_div,abs_norm,div_le_iff₀ hn]
  rw [Cylindrical.axis,inner_axis] at hh
  have hh2:= (sq_le_sq₀ (abs_nonneg (x 6)) (show 0≤3/4*Real.sqrt (Cylindrical.radiusSq axis x) by positivity)).mpr hh
  rw [mul_pow,sq_abs,hsq] at hh2
  rw [Cylindrical.radiusSq,Cylindrical.axis,inner_axis] at hh2
  nlinarith [sq_abs (x 6)]

lemma upperFamily_continuous (l:ℝ) : Continuous (upperFamily l) := by
  have hc:Continuous (fun x:Space 7=>l⁻¹ • x):=continuous_id.const_smul l⁻¹
  have hg:Continuous (fun x:Space 7=>max (upperSigned (l⁻¹ • x)) 0):=
    (upperSigned_continuous.comp hc).max continuous_const
  exact continuous_const.mul hg
end Bernoulli.DeSilvaJerison

end
end

end OAI
end

section
-- module Solutions.OAIQW_BernoulliCone.PositiveFoliation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE

section
noncomputable section
open Set Filter
open scoped Topology
namespace Bernoulli.Foliation

lemma monotone_positive_part {f:ℝ→ℝ} {a b:ℝ} (hab:a≤b)
    (hc:ContinuousOn f (Icc a b))
    (hd:∀t∈Ico a b, 0<f t → ∃v:ℝ, 0<v ∧ HasDerivWithinAt f v (Ici t) t) :
    max (f a) 0 ≤ max (f b) 0 := by
  rcases hab.eq_or_lt with h|h
  · simp [h]
  · rcases lt_or_ge 0 (f a) with hp|hp
    · exact max_le_max ((strict_increase_above_zero h hc hp hd).le) le_rfl
    · rw [max_eq_right hp]
      exact le_max_right _ _

end Bernoulli.Foliation

end
end

end OAI
end

section
-- module Solutions.OAIQW_BernoulliCone.UpperFoliation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Filter
open scoped Topology ContDiff Laplacian
namespace Bernoulli.DeSilvaJerison

lemma upperFamily_monotone (x:Space 7) : MonotoneOn (fun l=>upperFamily l x) (Ioi 0) := by
  intro a ha b hb hab
  change upperFamily a x ≤ upperFamily b x
  rw [upperFamily_eq_max ha.le,upperFamily_eq_max hb.le]
  exact Foliation.monotone_positive_part hab
    ((upperTrace_continuous x).mono (fun t ht=>ha.trans_le ht.1))
    (fun t ht hp=>upperTrace_right_derivative x (ha.trans_le ht.1) hp)
end Bernoulli.DeSilvaJerison

end
end

end OAI
end

section
-- module Solutions.OAIQW_BernoulliCone.UpperLeaves
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Filter
open scoped Topology
namespace Bernoulli.DeSilvaJerison

lemma U_le_upperFamily (x:Space 7) {l:ℝ} (hl:0<l) : U x≤upperFamily l x := by
  apply le_of_tendsto (upperFamily_tendsto_zero x)
  have hh:∀ᶠ s:ℝ in 𝓝[>] 0,s<l := (gt_mem_nhds hl).filter_mono nhdsWithin_le_nhds
  filter_upwards [hh,self_mem_nhdsWithin] with s hs hp
  exact upperFamily_monotone x hp hl hs.le
lemma upperParameter_spec {x:Space 7} {t:ℝ} (ht:U x<t) :
    0<upperParameter x t ∧ upperFamily (upperParameter x t) x=t := by
  rw [upperParameter,dite_eq_left ht]
  exact (existsUnique_upper_leaf x ht).exists.choose_spec
lemma upperParameter_unique {x:Space 7} {t l:ℝ} (ht:U x<t) (hl:0<l) (he:upperFamily l x=t) :
    upperParameter x t=l := by
  exact ExistsUnique.unique (existsUnique_upper_leaf x ht) (upperParameter_spec ht) ⟨hl,he⟩
lemma upperParameter_lt_iff {x:Space 7} {t l:ℝ} (ht:U x<t) (hl:0<l) :
    upperParameter x t<l ↔ t<upperFamily l x := by
  obtain ⟨hp,he⟩:=upperParameter_spec ht
  constructor
  · intro h
    rw [←he]
    exact upperFamily_strict hp h (by rw [he]; exact (U_nonneg x).trans_lt ht)
  · intro h
    by_contra hn
    have hh:=upperFamily_monotone x hl hp (le_of_not_gt hn)
    dsimp only at hh
    rw [he] at hh
    linarith
lemma lt_upperParameter_iff {x:Space 7} {t l:ℝ} (ht:U x<t) (hl:0<l) :
    l<upperParameter x t ↔ upperFamily l x<t := by
  obtain ⟨hp,he⟩:=upperParameter_spec ht
  constructor
  · intro h
    by_cases hw:0<upperFamily l x
    · rw [←he]; exact upperFamily_strict hl h hw
    · exact (le_of_not_gt hw).trans_lt ((U_nonneg x).trans_lt ht)
  · intro h
    by_contra hn
    have hh:=upperFamily_monotone x hp hl (le_of_not_gt hn)
    dsimp only at hh
    rw [he] at hh
    linarith
end Bernoulli.DeSilvaJerison

end
end

end OAI
end

section
-- module Solutions.OAIQW_BernoulliCone.UpperParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace Bernoulli.DeSilvaJerison

lemma upperParameter_continuousAt {p:Space 7×ℝ} (hp:U p.1<p.2) :
    ContinuousAt (fun z:Space 7×ℝ=>upperParameter z.1 z.2) p := by
  have hdom:∀ᶠ z:Space 7×ℝ in 𝓝 p,U z.1<z.2 :=
    (U_continuous.continuousAt.comp continuous_fst.continuousAt).eventually_lt
      continuous_snd.continuousAt hp
  rw [ContinuousAt,tendsto_order]
  constructor
  · intro a ha
    by_cases hapos:0<a
    · have hat:upperFamily a p.1<p.2:=(lt_upperParameter_iff hp hapos).mp ha
      have hnear:∀ᶠ z:Space 7×ℝ in 𝓝 p,upperFamily a z.1<z.2 :=
        ((upperFamily_continuous a).continuousAt.comp continuous_fst.continuousAt).eventually_lt
          continuous_snd.continuousAt hat
      filter_upwards [hdom,hnear] with z hz hz1
      exact (lt_upperParameter_iff hz hapos).mpr hz1
    · filter_upwards [hdom] with z hz
      exact (le_of_not_gt hapos).trans_lt (upperParameter_spec hz).1
  · intro b hb
    have hbpos:0<b := (upperParameter_spec hp).1.trans hb
    have hbt:p.2<upperFamily b p.1:=(upperParameter_lt_iff hp hbpos).mp hb
    have hnear:∀ᶠ z:Space 7×ℝ in 𝓝 p,z.2<upperFamily b z.1 :=
      continuous_snd.continuousAt.eventually_lt
        ((upperFamily_continuous b).continuousAt.comp continuous_fst.continuousAt) hbt
    filter_upwards [hdom,hnear] with z hz hz1
    exact (upperParameter_lt_iff hz hbpos).mpr hz1
lemma upperParameter_continuousOn : ContinuousOn (fun z:Space 7×ℝ=>upperParameter z.1 z.2)
    {z|U z.1<z.2} := fun _ hp=>(upperParameter_continuousAt hp).continuousWithinAt
end Bernoulli.DeSilvaJerison

end
end

end OAI
end

section
-- module Solutions.OAIQW_BernoulliCone.ScalarImplicit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE

section
noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace Bernoulli.Foliation
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
lemma real_linear_invertible {L:ℝ→L[ℝ] ℝ} (hL:L 1≠0) :L.IsInvertible := by
  have he:∀s:ℝ,L s=s*L 1:=fun s=>by simpa using L.map_smul s (1:ℝ)
  let R:ℝ→L[ℝ] ℝ:=(L 1)⁻¹ • ContinuousLinearMap.id ℝ ℝ
  apply ContinuousLinearMap.IsInvertible.of_inverse (g:=R)
  · apply ContinuousLinearMap.ext
    intro s
    simp only [ContinuousLinearMap.comp_apply,R,smul_apply,
      ContinuousLinearMap.id_apply,smul_eq_mul]
    rw [he]
    field_simp
  · apply ContinuousLinearMap.ext
    intro s
    simp only [ContinuousLinearMap.comp_apply,R,smul_apply,
      ContinuousLinearMap.id_apply,smul_eq_mul]
    rw [he]
    field_simp
    rw [he]
    ring
lemma scalar_implicit {F:E×ℝ→ℝ} {x:E} {l ρ:ℝ}
    (hF:ContDiffAt ℝ ∞ F (x,l)) (hd:HasDerivAt (fun s:ℝ=>F (x,s)) ρ l) (hρ:ρ≠0) :
    ∃ψ:E→ℝ, ContDiffAt ℝ ∞ ψ x ∧ ψ x=l ∧
      ∀ᶠ y in 𝓝 x,F (y,ψ y)=F (x,l) := by
  have hc:HasDerivAt (fun s:ℝ=>F (x,s)) ((fderiv ℝ F (x,l)) (0,1)) l := by
    exact (hF.differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt l
      ((hasDerivAt_const l x).prodMk (hasDerivAt_id l))
  have hl:(fderiv ℝ F (x,l) ∘L ContinuousLinearMap.inr ℝ E ℝ) 1=ρ := by
    simpa using hc.unique hd
  have hi:(fderiv ℝ F (x,l) ∘L ContinuousLinearMap.inr ℝ E ℝ).IsInvertible:=
    real_linear_invertible (by rw [hl]; exact hρ)
  exact ⟨hF.implicitFunction (by simp) hi,hF.contDiffAt_implicitFunction (by simp) hi,
    hF.implicitFunction_apply_self (by simp) hi,hF.eventually_apply_implicitFunction (by simp) hi⟩
/-- The local uniqueness clause of the scalar implicit-function theorem is
needed for a smooth extension up to one side of a genuine seam. -/
lemma scalar_implicit_unique {F:E×ℝ→ℝ} {x:E} {l ρ:ℝ}
    (hF:ContDiffAt ℝ ∞ F (x,l)) (hd:HasDerivAt (fun s:ℝ=>F (x,s)) ρ l) (hρ:ρ≠0) :
    ∃ψ:E→ℝ, ContDiffAt ℝ ∞ ψ x ∧ ψ x=l ∧
      (∀ᶠ y in 𝓝 x,F (y,ψ y)=F (x,l)) ∧
      ∀ᶠ z in 𝓝 (x,l), F z=F (x,l) ↔ ψ z.1=z.2 := by
  have hc:HasDerivAt (fun s:ℝ=>F (x,s)) ((fderiv ℝ F (x,l)) (0,1)) l :=
    (hF.differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt l
      ((hasDerivAt_const l x).prodMk (hasDerivAt_id l))
  have hl:(fderiv ℝ F (x,l) ∘L ContinuousLinearMap.inr ℝ E ℝ) 1=ρ := by
    simpa using hc.unique hd
  have hi:(fderiv ℝ F (x,l) ∘L ContinuousLinearMap.inr ℝ E ℝ).IsInvertible:=
    real_linear_invertible (by rw [hl]; exact hρ)
  exact ⟨hF.implicitFunction (by simp) hi,hF.contDiffAt_implicitFunction (by simp) hi,
    hF.implicitFunction_apply_self (by simp) hi,
    hF.eventually_apply_implicitFunction (by simp) hi,
    hF.eventually_apply_eq_iff_implicitFunction (by simp) hi⟩
end Bernoulli.Foliation

end
end

end OAI
end

section
-- module Solutions.OAIQW_BernoulliCone.UpperSmoothLeaves
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace Bernoulli.DeSilvaJerison

lemma upperSigned_contDiffAt {x:Space 7} (hq:Cylindrical.radiusSq axis x≠1) :
    ContDiffAt ℝ ∞ upperSigned x := by
  have hcont:ContinuousAt (Cylindrical.radiusSq axis) x :=
    (Cylindrical.radiusSq_contDiff axis (n:=1)).continuous.continuousAt
  rcases lt_or_gt_of_ne hq with h|h
  · apply (smoothCap_contDiffAt h.le).congr_of_eventuallyEq
    filter_upwards [hcont.eventually (gt_mem_nhds h)] with y hy
    exact upperSigned_cap hy.le
  · have hqp:0<Cylindrical.radiusSq axis x:=by linarith
    obtain ⟨hx,ha⟩:=radiusSq_pos_data hqp
    apply (outerSigned_contDiffAt hx ha).congr_of_eventuallyEq
    filter_upwards [hcont.eventually (lt_mem_nhds h)] with y hy
    exact upperSigned_outer hy.le
lemma upperFamily_joint_contDiffAt {p:ℝ×Space 7} (hl:0<p.1)
    (hp:0<upperFamily p.1 p.2) (hq:Cylindrical.radiusSq axis (p.1⁻¹ • p.2)≠1) :
    ContDiffAt ℝ ∞ (fun z:ℝ×Space 7=>upperFamily z.1 z.2) p := by
  have hpos:0<upperSigned (p.1⁻¹ • p.2) := by
    have hh:0 < max (upperSigned (p.1⁻¹ • p.2)) 0:=
      pos_of_mul_pos_right hp (mul_nonneg κ_pos.le hl.le)
    simpa using hh
  have hi:ContDiffAt ℝ ∞ (fun z:ℝ×Space 7=>z.1⁻¹ • z.2) p:=
    (contDiffAt_fst.inv hl.ne').smul contDiffAt_snd
  have hs0 : ContDiffAt ℝ ∞ upperSigned (p.1⁻¹ • p.2) :=
    upperSigned_contDiffAt hq
  have hs:ContDiffAt ℝ ∞ (fun z:ℝ×Space 7=>upperSigned (z.1⁻¹ • z.2)) p := by
    exact ContDiffAt.comp (f:=fun z:ℝ×Space 7=>z.1⁻¹ • z.2) (g:=upperSigned) p hs0 hi
  apply ((contDiffAt_const.mul contDiffAt_fst).mul hs).congr_of_eventuallyEq
  filter_upwards [hs.continuousAt.eventually (lt_mem_nhds hpos)] with z hz
  exact congrArg (κ*z.1* ·) (max_eq_left hz.le)
lemma upperFamily_scale_derivative {x:Space 7} {l:ℝ} (hl:0<l)
    (hp:0<upperFamily l x) (hq:Cylindrical.radiusSq axis (l⁻¹ • x)≠1) :
    ∃ρ:ℝ,0<ρ ∧ HasDerivAt (fun s:ℝ=>upperFamily s x) ρ l := by
  let ρ:=κ*(upperSigned (l⁻¹ • x)-inner ℝ (l⁻¹ • x) (gradient upperSigned (l⁻¹ • x)))
  have hd:HasDerivAt (upperTrace x) ρ l := by
    have hh:HasDerivAt (fun s:ℝ=>κ*(s*upperSigned (s⁻¹ • x))) ρ l:=
      (Foliation.hasDerivAt_dilate x hl.ne'
        ((upperSigned_contDiffAt hq).differentiableAt (by simp))).const_mul κ
    change HasDerivAt (fun s=>κ*s*upperSigned (s⁻¹ • x)) ρ l
    simpa only [mul_assoc] using hh
  have hpt:0<upperTrace x l := by rw [upperFamily_eq_max hl.le x] at hp; simpa using hp
  obtain ⟨v,hv,hdv⟩:=upperTrace_right_derivative x hl hpt
  have he:ρ=v:=(uniqueDiffWithinAt_Ici l).eq_deriv (Ici l) hd.hasDerivWithinAt hdv
  refine ⟨ρ,he.symm ▸ hv,?_⟩
  apply hd.congr_of_eventuallyEq
  have hln:∀ᶠ s:ℝ in 𝓝 l,0<s:=lt_mem_nhds hl
  have hpn:∀ᶠ s:ℝ in 𝓝 l,0<upperTrace x s:=hd.continuousAt.eventually (lt_mem_nhds hpt)
  filter_upwards [hln,hpn] with s hs hs1
  rw [upperFamily_eq_max hs.le,max_eq_left hs1.le]
lemma upperParameter_contDiffAt {p:Space 7×ℝ} (hp:U p.1<p.2)
    (hq:Cylindrical.radiusSq axis ((upperParameter p.1 p.2)⁻¹ • p.1)≠1) :
    ContDiffAt ℝ ∞ (fun z:Space 7×ℝ=>upperParameter z.1 z.2) p := by
  let l:=upperParameter p.1 p.2
  have hl:0<l:=(upperParameter_spec hp).1
  have he:upperFamily l p.1=p.2:=(upperParameter_spec hp).2
  have ht:0<p.2:=(U_nonneg p.1).trans_lt hp
  let F:(Space 7×ℝ)×ℝ→ℝ:=fun z=>upperFamily z.2 z.1.1-z.1.2
  have hpl:0<upperFamily l p.1 := by rw [he]; exact ht
  have hUF:ContDiffAt ℝ ∞ (fun z:ℝ×Space 7=>upperFamily z.1 z.2) (l,p.1) :=
    upperFamily_joint_contDiffAt (p:=(l,p.1)) hl hpl hq
  have hF:ContDiffAt ℝ ∞ F (p,l) := by
    have hh:ContDiffAt ℝ ∞ (fun z:(Space 7×ℝ)×ℝ=>(z.2,z.1.1)) (p,l):=by fun_prop
    exact (hUF.comp (p,l) hh).sub
      (contDiffAt_fst.snd)
  obtain ⟨ρ,hρ,hd⟩:=upperFamily_scale_derivative hl hpl hq
  have hdF:HasDerivAt (fun s:ℝ=>F (p,s)) ρ l:=by simpa only [F] using hd.sub_const p.2
  obtain ⟨ψ,hψ,hψ0,hψeq⟩:=Foliation.scalar_implicit hF hdF hρ.ne'
  have hF0:F (p,l)=0:=by dsimp [F]; rw [he,sub_self]
  apply hψ.congr_of_eventuallyEq
  have hψpos:∀ᶠ z in 𝓝 p,0<ψ z:=hψ.continuousAt.eventually (lt_mem_nhds (by rwa [hψ0]))
  have hdom:∀ᶠ z:Space 7×ℝ in 𝓝 p,U z.1<z.2 :=
    (U_continuous.continuousAt.comp continuous_fst.continuousAt).eventually_lt continuous_snd.continuousAt hp
  filter_upwards [hψeq,hψpos,hdom] with z hz hz1 hz2
  rw [hF0] at hz
  exact upperParameter_unique hz2 hz1 (sub_eq_zero.mp hz)
end Bernoulli.DeSilvaJerison

end
end

end OAI
end

section
-- module Solutions.OAIQW_BernoulliCone.FoliationDifferential
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE uG

section
noncomputable section
open Set Filter InnerProductSpace
open scoped Topology ContDiff Laplacian
namespace Bernoulli.Foliation
variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

lemma inner_spatialGradient (F:E×ℝ→ℝ) (p:E×ℝ) (v:E) :
    inner ℝ (spatialGradient F p) v = fderiv ℝ F p (v,0) := by
  rw [spatialGradient,←toDual_apply_apply (𝕜:=ℝ),LinearIsometryEquiv.apply_symm_apply]
  rfl

omit [FiniteDimensional ℝ E] in
lemma sliceLeft_hasFDerivAt {G : Type uG} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {F:E×ℝ→G} {p:E×ℝ} (hF:DifferentiableAt ℝ F p) :
    HasFDerivAt (fun x:E=>F (x,p.2)) (fderiv ℝ F p ∘L ContinuousLinearMap.inl ℝ E ℝ) p.1 := by
  rcases p with ⟨x,t⟩
  have hi:HasFDerivAt (fun y:E=>(y,t)) (ContinuousLinearMap.inl ℝ E ℝ) x := by
    simpa only [ContinuousLinearMap.inl,id_eq] using (hasFDerivAt_id (𝕜:=ℝ) x).prodMk (hasFDerivAt_const t x)
  exact hF.hasFDerivAt.comp x hi

lemma spatialGradient_eq {F:E×ℝ→ℝ} {p:E×ℝ} (hF:DifferentiableAt ℝ F p) :
    spatialGradient F p=gradient (fun x:E=>F (x,p.2)) p.1 := by
  apply ext_inner_right ℝ
  intro v
  rw [inner_spatialGradient,inner_gradient_left]
  have hd := sliceLeft_hasFDerivAt hF
  rw [hd.fderiv]
  simp

lemma spatialGradient_contDiffAt {F:E×ℝ→ℝ} {p:E×ℝ} (hF:ContDiffAt ℝ ∞ F p) :
    ContDiffAt ℝ ∞ (spatialGradient F) p := by
  have hpart : ContDiffAt ℝ ∞ (fun q:E×ℝ=>fderiv ℝ F q ∘L ContinuousLinearMap.inl ℝ E ℝ) p :=
    (hF.fderiv_right (by simp)).clm_comp contDiffAt_const
  exact (toDual ℝ E).symm.toContinuousLinearEquiv.contDiff.contDiffAt.comp p hpart

end Bernoulli.Foliation

end
end

end OAI
end

section
-- module Solutions.OAIQW_BernoulliCone.UpperCalibration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Filter InnerProductSpace
open scoped Topology ContDiff Laplacian
namespace Bernoulli.DeSilvaJerison

lemma upperFamily_contDiffAt_swap {x:Space 7} {l:ℝ} (hl:0<l)
    (hp:0<upperFamily l x) (hq:Cylindrical.radiusSq axis (l⁻¹ • x)≠1) :
    ContDiffAt ℝ ∞ (fun z:Space 7×ℝ=>upperFamily z.2 z.1) (x,l) := by
  have hh:ContDiffAt ℝ ∞ (fun z:ℝ×Space 7=>upperFamily z.1 z.2) (l,x):=
    upperFamily_joint_contDiffAt (p:=(l,x)) hl hp hq
  have hi:ContDiffAt ℝ ∞ (fun z:Space 7×ℝ=>(z.2,z.1)) (x,l):=
    contDiffAt_snd.prodMk contDiffAt_fst
  exact ContDiffAt.comp (f:=fun z:Space 7×ℝ=>(z.2,z.1)) (x,l) hh hi

lemma upperCalibration_contDiffAt {p:Space 7×ℝ} (hp:U p.1<p.2)
    (hq:Cylindrical.radiusSq axis ((upperParameter p.1 p.2)⁻¹ • p.1)≠1) :
    ContDiffAt ℝ ∞ upperCalibration p := by
  obtain ⟨hl,he⟩:=upperParameter_spec hp
  have hF:ContDiffAt ℝ ∞ (fun z:Space 7×ℝ=>upperFamily z.2 z.1)
      (p.1,upperParameter p.1 p.2):=by
    exact upperFamily_contDiffAt_swap hl (by rw [he]; exact (U_nonneg _).trans_lt hp) hq
  exact (Foliation.spatialGradient_contDiffAt hF).comp p
    (contDiffAt_fst.prodMk (upperParameter_contDiffAt hp hq))

end Bernoulli.DeSilvaJerison

end
end

end OAI
end

section
-- module Solutions.OAIQW_BernoulliCone.OuterSlope
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Filter
open scoped Topology ContDiff Laplacian
namespace Bernoulli.DeSilvaJerison
open Axisymmetric
lemma Zsigned_gradient {x:Space 7} (hx:x≠0) (ha:|angle x|<1) :
    gradient Zsigned x=polarGradient axis x (f (angle x)) (fp (angle x)) := by
  have hi:inner ℝ x axis/‖x‖∈Ioo (-1:ℝ) 1:=by
    simpa only [inner_axis,angle] using (show angle x∈Ioo (-1:ℝ) 1 from abs_lt.mp ha)
  rw [Zsigned,(hasGradientAt_lift axis x 1 hx (hasDerivAt_f hi)).gradient]
  simp only [Real.rpow_one,div_self (norm_ne_zero_iff.mpr hx),one_smul,one_mul,inner_axis,angle]
lemma outerSigned_gradient {x:Space 7} (hx:x≠0) (ha:|angle x|<1) :
    gradient outerSigned x=polarGradient axis x (f (angle x)) (fp (angle x))+
      (capAmplitude*(‖x‖^(-2:ℝ)/‖x‖)) • polarGradient axis x (-2*gSup (angle x)) (gSup1 (angle x)) := by
  have hdz: DifferentiableAt ℝ Zsigned x := (signed_contDiffAt (n:=1) hx ha).differentiableAt (by norm_num)
  have hdk: DifferentiableAt ℝ KSup x := (KSup_contDiffAt (n:=1) hx ha).differentiableAt (by norm_num)
  change gradient (fun x=>Zsigned x+capAmplitude*KSup x) x=_
  rw [gradient_add' hdz (hdk.const_mul capAmplitude),gradient_const_mul _ hdk,
    Zsigned_gradient hx ha,KSup_gradient hx ha,smul_smul]
lemma outer_zero_coefficient {x:Space 7} (hq:0<Cylindrical.radiusSq axis x) (hz:outerSigned x=0) :
    capAmplitude*(‖x‖^(-2:ℝ)/‖x‖)= -f (angle x)/gSup (angle x) := by
  obtain ⟨hx,ha⟩:=radiusSq_pos_data hq
  have hn:‖x‖≠0:=norm_ne_zero_iff.mpr hx
  have hg:(gSup (angle x))≠0:=(gSup_pos ha).ne'
  rw [outerSigned,Zsigned_eq,KSup,lift,inner_axis] at hz
  change ‖x‖*f (angle x)+capAmplitude*(‖x‖^(-2:ℝ)*gSup (angle x))=0 at hz
  field_simp
  linarith
lemma GSup_even (t:ℝ) : GSup (-t)=GSup t := by
  simp only [GSup,f_neg,fp_neg_arg,qSup,neg_sq]
  ring
lemma GSup_abs (t:ℝ) : GSup |t|=GSup t := by
  rcases le_total 0 t with h|h
  · rw [abs_of_nonneg h]
  · rw [abs_of_nonpos h,GSup_even]
lemma outer_zero_slope {x:Space 7} (hq:0<Cylindrical.radiusSq axis x) (hz:outerSigned x=0) :
    ‖gradient outerSigned x‖^2=GSup (angle x) := by
  obtain ⟨hx,ha⟩:=radiusSq_pos_data hq
  have hg:(gSup (angle x))≠0:=(gSup_pos ha).ne'
  have he:gradient outerSigned x=polarGradient axis x (3*f (angle x))
      (fp (angle x)-f (angle x)*qSup (angle x)) := by
    rw [outerSigned_gradient hx ha,outer_zero_coefficient hq hz,qSup_eq ha]
    apply ext_inner_right ℝ
    intro v
    simp only [polarGradient,inner_add_left,inner_sub_left,real_inner_smul_left]
    field_simp
    ring
  rw [he,norm_sq_polarGradient axis_norm hx]
  simp only [inner_axis,GSup,angle]
  ring
lemma outer_zero_angle {x:Space 7} (hq:1≤Cylindrical.radiusSq axis x) (hz:outerSigned x=0) :
    t7 < |angle x| ∧ |angle x|≤3/5 := by
  have hqp:0<Cylindrical.radiusSq axis x:=by linarith
  obtain ⟨hx,ha⟩:=radiusSq_pos_data hqp
  refine ⟨?_,outer_nonnegative_angle hq (le_of_eq hz.symm)⟩
  have hk:=mul_pos capAmplitude_pos (KSup_pos hx ha)
  have hf:f (angle x)<0 := by
    rw [outerSigned,Zsigned_eq] at hz
    have hr:0<‖x‖:=norm_pos_iff.mpr hx
    nlinarith
  by_contra hh
  have he:p (angle x)=f (angle x):=p_eq_f (not_lt.mp hh)
  have hp:=p_nonneg (angle x)
  rw [he] at hp
  linarith
/-- Strict free-boundary slope for the actual exterior function, not just its
one-variable numerical certificate. -/
theorem outer_zero_slope_lt {x:Space 7} (hq:1≤Cylindrical.radiusSq axis x) (hz:outerSigned x=0) :
    ‖gradient outerSigned x‖^2<c7 := by
  rw [outer_zero_slope (by linarith) hz,←GSup_abs]
  exact GSup_lt_c7 (outer_zero_angle hq hz).1 (outer_zero_angle hq hz).2
end Bernoulli.DeSilvaJerison

end
end

end OAI
end

section
-- module Solutions.OAIQW_BernoulliCone.CalibrationTraces
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Filter InnerProductSpace
open scoped Topology ContDiff Laplacian
namespace Bernoulli.DeSilvaJerison
lemma gradient_dilation {f:Space 7→ℝ} {x:Space 7} {l:ℝ} (hl:l≠0)
    (hf:DifferentiableAt ℝ f (l⁻¹ • x)) :
    gradient (fun y=>κ*l*f (l⁻¹ • y)) x=κ • gradient f (l⁻¹ • x) := by
  have hd:HasFDerivAt (fun y:Space 7=>l⁻¹ • y)
      (l⁻¹ • ContinuousLinearMap.id ℝ (Space 7)) x := (hasFDerivAt_id x).const_smul l⁻¹
  have hh:HasFDerivAt (fun y:Space 7=>κ*l*f (l⁻¹ • y))
      ((κ*l) • (fderiv ℝ f (l⁻¹ • x) ∘L (l⁻¹ • ContinuousLinearMap.id ℝ (Space 7)))) x :=
    (hf.hasFDerivAt.comp x hd).const_mul (κ*l)
  apply ext_inner_right ℝ
  intro v
  rw [inner_gradient_left,hh.fderiv,real_inner_smul_left,inner_gradient_left]
  simp only [smul_apply,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply,map_smul,smul_eq_mul]
  field_simp

lemma upperFamily_gradient {x:Space 7} {l:ℝ} (hl:0<l)
    (hp:0<upperFamily l x) (hq:Cylindrical.radiusSq axis (l⁻¹ • x)≠1) :
    gradient (upperFamily l) x=κ • gradient upperSigned (l⁻¹ • x) := by
  have hf:ContDiffAt ℝ ∞ upperSigned (l⁻¹ • x):=upperSigned_contDiffAt hq
  have hs:ContinuousAt (fun y:Space 7=>upperSigned (l⁻¹ • y)) x:=
    hf.continuousAt.comp ((continuous_id.const_smul l⁻¹).continuousAt)
  have hpos:0<upperSigned (l⁻¹ • x):=by
    have hh:0 < max (upperSigned (l⁻¹ • x)) 0:=pos_of_mul_pos_right hp (mul_nonneg κ_pos.le hl.le)
    simpa using hh
  have he:upperFamily l =ᶠ[𝓝 x] (fun y=>κ*l*upperSigned (l⁻¹ • y)) := by
    filter_upwards [hs.eventually (lt_mem_nhds hpos)] with y hy
    exact congrArg (κ*l* ·) (max_eq_left hy.le)
  rw [gradient,he.fderiv_eq]
  exact gradient_dilation hl.ne' (hf.differentiableAt (by simp))

lemma upperCalibration_eq {p:Space 7×ℝ} (hp:U p.1<p.2)
    (hq:Cylindrical.radiusSq axis ((upperParameter p.1 p.2)⁻¹ • p.1)≠1) :
    upperCalibration p=κ • gradient upperSigned ((upperParameter p.1 p.2)⁻¹ • p.1) := by
  obtain ⟨hl,he⟩:=upperParameter_spec hp
  have hpos:0<upperFamily (upperParameter p.1 p.2) p.1:=by rw [he]; exact (U_nonneg _).trans_lt hp
  rw [upperCalibration,Foliation.spatialGradient_eq
    ((upperFamily_contDiffAt_swap hl hpos hq).differentiableAt (by simp))]
  exact upperFamily_gradient hl hpos hq

lemma capH_eq_zero_iff (s:ℝ) : capH s=0 ↔ |s|=3/4 := by
  constructor
  · intro hs
    have h1:(|s|≤3/4):=(capH_nonneg_iff s).mp (le_of_eq hs.symm)
    have h2:¬|s|<3/4:=by intro h; have hp:=(capH_pos_iff s).mpr h; rw [hs] at hp; exact lt_irrefl _ hp
    exact le_antisymm h1 (not_lt.mp h2)
  · intro hs
    have h1:0≤capH s:=(capH_nonneg_iff s).mpr hs.le
    have h2:¬0<capH s:=by intro h; have hp:=(capH_pos_iff s).mp h; rw [hs] at hp; exact lt_irrefl _ hp
    exact le_antisymm (not_lt.mp h2) h1

lemma smoothCap_zero_slope {x:Space 7} (hq:Cylindrical.radiusSq axis x≤1)
    (hz:smoothCap x=0) : ‖gradient smoothCap x‖^2<c7 := by
  have hq0:=Cylindrical.radiusSq_nonneg axis x axis_norm
  have hv:0<CapAlgebra.V (Cylindrical.radiusSq axis x) capB:=
    (CapAlgebra.V_bounds hq0 hq capB_bounds.1 capB_bounds.2).1
  have hY:0<CapAlgebra.Y (Cylindrical.radiusSq axis x) capB capC:=
    CapAlgebra.Y_pos hq0 hv capC_pos
  have hh:capH (Cylindrical.axis axis x/CapAlgebra.V (Cylindrical.radiusSq axis x) capB)=0 := by
    change CapAlgebra.Y _ _ _ * capH (_ * (CapAlgebra.V _ _)⁻¹)=0 at hz
    simpa only [div_eq_mul_inv] using (mul_eq_zero.mp hz).resolve_left hY.ne'
  exact smoothCap_boundary_slope_lt hq ((capH_eq_zero_iff _).mp hh)

lemma normalized_slope_lt {G:Space 7} (hG:‖G‖^2<c7) : ‖κ • G‖^2<1 := by
  rw [norm_smul,Real.norm_eq_abs,mul_pow,sq_abs,←κ_sq]
  exact mul_lt_mul_of_pos_left hG (sq_pos_of_pos κ_pos)

theorem upper_free_boundary_slopes {x:Space 7} (hz:upperSigned x=0) :
    (Cylindrical.radiusSq axis x≤1 → ‖κ • gradient smoothCap x‖^2<1) ∧
    (1≤Cylindrical.radiusSq axis x → ‖κ • gradient outerSigned x‖^2<1) := by
  constructor
  · intro hq
    exact normalized_slope_lt (smoothCap_zero_slope hq (by rwa [upperSigned_cap hq] at hz))
  · intro hq
    exact normalized_slope_lt (outer_zero_slope_lt hq (by rwa [upperSigned_outer hq] at hz))
end Bernoulli.DeSilvaJerison

end
end

end OAI
end

section
-- module Solutions.OAIQW_BernoulliCone.FluxBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Filter InnerProductSpace
open scoped Topology ContDiff
namespace Bernoulli.DeSilvaJerison
open Axisymmetric
lemma cap_positive_bounded {x:Space 7} (hq:Cylindrical.radiusSq axis x≤1)
    (hp:0<smoothCap x) : ‖x‖≤2 := by
  have hq0:=Cylindrical.radiusSq_nonneg axis x axis_norm
  obtain ⟨hv,hv1⟩:=CapAlgebra.V_bounds hq0 hq capB_bounds.1 capB_bounds.2
  have hy:=CapAlgebra.Y_pos hq0 hv capC_pos
  have hH:0<capH (Cylindrical.axis axis x/CapAlgebra.V (Cylindrical.radiusSq axis x) capB):=by
    change 0<CapAlgebra.Y _ _ _ * capH (_ * (CapAlgebra.V _ _)⁻¹) at hp
    rw [←div_eq_mul_inv] at hp
    exact pos_of_mul_pos_right hp hy.le
  have ha:|Cylindrical.axis axis x|<3/4:=by
    have hh:=(capH_pos_iff _).mp hH
    rw [abs_div,abs_of_pos hv,div_lt_iff₀ hv] at hh
    nlinarith
  have hsq:(Cylindrical.axis axis x)^2<(3/4:ℝ)^2:=by
    rw [←sq_abs]
    exact (sq_lt_sq₀ (abs_nonneg _) (by norm_num)).mpr ha
  unfold Cylindrical.radiusSq at hq
  nlinarith [norm_nonneg x]
lemma cap_gradient_uniform_bound : ∃C:ℝ,0<C ∧
    ∀x:Space 7,Cylindrical.radiusSq axis x≤1 → 0<smoothCap x → ‖gradient smoothCap x‖≤C := by
  let S:Set (Space 7):={x|Cylindrical.radiusSq axis x≤1} ∩ Metric.closedBall 0 2
  have hs:IsCompact S:=(isCompact_closedBall (0:Space 7) 2).inter_left
    (isClosed_le (Cylindrical.radiusSq_contDiff axis (n:=1)).continuous continuous_const)
  have hg:ContinuousOn (gradient smoothCap) S:=by
    intro x hx
    have hh:ContDiffAt ℝ ∞ (gradient smoothCap) x:=
      (toDual ℝ (Space 7)).symm.toContinuousLinearEquiv.contDiff.contDiffAt.comp x
        ((smoothCap_contDiffAt hx.1).fderiv_right (by simp))
    exact hh.continuousAt.continuousWithinAt
  obtain ⟨C,hC⟩:=hs.exists_bound_of_continuousOn hg
  refine ⟨|C|+1,by positivity,?_⟩
  intro x hq hp
  have hx:x∈S:=⟨hq,by simpa using cap_positive_bounded hq hp⟩
  exact (hC x hx).trans (by linarith [le_abs_self C])
lemma polarGradient_norm_bound {x:Space 7} (hx:x≠0) (a b:ℝ) :
    ‖polarGradient axis x a b‖≤|a|+|b| := by
  have hh:=norm_sq_polarGradient axis_norm hx a b
  have hab:0≤|a| * |b|:=mul_nonneg (abs_nonneg _) (abs_nonneg _)
  have hb:0≤(inner ℝ x axis/‖x‖)^2*b^2:=mul_nonneg (sq_nonneg _) (sq_nonneg _)
  nlinarith [sq_abs a,sq_abs b,norm_nonneg (polarGradient axis x a b),abs_nonneg a,abs_nonneg b]
lemma outer_gradient_uniform_bound : ∃C:ℝ,0<C ∧
    ∀x:Space 7,1≤Cylindrical.radiusSq axis x → 0<outerSigned x → ‖gradient outerSigned x‖≤C := by
  let R:ℝ→ℝ:=fun t=>|f t|+|fp t|+capAmplitude*(2*|gSup t|+|gSup1 t|)
  have hR:ContinuousOn R (Icc (-3/5:ℝ) (3/5)):=by
    intro t ht
    have ht1:t∈Ioo (-1:ℝ) 1:=⟨by linarith [ht.1],by linarith [ht.2]⟩
    have ht2:|t|<1:=abs_lt.mpr ht1
    exact (((hasDerivAt_f ht1).continuousAt.abs.add (hasDerivAt_fp ht1).continuousAt.abs).add
      (continuousAt_const.mul (((hasDerivAt_gSup ht2).continuousAt.abs.const_mul 2).add
        (hasDerivAt_gSup1 ht2).continuousAt.abs))).continuousWithinAt
  obtain ⟨C,hC⟩:=isCompact_Icc.exists_bound_of_continuousOn hR
  refine ⟨|C|+1,by positivity,?_⟩
  intro x hq hp
  obtain ⟨hx,ha⟩:=radiusSq_pos_data (show 0<Cylindrical.radiusSq axis x by linarith)
  have hat:|angle x|≤3/5:=outer_nonnegative_angle hq hp.le
  have hn:1≤‖x‖:=by
    unfold Cylindrical.radiusSq at hq
    nlinarith [norm_nonneg x,sq_nonneg (Cylindrical.axis axis x)]
  have hn0:0<‖x‖:=by linarith
  have hfac:0≤‖x‖^(-2:ℝ)/‖x‖ ∧ ‖x‖^(-2:ℝ)/‖x‖≤1:=by
    rw [Real.rpow_neg (norm_nonneg x),Real.rpow_two]
    constructor
    · positivity
    · apply (div_le_one hn0).mpr
      exact (inv_le_one_of_one_le₀ (by nlinarith : 1≤‖x‖^2)).trans hn
  have hc:0≤capAmplitude*(‖x‖^(-2:ℝ)/‖x‖):=mul_nonneg capAmplitude_pos.le hfac.1
  have hc1:capAmplitude*(‖x‖^(-2:ℝ)/‖x‖)≤capAmplitude:=by nlinarith [capAmplitude_pos]
  have hm:‖gradient outerSigned x‖≤R (angle x):=by
    rw [outerSigned_gradient hx ha]
    calc
      _≤‖polarGradient axis x (f (angle x)) (fp (angle x))‖+
          ‖(capAmplitude*(‖x‖^(-2:ℝ)/‖x‖)) • polarGradient axis x (-2*gSup (angle x)) (gSup1 (angle x))‖ := norm_add_le _ _
      _≤(|f (angle x)|+|fp (angle x)|)+
          capAmplitude*(2*|gSup (angle x)|+|gSup1 (angle x)|) := by
        rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hc]
        apply add_le_add (polarGradient_norm_bound hx _ _)
        have hh:=polarGradient_norm_bound hx (-2*gSup (angle x)) (gSup1 (angle x))
        norm_num only [abs_mul,abs_neg,abs_of_pos (by norm_num : 0<(2:ℝ))] at hh
        exact (mul_le_mul_of_nonneg_left hh hc).trans
          (mul_le_mul_of_nonneg_right hc1 (show 0≤2*|gSup (angle x)|+|gSup1 (angle x)| by positivity))
      _=R (angle x):=rfl
  have hbound:‖R (angle x)‖≤C:=hC _ (by simpa only [neg_div,Set.mem_Icc] using abs_le.mp hat)
  exact hm.trans ((le_abs_self _).trans (hbound.trans (by linarith [le_abs_self C])))
end Bernoulli.DeSilvaJerison

end
end

end OAI
end

section
-- module Solutions.OAIQW_BernoulliCone.ExteriorCalibration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Filter InnerProductSpace
open scoped Topology ContDiff
namespace Bernoulli.DeSilvaJerison
lemma upperFamily_outer_gradient {x:Space 7} {l:ℝ} (hl:0<l)
    (hq:l^2<Cylindrical.radiusSq axis x) (hp:0<upperFamily l x) :
    gradient (upperFamily l) x=κ • gradient Zsigned x+
      (κ*capAmplitude*l^3) • gradient KSup x := by
  have hqp:0<Cylindrical.radiusSq axis x:=(sq_pos_of_pos hl).trans hq
  obtain ⟨hx,ha⟩:=radiusSq_pos_data hqp
  have hdZ:DifferentiableAt ℝ Zsigned x:=(signed_contDiffAt (n:=1) hx ha).differentiableAt (by norm_num)
  have hdK:DifferentiableAt ℝ KSup x:=(KSup_contDiffAt (n:=1) hx ha).differentiableAt (by norm_num)
  have he:upperFamily l =ᶠ[𝓝 x] (fun y=>κ*(Zsigned y+capAmplitude*l^3*KSup y)) := by
    filter_upwards [((Cylindrical.radiusSq_contDiff axis (n:=1)).continuous.continuousAt).eventually (lt_mem_nhds hq),
      (upperFamily_continuous l).continuousAt.eventually (lt_mem_nhds hp)] with y hy hpy
    rw [upperFamily_outer_formula hl hy.le] at hpy ⊢
    have hh:0<Zsigned y+capAmplitude*l^3*KSup y:=by
      have hm:=pos_of_mul_pos_right hpy κ_pos.le
      simpa using hm
    rw [max_eq_left hh.le]
  rw [gradient,he.fderiv_eq]
  change gradient (fun y=>κ*(Zsigned y+capAmplitude*l^3*KSup y)) x=_
  have hdf:DifferentiableAt ℝ (fun y=>Zsigned y+capAmplitude*l^3*KSup y) x:=
    hdZ.add (hdK.const_mul (capAmplitude*l^3))
  rw [gradient_const_mul κ hdf,
    gradient_add' hdZ (hdK.const_mul (capAmplitude*l^3)),gradient_const_mul (capAmplitude*l^3) hdK,smul_add,smul_smul]
  congr 2
  ring

/-- On the actual exterior branch the inverse leaf parameter cancels completely.
The calibration extends affinely to the lower graph; there is no cube-root
singularity in the field itself. -/
theorem upperCalibration_outer_affine {p:Space 7×ℝ} (hp:U p.1<p.2)
    (hq:(upperParameter p.1 p.2)^2<Cylindrical.radiusSq axis p.1) :
    upperCalibration p=κ • gradient Zsigned p.1+
      ((p.2-κ*Zsigned p.1)/KSup p.1) • gradient KSup p.1 := by
  let l:=upperParameter p.1 p.2
  obtain ⟨hl,he⟩:=upperParameter_spec hp
  change 0<l at hl
  change upperFamily l p.1=p.2 at he
  have ht:0<p.2:=(U_nonneg _).trans_lt hp
  have hpos:0<upperFamily l p.1:=by rw [he]; exact ht
  have hqp:0<Cylindrical.radiusSq axis p.1:=(sq_pos_of_pos hl).trans hq
  obtain ⟨hx,ha⟩:=radiusSq_pos_data hqp
  have hK:KSup p.1≠0:=(KSup_pos hx ha).ne'
  have hqe:Cylindrical.radiusSq axis (l⁻¹ • p.1)≠1:=by
    rw [Cylindrical.radiusSq_smul]
    have hh:(l⁻¹)^2*Cylindrical.radiusSq axis p.1>1:=by
      rw [inv_pow,←div_eq_inv_mul]
      change 1<Cylindrical.radiusSq axis p.1/l^2
      exact (lt_div_iff₀ (sq_pos_of_pos hl)).mpr (by simpa only [one_mul] using hq)
    exact ne_of_gt hh
  rw [upperCalibration,Foliation.spatialGradient_eq
    ((upperFamily_contDiffAt_swap hl hpos hqe).differentiableAt (by simp)),
    upperFamily_outer_gradient hl hq hpos]
  congr 1
  have hh:=upperFamily_outer_formula hl hq.le
  rw [he] at hh
  have hsg:0<Zsigned p.1+capAmplitude*l^3*KSup p.1:=by
    have hm:0 < max (Zsigned p.1+capAmplitude*l^3*KSup p.1) 0:=by
      exact pos_of_mul_pos_right (hh ▸ ht) κ_pos.le
    simpa using hm
  rw [max_eq_left hsg.le] at hh
  apply congrArg (fun a:ℝ=>a • gradient KSup p.1)
  apply (eq_div_iff hK).mpr
  nlinarith [hh]
end Bernoulli.DeSilvaJerison

end
end

end OAI
end

section
-- module Solutions.OAIQW_BernoulliCone.BoundedCalibration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Filter InnerProductSpace
open scoped Topology ContDiff
namespace Bernoulli.DeSilvaJerison

lemma upperParameter_signed_pos {p:Space 7×ℝ} (hp:U p.1<p.2) :
    0<upperSigned ((upperParameter p.1 p.2)⁻¹ • p.1) := by
  obtain ⟨hl,he⟩:=upperParameter_spec hp
  have hpos:0<upperFamily (upperParameter p.1 p.2) p.1:=by
    rw [he]; exact (U_nonneg _).trans_lt hp
  have hh:0 < max (upperSigned ((upperParameter p.1 p.2)⁻¹ • p.1)) 0:=
    pos_of_mul_pos_right hpos (mul_nonneg κ_pos.le hl.le)
  simpa using hh
lemma upperFlux_uniform_bound : ∃C:ℝ,0<C ∧ ∀p:Space 7×ℝ,‖upperFlux p‖≤C := by
  obtain ⟨C,hC,hcap⟩:=cap_gradient_uniform_bound
  obtain ⟨D,hD,hext⟩:=outer_gradient_uniform_bound
  refine ⟨κ*(C+D),mul_pos κ_pos (add_pos hC hD),?_⟩
  intro p
  by_cases hp:U p.1<p.2
  · have hpos:=upperParameter_signed_pos hp
    rw [upperFlux,ite_eq_left hp,norm_smul,Real.norm_eq_abs,abs_of_pos κ_pos]
    apply mul_le_mul_of_nonneg_left _ κ_pos.le
    split_ifs with hq
    · rw [upperSigned_cap hq] at hpos
      exact (hcap _ hq hpos).trans (by linarith)
    · have hq':1≤Cylindrical.radiusSq axis ((upperParameter p.1 p.2)⁻¹ • p.1):=
        (lt_of_not_ge hq).le
      rw [upperSigned_outer hq'] at hpos
      exact (hext _ hq' hpos).trans (by linarith)
  · simp only [upperFlux,ite_eq_right hp,norm_zero]
    exact mul_nonneg κ_pos.le (by linarith)
lemma upperSigned_gradient_cap {x:Space 7} (hq:Cylindrical.radiusSq axis x<1) :
    gradient upperSigned x=gradient smoothCap x := by
  have hc:ContinuousAt (Cylindrical.radiusSq axis) x:=
    (Cylindrical.radiusSq_contDiff axis (n:=1)).continuous.continuousAt
  have he:upperSigned =ᶠ[𝓝 x] smoothCap:=by
    filter_upwards [hc.eventually (gt_mem_nhds hq)] with y hy
    exact upperSigned_cap hy.le
  exact congrArg ((toDual ℝ (Space 7)).symm) he.fderiv_eq
lemma upperSigned_gradient_outer {x:Space 7} (hq:1<Cylindrical.radiusSq axis x) :
    gradient upperSigned x=gradient outerSigned x := by
  have hc:ContinuousAt (Cylindrical.radiusSq axis) x:=
    (Cylindrical.radiusSq_contDiff axis (n:=1)).continuous.continuousAt
  have he:upperSigned =ᶠ[𝓝 x] outerSigned:=by
    filter_upwards [hc.eventually (lt_mem_nhds hq)] with y hy
    exact upperSigned_outer hy.le
  exact congrArg ((toDual ℝ (Space 7)).symm) he.fderiv_eq
lemma upperFlux_eq_calibration {p:Space 7×ℝ} (hp:U p.1<p.2)
    (hq:Cylindrical.radiusSq axis ((upperParameter p.1 p.2)⁻¹ • p.1)≠1) :
    upperFlux p=upperCalibration p := by
  rw [upperCalibration_eq hp hq,upperFlux,ite_eq_left hp]
  congr 1
  rcases lt_or_gt_of_ne hq with h|h
  · rw [ite_eq_left h.le,upperSigned_gradient_cap h]
  · rw [ite_eq_right (not_le.mpr h),upperSigned_gradient_outer h]
lemma upperFlux_eventually_eq {p:Space 7×ℝ} (hp:U p.1<p.2)
    (hq:Cylindrical.radiusSq axis ((upperParameter p.1 p.2)⁻¹ • p.1)≠1) :
    upperFlux =ᶠ[𝓝 p] upperCalibration := by
  have hn:∀ᶠ z:Space 7×ℝ in 𝓝 p,U z.1<z.2:=
    (U_continuous.continuousAt.comp continuous_fst.continuousAt).eventually_lt
      continuous_snd.continuousAt hp
  have hl:upperParameter p.1 p.2≠0:=(upperParameter_spec hp).1.ne'
  have hc:ContinuousAt (fun z:Space 7×ℝ=>
      Cylindrical.radiusSq axis ((upperParameter z.1 z.2)⁻¹ • z.1)) p:=
    (Cylindrical.radiusSq_contDiff axis (n:=1)).continuous.continuousAt.comp
      (((upperParameter_contDiffAt hp hq).continuousAt.inv₀ hl).smul continuous_fst.continuousAt)
  filter_upwards [hn,hc.eventually_ne hq] with z hz hzq
  exact upperFlux_eq_calibration hz hzq
lemma upperFlux_contDiffAt {p:Space 7×ℝ} (hp:U p.1<p.2)
    (hq:Cylindrical.radiusSq axis ((upperParameter p.1 p.2)⁻¹ • p.1)≠1) :
    ContDiffAt ℝ ∞ upperFlux p :=
  (upperCalibration_contDiffAt hp hq).congr_of_eventuallyEq (upperFlux_eventually_eq hp hq)
lemma upperParameter_measurable : Measurable (fun z:Space 7×ℝ=>upperParameter z.1 z.2) := by
  let S:Set (Space 7×ℝ):={z|U z.1<z.2}
  have hS:IsOpen S:=isOpen_lt (U_continuous.comp continuous_fst) continuous_snd
  have hh:Measurable (S.piecewise (fun z=>upperParameter z.1 z.2) (fun _=>0)):=
    upperParameter_continuousOn.measurable_piecewise continuousOn_const hS.measurableSet
  convert hh using 1
  ext z
  by_cases hz:U z.1<z.2
  · simp [S,hz]
  · simp [S,hz,upperParameter]
lemma upperFlux_measurable : Measurable upperFlux := by
  have hi:Measurable (fun z:Space 7×ℝ=>(upperParameter z.1 z.2)⁻¹ • z.1):=
    upperParameter_measurable.inv.smul measurable_fst
  have hq:Measurable (fun z:Space 7×ℝ=>Cylindrical.radiusSq axis ((upperParameter z.1 z.2)⁻¹ • z.1)):=
    (Cylindrical.radiusSq_contDiff axis (n:=1)).continuous.measurable.comp hi
  have h1:MeasurableSet {z:Space 7×ℝ|U z.1<z.2}:=
    measurableSet_lt (U_continuous.measurable.comp measurable_fst) measurable_snd
  have h2:MeasurableSet {z:Space 7×ℝ|Cylindrical.radiusSq axis ((upperParameter z.1 z.2)⁻¹ • z.1)≤1}:=
    measurableSet_le hq measurable_const
  exact ((LipschitzSobolev.measurable_gradient.comp hi).ite h2
    (LipschitzSobolev.measurable_gradient.comp hi)).const_smul κ |>.ite h1 measurable_const

/-- The height primitive is integrable and has linear growth, using the actual
field's uniform bound, independently of seam choices. -/
lemma upperFlux_intervalIntegrable (x:Space 7) (a b:ℝ) :
    IntervalIntegrable (fun s:ℝ=>upperFlux (x,s)) MeasureTheory.volume a b := by
  obtain ⟨C,hC,hbound⟩:=upperFlux_uniform_bound
  rw [intervalIntegrable_iff]
  apply MeasureTheory.Integrable.mono' (g:=fun _:ℝ=>C)
    (intervalIntegrable_const (a:=a) (b:=b) (c:=C)).def'
  · exact (upperFlux_measurable.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun s=>hbound (x,s)
end Bernoulli.DeSilvaJerison

end
end

end OAI
end

section
-- module Solutions.OAIQW_BernoulliCone.CapExtension
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Filter InnerProductSpace
open scoped Topology ContDiff
namespace Bernoulli.DeSilvaJerison

lemma upperFamily_eq_cap {x:Space 7} {l:ℝ} (hl:0<l)
    (hp:0<upperFamily l x) (hq:Cylindrical.radiusSq axis (l⁻¹ • x)≤1) :
    upperFamily l x=κ*l*smoothCap (l⁻¹ • x) := by
  have hh:0 < max (upperSigned (l⁻¹ • x)) 0:=
    pos_of_mul_pos_right hp (mul_nonneg κ_pos.le hl.le)
  have hs:0<upperSigned (l⁻¹ • x):=by simpa using hh
  rw [upperFamily,max_eq_left hs.le,upperSigned_cap hq]

/-- Smooth signed extensions of the inverse cap parameter through the actual
cap/exterior interface, obtained by IFT with local uniqueness. -/
lemma capParameter_local_extension {p:Space 7×ℝ} (hp:U p.1<p.2)
    (hq:Cylindrical.radiusSq axis ((upperParameter p.1 p.2)⁻¹ • p.1)≤1) :
    ∃ψ:Space 7×ℝ→ℝ,ContDiffAt ℝ ∞ ψ p ∧ ψ p=upperParameter p.1 p.2 ∧
      ∀ᶠ z in 𝓝 p, U z.1<z.2 →
        Cylindrical.radiusSq axis ((upperParameter z.1 z.2)⁻¹ • z.1)≤1 →
        ψ z=upperParameter z.1 z.2 := by
  let l:=upperParameter p.1 p.2
  have hl:0<l:=(upperParameter_spec hp).1
  have he:upperFamily l p.1=p.2:=(upperParameter_spec hp).2
  have hpos:0<upperFamily l p.1:=he.symm ▸ (U_nonneg p.1).trans_lt hp
  have hc:ContDiffAt ℝ ∞ smoothCap (l⁻¹ • p.1):=smoothCap_contDiffAt hq
  have hpc:0<smoothCap (l⁻¹ • p.1):=by
    rw [←upperSigned_cap hq]
    exact upperParameter_signed_pos hp
  let F:(Space 7×ℝ)×ℝ→ℝ:=fun z=>κ*z.2*smoothCap (z.2⁻¹ • z.1.1)-z.1.2
  have hi:ContDiffAt ℝ ∞ (fun z:(Space 7×ℝ)×ℝ=>z.2⁻¹ • z.1.1) (p,l):=
    (contDiffAt_snd.inv hl.ne').smul (contDiffAt_fst.fst)
  have hF:ContDiffAt ℝ ∞ F (p,l):=
    ((contDiffAt_const.mul contDiffAt_snd).mul (hc.comp (p,l) hi)).sub contDiffAt_fst.snd
  let ρ:=κ*(smoothCap (l⁻¹ • p.1)-inner ℝ (l⁻¹ • p.1) (gradient smoothCap (l⁻¹ • p.1)))
  have hρ:0<ρ:=mul_pos κ_pos (smoothCap_radial_defect_pos hq hpc)
  have hd:HasDerivAt (fun s:ℝ=>F (p,s)) ρ l := by
    have hh:=((Foliation.hasDerivAt_dilate p.1 hl.ne'
      (hc.differentiableAt (by simp))).const_mul κ).sub_const p.2
    simpa only [F,mul_assoc] using hh
  obtain ⟨ψ,hψ,hψ0,hψeq,huniq⟩:=Foliation.scalar_implicit_unique hF hd hρ.ne'
  refine ⟨ψ,hψ,hψ0,?_⟩
  have hF0:F (p,l)=0:=by
    dsimp [F]
    rw [←upperFamily_eq_cap hl hpos hq,he,sub_self]
  have ht:Tendsto (fun z:Space 7×ℝ=>(z,upperParameter z.1 z.2)) (𝓝 p) (𝓝 (p,l)):=
    tendsto_id.prodMk_nhds (upperParameter_continuousAt hp)
  filter_upwards [ht.eventually huniq] with z hz hzp hzq
  apply hz.mp
  rw [hF0]
  dsimp [F]
  have hzpos:0<upperFamily (upperParameter z.1 z.2) z.1:=
    (upperParameter_spec hzp).2.symm ▸ (U_nonneg z.1).trans_lt hzp
  rw [←upperFamily_eq_cap (upperParameter_spec hzp).1 hzpos hzq,
    (upperParameter_spec hzp).2,sub_self]

lemma gradient_smoothCap_contDiffAt {x:Space 7} (hq:Cylindrical.radiusSq axis x≤1) :
    ContDiffAt ℝ ∞ (gradient smoothCap) x := by
  exact (toDual ℝ (Space 7)).symm.contDiff.contDiffAt.comp x
    ((smoothCap_contDiffAt hq).fderiv_right (by simp))

/-- The actual one-sided cap flux admits a smooth germ even at the seam.
No regularity of the discontinuous full flux is asserted. -/
theorem upperFlux_cap_local_extension {p:Space 7×ℝ} (hp:U p.1<p.2)
    (hq:Cylindrical.radiusSq axis ((upperParameter p.1 p.2)⁻¹ • p.1)≤1) :
    ∃B:Space 7×ℝ→Space 7,ContDiffAt ℝ ∞ B p ∧ B p=upperFlux p ∧
      ∀ᶠ z in 𝓝 p,U z.1<z.2 →
        Cylindrical.radiusSq axis ((upperParameter z.1 z.2)⁻¹ • z.1)≤1 → B z=upperFlux z := by
  obtain ⟨ψ,hψ,hψ0,he⟩:=capParameter_local_extension hp hq
  let B:Space 7×ℝ→Space 7:=fun z=>κ • gradient smoothCap ((ψ z)⁻¹ • z.1)
  have hψp:ψ p≠0:=by rw [hψ0]; exact (upperParameter_spec hp).1.ne'
  have hn:ContDiffAt ℝ ∞ (fun z:Space 7×ℝ=>(ψ z)⁻¹ • z.1) p:=
    (hψ.inv hψp).smul contDiffAt_fst
  have hg:ContDiffAt ℝ ∞ (gradient smoothCap) ((ψ p)⁻¹ • p.1):=by
    rw [hψ0]; exact gradient_smoothCap_contDiffAt hq
  refine ⟨B,(hg.comp p hn).const_smul κ,?_,?_⟩
  · simp only [B,hψ0,upperFlux,ite_eq_left hp,ite_eq_left hq]
  · filter_upwards [he] with z hz hzp hzq
    simp only [B,hz hzp hzq,upperFlux,ite_eq_left hzp,ite_eq_left hzq]
end Bernoulli.DeSilvaJerison

end
end

end OAI
end

section
-- module Solutions.OAIQW_BernoulliCone.SeamHeight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Filter InnerProductSpace
open scoped Topology ContDiff
namespace Bernoulli.DeSilvaJerison

lemma seamHeight_formula (x:Space 7):
    seamHeight x=κ*Real.sqrt (Cylindrical.radiusSq axis x)*
      capH (Cylindrical.axis axis x/Real.sqrt (Cylindrical.radiusSq axis x)) := by
  simp only [seamHeight,Cylindrical.lift,div_eq_mul_inv,mul_assoc]
lemma seamHeight_contDiffAt {x:Space 7} (hq:0<Cylindrical.radiusSq axis x) :
    ContDiffAt ℝ ∞ seamHeight x := by
  have hs:ContDiffAt ℝ ∞ Real.sqrt (Cylindrical.radiusSq axis x):=Real.contDiffAt_sqrt hq.ne'
  have hL:ContDiffAt ℝ ∞ (Cylindrical.lift axis Real.sqrt (fun q:ℝ=>(Real.sqrt q)⁻¹) capH) x :=
    Cylindrical.contDiffAt_lift hs (hs.inv (Real.sqrt_pos.mpr hq).ne') capH_contDiff.contDiffAt
  exact contDiffAt_const.mul hL

lemma normalized_radius_seam {x:Space 7} (hq:0<Cylindrical.radiusSq axis x) :
    Cylindrical.radiusSq axis ((Real.sqrt (Cylindrical.radiusSq axis x))⁻¹ • x)=1 := by
  rw [Cylindrical.radiusSq_smul,inv_pow,Real.sq_sqrt hq.le,inv_mul_cancel₀ hq.ne']

lemma upperFamily_at_seam {x:Space 7} (hq:0<Cylindrical.radiusSq axis x) :
    upperFamily (Real.sqrt (Cylindrical.radiusSq axis x)) x=max (seamHeight x) 0 := by
  have hr:0<Real.sqrt (Cylindrical.radiusSq axis x):=Real.sqrt_pos.mpr hq
  have he:=normalized_radius_seam hq
  rw [upperFamily,upperSigned_cap he.le,smoothCap_at_seam he,seamHeight_formula,
    Cylindrical.axis_smul,←div_eq_inv_mul]
  rw [mul_max_of_nonneg _ _ (mul_nonneg κ_pos.le hr.le),mul_zero]

lemma upperParameter_seam_iff {p:Space 7×ℝ} (hp:U p.1<p.2)
    (hq:0<Cylindrical.radiusSq axis p.1) :
    Cylindrical.radiusSq axis ((upperParameter p.1 p.2)⁻¹ • p.1)≤1 ↔ seamHeight p.1≤p.2 := by
  let r:=Real.sqrt (Cylindrical.radiusSq axis p.1)
  let l:=upperParameter p.1 p.2
  have hr:0<r:=Real.sqrt_pos.mpr hq
  have hl:0<l:=(upperParameter_spec hp).1
  have hle:Cylindrical.radiusSq axis (l⁻¹ • p.1)≤1 ↔ r≤l := by
    rw [Cylindrical.radiusSq_smul,inv_pow,←div_eq_inv_mul,div_le_iff₀ (sq_pos_of_pos hl),one_mul]
    have he:r^2=Cylindrical.radiusSq axis p.1:=Real.sq_sqrt hq.le
    rw [←he]
    exact sq_le_sq₀ hr.le hl.le
  rw [hle,←not_lt,upperParameter_lt_iff hp hr,upperFamily_at_seam hq,not_lt]
  exact max_le_iff.trans (and_iff_left ((U_nonneg _).trans hp.le))
end Bernoulli.DeSilvaJerison

end
end

end OAI
end

section
-- module Solutions.OAIQW_BernoulliCone.ClosedGermExtension
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE uG

section
noncomputable section
open Set Filter
open scoped Topology ContDiff Manifold
namespace Bernoulli.LocalExtension
variable {E : Type uE} {G : Type uG} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup G] [NormedSpace ℝ G]
/-- C1 germs agreeing on a closed subset glue to a global C1 extension.
This is an application of the actual smooth partition of unity, not a Whitney
extension premise. -/
lemma exists_contDiff_one_of_closed_germs {S:Set E} (hS:IsClosed S) {F:E→G}
    (hg:∀x∈S,∃B:E→G,ContDiffAt ℝ 1 B x ∧ ∀ᶠ y in 𝓝 x,y∈S→B y=F y) :
    ∃B:E→G,ContDiff ℝ 1 B ∧ EqOn B F S := by
  classical
  let t:E→Set G:=fun x=>if x∈S then {F x} else univ
  have ht(x:E):Convex ℝ (t x):=by
    by_cases hx:x∈S
    · simpa only [t,ite_eq_left hx] using convex_singleton (F x)
    · simpa only [t,ite_eq_right hx] using (convex_univ : Convex ℝ (univ:Set G))
  have hl(x:E):∃U∈𝓝 x,∃g:E→G,ContMDiffOn 𝓘(ℝ,E) 𝓘(ℝ,G) 1 g U ∧
      ∀y∈U,g y∈t y := by
    by_cases hx:x∈S
    · obtain ⟨g,hgc,hge⟩:=hg x hx
      obtain ⟨V,hV,hgV⟩:=hgc.contDiffOn le_rfl (by norm_num)
      refine ⟨V∩{y|y∈S → g y=F y},inter_mem hV hge,g,?_,?_⟩
      · exact (hgV.mono inter_subset_left).contMDiffOn
      · intro y hy
        by_cases hyS:y∈S
        · simp only [t,ite_eq_left hyS,mem_singleton_iff]
          exact hy.2 hyS
        · simp only [t,ite_eq_right hyS,mem_univ]
    · refine ⟨Sᶜ,hS.isOpen_compl.mem_nhds hx,fun _=>0,contMDiffOn_const,?_⟩
      intro y hy
      simp only [t,ite_eq_right hy,mem_univ]
  obtain ⟨B,hB⟩:=exists_contMDiffMap_forall_mem_convex_of_local 𝓘(ℝ,E) ht hl
  refine ⟨B,B.contMDiff.contDiff,?_⟩
  intro x hx
  simpa only [t,ite_eq_left hx,mem_singleton_iff] using hB x
end Bernoulli.LocalExtension

end
end

end OAI
end

section
-- module Solutions.OAIQW_BernoulliCone.SmoothLocalizedExtension
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE uG

section
noncomputable section
open Set Filter
open scoped Topology ContDiff Manifold
namespace Bernoulli.LocalExtension
variable {E : Type uE} {G : Type uG} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup G] [NormedSpace ℝ G]
lemma exists_cutoff {K D:Set E} (hK:IsCompact K) (hD:IsOpen D) (hKD:K⊆D) :
    ∃φ:E→ℝ,ContDiff ℝ ∞ φ ∧ HasCompactSupport φ ∧ tsupport φ⊆D ∧
      (∀ᶠ x in 𝓝ˢ K,φ x=1) := by
  obtain ⟨δ,hδ,hδD⟩:=hK.exists_thickening_subset_open hD hKD
  have hki:K⊆interior (Metric.cthickening (δ/2) K):=
    (Metric.self_subset_thickening (half_pos hδ) _).trans
      (Metric.thickening_subset_interior_cthickening _ _)
  obtain ⟨φ,hφ1,hφ0,hφb⟩:=exists_contMDiffMap_one_nhds_of_subset_interior
    (𝓘(ℝ,E)) (n:=⊤) hK.isClosed hki
  refine ⟨φ,φ.contMDiff.contDiff,HasCompactSupport.intro hK.cthickening hφ0,?_,hφ1⟩
  have hs:tsupport (φ:E→ℝ)⊆Metric.cthickening (δ/2) K:=by
    apply closure_minimal _ Metric.isClosed_cthickening
    intro x hx
    by_contra hn
    exact hx (hφ0 x hn)
  exact hs.trans ((Metric.cthickening_subset_thickening' hδ (by linarith) _).trans hδD)

/-- A compact part of a genuinely smooth open domain admits a global smooth
representative. This permits use of global calculus only after verifying the
actual local hypotheses. -/
lemma exists_contDiff_extension {n:ℕ∞} {F:E→G} {K D:Set E}
    (hK:IsCompact K) (hD:IsOpen D) (hKD:K⊆D) (hF:ContDiffOn ℝ n F D) :
    ∃B:E→G,ContDiff ℝ n B ∧ B =ᶠ[𝓝ˢ K] F := by
  obtain ⟨φ,hφ,hφc,hφD,hφ1⟩:=exists_cutoff hK hD hKD
  refine ⟨fun x=>φ x • F x,?_,?_⟩
  · rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx:x∈D
    · exact (hφ.of_le (m:=n) (by exact_mod_cast (le_top : n≤⊤))).contDiffAt.smul (hF.contDiffAt (hD.mem_nhds hx))
    · have hxt:x∉tsupport φ:=fun h=>hx (hφD h)
      apply (contDiffAt_const (c:=(0:G))).congr_of_eventuallyEq
      filter_upwards [notMem_tsupport_iff_eventuallyEq.1 hxt] with y hy
      simp [hy]
  · filter_upwards [hφ1] with x hx
    simp [hx]
end Bernoulli.LocalExtension

end
end

end OAI
end

section
-- module Solutions.OAIQW_BernoulliCone.LocalFluxExtensions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Filter InnerProductSpace
open scoped Topology ContDiff
namespace Bernoulli.DeSilvaJerison

lemma exteriorFlux_contDiffAt {p:Space 7×ℝ} (hq:0<Cylindrical.radiusSq axis p.1) :
    ContDiffAt ℝ ∞ exteriorFlux p := by
  obtain ⟨hx,ha⟩:=radiusSq_pos_data hq
  have hZ:ContDiffAt ℝ ∞ Zsigned p.1:=signed_contDiffAt hx ha
  have hK:ContDiffAt ℝ ∞ KSup p.1:=KSup_contDiffAt hx ha
  have hgZ:ContDiffAt ℝ ∞ (gradient Zsigned) p.1:=
    (toDual ℝ (Space 7)).symm.contDiff.contDiffAt.comp p.1 (hZ.fderiv_right (by simp))
  have hgK:ContDiffAt ℝ ∞ (gradient KSup) p.1:=
    (toDual ℝ (Space 7)).symm.contDiff.contDiffAt.comp p.1 (hK.fderiv_right (by simp))
  exact ((hgZ.comp p contDiffAt_fst).const_smul κ).add
    (((contDiffAt_snd.sub (contDiffAt_const.mul (hZ.comp p contDiffAt_fst))).div
      (hK.comp p contDiffAt_fst) (KSup_pos hx ha).ne').smul (hgK.comp p contDiffAt_fst))
lemma upperFlux_eq_exterior {p:Space 7×ℝ} (hp:U p.1<p.2)
    (hq:0<Cylindrical.radiusSq axis p.1) (ht:p.2<seamHeight p.1) :
    upperFlux p=exteriorFlux p := by
  have hqn:¬Cylindrical.radiusSq axis ((upperParameter p.1 p.2)⁻¹ • p.1)≤1:=
    fun h=>not_lt.mpr ((upperParameter_seam_iff hp hq).mp h) ht
  have hqs:(upperParameter p.1 p.2)^2<Cylindrical.radiusSq axis p.1:=by
    have hl:0<upperParameter p.1 p.2:=(upperParameter_spec hp).1
    have hh:1<Cylindrical.radiusSq axis ((upperParameter p.1 p.2)⁻¹ • p.1):=not_le.mp hqn
    rw [Cylindrical.radiusSq_smul,inv_pow,←div_eq_inv_mul,lt_div_iff₀ (sq_pos_of_pos hl),one_mul] at hh
    exact hh
  rw [upperFlux_eq_calibration hp (ne_of_gt (not_le.mp hqn)),upperCalibration_outer_affine hp hqs]
  rfl

/-- The actual two branch fields have global C1 representatives on any compact
positive-height tube away from the axis. Only the cap-side field is extended
from a one-sided region; the full discontinuous flux is never declared smooth. -/
theorem compact_branch_extensions {K:Set (Space 7×ℝ)} (hK:IsCompact K)
    (hp:∀p∈K,U p.1<p.2) (hq:∀p∈K,0<Cylindrical.radiusSq axis p.1) :
    ∃A B:Space 7×ℝ→Space 7,ContDiff ℝ 1 A ∧ ContDiff ℝ 1 B ∧
      EqOn A exteriorFlux K ∧
      ∀p∈K,seamHeight p.1≤p.2 → B p=upperFlux p := by
  let D:Set (Space 7×ℝ):={p|0<Cylindrical.radiusSq axis p.1}
  have hD:IsOpen D:=isOpen_lt continuous_const
    ((Cylindrical.radiusSq_contDiff axis (n:=1)).continuous.comp continuous_fst)
  have hKD:K⊆D:=hq
  obtain ⟨A,hA,hAe⟩:=LocalExtension.exists_contDiff_extension (n:=1) hK hD hKD
    (fun p hpd=>(exteriorFlux_contDiffAt hpd).of_le (by simp) |>.contDiffWithinAt)
  let S:Set (Space 7×ℝ):={p∈K|seamHeight p.1≤p.2}
  have hσ:ContinuousOn (fun p:Space 7×ℝ=>seamHeight p.1) K:=by
    intro p hpk
    exact ((seamHeight_contDiffAt (hq p hpk)).continuousAt.comp continuous_fst.continuousAt).continuousWithinAt
  have hS:IsClosed S:=hK.isClosed.isClosed_le hσ continuousOn_snd
  obtain ⟨B,hB,hBe⟩:=LocalExtension.exists_contDiff_one_of_closed_germs hS (F:=upperFlux) (by
    intro p hps
    have hqp:=((upperParameter_seam_iff (hp p hps.1) (hq p hps.1)).mpr hps.2)
    obtain ⟨C,hC,hCp,hCe⟩:=upperFlux_cap_local_extension (hp p hps.1) hqp
    refine ⟨C,hC.of_le (by simp),?_⟩
    filter_upwards [hCe] with y hy hys
    exact hy (hp y hys.1) ((upperParameter_seam_iff (hp y hys.1) (hq y hys.1)).mpr hys.2))
  refine ⟨A,B,hA,hB,?_,?_⟩
  · intro p hpk
    exact (hAe.filter_mono (nhds_le_nhdsSet hpk)).self_of_nhds
  · intro p hpk hpt
    exact hBe ⟨hpk,hpt⟩
end Bernoulli.DeSilvaJerison

end
end

end OAI
end

section
-- module Solutions.OAIQW_BernoulliCone.JointIntervalIntegral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE uG

section
noncomputable section
open MeasureTheory Set Filter
open scoped Topology ContDiff
namespace Bernoulli.ParametricIntegral
variable {E : Type uE} {G : Type uG} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]

omit [CompleteSpace G] in
/-- A compact-interval parameter derivative, with domination obtained from C1
on an actual compact product. No derivative bound is an extra premise. -/
theorem fixed_hasFDerivAt {F:E×ℝ→G} (hF:ContDiff ℝ 1 F) (x:E) (a b:ℝ) :
    HasFDerivAt (fun y:E=>∫t in a..b,F (y,t))
      (∫t in a..b,fderiv ℝ F (x,t) ∘L ContinuousLinearMap.inl ℝ E ℝ) x := by
  let D:E×ℝ→E→L[ℝ] G:=fun p=>fderiv ℝ F p ∘L ContinuousLinearMap.inl ℝ E ℝ
  have hD:Continuous D:=(hF.continuous_fderiv (by norm_num)).clm_comp continuous_const
  have hc:IsCompact ((Metric.closedBall x 1)×ˢ(uIcc a b)):=
    (isCompact_closedBall x 1).prod isCompact_uIcc
  obtain ⟨C,hC⟩:=hc.exists_bound_of_continuousOn hD.continuousOn
  have hFu (y:E):Continuous (fun t:ℝ=>F (y,t)):=hF.continuous.comp (continuous_const.prodMk continuous_id)
  have hDu (y:E):Continuous (fun t:ℝ=>D (y,t)):=hD.comp (continuous_const.prodMk continuous_id)
  apply intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le
    (F:=fun y t=>F (y,t)) (F':=fun y t=>D (y,t))
    (s:=Metric.closedBall x 1) (bound:=fun _=>C) (Metric.closedBall_mem_nhds x (by norm_num))
  · exact .of_forall fun y=>(hFu y).aestronglyMeasurable
  · exact (hFu x).intervalIntegrable a b
  · exact (hDu x).aestronglyMeasurable
  · exact ae_of_all _ fun t ht y hy=>hC (y,t) ⟨hy,uIoc_subset_uIcc ht⟩
  · exact intervalIntegrable_const
  · exact ae_of_all _ fun t _ y _=>by
      have hi:HasFDerivAt (fun z:E=>(z,t)) (ContinuousLinearMap.inl ℝ E ℝ) y := by
        simpa only [ContinuousLinearMap.inl,id_eq] using
          (hasFDerivAt_id (𝕜:=ℝ) y).prodMk (hasFDerivAt_const t y)
      exact ((hF.differentiable (by norm_num)) (y,t)).hasFDerivAt.comp y hi

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E] [CompleteSpace G] in
lemma heightPrimitive_rescale (F:E×ℝ→G) (p:E×ℝ) :
    heightPrimitive F p=∫s in (0:ℝ)..1,p.2 • F (p.1,s*p.2) := by
  by_cases ht:p.2=0
  · simp [heightPrimitive,ht]
  · rw [intervalIntegral.integral_smul]
    have hh:=intervalIntegral.integral_comp_mul_right (a:=0) (b:=1) (fun s:ℝ=>F (p.1,s)) ht
    rw [hh]
    simp only [zero_mul,one_mul,smul_smul,mul_inv_cancel₀ ht,one_smul,heightPrimitive]

end Bernoulli.ParametricIntegral

end
end

end OAI
end

section
-- module Solutions.OAIQW_BernoulliCone.SmoothIntervalPrimitive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE uG

section
noncomputable section
open MeasureTheory Set Filter
open scoped Topology ContDiff
namespace Bernoulli.ParametricIntegral
variable {E : Type uE} {G : Type uG} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]

omit [CompleteSpace G] in
lemma fixed_contDiff_one [CompleteSpace G] {F:E×ℝ→G} (hF:ContDiff ℝ 1 F) :
    ContDiff ℝ 1 (fun x:E=>∫t in (0:ℝ)..1,F (x,t)) := by
  let D:E×ℝ→E→L[ℝ] G:=fun p=>fderiv ℝ F p ∘L ContinuousLinearMap.inl ℝ E ℝ
  have hD:Continuous D:=(hF.continuous_fderiv (by norm_num)).clm_comp continuous_const
  have hc:Continuous (fun x:E=>∫t in Icc (0:ℝ) 1,D (x,t)):=
    continuous_parametric_integral_of_continuous hD isCompact_Icc
  have he: (fun x:E=>∫t in Icc (0:ℝ) 1,D (x,t))=
      (fun x:E=>∫t in (0:ℝ)..1,D (x,t)) := by
    ext x
    rw [intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤1),integral_Icc_eq_integral_Ioc]
  rw [he] at hc
  exact contDiff_one_iff_hasFDerivAt.mpr ⟨_,hc,fun x=>fixed_hasFDerivAt hF x 0 1⟩

lemma heightPrimitive_contDiff_one {F:E×ℝ→G} (hF:ContDiff ℝ 1 F) :
    ContDiff ℝ 1 (heightPrimitive F) := by
  let B:(E×ℝ)×ℝ→G:=fun z=>z.1.2 • F (z.1.1,z.2*z.1.2)
  have hB:ContDiff ℝ 1 B:=by
    have hm:ContDiff ℝ 1 (fun z:(E×ℝ)×ℝ=>(z.1.1,z.2*z.1.2)):=by fun_prop
    exact (contDiff_fst.snd).smul (hF.comp hm)
  have he:heightPrimitive F=(fun y:E×ℝ=>∫s in (0:ℝ)..1,B (y,s)):=
    funext (heightPrimitive_rescale F)
  rw [he]
  exact fixed_contDiff_one hB
end Bernoulli.ParametricIntegral

end
end

end OAI
end

section
-- module Solutions.OAIQW_BernoulliCone.ClampedFoliationGraph
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE

section
noncomputable section
open Set Filter InnerProductSpace MeasureTheory
open scoped Topology ContDiff
namespace Bernoulli.Foliation
variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
lemma le_clampedHeight [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (u σ v:E→ℝ) (x:E):u x≤clampedHeight u σ v x:=le_max_left _ _
omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
lemma clampedHeight_le [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {u σ v:E→ℝ} {x:E} (h:u x≤v x):clampedHeight u σ v x≤v x:=
  max_le h (min_le_left _ _)
omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
lemma below_clampedHeight [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {u σ v:E→ℝ} {x:E} {t:ℝ}
    (hl:u x<t) (ht:t<clampedHeight u σ v x):t<σ x := by
  have hh:=lt_max_iff.mp ht
  rcases hh with h|h
  · exact False.elim ((not_lt.mpr hl.le) h)
  · exact h.trans_le (min_le_right _ _)
omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
lemma above_clampedHeight [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {u σ v:E→ℝ} {x:E} {t:ℝ}
    (hu:clampedHeight u σ v x<t) (ht:t<v x):σ x<t := by
  have hh:min (v x) (σ x)<t:=(le_max_right _ _).trans_lt hu
  exact (min_lt_iff.mp hh).resolve_left (not_lt.mpr ht.le)

omit [FiniteDimensional ℝ E] in
lemma graphPotential_eq_integral [FiniteDimensional ℝ E]
    {A:E×ℝ→E} (hA:Continuous A) (u v:E→ℝ) (x:E) :
    graphPotential A u v x=(2:ℝ) • (∫s in u x..v x,A (x,s)) := by
  have hc:Continuous (fun s:ℝ=>A (x,s)):=hA.comp (continuous_const.prodMk continuous_id)
  unfold graphPotential ParametricIntegral.heightPrimitive
  rw [←intervalIntegral.integral_interval_sub_left (hc.intervalIntegrable 0 (v x))
    (hc.intervalIntegrable 0 (u x))]

lemma clamped_integral_identity {F A B:E×ℝ→E} (hA:Continuous A) (hB:Continuous B)
    {u σ v:E→ℝ} {x:E} (huv:u x≤v x)
    (hFi:∀a b:ℝ,IntervalIntegrable (fun t:ℝ=>F (x,t)) volume a b)
    (hAe:∀t∈Ioo (u x) (v x),t<σ x → F (x,t)=A (x,t))
    (hBe:∀t∈Ioo (u x) (v x),σ x<t → F (x,t)=B (x,t)) :
    (2:ℝ) • (∫s in u x..v x,F (x,s))=
      splitGraphPotential A B u (clampedHeight u σ v) v x := by
  let w:=clampedHeight u σ v x
  have huw:u x≤w:=le_clampedHeight u σ v x
  have hwv:w≤v x:=clampedHeight_le huv
  have heA:(∫s in u x..w,F (x,s))=∫s in u x..w,A (x,s):=
    intervalIntegral.integral_congr_Ioo_of_le huw (fun t ht=>hAe t ⟨ht.1,ht.2.trans_le hwv⟩
      (below_clampedHeight ht.1 ht.2))
  have heB:(∫s in w..v x,F (x,s))=∫s in w..v x,B (x,s):=
    intervalIntegral.integral_congr_Ioo_of_le hwv (fun t ht=>hBe t ⟨huw.trans_lt ht.1,ht.2⟩
      (above_clampedHeight ht.1 ht.2))
  rw [splitGraphPotential,graphPotential_eq_integral hA,graphPotential_eq_integral hB]
  rw [←intervalIntegral.integral_add_adjacent_intervals (hFi (u x) w) (hFi w (v x)),heA,heB,smul_add]

lemma graphPotential_locallyLipschitz {A:E×ℝ→E} (hA:ContDiff ℝ 1 A)
    {u v:E→ℝ} (hu:LocallyLipschitz u) (hv:LocallyLipschitz v) :
    LocallyLipschitz (graphPotential A u v) := by
  have hh:= (ParametricIntegral.heightPrimitive_contDiff_one hA).locallyLipschitz
  exact ((2:ℝ) • ContinuousLinearMap.id ℝ E).lipschitz.locallyLipschitz.comp
    ((hh.comp (LocallyLipschitz.id.prodMk hv)).sub (hh.comp (LocallyLipschitz.id.prodMk hu)))

lemma clamped_split_locallyLipschitz {A B:E×ℝ→E} (hA:ContDiff ℝ 1 A) (hB:ContDiff ℝ 1 B)
    {u σ v:E→ℝ} (hu:LocallyLipschitz u) (hv:LocallyLipschitz v) (hσ:LocallyLipschitz σ) :
    LocallyLipschitz (splitGraphPotential A B u (clampedHeight u σ v) v) := by
  have hw:LocallyLipschitz (clampedHeight u σ v):=hu.max (hv.min hσ)
  exact (graphPotential_locallyLipschitz hA hu hw).add (graphPotential_locallyLipschitz hB hw hv)
end Bernoulli.Foliation

end
end

end OAI
end

section
-- module Solutions.OAIQW_BernoulliCone.VerticalGraphLocalization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE

section
noncomputable section
open Set Filter InnerProductSpace MeasureTheory
open scoped Topology ContDiff NNReal
namespace Bernoulli.Foliation
variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

lemma real_interval_combination {a b s:ℝ} (hab:a≤b) (hs:s∈Icc a b) :
    ∃t∈Icc (0:ℝ) 1,s=(1-t)*a+t*b := by
  rcases hab.eq_or_lt with he|hl
  · subst b
    exact ⟨0,by norm_num,by have hh:=le_antisymm hs.2 hs.1; simpa using hh⟩
  · refine ⟨(s-a)/(b-a),⟨div_nonneg (sub_nonneg.mpr hs.1) (sub_pos.mpr hl).le,?_⟩,?_⟩
    · exact (div_le_one (sub_pos.mpr hl)).mpr (sub_le_sub_right hs.2 a)
    · field_simp; ring

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
lemma eventually_vertical_segment [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {u v:E→ℝ} {x:E} (hu:ContinuousAt u x) (hv:ContinuousAt v x)
    (huv:u x≤v x) {V:Set (E×ℝ)} (hV:V∈𝓝ˢ ({x}×ˢ Icc (u x) (v x))) :
    ∀ᶠ y in 𝓝 x,u y≤v y → ∀s∈Icc (u y) (v y),(y,s)∈V := by
  have hh:∀ᶠ y in 𝓝 x,∀t∈Icc (0:ℝ) 1,(y,(1-t)*u y+t*v y)∈V:=by
    apply isCompact_Icc.eventually_forall_of_forall_eventually
    intro t ht
    have hc:ContinuousAt (fun p:E×ℝ=>(p.1,(1-p.2)*u p.1+p.2*v p.1)) (x,t):=by
      exact continuous_fst.continuousAt.prodMk
        (((continuousAt_const.sub continuous_snd.continuousAt).mul (hu.comp continuous_fst.continuousAt)).add
          (continuous_snd.continuousAt.mul (hv.comp continuous_fst.continuousAt)))
    have hp:(x,(1-t)*u x+t*v x)∈({x}×ˢ Icc (u x) (v x)):=by
      refine ⟨rfl,?_,?_⟩
      · nlinarith [mul_nonneg ht.1 (sub_nonneg.mpr huv)]
      · nlinarith [mul_nonneg (sub_nonneg.mpr ht.2) (sub_nonneg.mpr huv)]
    exact hc.eventually ((nhds_le_nhdsSet hp) hV)
  filter_upwards [hh] with y hy hyuv s hs
  obtain ⟨t,ht,rfl⟩:=real_interval_combination hyuv hs
  exact hy t ht

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
lemma locallyLipschitz_germ [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {F Q:E→E} {x:E} (hQ:LocallyLipschitz Q) (he:F =ᶠ[𝓝 x] Q) :
    ∃K:ℝ≥0,∃V∈𝓝 x,LipschitzOnWith K F V := by
  obtain ⟨K,V,hV,hL⟩:=hQ x
  refine ⟨K,V∩{y|F y=Q y},inter_mem hV he,?_⟩
  intro y hy z hz
  rw [hy.2,hz.2]
  exact hL hy.1 hz.1

lemma verticalPotential_smooth_germ {F:E×ℝ→E} {u v:E→ℝ}
    (hu:LocallyLipschitz u) (hv:LocallyLipschitz v) (huv:∀y,u y≤v y) {x:E}
    {D:Set (E×ℝ)} (hD:IsOpen D) (hFD:ContDiffOn ℝ 1 F D)
    (hK:({x}×ˢ Icc (u x) (v x))⊆D)
    (_hFi:∀y a b,IntervalIntegrable (fun t:ℝ=>F (y,t)) volume a b) :
    ∃K:ℝ≥0,∃V∈𝓝 x,LipschitzOnWith K (verticalPotential F u v) V := by
  obtain ⟨A,hA,hAe⟩:=LocalExtension.exists_contDiff_extension
    (isCompact_singleton.prod isCompact_Icc) hD hK hFD
  have hn:=eventually_vertical_segment hu.continuous.continuousAt hv.continuous.continuousAt
    (huv x) hAe
  apply locallyLipschitz_germ (graphPotential_locallyLipschitz hA hu hv)
  filter_upwards [hn] with y hy
  rw [graphPotential_eq_integral hA.continuous]
  unfold verticalPotential
  congr 1
  apply intervalIntegral.integral_congr_Ioo_of_le (huv y)
  intro s hs
  exact (hy (huv y) s ⟨hs.1.le,hs.2.le⟩).symm
end Bernoulli.Foliation

end
end

end OAI
end

section
-- module Solutions.OAIQW_BernoulliCone.PrimitiveLocal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Filter InnerProductSpace MeasureTheory
open scoped Topology ContDiff NNReal
namespace Bernoulli.DeSilvaJerison
open Foliation

lemma above_U_isOpen : IsOpen {p:Space 7×ℝ|U p.1<p.2}:=
  isOpen_lt (U_continuous.comp continuous_fst) continuous_snd

lemma capTube_isOpen : IsOpen {p:Space 7×ℝ|U p.1<p.2 ∧
    Cylindrical.radiusSq axis ((upperParameter p.1 p.2)⁻¹ • p.1)<1} := by
  rw [isOpen_iff_mem_nhds]
  intro p hp
  have hq:ContinuousAt (fun z:Space 7×ℝ=>
      Cylindrical.radiusSq axis ((upperParameter z.1 z.2)⁻¹ • z.1)) p:=
    (Cylindrical.radiusSq_contDiff axis (n:=1)).continuous.continuousAt.comp
      (((upperParameter_continuousAt hp.1).inv₀ (upperParameter_spec hp.1).1.ne').smul continuous_fst.continuousAt)
  exact inter_mem (above_U_isOpen.mem_nhds hp.1) (hq.eventually (gt_mem_nhds hp.2))

lemma upperFlux_primitive_axis_lipschitz {u v:Space 7→ℝ}
    (hu:LocallyLipschitz u) (hv:LocallyLipschitz v) (huv:∀y,u y≤v y)
    (huU:∀y,U y<u y) {x:Space 7} (hqx:Cylindrical.radiusSq axis x=0) :
    ∃K:ℝ≥0,∃V∈𝓝 x,LipschitzOnWith K (verticalPotential upperFlux u v) V := by
  apply verticalPotential_smooth_germ hu hv huv capTube_isOpen
    (fun p hp=>(upperFlux_contDiffAt hp.1 hp.2.ne).of_le (by simp) |>.contDiffWithinAt)
    _ upperFlux_intervalIntegrable
  intro p hp
  have hpx:p.1=x:=hp.1
  change U p.1<p.2 ∧ Cylindrical.radiusSq axis ((upperParameter p.1 p.2)⁻¹ • p.1)<1
  rw [hpx]
  refine ⟨(huU x).trans_le hp.2.1,?_⟩
  rw [Cylindrical.radiusSq_smul,hqx,mul_zero]
  norm_num

lemma seamHeight_smooth_germ {x:Space 7} (hqx:0<Cylindrical.radiusSq axis x) :
    ∃σ:Space 7→ℝ,ContDiff ℝ 1 σ ∧ σ =ᶠ[𝓝 x] seamHeight := by
  have hD:IsOpen {y:Space 7|0<Cylindrical.radiusSq axis y}:=
    isOpen_lt continuous_const (Cylindrical.radiusSq_contDiff axis (n:=1)).continuous
  obtain ⟨σ,hσ,hσe⟩:=LocalExtension.exists_contDiff_extension (n:=1)
    (isCompact_singleton (x:=x)) hD (singleton_subset_iff.mpr hqx)
    (fun y hy=>(seamHeight_contDiffAt hy).of_le (by simp) |>.contDiffWithinAt)
  exact ⟨σ,hσ,by simpa using hσe⟩

lemma upperFlux_compact_tube {x:Space 7} {a b:ℝ} (hua:U x<a)
    (hqx:0<Cylindrical.radiusSq axis x) :
    ∃K:Set (Space 7×ℝ),IsCompact K ∧ ({x}×ˢ Icc a b)⊆interior K ∧
      (∀p∈K,U p.1<p.2) ∧ (∀p∈K,0<Cylindrical.radiusSq axis p.1) := by
  let D:Set (Space 7×ℝ):={p|U p.1<p.2 ∧ 0<Cylindrical.radiusSq axis p.1}
  have hD:IsOpen D:=above_U_isOpen.inter (isOpen_lt continuous_const
    ((Cylindrical.radiusSq_contDiff axis (n:=1)).continuous.comp continuous_fst))
  have hk:({x}×ˢ Icc a b)⊆D:=by
    intro p hp
    have hpx:p.1=x:=hp.1
    exact ⟨by rw [hpx]; exact hua.trans_le hp.2.1,by rwa [hpx]⟩
  obtain ⟨K,hK,hKi,hKD⟩:=exists_compact_between (isCompact_singleton.prod isCompact_Icc) hD hk
  exact ⟨K,hK,hKi,fun p hp=>(hKD hp).1,fun p hp=>(hKD hp).2⟩

lemma upperFlux_primitive_offaxis_lipschitz {u v:Space 7→ℝ}
    (hu:LocallyLipschitz u) (hv:LocallyLipschitz v) (huv:∀y,u y≤v y)
    (huU:∀y,U y<u y) {x:Space 7} (hqx:0<Cylindrical.radiusSq axis x) :
    ∃K:ℝ≥0,∃V∈𝓝 x,LipschitzOnWith K (verticalPotential upperFlux u v) V := by
  obtain ⟨K,hK,hKi,hKp,hKq⟩:=upperFlux_compact_tube (b:=v x) (huU x) hqx
  obtain ⟨A,B,hA,hB,hAe,hBe⟩:=compact_branch_extensions hK hKp hKq
  obtain ⟨σ,hσ,hσe⟩:=seamHeight_smooth_germ hqx
  have hn:=eventually_vertical_segment hu.continuous.continuousAt hv.continuous.continuousAt
    (huv x) (subset_interior_iff_mem_nhdsSet.mp hKi)
  apply locallyLipschitz_germ (clamped_split_locallyLipschitz hA hB hu hv hσ.locallyLipschitz)
  filter_upwards [hn,hσe] with y hy hye
  apply clamped_integral_identity hA.continuous hB.continuous (huv y) (upperFlux_intervalIntegrable y)
  · intro t ht hts
    have hp:(y,t)∈K:=hy (huv y) t ⟨ht.1.le,ht.2.le⟩
    rw [hAe hp,upperFlux_eq_exterior (hKp _ hp) (hKq _ hp) (by rwa [←hye])]
  · intro t ht hst
    have hp:(y,t)∈K:=hy (huv y) t ⟨ht.1.le,ht.2.le⟩
    exact (hBe _ hp (by rw [←hye]; exact hst.le)).symm

/-- The actual discontinuous calibration has a locally Lipschitz vertical
primitive whenever its endpoints stay strictly above U. This includes the
axis and the vertex, not just the smooth off-interface regions. -/
theorem upperFlux_primitive_locallyLipschitz {u v:Space 7→ℝ}
    (hu:LocallyLipschitz u) (hv:LocallyLipschitz v) (huv:∀y,u y≤v y)
    (huU:∀y,U y<u y) : LocallyLipschitz (verticalPotential upperFlux u v) := by
  intro x
  rcases (Cylindrical.radiusSq_nonneg axis x axis_norm).eq_or_lt with he|hl
  · exact upperFlux_primitive_axis_lipschitz hu hv huv huU he.symm
  · exact upperFlux_primitive_offaxis_lipschitz hu hv huv huU hl
end Bernoulli.DeSilvaJerison

end
end

end OAI
end

section
-- module Solutions.OAIQW_BernoulliCone.CompactLipschitzDivergence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE uG

section
noncomputable section
open MeasureTheory Set Filter InnerProductSpace
open scoped Topology ContDiff NNReal
namespace Bernoulli.Foliation
variable {E : Type uE} {G : Type uG} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

omit [NormedSpace ℝ G] in
lemma locallyLipschitz_compact_lipschitz [NormedSpace ℝ G] {F:E→G} (hl:LocallyLipschitz F)
    (hc:HasCompactSupport F) : ∃K:ℝ≥0,LipschitzWith K F := by
  obtain ⟨R,hR⟩:=hc.isBounded.subset_ball (0:E)
  obtain ⟨K,hK⟩:=hl.locallyLipschitzOn.exists_lipschitzOnWith_of_compact
    (isCompact_closedBall (0:E) (R+1))
  obtain ⟨M,hM⟩:=hc.exists_bound_of_continuousOn hl.continuous.continuousOn
  let C:ℝ≥0:=⟨max (K:ℝ) (max M 0),le_max_of_le_right (le_max_right _ _)⟩
  have hKC:(K:ℝ)≤C:=le_max_left _ _
  have hMC:M≤(C:ℝ):=(le_max_left M 0).trans (le_max_right _ _)
  have hbound (x y:E) (hx:x∈tsupport F) (hy:y∉Metric.closedBall (0:E) (R+1)):
      dist (F x) (F y)≤(C:ℝ)*dist x y := by
    have hFx:dist x 0<R:=hR hx
    have hFy:R+1<dist y 0:=by simpa only [Metric.mem_closedBall,not_le] using hy
    have hdy:1≤dist x y:=by have hh:=dist_triangle y x 0; rw [dist_comm y x] at hh; linarith
    have hyS:y∉tsupport F:=by
      intro hys
      have hyR:=hR hys
      change dist y 0<R at hyR
      linarith
    rw [image_eq_zero_of_notMem_tsupport hyS,dist_zero_right]
    exact (hM x hx).trans (hMC.trans (le_mul_of_one_le_right C.2 hdy))
  refine ⟨C,LipschitzWith.of_dist_le_mul fun x y=>?_⟩
  by_cases hx:x∈tsupport F
  · by_cases hy:y∈Metric.closedBall (0:E) (R+1)
    · have hxB:x∈Metric.closedBall (0:E) (R+1):=by
        have hh:=hR hx
        change dist x 0<R at hh
        change dist x 0≤R+1
        linarith
      exact (hK.dist_le_mul x hxB y hy).trans (mul_le_mul_of_nonneg_right hKC dist_nonneg)
    · exact hbound x y hx hy
  · by_cases hy:y∈tsupport F
    · by_cases hxB:x∈Metric.closedBall (0:E) (R+1)
      · have hyB:y∈Metric.closedBall (0:E) (R+1):=by
          have hh:=hR hy
          change dist y 0<R at hh
          change dist y 0≤R+1
          linarith
        exact (hK.dist_le_mul x hxB y hyB).trans (mul_le_mul_of_nonneg_right hKC dist_nonneg)
      · simpa only [dist_comm] using hbound y x hy hxB
    · rw [image_eq_zero_of_notMem_tsupport hx,image_eq_zero_of_notMem_tsupport hy,dist_self]
      positivity

lemma integral_directional_compact {d:ℕ} {f:Space d→ℝ} {K:ℝ≥0}
    (hf:LipschitzWith K f) (hc:HasCompactSupport f) (v:Space d) :
    (∫x,fderiv ℝ f x v)=0 := by
  obtain ⟨φ,hφ,hφc,hφS,hφ1⟩:=LocalExtension.exists_cutoff hc isOpen_univ (subset_univ _)
  have hφT:Test univ φ:=⟨hφ,hφc,hφS⟩
  have hh:=LipschitzSobolev.weakGradient hf univ φ hφT v
  simp only [Measure.restrict_univ,inner_gradient_left] at hh
  have hr:(fun x:Space d=>fderiv ℝ f x v * φ x)=(fun x=>fderiv ℝ f x v):=by
    funext x
    by_cases hx:x∈tsupport f
    · have he:φ x=1:=(show φ =ᶠ[𝓝 x] (fun _=>1) from hφ1.filter_mono (nhds_le_nhdsSet hx)).self_of_nhds
      rw [he,mul_one]
    · rw [fderiv_of_notMem_tsupport ℝ hx,zero_apply,zero_mul]
  have he:(fun x:Space d=>f x*(fderiv ℝ φ x) v)=0:=by
    funext x
    by_cases hx:x∈tsupport f
    · have heq:φ =ᶠ[𝓝 x] (fun _=>1):=hφ1.filter_mono (nhds_le_nhdsSet hx)
      simp only [heq.fderiv_eq,fderiv_fun_const,zero_apply,mul_zero,Pi.zero_apply]
    · rw [image_eq_zero_of_notMem_tsupport hx,zero_mul]
      rfl
  rw [hr,he] at hh
  simpa only [integral_zero,Pi.zero_def,zero_eq_neg] using hh
lemma integrable_directional_compact {d:ℕ} {f:Space d→ℝ} {K:ℝ≥0}
    (hf:LipschitzWith K f) (hc:HasCompactSupport f) (v:Space d) :
    Integrable (fun x=>fderiv ℝ f x v) := by
  have hs:Function.support (fun x=>fderiv ℝ f x v)⊆tsupport f:=
    (subset_tsupport _).trans (tsupport_fderiv_apply_subset ℝ v)
  apply (integrableOn_iff_integrable_of_support_subset hs).mp
  apply (integrableOn_const (μ:=volume) (C:=((K:ℝ)*‖v‖)) hc.measure_ne_top).mono'
    (((continuous_id.clm_apply continuous_const : Continuous (fun L:Space d→L[ℝ]ℝ=>L v)).measurable.comp (measurable_fderiv ℝ f)).aestronglyMeasurable.restrict)
  filter_upwards [] with x
  exact ((fderiv ℝ f x).le_opNorm v).trans
    (mul_le_mul_of_nonneg_right (norm_fderiv_le_of_lipschitz ℝ hf) (norm_nonneg v))

lemma integrable_divergence_compact {d:ℕ} {F:Space d→Space d} {K:ℝ≥0}
    (hF:LipschitzWith K F) (hc:HasCompactSupport F) : Integrable (divergence F) := by
  let e:=stdOrthonormalBasis ℝ (Space d)
  let f:=fun i x=>inner ℝ (e i) (F x)
  have hf i:LipschitzWith (‖innerSL ℝ (e i)‖₊*K) (f i):=
    (innerSL ℝ (e i)).lipschitz.comp hF
  have hfc i:HasCompactSupport (f i):=by
    apply HasCompactSupport.intro hc
    intro x hx
    simp only [f,image_eq_zero_of_notMem_tsupport hx,inner_zero_right]
  have he:divergence F =ᵐ[volume] (fun x=>∑i,fderiv ℝ (f i) x (e i)):=by
    filter_upwards [hF.ae_differentiableAt] with x hx
    unfold divergence
    apply Finset.sum_congr rfl
    intro i hi
    have hd:HasFDerivAt (f i) ((innerSL ℝ (e i)) ∘L fderiv ℝ F x) x:=
      (innerSL ℝ (e i)).hasFDerivAt.comp x hx.hasFDerivAt
    rw [hd.fderiv]
    rfl
  exact (integrable_finsetSum _ (fun i hi=>integrable_directional_compact (hf i) (hfc i) (e i))).congr he.symm

lemma divergence_zero_outside_support {d:ℕ} {F:Space d→Space d} {x:Space d}
    (hx:x∉tsupport F) : divergence F x=0 := by
  unfold divergence
  simp only [fderiv_of_notMem_tsupport ℝ hx,zero_apply,inner_zero_right,
    Finset.sum_const_zero]

/-- The divergence of a genuine compactly supported Lipschitz vector field
has integral zero, with the a.e. derivative justified by Rademacher. -/
theorem integral_divergence_compact {d:ℕ} {F:Space d→Space d} {K:ℝ≥0}
    (hF:LipschitzWith K F) (hc:HasCompactSupport F) :
    (∫x,divergence F x)=0 := by
  let e:=stdOrthonormalBasis ℝ (Space d)
  let f:=fun i x=>inner ℝ (e i) (F x)
  have hf i:LipschitzWith (‖innerSL ℝ (e i)‖₊*K) (f i):=
    (innerSL ℝ (e i)).lipschitz.comp hF
  have hfc i:HasCompactSupport (f i):=by
    apply HasCompactSupport.intro hc
    intro x hx
    simp only [f,image_eq_zero_of_notMem_tsupport hx,inner_zero_right]
  have he:divergence F =ᵐ[volume] (fun x=>∑i,fderiv ℝ (f i) x (e i)):=by
    filter_upwards [hF.ae_differentiableAt] with x hx
    unfold divergence
    apply Finset.sum_congr rfl
    intro i hi
    have hd:HasFDerivAt (f i) ((innerSL ℝ (e i)) ∘L fderiv ℝ F x) x:=
      (innerSL ℝ (e i)).hasFDerivAt.comp x hx.hasFDerivAt
    rw [hd.fderiv]
    rfl
  rw [integral_congr_ae he,integral_finsetSum _ (fun i hi=>integrable_directional_compact (hf i) (hfc i) (e i))]
  simp only [integral_directional_compact (hf _) (hfc _),Finset.sum_const_zero]
end Bernoulli.Foliation

end
end

end OAI
end

section
-- module Solutions.OAIQW_BernoulliCone.ClampedSeam
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Filter InnerProductSpace MeasureTheory
open scoped Topology ContDiff NNReal
namespace Bernoulli.DeSilvaJerison
open Foliation
lemma clamped_seam_axis {u v:Space 7→ℝ} {x:Space 7} (hu:U x<u x)
    (hq:Cylindrical.radiusSq axis x=0) : clampedHeight u seamHeight v x=u x := by
  have hσ:seamHeight x=0:=by rw [seamHeight_formula,hq,Real.sqrt_zero]; ring
  unfold clampedHeight
  rw [hσ,max_eq_left ((min_le_right _ _).trans ((U_nonneg x).trans hu.le))]

lemma clamped_seam_le_lower {u v:Space 7→ℝ} {x:Space 7} (hu:U x<u x)
    (hq:Cylindrical.radiusSq axis ((upperParameter x (u x))⁻¹ • x)<1) :
    clampedHeight u seamHeight v x=u x := by
  rcases (Cylindrical.radiusSq_nonneg axis x axis_norm).eq_or_lt with he|hl
  · exact clamped_seam_axis hu he.symm
  · have hs:seamHeight x≤u x:=(upperParameter_seam_iff (p:=(x,u x)) hu hl).mp hq.le
    exact max_eq_left ((min_le_right _ _).trans hs)

theorem clamped_seam_locallyLipschitz {u v:Space 7→ℝ}
    (hu:LocallyLipschitz u) (hv:LocallyLipschitz v) (huU:∀y,U y<u y) :
    LocallyLipschitz (clampedHeight u seamHeight v) := by
  intro x
  rcases (Cylindrical.radiusSq_nonneg axis x axis_norm).eq_or_lt with he|hl
  · have hpx:(x,u x)∈{p:Space 7×ℝ|U p.1<p.2 ∧
        Cylindrical.radiusSq axis ((upperParameter p.1 p.2)⁻¹ • p.1)<1}:=by
      refine ⟨huU x,?_⟩
      rw [Cylindrical.radiusSq_smul,←he,mul_zero]
      norm_num
    have hn:∀ᶠ y in 𝓝 x,Cylindrical.radiusSq axis ((upperParameter y (u y))⁻¹ • y)<1:=
      ((continuousAt_id.prodMk hu.continuous.continuousAt).eventually (capTube_isOpen.mem_nhds hpx)).mono fun _ h=>h.2
    obtain ⟨K,V,hV,hL⟩:=hu x
    refine ⟨K,V∩{y|clampedHeight u seamHeight v y=u y},inter_mem hV (hn.mono fun y hy=>clamped_seam_le_lower (huU y) hy),?_⟩
    intro y hy z hz
    rw [hy.2,hz.2]
    exact hL hy.1 hz.1
  · obtain ⟨σ,hσ,hσe⟩:=seamHeight_smooth_germ hl
    have hw:LocallyLipschitz (clampedHeight u σ v):=hu.max (hv.min hσ.locallyLipschitz)
    obtain ⟨K,V,hV,hL⟩:=hw x
    refine ⟨K,V∩{y|σ y=seamHeight y},inter_mem hV hσe,?_⟩
    intro y hy z hz
    have he1:clampedHeight u seamHeight v y=clampedHeight u σ v y:=by
      change max (u y) (min (v y) (seamHeight y))=max (u y) (min (v y) (σ y))
      rw [hy.2]
    have he2:clampedHeight u seamHeight v z=clampedHeight u σ v z:=by
      change max (u z) (min (v z) (seamHeight z))=max (u z) (min (v z) (σ z))
      rw [hz.2]
    rw [he1,he2]
    exact hL hy.1 hz.1

lemma clamped_sub_lower_compact {u v:Space 7→ℝ} (h:HasCompactSupport (fun x=>v x-u x)) :
    HasCompactSupport (fun x=>clampedHeight u seamHeight v x-u x) := by
  apply HasCompactSupport.intro h
  intro x hx
  have hvu:v x=u x:=sub_eq_zero.mp (image_eq_zero_of_notMem_tsupport (f:=fun y=>v y-u y) hx)
  change max (u x) (min (v x) (seamHeight x))-u x=0
  rw [hvu,max_eq_left (min_le_left _ _),sub_self]

theorem clamped_seam_lipschitz {u v:Space 7→ℝ} {K L:ℝ≥0}
    (hu:LipschitzWith K u) (hv:LipschitzWith L v) (huU:∀y,U y<u y)
    (hc:HasCompactSupport (fun x=>v x-u x)) :
    ∃M:ℝ≥0,LipschitzWith M (clampedHeight u seamHeight v) := by
  have hh:=clamped_seam_locallyLipschitz hu.locallyLipschitz hv.locallyLipschitz huU
  obtain ⟨C,hC⟩:=locallyLipschitz_compact_lipschitz (hh.sub hu.locallyLipschitz) (clamped_sub_lower_compact hc)
  refine ⟨C+K,?_⟩
  convert! hC.add hu using 1
  ext x
  exact (sub_add_cancel _ _).symm
end Bernoulli.DeSilvaJerison

end
end

end OAI
end

section
-- module Solutions.OAIQW_BernoulliCone.ClampedGraphBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE

section
noncomputable section
open Set Filter InnerProductSpace MeasureTheory
open scoped Topology ContDiff
namespace Bernoulli.Foliation
variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

lemma gradient_eq_of_order_contact {u v:E→ℝ} {x:E}
    (hu:DifferentiableAt ℝ u x) (hv:DifferentiableAt ℝ v x)
    (hle:∀y,u y≤v y) (he:u x=v x) : gradient u x=gradient v x := by
  have hm:IsLocalMin (fun y=>v y-u y) x:=by
    filter_upwards [] with y
    change v x-u x≤v y-u y
    rw [←he,sub_self]
    exact sub_nonneg.mpr (hle y)
  have hh:=hm.hasFDerivAt_eq_zero (hv.hasFDerivAt.sub hu.hasFDerivAt)
  exact congrArg ((toDual ℝ E).symm) (sub_eq_zero.mp hh).symm

end Bernoulli.Foliation

end
end

end OAI
end

section
-- module Solutions.OAIQW_BernoulliCone.PositiveTrace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Filter InnerProductSpace
open scoped Topology ContDiff
namespace Bernoulli.DeSilvaJerison
lemma U_lt_upperFamily {x:Space 7} (hx:0<U x) {l:ℝ} (hl:0<l) :
    U x<upperFamily l x := by
  have ha:0<l/2:=half_pos hl
  have hs:=U_le_upperFamily x ha
  exact hs.trans_lt (upperFamily_strict ha (by linarith) (hx.trans_le hs))
lemma U_pos_radiusSq {x:Space 7} (hx:0<U x) : 0<Cylindrical.radiusSq axis x := by
  have hq:=Cylindrical.radiusSq_nonneg axis x axis_norm
  by_contra hn
  have he:Cylindrical.radiusSq axis x=0:=le_antisymm (not_lt.mp hn) hq
  rw [U_zero_of_radiusSq_zero he] at hx
  exact lt_irrefl _ hx
lemma upperParameter_eventually_outer {x:Space 7} (hx:0<U x) :
    ∀ᶠ t:ℝ in 𝓝[>] (U x),(upperParameter x t)^2<Cylindrical.radiusSq axis x := by
  have hq:=U_pos_radiusSq hx
  let l:=Real.sqrt (Cylindrical.radiusSq axis x)
  have hl:0<l:=Real.sqrt_pos.mpr hq
  have hlt:=U_lt_upperFamily hx hl
  have hn:∀ᶠ t:ℝ in 𝓝[>] (U x),t<upperFamily l x :=
    (gt_mem_nhds hlt).filter_mono nhdsWithin_le_nhds
  filter_upwards [hn,self_mem_nhdsWithin] with t ht htx
  have hh:upperParameter x t<l:=(upperParameter_lt_iff htx hl).mpr ht
  have hp:= (upperParameter_spec htx).1
  have hsq: (upperParameter x t)^2<l^2 := (sq_lt_sq₀ hp.le hl.le).mpr hh
  simpa only [l,Real.sq_sqrt hq.le] using hsq
lemma U_eq_signed_of_pos {x:Space 7} (hx:0<U x) : U x=κ*Zsigned x := by
  have hq := U_pos_radiusSq hx
  rw [U_eq_signed_pospart hq] at hx ⊢
  have hh:0<Zsigned x:=by
    have hh1:0 < max (Zsigned x) 0:=pos_of_mul_pos_right hx κ_pos.le
    simpa using hh1
  rw [max_eq_left hh.le]
lemma gradient_U_eq_signed {x:Space 7} (hx:0<U x) :
    gradient U x=κ • gradient Zsigned x := by
  have hn:∀ᶠ y in 𝓝 x,0<U y:=U_continuous.continuousAt.eventually (lt_mem_nhds hx)
  have he:U =ᶠ[𝓝 x] (fun y=>κ*Zsigned y):=hn.mono fun y hy=>U_eq_signed_of_pos hy
  obtain ⟨hx0,ha⟩:=radiusSq_pos_data (U_pos_radiusSq hx)
  rw [gradient,he.fderiv_eq]
  exact gradient_const_mul κ ((signed_contDiffAt (n:=1) hx0 ha).differentiableAt (by norm_num))
lemma normalized_radiusSq_ne_one {x:Space 7} {l:ℝ} (hl:0<l)
    (hq:l^2<Cylindrical.radiusSq axis x) :
    Cylindrical.radiusSq axis (l⁻¹ • x)≠1 := by
  rw [Cylindrical.radiusSq_smul]
  have hh:(l⁻¹)^2*Cylindrical.radiusSq axis x>1:=by
    rw [inv_pow,←div_eq_inv_mul]
    change 1<Cylindrical.radiusSq axis x/l^2
    exact (lt_div_iff₀ (sq_pos_of_pos hl)).mpr (by simpa only [one_mul] using hq)
  exact ne_of_gt hh
lemma upperFlux_outer_affine {x:Space 7} {t:ℝ} (ht:U x<t)
    (hq:(upperParameter x t)^2<Cylindrical.radiusSq axis x) :
    upperFlux (x,t)=κ • gradient Zsigned x+((t-κ*Zsigned x)/KSup x) • gradient KSup x := by
  have hl:0<upperParameter x t:=(upperParameter_spec ht).1
  have hqe:=normalized_radiusSq_ne_one hl hq
  rw [upperFlux_eq_calibration (p:=(x,t)) ht hqe]
  exact upperCalibration_outer_affine (p:=(x,t)) ht hq
/-- The actual bounded field has the exact positive-phase lower trace. -/
theorem upperFlux_tendsto_positive_trace {x:Space 7} (hx:0<U x) :
    Tendsto (fun t:ℝ=>upperFlux (x,t)) (𝓝[>] (U x)) (𝓝 (gradient U x)) := by
  have he:(fun t:ℝ=>upperFlux (x,t)) =ᶠ[𝓝[>] (U x)]
      (fun t=>κ • gradient Zsigned x+((t-κ*Zsigned x)/KSup x) • gradient KSup x) := by
    filter_upwards [upperParameter_eventually_outer hx,self_mem_nhdsWithin] with t hq ht
    exact upperFlux_outer_affine ht hq
  have hc:ContinuousAt (fun t:ℝ=>κ • gradient Zsigned x+
      ((t-κ*Zsigned x)/KSup x) • gradient KSup x) (U x):=by fun_prop
  apply Tendsto.congr' he.symm
  simpa only [U_eq_signed_of_pos hx,sub_self,zero_div,zero_smul,add_zero,gradient_U_eq_signed hx] using
    hc.tendsto.mono_left nhdsWithin_le_nhds
end Bernoulli.DeSilvaJerison

end
end

end OAI
end

section
-- module Solutions.OAIQW_BernoulliCone.CompactZeroFiber
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE

section
noncomputable section
open Set Filter
open scoped Topology
namespace Bernoulli.Foliation
variable {E : Type uE} [TopologicalSpace E]
/-- Compact zero-fiber control. No convergence of the selected root is needed. -/
lemma eventually_near_zero_fiber {K:Set E} (hK:IsCompact K) {f g:E→ℝ} {C:ℝ}
    (hf:∀x∈K,ContinuousAt f x) (hg:∀x∈K,ContinuousAt g x)
    (hzero:∀x∈K,f x=0 → g x<C) :
    ∀ᶠ t:ℝ in 𝓝 0,∀x∈K,f x=t → g x<C := by
  apply hK.eventually_forall_of_forall_eventually
  intro x hx
  by_cases hz:f x=0
  · have hh:∀ᶠ p:ℝ×E in 𝓝 (0,x),g p.2<C:=
      ((hg x hx).comp continuous_snd.continuousAt).eventually (gt_mem_nhds (hzero x hx hz))
    exact hh.mono fun p hp _=>hp
  · have hn:f x-(0:ℝ)≠0:=by simpa using hz
    have hh:∀ᶠ p:ℝ×E in 𝓝 (0,x),f p.2-p.1≠0:=
      (((hf x hx).comp continuous_snd.continuousAt).sub continuous_fst.continuousAt).eventually_ne hn
    exact hh.mono fun p hp he=>False.elim (hp (sub_eq_zero.mpr he))
end Bernoulli.Foliation

end
end

end OAI
end

section
-- module Solutions.OAIQW_BernoulliCone.ZeroTrace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Filter InnerProductSpace
open scoped Topology ContDiff
namespace Bernoulli.DeSilvaJerison
lemma exists_zero_upper_leaf {x:Space 7} (hq:0<Cylindrical.radiusSq axis x)
    (hz:Zsigned x<0) : ∃l:ℝ,0<l ∧ upperFamily l x=0 := by
  have hc:ContinuousAt (fun l:ℝ=>Zsigned x+capAmplitude*l^3*KSup x) 0:=by fun_prop
  have hp:Zsigned x+capAmplitude*(0:ℝ)^3*KSup x<0:=by simpa using hz
  have hn:∀ᶠ l:ℝ in 𝓝[>] 0,Zsigned x+capAmplitude*l^3*KSup x<0:=
    (hc.eventually (gt_mem_nhds hp)).filter_mono nhdsWithin_le_nhds
  have hqn:∀ᶠ l:ℝ in 𝓝[>] 0,l^2<Cylindrical.radiusSq axis x:=
    ((continuousAt_id.pow 2).eventually (gt_mem_nhds (by simpa using hq))).filter_mono nhdsWithin_le_nhds
  have hn0:∀ᶠ l:ℝ in 𝓝[>] 0,0<l:=self_mem_nhdsWithin
  obtain ⟨l,hl,hlq,hlp⟩:=(hn0.and (hqn.and hn)).exists
  refine ⟨l,hl,?_⟩
  rw [upperFamily_outer_formula hl hlq.le,max_eq_right hlp.le,mul_zero]
lemma upperParameter_compact_near_zero {x:Space 7} (hq:0<Cylindrical.radiusSq axis x)
    (hz:Zsigned x<0) : ∃a b:ℝ,0<a ∧ a≤b ∧
      ∀t:ℝ,0<t → t<1 → upperParameter x t∈Icc a b := by
  have hU:U x=0:=by rw [U_eq_signed_pospart hq,max_eq_right hz.le,mul_zero]
  obtain ⟨a,ha,hea⟩:=exists_zero_upper_leaf hq hz
  let b:=upperParameter x 1
  have ht:U x<1:=by rw [hU]; norm_num
  have hb:0<b:=(upperParameter_spec ht).1
  have hab:a<b:=(lt_upperParameter_iff ht ha).mpr (by rw [hea]; norm_num)
  refine ⟨a,b,ha,hab.le,?_⟩
  intro t ht0 ht1
  have hUt:U x<t:=by rwa [hU]
  refine ⟨((lt_upperParameter_iff hUt ha).mpr (by rwa [hea])).le,?_⟩
  apply le_of_lt ((upperParameter_lt_iff hUt hb).mpr _)
  change t<upperFamily (upperParameter x 1) x
  rw [(upperParameter_spec ht).2]
  exact ht1
lemma upperTrace_continuousAt (x:Space 7) {l:ℝ} (hl:0<l) :
    ContinuousAt (upperTrace x) l := by
  exact ((continuousAt_const.mul continuousAt_id).mul
    (upperSigned_continuous.continuousAt.comp
      ((continuousAt_id.inv₀ hl.ne').smul continuousAt_const)))
lemma gradient_smoothCap_continuousAt {y:Space 7} (hq:Cylindrical.radiusSq axis y≤1) :
    ContinuousAt (gradient smoothCap) y := by
  have hh:ContDiffAt ℝ ∞ (gradient smoothCap) y:=
    (toDual ℝ (Space 7)).symm.toContinuousLinearEquiv.contDiff.contDiffAt.comp y
      ((smoothCap_contDiffAt hq).fderiv_right (by simp))
  exact hh.continuousAt
lemma gradient_outerSigned_continuousAt {y:Space 7} (hq:1≤Cylindrical.radiusSq axis y) :
    ContinuousAt (gradient outerSigned) y := by
  obtain ⟨hy,ha⟩:=radiusSq_pos_data (show 0<Cylindrical.radiusSq axis y by linarith)
  have hh:ContDiffAt ℝ ∞ (gradient outerSigned) y:=
    (toDual ℝ (Space 7)).symm.toContinuousLinearEquiv.contDiff.contDiffAt.comp y
      ((outerSigned_contDiffAt (n:=∞) hy ha).fderiv_right (by simp))
  exact hh.continuousAt
lemma scaled_gradient_norm_sq_continuousAt (x:Space 7) {l:ℝ} (hl:0<l)
    {W:Space 7→Space 7} (hW:ContinuousAt W (l⁻¹ • x)) :
    ContinuousAt (fun s:ℝ=>‖κ • W (s⁻¹ • x)‖^2) l := by
  have hc:ContinuousAt (fun s:ℝ=>s⁻¹ • x) l:=
    (continuousAt_id.inv₀ hl.ne').smul continuousAt_const
  have hg:ContinuousAt (fun s:ℝ=>W (s⁻¹ • x)) l:=
    ContinuousAt.comp (f:=fun s:ℝ=>s⁻¹ • x) (g:=W) hW hc
  exact (hg.const_smul κ).norm.pow 2
lemma normalized_radiusSq_ge_one {x:Space 7} {l:ℝ} (hl:0<l)
    (hq:l^2≤Cylindrical.radiusSq axis x) : 1≤Cylindrical.radiusSq axis (l⁻¹ • x) := by
  rw [Cylindrical.radiusSq_smul,inv_pow,←div_eq_inv_mul,le_div_iff₀ (sq_pos_of_pos hl),one_mul]
  exact hq

theorem upperFlux_eventually_subunit {x:Space 7} (hq:0<Cylindrical.radiusSq axis x)
    (hz:Zsigned x<0) : ∀ᶠ t:ℝ in 𝓝[>] 0,‖upperFlux (x,t)‖^2<1 := by
  have hU:U x=0:=by rw [U_eq_signed_pospart hq,max_eq_right hz.le,mul_zero]
  obtain ⟨a,b,ha,hab,hpar⟩:=upperParameter_compact_near_zero hq hz
  let Kc:Set ℝ:=Icc a b ∩ {l|Cylindrical.radiusSq axis x≤l^2}
  let Ko:Set ℝ:=Icc a b ∩ {l|l^2≤Cylindrical.radiusSq axis x}
  have hKc:IsCompact Kc:=isCompact_Icc.inter_right (isClosed_le continuous_const (continuous_id.pow 2))
  have hKo:IsCompact Ko:=isCompact_Icc.inter_right (isClosed_le (continuous_id.pow 2) continuous_const)
  have hlc (l:ℝ)(hl:l∈Kc):0<l:=ha.trans_le hl.1.1
  have hlo (l:ℝ)(hl:l∈Ko):0<l:=ha.trans_le hl.1.1
  have hqc (l:ℝ)(hl:l∈Kc):Cylindrical.radiusSq axis (l⁻¹ • x)≤1:=
    (radiusSq_inv_smul_le_iff (hlc l hl) x).mpr hl.2
  have hqo (l:ℝ)(hl:l∈Ko):1≤Cylindrical.radiusSq axis (l⁻¹ • x):=
    normalized_radiusSq_ge_one (hlo l hl) hl.2
  have hs0(l:ℝ)(hl:0<l)(he:upperTrace x l=0):upperSigned (l⁻¹ • x)=0:=
    (mul_eq_zero.mp he).resolve_left (mul_pos κ_pos hl).ne'
  have hc:∀ᶠ t:ℝ in 𝓝 0,∀l∈Kc,upperTrace x l=t → ‖κ • gradient smoothCap (l⁻¹ • x)‖^2<1:=by
    apply Foliation.eventually_near_zero_fiber hKc
    · exact fun l hl=>upperTrace_continuousAt x (hlc l hl)
    · intro l hl
      exact scaled_gradient_norm_sq_continuousAt x (hlc l hl)
        (gradient_smoothCap_continuousAt (hqc l hl))
    · intro l hl he
      exact (upper_free_boundary_slopes (hs0 l (hlc l hl) he)).1 (hqc l hl)
  have ho:∀ᶠ t:ℝ in 𝓝 0,∀l∈Ko,upperTrace x l=t → ‖κ • gradient outerSigned (l⁻¹ • x)‖^2<1:=by
    apply Foliation.eventually_near_zero_fiber hKo
    · exact fun l hl=>upperTrace_continuousAt x (hlo l hl)
    · intro l hl
      exact scaled_gradient_norm_sq_continuousAt x (hlo l hl)
        (gradient_outerSigned_continuousAt (hqo l hl))
    · intro l hl he
      exact (upper_free_boundary_slopes (hs0 l (hlo l hl) he)).2 (hqo l hl)
  have htn:∀ᶠ t:ℝ in 𝓝[>] 0,t<1:=(gt_mem_nhds (by norm_num : (0:ℝ)<1)).filter_mono nhdsWithin_le_nhds
  filter_upwards [hc.filter_mono nhdsWithin_le_nhds,ho.filter_mono nhdsWithin_le_nhds,htn,self_mem_nhdsWithin] with t hct hot ht1 ht0
  have ht:U x<t:=by rwa [hU]
  have hl:0<upperParameter x t:=(upperParameter_spec ht).1
  have he:upperTrace x (upperParameter x t)=t := by
    have hh:=(upperParameter_spec ht).2
    rw [upperFamily_eq_max hl.le] at hh
    have hpos:0<upperTrace x (upperParameter x t):=by rw [←hh] at ht0; simpa using ht0
    rwa [max_eq_left hpos.le] at hh
  rw [upperFlux,ite_eq_left ht]
  split_ifs with hqc'
  · exact hct _ ⟨hpar t ht0 ht1,(radiusSq_inv_smul_le_iff hl x).mp hqc'⟩ he
  · have hqo':(upperParameter x t)^2≤Cylindrical.radiusSq axis x:=by
      have hh:¬Cylindrical.radiusSq axis x≤(upperParameter x t)^2:=by
        intro h; exact hqc' ((radiusSq_inv_smul_le_iff hl x).mpr h)
      exact (not_le.mp hh).le
    exact hot _ ⟨hpar t ht0 ht1,hqo'⟩ he
end Bernoulli.DeSilvaJerison

end
end

end OAI
end

section
-- module Solutions.OAIQW_BernoulliCone.TraceBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Filter InnerProductSpace MeasureTheory
open scoped Topology ContDiff
namespace Bernoulli.DeSilvaJerison

lemma radiusSq_zero_coordinate {x:Space 7} (hq:Cylindrical.radiusSq axis x=0) : x 0=0 := by
  have ht:Cylindrical.transverse axis x=0:=by
    have hh:=Cylindrical.transverse_sq axis x axis_norm
    rw [hq] at hh
    exact norm_eq_zero.mp (sq_eq_zero_iff.mp hh)
  have hh:=congrArg (fun y:Space 7=>y 0) ht
  simpa [Cylindrical.transverse,axis] using hh

lemma radiusSq_pos_ae : ∀ᵐ x:Space 7 ∂volume,0<Cylindrical.radiusSq axis x := by
  let e:Space 7:=EuclideanSpace.single 0 1
  let a:=innerSL ℝ e
  have he:e≠0:=by simp [e]
  have ha:a≠0:=by
    intro hh
    have hx:inner ℝ e e=0:=by
      have h:=congrArg (fun f:Space 7→L[ℝ]ℝ=>f e) hh
      simpa [a] using h
    exact he (inner_self_eq_zero.mp hx)
  have hker:volume (LinearMap.ker a.toLinearMap : Set (Space 7))=0:=by
    apply Measure.addHaar_submodule
    rw [Ne,LinearMap.ker_eq_top]
    intro hh
    exact ha (ContinuousLinearMap.coe_injective hh)
  have hne:∀ᵐ x:Space 7 ∂volume,x 0≠0:=by
    rw [ae_iff]
    change volume {x:Space 7 | inner ℝ e x=0}=0 at hker
    simpa [e,not_not,EuclideanSpace.inner_single_left] using hker
  filter_upwards [hne] with x hx
  exact lt_of_le_of_ne (Cylindrical.radiusSq_nonneg axis x axis_norm)
    (fun h=>hx (radiusSq_zero_coordinate h.symm))

lemma boundary_signed_slope {x:Space 7} (hq:0<Cylindrical.radiusSq axis x)
    (hz:Zsigned x=0) : ‖κ • gradient Zsigned x‖^2=1 := by
  obtain ⟨hx,ha⟩:=radiusSq_pos_data hq
  have hf:f (angle x)=0:=by
    rw [Zsigned_eq] at hz
    exact (mul_eq_zero.mp hz).resolve_left (norm_ne_zero_iff.mpr hx)
  have ht:|angle x|=t7:=root_unique ⟨abs_nonneg _,ha⟩ (by rwa [f_abs])
  rw [norm_smul,mul_pow,Real.norm_eq_abs,sq_abs,Zsigned_boundary_slope hx ht,κ_sq]

lemma boundary_outer_eventually {x:Space 7} (hq:0<Cylindrical.radiusSq axis x)
    (hz:Zsigned x=0) :
    ∀ᶠ t:ℝ in 𝓝[>] 0,(upperParameter x t)^2<Cylindrical.radiusSq axis x := by
  let l:=Real.sqrt (Cylindrical.radiusSq axis x)/2
  have hl:0<l:=by dsimp [l]; positivity
  have hlq:l^2<Cylindrical.radiusSq axis x:=by
    have hh:=Real.sq_sqrt hq.le
    dsimp [l]
    nlinarith
  obtain ⟨hx,ha⟩:=radiusSq_pos_data hq
  have hpos:0<capAmplitude*l^3*KSup x:=mul_pos (mul_pos capAmplitude_pos (pow_pos hl _)) (KSup_pos hx ha)
  have hF:0<upperFamily l x:=by
    rw [upperFamily_outer_formula hl hlq.le,hz,zero_add,max_eq_left hpos.le]
    exact mul_pos κ_pos hpos
  have hU:U x=0:=by rw [U_eq_signed_pospart hq,hz,max_self,mul_zero]
  have hn:∀ᶠ t:ℝ in 𝓝[>] 0,t<upperFamily l x:=
    (gt_mem_nhds hF).filter_mono nhdsWithin_le_nhds
  filter_upwards [hn,self_mem_nhdsWithin] with t ht ht0
  have htt:U x<t:=by rwa [hU]
  have hh:upperParameter x t<l:=(upperParameter_lt_iff htt hl).mpr ht
  exact ((sq_lt_sq₀ (upperParameter_spec htt).1.le hl.le).mpr hh).trans hlq

lemma upperFlux_boundary_trace {x:Space 7} (hq:0<Cylindrical.radiusSq axis x)
    (hz:Zsigned x=0) :
    Tendsto (fun t:ℝ=>upperFlux (x,t)) (𝓝[>] 0) (𝓝 (κ • gradient Zsigned x)) := by
  have hU:U x=0:=by rw [U_eq_signed_pospart hq,hz,max_self,mul_zero]
  have he:(fun t:ℝ=>upperFlux (x,t)) =ᶠ[𝓝[>] 0]
      (fun t=>κ • gradient Zsigned x+(t/KSup x) • gradient KSup x):=by
    filter_upwards [boundary_outer_eventually hq hz,self_mem_nhdsWithin] with t ht ht0
    rw [upperFlux_outer_affine (by rwa [hU]) ht,hz,mul_zero,sub_zero]
  apply Tendsto.congr' he.symm
  have hc:ContinuousAt (fun t:ℝ=>κ • gradient Zsigned x+(t/KSup x) • gradient KSup x) 0:=by fun_prop
  simpa only [zero_div,zero_smul,add_zero] using hc.tendsto.mono_left nhdsWithin_le_nhds

/-- Full zero-phase upper trace bound, including the conical boundary. Only
the null axis is excluded; no assertion about the boundary's measure is used. -/
theorem upperFlux_zero_trace_bound {x:Space 7} (hq:0<Cylindrical.radiusSq axis x)
    (hU:U x=0) {η:ℝ} (hη:0<η) :
    ∀ᶠ t:ℝ in 𝓝[>] 0,‖upperFlux (x,t)‖^2<1+η := by
  have hz:Zsigned x≤0:=by
    rw [U_eq_signed_pospart hq] at hU
    have hh:max (Zsigned x) 0=0:=(mul_eq_zero.mp hU).resolve_left κ_pos.ne'
    exact (le_max_left _ _).trans hh.le
  rcases hz.eq_or_lt with he|hl
  · have ht:=((upperFlux_boundary_trace hq he).norm.pow 2)
    rw [boundary_signed_slope hq he] at ht
    exact ht.eventually (gt_mem_nhds (by linarith : (1:ℝ)<1+η))
  · exact (upperFlux_eventually_subunit hq hl).mono fun _ h=>by linarith
end Bernoulli.DeSilvaJerison

end
end

end OAI
end

section
-- module Solutions.OAIQW_BernoulliCone.IntegratedPrimitive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Filter InnerProductSpace MeasureTheory
open scoped Topology ContDiff NNReal
namespace Bernoulli.DeSilvaJerison
open Foliation

lemma shiftU_lipschitz {K:ℝ≥0} (hK:LipschitzWith K U) (ε:ℝ) :
    LipschitzWith K (shiftU ε):=by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simpa only [shiftU,dist_add_right] using hK.dist_le_mul x y
lemma ceilingGraph_lipschitz {K L:ℝ≥0} {v:Space 7→ℝ}
    (hK:LipschitzWith K U) (hL:LipschitzWith L v) (ε:ℝ) :
    LipschitzWith (max K L) (ceilingGraph ε v):=(shiftU_lipschitz hK ε).max hL
lemma ceiling_eq_shift_outside {v:Space 7→ℝ} {ε:ℝ} (hε:0≤ε) {x:Space 7}
    (hx:x∉tsupport (fun y=>v y-U y)) : ceilingGraph ε v x=shiftU ε x := by
  have hv:v x=U x:=sub_eq_zero.mp (image_eq_zero_of_notMem_tsupport (f:=fun y=>v y-U y) hx)
  exact max_eq_left (by dsimp [shiftU]; rw [hv]; linarith)
lemma ceiling_sub_compact {v:Space 7→ℝ} {ε:ℝ} (hε:0≤ε)
    (hc:HasCompactSupport (fun y=>v y-U y)) :
    HasCompactSupport (fun x=>ceilingGraph ε v x-shiftU ε x) := by
  apply HasCompactSupport.intro hc
  intro x hx
  rw [ceiling_eq_shift_outside hε hx,sub_self]
lemma comparison_primitive_support {v:Space 7→ℝ} {ε:ℝ} (hε:0≤ε) :
    tsupport (verticalPotential upperFlux (shiftU ε) (ceilingGraph ε v))⊆tsupport (fun y=>v y-U y) := by
  apply closure_minimal _ (isClosed_tsupport _)
  intro x hx
  by_contra hn
  have he:=ceiling_eq_shift_outside hε hn
  exact hx (by simp [verticalPotential,he])
lemma comparison_primitive_compact {v:Space 7→ℝ} {ε:ℝ} (hε:0≤ε)
    (hc:HasCompactSupport (fun y=>v y-U y)) :
    HasCompactSupport (verticalPotential upperFlux (shiftU ε) (ceilingGraph ε v)) :=
  hc.of_isClosed_subset (isClosed_tsupport _) (comparison_primitive_support hε)

lemma shiftU_gradient {ε:ℝ} {x:Space 7} (hx:DifferentiableAt ℝ U x) :
    gradient (shiftU ε) x=gradient U x := by
  have hd:HasFDerivAt (shiftU ε) (fderiv ℝ U x) x:=hx.hasFDerivAt.add_const ε
  unfold gradient
  rw [hd.fderiv]
lemma ceilingGraph_gradient {ε:ℝ} {v:Space 7→ℝ} {x:Space 7}
    (hv:ContinuousAt v x) (hlt:U x+ε<v x) :
    gradient (ceilingGraph ε v) x=gradient v x := by
  have he:ceilingGraph ε v =ᶠ[𝓝 x] v:=by
    filter_upwards [(U_continuous.continuousAt.add_const ε).eventually_lt hv hlt] with y hy
    exact max_eq_right hy.le
  unfold gradient
  rw [he.fderiv_eq]

lemma comparisonR_ae_bound {v:Space 7→ℝ} {L:ℝ≥0} (hv:LipschitzWith L v)
    {ε:ℝ} (hε:0<ε) (hc:HasCompactSupport (fun y=>v y-U y)) :
    ∀ᵐ x:Space 7 ∂volume,
      divergence (verticalPotential upperFlux (shiftU ε) (ceilingGraph ε v)) x≤comparisonR ε v x := by
  obtain ⟨K,hK⟩:=exists_lipschitz_U
  have ha:=shiftU_lipschitz hK ε
  have hb:=ceilingGraph_lipschitz hK hv ε
  obtain ⟨M,hM⟩:=clamped_seam_lipschitz ha hb (fun x=>by dsimp [shiftU]; linarith)
    (ceiling_sub_compact hε.le hc)
  filter_upwards [radiusSq_pos_ae,hK.ae_differentiableAt,ha.ae_differentiableAt,
    hb.ae_differentiableAt,hM.ae_differentiableAt] with x hqx hdu hda hdb hdw
  have h:=upperFlux_primitive_bound ha.continuous.continuousAt hb.continuous.continuousAt
    (fun y=>le_max_left _ _) (by dsimp [shiftU]; linarith) hqx hda hdb hdw
  rw [shiftU_gradient hdu] at h
  by_cases hlt:U x+ε<v x
  · have hh:shiftU ε x<ceilingGraph ε v x:=(lt_max_iff.mpr (Or.inr hlt))
    rw [ite_eq_left hh,ceilingGraph_gradient hv.continuous.continuousAt hlt] at h
    simpa only [shiftU,comparisonR,ite_eq_left hlt] using h
  · have hh:¬shiftU ε x<ceilingGraph ε v x:=by
      simpa only [ceilingGraph,shiftU,lt_max_iff,lt_self_iff_false,false_or] using hlt
    simpa only [ite_eq_right hh,comparisonR,ite_eq_right hlt] using h

lemma comparisonR_measurable {v:Space 7→ℝ} (hv:Measurable v) (ε:ℝ):
    Measurable (comparisonR ε v) := by
  have hA:Measurable (fun x:Space 7=>upperFlux (x,U x+ε)):=
    upperFlux_measurable.comp (measurable_id.prodMk (U_continuous.measurable.add_const ε))
  exact ((LipschitzSobolev.measurable_gradient.norm.pow_const 2 |>.add (hA.norm.pow_const 2)).sub
    ((hA.inner LipschitzSobolev.measurable_gradient).const_mul 2)).ite
      (measurableSet_lt (U_continuous.measurable.add_const ε) hv) measurable_const

lemma comparisonR_bound {v:Space 7→ℝ} {K L:ℝ≥0} (hK:LipschitzWith K U)
    (hL:LipschitzWith L v) {C:ℝ} (hC:0≤C) (hA:∀p:Space 7×ℝ,‖upperFlux p‖≤C) (ε:ℝ) (x:Space 7):
    ‖comparisonR ε v x‖≤(L:ℝ)^2+C^2+2*C*K := by
  unfold comparisonR
  split_ifs
  · have h1:‖gradient v x‖^2≤(L:ℝ)^2:=sq_le_sq₀ (norm_nonneg _) L.2 |>.mpr (LipschitzSobolev.norm_gradient_le hL x)
    have h2:‖upperFlux (x,U x+ε)‖^2≤C^2:=sq_le_sq₀ (norm_nonneg _) hC |>.mpr (hA _)
    have h3:‖inner ℝ (upperFlux (x,U x+ε)) (gradient U x)‖≤C*K:=
      (norm_inner_le_norm _ _).trans (mul_le_mul (hA _) (LipschitzSobolev.norm_gradient_le hK x) (norm_nonneg _) hC)
    calc
      _ ≤ ‖(‖gradient v x‖^2+‖upperFlux (x,U x+ε)‖^2)‖+‖2*inner ℝ (upperFlux (x,U x+ε)) (gradient U x)‖:=norm_sub_le _ _
      _ ≤ (L:ℝ)^2+C^2+2*C*K:=by
        rw [Real.norm_eq_abs,abs_of_nonneg (add_nonneg (sq_nonneg _) (sq_nonneg _)),norm_mul]
        norm_num only [Real.norm_ofNat]
        nlinarith
  · simp only [norm_zero]; positivity

/-- The genuine compact graph primitive yields an integrated comparison at
positive height. Hypotheses concern a competitor, never desired minimality. -/
theorem comparisonR_integral_nonneg {v:Space 7→ℝ} {L:ℝ≥0} (hv:LipschitzWith L v)
    {ε:ℝ} (hε:0<ε) (hc:HasCompactSupport (fun y=>v y-U y))
    {c:Space 7} {r:ℝ} (hS:tsupport (fun y=>v y-U y)⊆Metric.ball c r) :
    0≤∫x in Metric.ball c r,comparisonR ε v x := by
  let P:=verticalPotential upperFlux (shiftU ε) (ceilingGraph ε v)
  obtain ⟨K,hK⟩:=exists_lipschitz_U
  have hPc:HasCompactSupport P:=comparison_primitive_compact hε.le hc
  have hPl:LocallyLipschitz P:=upperFlux_primitive_locallyLipschitz
    (shiftU_lipschitz hK ε).locallyLipschitz (ceilingGraph_lipschitz hK hv ε).locallyLipschitz
    (fun x=>le_max_left _ _) (fun x=>by dsimp [shiftU]; linarith)
  obtain ⟨M,hM⟩:=locallyLipschitz_compact_lipschitz hPl hPc
  obtain ⟨C,hC,hA⟩:=upperFlux_uniform_bound
  have hR:IntegrableOn (comparisonR ε v) (Metric.ball c r):=
    (integrableOn_const (μ:=volume) (C:=(L:ℝ)^2+C^2+2*C*K) (measure_ball_lt_top.ne)).mono'
      (comparisonR_measurable hv.continuous.measurable ε).aestronglyMeasurable.restrict
      (Eventually.of_forall (comparisonR_bound hK hv hC.le hA ε))
  have hz:(∫x in Metric.ball c r,divergence P x)=0:=by
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx=>
      divergence_zero_outside_support (fun hp=>hx (hS (comparison_primitive_support hε.le hp))))]
    exact integral_divergence_compact hM hPc
  rw [←hz]
  exact integral_mono_ae (integrable_divergence_compact hM hPc).integrableOn hR
    ((comparisonR_ae_bound hv hε hc).filter_mono (ae_mono Measure.restrict_le_self))
end Bernoulli.DeSilvaJerison

end
end

end OAI
end

section
-- module Solutions.OAIQW_BernoulliCone.IntegralUpperLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uα

section
noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace Bernoulli
open scoped _root_.Bernoulli

theorem integral_nonneg_of_dominated_upper_limit {α : Type uα} [MeasurableSpace α]
    {μ:Measure α} {R:ℕ→α→ℝ} {D C:α→ℝ}
    (hR:∀n,Integrable (R n) μ) (hD:Integrable D μ) (hC:Integrable C μ)
    (hbound:∀n,∀ᵐ x ∂μ,‖R n x‖≤C x)
    (hpos:∀n,0≤∫x,R n x ∂μ)
    (hlim:∀ᵐ x ∂μ,∀η:ℝ,0<η → ∀ᶠ n in atTop,R n x<D x+η) :
    0≤∫x,D x ∂μ := by
  let E:=fun n x=>max (R n x-D x) 0
  have hEn n:∫x,E n x ∂μ≥0:=integral_nonneg (fun x=>le_max_right _ _)
  have hEb n:∀ᵐ x ∂μ,‖E n x‖≤C x+‖D x‖:=by
    filter_upwards [hbound n] with x hx
    rw [Real.norm_eq_abs,abs_of_nonneg (le_max_right _ _)]
    apply max_le
    · calc
        R n x-D x ≤ ‖R n x-D x‖ := le_abs_self _
        _ ≤ ‖R n x‖+‖D x‖ := norm_sub_le _ _
        _ ≤ C x+‖D x‖ := add_le_add hx le_rfl
    · exact add_nonneg ((norm_nonneg _).trans hx) (norm_nonneg _)
  have hEi n:Integrable (E n) μ:=
    (hC.add hD.norm).mono' (((hR n).aestronglyMeasurable.aemeasurable.sub hD.aestronglyMeasurable.aemeasurable).max aemeasurable_const).aestronglyMeasurable (hEb n)
  have hEc:∀ᵐ x ∂μ,Tendsto (fun n=>E n x) atTop (𝓝 0):=by
    filter_upwards [hlim] with x hx
    apply tendsto_order.2
    constructor
    · intro a ha
      exact Eventually.of_forall fun n=>ha.trans_le (le_max_right _ _)
    · intro b hb
      exact (hx b hb).mono fun n hn=>max_lt (by linarith) hb
  have ht:Tendsto (fun n=>∫x,E n x ∂μ) atTop (𝓝 0):=by
    simpa using tendsto_integral_of_dominated_convergence (C+fun x=>‖D x‖)
      (fun n=>(hEi n).aestronglyMeasurable) (hC.add hD.norm) hEb hEc
  have hi n:0≤(∫x,D x ∂μ)+(∫x,E n x ∂μ):=by
    rw [←integral_add hD (hEi n)]
    refine (hpos n).trans (integral_mono_ae (hR n) (hD.add (hEi n)) ?_)
    filter_upwards [] with x
    have hh:=le_max_left (R n x-D x) 0
    change R n x≤D x+max (R n x-D x) 0
    linarith
  have h:=ge_of_tendsto (tendsto_const_nhds.add ht) (Eventually.of_forall hi)
  simpa using h
end Bernoulli

end
end

end OAI
end

section
-- module Solutions.OAIQW_BernoulliCone.UpperLipschitzComparison
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Filter InnerProductSpace MeasureTheory
open scoped Topology ContDiff NNReal
namespace Bernoulli.DeSilvaJerison
open Foliation

lemma comparisonR_upper_limit {v:Space 7→ℝ} {x:Space 7}
    (hdu:DifferentiableAt ℝ U x) (hdv:DifferentiableAt ℝ v x)
    (hUv:∀y,U y≤v y) (hq:0<Cylindrical.radiusSq axis x)
    {ε:ℕ→ℝ} (hε:∀n,0<ε n) (hεt:Tendsto ε atTop (𝓝 0))
    {η:ℝ} (hη:0<η) : ∀ᶠ n in atTop,comparisonR (ε n) v x<energyDifference v x+η := by
  rcases (hUv x).eq_or_lt with he|hl
  · have hg:=gradient_eq_of_order_contact hdu hdv hUv he
    have hd:energyDifference v x=0:=by simp [energyDifference,←he,←hg]
    filter_upwards [] with n
    have hn:¬U x+ε n<v x:=by rw [←he]; linarith [hε n]
    simpa only [comparisonR,ite_eq_right hn,hd,zero_add] using hη
  · have hvp:0<v x:=(U_nonneg x).trans_lt hl
    have hheight:Tendsto (fun n=>U x+ε n) atTop (𝓝[>] U x):=by
      rw [tendsto_nhdsWithin_iff]
      exact ⟨by simpa using tendsto_const_nhds.add hεt,
        Eventually.of_forall (fun n=>by change U x<U x+ε n; linarith [hε n])⟩
    have hlt:∀ᶠ n in atTop,U x+ε n<v x:=
      (by simpa using tendsto_const_nhds.add hεt : Tendsto (fun n=>U x+ε n) atTop (𝓝 (U x))).eventually (gt_mem_nhds hl)
    rcases (U_nonneg x).eq_or_lt with he0|hp
    · have hu0:U x=0:=he0.symm
      have hg:gradient U x=0:=by
        have hh:=gradient_eq_of_order_contact (differentiableAt_const (c:=(0:ℝ))) hdu U_nonneg he0
        simpa only [gradient_fun_const] using hh.symm
      have hεw:Tendsto ε atTop (𝓝[>] (0:ℝ)):=by
        rw [tendsto_nhdsWithin_iff]
        exact ⟨hεt,Eventually.of_forall hε⟩
      have hn:=hεw.eventually (upperFlux_zero_trace_bound hq hu0 hη)
      filter_upwards [hn,hlt] with n hn hlt
      rw [comparisonR,ite_eq_left hlt]
      simp only [energyDifference,hu0,hg,norm_zero,zero_pow (by norm_num:2≠0),
        ite_eq_left hvp,lt_self_iff_false,ite_false,zero_add,inner_zero_right,mul_zero,sub_zero]
      linarith
    · have hA:Tendsto (fun n=>upperFlux (x,U x+ε n)) atTop (𝓝 (gradient U x)):=
        (upperFlux_tendsto_positive_trace hp).comp hheight
      have ht:Tendsto (fun n=>‖gradient v x‖^2+‖upperFlux (x,U x+ε n)‖^2-
          2*inner ℝ (upperFlux (x,U x+ε n)) (gradient U x)) atTop
          (𝓝 (energyDifference v x)):=by
        have hvc:Tendsto (fun _n:ℕ=>‖gradient v x‖^2) atTop (𝓝 (‖gradient v x‖^2)):=tendsto_const_nhds
        have hgc:Tendsto (fun _n:ℕ=>gradient U x) atTop (𝓝 (gradient U x)):=tendsto_const_nhds
        have hh:=(hvc.add (hA.norm.pow 2)).sub ((hA.inner hgc).const_mul 2)
        convert hh using 1
        simp only [energyDifference,ite_eq_left hp,ite_eq_left hvp,real_inner_self_eq_norm_sq]
        ring_nf
      have hn:=ht.eventually (gt_mem_nhds (by linarith : energyDifference v x<energyDifference v x+η))
      filter_upwards [hn,hlt] with n hn hlt
      simpa only [comparisonR,ite_eq_left hlt] using hn

/-- Actual one-sided global energy comparison for every Lipschitz compact
upper perturbation. All flux/slopes have been constructed explicitly. -/
theorem U_upper_lipschitz_comparison_oai {v:Space 7→ℝ} {L:ℝ≥0}
    (hv:LipschitzWith L v) (hUv:∀x,U x≤v x)
    (hc:HasCompactSupport (fun y=>v y-U y))
    {c:Space 7} {r:ℝ} (hS:tsupport (fun y=>v y-U y)⊆Metric.ball c r) :
    energy (Metric.ball c r) U (gradient U)≤energy (Metric.ball c r) v (gradient v) := by
  let B:=Metric.ball c r
  let μ:=volume.restrict B
  let :IsFiniteMeasure μ:=isFiniteMeasure_restrict.mpr measure_ball_lt_top.ne
  obtain ⟨K,hK⟩:=exists_lipschitz_U
  obtain ⟨C,hC,hA⟩:=upperFlux_uniform_bound
  let ε:ℕ→ℝ:=fun n=>1/((n:ℝ)+1)
  have hε(n:ℕ):0<ε n:=by dsimp [ε]; positivity
  have hεt:Tendsto ε atTop (𝓝 0):=tendsto_one_div_add_atTop_nhds_zero_nat
  have huH:=LipschitzSobolev.h1_ball hK c r
  have hvH:=LipschitzSobolev.h1_ball hv c r
  have huI:Integrable (fun x=>‖gradient U x‖^2+if 0<U x then (1:ℝ) else 0) μ:=
    (huH.2.1.integrable_norm_pow (by norm_num)).add (integrable_phase huH.1.aestronglyMeasurable)
  have hvI:Integrable (fun x=>‖gradient v x‖^2+if 0<v x then (1:ℝ) else 0) μ:=
    (hvH.2.1.integrable_norm_pow (by norm_num)).add (integrable_phase hvH.1.aestronglyMeasurable)
  have hRi(n:ℕ):Integrable (comparisonR (ε n) v) μ:=
    (integrable_const ((L:ℝ)^2+C^2+2*C*K)).mono'
      (comparisonR_measurable hv.continuous.measurable (ε n)).aestronglyMeasurable
      (Eventually.of_forall (comparisonR_bound hK hv hC.le hA (ε n)))
  have hlim:∀ᵐ x ∂μ,∀η:ℝ,0<η → ∀ᶠ n in atTop,
      comparisonR (ε n) v x<energyDifference v x+η:=by
    have hh:∀ᵐ x:Space 7 ∂volume,∀η:ℝ,0<η → ∀ᶠ n in atTop,
        comparisonR (ε n) v x<energyDifference v x+η:=by
      filter_upwards [hK.ae_differentiableAt,hv.ae_differentiableAt,radiusSq_pos_ae] with x hdu hdv hqx η hη
      exact comparisonR_upper_limit hdu hdv hUv hqx hε hεt hη
    exact hh.filter_mono (ae_mono Measure.restrict_le_self)
  have hi:=integral_nonneg_of_dominated_upper_limit hRi (hvI.sub huI)
    (integrable_const ((L:ℝ)^2+C^2+2*C*K))
    (fun n=>Eventually.of_forall (comparisonR_bound hK hv hC.le hA (ε n)))
    (fun n=>comparisonR_integral_nonneg hv (hε n) hc hS) hlim
  change 0≤∫x,energyDifference v x ∂μ at hi
  rw [show energyDifference v=(fun x=>(‖gradient v x‖^2+if 0<v x then (1:ℝ) else 0)-
    (‖gradient U x‖^2+if 0<U x then (1:ℝ) else 0)) from rfl,integral_sub hvI huI] at hi
  exact sub_nonneg.mp hi
end Bernoulli.DeSilvaJerison

end
end

end OAI
end

theorem solution : type_of% @OAI.Bernoulli.DeSilvaJerison.U_upper_lipschitz_comparison_oai := @OAI.Bernoulli.DeSilvaJerison.U_upper_lipschitz_comparison_oai
