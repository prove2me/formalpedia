-- Prove2me | solution 1 for OAI.Bernoulli.nonflat_in_seven
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-23T21:36:22.578991+00:00
-- url     : https://prove2.me/submissions/c61a76a9-492e-4719-8608-f9883b13eb0b

import Mathlib
import Definitions.Def_BernoulliNonflatInSeven
import Definitions.Def_OAIQWBNS000
import Theorems.Thm_OAI_Bernoulli_DeSilvaJerison_U_global_minimizer

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

lemma p_neg (t : ℝ) : p (-t) = p t := by simp only [p, abs_neg]

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

end Bernoulli.DeSilvaJerison

/-! The concrete seven-dimensional cone belonging to the De Silva–Jerison profile.
These are actual function/Sobolev constructions, not an assumption of minimality. -/
namespace Bernoulli.DeSilvaJerison

lemma Z_le_norm (x : Space 7) : Z x ≤ ‖x‖ := by
  calc Z x ≤ ‖x‖ * 1 := mul_le_mul_of_nonneg_left (p_le_one _) (norm_nonneg x)
    _ = _ := mul_one _
lemma U_even (x : Space 7) : U (-x) = U x := by
  simp only [U,Z,norm_neg,PiLp.neg_apply,neg_div,p_neg]

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

lemma U_smul (r : ℝ) (hr : 0<r) (x : Space 7) : U (r • x) = r * U x := by
  simp only [U,Z,norm_smul,Real.norm_eq_abs,abs_of_pos hr,PiLp.smul_apply,smul_eq_mul,
    mul_div_mul_left _ _ (ne_of_gt hr)]
  ring

theorem U_homogeneous : OneHomogeneous U := by
  intro r hr
  exact Filter.Eventually.of_forall (U_smul r hr)

/-- Values in every direction perpendicular to the symmetry axis are positive. -/
lemma U_of_coordinate_zero {x : Space 7} (hx : x 6=0) : U x = κ*‖x‖ := by
  simp [U,Z,hx]

theorem U_nonzero : Nonzero U := by
  intro h
  have he := congrFun (MeasureTheory.Measure.eq_of_ae_eq h U_continuous continuous_const)
    (EuclideanSpace.single 0 (1:ℝ) : Space 7)
  have hv : U (EuclideanSpace.single 0 (1:ℝ)) = κ := by
    rw [U_of_coordinate_zero (by simp)]
    simp
  rw [hv] at he
  exact (ne_of_gt κ_pos) he

theorem U_not_flat : ¬ Flat U := by
  rintro ⟨e,he,hae⟩
  have hc : Continuous (fun x : Space 7 => max (inner ℝ x e) 0) := by fun_prop
  have heq := MeasureTheory.Measure.eq_of_ae_eq hae U_continuous hc
  have hp := congrFun heq e
  have hn := congrFun heq (-e)
  rw [U_even] at hn
  rw [real_inner_self_eq_norm_sq,he] at hp
  rw [inner_neg_left,real_inner_self_eq_norm_sq,he] at hn
  norm_num at hp hn
  linarith

end Bernoulli.DeSilvaJerison

/-! Euclidean calculus for the actual De Silva–Jerison axisymmetric construction.
No free-boundary or variational conclusion is built into these definitions. -/
end
end
end

end OAI
end

section
-- module Solutions.OAIQW_BernoulliCone.GlobalMinimizer
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

theorem exists_nonflat_dimension_seven :
    ∃u:Space 7→ℝ,GlobalMinimizer u ∧ Nonzero u ∧ OneHomogeneous u ∧ ¬Flat u :=
  ⟨U,U_global_minimizer,U_nonzero,U_homogeneous,U_not_flat⟩
end Bernoulli.DeSilvaJerison

end
end

end OAI
end

section
-- module Solutions.OAIQW_BernoulliCone.Main
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace Bernoulli
open scoped _root_.Bernoulli

theorem nonflat_in_seven_oai : ∃ u : Space 7 → ℝ,
    GlobalMinimizer u ∧ Nonzero u ∧ OneHomogeneous u ∧ ¬ Flat u :=
  DeSilvaJerison.exists_nonflat_dimension_seven
end Bernoulli

end
end

end OAI
end

theorem solution : type_of% @OAI.Bernoulli.nonflat_in_seven_oai := @OAI.Bernoulli.nonflat_in_seven_oai
