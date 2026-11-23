-- Prove2me | solution 1 for GlobalTheory.AppellHumbertTrivial.eq_zero_of_gaussian_decay
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:35:21.760129+00:00
-- url     : https://prove2.me/submissions/001d37bb-5624-4140-9294-b693389f6006

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_AppellHumbertTrivialOfNowhereVanishing

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory
open GlobalTheory.AppellHumbertTrivial
namespace GlobalTheory.AppellHumbertTrivial
namespace _root_.GlobalTheory.AppellHumbertTrivial
theorem _root_.solution (f : ℂ → ℂ) (hf : Differentiable ℂ f) (C a : ℝ) (ha : a < 0)
    (h : ∀ t, ‖f t‖ ≤ C * Real.exp (‖t‖ ^ 2 * a)) : f 0 = 0 := by
  have hbd : Bornology.IsBounded (Set.range f) := by
    rw [isBounded_iff_forall_norm_le]
    refine ⟨max C 0, ?_⟩
    rintro _ ⟨t, rfl⟩
    have he : Real.exp (‖t‖ ^ 2 * a) ≤ 1 :=
      Real.exp_le_one_iff.2 (mul_nonpos_of_nonneg_of_nonpos (by positivity) ha.le)
    have hp := Real.exp_pos (‖t‖ ^ 2 * a)
    refine (h t).trans ?_
    rcases le_or_gt 0 C with hC | hC
    · exact (mul_le_of_le_one_right hC he).trans (le_max_left _ _)
    · nlinarith [le_max_right C 0]
  have hconst : ∀ t, f 0 = f t := fun t => hf.apply_eq_apply_of_bounded hbd 0 t
  have h1 : Filter.Tendsto (fun n : ℕ => (n : ℝ) ^ 2 * a) Filter.atTop Filter.atBot :=
    ((Filter.tendsto_pow_atTop two_ne_zero).comp tendsto_natCast_atTop_atTop).atTop_mul_const_of_neg ha
  have hlim : Filter.Tendsto (fun n : ℕ => C * Real.exp ((n : ℝ) ^ 2 * a)) Filter.atTop
      (nhds 0) := by
    simpa using (Real.tendsto_exp_atBot.comp h1).const_mul C
  have hle : ∀ n : ℕ, ‖f 0‖ ≤ C * Real.exp ((n : ℝ) ^ 2 * a) := fun n => by
    rw [hconst (n : ℂ)]
    simpa using h (n : ℂ)
  exact norm_le_zero_iff.1 (ge_of_tendsto' hlim hle)
end _root_.GlobalTheory.AppellHumbertTrivial
end GlobalTheory.AppellHumbertTrivial
