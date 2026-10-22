-- Prove2me | solution 1 for JHolomorphic.contDiffOn_of_isWeakJHolomorphicOn
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-21T12:03:26.514372+00:00
-- url     : https://prove2.me/submissions/077b2f70-cacc-4ff1-b043-ee7cfe2f609c

import Definitions.Def_JHolomorphic_Setting
import Theorems.Thm_JHolomorphic_isAlmostComplexOn_tangent
import Theorems.Thm_JHolomorphic_tangent_isWeakJHolomorphicOn
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Normed.Operator.Bilinear



namespace JHolomorphic

open MeasureTheory
open scoped ContDiff

universe w

theorem contDiffOn_nat_of_isWeakJHolomorphicOn_aux (n : ℕ) :
    ∀ (E : Type w) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
      (p : ℝ) (_ : 2 < p) (J : E → E →L[ℝ] E) (O : Set E) (_ : IsAlmostComplexOn J O)
      (U : Set ℂ) (_ : IsOpen U) (u : ℂ → E) (_ : IsWeakJHolomorphicOn p J O U u),
      ContDiffOn ℝ n u U := by
  induction n with
  | zero =>
    intro E _ _ _ p hp J O hJ U hU u hu
    exact contDiffOn_zero.mpr hu.1
  | succ n ih =>
    intro E _ _ _ p hp J O hJ U hU u hu
    obtain ⟨hhol, hw⟩ := tangent_isWeakJHolomorphicOn p hp J O hJ U hU u hu
    have hwC := ih (E × E) p hp _ _ (isAlmostComplexOn_tangent J O hJ) U hU _ hw
    have hu1 : ContDiffOn ℝ n u U := hwC.fst
    have hv : ContDiffOn ℝ n (fun z => fderiv ℝ u z 1) U := hwC.snd
    have hJu : ContDiffOn ℝ n (fun z => J (u z)) U :=
      (hJ.2.1.of_le (by exact_mod_cast le_top)).comp hu1 hu.2.1
    -- `Du(z) = re ⊗ ∂ₛu + im ⊗ J(u) ∂ₛu`
    have hD : ∀ z ∈ U, fderiv ℝ u z =
        ContinuousLinearMap.smulRightL ℝ ℂ E Complex.reCLM (fderiv ℝ u z 1) +
          ContinuousLinearMap.smulRightL ℝ ℂ E Complex.imCLM (J (u z) (fderiv ℝ u z 1)) := by
      intro z hz
      have h0 := (hhol z hz).2
      have hJJ := congrArg (fun L => L (fderiv ℝ u z Complex.I)) (hJ.2.2 (u z) (hu.2.1 hz))
      simp only [ContinuousLinearMap.coe_comp', Function.comp_apply,
        ContinuousLinearMap.neg_apply, ContinuousLinearMap.id_apply] at hJJ
      have hI : fderiv ℝ u z Complex.I = J (u z) (fderiv ℝ u z 1) := by
        unfold dbarJ at h0
        have h1 := congrArg (J (u z)) h0
        rw [map_add, hJJ, map_zero] at h1
        rw [← sub_eq_add_neg, sub_eq_zero] at h1
        exact h1.symm
      refine ContinuousLinearMap.ext fun w => ?_
      have hw' : w = w.re • (1 : ℂ) + w.im • Complex.I := by
        apply Complex.ext <;> simp
      conv_lhs => rw [hw', map_add, map_smul, map_smul]
      simp [hI]
    rw [show ((n + 1 : ℕ) : WithTop ℕ∞) = (n : WithTop ℕ∞) + 1 by push_cast; rfl,
      contDiffOn_succ_iff_fderiv_of_isOpen hU]
    refine ⟨fun z hz => (hhol z hz).1.differentiableWithinAt, fun h => ?_, ?_⟩
    · exact absurd h (by simp)
    · refine ContDiffOn.congr ?_ hD
      exact (((ContinuousLinearMap.smulRightL ℝ ℂ E Complex.reCLM).contDiff.comp_contDiffOn hv).add
        ((ContinuousLinearMap.smulRightL ℝ ℂ E Complex.imCLM).contDiff.comp_contDiffOn
          (hJu.clm_apply hv)))

end JHolomorphic

open JHolomorphic

open MeasureTheory Metric Filter Topology DbarRegularity
open scoped ContDiff ENNReal NNReal

theorem solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] (p : ℝ) (hp : 2 < p)
    (J : E → E →L[ℝ] E) (O : Set E) (hJ : IsAlmostComplexOn J O) (U : Set ℂ) (hU : IsOpen U)
    (u : ℂ → E) (hu : IsWeakJHolomorphicOn p J O U u) :
    ContDiffOn ℝ ∞ u U :=
  contDiffOn_infty.mpr fun n => JHolomorphic.contDiffOn_nat_of_isWeakJHolomorphicOn_aux n E p hp J O hJ U hU u hu
