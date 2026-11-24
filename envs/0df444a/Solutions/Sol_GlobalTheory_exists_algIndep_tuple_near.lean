-- Prove2me | solution 1 for GlobalTheory.exists_algIndep_tuple_near
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:44:52.333377+00:00
-- url     : https://prove2.me/submissions/77ea465c-32ea-4e1d-a8b0-55ccd49863a7

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ValuationResidueLemmas
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_AlgebraMapOLInjective
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_NormOrderStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_CastAddNeNatAdd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_DenseMvPolynomialEvalNeZero
import Theorems.Thm_GlobalTheory_dense_mvPolynomial_eval_ne_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_NPB_gpt_succ
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_NPB_gpt_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_NPB_hImg_succ
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_NPB_hImg_zero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.ChartRestriction.G.T0.NPB.gpt_succ
attribute [local simp] ReciprocityTheory.ChartRestriction.G.T0.NPB.gpt_zero
attribute [local simp] ReciprocityTheory.ChartRestriction.G.T0.NPB.hImg_succ
attribute [local simp] ReciprocityTheory.ChartRestriction.G.T0.NPB.hImg_zero



set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.T0
open scoped TensorProduct
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    ∀ (K : Type) [Field K] [Countable K] (sg : K →+* ℂ) (D : ℕ) (z₀ : Fin D → ℂ) (ε : ℝ), 0 < ε → ∃ z : Fin D → ℂ, (∀ i, ‖z i - z₀ i‖ < ε) ∧ ∀ p : MvPolynomial (Fin D) K, p ≠ 0 → MvPolynomial.eval₂ sg z p ≠ 0 := by
  intro K _ _ sg D z₀ ε hε
  let S : {p : MvPolynomial (Fin D) K // p ≠ 0} → Set (Fin D → ℂ) :=
    fun p => {z | MvPolynomial.eval z (MvPolynomial.map sg p.1) ≠ 0}
  have : Countable (MvPolynomial (Fin D) K) := by
    refine Function.Surjective.countable (f := fun l : List ((Fin D →₀ ℕ) × K) =>
      (l.map fun mc => MvPolynomial.monomial mc.1 mc.2).sum) fun p => ?_
    refine ⟨p.support.toList.map fun m => (m, MvPolynomial.coeff m p), ?_⟩
    simp only [List.map_map]
    rw [Finset.sum_map_toList]
    exact p.as_sum.symm
  have hS : Dense (⋂ p, S p) := by
    apply dense_iInter_of_isOpen
    · intro p
      exact isOpen_ne_fun (MvPolynomial.continuous_eval _) continuous_const
    · intro p
      refine dense_mvPolynomial_eval_ne_zero _ fun h0 => p.2 ?_
      exact MvPolynomial.map_injective sg sg.injective (h0.trans (map_zero _).symm)
  obtain ⟨z, hzS, hz⟩ := hS.exists_mem_open (Metric.isOpen_ball (x := z₀)) (Metric.nonempty_ball.mpr hε)
  refine ⟨z, ?_, fun p hp => ?_⟩
  · rw [Metric.mem_ball, dist_pi_lt_iff hε] at hz
    intro i
    rw [← dist_eq_norm]
    exact hz i
  · rw [← MvPolynomial.eval_map]
    exact Set.mem_iInter.mp hzS ⟨p, hp⟩
end GlobalTheory
