-- Prove2me | solution 1 for GlobalTheory.IsogenySum.eq_zero_of_im_lattice
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T01:21:37.950918+00:00
-- url     : https://prove2.me/submissions/f0f81de9-a31f-4eed-8b06-c545d06066dd

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_FockTranslationLaws
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_IntegrableOnFundamentalDomainOfContinuous
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ContinuousThetaSectionPointwiseNormSq
import Theorems.Thm_GlobalTheory_FockTranslation_herm_add_left
import Theorems.Thm_GlobalTheory_FockTranslation_herm_self_re


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open Complex ReciprocityTheory.ChartRestriction.G.I2 MeasureTheory
open GlobalTheory.IsogenySum
open FockTranslation
variable {ι : Type} [Fintype ι]
namespace GlobalTheory.IsogenySum
theorem _root_.solution (Y : GT ι) {a : EuclideanSpace ℂ ι}
    (h : ∀ y ∈ lat Y.b, (Hf y a).im = 0) : a = 0 := by
  have hspan : ∀ v, (Hf v a).im = 0 := by
    intro v
    have hv : v ∈ Submodule.span ℝ (Set.range Y.b) := by
      rw [Y.b.span_eq]; exact Submodule.mem_top
    induction hv using Submodule.span_induction with
    | mem x hx => exact h x (Submodule.subset_span hx)
    | zero => simp [Hf]
    | add x y _ _ hx hy => rw [herm_add_left, Complex.add_im, hx, hy, add_zero]
    | smul c x _ hx =>
      have e : Hf (c • x) a = (c : ℂ) * Hf x a := by
        simp only [Hf, PiLp.smul_apply, Complex.real_smul, Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by ring
      rw [e, Complex.im_ofReal_mul, hx, mul_zero]
  have h1 := hspan (I • a)
  have e : Hf (I • a) a = I * Hf a a := by
    simp only [Hf, PiLp.smul_apply, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [e, Complex.I_mul_im, herm_self_re] at h1
  simpa using h1
end GlobalTheory.IsogenySum
