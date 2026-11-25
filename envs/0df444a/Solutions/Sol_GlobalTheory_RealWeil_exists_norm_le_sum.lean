-- Prove2me | solution 1 for GlobalTheory.RealWeil.exists_norm_le_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T05:14:45.701668+00:00
-- url     : https://prove2.me/submissions/26286bfa-e3c3-4332-9cde-a9b3c06da506

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_RealMetaplecticRepresentation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IteratedLineDerivMemWeylAlg
import Theorems.Thm_GlobalTheory_RealWeil_exists_seminorm_le
import Theorems.Thm_GlobalTheory_RealWeil_schwartzToL2_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Complex SchwartzMap LineDeriv Matrix
open scoped Real RealInnerProductSpace ContDiff FourierTransform
open GlobalTheory GlobalTheory.RealWeil
variable {l : Type} [Fintype l]
variable [DecidableEq l]
namespace GlobalTheory.RealWeil
theorem _root_.solution (lam : Sch l →L[ℂ] ℂ) :
    ∃ (ι : Type) (_ : Fintype ι) (A : ι → (Sch l →L[ℂ] Sch l)) (C : ℝ), 0 ≤ C ∧
      (∀ i, A i ∈ weylAlg l) ∧ ∀ f, ‖lam f‖ ≤ C * ∑ i, ‖schwartzToL2 l (A i f)‖ := by
  obtain ⟨s, C, -, hC⟩ := Seminorm.bound_of_continuous (schwartz_withSeminorms ℂ (EuclideanSpace ℝ l) ℂ)
    ((normSeminorm ℂ ℂ).comp lam.toLinearMap) (continuous_norm.comp lam.continuous)
  have hC' : ∀ f, ‖lam f‖ ≤ C * s.sup (schwartzSeminormFamily ℂ (EuclideanSpace ℝ l) ℂ) f := fun f => hC f
  clear hC
  choose A hA hA' using exists_seminorm_le (l := l)
  simp only [← schwartzToL2_apply] at hA'
  refine ⟨Σ p : s, (Fin p.1.2 → l), inferInstance, fun i => A i.1.1.1 i.1.1.2 i.2, C, C.2, fun i => hA _ _ _,
    fun f => (hC' f).trans (mul_le_mul_of_nonneg_left ?_ C.2)⟩
  rw [Fintype.sum_sigma]
  refine Seminorm.finset_sup_apply_le (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _)
    fun p hp => ?_
  rw [schwartzSeminormFamily_apply]
  refine (hA' p.1 p.2 f).trans ?_
  exact Finset.single_le_sum (f := fun q : s => ∑ r, ‖schwartzToL2 l (A q.1.1 q.1.2 r f)‖)
    (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ (⟨p, hp⟩ : s))
end GlobalTheory.RealWeil
