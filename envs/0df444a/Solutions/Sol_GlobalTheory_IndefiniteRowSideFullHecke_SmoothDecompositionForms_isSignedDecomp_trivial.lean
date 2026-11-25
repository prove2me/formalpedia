-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.SmoothDecompositionForms.isSignedDecomp_trivial
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:54:53.03386+00:00
-- url     : https://prove2.me/submissions/e0c3cb3c-80eb-48db-8983-3ef897700d05

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UpqRep
import Definitions.Def_Formalism_PeriodIntegrals_IsLowUnitH
import Definitions.Def_Formalism_PeriodIntegrals_BesselMapUniq
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HighestWeightUniqueness_HpkMulMulHpkApply
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_JetGauges_SmoothDecompositionForms
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_SmoothDecompositionForms_dsigW_zero
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_SmoothDecompositionForms_zero_mem_smooth

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open scoped InnerProductSpace
open PI.UpqRep
noncomputable section
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.SmoothDecompositionForms
attribute [instance] HRep.instNorm HRep.instInner HRep.instComplete
variable {k r : ℕ}
variable {ι : Type} [Fintype ι]
namespace GlobalTheory.IndefiniteRowSideFullHecke.SmoothDecompositionForms
theorem _root_.solution [DecidableEq ι] (R : HRep k r) (ep : ι → ℝ) (hep : ∀ c, ep c = 1 ∨ ep c = -1) :
    IsSignedDecomp (fun _ => (1 : Matrix ι ι ℂ)) (Matrix.diagonal fun c => (ep c : ℂ)) R (fun _ : ι => R)
      (fun j v => Pi.single j v) (fun j x => x j) ep := by
  have hact : ∀ g (x : ι → R.H), tensAct (fun _ => (1 : Matrix ι ι ℂ)) R g x = fun c => R.σ g (x c) := by
    intro g x; funext c
    simp [tensAct, Matrix.one_apply]
  have hform : ∀ x y : ι → R.H, tensForm (Matrix.diagonal fun c => (ep c : ℂ)) x y =
      ∑ c, (ep c : ℂ) * ⟪y c, x c⟫_ℂ := by
    intro x y
    simp [tensForm, Matrix.diagonal_apply]
  refine ⟨⟨fun j c => ?_, fun j => ⟨fun x hx => hx j, fun _ _ _ _ => rfl, fun _ _ _ => rfl, fun w hw => ?_⟩,
    fun j g _ v _ => ?_, fun j g _ x _ => by rw [hact], fun j v _ => by simp, fun i j h v _ => by simp [h],
    fun x _ => Finset.univ_sum_single x⟩, hep, fun j x _ y _ => ?_, fun i j h x _ y _ => ?_⟩
  · by_cases h : c = j
    · subst h
      simp only [Pi.single_eq_same]
      exact ⟨fun _ hv => hv, fun _ _ _ _ => rfl, fun _ _ _ => rfl,
        fun w hw => ⟨1, [w], by simpa using hw, fun v _ => by simp [HRep.semi]⟩⟩
    · simp only [Pi.single_eq_of_ne h]
      exact ⟨fun _ _ => zero_mem_smooth R, fun _ _ _ _ => by simp, fun _ _ _ => by simp,
        fun w _ => ⟨0, [], by simp, fun v _ => by simp [dsigW_zero]⟩⟩
  · refine ⟨1, [w], by simpa using hw, fun x _ => ?_⟩
    simp only [HRep.semi, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, one_mul]
    exact Finset.single_le_sum (f := fun c => ‖dsigW (k := k) (r := r) R.σ w (x c)‖) (fun _ _ => norm_nonneg _)
      (Finset.mem_univ j)
  · rw [hact]; funext c
    by_cases h : c = j
    · subst h; simp
    · simp [Pi.single_eq_of_ne h]
  · rw [hform, Finset.sum_eq_single j (fun c _ h => by simp [Pi.single_eq_of_ne h]) (by simp)]
    simp
  · rw [hform]
    refine Finset.sum_eq_zero fun c _ => ?_
    by_cases hc : c = i
    · subst hc; simp [Pi.single_eq_of_ne h]
    · simp [Pi.single_eq_of_ne hc]
end GlobalTheory.IndefiniteRowSideFullHecke.SmoothDecompositionForms
