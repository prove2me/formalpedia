-- Prove2me | solution 1 for GlobalTheory.FormalSeries.exists_subst_inverse
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:43:29.949956+00:00
-- url     : https://prove2.me/submissions/9082f01e-c547-4e57-83ad-8ac1d14499c3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_EqZeroOrSingleOfDegreeLtTwo
import Theorems.Thm_GlobalTheory_FormalSeries_jacobian_apply
import Theorems.Thm_GlobalTheory_FormalSeries_jacobian_X
import Theorems.Thm_GlobalTheory_FormalSeries_jacobian_subst
import Theorems.Thm_GlobalTheory_FormalSeries_exists_subst_eq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.FormalSeries.jacobian_apply
attribute [local simp] GlobalTheory.FormalSeries.jacobian_X

set_option autoImplicit false
noncomputable section
open GlobalTheory
open GlobalTheory.FormalSeries
open MvPowerSeries
variable {σ τ υ R S : Type*} [CommRing R] [CommRing S]
variable [Algebra R S]
namespace GlobalTheory.FormalSeries
theorem _root_.solution [Fintype σ] [Fintype τ] [DecidableEq σ] [DecidableEq τ]
    {u : τ → MvPowerSeries σ R} (hu : ∀ i, constantCoeff (u i) = 0) {B : Matrix σ τ R}
    (hB : jacobian u * B = 1) (hB' : B * jacobian u = 1) :
    ∃ v : σ → MvPowerSeries τ R, (∀ j, constantCoeff (v j) = 0) ∧
      (∀ i, (u i).subst v = X i) ∧ ∀ j, (v j).subst u = X j := by
  obtain ⟨v, hv0, hv⟩ := exists_subst_eq hu hB (c := (X : τ → MvPowerSeries τ R))
    (fun i => constantCoeff_X i)
  have hJ : jacobian u * jacobian v = 1 := by
    rw [← jacobian_subst hv0 u]
    simp only [hv]
    exact jacobian_X
  have hJv : jacobian v = B :=
    calc jacobian v = (B * jacobian u) * jacobian v := by rw [hB', Matrix.one_mul]
      _ = B := by rw [Matrix.mul_assoc, hJ, Matrix.mul_one]
  obtain ⟨w, hw0, hw⟩ := exists_subst_eq hv0 (B := jacobian u) (by rw [hJv]; exact hB')
    (c := (X : σ → MvPowerSeries σ R)) (fun j => constantCoeff_X j)
  have hvs : HasSubst v := hasSubst_of_constantCoeff_zero hv0
  have hws : HasSubst w := hasSubst_of_constantCoeff_zero hw0
  have huw : u = w := by
    funext i
    calc u i = (u i).subst (X : σ → MvPowerSeries σ R) := by rw [subst_self]; rfl
      _ = (u i).subst (fun s => (v s).subst w) := by simp only [hw]
      _ = ((u i).subst v).subst w := (subst_comp_subst_apply hvs hws _).symm
      _ = w i := by rw [hv, subst_X hws]
  refine ⟨v, hv0, hv, fun j => ?_⟩
  rw [huw]
  exact hw j
end GlobalTheory.FormalSeries
