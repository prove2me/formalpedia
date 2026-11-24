-- Prove2me | solution 1 for GlobalTheory.FormalSeries.exists_subst_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T16:08:42.700725+00:00
-- url     : https://prove2.me/submissions/45ac403d-7a1f-4c58-9c8b-08dd7dc313b2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_EqZeroOrSingleOfDegreeLtTwo
import Theorems.Thm_GlobalTheory_FormalSeries_jacobian_apply
import Theorems.Thm_GlobalTheory_FormalSeries_jacobian_X
import Theorems.Thm_GlobalTheory_FormalSeries_le_order_sum
import Theorems.Thm_GlobalTheory_FormalSeries_two_le_order_sub_linear
import Theorems.Thm_GlobalTheory_FormalSeries_le_order_subst_sub_subst
import Theorems.Thm_GlobalTheory_FormalSeries_subst_eq_linear_add
import Theorems.Thm_GlobalTheory_FormalSeries_existsUnique_fixedPoint
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
theorem _root_.solution [Fintype σ] [Fintype τ] [DecidableEq τ] {u : τ → MvPowerSeries σ R}
    (hu : ∀ i, constantCoeff (u i) = 0) {B : Matrix σ τ R} (hB : jacobian u * B = 1)
    {c : τ → MvPowerSeries υ R} (hc : ∀ i, constantCoeff (c i) = 0) :
    ∃ v : σ → MvPowerSeries υ R, (∀ j, constantCoeff (v j) = 0) ∧ ∀ i, (u i).subst v = c i := by
  obtain ⟨N, hN⟩ : ∃ N : τ → MvPowerSeries σ R,
      ∀ i, N i = u i - ∑ j, coeff (Finsupp.single j 1) (u i) • X j := ⟨_, fun _ => rfl⟩
  have hN2 : ∀ i, 2 ≤ (N i).order := fun i => by rw [hN]; exact two_le_order_sub_linear (hu i)
  have hNc : ∀ i, constantCoeff (N i) = 0 := fun i =>
    one_le_order_iff_constCoeff_eq_zero.mp (le_trans (by norm_num) (hN2 i))
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : (σ → MvPowerSeries υ R) → (σ → MvPowerSeries υ R),
      ∀ v j, Φ v j = ∑ i, B j i • (c i - (N i).subst v) := ⟨fun v j => ∑ i, B j i • (c i - (N i).subst v), fun _ _ => rfl⟩
  have h0 : ∀ v, (∀ s, constantCoeff (v s) = 0) → ∀ s, constantCoeff (Φ v s) = 0 := by
    intro v hv j
    rw [hΦ, map_sum]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [constantCoeff_smul, map_sub, hc i,
      constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero hv) hv (hNc i), sub_zero,
      smul_zero]
  have hΦk : ∀ v w (k : ℕ), (∀ s, constantCoeff (v s) = 0) → (∀ s, constantCoeff (w s) = 0) →
      (∀ s, (k : ℕ∞) ≤ (v s - w s).order) →
        ∀ s, ((k + 1 : ℕ) : ℕ∞) ≤ (Φ v s - Φ w s).order := by
    intro v w k hv hw hvw j
    rw [hΦ, hΦ, ← Finset.sum_sub_distrib]
    refine le_order_sum _ fun i _ => ?_
    rw [← smul_sub, sub_sub_sub_cancel_left]
    have hwv : ∀ s, (k : ℕ∞) ≤ (w s - v s).order := fun s => by
      rw [← neg_sub, order_neg]
      exact hvw s
    exact (le_order_subst_sub_subst hw hv hwv (hN2 i)).trans le_order_smul
  obtain ⟨v, ⟨hv0, hvfix⟩, -⟩ := existsUnique_fixedPoint Φ h0 hΦk
  refine ⟨v, hv0, fun i => ?_⟩
  have hvs : HasSubst v := hasSubst_of_constantCoeff_zero hv0
  have hvj : ∀ j, v j = ∑ i', B j i' • (c i' - (N i').subst v) := fun j => by
    rw [← hΦ, hvfix]
  rw [subst_eq_linear_add hvs (u i), ← hN i]
  have hlin : ∑ j, coeff (Finsupp.single j 1) (u i) • v j = c i - (N i).subst v :=
    calc ∑ j, coeff (Finsupp.single j 1) (u i) • v j
        = ∑ j, ∑ i', (jacobian u i j * B j i') • (c i' - (N i').subst v) := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [hvj j, Finset.smul_sum]
          simp only [smul_smul, jacobian_apply]
      _ = ∑ i', (jacobian u * B) i i' • (c i' - (N i').subst v) := by
          rw [Finset.sum_comm]
          simp only [Matrix.mul_apply, Finset.sum_smul]
      _ = c i - (N i).subst v := by
          rw [hB]
          simp [Matrix.one_apply]
  rw [hlin, sub_add_cancel]
end GlobalTheory.FormalSeries
