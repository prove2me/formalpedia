-- Prove2me | solution 1 for GlobalTheory.SocleDet.mem_span_X_of_coeff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:11:00.110682+00:00
-- url     : https://prove2.me/submissions/550c247a-cfa4-45b7-83be-f4e12295fa41

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_CoeffEqZeroOfMemSpanPow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.SocleDet
open Matrix
open MvPowerSeries
variable {k : Type*} [CommRing k] {σ : Type*}
namespace GlobalTheory.SocleDet
theorem _root_.solution (S : Finset σ) : ∀ p : MvPowerSeries σ k,
    (∀ m : σ →₀ ℕ, (∀ j ∈ S, m j = 0) → coeff m p = 0) →
      p ∈ Ideal.span ((fun i => (X i : MvPowerSeries σ k)) '' S) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    intro p hp
    have : p = 0 := MvPowerSeries.ext fun m => hp m (by simp)
    simp [this]
  | insert i S hi ih =>
    intro p hp
    let q : MvPowerSeries σ k := fun m => if m i = 0 then coeff m p else 0
    have hq : ∀ m, coeff m q = if m i = 0 then coeff m p else 0 := fun _ => rfl
    have h1 : q ∈ Ideal.span ((fun i => (X i : MvPowerSeries σ k)) '' (insert i S : Finset σ)) := by
      refine Ideal.span_mono (Set.image_mono (by simp)) (ih q fun m hm => ?_)
      rw [hq]
      split_ifs with h
      · refine hp m fun j hj => ?_
        rcases Finset.mem_insert.1 hj with rfl | hj
        exacts [h, hm j hj]
      · rfl
    have h2 : (X i : MvPowerSeries σ k) ∣ p - q :=
      X_dvd_iff.2 fun m hm => by rw [map_sub, hq, if_pos hm, sub_self]
    obtain ⟨r, hr⟩ := h2
    rw [eq_add_of_sub_eq hr]
    exact Ideal.add_mem _ (Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨i, by simp, rfl⟩)) h1
end GlobalTheory.SocleDet
