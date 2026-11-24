-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SchrLaw.goodChar_isLocallyConstant
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T13:35:08.92422+00:00
-- url     : https://prove2.me/submissions/c35a7018-f7d8-452e-9a2c-efcf033f27fa

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_MembershipCriteria_GoodChar
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MembershipProofs_GoodCharIsLocallyConstant

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.CompanionTheory.VacLoc GlobalTheory.CompanionTheory.FinHeis GlobalTheory.WeilM MeasureTheory Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SchrLaw
namespace GlobalTheory.CompanionTheory.SchrLaw
theorem _root_.solution {R : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    {ψ : AddChar R ℂ} {O : Subring R} {u : Rˣ} (h : GoodChar ψ O u) : IsLocallyConstant (ψ : R → ℂ) := by
  have hone : ∀ z : R, ((u⁻¹ : Rˣ) : R) * z ∈ O → ψ z = 1 := by
    intro z hz
    have hu : ∀ y ∈ O, ψ ((u : R) * y) = 1 :=
      (h.ann (u : R)).2 (by rw [Units.inv_mul]; exact O.one_mem)
    have := hu _ hz
    rwa [Units.mul_inv_cancel_left] at this
  rw [IsLocallyConstant.iff_exists_open]
  intro x
  refine ⟨{y | ((u⁻¹ : Rˣ) : R) * (y - x) ∈ O}, ?_, ?_, ?_⟩
  · exact h.isOpen.preimage (continuous_const.mul (continuous_id.sub continuous_const))
  · simp only [Set.mem_ofPred_eq, sub_self, mul_zero]
    exact O.zero_mem
  · intro y hy
    have hy' : y = x + (y - x) := by abel
    rw [hy', AddChar.map_add_eq_mul, hone _ hy, mul_one]
end GlobalTheory.CompanionTheory.SchrLaw
