-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.KoszulBd.commute_of_unitary_conjugate
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:48:26.324233+00:00
-- url     : https://prove2.me/submissions/bcbbdcb4-aec6-4c7c-b52e-b5639621d9a0

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_DiscreteSeriesCharacters_CapelliDeterminantBlockProduct
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_CommuteOfUnitaryConjugate

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.KoszulBd
open CompanionTheory.D.DSIC
open Formalism.REAL (GlRel)
variable {n : ℕ} {ε : Fin n → Bool}
variable {ι R : Type} [Fintype ι] [DecidableEq ι] [Ring R] [Algebra ℂ R]
omit [DecidableEq ι] [Algebra ℂ R]
namespace GlobalTheory.CompanionTheory.KoszulBd
theorem _root_.solution (T G : R) (L A : ι → R) (hTA : ∀ k, Commute T (A k)) (hGL : ∀ k, Commute G (L k))
    (h : ∑ k, (T * L k - L k * T) * A k + ∑ k, L k * (G * A k - A k * G) = 0) :
    Commute (T + G) (∑ k, L k * A k) := by
  have e : (T + G) * (∑ k, L k * A k) - (∑ k, L k * A k) * (T + G)
      = ∑ k, (T * L k - L k * T) * A k + ∑ k, L k * (G * A k - A k * G) := by
    rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    have hG : G * (L k * A k) = L k * (G * A k) := by rw [← mul_assoc, (hGL k).eq, mul_assoc]
    have hT : L k * A k * T = L k * T * A k := by rw [mul_assoc, ← (hTA k).eq, ← mul_assoc]
    calc (T + G) * (L k * A k) - L k * A k * (T + G)
        = T * (L k * A k) + G * (L k * A k) - (L k * A k * T + L k * A k * G) := by
          rw [add_mul, mul_add]
      _ = T * (L k * A k) + L k * (G * A k) - (L k * T * A k + L k * A k * G) := by rw [hG, hT]
      _ = (T * L k - L k * T) * A k + L k * (G * A k - A k * G) := by noncomm_ring
  show (T + G) * _ = _ * (T + G)
  rw [← sub_eq_zero, e]
  exact h
end GlobalTheory.CompanionTheory.KoszulBd
