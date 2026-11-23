-- Prove2me | solution 1 for GlobalTheory.exists_lift_maximalSpectrum_pi
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:22:38.023988+00:00
-- url     : https://prove2.me/submissions/038f1b44-e5a0-43d1-8721-d3a3a7c4f607

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DualRestrictSurjectiveOfIsTorsionFreeQuotient
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsIsSymplecticBasisToMatrixOffDiagDvd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Module Function
open private exists_symmetric_X_invertible_add_mul_of_ker_inter_eq_bot from
  Mathlib.LinearAlgebra.SymplecticGroup
open GlobalTheory
variable {R : Type*} [CommRing R]
namespace GlobalTheory
theorem _root_.solution [Finite (MaximalSpectrum R)] :
    ∃ s : (∀ m : MaximalSpectrum R, R ⧸ m.asIdeal) → R,
      ∀ x m, Ideal.Quotient.mk m.asIdeal (s x) = x m := by
  choose s hs using Ideal.pi_quotient_surjective (I := fun m : MaximalSpectrum R => m.asIdeal)
    fun _ _ => MaximalSpectrum.isCoprime_of_ne
  exact ⟨s, hs⟩
end GlobalTheory
