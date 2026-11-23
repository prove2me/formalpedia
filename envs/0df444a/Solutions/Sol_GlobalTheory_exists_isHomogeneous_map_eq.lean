-- Prove2me | solution 1 for GlobalTheory.exists_isHomogeneous_map_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:22:52.207984+00:00
-- url     : https://prove2.me/submissions/7cf980c3-1031-4d38-ad4b-dc42e89279ec

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsRingKrullDimQuotientMvPolynomialEqNat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsFormsAlgebraicIndependentSmulSubSumMem
import Theorems.Thm_GlobalTheory_map_homogeneousComponent_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open MvPolynomial
attribute [local instance] MvPolynomial.gradedAlgebra
variable {σ ι R : Type*} [CommRing R]
namespace GlobalTheory
theorem _root_.solution {R' : Type*} [CommRing R'] {φ : R →+* R'}
    (hφ : Function.Surjective φ) {n : ℕ} {q : MvPolynomial σ R'} (hq : q.IsHomogeneous n) :
    ∃ p : MvPolynomial σ R, p.IsHomogeneous n ∧ map φ p = q := by
  obtain ⟨p, rfl⟩ := map_surjective φ hφ q
  exact ⟨homogeneousComponent n p, homogeneousComponent_isHomogeneous _ _, by
    rw [map_homogeneousComponent_eq, homogeneousComponent_eq_self hq]⟩
end GlobalTheory
