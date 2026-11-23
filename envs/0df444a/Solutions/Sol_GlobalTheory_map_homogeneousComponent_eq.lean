-- Prove2me | solution 1 for GlobalTheory.map_homogeneousComponent_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:15:48.039232+00:00
-- url     : https://prove2.me/submissions/736c7d37-dfaf-4d67-92a8-7c1cfbfa5240

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsRingKrullDimQuotientMvPolynomialEqNat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsFormsAlgebraicIndependentSmulSubSumMem

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
theorem _root_.solution {R' : Type*} [CommRing R'] (φ : R →+* R') (n : ℕ)
    (p : MvPolynomial σ R) :
    map φ (homogeneousComponent n p) = homogeneousComponent n (map φ p) := by
  ext m
  simp only [coeff_map, coeff_homogeneousComponent]
  split_ifs <;> simp
end GlobalTheory
