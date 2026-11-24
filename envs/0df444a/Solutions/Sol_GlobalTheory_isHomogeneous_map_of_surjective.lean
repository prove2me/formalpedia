-- Prove2me | solution 1 for GlobalTheory.isHomogeneous_map_of_surjective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:02:37.623301+00:00
-- url     : https://prove2.me/submissions/442e07c8-5bc3-4b2d-87d4-d046447a79c9

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
    (hφ : Function.Surjective φ) {I : Ideal (MvPolynomial σ R)}
    (hI : I.IsHomogeneous (homogeneousSubmodule σ R)) :
    (I.map (map φ)).IsHomogeneous (homogeneousSubmodule σ R') := by
  intro n q hq
  obtain ⟨p, hp, rfl⟩ := (Ideal.mem_map_iff_of_surjective _ (map_surjective φ hφ)).mp hq
  have h1 : ((DirectSum.decompose (homogeneousSubmodule σ R') (map φ p) n : _) :
      MvPolynomial σ R') = homogeneousComponent n (map φ p) := decomposition.decompose'_apply _ _
  rw [h1, ← map_homogeneousComponent_eq]
  exact Ideal.mem_map_of_mem _ (homogeneousComponent_mem_of_mem hI hp n)
end GlobalTheory
