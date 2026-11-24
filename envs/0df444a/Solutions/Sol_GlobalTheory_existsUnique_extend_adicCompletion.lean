-- Prove2me | solution 1 for GlobalTheory.existsUnique_extend_adicCompletion
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:38:10.475093+00:00
-- url     : https://prove2.me/submissions/8e37a6f2-0cdd-4105-a938-083276c23018

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsUniqueFactorCompletedStalkOfMap
import Theorems.Thm_GlobalTheory_exists_extend_adicCompletion
import Theorems.Thm_GlobalTheory_adicCompletion_ringHom_ext

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry IsLocalRing
universe u
open GlobalTheory
variable {A R : Type*} [CommRing A] [CommRing R]
namespace GlobalTheory
theorem _root_.solution (φ : A →+* R) {J : Ideal A} (hJ : J.FG) (I : Ideal R)
    [IsAdicComplete I R] (hk : ∃ k : ℕ, J.map φ ^ k ≤ I) :
    ∃! ψ : AdicCompletion J A →+* R, ψ.comp (algebraMap A (AdicCompletion J A)) = φ := by
  obtain ⟨k, hk⟩ := hk
  obtain ⟨ψ, hψ, -⟩ := exists_extend_adicCompletion φ J I hk
  refine ⟨ψ, hψ, fun ψ' hψ' => ?_⟩
  exact adicCompletion_ringHom_ext hJ I (k := k) (by rwa [hψ']) (hψ'.trans hψ.symm)
end GlobalTheory
