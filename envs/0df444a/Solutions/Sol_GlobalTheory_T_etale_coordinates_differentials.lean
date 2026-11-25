-- Prove2me | solution 1 for GlobalTheory.T.etale_coordinates_differentials
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T18:19:19.02631+00:00
-- url     : https://prove2.me/submissions/1969402b-7e71-4792-9fa0-3dbf18612076

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_EtaleCoordinatesDifferentials
import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_NadelVanishingPairs_NadelVanishingLemmas_EtaleCoordinatesDifferentials
import Theorems.Thm_GlobalTheory_EtaleCoordRank_finrank_and_linearIndependent_D_unit_mul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct Polynomial
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (R B K : Type) [CommRing R] [CommRing B] [Field K] [Algebra R B] [Algebra B K] (d : ℕ) (t : Fin d → B), (MvPolynomial.eval₂Hom (algebraMap R B) t).Etale → Module.finrank K (K ⊗[B] Ω[B⁄R]) = d ∧ ∀ (ι : Type) (e : ι ↪ Fin d) (u : ι → Bˣ), (∀ i, algebraMap B K (t (e i)) = 0) → LinearIndependent K (fun i => (1 : K) ⊗ₜ[B] KaehlerDifferential.D R B ((u i : B) * t (e i))) := by
  first | exact @_root_.GlobalTheory.EtaleCoordRank.finrank_and_linearIndependent_D_unit_mul | exact _root_.GlobalTheory.EtaleCoordRank.finrank_and_linearIndependent_D_unit_mul | (intros; apply _root_.GlobalTheory.EtaleCoordRank.finrank_and_linearIndependent_D_unit_mul <;> assumption)
end _root_.GlobalTheory.T
