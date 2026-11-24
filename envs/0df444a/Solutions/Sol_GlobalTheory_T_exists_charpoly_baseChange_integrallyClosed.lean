-- Prove2me | solution 1 for GlobalTheory.T.exists_charpoly_baseChange_integrallyClosed
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:31:19.805179+00:00
-- url     : https://prove2.me/submissions/935eab77-ea9c-4db6-9b2e-4b4a9ab74918

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsCharpolyBaseChangeIntegrallyClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_AlgebraMapNormCoeff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsCharpolyBaseChangeIntegrallyClosedStatement
import Theorems.Thm_GlobalTheory_NormalDescent_exists_map_eq_charK


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Polynomial GlobalTheory.NormalDescent
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ {A B K : Type} [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [CommRing B] [Field K]
    [Algebra A K] [IsFractionRing A K] (φ : A →+* B) (hφ : φ.Finite) (b : B),
    ∃ P : A[X], P.map (algebraMap A K) = charK φ hφ K b := by
  first | exact @GlobalTheory.NormalDescent.exists_map_eq_charK | exact GlobalTheory.NormalDescent.exists_map_eq_charK | (intros; apply GlobalTheory.NormalDescent.exists_map_eq_charK <;> assumption)
end _root_.GlobalTheory.T
