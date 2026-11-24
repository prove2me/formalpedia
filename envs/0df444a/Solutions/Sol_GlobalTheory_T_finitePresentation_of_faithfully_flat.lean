-- Prove2me | solution 1 for GlobalTheory.T.finitePresentation_of_faithfully_flat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:09:31.956371+00:00
-- url     : https://prove2.me/submissions/755e9d94-7a44-4a48-a038-fc43539de693

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_AlgebraProofs_FinitePresentationOfFaithfullyFlat
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_AlgebraProofs_FinitePresentationOfFaithfullyFlatStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_FinPresDescent_finitePresentation_of_finite_projective_faithfullyFlat


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (R C D : Type) [CommRing R] [CommRing C] [CommRing D] [Algebra R C] [Algebra C D] [Algebra R D] [IsScalarTower R C D], Module.Finite C D → Module.Projective C D → Module.FaithfullyFlat C D → Algebra.FinitePresentation R D → Algebra.FinitePresentation R C := by
  first | exact @GlobalTheory.CompanionTheory.FinPresDescent.finitePresentation_of_finite_projective_faithfullyFlat | exact GlobalTheory.CompanionTheory.FinPresDescent.finitePresentation_of_finite_projective_faithfullyFlat | (intros; apply GlobalTheory.CompanionTheory.FinPresDescent.finitePresentation_of_finite_projective_faithfullyFlat <;> assumption)
end _root_.GlobalTheory.T
