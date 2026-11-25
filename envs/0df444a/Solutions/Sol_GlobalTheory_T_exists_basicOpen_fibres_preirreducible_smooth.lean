-- Prove2me | solution 1 for GlobalTheory.T.exists_basicOpen_fibres_preirreducible_smooth
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T05:29:08.581882+00:00
-- url     : https://prove2.me/submissions/09f43807-701e-4e2b-b578-22c6c1cd2e9b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsBasicOpenFibresPreirreducibleSmooth
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsBasicOpenFibresPreirreducibleSmoothStatement
import Theorems.Thm_GlobalTheory_exists_basicOpen_fibres_preirreducible


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B], Algebra.Smooth A B → ∀ (q : PrimeSpectrum B) (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra A Ω], q.asIdeal.comap (algebraMap A B) = RingHom.ker (algebraMap A Ω) → PreirreducibleSpace (PrimeSpectrum (Ω ⊗[A] B)) → ∃ (b : B) (a : A) (I : Finset A), b ∉ q.asIdeal ∧ algebraMap A B a ∉ q.asIdeal ∧ (∀ c ∈ I, algebraMap A B c ∈ q.asIdeal) ∧ ∀ t : PrimeSpectrum A, a ∉ t.asIdeal → (∀ c ∈ I, c ∈ t.asIdeal) → IsPreirreducible {r : PrimeSpectrum B | r.asIdeal.comap (algebraMap A B) = t.asIdeal ∧ b ∉ r.asIdeal} := by
  first | exact @GlobalTheory.exists_basicOpen_fibres_preirreducible | exact GlobalTheory.exists_basicOpen_fibres_preirreducible | (intros; apply GlobalTheory.exists_basicOpen_fibres_preirreducible <;> assumption)
end _root_.GlobalTheory.T
