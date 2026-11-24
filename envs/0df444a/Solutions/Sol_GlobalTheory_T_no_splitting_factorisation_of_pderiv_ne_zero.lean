-- Prove2me | solution 1 for GlobalTheory.T.no_splitting_factorisation_of_pderiv_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:08:41.206732+00:00
-- url     : https://prove2.me/submissions/383e397e-8edb-4d56-89d6-e41706a8a2f6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NoSplittingFactorisationOfPderivNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NoSplittingFactorisationOfPderivNeZeroStatement
import Theorems.Thm_GlobalTheory_hypersurface_part_no_splitting_factorisation


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
theorem _root_.solution : ∀ (Ω : Type) [Field Ω] (σ : Type) (f g : MvPolynomial σ Ω) (i : σ) (D : ℕ), (∀ Q : σ → Ω, MvPolynomial.eval Q f = 0 → MvPolynomial.eval Q g ≠ 0 → MvPolynomial.eval Q (MvPolynomial.pderiv i f) ≠ 0) → IsPreirreducible (PrimeSpectrum.zeroLocus {f} \ PrimeSpectrum.zeroLocus {g}) → ¬ (∃ u v : MvPolynomial σ Ω, u.totalDegree ≤ D ∧ v.totalDegree ≤ D ∧ u * v = f ∧ ∃ P Q : σ → Ω, MvPolynomial.eval P u = 0 ∧ MvPolynomial.eval P g ≠ 0 ∧ MvPolynomial.eval Q v = 0 ∧ MvPolynomial.eval Q g ≠ 0) := by
  first | exact @GlobalTheory.hypersurface_part_no_splitting_factorisation | exact GlobalTheory.hypersurface_part_no_splitting_factorisation | (intros; apply GlobalTheory.hypersurface_part_no_splitting_factorisation <;> assumption)
end _root_.GlobalTheory.T
