-- Prove2me | solution 1 for GlobalTheory.T.hypersurface_diff_isPreirreducible_of_no_splitting
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:08:38.166647+00:00
-- url     : https://prove2.me/submissions/8c2685ba-9d06-40f5-b38e-6eeaa0a0d009

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HypersurfaceDiffIsPreirreducibleOfNoSplitting
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HypersurfaceDiffIsPreirreducibleOfNoSplittingStatement
import Theorems.Thm_GlobalTheory_hypersurface_diff_isPreirreducible


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
theorem _root_.solution : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (σ : Type) [Finite σ] (f g : MvPolynomial σ Ω) (D : ℕ), f ≠ 0 → f.totalDegree ≤ D → ¬ (∃ u v : MvPolynomial σ Ω, u.totalDegree ≤ D ∧ v.totalDegree ≤ D ∧ u * v = f ∧ ∃ P Q : σ → Ω, MvPolynomial.eval P u = 0 ∧ MvPolynomial.eval P g ≠ 0 ∧ MvPolynomial.eval Q v = 0 ∧ MvPolynomial.eval Q g ≠ 0) → IsPreirreducible (PrimeSpectrum.zeroLocus {f} \ PrimeSpectrum.zeroLocus {g}) := by
  first | exact @GlobalTheory.hypersurface_diff_isPreirreducible | exact GlobalTheory.hypersurface_diff_isPreirreducible | (intros; apply GlobalTheory.hypersurface_diff_isPreirreducible <;> assumption)
end _root_.GlobalTheory.T
