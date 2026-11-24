-- Prove2me | solution 1 for GlobalTheory.UnitaryOrbitForm.dotProduct_star_eq_re
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:05:09.709151+00:00
-- url     : https://prove2.me/submissions/02c5c2e0-b615-4dbc-9ea8-5f135c377f6d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_ExistsGlIsometryCompEqOfNondegenerate
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_EqZeroOfEventuallyDotProductStarEqZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.UnitaryOrbitForm
open Matrix Filter Topology
variable {r : ℕ}
namespace GlobalTheory.UnitaryOrbitForm
theorem _root_.solution {A : Matrix (Fin r) (Fin r) ℂ} (hA : A.IsHermitian)
    (w : Fin r → ℂ) : w ⬝ᵥ A *ᵥ star w = ((w ⬝ᵥ A *ᵥ star w).re : ℂ) := by
  have hc : star (w ⬝ᵥ A *ᵥ star w) = w ⬝ᵥ A *ᵥ star w := by
    simp only [dotProduct, mulVec, Finset.mul_sum, star_sum, star_mul', star_star, Pi.star_apply]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [← hA.apply i j]
    ring
  exact (Complex.conj_eq_iff_re.mp hc).symm
end GlobalTheory.UnitaryOrbitForm
