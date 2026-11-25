-- Prove2me | solution 1 for GroundTheory.Arith.SchemeCoh.ProjSpace.sum_nsmul_mult
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:53:28.509828+00:00
-- url     : https://prove2.me/submissions/9b6f83d7-3d15-4f42-b88e-7e11a8f766c1

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ProjSpace
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ProjLaurent
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_ProjSpace_sum_mult

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Arith GroundTheory.Arith.SchemeCoh
open AlgebraicGeometry MvPolynomial
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
noncomputable section
open GroundTheory.Arith.SchemeCoh.ProjSpace
variable {A : Type u} [CommRing A] {n : ℕ}
namespace GroundTheory.Arith.SchemeCoh.ProjSpace
theorem _root_.solution {p : ℕ} (i : Fin p → Fin (n + 1)) (N : ℕ) :
    ∑ x, (N • mult i) x = (N : ℤ) * p := by
  change ∑ x, N • mult i x = _
  rw [← Finset.smul_sum, sum_mult, nsmul_eq_mul]
end GroundTheory.Arith.SchemeCoh.ProjSpace
