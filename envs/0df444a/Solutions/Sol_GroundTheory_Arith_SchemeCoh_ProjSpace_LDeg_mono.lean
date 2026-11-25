-- Prove2me | solution 1 for GroundTheory.Arith.SchemeCoh.ProjSpace.LDeg_mono
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:52:39.128163+00:00
-- url     : https://prove2.me/submissions/49be32e5-84fa-4bd0-88dc-9fb1ce43fe00

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ProjSpace
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ProjLaurent
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_ProjSpace_Allowed_mono

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
theorem _root_.solution {s t : Set (Fin (n + 1))} (hst : s ⊆ t) (k : ℤ) : LDeg A s k ≤ LDeg A t k :=
  fun _ hℓ m hm => (hℓ m hm).mono hst
end GroundTheory.Arith.SchemeCoh.ProjSpace
