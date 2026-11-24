-- Prove2me | solution 1 for GroundTheory.Arith.SchemeCoh.ProjSpace.Allowed.mono
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:45:34.421563+00:00
-- url     : https://prove2.me/submissions/f6cd236d-ccdd-45ca-b0f8-16fc71d195eb

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ProjSpace
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ProjLaurent

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
namespace Allowed
theorem _root_.solution {s t : Set (Fin (n + 1))} {k : ℤ} {m : Fin (n + 1) → ℤ} (h : Allowed s k m)
    (hst : s ⊆ t) : Allowed t k m :=
  ⟨h.1, fun j hj => h.2 j fun hs => hj (hst hs)⟩
end Allowed
end GroundTheory.Arith.SchemeCoh.ProjSpace
