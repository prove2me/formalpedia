-- Prove2me | solution 1 for GroundTheory.Arith.SchemeCoh.ProjSpace.coeff_toLaurent_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T18:41:31.14139+00:00
-- url     : https://prove2.me/submissions/40f74334-6519-498b-9fee-86b85d3e9a71

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
theorem _root_.solution {a : MvPolynomial (Fin (n + 1)) A} {m : Fin (n + 1) → ℤ}
    (hm : m ∉ Set.range (expHom n)) : (toLaurent A n a).coeff m = 0 :=
  Finsupp.mapDomain_of_notMem_range _ _ hm
end GroundTheory.Arith.SchemeCoh.ProjSpace
