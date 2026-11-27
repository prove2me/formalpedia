-- Prove2me | solution 1 for GroundTheory.Arith.SchemeCoh.mem_reesSubmodule_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:42:46.803839+00:00
-- url     : https://prove2.me/submissions/0597d75a-f1b2-43ae-9e01-2517ae008376

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ProperCohomology_ReesSubmodule

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
open Polynomial
universe u v w
variable {A : Type u} [CommRing A] (I : Ideal A)
variable (M : Type v) [AddCommGroup M] [Module A M]
variable {I M}
namespace GroundTheory.Arith.SchemeCoh
theorem _root_.solution {p : PolynomialModule A M} :
    p ∈ reesSubmodule I M ↔ ∀ n, p.coeff n ∈ I ^ n • (⊤ : Submodule A M) := Iff.rfl
end GroundTheory.Arith.SchemeCoh
