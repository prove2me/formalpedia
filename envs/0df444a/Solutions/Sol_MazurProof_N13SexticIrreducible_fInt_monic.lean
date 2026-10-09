-- Prove2me | solution 1 for MazurProof.N13SexticIrreducible.fInt_monic
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-10-09T03:35:13.092883+00:00
-- url     : https://prove2.me/submissions/73d8f63a-7a66-41a0-aecd-64a64c10a16f

import Mathlib
import Definitions.Def_MazurN13_L0

set_option maxHeartbeats 1000000

-- ===== FLT.Assumptions.MazurProof.N13SexticIrreducible =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13SexticIrreducible =====
section
/-!
# Irreducibility of the N13 sextic

The sextic defining the fake two-descent algebra is irreducible over `ℚ`.
We prove this structurally by reduction modulo three.  An irreducible
degree-`d` factor over `𝔽₃` divides `X ^ (3 ^ d) - X`, by applying finite-field
Frobenius in its adjoin-root field.  Three short Bézout identities exclude
degrees one through three, which is the full Rabin test for a sextic.  No
finite-field polynomials are enumerated.
-/
open Polynomial
namespace MazurProof.N13SexticIrreducible
noncomputable section
theorem fInt_monic : fInt.Monic := by
  unfold fInt
  monicity!
end
end MazurProof.N13SexticIrreducible
end

end

theorem solution : type_of% @MazurProof.N13SexticIrreducible.fInt_monic := @MazurProof.N13SexticIrreducible.fInt_monic
