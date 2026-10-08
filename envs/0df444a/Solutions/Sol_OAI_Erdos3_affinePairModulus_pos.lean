-- Prove2me | solution 1 for OAI.Erdos3.affinePairModulus_pos
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-08T11:02:29.970803+00:00
-- url     : https://prove2.me/submissions/3039cd72-cf88-498b-a008-43f243a95877

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B013

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.UniformBoxResidueMass
namespace OAI

section

namespace Erdos3

open scoped BigOperators Matrix

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem affinePairModulus_pos {J : Type*} [Fintype J] (t u : J → ℤ) (k : J)
    (hne : u k - t k ≠ 0) : 0 < affinePairModulus t u := by
  apply Int.natAbs_pos.mpr
  apply BohrLattice.Primitive.content_ne_zero
  intro h
  exact hne (congrFun h k)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

end OAI

end

theorem solution.{u_1} : type_of% @OAI.Erdos3.affinePairModulus_pos.{u_1} := @OAI.Erdos3.affinePairModulus_pos.{u_1}
