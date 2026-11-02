-- Prove2me | solution 1 for OAI.Laughlin.Fock.occupationInner_scalar_wedge_zero_s50
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-01T12:37:52.743441+00:00
-- url     : https://prove2.me/submissions/e26a9edb-2982-4e6d-80ad-d8dc787f2162
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_LaughlinPlanar
import Definitions.Def_OAIQ050L006
import Definitions.Def_OAIQ050L007
import Theorems.Thm_OAI_Laughlin_Fock_vectorCreate_adjoint_s50

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Operators_PositiveFockLift
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators ComplexOrder
open Matrix

theorem occupationInner_star (Q : ℕ) (x y : Space Q) :
    star (occupationInner Q x y) = occupationInner Q y x := by
  simp [occupationInner,star_mul,mul_comm]

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Exterior_SpinUnitary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open Rotation
open scoped BigOperators

theorem occupationInner_scalar_wedge_zero_s50_oai (Q : ℕ) (r : ℂ) (v : Orbital Q) (x : Space Q) :
    occupationInner Q (algebraMap ℂ (Space Q) r) (ExteriorAlgebra.ι ℂ v*x) = 0 := by
  have h := congrArg star (vectorCreate_adjoint_s50 Q v x (algebraMap ℂ (Space Q) r))
  rw [occupationInner_star,occupationInner_star] at h
  simpa [vectorAnnihilate,occupationInner] using h

end Laughlin.Fock

end OAI
end

theorem solution : type_of% @OAI.Laughlin.Fock.occupationInner_scalar_wedge_zero_s50_oai := @OAI.Laughlin.Fock.occupationInner_scalar_wedge_zero_s50_oai
