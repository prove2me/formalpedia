-- Prove2me | solution 1 for GlobalTheory.UnitCocycle.datum_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:00:50.204892+00:00
-- url     : https://prove2.me/submissions/df084285-234e-4945-80f2-73d4ed0dc17e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsUniqueBaseChangeEqOfMem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LocallyTrivialUnitCocycleFaithfullyFlat

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits TensorProduct
open GlobalTheory
open GlobalTheory.UnitCocycle
variable {R B : Type} [CommRing R] [CommRing B] [Algebra R B]
namespace GlobalTheory.UnitCocycle
theorem _root_.solution (c : B ⊗[R] B) (x : B) : datum c x = c * (x ⊗ₜ[R] (1 : B)) := by
  rw [datum, LinearMap.toSpanSingleton_apply, Algebra.smul_def, mul_comm]
  rfl
end GlobalTheory.UnitCocycle
