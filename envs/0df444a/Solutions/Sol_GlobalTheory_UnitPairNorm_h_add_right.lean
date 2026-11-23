-- Prove2me | solution 1 for GlobalTheory.UnitPairNorm.h_add_right
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:12:04.506927+00:00
-- url     : https://prove2.me/submissions/022edf57-ca2c-4497-b89b-55ba91513046

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsUnitNorm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.UnitPairNorm
open Module
variable {O E : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field E]
  [Algebra O E] [IsFractionRing O E]
variable {V : Type} [AddCommGroup V] [Module E V] [Module O V] [IsScalarTower O E V]
namespace GlobalTheory.UnitPairNorm
theorem _root_.solution (c : E ≃+* E) (h : V → V → E)
    (hadd : ∀ x y z : V, h (x + y) z = h x z + h y z)
    (hsym : ∀ x y : V, h y x = c (h x y)) (y a b : V) :
    h y (a + b) = h y a + h y b := by
  rw [hsym (a + b) y, hadd, map_add, ← hsym, ← hsym]
end GlobalTheory.UnitPairNorm
