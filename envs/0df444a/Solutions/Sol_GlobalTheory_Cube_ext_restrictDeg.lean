-- Prove2me | solution 1 for GlobalTheory.Cube.ext_restrictDeg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T07:44:37.456733+00:00
-- url     : https://prove2.me/submissions/99e14d16-819e-4541-9e8c-602ee277f6bd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_CubeTotalComplexAcyclicOfSlicesInductionOnCard
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_RangeRestrictCompSubtypeOfOrthogonalOfNe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits HomologicalComplex TensorProduct
universe v u
open GlobalTheory
open GlobalTheory.Cube
variable {ι : Type} {R : Type u} [Ring R]
namespace GlobalTheory.Cube
theorem _root_.solution {A : Cube.{v} ι R} {x y : ∀ s, A.obj s}
    (h : ∀ p, restrictDeg A p x = restrictDeg A p y) : x = y :=
  funext fun s => congrFun (h s.card) ⟨s, rfl⟩
end GlobalTheory.Cube
