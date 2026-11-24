-- Prove2me | solution 1 for GlobalTheory.K5.Basic.isClo_algebraicClosure
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T18:24:54.239831+00:00
-- url     : https://prove2.me/submissions/8fc86411-56fb-408f-a508-408aa1a4f93e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_NotCoboundaryConstantOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.K5 GlobalTheory.K5.Basic
open Polynomial
variable (p : ℕ) [hp : Fact p.Prime]
namespace GlobalTheory.K5.Basic
theorem _root_.solution : IsClo p (AlgebraicClosure (FractionRing (O0 p))) where
  inj := by
    rw [IsScalarTower.algebraMap_eq (O0 p) (FractionRing (O0 p))]
    exact (algebraMap (FractionRing (O0 p)) _).injective.comp (IsFractionRing.injective _ _)
  alg := (IsFractionRing.comap_isAlgebraic_iff (A := O0 p) (K := FractionRing (O0 p))).2
    inferInstance
  clo := inferInstance
end GlobalTheory.K5.Basic
