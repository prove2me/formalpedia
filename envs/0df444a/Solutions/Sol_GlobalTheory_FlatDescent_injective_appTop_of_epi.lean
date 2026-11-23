-- Prove2me | solution 1 for GlobalTheory.FlatDescent.injective_appTop_of_epi
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:36:49.747993+00:00
-- url     : https://prove2.me/submissions/bbcecd69-e2ce-4df0-b92a-6f29d52a14d2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsAppTopEqOfEffectiveEpi

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits AlgebraicGeometry Opposite
open GlobalTheory
open GlobalTheory.FlatDescent
universe u
variable {X Y Z : Scheme.{u}}
namespace GlobalTheory.FlatDescent
theorem _root_.solution (p : Y ⟶ X) [Epi p] : Function.Injective p.appTop := by
  have : Epi (Scheme.Γ.rightOp.map p) :=
    have := ΓSpec.adjunction.isLeftAdjoint
    inferInstance
  have : Mono p.appTop := inferInstanceAs (Mono (Scheme.Γ.rightOp.map p).unop)
  exact ConcreteCategory.injective_of_mono_of_preservesPullback p.appTop
end GlobalTheory.FlatDescent
