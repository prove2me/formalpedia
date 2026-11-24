-- Prove2me | solution 1 for GlobalTheory.FibSurj.fibMap_fst
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T15:00:42.611181+00:00
-- url     : https://prove2.me/submissions/c7e20692-d38c-4fe7-9df3-28adbc9618ce

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_SpecialFibreUnits
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SpecialFibreConnectedOfBaseChange

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits AlgebraicGeometry
open GlobalTheory GlobalTheory.FibSurj
open IsLocalRing
variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
  {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (φ : V →+* O) [IsLocalHom φ]
  {X : Scheme.{0}} (s : X ⟶ Spec (.of V))
namespace GlobalTheory.FibSurj
theorem _root_.solution : fibMap φ s ≫ pullback.fst _ _ = pullback.fst _ _ ≫ pullback.fst _ _ :=
  pullback.lift_fst _ _ _
end GlobalTheory.FibSurj
