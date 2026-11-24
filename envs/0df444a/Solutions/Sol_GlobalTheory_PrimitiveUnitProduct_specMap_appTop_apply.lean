-- Prove2me | solution 1 for GlobalTheory.PrimitiveUnitProduct.specMap_appTop_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T19:30:56.143095+00:00
-- url     : https://prove2.me/submissions/f4f82417-6079-40e0-bd79-84293a18cf04

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_UnitOnProductEqOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct CategoryTheory AlgebraicGeometry Limits
open GlobalTheory GlobalTheory.PrimitiveUnitProduct
namespace GlobalTheory.PrimitiveUnitProduct
theorem _root_.solution {R S : CommRingCat} (φ : R ⟶ S) (s : Γ(Spec R, ⊤)) :
    (Scheme.ΓSpecIso S).hom ((Spec.map φ).appTop s) = φ ((Scheme.ΓSpecIso R).hom s) :=
  congrArg (fun t => t.hom s) (Scheme.ΓSpecIso_naturality φ)
end GlobalTheory.PrimitiveUnitProduct
