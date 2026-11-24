-- Prove2me | solution 1 for GlobalTheory.PrimitiveUnitProduct.appTop_comp_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T19:30:53.348538+00:00
-- url     : https://prove2.me/submissions/b9ec2512-b4b4-4696-9b15-41a4cdff65a9

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
theorem _root_.solution {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) (s : Γ(Z, ⊤)) :
    (f ≫ g).appTop s = f.appTop (g.appTop s) := by
  rw [Scheme.Hom.comp_appTop]; rfl
end GlobalTheory.PrimitiveUnitProduct
