-- Prove2me | solution 1 for GlobalTheory.RiemannRel.hermForm_cols
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T19:56:39.101218+00:00
-- url     : https://prove2.me/submissions/7955e009-f6e6-4a62-adb0-9bb49f974fe3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_GeomIntSelf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsSiegelPeriodOfSymplecticBasis

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ZM GlobalTheory.KeyFam
open Matrix
open GlobalTheory GlobalTheory.RiemannRel
namespace GlobalTheory.RiemannRel
theorem _root_.solution {h : ℕ} (Hm P Q : Matrix (Fin h) (Fin h) ℂ) (i j : Fin h) :
    (Pᵀ * Hm * Q.map star) i j = hermForm Hm (fun k => P k i) (fun k => Q k j) := by
  rw [Matrix.mul_assoc]
  simp [hermForm, Matrix.mul_apply, dotProduct, Matrix.mulVec]
end GlobalTheory.RiemannRel
