-- Prove2me | solution 1 for GlobalTheory.OnePoint.nilradical_le_ker
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:08:22.467802+00:00
-- url     : https://prove2.me/submissions/a26fde1f-0e4f-4ca4-a946-d4ed0b32d5c2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsIntegrallyClosedInFractionFieldPowerSeries

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped LaurentSeries PowerSeries
open CategoryTheory Limits AlgebraicGeometry
open GlobalTheory GlobalTheory.OnePoint
universe u v w
local notation "specAlg(" K ", " L ")" => Spec.map (CommRingCat.ofHom (algebraMap K L))
namespace GlobalTheory.OnePoint
theorem _root_.solution {T X : Scheme.{u}} [IsReduced T] (g : T ⟶ X) :
    X.nilradical ≤ g.ker := by
  refine Scheme.IdealSheafData.le_ofIdeals_iff.mpr fun U a ha ↦ ?_
  have ha' : IsNilpotent a := mem_nilradical.mp ha
  exact (ha'.map (g.app U).hom).eq_zero
end GlobalTheory.OnePoint
