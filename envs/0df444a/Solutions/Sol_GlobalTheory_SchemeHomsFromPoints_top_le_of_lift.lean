-- Prove2me | solution 1 for GlobalTheory.SchemeHomsFromPoints.top_le_of_lift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T20:35:53.039797+00:00
-- url     : https://prove2.me/submissions/97ab0474-90d2-4cc6-b363-637cda9fe071

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_DenseClosedPoints

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp valAt valAt')
open GlobalTheory GlobalTheory.SchemeHomsFromPoints
namespace GlobalTheory.SchemeHomsFromPoints
theorem _root_.solution {X T : Scheme.{0}} (W : X.Opens) (x : T ⟶ X) (x' : T ⟶ W)
    (hx : x' ≫ W.ι = x) : ⊤ ≤ x ⁻¹ᵁ W := by
  subst hx
  intro t _
  exact (x'.base t).2
end GlobalTheory.SchemeHomsFromPoints
