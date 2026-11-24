-- Prove2me | solution 1 for GlobalTheory.WCub.alg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:11:50.444092+00:00
-- url     : https://prove2.me/submissions/e3a37c0a-aea8-4437-a634-934228cae812

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_TripleProductPointCompProjection

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory
open GlobalTheory.WCub
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
namespace GlobalTheory.WCub
theorem _root_.solution {U K : Type} [CommGroup U] [Fintype K] (ε : K → ℤ) (a b c d : K → U) (h : ∀ k, a k * b k = c k * d k)
    {tM tM' tL tL' : U} (e₁ : tM = (∏ k, a k ^ ε k) * tM') (e₂ : tM = (∏ k, c k ^ ε k) * tL)
    (e₃ : tL = (∏ k, d k ^ ε k) * tL') : tM' = (∏ k, b k ^ ε k) * tL' := by
  have : (∏ k, a k ^ ε k) * (∏ k, b k ^ ε k) = (∏ k, c k ^ ε k) * (∏ k, d k ^ ε k) := by
    rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun k _ => by rw [← mul_zpow, ← mul_zpow, h]
  apply mul_left_cancel (a := ∏ k, a k ^ ε k)
  rw [← e₁, e₂, e₃, ← _root_.mul_assoc, ← _root_.mul_assoc, this]
end GlobalTheory.WCub
