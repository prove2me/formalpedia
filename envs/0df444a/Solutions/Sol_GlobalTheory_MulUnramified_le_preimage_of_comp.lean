-- Prove2me | solution 1 for GlobalTheory.MulUnramified.le_preimage_of_comp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:43:59.307568+00:00
-- url     : https://prove2.me/submissions/df986a09-a9f6-4ad1-a5b3-6ff42e5a287f

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_FormallyUnramifiedMulN

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.MulUnramified
namespace GlobalTheory.MulUnramified
theorem _root_.solution {T P X : Scheme.{0}} (a : T ⟶ P) (p : P ⟶ X)
    {V : X.Opens} {V' : P.Opens} {W : T.Opens} (h₁ : V' ≤ p ⁻¹ᵁ V) (h₂ : W ≤ a ⁻¹ᵁ V') :
    W ≤ (a ≫ p) ⁻¹ᵁ V := fun _ hx ↦ h₁ (h₂ hx)
end GlobalTheory.MulUnramified
