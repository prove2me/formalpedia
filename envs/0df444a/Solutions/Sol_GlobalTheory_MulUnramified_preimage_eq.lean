-- Prove2me | solution 1 for GlobalTheory.MulUnramified.preimage_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T18:59:27.115525+00:00
-- url     : https://prove2.me/submissions/9f547269-ea37-4a24-847a-15e3dd500d25

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
theorem _root_.solution {T₀ T X : Scheme.{0}} (i : T₀ ⟶ T) (hi : Function.Surjective i) {f g : T ⟶ X}
    (h : i ≫ f = i ≫ g) (V : X.Opens) : f ⁻¹ᵁ V = g ⁻¹ᵁ V := by
  ext x
  obtain ⟨x, rfl⟩ := hi x
  have : f (i x) = g (i x) := congr($h x)
  simp [this]
end GlobalTheory.MulUnramified
