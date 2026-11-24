-- Prove2me | solution 1 for GlobalTheory.gm_mul_eq_of_res_mul_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:58:58.821918+00:00
-- url     : https://prove2.me/submissions/a40dcb78-2746-48c0-bb45-f551465b3f0e

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_GmMulEqOfResMulEq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_res


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
set_option autoImplicit false
noncomputable section
open GlobalTheory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
namespace GlobalTheory
theorem _root_.solution {Y Z : Scheme.{0}} {V U₁ U₂ U₃ U₄ : Y.Opens} {h₁ : V ≤ U₁} {h₂ : V ≤ U₂}
    {h₃ : V ≤ U₃} {h₄ : V ≤ U₄} {a : Γ(Y, U₁)ˣ} {b : Γ(Y, U₂)ˣ} {c : Γ(Y, U₃)ˣ} {d : Γ(Y, U₄)ˣ}
    (H : res h₁ a * res h₂ b = res h₃ c * res h₄ d) (r : Z ⟶ Y) (z : Z) (hz : r z ∈ V) :
    gm r z U₁ a * gm r z U₂ b = gm r z U₃ c * gm r z U₄ d := by
  have e := congrArg (gm r z V) H
  rwa [map_mul, map_mul, gm_res r z h₁ hz, gm_res r z h₂ hz, gm_res r z h₃ hz, gm_res r z h₄ hz] at e
end GlobalTheory
