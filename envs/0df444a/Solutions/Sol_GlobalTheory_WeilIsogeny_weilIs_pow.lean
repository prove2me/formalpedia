-- Prove2me | solution 1 for GlobalTheory.WeilIsogeny.weilIs_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T14:48:11.368435+00:00
-- url     : https://prove2.me/submissions/fa7eb699-f232-42ac-a831-7ede96306da8

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_GenMove
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBLocal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsUniqueWeilIs
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsGenMovePow
import Theorems.Thm_GlobalTheory_WeilIsogeny_weilIs_of_local
import Theorems.Thm_GlobalTheory_WeilIsogeny_exists_theta_pow
import Theorems.Thm_GlobalTheory_CommutatorPairing_commIsOf_iff


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.WeilIsogeny
open CommutatorPairing
variable {S : Scheme.{0}} {A B : Over S} [GrpObj A] [GrpObj B] {L : LB A.left} {M : LB B.left}
namespace GlobalTheory.WeilIsogeny
theorem _root_.solution (hG : GlobalFnsSt) (hA : IsAbelianScheme A) (hL : L.IsLB) (d : ℕ) {n : ℤ} {T : Over S}
    {x y : T ⟶ A} {c : Γ(T.left, ⊤)ˣ} (h : WeilIs A L n x y c) : WeilIs A L (n * d) x y (c ^ d) := by
  refine weilIs_of_local hG hA hL fun p => ?_
  obtain ⟨V, hV, ⟨θx, θy, ex, ey⟩, H⟩ := h p
  obtain ⟨θx', fx, vx⟩ := exists_theta_pow d θx
  obtain ⟨θy', fy, vy⟩ := exists_theta_pow d θy
  refine ⟨V, hV, θx', θy', fx.trans ex, fy.trans ey, (commIsOf_iff hL _ _ _).2 fun Z t a z J hJ => ?_⟩
  have e := (commIsOf_iff hL _ _ _).1 (H θx θy ex ey) Z t a z J hJ
  have e' : unitRes V (c ^ d) = unitRes V c ^ d := map_pow _ _ _
  rw [e', map_pow, ← e, commVal, commVal, vx, vx, vy, vy, fx, fy]
  simp only [mul_pow, inv_pow]
end GlobalTheory.WeilIsogeny
