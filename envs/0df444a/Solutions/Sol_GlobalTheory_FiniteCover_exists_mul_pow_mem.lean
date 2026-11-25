-- Prove2me | solution 1 for GlobalTheory.FiniteCover.exists_mul_pow_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:45:29.456344+00:00
-- url     : https://prove2.me/submissions/95cddaf4-d070-42bb-867f-c9539f5f9876

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PointEqOfSubsingleton
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsCommonMultiple
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsSecValEqIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_FinrankSecPullSandwich
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory GlobalTheory.FiniteCover
variable {X X' : Scheme.{0}} [IsIntegral X] [IsIntegral X']
namespace GlobalTheory.FiniteCover
theorem _root_.solution {D D' : X.Opens} (hD : IsAffineOpen D) (h : genericPoint X ∈ D)
    (h' : genericPoint X ∈ D') (r : Γ(X, D)) (hr : toField h r ≠ 0) (hle : X.basicOpen r ≤ D')
    (c : Γ(X, D')) : ∃ m : ℕ, toField h' c * toField h r ^ m ∈ (toField h).range := by
  have hb : genericPoint X ∈ X.basicOpen r :=
    (Scheme.mem_basicOpen X r _ h).2 (isUnit_iff_ne_zero.2 hr)
  have := hD.isLocalization_basicOpen r
  obtain ⟨m, b, e⟩ := IsLocalization.Away.surj r (rs X hle c)
  have e' : toField hb (rs X hle c * rs X (X.basicOpen_le r) r ^ m) =
      toField hb (rs X (X.basicOpen_le r) b) := congrArg (toField hb) e
  rw [map_mul, map_pow, toField_rs, toField_rs, toField_rs] at e'
  exact ⟨m, b, e'.symm⟩
end GlobalTheory.FiniteCover
