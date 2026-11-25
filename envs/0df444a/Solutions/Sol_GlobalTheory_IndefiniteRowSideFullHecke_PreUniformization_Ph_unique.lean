-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.PreUniformization.Ph.unique
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:51:30.863263+00:00
-- url     : https://prove2.me/submissions/64422a46-2708-423a-aecd-21ed6bccc2e2

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PointEqOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_CMModuli_PreUniformization
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_congr
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_sec_ext_val


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.PreUniformization
variable {R : Type} [CommRing R] [IsDomain R]
variable (D : DegPre R) (F : Type) [Field F] [Algebra (FractionRing R) F]
namespace GlobalTheory.IndefiniteRowSideFullHecke.PreUniformization
namespace Ph
theorem _root_.solution {k : ℕ} {y : D.X} {g : GtPtF D F} {w} {s s₁ s₂ : RawFam D F k} (h₁ : Ph D F k y g w s s₁)
    (h₂ : Ph D F k y g w s s₂) : s₁ = s₂ := by
  funext β
  obtain ⟨α, rfl⟩ : ∃ α, β = α + y := ⟨β - y, (sub_add_cancel _ _).symm⟩
  have e : (s₁ (α + y)).f = (s₂ (α + y)).f := funext fun j => sec_ext_val D.P.isLB (fun z J hJ => by
    have a := (h₁.2.2 α _ (fst _ _) (snd _ _) z J hJ).trans (h₂.2.2 α _ (fst _ _) (snd _ _) z J hJ).symm
    rwa [lift_fst_snd] at a) j
  cases hs₁ : s₁ (α + y); cases hs₂ : s₂ (α + y)
  rw [hs₁, hs₂] at e
  congr
end Ph
end GlobalTheory.IndefiniteRowSideFullHecke.PreUniformization
