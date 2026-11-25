-- Prove2me | solution 1 for GlobalTheory.CubeDescent.val_eq_of_section
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:45:27.6481+00:00
-- url     : https://prove2.me/submissions/b4129619-e78b-432b-83a0-5b8b00496af1

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RosVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_InvariantFunctionsDescend
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_QuotientIsAbelianSchemeOfQuotientScheme
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_CubeDescendsAlongEtaleIsogeny
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gen_unique__84c95b4ccdb0
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_pullGen_isGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_pull


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory GlobalTheory.CubeDescent
variable {S X : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {Q : Over S}
  {φ : K → (Q.left ⟶ X)} {ε : K → ℤ}
namespace GlobalTheory.CubeDescent
theorem _root_.solution (hL : L.IsLB) {u : LB.Gen (LB.LinComb L φ ε)} (hu : u.IsGen)
    {P T : Over S} (p : P ⟶ T) (e : T ⟶ P) (he : e ≫ p = 𝟙 T)
    (hp : Function.Surjective p.left.appTop.hom) (a a' : P ⟶ Q)
    (hF : FormEq (fun k => a'.left ≫ φ k) ε (fun k => a.left ≫ φ k) ε)
    (h : ∀ y J, Good L y J → val u (e ≫ a).left y J = val u (e ≫ a').left y J)
    {T' : Over S} (ρ : T' ⟶ P) (z : T'.left) (J) (hJ : Good L z J) :
    val u (ρ ≫ a).left z J = val u (ρ ≫ a').left z J := by
  have := gen_unique' hL hF p.left e.left (congrArg (fun q => q.left) he) hp
    (DVR.pullGen_isGen _ _ _ _ hu a.left) (DVR.pullGen_isGen _ _ _ _ hu a'.left)
    (fun y J hJ => by rw [val_pull hJ, val_pull hJ]; exact h y J hJ) _ ρ.left z J hJ
  rw [val_pull hJ, val_pull hJ] at this
  exact this
end GlobalTheory.CubeDescent
