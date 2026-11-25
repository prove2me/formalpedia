-- Prove2me | solution 1 for GlobalTheory.UU.UnitRigid.exists_universal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:35:33.116882+00:00
-- url     : https://prove2.me/submissions/ed717b11-2834-4d48-87bc-dc8cb2a1bc87

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PointEqOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueTorusCompat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsCompRedIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsUnitAddMonoidAlgebraIffOfTwoUniqueSums
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RosVal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_EqOneOfGroupLike
import Theorems.Thm_GlobalTheory_UU_UnitRigid_chV_comp
import Theorems.Thm_GlobalTheory_UU_UnitRigid_point_ext
import Theorems.Thm_GlobalTheory_UU_UnitRigid_exists_point
import Theorems.Thm_GlobalTheory_UU_CubWeil_comp
import Theorems.Thm_GlobalTheory_UU_IsCPMap_comp
import Theorems.Thm_GlobalTheory_UU_RingPoint_exists_ringPoint
import Theorems.Thm_GlobalTheory_WeilCube_IsRatio_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_Rosenlicht_over_appTop_comp


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
open GlobalTheory.UU
noncomputable section
open GlobalTheory GlobalTheory.UU GlobalTheory.UU.UnitRigid
variable {S : Scheme.{0}} {X : Type} [AddCommGroup X]
namespace GlobalTheory.UU.UnitRigid
theorem _root_.solution {Y W : Over S} [IsAffine W.left] (y : W ⟶ Y) (u : Γ((splitTorus S X ⊗ Y).left, ⊤)) :
    ∃ g : AddMonoidAlgebra Γ(W.left, ⊤) X, ∀ (Z : Over S) (s : Z ⟶ W) (t : Z ⟶ splitTorus S X)
      (θ : AddMonoidAlgebra Γ(W.left, ⊤) X →+* Γ(Z.left, ⊤)),
      (∀ b, θ (AddMonoidAlgebra.single 0 b) = s.left.appTop.hom b) →
      (∀ χ, θ (AddMonoidAlgebra.single χ 1) = (chV t χ).val) → (lift t (s ≫ y)).left.appTop.hom u = θ g := by
  obtain ⟨U, y₀, e, -, -, H⟩ := RingPoint.exists_ringPoint W (AddMonoidAlgebra Γ(W.left, ⊤) X)
    AddMonoidAlgebra.singleZeroRingHom
  obtain ⟨t₀, ht₀⟩ := exists_point U (e.symm.toMonoidHom.comp (AddMonoidAlgebra.of _ X))
  refine ⟨e ((lift t₀ (y₀ ≫ y)).left.appTop.hom u), fun Z s t θ h₁ h₂ => ?_⟩
  obtain ⟨σ, hσ, hθ⟩ := H Z s θ h₁
  have ht : σ ≫ t₀ = t := point_ext fun χ => by
    rw [chV_comp, hθ, ht₀, ← h₂]
    exact congrArg θ (e.apply_symm_apply _)
  rw [← hθ, ← ht, ← hσ, Category.assoc, ← comp_lift, Rosenlicht.over_appTop_comp]
end GlobalTheory.UU.UnitRigid
