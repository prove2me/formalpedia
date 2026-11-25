-- Prove2me | solution 1 for GlobalTheory.IsoDesc.cubV_toBase_hom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T15:14:44.567592+00:00
-- url     : https://prove2.me/submissions/47540208-04ec-47ac-b057-ff091821e1ec

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PointEqOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueTorusCompat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsUniqueCharacterOfMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_InvariantFunctionsDescend
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_IsCPMapDescends
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
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
noncomputable section
open GlobalTheory GlobalTheory.IsoDesc
variable {S S' : Scheme.{0}} {f : S' ⟶ S} {G B' : Over S'} {B : Over S} [GrpObj G] [IsCommMonObj G] [GrpObj B']
  [IsCommMonObj B'] [GrpObj B] [IsCommMonObj B] {P : CP G} {M' : CP B'} {M : CP B} {q : G ⟶ B'}
  {β : B'.left ⟶ B.left} {hβ : β ≫ B.hom = B'.hom ≫ f}
namespace GlobalTheory.IsoDesc
theorem _root_.solution {L : RigLB B'} (c : CubicalStr B' L) (h : q.left ≫ B'.hom = G.hom ≫ 𝟙 S') {T : Over S'}
    (z : T.left) (J) (x y u : T ⟶ G) :
    cubV c (T := Over.mk (T.hom ≫ 𝟙 S')) z J (toBase h x) (toBase h y) (toBase h u) =
      cubV c z J (x ≫ q) (y ≫ q) (u ≫ q) := by
  let ρ : Over.mk (T.hom ≫ 𝟙 S') ⟶ T := Over.homMk (𝟙 T.left) (by simp)
  have e : ∀ a : T ⟶ G, toBase h a = ρ ≫ a ≫ q := fun a => Over.OverMorphism.ext (Category.id_comp _).symm
  have e' : (lift (toBase h x) (lift (toBase h y) (toBase h u))).left =
      (lift (x ≫ q) (lift (y ≫ q) (u ≫ q))).left := by
    rw [e, e, e, ← comp_lift, ← comp_lift]; exact Category.id_comp _
  exact congrArg (fun r => val (L := L.L) (φ := thφ B' (x3 B')) (ε := thε) c.t r z J) e'
end GlobalTheory.IsoDesc
