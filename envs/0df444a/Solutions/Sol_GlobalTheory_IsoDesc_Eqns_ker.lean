-- Prove2me | solution 1 for GlobalTheory.IsoDesc.Eqns.ker
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T15:51:03.531062+00:00
-- url     : https://prove2.me/submissions/35664a14-0ace-4145-b03b-71828eba999b

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
import Theorems.Thm_GlobalTheory_IsoDesc_IsQuot_trans
import Theorems.Thm_GlobalTheory_UU_IsWt_mul
import Theorems.Thm_GlobalTheory_UU_TorusCompat_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_isCub_cubV


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
namespace Eqns
theorem _root_.solution (mul : ∀ (T : Over S') (x y : T ⟶ B'), toBase hβ (x * y) = toBase hβ x * toBase hβ y)
    {T : Over S'} {z : T.left} {I J} (hI : Good M'.L.L z I) (hJ : Good M.L.L z J) {A : Type} [Group A]
    {π : A → (T ⟶ B')} {V : A → (T.left.presheaf.stalk z)ˣ} (h : Eqns M' M hβ z I J π V) {t : A} (ht : π t = 1) :
    V t = V t⁻¹ ∧ ∀ y u, V (t * y) * V (t * u) * V (y * u) * V 1 = V (t * y * u) * V t * V y * V u := by
  have o : toBase hβ (1 : T ⟶ B') = 1 := map_one (toBaseHom mul T)
  constructor
  · have a := h.2.1 t
    have o' : (1 : T ⟶ B').left ≫ β = (1 : Over.mk (T.hom ≫ f) ⟶ B).left := congrArg (fun a => a.left) o
    have c := M.val_sym_one (T := Over.mk (T.hom ≫ f)) hJ
    rw [ht, M'.val_sym_one hI, o', _root_.mul_one] at a
    exact ((_root_.one_mul _).symm.trans (congrArg (· * V t) c.symm)).trans a
  · intro y u
    have a := h.2.2 t y u
    have c : @id (T.left.presheaf.stalk z)ˣ (cubV M.c (T := Over.mk (T.hom ≫ f)) z J 1
      (toBase hβ (π y)) (toBase hβ (π u))) = 1 := (isCub_cubV M.c (T := Over.mk (T.hom ≫ f)) hJ).face _ _
    rwa [ht, o, c, (isCub_cubV M'.c hI).face, _root_.one_mul, _root_.mul_one] at a
end Eqns
end GlobalTheory.IsoDesc
