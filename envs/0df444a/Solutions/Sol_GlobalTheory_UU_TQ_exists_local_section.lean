-- Prove2me | solution 1 for GlobalTheory.UU.TQ.exists_local_section
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:07:25.936294+00:00
-- url     : https://prove2.me/submissions/c2a68b8b-754e-46a2-bc6b-f6202bfc52d8

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PointEqOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueTorusCompat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsAffineOpenAndBijectiveOfWeightUnits
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsAffineWeightUnits
import Theorems.Thm_GlobalTheory_UU_TQ_exists_affine_weight_units
import Theorems.Thm_GlobalTheory_UU_CubWeil_comp
import Theorems.Thm_GlobalTheory_UU_IsCPMap_comp
import Theorems.Thm_GlobalTheory_UU_TorusCompat_trans
import Theorems.Thm_GlobalTheory_WeilCube_IsRatio_comp
import Theorems.Thm_GlobalTheory_isAffineOpen_and_bijective_of_weight_units
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans


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
open GlobalTheory GlobalTheory.UU
variable {S : Scheme.{0}} {X : Type} [AddCommGroup X]
namespace GlobalTheory.UU
namespace TQ
theorem _root_.solution [Module.Free ℤ X] [Module.Finite ℤ X] {G : Over S} [GrpObj G] (Q : TQ G X)
    (b : Q.B.left) : ∃ (V : Q.B.left.Opens) (hV : IsAffineOpen V), b ∈ V ∧
      ∃ s : Spec Γ(Q.B.left, V) ⟶ G.left, s ≫ Q.q.left = hV.fromSpec := by
  obtain ⟨V, hV, hb, u, hu⟩ := Q.exists_affine_weight_units b
  have := Q.q_affine
  obtain ⟨hU, hbij⟩ := isAffineOpen_and_bijective_of_weight_units S X G Q.B Q.q Q.i Q.q_hom Q.i_hom Q.q_flat Q.q_surj
    inferInstance Q.isKernel V hV u hu
  let φ := RingEquiv.ofBijective _ hbij
  let ε : AddMonoidAlgebra Γ(Q.B.left, V) X →+* Γ(Q.B.left, V) :=
    (AddMonoidAlgebra.lift Γ(Q.B.left, V) Γ(Q.B.left, V) X 1).toRingHom
  let r : Γ(G.left, Q.q.left ⁻¹ᵁ V) ⟶ Γ(Q.B.left, V) := CommRingCat.ofHom (ε.comp φ.symm.toRingHom)
  have hr : Q.q.left.appLE V _ le_rfl ≫ r = 𝟙 _ := by
    rw [← Scheme.Hom.app_eq_appLE]
    ext a
    have h : φ (AddMonoidAlgebra.single 0 a) = (Q.q.left.app V).hom a :=
      (AddMonoidAlgebra.liftNC_single _ _ 0 a).trans
        ((congrArg (_ * ·) (((Units.coeHom _).comp u).map_one)).trans (_root_.mul_one _))
    change ε (φ.symm ((Q.q.left.app V).hom a)) = a
    rw [← h, RingEquiv.symm_apply_apply]
    simp [ε]
  refine ⟨V, hV, hb, Spec.map r ≫ hU.fromSpec, ?_⟩
  rw [Category.assoc, ← IsAffineOpen.SpecMap_appLE_fromSpec Q.q.left hV hU le_rfl, ← Category.assoc,
    ← Spec.map_comp, hr, Spec.map_id, Category.id_comp]
end TQ
end GlobalTheory.UU
