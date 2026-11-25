-- Prove2me | solution 1 for GlobalTheory.CubeLift.Reduces.even
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T18:07:15.795985+00:00
-- url     : https://prove2.me/submissions/89d816d5-9604-43f4-ba5f-6e9e0a97ef46

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PointEqOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueTorusCompat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_IsNilpotentOfRd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_EvSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsGenLiftOfIsNilpotent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ThickenedPointToTorusExtensionGenerator
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsEvenCubicalTrivialisationLiftNilpotent
import Theorems.Thm_GlobalTheory_CubeLift_exists_odd
import Theorems.Thm_GlobalTheory_CubeLift_odd_alg
import Theorems.Thm_GlobalTheory_CubeLift_odd_red_alg
import Theorems.Thm_GlobalTheory_CubeLift_up_comp
import Theorems.Thm_GlobalTheory_CubeLift_eq_one_of_dif
import Theorems.Thm_GlobalTheory_Descent_freeIso_hom
import Theorems.Thm_GlobalTheory_QCoh_germLinear_apply
import Theorems.Thm_GlobalTheory_QCoh_resBasicOpen_apply
import Theorems.Thm_GlobalTheory_QCoh_resLinear_apply
import Theorems.Thm_GlobalTheory_TorusCoord_IsPointOf_pull
import Theorems.Thm_GlobalTheory_UU_TorusCompat_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_HasGen_gen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_HasGen_pull
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_unit_ext
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Pdiv_PullbackComparison_unit_ext
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.Descent.freeIso_hom
attribute [local simp] GlobalTheory.QCoh.germLinear_apply
attribute [local simp] GlobalTheory.QCoh.resBasicOpen_apply
attribute [local simp] GlobalTheory.QCoh.resLinear_apply



set_option autoImplicit false
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
noncomputable section
open GlobalTheory GlobalTheory.CubeLift
open SplitTorus (bcMap)
variable {A : Type} [CommRing A] {J : Ideal A} {X : Type} [AddCommGroup X]
  {G : Over (Spec (CommRingCat.of A))} [GrpObj G] [IsCommMonObj G]
  {G₀ : Over (Spec (CommRingCat.of (A ⧸ J)))} [GrpObj G₀] [IsCommMonObj G₀]
  {F : G₀.left ⟶ G.left} {hw : F ≫ G.hom = G₀.hom ≫ red J} {P : CP G} {P₀ : CP G₀}
  {w : LB.Iso P₀.L.L (P.L.L.pull F)} {i : splitTorus _ X ⟶ G} {i₀ : splitTorus _ X ⟶ G₀}
namespace GlobalTheory.CubeLift
namespace Reduces
theorem _root_.solution [IsMonHom i] [IsMonHom i₀] (hJ : IsNilpotent J) (h : IsCPMap P₀ P (red J) F hw w)
    (hi : bcMap (red J) X ≫ i.left = i₀.left ≫ F) {σ₀ : CubTriv P₀.c i₀} (h₀ : σ₀.Even) {σ : CubTriv P.c i}
    (hr : Reduces w σ.s σ₀) : σ.Even := by
  obtain ⟨E, hE⟩ := exists_odd P σ.s σ.gen
  have e : E = 1 := by
    refine eq_one_of_dif hJ E (unit_ext fun z _ => ?_) fun T x y u => unit_ext fun z _ => ?_
    · obtain ⟨C, hC⟩ := exists_good_pt P.L.isLB z
      obtain ⟨C₀, hC₀⟩ := exists_good_pt P₀.L.isLB z
      let T := splitTorus (Spec (CommRingCat.of (A ⧸ J))) X
      have e := hE _ (up T (𝟙 T)) z C hC
      rw [up_comp (hw := hw) hi, ← map_inv] at e
      obtain ⟨W, hW⟩ : ∃ W : (T ⟶ G₀) → (T.left.presheaf.stalk z)ˣ,
        ∀ x, W x = gw w x.left z (C (x.left ≫ F)) (C₀ x.left) := ⟨_, fun _ => rfl⟩
      have r : ∀ x, val σ.s (up T x).left z C = _ := hr T z C₀ C hC₀ hC W hW
      have c := (h.vals T z C₀ C hC₀ hC W hW).2.1 (𝟙 T ≫ i₀)
      rw [← GrpObj.inv_comp] at c
      have e' := odd_red_alg (h₀ T (𝟙 T) z C₀ hC₀) c ((r _).symm.trans (e.trans
        (congrArg (_ * ·) (congrArg₂ (· * ·) rfl (r _)))))
      rw [map_one, ← gm_top, ← Category.id_comp (bcMap _ _)]
      exact e'
    · obtain ⟨C, hC⟩ := exists_good_pt P.L.isLB z
      have a := σ.cub T x⁻¹ y⁻¹ u⁻¹ z C hC
      have b := P.sym_cub T (x ≫ i) (y ≫ i) (u ≫ i) z C hC
      simp only [← MonObj.mul_comp, ← GrpObj.inv_comp] at b
      rw [dif]
      simp only [map_mul, map_div, ← gm_top, map_one]
      exact odd_alg (σ := fun a : T ⟶ splitTorus _ X => val σ.s a.left z C)
        (s := fun a => val P.sym (a ≫ i).left z C) (E := fun a => gm a.left z ⊤ E) (fun a => hE T a z C hC)
        (σ.cub T x y u z C hC) a b
  intro T x z C hC
  rw [hE T x z C hC, e, map_one, _root_.one_mul]
end Reduces
end GlobalTheory.CubeLift
