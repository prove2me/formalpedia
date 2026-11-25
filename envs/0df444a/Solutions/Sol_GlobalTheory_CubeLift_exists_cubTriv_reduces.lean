-- Prove2me | solution 1 for GlobalTheory.CubeLift.exists_cubTriv_reduces
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T18:09:04.180722+00:00
-- url     : https://prove2.me/submissions/4eef139b-d3e3-499c-a360-84094a3cc2bf

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
import Theorems.Thm_GlobalTheory_CubeLift_exists_defect
import Theorems.Thm_GlobalTheory_CubeLift_defect_alg
import Theorems.Thm_GlobalTheory_CubeLift_cub_red_alg
import Theorems.Thm_GlobalTheory_CubeLift_scale_alg
import Theorems.Thm_GlobalTheory_CubeLift_exists_reduces
import Theorems.Thm_GlobalTheory_CubeLift_up_comp
import Theorems.Thm_GlobalTheory_CubeLift_Reduces_scale
import Theorems.Thm_GlobalTheory_CubeLift_exists_dif
import Theorems.Thm_GlobalTheory_Descent_freeIso_hom
import Theorems.Thm_GlobalTheory_QCoh_germLinear_apply
import Theorems.Thm_GlobalTheory_QCoh_resBasicOpen_apply
import Theorems.Thm_GlobalTheory_QCoh_resLinear_apply
import Theorems.Thm_GlobalTheory_SplitTorus_torusMap_bcMap
import Theorems.Thm_GlobalTheory_TorusCoord_IsPointOf_pull
import Theorems.Thm_GlobalTheory_UU_TorusCompat_trans
import Theorems.Thm_P2M_GlobalTheory_CubeLift_pt_p__23b979d5f8a6
import Theorems.Thm_P2M_GlobalTheory_CubeLift_pt_p__5876b0f23257
import Theorems.Thm_P2M_GlobalTheory_CubeLift_pt_p__b32ea6907c6f
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_HasGen_pull
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_scaleGen_isGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_isCub_cubV
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
theorem _root_.solution [IsMonHom i] [IsMonHom i₀] (hJ : IsNilpotent J) (h : IsCPMap P₀ P (red J) F hw w)
    (hi : bcMap (red J) X ≫ i.left = i₀.left ≫ F) (σ₀ : CubTriv P₀.c i₀) :
    ∃ σ : CubTriv P.c i, Reduces w σ.s σ₀ := by
  obtain ⟨t, ht, hr⟩ := exists_reduces hJ h hi σ₀
  obtain ⟨D, hD⟩ := exists_defect P.c t ht (SplitTorus.torusMap _ (p₁ (X := X))) (SplitTorus.torusMap _ p₂)
    (SplitTorus.torusMap _ p₃)
  have hD' : ∀ (T : Over (Spec (CommRingCat.of A))) (z : T.left) (C), Good P.L.L z C →
      ∀ x y u : T ⟶ splitTorus _ X, val t (x * y * u).left z C * val t x.left z C * val t y.left z C *
        val t u.left z C = gm (𝟙 T.left) z ⊤ (app (pt x y u).left D) * (cubV P.c z C (x ≫ i) (y ≫ i) (u ≫ i) *
          val t (x * y).left z C * val t (x * u).left z C * val t (y * u).left z C) := fun T z C hC x y u => by
    have e := hD T (pt x y u) z C hC
    rwa [pt_p₁, pt_p₂, pt_p₃, gm_top] at e
  have alg := fun (T : Over (Spec (CommRingCat.of A))) (z : T.left) =>
    defect_alg (isCub_cubV P.c (exists_good_pt P.L.isLB z).choose_spec)
      (MonoidHom.mk' (fun x : T ⟶ splitTorus _ X => x ≫ i) fun x y => MonObj.mul_comp x y i)
      (fun x => val t x.left z _) (fun x y u => gm (𝟙 T.left) z ⊤ (app (pt x y u).left D))
      (hD' T z _ (exists_good_pt P.L.isLB z).choose_spec)
  have h₀ : app (bcMap (red J) (X × X × X)) D = 1 := unit_ext fun z _ => by
    obtain ⟨C, hC⟩ := exists_good_pt P.L.isLB z
    obtain ⟨C₀, hC₀⟩ := exists_good_pt P₀.L.isLB z
    let T := splitTorus (Spec (CommRingCat.of (A ⧸ J))) (X × X × X)
    have k : ∀ p : X →+ X × X × X, up T (𝟙 T) ≫ SplitTorus.torusMap _ p = up T (SplitTorus.torusMap _ p) :=
      fun p => Over.OverMorphism.ext (((congrArg (· ≫ _) (Category.id_comp _)).trans
        (SplitTorus.torusMap_bcMap (red J) p).symm))
    have e := hD _ (up T (𝟙 T)) z C hC
    rw [k, k, k, up_comp (hw := hw) hi, up_comp (hw := hw) hi, up_comp (hw := hw) hi] at e
    simp only [← map_mul] at e
    obtain ⟨W, hW⟩ : ∃ W : (T ⟶ G₀) → (T.left.presheaf.stalk z)ˣ,
      ∀ x, W x = gw w x.left z (C (x.left ≫ F)) (C₀ x.left) := ⟨_, fun _ => rfl⟩
    have r : ∀ x, val t (up T x).left z C = _ := hr T z C₀ C hC₀ hC W hW
    have c := (h.vals T z C₀ C hC₀ hC W hW).2.2 (SplitTorus.torusMap _ p₁ ≫ i₀) (SplitTorus.torusMap _ p₂ ≫ i₀)
      (SplitTorus.torusMap _ p₃ ≫ i₀)
    simp only [← MonObj.mul_comp] at c
    have e' := cub_red_alg (σ₀.cub T _ _ _ z C₀ hC₀) c (r _) (r _) (r _) (r _) (r _) (r _) (r _) e
    rw [map_one, ← gm_top, ← Category.id_comp (bcMap _ _)]
    exact e'
  obtain ⟨g, hg, hg'⟩ := exists_dif hJ D (fun T x y u => unit_ext fun z _ => (alg T z).1 x y u)
    (fun T x y u => unit_ext fun z _ => (alg T z).2.1 x y u)
    (fun T x y u v => unit_ext fun z _ => by rw [map_mul, map_mul]; exact (alg T z).2.2 x y u v) h₀
  refine ⟨⟨scaleGen g⁻¹ t, scaleGen_isGen _ ht, fun T x y u z C hC => ?_⟩, hr.scale (by rw [map_inv, hg, inv_one])⟩
  have e := hD' T z C hC x y u
  rw [hg', dif] at e
  simp only [map_mul, map_div, ← gm_top] at e
  simp only [val_scaleGen _ _ _ hC, map_inv]
  exact scale_alg e
end GlobalTheory.CubeLift
