-- Prove2me | solution 1 for GlobalTheory.UU.IsCPMap.comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T14:45:54.593485+00:00
-- url     : https://prove2.me/submissions/1343a8b3-f3d3-4e7d-9b2f-e198843ab62f

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_LinCombTrivG
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsSplitTorusPointsMulEquiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_LocallyOfFinitePresentationDiagMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_CubicalSymmetryTransport
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_WeilIsGrpPullbackIff
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PointEqOfSubsingleton
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsCub_comm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_Tri_pgen_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_isGen_iff


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
open GlobalTheory GlobalTheory.UU
variable {S S' : Scheme.{0}}
attribute [instance] TQ.grp TQ.comm
variable {S'' : Scheme.{0}} {G : Over S} {G' : Over S'} {G'' : Over S''} [GrpObj G] [IsCommMonObj G] [GrpObj G']
  [IsCommMonObj G'] [GrpObj G''] [IsCommMonObj G'']
  {f : S' ⟶ S} {F : G'.left ⟶ G.left} {hw : F ≫ G.hom = G'.hom ≫ f}
namespace GlobalTheory.UU
namespace IsCPMap
theorem _root_.solution {P : CP G} {P' : CP G'} {P'' : CP G''} {f' : S'' ⟶ S'} {F' : G''.left ⟶ G'.left}
    {hw' : F' ≫ G'.hom = G''.hom ≫ f'} {w : LB.Iso P'.L.L (P.L.L.pull F)} {w' : LB.Iso P''.L.L (P'.L.L.pull F')}
    (h : IsCPMap P' P f F hw w) (h' : IsCPMap P'' P' f' F' hw' w')
    (hw'' : (F' ≫ F) ≫ G.hom = G''.hom ≫ f' ≫ f) {w'' : LB.Iso P''.L.L (P.L.L.pull (F' ≫ F))} (Tw : Tri w w' w'') :
    IsCPMap P'' P (f' ≫ f) (F' ≫ F) hw'' w'' := by
  have e : ∀ (T : Over S'') (x : T ⟶ G''), toBase hw'' x =
      (Over.homMk (𝟙 T.left) (by simp) : Over.mk (T.hom ≫ f' ≫ f) ⟶ Over.mk ((Over.mk (T.hom ≫ f')).hom ≫ f)) ≫
        toBase hw (toBase hw' x) := by
    intro T x
    ext
    simp [toBase]
  have pgen : PGen w'' := Tw.pgen_comp P'.L.isLB ((isGen_iff w).1 h.gen) ((isGen_iff w').1 h'.gen)
  refine ⟨fun T x y => ?_, (isGen_iff w'').2 pgen, ?_⟩
  · rw [e, e, e, h'.mul, h.mul, MonObj.comp_mul]
  · intro T z J'' J hJ'' hJ W'' hW''
    obtain ⟨J', hJ'⟩ := exists_good_pt P'.L.isLB z
    obtain ⟨W₁, hW₁⟩ : ∃ W₁ : (Over.mk (T.hom ≫ f') ⟶ G') → (T.left.presheaf.stalk z)ˣ,
        ∀ y, W₁ y = gw w y.left z (J (y.left ≫ F)) (J' y.left) := ⟨_, fun _ => rfl⟩
    obtain ⟨W, hW⟩ : ∃ W : (T ⟶ G'') → (T.left.presheaf.stalk z)ˣ,
        ∀ x, W x = gw w' x.left z (J' (x.left ≫ F')) (J'' x.left) := ⟨_, fun _ => rfl⟩
    obtain ⟨r1, s1, c1⟩ := h.vals (Over.mk (T.hom ≫ f')) z J' J hJ' hJ W₁ hW₁
    obtain ⟨r2, s2, c2⟩ := h'.vals T z J'' J' hJ'' hJ' W hW
    have t1 : toBase hw' (1 : T ⟶ G'') = 1 := map_one (toBaseHom h'.mul T)
    have tinv : ∀ x : T ⟶ G'', toBase hw' x⁻¹ = (toBase hw' x)⁻¹ := fun x => map_inv (toBaseHom h'.mul T) x
    have tmul : ∀ x y : T ⟶ G'', toBase hw' (x * y) = toBase hw' x * toBase hw' y := h'.mul T
    have tl : ∀ x : T ⟶ G'', (toBase hw' x).left = x.left ≫ F' := fun _ => rfl
    have hrel : ∀ x : T ⟶ G'', W'' x = W₁ (toBase hw' x) * W x := by
      intro x
      have hm1 : F (F' (x.left z)) ∈ P.L.L.U (J (x.left ≫ F' ≫ F)) := hJ _
      have hm2 : F' (x.left z) ∈ P'.L.L.U (J' (x.left ≫ F')) := hJ' _
      have hm3 : x.left z ∈ P''.L.L.U (J'' x.left) := hJ'' _
      rw [hW'', Tw T.left x.left z _ _ _ hm1 hm2 hm3, hW₁, hW, tl, Category.assoc]
    refine ⟨?_, fun x => ?_, fun x y u => ?_⟩
    · simp only [Over.mk_hom] at r1
      rw [hrel, t1, _root_.mul_assoc, ← r2, ← r1, Category.assoc]
    · have s1' := s1 (toBase hw' x)
      have s2' := s2 x
      rw [tl, Category.assoc, ← tinv] at s1'
      rw [hrel, hrel]
      apply Additive.ofMul.injective
      replace s1' := congrArg Additive.ofMul s1'
      replace s2' := congrArg Additive.ofMul s2'
      simp only [ofMul_mul] at s1' s2' ⊢
      linear_combination (norm := abel) s1' + s2'
    · have c1' := c1 (toBase hw' x) (toBase hw' y) (toBase hw' u)
      have c2' := c2 x y u
      have hcub : cubV P.c (T := Over.mk (T.hom ≫ f' ≫ f)) z J (toBase hw'' x) (toBase hw'' y) (toBase hw'' u) =
          cubV P.c z J (toBase hw (toBase hw' x)) (toBase hw (toBase hw' y)) (toBase hw (toBase hw' u)) := by
        unfold cubV
        rw [e, e, e, ← comp_lift, ← comp_lift]
        simp only [Over.comp_left, Over.homMk_left]
        exact congrArg (fun r => val P.c.t r z J) (Category.id_comp _)
      simp only [← tmul, ← t1, id_eq] at c1'
      simp only [id_eq] at c2' ⊢
      rw [hcub]
      simp only [hrel]
      apply Additive.ofMul.injective
      replace c1' := congrArg Additive.ofMul c1'
      replace c2' := congrArg Additive.ofMul c2'
      simp only [ofMul_mul] at c1' c2' ⊢
      linear_combination (norm := abel) c1' + c2'
end IsCPMap
end GlobalTheory.UU
