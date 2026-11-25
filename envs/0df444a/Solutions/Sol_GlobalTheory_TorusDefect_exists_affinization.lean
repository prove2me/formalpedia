-- Prove2me | solution 1 for GlobalTheory.TorusDefect.exists_affinization
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T15:57:26.255144+00:00
-- url     : https://prove2.me/submissions/7ae2cbeb-9cbf-49cb-821d-b39bdc44069f

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ReductionSurjectiveOfIsNilpotent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_LeftEqIffLieVecSmul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_HomBaseChangeBijectiveOfLeNilradical
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsUnitAddMonoidAlgebraIffOfTwoUniqueSums
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsIsMonHomSplitTorusOfSqEqBot
import Theorems.Thm_GlobalTheory_SplitTorus_val_zero
import Theorems.Thm_GlobalTheory_SqZero_UnitInChart_map
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_spMap_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_spMap_id
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_spMap_left
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_isMonHom_of_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_spMap_comp


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
  AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap spMap_left spMap_comp spMap_id)
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (epsR IsLieBasis isMonHom_of_mul)
open scoped CategoryTheory.Obj
open AddMonoidAlgebra (single mapDomainAlgHom)
open GlobalTheory GlobalTheory.TorusDefect
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.SqZero GlobalTheory.Diag
variable {A : Type} [CommRing A] {X Y : Type} [AddCommGroup X] [AddCommGroup Y]
  {C C' : Type} [CommRing C] [Algebra A C] [CommRing C'] [Algebra A C']
namespace GlobalTheory.TorusDefect
theorem _root_.solution (Z : Over (Spec (CommRingCat.of A))) :
    ∃ (C : Type) (_ : CommRing C) (_ : Algebra A C) (p : Z ⟶ sp C),
      (∀ a : Z ⟶ splitTorus (Spec (CommRingCat.of A)) X, ∃ a', p ≫ a' = a) ∧
      ∀ (J : Ideal A) (s : Z.left ⟶ Spec (CommRingCat.of (A ⧸ J))),
        Z.hom = s ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) →
        ∀ j ∈ J, algebraMap A C j = 0 := by
  let inst : Algebra A Γ(Z.left, ⊤) :=
    (Z.hom.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom).toAlgebra
  have e : CommRingCat.ofHom (algebraMap A Γ(Z.left, ⊤)) =
      (Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ Z.hom.appTop := rfl
  have hw : Z.left.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (algebraMap A Γ(Z.left, ⊤))) = Z.hom := by
    rw [e, Spec.map_comp, ← Category.assoc, ← Scheme.toSpecΓ_naturality, Category.assoc,
      toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]
  refine ⟨Γ(Z.left, ⊤), inferInstance, inst, Over.homMk Z.left.toSpecΓ hw, ?_, ?_⟩
  · intro a
    let F : Multiplicative X →* Γ(Z.left, ⊤) :=
      { toFun := fun x => SplitTorus.val a x.toAdd
        map_one' := SplitTorus.val_zero a
        map_mul' := fun x y => SplitTorus.val_add a x.toAdd y.toAdd }
    refine ⟨GlobalTheory.Diag.ofVal _ F, SplitTorus.hom_ext fun x => ?_⟩
    have h1 := GlobalTheory.Diag.charVal_ofVal
      (g := Spec.map (CommRingCat.ofHom (algebraMap A Γ(Z.left, ⊤)))) F x
    unfold GlobalTheory.Diag.charVal at h1
    rw [SplitTorus.val_comp, SplitTorus.val_eq]
    change (Z.left.toSpecΓ.appTop).hom _ = _
    rw [Scheme.toSpecΓ_appTop]
    exact h1
  · intro J s hs j hj
    show Z.hom.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom j) = 0
    rw [hs, Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply,
      SplitTorus.specMap_appTop_apply, CommRingCat.hom_ofHom, Ideal.Quotient.eq_zero_iff_mem.2 hj,
      map_zero, map_zero]
end GlobalTheory.TorusDefect
