-- Prove2me | solution 1 for GlobalTheory.groupRing_hom_const_of_laurent
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T16:17:25.848014+00:00
-- url     : https://prove2.me/submissions/d74115b7-b09a-45d9-9c7d-c73541dd2043

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_AbelianSchemeQuotients_IsAbelianScheme
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_DimSplitPf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_GeometricallyIntegralIffGeometricallyConnectedOf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_HomBaseChangeBijectiveOfLeNilradical
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_LocallyOfFinitePresentationDiagMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_BijectiveRestrictPointsOfEtaleOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_GroupRingHomConstOfLaurent
import Theorems.Thm_GlobalTheory_GroupRingConst_pt_single
import Theorems.Thm_GlobalTheory_GroupRingConst_pt_comp_algebraMap
import Theorems.Thm_GlobalTheory_GroupRingConst_powChar_apply
import Theorems.Thm_GlobalTheory_GroupRingConst_eq_prod_powChar
import Theorems.Thm_GlobalTheory_GroupRingConst_family_comp_algebraMap
import Theorems.Thm_GlobalTheory_GroupRingConst_pt_comp_family
import Theorems.Thm_GlobalTheory_GroupRingConst_spec_comp
import Theorems.Thm_GlobalTheory_restrictPoints_val
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.restrictPoints_val


attribute [local simp] GlobalTheory.GroupRingConst.pt_single
attribute [local simp] GlobalTheory.GroupRingConst.powChar_apply
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Semi
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.GroupRingConst
private lemma powChar_one {G X : Type} [CommGroup G] [AddCommGroup X] (l : X →+ ℤ) :
    GlobalTheory.GroupRingConst.powChar l (1 : G) = 1 := by
  refine MonoidHom.ext fun m => ?_
  rw [MonoidHom.one_apply, ← ofAdd_toAdd m, GlobalTheory.GroupRingConst.powChar_apply, one_zpow]
private lemma pt_eq_lemma_2 {R F X : Type} [CommRing R] [CommRing F] [AddCommGroup X]
    (φ : AddMonoidAlgebra R X →+* F) :
    φ = GlobalTheory.GroupRingConst.pt (φ.comp (algebraMap R (AddMonoidAlgebra R X)))
      ((φ.toMonoidHom.comp (AddMonoidAlgebra.of R X)).toHomUnits) := by
  refine AddMonoidAlgebra.ringHom_ext (fun x => ?_) (fun a => ?_)
  · simp [GlobalTheory.GroupRingConst.pt_single, AddMonoidAlgebra.coe_algebraMap]
  · simp [GlobalTheory.GroupRingConst.pt_single, MonoidHom.coe_toHomUnits, AddMonoidAlgebra.of_apply]
    rw [← map_mul, AddMonoidAlgebra.single_mul_single, zero_add, _root_.one_mul]
private lemma step_lemma_3 {S Y : Scheme.{0}} (p : Y ⟶ S)
    (h : ∀ (L : Type) [Field L] (s : Spec (CommRingCat.of L) ⟶ S) (f : Spec (CommRingCat.of (AddMonoidAlgebra L ℤ)) ⟶ Y),
      f ≫ p = Spec.map (CommRingCat.ofHom (algebraMap L (AddMonoidAlgebra L ℤ))) ≫ s →
      ∃ k : Spec (CommRingCat.of L) ⟶ Y, f = Spec.map (CommRingCat.ofHom (algebraMap L (AddMonoidAlgebra L ℤ))) ≫ k)
    {R X : Type} [CommRing R] [AddCommGroup X]
    (s : Spec (CommRingCat.of R) ⟶ S) (f : Spec (CommRingCat.of (AddMonoidAlgebra R X)) ⟶ Y)
    (hf : f ≫ p = Spec.map (CommRingCat.ofHom (algebraMap R (AddMonoidAlgebra R X))) ≫ s)
    (L : Type) [Field L] (r : R →+* L) (c : Multiplicative X →* Lˣ) (l : X →+ ℤ) (u : Lˣ) :
    Spec.map (CommRingCat.ofHom (GlobalTheory.GroupRingConst.pt r (c * GlobalTheory.GroupRingConst.powChar l u))) ≫ f =
      Spec.map (CommRingCat.ofHom (GlobalTheory.GroupRingConst.pt r c)) ≫ f := by
  obtain ⟨k, hk⟩ := h L (Spec.map (CommRingCat.ofHom r) ≫ s)
    (Spec.map (CommRingCat.ofHom (GlobalTheory.GroupRingConst.family r c l)) ≫ f) (by
      rw [Category.assoc, hf, ← Category.assoc, GlobalTheory.GroupRingConst.spec_comp, GlobalTheory.GroupRingConst.family_comp_algebraMap, ← GlobalTheory.GroupRingConst.spec_comp,
        Category.assoc])
  have key : ∀ v : Lˣ, Spec.map (CommRingCat.ofHom (GlobalTheory.GroupRingConst.pt r (c * GlobalTheory.GroupRingConst.powChar l v))) ≫ f = k := by
    intro v
    rw [← GlobalTheory.GroupRingConst.pt_comp_family, ← GlobalTheory.GroupRingConst.spec_comp, Category.assoc, hk, ← Category.assoc, GlobalTheory.GroupRingConst.spec_comp,
      GlobalTheory.GroupRingConst.pt_comp_algebraMap, CommRingCat.ofHom_id, Spec.map_id, Category.id_comp]
  have h1 := key 1
  rw [powChar_one, _root_.mul_one] at h1
  rw [key u, h1]
private lemma chain_lemma_4 {S Y : Scheme.{0}} (p : Y ⟶ S)
    (h : ∀ (L : Type) [Field L] (s : Spec (CommRingCat.of L) ⟶ S) (f : Spec (CommRingCat.of (AddMonoidAlgebra L ℤ)) ⟶ Y),
      f ≫ p = Spec.map (CommRingCat.ofHom (algebraMap L (AddMonoidAlgebra L ℤ))) ≫ s →
      ∃ k : Spec (CommRingCat.of L) ⟶ Y, f = Spec.map (CommRingCat.ofHom (algebraMap L (AddMonoidAlgebra L ℤ))) ≫ k)
    {R X : Type} [CommRing R] [AddCommGroup X]
    (s : Spec (CommRingCat.of R) ⟶ S) (f : Spec (CommRingCat.of (AddMonoidAlgebra R X)) ⟶ Y)
    (hf : f ≫ p = Spec.map (CommRingCat.ofHom (algebraMap R (AddMonoidAlgebra R X))) ≫ s) [Module.Free ℤ X] [Module.Finite ℤ X]
    (L : Type) [Field L] (r : R →+* L) (c : Multiplicative X →* Lˣ) :
    Spec.map (CommRingCat.ofHom (GlobalTheory.GroupRingConst.pt r c)) ≫ f = Spec.map (CommRingCat.ofHom (GlobalTheory.GroupRingConst.pt r 1)) ≫ f := by
  classical
  let b := Module.Free.chooseBasis ℤ X
  have key : ∀ t : Finset (Module.Free.ChooseBasisIndex ℤ X),
      Spec.map (CommRingCat.ofHom (GlobalTheory.GroupRingConst.pt r (∏ i ∈ t,
        GlobalTheory.GroupRingConst.powChar (b.coord i).toAddMonoidHom (c (Multiplicative.ofAdd (b i)))))) ≫ f =
      Spec.map (CommRingCat.ofHom (GlobalTheory.GroupRingConst.pt r 1)) ≫ f := by
    intro t
    induction t using Finset.induction_on with
    | empty => rw [Finset.prod_empty]
    | @insert i t hi ih =>
      rw [Finset.prod_insert hi, _root_.mul_comm (GlobalTheory.GroupRingConst.powChar _ _), step_lemma_3 p h s f hf, ih]
  conv_lhs => rw [GlobalTheory.GroupRingConst.eq_prod_powChar b c]
  exact key Finset.univ
private lemma pts_lemma_5 {S Y : Scheme.{0}} (p : Y ⟶ S)
    (h : ∀ (L : Type) [Field L] (s : Spec (CommRingCat.of L) ⟶ S) (f : Spec (CommRingCat.of (AddMonoidAlgebra L ℤ)) ⟶ Y),
      f ≫ p = Spec.map (CommRingCat.ofHom (algebraMap L (AddMonoidAlgebra L ℤ))) ≫ s →
      ∃ k : Spec (CommRingCat.of L) ⟶ Y, f = Spec.map (CommRingCat.ofHom (algebraMap L (AddMonoidAlgebra L ℤ))) ≫ k)
    {R X : Type} [CommRing R] [AddCommGroup X]
    (s : Spec (CommRingCat.of R) ⟶ S) (f : Spec (CommRingCat.of (AddMonoidAlgebra R X)) ⟶ Y)
    (hf : f ≫ p = Spec.map (CommRingCat.ofHom (algebraMap R (AddMonoidAlgebra R X))) ≫ s) [Module.Free ℤ X] [Module.Finite ℤ X]
    (L : Type) [Field L] (φ : AddMonoidAlgebra R X →+* L) :
    Spec.map (CommRingCat.ofHom φ) ≫ f = Spec.map (CommRingCat.ofHom φ) ≫
      Spec.map (CommRingCat.ofHom (algebraMap R (AddMonoidAlgebra R X))) ≫
        Spec.map (CommRingCat.ofHom (GlobalTheory.GroupRingConst.pt (RingHom.id R) 1)) ≫ f := by
  rw [← Category.assoc, ← Category.assoc, GlobalTheory.GroupRingConst.spec_comp, GlobalTheory.GroupRingConst.spec_comp]
  have e1 : (φ.comp (algebraMap R (AddMonoidAlgebra R X))).comp
      (GlobalTheory.GroupRingConst.pt (RingHom.id R) (1 : Multiplicative X →* Rˣ)) =
      GlobalTheory.GroupRingConst.pt (φ.comp (algebraMap R (AddMonoidAlgebra R X))) (1 : Multiplicative X →* Lˣ) := by
    refine AddMonoidAlgebra.ringHom_ext (fun x => ?_) (fun a => ?_) <;> simp [GlobalTheory.GroupRingConst.pt_single]
  rw [e1]
  conv_lhs => rw [pt_eq_lemma_2 φ]
  exact chain_lemma_4 p h s f hf L _ _
end GlobalTheory.GroupRingConst
end

set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Semi
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.GroupRingConst
namespace GlobalTheory
theorem _root_.solution {S Y : Scheme.{0}} (p : Y ⟶ S) [IsSeparated p]
    (h : ∀ (L : Type) [Field L] (s : Spec (CommRingCat.of L) ⟶ S) (f : Spec (CommRingCat.of (AddMonoidAlgebra L ℤ)) ⟶ Y),
      f ≫ p = Spec.map (CommRingCat.ofHom (algebraMap L (AddMonoidAlgebra L ℤ))) ≫ s →
      ∃ k : Spec (CommRingCat.of L) ⟶ Y, f = Spec.map (CommRingCat.ofHom (algebraMap L (AddMonoidAlgebra L ℤ))) ≫ k)
    (R : Type) [CommRing R] [IsDomain R] (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X]
    (s : Spec (CommRingCat.of R) ⟶ S) (f : Spec (CommRingCat.of (AddMonoidAlgebra R X)) ⟶ Y)
    (hf : f ≫ p = Spec.map (CommRingCat.ofHom (algebraMap R (AddMonoidAlgebra R X))) ≫ s) :
    ∃ k : Spec (CommRingCat.of R) ⟶ Y, f = Spec.map (CommRingCat.ofHom (algebraMap R (AddMonoidAlgebra R X))) ≫ k := by
  classical
  have : UniqueSums X := UniqueSums.of_injective_addHom
    (Module.Free.chooseBasis ℤ X).repr.toLinearMap.toAddMonoidHom.toAddHom
    (Module.Free.chooseBasis ℤ X).repr.injective inferInstance
  have hcomp : (pt (RingHom.id R) (1 : Multiplicative X →* Rˣ)).comp
      (algebraMap R (AddMonoidAlgebra R X)) = RingHom.id R := pt_comp_algebraMap _ _
  refine ⟨Spec.map (CommRingCat.ofHom (pt (RingHom.id R) 1)) ≫ f, ?_⟩
  refine ext_of_fromSpecResidueField_eq _ _ p Set.univ dense_univ (fun x _ => ?_) ?_
  · obtain ⟨φ, hφ⟩ : ∃ φ : AddMonoidAlgebra R X →+*
        ((Spec (CommRingCat.of (AddMonoidAlgebra R X))).residueField x),
        Spec.map (CommRingCat.ofHom φ) = (Spec (CommRingCat.of (AddMonoidAlgebra R X))).fromSpecResidueField x :=
      ⟨(Spec.preimage ((Spec (CommRingCat.of (AddMonoidAlgebra R X))).fromSpecResidueField x)).hom,
        by rw [CommRingCat.ofHom_hom, Spec.map_preimage]⟩
    rw [← hφ]
    exact pts_lemma_5 p h s f hf _ φ
  · rw [hf, Category.assoc, Category.assoc, hf,
      ← Category.assoc _ (Spec.map (CommRingCat.ofHom (algebraMap R (AddMonoidAlgebra R X)))), spec_comp, hcomp,
      CommRingCat.ofHom_id, Spec.map_id, Category.id_comp]
end GlobalTheory
