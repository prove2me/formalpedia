-- Prove2me | solution 1 for OAI.Tachikawa.Construction.XInverseTwist_weight
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T02:50:46.300895+00:00
-- url     : https://prove2.me/submissions/b2f80c15-a57e-41e3-ae96-93280a083883

import Mathlib
import Definitions.Def_Tachikawa
import Definitions.Def_OAIQ116Ta016

section
-- module Solutions.OAIQ116_Tach.Tachikawa_Coresolution
attribute [-instance] _root_.OAI.Tachikawa.DownHom.instAddCommGroupCochain _root_.OAI.Tachikawa.LeftCoinduced.coextend_additive _root_.OAI.Tachikawa.LeftCoinduced.coextend_preservesInjective _root_.OAI.Tachikawa.OuterTensor.restrictionPreservesHomology _root_.OAI.Tachikawa.TotalDualPairing.instTensorSignsNatUp_solutions _root_.OAI.Tachikawa.TotalMap.sourceHasCoproduct _root_.OAI.Tachikawa.downIntTensorSigns
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
set_option backward.isDefEq.respectTransparency false


noncomputable section



namespace Tachikawa
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open CochainComplex

section Shift
variable {C D : Type*} [Category C] [Category D] [HasShift C ℤ] [HasShift D ℤ]
  (F : C ⥤ D) [F.CommShift ℤ] {X Y Z : C} {n : ℤ}
lemma shifted_map_precomp (a : X ⟶ Y) (b : Y ⟶ Z⟦n⟧) :
    ShiftedHom.map (a ≫ b) F = F.map a ≫ ShiftedHom.map b F := by
  simp only [ShiftedHom.map,Functor.map_comp,Category.assoc]
lemma shifted_map_postcomp (a : X ⟶ Y⟦n⟧) (b : Y ⟶ Z) :
    ShiftedHom.map (a ≫ b⟦n⟧') F = ShiftedHom.map a F ≫ (F.map b)⟦n⟧' := by
  simp only [ShiftedHom.map,Functor.map_comp,Category.assoc,
    Functor.commShiftIso_hom_naturality]
end Shift

variable {C D : Type*} [Category C] [Abelian C] [Category D] [Abelian D]
  [HasDerivedCategory C] [HasDerivedCategory D]
  (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  {X Y : C} {K : CochainComplex C ℤ}

lemma derived_roof_map {n : ℤ} (p : K ⟶ (singleFunctor C 0).obj X) [QuasiIso p]
    (f : K ⟶ ((singleFunctor C 0).obj Y)⟦n⟧) :
    (F.mapDerivedCategorySingleFunctor 0).inv.app X ≫
      ShiftedHom.map (inv (DerivedCategory.Q.map p) ≫ ShiftedHom.map f DerivedCategory.Q)
        F.mapDerivedCategory ≫
      ((F.mapDerivedCategorySingleFunctor 0).hom.app Y)⟦n⟧' =
    inv (DerivedCategory.Q.map
      ((F.mapHomologicalComplex (.up ℤ)).map p ≫
        (F.mapCochainComplexSingleFunctor 0).hom.app X)) ≫
      ShiftedHom.map (ShiftedHom.map f (F.mapHomologicalComplex (.up ℤ)) ≫
        ((F.mapCochainComplexSingleFunctor 0).hom.app Y)⟦n⟧') DerivedCategory.Q := by
  let A := F.mapDerivedCategoryFactors
  have hf : ShiftedHom.map (ShiftedHom.map f DerivedCategory.Q) F.mapDerivedCategory =
      A.hom.app K ≫ ShiftedHom.map
        (ShiftedHom.map f (F.mapHomologicalComplex (.up ℤ))) DerivedCategory.Q ≫
          (A.inv.app ((singleFunctor C 0).obj Y))⟦n⟧' := by
    have h := ShiftedHom.map_naturality_2 f A
    simpa only [ShiftedHom.mk₀_comp,ShiftedHom.comp_mk₀,ShiftedHom.comp_map] using h.symm
  have hp : F.mapDerivedCategory.map (inv (DerivedCategory.Q.map p)) ≫ A.hom.app K =
      A.hom.app ((singleFunctor C 0).obj X) ≫
        inv (DerivedCategory.Q.map ((F.mapHomologicalComplex (.up ℤ)).map p)) := by
    apply (cancel_mono (DerivedCategory.Q.map
      ((F.mapHomologicalComplex (.up ℤ)).map p))).mp
    simp only [Category.assoc,IsIso.inv_hom_id,Category.comp_id]
    rw [← F.mapDerivedCategoryFactors_hom_naturality p,← Category.assoc,
      ← F.mapDerivedCategory.map_comp,IsIso.inv_hom_id,F.mapDerivedCategory.map_id,
      Category.id_comp]
  rw [shifted_map_precomp,hf]
  simp only [Category.assoc]
  rw [← Category.assoc _ (A.hom.app K),hp]
  simp only [Category.assoc]
  dsimp only [A]
  have hy : F.mapDerivedCategoryFactors.inv.app ((singleFunctor C 0).obj Y) ≫
      (F.mapDerivedCategorySingleFunctor 0).hom.app Y =
      DerivedCategory.Q.map ((F.mapCochainComplexSingleFunctor 0).hom.app Y) :=
    F.mapDerivedCategoryFactors_inv_app_mapDerivedCategorySingleFunctor_hom_app Y
  have hx : (F.mapDerivedCategorySingleFunctor 0).inv.app X ≫
      F.mapDerivedCategoryFactors.hom.app ((singleFunctor C 0).obj X) =
      DerivedCategory.Q.map ((F.mapCochainComplexSingleFunctor 0).inv.app X) :=
    F.mapDerivedCategorySingleFunctor_inv_app_mapDerivedCategoryFactors_hom_app X
  rw [← Functor.map_comp]
  erw [hy]
  rw [← Category.assoc ((F.mapDerivedCategorySingleFunctor 0).inv.app X)
    (F.mapDerivedCategoryFactors.hom.app ((singleFunctor C 0).obj X))]
  erw [hx]
  have hc : DerivedCategory.Q.map ((F.mapCochainComplexSingleFunctor 0).inv.app X) =
      inv (DerivedCategory.Q.map ((F.mapCochainComplexSingleFunctor 0).hom.app X)) := by
    apply IsIso.eq_inv_of_hom_inv_id
    rw [← DerivedCategory.Q.map_comp,Iso.hom_inv_id_app,DerivedCategory.Q.map_id]
  simp only [Functor.map_comp,IsIso.inv_comp,shifted_map_postcomp,Category.assoc]
  rw [hc]
end Tachikawa



end

end OAI
end

section
-- module Solutions.OAIQ116_Tach.Tachikawa_TwistHom
attribute [-instance] _root_.OAI.Tachikawa.DownHom.instAddCommGroupCochain _root_.OAI.Tachikawa.Enveloping.instAddCommGroupCarrierMulOppositeRightObj _root_.OAI.Tachikawa.Enveloping.instModuleCarrierMulOppositeRightObj_1 _root_.OAI.Tachikawa.LeftCoinduced.coextend_additive _root_.OAI.Tachikawa.LeftCoinduced.coextend_preservesInjective _root_.OAI.Tachikawa.OuterTensor.restrictionPreservesHomology _root_.OAI.Tachikawa.TotalDualPairing.instIsIsoHomologicalComplexNatModuleCatUpComparison _root_.OAI.Tachikawa.TotalDualPairing.instTensorSignsNatUp_solutions _root_.OAI.Tachikawa.TotalMap.sourceHasCoproduct _root_.OAI.Tachikawa.downIntTensorSigns
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
set_option backward.isDefEq.respectTransparency false


noncomputable section

namespace Tachikawa
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open CochainComplex CochainComplex.HomComplex
variable {C D : Type*} [Category C] [Abelian C] [Category D] [Abelian D]
  (F : C ⥤ D) [F.Additive] [F.PreservesProjectiveObjects] [F.PreservesHomology]
  {X : C} (P : ProjectiveResolution X)

lemma mappedResolutionCochainIso_π :
    (mappedResolutionCochainIso F P).hom ≫
      (F.mapHomologicalComplex (.up ℤ)).map P.π' ≫
        (F.mapCochainComplexSingleFunctor 0).hom.app X =
      (mappedResolution F P).π' := by
  ext j
  by_cases hj : j = 0
  · subst j
    dsimp only [mappedResolution, Functor.mapProjectiveResolution,
      Functor.mapHomologicalComplex]
    simp only [HomologicalComplex.comp_f,
      HomologicalComplex.Hom.isoOfComponents_hom_f, mappedResolutionCochainIso,
      mappedResolutionCochainXIso_nonpos F P 0 0 rfl,
      ProjectiveResolution.π'_f_zero, Functor.map_comp]
    simp [mappedResolution,
      Functor.mapCochainComplexSingleFunctor,
      singleMapHomologicalComplex]
    simp only [singleObjXSelf,singleObjXIsoOfEq,eqToIso.inv]
    erw [eqToHom_refl, Category.comp_id, eqToHom_refl, Category.comp_id]
    erw [F.map_id, Category.comp_id]
    try rfl
  · exact (isZero_single_obj_X (.up ℤ) 0 (F.obj X) j hj).eq_of_tgt _ _

omit [F.PreservesProjectiveObjects] [F.PreservesHomology] in
lemma map_toSingle_shifted {K : CochainComplex C ℤ} {Y : C}
    {p n : ℤ} (f : K.X p ⟶ Y) (h : p+n=0) (p' : ℤ) (hp' : p'+1=p)
    (hf : K.d p' p ≫ f = 0) :
    ShiftedHom.map (Cocycle.equivHomShift.symm (Cocycle.toSingleMk f h p' hp' hf))
      (F.mapHomologicalComplex (.up ℤ)) ≫
        ((F.mapCochainComplexSingleFunctor 0).hom.app Y)⟦n⟧' =
      Cocycle.equivHomShift.symm (Cocycle.toSingleMk (F.map f) h p' hp'
        (by simp only [Functor.mapHomologicalComplex_obj_d,← F.map_comp,hf,F.map_zero])) := by
  ext j
  simp [ShiftedHom.map,Cocycle.equivHomShift_symm_apply,
    Cocycle.toSingleMk,Cocycle.homOf,Cocycle.rightShift,
    Cochain.rightShift_v, Cochain.toSingleMk,
    Functor.mapCochainComplexSingleFunctor,singleMapHomologicalComplex]
  by_cases hj : j = p
  · subst j
    simp [Cochain.single,h,HomologicalComplex.XIsoOfEq,
      singleObjXSelf,singleObjXIsoOfEq,eqToHom_map]
  · simp [Cochain.single_v_eq_zero _ _ _ _ _ hj]
end Tachikawa



namespace Tachikawa
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian HomologicalComplex
open CochainComplex CochainComplex.HomComplex
variable {C D : Type*} [Category C] [Abelian C] [Category D] [Abelian D]
  (F : C ⥤ D) [F.Additive] [F.PreservesProjectiveObjects]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  {X Y : C} (P : ProjectiveResolution X)

lemma extMk_hom_roof [HasDerivedCategory C] [HasExt C]
    {n : ℕ} (f : P.complex.X n ⟶ Y) (hf : P.complex.d (n+1) n ≫ f = 0) :
    (P.extMk f (n+1) rfl hf).hom = inv (DerivedCategory.Q.map P.π') ≫
      ShiftedHom.map (Cocycle.equivHomShift.symm
        (Cocycle.toSingleMk ((P.cochainComplexXIso (-n) n rfl).hom ≫ f)
          (by simp) (-((n+1 : ℕ) : ℤ)) (by omega)
          (by
            rw [ProjectiveResolution.cochainComplex_d _ _ _ (n+1) n rfl rfl]
            simp only [Category.assoc,Iso.inv_hom_id_assoc,hf,comp_zero])))
        DerivedCategory.Q := by
  rw [ProjectiveResolution.extMk_hom]
  simp [DerivedCategory.singleFunctorIsoCompQ,ShiftedHom.mk₀_comp,ShiftedHom.comp_mk₀]
  change _ ≫ (CategoryTheory.shiftFunctor (DerivedCategory C) (n : ℤ)).map
    (𝟙 (DerivedCategory.Q.obj ((CochainComplex.singleFunctor C 0).obj Y))) = _
  rw [CategoryTheory.Functor.map_id,Category.comp_id]

lemma mappedResolutionCochain_cocycle {n : ℕ} (f : P.complex.X n ⟶ Y)
    (hf : P.complex.d (n+1) n ≫ f = 0) :
    (mappedResolutionCochainIso F P).hom ≫
      ShiftedHom.map (Cocycle.equivHomShift.symm
        (Cocycle.toSingleMk ((P.cochainComplexXIso (-n) n rfl).hom ≫ f)
          (by simp) (-((n+1 : ℕ) : ℤ)) (by omega)
          (by
            rw [ProjectiveResolution.cochainComplex_d _ _ _ (n+1) n rfl rfl]
            simp only [Category.assoc,Iso.inv_hom_id_assoc,hf,comp_zero])))
        (F.mapHomologicalComplex (.up ℤ)) ≫
      ((F.mapCochainComplexSingleFunctor 0).hom.app Y)⟦(n : ℤ)⟧' =
    Cocycle.equivHomShift.symm (Cocycle.toSingleMk
      (((mappedResolution F P).cochainComplexXIso (-n) n rfl).hom ≫ F.map f)
      (by simp) (-((n+1 : ℕ) : ℤ)) (by omega) (by
        rw [ProjectiveResolution.cochainComplex_d _ _ _ (n+1) n rfl rfl]
        dsimp only [mappedResolution, Functor.mapProjectiveResolution,
          Functor.mapHomologicalComplex]
        simp only [Category.assoc,Iso.inv_hom_id_assoc]
        change _ ≫ F.map (P.complex.d (n+1) n) ≫ F.map f = 0
        rw [← F.map_comp,hf,F.map_zero,comp_zero])) := by
  rw [map_toSingle_shifted]
  rw [← Cocycle.equivHomShift_symm_precomp,← Cocycle.toSingleMk_precomp]
  congr 2
  change (mappedResolutionCochainXIso F P (-n)).hom ≫
    F.map ((P.cochainComplexXIso (-n) n rfl).hom ≫ f) = _
  rw [mappedResolutionCochainXIso_nonpos F P (-n) n rfl]
  dsimp only [mappedResolution, Functor.mapProjectiveResolution,
    Functor.mapHomologicalComplex]
  simp [← F.map_comp_assoc]
end Tachikawa



namespace Tachikawa
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
variable {C D : Type*} [Category C] [Abelian C] [Category D] [Abelian D]
  (F : C ⥤ D) [F.Additive] [F.PreservesProjectiveObjects]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [HasDerivedCategory C] [HasDerivedCategory D] [HasExt C] [HasExt D]
  {X Y : C} (P : ProjectiveResolution X)

lemma mapExactFunctor_extMk {n : ℕ} (f : P.complex.X n ⟶ Y)
    (hf : P.complex.d (n+1) n ≫ f = 0) :
    (P.extMk f (n+1) rfl hf).mapExactFunctor F =
      (mappedResolution F P).extMk (F.map f) (n+1) rfl
        (by change F.map _ ≫ F.map _ = 0; rw [← F.map_comp,hf,F.map_zero]) := by
  apply Ext.ext
  rw [Ext.mapExactFunctor_hom,extMk_hom_roof,derived_roof_map]
  conv_rhs => erw [extMk_hom_roof (mappedResolution F P)]
  have hπ := mappedResolutionCochainIso_π F P
  have hc := mappedResolutionCochain_cocycle F P f hf
  have hq := congrArg (fun z => DerivedCategory.Q.map z) hπ
  simp only [Functor.map_comp] at hq
  have hr : inv (DerivedCategory.Q.map (mappedResolution F P).π') ≫
      DerivedCategory.Q.map (mappedResolutionCochainIso F P).hom =
      inv (DerivedCategory.Q.map
        ((F.mapHomologicalComplex (.up ℤ)).map P.π' ≫
          (F.mapCochainComplexSingleFunctor 0).hom.app X)) := by
    apply (cancel_mono (DerivedCategory.Q.map
      ((F.mapHomologicalComplex (.up ℤ)).map P.π' ≫
        (F.mapCochainComplexSingleFunctor 0).hom.app X))).1
    simp only [Functor.map_comp,Category.assoc,IsIso.inv_hom_id]
    rw [hq,IsIso.inv_hom_id]
  dsimp only [mappedResolution] at hc ⊢
  rw [← hc]
  simp only [shifted_map_precomp]
  rw [← Category.assoc (inv (DerivedCategory.Q.map (mappedResolution F P).π')),hr]
end Tachikawa



namespace Tachikawa
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open scoped ModuleCat.Algebra
variable {k R : Type} [Field k] [Ring R] [Algebra k R]
  (F : ModuleCat R ⥤ ModuleCat R) [F.Additive] [F.Linear k]
  [F.PreservesProjectiveObjects] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  {X : ModuleCat R} (P : ProjectiveResolution X) (e : F.obj X ≅ X)

lemma resolutionTwistHom_extMk
    (l : ProjectiveResolution.Hom P (mappedResolution F P) e.inv)
    {n : ℕ} (f : P.complex.X n ⟶ X) (hf : P.complex.d (n+1) n ≫ f = 0) :
    extIso (k := k) e e n ((P.extMk f (n+1) rfl hf).mapExactFunctor F) =
      P.extMk ((resolutionTwistHom (k := k) F P e l.hom).f n f) (n+1) rfl
        (by change P.complex.d (n+1) n ≫ l.hom.f n ≫ F.map f ≫ e.hom = 0
            erw [← l.hom.comm_assoc]
            change l.hom.f (n+1) ≫ F.map (P.complex.d (n+1) n) ≫ F.map f ≫ e.hom = 0
            erw [← F.map_comp_assoc,hf,F.map_zero,zero_comp,comp_zero]) := by
  let := HasDerivedCategory.standard (ModuleCat R)
  change (Ext.mk₀ e.inv).comp
    (((P.extMk f (n+1) rfl hf).mapExactFunctor F).comp (Ext.mk₀ e.hom) (add_zero n))
      (zero_add n) = _
  erw [mapExactFunctor_extMk,(mappedResolution F P).extMk_comp_mk₀,
    ProjectiveResolution.mk₀_comp_extMk _ _ _ _ l]
  rfl

end Tachikawa



end

end OAI
end

section
-- module Solutions.OAIQ116_Tach.Tachikawa_OuterExt
attribute [-instance] _root_.OAI.Tachikawa.Construction.simpleTwist_preserves_projective _root_.OAI.Tachikawa.DownHom.instAddCommGroupCochain _root_.OAI.Tachikawa.DownHom.instModuleCochain _root_.OAI.Tachikawa.Enveloping.inducedRegularCochain_projective _root_.OAI.Tachikawa.Enveloping.instAddCommGroupCarrierMulOppositeRightObj _root_.OAI.Tachikawa.Enveloping.instModuleCarrierMulOppositeRightObj_1 _root_.OAI.Tachikawa.LeftCoinduced.coextend_additive _root_.OAI.Tachikawa.LeftCoinduced.coextend_preservesInjective _root_.OAI.Tachikawa.OuterTensor.instAdditiveModuleCatTensorProductObjFunctorFlipBifunctor _root_.OAI.Tachikawa.OuterTensor.instPreservesFiniteColimitsModuleCatTensorProductObjFunctorFlipBifunctor _root_.OAI.Tachikawa.OuterTensor.instPreservesFiniteLimitsModuleCatTensorProductObjFunctorFlipBifunctor _root_.OAI.Tachikawa.Triangular.instProjectiveCarrierOneFree _root_.OAI.Tachikawa.downIntTensorSigns
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
set_option backward.isDefEq.respectTransparency false


noncomputable section



namespace Tachikawa.OuterTensor
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped TensorProduct ModuleCat.Algebra

variable {k A B : Type} [Field k] [Ring A] [Ring B] [Algebra k A] [Algebra k B]
  [CharP k 2]
  {M : ModuleCat A} {N : ModuleCat B}
  (P : ProjectiveResolution M) (Q : ProjectiveResolution N)
  [∀ n, Module.Finite A (P.complex.X n)] [∀ n, Module.Finite B (Q.complex.X n)]
  [∀ n, FiniteDimensional k (P.complex.X n)] [∀ n, FiniteDimensional k (Q.complex.X n)]

lemma homTotal_evaluate (n i j : ℕ) (h : i+j=n)
    (z : (P.complex.X i ⟶ M) ⊗[k] (Q.complex.X j ⟶ N)) :
    ιMapBifunctor P.complex Q.complex (bifunctor k A B) (.down ℕ) i j n h ≫
      (homTotalIso P.complex Q.complex M N).hom.f n
        (ιMapBifunctor (resolutionHom k A P.complex M) (resolutionHom k B Q.complex N)
          (tensorF k) (.up ℕ) i j n h z) = homMap z :=
  TotalDualPairing.evaluate_ι_self _ _ _ (homBicomplexEquiv P.complex Q.complex M N) n i j h z

lemma homTotal_evaluate_ne (n i j a b : ℕ) (h : i+j=n) (h' : a+b=n)
    (hne : (a,b) ≠ (i,j)) (z : (P.complex.X i ⟶ M) ⊗[k] (Q.complex.X j ⟶ N)) :
    ιMapBifunctor P.complex Q.complex (bifunctor k A B) (.down ℕ) a b n h' ≫
      (homTotalIso P.complex Q.complex M N).hom.f n
        (ιMapBifunctor (resolutionHom k A P.complex M) (resolutionHom k B Q.complex N)
          (tensorF k) (.up ℕ) i j n h z) = 0 :=
  TotalDualPairing.evaluate_ι_ne _ _ _ (homBicomplexEquiv P.complex Q.complex M N) n i j a b h h' hne z

variable (σ : A ≃ₐ[k] A) (τ : B ≃ₐ[k] B)
  (e : (algebraTwist σ).obj M ≅ M) (f : (algebraTwist τ).obj N ≅ N)
  (lP : ProjectiveResolution.Hom P (mappedResolution (algebraTwist σ) P) e.inv)
  (lQ : ProjectiveResolution.Hom Q (mappedResolution (algebraTwist τ) Q) f.inv)

omit [CharP k 2] [∀ n, Module.Finite A (P.complex.X n)]
  [∀ n, Module.Finite B (Q.complex.X n)]
  [∀ n, FiniteDimensional k (P.complex.X n)]
  [∀ n, FiniteDimensional k (Q.complex.X n)] in
lemma homMap_twist (i j : ℕ) (z : (P.complex.X i ⟶ M) ⊗[k] (Q.complex.X j ⟶ N)) :
    homMap (TensorProduct.map
      ((resolutionTwistHom (k := k) (algebraTwist σ) P e lP.hom).f i).hom
      ((resolutionTwistHom (k := k) (algebraTwist τ) Q f lQ.hom).f j).hom z) =
    morphism (lP.hom.f i) (lQ.hom.f j) ≫
      (twistObjIso σ τ (P.complex.X i) (Q.complex.X j)).hom ≫
      (algebraTwist (Algebra.TensorProduct.congr σ τ)).map (homMap z) ≫
      (tensorTwistObjIso σ τ e f).hom := by
  dsimp only [mappedResolution] at lP lQ ⊢
  induction z using OAI.tensorInductionOn with
  | tmul u v =>
    change morphism (lP.hom.f i ≫ (algebraTwist σ).map u ≫ e.hom)
      (lQ.hom.f j ≫ (algebraTwist τ).map v ≫ f.hom) =
      morphism (lP.hom.f i) (lQ.hom.f j) ≫
        (twistObjIso σ τ (P.complex.X i) (Q.complex.X j)).hom ≫
        (algebraTwist (Algebra.TensorProduct.congr σ τ)).map (morphism u v) ≫
        (twistObjIso σ τ M N).inv ≫ morphism e.hom f.hom
    refine (morphism_comp (lP.hom.f i) ((algebraTwist σ).map u ≫ e.hom)
      (lQ.hom.f j) ((algebraTwist τ).map v ≫ f.hom)).symm.trans ?_
    apply congrArg (fun morph => morphism (lP.hom.f i) (lQ.hom.f j) ≫ morph)
    refine (morphism_comp ((algebraTwist σ).map u) e.hom
      ((algebraTwist τ).map v) f.hom).symm.trans ?_
    exact (congrArg (fun morph => morph ≫ morphism e.hom f.hom)
      ((Iso.eq_comp_inv (twistObjIso σ τ M N)).mpr
        (twistObjIso_natural σ τ u v))).trans (by simp only [Category.assoc]; try rfl)
  | add z w hz hw =>
    exact (congrArg homMap (map_add _ z w)).trans ((map_add homMap _ _).trans
      ((congrArg₂ (· + ·) hz hw).trans (by
        erw [map_add, Functor.map_add, Preadditive.add_comp,
          Preadditive.comp_add, Preadditive.comp_add]
        try rfl)))

lemma homTotal_twist :
    mapBifunctorMap (resolutionTwistHom (k := k) (algebraTwist σ) P e lP.hom)
      (resolutionTwistHom (k := k) (algebraTwist τ) Q f lQ.hom) (tensorF k) (.up ℕ) ≫
      (homTotalIso P.complex Q.complex M N).hom =
    (homTotalIso P.complex Q.complex M N).hom ≫ tensorResolutionTwist P Q σ τ e f lP lQ := by
  dsimp only [mappedResolution] at lP lQ ⊢
  apply HomologicalComplex.Hom.ext
  funext n
  apply mapBifunctor.hom_ext
  intro i j h
  change _ ≫ (_ ≫ _) = _ ≫ (_ ≫ _)
  rw [← Category.assoc,ι_mapBifunctorMap]
  simp only [Category.assoc]
  rw [tensorF_maps_assoc]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  change (P.complex.X i ⟶ M) ⊗[k] (Q.complex.X j ⟶ N) at z
  change (homTotalIso P.complex Q.complex M N).hom.f n
    (ιMapBifunctor (resolutionHom k A P.complex M) (resolutionHom k B Q.complex N)
      (tensorF k) (.up ℕ) i j n h
      (TensorProduct.map
        ((resolutionTwistHom (k := k) (algebraTwist σ) P e lP.hom).f i).hom
        ((resolutionTwistHom (k := k) (algebraTwist τ) Q f lQ.hom).f j).hom z)) =
    (tensorTwistLiftHom σ τ P Q e f lP lQ).f n ≫
      (algebraTwist (Algebra.TensorProduct.congr σ τ)).map
        ((homTotalIso P.complex Q.complex M N).hom.f n
          (ιMapBifunctor (resolutionHom k A P.complex M) (resolutionHom k B Q.complex N)
      (tensorF k) (.up ℕ) i j n h z)) ≫ (tensorTwistObjIso σ τ e f).hom
  apply mapBifunctor.hom_ext
  intro a b h'
  rw [← Category.assoc,ι_tensorTwistLiftHom]
  simp only [Category.assoc]
  erw [← Functor.map_comp_assoc]
  by_cases hab : (a,b) = (i,j)
  · obtain ⟨rfl,rfl⟩ := Prod.mk.inj hab
    erw [homTotal_evaluate,homTotal_evaluate]
    exact homMap_twist P Q σ τ e f lP lQ a b z
  · erw [homTotal_evaluate_ne P Q n i j a b h h' hab,
      homTotal_evaluate_ne P Q n i j a b h h' hab]
    erw [Functor.map_zero,zero_comp,comp_zero]

end Tachikawa.OuterTensor

end

end OAI
end

section
-- module Solutions.OAIQ116_Tach.Tachikawa_Nakayama
attribute [-instance] _root_.OAI.Tachikawa.DownHom.instAddCommGroupCochain _root_.OAI.Tachikawa.DownHom.instModuleCochain _root_.OAI.Tachikawa.Enveloping.instAddCommGroupCarrierMulOppositeRightObj _root_.OAI.Tachikawa.Enveloping.instModuleCarrierMulOppositeRightObj_1 _root_.OAI.Tachikawa.LeftCoinduced.coextend_additive _root_.OAI.Tachikawa.LeftCoinduced.coextend_preservesInjective _root_.OAI.Tachikawa.OuterTensor.instAdditiveModuleCatTensorProductObjFunctorFlipBifunctor _root_.OAI.Tachikawa.downIntTensorSigns
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace Tachikawa
open CategoryTheory CategoryTheory.Limits HomologicalComplex
variable {k : Type*} [Field k] {I : Type*} {c : ComplexShape I}

lemma homologyMap_eq_of_component {C : Type*} [Category C] [Abelian C]
    {K L : HomologicalComplex C c} (f g : K ⟶ L) (i : I) (h : f.f i = g.f i) :
    homologyMap f i = homologyMap g i := by
  apply (cancel_epi (K.homologyπ i)).1
  rw [homologyπ_naturality,homologyπ_naturality]
  congr 1
  apply (cancel_mono (L.iCycles i)).1
  rw [cyclesMap_i,cyclesMap_i,h]

lemma homologyMap_eq_scalar {K : HomologicalComplex (ModuleCat k) c}
    (f : K ⟶ K) (i : I) (r : k) (hf : f.f i = r • 𝟙 (K.X i)) :
    homologyMap f i = r • 𝟙 (K.homology i) := by
  have h := homologyMap_eq_of_component f (r • 𝟙 K) i hf
  rw [h]
  change ShortComplex.homologyMap ((shortComplexFunctor (ModuleCat k) c i).map
    (r • 𝟙 K)) = _
  have hsc : (shortComplexFunctor (ModuleCat k) c i).map (r • 𝟙 K) =
      r • 𝟙 (K.sc i) := by ext <;> rfl
  rw [hsc,ShortComplex.homologyMap_smul,ShortComplex.homologyMap_id]
  rfl

lemma homologyMap_scalar_of_conjugate {K L : HomologicalComplex (ModuleCat k) c}
    (e : HomotopyEquiv K L) (f : K ⟶ K) (i : I) (r : k)
    (hf : (e.inv ≫ f ≫ e.hom).f i = r • 𝟙 (L.X i)) :
    homologyMap f i = r • 𝟙 (K.homology i) := by
  have h := homologyMap_eq_scalar (e.inv ≫ f ≫ e.hom) i r hf
  have hh := e.homotopyInvHomId.homologyMap_eq i
  rw [homologyMap_comp,homologyMap_id] at hh
  apply (cancel_epi (homologyMap e.inv i)).1
  apply (cancel_mono (homologyMap e.hom i)).1
  rw [Category.assoc,← homologyMap_comp,← homologyMap_comp,h]
  rw [Linear.comp_smul,Category.comp_id,Linear.smul_comp]
  exact (congrArg (fun z => r • z) hh).symm

namespace VectorSplit

variable {K L : CochainComplex (ModuleCat k) ℕ}

lemma tensor_conjugate_component (f : K ⟶ K) (g : L ⟶ L)
    (n : ℕ) (a b : ℕ → k) (r : k)
    (hf : ∀ i, (inclusion K ≫ f ≫ projection K).f i = a i • 𝟙 _)
    (hg : ∀ j, (inclusion L ≫ g ≫ projection L).f j = b j • 𝟙 _)
    (hab : ∀ i j, i+j=n → a i * b j = r ∨
      IsZero (((tensorFunctor (k := k)).obj ((homologyComplex K).X i)).obj
        ((homologyComplex L).X j))) :
    ((tensorHomologyHomotopyEquiv K L (.up ℕ)).inv ≫
      mapBifunctorMap f g (tensorFunctor (k := k)) (.up ℕ) ≫
        (tensorHomologyHomotopyEquiv K L (.up ℕ)).hom).f n = r • 𝟙 _ := by
  change (mapBifunctorMap (inclusion K) (inclusion L) (tensorFunctor (k := k)) (.up ℕ) ≫
    mapBifunctorMap f g (tensorFunctor (k := k)) (.up ℕ) ≫
    mapBifunctorMap (projection K) (projection L) (tensorFunctor (k := k)) (.up ℕ)).f n = _
  rw [← Category.assoc,bifunctorMap_comp,bifunctorMap_comp]
  simp only [Category.assoc]
  apply HomologicalComplex₂.total.hom_ext
  intro i j hij
  erw [ι_mapBifunctorMap]
  rcases hab i j hij with hab | hz
  · rw [hf,hg]
    simp only [Functor.map_smul,NatTrans.app_smul,CategoryTheory.Functor.map_id,NatTrans.id_app,
      Linear.smul_comp,Linear.comp_smul,Category.id_comp,Category.comp_id,smul_smul,
      ]
    rw [mul_comm (b j),hab]
    rfl
  · exact hz.eq_of_src _ _

lemma tensor_homology_scalar (f : K ⟶ K) (g : L ⟶ L)
    (n : ℕ) (a b : ℕ → k) (r : k)
    (hf : ∀ i, (inclusion K ≫ f ≫ projection K).f i = a i • 𝟙 _)
    (hg : ∀ j, (inclusion L ≫ g ≫ projection L).f j = b j • 𝟙 _)
    (hab : ∀ i j, i+j=n → a i * b j = r ∨
      IsZero (((tensorFunctor (k := k)).obj ((homologyComplex K).X i)).obj
        ((homologyComplex L).X j))) :
    homologyMap (mapBifunctorMap f g (tensorFunctor (k := k)) (.up ℕ)) n = r • 𝟙 _ :=
  homologyMap_scalar_of_conjugate (tensorHomologyHomotopyEquiv K L (.up ℕ)) _ n r
    (tensor_conjugate_component f g n a b r hf hg hab)
end VectorSplit
end Tachikawa



namespace Tachikawa
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open scoped ModuleCat.Algebra
variable {k R : Type} [Field k] [Ring R] [Algebra k R]
  {X Y : ModuleCat R} (P : ProjectiveResolution X)

lemma resolutionHomologyExtAll_quotient (n : ℕ)
    (z : VectorSplit.Z (resolutionHom k R P.complex Y) n) :
    resolutionHomologyExtAll (N := Y) P n (VectorSplit.quotient _ n z) =
      resolutionCyclesToExt Y P n z := by
  have aux {V W : Type} [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
      (f : V →ₗ[k] W) (hf : Function.Surjective f) (T : Submodule k V)
      (h : f.ker = T) (z : V) :
      (by rw [← h]; exact f.quotKerEquivOfSurjective hf : (V ⧸ T) ≃ₗ[k] W) (T.mkQ z) = f z := by
    subst T
    exact LinearMap.quotKerEquivOfSurjective_apply_mk f hf z
  exact aux (resolutionCyclesToExt Y P n) (resolutionCyclesToExt_surjective Y P n)
    _ (resolutionCyclesToExt_ker_all P n) z

variable (F : ModuleCat R ⥤ ModuleCat R) [F.Additive] [F.Linear k]
  [F.PreservesProjectiveObjects] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  (e : F.obj X ≅ X)

lemma resolutionTwistHom_scalar
    (l : ProjectiveResolution.Hom P (mappedResolution F P) e.inv) (n : ℕ) (r : k)
    (h : ∀ x : Ext X X n, extIso (k := k) e e n (x.mapExactFunctor F) = r • x) :
    (VectorSplit.inclusion (resolutionHom k R P.complex X) ≫
      resolutionTwistHom (k := k) F P e l.hom ≫
      VectorSplit.projection (resolutionHom k R P.complex X)).f n = r • 𝟙 _ := by
  let K := resolutionHom k R P.complex X
  let S := resolutionTwistHom (k := k) F P e l.hom
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change VectorSplit.H K n at x
  let z := VectorSplit.representatives K n x
  have hz : S.f n z.val ∈ VectorSplit.Z K n := by
    change K.d n ((ComplexShape.up ℕ).next n) (S.f n z.val) = 0
    have he := congrArg (fun f => f z.val) (S.comm n ((ComplexShape.up ℕ).next n))
    change K.d n ((ComplexShape.up ℕ).next n) (S.f n z.val) =
      S.f ((ComplexShape.up ℕ).next n) (K.d n ((ComplexShape.up ℕ).next n) z.val) at he
    rw [he,z.property]
    exact map_zero _
  change VectorSplit.quotient K n (VectorSplit.retract K n (S.f n z.val)) = r • x
  rw [show (S.f n z.val) = (⟨S.f n z.val,hz⟩ : VectorSplit.Z K n).val from rfl,
    VectorSplit.retract_cycle]
  apply (resolutionHomologyExtAll (N := X) P n (k := k)).injective
  rw [(resolutionHomologyExtAll (N := X) P n (k := k)).map_smul r x,
    resolutionHomologyExtAll_quotient]
  have hs := resolutionTwistHom_extMk (k := k) F P e l z.val
    ((resolutionHom_memZ k R P.complex X n z.val).mp z.property)
  change extIso (k := k) e e n ((resolutionCyclesToExt X P n z).mapExactFunctor F) =
    resolutionCyclesToExt X P n ⟨S.f n z.val,hz⟩ at hs
  rw [← hs,h]
  congr 1
  rw [← resolutionHomologyExtAll_quotient,VectorSplit.quotient_representatives_apply]

end Tachikawa



namespace Tachikawa
open CategoryTheory CategoryTheory.Limits HomologicalComplex
variable {k : Type*} [Field k] {I : Type*} {c : ComplexShape I}

lemma component_scalar_of_homologyMap {K : HomologicalComplex (ModuleCat k) c}
    (hd : ∀ i j, K.d i j = 0) (f : K ⟶ K) (i : I) (r : k)
    (h : homologyMap f i = r • 𝟙 _) : f.f i = r • 𝟙 _ := by
  have : IsIso (K.iCycles i) := (K.sc i).isIso_iCycles (hd _ _)
  have : IsIso (K.homologyπ i) := (K.sc i).isIso_homologyπ (hd _ _)
  have hc : cyclesMap f i = r • 𝟙 _ := by
    apply (cancel_mono (K.homologyπ i)).1
    rw [← homologyπ_naturality,h,Linear.comp_smul,Linear.smul_comp,
      Category.comp_id,Category.id_comp]
  apply (cancel_epi (K.iCycles i)).1
  rw [← cyclesMap_i,hc,Linear.smul_comp,Linear.comp_smul,
    Category.comp_id,Category.id_comp]

lemma conjugate_scalar_of_homologyMap {K L : HomologicalComplex (ModuleCat k) c}
    (e : HomotopyEquiv K L) (hd : ∀ i j, L.d i j = 0) (f : K ⟶ K)
    (i : I) (r : k) (h : homologyMap f i = r • 𝟙 _) :
    (e.inv ≫ f ≫ e.hom).f i = r • 𝟙 _ := by
  apply component_scalar_of_homologyMap hd
  rw [homologyMap_comp,homologyMap_comp,h]
  simp only [Linear.comp_smul,Linear.smul_comp,Category.id_comp]
  rw [← homologyMap_comp,e.homotopyInvHomId.homologyMap_eq,homologyMap_id]

lemma homologyMap_scalar_of_intertwine {K L : HomologicalComplex (ModuleCat k) c}
    (e : K ≅ L) (f : K ⟶ K) (g : L ⟶ L) (h : f ≫ e.hom = e.hom ≫ g)
    (i : I) (r : k) (hf : homologyMap f i = r • 𝟙 _) :
    homologyMap g i = r • 𝟙 _ := by
  have hs := congrArg (fun u => homologyMap u i) h
  rw [homologyMap_comp,homologyMap_comp,hf] at hs
  apply (cancel_epi (homologyMap e.hom i)).1
  rw [Linear.comp_smul,Category.comp_id]
  exact hs.symm.trans (by rw [Linear.smul_comp,Category.id_comp])

end Tachikawa



namespace Tachikawa
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian HomologicalComplex
open scoped ModuleCat.Algebra
variable {k R : Type} [Field k] [Ring R] [Algebra k R]
  (F : ModuleCat R ⥤ ModuleCat R) [F.Additive] [F.Linear k]
  [F.PreservesProjectiveObjects] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  {X : ModuleCat R} (P : ProjectiveResolution X) (e : F.obj X ≅ X)

lemma extTwist_scalar_of_homologyMap
    (l : ProjectiveResolution.Hom P (mappedResolution F P) e.inv) (n : ℕ) (r : k)
    (h : homologyMap (resolutionTwistHom (k := k) F P e l.hom) n = r • 𝟙 _)
    (x : Ext X X n) : extIso (k := k) e e n (x.mapExactFunctor F) = r • x := by
  let K := resolutionHom k R P.complex X
  let S := resolutionTwistHom (k := k) F P e l.hom
  have hf := conjugate_scalar_of_homologyMap (VectorSplit.homologyHomotopyEquiv K)
    (fun _ _ => rfl) S n r h
  obtain ⟨y,rfl⟩ := (resolutionHomologyExtAll (N := X) P n (k := k)).surjective x
  let z := VectorSplit.representatives K n y
  have hz : S.f n z.val ∈ VectorSplit.Z K n := by
    change K.d n ((ComplexShape.up ℕ).next n) (S.f n z.val) = 0
    have he := congrArg (fun f => f z.val) (S.comm n ((ComplexShape.up ℕ).next n))
    change K.d n ((ComplexShape.up ℕ).next n) (S.f n z.val) =
      S.f ((ComplexShape.up ℕ).next n) (K.d n ((ComplexShape.up ℕ).next n) z.val) at he
    rw [he,z.property]
    exact map_zero _
  have hy := congrArg (fun u => u y) hf
  change VectorSplit.quotient K n (VectorSplit.retract K n (S.f n z.val)) = r • y at hy
  rw [show S.f n z.val = (⟨S.f n z.val,hz⟩ : VectorSplit.Z K n).val from rfl,
    VectorSplit.retract_cycle] at hy
  have hs := resolutionTwistHom_extMk (k := k) F P e l z.val
    ((resolutionHom_memZ k R P.complex X n z.val).mp z.property)
  change extIso (k := k) e e n ((resolutionCyclesToExt X P n z).mapExactFunctor F) =
    resolutionCyclesToExt X P n ⟨S.f n z.val,hz⟩ at hs
  rw [← resolutionHomologyExtAll_quotient,VectorSplit.quotient_representatives_apply] at hs
  rw [hs,← resolutionHomologyExtAll_quotient,hy]
  exact (resolutionHomologyExtAll (N := X) P n (k := k)).map_smul r y

end Tachikawa



end

end OAI
end

section
-- module Solutions.OAIQ116_Tach.Tachikawa_Period
attribute [-instance] _root_.OAI.Tachikawa.AlgebraInduction.resFinite _root_.OAI.Tachikawa.Construction.instFiniteCSubtypeMemSubmoduleCe _root_.OAI.Tachikawa.Construction.instFiniteCSubtypeMemSubmoduleCf _root_.OAI.Tachikawa.Construction.instFiniteDimensionalCarrierBBRegularLeftObj _root_.OAI.Tachikawa.Construction.instFiniteDimensionalCarrierEXObj _root_.OAI.Tachikawa.Construction.instFiniteMulOppositeC _root_.OAI.Tachikawa.Construction.instFiniteMulOppositeCSubtypeMemSubmoduleEC _root_.OAI.Tachikawa.Construction.instFiniteMulOppositeCSubtypeMemSubmoduleFC _root_.OAI.Tachikawa.Construction.instInjectiveE _root_.OAI.Tachikawa.Construction.instIsScalarTowerEX _root_.OAI.Tachikawa.Construction.instModuleEX _root_.OAI.Tachikawa.Construction.instProjectiveMulOppositeC _root_.OAI.Tachikawa.Construction.simpleTwist_preserves_projective _root_.OAI.Tachikawa.DownHom.instAddCommGroupCochain _root_.OAI.Tachikawa.DownHom.instModuleCochain _root_.OAI.Tachikawa.Enveloping.instAddCommGroupCarrierMulOppositeRightObj _root_.OAI.Tachikawa.Enveloping.instModuleCarrierMulOppositeRightObj_1 _root_.OAI.Tachikawa.LeftCoinduced.coextend_additive _root_.OAI.Tachikawa.LeftCoinduced.coextend_preservesInjective _root_.OAI.Tachikawa.SourceField.sourceAlgebra_finite _root_.OAI.Tachikawa.downIntTensorSigns
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section



namespace Tachikawa.C
open CategoryTheory CategoryTheory.Abelian
open scoped ModuleCat.Algebra
variable {k : Type} [Field k] [CharP k 2] (q : k)

omit [CharP k 2] in

lemma inducedRange_hom_zero (n : ℕ) (f : inducedRangeObj q n ⟶ simpleObj q) : f = 0 := by
  have hh : ModuleCat.ofHom (inducedD q n).hom.rangeRestrict ≫ f = 0 :=
    induced_positive_hom_zero q n _
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  rintro ⟨x,y,hy⟩
  subst x
  exact congrArg (fun g : inducedObj q (n+1) ⟶ simpleObj q => g y) hh

omit [CharP k 2] in
lemma inducedRange_ext_zero_zero (n : ℕ) :
    Subsingleton (Ext (inducedRangeObj q n) (simpleObj q) 0) := by
  have : Subsingleton (inducedRangeObj q n ⟶ simpleObj q) :=
    subsingleton_of_forall_eq 0 (inducedRange_hom_zero q n)
  exact Ext.addEquiv₀.injective.subsingleton

omit [CharP k 2] in
lemma simple_ext_one_zero (hp : ∀ n : ℕ, 0 < n → 1+q^n ≠ 0) :
    Subsingleton (Ext (simpleObj q) (simpleObj q) 1) := by
  apply subsingleton_of_forall_eq 0
  intro x
  let : Module.Projective (T q) (inducedObj q 0) := inducedObj_projective q 0
  let : Subsingleton (Ext (initialShortComplex q hp).X₂ (simpleObj q) 1) :=
    show Subsingleton (Ext (inducedObj q 0) (simpleObj q) 1) from Ext.subsingleton_of_projective _ _ 0
  obtain ⟨y,hy⟩ := Ext.contravariant_sequence_exact₃ (initial_shortExact q hp) (simpleObj q)
    x (Subsingleton.elim _ _) (n₀ := 0) (by omega)
  let : Subsingleton (Ext (initialShortComplex q hp).X₁ (simpleObj q) 0) :=
    inducedRange_ext_zero_zero q 0
  rw [Subsingleton.elim y 0, Ext.comp_zero] at hy
  exact hy.symm

lemma firstRange_ext_one_zero (hq : q ≠ 0) (hp : ∀ n : ℕ, 0 < n → 1+q^n ≠ 0) :
    Subsingleton (Ext (inducedRangeObj q 0) (simpleObj q) 1) := by
  let : Subsingleton (Ext (middleShortComplex q hq hp).X₂ (simpleObj q) 0) :=
    induced_positive_ext_zero q 0 0
  let : Subsingleton (Ext (middleShortComplex q hq hp).X₂ (simpleObj q) 1) :=
    induced_positive_ext_zero q 0 1
  let : Subsingleton (Ext (middleShortComplex q hq hp).X₁ (simpleObj q) 0) :=
    inducedRange_ext_zero_zero q 1
  exact (extShiftEquiv k (middle_shortExact q hq hp) (simpleObj q) 0).symm.injective.subsingleton

lemma simple_ext_two_zero (hq : q ≠ 0) (hp : ∀ n : ℕ, 0 < n → 1+q^n ≠ 0) :
    Subsingleton (Ext (simpleObj q) (simpleObj q) 2) := by
  let : Module.Projective (T q) (inducedObj q 0) := inducedObj_projective q 0
  let : Subsingleton (Ext (initialShortComplex q hp).X₂ (simpleObj q) 1) :=
    show Subsingleton (Ext (inducedObj q 0) (simpleObj q) 1) from Ext.subsingleton_of_projective _ _ 0
  let : Subsingleton (Ext (initialShortComplex q hp).X₂ (simpleObj q) 2) :=
    show Subsingleton (Ext (inducedObj q 0) (simpleObj q) 2) from Ext.subsingleton_of_projective _ _ 1
  let : Subsingleton (Ext (initialShortComplex q hp).X₁ (simpleObj q) 1) :=
    firstRange_ext_one_zero q hq hp
  exact (extShiftEquiv k (initial_shortExact q hp) (simpleObj q) 1).symm.injective.subsingleton

end Tachikawa.C



namespace Tachikawa.C
open CategoryTheory CategoryTheory.Abelian
open scoped ModuleCat.Algebra
variable {k : Type} [Field k] [CharP k 2] (q : k)

lemma simpleExtPeriod_apply (hq : q ≠ 0) (hp : ∀ n : ℕ, 0 < n → 1+q^n ≠ 0)
    (n : ℕ) (x : Ext (simpleObj q) (simpleObj q) n) :
    simpleExtPeriod q hq hp n x =
      (initialClass q hp).comp (c := n+3)
        ((middleClass q hq hp).comp (c := n+2)
          ((upperClass q).comp (c := n+1)
            ((homologyClass q hq hp).comp x (zero_add n))
            (by omega)) (by omega)) (by omega) := rfl

lemma simpleExtPeriod_eq_tau_comp (hq : q ≠ 0) (hp : ∀ n : ℕ, 0 < n → 1+q^n ≠ 0)
    (n : ℕ) (x : Ext (simpleObj q) (simpleObj q) n) :
    simpleExtPeriod q hq hp n x = (tau q hq hp).comp x (by omega) := by
  simp only [tau, simpleExtPeriod_apply, Ext.comp_mk₀_id]
  rw [Ext.comp_assoc (a₂₃ := n+2) _ _ _ (by omega) (by omega) (by omega),
    Ext.comp_assoc (a₂₃ := n+1) _ _ _ (by omega) (by omega) (by omega),
    Ext.comp_assoc (a₂₃ := n) _ _ _ (by omega) (by omega) (by omega)]

lemma simpleExt_zero_off_multiples (hq : q ≠ 0)
    (hp : ∀ n : ℕ, 0 < n → 1+q^n ≠ 0) (n : ℕ) (hn : n % 3 ≠ 0) :
    Subsingleton (Ext (simpleObj q) (simpleObj q) n) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases h1 : n = 1
    · subst n
      exact simple_ext_one_zero q hp
    by_cases h2 : n = 2
    · subst n
      exact simple_ext_two_zero q hq hp
    have h3 : 3 ≤ n := by omega
    have hm : (n-3)%3 ≠ 0 := by omega
    have := ih (n-3) (by omega) hm
    have he : n = (n-3)+3 := by omega
    rw [he]
    exact (simpleExtPeriod q hq hp (n-3)).symm.injective.subsingleton

end Tachikawa.C



namespace Tachikawa.C
open CategoryTheory CategoryTheory.Abelian
open scoped ModuleCat.Algebra
variable {k : Type} [Field k] [CharP k 2] (q H : k) (hH : H ≠ 0)

lemma homology_twist_comparison (hq : q ≠ 0) (hp : ∀ n : ℕ, 0 < n → 1+q^n ≠ 0) :
    (tTwist q H hH).map (homologyShortComplex q hq hp).g ≫
      (H • simpleTwistComparison q H hH) =
    cyclesTwistComparison q H hH ≫ (homologyShortComplex q hq hp).g := by
  apply ModuleCat.hom_ext
  ext x
  change H • nuTwoAug q x.val.2 = nuTwoAug q (H • x.val.2)
  exact ((nuTwoAug q).map_smul H x.val.2).symm

end Tachikawa.C



namespace Tachikawa
open CategoryTheory CategoryTheory.Abelian
variable {C : Type*} [Category C] [Abelian C] [HasExt C]

lemma ext_push_comparison {A B A' B' Z : C} {a n c : ℕ}
    (f : Ext A B a) (f' : Ext A' B' a) (u : A ⟶ A') (v : B ⟶ B')
    (h : f.comp (Ext.mk₀ v) (add_zero a) = (Ext.mk₀ u).comp f' (zero_add a))
    (z : Ext B' Z n) (hc : a+n=c) :
    f.comp ((Ext.mk₀ v).comp z (zero_add n)) hc =
      (Ext.mk₀ u).comp (f'.comp z hc) (zero_add c) := by
  rw [← Ext.comp_assoc_of_second_deg_zero,h]
  exact Ext.comp_assoc _ _ _ (zero_add a) hc (by omega)

end Tachikawa



namespace Tachikawa.C
open CategoryTheory CategoryTheory.Abelian
open scoped ModuleCat.Algebra
variable {k : Type} [Field k] [CharP k 2] (q H : k) (hH : H ≠ 0)
  (hq : q ≠ 0) (hp : ∀ n : ℕ, 0 < n → 1+q^n ≠ 0)

omit [CharP k 2] in
lemma initial_twist_naturality :
    ((initialClass q hp).mapExactFunctor (tTwist q H hH)).comp
      (Ext.mk₀ (rangeTwistComparison q H hH 0)) (add_zero 1) =
    (Ext.mk₀ (simpleTwistComparison q H hH)).comp (initialClass q hp) (zero_add 1) := by
  dsimp only [initialClass]
  erw [Ext.mapExactFunctor_extClass]
  exact
    ((initial_shortExact q hp).map_of_exact (tTwist q H hH)).extClass_naturality
      (initial_shortExact q hp) (twistInitialHom q H hH hp)

lemma middle_twist_naturality :
    ((middleClass q hq hp).mapExactFunctor (tTwist q H hH)).comp
      (Ext.mk₀ (rangeTwistComparison q H hH 1)) (add_zero 1) =
    (Ext.mk₀ (rangeTwistComparison q H hH 0)).comp (middleClass q hq hp) (zero_add 1) := by
  dsimp only [middleClass]
  erw [Ext.mapExactFunctor_extClass]
  exact
    ((middle_shortExact q hq hp).map_of_exact (tTwist q H hH)).extClass_naturality
      (middle_shortExact q hq hp) (twistMiddleHom q H hH hq hp)

omit [CharP k 2] in
lemma upper_twist_naturality :
    ((upperClass q).mapExactFunctor (tTwist q H hH)).comp
      (Ext.mk₀ (cyclesTwistComparison q H hH)) (add_zero 1) =
    (Ext.mk₀ (rangeTwistComparison q H hH 1)).comp (upperClass q) (zero_add 1) := by
  dsimp only [upperClass]
  erw [Ext.mapExactFunctor_extClass]
  exact
    ((upper_shortExact q).map_of_exact (tTwist q H hH)).extClass_naturality
      (upper_shortExact q) (twistUpperHom q H hH)

lemma homology_twist_naturality :
    ((homologyClass q hq hp).mapExactFunctor (tTwist q H hH)).comp
      (Ext.mk₀ (H • simpleTwistComparison q H hH)) (add_zero 0) =
    (Ext.mk₀ (cyclesTwistComparison q H hH)).comp (homologyClass q hq hp) (zero_add 0) := by
  dsimp only [homologyClass]
  erw [Ext.mapExactFunctor_mk₀]
  erw [Ext.mk₀_comp_mk₀, Ext.mk₀_comp_mk₀]
  exact congrArg Ext.mk₀ (homology_twist_comparison q H hH hq hp)

lemma tau_twist_naturality :
    ((tau q hq hp).mapExactFunctor (tTwist q H hH)).comp
      (Ext.mk₀ (H • simpleTwistComparison q H hH)) (add_zero 3) =
    (Ext.mk₀ (simpleTwistComparison q H hH)).comp (tau q hq hp) (zero_add 3) := by
  simp only [tau,simpleExtPeriod_apply,Ext.comp_mk₀_id,Ext.mapExactFunctor_comp,
    Ext.comp_assoc_of_third_deg_zero]
  rw [homology_twist_naturality q H hH hq hp]
  rw [ext_push_comparison _ _ _ _ (upper_twist_naturality q H hH),
    ext_push_comparison _ _ _ _ (middle_twist_naturality q H hH hq hp),
    ext_push_comparison _ _ _ _ (initial_twist_naturality q H hH hp)]

end Tachikawa.C



namespace Tachikawa.C
open CategoryTheory CategoryTheory.Abelian
open scoped ModuleCat.Algebra
variable {k : Type} [Field k] [CharP k 2] (q : k)
  (hq : q ≠ 0) (hp : ∀ n : ℕ, 0 < n → 1+q^n ≠ 0)

lemma tauPower_zero : tauPower q hq hp 0 = Ext.mk₀ (𝟙 (simpleObj q)) := by
  change Ext.mk₀ ((1:k) • 𝟙 (simpleObj q)) = _
  rw [one_smul]

lemma tauPower_succ (m : ℕ) : tauPower q hq hp (m+1) =
    (tau q hq hp).comp (tauPower q hq hp m) (by omega) := by
  unfold tauPower
  simp only [simpleExtMultiple]
  have h : 3*(m+1) = 3*m+3 := by omega
  generalize he : simpleExtMultiple q hq hp m = e
  cases h
  change simpleExtPeriod q hq hp (3*m) (e.symm 1) = _
  exact simpleExtPeriod_eq_tau_comp q hq hp (3*m) (e.symm 1)

lemma eq_smul_tauPower (m : ℕ) (x : Ext (simpleObj q) (simpleObj q) (3*m)) :
    x = simpleExtMultiple q hq hp m x • tauPower q hq hp m := by
  apply (simpleExtMultiple q hq hp m).injective
  rw [map_smul]
  simp only [tauPower,LinearEquiv.apply_symm_apply,smul_eq_mul,mul_one]

end Tachikawa.C



namespace Tachikawa
open CategoryTheory CategoryTheory.Abelian
open scoped ModuleCat.Algebra

section Iso
variable {K : Type*} [Field K] {D : Type*} [Category D] [Abelian D] [HasExt D]
  [Linear K D] {X Y Z X' Y' Z' : D}
lemma extIso_comp (e : X ≅ X') (f : Y ≅ Y') (g : Z ≅ Z')
    {a b c : ℕ} (x : Ext X Y a) (y : Ext Y Z b) (h : a+b=c) :
    extIso (k := K) e g c (x.comp y h) =
      (extIso (k := K) e f a x).comp (extIso (k := K) f g b y) h := by
  change (Ext.mk₀ e.inv).comp ((x.comp y h).comp (Ext.mk₀ g.hom) (add_zero c))
    (zero_add c) = ((Ext.mk₀ e.inv).comp (x.comp (Ext.mk₀ f.hom) (add_zero a))
      (zero_add a)).comp ((Ext.mk₀ f.inv).comp
        (y.comp (Ext.mk₀ g.hom) (add_zero b)) (zero_add b)) h
  rw [Ext.comp_assoc (Ext.mk₀ e.inv) (x.comp (Ext.mk₀ f.hom) (add_zero a))
    ((Ext.mk₀ f.inv).comp (y.comp (Ext.mk₀ g.hom) (add_zero b)) (zero_add b))
    (zero_add a) h (by omega)]
  simp only [← Ext.comp_assoc_of_second_deg_zero,Ext.mk₀_comp_mk₀,
    Iso.hom_inv_id,Ext.comp_mk₀_id,Ext.comp_assoc_of_third_deg_zero]
end Iso

namespace C
variable {k : Type} [Field k] [CharP k 2] (q H : k) (hH : H ≠ 0)
  (hq : q ≠ 0) (hp : ∀ n : ℕ, 0 < n → 1+q^n ≠ 0)

omit [CharP k 2] in
lemma simpleTwistExt_comp {a b c : ℕ}
    (x : Ext (simpleObj q) (simpleObj q) a)
    (y : Ext (simpleObj q) (simpleObj q) b) (h : a+b=c) :
    simpleTwistExt q H hH c (x.comp y h) =
      (simpleTwistExt q H hH a x).comp (simpleTwistExt q H hH b y) h := by
  simp only [simpleTwistExt,LinearMap.comp_apply,LinearEquiv.coe_coe,
    Functor.mapExtLinearMap_apply,Ext.mapExactFunctor_comp]
  exact extIso_comp (K := k) _ _ _ _ _ h

omit [CharP k 2] in
lemma simpleTwist_mk₀_smul : Ext.mk₀ (H • (simpleTwistIso q H hH).hom) =
    H • Ext.mk₀ (simpleTwistIso q H hH).hom := by
  have h := Ext.mk₀_smul H (simpleTwistIso q H hH).hom
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  apply ModuleCat.hom_ext
  ext x
  change H * (show k from x) = (H * 1) * (show k from x)
  rw [mul_one]

lemma simpleTwist_tau : simpleTwistExt q H hH 3 (tau q hq hp) = H⁻¹ • tau q hq hp := by
  have ht := tau_twist_naturality q H hH hq hp
  have hs := congrArg (fun x => (Ext.mk₀ (simpleTwistIso q H hH).inv).comp x
    (zero_add 3)) ht
  have hscalar : H • simpleTwistExt q H hH 3 (tau q hq hp) = tau q hq hp := by
    change (Ext.mk₀ (simpleTwistIso q H hH).inv).comp
      (((tau q hq hp).mapExactFunctor (tTwist q H hH)).comp
        (Ext.mk₀ (H • (simpleTwistIso q H hH).hom)) (add_zero 3)) (zero_add 3) =
      (Ext.mk₀ (simpleTwistIso q H hH).inv).comp
        ((Ext.mk₀ (simpleTwistIso q H hH).hom).comp (tau q hq hp) (zero_add 3))
        (zero_add 3) at hs
    rw [simpleTwist_mk₀_smul q H hH,Ext.comp_smul,Ext.comp_smul] at hs
    change H • ((Ext.mk₀ (simpleTwistIso q H hH).inv).comp
      (((tau q hq hp).mapExactFunctor (tTwist q H hH)).comp
        (Ext.mk₀ (simpleTwistIso q H hH).hom) (add_zero 3)) (zero_add 3)) = _
    simpa only [← Ext.comp_assoc_of_second_deg_zero,Ext.mk₀_comp_mk₀,
      Iso.inv_hom_id,Ext.mk₀_id_comp] using hs
  calc
    simpleTwistExt q H hH 3 (tau q hq hp) =
      H⁻¹ • (H • simpleTwistExt q H hH 3 (tau q hq hp)) := by
        rw [smul_smul,inv_mul_cancel₀ hH,one_smul]
    _ = H⁻¹ • tau q hq hp := congrArg (fun x => H⁻¹ • x) hscalar

lemma simpleTwist_tauPower (m : ℕ) :
    simpleTwistExt q H hH (3*m) (tauPower q hq hp m) =
      (H⁻¹)^m • tauPower q hq hp m := by
  induction m with
  | zero =>
    rw [tauPower_zero]
    simp [simpleTwistExt,Functor.mapExtLinearMap_apply,Ext.mapExactFunctor_mk₀,extIso]
  | succ m ih =>
    rw [tauPower_succ,simpleTwistExt_comp,simpleTwist_tau q H hH hq hp,ih,
      Ext.smul_comp,Ext.comp_smul,smul_smul,pow_succ']

include hq hp in

lemma simpleTwist_weight (m : ℕ) (x : Ext (simpleObj q) (simpleObj q) (3*m)) :
    simpleTwistExt q H hH (3*m) x = (H⁻¹)^m • x := by
  nth_rw 1 [eq_smul_tauPower q hq hp m x]
  rw [map_smul,simpleTwist_tauPower q H hH hq hp,smul_comm,
    ← eq_smul_tauPower q hq hp m x]

end C
end Tachikawa

end

end OAI
end

section
-- module Solutions.OAIQ116_Tach.Tachikawa_Socle
attribute [-instance] _root_.OAI.Tachikawa.AlgebraInduction.resFinite _root_.OAI.Tachikawa.Construction.instFiniteCSubtypeMemSubmoduleCe _root_.OAI.Tachikawa.Construction.instFiniteCSubtypeMemSubmoduleCf _root_.OAI.Tachikawa.Construction.instFiniteDimensionalCarrierBBRegularLeftObj _root_.OAI.Tachikawa.Construction.instFiniteDimensionalCarrierEXObj _root_.OAI.Tachikawa.Construction.instFiniteMulOppositeC _root_.OAI.Tachikawa.Construction.instFiniteMulOppositeCSubtypeMemSubmoduleEC _root_.OAI.Tachikawa.Construction.instFiniteMulOppositeCSubtypeMemSubmoduleFC _root_.OAI.Tachikawa.Construction.instProjectiveMulOppositeC _root_.OAI.Tachikawa.DownHom.instAddCommGroupCochain _root_.OAI.Tachikawa.DownHom.instModuleCochain _root_.OAI.Tachikawa.Enveloping.coindEndo_finite _root_.OAI.Tachikawa.Enveloping.coindObj_finite _root_.OAI.Tachikawa.Enveloping.eval_finite _root_.OAI.Tachikawa.Enveloping.inducedRegularCochain_projective _root_.OAI.Tachikawa.Enveloping.inducedRegularComplex_finite _root_.OAI.Tachikawa.Enveloping.instAddCommGroupCarrierMulOppositeRightObj _root_.OAI.Tachikawa.Enveloping.instFiniteCarrierDualLeftObjOfFiniteDimensional _root_.OAI.Tachikawa.Enveloping.instFiniteDimensionalCarrierAlgCoindObjOfMulOpposite _root_.OAI.Tachikawa.Enveloping.instFiniteDimensionalCarrierDualLeftObj _root_.OAI.Tachikawa.Enveloping.instModuleCarrierMulOppositeRightObj_1 _root_.OAI.Tachikawa.Enveloping.rightFunctor_finite _root_.OAI.Tachikawa.HomBimodule.instFiniteDimensionalCarrierAlgObj _root_.OAI.Tachikawa.LeftCoinduced.C_finite _root_.OAI.Tachikawa.LeftCoinduced.J_finite _root_.OAI.Tachikawa.LeftCoinduced.coextend_additive _root_.OAI.Tachikawa.LeftCoinduced.coextend_preservesInjective _root_.OAI.Tachikawa.LeftCoinduced.iterate_finite _root_.OAI.Tachikawa.OuterTensor.instAdditiveModuleCatTensorProductObjFunctorFlipBifunctor _root_.OAI.Tachikawa.OuterTensor.instPreservesFiniteColimitsModuleCatTensorProductObjFunctorFlipBifunctor _root_.OAI.Tachikawa.OuterTensor.instPreservesFiniteLimitsModuleCatTensorProductObjFunctorFlipBifunctor _root_.OAI.Tachikawa.SourceField.sourceAlgebra_finite _root_.OAI.Tachikawa.Triangular.instFiniteCarrierOneFree _root_.OAI.Tachikawa.Triangular.instFiniteDimensionalAlgOfCarrierAlg _root_.OAI.Tachikawa.Triangular.instFiniteDimensionalCarrierAlgD₀ObjOfAlg _root_.OAI.Tachikawa.Triangular.instFiniteDimensionalCarrierAlgD₁Obj _root_.OAI.Tachikawa.Triangular.instProjectiveCarrierOneFree _root_.OAI.Tachikawa.downIntTensorSigns _root_.OAI.Tachikawa.freeEndo_finite _root_.OAI.Tachikawa.freeKernel_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section



namespace Tachikawa.Construction
open CategoryTheory CategoryTheory.Abelian HomologicalComplex
open scoped ModuleCat.Algebra
variable {k : Type} [Field k] [CharP k 2] (q H : k) (hH : H ≠ 0)
  (hq : q ≠ 0) (hp : ∀ n : ℕ, 0 < n → 1+q^n ≠ 0)

include hq hp in
lemma simpleResolutionTwist_scalar (n : ℕ) :
    (VectorSplit.inclusion (resolutionHom k (T q) (sResolution q).complex (C.simpleObj q)) ≫
      simpleResolutionTwist q H hH ≫
      VectorSplit.projection (resolutionHom k (T q) (sResolution q).complex (C.simpleObj q))).f n =
        (H⁻¹)^(n/3) • 𝟙 _ := by
  apply resolutionTwistHom_scalar
  intro x
  by_cases hn : n % 3 = 0
  · obtain ⟨m,rfl⟩ := Nat.dvd_of_mod_eq_zero hn
    change C.simpleTwistExt q H hH (3*m) x = _
    rw [C.simpleTwist_weight q H hH hq hp, Nat.mul_div_cancel_left m (by omega : 0<3)]
  · let := C.simpleExt_zero_off_multiples q hq hp n hn
    exact Subsingleton.elim _ _

end Tachikawa.Construction



namespace Tachikawa.Construction
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian HomologicalComplex
open scoped TensorProduct ModuleCat.Algebra
variable {k : Type} [Field k] [CharP k 2] (q H : k) (hH : H ≠ 0)
  (hq : q ≠ 0) (hp : ∀ n : ℕ, 0 < n → 1+q^n ≠ 0)

include hq hp in
lemma tensorHom_twist_scalar (n : ℕ) :
    homologyMap (mapBifunctorMap (simpleResolutionTwist q H hH) (simpleResolutionTwist q H hH)
      (OuterTensor.tensorF k) (.up ℕ)) n = (H⁻¹)^(n/3) • 𝟙 _ := by
  apply VectorSplit.tensor_homology_scalar _ _ n (fun i => (H⁻¹)^(i/3)) (fun i => (H⁻¹)^(i/3))
    ((H⁻¹)^(n/3)) (simpleResolutionTwist_scalar q H hH hq hp)
    (simpleResolutionTwist_scalar q H hH hq hp)
  intro i j hij
  by_cases hi : i % 3 = 0
  · by_cases hj : j % 3 = 0
    · left
      rw [← pow_add]
      congr 1
      omega
    · right
      let := C.simpleExt_zero_off_multiples q hq hp j hj
      let : Subsingleton (VectorSplit.H
          (resolutionHom k (T q) (sResolution q).complex (C.simpleObj q)) j) :=
        (resolutionHomologyExtAll (N := C.simpleObj q) (sResolution q) j (k := k)).injective.subsingleton
      change IsZero (ModuleCat.of k (VectorSplit.H
        (resolutionHom k (T q) (sResolution q).complex (C.simpleObj q)) i ⊗[k]
        VectorSplit.H (resolutionHom k (T q) (sResolution q).complex (C.simpleObj q)) j))
      exact ModuleCat.isZero_of_subsingleton _
  · right
    let := C.simpleExt_zero_off_multiples q hq hp i hi
    let : Subsingleton (VectorSplit.H
        (resolutionHom k (T q) (sResolution q).complex (C.simpleObj q)) i) :=
      (resolutionHomologyExtAll (N := C.simpleObj q) (sResolution q) i (k := k)).injective.subsingleton
    change IsZero (ModuleCat.of k (VectorSplit.H
      (resolutionHom k (T q) (sResolution q).complex (C.simpleObj q)) i ⊗[k]
      VectorSplit.H (resolutionHom k (T q) (sResolution q).complex (C.simpleObj q)) j))
    exact ModuleCat.isZero_of_subsingleton _

include hq hp in
lemma xTensorTwist_homology_scalar (n : ℕ) :
    homologyMap (xTensorTwist q H hH) n = (H⁻¹)^(n/3) • 𝟙 _ := by
  exact homologyMap_scalar_of_intertwine
    (OuterTensor.homTotalIso (k := k) (sResolution q).complex (sResolution q).complex
      (sFinite q).obj (sFinite q).obj) _ _
    (OuterTensor.homTotal_twist (sResolution q) (sResolution q)
      (TrivialExtension.scaleDual (R := C k q) H hH) (TrivialExtension.scaleDual (R := C k q) H hH)
      (C.simpleTwistIso q H hH) (C.simpleTwistIso q H hH)
      (simpleResolutionTwistLift q H hH) (simpleResolutionTwistLift q H hH))
    n _ (tensorHom_twist_scalar q H hH hq hp n)

include hq hp in

lemma XTensorTwist_weight (n : ℕ) (x : Ext (XTensorObj q) (XTensorObj q) n) :
    extIso (k := k) (XTensorTwistIso q H hH) (XTensorTwistIso q H hH) n
      (x.mapExactFunctor (eTwist q H hH)) = (H⁻¹)^(n/3) • x :=
  extTwist_scalar_of_homologyMap (eTwist q H hH) (xTensorResolution q)
    (XTensorTwistIso q H hH) (xTensorTwistLift q H hH) n _
      (xTensorTwist_homology_scalar q H hH hq hp n) x

end Tachikawa.Construction



namespace Tachikawa
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
variable {k R : Type} [Field k] [Ring R] [Algebra k R]
open scoped ModuleCat.Algebra

lemma extIso_trans {X Y Z X' Y' Z' : ModuleCat R}
    (e : X ≅ Y) (f : Y ≅ Z) (e' : X' ≅ Y') (f' : Y' ≅ Z') (n : ℕ)
    (x : Ext X X' n) :
    extIso (k := k) f f' n (extIso (k := k) e e' n x) = extIso (k := k) (e ≪≫ f) (e' ≪≫ f') n x := by
  simp [extIso]

variable (F : ModuleCat R ⥤ ModuleCat R) [F.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]

lemma extIso_map {X Y X' Y' : ModuleCat R} (e : X ≅ Y) (f : X' ≅ Y') (n : ℕ)
    (x : Ext X X' n) :
    (extIso (k := k) e f n x).mapExactFunctor F =
      extIso (k := k) (F.mapIso e) (F.mapIso f) n (x.mapExactFunctor F) := by
  simp only [extIso,LinearEquiv.coe_mk,LinearMap.coe_mk,AddHom.coe_mk,
    Ext.mapExactFunctor_comp,Ext.mapExactFunctor_mk₀]
  rfl

lemma extTwist_weight_transport {X Y : ModuleCat R} (e : F.obj X ≅ X)
    (u : X ≅ Y) (n : ℕ) (r : k)
    (h : ∀ x : Ext X X n, extIso (k := k) e e n (x.mapExactFunctor F) = r • x)
    (y : Ext Y Y n) :
    extIso (k := k) (F.mapIso u.symm ≪≫ e ≪≫ u) (F.mapIso u.symm ≪≫ e ≪≫ u) n
      (y.mapExactFunctor F) = r • y := by
  obtain ⟨x,rfl⟩ := (extIso (k := k) u u n).surjective y
  rw [extIso_map]
  have hi : F.mapIso u ≪≫ (F.mapIso u.symm ≪≫ e ≪≫ u) = e ≪≫ u := by
    apply Iso.ext
    simp
  rw [extIso_trans,hi,← extIso_trans,h]
  exact (extIso (k := k) u u n).map_smul r x

end Tachikawa



namespace Tachikawa.Construction
open CategoryTheory CategoryTheory.Abelian
open scoped ModuleCat.Algebra TensorProduct
variable {k : Type} [Field k] [CharP k 2] (q H : k) (hH : H ≠ 0)

omit [CharP k 2] in
lemma XTwistIso_hom : (XTwistIso q H hH).hom = XTwistComparison q H hH := by
  apply (cancel_epi ((eTwist q H hH).map (XTensorIso q).hom)).1
  simp only [XTwistIso,Iso.trans_hom,Functor.mapIso_hom,Iso.symm_hom,
    ← Functor.map_comp_assoc,Iso.hom_inv_id]
  rw [(eTwist q H hH).map_id,Category.id_comp]
  apply (cancel_epi (OuterTensor.twistObjIso
    (TrivialExtension.scaleDual (R := C k q) H hH)
    (TrivialExtension.scaleDual (R := C k q) H hH)
    (C.simpleObj q) (C.simpleObj q)).hom).1
  change _ ≫ ((_ ≫ _) ≫ _) = _
  erw [Category.assoc, Iso.hom_inv_id_assoc]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  induction z using OAI.tensorInductionOn with
  | tmul x y => rfl
  | add x y hx hy =>
    exact (map_add _ x y).trans ((congrArg₂ (· + ·) hx hy).trans
      (map_add _ x y).symm)

lemma XTwist_weight (hq : q ≠ 0) (hp : ∀ n : ℕ, 0 < n → 1+q^n ≠ 0)
    (n : ℕ) (x : Ext (ModuleCat.of (E q) (X q)) (ModuleCat.of (E q) (X q)) n) :
    extIso (k := k) (XTwistIso q H hH) (XTwistIso q H hH) n
      (x.mapExactFunctor (twistE q H hH)) = (H⁻¹)^(n/3) • x :=
  extTwist_weight_transport (eTwist q H hH) (XTensorTwistIso q H hH) (XTensorIso q) n _
    (XTensorTwist_weight q H hH hq hp n) x

end Tachikawa.Construction



namespace Tachikawa.Construction
open CategoryTheory CategoryTheory.Abelian
open scoped TensorProduct ModuleCat.Algebra
variable {k : Type} [Field k] (q H : k) (hH : H ≠ 0)

lemma sigma_symm : (sigma q H hH).symm = sigma q H⁻¹ (inv_ne_zero hH) := by
  apply AlgEquiv.ext
  intro z
  induction z using OAI.tensorInductionOn with
  | tmul x y => rfl
  | add x y hx hy => simp only [map_add,hx,hy]

variable [CharP k 2]

omit [CharP k 2] in
lemma XInverseTwistIso_hom_apply (x) : (XInverseTwistIso q H hH).hom x = x := rfl

lemma XTwist_weight_of_eq (hq : q ≠ 0) (hp : ∀ n : ℕ, 0 < n → 1+q^n ≠ 0)
    (σ : E q ≃ₐ[k] E q) (hσ : σ = sigma q H hH)
    (e : (SymmetrizingForm.twistFunctor σ).obj (ModuleCat.of (E q) (X q)) ≅
      ModuleCat.of (E q) (X q)) (he : ∀ x, e.hom x = x)
    (n : ℕ) (x : Ext (ModuleCat.of (E q) (X q)) (ModuleCat.of (E q) (X q)) n) :
    extIso (k := k) e e n (x.mapExactFunctor (SymmetrizingForm.twistFunctor σ)) =
      H⁻¹^(n/3) • x := by
  subst σ
  have hee : e = XTwistIso q H hH := by
    apply Iso.ext
    rw [XTwistIso_hom]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    exact he
  subst e
  exact XTwist_weight q H hH hq hp n x

lemma XInverseTwist_weight_oai (hq : q ≠ 0) (hp : ∀ n : ℕ, 0 < n → 1+q^n ≠ 0)
    (n : ℕ) (x : Ext (ModuleCat.of (E q) (X q)) (ModuleCat.of (E q) (X q)) n) :
    extIso (k := k) (XInverseTwistIso q H hH) (XInverseTwistIso q H hH) n
      (x.mapExactFunctor (SymmetrizingForm.twistFunctor (sigma q H hH).symm)) =
        H^(n/3) • x := by
  simpa only [inv_inv] using XTwist_weight_of_eq q H⁻¹ (inv_ne_zero hH) hq hp
    (sigma q H hH).symm (sigma_symm q H hH) (XInverseTwistIso q H hH)
    (XInverseTwistIso_hom_apply q H hH) n x

end Tachikawa.Construction

end

end OAI
end

theorem solution : type_of% @OAI.Tachikawa.Construction.XInverseTwist_weight_oai := @OAI.Tachikawa.Construction.XInverseTwist_weight_oai
