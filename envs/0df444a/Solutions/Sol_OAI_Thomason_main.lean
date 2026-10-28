-- Prove2me | solution 1 for OAI.Thomason.main
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T10:23:56.584228+00:00
-- url     : https://prove2.me/submissions/443204e5-85cf-42e5-bd64-ba19c424a017

import Mathlib
import Definitions.Def_ThomasonModelStructures
import Definitions.Def_OAIQ043T012
import Theorems.Thm_OAI_Thomason_GrayRecursive_IntervalHom_chainComparison_poset_twocells_bijective

section
-- module Solutions.OAIQ043_TH.Thomason_Cones
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Thomason.FiniteVertexChain.tableMap_isIso _root_.OAI.Thomason.GeometricRecognition.Mesh.finiteChains _root_.OAI.Thomason.GeometricRecognition.PolyPoint.finiteBoundedFaces _root_.OAI.Thomason.GrayRecursive.CellWeight.instCoeFunForallCell _root_.OAI.Thomason.GrayRecursive.IntervalHom.chainComparison_empty_isIso _root_.OAI.Thomason.GrayRecursive.IntervalHom.tensorFunctor_isLeftAdjoint _root_.OAI.Thomason.GrayRecursive.IntervalHom.tensorFunctor_preservesColimits _root_.OAI.Thomason.KanQuillen.boundary_small _root_.OAI.Thomason.KanQuillen.boundary_smallCardinal _root_.OAI.Thomason.KanQuillen.boundary_smallObject _root_.OAI.Thomason.OmegaCategory.FilteredColimit.globeHomPreservesColimit _root_.OAI.Thomason.OmegaCategory.FilteredColimit.nInclusion_preservesFilteredColimit _root_.OAI.Thomason.OmegaCategory.FilteredColimit.streetPreservesColimit _root_.OAI.Thomason.OmegaCategory.fullInclusion_nerve_mono _root_.OAI.Thomason.OmegaCategory.fullOnMap_nerve_mono _root_.OAI.Thomason.OmegaCategory.globe_finitelyPresentable _root_.OAI.Thomason.OmegaCategory.hasLimits _root_.OAI.Thomason.OmegaCategory.locallyFinitelyPresentable _root_.OAI.Thomason.OmegaCategory.locallyPresentable _root_.OAI.Thomason.OmegaCategory.nCategoryInclusion_faithful _root_.OAI.Thomason.OmegaCategory.nCategoryInclusion_full _root_.OAI.Thomason.OmegaCategory.nCategoryInclusion_preservesLimits _root_.OAI.Thomason.OmegaCategory.nCategoryInclusion_reflective _root_.OAI.Thomason.OmegaCategory.nInclusion_finitelyAccessible _root_.OAI.Thomason.OmegaCategory.oneFiber_preservesColimits _root_.OAI.Thomason.OmegaCategory.oneSkeletonCategory _root_.OAI.Thomason.OmegaCategory.opFunctor_isEquivalence _root_.OAI.Thomason.OmegaCategory.reverseLabelFunctor_isEquivalence _root_.OAI.Thomason.OmegaCategory.truncation_preservesColimits _root_.OAI.Thomason.OmegaCategory.zeroFiber_preservesColimits _root_.OAI.Thomason.Subdivision.ex_preservesFilteredColimits _root_.OAI.Thomason.Subdivision.finiteNonemptyChains _root_.OAI.Thomason.Subdivision.finiteOrderNerve _root_.OAI.Thomason.Subdivision.sequentialSSetColim_preservesFiniteLimits _root_.OAI.Thomason.categorificationSimplexLeg_isIso _root_.OAI.Thomason.categorification_preservesColimits _root_.OAI.Thomason.finiteInclusion_preservesFilteredColimits _root_.OAI.Thomason.orientalFiniteCells _root_.OAI.Thomason.posetCategorificationTableMap_isIso _root_.OAI.Thomason.posetCategorificationTableMap_ordinal_isIso _root_.OAI.Thomason.raisedOrientals_hasLeftKan _root_.OAI.Thomason.streetPreservesFilteredShape _root_.OAI.Thomason.street_preservesFilteredColimits _root_.OAI.Thomason.thomasonBoundary_smallCardinal _root_.OAI.Thomason.thomasonHorn_smallCardinal _root_.OAI.Thomason.thomasonLeft_finitelyPresentable _root_.OAI.Thomason.thomasonRight_finitelyAccessible _root_.OAI.Thomason.thomasonRight_preservesFilteredColimits _root_.OAI.Thomason.thomasonWeakEquivalences_hasTwoOutOfThreeProperty _root_.OAI.Thomason.thomasonWeakEquivalences_isStableUnderRetracts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Cones. -/

noncomputable section
universe u v w z


namespace Thomason.OmegaCategory

namespace Subcategory

variable {C : OmegaCategory.{u}} (S : Subcategory C)

lemma lift_inclusion {D : OmegaCategory.{v}} (F : Functor D C)
    (hf : ∀ x, F.map x ∈ S.carrier) : Functor.comp (S.lift F hf) S.inclusion = F := rfl

end Subcategory

end Thomason.OmegaCategory

end

end OAI
end

section
-- module Solutions.OAIQ043_TH.Thomason_GrayGenerators
attribute [-instance] _root_.OAI.Thomason.GrayRecursive.CellWeight.instCoeFunForallCell _root_.OAI.Thomason.GrayRecursive.IntervalHom.chainComparison_empty_isIso _root_.OAI.Thomason.GrayRecursive.IntervalHom.tensorFunctor_isLeftAdjoint _root_.OAI.Thomason.GrayRecursive.IntervalHom.tensorFunctor_preservesColimits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Gray Generators. -/

noncomputable section
universe u v w z


namespace Thomason.OmegaCategory

lemma join_factor_right (C : OmegaCategory.{u}) (k l : ℕ) (hkl : k < l)
    (a b : C.Cell) (h : C.target k a = C.source k b) :
    C.join k a b = C.join l (C.join k a (C.source l b)) (C.join k (C.target l a) b) := by
  have hab : C.target k a = C.source k (C.source l b) := by
    rw [C.source_source, min_eq_left (le_of_lt hkl)]; exact h
  have hab' : C.target k (C.target l a) = C.source k b := by
    rw [C.target_target, min_eq_left (le_of_lt hkl)]; exact h
  have h' := C.join_interchange k l hkl a (C.target l a) (C.source l b) b
    (C.source_target_self l a).symm (C.target_source_self l b) hab hab'
  rw [C.join_right_unit l a (C.target l a) (C.source_target_self l a)
    (C.source_target_self l a).symm,
    C.join_left_unit l (C.source l b) b (C.source_source_self l b) (C.target_source_self l b)] at h'
  exact h'

end Thomason.OmegaCategory

end

end OAI
end

section
-- module Solutions.OAIQ043_TH.Thomason_ProperTransfer
attribute [-instance] _root_.OAI.Thomason.GrayRecursive.CellWeight.instCoeFunForallCell _root_.OAI.Thomason.GrayRecursive.IntervalHom.chainComparison_empty_isIso _root_.OAI.Thomason.GrayRecursive.IntervalHom.tensorFunctor_isLeftAdjoint _root_.OAI.Thomason.GrayRecursive.IntervalHom.tensorFunctor_preservesColimits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Proper Transfer. -/

noncomputable section
universe u v w z


namespace Thomason.AbstractTransfer.Boundaries
open CategoryTheory Limits Simplicial PartialOrder KanLocal
open AttachmentComparison (upward)
open HornAttachments
open AbstractTransfer
open BoundaryProperness (PosetAttachment sumData)
attribute [-instance] CategoryTheory.Sigma.sigma

end Thomason.AbstractTransfer.Boundaries

end

noncomputable section
universe u v w z


namespace Thomason
open CategoryTheory Limits AbstractTransfer
attribute [local instance] Cardinal.fact_isRegular_aleph0 Cardinal.orderBotAleph0OrdToType

theorem fullMain_of_rightIntervalExtension : RightIntervalExtensionExists.{u} → FullMain.{u} := by
  rintro ⟨T⟩
  exact ⟨⟨KanQuillen.geometricModel⟩, ⟨omegaEndpointOfGray T⟩,
    fun n hn => ⟨finiteEndpointOfGray T n hn⟩⟩
end Thomason

end

end OAI
end

section
-- module Solutions.OAIQ043_TH.Thomason_StandardComparison
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Standard Comparison. -/

noncomputable section
universe u v w z


namespace Thomason.GrayRecursive.IntervalHom
open CategoryTheory DirectedComplex DirectedComplex.Table GlobeComplex OmegaCategory

variable {M N : DirectedComplex.{u}}

lemma chainComparison_globe (n : ℕ) : chainComparison (complex.{u} n) = (globeTensorIso n).hom := by
  apply (homEquiv (complex.{u} n).nu (K.{u} n).nu).injective
  change curry (uncurry (chainDiagram (complex n))) = curry (uncurry (globeDiagram n))
  rw [curry_uncurry,curry_uncurry]
  apply GlobeComplex.functor_ext
  change tableCell (topTable n) = _
  rw [tableCell_of_bounded n _ (topTable_bounded n),globeDiagram_top]
  apply congrArg ofMap
  have he : tableMap.{u,u} n (topTable n) = Hom.id (complex n) := by
    apply GlobeComplex.hom_ext
    rw [tableMap_nu_top,topTable_bounded]
    rfl
  rw [tableCylinder,he,Hom.cylinder_id]
  rfl

instance chainComparison_globe_isIso (n : ℕ) : IsIso (chainComparison (complex.{u} n)) := by
  rw [chainComparison_globe]
  infer_instance
end Thomason.GrayRecursive.IntervalHom

end

noncomputable section
universe u v w z


namespace Thomason.GrayRecursive.IntervalHom
open CategoryTheory DirectedComplex DirectedComplex.Table GlobeComplex OmegaCategory

theorem fullMain_of_simplexComparison_isIso
    (h : ∀ (P : Type u) [LinearOrder P] [Finite P],
      IsIso (chainComparison (NormalizedChains.complex P))) : FullMain.{u} :=
  fullMain_of_rightIntervalExtension ⟨intervalExtensionOfSimplexIsIso h⟩
end Thomason.GrayRecursive.IntervalHom

end

noncomputable section
universe u v w z


namespace Thomason.GrayRecursive.IntervalHom
open CategoryTheory DirectedComplex

lemma chainComparison_isIso_of_iso {M N : DirectedComplex.{u}} (e : M ≅ N)
    [IsIso (chainComparison M)] : IsIso (chainComparison N) := by
  have h := chainComparison_natural e.hom
  have : IsIso (tensorFunctor.map e.hom.nu) :=
    show IsIso ((nuFunctor ⋙ tensorFunctor).map e.hom) from inferInstance
  have : IsIso ((cylinderFunctor ⋙ nuFunctor).map e.hom) := inferInstance
  have : IsIso (tensorFunctor.map e.hom.nu ≫ chainComparison N) := by
    rw [h]
    change IsIso (chainComparison M ≫ (cylinderFunctor ⋙ nuFunctor).map e.hom)
    exact IsIso.comp_isIso' ‹IsIso (chainComparison M)›
      ‹IsIso ((cylinderFunctor ⋙ nuFunctor).map e.hom)›
  exact IsIso.of_isIso_comp_left (tensorFunctor.map e.hom.nu) (chainComparison N)

end Thomason.GrayRecursive.IntervalHom

end

noncomputable section
universe u v w z


namespace Thomason.GrayRecursive.IntervalHom
open CategoryTheory DirectedComplex

instance chainComparison_simplexZero_isIso :
    IsIso (chainComparison (NormalizedChains.complex (ULift.{u} (Fin 1)))) :=
  chainComparison_isIso_of_iso GlobeComplex.simplexZeroIso

instance chainComparison_simplexOne_isIso :
    IsIso (chainComparison (NormalizedChains.complex (ULift.{u} (Fin 2)))) :=
  chainComparison_isIso_of_iso GlobeComplex.simplexOneIso

end Thomason.GrayRecursive.IntervalHom

end

noncomputable section
universe u v w z


namespace Thomason.GrayRecursive.IntervalHom
open CategoryTheory DirectedComplex

lemma chainComparison_small_isIso (P : Type u) [LinearOrder P] [Fintype P]
    (h : Fintype.card P ≤ 2) :
    IsIso (chainComparison (NormalizedChains.complex P)) := by
  have hcases : Fintype.card P = 0 ∨ Fintype.card P = 1 ∨ Fintype.card P = 2 := by omega
  rcases hcases with h0 | h1 | h2
  · let : IsEmpty P := Fintype.card_eq_zero_iff.mp h0
    infer_instance
  · exact chainComparison_isIso_of_iso (NormalizedChains.complexFinIso P h1)
  · exact chainComparison_isIso_of_iso (NormalizedChains.complexFinIso P h2)

lemma simplexComparison_isIso_of_standard
    (h : ∀ m : ℕ, IsIso (chainComparison
      (NormalizedChains.complex (ULift.{u} (Fin (m+3))))))
    (P : Type u) [LinearOrder P] [Finite P] :
    IsIso (chainComparison (NormalizedChains.complex P)) := by
  let := Fintype.ofFinite P
  by_cases hsmall : Fintype.card P ≤ 2
  · exact chainComparison_small_isIso P hsmall
  · have hcard : Fintype.card P = (Fintype.card P - 3) + 3 := by omega
    let := h (Fintype.card P - 3)
    exact chainComparison_isIso_of_iso (NormalizedChains.complexFinIso P hcard)

theorem fullMain_of_standardSimplexComparison_isIso
    (h : ∀ m : ℕ, IsIso (chainComparison
      (NormalizedChains.complex (ULift.{u} (Fin (m+3)))))) : FullMain.{u} :=
  fullMain_of_simplexComparison_isIso (simplexComparison_isIso_of_standard h)
end Thomason.GrayRecursive.IntervalHom

end

noncomputable section
universe u v w z


namespace Thomason.OmegaCategory.Presentation

lemma cells_induction (P : Presentation.{u}) (Q : P.category.Cell → Prop)
    (gen : ∀ g, Q (P.generator g))
    (source : ∀ k x, Q x → Q (P.category.source k x))
    (target : ∀ k x, Q x → Q (P.category.target k x))
    (comp : ∀ k x y (h : P.category.target k x = P.category.source k y),
      Q x → Q y → Q (P.category.comp k x y h))
    (x : P.category.Cell) : Q x := by
  induction x using Quotient.inductionOn with | h x =>
    rcases x with ⟨x,hx⟩
    induction hx with
    | gen g => exact gen g
    | source k x hx ih => exact source k _ ih
    | target k x hx ih => exact target k _ ih
    | comp k x y hx hy hm ihx ihy =>
      have hc : P.category.target k (Quotient.mk _ ⟨x,hx⟩) =
          P.category.source k (Quotient.mk _ ⟨y,hy⟩) := Quotient.sound hm
      rw [← P.mk_comp k ⟨x,hx⟩ ⟨y,hy⟩ hm hc]
      exact comp k _ _ hc ihx ihy

end Thomason.OmegaCategory.Presentation

end

end OAI
end

section
-- module Solutions.OAIQ043_TH.Thomason_CylinderProfiles
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Cylinder Profiles. -/

noncomputable section
universe u v w z


namespace Thomason.GrayRecursive.IntervalHom
open CategoryTheory DirectedComplex DirectedComplex.Table GlobeComplex OmegaCategory

variable {X Y : OmegaCategory.{u}}

lemma generatorCylinder_endpoint (n : ℕ) (x : X.Cells n) (a : Bool)
    (t : Table (complex.{u} n)) :
    (generatorCylinder n x).map (atEnd a t) =
      ((tensorEndpoint a).app X).map ((GlobeComplex.lift x.val x.property).map t) := by
  have h : OmegaCategory.Functor.comp ((complex n).cylinderEndpoint a).nu (generatorCylinder n x) =
      OmegaCategory.Functor.comp (GlobeComplex.lift x.val x.property) ((tensorEndpoint a).app X) := by
    apply GlobeComplex.functor_ext
    change (tensorPresentation X).generator ⟨n,x,atEnd a (topTable n)⟩ =
      ((tensorEndpoint a).app X).map ((GlobeComplex.lift x.val x.property).map (topTable n))
    rw [lift_top,tensorEndpoint_bounded a X n x]
  exact congrArg (fun F => F.map t) h

lemma tensorParameter_generator (n : ℕ) (x : X.Cells n) (z : Table (K.{u} n)) :
    (tensorParameter X).map ((tensorPresentation X).generator ⟨n,x,z⟩) =
      (faceMap.{u} 0 n false).cylinder.nu.map z := by
  change (globeTensorHom 0).map ((tensorFunctor.map (constantAt X (topTable 0) (topTable_bounded 0))).map
    ((tensorPresentation X).generator ⟨n,x,z⟩)) = _
  erw [tensorFunctor_map_generator,globeTensorHom_generator]
  change (eval n ((globeDiagram 0).map (topTable 0))).map z = _
  rw [globeDiagram_top,eval_ofMap]
  rfl

lemma intervalLabel_cylinder_map {n m : ℕ} (f : Hom (complex.{u} n) (complex.{u} m))
    (z : Table (K.{u} n)) (b : Bool) :
    intervalLabel (f.cylinder.nu.map z) b = intervalLabel z b :=
  f.map_augmentation ((z.row 0 b).2)

@[simp] lemma tensorLabel_generator (n : ℕ) (x : X.Cells n) (z : Table (K.{u} n)) (b : Bool) :
    tensorLabel ((tensorPresentation X).generator ⟨n,x,z⟩) b = intervalLabel z b := by
  unfold tensorLabel
  rw [tensorParameter_generator,intervalLabel_cylinder_map]

@[simp] lemma tensorLabel_endpoint (a b : Bool) (x : X.Cell) :
    tensorLabel (((tensorEndpoint a).app X).map x) b = if a then 1 else 0 := by
  obtain ⟨n,hn⟩ := X.finite_dimension x
  erw [tensorEndpoint_bounded a X n ⟨x,hn⟩,tensorLabel_generator,intervalLabel_end]

lemma tensorLabel_monotone (x : (tensorFunctor.obj X).Cell) :
    tensorLabel x false ≤ tensorLabel x true := interval_monotone ((tensorParameter X).map x)

lemma tensorLabel_source (k : ℕ) (x : (tensorFunctor.obj X).Cell) (b : Bool) :
    tensorLabel ((tensorFunctor.obj X).source k x) b =
      if k = 0 then tensorLabel x false else tensorLabel x b := by
  unfold tensorLabel
  rw [(tensorParameter X).map_source]
  cases k with
  | zero => rfl
  | succ k => rfl

lemma tensorLabel_target (k : ℕ) (x : (tensorFunctor.obj X).Cell) (b : Bool) :
    tensorLabel ((tensorFunctor.obj X).target k x) b =
      if k = 0 then tensorLabel x true else tensorLabel x b := by
  unfold tensorLabel
  rw [(tensorParameter X).map_target]
  cases k with
  | zero => rfl
  | succ k => rfl

lemma tensorLabel_comp (k : ℕ) (x y : (tensorFunctor.obj X).Cell)
    (h : (tensorFunctor.obj X).target k x = (tensorFunctor.obj X).source k y) :
    tensorLabel ((tensorFunctor.obj X).comp k x y h) false = tensorLabel x false ∧
      tensorLabel ((tensorFunctor.obj X).comp k x y h) true = tensorLabel y true := by
  have hs := congrArg (fun z => tensorLabel z false)
    ((tensorFunctor.obj X).source_comp_le 0 k (Nat.zero_le _) x y h)
  have ht := congrArg (fun z => tensorLabel z true)
    ((tensorFunctor.obj X).target_comp_le 0 k (Nat.zero_le _) x y h)
  simpa only [tensorLabel_source,tensorLabel_target,ite_self] using And.intro hs ht

lemma tensorLabel_comp_stationary (k : ℕ) (x y : (tensorFunctor.obj X).Cell)
    (h : (tensorFunctor.obj X).target k x = (tensorFunctor.obj X).source k y) (a : ℤ)
    (hs : tensorLabel ((tensorFunctor.obj X).comp k x y h) false = a)
    (ht : tensorLabel ((tensorFunctor.obj X).comp k x y h) true = a) :
    (∀ b, tensorLabel x b = a) ∧ ∀ b, tensorLabel y b = a := by
  obtain ⟨h₀,h₁⟩ := tensorLabel_comp k x y h
  have hx : tensorLabel x false = a := h₀.symm.trans hs
  have hy : tensorLabel y true = a := h₁.symm.trans ht
  have hm (b : Bool) := congrArg (fun z => tensorLabel z b) h
  simp only [tensorLabel_source,tensorLabel_target] at hm
  have hx' : tensorLabel x true = a := by
    by_cases hk : k = 0
    · have hm' := hm false
      rw [ite_eq_left hk,ite_eq_left hk] at hm'
      have hxle := tensorLabel_monotone x
      have hyle := tensorLabel_monotone y
      omega
    · have hm' := hm true
      simpa only [ite_eq_right hk,hy] using hm'
  have hy' : tensorLabel y false = a := by
    by_cases hk : k = 0
    · have hm' := hm false
      rw [ite_eq_left hk,ite_eq_left hk,hx'] at hm'
      exact hm'.symm
    · have hm' := hm false
      simpa only [ite_eq_right hk,hx] using hm'.symm
  constructor <;> intro b <;> cases b
  · exact hx
  · exact hx'
  · exact hy'
  · exact hy

lemma tensor_zero_faces_are_endpoints (z : (tensorFunctor.obj X).Cell) :
    (∃ (a : Bool) (x : X.Cell), (tensorFunctor.obj X).source 0 z = ((tensorEndpoint a).app X).map x) ∧
      ∃ (a : Bool) (x : X.Cell), (tensorFunctor.obj X).target 0 z = ((tensorEndpoint a).app X).map x := by
  apply (tensorPresentation X).cells_induction (fun z =>
    (∃ (a : Bool) (x : X.Cell), (tensorFunctor.obj X).source 0 z = ((tensorEndpoint a).app X).map x) ∧
      ∃ (a : Bool) (x : X.Cell), (tensorFunctor.obj X).target 0 z = ((tensorEndpoint a).app X).map x)
  · rintro ⟨n,x,t⟩
    have hh (b : Bool) : ∃ (a : Bool) (q : X.Cell),
        (tensorFunctor.obj X).face 0 b ((tensorPresentation X).generator ⟨n,x,t⟩) =
          ((tensorEndpoint a).app X).map q := by
      obtain ⟨a,ha⟩ := endpoint_of_stationary_interval (truncate 0 b t) (by rfl)
      refine ⟨a,(GlobeComplex.lift x.val x.property).map (project (truncate 0 b t)),?_⟩
      change (tensorPresentation X).category.face 0 b ((generatorCylinder n x).map t) = _
      rw [← (generatorCylinder n x).map_face]
      have hf : (K n).nu.face 0 b t = truncate 0 b t := by cases b <;> rfl
      rw [hf]
      conv_lhs => rw [ha]
      exact generatorCylinder_endpoint n x a _
    exact ⟨hh false,hh true⟩
  · intro k z hz
    change (∃ (a : Bool) (x : X.Cell), (tensorFunctor.obj X).source 0 ((tensorFunctor.obj X).source k z) = ((tensorEndpoint a).app X).map x) ∧
      ∃ (a : Bool) (x : X.Cell), (tensorFunctor.obj X).target 0 ((tensorFunctor.obj X).source k z) = ((tensorEndpoint a).app X).map x
    constructor
    · erw [(tensorFunctor.obj X).source_source,Nat.min_eq_left (Nat.zero_le _)]
      exact hz.1
    · cases k with
      | zero =>
        erw [(tensorFunctor.obj X).target_source_self]
        exact hz.1
      | succ k =>
        erw [(tensorFunctor.obj X).target_source]
        simpa only [Nat.zero_lt_succ,ite_true] using hz.2
  · intro k z hz
    change (∃ (a : Bool) (x : X.Cell), (tensorFunctor.obj X).source 0 ((tensorFunctor.obj X).target k z) = ((tensorEndpoint a).app X).map x) ∧
      ∃ (a : Bool) (x : X.Cell), (tensorFunctor.obj X).target 0 ((tensorFunctor.obj X).target k z) = ((tensorEndpoint a).app X).map x
    constructor
    · cases k with
      | zero =>
        erw [(tensorFunctor.obj X).source_target_self]
        exact hz.2
      | succ k =>
        erw [(tensorFunctor.obj X).source_target]
        simpa only [Nat.zero_lt_succ,ite_true] using hz.1
    · erw [(tensorFunctor.obj X).target_target,Nat.min_eq_left (Nat.zero_le _)]
      exact hz.2
  · intro k x y h hx hy
    change (∃ (a : Bool) (t : X.Cell), (tensorFunctor.obj X).source 0 ((tensorFunctor.obj X).comp k x y h) = ((tensorEndpoint a).app X).map t) ∧
      ∃ (a : Bool) (t : X.Cell), (tensorFunctor.obj X).target 0 ((tensorFunctor.obj X).comp k x y h) = ((tensorEndpoint a).app X).map t
    constructor
    · erw [(tensorFunctor.obj X).source_comp_le 0 k (Nat.zero_le _)]
      exact hx.1
    · erw [(tensorFunctor.obj X).target_comp_le 0 k (Nat.zero_le _)]
      exact hy.2

lemma tensorEndpoint_injective (a : Bool) :
    Function.Injective (((tensorEndpoint a).app X).map) := by
  intro x y h
  have hp (t : X.Cell) : (tensorProjection.app X).map (((tensorEndpoint a).app X).map t) = t :=
    congrArg (fun F : X ⟶ X => F.map t) (congrArg (fun η => η.app X) (tensorEndpoint_projection a))
  have hh := congrArg (tensorProjection.app X).map h
  simpa only [hp] using hh

lemma tensorEndpoint_eq_iff (a b : Bool) (x y : X.Cell) :
    ((tensorEndpoint a).app X).map x = ((tensorEndpoint b).app X).map y ↔ a = b ∧ x = y := by
  constructor
  · intro h
    have hh := congrArg (fun z => tensorLabel z false) h
    rw [tensorLabel_endpoint,tensorLabel_endpoint] at hh
    have hab : a = b := by cases a <;> cases b <;> first | rfl | norm_num at hh
    subst b
    exact ⟨rfl,tensorEndpoint_injective a h⟩
  · rintro ⟨rfl,rfl⟩
    rfl

lemma tensor_object_endpoint (z : (tensorFunctor.obj X).Cell)
    (hz : (tensorFunctor.obj X).source 0 z = z) :
    ∃! ax : Bool × X.Objects, z = ((tensorEndpoint ax.1).app X).map ax.2.val := by
  obtain ⟨a,x,hx⟩ := (tensor_zero_faces_are_endpoints z).1
  have he : z = ((tensorEndpoint a).app X).map x := hz.symm.trans hx
  have hxb : X.source 0 x = x := by
    apply tensorEndpoint_injective a
    change ((tensorEndpoint a).app X).map (((𝟭 OmegaCategory).obj X).source 0 x) = _
    rw [((tensorEndpoint a).app X).map_source,← he,hz]
  refine ⟨⟨a,⟨x,hxb⟩⟩,he,?_⟩
  rintro ⟨b,y⟩ hy
  have hh := (tensorEndpoint_eq_iff b a y.val x).mp (hy.symm.trans he)
  exact Prod.ext hh.1 (Subtype.ext hh.2)

lemma tensor_object_reconstruct (z : (tensorFunctor.obj X).Cell)
    (hz : (tensorFunctor.obj X).source 0 z = z) (a : Bool)
    (ha : tensorLabel z false = if a then 1 else 0) :
    z = ((tensorEndpoint a).app X).map ((tensorProjection.app X).map z) := by
  obtain ⟨⟨b,x⟩,hx,_⟩ := tensor_object_endpoint z hz
  have he := ha
  rw [hx,tensorLabel_endpoint] at he
  have hab : a = b := by cases a <;> cases b <;> first | rfl | norm_num at he
  subst b
  have hp := congrArg (fun F : X ⟶ X => F.map x.val)
    (congrArg (fun η => η.app X) (tensorEndpoint_projection a))
  change (tensorProjection.app X).map (((tensorEndpoint a).app X).map x.val) = x.val at hp
  rw [hx,hp]

lemma generatorCylinder_stationary (n : ℕ) (x : X.Cells n) (z : Table (K.{u} n)) (a : Bool)
    (hs : intervalLabel z false = if a then 1 else 0)
    (ht : intervalLabel z true = if a then 1 else 0) :
    (tensorPresentation X).generator ⟨n,x,z⟩ =
      ((tensorEndpoint a).app X).map ((tensorProjection.app X).map
        ((tensorPresentation X).generator ⟨n,x,z⟩)) := by
  obtain ⟨b,hb⟩ := endpoint_of_stationary_interval z (ht.trans hs.symm)
  have he := hs
  change z = atEnd b (project z) at hb
  rw [hb,intervalLabel_end] at he
  have hab : a = b := by cases a <;> cases b <;> first | rfl | norm_num at he
  subst b
  erw [tensorProjection_generator X n x z]
  change (generatorCylinder n x).map z = _
  conv_lhs => rw [hb]
  exact generatorCylinder_endpoint n x a _

lemma tensor_stationary_reconstruct (z : (tensorFunctor.obj X).Cell) (a : Bool)
    (hs : tensorLabel z false = if a then 1 else 0)
    (ht : tensorLabel z true = if a then 1 else 0) :
    z = ((tensorEndpoint a).app X).map ((tensorProjection.app X).map z) := by
  let Q (z : (tensorFunctor.obj X).Cell) := ∀ a : Bool,
    tensorLabel z false = (if a then 1 else 0) → tensorLabel z true = (if a then 1 else 0) →
      z = ((tensorEndpoint a).app X).map ((tensorProjection.app X).map z)
  suffices hh : Q z from hh a hs ht
  apply (tensorPresentation X).cells_induction Q
  · rintro ⟨n,x,z⟩ a hs ht
    rw [tensorLabel_generator n x z false] at hs
    rw [tensorLabel_generator n x z true] at ht
    exact generatorCylinder_stationary n x z a hs ht
  · intro k x ih a hs ht
    change tensorLabel ((tensorFunctor.obj X).source k x) false = _ at hs
    change tensorLabel ((tensorFunctor.obj X).source k x) true = _ at ht
    cases k with
    | zero => exact tensor_object_reconstruct _ ((tensorFunctor.obj X).source_source_self 0 x) a hs
    | succ k =>
      erw [tensorLabel_source] at hs ht
      simp only [Nat.succ_ne_zero,ite_false] at hs ht
      have hh := congrArg ((tensorFunctor.obj X).source (k+1)) (ih a hs ht)
      erw [← ((tensorEndpoint a).app X).map_source,← (tensorProjection.app X).map_source] at hh
      exact hh
  · intro k x ih a hs ht
    change tensorLabel ((tensorFunctor.obj X).target k x) false = _ at hs
    change tensorLabel ((tensorFunctor.obj X).target k x) true = _ at ht
    cases k with
    | zero => exact tensor_object_reconstruct _ ((tensorFunctor.obj X).source_target_self 0 x) a hs
    | succ k =>
      erw [tensorLabel_target] at hs ht
      simp only [Nat.succ_ne_zero,ite_false] at hs ht
      have hh := congrArg ((tensorFunctor.obj X).target (k+1)) (ih a hs ht)
      erw [← ((tensorEndpoint a).app X).map_target,← (tensorProjection.app X).map_target] at hh
      exact hh
  · intro k x y h ihx ihy a hs ht
    obtain ⟨hx,hy⟩ := tensorLabel_comp_stationary k x y h _ hs ht
    have hxx := ihx a (hx false) (hx true)
    have hyy := ihy a (hy false) (hy true)
    let e : tensorFunctor.obj X ⟶ tensorFunctor.obj X := tensorProjection.app X ≫ (tensorEndpoint a).app X
    change (tensorFunctor.obj X).comp k x y h = e.map ((tensorFunctor.obj X).comp k x y h)
    rw [e.map_comp k x y h (e.map_composable h)]
    congr 1
end Thomason.GrayRecursive.IntervalHom

end

noncomputable section
universe u v w z


namespace Thomason.DirectedComplex

namespace CylinderTables
open Table
variable {M : DirectedComplex.{u}}

lemma label_truncate (k : ℕ) (e : Bool) (t : Table M.cylinder) (b : Bool) :
    label (truncate k e t) b = if k = 0 then label t e else label t b := by
  cases k with
  | zero => rfl
  | succ k => rfl

lemma label_comp (k : ℕ) (x y : Table M.cylinder)
    (h : truncate k true x = truncate k false y) :
    label (comp k x y h) false = label x false ∧
      label (comp k x y h) true = label y true := by
  have hs := congrArg (fun z : Table M.cylinder => label z false) (source_comp_le 0 k (Nat.zero_le _) x y h)
  have ht := congrArg (fun z : Table M.cylinder => label z true) (target_comp_le 0 k (Nat.zero_le _) x y h)
  simpa only [label_truncate,ite_self] using And.intro hs ht

lemma label_endpoint (a b : Bool) (x : Table M) :
    label ((M.cylinderEndpoint a).table x) b = if a then 1 else 0 := by
  cases a
  · exact M.augmentation.map_zero
  · exact x.augmentation b

lemma label_cylinder_map {N : DirectedComplex.{v}} (f : Hom M N) (x : Table M.cylinder) (b : Bool) :
    label (f.cylinder.table x) b = label x b := f.map_augmentation (side x true 0 b)

end CylinderTables
end Thomason.DirectedComplex

end

noncomputable section
universe u v w z


namespace Thomason.GrayRecursive.IntervalHom
open CategoryTheory DirectedComplex DirectedComplex.Table GlobeComplex OmegaCategory

variable {M : DirectedComplex.{u}}

lemma chainComparison_label (z : (tensorFunctor.obj M.nu).Cell) (b : Bool) :
    CylinderTables.label ((chainComparison M).map z) b = tensorLabel z b := by
  suffices h : ∀ b, CylinderTables.label ((chainComparison M).map z) b = tensorLabel z b from h b
  apply (tensorPresentation M.nu).cells_induction (fun z =>
    ∀ b, CylinderTables.label ((chainComparison M).map z) b = tensorLabel z b)
  · rintro ⟨n,x,t⟩ b
    erw [chainComparison_generator,tensorLabel_generator]
    change CylinderTables.label ((tableMap n x.val).cylinder.table t) b = intervalLabel t b
    exact CylinderTables.label_cylinder_map (tableMap n x.val) t b
  · intro k x ih b
    change CylinderTables.label ((chainComparison M).map ((tensorFunctor.obj M.nu).source k x)) b =
      tensorLabel ((tensorFunctor.obj M.nu).source k x) b
    erw [(chainComparison M).map_source,tensorLabel_source]
    change CylinderTables.label (truncate k false ((chainComparison M).map x)) b = _
    erw [CylinderTables.label_truncate,ih,ih]
  · intro k x ih b
    change CylinderTables.label ((chainComparison M).map ((tensorFunctor.obj M.nu).target k x)) b =
      tensorLabel ((tensorFunctor.obj M.nu).target k x) b
    erw [(chainComparison M).map_target,tensorLabel_target]
    change CylinderTables.label (truncate k true ((chainComparison M).map x)) b = _
    erw [CylinderTables.label_truncate,ih,ih]
  · intro k x y h ihx ihy b
    change CylinderTables.label ((chainComparison M).map ((tensorFunctor.obj M.nu).comp k x y h)) b = _
    rw [(chainComparison M).map_comp k x y h ((chainComparison M).map_composable h)]
    have ht := CylinderTables.label_comp k ((chainComparison M).map x) ((chainComparison M).map y)
      ((chainComparison M).map_composable h)
    have hs := tensorLabel_comp k x y h
    cases b
    · exact ht.1.trans ((ihx false).trans hs.1.symm)
    · exact ht.2.trans ((ihy true).trans hs.2.symm)

lemma chainComparison_project (z : (tensorFunctor.obj M.nu).Cell) :
    CylinderTables.project ((chainComparison M).map z) = (tensorProjection.app M.nu).map z :=
  congrArg (fun F : tensorFunctor.obj M.nu ⟶ M.nu => F.map z) (chainComparison_projection M)

lemma chainComparison_endpoint_apply (a : Bool) (x : Table M) :
    (chainComparison M).map (((tensorEndpoint a).app M.nu).map x) = (M.cylinderEndpoint a).table x :=
  congrArg (fun F : M.nu ⟶ M.cylinder.nu => F.map x) (chainComparison_endpoint M a)

lemma chainComparison_endpoint_fiber (z : (tensorFunctor.obj M.nu).Cell)
    (a : Bool) (x : Table M) :
    (chainComparison M).map z = (M.cylinderEndpoint a).table x ↔
      z = ((tensorEndpoint a).app M.nu).map x := by
  constructor
  · intro hz
    have hlabel (b : Bool) : tensorLabel z b = if a then 1 else 0 := by
      rw [← chainComparison_label,hz,CylinderTables.label_endpoint]
    have hp : (tensorProjection.app M.nu).map z = x := by
      rw [← chainComparison_project,hz]
      exact congrArg (fun F : M.nu ⟶ M.nu => F.map x)
        (show (M.cylinderEndpoint a).nu ≫ M.cylinderProjection.nu = 𝟙 M.nu from
          congrArg Hom.nu (M.cylinderProjection_endpoint a))
    exact (tensor_stationary_reconstruct z a (hlabel false) (hlabel true)).trans
      (congrArg ((tensorEndpoint a).app M.nu).map hp)
  · rintro rfl
    exact chainComparison_endpoint_apply a x

end Thomason.GrayRecursive.IntervalHom

end

end OAI
end

section
-- module Solutions.OAIQ043_TH.Thomason_BoundedCylinders
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Bounded Cylinders. -/

noncomputable section
universe u v w z


namespace Thomason.GrayRecursive.IntervalHom
open CategoryTheory DirectedComplex DirectedComplex.Table GlobeComplex OmegaCategory

variable {X Y : OmegaCategory.{u}} {M : DirectedComplex.{u}}

lemma chainComparison_verticalCell (n : ℕ) (x : M.nu.Cells n) :
    (chainComparison M).map (verticalCell n x) = verticalTable x.val := by
  change (chainComparison M).map ((tensorPresentation M.nu).generator ⟨n,x,_⟩) = _
  erw [chainComparison_generator,tableCylinder_vertical]
  exact congrArg verticalTable x.property

lemma generatorCylinder_vertical_face (n m : ℕ) (x : X.Cells n) (a : Bool) :
    (generatorCylinder n x).map (verticalTable (truncate m a (topTable n))) =
      verticalCell m ⟨X.face m a x.val, by
        cases a
        · exact X.source_source_self m x.val
        · exact X.source_target_self m x.val⟩ := by
  let v : X.Cells m := ⟨X.face m a x.val, by
    cases a
    · exact X.source_source_self m x.val
    · exact X.source_target_self m x.val⟩
  have he := tensorUnitCell_face m a x.val
  rw [tensorUnitCell_of_bounded n x, face_ofMap] at he
  change tensorUnitCell v.val = _ at he
  rw [tensorUnitCell_of_bounded m v] at he
  have h := congrArg (fun t => (eval m t).map (verticalTable (topTable m))) he
  rw [eval_ofMap_self, eval_ofMap_self] at h
  change verticalCell m v =
    (generatorCylinder n x).map ((faceMap n m a).cylinder.nu.map (verticalTable (topTable m))) at h
  rw [verticalTable_natural,faceMap_top] at h
  exact h.symm

lemma verticalCell_dimension_independent (n m : ℕ) (hnm : n ≤ m) (x : X.Cells n) :
    verticalCell m ⟨x.val, X.source_fixed_upwards hnm x.property⟩ = verticalCell n x := by
  have h := generatorCylinder_vertical_face n m x false
  have hd : truncate m false (topTable.{u} n) = topTable n :=
    (complex n).nu.source_fixed_upwards hnm (topTable_bounded n)
  rw [hd] at h
  have hx : X.face m false x.val = x.val := X.source_fixed_upwards hnm x.property
  exact (congrArg (verticalCell m) (Subtype.ext hx.symm)).trans h.symm

end Thomason.GrayRecursive.IntervalHom

end

noncomputable section
universe u v w z


namespace Thomason.GrayRecursive.IntervalHom
open CategoryTheory DirectedComplex DirectedComplex.Table GlobeComplex OmegaCategory

variable {X Y : OmegaCategory.{u}}

lemma tensor_cells_induction (P : (tensorFunctor.obj X).Cell → Prop)
    (hend : ∀ a x, P (((tensorEndpoint a).app X).map x))
    (hvertical : ∀ n (x : X.Cells n), P (verticalCell n x))
    (hsource : ∀ k x, P x → P ((tensorFunctor.obj X).source k x))
    (htarget : ∀ k x, P x → P ((tensorFunctor.obj X).target k x))
    (hcomp : ∀ k x y (h : (tensorFunctor.obj X).target k x =
      (tensorFunctor.obj X).source k y), P x → P y →
      P ((tensorFunctor.obj X).comp k x y h)) : ∀ z, P z := by
  apply (tensorPresentation X).cells_induction P
  · rintro ⟨n,x,z⟩
    change P ((generatorCylinder n x).map z)
    apply GrayRecursive.generated n (fun t => P ((generatorCylinder n x).map t))
    · intro a t
      rw [generatorCylinder_endpoint]
      exact hend a _
    · intro t
      obtain ⟨p,a,_,he⟩ := table_classification t
      rw [he,generatorCylinder_vertical_face]
      exact hvertical p _
    · intro k s t h hs ht
      erw [(generatorCylinder n x).map_comp k s t h ((generatorCylinder n x).map_composable h)]
      exact hcomp k _ _ _ hs ht
  · exact hsource
  · exact htarget
  · exact hcomp

lemma verticalCell_eq_of_value {n m : ℕ} (x : X.Cells n) (y : X.Cells m)
    (h : x.val = y.val) : verticalCell n x = verticalCell m y := by
  let xn : X.Cells (max n m) := ⟨x.val,X.source_fixed_upwards (le_max_left _ _) x.property⟩
  let ym : X.Cells (max n m) := ⟨y.val,X.source_fixed_upwards (le_max_right _ _) y.property⟩
  calc
    verticalCell n x = verticalCell (max n m) xn :=
      (verticalCell_dimension_independent n (max n m) (le_max_left _ _) x).symm
    _ = verticalCell (max n m) ym := congrArg (verticalCell (max n m)) (Subtype.ext h)
    _ = verticalCell m y := verticalCell_dimension_independent m (max n m) (le_max_right _ _) y

lemma verticalCell_bounded_of_bounded (p n : ℕ) (x : X.Cells p)
    (hx : X.source n x.val = x.val) :
    (tensorFunctor.obj X).source (n+1) (verticalCell p x) = verticalCell p x := by
  rw [verticalCell_eq_of_value x (⟨x.val,hx⟩ : X.Cells n) rfl]
  exact verticalCell_bounded n _

lemma tensor_truncated {n : ℕ} (hn : X.IsTruncated n) :
    (tensorFunctor.obj X).IsTruncated (n+1) := by
  apply tensor_cells_induction (fun z => (tensorFunctor.obj X).source (n+1) z = z)
  · intro a x
    rw [← ((tensorEndpoint a).app X).map_source]
    exact congrArg ((tensorEndpoint a).app X).map (X.source_fixed_upwards (by omega) (hn x))
  · intro p x
    exact verticalCell_bounded_of_bounded p n x (hn x.val)
  · intro k x hx
    by_cases hk : k < n+1
    · exact (tensorFunctor.obj X).source_fixed_upwards (by omega)
        ((tensorFunctor.obj X).source_source_self k x)
    · rw [(tensorFunctor.obj X).source_fixed_upwards (by omega : n+1 ≤ k) hx]
      exact hx
  · intro k x hx
    by_cases hk : k < n+1
    · exact (tensorFunctor.obj X).source_fixed_upwards (by omega)
        ((tensorFunctor.obj X).source_target_self k x)
    · rw [(tensorFunctor.obj X).target_eq_self_of_source_eq_self
        ((tensorFunctor.obj X).source_fixed_upwards (by omega : n+1 ≤ k) hx)]
      exact hx
  · intro k x y h hx hy
    by_cases hk : k < n+1
    · rw [(tensorFunctor.obj X).source_comp_gt (n+1) k hk x y h
        ((tensorFunctor.obj X).source_composable hk h)]
      congr 1
    · rw [(tensorFunctor.obj X).comp_of_left_source_fixed k x y h
        ((tensorFunctor.obj X).source_fixed_upwards (by omega) hx)]
      exact hy
end Thomason.GrayRecursive.IntervalHom

end

noncomputable section
universe u v w z


namespace Thomason.GrayRecursive.IntervalHom
open CategoryTheory DirectedComplex DirectedComplex.Table GlobeComplex OmegaCategory

variable {X Y : OmegaCategory.{u}}

lemma tensor_bounded_cells_induction (k : ℕ) (P : (tensorFunctor.obj X).Cell → Prop)
    (hend : ∀ a x, X.source k x = x → P (((tensorEndpoint a).app X).map x))
    (hvertical : ∀ r, r < k → ∀ x : X.Cells r, P (verticalCell r x))
    (hlower : ∀ r, r < k → ∀ z, (tensorFunctor.obj X).source r z = z → P z)
    (hcomp : ∀ r, r < k → ∀ x y
      (_hx : (tensorFunctor.obj X).source k x = x)
      (_hy : (tensorFunctor.obj X).source k y = y)
      (h : (tensorFunctor.obj X).target r x = (tensorFunctor.obj X).source r y),
        P x → P y → P ((tensorFunctor.obj X).comp r x y h)) :
    ∀ z, (tensorFunctor.obj X).source k z = z → P z := by
  let T := tensorFunctor.obj X
  have hg (n : ℕ) (x : X.Cells n) (t : Table (K n))
      (ht : truncate k false t = t) : P ((generatorCylinder n x).map t) := by
    have h := generated_bounded n k
      (fun t => T.source k ((generatorCylinder n x).map t) = (generatorCylinder n x).map t ∧
        P ((generatorCylinder n x).map t)) ?_ ?_ ?_ t ht
    · exact h.2
    · intro a y hy
      rw [generatorCylinder_endpoint]
      have hb : X.source k ((GlobeComplex.lift x.val x.property).map y) = (GlobeComplex.lift x.val x.property).map y := by
        erw [← (GlobeComplex.lift x.val x.property).map_source]
        exact congrArg (GlobeComplex.lift x.val x.property).map hy
      exact ⟨(((tensorEndpoint a).app X).map_source k _).symm.trans
        (congrArg ((tensorEndpoint a).app X).map hb), hend a _ hb⟩
    · intro r hr y hy
      obtain ⟨p,a,_,hpr,rfl⟩ := bounded_table_classification y hy
      rw [generatorCylinder_vertical_face]
      exact ⟨T.source_fixed_upwards (by omega : p+1 ≤ k) (verticalCell_bounded p _),
        hvertical p (by omega) _⟩
    · intro l s t h hs ht
      erw [(generatorCylinder n x).map_comp l s t h ((generatorCylinder n x).map_composable h)]
      by_cases hl : l < k
      · refine ⟨?_, hcomp l hl _ _ hs.1 ht.1 _ hs.2 ht.2⟩
        erw [T.source_comp_gt k l hl _ _ _ (T.source_composable hl
          ((generatorCylinder n x).map_composable h))]
        exact T.comp_congr_cells l _ _ hs.1 ht.1
      · erw [T.comp_of_left_source_fixed l _ _ _ (T.source_fixed_upwards (by omega) hs.1)]
        exact ht
  have hh : ∀ z : T.Cell, P (T.source k z) ∧ P (T.target k z) := by
    apply (tensorPresentation X).cells_induction
      (fun z => P (T.source k z) ∧ P (T.target k z))
    · rintro ⟨n,x,z⟩
      change Table (K n) at z
      change P (T.source k ((generatorCylinder n x).map z)) ∧
        P (T.target k ((generatorCylinder n x).map z))
      erw [← (generatorCylinder n x).map_source, ← (generatorCylinder n x).map_target]
      exact ⟨hg n x (truncate k false z) (by simp only [truncate_truncate,lt_self_iff_false,ite_false]),
        hg n x (truncate k true z) (by simp only [truncate_truncate,lt_self_iff_false,ite_false])⟩
    · intro i z hz
      change P (T.source k (T.source i z)) ∧ P (T.target k (T.source i z))
      by_cases hi : i < k
      · erw [T.source_source, min_eq_right hi.le, T.target_source, ite_eq_right (by omega : ¬ k < i)]
        exact ⟨hlower i hi _ (T.source_source_self i z), hlower i hi _ (T.source_source_self i z)⟩
      · by_cases he : k = i
        · subst i
          erw [T.source_source_self,T.target_source_self]
          exact And.intro hz.1 hz.1
        · erw [T.source_source, min_eq_left (by omega : k ≤ i),
            T.target_source, ite_eq_left (by omega : k < i)]
          exact hz
    · intro i z hz
      change P (T.source k (T.target i z)) ∧ P (T.target k (T.target i z))
      by_cases hi : i < k
      · erw [T.source_target, ite_eq_right (by omega : ¬ k < i), T.target_target, min_eq_right hi.le]
        exact ⟨hlower i hi _ (T.source_target_self i z), hlower i hi _ (T.source_target_self i z)⟩
      · by_cases he : k = i
        · subst i
          erw [T.source_target_self,T.target_target_self]
          exact And.intro hz.2 hz.2
        · erw [T.source_target, ite_eq_left (by omega : k < i), T.target_target, min_eq_left (by omega : k ≤ i)]
          exact hz
    · intro l x y h hx hy
      by_cases hl : l < k
      · erw [T.source_comp_gt k l hl _ _ _ (T.source_composable hl h),
          T.target_comp_gt k l hl _ _ _ (T.target_composable hl h)]
        exact ⟨hcomp l hl _ _ (T.source_source_self k x) (T.source_source_self k y) _ hx.1 hy.1,
          hcomp l hl _ _ (T.source_target_self k x) (T.source_target_self k y) _ hx.2 hy.2⟩
      · erw [T.source_comp_le k l (by omega), T.target_comp_le k l (by omega)]
        exact ⟨hx.1,hy.2⟩
  intro z hz
  have hh₁ := (hh z).1
  change P ((tensorFunctor.obj X).source k z) at hh₁
  simpa only [hz] using hh₁
end Thomason.GrayRecursive.IntervalHom

end

end OAI
end

section
-- module Solutions.OAIQ043_TH.Thomason_RankedAtoms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Ranked Atoms. -/

noncomputable section
universe u v w z


namespace Thomason.DirectedComplex
open Table

attribute [instance] RankedAtoms.finite
namespace RankedAtoms
variable {K : DirectedComplex.{u}} (A : RankedAtoms.{u,v} K)
open scoped Classical
include A

lemma basis_own (b : A.Index) : A.basis (A.dim b) b = (A.atom b).row (A.dim b) false := by
  simp [basis]

attribute [local instance] OAI.Thomason.DirectedComplex.RankedAtoms.rankedAtomsDecidableEq
lemma coefficient_basis (p : ℕ) (b c : A.Index) :
    A.coefficient c p (A.basis p b) =
      if A.dim b = p then (if b = c then 1 else 0) else 0 := by
  classical
  by_cases h : A.dim b = p
  · subst p
    rw [A.basis_own, A.top]
    simp
  · simp [basis,h]

lemma coefficient_eq_zero (b : A.Index) (p : ℕ) (x : K.Chain p) (h : A.dim b ≠ p) :
    A.coefficient b p x = 0 := by
  by_contra hn
  exact h (A.homogeneous b p x hn)

lemma expansion (p : ℕ) (x : K.Chain p) :
    ∑ b, A.coefficient b p x • A.basis p b = x := by
  classical
  apply A.ext p
  intro c
  rw [map_sum]
  simp only [map_zsmul, A.coefficient_basis]
  rw [Finset.sum_eq_single c]
  · by_cases h : A.dim c = p
    · simp [h]
    · simp [h,A.coefficient_eq_zero c p x h]
  · intro b _ hbc
    simp [hbc]
  · simp

lemma basis_positive (p : ℕ) (b : A.Index) : A.basis p b ∈ K.positive p := by
  classical
  apply (A.positive p _).mpr
  intro c
  rw [A.coefficient_basis]
  split_ifs <;> omega

lemma derivative_rank (p : ℕ) (b c : A.Index) (hb : A.dim b = p+1) :
    (0 < A.coefficient c p (K.d p (A.basis (p+1) b)) → A.rank c < A.rank b) ∧
    (A.coefficient c p (K.d p (A.basis (p+1) b)) < 0 → A.rank b < A.rank c) := by
  have hd : A.basis (p+1) b = (A.atom b).row (p+1) false := by
    rw [← hb,A.basis_own]
  rw [hd,(A.atom b).boundary,map_sub]
  have hs := (A.positive p _).mp ((A.atom b).positive p false) c
  have ht := (A.positive p _).mp ((A.atom b).positive p true) c
  constructor
  · intro h
    exact A.ranked b p (by omega) true c (by omega)
  · intro h
    exact A.ranked b p (by omega) false c (by omega)

lemma mass_apply (p : ℕ) (x : K.Chain p) :
    A.mass p x = ∑ b, A.coefficient b p x := by simp [mass]

lemma mass_basis (p : ℕ) (b : A.Index) (hb : A.dim b = p) :
    A.mass p (A.basis p b) = 1 := by
  classical
  rw [A.mass_apply]
  simp only [A.coefficient_basis, ite_eq_left hb]
  simp

lemma mass_pos (p : ℕ) (x : K.Chain p) (hx : x ∈ K.positive p)
    (b : A.Index) (hb : 0 < A.coefficient b p x) : 0 < A.mass p x := by
  rw [A.mass_apply]
  exact Finset.sum_pos' (fun c _ => (A.positive p x).mp hx c)
    ⟨b,Finset.mem_univ _,hb⟩

lemma augmentation_basis (b : A.Index) :
    K.augmentation (A.basis 0 b) = if A.dim b = 0 then 1 else 0 := by
  by_cases h : A.dim b = 0
  · have he : A.basis 0 b = (A.atom b).row 0 false := by rw [← h,A.basis_own]
    rw [he,(A.atom b).augmentation,ite_eq_left h]
  · simp [basis,h]

lemma augmentation_eq_mass (x : K.Chain 0) : K.augmentation x = A.mass 0 x := by
  classical
  conv_lhs => rw [← A.expansion 0 x]
  rw [map_sum,A.mass_apply]
  apply Finset.sum_congr rfl
  intro b _
  rw [map_zsmul,A.augmentation_basis]
  by_cases h : A.dim b = 0
  · simp [h]
  · simp [h,A.coefficient_eq_zero b 0 x h]

lemma positive_augmentation_zero (x : K.Chain 0) (hx : x ∈ K.positive 0)
    (he : K.augmentation x = 0) : x = 0 := by
  apply A.ext 0
  intro b
  rw [map_zero]
  have hb := (A.positive 0 x).mp hx b
  by_contra hn
  have hp := A.mass_pos 0 x hx b (by omega)
  rw [A.augmentation_eq_mass x] at he
  omega

lemma peel_remainder (p : ℕ) (x : K.Chain p) (hx : x ∈ K.positive p)
    (b : A.Index) (hb : 0 < A.coefficient b p x) :
    x - A.basis p b ∈ K.positive p := by
  classical
  have hd := A.homogeneous b p x (ne_of_gt hb)
  apply (A.positive p _).mpr
  intro c
  rw [map_sub,A.coefficient_basis,ite_eq_left hd]
  by_cases h : b = c
  · subst c; simp only; omega
  · rw [ite_eq_right h,sub_zero]
    exact (A.positive p x).mp hx c

lemma objects_atomic (x : Table K) (hx : truncate 0 false x = x) :
    ∃ b : A.Index, A.dim b = 0 ∧ x = A.atom b := by
  classical
  have he : A.mass 0 (x.row 0 false) = 1 := by rw [← A.augmentation_eq_mass,x.augmentation]
  obtain ⟨b,hb⟩ : ∃ b, 0 < A.coefficient b 0 (x.row 0 false) := by
    by_contra h
    push Not at h
    have hz : A.mass 0 (x.row 0 false) ≤ 0 := by
      rw [A.mass_apply]
      exact Finset.sum_nonpos (fun b _ => h b)
    omega
  have hd := A.homogeneous b 0 (x.row 0 false) (ne_of_gt hb)
  have hb' : A.basis 0 b = (A.atom b).row 0 false := by rw [← hd,A.basis_own]
  have hrem := A.peel_remainder 0 (x.row 0 false) (x.positive 0 false) b hb
  have haug : K.augmentation (x.row 0 false - A.basis 0 b) = 0 := by
    rw [map_sub,x.augmentation,A.augmentation_basis,ite_eq_left hd,sub_self]
  have hr := sub_eq_zero.mp (A.positive_augmentation_zero _ hrem haug)
  refine ⟨b,hd,?_⟩
  have ha : truncate 0 false (A.atom b) = A.atom b := hd ▸ A.bounded b
  ext p e
  by_cases hp : p = 0
  · subst p
    cases e
    · exact hr.trans hb'
    · rw [← row_top_fixed x hx,← row_top_fixed (A.atom b) ha]
      exact hr.trans hb'
  · rw [row_above_fixed x hx (by omega) e,row_above_fixed (A.atom b) ha (by omega) e]

lemma peel_positive (p : ℕ) (z : K.Chain (p+1)) (x : K.Chain p)
    (hz : z ∈ K.positive (p+1)) (hx : x ∈ K.positive p)
    (hy : x + K.d p z ∈ K.positive p) (b : A.Index)
    (hb : 0 < A.coefficient b (p+1) z)
    (hmax : ∀ c, A.coefficient c (p+1) z ≠ 0 → A.rank c ≤ A.rank b) :
    x + K.d p (A.basis (p+1) b) ∈ K.positive p := by
  classical
  have hd := A.homogeneous b (p+1) z (ne_of_gt hb)
  apply (A.positive p _).mpr
  intro t
  rw [map_add]
  by_cases ht : 0 ≤ A.coefficient t p (K.d p (A.basis (p+1) b))
  · exact add_nonneg ((A.positive p x).mp hx t) ht
  have hrank := (A.derivative_rank p b t hd).2 (lt_of_not_ge ht)
  have hnonpos (c : A.Index) :
      A.coefficient c (p+1) z * A.coefficient t p (K.d p (A.basis (p+1) c)) ≤ 0 := by
    by_cases hc : A.coefficient c (p+1) z = 0
    · simp [hc]
    have hdc := A.homogeneous c (p+1) z hc
    apply mul_nonpos_of_nonneg_of_nonpos ((A.positive (p+1) z).mp hz c)
    by_contra hn
    have hr := (A.derivative_rank p c t hdc).1 (lt_of_not_ge hn)
    have hm := hmax c hc
    omega
  have hbd : A.coefficient t p (K.d p z) ≤
      A.coefficient b (p+1) z * A.coefficient t p (K.d p (A.basis (p+1) b)) := by
    conv_lhs => rw [← A.expansion (p+1) z]
    rw [map_sum,map_sum]
    simp only [map_zsmul,smul_eq_mul]
    calc
      _ ≤ ∑ c : A.Index, if c = b then
        A.coefficient b (p+1) z * A.coefficient t p (K.d p (A.basis (p+1) b)) else 0 := by
          apply Finset.sum_le_sum
          intro c _
          by_cases h : c = b
          · subst c; simp only; exact le_rfl
          · rw [ite_eq_right h]; exact hnonpos c
      _ = _ := by simp
  have hmul : A.coefficient b (p+1) z * A.coefficient t p (K.d p (A.basis (p+1) b)) ≤
      A.coefficient t p (K.d p (A.basis (p+1) b)) := by
    calc
      _ ≤ 1 * A.coefficient t p (K.d p (A.basis (p+1) b)) :=
        mul_le_mul_of_nonpos_right (by omega) (by omega)
      _ = _ := one_mul _
  have hy' := (A.positive p _).mp hy t
  rw [map_add] at hy'
  omega

lemma top_pasting {n : ℕ} (y : Table K) (hy : truncate (n+1) false y = y) :
    A.TopPasting n y := by
  classical
  generalize hm : (A.mass (n+1) (y.row (n+1) false)).toNat = m
  induction m using Nat.strong_induction_on generalizing y with
  | h m ih =>
    let z := y.row (n+1) false
    have hz : z ∈ K.positive (n+1) := y.positive (n+1) false
    by_cases he : z = 0
    · exact .identity y (fixed_of_top_zero hy he)
    let S := Finset.univ.filter (fun b => A.coefficient b (n+1) z ≠ 0)
    have hs : S.Nonempty := by
      by_contra hn
      apply he
      apply A.ext (n+1)
      intro b
      rw [map_zero]
      by_contra hb
      exact hn ⟨b,by simp [S,hb]⟩
    obtain ⟨b,hb,hmax⟩ := Finset.exists_max_image S A.rank hs
    have hb' : A.coefficient b (n+1) z ≠ 0 := (Finset.mem_filter.mp hb).2
    have hp : 0 < A.coefficient b (n+1) z :=
      lt_of_le_of_ne ((A.positive (n+1) z).mp hz b) (Ne.symm hb')
    have hd := A.homogeneous b (n+1) z hb'
    have hrem := A.peel_remainder (n+1) z hz b hp
    have hfinal : y.row n false + K.d n z ∈ K.positive n := by
      change y.row n false + K.d n (y.row (n+1) false) ∈ _
      rw [y.boundary]
      convert y.positive n true using 1; abel
    have hpos := A.peel_positive n z (y.row n false) hz (y.positive n false) hfinal b hp
      (fun c hc => hmax c (by simp [S,hc]))
    obtain ⟨x,w,hxw,hx,hw,hxt,hwt,heq⟩ :=
      split_top y hy (A.basis (n+1) b) (z - A.basis (n+1) b)
        (A.basis_positive (n+1) b) hrem (by dsimp [z]; abel) hpos
    have hlt : (A.mass (n+1) (w.row (n+1) false)).toNat < m := by
      rw [hwt,map_sub,A.mass_basis (n+1) b hd,← hm]
      change (A.mass (n+1) z - 1).toNat < (A.mass (n+1) z).toNat
      rw [Int.toNat_lt_toNat (A.mass_pos (n+1) z hz b hp)]
      omega
    rw [← heq]
    exact .compose x w hxw (.basis x b hx hd hxt) (ih _ hlt w hw rfl)

lemma coefficient_cut (p : ℕ) (z : K.Chain p) (P : A.Index → Prop) (b : A.Index) :
    A.coefficient b p (A.cut p z P) = if P b then A.coefficient b p z else 0 := by
  classical
  rw [cut,map_sum]
  simp only [apply_ite,map_zsmul,map_zero,A.coefficient_basis]
  rw [Finset.sum_eq_single b]
  · by_cases hd : A.dim b = p
    · by_cases hp : P b <;> simp [hd,hp]
    · simp [hd,A.coefficient_eq_zero b p z hd]
  · intro c _ hc
    by_cases hP : P c <;> simp [hP,hc]
  · simp

lemma cut_positive (p : ℕ) (z : K.Chain p) (hz : z ∈ K.positive p) (P : A.Index → Prop) :
    A.cut p z P ∈ K.positive p := by
  apply (A.positive p _).mpr
  intro b
  rw [A.coefficient_cut]
  split_ifs
  · exact (A.positive p z).mp hz b
  · exact le_rfl

lemma cut_add_complement (p : ℕ) (z : K.Chain p) (P : A.Index → Prop) :
    A.cut p z P + A.cut p z (fun b => ¬P b) = z := by
  apply A.ext p
  intro b
  rw [map_add,A.coefficient_cut,A.coefficient_cut]
  by_cases h : P b <;> simp [h]

lemma coefficient_derivative (p : ℕ) (z : K.Chain (p+1)) (t : A.Index) :
    A.coefficient t p (K.d p z) =
      ∑ b, A.coefficient b (p+1) z * A.coefficient t p (K.d p (A.basis (p+1) b)) := by
  conv_lhs => rw [← A.expansion (p+1) z]
  rw [map_sum,map_sum]
  simp only [map_zsmul,smul_eq_mul]

lemma derivative_nonneg_of_before (p : ℕ) (z : K.Chain (p+1)) (hz : z ∈ K.positive (p+1))
    (r : ℤ) (hs : ∀ b, A.coefficient b (p+1) z ≠ 0 → r < A.rank b)
    (t : A.Index) (ht : A.rank t ≤ r) : 0 ≤ A.coefficient t p (K.d p z) := by
  classical
  rw [A.coefficient_derivative]
  apply Finset.sum_nonneg
  intro b _
  by_cases hb : A.coefficient b (p+1) z = 0
  · simp [hb]
  apply mul_nonneg ((A.positive (p+1) z).mp hz b)
  by_contra hn
  have hr := (A.derivative_rank p b t (A.homogeneous b (p+1) z hb)).2 (lt_of_not_ge hn)
  have hm := hs b hb
  omega

lemma derivative_nonpos_of_after (p : ℕ) (z : K.Chain (p+1)) (hz : z ∈ K.positive (p+1))
    (r : ℤ) (hs : ∀ b, A.coefficient b (p+1) z ≠ 0 → A.rank b ≤ r)
    (t : A.Index) (ht : r ≤ A.rank t) : A.coefficient t p (K.d p z) ≤ 0 := by
  classical
  rw [A.coefficient_derivative]
  apply Finset.sum_nonpos
  intro b _
  by_cases hb : A.coefficient b (p+1) z = 0
  · simp [hb]
  apply mul_nonpos_of_nonneg_of_nonpos ((A.positive (p+1) z).mp hz b)
  by_contra hn
  have hr := (A.derivative_rank p b t (A.homogeneous b (p+1) z hb)).1 (lt_of_not_ge hn)
  have hm := hs b hb
  omega

lemma cut_before_derivative (p : ℕ) (z : K.Chain (p+1)) (hz : z ∈ K.positive (p+1))
    (r : ℤ) (t : A.Index) (ht : A.rank t ≤ r) :
    0 ≤ A.coefficient t p (K.d p (A.cut (p+1) z (fun b => r < A.rank b))) := by
  apply A.derivative_nonneg_of_before p _ (A.cut_positive _ _ hz _) r _ t ht
  intro b hb
  rw [A.coefficient_cut] at hb
  by_contra hn
  exact hb (ite_eq_right hn)

lemma cut_after_derivative (p : ℕ) (z : K.Chain (p+1)) (hz : z ∈ K.positive (p+1))
    (r : ℤ) (t : A.Index) (ht : r ≤ A.rank t) :
    A.coefficient t p (K.d p (A.cut (p+1) z (fun b => ¬r < A.rank b))) ≤ 0 := by
  apply A.derivative_nonpos_of_after p _ (A.cut_positive _ _ hz _) r _ t ht
  intro b hb
  rw [A.coefficient_cut] at hb
  by_contra hn
  exact hb (ite_eq_right (not_not_intro (lt_of_not_ge hn)))

lemma rank_cut_positive (p : ℕ) (r : ℤ) (a b x y : K.Chain p) (z : K.Chain (p+1))
    (ha : a ∈ K.positive p) (hb : b ∈ K.positive p)
    (hx : x ∈ K.positive p) (hy : y ∈ K.positive p) (hz : z ∈ K.positive (p+1))
    (has : ∀ t, A.coefficient t p a ≠ 0 → r < A.rank t)
    (hbs : ∀ t, A.coefficient t p b ≠ 0 → A.rank t < r)
    (he : y - x = b - a + K.d p z) :
    x + K.d p (A.cut (p+1) z (fun t => r < A.rank t)) ∈ K.positive p ∧
    y - K.d p (A.cut (p+1) z (fun t => ¬r < A.rank t)) ∈ K.positive p := by
  have hh (t : A.Index) := congrArg (A.coefficient t p) he
  have dh : K.d p z = K.d p (A.cut (p+1) z (fun t => r < A.rank t)) +
      K.d p (A.cut (p+1) z (fun t => ¬r < A.rank t)) := by
    rw [← map_add,A.cut_add_complement]
  simp only [dh,map_sub,map_add] at hh
  constructor
  · apply (A.positive p _).mpr
    intro t
    rw [map_add]
    by_cases ht : A.rank t ≤ r
    · exact add_nonneg ((A.positive p x).mp hx t) (A.cut_before_derivative p z hz r t ht)
    · have hbt : A.coefficient t p b = 0 := by
        by_contra hn
        have := hbs t hn
        omega
      have hf := hh t
      rw [hbt] at hf
      have hf' := A.cut_after_derivative p z hz r t (by omega)
      have hp := (A.positive p y).mp hy t
      have hn := (A.positive p a).mp ha t
      omega
  · apply (A.positive p _).mpr
    intro t
    rw [map_sub]
    by_cases ht : r ≤ A.rank t
    · exact sub_nonneg.mpr (le_trans (A.cut_after_derivative p z hz r t ht) ((A.positive p y).mp hy t))
    · have hat : A.coefficient t p a = 0 := by
        by_contra hn
        have := has t hn
        omega
      have hf := hh t
      rw [hat] at hf
      have hf' := A.cut_before_derivative p z hz r t (by omega)
      have hp := (A.positive p x).mp hx t
      have hn := (A.positive p b).mp hb t
      omega

lemma common_atom_context (b : A.Index) (s : ℕ) (hs : s < A.dim b)
    (y : Table K) (hy : y.row (s+1) false = (A.atom b).row (s+1) false) :
    y.row s false - (A.atom b).row s false ∈ K.positive s ∧
      y.row s true - (A.atom b).row s true = y.row s false - (A.atom b).row s false := by
  have he : y.row s true - y.row s false = (A.atom b).row s true - (A.atom b).row s false := by
    rw [← y.boundary s false,hy,(A.atom b).boundary]
  constructor
  · apply (A.positive s _).mpr
    intro t
    rw [map_sub]
    by_cases ht : A.coefficient t s ((A.atom b).row s false) = 0
    · rw [ht,sub_zero]
      exact (A.positive s _).mp (y.positive s false) t
    have hf : A.coefficient t s ((A.atom b).row s true) = 0 := by
      by_contra hn
      have hs' := A.ranked b s hs false t ht
      have ht' := A.ranked b s hs true t hn
      simp only [Bool.false_eq_true,ite_false,ite_true] at hs' ht'
      omega
    have hh := congrArg (A.coefficient t s) he
    simp only [map_sub,hf] at hh
    have hp := (A.positive s _).mp (y.positive s true) t
    omega
  · apply A.ext s
    intro t
    have hh := congrArg (A.coefficient t s) he
    simp only [map_sub] at hh ⊢
    omega

lemma atom_context_pasting {n : ℕ} (b : A.Index) (hdim : A.dim b = n+1)
    (hsmall : ∀ x : Table K, truncate n false x = x → A.AtomPasting x)
    (k : ℕ) (hk : k ≤ n) (y : Table K)
    (hy : ∀ p, k < p → ∀ e, y.row p e = (A.atom b).row p e) : A.AtomPasting y := by
  induction k generalizing y with
  | zero =>
    obtain ⟨hz,hcommon⟩ := A.common_atom_context b 0 (by omega) y (hy 1 (by omega) false)
    have haug : K.augmentation (y.row 0 false - (A.atom b).row 0 false) = 0 := by
      rw [map_sub,y.augmentation,(A.atom b).augmentation,sub_self]
    have hz₀ := A.positive_augmentation_zero _ hz haug
    have he : y = A.atom b := by
      ext p e
      cases p with
      | zero =>
        cases e
        · exact sub_eq_zero.mp hz₀
        · exact sub_eq_zero.mp (hcommon.trans hz₀)
      | succ p => exact hy (p+1) (by omega) e
    rw [he]
    exact .atom b
  | succ k ih =>
    obtain ⟨hz,hcommon⟩ := A.common_atom_context b (k+1) (by omega) y (hy (k+2) (by omega) false)
    let z := y.row (k+1) false - (A.atom b).row (k+1) false
    let c := A.cut (k+1) z (fun t => A.rank b < A.rank t)
    let d := A.cut (k+1) z (fun t => ¬A.rank b < A.rank t)
    have hc : c ∈ K.positive (k+1) := A.cut_positive _ _ hz _
    have hd : d ∈ K.positive (k+1) := A.cut_positive _ _ hz _
    have hcd : c + d = z := A.cut_add_complement _ _ _
    have hrows (e : Bool) : y.row (k+1) e - c - d = (A.atom b).row (k+1) e := by
      have he : y.row (k+1) e - (A.atom b).row (k+1) e = z := by
        cases e
        · rfl
        · exact hcommon
      rw [sub_sub,hcd]
      exact sub_eq_iff_eq_add.mpr ((sub_eq_iff_eq_add.mp he).trans (add_comm _ _))
    have ht : ∀ e, y.row (k+1) e - c - d ∈ K.positive (k+1) := by
      intro e
      rw [hrows]
      exact (A.atom b).positive _ _
    have hdiff : y.row k true - y.row k false = (A.atom b).row k true -
        (A.atom b).row k false + K.d k z := by
      dsimp [z]
      rw [map_sub,y.boundary,(A.atom b).boundary]
      abel
    obtain ⟨hstart,hend⟩ := A.rank_cut_positive k (A.rank b) _ _ _ _ z
      ((A.atom b).positive k false) ((A.atom b).positive k true)
      (y.positive k false) (y.positive k true) hz
      (fun t ht => A.ranked b k (by omega) false t ht)
      (fun t ht => A.ranked b k (by omega) true t ht) hdiff
    let m := removeContext k y c d ht hstart hend
    have hm : A.AtomPasting m := by
      apply ih (by omega) m
      intro p hp e
      change removeContextRow k y c d p e = (A.atom b).row p e
      by_cases hpk : p = k+1
      · subst p; rw [removeContextRow_top,hrows]
      · rw [removeContextRow_other k y c d p e (by omega) hpk]
        exact hy p (by omega) e
    obtain ⟨l,r,hlm,hmr,hl,hr,he⟩ := factor_context k y c d hc hd ht hstart hend
    rw [← he]
    exact .compose k _ _ hmr
      (.compose k _ _ hlm (hsmall l (K.nu.source_fixed_upwards hk hl)) hm)
      (hsmall r (K.nu.source_fixed_upwards hk hr))

theorem atomic_pasting (n : ℕ) (y : Table K) (hy : truncate n false y = y) : A.AtomPasting y := by
  induction n generalizing y with
  | zero =>
    obtain ⟨b,hd,rfl⟩ := A.objects_atomic y hy
    exact .atom b
  | succ n ih =>
    have htop := A.top_pasting y hy
    clear hy
    induction htop with
    | identity x hx => exact ih x hx
    | basis x b hx hb ht =>
      have ha : truncate (n+1) false (A.atom b) = A.atom b := hb ▸ A.bounded b
      have ht' : x.row (n+1) false = (A.atom b).row (n+1) false := by
        rw [ht,← hb,A.basis_own]
      apply A.atom_context_pasting b hb ih n le_rfl x
      intro p hp e
      exact NormalizedChains.rows_above_top_agree x (A.atom b) hx ha ht' p (by omega) e
    | compose x y h hx hy ihx ihy => exact .compose n x y h ihx ihy

theorem all_atomic (y : Table K) : A.AtomPasting y := by
  obtain ⟨n,hn⟩ := K.nu.finite_dimension y
  exact A.atomic_pasting n y hn

end RankedAtoms
end Thomason.DirectedComplex

end

end OAI
end

section
-- module Solutions.OAIQ043_TH.Thomason_FiniteGluing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite Gluing. -/

noncomputable section
universe u v w z


namespace Thomason.DirectedComplex.RankedAtoms
open Table OmegaCategory CategoryTheory
variable {K : DirectedComplex.{u}} (A : RankedAtoms.{u,v} K)
include A

lemma positive_add_zero {p : ℕ} {x y : K.Chain p}
    (hx : x ∈ K.positive p) (hy : y ∈ K.positive p) (h : x+y=0) : x=0 ∧ y=0 := by
  have he (b : A.Index) : A.coefficient b p x = 0 ∧ A.coefficient b p y = 0 := by
    have hh := congrArg (A.coefficient b p) h
    rw [map_add,map_zero] at hh
    have hx' := (A.positive p x).mp hx b
    have hy' := (A.positive p y).mp hy b
    omega
  exact ⟨A.ext p x 0 (fun b => (he b).1.trans (map_zero _).symm),
    A.ext p y 0 (fun b => (he b).2.trans (map_zero _).symm)⟩

lemma comp_dimension_factors {k n : ℕ} (x y : Table K)
    (h : truncate k true x = truncate k false y)
    (hz : truncate n false (comp k x y h) = comp k x y h) :
    truncate n false x = x ∧ truncate n false y = y := by
  have habove (p : ℕ) (hp : max n k < p) (b : Bool) :
      x.row p b = 0 ∧ y.row p b = 0 := by
    have he := row_above_fixed (comp k x y h) hz (by omega : n < p) b
    rw [comp_row] at he
    simp only [show ¬p < k by omega, show p ≠ k by omega, ite_false] at he
    exact A.positive_add_zero (x.positive p b) (y.positive p b) he
  have hx := dimension_of_rows_above_zero x (fun p hp b => (habove p hp b).1)
  have hy := dimension_of_rows_above_zero y (fun p hp b => (habove p hp b).2)
  by_cases hkn : k ≤ n
  · simpa only [max_eq_left hkn] using And.intro hx hy
  · have hnk : n ≤ k := by omega
    rw [max_eq_right hnk] at hx hy
    have hz' : truncate k false (comp k x y h) = comp k x y h :=
      K.nu.source_fixed_upwards hnk hz
    have hz'' : truncate k true (comp k x y h) = comp k x y h :=
      K.nu.target_eq_self_of_source_eq_self hz'
    have hzx : comp k x y h = x := by rw [← hz', source_comp_le k k le_rfl, hx]
    have hzy : comp k x y h = y := by
      rw [← hz'', target_comp_le k k le_rfl]
      exact K.nu.target_eq_self_of_source_eq_self hy
    exact ⟨hzx ▸ hz, hzy ▸ hz⟩

lemma atom_dimension_le {n : ℕ} (b : A.Index)
    (h : truncate n false (A.atom b) = A.atom b) : A.dim b ≤ n := by
  by_contra hn
  have hz := row_above_fixed (A.atom b) h (by omega : n < A.dim b) false
  have ht := A.top b b false
  rw [hz,map_zero] at ht
  simp at ht

lemma bounded_pasting (n : ℕ) (x : Table K) (hx : truncate n false x = x) :
    A.BoundedPasting n x := by
  have hh := A.all_atomic x
  induction hh with
  | atom b => exact .atom b (A.atom_dimension_le b hx)
  | compose k x y h hx' hy' ihx ihy =>
    obtain ⟨hdx,hdy⟩ := A.comp_dimension_factors x y h hx
    by_cases hk : k < n
    · exact .compose k hk x y h (ihx hdx) (ihy hdy)
    · have he : comp k x y h = y := K.nu.comp_of_left_source_fixed k x y h
        (K.nu.source_fixed_upwards (by omega : n ≤ k) hdx)
      rw [he]
      exact ihy hdy

lemma surjective_onCells_of_lower_injective {C : OmegaCategory.{w}}
    (F : OmegaCategory.Functor C K.nu) (n : ℕ)
    (hlower : ∀ k, k < n → Function.Injective (F.onCells k))
    (hatom : ∀ b, A.dim b ≤ n → ∃ x : C.Cells n, F.map x.val = A.atom b) :
    Function.Surjective (F.onCells n) := by
  have hlift (t : Table K) (hp : A.BoundedPasting n t) :
      ∃ y : C.Cells n, F.map y.val = t := by
    induction hp with
    | atom b hb => exact hatom b hb
    | compose k hk x y hxy hpx hpy ihx ihy =>
      obtain ⟨a,ha⟩ := ihx
      obtain ⟨b,hb⟩ := ihy
      have hm : C.target k a.val = C.source k b.val := by
        exact congrArg Subtype.val
          (hlower k hk (a₁ := ⟨C.target k a.val,C.source_target_self k a.val⟩)
            (a₂ := ⟨C.source k b.val,C.source_source_self k b.val⟩)
            (Subtype.ext (by change F.map _ = F.map _; rw [F.map_target,F.map_source,ha,hb]; exact hxy)))
      refine ⟨C.gradedComp hk a b hm, ?_⟩
      change F.map (C.comp k a.val b.val hm) = _
      rw [F.map_comp k a.val b.val hm (F.map_composable hm)]
      change K.nu.comp k (F.map a.val) (F.map b.val) _ = K.nu.comp k x y hxy
      congr 1
  intro x
  obtain ⟨y,hy⟩ := hlift x.val (A.bounded_pasting n x.val x.property)
  exact ⟨y,Subtype.ext hy⟩

end Thomason.DirectedComplex.RankedAtoms

end

noncomputable section
universe u v w z


namespace Thomason.GrayRecursive.IntervalHom
open CategoryTheory DirectedComplex Table OmegaCategory NormalizedChains

variable {N : ℕ} {P : Type u} [LinearOrder P]

lemma chainComparison_atom_lift (e : Fin (N+1) ≃o P)
    (b : (Prism.Basis.ofOrderIso e).Index) :
    ∃ x : (tensorFunctor.obj (NormalizedChains.complex P).nu).Cells
      ((Prism.Basis.ofOrderIso e).dim b),
      (chainComparison (NormalizedChains.complex P)).map x.val = (Prism.Basis.ofOrderIso e).atom b := by
  let M := NormalizedChains.complex P
  let f := complexMap (e : Fin (N+1) →o P)
  change ∃ x : (tensorFunctor.obj M.nu).Cells (Prism.Basis.dim b),
    (chainComparison M).map x.val = f.cylinder.table (Prism.Basis.atom b)
  cases b with
  | endpoint a w =>
    let x := f.table w.atom
    have hx : M.nu.source w.dim x = x := by
      change truncate w.dim false (f.table w.atom) = f.table w.atom
      rw [← Hom.table_truncate,w.atom_dim]
    refine ⟨⟨((tensorEndpoint a).app M.nu).map x, ?_⟩, ?_⟩
    · change (tensorFunctor.obj M.nu).source w.dim _ = _
      erw [endpoint_source,hx]
    · rw [chainComparison_endpoint_apply]
      exact (congrArg (fun h : Hom (NormalizedChains.complex (Fin (N+1))) M.cylinder =>
        h.table w.atom) (f.cylinder_endpoint a)).symm
  | vertical w =>
    let x := f.table w.atom
    have hx : M.nu.source w.dim x = x := by
      change truncate w.dim false (f.table w.atom) = f.table w.atom
      rw [← Hom.table_truncate,w.atom_dim]
    refine ⟨⟨verticalCell w.dim ⟨x,hx⟩, verticalCell_bounded _ _⟩, ?_⟩
    erw [chainComparison_verticalCell w.dim ⟨x,hx⟩]
    exact (verticalTable_natural f w.atom).symm

end Thomason.GrayRecursive.IntervalHom

end

end OAI
end

section
-- module Solutions.OAIQ043_TH.Thomason_AtomFibers
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Atom Fibers. -/

noncomputable section
universe u v w z


namespace Thomason.OmegaCategory.Functor
open CategoryTheory

variable {C D : OmegaCategory.{u}} (F : C ⟶ D)

lemma onCells_injective_mono {n k : ℕ} (hkn : k ≤ n)
    (h : Function.Injective (F.onCells n)) : Function.Injective (F.onCells k) := by
  intro x y he
  have heq : F.map x.val = F.map y.val := congrArg Subtype.val he
  apply Subtype.ext
  exact congrArg (fun z : C.Cells n => z.val) (h
    (a₁ := ⟨x.val,C.source_fixed_upwards hkn x.property⟩)
    (a₂ := ⟨y.val,C.source_fixed_upwards hkn y.property⟩)
    (Subtype.ext heq))

lemma onCells_injective_of_map_injective (h : Function.Injective F.map) (n : ℕ) :
    Function.Injective (F.onCells n) := by
  intro x y he
  exact Subtype.ext (h (congrArg Subtype.val he))

lemma map_surjective_of_onCells_surjective
    (h : ∀ n, Function.Surjective (F.onCells n)) : Function.Surjective F.map := by
  intro y
  obtain ⟨n,hn⟩ := D.finite_dimension y
  obtain ⟨x,hx⟩ := h n ⟨y,hn⟩
  exact ⟨x.val,congrArg Subtype.val hx⟩

lemma map_injective_of_onCells_injective {n : ℕ} (hn : C.IsTruncated n)
    (h : Function.Injective (F.onCells n)) : Function.Injective F.map := by
  intro x y he
  exact congrArg Subtype.val
    (h (a₁ := ⟨x,hn x⟩) (a₂ := ⟨y,hn y⟩) (Subtype.ext he))

end Thomason.OmegaCategory.Functor

end

noncomputable section
universe u v w z


namespace Thomason.GrayRecursive.IntervalHom
open CategoryTheory DirectedComplex DirectedComplex.Table OmegaCategory NormalizedChains

lemma chainComparison_finiteSimplex_surjective_of_lower_injective
    (P : Type u) [LinearOrder P] [Finite P] (n : ℕ)
    (h : ∀ k, k < n → Function.Injective
      ((chainComparison (NormalizedChains.complex P)).onCells k)) :
    Function.Surjective ((chainComparison (NormalizedChains.complex P)).onCells n) := by
  let := Fintype.ofFinite P
  by_cases he : Fintype.card P = 0
  · let : IsEmpty P := Fintype.card_eq_zero_iff.mp he
    intro t
    exact isEmptyElim (PosetTables.tableStart
      ((NormalizedChains.complex P).cylinderProjection.table t.val))
  · have hp : Fintype.card P = (Fintype.card P - 1) + 1 := by omega
    let e := Fintype.orderIsoFinOfCardEq P hp
    apply (Prism.Basis.ofOrderIso e).surjective_onCells_of_lower_injective
      (chainComparison (NormalizedChains.complex P)) n h
    intro b hb
    obtain ⟨x,hx⟩ := chainComparison_atom_lift e b
    exact ⟨⟨x.val, (tensorFunctor.obj (NormalizedChains.complex P).nu).source_fixed_upwards hb x.property⟩,hx⟩

lemma chainComparison_finiteSimplex_isIso_of_injective
    (P : Type u) [LinearOrder P] [Finite P]
    (h : Function.Injective (chainComparison (NormalizedChains.complex P)).map) :
    IsIso (chainComparison (NormalizedChains.complex P)) := by
  exact (OmegaCategory.isoOfBijective (chainComparison (NormalizedChains.complex P))
    ⟨h,(chainComparison (NormalizedChains.complex P)).map_surjective_of_onCells_surjective
      (fun n => chainComparison_finiteSimplex_surjective_of_lower_injective P n
        (fun k _ => (chainComparison (NormalizedChains.complex P)).onCells_injective_of_map_injective h k))⟩).isIso_hom

end Thomason.GrayRecursive.IntervalHom

end

noncomputable section
universe u v w z


namespace Thomason.DirectedComplex.RankedAtoms
open Table
variable {K : DirectedComplex.{u}} (A : RankedAtoms.{u,v} K)
include A

lemma atom_face_coefficient_pos (b : A.Index) (p : ℕ) (hp : p < A.dim b) (e : Bool) :
    ∃ c : A.Index, 0 < A.coefficient c p ((A.atom b).row p e) := by
  induction p with
  | zero =>
    by_contra hn
    push Not at hn
    have he : (A.atom b).row 0 e = 0 := by
      apply A.ext 0
      intro c
      rw [map_zero]
      have hx := (A.positive 0 _).mp ((A.atom b).positive 0 e) c
      exact le_antisymm (hn c) hx
    have ha := (A.atom b).augmentation e
    rw [he,map_zero] at ha
    omega
  | succ p ih =>
    by_contra hn
    push Not at hn
    have he : (A.atom b).row (p+1) e = 0 := by
      apply A.ext (p+1)
      intro c
      rw [map_zero]
      exact le_antisymm (hn c)
        ((A.positive (p+1) _).mp ((A.atom b).positive (p+1) e) c)
    have hd := (A.atom b).boundary p e
    rw [he,map_zero] at hd
    have hh : (A.atom b).row p true = (A.atom b).row p false :=
      sub_eq_zero.mp hd.symm
    obtain ⟨c,hc⟩ := ih (by omega)
    have hs : A.coefficient c p ((A.atom b).row p false) ≠ 0 := by
      cases e
      · exact ne_of_gt hc
      · rw [← hh]; exact ne_of_gt hc
    have ht : A.coefficient c p ((A.atom b).row p true) ≠ 0 := by rw [hh]; exact hs
    have hr := A.ranked b p (by omega) false c hs
    have hr' := A.ranked b p (by omega) true c ht
    simp only [Bool.false_eq_true,ite_false,ite_true] at hr hr'
    omega

lemma basis_derivative_negative (p : ℕ) (b : A.Index) (hb : A.dim b = p+1) :
    ∃ c : A.Index, A.rank b < A.rank c ∧
      A.coefficient c p (K.d p (A.basis (p+1) b)) < 0 := by
  obtain ⟨c,hc⟩ := A.atom_face_coefficient_pos b p (by omega) false
  have hs : A.rank b < A.rank c := A.ranked b p (by omega) false c (ne_of_gt hc)
  have ht : A.coefficient c p ((A.atom b).row p true) = 0 := by
    by_contra hn
    have h := A.ranked b p (by omega) true c hn
    simp only [ite_true] at h
    omega
  refine ⟨c,hs,?_⟩
  have he : A.basis (p+1) b = (A.atom b).row (p+1) false := by rw [← hb,A.basis_own]
  rw [he,(A.atom b).boundary,map_sub,ht]
  omega

lemma maximal_transition_coefficient_le (p : ℕ) (z : K.Chain (p+1))
    (x : K.Chain p) (hz : z ∈ K.positive (p+1))
    (hy : x + K.d p z ∈ K.positive p) (b : A.Index)
    (hb : A.coefficient b (p+1) z ≠ 0)
    (hmax : ∀ c, A.coefficient c (p+1) z ≠ 0 → A.rank c ≤ A.rank b) :
    ∃ t : A.Index, A.coefficient b (p+1) z ≤ A.coefficient t p x := by
  classical
  obtain ⟨t,ht,hd⟩ := A.basis_derivative_negative p b (A.homogeneous b (p+1) z hb)
  have hnonpos (c : A.Index) :
      A.coefficient c (p+1) z * A.coefficient t p (K.d p (A.basis (p+1) c)) ≤ 0 := by
    by_cases hc : A.coefficient c (p+1) z = 0
    · simp [hc]
    apply mul_nonpos_of_nonneg_of_nonpos ((A.positive (p+1) z).mp hz c)
    by_contra hn
    have h := (A.derivative_rank p c t (A.homogeneous c (p+1) z hc)).1 (lt_of_not_ge hn)
    have hm := hmax c hc
    omega
  have hsum : A.coefficient t p (K.d p z) ≤
      A.coefficient b (p+1) z * A.coefficient t p (K.d p (A.basis (p+1) b)) := by
    rw [A.coefficient_derivative]
    calc
      _ ≤ ∑ c : A.Index, if c = b then A.coefficient b (p+1) z *
            A.coefficient t p (K.d p (A.basis (p+1) b)) else 0 := by
        apply Finset.sum_le_sum
        intro c _
        by_cases hc : c = b
        · subst c; simp only; exact le_rfl
        · rw [ite_eq_right hc]; exact hnonpos c
      _ = _ := by simp
  have hmul : A.coefficient b (p+1) z * A.coefficient t p (K.d p (A.basis (p+1) b)) ≤
      - A.coefficient b (p+1) z := by
    calc
      _ ≤ A.coefficient b (p+1) z * (-1) := mul_le_mul_of_nonneg_left (by omega)
        ((A.positive (p+1) z).mp hz b)
      _ = _ := mul_neg_one _
  have hh := (A.positive p _).mp hy t
  rw [map_add] at hh
  exact ⟨t,by omega⟩

lemma top_coefficient_le_one (n : ℕ) (y : Table K) (hy : truncate n false y = y)
    (b : A.Index) : A.coefficient b n (y.row n false) ≤ 1 := by
  classical
  induction n generalizing y b with
  | zero =>
    obtain ⟨c,hc,rfl⟩ := A.objects_atomic y hy
    have he := A.top c b false
    rw [hc] at he
    rw [he]
    split_ifs <;> omega
  | succ n ihn =>
    generalize hm : (A.mass (n+1) (y.row (n+1) false)).toNat = m
    induction m using Nat.strong_induction_on generalizing y b with
    | h m ihm =>
      let z := y.row (n+1) false
      have hz : z ∈ K.positive (n+1) := y.positive (n+1) false
      by_cases he : z = 0
      · change A.coefficient b (n+1) z ≤ 1
        rw [he,map_zero]
        omega
      let S := Finset.univ.filter (fun c => A.coefficient c (n+1) z ≠ 0)
      have hs : S.Nonempty := by
        by_contra hn
        apply he
        apply A.ext (n+1)
        intro c
        rw [map_zero]
        by_contra hc
        exact hn ⟨c,by simp [S,hc]⟩
      obtain ⟨c,hc,hmax⟩ := Finset.exists_max_image S A.rank hs
      have hc' : A.coefficient c (n+1) z ≠ 0 := (Finset.mem_filter.mp hc).2
      have hmax' : ∀ d, A.coefficient d (n+1) z ≠ 0 → A.rank d ≤ A.rank c :=
        fun d hd => hmax d (by simp [S,hd])
      have hp : 0 < A.coefficient c (n+1) z :=
        lt_of_le_of_ne ((A.positive (n+1) z).mp hz c) (Ne.symm hc')
      have hd := A.homogeneous c (n+1) z hc'
      have hfinal : y.row n false + K.d n z ∈ K.positive n := by
        change y.row n false + K.d n (y.row (n+1) false) ∈ _
        rw [y.boundary]
        convert y.positive n true using 1; abel
      by_cases hbc : b = c
      · subst b
        obtain ⟨t,ht⟩ := A.maximal_transition_coefficient_le n z (y.row n false) hz hfinal c hc' hmax'
        have hi := ihn (truncate n false y) (by simp only [truncate_truncate,lt_self_iff_false,ite_false]) t
        change A.coefficient t n ((truncate n false y).row n false) ≤ 1 at hi
        simp only [truncate_row, lt_self_iff_false, ite_false, ite_true] at hi
        exact ht.trans hi
      · have hrem := A.peel_remainder (n+1) z hz c hp
        have hpos := A.peel_positive n z (y.row n false) hz (y.positive n false) hfinal c hp hmax'
        obtain ⟨x,w,hxw,hx,hw,hxt,hwt,heq⟩ :=
          split_top y hy (A.basis (n+1) c) (z - A.basis (n+1) c)
            (A.basis_positive (n+1) c) hrem (by dsimp [z]; abel) hpos
        have hlt : (A.mass (n+1) (w.row (n+1) false)).toNat < m := by
          rw [hwt,map_sub,A.mass_basis (n+1) c hd,← hm]
          change (A.mass (n+1) z - 1).toNat < (A.mass (n+1) z).toNat
          rw [Int.toNat_lt_toNat (A.mass_pos (n+1) z hz c hp)]
          omega
        have hi := ihm _ hlt w hw b rfl
        rw [hwt,map_sub,A.coefficient_basis,ite_eq_left hd,ite_eq_right (Ne.symm hbc),sub_zero] at hi
        exact hi

end Thomason.DirectedComplex.RankedAtoms

end

noncomputable section
universe u v w z


namespace Thomason.DirectedComplex.RankedAtoms
open Table
variable {K : DirectedComplex.{u}} (A : RankedAtoms.{u,v} K)
include A

lemma positive_split_basis (p : ℕ) (b : A.Index) (hb : A.dim b = p)
    (x y : K.Chain p) (hx : x ∈ K.positive p) (hy : y ∈ K.positive p)
    (he : x+y = A.basis p b) : x = 0 ∨ y = 0 := by
  have h (c : A.Index) := congrArg (A.coefficient c p) he
  simp only [map_add,A.coefficient_basis,ite_eq_left hb] at h
  have hbx := (A.positive p x).mp hx b
  have hby := (A.positive p y).mp hy b
  have hsum : A.coefficient b p x + A.coefficient b p y = 1 := by simpa using h b
  have heq (c : A.Index) (hc : c ≠ b) : A.coefficient c p x = 0 ∧ A.coefficient c p y = 0 := by
    have hh := h c
    rw [ite_eq_right (Ne.symm hc)] at hh
    have hhx := (A.positive p x).mp hx c
    have hhy := (A.positive p y).mp hy c
    omega
  have hh : A.coefficient b p x = 0 ∨ A.coefficient b p y = 0 := by omega
  rcases hh with hx0 | hy0
  · left
    apply A.ext p
    intro c
    rw [map_zero]
    by_cases hc : c = b
    · simpa only [hc] using hx0
    · exact (heq c hc).1
  · right
    apply A.ext p
    intro c
    rw [map_zero]
    by_cases hc : c = b
    · simpa only [hc] using hy0
    · exact (heq c hc).2

lemma atom_subrows_fixed (b : A.Index) (k n : ℕ) (hn : n ≤ A.dim b)
    (x : Table K) (hx : truncate n false x = x)
    (hsub : ∀ p, k < p → ∀ e c,
      A.coefficient c p (x.row p e) ≤ A.coefficient c p ((A.atom b).row p e))
    (htop : x.row (A.dim b) false = 0) : truncate k false x = x := by
  induction n generalizing x with
  | zero => exact K.nu.source_fixed_upwards (Nat.zero_le k) hx
  | succ n ih =>
    by_cases hk : n+1 ≤ k
    · exact K.nu.source_fixed_upwards hk hx
    have hkn : k < n+1 := by omega
    have he : x.row (n+1) false = 0 := by
      by_cases he : n+1 = A.dim b
      · exact (congrArg (fun p => x.row p false = 0) he).mpr htop
      apply A.ext (n+1)
      intro c
      rw [map_zero]
      have hc := (A.positive (n+1) _).mp (x.positive (n+1) false) c
      by_contra hne
      have hpos : 0 < A.coefficient c (n+1) (x.row (n+1) false) := by omega
      have hs := hsub (n+1) hkn false c
      have ht := hsub (n+1) hkn true c
      rw [← row_top_fixed x hx] at ht
      have hrs := A.ranked b (n+1) (by omega) false c (ne_of_gt (hpos.trans_le hs))
      have hrt := A.ranked b (n+1) (by omega) true c (ne_of_gt (hpos.trans_le ht))
      simp only [Bool.false_eq_true,ite_false,ite_true] at hrs hrt
      omega
    exact ih (by omega) x (fixed_of_top_zero hx he) hsub htop

lemma atom_indecomposable (b : A.Index) (k : ℕ) (x y : Table K)
    (h : truncate k true x = truncate k false y)
    (he : comp k x y h = A.atom b) :
    truncate k false x = x ∨ truncate k false y = y := by
  have hz : truncate (A.dim b) false (comp k x y h) = comp k x y h := by
    rw [he]; exact A.bounded b
  obtain ⟨hx,hy⟩ := A.comp_dimension_factors x y h hz
  by_cases hk : A.dim b ≤ k
  · exact Or.inl (K.nu.source_fixed_upwards hk hx)
  have hkd : k < A.dim b := by omega
  have hrows (p : ℕ) (hp : k < p) (e : Bool) :
      x.row p e + y.row p e = (A.atom b).row p e := by
    have hh := congrArg (fun z : Table K => z.row p e) he
    rw [comp_row] at hh
    simpa only [show ¬p < k by omega,show p ≠ k by omega,ite_false] using hh
  have hsub (p : ℕ) (hp : k < p) (e : Bool) (c : A.Index) :
      A.coefficient c p (x.row p e) ≤ A.coefficient c p ((A.atom b).row p e) ∧
      A.coefficient c p (y.row p e) ≤ A.coefficient c p ((A.atom b).row p e) := by
    have hh := congrArg (A.coefficient c p) (hrows p hp e)
    rw [map_add] at hh
    have hhx := (A.positive p _).mp (x.positive p e) c
    have hhy := (A.positive p _).mp (y.positive p e) c
    omega
  have ht : x.row (A.dim b) false + y.row (A.dim b) false = A.basis (A.dim b) b := by
    rw [A.basis_own]; exact hrows (A.dim b) hkd false
  rcases A.positive_split_basis (A.dim b) b rfl _ _ (x.positive _ _) (y.positive _ _) ht with hxt | hyt
  · exact Or.inl (A.atom_subrows_fixed b k (A.dim b) le_rfl x hx
      (fun p hp e c => (hsub p hp e c).1) hxt)
  · exact Or.inr (A.atom_subrows_fixed b k (A.dim b) le_rfl y hy
      (fun p hp e c => (hsub p hp e c).2) hyt)
end Thomason.DirectedComplex.RankedAtoms

end

noncomputable section
universe u v w z


namespace Thomason.GrayRecursive.IntervalHom
open CategoryTheory DirectedComplex DirectedComplex.Table GlobeComplex OmegaCategory
variable {M : DirectedComplex.{u}} (A : RankedAtoms.{u,v} M.cylinder)
include A

lemma chainComparison_lowers_dimension (n : ℕ)
    (z : (tensorFunctor.obj M.nu).Cell)
    (hz : (tensorFunctor.obj M.nu).source (n+1) z = z)
    (hzero : ((chainComparison M).map z).row (n+1) false = 0) :
    (tensorFunctor.obj M.nu).source n z = z := by
  let T := tensorFunctor.obj M.nu
  let F := chainComparison M
  have img_bound (z : T.Cell) (hz : T.source (n+1) z = z) :
      truncate (n+1) false (F.map z) = F.map z := by
    change M.cylinder.nu.source (n+1) (F.map z) = F.map z
    rw [← F.map_source,hz]
  apply tensor_bounded_cells_induction (n+1)
    (fun z => (F.map z).row (n+1) false = 0 → T.source n z = z) ?_ ?_ ?_ ?_ z hz hzero
  · intro a x hx he
    apply (chainComparison_endpoint_fiber (T.source n (((tensorEndpoint a).app M.nu).map x)) a x).mp
    rw [F.map_source]
    have hb : T.source (n+1) (((tensorEndpoint a).app M.nu).map x) =
        ((tensorEndpoint a).app M.nu).map x := by
      rw [← ((tensorEndpoint a).app M.nu).map_source]
      exact congrArg ((tensorEndpoint a).app M.nu).map hx
    exact (fixed_of_top_zero (img_bound _ hb) he).trans (chainComparison_endpoint_apply a x)
  · intro r hr x he
    by_cases hrn : r < n
    · exact T.source_fixed_upwards (by omega : r+1 ≤ n) (verticalCell_bounded r x)
    have hrn : r = n := by omega
    subst r
    have he' : x.val.row n false = 0 := by
      change ((chainComparison M).map (verticalCell n x)).row (n+1) false = 0 at he
      rw [chainComparison_verticalCell] at he
      have hh := congrArg (fun t : M.cylinder.Chain (n+1) => t.2.2) he
      change (verticalRow x.val (n+1) false).2.2 = 0 at hh
      simp only [verticalRow] at hh
      split_ifs at hh <;> exact hh
    cases n with
    | zero =>
      have ha := x.val.augmentation false
      rw [he',map_zero] at ha
      exact False.elim (by omega)
    | succ n =>
      exact verticalCell_bounded_of_bounded (n+1) n x (fixed_of_top_zero x.property he')
  · intro r hr y hy _
    exact T.source_fixed_upwards (by omega) hy
  · intro r hr x y hx hy h ihx ihy he
    change (F.map (T.comp r x y h)).row (n+1) false = 0 at he
    rw [F.map_comp r x y h (F.map_composable h)] at he
    change (DirectedComplex.Table.comp r (F.map x) (F.map y) (F.map_composable h)).row (n+1) false = 0 at he
    erw [comp_row] at he
    simp only [show ¬n+1 < r by omega,show n+1 ≠ r by omega,ite_false] at he
    obtain ⟨hxt,hyt⟩ := A.positive_add_zero ((F.map x).positive (n+1) false)
      ((F.map y).positive (n+1) false) he
    have hx' := ihx hxt
    have hy' := ihy hyt
    by_cases hrn : r < n
    · rw [T.source_comp_gt n r hrn x y h (T.source_composable hrn h)]
      exact T.comp_congr_cells r _ _ hx' hy'
    · have hnr : n = r := by omega
      subst r
      rw [T.comp_of_left_source_fixed n x y h hx']
      exact hy'

lemma chainComparison_reflects_dimension (n : ℕ)
    (z : (tensorFunctor.obj M.nu).Cell)
    (hz : truncate n false ((chainComparison M).map z) = (chainComparison M).map z) :
    (tensorFunctor.obj M.nu).source n z = z := by
  obtain ⟨d,hd⟩ := (tensorFunctor.obj M.nu).finite_dimension z
  induction d generalizing z with
  | zero => exact (tensorFunctor.obj M.nu).source_fixed_upwards (Nat.zero_le n) hd
  | succ d ih =>
    by_cases hdn : d+1 ≤ n
    · exact (tensorFunctor.obj M.nu).source_fixed_upwards hdn hd
    have hzero := row_above_fixed ((chainComparison M).map z) hz (by omega : n < d+1) false
    exact ih z hz (chainComparison_lowers_dimension A d z hd hzero)
end Thomason.GrayRecursive.IntervalHom

end

noncomputable section
universe u v w z


namespace Thomason.DirectedComplex.CylinderTables
open Table
variable {M : DirectedComplex.{u}}

lemma cross_vertical (x : Table M) (p : ℕ) (e : Bool) :
    cross (verticalTable x) p e = x.row p e := by
  change (verticalRow x (p+1) e).2.2 = x.row p e
  simp only [verticalRow]
  split_ifs <;> rfl

lemma vertical_injective : Function.Injective (verticalTable (K := M)) := by
  intro x y h
  apply Table.ext
  funext p e
  exact (cross_vertical x p e).symm.trans
    ((congrArg (fun z => cross z p e) h).trans (cross_vertical y p e))

lemma label_vertical (x : Table M) (e : Bool) :
    label (verticalTable x) e = if e then 1 else 0 := by
  cases e
  · exact M.augmentation.map_zero
  · exact x.augmentation true

lemma vertical_ne_endpoint (x y : Table M) (a : Bool) :
    verticalTable x ≠ (M.cylinderEndpoint a).table y := by
  intro h
  have hs := congrArg (fun z => label z false) h
  have ht := congrArg (fun z => label z true) h
  rw [label_vertical,label_endpoint] at hs ht
  cases a <;> simp_all

end Thomason.DirectedComplex.CylinderTables

end

noncomputable section
universe u v w z


namespace Thomason.GrayRecursive.IntervalHom
open CategoryTheory DirectedComplex DirectedComplex.Table GlobeComplex OmegaCategory
variable {M : DirectedComplex.{u}} (A : RankedAtoms.{u,v} M.cylinder)
include A

lemma chainComparison_atom_generator (b : A.Index)
    (z : (tensorFunctor.obj M.nu).Cell)
    (hz : (chainComparison M).map z = A.atom b) :
    (∃ (a : Bool) (x : M.nu.Cells (A.dim b)), z = ((tensorEndpoint a).app M.nu).map x.val) ∨
    (∃ r, r+1 = A.dim b ∧ ∃ x : M.nu.Cells r, z = verticalCell r x) := by
  let T := tensorFunctor.obj M.nu
  let F := chainComparison M
  have hb : T.source (A.dim b) z = z :=
    chainComparison_reflects_dimension A (A.dim b) z (hz ▸ A.bounded b)
  apply tensor_bounded_cells_induction (A.dim b)
    (fun z => F.map z = A.atom b →
      (∃ (a : Bool) (x : M.nu.Cells (A.dim b)), z = ((tensorEndpoint a).app M.nu).map x.val) ∨
      (∃ r, r+1 = A.dim b ∧ ∃ x : M.nu.Cells r, z = verticalCell r x)) ?_ ?_ ?_ ?_ z hb hz
  · intro a x hx _
    exact Or.inl ⟨a,⟨x,hx⟩,rfl⟩
  · intro r hr x he
    have hd : A.dim b ≤ r+1 := by
      apply A.atom_dimension_le b
      rw [← he]
      change M.cylinder.nu.source (r+1) (F.map (verticalCell r x)) = _
      rw [← F.map_source]
      exact congrArg F.map (verticalCell_bounded r x)
    exact Or.inr ⟨r,by omega,x,rfl⟩
  · intro r hr x hx he
    have hd : A.dim b ≤ r := by
      apply A.atom_dimension_le b
      rw [← he]
      change M.cylinder.nu.source r (F.map x) = _
      rw [← F.map_source]
      exact congrArg F.map hx
    omega
  · intro r hr x y hx hy h ihx ihy he
    have him : DirectedComplex.Table.comp r (F.map x) (F.map y) (F.map_composable h) = A.atom b :=
      (F.map_comp r x y h (F.map_composable h)).symm.trans he
    rcases A.atom_indecomposable b r (F.map x) (F.map y) (F.map_composable h) him with hf | hf
    · have hx' := chainComparison_reflects_dimension A r x hf
      have hc := T.comp_of_left_source_fixed r x y h hx'
      rw [hc] at he ⊢
      exact ihy he
    · have hy' := chainComparison_reflects_dimension A r y hf
      have hc := T.comp_of_right_source_fixed r x y h hy'
      rw [hc] at he ⊢
      exact ihx he

lemma chainComparison_atom_fiber_subsingleton (b : A.Index)
    (x y : (tensorFunctor.obj M.nu).Cell)
    (hx : (chainComparison M).map x = A.atom b)
    (hy : (chainComparison M).map y = A.atom b) : x = y := by
  rcases chainComparison_atom_generator A b x hx with ⟨a,t,rfl⟩ | ⟨r,_,t,rfl⟩
  · exact ((chainComparison_endpoint_fiber y a t.val).mp
      (hy.trans (hx.symm.trans (chainComparison_endpoint_apply a t.val)))).symm
  · rw [chainComparison_verticalCell] at hx
    rcases chainComparison_atom_generator A b y hy with ⟨a,s,rfl⟩ | ⟨q,_,s,rfl⟩
    · erw [chainComparison_endpoint_apply a s.val] at hy
      exact False.elim (CylinderTables.vertical_ne_endpoint t.val s.val a (hx.trans hy.symm))
    · rw [chainComparison_verticalCell] at hy
      exact verticalCell_eq_of_value t s (CylinderTables.vertical_injective (hx.trans hy.symm))

end Thomason.GrayRecursive.IntervalHom

end

end OAI
end

section
-- module Solutions.OAIQ043_TH.Thomason_TopSequences
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Top Sequences. -/

noncomputable section
universe u v w z


namespace Thomason.GrayRecursive.IntervalHom
open CategoryTheory DirectedComplex DirectedComplex.Table GlobeComplex OmegaCategory
variable {X Y : OmegaCategory.{u}}

lemma ofMap_in_image_iff (S : Subcategory Y) {n : ℕ}
    (F : (K.{u} n).nu ⟶ Y) :
    ofMap F ∈ (OmegaCategory.Functor.injectiveImage (mapFunctor S.inclusion)
      (mapCell_injective S.inclusion S.inclusion_injective)).carrier ↔
    ∀ t, F.map t ∈ S.carrier := by
  constructor
  · rintro ⟨x,hx⟩ t
    have h := congrArg (fun c => (eval n c).map t) hx
    rw [eval_ofMap_self] at h
    exact h ▸ ((eval n x).map t).property
  · intro h
    refine ⟨ofMap (S.lift F h),?_⟩
    change mapCell S.inclusion (ofMap (S.lift F h)) = ofMap F
    rw [mapCell_ofMap,S.lift_inclusion]

lemma mem_cylinderSubcategory_iff (S : Subcategory (tensorFunctor.obj X))
    (n : ℕ) (x : X.Cells n) :
    x.val ∈ (cylinderSubcategory S).carrier ↔ ∀ t, (generatorCylinder n x).map t ∈ S.carrier := by
  change tensorUnitCell x.val ∈ (OmegaCategory.Functor.injectiveImage (mapFunctor S.inclusion)
    (mapCell_injective S.inclusion S.inclusion_injective)).carrier ↔ _
  erw [tensorUnitCell_of_bounded n x,ofMap_in_image_iff]
  rfl

end Thomason.GrayRecursive.IntervalHom

end

noncomputable section
universe u v w z


namespace Thomason.GrayRecursive.IntervalHom
open CategoryTheory DirectedComplex Table OmegaCategory NormalizedChains

lemma chainComparison_endpoint_basis {N : ℕ} {P : Type u} [LinearOrder P]
    (e : Fin (N+1) ≃o P) (a : Bool) (b : (Prism.Word.ofOrderIso e).Index) :
    (chainComparison (NormalizedChains.complex P)).map
      (((tensorEndpoint a).app (NormalizedChains.complex P).nu).map
        ((Prism.Word.ofOrderIso e).atom b)) =
      (Prism.Basis.ofOrderIso e).atom (.endpoint a b) := by
  rw [chainComparison_endpoint_apply]
  exact (congrArg (fun h : Hom (NormalizedChains.complex (Fin (N+1)))
      (NormalizedChains.complex P).cylinder => h.table b.atom)
    ((complexMap (e : Fin (N+1) →o P)).cylinder_endpoint a)).symm

lemma chainComparison_vertical_basis {N : ℕ} {P : Type u} [LinearOrder P]
    (e : Fin (N+1) ≃o P) (b : (Prism.Word.ofOrderIso e).Index) :
    (chainComparison (NormalizedChains.complex P)).map
      (verticalCell ((Prism.Word.ofOrderIso e).dim b)
        ⟨(Prism.Word.ofOrderIso e).atom b,(Prism.Word.ofOrderIso e).bounded b⟩) =
      (Prism.Basis.ofOrderIso e).atom (.vertical b) := by
  erw [chainComparison_verticalCell ((Prism.Word.ofOrderIso e).dim b)
    ⟨(Prism.Word.ofOrderIso e).atom b,(Prism.Word.ofOrderIso e).bounded b⟩]
  exact (verticalTable_natural (complexMap (e : Fin (N+1) →o P)) b.atom).symm

end Thomason.GrayRecursive.IntervalHom

end

noncomputable section
universe u v w z


namespace Thomason.GrayRecursive.IntervalHom
open CategoryTheory DirectedComplex Table OmegaCategory GlobeComplex
variable {M : DirectedComplex.{u}} (A : RankedAtoms.{u,v} M)

namespace AtomicLayers
variable {A} {n : ℕ}

lemma endpoint_cell (a : Bool) (x : M.nu.Cell) (hx : M.nu.source n x = x) :
    AtomicLayers A n (((tensorEndpoint a).app M.nu).map x) := by
  have h := A.bounded_pasting n x hx
  clear hx
  induction h with
  | atom b hb => exact .endpoint a b hb
  | compose k hk x y h hpx hpy ihx ihy =>
    change AtomicLayers A n (((tensorEndpoint a).app M.nu).map (M.nu.comp k x y h))
    erw [((tensorEndpoint a).app M.nu).map_comp k x y h
      (((tensorEndpoint a).app M.nu).map_composable h)]
    exact .compose k hk _ _ _ ihx ihy

lemma cylinder_atom (b : A.Index) (hb : A.dim b < n) :
    A.atom b ∈ (cylinderSubcategory (subcategory A n)).carrier := by
  apply (mem_cylinderSubcategory_iff (subcategory A n) (A.dim b)
    ⟨A.atom b,A.bounded b⟩).mpr
  intro t
  apply GrayRecursive.generated (A.dim b)
    (fun z => (generatorCylinder (X := M.nu) (A.dim b)
      ⟨A.atom b,A.bounded b⟩).map z ∈ (subcategory A n).carrier)
  · intro a s
    erw [generatorCylinder_endpoint]
    apply endpoint_cell
    obtain ⟨p,e,hp,rfl⟩ := table_classification s
    erw [← (GlobeComplex.lift (C := M.nu) (A.atom b) (A.bounded b)).map_source]
    apply congrArg (GlobeComplex.lift (C := M.nu) (A.atom b) (A.bounded b)).map
    change truncate n false (truncate p e (topTable (A.dim b))) = _
    rw [truncate_truncate,ite_eq_right (by omega : ¬ n < p)]
  · intro s
    obtain ⟨p,e,hp,rfl⟩ := table_classification s
    erw [generatorCylinder_vertical_face]
    by_cases he : p = A.dim b
    · subst p
      have hf : M.nu.face (A.dim b) e (A.atom b) = A.atom b :=
        M.nu.face_of_fixed (A.bounded b) le_rfl e
      erw [verticalCell_eq_of_value _ (⟨A.atom b,A.bounded b⟩ : M.nu.Cells (A.dim b)) hf]
      exact AtomicLayers.vertical b hb
    · exact AtomicLayers.lower (p+1) (by omega) _ (verticalCell_bounded _ _)
  · intro k s t h hs ht
    erw [(generatorCylinder (X := M.nu) (A.dim b) ⟨A.atom b,A.bounded b⟩).map_comp k s t h
      ((generatorCylinder (X := M.nu) (A.dim b) ⟨A.atom b,A.bounded b⟩).map_composable h)]
    exact (subcategory A n).comp_mem k _ hs ht

lemma vertical_cell (r : ℕ) (hr : r < n) (x : M.nu.Cells r) :
    AtomicLayers A n (verticalCell r x) := by
  have hh (y : M.nu.Cell) (hp : A.BoundedPasting r y) :
      y ∈ (cylinderSubcategory (subcategory A n)).carrier := by
    induction hp with
    | atom b hb => exact cylinder_atom b (by omega)
    | compose k hk a b h hpa hpb iha ihb =>
      exact (cylinderSubcategory (subcategory A n)).comp_mem k h iha ihb
  exact (mem_cylinderSubcategory_iff (subcategory A n) r x).mp
    (hh x.val (A.bounded_pasting r x.val x.property))
    (verticalTable (topTable r))

end AtomicLayers

theorem tensor_atomic_layers (n : ℕ) (z : (tensorFunctor.obj M.nu).Cell)
    (hz : (tensorFunctor.obj M.nu).source n z = z) : AtomicLayers A n z := by
  apply tensor_bounded_cells_induction n (AtomicLayers A n)
    (fun a x hx => AtomicLayers.endpoint_cell a x hx)
    (fun r hr x => AtomicLayers.vertical_cell r hr x)
    (fun r hr x hx => .lower r hr x hx)
    (fun r hr x y _ _ h hx hy => .compose r hr x y h hx hy) z hz
end Thomason.GrayRecursive.IntervalHom

end

noncomputable section
universe u v w z


namespace Thomason.OmegaCategory

variable (C : OmegaCategory.{u}) (n : ℕ) (G : C.Cell → Prop)

variable {C n G}
namespace Whisker

lemma bounded {x : C.Cell} (h : C.Whisker n G x) : C.source (n+1) x = x := by
  induction h with
  | generator x hg hx => exact hx
  | left k hk a x ha h hx ih =>
    rw [C.join_source_gt (n+1) k a x (by omega) h,
      C.source_fixed_upwards (Nat.le_succ n) ha,ih]
  | right k hk x a ha h hx ih =>
    rw [C.join_source_gt (n+1) k x a (by omega) h,
      ih,C.source_fixed_upwards (Nat.le_succ n) ha]

end Whisker
namespace TopSequence

lemma whisker_left {x : C.Cell} (hx : C.TopSequence n G x)
    (k : ℕ) (hk : k < n) (a : C.Cell) (ha : C.source n a = a)
    (h : C.target k a = C.source k x) : C.TopSequence n G (C.join k a x) := by
  induction hx with
  | lower x hx =>
    apply TopSequence.lower
    rw [C.join_source_gt n k a x hk h,ha,hx]
  | single x hx => exact .single _ (.left k hk a x ha h hx)
  | compose x y hxy hx hy ihx ihy =>
    have hax : C.target k a = C.source k x := by
      rw [C.join_source_le k n x y hk.le hxy] at h
      exact h
    have hay : C.target k a = C.source k y := by
      have he := congrArg (C.source k) hxy
      simp only [C.source_target,ite_eq_left hk,C.source_source,min_eq_left hk.le] at he
      exact hax.trans he
    rw [C.join_whisker_left k n hk a x y ha hxy hax hay]
    refine .compose _ _ ?_ (ihx hax) (ihy hay)
    rw [C.join_target_gt n k a x hk hax,C.join_source_gt n k a y hk hay]
    rw [ha,C.target_eq_self_of_source_eq_self ha,hxy]

lemma whisker_right {x : C.Cell} (hx : C.TopSequence n G x)
    (k : ℕ) (hk : k < n) (a : C.Cell) (ha : C.source n a = a)
    (h : C.target k x = C.source k a) : C.TopSequence n G (C.join k x a) := by
  induction hx with
  | lower x hx =>
    apply TopSequence.lower
    rw [C.join_source_gt n k x a hk h,hx,ha]
  | single x hx => exact .single _ (.right k hk x a ha h hx)
  | compose x y hxy hx hy ihx ihy =>
    have hya : C.target k y = C.source k a := by
      rw [C.join_target_le k n x y hk.le hxy] at h
      exact h
    have hxa : C.target k x = C.source k a := by
      have he := congrArg (C.target k) hxy
      simp only [C.target_target,min_eq_left hk.le,C.target_source,ite_eq_left hk] at he
      exact he.trans hya
    rw [C.join_whisker_right k n hk x y a ha hxy hxa hya]
    refine .compose _ _ ?_ (ihx hxa) (ihy hya)
    rw [C.join_target_gt n k x a hk hxa,C.join_source_gt n k y a hk hya]
    rw [ha,C.target_eq_self_of_source_eq_self ha,hxy]

lemma join {x y : C.Cell} (hx : C.TopSequence n G x) (hy : C.TopSequence n G y)
    (k : ℕ) (hk : k ≤ n) (h : C.target k x = C.source k y) :
    C.TopSequence n G (C.join k x y) := by
  by_cases hn : k = n
  · subst k
    exact .compose x y h hx hy
  have hkn : k < n := by omega
  have hxs : C.target k x = C.source k (C.source n y) := by
    rw [C.source_source,min_eq_left hk]
    exact h
  have hty : C.target k (C.target n x) = C.source k y := by
    rw [C.target_target,min_eq_left hk]
    exact h
  rw [C.join_factor_right k n hkn x y h]
  refine .compose _ _ ?_
    (hx.whisker_right k hkn _ (C.source_source_self n y) hxs)
    (hy.whisker_left k hkn _ (C.source_target_self n x) hty)
  rw [C.join_target_gt n k x (C.source n y) hkn hxs,
    C.join_source_gt n k (C.target n x) y hkn hty,
    C.source_target_self n x,C.target_source_self n y]

lemma comp {x y : C.Cell} (hx : C.TopSequence n G x) (hy : C.TopSequence n G y)
    (k : ℕ) (hk : k ≤ n) (h : C.target k x = C.source k y) :
    C.TopSequence n G (C.comp k x y h) := by
  rw [← C.join_eq k x y h]
  exact hx.join hy k hk h

end TopSequence
end Thomason.OmegaCategory

end

noncomputable section
universe u v w z


namespace Thomason.DirectedComplex.RankedAtoms
open Table OmegaCategory

variable {K : DirectedComplex.{u}} (A : RankedAtoms.{u,v} K)
variable {C : OmegaCategory.{w}} (F : OmegaCategory.Functor C K.nu)

lemma top_row_join (n k : ℕ) (hk : k < n) (x y : C.Cell)
    (h : C.target k x = C.source k y) :
    (F.map (C.join k x y)).row n false =
      (F.map x).row n false + (F.map y).row n false := by
  rw [F.map_join k x y h,K.nu.join_eq k (F.map x) (F.map y) (F.map_composable h)]
  change (Table.comp k (F.map x) (F.map y) (F.map_composable h)).row n false = _
  erw [comp_row]
  simp only [show ¬ n < k by omega,show n ≠ k by omega,ite_false]

lemma top_row_lower (n : ℕ) (x : C.Cell) (hx : C.source n x = x) :
    (F.map x).row (n+1) false = 0 := by
  have h : truncate n false (F.map x) = F.map x :=
    (F.map_source n x).symm.trans (congrArg F.map hx)
  exact row_above_fixed (F.map x) h (Nat.lt_succ_self n) false

lemma whisker_top_basis {n : ℕ} {x : C.Cell} (h : C.Whisker n (A.TopGenerator F n) x) :
    ∃ b : A.Index, A.dim b = n+1 ∧ (F.map x).row (n+1) false = A.basis (n+1) b := by
  induction h with
  | generator x hg hx =>
    obtain ⟨b,hb,he⟩ := hg
    refine ⟨b,hb,?_⟩
    rw [he,← hb,A.basis_own]
  | left k hk a x ha h hx ih =>
    obtain ⟨b,hb,he⟩ := ih
    refine ⟨b,hb,?_⟩
    rw [top_row_join F (n+1) k (by omega) a x h,top_row_lower F n a ha,zero_add,he]
  | right k hk x a ha h hx ih =>
    obtain ⟨b,hb,he⟩ := ih
    refine ⟨b,hb,?_⟩
    rw [top_row_join F (n+1) k (by omega) x a h,top_row_lower F n a ha,add_zero,he]

lemma top_and_source_ext (n : ℕ) (x y : Table K)
    (hx : truncate (n+1) false x = x) (hy : truncate (n+1) false y = y)
    (ht : x.row (n+1) false = y.row (n+1) false)
    (hs : truncate n false x = truncate n false y) : x = y := by
  ext p e
  by_cases hp : n < p
  · exact NormalizedChains.rows_above_top_agree x y hx hy ht p (by omega) e
  · have hpn : p ≤ n := by omega
    by_cases he : p = n ∧ e = true
    · obtain ⟨he,rfl⟩ := he
      subst p
      have hleft := congrArg (fun z : Table K => z.row n false) hs
      simp only [truncate_row,lt_self_iff_false,ite_false,ite_true] at hleft
      have hd := congrArg (K.d n) ht
      rw [x.boundary,y.boundary,hleft] at hd
      exact (sub_left_inj).mp hd
    · have h := congrArg (fun z : Table K => z.row p e) hs
      by_cases hpn' : p < n
      · simpa only [truncate_row,ite_eq_left hpn'] using h
      · have hp : p = n := by omega
        subst p
        have he' : e = false := by cases e <;> simp_all
        subst e
        simpa only [truncate_row,lt_self_iff_false,ite_false,ite_true] using h
end Thomason.DirectedComplex.RankedAtoms

end

noncomputable section
universe u v w z


namespace Thomason.GrayRecursive.IntervalHom
open CategoryTheory DirectedComplex Table OmegaCategory NormalizedChains

variable {N : ℕ} {P : Type u} [LinearOrder P] (e : Fin (N+1) ≃o P)

theorem tensor_top_sequence (n : ℕ)
    (x : (tensorFunctor.obj (NormalizedChains.complex P).nu).Cell)
    (hx : (tensorFunctor.obj (NormalizedChains.complex P).nu).source (n+1) x = x) :
    (tensorFunctor.obj (NormalizedChains.complex P).nu).TopSequence n
      ((Prism.Basis.ofOrderIso e).TopGenerator (chainComparison (NormalizedChains.complex P)) n) x := by
  let M := NormalizedChains.complex P
  let A := Prism.Word.ofOrderIso e
  let B := Prism.Basis.ofOrderIso e
  let T := tensorFunctor.obj M.nu
  let F := chainComparison M
  have hh := tensor_atomic_layers A (n+1) x hx
  clear hx
  induction hh with
  | endpoint a b hb =>
    by_cases he : A.dim b ≤ n
    · apply TopSequence.lower
      erw [endpoint_source]
      exact congrArg ((tensorEndpoint a).app M.nu).map
        (M.nu.source_fixed_upwards he (A.bounded b))
    · apply TopSequence.single
      apply Whisker.generator
      · exact ⟨Prism.Basis.endpoint a b,by change A.dim b = n+1; omega,
          chainComparison_endpoint_basis e a b⟩
      · erw [endpoint_source]
        exact congrArg ((tensorEndpoint a).app M.nu).map
          (M.nu.source_fixed_upwards hb (A.bounded b))
  | vertical b hb =>
    by_cases he : A.dim b < n
    · exact TopSequence.lower _ (T.source_fixed_upwards (by omega : A.dim b+1 ≤ n)
        (verticalCell_bounded _ _))
    · apply TopSequence.single
      apply Whisker.generator
      · exact ⟨Prism.Basis.vertical b,by change A.dim b+1 = n+1; omega,
          chainComparison_vertical_basis e b⟩
      · exact T.source_fixed_upwards (by omega : A.dim b+1 ≤ n+1)
          (verticalCell_bounded _ _)
  | lower k hk z hz => exact TopSequence.lower _ (T.source_fixed_upwards (by omega : k ≤ n) hz)
  | compose k hk x y h hx hy ihx ihy => exact ihx.comp ihy k (by omega) h

end Thomason.GrayRecursive.IntervalHom

end

end OAI
end

section
-- module Solutions.OAIQ043_TH.Thomason_LayeredWhiskers
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Layered Whiskers. -/

noncomputable section
universe u v w z


namespace Thomason.OmegaCategory

variable (C : OmegaCategory.{u})

lemma join_distribute_left (k n : ℕ) (hk : k < n) (a l r : C.Cell)
    (hlr : C.target n l = C.source n r)
    (hal : C.target k a = C.source k l) :
    C.join k a (C.join n l r) =
      C.join n (C.join k a l) (C.join k (C.target n a) r) := by
  have htr : C.target k (C.target n a) = C.source k r := by
    have hh := congrArg (C.source k) hlr
    simp only [C.source_target, ite_eq_left hk, C.source_source, min_eq_left hk.le] at hh
    rw [C.target_target, min_eq_left hk.le]
    exact hal.trans hh
  have he := C.join_interchange k n hk a (C.target n a) l r
    (C.source_target_self n a).symm hlr hal htr
  rw [C.join_right_unit n a (C.target n a) (C.source_target_self n a)
    (C.source_target_self n a).symm] at he
  exact he

lemma join_distribute_right (k n : ℕ) (hk : k < n) (l r a : C.Cell)
    (hlr : C.target n l = C.source n r)
    (hra : C.target k r = C.source k a) :
    C.join k (C.join n l r) a =
      C.join n (C.join k l (C.source n a)) (C.join k r a) := by
  have hls : C.target k l = C.source k (C.source n a) := by
    have hh := congrArg (C.target k) hlr
    simp only [C.target_target, min_eq_left hk.le, C.target_source, ite_eq_left hk] at hh
    rw [C.source_source, min_eq_left hk.le]
    exact hh.trans hra
  have he := C.join_interchange k n hk l r (C.source n a) a
    hlr (C.target_source_self n a) hls hra
  rw [C.join_left_unit n (C.source n a) a (C.source_source_self n a)
    (C.target_source_self n a)] at he
  exact he

variable {C}
namespace LayeredWhisker
variable {G : C.Cell → Prop}

lemma of_generator {b : C.Cell} (hb : G b) (n : ℕ) : C.LayeredWhisker G n b := by
  induction n with
  | zero => exact hb
  | succ n ih =>
    refine ⟨C.source n b,b,C.target n b,
      C.source_fixed_upwards (Nat.le_succ n) (C.source_source_self n b),
      C.source_fixed_upwards (Nat.le_succ n) (C.source_target_self n b),ih,
      C.target_source_self n b,(C.source_target_self n b).symm,?_⟩
    rw [C.join_left_unit n (C.source n b) b (C.source_source_self n b)
      (C.target_source_self n b), C.join_right_unit n b (C.target n b)
      (C.source_target_self n b) (C.source_target_self n b).symm]

lemma left {n : ℕ} {x : C.Cell} (hx : C.LayeredWhisker G n x)
    (k : ℕ) (hk : k < n) (a : C.Cell) (ha : C.source n a = a)
    (h : C.target k a = C.source k x) : C.LayeredWhisker G n (C.join k a x) := by
  induction n generalizing x k a with
  | zero => omega
  | succ n ih =>
    obtain ⟨l,m,r,hl,hr,hm,hlm,hmr,rfl⟩ := hx
    have hlmr : C.target n (C.join n l m) = C.source n r := by
      rw [C.join_target_le n n l m le_rfl hlm]
      exact hmr
    by_cases hkn : k = n
    · subst k
      have hal : C.target n a = C.source n l := by
        rw [C.join_source_le n n _ r le_rfl hlmr,
          C.join_source_le n n l m le_rfl hlm] at h
        exact h
      refine ⟨C.join n a l,m,r,?_,hr,hm,?_,hmr,?_⟩
      · rw [C.join_source_gt (n+1) n a l (Nat.lt_succ_self n) hal,ha,hl]
      · rw [C.join_target_le n n a l le_rfl hal]
        exact hlm
      · rw [C.join_assoc n (C.join n a l) m r
          (by rw [C.join_target_le n n a l le_rfl hal]; exact hlm) hmr,
          C.join_assoc n a l (C.join n m r) hal
          (by rw [C.join_source_le n n m r le_rfl hmr]; exact hlm),
          C.join_assoc n l m r hlm hmr]
    · have hkn : k < n := by omega
      have hal : C.target k a = C.source k l := by
        rw [C.join_source_le k n _ r hkn.le hlmr,
          C.join_source_le k n l m hkn.le hlm] at h
        exact h
      have hm' : C.source k l = C.source k m := by
        have hh := congrArg (C.source k) hlm
        simpa only [C.source_target,ite_eq_left hkn,C.source_source,min_eq_left hkn.le] using hh
      have hr' : C.source k m = C.source k r := by
        have hh := congrArg (C.source k) hmr
        simpa only [C.source_target,ite_eq_left hkn,C.source_source,min_eq_left hkn.le] using hh
      have htm : C.target k (C.target n a) = C.source k m := by
        rw [C.target_target,min_eq_left hkn.le]
        exact hal.trans hm'
      have htr : C.target k (C.target n a) = C.source k r := htm.trans hr'
      have hai : C.target k a = C.source k (C.join n l m) := by
        rw [C.join_source_le k n l m hkn.le hlm]
        exact hal
      refine ⟨C.join k a l, C.join k (C.target n a) m,
        C.join k (C.target n a) r,?_,?_,
        ih hm k hkn (C.target n a) (C.source_target_self n a) htm,?_,?_,?_⟩
      · rw [C.join_source_gt (n+1) k a l (by omega) hal,ha,hl]
      · rw [C.join_source_gt (n+1) k (C.target n a) r (by omega) htr,
          C.source_fixed_upwards (Nat.le_succ n) (C.source_target_self n a),hr]
      · rw [C.join_target_gt n k a l hkn hal,
          C.join_source_gt n k (C.target n a) m hkn htm,
          C.source_target_self n a,hlm]
      · rw [C.join_target_gt n k (C.target n a) m hkn htm,
          C.join_source_gt n k (C.target n a) r hkn htr,
          C.source_target_self n a,C.target_target,min_self,hmr]
      · rw [C.join_distribute_left k n hkn a (C.join n l m) r hlmr hai,
          C.join_distribute_left k n hkn a l m hlm hal]

lemma right {n : ℕ} {x : C.Cell} (hx : C.LayeredWhisker G n x)
    (k : ℕ) (hk : k < n) (a : C.Cell) (ha : C.source n a = a)
    (h : C.target k x = C.source k a) : C.LayeredWhisker G n (C.join k x a) := by
  induction n generalizing x k a with
  | zero => omega
  | succ n ih =>
    obtain ⟨l,m,r,hl,hr,hm,hlm,hmr,rfl⟩ := hx
    have hlmr : C.target n (C.join n l m) = C.source n r := by
      rw [C.join_target_le n n l m le_rfl hlm]
      exact hmr
    by_cases hkn : k = n
    · subst k
      have hra : C.target n r = C.source n a := by
        rw [C.join_target_le n n _ r le_rfl hlmr] at h
        exact h
      refine ⟨l,m,C.join n r a,hl,?_,hm,hlm,?_,?_⟩
      · rw [C.join_source_gt (n+1) n r a (Nat.lt_succ_self n) hra,hr,ha]
      · rw [C.join_source_le n n r a le_rfl hra]
        exact hmr
      · exact C.join_assoc n (C.join n l m) r a hlmr hra
    · have hkn : k < n := by omega
      have hra : C.target k r = C.source k a := by
        rw [C.join_target_le k n _ r hkn.le hlmr] at h
        exact h
      have hl' : C.target k l = C.target k m := by
        have hh := congrArg (C.target k) hlm
        simpa only [C.target_target,min_eq_left hkn.le,C.target_source,ite_eq_left hkn] using hh
      have hm' : C.target k m = C.target k r := by
        have hh := congrArg (C.target k) hmr
        simpa only [C.target_target,min_eq_left hkn.le,C.target_source,ite_eq_left hkn] using hh
      have hms : C.target k m = C.source k (C.source n a) := by
        rw [C.source_source,min_eq_left hkn.le]
        exact hm'.trans hra
      have hls : C.target k l = C.source k (C.source n a) := hl'.trans hms
      have his : C.target k (C.join n l m) = C.source k (C.source n a) := by
        rw [C.join_target_le k n l m hkn.le hlm]
        exact hms
      refine ⟨C.join k l (C.source n a), C.join k m (C.source n a),
        C.join k r a,?_,?_,
        ih hm k hkn (C.source n a) (C.source_source_self n a) hms,?_,?_,?_⟩
      · rw [C.join_source_gt (n+1) k l (C.source n a) (by omega) hls,hl,
          C.source_fixed_upwards (Nat.le_succ n) (C.source_source_self n a)]
      · rw [C.join_source_gt (n+1) k r a (by omega) hra,hr,ha]
      · rw [C.join_target_gt n k l (C.source n a) hkn hls,
          C.join_source_gt n k m (C.source n a) hkn hms,
          C.source_source_self n a,C.target_source_self n a,hlm]
      · rw [C.join_target_gt n k m (C.source n a) hkn hms,
          C.join_source_gt n k r a hkn hra,C.target_source_self n a,hmr]
      · rw [C.join_distribute_right k n hkn (C.join n l m) r a hlmr hra,
          C.join_whisker_right k n hkn l m (C.source n a)
            (C.source_source_self n a) hlm hls hms]

end LayeredWhisker

end Thomason.OmegaCategory

end

noncomputable section
universe u v w z


namespace Thomason.DirectedComplex
open OmegaCategory

namespace Table
variable {K : DirectedComplex.{u}}

lemma comp_left_cancel (n : ℕ) (x y z : Table K)
    (hxy : truncate n true x = truncate n false y)
    (hxz : truncate n true x = truncate n false z)
    (he : comp n x y hxy = comp n x z hxz) : y = z := by
  ext p e
  by_cases hp : p < n
  · exact (lower_rows_eq hxy hp e).symm.trans (lower_rows_eq hxz hp e)
  · by_cases hpn : p = n
    · subst p
      cases e
      · exact (matching_row_eq hxy).symm.trans (matching_row_eq hxz)
      · have hh := congrArg (fun t : Table K => t.row n true) he
        simpa only [comp_row,lt_self_iff_false,ite_false,ite_true] using hh
    · have hh := congrArg (fun t : Table K => t.row p e) he
      simp only [comp_row,ite_eq_right hp,ite_eq_right hpn] at hh
      exact add_left_cancel hh

lemma comp_right_cancel (n : ℕ) (x y z : Table K)
    (hxz : truncate n true x = truncate n false z)
    (hyz : truncate n true y = truncate n false z)
    (he : comp n x z hxz = comp n y z hyz) : x = y := by
  ext p e
  by_cases hp : p < n
  · exact (lower_rows_eq hxz hp e).trans (lower_rows_eq hyz hp e).symm
  · by_cases hpn : p = n
    · subst p
      cases e
      · have hh := congrArg (fun t : Table K => t.row n false) he
        simpa only [comp_row,lt_self_iff_false,ite_false,ite_true,Bool.false_eq_true] using hh
      · exact (matching_row_eq hxz).trans (matching_row_eq hyz).symm
    · have hh := congrArg (fun t : Table K => t.row p e) he
      simp only [comp_row,ite_eq_right hp,ite_eq_right hpn] at hh
      exact add_right_cancel hh

lemma join_left_cancel (n : ℕ) (x y z : Table K)
    (hxy : K.nu.target n x = K.nu.source n y)
    (hxz : K.nu.target n x = K.nu.source n z)
    (he : K.nu.join n x y = K.nu.join n x z) : y = z := by
  rw [K.nu.join_eq n x y hxy,K.nu.join_eq n x z hxz] at he
  exact comp_left_cancel n x y z hxy hxz he

lemma join_right_cancel (n : ℕ) (x y z : Table K)
    (hxz : K.nu.target n x = K.nu.source n z)
    (hyz : K.nu.target n y = K.nu.source n z)
    (he : K.nu.join n x z = K.nu.join n y z) : x = y := by
  rw [K.nu.join_eq n x z hxz,K.nu.join_eq n y z hyz] at he
  exact comp_right_cancel n x y z hxz hyz he

end Table

namespace RankedAtoms
open Table
variable {K : DirectedComplex.{u}} (A : RankedAtoms.{u,v} K)
variable {C : OmegaCategory.{w}} (F : OmegaCategory.Functor C K.nu)

lemma top_and_target_ext (n : ℕ) (x y : Table K)
    (hx : truncate (n+1) false x = x) (hy : truncate (n+1) false y = y)
    (ht : x.row (n+1) false = y.row (n+1) false)
    (hs : truncate n true x = truncate n true y) : x = y := by
  ext p e
  by_cases hp : n < p
  · exact NormalizedChains.rows_above_top_agree x y hx hy ht p (by omega) e
  · have hpn : p ≤ n := by omega
    by_cases he : p = n ∧ e = false
    · obtain ⟨he,rfl⟩ := he
      subst p
      have hright := congrArg (fun z : Table K => z.row n true) hs
      simp only [truncate_row,lt_self_iff_false,ite_false,ite_true] at hright
      have hd := congrArg (K.d n) ht
      rw [x.boundary,y.boundary,hright] at hd
      exact (sub_right_inj).mp hd
    · have h := congrArg (fun z : Table K => z.row p e) hs
      by_cases hpn' : p < n
      · simpa only [truncate_row,ite_eq_left hpn'] using h
      · have hp : p = n := by omega
        subst p
        have he' : e = true := by cases e <;> simp_all
        subst e
        simpa only [truncate_row,lt_self_iff_false,ite_false,ite_true] using h

namespace OrderedWhisker
variable {A F}

lemma layered {b : A.Index} {n : ℕ} {x : C.Cell} (hx : A.OrderedWhisker F b n x) :
    C.LayeredWhisker (fun z => F.map z = A.atom b) n x := by
  induction n generalizing x with
  | zero => exact hx
  | succ n ih =>
    obtain ⟨l,m,r,hl,hr,hm,hlm,hmr,_,_,he⟩ := hx
    exact ⟨l,m,r,hl,hr,ih hm,hlm,hmr,he⟩

lemma row_above {b : A.Index} {n : ℕ} {x : C.Cell} (hx : A.OrderedWhisker F b n x)
    (p : ℕ) (hp : n < p) (e : Bool) : (F.map x).row p e = (A.atom b).row p e := by
  induction n generalizing x with
  | zero => change F.map x = A.atom b at hx; rw [hx]
  | succ n ih =>
    obtain ⟨l,m,r,hl,hr,hm,hlm,hmr,_,_,rfl⟩ := hx
    have hf (a : C.Cell) (ha : C.source (n+1) a = a) : (F.map a).row p e = 0 :=
      row_above_fixed (F.map a) ((F.map_source (n+1) a).symm.trans (congrArg F.map ha)) hp e
    have hpm : ¬p < n := by omega
    have hpn : p ≠ n := by omega
    have hlmr : C.target n (C.join n l m) = C.source n r := by
      rw [C.join_target_le n n l m le_rfl hlm]; exact hmr
    rw [F.map_join n _ r hlmr,K.nu.join_eq n _ _ (F.map_composable hlmr)]
    change (comp n (F.map (C.join n l m)) (F.map r) (F.map_composable hlmr)).row p e = _
    erw [comp_row]
    rw [ite_eq_right hpm,ite_eq_right hpn,F.map_join n l m hlm,
      K.nu.join_eq n _ _ (F.map_composable hlm)]
    change (comp n (F.map l) (F.map m) (F.map_composable hlm)).row p e + (F.map r).row p e = _
    erw [comp_row]
    rw [ite_eq_right hpm,ite_eq_right hpn,hf l hl,hf r hr,zero_add,add_zero]
    exact ih hm (by omega)

lemma split_unique (p : ℕ) (r : ℤ) (l₁ l₂ r₁ r₂ : K.Chain p)
    (hl₁ : ∀ c, A.coefficient c p l₁ ≠ 0 → r < A.rank c)
    (hl₂ : ∀ c, A.coefficient c p l₂ ≠ 0 → r < A.rank c)
    (hr₁ : ∀ c, A.coefficient c p r₁ ≠ 0 → ¬ r < A.rank c)
    (hr₂ : ∀ c, A.coefficient c p r₂ ≠ 0 → ¬ r < A.rank c)
    (he : l₁ + r₁ = l₂ + r₂) : l₁ = l₂ ∧ r₁ = r₂ := by
  have hl : l₁ = l₂ := by
    apply A.ext p
    intro c
    have hh := congrArg (A.coefficient c p) he
    simp only [map_add] at hh
    by_cases hc : r < A.rank c
    · have h₁ : A.coefficient c p r₁ = 0 := by by_contra h; exact hr₁ c h hc
      have h₂ : A.coefficient c p r₂ = 0 := by by_contra h; exact hr₂ c h hc
      simpa only [h₁,h₂,add_zero] using hh
    · have h₁ : A.coefficient c p l₁ = 0 := by by_contra h; exact hc (hl₁ c h)
      have h₂ : A.coefficient c p l₂ = 0 := by by_contra h; exact hc (hl₂ c h)
      exact h₁.trans h₂.symm
  exact ⟨hl,add_left_cancel (hl ▸ he)⟩

theorem eq_of_map_eq (b : A.Index) (n : ℕ)
    (hatom : ∀ x y : C.Cell, F.map x = A.atom b → F.map y = A.atom b → x = y)
    (hsmall : ∀ k, k ≤ n → Function.Injective (F.onCells k))
    (x y : C.Cell) (hx : A.OrderedWhisker F b n x) (hy : A.OrderedWhisker F b n y)
    (he : F.map x = F.map y) : x = y := by
  induction n generalizing x y with
  | zero => exact hatom x y hx hy
  | succ n ih =>
    obtain ⟨l,m,r,hl,hr,hm,hlm,hmr,hlo,hro,rfl⟩ := hx
    obtain ⟨l',m',r',hl',hr',hm',hlm',hmr',hlo',hro',rfl⟩ := hy
    have hfm := hm.row_above (n+1) (Nat.lt_succ_self n) false
    have hfm' := hm'.row_above (n+1) (Nat.lt_succ_self n) false
    have hlmr : C.target n (C.join n l m) = C.source n r := by
      rw [C.join_target_le n n l m le_rfl hlm]; exact hmr
    have hlmr' : C.target n (C.join n l' m') = C.source n r' := by
      rw [C.join_target_le n n l' m' le_rfl hlm']; exact hmr'
    have ht := congrArg (fun t : Table K => t.row (n+1) false) he
    rw [top_row_join F (n+1) n (Nat.lt_succ_self n) _ r hlmr,
      top_row_join F (n+1) n (Nat.lt_succ_self n) l m hlm,
      top_row_join F (n+1) n (Nat.lt_succ_self n) _ r' hlmr',
      top_row_join F (n+1) n (Nat.lt_succ_self n) l' m' hlm',hfm,hfm'] at ht
    have hsum : (F.map l).row (n+1) false + (F.map r).row (n+1) false =
        (F.map l').row (n+1) false + (F.map r').row (n+1) false := by
      have hh := congrArg (fun z => z - (A.atom b).row (n+1) false) ht
      convert hh using 1 <;> abel
    obtain ⟨hlt,hrt⟩ := split_unique (A := A) (n+1) (A.rank b) _ _ _ _ hlo hlo' hro hro' hsum
    have hf (z : C.Cell) (hz : C.source (n+1) z = z) : truncate (n+1) false (F.map z) = F.map z :=
      (F.map_source (n+1) z).symm.trans (congrArg F.map hz)
    have hle : F.map l = F.map l' := by
      apply top_and_source_ext n _ _ (hf l hl) (hf l' hl') hlt
      have hs := congrArg (K.nu.source n) he
      rw [← F.map_source,← F.map_source,
        C.join_source_le n n _ r le_rfl hlmr,C.join_source_le n n l m le_rfl hlm,
        C.join_source_le n n _ r' le_rfl hlmr',C.join_source_le n n l' m' le_rfl hlm',
        F.map_source,F.map_source] at hs
      exact hs
    have hre : F.map r = F.map r' := by
      apply top_and_target_ext n _ _ (hf r hr) (hf r' hr') hrt
      have hs := congrArg (K.nu.target n) he
      rw [← F.map_target,← F.map_target,
        C.join_target_le n n _ r le_rfl hlmr,C.join_target_le n n _ r' le_rfl hlmr',
        F.map_target,F.map_target] at hs
      exact hs
    have hll : l = l' := congrArg Subtype.val (hsmall (n+1) le_rfl
      (a₁ := ⟨l,hl⟩) (a₂ := ⟨l',hl'⟩) (Subtype.ext hle))
    have hrr : r = r' := congrArg Subtype.val (hsmall (n+1) le_rfl
      (a₁ := ⟨r,hr⟩) (a₂ := ⟨r',hr'⟩) (Subtype.ext hre))
    subst l'
    subst r'
    have hmm : F.map m = F.map m' := by
      rw [F.map_join n _ r hlmr,F.map_join n l m hlm,
        F.map_join n _ r hlmr',F.map_join n l m' hlm'] at he
      apply Table.join_left_cancel n (F.map l) _ _ (F.map_composable hlm) (F.map_composable hlm')
      apply Table.join_right_cancel n _ _ (F.map r)
        (by rw [← F.map_join n l m hlm]; exact F.map_composable hlmr)
        (by rw [← F.map_join n l m' hlm']; exact F.map_composable hlmr') he
    have hmm' : m = m' := ih (fun k hk => hsmall k (by omega)) m m' hm hm' hmm
    rw [hmm']

end OrderedWhisker
end RankedAtoms
end Thomason.DirectedComplex

end

noncomputable section
universe u v w z


namespace Thomason.DirectedComplex
open Table OmegaCategory

namespace Table
variable {K : DirectedComplex.{u}}

lemma factor_context_with_top (k : ℕ) (y : Table K) (c d : K.Chain (k+1))
    (hc : c ∈ K.positive (k+1)) (hd : d ∈ K.positive (k+1))
    (ht : ∀ b, y.row (k+1) b - c - d ∈ K.positive (k+1))
    (hs : y.row k false + K.d k c ∈ K.positive k)
    (he : y.row k true - K.d k d ∈ K.positive k) :
    ∃ (l r : Table K) (hlm : truncate k true l = truncate k false (removeContext k y c d ht hs he))
      (hmr : truncate k true (comp k l (removeContext k y c d ht hs he) hlm) = truncate k false r),
      truncate (k+1) false l = l ∧ truncate (k+1) false r = r ∧
      l.row (k+1) false = c ∧ r.row (k+1) false = d ∧
      comp k (comp k l (removeContext k y c d ht hs he) hlm) r hmr = y := by
  let m := removeContext k y c d ht hs he
  let s := truncate k false y
  have hsf : truncate k false s = s := by simp [s, truncate_truncate_same]
  have hs' : s.row k false + K.d k c ∈ K.positive k := by simpa [s] using hs
  let l := extendTop k s hsf c hc hs'
  have hlm : truncate k true l = truncate k false m := by
    ext p b
    rw [truncate_row, truncate_row]
    by_cases hp : p < k
    · simp only [ite_eq_left hp]
      change extensionRow k s c p b = removeContextRow k y c d p b
      rw [extensionRow_other k s c p b (by omega) (by omega),
        removeContextRow_other k y c d p b (by omega) (by omega)]
      simp [s, hp]
    · rw [ite_eq_right hp, ite_eq_right hp]
      by_cases heq : p = k
      · subst p
        simp only [ite_true]
        change extensionRow k s c k true = removeContextRow k y c d k false
        simp [s]
      · simp only [ite_eq_right heq]
  let t := truncate k true m
  have htf : truncate k false t = t := by simp [t, truncate_truncate]
  have htrow : t.row k false = y.row k true - K.d k d := by simp [t, m]
  have ht' : t.row k false + K.d k d ∈ K.positive k := by
    rw [htrow, sub_add_cancel]; exact y.positive k true
  let r := extendTop k t htf d hd ht'
  have hmr : truncate k true (comp k l m hlm) = truncate k false r := by
    rw [target_comp_le k k le_rfl, extendTop_source]
  refine ⟨l, r, hlm, hmr, extendTop_dimension k s hsf c hc hs',
    extendTop_dimension k t htf d hd ht', by simp [l], by simp [r], ?_⟩
  ext p b
  simp only [comp_row]
  by_cases hp : p < k
  · simp only [ite_eq_left hp]
    change extensionRow k s c p b = y.row p b
    rw [extensionRow_other k s c p b (by omega) (by omega)]
    simp [s, hp]
  · simp only [ite_eq_right hp]
    by_cases heq : p = k
    · subst p
      simp only [ite_true]
      cases b
      · simp only [Bool.false_eq_true, ite_false]
        change extensionRow k s c k false = y.row k false
        simp [s]
      · simp only [ite_true]
        change extensionRow k t d k true = y.row k true
        simp only [extensionRow_middle, ite_true, htrow, sub_add_cancel]
    · simp only [ite_eq_right heq]
      by_cases hk : p = k+1
      · subst p
        change extensionRow k s c (k+1) b + removeContextRow k y c d (k+1) b +
          extensionRow k t d (k+1) b = y.row (k+1) b
        rw [extensionRow_top, extensionRow_top, removeContextRow_top]
        abel
      · change extensionRow k s c p b + removeContextRow k y c d p b +
          extensionRow k t d p b = y.row p b
        rw [extensionRow_other k s c p b heq hk, extensionRow_other k t d p b heq hk,
          removeContextRow_other k y c d p b heq hk]
        have hz₁ : s.row p b = 0 := by simp [s, hp, heq]
        have hz₂ : t.row p b = 0 := by simp [t, hp, heq]
        rw [hz₁, hz₂, zero_add, add_zero]

end Table

namespace RankedAtoms
variable {K : DirectedComplex.{u}} (A : RankedAtoms.{u,v} K)
variable {C : OmegaCategory.{w}} (F : OmegaCategory.Functor C K.nu)

theorem table_ordered_whisker (b : A.Index) (n : ℕ) (hn : n < A.dim b)
    (y : Table K) (hy : ∀ p, n < p → ∀ e, y.row p e = (A.atom b).row p e) :
    A.OrderedWhisker (OmegaCategory.Functor.id K.nu) b n y := by
  induction n generalizing y with
  | zero =>
    change y = A.atom b
    obtain ⟨hz,hcommon⟩ := A.common_atom_context b 0 hn y (hy 1 (by omega) false)
    have haug : K.augmentation (y.row 0 false - (A.atom b).row 0 false) = 0 := by
      rw [map_sub,y.augmentation,(A.atom b).augmentation,sub_self]
    have hz₀ := A.positive_augmentation_zero _ hz haug
    ext p e
    cases p with
    | zero =>
      cases e
      · exact sub_eq_zero.mp hz₀
      · exact sub_eq_zero.mp (hcommon.trans hz₀)
    | succ p => exact hy (p+1) (by omega) e
  | succ n ih =>
    obtain ⟨hz,hcommon⟩ := A.common_atom_context b (n+1) hn y (hy (n+2) (by omega) false)
    let z := y.row (n+1) false - (A.atom b).row (n+1) false
    let c := A.cut (n+1) z (fun t => A.rank b < A.rank t)
    let d := A.cut (n+1) z (fun t => ¬ A.rank b < A.rank t)
    have hc : c ∈ K.positive (n+1) := A.cut_positive _ _ hz _
    have hd : d ∈ K.positive (n+1) := A.cut_positive _ _ hz _
    have hcd : c + d = z := A.cut_add_complement _ _ _
    have hrows (e : Bool) : y.row (n+1) e - c - d = (A.atom b).row (n+1) e := by
      have he : y.row (n+1) e - (A.atom b).row (n+1) e = z := by
        cases e
        · rfl
        · exact hcommon
      rw [sub_sub,hcd]
      exact sub_eq_iff_eq_add.mpr ((sub_eq_iff_eq_add.mp he).trans (add_comm _ _))
    have ht : ∀ e, y.row (n+1) e - c - d ∈ K.positive (n+1) := by
      intro e
      rw [hrows]
      exact (A.atom b).positive _ _
    have hdiff : y.row n true - y.row n false = (A.atom b).row n true -
        (A.atom b).row n false + K.d n z := by
      dsimp [z]
      rw [map_sub,y.boundary,(A.atom b).boundary]
      abel
    obtain ⟨hstart,hend⟩ := A.rank_cut_positive n (A.rank b) _ _ _ _ z
      ((A.atom b).positive n false) ((A.atom b).positive n true)
      (y.positive n false) (y.positive n true) hz
      (fun t ht => A.ranked b n (by omega) false t ht)
      (fun t ht => A.ranked b n (by omega) true t ht) hdiff
    let m := removeContext n y c d ht hstart hend
    have hm : A.OrderedWhisker (OmegaCategory.Functor.id K.nu) b n m := by
      apply ih (by omega) m
      intro p hp e
      change removeContextRow n y c d p e = (A.atom b).row p e
      by_cases hpn : p = n+1
      · subst p; rw [removeContextRow_top,hrows]
      · rw [removeContextRow_other n y c d p e (by omega) hpn]
        exact hy p (by omega) e
    obtain ⟨l,r,hlm,hmr,hl,hr,hlt,hrt,he⟩ := factor_context_with_top n y c d hc hd ht hstart hend
    have hmr' : K.nu.target n m = K.nu.source n r := by
      change truncate n true m = truncate n false r
      rw [target_comp_le n n le_rfl] at hmr
      exact hmr
    refine ⟨l,m,r,hl,hr,hm,hlm,hmr',?_,?_,?_⟩
    · intro t ht
      change A.coefficient t (n+1) (l.row (n+1) false) ≠ 0 at ht
      rw [hlt,A.coefficient_cut] at ht
      by_contra hh
      exact ht (ite_eq_right hh)
    · intro t ht
      change A.coefficient t (n+1) (r.row (n+1) false) ≠ 0 at ht
      rw [hrt,A.coefficient_cut] at ht
      by_contra hh
      exact ht (ite_eq_right (not_not_intro hh))
    · rw [K.nu.join_eq n l m hlm]
      rw [K.nu.join_eq n (K.nu.comp n l m hlm) r hmr]
      exact he.symm

namespace OrderedWhisker
variable {A F}

theorem lift (b : A.Index) (n : ℕ)
    (hatom : ∃ x : C.Cell, F.map x = A.atom b)
    (hsmall : ∀ k, k ≤ n → Function.Bijective (F.onCells k))
    (y : Table K) (hy : A.OrderedWhisker (OmegaCategory.Functor.id K.nu) b n y) :
    ∃ x : C.Cell, A.OrderedWhisker F b n x ∧ F.map x = y := by
  induction n generalizing y with
  | zero =>
    obtain ⟨x,hx⟩ := hatom
    exact ⟨x,hx,hx.trans hy.symm⟩
  | succ n ih =>
    obtain ⟨l,m,r,hl,hr,hm,hlm,hmr,hlo,hro,rfl⟩ := hy
    obtain ⟨l',hl'⟩ := (hsmall (n+1) le_rfl).2 ⟨l,hl⟩
    obtain ⟨r',hr'⟩ := (hsmall (n+1) le_rfl).2 ⟨r,hr⟩
    have hfl : F.map l'.val = l := congrArg Subtype.val hl'
    have hfr : F.map r'.val = r := congrArg Subtype.val hr'
    obtain ⟨m',hm',hfm⟩ := ih (fun k hk => hsmall k (by omega)) m hm
    have hlm' : C.target n l'.val = C.source n m' := by
      apply congrArg Subtype.val ((hsmall n (Nat.le_succ n)).1
        (a₁ := ⟨C.target n l'.val,C.source_target_self n _⟩)
        (a₂ := ⟨C.source n m',C.source_source_self n _⟩) (Subtype.ext ?_))
      change F.map (C.target n l'.val) = F.map (C.source n m')
      rw [F.map_target,F.map_source,hfl,hfm]
      exact hlm
    have hmr' : C.target n m' = C.source n r'.val := by
      apply congrArg Subtype.val ((hsmall n (Nat.le_succ n)).1
        (a₁ := ⟨C.target n m',C.source_target_self n _⟩)
        (a₂ := ⟨C.source n r'.val,C.source_source_self n _⟩) (Subtype.ext ?_))
      change F.map (C.target n m') = F.map (C.source n r'.val)
      rw [F.map_target,F.map_source,hfm,hfr]
      exact hmr
    have hlmr' : C.target n (C.join n l'.val m') = C.source n r'.val := by
      rw [C.join_target_le n n l'.val m' le_rfl hlm']; exact hmr'
    refine ⟨C.join n (C.join n l'.val m') r'.val,?_,?_⟩
    · refine ⟨l'.val,m',r'.val,l'.property,r'.property,hm',hlm',hmr',?_,?_,rfl⟩
      · intro c hc
        rw [hfl] at hc
        exact hlo c hc
      · intro c hc
        rw [hfr] at hc
        exact hro c hc
    · rw [F.map_join n _ r'.val hlmr',F.map_join n l'.val m' hlm',hfl,hfm,hfr]

end OrderedWhisker

end RankedAtoms
end Thomason.DirectedComplex

end

noncomputable section
universe u v w z


namespace Thomason.OmegaCategory
variable {C : OmegaCategory.{u}} {D : OmegaCategory.{v}}

lemma Functor.bounded_ext (F : Functor C D) (n : ℕ)
    (hinj : Function.Injective (F.onCells n)) (x y : C.Cell)
    (hx : C.source n x = x) (hy : C.source n y = y) (he : F.map x = F.map y) : x = y :=
  congrArg Subtype.val (hinj (a₁ := ⟨x,hx⟩) (a₂ := ⟨y,hy⟩) (Subtype.ext he))

lemma LayeredWhisker.row_bounded {G : C.Cell → Prop} (d : ℕ)
    (hg : ∀ x, G x → C.source d x = x) {n : ℕ} (hn : n ≤ d) {x : C.Cell}
    (hx : C.LayeredWhisker G n x) : C.source d x = x := by
  induction n generalizing x with
  | zero => exact hg x hx
  | succ n ih =>
    obtain ⟨l,m,r,hl,hr,hm,hlm,hmr,rfl⟩ := hx
    have hlmr : C.target n (C.join n l m) = C.source n r := by
      rw [C.join_target_le n n l m le_rfl hlm]; exact hmr
    rw [C.join_source_gt d n _ r (by omega) hlmr,
      C.join_source_gt d n l m (by omega) hlm,
      C.source_fixed_upwards hn hl,C.source_fixed_upwards hn hr,ih (by omega) hm]

lemma LayeredWhisker.whisker {G : C.Cell → Prop} (d : ℕ)
    (hg : ∀ x, G x → C.source (d+1) x = x) {n : ℕ} (hn : n ≤ d) {x : C.Cell}
    (hx : C.LayeredWhisker G n x) : C.Whisker d G x := by
  induction n generalizing x with
  | zero => exact .generator x hx (hg x hx)
  | succ n ih =>
    obtain ⟨l,m,r,hl,hr,hm,hlm,hmr,rfl⟩ := hx
    have hlmr : C.target n (C.join n l m) = C.source n r := by
      rw [C.join_target_le n n l m le_rfl hlm]; exact hmr
    exact .right n (by omega) _ r (C.source_fixed_upwards hn hr) hlmr
      (.left n (by omega) l m (C.source_fixed_upwards hn hl) hlm (ih (by omega) hm))

end Thomason.OmegaCategory

end

end OAI
end

section
-- module Solutions.OAIQ043_TH.Thomason_RankedExchange
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Ranked Exchange. -/

noncomputable section
universe u v w z


namespace Thomason.DirectedComplex.RankedAtoms
open Table OmegaCategory

variable {K : DirectedComplex.{u}} (A : RankedAtoms.{u,v} K)
variable {C : OmegaCategory.{w}} (F : OmegaCategory.Functor C K.nu)

namespace AtomPath
variable {A F} {n : ℕ}

lemma bounded {bs : List A.Index} {x : C.Cell} (h : A.AtomPath F n bs x) :
    C.source (n+1) x = x := by
  induction h with
  | nil x hx => exact C.source_fixed_upwards (Nat.le_succ n) hx
  | cons b hb x y bs hx ht h hy ih =>
    rw [C.join_source_gt (n+1) n x y (Nat.lt_succ_self n) h,hx.bounded,ih]

lemma append {bs cs : List A.Index} {x y : C.Cell}
    (hx : A.AtomPath F n bs x) (hy : A.AtomPath F n cs y)
    (h : C.target n x = C.source n y) : A.AtomPath F n (bs++cs) (C.join n x y) := by
  induction hx with
  | nil x hx =>
    rw [C.join_left_unit n x y hx h]
    exact hy
  | cons b hb z x bs hz ht hz_x hp ih =>
    have hx_y : C.target n x = C.source n y := by
      rw [C.join_target_le n n z x le_rfl hz_x] at h
      exact h
    rw [C.join_assoc n z x y hz_x hx_y]
    refine .cons b hb z (C.join n x y) (bs++cs) hz ht ?_ (ih hx_y)
    rw [C.join_source_le n n x y le_rfl hx_y]
    exact hz_x

lemma single {x : C.Cell} (hx : C.Whisker n (A.TopGenerator F n) x) :
    ∃ b, A.AtomPath F n [b] x := by
  obtain ⟨b,hb,ht⟩ := A.whisker_top_basis F hx
  refine ⟨b,?_⟩
  have h : C.target n x = C.source n (C.target n x) := (C.source_target_self n x).symm
  have hp := AtomPath.cons b hb x (C.target n x) [] hx ht h
    (AtomPath.nil (A := A) (F := F) (C.target n x) (C.source_target_self n x))
  rw [C.join_right_unit n x (C.target n x) (C.source_target_self n x) h] at hp
  exact hp

lemma coefficient {bs : List A.Index} {x : C.Cell} (h : A.AtomPath F n bs x)
    (b : A.Index) : A.coefficient b (n+1) ((F.map x).row (n+1) false) =
      (by classical exact (bs.count b : ℤ)) := by
  classical
  induction h with
  | nil x hx => rw [top_row_lower F n x hx,map_zero]; rfl
  | cons c hc x y cs hx ht h hp ih =>
    rw [top_row_join F (n+1) n (Nat.lt_succ_self n) x y h,map_add,ht,A.coefficient_basis,
      ite_eq_left hc,ih]
    by_cases he : c = b
    · subst c
      simp
      omega
    · simp [he]

lemma nodup {bs : List A.Index} {x : C.Cell} (h : A.AtomPath F n bs x) : bs.Nodup := by
  classical
  apply List.nodup_iff_count_le_one.mpr
  intro b
  have hm := A.top_coefficient_le_one (n+1) (F.map x)
    ((F.map_source (n+1) x).symm.trans (congrArg F.map h.bounded)) b
  rw [h.coefficient b] at hm
  omega

lemma perm_of_image_eq {bs cs : List A.Index} {x y : C.Cell}
    (hx : A.AtomPath F n bs x) (hy : A.AtomPath F n cs y) (he : F.map x = F.map y) :
    bs.Perm cs := by
  classical
  apply List.perm_iff_count.mpr
  intro b
  have h := congrArg (fun t : Table K => A.coefficient b (n+1) (t.row (n+1) false)) he
  rw [hx.coefficient b,hy.coefficient b] at h
  exact_mod_cast h

end AtomPath

lemma topSequence_path {n : ℕ} {x : C.Cell}
    (h : C.TopSequence n (A.TopGenerator F n) x) :
    ∃ bs : List A.Index, A.AtomPath F n bs x := by
  induction h with
  | lower x hx => exact ⟨[],.nil x hx⟩
  | single x hx =>
    obtain ⟨b,hb⟩ := AtomPath.single hx
    exact ⟨[b],hb⟩
  | compose x y h hx hy ihx ihy =>
    obtain ⟨bs,hbs⟩ := ihx
    obtain ⟨cs,hcs⟩ := ihy
    exact ⟨bs++cs,hbs.append hcs h⟩
end Thomason.DirectedComplex.RankedAtoms

end

noncomputable section
universe u v w z


namespace Thomason.DirectedComplex.RankedAtoms
open Table OmegaCategory

variable {K : DirectedComplex.{u}} (A : RankedAtoms.{u,v} K)

lemma orderRank_strict {b c : A.Index} (h : A.rank b < A.rank c) :
    A.orderRank b < A.orderRank c := by
  have hb : ((Fintype.equivFin A.Index b).val : ℤ) < Fintype.card A.Index := by
    exact_mod_cast (Fintype.equivFin A.Index b).isLt
  have hc : (0 : ℤ) ≤ (Fintype.equivFin A.Index c).val := Int.natCast_nonneg _
  have hn : (0 : ℤ) ≤ Fintype.card A.Index := Int.natCast_nonneg _
  have hm := mul_le_mul_of_nonneg_left (Int.add_one_le_iff.mpr h) hn
  dsimp [orderRank]
  nlinarith

lemma orderRank_injective : Function.Injective A.orderRank := by
  intro b c h
  have hr : A.rank b = A.rank c := by
    have hbc : ¬ A.rank b < A.rank c := fun hn => (ne_of_lt (A.orderRank_strict hn)) h
    have hcb : ¬ A.rank c < A.rank b := fun hn => (ne_of_lt (A.orderRank_strict hn)) h.symm
    omega
  have hf : (Fintype.equivFin A.Index b).val = (Fintype.equivFin A.Index c).val := by
    dsimp [orderRank] at h
    rw [hr] at h
    exact_mod_cast add_left_cancel h
  exact (Fintype.equivFin A.Index).injective (Fin.ext hf)

lemma rank_le_of_orderRank_le {b c : A.Index} (h : A.orderRank b ≤ A.orderRank c) :
    A.rank b ≤ A.rank c := by
  by_contra hn
  exact (not_lt_of_ge h) (A.orderRank_strict (lt_of_not_ge hn))

namespace AtomPath
variable {A}

lemma sorted_list_unique {C : OmegaCategory.{w}} {F : OmegaCategory.Functor C K.nu}
    {n : ℕ} {bs cs : List A.Index} {x y : C.Cell}
    (hx : A.AtomPath F n bs x) (hy : A.AtomPath F n cs y)
    (hbs : bs.Pairwise (fun b c => A.orderRank c < A.orderRank b))
    (hcs : cs.Pairwise (fun b c => A.orderRank c < A.orderRank b))
    (he : F.map x = F.map y) : bs = cs := by
  exact List.Perm.eq_of_pairwise
    (fun b c _ _ hbc hcb => A.orderRank_injective (le_antisymm hcb hbc))
    (hbs.imp fun h => h.le) (hcs.imp fun h => h.le)
    (hx.perm_of_image_eq hy he)

end AtomPath

end Thomason.DirectedComplex.RankedAtoms

end

noncomputable section
universe u v w z


namespace Thomason.DirectedComplex.RankedAtoms
open Table OmegaCategory

variable {K : DirectedComplex.{u}} (A : RankedAtoms.{u,v} K)
variable {C : OmegaCategory.{w}} (F : OmegaCategory.Functor C K.nu)

namespace AtomPath
variable {A F} {n : ℕ}

lemma eq_of_same_list
    (hn : ∀ x y : C.Cell, C.source n x = x → C.source n y = y → F.map x = F.map y → x = y)
    (hw : A.WhiskerFaithful F n)
    {bs : List A.Index} {x y : C.Cell}
    (hx : A.AtomPath F n bs x) (hy : A.AtomPath F n bs y)
    (he : F.map x = F.map y) : x = y := by
  induction hx generalizing y with
  | nil x hx =>
    cases hy with
    | nil y hy => exact hn x y hx hy he
  | cons b hb x z bs hx ht h hz ih =>
    cases hy with
    | cons _ _ y w _ hy hs h' hw' =>
      have hf (a : C.Cell) (ha : C.source (n+1) a = a) :
          truncate (n+1) false (F.map a) = F.map a :=
        (F.map_source (n+1) a).symm.trans (congrArg F.map ha)
      have hsource : truncate n false (F.map x) = truncate n false (F.map y) := by
        have h₀ := congrArg (fun t : Table K => truncate n false t) he
        change K.nu.source n _ = K.nu.source n _ at h₀
        rw [← F.map_source,← F.map_source,
          C.join_source_le n n x z le_rfl h,C.join_source_le n n y w le_rfl h',
          F.map_source,F.map_source] at h₀
        exact h₀
      have hhead : F.map x = F.map y :=
        top_and_source_ext n _ _ (hf x hx.bounded) (hf y hy.bounded) (ht.trans hs.symm) hsource
      have hxy : x = y := hw x y hx hy hhead
      subst y
      have htail : F.map z = F.map w := by
        apply top_and_source_ext n _ _ (hf z hz.bounded) (hf w hw'.bounded)
        · have ht₀ := congrArg (fun t : Table K => t.row (n+1) false) he
          rw [top_row_join F (n+1) n (Nat.lt_succ_self n) x z h,
            top_row_join F (n+1) n (Nat.lt_succ_self n) x w h'] at ht₀
          exact add_left_cancel ht₀
        · change K.nu.source n _ = K.nu.source n _
          rw [← F.map_source,← F.map_source,← h,← h']
      rw [ih hw' htail]

lemma eq_of_sorted
    (hn : ∀ x y : C.Cell, C.source n x = x → C.source n y = y → F.map x = F.map y → x = y)
    (hw : A.WhiskerFaithful F n)
    {bs cs : List A.Index} {x y : C.Cell}
    (hx : A.AtomPath F n bs x) (hy : A.AtomPath F n cs y)
    (hbs : bs.Pairwise (fun b c => A.orderRank c < A.orderRank b))
    (hcs : cs.Pairwise (fun b c => A.orderRank c < A.orderRank b))
    (he : F.map x = F.map y) : x = y := by
  have hh := hx.sorted_list_unique hy hbs hcs he
  subst cs
  exact hx.eq_of_same_list hn hw hy he

lemma insert_sorted (hex : A.HasAdjacentExchange F n)
    {bs : List A.Index} {y : C.Cell} (hy : A.AtomPath F n bs y)
    (hbs : bs.Pairwise (fun b c => A.orderRank c < A.orderRank b))
    (b : A.Index) (hb : A.dim b = n+1) (x : C.Cell)
    (hx : C.Whisker n (A.TopGenerator F n) x)
    (ht : (F.map x).row (n+1) false = A.basis (n+1) b)
    (h : C.target n x = C.source n y) :
    ∃ cs : List A.Index, A.AtomPath F n cs (C.join n x y) ∧
      cs.Pairwise (fun b c => A.orderRank c < A.orderRank b) := by
  induction hy generalizing b x with
  | nil y hy =>
    exact ⟨[b],.cons b hb x y [] hx ht h (.nil y hy),by simp⟩
  | cons c hc y z bs hy hs hyz hz ih =>
    obtain ⟨hcbs,hbs'⟩ := List.pairwise_cons.mp hbs
    have hxy : C.target n x = C.source n y := by
      rw [C.join_source_le n n y z le_rfl hyz] at h
      exact h
    by_cases hbc : A.orderRank c < A.orderRank b
    · refine ⟨b::c::bs,.cons b hb x (C.join n y z) (c::bs) hx ht h
        (.cons c hc y z bs hy hs hyz hz),List.pairwise_cons.mpr ⟨?_,hbs⟩⟩
      intro t hmem
      rcases List.mem_cons.mp hmem with rfl | hmem
      · exact hbc
      · exact (hcbs t hmem).trans hbc
    · have hne : b ≠ c := by
        have hp := AtomPath.cons (A := A) (F := F) b hb x (C.join n y z) (c::bs) hx ht h
          (.cons c hc y z bs hy hs hyz hz)
        have hn := (List.nodup_cons.mp hp.nodup).1
        intro heq
        apply hn
        simp [heq]
      have hlt : A.orderRank b < A.orderRank c := by
        have hh : A.orderRank b ≠ A.orderRank c := fun heq => hne (A.orderRank_injective heq)
        omega
      obtain ⟨y',x',hy',hx',hty',htx',hyx',heq⟩ := hex b c hb hc hlt x y hx hy ht hs hxy
      have hxz : C.target n x' = C.source n z := by
        have ht₀ := congrArg (C.target n) heq
        rw [C.join_target_le n n x y le_rfl hxy,
          C.join_target_le n n y' x' le_rfl hyx'] at ht₀
        exact ht₀.symm.trans hyz
      obtain ⟨cs,hcs,hsorted⟩ := ih hbs' b hb x' hx' htx' hxz
      have hm : C.target n y' = C.source n (C.join n x' z) := by
        rw [C.join_source_le n n x' z le_rfl hxz]
        exact hyx'
      have hperm : cs.Perm (b::bs) := hcs.perm_of_image_eq
        (.cons b hb x' z bs hx' htx' hxz hz) rfl
      have hsame : C.join n x (C.join n y z) = C.join n y' (C.join n x' z) := by
        rw [← C.join_assoc n x y z hxy hyz,heq,C.join_assoc n y' x' z hyx' hxz]
      refine ⟨c::cs,?_,List.pairwise_cons.mpr ⟨?_,hsorted⟩⟩
      · rw [hsame]
        exact .cons c hc y' (C.join n x' z) cs hy' hty' hm hcs
      · intro t hmem
        have hh := hperm.mem_iff.mp hmem
        rcases List.mem_cons.mp hh with rfl | hh
        · exact hlt
        · exact hcbs t hh

lemma sorted (hex : A.HasAdjacentExchange F n)
    {bs : List A.Index} {x : C.Cell} (hx : A.AtomPath F n bs x) :
    ∃ cs : List A.Index, A.AtomPath F n cs x ∧
      cs.Pairwise (fun b c => A.orderRank c < A.orderRank b) := by
  induction hx with
  | nil x hx => exact ⟨[],.nil x hx,by simp⟩
  | cons b hb x y bs hx ht h hy ih =>
    obtain ⟨cs,hcs,hs⟩ := ih
    exact hcs.insert_sorted hex hs b hb x hx ht h

lemma eq_of_exchange
    (hn : ∀ x y : C.Cell, C.source n x = x → C.source n y = y → F.map x = F.map y → x = y)
    (hw : A.WhiskerFaithful F n) (hex : A.HasAdjacentExchange F n)
    {bs cs : List A.Index} {x y : C.Cell}
    (hx : A.AtomPath F n bs x) (hy : A.AtomPath F n cs y)
    (he : F.map x = F.map y) : x = y := by
  obtain ⟨bs,hbs,hs⟩ := hx.sorted hex
  obtain ⟨cs,hcs,ht⟩ := hy.sorted hex
  exact hbs.eq_of_sorted hn hw hcs hs ht he

end AtomPath

lemma onCells_injective_of_exchange (n : ℕ)
    (hn : Function.Injective (F.onCells n))
    (hgen : ∀ x : C.Cell, C.source (n+1) x = x →
      C.TopSequence n (A.TopGenerator F n) x)
    (hw : A.WhiskerFaithful F n) (hex : A.HasAdjacentExchange F n) :
    Function.Injective (F.onCells (n+1)) := by
  intro x y he
  obtain ⟨bs,hbs⟩ := A.topSequence_path F (hgen x.val x.property)
  obtain ⟨cs,hcs⟩ := A.topSequence_path F (hgen y.val y.property)
  apply Subtype.ext
  apply hbs.eq_of_exchange ?_ hw hex hcs (congrArg Subtype.val he)
  intro a b ha hb he
  exact congrArg Subtype.val (hn (a₁ := ⟨a,ha⟩) (a₂ := ⟨b,hb⟩) (Subtype.ext he))
end Thomason.DirectedComplex.RankedAtoms

end

end OAI
end

section
-- module Solutions.OAIQ043_TH.Thomason_RankedFaithfulness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Ranked Faithfulness. -/

noncomputable section
universe u v w z


namespace Thomason.DirectedComplex.RankedAtoms
open Table OmegaCategory
variable {K : DirectedComplex.{u}} (A : RankedAtoms.{u,v} K)
variable {C : OmegaCategory.{w}} (F : OmegaCategory.Functor C K.nu)

lemma table_rank_split (n : ℕ) (s : ℤ) (x : Table K)
    (hx : truncate (n+1) false x = x) :
    ∃ l r : Table K, ∃ h : truncate n true l = truncate n false r,
      truncate (n+1) false l = l ∧ truncate (n+1) false r = r ∧
      (∀ b, A.coefficient b (n+1) (l.row (n+1) false) ≠ 0 → s < A.rank b) ∧
      (∀ b, A.coefficient b (n+1) (r.row (n+1) false) ≠ 0 → ¬s < A.rank b) ∧
      x = comp n l r h := by
  let c := A.cut (n+1) (x.row (n+1) false) (fun b => s < A.rank b)
  let d := A.cut (n+1) (x.row (n+1) false) (fun b => ¬s < A.rank b)
  have hp := (A.rank_cut_positive n s 0 0 (x.row n false) (x.row n true) _
    (K.positive n).zero_mem (K.positive n).zero_mem
    (x.positive n false) (x.positive n true) (x.positive (n+1) false)
    (by simp) (by simp) (by rw [sub_zero,zero_add,x.boundary])).1
  obtain ⟨l,r,h,hl,hr,hlt,hrt,he⟩ := split_top x hx c d
    (A.cut_positive _ _ (x.positive _ _) _) (A.cut_positive _ _ (x.positive _ _) _)
    (A.cut_add_complement _ _ _) hp
  refine ⟨l,r,h,hl,hr,?_,?_,he.symm⟩
  · intro b hb
    rw [hlt,A.coefficient_cut] at hb
    by_contra hn
    exact hb (ite_eq_right hn)
  · intro b hb
    rw [hrt,A.coefficient_cut] at hb
    by_contra hn
    exact hb (ite_eq_right (not_not_intro hn))

lemma rank_split (n : ℕ) (s : ℤ)
    (hinj : Function.Injective (F.onCells n))
    (hbij : Function.Bijective (F.onCells (n+1))) (x : C.Cell)
    (hx : C.source (n+1) x = x) :
    ∃ l r : C.Cell, C.source (n+1) l = l ∧ C.source (n+1) r = r ∧
      C.target n l = C.source n r ∧
      (∀ b, A.coefficient b (n+1) ((F.map l).row (n+1) false) ≠ 0 → s < A.rank b) ∧
      (∀ b, A.coefficient b (n+1) ((F.map r).row (n+1) false) ≠ 0 → ¬s < A.rank b) ∧
      x = C.join n l r := by
  obtain ⟨l,r,h,hl,hr,hlo,hro,he⟩ := A.table_rank_split n s (F.map x)
    ((F.map_source (n+1) x).symm.trans (congrArg F.map hx))
  obtain ⟨l',hl'⟩ := hbij.2 ⟨l,hl⟩
  obtain ⟨r',hr'⟩ := hbij.2 ⟨r,hr⟩
  have hfl : F.map l'.val = l := congrArg Subtype.val hl'
  have hfr : F.map r'.val = r := congrArg Subtype.val hr'
  have hm : C.target n l'.val = C.source n r'.val := by
    apply F.bounded_ext n hinj _ _ (C.source_target_self n _) (C.source_source_self n _)
    rw [F.map_target,F.map_source,hfl,hfr]
    exact h
  refine ⟨l'.val,r'.val,l'.property,r'.property,hm,?_,?_,?_⟩
  · simpa only [hfl] using hlo
  · simpa only [hfr] using hro
  · apply F.bounded_ext (n+1) hbij.1 _ _ hx
      (by rw [C.join_source_gt (n+1) n _ _ (Nat.lt_succ_self n) hm,l'.property,r'.property])
    rw [F.map_join n _ _ hm,hfl,hfr,K.nu.join_eq n l r h]
    exact he

lemma rank_split_unique (n : ℕ) (s : ℤ)
    (hinj : Function.Injective (F.onCells (n+1))) (l r l' r' : C.Cell)
    (hl : C.source (n+1) l = l) (hr : C.source (n+1) r = r)
    (hl' : C.source (n+1) l' = l') (hr' : C.source (n+1) r' = r')
    (h : C.target n l = C.source n r) (h' : C.target n l' = C.source n r')
    (hlo : ∀ b, A.coefficient b (n+1) ((F.map l).row (n+1) false) ≠ 0 → s < A.rank b)
    (hro : ∀ b, A.coefficient b (n+1) ((F.map r).row (n+1) false) ≠ 0 → ¬s < A.rank b)
    (hlo' : ∀ b, A.coefficient b (n+1) ((F.map l').row (n+1) false) ≠ 0 → s < A.rank b)
    (hro' : ∀ b, A.coefficient b (n+1) ((F.map r').row (n+1) false) ≠ 0 → ¬s < A.rank b)
    (he : C.join n l r = C.join n l' r') : l = l' ∧ r = r' := by
  have het := congrArg (fun x => (F.map x).row (n+1) false) he
  rw [top_row_join F (n+1) n (Nat.lt_succ_self n) l r h,
    top_row_join F (n+1) n (Nat.lt_succ_self n) l' r' h'] at het
  obtain ⟨hls,hrs⟩ := OrderedWhisker.split_unique (A := A) (n+1) s _ _ _ _ hlo hlo' hro hro' het
  have hf (x : C.Cell) (hx : C.source (n+1) x = x) : truncate (n+1) false (F.map x) = F.map x :=
    (F.map_source (n+1) x).symm.trans (congrArg F.map hx)
  constructor
  · apply F.bounded_ext (n+1) hinj l l' hl hl'
    apply top_and_source_ext n _ _ (hf l hl) (hf l' hl') hls
    have hh := congrArg (fun x => F.map (C.source n x)) he
    rw [C.join_source_le n n l r le_rfl h,C.join_source_le n n l' r' le_rfl h',
      F.map_source,F.map_source] at hh
    exact hh
  · apply F.bounded_ext (n+1) hinj r r' hr hr'
    apply top_and_target_ext n _ _ (hf r hr) (hf r' hr') hrs
    have hh := congrArg (fun x => F.map (C.target n x)) he
    rw [C.join_target_le n n l r le_rfl h,C.join_target_le n n l' r' le_rfl h',
      F.map_target,F.map_target] at hh
    exact hh
end Thomason.DirectedComplex.RankedAtoms

end

noncomputable section
universe u v w z


namespace Thomason.DirectedComplex.RankedAtoms
open Table OmegaCategory
variable {K : DirectedComplex.{u}} (A : RankedAtoms.{u,v} K)
variable {C : OmegaCategory.{w}} (F : OmegaCategory.Functor C K.nu)

lemma support_add (p : ℕ) (P : A.Index → Prop) (x y : K.Chain p)
    (hx : ∀ b, A.coefficient b p x ≠ 0 → P b)
    (hy : ∀ b, A.coefficient b p y ≠ 0 → P b) :
    ∀ b, A.coefficient b p (x+y) ≠ 0 → P b := by
  intro b hb
  rw [map_add] at hb
  by_cases h : A.coefficient b p x = 0
  · exact hy b (by simpa only [h,zero_add] using hb)
  · exact hx b h

lemma layered_row_above (b : A.Index) {n : ℕ} {x : C.Cell}
    (hx : C.LayeredWhisker (fun z => F.map z = A.atom b) n x)
    (p : ℕ) (hp : n < p) (e : Bool) : (F.map x).row p e = (A.atom b).row p e := by
  induction n generalizing x with
  | zero => change F.map x = A.atom b at hx; rw [hx]
  | succ n ih =>
    obtain ⟨l,m,r,hl,hr,hm,hlm,hmr,rfl⟩ := hx
    have hf (a : C.Cell) (ha : C.source (n+1) a = a) : (F.map a).row p e = 0 :=
      row_above_fixed (F.map a) ((F.map_source (n+1) a).symm.trans (congrArg F.map ha)) hp e
    have hpm : ¬p < n := by omega
    have hpn : p ≠ n := by omega
    have hlmr : C.target n (C.join n l m) = C.source n r := by
      rw [C.join_target_le n n l m le_rfl hlm]; exact hmr
    rw [F.map_join n _ r hlmr,K.nu.join_eq n _ _ (F.map_composable hlmr)]
    change (comp n (F.map (C.join n l m)) (F.map r) (F.map_composable hlmr)).row p e = _
    erw [comp_row]
    rw [ite_eq_right hpm,ite_eq_right hpn,F.map_join n l m hlm,
      K.nu.join_eq n _ _ (F.map_composable hlm)]
    change (comp n (F.map l) (F.map m) (F.map_composable hlm)).row p e + (F.map r).row p e = _
    erw [comp_row]
    rw [ite_eq_right hpm,ite_eq_right hpn,hf l hl,hf r hr,zero_add,add_zero]
    exact ih hm (by omega)

lemma layered_bounded (b : A.Index) (d : ℕ) (hb : A.dim b ≤ d)
    (hreflect : ∀ k x, truncate k false (F.map x) = F.map x → C.source k x = x)
    {n : ℕ} (hn : n ≤ d) {x : C.Cell}
    (hx : C.LayeredWhisker (fun z => F.map z = A.atom b) n x) : C.source d x = x := by
  apply hx.row_bounded d (fun z hz => ?_) hn
  apply hreflect d z
  rw [hz]
  exact K.nu.source_fixed_upwards hb (A.bounded b)

lemma lower_single_ordered (n : ℕ)
    (hsmall : ∀ k, k ≤ n+1 → Function.Bijective (F.onCells k))
    (hreflect : ∀ k x, truncate k false (F.map x) = F.map x → C.source k x = x)
    (b : A.Index) (hb : A.dim b = n+1) (x : C.Cell)
    (hx : C.source (n+1) x = x)
    (ht : (F.map x).row (n+1) false = A.basis (n+1) b) :
    A.OrderedWhisker F b n x := by
  have hf : truncate (n+1) false (F.map x) = F.map x :=
    (F.map_source (n+1) x).symm.trans (congrArg F.map hx)
  have hta : (F.map x).row (n+1) false = (A.atom b).row (n+1) false := by
    rw [ht,← hb,A.basis_own]
  have hay : A.OrderedWhisker (OmegaCategory.Functor.id K.nu) b n (F.map x) :=
    A.table_ordered_whisker b n (by omega) _
      (fun p hp e => NormalizedChains.rows_above_top_agree _ _ hf (hb ▸ A.bounded b) hta p (by omega) e)
  obtain ⟨a,ha⟩ := (hsmall (n+1) le_rfl).2 ⟨A.atom b,hb ▸ A.bounded b⟩
  obtain ⟨y,hy,he⟩ := OrderedWhisker.lift (A := A) (F := F) b n
    ⟨a.val,congrArg Subtype.val ha⟩ (fun k hk => hsmall k (by omega)) _ hay
  have hyb : C.source (n+1) y = y := hreflect (n+1) y (by rw [he]; exact hf)
  have hyx := F.bounded_ext (n+1) (hsmall (n+1) le_rfl).1 y x hyb hx he
  simpa only [hyx] using hy

theorem ordered_exchange (n : ℕ)
    (hsmall : ∀ k, k ≤ n → Function.Bijective (F.onCells k))
    (b c : A.Index) (hb : n < A.dim b) (hc : n < A.dim c)
    (hbc : A.rank b ≤ A.rank c) (x y : C.Cell)
    (hx : A.OrderedWhisker F b n x) (hy : A.OrderedWhisker F c n y)
    (h : C.target n x = C.source n y) :
    ∃ y' x' : C.Cell,
      C.LayeredWhisker (fun z => F.map z = A.atom c) n y' ∧
      C.LayeredWhisker (fun z => F.map z = A.atom b) n x' ∧
      C.target n y' = C.source n x' ∧ C.join n x y = C.join n y' x' := by
  cases n with
  | zero =>
    have he : truncate 0 true (A.atom b) = truncate 0 false (A.atom c) := by
      change F.map x = A.atom b at hx
      change F.map y = A.atom c at hy
      have hh := congrArg F.map h
      rw [F.map_target,F.map_source,hx,hy] at hh
      exact hh
    have hr : (A.atom b).row 0 true = (A.atom c).row 0 false := by
      have hh := congrArg (fun t : Table K => t.row 0 false) he
      simpa using hh
    have hm : A.mass 0 ((A.atom c).row 0 false) = 1 := by
      rw [← A.augmentation_eq_mass,(A.atom c).augmentation]
    obtain ⟨t,ht⟩ : ∃ t, A.coefficient t 0 ((A.atom c).row 0 false) ≠ 0 := by
      by_contra hn
      push Not at hn
      have hz : (A.atom c).row 0 false = 0 := A.ext 0 _ 0 (by simpa using hn)
      rw [hz,map_zero] at hm
      omega
    have ht' : A.coefficient t 0 ((A.atom b).row 0 true) ≠ 0 := by rwa [hr]
    have h₁ := A.ranked b 0 hb true t ht'
    have h₂ := A.ranked c 0 hc false t ht
    simp only [ite_true,Bool.false_eq_true,ite_false] at h₁ h₂
    omega
  | succ n =>
    obtain ⟨l,m,r,hl,hr,hm,hlm,hmr,hlo,hro,rfl⟩ := hx
    obtain ⟨a,z,d,ha,hd,hz,haz,hzd,hao,hdo,rfl⟩ := hy
    obtain ⟨dH,dL,hdH,hdL,hdHL,hdHo,hdLo,heD⟩ :=
      A.rank_split F n (A.rank b) (hsmall n (by omega)).1 (hsmall (n+1) le_rfl) d hd
    have hlmr : C.target n (C.join n l m) = C.source n r := by
      rw [C.join_target_le n n l m le_rfl hlm]; exact hmr
    have hazd : C.target n (C.join n a z) = C.source n d := by
      rw [C.join_target_le n n a z le_rfl haz]; exact hzd
    have hzH : C.target n z = C.source n dH := by
      rw [heD,C.join_source_le n n dH dL le_rfl hdHL] at hzd; exact hzd
    have hazH : C.target n (C.join n a z) = C.source n dH := by
      rw [C.join_target_le n n a z le_rfl haz]; exact hzH
    let X := C.join n m r
    let Y := C.join n (C.join n a z) dH
    have hlX : C.target n l = C.source n X := by
      dsimp [X]; rw [C.join_source_le n n m r le_rfl hmr]; exact hlm
    have hYL : C.target n Y = C.source n dL := by
      dsimp [Y]; rw [C.join_target_le n n _ dH le_rfl hazH]; exact hdHL
    have hxform : C.join n (C.join n l m) r = C.join n l X :=
      C.join_assoc n l m r hlm hmr
    have hyform : C.join n (C.join n a z) d = C.join n Y dL := by
      rw [heD]
      exact (C.join_assoc n (C.join n a z) dH dL hazH hdHL).symm
    rw [hxform,hyform,C.join_target_gt (n+1) n l X (Nat.lt_succ_self n) hlX,
      C.join_source_gt (n+1) n Y dL (Nat.lt_succ_self n) hYL,
      C.target_eq_self_of_source_eq_self hl,hdL] at h
    have hlTX : C.target n l = C.source n (C.target (n+1) X) := by
      rw [C.source_target,ite_eq_left (Nat.lt_succ_self n)]; exact hlX
    have hSYL : C.target n (C.source (n+1) Y) = C.source n dL := by
      rw [C.target_source,ite_eq_left (Nat.lt_succ_self n)]; exact hYL
    have hf (t : C.Cell) (ht : C.source (n+1) t = t) :
        (F.map t).row (n+1) true = (F.map t).row (n+1) false :=
      (row_top_fixed (F.map t) ((F.map_source (n+1) t).symm.trans (congrArg F.map ht))).symm
    have hTX : ∀ t, A.coefficient t (n+1) ((F.map (C.target (n+1) X)).row (n+1) false) ≠ 0 →
        ¬ A.rank b < A.rank t := by
      rw [F.map_target]
      change ∀ t, A.coefficient t (n+1) ((truncate (n+1) true (F.map X)).row (n+1) false) ≠ 0 → _
      erw [truncate_row]
      simp only [lt_self_iff_false,ite_false,ite_true]
      dsimp [X]
      rw [F.map_join n m r hmr,K.nu.join_eq n _ _ (F.map_composable hmr)]
      change ∀ t, A.coefficient t (n+1) ((comp n (F.map m) (F.map r) (F.map_composable hmr)).row (n+1) true) ≠ 0 → _
      erw [comp_row]
      simp only [show ¬n+1 < n by omega,show n+1 ≠ n by omega,ite_false]
      rw [hm.row_above (n+1) (Nat.lt_succ_self n) true,hf r hr]
      apply A.support_add (n+1) _ _ _ ?_ hro
      intro t ht
      have hh := A.ranked b (n+1) hb true t ht
      simp only [ite_true] at hh
      omega
    have hSY : ∀ t, A.coefficient t (n+1) ((F.map (C.source (n+1) Y)).row (n+1) false) ≠ 0 →
        A.rank b < A.rank t := by
      rw [F.map_source]
      change ∀ t, A.coefficient t (n+1) ((truncate (n+1) false (F.map Y)).row (n+1) false) ≠ 0 → _
      erw [truncate_row]
      simp only [lt_self_iff_false,ite_false,ite_true]
      dsimp [Y]
      rw [top_row_join F (n+1) n (Nat.lt_succ_self n) _ dH hazH,
        top_row_join F (n+1) n (Nat.lt_succ_self n) a z haz,
        hz.row_above (n+1) (Nat.lt_succ_self n) false]
      apply A.support_add (n+1) _ _ _ (A.support_add (n+1) _ _ _ ?_ ?_) hdHo
      · intro t ht; exact hbc.trans_lt (hao t ht)
      · intro t ht
        have hh := A.ranked c (n+1) hc false t ht
        simp only [Bool.false_eq_true,ite_false] at hh
        exact hbc.trans_lt hh
    obtain ⟨hlY,hXL⟩ := A.rank_split_unique F n (A.rank b) (hsmall (n+1) le_rfl).1
      l (C.target (n+1) X) (C.source (n+1) Y) dL hl (C.source_target_self (n+1) X)
      (C.source_source_self (n+1) Y) hdL hlTX hSYL hlo hTX hSY hdLo h
    have hYX : C.target n Y = C.source n X := by
      rw [hlY,C.target_source,ite_eq_left (Nat.lt_succ_self n)] at hlX; exact hlX
    have hYS : C.target n Y = C.source n (C.source (n+1) X) := by
      rw [C.source_source,min_eq_left (Nat.le_succ n)]; exact hYX
    have hTYX : C.target n (C.target (n+1) Y) = C.source n X := by
      rw [C.target_target,min_eq_left (Nat.le_succ n)]; exact hYX
    have hTYm : C.target n (C.target (n+1) Y) = C.source n m := by
      rw [C.join_source_le n n m r le_rfl hmr] at hTYX; exact hTYX
    have hHS : C.target n dH = C.source n (C.source (n+1) X) := by
      dsimp [Y] at hYS
      rw [C.join_target_le n n _ dH le_rfl hazH] at hYS; exact hYS
    let y' := C.join n Y (C.source (n+1) X)
    let x' := C.join n (C.target (n+1) Y) X
    have hy' : C.LayeredWhisker (fun t => F.map t = A.atom c) (n+1) y' := by
      refine ⟨a,z,C.join n dH (C.source (n+1) X),ha,?_,hz.layered,haz,?_,?_⟩
      · rw [C.join_source_gt (n+1) n _ _ (Nat.lt_succ_self n) hHS,hdH,C.source_source_self]
      · rw [C.join_source_le n n _ _ le_rfl hHS]; exact hzH
      · exact C.join_assoc n (C.join n a z) dH (C.source (n+1) X) hazH hHS
    have hx' : C.LayeredWhisker (fun t => F.map t = A.atom b) (n+1) x' := by
      refine ⟨C.target (n+1) Y,m,r,C.source_target_self (n+1) Y,hr,hm.layered,hTYm,hmr,?_⟩
      exact (C.join_assoc n (C.target (n+1) Y) m r hTYm hmr).symm
    have hyx' : C.target (n+1) y' = C.source (n+1) x' := by
      dsimp [y',x']
      rw [C.join_target_gt (n+1) n _ _ (Nat.lt_succ_self n) hYS,
        C.join_source_gt (n+1) n _ _ (Nat.lt_succ_self n) hTYX,
        C.source_target_self,C.target_source_self]
    have he₁ := C.join_interchange n (n+1) (Nat.lt_succ_self n)
      (C.source (n+1) Y) Y X (C.target (n+1) X)
      (C.target_source_self (n+1) Y) (C.source_target_self (n+1) X).symm
      (by rw [C.target_source,ite_eq_left (Nat.lt_succ_self n)]; exact hYX)
      (by rw [C.source_target,ite_eq_left (Nat.lt_succ_self n)]; exact hYX)
    rw [C.join_left_unit (n+1) _ Y (C.source_source_self (n+1) Y)
      (C.target_source_self (n+1) Y),C.join_right_unit (n+1) X _
      (C.source_target_self (n+1) X) (C.source_target_self (n+1) X).symm] at he₁
    have he₂ := C.join_interchange n (n+1) (Nat.lt_succ_self n)
      Y (C.target (n+1) Y) (C.source (n+1) X) X
      (C.source_target_self (n+1) Y).symm (C.target_source_self (n+1) X) hYS hTYX
    rw [C.join_right_unit (n+1) Y _ (C.source_target_self (n+1) Y)
      (C.source_target_self (n+1) Y).symm,C.join_left_unit (n+1) _ X
      (C.source_source_self (n+1) X) (C.target_source_self (n+1) X)] at he₂
    refine ⟨y',x',hy',hx',hyx',?_⟩
    rw [hxform,hyform,hlY,← hXL]
    exact he₁.symm.trans he₂
end Thomason.DirectedComplex.RankedAtoms

end

noncomputable section
universe u v w z


namespace Thomason.DirectedComplex.RankedAtoms
open Table OmegaCategory
variable {K : DirectedComplex.{u}} (A : RankedAtoms.{u,v} K)
variable {C : OmegaCategory.{w}} (F : OmegaCategory.Functor C K.nu)

namespace AtomPath
variable {A F} {n : ℕ}

lemma index_support {bs : List A.Index} {a : C.Cell} (ha : A.AtomPath F n bs a)
    (P : A.Index → Prop)
    (hs : ∀ c, A.coefficient c (n+1) ((F.map a).row (n+1) false) ≠ 0 → P c) :
    ∀ c ∈ bs, P c := by
  classical
  intro c hc
  apply hs c
  rw [ha.coefficient c]
  exact_mod_cast (ne_of_gt (List.count_pos_iff.mpr hc))

lemma move_low (n : ℕ)
    (hsmall : ∀ k, k ≤ n+1 → Function.Bijective (F.onCells k))
    (hreflect : ∀ k x, truncate k false (F.map x) = F.map x → C.source k x = x)
    (b : A.Index) (hb : n < A.dim b)
    (hnorm : ∀ z, C.LayeredWhisker (fun t => F.map t = A.atom b) n z → A.OrderedWhisker F b n z)
    {bs : List A.Index} {a : C.Cell} (ha : A.AtomPath F n bs a)
    (hs : ∀ c ∈ bs, A.rank c ≤ A.rank b) (x : C.Cell)
    (hx : A.OrderedWhisker F b n x) (h : C.target n a = C.source n x) :
    ∃ y a' : C.Cell, A.OrderedWhisker F b n y ∧ C.source (n+1) a' = a' ∧
      (F.map a').row (n+1) false = (F.map a).row (n+1) false ∧
      C.target n y = C.source n a' ∧ C.join n a x = C.join n y a' := by
  induction ha generalizing x with
  | nil a ha =>
    refine ⟨x,C.target n x,hx,C.source_fixed_upwards (Nat.le_succ n) (C.source_target_self n x),?_,
      (C.source_target_self n x).symm,?_⟩
    · rw [top_row_lower F n a ha,top_row_lower F n _ (C.source_target_self n x)]
    · rw [C.join_left_unit n a x ha h,C.join_right_unit n x _ (C.source_target_self n x)
        (C.source_target_self n x).symm]
  | cons c hc z a bs hz ht hza ha ih =>
    have hax : C.target n a = C.source n x := by
      rw [C.join_target_le n n z a le_rfl hza] at h; exact h
    obtain ⟨y,a',hy,ha',hat,hya',he⟩ := ih (fun t ht => hs t (List.mem_cons_of_mem c ht)) x hx hax
    have hzy : C.target n z = C.source n y := by
      have hh := congrArg (C.source n) he
      rw [C.join_source_le n n a x le_rfl hax,C.join_source_le n n y a' le_rfl hya'] at hh
      exact hza.trans hh
    have hzo := A.lower_single_ordered F n hsmall hreflect c hc z hz.bounded ht
    obtain ⟨y',z',hy',hz',hyz',hez⟩ := A.ordered_exchange F n
      (fun k hk => hsmall k (by omega)) c b (by omega) hb (hs c (List.mem_cons_self)) z y hzo hy hzy
    have hz'b := A.layered_bounded F c (n+1) hc.le hreflect (Nat.le_succ n) hz'
    have hz't : (F.map z').row (n+1) false = (F.map z).row (n+1) false := by
      rw [A.layered_row_above F c hz' (n+1) (Nat.lt_succ_self n) false,ht,← hc,A.basis_own]
    have hz'a' : C.target n z' = C.source n a' := by
      have hh := congrArg (C.target n) hez
      rw [C.join_target_le n n z y le_rfl hzy,C.join_target_le n n y' z' le_rfl hyz'] at hh
      exact hh.symm.trans hya'
    have hym : C.target n y' = C.source n (C.join n z' a') := by
      rw [C.join_source_le n n z' a' le_rfl hz'a']; exact hyz'
    refine ⟨y',C.join n z' a',hnorm y' hy',?_,?_,hym,?_⟩
    · rw [C.join_source_gt (n+1) n z' a' (Nat.lt_succ_self n) hz'a',hz'b,ha']
    · rw [top_row_join F (n+1) n (Nat.lt_succ_self n) z' a' hz'a',
        top_row_join F (n+1) n (Nat.lt_succ_self n) z a hza,hz't,hat]
    · rw [C.join_assoc n z a x hza hax,he,← C.join_assoc n z y a' hzy hya',hez,
        C.join_assoc n y' z' a' hyz' hz'a']

lemma move_high (n : ℕ)
    (hsmall : ∀ k, k ≤ n+1 → Function.Bijective (F.onCells k))
    (hreflect : ∀ k x, truncate k false (F.map x) = F.map x → C.source k x = x)
    (b : A.Index) (hb : n < A.dim b)
    (hnorm : ∀ z, C.LayeredWhisker (fun t => F.map t = A.atom b) n z → A.OrderedWhisker F b n z)
    {bs : List A.Index} {a : C.Cell} (ha : A.AtomPath F n bs a)
    (hs : ∀ c ∈ bs, A.rank b < A.rank c) (x : C.Cell)
    (hx : A.OrderedWhisker F b n x) (h : C.target n x = C.source n a) :
    ∃ a' y : C.Cell, C.source (n+1) a' = a' ∧ A.OrderedWhisker F b n y ∧
      (F.map a').row (n+1) false = (F.map a).row (n+1) false ∧
      C.target n a' = C.source n y ∧ C.join n x a = C.join n a' y := by
  induction ha generalizing x with
  | nil a ha =>
    refine ⟨C.source n x,x,C.source_fixed_upwards (Nat.le_succ n) (C.source_source_self n x),hx,?_,
      C.target_source_self n x,?_⟩
    · rw [top_row_lower F n a ha,top_row_lower F n _ (C.source_source_self n x)]
    · rw [C.join_right_unit n x a ha h,C.join_left_unit n _ x (C.source_source_self n x)
        (C.target_source_self n x)]
  | cons c hc z a bs hz ht hza ha ih =>
    have hxz : C.target n x = C.source n z := by
      rw [C.join_source_le n n z a le_rfl hza] at h; exact h
    have hzo := A.lower_single_ordered F n hsmall hreflect c hc z hz.bounded ht
    obtain ⟨z',x',hz',hx',hzx',hez⟩ := A.ordered_exchange F n
      (fun k hk => hsmall k (by omega)) b c hb (by omega) (hs c (List.mem_cons_self)).le x z hx hzo hxz
    have hz'b := A.layered_bounded F c (n+1) hc.le hreflect (Nat.le_succ n) hz'
    have hz't : (F.map z').row (n+1) false = (F.map z).row (n+1) false := by
      rw [A.layered_row_above F c hz' (n+1) (Nat.lt_succ_self n) false,ht,← hc,A.basis_own]
    have hx'a : C.target n x' = C.source n a := by
      have hh := congrArg (C.target n) hez
      rw [C.join_target_le n n x z le_rfl hxz,C.join_target_le n n z' x' le_rfl hzx'] at hh
      exact hh.symm.trans hza
    obtain ⟨a',y,ha',hy,hat,ha'y,he⟩ := ih (fun t ht => hs t (List.mem_cons_of_mem c ht)) x'
      (hnorm x' hx') hx'a
    have hz'a' : C.target n z' = C.source n a' := by
      have hh := congrArg (C.source n) he
      rw [C.join_source_le n n x' a le_rfl hx'a,C.join_source_le n n a' y le_rfl ha'y] at hh
      exact hzx'.trans hh
    have hmy : C.target n (C.join n z' a') = C.source n y := by
      rw [C.join_target_le n n z' a' le_rfl hz'a']; exact ha'y
    refine ⟨C.join n z' a',y,?_,hy,?_,hmy,?_⟩
    · rw [C.join_source_gt (n+1) n z' a' (Nat.lt_succ_self n) hz'a',hz'b,ha']
    · rw [top_row_join F (n+1) n (Nat.lt_succ_self n) z' a' hz'a',
        top_row_join F (n+1) n (Nat.lt_succ_self n) z a hza,hz't,hat]
    · rw [← C.join_assoc n x z a hxz hza,hez,C.join_assoc n z' x' a hzx' hx'a,he,
        ← C.join_assoc n z' a' y hz'a' ha'y]

end AtomPath
end Thomason.DirectedComplex.RankedAtoms

end

noncomputable section
universe u v w z


namespace Thomason.DirectedComplex.RankedAtoms
open Table OmegaCategory
variable {K : DirectedComplex.{u}} (A : RankedAtoms.{u,v} K)
variable {C : OmegaCategory.{w}} (F : OmegaCategory.Functor C K.nu)

theorem layered_ordered (n : ℕ)
    (hsmall : ∀ k, k ≤ n → Function.Bijective (F.onCells k))
    (hgen : ∀ k, k < n → ∀ a : C.Cell, C.source (k+1) a = a →
      C.TopSequence k (A.TopGenerator F k) a)
    (hreflect : ∀ k x, truncate k false (F.map x) = F.map x → C.source k x = x)
    (b : A.Index) (hb : n < A.dim b) (x : C.Cell)
    (hx : C.LayeredWhisker (fun t => F.map t = A.atom b) n x) :
    A.OrderedWhisker F b n x := by
  induction n generalizing x with
  | zero => exact hx
  | succ n ih =>
    have hnorm : ∀ z, C.LayeredWhisker (fun t => F.map t = A.atom b) n z →
        A.OrderedWhisker F b n z :=
      fun z hz => ih (fun k hk => hsmall k (by omega))
        (fun k hk => hgen k (by omega)) (by omega) z hz
    obtain ⟨l,m,r,hl,hr,hm,hlm,hmr,rfl⟩ := hx
    obtain ⟨lH,lL,hlH,hlL,hlHL,hlHo,hlLo,heL⟩ :=
      A.rank_split F n (A.rank b) (hsmall n (by omega)).1 (hsmall (n+1) le_rfl) l hl
    have hLm : C.target n lL = C.source n m := by
      rw [heL,C.join_target_le n n lH lL le_rfl hlHL] at hlm; exact hlm
    obtain ⟨bs,hbs⟩ := A.topSequence_path F (hgen n (Nat.lt_succ_self n) lL hlL)
    have hbslo : ∀ c ∈ bs, A.rank c ≤ A.rank b :=
      hbs.index_support _ (fun c hc => le_of_not_gt (hlLo c hc))
    obtain ⟨m₁,aLow,hm₁,haLow,hatLow,hm₁a,heLow⟩ :=
      hbs.move_low n hsmall hreflect b (by omega) hnorm hbslo m (hnorm m hm) hLm
    have hHm₁ : C.target n lH = C.source n m₁ := by
      have hh := congrArg (C.source n) heLow
      rw [C.join_source_le n n lL m le_rfl hLm,
        C.join_source_le n n m₁ aLow le_rfl hm₁a] at hh
      exact hlHL.trans hh
    have haLowr : C.target n aLow = C.source n r := by
      have hh := congrArg (C.target n) heLow
      rw [C.join_target_le n n lL m le_rfl hLm,
        C.join_target_le n n m₁ aLow le_rfl hm₁a] at hh
      exact hh.symm.trans hmr
    have har : C.source (n+1) (C.join n aLow r) = C.join n aLow r := by
      rw [C.join_source_gt (n+1) n aLow r (Nat.lt_succ_self n) haLowr,haLow,hr]
    obtain ⟨rH,rL,hrH,hrL,hrHL,hrHo,hrLo,heR⟩ :=
      A.rank_split F n (A.rank b) (hsmall n (by omega)).1 (hsmall (n+1) le_rfl) _ har
    have hm₁H : C.target n m₁ = C.source n rH := by
      have hh := congrArg (C.source n) heR
      rw [C.join_source_le n n aLow r le_rfl haLowr,
        C.join_source_le n n rH rL le_rfl hrHL] at hh
      exact hm₁a.trans hh
    obtain ⟨cs,hcs⟩ := A.topSequence_path F (hgen n (Nat.lt_succ_self n) rH hrH)
    have hcshi : ∀ c ∈ cs, A.rank b < A.rank c := hcs.index_support _ hrHo
    obtain ⟨aHigh,m₂,haHigh,hm₂,hatHigh,ham₂,heHigh⟩ :=
      hcs.move_high n hsmall hreflect b (by omega) hnorm hcshi m₁ hm₁ hm₁H
    have hHaHigh : C.target n lH = C.source n aHigh := by
      have hh := congrArg (C.source n) heHigh
      rw [C.join_source_le n n m₁ rH le_rfl hm₁H,
        C.join_source_le n n aHigh m₂ le_rfl ham₂] at hh
      exact hHm₁.trans hh
    have hm₂L : C.target n m₂ = C.source n rL := by
      have hh := congrArg (C.target n) heHigh
      rw [C.join_target_le n n m₁ rH le_rfl hm₁H,
        C.join_target_le n n aHigh m₂ le_rfl ham₂] at hh
      exact hh.symm.trans hrHL
    refine ⟨C.join n lH aHigh,m₂,rL,?_,hrL,hm₂,?_,hm₂L,?_,hrLo,?_⟩
    · rw [C.join_source_gt (n+1) n lH aHigh (Nat.lt_succ_self n) hHaHigh,hlH,haHigh]
    · rw [C.join_target_le n n lH aHigh le_rfl hHaHigh]; exact ham₂
    · rw [top_row_join F (n+1) n (Nat.lt_succ_self n) lH aHigh hHaHigh,hatHigh]
      exact A.support_add (n+1) _ _ _ hlHo hrHo
    · have hHma : C.target n (C.join n lH m₁) = C.source n aLow := by
        rw [C.join_target_le n n lH m₁ le_rfl hHm₁]; exact hm₁a
      have hHmH : C.target n (C.join n lH m₁) = C.source n rH := by
        rw [C.join_target_le n n lH m₁ le_rfl hHm₁]; exact hm₁H
      rw [heL,C.join_assoc n lH lL m hlHL hLm,heLow,
        ← C.join_assoc n lH m₁ aLow hHm₁ hm₁a,
        C.join_assoc n (C.join n lH m₁) aLow r hHma haLowr,heR,
        ← C.join_assoc n (C.join n lH m₁) rH rL hHmH hrHL,
        C.join_assoc n lH m₁ rH hHm₁ hm₁H,heHigh,
        ← C.join_assoc n lH aHigh m₂ hHaHigh ham₂]
end Thomason.DirectedComplex.RankedAtoms

end

noncomputable section
universe u v w z


namespace Thomason.OmegaCategory
variable {C : OmegaCategory.{u}}
lemma Whisker.mono {n : ℕ} {G H : C.Cell → Prop} {x : C.Cell}
    (hx : C.Whisker n G x) (h : ∀ z, G z → H z) : C.Whisker n H x := by
  induction hx with
  | generator z hz hd => exact .generator z (h z hz) hd
  | left k hk a z ha hm hz ih => exact .left k hk a z ha hm ih
  | right k hk z a ha hm hz ih => exact .right k hk z a ha hm ih
end Thomason.OmegaCategory

end

noncomputable section
universe u v w z


namespace Thomason.DirectedComplex.RankedAtoms
open Table OmegaCategory
variable {K : DirectedComplex.{u}} (A : RankedAtoms.{u,v} K)
variable {C : OmegaCategory.{w}} (F : OmegaCategory.Functor C K.nu)

lemma basis_injective_on_dim (p : ℕ) (b c : A.Index)
    (hb : A.dim b = p) (hc : A.dim c = p) (he : A.basis p b = A.basis p c) : b = c := by
  classical
  by_contra hne
  have hh := congrArg (A.coefficient b p) he
  simp [A.coefficient_basis,hb,hc,Ne.symm hne] at hh

lemma whisker_atom_layered {n : ℕ} {x : C.Cell}
    (hx : C.Whisker n (A.TopGenerator F n) x) :
    ∃ b, A.dim b = n+1 ∧ C.LayeredWhisker (fun z => F.map z = A.atom b) n x := by
  induction hx with
  | generator x hx hd =>
    obtain ⟨b,hb,he⟩ := hx
    exact ⟨b,hb,LayeredWhisker.of_generator he n⟩
  | left k hk a x ha hm hx ih =>
    obtain ⟨b,hb,hh⟩ := ih
    exact ⟨b,hb,hh.left k hk a ha hm⟩
  | right k hk x a ha hm hx ih =>
    obtain ⟨b,hb,hh⟩ := ih
    exact ⟨b,hb,hh.right k hk a ha hm⟩

lemma whisker_layered_of_top (n : ℕ) (b : A.Index) (hb : A.dim b = n+1)
    (x : C.Cell) (hx : C.Whisker n (A.TopGenerator F n) x)
    (ht : (F.map x).row (n+1) false = A.basis (n+1) b) :
    C.LayeredWhisker (fun z => F.map z = A.atom b) n x := by
  obtain ⟨c,hc,hh⟩ := A.whisker_atom_layered F hx
  have htop : (F.map x).row (n+1) false = A.basis (n+1) c := by
    rw [A.layered_row_above F c hh (n+1) (Nat.lt_succ_self n) false,← hc,A.basis_own]
  have he := A.basis_injective_on_dim (n+1) c b hc hb (htop.symm.trans ht)
  simpa only [he] using hh

theorem whiskerFaithful (n : ℕ)
    (hsmall : ∀ k, k ≤ n → Function.Bijective (F.onCells k))
    (hgen : ∀ k, k < n → ∀ a : C.Cell, C.source (k+1) a = a →
      C.TopSequence k (A.TopGenerator F k) a)
    (hreflect : ∀ k x, truncate k false (F.map x) = F.map x → C.source k x = x)
    (hatom : ∀ b (x y : C.Cell), F.map x = A.atom b → F.map y = A.atom b → x = y) :
    A.WhiskerFaithful F n := by
  intro x y hx hy he
  obtain ⟨b,hb,ht⟩ := A.whisker_top_basis F hx
  have hty : (F.map y).row (n+1) false = A.basis (n+1) b := by rw [← he]; exact ht
  have hx' := A.layered_ordered F n hsmall hgen hreflect b (by omega) x
    (A.whisker_layered_of_top F n b hb x hx ht)
  have hy' := A.layered_ordered F n hsmall hgen hreflect b (by omega) y
    (A.whisker_layered_of_top F n b hb y hy hty)
  exact OrderedWhisker.eq_of_map_eq b n (hatom b) (fun k hk => (hsmall k hk).1) x y hx' hy' he

theorem hasAdjacentExchange (n : ℕ)
    (hsmall : ∀ k, k ≤ n → Function.Bijective (F.onCells k))
    (hgen : ∀ k, k < n → ∀ a : C.Cell, C.source (k+1) a = a →
      C.TopSequence k (A.TopGenerator F k) a)
    (hreflect : ∀ k x, truncate k false (F.map x) = F.map x → C.source k x = x) :
    A.HasAdjacentExchange F n := by
  intro b c hb hc hbc x y hx hy ht hs hm
  have hx' := A.layered_ordered F n hsmall hgen hreflect b (by omega) x
    (A.whisker_layered_of_top F n b hb x hx ht)
  have hy' := A.layered_ordered F n hsmall hgen hreflect c (by omega) y
    (A.whisker_layered_of_top F n c hc y hy hs)
  obtain ⟨y',x',hy',hx',hm',he⟩ := A.ordered_exchange F n hsmall b c (by omega) (by omega)
    (A.rank_le_of_orderRank_le hbc.le) x y hx' hy' hm
  have hw (d : A.Index) (hd : A.dim d = n+1) (z : C.Cell)
      (hz : C.LayeredWhisker (fun t => F.map t = A.atom d) n z) :
      C.Whisker n (A.TopGenerator F n) z := by
    exact (hz.whisker n (fun t ht => hreflect (n+1) t (by rw [ht,← hd]; exact A.bounded d))
      le_rfl).mono (fun t ht => ⟨d,hd,ht⟩)
  refine ⟨y',x',hw c hc y' hy',hw b hb x' hx',?_,?_,hm',he⟩
  · rw [A.layered_row_above F c hy' (n+1) (Nat.lt_succ_self n) false,← hc,A.basis_own]
  · rw [A.layered_row_above F b hx' (n+1) (Nat.lt_succ_self n) false,← hb,A.basis_own]

theorem onCells_injective_step (n : ℕ)
    (hsmall : ∀ k, k ≤ n → Function.Bijective (F.onCells k))
    (hgen : ∀ k, k ≤ n → ∀ a : C.Cell, C.source (k+1) a = a →
      C.TopSequence k (A.TopGenerator F k) a)
    (hreflect : ∀ k x, truncate k false (F.map x) = F.map x → C.source k x = x)
    (hatom : ∀ b (x y : C.Cell), F.map x = A.atom b → F.map y = A.atom b → x = y) :
    Function.Injective (F.onCells (n+1)) :=
  A.onCells_injective_of_exchange F n (hsmall n le_rfl).1 (hgen n le_rfl)
    (A.whiskerFaithful F n hsmall (fun k hk => hgen k hk.le) hreflect hatom)
    (A.hasAdjacentExchange F n hsmall (fun k hk => hgen k hk.le) hreflect)
end Thomason.DirectedComplex.RankedAtoms

end

noncomputable section
universe u v w z


namespace Thomason.GrayRecursive.IntervalHom
open CategoryTheory DirectedComplex Table OmegaCategory NormalizedChains

theorem chainComparison_finiteSimplex_onCells_bijective
    {N : ℕ} {P : Type u} [LinearOrder P] (e : Fin (N+1) ≃o P) (n : ℕ) :
    Function.Bijective ((chainComparison (NormalizedChains.complex P)).onCells n) := by
  let := Fintype.ofEquiv (Fin (N+1)) e.toEquiv
  induction n using Nat.strong_induction_on with
  | h n ih =>
    refine ⟨?_,chainComparison_finiteSimplex_surjective_of_lower_injective P n
      (fun k hk => (ih k hk).1)⟩
    cases n with
    | zero =>
      exact (chainComparison (NormalizedChains.complex P)).onCells_injective_mono (by omega : 0 ≤ 2)
        (chainComparison_poset_twocells_bijective P).1
    | succ n =>
      exact (Prism.Basis.ofOrderIso e).onCells_injective_step
        (chainComparison (NormalizedChains.complex P)) n (fun k hk => ih k (by omega))
        (fun k _ => tensor_top_sequence e k)
        (chainComparison_reflects_dimension (Prism.Basis.ofOrderIso e))
        (chainComparison_atom_fiber_subsingleton (Prism.Basis.ofOrderIso e))

theorem standardSimplexComparison_isIso (m : ℕ) :
    IsIso (chainComparison (NormalizedChains.complex (ULift.{u} (Fin (m+3))))) := by
  apply chainComparison_finiteSimplex_isIso_of_injective
  apply (chainComparison (NormalizedChains.complex (ULift.{u} (Fin (m+3))))).map_injective_of_onCells_injective
    (n := m+3)
    (tensor_truncated (NormalizedChains.table_truncated_of_card_le (n := m+2) (by simp)))
  exact (chainComparison_finiteSimplex_onCells_bijective
    (N := m+2) (finLiftOrderIso (m+3)) (m+3)).1
end Thomason.GrayRecursive.IntervalHom

end

noncomputable section
universe u v w z


namespace Thomason

theorem main_oai : FullMain.{u} :=
  GrayRecursive.IntervalHom.fullMain_of_standardSimplexComparison_isIso
    GrayRecursive.IntervalHom.standardSimplexComparison_isIso
end Thomason

end

end OAI
end

theorem solution.{u} : type_of% @OAI.Thomason.main_oai.{u} := @OAI.Thomason.main_oai.{u}
