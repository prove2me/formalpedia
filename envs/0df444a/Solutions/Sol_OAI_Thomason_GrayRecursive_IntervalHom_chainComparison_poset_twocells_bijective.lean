-- Prove2me | solution 1 for OAI.Thomason.GrayRecursive.IntervalHom.chainComparison_poset_twocells_bijective
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T10:22:32.648487+00:00
-- url     : https://prove2.me/submissions/a8392fa3-ac15-4f46-aac6-2700205003ef

import Mathlib
import Definitions.Def_ThomasonModelStructures
import Definitions.Def_OAIQ043T012

section
-- module Solutions.OAIQ043_TH.Thomason_SimplexRanks
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Thomason.GeometricRecognition.Mesh.finiteChains _root_.OAI.Thomason.GeometricRecognition.PolyPoint.finiteBoundedFaces _root_.OAI.Thomason.KanQuillen.boundary_small _root_.OAI.Thomason.KanQuillen.boundary_smallCardinal _root_.OAI.Thomason.KanQuillen.boundary_smallObject _root_.OAI.Thomason.NormalizedChains.finiteWord _root_.OAI.Thomason.Subdivision.ex_preservesFilteredColimits _root_.OAI.Thomason.Subdivision.finiteNonemptyChains _root_.OAI.Thomason.Subdivision.finiteOrderNerve _root_.OAI.Thomason.Subdivision.sequentialSSetColim_preservesFiniteLimits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Simplex Ranks. -/

noncomputable section
universe u v w z


namespace Thomason.NormalizedChains

variable {E : Type u} [PartialOrder E]

lemma chainMass_nonneg {z : Chains E} (hz : Positive z) : 0 ≤ chainMass z := by
  classical
  rw [chainMass_eq_sum, Finsupp.sum]
  exact Finset.sum_nonneg (fun w _ => hz w)

end Thomason.NormalizedChains

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

lemma join_four (C : OmegaCategory.{u}) (k : ℕ) (a b c d : C.Cell)
    (hab : C.target k a = C.source k b) (hbc : C.target k b = C.source k c)
    (hcd : C.target k c = C.source k d) :
    C.join k (C.join k a b) (C.join k c d) = C.join k a (C.join k (C.join k b c) d) := by
  have hb_cd : C.target k b = C.source k (C.join k c d) := by
    rw [C.join_source_le k k c d le_rfl hcd]; exact hbc
  rw [C.join_assoc k a b (C.join k c d) hab hb_cd, C.join_assoc k b c d hbc hcd]

lemma join_four_middle (C : OmegaCategory.{u}) (k : ℕ) (a b c d e f : C.Cell)
    (hab : C.target k a = C.source k b) (hbc : C.target k b = C.source k c)
    (hcd : C.target k c = C.source k d) (hae : C.target k a = C.source k e)
    (hef : C.target k e = C.source k f) (hfd : C.target k f = C.source k d)
    (hm : C.join k b c = C.join k e f) :
    C.join k (C.join k a b) (C.join k c d) =
      C.join k (C.join k a e) (C.join k f d) := by
  rw [C.join_four k a b c d hab hbc hcd, C.join_four k a e f d hae hef hfd, hm]

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

lemma join_factor_left (C : OmegaCategory.{u}) (k l : ℕ) (hkl : k < l)
    (a b : C.Cell) (h : C.target k a = C.source k b) :
    C.join k a b = C.join l (C.join k (C.source l a) b) (C.join k a (C.target l b)) := by
  have hab : C.target k (C.source l a) = C.source k b := by
    rw [C.target_source, ite_eq_left hkl]; exact h
  have hab' : C.target k a = C.source k (C.target l b) := by
    rw [C.source_target, ite_eq_left hkl]; exact h
  have h' := C.join_interchange k l hkl (C.source l a) a b (C.target l b)
    (C.target_source_self l a) (C.source_target_self l b).symm hab hab'
  rw [C.join_left_unit l (C.source l a) a (C.source_source_self l a) (C.target_source_self l a),
    C.join_right_unit l b (C.target l b) (C.source_target_self l b)
      (C.source_target_self l b).symm] at h'
  exact h'

lemma join_middle (C : OmegaCategory.{u}) (k l : ℕ) (hkl : k < l)
    (a b : C.Cell) (h : C.target k a = C.source k b) :
    C.join l (C.join k a (C.source l b)) (C.join k (C.target l a) b) =
      C.join l (C.join k (C.source l a) b) (C.join k a (C.target l b)) :=
  (C.join_factor_right k l hkl a b h).symm.trans (C.join_factor_left k l hkl a b h)

end Thomason.OmegaCategory

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

lemma project_row (t : Table M.cylinder) (p : ℕ) (b : Bool) :
    (project t).row p b = side t false p b + side t true p b := by cases p <;> rfl

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

variable (hM : PositiveAcyclic M)
include hM

lemma label_values (t : Table M.cylinder) (b : Bool) :
    label t b = 0 ∨ label t b = 1 := by
  have h := augmentation_sides t b
  have h₀ := hM.augmentation_nonneg _ (side_positive t false 0 b)
  have h₁ := hM.augmentation_nonneg _ (side_positive t true 0 b)
  dsimp [label]
  omega

lemma label_monotone (t : Table M.cylinder) : label t false ≤ label t true := by
  have h := hM.augmentation_nonneg _ (cross_positive t 0 false)
  rw [augmentation_cross] at h
  omega

lemma cross_zero_of_stationary (t : Table M.cylinder) (h : label t true = label t false) :
    ∀ p b, cross t p b = 0 := by
  intro p b
  induction p generalizing b with
  | zero =>
    exact hM.augmentation_zero _ (cross_positive t 0 b) (by rw [augmentation_cross,h,sub_self])
  | succ p ih =>
    exact hM.cycle_zero p _ (cross_positive t (p+1) b) (by rw [cross_boundary,ih true,ih false,sub_self])

lemma side_zero_of_empty (t : Table M.cylinder) (a : Bool)
    (hc : ∀ p b, cross t p b = 0) (hs : ∀ b, side t a 0 b = 0) :
    ∀ p b, side t a p b = 0 := by
  intro p b
  induction p generalizing b with
  | zero => exact hs b
  | succ p ih =>
    apply hM.cycle_zero p _ (side_positive t a (p+1) b)
    cases a with
    | false => simpa only [hc,smul_zero,ih,sub_zero,sub_self] using left_boundary t p b
    | true => simpa only [hc,smul_zero,ih,add_zero,sub_self] using right_boundary t p b

lemma stationary_reconstruct (t : Table M.cylinder) (a : Bool)
    (hs : label t false = if a then 1 else 0)
    (ht : label t true = if a then 1 else 0) :
    t = (M.cylinderEndpoint a).table (project t) := by
  have hc := cross_zero_of_stationary hM t (ht.trans hs.symm)
  have he : ∀ p b, side t (!a) p b = 0 := by
    apply side_zero_of_empty hM t (!a) hc
    intro b
    apply hM.augmentation_zero _ (side_positive t (!a) 0 b)
    have hh : label t b = if a then 1 else 0 := by cases b; exact hs; exact ht
    have haug := augmentation_sides t b
    cases a <;> dsimp [label] at hh <;> simp only [Bool.not_false,Bool.not_true] at haug ⊢ <;> omega
  ext p b
  change t.row p b = M.cylinderEndpointMap a p ((project t).row p b)
  rw [project_row]
  cases a
  · have hz := he p b
    change side t true p b = 0 at hz
    rw [hz,add_zero]
    cases p with
    | zero => exact Prod.ext rfl hz
    | succ p => exact Prod.ext rfl (Prod.ext hz (hc p b))
  · have hz := he p b
    change side t false p b = 0 at hz
    rw [hz,zero_add]
    cases p with
    | zero => exact Prod.ext hz rfl
    | succ p => exact Prod.ext hz (Prod.ext rfl (hc p b))

lemma endpoint_or_crossing (t : Table M.cylinder) :
    (∃ a, t = (M.cylinderEndpoint a).table (project t)) ∨
      (label t false = 0 ∧ label t true = 1) := by
  have hs := label_values hM t false
  have ht := label_values hM t true
  have hm := label_monotone hM t
  by_cases h : label t false = label t true
  · left
    rcases hs with hs | hs
    · exact ⟨false,stationary_reconstruct hM t false hs (h.symm.trans hs)⟩
    · exact ⟨true,stationary_reconstruct hM t true hs (h.symm.trans hs)⟩
  · right
    constructor <;> omega

end CylinderTables
end Thomason.DirectedComplex

end

noncomputable section
universe u v w z


namespace Thomason.NormalizedChains
open DirectedComplex
variable (E : Type u) [PartialOrder E]

theorem complexPositiveAcyclic : PositiveAcyclic (complex E) where
  augmentation_nonneg x hx := by
    change 0 ≤ emptyCoefficient (boundary x.val)
    rw [augmentation_eq_sum x.property,← chainMass_eq_sum]
    exact chainMass_nonneg hx
  augmentation_zero x hx ha := Subtype.ext (positive_augmentation_zero x.property hx ha)
  cycle_zero p x hx hd := Subtype.ext (positive_cycle_zero_partial x.property hx (congrArg Subtype.val hd))

end Thomason.NormalizedChains

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
-- module Solutions.OAIQ043_TH.Thomason_EdgeComparison
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Edge Comparison. -/

noncomputable section
universe u v w z


namespace Thomason.DirectedComplex.CylinderTables
open Table
variable {M : DirectedComplex.{u}}

lemma crossing_edge_factor (hM : PositiveAcyclic M) (t : Table M.cylinder)
    (hs : label t false = 0) (ht : label t true = 1) (hb : truncate 1 false t = t) :
    comp 0 (comp 0 ((M.cylinderEndpoint false).table (leftProfile t hs ht))
      (verticalTable (crossingProfile t hs ht)) (crossing_edge_matching_left hM t hs ht hb))
      ((M.cylinderEndpoint true).table (rightProfile t hs ht))
      (crossing_edge_matching_right hM t hs ht hb) = t := by
  have hc := crossingProfile_bounded t hs ht hb
  have hzc (p : ℕ) (hp : 0 < p) (b : Bool) := row_above_fixed (crossingProfile t hs ht) hc hp b
  obtain ⟨hsrc,htgt⟩ := crossing_starts_ends hM t hs ht
  ext p b
  rw [comp_row,comp_row]
  cases p with
  | zero =>
    cases b
    · change (M.cylinderEndpointMap false 0 ((leftProfile t hs ht).row 0 false)) = t.row 0 false
      change (side t false 0 false + 0,0) = t.row 0 false
      rw [add_zero]
      exact Prod.ext rfl hsrc.symm
    · change (M.cylinderEndpointMap true 0 ((rightProfile t hs ht).row 0 true)) = t.row 0 true
      change (0,side t true 0 true + 0) = t.row 0 true
      rw [add_zero]
      exact Prod.ext htgt.symm rfl
  | succ p =>
    simp only [show ¬p+1 < 0 by omega, show p+1 ≠ 0 by omega, ite_false]
    change M.cylinderEndpointMap false (p+1) (leftProfileRow t (p+1) b) +
      verticalRow (crossingProfile t hs ht) (p+1) b +
      M.cylinderEndpointMap true (p+1) (rightProfileRow t (p+1) b) = t.row (p+1) b
    have hz : cross t (p+1) b = 0 := hzc (p+1) (by omega) b
    have hleft : leftProfileRow t (p+1) b = side t false (p+1) b := by
      simp only [leftProfileRow,hz,ite_self,add_zero]
    have hright : rightProfileRow t (p+1) b = side t true (p+1) b := by
      simp only [rightProfileRow,hz,ite_self,add_zero]
    rw [hleft,hright]
    have hv : verticalRow (crossingProfile t hs ht) (p+1) b = (0,0,cross t p b) := by
      simp only [verticalRow,hzc (p+1) (by omega) b]
      split_ifs <;> rfl
    rw [hv]
    change (side t false (p+1) b,0,0) + (0,0,cross t p b) +
      (0,side t true (p+1) b,0) = t.row (p+1) b
    simp only [Prod.mk_add_mk,add_zero,zero_add]
    rfl
end Thomason.DirectedComplex.CylinderTables

end

noncomputable section
universe u v w z


namespace Thomason.GrayRecursive.IntervalHom
open CategoryTheory DirectedComplex DirectedComplex.Table GlobeComplex OmegaCategory

variable {X Y : OmegaCategory.{u}} {M : DirectedComplex.{u}}

lemma verticalObject_bounded (c : X.Objects) :
    (tensorFunctor.obj X).source 1 (verticalObject c) = verticalObject c := by
  change (tensorFunctor.obj X).source 1 ((generatorCylinder 0 c).map _) = _
  erw [← (generatorCylinder 0 c).map_source]
  change (generatorCylinder 0 c).map (truncate 1 false (verticalTable (topTable 0))) = _
  rw [vertical_fixed _ (topTable_bounded 0)]
  rfl

lemma verticalObject_face (c : X.Objects) (a : Bool) :
    (tensorFunctor.obj X).face 0 a (verticalObject c) = ((tensorEndpoint a).app X).map c.val := by
  unfold verticalObject
  erw [← (generatorCylinder 0 c).map_face]
  have he : (K.{u} 0).nu.face 0 a (verticalTable (topTable 0)) = atEnd a (topTable 0) := by
    change (if a then truncate 0 true (verticalTable (topTable 0)) else
      truncate 0 false (verticalTable (topTable 0))) = _
    cases a <;> exact CylinderTables.vertical_object_face _ (topTable_bounded 0) _
  erw [he,generatorCylinder_endpoint,lift_top]

lemma verticalObject_source (c : X.Objects) :
    (tensorFunctor.obj X).source 0 (verticalObject c) = ((tensorEndpoint false).app X).map c.val :=
  verticalObject_face c false

lemma verticalObject_target (c : X.Objects) :
    (tensorFunctor.obj X).target 0 (verticalObject c) = ((tensorEndpoint true).app X).map c.val :=
  verticalObject_face c true

lemma verticalObject_natural (F : X ⟶ Y) (c : X.Objects) :
    (tensorFunctor.map F).map (verticalObject c) = verticalObject (F.objects c) := by
  apply tensorFunctor_map_generator

lemma chainComparison_verticalObject (c : M.nu.Objects) :
    (chainComparison M).map (verticalObject c) = verticalTable c.val := by
  change (chainComparison M).map ((tensorPresentation M.nu).generator ⟨0,c,_⟩) = _
  erw [chainComparison_generator,tableCylinder_vertical]
  exact congrArg verticalTable c.property

lemma crossingEdge_left_matching (l : X.Cell) (c : X.Objects)
    (hl : X.target 0 l = c.val) :
    (tensorFunctor.obj X).target 0 (((tensorEndpoint false).app X).map l) =
      (tensorFunctor.obj X).source 0 (verticalObject c) := by
  rw [verticalObject_source,← ((tensorEndpoint false).app X).map_target]
  exact congrArg ((tensorEndpoint false).app X).map hl

lemma crossingEdge_right_matching (l : X.Cell) (c : X.Objects) (r : X.Cell)
    (hl : X.target 0 l = c.val) (hr : X.source 0 r = c.val) :
    (tensorFunctor.obj X).target 0
      ((tensorFunctor.obj X).join 0 (((tensorEndpoint false).app X).map l) (verticalObject c)) =
        (tensorFunctor.obj X).source 0 (((tensorEndpoint true).app X).map r) := by
  rw [(tensorFunctor.obj X).join_target_le 0 0 _ _ le_rfl (crossingEdge_left_matching l c hl),
    verticalObject_target,← ((tensorEndpoint true).app X).map_source]
  exact congrArg ((tensorEndpoint true).app X).map hr.symm

lemma chainComparison_crossingEdge (l : Table M) (c : M.nu.Objects) (r : Table M)
    (hl : truncate 0 true l = c.val) (hr : truncate 0 false r = c.val) :
    (chainComparison M).map (crossingEdge l c r) =
      M.cylinder.nu.join 0 (M.cylinder.nu.join 0 ((M.cylinderEndpoint false).table l)
        (verticalTable c.val)) ((M.cylinderEndpoint true).table r) := by
  unfold crossingEdge
  erw [(chainComparison M).map_join 0 _ _ (crossingEdge_right_matching (X := M.nu) l c r hl hr),
    (chainComparison M).map_join 0 _ _ (crossingEdge_left_matching (X := M.nu) l c hl)]
  rw [chainComparison_endpoint_apply,chainComparison_endpoint_apply,chainComparison_verticalObject]

lemma chainComparison_crossingEdgeLift (hM : PositiveAcyclic M) (t : Table M.cylinder)
    (hs : CylinderTables.label t false = 0) (ht : CylinderTables.label t true = 1)
    (hb : truncate 1 false t = t) :
    (chainComparison M).map (crossingEdgeLift t hs ht hb) = t := by
  erw [crossingEdgeLift,chainComparison_crossingEdge _ _ _
    (CylinderTables.crossing_edge_left_target hM t hs ht hb)
    (CylinderTables.crossing_edge_right_source hM t hs ht hb)]
  erw [M.cylinder.nu.join_eq 0 _ _ (CylinderTables.crossing_edge_matching_left hM t hs ht hb),
    M.cylinder.nu.join_eq 0 _ _ (CylinderTables.crossing_edge_matching_right hM t hs ht hb)]
  exact CylinderTables.crossing_edge_factor hM t hs ht hb

end Thomason.GrayRecursive.IntervalHom

end

noncomputable section
universe u v w z


namespace Thomason.GlobeComplex
open DirectedComplex

theorem complexPositiveAcyclic (n : ℕ) : PositiveAcyclic (complex.{u} n) where
  augmentation_nonneg _ hx := mass_nonneg hx
  augmentation_zero _ hx h := (mass_eq_zero_iff hx).mp h
  cycle_zero _ _ hx h := positive_cycle_zero _ hx h

end Thomason.GlobeComplex

end

noncomputable section
universe u v w z


namespace Thomason.GrayRecursive.IntervalHom
open CategoryTheory DirectedComplex DirectedComplex.Table GlobeComplex OmegaCategory
variable {X Y : OmegaCategory.{u}}

lemma crossingEdge_source (l : X.Cell) (c : X.Objects) (r : X.Cell)
    (hl : X.target 0 l = c.val) (hr : X.source 0 r = c.val) :
    (tensorFunctor.obj X).source 0 (crossingEdge l c r) =
      ((tensorEndpoint false).app X).map (X.source 0 l) := by
  unfold crossingEdge
  rw [(tensorFunctor.obj X).join_source_le 0 0 _ _ le_rfl (crossingEdge_right_matching l c r hl hr),
    (tensorFunctor.obj X).join_source_le 0 0 _ _ le_rfl (crossingEdge_left_matching l c hl),
    ← ((tensorEndpoint false).app X).map_source]
  rfl

lemma crossingEdge_target (l : X.Cell) (c : X.Objects) (r : X.Cell)
    (hl : X.target 0 l = c.val) (hr : X.source 0 r = c.val) :
    (tensorFunctor.obj X).target 0 (crossingEdge l c r) =
      ((tensorEndpoint true).app X).map (X.target 0 r) := by
  unfold crossingEdge
  rw [(tensorFunctor.obj X).join_target_le 0 0 _ _ le_rfl (crossingEdge_right_matching l c r hl hr),
    ← ((tensorEndpoint true).app X).map_target]
  rfl

lemma tensorFunctor_map_endpoint (F : X ⟶ Y) (a : Bool) (x : X.Cell) :
    (tensorFunctor.map F).map (((tensorEndpoint a).app X).map x) =
      ((tensorEndpoint a).app Y).map (F.map x) :=
  (congrArg (fun f : X ⟶ tensorFunctor.obj Y => f.map x) ((tensorEndpoint a).naturality F)).symm

lemma tensorFunctor_map_crossingEdge (F : X ⟶ Y) (l : X.Cell) (c : X.Objects) (r : X.Cell)
    (hl : X.target 0 l = c.val) (hr : X.source 0 r = c.val) :
    (tensorFunctor.map F).map (crossingEdge l c r) = crossingEdge (F.map l) (F.objects c) (F.map r) := by
  unfold crossingEdge
  rw [(tensorFunctor.map F).map_join 0 _ _ (crossingEdge_right_matching l c r hl hr),
    (tensorFunctor.map F).map_join 0 _ _ (crossingEdge_left_matching l c hl),
    tensorFunctor_map_endpoint,tensorFunctor_map_endpoint,verticalObject_natural]

lemma EdgeNormal.map (F : X ⟶ Y) {z : (tensorFunctor.obj X).Cell} (hz : EdgeNormal X z) :
    EdgeNormal Y ((tensorFunctor.map F).map z) := by
  cases hz with
  | endpoint a x hx =>
    rw [tensorFunctor_map_endpoint]
    exact .endpoint a (F.map x) ((F.map_source 1 x).symm.trans (congrArg F.map hx))
  | crossing l c r hl hr hdl hdr =>
    rw [tensorFunctor_map_crossingEdge F l c r hl hr]
    exact .crossing (F.map l) (F.objects c) (F.map r)
      ((F.map_target 0 l).symm.trans (congrArg F.map hl))
      ((F.map_source 0 r).symm.trans (congrArg F.map hr))
      ((F.map_source 1 l).symm.trans (congrArg F.map hdl))
      ((F.map_source 1 r).symm.trans (congrArg F.map hdr))

lemma EdgeNormal.face_zero {z : (tensorFunctor.obj X).Cell} (hz : EdgeNormal X z) (b : Bool) :
    EdgeNormal X ((tensorFunctor.obj X).face 0 b z) := by
  cases hz with
  | endpoint a x hx =>
    rw [← ((tensorEndpoint a).app X).map_face]
    exact .endpoint a _ (X.source_fixed_upwards (by omega : 0 ≤ 1) (by
      change X.face 0 false (X.face 0 b x) = X.face 0 b x
      rw [X.face_face]; simp))
  | crossing l c r hl hr hdl hdr =>
    cases b
    · change EdgeNormal X ((tensorFunctor.obj X).source 0 _)
      rw [crossingEdge_source l c r hl hr]
      exact .endpoint false _ (X.source_fixed_upwards (by omega : 0 ≤ 1) (X.source_source_self 0 l))
    · change EdgeNormal X ((tensorFunctor.obj X).target 0 _)
      rw [crossingEdge_target l c r hl hr]
      exact .endpoint true _ (X.source_fixed_upwards (by omega : 0 ≤ 1) (X.source_target_self 0 r))

lemma generatorCylinder_as_map (n : ℕ) (x : X.Cells n) (z : Table (K.{u} n)) :
    (generatorCylinder n x).map z =
      (tensorFunctor.map (GlobeComplex.lift x.val x.property)).map ((globeTensorIso n).inv.map z) := by
  change _ = (tensorFunctor.map (GlobeComplex.lift x.val x.property)).map
    ((tensorPresentation (complex n).nu).generator ⟨n,⟨topTable n,topTable_bounded n⟩,z⟩)
  erw [tensorFunctor_map_generator]
  simp only [lift_top]
  rfl

lemma globe_inv_edge_normal (n : ℕ) (t : Table (K.{u} n)) (ht : truncate 1 false t = t) :
    EdgeNormal (complex n).nu ((globeTensorIso n).inv.map t) := by
  rcases CylinderTables.endpoint_or_crossing (complexPositiveAcyclic n) t with ⟨a,ha⟩ | ⟨hs,he⟩
  · have hp : truncate 1 false (CylinderTables.project t) = CylinderTables.project t := by
      change truncate 1 false ((complex n).cylinderProjection.table t) = _
      rw [← Hom.table_truncate,ht]
      rfl
    have him : (chainComparison (complex n)).map (((tensorEndpoint a).app (complex n).nu).map
        (CylinderTables.project t)) = t := (chainComparison_endpoint_apply a _).trans ha.symm
    rw [chainComparison_globe] at him
    have hi := congrArg (globeTensorIso n).inv.map him
    have hback := congrArg (fun F : tensorFunctor.obj (complex n).nu ⟶ tensorFunctor.obj (complex n).nu =>
      F.map (((tensorEndpoint a).app (complex n).nu).map (CylinderTables.project t))) (globeTensorIso n).hom_inv_id
    change (globeTensorIso n).inv.map ((globeTensorIso n).hom.map _) = _ at hback
    rw [hback] at hi
    rw [← hi]
    exact .endpoint a _ hp
  · have him := chainComparison_crossingEdgeLift (complexPositiveAcyclic n) t hs he ht
    rw [chainComparison_globe] at him
    have hi := congrArg (globeTensorIso n).inv.map him
    have hback := congrArg (fun F : tensorFunctor.obj (complex n).nu ⟶ tensorFunctor.obj (complex n).nu =>
      F.map (crossingEdgeLift t hs he ht)) (globeTensorIso n).hom_inv_id
    change (globeTensorIso n).inv.map ((globeTensorIso n).hom.map _) = _ at hback
    rw [hback] at hi
    rw [← hi]
    exact .crossing _ _ _
      (CylinderTables.crossing_edge_left_target (complexPositiveAcyclic n) t hs he ht)
      (CylinderTables.crossing_edge_right_source (complexPositiveAcyclic n) t hs he ht)
      (CylinderTables.leftProfile_bounded t hs he ht)
      (CylinderTables.rightProfile_bounded t hs he ht)

lemma generatorCylinder_edge_normal (n : ℕ) (x : X.Cells n) (t : Table (K.{u} n))
    (ht : truncate 1 false t = t) : EdgeNormal X ((generatorCylinder n x).map t) := by
  rw [generatorCylinder_as_map]
  exact (globe_inv_edge_normal n t ht).map _
end Thomason.GrayRecursive.IntervalHom

end

noncomputable section
universe u v w z


namespace Thomason.GrayRecursive.IntervalHom
open CategoryTheory DirectedComplex DirectedComplex.Table GlobeComplex OmegaCategory
variable {X : OmegaCategory.{u}}

lemma endpoint_target (a : Bool) (k : ℕ) (x : X.Cell) :
    (tensorFunctor.obj X).target k (((tensorEndpoint a).app X).map x) =
      ((tensorEndpoint a).app X).map (X.target k x) := (((tensorEndpoint a).app X).map_target k x).symm

lemma endpoint_join_crossing (x l : X.Cell) (c : X.Objects) (r : X.Cell)
    (hxl : X.target 0 x = X.source 0 l) (hl : X.target 0 l = c.val) (hr : X.source 0 r = c.val) :
    (tensorFunctor.obj X).join 0 (((tensorEndpoint false).app X).map x) (crossingEdge l c r) =
      crossingEdge (X.join 0 x l) c r := by
  let e₀ := ((tensorEndpoint false).app X)
  let e₁ := ((tensorEndpoint true).app X)
  have h₁ : (tensorFunctor.obj X).target 0 (e₀.map x) = (tensorFunctor.obj X).source 0 (e₀.map l) :=
    e₀.map_composable hxl
  have h₂ := crossingEdge_left_matching l c hl
  have h₃ := crossingEdge_right_matching l c r hl hr
  unfold crossingEdge
  erw [e₀.map_join 0 x l hxl]
  rw [(tensorFunctor.obj X).join_assoc 0 (e₀.map x) (e₀.map l) (verticalObject c) h₁ h₂]
  rw [(tensorFunctor.obj X).join_assoc 0 (e₀.map x) _ (e₁.map r) _ h₃]
  rw [(tensorFunctor.obj X).join_source_le 0 0 _ _ le_rfl h₂]
  exact h₁

lemma crossing_join_endpoint (l : X.Cell) (c : X.Objects) (r y : X.Cell)
    (hl : X.target 0 l = c.val) (hr : X.source 0 r = c.val) (hry : X.target 0 r = X.source 0 y) :
    (tensorFunctor.obj X).join 0 (crossingEdge l c r) (((tensorEndpoint true).app X).map y) =
      crossingEdge l c (X.join 0 r y) := by
  have h₁ := crossingEdge_right_matching l c r hl hr
  have h₂ : (tensorFunctor.obj X).target 0 (((tensorEndpoint true).app X).map r) =
      (tensorFunctor.obj X).source 0 (((tensorEndpoint true).app X).map y) :=
    ((tensorEndpoint true).app X).map_composable hry
  unfold crossingEdge
  erw [((tensorEndpoint true).app X).map_join 0 r y hry,
    (tensorFunctor.obj X).join_assoc 0 _ _ _ h₁ h₂]

lemma EdgeNormal.join {x y : (tensorFunctor.obj X).Cell} (hx : EdgeNormal X x) (hy : EdgeNormal X y)
    (h : (tensorFunctor.obj X).target 0 x = (tensorFunctor.obj X).source 0 y) :
    EdgeNormal X ((tensorFunctor.obj X).join 0 x y) := by
  cases hx with
  | endpoint a x hx =>
    cases hy with
    | endpoint b y hy =>
      rw [endpoint_target,endpoint_source] at h
      obtain ⟨hab,hxy⟩ := (tensorEndpoint_eq_iff a b _ _).mp h
      subst b
      rw [← ((tensorEndpoint a).app X).map_join 0 x y hxy]
      exact .endpoint a _ (composite_bounded X (by omega : 0 < 1) x y hx hy hxy)
    | crossing l c r hl hr hdl hdr =>
      rw [endpoint_target,crossingEdge_source l c r hl hr] at h
      obtain ⟨ha,hxl⟩ := (tensorEndpoint_eq_iff a false _ _).mp h
      subst a
      rw [endpoint_join_crossing x l c r hxl hl hr]
      exact .crossing _ c r ((X.join_target_le 0 0 x l le_rfl hxl).trans hl) hr
        (composite_bounded X (by omega : 0 < 1) x l hx hdl hxl) hdr
  | crossing l c r hl hr hdl hdr =>
    cases hy with
    | endpoint a y hy =>
      rw [crossingEdge_target l c r hl hr,endpoint_source] at h
      obtain ⟨ha,hry⟩ := (tensorEndpoint_eq_iff true a _ _).mp h
      subst a
      rw [crossing_join_endpoint l c r y hl hr hry]
      exact .crossing l c _ hl ((X.join_source_le 0 0 r y le_rfl hry).trans hr) hdl
        (composite_bounded X (by omega : 0 < 1) r y hdr hy hry)
    | crossing l' c' r' hl' hr' hdl' hdr' =>
      rw [crossingEdge_target l c r hl hr,crossingEdge_source l' c' r' hl' hr'] at h
      exact False.elim (Bool.noConfusion ((tensorEndpoint_eq_iff true false _ _).mp h).1)

lemma tensor_one_faces_normal (z : (tensorFunctor.obj X).Cell) (b : Bool) :
    EdgeNormal X ((tensorFunctor.obj X).face 1 b z) := by
  suffices h : ∀ b : Bool, EdgeNormal X ((tensorFunctor.obj X).face 1 b z) from h b
  apply (tensorPresentation X).cells_induction (fun z => ∀ b : Bool,
    EdgeNormal X ((tensorFunctor.obj X).face 1 b z))
  · rintro ⟨n,x,t⟩ b
    change EdgeNormal X ((tensorFunctor.obj X).face 1 b ((generatorCylinder n x).map t))
    erw [← (generatorCylinder n x).map_face]
    have he : (K n).nu.face 1 b t = truncate 1 b t := by cases b <;> rfl
    rw [he]
    exact generatorCylinder_edge_normal n x _ (by
      erw [truncate_truncate]; simp)
  · intro k x hx b
    change EdgeNormal X ((tensorFunctor.obj X).face 1 b ((tensorFunctor.obj X).face k false x))
    erw [(tensorFunctor.obj X).face_face]
    by_cases hk : 1 < k
    · rw [ite_eq_left hk]; exact hx b
    · rw [ite_eq_right hk]
      have hk' : k = 0 ∨ k = 1 := by omega
      rcases hk' with rfl | rfl
      · have he := (hx false).face_zero false
        erw [(tensorFunctor.obj X).face_face,ite_eq_left (by omega : 0 < 1)] at he
        exact he
      · exact hx false
  · intro k x hx b
    change EdgeNormal X ((tensorFunctor.obj X).face 1 b ((tensorFunctor.obj X).face k true x))
    erw [(tensorFunctor.obj X).face_face]
    by_cases hk : 1 < k
    · rw [ite_eq_left hk]; exact hx b
    · rw [ite_eq_right hk]
      have hk' : k = 0 ∨ k = 1 := by omega
      rcases hk' with rfl | rfl
      · have he := (hx false).face_zero true
        erw [(tensorFunctor.obj X).face_face,ite_eq_left (by omega : 0 < 1)] at he
        exact he
      · exact hx true
  · intro k x y h hx hy b
    change EdgeNormal X ((tensorFunctor.obj X).face 1 b ((tensorFunctor.obj X).comp k x y h))
    cases k with
    | zero =>
      cases b
      · change EdgeNormal X ((tensorFunctor.obj X).source 1 _)
        rw [← (tensorFunctor.obj X).join_eq 0 x y h,
          (tensorFunctor.obj X).join_source_gt 1 0 x y (by omega) h]
        exact (hx false).join (hy false) ((tensorFunctor.obj X).source_composable (by omega) h)
      · change EdgeNormal X ((tensorFunctor.obj X).target 1 _)
        rw [← (tensorFunctor.obj X).join_eq 0 x y h,
          (tensorFunctor.obj X).join_target_gt 1 0 x y (by omega) h]
        exact (hx true).join (hy true) ((tensorFunctor.obj X).target_composable (by omega) h)
    | succ k =>
      cases b
      · change EdgeNormal X ((tensorFunctor.obj X).source 1 _)
        rw [(tensorFunctor.obj X).source_comp_le 1 (k+1) (by omega) x y h]
        exact hx false
      · change EdgeNormal X ((tensorFunctor.obj X).target 1 _)
        rw [(tensorFunctor.obj X).target_comp_le 1 (k+1) (by omega) x y h]
        exact hy true

lemma tensor_edge_normal (z : (tensorFunctor.obj X).Cell)
    (hz : (tensorFunctor.obj X).source 1 z = z) : EdgeNormal X z := by
  have h := tensor_one_faces_normal z false
  change EdgeNormal X ((tensorFunctor.obj X).source 1 z) at h
  rwa [hz] at h
end Thomason.GrayRecursive.IntervalHom

end

noncomputable section
universe u v w z


namespace Thomason.GrayRecursive.IntervalHom
open CategoryTheory DirectedComplex DirectedComplex.Table GlobeComplex OmegaCategory
variable {M : DirectedComplex.{u}}

lemma crossing_edge_table_matching_left (l : Table M) (c : M.nu.Objects)
    (hl : truncate 0 true l = c.val) :
    truncate 0 true ((M.cylinderEndpoint false).table l) = truncate 0 false (verticalTable c.val) := by
  rw [CylinderTables.vertical_object_face c.val c.property,← Hom.table_truncate,hl]

lemma crossing_edge_table_matching_right (l : Table M) (c : M.nu.Objects) (r : Table M)
    (hl : truncate 0 true l = c.val) (hr : truncate 0 false r = c.val) :
    M.cylinder.nu.target 0 (M.cylinder.nu.join 0 ((M.cylinderEndpoint false).table l) (verticalTable c.val)) =
      M.cylinder.nu.source 0 ((M.cylinderEndpoint true).table r) := by
  rw [M.cylinder.nu.join_target_le 0 0 _ _ le_rfl (crossing_edge_table_matching_left l c hl)]
  change truncate 0 true (verticalTable c.val) = truncate 0 false ((M.cylinderEndpoint true).table r)
  rw [CylinderTables.vertical_object_face c.val c.property,← Hom.table_truncate,hr]

lemma chainComparison_crossingEdge_row_succ (l : Table M) (c : M.nu.Objects) (r : Table M)
    (hl : truncate 0 true l = c.val) (hr : truncate 0 false r = c.val) (p : ℕ) (b : Bool) :
    ((chainComparison M).map (crossingEdge l c r)).row (p+1) b =
      (l.row (p+1) b,r.row (p+1) b,c.val.row p b) := by
  rw [chainComparison_crossingEdge l c r hl hr,
    table_join_zero_row_succ _ _ (crossing_edge_table_matching_right l c r hl hr),
    table_join_zero_row_succ _ _ (crossing_edge_table_matching_left l c hl)]
  change M.cylinderEndpointMap false (p+1) (l.row (p+1) b) + verticalRow c.val (p+1) b +
    M.cylinderEndpointMap true (p+1) (r.row (p+1) b) = _
  have hz : c.val.row (p+1) b = 0 := row_above_fixed c.val c.property (by omega) b
  have hv : verticalRow c.val (p+1) b = (0,0,c.val.row p b) := by
    simp only [verticalRow,hz]
    split_ifs <;> rfl
  rw [hv]
  change (l.row (p+1) b,0,0) + (0,0,c.val.row p b) + (0,r.row (p+1) b,0) = _
  simp only [Prod.mk_add_mk,add_zero,zero_add]

lemma chainComparison_crossingEdge_row_zero (l : Table M) (c : M.nu.Objects) (r : Table M)
    (hl : truncate 0 true l = c.val) (hr : truncate 0 false r = c.val) (b : Bool) :
    ((chainComparison M).map (crossingEdge l c r)).row 0 b =
      if b then (0,r.row 0 true) else (l.row 0 false,0) := by
  rw [chainComparison_crossingEdge l c r hl hr,
    table_join_zero_row_zero _ _ (crossing_edge_table_matching_right l c r hl hr),
    table_join_zero_row_zero _ _ (crossing_edge_table_matching_left l c hl)]
  cases b <;> rfl

lemma chainComparison_crossingEdge_injective
    (l l' : Table M) (c c' : M.nu.Objects) (r r' : Table M)
    (hl : truncate 0 true l = c.val) (hr : truncate 0 false r = c.val)
    (hl' : truncate 0 true l' = c'.val) (hr' : truncate 0 false r' = c'.val)
    (he : (chainComparison M).map (crossingEdge l c r) =
      (chainComparison M).map (crossingEdge l' c' r')) :
    l = l' ∧ c = c' ∧ r = r' := by
  have hrows (p : ℕ) (b : Bool) := congrArg (fun t : Table M.cylinder => t.row (p+1) b) he
  simp only [chainComparison_crossingEdge_row_succ l c r hl hr,
    chainComparison_crossingEdge_row_succ l' c' r' hl' hr'] at hrows
  have hc : c = c' := by
    apply Subtype.ext
    apply Table.ext
    funext p b
    exact congrArg (fun z => z.2.2) (hrows p b)
  subst c'
  have he₀ (b : Bool) := congrArg (fun t : Table M.cylinder => t.row 0 b) he
  simp only [chainComparison_crossingEdge_row_zero l c r hl hr,
    chainComparison_crossingEdge_row_zero l' c r' hl' hr'] at he₀
  have he_l : l = l' := by
    ext p b
    cases p with
    | succ p => exact congrArg Prod.fst (hrows p b)
    | zero =>
      cases b
      · exact congrArg Prod.fst (he₀ false)
      · have h := congrArg (fun t : Table M => t.row 0 false) (hl.trans hl'.symm)
        exact h
  have he_r : r = r' := by
    ext p b
    cases p with
    | succ p => exact congrArg (fun z => z.2.1) (hrows p b)
    | zero =>
      cases b
      · have h := congrArg (fun t : Table M => t.row 0 false) (hr.trans hr'.symm)
        exact h
      · exact congrArg Prod.snd (he₀ true)
  exact ⟨he_l,rfl,he_r⟩

lemma chainComparison_edges_injective (x y : (tensorFunctor.obj M.nu).Cell)
    (hx : (tensorFunctor.obj M.nu).source 1 x = x) (hy : (tensorFunctor.obj M.nu).source 1 y = y)
    (he : (chainComparison M).map x = (chainComparison M).map y) : x = y := by
  have hnx := tensor_edge_normal x hx
  have hny := tensor_edge_normal y hy
  cases hnx with
  | endpoint a x hx =>
    exact ((chainComparison_endpoint_fiber y a x).mp
      (he.symm.trans (chainComparison_endpoint_apply a x))).symm
  | crossing l c r hl hr hdl hdr =>
    cases hny with
    | endpoint a y hy =>
      exact (chainComparison_endpoint_fiber _ a y).mp (he.trans (chainComparison_endpoint_apply a y))
    | crossing l' c' r' hl' hr' hdl' hdr' =>
      obtain ⟨rfl,rfl,rfl⟩ := chainComparison_crossingEdge_injective l l' c c' r r' hl hr hl' hr' he
      rfl

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


namespace Thomason.DirectedComplex.CylinderTables
open Table
variable {M : DirectedComplex.{u}}

lemma tableSandwich_bounded (l c r : Table M)
    (hl : l.row 0 true = c.row 0 false) (hr : r.row 0 false = c.row 0 true)
    (hdl : truncate 2 false l = l) (hdc : truncate 1 false c = c) (hdr : truncate 2 false r = r) :
    truncate 2 false (tableSandwich l c r) = tableSandwich l c r := by
  have heL : M.cylinder.nu.source 2 ((M.cylinderEndpoint false).table l) =
      (M.cylinderEndpoint false).table l := by
    change truncate 2 false _ = _
    rw [← Hom.table_truncate, hdl]
  have heR : M.cylinder.nu.source 2 ((M.cylinderEndpoint true).table r) =
      (M.cylinderEndpoint true).table r := by
    change truncate 2 false _ = _
    rw [← Hom.table_truncate, hdr]
  exact GrayRecursive.IntervalHom.composite_bounded M.cylinder.nu (by omega : 0 < 2) _ _
    (GrayRecursive.IntervalHom.composite_bounded M.cylinder.nu (by omega : 0 < 2) _ _
      heL (GrayRecursive.vertical_fixed c hdc) (tableSandwich_match_left l c hl))
    heR (tableSandwich_match_right l c r hl hr)

section TwoCell
variable (hM : PositiveAcyclic M) (t : Table M.cylinder)
    (hs : label t false = 0) (ht : label t true = 1)

include hM

variable (hb : truncate 2 false t = t)
include hb

omit hM in
lemma profileCross_two_zero (b : Bool) : cross t 2 b = 0 :=
  cross_of_row_zero t 2 b (row_above_fixed t hb (by omega) b)

lemma twoRight_two (b : Bool) : (twoRight t hs ht).row 2 b = (0,side t true 2 b,0) := by
  rw [twoRight, tableSandwich_succ _ _ _ (twoRight_matches hM t hs ht).1 (twoRight_matches hM t hs ht).2]
  have hl := row_above_fixed _ (profileEdge_bounded t hs ht false false) (by omega : 1 < 2) b
  have hc := profileCross_two_zero t hb b
  simp only [hl, map_zero]
  change (0 : M.cylinder.Chain 2) + verticalRow _ 2 b +
    M.cylinderEndpointMap true 2 (rightProfileRow t 2 b) = _
  cases b <;>
    simp [verticalRow, truncate_row, rightProfileRow, hc, cylinderEndpointMap]

lemma twoMiddle_two (b : Bool) : (twoMiddle t hs ht).row 2 b = (0,0,cross t 1 b) := by
  rw [twoMiddle, tableSandwich_succ _ _ _ (twoMiddle_matches hM t hs ht).1 (twoMiddle_matches hM t hs ht).2]
  have hl := row_above_fixed _ (profileEdge_bounded t hs ht false false) (by omega : 1 < 2) b
  have hr := row_above_fixed _ (profileEdge_bounded t hs ht true true) (by omega : 1 < 2) b
  simp only [hl, hr, map_zero, zero_add, add_zero]
  change verticalRow (crossingProfile t hs ht) 2 b = _
  have hc := profileCross_two_zero t hb b
  cases b <;> simp [verticalRow, crossingProfile, hc]

lemma twoLeft_two (b : Bool) : (twoLeft t hs ht).row 2 b = (side t false 2 b,0,0) := by
  rw [twoLeft, tableSandwich_succ _ _ _ (twoLeft_matches hM t hs ht).1 (twoLeft_matches hM t hs ht).2]
  have hr := row_above_fixed _ (profileEdge_bounded t hs ht true true) (by omega : 1 < 2) b
  have hc := profileCross_two_zero t hb b
  simp only [hr, map_zero, add_zero]
  change M.cylinderEndpointMap false 2 (leftProfileRow t 2 b) + verticalRow _ 2 b = _
  cases b <;> simp [verticalRow, truncate_row, leftProfileRow, hc, cylinderEndpointMap]

omit hM hb in
lemma profileEdge_bounded_two (_hM : PositiveAcyclic M) (t : Table M.cylinder)
    (hs : label t false = 0) (ht : label t true = 1)
    (_hb : truncate 2 false t = t) (a b : Bool) :
    truncate 2 false (profileEdge t hs ht a b) = profileEdge t hs ht a b :=
  M.nu.source_fixed_upwards (by omega : 1 ≤ 2) (profileEdge_bounded t hs ht a b)

lemma twoRight_bounded : truncate 2 false (twoRight t hs ht) = twoRight t hs ht :=
  tableSandwich_bounded _ _ _ (twoRight_matches hM t hs ht).1 (twoRight_matches hM t hs ht).2
    (profileEdge_bounded_two hM t hs ht hb false false)
    (by simp only [truncate_truncate, Nat.not_lt_zero, ite_false])
    (rightProfile_bounded t hs ht hb)

lemma twoMiddle_bounded : truncate 2 false (twoMiddle t hs ht) = twoMiddle t hs ht :=
  tableSandwich_bounded _ _ _ (twoMiddle_matches hM t hs ht).1 (twoMiddle_matches hM t hs ht).2
    (profileEdge_bounded_two hM t hs ht hb false false) (crossingProfile_bounded t hs ht hb)
    (profileEdge_bounded_two hM t hs ht hb true true)

lemma twoLeft_bounded : truncate 2 false (twoLeft t hs ht) = twoLeft t hs ht :=
  tableSandwich_bounded _ _ _ (twoLeft_matches hM t hs ht).1 (twoLeft_matches hM t hs ht).2
    (leftProfile_bounded t hs ht hb)
    (by simp only [truncate_truncate, Nat.not_lt_zero, ite_false])
    (profileEdge_bounded_two hM t hs ht hb true true)

omit hM hb in
lemma twoRight_source (hM : PositiveAcyclic M) (t : Table M.cylinder)
    (hs : label t false = 0) (ht : label t true = 1) (_hb : truncate 2 false t = t) :
    truncate 1 false (twoRight t hs ht) = truncate 1 false t := by
  apply truncate_one_ext
  · exact twoRight_zero hM t hs ht
  · rw [twoRight_one hM t hs ht]
    simp only [Bool.false_eq_true, ite_false, add_zero]
    rfl

lemma crossing_two_factor :
    comp 1 (comp 1 (twoRight t hs ht) (twoMiddle t hs ht) (twoRightMiddle_match hM t hs ht hb))
      (twoLeft t hs ht) (twoRightMiddleLeft_match hM t hs ht hb) = t := by
  apply ext_source_top (comp_dimension (by omega : 1 < 2)
    (comp_dimension (by omega : 1 < 2) (twoRight_bounded hM t hs ht hb)
      (twoMiddle_bounded hM t hs ht hb) _) (twoLeft_bounded hM t hs ht hb) _) hb
  · rw [source_comp_le 1 1 le_rfl, source_comp_le 1 1 le_rfl]
    exact twoRight_source hM t hs ht hb
  · simp only [comp_row, show ¬2 < 1 by omega, show (2 : ℕ) ≠ 1 by omega, ite_false]
    rw [twoRight_two hM t hs ht hb, twoMiddle_two hM t hs ht hb, twoLeft_two hM t hs ht hb]
    simp only [Prod.mk_add_mk, add_zero, zero_add]
    rfl

end TwoCell
end Thomason.DirectedComplex.CylinderTables

end

noncomputable section
universe u v w z


namespace Thomason.GrayRecursive.IntervalHom
open CategoryTheory DirectedComplex DirectedComplex.Table OmegaCategory
open CylinderTables
variable {M : DirectedComplex.{u}}

lemma TwoLiftable.endpoint (a : Bool) (t : Table M) (ht : truncate 2 false t = t) :
    TwoLiftable ((M.cylinderEndpoint a).table t) := by
  refine ⟨((tensorEndpoint a).app M.nu).map t, ?_, chainComparison_endpoint_apply a t⟩
  erw [← ((tensorEndpoint a).app M.nu).map_source]
  exact congrArg ((tensorEndpoint a).app M.nu).map ht

lemma TwoLiftable.vertical (t : Table M) (ht : truncate 1 false t = t) :
    TwoLiftable (verticalTable t) := by
  refine ⟨(generatorCylinder (X := M.nu) 1 ⟨t,ht⟩).map (verticalTable (GlobeComplex.topTable 1)), ?_, ?_⟩
  · exact ((generatorCylinder (X := M.nu) 1 ⟨t,ht⟩).map_source 2 _).symm.trans
      (congrArg (generatorCylinder (X := M.nu) 1 ⟨t,ht⟩).map
        (vertical_fixed _ (GlobeComplex.topTable_bounded 1)))
  · change (chainComparison M).map ((tensorPresentation M.nu).generator ⟨1,⟨t,ht⟩,_⟩) = _
    erw [chainComparison_generator,tableCylinder_vertical,ht]

lemma TwoLiftable.comp {a b : Table M.cylinder} (ha : TwoLiftable a) (hb : TwoLiftable b)
    (k : ℕ) (hk : k ≤ 1) (h : truncate k true a = truncate k false b) :
    TwoLiftable (DirectedComplex.Table.comp k a b h) := by
  obtain ⟨x,hx,rfl⟩ := ha
  obtain ⟨y,hy,rfl⟩ := hb
  have hm : (tensorFunctor.obj M.nu).target k x = (tensorFunctor.obj M.nu).source k y := by
    apply chainComparison_edges_injective
    · exact (tensorFunctor.obj M.nu).source_fixed_upwards hk
        ((tensorFunctor.obj M.nu).source_target_self k x)
    · exact (tensorFunctor.obj M.nu).source_fixed_upwards hk
        ((tensorFunctor.obj M.nu).source_source_self k y)
    · rw [(chainComparison M).map_target, (chainComparison M).map_source]
      exact h
  refine ⟨(tensorFunctor.obj M.nu).comp k x y hm, ?_, ?_⟩
  · rw [← (tensorFunctor.obj M.nu).join_eq k x y hm]
    exact composite_bounded _ (by omega : k < 2) x y hx hy hm
  · exact (chainComparison M).map_comp k x y hm h

lemma TwoLiftable.join {a b : Table M.cylinder} (ha : TwoLiftable a) (hb : TwoLiftable b)
    (k : ℕ) (hk : k ≤ 1) (h : truncate k true a = truncate k false b) :
    TwoLiftable (M.cylinder.nu.join k a b) := by
  rw [M.cylinder.nu.join_eq k a b h]
  exact ha.comp hb k hk h

lemma TwoLiftable.sandwich (l c r : Table M)
    (hl : l.row 0 true = c.row 0 false) (hr : r.row 0 false = c.row 0 true)
    (hdl : truncate 2 false l = l) (hdc : truncate 1 false c = c) (hdr : truncate 2 false r = r) :
    TwoLiftable (tableSandwich l c r) :=
  ((TwoLiftable.endpoint false l hdl).join (TwoLiftable.vertical c hdc) 0 (by omega)
    (tableSandwich_match_left l c hl)).join (TwoLiftable.endpoint true r hdr) 0 (by omega)
    (tableSandwich_match_right l c r hl hr)

theorem chainComparison_crossing_twocells_surjective (hM : PositiveAcyclic M)
    (t : Table M.cylinder) (hs : label t false = 0) (ht : label t true = 1)
    (hb : truncate 2 false t = t) : TwoLiftable t := by
  have hr : TwoLiftable (twoRight t hs ht) :=
    TwoLiftable.sandwich _ _ _ (twoRight_matches hM t hs ht).1 (twoRight_matches hM t hs ht).2
      (profileEdge_bounded_two hM t hs ht hb false false)
      (by simp only [truncate_truncate, Nat.not_lt_zero, ite_false]) (rightProfile_bounded t hs ht hb)
  have hc : TwoLiftable (twoMiddle t hs ht) :=
    TwoLiftable.sandwich _ _ _ (twoMiddle_matches hM t hs ht).1 (twoMiddle_matches hM t hs ht).2
      (profileEdge_bounded_two hM t hs ht hb false false) (crossingProfile_bounded t hs ht hb)
      (profileEdge_bounded_two hM t hs ht hb true true)
  have hl : TwoLiftable (twoLeft t hs ht) :=
    TwoLiftable.sandwich _ _ _ (twoLeft_matches hM t hs ht).1 (twoLeft_matches hM t hs ht).2
      (leftProfile_bounded t hs ht hb) (by simp only [truncate_truncate, Nat.not_lt_zero, ite_false])
      (profileEdge_bounded_two hM t hs ht hb true true)
  rw [← crossing_two_factor hM t hs ht hb]
  exact (hr.comp hc 1 le_rfl (twoRightMiddle_match hM t hs ht hb)).comp hl 1 le_rfl
    (twoRightMiddleLeft_match hM t hs ht hb)

theorem chainComparison_twocells_surjective (hM : PositiveAcyclic M) :
    Function.Surjective ((chainComparison M).onCells 2) := by
  intro t
  have hl : TwoLiftable t.val := by
    rcases endpoint_or_crossing hM t.val with ⟨a,ha⟩ | ⟨hs,ht⟩
    · rw [ha]
      apply TwoLiftable.endpoint
      change truncate 2 false (M.cylinderProjection.table t.val) = _
      erw [← Hom.table_truncate, show truncate 2 false t.val = t.val from t.property]
      rfl
    · exact chainComparison_crossing_twocells_surjective hM t.val hs ht t.property
  obtain ⟨x,hx,he⟩ := hl
  exact ⟨⟨x,hx⟩,Subtype.ext he⟩

end Thomason.GrayRecursive.IntervalHom

end

noncomputable section
universe u v w z


namespace Thomason.GrayRecursive.IntervalHom
open CategoryTheory DirectedComplex DirectedComplex.Table GlobeComplex OmegaCategory

variable {X Y : OmegaCategory.{u}} {M : DirectedComplex.{u}}

lemma verticalCell_natural (F : X ⟶ Y) (n : ℕ) (x : X.Cells n) :
    (tensorFunctor.map F).map (verticalCell n x) = verticalCell n (F.onCells n x) :=
  tensorFunctor_map_generator F n x (verticalTable (topTable n))

lemma chainComparison_verticalCell (n : ℕ) (x : M.nu.Cells n) :
    (chainComparison M).map (verticalCell n x) = verticalTable x.val := by
  change (chainComparison M).map ((tensorPresentation M.nu).generator ⟨n,x,_⟩) = _
  erw [chainComparison_generator,tableCylinder_vertical]
  exact congrArg verticalTable x.property

lemma vertical_one_face (a : Bool) :
    truncate 1 a (verticalTable (topTable.{u} 1)) =
      if a then (K.{u} 1).nu.join 0 (atEnd false (topTable 1)) (verticalTable (vertex 0 true))
      else (K.{u} 1).nu.join 0 (verticalTable (vertex 0 false)) (atEnd true (topTable 1)) := by
  rw [← suspendTable_top 0, ← up_vertical, ← up_truncate]
  rw [CylinderTables.vertical_object_face _ (topTable_bounded 0)]
  cases a
  · change up (atEnd false (topTable 0)) = _
    rw [up_endpoint_false]
    exact ((K 1).nu.join_eq 0 _ _ (up_endpoint_left_matching (topTable 0))).symm
  · change up (atEnd true (topTable 0)) = _
    rw [up_endpoint_true]
    exact ((K 1).nu.join_eq 0 _ _ (up_endpoint_right_matching (topTable 0))).symm

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

lemma generatorCylinder_vertical_vertex (n : ℕ) (x : X.Cells (n+1)) (a : Bool) :
    (generatorCylinder (n+1) x).map (verticalTable (vertex n a)) =
      verticalObject ⟨X.face 0 a x.val, by cases a; exact X.source_source_self 0 x.val; exact X.source_target_self 0 x.val⟩ := by
  let v : X.Objects := ⟨X.face 0 a x.val, by cases a; exact X.source_source_self 0 x.val; exact X.source_target_self 0 x.val⟩
  have he := tensorUnitCell_face 0 a x.val
  rw [tensorUnitCell_of_bounded (n+1) x, face_ofMap] at he
  change tensorUnitCell v.val = _ at he
  rw [tensorUnitCell_of_bounded 0 v] at he
  have h := congrArg (fun t => (eval 0 t).map (verticalTable (topTable 0))) he
  rw [eval_ofMap_self, eval_ofMap_self, restrictCylinder_zero_vertical] at h
  exact h.symm

lemma verticalCell_one_face (x : X.Cells 1) (a : Bool) :
    (tensorFunctor.obj X).face 1 a (verticalCell 1 x) =
      if a then (tensorFunctor.obj X).join 0 (((tensorEndpoint false).app X).map x.val)
        (verticalObject ⟨X.target 0 x.val, X.source_target_self 0 x.val⟩)
      else (tensorFunctor.obj X).join 0
        (verticalObject ⟨X.source 0 x.val, X.source_source_self 0 x.val⟩)
        (((tensorEndpoint true).app X).map x.val) := by
  unfold verticalCell
  erw [← (generatorCylinder 1 x).map_face]
  have hh : (K.{u} 1).nu.face 1 a (verticalTable (topTable 1)) =
      truncate 1 a (verticalTable (topTable 1)) := by cases a <;> rfl
  rw [hh,vertical_one_face]
  cases a
  · simp only [Bool.false_eq_true, ite_false]
    erw [(generatorCylinder 1 x).map_join 0 _ _ (by
        change truncate 0 true (verticalTable (vertex 0 false)) = truncate 0 false (atEnd true (topTable 1))
        rw [← suspendTable_top 0]
        exact up_endpoint_left_matching (topTable 0)),
      generatorCylinder_endpoint,lift_top,generatorCylinder_vertical_vertex]
    rfl
  · simp only [ite_true]
    erw [(generatorCylinder 1 x).map_join 0 _ _ (by
        change truncate 0 true (atEnd false (topTable 1)) = truncate 0 false (verticalTable (vertex 0 true))
        rw [← suspendTable_top 0]
        exact up_endpoint_right_matching (topTable 0)),
      generatorCylinder_endpoint,lift_top,generatorCylinder_vertical_vertex]
    rfl

lemma generatorCylinder_comp {n k : ℕ} (hk : k < n) (x y : X.Cells n)
    (h : X.target k x.val = X.source k y.val) :
    generatorCylinder n (X.gradedComp hk x y h) =
      pasteCylinder hk (generatorCylinder n x) (generatorCylinder n y)
        (generatorCylinder_matching x y h) := by
  apply ofMap_injective
  rw [← tensorUnitCell_of_bounded n (X.gradedComp hk x y h)]
  have h' : face k true (tensorUnitCell x.val) = face k false (tensorUnitCell y.val) := by
    rw [← tensorUnitCell_face k true, ← tensorUnitCell_face k false]
    exact congrArg tensorUnitCell h
  change tensorUnitCell (X.comp k x.val y.val h) = _
  rw [tensorUnitCell_comp k x.val y.val h h']
  change comp k (tensorUnitCell x.val) (tensorUnitCell y.val) h' = _
  simp only [tensorUnitCell_of_bounded n x,tensorUnitCell_of_bounded n y]
  exact comp_ofMap hk _ _ _

lemma verticalCell_one_comp (x y : X.Cells 1) (h : X.target 0 x.val = X.source 0 y.val) :
    verticalCell 1 (X.gradedComp (by omega : 0 < 1) x y h) =
      (tensorFunctor.obj X).join 1
        ((tensorFunctor.obj X).join 0 (verticalCell 1 x) (((tensorEndpoint true).app X).map y.val))
        ((tensorFunctor.obj X).join 0 (((tensorEndpoint false).app X).map x.val) (verticalCell 1 y)) := by
  unfold verticalCell
  rw [generatorCylinder_comp, ← suspendTable_top 0, ← up_vertical, pasteCylinder_zero_up,
    concatInterval_zero_vertical]
  rw [hom_join_val _ _ _ (zero_interval_seam _ _
    ((rectangleDiagramOfFunctor (generatorCylinder 1 x)).horizontalDiagonal_matching
      (rectangleDiagramOfFunctor (generatorCylinder 1 y))
      (zeroFaceMatching_seam (generatorCylinder_matching x y h))))]
  erw [RectangleDiagram.horizontalDiagonalOne_map,RectangleDiagram.horizontalDiagonalTwo_map,
    project_zero_vertical,suspendTable_top]
  change (tensorFunctor.obj X).join 1
    ((tensorFunctor.obj X).join 0 ((generatorCylinder 1 x).map (up (verticalTable (topTable 0))))
      ((generatorCylinder 1 y).map (atEnd true (topTable 1))))
    ((tensorFunctor.obj X).join 0 ((generatorCylinder 1 x).map (atEnd false (topTable 1)))
      ((generatorCylinder 1 y).map (up (verticalTable (topTable 0))))) = _
  rw [up_vertical,suspendTable_top,generatorCylinder_endpoint,generatorCylinder_endpoint,lift_top,lift_top]
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
-- module Solutions.OAIQ043_TH.Thomason_TwoCellExchange
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Two Cell Exchange. -/

noncomputable section
universe u v w z


namespace Thomason.GrayRecursive.IntervalHom
open CategoryTheory DirectedComplex DirectedComplex.Table GlobeComplex OmegaCategory

variable {X : OmegaCategory.{u}}

lemma crossingEdge_source_one (l : X.Cell) (c : X.Objects) (r : X.Cell)
    (hl : X.target 0 l = c.val) (hr : X.source 0 r = c.val) :
    (tensorFunctor.obj X).source 1 (crossingEdge l c r) =
      crossingEdge (X.source 1 l) c (X.source 1 r) := by
  unfold crossingEdge
  rw [(tensorFunctor.obj X).join_source_gt 1 0 _ _ (by omega)
      (crossingEdge_right_matching l c r hl hr),
    (tensorFunctor.obj X).join_source_gt 1 0 _ _ (by omega)
      (crossingEdge_left_matching l c hl),
    endpoint_source, endpoint_source, verticalObject_bounded]

lemma crossingEdge_target_one (l : X.Cell) (c : X.Objects) (r : X.Cell)
    (hl : X.target 0 l = c.val) (hr : X.source 0 r = c.val) :
    (tensorFunctor.obj X).target 1 (crossingEdge l c r) =
      crossingEdge (X.target 1 l) c (X.target 1 r) := by
  unfold crossingEdge
  rw [(tensorFunctor.obj X).join_target_gt 1 0 _ _ (by omega)
      (crossingEdge_right_matching l c r hl hr),
    (tensorFunctor.obj X).join_target_gt 1 0 _ _ (by omega)
      (crossingEdge_left_matching l c hl),
    endpoint_target, endpoint_target,
    (tensorFunctor.obj X).target_eq_self_of_source_eq_self (verticalObject_bounded c)]

namespace CrossingSquare
variable (D : CrossingSquare X)

lemma vertical_source_zero (a : X.Cells 1) :
    (tensorFunctor.obj X).source 0 (verticalCell 1 a) =
      ((tensorEndpoint false).app X).map (X.source 0 a.val) := by
  have h := congrArg ((tensorFunctor.obj X).source 0) (verticalCell_one_face a false)
  change (tensorFunctor.obj X).source 0 ((tensorFunctor.obj X).source 1 (verticalCell 1 a)) = _ at h
  rw [(tensorFunctor.obj X).source_source, min_eq_left (by omega : 0 ≤ 1)] at h
  simp only [Bool.false_eq_true, ite_false] at h
  have hm : (tensorFunctor.obj X).target 0
      (verticalObject ⟨X.source 0 a.val, X.source_source_self 0 a.val⟩) =
      (tensorFunctor.obj X).source 0 (((tensorEndpoint true).app X).map a.val) := by
    erw [verticalObject_target, endpoint_source]
  erw [(tensorFunctor.obj X).join_source_le 0 0 _ _ le_rfl hm, verticalObject_source] at h
  exact h

lemma vertical_target_zero (a : X.Cells 1) :
    (tensorFunctor.obj X).target 0 (verticalCell 1 a) =
      ((tensorEndpoint true).app X).map (X.target 0 a.val) := by
  have h := congrArg ((tensorFunctor.obj X).target 0) (verticalCell_one_face a true)
  change (tensorFunctor.obj X).target 0 ((tensorFunctor.obj X).target 1 (verticalCell 1 a)) = _ at h
  rw [(tensorFunctor.obj X).target_target, min_eq_left (by omega : 0 ≤ 1)] at h
  simp only [ite_true] at h
  have hm : (tensorFunctor.obj X).target 0 (((tensorEndpoint false).app X).map a.val) =
      (tensorFunctor.obj X).source 0
        (verticalObject ⟨X.target 0 a.val, X.source_target_self 0 a.val⟩) := by
    erw [verticalObject_source, endpoint_target]
  erw [(tensorFunctor.obj X).join_target_le 0 0 _ _ le_rfl hm, verticalObject_target] at h
  exact h

lemma middle_matching_left :
    (tensorFunctor.obj X).target 0 (((tensorEndpoint false).app X).map D.left.val) =
      (tensorFunctor.obj X).source 0 (verticalCell 1 D.cross) := by
  rw [endpoint_target, vertical_source_zero, D.lc]

lemma middle_matching_right :
    (tensorFunctor.obj X).target 0
      ((tensorFunctor.obj X).join 0 (((tensorEndpoint false).app X).map D.left.val)
        (verticalCell 1 D.cross)) =
      (tensorFunctor.obj X).source 0 (((tensorEndpoint true).app X).map D.right.val) := by
  rw [(tensorFunctor.obj X).join_target_le 0 0 _ _ le_rfl D.middle_matching_left,
    vertical_target_zero, endpoint_source, D.cr]

lemma middle_source : (tensorFunctor.obj X).source 1 D.middle =
    crossingEdge D.left.val D.entry (X.join 0 D.cross.val D.right.val) := by
  unfold middle
  rw [(tensorFunctor.obj X).join_source_gt 1 0 _ _ (by omega) D.middle_matching_right,
    (tensorFunctor.obj X).join_source_gt 1 0 _ _ (by omega) D.middle_matching_left,
    endpoint_source, D.left.property, endpoint_source, D.right.property]
  change (tensorFunctor.obj X).join 0
    ((tensorFunctor.obj X).join 0 _ ((tensorFunctor.obj X).face 1 false (verticalCell 1 D.cross))) _ = _
  rw [verticalCell_one_face]
  simp only [Bool.false_eq_true, ite_false]
  unfold crossingEdge
  have hv : (tensorFunctor.obj X).target 0 (verticalObject D.entry) =
      (tensorFunctor.obj X).source 0 (((tensorEndpoint true).app X).map D.cross.val) := by
    rw [verticalObject_target, endpoint_source]
  rw [← (tensorFunctor.obj X).join_assoc 0 _ _ _
      (crossingEdge_left_matching D.left.val D.entry D.lc) hv,
    (tensorFunctor.obj X).join_assoc 0 _ _ _
      (crossingEdge_right_matching D.left.val D.entry D.cross.val D.lc rfl)
      (((tensorEndpoint true).app X).map_composable D.cr),
    ← ((tensorEndpoint true).app X).map_join 0 _ _ D.cr]
  rfl

lemma middle_target : (tensorFunctor.obj X).target 1 D.middle =
    crossingEdge (X.join 0 D.left.val D.cross.val) D.exit D.right.val := by
  unfold middle
  rw [(tensorFunctor.obj X).join_target_gt 1 0 _ _ (by omega) D.middle_matching_right,
    (tensorFunctor.obj X).join_target_gt 1 0 _ _ (by omega) D.middle_matching_left,
    endpoint_target, X.target_eq_self_of_source_eq_self D.left.property,
    endpoint_target, X.target_eq_self_of_source_eq_self D.right.property]
  change (tensorFunctor.obj X).join 0
    ((tensorFunctor.obj X).join 0 _ ((tensorFunctor.obj X).face 1 true (verticalCell 1 D.cross))) _ = _
  rw [verticalCell_one_face]
  simp only [ite_true]
  unfold crossingEdge
  have hv : (tensorFunctor.obj X).target 0 (((tensorEndpoint false).app X).map D.cross.val) =
      (tensorFunctor.obj X).source 0 (verticalObject D.exit) := by
    rw [verticalObject_source, endpoint_target]
  rw [← (tensorFunctor.obj X).join_assoc 0 _ _ _
      (((tensorEndpoint false).app X).map_composable D.lc) hv,
    ← ((tensorEndpoint false).app X).map_join 0 _ _ D.lc]
  rfl

lemma first_source : (tensorFunctor.obj X).source 1 D.first =
    crossingEdge D.left.val D.entry (X.source 1 D.right₂.val) := by
  rw [first, crossingEdge_source_one _ _ _ D.lc D.right₂_source_zero, D.left.property]

lemma first_target : (tensorFunctor.obj X).target 1 D.first =
    crossingEdge D.left.val D.entry (X.join 0 D.cross.val D.right.val) := by
  rw [first, crossingEdge_target_one _ _ _ D.lc D.right₂_source_zero,
    X.target_eq_self_of_source_eq_self D.left.property, D.right_target]

lemma last_source : (tensorFunctor.obj X).source 1 D.last =
    crossingEdge (X.join 0 D.left.val D.cross.val) D.exit D.right.val := by
  rw [last, crossingEdge_source_one _ _ _ D.left₂_target_zero D.cr.symm,
    D.right.property, D.left_source]

lemma last_target : (tensorFunctor.obj X).target 1 D.last =
    crossingEdge (X.target 1 D.left₂.val) D.exit D.right.val := by
  rw [last, crossingEdge_target_one _ _ _ D.left₂_target_zero D.cr.symm,
    X.target_eq_self_of_source_eq_self D.right.property]

lemma first_middle : (tensorFunctor.obj X).target 1 D.first =
    (tensorFunctor.obj X).source 1 D.middle := D.first_target.trans D.middle_source.symm

lemma middle_last : (tensorFunctor.obj X).target 1 D.middle =
    (tensorFunctor.obj X).source 1 D.last := D.middle_target.trans D.last_source.symm

lemma firstMiddle_last : (tensorFunctor.obj X).target 1
    ((tensorFunctor.obj X).join 1 D.first D.middle) = (tensorFunctor.obj X).source 1 D.last := by
  rw [(tensorFunctor.obj X).join_target_le 1 1 _ _ le_rfl D.first_middle]
  exact D.middle_last

lemma source_one : (tensorFunctor.obj X).source 1 D.value =
    crossingEdge D.left.val D.entry (X.source 1 D.right₂.val) := by
  rw [value, (tensorFunctor.obj X).join_source_le 1 1 _ _ le_rfl D.firstMiddle_last,
    (tensorFunctor.obj X).join_source_le 1 1 _ _ le_rfl D.first_middle, D.first_source]

lemma target_one : (tensorFunctor.obj X).target 1 D.value =
    crossingEdge (X.target 1 D.left₂.val) D.exit D.right.val := by
  rw [value, (tensorFunctor.obj X).join_target_le 1 1 _ _ le_rfl D.firstMiddle_last, D.last_target]

end CrossingSquare
end Thomason.GrayRecursive.IntervalHom

end

noncomputable section
universe u v w z


namespace Thomason.GrayRecursive.IntervalHom
open CategoryTheory DirectedComplex DirectedComplex.Table GlobeComplex OmegaCategory
open CylinderTables

variable {M : DirectedComplex.{u}}
lemma table_join_row_above (k p : ℕ) (hkp : k < p) (x y : Table M)
    (h : truncate k true x = truncate k false y) (b : Bool) :
    (M.nu.join k x y).row p b = x.row p b + y.row p b := by
  rw [M.nu.join_eq k x y h]
  change (DirectedComplex.Table.comp k x y h).row p b = _
  simp only [comp_row, show ¬p < k by omega, Ne.symm hkp.ne, ite_false]

namespace CrossingSquare

variable (D : CrossingSquare M.nu)

lemma image_middle : (chainComparison M).map D.middle =
    tableSandwich D.left.val D.cross.val D.right.val := by
  unfold middle tableSandwich
  erw [(chainComparison M).map_join 0 _ _ D.middle_matching_right,
    (chainComparison M).map_join 0 _ _ D.middle_matching_left,
    chainComparison_endpoint_apply false D.left.val,
    chainComparison_endpoint_apply true D.right.val,
    chainComparison_verticalCell 1 D.cross]

lemma image_first : (chainComparison M).map D.first =
    tableSandwich D.left.val D.entry.val D.right₂.val :=
  chainComparison_crossingEdge D.left.val D.entry D.right₂.val D.lc D.right₂_source_zero

lemma image_last : (chainComparison M).map D.last =
    tableSandwich D.left₂.val D.exit.val D.right.val :=
  chainComparison_crossingEdge D.left₂.val D.exit D.right.val D.left₂_target_zero D.cr.symm

lemma image_two (b : Bool) :
    ((chainComparison M).map D.value).row 2 b =
      (D.left₂.val.row 2 b, D.right₂.val.row 2 b, D.cross.val.row 1 b) := by
  have hl : D.left.val.row 0 true = D.cross.val.row 0 false :=
    congrArg (fun t : Table M => t.row 0 false) D.lc
  have hr : D.right.val.row 0 false = D.cross.val.row 0 true :=
    congrArg (fun t : Table M => t.row 0 false) D.cr.symm
  have hleft := row_above_fixed D.left.val D.left.property (by omega : 1 < 2) b
  have hright := row_above_fixed D.right.val D.right.property (by omega : 1 < 2) b
  have hcross := row_above_fixed D.cross.val D.cross.property (by omega : 1 < 2) b
  have hv : verticalRow D.cross.val 2 b = (0, 0, D.cross.val.row 1 b) := by
    cases b <;> simp [verticalRow, hcross]
  unfold value
  rw [(chainComparison M).map_join 1 _ _ D.firstMiddle_last,
    (chainComparison M).map_join 1 _ _ D.first_middle]
  erw [table_join_row_above 1 2 (by omega) _ _ ?_ b,
    table_join_row_above 1 2 (by omega) _ _ ((chainComparison M).map_composable D.first_middle) b]
  rotate_left
  · have hm := (chainComparison M).map_composable D.firstMiddle_last
    rw [(chainComparison M).map_join 1 _ _ D.first_middle] at hm
    exact hm
  rw [show D.first = crossingEdge D.left.val D.entry D.right₂.val from rfl,
    show D.last = crossingEdge D.left₂.val D.exit D.right.val from rfl,
    chainComparison_crossingEdge_row_succ D.left.val D.entry D.right₂.val D.lc D.right₂_source_zero,
    chainComparison_crossingEdge_row_succ D.left₂.val D.exit D.right.val D.left₂_target_zero D.cr.symm,
    D.image_middle,
    tableSandwich_succ _ _ _ hl hr]
  have hs : D.entry.val.row 1 b = 0 :=
    row_above_fixed D.entry.val D.entry.property (by omega : 0 < 1) b
  have ht : D.exit.val.row 1 b = 0 :=
    row_above_fixed D.exit.val D.exit.property (by omega : 0 < 1) b
  rw [hleft, hright, hs, ht, hv]
  change (0, D.right₂.val.row 2 b, 0) +
    ((0 : M.cylinder.Chain 2) + (0, 0, D.cross.val.row 1 b) + 0) +
      (D.left₂.val.row 2 b, 0, 0) = _
  simp only [Prod.mk_add_mk, add_zero, zero_add]

theorem image_ext (E : CrossingSquare M.nu)
    (h : (chainComparison M).map D.value = (chainComparison M).map E.value) : D = E := by
  have hs := congrArg (M.cylinder.nu.source 1) h
  rw [← (chainComparison M).map_source, ← (chainComparison M).map_source,
    D.source_one, E.source_one] at hs
  have hr (A : CrossingSquare M.nu) :
      truncate 0 false (truncate 1 false A.right₂.val) = A.entry.val := by
    change M.nu.source 0 (M.nu.source 1 A.right₂.val) = _
    rw [M.nu.source_source, min_eq_left (by omega : 0 ≤ 1)]
    exact A.right₂_source_zero
  obtain ⟨hl, hc₀, hR₀⟩ := chainComparison_crossingEdge_injective
    D.left.val E.left.val D.entry E.entry (truncate 1 false D.right₂.val) (truncate 1 false E.right₂.val)
    D.lc (hr D) E.lc (hr E) hs
  have ht := congrArg (M.cylinder.nu.target 1) h
  rw [← (chainComparison M).map_target, ← (chainComparison M).map_target,
    D.target_one, E.target_one] at ht
  have hl' (A : CrossingSquare M.nu) :
      truncate 0 true (truncate 1 true A.left₂.val) = A.exit.val := by
    change M.nu.target 0 (M.nu.target 1 A.left₂.val) = _
    rw [M.nu.target_target, min_eq_left (by omega : 0 ≤ 1)]
    exact A.left₂_target_zero
  obtain ⟨_, _, hr'⟩ := chainComparison_crossingEdge_injective
    (truncate 1 true D.left₂.val) (truncate 1 true E.left₂.val) D.exit E.exit D.right.val E.right.val
    (hl' D) D.cr.symm (hl' E) E.cr.symm ht
  have htop := congrArg (fun t : Table M.cylinder => t.row 2 false) h
  rw [D.image_two, E.image_two] at htop
  have hc : D.cross = E.cross := by
    apply Subtype.ext
    apply ext_source_top D.cross.property E.cross.property
    · exact congrArg Subtype.val hc₀
    · exact congrArg (fun x => x.2.2) htop
  have hL : D.left₂ = E.left₂ := by
    apply Subtype.ext
    apply ext_source_top D.left₂.property E.left₂.property
    · change M.nu.source 1 D.left₂.val = M.nu.source 1 E.left₂.val
      rw [D.left_source, E.left_source, hl, hc]
    · exact congrArg Prod.fst htop
  have hR : D.right₂ = E.right₂ := by
    apply Subtype.ext
    apply ext_source_top D.right₂.property E.right₂.property
    · exact hR₀
    · exact congrArg (fun x => x.2.1) htop
  have hl'' : D.left = E.left := Subtype.ext hl
  have hr'' : D.right = E.right := Subtype.ext hr'
  cases D
  cases E
  cases hl''
  cases hc
  cases hr''
  cases hL
  cases hR
  rfl

end CrossingSquare
end Thomason.GrayRecursive.IntervalHom

end

noncomputable section
universe u v w z


namespace Thomason.GrayRecursive.IntervalHom
open CategoryTheory DirectedComplex DirectedComplex.Table GlobeComplex OmegaCategory
open CylinderTables

variable {M : DirectedComplex.{u}}
namespace CrossingSquare

lemma image_ofTable (hM : PositiveAcyclic M) (t : M.cylinder.nu.Cells 2)
    (hs : label t.val false = 0) (ht : label t.val true = 1) :
    (chainComparison M).map (ofTable hM t hs ht).value = t.val := by
  let D := ofTable hM t hs ht
  have hR : (chainComparison M).map D.first = twoRight t.val hs ht := D.image_first
  have hC : (chainComparison M).map D.middle = twoMiddle t.val hs ht := D.image_middle
  have hL : (chainComparison M).map D.last = twoLeft t.val hs ht := D.image_last
  change (chainComparison M).map D.value = _
  rw [value, (chainComparison M).map_join 1 _ _ D.firstMiddle_last,
    (chainComparison M).map_join 1 _ _ D.first_middle, hR, hC, hL,
    M.cylinder.nu.join_eq 1 _ _ (twoRightMiddle_match hM t.val hs ht t.property)]
  erw [M.cylinder.nu.join_eq 1 _ _ (twoRightMiddleLeft_match hM t.val hs ht t.property)]
  exact crossing_two_factor hM t.val hs ht t.property

end CrossingSquare
end Thomason.GrayRecursive.IntervalHom

end

noncomputable section
universe u v w z


namespace Thomason.GrayRecursive.IntervalHom
open CategoryTheory DirectedComplex DirectedComplex.Table GlobeComplex OmegaCategory

variable {X : OmegaCategory.{u}}

lemma crossingEdge_comp_right (l : X.Cells 1) (c : X.Objects) (r s : X.Cell)
    (hl : X.target 0 l.val = c.val) (hr : X.source 0 r = c.val)
    (hs : X.source 0 s = c.val) (h : X.target 1 r = X.source 1 s) :
    crossingEdge l.val c (X.join 1 r s) =
      (tensorFunctor.obj X).join 1 (crossingEdge l.val c r) (crossingEdge l.val c s) := by
  unfold crossingEdge
  erw [((tensorEndpoint true).app X).map_join 1 r s h]
  apply (tensorFunctor.obj X).join_whisker_left 0 1 (by omega)
  · apply composite_bounded _ (by omega : 0 < 1) _ _ _
      (verticalObject_bounded c) (crossingEdge_left_matching l.val c hl)
    rw [endpoint_source, l.property]
  · exact ((tensorEndpoint true).app X).map_composable h
  · exact crossingEdge_right_matching l.val c r hl hr
  · exact crossingEdge_right_matching l.val c s hl hs

lemma crossingEdge_comp_left (l s : X.Cell) (c : X.Objects) (r : X.Cells 1)
    (hl : X.target 0 l = c.val) (hs : X.target 0 s = c.val)
    (hr : X.source 0 r.val = c.val) (h : X.target 1 l = X.source 1 s) :
    crossingEdge (X.join 1 l s) c r.val =
      (tensorFunctor.obj X).join 1 (crossingEdge l c r.val) (crossingEdge s c r.val) := by
  unfold crossingEdge
  erw [((tensorEndpoint false).app X).map_join 1 l s h,
    (tensorFunctor.obj X).join_whisker_right 0 1 (by omega) _ _ _
      (verticalObject_bounded c) (((tensorEndpoint false).app X).map_composable h)
      (crossingEdge_left_matching l c hl) (crossingEdge_left_matching s c hs)]
  apply (tensorFunctor.obj X).join_whisker_right 0 1 (by omega)
  · rw [endpoint_source, r.property]
  · rw [(tensorFunctor.obj X).join_target_gt 1 0 _ _ (by omega)
        (crossingEdge_left_matching l c hl),
      (tensorFunctor.obj X).join_source_gt 1 0 _ _ (by omega)
        (crossingEdge_left_matching s c hs), endpoint_target, endpoint_source,
      h, verticalObject_bounded,
      (tensorFunctor.obj X).target_eq_self_of_source_eq_self (verticalObject_bounded c)]
  · exact crossingEdge_right_matching l c r.val hl hr
  · exact crossingEdge_right_matching s c r.val hs hr

lemma crossingEdge_middle (l r : X.Cell) (c : X.Objects)
    (hl : X.target 0 l = c.val) (hr : X.source 0 r = c.val) :
    (tensorFunctor.obj X).join 1
      (crossingEdge l c (X.source 1 r)) (crossingEdge (X.target 1 l) c r) =
    (tensorFunctor.obj X).join 1
      (crossingEdge (X.source 1 l) c r) (crossingEdge l c (X.target 1 r)) := by
  have h := (tensorFunctor.obj X).join_middle 0 1 (by omega)
    ((tensorFunctor.obj X).join 0 (((tensorEndpoint false).app X).map l) (verticalObject c))
    (((tensorEndpoint true).app X).map r) (crossingEdge_right_matching l c r hl hr)
  rw [(tensorFunctor.obj X).join_target_gt 1 0 _ _ (by omega)
      (crossingEdge_left_matching l c hl),
    (tensorFunctor.obj X).join_source_gt 1 0 _ _ (by omega)
      (crossingEdge_left_matching l c hl), endpoint_target, endpoint_source,
    endpoint_target, endpoint_source, verticalObject_bounded,
    (tensorFunctor.obj X).target_eq_self_of_source_eq_self (verticalObject_bounded c)] at h
  exact h

lemma whiskeredVertical_left_match (l : X.Cell) (c : X.Cells 1)
    (hl : X.target 0 l = X.source 0 c.val) :
    (tensorFunctor.obj X).target 0 (((tensorEndpoint false).app X).map l) =
      (tensorFunctor.obj X).source 0 (verticalCell 1 c) := by
  rw [endpoint_target, CrossingSquare.vertical_source_zero, hl]

lemma whiskeredVertical_right_match (l : X.Cell) (c : X.Cells 1) (r : X.Cell)
    (hl : X.target 0 l = X.source 0 c.val) (hr : X.target 0 c.val = X.source 0 r) :
    (tensorFunctor.obj X).target 0
      ((tensorFunctor.obj X).join 0 (((tensorEndpoint false).app X).map l) (verticalCell 1 c)) =
      (tensorFunctor.obj X).source 0 (((tensorEndpoint true).app X).map r) := by
  rw [(tensorFunctor.obj X).join_target_le 0 0 _ _ le_rfl (whiskeredVertical_left_match l c hl),
    CrossingSquare.vertical_target_zero, endpoint_source, hr]

lemma whiskeredVertical_source (l : X.Cells 1) (c : X.Cells 1) (r : X.Cells 1)
    (hl : X.target 0 l.val = X.source 0 c.val) (hr : X.target 0 c.val = X.source 0 r.val) :
    (tensorFunctor.obj X).source 1 (whiskeredVertical l.val c r.val) =
      crossingEdge l.val ⟨X.source 0 c.val, X.source_source_self 0 c.val⟩ (X.join 0 c.val r.val) := by
  let D : CrossingSquare X :=
    { left := l, cross := c, right := r
      left₂ := ⟨X.join 0 l.val c.val, X.source_fixed_upwards (by omega : 1 ≤ 2)
        (composite_bounded X (by omega : 0 < 1) _ _ l.property c.property hl)⟩
      right₂ := ⟨X.join 0 c.val r.val, X.source_fixed_upwards (by omega : 1 ≤ 2)
        (composite_bounded X (by omega : 0 < 1) _ _ c.property r.property hr)⟩
      lc := hl, cr := hr
      left_source := composite_bounded X (by omega : 0 < 1) _ _ l.property c.property hl
      right_target := X.target_eq_self_of_source_eq_self
        (composite_bounded X (by omega : 0 < 1) _ _ c.property r.property hr) }
  exact D.middle_source

lemma whiskeredVertical_target (l : X.Cells 1) (c : X.Cells 1) (r : X.Cells 1)
    (hl : X.target 0 l.val = X.source 0 c.val) (hr : X.target 0 c.val = X.source 0 r.val) :
    (tensorFunctor.obj X).target 1 (whiskeredVertical l.val c r.val) =
      crossingEdge (X.join 0 l.val c.val) ⟨X.target 0 c.val, X.source_target_self 0 c.val⟩ r.val := by
  let D : CrossingSquare X :=
    { left := l, cross := c, right := r
      left₂ := ⟨X.join 0 l.val c.val, X.source_fixed_upwards (by omega : 1 ≤ 2)
        (composite_bounded X (by omega : 0 < 1) _ _ l.property c.property hl)⟩
      right₂ := ⟨X.join 0 c.val r.val, X.source_fixed_upwards (by omega : 1 ≤ 2)
        (composite_bounded X (by omega : 0 < 1) _ _ c.property r.property hr)⟩
      lc := hl, cr := hr
      left_source := composite_bounded X (by omega : 0 < 1) _ _ l.property c.property hl
      right_target := X.target_eq_self_of_source_eq_self
        (composite_bounded X (by omega : 0 < 1) _ _ c.property r.property hr) }
  exact D.middle_target

lemma verticalCell_one_source (c : X.Cells 1) :
    (tensorFunctor.obj X).source 1 (verticalCell 1 c) =
      (tensorFunctor.obj X).join 0
        (verticalObject ⟨X.source 0 c.val, X.source_source_self 0 c.val⟩)
        (((tensorEndpoint true).app X).map c.val) := verticalCell_one_face c false

lemma verticalCell_one_target (c : X.Cells 1) :
    (tensorFunctor.obj X).target 1 (verticalCell 1 c) =
      (tensorFunctor.obj X).join 0 (((tensorEndpoint false).app X).map c.val)
        (verticalObject ⟨X.target 0 c.val, X.source_target_self 0 c.val⟩) := verticalCell_one_face c true

lemma whiskeredVertical_comp (l c d r : X.Cells 1)
    (hl : X.target 0 l.val = X.source 0 c.val)
    (hc : X.target 0 c.val = X.source 0 d.val)
    (hr : X.target 0 d.val = X.source 0 r.val) :
    whiskeredVertical l.val (X.gradedComp (by omega : 0 < 1) c d hc) r.val =
      (tensorFunctor.obj X).join 1
        (whiskeredVertical l.val c (X.join 0 d.val r.val))
        (whiskeredVertical (X.join 0 l.val c.val) d r.val) := by
  let T := tensorFunctor.obj X
  let E₀ := (tensorEndpoint false).app X
  let E₁ := (tensorEndpoint true).app X
  have hcad : T.target 0 (verticalCell 1 c) = T.source 0 (E₁.map d.val) := by
    rw [CrossingSquare.vertical_target_zero, endpoint_source, hc]
  have hcb : T.target 0 (E₀.map c.val) = T.source 0 (verticalCell 1 d) := by
    rw [endpoint_target, CrossingSquare.vertical_source_zero, hc]
  let A := T.join 0 (verticalCell 1 c) (E₁.map d.val)
  let B := T.join 0 (E₀.map c.val) (verticalCell 1 d)
  have ha : T.target 1 A = T.source 1 B := by
    dsimp [A,B]
    rw [T.join_target_gt 1 0 _ _ (by omega) hcad,
      T.join_source_gt 1 0 _ _ (by omega) hcb,
      verticalCell_one_target, verticalCell_one_source,
      endpoint_target, endpoint_source,
      X.target_eq_self_of_source_eq_self d.property, c.property]
    have he : (⟨X.target 0 c.val, X.source_target_self 0 c.val⟩ : X.Objects) =
        ⟨X.source 0 d.val, X.source_source_self 0 d.val⟩ := Subtype.ext hc
    rw [he]
    apply T.join_assoc
    · erw [verticalObject_source, endpoint_target, hc]
    · erw [verticalObject_target, endpoint_source]
  have hla : T.target 0 (E₀.map l.val) = T.source 0 A := by
    rw [show A = T.join 0 (verticalCell 1 c) (E₁.map d.val) from rfl,
      T.join_source_le 0 0 _ _ le_rfl hcad]
    exact whiskeredVertical_left_match l.val c hl
  have hlb : T.target 0 (E₀.map l.val) = T.source 0 B := by
    rw [show B = T.join 0 (E₀.map c.val) (verticalCell 1 d) from rfl,
      T.join_source_le 0 0 _ _ le_rfl hcb, endpoint_target, endpoint_source, hl]
  have hlfix : T.source 1 (E₀.map l.val) = E₀.map l.val := by rw [endpoint_source,l.property]
  have hrfix : T.source 1 (E₁.map r.val) = E₁.map r.val := by rw [endpoint_source,r.property]
  have hlar : T.target 0 (T.join 0 (E₀.map l.val) A) = T.source 0 (E₁.map r.val) := by
    rw [T.join_target_le 0 0 _ _ le_rfl hla,
      show A = T.join 0 (verticalCell 1 c) (E₁.map d.val) from rfl,
      T.join_target_le 0 0 _ _ le_rfl hcad, endpoint_target, endpoint_source, hr]
  have hlbr : T.target 0 (T.join 0 (E₀.map l.val) B) = T.source 0 (E₁.map r.val) := by
    rw [T.join_target_le 0 0 _ _ le_rfl hlb,
      show B = T.join 0 (E₀.map c.val) (verticalCell 1 d) from rfl,
      T.join_target_le 0 0 _ _ le_rfl hcb,
      CrossingSquare.vertical_target_zero, endpoint_source, hr]
  have hab : T.target 1 (T.join 0 (E₀.map l.val) A) = T.source 1 (T.join 0 (E₀.map l.val) B) := by
    rw [T.join_target_gt 1 0 _ _ (by omega) hla,
      T.join_source_gt 1 0 _ _ (by omega) hlb,
      T.target_eq_self_of_source_eq_self hlfix, hlfix, ha]
  unfold whiskeredVertical
  rw [verticalCell_one_comp]
  change T.join 0 (T.join 0 (E₀.map l.val) (T.join 1 A B)) (E₁.map r.val) = _
  rw [T.join_whisker_left 0 1 (by omega) _ _ _ hlfix ha hla hlb,
    T.join_whisker_right 0 1 (by omega) _ _ _ hrfix hab hlar hlbr]
  have he₁ : T.join 0 (T.join 0 (E₀.map l.val) A) (E₁.map r.val) =
      T.join 0 (T.join 0 (E₀.map l.val) (verticalCell 1 c)) (E₁.map (X.join 0 d.val r.val)) := by
    dsimp [A]
    erw [E₁.map_join 0 _ _ hr]
    rw [← T.join_assoc 0 _ _ _ (whiskeredVertical_left_match l.val c hl) hcad,
      T.join_assoc 0 _ _ _ (whiskeredVertical_right_match l.val c d.val hl hc)
        (E₁.map_composable hr)]
  have he₂ : T.join 0 (T.join 0 (E₀.map l.val) B) (E₁.map r.val) =
      T.join 0 (T.join 0 (E₀.map (X.join 0 l.val c.val)) (verticalCell 1 d)) (E₁.map r.val) := by
    dsimp [B]
    erw [E₀.map_join 0 _ _ hl]
    rw [T.join_assoc 0 _ _ _ (E₀.map_composable hl) hcb]
  rw [he₁,he₂]

lemma whiskeredVertical_exchange_right (l c : X.Cells 1) (r : X.Cell)
    (hl : X.target 0 l.val = X.source 0 c.val)
    (hr : X.target 0 c.val = X.source 0 r) :
    (tensorFunctor.obj X).join 1
      (whiskeredVertical l.val c (X.source 1 r))
      (crossingEdge (X.join 0 l.val c.val)
        ⟨X.target 0 c.val, X.source_target_self 0 c.val⟩ r) =
    (tensorFunctor.obj X).join 1
      (crossingEdge l.val ⟨X.source 0 c.val, X.source_source_self 0 c.val⟩ (X.join 0 c.val r))
      (whiskeredVertical l.val c (X.target 1 r)) := by
  let T := tensorFunctor.obj X
  let E₀ := (tensorEndpoint false).app X
  let E₁ := (tensorEndpoint true).app X
  have h := T.join_middle 0 1 (by omega)
    (T.join 0 (E₀.map l.val) (verticalCell 1 c)) (E₁.map r)
    (whiskeredVertical_right_match l.val c r hl hr)
  rw [T.join_source_gt 1 0 _ _ (by omega) (whiskeredVertical_left_match l.val c hl),
    T.join_target_gt 1 0 _ _ (by omega) (whiskeredVertical_left_match l.val c hl),
    endpoint_source, endpoint_source, endpoint_target, endpoint_target,
    l.property, X.target_eq_self_of_source_eq_self l.property,
    verticalCell_one_source, verticalCell_one_target] at h
  have hem : T.target 0 (E₀.map c.val) = T.source 0
      (verticalObject ⟨X.target 0 c.val, X.source_target_self 0 c.val⟩) := by
    erw [endpoint_target, verticalObject_source]
  rw [← T.join_assoc 0 _ _ _ (E₀.map_composable hl) hem] at h
  erw [← E₀.map_join 0 _ _ hl] at h
  have hmv : T.target 0
      (verticalObject ⟨X.source 0 c.val, X.source_source_self 0 c.val⟩) =
      T.source 0 (E₁.map c.val) := by erw [verticalObject_target, endpoint_source]
  erw [← T.join_assoc 0 _ _ _ (crossingEdge_left_matching l.val _ hl) hmv,
    T.join_assoc 0 _ _ _ (crossingEdge_right_matching l.val _ c.val hl rfl)
      (E₁.map_composable hr)] at h
  erw [← E₁.map_join 0 _ _ hr] at h
  exact h

lemma whiskeredVertical_exchange_left (l : X.Cell) (c r : X.Cells 1)
    (hl : X.target 0 l = X.source 0 c.val)
    (hr : X.target 0 c.val = X.source 0 r.val) :
    (tensorFunctor.obj X).join 1
      (crossingEdge l ⟨X.source 0 c.val, X.source_source_self 0 c.val⟩ (X.join 0 c.val r.val))
      (whiskeredVertical (X.target 1 l) c r.val) =
    (tensorFunctor.obj X).join 1
      (whiskeredVertical (X.source 1 l) c r.val)
      (crossingEdge (X.join 0 l c.val)
        ⟨X.target 0 c.val, X.source_target_self 0 c.val⟩ r.val) := by
  let T := tensorFunctor.obj X
  let E₀ := (tensorEndpoint false).app X
  let E₁ := (tensorEndpoint true).app X
  have hcr : T.target 0 (verticalCell 1 c) = T.source 0 (E₁.map r.val) := by
    rw [CrossingSquare.vertical_target_zero, endpoint_source, hr]
  have hlt : T.target 0 (E₀.map l) = T.source 0 (T.join 0 (verticalCell 1 c) (E₁.map r.val)) := by
    rw [T.join_source_le 0 0 _ _ le_rfl hcr]
    exact whiskeredVertical_left_match l c hl
  have h := T.join_middle 0 1 (by omega) (E₀.map l)
    (T.join 0 (verticalCell 1 c) (E₁.map r.val)) hlt
  rw [T.join_source_gt 1 0 _ _ (by omega) hcr,
    T.join_target_gt 1 0 _ _ (by omega) hcr,
    endpoint_source, endpoint_source, endpoint_target, endpoint_target,
    r.property, X.target_eq_self_of_source_eq_self r.property,
    verticalCell_one_source, verticalCell_one_target] at h
  have hl' : X.target 0 (X.source 1 l) = X.source 0 c.val := by
    rw [X.target_source, ite_eq_left (by omega : 0 < 1)]; exact hl
  have hl'' : X.target 0 (X.target 1 l) = X.source 0 c.val := by
    rw [X.target_target, min_eq_left (by omega : 0 ≤ 1)]; exact hl
  rw [← T.join_assoc 0 _ _ _ (whiskeredVertical_left_match _ c hl') hcr,
    ← T.join_assoc 0 _ _ _ (whiskeredVertical_left_match _ c hl'') hcr] at h
  have hsrc : T.join 0 (E₀.map l)
      (T.join 0 (T.join 0 (verticalObject ⟨X.source 0 c.val, X.source_source_self 0 c.val⟩)
        (E₁.map c.val)) (E₁.map r.val)) =
      crossingEdge l ⟨X.source 0 c.val, X.source_source_self 0 c.val⟩ (X.join 0 c.val r.val) := by
    unfold crossingEdge
    erw [T.join_assoc 0 _ _ _ (by erw [verticalObject_target, endpoint_source]) (E₁.map_composable hr),
      ← T.join_assoc 0 _ _ _ (crossingEdge_left_matching l _ hl) (by
        erw [← E₁.map_join 0 _ _ hr]
        erw [verticalObject_target, endpoint_source, X.join_source_le 0 0 _ _ le_rfl hr])]
    erw [E₁.map_join 0 _ _ hr]
  have htgt : T.join 0 (E₀.map l)
      (T.join 0 (T.join 0 (E₀.map c.val)
        (verticalObject ⟨X.target 0 c.val, X.source_target_self 0 c.val⟩)) (E₁.map r.val)) =
      crossingEdge (X.join 0 l c.val)
        ⟨X.target 0 c.val, X.source_target_self 0 c.val⟩ r.val := by
    unfold crossingEdge
    have h₁ : T.target 0 (E₀.map c.val) = T.source 0
        (verticalObject ⟨X.target 0 c.val, X.source_target_self 0 c.val⟩) := by
      erw [endpoint_target, verticalObject_source]
    have h₂ : T.target 0 (T.join 0 (E₀.map c.val)
        (verticalObject ⟨X.target 0 c.val, X.source_target_self 0 c.val⟩)) =
        T.source 0 (E₁.map r.val) := crossingEdge_right_matching c.val _ r.val rfl hr.symm
    rw [← T.join_assoc 0 _ _ _ (by
        rw [T.join_source_le 0 0 _ _ le_rfl h₁, endpoint_source, endpoint_target, hl]) h₂,
      ← T.join_assoc 0 _ _ _ (E₀.map_composable hl) h₁]
    erw [E₀.map_join 0 _ _ hl]
  rw [hsrc,htgt] at h
  exact h
end Thomason.GrayRecursive.IntervalHom

end

end OAI
end

section
-- module Solutions.OAIQ043_TH.Thomason_TwoCellComparison
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Two Cell Comparison. -/

noncomputable section
universe u v w z


namespace Thomason.OmegaCategory

lemma join_six_exchange (C : OmegaCategory.{u}) (k : ℕ)
    (a b c d e f u v p q r s : C.Cell)
    (hab : C.target k a = C.source k b)
    (hbc : C.target k b = C.source k c)
    (hcd : C.target k c = C.source k d)
    (hde : C.target k d = C.source k e)
    (hef : C.target k e = C.source k f)
    (huv : C.target k u = C.source k v)
    (hpq : C.target k p = C.source k q)
    (hrs : C.target k r = C.source k s)
    (h₁ : C.join k c d = C.join k u v)
    (h₂ : C.join k b u = C.join k p q)
    (h₃ : C.join k v e = C.join k r s) :
    C.join k (C.join k (C.join k a b) c) (C.join k (C.join k d e) f) =
      C.join k (C.join k (C.join k a p) (C.join k q r)) (C.join k s f) := by
  have hcu : C.source k c = C.source k u := by
    simpa only [C.join_source_le k k _ _ le_rfl hcd,
      C.join_source_le k k _ _ le_rfl huv] using congrArg (C.source k) h₁
  have hdv : C.target k d = C.target k v := by
    simpa only [C.join_target_le k k _ _ le_rfl hcd,
      C.join_target_le k k _ _ le_rfl huv] using congrArg (C.target k) h₁
  have hbu := hbc.trans hcu
  have hve := hdv.symm.trans hde
  have hbp : C.source k b = C.source k p := by
    simpa only [C.join_source_le k k _ _ le_rfl hbu,
      C.join_source_le k k _ _ le_rfl hpq] using congrArg (C.source k) h₂
  have huq : C.target k u = C.target k q := by
    simpa only [C.join_target_le k k _ _ le_rfl hbu,
      C.join_target_le k k _ _ le_rfl hpq] using congrArg (C.target k) h₂
  have hvr : C.source k v = C.source k r := by
    simpa only [C.join_source_le k k _ _ le_rfl hve,
      C.join_source_le k k _ _ le_rfl hrs] using congrArg (C.source k) h₃
  have hes : C.target k e = C.target k s := by
    simpa only [C.join_target_le k k _ _ le_rfl hve,
      C.join_target_le k k _ _ le_rfl hrs] using congrArg (C.target k) h₃
  have hap := hab.trans hbp
  have hqr := huq.symm.trans (huv.trans hvr)
  have hsf := hes.symm.trans hef
  have habc : C.target k (C.join k a b) = C.source k c := by
    rw [C.join_target_le k k _ _ le_rfl hab]; exact hbc
  have habu : C.target k (C.join k a b) = C.source k u := by
    rw [C.join_target_le k k _ _ le_rfl hab]; exact hbu
  have hdef : C.target k d = C.source k (C.join k e f) := by
    rw [C.join_source_le k k _ _ le_rfl hef]; exact hde
  have hvef : C.target k v = C.source k (C.join k e f) := by
    rw [C.join_source_le k k _ _ le_rfl hef]; exact hve
  have hpqr : C.target k p = C.source k (C.join k q r) := by
    rw [C.join_source_le k k _ _ le_rfl hqr]; exact hpq
  have hrsf : C.target k r = C.source k (C.join k s f) := by
    rw [C.join_source_le k k _ _ le_rfl hsf]; exact hrs
  have hqrs : C.target k (C.join k q r) = C.source k s := by
    rw [C.join_target_le k k _ _ le_rfl hqr]; exact hrs
  rw [C.join_assoc k d e f hde hef,
    C.join_four_middle k (C.join k a b) c d (C.join k e f) u v
      habc hcd hdef habu huv hvef h₁,
    C.join_assoc k a b u hab hbu,
    ← C.join_assoc k v e f hve hef, h₂, h₃,
    ← C.join_assoc k a p q hap hpq]
  
  rw [C.join_assoc k r s f hrs hsf]
  have hqrsf : C.target k q = C.source k (C.join k r (C.join k s f)) := by
    rw [C.join_source_le k k _ _ le_rfl hrsf]; exact hqr
  rw [C.join_assoc k (C.join k a p) q (C.join k r (C.join k s f))
      (by rw [C.join_target_le k k _ _ le_rfl hap]; exact hpq) hqrsf,
    ← C.join_assoc k q r (C.join k s f) hqr hrsf,
    ← C.join_assoc k (C.join k a p) (C.join k q r) (C.join k s f)
      (by rw [C.join_target_le k k _ _ le_rfl hap]; exact hpqr)
      (by rw [C.join_target_le k k _ _ le_rfl hqr,
        C.join_source_le k k _ _ le_rfl hsf]; exact hrs)]

end Thomason.OmegaCategory

end

noncomputable section
universe u v w z


namespace Thomason.GrayRecursive.IntervalHom
open CategoryTheory DirectedComplex DirectedComplex.Table GlobeComplex OmegaCategory
variable {X : OmegaCategory.{u}}
namespace CrossingSquare

variable (D E : CrossingSquare X)
variable (hl : X.target 1 D.left₂.val = E.left.val)
variable (hc : D.exit.val = E.entry.val)
variable (hr : D.right.val = X.source 1 E.right₂.val)

lemma comp_entry : (D.comp E hl hc hr).entry = D.entry := by
  apply Subtype.ext
  exact X.join_source_le 0 0 _ _ le_rfl hc

lemma comp_exit : (D.comp E hl hc hr).exit = E.exit := by
  apply Subtype.ext
  exact X.join_target_le 0 0 _ _ le_rfl hc

lemma comp_value : (D.comp E hl hc hr).value =
    (tensorFunctor.obj X).join 1 D.value E.value := by
  let T := tensorFunctor.obj X
  let G := D.comp E hl hc hr
  let lc : X.Cells 1 := ⟨X.join 0 D.left.val D.cross.val,
    composite_bounded X (by omega : 0 < 1) _ _ D.left.property D.cross.property D.lc⟩
  let cr : X.Cells 1 := ⟨X.join 0 E.cross.val E.right.val,
    composite_bounded X (by omega : 0 < 1) _ _ E.cross.property E.right.property E.cr⟩
  let U := crossingEdge lc.val D.exit E.right₂.val
  let V := crossingEdge D.left₂.val D.exit cr.val
  let P := crossingEdge D.left.val D.entry (X.join 0 D.cross.val E.right₂.val)
  let Q := whiskeredVertical D.left.val D.cross cr.val
  let R := whiskeredVertical lc.val E.cross E.right.val
  let S := crossingEdge (X.join 0 D.left₂.val E.cross.val) E.exit E.right.val
  have hh : D.exit = E.entry := Subtype.ext hc
  have hlc : X.target 0 lc.val = D.exit.val :=
    X.join_target_le 0 0 _ _ le_rfl D.lc
  have hcr : X.source 0 cr.val = E.entry.val :=
    X.join_source_le 0 0 _ _ le_rfl E.cr
  have hDcr : X.target 0 D.cross.val = X.source 0 cr.val := hc.trans hcr.symm
  have hLcE : X.target 0 lc.val = X.source 0 E.cross.val := hlc.trans hc
  have hER : X.source 0 E.right₂.val = D.exit.val := E.right₂_source_zero.trans hc.symm
  have huv : T.target 1 U = T.source 1 V := by
    change T.target 1 (crossingEdge lc.val D.exit E.right₂.val) =
      T.source 1 (crossingEdge D.left₂.val D.exit cr.val)
    rw [crossingEdge_target_one _ _ _ hlc hER,
      crossingEdge_source_one _ _ _ D.left₂_target_zero (hcr.trans hc.symm),
      X.target_eq_self_of_source_eq_self lc.property,cr.property,D.left_source,E.right_target]
  have hpq : T.target 1 P = T.source 1 Q := by
    change T.target 1 (crossingEdge D.left.val D.entry (X.join 0 D.cross.val E.right₂.val)) =
      T.source 1 (whiskeredVertical D.left.val D.cross cr.val)
    rw [crossingEdge_target_one _ _ _ D.lc
        (X.join_source_le 0 0 _ _ le_rfl (D.comp_right_match E hc)),
      X.target_eq_self_of_source_eq_self D.left.property,
      X.join_target_gt 1 0 _ _ (by omega) (D.comp_right_match E hc),
      X.target_eq_self_of_source_eq_self D.cross.property, E.right_target,
      whiskeredVertical_source D.left D.cross cr D.lc hDcr]
  have hrs : T.target 1 R = T.source 1 S := by
    change T.target 1 (whiskeredVertical lc.val E.cross E.right.val) =
      T.source 1 (crossingEdge (X.join 0 D.left₂.val E.cross.val) E.exit E.right.val)
    rw [whiskeredVertical_target lc E.cross E.right hLcE E.cr,
      crossingEdge_source_one _ _ _
        (X.join_target_le 0 0 _ _ le_rfl (D.comp_left_match E hc)) E.cr.symm,
      X.join_source_gt 1 0 _ _ (by omega) (D.comp_left_match E hc),
      E.cross.property,E.right.property,D.left_source]
  have hde : T.target 1 D.last = T.source 1 E.first := by
    rw [D.last_target,E.first_source,hl,hr,hh]
  have h₁ : T.join 1 D.last E.first = T.join 1 U V := by
    have H := crossingEdge_middle D.left₂.val E.right₂.val D.exit D.left₂_target_zero hER
    rw [D.left_source,hl,E.right_target] at H
    change T.join 1 (crossingEdge D.left₂.val D.exit D.right.val)
      (crossingEdge E.left.val E.entry E.right₂.val) = _
    rw [hr,← hh]
    exact H
  have h₂ : T.join 1 D.middle U = T.join 1 P Q := by
    change T.join 1 (whiskeredVertical D.left.val D.cross D.right.val)
      (crossingEdge (X.join 0 D.left.val D.cross.val) D.exit E.right₂.val) = _
    rw [hr]
    have H := whiskeredVertical_exchange_right D.left D.cross E.right₂.val D.lc
      (D.comp_right_match E hc)
    rw [E.right_target] at H
    exact H
  have h₃ : T.join 1 V E.middle = T.join 1 R S := by
    have H := whiskeredVertical_exchange_left D.left₂.val E.cross E.right
      (D.comp_left_match E hc) E.cr
    rw [hl,D.left_source] at H
    change T.join 1 (crossingEdge D.left₂.val D.exit cr.val)
      (whiskeredVertical E.left.val E.cross E.right.val) = _
    rw [hh]
    exact H
  have hfirst : G.first = T.join 1 D.first P := by
    change crossingEdge D.left.val G.entry
      (X.join 1 D.right₂.val (X.join 0 D.cross.val E.right₂.val)) = _
    rw [D.comp_entry E hl hc hr]
    exact crossingEdge_comp_right D.left D.entry D.right₂.val (X.join 0 D.cross.val E.right₂.val)
      D.lc D.right₂_source_zero
      (X.join_source_le 0 0 _ _ le_rfl (D.comp_right_match E hc))
      (D.comp_right₂_match E hc hr)
  have hmiddle : G.middle = T.join 1 Q R := by
    have he : G.cross = X.gradedComp (by omega : 0 < 1) D.cross E.cross hc := by
      apply Subtype.ext
      exact X.join_eq 0 D.cross.val E.cross.val hc
    change whiskeredVertical D.left.val G.cross E.right.val = _
    rw [he]
    exact whiskeredVertical_comp D.left D.cross E.cross E.right D.lc hc E.cr
  have hlast : G.last = T.join 1 S E.last := by
    change crossingEdge (X.join 1 (X.join 0 D.left₂.val E.cross.val) E.left₂.val)
      G.exit E.right.val = _
    rw [D.comp_exit E hl hc hr]
    exact crossingEdge_comp_left (X.join 0 D.left₂.val E.cross.val) E.left₂.val E.exit E.right
      (X.join_target_le 0 0 _ _ le_rfl (D.comp_left_match E hc)) E.left₂_target_zero E.cr.symm
      (D.comp_left₂_match E hl hc)
  have H := T.join_six_exchange 1 D.first D.middle D.last E.first E.middle E.last U V P Q R S
    D.first_middle D.middle_last hde E.first_middle E.middle_last huv hpq hrs h₁ h₂ h₃
  change T.join 1 (T.join 1 G.first G.middle) G.last =
    T.join 1 (T.join 1 (T.join 1 D.first D.middle) D.last)
      (T.join 1 (T.join 1 E.first E.middle) E.last)
  rw [hfirst,hmiddle,hlast]
  exact H.symm

lemma seam_of_matching {M : DirectedComplex.{u}} (D E : CrossingSquare M.nu)
    (h : (tensorFunctor.obj M.nu).target 1 D.value =
      (tensorFunctor.obj M.nu).source 1 E.value) :
    M.nu.target 1 D.left₂.val = E.left.val ∧
      D.exit.val = E.entry.val ∧ D.right.val = M.nu.source 1 E.right₂.val := by
  rw [D.target_one,E.source_one] at h
  obtain ⟨h₁,h₂,h₃⟩ := chainComparison_crossingEdge_injective
      (M.nu.target 1 D.left₂.val) E.left.val D.exit E.entry
      D.right.val (M.nu.source 1 E.right₂.val)
      (by change M.nu.target 0 (M.nu.target 1 D.left₂.val) = _
          rw [M.nu.target_target,min_eq_left (by omega : 0 ≤ 1)]; exact D.left₂_target_zero)
      D.cr.symm E.lc
      (by change M.nu.source 0 (M.nu.source 1 E.right₂.val) = _
          rw [M.nu.source_source,min_eq_left (by omega : 0 ≤ 1)]; exact E.right₂_source_zero)
      (congrArg (chainComparison M).map h)
  exact ⟨h₁,congrArg Subtype.val h₂,h₃⟩

end CrossingSquare
end Thomason.GrayRecursive.IntervalHom

end

noncomputable section
universe u v w z


namespace Thomason.OmegaCategory

lemma join_comp_source (C : OmegaCategory.{u}) (k l : ℕ) (hkl : k < l)
    (a b c : C.Cell) (hbc : C.target l b = C.source l c)
    (hab : C.target k a = C.source k b) :
    C.join k a (C.join l b c) =
      C.join l (C.join k (C.source l a) b) (C.join k a c) := by
  have hac : C.target k a = C.source k c := by
    have hh := congrArg (C.source k) hbc
    rw [C.source_target, ite_eq_left hkl, C.source_source, min_eq_left hkl.le] at hh
    exact hab.trans hh
  have hsab : C.target k (C.source l a) = C.source k b := by
    rw [C.target_source, ite_eq_left hkl]; exact hab
  have h := C.join_interchange k l hkl (C.source l a) a b c
    (C.target_source_self l a) hbc hsab hac
  rw [C.join_left_unit l (C.source l a) a (C.source_source_self l a)
    (C.target_source_self l a)] at h
  exact h

lemma join_comp_target (C : OmegaCategory.{u}) (k l : ℕ) (hkl : k < l)
    (a b c : C.Cell) (hbc : C.target l b = C.source l c)
    (hba : C.target k b = C.source k a) :
    C.join k (C.join l b c) a =
      C.join l (C.join k b a) (C.join k c (C.target l a)) := by
  have hca : C.target k c = C.source k a := by
    have hh := congrArg (C.target k) hbc
    rw [C.target_target, min_eq_left hkl.le, C.target_source, ite_eq_left hkl] at hh
    exact hh.symm.trans hba
  have hcat : C.target k c = C.source k (C.target l a) := by
    rw [C.source_target, ite_eq_left hkl]; exact hca
  have h := C.join_interchange k l hkl b c a (C.target l a)
    hbc (C.source_target_self l a).symm hba hcat
  rw [C.join_right_unit l a (C.target l a) (C.source_target_self l a)
    (C.source_target_self l a).symm] at h
  exact h

end Thomason.OmegaCategory

end

noncomputable section
universe u v w z


namespace Thomason.GrayRecursive.IntervalHom
open CategoryTheory DirectedComplex DirectedComplex.Table GlobeComplex OmegaCategory
variable {X : OmegaCategory.{u}}

lemma crossingEdge_whisker_left (a l : X.Cell) (c : X.Objects) (r : X.Cell)
    (h : X.target 0 a = X.source 0 l) (hl : X.target 0 l = c.val)
    (hr : X.source 0 r = c.val) :
    crossingEdge (X.join 0 a l) c r = (tensorFunctor.obj X).join 0
      (((tensorEndpoint false).app X).map a) (crossingEdge l c r) := by
  let T := tensorFunctor.obj X
  let E := (tensorEndpoint false).app X
  unfold crossingEdge
  erw [E.map_join 0 _ _ h]
  rw [T.join_assoc 0 _ _ _ (E.map_composable h) (crossingEdge_left_matching l c hl),
    T.join_assoc 0 _ _ _ (by
      rw [T.join_source_le 0 0 _ _ le_rfl (crossingEdge_left_matching l c hl)]
      exact E.map_composable h) (crossingEdge_right_matching l c r hl hr)]

lemma crossingEdge_whisker_right (l : X.Cell) (c : X.Objects) (r a : X.Cell)
    (hl : X.target 0 l = c.val) (hr : X.source 0 r = c.val)
    (h : X.target 0 r = X.source 0 a) :
    crossingEdge l c (X.join 0 r a) = (tensorFunctor.obj X).join 0
      (crossingEdge l c r) (((tensorEndpoint true).app X).map a) := by
  unfold crossingEdge
  erw [((tensorEndpoint true).app X).map_join 0 _ _ h,
    (tensorFunctor.obj X).join_assoc 0 _ _ _ (crossingEdge_right_matching l c r hl hr)
      (((tensorEndpoint true).app X).map_composable h)]

lemma whiskeredVertical_whisker_left (a l : X.Cell) (c : X.Cells 1) (r : X.Cell)
    (h : X.target 0 a = X.source 0 l) (hl : X.target 0 l = X.source 0 c.val)
    (hr : X.target 0 c.val = X.source 0 r) :
    whiskeredVertical (X.join 0 a l) c r = (tensorFunctor.obj X).join 0
      (((tensorEndpoint false).app X).map a) (whiskeredVertical l c r) := by
  let T := tensorFunctor.obj X
  let E := (tensorEndpoint false).app X
  unfold whiskeredVertical
  erw [E.map_join 0 _ _ h]
  rw [T.join_assoc 0 _ _ _ (E.map_composable h) (whiskeredVertical_left_match l c hl),
    T.join_assoc 0 _ _ _ (by
      rw [T.join_source_le 0 0 _ _ le_rfl (whiskeredVertical_left_match l c hl)]
      exact E.map_composable h) (whiskeredVertical_right_match l c r hl hr)]

lemma whiskeredVertical_whisker_right (l : X.Cell) (c : X.Cells 1) (r a : X.Cell)
    (hl : X.target 0 l = X.source 0 c.val) (hr : X.target 0 c.val = X.source 0 r)
    (h : X.target 0 r = X.source 0 a) :
    whiskeredVertical l c (X.join 0 r a) = (tensorFunctor.obj X).join 0
      (whiskeredVertical l c r) (((tensorEndpoint true).app X).map a) := by
  unfold whiskeredVertical
  erw [((tensorEndpoint true).app X).map_join 0 _ _ h,
    (tensorFunctor.obj X).join_assoc 0 _ _ _ (whiskeredVertical_right_match l c r hl hr)
      (((tensorEndpoint true).app X).map_composable h)]

namespace CrossingSquare
variable (D : CrossingSquare X)

lemma source_zero : (tensorFunctor.obj X).source 0 D.value =
    ((tensorEndpoint false).app X).map (X.source 0 D.left.val) := by
  rw [value, (tensorFunctor.obj X).join_source_le 0 1 _ _ (by omega) D.firstMiddle_last,
    (tensorFunctor.obj X).join_source_le 0 1 _ _ (by omega) D.first_middle]
  exact crossingEdge_source _ _ _ D.lc D.right₂_source_zero

lemma target_zero : (tensorFunctor.obj X).target 0 D.value =
    ((tensorEndpoint true).app X).map (X.target 0 D.right.val) := by
  rw [value, (tensorFunctor.obj X).join_target_le 0 1 _ _ (by omega) D.firstMiddle_last]
  exact crossingEdge_target _ _ _ D.left₂_target_zero D.cr.symm

variable (a : X.Cells 2) (h : X.target 0 a.val = X.source 0 D.left.val)

lemma whiskerLeft_value : (D.whiskerLeft a h).value = (tensorFunctor.obj X).join 0
    (((tensorEndpoint false).app X).map a.val) D.value := by
  let T := tensorFunctor.obj X
  let E := (tensorEndpoint false).app X
  let G := D.whiskerLeft a h
  have hfirst : G.first = T.join 0 (E.map (X.source 1 a.val)) D.first :=
    crossingEdge_whisker_left _ _ _ _ (D.whisker_left_source_match a h) D.lc D.right₂_source_zero
  have hmiddle : G.middle = T.join 0 (E.map (X.source 1 a.val)) D.middle :=
    whiskeredVertical_whisker_left _ _ _ _ (D.whisker_left_source_match a h) D.lc D.cr
  have hlast : G.last = T.join 0 (E.map a.val) D.last :=
    crossingEdge_whisker_left _ _ _ _ (D.whisker_left_match a h) D.left₂_target_zero D.cr.symm
  change T.join 1 (T.join 1 G.first G.middle) G.last = _
  rw [hfirst,hmiddle,hlast]
  have hm₁ : T.target 0 (E.map a.val) = T.source 0 D.first := by
    rw [endpoint_target, first, crossingEdge_source _ _ _ D.lc D.right₂_source_zero, h]
  have hm₂ : T.target 0 (E.map a.val) = T.source 0 (T.join 1 D.first D.middle) := by
    rw [T.join_source_le 0 1 _ _ (by omega) D.first_middle]; exact hm₁
  have hms : T.target 0 (T.source 1 (E.map a.val)) = T.source 0 D.first := by
    rw [T.target_source, ite_eq_left (by omega : 0 < 1)]; exact hm₁
  change _ = T.join 0 (E.map a.val) (T.join 1 (T.join 1 D.first D.middle) D.last)
  rw [T.join_comp_source 0 1 (by omega) _ _ _ D.firstMiddle_last hm₂,
    T.join_comp_source 0 1 (by omega) _ _ _ D.first_middle hms,
    T.source_source_self, endpoint_source]

variable (hr : X.target 0 D.right.val = X.source 0 a.val)

lemma whiskerRight_value : (D.whiskerRight a hr).value = (tensorFunctor.obj X).join 0
    D.value (((tensorEndpoint true).app X).map a.val) := by
  let T := tensorFunctor.obj X
  let E := (tensorEndpoint true).app X
  let G := D.whiskerRight a hr
  have hfirst : G.first = T.join 0 D.first (E.map a.val) :=
    crossingEdge_whisker_right _ _ _ _ D.lc D.right₂_source_zero (D.whisker_right_match a hr)
  have hmiddle : G.middle = T.join 0 D.middle (E.map (X.target 1 a.val)) :=
    whiskeredVertical_whisker_right _ _ _ _ D.lc D.cr (D.whisker_right_target_match a hr)
  have hlast : G.last = T.join 0 D.last (E.map (X.target 1 a.val)) :=
    crossingEdge_whisker_right _ _ _ _ D.left₂_target_zero D.cr.symm
      (D.whisker_right_target_match a hr)
  change T.join 1 (T.join 1 G.first G.middle) G.last = _
  rw [hfirst,hmiddle,hlast]
  have hm₁ : T.target 0 D.first = T.source 0 (E.map a.val) := by
    rw [endpoint_source, first, crossingEdge_target _ _ _ D.lc D.right₂_source_zero,
      D.right₂_target_zero, hr]
  have hm₂ : T.target 0 (T.join 1 D.first D.middle) = T.source 0 (E.map a.val) := by
    have hmf := congrArg (T.target 0) D.first_middle
    rw [T.target_target, min_eq_left (by omega : 0 ≤ 1), T.target_source,
      ite_eq_left (by omega : 0 < 1)] at hmf
    rw [T.join_target_le 0 1 _ _ (by omega) D.first_middle]
    exact hmf.symm.trans hm₁
  change _ = T.join 0 (T.join 1 (T.join 1 D.first D.middle) D.last) (E.map a.val)
  rw [T.join_comp_target 0 1 (by omega) _ _ _ D.firstMiddle_last hm₂,
    T.join_comp_target 0 1 (by omega) _ _ _ D.first_middle hm₁, endpoint_target]

end CrossingSquare
end Thomason.GrayRecursive.IntervalHom

end

noncomputable section
universe u v w z


namespace Thomason.GrayRecursive.IntervalHom
open CategoryTheory DirectedComplex DirectedComplex.Table GlobeComplex OmegaCategory
variable {X Y : OmegaCategory.{u}}

namespace CrossingSquare

lemma map_entry (D : CrossingSquare X) (F : X ⟶ Y) :
    (D.map F).entry = F.objects D.entry := by
  apply Subtype.ext
  exact (F.map_source 0 D.cross.val).symm

lemma map_exit (D : CrossingSquare X) (F : X ⟶ Y) :
    (D.map F).exit = F.objects D.exit := by
  apply Subtype.ext
  exact (F.map_target 0 D.cross.val).symm

lemma map_value (D : CrossingSquare X) (F : X ⟶ Y) :
    (D.map F).value = (tensorFunctor.map F).map D.value := by
  have hfirst : (D.map F).first = (tensorFunctor.map F).map D.first := by
    rw [first, D.map_entry, first, tensorFunctor_map_crossingEdge F _ _ _ D.lc D.right₂_source_zero]
    rfl
  have hlast : (D.map F).last = (tensorFunctor.map F).map D.last := by
    rw [last, D.map_exit, last, tensorFunctor_map_crossingEdge F _ _ _ D.left₂_target_zero D.cr.symm]
    rfl
  have hmiddle : (D.map F).middle = (tensorFunctor.map F).map D.middle := by
    rw [middle, middle,
      (tensorFunctor.map F).map_join 0 _ _ D.middle_matching_right,
      (tensorFunctor.map F).map_join 0 _ _ D.middle_matching_left,
      tensorFunctor_map_endpoint, tensorFunctor_map_endpoint,
      verticalCell_natural]
    rfl
  rw [value, value, hfirst, hmiddle, hlast,
    (tensorFunctor.map F).map_join 1 _ _ D.firstMiddle_last,
    (tensorFunctor.map F).map_join 1 _ _ D.first_middle]

end CrossingSquare

lemma SquareNormal.map (F : X ⟶ Y) {z : (tensorFunctor.obj X).Cell} (hz : SquareNormal X z) :
    SquareNormal Y ((tensorFunctor.map F).map z) := by
  cases hz with
  | endpoint a x hx =>
    rw [tensorFunctor_map_endpoint]
    exact .endpoint a _ ((F.map_source 2 x).symm.trans (congrArg F.map hx))
  | crossing D => rw [← D.map_value F]; exact .crossing _

lemma globe_inv_square_normal (n : ℕ) (t : Table (K.{u} n)) (ht : truncate 2 false t = t) :
    SquareNormal (complex n).nu ((globeTensorIso n).inv.map t) := by
  rcases CylinderTables.endpoint_or_crossing (complexPositiveAcyclic n) t with ⟨a,ha⟩ | ⟨hs,he⟩
  · have hp : truncate 2 false (CylinderTables.project t) = CylinderTables.project t := by
      change truncate 2 false ((complex n).cylinderProjection.table t) = _
      rw [← Hom.table_truncate,ht]
      rfl
    have him : (chainComparison (complex n)).map (((tensorEndpoint a).app (complex n).nu).map
        (CylinderTables.project t)) = t := (chainComparison_endpoint_apply a _).trans ha.symm
    rw [chainComparison_globe] at him
    have hi := congrArg (globeTensorIso n).inv.map him
    have hb := congrArg (fun F : tensorFunctor.obj (complex n).nu ⟶ tensorFunctor.obj (complex n).nu =>
      F.map (((tensorEndpoint a).app (complex n).nu).map (CylinderTables.project t))) (globeTensorIso n).hom_inv_id
    change (globeTensorIso n).inv.map ((globeTensorIso n).hom.map _) = _ at hb
    rw [hb] at hi
    rw [← hi]
    exact .endpoint a _ hp
  · let D := CrossingSquare.ofTable (complexPositiveAcyclic n) ⟨t,ht⟩ hs he
    have him : (chainComparison (complex n)).map D.value = t :=
      CrossingSquare.image_ofTable (complexPositiveAcyclic n) ⟨t,ht⟩ hs he
    rw [chainComparison_globe] at him
    have hi := congrArg (globeTensorIso n).inv.map him
    have hb := congrArg (fun F : tensorFunctor.obj (complex n).nu ⟶ tensorFunctor.obj (complex n).nu =>
      F.map D.value) (globeTensorIso n).hom_inv_id
    change (globeTensorIso n).inv.map ((globeTensorIso n).hom.map _) = _ at hb
    rw [hb] at hi
    rw [← hi]
    exact .crossing D

lemma generatorCylinder_square_normal (n : ℕ) (x : X.Cells n) (t : Table (K.{u} n))
    (ht : truncate 2 false t = t) : SquareNormal X ((generatorCylinder n x).map t) := by
  rw [generatorCylinder_as_map]
  exact (globe_inv_square_normal n t ht).map _

lemma vertical_square_normal (n : ℕ) (hn : n < 2) (x : X.Cells n) :
    SquareNormal X (verticalCell n x) :=
  generatorCylinder_square_normal n x _
    ((K n).nu.source_fixed_upwards (by omega : n+1 ≤ 2)
      (vertical_fixed _ (topTable_bounded n)))

lemma SquareNormal.join_zero {x y : (tensorFunctor.obj X).Cell}
    (hx : SquareNormal X x) (hy : SquareNormal X y)
    (h : (tensorFunctor.obj X).target 0 x = (tensorFunctor.obj X).source 0 y) :
    SquareNormal X ((tensorFunctor.obj X).join 0 x y) := by
  cases hx with
  | endpoint a x hx =>
    cases hy with
    | endpoint b y hy =>
      rw [endpoint_target,endpoint_source] at h
      obtain ⟨hab,hxy⟩ := (tensorEndpoint_eq_iff a b _ _).mp h
      subst b
      rw [← ((tensorEndpoint a).app X).map_join 0 x y hxy]
      exact .endpoint a _ (composite_bounded X (by omega : 0 < 2) x y hx hy hxy)
    | crossing D =>
      rw [endpoint_target,D.source_zero] at h
      obtain ⟨ha,hxl⟩ := (tensorEndpoint_eq_iff a false _ _).mp h
      subst a
      rw [← D.whiskerLeft_value ⟨x,hx⟩ hxl]
      exact .crossing _
  | crossing D =>
    cases hy with
    | endpoint a y hy =>
      rw [D.target_zero,endpoint_source] at h
      obtain ⟨ha,hry⟩ := (tensorEndpoint_eq_iff true a _ _).mp h
      subst a
      rw [← D.whiskerRight_value ⟨y,hy⟩ hry]
      exact .crossing _
    | crossing E =>
      rw [D.target_zero,E.source_zero] at h
      exact False.elim (Bool.noConfusion ((tensorEndpoint_eq_iff true false _ _).mp h).1)

lemma EdgeNormal.square {z : (tensorFunctor.obj X).Cell} (hz : EdgeNormal X z) :
    SquareNormal X z := by
  cases hz with
  | endpoint a x hx => exact .endpoint a x (X.source_fixed_upwards (by omega : 1 ≤ 2) hx)
  | crossing l c r hl hr hdl hdr =>
    have hv : SquareNormal X (verticalObject c) := vertical_square_normal 0 (by omega) c
    exact ((SquareNormal.endpoint false l (X.source_fixed_upwards (by omega : 1 ≤ 2) hdl)).join_zero hv
      (crossingEdge_left_matching l c hl)).join_zero
      (.endpoint true r (X.source_fixed_upwards (by omega : 1 ≤ 2) hdr))
      (crossingEdge_right_matching l c r hl hr)
end Thomason.GrayRecursive.IntervalHom

end

noncomputable section
universe u v w z


namespace Thomason.GrayRecursive.IntervalHom
open CategoryTheory DirectedComplex DirectedComplex.Table GlobeComplex OmegaCategory
variable {X : OmegaCategory.{u}} {M : DirectedComplex.{u}}

lemma endpoint_crossing_square_not_matching (a : Bool) (x : X.Cell) (D : CrossingSquare X)
    (h : (tensorFunctor.obj X).target 1 (((tensorEndpoint a).app X).map x) =
      (tensorFunctor.obj X).source 1 D.value) : False := by
  let T := tensorFunctor.obj X
  have hs := congrArg (T.source 0) h
  have ht := congrArg (T.target 0) h
  rw [T.source_target,ite_eq_left (by omega : 0 < 1),T.source_source,min_eq_left (by omega : 0 ≤ 1)] at hs
  rw [T.target_target,min_eq_left (by omega : 0 ≤ 1),T.target_source,ite_eq_left (by omega : 0 < 1)] at ht
  change (tensorFunctor.obj X).source 0 _ = (tensorFunctor.obj X).source 0 _ at hs
  change (tensorFunctor.obj X).target 0 _ = (tensorFunctor.obj X).target 0 _ at ht
  rw [endpoint_source,D.source_zero] at hs
  rw [endpoint_target,D.target_zero] at ht
  exact Bool.noConfusion (((tensorEndpoint_eq_iff a true _ _).mp ht).1.symm.trans
    ((tensorEndpoint_eq_iff a false _ _).mp hs).1)

lemma crossing_square_endpoint_not_matching (D : CrossingSquare X) (a : Bool) (x : X.Cell)
    (h : (tensorFunctor.obj X).target 1 D.value =
      (tensorFunctor.obj X).source 1 (((tensorEndpoint a).app X).map x)) : False := by
  let T := tensorFunctor.obj X
  have hs := congrArg (T.source 0) h
  have ht := congrArg (T.target 0) h
  rw [T.source_target,ite_eq_left (by omega : 0 < 1),T.source_source,min_eq_left (by omega : 0 ≤ 1)] at hs
  rw [T.target_target,min_eq_left (by omega : 0 ≤ 1),T.target_source,ite_eq_left (by omega : 0 < 1)] at ht
  change (tensorFunctor.obj X).source 0 _ = (tensorFunctor.obj X).source 0 _ at hs
  change (tensorFunctor.obj X).target 0 _ = (tensorFunctor.obj X).target 0 _ at ht
  rw [D.source_zero,endpoint_source] at hs
  rw [D.target_zero,endpoint_target] at ht
  exact Bool.noConfusion (((tensorEndpoint_eq_iff true a _ _).mp ht).1.trans
    ((tensorEndpoint_eq_iff false a _ _).mp hs).1.symm)

lemma SquareNormal.join_one {x y : (tensorFunctor.obj M.nu).Cell}
    (hx : SquareNormal M.nu x) (hy : SquareNormal M.nu y)
    (h : (tensorFunctor.obj M.nu).target 1 x = (tensorFunctor.obj M.nu).source 1 y) :
    SquareNormal M.nu ((tensorFunctor.obj M.nu).join 1 x y) := by
  cases hx with
  | endpoint a x hx =>
    cases hy with
    | endpoint b y hy =>
      rw [endpoint_target,endpoint_source] at h
      obtain ⟨hab,hxy⟩ := (tensorEndpoint_eq_iff a b _ _).mp h
      subst b
      rw [← ((tensorEndpoint a).app M.nu).map_join 1 x y hxy]
      exact .endpoint a _ (composite_bounded M.nu (by omega : 1 < 2) x y hx hy hxy)
    | crossing D => exact False.elim (endpoint_crossing_square_not_matching a x D h)
  | crossing D =>
    cases hy with
    | endpoint a y hy => exact False.elim (crossing_square_endpoint_not_matching D a y h)
    | crossing E =>
      obtain ⟨hl,hc,hr⟩ := D.seam_of_matching E h
      rw [← D.comp_value E hl hc hr]
      exact .crossing _

lemma tensor_square_normal (z : (tensorFunctor.obj M.nu).Cell)
    (hz : (tensorFunctor.obj M.nu).source 2 z = z) : SquareNormal M.nu z := by
  apply tensor_bounded_cells_induction 2 (SquareNormal M.nu) ?_ ?_ ?_ ?_ z hz
  · intro a x hx; exact .endpoint a x hx
  · exact vertical_square_normal
  · intro r hr t ht
    exact (tensor_edge_normal t ((tensorFunctor.obj M.nu).source_fixed_upwards (by omega : r ≤ 1) ht)).square
  · intro r hr x y hx hy hm hnx hny
    rw [← (tensorFunctor.obj M.nu).join_eq r x y hm]
    have he : r = 0 ∨ r = 1 := by omega
    rcases he with rfl | rfl
    · exact hnx.join_zero hny hm
    · exact hnx.join_one hny hm

lemma chainComparison_twocells_injective (x y : (tensorFunctor.obj M.nu).Cell)
    (hx : (tensorFunctor.obj M.nu).source 2 x = x) (hy : (tensorFunctor.obj M.nu).source 2 y = y)
    (he : (chainComparison M).map x = (chainComparison M).map y) : x = y := by
  have hnx := tensor_square_normal x hx
  have hny := tensor_square_normal y hy
  cases hnx with
  | endpoint a x hx =>
    exact ((chainComparison_endpoint_fiber y a x).mp
      (he.symm.trans (chainComparison_endpoint_apply a x))).symm
  | crossing D =>
    cases hny with
    | endpoint a y hy =>
      exact (chainComparison_endpoint_fiber _ a y).mp (he.trans (chainComparison_endpoint_apply a y))
    | crossing E => exact congrArg CrossingSquare.value (D.image_ext E he)

theorem chainComparison_twocells_bijective (hM : PositiveAcyclic M) :
    Function.Bijective ((chainComparison M).onCells 2) := by
  refine ⟨?_, chainComparison_twocells_surjective hM⟩
  intro x y he
  apply Subtype.ext
  exact chainComparison_twocells_injective x.val y.val x.property y.property (congrArg Subtype.val he)

theorem chainComparison_poset_twocells_bijective_oai (P : Type u) [PartialOrder P] :
    Function.Bijective ((chainComparison (NormalizedChains.complex P)).onCells 2) :=
  chainComparison_twocells_bijective (NormalizedChains.complexPositiveAcyclic P)
end Thomason.GrayRecursive.IntervalHom

end

end OAI
end

theorem solution.{u} : type_of% @OAI.Thomason.GrayRecursive.IntervalHom.chainComparison_poset_twocells_bijective_oai.{u} := @OAI.Thomason.GrayRecursive.IntervalHom.chainComparison_poset_twocells_bijective_oai.{u}
