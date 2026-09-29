-- Prove2me | solution 1 for ModularCurve.XHDRModelAtP.comap_curveChange_pi_ofPoint_genericFibre_eq_mul_prod_pow_of_restrictAlong_pointEquivPlace_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/993bc2c4-c947-59e6-8c4e-7788409e26f0

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_AlgebraicGeometry_RelPicardPullback
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivOfPoint
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_DivisorPushPull
import Theorems.Thm_AlgebraicCurve_CurveModel_ker_comap_eq_prod_ker_pow_ramificationIndex
import Theorems.Thm_ModularCurve_XHDRModelAtP_fromSpecStalk_genericPoint_comp_eq_specMap_ffEquiv_degeneracyEmb_of_chartPin
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XHDRModelAtP_comap_curveChange_pi_ofPoint_genericFibre_eq_mul_prod_pow_of_restrictAlong_pointEquivPlace_eq

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1600000

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra AlgebraicCurve IsLocalRing ModularCurve ModularCurve.XHDRLevel AlgebraicGeometry.RelPicard

open scoped MatrixGroups

noncomputable section

namespace IdealDict

open Topology

section FieldMap

variable {X Y Z : Scheme.{u}} [IsIntegral X] [IsIntegral Y] [IsIntegral Z]

theorem apply_genericPoint_eq (f : X ⟶ Y) [Flat f] : f.base (genericPoint X) = genericPoint Y := by
  obtain ⟨a, ha, hfa⟩ := Flat.generalizingMap f (genericPoint_specializes (f.base (genericPoint X)))
  have hgen : IsGenericPoint a (Set.univ : Set X) := by
    rw [isGenericPoint_iff_specializes]
    intro y
    simp only [Set.mem_univ, iff_true]
    exact ha.trans (genericPoint_specializes y)
  have : a = genericPoint X := hgen.eq (genericPoint_spec X)
  rw [← this]; exact hfa

noncomputable def fieldMap (f : X ⟶ Y) (h : f.base (genericPoint X) = genericPoint Y) :
    Y.functionField →+* X.functionField :=
  (f.stalkMap (genericPoint X)).hom.comp
    (Y.presheaf.stalkSpecializes (specializes_of_eq h : f.base (genericPoint X) ⤳ genericPoint Y)).hom

theorem fieldMap_eq (f : X ⟶ Y) (h : f.base (genericPoint X) = genericPoint Y) :
    CommRingCat.ofHom (fieldMap f h) =
      Y.presheaf.stalkSpecializes (specializes_of_eq h : f.base (genericPoint X) ⤳ genericPoint Y) ≫
        f.stalkMap (genericPoint X) := rfl

theorem algebraMap_stalkMap (f : X ⟶ Y) (h : f.base (genericPoint X) = genericPoint Y)
    (p : X) (s : Y.presheaf.stalk (f.base p)) :
    algebraMap _ X.functionField (f.stalkMap p s) = fieldMap f h (algebraMap _ Y.functionField s) := by
  change (X.presheaf.stalkSpecializes (genericPoint_specializes p)).hom (f.stalkMap p s) =
    (f.stalkMap (genericPoint X)).hom ((Y.presheaf.stalkSpecializes _).hom
      ((Y.presheaf.stalkSpecializes (genericPoint_specializes (f.base p))).hom s))
  rw [← Scheme.Hom.stalkSpecializes_stalkMap_apply f (genericPoint X) p (genericPoint_specializes p) s]
  congr 1
  rw [← CommRingCat.comp_apply, TopCat.Presheaf.stalkSpecializes_comp]

theorem fieldMap_germToFunctionField (f : X ⟶ Y) (h : f.base (genericPoint X) = genericPoint Y)
    (U : Y.Opens) [hU : Nonempty (U : Scheme.{u})] [hU' : Nonempty ((f ⁻¹ᵁ U : X.Opens) : Scheme.{u})]
    (s : Γ(Y, U)) :
    fieldMap f h (Y.germToFunctionField U s) = X.germToFunctionField (f ⁻¹ᵁ U) (f.app U s) := by
  have hη : f.base (genericPoint X) ∈ U := by
    rw [h]
    exact ((genericPoint_spec Y).mem_open_set_iff U.2).mpr
      ⟨(Classical.arbitrary (U : Scheme.{u})).1, Set.mem_univ _, (Classical.arbitrary (U : Scheme.{u})).2⟩
  change (f.stalkMap (genericPoint X)).hom ((Y.presheaf.stalkSpecializes _).hom
      ((Y.presheaf.germ U (genericPoint Y) _).hom s)) = (X.presheaf.germ (f ⁻¹ᵁ U) (genericPoint X) _).hom (f.app U s)
  rw [TopCat.Presheaf.germ_stalkSpecializes_apply, Scheme.Hom.germ_stalkMap_apply]

theorem fieldMap_comp (f : X ⟶ Y) (g : Y ⟶ Z) (hf : f.base (genericPoint X) = genericPoint Y)
    (hg : g.base (genericPoint Y) = genericPoint Z) (hfg : (f ≫ g).base (genericPoint X) = genericPoint Z) :
    fieldMap (f ≫ g) hfg = (fieldMap f hf).comp (fieldMap g hg) := by
  apply RingHom.ext
  intro t

  obtain ⟨U, hU, s, rfl⟩ := TopCat.Presheaf.germ_exist (F := Z.presheaf) (x := genericPoint Z) t
  haveI : Nonempty (U : Scheme.{u}) := ⟨⟨_, hU⟩⟩
  have hηY : g.base (genericPoint Y) ∈ U := by rw [hg]; exact hU
  haveI : Nonempty ((g ⁻¹ᵁ U : Y.Opens) : Scheme.{u}) := ⟨⟨_, hηY⟩⟩
  have hηX : (f ≫ g).base (genericPoint X) ∈ U := by rw [hfg]; exact hU
  haveI : Nonempty (((f ≫ g) ⁻¹ᵁ U : X.Opens) : Scheme.{u}) := ⟨⟨_, hηX⟩⟩
  have hηX' : f.base (genericPoint X) ∈ g ⁻¹ᵁ U := by
    show (f ≫ g).base (genericPoint X) ∈ U; exact hηX
  haveI : Nonempty ((f ⁻¹ᵁ (g ⁻¹ᵁ U) : X.Opens) : Scheme.{u}) := ⟨⟨_, hηX'⟩⟩
  have e1 := fieldMap_germToFunctionField (f ≫ g) hfg U s
  have e2 := fieldMap_germToFunctionField g hg U s
  have e3 := fieldMap_germToFunctionField f hf (g ⁻¹ᵁ U) (g.app U s)
  change fieldMap (f ≫ g) hfg (Z.germToFunctionField U s) = fieldMap f hf (fieldMap g hg (Z.germToFunctionField U s))
  rw [e1, e2, e3]
  rfl

theorem fieldMap_eq_of_fromSpecStalk_comp_eq (f : X ⟶ Y) (h : f.base (genericPoint X) = genericPoint Y)
    (c : Y.functionField →+* X.functionField)
    (hc : X.fromSpecStalk (genericPoint X) ≫ f = Spec.map (CommRingCat.ofHom c) ≫ Y.fromSpecStalk (genericPoint Y)) :
    fieldMap f h = c := by
  have key : Spec.map (CommRingCat.ofHom (fieldMap f h)) ≫ Y.fromSpecStalk (genericPoint Y) =
      Spec.map (CommRingCat.ofHom c) ≫ Y.fromSpecStalk (genericPoint Y) := by
    rw [← hc, fieldMap_eq, Spec.map_comp, Category.assoc, Scheme.SpecMap_stalkSpecializes_fromSpecStalk,
      Scheme.SpecMap_stalkMap_fromSpecStalk]
  have := (cancel_mono (Y.fromSpecStalk (genericPoint Y))).mp key
  have := Spec.map_injective this
  exact congrArg CommRingCat.Hom.hom this

end FieldMap

theorem map_maximalIdeal_ringEquiv {A B : Type*} [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B]
    (e : A ≃+* B) : (IsLocalRing.maximalIdeal A).map e.toRingHom = IsLocalRing.maximalIdeal B := by
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap]
    intro x hx
    rw [Ideal.mem_comap]
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hx ⊢
    intro hu
    apply hx
    have h := hu.map e.symm
    simpa using h
  · intro y hy
    have : y = e.toRingHom (e.symm y) := (e.apply_symm_apply y).symm
    rw [this]
    apply Ideal.mem_map_of_mem
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hy ⊢
    intro hu
    apply hy
    have h := hu.map e
    simpa using h

section Restrict

variable {K : Type u} [Field K] [IsAlgClosed K]
  {L : Type u} [Field L] [Algebra K L] {L' : Type u} [Field L'] [Algebra K L']
  (M : CurveModel K L) (M' : CurveModel K L')
  (φ : L' →ₐ[K] L) (hφ : φ.toRingHom.IsIntegral)
  (πM : M.C ⟶ M'.C) (hπM : πM ≫ M'.toBase = M.toBase)
  (hgen : M.C.fromSpecStalk (genericPoint M.C) ≫ πM =
    Spec.map (CommRingCat.ofHom (M.ffEquiv.toRingHom.comp (φ.toRingHom.comp M'.ffEquiv.symm.toRingHom))) ≫
      M'.C.fromSpecStalk (genericPoint M'.C))

def imagePoint (z : {q : Spec (CommRingCat.of K) ⟶ M.C // q ≫ M.toBase = 𝟙 _}) :
    {q : Spec (CommRingCat.of K) ⟶ M'.C // q ≫ M'.toBase = 𝟙 _} :=
  ⟨z.1 ≫ πM, by rw [Category.assoc, hπM]; exact z.2⟩

@[scoped simp] theorem imagePoint_val (z : {q : Spec (CommRingCat.of K) ⟶ M.C // q ≫ M.toBase = 𝟙 _}) :
    (imagePoint M M' πM hπM z).1 = z.1 ≫ πM := rfl

include hgen in
theorem genericPoint_eq : πM.base (genericPoint M.C) = genericPoint M'.C := by
  have h := congrArg (fun g => g.base (IsLocalRing.closedPoint M.C.functionField)) hgen
  simp only [Scheme.Hom.comp_apply, Scheme.fromSpecStalk_closedPoint] at h
  rw [h]
  have : (Spec.map (CommRingCat.ofHom (M.ffEquiv.toRingHom.comp (φ.toRingHom.comp M'.ffEquiv.symm.toRingHom)))).base
      (IsLocalRing.closedPoint M.C.functionField) = IsLocalRing.closedPoint M'.C.functionField := Subsingleton.elim _ _
  rw [this, Scheme.fromSpecStalk_closedPoint]

include hgen in

theorem restrictAlong_pointEquivPlace (z : {q : Spec (CommRingCat.of K) ⟶ M.C // q ≫ M.toBase = 𝟙 _}) :
    (M.pointEquivPlace z).restrictAlong φ hφ = M'.pointEquivPlace (imagePoint M M' πM hπM z) := by
  classical
  set x₀ : ↥M.C := z.1.base (IsLocalRing.closedPoint K) with hx₀
  let x : closedPoints M.C := pointEquivClosedPoint M.toBase z
  let x' : closedPoints M'.C := pointEquivClosedPoint M'.toBase (imagePoint M M' πM hπM z)
  have hxval : x.1 = x₀ := rfl
  have hx'val : x'.1 = πM.base x₀ := by
    show (z.1 ≫ πM).base (IsLocalRing.closedPoint K) = πM.base (z.1.base (IsLocalRing.closedPoint K))
    rw [Scheme.Hom.comp_apply]
  have hξ : πM.base (genericPoint M.C) = genericPoint M'.C := genericPoint_eq M M' φ πM hgen
  have hB : fieldMap πM hξ = M.ffEquiv.toRingHom.comp (φ.toRingHom.comp M'.ffEquiv.symm.toRingHom) :=
    fieldMap_eq_of_fromSpecStalk_comp_eq πM hξ _ hgen
  let S := M.C.presheaf.stalk x₀
  let S' := M'.C.presheaf.stalk (πM.base x₀)
  let ρ : S →+* L := M.ffEquiv.symm.toRingHom.comp (algebraMap S M.C.functionField)
  let ρ' : S' →+* L' := M'.ffEquiv.symm.toRingHom.comp (algebraMap S' M'.C.functionField)
  have hcompat : ∀ t : S', ρ ((πM.stalkMap x₀).hom t) = φ (ρ' t) := fun t => by
    show M.ffEquiv.symm (algebraMap S M.C.functionField ((πM.stalkMap x₀).hom t)) =
      φ (M'.ffEquiv.symm (algebraMap S' M'.C.functionField t))
    rw [algebraMap_stalkMap πM hξ x₀ t, hB]
    simp only [RingHom.coe_comp, RingEquiv.toRingHom_eq_coe, Function.comp_apply, RingHom.coe_coe,
      AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, RingEquiv.symm_apply_apply]
    try rfl
  set w : Place K L := M.pointEquivPlace z with hw
  have hwx : w = M.placeOfPoint x := rfl
  set w' : Place K L' := M'.pointEquivPlace (imagePoint M M' πM hπM z) with hw'
  have hw'x : w' = M'.placeOfPoint ⟨πM.base x₀, hx'val ▸ x'.2⟩ := by
    rw [hw', CurveModel.pointEquivPlace_apply]
    congr 1
  have hrange : ρ.range = w.toValuationSubring.toSubring := M.range_stalk_eq x
  have hrange' : ρ'.range = w'.toValuationSubring.toSubring := by rw [hw'x]; exact M'.range_stalk_eq ⟨πM.base x₀, hx'val ▸ x'.2⟩

  haveI : IsLocalHom (πM.stalkMap x₀).hom := inferInstance
  apply Place.ext
  ext u
  show u ∈ ((M.pointEquivPlace z).restrictAlong φ hφ).toValuationSubring ↔ u ∈ w'.toValuationSubring
  have hmem_iff : u ∈ ((M.pointEquivPlace z).restrictAlong φ hφ).toValuationSubring ↔ φ u ∈ w.toValuationSubring := Iff.rfl
  rw [hmem_iff]
  constructor
  · intro hu

    by_contra hnot
    have hu0 : u ≠ 0 := by rintro rfl; exact hnot (zero_mem _)
    have hinv : u⁻¹ ∈ w'.toValuationSubring := (w'.toValuationSubring.mem_or_inv_mem u).resolve_left hnot

    have ht : u⁻¹ ∈ ρ'.range := by rw [hrange']; exact hinv
    obtain ⟨t, htu⟩ := ht
    have htnu : ¬ IsUnit t := by
      intro htU
      apply hnot

      obtain ⟨tu, rfl⟩ := htU
      have : u = ρ' (↑tu⁻¹ : S') := by
        have h1 : ρ' (↑tu : S') * ρ' (↑tu⁻¹ : S') = 1 := by rw [← map_mul, Units.mul_inv, map_one]
        rw [htu] at h1
        calc u = u * (u⁻¹ * ρ' (↑tu⁻¹ : S')) := by rw [h1, mul_one]
          _ = ρ' (↑tu⁻¹ : S') := by rw [← mul_assoc, mul_inv_cancel₀ hu0, one_mul]
      rw [this, ← ValuationSubring.mem_toSubring, ← hrange']
      exact ⟨_, rfl⟩

    have himg : ¬ IsUnit ((πM.stalkMap x₀).hom t) := fun h => htnu (isUnit_of_map_unit (πM.stalkMap x₀).hom t h)
    apply himg

    have hρinj : Function.Injective ρ := M.ffEquiv.symm.injective.comp (IsFractionRing.injective S M.C.functionField)
    have hval : ρ ((πM.stalkMap x₀).hom t) = (φ u)⁻¹ := by rw [hcompat, htu, map_inv₀]

    have hs : φ u ∈ ρ.range := by rw [hrange]; exact hu
    obtain ⟨s, hsu⟩ := hs
    have hmul : (πM.stalkMap x₀).hom t * s = 1 := by
      apply hρinj
      rw [map_mul, hval, hsu, map_one, inv_mul_cancel₀]
      intro h0
      exact hu0 ((map_eq_zero φ).mp h0)
    exact IsUnit.of_mul_eq_one _ hmul
  · intro hu
    have ht : u ∈ ρ'.range := by rw [hrange']; exact hu
    obtain ⟨t, rfl⟩ := ht
    rw [← hcompat, ← ValuationSubring.mem_toSubring, ← hrange]
    exact ⟨_, rfl⟩

end Restrict

section Enum

variable {K : Type u} [Field K] [IsAlgClosed K]
  {L : Type u} [Field L] [Algebra K L] {L' : Type u} [Field L'] [Algebra K L']
  [IsCurveOver K L] [IsCurveOver K L'] [Algebra.EssFiniteType K L] [Algebra.EssFiniteType K L']
  (M : CurveModel K L) (M' : CurveModel K L')
  (φ : L' →ₐ[K] L) (hφ : φ.toRingHom.IsIntegral)
  (πM : M.C ⟶ M'.C) (hπM : πM ≫ M'.toBase = M.toBase)
  (hgen : M.C.fromSpecStalk (genericPoint M.C) ≫ πM =
    Spec.map (CommRingCat.ofHom (M.ffEquiv.toRingHom.comp (φ.toRingHom.comp M'.ffEquiv.symm.toRingHom))) ≫
      M'.C.fromSpecStalk (genericPoint M'.C))
  [IsFinite πM] [Flat πM] [LocallyOfFinitePresentation πM]

include hgen hπM in

theorem ker_comap_eq_ker_mul_prod
    (y : {q : Spec (CommRingCat.of K) ⟶ M.C // q ≫ M.toBase = 𝟙 _})
    (hw₀ : Place.ramificationIndexAlong φ (M.pointEquivPlace y) = 1)
    (k : ℕ) (y' : Fin k → {q : Spec (CommRingCat.of K) ⟶ M.C // q ≫ M.toBase = 𝟙 _}) (e : Fin k → ℕ)
    (hinj : Function.Injective y') (hne : ∀ j, y' j ≠ y)
    (hfib : ∀ j, (M.pointEquivPlace (y' j)).restrictAlong φ hφ = (M.pointEquivPlace y).restrictAlong φ hφ)
    (hall : ∀ w : Place K L, w.restrictAlong φ hφ = (M.pointEquivPlace y).restrictAlong φ hφ → w ≠ M.pointEquivPlace y →
      ∃ j, w = M.pointEquivPlace (y' j))
    (he : ∀ j, e j = Place.ramificationIndexAlong φ (M.pointEquivPlace (y' j))) :
    (∀ j, (y' j).1 ≫ πM = y.1 ≫ πM) ∧
    ((y.1 ≫ πM).ker.comap πM = y.1.ker * ∏ j, (y' j).1.ker ^ (e j)) := by
  classical
  letI := algebraAlong φ
  haveI := isScalarTower_along φ
  haveI := isIntegral_along φ hφ

  set v := imagePoint M M' πM hπM y with hv
  have hR : ∀ z : {q : Spec (CommRingCat.of K) ⟶ M.C // q ≫ M.toBase = 𝟙 _},
      (M.pointEquivPlace z).restrict L' = M'.pointEquivPlace (imagePoint M M' πM hπM z) :=
    fun z => restrictAlong_pointEquivPlace M M' φ hφ πM hπM hgen z

  have h1 : ∀ j, (y' j).1 ≫ πM = y.1 ≫ πM := by
    intro j
    have hj : M'.pointEquivPlace (imagePoint M M' πM hπM (y' j)) = M'.pointEquivPlace v := by
      rw [← hR, ← hR]; exact hfib j
    have := M'.pointEquivPlace.injective hj
    exact congrArg Subtype.val this
  refine ⟨h1, ?_⟩

  have hplace : ∀ (a : {q : Spec (CommRingCat.of K) ⟶ M.C // q ≫ M.toBase = 𝟙 _})
      (x : {q : Spec (CommRingCat.of K) ⟶ M'.C // q ≫ M'.toBase = 𝟙 _}),
      a.1 ≫ πM = x.1 → (M.pointEquivPlace a).restrict L' = M'.pointEquivPlace x := by
    intro a x hax
    rw [hR]
    congr 1
    exact Subtype.ext hax
  have key := AlgebraicCurve.CurveModel.ker_comap_eq_prod_ker_pow_ramificationIndex M' M πM hπM hplace v
  rw [show (y.1 ≫ πM) = v.1 from rfl, key]

  set W₀ := M.pointEquivPlace y with hW₀
  set W : Fin k → Place K L := fun j => M.pointEquivPlace (y' j) with hW
  have hWinj : Function.Injective W := fun a b h => hinj (M.pointEquivPlace.injective h)
  have hW₀v : W₀.restrict L' = M'.pointEquivPlace v := hR y
  have hfiber : (M'.pointEquivPlace v).fiber L = insert W₀ (Finset.univ.image W) := by
    ext w
    rw [Place.mem_fiber, Finset.mem_insert, Finset.mem_image]
    constructor
    · intro hw
      by_cases hw0 : w = W₀
      · exact Or.inl hw0
      · obtain ⟨j, rfl⟩ := hall w (by rw [← hW₀v] at hw; exact hw) hw0
        exact Or.inr ⟨j, Finset.mem_univ _, rfl⟩
    · rintro (rfl | ⟨j, -, rfl⟩)
      · exact hW₀v
      · show (M.pointEquivPlace (y' j)).restrict L' = _
        have := hfib j
        change (M.pointEquivPlace (y' j)).restrict L' = W₀.restrict L' at this
        rw [this, hW₀v]
  have hW₀nmem : W₀ ∉ Finset.univ.image W := by
    rw [Finset.mem_image]
    rintro ⟨j, -, hj⟩
    exact hne j (M.pointEquivPlace.injective hj)
  rw [hfiber, Finset.prod_insert hW₀nmem, Finset.prod_image (fun a _ b _ h => hWinj h)]
  congr 1
  · rw [hW₀, Equiv.symm_apply_apply]
    change y.1.ker ^ Place.ramificationIndexAlong φ (M.pointEquivPlace y) = _
    rw [hw₀, pow_one]
  · refine Finset.prod_congr rfl fun j _ => ?_
    show (M.pointEquivPlace.symm (M.pointEquivPlace (y' j))).1.ker ^ Place.ramificationIndexAlong φ (M.pointEquivPlace (y' j)) = _
    rw [Equiv.symm_apply_apply, ← he]

end Enum

section IsoTransport

variable {X Y W : Scheme.{u}}

theorem ker_comap_of_isIso (i : W ⟶ Y) [IsClosedImmersion i] (g : X ⟶ Y) [IsIso g] :
    i.ker.comap g = (i ≫ inv g).ker := by
  rw [← Scheme.IdealSheafData.ker_fst_of_isClosedImmersion i g]
  have h : pullback.fst g i = pullback.snd g i ≫ (i ≫ inv g) := by
    rw [← Category.assoc, ← pullback.condition, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  rw [h, Scheme.Hom.ker_comp_of_isIso]

theorem comap_mul_of_isIso (I J : Y.IdealSheafData) (g : X ⟶ Y) [IsIso g] :
    (I * J).comap g = I.comap g * J.comap g := by
  refine Scheme.IdealSheafData.ext (funext fun U => ?_)
  rw [Scheme.IdealSheafData.ideal_mul, Pi.mul_apply, Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion,
    Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion, Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion,
    Scheme.IdealSheafData.ideal_mul, Pi.mul_apply]
  set e := (g.appIso U) with he

  have hc : ∀ K : Ideal Γ(Y, g ''ᵁ U), K.comap e.inv.hom = K.map e.hom.hom := by
    intro K
    apply le_antisymm
    · intro x hx
      rw [Ideal.mem_comap] at hx
      have : x = e.hom.hom (e.inv.hom x) := by
        change x = (e.inv ≫ e.hom).hom x
        rw [e.inv_hom_id]; rfl
      rw [this]; exact Ideal.mem_map_of_mem _ hx
    · rw [Ideal.map_le_iff_le_comap]
      intro k hk
      rw [Ideal.mem_comap, Ideal.mem_comap]
      have : e.inv.hom (e.hom.hom k) = k := by
        change (e.hom ≫ e.inv).hom k = k
        rw [e.hom_inv_id]; rfl
      rw [this]; exact hk
  rw [hc, hc, hc, Ideal.map_mul]

def comapMonoidHom (g : X ⟶ Y) [IsIso g] : Y.IdealSheafData →* X.IdealSheafData where
  toFun I := I.comap g
  map_one' := Scheme.IdealSheafData.comap_top g
  map_mul' I J := comap_mul_of_isIso I J g

theorem comapMonoidHom_apply (g : X ⟶ Y) [IsIso g] (I : Y.IdealSheafData) : comapMonoidHom g I = I.comap g := rfl

end IsoTransport

end IdealDict
p2m_reactivate "P2MW.S_ModularCurve_XHDRModelAtP_comap_curveChange_pi_ofPoint_genericFibre_eq_mul_prod_pow_of_restrictAlong_pointEquivPlace_eq.IdealDict"

end
p2m_reactivate "P2MW.S_ModularCurve_XHDRModelAtP_comap_curveChange_pi_ofPoint_genericFibre_eq_mul_prod_pow_of_restrictAlong_pointEquivPlace_eq.IdealDict"

open IdealDict in
theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) [NeZero (M / p)]
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)
    (αH : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hα : ∀ u : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)), ((αH u : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)))
    (hαint : αH.toRingHom.IsIntegral)
    (Meta₀ : CurveModel (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)))
    (eeta₀ : Meta₀.C ⟶ pullback (toBase p (XHDRLevel.ΓN p M H hpM) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ)))))
    [IsIso eeta₀]
    (heeta₀ : eeta₀ ≫ pullback.snd _ _ = Meta₀.toBase)
    (hne₀ : Nonempty (Scheme.Opens.toScheme ((eeta₀ ≫ pullback.fst (toBase p (XHDRLevel.ΓN p M H hpM) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ))))) ⁻¹ᵁ ((ιFin p (XHDRLevel.ΓN p M H hpM) hj) ''ᵁ ⊤))))
    (hpin₀ : haveI := hne₀
      ∀ a : ↥(chartAlgFin p (XHDRLevel.ΓN p M H hpM) hj),
            ((Meta₀.ffEquiv.symm
                (Meta₀.C.germToFunctionField
                  ((eeta₀ ≫ pullback.fst (toBase p (XHDRLevel.ΓN p M H hpM) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ))))) ⁻¹ᵁ ((ιFin p (XHDRLevel.ΓN p M H hpM) hj) ''ᵁ ⊤))
                  (((eeta₀ ≫ pullback.fst (toBase p (XHDRLevel.ΓN p M H hpM) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ))))).app ((ιFin p (XHDRLevel.ΓN p M H hpM) hj) ''ᵁ ⊤)).hom
                    (((ιFin p (XHDRLevel.ΓN p M H hpM) hj).appIso ⊤).inv
                      ((Scheme.ΓSpecIso (CommRingCat.of ↥(chartAlgFin p (XHDRLevel.ΓN p M H hpM) hj))).inv a))))
                : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) : LaurentSeries (AlgebraicClosure ℚ)) =
              coeffEmb (AlgebraicClosure ℚ) ((a : ↥(qExpFunctionFieldC ℚ (XHDRLevel.ΓN p M H hpM))) : LaurentSeries ℚ))
    [IsSeparated (toBase p (ΓM M H) hj)] [IsSeparated (toBase p (ΓN p M H hpM) hj)]

    [IsCurveOver (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)] [IsCurveOver (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))]
    [Algebra.EssFiniteType (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)]
    [Algebra.EssFiniteType (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))]

    [IsFinite (curveChange 𝔛.π.1 𝔛.π.2 (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ)))))]
    [Flat (curveChange 𝔛.π.1 𝔛.π.2 (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ)))))]
    [LocallyOfFinitePresentation (curveChange 𝔛.π.1 𝔛.π.2 (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ)))))]

    (y : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _})
    (hw₀ : Place.ramificationIndexAlong αH (𝔛.Meta.pointEquivPlace y) = 1)
    (k : ℕ) (y' : Fin k → {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _}) (e : Fin k → ℕ)
    (hinj : Function.Injective y') (hne : ∀ j, y' j ≠ y)
    (hfib : ∀ j, (𝔛.Meta.pointEquivPlace (y' j)).restrictAlong αH hαint = (𝔛.Meta.pointEquivPlace y).restrictAlong αH hαint)
    (hall : ∀ w : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H),
      w.restrictAlong αH hαint = (𝔛.Meta.pointEquivPlace y).restrictAlong αH hαint → w ≠ 𝔛.Meta.pointEquivPlace y →
        ∃ j, w = 𝔛.Meta.pointEquivPlace (y' j))
    (he : ∀ j, e j = Place.ramificationIndexAlong αH (𝔛.Meta.pointEquivPlace (y' j))) :

    (∀ j, (y' j).1 ≫ 𝔛.eeta ≫ pullback.fst _ _ ≫ 𝔛.π.1 = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ ≫ 𝔛.π.1) ∧

    (RelEffCartierDiv.ofPoint (toBase p (ΓN p M H hpM) hj) ((y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _) ≫ 𝔛.π.1)
        (g := Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ))))
        (by rw [Category.assoc, 𝔛.π.2, Category.assoc, Category.assoc, pullback.condition, ← Category.assoc 𝔛.eeta, 𝔛.heeta,
              ← Category.assoc, y.2, Category.id_comp])).I.comap
        (curveChange 𝔛.π.1 𝔛.π.2 (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ))))) =
      (RelEffCartierDiv.ofPoint (toBase p (ΓM M H) hj) (y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _)
          (g := Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ))))
          (by rw [Category.assoc, Category.assoc, pullback.condition, ← Category.assoc 𝔛.eeta, 𝔛.heeta, ← Category.assoc, y.2, Category.id_comp])).I *
        ∏ j, (RelEffCartierDiv.ofPoint (toBase p (ΓM M H) hj) ((y' j).1 ≫ 𝔛.eeta ≫ pullback.fst _ _)
            (g := Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ))))
            (by rw [Category.assoc, Category.assoc, pullback.condition, ← Category.assoc 𝔛.eeta, 𝔛.heeta, ← Category.assoc, (y' j).2,
                  Category.id_comp])).I ^ (e j) := by
  classical

  let sa := Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ)))
  let ee : 𝔛.Meta.C ⟶ pullback (toBase p (ΓM M H) hj) sa := 𝔛.eeta
  let e₀ : Meta₀.C ⟶ pullback (toBase p (ΓN p M H hpM) hj) sa := eeta₀
  let cc : pullback (toBase p (ΓM M H) hj) sa ⟶ pullback (toBase p (ΓN p M H hpM) hj) sa := curveChange 𝔛.π.1 𝔛.π.2 sa
  haveI : IsIso ee := 𝔛.eeta_iso
  have hcc_fst : cc ≫ pullback.fst _ _ = pullback.fst _ _ ≫ 𝔛.π.1 := pullback.lift_fst _ _ _
  have hcc_snd : cc ≫ pullback.snd _ _ = pullback.snd _ _ := by
    show curveChange 𝔛.π.1 𝔛.π.2 sa ≫ _ = _
    rw [curveChange_snd]

  let πM : 𝔛.Meta.C ⟶ Meta₀.C := ee ≫ cc ≫ inv e₀
  have hπM : πM ≫ Meta₀.toBase = 𝔛.Meta.toBase := by
    show (ee ≫ cc ≫ inv e₀) ≫ Meta₀.toBase = _
    rw [← heeta₀, Category.assoc, Category.assoc, IsIso.inv_hom_id_assoc, hcc_snd]
    exact 𝔛.heeta
  have hπM₁ : πM ≫ eeta₀ ≫ pullback.fst _ _ = 𝔛.eeta ≫ pullback.fst _ _ ≫ 𝔛.π.1 := by
    show (ee ≫ cc ≫ inv e₀) ≫ e₀ ≫ _ = _
    rw [Category.assoc, Category.assoc, IsIso.inv_hom_id_assoc, hcc_fst]
  have hgen := ModularCurve.XHDRModelAtP.fromSpecStalk_genericPoint_comp_eq_specMap_ffEquiv_degeneracyEmb_of_chartPin
    p M H hpM hj 𝔛 αH hα Meta₀ eeta₀ heeta₀ hne₀ hpin₀ πM hπM₁ hπM

  have hci : ∀ z : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _}, IsClosedImmersion z.1 := by
    intro z
    have : IsClosedImmersion (z.1 ≫ 𝔛.Meta.toBase) := by rw [z.2]; infer_instance
    exact .of_comp z.1 𝔛.Meta.toBase
  haveI : IsClosedImmersion y.1 := hci y
  haveI : ∀ j, IsClosedImmersion (y' j).1 := fun j => hci (y' j)
  haveI : IsClosedImmersion (y.1 ≫ πM) := by
    have : IsClosedImmersion ((y.1 ≫ πM) ≫ Meta₀.toBase) := by rw [Category.assoc, hπM, y.2]; infer_instance
    exact .of_comp (y.1 ≫ πM) Meta₀.toBase
  haveI : IsFinite πM := inferInstance
  haveI : Flat πM := inferInstance
  haveI : LocallyOfFinitePresentation πM := inferInstance

  obtain ⟨h1, h2⟩ := ker_comap_eq_ker_mul_prod 𝔛.Meta Meta₀ αH hαint πM hπM hgen y hw₀ k y' e hinj hne hfib hall he
  refine ⟨fun j => ?_, ?_⟩
  ·
    have := congrArg (· ≫ e₀ ≫ pullback.fst _ _) (h1 j)
    simp only [Category.assoc] at this
    rw [hπM₁] at this
    simpa only [Category.assoc] using this
  ·

    have hyP : graphOver (toBase p (ΓM M H) hj) (y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _) (g := sa)
        (by rw [Category.assoc, Category.assoc, pullback.condition, ← Category.assoc 𝔛.eeta, 𝔛.heeta, ← Category.assoc, y.2, Category.id_comp]) =
        y.1 ≫ ee := by
      apply pullback.hom_ext
      · rw [graphOver_fst, Category.assoc]
      · rw [graphOver_snd, Category.assoc, 𝔛.heeta, y.2]
    have hy'P : ∀ j, graphOver (toBase p (ΓM M H) hj) ((y' j).1 ≫ 𝔛.eeta ≫ pullback.fst _ _) (g := sa)
        (by rw [Category.assoc, Category.assoc, pullback.condition, ← Category.assoc 𝔛.eeta, 𝔛.heeta, ← Category.assoc, (y' j).2, Category.id_comp]) =
        (y' j).1 ≫ ee := by
      intro j
      apply pullback.hom_ext
      · rw [graphOver_fst, Category.assoc]
      · rw [graphOver_snd, Category.assoc, 𝔛.heeta, (y' j).2]
    have hvP : graphOver (toBase p (ΓN p M H hpM) hj) ((y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _) ≫ 𝔛.π.1) (g := sa)
        (by rw [Category.assoc, 𝔛.π.2, Category.assoc, Category.assoc, pullback.condition, ← Category.assoc 𝔛.eeta, 𝔛.heeta,
              ← Category.assoc, y.2, Category.id_comp]) =
        y.1 ≫ ee ≫ cc := by
      apply pullback.hom_ext
      · rw [graphOver_fst]; simp only [Category.assoc, hcc_fst]; rfl
      · rw [graphOver_snd, Category.assoc, Category.assoc, hcc_snd, 𝔛.heeta, y.2]
    rw [RelEffCartierDiv.ofPoint_I, RelEffCartierDiv.ofPoint_I, hyP, hvP]
    simp_rw [RelEffCartierDiv.ofPoint_I]

    have h2' := congrArg (fun I : 𝔛.Meta.C.IdealSheafData => I.comap (inv ee)) h2

    have hL : ((y.1 ≫ πM).ker.comap πM).comap (inv ee) = (y.1 ≫ ee ≫ cc).ker.comap cc := by
      rw [← Scheme.IdealSheafData.comap_comp, show inv ee ≫ πM = cc ≫ inv e₀ by
            show inv ee ≫ ee ≫ cc ≫ inv e₀ = _; rw [IsIso.inv_hom_id_assoc],
        Scheme.IdealSheafData.comap_comp, ker_comap_of_isIso, IsIso.inv_inv]
      show ((y.1 ≫ ee ≫ cc ≫ inv e₀) ≫ e₀).ker.comap cc = _
      simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]

    have hR : (y.1.ker * ∏ j, (y' j).1.ker ^ e j).comap (inv ee) = (y.1 ≫ ee).ker * ∏ j, ((y' j).1 ≫ ee).ker ^ e j := by
      rw [← comapMonoidHom_apply, map_mul, map_prod]
      simp only [map_pow, comapMonoidHom_apply]
      rw [ker_comap_of_isIso, IsIso.inv_inv]
      congr 1
      refine Finset.prod_congr rfl fun j _ => ?_
      rw [ker_comap_of_isIso, IsIso.inv_inv]
    rw [hL, hR] at h2'
    rw [h2']
    congr 1
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [hy'P j]

end S_ModularCurve_XHDRModelAtP_comap_curveChange_pi_ofPoint_genericFibre_eq_mul_prod_pow_of_restrictAlong_pointEquivPlace_eq
end P2MW
export P2MW.S_ModularCurve_XHDRModelAtP_comap_curveChange_pi_ofPoint_genericFibre_eq_mul_prod_pow_of_restrictAlong_pointEquivPlace_eq (solution)
