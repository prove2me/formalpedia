-- Prove2me | solution 1 for GoodReductionJacobian.RelativeGroupLaw.exists_sheaf_smallFppfTopology_sectionsEquiv_of_isCommutative
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/8a219071-b62e-56bc-a9e1-478bdd787248

import Mathlib
import Definitions.Def_AlgebraicGeometry_FppfSiteCohomology
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Theorems.Thm_AlgebraicGeometry_Scheme_isSheaf_smallFppfTopology_forget_op_comp_yoneda_obj
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_sheaf_smallFppfTopology_sectionsEquiv_of_isCommutative

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme NeronModelInfra GoodReductionJacobian

universe u

noncomputable section

namespace P3Glue

variable {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}
  (G : RelativeGroupLaw R f) (hG : G.IsCommutative)

@[reducible] def ptCommGroup (U : (Spec (CommRingCat.of R)).Fppf) : CommGroup (SchemeHomOver U.hom f) :=
  { G.pointGroup U.hom with mul_comm := fun x y => hG U.hom x y }

abbrev PtsCarrier (U : (Spec (CommRingCat.of R)).Fppf) : Type (u + 1) :=
  ULift.{u + 1} (Additive (SchemeHomOver U.hom f))

abbrev instAddCommGroupPtsCarrier (U : (Spec (CommRingCat.of R)).Fppf) : AddCommGroup (PtsCarrier (f := f) U) :=
  letI : CommGroup (SchemeHomOver U.hom f) := ptCommGroup G hG U
  inferInstance

def resAdd {U V : (Spec (CommRingCat.of R)).Fppf} (k : U ⟶ V) :
    letI := instAddCommGroupPtsCarrier G hG V
    letI := instAddCommGroupPtsCarrier G hG U
    PtsCarrier (f := f) V →+ PtsCarrier (f := f) U :=
  letI := instAddCommGroupPtsCarrier G hG V
  letI := instAddCommGroupPtsCarrier G hG U
  { toFun := fun x => ⟨Additive.ofMul (schemeHomOverComp k.left (MorphismProperty.Over.w k) (Additive.toMul x.down))⟩
    map_zero' := by
      apply ULift.ext
      exact congrArg Additive.ofMul (G.one_natural V.hom U.hom k.left (MorphismProperty.Over.w k))
    map_add' := fun x y => by
      apply ULift.ext
      exact congrArg Additive.ofMul
        (G.mul_natural V.hom U.hom k.left (MorphismProperty.Over.w k) (Additive.toMul x.down) (Additive.toMul y.down)) }

theorem resAdd_apply {U V : (Spec (CommRingCat.of R)).Fppf} (k : U ⟶ V) (x : PtsCarrier (f := f) V) :
    resAdd G hG k x =
      ⟨Additive.ofMul (schemeHomOverComp k.left (MorphismProperty.Over.w k) (Additive.toMul x.down))⟩ :=
  rfl

def ptsPresheaf : ((Spec (CommRingCat.of R)).Fppf)ᵒᵖ ⥤ Ab.{u + 1} where
  obj U := @AddCommGrpCat.of (PtsCarrier (f := f) (unop U)) (instAddCommGroupPtsCarrier G hG (unop U))
  map k := @AddCommGrpCat.ofHom _ _ (instAddCommGroupPtsCarrier G hG _) (instAddCommGroupPtsCarrier G hG _)
    (resAdd G hG k.unop)
  map_id U := by
    refine AddCommGrpCat.ext fun x => ?_
    change resAdd G hG (𝟙 (unop U)) x = x
    rw [resAdd_apply]
    exact congrArg ULift.up (congrArg Additive.ofMul
      (Subtype.ext (Category.id_comp _) : schemeHomOverComp _ _ (Additive.toMul x.down) = Additive.toMul x.down))
  map_comp k l := by
    refine AddCommGrpCat.ext fun x => ?_
    change resAdd G hG (l.unop ≫ k.unop) x = resAdd G hG l.unop (resAdd G hG k.unop x)
    rw [resAdd_apply, resAdd_apply, resAdd_apply]
    exact congrArg ULift.up (congrArg Additive.ofMul (Subtype.ext (Category.assoc _ _ _)))

theorem ptsPresheaf_map_apply {U V : ((Spec (CommRingCat.of R)).Fppf)ᵒᵖ} (k : U ⟶ V) (x : PtsCarrier (f := f) (unop U)) :
    (ptsPresheaf G hG).map k x =
      ⟨Additive.ofMul (schemeHomOverComp k.unop.left (MorphismProperty.Over.w k.unop) (Additive.toMul x.down))⟩ :=
  rfl

theorem ptsPresheaf_isSheaf : Presheaf.IsSheaf (smallFppfTopology (Spec (CommRingCat.of R))) (ptsPresheaf G hG) := by
  rw [Presheaf.isSheaf_iff_isSheaf_forget (smallFppfTopology (Spec (CommRingCat.of R))) _ (forget Ab.{u + 1}),
    isSheaf_iff_isSheaf_of_type]
  refine Presieve.isSheaf_of_nat_equiv
    (P₁ := (Scheme.Fppf.forget (Spec (CommRingCat.of R))).op ⋙ yoneda.obj (Over.mk f))
    (P₂ := ptsPresheaf G hG ⋙ forget Ab.{u + 1})
    (fun U => (Equiv.trans
      { toFun := fun y => Additive.ofMul (⟨y.left, Over.w y⟩ : SchemeHomOver U.hom f)
        invFun := fun x => Over.homMk (Additive.toMul x).1 (Additive.toMul x).2
        left_inv := fun y => Over.OverMorphism.ext rfl
        right_inv := fun x => rfl } Equiv.ulift.symm)) ?_
    ((isSheaf_iff_isSheaf_of_type _ _).mp
      (AlgebraicGeometry.Scheme.isSheaf_smallFppfTopology_forget_op_comp_yoneda_obj
        (Spec (CommRingCat.of R)) (Over.mk f)))
  intro U V k y
  rfl

def ptsSheaf : Sheaf (smallFppfTopology (Spec (CommRingCat.of R))) Ab.{u + 1} :=
  ⟨ptsPresheaf G hG, ptsPresheaf_isSheaf G hG⟩

theorem pow_eq_nsmul {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x : SchemeHomOver t f) (n : ℕ) :
    (letI := G.pointGroup t; x ^ n) = G.nsmul t n x := by
  induction n with
  | zero => rfl
  | succ n ih =>
    letI := G.pointGroup t
    change x ^ (n + 1) = G.mul t (G.nsmul t n x) x
    rw [pow_succ, ih]
    rfl

theorem coe_nsmul {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x : SchemeHomOver t f) (n : ℕ) :
    (G.nsmul t n x).1 = x.1 ≫ G.schemeNsmul n := by
  have hx : schemeHomOverComp x.1 x.2 (RelativeGroupLaw.idPoint (f := f)) = x :=
    Subtype.ext (Category.comp_id _)
  have h := G.nsmul_natural f t x.1 x.2 n RelativeGroupLaw.idPoint
  rw [hx] at h
  rw [← h]
  rfl

end P3Glue
p2m_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_sheaf_smallFppfTopology_sectionsEquiv_of_isCommutative.P3Glue"

end
p2m_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_sheaf_smallFppfTopology_sectionsEquiv_of_isCommutative.P3Glue"

open P3Glue in

theorem solution
    {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}
    (G : RelativeGroupLaw R f) (hG : G.IsCommutative) :
    ∃ (𝒢 : Sheaf (smallFppfTopology (Spec (CommRingCat.of R))) Ab.{u + 1})
      (e : ∀ U : (Spec (CommRingCat.of R)).Fppf, 𝒢.1.obj (op U) ≃ SchemeHomOver U.hom f),
      (∀ (U : (Spec (CommRingCat.of R)).Fppf) (s s' : 𝒢.1.obj (op U)),
          e U (s + s') = G.mul U.hom (e U s) (e U s')) ∧
      (∀ {U V : (Spec (CommRingCat.of R)).Fppf} (k : U ⟶ V) (s : 𝒢.1.obj (op V)),
          e U (𝒢.1.map k.op s) = schemeHomOverComp k.left (MorphismProperty.Over.w k) (e V s)) ∧
      (∀ (n : ℕ) (U : (Spec (CommRingCat.of R)).Fppf) (s : 𝒢.1.obj (op U)),
          (e U (((n : ℤ) • 𝟙 𝒢 : 𝒢 ⟶ 𝒢).1.app (op U) s)).1 = (e U s).1 ≫ G.schemeNsmul n) := by
  classical
  refine ⟨ptsSheaf G hG, fun U => Equiv.ulift.trans Additive.toMul, ?_, ?_, ?_⟩
  · intro U s s'
    rfl
  · intro U V k s
    rfl
  · intro n U s

    letI := G.pointGroup U.hom
    have h1 : (((n : ℤ) • 𝟙 (ptsSheaf G hG) : ptsSheaf G hG ⟶ ptsSheaf G hG).1.app (op U) s) = (n : ℤ) • s := by
      rfl
    rw [h1]
    change (Additive.toMul (((n : ℤ) • s).down)).1 = (Additive.toMul s.down).1 ≫ G.schemeNsmul n
    rw [← coe_nsmul G U.hom, ← pow_eq_nsmul G U.hom]
    rfl

end S_GoodReductionJacobian_RelativeGroupLaw_exists_sheaf_smallFppfTopology_sectionsEquiv_of_isCommutative
end P2MW
export P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_sheaf_smallFppfTopology_sectionsEquiv_of_isCommutative (solution)
