-- Prove2me | solution 1 for N25.RatPointModel.exists_localRealization
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:30:43.304429+00:00
-- url     : https://prove2.me/submissions/c9b75a32-299d-4ed0-8d1c-db695ff4781f

import Mathlib
import Definitions.Def_N25_RatPointModel
import Definitions.Def_N25_LocalCarrier
import Theorems.Thm_N25_RatPointModel_barMap_injective
import Theorems.Thm_N25_RatPointModel_localMap_injective
import Theorems.Thm_AlgebraicGeometry_Scheme_exists_specMap_fixedField_comp_eq_of_forall_comp_eq
import Theorems.Thm_KeystoneLadder_SameP1Vec_trans

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency.types false

noncomputable section

open CategoryTheory AlgebraicGeometry GoodReductionJacobian

namespace N25

local instance instL_N25_RatPointModel_exists_localRealizatio_bfd51b_s6f0e77 : Fact (Nat.Prime 5) := ⟨by decide⟩

local instance instL_N25_RatPointModel_exists_localRealizatio_3dbe1c_s6f0e77 : IsScalarTower ℚ ℚ_[5] (PadicAlgCl 5) :=
  IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)

/-- Fixed geometric morphisms over the local algebraic closure descend to the local field. -/
private theorem local_point_descent {X : Scheme.{0}}
    (x : Spec (CommRingCat.of (PadicAlgCl 5)) ⟶ X)
    (hx : ∀ τ : G5, Spec.map (CommRingCat.ofHom τ.toRingHom) ≫ x = x) :
    ∃ y : Spec (CommRingCat.of ℚ_[5]) ⟶ X,
      Spec.map (CommRingCat.ofHom (algebraMap ℚ_[5] (PadicAlgCl 5))) ≫ y = x := by
  letI : IsAlgClosure ℚ_[5] (PadicAlgCl 5) :=
    { isAlgClosed := AlgebraicClosure.isAlgClosed ℚ_[5]
      isAlgebraic := ⟨fun z => by
        have hz : IsIntegral ℚ_[5] z := by
          convert ((AlgebraicClosure.isAlgebraic ℚ_[5]).isAlgebraic z).isIntegral
        exact hz.isAlgebraic⟩ }
  letI : IsGalois ℚ_[5] (PadicAlgCl 5) :=
    { to_isSeparable := IsAlgClosure.separable ℚ_[5] (PadicAlgCl 5)
      to_normal := IsAlgClosure.normal ℚ_[5] (PadicAlgCl 5) }
  have hd := Scheme.exists_specMap_fixedField_comp_eq_of_forall_comp_eq
    (⊤ : Subgroup (PadicAlgCl 5 ≃ₐ[ℚ_[5]] PadicAlgCl 5)) x (fun τ _ => hx τ)
  rw [InfiniteGalois.fixedField_bot] at hd
  obtain ⟨y, hy⟩ := hd
  let e := IntermediateField.botEquiv ℚ_[5] (PadicAlgCl 5)
  refine ⟨Spec.map (CommRingCat.ofHom e.toRingHom) ≫ y, ?_⟩
  rw [← Category.assoc, ← Spec.map_comp]
  convert hy using 2
  congr 1
  apply CommRingCat.hom_ext
  ext a
  exact congrArg Subtype.val (e.symm_apply_apply a)

/-- Compatibility of the prescribed completion embedding with local restriction. -/
private theorem completion_action (D : RatPointModel) (τ : G5) (x : J) :
    Spec.map (CommRingCat.ofHom τ.toRingHom) ≫
      (RelativeGroupLaw.AlgPoints.toPoint (D.barMap (D.pts x))).1 =
      (RelativeGroupLaw.AlgPoints.toPoint (D.barMap (D.pts (r5 τ • x)))).1 := by
  rw [D.equivariant]
  change Spec.map (CommRingCat.ofHom τ.toRingHom) ≫
      (Spec.map (CommRingCat.ofHom (padicEmbedding 5).toRingHom) ≫
        (RelativeGroupLaw.AlgPoints.toPoint (D.pts x)).1) =
    Spec.map (CommRingCat.ofHom (padicEmbedding 5).toRingHom) ≫
      (Spec.map (CommRingCat.ofHom (r5 τ).toRingHom) ≫
        (RelativeGroupLaw.AlgPoints.toPoint (D.pts x)).1)
  have hc : CommRingCat.ofHom (padicEmbedding 5).toRingHom ≫ CommRingCat.ofHom τ.toRingHom =
      CommRingCat.ofHom (r5 τ).toRingHom ≫ CommRingCat.ofHom (padicEmbedding 5).toRingHom := by
    apply CommRingCat.hom_ext
    ext z
    exact (padicEmbedding_localGaloisToGlobal 5 τ z).symm
  rw [← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp]
  exact congrArg (fun g : CommRingCat.of (AlgebraicClosure ℚ) ⟶ CommRingCat.of (PadicAlgCl 5) =>
    Spec.map g ≫ (RelativeGroupLaw.AlgPoints.toPoint (D.pts x)).1) hc

/-- Local points extend to morphisms fixed by every local automorphism. -/
private theorem local_map_fixed (D : RatPointModel) (τ : G5) (y : D.Local) :
    Spec.map (CommRingCat.ofHom τ.toRingHom) ≫
      (RelativeGroupLaw.AlgPoints.toPoint (D.localMap y)).1 =
      (RelativeGroupLaw.AlgPoints.toPoint (D.localMap y)).1 := by
  change Spec.map (CommRingCat.ofHom τ.toRingHom) ≫
      (Spec.map (CommRingCat.ofHom (algebraMap ℚ_[5] (PadicAlgCl 5))) ≫
        (RelativeGroupLaw.AlgPoints.toPoint y).1) =
    Spec.map (CommRingCat.ofHom (algebraMap ℚ_[5] (PadicAlgCl 5))) ≫
      (RelativeGroupLaw.AlgPoints.toPoint y).1
  have hc : CommRingCat.ofHom (algebraMap ℚ_[5] (PadicAlgCl 5)) ≫
      CommRingCat.ofHom τ.toRingHom =
      CommRingCat.ofHom (algebraMap ℚ_[5] (PadicAlgCl 5)) := by
    apply CommRingCat.hom_ext
    ext a
    exact τ.commutes a
  rw [← Category.assoc, ← Spec.map_comp]
  exact congrArg (fun g : CommRingCat.of ℚ_[5] ⟶ CommRingCat.of (PadicAlgCl 5) =>
    Spec.map g ≫ (RelativeGroupLaw.AlgPoints.toPoint y).1) hc

/-- A fixed global algebraic point has a unique local rational realization. -/
private theorem exists_local_point (D : RatPointModel) (x : ↥M5) :
    ∃ y : D.Local, D.localMap y = D.barMap (D.pts (x : J)) := by
  let z := D.barMap (D.pts (x : J))
  obtain ⟨y, hy⟩ := local_point_descent (RelativeGroupLaw.AlgPoints.toPoint z).1
    (fun τ => (completion_action D τ x).trans (by rw [x.2 τ]))
  let a := IsScalarTower.toAlgHom ℚ ℚ_[5] (PadicAlgCl 5)
  let b := Spec.map (CommRingCat.ofHom a.toRingHom)
  letI : Epi b := Flat.epi_of_flat_of_surjective b
  have hyover : y ≫ D.f = Spec.map (CommRingCat.ofHom (algebraMap ℚ ℚ_[5])) := by
    apply (cancel_epi b).mp
    rw [← Category.assoc]
    change (Spec.map (CommRingCat.ofHom (algebraMap ℚ_[5] (PadicAlgCl 5))) ≫ y) ≫ D.f = _
    rw [hy, (RelativeGroupLaw.AlgPoints.toPoint z).2]
    exact (RelativeGroupLaw.AlgPoints.specMap_comp_algebraMap a).symm
  refine ⟨RelativeGroupLaw.AlgPoints.ofPoint ⟨y, hyover⟩, ?_⟩
  apply RelativeGroupLaw.AlgPoints.toPoint_injective
  apply Subtype.ext
  exact hy

/-- Local fixed points are precisely local points whose extension is globally algebraic. -/
theorem _root_.solution (D : RatPointModel) :
    ∃ e : ↥M5 →+ D.Local,
      Function.Injective e ∧
      (∀ x : ↥M5, D.localMap (e x) = D.barMap (D.pts (x : J))) ∧
      (∀ y : D.Local, y ∈ e.range ↔ D.localMap y ∈ D.barMap.range) := by
  choose lift hlift using exists_local_point D
  let e : ↥M5 →+ D.Local := AddMonoidHom.mk' lift (fun x y => by
    apply D.localMap_injective
    simp only [map_add, hlift, AddSubgroup.coe_add])
  have he (x : ↥M5) : D.localMap (e x) = D.barMap (D.pts (x : J)) := hlift x
  refine ⟨e, ?_, he, ?_⟩
  · intro x y h
    apply Subtype.ext
    apply D.pts.injective
    apply D.barMap_injective
    rw [← he, ← he, h]
  · intro y
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨D.pts (x : J), (he x).symm⟩
    · rintro ⟨z, hz⟩
      let x := D.pts.symm z
      have hfixed : x ∈ M5 := by
        intro τ
        apply D.pts.injective
        apply D.barMap_injective
        apply RelativeGroupLaw.AlgPoints.toPoint_injective
        apply Subtype.ext
        rw [← completion_action, D.pts.apply_symm_apply, hz]
        exact local_map_fixed D τ y
      refine ⟨⟨x, hfixed⟩, ?_⟩
      apply D.localMap_injective
      rw [he]
      exact (congrArg D.barMap (D.pts.apply_symm_apply z)).trans hz

end N25
