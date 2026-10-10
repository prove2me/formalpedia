-- Prove2me | solution 1 for MazurTransfer.represented_picard_field_points_classify_line_bundles
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-09T21:50:59.183411+00:00
-- url     : https://prove2.me/submissions/a44a7da7-5482-45d6-8ded-1db2b3282203

import Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_linearEquiv_sectionsOf_of_iso
import Theorems.Thm_AlgebraicGeometry_RelPicard_isAlgEquivZero_iff_eulerChar_sectionsOf_eq
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_nonempty_iso_tensorUnit_of_field
import Definitions.Def_AlgebraicGeometry_RelPicardAbelJacobiFamily
import Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_sectionsOf_baseChange_equiv_of_locallyTrivial
section
/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Complete conjugation/base-change and Euler-characteristic helper proofs reused
from official Anthropic FLT at 6e837e75355538c7f80bab5b956861e86c4eacc2.
Design boundary: make dependencies used by the field-point classification
explicit without relying on implementation namespaces in platform imports.
Named downstream consumer: the unchanged actual order-13 Picard field-point
and line-bundle classification on Prove2Me.
-/
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open scoped TensorProduct
namespace MazurTransfer.UniversalFieldPointPublicHelpers
section Conj

variable {R : Type*} [CommRing R] {M N M' N' : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  [AddCommGroup M'] [Module R M'] [AddCommGroup N'] [Module R N']

noncomputable def kerEquivOfConj (f : M →ₗ[R] N) (f' : M' →ₗ[R] N') (eM : M ≃ₗ[R] M') (eN : N ≃ₗ[R] N')
    (h : ∀ x, eN (f x) = f' (eM x)) : LinearMap.ker f ≃ₗ[R] LinearMap.ker f' :=
  LinearEquiv.ofSubmodules eM (LinearMap.ker f) (LinearMap.ker f') (by
    ext y
    simp only [Submodule.mem_map, LinearMap.mem_ker]
    constructor
    · rintro ⟨x, hx, rfl⟩
      rw [LinearEquiv.coe_coe, ← h, hx, map_zero]
    · intro hy
      refine ⟨eM.symm y, ?_, by simp⟩
      apply eN.injective
      rw [h, LinearEquiv.apply_symm_apply, hy, map_zero])

noncomputable def cokerEquivOfConj (f : M →ₗ[R] N) (f' : M' →ₗ[R] N') (eM : M ≃ₗ[R] M') (eN : N ≃ₗ[R] N')
    (h : ∀ x, eN (f x) = f' (eM x)) : (N ⧸ LinearMap.range f) ≃ₗ[R] (N' ⧸ LinearMap.range f') :=
  Submodule.Quotient.equiv (LinearMap.range f) (LinearMap.range f') eN (by
    ext y
    simp only [Submodule.mem_map, LinearMap.mem_range]
    constructor
    · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
      exact ⟨eM x, (h x).symm⟩
    · rintro ⟨x, rfl⟩
      exact ⟨f (eM.symm x), ⟨_, rfl⟩, by rw [LinearEquiv.coe_coe, h, LinearEquiv.apply_symm_apply]⟩)

end Conj

section Coker

variable {R : Type*} [CommRing R] {C0 C1 : Type*} [AddCommGroup C0] [Module R C0] [AddCommGroup C1] [Module R C1]

theorem nonempty_cokerBaseChangeEquiv (d : C0 →ₗ[R] C1) (A : Type*) [CommRing A] [Algebra R A] :
    Nonempty (((A ⊗[R] C1) ⧸ LinearMap.range (d.baseChange A)) ≃ₗ[A] A ⊗[R] (C1 ⧸ LinearMap.range d)) := by
  let q : C1 →ₗ[R] C1 ⧸ LinearMap.range d := (LinearMap.range d).mkQ
  let qA : A ⊗[R] C1 →ₗ[A] A ⊗[R] (C1 ⧸ LinearMap.range d) := q.baseChange A
  have hsurj : Function.Surjective qA := by
    rw [show (qA : A ⊗[R] C1 → A ⊗[R] (C1 ⧸ LinearMap.range d)) = LinearMap.lTensor A q from
      LinearMap.baseChange_eq_ltensor q]
    exact LinearMap.lTensor_surjective A (Submodule.mkQ_surjective _)
  have hker : LinearMap.ker qA = LinearMap.range (d.baseChange A) := by
    have h1 : LinearMap.ker (LinearMap.lTensor A q) = LinearMap.range (LinearMap.lTensor A d) := by
      rw [lTensor_mkQ]
      have hd : d = (LinearMap.range d).subtype ∘ₗ d.rangeRestrict := LinearMap.ext fun _ => rfl
      conv_rhs => rw [hd, LinearMap.lTensor_comp]
      rw [LinearMap.range_comp_of_range_eq_top]
      exact LinearMap.range_eq_top.mpr (LinearMap.lTensor_surjective A (LinearMap.surjective_rangeRestrict d))
    ext x
    rw [LinearMap.mem_ker, LinearMap.mem_range]
    have hx : qA x = LinearMap.lTensor A q x := congrFun (LinearMap.baseChange_eq_ltensor q) x
    rw [hx, ← LinearMap.mem_ker, h1, LinearMap.mem_range]
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨y, (congrFun (LinearMap.baseChange_eq_ltensor d) y)⟩
    · rintro ⟨y, rfl⟩
      exact ⟨y, (congrFun (LinearMap.baseChange_eq_ltensor d) y).symm⟩
  exact ⟨(Submodule.quotEquivOfEq _ _ hker.symm).trans (qA.quotKerEquivOfSurjective hsurj)⟩

end Coker

section FieldExt

variable {R : Type*} [CommRing R] {C0 C1 : Type*} [AddCommGroup C0] [Module R C0] [AddCommGroup C1] [Module R C1]

theorem nonempty_kerBaseChangeEquiv_of_flat {K : Type*} [CommRing K] {V0 V1 : Type*} [AddCommGroup V0] [Module K V0]
    [AddCommGroup V1] [Module K V1] (δ : V0 →ₗ[K] V1) (K' : Type*) [CommRing K'] [Algebra K K'] [Module.Flat K K'] :
    Nonempty (LinearMap.ker (δ.baseChange K') ≃ₗ[K'] K' ⊗[K] LinearMap.ker δ) := by
  let ι : K' ⊗[K] LinearMap.ker δ →ₗ[K'] K' ⊗[K] V0 := (LinearMap.ker δ).subtype.baseChange K'
  have hι : ∀ x, δ.baseChange K' (ι x) = 0 := by
    intro x
    rw [← LinearMap.comp_apply, ← LinearMap.baseChange_comp, LinearMap.comp_ker_subtype, LinearMap.baseChange_zero,
      LinearMap.zero_apply]
  let j : K' ⊗[K] LinearMap.ker δ →ₗ[K'] LinearMap.ker (δ.baseChange K') := ι.codRestrict _ hι
  have hinj : Function.Injective j := by
    intro x y hxy
    have : ι x = ι y := congrArg Subtype.val hxy
    have hιinj : Function.Injective ι := by
      rw [show (ι : K' ⊗[K] LinearMap.ker δ → K' ⊗[K] V0) = LinearMap.lTensor K' (LinearMap.ker δ).subtype from
        LinearMap.baseChange_eq_ltensor _]
      exact Module.Flat.lTensor_preserves_injective_linearMap _ Subtype.val_injective
    exact hιinj this
  have hsurj : Function.Surjective j := by
    rintro ⟨x, hx⟩
    have hex : Function.Exact (LinearMap.lTensor K' (LinearMap.ker δ).subtype) (LinearMap.lTensor K' δ) :=
      Module.Flat.lTensor_exact K' (LinearMap.exact_subtype_ker_map δ)
    have hx' : LinearMap.lTensor K' δ x = 0 := by
      rw [← congrFun (LinearMap.baseChange_eq_ltensor δ) x]; exact hx
    obtain ⟨y, hy⟩ := (hex x).mp hx'
    refine ⟨y, Subtype.ext ?_⟩
    change ι y = x
    rw [← hy]
    exact congrFun (LinearMap.baseChange_eq_ltensor _) y
  exact ⟨(LinearEquiv.ofBijective j ⟨hinj, hsurj⟩).symm⟩

theorem baseChange_baseChange_conj (d : C0 →ₗ[R] C1) (K K' : Type*) [CommRing K] [CommRing K'] [Algebra R K]
    [Algebra R K'] [Algebra K K'] [IsScalarTower R K K'] (x : K' ⊗[K] (K ⊗[R] C0)) :
    TensorProduct.AlgebraTensorModule.cancelBaseChange R K K' K' C1 ((d.baseChange K).baseChange K' x) =
      d.baseChange K' (TensorProduct.AlgebraTensorModule.cancelBaseChange R K K' K' C0 x) := by
  rw [LinearMap.baseChange_baseChange]
  simp

theorem finrank_ker_coker_baseChange_field {K : Type*} [Field K] {V0 V1 : Type*} [AddCommGroup V0] [Module K V0]
    [AddCommGroup V1] [Module K V1] (δ : V0 →ₗ[K] V1) (K' : Type*) [Field K'] [Algebra K K'] :
    Module.finrank K' (LinearMap.ker (δ.baseChange K')) = Module.finrank K (LinearMap.ker δ) ∧
    Module.finrank K' ((K' ⊗[K] V1) ⧸ LinearMap.range (δ.baseChange K')) =
      Module.finrank K (V1 ⧸ LinearMap.range δ) := by
  obtain ⟨eker⟩ := nonempty_kerBaseChangeEquiv_of_flat δ K'
  obtain ⟨ecok⟩ := nonempty_cokerBaseChangeEquiv δ K'
  exact ⟨eker.finrank_eq.trans Module.finrank_baseChange, ecok.finrank_eq.trans Module.finrank_baseChange⟩

theorem finrank_ker_coker_baseChange_eq (d : C0 →ₗ[R] C1) (K K' : Type*) [Field K] [Field K'] [Algebra R K]
    [Algebra R K'] [Algebra K K'] [IsScalarTower R K K'] :
    Module.finrank K' (LinearMap.ker (d.baseChange K')) = Module.finrank K (LinearMap.ker (d.baseChange K)) ∧
    Module.finrank K' ((K' ⊗[R] C1) ⧸ LinearMap.range (d.baseChange K')) =
      Module.finrank K ((K ⊗[R] C1) ⧸ LinearMap.range (d.baseChange K)) := by
  have hconj := baseChange_baseChange_conj d K K'
  let eK : LinearMap.ker ((d.baseChange K).baseChange K') ≃ₗ[K'] LinearMap.ker (d.baseChange K') :=
    kerEquivOfConj _ _ (TensorProduct.AlgebraTensorModule.cancelBaseChange R K K' K' C0)
      (TensorProduct.AlgebraTensorModule.cancelBaseChange R K K' K' C1) hconj
  let eC : ((K' ⊗[K] (K ⊗[R] C1)) ⧸ LinearMap.range ((d.baseChange K).baseChange K')) ≃ₗ[K']
      ((K' ⊗[R] C1) ⧸ LinearMap.range (d.baseChange K')) :=
    cokerEquivOfConj _ _ (TensorProduct.AlgebraTensorModule.cancelBaseChange R K K' K' C0)
      (TensorProduct.AlgebraTensorModule.cancelBaseChange R K K' K' C1) hconj
  obtain ⟨hk, hc⟩ := finrank_ker_coker_baseChange_field (d.baseChange K) K'
  exact ⟨eK.finrank_eq.symm.trans hk, eC.finrank_eq.symm.trans hc⟩

end FieldExt

universe u

theorem twoAffineOpenCover_ext {Y : Scheme.{u}} {𝒲 𝒲' : Y.TwoAffineOpenCover}
    (h0 : 𝒲.U0 = 𝒲'.U0) (h1 : 𝒲.U1 = 𝒲'.U1) : 𝒲 = 𝒲' := by
  obtain ⟨U0, U1, _, _, _, _⟩ := 𝒲
  obtain ⟨U0', U1', _, _, _, _⟩ := 𝒲'
  dsimp only at h0 h1
  subst h0
  subst h1
  rfl

theorem preimage_id_opens {Y : Scheme.{u}} (U : Y.Opens) : (𝟙 Y) ⁻¹ᵁ U = U := rfl


theorem nonempty_linearEquiv_of_iso {k : Type u} [Field k] {Y : Scheme.{u}} (y : Y ⟶ Spec (CommRingCat.of k))
    (𝒲 : Y.TwoAffineOpenCover) {M M' : Y.Modules} (e : M ≅ M') :
    Nonempty ((𝒲.sectionsOf y M).H0 ≃ₗ[k] (𝒲.sectionsOf y M').H0) ∧
      Nonempty ((𝒲.sectionsOf y M).H1 ≃ₗ[k] (𝒲.sectionsOf y M').H1) := by
  obtain ⟨𝒲', h0, h1, ⟨e0⟩, ⟨e1⟩⟩ :=
    Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_of_iso y y (Iso.refl Y) (Category.id_comp y)
      𝒲 M' M (e ≪≫ ((Scheme.Modules.pullbackId Y).app M').symm)
  have h𝒲 : 𝒲' = 𝒲 :=
    twoAffineOpenCover_ext (h0.trans (preimage_id_opens _)) (h1.trans (preimage_id_opens _))
  subst h𝒲
  exact ⟨⟨e0⟩, ⟨e1⟩⟩

theorem eulerChar_congr {k : Type u} [Field k] {Y : Scheme.{u}} (y : Y ⟶ Spec (CommRingCat.of k))
    (𝒲 : Y.TwoAffineOpenCover) {M M' : Y.Modules} (e : M ≅ M') :
    (Module.finrank k (𝒲.sectionsOf y M).H0 : ℤ) - Module.finrank k (𝒲.sectionsOf y M).H1
      = (Module.finrank k (𝒲.sectionsOf y M').H0 : ℤ) - Module.finrank k (𝒲.sectionsOf y M').H1 := by
  obtain ⟨⟨e0⟩, ⟨e1⟩⟩ := nonempty_linearEquiv_of_iso y 𝒲 e
  rw [e0.finrank_eq, e1.finrank_eq]



noncomputable def pullbackCompCompIso {X Y Z W : Scheme.{u}} (f : X ⟶ Y) (s : Y ⟶ Z) (q : Z ⟶ W) (g : X ⟶ W)
    (hfac : (f ≫ s) ≫ q = g) (L : W.Modules) :
    (Scheme.Modules.pullback (f ≫ s)).obj ((Scheme.Modules.pullback q).obj L) ≅ (Scheme.Modules.pullback g).obj L :=
  (Scheme.Modules.pullbackComp (f ≫ s) q).app L ≪≫ (Scheme.Modules.pullbackCongr hfac).app L


noncomputable def isoPullbackInvPullbackObj {X Y : Scheme.{u}} (p : X ⟶ Y) [IsIso p] (L : Y.Modules) :
    L ≅ (Scheme.Modules.pullback (inv p)).obj ((Scheme.Modules.pullback p).obj L) :=
  ((Scheme.Modules.pullbackComp (inv p) p ≪≫ Scheme.Modules.pullbackCongr (IsIso.inv_hom_id p) ≪≫
      Scheme.Modules.pullbackId Y).app L).symm


#print axioms finrank_ker_coker_baseChange_field
#print axioms eulerChar_congr
end MazurTransfer.UniversalFieldPointPublicHelpers
end
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open AlgebraicGeometry.RelPicard NeronModelInfra GoodReductionJacobian
section
/-
Copyright (c) 2026 Vas and contributors. All rights reserved.
Released under Apache-2.0 license as described in the file LICENSE.

Design boundary: both cohomology dimensions of a line bundle on a genuine
two-affine cover are preserved by a field extension. Named downstream consumer:
the degree-zero condition over F₃ and F₅ for the actual order-13 Picard scheme.
The section base-change and conjugation proofs are reused from official
Anthropic FLT at 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
No algebraic-closure assumption is imposed on the base or extension field.
-/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct
open MazurTransfer.UniversalFieldPointPublicHelpers

namespace MazurTransfer.UniversalLineBundleFieldComparison

private theorem finrank_ker_coker_eq_of_sections_equiv
    {k : Type u} [Field k] {K : Type u} [Field K] [Algebra k K]
    {P0 P1 P01 : Type u} [AddCommGroup P0] [Module k P0]
    [AddCommGroup P1] [Module k P1] [AddCommGroup P01] [Module k P01]
    (r0 : P0 →ₗ[k] P01) (r1 : P1 →ₗ[k] P01)
    {Q0 Q1 Q01 : Type u} [AddCommGroup Q0] [Module K Q0]
    [AddCommGroup Q1] [Module K Q1] [AddCommGroup Q01] [Module K Q01]
    (s0 : Q0 →ₗ[K] Q01) (s1 : Q1 →ₗ[K] Q01)
    (e0 : K ⊗[k] P0 ≃ₗ[K] Q0) (e1 : K ⊗[k] P1 ≃ₗ[K] Q1)
    (e01 : K ⊗[k] P01 ≃ₗ[K] Q01)
    (h0 : ∀ x, e01 ((r0.baseChange K) x) = s0 (e0 x))
    (h1 : ∀ x, e01 ((r1.baseChange K) x) = s1 (e1 x)) :
    Module.finrank K (LinearMap.ker ((-s0).coprod s1)) =
      Module.finrank k (LinearMap.ker ((-r0).coprod r1)) ∧
    Module.finrank K (Q01 ⧸ LinearMap.range ((-s0).coprod s1)) =
      Module.finrank k (P01 ⧸ LinearMap.range ((-r0).coprod r1)) := by
  let d : P0 × P1 →ₗ[k] P01 := (-r0).coprod r1
  let d' : Q0 × Q1 →ₗ[K] Q01 := (-s0).coprod s1
  let E : K ⊗[k] (P0 × P1) ≃ₗ[K] Q0 × Q1 :=
    TensorProduct.prodRight k K K P0 P1 ≪≫ₗ e0.prodCongr e1
  have hsq : ∀ z, e01 ((d.baseChange K) z) = d' (E z) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a p =>
      obtain ⟨p0, p1⟩ := p
      have hr0 : e01 (a ⊗ₜ[k] r0 p0) = s0 (e0 (a ⊗ₜ[k] p0)) := by
        have h := h0 (a ⊗ₜ[k] p0)
        rwa [LinearMap.baseChange_tmul] at h
      have hr1 : e01 (a ⊗ₜ[k] r1 p1) = s1 (e1 (a ⊗ₜ[k] p1)) := by
        have h := h1 (a ⊗ₜ[k] p1)
        rwa [LinearMap.baseChange_tmul] at h
      simp only [E, d, d', LinearMap.baseChange_tmul, LinearMap.coprod_apply,
        LinearMap.neg_apply, LinearEquiv.trans_apply, TensorProduct.prodRight_tmul,
        LinearEquiv.prodCongr_apply, TensorProduct.tmul_add, TensorProduct.tmul_neg,
        map_add, map_neg, hr0, hr1]
    | add x y hx hy => simp only [map_add, hx, hy]
  have ek := kerEquivOfConj (d.baseChange K) d' E e01 hsq
  have ec := cokerEquivOfConj (d.baseChange K) d' E e01 hsq
  have hr := finrank_ker_coker_baseChange_field d K
  exact ⟨ek.finrank_eq.symm.trans hr.1, ec.finrank_eq.symm.trans hr.2⟩

/-- Both Čech cohomology dimensions of an invertible sheaf survive every field extension. -/
theorem finrank_H0_H1_baseChange
    {k : Type u} [Field k] {X : Scheme.{u}}
    (x : X ⟶ Spec (CommRingCat.of k)) (𝒱 : X.TwoAffineOpenCover)
    (M : X.Modules) (hM : Scheme.Modules.IsInvertible M)
    (K : Type u) [Field K] [Algebra k K] :
    Module.finrank K
        ((𝒱.pullback x K).sectionsOf (pullback.snd x (Scheme.TwoAffineOpenCover.specMap k K))
          ((Scheme.Modules.pullback (pullback.fst x (Scheme.TwoAffineOpenCover.specMap k K))).obj M)).H0 =
      Module.finrank k (𝒱.sectionsOf x M).H0 ∧
    Module.finrank K
        ((𝒱.pullback x K).sectionsOf (pullback.snd x (Scheme.TwoAffineOpenCover.specMap k K))
          ((Scheme.Modules.pullback (pullback.fst x (Scheme.TwoAffineOpenCover.specMap k K))).obj M)).H1 =
      Module.finrank k (𝒱.sectionsOf x M).H1 := by
  obtain ⟨e0, e1, e01, h0, h1, _, _, _⟩ :=
    Scheme.TwoAffineOpenCover.exists_sectionsOf_baseChange_equiv_of_locallyTrivial 𝒱 x M hM.1 K
  exact finrank_ker_coker_eq_of_sections_equiv _ _ _ _ e0 e1 e01 h0 h1


end MazurTransfer.UniversalLineBundleFieldComparison
end


section
/-
Copyright (c) 2026 Vas and contributors. All rights reserved.
Released under Apache-2.0 license as described in the file LICENSE.

Design boundary: characterize geometric algebraic equivalence to zero using
the Euler characteristic over the actual base field. Named downstream consumer:
the arithmetic divisor-class/Jacobian comparison for the order-13 curve over
F₃ and F₅. This does not assert that the base field is algebraically closed.
Generic geometric comparison and sheaf pullback proofs are reused from official
Anthropic FLT at 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
-/

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra
open AlgebraicGeometry.RelPicard
open MazurTransfer.UniversalFieldPointPublicHelpers

namespace MazurTransfer.UniversalLineBundleFieldComparison

noncomputable def curveEulerChar {k : Type u} [Field k] {X : Scheme.{u}}
    (x : X ⟶ Spec (CommRingCat.of k)) (𝒱 : X.TwoAffineOpenCover) (M : X.Modules) : ℤ :=
  (Module.finrank k (𝒱.sectionsOf x M).H0 : ℤ) - Module.finrank k (𝒱.sectionsOf x M).H1

/-- A geometric degree-zero condition, quantified over algebraically closed extensions.
It concerns the actual sheaf and actual base-change scheme, without a rational-point
parametrization of all closed points. -/
def GeometricallyAlgEquivZero {k : Type u} [Field k] {X : Scheme.{u}}
    (x : X ⟶ Spec (CommRingCat.of k)) (M : X.Modules) : Prop :=
  ∀ (K : Type u) [Field K] [Algebra k K] [IsAlgClosed K],
    IsAlgEquivZero (pullback.snd x (Scheme.TwoAffineOpenCover.specMap k K))
      ((Scheme.Modules.pullback (pullback.fst x (Scheme.TwoAffineOpenCover.specMap k K))).obj M)

theorem curveEulerChar_baseChange
    {k : Type u} [Field k] {X : Scheme.{u}}
    (x : X ⟶ Spec (CommRingCat.of k)) (𝒱 : X.TwoAffineOpenCover)
    (M : X.Modules) (hM : Scheme.Modules.IsInvertible M)
    (K : Type u) [Field K] [Algebra k K] :
    curveEulerChar (pullback.snd x (Scheme.TwoAffineOpenCover.specMap k K)) (𝒱.pullback x K)
        ((Scheme.Modules.pullback (pullback.fst x (Scheme.TwoAffineOpenCover.specMap k K))).obj M) =
      curveEulerChar x 𝒱 M := by
  obtain ⟨h0, h1⟩ := finrank_H0_H1_baseChange x 𝒱 M hM K
  unfold curveEulerChar
  rw [h0, h1]

private theorem unit_curveEulerChar_baseChange
    {k : Type u} [Field k] {X : Scheme.{u}}
    (x : X ⟶ Spec (CommRingCat.of k)) (𝒱 : X.TwoAffineOpenCover)
    (K : Type u) [Field K] [Algebra k K] :
    curveEulerChar (pullback.snd x (Scheme.TwoAffineOpenCover.specMap k K)) (𝒱.pullback x K)
        (𝟙_ (pullback x (Scheme.TwoAffineOpenCover.specMap k K)).Modules) =
      curveEulerChar x 𝒱 (𝟙_ X.Modules) := by
  have he := eulerChar_congr (pullback.snd x (Scheme.TwoAffineOpenCover.specMap k K))
    (𝒱.pullback x K)
    (Scheme.Modules.pullbackTensorUnitObjIso (pullback.fst x (Scheme.TwoAffineOpenCover.specMap k K)))
  exact he.symm.trans (curveEulerChar_baseChange x 𝒱 (𝟙_ X.Modules)
    (Scheme.Modules.isInvertible_unit X) K)

/-- Over an arbitrary base field, geometric algebraic equivalence to zero is
equivalent to equality with the structure sheaf's Euler characteristic over that field. -/
theorem geometricallyAlgEquivZero_iff_curveEulerChar_eq
    (k : Type u) [Field k] {X : Scheme.{u}}
    (x : X ⟶ Spec (CommRingCat.of k))
    [IsProper x] [SmoothOfRelativeDimension 1 x] [GeometricallyIntegral x]
    (M : X.Modules) (hM : Scheme.Modules.IsInvertible M) (𝒱 : X.TwoAffineOpenCover) :
    GeometricallyAlgEquivZero x M ↔ curveEulerChar x 𝒱 M = curveEulerChar x 𝒱 (𝟙_ X.Modules) := by
  have key : ∀ (K : Type u) [Field K] [Algebra k K] [IsAlgClosed K],
      IsAlgEquivZero (pullback.snd x (Scheme.TwoAffineOpenCover.specMap k K))
          ((Scheme.Modules.pullback (pullback.fst x (Scheme.TwoAffineOpenCover.specMap k K))).obj M) ↔
        curveEulerChar x 𝒱 M = curveEulerChar x 𝒱 (𝟙_ X.Modules) := by
    intro K _ _ _
    let y := pullback.snd x (Scheme.TwoAffineOpenCover.specMap k K)
    let N := (Scheme.Modules.pullback (pullback.fst x (Scheme.TwoAffineOpenCover.specMap k K))).obj M
    letI := smoothOfRelativeDimension_isStableUnderBaseChange 1
    haveI : SmoothOfRelativeDimension 1 y :=
      MorphismProperty.IsStableUnderBaseChange.of_isPullback
        (P := (@SmoothOfRelativeDimension 1 : MorphismProperty Scheme.{u}))
        (IsPullback.of_hasPullback x (Scheme.TwoAffineOpenCover.specMap k K))
        (inferInstance : SmoothOfRelativeDimension 1 x)
    haveI : IsIntegral (pullback x (Scheme.TwoAffineOpenCover.specMap k K)) :=
      pullback_of_geometrically
        (GeometricallyIntegral.geometrically_isIntegral (f := x))
        K (Scheme.TwoAffineOpenCover.specMap k K)
    have hk := isAlgEquivZero_iff_eulerChar_sectionsOf_eq K y N
      (hM.pullback (pullback.fst x (Scheme.TwoAffineOpenCover.specMap k K))) (𝒱.pullback x K)
    change IsAlgEquivZero y N ↔
      curveEulerChar y (𝒱.pullback x K) N =
        curveEulerChar y (𝒱.pullback x K) (𝟙_ (pullback x (Scheme.TwoAffineOpenCover.specMap k K)).Modules) at hk
    rw [curveEulerChar_baseChange x 𝒱 M hM K, unit_curveEulerChar_baseChange x 𝒱 K] at hk
    exact hk
  constructor
  · intro h
    exact (key (AlgebraicClosure k)).mp (h (AlgebraicClosure k))
  · intro h K _ _ _
    exact (key K).mpr h


end MazurTransfer.UniversalLineBundleFieldComparison
end


section
/-
Copyright (c) 2026 Vas and contributors. All rights reserved.
Released under Apache-2.0 license as described in the file LICENSE.

Design boundary: attach an actual line bundle on the original curve to each
base-field point of a represented degree-zero Picard scheme, prove geometric
degree zero and detect equality by sheaf isomorphism. Named downstream consumer:
the finite-field order-13 divisor-class/Jacobian comparison. The constructions
use the official Anthropic FLT relative Picard interface at commit
6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0, and do not require an
algebraically closed base field or a point/divisor-class dictionary.
-/

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
open AlgebraicGeometry.RelPicard
open MazurTransfer.UniversalFieldPointPublicHelpers

namespace MazurTransfer.UniversalLineBundleFieldComparison

noncomputable def pointLineBundle {k : Type u} [Field k] {X : Scheme.{u}}
    (x : X ⟶ Spec (CommRingCat.of k))
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) x)
    (D : RelativePic0Designation k x)
    (h : RepresentsRelSubPic x ε (algEquivZeroCut x ε) D)
    (a : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) D.toBase) : X.Modules :=
  (Scheme.Modules.pullback (toProdSpec x)).obj (h.poincare.pullbackAlong a).L

theorem pointLineBundle_isInvertible {k : Type u} [Field k] {X : Scheme.{u}}
    (x : X ⟶ Spec (CommRingCat.of k))
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) x)
    (D : RelativePic0Designation k x)
    (h : RepresentsRelSubPic x ε (algEquivZeroCut x ε) D)
    (a : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) D.toBase) :
    Scheme.Modules.IsInvertible (pointLineBundle x ε D h a) :=
  (h.poincare.pullbackAlong a).isInvertible.pullback (toProdSpec x)

theorem pointLineBundle_geometricallyAlgEquivZero {k : Type u} [Field k] {X : Scheme.{u}}
    (x : X ⟶ Spec (CommRingCat.of k))
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) x)
    (D : RelativePic0Designation k x)
    (h : RepresentsRelSubPic x ε (algEquivZeroCut x ε) D)
    (a : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) D.toBase) :
    GeometricallyAlgEquivZero x (pointLineBundle x ε D h a) := by
  intro K _ _ _
  let s := Scheme.TwoAffineOpenCover.specMap k K
  let P := (h.poincare.pullbackAlong a).L
  let g := toProdSpec x
  have hg : g ≫ pullback.snd x (𝟙 _) = x := pullback.lift_snd _ _ _
  let f : pullback x s ⟶ pullback (pullback.snd x (𝟙 (Spec (CommRingCat.of k)))) s :=
    pullback.lift (pullback.fst x s ≫ g) (pullback.snd x s)
      (by rw [Category.assoc, hg, pullback.condition])
  have hf : f ≫ fibreAt x (𝟙 _) s = pullback.snd x s := pullback.lift_snd _ _ _
  have hfac : f ≫ pullback.fst (pullback.snd x (𝟙 _)) s = pullback.fst x s ≫ g :=
    pullback.lift_fst _ _ _
  have hzero := (algEquivZeroCut x ε).pullback_mem _ _ a _ h.poincare_mem
  exact ((hzero K s).pullback f hf).of_iso
    ((Scheme.Modules.pullbackComp f (pullback.fst (pullback.snd x (𝟙 _)) s)).app P ≪≫
      (Scheme.Modules.pullbackCongr hfac).app P ≪≫
      ((Scheme.Modules.pullbackComp (pullback.fst x s) g).app P).symm)

/-- The original curve's line bundle detects equality of base-field Picard points. -/
theorem pointLineBundle_iso_iff {k : Type u} [Field k] {X : Scheme.{u}}
    (x : X ⟶ Spec (CommRingCat.of k))
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) x)
    (D : RelativePic0Designation k x)
    (h : RepresentsRelSubPic x ε (algEquivZeroCut x ε) D)
    (a b : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) D.toBase) :
    Nonempty (pointLineBundle x ε D h a ≅ pointLineBundle x ε D h b) ↔ a = b := by
  constructor
  · rintro ⟨e⟩
    let g := toProdSpec x
    letI : IsIso g := ⟨⟨pullback.fst x (𝟙 _), toProdSpec_fst x, fst_toProdSpec x⟩⟩
    exact h.ext_of_iso (𝟙 _) a b
      ⟨isoPullbackInvPullbackObj g (h.poincare.pullbackAlong a).L ≪≫
        (Scheme.Modules.pullback (inv g)).mapIso e ≪≫
        (isoPullbackInvPullbackObj g (h.poincare.pullbackAlong b).L).symm⟩
  · rintro rfl
    exact ⟨Iso.refl _⟩

/-- The degree-zero Euler-characteristic identity holds over the base field itself. -/
theorem pointLineBundle_curveEulerChar_eq {k : Type u} [Field k] {X : Scheme.{u}}
    (x : X ⟶ Spec (CommRingCat.of k))
    [IsProper x] [SmoothOfRelativeDimension 1 x] [GeometricallyIntegral x]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) x)
    (D : RelativePic0Designation k x)
    (h : RepresentsRelSubPic x ε (algEquivZeroCut x ε) D)
    (a : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) D.toBase)
    (𝒱 : X.TwoAffineOpenCover) :
    curveEulerChar x 𝒱 (pointLineBundle x ε D h a) = curveEulerChar x 𝒱 (𝟙_ X.Modules) :=
  (geometricallyAlgEquivZero_iff_curveEulerChar_eq k x (pointLineBundle x ε D h a)
    (pointLineBundle_isInvertible x ε D h a) 𝒱).mp
    (pointLineBundle_geometricallyAlgEquivZero x ε D h a)


end MazurTransfer.UniversalLineBundleFieldComparison
end


section
/-
Copyright (c) 2026 Vas and contributors. All rights reserved.
Released under Apache-2.0 license as described in the file LICENSE.

Design boundary: classify every invertible sheaf of geometric degree zero on
the original curve by a unique base-field point of its represented Picard
scheme. Named downstream consumer: order-13 arithmetic divisor-class/Jacobian
comparison over F₃ and F₅. Field-spectrum triviality and relative Picard inputs
are reused from official Anthropic FLT at commit
6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0. The base field is arbitrary.
-/

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open AlgebraicGeometry.RelPicard NeronModelInfra GoodReductionJacobian

namespace MazurTransfer.UniversalLineBundleFieldComparison

private noncomputable def rigidifiedAtField {k : Type u} [Field k] {X : Scheme.{u}}
    (x : X ⟶ Spec (CommRingCat.of k))
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) x)
    (M : X.Modules) (hM : Scheme.Modules.IsInvertible M) :
    RigidifiedLineBundle x ε (𝟙 (Spec (CommRingCat.of k))) where
  L := (Scheme.Modules.pullback (pullback.fst x (𝟙 _))).obj M
  isInvertible := hM.pullback _
  rigidified := (hM.pullback (pullback.fst x (𝟙 _))).pullback
    (rigSection x (𝟙 _) ε) |>.nonempty_iso_tensorUnit_of_field k _

private theorem rigidifiedAtField_fibrewiseAlgEquivZero
    {k : Type u} [Field k] {X : Scheme.{u}}
    (x : X ⟶ Spec (CommRingCat.of k))
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) x)
    (M : X.Modules) (hM : Scheme.Modules.IsInvertible M)
    (hzero : GeometricallyAlgEquivZero x M) :
    FibrewiseAlgEquivZero (rigidifiedAtField x ε M hM) := by
  intro K _ _ s
  letI : Algebra k K := (Spec.preimage s).hom.toAlgebra
  have hs : Scheme.TwoAffineOpenCover.specMap k K = s := by
    change Spec.map (CommRingCat.ofHom (Spec.preimage s).hom) = s
    rw [CommRingCat.ofHom_hom, Spec.map_preimage]
  have hz := hzero K
  let q : pullback (pullback.snd x (𝟙 (Spec (CommRingCat.of k)))) s ⟶
      pullback x (Scheme.TwoAffineOpenCover.specMap k K) :=
    pullback.lift (pullback.fst (pullback.snd x (𝟙 _)) s ≫ pullback.fst x (𝟙 _))
      (pullback.snd (pullback.snd x (𝟙 _)) s) (by
        rw [Category.assoc, pullback.condition, Category.comp_id, pullback.condition, hs])
  have hq : q ≫ pullback.snd x (Scheme.TwoAffineOpenCover.specMap k K) =
      fibreAt x (𝟙 _) s := pullback.lift_snd _ _ _
  have hfac : q ≫ pullback.fst x (Scheme.TwoAffineOpenCover.specMap k K) =
      pullback.fst (pullback.snd x (𝟙 _)) s ≫ pullback.fst x (𝟙 _) :=
    pullback.lift_fst _ _ _
  exact (hz.pullback q hq).of_iso
    ((Scheme.Modules.pullbackComp q (pullback.fst x (Scheme.TwoAffineOpenCover.specMap k K))).app M ≪≫
      (Scheme.Modules.pullbackCongr hfac).app M ≪≫
      ((Scheme.Modules.pullbackComp (pullback.fst (pullback.snd x (𝟙 _)) s)
        (pullback.fst x (𝟙 _))).app M).symm)

/-- Every invertible geometric degree-zero sheaf is represented by one unique
point over the base field, including when that field is finite. -/
theorem existsUnique_pointLineBundle_iso
    {k : Type u} [Field k] {X : Scheme.{u}}
    (x : X ⟶ Spec (CommRingCat.of k))
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) x)
    (D : RelativePic0Designation k x)
    (h : RepresentsRelSubPic x ε (algEquivZeroCut x ε) D)
    (M : X.Modules) (hM : Scheme.Modules.IsInvertible M)
    (hzero : GeometricallyAlgEquivZero x M) :
    ∃! a : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) D.toBase,
      Nonempty (pointLineBundle x ε D h a ≅ M) := by
  let N := rigidifiedAtField x ε M hM
  have hN : (algEquivZeroCut x ε).P (𝟙 _) N :=
    rigidifiedAtField_fibrewiseAlgEquivZero x ε M hM hzero
  let a := h.classify (𝟙 _) N hN
  obtain ⟨e⟩ := h.classify_spec (𝟙 _) N hN
  have ha : Nonempty (pointLineBundle x ε D h a ≅ M) :=
    ⟨(Scheme.Modules.pullback (toProdSpec x)).mapIso e ≪≫
      (Scheme.Modules.pullbackComp (toProdSpec x) (pullback.fst x (𝟙 _))).app M ≪≫
      (Scheme.Modules.pullbackCongr (toProdSpec_fst x)).app M ≪≫
      (Scheme.Modules.pullbackId X).app M⟩
  refine ⟨a, ha, ?_⟩
  intro b hb
  exact (pointLineBundle_iso_iff x ε D h b a).mp ⟨hb.some ≪≫ ha.some.symm⟩

/-- The same classification uses an Euler characteristic computed over the
base field, rather than an algebraically closed substitute for that field. -/
theorem existsUnique_pointLineBundle_iso_of_curveEulerChar_eq
    {k : Type u} [Field k] {X : Scheme.{u}}
    (x : X ⟶ Spec (CommRingCat.of k))
    [IsProper x] [SmoothOfRelativeDimension 1 x] [GeometricallyIntegral x]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) x)
    (D : RelativePic0Designation k x)
    (h : RepresentsRelSubPic x ε (algEquivZeroCut x ε) D)
    (M : X.Modules) (hM : Scheme.Modules.IsInvertible M)
    (𝒱 : X.TwoAffineOpenCover)
    (hχ : curveEulerChar x 𝒱 M = curveEulerChar x 𝒱 (𝟙_ X.Modules)) :
    ∃! a : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) D.toBase,
      Nonempty (pointLineBundle x ε D h a ≅ M) :=
  existsUnique_pointLineBundle_iso x ε D h M hM
    ((geometricallyAlgEquivZero_iff_curveEulerChar_eq k x M hM 𝒱).mpr hχ)


end MazurTransfer.UniversalLineBundleFieldComparison
end


/-
Copyright (c) 2026 Vas and contributors. All rights reserved.
Released under Apache-2.0 license as described in the file LICENSE.

Design boundary: on the literal order-13 curve, the represented Picard scheme's
base-field points give actual invertible sheaves with Euler-characteristic degree
zero, and their sheaf isomorphism classes detect equality. Named downstream
consumer: the order-13 arithmetic divisor-class/Jacobian-point comparison over
F₃ and F₅. Actual curve and arithmetic: MazurTheorem WIP at
54d43d8dda8a6fcf069cc02a815f850d762c5c0c. Picard and cohomology inputs:
official Anthropic FLT at 6e837e75355538c7f80bab5b956861e86c4eacc2,
Apache-2.0. This result does not claim the remaining divisor-class bijection.
-/

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open AlgebraicGeometry.RelPicard NeronModelInfra GoodReductionJacobian

theorem solution.{u}
    {K : Type u} [Field K] {X : Scheme.{u}}
    (x : X ⟶ Spec (CommRingCat.of K))
    [IsProper x] [SmoothOfRelativeDimension 1 x] [GeometricallyIntegral x]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) x)
    (D : RelativePic0Designation K x)
    (h : RepresentsRelSubPic x ε (algEquivZeroCut x ε) D) :
      let M := fun a : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) D.toBase =>
        (Scheme.Modules.pullback
          (toProdSpec (x))).obj
          (h.poincare.pullbackAlong a).L
      (∀ a, Scheme.Modules.IsInvertible (M a) ∧
        ∀ 𝒱 : (X).TwoAffineOpenCover,
          (Module.finrank K
            (𝒱.sectionsOf (x) (M a)).H0 : ℤ) -
            Module.finrank K
              (𝒱.sectionsOf (x) (M a)).H1 =
          (Module.finrank K
            (𝒱.sectionsOf (x)
              (𝟙_ (X).Modules)).H0 : ℤ) -
            Module.finrank K
              (𝒱.sectionsOf (x)
                (𝟙_ (X).Modules)).H1) ∧
      (∀ a b, Nonempty (M a ≅ M b) ↔ a = b) ∧
      (∀ (𝒱 : (X).TwoAffineOpenCover)
        (N : (X).Modules),
        Scheme.Modules.IsInvertible N →
        (Module.finrank K
          (𝒱.sectionsOf (x) N).H0 : ℤ) -
          Module.finrank K
            (𝒱.sectionsOf (x) N).H1 =
        (Module.finrank K
          (𝒱.sectionsOf (x)
            (𝟙_ (X).Modules)).H0 : ℤ) -
          Module.finrank K
            (𝒱.sectionsOf (x)
              (𝟙_ (X).Modules)).H1 →
        ∃! a : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) D.toBase,
          Nonempty (M a ≅ N)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro a
    exact ⟨MazurTransfer.UniversalLineBundleFieldComparison.pointLineBundle_isInvertible x ε D h a,
      fun 𝒱 => MazurTransfer.UniversalLineBundleFieldComparison.pointLineBundle_curveEulerChar_eq x ε D h a 𝒱⟩
  · intro a b
    exact MazurTransfer.UniversalLineBundleFieldComparison.pointLineBundle_iso_iff x ε D h a b
  · intro 𝒱 N hN hχ
    exact MazurTransfer.UniversalLineBundleFieldComparison.existsUnique_pointLineBundle_iso_of_curveEulerChar_eq
      x ε D h N hN 𝒱 hχ


#print axioms solution
