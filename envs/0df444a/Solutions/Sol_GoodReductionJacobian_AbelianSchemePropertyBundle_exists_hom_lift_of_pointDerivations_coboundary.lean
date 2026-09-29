-- Prove2me | solution 1 for GoodReductionJacobian.AbelianSchemePropertyBundle.exists_hom_lift_of_pointDerivations_coboundary
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/b79d31cc-6369-537f-a891-0c9aa2c000e5

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverComap
import Definitions.Def_AlgebraicGeometry_OModulePresheafHom
import Definitions.Def_AlgebraicGeometry_SmallExtensionPairTangent
import Definitions.Def_AlgebraicGeometry_SmallExtensionTangentCoords
import Definitions.Def_AlgebraicGeometry_TangentCoordsOfPairAt
import Definitions.Def_Algebra_PointDerivations

import Theorems.Thm_AlgebraicGeometry_SmallExtension_exists_isTangentCoordsOfPairAt_of_pointDerivations
import Theorems.Thm_AlgebraicGeometry_SmallExtension_eq_of_isTangentCoordsOfPairAt_of_isTangentCoordsOfPairAt
import Theorems.Thm_AlgebraicGeometry_SmallExtension_isTangentCoordsOfPairAt_comp_of_flat
import Theorems.Thm_AlgebraicGeometry_SmallExtension_isTangentCoordsOfPairAt_add
import Theorems.Thm_AlgebraicGeometry_SmallExtension_exists_isTangentCoordsOfPairAt
import Theorems.Thm_AlgebraicGeometry_Scheme_OrderedAffineCover_exists_comp_eq_of_forall_idx_agree
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_hom_lift_of_pointDerivations_coboundary

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 8000000
set_option synthInstance.maxHeartbeats 320000

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian IsLocalRing TensorProduct AlgebraicGeometry.SmallExtension AlgebraicGeometry.Scheme.TwoAffineOpenCover"

universe u

noncomputable section

namespace K2Beta

theorem fromSpec_comp_eq {T' : Type u} [CommRing T'] {P : Scheme.{u}} (p : P ⟶ Spec (CommRingCat.of T'))
    {U : P.Opens} (hU : IsAffineOpen U) :
    letI := algebraOfHom p U
    hU.isoSpec.inv ≫ U.ι ≫ p = Spec.map (CommRingCat.ofHom (algebraMap T' Γ(P, U))) := by
  letI := algebraOfHom p U
  show hU.isoSpec.inv ≫ U.ι ≫ p = Spec.map ((Scheme.ΓSpecIso (.of T')).inv ≫ p.appLE ⊤ U le_top)
  rw [Spec.map_comp, IsAffineOpen.isoSpec_inv_ι_assoc,
    ← IsAffineOpen.SpecMap_appLE_fromSpec p (isAffineOpen_top _) hU (le_top : U ≤ p ⁻¹ᵁ ⊤),
    IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv]

theorem specMap_presheafMap_comp_isoSpec_inv {P : Scheme.{u}} {U V : P.Opens} (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (h : V ≤ U) :
    Spec.map (P.presheaf.map (homOfLE h).op) ≫ hU.isoSpec.inv = hV.isoSpec.inv ≫ P.homOfLE h := by
  rw [← cancel_mono U.ι, Category.assoc, Category.assoc, IsAffineOpen.isoSpec_inv_ι, IsAffineOpen.map_fromSpec hU hV,
    Scheme.homOfLE_ι, IsAffineOpen.isoSpec_inv_ι]

theorem specMap_restrictAlgHom_comp_isoSpec_inv {T' : Type u} [CommRing T'] {P : Scheme.{u}} (p : P ⟶ Spec (CommRingCat.of T'))
    {U V : P.Opens} (hU : IsAffineOpen U) (hV : IsAffineOpen V) (h : V ≤ U) :
    letI := algebraOfHom p U; letI := algebraOfHom p V
    Spec.map (CommRingCat.ofHom (restrictAlgHom p h).toRingHom) ≫ hU.isoSpec.inv = hV.isoSpec.inv ≫ P.homOfLE h :=
  specMap_presheafMap_comp_isoSpec_inv hU hV h

theorem flat_sections {T' : Type u} [CommRing T'] {P : Scheme.{u}} (p : P ⟶ Spec (CommRingCat.of T')) [Flat p]
    {U : P.Opens} (hU : IsAffineOpen U) :
    letI := algebraOfHom p U
    Module.Flat T' Γ(P, U) := by
  have h1 : (p.appLE ⊤ U le_top).hom.Flat := Flat.flat_appLE p (isAffineOpen_top _) hU le_top
  have h0 : (Scheme.ΓSpecIso (.of T')).inv.hom.Flat :=
    RingHom.Flat.of_bijective (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of T')).inv)
  have h2 : ((Scheme.ΓSpecIso (.of T')).inv ≫ p.appLE ⊤ U le_top).hom.Flat := by
    rw [CommRingCat.hom_comp]
    exact @RingHom.Flat.comp _ _ _ _ _ _ _ _ h0 h1
  exact h2

theorem specMap_algHom_comp_specMap_algebraMap {T' : Type u} [CommRing T'] {C C' : Type u} [CommRing C] [CommRing C']
    [Algebra T' C] [Algebra T' C'] (h : C →ₐ[T'] C') :
    Spec.map (CommRingCat.ofHom h.toRingHom) ≫ Spec.map (CommRingCat.ofHom (algebraMap T' C)) =
      Spec.map (CommRingCat.ofHom (algebraMap T' C')) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  ext x
  simp

theorem specMap_mk_comp_specMap_algHom {T' : Type u} [CommRing T'] (I : Ideal T') {C C' : Type u} [CommRing C] [CommRing C']
    [Algebra T' C] [Algebra T' C'] (h : C →ₐ[T'] C') :
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.map (algebraMap T' C')))) ≫ Spec.map (CommRingCat.ofHom h.toRingHom) =
      Spec.map (CommRingCat.ofHom (Ideal.quotientMap (I.map (algebraMap T' C')) h.toRingHom
        (Ideal.map_le_iff_le_comap.mpr fun x hx => by
          simp only [Ideal.mem_comap, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.commutes]
          exact Ideal.mem_map_of_mem _ hx))) ≫
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.map (algebraMap T' C)))) := by
  have key : (Ideal.Quotient.mk (I.map (algebraMap T' C'))).comp h.toRingHom =
      (Ideal.quotientMap (I.map (algebraMap T' C')) h.toRingHom
        (Ideal.map_le_iff_le_comap.mpr fun x hx => by
          simp only [Ideal.mem_comap, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.commutes]
          exact Ideal.mem_map_of_mem _ hx)).comp (Ideal.Quotient.mk (I.map (algebraMap T' C))) := by
    ext x; rfl
  rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, key]

theorem congr_mod_comp {T' : Type u} [CommRing T'] (I : Ideal T') {C C' : Type u} [CommRing C] [CommRing C']
    [Algebra T' C] [Algebra T' C'] (h : C →ₐ[T'] C') {Y : Scheme.{u}} (u v : Spec (CommRingCat.of C) ⟶ Y)
    (huv : Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.map (algebraMap T' C)))) ≫ u =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.map (algebraMap T' C)))) ≫ v) :
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.map (algebraMap T' C')))) ≫ (Spec.map (CommRingCat.ofHom h.toRingHom) ≫ u) =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.map (algebraMap T' C')))) ≫ (Spec.map (CommRingCat.ofHom h.toRingHom) ≫ v) := by
  rw [← Category.assoc, specMap_mk_comp_specMap_algHom I h, Category.assoc, huv, ← Category.assoc, ← Category.assoc,
    specMap_mk_comp_specMap_algHom I h]

theorem SmallExtension.IsTangentOfPair.congr_mod {T' : Type u} [CommRing T'] [IsLocalRing T'] (I : Ideal T')
    (V : Type u) [AddCommGroup V] [Module (ResidueField T') V] [Module (ResidueField T')ᵐᵒᵖ V]
    [IsCentralScalar (ResidueField T') V] [Module T' V] [IsScalarTower T' (ResidueField T') V]
    (ι : V →ₗ[T'] T') (C : Type u) [CommRing C] [Algebra T' C]
    {Y : Scheme.{u}} {u v : Spec (CommRingCat.of C) ⟶ Y} {w : Spec (CommRingCat.of (SmallExtension.thickening T' V C)) ⟶ Y}
    (h : SmallExtension.IsTangentOfPair I V ι C u v w) :
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.map (algebraMap T' C)))) ≫ u =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.map (algebraMap T' C)))) ≫ v := by
  obtain ⟨ϑ, _, φ, hu, hv, _⟩ := h
  rw [← hu, ← hv, ← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
    ← CommRingCat.ofHom_comp]
  congr 3
  ext ⟨x, hx⟩
  exact (SmallExtension.mem_pairRing I C).mp hx

theorem sigma_restrict {T' : Type u} [CommRing T'] [IsLocalRing T'] {P Pk : Scheme.{u}}
    (p : P ⟶ Spec (CommRingCat.of T')) (q : Pk ⟶ Spec (CommRingCat.of (ResidueField T')))
    (bk : Pk ⟶ P) [IsAffineHom bk] (𝒲 : P.OrderedAffineCover)
    (σ : ∀ {n : ℕ} (s : 𝒲.Idx n),
      letI := algebraOfHom p (𝒲.inter s)
      ((ResidueField T') ⊗[T'] Γ(P, 𝒲.inter s)) ≃+* Γ(Pk, (𝒲.comap bk).inter s))
    (hσ₁ : ∀ {n : ℕ} (s : 𝒲.Idx n) (x : Γ(P, 𝒲.inter s)),
      letI := algebraOfHom p (𝒲.inter s)
      σ s ((1 : ResidueField T') ⊗ₜ[T'] x) =
        (Pk.presheaf.map (homOfLE (𝒲.comap_inter_le bk s)).op).hom ((bk.app (𝒲.inter s)).hom x))
    (hσ₂ : ∀ {n : ℕ} (s : 𝒲.Idx n) (a : ResidueField T'),
      letI := algebraOfHom p (𝒲.inter s)
      letI := algebraOfHom q ((𝒲.comap bk).inter s)
      σ s (a ⊗ₜ[T'] (1 : Γ(P, 𝒲.inter s))) = algebraMap (ResidueField T') Γ(Pk, (𝒲.comap bk).inter s) a)
    {n : ℕ} (s : 𝒲.Idx (n + 1)) (j : Fin (n + 2))
    (x : letI := algebraOfHom p (𝒲.inter (𝒲.face s j)); (ResidueField T') ⊗[T'] Γ(P, 𝒲.inter (𝒲.face s j))) :
    letI := algebraOfHom p (𝒲.inter (𝒲.face s j)); letI := algebraOfHom p (𝒲.inter s)
    σ s (Algebra.TensorProduct.map (AlgHom.id (ResidueField T') (ResidueField T'))
        (restrictAlgHom p (𝒲.inter_le_inter_face s j)) x) =
      (Pk.presheaf.map (homOfLE ((𝒲.comap bk).inter_le_inter_face s j)).op).hom (σ (𝒲.face s j) x) := by
  letI := algebraOfHom p (𝒲.inter (𝒲.face s j)); letI := algebraOfHom p (𝒲.inter s)
  letI := algebraOfHom q ((𝒲.comap bk).inter s); letI := algebraOfHom q ((𝒲.comap bk).inter ((𝒲.comap bk).face s j))
  let r : Γ(Pk, (𝒲.comap bk).inter (𝒲.face s j)) →+* Γ(Pk, (𝒲.comap bk).inter s) :=
    (Pk.presheaf.map (homOfLE ((𝒲.comap bk).inter_le_inter_face s j)).op).hom
  show σ s (Algebra.TensorProduct.map (AlgHom.id (ResidueField T') (ResidueField T'))
        (restrictAlgHom p (𝒲.inter_le_inter_face s j)) x) = r (σ (𝒲.face s j) x)
  induction x using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero, map_zero, map_zero]
  | add x y hx hy => rw [map_add, map_add, map_add, map_add, hx, hy]
  | tmul a c =>
    have split1 : a ⊗ₜ[T'] (restrictAlgHom p (𝒲.inter_le_inter_face s j) c) =
        (a ⊗ₜ[T'] (1 : Γ(P, 𝒲.inter s))) * ((1 : ResidueField T') ⊗ₜ[T'] (restrictAlgHom p (𝒲.inter_le_inter_face s j) c)) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    have split2 : a ⊗ₜ[T'] c = (a ⊗ₜ[T'] (1 : Γ(P, 𝒲.inter (𝒲.face s j)))) * ((1 : ResidueField T') ⊗ₜ[T'] c) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, split1, map_mul, hσ₂, hσ₁, split2, map_mul, map_mul, hσ₂, hσ₁]
    congr 1
    · exact ((restrictAlgHom q ((𝒲.comap bk).inter_le_inter_face s j)).commutes a).symm
    · change ((P.presheaf.map (homOfLE (𝒲.inter_le_inter_face s j)).op ≫ bk.app (𝒲.inter s)) ≫
          Pk.presheaf.map (homOfLE (𝒲.comap_inter_le bk s)).op).hom c =
        ((bk.app (𝒲.inter (𝒲.face s j)) ≫ Pk.presheaf.map (homOfLE (𝒲.comap_inter_le bk (𝒲.face s j))).op) ≫
          Pk.presheaf.map (homOfLE ((𝒲.comap bk).inter_le_inter_face s j)).op).hom c
      rw [bk.naturality (homOfLE (𝒲.inter_le_inter_face s j)).op, Category.assoc, Category.assoc, ← Functor.map_comp,
        ← Functor.map_comp]
      rfl

theorem d_zero_apply {R : Type u} [CommRing R] {X : Scheme.{u}} {π : X ⟶ Spec (.of R)} (F : OModulePresheaf π)
    (K : X.OrderedAffineCover) (x : F.cochain K 0) (s : K.Idx 1) :
    F.d K 0 x s = F.res (K.inter_le_inter_face s 0) (x (K.face s 0)) - F.res (K.inter_le_inter_face s 1) (x (K.face s 1)) := by
  rw [OModulePresheaf.d_apply, Fin.sum_univ_two]
  simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_zsmul, neg_one_zsmul, ← sub_eq_add_neg]

theorem key_identity {k : Type u} [Field k] {A W E0 E1 Es F0 F1 Fs : Type u}
    [AddCommGroup W] [Module k W]
    [CommRing E0] [CommRing E1] [CommRing Es] [Module k E0] [Module k E1] [Module k Es]
    [CommRing F0] [CommRing F1] [CommRing Fs]
    (σ0 : E0 ≃+* F0) (σ1 : E1 ≃+* F1) (σs : Es ≃+* Fs)
    (g0 : E0 →ₗ[k] Es) (g1 : E1 →ₗ[k] Es) (r0 : F0 →+* Fs) (r1 : F1 →+* Fs)
    (hg0 : ∀ x, σs (g0 x) = r0 (σ0 x)) (hg1 : ∀ x, σs (g1 x) = r1 (σ1 x))
    (cs : A → (W →ₗ[k] Es)) (D0 : A → (W →ₗ[k] E0)) (D1 : A → (W →ₗ[k] E1))
    (cv : A → W → Fs) (b0 : A → W → F0) (b1 : A → W → F1)
    (hcs : ∀ a ξ, σs (cs a ξ) = cv a ξ) (hD0 : ∀ a ξ, D0 a ξ = -σ0.symm (b0 a ξ)) (hD1 : ∀ a ξ, D1 a ξ = -σ1.symm (b1 a ξ))
    (hb : ∀ a ξ, cv a ξ = r0 (b0 a ξ) - r1 (b1 a ξ)) :
    cs + (fun a => g0 ∘ₗ D0 a) = (fun a => g1 ∘ₗ D1 a) := by
  funext a; apply LinearMap.ext; intro ξ
  rw [Pi.add_apply, LinearMap.add_apply, LinearMap.comp_apply, LinearMap.comp_apply, hD0, hD1]
  apply σs.injective
  rw [map_add, hcs, hg0, hg1]
  simp only [map_neg, RingEquiv.apply_symm_apply]
  rw [hb]
  abel

theorem edge_agree
    {T' : Type u} [CommRing T'] [IsLocalRing T'] [IsArtinianRing T']
    (I : Ideal T') (hI : I ≤ maximalIdeal T') (hsmall : I * maximalIdeal T' = ⊥)
    (V : Type u) [AddCommGroup V] [Module (ResidueField T') V] [Module (ResidueField T')ᵐᵒᵖ V]
    [IsCentralScalar (ResidueField T') V] [Module.Finite (ResidueField T') V]
    [Module T' V] [IsScalarTower T' (ResidueField T') V]
    (ι : V →ₗ[T'] T') (hι : Function.Injective ι) (hιI : LinearMap.range ι = Submodule.restrictScalars T' I)
    (C0 C1 Cs : Type u) [CommRing C0] [CommRing C1] [CommRing Cs] [Algebra T' C0] [Algebra T' C1] [Algebra T' Cs]
    [Module.Flat T' Cs]
    (h0 : C0 →ₐ[T'] Cs) (h1 : C1 →ₐ[T'] Cs)
    {Y : Scheme.{u}} (qY : Y ⟶ Spec (CommRingCat.of T'))
    {Ak : Scheme.{u}} (xk : Ak ⟶ Spec (CommRingCat.of (ResidueField T'))) (Lk : RelativeGroupLaw (ResidueField T') xk)
    (ak : Ak ⟶ Y) (hak : IsPullback ak xk qY (Spec.map (CommRingCat.ofHom (residue T'))))
    (Ue : Ak.Opens) (hUe : IsAffineOpen Ue)
    (e₁ : Spec (CommRingCat.of (ResidueField T')) ⟶ (Ue : Scheme.{u})) (he₁ : e₁ ≫ Ue.ι = (Lk.one (𝟙 _)).1)
    (u0 u1 : Spec (CommRingCat.of Cs) ⟶ Y)
    (hu0 : u0 ≫ qY = Spec.map (CommRingCat.ofHom (algebraMap T' Cs)))
    (hu1 : u1 ≫ qY = Spec.map (CommRingCat.ofHom (algebraMap T' Cs)))
    (ut0 v0 : Spec (CommRingCat.of C0) ⟶ Y) (ut1 v1 : Spec (CommRingCat.of C1) ⟶ Y)
    (hr0 : Spec.map (CommRingCat.ofHom h0.toRingHom) ≫ ut0 = u1)
    (hr1 : Spec.map (CommRingCat.ofHom h1.toRingHom) ≫ ut1 = u0)
    (hv0f : v0 ≫ qY = Spec.map (CommRingCat.ofHom (algebraMap T' C0)))
    (hv1f : v1 ≫ qY = Spec.map (CommRingCat.ofHom (algebraMap T' C1)))
    (hvm0 : Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.map (algebraMap T' C0)))) ≫ ut0 =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.map (algebraMap T' C0)))) ≫ v0)
    (hvm1 : Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.map (algebraMap T' C1)))) ≫ ut1 =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.map (algebraMap T' C1)))) ≫ v1)
    (D0 : Γ(Ak, Ue) → (Module.Dual (ResidueField T') V →ₗ[ResidueField T'] ((ResidueField T') ⊗[T'] C0)))
    (D1 : Γ(Ak, Ue) → (Module.Dual (ResidueField T') V →ₗ[ResidueField T'] ((ResidueField T') ⊗[T'] C1)))
    (hD0 : IsTangentCoordsOfPairAt I V ι C0 ut0 v0 xk Lk ak Ue D0)
    (hD1 : IsTangentCoordsOfPairAt I V ι C1 ut1 v1 xk Lk ak Ue D1)
    (cs : Γ(Ak, Ue) → (Module.Dual (ResidueField T') V →ₗ[ResidueField T'] ((ResidueField T') ⊗[T'] Cs)))
    (hcs : IsTangentCoordsOfPairAt I V ι Cs u0 u1 xk Lk ak Ue cs)
    (key : cs + (fun a => (Algebra.TensorProduct.map (AlgHom.id (ResidueField T') (ResidueField T')) h0).toLinearMap ∘ₗ D0 a) =
      (fun a => (Algebra.TensorProduct.map (AlgHom.id (ResidueField T') (ResidueField T')) h1).toLinearMap ∘ₗ D1 a)) :
    Spec.map (CommRingCat.ofHom h1.toRingHom) ≫ v1 = Spec.map (CommRingCat.ofHom h0.toRingHom) ≫ v0 := by

  have c1 := AlgebraicGeometry.SmallExtension.isTangentCoordsOfPairAt_comp_of_flat I hI hsmall V ι hι hιI
    C1 Cs h1 _ _ xk Lk ak Ue _ hD1
  rw [hr1] at c1

  have c0 := AlgebraicGeometry.SmallExtension.isTangentCoordsOfPairAt_comp_of_flat I hI hsmall V ι hι hιI
    C0 Cs h0 _ _ xk Lk ak Ue _ hD0
  rw [hr0] at c0

  have hm01 : Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.map (algebraMap T' Cs)))) ≫ u0 =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.map (algebraMap T' Cs)))) ≫ u1 := by
    obtain ⟨w₀, -, -, hpair, -, -⟩ := hcs
    exact SmallExtension.IsTangentOfPair.congr_mod I V ι _ hpair
  have hm1v0 := congr_mod_comp I h0 _ _ hvm0
  rw [hr0] at hm1v0
  have hm0v1 := congr_mod_comp I h1 _ _ hvm1
  rw [hr1] at hm0v1
  have hv0f' : (Spec.map (CommRingCat.ofHom h0.toRingHom) ≫ v0) ≫ qY = Spec.map (CommRingCat.ofHom (algebraMap T' Cs)) := by
    rw [Category.assoc, hv0f, specMap_algHom_comp_specMap_algebraMap]
  have hv1f' : (Spec.map (CommRingCat.ofHom h1.toRingHom) ≫ v1) ≫ qY = Spec.map (CommRingCat.ofHom (algebraMap T' Cs)) := by
    rw [Category.assoc, hv1f, specMap_algHom_comp_specMap_algebraMap]

  obtain ⟨c₃, hc₃⟩ := AlgebraicGeometry.SmallExtension.exists_isTangentCoordsOfPairAt I hI hsmall V ι hι hιI
    Cs qY u0 hu0 xk Lk ak hak Ue hUe e₁ he₁ _ hv0f' (hm01.trans hm1v0)

  have hadd := AlgebraicGeometry.SmallExtension.isTangentCoordsOfPairAt_add I hI hsmall V ι hι hιI Cs qY
    _ _ _ hu0 hu1 hv0f' hm01 hm1v0 xk Lk ak hak Ue hUe e₁ he₁ _ _ _ hcs c0 hc₃
  rw [key] at hadd
  subst hadd
  exact AlgebraicGeometry.SmallExtension.eq_of_isTangentCoordsOfPairAt_of_isTangentCoordsOfPairAt I hI hsmall V ι hι hιI
    Cs qY u0 hu0 xk Lk ak hak Ue hUe e₁ he₁ _ _ hv1f' hv0f' hm0v1 (hm01.trans hm1v0) _ c1 hc₃

end K2Beta

theorem solution
    (T' T : Type u) [CommRing T'] [IsLocalRing T'] [IsArtinianRing T'] [IsAlgClosed (ResidueField T')]
    [CommRing T] (π : T' →+* T) (hπ : Function.Surjective π) (hker : IsNilpotent (RingHom.ker π))
    (hsmall : RingHom.ker π * maximalIdeal T' = ⊥)

    {A₀ : Scheme.{u}} (f₀ : A₀ ⟶ Spec (CommRingCat.of T)) (L₀ : RelativeGroupLaw T f₀) (hc₀ : L₀.IsCommutative)
    (h₀ : AbelianSchemePropertyBundle T f₀)
    {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of T')) (hs : Smooth f) (hp : IsProper f)
    (g : A₀ ⟶ A) (hg : IsPullback g f₀ f (Spec.map (CommRingCat.ofHom π)))

    {A₀' : Scheme.{u}} (f₀' : A₀' ⟶ Spec (CommRingCat.of T)) (L₀' : RelativeGroupLaw T f₀') (hc₀' : L₀'.IsCommutative)
    (h₀' : AbelianSchemePropertyBundle T f₀')
    {A' : Scheme.{u}} (f' : A' ⟶ Spec (CommRingCat.of T')) (hs' : Smooth f') (hp' : IsProper f')
    (g' : A₀' ⟶ A') (hg' : IsPullback g' f₀' f' (Spec.map (CommRingCat.ofHom π)))
    (e' : SchemeHomOver (𝟙 (Spec (CommRingCat.of T'))) f')
    (he' : Spec.map (CommRingCat.ofHom π) ≫ e'.1 = (L₀'.one (𝟙 (Spec (CommRingCat.of T)))).1 ≫ g')

    (u₀ : A₀ ⟶ A₀') (hu₀ : u₀ ≫ f₀' = f₀)

    (hI : RingHom.ker π ≤ maximalIdeal T')
    (ρ : T →+* ResidueField T') (hρ : ρ.comp π = residue T')
    (V : Type u) [AddCommGroup V] [Module (ResidueField T') V] [Module.Finite (ResidueField T') V]
    [Module T' V] [IsScalarTower T' (ResidueField T') V]
    [Module (ResidueField T')ᵐᵒᵖ V] [IsCentralScalar (ResidueField T') V]
    (ι : V →ₗ[T'] T') (hι : Function.Injective ι)
    (hιI : LinearMap.range ι = Submodule.restrictScalars T' (RingHom.ker π))

    [IsSeparated f]
    (𝒲 : A.OrderedAffineCover)
    (m : ∀ i : 𝒲.ι, (↑(𝒲.U i) : Scheme.{u}) ⟶ A')
    (hmf : ∀ i, m i ≫ f' = (𝒲.U i).ι ≫ f)
    (hmμ : ∀ i, morphismRestrict g (𝒲.U i) ≫ m i = (g ⁻¹ᵁ (𝒲.U i)).ι ≫ u₀ ≫ g')

    {Ak' : Scheme.{u}} (fk' : Ak' ⟶ Spec (CommRingCat.of (ResidueField T'))) (Lk' : RelativeGroupLaw (ResidueField T') fk')
    (i₀' : Ak' ⟶ A₀') (hi₀' : IsPullback i₀' fk' f₀' (Spec.map (CommRingCat.ofHom ρ)))
    (Ue' : Ak'.Opens) (hUe' : IsAffineOpen Ue')
    (e₁' : Spec (CommRingCat.of (ResidueField T')) ⟶ (Ue' : Scheme.{u})) (he₁' : e₁' ≫ Ue'.ι = (Lk'.one (𝟙 _)).1)

    {Ak : Scheme.{u}} (bk : Ak ⟶ A) [IsAffineHom bk] (yk : Ak ⟶ Spec (CommRingCat.of (ResidueField T')))
    (hbk : IsPullback bk yk f (Spec.map (CommRingCat.ofHom (residue T'))))
    (σ : ∀ {n : ℕ} (s : 𝒲.Idx n),
      letI := algebraOfHom f (𝒲.inter s)
      ((ResidueField T') ⊗[T'] Γ(A, 𝒲.inter s)) ≃+* Γ(Ak, (𝒲.comap bk).inter s))
    (hσ₁ : ∀ {n : ℕ} (s : 𝒲.Idx n) (x : Γ(A, 𝒲.inter s)),
      letI := algebraOfHom f (𝒲.inter s)
      σ s ((1 : ResidueField T') ⊗ₜ[T'] x) =
        (Ak.presheaf.map (homOfLE (𝒲.comap_inter_le bk s)).op).hom ((bk.app (𝒲.inter s)).hom x))
    (hσ₂ : ∀ {n : ℕ} (s : 𝒲.Idx n) (a : ResidueField T'),
      letI := algebraOfHom f (𝒲.inter s)
      letI := algebraOfHom yk ((𝒲.comap bk).inter s)
      σ s (a ⊗ₜ[T'] (1 : Γ(A, 𝒲.inter s))) = algebraMap (ResidueField T') Γ(Ak, (𝒲.comap bk).inter s) a)

    (c : letI := algebraOfHom fk' Ue'
      ↥(Algebra.PointDerivations (ResidueField T') Γ(Ak', Ue')
          ((Ue'.topIso.inv ≫ e₁'.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of (ResidueField T'))).hom).hom)
          (Module.Dual (ResidueField T') V →ₗ[ResidueField T'] (OModulePresheaf.unit yk).cochain (𝒲.comap bk) 1)))
    (hc : letI := algebraOfHom fk' Ue'
      (∀ s : 𝒲.Idx 1,
        letI := algebraOfHom f (𝒲.inter s)
        ∃ cs : Γ(Ak', Ue') → (Module.Dual (ResidueField T') V →ₗ[ResidueField T'] ((ResidueField T') ⊗[T'] Γ(A, 𝒲.inter s))),
          IsTangentCoordsOfPairAt (RingHom.ker π) V ι Γ(A, 𝒲.inter s)
            ((Scheme.OrderedAffineCover.isAffineOpen_inter f 𝒲 s).isoSpec.inv ≫
              A.homOfLE (𝒲.inter_le s 0) ≫ m (s.1 0))
            ((Scheme.OrderedAffineCover.isAffineOpen_inter f 𝒲 s).isoSpec.inv ≫
              A.homOfLE (𝒲.inter_le s 1) ≫ m (s.1 1))
            fk' Lk' (i₀' ≫ g') Ue' cs ∧
          ∀ (a : Γ(Ak', Ue')) (ξ : Module.Dual (ResidueField T') V), σ s (cs a ξ) = c.1 a ξ s))
    (b : letI := algebraOfHom fk' Ue'
      ↥(Algebra.PointDerivations (ResidueField T') Γ(Ak', Ue')
          ((Ue'.topIso.inv ≫ e₁'.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of (ResidueField T'))).hom).hom)
          (Module.Dual (ResidueField T') V →ₗ[ResidueField T'] (OModulePresheaf.unit yk).cochain (𝒲.comap bk) 0)))
    (hb : letI := algebraOfHom fk' Ue'
      ∀ (a : Γ(Ak', Ue')) (ξ : Module.Dual (ResidueField T') V),
        (OModulePresheaf.unit yk).d (𝒲.comap bk) 0 (b.1 a ξ) = c.1 a ξ) :
    ∃ u : A ⟶ A', u ≫ f' = f ∧ g ≫ u = u₀ ≫ g' := by
  classical
  haveI hflat : Flat f := by haveI := hs; infer_instance
  have hW : ∀ {n : ℕ} (s : 𝒲.Idx n), IsAffineOpen (𝒲.inter s) := fun s =>
    Scheme.OrderedAffineCover.isAffineOpen_inter f 𝒲 s

  have hak : IsPullback (i₀' ≫ g') fk' f' (Spec.map (CommRingCat.ofHom (residue T'))) := by
    have := IsPullback.paste_horiz hi₀' hg'
    rwa [← Spec.map_comp, ← CommRingCat.ofHom_comp, hρ] at this

  have hu : ∀ {n : ℕ} (s : 𝒲.Idx n) (i : 𝒲.ι) (hle : 𝒲.inter s ≤ 𝒲.U i), letI := algebraOfHom f (𝒲.inter s)
      ((hW s).isoSpec.inv ≫ A.homOfLE hle ≫ m i) ≫ f' =
        Spec.map (CommRingCat.ofHom (algebraMap T' Γ(A, 𝒲.inter s))) := by
    intro n s i hle
    rw [Category.assoc, Category.assoc, hmf, ← Category.assoc (A.homOfLE _), Scheme.homOfLE_ι]
    exact K2Beta.fromSpec_comp_eq f (hW s)

  have hres : ∀ {n n' : ℕ} (s : 𝒲.Idx n) (s' : 𝒲.Idx n') (hss : 𝒲.inter s' ≤ 𝒲.inter s) (i : 𝒲.ι)
      (hle : 𝒲.inter s ≤ 𝒲.U i) (hle' : 𝒲.inter s' ≤ 𝒲.U i),
      letI := algebraOfHom f (𝒲.inter s); letI := algebraOfHom f (𝒲.inter s')
      Spec.map (CommRingCat.ofHom (restrictAlgHom f hss).toRingHom) ≫ ((hW s).isoSpec.inv ≫ A.homOfLE hle ≫ m i) =
        (hW s').isoSpec.inv ≫ A.homOfLE hle' ≫ m i := by
    intro n n' s s' hss i hle hle'
    rw [← Category.assoc, K2Beta.specMap_restrictAlgHom_comp_isoSpec_inv f (hW s) (hW s') hss, Category.assoc,
      ← Category.assoc (A.homOfLE hss), Scheme.homOfLE_homOfLE]

  have hσalg : ∀ {n : ℕ} (s : 𝒲.Idx n) (a : (ResidueField T')), letI := algebraOfHom f (𝒲.inter s)
      letI := algebraOfHom yk ((𝒲.comap bk).inter s)
      σ s (algebraMap (ResidueField T') ((ResidueField T') ⊗[T'] Γ(A, 𝒲.inter s)) a) = algebraMap (ResidueField T') Γ(Ak, (𝒲.comap bk).inter s) a := by
    intro n s a
    letI := algebraOfHom f (𝒲.inter s)
    rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
    exact hσ₂ s a
  let ψ : ∀ t : 𝒲.Idx 0, letI := algebraOfHom f (𝒲.inter t)
      ((OModulePresheaf.unit yk).cochain (𝒲.comap bk) 0) →ₗ[(ResidueField T')] ((ResidueField T') ⊗[T'] Γ(A, 𝒲.inter t)) := fun t =>
    letI := algebraOfHom f (𝒲.inter t)
    letI := algebraOfHom yk ((𝒲.comap bk).inter t)
    { toFun := fun x => -(σ t).symm (x t)
      map_add' := fun x y => by
        have h := map_add (σ t).symm (x t) (y t)
        exact (congrArg (fun z => -z) h).trans (neg_add _ _)
      map_smul' := fun a x => by
        change -(σ t).symm (a • (x t : Γ(Ak, (𝒲.comap bk).inter t))) = a • -(σ t).symm (x t)
        rw [smul_neg, neg_inj]
        apply (σ t).injective
        rw [RingEquiv.apply_symm_apply, Algebra.smul_def, map_mul, hσalg, RingEquiv.apply_symm_apply]
        rfl }
  have hψ : ∀ (t : 𝒲.Idx 0) (x : (OModulePresheaf.unit yk).cochain (𝒲.comap bk) 0),
      ψ t x = -(σ t).symm (x t) := fun t x => rfl

  let D : ∀ t : 𝒲.Idx 0, letI := algebraOfHom fk' Ue'; letI := algebraOfHom f (𝒲.inter t)
      ↥(Algebra.PointDerivations (ResidueField T') Γ(Ak', Ue')
          ((Ue'.topIso.inv ≫ e₁'.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of (ResidueField T'))).hom).hom)
          (Module.Dual (ResidueField T') V →ₗ[(ResidueField T')] ((ResidueField T') ⊗[T'] Γ(A, 𝒲.inter t)))) := fun t =>
    letI := algebraOfHom fk' Ue'; letI := algebraOfHom f (𝒲.inter t)
    Algebra.PointDerivations.map _ (LinearMap.llcomp (ResidueField T') (Module.Dual (ResidueField T') V) _ _ (ψ t)) b
  have hD : ∀ (t : 𝒲.Idx 0) (a : Γ(Ak', Ue')) (ξ : Module.Dual (ResidueField T') V), letI := algebraOfHom fk' Ue'; letI := algebraOfHom f (𝒲.inter t)
      (D t : Γ(Ak', Ue') →ₗ[(ResidueField T')] (Module.Dual (ResidueField T') V →ₗ[(ResidueField T')] ((ResidueField T') ⊗[T'] Γ(A, 𝒲.inter t)))) a ξ = -(σ t).symm (b.1 a ξ t) :=
    fun t a ξ => rfl

  have EXP : ∀ t : 𝒲.Idx 0, letI := algebraOfHom fk' Ue'; letI := algebraOfHom f (𝒲.inter t)
      ∃ v : Spec (CommRingCat.of Γ(A, 𝒲.inter t)) ⟶ A',
        v ≫ f' = Spec.map (CommRingCat.ofHom (algebraMap T' Γ(A, 𝒲.inter t))) ∧
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk ((RingHom.ker π).map (algebraMap T' Γ(A, 𝒲.inter t))))) ≫
            ((hW t).isoSpec.inv ≫ A.homOfLE (𝒲.inter_le t 0) ≫ m (t.1 0)) =
          Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk ((RingHom.ker π).map (algebraMap T' Γ(A, 𝒲.inter t))))) ≫ v ∧
        IsTangentCoordsOfPairAt (RingHom.ker π) V ι Γ(A, 𝒲.inter t) ((hW t).isoSpec.inv ≫ A.homOfLE (𝒲.inter_le t 0) ≫ m (t.1 0)) v fk' Lk' (i₀' ≫ g') Ue'
          (fun a => (D t : Γ(Ak', Ue') →ₗ[(ResidueField T')] (Module.Dual (ResidueField T') V →ₗ[(ResidueField T')] ((ResidueField T') ⊗[T'] Γ(A, 𝒲.inter t)))) a) := by
    intro t
    letI := algebraOfHom fk' Ue'; letI := algebraOfHom f (𝒲.inter t)
    haveI : Module.Flat T' Γ(A, 𝒲.inter t) := K2Beta.flat_sections f (hW t)
    exact AlgebraicGeometry.SmallExtension.exists_isTangentCoordsOfPairAt_of_pointDerivations (RingHom.ker π) hI hsmall V ι hι hιI
      Γ(A, 𝒲.inter t) f' _ (hu t (t.1 0) (𝒲.inter_le t 0)) fk' Lk' (i₀' ≫ g') hak Ue' hUe' e₁' he₁' (D t)
  choose v hvf hvm hvc using EXP

  have hagree : ∀ s : 𝒲.Idx 1, letI := algebraOfHom f (𝒲.inter s)
      letI := algebraOfHom f (𝒲.inter (𝒲.face s 0)); letI := algebraOfHom f (𝒲.inter (𝒲.face s 1))
      Spec.map (CommRingCat.ofHom (restrictAlgHom f (𝒲.inter_le_inter_face s 1)).toRingHom) ≫ v (𝒲.face s 1) =
        Spec.map (CommRingCat.ofHom (restrictAlgHom f (𝒲.inter_le_inter_face s 0)).toRingHom) ≫ v (𝒲.face s 0) := by
    intro s
    letI iS := algebraOfHom f (𝒲.inter s)
    letI i0 := algebraOfHom f (𝒲.inter (𝒲.face s 0)); letI i1 := algebraOfHom f (𝒲.inter (𝒲.face s 1))
    letI := algebraOfHom fk' Ue'
    letI := algebraOfHom yk ((𝒲.comap bk).inter s)
    letI := algebraOfHom yk ((𝒲.comap bk).inter (𝒲.face s 0))
    letI := algebraOfHom yk ((𝒲.comap bk).inter (𝒲.face s 1))
    haveI : Module.Flat T' Γ(A, 𝒲.inter s) := K2Beta.flat_sections f (hW s)
    obtain ⟨cs, hcs, hcsσ⟩ := hc s
    exact K2Beta.edge_agree (RingHom.ker π) hI hsmall V ι hι hιI Γ(A, 𝒲.inter (𝒲.face s 0)) Γ(A, 𝒲.inter (𝒲.face s 1)) Γ(A, 𝒲.inter s)
      (restrictAlgHom f (𝒲.inter_le_inter_face s 0)) (restrictAlgHom f (𝒲.inter_le_inter_face s 1))
      f' fk' Lk' (i₀' ≫ g') hak Ue' hUe' e₁' he₁' _ _ (hu s (s.1 0) (𝒲.inter_le s 0)) (hu s (s.1 1) (𝒲.inter_le s 1))
      _ (v (𝒲.face s 0)) _ (v (𝒲.face s 1))
      (hres (𝒲.face s 0) s (𝒲.inter_le_inter_face s 0) (s.1 1) (𝒲.inter_le (𝒲.face s 0) 0) (𝒲.inter_le s 1))
      (hres (𝒲.face s 1) s (𝒲.inter_le_inter_face s 1) (s.1 0) (𝒲.inter_le (𝒲.face s 1) 0) (𝒲.inter_le s 0))
      (hvf (𝒲.face s 0)) (hvf (𝒲.face s 1)) (hvm (𝒲.face s 0)) (hvm (𝒲.face s 1)) _ _ (hvc (𝒲.face s 0)) (hvc (𝒲.face s 1))
      cs hcs
      (K2Beta.key_identity (σ (𝒲.face s 0)) (σ (𝒲.face s 1)) (σ s) _ _
        (Ak.presheaf.map (homOfLE ((𝒲.comap bk).inter_le_inter_face s 0)).op).hom
        (Ak.presheaf.map (homOfLE ((𝒲.comap bk).inter_le_inter_face s 1)).op).hom
        (K2Beta.sigma_restrict f yk bk 𝒲 σ hσ₁ hσ₂ s 0) (K2Beta.sigma_restrict f yk bk 𝒲 σ hσ₁ hσ₂ s 1)
        cs _ _ (fun a ξ => c.1 a ξ s) (fun a ξ => b.1 a ξ (𝒲.face s 0)) (fun a ξ => b.1 a ξ (𝒲.face s 1))
        hcsσ (hD (𝒲.face s 0)) (hD (𝒲.face s 1))
        (fun a ξ => by beta_reduce; rw [← hb a ξ]; exact K2Beta.d_zero_apply _ _ _ _))

  exact AlgebraicGeometry.Scheme.OrderedAffineCover.exists_comp_eq_of_forall_idx_agree π hπ hker f f₀ g hg f' (u₀ ≫ g') 𝒲 m hmμ
    v hvf hvm hagree

end
end S_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_hom_lift_of_pointDerivations_coboundary
end P2MW
export P2MW.S_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_hom_lift_of_pointDerivations_coboundary (solution)
