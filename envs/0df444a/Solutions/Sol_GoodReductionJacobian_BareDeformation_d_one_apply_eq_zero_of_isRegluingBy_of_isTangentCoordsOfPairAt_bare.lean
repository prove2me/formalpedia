-- Prove2me | solution 1 for GoodReductionJacobian.BareDeformation.d_one_apply_eq_zero_of_isRegluingBy_of_isTangentCoordsOfPairAt_bare
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/190f0c0f-9d7a-5610-950a-47a076e4b471

import Definitions.Def_CerednikDrinfeld_QMFormalModuleOf
import Definitions.Def_GoodReductionJacobian_BareDeformation
import Definitions.Def_GoodReductionJacobian_IsRegluingBy
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverComap
import Definitions.Def_AlgebraicGeometry_OModulePresheafHom
import Definitions.Def_AlgebraicGeometry_SquareZeroDeformation
import Definitions.Def_AlgebraicGeometry_SquareZeroRelTangent
import Definitions.Def_AlgebraicGeometry_SmallExtensionPairTangent
import Definitions.Def_AlgebraicGeometry_TangentCoordsOfPair
import Definitions.Def_AlgebraicGeometry_SmallExtensionTangentCoords
import Definitions.Def_AlgebraicGeometry_TangentCoordsOfPairAt
import Definitions.Def_Algebra_PointDerivations
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw

import Theorems.Thm_AlgebraicGeometry_IsPullback_exists_iso_Spec_quotient_comp_morphismRestrict_eq
import Theorems.Thm_AlgebraicGeometry_SmallExtension_exists_pointDerivations_isTangentCoordsOfPairAt_of_flat
import Theorems.Thm_AlgebraicGeometry_SmallExtension_isTangentCoordsOfPairAt_comp_of_flat
import Theorems.Thm_AlgebraicGeometry_SmallExtension_isTangentCoordsOfPairAt_add
import Theorems.Thm_AlgebraicGeometry_isPushout_specMap_of_isPullback_of_surjective_of_isNilpotent
import Theorems.Thm_AlgebraicGeometry_Scheme_OrderedAffineCover_exists_ringEquiv_tensor_sections_baseChange_inter
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_BareDeformation_d_one_apply_eq_zero_of_isRegluingBy_of_isTangentCoordsOfPairAt_bare

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option synthInstance.maxHeartbeats 320000

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian P2MW.S_GoodReductionJacobian_BareDeformation_d_one_apply_eq_zero_of_isRegluingBy_of_isTangentCoordsOfPairAt_bare.GoodReductionJacobian QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM CerednikDrinfeld.SpecialFormal IsLocalRing AlgebraicGeometry.Scheme.TwoAffineOpenCover TensorProduct AlgebraicGeometry.SmallExtension"

open scoped Quaternion TensorProduct NumberField

universe u

noncomputable section

namespace GoodReductionJacobian
p2m_export "GoodReductionJacobian" "RelativeGroupLaw AbelianSchemePropertyBundle BareDeformation RelativeGroupLaw.baseChange"
namespace P2mRegluedClass
p2m_open "GoodReductionJacobian"

theorem exists_pointDerivations_pi {k : Type*} [Field k] {A : Type*} [CommRing A] [Algebra k A] (ev : A →+* k)
    {W : Type*} [AddCommGroup W] [Module k W] {ι' : Type*} {N : ι' → Type*} {M : ι' → Type*}
    [∀ i, AddCommGroup (N i)] [∀ i, Module k (N i)] [∀ i, AddCommGroup (M i)] [∀ i, Module k (M i)]
    (D : ∀ i, ↥(Algebra.PointDerivations k A ev (W →ₗ[k] N i))) (L : ∀ i, N i →ₗ[k] M i) :
    ∃ B : ↥(Algebra.PointDerivations k A ev (W →ₗ[k] ((i : ι') → M i))),
      ∀ (a : A) (w : W) (i : ι'), B.1 a w i = L i ((D i).1 a w) := by
  let B₀ : A →ₗ[k] (W →ₗ[k] ((i : ι') → M i)) :=
    { toFun := fun a => LinearMap.pi fun i => (L i).comp ((D i).1 a)
      map_add' := fun a a' => by
        apply LinearMap.ext; intro w; funext i
        simp only [LinearMap.pi_apply, LinearMap.comp_apply, map_add, LinearMap.add_apply, Pi.add_apply]
      map_smul' := fun r a => by
        apply LinearMap.ext; intro w; funext i
        simp only [LinearMap.pi_apply, LinearMap.comp_apply, map_smul, LinearMap.smul_apply, Pi.smul_apply,
          RingHom.id_apply] }
  refine ⟨⟨B₀, fun a a' => ?_⟩, fun a w i => rfl⟩
  apply LinearMap.ext; intro w; funext i
  show L i ((D i).1 (a * a') w) = (ev a • B₀ a' + ev a' • B₀ a) w i
  rw [(D i).2 a a']
  simp only [B₀, LinearMap.add_apply, LinearMap.smul_apply, map_add, map_smul, Pi.add_apply, Pi.smul_apply,
    LinearMap.coe_mk, AddHom.coe_mk, LinearMap.pi_apply, LinearMap.comp_apply]

theorem fromSpec_comp_eq {R : Type u} [CommRing R] {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) {U : X.Opens}
    (hU : IsAffineOpen U) :
    letI := algebraOfHom f U
    hU.fromSpec ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R Γ(X, U))) := by
  letI := algebraOfHom f U
  have h := IsAffineOpen.SpecMap_appLE_fromSpec f (isAffineOpen_top (Spec (.of R))) hU
    (show U ≤ f ⁻¹ᵁ ⊤ by simp)
  rw [← h, IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv, ← Spec.map_comp]
  rfl

theorem specMap_isoSpec_inv_homOfLE {X : Scheme.{u}} {U V W : X.Opens} (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (h : V ≤ U) (hUW : U ≤ W) (hVW : V ≤ W) :
    Spec.map (X.presheaf.map (homOfLE h).op) ≫ hU.isoSpec.inv ≫ X.homOfLE hUW = hV.isoSpec.inv ≫ X.homOfLE hVW := by
  rw [← cancel_mono W.ι]
  simp only [Category.assoc, Scheme.homOfLE_ι, IsAffineOpen.isoSpec_inv_ι]
  exact IsAffineOpen.map_fromSpec _ _ _

theorem flat_sections {R : Type u} [CommRing R] {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) [hf : Flat f] {U : X.Opens}
    (hU : IsAffineOpen U) :
    letI := algebraOfHom f U
    Module.Flat R Γ(X, U) := by
  have h := HasRingHomProperty.appLE @Flat f hf ⟨⊤, isAffineOpen_top _⟩ ⟨U, hU⟩ (by simp)
  have h' : RingHom.Flat ((Scheme.ΓSpecIso (.of R)).inv ≫ f.appLE ⊤ U le_top).hom := by
    rw [CommRingCat.hom_comp]
    exact RingHom.Flat.comp (RingHom.Flat.of_bijective (Scheme.ΓSpecIso (.of R)).symm.commRingCatIsoToRingEquiv.bijective) h
  exact h'

section Charts

variable {T' : Type u} [CommRing T'] {X Y : Scheme.{u}} (q : X ⟶ Spec (CommRingCat.of T')) (qY : Y ⟶ Spec (CommRingCat.of T'))
  [IsSeparated q] (𝒲 : X.OrderedAffineCover) (m : ∀ i : 𝒲.ι, (↑(𝒲.U i) : Scheme.{u}) ⟶ Y)

theorem specMap_restrict_isoSpec_inv_homOfLE {n : ℕ} (t : 𝒲.Idx (n + 1)) (j : Fin (n + 2)) (i : Fin (n + 1)) :
    Spec.map (CommRingCat.ofHom
        (letI := algebraOfHom q (𝒲.inter t)
         letI := algebraOfHom q (𝒲.inter (𝒲.face t j))
         (restrictAlgHom q (𝒲.inter_le_inter_face t j)).toRingHom)) ≫
      (Scheme.OrderedAffineCover.isAffineOpen_inter q 𝒲 (𝒲.face t j)).isoSpec.inv ≫
        X.homOfLE (𝒲.inter_le (𝒲.face t j) i)
    = (Scheme.OrderedAffineCover.isAffineOpen_inter q 𝒲 t).isoSpec.inv ≫
        X.homOfLE (𝒲.inter_le t (j.succAbove i)) := by
  exact specMap_isoSpec_inv_homOfLE _ _ (𝒲.inter_le_inter_face t j) _ _

theorem chart_comp_eq (hmf : ∀ i, m i ≫ qY = (𝒲.U i).ι ≫ q) {n : ℕ} (s : 𝒲.Idx n)
    (x : 𝒲.ι) (hx : 𝒲.inter s ≤ 𝒲.U x) :
    letI := algebraOfHom q (𝒲.inter s)
    ((Scheme.OrderedAffineCover.isAffineOpen_inter q 𝒲 s).isoSpec.inv ≫ X.homOfLE hx ≫ m x) ≫ qY
      = Spec.map (CommRingCat.ofHom (algebraMap T' Γ(X, 𝒲.inter s))) := by
  rw [Category.assoc, Category.assoc, hmf, Scheme.homOfLE_ι_assoc,
    ← fromSpec_comp_eq q (Scheme.OrderedAffineCover.isAffineOpen_inter q 𝒲 s), IsAffineOpen.isoSpec_inv_ι_assoc]

variable {T : Type u} [CommRing T] (π : T' →+* T) {X₀ : Scheme.{u}} (q₀ : X₀ ⟶ Spec (CommRingCat.of T)) (G : X₀ ⟶ X)
  (v : X₀ ⟶ Y)

theorem chart_comp_eq_mod (hπ : Function.Surjective π) (hker : IsNilpotent (RingHom.ker π))
    (hG : IsPullback G q₀ q (Spec.map (CommRingCat.ofHom π)))
    (hmμ : ∀ i, (G ∣_ 𝒲.U i) ≫ m i = (G ⁻¹ᵁ 𝒲.U i).ι ≫ v)
    {n : ℕ} (s : 𝒲.Idx n) (x y : 𝒲.ι) (hx : 𝒲.inter s ≤ 𝒲.U x) (hy : 𝒲.inter s ≤ 𝒲.U y) :
    letI := algebraOfHom q (𝒲.inter s)
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk ((RingHom.ker π).map (algebraMap T' Γ(X, 𝒲.inter s))))) ≫
        ((Scheme.OrderedAffineCover.isAffineOpen_inter q 𝒲 s).isoSpec.inv ≫ X.homOfLE hx ≫ m x)
      = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk ((RingHom.ker π).map (algebraMap T' Γ(X, 𝒲.inter s))))) ≫
        ((Scheme.OrderedAffineCover.isAffineOpen_inter q 𝒲 s).isoSpec.inv ≫ X.homOfLE hy ≫ m y) := by
  letI := algebraOfHom q (𝒲.inter s)
  obtain ⟨-, ε, hε⟩ := AlgebraicGeometry.IsPullback.exists_iso_Spec_quotient_comp_morphismRestrict_eq π hπ hker
    q q₀ G hG (𝒲.inter s) (Scheme.OrderedAffineCover.isAffineOpen_inter q 𝒲 s)
  have hε' : Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk ((RingHom.ker π).map (algebraMap T' Γ(X, 𝒲.inter s)))))
      ≫ (Scheme.OrderedAffineCover.isAffineOpen_inter q 𝒲 s).isoSpec.inv = ε.hom ≫ (G ∣_ 𝒲.inter s) := by
    rw [← hε, Category.assoc, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have key : ∀ (x : 𝒲.ι) (hx : 𝒲.inter s ≤ 𝒲.U x), (G ∣_ 𝒲.inter s) ≫ X.homOfLE hx ≫ m x = (G ⁻¹ᵁ 𝒲.inter s).ι ≫ v := by
    intro x hx
    have hres : (G ∣_ 𝒲.inter s) ≫ X.homOfLE hx = X₀.homOfLE (G.preimage_mono hx) ≫ (G ∣_ 𝒲.U x) := by
      rw [← cancel_mono (𝒲.U x).ι, Category.assoc, Scheme.homOfLE_ι, morphismRestrict_ι, Category.assoc,
        morphismRestrict_ι, Scheme.homOfLE_ι_assoc]
    rw [← Category.assoc, hres, Category.assoc, hmμ x, Scheme.homOfLE_ι_assoc]
  have e1 : ∀ (x : 𝒲.ι) (hx : 𝒲.inter s ≤ 𝒲.U x),
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk ((RingHom.ker π).map (algebraMap T' Γ(X, 𝒲.inter s))))) ≫
        ((Scheme.OrderedAffineCover.isAffineOpen_inter q 𝒲 s).isoSpec.inv ≫ X.homOfLE hx ≫ m x)
        = ε.hom ≫ (G ⁻¹ᵁ 𝒲.inter s).ι ≫ v := fun x hx => by
    rw [← Category.assoc, hε', Category.assoc, key x hx]
  exact (e1 x hx).trans (e1 y hy).symm

end Charts

section Sigma

variable {T' : Type u} [CommRing T'] [IsLocalRing T'] {X : Scheme.{u}} (q : X ⟶ Spec (CommRingCat.of T'))
  [IsSeparated q] (𝒲 : X.OrderedAffineCover)
  {Pk : Scheme.{u}} (bk : Pk ⟶ X) [IsAffineHom bk]
  (σ : ∀ {n : ℕ} (s : 𝒲.Idx n),
    letI := algebraOfHom q (𝒲.inter s)
    ((ResidueField T') ⊗[T'] Γ(X, 𝒲.inter s)) ≃+* Γ(Pk, (𝒲.comap bk).inter s))

theorem sigma_restrict (yk : Pk ⟶ Spec (CommRingCat.of (ResidueField T')))
    (hσ₁ : ∀ {n : ℕ} (s : 𝒲.Idx n) (x : Γ(X, 𝒲.inter s)),
      letI := algebraOfHom q (𝒲.inter s)
      σ s ((1 : ResidueField T') ⊗ₜ[T'] x) =
        (Pk.presheaf.map (homOfLE (𝒲.comap_inter_le bk s)).op).hom ((bk.app (𝒲.inter s)).hom x))
    (hσ₂ : ∀ {n : ℕ} (s : 𝒲.Idx n) (a : ResidueField T'),
      letI := algebraOfHom q (𝒲.inter s)
      letI := algebraOfHom yk ((𝒲.comap bk).inter s)
      σ s (a ⊗ₜ[T'] (1 : Γ(X, 𝒲.inter s))) = algebraMap (ResidueField T') Γ(Pk, (𝒲.comap bk).inter s) a)
    {n : ℕ} (t : 𝒲.Idx (n + 1)) (j : Fin (n + 2))
    (x : letI := algebraOfHom q (𝒲.inter (𝒲.face t j))
         (ResidueField T') ⊗[T'] Γ(X, 𝒲.inter (𝒲.face t j))) :
    letI := algebraOfHom q (𝒲.inter t)
    letI := algebraOfHom q (𝒲.inter (𝒲.face t j))
    σ t (Algebra.TensorProduct.map (AlgHom.id (ResidueField T') (ResidueField T'))
          (restrictAlgHom q (𝒲.inter_le_inter_face t j)) x)
      = (Pk.presheaf.map (homOfLE ((𝒲.comap bk).inter_le_inter_face t j :
            (𝒲.comap bk).inter t ≤ (𝒲.comap bk).inter (𝒲.face t j))).op).hom (σ (𝒲.face t j) x) := by
  letI := algebraOfHom q (𝒲.inter t)
  letI := algebraOfHom q (𝒲.inter (𝒲.face t j))
  letI := algebraOfHom yk ((𝒲.comap bk).inter t)
  letI := algebraOfHom yk ((𝒲.comap bk).inter (𝒲.face t j))
  induction x using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero, map_zero]; exact (map_zero _).symm
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add]; exact (map_add _ _ _).symm
  | tmul a c =>
    have hsplit : ∀ (B : Type u) [CommRing B] [Algebra T' B] (a : ResidueField T') (b : B),
        a ⊗ₜ[T'] b = (a ⊗ₜ[T'] (1 : B)) * ((1 : ResidueField T') ⊗ₜ[T'] b) := by
      intro B _ _ a b
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, hsplit, map_mul, hσ₂, hσ₁, hsplit, map_mul, hσ₂, hσ₁]
    refine Eq.trans ?_ (map_mul _ _ _).symm
    congr 1
    · change (yk.appLE ⊤ ((𝒲.comap bk).inter t) le_top).hom _
        = (yk.appLE ⊤ ((𝒲.comap bk).inter (𝒲.face t j)) le_top ≫ Pk.presheaf.map (homOfLE _).op).hom _
      rw [Scheme.Hom.appLE_map]
    · change (bk.app (𝒲.inter t) ≫ Pk.presheaf.map (homOfLE (𝒲.comap_inter_le bk t)).op).hom
          ((X.presheaf.map (homOfLE (𝒲.inter_le_inter_face t j)).op).hom c)
        = (Pk.presheaf.map (homOfLE (𝒲.comap_inter_le bk (𝒲.face t j))).op ≫
            Pk.presheaf.map (homOfLE ((𝒲.comap bk).inter_le_inter_face t j :
              (𝒲.comap bk).inter t ≤ (𝒲.comap bk).inter (𝒲.face t j))).op).hom ((bk.app (𝒲.inter (𝒲.face t j))).hom c)
      change (X.presheaf.map (homOfLE (𝒲.inter_le_inter_face t j)).op ≫ bk.app (𝒲.inter t) ≫
          Pk.presheaf.map (homOfLE (𝒲.comap_inter_le bk t)).op).hom c = _
      rw [← Category.assoc, Scheme.Hom.naturality, Category.assoc, ← Functor.map_comp, ← Functor.map_comp]
      rfl

end Sigma

theorem sum_three_coords_eq_zero
    {T' : Type u} [CommRing T'] [IsLocalRing T'] [IsArtinianRing T']
    (I : Ideal T') (hI : I ≤ maximalIdeal T') (hsmall : I * maximalIdeal T' = ⊥)
    (V : Type u) [AddCommGroup V] [Module (ResidueField T') V] [Module (ResidueField T')ᵐᵒᵖ V]
    [IsCentralScalar (ResidueField T') V] [Module.Finite (ResidueField T') V]
    [Module T' V] [IsScalarTower T' (ResidueField T') V]
    (ι : V →ₗ[T'] T') (hι : Function.Injective ι) (hιI : LinearMap.range ι = Submodule.restrictScalars T' I)
    (C : Type u) [CommRing C] [Algebra T' C] [Module.Flat T' C]
    {Y : Scheme.{u}} (qY : Y ⟶ Spec (CommRingCat.of T'))
    (w : Fin (1 + 2) → (Spec (CommRingCat.of C) ⟶ Y))
    (hw : ∀ i, w i ≫ qY = Spec.map (CommRingCat.ofHom (algebraMap T' C)))
    (hagree : ∀ i j, Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.map (algebraMap T' C)))) ≫ w i
      = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.map (algebraMap T' C)))) ≫ w j)
    {Ak : Scheme.{u}} (xk : Ak ⟶ Spec (CommRingCat.of (ResidueField T'))) (Lk : RelativeGroupLaw (ResidueField T') xk)
    (ak : Ak ⟶ Y) (hak : IsPullback ak xk qY (Spec.map (CommRingCat.ofHom (residue T'))))
    (Ue : Ak.Opens) (hUe : IsAffineOpen Ue)
    (e₁ : Spec (CommRingCat.of (ResidueField T')) ⟶ (Ue : Scheme.{u})) (he₁ : e₁ ≫ Ue.ι = (Lk.one (𝟙 _)).1)
    (D : Fin (1 + 2) → Γ(Ak, Ue) → (Module.Dual (ResidueField T') V →ₗ[ResidueField T'] (ResidueField T' ⊗[T'] C)))
    (hD : ∀ r : Fin (1 + 2), IsTangentCoordsOfPairAt I V ι C (w (r.succAbove 0)) (w (r.succAbove 1)) xk Lk ak Ue (D r))
    (a : Γ(Ak, Ue)) (ξ : Module.Dual (ResidueField T') V) :
    ∑ r : Fin (1 + 2), ((-1 : ℤ) ^ (r : ℕ)) • D r a ξ = 0 := by
  have hD0 : IsTangentCoordsOfPairAt I V ι C (w 1) (w 2) xk Lk ak Ue (D 0) := hD 0
  have hD1 : IsTangentCoordsOfPairAt I V ι C (w 0) (w 2) xk Lk ak Ue (D 1) := hD 1
  have hD2 : IsTangentCoordsOfPairAt I V ι C (w 0) (w 1) xk Lk ak Ue (D 2) := hD 2
  have hadd := AlgebraicGeometry.SmallExtension.isTangentCoordsOfPairAt_add I hI hsmall V ι hι hιI C qY (w 0) (w 1) (w 2)
    (hw 0) (hw 1) (hw 2) (hagree 0 1) (hagree 1 2) xk Lk ak hak Ue hUe e₁ he₁ (D 2) (D 0) (D 1) hD2 hD0 hD1
  have h3 : D 1 a ξ = D 2 a ξ + D 0 a ξ := by rw [hadd]; rfl
  show ∑ r : Fin 3, ((-1 : ℤ) ^ (r : ℕ)) • D r a ξ = 0
  rw [Fin.sum_univ_three]
  simp only [Fin.val_zero, Fin.val_one, Fin.val_two, pow_zero, pow_one, one_zsmul, neg_one_zsmul, h3]
  rw [show ((-1 : ℤ) ^ 2) = 1 by norm_num, one_zsmul]
  abel

theorem coords_restrict_face
    {T' : Type u} [CommRing T'] [IsLocalRing T'] [IsArtinianRing T']
    (I : Ideal T') (hI : I ≤ maximalIdeal T') (hsmall : I * maximalIdeal T' = ⊥)
    (V : Type u) [AddCommGroup V] [Module (ResidueField T') V] [Module (ResidueField T')ᵐᵒᵖ V]
    [IsCentralScalar (ResidueField T') V] [Module.Finite (ResidueField T') V]
    [Module T' V] [IsScalarTower T' (ResidueField T') V]
    (ι : V →ₗ[T'] T') (hι : Function.Injective ι) (hιI : LinearMap.range ι = Submodule.restrictScalars T' I)
    {X Y : Scheme.{u}} (q : X ⟶ Spec (CommRingCat.of T'))
    [IsSeparated q] (𝒲 : X.OrderedAffineCover)
    (m : ∀ i : 𝒲.ι, (↑(𝒲.U i) : Scheme.{u}) ⟶ Y)
    {Ak : Scheme.{u}} (fk : Ak ⟶ Spec (CommRingCat.of (ResidueField T'))) (Lk : RelativeGroupLaw (ResidueField T') fk)
    (ak : Ak ⟶ Y) (Ue : Ak.Opens)
    (t : 𝒲.Idx (1 + 1)) (r : Fin (1 + 2))
    (hflat : letI := algebraOfHom q (𝒲.inter t); Module.Flat T' Γ(X, 𝒲.inter t))
    (δr : letI := algebraOfHom q (𝒲.inter (𝒲.face t r))
      Γ(Ak, Ue) → (Module.Dual (ResidueField T') V →ₗ[ResidueField T'] (ResidueField T' ⊗[T'] Γ(X, 𝒲.inter (𝒲.face t r)))))
    (hδr : letI := algebraOfHom q (𝒲.inter (𝒲.face t r))
      IsTangentCoordsOfPairAt I V ι Γ(X, 𝒲.inter (𝒲.face t r))
        ((Scheme.OrderedAffineCover.isAffineOpen_inter q 𝒲 (𝒲.face t r)).isoSpec.inv ≫
          X.homOfLE (𝒲.inter_le (𝒲.face t r) 0) ≫ m ((𝒲.face t r).1 0))
        ((Scheme.OrderedAffineCover.isAffineOpen_inter q 𝒲 (𝒲.face t r)).isoSpec.inv ≫
          X.homOfLE (𝒲.inter_le (𝒲.face t r) 1) ≫ m ((𝒲.face t r).1 1))
        fk Lk ak Ue δr) :
    letI := algebraOfHom q (𝒲.inter t)
    letI := algebraOfHom q (𝒲.inter (𝒲.face t r))
    IsTangentCoordsOfPairAt I V ι Γ(X, 𝒲.inter t)
      ((Scheme.OrderedAffineCover.isAffineOpen_inter q 𝒲 t).isoSpec.inv ≫
          X.homOfLE (𝒲.inter_le t (r.succAbove 0)) ≫ m (t.1 (r.succAbove 0)))
      ((Scheme.OrderedAffineCover.isAffineOpen_inter q 𝒲 t).isoSpec.inv ≫
          X.homOfLE (𝒲.inter_le t (r.succAbove 1)) ≫ m (t.1 (r.succAbove 1)))
      fk Lk ak Ue
      (fun a => (Algebra.TensorProduct.map (AlgHom.id (ResidueField T') (ResidueField T'))
          (restrictAlgHom q (𝒲.inter_le_inter_face t r))).toLinearMap ∘ₗ δr a) := by
  letI := algebraOfHom q (𝒲.inter t)
  letI := algebraOfHom q (𝒲.inter (𝒲.face t r))
  haveI := hflat
  have h := AlgebraicGeometry.SmallExtension.isTangentCoordsOfPairAt_comp_of_flat I hI hsmall V ι hι hιI
    Γ(X, 𝒲.inter (𝒲.face t r)) Γ(X, 𝒲.inter t)
    (restrictAlgHom q (𝒲.inter_le_inter_face t r)) _ _ fk Lk ak Ue _ hδr
  have hw : ∀ i : Fin (0 + 1 + 1),
      Spec.map (CommRingCat.ofHom (restrictAlgHom q (𝒲.inter_le_inter_face t r)).toRingHom) ≫
        ((Scheme.OrderedAffineCover.isAffineOpen_inter q 𝒲 (𝒲.face t r)).isoSpec.inv ≫
          X.homOfLE (𝒲.inter_le (𝒲.face t r) i) ≫ m ((𝒲.face t r).1 i))
        = (Scheme.OrderedAffineCover.isAffineOpen_inter q 𝒲 t).isoSpec.inv ≫
          X.homOfLE (𝒲.inter_le t (r.succAbove i)) ≫ m (t.1 (r.succAbove i)) := by
    intro i
    rw [← Category.assoc ((Scheme.OrderedAffineCover.isAffineOpen_inter q 𝒲 t).isoSpec.inv),
      ← specMap_restrict_isoSpec_inv_homOfLE q 𝒲 t r i]
    try simp only [Category.assoc]
    rfl
  rw [hw 0, hw 1] at h
  exact h

end GoodReductionJacobian.P2mRegluedClass

open GoodReductionJacobian.P2mRegluedClass

namespace GoodReductionJacobian
p2m_export "GoodReductionJacobian" "RelativeGroupLaw AbelianSchemePropertyBundle BareDeformation RelativeGroupLaw.baseChange"
namespace P2mRegluedClass
p2m_open "GoodReductionJacobian"

theorem isTangentCoordsOfPairAt_reading_change
    {T' : Type u} [CommRing T'] [IsLocalRing T'] (I : Ideal T')
    (V : Type u) [AddCommGroup V] [Module (ResidueField T') V] [Module (ResidueField T')ᵐᵒᵖ V]
    [IsCentralScalar (ResidueField T') V] [Module T' V] [IsScalarTower T' (ResidueField T') V]
    (ι : V →ₗ[T'] T') (C : Type u) [CommRing C] [Algebra T' C]
    (hInil : IsNilpotent (I.map (algebraMap T' C)))
    {U Y Y' : Scheme.{u}} (z : U ⟶ Y) (z' : U ⟶ Y') (u v : Spec (CommRingCat.of C) ⟶ U)
    (huv : Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.map (algebraMap T' C)))) ≫ u
      = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.map (algebraMap T' C)))) ≫ v)
    {Ak : Scheme.{u}} (xk : Ak ⟶ Spec (CommRingCat.of (ResidueField T'))) (Lk : RelativeGroupLaw (ResidueField T') xk)
    (ak : Ak ⟶ Y) (ak' : Ak ⟶ Y') (Ue : Ak.Opens)
    (hz : ∀ {S : Scheme.{u}} (g : S ⟶ U) (gk : S ⟶ Ak), g ≫ z = gk ≫ ak → g ≫ z' = gk ≫ ak')
    (c : Γ(Ak, Ue) → (Module.Dual (ResidueField T') V →ₗ[ResidueField T'] (ResidueField T' ⊗[T'] C)))
    (h : IsTangentCoordsOfPairAt I V ι C (u ≫ z) (v ≫ z) xk Lk ak Ue c) :
    IsTangentCoordsOfPairAt I V ι C (u ≫ z') (v ≫ z') xk Lk ak' Ue c := by
  obtain ⟨w₀, hw₀, w₁, ⟨ϑ, hϑ, φ, hφ1, hφ2, hφ3⟩, hw₁, hc⟩ := h
  have HP : IsPullback (CommRingCat.ofHom (pairFst I C)) (CommRingCat.ofHom (pairSnd I C))
      (CommRingCat.ofHom (Ideal.Quotient.mk (I.map (algebraMap T' C))))
      (CommRingCat.ofHom (Ideal.Quotient.mk (I.map (algebraMap T' C)))) :=
    IsPullback.of_isLimit (CommRingCat.pullbackConeIsLimit
      (CommRingCat.ofHom (Ideal.Quotient.mk (I.map (algebraMap T' C))))
      (CommRingCat.ofHom (Ideal.Quotient.mk (I.map (algebraMap T' C)))))
  have hnil : ∀ x ∈ RingHom.ker (CommRingCat.ofHom (Ideal.Quotient.mk (I.map (algebraMap T' C)))).hom, IsNilpotent x := by
    intro x hx
    rw [CommRingCat.hom_ofHom, Ideal.mk_ker] at hx
    obtain ⟨n, hn⟩ := hInil
    refine ⟨n, ?_⟩
    have hxn : x ^ n ∈ (I.map (algebraMap T' C)) ^ n := Ideal.pow_mem_pow hx n
    rw [hn] at hxn
    simpa using hxn
  have HPO := AlgebraicGeometry.isPushout_specMap_of_isPullback_of_surjective_of_isNilpotent HP
    Ideal.Quotient.mk_surjective hnil
  let φU : Spec (CommRingCat.of ↥(pairRing I C)) ⟶ U := HPO.desc u v huv
  have h1 : Spec.map (CommRingCat.ofHom (pairFst I C)) ≫ φU = u := HPO.inl_desc u v huv
  have h2 : Spec.map (CommRingCat.ofHom (pairSnd I C)) ≫ φU = v := HPO.inr_desc u v huv
  have hφU : φU ≫ z = φ := by
    apply HPO.hom_ext
    · rw [← Category.assoc, h1, hφ1]
    · rw [← Category.assoc, h2, hφ2]
  refine ⟨w₀, hw₀, w₁, ⟨ϑ, hϑ, φU ≫ z', ?_, ?_, ?_⟩, hw₁, hc⟩
  · rw [← Category.assoc, h1]
  · rw [← Category.assoc, h2]
  · have hh : (Spec.map (CommRingCat.ofHom ϑ) ≫ φU) ≫ z = w₀ ≫ ak := by
      rw [Category.assoc, hφU, ← hφ3]
    rw [← Category.assoc]
    exact (hz _ _ hh).symm

theorem sum_three_coords_eq_zero'
    {T' : Type u} [CommRing T'] [IsLocalRing T'] [IsArtinianRing T']
    (I : Ideal T') (hI : I ≤ maximalIdeal T') (hsmall : I * maximalIdeal T' = ⊥)
    (V : Type u) [AddCommGroup V] [Module (ResidueField T') V] [Module (ResidueField T')ᵐᵒᵖ V]
    [IsCentralScalar (ResidueField T') V] [Module.Finite (ResidueField T') V]
    [Module T' V] [IsScalarTower T' (ResidueField T') V]
    (ι : V →ₗ[T'] T') (hι : Function.Injective ι) (hιI : LinearMap.range ι = Submodule.restrictScalars T' I)
    (C : Type u) [CommRing C] [Algebra T' C] [Module.Flat T' C]
    {Y : Scheme.{u}} (qY : Y ⟶ Spec (CommRingCat.of T'))
    (w : Fin (1 + 2) → (Spec (CommRingCat.of C) ⟶ Y))
    (hw : ∀ i, w i ≫ qY = Spec.map (CommRingCat.ofHom (algebraMap T' C)))
    (hagree : ∀ i j, Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.map (algebraMap T' C)))) ≫ w i
      = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.map (algebraMap T' C)))) ≫ w j)
    {Ak : Scheme.{u}} (xk : Ak ⟶ Spec (CommRingCat.of (ResidueField T'))) (Lk : RelativeGroupLaw (ResidueField T') xk)
    (ak : Ak ⟶ Y) (hak : IsPullback ak xk qY (Spec.map (CommRingCat.ofHom (residue T'))))
    (Ue : Ak.Opens) (hUe : IsAffineOpen Ue)
    (e₁ : Spec (CommRingCat.of (ResidueField T')) ⟶ (Ue : Scheme.{u})) (he₁ : e₁ ≫ Ue.ι = (Lk.one (𝟙 _)).1)
    (D : Fin (1 + 2) → Γ(Ak, Ue) → (Module.Dual (ResidueField T') V →ₗ[ResidueField T'] (ResidueField T' ⊗[T'] C)))
    (hD : ∀ r : Fin (1 + 2), IsTangentCoordsOfPairAt I V ι C (w (r.succAbove 1)) (w (r.succAbove 0)) xk Lk ak Ue (D r))
    (a : Γ(Ak, Ue)) (ξ : Module.Dual (ResidueField T') V) :
    ∑ r : Fin (1 + 2), ((-1 : ℤ) ^ (r : ℕ)) • D r a ξ = 0 := by
  have hD0 : IsTangentCoordsOfPairAt I V ι C (w 2) (w 1) xk Lk ak Ue (D 0) := hD 0
  have hD1 : IsTangentCoordsOfPairAt I V ι C (w 2) (w 0) xk Lk ak Ue (D 1) := hD 1
  have hD2 : IsTangentCoordsOfPairAt I V ι C (w 1) (w 0) xk Lk ak Ue (D 2) := hD 2
  have hadd := AlgebraicGeometry.SmallExtension.isTangentCoordsOfPairAt_add I hI hsmall V ι hι hιI C qY (w 2) (w 1) (w 0)
    (hw 2) (hw 1) (hw 0) (hagree 2 1) (hagree 1 0) xk Lk ak hak Ue hUe e₁ he₁ (D 0) (D 2) (D 1) hD0 hD2 hD1
  have h3 : D 1 a ξ = D 0 a ξ + D 2 a ξ := by rw [hadd]; rfl
  show ∑ r : Fin 3, ((-1 : ℤ) ^ (r : ℕ)) • D r a ξ = 0
  rw [Fin.sum_univ_three]
  simp only [Fin.val_zero, Fin.val_one, Fin.val_two, pow_zero, pow_one, one_zsmul, neg_one_zsmul, h3]
  rw [show ((-1 : ℤ) ^ 2) = 1 by norm_num, one_zsmul]
  abel

theorem coords_restrict_face'
    {T' : Type u} [CommRing T'] [IsLocalRing T'] [IsArtinianRing T']
    (I : Ideal T') (hI : I ≤ maximalIdeal T') (hsmall : I * maximalIdeal T' = ⊥)
    (V : Type u) [AddCommGroup V] [Module (ResidueField T') V] [Module (ResidueField T')ᵐᵒᵖ V]
    [IsCentralScalar (ResidueField T') V] [Module.Finite (ResidueField T') V]
    [Module T' V] [IsScalarTower T' (ResidueField T') V]
    (ι : V →ₗ[T'] T') (hι : Function.Injective ι) (hιI : LinearMap.range ι = Submodule.restrictScalars T' I)
    {X Y : Scheme.{u}} (q : X ⟶ Spec (CommRingCat.of T'))
    [IsSeparated q] (𝒲 : X.OrderedAffineCover)
    (m : ∀ i : 𝒲.ι, (↑(𝒲.U i) : Scheme.{u}) ⟶ Y)
    {Ak : Scheme.{u}} (fk : Ak ⟶ Spec (CommRingCat.of (ResidueField T'))) (Lk : RelativeGroupLaw (ResidueField T') fk)
    (ak : Ak ⟶ Y) (Ue : Ak.Opens)
    (t : 𝒲.Idx (1 + 1)) (r : Fin (1 + 2))
    (hflat : letI := algebraOfHom q (𝒲.inter t); Module.Flat T' Γ(X, 𝒲.inter t))
    (δr : letI := algebraOfHom q (𝒲.inter (𝒲.face t r))
      Γ(Ak, Ue) → (Module.Dual (ResidueField T') V →ₗ[ResidueField T'] (ResidueField T' ⊗[T'] Γ(X, 𝒲.inter (𝒲.face t r)))))
    (hδr : letI := algebraOfHom q (𝒲.inter (𝒲.face t r))
      IsTangentCoordsOfPairAt I V ι Γ(X, 𝒲.inter (𝒲.face t r))
        ((Scheme.OrderedAffineCover.isAffineOpen_inter q 𝒲 (𝒲.face t r)).isoSpec.inv ≫
          X.homOfLE (𝒲.inter_le (𝒲.face t r) 1) ≫ m ((𝒲.face t r).1 1))
        ((Scheme.OrderedAffineCover.isAffineOpen_inter q 𝒲 (𝒲.face t r)).isoSpec.inv ≫
          X.homOfLE (𝒲.inter_le (𝒲.face t r) 0) ≫ m ((𝒲.face t r).1 0))
        fk Lk ak Ue δr) :
    letI := algebraOfHom q (𝒲.inter t)
    letI := algebraOfHom q (𝒲.inter (𝒲.face t r))
    IsTangentCoordsOfPairAt I V ι Γ(X, 𝒲.inter t)
      ((Scheme.OrderedAffineCover.isAffineOpen_inter q 𝒲 t).isoSpec.inv ≫
          X.homOfLE (𝒲.inter_le t (r.succAbove 1)) ≫ m (t.1 (r.succAbove 1)))
      ((Scheme.OrderedAffineCover.isAffineOpen_inter q 𝒲 t).isoSpec.inv ≫
          X.homOfLE (𝒲.inter_le t (r.succAbove 0)) ≫ m (t.1 (r.succAbove 0)))
      fk Lk ak Ue
      (fun a => (Algebra.TensorProduct.map (AlgHom.id (ResidueField T') (ResidueField T'))
          (restrictAlgHom q (𝒲.inter_le_inter_face t r))).toLinearMap ∘ₗ δr a) := by
  letI := algebraOfHom q (𝒲.inter t)
  letI := algebraOfHom q (𝒲.inter (𝒲.face t r))
  haveI := hflat
  have h := AlgebraicGeometry.SmallExtension.isTangentCoordsOfPairAt_comp_of_flat I hI hsmall V ι hι hιI
    Γ(X, 𝒲.inter (𝒲.face t r)) Γ(X, 𝒲.inter t)
    (restrictAlgHom q (𝒲.inter_le_inter_face t r)) _ _ fk Lk ak Ue _ hδr
  have hw : ∀ i : Fin (0 + 1 + 1),
      Spec.map (CommRingCat.ofHom (restrictAlgHom q (𝒲.inter_le_inter_face t r)).toRingHom) ≫
        ((Scheme.OrderedAffineCover.isAffineOpen_inter q 𝒲 (𝒲.face t r)).isoSpec.inv ≫
          X.homOfLE (𝒲.inter_le (𝒲.face t r) i) ≫ m ((𝒲.face t r).1 i))
        = (Scheme.OrderedAffineCover.isAffineOpen_inter q 𝒲 t).isoSpec.inv ≫
          X.homOfLE (𝒲.inter_le t (r.succAbove i)) ≫ m (t.1 (r.succAbove i)) := by
    intro i
    rw [← Category.assoc ((Scheme.OrderedAffineCover.isAffineOpen_inter q 𝒲 t).isoSpec.inv),
      ← specMap_restrict_isoSpec_inv_homOfLE q 𝒲 t r i]
    try simp only [Category.assoc]
    rfl
  rw [hw 1, hw 0] at h
  exact h

end GoodReductionJacobian.P2mRegluedClass
theorem solution
    (B B₁ : Type) [CommRing B] [IsLocalRing B] [IsArtinianRing B] [IsAlgClosed (ResidueField B)]
    [CommRing B₁] [Algebra B B₁]
    (hπ : Function.Surjective (algebraMap B B₁)) (hker : IsNilpotent (RingHom.ker (algebraMap B B₁)))
    (hsmall : RingHom.ker (algebraMap B B₁) * maximalIdeal B = ⊥)
    {A₁ : Scheme.{0}} (f₁ : A₁ ⟶ Spec (CommRingCat.of B₁)) (L₁ : RelativeGroupLaw B₁ f₁) (hc₁ : L₁.IsCommutative)
    (h₁ : AbelianSchemePropertyBundle B₁ f₁)
    (hI : RingHom.ker (algebraMap B B₁) ≤ maximalIdeal B)
    (V : Type) [AddCommGroup V] [Module (ResidueField B) V] [Module.Finite (ResidueField B) V]
    [Module B V] [IsScalarTower B (ResidueField B) V]
    [Module (ResidueField B)ᵐᵒᵖ V] [IsCentralScalar (ResidueField B) V]
    (ι : V →ₗ[B] B) (hι : Function.Injective ι)
    (hιI : LinearMap.range ι = Submodule.restrictScalars B (RingHom.ker (algebraMap B B₁)))

    (D₀ : BareDeformation f₁ L₁ B) [IsSeparated D₀.f]
    (𝒰 : D₀.A.OrderedAffineCover) (i₀ : 𝒰.ι) (e₀ : Spec (CommRingCat.of B) ⟶ ↑(𝒰.U i₀)) (he₀ : e₀ ≫ (𝒰.U i₀).ι = (D₀.L.one (𝟙 _)).1)

    (e₁ : Spec (CommRingCat.of (ResidueField B)) ⟶ (((𝒰.baseChange D₀.f (ResidueField B)).U i₀) : Scheme.{0}))
    (he₁ : e₁ ≫ ((𝒰.baseChange D₀.f (ResidueField B)).U i₀).ι = ((RelativeGroupLaw.baseChange (specMap B (ResidueField B)) D₀.L).one (𝟙 _)).1)
    (σ : ∀ s : 𝒰.Idx 1,
      letI := algebraOfHom D₀.f (𝒰.inter s)
      ((ResidueField B) ⊗[B] Γ(D₀.A, 𝒰.inter s)) ≃+* Γ((pullback D₀.f (specMap B (ResidueField B))), (𝒰.baseChange D₀.f (ResidueField B)).inter s))
    (hσ₁ : ∀ (s : 𝒰.Idx 1) (x : Γ(D₀.A, 𝒰.inter s)),
      letI := algebraOfHom D₀.f (𝒰.inter s)
      σ s ((1 : (ResidueField B)) ⊗ₜ[B] x) =
        ((pullback D₀.f (specMap B (ResidueField B))).presheaf.map (homOfLE (𝒰.baseChange_inter_le D₀.f (ResidueField B) s)).op).hom
          (((pullback.fst D₀.f (specMap B (ResidueField B))).app (𝒰.inter s)).hom x))
    (hσ₂ : ∀ (s : 𝒰.Idx 1) (a : (ResidueField B)),
      letI := algebraOfHom D₀.f (𝒰.inter s)
      letI := algebraOfHom (pullback.snd D₀.f (specMap B (ResidueField B))) ((𝒰.baseChange D₀.f (ResidueField B)).inter s)
      σ s (a ⊗ₜ[B] (1 : Γ(D₀.A, 𝒰.inter s))) = algebraMap (ResidueField B) Γ((pullback D₀.f (specMap B (ResidueField B))), (𝒰.baseChange D₀.f (ResidueField B)).inter s) a)
    (τ : ∀ s : 𝒰.Idx 1, ((↑(𝒰.inter s) : Scheme.{0}) ≅ ↑(𝒰.inter s)))
    (D : BareDeformation f₁ L₁ B) (hD : D₀.IsRegluingBy 𝒰 τ D)
    (c : letI := algebraOfHom (pullback.snd D₀.f (specMap B (ResidueField B))) ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)
      ↥(Algebra.PointDerivations (ResidueField B) Γ((pullback D₀.f (specMap B (ResidueField B))), ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)) ((((𝒰.baseChange D₀.f (ResidueField B)).U i₀).topIso.inv ≫ e₁.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of (ResidueField B))).hom).hom) (Module.Dual (ResidueField B) V →ₗ[(ResidueField B)] ((OModulePresheaf.unit (pullback.snd D₀.f (specMap B (ResidueField B)))).cochain (𝒰.baseChange D₀.f (ResidueField B)) 1))))
    (hτ : letI := algebraOfHom (pullback.snd D₀.f (specMap B (ResidueField B))) ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)
      ∀ s : 𝒰.Idx 1,
        letI := algebraOfHom D₀.f (𝒰.inter s)
        ∃ cs : Γ((pullback D₀.f (specMap B (ResidueField B))), ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)) → (Module.Dual (ResidueField B) V →ₗ[(ResidueField B)] ((ResidueField B) ⊗[B] Γ(D₀.A, 𝒰.inter s))),
          AlgebraicGeometry.SmallExtension.IsTangentCoordsOfPairAt (RingHom.ker (algebraMap B B₁)) V ι Γ(D₀.A, 𝒰.inter s)
            ((Scheme.OrderedAffineCover.isAffineOpen_inter D₀.f 𝒰 s).fromSpec)
            ((Scheme.OrderedAffineCover.isAffineOpen_inter D₀.f 𝒰 s).isoSpec.inv ≫ (τ s).hom ≫ (𝒰.inter s).ι)
            (pullback.snd D₀.f (specMap B (ResidueField B))) (RelativeGroupLaw.baseChange (specMap B (ResidueField B)) D₀.L) (pullback.fst D₀.f (specMap B (ResidueField B))) ((𝒰.baseChange D₀.f (ResidueField B)).U i₀) cs ∧
          ∀ (a : Γ((pullback D₀.f (specMap B (ResidueField B))), ((𝒰.baseChange D₀.f (ResidueField B)).U i₀))) (ξ : Module.Dual (ResidueField B) V), σ s (cs a ξ) = c.1 a ξ s) :
    ∀ (a : Γ((pullback D₀.f (specMap B (ResidueField B))), ((𝒰.baseChange D₀.f (ResidueField B)).U i₀))) (ξ : Module.Dual (ResidueField B) V), (OModulePresheaf.unit (pullback.snd D₀.f (specMap B (ResidueField B)))).d (𝒰.baseChange D₀.f (ResidueField B)) 1 (c.1 a ξ) = 0 := by
  classical
  intro a ξ
  obtain ⟨hτf, hτg, ιD, hιopen, hιf, hιsurj, hιg, hιτ⟩ := hD
  haveI : Smooth D₀.f := D₀.bundle.smooth
  haveI hflat : Flat D₀.f := inferInstance
  have haff : ∀ {n : ℕ} (s : 𝒰.Idx n), IsAffineOpen (𝒰.inter s) := fun s => Scheme.OrderedAffineCover.isAffineOpen_inter D₀.f 𝒰 s
  have slot_flat : ∀ {n : ℕ} (s : 𝒰.Idx n), letI := algebraOfHom D₀.f (𝒰.inter s); Module.Flat B Γ(D₀.A, 𝒰.inter s) :=
    fun s => flat_sections D₀.f (haff s)
  letI instUe := algebraOfHom (pullback.snd D₀.f (specMap B (ResidueField B))) ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)
  have hUe : IsAffineOpen ((𝒰.baseChange D₀.f (ResidueField B)).U i₀) := (𝒰.baseChange D₀.f (ResidueField B)).isAffineOpen i₀
  haveI : IsAffineHom (pullback.fst D₀.f (specMap B (ResidueField B))) := MorphismProperty.pullback_fst _ _ inferInstance

  have hK : ∀ b ∈ RingHom.ker (algebraMap B B₁), residue B b = 0 := by
    intro b hb
    rw [IsLocalRing.residue_eq_zero_iff]
    exact hI hb
  let ρ : B₁ →+* ResidueField B :=
    (Ideal.Quotient.lift (RingHom.ker (algebraMap B B₁)) (residue B) hK).comp
      (RingHom.quotientKerEquivOfSurjective hπ).symm.toRingHom
  have hρ : ρ.comp (algebraMap B B₁) = residue B := by
    ext b
    simp only [ρ, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe,
      RingHom.quotientKerEquivOfSurjective_symm_apply, Ideal.Quotient.lift_mk]
  have hspec : specMap B (ResidueField B) = Spec.map (CommRingCat.ofHom (residue B)) := by
    show Spec.map (CommRingCat.ofHom (algebraMap B (ResidueField B))) = _
    rw [IsLocalRing.ResidueField.algebraMap_eq]
  have hSpecρ : Spec.map (CommRingCat.ofHom (residue B))
      = Spec.map (CommRingCat.ofHom ρ) ≫ Spec.map (CommRingCat.ofHom (algebraMap B B₁)) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hρ]
  have hak : IsPullback (pullback.fst D₀.f (specMap B (ResidueField B))) (pullback.snd D₀.f (specMap B (ResidueField B)))
      D₀.f (Spec.map (CommRingCat.ofHom (residue B))) := by
    rw [← hspec]; exact IsPullback.of_hasPullback _ _
  have hw₀ : pullback.fst D₀.f (specMap B (ResidueField B)) ≫ D₀.f
      = (pullback.snd D₀.f (specMap B (ResidueField B)) ≫ Spec.map (CommRingCat.ofHom ρ)) ≫
          Spec.map (CommRingCat.ofHom (algebraMap B B₁)) := by
    rw [Category.assoc, ← hSpecρ]; exact hak.w
  let jA : pullback D₀.f (specMap B (ResidueField B)) ⟶ A₁ := D₀.cart.lift _ _ hw₀
  have hjAg : jA ≫ D₀.g = pullback.fst D₀.f (specMap B (ResidueField B)) := D₀.cart.lift_fst _ _ _
  have hjAf : jA ≫ f₁ = pullback.snd D₀.f (specMap B (ResidueField B)) ≫ Spec.map (CommRingCat.ofHom ρ) := D₀.cart.lift_snd _ _ _
  have hjA : IsPullback jA (pullback.snd D₀.f (specMap B (ResidueField B))) f₁ (Spec.map (CommRingCat.ofHom ρ)) := by
    refine IsPullback.of_right ?_ hjAf D₀.cart
    rw [hjAg, ← hSpecρ]; exact hak
  have hak' : IsPullback (jA ≫ D.g) (pullback.snd D₀.f (specMap B (ResidueField B))) D.f (Spec.map (CommRingCat.ofHom (residue B))) := by
    have h := hjA.paste_horiz D.cart
    rwa [← hSpecρ] at h

  choose cs hcs hcsσ using hτ
  have hpair : ∀ s : 𝒰.Idx 1,
      letI := algebraOfHom D₀.f (𝒰.inter s)
      IsTangentCoordsOfPairAt (RingHom.ker (algebraMap B B₁)) V ι Γ(D₀.A, 𝒰.inter s)
        ((Scheme.OrderedAffineCover.isAffineOpen_inter D₀.f 𝒰 s).isoSpec.inv ≫ D₀.A.homOfLE (𝒰.inter_le s 1) ≫ ιD (s.1 1))
        ((Scheme.OrderedAffineCover.isAffineOpen_inter D₀.f 𝒰 s).isoSpec.inv ≫ D₀.A.homOfLE (𝒰.inter_le s 0) ≫ ιD (s.1 0))
        (pullback.snd D₀.f (specMap B (ResidueField B))) (RelativeGroupLaw.baseChange (specMap B (ResidueField B)) D₀.L)
        (jA ≫ D.g) ((𝒰.baseChange D₀.f (ResidueField B)).U i₀) (cs s) := by
    intro s
    letI := algebraOfHom D₀.f (𝒰.inter s)
    obtain ⟨hIC, ε, hε⟩ := AlgebraicGeometry.IsPullback.exists_iso_Spec_quotient_comp_morphismRestrict_eq (algebraMap B B₁) hπ hker
      D₀.f f₁ D₀.g D₀.cart (𝒰.inter s) (haff s)
    have hε' : Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk ((RingHom.ker (algebraMap B B₁)).map (algebraMap B Γ(D₀.A, 𝒰.inter s)))))
        ≫ (haff s).isoSpec.inv = ε.hom ≫ (D₀.g ∣_ 𝒰.inter s) := by
      rw [← hε, Category.assoc, Category.assoc, Iso.hom_inv_id, Category.comp_id]
    have e_u : ((Scheme.OrderedAffineCover.isAffineOpen_inter D₀.f 𝒰 s).isoSpec.inv ≫ D₀.A.homOfLE (𝒰.inter_le s 1)) ≫ (𝒰.U (s.1 1)).ι
        = (Scheme.OrderedAffineCover.isAffineOpen_inter D₀.f 𝒰 s).fromSpec := by
      rw [Category.assoc, Scheme.homOfLE_ι, IsAffineOpen.isoSpec_inv_ι]
    have e_v : ((Scheme.OrderedAffineCover.isAffineOpen_inter D₀.f 𝒰 s).isoSpec.inv ≫ (τ s).hom ≫ D₀.A.homOfLE (𝒰.inter_le s 1)) ≫ (𝒰.U (s.1 1)).ι
        = (Scheme.OrderedAffineCover.isAffineOpen_inter D₀.f 𝒰 s).isoSpec.inv ≫ (τ s).hom ≫ (𝒰.inter s).ι := by
      simp only [Category.assoc, Scheme.homOfLE_ι]
    have huv' : Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk ((RingHom.ker (algebraMap B B₁)).map (algebraMap B Γ(D₀.A, 𝒰.inter s))))) ≫
          ((Scheme.OrderedAffineCover.isAffineOpen_inter D₀.f 𝒰 s).isoSpec.inv ≫ D₀.A.homOfLE (𝒰.inter_le s 1))
        = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk ((RingHom.ker (algebraMap B B₁)).map (algebraMap B Γ(D₀.A, 𝒰.inter s))))) ≫
          ((Scheme.OrderedAffineCover.isAffineOpen_inter D₀.f 𝒰 s).isoSpec.inv ≫ (τ s).hom ≫ D₀.A.homOfLE (𝒰.inter_le s 1)) := by
      rw [← cancel_mono (𝒰.U (s.1 1)).ι]
      simp only [Category.assoc, Scheme.homOfLE_ι]
      have L : Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk ((RingHom.ker (algebraMap B B₁)).map (algebraMap B Γ(D₀.A, 𝒰.inter s))))) ≫
          (haff s).isoSpec.inv ≫ (𝒰.inter s).ι = ε.hom ≫ (D₀.g ∣_ 𝒰.inter s) ≫ (𝒰.inter s).ι := by
        rw [← Category.assoc, hε', Category.assoc]
      have R : Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk ((RingHom.ker (algebraMap B B₁)).map (algebraMap B Γ(D₀.A, 𝒰.inter s))))) ≫
          (haff s).isoSpec.inv ≫ (τ s).hom ≫ (𝒰.inter s).ι = ε.hom ≫ (D₀.g ∣_ 𝒰.inter s) ≫ (𝒰.inter s).ι := by
        rw [← Category.assoc, hε', Category.assoc, ← Category.assoc (D₀.g ∣_ 𝒰.inter s), hτg s]
      exact L.trans R.symm
    have hz : ∀ {S : Scheme.{0}} (g : S ⟶ ↑(𝒰.U (s.1 1))) (gk : S ⟶ pullback D₀.f (specMap B (ResidueField B))),
        g ≫ (𝒰.U (s.1 1)).ι = gk ≫ pullback.fst D₀.f (specMap B (ResidueField B)) →
        g ≫ ιD (s.1 1) = gk ≫ (jA ≫ D.g) := by
      intro S g gk hg
      have hsub : Set.range (gk ≫ jA) ⊆ Set.range (D₀.g ⁻¹ᵁ 𝒰.U (s.1 1)).ι := by
        rintro _ ⟨x, rfl⟩
        rw [Scheme.Opens.range_ι]
        change ((gk ≫ jA) ≫ D₀.g) x ∈ (𝒰.U (s.1 1) : Set D₀.A)
        rw [Category.assoc, hjAg, ← hg]
        exact (g x).2
      let h := IsOpenImmersion.lift (D₀.g ⁻¹ᵁ 𝒰.U (s.1 1)).ι (gk ≫ jA) hsub
      have hh : h ≫ (D₀.g ⁻¹ᵁ 𝒰.U (s.1 1)).ι = gk ≫ jA := IsOpenImmersion.lift_fac _ _ _
      have hg' : g = h ≫ (D₀.g ∣_ 𝒰.U (s.1 1)) := by
        rw [← cancel_mono (𝒰.U (s.1 1)).ι, Category.assoc, morphismRestrict_ι, ← Category.assoc, hh, Category.assoc, hjAg, hg]
      rw [hg', Category.assoc, hιg, ← Category.assoc, hh, Category.assoc]
    have h0 := hcs s
    rw [← e_u, ← e_v] at h0
    have h1 := isTangentCoordsOfPairAt_reading_change (RingHom.ker (algebraMap B B₁)) V ι Γ(D₀.A, 𝒰.inter s) hIC
      (𝒰.U (s.1 1)).ι (ιD (s.1 1)) _ _ huv'
      (pullback.snd D₀.f (specMap B (ResidueField B))) (RelativeGroupLaw.baseChange (specMap B (ResidueField B)) D₀.L)
      (pullback.fst D₀.f (specMap B (ResidueField B))) (jA ≫ D.g) ((𝒰.baseChange D₀.f (ResidueField B)).U i₀) hz (cs s) h0
    have e_u' : ((Scheme.OrderedAffineCover.isAffineOpen_inter D₀.f 𝒰 s).isoSpec.inv ≫ D₀.A.homOfLE (𝒰.inter_le s 1)) ≫ ιD (s.1 1)
        = (Scheme.OrderedAffineCover.isAffineOpen_inter D₀.f 𝒰 s).isoSpec.inv ≫ D₀.A.homOfLE (𝒰.inter_le s 1) ≫ ιD (s.1 1) :=
      Category.assoc _ _ _
    have e_v' : ((Scheme.OrderedAffineCover.isAffineOpen_inter D₀.f 𝒰 s).isoSpec.inv ≫ (τ s).hom ≫ D₀.A.homOfLE (𝒰.inter_le s 1)) ≫ ιD (s.1 1)
        = (Scheme.OrderedAffineCover.isAffineOpen_inter D₀.f 𝒰 s).isoSpec.inv ≫ D₀.A.homOfLE (𝒰.inter_le s 0) ≫ ιD (s.1 0) := by
      simp only [Category.assoc]
      rw [← hιτ s]
    rw [e_u', e_v'] at h1
    exact h1

  have Hσ : ∀ (n : ℕ) (s : 𝒰.Idx n), _ := fun n s =>
    AlgebraicGeometry.Scheme.OrderedAffineCover.exists_ringEquiv_tensor_sections_baseChange_inter D₀.f 𝒰 (ResidueField B) s
  choose σ' hσ'₁ hσ'₂ using Hσ
  have hσσ' : ∀ (s : 𝒰.Idx 1) (x : letI := algebraOfHom D₀.f (𝒰.inter s); (ResidueField B) ⊗[B] Γ(D₀.A, 𝒰.inter s)),
      σ s x = σ' 1 s x := by
    intro s x
    letI := algebraOfHom D₀.f (𝒰.inter s)
    induction x using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero]
    | tmul a' y =>
      have e : a' ⊗ₜ[B] y = (a' ⊗ₜ[B] (1 : Γ(D₀.A, 𝒰.inter s))) * ((1 : ResidueField B) ⊗ₜ[B] y) := by
        rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
      rw [e, map_mul, map_mul, hσ₁ s y, hσ₂ s a', hσ'₁ 1 s y, hσ'₂ 1 s a']
    | add x y hx hy => rw [map_add, map_add, hx, hy]

  funext t
  rw [OModulePresheaf.d_apply, Pi.zero_apply]
  letI := algebraOfHom D₀.f (𝒰.inter t)
  let w : Fin (1 + 2) → (Spec (CommRingCat.of Γ(D₀.A, 𝒰.inter t)) ⟶ D.A) := fun x =>
    (Scheme.OrderedAffineCover.isAffineOpen_inter D₀.f 𝒰 t).isoSpec.inv ≫ D₀.A.homOfLE (𝒰.inter_le t x) ≫ ιD (t.1 x)
  let Dr : ∀ r : Fin (1 + 2), Γ(pullback D₀.f (specMap B (ResidueField B)), (𝒰.baseChange D₀.f (ResidueField B)).U i₀) →
      (Module.Dual (ResidueField B) V →ₗ[ResidueField B] ((ResidueField B) ⊗[B] Γ(D₀.A, 𝒰.inter t))) := fun r a' =>
    letI := algebraOfHom D₀.f (𝒰.inter (𝒰.face t r))
    (Algebra.TensorProduct.map (AlgHom.id (ResidueField B) (ResidueField B))
        (restrictAlgHom D₀.f (𝒰.inter_le_inter_face t r))).toLinearMap ∘ₗ cs (𝒰.face t r) a'
  have hDr : ∀ r : Fin (1 + 2), IsTangentCoordsOfPairAt (RingHom.ker (algebraMap B B₁)) V ι Γ(D₀.A, 𝒰.inter t)
      (w (r.succAbove 1)) (w (r.succAbove 0))
      (pullback.snd D₀.f (specMap B (ResidueField B))) (RelativeGroupLaw.baseChange (specMap B (ResidueField B)) D₀.L)
      (jA ≫ D.g) ((𝒰.baseChange D₀.f (ResidueField B)).U i₀) (Dr r) := fun r =>
    coords_restrict_face' (RingHom.ker (algebraMap B B₁)) hI hsmall V ι hι hιI D₀.f 𝒰 ιD
      (pullback.snd D₀.f (specMap B (ResidueField B))) (RelativeGroupLaw.baseChange (specMap B (ResidueField B)) D₀.L)
      (jA ≫ D.g) ((𝒰.baseChange D₀.f (ResidueField B)).U i₀) t r (slot_flat t) (cs (𝒰.face t r)) (hpair (𝒰.face t r))
  have hsum : ∑ r : Fin (1 + 2), ((-1 : ℤ) ^ (r : ℕ)) • Dr r a ξ = 0 :=
    sum_three_coords_eq_zero' (RingHom.ker (algebraMap B B₁)) hI hsmall V ι hι hιI Γ(D₀.A, 𝒰.inter t) D.f w
      (fun x => chart_comp_eq D₀.f D.f 𝒰 ιD hιf t (t.1 x) (𝒰.inter_le t x))
      (fun x y => chart_comp_eq_mod (q := D₀.f) (𝒲 := 𝒰) (m := ιD) (π := algebraMap B B₁) (q₀ := f₁) (G := D₀.g) (v := D.g)
        hπ hker D₀.cart hιg t (t.1 x) (t.1 y) (𝒰.inter_le t x) (𝒰.inter_le t y))
      (pullback.snd D₀.f (specMap B (ResidueField B))) (RelativeGroupLaw.baseChange (specMap B (ResidueField B)) D₀.L)
      (jA ≫ D.g) hak' ((𝒰.baseChange D₀.f (ResidueField B)).U i₀) hUe e₁ he₁ Dr hDr a ξ
  have hterm : ∀ r : Fin (1 + 2),
      (OModulePresheaf.unit (pullback.snd D₀.f (specMap B (ResidueField B)))).res
          ((𝒰.baseChange D₀.f (ResidueField B)).inter_le_inter_face t r) (c.1 a ξ ((𝒰.baseChange D₀.f (ResidueField B)).face t r))
        = σ' 2 t (Dr r a ξ) := by
    intro r
    show ((pullback D₀.f (specMap B (ResidueField B))).presheaf.map
        (homOfLE ((𝒰.baseChange D₀.f (ResidueField B)).inter_le_inter_face t r)).op).hom (c.1 a ξ (𝒰.face t r)) = _
    rw [← hcsσ (𝒰.face t r) a ξ, hσσ']
    exact (sigma_restrict D₀.f 𝒰 (pullback.fst D₀.f (specMap B (ResidueField B))) (fun {n} s => σ' n s)
      (pullback.snd D₀.f (specMap B (ResidueField B))) (fun {n} s x => hσ'₁ n s x) (fun {n} s a' => hσ'₂ n s a') t r _).symm
  calc ∑ r : Fin (1 + 2), ((-1 : ℤ) ^ (r : ℕ)) •
          (OModulePresheaf.unit (pullback.snd D₀.f (specMap B (ResidueField B)))).res
            ((𝒰.baseChange D₀.f (ResidueField B)).inter_le_inter_face t r) (c.1 a ξ ((𝒰.baseChange D₀.f (ResidueField B)).face t r))
      = ∑ r : Fin (1 + 2), ((-1 : ℤ) ^ (r : ℕ)) • σ' 2 t (Dr r a ξ) := Finset.sum_congr rfl (fun r _ => by rw [hterm]; rfl)
    _ = σ' 2 t (∑ r : Fin (1 + 2), ((-1 : ℤ) ^ (r : ℕ)) • Dr r a ξ) := by
          rw [map_sum]; refine Finset.sum_congr rfl (fun r _ => ?_); rw [map_zsmul]
    _ = 0 := by rw [hsum, map_zero]

end
end S_GoodReductionJacobian_BareDeformation_d_one_apply_eq_zero_of_isRegluingBy_of_isTangentCoordsOfPairAt_bare
end P2MW
export P2MW.S_GoodReductionJacobian_BareDeformation_d_one_apply_eq_zero_of_isRegluingBy_of_isTangentCoordsOfPairAt_bare (solution)
