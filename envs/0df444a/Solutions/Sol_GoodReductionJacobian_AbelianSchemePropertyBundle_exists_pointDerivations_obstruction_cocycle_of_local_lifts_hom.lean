-- Prove2me | solution 1 for GoodReductionJacobian.AbelianSchemePropertyBundle.exists_pointDerivations_obstruction_cocycle_of_local_lifts_hom
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/2c6ba194-3168-5ebd-9954-8f96425e920e

import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverComap
import Definitions.Def_AlgebraicGeometry_OModulePresheafHom
import Definitions.Def_AlgebraicGeometry_SmallExtensionPairTangent
import Definitions.Def_AlgebraicGeometry_SmallExtensionTangentCoords
import Definitions.Def_AlgebraicGeometry_TangentCoordsOfPairAt
import Definitions.Def_Algebra_PointDerivations

import Theorems.Thm_AlgebraicGeometry_IsPullback_exists_iso_Spec_quotient_comp_morphismRestrict_eq
import Theorems.Thm_AlgebraicGeometry_SmallExtension_exists_pointDerivations_isTangentCoordsOfPairAt_of_flat
import Theorems.Thm_AlgebraicGeometry_SmallExtension_isTangentCoordsOfPairAt_comp_of_flat
import Theorems.Thm_AlgebraicGeometry_SmallExtension_isTangentCoordsOfPairAt_add
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_pointDerivations_obstruction_cocycle_of_local_lifts_hom

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option synthInstance.maxHeartbeats 320000

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian P2MW.S_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_pointDerivations_obstruction_cocycle_of_local_lifts_hom.GoodReductionJacobian IsLocalRing TensorProduct AlgebraicGeometry.SmallExtension AlgebraicGeometry.Scheme.TwoAffineOpenCover"

universe u

noncomputable section

namespace GoodReductionJacobian
p2m_export "GoodReductionJacobian" "AbelianSchemePropertyBundle RelativeGroupLaw"
namespace P2mHomObAlpha
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

end GoodReductionJacobian.P2mHomObAlpha

open GoodReductionJacobian.P2mHomObAlpha

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
      σ s (a ⊗ₜ[T'] (1 : Γ(A, 𝒲.inter s))) = algebraMap (ResidueField T') Γ(Ak, (𝒲.comap bk).inter s) a) :
    letI := algebraOfHom fk' Ue'
    ∃ c : ↥(Algebra.PointDerivations (ResidueField T') Γ(Ak', Ue')
          ((Ue'.topIso.inv ≫ e₁'.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of (ResidueField T'))).hom).hom)
          (Module.Dual (ResidueField T') V →ₗ[ResidueField T'] (OModulePresheaf.unit yk).cochain (𝒲.comap bk) 1)),

      (∀ s : 𝒲.Idx 1,
        letI := algebraOfHom f (𝒲.inter s)
        ∃ cs : Γ(Ak', Ue') → (Module.Dual (ResidueField T') V →ₗ[ResidueField T'] ((ResidueField T') ⊗[T'] Γ(A, 𝒲.inter s))),
          IsTangentCoordsOfPairAt (RingHom.ker π) V ι Γ(A, 𝒲.inter s)
            ((Scheme.OrderedAffineCover.isAffineOpen_inter f 𝒲 s).isoSpec.inv ≫
              A.homOfLE (𝒲.inter_le s 0) ≫ m (s.1 0))
            ((Scheme.OrderedAffineCover.isAffineOpen_inter f 𝒲 s).isoSpec.inv ≫
              A.homOfLE (𝒲.inter_le s 1) ≫ m (s.1 1))
            fk' Lk' (i₀' ≫ g') Ue' cs ∧
          ∀ (a : Γ(Ak', Ue')) (ξ : Module.Dual (ResidueField T') V), σ s (cs a ξ) = c.1 a ξ s) ∧

      (∀ (a : Γ(Ak', Ue')) (ξ : Module.Dual (ResidueField T') V),
        (OModulePresheaf.unit yk).d (𝒲.comap bk) 1 (c.1 a ξ) = 0) := by
  classical

  haveI hflat : Flat f := by haveI := hs; infer_instance
  have slot_flat : ∀ {n : ℕ} (s : 𝒲.Idx n),
      letI := algebraOfHom f (𝒲.inter s)
      Module.Flat T' Γ(A, 𝒲.inter s) := fun s => flat_sections f (Scheme.OrderedAffineCover.isAffineOpen_inter f 𝒲 s)
  have slot_over : ∀ {n : ℕ} (s : 𝒲.Idx n) (x : 𝒲.ι) (hx : 𝒲.inter s ≤ 𝒲.U x),
      letI := algebraOfHom f (𝒲.inter s)
      ((Scheme.OrderedAffineCover.isAffineOpen_inter f 𝒲 s).isoSpec.inv ≫ A.homOfLE hx ≫ m x) ≫ f'
        = Spec.map (CommRingCat.ofHom (algebraMap T' Γ(A, 𝒲.inter s))) :=
    fun s x hx => chart_comp_eq f f' 𝒲 m hmf s x hx
  have slot_agree : ∀ {n : ℕ} (s : 𝒲.Idx n) (x y : 𝒲.ι) (hx : 𝒲.inter s ≤ 𝒲.U x) (hy : 𝒲.inter s ≤ 𝒲.U y),
      letI := algebraOfHom f (𝒲.inter s)
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk ((RingHom.ker π).map (algebraMap T' Γ(A, 𝒲.inter s))))) ≫
          ((Scheme.OrderedAffineCover.isAffineOpen_inter f 𝒲 s).isoSpec.inv ≫ A.homOfLE hx ≫ m x)
        = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk ((RingHom.ker π).map (algebraMap T' Γ(A, 𝒲.inter s))))) ≫
          ((Scheme.OrderedAffineCover.isAffineOpen_inter f 𝒲 s).isoSpec.inv ≫ A.homOfLE hy ≫ m y) :=
    fun s x y hx hy => chart_comp_eq_mod (q := f) (𝒲 := 𝒲) (m := m) (π := π) (q₀ := f₀) (G := g) (v := u₀ ≫ g')
      hπ hker hg hmμ s x y hx hy

  have hak : IsPullback (i₀' ≫ g') fk' f' (Spec.map (CommRingCat.ofHom (residue T'))) := by
    have := hi₀'.paste_horiz hg'
    rwa [← Spec.map_comp, ← CommRingCat.ofHom_comp, hρ] at this
  letI instUe := algebraOfHom fk' Ue'

  have hδ : ∀ s : 𝒲.Idx 1,
      letI := algebraOfHom f (𝒲.inter s)
      ∃ δ : ↥(Algebra.PointDerivations (ResidueField T') Γ(Ak', Ue')
          ((Ue'.topIso.inv ≫ e₁'.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of (ResidueField T'))).hom).hom)
          (Module.Dual (ResidueField T') V →ₗ[ResidueField T'] (ResidueField T' ⊗[T'] Γ(A, 𝒲.inter s)))),
        IsTangentCoordsOfPairAt (RingHom.ker π) V ι Γ(A, 𝒲.inter s)
          ((Scheme.OrderedAffineCover.isAffineOpen_inter f 𝒲 s).isoSpec.inv ≫
            A.homOfLE (𝒲.inter_le s 0) ≫ m (s.1 0))
          ((Scheme.OrderedAffineCover.isAffineOpen_inter f 𝒲 s).isoSpec.inv ≫
            A.homOfLE (𝒲.inter_le s 1) ≫ m (s.1 1))
          fk' Lk' (i₀' ≫ g') Ue' (fun a => δ.1 a) := by
    intro s
    letI := algebraOfHom f (𝒲.inter s)
    haveI := slot_flat s
    exact AlgebraicGeometry.SmallExtension.exists_pointDerivations_isTangentCoordsOfPairAt_of_flat
      (RingHom.ker π) hI hsmall V ι hι hιI Γ(A, 𝒲.inter s) f'
      _ (slot_over s (s.1 0) (𝒲.inter_le s 0)) _ (slot_over s (s.1 1) (𝒲.inter_le s 1))
      (slot_agree s (s.1 0) (s.1 1) (𝒲.inter_le s 0) (𝒲.inter_le s 1))
      fk' Lk' (i₀' ≫ g') hak Ue' hUe' e₁' he₁'
  choose δ hδ using hδ

  have σlin : ∀ (n : ℕ) (s : 𝒲.Idx n),
      letI := algebraOfHom f (𝒲.inter s)
      ∃ L : ((ResidueField T') ⊗[T'] Γ(A, 𝒲.inter s)) →ₗ[ResidueField T']
          (OModulePresheaf.unit yk).obj ((𝒲.comap bk).inter s), ∀ x, L x = σ s x := by
    intro n s
    letI := algebraOfHom f (𝒲.inter s)
    letI := algebraOfHom yk ((𝒲.comap bk).inter s)
    refine ⟨{ toFun := fun x => σ s x, map_add' := fun x y => map_add (σ s) x y, map_smul' := fun r x => ?_ }, fun x => rfl⟩
    show σ s (r • x) = r • σ s x
    rw [Algebra.smul_def, Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply, map_mul,
      hσ₂ s r, ← Algebra.smul_def]
  choose σL hσL using σlin

  obtain ⟨c, hc0⟩ := exists_pointDerivations_pi
    ((Ue'.topIso.inv ≫ e₁'.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of (ResidueField T'))).hom).hom)
    (M := fun s : (𝒲.comap bk).Idx 1 => (OModulePresheaf.unit yk).obj ((𝒲.comap bk).inter s))
    (fun s : (𝒲.comap bk).Idx 1 => δ s) (fun s => σL 1 s)
  have hc1 : ∀ a ξ s, c.1 a ξ s = σ s ((δ s).1 a ξ) := fun a ξ s => (hc0 a ξ s).trans (hσL 1 s _)

  have hO1 : (∀ s : 𝒲.Idx 1,
        letI := algebraOfHom f (𝒲.inter s)
        ∃ cs : Γ(Ak', Ue') → (Module.Dual (ResidueField T') V →ₗ[ResidueField T'] ((ResidueField T') ⊗[T'] Γ(A, 𝒲.inter s))),
          IsTangentCoordsOfPairAt (RingHom.ker π) V ι Γ(A, 𝒲.inter s)
            ((Scheme.OrderedAffineCover.isAffineOpen_inter f 𝒲 s).isoSpec.inv ≫
              A.homOfLE (𝒲.inter_le s 0) ≫ m (s.1 0))
            ((Scheme.OrderedAffineCover.isAffineOpen_inter f 𝒲 s).isoSpec.inv ≫
              A.homOfLE (𝒲.inter_le s 1) ≫ m (s.1 1))
            fk' Lk' (i₀' ≫ g') Ue' cs ∧
          ∀ (a : Γ(Ak', Ue')) (ξ : Module.Dual (ResidueField T') V), σ s (cs a ξ) = c.1 a ξ s) := by
    intro s
    exact ⟨fun a => (δ s).1 a, hδ s, fun a ξ => (hc1 a ξ s).symm⟩

  have hO2 : ∀ (a : Γ(Ak', Ue')) (ξ : Module.Dual (ResidueField T') V),
      (OModulePresheaf.unit yk).d (𝒲.comap bk) 1 (c.1 a ξ) = 0 := by
    intro a ξ
    funext t
    rw [OModulePresheaf.d_apply, Pi.zero_apply]
    letI := algebraOfHom f (𝒲.inter t)

    let w : Fin (1 + 2) → (Spec (CommRingCat.of Γ(A, 𝒲.inter t)) ⟶ A') := fun x =>
      (Scheme.OrderedAffineCover.isAffineOpen_inter f 𝒲 t).isoSpec.inv ≫
        A.homOfLE (𝒲.inter_le t x) ≫ m (t.1 x)

    let D : ∀ r : Fin (1 + 2), Γ(Ak', Ue') → (Module.Dual (ResidueField T') V →ₗ[ResidueField T']
        ((ResidueField T') ⊗[T'] Γ(A, 𝒲.inter t))) := fun r a' =>
      letI := algebraOfHom f (𝒲.inter (𝒲.face t r))
      (Algebra.TensorProduct.map (AlgHom.id (ResidueField T') (ResidueField T'))
          (restrictAlgHom f (𝒲.inter_le_inter_face t r))).toLinearMap ∘ₗ (δ (𝒲.face t r)).1 a'
    have hD : ∀ r : Fin (1 + 2), IsTangentCoordsOfPairAt (RingHom.ker π) V ι Γ(A, 𝒲.inter t)
        (w (r.succAbove 0)) (w (r.succAbove 1)) fk' Lk' (i₀' ≫ g') Ue' (D r) := fun r =>
      coords_restrict_face (RingHom.ker π) hI hsmall V ι hι hιI f 𝒲 m fk' Lk' (i₀' ≫ g') Ue' t r (slot_flat t)
        (fun a' => (δ (𝒲.face t r)).1 a') (hδ (𝒲.face t r))
    have hsum : ∑ r : Fin (1 + 2), ((-1 : ℤ) ^ (r : ℕ)) • D r a ξ = 0 :=
      sum_three_coords_eq_zero (RingHom.ker π) hI hsmall V ι hι hιI Γ(A, 𝒲.inter t) f' w
        (fun i => slot_over t (t.1 i) (𝒲.inter_le t i)) (fun i j => slot_agree t (t.1 i) (t.1 j) (𝒲.inter_le t i) (𝒲.inter_le t j))
        fk' Lk' (i₀' ≫ g') hak Ue' hUe' e₁' he₁' D hD a ξ

    have hterm : ∀ r : Fin (1 + 2),
        (OModulePresheaf.unit yk).res ((𝒲.comap bk).inter_le_inter_face t r) (c.1 a ξ ((𝒲.comap bk).face t r))
          = σ t (D r a ξ) := by
      intro r
      show (Ak.presheaf.map (homOfLE ((𝒲.comap bk).inter_le_inter_face t r)).op).hom (c.1 a ξ (𝒲.face t r)) = _
      rw [hc1]
      exact (sigma_restrict f 𝒲 bk σ yk hσ₁ hσ₂ t r _).symm
    calc ∑ r : Fin (1 + 2), ((-1 : ℤ) ^ (r : ℕ)) •
            (OModulePresheaf.unit yk).res ((𝒲.comap bk).inter_le_inter_face t r) (c.1 a ξ ((𝒲.comap bk).face t r))
        = ∑ r : Fin (1 + 2), ((-1 : ℤ) ^ (r : ℕ)) • σ t (D r a ξ) := Finset.sum_congr rfl (fun r _ => by rw [hterm]; rfl)
      _ = σ t (∑ r : Fin (1 + 2), ((-1 : ℤ) ^ (r : ℕ)) • D r a ξ) := by
            rw [map_sum]; refine Finset.sum_congr rfl (fun r _ => ?_); rw [map_zsmul]
      _ = 0 := by rw [hsum, map_zero]
  exact ⟨c, hO1, hO2⟩

end
end S_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_pointDerivations_obstruction_cocycle_of_local_lifts_hom
end P2MW
export P2MW.S_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_pointDerivations_obstruction_cocycle_of_local_lifts_hom (solution)
