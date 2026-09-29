-- Prove2me | solution 1 for GoodReductionJacobian.RelativeGroupLaw.exists_d_comap_slice_eq_of_isTangentCoordsOfPairAt_slice
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/ed9a750d-0618-5601-a4c6-fe6090f44f4e

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
import Theorems.Thm_AlgebraicGeometry_SmallExtension_isTangentCoordsOfPairAt_comp_of_flat
import Theorems.Thm_AlgebraicGeometry_SmallExtension_isTangentCoordsOfPairAt_add
import Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_flat_sections_of_flat
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_d_comap_slice_eq_of_isTangentCoordsOfPairAt_slice

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian IsLocalRing TensorProduct AlgebraicGeometry.SmallExtension AlgebraicGeometry.Scheme.TwoAffineOpenCover"

universe u

noncomputable section

namespace E160A3

p2m_open "AlgebraicGeometry.Scheme.TwoAffineOpenCover TensorProduct"

theorem appLE_congr_hom {X Y : Scheme.{u}} {f g : X ⟶ Y} (hfg : f = g) (U : Y.Opens) (V : X.Opens)
    (h : V ≤ f ⁻¹ᵁ U) (h' : V ≤ g ⁻¹ᵁ U) : f.appLE U V h = g.appLE U V h' := by
  subst hfg; rfl

section Phi

variable {T' : Type u} [CommRing T'] [IsLocalRing T']
  {A Ak : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of T'))
  (fk : Ak ⟶ Spec (CommRingCat.of (ResidueField T'))) (ak : Ak ⟶ A)
  (hak : ak ≫ f = fk ≫ Spec.map (CommRingCat.ofHom (residue T')))

@[reducible] def algT (U' : Ak.Opens) : Algebra T' Γ(Ak, U') :=
  algebraOfHom (fk ≫ Spec.map (CommRingCat.ofHom (residue T'))) U'

theorem ΓSpecIso_inv_residue (r : T') :
    ((Spec.map (CommRingCat.ofHom (residue T'))).appTop).hom ((Scheme.ΓSpecIso (CommRingCat.of T')).inv.hom r) =
      (Scheme.ΓSpecIso (CommRingCat.of (ResidueField T'))).inv.hom (residue T' r) := by
  have h2 := congrArg (fun φ => φ.hom r) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (residue T')))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h2
  exact h2.symm

theorem algebraMap_algT (U' : Ak.Opens) (r : T') :
    letI := algebraOfHom fk U'
    (algT fk U').algebraMap r = algebraMap (ResidueField T') Γ(Ak, U') (residue T' r) := by
  letI := algebraOfHom fk U'
  change ((fk ≫ Spec.map (CommRingCat.ofHom (residue T'))).appLE ⊤ U' le_top).hom
      ((Scheme.ΓSpecIso (CommRingCat.of T')).inv.hom r) =
    (fk.appLE ⊤ U' le_top).hom ((Scheme.ΓSpecIso (CommRingCat.of (ResidueField T'))).inv.hom (residue T' r))
  rw [Scheme.Hom.comp_appLE, ← ΓSpecIso_inv_residue]
  rfl

def phiK (U' : Ak.Opens) :
    letI := algT fk U'
    ResidueField T' →ₐ[T'] Γ(Ak, U') :=
  letI := algT fk U'
  letI iK := algebraOfHom fk U'
  { toRingHom := iK.algebraMap
    commutes' := fun r => by
      change algebraMap (ResidueField T') Γ(Ak, U') (residue T' r) = (algT fk U').algebraMap r
      rw [algebraMap_algT] }

def phiA (W : A.Opens) (U' : Ak.Opens) (h : U' ≤ ak ⁻¹ᵁ W) :
    letI := algebraOfHom f W
    letI := algT fk U'
    Γ(A, W) →ₐ[T'] Γ(Ak, U') :=
  letI := algebraOfHom f W
  letI := algT fk U'
  { toRingHom := (ak.appLE W U' h).hom
    commutes' := fun r => by
      change (ak.appLE W U' h).hom ((f.appLE ⊤ W le_top).hom ((Scheme.ΓSpecIso (CommRingCat.of T')).inv.hom r)) =
        ((fk ≫ Spec.map (CommRingCat.ofHom (residue T'))).appLE ⊤ U' le_top).hom
          ((Scheme.ΓSpecIso (CommRingCat.of T')).inv.hom r)
      change (f.appLE ⊤ W le_top ≫ ak.appLE W U' h).hom _ = _
      rw [Scheme.Hom.appLE_comp_appLE, appLE_congr_hom hak ⊤ U' _ le_top] }

def Phi (W : A.Opens) (U' : Ak.Opens) (h : U' ≤ ak ⁻¹ᵁ W) :
    letI := algebraOfHom f W
    letI := algT fk U'
    ResidueField T' ⊗[T'] Γ(A, W) →ₐ[T'] Γ(Ak, U') :=
  letI := algebraOfHom f W
  letI := algT fk U'
  Algebra.TensorProduct.lift (phiK fk U') (phiA f fk ak hak W U' h) (fun _ _ => Commute.all _ _)

theorem Phi_tmul (W : A.Opens) (U' : Ak.Opens) (h : U' ≤ ak ⁻¹ᵁ W) (a : ResidueField T') (x : Γ(A, W)) :
    letI := algebraOfHom f W
    letI := algebraOfHom fk U'
    Phi f fk ak hak W U' h (a ⊗ₜ[T'] x) = algebraMap (ResidueField T') Γ(Ak, U') a * (ak.appLE W U' h).hom x := by
  letI := algebraOfHom f W
  letI := algT fk U'
  show Algebra.TensorProduct.lift (phiK fk U') (phiA f fk ak hak W U' h) _ (a ⊗ₜ[T'] x) = _
  rw [Algebra.TensorProduct.lift_tmul]
  rfl

theorem res_Phi (W W₂ : A.Opens) (hW : W₂ ≤ W) (U' U₂ : Ak.Opens) (hU : U₂ ≤ U') (h : U' ≤ ak ⁻¹ᵁ W)
    (h₂ : U₂ ≤ ak ⁻¹ᵁ W₂) (y : letI := algebraOfHom f W; ResidueField T' ⊗[T'] Γ(A, W)) :
    letI := algebraOfHom f W
    letI := algebraOfHom f W₂
    (Ak.presheaf.map (homOfLE hU).op).hom (Phi f fk ak hak W U' h y) =
      Phi f fk ak hak W₂ U₂ h₂
        ((Algebra.TensorProduct.map (AlgHom.id (ResidueField T') (ResidueField T'))
          (restrictAlgHom f hW)).toLinearMap y) := by
  letI := algebraOfHom f W
  letI := algebraOfHom f W₂
  induction y using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul a x =>
    rw [AlgHom.toLinearMap_apply, Algebra.TensorProduct.map_tmul, Phi_tmul, Phi_tmul, map_mul]
    congr 1
    · letI := algebraOfHom fk U'; letI := algebraOfHom fk U₂
      change (fk.appLE ⊤ U' le_top ≫ Ak.presheaf.map (homOfLE hU).op).hom _ = (fk.appLE ⊤ U₂ le_top).hom _
      rw [Scheme.Hom.appLE_map]; rfl
    · change (ak.appLE W U' h ≫ Ak.presheaf.map (homOfLE hU).op).hom x =
        (A.presheaf.map (homOfLE hW).op ≫ ak.appLE W₂ U₂ h₂).hom x
      rw [Scheme.Hom.appLE_map, Scheme.Hom.map_appLE]
  | add y z hy hz => simp only [map_add, hy, hz]

end Phi

end E160A3

end

noncomputable section

namespace E160A3

p2m_open "AlgebraicGeometry.Scheme.TwoAffineOpenCover TensorProduct"

section Sigma

variable {T' : Type u} [CommRing T'] [IsLocalRing T']
  {A Ak P Pk : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of T'))
  (fk : Ak ⟶ Spec (CommRingCat.of (ResidueField T'))) (ak : Ak ⟶ A)
  (hak : ak ≫ f = fk ≫ Spec.map (CommRingCat.ofHom (residue T')))
  (qP : P ⟶ Spec (CommRingCat.of T')) (bk : Pk ⟶ P) (yk : Pk ⟶ Spec (CommRingCat.of (ResidueField T')))
  (s : A ⟶ P) (iS : Ak ⟶ Pk)

theorem sigma_push (hiP : iS ≫ bk = ak ≫ s) (hiSy : iS ≫ yk = fk) (W : P.Opens) (Wk : Pk.Opens) (hWk : Wk ≤ bk ⁻¹ᵁ W) (U' : Ak.Opens) (hU' : U' ≤ iS ⁻¹ᵁ Wk)
    (h : U' ≤ ak ⁻¹ᵁ (s ⁻¹ᵁ W))
    (σ : letI := algebraOfHom qP W; ResidueField T' ⊗[T'] Γ(P, W) ≃+* Γ(Pk, Wk))
    (hσ₁ : ∀ x : Γ(P, W), letI := algebraOfHom qP W;
      σ ((1 : ResidueField T') ⊗ₜ[T'] x) = (Pk.presheaf.map (homOfLE hWk).op).hom ((bk.app W).hom x))
    (hσ₂ : ∀ a : ResidueField T', letI := algebraOfHom qP W; letI := algebraOfHom yk Wk;
      σ (a ⊗ₜ[T'] (1 : Γ(P, W))) = algebraMap (ResidueField T') Γ(Pk, Wk) a)
    (hS : letI := algebraOfHom qP W; letI := algebraOfHom f (s ⁻¹ᵁ W); Γ(P, W) →ₐ[T'] Γ(A, s ⁻¹ᵁ W))
    (hhS : ∀ x, hS x = (s.appLE W (s ⁻¹ᵁ W) le_rfl).hom x)
    (z : letI := algebraOfHom qP W; ResidueField T' ⊗[T'] Γ(P, W)) :
    letI := algebraOfHom qP W
    letI := algebraOfHom f (s ⁻¹ᵁ W)
    (Ak.presheaf.map (homOfLE hU').op).hom ((iS.app Wk).hom (σ z)) =
      Phi f fk ak hak (s ⁻¹ᵁ W) U' h
        ((Algebra.TensorProduct.map (AlgHom.id (ResidueField T') (ResidueField T')) hS).toLinearMap z) := by
  letI := algebraOfHom qP W
  letI := algebraOfHom f (s ⁻¹ᵁ W)
  letI := algebraOfHom yk Wk
  letI := algebraOfHom fk U'
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add y z hy hz => simp only [map_add, hy, hz]
  | tmul a x =>
    rw [AlgHom.toLinearMap_apply, Algebra.TensorProduct.map_tmul, Phi_tmul, AlgHom.id_apply, hhS]
    have hax : a ⊗ₜ[T'] x = (a ⊗ₜ[T'] (1 : Γ(P, W))) * ((1 : ResidueField T') ⊗ₜ[T'] x) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    rw [hax, map_mul, hσ₁, hσ₂, map_mul, map_mul]
    congr 1
    ·
      change (yk.appLE ⊤ Wk le_top ≫ iS.app Wk ≫ Ak.presheaf.map (homOfLE hU').op).hom
          ((Scheme.ΓSpecIso (CommRingCat.of (ResidueField T'))).inv.hom a) =
        (fk.appLE ⊤ U' le_top).hom ((Scheme.ΓSpecIso (CommRingCat.of (ResidueField T'))).inv.hom a)
      congr 2
      rw [Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_map, Scheme.Hom.appLE_comp_appLE,
        appLE_congr_hom hiSy ⊤ U' _ le_top]
    ·
      change (bk.app W ≫ Pk.presheaf.map (homOfLE hWk).op ≫ iS.app Wk ≫ Ak.presheaf.map (homOfLE hU').op).hom x =
        (s.appLE W (s ⁻¹ᵁ W) le_rfl ≫ ak.appLE (s ⁻¹ᵁ W) U' h).hom x
      congr 2
      rw [Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_map_assoc, Scheme.Hom.app_eq_appLE,
        Scheme.Hom.appLE_map, Scheme.Hom.appLE_comp_appLE, Scheme.Hom.appLE_comp_appLE,
        appLE_congr_hom hiP W U' _ _]

end Sigma

end E160A3

end

noncomputable section

namespace E160A3

p2m_open "AlgebraicGeometry.Scheme.TwoAffineOpenCover TensorProduct AlgebraicGeometry.SmallExtension"

theorem fromSpec_comp_eq {R : Type u} [CommRing R] {X : Scheme.{u}} (q : X ⟶ Spec (CommRingCat.of R))
    {U : X.Opens} (hU : IsAffineOpen U) :
    letI := algebraOfHom q U
    hU.fromSpec ≫ q = Spec.map (CommRingCat.ofHom (algebraMap R Γ(X, U))) := by
  letI := algebraOfHom q U
  have h1 : CommRingCat.ofHom (algebraMap R Γ(X, U)) = (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ q.appLE ⊤ U le_top := rfl
  rw [h1, Spec.map_comp, ← Scheme.isoSpec_Spec_inv, ← IsAffineOpen.fromSpec_top,
    IsAffineOpen.SpecMap_appLE_fromSpec q (isAffineOpen_top (Spec (CommRingCat.of R))) hU le_top]

section Coords

variable {T' : Type u} [CommRing T'] [IsLocalRing T']
  {A P : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of T')) (qP : P ⟶ Spec (CommRingCat.of T'))
  (s : A ⟶ P) (hsq : s ≫ qP = f)

def sliceAlgHom (W : P.Opens) :
    letI := algebraOfHom qP W
    letI := algebraOfHom f (s ⁻¹ᵁ W)
    Γ(P, W) →ₐ[T'] Γ(A, s ⁻¹ᵁ W) :=
  letI := algebraOfHom qP W
  letI := algebraOfHom f (s ⁻¹ᵁ W)
  { toRingHom := (s.appLE W (s ⁻¹ᵁ W) le_rfl).hom
    commutes' := fun r => by
      change (qP.appLE ⊤ W le_top ≫ s.appLE W (s ⁻¹ᵁ W) le_rfl).hom ((Scheme.ΓSpecIso (CommRingCat.of T')).inv.hom r) =
        (f.appLE ⊤ (s ⁻¹ᵁ W) le_top).hom ((Scheme.ΓSpecIso (CommRingCat.of T')).inv.hom r)
      rw [Scheme.Hom.appLE_comp_appLE, appLE_congr_hom hsq ⊤ (s ⁻¹ᵁ W) _ le_top] }

theorem ofHom_sliceAlgHom (W : P.Opens) :
    letI := algebraOfHom qP W
    letI := algebraOfHom f (s ⁻¹ᵁ W)
    CommRingCat.ofHom (sliceAlgHom f qP s hsq W).toRingHom = s.appLE W (s ⁻¹ᵁ W) le_rfl := rfl

end Coords

section CoordsEq

variable {T' : Type u} [CommRing T'] [IsLocalRing T'] [IsArtinianRing T']
  (I : Ideal T') (hI : I ≤ maximalIdeal T') (hsmall : I * maximalIdeal T' = ⊥)
  (V : Type u) [AddCommGroup V] [Module (ResidueField T') V] [Module (ResidueField T')ᵐᵒᵖ V]
  [IsCentralScalar (ResidueField T') V] [Module.Finite (ResidueField T') V]
  [Module T' V] [IsScalarTower T' (ResidueField T') V]
  (ι : V →ₗ[T'] T') (hι : Function.Injective ι) (hιI : LinearMap.range ι = Submodule.restrictScalars T' I)
  {A Ak P : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of T')) [Flat f] (qP : P ⟶ Spec (CommRingCat.of T'))
  (fk : Ak ⟶ Spec (CommRingCat.of (ResidueField T'))) (Lk : RelativeGroupLaw (ResidueField T') fk)
  (ak : Ak ⟶ A) (hak : IsPullback ak fk f (Spec.map (CommRingCat.ofHom (residue T'))))
  (Ue : Ak.Opens) (hUe : IsAffineOpen Ue)
  (e₁ : Spec (CommRingCat.of (ResidueField T')) ⟶ (Ue : Scheme.{u})) (he₁ : e₁ ≫ Ue.ι = (Lk.one (𝟙 _)).1)
  (s : A ⟶ P) (hsq : s ≫ qP = f)

include hI hsmall hι hιI hak hUe he₁

theorem slice_coords_eq_sub (W₀ W₁ Wt : P.Opens) (hW₀ : Wt ≤ W₀) (hW₁ : Wt ≤ W₁)
    (hWt : IsAffineOpen Wt) (hD₀ : IsAffineOpen (s ⁻¹ᵁ W₀)) (hD₁ : IsAffineOpen (s ⁻¹ᵁ W₁))
    (hDt : IsAffineOpen (s ⁻¹ᵁ Wt))
    (m₀ : (W₀ : Scheme.{u}) ⟶ A) (m₁ : (W₁ : Scheme.{u}) ⟶ A)
    (hm₀ : m₀ ≫ f = W₀.ι ≫ qP) (hm₁ : m₁ ≫ f = W₁.ι ≫ qP)
    (cs : letI := algebraOfHom qP Wt
      Γ(Ak, Ue) → (Module.Dual (ResidueField T') V →ₗ[ResidueField T'] (ResidueField T' ⊗[T'] Γ(P, Wt))))
    (hcs : letI := algebraOfHom qP Wt
      IsTangentCoordsOfPairAt I V ι Γ(P, Wt) (hWt.isoSpec.inv ≫ P.homOfLE hW₀ ≫ m₀)
        (hWt.isoSpec.inv ≫ P.homOfLE hW₁ ≫ m₁) fk Lk ak Ue cs)
    (b₀ : letI := algebraOfHom f (s ⁻¹ᵁ W₀)
      Γ(Ak, Ue) → (Module.Dual (ResidueField T') V →ₗ[ResidueField T'] (ResidueField T' ⊗[T'] Γ(A, s ⁻¹ᵁ W₀))))
    (b₁ : letI := algebraOfHom f (s ⁻¹ᵁ W₁)
      Γ(Ak, Ue) → (Module.Dual (ResidueField T') V →ₗ[ResidueField T'] (ResidueField T' ⊗[T'] Γ(A, s ⁻¹ᵁ W₁))))
    (hbmod₀ : letI := algebraOfHom f (s ⁻¹ᵁ W₀)
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.map (algebraMap T' Γ(A, s ⁻¹ᵁ W₀))))) ≫ hD₀.fromSpec =
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.map (algebraMap T' Γ(A, s ⁻¹ᵁ W₀))))) ≫
          (hD₀.isoSpec.inv ≫ (s ∣_ W₀) ≫ m₀))
    (hbmod₁ : letI := algebraOfHom f (s ⁻¹ᵁ W₁)
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.map (algebraMap T' Γ(A, s ⁻¹ᵁ W₁))))) ≫ hD₁.fromSpec =
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.map (algebraMap T' Γ(A, s ⁻¹ᵁ W₁))))) ≫
          (hD₁.isoSpec.inv ≫ (s ∣_ W₁) ≫ m₁))
    (hb₀ : letI := algebraOfHom f (s ⁻¹ᵁ W₀)
      IsTangentCoordsOfPairAt I V ι Γ(A, s ⁻¹ᵁ W₀) hD₀.fromSpec (hD₀.isoSpec.inv ≫ (s ∣_ W₀) ≫ m₀) fk Lk ak Ue b₀)
    (hb₁ : letI := algebraOfHom f (s ⁻¹ᵁ W₁)
      IsTangentCoordsOfPairAt I V ι Γ(A, s ⁻¹ᵁ W₁) hD₁.fromSpec (hD₁.isoSpec.inv ≫ (s ∣_ W₁) ≫ m₁) fk Lk ak Ue b₁)
    (a : Γ(Ak, Ue)) :
    letI := algebraOfHom qP Wt
    letI := algebraOfHom f (s ⁻¹ᵁ W₀)
    letI := algebraOfHom f (s ⁻¹ᵁ W₁)
    letI := algebraOfHom f (s ⁻¹ᵁ Wt)
    (Algebra.TensorProduct.map (AlgHom.id (ResidueField T') (ResidueField T')) (sliceAlgHom f qP s hsq Wt)).toLinearMap ∘ₗ cs a =
      (Algebra.TensorProduct.map (AlgHom.id (ResidueField T') (ResidueField T'))
          (restrictAlgHom f (show s ⁻¹ᵁ Wt ≤ s ⁻¹ᵁ W₁ from fun x hx => hW₁ hx))).toLinearMap ∘ₗ b₁ a -
      (Algebra.TensorProduct.map (AlgHom.id (ResidueField T') (ResidueField T'))
          (restrictAlgHom f (show s ⁻¹ᵁ Wt ≤ s ⁻¹ᵁ W₀ from fun x hx => hW₀ hx))).toLinearMap ∘ₗ b₀ a := by
  letI := algebraOfHom qP Wt
  letI i₀ := algebraOfHom f (s ⁻¹ᵁ W₀)
  letI i₁ := algebraOfHom f (s ⁻¹ᵁ W₁)
  letI it := algebraOfHom f (s ⁻¹ᵁ Wt)
  haveI : Module.Flat T' Γ(A, s ⁻¹ᵁ Wt) := flat_sections_of_flat f (s ⁻¹ᵁ Wt) hDt
  have le₀ : s ⁻¹ᵁ Wt ≤ s ⁻¹ᵁ W₀ := fun x hx => hW₀ hx
  have le₁ : s ⁻¹ᵁ Wt ≤ s ⁻¹ᵁ W₁ := fun x hx => hW₁ hx

  have R₀ := isTangentCoordsOfPairAt_comp_of_flat I hI hsmall V ι hι hιI Γ(A, s ⁻¹ᵁ W₀) Γ(A, s ⁻¹ᵁ Wt)
    (restrictAlgHom f le₀) _ _ fk Lk ak Ue b₀ hb₀
  have R₁ := isTangentCoordsOfPairAt_comp_of_flat I hI hsmall V ι hι hιI Γ(A, s ⁻¹ᵁ W₁) Γ(A, s ⁻¹ᵁ Wt)
    (restrictAlgHom f le₁) _ _ fk Lk ak Ue b₁ hb₁
  have Rt := isTangentCoordsOfPairAt_comp_of_flat I hI hsmall V ι hι hιI Γ(P, Wt) Γ(A, s ⁻¹ᵁ Wt)
    (sliceAlgHom f qP s hsq Wt) _ _ fk Lk ak Ue cs hcs

  have hρ₀ : CommRingCat.ofHom (restrictAlgHom f le₀).toRingHom = A.presheaf.map (homOfLE le₀).op := rfl
  have hρ₁ : CommRingCat.ofHom (restrictAlgHom f le₁).toRingHom = A.presheaf.map (homOfLE le₁).op := rfl
  have M1₀ : Spec.map (CommRingCat.ofHom (restrictAlgHom f le₀).toRingHom) ≫ hD₀.fromSpec = hDt.fromSpec := by
    rw [hρ₀]; exact IsAffineOpen.map_fromSpec hD₀ hDt (homOfLE le₀).op
  have M1₁ : Spec.map (CommRingCat.ofHom (restrictAlgHom f le₁).toRingHom) ≫ hD₁.fromSpec = hDt.fromSpec := by
    rw [hρ₁]; exact IsAffineOpen.map_fromSpec hD₁ hDt (homOfLE le₁).op
  have M2₀ : Spec.map (CommRingCat.ofHom (restrictAlgHom f le₀).toRingHom) ≫ hD₀.isoSpec.inv ≫ (s ∣_ W₀) =
      hDt.isoSpec.inv ≫ (s ∣_ Wt) ≫ P.homOfLE hW₀ := by
    rw [← cancel_mono W₀.ι]
    simp only [Category.assoc, morphismRestrict_ι, Scheme.homOfLE_ι]
    rw [IsAffineOpen.isoSpec_inv_ι_assoc, IsAffineOpen.isoSpec_inv_ι_assoc, ← Category.assoc, M1₀]
  have M2₁ : Spec.map (CommRingCat.ofHom (restrictAlgHom f le₁).toRingHom) ≫ hD₁.isoSpec.inv ≫ (s ∣_ W₁) =
      hDt.isoSpec.inv ≫ (s ∣_ Wt) ≫ P.homOfLE hW₁ := by
    rw [← cancel_mono W₁.ι]
    simp only [Category.assoc, morphismRestrict_ι, Scheme.homOfLE_ι]
    rw [IsAffineOpen.isoSpec_inv_ι_assoc, IsAffineOpen.isoSpec_inv_ι_assoc, ← Category.assoc, M1₁]
  have M3 : Spec.map (CommRingCat.ofHom (sliceAlgHom f qP s hsq Wt).toRingHom) ≫ hWt.isoSpec.inv =
      hDt.isoSpec.inv ≫ (s ∣_ Wt) := by
    rw [← cancel_mono Wt.ι, ofHom_sliceAlgHom]
    simp only [Category.assoc, morphismRestrict_ι]
    rw [IsAffineOpen.isoSpec_inv_ι, IsAffineOpen.isoSpec_inv_ι_assoc,
      IsAffineOpen.SpecMap_appLE_fromSpec s hWt hDt le_rfl]

  have M2₀' := congrArg (· ≫ m₀) M2₀
  have M2₁' := congrArg (· ≫ m₁) M2₁
  have M3₀ := congrArg (· ≫ (P.homOfLE hW₀ ≫ m₀)) M3
  have M3₁ := congrArg (· ≫ (P.homOfLE hW₁ ≫ m₁)) M3
  simp only [Category.assoc] at M2₀' M2₁' M3₀ M3₁
  rw [M1₀, M2₀'] at R₀
  rw [M1₁, M2₁'] at R₁
  rw [M3₀, M3₁] at Rt

  have hu : hDt.fromSpec ≫ f = Spec.map (CommRingCat.ofHom (algebraMap T' Γ(A, s ⁻¹ᵁ Wt))) :=
    fromSpec_comp_eq f hDt
  have hy : ∀ {W : P.Opens} (hW : Wt ≤ W) (mW : (W : Scheme.{u}) ⟶ A) (hmW : mW ≫ f = W.ι ≫ qP),
      (hDt.isoSpec.inv ≫ (s ∣_ Wt) ≫ P.homOfLE hW ≫ mW) ≫ f =
        Spec.map (CommRingCat.ofHom (algebraMap T' Γ(A, s ⁻¹ᵁ Wt))) := by
    intro W hW mW hmW
    rw [← hu, ← IsAffineOpen.isoSpec_inv_ι]
    simp only [Category.assoc]
    rw [hmW, Scheme.homOfLE_ι_assoc, morphismRestrict_ι_assoc, hsq]
  have hquot : ∀ {W : P.Opens} (leW : s ⁻¹ᵁ Wt ≤ s ⁻¹ᵁ W),
      letI := algebraOfHom f (s ⁻¹ᵁ W)
      ∃ ρbar : (Γ(A, s ⁻¹ᵁ W) ⧸ I.map (algebraMap T' Γ(A, s ⁻¹ᵁ W))) →+*
          (Γ(A, s ⁻¹ᵁ Wt) ⧸ I.map (algebraMap T' Γ(A, s ⁻¹ᵁ Wt))),
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.map (algebraMap T' Γ(A, s ⁻¹ᵁ Wt))))) ≫ Spec.map (CommRingCat.ofHom (restrictAlgHom f leW).toRingHom) =
          Spec.map (CommRingCat.ofHom ρbar) ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.map (algebraMap T' Γ(A, s ⁻¹ᵁ W))))) := by
    intro W leW
    letI iW := algebraOfHom f (s ⁻¹ᵁ W)
    have hle : I.map (algebraMap T' Γ(A, s ⁻¹ᵁ W)) ≤
        (I.map (algebraMap T' Γ(A, s ⁻¹ᵁ Wt))).comap (restrictAlgHom f leW).toRingHom := by
      rw [Ideal.map_le_iff_le_comap]
      intro r hr
      simp only [Ideal.mem_comap]
      have h1 : (restrictAlgHom f leW).toRingHom (algebraMap T' Γ(A, s ⁻¹ᵁ W) r) = algebraMap T' Γ(A, s ⁻¹ᵁ Wt) r :=
        (restrictAlgHom f leW).commutes r
      rw [h1]
      exact Ideal.mem_map_of_mem _ hr
    refine ⟨Ideal.quotientMap _ (restrictAlgHom f leW).toRingHom hle, ?_⟩
    have hq : (Ideal.Quotient.mk (I.map (algebraMap T' Γ(A, s ⁻¹ᵁ Wt)))).comp (restrictAlgHom f leW).toRingHom =
        (Ideal.quotientMap _ (restrictAlgHom f leW).toRingHom hle).comp (Ideal.Quotient.mk _) :=
      (Ideal.quotientMap_comp_mk hle).symm
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, hq]
  have huv₀ : Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.map (algebraMap T' Γ(A, s ⁻¹ᵁ Wt))))) ≫ hDt.fromSpec =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.map (algebraMap T' Γ(A, s ⁻¹ᵁ Wt))))) ≫ (hDt.isoSpec.inv ≫ (s ∣_ Wt) ≫ P.homOfLE hW₀ ≫ m₀) := by
    obtain ⟨ρbar, hρbar⟩ := hquot le₀
    calc Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.map (algebraMap T' Γ(A, s ⁻¹ᵁ Wt))))) ≫ hDt.fromSpec
        = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.map (algebraMap T' Γ(A, s ⁻¹ᵁ Wt))))) ≫ (Spec.map (CommRingCat.ofHom (restrictAlgHom f le₀).toRingHom) ≫ hD₀.fromSpec) := by rw [M1₀]
      _ = (Spec.map (CommRingCat.ofHom ρbar) ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.map (algebraMap T' Γ(A, s ⁻¹ᵁ W₀)))))) ≫ hD₀.fromSpec := by rw [← Category.assoc, hρbar]
      _ = Spec.map (CommRingCat.ofHom ρbar) ≫ (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.map (algebraMap T' Γ(A, s ⁻¹ᵁ W₀))))) ≫ hD₀.fromSpec) := by rw [Category.assoc]
      _ = Spec.map (CommRingCat.ofHom ρbar) ≫ (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.map (algebraMap T' Γ(A, s ⁻¹ᵁ W₀))))) ≫ (hD₀.isoSpec.inv ≫ (s ∣_ W₀) ≫ m₀)) := by rw [hbmod₀]
      _ = (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.map (algebraMap T' Γ(A, s ⁻¹ᵁ Wt))))) ≫ Spec.map (CommRingCat.ofHom (restrictAlgHom f le₀).toRingHom)) ≫ (hD₀.isoSpec.inv ≫ (s ∣_ W₀) ≫ m₀) := by
          rw [← Category.assoc (Spec.map (CommRingCat.ofHom ρbar)), ← hρbar]
      _ = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.map (algebraMap T' Γ(A, s ⁻¹ᵁ Wt))))) ≫ (Spec.map (CommRingCat.ofHom (restrictAlgHom f le₀).toRingHom) ≫ hD₀.isoSpec.inv ≫ (s ∣_ W₀) ≫ m₀) := by rw [Category.assoc]
      _ = _ := by rw [M2₀']
  have huv₁ : Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.map (algebraMap T' Γ(A, s ⁻¹ᵁ Wt))))) ≫ hDt.fromSpec =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.map (algebraMap T' Γ(A, s ⁻¹ᵁ Wt))))) ≫ (hDt.isoSpec.inv ≫ (s ∣_ Wt) ≫ P.homOfLE hW₁ ≫ m₁) := by
    obtain ⟨ρbar, hρbar⟩ := hquot le₁
    calc Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.map (algebraMap T' Γ(A, s ⁻¹ᵁ Wt))))) ≫ hDt.fromSpec
        = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.map (algebraMap T' Γ(A, s ⁻¹ᵁ Wt))))) ≫ (Spec.map (CommRingCat.ofHom (restrictAlgHom f le₁).toRingHom) ≫ hD₁.fromSpec) := by rw [M1₁]
      _ = (Spec.map (CommRingCat.ofHom ρbar) ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.map (algebraMap T' Γ(A, s ⁻¹ᵁ W₁)))))) ≫ hD₁.fromSpec := by rw [← Category.assoc, hρbar]
      _ = Spec.map (CommRingCat.ofHom ρbar) ≫ (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.map (algebraMap T' Γ(A, s ⁻¹ᵁ W₁))))) ≫ hD₁.fromSpec) := by rw [Category.assoc]
      _ = Spec.map (CommRingCat.ofHom ρbar) ≫ (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.map (algebraMap T' Γ(A, s ⁻¹ᵁ W₁))))) ≫ (hD₁.isoSpec.inv ≫ (s ∣_ W₁) ≫ m₁)) := by rw [hbmod₁]
      _ = (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.map (algebraMap T' Γ(A, s ⁻¹ᵁ Wt))))) ≫ Spec.map (CommRingCat.ofHom (restrictAlgHom f le₁).toRingHom)) ≫ (hD₁.isoSpec.inv ≫ (s ∣_ W₁) ≫ m₁) := by
          rw [← Category.assoc (Spec.map (CommRingCat.ofHom ρbar)), ← hρbar]
      _ = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.map (algebraMap T' Γ(A, s ⁻¹ᵁ Wt))))) ≫ (Spec.map (CommRingCat.ofHom (restrictAlgHom f le₁).toRingHom) ≫ hD₁.isoSpec.inv ≫ (s ∣_ W₁) ≫ m₁) := by rw [Category.assoc]
      _ = _ := by rw [M2₁']
  have hadd := isTangentCoordsOfPairAt_add I hI hsmall V ι hι hιI Γ(A, s ⁻¹ᵁ Wt) f
    hDt.fromSpec (hDt.isoSpec.inv ≫ (s ∣_ Wt) ≫ P.homOfLE hW₀ ≫ m₀) (hDt.isoSpec.inv ≫ (s ∣_ Wt) ≫ P.homOfLE hW₁ ≫ m₁)
    hu (hy hW₀ m₀ hm₀) (hy hW₁ m₁ hm₁) huv₀ (huv₀.symm.trans huv₁) fk Lk ak hak Ue hUe e₁ he₁ _ _ _ R₀ Rt R₁
  have := congrFun hadd a
  simp only [Pi.add_apply] at this
  rw [this]
  exact (add_sub_cancel_left ((Algebra.TensorProduct.map (AlgHom.id (ResidueField T') (ResidueField T')) (restrictAlgHom f le₀)).toLinearMap ∘ₗ b₀ a) _).symm

end CoordsEq

end E160A3

end

noncomputable section

namespace E160A3

p2m_open "AlgebraicGeometry.Scheme.TwoAffineOpenCover TensorProduct AlgebraicGeometry.SmallExtension"

section Core

variable {T' : Type u} [CommRing T'] [IsLocalRing T'] [IsArtinianRing T']
  (I : Ideal T') (hI : I ≤ maximalIdeal T') (hsmall : I * maximalIdeal T' = ⊥)
  (V : Type u) [AddCommGroup V] [Module (ResidueField T') V] [Module (ResidueField T')ᵐᵒᵖ V]
  [IsCentralScalar (ResidueField T') V] [Module.Finite (ResidueField T') V]
  [Module T' V] [IsScalarTower T' (ResidueField T') V]
  (ι : V →ₗ[T'] T') (hι : Function.Injective ι) (hιI : LinearMap.range ι = Submodule.restrictScalars T' I)
  {A Ak P Pk : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of T')) [Flat f] (qP : P ⟶ Spec (CommRingCat.of T'))
  (fk : Ak ⟶ Spec (CommRingCat.of (ResidueField T'))) (Lk : RelativeGroupLaw (ResidueField T') fk)
  (ak : Ak ⟶ A) (hak : IsPullback ak fk f (Spec.map (CommRingCat.ofHom (residue T'))))
  (Ue : Ak.Opens) (hUe : IsAffineOpen Ue)
  (e₁ : Spec (CommRingCat.of (ResidueField T')) ⟶ (Ue : Scheme.{u})) (he₁ : e₁ ≫ Ue.ι = (Lk.one (𝟙 _)).1)
  (𝒲 : P.OrderedAffineCover) (m : ∀ i : 𝒲.ι, (↑(𝒲.U i) : Scheme.{u}) ⟶ A)
  (hmf : ∀ i, m i ≫ f = (𝒲.U i).ι ≫ qP)
  (hWaff : ∀ t : 𝒲.Idx 1, IsAffineOpen (𝒲.inter t))
  (bk : Pk ⟶ P) [IsAffineHom bk] (yk : Pk ⟶ Spec (CommRingCat.of (ResidueField T')))
  (σ : ∀ t : 𝒲.Idx 1, letI := algebraOfHom qP (𝒲.inter t)
    (ResidueField T' ⊗[T'] Γ(P, 𝒲.inter t)) ≃+* Γ(Pk, (𝒲.comap bk).inter t))
  (hσ₁ : ∀ (t : 𝒲.Idx 1) (x : Γ(P, 𝒲.inter t)), letI := algebraOfHom qP (𝒲.inter t)
    σ t ((1 : ResidueField T') ⊗ₜ[T'] x) =
      (Pk.presheaf.map (homOfLE (𝒲.comap_inter_le bk t)).op).hom ((bk.app (𝒲.inter t)).hom x))
  (hσ₂ : ∀ (t : 𝒲.Idx 1) (a : ResidueField T'), letI := algebraOfHom qP (𝒲.inter t)
    letI := algebraOfHom yk ((𝒲.comap bk).inter t)
    σ t (a ⊗ₜ[T'] (1 : Γ(P, 𝒲.inter t))) = algebraMap (ResidueField T') Γ(Pk, (𝒲.comap bk).inter t) a)
  (s : A ⟶ P) (hsq : s ≫ qP = f) (hsaff : ∀ W : P.Opens, IsAffineOpen W → IsAffineOpen (s ⁻¹ᵁ W))
  (iS : Ak ⟶ Pk) [IsAffineHom iS] (hiP : iS ≫ bk = ak ≫ s) (hiSy : iS ≫ yk = fk)
  (c : Γ(Ak, Ue) → Module.Dual (ResidueField T') V → ∀ t : 𝒲.Idx 1, Γ(Pk, (𝒲.comap bk).inter t))
  (hc : ∀ t : 𝒲.Idx 1, letI := algebraOfHom qP (𝒲.inter t)
    ∃ cs : Γ(Ak, Ue) → (Module.Dual (ResidueField T') V →ₗ[ResidueField T'] (ResidueField T' ⊗[T'] Γ(P, 𝒲.inter t))),
      IsTangentCoordsOfPairAt I V ι Γ(P, 𝒲.inter t)
        ((hWaff t).isoSpec.inv ≫ P.homOfLE (𝒲.inter_le t 0) ≫ m (t.1 0))
        ((hWaff t).isoSpec.inv ≫ P.homOfLE (𝒲.inter_le t 1) ≫ m (t.1 1)) fk Lk ak Ue cs ∧
      ∀ (a : Γ(Ak, Ue)) (ξ : Module.Dual (ResidueField T') V), σ t (cs a ξ) = c a ξ t)
  (hb : ∀ (i : 𝒲.ι) (hU : IsAffineOpen (s ⁻¹ᵁ 𝒲.U i)), letI := algebraOfHom f (s ⁻¹ᵁ 𝒲.U i)
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.map (algebraMap T' Γ(A, s ⁻¹ᵁ 𝒲.U i))))) ≫ hU.fromSpec =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.map (algebraMap T' Γ(A, s ⁻¹ᵁ 𝒲.U i))))) ≫
        (hU.isoSpec.inv ≫ (s ∣_ 𝒲.U i) ≫ m i) ∧
    ∃ b : Γ(Ak, Ue) → (Module.Dual (ResidueField T') V →ₗ[ResidueField T'] (ResidueField T' ⊗[T'] Γ(A, s ⁻¹ᵁ 𝒲.U i))),
      IsTangentCoordsOfPairAt I V ι Γ(A, s ⁻¹ᵁ 𝒲.U i) hU.fromSpec (hU.isoSpec.inv ≫ (s ∣_ 𝒲.U i) ≫ m i) fk Lk ak Ue b)

include hI hsmall hι hιI hak hUe he₁ hmf hσ₁ hσ₂ hsq hsaff hiP hiSy hc hb

theorem slice_core (a : Γ(Ak, Ue)) (ξ : Module.Dual (ResidueField T') V) :
    ∃ b : (OModulePresheaf.unit fk).cochain ((𝒲.comap bk).comap iS) 0,
      (OModulePresheaf.unit fk).d ((𝒲.comap bk).comap iS) 0 b = fun t =>
        (Ak.presheaf.map (homOfLE ((𝒲.comap bk).comap_inter_le iS t)).op).hom
          ((iS.app ((𝒲.comap bk).inter t)).hom (c a ξ t)) := by
  classical
  have hU : ∀ i, IsAffineOpen (s ⁻¹ᵁ 𝒲.U i) := fun i => hsaff _ (𝒲.isAffineOpen i)
  let bf : ∀ i, letI := algebraOfHom f (s ⁻¹ᵁ 𝒲.U i)
      Γ(Ak, Ue) → (Module.Dual (ResidueField T') V →ₗ[ResidueField T'] (ResidueField T' ⊗[T'] Γ(A, s ⁻¹ᵁ 𝒲.U i))) :=
    fun i => (hb i (hU i)).2.choose
  have hbf : ∀ i, letI := algebraOfHom f (s ⁻¹ᵁ 𝒲.U i)
      IsTangentCoordsOfPairAt I V ι Γ(A, s ⁻¹ᵁ 𝒲.U i) (hU i).fromSpec ((hU i).isoSpec.inv ≫ (s ∣_ 𝒲.U i) ≫ m i)
        fk Lk ak Ue (bf i) := fun i => (hb i (hU i)).2.choose_spec
  have hmod := fun i => (hb i (hU i)).1
  have hakw : ak ≫ f = fk ≫ Spec.map (CommRingCat.ofHom (residue T')) := hak.w

  have hle : ∀ r : ((𝒲.comap bk).comap iS).Idx 0,
      ((𝒲.comap bk).comap iS).inter r ≤ ak ⁻¹ᵁ (s ⁻¹ᵁ 𝒲.U (r.1 0)) := fun r => by
    refine (((𝒲.comap bk).comap iS).inter_le r 0).trans ?_
    change iS ⁻¹ᵁ (bk ⁻¹ᵁ 𝒲.U (r.1 0)) ≤ ak ⁻¹ᵁ (s ⁻¹ᵁ 𝒲.U (r.1 0))
    rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, hiP]
  have hlet : ∀ t : 𝒲.Idx 1, ((𝒲.comap bk).comap iS).inter t ≤ ak ⁻¹ᵁ (s ⁻¹ᵁ 𝒲.inter t) := fun t => by
    have h1 : ((𝒲.comap bk).comap iS).inter t ≤ iS ⁻¹ᵁ (bk ⁻¹ᵁ 𝒲.inter t) :=
      (((𝒲.comap bk).comap_inter_le iS t)).trans (fun x hx => 𝒲.comap_inter_le bk t hx)
    rw [← Scheme.Hom.comp_preimage, hiP, Scheme.Hom.comp_preimage] at h1
    exact h1
  refine ⟨fun r => Phi f fk ak hakw (s ⁻¹ᵁ 𝒲.U (r.1 0)) (((𝒲.comap bk).comap iS).inter r) (hle r)
    (bf (r.1 0) a ξ), ?_⟩
  funext t
  letI i0 := algebraOfHom f (s ⁻¹ᵁ 𝒲.U (t.1 0))
  letI i1 := algebraOfHom f (s ⁻¹ᵁ 𝒲.U (t.1 1))
  letI it := algebraOfHom f (s ⁻¹ᵁ 𝒲.inter t)
  letI iq := algebraOfHom qP (𝒲.inter t)
  rw [OModulePresheaf.d_apply, Fin.sum_univ_two]
  simp only [Fin.val_zero, pow_zero, one_smul, Fin.val_one, pow_one, neg_one_zsmul]

  have le₀ : s ⁻¹ᵁ 𝒲.inter t ≤ s ⁻¹ᵁ 𝒲.U (t.1 0) := fun x hx => 𝒲.inter_le t 0 hx
  have le₁ : s ⁻¹ᵁ 𝒲.inter t ≤ s ⁻¹ᵁ 𝒲.U (t.1 1) := fun x hx => 𝒲.inter_le t 1 hx
  have e0 : (OModulePresheaf.unit fk).res (((𝒲.comap bk).comap iS).inter_le_inter_face t 0)
      (Phi f fk ak hakw (s ⁻¹ᵁ 𝒲.U ((((𝒲.comap bk).comap iS).face t 0).1 0))
        (((𝒲.comap bk).comap iS).inter (((𝒲.comap bk).comap iS).face t 0)) (hle _)
        (bf ((((𝒲.comap bk).comap iS).face t 0).1 0) a ξ)) =
      Phi f fk ak hakw (s ⁻¹ᵁ 𝒲.inter t) (((𝒲.comap bk).comap iS).inter t) (hlet t)
        ((Algebra.TensorProduct.map (AlgHom.id (ResidueField T') (ResidueField T'))
          (restrictAlgHom f le₁)).toLinearMap (bf (t.1 1) a ξ)) :=
    res_Phi f fk ak hakw _ _ le₁ _ _ _ _ _ _
  have e1 : (OModulePresheaf.unit fk).res (((𝒲.comap bk).comap iS).inter_le_inter_face t 1)
      (Phi f fk ak hakw (s ⁻¹ᵁ 𝒲.U ((((𝒲.comap bk).comap iS).face t 1).1 0))
        (((𝒲.comap bk).comap iS).inter (((𝒲.comap bk).comap iS).face t 1)) (hle _)
        (bf ((((𝒲.comap bk).comap iS).face t 1).1 0) a ξ)) =
      Phi f fk ak hakw (s ⁻¹ᵁ 𝒲.inter t) (((𝒲.comap bk).comap iS).inter t) (hlet t)
        ((Algebra.TensorProduct.map (AlgHom.id (ResidueField T') (ResidueField T'))
          (restrictAlgHom f le₀)).toLinearMap (bf (t.1 0) a ξ)) :=
    res_Phi f fk ak hakw _ _ le₀ _ _ _ _ _ _
  rw [e0, e1]

  obtain ⟨cs, hcs, hcsσ⟩ := hc t
  have hcoord := slice_coords_eq_sub I hI hsmall V ι hι hιI f qP fk Lk ak hak Ue hUe e₁ he₁ s hsq
    (𝒲.U (t.1 0)) (𝒲.U (t.1 1)) (𝒲.inter t) (𝒲.inter_le t 0) (𝒲.inter_le t 1)
    (hWaff t) (hU (t.1 0)) (hU (t.1 1)) (hsaff _ (hWaff t)) (m (t.1 0)) (m (t.1 1)) (hmf _) (hmf _)
    cs hcs (bf (t.1 0)) (bf (t.1 1)) (hmod (t.1 0)) (hmod (t.1 1)) (hbf (t.1 0)) (hbf (t.1 1)) a
  have hcoordξ := LinearMap.congr_fun hcoord ξ
  simp only [LinearMap.comp_apply, LinearMap.sub_apply] at hcoordξ
  rw [← sub_eq_add_neg]
  have key : Phi f fk ak hakw (s ⁻¹ᵁ 𝒲.inter t) (((𝒲.comap bk).comap iS).inter t) (hlet t)
        ((Algebra.TensorProduct.map (AlgHom.id (ResidueField T') (ResidueField T'))
          (restrictAlgHom f le₁)).toLinearMap (bf (t.1 1) a ξ)) -
      Phi f fk ak hakw (s ⁻¹ᵁ 𝒲.inter t) (((𝒲.comap bk).comap iS).inter t) (hlet t)
        ((Algebra.TensorProduct.map (AlgHom.id (ResidueField T') (ResidueField T'))
          (restrictAlgHom f le₀)).toLinearMap (bf (t.1 0) a ξ)) =
      Phi f fk ak hakw (s ⁻¹ᵁ 𝒲.inter t) (((𝒲.comap bk).comap iS).inter t) (hlet t)
        ((Algebra.TensorProduct.map (AlgHom.id (ResidueField T') (ResidueField T'))
          (sliceAlgHom f qP s hsq (𝒲.inter t))).toLinearMap (cs a ξ)) := by
    rw [hcoordξ, map_sub]
  refine key.trans ?_
  rw [← hcsσ]
  exact (sigma_push f fk ak hakw qP bk yk s iS hiP hiSy (𝒲.inter t) ((𝒲.comap bk).inter t)
    (𝒲.comap_inter_le bk t) (((𝒲.comap bk).comap iS).inter t) ((𝒲.comap bk).comap_inter_le iS t) (hlet t)
    (σ t) (hσ₁ t) (hσ₂ t) (sliceAlgHom f qP s hsq (𝒲.inter t)) (fun x => rfl) (cs a ξ)).symm

end Core

end E160A3

end

theorem solution
    (T' T : Type u) [CommRing T'] [IsLocalRing T'] [IsArtinianRing T'] [IsAlgClosed (ResidueField T')]
    [CommRing T] (π : T' →+* T) (hπ : Function.Surjective π) (hker : IsNilpotent (RingHom.ker π))
    (hsmall : RingHom.ker π * maximalIdeal T' = ⊥)
    {A₀ : Scheme.{u}} (f₀ : A₀ ⟶ Spec (CommRingCat.of T)) (L₀ : RelativeGroupLaw T f₀) (hc₀ : L₀.IsCommutative)
    (h₀ : AbelianSchemePropertyBundle T f₀)
    {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of T')) (hs : Smooth f) (hp : IsProper f)
    (g : A₀ ⟶ A) (hg : IsPullback g f₀ f (Spec.map (CommRingCat.ofHom π)))
    (e : SchemeHomOver (𝟙 (Spec (CommRingCat.of T'))) f)
    (he : Spec.map (CommRingCat.ofHom π) ≫ e.1 = (L₀.one (𝟙 (Spec (CommRingCat.of T)))).1 ≫ g)

    (hI : RingHom.ker π ≤ maximalIdeal T')
    (ρ : T →+* ResidueField T') (hρ : ρ.comp π = residue T')
    (V : Type u) [AddCommGroup V] [Module (ResidueField T') V] [Module.Finite (ResidueField T') V]
    [Module T' V] [IsScalarTower T' (ResidueField T') V]
    [Module (ResidueField T')ᵐᵒᵖ V] [IsCentralScalar (ResidueField T') V]
    (ι : V →ₗ[T'] T') (hι : Function.Injective ι)
    (hιI : LinearMap.range ι = Submodule.restrictScalars T' (RingHom.ker π))

    [IsSeparated (pullback.fst f f ≫ f)]
    (𝒲 : (pullback f f).OrderedAffineCover)
    (m : ∀ i : 𝒲.ι, (↑(𝒲.U i) : Scheme.{u}) ⟶ A)
    (hmf : ∀ i, m i ≫ f = (𝒲.U i).ι ≫ pullback.fst f f ≫ f)
    (hmμ : ∀ i, morphismRestrict (pullback.lift (pullback.fst f₀ f₀ ≫ g) (pullback.snd f₀ f₀ ≫ g)
              (by rw [Category.assoc, Category.assoc, hg.w, ← Category.assoc, ← Category.assoc, pullback.condition])) (𝒲.U i) ≫ m i
        = ((pullback.lift (pullback.fst f₀ f₀ ≫ g) (pullback.snd f₀ f₀ ≫ g)
              (by rw [Category.assoc, Category.assoc, hg.w, ← Category.assoc, ← Category.assoc, pullback.condition])) ⁻¹ᵁ (𝒲.U i)).ι ≫
          (L₀.mul (pullback.fst f₀ f₀ ≫ f₀) ⟨pullback.fst f₀ f₀, rfl⟩ ⟨pullback.snd f₀ f₀, pullback.condition.symm⟩).1 ≫ g)

    {Ak : Scheme.{u}} (fk : Ak ⟶ Spec (CommRingCat.of (ResidueField T'))) (Lk : RelativeGroupLaw (ResidueField T') fk)
    (i₀ : Ak ⟶ A₀) (hi₀ : IsPullback i₀ fk f₀ (Spec.map (CommRingCat.ofHom ρ)))
    (Ue : Ak.Opens) (hUe : IsAffineOpen Ue)
    (e₁ : Spec (CommRingCat.of (ResidueField T')) ⟶ (Ue : Scheme.{u})) (he₁ : e₁ ≫ Ue.ι = (Lk.one (𝟙 _)).1)

    {Pk : Scheme.{u}} (bk : Pk ⟶ pullback f f) [IsAffineHom bk] (yk : Pk ⟶ Spec (CommRingCat.of (ResidueField T')))
    (hbk : IsPullback bk yk (pullback.fst f f ≫ f) (Spec.map (CommRingCat.ofHom (residue T'))))
    (σ : ∀ {n : ℕ} (s : 𝒲.Idx n),
      letI := algebraOfHom (pullback.fst f f ≫ f) (𝒲.inter s)
      ((ResidueField T') ⊗[T'] Γ(pullback f f, 𝒲.inter s)) ≃+* Γ(Pk, (𝒲.comap bk).inter s))
    (hσ₁ : ∀ {n : ℕ} (s : 𝒲.Idx n) (x : Γ(pullback f f, 𝒲.inter s)),
      letI := algebraOfHom (pullback.fst f f ≫ f) (𝒲.inter s)
      σ s ((1 : ResidueField T') ⊗ₜ[T'] x) =
        (Pk.presheaf.map (homOfLE (𝒲.comap_inter_le bk s)).op).hom ((bk.app (𝒲.inter s)).hom x))
    (hσ₂ : ∀ {n : ℕ} (s : 𝒲.Idx n) (a : ResidueField T'),
      letI := algebraOfHom (pullback.fst f f ≫ f) (𝒲.inter s)
      letI := algebraOfHom yk ((𝒲.comap bk).inter s)
      σ s (a ⊗ₜ[T'] (1 : Γ(pullback f f, 𝒲.inter s))) = algebraMap (ResidueField T') Γ(Pk, (𝒲.comap bk).inter s) a)

    (p₁ p₂ : Pk ⟶ Ak)
    (hp₁ : p₁ ≫ i₀ ≫ g = bk ≫ pullback.fst f f) (hp₁k : p₁ ≫ fk = yk)
    (hp₂ : p₂ ≫ i₀ ≫ g = bk ≫ pullback.snd f f) (hp₂k : p₂ ≫ fk = yk)
    (hPk : IsPullback p₁ p₂ fk fk)
    (ek : Spec (CommRingCat.of (ResidueField T')) ⟶ Ak)
    (hek : ek ≫ i₀ ≫ g = Spec.map (CommRingCat.ofHom (residue T')) ≫ e.1) (hekk : ek ≫ fk = 𝟙 _)
    (iX : Ak ⟶ Pk) [IsClosedImmersion iX] (hiX₁ : iX ≫ p₁ = 𝟙 Ak) (hiX₂ : iX ≫ p₂ = fk ≫ ek)
    (hiXP : iX ≫ bk = (i₀ ≫ g) ≫ pullback.lift (𝟙 A) (f ≫ e.1) (by rw [Category.id_comp, Category.assoc, e.2, Category.comp_id]))
    (iY : Ak ⟶ Pk) [IsClosedImmersion iY] (hiY₁ : iY ≫ p₁ = fk ≫ ek) (hiY₂ : iY ≫ p₂ = 𝟙 Ak)
    (hiYP : iY ≫ bk = (i₀ ≫ g) ≫ pullback.lift (f ≫ e.1) (𝟙 A) (by rw [Category.id_comp, Category.assoc, e.2, Category.comp_id]))
    (c : letI := algebraOfHom fk Ue
      ↥(Algebra.PointDerivations (ResidueField T') Γ(Ak, Ue)
          ((Ue.topIso.inv ≫ e₁.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of (ResidueField T'))).hom).hom)
          (Module.Dual (ResidueField T') V →ₗ[ResidueField T'] (OModulePresheaf.unit (p₁ ≫ fk)).cochain (𝒲.comap bk) 1)))
    (hc : letI := algebraOfHom fk Ue
      (∀ s : 𝒲.Idx 1,
        letI := algebraOfHom (pullback.fst f f ≫ f) (𝒲.inter s)
        ∃ cs : Γ(Ak, Ue) → (Module.Dual (ResidueField T') V →ₗ[ResidueField T'] ((ResidueField T') ⊗[T'] Γ(pullback f f, 𝒲.inter s))),
          IsTangentCoordsOfPairAt (RingHom.ker π) V ι Γ(pullback f f, 𝒲.inter s)
            ((Scheme.OrderedAffineCover.isAffineOpen_inter (pullback.fst f f ≫ f) 𝒲 s).isoSpec.inv ≫
              (pullback f f).homOfLE (𝒲.inter_le s 0) ≫ m (s.1 0))
            ((Scheme.OrderedAffineCover.isAffineOpen_inter (pullback.fst f f ≫ f) 𝒲 s).isoSpec.inv ≫
              (pullback f f).homOfLE (𝒲.inter_le s 1) ≫ m (s.1 1))
            fk Lk (i₀ ≫ g) Ue cs ∧
          ∀ (a : Γ(Ak, Ue)) (ξ : Module.Dual (ResidueField T') V), σ s (cs a ξ) = c.1 a ξ s))

    (sX : A ⟶ pullback f f) (hsX : sX = pullback.lift (𝟙 A) (f ≫ e.1) (by rw [Category.id_comp, Category.assoc, e.2, Category.comp_id]))
    (sY : A ⟶ pullback f f) (hsY : sY = pullback.lift (f ≫ e.1) (𝟙 A) (by rw [Category.id_comp, Category.assoc, e.2, Category.comp_id]))

    (hbX : ∀ (i : 𝒲.ι) (hU : IsAffineOpen (sX ⁻¹ᵁ 𝒲.U i)),
      letI := algebraOfHom f (sX ⁻¹ᵁ 𝒲.U i)
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk ((RingHom.ker π).map (algebraMap T' Γ(A, sX ⁻¹ᵁ 𝒲.U i))))) ≫ hU.fromSpec
        = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk ((RingHom.ker π).map (algebraMap T' Γ(A, sX ⁻¹ᵁ 𝒲.U i))))) ≫
            (hU.isoSpec.inv ≫ (sX ∣_ 𝒲.U i) ≫ m i) ∧
      ∃ b : Γ(Ak, Ue) → (Module.Dual (ResidueField T') V →ₗ[ResidueField T'] ((ResidueField T') ⊗[T'] Γ(A, sX ⁻¹ᵁ 𝒲.U i))),
        IsTangentCoordsOfPairAt (RingHom.ker π) V ι Γ(A, sX ⁻¹ᵁ 𝒲.U i)
          hU.fromSpec (hU.isoSpec.inv ≫ (sX ∣_ 𝒲.U i) ≫ m i) fk Lk (i₀ ≫ g) Ue b)
    (hbY : ∀ (i : 𝒲.ι) (hU : IsAffineOpen (sY ⁻¹ᵁ 𝒲.U i)),
      letI := algebraOfHom f (sY ⁻¹ᵁ 𝒲.U i)
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk ((RingHom.ker π).map (algebraMap T' Γ(A, sY ⁻¹ᵁ 𝒲.U i))))) ≫ hU.fromSpec
        = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk ((RingHom.ker π).map (algebraMap T' Γ(A, sY ⁻¹ᵁ 𝒲.U i))))) ≫
            (hU.isoSpec.inv ≫ (sY ∣_ 𝒲.U i) ≫ m i) ∧
      ∃ b : Γ(Ak, Ue) → (Module.Dual (ResidueField T') V →ₗ[ResidueField T'] ((ResidueField T') ⊗[T'] Γ(A, sY ⁻¹ᵁ 𝒲.U i))),
        IsTangentCoordsOfPairAt (RingHom.ker π) V ι Γ(A, sY ⁻¹ᵁ 𝒲.U i)
          hU.fromSpec (hU.isoSpec.inv ≫ (sY ∣_ 𝒲.U i) ≫ m i) fk Lk (i₀ ≫ g) Ue b) :
    (∀ (a : Γ(Ak, Ue)) (ξ : Module.Dual (ResidueField T') V),
        ∃ b : (OModulePresheaf.unit fk).cochain ((𝒲.comap bk).comap iX) 0,
          (OModulePresheaf.unit fk).d ((𝒲.comap bk).comap iX) 0 b = fun t =>
            (Ak.presheaf.map (homOfLE ((𝒲.comap bk).comap_inter_le iX t)).op).hom
              ((iX.app ((𝒲.comap bk).inter t)).hom (c.1 a ξ t))) ∧
    (∀ (a : Γ(Ak, Ue)) (ξ : Module.Dual (ResidueField T') V),
        ∃ b : (OModulePresheaf.unit fk).cochain ((𝒲.comap bk).comap iY) 0,
          (OModulePresheaf.unit fk).d ((𝒲.comap bk).comap iY) 0 b = fun t =>
            (Ak.presheaf.map (homOfLE ((𝒲.comap bk).comap_inter_le iY t)).op).hom
              ((iY.app ((𝒲.comap bk).inter t)).hom (c.1 a ξ t))) := by
  classical

  haveI : Smooth f := hs
  haveI : Flat f := inferInstance
  haveI : IsProper f := hp
  haveI : IsSeparated f := inferInstance
  haveI : IsSeparated (pullback.fst f f) := MorphismProperty.pullback_fst _ _ inferInstance
  haveI : IsSeparated (pullback.snd f f) := MorphismProperty.pullback_snd _ _ inferInstance
  have hak : IsPullback (i₀ ≫ g) fk f (Spec.map (CommRingCat.ofHom (residue T'))) := by
    have h := IsPullback.paste_horiz hi₀ hg
    rwa [← Spec.map_comp, show CommRingCat.ofHom π ≫ CommRingCat.ofHom ρ = CommRingCat.ofHom (residue T') from by
      rw [← CommRingCat.ofHom_comp, hρ]] at h
  have hsXfst : sX ≫ pullback.fst f f = 𝟙 A := by rw [hsX, pullback.lift_fst]
  have hsYsnd : sY ≫ pullback.snd f f = 𝟙 A := by rw [hsY, pullback.lift_snd]
  have hsqX : sX ≫ pullback.fst f f ≫ f = f := by rw [← Category.assoc, hsXfst, Category.id_comp]
  have hsqY : sY ≫ pullback.fst f f ≫ f = f := by
    rw [← Category.assoc, hsY, pullback.lift_fst, Category.assoc, e.2, Category.comp_id]
  have hiSyX : iX ≫ yk = fk := by rw [← hp₁k, ← Category.assoc, hiX₁, Category.id_comp]
  have hiSyY : iY ≫ yk = fk := by rw [← hp₂k, ← Category.assoc, hiY₂, Category.id_comp]
  have hiPX : iX ≫ bk = (i₀ ≫ g) ≫ sX := by rw [hiXP, hsX]
  have hiPY : iY ≫ bk = (i₀ ≫ g) ≫ sY := by rw [hiYP, hsY]
  haveI : IsClosedImmersion sX := by
    have : IsClosedImmersion (sX ≫ pullback.fst f f) := by rw [hsXfst]; infer_instance
    exact IsClosedImmersion.of_comp sX (pullback.fst f f)
  haveI : IsClosedImmersion sY := by
    have : IsClosedImmersion (sY ≫ pullback.snd f f) := by rw [hsYsnd]; infer_instance
    exact IsClosedImmersion.of_comp sY (pullback.snd f f)
  have hsaffX : ∀ W : (pullback f f).Opens, IsAffineOpen W → IsAffineOpen (sX ⁻¹ᵁ W) := fun W hW => hW.preimage sX
  have hsaffY : ∀ W : (pullback f f).Opens, IsAffineOpen W → IsAffineOpen (sY ⁻¹ᵁ W) := fun W hW => hW.preimage sY
  have hWaff : ∀ {n : ℕ} (t : 𝒲.Idx n), IsAffineOpen (𝒲.inter t) := fun t =>
    Scheme.OrderedAffineCover.isAffineOpen_inter (pullback.fst f f ≫ f) 𝒲 t
  haveI : IsAffineHom iX := inferInstance
  haveI : IsAffineHom iY := inferInstance
  refine ⟨fun a ξ => ?_, fun a ξ => ?_⟩
  · exact E160A3.slice_core (RingHom.ker π) hI hsmall V ι hι hιI f (pullback.fst f f ≫ f) fk Lk (i₀ ≫ g) hak
      Ue hUe e₁ he₁ 𝒲 m hmf (fun t => hWaff t) bk yk (fun t => σ t) (fun t x => hσ₁ t x) (fun t a => hσ₂ t a)
      sX hsqX hsaffX iX hiPX hiSyX (fun a ξ t => c.1 a ξ t) hc hbX a ξ
  · exact E160A3.slice_core (RingHom.ker π) hI hsmall V ι hι hιI f (pullback.fst f f ≫ f) fk Lk (i₀ ≫ g) hak
      Ue hUe e₁ he₁ 𝒲 m hmf (fun t => hWaff t) bk yk (fun t => σ t) (fun t x => hσ₁ t x) (fun t a => hσ₂ t a)
      sY hsqY hsaffY iY hiPY hiSyY (fun a ξ t => c.1 a ξ t) hc hbY a ξ

end S_GoodReductionJacobian_RelativeGroupLaw_exists_d_comap_slice_eq_of_isTangentCoordsOfPairAt_slice
end P2MW
export P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_d_comap_slice_eq_of_isTangentCoordsOfPairAt_slice (solution)
