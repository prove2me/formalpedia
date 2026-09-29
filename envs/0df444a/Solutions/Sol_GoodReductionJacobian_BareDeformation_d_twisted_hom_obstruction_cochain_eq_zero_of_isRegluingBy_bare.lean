-- Prove2me | solution 1 for GoodReductionJacobian.BareDeformation.d_twisted_hom_obstruction_cochain_eq_zero_of_isRegluingBy_bare
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/079c9b64-e845-515d-bd34-68906ce91e3d

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
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCochainPullback

import Theorems.Thm_AlgebraicGeometry_SmallExtension_isTangentCoordsOfPairAt_add
import Theorems.Thm_AlgebraicGeometry_SmallExtension_isTangentCoordsOfPairAt_comp_of_flat
import Theorems.Thm_AlgebraicGeometry_IsPullback_exists_iso_Spec_quotient_comp_morphismRestrict_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_BareDeformation_d_twisted_hom_obstruction_cochain_eq_zero_of_isRegluingBy_bare

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM CerednikDrinfeld.SpecialFormal IsLocalRing AlgebraicGeometry.Scheme.TwoAffineOpenCover"

open scoped Quaternion TensorProduct NumberField

universe u

noncomputable section

namespace P2mTwistedO2

open AlgebraicGeometry.SmallExtension

theorem map_id_apply_eq_self {T' : Type u} [CommRing T'] [IsLocalRing T'] (I : Ideal T') (hI : I ≤ maximalIdeal T')
    (C : Type u) [CommRing C] [Algebra T' C] (ψ : C →ₐ[T'] C)
    (hψ : ∀ c : C, Ideal.Quotient.mk (I.map (algebraMap T' C)) (ψ c) = Ideal.Quotient.mk (I.map (algebraMap T' C)) c)
    (x : ResidueField T' ⊗[T'] C) :
    Algebra.TensorProduct.map (AlgHom.id (ResidueField T') (ResidueField T')) ψ x = x := by
  have key : ∀ z ∈ I.map (algebraMap T' C), ((1 : ResidueField T') ⊗ₜ[T'] z : ResidueField T' ⊗[T'] C) = 0 := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨i, hi, rfl⟩ := hz
      rw [Algebra.algebraMap_eq_smul_one, ← TensorProduct.smul_tmul, Algebra.smul_def, mul_one,
        show algebraMap T' (ResidueField T') i = 0 from (residue_eq_zero_iff i).mpr (hI hi), TensorProduct.zero_tmul]
    | zero => exact TensorProduct.tmul_zero _ _
    | add z w _ _ hz hw => rw [TensorProduct.tmul_add, hz, hw, add_zero]
    | smul c z _ hz =>
      rw [smul_eq_mul, show ((1 : ResidueField T') ⊗ₜ[T'] (c * z) : ResidueField T' ⊗[T'] C) =
        ((1 : ResidueField T') ⊗ₜ[T'] c) * ((1 : ResidueField T') ⊗ₜ[T'] z) by rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul],
        hz, mul_zero]
  induction x using TensorProduct.induction_on with
  | zero => exact map_zero _
  | tmul a c =>
    rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
    have hz : ψ c - c ∈ I.map (algebraMap T' C) := Ideal.Quotient.eq.mp (hψ c)
    have h0 : (a ⊗ₜ[T'] (ψ c - c) : ResidueField T' ⊗[T'] C) = 0 := by
      rw [show (a ⊗ₜ[T'] (ψ c - c) : ResidueField T' ⊗[T'] C) = (a ⊗ₜ[T'] (1 : C)) * ((1 : ResidueField T') ⊗ₜ[T'] (ψ c - c)) by
        rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul], key _ hz, mul_zero]
    rwa [TensorProduct.tmul_sub, sub_eq_zero] at h0
  | add x y hx hy => rw [map_add, hx, hy]

theorem specMap_mk_comp_eq_of_isTangentCoordsOfPairAt {T' : Type u} [CommRing T'] [IsLocalRing T'] (I : Ideal T')
    (V : Type u) [AddCommGroup V] [Module (ResidueField T') V] [Module (ResidueField T')ᵐᵒᵖ V]
    [IsCentralScalar (ResidueField T') V] [Module T' V] [IsScalarTower T' (ResidueField T') V]
    (ι : V →ₗ[T'] T') (C : Type u) [CommRing C] [Algebra T' C]
    {Y : Scheme.{u}} (u v : Spec (CommRingCat.of C) ⟶ Y)
    {Ak : Scheme.{u}} (xk : Ak ⟶ Spec (CommRingCat.of (ResidueField T'))) (Lk : RelativeGroupLaw (ResidueField T') xk)
    (ak : Ak ⟶ Y) (Ue : Ak.Opens)
    (c : Γ(Ak, Ue) → (Module.Dual (ResidueField T') V →ₗ[ResidueField T'] (ResidueField T' ⊗[T'] C)))
    (h : IsTangentCoordsOfPairAt I V ι C u v xk Lk ak Ue c) :
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.map (algebraMap T' C)))) ≫ u
      = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.map (algebraMap T' C)))) ≫ v := by
  obtain ⟨w₀, hw₀, w₁, ⟨ϑ, _, φ, hu, hv, -⟩, -, -⟩ := h
  rw [← hu, ← hv, ← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
    ← CommRingCat.ofHom_comp]
  have : (Ideal.Quotient.mk (I.map (algebraMap T' C))).comp (pairFst I C) =
      (Ideal.Quotient.mk (I.map (algebraMap T' C))).comp (pairSnd I C) := RingHom.ext fun x => x.2
  rw [this]

theorem flat_sections {R : Type u} [CommRing R] {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) [hf : Flat f] {U : X.Opens}
    (hU : IsAffineOpen U) :
    letI := algebraOfHom f U
    Module.Flat R Γ(X, U) := by
  have h := HasRingHomProperty.appLE @Flat f hf ⟨⊤, isAffineOpen_top _⟩ ⟨U, hU⟩ (by simp)
  have h' : RingHom.Flat ((Scheme.ΓSpecIso (.of R)).inv ≫ f.appLE ⊤ U le_top).hom := by
    rw [CommRingCat.hom_comp]
    exact RingHom.Flat.comp (RingHom.Flat.of_bijective (Scheme.ΓSpecIso (.of R)).symm.commRingCatIsoToRingEquiv.bijective) h
  exact h'

theorem fromSpec_comp_eq {R : Type u} [CommRing R] {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) {U : X.Opens}
    (hU : IsAffineOpen U) :
    letI := algebraOfHom f U
    hU.fromSpec ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R Γ(X, U))) := by
  letI := algebraOfHom f U
  have h := IsAffineOpen.SpecMap_appLE_fromSpec f (isAffineOpen_top (Spec (.of R))) hU
    (show U ≤ f ⁻¹ᵁ ⊤ by simp)
  rw [← h, IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv, ← Spec.map_comp]
  rfl

theorem apply_eq_self_of_morphismRestrict_comp_eq {X₀ X : Scheme.{u}} (G : X₀ ⟶ X) [Surjective G] (U : X.Opens)
    (τ : (↑U : Scheme.{u}) ⟶ ↑U) (hτ : (G ∣_ U) ≫ τ = G ∣_ U) (y : ↑U) : τ y = y := by
  haveI : Surjective (G ∣_ U) := IsZariskiLocalAtTarget.restrict ‹_› U
  obtain ⟨x, rfl⟩ := (G ∣_ U).surjective y
  rw [← Scheme.Hom.comp_apply, hτ]

theorem surjective_of_isPullback_of_surjective_of_isNilpotent {T' T : Type u} [CommRing T'] [CommRing T]
    (π : T' →+* T) (hπ : Function.Surjective π) (hker : IsNilpotent (RingHom.ker π))
    {P P₀ : Scheme.{u}} (p : P ⟶ Spec (.of T')) (p₀ : P₀ ⟶ Spec (.of T)) (G : P₀ ⟶ P)
    (hG : IsPullback G p₀ p (Spec.map (CommRingCat.ofHom π))) : Surjective G := by
  haveI : Surjective (Spec.map (CommRingCat.ofHom π)) := by
    refine ⟨fun x => ?_⟩
    have hr : Set.range (PrimeSpectrum.comap π) = Set.univ := by
      rw [range_comap_of_surjective _ π hπ, Set.eq_univ_iff_forall]
      intro q
      rw [PrimeSpectrum.mem_zeroLocus]
      obtain ⟨n, hn⟩ := hker
      have hle : RingHom.ker π ≤ q.asIdeal :=
        Ideal.IsPrime.le_of_pow_le (n := n) (by rw [hn]; exact bot_le)
      exact hle
    obtain ⟨y, hy⟩ := (Set.ext_iff.mp hr x).mpr (Set.mem_univ x)
    exact ⟨y, hy⟩
  exact MorphismProperty.of_isPullback (P := @Surjective) hG.flip ‹_›

theorem isPullback_comp_of_factor {B B₁ : Type u} [CommRing B] [IsLocalRing B] [CommRing B₁] [Algebra B B₁]
    (hπ : Function.Surjective (algebraMap B B₁)) (hI : RingHom.ker (algebraMap B B₁) ≤ maximalIdeal B)
    {A₁ X₀ X Xκ : Scheme.{u}} (f₁ : A₁ ⟶ Spec (.of B₁))
    (f₀ : X₀ ⟶ Spec (.of B)) (g₀ : A₁ ⟶ X₀) (hg₀ : IsPullback g₀ f₁ f₀ (Spec.map (CommRingCat.ofHom (algebraMap B B₁))))
    (f : X ⟶ Spec (.of B)) (g : A₁ ⟶ X) (hg : IsPullback g f₁ f (Spec.map (CommRingCat.ofHom (algebraMap B B₁))))
    (bκ : Xκ ⟶ X₀) (pκ : Xκ ⟶ Spec (.of (ResidueField B)))
    (hκ : IsPullback bκ pκ f₀ (Spec.map (CommRingCat.ofHom (algebraMap B (ResidueField B)))))
    (jκ : Xκ ⟶ A₁) (hjκ : jκ ≫ g₀ = bκ) :
    IsPullback (jκ ≫ g) pκ f (Spec.map (CommRingCat.ofHom (residue B))) := by
  have hk : RingHom.ker (algebraMap B B₁) ≤ RingHom.ker (residue B) := by rwa [ker_residue]
  let ρ : B₁ →+* ResidueField B := RingHom.liftOfSurjective (algebraMap B B₁) hπ ⟨residue B, hk⟩
  have hρ : ρ.comp (algebraMap B B₁) = residue B := RingHom.liftOfRightInverse_comp _ _ _ _
  have e1 : Spec.map (CommRingCat.ofHom ρ) ≫ Spec.map (CommRingCat.ofHom (algebraMap B B₁)) =
      Spec.map (CommRingCat.ofHom (residue B)) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hρ]
  have e2 : Spec.map (CommRingCat.ofHom (algebraMap B (ResidueField B))) = Spec.map (CommRingCat.ofHom (residue B)) := rfl
  haveI : IsClosedImmersion (Spec.map (CommRingCat.ofHom (algebraMap B B₁))) :=
    IsClosedImmersion.spec_of_surjective _ hπ
  have hcomm : jκ ≫ f₁ = pκ ≫ Spec.map (CommRingCat.ofHom ρ) := by
    rw [← cancel_mono (Spec.map (CommRingCat.ofHom (algebraMap B B₁))), Category.assoc, Category.assoc, e1,
      ← hg₀.w, ← Category.assoc, hjκ, hκ.w, e2]
  have big : IsPullback (jκ ≫ g₀) pκ f₀ (Spec.map (CommRingCat.ofHom ρ) ≫ Spec.map (CommRingCat.ofHom (algebraMap B B₁))) := by
    rw [hjκ, e1, ← e2]; exact hκ
  have sqL : IsPullback jκ pκ f₁ (Spec.map (CommRingCat.ofHom ρ)) := IsPullback.of_right big hcomm hg₀
  have := IsPullback.paste_horiz sqL hg
  rwa [e1] at this

theorem res_app_algebraMap {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] {X P : Scheme.{u}}
    (q : X ⟶ Spec (.of R)) (y : P ⟶ Spec (.of S)) (b : P ⟶ X)
    (hsq : b ≫ q = y ≫ Spec.map (CommRingCat.ofHom (algebraMap R S)))
    {W : X.Opens} {W' : P.Opens} (hW' : W' ≤ b ⁻¹ᵁ W) (x : R) :
    letI := algebraOfHom q W; letI := algebraOfHom y W'
    (P.presheaf.map (homOfLE hW').op).hom ((b.app W).hom (algebraMap R Γ(X, W) x)) = algebraMap S Γ(P, W') (algebraMap R S x) := by
  letI := algebraOfHom q W; letI := algebraOfHom y W'
  rw [algebraMap_algebraOfHom, algebraMap_algebraOfHom]
  change (q.appLE ⊤ W le_top ≫ b.app W ≫ P.presheaf.map (homOfLE hW').op).hom ((Scheme.ΓSpecIso (.of R)).inv.hom x) =
    (y.appLE ⊤ W' le_top).hom ((Scheme.ΓSpecIso (.of S)).inv.hom (algebraMap R S x))
  have h1 : q.appLE ⊤ W le_top ≫ b.app W ≫ P.presheaf.map (homOfLE hW').op = (b ≫ q).appLE ⊤ W' le_top := by
    rw [Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_map, Scheme.Hom.appLE_comp_appLE]
  rw [h1, hsq, Scheme.Hom.comp_appLE, ← CommRingCat.comp_apply]
  have h2 : (Scheme.ΓSpecIso (.of R)).inv ≫ (Spec.map (CommRingCat.ofHom (algebraMap R S))).app ⊤ =
      CommRingCat.ofHom (algebraMap R S) ≫ (Scheme.ΓSpecIso (.of S)).inv :=
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap R S))).symm
  rw [← Category.assoc, h2]
  rfl

theorem exists_ringHom_tmul {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] {X P : Scheme.{u}}
    (q : X ⟶ Spec (.of R)) (y : P ⟶ Spec (.of S)) (b : P ⟶ X)
    (hsq : b ≫ q = y ≫ Spec.map (CommRingCat.ofHom (algebraMap R S)))
    {W : X.Opens} {W' : P.Opens} (hW' : W' ≤ b ⁻¹ᵁ W) :
    letI := algebraOfHom q W; letI := algebraOfHom y W'
    ∃ φ : S ⊗[R] Γ(X, W) →+* Γ(P, W'),
      (∀ c : Γ(X, W), φ ((1 : S) ⊗ₜ[R] c) = (P.presheaf.map (homOfLE hW').op).hom ((b.app W).hom c)) ∧
      (∀ a : S, φ (a ⊗ₜ[R] (1 : Γ(X, W))) = algebraMap S Γ(P, W') a) := by
  letI := algebraOfHom q W; letI := algebraOfHom y W'
  letI : Algebra R Γ(P, W') := ((algebraMap S Γ(P, W')).comp (algebraMap R S)).toAlgebra
  haveI : IsScalarTower R S Γ(P, W') := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let g : Γ(X, W) →ₐ[R] Γ(P, W') :=
    { toRingHom := (b.app W ≫ P.presheaf.map (homOfLE hW').op).hom
      commutes' := fun x => by
        show (P.presheaf.map (homOfLE hW').op).hom ((b.app W).hom (algebraMap R Γ(X, W) x)) = _
        rw [res_app_algebraMap q y b hsq hW' x]; rfl }
  refine ⟨(Algebra.TensorProduct.lift (Algebra.ofId S Γ(P, W')) g (fun _ _ => Commute.all _ _)).toRingHom, ?_, ?_⟩
  · intro c
    show Algebra.TensorProduct.lift (Algebra.ofId S Γ(P, W')) g _ ((1 : S) ⊗ₜ[R] c) = _
    rw [Algebra.TensorProduct.lift_tmul, map_one, one_mul]; rfl
  · intro a
    show Algebra.TensorProduct.lift (Algebra.ofId S Γ(P, W')) g _ (a ⊗ₜ[R] (1 : Γ(X, W))) = _
    rw [Algebra.TensorProduct.lift_tmul, map_one, mul_one]; rfl

theorem res_sigma_eq {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] {X P : Scheme.{u}}
    (q : X ⟶ Spec (.of R)) (y : P ⟶ Spec (.of S)) (b : P ⟶ X)
    {U W : X.Opens} (hWU : W ≤ U) {U' W' : P.Opens} (hU' : U' ≤ b ⁻¹ᵁ U) (hW' : W' ≤ b ⁻¹ᵁ W) (hWU' : W' ≤ U')
    (σ : letI := algebraOfHom q U; (S ⊗[R] Γ(X, U)) ≃+* Γ(P, U'))
    (hσ₁ : letI := algebraOfHom q U
      ∀ c : Γ(X, U), σ ((1 : S) ⊗ₜ[R] c) = (P.presheaf.map (homOfLE hU').op).hom ((b.app U).hom c))
    (hσ₂ : letI := algebraOfHom q U; letI := algebraOfHom y U'
      ∀ a : S, σ (a ⊗ₜ[R] (1 : Γ(X, U))) = algebraMap S Γ(P, U') a)
    (φ : letI := algebraOfHom q W; (S ⊗[R] Γ(X, W)) →+* Γ(P, W'))
    (hφ₁ : letI := algebraOfHom q W
      ∀ c : Γ(X, W), φ ((1 : S) ⊗ₜ[R] c) = (P.presheaf.map (homOfLE hW').op).hom ((b.app W).hom c))
    (hφ₂ : letI := algebraOfHom q W; letI := algebraOfHom y W'
      ∀ a : S, φ (a ⊗ₜ[R] (1 : Γ(X, W))) = algebraMap S Γ(P, W') a)
    (x : letI := algebraOfHom q U; S ⊗[R] Γ(X, U)) :
    letI := algebraOfHom q U; letI := algebraOfHom q W
    (P.presheaf.map (homOfLE hWU').op).hom (σ x) =
      φ (Algebra.TensorProduct.map (AlgHom.id S S) (restrictAlgHom q hWU) x) := by
  letI := algebraOfHom q U; letI := algebraOfHom q W
  letI := algebraOfHom y U'; letI := algebraOfHom y W'
  induction x using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero, map_zero, map_zero]
  | add x x' hx hx' => rw [map_add, map_add, hx, hx', map_add, map_add]
  | tmul a c =>
    have hsplit : ∀ (A : Type u) [CommRing A] [Algebra R A] (a : S) (c : A),
        a ⊗ₜ[R] c = (a ⊗ₜ[R] (1 : A)) * ((1 : S) ⊗ₜ[R] c) := by
      intro A _ _ a c
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, hsplit, map_mul, hσ₂, hσ₁, hsplit, map_mul, map_mul, hφ₂, hφ₁]
    congr 1
    · change (y.appLE ⊤ U' le_top ≫ P.presheaf.map (homOfLE hWU').op).hom _ = (y.appLE ⊤ W' le_top).hom _
      rw [Scheme.Hom.appLE_map]
    · change (b.app U ≫ P.presheaf.map (homOfLE hU').op ≫ P.presheaf.map (homOfLE hWU').op).hom c =
        (X.presheaf.map (homOfLE hWU).op ≫ b.app W ≫ P.presheaf.map (homOfLE hW').op).hom c
      rw [← Category.assoc (X.presheaf.map _), Scheme.Hom.naturality, Category.assoc, ← Functor.map_comp, ← Functor.map_comp]
      rfl

theorem specMap_isoSpec_inv {X : Scheme.{u}} {U V : X.Opens} (hU : IsAffineOpen U) (hV : IsAffineOpen V) (h : V ≤ U) :
    Spec.map (X.presheaf.map (homOfLE h).op) ≫ hU.isoSpec.inv = hV.isoSpec.inv ≫ X.homOfLE h := by
  rw [← cancel_mono U.ι, Category.assoc, Category.assoc, Scheme.homOfLE_ι, IsAffineOpen.isoSpec_inv_ι,
    IsAffineOpen.isoSpec_inv_ι]
  exact IsAffineOpen.map_fromSpec _ _ _

theorem exists_restrict_algHom {B : Type u} [CommRing B] {X : Scheme.{u}} (f : X ⟶ Spec (.of B))
    {U W : X.Opens} (hW : IsAffineOpen W) (hWU : W ≤ U)
    (τ : (↑U : Scheme.{u}) ⟶ ↑U) (hτf : τ ≫ U.ι ≫ f = U.ι ≫ f) (hτid : ∀ y : ↑U, τ y = y) :
    letI := algebraOfHom f W
    ∃ (θ : (↑W : Scheme.{u}) ⟶ ↑W) (h : Γ(X, W) →ₐ[B] Γ(X, W)),
      θ ≫ W.ι = X.homOfLE hWU ≫ τ ≫ U.ι ∧
      hW.isoSpec.inv ≫ θ = Spec.map (CommRingCat.ofHom h.toRingHom) ≫ hW.isoSpec.inv := by
  letI := algebraOfHom f W
  have hrange : Set.range ⇑(X.homOfLE hWU ≫ τ ≫ U.ι) ⊆ Set.range ⇑W.ι := by
    rintro _ ⟨y, rfl⟩
    refine ⟨y, ?_⟩
    rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, hτid, ← Scheme.Hom.comp_apply, Scheme.homOfLE_ι]
  let θ : (↑W : Scheme.{u}) ⟶ ↑W := IsOpenImmersion.lift W.ι (X.homOfLE hWU ≫ τ ≫ U.ι) hrange
  have hθ : θ ≫ W.ι = X.homOfLE hWU ≫ τ ≫ U.ι := IsOpenImmersion.lift_fac _ _ _

  let m : Spec (.of Γ(X, W)) ⟶ Spec (.of Γ(X, W)) := hW.isoSpec.inv ≫ θ ≫ hW.isoSpec.hom
  let h₀ : CommRingCat.of Γ(X, W) ⟶ CommRingCat.of Γ(X, W) := Spec.preimage m
  have hm : Spec.map h₀ = m := Spec.map_preimage m
  have hfS : hW.fromSpec ≫ f = Spec.map (CommRingCat.ofHom (algebraMap B Γ(X, W))) := by
    have h := IsAffineOpen.SpecMap_appLE_fromSpec f (isAffineOpen_top (Spec (.of B))) hW
      (show W ≤ f ⁻¹ᵁ ⊤ by simp)
    rw [← h, IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv, ← Spec.map_comp]
    rfl
  have hover : m ≫ Spec.map (CommRingCat.ofHom (algebraMap B Γ(X, W))) =
      Spec.map (CommRingCat.ofHom (algebraMap B Γ(X, W))) := by
    have hθ' : θ ≫ W.ι ≫ f = X.homOfLE hWU ≫ τ ≫ U.ι ≫ f := by
      rw [← Category.assoc, hθ]; simp only [Category.assoc]
    rw [← hfS, ← IsAffineOpen.isoSpec_inv_ι]
    simp only [m, Category.assoc, Iso.hom_inv_id_assoc]
    rw [hθ', hτf, Scheme.homOfLE_ι_assoc]
  have hcomm : ∀ b : B, h₀.hom (algebraMap B Γ(X, W) b) = algebraMap B Γ(X, W) b := by
    intro b
    have h2 : CommRingCat.ofHom (algebraMap B Γ(X, W)) ≫ h₀ = CommRingCat.ofHom (algebraMap B Γ(X, W)) := by
      apply Spec.map_injective
      rw [Spec.map_comp, hm, hover]
    exact congrArg (fun φ : CommRingCat.of B ⟶ CommRingCat.of Γ(X, W) => φ.hom b) h2
  let h : Γ(X, W) →ₐ[B] Γ(X, W) :=
    { toRingHom := h₀.hom, commutes' := hcomm }
  refine ⟨θ, h, hθ, ?_⟩
  have : CommRingCat.ofHom h.toRingHom = h₀ := rfl
  rw [this, hm, Category.assoc, Category.assoc, Iso.hom_inv_id, Category.comp_id]

end P2mTwistedO2

end

open P2mTwistedO2 AlgebraicGeometry.SmallExtension

set_option maxHeartbeats 1600000 in

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
    (c : letI := algebraOfHom (pullback.snd D₀.f (specMap B (ResidueField B))) ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)
      ↥(Algebra.PointDerivations (ResidueField B) Γ((pullback D₀.f (specMap B (ResidueField B))), ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)) (((𝒰.baseChange D₀.f (ResidueField B)).U i₀).topIso.inv ≫ e₁.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of (ResidueField B))).hom).hom
          (Module.Dual (ResidueField B) V →ₗ[(ResidueField B)] (OModulePresheaf.unit (pullback.snd D₀.f (specMap B (ResidueField B)))).cochain (𝒰.baseChange D₀.f (ResidueField B)) 1)))
    (hc : letI := algebraOfHom (pullback.snd D₀.f (specMap B (ResidueField B))) ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)
      ∀ (a : Γ((pullback D₀.f (specMap B (ResidueField B))), ((𝒰.baseChange D₀.f (ResidueField B)).U i₀))) (ξ : Module.Dual (ResidueField B) V),
      (c : Γ((pullback D₀.f (specMap B (ResidueField B))), ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)) →ₗ[(ResidueField B)] (Module.Dual (ResidueField B) V →ₗ[(ResidueField B)] (OModulePresheaf.unit (pullback.snd D₀.f (specMap B (ResidueField B)))).cochain (𝒰.baseChange D₀.f (ResidueField B)) 1)) a ξ
        ∈ LinearMap.ker ((OModulePresheaf.unit (pullback.snd D₀.f (specMap B (ResidueField B)))).d (𝒰.baseChange D₀.f (ResidueField B)) 1))

    (τ : ∀ s : 𝒰.Idx 1, ((↑(𝒰.inter s) : Scheme.{0}) ≅ ↑(𝒰.inter s)))
    (D : BareDeformation f₁ L₁ B) (hD : D₀.IsRegluingBy 𝒰 τ D)
    (hτ : ∀ s : 𝒰.Idx 1,
        letI := algebraOfHom D₀.f (𝒰.inter s)
        letI := algebraOfHom (pullback.snd D₀.f (specMap B (ResidueField B))) ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)
        ∃ cs : Γ((pullback D₀.f (specMap B (ResidueField B))), ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)) → (Module.Dual (ResidueField B) V →ₗ[(ResidueField B)] ((ResidueField B) ⊗[B] Γ(D₀.A, 𝒰.inter s))),
          AlgebraicGeometry.SmallExtension.IsTangentCoordsOfPairAt (RingHom.ker (algebraMap B B₁)) V ι Γ(D₀.A, 𝒰.inter s)
            ((Scheme.OrderedAffineCover.isAffineOpen_inter D₀.f 𝒰 s).fromSpec)
            ((Scheme.OrderedAffineCover.isAffineOpen_inter D₀.f 𝒰 s).isoSpec.inv ≫ (τ s).hom ≫ (𝒰.inter s).ι)
            (pullback.snd D₀.f (specMap B (ResidueField B))) (RelativeGroupLaw.baseChange (specMap B (ResidueField B)) D₀.L) (pullback.fst D₀.f (specMap B (ResidueField B))) ((𝒰.baseChange D₀.f (ResidueField B)).U i₀) cs ∧
          ∀ (a : Γ((pullback D₀.f (specMap B (ResidueField B))), ((𝒰.baseChange D₀.f (ResidueField B)).U i₀))) (ξ : Module.Dual (ResidueField B) V),
            σ s (cs a ξ) = (c : Γ((pullback D₀.f (specMap B (ResidueField B))), ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)) →ₗ[(ResidueField B)] (Module.Dual (ResidueField B) V →ₗ[(ResidueField B)] (OModulePresheaf.unit (pullback.snd D₀.f (specMap B (ResidueField B)))).cochain (𝒰.baseChange D₀.f (ResidueField B)) 1)) a ξ s)

    (φ₁ : A₁ ⟶ A₁) (hφ₁ : φ₁ ≫ f₁ = f₁)
    (jκ : (pullback D₀.f (specMap B (ResidueField B))) ⟶ A₁) (hjκ : jκ ≫ D₀.g = (pullback.fst D₀.f (specMap B (ResidueField B))))
    (ψ : (pullback D₀.f (specMap B (ResidueField B))) ⟶ (pullback D₀.f (specMap B (ResidueField B)))) (hψ : ψ ≫ (pullback.snd D₀.f (specMap B (ResidueField B))) = (pullback.snd D₀.f (specMap B (ResidueField B))))
    (hψ₁ : ψ ≫ jκ = jκ ≫ φ₁)

    (mp : ∀ i : 𝒰.ι, (↑(𝒰.U i) : Scheme.{0}) ⟶ D.A)
    (hmpf : ∀ i, mp i ≫ D.f = (𝒰.U i).ι ≫ D₀.f)
    (hmpμ : ∀ i, morphismRestrict D₀.g (𝒰.U i) ≫ mp i = (D₀.g ⁻¹ᵁ (𝒰.U i)).ι ≫ φ₁ ≫ D.g)
    (c' : letI := algebraOfHom (pullback.snd D₀.f (specMap B (ResidueField B))) ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)
      ↥(Algebra.PointDerivations (ResidueField B) Γ((pullback D₀.f (specMap B (ResidueField B))), ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)) ((((𝒰.baseChange D₀.f (ResidueField B)).U i₀).topIso.inv ≫ e₁.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of (ResidueField B))).hom).hom) (Module.Dual (ResidueField B) V →ₗ[(ResidueField B)] ((OModulePresheaf.unit (pullback.snd D₀.f (specMap B (ResidueField B)))).cochain (𝒰.baseChange D₀.f (ResidueField B)) 1))))
    (hc' : letI := algebraOfHom (pullback.snd D₀.f (specMap B (ResidueField B))) ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)
      ∀ s : 𝒰.Idx 1,
        letI := algebraOfHom D₀.f (𝒰.inter s)
        ∃ cs : Γ((pullback D₀.f (specMap B (ResidueField B))), ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)) → (Module.Dual (ResidueField B) V →ₗ[(ResidueField B)] ((ResidueField B) ⊗[B] Γ(D₀.A, 𝒰.inter s))),
          AlgebraicGeometry.SmallExtension.IsTangentCoordsOfPairAt (RingHom.ker (algebraMap B B₁)) V ι Γ(D₀.A, 𝒰.inter s)
            ((Scheme.OrderedAffineCover.isAffineOpen_inter D₀.f 𝒰 s).isoSpec.inv ≫ D₀.A.homOfLE (𝒰.inter_le s 0) ≫ mp (s.1 0))
            ((Scheme.OrderedAffineCover.isAffineOpen_inter D₀.f 𝒰 s).isoSpec.inv ≫ (τ s).hom ≫ D₀.A.homOfLE (𝒰.inter_le s 1) ≫ mp (s.1 1))
            (pullback.snd D₀.f (specMap B (ResidueField B))) (RelativeGroupLaw.baseChange (specMap B (ResidueField B)) D₀.L) (jκ ≫ D.g) ((𝒰.baseChange D₀.f (ResidueField B)).U i₀) cs ∧
          ∀ (a : Γ((pullback D₀.f (specMap B (ResidueField B))), ((𝒰.baseChange D₀.f (ResidueField B)).U i₀))) (ξ : Module.Dual (ResidueField B) V), σ s (cs a ξ) = c'.1 a ξ s) :
    letI := algebraOfHom (pullback.snd D₀.f (specMap B (ResidueField B))) ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)
    ∀ (a : Γ((pullback D₀.f (specMap B (ResidueField B))), ((𝒰.baseChange D₀.f (ResidueField B)).U i₀))) (ξ : Module.Dual (ResidueField B) V),
      (OModulePresheaf.unit (pullback.snd D₀.f (specMap B (ResidueField B)))).d (𝒰.baseChange D₀.f (ResidueField B)) 1 (c'.1 a ξ) = 0 := by

  classical
  letI := algebraOfHom (pullback.snd D₀.f (specMap B (ResidueField B))) ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)
  intro a ξ
  obtain ⟨hτf, hτg, ιD, hιopen, hιf, hιsurj, hιg, hιglue⟩ := hD

  haveI : Smooth D₀.f := D₀.bundle.smooth
  haveI hflat0 : Flat D₀.f := inferInstance
  haveI hsurj : Surjective D₀.g :=
    surjective_of_isPullback_of_surjective_of_isNilpotent (algebraMap B B₁) hπ hker D₀.f f₁ D₀.g D₀.cart
  have hsq0 : IsPullback (pullback.fst D₀.f (specMap B (ResidueField B))) (pullback.snd D₀.f (specMap B (ResidueField B)))
      D₀.f (Spec.map (CommRingCat.ofHom (algebraMap B (ResidueField B)))) := IsPullback.of_hasPullback _ _
  have hak : IsPullback (jκ ≫ D.g) (pullback.snd D₀.f (specMap B (ResidueField B))) D.f
      (Spec.map (CommRingCat.ofHom (residue B))) :=
    isPullback_comp_of_factor hπ hI f₁ D₀.f D₀.g D₀.cart D.f D.g D.cart _ _ hsq0 jκ hjκ
  haveI : IsAffineHom (pullback.fst D₀.f (specMap B (ResidueField B))) := isAffineHom_fst D₀.f (ResidueField B)
  have hUe : IsAffineOpen ((𝒰.baseChange D₀.f (ResidueField B)).U i₀) :=
    (𝒰.isAffineOpen i₀).preimage (pullback.fst D₀.f (specMap B (ResidueField B)))

  funext t
  rw [OModulePresheaf.d_apply, Pi.zero_apply]
  letI := algebraOfHom D₀.f (𝒰.inter t)
  have hUt : IsAffineOpen (𝒰.inter t) := 𝒰.isAffineOpen_inter D₀.f t
  haveI : Module.Flat B Γ(D₀.A, 𝒰.inter t) := flat_sections D₀.f hUt

  obtain ⟨φ, hφ₁, hφ₂⟩ := exists_ringHom_tmul D₀.f (pullback.snd D₀.f (specMap B (ResidueField B)))
    (pullback.fst D₀.f (specMap B (ResidueField B))) hsq0.w
    ((𝒰.baseChange_inter_le D₀.f (ResidueField B) t))

  have hA : ∀ x : Fin 3, (hUt.isoSpec.inv ≫ D₀.A.homOfLE (𝒰.inter_le t x) ≫ mp (t.1 x)) ≫ D.f = Spec.map (CommRingCat.ofHom (algebraMap B Γ(D₀.A, 𝒰.inter t))) := by
    intro x
    simp only [Category.assoc]
    rw [hmpf, Scheme.homOfLE_ι_assoc, ← fromSpec_comp_eq D₀.f hUt, IsAffineOpen.isoSpec_inv_ι_assoc]
  have hψalg : ∀ ψ : Γ(D₀.A, 𝒰.inter t) →ₐ[B] Γ(D₀.A, 𝒰.inter t),
      Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ Spec.map (CommRingCat.ofHom (algebraMap B Γ(D₀.A, 𝒰.inter t))) =
      Spec.map (CommRingCat.ofHom (algebraMap B Γ(D₀.A, 𝒰.inter t))) := fun ψ => by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, AlgHom.toRingHom_eq_coe, AlgHom.comp_algebraMap]

  have hface : ∀ (r : Fin 3) (i j : Fin 3) (hi : r.succAbove 0 = i) (hj : r.succAbove 1 = j),
      ∃ (h : Γ(D₀.A, 𝒰.inter t) →ₐ[B] Γ(D₀.A, 𝒰.inter t))
      (Dr : Γ((pullback D₀.f (specMap B (ResidueField B))), ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)) →
        (Module.Dual (ResidueField B) V →ₗ[ResidueField B] (ResidueField B ⊗[B] Γ(D₀.A, 𝒰.inter t)))),
      (∀ c, Ideal.Quotient.mk ((RingHom.ker (algebraMap B B₁)).map (algebraMap B Γ(D₀.A, 𝒰.inter t))) (h c) =
        Ideal.Quotient.mk ((RingHom.ker (algebraMap B B₁)).map (algebraMap B Γ(D₀.A, 𝒰.inter t))) c) ∧
      IsTangentCoordsOfPairAt (RingHom.ker (algebraMap B B₁)) V ι Γ(D₀.A, 𝒰.inter t)
        ((hUt.isoSpec.inv ≫ D₀.A.homOfLE (𝒰.inter_le t i) ≫ mp (t.1 i))) (Spec.map (CommRingCat.ofHom h.toRingHom) ≫ (hUt.isoSpec.inv ≫ D₀.A.homOfLE (𝒰.inter_le t j) ≫ mp (t.1 j)))
        (pullback.snd D₀.f (specMap B (ResidueField B))) (RelativeGroupLaw.baseChange (specMap B (ResidueField B)) D₀.L)
        (jκ ≫ D.g) ((𝒰.baseChange D₀.f (ResidueField B)).U i₀) Dr ∧
      (hUt.isoSpec.inv ≫ D₀.A.homOfLE (𝒰.inter_le t i) ≫ ιD (t.1 i)) = Spec.map (CommRingCat.ofHom h.toRingHom) ≫ (hUt.isoSpec.inv ≫ D₀.A.homOfLE (𝒰.inter_le t j) ≫ ιD (t.1 j)) ∧
      ((pullback D₀.f (specMap B (ResidueField B))).presheaf.map
          (homOfLE ((𝒰.baseChange D₀.f (ResidueField B)).inter_le_inter_face t r)).op).hom (c'.1 a ξ (𝒰.face t r)) =
        φ (Dr a ξ) := by
    intro r i j hi hj
    subst hi; subst hj
    have hts : 𝒰.inter t ≤ 𝒰.inter (𝒰.face t r) := 𝒰.inter_le_inter_face t r
    have hUs : IsAffineOpen (𝒰.inter (𝒰.face t r)) := 𝒰.isAffineOpen_inter D₀.f _
    letI := algebraOfHom D₀.f (𝒰.inter (𝒰.face t r))

    obtain ⟨θ, h, hθ, hh⟩ := exists_restrict_algHom D₀.f hUt hts (τ (𝒰.face t r)).hom (hτf _)
      (apply_eq_self_of_morphismRestrict_comp_eq D₀.g _ _ (hτg _))

    have hθx : ∀ {Z : Scheme} (x : 𝒰.ι) (hsx : 𝒰.inter (𝒰.face t r) ≤ 𝒰.U x) (htx : 𝒰.inter t ≤ 𝒰.U x)
        (m : (↑(𝒰.U x) : Scheme) ⟶ Z),
        D₀.A.homOfLE hts ≫ (τ (𝒰.face t r)).hom ≫ D₀.A.homOfLE hsx ≫ m = θ ≫ D₀.A.homOfLE htx ≫ m := by
      intro Z x hsx htx m
      have e : D₀.A.homOfLE hts ≫ (τ (𝒰.face t r)).hom ≫ D₀.A.homOfLE hsx = θ ≫ D₀.A.homOfLE htx := by
        rw [← cancel_mono (𝒰.U x).ι]
        simp only [Category.assoc, Scheme.homOfLE_ι]
        rw [hθ]
      rw [← Category.assoc θ, ← e]; simp only [Category.assoc]

    have hgθ : (D₀.g ∣_ 𝒰.inter t) ≫ θ = D₀.g ∣_ 𝒰.inter t := by
      rw [← cancel_mono (𝒰.inter t).ι, Category.assoc, hθ]
      have e : (D₀.g ∣_ 𝒰.inter t) ≫ D₀.A.homOfLE hts =
          A₁.homOfLE (D₀.g.preimage_mono hts) ≫ (D₀.g ∣_ 𝒰.inter (𝒰.face t r)) := by
        rw [← cancel_mono (𝒰.inter (𝒰.face t r)).ι, Category.assoc, Scheme.homOfLE_ι, morphismRestrict_ι, Category.assoc,
          morphismRestrict_ι, Scheme.homOfLE_ι_assoc]
      rw [← Category.assoc, e, Category.assoc, ← Category.assoc (D₀.g ∣_ 𝒰.inter (𝒰.face t r)), hτg, morphismRestrict_ι,
        Scheme.homOfLE_ι_assoc, morphismRestrict_ι]
    have hhmod : ∀ c, Ideal.Quotient.mk ((RingHom.ker (algebraMap B B₁)).map (algebraMap B Γ(D₀.A, 𝒰.inter t))) (h c) =
        Ideal.Quotient.mk ((RingHom.ker (algebraMap B B₁)).map (algebraMap B Γ(D₀.A, 𝒰.inter t))) c := by
      obtain ⟨-, ε, hε⟩ := AlgebraicGeometry.IsPullback.exists_iso_Spec_quotient_comp_morphismRestrict_eq
        (algebraMap B B₁) hπ hker D₀.f f₁ D₀.g D₀.cart (𝒰.inter t) hUt
      have e1 : θ ≫ hUt.isoSpec.hom = hUt.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom h.toRingHom) := by
        rw [← cancel_epi hUt.isoSpec.inv, ← Category.assoc, hh]
        simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id, Iso.inv_hom_id_assoc]
      have e2 : Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk ((RingHom.ker (algebraMap B B₁)).map
            (algebraMap B Γ(D₀.A, 𝒰.inter t))))) ≫ Spec.map (CommRingCat.ofHom h.toRingHom) =
          Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk ((RingHom.ker (algebraMap B B₁)).map
            (algebraMap B Γ(D₀.A, 𝒰.inter t))))) := by
        rw [← hε]; simp only [Category.assoc]; rw [← e1, ← Category.assoc (D₀.g ∣_ 𝒰.inter t), hgθ]
      have e3 : CommRingCat.ofHom h.toRingHom ≫ CommRingCat.ofHom (Ideal.Quotient.mk ((RingHom.ker (algebraMap B B₁)).map
            (algebraMap B Γ(D₀.A, 𝒰.inter t)))) =
          CommRingCat.ofHom (Ideal.Quotient.mk ((RingHom.ker (algebraMap B B₁)).map (algebraMap B Γ(D₀.A, 𝒰.inter t)))) := by
        apply Spec.map_injective; rw [Spec.map_comp, e2]
      intro c
      exact congrArg (fun φ' : CommRingCat.of Γ(D₀.A, 𝒰.inter t) ⟶ _ => φ'.hom c) e3

    obtain ⟨cs, hcs, hcsσ⟩ := hc' (𝒰.face t r)
    have hR := isTangentCoordsOfPairAt_comp_of_flat (RingHom.ker (algebraMap B B₁)) hI hsmall V ι hι hιI
      Γ(D₀.A, 𝒰.inter (𝒰.face t r)) Γ(D₀.A, 𝒰.inter t) (restrictAlgHom D₀.f hts) _ _ _ _ _ _ _ hcs
    have hρ : Spec.map (CommRingCat.ofHom (restrictAlgHom D₀.f hts).toRingHom) ≫ hUs.isoSpec.inv =
        hUt.isoSpec.inv ≫ D₀.A.homOfLE hts := specMap_isoSpec_inv hUs hUt hts
    have e4 : Spec.map (CommRingCat.ofHom (restrictAlgHom D₀.f hts).toRingHom) ≫
        ((Scheme.OrderedAffineCover.isAffineOpen_inter D₀.f 𝒰 (𝒰.face t r)).isoSpec.inv ≫
          D₀.A.homOfLE (𝒰.inter_le (𝒰.face t r) 0) ≫ mp ((𝒰.face t r).1 0)) =
        hUt.isoSpec.inv ≫ D₀.A.homOfLE (𝒰.inter_le t (r.succAbove 0)) ≫ mp (t.1 (r.succAbove 0)) := by
      rw [← Category.assoc, hρ, Category.assoc, Scheme.homOfLE_homOfLE_assoc]
      rfl
    have e5 : Spec.map (CommRingCat.ofHom (restrictAlgHom D₀.f hts).toRingHom) ≫
        ((Scheme.OrderedAffineCover.isAffineOpen_inter D₀.f 𝒰 (𝒰.face t r)).isoSpec.inv ≫ (τ (𝒰.face t r)).hom ≫
          D₀.A.homOfLE (𝒰.inter_le (𝒰.face t r) 1) ≫ mp ((𝒰.face t r).1 1)) =
        Spec.map (CommRingCat.ofHom h.toRingHom) ≫
          hUt.isoSpec.inv ≫ D₀.A.homOfLE (𝒰.inter_le t (r.succAbove 1)) ≫ mp (t.1 (r.succAbove 1)) := by
      rw [← Category.assoc, hρ, Category.assoc, hθx ((𝒰.face t r).1 1) _ (𝒰.inter_le t (r.succAbove 1)),
        ← Category.assoc, hh, Category.assoc]
      rfl
    rw [e4, e5] at hR

    have hB : hUt.isoSpec.inv ≫ D₀.A.homOfLE (𝒰.inter_le t (r.succAbove 0)) ≫ ιD (t.1 (r.succAbove 0)) =
        Spec.map (CommRingCat.ofHom h.toRingHom) ≫
          hUt.isoSpec.inv ≫ D₀.A.homOfLE (𝒰.inter_le t (r.succAbove 1)) ≫ ιD (t.1 (r.succAbove 1)) := by
      have hg : hUt.isoSpec.inv ≫ D₀.A.homOfLE hts ≫ D₀.A.homOfLE (𝒰.inter_le (𝒰.face t r) 0) ≫ ιD ((𝒰.face t r).1 0) =
          hUt.isoSpec.inv ≫ D₀.A.homOfLE hts ≫ (τ (𝒰.face t r)).hom ≫ D₀.A.homOfLE (𝒰.inter_le (𝒰.face t r) 1) ≫
            ιD ((𝒰.face t r).1 1) := by
        rw [hιglue (𝒰.face t r)]
      rw [Scheme.homOfLE_homOfLE_assoc, hθx ((𝒰.face t r).1 1) _ (𝒰.inter_le t (r.succAbove 1)), ← Category.assoc _ θ,
        hh, Category.assoc] at hg
      exact hg

    refine ⟨h, fun a' => (Algebra.TensorProduct.map (AlgHom.id (ResidueField B) (ResidueField B))
      (restrictAlgHom D₀.f hts)).toLinearMap ∘ₗ cs a', hhmod, hR, hB, ?_⟩
    rw [← hcsσ a ξ, LinearMap.comp_apply, AlgHom.toLinearMap_apply]
    exact res_sigma_eq D₀.f (pullback.snd D₀.f (specMap B (ResidueField B))) (pullback.fst D₀.f (specMap B (ResidueField B)))
      hts (𝒰.baseChange_inter_le D₀.f (ResidueField B) (𝒰.face t r)) (𝒰.baseChange_inter_le D₀.f (ResidueField B) t)
      ((𝒰.baseChange D₀.f (ResidueField B)).inter_le_inter_face t r) (σ _) (hσ₁ _) (hσ₂ _) φ hφ₁ hφ₂ (cs a ξ)

  obtain ⟨h0, D0, hh0, hD0, hB0, hT0⟩ := hface 0 1 2 (by decide) (by decide)
  obtain ⟨h1, D1, hh1, hD1, hB1, hT1⟩ := hface 1 0 2 (by decide) (by decide)
  obtain ⟨h2, D2, hh2, hD2, hB2, hT2⟩ := hface 2 0 1 (by decide) (by decide)

  have hmono : Mono ((hUt.isoSpec.inv ≫ D₀.A.homOfLE (𝒰.inter_le t 2) ≫ ιD (t.1 2))) := by
    haveI := hιopen (t.1 2)
    infer_instance
  have hcoc : Spec.map (CommRingCat.ofHom h1.toRingHom) ≫ (hUt.isoSpec.inv ≫ D₀.A.homOfLE (𝒰.inter_le t 2) ≫ mp (t.1 2)) =
      Spec.map (CommRingCat.ofHom h2.toRingHom) ≫ Spec.map (CommRingCat.ofHom h0.toRingHom) ≫ (hUt.isoSpec.inv ≫ D₀.A.homOfLE (𝒰.inter_le t 2) ≫ mp (t.1 2)) := by
    have e : Spec.map (CommRingCat.ofHom h1.toRingHom) ≫ (hUt.isoSpec.inv ≫ D₀.A.homOfLE (𝒰.inter_le t 2) ≫ ιD (t.1 2)) =
        Spec.map (CommRingCat.ofHom h2.toRingHom) ≫ Spec.map (CommRingCat.ofHom h0.toRingHom) ≫ (hUt.isoSpec.inv ≫ D₀.A.homOfLE (𝒰.inter_le t 2) ≫ ιD (t.1 2)) := by
      rw [← hB1, hB2, hB0]
    have e' : Spec.map (CommRingCat.ofHom h1.toRingHom) =
        Spec.map (CommRingCat.ofHom h2.toRingHom) ≫ Spec.map (CommRingCat.ofHom h0.toRingHom) := by
      rw [← cancel_mono ((hUt.isoSpec.inv ≫ D₀.A.homOfLE (𝒰.inter_le t 2) ≫ ιD (t.1 2))), Category.assoc]; exact e
    rw [e', Category.assoc]

  have hmap : ∀ (ψ : Γ(D₀.A, 𝒰.inter t) →ₐ[B] Γ(D₀.A, 𝒰.inter t)),
      (∀ c, Ideal.Quotient.mk ((RingHom.ker (algebraMap B B₁)).map (algebraMap B Γ(D₀.A, 𝒰.inter t))) (ψ c) =
        Ideal.Quotient.mk ((RingHom.ker (algebraMap B B₁)).map (algebraMap B Γ(D₀.A, 𝒰.inter t))) c) →
      ∀ cc : Γ((pullback D₀.f (specMap B (ResidueField B))), ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)) →
        (Module.Dual (ResidueField B) V →ₗ[ResidueField B] (ResidueField B ⊗[B] Γ(D₀.A, 𝒰.inter t))),
      (fun a' => (Algebra.TensorProduct.map (AlgHom.id (ResidueField B) (ResidueField B)) ψ).toLinearMap ∘ₗ cc a') = cc :=
    fun ψ hψ cc => funext fun a' => LinearMap.ext fun ξ' => by
      rw [LinearMap.comp_apply, AlgHom.toLinearMap_apply, map_id_apply_eq_self _ hI _ ψ hψ]
  have hD0' : IsTangentCoordsOfPairAt (RingHom.ker (algebraMap B B₁)) V ι Γ(D₀.A, 𝒰.inter t)
      (Spec.map (CommRingCat.ofHom h2.toRingHom) ≫ (hUt.isoSpec.inv ≫ D₀.A.homOfLE (𝒰.inter_le t 1) ≫ mp (t.1 1))) (Spec.map (CommRingCat.ofHom h1.toRingHom) ≫ (hUt.isoSpec.inv ≫ D₀.A.homOfLE (𝒰.inter_le t 2) ≫ mp (t.1 2)))
      (pullback.snd D₀.f (specMap B (ResidueField B))) (RelativeGroupLaw.baseChange (specMap B (ResidueField B)) D₀.L)
      (jκ ≫ D.g) ((𝒰.baseChange D₀.f (ResidueField B)).U i₀) D0 := by
    have h := isTangentCoordsOfPairAt_comp_of_flat (RingHom.ker (algebraMap B B₁)) hI hsmall V ι hι hιI
      Γ(D₀.A, 𝒰.inter t) Γ(D₀.A, 𝒰.inter t) h2 _ _ _ _ _ _ _ hD0
    rw [hmap h2 hh2] at h
    rw [hcoc]
    exact h

  have hadd : D1 = D2 + D0 :=
    isTangentCoordsOfPairAt_add (RingHom.ker (algebraMap B B₁)) hI hsmall V ι hι hιI Γ(D₀.A, 𝒰.inter t) D.f
      ((hUt.isoSpec.inv ≫ D₀.A.homOfLE (𝒰.inter_le t 0) ≫ mp (t.1 0))) (Spec.map (CommRingCat.ofHom h2.toRingHom) ≫ (hUt.isoSpec.inv ≫ D₀.A.homOfLE (𝒰.inter_le t 1) ≫ mp (t.1 1))) (Spec.map (CommRingCat.ofHom h1.toRingHom) ≫ (hUt.isoSpec.inv ≫ D₀.A.homOfLE (𝒰.inter_le t 2) ≫ mp (t.1 2)))
      (hA 0) (by rw [Category.assoc, hA, hψalg]) (by rw [Category.assoc, hA, hψalg])
      (specMap_mk_comp_eq_of_isTangentCoordsOfPairAt _ V ι _ _ _ _ _ _ _ _ hD2)
      (specMap_mk_comp_eq_of_isTangentCoordsOfPairAt _ V ι _ _ _ _ _ _ _ _ hD0')
      _ _ (jκ ≫ D.g) hak _ hUe e₁ he₁ D2 D0 D1 hD2 hD0' hD1

  show ∑ r : Fin 3, ((-1 : ℤ) ^ (r : ℕ)) •
      ((pullback D₀.f (specMap B (ResidueField B))).presheaf.map
          (homOfLE ((𝒰.baseChange D₀.f (ResidueField B)).inter_le_inter_face t r)).op).hom (c'.1 a ξ (𝒰.face t r)) = 0
  rw [Fin.sum_univ_three, hT0, hT1, hT2, hadd]
  have e3 : φ ((D2 + D0) a ξ) = φ (D2 a ξ) + φ (D0 a ξ) := by
    rw [Pi.add_apply, LinearMap.add_apply, map_add]
  simp only [Fin.val_zero, Fin.val_one, Fin.val_two, pow_zero, pow_one, e3, zsmul_eq_mul, Int.cast_pow, Int.cast_neg,
    Int.cast_one]
  ring

end S_GoodReductionJacobian_BareDeformation_d_twisted_hom_obstruction_cochain_eq_zero_of_isRegluingBy_bare
end P2MW
export P2MW.S_GoodReductionJacobian_BareDeformation_d_twisted_hom_obstruction_cochain_eq_zero_of_isRegluingBy_bare (solution)
