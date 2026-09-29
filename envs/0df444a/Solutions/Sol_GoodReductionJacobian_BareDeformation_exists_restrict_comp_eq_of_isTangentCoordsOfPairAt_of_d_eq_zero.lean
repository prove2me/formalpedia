-- Prove2me | solution 1 for GoodReductionJacobian.BareDeformation.exists_restrict_comp_eq_of_isTangentCoordsOfPairAt_of_d_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/956b88f5-cdcc-5ff6-83b4-a6a2ab9e8478

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
import Theorems.Thm_AlgebraicGeometry_SmallExtension_isTangentCoordsOfPairAt_comp_of_flat
import Theorems.Thm_AlgebraicGeometry_SmallExtension_isTangentCoordsOfPairAt_add
import Theorems.Thm_AlgebraicGeometry_SmallExtension_eq_of_isTangentCoordsOfPairAt_of_isTangentCoordsOfPairAt
import Theorems.Thm_AlgebraicGeometry_SmallExtension_exists_isTangentCoordsOfPairAt
import Theorems.Thm_AlgebraicGeometry_Scheme_OrderedAffineCover_exists_ringEquiv_tensor_sections_baseChange_inter
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_BareDeformation_exists_restrict_comp_eq_of_isTangentCoordsOfPairAt_of_d_eq_zero

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM CerednikDrinfeld.SpecialFormal IsLocalRing AlgebraicGeometry.Scheme.TwoAffineOpenCover"

open scoped Quaternion TensorProduct NumberField
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
open AlgebraicGeometry.SmallExtension

namespace P2mWs2RG2

section Restrict

variable {X W : Scheme.{0}} (U : X.Opens) (τ : (U : Scheme.{0}) ≅ (U : Scheme.{0}))
  (h : W ⟶ (U : Scheme.{0})) (hsurj : Function.Surjective h.base) (hτ : h ≫ τ.hom = h)

include hsurj hτ in
theorem base_apply_eq (x : (U : Scheme.{0})) : τ.hom.base x = x := by
  obtain ⟨y, rfl⟩ := hsurj x
  rw [← Scheme.Hom.comp_apply, hτ]

include hsurj hτ in

theorem range_homOfLE_comp_subset {U' : X.Opens} (hle : U' ≤ U) :
    Set.range (X.homOfLE hle ≫ τ.hom).base ⊆ Set.range (X.homOfLE hle).base := by
  rintro _ ⟨z, rfl⟩
  refine ⟨z, ?_⟩
  rw [Scheme.Hom.comp_apply, base_apply_eq U τ h hsurj hτ]

noncomputable def restr {U' : X.Opens} (hle : U' ≤ U) : (U' : Scheme.{0}) ⟶ (U' : Scheme.{0}) :=
  IsOpenImmersion.lift (X.homOfLE hle) (X.homOfLE hle ≫ τ.hom) (range_homOfLE_comp_subset U τ h hsurj hτ hle)

@[reassoc]
theorem restr_fac {U' : X.Opens} (hle : U' ≤ U) :
    restr U τ h hsurj hτ hle ≫ X.homOfLE hle = X.homOfLE hle ≫ τ.hom :=
  IsOpenImmersion.lift_fac _ _ _

end Restrict

section Surj

variable {B B₁ : Type} [CommRing B] [CommRing B₁] [Algebra B B₁]
  (hπ : Function.Surjective (algebraMap B B₁)) (hker : IsNilpotent (RingHom.ker (algebraMap B B₁)))

include hπ hker in
theorem surjective_specMap : Surjective (Spec.map (CommRingCat.ofHom (algebraMap B B₁))) := by
  refine ⟨fun p => ?_⟩

  have hrange := range_comap_of_surjective _ (algebraMap B B₁) hπ
  have hp : p ∈ Set.range (PrimeSpectrum.comap (algebraMap B B₁)) := by
    rw [hrange]
    intro x hx
    obtain ⟨n, hn⟩ := hker
    have hxn : x ^ n ∈ (RingHom.ker (algebraMap B B₁)) ^ n := Ideal.pow_mem_pow hx n
    rw [hn] at hxn
    have : x ^ n = 0 := by simpa using hxn
    exact p.isPrime.mem_of_pow_mem n (by rw [this]; exact p.asIdeal.zero_mem)
  obtain ⟨q, hq⟩ := hp
  exact ⟨q, hq⟩

variable {A₁ : Scheme.{0}} {f₁ : A₁ ⟶ Spec (CommRingCat.of B₁)} {L₁ : RelativeGroupLaw B₁ f₁}
  (D₀ : BareDeformation f₁ L₁ B)

include hπ hker in
theorem surjective_g : Function.Surjective D₀.g.base := by
  have : Surjective D₀.g :=
    MorphismProperty.of_isPullback (P := @Surjective) D₀.cart.flip (surjective_specMap hπ hker)
  exact this.surj

include hπ hker in

theorem surjective_g_restrict (U : D₀.A.Opens) : Function.Surjective (D₀.g ∣_ U).base := by
  intro x
  obtain ⟨y, hy⟩ := surjective_g hπ hker D₀ x.1
  refine ⟨⟨y, show y ∈ D₀.g ⁻¹ᵁ U by simp [hy, x.2]⟩, ?_⟩
  apply Subtype.ext
  rw [morphismRestrict_base_coe]
  exact hy

end Surj

end P2mWs2RG2

namespace P2mWs2RG2

section Frame

variable {B B₁ : Type} [CommRing B] [CommRing B₁] [Algebra B B₁]
  (hπ : Function.Surjective (algebraMap B B₁)) (hker : IsNilpotent (RingHom.ker (algebraMap B B₁)))
  {A₁ : Scheme.{0}} {f₁ : A₁ ⟶ Spec (CommRingCat.of B₁)} {L₁ : RelativeGroupLaw B₁ f₁}
  (D₀ : BareDeformation f₁ L₁ B) [IsSeparated D₀.f] (𝒰 : D₀.A.OrderedAffineCover)
  (τ : ∀ s : 𝒰.Idx 1, ((↑(𝒰.inter s) : Scheme.{0}) ≅ ↑(𝒰.inter s)))
  (hτB : ∀ s : 𝒰.Idx 1, (τ s).hom ≫ (𝒰.inter s).ι ≫ D₀.f = (𝒰.inter s).ι ≫ D₀.f)
  (hτg : ∀ s : 𝒰.Idx 1, (D₀.g ∣_ 𝒰.inter s) ≫ (τ s).hom = D₀.g ∣_ 𝒰.inter s)

noncomputable def ρ (r : 𝒰.Idx 2) (ℓ : Fin 3) : (↑(𝒰.inter r) : Scheme.{0}) ⟶ ↑(𝒰.inter r) :=
  restr (𝒰.inter (𝒰.face r ℓ)) (τ (𝒰.face r ℓ)) (D₀.g ∣_ 𝒰.inter (𝒰.face r ℓ))
    (surjective_g_restrict hπ hker D₀ _) (hτg _) (𝒰.inter_le_inter_face r ℓ)

theorem ρ_fac (r : 𝒰.Idx 2) (ℓ : Fin 3) :
    ρ hπ hker D₀ 𝒰 τ hτg r ℓ ≫ D₀.A.homOfLE (𝒰.inter_le_inter_face r ℓ) =
      D₀.A.homOfLE (𝒰.inter_le_inter_face r ℓ) ≫ (τ (𝒰.face r ℓ)).hom :=
  restr_fac _ _ _ _ _ _

@[reassoc]
theorem ρ_ι (r : 𝒰.Idx 2) (ℓ : Fin 3) :
    ρ hπ hker D₀ 𝒰 τ hτg r ℓ ≫ (𝒰.inter r).ι =
      D₀.A.homOfLE (𝒰.inter_le_inter_face r ℓ) ≫ (τ (𝒰.face r ℓ)).hom ≫ (𝒰.inter (𝒰.face r ℓ)).ι := by
  rw [← Scheme.homOfLE_ι D₀.A (𝒰.inter_le_inter_face r ℓ), ← Category.assoc, ρ_fac, Category.assoc]

theorem ρ_base (r : 𝒰.Idx 2) (ℓ : Fin 3) (x : (↑(𝒰.inter r) : Scheme.{0})) : (ρ hπ hker D₀ 𝒰 τ hτg r ℓ).base x = x := by
  apply (𝒰.inter r).ι.isOpenEmbedding.injective
  rw [← Scheme.Hom.comp_apply, ρ_ι, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply,
    base_apply_eq _ _ _ (surjective_g_restrict hπ hker D₀ _) (hτg _)]
  simp

include hτB in
theorem ρ_over (r : 𝒰.Idx 2) (ℓ : Fin 3) :
    ρ hπ hker D₀ 𝒰 τ hτg r ℓ ≫ (𝒰.inter r).ι ≫ D₀.f = (𝒰.inter r).ι ≫ D₀.f := by
  rw [ρ_ι_assoc, hτB, Scheme.homOfLE_ι_assoc]

theorem isAffineOpen_inter3 (r : 𝒰.Idx 2) : IsAffineOpen (𝒰.inter r) :=
  Scheme.OrderedAffineCover.isAffineOpen_inter D₀.f 𝒰 r

noncomputable def twist (r : 𝒰.Idx 2) (ℓ : Fin 3) : Spec Γ(D₀.A, 𝒰.inter r) ⟶ D₀.A :=
  (isAffineOpen_inter3 D₀ 𝒰 r).isoSpec.inv ≫ ρ hπ hker D₀ 𝒰 τ hτg r ℓ ≫ (𝒰.inter r).ι

end Frame

end P2mWs2RG2

namespace P2mWs2RG2

section ChartsB

variable {T' : Type} [CommRing T'] {Y : Scheme.{0}} (q : Y ⟶ Spec (CommRingCat.of T'))

theorem appLE_top_res {U U' : Y.Opens} (h : U ≤ U') :
    ((Scheme.ΓSpecIso (CommRingCat.of T')).inv ≫ q.appLE ⊤ U' le_top) ≫ Y.presheaf.map (homOfLE h).op =
      (Scheme.ΓSpecIso (CommRingCat.of T')).inv ≫ q.appLE ⊤ U le_top := by
  rw [Category.assoc, Scheme.Hom.appLE_map]

theorem fromSpec_comp_eq' {U : Y.Opens} (hU : IsAffineOpen U) :
    hU.fromSpec ≫ q = Spec.map ((Scheme.ΓSpecIso (CommRingCat.of T')).inv ≫ q.appLE ⊤ U le_top) := by
  have happ : q.appLE ⊤ U le_top = q.appTop ≫ Y.presheaf.map (homOfLE le_top).op := rfl
  calc hU.fromSpec ≫ q
      = hU.fromSpec ≫ q ≫ (Spec (CommRingCat.of T')).toSpecΓ ≫
          Spec.map (Scheme.ΓSpecIso (CommRingCat.of T')).inv := by
        rw [toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]
    _ = Spec.map ((Scheme.ΓSpecIso (CommRingCat.of T')).inv ≫ q.appLE ⊤ U le_top) := by
        rw [Scheme.toSpecΓ_naturality_assoc, hU.fromSpec_toSpecΓ_assoc, happ]
        simp only [Spec.map_comp, Category.assoc]

theorem specOver' {U : Y.Opens} (hU : IsAffineOpen U) :
    letI := algebraOfHom q U
    hU.fromSpec ≫ q = Spec.map (CommRingCat.ofHom (algebraMap T' Γ(Y, U))) :=
  fromSpec_comp_eq' q hU

theorem flat_algebraOfHom [Flat q] {U : Y.Opens} (hU : IsAffineOpen U) :
    letI := algebraOfHom q U
    Module.Flat T' Γ(Y, U) := by
  have : Flat (Spec.map ((Scheme.ΓSpecIso (CommRingCat.of T')).inv ≫ q.appLE ⊤ U le_top)) := by
    rw [← fromSpec_comp_eq' q hU]; infer_instance
  exact (HasRingHomProperty.Spec_iff (P := @Flat)).mp this

theorem spec_restrictAlgHom {U U' : Y.Opens} (h : U ≤ U') :
    letI := algebraOfHom q U; letI := algebraOfHom q U'
    Spec.map (CommRingCat.ofHom (restrictAlgHom q h).toRingHom) = Spec.map (Y.presheaf.map (homOfLE h).op) := rfl

theorem spec_restrictAlgHom_fromSpec {U U' : Y.Opens} (hU : IsAffineOpen U) (hU' : IsAffineOpen U') (h : U ≤ U') :
    letI := algebraOfHom q U; letI := algebraOfHom q U'
    Spec.map (CommRingCat.ofHom (restrictAlgHom q h).toRingHom) ≫ hU'.fromSpec = hU.fromSpec := by
  rw [spec_restrictAlgHom]; exact IsAffineOpen.map_fromSpec hU' hU (homOfLE h).op

@[reassoc]
theorem spec_restrictAlgHom_isoSpec_inv {U U' : Y.Opens} (hU : IsAffineOpen U) (hU' : IsAffineOpen U') (h : U ≤ U') :
    letI := algebraOfHom q U; letI := algebraOfHom q U'
    Spec.map (CommRingCat.ofHom (restrictAlgHom q h).toRingHom) ≫ hU'.isoSpec.inv = hU.isoSpec.inv ≫ Y.homOfLE h := by
  rw [← cancel_mono U'.ι, Category.assoc, Category.assoc, IsAffineOpen.isoSpec_inv_ι, Scheme.homOfLE_ι,
    IsAffineOpen.isoSpec_inv_ι]
  exact spec_restrictAlgHom_fromSpec q hU hU' h

end ChartsB

end P2mWs2RG2

namespace P2mWs2RG2

section Tensor

variable {B : Type} [CommRing B] [IsLocalRing B] (I : Ideal B) (hI : I ≤ maximalIdeal B)
  (C : Type) [CommRing C] [Algebra B C]

include hI in
theorem tmul_eq_zero_of_mem_map (a : ResidueField B) (y : C) (hy : y ∈ I.map (algebraMap B C)) :
    (a ⊗ₜ[B] y : ResidueField B ⊗[B] C) = 0 := by
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨i, hi, rfl⟩ := hy
    rw [Algebra.algebraMap_eq_smul_one, TensorProduct.tmul_smul, TensorProduct.smul_tmul', Algebra.smul_def,
      IsLocalRing.ResidueField.algebraMap_eq, (IsLocalRing.residue_eq_zero_iff i).mpr (hI hi), zero_mul,
      TensorProduct.zero_tmul]
  | zero => exact TensorProduct.tmul_zero _ _
  | add y z _ _ hy hz => rw [TensorProduct.tmul_add, hy, hz, add_zero]
  | smul c y _ hy =>
    rw [smul_eq_mul, show (a ⊗ₜ[B] (c * y) : ResidueField B ⊗[B] C) = ((1 : ResidueField B) ⊗ₜ[B] c) * (a ⊗ₜ[B] y) by
      rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul], hy, mul_zero]

include hI in
theorem tensor_map_eq_id (φ : C →ₐ[B] C) (hφ : ∀ x, φ x - x ∈ I.map (algebraMap B C)) :
    Algebra.TensorProduct.map (AlgHom.id (ResidueField B) (ResidueField B)) φ =
      AlgHom.id (ResidueField B) (ResidueField B ⊗[B] C) := by
  refine AlgHom.ext fun x => ?_
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a c =>
    rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, AlgHom.id_apply, ← sub_eq_zero, ← TensorProduct.tmul_sub]
    exact tmul_eq_zero_of_mem_map I hI C a _ (hφ c)
  | add x y hx hy => rw [map_add, hx, hy, map_add]

end Tensor

end P2mWs2RG2

namespace P2mWs2RG2

section Iface

variable {B B₁ : Type} [CommRing B] [IsLocalRing B] [IsArtinianRing B] [CommRing B₁] [Algebra B B₁]
  (hπ : Function.Surjective (algebraMap B B₁)) (hker : IsNilpotent (RingHom.ker (algebraMap B B₁)))
  (hsmall : RingHom.ker (algebraMap B B₁) * maximalIdeal B = ⊥)
  (hI : RingHom.ker (algebraMap B B₁) ≤ maximalIdeal B)
  (V : Type) [AddCommGroup V] [Module (ResidueField B) V] [Module.Finite (ResidueField B) V]
  [Module B V] [IsScalarTower B (ResidueField B) V]
  [Module (ResidueField B)ᵐᵒᵖ V] [IsCentralScalar (ResidueField B) V]
  (ι : V →ₗ[B] B) (hι : Function.Injective ι)
  (hιI : LinearMap.range ι = Submodule.restrictScalars B (RingHom.ker (algebraMap B B₁)))
  {A₁ : Scheme.{0}} {f₁ : A₁ ⟶ Spec (CommRingCat.of B₁)} {L₁ : RelativeGroupLaw B₁ f₁}
  (D₀ : BareDeformation f₁ L₁ B) [IsSeparated D₀.f] (𝒰 : D₀.A.OrderedAffineCover) (i₀ : 𝒰.ι)
  (τ : ∀ s : 𝒰.Idx 1, ((↑(𝒰.inter s) : Scheme.{0}) ≅ ↑(𝒰.inter s)))
  (hτB : ∀ s : 𝒰.Idx 1, (τ s).hom ≫ (𝒰.inter s).ι ≫ D₀.f = (𝒰.inter s).ι ≫ D₀.f)
  (hτg : ∀ s : 𝒰.Idx 1, (D₀.g ∣_ 𝒰.inter s) ≫ (τ s).hom = D₀.g ∣_ 𝒰.inter s)

theorem flat_inter {i : ℕ} (s : 𝒰.Idx i) :
    letI := algebraOfHom D₀.f (𝒰.inter s)
    Module.Flat B Γ(D₀.A, 𝒰.inter s) := by
  haveI := D₀.bundle.smooth
  exact flat_algebraOfHom D₀.f (Scheme.OrderedAffineCover.isAffineOpen_inter D₀.f 𝒰 s)

theorem fromSpec_over (r : 𝒰.Idx 2) :
    letI := algebraOfHom D₀.f (𝒰.inter r)
    (isAffineOpen_inter3 D₀ 𝒰 r).fromSpec ≫ D₀.f = Spec.map (CommRingCat.ofHom (algebraMap B Γ(D₀.A, 𝒰.inter r))) :=
  specOver' D₀.f _

theorem specMk_isoSpecInv_ρ (r : 𝒰.Idx 2) (ℓ : Fin 3) :
    letI := algebraOfHom D₀.f (𝒰.inter r)
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk ((RingHom.ker (algebraMap B B₁)).map (algebraMap B Γ(D₀.A, 𝒰.inter r))))) ≫
        (isAffineOpen_inter3 D₀ 𝒰 r).isoSpec.inv ≫ ρ hπ hker D₀ 𝒰 τ hτg r ℓ =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk ((RingHom.ker (algebraMap B B₁)).map (algebraMap B Γ(D₀.A, 𝒰.inter r))))) ≫
        (isAffineOpen_inter3 D₀ 𝒰 r).isoSpec.inv := by
  letI := algebraOfHom D₀.f (𝒰.inter r)

  have hle := 𝒰.inter_le_inter_face r ℓ
  rw [← cancel_mono (D₀.A.homOfLE (𝒰.inter_le_inter_face r ℓ)), Category.assoc, Category.assoc, ρ_fac,
    Category.assoc]

  obtain ⟨z, hz⟩ : ∃ z : Spec (CommRingCat.of ((D₀.A.presheaf.obj (Opposite.op (𝒰.inter r))) ⧸
      (RingHom.ker (algebraMap B B₁)).map (algebraMap B (D₀.A.presheaf.obj (Opposite.op (𝒰.inter r)))))) ⟶
        ↑(D₀.g ⁻¹ᵁ 𝒰.inter (𝒰.face r ℓ)),
      z ≫ (D₀.g ∣_ 𝒰.inter (𝒰.face r ℓ)) =
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk ((RingHom.ker (algebraMap B B₁)).map (algebraMap B (D₀.A.presheaf.obj (Opposite.op (𝒰.inter r))))))) ≫
          (isAffineOpen_inter3 D₀ 𝒰 r).isoSpec.inv ≫ D₀.A.homOfLE (𝒰.inter_le_inter_face r ℓ) := by

    let e := RingHom.quotientKerEquivOfSurjective hπ
    let g₀ : B ⧸ RingHom.ker (algebraMap B B₁) →+* (D₀.A.presheaf.obj (Opposite.op (𝒰.inter r))) ⧸
        (RingHom.ker (algebraMap B B₁)).map (algebraMap B (D₀.A.presheaf.obj (Opposite.op (𝒰.inter r)))) :=
      Ideal.Quotient.lift _ ((Ideal.Quotient.mk _).comp (algebraMap B (D₀.A.presheaf.obj (Opposite.op (𝒰.inter r))))) (fun b hb => by
        rw [RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem]; exact Ideal.mem_map_of_mem _ hb)
    let ψ : B₁ →+* (D₀.A.presheaf.obj (Opposite.op (𝒰.inter r))) ⧸
        (RingHom.ker (algebraMap B B₁)).map (algebraMap B (D₀.A.presheaf.obj (Opposite.op (𝒰.inter r)))) :=
      g₀.comp e.symm.toRingHom
    have hψ : ψ.comp (algebraMap B B₁) = (Ideal.Quotient.mk _).comp (algebraMap B (D₀.A.presheaf.obj (Opposite.op (𝒰.inter r)))) := by
      refine RingHom.ext fun b => ?_
      have : e.symm (algebraMap B B₁ b) = Ideal.Quotient.mk _ b := by
        rw [RingEquiv.symm_apply_eq]; rfl
      change g₀ (e.symm (algebraMap B B₁ b)) = _
      rw [this]; rfl
    have hcompat : (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk ((RingHom.ker (algebraMap B B₁)).map (algebraMap B (D₀.A.presheaf.obj (Opposite.op (𝒰.inter r))))))) ≫
          (isAffineOpen_inter3 D₀ 𝒰 r).isoSpec.inv ≫ D₀.A.homOfLE (𝒰.inter_le_inter_face r ℓ) ≫ (𝒰.inter (𝒰.face r ℓ)).ι) ≫ D₀.f =
        Spec.map (CommRingCat.ofHom ψ) ≫ Spec.map (CommRingCat.ofHom (algebraMap B B₁)) := by
      rw [Scheme.homOfLE_ι, Category.assoc, Category.assoc, IsAffineOpen.isoSpec_inv_ι_assoc, specOver' D₀.f,
        ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, hψ]
    let L := D₀.cart.lift _ _ hcompat
    have hL : L ≫ D₀.g = _ := D₀.cart.lift_fst _ _ hcompat
    have hrange : Set.range L.base ⊆ Set.range (D₀.g ⁻¹ᵁ 𝒰.inter (𝒰.face r ℓ)).ι.base := by
      rintro _ ⟨x, rfl⟩
      rw [Scheme.Opens.range_ι]
      show D₀.g.base (L.base x) ∈ (𝒰.inter (𝒰.face r ℓ) : Set D₀.A)
      rw [← Scheme.Hom.comp_apply, hL]
      simp only [Scheme.Hom.comp_apply]
      exact Subtype.property _
    refine ⟨IsOpenImmersion.lift _ L hrange, ?_⟩
    rw [← cancel_mono (𝒰.inter (𝒰.face r ℓ)).ι, Category.assoc, morphismRestrict_ι, IsOpenImmersion.lift_fac_assoc, hL,
      Category.assoc, Category.assoc]
  calc _ = (z ≫ (D₀.g ∣_ 𝒰.inter (𝒰.face r ℓ))) ≫ (τ (𝒰.face r ℓ)).hom := by rw [hz]; simp only [Category.assoc]
    _ = z ≫ (D₀.g ∣_ 𝒰.inter (𝒰.face r ℓ)) := by rw [Category.assoc, hτg]
    _ = _ := hz

theorem hak_pullback :
    IsPullback (pullback.fst D₀.f (specMap B (ResidueField B))) (pullback.snd D₀.f (specMap B (ResidueField B)))
      D₀.f (Spec.map (CommRingCat.ofHom (residue B))) :=
  IsPullback.of_hasPullback _ _

include hI hsmall hι hιI in

theorem coords_restrict (r : 𝒰.Idx 2) (ℓ : Fin 3)
    (cs : letI := algebraOfHom D₀.f (𝒰.inter (𝒰.face r ℓ))
      Γ((pullback D₀.f (specMap B (ResidueField B))), ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)) →
        (Module.Dual (ResidueField B) V →ₗ[(ResidueField B)] ((ResidueField B) ⊗[B] Γ(D₀.A, 𝒰.inter (𝒰.face r ℓ)))))
    (hcs : letI := algebraOfHom D₀.f (𝒰.inter (𝒰.face r ℓ))
      IsTangentCoordsOfPairAt (RingHom.ker (algebraMap B B₁)) V ι Γ(D₀.A, 𝒰.inter (𝒰.face r ℓ))
        ((Scheme.OrderedAffineCover.isAffineOpen_inter D₀.f 𝒰 (𝒰.face r ℓ)).fromSpec)
        ((Scheme.OrderedAffineCover.isAffineOpen_inter D₀.f 𝒰 (𝒰.face r ℓ)).isoSpec.inv ≫ (τ (𝒰.face r ℓ)).hom ≫ (𝒰.inter (𝒰.face r ℓ)).ι)
        (pullback.snd D₀.f (specMap B (ResidueField B))) (RelativeGroupLaw.baseChange (specMap B (ResidueField B)) D₀.L)
        (pullback.fst D₀.f (specMap B (ResidueField B))) ((𝒰.baseChange D₀.f (ResidueField B)).U i₀) cs) :
    letI := algebraOfHom D₀.f (𝒰.inter r); letI := algebraOfHom D₀.f (𝒰.inter (𝒰.face r ℓ))
    IsTangentCoordsOfPairAt (RingHom.ker (algebraMap B B₁)) V ι Γ(D₀.A, 𝒰.inter r)
      ((isAffineOpen_inter3 D₀ 𝒰 r).fromSpec) ((isAffineOpen_inter3 D₀ 𝒰 r).isoSpec.inv ≫ ρ hπ hker D₀ 𝒰 τ hτg r ℓ ≫ (𝒰.inter r).ι)
      (pullback.snd D₀.f (specMap B (ResidueField B))) (RelativeGroupLaw.baseChange (specMap B (ResidueField B)) D₀.L)
      (pullback.fst D₀.f (specMap B (ResidueField B))) ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)
      (fun a => (Algebra.TensorProduct.map (AlgHom.id (ResidueField B) (ResidueField B))
        (restrictAlgHom D₀.f (𝒰.inter_le_inter_face r ℓ))).toLinearMap ∘ₗ cs a) := by
  letI := algebraOfHom D₀.f (𝒰.inter r); letI := algebraOfHom D₀.f (𝒰.inter (𝒰.face r ℓ))
  haveI := flat_inter D₀ 𝒰 r
  have H := AlgebraicGeometry.SmallExtension.isTangentCoordsOfPairAt_comp_of_flat (RingHom.ker (algebraMap B B₁)) hI hsmall
    V ι hι hιI Γ(D₀.A, 𝒰.inter (𝒰.face r ℓ)) Γ(D₀.A, 𝒰.inter r) (restrictAlgHom D₀.f (𝒰.inter_le_inter_face r ℓ))
    _ _ (pullback.snd D₀.f (specMap B (ResidueField B))) (RelativeGroupLaw.baseChange (specMap B (ResidueField B)) D₀.L)
    (pullback.fst D₀.f (specMap B (ResidueField B))) ((𝒰.baseChange D₀.f (ResidueField B)).U i₀) cs hcs
  rw [spec_restrictAlgHom_fromSpec D₀.f (isAffineOpen_inter3 D₀ 𝒰 r)
      (Scheme.OrderedAffineCover.isAffineOpen_inter D₀.f 𝒰 (𝒰.face r ℓ)) (𝒰.inter_le_inter_face r ℓ),
    spec_restrictAlgHom_isoSpec_inv_assoc D₀.f (isAffineOpen_inter3 D₀ 𝒰 r)
      (Scheme.OrderedAffineCover.isAffineOpen_inter D₀.f 𝒰 (𝒰.face r ℓ)) (𝒰.inter_le_inter_face r ℓ),
    ← ρ_ι hπ hker D₀ 𝒰 τ hτg r ℓ] at H
  exact H

include hI hsmall hι hιI hτB in

theorem coords_precomp (r : 𝒰.Idx 2)
    (cs : letI := algebraOfHom D₀.f (𝒰.inter (𝒰.face r 0))
      Γ((pullback D₀.f (specMap B (ResidueField B))), ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)) →
        (Module.Dual (ResidueField B) V →ₗ[(ResidueField B)] ((ResidueField B) ⊗[B] Γ(D₀.A, 𝒰.inter (𝒰.face r 0)))))
    (hcs : letI := algebraOfHom D₀.f (𝒰.inter (𝒰.face r 0))
      IsTangentCoordsOfPairAt (RingHom.ker (algebraMap B B₁)) V ι Γ(D₀.A, 𝒰.inter (𝒰.face r 0))
        ((Scheme.OrderedAffineCover.isAffineOpen_inter D₀.f 𝒰 (𝒰.face r 0)).fromSpec)
        ((Scheme.OrderedAffineCover.isAffineOpen_inter D₀.f 𝒰 (𝒰.face r 0)).isoSpec.inv ≫ (τ (𝒰.face r 0)).hom ≫ (𝒰.inter (𝒰.face r 0)).ι)
        (pullback.snd D₀.f (specMap B (ResidueField B))) (RelativeGroupLaw.baseChange (specMap B (ResidueField B)) D₀.L)
        (pullback.fst D₀.f (specMap B (ResidueField B))) ((𝒰.baseChange D₀.f (ResidueField B)).U i₀) cs) :
    letI := algebraOfHom D₀.f (𝒰.inter r); letI := algebraOfHom D₀.f (𝒰.inter (𝒰.face r 0))
    IsTangentCoordsOfPairAt (RingHom.ker (algebraMap B B₁)) V ι Γ(D₀.A, 𝒰.inter r)
      ((isAffineOpen_inter3 D₀ 𝒰 r).isoSpec.inv ≫ ρ hπ hker D₀ 𝒰 τ hτg r 2 ≫ (𝒰.inter r).ι)
      ((isAffineOpen_inter3 D₀ 𝒰 r).isoSpec.inv ≫ ρ hπ hker D₀ 𝒰 τ hτg r 2 ≫ ρ hπ hker D₀ 𝒰 τ hτg r 0 ≫ (𝒰.inter r).ι)
      (pullback.snd D₀.f (specMap B (ResidueField B))) (RelativeGroupLaw.baseChange (specMap B (ResidueField B)) D₀.L)
      (pullback.fst D₀.f (specMap B (ResidueField B))) ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)
      (fun a => (Algebra.TensorProduct.map (AlgHom.id (ResidueField B) (ResidueField B))
        (restrictAlgHom D₀.f (𝒰.inter_le_inter_face r 0))).toLinearMap ∘ₗ cs a) := by
  letI := algebraOfHom D₀.f (𝒰.inter r); letI := algebraOfHom D₀.f (𝒰.inter (𝒰.face r 0))
  haveI := flat_inter D₀ 𝒰 r
  have hU := isAffineOpen_inter3 D₀ 𝒰 r

  let φ : Γ(D₀.A, 𝒰.inter r) ⟶ Γ(D₀.A, 𝒰.inter r) :=
    Spec.preimage (hU.isoSpec.inv ≫ ρ hπ hker D₀ 𝒰 τ hτg r 2 ≫ hU.isoSpec.hom)
  have hφ : Spec.map φ = hU.isoSpec.inv ≫ ρ hπ hker D₀ 𝒰 τ hτg r 2 ≫ hU.isoSpec.hom := Spec.map_preimage _
  have hφ' : ∀ {W : Scheme.{0}} (k : (↑(𝒰.inter r) : Scheme.{0}) ⟶ W),
      Spec.map φ ≫ hU.isoSpec.inv ≫ k = hU.isoSpec.inv ≫ ρ hπ hker D₀ 𝒰 τ hτg r 2 ≫ k := by
    intro W k; rw [hφ]; simp only [Category.assoc, Iso.hom_inv_id_assoc]
  have hφalg : CommRingCat.ofHom (algebraMap B Γ(D₀.A, 𝒰.inter r)) ≫ φ =
      CommRingCat.ofHom (algebraMap B Γ(D₀.A, 𝒰.inter r)) := by
    apply Spec.map_injective
    rw [Spec.map_comp, ← fromSpec_over D₀ 𝒰 r, ← IsAffineOpen.isoSpec_inv_ι, Category.assoc, hφ',
      ρ_over hπ hker D₀ 𝒰 τ hτB hτg]
  let φA : Γ(D₀.A, 𝒰.inter r) →ₐ[B] Γ(D₀.A, 𝒰.inter r) :=
    { φ.hom with
      commutes' := fun b => by
        change (CommRingCat.ofHom (algebraMap B Γ(D₀.A, 𝒰.inter r)) ≫ φ).hom b = _
        rw [hφalg]; rfl }
  have hSpecφA : Spec.map (CommRingCat.ofHom φA.toRingHom) = Spec.map φ := rfl

  have hφmod : ∀ x, φA x - x ∈ (RingHom.ker (algebraMap B B₁)).map (algebraMap B Γ(D₀.A, 𝒰.inter r)) := by
    have h2 := specMk_isoSpecInv_ρ hπ hker D₀ 𝒰 τ hτg r 2
    have hφ₁ : Spec.map φ ≫ hU.isoSpec.inv = hU.isoSpec.inv ≫ ρ hπ hker D₀ 𝒰 τ hτg r 2 := by
      simpa only [Category.comp_id] using hφ' (𝟙 _)
    rw [← hφ₁, ← Category.assoc] at h2
    have h2' := (cancel_mono _).mp h2
    rw [← Spec.map_comp] at h2'
    have h3 := Spec.map_injective h2'
    intro x
    have hx := congrArg (fun f => f.hom x) h3
    change Ideal.Quotient.mk _ (φ.hom x) = Ideal.Quotient.mk _ x at hx
    exact (Ideal.Quotient.eq).mp hx
  have hmapid := tensor_map_eq_id (RingHom.ker (algebraMap B B₁)) hI Γ(D₀.A, 𝒰.inter r) φA hφmod

  have H0 := coords_restrict hπ hker hsmall hI V ι hι hιI D₀ 𝒰 i₀ τ hτg r 0 cs hcs
  have H := AlgebraicGeometry.SmallExtension.isTangentCoordsOfPairAt_comp_of_flat (RingHom.ker (algebraMap B B₁)) hI hsmall
    V ι hι hιI Γ(D₀.A, 𝒰.inter r) Γ(D₀.A, 𝒰.inter r) φA _ _
    (pullback.snd D₀.f (specMap B (ResidueField B))) (RelativeGroupLaw.baseChange (specMap B (ResidueField B)) D₀.L)
    (pullback.fst D₀.f (specMap B (ResidueField B))) ((𝒰.baseChange D₀.f (ResidueField B)).U i₀) _ H0
  rw [hSpecφA, ← IsAffineOpen.isoSpec_inv_ι, hφ', hφ', hmapid] at H
  simpa only [AlgHom.toLinearMap_id, LinearMap.id_comp] using H

end Iface

end P2mWs2RG2

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct AlgebraicGeometry.Scheme.TwoAffineOpenCover"

universe u

namespace P2mWs2RG2
namespace Cocycle

theorem ringHom_tmul_ext {R A B C : Type u} [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    [Semiring C] (f g : A ⊗[R] B →+* C)
    (h₁ : ∀ a : A, f (a ⊗ₜ 1) = g (a ⊗ₜ 1)) (h₂ : ∀ b : B, f (1 ⊗ₜ b) = g (1 ⊗ₜ b)) (z : A ⊗[R] B) :
    f z = g z := by
  induction z using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | tmul a b =>
    have : a ⊗ₜ[R] b = (a ⊗ₜ[R] (1 : B)) * ((1 : A) ⊗ₜ[R] b) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    rw [this, map_mul, map_mul, h₁, h₂]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

variable {R : Type u} [CommRing R] {X : Scheme.{u}} (π : X ⟶ Spec (CommRingCat.of R)) [IsSeparated π]
  (𝒰 : X.OrderedAffineCover) (A : Type u) [CommRing A] [Algebra R A]

theorem cocycle_transfer (r : 𝒰.Idx 2)
    (σ : ∀ ℓ : Fin 3,
      letI := algebraOfHom π (𝒰.inter (𝒰.face r ℓ))
      (A ⊗[R] Γ(X, 𝒰.inter (𝒰.face r ℓ))) ≃+*
        Γ(pullback π (specMap R A), (𝒰.baseChange π A).inter (𝒰.face r ℓ)))
    (hσ₁ : ∀ (ℓ : Fin 3) (x : Γ(X, 𝒰.inter (𝒰.face r ℓ))),
      letI := algebraOfHom π (𝒰.inter (𝒰.face r ℓ))
      σ ℓ ((1 : A) ⊗ₜ[R] x) =
        ((pullback π (specMap R A)).presheaf.map (homOfLE (𝒰.baseChange_inter_le π A (𝒰.face r ℓ))).op).hom
          (((pullback.fst π (specMap R A)).app (𝒰.inter (𝒰.face r ℓ))).hom x))
    (hσ₂ : ∀ (ℓ : Fin 3) (a : A),
      letI := algebraOfHom π (𝒰.inter (𝒰.face r ℓ))
      letI := algebraOfHom (pullback.snd π (specMap R A)) ((𝒰.baseChange π A).inter (𝒰.face r ℓ))
      σ ℓ (a ⊗ₜ[R] (1 : Γ(X, 𝒰.inter (𝒰.face r ℓ)))) =
        algebraMap A Γ(pullback π (specMap R A), (𝒰.baseChange π A).inter (𝒰.face r ℓ)) a)
    (γ : (OModulePresheaf.unit (pullback.snd π (specMap R A))).cochain (𝒰.baseChange π A) 1)
    (hγ : (OModulePresheaf.unit (pullback.snd π (specMap R A))).d (𝒰.baseChange π A) 1 γ r = 0)
    (y : ∀ ℓ : Fin 3, letI := algebraOfHom π (𝒰.inter (𝒰.face r ℓ)); A ⊗[R] Γ(X, 𝒰.inter (𝒰.face r ℓ)))
    (hy : ∀ ℓ : Fin 3, σ ℓ (y ℓ) = γ (𝒰.face r ℓ)) :
    letI := fun ℓ : Fin 3 => algebraOfHom π (𝒰.inter (𝒰.face r ℓ))
    letI := algebraOfHom π (𝒰.inter r)
    (Algebra.TensorProduct.map (AlgHom.id A A) (restrictAlgHom π (𝒰.inter_le_inter_face r 1))) (y 1) =
      (Algebra.TensorProduct.map (AlgHom.id A A) (restrictAlgHom π (𝒰.inter_le_inter_face r 2))) (y 2) +
      (Algebra.TensorProduct.map (AlgHom.id A A) (restrictAlgHom π (𝒰.inter_le_inter_face r 0))) (y 0) := by
  classical
  letI := fun ℓ : Fin 3 => algebraOfHom π (𝒰.inter (𝒰.face r ℓ))
  letI iR := algebraOfHom π (𝒰.inter r)
  letI iRA := algebraOfHom (pullback.snd π (specMap R A)) ((𝒰.baseChange π A).inter r)

  obtain ⟨σr, hσr1, hσr2⟩ :=
    AlgebraicGeometry.Scheme.OrderedAffineCover.exists_ringEquiv_tensor_sections_baseChange_inter π 𝒰 A r

  have nat : ∀ (ℓ : Fin 3) (z : A ⊗[R] Γ(X, 𝒰.inter (𝒰.face r ℓ))),
      ((pullback π (specMap R A)).presheaf.map (homOfLE ((𝒰.baseChange π A).inter_le_inter_face r ℓ)).op).hom (σ ℓ z) =
        σr ((Algebra.TensorProduct.map (AlgHom.id A A) (restrictAlgHom π (𝒰.inter_le_inter_face r ℓ))) z) := by
    intro ℓ
    letI := algebraOfHom (pullback.snd π (specMap R A)) ((𝒰.baseChange π A).inter (𝒰.face r ℓ))
    apply ringHom_tmul_ext
      (((pullback π (specMap R A)).presheaf.map (homOfLE ((𝒰.baseChange π A).inter_le_inter_face r ℓ)).op).hom.comp
        (σ ℓ).toRingHom)
      (σr.toRingHom.comp (Algebra.TensorProduct.map (AlgHom.id A A) (restrictAlgHom π (𝒰.inter_le_inter_face r ℓ))).toRingHom)
    · intro a
      show ((pullback π (specMap R A)).presheaf.map _).hom (σ ℓ (a ⊗ₜ 1)) =
        σr (Algebra.TensorProduct.map (AlgHom.id A A) (restrictAlgHom π (𝒰.inter_le_inter_face r ℓ)) (a ⊗ₜ 1))
      rw [hσ₂, Algebra.TensorProduct.map_tmul, map_one, AlgHom.id_apply, hσr2, algebraMap_algebraOfHom, algebraMap_algebraOfHom]
      show ((pullback.snd π (specMap R A)).appLE ⊤ _ le_top ≫ (pullback π (specMap R A)).presheaf.map _).hom _ = _
      rw [Scheme.Hom.appLE_map]
    · intro x
      show ((pullback π (specMap R A)).presheaf.map _).hom (σ ℓ (1 ⊗ₜ x)) =
        σr (Algebra.TensorProduct.map (AlgHom.id A A) (restrictAlgHom π (𝒰.inter_le_inter_face r ℓ)) (1 ⊗ₜ x))
      rw [hσ₁, Algebra.TensorProduct.map_tmul, map_one, hσr1]
      show ((pullback.fst π (specMap R A)).appLE (𝒰.inter (𝒰.face r ℓ)) ((𝒰.baseChange π A).inter (𝒰.face r ℓ))
            (𝒰.baseChange_inter_le π A (𝒰.face r ℓ)) ≫
          (pullback π (specMap R A)).presheaf.map (homOfLE ((𝒰.baseChange π A).inter_le_inter_face r ℓ)).op).hom x =
        (X.presheaf.map (homOfLE (𝒰.inter_le_inter_face r ℓ)).op ≫
          (pullback.fst π (specMap R A)).appLE (𝒰.inter r) ((𝒰.baseChange π A).inter r) (𝒰.baseChange_inter_le π A r)).hom x
      rw [Scheme.Hom.appLE_map, Scheme.Hom.map_appLE]

  have hd := hγ
  rw [OModulePresheaf.d_apply, Fin.sum_univ_three] at hd
  simp only [Fin.val_zero, Fin.val_one, Fin.val_two, pow_zero, pow_one, one_smul, neg_smul] at hd
  have h2 : ((-1 : ℤ) ^ 2 : ℤ) = 1 := by norm_num
  rw [h2, one_smul] at hd
  apply σr.injective
  rw [map_add, ← nat, ← nat, ← nat, hy, hy, hy]

  have hd' := eq_neg_of_add_eq_zero_left hd

  have : ∀ (a b c : Γ(pullback π (specMap R A), (𝒰.baseChange π A).inter r)), a + -b + c = 0 → b = c + a := by
    intro a b c h
    have := congrArg (· + b) h
    simp only [zero_add] at this
    rw [← this]; abel
  exact this _ _ _ hd

theorem cocycle_coords (r : 𝒰.Idx 2)
    (σ : ∀ ℓ : Fin 3,
      letI := algebraOfHom π (𝒰.inter (𝒰.face r ℓ))
      (A ⊗[R] Γ(X, 𝒰.inter (𝒰.face r ℓ))) ≃+*
        Γ(pullback π (specMap R A), (𝒰.baseChange π A).inter (𝒰.face r ℓ)))
    (hσ₁ : ∀ (ℓ : Fin 3) (x : Γ(X, 𝒰.inter (𝒰.face r ℓ))),
      letI := algebraOfHom π (𝒰.inter (𝒰.face r ℓ))
      σ ℓ ((1 : A) ⊗ₜ[R] x) =
        ((pullback π (specMap R A)).presheaf.map (homOfLE (𝒰.baseChange_inter_le π A (𝒰.face r ℓ))).op).hom
          (((pullback.fst π (specMap R A)).app (𝒰.inter (𝒰.face r ℓ))).hom x))
    (hσ₂ : ∀ (ℓ : Fin 3) (a : A),
      letI := algebraOfHom π (𝒰.inter (𝒰.face r ℓ))
      letI := algebraOfHom (pullback.snd π (specMap R A)) ((𝒰.baseChange π A).inter (𝒰.face r ℓ))
      σ ℓ (a ⊗ₜ[R] (1 : Γ(X, 𝒰.inter (𝒰.face r ℓ)))) =
        algebraMap A Γ(pullback π (specMap R A), (𝒰.baseChange π A).inter (𝒰.face r ℓ)) a)
    {Ω : Type u} {D : Type u} [AddCommGroup D] [Module A D]
    (γ : Ω → D → (OModulePresheaf.unit (pullback.snd π (specMap R A))).cochain (𝒰.baseChange π A) 1)
    (hγ : ∀ (a : Ω) (ξ : D), γ a ξ ∈ LinearMap.ker ((OModulePresheaf.unit (pullback.snd π (specMap R A))).d (𝒰.baseChange π A) 1))
    (cs : ∀ ℓ : Fin 3, letI := algebraOfHom π (𝒰.inter (𝒰.face r ℓ)); Ω → (D →ₗ[A] A ⊗[R] Γ(X, 𝒰.inter (𝒰.face r ℓ))))
    (hcs : ∀ (ℓ : Fin 3) (a : Ω) (ξ : D), σ ℓ (cs ℓ a ξ) = γ a ξ (𝒰.face r ℓ)) :
    letI := fun ℓ : Fin 3 => algebraOfHom π (𝒰.inter (𝒰.face r ℓ))
    letI := algebraOfHom π (𝒰.inter r)
    (fun a => (Algebra.TensorProduct.map (AlgHom.id A A) (restrictAlgHom π (𝒰.inter_le_inter_face r 1))).toLinearMap ∘ₗ cs 1 a) =
      (fun a => (Algebra.TensorProduct.map (AlgHom.id A A) (restrictAlgHom π (𝒰.inter_le_inter_face r 2))).toLinearMap ∘ₗ cs 2 a) +
      (fun a => (Algebra.TensorProduct.map (AlgHom.id A A) (restrictAlgHom π (𝒰.inter_le_inter_face r 0))).toLinearMap ∘ₗ cs 0 a) := by
  letI := fun ℓ : Fin 3 => algebraOfHom π (𝒰.inter (𝒰.face r ℓ))
  letI := algebraOfHom π (𝒰.inter r)
  funext a
  apply LinearMap.ext
  intro ξ
  simp only [Pi.add_apply, LinearMap.add_apply, LinearMap.coe_comp, Function.comp_apply, AlgHom.toLinearMap_apply]
  have h0 : (OModulePresheaf.unit (pullback.snd π (specMap R A))).d (𝒰.baseChange π A) 1 (γ a ξ) r = 0 := by
    have := hγ a ξ
    rw [LinearMap.mem_ker] at this
    rw [this]; rfl
  exact cocycle_transfer π 𝒰 A r σ hσ₁ hσ₂ (γ a ξ) h0 (fun ℓ => cs ℓ a ξ) (fun ℓ => hcs ℓ a ξ)

end P2mWs2RG2.Cocycle

namespace P2mWs2RG2
namespace Assembly

open IsLocalRing AlgebraicGeometry.SmallExtension GoodReductionJacobian NeronModelInfra

theorem rho_one_eq_of
    {T' : Type u} [CommRing T'] [IsLocalRing T'] [IsArtinianRing T']
    (I : Ideal T') (hI : I ≤ maximalIdeal T') (hsmall : I * maximalIdeal T' = ⊥)
    (V : Type u) [AddCommGroup V] [Module (ResidueField T') V] [Module (ResidueField T')ᵐᵒᵖ V]
    [IsCentralScalar (ResidueField T') V] [Module.Finite (ResidueField T') V]
    [Module T' V] [IsScalarTower T' (ResidueField T') V]
    (ι : V →ₗ[T'] T') (hι : Function.Injective ι) (hιI : LinearMap.range ι = Submodule.restrictScalars T' I)
    {Y : Scheme.{u}} (qY : Y ⟶ Spec (CommRingCat.of T')) (U : Y.Opens) (hU : IsAffineOpen U)
    (hflat : letI := algebraOfHom qY U; Module.Flat T' Γ(Y, U))
    (hincl : letI := algebraOfHom qY U; hU.fromSpec ≫ qY = Spec.map (CommRingCat.ofHom (algebraMap T' Γ(Y, U))))
    {Ak : Scheme.{u}} (xk : Ak ⟶ Spec (CommRingCat.of (ResidueField T'))) (Lk : RelativeGroupLaw (ResidueField T') xk)
    (ak : Ak ⟶ Y) (hak : IsPullback ak xk qY (Spec.map (CommRingCat.ofHom (residue T'))))
    (Ue : Ak.Opens) (hUe : IsAffineOpen Ue)
    (e₁ : Spec (CommRingCat.of (ResidueField T')) ⟶ (Ue : Scheme.{u})) (he₁ : e₁ ≫ Ue.ι = (Lk.one (𝟙 _)).1)
    (ρ : Fin 3 → ((U : Scheme.{u}) ⟶ (U : Scheme.{u})))
    (hρB : ∀ ℓ : Fin 3, ρ ℓ ≫ U.ι ≫ qY = U.ι ≫ qY)
    (hagree : letI := algebraOfHom qY U
      ∀ ℓ : Fin 3, Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.map (algebraMap T' Γ(Y, U))))) ≫ hU.isoSpec.inv ≫ ρ ℓ =
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.map (algebraMap T' Γ(Y, U))))) ≫ hU.isoSpec.inv)
    (c₁ c₂ c₀ : letI := algebraOfHom qY U
      Γ(Ak, Ue) → (Module.Dual (ResidueField T') V →ₗ[ResidueField T'] (ResidueField T' ⊗[T'] Γ(Y, U))))
    (h₁ : letI := algebraOfHom qY U
      IsTangentCoordsOfPairAt I V ι Γ(Y, U) hU.fromSpec (hU.isoSpec.inv ≫ ρ 1 ≫ U.ι) xk Lk ak Ue c₁)
    (h₂ : letI := algebraOfHom qY U
      IsTangentCoordsOfPairAt I V ι Γ(Y, U) hU.fromSpec (hU.isoSpec.inv ≫ ρ 2 ≫ U.ι) xk Lk ak Ue c₂)
    (h₀ : letI := algebraOfHom qY U
      IsTangentCoordsOfPairAt I V ι Γ(Y, U) (hU.isoSpec.inv ≫ ρ 2 ≫ U.ι) (hU.isoSpec.inv ≫ ρ 2 ≫ ρ 0 ≫ U.ι) xk Lk ak Ue c₀)
    (hcyc : c₁ = c₂ + c₀) :
    ρ 1 = ρ 2 ≫ ρ 0 := by
  classical
  letI := algebraOfHom qY U
  haveI := hflat

  have hinv : hU.isoSpec.inv ≫ U.ι = hU.fromSpec := hU.isoSpec_inv_ι
  have hover : ∀ (g : (U : Scheme.{u}) ⟶ (U : Scheme.{u})), g ≫ U.ι ≫ qY = U.ι ≫ qY →
      (hU.isoSpec.inv ≫ g ≫ U.ι) ≫ qY = Spec.map (CommRingCat.ofHom (algebraMap T' Γ(Y, U))) := by
    intro g hg
    rw [Category.assoc, Category.assoc, hg, ← Category.assoc, hinv, hincl]
  have hov1 := hover (ρ 1) (hρB 1)
  have hov2 := hover (ρ 2) (hρB 2)
  have hov20 : (hU.isoSpec.inv ≫ ρ 2 ≫ ρ 0 ≫ U.ι) ≫ qY = Spec.map (CommRingCat.ofHom (algebraMap T' Γ(Y, U))) := by
    have := hover (ρ 2 ≫ ρ 0) (by rw [Category.assoc, hρB 0, hρB 2])
    simpa only [Category.assoc] using this

  have hag : ∀ ℓ : Fin 3, Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.map (algebraMap T' Γ(Y, U))))) ≫ hU.fromSpec =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.map (algebraMap T' Γ(Y, U))))) ≫ hU.isoSpec.inv ≫ ρ ℓ ≫ U.ι := by
    intro ℓ
    rw [← hinv, show Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.map (algebraMap T' Γ(Y, U))))) ≫ hU.isoSpec.inv ≫ ρ ℓ ≫ U.ι =
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.map (algebraMap T' Γ(Y, U))))) ≫ hU.isoSpec.inv ≫ ρ ℓ) ≫ U.ι by
        simp only [Category.assoc], hagree ℓ, Category.assoc]
  have hag20' : Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.map (algebraMap T' Γ(Y, U))))) ≫ hU.isoSpec.inv ≫ ρ 2 ≫ ρ 0 =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.map (algebraMap T' Γ(Y, U))))) ≫ hU.isoSpec.inv := by
    calc Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.map (algebraMap T' Γ(Y, U))))) ≫ hU.isoSpec.inv ≫ ρ 2 ≫ ρ 0
        = (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.map (algebraMap T' Γ(Y, U))))) ≫ hU.isoSpec.inv ≫ ρ 2) ≫ ρ 0 := by
          simp only [Category.assoc]
      _ = (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.map (algebraMap T' Γ(Y, U))))) ≫ hU.isoSpec.inv) ≫ ρ 0 := by
          rw [hagree 2]
      _ = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.map (algebraMap T' Γ(Y, U))))) ≫ hU.isoSpec.inv := by
          rw [Category.assoc, hagree 0]
  have hag20 : Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.map (algebraMap T' Γ(Y, U))))) ≫ hU.fromSpec =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.map (algebraMap T' Γ(Y, U))))) ≫ hU.isoSpec.inv ≫ ρ 2 ≫ ρ 0 ≫ U.ι := by
    rw [← hinv, show Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.map (algebraMap T' Γ(Y, U))))) ≫ hU.isoSpec.inv ≫ ρ 2 ≫ ρ 0 ≫ U.ι =
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.map (algebraMap T' Γ(Y, U))))) ≫ hU.isoSpec.inv ≫ ρ 2 ≫ ρ 0) ≫ U.ι by
        simp only [Category.assoc], hag20', Category.assoc]
  have hag2to20 : Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.map (algebraMap T' Γ(Y, U))))) ≫ (hU.isoSpec.inv ≫ ρ 2 ≫ U.ι) =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.map (algebraMap T' Γ(Y, U))))) ≫ (hU.isoSpec.inv ≫ ρ 2 ≫ ρ 0 ≫ U.ι) := by
    rw [← hag 2, hag20]

  obtain ⟨c₃, hc₃⟩ := AlgebraicGeometry.SmallExtension.exists_isTangentCoordsOfPairAt I hI hsmall V ι hι hιI Γ(Y, U) qY
    hU.fromSpec hincl xk Lk ak hak Ue hUe e₁ he₁ (hU.isoSpec.inv ≫ ρ 2 ≫ ρ 0 ≫ U.ι) hov20 hag20
  have hsum := AlgebraicGeometry.SmallExtension.isTangentCoordsOfPairAt_add I hI hsmall V ι hι hιI Γ(Y, U) qY
    hU.fromSpec (hU.isoSpec.inv ≫ ρ 2 ≫ U.ι) (hU.isoSpec.inv ≫ ρ 2 ≫ ρ 0 ≫ U.ι) hincl hov2 hov20 (hag 2) hag2to20
    xk Lk ak hak Ue hUe e₁ he₁ c₂ c₀ c₃ h₂ h₀ hc₃
  rw [← hcyc] at hsum
  rw [hsum] at hc₃
  have heq := AlgebraicGeometry.SmallExtension.eq_of_isTangentCoordsOfPairAt_of_isTangentCoordsOfPairAt I hI hsmall V ι hι hιI
    Γ(Y, U) qY hU.fromSpec hincl xk Lk ak hak Ue hUe e₁ he₁ (hU.isoSpec.inv ≫ ρ 1 ≫ U.ι) (hU.isoSpec.inv ≫ ρ 2 ≫ ρ 0 ≫ U.ι)
    hov1 hov20 (hag 1) hag20 c₁ h₁ hc₃
  rw [← cancel_epi hU.isoSpec.inv, ← cancel_mono U.ι]
  simpa only [Category.assoc] using heq

end P2mWs2RG2.Assembly

open P2mWs2RG2 in
theorem solution
    {q : ℕ} [Fact q.Prime]
    (B B₁ : Type) [CommRing B] [IsLocalRing B] [IsArtinianRing B] [IsAlgClosed (ResidueField B)]
    [CommRing B₁] [Algebra B B₁]
    (hπ : Function.Surjective (algebraMap B B₁)) (hker : IsNilpotent (RingHom.ker (algebraMap B B₁)))
    (hsmall : RingHom.ker (algebraMap B B₁) * maximalIdeal B = ⊥)
    (hq : IsNilpotent ((q : ℕ) : B))
    {A₁ : Scheme.{0}} (f₁ : A₁ ⟶ Spec (CommRingCat.of B₁)) (L₁ : RelativeGroupLaw B₁ f₁) (hc₁ : L₁.IsCommutative)
    (h₁ : AbelianSchemePropertyBundle B₁ f₁)
    (F : MvFormalGroup 2 B) [F.IsComm]
    (θ₁ : RelativeGroupLaw.FormalCoordinates f₁ 2) (hθ₁ : L₁.IsFormalCoordinates (F.map (algebraMap B B₁)) θ₁)
    (hinf₁ : ∀ (C : Type) [CommRing C] [Algebra B₁ C] (m : ℕ) (P : SchemeHomOver (Scheme.specOver (𝒪 := B₁) C) f₁),
      nsmulPt L₁ (Scheme.specOver (𝒪 := B₁) C) (q ^ m) P = L₁.one (Scheme.specOver (𝒪 := B₁) C) →
        ∃ J : Ideal C, IsNilpotent J ∧ L₁.IsInfinitesimal J P)
    (hheight : ∀ (k : Type) [Field k] (ρ : B →+* k), Function.Surjective ρ →
      Module.finrank k (MvPowerSeries (Fin 2) k ⧸ Ideal.span (Set.range ((F.map ρ).nthSeries q))) = q ^ 4)
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
    (hτB : ∀ s : 𝒰.Idx 1, (τ s).hom ≫ (𝒰.inter s).ι ≫ D₀.f = (𝒰.inter s).ι ≫ D₀.f)
    (hτg : ∀ s : 𝒰.Idx 1, (D₀.g ∣_ 𝒰.inter s) ≫ (τ s).hom = D₀.g ∣_ 𝒰.inter s)
    (hτc : ∀ s : 𝒰.Idx 1,
        letI := algebraOfHom D₀.f (𝒰.inter s)
        letI := algebraOfHom (pullback.snd D₀.f (specMap B (ResidueField B))) ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)
        ∃ cs : Γ((pullback D₀.f (specMap B (ResidueField B))), ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)) → (Module.Dual (ResidueField B) V →ₗ[(ResidueField B)] ((ResidueField B) ⊗[B] Γ(D₀.A, 𝒰.inter s))),
          AlgebraicGeometry.SmallExtension.IsTangentCoordsOfPairAt (RingHom.ker (algebraMap B B₁)) V ι Γ(D₀.A, 𝒰.inter s)
            ((Scheme.OrderedAffineCover.isAffineOpen_inter D₀.f 𝒰 s).fromSpec)
            ((Scheme.OrderedAffineCover.isAffineOpen_inter D₀.f 𝒰 s).isoSpec.inv ≫ (τ s).hom ≫ (𝒰.inter s).ι)
            (pullback.snd D₀.f (specMap B (ResidueField B))) (RelativeGroupLaw.baseChange (specMap B (ResidueField B)) D₀.L) (pullback.fst D₀.f (specMap B (ResidueField B))) ((𝒰.baseChange D₀.f (ResidueField B)).U i₀) cs ∧
          ∀ (a : Γ((pullback D₀.f (specMap B (ResidueField B))), ((𝒰.baseChange D₀.f (ResidueField B)).U i₀))) (ξ : Module.Dual (ResidueField B) V),
            σ s (cs a ξ) = (c : Γ((pullback D₀.f (specMap B (ResidueField B))), ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)) →ₗ[(ResidueField B)] (Module.Dual (ResidueField B) V →ₗ[(ResidueField B)] (OModulePresheaf.unit (pullback.snd D₀.f (specMap B (ResidueField B)))).cochain (𝒰.baseChange D₀.f (ResidueField B)) 1)) a ξ s) :
    ∀ r : 𝒰.Idx 2, ∃ ρ : Fin 3 → ((↑(𝒰.inter r) : Scheme.{0}) ⟶ ↑(𝒰.inter r)),
        (∀ j : Fin 3, ρ j ≫ D₀.A.homOfLE (𝒰.inter_le_inter_face r j)
            = D₀.A.homOfLE (𝒰.inter_le_inter_face r j) ≫ (τ (𝒰.face r j)).hom) ∧
        ρ 1 = ρ 2 ≫ ρ 0 := by
  classical
  intro r
  letI := algebraOfHom (pullback.snd D₀.f (specMap B (ResidueField B))) ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)
  refine ⟨fun ℓ => P2mWs2RG2.ρ hπ hker D₀ 𝒰 τ hτg r ℓ, fun j => P2mWs2RG2.ρ_fac hπ hker D₀ 𝒰 τ hτg r j, ?_⟩

  have hW := fun ℓ : Fin 3 => hτc (𝒰.face r ℓ)
  choose cs hcs1 hcs2 using hW
  have hcyc := P2mWs2RG2.Cocycle.cocycle_coords D₀.f 𝒰 (ResidueField B) r (fun ℓ => σ (𝒰.face r ℓ))
    (fun ℓ x => hσ₁ (𝒰.face r ℓ) x) (fun ℓ a => hσ₂ (𝒰.face r ℓ) a)
    (fun a ξ => (c : Γ((pullback D₀.f (specMap B (ResidueField B))), ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)) →ₗ[(ResidueField B)]
      (Module.Dual (ResidueField B) V →ₗ[(ResidueField B)]
        (OModulePresheaf.unit (pullback.snd D₀.f (specMap B (ResidueField B)))).cochain (𝒰.baseChange D₀.f (ResidueField B)) 1)) a ξ)
    hc cs (fun ℓ a ξ => hcs2 ℓ a ξ)
  exact P2mWs2RG2.Assembly.rho_one_eq_of (RingHom.ker (algebraMap B B₁)) hI hsmall V ι hι hιI D₀.f (𝒰.inter r)
    (P2mWs2RG2.isAffineOpen_inter3 D₀ 𝒰 r) (P2mWs2RG2.flat_inter D₀ 𝒰 r) (P2mWs2RG2.fromSpec_over D₀ 𝒰 r)
    (pullback.snd D₀.f (specMap B (ResidueField B))) (RelativeGroupLaw.baseChange (specMap B (ResidueField B)) D₀.L)
    (pullback.fst D₀.f (specMap B (ResidueField B))) (P2mWs2RG2.hak_pullback D₀)
    ((𝒰.baseChange D₀.f (ResidueField B)).U i₀) ((𝒰.baseChange D₀.f (ResidueField B)).isAffineOpen i₀) e₁ he₁
    (fun ℓ => P2mWs2RG2.ρ hπ hker D₀ 𝒰 τ hτg r ℓ) (fun ℓ => P2mWs2RG2.ρ_over hπ hker D₀ 𝒰 τ hτB hτg r ℓ)
    (fun ℓ => P2mWs2RG2.specMk_isoSpecInv_ρ hπ hker D₀ 𝒰 τ hτg r ℓ) _ _ _
    (P2mWs2RG2.coords_restrict hπ hker hsmall hI V ι hι hιI D₀ 𝒰 i₀ τ hτg r 1 (cs 1) (hcs1 1))
    (P2mWs2RG2.coords_restrict hπ hker hsmall hI V ι hι hιI D₀ 𝒰 i₀ τ hτg r 2 (cs 2) (hcs1 2))
    (P2mWs2RG2.coords_precomp hπ hker hsmall hI V ι hι hιI D₀ 𝒰 i₀ τ hτB hτg r (cs 0) (hcs1 0))
    hcyc

end S_GoodReductionJacobian_BareDeformation_exists_restrict_comp_eq_of_isTangentCoordsOfPairAt_of_d_eq_zero
end P2MW
export P2MW.S_GoodReductionJacobian_BareDeformation_exists_restrict_comp_eq_of_isTangentCoordsOfPairAt_of_d_eq_zero (solution)
