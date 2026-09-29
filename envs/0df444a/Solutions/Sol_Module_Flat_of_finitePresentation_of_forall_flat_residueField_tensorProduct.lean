-- Prove2me | solution 1 for Module.Flat.of_finitePresentation_of_forall_flat_residueField_tensorProduct
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/2fbaab72-afcf-5821-830a-bdd8510a4c63

import Mathlib
import Theorems.Thm_IsLocalRing_flat_of_isScalarTower_of_flat_of_flat_quotient_maximalIdeal_map
import Theorems.Thm_Module_Flat_exists_fg_subalgebra_flat_localization_tensorProduct
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Module_Flat_of_finitePresentation_of_forall_flat_residueField_tensorProduct

open TensorProduct

namespace FibreFlatSol

theorem flat_of_ringEquiv {R R' S S' : Type*} [CommRing R] [CommRing R'] [CommRing S]
    [CommRing S'] [Algebra R S] [Algebra R' S'] (eR : R ≃+* R') (eS : S ≃+* S')
    (h : ∀ r, eS (algebraMap R S r) = algebraMap R' S' (eR r)) [Module.Flat R S] :
    Module.Flat R' S' := by
  letI iRR' : Algebra R R' := eR.toRingHom.toAlgebra
  letI iRS' : Algebra R S' := ((algebraMap R' S').comp eR.toRingHom).toAlgebra
  haveI : IsScalarTower R R' S' := IsScalarTower.of_algebraMap_eq' rfl

  let eL : S ≃ₗ[R] S' :=
    { eS with
      map_smul' := fun r s => by
        change eS (r • s) = r • eS s
        simp only [Algebra.smul_def]
        rw [map_mul, h]
        rfl }
  haveI : Module.Flat R S' := Module.Flat.of_linearEquiv eL.symm
  haveI : IsLocalization (⊥ : Submonoid R) R' := by
    refine IsLocalization.of_le_isUnit_of_bijective ?_ eR.bijective
    rintro _ ⟨x, hx, rfl⟩
    rw [SetLike.mem_coe, Submonoid.mem_bot] at hx
    subst hx
    simp
  exact (Module.flat_iff_of_isLocalization (S := R') (p := (⊥ : Submonoid R)) (M := S')).mpr ‹_›

theorem flat_localization_of_ringEquiv {R R' B B' : Type*} [CommRing R] [CommRing R']
    [CommRing B] [CommRing B'] [Algebra R B] [Algebra R' B'] (eR : R ≃+* R') (e : B ≃+* B')
    (h : ∀ r, e (algebraMap R B r) = algebraMap R' B' (eR r)) (P : Ideal B) [P.IsPrime]
    (P' : Ideal B') [P'.IsPrime] (hP : P = P'.comap e.toRingHom)
    [Module.Flat R (Localization.AtPrime P)] :
    Module.Flat R' (Localization.AtPrime P') := by
  have H : (P.primeCompl).map e.toMonoidHom = P'.primeCompl := by
    ext x
    simp only [Submonoid.mem_map, Ideal.mem_primeCompl_iff]
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa [hP, Ideal.mem_comap] using hy
    · intro hx
      refine ⟨e.symm x, ?_, by simp⟩
      intro hx'
      apply hx
      rw [hP] at hx'
      have : e.toRingHom (e.symm x) ∈ P' := Ideal.mem_comap.mp hx'
      simpa using this
  let eL : Localization.AtPrime P ≃+* Localization.AtPrime P' :=
    IsLocalization.ringEquivOfRingEquiv (Localization.AtPrime P) (Localization.AtPrime P') e H
  refine flat_of_ringEquiv (S := Localization.AtPrime P) eR eL fun r => ?_
  rw [IsScalarTower.algebraMap_apply R B (Localization.AtPrime P),
    IsScalarTower.algebraMap_apply R' B' (Localization.AtPrime P')]
  change eL (algebraMap B _ (algebraMap R B r)) = _
  rw [show eL (algebraMap B _ (algebraMap R B r)) = algebraMap B' _ (e (algebraMap R B r))
    from IsLocalization.ringEquivOfRingEquiv_eq H _]
  exact congrArg _ (h r)

theorem flat_of_flat_of_isLocalization {C D : Type*} (C' D' : Type*) [CommRing C] [CommRing D]
    [CommRing C'] [CommRing D'] [Algebra C C'] [Algebra D D'] [Algebra C' D']
    (M : Submonoid C) [IsLocalization M C'] (N : Submonoid D) [IsLocalization N D']
    (f : C →+* D) (hf : f.Flat)
    (hcomm : (algebraMap D D').comp f = (algebraMap C' D').comp (algebraMap C C')) :
    Module.Flat C' D' := by
  algebraize [f, (algebraMap D D').comp f]
  haveI : IsScalarTower C C' D' := IsScalarTower.of_algebraMap_eq' hcomm
  haveI : Module.Flat D D' := IsLocalization.flat D' N
  haveI : Module.Flat C D' := Module.Flat.trans C D D'
  exact (Module.flat_iff_of_isLocalization (S := C') (p := M) (M := D')).mpr this

section FibreLoc

variable {R₁ A₁ : Type*} [CommRing R₁] [CommRing A₁] [Algebra R₁ A₁]
  (p : Ideal R₁) [p.IsPrime] (P : Ideal A₁) [P.IsPrime]

local notation "R_[" p "]" => Localization.AtPrime p
local notation "κ_[" p "]" =>
  Localization.AtPrime p ⧸ IsLocalRing.maximalIdeal (Localization.AtPrime p)

local notation "T_[" p ", " P "]" =>
  Localization.AtPrime P ⧸ Ideal.map (algebraMap (Localization.AtPrime p) (Localization.AtPrime P))
    (IsLocalRing.maximalIdeal (Localization.AtPrime p))

attribute [local instance] Algebra.TensorProduct.rightAlgebra

variable [P.LiesOver p] [Algebra R_[p] R_[P]] [Localization.AtPrime.IsLiesOverAlgebra p P]

theorem isScalarTower_quot_fibre : IsScalarTower R₁ κ_[p] T_[p, P] :=
  IsScalarTower.of_algebraMap_eq (R := R₁) (S := κ_[p]) (A := T_[p, P]) fun r => by
    symm
    rw [IsScalarTower.algebraMap_apply R₁ R_[p] κ_[p], Ideal.Quotient.algebraMap_eq,
      Ideal.Quotient.algebraMap_quotient_map_quotient,
      ← IsScalarTower.algebraMap_apply R₁ R_[p] R_[P],
      IsScalarTower.algebraMap_apply R₁ R_[P] T_[p, P], Ideal.Quotient.algebraMap_eq]

attribute [local instance] isScalarTower_quot_fibre

noncomputable def fibToQuot : κ_[p] ⊗[R₁] A₁ →ₐ[R₁] T_[p, P] :=
  Algebra.TensorProduct.lift (IsScalarTower.toAlgHom R₁ _ _) (IsScalarTower.toAlgHom R₁ A₁ _)
    fun _ _ => .all _ _

@[scoped simp] lemma fibToQuot_tmul (x : κ_[p]) (a : A₁) :
    fibToQuot p P (x ⊗ₜ a) = algebraMap _ _ x * algebraMap A₁ _ a :=
  Algebra.TensorProduct.lift_tmul ..

noncomputable abbrev fibToQuotAlgebra : Algebra (κ_[p] ⊗[R₁] A₁) T_[p, P] :=
  (fibToQuot p P : κ_[p] ⊗[R₁] A₁ →+* T_[p, P]).toAlgebra

lemma isPushout_localization_self : Algebra.IsPushout R₁ R_[p] R_[P] R_[P] := by
  haveI : IsLocalization (Algebra.algebraMapSubmonoid R_[P] p.primeCompl) R_[P] := by
    refine IsLocalization.of_le_isUnit ?_
    rintro _ ⟨r, hr, rfl⟩
    rw [IsScalarTower.algebraMap_apply R₁ A₁ R_[P]]
    refine IsLocalization.map_units (M := P.primeCompl) R_[P] ⟨algebraMap R₁ A₁ r, ?_⟩
    show algebraMap R₁ A₁ r ∉ P
    have : p = P.under R₁ := Ideal.LiesOver.over
    intro h; exact hr (this ▸ h)
  exact (Algebra.isPushout_of_isLocalization p.primeCompl R_[p] R_[P] R_[P]).symm

omit [Algebra R₁ A₁] [P.LiesOver p] [Localization.AtPrime.IsLiesOverAlgebra p P] in

lemma isPushout_quot_fibre : Algebra.IsPushout R_[p] κ_[p] R_[P] T_[p, P] := by
  refine Algebra.IsPushout.of_equiv (S' := κ_[p] ⊗[R_[p]] R_[P])
    (Algebra.TensorProduct.quotIdealMapEquivQuotTensor R_[P]
      (IsLocalRing.maximalIdeal R_[p])).symm ?_
  ext s
  simp only [RingHom.coe_comp, Function.comp_apply]
  change (Algebra.TensorProduct.quotIdealMapEquivQuotTensor R_[P]
      (IsLocalRing.maximalIdeal R_[p])).symm ((1 : _) ⊗ₜ s) = _
  rw [AlgEquiv.symm_apply_eq]
  simp

lemma isLocalization_fibToQuot :
    letI := fibToQuotAlgebra p P
    @IsLocalization (κ_[p] ⊗[R₁] A₁) _ (Algebra.algebraMapSubmonoid (κ_[p] ⊗[R₁] A₁) P.primeCompl)
      T_[p, P] _ _ := by
  letI := fibToQuotAlgebra p P
  haveI : IsScalarTower A₁ (κ_[p] ⊗[R₁] A₁) T_[p, P] :=
    IsScalarTower.of_algebraMap_eq (R := A₁) (S := κ_[p] ⊗[R₁] A₁) (A := T_[p, P]) fun a => by
      change _ = fibToQuot p P ((1 : κ_[p]) ⊗ₜ a)
      simp
  haveI : IsScalarTower κ_[p] (κ_[p] ⊗[R₁] A₁) T_[p, P] :=
    IsScalarTower.of_algebraMap_eq (R := κ_[p]) (S := κ_[p] ⊗[R₁] A₁) (A := T_[p, P]) fun x => by
      change _ = fibToQuot p P (x ⊗ₜ (1 : A₁))
      simp
  haveI : IsScalarTower R₁ (κ_[p] ⊗[R₁] A₁) T_[p, P] :=
    IsScalarTower.of_algebraMap_eq (R := R₁) (S := κ_[p] ⊗[R₁] A₁) (A := T_[p, P])
      fun r => ((fibToQuot p P).commutes r).symm
  rw [Algebra.isLocalization_iff_isPushout P.primeCompl R_[P],
    Algebra.IsPushout.comm, ← Algebra.IsPushout.comp_iff R₁ A₁ κ_[p] (κ_[p] ⊗[R₁] A₁),
    Algebra.IsPushout.comm]
  haveI := isPushout_localization_self p P
  rw [Algebra.IsPushout.comp_iff R₁ R_[p] R_[P] R_[P]]
  exact isPushout_quot_fibre p P

end FibreLoc

section LayerI

attribute [local instance] Algebra.TensorProduct.rightAlgebra isScalarTower_quot_fibre

set_option maxHeartbeats 3200000 in

theorem flat_localization_of_flat_fibre_of_isNoetherianRing
    {R₁ A₁ B₁ : Type} [CommRing R₁] [CommRing A₁] [CommRing B₁] [Algebra R₁ A₁] [Algebra R₁ B₁]
    [Algebra A₁ B₁] [IsScalarTower R₁ A₁ B₁] [IsNoetherianRing R₁] [Algebra.FiniteType R₁ A₁]
    [Algebra.FiniteType R₁ B₁] (Q : Ideal B₁) [Q.IsPrime]
    [Module.Flat R₁ (Localization.AtPrime Q)] (p : Ideal R₁) [p.IsPrime] (hp : p = Q.under R₁)
    (hfib : (Algebra.TensorProduct.map (AlgHom.id p.ResidueField p.ResidueField)
        (IsScalarTower.toAlgHom R₁ A₁ B₁)).toRingHom.Flat) :
    Module.Flat A₁ (Localization.AtPrime Q) := by
  subst hp
  set p : Ideal R₁ := Q.under R₁ with hp
  set P : Ideal A₁ := Q.under A₁ with hP
  haveI : P.LiesOver p := ⟨(Ideal.under_under (A := R₁) (B := A₁) Q).symm⟩
  letI := Localization.AtPrime.algebraOfLiesOver p P
  letI := Localization.AtPrime.algebraOfLiesOver P Q
  letI := Localization.AtPrime.algebraOfLiesOver p Q
  haveI : IsNoetherianRing A₁ := Algebra.FiniteType.isNoetherianRing R₁ A₁
  haveI : IsNoetherianRing B₁ := Algebra.FiniteType.isNoetherianRing R₁ B₁

  set Rp := Localization.AtPrime p
  set S := Localization.AtPrime P
  set S' := Localization.AtPrime Q
  set 𝔪 := IsLocalRing.maximalIdeal Rp
  set κ := Rp ⧸ 𝔪
  set T := S ⧸ 𝔪.map (algebraMap Rp S)
  set T' := S' ⧸ 𝔪.map (algebraMap Rp S')

  have hflat : Module.Flat Rp S' :=
    (Module.flat_iff_of_isLocalization (S := Rp) (p := p.primeCompl) (M := S')).mpr ‹_›

  letI iTT' : Algebra T T' :=
    Ideal.Quotient.algebraQuotientOfLEComap (Ideal.map_le_iff_le_comap.mp (le_of_eq
      (by rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq Rp S S'])))
  have key : Module.Flat T T' := by

    have hTT' : ∀ x : S, algebraMap T T' (Ideal.Quotient.mk _ x) =
        Ideal.Quotient.mk _ (algebraMap S S' x) := fun x => Ideal.quotientMap_mk ..
    haveI : IsScalarTower R₁ T T' :=
      IsScalarTower.of_algebraMap_eq (R := R₁) (S := T) (A := T') fun r => by
        rw [IsScalarTower.algebraMap_apply R₁ S T, Ideal.Quotient.algebraMap_eq, hTT',
          ← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply R₁ S' T',
          Ideal.Quotient.algebraMap_eq]
    haveI : IsScalarTower A₁ T T' :=
      IsScalarTower.of_algebraMap_eq (R := A₁) (S := T) (A := T') fun r => by
        rw [IsScalarTower.algebraMap_apply A₁ S T, Ideal.Quotient.algebraMap_eq, hTT',
          ← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply A₁ S' T',
          Ideal.Quotient.algebraMap_eq]
    haveI : IsScalarTower κ T T' :=
      IsScalarTower.of_algebraMap_eq (R := κ) (S := T) (A := T') fun x => by
        obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
        rw [Ideal.Quotient.algebraMap_quotient_map_quotient,
          Ideal.Quotient.algebraMap_quotient_map_quotient, hTT', ← IsScalarTower.algebraMap_apply]

    letI iFT : Algebra (κ ⊗[R₁] A₁) T := fibToQuotAlgebra p P
    letI iF'T' : Algebra (κ ⊗[R₁] B₁) T' := fibToQuotAlgebra p Q
    haveI hlocT := isLocalization_fibToQuot p P
    haveI hlocT' := isLocalization_fibToQuot p Q
    have hF : RingHom.Flat (R := κ ⊗[R₁] A₁) (S := κ ⊗[R₁] B₁)
        (Algebra.TensorProduct.map (AlgHom.id κ κ)
          (IsScalarTower.toAlgHom R₁ A₁ B₁)).toRingHom := by exact hfib
    have hcomp : (IsScalarTower.toAlgHom R₁ T T').comp (fibToQuot p P) =
        (fibToQuot p Q).comp
          ((Algebra.TensorProduct.map (AlgHom.id κ κ)
            (IsScalarTower.toAlgHom R₁ A₁ B₁)).restrictScalars R₁) := by
      apply Algebra.TensorProduct.ext'
      intro x a
      simp only [AlgHom.coe_comp, Function.comp_apply, AlgHom.coe_restrictScalars',
        Algebra.TensorProduct.map_tmul, AlgHom.coe_id, id_eq, IsScalarTower.coe_toAlgHom']
      rw [fibToQuot_tmul, fibToQuot_tmul, map_mul, ← IsScalarTower.algebraMap_apply,
        ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
    exact flat_of_flat_of_isLocalization (C := κ ⊗[R₁] A₁) (D := κ ⊗[R₁] B₁) T T'
      (Algebra.algebraMapSubmonoid (κ ⊗[R₁] A₁) P.primeCompl)
      (Algebra.algebraMapSubmonoid (κ ⊗[R₁] B₁) Q.primeCompl) _ hF
      (congrArg (fun f : κ ⊗[R₁] A₁ →ₐ[R₁] T' => (f : κ ⊗[R₁] A₁ →+* T')) hcomp).symm
  have hSS' : Module.Flat S S' :=
    IsLocalRing.flat_of_isScalarTower_of_flat_of_flat_quotient_maximalIdeal_map
      (R := Rp) (S := S) (S' := S') hflat key
  haveI : Module.Flat A₁ S := IsLocalization.flat S P.primeCompl
  exact Module.Flat.trans A₁ S S'

end LayerI

attribute [local instance] Algebra.TensorProduct.rightAlgebra

theorem isScalarTower_rightAlgebra_of_tower {R₀ R K A : Type*} [CommRing R₀] [CommRing R]
    [CommRing K] [CommRing A] [Algebra R K] [Algebra R A] [Algebra R₀ R] [Algebra R₀ K]
    [Algebra R₀ A] [IsScalarTower R₀ R K] [IsScalarTower R₀ R A] :
    IsScalarTower R₀ A (K ⊗[R] A) :=
  IsScalarTower.of_algebraMap_eq (R := R₀) (S := A) (A := K ⊗[R] A) fun r => by
    rw [IsScalarTower.algebraMap_apply R₀ R (K ⊗[R] A), IsScalarTower.algebraMap_apply R₀ R A,
      Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one (r := algebraMap R₀ R r),
      Algebra.TensorProduct.one_def]
    change _ = (1 : K) ⊗ₜ[R] ((algebraMap R₀ R r) • (1 : A))
    rw [tmul_smul]

section Descent

variable {R₁ R : Type*} [CommRing R₁] [CommRing R] [Algebra R₁ R] (p : Ideal R)
  {A₁ A B₁ B : Type*} [CommRing A₁] [CommRing A] [CommRing B₁] [CommRing B]
  [Algebra R₁ A₁] [Algebra R₁ B₁] [Algebra A₁ B₁] [IsScalarTower R₁ A₁ B₁]
  [Algebra R A] [Algebra R B] [Algebra A B] [IsScalarTower R A B]
  [Algebra R₁ A] [Algebra R₁ B] [IsScalarTower R₁ R A] [IsScalarTower R₁ R B]
  [Algebra A₁ A] [Algebra B₁ B] [IsScalarTower R₁ A₁ A] [IsScalarTower R₁ B₁ B]
  [Algebra A₁ B] [IsScalarTower A₁ A B] [IsScalarTower A₁ B₁ B]
  [Algebra.IsPushout R₁ R A₁ A] [Algebra.IsPushout R₁ R B₁ B] [p.IsPrime]

local notation "κ" => Ideal.ResidueField p
local notation "κ₁" => Ideal.ResidueField (Ideal.under R₁ p)
local notation "F₁" => Ideal.ResidueField (Ideal.under R₁ p) ⊗[R₁] A₁
local notation "F₁'" => Ideal.ResidueField (Ideal.under R₁ p) ⊗[R₁] B₁
local notation "F" => Ideal.ResidueField p ⊗[R] A
local notation "F'" => Ideal.ResidueField p ⊗[R] B

set_option maxHeartbeats 8000000 in

theorem flat_fibre_descent
    (hfib : (Algebra.TensorProduct.map (AlgHom.id p.ResidueField p.ResidueField)
      (IsScalarTower.toAlgHom R A B)).toRingHom.Flat) :
    (Algebra.TensorProduct.map
      (AlgHom.id (p.under R₁).ResidueField (p.under R₁).ResidueField)
        (IsScalarTower.toAlgHom R₁ A₁ B₁)).toRingHom.Flat := by

  let ι : κ₁ →ₐ[R₁] κ := Ideal.ResidueField.mapₐ (Ideal.under R₁ p) p (Algebra.ofId R₁ R) rfl
  letI iκ0 : Algebra κ₁ κ := RingHom.toAlgebra (R := κ₁) (S := κ) ι.toRingHom
  haveI tw0 : IsScalarTower R₁ κ₁ κ :=
    IsScalarTower.of_algebraMap_eq (R := R₁) (S := κ₁) (A := κ) fun r => (ι.commutes r).symm
  let f₁ : F₁ →ₐ[κ₁] F₁' :=
    Algebra.TensorProduct.map (AlgHom.id κ₁ κ₁) (IsScalarTower.toAlgHom R₁ A₁ B₁)
  let f : F →ₐ[κ] F' :=
    Algebra.TensorProduct.map (AlgHom.id κ κ) (IsScalarTower.toAlgHom R A B)
  letI ib1 : Algebra F₁ F₁' := RingHom.toAlgebra (R := F₁) (S := F₁') f₁.toRingHom
  letI ib2 : Algebra F F' := RingHom.toAlgebra (R := F) (S := F') f.toRingHom
  have hF : Module.Flat F F' := by exact hfib
  change Module.Flat F₁ F₁'

  haveI tw1 : IsScalarTower κ₁ F₁ F₁' :=
    IsScalarTower.of_algebraMap_eq (R := κ₁) (S := F₁) (A := F₁') fun r => (f₁.commutes r).symm
  haveI tw2 : IsScalarTower κ F F' :=
    IsScalarTower.of_algebraMap_eq (R := κ) (S := F) (A := F') fun r => (f.commutes r).symm
  haveI tw3 : IsScalarTower R₁ F₁ F₁' :=
    IsScalarTower.of_algebraMap_eq (R := R₁) (S := F₁) (A := F₁') fun r => by
      rw [IsScalarTower.algebraMap_apply R₁ κ₁ F₁, IsScalarTower.algebraMap_apply R₁ κ₁ F₁',
        ← IsScalarTower.algebraMap_apply κ₁ F₁ F₁']
  haveI tw4 : IsScalarTower R F F' :=
    IsScalarTower.of_algebraMap_eq (R := R) (S := F) (A := F') fun r => by
      rw [IsScalarTower.algebraMap_apply R κ F, IsScalarTower.algebraMap_apply R κ F',
        ← IsScalarTower.algebraMap_apply κ F F']
  haveI tw5 : IsScalarTower R₁ A F := isScalarTower_rightAlgebra_of_tower
  haveI tw6 : IsScalarTower R₁ B F' := isScalarTower_rightAlgebra_of_tower
  haveI tw7 : IsScalarTower R₁ A B :=
    IsScalarTower.of_algebraMap_eq (R := R₁) (S := A) (A := B) fun r => by
      rw [IsScalarTower.algebraMap_apply R₁ R A, IsScalarTower.algebraMap_apply R₁ R B,
        ← IsScalarTower.algebraMap_apply R A B]

  let g : F₁ →ₐ[R₁] F :=
    Algebra.TensorProduct.lift ((IsScalarTower.toAlgHom R₁ κ F).comp ι)
      ((IsScalarTower.toAlgHom R₁ A F).comp (IsScalarTower.toAlgHom R₁ A₁ A)) fun _ _ => .all _ _
  let g' : F₁' →ₐ[R₁] F' :=
    Algebra.TensorProduct.lift ((IsScalarTower.toAlgHom R₁ κ F').comp ι)
      ((IsScalarTower.toAlgHom R₁ B F').comp (IsScalarTower.toAlgHom R₁ B₁ B)) fun _ _ => .all _ _
  have hg : ∀ (x : κ₁) (a : A₁), g (x ⊗ₜ a) = algebraMap κ F (ι x) * algebraMap A F
      (algebraMap A₁ A a) := fun x a => Algebra.TensorProduct.lift_tmul ..
  have hg' : ∀ (x : κ₁) (b : B₁), g' (x ⊗ₜ b) = algebraMap κ F' (ι x) * algebraMap B F'
      (algebraMap B₁ B b) := fun x b => Algebra.TensorProduct.lift_tmul ..

  haveI : SMulCommClass R κ₁ κ :=
    ⟨fun r x k => by simp only [Algebra.smul_def]; ring⟩
  letI ia1 : Algebra κ₁ F := Algebra.TensorProduct.leftAlgebra
  letI ia2 : Algebra κ₁ F' := Algebra.TensorProduct.leftAlgebra
  letI ia3 : Algebra F₁ F := RingHom.toAlgebra (R := F₁) (S := F) g.toRingHom
  letI ia4 : Algebra F₁' F' := RingHom.toAlgebra (R := F₁') (S := F') g'.toRingHom
  letI ia5 : Algebra F₁ F' :=
    RingHom.toAlgebra (R := F₁) (S := F') ((algebraMap F F').comp (algebraMap F₁ F))
  letI ia6 : Algebra A₁ F :=
    RingHom.toAlgebra (R := A₁) (S := F) ((algebraMap A F).comp (algebraMap A₁ A))
  letI ia7 : Algebra B₁ F' :=
    RingHom.toAlgebra (R := B₁) (S := F') ((algebraMap B F').comp (algebraMap B₁ B))
  letI ia8 : Algebra A₁ F₁' :=
    RingHom.toAlgebra (R := A₁) (S := F₁') ((algebraMap B₁ F₁').comp (algebraMap A₁ B₁))
  letI ia9 : Algebra A F' :=
    RingHom.toAlgebra (R := A) (S := F') ((algebraMap B F').comp (algebraMap A B))
  letI ia10 : Algebra A₁ F' :=
    RingHom.toAlgebra (R := A₁) (S := F') ((algebraMap A F').comp (algebraMap A₁ A))

  haveI : IsScalarTower F₁ F F' := IsScalarTower.of_algebraMap_eq' rfl
  haveI : IsScalarTower A₁ A F := IsScalarTower.of_algebraMap_eq' rfl
  haveI : IsScalarTower B₁ B F' := IsScalarTower.of_algebraMap_eq' rfl
  haveI : IsScalarTower A₁ B₁ F₁' := IsScalarTower.of_algebraMap_eq' rfl
  haveI : IsScalarTower A B F' := IsScalarTower.of_algebraMap_eq' rfl
  haveI : IsScalarTower A₁ A F' := IsScalarTower.of_algebraMap_eq' rfl
  haveI tw8 : IsScalarTower κ₁ κ F := inferInstance
  haveI tw9 : IsScalarTower κ₁ κ F' := inferInstance
  haveI tw10 : IsScalarTower R₁ κ₁ F := inferInstance
  haveI tw11 : IsScalarTower R₁ κ₁ F' := inferInstance
  haveI tw12 : IsScalarTower A₁ F₁ F₁' :=
    IsScalarTower.of_algebraMap_eq (R := A₁) (S := F₁) (A := F₁') fun a => by
      change (1 : κ₁) ⊗ₜ[R₁] (algebraMap A₁ B₁ a) = f₁ ((1 : κ₁) ⊗ₜ[R₁] a)
      simp [f₁]
  haveI tw13 : IsScalarTower A F F' :=
    IsScalarTower.of_algebraMap_eq (R := A) (S := F) (A := F') fun a => by
      change (1 : κ) ⊗ₜ[R] (algebraMap A B a) = f ((1 : κ) ⊗ₜ[R] a)
      simp [f]
  haveI : IsScalarTower R₁ F₁ F :=
    IsScalarTower.of_algebraMap_eq (R := R₁) (S := F₁) (A := F) fun r => (g.commutes r).symm
  haveI : IsScalarTower R₁ F₁' F' :=
    IsScalarTower.of_algebraMap_eq (R := R₁) (S := F₁') (A := F') fun r => (g'.commutes r).symm
  haveI tw14 : IsScalarTower κ₁ F₁ F :=
    IsScalarTower.of_algebraMap_eq (R := κ₁) (S := F₁) (A := F) fun x => by
      change _ = g (x ⊗ₜ (1 : A₁))
      rw [hg, map_one, map_one, mul_one, IsScalarTower.algebraMap_apply κ₁ κ F]; rfl
  haveI tw15 : IsScalarTower κ₁ F₁' F' :=
    IsScalarTower.of_algebraMap_eq (R := κ₁) (S := F₁') (A := F') fun x => by
      change _ = g' (x ⊗ₜ (1 : B₁))
      rw [hg', map_one, map_one, mul_one, IsScalarTower.algebraMap_apply κ₁ κ F']; rfl
  haveI tw16 : IsScalarTower A₁ F₁ F :=
    IsScalarTower.of_algebraMap_eq (R := A₁) (S := F₁) (A := F) fun a => by
      change _ = g ((1 : κ₁) ⊗ₜ a)
      rw [hg, map_one, map_one, one_mul]; rfl
  haveI tw17 : IsScalarTower B₁ F₁' F' :=
    IsScalarTower.of_algebraMap_eq (R := B₁) (S := F₁') (A := F') fun b => by
      change _ = g' ((1 : κ₁) ⊗ₜ b)
      rw [hg', map_one, map_one, one_mul]; rfl
  haveI tw18 : IsScalarTower R₁ A₁ F :=
    IsScalarTower.of_algebraMap_eq (R := R₁) (S := A₁) (A := F) fun r => by
      rw [IsScalarTower.algebraMap_apply A₁ A F, ← IsScalarTower.algebraMap_apply R₁ A₁ A,
        ← IsScalarTower.algebraMap_apply R₁ A F]
  haveI tw19 : IsScalarTower A₁ B₁ F' :=
    IsScalarTower.of_algebraMap_eq (R := A₁) (S := B₁) (A := F') fun a => by
      rw [IsScalarTower.algebraMap_apply A₁ A F', IsScalarTower.algebraMap_apply B₁ B F',
        IsScalarTower.algebraMap_apply A B F', ← IsScalarTower.algebraMap_apply A₁ A B,
        ← IsScalarTower.algebraMap_apply A₁ B₁ B]
  haveI tw20 : IsScalarTower A₁ B F' :=
    IsScalarTower.of_algebraMap_eq (R := A₁) (S := B) (A := F') fun a => by
      rw [IsScalarTower.algebraMap_apply A₁ A F', IsScalarTower.algebraMap_apply A B F',
        ← IsScalarTower.algebraMap_apply A₁ A B]
  haveI tw21 : IsScalarTower A₁ F F' :=
    IsScalarTower.of_algebraMap_eq (R := A₁) (S := F) (A := F') fun a => by
      rw [IsScalarTower.algebraMap_apply A₁ A F', IsScalarTower.algebraMap_apply A₁ A F,
        ← IsScalarTower.algebraMap_apply A F F']
  haveI tw22 : IsScalarTower A₁ F₁' F' :=
    IsScalarTower.of_algebraMap_eq (R := A₁) (S := F₁') (A := F') fun a => by
      rw [IsScalarTower.algebraMap_apply A₁ B₁ F₁', ← IsScalarTower.algebraMap_apply B₁ F₁' F',
        ← IsScalarTower.algebraMap_apply A₁ B₁ F']

  have hcomp : g'.comp (f₁.restrictScalars R₁) = (f.restrictScalars R₁).comp g := by
    apply Algebra.TensorProduct.ext'
    intro x a
    simp only [AlgHom.coe_comp, Function.comp_apply, AlgHom.coe_restrictScalars']
    rw [show f₁ (x ⊗ₜ a) = x ⊗ₜ (algebraMap A₁ B₁ a) by simp [f₁], hg', hg, map_mul,
      show f (algebraMap κ F (ι x)) = algebraMap κ F' (ι x) from f.commutes _]
    congr 1
    change _ = algebraMap F F' (algebraMap A F (algebraMap A₁ A a))
    rw [← IsScalarTower.algebraMap_apply A₁ B₁ B, ← IsScalarTower.algebraMap_apply A₁ B F',
      ← IsScalarTower.algebraMap_apply A F F',
      ← IsScalarTower.algebraMap_apply A₁ A F']
  haveI tw23 : IsScalarTower F₁ F₁' F' :=
    IsScalarTower.of_algebraMap_eq' (R := F₁) (S := F₁') (A := F')
      (congrArg (fun h : F₁ →ₐ[R₁] F' => (h : F₁ →+* F')) hcomp).symm

  have hA : Algebra.IsPushout κ₁ F₁ κ F := by
    have h1 : Algebra.IsPushout R₁ κ A₁ F := by
      rw [Algebra.IsPushout.comp_iff R₁ R A₁ A]
      infer_instance
    rw [Algebra.IsPushout.comp_iff R₁ κ₁ A₁ F₁] at h1
    exact h1.symm

  have hB0 : Algebra.IsPushout A₁ B₁ A B := by
    haveI : Algebra.IsPushout R₁ A₁ R A := Algebra.IsPushout.symm inferInstance
    rw [← Algebra.IsPushout.comp_iff R₁ A₁ R A]
    exact Algebra.IsPushout.symm inferInstance
  have hB1 : Algebra.IsPushout A B F F' := by
    rw [← Algebra.IsPushout.comp_iff R A κ F]
    infer_instance
  have hB1' : Algebra.IsPushout A₁ B₁ F₁ F₁' := by
    rw [← Algebra.IsPushout.comp_iff R₁ A₁ κ₁ F₁]
    infer_instance
  have hB2 : Algebra.IsPushout A₁ F B₁ F' := by
    haveI := hB0.symm
    rw [Algebra.IsPushout.comp_iff A₁ A B₁ B]
    exact hB1.symm
  have hB : Algebra.IsPushout F₁ F F₁' F' := by
    haveI := hB1'.symm
    rwa [Algebra.IsPushout.comp_iff A₁ F₁ B₁ F₁'] at hB2

  haveI : Module.FaithfullyFlat κ₁ κ := inferInstance
  haveI : Module.FaithfullyFlat F₁ F :=
    Module.FaithfullyFlat.of_linearEquiv F₁ (F₁ ⊗[κ₁] κ)
      (Algebra.IsPushout.equiv κ₁ F₁ κ F).toLinearEquiv.symm
  haveI : Module.Flat F (F ⊗[F₁] F₁') :=
    Module.Flat.of_linearEquiv (Algebra.IsPushout.equiv F₁ F F₁' F').toLinearEquiv
  exact Module.Flat.of_flat_tensorProduct F₁ F₁' F

end Descent

theorem flat_localization_ascent {R₁ R A₁ A B₁ B : Type*} [CommRing R₁] [CommRing R]
    [CommRing A₁] [CommRing A] [CommRing B₁] [CommRing B] [Algebra R₁ R]
    [Algebra R₁ A₁] [Algebra R₁ B₁] [Algebra A₁ B₁] [IsScalarTower R₁ A₁ B₁]
    [Algebra R A] [Algebra R B] [Algebra A B] [IsScalarTower R A B]
    [Algebra R₁ A] [Algebra R₁ B] [IsScalarTower R₁ R A] [IsScalarTower R₁ R B]
    [Algebra A₁ A] [Algebra B₁ B] [IsScalarTower R₁ A₁ A] [IsScalarTower R₁ B₁ B]
    [Algebra A₁ B] [IsScalarTower A₁ A B] [IsScalarTower A₁ B₁ B]
    [Algebra.IsPushout R₁ R A₁ A] [Algebra.IsPushout R₁ R B₁ B]
    (Q : Ideal B) [Q.IsPrime] (Q₁ : Ideal B₁) [Q₁.IsPrime] (hQ₁ : Q₁ = Q.under B₁)
    [Module.Flat A₁ (Localization.AtPrime Q₁)] :
    Module.Flat A (Localization.AtPrime Q) := by
  haveI : IsScalarTower R₁ A B :=
    IsScalarTower.of_algebraMap_eq (R := R₁) (S := A) (A := B) fun r => by
      rw [IsScalarTower.algebraMap_apply R₁ R A, IsScalarTower.algebraMap_apply R₁ R B,
        ← IsScalarTower.algebraMap_apply R A B]
  have hB0 : Algebra.IsPushout A₁ B₁ A B := by
    haveI : Algebra.IsPushout R₁ A₁ R A := Algebra.IsPushout.symm inferInstance
    rw [← Algebra.IsPushout.comp_iff R₁ A₁ R A]
    exact Algebra.IsPushout.symm inferInstance

  let M : Submonoid B := Algebra.algebraMapSubmonoid B Q₁.primeCompl
  haveI hBT : Algebra.IsPushout B₁ B (Localization.AtPrime Q₁) (Localization M) :=
    Algebra.isPushout_of_isLocalization Q₁.primeCompl (Localization.AtPrime Q₁) B (Localization M)
  haveI : IsScalarTower A₁ (Localization.AtPrime Q₁) (Localization M) :=
    IsScalarTower.of_algebraMap_eq (R := A₁) (S := Localization.AtPrime Q₁) (A := Localization M)
      fun a => by
        rw [IsScalarTower.algebraMap_apply A₁ B₁ (Localization.AtPrime Q₁),
          ← IsScalarTower.algebraMap_apply B₁ (Localization.AtPrime Q₁) (Localization M),
          IsScalarTower.algebraMap_apply A₁ B₁ (Localization M)]
  have hAT : Algebra.IsPushout A₁ A (Localization.AtPrime Q₁) (Localization M) := by
    have : Algebra.IsPushout B₁ (Localization.AtPrime Q₁) B (Localization M) := hBT.symm
    rw [← Algebra.IsPushout.comp_iff A₁ B₁ A B] at this
    exact this.symm
  haveI : Module.Flat A (Localization M) :=
    Module.Flat.isBaseChange A₁ A (Localization.AtPrime Q₁) (Localization M) hAT.out

  have hle : M ≤ Q.primeCompl := by
    rintro _ ⟨b, hb, rfl⟩
    intro h
    apply hb
    rw [hQ₁]
    exact h
  letI : Algebra (Localization M) (Localization.AtPrime Q) :=
    IsLocalization.localizationAlgebraOfSubmonoidLe (Localization M) (Localization.AtPrime Q) M
      Q.primeCompl hle
  haveI : IsScalarTower B (Localization M) (Localization.AtPrime Q) :=
    IsLocalization.localization_isScalarTower_of_submonoid_le (Localization M)
      (Localization.AtPrime Q) M Q.primeCompl hle
  haveI : IsLocalization (Q.primeCompl.map (algebraMap B (Localization M)))
      (Localization.AtPrime Q) :=
    IsLocalization.isLocalization_of_submonoid_le (Localization M) (Localization.AtPrime Q) M
      Q.primeCompl hle
  haveI : Module.Flat (Localization M) (Localization.AtPrime Q) :=
    IsLocalization.flat (Localization.AtPrime Q) (Q.primeCompl.map (algebraMap B (Localization M)))
  haveI : IsScalarTower A (Localization M) (Localization.AtPrime Q) :=
    IsScalarTower.of_algebraMap_eq (R := A) (S := Localization M) (A := Localization.AtPrime Q)
      fun a => by
        rw [IsScalarTower.algebraMap_apply A B (Localization.AtPrime Q),
          IsScalarTower.algebraMap_apply B (Localization M) (Localization.AtPrime Q),
          ← IsScalarTower.algebraMap_apply A B (Localization M)]
  exact Module.Flat.trans A (Localization M) (Localization.AtPrime Q)

theorem flat_localization_of_model {R₁ A₁ B₁ : Type} {R A B : Type*} [CommRing R₁]
    [CommRing R] [CommRing A₁] [CommRing A] [CommRing B₁] [CommRing B] [Algebra R₁ R]
    [Algebra R₁ A₁] [Algebra R₁ B₁] [Algebra A₁ B₁] [IsScalarTower R₁ A₁ B₁]
    [Algebra R A] [Algebra R B] [Algebra A B] [IsScalarTower R A B]
    [Algebra R₁ A] [Algebra R₁ B] [IsScalarTower R₁ R A] [IsScalarTower R₁ R B]
    [Algebra A₁ A] [Algebra B₁ B] [IsScalarTower R₁ A₁ A] [IsScalarTower R₁ B₁ B]
    [Algebra A₁ B] [IsScalarTower A₁ A B] [IsScalarTower A₁ B₁ B]
    [Algebra.IsPushout R₁ R A₁ A] [Algebra.IsPushout R₁ R B₁ B]
    [IsNoetherianRing R₁] [Algebra.FiniteType R₁ A₁] [Algebra.FiniteType R₁ B₁]
    (Q : Ideal B) [Q.IsPrime] (Q₁ : Ideal B₁) [Q₁.IsPrime] (hQ₁ : Q₁ = Q.under B₁)
    [Module.Flat R₁ (Localization.AtPrime Q₁)]
    (hfib : (Algebra.TensorProduct.map
      (AlgHom.id (Q.under R).ResidueField (Q.under R).ResidueField)
        (IsScalarTower.toAlgHom R A B)).toRingHom.Flat) :
    Module.Flat A (Localization.AtPrime Q) := by
  have h1 := flat_fibre_descent (R₁ := R₁) (Q.under R) (A₁ := A₁) (A := A) (B₁ := B₁) (B := B) hfib
  haveI : IsScalarTower R₁ B₁ B := inferInstance
  have hp : (Q.under R).under R₁ = Q₁.under R₁ := by
    rw [Ideal.under_under, hQ₁, Ideal.under_under]
  haveI : Module.Flat A₁ (Localization.AtPrime Q₁) :=
    @flat_localization_of_flat_fibre_of_isNoetherianRing R₁ A₁ B₁ _ _ _ _ _ _ _ _ _ _ Q₁ _ _
      ((Q.under R).under R₁) _ hp h1
  exact flat_localization_ascent (R₁ := R₁) (R := R) (A₁ := A₁) (B₁ := B₁) Q Q₁ hQ₁

set_option maxHeartbeats 8000000 in

theorem flat_localization_of_model₀ {R₀ A₀ B₀ : Type} {R A B : Type*} [CommRing R₀]
    [CommRing R] [CommRing A₀] [CommRing A] [CommRing B₀] [CommRing B] [Algebra R₀ R]
    [Algebra R₀ A₀] [Algebra R₀ B₀] [Algebra A₀ B₀] [IsScalarTower R₀ A₀ B₀]
    [Algebra R A] [Algebra R B] [Algebra A B] [IsScalarTower R A B]
    [Algebra R₀ A] [Algebra R₀ B] [IsScalarTower R₀ R A] [IsScalarTower R₀ R B]
    [Algebra A₀ A] [Algebra B₀ B] [IsScalarTower R₀ A₀ A] [IsScalarTower R₀ B₀ B]
    [Algebra A₀ B] [IsScalarTower A₀ A B] [IsScalarTower A₀ B₀ B]
    [Algebra.IsPushout R₀ R A₀ A] [Algebra.IsPushout R₀ R B₀ B]
    [IsNoetherianRing R₀] [Algebra.FiniteType R₀ A₀] [Algebra.FiniteType R₀ B₀]
    [Module.Flat R B] (Q : Ideal B) [Q.IsPrime]
    (hfib : (Algebra.TensorProduct.map
      (AlgHom.id (Q.under R).ResidueField (Q.under R).ResidueField)
        (IsScalarTower.toAlgHom R A B)).toRingHom.Flat) :
    Module.Flat A (Localization.AtPrime Q) := by

  let eB' : R ⊗[R₀] B₀ ≃ₐ[R] B := Algebra.IsPushout.equiv R₀ R B₀ B
  let P : Ideal (R ⊗[R₀] B₀) := Q.comap (eB' : R ⊗[R₀] B₀ →+* B)
  haveI : Module.Flat R (Localization.AtPrime P) := by
    refine flat_localization_of_ringEquiv (RingEquiv.refl R) eB'.symm.toRingEquiv
      (fun r => eB'.symm.commutes r) Q P ?_
    rw [Ideal.comap_comap]
    ext x
    simp
  obtain ⟨R₁s, hfg, hflat₁⟩ :=
    Module.Flat.exists_fg_subalgebra_flat_localization_tensorProduct (R₀ := R₀) (R := R) P

  haveI : Algebra.FiniteType R₀ R₁s := (Subalgebra.fg_iff_finiteType _).mp hfg
  obtain ⟨n, g, hg⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp ‹Algebra.FiniteType R₀ R₁s›
  obtain ⟨R₁, _, _, _, ⟨e₁⟩⟩ : ∃ (R₁ : Type) (_ : CommRing R₁) (_ : Algebra R₀ R₁)
      (_ : IsNoetherianRing R₁), Nonempty (R₁ ≃ₐ[R₀] R₁s) :=
    ⟨_, inferInstance, inferInstance, inferInstance, ⟨Ideal.quotientKerAlgEquivOfSurjective hg⟩⟩

  let v : R₁ →ₐ[R₀] R := R₁s.val.comp (e₁ : R₁ →ₐ[R₀] R₁s)
  letI iR₁R : Algebra R₁ R := RingHom.toAlgebra (R := R₁) (S := R) v.toRingHom
  haveI : IsScalarTower R₀ R₁ R :=
    IsScalarTower.of_algebraMap_eq (R := R₀) (S := R₁) (A := R) fun r => (v.commutes r).symm
  letI iR₁A : Algebra R₁ A := RingHom.toAlgebra (R := R₁) (S := A)
    ((algebraMap R A).comp (algebraMap R₁ R))
  letI iR₁B : Algebra R₁ B := RingHom.toAlgebra (R := R₁) (S := B)
    ((algebraMap R B).comp (algebraMap R₁ R))
  haveI : IsScalarTower R₁ R A := IsScalarTower.of_algebraMap_eq' rfl
  haveI : IsScalarTower R₁ R B := IsScalarTower.of_algebraMap_eq' rfl
  haveI : IsScalarTower R₀ R₁ A :=
    IsScalarTower.of_algebraMap_eq (R := R₀) (S := R₁) (A := A) fun r => by
      rw [IsScalarTower.algebraMap_apply R₁ R A, ← IsScalarTower.algebraMap_apply R₀ R₁ R,
        ← IsScalarTower.algebraMap_apply R₀ R A]
  haveI : IsScalarTower R₀ R₁ B :=
    IsScalarTower.of_algebraMap_eq (R := R₀) (S := R₁) (A := B) fun r => by
      rw [IsScalarTower.algebraMap_apply R₁ R B, ← IsScalarTower.algebraMap_apply R₀ R₁ R,
        ← IsScalarTower.algebraMap_apply R₀ R B]
  haveI : IsScalarTower R₁ A B :=
    IsScalarTower.of_algebraMap_eq (R := R₁) (S := A) (A := B) fun r => by
      rw [IsScalarTower.algebraMap_apply R₁ R A, IsScalarTower.algebraMap_apply R₁ R B,
        ← IsScalarTower.algebraMap_apply R A B]
  let φ₁ : R₁ ⊗[R₀] A₀ →ₐ[R₁] R₁ ⊗[R₀] B₀ :=
    Algebra.TensorProduct.map (AlgHom.id R₁ R₁) (IsScalarTower.toAlgHom R₀ A₀ B₀)
  letI iA₁B₁ : Algebra (R₁ ⊗[R₀] A₀) (R₁ ⊗[R₀] B₀) :=
    RingHom.toAlgebra (R := R₁ ⊗[R₀] A₀) (S := R₁ ⊗[R₀] B₀) φ₁.toRingHom
  haveI : IsScalarTower R₁ (R₁ ⊗[R₀] A₀) (R₁ ⊗[R₀] B₀) :=
    IsScalarTower.of_algebraMap_eq (R := R₁) (S := R₁ ⊗[R₀] A₀) (A := R₁ ⊗[R₀] B₀)
      fun r => (φ₁.commutes r).symm
  let χA : R₁ ⊗[R₀] A₀ →ₐ[R₁] A :=
    Algebra.TensorProduct.lift (Algebra.ofId R₁ A) (IsScalarTower.toAlgHom R₀ A₀ A)
      fun _ _ => .all _ _
  let χB : R₁ ⊗[R₀] B₀ →ₐ[R₁] B :=
    Algebra.TensorProduct.lift (Algebra.ofId R₁ B) (IsScalarTower.toAlgHom R₀ B₀ B)
      fun _ _ => .all _ _
  have hχA : ∀ (x : R₁) (a : A₀), χA (x ⊗ₜ a) = algebraMap R₁ A x * algebraMap A₀ A a :=
    fun x a => Algebra.TensorProduct.lift_tmul ..
  have hχB : ∀ (x : R₁) (b : B₀), χB (x ⊗ₜ b) = algebraMap R₁ B x * algebraMap B₀ B b :=
    fun x b => Algebra.TensorProduct.lift_tmul ..
  letI iA₁A : Algebra (R₁ ⊗[R₀] A₀) A := RingHom.toAlgebra (R := R₁ ⊗[R₀] A₀) (S := A) χA.toRingHom
  letI iB₁B : Algebra (R₁ ⊗[R₀] B₀) B := RingHom.toAlgebra (R := R₁ ⊗[R₀] B₀) (S := B) χB.toRingHom
  letI iA₁B : Algebra (R₁ ⊗[R₀] A₀) B := RingHom.toAlgebra (R := R₁ ⊗[R₀] A₀) (S := B)
    ((algebraMap A B).comp (algebraMap (R₁ ⊗[R₀] A₀) A))
  haveI : IsScalarTower (R₁ ⊗[R₀] A₀) A B := IsScalarTower.of_algebraMap_eq' rfl
  haveI : IsScalarTower R₁ (R₁ ⊗[R₀] A₀) A :=
    IsScalarTower.of_algebraMap_eq (R := R₁) (S := R₁ ⊗[R₀] A₀) (A := A)
      fun r => (χA.commutes r).symm
  haveI : IsScalarTower R₁ (R₁ ⊗[R₀] B₀) B :=
    IsScalarTower.of_algebraMap_eq (R := R₁) (S := R₁ ⊗[R₀] B₀) (A := B)
      fun r => (χB.commutes r).symm
  haveI : IsScalarTower A₀ (R₁ ⊗[R₀] A₀) A :=
    IsScalarTower.of_algebraMap_eq (R := A₀) (S := R₁ ⊗[R₀] A₀) (A := A) fun a => by
      change _ = χA ((1 : R₁) ⊗ₜ a)
      rw [hχA, map_one, one_mul]
  haveI : IsScalarTower B₀ (R₁ ⊗[R₀] B₀) B :=
    IsScalarTower.of_algebraMap_eq (R := B₀) (S := R₁ ⊗[R₀] B₀) (A := B) fun b => by
      change _ = χB ((1 : R₁) ⊗ₜ b)
      rw [hχB, map_one, one_mul]
  haveI : IsScalarTower (R₁ ⊗[R₀] A₀) (R₁ ⊗[R₀] B₀) B := by
    refine IsScalarTower.of_algebraMap_eq' (R := R₁ ⊗[R₀] A₀) (S := R₁ ⊗[R₀] B₀) (A := B) ?_
    change ((IsScalarTower.toAlgHom R₁ A B).comp χA).toRingHom = (χB.comp φ₁).toRingHom
    congr 1
    apply Algebra.TensorProduct.ext'
    intro x a
    simp only [AlgHom.coe_comp, Function.comp_apply, IsScalarTower.coe_toAlgHom']
    rw [hχA, show φ₁ (x ⊗ₜ a) = x ⊗ₜ (algebraMap A₀ B₀ a) by simp [φ₁], hχB, map_mul,
      ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply,
      ← IsScalarTower.algebraMap_apply]
  haveI : IsScalarTower R₀ (R₁ ⊗[R₀] A₀) A :=
    IsScalarTower.of_algebraMap_eq (R := R₀) (S := R₁ ⊗[R₀] A₀) (A := A) fun r => by
      rw [IsScalarTower.algebraMap_apply R₀ R₁ (R₁ ⊗[R₀] A₀),
        ← IsScalarTower.algebraMap_apply R₁ (R₁ ⊗[R₀] A₀) A,
        ← IsScalarTower.algebraMap_apply R₀ R₁ A]
  haveI : IsScalarTower R₀ (R₁ ⊗[R₀] B₀) B :=
    IsScalarTower.of_algebraMap_eq (R := R₀) (S := R₁ ⊗[R₀] B₀) (A := B) fun r => by
      rw [IsScalarTower.algebraMap_apply R₀ R₁ (R₁ ⊗[R₀] B₀),
        ← IsScalarTower.algebraMap_apply R₁ (R₁ ⊗[R₀] B₀) B,
        ← IsScalarTower.algebraMap_apply R₀ R₁ B]
  haveI : Algebra.IsPushout R₁ R (R₁ ⊗[R₀] A₀) A :=
    (Algebra.IsPushout.comp_iff R₀ R₁ A₀ (R₁ ⊗[R₀] A₀)).mp inferInstance
  haveI : Algebra.IsPushout R₁ R (R₁ ⊗[R₀] B₀) B :=
    (Algebra.IsPushout.comp_iff R₀ R₁ B₀ (R₁ ⊗[R₀] B₀)).mp inferInstance
  haveI : Algebra.FiniteType R₁ (R₁ ⊗[R₀] A₀) := inferInstance
  haveI : Algebra.FiniteType R₁ (R₁ ⊗[R₀] B₀) := inferInstance

  haveI : Module.Flat R₁ (Localization.AtPrime (Q.under (R₁ ⊗[R₀] B₀))) := by
    refine flat_localization_of_ringEquiv (R := R₁s) (B := R₁s ⊗[R₀] B₀) e₁.symm.toRingEquiv
      (Algebra.TensorProduct.congr (e₁.symm : R₁s ≃ₐ[R₀] R₁)
        (AlgEquiv.refl : B₀ ≃ₐ[R₀] B₀)).toRingEquiv
      (fun r => ?_) (P.comap (Algebra.TensorProduct.map R₁s.val (AlgHom.id R₀ B₀)).toRingHom)
      (Q.under (R₁ ⊗[R₀] B₀)) ?_
    · change Algebra.TensorProduct.congr (e₁.symm : R₁s ≃ₐ[R₀] R₁) (AlgEquiv.refl : B₀ ≃ₐ[R₀] B₀)
        (r ⊗ₜ (1 : B₀)) = (e₁.symm r) ⊗ₜ (1 : B₀)
      simp [Algebra.TensorProduct.congr_apply]
    · change Ideal.comap _ (Ideal.comap _ Q) = Ideal.comap _ (Ideal.comap _ Q)
      rw [Ideal.comap_comap, Ideal.comap_comap]
      congr 1
      change (eB'.toAlgHom.restrictScalars R₀ |>.comp
          (Algebra.TensorProduct.map R₁s.val (AlgHom.id R₀ B₀))).toRingHom =
        ((χB.restrictScalars R₀).comp (Algebra.TensorProduct.congr (e₁.symm : R₁s ≃ₐ[R₀] R₁)
          (AlgEquiv.refl : B₀ ≃ₐ[R₀] B₀)).toAlgHom).toRingHom
      congr 1
      apply Algebra.TensorProduct.ext'
      intro r b
      simp only [AlgHom.coe_comp, Function.comp_apply, AlgHom.coe_restrictScalars',
        Algebra.TensorProduct.map_tmul, AlgHom.coe_id, id_eq,
        AlgEquiv.coe_algHom, Algebra.TensorProduct.congr_apply, AlgEquiv.coe_refl]
      rw [hχB, show eB' (R₁s.val r ⊗ₜ[R₀] b) = algebraMap R B (R₁s.val r) * algebraMap B₀ B b from
        Algebra.IsPushout.equiv_tmul .., IsScalarTower.algebraMap_apply R₁ R B]
      congr 2
      change (r : R) = R₁s.val (e₁ (e₁.symm r))
      simp
  exact flat_localization_of_model (R₁ := R₁) (A₁ := R₁ ⊗[R₀] A₀) (B₁ := R₁ ⊗[R₀] B₀) Q
    (Q.under (R₁ ⊗[R₀] B₀)) rfl hfib

end FibreFlatSol
p2m_reactivate "P2MW.S_Module_Flat_of_finitePresentation_of_forall_flat_residueField_tensorProduct.FibreFlatSol"

attribute [local instance] Algebra.TensorProduct.rightAlgebra in
open FibreFlatSol in
set_option maxHeartbeats 8000000 in

theorem solution
    {R A B : Type*} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] [Algebra A B] [IsScalarTower R A B]
    [Algebra.FinitePresentation R A] [Algebra.FinitePresentation R B] [Module.Flat R B]
    (hfib : ∀ (p : Ideal R) [p.IsPrime],
      (Algebra.TensorProduct.map (AlgHom.id p.ResidueField p.ResidueField)
        (IsScalarTower.toAlgHom R A B)).toRingHom.Flat) :
    Module.Flat A B := by
  classical

  refine Module.flat_of_isLocalized_maximal B B (fun Q _ => Localization.AtPrime Q)
    (fun Q _ => Algebra.linearMap B _) fun Q _ => ?_

  haveI : Algebra.FinitePresentation A B :=
    Algebra.FinitePresentation.of_restrict_scalars_finitePresentation R A B
  let PA := Algebra.Presentation.ofFinitePresentation R A
  let PB := Algebra.Presentation.ofFinitePresentation A B
  have hσ : ∀ a : A, ∃ q : PA.Ring, MvPolynomial.aeval PA.val q = a := fun a => by
    obtain ⟨q, hq⟩ := PA.algebraMap_surjective a
    exact ⟨q, by rwa [← Algebra.Generators.algebraMap_apply]⟩
  choose σ hσ using hσ

  let C : Set R := PA.coeffs ∪ ⋃ b ∈ PB.coeffs, ((σ b).coeffs : Set R)
  have hC : C.Finite :=
    PA.finite_coeffs.union (PB.finite_coeffs.biUnion fun b _ => Finset.finite_toSet _)

  obtain ⟨R₀, _, _, θ, hθ⟩ : ∃ (R₀ : Type) (_ : CommRing R₀) (_ : IsNoetherianRing R₀)
      (θ : R₀ →+* R), C ⊆ Set.range θ := by
    obtain ⟨k, c, hc⟩ := hC.fin_embedding
    refine ⟨MvPolynomial (Fin k) ℤ, inferInstance, inferInstance,
      (MvPolynomial.aeval fun i => (c i : R)).toRingHom, fun x hx => ?_⟩
    rw [← hc] at hx
    obtain ⟨i, rfl⟩ := hx
    exact ⟨MvPolynomial.X i, by simp⟩
  letI iR₀R : Algebra R₀ R := RingHom.toAlgebra θ
  letI iR₀A : Algebra R₀ A := RingHom.toAlgebra ((algebraMap R A).comp θ)
  letI iR₀B : Algebra R₀ B := RingHom.toAlgebra ((algebraMap R B).comp θ)
  haveI : IsScalarTower R₀ R A := IsScalarTower.of_algebraMap_eq' rfl
  haveI : IsScalarTower R₀ R B := IsScalarTower.of_algebraMap_eq' rfl
  haveI : IsScalarTower R₀ A B :=
    IsScalarTower.of_algebraMap_eq (R := R₀) (S := A) (A := B) fun r => by
      rw [IsScalarTower.algebraMap_apply R₀ R A, IsScalarTower.algebraMap_apply R₀ R B,
        ← IsScalarTower.algebraMap_apply R A B]
  replace hθ : C ⊆ Set.range (algebraMap R₀ R) := hθ

  obtain ⟨A₀, _, _, _, _, _, _, hcoeffB⟩ : ∃ (A₀ : Type) (_ : CommRing A₀) (_ : Algebra R₀ A₀)
      (_ : Algebra A₀ A) (_ : IsScalarTower R₀ A₀ A) (_ : Algebra.FiniteType R₀ A₀),
      Algebra.IsPushout R₀ R A₀ A ∧ (PB.coeffs : Set A) ⊆ Set.range (algebraMap A₀ A) := by
    haveI : PA.HasCoeffs R₀ := ⟨Set.subset_union_left.trans hθ⟩
    let ψ : PA.ModelOfHasCoeffs R₀ →ₐ[R₀] A :=
      Ideal.Quotient.liftₐ _ (MvPolynomial.aeval PA.val) (by
        simp_rw [← RingHom.mem_ker, ← SetLike.le_def, Ideal.span_le]
        rintro a ⟨i, rfl⟩
        simp)
    have hψ : ∀ y, ψ (Ideal.Quotient.mk _ y) = MvPolynomial.aeval PA.val y := fun y => rfl
    letI : Algebra (PA.ModelOfHasCoeffs R₀) A := RingHom.toAlgebra ψ.toRingHom
    haveI : IsScalarTower R₀ (PA.ModelOfHasCoeffs R₀) A :=
      IsScalarTower.of_algebraMap_eq fun r => (ψ.commutes r).symm
    refine ⟨PA.ModelOfHasCoeffs R₀, inferInstance, inferInstance, inferInstance, inferInstance,
      inferInstance, ?_, ?_⟩
    · refine Algebra.IsPushout.of_equiv (S' := R ⊗[R₀] PA.ModelOfHasCoeffs R₀)
        (PA.tensorModelOfHasCoeffsEquiv R₀) ?_
      refine RingHom.ext fun z => ?_
      obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective z
      change PA.tensorModelOfHasCoeffsEquiv R₀ ((1 : R) ⊗ₜ Ideal.Quotient.mk _ y) =
        ψ (Ideal.Quotient.mk _ y)
      rw [Algebra.Presentation.tensorModelOfHasCoeffsEquiv_tmul, hψ, map_one, one_mul]
    · intro b hb
      have hsub : ((σ b).coeffs : Set R) ⊆ Set.range (algebraMap R₀ R) :=
        subset_trans (fun r hr => Set.mem_union_right _ (Set.mem_biUnion hb hr)) hθ
      obtain ⟨q, hq⟩ := MvPolynomial.mem_range_map_iff_coeffs_subset.mpr hsub
      refine ⟨Ideal.Quotient.mk _ q, ?_⟩
      change ψ (Ideal.Quotient.mk _ q) = b
      rw [hψ, ← MvPolynomial.aeval_map_algebraMap R, hq, hσ]

  letI iA₀B : Algebra A₀ B := RingHom.toAlgebra ((algebraMap A B).comp (algebraMap A₀ A))
  haveI : IsScalarTower A₀ A B := IsScalarTower.of_algebraMap_eq' rfl
  obtain ⟨B₀, _, _, _, _, _, _⟩ : ∃ (B₀ : Type) (_ : CommRing B₀) (_ : Algebra A₀ B₀)
      (_ : Algebra B₀ B) (_ : IsScalarTower A₀ B₀ B) (_ : Algebra.FiniteType A₀ B₀),
      Algebra.IsPushout A₀ A B₀ B := by
    haveI : PB.HasCoeffs A₀ := ⟨hcoeffB⟩
    let ψ : PB.ModelOfHasCoeffs A₀ →ₐ[A₀] B :=
      Ideal.Quotient.liftₐ _ (MvPolynomial.aeval PB.val) (by
        simp_rw [← RingHom.mem_ker, ← SetLike.le_def, Ideal.span_le]
        rintro a ⟨i, rfl⟩
        simp)
    have hψ : ∀ y, ψ (Ideal.Quotient.mk _ y) = MvPolynomial.aeval PB.val y := fun y => rfl
    letI : Algebra (PB.ModelOfHasCoeffs A₀) B := RingHom.toAlgebra ψ.toRingHom
    haveI : IsScalarTower A₀ (PB.ModelOfHasCoeffs A₀) B :=
      IsScalarTower.of_algebraMap_eq fun r => (ψ.commutes r).symm
    refine ⟨PB.ModelOfHasCoeffs A₀, inferInstance, inferInstance, inferInstance, inferInstance,
      inferInstance, ?_⟩
    refine Algebra.IsPushout.of_equiv (S' := A ⊗[A₀] PB.ModelOfHasCoeffs A₀)
      (PB.tensorModelOfHasCoeffsEquiv A₀) ?_
    refine RingHom.ext fun z => ?_
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective z
    change PB.tensorModelOfHasCoeffsEquiv A₀ ((1 : A) ⊗ₜ Ideal.Quotient.mk _ y) =
      ψ (Ideal.Quotient.mk _ y)
    rw [Algebra.Presentation.tensorModelOfHasCoeffsEquiv_tmul, hψ, map_one, one_mul]

  letI iR₀B₀ : Algebra R₀ B₀ := RingHom.toAlgebra ((algebraMap A₀ B₀).comp (algebraMap R₀ A₀))
  haveI : IsScalarTower R₀ A₀ B₀ := IsScalarTower.of_algebraMap_eq' rfl
  haveI : Algebra.FiniteType R₀ B₀ := Algebra.FiniteType.trans (S := A₀) inferInstance inferInstance
  haveI : IsScalarTower R₀ B₀ B :=
    IsScalarTower.of_algebraMap_eq (R := R₀) (S := B₀) (A := B) fun r => by
      rw [IsScalarTower.algebraMap_apply R₀ A₀ B₀, ← IsScalarTower.algebraMap_apply A₀ B₀ B,
        IsScalarTower.algebraMap_apply A₀ A B, ← IsScalarTower.algebraMap_apply R₀ A₀ A,
        ← IsScalarTower.algebraMap_apply R₀ A B]
  haveI : Algebra.IsPushout R₀ R B₀ B := by
    haveI : Algebra.IsPushout R₀ A₀ R A := Algebra.IsPushout.symm inferInstance
    have h : Algebra.IsPushout A₀ B₀ A B := Algebra.IsPushout.symm inferInstance
    rw [← Algebra.IsPushout.comp_iff R₀ A₀ R A] at h
    exact h.symm
  exact flat_localization_of_model₀ (R₀ := R₀) (A₀ := A₀) (B₀ := B₀) Q (hfib _)

end S_Module_Flat_of_finitePresentation_of_forall_flat_residueField_tensorProduct
end P2MW
export P2MW.S_Module_Flat_of_finitePresentation_of_forall_flat_residueField_tensorProduct (solution)
