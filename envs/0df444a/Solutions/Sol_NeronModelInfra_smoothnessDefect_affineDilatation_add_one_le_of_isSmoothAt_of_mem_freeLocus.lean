-- Prove2me | solution 1 for NeronModelInfra.smoothnessDefect_affineDilatation_add_one_le_of_isSmoothAt_of_mem_freeLocus
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/df1e2a59-6822-58eb-80cc-272a2ab94c42

import Mathlib
import Definitions.Def_NeronModelInfra_WeakNeronModel
import Definitions.Def_NeronModelInfra_SmoothnessDefect
import Definitions.Def_RingTheory_AffineDilatation
import Theorems.Thm_AffineDilatation_exists_algHom_isLocalization_map
import Theorems.Thm_AffineDilatation_isSMulRegular_and_map_eq_span_singleton
import Theorems.Thm_IsDiscreteValuationRing_length_torsion_quotient_add_finrank_le_of_sq_smul_le_prod
import Theorems.Thm_KaehlerDifferential_nonempty_baseChange_linearEquiv_quotient_span_tmul_D_of_surjective
import Theorems.Thm_Algebra_exists_smooth_surjective_localizationAway_basis_kaehlerDifferential_comap_eq_span
import Theorems.Thm_NeronModelInfra_le_sq_of_linearIndependent_tmul_D_of_forall_indexOne
import Theorems.Thm_AffineDilatation_exists_basis_kaehlerDifferential_of_smooth_of_basis
import Theorems.Thm_AffineDilatation_exists_algHom_surjective_ker_iff_of_surjective
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NeronModelInfra_smoothnessDefect_affineDilatation_add_one_le_of_isSmoothAt_of_mem_freeLocus

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra TensorProduct

universe u

open KaehlerDifferential IsLocalRing

noncomputable section

namespace NeronJacobiSkeleton

variable {R : Type u} [CommRing R] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
variable {R' : Type u} [CommRing R'] [IsLocalRing R'] (a : Spec (CommRingCat.of R') ⟶ X)

abbrev globalAlgebra : Algebra R Γ(X, ⊤) :=
  (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom).toAlgebra

abbrev globalPointAlgebra : Algebra Γ(X, ⊤) R' :=
  ((Scheme.stalkClosedPointTo a).hom.comp
    (X.presheaf.germ ⊤ (a (IsLocalRing.closedPoint R')) trivial).hom).toAlgebra

theorem smoothnessDefect_eq_length_torsion_global [IsAffine X] :
    smoothnessDefect f a =
      (letI : Algebra R Γ(X, ⊤) := globalAlgebra f
       letI : Algebra Γ(X, ⊤) R' := globalPointAlgebra a
       Module.length R' (Submodule.torsion R' (R' ⊗[Γ(X, ⊤)] Ω[Γ(X, ⊤)⁄R]))) := by
  rw [smoothnessDefect_def]

  set x : X := a (IsLocalRing.closedPoint R') with hx
  letI iRA : Algebra R Γ(X, ⊤) := globalAlgebra f
  letI iAR' : Algebra Γ(X, ⊤) R' := globalPointAlgebra a
  letI iRO : Algebra R (X.presheaf.stalk x) := stalkAlgebra f x
  letI iOR' : Algebra (X.presheaf.stalk x) R' := pointAlgebra a
  letI iAO : Algebra Γ(X, ⊤) (X.presheaf.stalk x) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨x, trivial⟩ : (⊤ : X.Opens))
  haveI : IsScalarTower R Γ(X, ⊤) (X.presheaf.stalk x) :=
    IsScalarTower.of_algebraMap_eq' rfl
  haveI : IsScalarTower Γ(X, ⊤) (X.presheaf.stalk x) R' :=
    IsScalarTower.of_algebraMap_eq' rfl

  haveI : IsLocalization.AtPrime (X.presheaf.stalk x)
      ((isAffineOpen_top X).primeIdealOf (⟨x, trivial⟩ : (⊤ : X.Opens))).asIdeal :=
    (isAffineOpen_top X).isLocalization_stalk ⟨x, trivial⟩
  haveI : Algebra.FormallyEtale Γ(X, ⊤) (X.presheaf.stalk x) :=
    Algebra.FormallyEtale.of_isLocalization
      (((isAffineOpen_top X).primeIdealOf (⟨x, trivial⟩ : (⊤ : X.Opens))).asIdeal.primeCompl)

  let e₁ : (X.presheaf.stalk x) ⊗[Γ(X, ⊤)] Ω[Γ(X, ⊤)⁄R] ≃ₗ[X.presheaf.stalk x] Ω[X.presheaf.stalk x⁄R] :=
    KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale R Γ(X, ⊤) (X.presheaf.stalk x)
  let e₂ : R' ⊗[X.presheaf.stalk x] Ω[X.presheaf.stalk x⁄R] ≃ₗ[R']
      R' ⊗[X.presheaf.stalk x] ((X.presheaf.stalk x) ⊗[Γ(X, ⊤)] Ω[Γ(X, ⊤)⁄R]) :=
    (e₁.symm.baseChange (X.presheaf.stalk x) R' _ _)
  let e₃ : R' ⊗[X.presheaf.stalk x] ((X.presheaf.stalk x) ⊗[Γ(X, ⊤)] Ω[Γ(X, ⊤)⁄R]) ≃ₗ[R']
      R' ⊗[Γ(X, ⊤)] Ω[Γ(X, ⊤)⁄R] :=
    TensorProduct.AlgebraTensorModule.cancelBaseChange Γ(X, ⊤) (X.presheaf.stalk x) R' R' Ω[Γ(X, ⊤)⁄R]
  exact length_torsion_eq_of_equiv' (e₂.trans e₃)
where

  length_torsion_eq_of_equiv' {S : Type u} [CommRing S] {M M' : Type u}
      [AddCommGroup M] [Module S M] [AddCommGroup M'] [Module S M'] (e : M ≃ₗ[S] M') :
      Module.length S (Submodule.torsion S M) = Module.length S (Submodule.torsion S M') := by
    have : (Submodule.torsion S M).map (e : M →ₗ[S] M') = Submodule.torsion S M' := by
      ext y
      simp only [Submodule.mem_map, Submodule.mem_torsion_iff]
      constructor
      · rintro ⟨x, ⟨a, ha⟩, rfl⟩
        refine ⟨a, ?_⟩
        change (a : S) • (e : M →ₗ[S] M') x = 0
        change (a : S) • x = 0 at ha
        rw [← map_smul, ha, map_zero]
      · rintro ⟨a, ha⟩
        refine ⟨e.symm y, ⟨a, ?_⟩, by simp⟩
        change (a : S) • e.symm y = 0
        change (a : S) • y = 0 at ha
        rw [← map_smul, ha, map_zero]
    rw [← this]
    exact (e.submoduleMap (Submodule.torsion S M)).length_eq

theorem algebraMap_globalPointAlgebra_globalAlgebra [Algebra R R']
    (ha : a ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R R'))) (r : R) :
    (letI : Algebra R Γ(X, ⊤) := globalAlgebra f
     letI : Algebra Γ(X, ⊤) R' := globalPointAlgebra a
     algebraMap Γ(X, ⊤) R' (algebraMap R Γ(X, ⊤) r)) = algebraMap R R' r := by
  letI iRA : Algebra R Γ(X, ⊤) := globalAlgebra f
  letI iAR' : Algebra Γ(X, ⊤) R' := globalPointAlgebra a
  change (Scheme.stalkClosedPointTo a).hom ((X.presheaf.germ ⊤ (a (IsLocalRing.closedPoint R')) trivial).hom
    (f.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r))) = algebraMap R R' r

  have h1 := Scheme.Hom.germ_stalkMap_apply f ⊤ (a (IsLocalRing.closedPoint R')) trivial
    ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r)

  change (Scheme.stalkClosedPointTo a).hom ((X.presheaf.germ (f ⁻¹ᵁ ⊤) (a (IsLocalRing.closedPoint R')) trivial).hom
    ((f.app ⊤).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r))) = algebraMap R R' r
  rw [← h1]

  rw [← CommRingCat.comp_apply, ← Scheme.stalkClosedPointTo_comp]
  have key : ∀ (g : Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of R)),
      g = Spec.map (CommRingCat.ofHom (algebraMap R R')) → ∀ s,
      (Scheme.stalkClosedPointTo g).hom
        (((Spec (CommRingCat.of R)).presheaf.germ ⊤ (g (IsLocalRing.closedPoint R')) trivial).hom s) =
        algebraMap R R' ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom s) := by
    rintro g rfl s
    have h3 := Scheme.germ_stalkClosedPointTo_Spec (CommRingCat.ofHom (algebraMap R R'))
    have := congrArg (fun φ : (Spec (CommRingCat.of R)).presheaf.obj (Opposite.op ⊤) ⟶ CommRingCat.of R' =>
      φ.hom s) h3
    simp only [CommRingCat.comp_apply, CommRingCat.hom_ofHom] at this
    exact this
  refine (key (a ≫ f) ha _).trans ?_
  rw [← CommRingCat.comp_apply, Iso.inv_hom_id, CommRingCat.id_apply]

theorem smoothnessDefect_Spec_eq {R : Type u} [CommRing R] {A : Type u} [CommRing A] [Algebra R A]
    {R' : Type u} [CommRing R'] [IsLocalRing R'] (φ : A →+* R') :
    smoothnessDefect (Spec.map (CommRingCat.ofHom (algebraMap R A))) (Spec.map (CommRingCat.ofHom φ)) =
      (letI : Algebra A R' := φ.toAlgebra
       Module.length R' (Submodule.torsion R' (R' ⊗[A] Ω[A⁄R]))) := by
  rw [smoothnessDefect_eq_length_torsion_global]
  set Γ' : Type u := Γ(Spec (CommRingCat.of A), ⊤) with hΓ
  letI iRΓ : Algebra R Γ(Spec (CommRingCat.of A), ⊤) :=
    globalAlgebra (Spec.map (CommRingCat.ofHom (algebraMap R A)))
  letI iΓR' : Algebra Γ(Spec (CommRingCat.of A), ⊤) R' := globalPointAlgebra (Spec.map (CommRingCat.ofHom φ))
  letI iAR' : Algebra A R' := φ.toAlgebra
  letI iΓA : Algebra Γ(Spec (CommRingCat.of A), ⊤) A := (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom.toAlgebra
  haveI : IsScalarTower R Γ(Spec (CommRingCat.of A), ⊤) A := IsScalarTower.of_algebraMap_eq' (by
    apply RingHom.ext; intro r
    change algebraMap R A r = (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom
      ((Spec.map (CommRingCat.ofHom (algebraMap R A))).appTop.hom
        ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r))
    rw [← CommRingCat.comp_apply, Scheme.ΓSpecIso_naturality, CommRingCat.comp_apply,
      ← CommRingCat.comp_apply (Scheme.ΓSpecIso (CommRingCat.of R)).inv, Iso.inv_hom_id]
    rfl)
  haveI : IsScalarTower Γ(Spec (CommRingCat.of A), ⊤) A R' := IsScalarTower.of_algebraMap_eq' (by
    change ((Scheme.stalkClosedPointTo (Spec.map (CommRingCat.ofHom φ))).hom.comp
      ((Spec (CommRingCat.of A)).presheaf.germ ⊤ _ trivial).hom) =
      φ.comp (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom
    rw [← CommRingCat.hom_comp, Scheme.germ_stalkClosedPointTo_Spec]
    rfl)
  haveI : IsLocalization.Away (1 : Γ(Spec (CommRingCat.of A), ⊤)) A :=
    IsLocalization.away_of_isUnit_of_bijective _ isUnit_one
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of A)).hom)
  haveI : Algebra.FormallyEtale Γ(Spec (CommRingCat.of A), ⊤) A :=
    Algebra.FormallyEtale.of_isLocalization (Submonoid.powers (1 : Γ(Spec (CommRingCat.of A), ⊤)))
  let e₁ : A ⊗[Γ(Spec (CommRingCat.of A), ⊤)] Ω[Γ(Spec (CommRingCat.of A), ⊤)⁄R] ≃ₗ[A] Ω[A⁄R] :=
    KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale R Γ(Spec (CommRingCat.of A), ⊤) A
  let e₂ := (e₁.symm.baseChange A R' _ _)
  let e₃ := TensorProduct.AlgebraTensorModule.cancelBaseChange Γ(Spec (CommRingCat.of A), ⊤) A R' R'
    Ω[Γ(Spec (CommRingCat.of A), ⊤)⁄R]
  exact (smoothnessDefect_eq_length_torsion_global.length_torsion_eq_of_equiv' (e₂.trans e₃)).symm

theorem length_torsion_baseChange_kaehler_eq_of_formallyEtale
    (R : Type u) [CommRing R] (A S R' : Type u) [CommRing A] [CommRing S] [CommRing R']
    [Algebra R A] [Algebra R S] [Algebra A S] [IsScalarTower R A S]
    [Algebra A R'] [Algebra S R'] [IsScalarTower A S R'] [Algebra.FormallyEtale A S] :
    Module.length R' (Submodule.torsion R' (R' ⊗[S] Ω[S⁄R])) =
      Module.length R' (Submodule.torsion R' (R' ⊗[A] Ω[A⁄R])) := by
  let e₁ : S ⊗[A] Ω[A⁄R] ≃ₗ[S] Ω[S⁄R] := KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale R A S
  let e₂ := (e₁.symm.baseChange S R' _ _)
  let e₃ := TensorProduct.AlgebraTensorModule.cancelBaseChange A S R' R' Ω[A⁄R]
  exact smoothnessDefect_eq_length_torsion_global.length_torsion_eq_of_equiv' (e₂.trans e₃)

theorem length_torsion_quotient_mono_of_forall_exists_smul_mem
    {S : Type u} [CommRing S] [IsDomain S] {M : Type u} [AddCommGroup M] [Module S M]
    (N₁ N₂ : Submodule S M) (hle : N₁ ≤ N₂) (htor : ∀ x ∈ N₂, ∃ s : S, s ≠ 0 ∧ s • x ∈ N₁) :
    Module.length S (Submodule.torsion S (M ⧸ N₂)) ≤ Module.length S (Submodule.torsion S (M ⧸ N₁)) := by

  let q : (M ⧸ N₁) →ₗ[S] (M ⧸ N₂) := Submodule.factor hle
  have hq : ∀ y : M ⧸ N₂, y ∈ Submodule.torsion S (M ⧸ N₂) →
      ∃ x ∈ Submodule.torsion S (M ⧸ N₁), q x = y := by
    intro y hy
    obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective N₂ y
    obtain ⟨⟨a, ha⟩, hay⟩ := (Submodule.mem_torsion_iff _).mp hy
    change (a : S) • (Submodule.Quotient.mk m : M ⧸ N₂) = 0 at hay
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at hay
    obtain ⟨s, hs, hsm⟩ := htor _ hay
    refine ⟨Submodule.Quotient.mk m, ?_, rfl⟩
    refine (Submodule.mem_torsion_iff _).mpr ⟨⟨s * a, mul_ne_zero hs (nonZeroDivisors.ne_zero ha) |>
      mem_nonZeroDivisors_of_ne_zero⟩, ?_⟩
    change (s * (a : S)) • (Submodule.Quotient.mk m : M ⧸ N₁) = 0
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, mul_smul]
    exact hsm
  let q' : Submodule.torsion S (M ⧸ N₁) →ₗ[S] Submodule.torsion S (M ⧸ N₂) :=
    (q.restrict fun x hx => by
      obtain ⟨a, ha⟩ := (Submodule.mem_torsion_iff _).mp hx
      exact (Submodule.mem_torsion_iff _).mpr ⟨a, by
        change (a : S) • q x = 0; rw [← map_smul]; change q ((a : S) • x) = 0
        rw [show (a : S) • (x : M ⧸ N₁) = 0 from ha, map_zero]⟩)
  have hq' : Function.Surjective q' := by
    rintro ⟨y, hy⟩
    obtain ⟨x, hx, hxy⟩ := hq y hy
    exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩
  exact Module.length_le_of_surjective q' hq'

theorem one_tmul_smul_eq {S T : Type u} [CommRing S] [CommRing T] [Algebra S T] {M : Type u} [AddCommGroup M]
    [Module S M] (c : S) (m : M) :
    ((1 : T) ⊗ₜ[S] (c • m) : T ⊗[S] M) = algebraMap S T c • ((1 : T) ⊗ₜ[S] m) := by
  rw [← TensorProduct.smul_tmul, TensorProduct.smul_tmul', Algebra.smul_def, mul_one, smul_eq_mul, mul_one]

end NeronJacobiSkeleton

end

set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 16000000 in
open NeronJacobiSkeleton in
theorem solution
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (π : R) (hπ : IsLocalRing.maximalIdeal R = Ideal.span {π})
    {A : Type u} [CommRing A] [Algebra R A] [Algebra.FiniteType R A]
    (J : Ideal A) (hπJ : algebraMap R A π ∈ J)
    [Algebra (IsLocalRing.ResidueField R) (A ⧸ J)] [IsScalarTower R (IsLocalRing.ResidueField R) (A ⧸ J)]
    (hN : ∀ g : A,
      (∀ (R'' : Type u) [CommRing R''] [IsDomain R''] [IsDiscreteValuationRing R''] [Algebra R R'']
        [IsLocalHom (algebraMap R R'')], IsIndexOneExtension R R'' →
        ∀ c : A →ₐ[R] R'', J ≤ (IsLocalRing.maximalIdeal R'').comap c →
          g ∈ (IsLocalRing.maximalIdeal R'').comap c) → g ∈ J)
    (R' : Type u) [CommRing R'] [IsDomain R'] [IsDiscreteValuationRing R'] [Algebra R R']
    [IsLocalHom (algebraMap R R')] (hR' : IsIndexOneExtension R R')
    (φ : A →ₐ[R] R') (hgen : PrimeSpectrum.comap φ.toRingHom (⊥ : PrimeSpectrum R') ∈ Algebra.smoothLocus R A)
    (𝔮 : Ideal (A ⧸ J)) [𝔮.IsPrime] (h𝔮 : 𝔮.comap (Ideal.Quotient.mk J) = (IsLocalRing.maximalIdeal R').comap φ)
    (hsmooth : Algebra.IsSmoothAt (IsLocalRing.ResidueField R) 𝔮)
    (hfree : (⟨𝔮, ‹_›⟩ : PrimeSpectrum (A ⧸ J)) ∈
      Module.freeLocus (A ⧸ J) ((A ⧸ J) ⊗[A] Ω[A⁄R]))
    (φ' : AffineDilatation.Ring J (algebraMap R A π) →ₐ[R] R')
    (hφ' : ∀ a : A, φ' (algebraMap A (AffineDilatation.Ring J (algebraMap R A π)) a) = φ a) :
    smoothnessDefect
        (Spec.map (CommRingCat.ofHom (algebraMap R (AffineDilatation.Ring J (algebraMap R A π)))))
        (Spec.map (CommRingCat.ofHom φ'.toRingHom)) + 1 ≤
      max 1 (smoothnessDefect (Spec.map (CommRingCat.ofHom (algebraMap R A)))
        (Spec.map (CommRingCat.ofHom φ.toRingHom)))  := by
  classical

  let 𝔭 : Ideal A := (IsLocalRing.maximalIdeal R').comap φ.toRingHom
  haveI : 𝔭.IsPrime := Ideal.comap_isPrime _ _
  have h𝔮' : 𝔮.comap (Ideal.Quotient.mk J) = 𝔭 := h𝔮

  obtain ⟨g, hg, r, n, C, iC, iRC, iCAg, iT, hCsm, hθ, y, z, b, hby, hbz, hJC, hlin⟩ :=
    Algebra.exists_smooth_surjective_localizationAway_basis_kaehlerDifferential_comap_eq_span
      π hπ J hπJ 𝔭 𝔮 h𝔮' hsmooth hfree
  letI := iC; letI := iRC; letI := iCAg; haveI := iT
  set Ag : Type u := Localization.Away g with hAg

  have hgunit : IsUnit (φ g) := IsLocalRing.notMem_maximalIdeal.mp hg
  let φg : Ag →+* R' := IsLocalization.Away.lift g (g := φ.toRingHom) hgunit
  have hφg : ∀ a : A, φg (algebraMap A Ag a) = φ a := fun a => IsLocalization.Away.lift_eq g hgunit a

  set JC : Ideal C := Ideal.span (insert (algebraMap R C π) (Set.range z)) with hJCdef
  have hπJC : algebraMap R C π ∈ JC := Ideal.subset_span (Set.mem_insert _ _)

  have hNC : ∀ g₀ : C,
      (∀ (R'' : Type u) [CommRing R''] [IsDomain R''] [IsDiscreteValuationRing R''] [Algebra R R'']
        [IsLocalHom (algebraMap R R'')], IsIndexOneExtension R R'' →
        ∀ c : C →ₐ[R] R'', RingHom.ker (algebraMap C Ag) ≤ RingHom.ker c.toRingHom →
          JC ≤ (IsLocalRing.maximalIdeal R'').comap c → g₀ ∈ (IsLocalRing.maximalIdeal R'').comap c) →
      g₀ ∈ JC := by
    intro g₀ hg₀
    rw [← hJC, Ideal.mem_comap]
    obtain ⟨⟨a₀, ⟨_, ⟨m, rfl⟩⟩⟩, ha₀⟩ := IsLocalization.mk'_surjective (Submonoid.powers g) (algebraMap C Ag g₀)
    have hclaim : a₀ * g ∈ J := by
      apply hN
      intro R'' _ _ _ _ _ hR'' c hJc
      by_cases hcg : c g ∈ IsLocalRing.maximalIdeal R''
      · exact Ideal.mem_comap.mpr (by rw [map_mul]; exact Ideal.mul_mem_left _ _ hcg)
      · have hu : IsUnit (c.toRingHom g) := IsLocalRing.notMem_maximalIdeal.mp hcg
        let cg : Ag →+* R'' := IsLocalization.Away.lift g (g := c.toRingHom) hu
        have hcg_eq : ∀ a, cg (algebraMap A Ag a) = c a := IsLocalization.Away.lift_eq g hu
        let ct : C →ₐ[R] R'' := AlgHom.mk (cg.comp (algebraMap C Ag)) (fun r' => by
          change cg (algebraMap C Ag (algebraMap R C r')) = algebraMap R R'' r'
          rw [← IsScalarTower.algebraMap_apply R C Ag, IsScalarTower.algebraMap_apply R A Ag, hcg_eq,
            AlgHom.commutes])
        have hker : RingHom.ker (algebraMap C Ag) ≤ RingHom.ker ct.toRingHom := by
          intro f hf
          simp only [RingHom.mem_ker] at hf ⊢
          change cg (algebraMap C Ag f) = 0
          rw [hf, map_zero]
        have hJle : JC ≤ (IsLocalRing.maximalIdeal R'').comap ct := by
          rw [← hJC]
          intro j hj
          rw [Ideal.mem_comap] at hj ⊢
          change cg (algebraMap C Ag j) ∈ IsLocalRing.maximalIdeal R''
          have : J.map (algebraMap A Ag) ≤ (IsLocalRing.maximalIdeal R'').comap cg := by
            rw [Ideal.map_le_iff_le_comap, Ideal.comap_comap]
            intro a ha
            rw [Ideal.mem_comap, RingHom.comp_apply, hcg_eq]
            exact hJc ha
          exact this hj
        have h1 := hg₀ R'' hR'' ct hker hJle
        rw [Ideal.mem_comap] at h1
        change cg (algebraMap C Ag g₀) ∈ IsLocalRing.maximalIdeal R'' at h1
        rw [← ha₀] at h1
        have h2 : cg (IsLocalization.mk' Ag a₀ (⟨g ^ m, m, rfl⟩ : Submonoid.powers g)) *
            cg (algebraMap A Ag (g ^ m)) = c a₀ := by
          rw [← map_mul, IsLocalization.mk'_spec, hcg_eq]
        rw [Ideal.mem_comap, map_mul, ← h2, mul_assoc]
        exact Ideal.mul_mem_right _ _ h1

    have h3 : algebraMap C Ag g₀ =
        algebraMap A Ag (a₀ * g) * IsLocalization.mk' Ag 1 (⟨g ^ (m + 1), m + 1, rfl⟩ : Submonoid.powers g) := by
      rw [← ha₀, ← IsLocalization.mk'_one (M := Submonoid.powers g) Ag, ← IsLocalization.mk'_mul]
      rw [IsLocalization.mk'_eq_iff_eq]
      simp only [one_mul, mul_one]
      congr 1
      ring
    rw [h3]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ hclaim)
  have hIJ : RingHom.ker (algebraMap C Ag) ≤ JC := by
    rw [← hJC]; exact fun f hf => by
      simp only [Ideal.mem_comap, RingHom.mem_ker] at hf ⊢; rw [hf]; exact Ideal.zero_mem _
  have hIJ2 : RingHom.ker (algebraMap C Ag) ≤ JC ^ 2 :=
    NeronModelInfra.le_sq_of_linearIndependent_tmul_D_of_forall_indexOne π hπ hθ z hIJ hlin hNC

  obtain ⟨b', hb'y, hb'z⟩ :=
    AffineDilatation.exists_basis_kaehlerDifferential_of_smooth_of_basis π hπ y z b hby hbz

  obtain ⟨θ', hθ's, hθ'k⟩ :=
    AffineDilatation.exists_algHom_surjective_ker_iff_of_surjective (R := R) π (C := C) (A := Ag) hθ JC

  have hImap : JC.map (algebraMap C Ag) = J.map (algebraMap A Ag) := by
    rw [← hJC, Ideal.map_comap_of_surjective _ hθ]
  have hπeq : algebraMap R Ag π = algebraMap A Ag (algebraMap R A π) := IsScalarTower.algebraMap_apply R A Ag π
  have h5 : ∃ θ' : AffineDilatation.Ring JC (algebraMap R C π) →ₐ[C]
      AffineDilatation.Ring (J.map (algebraMap A Ag)) (algebraMap A Ag (algebraMap R A π)),
      Function.Surjective θ' ∧ ∀ x, θ' x = 0 ↔ ∃ ν : ℕ, (algebraMap R _ π) ^ ν * x ∈
        (RingHom.ker (algebraMap C Ag)).map (algebraMap C (AffineDilatation.Ring JC (algebraMap R C π))) := by
    have h := AffineDilatation.exists_algHom_surjective_ker_iff_of_surjective (R := R) π (C := C) (A := Ag) hθ JC
    rw [hImap, hπeq] at h
    exact h
  clear θ' hθ's hθ'k
  obtain ⟨θ', hθ's, hθ'k⟩ := h5
  obtain ⟨lam, hlam⟩ := AffineDilatation.exists_algHom_isLocalization_map J (algebraMap R A π) hπJ
    (Submonoid.powers g) Ag

  let A' : Type u := AffineDilatation.Ring J (algebraMap R A π)
  let B : Type u := AffineDilatation.Ring (J.map (algebraMap A Ag)) (algebraMap A Ag (algebraMap R A π))
  let C' : Type u := AffineDilatation.Ring JC (algebraMap R C π)

  letI iA'B : Algebra A' B := lam.toRingHom.toAlgebra
  haveI hlam' : IsLocalization (Algebra.algebraMapSubmonoid A' (Submonoid.powers g)) B := hlam
  haveI : Algebra.FormallyEtale A' B := Algebra.FormallyEtale.of_isLocalization
    (Algebra.algebraMapSubmonoid A' (Submonoid.powers g))
  have hunits : ∀ s : Algebra.algebraMapSubmonoid A' (Submonoid.powers g), IsUnit (φ'.toRingHom s) := by
    rintro ⟨_, ⟨s, ⟨k, rfl⟩, rfl⟩⟩
    change IsUnit (φ' (algebraMap A A' (g ^ k)))
    rw [hφ', map_pow]; exact hgunit.pow k
  let φB : B →+* R' := IsLocalization.lift (M := Algebra.algebraMapSubmonoid A' (Submonoid.powers g)) hunits
  have hφB : ∀ a' : A', φB (algebraMap A' B a') = φ' a' :=
    fun a' => IsLocalization.lift_eq (M := Algebra.algebraMapSubmonoid A' (Submonoid.powers g)) hunits a'

  letI iAgR' : Algebra Ag R' := φg.toAlgebra
  letI iAR' : Algebra A R' := φ.toRingHom.toAlgebra
  haveI : IsScalarTower A Ag R' := IsScalarTower.of_algebraMap_eq' (RingHom.ext fun a => (hφg a).symm)
  letI iCR' : Algebra C R' := (φg.comp (algebraMap C Ag)).toAlgebra
  haveI : IsScalarTower C Ag R' := IsScalarTower.of_algebraMap_eq' rfl
  have hδφ : smoothnessDefect (Spec.map (CommRingCat.ofHom (algebraMap R A)))
      (Spec.map (CommRingCat.ofHom φ.toRingHom)) =
      Module.length R' (Submodule.torsion R' (R' ⊗[Ag] Ω[Ag⁄R])) := by
    rw [smoothnessDefect_Spec_eq]
    haveI : Algebra.FormallyEtale A Ag := Algebra.FormallyEtale.of_isLocalization (Submonoid.powers g)
    exact (length_torsion_baseChange_kaehler_eq_of_formallyEtale R A Ag R').symm

  letI iC'B : Algebra C' B := θ'.toRingHom.toAlgebra
  haveI : IsScalarTower C C' B := IsScalarTower.of_algebraMap_eq' (θ'.comp_algebraMap).symm
  haveI : IsScalarTower R C' B := IsScalarTower.of_algebraMap_eq' (by
    rw [IsScalarTower.algebraMap_eq R C C', ← RingHom.comp_assoc, ← IsScalarTower.algebraMap_eq C C' B,
      IsScalarTower.algebraMap_eq R C B])
  haveI : IsScalarTower R A' B := IsScalarTower.of_algebraMap_eq' (by
    rw [IsScalarTower.algebraMap_eq R A A', ← RingHom.comp_assoc]
    have hl : (algebraMap A' B).comp (algebraMap A A') = algebraMap A B := lam.comp_algebraMap
    rw [hl, ← IsScalarTower.algebraMap_eq R A B])

  have hφBAg : φB.comp (algebraMap Ag B) = φg := by
    apply IsLocalization.ringHom_ext (Submonoid.powers g)
    ext a
    simp only [RingHom.comp_apply]
    rw [hφg, ← IsScalarTower.algebraMap_apply A Ag B, IsScalarTower.algebraMap_apply A A' B, hφB, hφ']
  letI iBR' : Algebra B R' := φB.toAlgebra
  letI iA'R' : Algebra A' R' := φ'.toRingHom.toAlgebra
  haveI : IsScalarTower A' B R' := IsScalarTower.of_algebraMap_eq' (RingHom.ext fun a' => (hφB a').symm)
  letI iC'R' : Algebra C' R' := (φB.comp θ'.toRingHom).toAlgebra
  haveI : IsScalarTower C' B R' := IsScalarTower.of_algebraMap_eq' rfl
  have hδφ' : smoothnessDefect (Spec.map (CommRingCat.ofHom (algebraMap R A')))
      (Spec.map (CommRingCat.ofHom φ'.toRingHom)) =
      Module.length R' (Submodule.torsion R' (R' ⊗[B] Ω[B⁄R])) := by
    rw [smoothnessDefect_Spec_eq]
    exact (length_torsion_baseChange_kaehler_eq_of_formallyEtale R A' B R').symm

  have hψ : ∀ c : C, algebraMap C' R' (algebraMap C C' c) = algebraMap C R' c := by
    intro c
    change φB (θ' (algebraMap C C' c)) = φg (algebraMap C Ag c)
    rw [θ'.commutes, IsScalarTower.algebraMap_apply C Ag B, ← RingHom.comp_apply, hφBAg]

  obtain ⟨eF⟩ := KaehlerDifferential.nonempty_baseChange_linearEquiv_quotient_span_tmul_D_of_surjective
    (R := R) (C := C) (A := Ag) (R' := R') hθ
  obtain ⟨eF'⟩ := KaehlerDifferential.nonempty_baseChange_linearEquiv_quotient_span_tmul_D_of_surjective
    (R := R) (C := C') (A := B) (R' := R') hθ's
  rw [hδφ, hδφ', smoothnessDefect_eq_length_torsion_global.length_torsion_eq_of_equiv' eF,
    smoothnessDefect_eq_length_torsion_global.length_torsion_eq_of_equiv' eF']

  obtain ⟨hregC', hJC'⟩ := AffineDilatation.isSMulRegular_and_map_eq_span_singleton JC (algebraMap R C π) hπJC
  have hπJ' : algebraMap A Ag (algebraMap R A π) ∈ J.map (algebraMap A Ag) := Ideal.mem_map_of_mem _ hπJ
  obtain ⟨hregB, -⟩ := AffineDilatation.isSMulRegular_and_map_eq_span_singleton (J.map (algebraMap A Ag))
    (algebraMap A Ag (algebraMap R A π)) hπJ'
  set πC' : C' := algebraMap R C' π with hπC'
  have hιπ : algebraMap C C' (algebraMap R C π) = πC' := (IsScalarTower.algebraMap_apply R C C' π).symm
  have hex : ∀ f : RingHom.ker (algebraMap C Ag), ∃ f' : C', πC' ^ 2 * f' = algebraMap C C' (f : C) := by
    rintro ⟨f, hf⟩
    have h1 : algebraMap C C' f ∈ (JC.map (algebraMap C C')) ^ 2 := by
      rw [← Ideal.map_pow]; exact Ideal.mem_map_of_mem _ (hIJ2 hf)
    rw [hJC', hιπ, Ideal.span_singleton_pow, Ideal.mem_span_singleton'] at h1
    obtain ⟨f', hf'⟩ := h1
    exact ⟨f', by rw [mul_comm]; exact hf'⟩
  choose fp hfp using hex
  have hθ'ι : ∀ f : RingHom.ker (algebraMap C Ag), θ' (algebraMap C C' (f : C)) = 0 := by
    rintro ⟨f, hf⟩
    rw [θ'.commutes, IsScalarTower.algebraMap_apply C Ag B, RingHom.mem_ker.mp hf, map_zero]
  have hθ'fp : ∀ f : RingHom.ker (algebraMap C Ag), θ' (fp f) = 0 := by
    intro f
    have h1 : θ' (πC' ^ 2 * fp f) = 0 := by rw [hfp, hθ'ι]
    rw [map_mul, map_pow] at h1
    have hπB : θ' πC' = algebraMap Ag B (algebraMap A Ag (algebraMap R A π)) := by
      rw [hπC', IsScalarTower.algebraMap_apply R C C' π, θ'.commutes, ← IsScalarTower.algebraMap_apply R C B,
        IsScalarTower.algebraMap_apply R Ag B, IsScalarTower.algebraMap_apply R A Ag]
    have h2 : (algebraMap A Ag (algebraMap R A π)) ^ 2 • θ' (fp f) = 0 := by
      rw [Algebra.smul_def, map_pow, ← hπB]; exact h1
    exact (hregB.pow 2) (show (algebraMap A Ag (algebraMap R A π)) ^ 2 • θ' (fp f) =
      (algebraMap A Ag (algebraMap R A π)) ^ 2 • (0 : B) by rw [h2, smul_zero])

  let N : Submodule R' (R' ⊗[C] Ω[C⁄R]) :=
    Submodule.span R' (Set.range fun f : RingHom.ker (algebraMap C Ag) => (1 : R') ⊗ₜ[C] D R C (f : C))
  let N'full : Submodule R' (R' ⊗[C'] Ω[C'⁄R]) :=
    Submodule.span R' (Set.range fun f' : RingHom.ker (algebraMap C' B) => (1 : R') ⊗ₜ[C'] D R C' (f' : C'))
  let N'' : Submodule R' (R' ⊗[C'] Ω[C'⁄R]) :=
    Submodule.span R' (Set.range fun f : RingHom.ker (algebraMap C Ag) => (1 : R') ⊗ₜ[C'] D R C' (fp f))
  change Module.length R' (Submodule.torsion R' ((R' ⊗[C'] Ω[C'⁄R]) ⧸ N'full)) + 1 ≤
    max 1 (Module.length R' (Submodule.torsion R' ((R' ⊗[C] Ω[C⁄R]) ⧸ N)))

  have hRC' : ∀ r : R, algebraMap C' R' (algebraMap R C' r) = algebraMap R R' r := by
    intro r
    rw [IsScalarTower.algebraMap_apply R C C' r, hψ]
    change φg (algebraMap C Ag (algebraMap R C r)) = algebraMap R R' r
    rw [← IsScalarTower.algebraMap_apply R C Ag, IsScalarTower.algebraMap_apply R A Ag, hφg, AlgHom.commutes]
  set π' : R' := algebraMap R R' π with hπ'def
  have hπ'irr : Irreducible π' := by
    rw [IsDiscreteValuationRing.irreducible_iff_uniformizer, ← hR'.map_maximalIdeal, hπ, Ideal.map_span,
      Set.image_singleton]
  have hπ'ne : π' ≠ 0 := hπ'irr.ne_zero
  have hψπ : algebraMap C' R' πC' = π' := by rw [hπC', hRC']

  have hN''le : N'' ≤ N'full := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨f, rfl⟩
    exact Submodule.subset_span ⟨⟨fp f, RingHom.mem_ker.mpr (hθ'fp f)⟩, rfl⟩

  have htmul : ∀ (c : C') (m : Ω[C'⁄R]),
      ((1 : R') ⊗ₜ[C'] (c • m) : R' ⊗[C'] Ω[C'⁄R]) = algebraMap C' R' c • ((1 : R') ⊗ₜ[C'] m) :=
    fun c m => one_tmul_smul_eq c m
  have hπC'sq : πC' ^ 2 = algebraMap R C' (π ^ 2) := by rw [hπC', map_pow]
  have hIC' : ∀ x ∈ (RingHom.ker (algebraMap C Ag)).map (algebraMap C C'),
      θ' x = 0 ∧ ((1 : R') ⊗ₜ[C'] D R C' x) ∈ N'' := by
    intro x hx
    refine Submodule.span_induction (p := fun x _ => θ' x = 0 ∧ ((1 : R') ⊗ₜ[C'] D R C' x) ∈ N'') ?_ ?_ ?_ ?_ hx
    · rintro _ ⟨f, hf, rfl⟩
      refine ⟨hθ'ι ⟨f, hf⟩, ?_⟩
      rw [← hfp ⟨f, hf⟩, Derivation.leibniz, hπC'sq, Derivation.map_algebraMap, smul_zero, add_zero, htmul]
      exact N''.smul_mem _ (Submodule.subset_span ⟨⟨f, hf⟩, rfl⟩)
    · exact ⟨map_zero _, by rw [map_zero, TensorProduct.tmul_zero]; exact Submodule.zero_mem _⟩
    · rintro x y - - ⟨hx0, hx⟩ ⟨hy0, hy⟩
      exact ⟨by rw [map_add, hx0, hy0, add_zero], by rw [map_add, TensorProduct.tmul_add]; exact N''.add_mem hx hy⟩
    · rintro c x - ⟨hx0, hx⟩
      refine ⟨by rw [smul_eq_mul, map_mul, hx0, mul_zero], ?_⟩
      rw [smul_eq_mul, Derivation.leibniz, TensorProduct.tmul_add, htmul, htmul]
      have hψx : algebraMap C' R' x = 0 := by
        change φB (θ' x) = 0
        rw [hx0, map_zero]
      rw [hψx, zero_smul, add_zero]
      exact N''.smul_mem _ hx

  have htors : ∀ x ∈ N'full, ∃ s : R', s ≠ 0 ∧ s • x ∈ N'' := by
    intro x hx
    refine Submodule.span_induction (p := fun x _ => ∃ s : R', s ≠ 0 ∧ s • x ∈ N'') ?_ ?_ ?_ ?_ hx
    · rintro _ ⟨⟨f', hf'⟩, rfl⟩
      have h0 : θ' f' = 0 := RingHom.mem_ker.mp hf'
      obtain ⟨ν, hν⟩ := (hθ'k f').mp h0
      refine ⟨π' ^ ν, pow_ne_zero ν hπ'ne, ?_⟩
      have h1 := (hIC' _ hν).2
      rw [Derivation.leibniz, TensorProduct.tmul_add, htmul, htmul, map_pow, hψπ] at h1
      have h2 : (D R C') ((algebraMap R _ π) ^ ν) = 0 := by
        rw [← map_pow]; exact Derivation.map_algebraMap _ _
      rw [h2, TensorProduct.tmul_zero, smul_zero, add_zero] at h1
      simpa only using h1
    · exact ⟨1, one_ne_zero, by rw [smul_zero]; exact Submodule.zero_mem _⟩
    · rintro x y - - ⟨s, hs, hsx⟩ ⟨t, ht, hty⟩
      refine ⟨s * t, mul_ne_zero hs ht, ?_⟩
      rw [smul_add]
      exact N''.add_mem (by rw [mul_comm, mul_smul]; exact N''.smul_mem t hsx)
        (by rw [mul_smul]; exact N''.smul_mem s hty)
    · rintro a x - ⟨s, hs, hsx⟩
      refine ⟨s, hs, ?_⟩
      rw [smul_comm]
      exact N''.smul_mem _ hsx
  have hmono : Module.length R' (Submodule.torsion R' ((R' ⊗[C'] Ω[C'⁄R]) ⧸ N'full)) ≤
      Module.length R' (Submodule.torsion R' ((R' ⊗[C'] Ω[C'⁄R]) ⧸ N'')) :=
    length_torsion_quotient_mono_of_forall_exists_smul_mem N'' N'full hN''le htors

  haveI : IsScalarTower C C' R' := IsScalarTower.of_algebraMap_eq' (RingHom.ext fun c => (hψ c).symm)
  let bF := Algebra.TensorProduct.basis R' b
  let bF' := Algebra.TensorProduct.basis R' b'
  let e0 : (Fin r ⊕ Fin n → R') ≃ₗ[R'] ((Fin r → R') × (Fin n → R')) := LinearEquiv.sumArrowLequivProdArrow (Fin r) (Fin n) R' R'
  let κ : (R' ⊗[C] Ω[C⁄R]) ≃ₗ[R'] ((Fin r → R') × (Fin n → R')) := bF.equivFun.trans e0
  let κ' : (R' ⊗[C'] Ω[C'⁄R]) ≃ₗ[R'] ((Fin r → R') × (Fin n → R')) := bF'.equivFun.trans e0
  let Dm : ((Fin r → R') × (Fin n → R')) →ₗ[R'] ((Fin r → R') × (Fin n → R')) := (LinearMap.id : (Fin r → R') →ₗ[R'] (Fin r → R')).prodMap
    (π' • (LinearMap.id : (Fin n → R') →ₗ[R'] (Fin n → R')))
  have he0 : ∀ f : Fin r ⊕ Fin n → R', e0 f = (fun i => f (Sum.inl i), fun j => f (Sum.inr j)) :=
    fun f => rfl
  have hDmap : ∀ (u : Fin r → R') (w : Fin n → R'), Dm (u, w) = (u, π' • w) := fun u w => rfl

  let Φ : (R' ⊗[C] Ω[C⁄R]) →ₗ[R'] (R' ⊗[C'] Ω[C'⁄R]) :=
    ((KaehlerDifferential.mapBaseChange R C C').baseChange R').comp
      (TensorProduct.AlgebraTensorModule.cancelBaseChange C C' R' R' Ω[C⁄R]).symm.toLinearMap
  have hΦ : ∀ m : Ω[C⁄R], Φ ((1 : R') ⊗ₜ[C] m) = (1 : R') ⊗ₜ[C'] KaehlerDifferential.map R R C C' m := by
    intro m
    change ((KaehlerDifferential.mapBaseChange R C C').baseChange R')
      ((TensorProduct.AlgebraTensorModule.cancelBaseChange C C' R' R' Ω[C⁄R]).symm ((1 : R') ⊗ₜ[C] m)) = _
    rw [TensorProduct.AlgebraTensorModule.cancelBaseChange_symm_tmul, LinearMap.baseChange_tmul,
      KaehlerDifferential.mapBaseChange_tmul]
    exact congrArg ((1 : R') ⊗ₜ[C'] ·) (one_smul C' ((KaehlerDifferential.map R R C C') m))
  have hmap_y : ∀ i, KaehlerDifferential.map R R C C' (b (Sum.inl i)) = b' (Sum.inl i) := by
    intro i; rw [hby, KaehlerDifferential.map_D, hb'y]
  have hmap_z : ∀ j, KaehlerDifferential.map R R C C' (b (Sum.inr j)) = πC' • b' (Sum.inr j) := by
    intro j; rw [hbz, KaehlerDifferential.map_D, hπC', hb'z]
  have hKC : (κ'.toLinearMap.comp Φ) = Dm.comp κ.toLinearMap := by
    refine bF.ext fun k => ?_
    rcases k with i | j
    · simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
      have h1 : Φ (bF (Sum.inl i)) = bF' (Sum.inl i) := by
        rw [Algebra.TensorProduct.basis_apply, hΦ, hmap_y, (Algebra.TensorProduct.basis_apply b' _).symm]
      change κ' (Φ (bF (Sum.inl i))) = Dm (κ (bF (Sum.inl i)))
      rw [h1]
      change e0 (bF'.equivFun (bF' (Sum.inl i))) = Dm (e0 (bF.equivFun (bF (Sum.inl i))))
      refine Prod.ext (funext fun i' => ?_) (funext fun j' => ?_)
      · simp only [Module.Basis.equivFun_apply, Module.Basis.repr_self, he0, hDmap]
        try simp [Finsupp.single_apply, Prod.smul_mk, Pi.smul_apply, smul_ite]
      · simp only [Module.Basis.equivFun_apply, Module.Basis.repr_self, he0, hDmap]
        try simp [Finsupp.single_apply, Prod.smul_mk, Pi.smul_apply, smul_ite]
    · simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
      have h1 : Φ (bF (Sum.inr j)) = π' • bF' (Sum.inr j) := by
        rw [Algebra.TensorProduct.basis_apply, hΦ, hmap_z, htmul, hψπ, (Algebra.TensorProduct.basis_apply b' _).symm]
      change κ' (Φ (bF (Sum.inr j))) = Dm (κ (bF (Sum.inr j)))
      rw [h1, map_smul]
      change π' • e0 (bF'.equivFun (bF' (Sum.inr j))) = Dm (e0 (bF.equivFun (bF (Sum.inr j))))
      refine Prod.ext (funext fun i' => ?_) (funext fun j' => ?_)
      · simp only [Module.Basis.equivFun_apply, Module.Basis.repr_self, he0, hDmap]
        try simp [Finsupp.single_apply, Prod.smul_mk, Pi.smul_apply, smul_ite]
      · simp only [Module.Basis.equivFun_apply, Module.Basis.repr_self, he0, hDmap]
        try simp [Finsupp.single_apply, Prod.smul_mk, Pi.smul_apply, smul_ite]
  have hKC' : ∀ x, κ' (Φ x) = Dm (κ x) := fun x => congrArg (fun L => L x) hKC |> fun h => by
    simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe] using h

  let I2 : Ideal R' := Ideal.span {π' ^ 2}
  have hΦgen : ∀ f : RingHom.ker (algebraMap C Ag),
      Φ ((1 : R') ⊗ₜ[C] D R C (f : C)) = (π' ^ 2) • ((1 : R') ⊗ₜ[C'] D R C' (fp f)) := by
    intro f
    rw [hΦ, KaehlerDifferential.map_D, ← hfp f, Derivation.leibniz, hπC'sq, Derivation.map_algebraMap, smul_zero,
      add_zero, ← hπC'sq, htmul, map_pow, hψπ]
  have hNΦ : N.map Φ = I2 • N'' := by
    apply le_antisymm
    · rw [Submodule.map_span, Submodule.span_le]
      rintro _ ⟨_, ⟨f, rfl⟩, rfl⟩
      rw [hΦgen]
      exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) (Submodule.subset_span ⟨f, rfl⟩)
    · rw [Submodule.smul_le]
      rintro a ha x hx
      obtain ⟨t, rfl⟩ := Ideal.mem_span_singleton'.mp ha
      rw [mul_smul]
      refine Submodule.smul_mem _ t ?_
      have hle : N'' ≤ (N.map Φ).comap ((π' ^ 2) • LinearMap.id) := by
        refine Submodule.span_le.mpr ?_
        rintro _ ⟨f, rfl⟩
        change ((1 : R') ⊗ₜ[C'] D R C' (fp f)) ∈ Submodule.comap ((π' ^ 2) • LinearMap.id) (N.map Φ)
        rw [Submodule.mem_comap, LinearMap.smul_apply, LinearMap.id_apply, ← hΦgen]
        exact Submodule.mem_map_of_mem (Submodule.subset_span ⟨f, rfl⟩)
      simpa only [Submodule.mem_comap, LinearMap.smul_apply, LinearMap.id_apply] using hle hx
  have hNcDm : (N.map κ.toLinearMap).map Dm = I2 • N''.map κ'.toLinearMap := by
    rw [← Submodule.map_comp, ← hKC, Submodule.map_comp, hNΦ, Submodule.map_smul'']

  let Fsub : Submodule R' ((Fin r → R') × (Fin n → R')) := (⊤ : Submodule R' (Fin r → R')).prod ((Ideal.span {π'} : Ideal R') • ⊤)
  have hDm_mem : ∀ v : ((Fin r → R') × (Fin n → R')), Dm v ∈ Fsub := by
    rintro ⟨u, w⟩
    refine ⟨trivial, ?_⟩
    change π' • w ∈ (Ideal.span {π'} : Ideal R') • (⊤ : Submodule R' (Fin n → R'))
    exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) trivial
  have hDm_inj : Function.Injective Dm := by
    rintro ⟨u, w⟩ ⟨u', w'⟩ h
    simp only [Dm, LinearMap.prodMap_apply, LinearMap.id_apply, LinearMap.smul_apply, Prod.mk.injEq] at h
    obtain ⟨rfl, h2⟩ := h
    have : w = w' := smul_right_injective (Fin n → R') hπ'ne h2
    rw [this]
  have hDm_surj : ∀ y ∈ Fsub, ∃ v, Dm v = y := by
    rintro ⟨u, w'⟩ ⟨-, hw'⟩
    change w' ∈ (Ideal.span {π'} : Ideal R') • (⊤ : Submodule R' (Fin n → R')) at hw'
    rw [Submodule.ideal_span_singleton_smul] at hw'
    obtain ⟨w, -, rfl⟩ := hw'
    exact ⟨(u, w), rfl⟩
  let Dm' : ((Fin r → R') × (Fin n → R')) ≃ₗ[R'] Fsub := LinearEquiv.ofBijective (Dm.codRestrict Fsub hDm_mem)
    ⟨fun a b h => hDm_inj (congrArg Subtype.val h), fun y => by
      obtain ⟨v, hv⟩ := hDm_surj y.1 y.2; exact ⟨v, Subtype.ext hv⟩⟩

  have hJ1hyp : I2 • N''.map κ'.toLinearMap ≤ Fsub := by
    rw [← hNcDm]; rintro _ ⟨v, -, rfl⟩; exact hDm_mem v
  have hJ1 := IsDiscreteValuationRing.length_torsion_quotient_add_finrank_le_of_sq_smul_le_prod π' hπ'irr r n
    (N''.map κ'.toLinearMap) hJ1hyp
  have eq1 : Module.length R' (Submodule.torsion R' ((R' ⊗[C'] Ω[C'⁄R]) ⧸ N'')) =
      Module.length R' (Submodule.torsion R' (((Fin r → R') × (Fin n → R')) ⧸ N''.map κ'.toLinearMap)) :=
    smoothnessDefect_eq_length_torsion_global.length_torsion_eq_of_equiv' (Submodule.Quotient.equiv _ _ κ' rfl)
  have hmapDm' : (N.map (κ.trans Dm').toLinearMap) = (I2 • N''.map κ'.toLinearMap).comap Fsub.subtype := by
    rw [← hNcDm]
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨κ x, Submodule.mem_map_of_mem hx, rfl⟩
    · rintro ⟨v, ⟨x, hx, rfl⟩, hv⟩
      refine ⟨x, hx, Subtype.ext ?_⟩
      change Dm (κ x) = Fsub.subtype y
      exact hv
  have eq2 : Module.length R' (Submodule.torsion R' ((R' ⊗[C] Ω[C⁄R]) ⧸ N)) =
      Module.length R' (Submodule.torsion R' (Fsub ⧸ (I2 • N''.map κ'.toLinearMap).comap Fsub.subtype)) :=
    smoothnessDefect_eq_length_torsion_global.length_torsion_eq_of_equiv'
      (Submodule.Quotient.equiv _ _ (κ.trans Dm') hmapDm')
  have key : Module.length R' (Submodule.torsion R' ((R' ⊗[C'] Ω[C'⁄R]) ⧸ N'')) +
      Module.finrank R' (N''.map κ'.toLinearMap) ≤
      Module.length R' (Submodule.torsion R' ((R' ⊗[C] Ω[C⁄R]) ⧸ N)) := by
    rw [eq1, eq2]; exact hJ1

  by_cases hρ : Module.finrank R' (N''.map κ'.toLinearMap) = 0
  · have hbot : N''.map κ'.toLinearMap = ⊥ := by
      rw [Submodule.eq_bot_iff]
      intro x hx
      obtain ⟨a, ha, hax⟩ := (Module.finrank_eq_zero_iff.mp hρ) ⟨x, hx⟩
      have h' : a • x = 0 := congrArg Subtype.val hax
      exact (smul_eq_zero.mp h').resolve_left ha
    have h0 : Module.length R' (Submodule.torsion R' (((Fin r → R') × (Fin n → R')) ⧸ N''.map κ'.toLinearMap)) = 0 := by
      rw [hbot]
      have e := (Submodule.quotEquivOfEqBot (⊥ : Submodule R' ((Fin r → R') × (Fin n → R'))) rfl)
      rw [smoothnessDefect_eq_length_torsion_global.length_torsion_eq_of_equiv' e,
        Submodule.isTorsionFree_iff_torsion_eq_bot.mp inferInstance]
      exact Module.length_bot
    have h0' : Module.length R' (Submodule.torsion R' ((R' ⊗[C'] Ω[C'⁄R]) ⧸ N'full)) = 0 :=
      le_antisymm (hmono.trans (by rw [eq1, h0])) bot_le
    rw [h0', zero_add]
    exact le_max_left _ _
  · have h1 : (1 : ℕ∞) ≤ Module.finrank R' (N''.map κ'.toLinearMap) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr hρ
    calc Module.length R' (Submodule.torsion R' ((R' ⊗[C'] Ω[C'⁄R]) ⧸ N'full)) + 1
        ≤ Module.length R' (Submodule.torsion R' ((R' ⊗[C'] Ω[C'⁄R]) ⧸ N'')) +
            Module.finrank R' (N''.map κ'.toLinearMap) := add_le_add hmono h1
      _ ≤ Module.length R' (Submodule.torsion R' ((R' ⊗[C] Ω[C⁄R]) ⧸ N)) := key
      _ ≤ _ := le_max_right _ _

end S_NeronModelInfra_smoothnessDefect_affineDilatation_add_one_le_of_isSmoothAt_of_mem_freeLocus
end P2MW
export P2MW.S_NeronModelInfra_smoothnessDefect_affineDilatation_add_one_le_of_isSmoothAt_of_mem_freeLocus (solution)
