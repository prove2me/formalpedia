-- Prove2me | solution 1 for IsLocalRing.isDomain_localization_atPrime_tensorProduct_of_isRegularLocalRing_quotient_of_perfectField
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/fb6a79ba-5e73-560c-8914-5a08b74d5520

import Mathlib
import Theorems.Thm_isRegularLocalRing_localization_atPrime_of_isStandardSmooth
import Theorems.Thm_Algebra_FormallySmooth_of_maximalIdeal_eq_span_of_perfectField
import Theorems.Thm_IsRegularLocalRing_isDomain
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IsLocalRing_isDomain_localization_atPrime_tensorProduct_of_isRegularLocalRing_quotient_of_perfectField
p2m_attr_erase "simp" "RegularLocalRingQuotientAscent.dualNumberFst_apply"

set_option autoImplicit false
set_option maxHeartbeats 6400000
set_option synthInstance.maxHeartbeats 1600000

universe u

open TensorProduct IsLocalRing

namespace Algebra p2m_export "Algebra" "FormallySmooth algebraMap_eq_smul_one EssFiniteType essFiniteType_iff_exists_subalgebra FormallySmooth.of_equiv TensorProduct.includeRight TensorProduct.tmul_mul_tmul TensorProduct.lift_tmul mk algebraMap TensorProduct.lift FormallySmooth.comp FormallySmooth.of_perfectField TensorProduct.algebraMap_apply IsSmoothAt.exists_notMem_isStandardSmooth IsSmoothAt FinitePresentation.of_finiteType smul_def EssFiniteType.of_comp TensorProduct.includeLeft restrictScalars commutes' TensorProduct.includeLeftRingHom FormallySmooth.of_isLocalization FinitePresentation FormallySmooth.of_maximalIdeal_eq_span_of_perfectField" namespace FormallySmooth p2m_export "Algebra.FormallySmooth" "of_equiv comp of_perfectField mk lift of_isLocalization of_maximalIdeal_eq_span_of_perfectField" end Algebra.FormallySmooth
p2m_open_scoped "Algebra Algebra.FormallySmooth" in

theorem Algebra.FormallySmooth.isRegularLocalRing_localization_atPrime_baseChange
    (𝔽 : Type u) [Field 𝔽] (S : Type u) [CommRing S] [Algebra 𝔽 S] [Algebra.EssFiniteType 𝔽 S] [Algebra.FormallySmooth 𝔽 S]
    (k : Type u) [Field k] [Algebra 𝔽 k] (𝔮 : Ideal (k ⊗[𝔽] S)) [𝔮.IsPrime] :
    IsRegularLocalRing (Localization.AtPrime 𝔮) := by
  classical
  let B := k ⊗[𝔽] S
  haveI : Algebra.FormallySmooth k B := inferInstance
  haveI : Algebra.EssFiniteType k B := inferInstance

  obtain ⟨B₀, M, hft, hloc⟩ := (Algebra.essFiniteType_iff_exists_subalgebra k B).mp (inferInstance : Algebra.EssFiniteType k B)
  haveI := hft
  haveI := hloc
  haveI : Algebra.FinitePresentation k B₀ := (Algebra.FinitePresentation.of_finiteType).mp hft

  let T := Localization.AtPrime 𝔮
  let 𝔭 : Ideal B₀ := 𝔮.comap (algebraMap B₀ B)
  haveI h𝔭 : 𝔭.IsPrime := Ideal.comap_isPrime _ _
  haveI : IsLocalization.AtPrime T 𝔭 :=
    IsLocalization.isLocalization_isLocalization_atPrime_isLocalization M (S := B) T 𝔮

  haveI : Algebra.FormallySmooth B T :=
    Algebra.FormallySmooth.of_isLocalization (R := k ⊗[𝔽] S) (Rₘ := Localization.AtPrime 𝔮) (M := 𝔮.primeCompl)
  haveI : Algebra.FormallySmooth k T := Algebra.FormallySmooth.comp k B T
  haveI : Algebra.IsSmoothAt k 𝔭 := by
    show Algebra.FormallySmooth k (Localization.AtPrime 𝔭)
    exact Algebra.FormallySmooth.of_equiv (A := T)
      ((IsLocalization.algEquiv 𝔭.primeCompl T (Localization.AtPrime 𝔭)).restrictScalars k)

  obtain ⟨f, hf, hstd⟩ := Algebra.IsSmoothAt.exists_notMem_isStandardSmooth (R := k) 𝔭
  haveI := hstd
  let C := Localization.Away f
  have hdisj : Disjoint (↑(Submonoid.powers f) : Set B₀) ↑𝔭 := by
    exact (Ideal.disjoint_powers_iff_notMem_of_isPrime f).mpr hf
  haveI h𝔭' : (𝔭.map (algebraMap B₀ C)).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers f) C 𝔭 h𝔭 hdisj
  have hcomap : (𝔭.map (algebraMap B₀ C)).comap (algebraMap B₀ C) = 𝔭 :=
    IsLocalization.under_map_of_isPrime_disjoint (Submonoid.powers f) C h𝔭 hdisj

  have hreg : IsRegularLocalRing (Localization.AtPrime (𝔭.map (algebraMap B₀ C))) :=
    isRegularLocalRing_localization_atPrime_of_isStandardSmooth k C (𝔭.map (algebraMap B₀ C))

  haveI : IsLocalization.AtPrime (Localization.AtPrime (𝔭.map (algebraMap B₀ C))) 𝔭 := by
    have this := IsLocalization.isLocalization_isLocalization_atPrime_isLocalization (Submonoid.powers f)
      (S := C) (Localization.AtPrime (𝔭.map (algebraMap B₀ C))) (𝔭.map (algebraMap B₀ C))
    have hM : ((𝔭.map (algebraMap B₀ C)).comap (algebraMap B₀ C)).primeCompl = 𝔭.primeCompl := by
      ext x
      simp only [Ideal.primeCompl, Submonoid.mem_mk, Subsemigroup.mem_mk, Set.mem_compl_iff, SetLike.mem_coe, hcomap]
    show IsLocalization 𝔭.primeCompl _
    rw [← hM]
    exact this
  let e : Localization.AtPrime (𝔭.map (algebraMap B₀ C)) ≃ₐ[B₀] T :=
    IsLocalization.algEquiv 𝔭.primeCompl _ _
  haveI := hreg
  exact IsRegularLocalRing.of_ringEquiv e.toRingEquiv

namespace GeomRegDomainK11FS

theorem formallySmooth_of_isRegularLocalRing_of_ringKrullDim_le_one
    (𝔽 : Type u) [Field 𝔽] [PerfectField 𝔽] (S : Type u) [CommRing S] [IsRegularLocalRing S]
    [Algebra 𝔽 S] [Algebra.EssFiniteType 𝔽 S] (hdim : ringKrullDim S ≤ 1) :
    Algebra.FormallySmooth 𝔽 S := by
  classical
  haveI : IsDomain S := IsRegularLocalRing.isDomain S
  have hfg : (maximalIdeal S).FG := IsNoetherian.noetherian _
  have hsf : ((maximalIdeal S).spanFinrank : WithBot ℕ∞) = ringKrullDim S := IsRegularLocalRing.spanFinrank_maximalIdeal
  by_cases h0 : maximalIdeal S = ⊥
  ·
    have hS : IsField S := (isField_iff_maximalIdeal_eq).mpr h0
    letI : Field S := hS.toField
    exact Algebra.FormallySmooth.of_perfectField
  ·
    obtain ⟨s, hs, hspan⟩ := Submodule.FG.exists_span_set_encard_eq_spanFinrank hfg
    have hcard : s.encard ≤ 1 := by
      rw [hs]
      have : ((maximalIdeal S).spanFinrank : WithBot ℕ∞) ≤ 1 := hsf ▸ hdim
      exact_mod_cast this

    rcases Set.encard_le_one_iff_eq.mp hcard with hs0 | ⟨u, rfl⟩
    · exfalso
      apply h0
      rw [← hspan, hs0]
      try exact Submodule.span_empty
    · have hu : maximalIdeal S = Ideal.span {u} := by
        rw [← hspan]
        try rfl
      have hu0 : u ≠ 0 := by
        intro h; apply h0; rw [hu, h, Ideal.span_singleton_eq_bot]
      exact Algebra.FormallySmooth.of_maximalIdeal_eq_span_of_perfectField 𝔽 S u hu0 hu

end GeomRegDomainK11FS

namespace GeomRegDomainK11

noncomputable def quotAlg {A : Type u} [CommRing A] [IsLocalRing A] (ϖ : A) (hϖA : maximalIdeal A = Ideal.span {ϖ})
    (T : Type u) [CommRing T] [Algebra A T] (hT : algebraMap A T ϖ = 0) : ResidueField A →+* T :=
  Ideal.Quotient.lift (maximalIdeal A) (algebraMap A T) (fun a ha => by
    rw [hϖA, Ideal.mem_span_singleton] at ha
    obtain ⟨c, rfl⟩ := ha
    rw [map_mul, hT, zero_mul])

theorem quotAlg_residue {A : Type u} [CommRing A] [IsLocalRing A] (ϖ : A) (hϖA : maximalIdeal A = Ideal.span {ϖ})
    (T : Type u) [CommRing T] [Algebra A T] (hT : algebraMap A T ϖ = 0) (a : A) :
    quotAlg ϖ hϖA T hT (residue A a) = algebraMap A T a :=
  Ideal.Quotient.lift_mk _ _ _

end GeomRegDomainK11

open GeomRegDomainK11 in
theorem solution
    {A : Type u} [CommRing A] [IsLocalRing A] (ϖ : A) (hϖA : IsLocalRing.maximalIdeal A = Ideal.span {ϖ})
    [PerfectField (IsLocalRing.ResidueField A)]
    (𝒪 : Type u) [CommRing 𝒪] [IsLocalRing 𝒪] [IsNoetherianRing 𝒪] [Algebra A 𝒪] [Algebra.EssFiniteType A 𝒪]
    (hϖ : algebraMap A 𝒪 ϖ ∈ IsLocalRing.maximalIdeal 𝒪)
    (hreg : IsRegularLocalRing (𝒪 ⧸ Ideal.span {algebraMap A 𝒪 ϖ}))
    (hdim : ringKrullDim (𝒪 ⧸ Ideal.span {algebraMap A 𝒪 ϖ}) ≤ 1)
    (k : Type u) [Field k] [Algebra A k] (hk : algebraMap A k ϖ = 0)
    (𝔮 : Ideal (𝒪 ⊗[A] k)) [𝔮.IsPrime]
    (h𝔮 : 𝔮.comap (Algebra.TensorProduct.includeLeft (R := A) (S := A) (A := 𝒪) (B := k)).toRingHom = IsLocalRing.maximalIdeal 𝒪) :
    IsDomain (Localization.AtPrime 𝔮) := by
  classical
  set I : Ideal 𝒪 := Ideal.span {algebraMap A 𝒪 ϖ} with hI

  have hkS : algebraMap A (𝒪 ⧸ I) ϖ = 0 := by
    change Ideal.Quotient.mk I (algebraMap A 𝒪 ϖ) = 0
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span rfl)
  letI algFk : Algebra (ResidueField A) k := (quotAlg ϖ hϖA k hk).toAlgebra
  letI algFS : Algebra (ResidueField A) (𝒪 ⧸ I) := (quotAlg ϖ hϖA (𝒪 ⧸ I) hkS).toAlgebra
  haveI istk : IsScalarTower A (ResidueField A) k :=
    IsScalarTower.of_algebraMap_eq fun a => (quotAlg_residue ϖ hϖA k hk a).symm
  haveI istS : IsScalarTower A (ResidueField A) (𝒪 ⧸ I) :=
    IsScalarTower.of_algebraMap_eq fun a => (quotAlg_residue ϖ hϖA (𝒪 ⧸ I) hkS a).symm
  haveI : Algebra.EssFiniteType A (𝒪 ⧸ I) := inferInstance
  haveI : Algebra.EssFiniteType (ResidueField A) (𝒪 ⧸ I) := Algebra.EssFiniteType.of_comp A _ _

  haveI := hreg
  haveI : Algebra.FormallySmooth (ResidueField A) (𝒪 ⧸ I) :=
    GeomRegDomainK11FS.formallySmooth_of_isRegularLocalRing_of_ringKrullDim_le_one (ResidueField A) (𝒪 ⧸ I) hdim

  obtain ⟨Φ, -⟩ : ∃ Φ : 𝒪 ⊗[A] k ≃+* k ⊗[ResidueField A] (𝒪 ⧸ I), True := by

    have halgAT : ∀ a : A, algebraMap A (k ⊗[ResidueField A] (𝒪 ⧸ I)) a = algebraMap A k a ⊗ₜ 1 := fun a =>
      Algebra.TensorProduct.algebraMap_apply a
    letI algFT : Algebra (ResidueField A) (𝒪 ⊗[A] k) :=
      ((Algebra.TensorProduct.includeRight (R := A) (A := 𝒪) (B := k)).toRingHom.comp
        (algebraMap (ResidueField A) k)).toAlgebra
    have halgFT : ∀ x : ResidueField A, algebraMap (ResidueField A) (𝒪 ⊗[A] k) x =
        (1 : 𝒪) ⊗ₜ[A] algebraMap (ResidueField A) k x := fun _ => rfl

    let f : 𝒪 →ₐ[A] k ⊗[ResidueField A] (𝒪 ⧸ I) :=
      { toRingHom := (Algebra.TensorProduct.includeRight (R := ResidueField A) (A := k) (B := 𝒪 ⧸ I)).toRingHom.comp
          (Ideal.Quotient.mk I)
        commutes' := fun a => by
          have h1 : Ideal.Quotient.mk I (algebraMap A 𝒪 a) = (residue A a) • (1 : 𝒪 ⧸ I) := by
            rw [Algebra.smul_def, mul_one]
            change _ = quotAlg ϖ hϖA (𝒪 ⧸ I) hkS (residue A a)
            rw [quotAlg_residue]
            rfl
          have h2 : algebraMap A k a = (residue A a) • (1 : k) := by
            rw [Algebra.smul_def, mul_one]
            exact (quotAlg_residue ϖ hϖA k hk a).symm
          change (1 : k) ⊗ₜ[ResidueField A] (Ideal.Quotient.mk I (algebraMap A 𝒪 a)) =
            algebraMap A k a ⊗ₜ[ResidueField A] (1 : 𝒪 ⧸ I)
          rw [h1, h2, TensorProduct.smul_tmul] }
    let g : k →ₐ[A] k ⊗[ResidueField A] (𝒪 ⧸ I) :=
      { toRingHom := Algebra.TensorProduct.includeLeftRingHom
        commutes' := fun a => rfl }
    let φ : 𝒪 ⊗[A] k →ₐ[A] k ⊗[ResidueField A] (𝒪 ⧸ I) := Algebra.TensorProduct.lift f g (fun _ _ => Commute.all _ _)
    have hφ : ∀ (o : 𝒪) (c : k), φ (o ⊗ₜ c) = c ⊗ₜ Ideal.Quotient.mk I o := fun o c => by
      rw [show φ (o ⊗ₜ c) = f o * g c from Algebra.TensorProduct.lift_tmul f g _ o c]
      change ((1 : k) ⊗ₜ[ResidueField A] Ideal.Quotient.mk I o) * (c ⊗ₜ[ResidueField A] (1 : 𝒪 ⧸ I)) = _
      rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]

    have hkill : ∀ o ∈ I, (Algebra.TensorProduct.includeLeftRingHom (R := A) (A := 𝒪) (B := k)) o = 0 := by
      intro o ho
      rw [hI, Ideal.mem_span_singleton] at ho
      obtain ⟨c, rfl⟩ := ho
      change (algebraMap A 𝒪 ϖ * c) ⊗ₜ[A] (1 : k) = 0
      rw [← mul_one (1 : k), ← Algebra.TensorProduct.tmul_mul_tmul, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul,
        ← Algebra.algebraMap_eq_smul_one, hk, TensorProduct.tmul_zero, zero_mul]
    let f' : (𝒪 ⧸ I) →ₐ[ResidueField A] 𝒪 ⊗[A] k :=
      { toRingHom := Ideal.Quotient.lift I _ hkill
        commutes' := fun x => by
          obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective x
          have h1 : algebraMap (ResidueField A) (𝒪 ⧸ I) (residue A a) = Ideal.Quotient.mk I (algebraMap A 𝒪 a) :=
            quotAlg_residue ϖ hϖA (𝒪 ⧸ I) hkS a
          change Ideal.Quotient.lift I _ hkill (algebraMap (ResidueField A) (𝒪 ⧸ I) (residue A a)) = _
          have h2 : algebraMap (ResidueField A) k (residue A a) = algebraMap A k a := quotAlg_residue ϖ hϖA k hk a
          rw [h1, Ideal.Quotient.lift_mk, halgFT, h2]
          change algebraMap A 𝒪 a ⊗ₜ[A] (1 : k) = (1 : 𝒪) ⊗ₜ[A] algebraMap A k a
          rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul] }
    let g' : k →ₐ[ResidueField A] 𝒪 ⊗[A] k :=
      { toRingHom := (Algebra.TensorProduct.includeRight (R := A) (A := 𝒪) (B := k)).toRingHom
        commutes' := fun x => rfl }
    let ψ : k ⊗[ResidueField A] (𝒪 ⧸ I) →ₐ[ResidueField A] 𝒪 ⊗[A] k :=
      Algebra.TensorProduct.lift g' f' (fun _ _ => Commute.all _ _)
    have hψ : ∀ (c : k) (o : 𝒪), ψ (c ⊗ₜ Ideal.Quotient.mk I o) = o ⊗ₜ c := fun c o => by
      rw [show ψ (c ⊗ₜ Ideal.Quotient.mk I o) = g' c * f' (Ideal.Quotient.mk I o) from
        Algebra.TensorProduct.lift_tmul g' f' _ c _]
      change ((1 : 𝒪) ⊗ₜ[A] c) * Ideal.Quotient.lift I _ hkill (Ideal.Quotient.mk I o) = _
      rw [Ideal.Quotient.lift_mk]
      change ((1 : 𝒪) ⊗ₜ[A] c) * (o ⊗ₜ[A] (1 : k)) = _
      rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]
    refine ⟨RingEquiv.ofRingHom φ.toRingHom ψ.toRingHom ?_ ?_, trivial⟩
    · apply RingHom.ext
      intro z
      induction z using TensorProduct.induction_on with
      | zero => simp
      | tmul c s =>
          obtain ⟨o, rfl⟩ := Ideal.Quotient.mk_surjective s
          change φ (ψ (c ⊗ₜ Ideal.Quotient.mk I o)) = c ⊗ₜ Ideal.Quotient.mk I o
          rw [hψ, hφ]
      | add x y hx hy =>
          change φ (ψ (x + y)) = x + y
          rw [map_add, map_add]
          exact congrArg₂ (· + ·) hx hy
    · apply RingHom.ext
      intro z
      induction z using TensorProduct.induction_on with
      | zero => simp
      | tmul o c =>
          change ψ (φ (o ⊗ₜ c)) = o ⊗ₜ c
          rw [hφ, hψ]
      | add x y hx hy =>
          change ψ (φ (x + y)) = x + y
          rw [map_add, map_add]
          exact congrArg₂ (· + ·) hx hy

  let 𝔮' : Ideal (k ⊗[ResidueField A] (𝒪 ⧸ I)) := 𝔮.comap Φ.symm
  haveI : 𝔮'.IsPrime := Ideal.comap_isPrime _ _
  have hreg' : IsRegularLocalRing (Localization.AtPrime 𝔮') :=
    Algebra.FormallySmooth.isRegularLocalRing_localization_atPrime_baseChange (ResidueField A) (𝒪 ⧸ I) k 𝔮'
  haveI := hreg'
  haveI : IsDomain (Localization.AtPrime 𝔮') := IsRegularLocalRing.isDomain (Localization.AtPrime 𝔮')
  have hmap : Submonoid.map Φ.toMonoidHom 𝔮.primeCompl = 𝔮'.primeCompl := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      change Φ x ∉ 𝔮'
      intro h
      exact hx (by simpa [𝔮', Ideal.mem_comap] using h)
    · intro hy
      refine ⟨Φ.symm y, ?_, by simp⟩
      change Φ.symm y ∉ 𝔮
      intro h
      exact hy (by simpa [𝔮', Ideal.mem_comap] using h)
  let e : Localization.AtPrime 𝔮 ≃+* Localization.AtPrime 𝔮' :=
    IsLocalization.ringEquivOfRingEquiv (Localization.AtPrime 𝔮) (Localization.AtPrime 𝔮') Φ hmap
  exact Function.Injective.isDomain e.toRingHom e.injective

end S_IsLocalRing_isDomain_localization_atPrime_tensorProduct_of_isRegularLocalRing_quotient_of_perfectField
end P2MW
export P2MW.S_IsLocalRing_isDomain_localization_atPrime_tensorProduct_of_isRegularLocalRing_quotient_of_perfectField (solution)
