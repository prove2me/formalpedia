-- Prove2me | solution 1 for OAI.MaximalSeshadri.Geometry.finite_affine_jet_test
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-11-04T15:21:40.349607+00:00
-- url     : https://prove2.me/submissions/42dcf89c-d6f6-40a5-9961-879dec7305e2

import Mathlib
import Definitions.Def_MaximalSeshadriConstants
import Definitions.Def_SeshadriPrelim6

set_option Elab.async false
set_option linter.all false

section
namespace OAI

section
noncomputable section

section

namespace MaximalSeshadri.AlgebraicJets
noncomputable section
open MvPolynomial

variable {σ R : Type*} [CommRing R]

def polynomialTranslate (x : σ → R) : MvPolynomial σ R ≃ₐ[R] MvPolynomial σ R :=
  AlgEquiv.ofAlgHom (aeval (fun i => X i + C (x i)))
    (aeval (fun i => X i - C (x i)))
    (by ext i; simp)
    (by ext i; simp)

lemma polynomialTranslate_constantCoeff (x : σ → R) (p : MvPolynomial σ R) :
    constantCoeff (polynomialTranslate x p) = eval x p := by
  have h : (constantCoeff : MvPolynomial σ R →+* R).comp
      (polynomialTranslate x).toRingHom = eval x := by
    apply ringHom_ext
    · intro c; simp [polynomialTranslate]
    · intro i; simp [polynomialTranslate]
  exact RingHom.congr_fun h p

lemma idealOfVars_eq_ker_constantCoeff :
    idealOfVars σ R = RingHom.ker (constantCoeff : MvPolynomial σ R →+* R) := by
  ext p
  rw [← pow_one (idealOfVars σ R), mem_pow_idealOfVars_iff']
  change (∀ index, index.degree < 1 → p.coeff index = 0) ↔ p.coeff 0 = 0
  constructor
  · exact fun h => h 0 (by simp)
  · intro h d hd
    have hd0 : d = 0 := (Finsupp.degree_eq_zero_iff d).mp (by omega)
    simpa [hd0] using h

theorem mem_rationalPoint_pow_iff (x : σ → R) (n : ℕ) (p : MvPolynomial σ R) :
    p ∈ (RingHom.ker (eval x)) ^ n ↔
      ∀ index : σ →₀ ℕ, index.degree < n → (polynomialTranslate x p).coeff index = 0 := by
  have heq : RingHom.ker (eval x) =
      (idealOfVars σ R).map (polynomialTranslate x).symm.toRingHom := by
    simp only [RingEquiv.toRingHom_eq_coe]
    rw [Ideal.map_comap_of_equiv ((polynomialTranslate x).symm.toRingEquiv)]
    ext f
    change eval x f = 0 ↔ polynomialTranslate x f ∈ idealOfVars σ R
    rw [idealOfVars_eq_ker_constantCoeff]
    change eval x f = 0 ↔ constantCoeff (polynomialTranslate x f) = 0
    rw [polynomialTranslate_constantCoeff]
  rw [heq, ← Ideal.map_pow]
  simp only [RingEquiv.toRingHom_eq_coe]
  rw [Ideal.map_comap_of_equiv ((polynomialTranslate x).symm.toRingEquiv)]
  change polynomialTranslate x p ∈ (idealOfVars σ R) ^ n ↔ _
  exact mem_pow_idealOfVars_iff' n _

end

noncomputable section
open MvPolynomial
variable {σ R : Type*} [CommRing R]

def polynomialJetCoeffsAt (x : σ → R) (n : ℕ) :
    MvPolynomial σ R →ₗ[R] (JetIndex σ n → R) :=
  (polynomialJetCoeffs n).comp (polynomialTranslate x).toLinearMap

lemma polynomialJetCoeffsAt_ker (x : σ → R) (n : ℕ) :
    (polynomialJetCoeffsAt x n).ker =
      ((RingHom.ker (eval x)) ^ n).restrictScalars R := by
  ext p
  rw [LinearMap.mem_ker, funext_iff]
  change (∀ index : JetIndex σ n, (polynomialTranslate x p).coeff index.val = 0) ↔ _
  rw [Submodule.restrictScalars_mem, mem_rationalPoint_pow_iff]
  exact ⟨fun h d hd => h ⟨d, hd⟩, fun h d => h d.val d.property⟩

lemma polynomialJetCoeffsAt_surjective [Finite σ] (x : σ → R) (n : ℕ) :
    Function.Surjective (polynomialJetCoeffsAt x n) :=
  (polynomialJetCoeffs_surjective n).comp (polynomialTranslate x).surjective

def polynomialJetEquivAt [Finite σ] (x : σ → R) (n : ℕ) :
    (MvPolynomial σ R ⧸ (RingHom.ker (eval x)) ^ n) ≃ₗ[R] (JetIndex σ n → R) := by
  let e := LinearMap.quotKerEquivOfSurjective
    (polynomialJetCoeffsAt x n) (polynomialJetCoeffsAt_surjective x n)
  exact (Submodule.quotEquivOfEq _ _ (polynomialJetCoeffsAt_ker x n).symm).trans e

@[simp] lemma polynomialJetEquivAt_mk [Finite σ] (x : σ → R) (n : ℕ)
    (p : MvPolynomial σ R) (d : JetIndex σ n) :
    polynomialJetEquivAt x n (Ideal.Quotient.mk _ p) d =
      (polynomialTranslate x p).coeff d.val := rfl

end

noncomputable section
open MvPolynomial

variable {σ R : Type*} [CommRing R]

@[simp] lemma jetAugment_mk (n : ℕ) (hn : 0 < n) (p : MvPolynomial σ R) :
    jetAugment n hn (Ideal.Quotient.mk _ p) = constantCoeff p := by
  change (aeval (fun _ : σ => (0 : R))) p = _
  simp [aeval_def]

lemma jetAugment_surjective (n : ℕ) (hn : 0 < n) :
    Function.Surjective (jetAugment (σ := σ) (R := R) n hn) :=
  fun c => ⟨algebraMap R _ c, by simp⟩

lemma jetAugment_ker (n : ℕ) (hn : 0 < n) :
    RingHom.ker (jetAugment (σ := σ) (R := R) n hn) =
      (idealOfVars σ R).map (Ideal.Quotient.mk ((idealOfVars σ R) ^ n)) := by
  ext z
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective z
  rw [RingHom.mem_ker, jetAugment_mk,
    Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective]
  constructor
  · intro h
    exact ⟨p, by rwa [idealOfVars_eq_ker_constantCoeff, RingHom.mem_ker], rfl⟩
  · rintro ⟨f, hf, hfp⟩
    have hd : f - p ∈ (idealOfVars σ R) ^ n := Ideal.Quotient.eq.mp hfp
    have hd' := (mem_pow_idealOfVars_iff' n (f - p)).mp hd 0 (by simpa using hn)
    have hf' : constantCoeff f = 0 := by
      rwa [idealOfVars_eq_ker_constantCoeff, RingHom.mem_ker] at hf
    change constantCoeff (f - p) = 0 at hd'
    simpa [map_sub, hf'] using hd'

lemma jetAugment_ker_nilpotent (n : ℕ) (hn : 0 < n) :
    IsNilpotent (RingHom.ker (jetAugment (σ := σ) (R := R) n hn)) := by
  refine ⟨n, ?_⟩
  rw [jetAugment_ker, ← Ideal.map_pow]
  exact Ideal.map_quotient_self _

end

noncomputable section
open MvPolynomial

variable {σ F S B : Type*} [CommRing F] [CommRing S] [Algebra F S]
  [Algebra (MvPolynomial σ F) S] [IsScalarTower F (MvPolynomial σ F) S]

lemma exists_lift_with_coordinates [CommRing B] [Algebra F B]
    [Algebra.FormallySmooth (MvPolynomial σ F) S]
    (β : MvPolynomial σ F →ₐ[F] B) (α : B →ₐ[F] S)
    (hαβ : α.comp β = IsScalarTower.toAlgHom F (MvPolynomial σ F) S)
    (hα : Function.Surjective α) (hnil : IsNilpotent (RingHom.ker α)) :
    ∃ τ : S →ₐ[F] B, α.comp τ = AlgHom.id F S ∧
      τ.comp (IsScalarTower.toAlgHom F (MvPolynomial σ F) S) = β := by
  let : Algebra (MvPolynomial σ F) B := β.toRingHom.toAlgebra
  let : IsScalarTower F (MvPolynomial σ F) B :=
    IsScalarTower.of_algebraMap_eq' β.comp_algebraMap.symm
  let ap : B →ₐ[MvPolynomial σ F] S :=
    { α.toRingHom with
      commutes' := fun p => AlgHom.congr_fun hαβ p }
  let τ := Algebra.FormallySmooth.liftOfSurjective
    (AlgHom.id (MvPolynomial σ F) S) ap hα hnil
  have hτ := Algebra.FormallySmooth.comp_liftOfSurjective
    (AlgHom.id (MvPolynomial σ F) S) ap hα hnil
  refine ⟨τ.restrictScalars F, ?_, ?_⟩
  · ext s
    exact AlgHom.congr_fun hτ s
  · ext i
    exact τ.commutes (X i)

theorem exists_regular_taylor [Algebra.FormallySmooth (MvPolynomial σ F) S]
    (n : ℕ) (hn : 0 < n) :
    ∃ τ : S →ₐ[F] JetAlgebra σ S n,
      (∀ s, jetAugment n hn (τ s) = s) ∧
      (∀ i, τ (algebraMap (MvPolynomial σ F) S (X i)) =
        algebraMap S (JetAlgebra σ S n) (algebraMap (MvPolynomial σ F) S (X i)) +
          Ideal.Quotient.mk _ (X i)) := by
  let T := JetAlgebra σ S n
  let x : σ → S := fun i => algebraMap (MvPolynomial σ F) S (X i)
  let β : MvPolynomial σ F →ₐ[F] T :=
    aeval (fun i => algebraMap S T (x i) + Ideal.Quotient.mk _ (X i))
  let α := (jetAugment (σ := σ) (R := S) n hn).restrictScalars F
  have hαβ : α.comp β = IsScalarTower.toAlgHom F (MvPolynomial σ F) S := by
    ext i
    change jetAugment n hn (β (X i)) = x i
    simp only [β, aeval_X, map_add, jetAugment_mk, constantCoeff_X, add_zero]
    exact (jetAugment (σ := σ) (R := S) n hn).commutes (x i)
  obtain ⟨τ, hτ, hcoord⟩ := exists_lift_with_coordinates β α hαβ
    (jetAugment_surjective n hn) (jetAugment_ker_nilpotent n hn)
  refine ⟨τ, fun s => AlgHom.congr_fun hτ s, ?_⟩
  intro i
  have hi := AlgHom.congr_fun hcoord (X i)
  exact hi.trans (aeval_X _ _)

end

noncomputable section
open MvPolynomial

variable {σ F R S : Type*} [CommRing F] [CommRing R] [CommRing S]
  [Algebra F R] [Algebra F S]

lemma jetAugment_map (φ : R →ₐ[F] S) (n : ℕ) (hn : 0 < n)
    (z : JetAlgebra σ R n) :
    jetAugment n hn (mapJetAlgebra φ n z) = φ (jetAugment n hn z) := by
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective z
  simp [MvPolynomial.constantCoeff_map]

lemma jetAugment_ker_pow (n : ℕ) (hn : 0 < n) :
    RingHom.ker (jetAugment (σ := σ) (R := S) n hn) ^ n = 0 := by
  rw [jetAugment_ker, ← Ideal.map_pow]
  exact Ideal.map_quotient_self _

end
end MaximalSeshadri.AlgebraicJets

end
end
end

end OAI
end

section
namespace OAI

section
noncomputable section
section
namespace MaximalSeshadri.AlgebraicJets
noncomputable section

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

def quotientBaseMap (I : Ideal R) :
    R ⧸ I →ₐ[R] S ⧸ I.map (algebraMap R S) :=
  Ideal.quotientMapₐ _ (Algebra.ofId R S) Ideal.le_comap_map

@[simp] lemma quotientBaseMap_mk (I : Ideal R) (x : R) :
    quotientBaseMap (S := S) I (Ideal.Quotient.mk I x) =
      Ideal.Quotient.mk (I.map (algebraMap R S)) (algebraMap R S x) := rfl

lemma quotient_factor_pow_ker_nilpotent (I : Ideal R) (n : ℕ) (hn : 0 < n) :
    IsNilpotent (RingHom.ker
      (Ideal.Quotient.factorₐ R (Ideal.pow_le_self hn.ne') : R ⧸ I ^ n →ₐ[R] R ⧸ I)) := by
  refine ⟨n, ?_⟩
  change RingHom.ker (Ideal.Quotient.factor (Ideal.pow_le_self hn.ne')) ^ n = 0
  rw [Ideal.Quotient.factor_ker, ← Ideal.map_pow]
  exact Ideal.map_quotient_self _

theorem quotientBaseMap_pow_bijective [Algebra.FormallyEtale R S]
    (I : Ideal R) (hI : Function.Bijective (quotientBaseMap (S := S) I))
    (n : ℕ) : Function.Bijective (quotientBaseMap (S := S) (I ^ n)) := by
  classical
  by_cases hn : n = 0
  · subst n
    have hR : I ^ 0 = (⊤ : Ideal R) := by simp
    have hS : (I ^ 0).map (algebraMap R S) = (⊤ : Ideal S) := by
      rw [hR, Ideal.map_top]
    let : Subsingleton (R ⧸ I ^ 0) := Ideal.Quotient.subsingleton_iff.mpr hR
    let : Subsingleton (S ⧸ (I ^ 0).map (algebraMap R S)) :=
      Ideal.Quotient.subsingleton_iff.mpr hS
    exact ⟨Function.injective_of_subsingleton _, Function.surjective_to_subsingleton _⟩
  have hn : 0 < n := Nat.pos_of_ne_zero hn
  let J := I.map (algebraMap R S)
  let mapn := quotientBaseMap (S := S) (I ^ n)
  let e : (R ⧸ I) ≃ₐ[R] (S ⧸ J) := AlgEquiv.ofBijective (quotientBaseMap I) hI
  let qR : R ⧸ I ^ n →ₐ[R] R ⧸ I := Ideal.Quotient.factorₐ R (Ideal.pow_le_self hn.ne')
  let qS : S ⧸ (I ^ n).map (algebraMap R S) →ₐ[R] S ⧸ J :=
    Ideal.Quotient.factorₐ R (Ideal.map_mono (Ideal.pow_le_self hn.ne'))
  have hqR : Function.Surjective qR := by
    intro x
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact ⟨Ideal.Quotient.mk (I ^ n) x, rfl⟩
  have hnR : IsNilpotent (RingHom.ker qR) := quotient_factor_pow_ker_nilpotent I n hn
  have hnS : IsNilpotent (RingHom.ker qS) := by
    refine ⟨n, ?_⟩
    change RingHom.ker (Ideal.Quotient.factor
      (Ideal.map_mono (f := algebraMap R S) (Ideal.pow_le_self (I := I) hn.ne'))) ^ n = 0
    rw [Ideal.Quotient.factor_ker, ← Ideal.map_pow]
    rw [← Ideal.map_pow]
    exact Ideal.map_quotient_self _
  let f : S →ₐ[R] R ⧸ I := e.symm.toAlgHom.comp (Ideal.Quotient.mkₐ R J)
  let g : S →ₐ[R] R ⧸ I ^ n := Algebra.FormallySmooth.liftOfSurjective f qR hqR hnR
  have hg : qR.comp g = f := Algebra.FormallySmooth.comp_liftOfSurjective _ _ _ _
  have hker : (I ^ n).map (algebraMap R S) ≤ RingHom.ker g := by
    rw [Ideal.map_le_iff_le_comap]
    intro x hx
    change g (algebraMap R S x) = 0
    rw [g.commutes]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hx
  let inv : S ⧸ (I ^ n).map (algebraMap R S) →ₐ[R] R ⧸ I ^ n :=
    Ideal.Quotient.liftₐ _ g hker
  have hleft : inv.comp mapn = AlgHom.id R _ := by
    apply Ideal.Quotient.algHom_ext
    ext
  have hmod : qS.comp (mapn.comp g) = qS.comp (Ideal.Quotient.mkₐ R _) := by
    ext x
    have hx := AlgHom.congr_fun hg x
    apply e.symm.injective
    change e.symm (qS (mapn (g x))) = e.symm (Ideal.Quotient.mk J x)
    have hcompat (y : R ⧸ I ^ n) : e.symm (qS (mapn y)) = qR y := by
      obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
      change e.symm (e (Ideal.Quotient.mk I y)) = Ideal.Quotient.mk I y
      exact e.symm_apply_apply _
    rw [hcompat]
    exact hx
  have hright' : mapn.comp g = Ideal.Quotient.mkₐ R _ :=
    Algebra.FormallyUnramified.lift_unique' qS hnS _ _ hmod
  have hright : mapn.comp inv = AlgHom.id R _ := by
    apply Ideal.Quotient.algHom_ext
    exact hright'
  exact ⟨fun x y h => by
    change mapn x = mapn y at h
    calc
      x = inv (mapn x) := (AlgHom.congr_fun hleft x).symm
      _ = inv (mapn y) := congrArg inv h
      _ = y := AlgHom.congr_fun hleft y,
    fun y => ⟨inv y, AlgHom.congr_fun hright y⟩⟩

end

noncomputable section
open IsLocalRing

variable {F R S : Type*} [Field F] [CommRing R] [CommRing S]
  [Algebra F R] [Algebra F S] [Algebra R S] [IsScalarTower F R S]
  [IsLocalRing R] [IsLocalRing S] [IsLocalHom (algebraMap R S)]

lemma quotientBaseMap_maximal_bijective
    (hmax : (maximalIdeal R).map (algebraMap R S) = maximalIdeal S)
    (ρ : S →ₐ[F] F) :
    Function.Bijective (quotientBaseMap (S := S) (maximalIdeal R)) := by
  have hρ : Function.Surjective ρ := fun c => ⟨algebraMap F S c, by simp⟩
  have hker : RingHom.ker ρ = maximalIdeal S :=
    eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective ρ hρ)
  constructor
  · intro x y h
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
    apply Ideal.Quotient.eq.mpr
    have hmem : algebraMap R S (x - y) ∈ maximalIdeal S := by
      rw [← hmax]
      have hh := Ideal.Quotient.eq.mp h
      change algebraMap R S x - algebraMap R S y ∈ _ at hh
      simpa only [map_sub] using hh
    have hc : x - y ∈ (maximalIdeal S).comap (algebraMap R S) := hmem
    rwa [maximalIdeal_comap] at hc
  · intro y
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
    refine ⟨Ideal.Quotient.mk _ (algebraMap F R (ρ y)), ?_⟩
    apply Ideal.Quotient.eq.mpr
    rw [hmax, ← hker]
    change ρ (algebraMap R S (algebraMap F R (ρ y)) - y) = 0
    rw [← IsScalarTower.algebraMap_apply F R S]
    simp

theorem local_etale_jet_equiv [Algebra.EssFiniteType R S]
    [Algebra.FormallyEtale R S] (ρ : S →ₐ[F] F) (n : ℕ) :
    Nonempty ((R ⧸ (maximalIdeal R) ^ n) ≃ₐ[R]
      (S ⧸ (maximalIdeal S) ^ n)) := by
  have hmax : (maximalIdeal R).map (algebraMap R S) = maximalIdeal S :=
    Algebra.FormallyUnramified.map_maximalIdeal
  have hbij := quotientBaseMap_pow_bijective (maximalIdeal R)
    (quotientBaseMap_maximal_bijective hmax ρ) n
  have heq : ((maximalIdeal R) ^ n).map (algebraMap R S) = (maximalIdeal S) ^ n := by
    rw [Ideal.map_pow, hmax]
  exact ⟨(AlgEquiv.ofBijective _ hbij).trans (Ideal.quotientEquivAlgOfEq R heq)⟩

end

noncomputable section
open IsLocalRing

variable {F R S : Type*} [Field F] [CommRing R] [CommRing S]
  [Algebra F R] [Algebra F S] [Algebra R S] [IsScalarTower F R S]

instance rationalKer_isMaximal (ρ : S →ₐ[F] F) : (RingHom.ker ρ).IsMaximal :=
  RingHom.ker_isMaximal_of_surjective ρ
    (fun c => ⟨algebraMap F S c, by simp⟩)

def rationalLocalMap (ρ : S →ₐ[F] F) :
    Localization.AtPrime (RingHom.ker ρ) →ₐ[F] F :=
  IsLocalization.liftAlgHom (f := ρ) fun u : (RingHom.ker ρ).primeCompl =>
    isUnit_iff_ne_zero.mpr (fun h => u.2 h)

theorem etale_rational_jet_equiv [Algebra.EssFiniteType R S]
    [Algebra.FormallyEtale R S] (ρ : S →ₐ[F] F) (n : ℕ) :
    Nonempty ((R ⧸ ((RingHom.ker ρ).under R) ^ n) ≃ₐ[F]
      (S ⧸ (RingHom.ker ρ) ^ n)) := by
  let q := RingHom.ker ρ
  let p := q.under R
  have hρ : Function.Surjective ρ := fun c => ⟨algebraMap F S c, by simp⟩
  let : q.IsMaximal := RingHom.ker_isMaximal_of_surjective ρ hρ
  have hp : p = RingHom.ker (ρ.comp (IsScalarTower.toAlgHom F R S)) := rfl
  let : p.IsMaximal := by
    rw [hp]
    exact RingHom.ker_isMaximal_of_surjective _
      (fun c => ⟨algebraMap F R c, by simp⟩)
  let Rp := Localization.AtPrime p
  let Sq := Localization.AtPrime q
  let : Algebra Rp Sq := Localization.AtPrime.algebraOfLiesOver p q
  let : Algebra.EssFiniteType Rp Sq := Algebra.EssFiniteType.of_comp R Rp Sq
  let : Algebra.FormallyEtale R Sq := Algebra.FormallyEtale.comp R S Sq
  let : Algebra.FormallyEtale Rp Sq := Algebra.FormallyEtale.of_restrictScalars (R := R)
  obtain ⟨e⟩ := local_etale_jet_equiv (R := Rp) (S := Sq) (rationalLocalMap ρ) n
  exact ⟨((IsLocalization.AtPrime.equivQuotMaximalIdealPow p Rp n).restrictScalars F).trans
    ((e.restrictScalars F).trans
      ((IsLocalization.AtPrime.equivQuotMaximalIdealPow q Sq n).restrictScalars F).symm)⟩

end

noncomputable section
open MvPolynomial
variable {σ F S : Type*} [Field F] [CommRing S] [Algebra F S]

def specializeTaylor (n : ℕ) (τ : S →ₐ[F] JetAlgebra σ S n) (ρ : S →ₐ[F] F) :
    S →ₐ[F] JetAlgebra σ F n :=
  (mapJetAlgebra ρ n).comp τ

lemma specializeTaylor_augment (n : ℕ) (hn : 0 < n)
    (τ : S →ₐ[F] JetAlgebra σ S n) (hτ : ∀ s, jetAugment n hn (τ s) = s)
    (ρ : S →ₐ[F] F) (s : S) :
    jetAugment n hn (specializeTaylor n τ ρ s) = ρ s := by
  rw [specializeTaylor, AlgHom.comp_apply, jetAugment_map, hτ]

lemma specializeTaylor_ker_le (n : ℕ) (hn : 0 < n)
    (τ : S →ₐ[F] JetAlgebra σ S n) (hτ : ∀ s, jetAugment n hn (τ s) = s)
    (ρ : S →ₐ[F] F) :
    (RingHom.ker ρ)^n ≤ RingHom.ker (specializeTaylor n τ ρ) := by
  rw [← Ideal.map_eq_bot_iff_le_ker, Ideal.map_pow]
  apply le_antisymm _ bot_le
  calc
    ((RingHom.ker ρ).map (specializeTaylor n τ ρ))^n ≤
        (RingHom.ker (jetAugment (σ := σ) (R := F) n hn))^n := by
      refine Ideal.pow_right_mono ?_ n
      rw [Ideal.map_le_iff_le_comap]
      intro s hs
      change jetAugment n hn (specializeTaylor n τ ρ s) = 0
      rw [specializeTaylor_augment n hn τ hτ]
      exact hs
    _ = ⊥ := jetAugment_ker_pow n hn

variable [Algebra (MvPolynomial σ F) S] [IsScalarTower F (MvPolynomial σ F) S]

lemma specializeTaylor_coordinate (n : ℕ) (τ : S →ₐ[F] JetAlgebra σ S n)
    (hcoord : ∀ i, τ (algebraMap (MvPolynomial σ F) S (X i)) =
      algebraMap S (JetAlgebra σ S n) (algebraMap (MvPolynomial σ F) S (X i)) +
        Ideal.Quotient.mk _ (X i)) (ρ : S →ₐ[F] F) :
    (specializeTaylor n τ ρ).comp (IsScalarTower.toAlgHom F (MvPolynomial σ F) S) =
      (Ideal.Quotient.mkₐ F _).comp (polynomialTranslate
        (fun i => ρ (algebraMap (MvPolynomial σ F) S (X i)))).toAlgHom := by
  ext i
  change mapJetAlgebra ρ n (τ (algebraMap (MvPolynomial σ F) S (X i))) = _
  rw [hcoord, map_add]
  change Ideal.Quotient.mk _ (MvPolynomial.map ρ.toRingHom
    (C (algebraMap (MvPolynomial σ F) S (X i)))) +
    Ideal.Quotient.mk _ (MvPolynomial.map ρ.toRingHom (X i)) = _
  simp [polynomialTranslate, add_comm]

lemma specializeTaylor_surjective (n : ℕ) (τ : S →ₐ[F] JetAlgebra σ S n)
    (hcoord : ∀ i, τ (algebraMap (MvPolynomial σ F) S (X i)) =
      algebraMap S (JetAlgebra σ S n) (algebraMap (MvPolynomial σ F) S (X i)) +
        Ideal.Quotient.mk _ (X i)) (ρ : S →ₐ[F] F) :
    Function.Surjective (specializeTaylor n τ ρ) := by
  have h := specializeTaylor_coordinate n τ hcoord ρ
  have hs : Function.Surjective ((specializeTaylor n τ ρ).comp
      (IsScalarTower.toAlgHom F (MvPolynomial σ F) S)) := by
    rw [h]
    exact Ideal.Quotient.mk_surjective.comp (polynomialTranslate _).surjective
  exact Function.Surjective.of_comp hs

theorem regularTaylor_detects_ideal_power [Finite σ] [Algebra.FormallyEtale (MvPolynomial σ F) S]
    [Algebra.EssFiniteType (MvPolynomial σ F) S]
    (n : ℕ) (hn : 0 < n) (τ : S →ₐ[F] JetAlgebra σ S n)
    (hτ : ∀ s, jetAugment n hn (τ s) = s)
    (hcoord : ∀ i, τ (algebraMap (MvPolynomial σ F) S (X i)) =
      algebraMap S (JetAlgebra σ S n) (algebraMap (MvPolynomial σ F) S (X i)) +
        Ideal.Quotient.mk _ (X i)) (ρ : S →ₐ[F] F) :
    RingHom.ker (specializeTaylor n τ ρ) = (RingHom.ker ρ)^n := by
  classical
  let I := (RingHom.ker ρ)^n
  let ψ : (S ⧸ I) →ₐ[F] JetAlgebra σ F n :=
    Ideal.Quotient.liftₐ I (specializeTaylor n τ ρ)
      (specializeTaylor_ker_le n hn τ hτ ρ)
  have hsurj : Function.Surjective ψ := by
    intro y
    obtain ⟨s, hs⟩ := specializeTaylor_surjective n τ hcoord ρ y
    exact ⟨Ideal.Quotient.mk I s, hs⟩
  let x : σ → F := fun i => ρ (algebraMap (MvPolynomial σ F) S (X i))
  have hres : (RingHom.ker ρ).under (MvPolynomial σ F) = RingHom.ker (eval x) := by
    have heq : ρ.toRingHom.comp (algebraMap (MvPolynomial σ F) S) = eval x := by
      apply ringHom_ext
      · intro c
        simp only [RingHom.comp_apply, eval_C]
        change ρ (algebraMap (MvPolynomial σ F) S (algebraMap F (MvPolynomial σ F) c)) = c
        rw [← IsScalarTower.algebraMap_apply F (MvPolynomial σ F) S]
        exact ρ.commutes c
      · intro i
        exact (eval_X (f := x) i).symm
    change RingHom.ker (ρ.toRingHom.comp (algebraMap (MvPolynomial σ F) S)) = _
    rw [heq]
  obtain ⟨e⟩ := etale_rational_jet_equiv (R := MvPolynomial σ F) ρ n
  let e' : (S ⧸ I) ≃ₗ[F] (JetIndex σ n → F) :=
    e.symm.toLinearEquiv.trans
      (((Ideal.quotientEquivAlgOfEq F (congrArg (fun J => J ^ n) hres)).toLinearEquiv).trans
        (polynomialJetEquivAt x n))
  let e'' : JetAlgebra σ F n ≃ₗ[F] (JetIndex σ n → F) := polynomialJetEquiv n
  let : FiniteDimensional F (JetIndex σ n → F) := Module.Finite.pi
  let : FiniteDimensional F (S ⧸ I) := Module.Finite.equiv e'.symm
  let : FiniteDimensional F (JetAlgebra σ F n) := Module.Finite.equiv e''.symm
  have hinj : Function.Injective ψ :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (e'.finrank_eq.trans e''.finrank_eq.symm) (f := ψ.toLinearMap)).mpr hsurj
  apply le_antisymm _ (specializeTaylor_ker_le n hn τ hτ ρ)
  intro s hs
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  apply hinj
  change specializeTaylor n τ ρ s = ψ 0
  rw [map_zero]
  exact hs

end

noncomputable section
open MvPolynomial
variable {σ F S : Type*} [Finite σ] [Field F] [CommRing S] [Algebra F S]

def regularTaylorCoeffs (n : ℕ) (τ : S →ₐ[F] JetAlgebra σ S n) :
    S →ₗ[F] (JetIndex σ n → S) :=
  ((polynomialJetEquiv (σ := σ) (R := S) n).toLinearMap.restrictScalars F).comp τ.toLinearMap

lemma specializedTaylor_coeff (n : ℕ) (τ : S →ₐ[F] JetAlgebra σ S n)
    (ρ : S →ₐ[F] F) (s : S) (d : JetIndex σ n) :
    polynomialJetEquiv n (specializeTaylor n τ ρ s) d =
      ρ (regularTaylorCoeffs n τ s d) := by
  obtain ⟨p, hp⟩ := Ideal.Quotient.mk_surjective (τ s)
  change polynomialJetEquiv n (mapJetAlgebra ρ n (τ s)) d =
    ρ (polynomialJetEquiv n (τ s) d)
  rw [← hp, mapJetAlgebra_mk, polynomialJetEquiv_mk, polynomialJetEquiv_mk]
  exact coeff_map _ _ _

variable [Algebra (MvPolynomial σ F) S] [IsScalarTower F (MvPolynomial σ F) S]

theorem regularTaylor_vanishing_iff [Algebra.FormallyEtale (MvPolynomial σ F) S]
    [Algebra.EssFiniteType (MvPolynomial σ F) S]
    (n : ℕ) (hn : 0 < n) (τ : S →ₐ[F] JetAlgebra σ S n)
    (hτ : ∀ s, jetAugment n hn (τ s) = s)
    (hcoord : ∀ i, τ (algebraMap (MvPolynomial σ F) S (X i)) =
      algebraMap S (JetAlgebra σ S n) (algebraMap (MvPolynomial σ F) S (X i)) +
        Ideal.Quotient.mk _ (X i)) (ρ : S →ₐ[F] F) (s : S) :
    s ∈ (RingHom.ker ρ)^n ↔ ∀ d, ρ (regularTaylorCoeffs n τ s d) = 0 := by
  rw [← regularTaylor_detects_ideal_power n hn τ hτ hcoord ρ]
  change specializeTaylor n τ ρ s = 0 ↔ _
  rw [← (polynomialJetEquiv (σ := σ) (R := F) n).map_eq_zero_iff]
  rw [funext_iff]
  exact forall_congr' fun d => by rw [specializedTaylor_coeff]; rfl

end

noncomputable section
open MvPolynomial
variable {σ F S : Type*} [Finite σ] [Field F] [CommRing S] [Algebra F S]
  [Algebra (MvPolynomial σ F) S] [IsScalarTower F (MvPolynomial σ F) S]
  [Algebra.FormallyEtale (MvPolynomial σ F) S]
  [Algebra.EssFiniteType (MvPolynomial σ F) S]

theorem exists_regular_jet_coeffs (n : ℕ) (hn : 0 < n) :
    ∃ D : S →ₗ[F] (JetIndex σ n → S),
      ∀ (ρ : S →ₐ[F] F) s, s ∈ (RingHom.ker ρ)^n ↔ ∀ d, ρ (D s d) = 0 := by
  obtain ⟨τ, hτ, hcoord⟩ := exists_regular_taylor (σ := σ) (F := F) (S := S) n hn
  exact ⟨regularTaylorCoeffs n τ, regularTaylor_vanishing_iff n hn τ hτ hcoord⟩

end
end MaximalSeshadri.AlgebraicJets
end

end
end

end OAI
end

section
namespace OAI

section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian TopologicalSpace
open MaximalSeshadri.Frames MaximalSeshadri.AlgebraicJets MaximalSeshadri.ProjectiveBertini

lemma finite_affine_jet_test {A : Type} [CommRing A] [Algebra ℂ A]
    (t : Fin 2 → A) (het : (MvPolynomial.aeval (R := ℂ) t).toRingHom.Etale)
    (ρ : A →ₐ[ℂ] ℂ) (n : ℕ) :
    ∃ J : A →ₗ[ℂ] (JetIndex (Fin 2) n → ℂ),
      ∀ a, J a = 0 ↔ a ∈ (RingHom.ker ρ)^n := by
  classical
  by_cases hn : n = 0
  · subst n
    refine ⟨0,fun a => ?_⟩
    simp
  let φ := MvPolynomial.aeval (R := ℂ) t
  let := φ.toAlgebra
  let : IsScalarTower ℂ (MvPolynomial (Fin 2) ℂ) A :=
    IsScalarTower.of_algebraMap_eq fun c => (φ.commutes c).symm
  let : Algebra.Etale (MvPolynomial (Fin 2) ℂ) A := RingHom.etale_algebraMap.mp het
  obtain ⟨D,hD⟩ := exists_regular_jet_coeffs (σ := Fin 2) (F := ℂ) (S := A) n (Nat.pos_of_ne_zero hn)
  let J : A →ₗ[ℂ] (JetIndex (Fin 2) n → ℂ) :=
    LinearMap.pi fun d => ρ.toLinearMap.comp ((LinearMap.proj d).comp D)
  refine ⟨J,fun a => ?_⟩
  rw [hD ρ a,funext_iff]
  rfl

end
end MaximalSeshadri.Geometry

end

end OAI
end

theorem solution : type_of% @OAI.MaximalSeshadri.Geometry.finite_affine_jet_test := @OAI.MaximalSeshadri.Geometry.finite_affine_jet_test
