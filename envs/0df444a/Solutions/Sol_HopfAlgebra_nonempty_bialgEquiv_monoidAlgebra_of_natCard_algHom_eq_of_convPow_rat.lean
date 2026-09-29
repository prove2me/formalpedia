-- Prove2me | solution 1 for HopfAlgebra.nonempty_bialgEquiv_monoidAlgebra_of_natCard_algHom_eq_of_convPow_rat
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/fcdae74a-1382-5a4e-88e4-fd04e1eea26b

import Mathlib
import Theorems.Thm_HopfAlgebra_isReduced_of_finiteType_of_charZero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HopfAlgebra_nonempty_bialgEquiv_monoidAlgebra_of_natCard_algHom_eq_of_convPow_rat
set_option maxHeartbeats 1600000
set_option autoImplicit false

namespace HopfAlgebra
p2m_export "HopfAlgebra" "ofAlgHom mul_antipode_rTensor_comul mul_antipode_lTensor_comul isReduced_of_finiteType_of_charZero"
namespace GenMu
p2m_open "HopfAlgebra"

attribute [local instance] Ideal.Quotient.field in
theorem formallyEtale_of_hopf_charZero
    (k : Type*) [Field k] [CharZero k]
    (B : Type*) [CommRing B] [HopfAlgebra k B] [Module.Finite k B] :
    Algebra.FormallyEtale k B := by
  haveI hFT : Algebra.FiniteType k B := inferInstance
  haveI hRed : IsReduced B := HopfAlgebra.isReduced_of_finiteType_of_charZero k B
  haveI hArt : IsArtinianRing B := .of_finite k B
  haveI hFin : Finite (MaximalSpectrum B) := inferInstance
  have hI (I : MaximalSpectrum B) : Algebra.FormallyEtale k (B ⧸ I.asIdeal) := by
    haveI : I.asIdeal.IsMaximal := I.isMaximal
    haveI : Module.Finite k (B ⧸ I.asIdeal) := Module.Finite.quotient k _
    haveI : Algebra.IsAlgebraic k (B ⧸ I.asIdeal) := Algebra.IsIntegral.isAlgebraic
    haveI : Algebra.IsSeparable k (B ⧸ I.asIdeal) := inferInstance
    exact Algebra.FormallyEtale.of_isSeparable k (B ⧸ I.asIdeal)
  exact Algebra.FormallyEtale.of_equiv ((IsArtinianRing.equivPi B).restrictScalars k).symm

theorem etale_of_hopf_charZero
    (k : Type*) [Field k] [CharZero k]
    (B : Type*) [CommRing B] [HopfAlgebra k B] [Module.Finite k B] :
    Algebra.Etale k B where
  formallyEtale := formallyEtale_of_hopf_charZero k B
  finitePresentation := by
    haveI : Algebra.FiniteType k B := inferInstance
    exact Algebra.FinitePresentation.of_finiteType.mp inferInstance

end HopfAlgebra.GenMu

universe u v w

namespace HopfAlgebra
p2m_export "HopfAlgebra" "ofAlgHom mul_antipode_rTensor_comul mul_antipode_lTensor_comul isReduced_of_finiteType_of_charZero"
namespace GenMuDescent
p2m_open "HopfAlgebra"

section Factorisation

variable {K : Type*} [Field K] {Ω : Type*} [CommRing Ω] [Algebra K Ω]
variable {J : Type*} {A : J → Type*} [∀ j, CommRing (A j)] [∀ j, Algebra K (A j)]

theorem single_mul_single_one [DecidableEq J] {j j' : J} (h : j ≠ j') (a : A j) :
    (Pi.single j a : Π j, A j) * Pi.single j' 1 = 0 := by
  funext k
  simp only [Pi.mul_apply, Pi.zero_apply]
  rcases eq_or_ne k j' with rfl | hk
  · rw [Pi.single_eq_of_ne (Ne.symm h), zero_mul]
  · rw [Pi.single_eq_of_ne hk, mul_zero]

def factorComponent [DecidableEq J] (φ : (Π j, A j) →ₐ[K] Ω) (j : J)
    (h1 : φ (Pi.single j 1) = 1) : A j →ₐ[K] Ω where
  toFun x := φ (Pi.single j x)
  map_one' := h1
  map_mul' x y := by rw [Pi.single_mul, map_mul]
  map_zero' := by rw [Pi.single_zero, map_zero]
  map_add' x y := by rw [Pi.single_add, map_add]
  commutes' r := by
    rw [Algebra.algebraMap_eq_smul_one, Pi.single_smul, map_smul, h1]
    exact (Algebra.algebraMap_eq_smul_one r).symm

@[scoped simp] theorem factorComponent_apply [DecidableEq J] (φ : (Π j, A j) →ₐ[K] Ω) (j : J)
    (h1 : φ (Pi.single j 1) = 1) (x : A j) :
    factorComponent φ j h1 x = φ (Pi.single j x) := rfl

theorem exists_factor_algHom [Finite J] [IsDomain Ω] (φ : (Π j, A j) →ₐ[K] Ω) :
    ∃ (j : J) (φ₀ : A j →ₐ[K] Ω), φ = φ₀.comp (Pi.evalAlgHom K A j) := by
  cases nonempty_fintype J
  classical

  have hidem : ∀ j, φ (Pi.single j 1) = 0 ∨ φ (Pi.single j 1) = 1 := by
    intro j
    have h2 : φ (Pi.single j 1) * φ (Pi.single j 1) = φ (Pi.single j 1) := by
      rw [← map_mul, ← Pi.single_mul, one_mul]
    have h3 : φ (Pi.single j 1) * (φ (Pi.single j 1) - 1) = 0 := by
      rw [mul_sub, h2, mul_one, sub_self]
    rcases mul_eq_zero.mp h3 with h | h
    · exact Or.inl h
    · exact Or.inr (sub_eq_zero.mp h)

  have hsum : (∑ j, φ (Pi.single j 1)) = 1 := by
    rw [← map_sum]
    have h1 : (∑ j, (Pi.single j 1 : Π j, A j)) = 1 := by
      simpa using Finset.univ_sum_single (1 : Π j, A j)
    rw [h1, map_one]
  have hex : ∃ j, φ (Pi.single j 1) = 1 := by
    by_contra hno
    have hall : ∀ j ∈ Finset.univ, φ (Pi.single (M := A) j 1) = 0 :=
      fun j _ => (hidem j).resolve_right fun h1 => hno ⟨j, h1⟩
    rw [Finset.sum_eq_zero hall] at hsum
    exact zero_ne_one hsum
  obtain ⟨j₀, h1⟩ := hex
  refine ⟨j₀, factorComponent φ j₀ h1, AlgHom.ext fun g => ?_⟩
  have hg : φ g = ∑ j, φ (Pi.single j (g j)) := by
    rw [← map_sum, Finset.univ_sum_single]
  have hzero : ∀ j ∈ Finset.univ, j ≠ j₀ → φ (Pi.single j (g j)) = 0 := by
    intro j _ hj
    have horth : φ (Pi.single j (g j)) * φ (Pi.single j₀ 1) = 0 := by
      rw [← map_mul, single_mul_single_one hj, map_zero]
    rwa [h1, mul_one] at horth
  calc φ g = ∑ j, φ (Pi.single j (g j)) := hg
  _ = φ (Pi.single j₀ (g j₀)) :=
      Finset.sum_eq_single j₀ hzero (fun h => absurd (Finset.mem_univ j₀) h)
  _ = (factorComponent φ j₀ h1).comp (Pi.evalAlgHom K A j₀) g := rfl

theorem factor_index_unique [Nontrivial Ω] [∀ j, Nontrivial (A j)] {j j' : J}
    {φ₀ : A j →ₐ[K] Ω} {φ₁ : A j' →ₐ[K] Ω}
    (h : φ₀.comp (Pi.evalAlgHom K A j) = φ₁.comp (Pi.evalAlgHom K A j')) : j = j' := by
  classical
  by_contra hne
  have happ := DFunLike.congr_fun h (Pi.single j 1)
  simp only [AlgHom.comp_apply, Pi.evalAlgHom_apply] at happ
  rw [Pi.single_eq_same, Pi.single_eq_of_ne (Ne.symm hne), map_one, map_zero] at happ
  exact one_ne_zero happ

end Factorisation

section Faithfulness

variable {K : Type*} [Field K] {Ω : Type*} [Field Ω] [Algebra K Ω] [IsAlgClosed Ω]

theorem points_separate_of_etale {B : Type u} [CommRing B] [Algebra K B] [Algebra.Etale K B]
    {x y : B} (h : ∀ χ : B →ₐ[K] Ω, χ x = χ y) : x = y := by
  obtain ⟨I, hfin, L, hfield, halg, e, hL⟩ :=
    (Algebra.Etale.iff_exists_algEquiv_prod K B).mp inferInstance
  haveI := hfin
  letI : ∀ i, Field (L i) := hfield
  letI : ∀ i, Algebra K (L i) := halg
  apply e.injective
  funext i
  haveI : Module.Finite K (L i) := (hL i).1
  have hχ := h (((IsAlgClosed.lift (M := Ω)).comp (Pi.evalAlgHom K L i)).comp e.toAlgHom)
  exact (IsAlgClosed.lift (R := K) (S := L i) (M := Ω)).toRingHom.injective hχ

theorem algHom_ext_of_points {B : Type*} [Semiring B] [Algebra K B]
    {C : Type u} [CommRing C] [Algebra K C] [Algebra.Etale K C]
    {ψ₁ ψ₂ : B →ₐ[K] C} (h : ∀ χ : C →ₐ[K] Ω, χ.comp ψ₁ = χ.comp ψ₂) : ψ₁ = ψ₂ :=
  AlgHom.ext fun b =>
    points_separate_of_etale (fun χ => DFunLike.congr_fun (h χ) b)

end Faithfulness

section RangeRealization

variable {K : Type*} [Field K] {Ω : Type*} [Field Ω] [Algebra K Ω]
variable {L : Type*} [CommRing L] [Algebra K L]
variable {M : Type*} [Field M] [Algebra K M]

noncomputable def homOfRangeLe (χ : M →ₐ[K] Ω) (β : L →ₐ[K] Ω)
    (h : ∀ x, ∃ y, χ y = β x) : L →ₐ[K] M where
  toFun x := (h x).choose
  map_one' := χ.toRingHom.injective
    (show χ (h 1).choose = χ 1 from
      ((h 1).choose_spec.trans (map_one β)).trans (map_one χ).symm)
  map_mul' x y := χ.toRingHom.injective
    (show χ (h (x * y)).choose = χ ((h x).choose * (h y).choose) from
      (((h (x * y)).choose_spec.trans (map_mul β x y)).trans
        (congrArg₂ (· * ·) (h x).choose_spec.symm (h y).choose_spec.symm)).trans
        (map_mul χ _ _).symm)
  map_zero' := χ.toRingHom.injective
    (show χ (h 0).choose = χ 0 from
      ((h 0).choose_spec.trans (map_zero β)).trans (map_zero χ).symm)
  map_add' x y := χ.toRingHom.injective
    (show χ (h (x + y)).choose = χ ((h x).choose + (h y).choose) from
      (((h (x + y)).choose_spec.trans (map_add β x y)).trans
        (congrArg₂ (· + ·) (h x).choose_spec.symm (h y).choose_spec.symm)).trans
        (map_add χ _ _).symm)
  commutes' r := χ.toRingHom.injective
    (show χ (h (algebraMap K L r)).choose = χ (algebraMap K M r) from
      ((h (algebraMap K L r)).choose_spec.trans (β.commutes r)).trans (χ.commutes r).symm)

theorem comp_homOfRangeLe (χ : M →ₐ[K] Ω) (β : L →ₐ[K] Ω)
    (h : ∀ x, ∃ y, χ y = β x) :
    χ.comp (homOfRangeLe χ β h) = β :=
  AlgHom.ext fun x => (h x).choose_spec

end RangeRealization

section Conjugacy

variable {K : Type*} [Field K] {Ω : Type*} [Field Ω] [Algebra K Ω]
  [IsAlgClosed Ω] [Algebra.IsAlgebraic K Ω]

theorem exists_algEquiv_comp_eq {M : Type*} [Field M] [Algebra K M]
    (σ τ : M →ₐ[K] Ω) : ∃ γ : Ω ≃ₐ[K] Ω, γ.toAlgHom.comp σ = τ := by
  letI : Algebra M Ω := σ.toRingHom.toAlgebra
  haveI : IsScalarTower K M Ω :=
    IsScalarTower.of_algebraMap_eq fun x => (σ.commutes x).symm
  haveI : Algebra.IsAlgebraic M Ω := Algebra.IsAlgebraic.tower_top (K := K) M
  obtain ⟨φ, hφ⟩ := IsAlgClosed.surjective_restrictDomain_of_isAlgebraic
    (K := K) (L := M) (M := Ω) (E := Ω) τ
  haveI : IsAlgClosure K Ω := ⟨inferInstance, inferInstance⟩
  refine ⟨AlgEquiv.ofBijective φ (AlgHom.normal_bijective K Ω Ω φ),
    AlgHom.ext fun m => ?_⟩
  exact DFunLike.congr_fun hφ m

end Conjugacy

section FixedField

variable {K : Type*} [Field K] {Ω : Type*} [Field Ω] [Algebra K Ω] [IsGalois K Ω]

theorem exists_preimage_of_equivariant_fix {M L : Type*} [Field M] [Algebra K M]
    [CommRing L] [Algebra K L] (χ : M →ₐ[K] Ω) (β : L →ₐ[K] Ω)
    (hfix : ∀ γ : Ω ≃ₐ[K] Ω, γ.toAlgHom.comp χ = χ → γ.toAlgHom.comp β = β)
    (x : L) : ∃ y, χ y = β x := by
  have hmem : β x ∈ IntermediateField.fixedField χ.fieldRange.fixingSubgroup := by
    rw [IntermediateField.mem_fixedField_iff]
    intro γ hγ
    have hχ : γ.toAlgHom.comp χ = χ := AlgHom.ext fun m =>
      ((IntermediateField.mem_fixingSubgroup_iff _ γ).mp hγ) (χ m)
        (AlgHom.mem_fieldRange.mpr ⟨m, rfl⟩)
    exact DFunLike.congr_fun (hfix γ hχ) x
  rw [InfiniteGalois.fixedField_fixingSubgroup χ.fieldRange] at hmem
  exact hmem

end FixedField

section ProductDescent

variable {K : Type*} [Field K] {Ω : Type*} [Field Ω] [Algebra K Ω]
  [IsAlgClosed Ω] [Algebra.IsAlgebraic K Ω] [IsGalois K Ω]

theorem exists_algHom_realizing_equivariant_pointsMap_pi_fields
    {I : Type v} {J : Type w} [Finite I] [Finite J]
    {L : I → Type*} {M : J → Type*}
    [∀ i, Field (L i)] [∀ i, Algebra K (L i)]
    [∀ j, Field (M j)] [∀ j, Algebra K (M j)]
    [∀ j, Algebra.IsAlgebraic K (M j)]
    (Φ : ((Π j, M j) →ₐ[K] Ω) → ((Π i, L i) →ₐ[K] Ω))
    (hΦ : ∀ (γ : Ω ≃ₐ[K] Ω) (χ : (Π j, M j) →ₐ[K] Ω),
      Φ (γ.toAlgHom.comp χ) = γ.toAlgHom.comp (Φ χ)) :
    ∃ ψ : (Π i, L i) →ₐ[K] (Π j, M j), ∀ χ, χ.comp ψ = Φ χ := by
  classical

  let base : ∀ j, M j →ₐ[K] Ω := fun _ => IsAlgClosed.lift

  have hfac : ∀ j, ∃ (i : I) (β : L i →ₐ[K] Ω),
      Φ ((base j).comp (Pi.evalAlgHom K M j)) = β.comp (Pi.evalAlgHom K L i) :=
    fun _ => exists_factor_algHom _
  choose ix β hβ using hfac

  have hrange : ∀ j (x : L (ix j)), ∃ y, base j y = β j x := by
    intro j
    refine exists_preimage_of_equivariant_fix (base j) (β j) ?_
    intro γ hγ
    have hP : γ.toAlgHom.comp ((base j).comp (Pi.evalAlgHom K M j))
        = (base j).comp (Pi.evalAlgHom K M j) := by
      rw [← AlgHom.comp_assoc, hγ]
    have h2 : (γ.toAlgHom.comp (β j)).comp (Pi.evalAlgHom K L (ix j))
        = (β j).comp (Pi.evalAlgHom K L (ix j)) := by
      rw [AlgHom.comp_assoc, ← hβ j, ← hΦ γ, hP, hβ j]
    refine AlgHom.ext fun x => ?_
    obtain ⟨g, hg⟩ := Function.surjective_eval (β := fun i => L i) (ix j) x
    have hg' : g (ix j) = x := hg
    have happ := DFunLike.congr_fun h2 g
    simp only [AlgHom.comp_apply, Pi.evalAlgHom_apply] at happ
    rw [hg'] at happ
    exact happ

  let ψfac : ∀ j, L (ix j) →ₐ[K] M j := fun j => homOfRangeLe (base j) (β j) (hrange j)
  have hψfac : ∀ j, (base j).comp (ψfac j) = β j := fun j => comp_homOfRangeLe _ _ _
  refine ⟨Pi.algHom K M (fun j => (ψfac j).comp (Pi.evalAlgHom K L (ix j))), fun χ => ?_⟩

  obtain ⟨j, χ₀, hχ⟩ := exists_factor_algHom χ
  obtain ⟨γ, hγ⟩ := exists_algEquiv_comp_eq (base j) χ₀
  have heval : (Pi.evalAlgHom K M j).comp
      (Pi.algHom K M fun j' => (ψfac j').comp (Pi.evalAlgHom K L (ix j')))
      = (ψfac j).comp (Pi.evalAlgHom K L (ix j)) :=
    AlgHom.ext fun _ => rfl
  have hcomp : χ.comp
      (Pi.algHom K M fun j' => (ψfac j').comp (Pi.evalAlgHom K L (ix j')))
      = γ.toAlgHom.comp ((β j).comp (Pi.evalAlgHom K L (ix j))) := by
    rw [hχ, AlgHom.comp_assoc, heval, ← hγ,
      AlgHom.comp_assoc γ.toAlgHom (base j) ((ψfac j).comp (Pi.evalAlgHom K L (ix j))),
      ← AlgHom.comp_assoc (base j) (ψfac j) (Pi.evalAlgHom K L (ix j)), hψfac j]
  have hRHS : Φ χ = γ.toAlgHom.comp ((β j).comp (Pi.evalAlgHom K L (ix j))) := by
    rw [hχ, ← hγ, AlgHom.comp_assoc, hΦ, hβ]
  rw [hcomp, hRHS]

end ProductDescent

section EtaleDescent

variable {K : Type*} [Field K] {Ω : Type*} [Field Ω] [Algebra K Ω]
  [IsAlgClosed Ω] [Algebra.IsAlgebraic K Ω] [IsGalois K Ω]

theorem exists_algHom_realizing_equivariant_pointsMap_of_etale
    {B : Type u} {C : Type v} [CommRing B] [CommRing C] [Algebra K B] [Algebra K C]
    [Algebra.Etale K B] [Algebra.Etale K C]
    (Φ : (C →ₐ[K] Ω) → (B →ₐ[K] Ω))
    (hΦ : ∀ (γ : Ω ≃ₐ[K] Ω) (χ : C →ₐ[K] Ω),
      Φ (γ.toAlgHom.comp χ) = γ.toAlgHom.comp (Φ χ)) :
    ∃ ψ : B →ₐ[K] C, ∀ χ : C →ₐ[K] Ω, χ.comp ψ = Φ χ := by
  obtain ⟨I, hIfin, L, hLfield, hLalg, eB, hL⟩ :=
    (Algebra.Etale.iff_exists_algEquiv_prod K B).mp inferInstance
  obtain ⟨J, hJfin, M, hMfield, hMalg, eC, hM⟩ :=
    (Algebra.Etale.iff_exists_algEquiv_prod K C).mp inferInstance
  haveI := hIfin
  haveI := hJfin
  letI : ∀ i, Field (L i) := hLfield
  letI : ∀ i, Algebra K (L i) := hLalg
  letI : ∀ j, Field (M j) := hMfield
  letI : ∀ j, Algebra K (M j) := hMalg
  haveI : ∀ j, Module.Finite K (M j) := fun j => (hM j).1

  have hΦ' : ∀ (γ : Ω ≃ₐ[K] Ω) (χ' : (Π j, M j) →ₐ[K] Ω),
      (Φ ((γ.toAlgHom.comp χ').comp eC.toAlgHom)).comp eB.symm.toAlgHom
        = γ.toAlgHom.comp ((Φ (χ'.comp eC.toAlgHom)).comp eB.symm.toAlgHom) := by
    intro γ χ'
    rw [AlgHom.comp_assoc, hΦ γ, AlgHom.comp_assoc]
  obtain ⟨ψ', hψ'⟩ := exists_algHom_realizing_equivariant_pointsMap_pi_fields
    (L := L) (M := M)
    (fun χ' => (Φ (χ'.comp eC.toAlgHom)).comp eB.symm.toAlgHom)
    (fun γ χ' => hΦ' γ χ')
  refine ⟨(eC.symm.toAlgHom.comp ψ').comp eB.toAlgHom, fun χ => ?_⟩
  have h1 : (χ.comp eC.symm.toAlgHom).comp ψ'
      = (Φ ((χ.comp eC.symm.toAlgHom).comp eC.toAlgHom)).comp eB.symm.toAlgHom :=
    hψ' (χ.comp eC.symm.toAlgHom)
  have hcancelC : (χ.comp eC.symm.toAlgHom).comp eC.toAlgHom = χ :=
    AlgHom.ext fun c => congrArg χ (eC.symm_apply_apply c)
  have hcancelB : eB.symm.toAlgHom.comp eB.toAlgHom = AlgHom.id K B :=
    AlgHom.ext fun b => eB.symm_apply_apply b
  calc χ.comp ((eC.symm.toAlgHom.comp ψ').comp eB.toAlgHom)
      = ((χ.comp eC.symm.toAlgHom).comp ψ').comp eB.toAlgHom := by
        rw [← AlgHom.comp_assoc, ← AlgHom.comp_assoc]
  _ = ((Φ ((χ.comp eC.symm.toAlgHom).comp eC.toAlgHom)).comp
        eB.symm.toAlgHom).comp eB.toAlgHom := by rw [h1]
  _ = Φ χ := by
        rw [hcancelC, AlgHom.comp_assoc, hcancelB, AlgHom.comp_id]

theorem existsUnique_algHom_realizing_equivariant_pointsMap_of_etale
    {B : Type u} {C : Type v} [CommRing B] [CommRing C] [Algebra K B] [Algebra K C]
    [Algebra.Etale K B] [Algebra.Etale K C]
    (Φ : (C →ₐ[K] Ω) → (B →ₐ[K] Ω))
    (hΦ : ∀ (γ : Ω ≃ₐ[K] Ω) (χ : C →ₐ[K] Ω),
      Φ (γ.toAlgHom.comp χ) = γ.toAlgHom.comp (Φ χ)) :
    ∃! ψ : B →ₐ[K] C, ∀ χ : C →ₐ[K] Ω, χ.comp ψ = Φ χ := by
  obtain ⟨ψ, hψ⟩ := exists_algHom_realizing_equivariant_pointsMap_of_etale Φ hΦ
  exact ⟨ψ, hψ, fun ψ' hψ' =>
    algHom_ext_of_points (fun χ => (hψ' χ).trans (hψ χ).symm)⟩

end EtaleDescent

end HopfAlgebra.GenMuDescent
p2m_reactivate "P2MW.S_HopfAlgebra_nonempty_bialgEquiv_monoidAlgebra_of_natCard_algHom_eq_of_convPow_rat.HopfAlgebra P2MW.S_HopfAlgebra_nonempty_bialgEquiv_monoidAlgebra_of_natCard_algHom_eq_of_convPow_rat.HopfAlgebra.GenMuDescent"
p2m_reactivate "P2MW.S_HopfAlgebra_nonempty_bialgEquiv_monoidAlgebra_of_natCard_algHom_eq_of_convPow_rat.HopfAlgebra"

namespace HopfAlgebra
p2m_export "HopfAlgebra" "ofAlgHom mul_antipode_rTensor_comul mul_antipode_lTensor_comul isReduced_of_finiteType_of_charZero"
namespace GenMu
p2m_open "HopfAlgebra"

p2m_open "WithConv HopfAlgebra P2MW.S_HopfAlgebra_nonempty_bialgEquiv_monoidAlgebra_of_natCard_algHom_eq_of_convPow_rat.HopfAlgebra"

section Units
variable {K : Type*} [CommRing K] {A : Type*} [CommRing A] [HopfAlgebra K A]
  {Ω : Type*} [CommRing Ω] [Algebra K Ω]

noncomputable def ιL : WithConv (A →ₐ[K] Ω) →* WithConv (A →ₗ[K] Ω) where
  toFun χ := toConv χ.ofConv.toLinearMap
  map_one' := AlgHom.toLinearMap_convOne
  map_mul' := AlgHom.toLinearMap_convMul

theorem ιL_apply (χ : WithConv (A →ₐ[K] Ω)) : ιL χ = toConv χ.ofConv.toLinearMap := rfl

theorem ιL_injective : Function.Injective (ιL : WithConv (A →ₐ[K] Ω) → WithConv (A →ₗ[K] Ω)) :=
  fun _ _ h => WithConv.ofConv_injective (AlgHom.toLinearMap_injective (WithConv.toConv_injective h))

theorem toConv_antipode_mul_toConv_id :
    toConv (antipode K (A := A)) * toConv (LinearMap.id : A →ₗ[K] A) = 1 := by
  rw [LinearMap.convMul_def, LinearMap.convOne_def]
  exact congrArg toConv (mul_antipode_rTensor_comul (R := K) (A := A))

theorem toConv_id_mul_toConv_antipode :
    toConv (LinearMap.id : A →ₗ[K] A) * toConv (antipode K (A := A)) = 1 := by
  rw [LinearMap.convMul_def, LinearMap.convOne_def]
  exact congrArg toConv (mul_antipode_lTensor_comul (R := K) (A := A))

theorem comp_convOne_linear (χ : A →ₐ[K] Ω) :
    χ.toLinearMap ∘ₗ (1 : WithConv (A →ₗ[K] A)).ofConv = (1 : WithConv (A →ₗ[K] Ω)).ofConv := by
  apply LinearMap.ext
  intro a
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.convOne_apply, AlgHom.toLinearMap_apply,
    AlgHom.commutes]

theorem isUnit_ιL (χ : WithConv (A →ₐ[K] Ω)) : IsUnit (ιL χ) := by
  have hdist := fun (f g : WithConv (A →ₗ[K] A)) =>
    LinearMap.algHom_comp_convMul_distrib χ.ofConv f g
  have h1 : toConv (χ.ofConv.toLinearMap ∘ₗ antipode K (A := A)) * ιL χ = 1 := by
    have := hdist (toConv (antipode K (A := A))) (toConv LinearMap.id)
    rw [toConv_antipode_mul_toConv_id, comp_convOne_linear] at this
    apply WithConv.ofConv_injective
    rw [this]
    rfl
  have h2 : ιL χ * toConv (χ.ofConv.toLinearMap ∘ₗ antipode K (A := A)) = 1 := by
    have := hdist (toConv LinearMap.id) (toConv (antipode K (A := A)))
    rw [toConv_id_mul_toConv_antipode, comp_convOne_linear] at this
    apply WithConv.ofConv_injective
    rw [this]
    rfl
  exact ⟨⟨ιL χ, _, h2, h1⟩, rfl⟩

scoped instance instFiniteWithConvAlgHom [Finite (A →ₐ[K] Ω)] : Finite (WithConv (A →ₐ[K] Ω)) :=
  Finite.of_equiv _ ⟨toConv, ofConv, fun _ => rfl, fun _ => rfl⟩

theorem natCard_withConv : Nat.card (WithConv (A →ₐ[K] Ω)) = Nat.card (A →ₐ[K] Ω) :=
  Nat.card_congr ⟨ofConv, toConv, fun _ => rfl, fun _ => rfl⟩

theorem isUnit_point [Finite (A →ₐ[K] Ω)] (χ : WithConv (A →ₐ[K] Ω)) : IsUnit χ := by
  obtain ⟨a, b, hab, h⟩ := Finite.exists_ne_map_eq_of_infinite (fun n : ℕ => χ ^ n)
  wlog hlt : a < b generalizing a b
  · exact this b a hab.symm h.symm (lt_of_le_of_ne (not_lt.mp hlt) hab.symm)
  obtain ⟨u, hu⟩ := isUnit_ιL χ
  have hpow : χ ^ (b - a) = 1 := by
    apply ιL_injective
    rw [map_pow, map_one]
    have h' : ιL (χ ^ a) = ιL (χ ^ b) := congrArg ιL h
    rw [← Nat.add_sub_cancel' hlt.le, pow_add, map_mul, map_pow, map_pow, ← hu,
      ← Units.val_pow_eq_pow_val, ← Units.val_pow_eq_pow_val] at h'
    rw [← hu, ← Units.val_pow_eq_pow_val]
    have h'' : (↑(u ^ a) : WithConv (A →ₗ[K] Ω)) * 1 = ↑(u ^ a) * ↑(u ^ (b - a)) := by
      rw [mul_one]; exact h'
    exact (Units.mul_right_inj (u ^ a) |>.mp h'').symm
  exact IsUnit.of_pow_eq_one hpow (Nat.sub_ne_zero_of_lt hlt)

@[reducible] noncomputable def pointsGroup [Finite (A →ₐ[K] Ω)] : Group (WithConv (A →ₐ[K] Ω)) :=
  groupOfIsUnit isUnit_point

end Units
p2m_reactivate "P2MW.S_HopfAlgebra_nonempty_bialgEquiv_monoidAlgebra_of_natCard_algHom_eq_of_convPow_rat.HopfAlgebra P2MW.S_HopfAlgebra_nonempty_bialgEquiv_monoidAlgebra_of_natCard_algHom_eq_of_convPow_rat.HopfAlgebra.GenMuDescent"

end HopfAlgebra.GenMu
p2m_reactivate "P2MW.S_HopfAlgebra_nonempty_bialgEquiv_monoidAlgebra_of_natCard_algHom_eq_of_convPow_rat.HopfAlgebra P2MW.S_HopfAlgebra_nonempty_bialgEquiv_monoidAlgebra_of_natCard_algHom_eq_of_convPow_rat.HopfAlgebra.GenMuDescent P2MW.S_HopfAlgebra_nonempty_bialgEquiv_monoidAlgebra_of_natCard_algHom_eq_of_convPow_rat.HopfAlgebra.GenMu"
p2m_reactivate "P2MW.S_HopfAlgebra_nonempty_bialgEquiv_monoidAlgebra_of_natCard_algHom_eq_of_convPow_rat.HopfAlgebra P2MW.S_HopfAlgebra_nonempty_bialgEquiv_monoidAlgebra_of_natCard_algHom_eq_of_convPow_rat.HopfAlgebra.GenMuDescent"

namespace HopfAlgebra
p2m_export "HopfAlgebra" "ofAlgHom mul_antipode_rTensor_comul mul_antipode_lTensor_comul isReduced_of_finiteType_of_charZero"
namespace GenMu
p2m_open "HopfAlgebra"
open WithConv

section GroupLikeEval
variable {R : Type*} [CommSemiring R] {C : Type*} [Semiring C] [Bialgebra R C]
  {A : Type*} [CommSemiring A] [Algebra R A]

theorem convMul_apply_of_isGroupLikeElem (f g : WithConv (C →ₐ[R] A)) {x : C}
    (hx : IsGroupLikeElem R x) : (f * g).ofConv x = f.ofConv x * g.ofConv x := by
  rw [AlgHom.convMul_apply, ((isGroupLikeElem_iff R x).1 hx).2, Algebra.TensorProduct.lift_tmul]

theorem convOne_apply_of_isGroupLikeElem {x : C} (hx : IsGroupLikeElem R x) :
    (1 : WithConv (C →ₐ[R] A)).ofConv x = 1 := by
  rw [AlgHom.convOne_apply, ((isGroupLikeElem_iff R x).1 hx).1, map_one]

theorem convPow_apply_of_isGroupLikeElem (f : WithConv (C →ₐ[R] A)) {x : C}
    (hx : IsGroupLikeElem R x) (n : ℕ) : (f ^ n).ofConv x = (f.ofConv x) ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, convOne_apply_of_isGroupLikeElem hx]
  | succ n ih => rw [pow_succ, pow_succ, convMul_apply_of_isGroupLikeElem _ _ hx, ih]

end GroupLikeEval
p2m_reactivate "P2MW.S_HopfAlgebra_nonempty_bialgEquiv_monoidAlgebra_of_natCard_algHom_eq_of_convPow_rat.HopfAlgebra P2MW.S_HopfAlgebra_nonempty_bialgEquiv_monoidAlgebra_of_natCard_algHom_eq_of_convPow_rat.HopfAlgebra.GenMuDescent P2MW.S_HopfAlgebra_nonempty_bialgEquiv_monoidAlgebra_of_natCard_algHom_eq_of_convPow_rat.HopfAlgebra.GenMu"

section PowHom
variable {M : Type*} [Monoid M]

def powHomOfPowEqOne (u : M) {n : ℕ} [NeZero n] (hu : u ^ n = 1) : Multiplicative (ZMod n) →* M where
  toFun g := u ^ (Multiplicative.toAdd g).val
  map_one' := by simp
  map_mul' a b := by
    simp only [toAdd_mul, ZMod.val_add, ← pow_add]
    conv_rhs => rw [← Nat.mod_add_div ((Multiplicative.toAdd a).val + (Multiplicative.toAdd b).val) n,
      pow_add, pow_mul, hu, one_pow, mul_one]

@[scoped simp] theorem powHomOfPowEqOne_apply (u : M) {n : ℕ} [NeZero n] (hu : u ^ n = 1)
    (g : Multiplicative (ZMod n)) :
    powHomOfPowEqOne u hu g = u ^ (Multiplicative.toAdd g).val := rfl

end PowHom
p2m_reactivate "P2MW.S_HopfAlgebra_nonempty_bialgEquiv_monoidAlgebra_of_natCard_algHom_eq_of_convPow_rat.HopfAlgebra P2MW.S_HopfAlgebra_nonempty_bialgEquiv_monoidAlgebra_of_natCard_algHom_eq_of_convPow_rat.HopfAlgebra.GenMuDescent P2MW.S_HopfAlgebra_nonempty_bialgEquiv_monoidAlgebra_of_natCard_algHom_eq_of_convPow_rat.HopfAlgebra.GenMu"

section MuSide
variable (K : Type*) [Field K] (Ω : Type*) [Field Ω] [Algebra K Ω] (q : ℕ) [hq : Fact q.Prime]

scoped instance neZero_of_fact_prime : NeZero q := ⟨hq.out.ne_zero⟩

scoped instance fact_one_lt_of_fact_prime : Fact (1 < q) := ⟨hq.out.one_lt⟩

noncomputable def gen : MonoidAlgebra K (Multiplicative (ZMod q)) :=
  MonoidAlgebra.single (Multiplicative.ofAdd 1) 1

theorem ofAdd_one_pow_val (g : Multiplicative (ZMod q)) :
    (Multiplicative.ofAdd (1 : ZMod q)) ^ (Multiplicative.toAdd g).val = g := by
  rw [← ofAdd_nsmul, nsmul_eq_mul, mul_one, ZMod.natCast_zmod_val, ofAdd_toAdd]

theorem gen_pow_val (g : Multiplicative (ZMod q)) :
    gen K q ^ (Multiplicative.toAdd g).val = MonoidAlgebra.single g 1 := by
  rw [gen, MonoidAlgebra.single_pow, one_pow, ofAdd_one_pow_val]

theorem gen_pow_q : gen K q ^ q = 1 := by
  rw [gen, MonoidAlgebra.single_pow, one_pow, ← ofAdd_nsmul, nsmul_eq_mul, mul_one,
    ZMod.natCast_self, ofAdd_zero, MonoidAlgebra.one_def]

theorem isGroupLikeElem_gen : IsGroupLikeElem K (gen K q) := by
  rw [gen, isGroupLikeElem_iff]
  constructor
  · rw [MonoidAlgebra.counit_single, CommSemiring.counit_apply]
  · rw [MonoidAlgebra.comul_single, CommSemiring.comul_apply, TensorProduct.map_tmul,
      MonoidAlgebra.lsingle_apply]

variable {K Ω q} in

theorem algHom_ext_gen {B : Type*} [Semiring B] [Algebra K B]
    {χ₁ χ₂ : MonoidAlgebra K (Multiplicative (ZMod q)) →ₐ[K] B}
    (h : χ₁ (gen K q) = χ₂ (gen K q)) : χ₁ = χ₂ :=
  MonoidAlgebra.algHom_ext (fun g => by rw [← gen_pow_val, map_pow, map_pow, h]) (Subsingleton.elim _ _)

theorem apply_gen_pow_q {B : Type*} [Semiring B] [Algebra K B]
    (χ : MonoidAlgebra K (Multiplicative (ZMod q)) →ₐ[K] B) : χ (gen K q) ^ q = 1 := by
  rw [← map_pow, gen_pow_q, map_one]

noncomputable def pointOfRoot (ζ : Ω) (hζ : ζ ^ q = 1) :
    MonoidAlgebra K (Multiplicative (ZMod q)) →ₐ[K] Ω :=
  MonoidAlgebra.lift K Ω _ (powHomOfPowEqOne ζ hζ)

theorem pointOfRoot_gen (ζ : Ω) (hζ : ζ ^ q = 1) : pointOfRoot K Ω q ζ hζ (gen K q) = ζ := by
  rw [pointOfRoot, gen, MonoidAlgebra.lift_single, one_smul, powHomOfPowEqOne_apply, toAdd_ofAdd,
    ZMod.val_one, pow_one]

theorem convMul_apply_gen (χ₁ χ₂ : WithConv (MonoidAlgebra K (Multiplicative (ZMod q)) →ₐ[K] Ω)) :
    (χ₁ * χ₂).ofConv (gen K q) = χ₁.ofConv (gen K q) * χ₂.ofConv (gen K q) :=
  convMul_apply_of_isGroupLikeElem _ _ (isGroupLikeElem_gen K q)

theorem convPow_apply_gen (χ : WithConv (MonoidAlgebra K (Multiplicative (ZMod q)) →ₐ[K] Ω)) (n : ℕ) :
    (χ ^ n).ofConv (gen K q) = χ.ofConv (gen K q) ^ n :=
  convPow_apply_of_isGroupLikeElem _ (isGroupLikeElem_gen K q) n

theorem convOne_apply_gen :
    (1 : WithConv (MonoidAlgebra K (Multiplicative (ZMod q)) →ₐ[K] Ω)).ofConv (gen K q) = 1 :=
  convOne_apply_of_isGroupLikeElem (isGroupLikeElem_gen K q)

theorem comp_eq_convPow_of_forall_pow (γ : Ω →ₐ[K] Ω) (n : ℕ)
    (hγ : ∀ ζ : Ω, ζ ^ q = 1 → γ ζ = ζ ^ n)
    (χ : WithConv (MonoidAlgebra K (Multiplicative (ZMod q)) →ₐ[K] Ω)) :
    γ.comp χ.ofConv = (χ ^ n).ofConv :=
  algHom_ext_gen (by rw [AlgHom.comp_apply, hγ _ (apply_gen_pow_q K q _), convPow_apply_gen])

theorem toConv_pointOfRoot_pow_q (ζ : Ω) (hζ : ζ ^ q = 1) :
    toConv (pointOfRoot K Ω q ζ hζ) ^ q = 1 := by
  apply WithConv.ext
  apply algHom_ext_gen
  rw [convPow_apply_gen, pointOfRoot_gen, hζ, convOne_apply_gen]

theorem toConv_pointOfRoot_ne_one (ζ : Ω) (hζ : ζ ^ q = 1) (h1 : ζ ≠ 1) :
    toConv (pointOfRoot K Ω q ζ hζ) ≠ 1 := by
  intro h
  apply h1
  have := congrArg (fun χ : WithConv (MonoidAlgebra K (Multiplicative (ZMod q)) →ₐ[K] Ω) =>
    χ.ofConv (gen K q)) h
  simpa only [pointOfRoot_gen, convOne_apply_gen] using this

end MuSide
p2m_reactivate "P2MW.S_HopfAlgebra_nonempty_bialgEquiv_monoidAlgebra_of_natCard_algHom_eq_of_convPow_rat.HopfAlgebra P2MW.S_HopfAlgebra_nonempty_bialgEquiv_monoidAlgebra_of_natCard_algHom_eq_of_convPow_rat.HopfAlgebra.GenMuDescent P2MW.S_HopfAlgebra_nonempty_bialgEquiv_monoidAlgebra_of_natCard_algHom_eq_of_convPow_rat.HopfAlgebra.GenMu"

end HopfAlgebra.GenMu
p2m_reactivate "P2MW.S_HopfAlgebra_nonempty_bialgEquiv_monoidAlgebra_of_natCard_algHom_eq_of_convPow_rat.HopfAlgebra P2MW.S_HopfAlgebra_nonempty_bialgEquiv_monoidAlgebra_of_natCard_algHom_eq_of_convPow_rat.HopfAlgebra.GenMuDescent P2MW.S_HopfAlgebra_nonempty_bialgEquiv_monoidAlgebra_of_natCard_algHom_eq_of_convPow_rat.HopfAlgebra.GenMu"
p2m_reactivate "P2MW.S_HopfAlgebra_nonempty_bialgEquiv_monoidAlgebra_of_natCard_algHom_eq_of_convPow_rat.HopfAlgebra P2MW.S_HopfAlgebra_nonempty_bialgEquiv_monoidAlgebra_of_natCard_algHom_eq_of_convPow_rat.HopfAlgebra.GenMuDescent P2MW.S_HopfAlgebra_nonempty_bialgEquiv_monoidAlgebra_of_natCard_algHom_eq_of_convPow_rat.HopfAlgebra.GenMu"

namespace HopfAlgebra
p2m_export "HopfAlgebra" "ofAlgHom mul_antipode_rTensor_comul mul_antipode_lTensor_comul isReduced_of_finiteType_of_charZero"
namespace GenMu
p2m_open "HopfAlgebra"
open WithConv
open scoped TensorProduct

section CyclotomicExponent
variable {K : Type*} [Field K] {Ω : Type*} [Field Ω] [Algebra K Ω] (q : ℕ) [Fact q.Prime]

theorem exists_pow_of_algEquiv (γ : Ω ≃ₐ[K] Ω) : ∃ n : ℕ, ∀ ζ : Ω, ζ ^ q = 1 → γ ζ = ζ ^ n := by
  obtain ⟨m, hm⟩ := rootsOfUnity.integer_power_of_ringEquiv' q γ.toRingEquiv
  refine ⟨(m % (q : ℤ)).toNat, fun ζ hζ => ?_⟩
  have hu : IsUnit ζ := IsUnit.of_pow_eq_one hζ (NeZero.ne q)
  have hunit : hu.unit ^ q = 1 := by
    ext
    rw [Units.val_pow_eq_pow_val, IsUnit.unit_spec, hζ, Units.val_one]
  have hmem : hu.unit ∈ rootsOfUnity q Ω := by
    rw [mem_rootsOfUnity]
    exact hunit
  have huq : hu.unit ^ (q : ℤ) = 1 := by
    rw [zpow_natCast]
    exact hunit
  have := hm hu.unit hmem
  rw [zpow_eq_zpow_emod m huq, ← Int.toNat_of_nonneg (Int.emod_nonneg m (by exact_mod_cast NeZero.ne q)),
    zpow_natCast, Units.val_pow_eq_pow_val, IsUnit.unit_spec] at this
  exact this

end CyclotomicExponent
p2m_reactivate "P2MW.S_HopfAlgebra_nonempty_bialgEquiv_monoidAlgebra_of_natCard_algHom_eq_of_convPow_rat.HopfAlgebra P2MW.S_HopfAlgebra_nonempty_bialgEquiv_monoidAlgebra_of_natCard_algHom_eq_of_convPow_rat.HopfAlgebra.GenMuDescent P2MW.S_HopfAlgebra_nonempty_bialgEquiv_monoidAlgebra_of_natCard_algHom_eq_of_convPow_rat.HopfAlgebra.GenMu"

section Comul
variable {K : Type*} [Field K] {Ω : Type*} [Field Ω] [Algebra K Ω] [IsAlgClosed Ω]
  {V : Type*} [CommRing V] [Bialgebra K V] {A : Type*} [CommRing A] [Bialgebra K A]

omit [IsAlgClosed Ω] in
theorem lift_map_eq (χ₁ χ₂ : A →ₐ[K] Ω) (e : V →ₐ[K] A) (z : V ⊗[K] V) :
    Algebra.TensorProduct.lift χ₁ χ₂ (fun _ _ => .all _ _) (Algebra.TensorProduct.map e e z) =
      Algebra.TensorProduct.lift (χ₁.comp e) (χ₂.comp e) (fun _ _ => .all _ _) z := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul x y => simp only [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.lift_tmul,
      AlgHom.comp_apply]
  | add a b ha hb => simp only [map_add, ha, hb]

omit [IsAlgClosed Ω] in

theorem eq_lift_of_point (θ : A ⊗[K] A →ₐ[K] Ω) :
    θ = Algebra.TensorProduct.lift (θ.comp Algebra.TensorProduct.includeLeft)
      ((θ.restrictScalars K).comp Algebra.TensorProduct.includeRight) (fun _ _ => .all _ _) := by
  apply Algebra.TensorProduct.ext
  · ext a
    simp only [AlgHom.comp_apply, Algebra.TensorProduct.includeLeft_apply,
      Algebra.TensorProduct.lift_tmul, map_one, mul_one]
  · ext a
    simp only [AlgHom.comp_apply, AlgHom.coe_restrictScalars', Algebra.TensorProduct.includeRight_apply,
      Algebra.TensorProduct.lift_tmul, map_one, one_mul]

theorem map_comp_comul_eq_of_points [Algebra.Etale K (A ⊗[K] A)] (e : V →ₐ[K] A)
    (hmul : ∀ χ₁ χ₂ : WithConv (A →ₐ[K] Ω),
      toConv ((χ₁ * χ₂).ofConv.comp e) = toConv (χ₁.ofConv.comp e) * toConv (χ₂.ofConv.comp e)) :
    (Algebra.TensorProduct.map e e).comp (Bialgebra.comulAlgHom K V) =
      (Bialgebra.comulAlgHom K A).comp e := by
  apply HopfAlgebra.GenMuDescent.algHom_ext_of_points (K := K) (Ω := Ω)
  intro θ
  set χ₁ : A →ₐ[K] Ω := θ.comp Algebra.TensorProduct.includeLeft
  set χ₂ : A →ₐ[K] Ω := (θ.restrictScalars K).comp Algebra.TensorProduct.includeRight
  have hθ := eq_lift_of_point θ
  have h1 : θ.comp ((Bialgebra.comulAlgHom K A).comp e) = (toConv χ₁ * toConv χ₂).ofConv.comp e := by
    apply AlgHom.ext
    intro v
    rw [AlgHom.comp_apply, AlgHom.comp_apply, AlgHom.comp_apply, AlgHom.convMul_apply,
      Bialgebra.comulAlgHom_apply, hθ]
  have h2 : θ.comp ((Algebra.TensorProduct.map e e).comp (Bialgebra.comulAlgHom K V)) =
      (toConv (χ₁.comp e) * toConv (χ₂.comp e)).ofConv := by
    apply AlgHom.ext
    intro v
    rw [AlgHom.comp_apply, AlgHom.comp_apply, AlgHom.convMul_apply, Bialgebra.comulAlgHom_apply, hθ,
      lift_map_eq]
  rw [h1, h2]
  exact (congrArg WithConv.ofConv (hmul (toConv χ₁) (toConv χ₂))).symm

end Comul
p2m_reactivate "P2MW.S_HopfAlgebra_nonempty_bialgEquiv_monoidAlgebra_of_natCard_algHom_eq_of_convPow_rat.HopfAlgebra P2MW.S_HopfAlgebra_nonempty_bialgEquiv_monoidAlgebra_of_natCard_algHom_eq_of_convPow_rat.HopfAlgebra.GenMuDescent P2MW.S_HopfAlgebra_nonempty_bialgEquiv_monoidAlgebra_of_natCard_algHom_eq_of_convPow_rat.HopfAlgebra.GenMu"

section Core
variable {K : Type*} [Field K] [CharZero K] {Ω : Type*} [Field Ω] [Algebra K Ω] [IsAlgClosed Ω]
  [Algebra.IsAlgebraic K Ω] [IsGalois K Ω] [CharZero Ω]
  (q : ℕ) [hq : Fact q.Prime]
  {A : Type*} [CommRing A] [HopfAlgebra K A] [Module.Finite K A]

local notation "V" => MonoidAlgebra K (Multiplicative (ZMod q))

theorem exists_isGroupLikeElem_of_natCard_algHom_eq_of_convPow
    (hgenq : Nat.card (A →ₐ[K] Ω) = q)
    (hgal : ∀ (γ : Ω ≃ₐ[K] Ω) (n : ℕ), (∀ ζ : Ω, ζ ^ q = 1 → γ ζ = ζ ^ n) →
      ∀ χ : WithConv (A →ₐ[K] Ω), toConv (γ.toAlgHom.comp χ.ofConv) = χ ^ n) :
    ∃ u : A, IsGroupLikeElem K u ∧ u ^ q = 1 ∧ u ≠ 1 := by
  classical
  let M := WithConv (A →ₐ[K] Ω)

  haveI : Algebra.Etale K A := etale_of_hopf_charZero K A
  haveI : Algebra.Etale K V := etale_of_hopf_charZero K V
  haveI : Algebra.Etale K (A ⊗[K] A) := etale_of_hopf_charZero K (A ⊗[K] A)

  haveI : Finite (A →ₐ[K] Ω) := Nat.finite_of_card_ne_zero (hgenq ▸ hq.out.ne_zero)
  letI : Group M := pointsGroup
  have hcardM : Nat.card M = q := natCard_withConv.trans hgenq
  haveI hcyc : IsCyclic M := isCyclic_of_prime_card hcardM
  let eM : M ≃* Multiplicative (ZMod q) :=
    (zmodCyclicMulEquiv hcyc).symm.trans
      (AddEquiv.toMultiplicative (ZMod.ringEquivCongr hcardM).toAddEquiv)

  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω q
  have hζq : ζ ^ q = 1 := hζ.pow_eq_one
  have hζ1 : ζ ≠ 1 := hζ.ne_one hq.out.one_lt
  let χζ : WithConv (V →ₐ[K] Ω) := toConv (pointOfRoot K Ω q ζ hζq)
  have hχζq : χζ ^ q = 1 := toConv_pointOfRoot_pow_q K Ω q ζ hζq

  let Φ : M → WithConv (V →ₐ[K] Ω) := fun m => powHomOfPowEqOne χζ hχζq (eM m)
  have hΦmul : ∀ m m' : M, Φ (m * m') = Φ m * Φ m' := fun m m' => by
    simp only [Φ, map_mul]
  have hΦpow : ∀ (m : M) (n : ℕ), Φ (m ^ n) = Φ m ^ n := fun m n => by
    simp only [Φ, map_pow]

  let Φfun : (A →ₐ[K] Ω) → (V →ₐ[K] Ω) := fun χ => (Φ (toConv χ)).ofConv
  have hΦeq : ∀ (γ : Ω ≃ₐ[K] Ω) (χ : A →ₐ[K] Ω),
      Φfun (γ.toAlgHom.comp χ) = γ.toAlgHom.comp (Φfun χ) := by
    intro γ χ
    obtain ⟨n, hn⟩ := exists_pow_of_algEquiv q γ
    simp only [Φfun]
    rw [comp_eq_convPow_of_forall_pow K Ω q γ.toAlgHom n hn, ← hΦpow]
    congr 2
    exact hgal γ n hn (toConv χ)

  obtain ⟨e, he⟩ :=
    HopfAlgebra.GenMuDescent.exists_algHom_realizing_equivariant_pointsMap_of_etale
      (K := K) (Ω := Ω) (B := V) (C := A) Φfun hΦeq

  have he' : ∀ m : M, toConv (m.ofConv.comp e) = Φ m := fun m => by
    rw [he]

  refine ⟨e (gen K q), ?_, ?_, ?_⟩
  ·
    rw [isGroupLikeElem_iff]
    constructor
    ·
      have h1 := he' 1
      rw [show Φ 1 = 1 by simp only [Φ, map_one]] at h1
      have h2 := congrArg (fun χ : WithConv (V →ₐ[K] Ω) => χ.ofConv (gen K q)) h1
      simp only [AlgHom.comp_apply, AlgHom.convOne_apply] at h2
      apply (algebraMap K Ω).injective
      rw [h2, (isGroupLikeElem_gen K q).counit_eq_one]
    ·
      have hmul : ∀ χ₁ χ₂ : WithConv (A →ₐ[K] Ω),
          toConv ((χ₁ * χ₂).ofConv.comp e) = toConv (χ₁.ofConv.comp e) * toConv (χ₂.ofConv.comp e) := by
        intro χ₁ χ₂
        rw [he', he', he']
        exact hΦmul χ₁ χ₂
      have hc := map_comp_comul_eq_of_points (K := K) (Ω := Ω) e hmul
      have hcg := DFunLike.congr_fun hc (gen K q)
      simp only [AlgHom.comp_apply, Bialgebra.comulAlgHom_apply] at hcg
      rw [← hcg, (isGroupLikeElem_gen K q).comul_eq_tmul_self, Algebra.TensorProduct.map_tmul]
  ·
    rw [← map_pow, gen_pow_q, map_one]
  ·
    intro hu
    apply hζ1
    let m₀ : M := eM.symm (Multiplicative.ofAdd 1)
    have hΦm₀ : Φ m₀ = χζ := by
      simp only [Φ, m₀, MulEquiv.apply_symm_apply, powHomOfPowEqOne_apply, toAdd_ofAdd, ZMod.val_one,
        pow_one]
    have h1 := he' m₀
    rw [hΦm₀] at h1
    have h2 := congrArg (fun χ : WithConv (V →ₐ[K] Ω) => χ.ofConv (gen K q)) h1
    simp only [AlgHom.comp_apply, χζ] at h2
    rw [pointOfRoot_gen] at h2
    rw [← h2, hu, map_one]

end Core
p2m_reactivate "P2MW.S_HopfAlgebra_nonempty_bialgEquiv_monoidAlgebra_of_natCard_algHom_eq_of_convPow_rat.HopfAlgebra P2MW.S_HopfAlgebra_nonempty_bialgEquiv_monoidAlgebra_of_natCard_algHom_eq_of_convPow_rat.HopfAlgebra.GenMuDescent P2MW.S_HopfAlgebra_nonempty_bialgEquiv_monoidAlgebra_of_natCard_algHom_eq_of_convPow_rat.HopfAlgebra.GenMu"

end HopfAlgebra.GenMu
p2m_reactivate "P2MW.S_HopfAlgebra_nonempty_bialgEquiv_monoidAlgebra_of_natCard_algHom_eq_of_convPow_rat.HopfAlgebra P2MW.S_HopfAlgebra_nonempty_bialgEquiv_monoidAlgebra_of_natCard_algHom_eq_of_convPow_rat.HopfAlgebra.GenMuDescent P2MW.S_HopfAlgebra_nonempty_bialgEquiv_monoidAlgebra_of_natCard_algHom_eq_of_convPow_rat.HopfAlgebra.GenMu"
p2m_reactivate "P2MW.S_HopfAlgebra_nonempty_bialgEquiv_monoidAlgebra_of_natCard_algHom_eq_of_convPow_rat.HopfAlgebra P2MW.S_HopfAlgebra_nonempty_bialgEquiv_monoidAlgebra_of_natCard_algHom_eq_of_convPow_rat.HopfAlgebra.GenMuDescent P2MW.S_HopfAlgebra_nonempty_bialgEquiv_monoidAlgebra_of_natCard_algHom_eq_of_convPow_rat.HopfAlgebra.GenMu"

namespace HopfAlgebra
p2m_export "HopfAlgebra" "ofAlgHom mul_antipode_rTensor_comul mul_antipode_lTensor_comul isReduced_of_finiteType_of_charZero"
namespace GenMu
p2m_open "HopfAlgebra"
open WithConv

theorem exists_isGroupLikeElem_of_natCard_algHom_eq_of_convPow_rat
    (q : ℕ) [Fact q.Prime]
    (A : Type) [CommRing A] [HopfAlgebra ℚ A] [Module.Finite ℚ A]
    (hgenq : Nat.card (A →ₐ[ℚ] AlgebraicClosure ℚ) = q)
    (hgal : ∀ (σ : AlgebraicClosure ℚ ≃+* AlgebraicClosure ℚ) (nσ : ℕ),
      (∀ ζ : AlgebraicClosure ℚ, ζ ^ q = 1 → σ ζ = ζ ^ nσ) →
      ∀ (ψ : A →ₐ[ℚ] AlgebraicClosure ℚ) (a : A),
        σ (ψ a) = (WithConv.ofConv (WithConv.toConv ψ ^ nσ)) a) :
    ∃ u : A, IsGroupLikeElem ℚ u ∧ u ^ q = 1 ∧ u ≠ 1 := by
  haveI : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := AlgebraicClosure.isAlgebraic ℚ
  haveI : IsAlgClosure ℚ (AlgebraicClosure ℚ) := ⟨inferInstance, inferInstance⟩
  haveI : IsGalois ℚ (AlgebraicClosure ℚ) := IsAlgClosure.isGalois ℚ _
  refine exists_isGroupLikeElem_of_natCard_algHom_eq_of_convPow (K := ℚ)
    (Ω := AlgebraicClosure ℚ) q hgenq ?_
  intro γ n hn χ
  apply WithConv.ext
  apply AlgHom.ext
  intro a
  exact hgal γ.toRingEquiv n hn χ.ofConv a

end HopfAlgebra.GenMu
p2m_reactivate "P2MW.S_HopfAlgebra_nonempty_bialgEquiv_monoidAlgebra_of_natCard_algHom_eq_of_convPow_rat.HopfAlgebra P2MW.S_HopfAlgebra_nonempty_bialgEquiv_monoidAlgebra_of_natCard_algHom_eq_of_convPow_rat.HopfAlgebra.GenMuDescent P2MW.S_HopfAlgebra_nonempty_bialgEquiv_monoidAlgebra_of_natCard_algHom_eq_of_convPow_rat.HopfAlgebra.GenMu"
p2m_reactivate "P2MW.S_HopfAlgebra_nonempty_bialgEquiv_monoidAlgebra_of_natCard_algHom_eq_of_convPow_rat.HopfAlgebra P2MW.S_HopfAlgebra_nonempty_bialgEquiv_monoidAlgebra_of_natCard_algHom_eq_of_convPow_rat.HopfAlgebra.GenMuDescent P2MW.S_HopfAlgebra_nonempty_bialgEquiv_monoidAlgebra_of_natCard_algHom_eq_of_convPow_rat.HopfAlgebra.GenMu"

namespace HopfAlgebra
p2m_export "HopfAlgebra" "ofAlgHom mul_antipode_rTensor_comul mul_antipode_lTensor_comul isReduced_of_finiteType_of_charZero"
namespace GenMu
p2m_open "HopfAlgebra"
open WithConv
open scoped TensorProduct

section Full
variable {K : Type*} [Field K] [CharZero K] {Ω : Type*} [Field Ω] [Algebra K Ω] [IsAlgClosed Ω]
  [Algebra.IsAlgebraic K Ω] [IsGalois K Ω] [CharZero Ω]
  (q : ℕ) [hq : Fact q.Prime]
  {A : Type*} [CommRing A] [HopfAlgebra K A] [Module.Finite K A]

local notation "V" => MonoidAlgebra K (Multiplicative (ZMod q))

omit [CharZero K] [IsAlgClosed Ω] [Algebra.IsAlgebraic K Ω] [IsGalois K Ω] [CharZero Ω] hq [Module.Finite K A] in

theorem algHom_eq_of_ofId_comp_eq {B : Type*} [Semiring B] [Algebra K B] {g₁ g₂ : B →ₐ[K] K}
    (h : (Algebra.ofId K Ω).comp g₁ = (Algebra.ofId K Ω).comp g₂) : g₁ = g₂ :=
  AlgHom.ext fun b => (algebraMap K Ω).injective (DFunLike.congr_fun h b)

theorem nonempty_bialgEquiv_monoidAlgebra_of_natCard_algHom_eq_of_convPow
    (hgenq : Nat.card (A →ₐ[K] Ω) = q)
    (hgal : ∀ (γ : Ω ≃ₐ[K] Ω) (n : ℕ), (∀ ζ : Ω, ζ ^ q = 1 → γ ζ = ζ ^ n) →
      ∀ χ : WithConv (A →ₐ[K] Ω), toConv (γ.toAlgHom.comp χ.ofConv) = χ ^ n) :
    Nonempty (A ≃ₐc[K] MonoidAlgebra K (Multiplicative (ZMod q))) := by
  classical
  let M := WithConv (A →ₐ[K] Ω)

  haveI : Algebra.Etale K A := etale_of_hopf_charZero K A
  haveI : Algebra.Etale K V := etale_of_hopf_charZero K V
  haveI : Algebra.Etale K (A ⊗[K] A) := etale_of_hopf_charZero K (A ⊗[K] A)

  haveI : Finite (A →ₐ[K] Ω) := Nat.finite_of_card_ne_zero (hgenq ▸ hq.out.ne_zero)
  letI : Group M := pointsGroup
  have hcardM : Nat.card M = q := natCard_withConv.trans hgenq
  haveI hcyc : IsCyclic M := isCyclic_of_prime_card hcardM
  let eM : M ≃* Multiplicative (ZMod q) :=
    (zmodCyclicMulEquiv hcyc).symm.trans
      (AddEquiv.toMultiplicative (ZMod.ringEquivCongr hcardM).toAddEquiv)

  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω q
  have hζq : ζ ^ q = 1 := hζ.pow_eq_one
  let χζ : WithConv (V →ₐ[K] Ω) := toConv (pointOfRoot K Ω q ζ hζq)
  have hχζq : χζ ^ q = 1 := toConv_pointOfRoot_pow_q K Ω q ζ hζq
  have hχζpow : ∀ n : ℕ, (χζ ^ n).ofConv (gen K q) = ζ ^ n := fun n => by
    rw [convPow_apply_gen]
    simp only [χζ, pointOfRoot_gen]

  let Φ : M → WithConv (V →ₐ[K] Ω) := fun m => powHomOfPowEqOne χζ hχζq (eM m)
  have hΦmul : ∀ m m' : M, Φ (m * m') = Φ m * Φ m' := fun m m' => by
    simp only [Φ, map_mul]
  have hΦpow : ∀ (m : M) (n : ℕ), Φ (m ^ n) = Φ m ^ n := fun m n => by
    simp only [Φ, map_pow]
  have hΦgen : ∀ m : M, (Φ m).ofConv (gen K q) = ζ ^ (Multiplicative.toAdd (eM m)).val := fun m => by
    simp only [Φ, powHomOfPowEqOne_apply, hχζpow]
  have hΦinj : Function.Injective Φ := by
    intro m m' h
    have h' := congrArg (fun χ : WithConv (V →ₐ[K] Ω) => χ.ofConv (gen K q)) h
    simp only [hΦgen] at h'
    have hval := hζ.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) h'
    exact eM.injective (Multiplicative.toAdd.injective (ZMod.val_injective _ hval))
  have hΦsurj : Function.Surjective Φ := by
    intro χ'
    obtain ⟨i, hi, hiq⟩ := hζ.eq_pow_of_pow_eq_one (apply_gen_pow_q K q χ'.ofConv)
    refine ⟨eM.symm (Multiplicative.ofAdd (i : ZMod q)), ?_⟩
    apply WithConv.ext
    apply algHom_ext_gen
    rw [hΦgen, MulEquiv.apply_symm_apply, toAdd_ofAdd, ZMod.val_natCast_of_lt hi, hiq]
  let ΦE : M ≃ WithConv (V →ₐ[K] Ω) := Equiv.ofBijective Φ ⟨hΦinj, hΦsurj⟩

  let Φfun : (A →ₐ[K] Ω) → (V →ₐ[K] Ω) := fun χ => (Φ (toConv χ)).ofConv
  let Ψfun : (V →ₐ[K] Ω) → (A →ₐ[K] Ω) := fun χ' => (ΦE.symm (toConv χ')).ofConv
  have hΦΨ : ∀ χ', Φfun (Ψfun χ') = χ' := fun χ' => by
    simp only [Φfun, Ψfun, toConv_ofConv]
    rw [show Φ (ΦE.symm (toConv χ')) = ΦE (ΦE.symm (toConv χ')) from rfl, Equiv.apply_symm_apply]
  have hΨΦ : ∀ χ, Ψfun (Φfun χ) = χ := fun χ => by
    simp only [Φfun, Ψfun, toConv_ofConv]
    rw [show Φ (toConv χ) = ΦE (toConv χ) from rfl, Equiv.symm_apply_apply]
  have hΦfun_inj : Function.Injective Φfun := fun χ₁ χ₂ h => by
    rw [← hΨΦ χ₁, ← hΨΦ χ₂, h]
  have hΦeq : ∀ (γ : Ω ≃ₐ[K] Ω) (χ : A →ₐ[K] Ω),
      Φfun (γ.toAlgHom.comp χ) = γ.toAlgHom.comp (Φfun χ) := by
    intro γ χ
    obtain ⟨n, hn⟩ := exists_pow_of_algEquiv q γ
    simp only [Φfun]
    rw [comp_eq_convPow_of_forall_pow K Ω q γ.toAlgHom n hn, ← hΦpow]
    congr 2
    exact hgal γ n hn (toConv χ)
  have hΨeq : ∀ (γ : Ω ≃ₐ[K] Ω) (χ' : V →ₐ[K] Ω),
      Ψfun (γ.toAlgHom.comp χ') = γ.toAlgHom.comp (Ψfun χ') := by
    intro γ χ'
    apply hΦfun_inj
    rw [hΦΨ, hΦeq, hΦΨ]

  obtain ⟨e, he⟩ :=
    HopfAlgebra.GenMuDescent.exists_algHom_realizing_equivariant_pointsMap_of_etale
      (K := K) (Ω := Ω) (B := V) (C := A) Φfun hΦeq
  obtain ⟨e', he'⟩ :=
    HopfAlgebra.GenMuDescent.exists_algHom_realizing_equivariant_pointsMap_of_etale
      (K := K) (Ω := Ω) (B := A) (C := V) Ψfun hΨeq
  have heM : ∀ m : M, toConv (m.ofConv.comp e) = Φ m := fun m => by rw [he]

  have h₁ : e.comp e' = AlgHom.id K A := by
    apply HopfAlgebra.GenMuDescent.algHom_ext_of_points (K := K) (Ω := Ω)
    intro χ
    rw [← AlgHom.comp_assoc, he, he', hΨΦ, AlgHom.comp_id]
  have h₂ : e'.comp e = AlgHom.id K V := by
    apply HopfAlgebra.GenMuDescent.algHom_ext_of_points (K := K) (Ω := Ω)
    intro χ'
    rw [← AlgHom.comp_assoc, he', he, hΦΨ, AlgHom.comp_id]
  let f : V ≃ₐ[K] A := AlgEquiv.ofAlgHom e e' h₁ h₂

  have hcounit : (Bialgebra.counitAlgHom K A).comp (f : V →ₐ[K] A) = Bialgebra.counitAlgHom K V := by
    apply algHom_eq_of_ofId_comp_eq (K := K) (Ω := Ω)
    have h1 := heM 1
    rw [show Φ 1 = 1 by simp only [Φ, map_one]] at h1
    have h1' := congrArg WithConv.ofConv h1
    exact h1'
  have hmul : ∀ χ₁ χ₂ : WithConv (A →ₐ[K] Ω),
      toConv ((χ₁ * χ₂).ofConv.comp e) = toConv (χ₁.ofConv.comp e) * toConv (χ₂.ofConv.comp e) := by
    intro χ₁ χ₂
    rw [heM, heM, heM]
    exact hΦmul χ₁ χ₂
  have hcomul : (Algebra.TensorProduct.map (f : V →ₐ[K] A) (f : V →ₐ[K] A)).comp
      (Bialgebra.comulAlgHom K V) = (Bialgebra.comulAlgHom K A).comp (f : V →ₐ[K] A) :=
    map_comp_comul_eq_of_points (K := K) (Ω := Ω) e hmul
  exact ⟨(BialgEquiv.ofAlgEquiv f hcounit hcomul).symm⟩

end Full
p2m_reactivate "P2MW.S_HopfAlgebra_nonempty_bialgEquiv_monoidAlgebra_of_natCard_algHom_eq_of_convPow_rat.HopfAlgebra P2MW.S_HopfAlgebra_nonempty_bialgEquiv_monoidAlgebra_of_natCard_algHom_eq_of_convPow_rat.HopfAlgebra.GenMuDescent P2MW.S_HopfAlgebra_nonempty_bialgEquiv_monoidAlgebra_of_natCard_algHom_eq_of_convPow_rat.HopfAlgebra.GenMu"

theorem nonempty_bialgEquiv_monoidAlgebra_of_natCard_algHom_eq_of_convPow_rat'
    (q : ℕ) [Fact q.Prime]
    (A : Type) [CommRing A] [HopfAlgebra ℚ A] [Module.Finite ℚ A]
    (hgenq : Nat.card (A →ₐ[ℚ] AlgebraicClosure ℚ) = q)
    (hgal : ∀ (σ : AlgebraicClosure ℚ ≃+* AlgebraicClosure ℚ) (nσ : ℕ),
      (∀ ζ : AlgebraicClosure ℚ, ζ ^ q = 1 → σ ζ = ζ ^ nσ) →
      ∀ (ψ : A →ₐ[ℚ] AlgebraicClosure ℚ) (a : A),
        σ (ψ a) = (WithConv.ofConv (WithConv.toConv ψ ^ nσ)) a) :
    Nonempty (A ≃ₐc[ℚ] MonoidAlgebra ℚ (Multiplicative (ZMod q))) := by
  haveI : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := AlgebraicClosure.isAlgebraic ℚ
  haveI : IsAlgClosure ℚ (AlgebraicClosure ℚ) := ⟨inferInstance, inferInstance⟩
  haveI : IsGalois ℚ (AlgebraicClosure ℚ) := IsAlgClosure.isGalois ℚ _
  refine nonempty_bialgEquiv_monoidAlgebra_of_natCard_algHom_eq_of_convPow (K := ℚ)
    (Ω := AlgebraicClosure ℚ) q hgenq ?_
  intro γ n hn χ
  apply WithConv.ext
  apply AlgHom.ext
  intro a
  exact hgal γ.toRingEquiv n hn χ.ofConv a

end HopfAlgebra.GenMu
p2m_reactivate "P2MW.S_HopfAlgebra_nonempty_bialgEquiv_monoidAlgebra_of_natCard_algHom_eq_of_convPow_rat.HopfAlgebra P2MW.S_HopfAlgebra_nonempty_bialgEquiv_monoidAlgebra_of_natCard_algHom_eq_of_convPow_rat.HopfAlgebra.GenMuDescent P2MW.S_HopfAlgebra_nonempty_bialgEquiv_monoidAlgebra_of_natCard_algHom_eq_of_convPow_rat.HopfAlgebra.GenMu"
p2m_reactivate "P2MW.S_HopfAlgebra_nonempty_bialgEquiv_monoidAlgebra_of_natCard_algHom_eq_of_convPow_rat.HopfAlgebra P2MW.S_HopfAlgebra_nonempty_bialgEquiv_monoidAlgebra_of_natCard_algHom_eq_of_convPow_rat.HopfAlgebra.GenMuDescent P2MW.S_HopfAlgebra_nonempty_bialgEquiv_monoidAlgebra_of_natCard_algHom_eq_of_convPow_rat.HopfAlgebra.GenMu"

theorem solution
    (q : ℕ) [Fact q.Prime]
    (A : Type) [CommRing A] [HopfAlgebra ℚ A] [Module.Finite ℚ A]
    (hgenq : Nat.card (A →ₐ[ℚ] AlgebraicClosure ℚ) = q)
    (hgal : ∀ (σ : AlgebraicClosure ℚ ≃+* AlgebraicClosure ℚ) (nσ : ℕ),
      (∀ ζ : AlgebraicClosure ℚ, ζ ^ q = 1 → σ ζ = ζ ^ nσ) →
      ∀ (ψ : A →ₐ[ℚ] AlgebraicClosure ℚ) (a : A),
        σ (ψ a) = (WithConv.ofConv (WithConv.toConv ψ ^ nσ)) a) :
    Nonempty (A ≃ₐc[ℚ] MonoidAlgebra ℚ (Multiplicative (ZMod q))) := by
  exact HopfAlgebra.GenMu.nonempty_bialgEquiv_monoidAlgebra_of_natCard_algHom_eq_of_convPow_rat'
    q A hgenq hgal

end S_HopfAlgebra_nonempty_bialgEquiv_monoidAlgebra_of_natCard_algHom_eq_of_convPow_rat
end P2MW
export P2MW.S_HopfAlgebra_nonempty_bialgEquiv_monoidAlgebra_of_natCard_algHom_eq_of_convPow_rat (solution)
