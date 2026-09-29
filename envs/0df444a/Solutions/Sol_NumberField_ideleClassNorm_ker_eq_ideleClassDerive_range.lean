-- Prove2me | solution 1 for NumberField.ideleClassNorm_ker_eq_ideleClassDerive_range
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/b7febd9f-8355-55eb-879d-6561552c2a4c

import Mathlib
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Theorems.Thm_M4aHerbrand_ideleClass_herbrandQuotient_eq_finrank
import Theorems.Thm_M4aHerbrand_idelicNormCoset_index_eq_ideleClassTateCard
import Theorems.Thm_M4aHerbrand_ideleClass_normCoset_index_ne_zero_and_finrank_dvd
import Theorems.Thm_M4aHerbrand_subsingleton_ideleGaloisDescent
import Theorems.Thm_NumberField_ideleClass_normCoset_index_dvd_finrank
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_ideleClassNorm_ker_eq_ideleClassDerive_range
p2m_attr_erase "instance" "FixedPoints.instMulActionElemFixedPointsOfSMulCommClass_definitions FixedPoints.module FixedPoints.instSMulElemFixedPointsOfSMulCommClass_definitions FixedPoints.instAddCommMonoidElemFixedPoints_definitions LanglandsTunnell.P2.Artin.ArtinPairCore.instNFN LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTENΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTKLN LanglandsTunnell.P2.Artin.ArtinPairCore.instFE LanglandsTunnell.P2.Artin.ArtinPairCore.instAKE LanglandsTunnell.P2.Artin.ArtinFieldCore.instAKN LanglandsTunnell.P2.Artin.ArtinPairCore.instCN LanglandsTunnell.P2.Artin.ArtinFieldCore.instFΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instAEΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instAjE LanglandsTunnell.P2.Artin.ArtinFieldCore.instGEN LanglandsTunnell.P2.Artin.ArtinFieldCore.instCΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instNZq LanglandsTunnell.P2.Artin.ArtinPairCore.instAEN LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKEN LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKjE LanglandsTunnell.P2.Artin.ArtinFieldCore.instCN LanglandsTunnell.P2.Artin.ArtinFieldCore.instANΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKLN LanglandsTunnell.P2.Artin.ArtinPairCore.instGEN LanglandsTunnell.P2.Artin.ArtinPairCore.instAiE LanglandsTunnell.P2.Artin.instCommGroupIp LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instAEN LanglandsTunnell.P2.Artin.ArtinPairCore.instFN LanglandsTunnell.P2.Artin.ArtinPairCore.instALN LanglandsTunnell.P2.Artin.ArtinFieldCore.instFN LanglandsTunnell.P2.Artin.ArtinPairCore.instAKN LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTKEN LanglandsTunnell.P2.Artin.ArtinFieldCore.instGEΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKiE LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFN LanglandsTunnell.P2.Artin.ArtinFieldCore.instAKE LanglandsTunnell.P2.Artin.ArtinPairCore.instNFE"
p2m_attr_erase "instance" "LanglandsTunnell.P2.Artin.ArtinFieldCore.instALN LanglandsTunnell.P2.Artin.primeAbove_liesOver LanglandsTunnell.P2.Artin.isGaloisGroup_ringOfIntegers LanglandsTunnell.P2.Artin.primeAbove_isMaximal LanglandsTunnell.P2.Artin.primeAbove_finite Deep.NTSupply.instNormalRayClassSubgroup instHenselianLocalRingOfCompactSpaceOfIsNoetherianRing NumberField.instHenselianLocalRingAdicCompletionIntegers instIsAdicCompleteMaximalIdealOfCompactSpace NumberField.instIsAdicCompleteMaximalIdealAdicCompletionIntegers instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions LanglandsTunnell.Lift48.instDecidablePredMatIsProjOrder LanglandsTunnell.Lift48.instDecidablePredMatIsPM1 FrobeniusDensity.isMaximal_ratPrimeIdeal LanglandsTunnell.P2.primeOver_finite LanglandsTunnell.P2.primeOver_isMaximal"
p2m_attr_erase "simp" "NumberField.FiniteSIdele.fibre_inr NumberField.FiniteSIdele.fibre_inl GroupCohomology.RepPi.proj_hom_apply GroupCohomology.RepPi.map_hom_apply GroupCohomology.RepPi.piRepresentation_apply GroupCohomology.RepPi.lift_hom_apply Rep.coe_invariantsMap_apply Rep.tateH0Map_mk Rep.coe_tateHneg1Map_apply Representation.coe_normToInvariants_apply Representation.normBar_mk AutomorphicForm.rightTranslationEmbed_smul_apply AutomorphicForm.CarrierPins.mk.injEq AutomorphicForm.CarrierPins.mk.sizeOf_spec AutomorphicForm.CuspidalityNotion.mk.injEq AutomorphicForm.HeckeEigensystem.twist_b AutomorphicForm.satakePow_zero AutomorphicForm.HeckeEigensystem.twist_a AutomorphicForm.HeckeEigensystem.mk.injEq AutomorphicForm.HeckeEigensystem.mk.sizeOf_spec AutomorphicForm.DescentPackage.mk.injEq AutomorphicForm.DescentPackage.mk.sizeOf_spec AutomorphicForm.CuspidalityNotion.mk.sizeOf_spec AutomorphicForm.satakePow_one FixedPoints.coe_zero FixedPoints.coe_smul FixedPoints.coe_add LanglandsTunnell.P2.Artin.ArtinPairCore.mk.sizeOf_spec LanglandsTunnell.P2.Artin.ArtinFieldCore.mk.sizeOf_spec LanglandsTunnell.P2.Artin.ArtinFieldCore.mk.injEq LanglandsTunnell.P2.Artin.ArtinPairCore.mk.injEq TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec NumberField.AdeleRing.val_finiteUnitsComponent IsDedekindDomain.FiniteAdeleRing.val_unitsComponent NumberField.AdeleRing.val_finitePartUnits NumberField.AdeleRing.val_infiniteUnitsComponent IsLocalRing.principalUnits_zero"

set_option autoImplicit false

open scoped TensorProduct

namespace R3HC1

p2m_open "Algebra TensorProduct.Algebra Matrix"

variable {K L : Type*} (A : Type*) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
  [IsGalois K L] [CommRing A] [Algebra K A]

noncomputable abbrev conj (τ : L ≃ₐ[K] L) : (A ⊗[K] L) ≃ₐ[A] (A ⊗[K] L) :=
  Algebra.TensorProduct.congr (AlgEquiv.refl : A ≃ₐ[A] A) τ

omit [FiniteDimensional K L] [IsGalois K L] in
theorem conj_tmul (τ : L ≃ₐ[K] L) (a : A) (l : L) : conj A τ (a ⊗ₜ[K] l) = a ⊗ₜ[K] τ l := by
  simp [Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.map_tmul]

private theorem _root_.R3HC1.main (z : A ⊗[K] L) :
    algebraMap A (A ⊗[K] L) (Algebra.norm A z) = ∏ τ : L ≃ₐ[K] L, conj A τ z := by
  classical

  let ι := Module.Free.ChooseBasisIndex K L
  let b : Module.Basis ι K L := Module.Free.chooseBasis K L
  let bA : Module.Basis ι A (A ⊗[K] L) := Algebra.TensorProduct.basis A b

  have hcard : Fintype.card (L ≃ₐ[K] L) = Fintype.card ι := by
    rw [← Module.finrank_eq_card_basis b, ← IsGalois.card_aut_eq_finrank, Nat.card_eq_fintype_card]
  let e : (L ≃ₐ[K] L) ≃ ι := Fintype.equivOfCardEq hcard

  let jR : L →+* A ⊗[K] L := (Algebra.TensorProduct.includeRight : L →ₐ[K] A ⊗[K] L).toRingHom
  let jL : A →+* A ⊗[K] L := algebraMap A (A ⊗[K] L)
  have jL_apply : ∀ a : A, jL a = a ⊗ₜ[K] (1 : L) := fun a => rfl
  have jR_apply : ∀ l : L, jR l = (1 : A) ⊗ₜ[K] l := fun l => rfl

  let M : Matrix ι ι A := Algebra.leftMulMatrix bA z
  let P : Matrix ι ι L := fun i j => (e.symm i) (b j)
  let P' : Matrix ι ι (A ⊗[K] L) := jR.mapMatrix P
  let M' : Matrix ι ι (A ⊗[K] L) := jL.mapMatrix M
  let d : ι → A ⊗[K] L := fun i => conj A (e.symm i) z

  have hcol : ∀ j : ι, ∑ k : ι, M k j ⊗ₜ[K] b k = z * ((1 : A) ⊗ₜ[K] b j) := by
    intro j
    have hrepr := bA.sum_repr (z * bA j)
    have hbA : ∀ k : ι, bA k = (1 : A) ⊗ₜ[K] b k := fun k => Algebra.TensorProduct.basis_apply b k
    simp only [hbA] at hrepr
    rw [← hrepr]
    refine Finset.sum_congr rfl fun k _ => ?_
    have hM : M k j = bA.repr (z * bA j) k := by
      simp only [M, Algebra.leftMulMatrix_apply, LinearMap.toMatrix_apply, Algebra.coe_lmul_eq_mul,
        LinearMap.mul_apply']
    rw [hM, hbA j, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  have hinter : P' * M' = Matrix.diagonal d * P' := by
    ext i j
    rw [Matrix.mul_apply, Matrix.diagonal_mul]
    have h1 : ∀ k : ι, P' i k * M' k j = conj A (e.symm i) (M k j ⊗ₜ[K] b k) := by
      intro k
      simp only [P', M', P, RingHom.mapMatrix_apply, Matrix.map_apply, jR_apply, jL_apply, conj_tmul,
        Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]
    simp only [h1]
    rw [← map_sum, hcol j, map_mul, conj_tmul]
    simp only [d, P', RingHom.mapMatrix_apply, Matrix.map_apply, jR_apply, P]

  have hdetM' : M'.det = jL (Algebra.norm A z) := by
    rw [Algebra.norm_eq_matrix_det bA z, RingHom.map_det]
  have hdetD : (Matrix.diagonal d).det = ∏ τ : L ≃ₐ[K] L, conj A τ z := by
    rw [Matrix.det_diagonal]
    exact Fintype.prod_equiv e.symm _ _ fun i => rfl

  have hPtP : Pᵀ * P = (algebraMap K L).mapMatrix (Algebra.traceMatrix K b) := by
    ext i j
    rw [Matrix.mul_apply, RingHom.mapMatrix_apply, Matrix.map_apply, Algebra.traceMatrix_apply,
      Algebra.traceForm_apply, trace_eq_sum_automorphisms]
    rw [← Fintype.sum_equiv e.symm (fun k => Pᵀ i k * P k j) (fun τ => τ (b i * b j))]
    intro k
    simp only [Matrix.transpose_apply, P, map_mul]
  have hdetP : IsUnit P.det := by
    rw [isUnit_iff_ne_zero]
    intro h0
    have h2 : (Pᵀ * P).det = 0 := by rw [Matrix.det_mul, Matrix.det_transpose, h0, mul_zero]
    rw [hPtP, ← RingHom.map_det, ← Algebra.discr_def] at h2
    exact Algebra.discr_not_zero_of_basis K b ((map_eq_zero _).mp h2)
  have hdetP' : IsUnit P'.det := by
    have : P'.det = jR P.det := (RingHom.map_det jR P).symm
    rw [this]; exact hdetP.map _

  have hdet := congrArg Matrix.det hinter
  rw [Matrix.det_mul, Matrix.det_mul, hdetM', hdetD, mul_comm] at hdet
  exact hdetP'.mul_left_injective hdet

p2m_export "R3HC1" "main"
end R3HC1

namespace R3Gen

open NumberField IsDedekindDomain M4aHerbrand M4aHerbrand.Bridge M4aHerbrand.GenuineDescent

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

local notation "𝔸K" => AdeleRing (𝓞 K) K
local notation "𝔸L" => AdeleRing (𝓞 L) L

@[reducible] noncomputable def instAlg : Algebra (AdeleRing (𝓞 K) K) (AdeleRing (𝓞 L) L) :=
  (genuineβ K L).toAlgebra

attribute [local instance] instAlg

theorem algebraMap_adele_injective : Function.Injective (algebraMap L (𝔸L)) := by
  intro x y h
  obtain ⟨w⟩ := (inferInstance : Nonempty (InfinitePlace L))
  have h1 := congrArg (fun z : 𝔸L => z.1 w) h
  exact (algebraMap L w.Completion).injective h1

noncomputable def te : ((AdeleRing (𝓞 K) K) ⊗[K] L) ≃ₐ[AdeleRing (𝓞 K) K] AdeleRing (𝓞 L) L :=
  genuineTensorEquiv K L

theorem te_tmul_one (x : 𝔸K) : te K L (x ⊗ₜ[K] (1 : L)) = genuineβ K L x :=
  genuineTensorEquiv_tmul_one K L x

theorem te_one_tmul (l : L) : te K L ((1 : 𝔸K) ⊗ₜ[K] l) = algebraMap L (𝔸L) l :=
  genuineTensorEquiv_one_tmul K L l

theorem algebraMap_eq_β (x : 𝔸K) : algebraMap (𝔸K) (𝔸L) x = genuineβ K L x := rfl

theorem act_apply (τ : L ≃ₐ[K] L) (x : 𝔸L) :
    (genuineDescentDatum K L).act τ x = te K L (R3HC1.conj (𝔸K) τ ((te K L).symm x)) := rfl

theorem unitsAct_val (τ : L ≃ₐ[K] L) (u : (𝔸L)ˣ) :
    (((genuineDescentDatum K L).unitsAct τ u : (𝔸L)ˣ) : 𝔸L) = (genuineDescentDatum K L).act τ (u : 𝔸L) :=
  rfl

theorem β_injective : Function.Injective (genuineβ K L) := by
  have h1 : Function.Injective
      (Algebra.TensorProduct.includeLeft : 𝔸K →ₐ[𝔸K] (𝔸K) ⊗[K] L) :=
    Algebra.TensorProduct.includeLeft_injective (S := 𝔸K) (algebraMap K L).injective
  intro x y hxy
  apply h1
  apply (te K L).injective
  change te K L (x ⊗ₜ[K] (1 : L)) = te K L (y ⊗ₜ[K] (1 : L))
  rw [te_tmul_one, te_tmul_one, hxy]

theorem act_β (τ : L ≃ₐ[K] L) (x : 𝔸K) :
    (genuineDescentDatum K L).act τ (genuineβ K L x) = genuineβ K L x := by
  rw [act_apply, ← te_tmul_one, AlgEquiv.symm_apply_apply, R3HC1.conj_tmul, map_one]

variable [IsGalois K L]

theorem sum_conj_mem_range (y : (𝔸K) ⊗[K] L) :
    ∑ τ : L ≃ₐ[K] L, R3HC1.conj (𝔸K) τ y ∈ Set.range (fun a : 𝔸K => a ⊗ₜ[K] (1 : L)) := by
  induction y using TensorProduct.induction_on with
  | zero => exact ⟨0, by simp⟩
  | tmul a l =>
    refine ⟨Algebra.trace K L l • a, ?_⟩
    simp only [R3HC1.conj_tmul]
    rw [← TensorProduct.tmul_sum, ← trace_eq_sum_automorphisms, Algebra.algebraMap_eq_smul_one,
      TensorProduct.tmul_smul, TensorProduct.smul_tmul']
  | add y₁ y₂ h₁ h₂ =>
    obtain ⟨a₁, ha₁⟩ := h₁
    obtain ⟨a₂, ha₂⟩ := h₂
    refine ⟨a₁ + a₂, ?_⟩
    simp only [map_add, Finset.sum_add_distrib, ← ha₁, ← ha₂, TensorProduct.add_tmul]

theorem exists_eq_tmul_one_of_forall_conj_eq (z : (𝔸K) ⊗[K] L)
    (hz : ∀ τ : L ≃ₐ[K] L, R3HC1.conj (𝔸K) τ z = z) : ∃ a : 𝔸K, z = a ⊗ₜ[K] (1 : L) := by
  haveI : Algebra.IsSeparable K L := IsGalois.to_isSeparable
  obtain ⟨d, hd⟩ := Algebra.trace_surjective K L 1

  have hsum : z = ∑ τ : L ≃ₐ[K] L, R3HC1.conj (𝔸K) τ (z * ((1 : 𝔸K) ⊗ₜ[K] d)) := by
    have h1 : ∀ τ : L ≃ₐ[K] L, R3HC1.conj (𝔸K) τ (z * ((1 : 𝔸K) ⊗ₜ[K] d)) =
        z * ((1 : 𝔸K) ⊗ₜ[K] τ d) := by
      intro τ; rw [map_mul, hz τ, R3HC1.conj_tmul]
    simp only [h1]
    rw [← Finset.mul_sum, ← TensorProduct.tmul_sum, ← trace_eq_sum_automorphisms, hd, map_one]
    exact (mul_one z).symm
  obtain ⟨a, ha⟩ := sum_conj_mem_range K L (z * ((1 : 𝔸K) ⊗ₜ[K] d))
  exact ⟨a, hsum.trans ha.symm⟩

theorem forall_unitsAct_eq_iff (u : (𝔸L)ˣ) :
    (∀ τ : L ≃ₐ[K] L, (genuineDescentDatum K L).unitsAct τ u = u) ↔
      u ∈ (Units.map (genuineβ K L).toMonoidHom).range := by
  constructor
  · intro hu

    have hval : ∀ w : (𝔸L)ˣ, (∀ τ : L ≃ₐ[K] L, (genuineDescentDatum K L).unitsAct τ w = w) →
        ∃ a : 𝔸K, (w : 𝔸L) = genuineβ K L a := by
      intro w hw
      have hz : ∀ τ : L ≃ₐ[K] L, R3HC1.conj (𝔸K) τ ((te K L).symm (w : 𝔸L)) = (te K L).symm (w : 𝔸L) := by
        intro τ
        have h := congrArg (fun v : (𝔸L)ˣ => (v : 𝔸L)) (hw τ)
        simp only [unitsAct_val, act_apply] at h
        apply (te K L).injective
        rw [h, AlgEquiv.apply_symm_apply]
      obtain ⟨a, ha⟩ := exists_eq_tmul_one_of_forall_conj_eq K L _ hz
      refine ⟨a, ?_⟩
      rw [← te_tmul_one, ← ha, AlgEquiv.apply_symm_apply]
    have hu' : ∀ τ : L ≃ₐ[K] L, (genuineDescentDatum K L).unitsAct τ u⁻¹ = u⁻¹ := by
      intro τ; rw [map_inv, hu τ]
    obtain ⟨a, ha⟩ := hval u hu
    obtain ⟨a', ha'⟩ := hval u⁻¹ hu'
    have h1 : a * a' = 1 := by
      apply β_injective K L
      rw [map_mul, ← ha, ← ha', map_one, ← Units.val_mul, mul_inv_cancel, Units.val_one]
    have h2 : a' * a = 1 := by rw [mul_comm]; exact h1
    exact ⟨⟨a, a', h1, h2⟩, Units.ext ha.symm⟩
  · rintro ⟨x, rfl⟩ τ
    exact Units.ext (act_β K L τ x)

theorem mem_sup_of_forall_twist_principal (u : (𝔸L)ˣ)
    (hu : ∀ τ : L ≃ₐ[K] L, ((genuineDescentDatum K L).unitsAct τ u)⁻¹ * u ∈ principalIdeles (𝓞 L) L) :
    u ∈ (Units.map (genuineβ K L).toMonoidHom).range ⊔ principalIdeles (𝓞 L) L := by
  set D := genuineDescentDatum K L with hD
  set ι : Lˣ →* (𝔸L)ˣ := Units.map (algebraMap L (𝔸L) : L →* 𝔸L) with hι
  have hιinj : Function.Injective ι := by
    intro x y hxy
    have h := congrArg (fun v : (𝔸L)ˣ => (v : 𝔸L)) hxy
    exact Units.ext (algebraMap_adele_injective L h)
  have hιact : ∀ (τ : L ≃ₐ[K] L) (c : Lˣ), D.unitsAct τ (ι c) = ι (τ • c) := by
    intro τ c
    refine Units.ext ?_
    rw [unitsAct_val]
    exact D.compat τ (c : L)

  choose lam hlam using fun τ => (hu τ : ∃ c : Lˣ, ι c = (D.unitsAct τ u)⁻¹ * u)
  have hcoc : groupCohomology.IsMulCocycle₁ lam := by
    intro g h
    apply hιinj
    rw [map_mul, ← hιact, hlam, hlam, hlam, map_mul (D.unitsAct), MulAut.mul_apply, map_mul, map_inv]

    group
  obtain ⟨b, hb⟩ := groupCohomology.isMulCoboundary₁_of_isMulCocycle₁_of_aut_to_units lam hcoc

  have hfix : ∀ τ : L ≃ₐ[K] L, D.unitsAct τ (u * ι b) = u * ι b := by
    intro τ
    have h1 : ι (τ • b) = ι b * ((D.unitsAct τ u)⁻¹ * u) := by
      rw [← hlam τ, ← map_mul, ← hb τ, div_eq_mul_inv, mul_comm (τ • b) b⁻¹, ← mul_assoc,
        mul_inv_cancel, one_mul]
    rw [map_mul, hιact, h1, mul_left_comm, mul_inv_cancel_left, mul_comm]
  have hw : u * ι b ∈ (Units.map (genuineβ K L).toMonoidHom).range :=
    (forall_unitsAct_eq_iff K L _).mp hfix
  have hb' : (ι b)⁻¹ ∈ principalIdeles (𝓞 L) L := inv_mem ⟨b, rfl⟩
  have : u = (u * ι b) * (ι b)⁻¹ := by rw [mul_inv_cancel_right]
  rw [this]
  exact Subgroup.mul_mem_sup hw hb'

theorem prod_unitsAct_eq (u : (𝔸L)ˣ) :
    ∏ τ : L ≃ₐ[K] L, (genuineDescentDatum K L).unitsAct τ u =
      Units.map (genuineβ K L).toMonoidHom ((genuineBaseChange K L).idelicNorm u) := by
  refine Units.ext ?_
  rw [Units.coe_prod]
  simp only [unitsAct_val, act_apply]
  rw [← map_prod, ← R3HC1.main, Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self,
    RingHom.id_apply, te_tmul_one]

  change genuineβ K L (Algebra.norm (𝔸K) ((te K L).symm (u : 𝔸L))) =
    genuineβ K L (Algebra.norm (𝔸K) (u : 𝔸L))
  rw [Algebra.norm_eq_of_algEquiv]

omit [IsGalois K L] in

theorem idelicNorm_unitsAct (τ : L ≃ₐ[K] L) (u : (𝔸L)ˣ) :
    (genuineBaseChange K L).idelicNorm ((genuineDescentDatum K L).unitsAct τ u) =
      (genuineBaseChange K L).idelicNorm u := by
  refine Units.ext ?_
  change Algebra.norm (𝔸K) ((genuineDescentDatum K L).act τ (u : 𝔸L)) = Algebra.norm (𝔸K) (u : 𝔸L)
  rw [act_apply, Algebra.norm_eq_of_algEquiv, Algebra.norm_eq_of_algEquiv, Algebra.norm_eq_of_algEquiv]

omit [IsGalois K L] in

theorem idelicNorm_principal
    (hN : ∀ m : L, (genuineBaseChange K L).adelicNorm (algebraMap L (𝔸L) m) =
      algebraMap K (𝔸K) (Algebra.norm K m)) (b : Lˣ) :
    (((genuineBaseChange K L).idelicNorm (Units.map (algebraMap L (𝔸L) : L →* 𝔸L) b) : (𝔸K)ˣ) : 𝔸K)
      = algebraMap K (𝔸K) (Algebra.norm K (b : L)) :=
  hN b

end R3Gen

namespace R3HC3

open NumberField IsDedekindDomain M4aHerbrand M4aHerbrand.Bridge M4aHerbrand.GenuineDescent

private theorem _root_.R3HC3.main (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [IsGalois K L] (D : IdeleGaloisDescent (𝓞 L) K L)
    (σ : L ≃ₐ[K] L) (hσ : ∀ τ, τ ∈ Subgroup.zpowers σ) :
    (ideleClassNorm D).ker = (ideleClassDerive D σ).range := by
  classical
  haveI : IsCyclic (L ≃ₐ[K] L) := ⟨⟨σ, hσ⟩⟩

  haveI := M4aHerbrand.subsingleton_ideleGaloisDescent (𝓞 L) K L
  obtain rfl : D = genuineDescentDatum K L := Subsingleton.elim _ _
  set D := genuineDescentDatum K L with hD
  refine le_antisymm ?_ ?_
  swap
  ·
    rintro _ ⟨c, rfl⟩
    rw [MonoidHom.mem_ker]
    change ideleClassNorm D (D.classAct σ c * c⁻¹) = 1
    rw [map_mul, map_inv, mul_inv_eq_one]
    simp only [ideleClassNorm, MonoidHom.coe_mk, OneHom.coe_mk, ← IdeleGaloisDescent.classAct_mul]
    exact @Fintype.prod_equiv _ _ _ (Fintype.ofFinite _) (Fintype.ofFinite _) _ (Equiv.mulRight σ)
      (fun τ => D.classAct (τ * σ) c) (fun τ => D.classAct τ c) fun τ => rfl

  set B := genuineBaseChange K L with hB
  set H : Subgroup (AdeleRing (𝓞 K) K)ˣ := principalIdeles (𝓞 K) K ⊔ B.idelicNorm.range with hH
  have hn : Module.finrank K L ≠ 0 := Module.finrank_pos.ne'

  have h2 : H.index ∣ Module.finrank K L := NumberField.ideleClass_normCoset_index_dvd_finrank K L
  have h1 := M4aHerbrand.ideleClass_normCoset_index_ne_zero_and_finrank_dvd K L B
  have hidx : H.index = Module.finrank K L := Nat.dvd_antisymm h2 h1.2

  have htate := M4aHerbrand.idelicNormCoset_index_eq_ideleClassTateCard K L D (genuineβ K L)
    B.idelicNorm σ hσ (genuineβ_compat K L) (R3Gen.β_injective K L)
    (R3Gen.forall_unitsAct_eq_iff K L) (R3Gen.mem_sup_of_forall_twist_principal K L)
    (R3Gen.prod_unitsAct_eq K L)

  have hherb := M4aHerbrand.ideleClass_herbrandQuotient_eq_finrank K L D σ hσ
  have hcard : Nat.card ((ideleClassNorm D).ker ⧸
      ((ideleClassDerive D σ).range.subgroupOf (ideleClassNorm D).ker)) = 1 := by
    have h := hherb.1
    rw [← htate, ← hH, hidx] at h

    have := Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hn) (h.symm.trans (mul_one _).symm)
    exact this

  intro c hc
  obtain ⟨x0, hx0⟩ := Nat.card_eq_one_iff_exists.mp hcard
  have hq : (QuotientGroup.mk (⟨c, hc⟩ : (ideleClassNorm D).ker) :
      (ideleClassNorm D).ker ⧸ ((ideleClassDerive D σ).range.subgroupOf (ideleClassNorm D).ker)) =
      QuotientGroup.mk 1 := by
    rw [hx0 (QuotientGroup.mk _), hx0 (QuotientGroup.mk 1)]
  rw [QuotientGroup.eq, mul_one, Subgroup.mem_subgroupOf] at hq
  simpa using (Subgroup.inv_mem_iff _).mp hq

p2m_export "R3HC3" "main"
end R3HC3

theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (D : M4aHerbrand.IdeleGaloisDescent (NumberField.RingOfIntegers L) K L) (σ : L ≃ₐ[K] L)
    (hσ : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ) :
    (M4aHerbrand.ideleClassNorm D).ker = (M4aHerbrand.ideleClassDerive D σ).range :=
  R3HC3.main K L D σ hσ

end S_NumberField_ideleClassNorm_ker_eq_ideleClassDerive_range
end P2MW
export P2MW.S_NumberField_ideleClassNorm_ker_eq_ideleClassDerive_range (solution)
