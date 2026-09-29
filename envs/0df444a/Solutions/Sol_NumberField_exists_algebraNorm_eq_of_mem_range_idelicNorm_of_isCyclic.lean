-- Prove2me | solution 1 for NumberField.exists_algebraNorm_eq_of_mem_range_idelicNorm_of_isCyclic
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/93dd5a3c-d31b-5bdd-b5aa-6b99d3806870

import Mathlib
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Theorems.Thm_M4aHerbrand_GenuineDescent_adelicNorm_genuineBaseChange_algebraMap
import Theorems.Thm_NumberField_ideleClassNorm_ker_eq_ideleClassDerive_range
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_exists_algebraNorm_eq_of_mem_range_idelicNorm_of_isCyclic
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

variable [IsGalois K L]

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

end R3Gen

namespace R3H

open NumberField IsDedekindDomain M4aHerbrand M4aHerbrand.Bridge M4aHerbrand.GenuineDescent

private theorem _root_.R3H.main (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [IsCyclic (L ≃ₐ[K] L)]
    (a : Kˣ)
    (ha : Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) a ∈
      (M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm.range) :
    ∃ b : L, Algebra.norm K b = (a : K) := by
  classical
  obtain ⟨σ, hσ⟩ := IsCyclic.exists_generator (α := L ≃ₐ[K] L)
  set D := genuineDescentDatum K L with hD
  set B := genuineBaseChange K L with hB
  obtain ⟨x, hx⟩ := ha

  have hker : (QuotientGroup.mk x : IdeleClassGroup (𝓞 L) L) ∈ (ideleClassNorm D).ker := by
    rw [MonoidHom.mem_ker]
    simp only [ideleClassNorm, MonoidHom.coe_mk, OneHom.coe_mk, IdeleGaloisDescent.classAct_mk]
    rw [← QuotientGroup.mk_prod, QuotientGroup.eq_one_iff]
    have hprod : (letI := Fintype.ofFinite (L ≃ₐ[K] L); ∏ τ : L ≃ₐ[K] L, D.unitsAct τ x) =
        Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)
          (Units.map (algebraMap K L : K →* L) a) := by
      have h := R3Gen.prod_unitsAct_eq K L x
      rw [← hB, hx] at h
      refine (Finset.prod_congr (by ext; simp) fun τ _ => rfl).trans (h.trans ?_)
      exact Units.ext (genuineβ_compat K L (a : K))
    rw [hprod]
    exact ⟨_, rfl⟩

  rw [NumberField.ideleClassNorm_ker_eq_ideleClassDerive_range K L D σ hσ] at hker
  obtain ⟨c, hc⟩ := hker
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective c
  change D.classAct σ (QuotientGroup.mk y) * (QuotientGroup.mk y)⁻¹ = QuotientGroup.mk x at hc
  rw [IdeleGaloisDescent.classAct_mk, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul,
    QuotientGroup.eq] at hc
  obtain ⟨b, hb⟩ := hc

  have hxeq : x = D.unitsAct σ y * y⁻¹ * Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* _) b := by
    rw [hb, mul_inv_cancel_left]
  have hN : B.idelicNorm x = B.idelicNorm (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* _) b) := by
    rw [hxeq, map_mul, map_mul, map_inv, R3Gen.idelicNorm_unitsAct, mul_inv_cancel, one_mul]
  refine ⟨(b : L), ?_⟩
  have hval := congrArg (fun u : (AdeleRing (𝓞 K) K)ˣ => (u : AdeleRing (𝓞 K) K)) (hx.symm.trans hN)
  simp only [Units.coe_map, MonoidHom.coe_coe] at hval
  change algebraMap K (AdeleRing (𝓞 K) K) (a : K) =
    B.adelicNorm (algebraMap L (AdeleRing (𝓞 L) L) (b : L)) at hval
  rw [hB, adelicNorm_genuineBaseChange_algebraMap] at hval
  exact (R3Gen.algebraMap_adele_injective K hval).symm

p2m_export "R3H" "main"
end R3H

theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [IsCyclic (L ≃ₐ[K] L)]
    (a : Kˣ)
    (ha : Units.map (algebraMap K (NumberField.AdeleRing (NumberField.RingOfIntegers K) K) :
        K →* NumberField.AdeleRing (NumberField.RingOfIntegers K) K) a ∈
      (M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm.range) :
    ∃ b : L, Algebra.norm K b = (a : K) :=
  R3H.main K L a ha

end S_NumberField_exists_algebraNorm_eq_of_mem_range_idelicNorm_of_isCyclic
end P2MW
export P2MW.S_NumberField_exists_algebraNorm_eq_of_mem_range_idelicNorm_of_isCyclic (solution)
