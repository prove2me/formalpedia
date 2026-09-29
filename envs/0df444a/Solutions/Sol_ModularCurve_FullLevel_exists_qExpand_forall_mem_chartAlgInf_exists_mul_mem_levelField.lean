-- Prove2me | solution 1 for ModularCurve.FullLevel.exists_qExpand_forall_mem_chartAlgInf_exists_mul_mem_levelField
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.339302+00:00
-- url     : https://prove2.me/submissions/f17519b9-a156-5262-9ce5-06a808b3f6d1

import Definitions.Def_ModularCurve_FullLevelSemistableCovering
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_AlgebraicCurve_ConstantReduction
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_GaloisRep_TameCharacter
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_AlgebraicCurve_ResidueDiscs
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_CoeffSemilinearAut
import Mathlib
import Theorems.Thm_ModularCurve_FullLevel_exists_finite_subgroup_forall_levelAutBar_mem
import Theorems.Thm_ModularCurve_FullLevel_levelAutBar_apply_eq_self_of_coe_eq_qExpand_of_mem_laurentBaseChange_gamma0
import Theorems.Thm_ModularCurve_FullLevel_qExpand_coe_mem_fieldBar_of_mem
import Theorems.Thm_ModularCurve_qExpFunctionFieldC_rat_gamma0_eq_modularFunctionFieldFull
import Theorems.Thm_ModularCurve_FullLevel_exists_ringEquiv_laurentBaseChange_levelField_coe_eq_coeffMap
import Theorems.Thm_ModularCurve_mem_chartAlgFin_and_forall_mem_chartAlgInf_exists_mul_mem_of_coe_eq_coeffEmb_jq_qExpand_of_one_lt
import Definitions.Def_ModularCurve_PhiGen
import Theorems.Thm_ModularCurve_exists_modularPolynomialData_evalSymm
import Theorems.Thm_ModularCurve_FullLevel_exists_qExpand_mem_chartAlgFin_and_forall_mem_closure_levelAutBar_exists_algEquiv_levelField
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_exists_qExpand_forall_mem_chartAlgInf_exists_mul_mem_levelField
p2m_attr_erase "instance" "ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt"
p2m_attr_erase "simp" "ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.qExpandAlgHomC_apply ModularCurve.ProjectiveLine.map_mk ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ"

set_option autoImplicit false

p2m_open "CategoryTheory AlgebraicGeometry AlgebraicCurve ModularCurve~coeffMap_injective ModularCurve.FullLevel IsLocalRing CongruenceSubgroup"
open scoped MatrixGroups

namespace TH1AuxIg

section Closure

variable {G : Type*} [Group G]

theorem forall_mem_closure_of_generators (s : Set G) (p : G → Prop)
    (h1 : p 1) (hmul : ∀ x y, p x → p y → p (x * y))
    (hgen : ∀ x ∈ s, p x) (hfin : ∀ x ∈ s, IsOfFinOrder x) :
    ∀ g ∈ Subgroup.closure s, p g := by
  have hpow : ∀ x, p x → ∀ n : ℕ, p (x ^ n) := by
    intro x hx n
    induction n with
    | zero => simpa using h1
    | succ n ih => rw [pow_succ]; exact hmul _ _ ih hx
  intro g hg
  induction hg using Subgroup.closure_induction'' with
  | mem x hx => exact hgen x hx
  | inv_mem x hx =>
      have h := hfin x hx
      have : x⁻¹ = x ^ (orderOf x - 1) := by
        rw [eq_comm, ← mul_eq_one_iff_eq_inv, ← pow_succ, tsub_add_cancel_of_le (by exact h.orderOf_pos),
          pow_orderOf_eq_one]
      rw [this]
      exact hpow x (hgen x hx) _
  | one => exact h1
  | mul x y _ _ hx hy => exact hmul x y hx hy

end Closure

section Comap

theorem mem_nonunits_comap_iff
    {F : Type} [Field F] (V : ValuationSubring F) (g : F ≃+* F) (f : F) :
    f ∈ (V.comap g.toRingHom).nonunits ↔ g f ∈ V.nonunits := by
  rw [ValuationSubring.mem_nonunits_iff_or, ValuationSubring.mem_nonunits_iff_or, ValuationSubring.mem_comap,
    RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, map_inv₀, map_eq_zero_iff _ g.injective]

theorem mem_comap_iff'
    {F : Type} [Field F] (V : ValuationSubring F) (g : F ≃+* F) (f : F) :
    f ∈ V.comap g.toRingHom ↔ g f ∈ V :=
  ValuationSubring.mem_comap

end Comap

section W1

theorem closure_comap_igusaRing_perm
    (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M']
    (OIg : CuspidalType.ProjLine q → ValuationSubring ↥(fieldBar q M'))
    (hIg_perm : ∀ (ζ' : Idx q) (γ : SL(2, ℤ)), γ ∈ Gamma0 M' →
      ∃ σ : Equiv.Perm (CuspidalType.ProjLine q),
        ∀ ℓ, (OIg ℓ).comap (levelAutBar q M' ζ' γ).toAlgHom.toRingHom = OIg (σ ℓ))
    (g : ↥(fieldBar q M') ≃ₐ[AlgebraicClosure ℚ] ↥(fieldBar q M'))
    (hg : g ∈ Subgroup.closure {τ : ↥(fieldBar q M') ≃ₐ[AlgebraicClosure ℚ] ↥(fieldBar q M') | ∃ (ζ : Idx q) (γ : SL(2, ℤ)), γ ∈ Gamma0 M' ∧ τ = levelAutBar q M' ζ γ}) :
    ∃ σ : Equiv.Perm (CuspidalType.ProjLine q), ∀ ℓ, (OIg ℓ).comap g.toAlgHom.toRingHom = OIg (σ ℓ) := by
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
      obtain ⟨ζ', γ, hγ, rfl⟩ := hx
      exact hIg_perm ζ' γ hγ
  | one => exact ⟨1, fun i => by ext f; rfl⟩
  | mul x y _ _ hx hy =>
      obtain ⟨σ, hσ⟩ := hx
      obtain ⟨ρ, hρ⟩ := hy
      refine ⟨ρ * σ, fun i => ?_⟩
      have : (OIg i).comap (x * y).toAlgHom.toRingHom =
          ((OIg i).comap x.toAlgHom.toRingHom).comap y.toAlgHom.toRingHom := by
        ext f; rfl
      rw [this, hσ, hρ, Equiv.Perm.mul_apply]
  | inv x _ hx =>
      obtain ⟨σ, hσ⟩ := hx
      refine ⟨σ⁻¹, fun i => ?_⟩
      have h := hσ (σ⁻¹ i)
      rw [show σ (σ⁻¹ i) = i from by simp] at h
      have : ((OIg (σ⁻¹ i)).comap x.toAlgHom.toRingHom).comap x⁻¹.toAlgHom.toRingHom = OIg (σ⁻¹ i) := by
        ext f
        show x (x⁻¹ f) ∈ OIg (σ⁻¹ i) ↔ f ∈ OIg (σ⁻¹ i)
        rw [show x (x⁻¹ f) = f from by simp]
      rw [← this, h]

end W1

section W4

open AlgebraicCurve.TwoChartIntegralModel in

theorem isIntegral_adjoin_map' {A : Type*} [CommRing A] {K K' : Type*} [Field K] [Field K'] [Algebra A K] [Algebra A K']
    (τ : K →ₐ[A] K') (t b : K) (hb : IsIntegral (Algebra.adjoin A ({t} : Set K)) b) :
    IsIntegral (Algebra.adjoin A ({τ t} : Set K')) (τ b) := by
  have hmap : (Algebra.adjoin A ({t} : Set K)).map τ = Algebra.adjoin A {τ t} := by
    rw [AlgHom.map_adjoin, Set.image_singleton]
  let φ : Algebra.adjoin A ({t} : Set K) →+* Algebra.adjoin A ({τ t} : Set K') :=
    { toFun := fun s => ⟨τ s, by rw [← hmap]; exact Subalgebra.mem_map.mpr ⟨s, s.2, rfl⟩⟩
      map_one' := by ext; simp
      map_mul' := fun a b => by ext; simp
      map_zero' := by ext; simp
      map_add' := fun a b => by ext; simp }
  exact hb.map_of_comp_eq φ τ.toRingHom (by ext s; rfl)

theorem mem_chartAlgInf_iff_of_algEquiv {A : Type} [CommRing A] {K K' : Type} [Field K] [Field K'] [Algebra A K]
    [Algebra A K'] (φ : K ≃ₐ[A] K') (t : K) (t' : K') (ht : φ t = t') (y : K) :
    y ∈ AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A K t ↔
      φ y ∈ AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A K' t' := by
  subst ht
  rw [AlgebraicCurve.TwoChartIntegralModel.mem_chartAlg_iff, AlgebraicCurve.TwoChartIntegralModel.mem_chartAlg_iff]
  constructor
  · intro h
    have := isIntegral_adjoin_map' (φ : K →ₐ[A] K') t⁻¹ y h
    rwa [AlgEquiv.coe_algHom, map_inv₀] at this
  · intro h
    have := isIntegral_adjoin_map' (φ.symm : K' →ₐ[A] K) (φ t)⁻¹ (φ y) h
    rwa [AlgEquiv.coe_algHom, map_inv₀, AlgEquiv.symm_apply_apply, AlgEquiv.symm_apply_apply] at this

theorem coeffMap_injective {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (hf : Function.Injective f) :
    Function.Injective (coeffMap f) := by
  intro x y h
  ext k
  apply hf
  have := congrArg (fun s => HahnSeries.coeff s k) h
  simpa [coeffMap_coeff] using this

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 12800000 in

theorem poleChart_bridge
    (q : ℕ) [Fact q.Prime] (hq : 5 ≤ q) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (hle : modularFunctionFieldBar M' ≤ fieldBar q M')
    (k₀ : IntermediateField ℚ (AlgebraicClosure ℚ))
    (K₁ : IntermediateField ↥k₀ (AlgebraicClosure ℚ)) (hK₁ : FiniteDimensional ↥k₀ ↥K₁)
    (A₁ : ValuationSubring ↥K₁) :
    letI : Algebra ↥k₀ ↥(fieldBar q M') :=
      ((algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')).comp (algebraMap ↥k₀ (AlgebraicClosure ℚ))).toAlgebra
    ∀ (F₀ : IntermediateField ↥k₀ ↥(fieldBar q M')),
      (IntermediateField.adjoin ↥k₀ (Set.range (algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M'))) ⊔ F₀ = ⊤) →
      (∀ (K' : IntermediateField ↥k₀ (AlgebraicClosure ℚ)), FiniteDimensional ↥k₀ ↥K' →
        ∀ (m : ℕ) (c : Fin m → AlgebraicClosure ℚ) (a : Fin m → ↥(fieldBar q M')), (∀ i, a i ∈ IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K' : Set (AlgebraicClosure ℚ))) ⊔ F₀) →
          LinearIndependent ↥K' c → ∑ i, algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') (c i) * a i = 0 → ∀ i, a i = 0) →
      (∀ f : ↥(fieldBar q M'), (f : LaurentSeries (AlgebraicClosure ℚ)) ∈ Set.range ⇑(coeffEmb (AlgebraicClosure ℚ)) → f ∈ F₀) →
    ∀ [Algebra ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀)],
      (∀ a : ↥A₁, ((algebraMap ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) a : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀)) : ↥(fieldBar q M')) =
        algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') ((a : ↥K₁) : AlgebraicClosure ℚ)) →
    ∀ (j₁ : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀)),
      ((j₁ : ↥(fieldBar q M')) = IntermediateField.inclusion hle (⟨coeffEmb (AlgebraicClosure ℚ) jq,
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ : ↥(modularFunctionFieldBar M'))) →
    ∀ [Fact (j₁ ≠ 0)],
    ∀ (j' : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀)),
      ((j' : ↥(fieldBar q M')) : LaurentSeries (AlgebraicClosure ℚ)) = coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ q jq) →
    (∀ c, c ∈ TwoChartIntegralModel.chartAlgInf ↥A₁ _ j' →
      ∃ s, s ∈ TwoChartIntegralModel.chartAlgInf ↥A₁ _ j₁ ∧
        (∃ a, a ∈ TwoChartIntegralModel.chartAlgInf ↥A₁ _ j₁ ∧ s = 1 + j₁⁻¹ * a) ∧
        s * c ∈ TwoChartIntegralModel.chartAlgInf ↥A₁ _ j₁) ∧
    (∀ c, c ∈ TwoChartIntegralModel.chartAlgInf ↥A₁ _ j₁ →
      ∃ s, s ∈ TwoChartIntegralModel.chartAlgInf ↥A₁ _ j' ∧
        (∃ a, a ∈ TwoChartIntegralModel.chartAlgInf ↥A₁ _ j' ∧ s = 1 + j'⁻¹ * a) ∧
        s * c ∈ TwoChartIntegralModel.chartAlgInf ↥A₁ _ j')  := by
  intro F₀ hK1 hLD hRAT instA halg j₁ hj₁ instj₁ j' hj'
  haveI : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
  have hq1 : 1 < q := (Fact.out : q.Prime).one_lt
  obtain ⟨e, he⟩ := ModularCurve.FullLevel.exists_ringEquiv_laurentBaseChange_levelField_coe_eq_coeffMap q M' k₀ K₁ hK₁
    F₀ hK1 (hLD K₁ hK₁) hRAT
  letI algAK : Algebra ↥A₁ ↥(laurentBaseChange ↥K₁ (xHFunctionField (q ^ 2 * M') (levelH q M'))) := ((algebraMap ↥K₁ ↥(laurentBaseChange ↥K₁ (xHFunctionField (q ^ 2 * M') (levelH q M')))).comp (algebraMap ↥A₁ ↥K₁)).toAlgebra
  haveI hsc : @IsScalarTower ↥A₁ ↥K₁ ↥(laurentBaseChange ↥K₁ (xHFunctionField (q ^ 2 * M') (levelH q M'))) inferInstance inferInstance algAK.toSMul :=
    @IsScalarTower.of_algebraMap_eq ↥A₁ ↥K₁ ↥(laurentBaseChange ↥K₁ (xHFunctionField (q ^ 2 * M') (levelH q M'))) _ _ _ _ _ algAK (fun _ => rfl)
  have hι : Function.Injective (algebraMap ↥K₁ (AlgebraicClosure ℚ)) := fun a b h => Subtype.ext h
  have hιcomp : (algebraMap ↥K₁ (AlgebraicClosure ℚ)).comp (algebraMap ℚ ↥K₁) = algebraMap ℚ (AlgebraicClosure ℚ) :=
    Subsingleton.elim _ _
  have hcc : ∀ x : LaurentSeries ℚ, coeffMap (algebraMap ↥K₁ (AlgebraicClosure ℚ)) (coeffEmb ↥K₁ x) =
      coeffEmb (AlgebraicClosure ℚ) x := fun x => by
    show coeffMap (algebraMap ↥K₁ (AlgebraicClosure ℚ)) (coeffMap (algebraMap ℚ ↥K₁) x) = coeffMap (algebraMap ℚ (AlgebraicClosure ℚ)) x
    rw [coeffMap_coeffMap, hιcomp]

  have hecomm : ∀ a : ↥A₁, e (algebraMap ↥A₁ ↥(laurentBaseChange ↥K₁ (xHFunctionField (q ^ 2 * M') (levelH q M'))) a) = algebraMap ↥A₁ _ a := by
    intro a
    have h1 := halg a
    have h2 : ((algebraMap ↥A₁ ↥(laurentBaseChange ↥K₁ (xHFunctionField (q ^ 2 * M') (levelH q M'))) a : ↥(laurentBaseChange ↥K₁ (xHFunctionField (q ^ 2 * M') (levelH q M')))) : LaurentSeries ↥K₁) = HahnSeries.single 0 ((a : ↥K₁)) := by
      rw [← algebraMap_laurentSeries_eq_single]; rfl
    apply Subtype.ext
    apply Subtype.ext
    rw [he, h2, h1, coeffMap_single]
    show HahnSeries.single 0 ((a : ↥K₁) : AlgebraicClosure ℚ) = ((algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') ((a : ↥K₁) : AlgebraicClosure ℚ) : ↥(fieldBar q M')) : LaurentSeries (AlgebraicClosure ℚ))
    rw [← algebraMap_laurentSeries_eq_single]; rfl
  let eA : ↥(laurentBaseChange ↥K₁ (xHFunctionField (q ^ 2 * M') (levelH q M'))) ≃ₐ[↥A₁] _ := AlgEquiv.ofRingEquiv (f := e) hecomm
  have heA : ∀ f, eA f = e f := fun _ => rfl

  let jK : ↥(laurentBaseChange ↥K₁ (xHFunctionField (q ^ 2 * M') (levelH q M'))) := e.symm j₁
  let j'K : ↥(laurentBaseChange ↥K₁ (xHFunctionField (q ^ 2 * M') (levelH q M'))) := e.symm j'
  have hejK : e jK = j₁ := e.apply_symm_apply j₁
  have hej'K : e j'K = j' := e.apply_symm_apply j'
  have hj₁coe : (((j₁ : ↥(fieldBar q M')) : LaurentSeries (AlgebraicClosure ℚ))) = coeffEmb (AlgebraicClosure ℚ) jq := by
    rw [hj₁]; rfl
  have hqjq : qExpand ℚ q jq ≠ 0 := by
    intro h0
    have := congrArg (fun s => HahnSeries.coeff s ((q : ℤ) * (-1))) h0
    simp only [qExpand_coeff_mul, coeff_jq_neg_one] at this
    simp at this

  have hjKc : coeffMap (algebraMap ↥K₁ (AlgebraicClosure ℚ)) ((jK : ↥(laurentBaseChange ↥K₁ (xHFunctionField (q ^ 2 * M') (levelH q M')))) : LaurentSeries ↥K₁) =
      coeffEmb (AlgebraicClosure ℚ) jq := by rw [← he, hejK, hj₁coe]
  have hj'Kc : coeffMap (algebraMap ↥K₁ (AlgebraicClosure ℚ)) ((j'K : ↥(laurentBaseChange ↥K₁ (xHFunctionField (q ^ 2 * M') (levelH q M')))) : LaurentSeries ↥K₁) =
      coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ q jq) := by rw [← he, hej'K, hj']
  haveI : Fact (jK ≠ 0) := ⟨fun h0 => jq_ne_zero (coeffMap_injective (algebraMap ℚ (AlgebraicClosure ℚ))
    (algebraMap ℚ (AlgebraicClosure ℚ)).injective (by
      show coeffEmb (AlgebraicClosure ℚ) jq = coeffMap (algebraMap ℚ (AlgebraicClosure ℚ)) 0
      rw [← hjKc, h0, map_zero]; simp))⟩
  haveI : Fact (j'K ≠ 0) := ⟨fun h0 => hqjq (coeffMap_injective (algebraMap ℚ (AlgebraicClosure ℚ))
    (algebraMap ℚ (AlgebraicClosure ℚ)).injective (by
      show coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ q jq) = coeffMap (algebraMap ℚ (AlgebraicClosure ℚ)) 0
      rw [← hj'Kc, h0, map_zero]; simp))⟩
  obtain ⟨-, -, H3, H4⟩ :=
    ModularCurve.mem_chartAlgFin_and_forall_mem_chartAlgInf_exists_mul_mem_of_coe_eq_coeffEmb_jq_qExpand_of_one_lt
      q hq1 ↥K₁ (laurentBaseChange ↥K₁ (xHFunctionField (q ^ 2 * M') (levelH q M'))) ↥A₁ jK
      (by apply coeffMap_injective _ hι; rw [hjKc, hcc])
      j'K
      (by apply coeffMap_injective _ hι; rw [hj'Kc, hcc])
  have heAj : eA jK = j₁ := hejK
  have heAj' : eA j'K = j' := hej'K
  refine ⟨fun c hc => ?_, fun c hc => ?_⟩
  · have hcK : e.symm c ∈ AlgebraicCurve.TwoChartIntegralModel.chartAlgInf ↥A₁ ↥(laurentBaseChange ↥K₁ (xHFunctionField (q ^ 2 * M') (levelH q M'))) j'K := by
      rw [mem_chartAlgInf_iff_of_algEquiv eA j'K j' heAj', heA, e.apply_symm_apply]; exact hc
    obtain ⟨sK, hsK, ⟨aK, haK, hsdef⟩, hsc⟩ := H3 _ hcK
    refine ⟨e sK, ?_, ⟨e aK, ?_, ?_⟩, ?_⟩
    · rw [← heA, ← mem_chartAlgInf_iff_of_algEquiv eA jK j₁ heAj]; exact hsK
    · rw [← heA, ← mem_chartAlgInf_iff_of_algEquiv eA jK j₁ heAj]; exact haK
    · rw [hsdef, map_add, map_one, map_mul, map_inv₀, hejK]
    · have : e sK * c = e (sK * e.symm c) := by rw [map_mul, e.apply_symm_apply]
      rw [this, ← heA, ← mem_chartAlgInf_iff_of_algEquiv eA jK j₁ heAj]; exact hsc
  · have hcK : e.symm c ∈ AlgebraicCurve.TwoChartIntegralModel.chartAlgInf ↥A₁ ↥(laurentBaseChange ↥K₁ (xHFunctionField (q ^ 2 * M') (levelH q M'))) jK := by
      rw [mem_chartAlgInf_iff_of_algEquiv eA jK j₁ heAj, heA, e.apply_symm_apply]; exact hc
    obtain ⟨sK, hsK, ⟨aK, haK, hsdef⟩, hsc⟩ := H4 _ hcK
    refine ⟨e sK, ?_, ⟨e aK, ?_, ?_⟩, ?_⟩
    · rw [← heA, ← mem_chartAlgInf_iff_of_algEquiv eA j'K j' heAj']; exact hsK
    · rw [← heA, ← mem_chartAlgInf_iff_of_algEquiv eA j'K j' heAj']; exact haK
    · rw [hsdef, map_add, map_one, map_mul, map_inv₀, hej'K]
    · have : e sK * c = e (sK * e.symm c) := by rw [map_mul, e.apply_symm_apply]
      rw [this, ← heA, ← mem_chartAlgInf_iff_of_algEquiv eA j'K j' heAj']; exact hsc

end W4

p2m_open "Polynomial AlgebraicGeometry.Polynomial"

section ModEq

variable {L : Type} [Field L] [CharZero L]

theorem exists_monic_eval₂_coeffEmb (p : ℕ) [Fact p.Prime] [NeZero p] :
    ∃ Φ : Polynomial (Polynomial ℤ), Φ.Monic ∧
      Φ.eval₂ (aeval (ModularCurve.coeffEmb L ModularCurve.jq)).toRingHom
        (ModularCurve.coeffEmb L (ModularCurve.qExpand ℚ p ModularCurve.jq)) = 0 ∧
      Φ.eval₂ (aeval (ModularCurve.coeffEmb L (ModularCurve.qExpand ℚ p ModularCurve.jq))).toRingHom
        (ModularCurve.coeffEmb L ModularCurve.jq) = 0 := by
  obtain ⟨data, hsymm⟩ := ModularCurve.exists_modularPolynomialData_evalSymm p
  have h0 : data.Φ.eval₂ (aeval ModularCurve.jq).toRingHom (ModularCurve.qExpand ℚ p ModularCurve.jq) = 0 := by
    have := data.eval_eq_zero
    rwa [ModularCurve.evalAtJ_def] at this
  have h1 : data.Φ.eval₂ (aeval (ModularCurve.qExpand ℚ p ModularCurve.jq)).toRingHom ModularCurve.jq = 0 := by
    rw [← hsymm]; exact h0
  have key : ∀ x y : LaurentSeries ℚ,
      (ModularCurve.coeffEmb L) (data.Φ.eval₂ (aeval x).toRingHom y)
        = data.Φ.eval₂ (aeval (ModularCurve.coeffEmb L x)).toRingHom (ModularCurve.coeffEmb L y) := by
    intro x y
    rw [hom_eval₂]
    congr 1
    refine Polynomial.ringHom_ext (fun a => ?_) ?_
    · simp
    · simp
  refine ⟨data.Φ, data.monic, ?_, ?_⟩
  · rw [← key, h0, map_zero]
  · rw [← key, h1, map_zero]

end ModEq

section Generic

variable {A T S : Type} [CommRing A] [Field T] [CommRing S] [Algebra A T]

theorem isIntegral_adjoin_of_eval₂_hom (ι : T →+* S) (hι : Function.Injective ι) (a b : T)
    (Φ : Polynomial (Polynomial ℤ)) (hm : Φ.Monic)
    (h : Φ.eval₂ (aeval (ι a)).toRingHom (ι b) = 0) :
    IsIntegral (Algebra.adjoin A ({a} : Set T)) b := by
  let a' : Algebra.adjoin A ({a} : Set T) := ⟨a, Algebra.self_mem_adjoin_singleton A a⟩
  let θ : Polynomial ℤ →+* Algebra.adjoin A ({a} : Set T) := (aeval a').toRingHom
  refine ⟨Φ.map θ, hm.map θ, ?_⟩
  rw [eval₂_map]
  apply hι
  rw [hom_eval₂, map_zero]
  convert h using 2
  refine Polynomial.ringHom_ext (fun n => by simp) ?_
  simp [θ, a']

end Generic

section JQ

theorem isIntegral_adjoin_jq_qExpand {A T : Type} [CommRing A] [Field T] [Algebra A T]
    (p : ℕ) [Fact p.Prime] (a b : T)
    (ι : T →+* LaurentSeries (AlgebraicClosure ℚ)) (hι : Function.Injective ι)
    (ha : ι a = ModularCurve.coeffEmb (AlgebraicClosure ℚ) ModularCurve.jq)
    (hb : haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
      ι b = ModularCurve.coeffEmb (AlgebraicClosure ℚ) (ModularCurve.qExpand ℚ p ModularCurve.jq)) :
    IsIntegral (Algebra.adjoin A ({a} : Set T)) b ∧ IsIntegral (Algebra.adjoin A ({b} : Set T)) a := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  obtain ⟨Φ, hm, h1, h2⟩ := exists_monic_eval₂_coeffEmb (L := AlgebraicClosure ℚ) p
  refine ⟨isIntegral_adjoin_of_eval₂_hom ι hι a b Φ hm ?_, isIntegral_adjoin_of_eval₂_hom ι hι b a Φ hm ?_⟩
  · convert h1 using 2 <;> first | rfl | exact Polynomial.ringHom_ext (fun n => by simp) (by simp [ha])
  · convert h2 using 2 <;> first | rfl | exact Polynomial.ringHom_ext (fun n => by simp) (by simp [hb])

end JQ

end TH1AuxIg

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 12800000 in
theorem solution
    (q : ℕ) [Fact q.Prime] (hq : 5 ≤ q) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (hle : modularFunctionFieldBar M' ≤ fieldBar q M')
    (k₀ : IntermediateField ℚ (AlgebraicClosure ℚ))
    (K₁ : IntermediateField ↥k₀ (AlgebraicClosure ℚ)) (hK₁ : FiniteDimensional ↥k₀ ↥K₁)
    (A₁ : ValuationSubring ↥K₁) :
    letI : Algebra ↥k₀ ↥(fieldBar q M') :=
      ((algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')).comp (algebraMap ↥k₀ (AlgebraicClosure ℚ))).toAlgebra
    ∀ (F₀ : IntermediateField ↥k₀ ↥(fieldBar q M')),
      (IntermediateField.adjoin ↥k₀ (Set.range (algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M'))) ⊔ F₀ = ⊤) →
      (∀ (ζ' : Idx q) (γ : SL(2, ℤ)), γ ∈ Gamma0 M' → ∀ f : ↥(fieldBar q M'), f ∈ F₀ → levelAutBar q M' ζ' γ f ∈ F₀) →
      (∀ (K' : IntermediateField ↥k₀ (AlgebraicClosure ℚ)), FiniteDimensional ↥k₀ ↥K' →
        ∀ (m : ℕ) (c : Fin m → AlgebraicClosure ℚ) (a : Fin m → ↥(fieldBar q M')), (∀ i, a i ∈ IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K' : Set (AlgebraicClosure ℚ))) ⊔ F₀) →
          LinearIndependent ↥K' c → ∑ i, algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') (c i) * a i = 0 → ∀ i, a i = 0) →
      (∀ f : ↥(fieldBar q M'), (f : LaurentSeries (AlgebraicClosure ℚ)) ∈ Set.range ⇑(coeffEmb (AlgebraicClosure ℚ)) → f ∈ F₀) →
    ∀ [Algebra ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀)],
      (∀ a : ↥A₁, ((algebraMap ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) a : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀)) : ↥(fieldBar q M')) =
        algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') ((a : ↥K₁) : AlgebraicClosure ℚ)) →
    ∀ (j₁ : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀)),
      ((j₁ : ↥(fieldBar q M')) = IntermediateField.inclusion hle (⟨coeffEmb (AlgebraicClosure ℚ) jq,
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ : ↥(modularFunctionFieldBar M'))) →
    ∀ [Fact (j₁ ≠ 0)],
    ∃ j' : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀),
      ((j' : ↥(fieldBar q M')) : LaurentSeries (AlgebraicClosure ℚ)) = coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ q jq) ∧
      (∀ y, y ∈ TwoChartIntegralModel.chartAlgInf ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j' →
        ∃ s, s ∈ TwoChartIntegralModel.chartAlgInf ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁ ∧
          (∃ a, a ∈ TwoChartIntegralModel.chartAlgInf ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁ ∧ s = 1 + j₁⁻¹ * a) ∧
          s * y ∈ TwoChartIntegralModel.chartAlgInf ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁) ∧
      (∀ y, y ∈ TwoChartIntegralModel.chartAlgInf ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁ →
        ∃ s, s ∈ TwoChartIntegralModel.chartAlgInf ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j' ∧
          (∃ a, a ∈ TwoChartIntegralModel.chartAlgInf ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j' ∧ s = 1 + j'⁻¹ * a) ∧
          s * y ∈ TwoChartIntegralModel.chartAlgInf ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j') := by
  intro F₀ hK1 hSTAB hLD hRAT instA₁ halg j₁ hj₁ instj₁
  obtain ⟨j', hj', -, -, -⟩ :=
    ModularCurve.FullLevel.exists_qExpand_mem_chartAlgFin_and_forall_mem_closure_levelAutBar_exists_algEquiv_levelField
      q hq M' hqM' hle k₀ K₁ hK₁ A₁ F₀ hK1 hSTAB hLD hRAT halg j₁ hj₁
  exact ⟨j', hj', TH1AuxIg.poleChart_bridge q hq M' hqM' hle k₀ K₁ hK₁ A₁ F₀ hK1 hLD hRAT halg j₁ hj₁ j' hj'⟩

end S_ModularCurve_FullLevel_exists_qExpand_forall_mem_chartAlgInf_exists_mul_mem_levelField
end P2MW
export P2MW.S_ModularCurve_FullLevel_exists_qExpand_forall_mem_chartAlgInf_exists_mul_mem_levelField (solution)
