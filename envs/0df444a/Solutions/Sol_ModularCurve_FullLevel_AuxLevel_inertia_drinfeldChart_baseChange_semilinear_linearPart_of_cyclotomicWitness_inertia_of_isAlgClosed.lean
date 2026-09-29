-- Prove2me | solution 1 for ModularCurve.FullLevel.AuxLevel.inertia_drinfeldChart_baseChange_semilinear_linearPart_of_cyclotomicWitness_inertia_of_isAlgClosed
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.339302+00:00
-- url     : https://prove2.me/submissions/2ab944ec-7529-5c56-95c8-3e4ba361a1bf

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_DrinfeldCurve_LocalChart
import Definitions.Def_ModularCurve_FullLevelLevelAutAt
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_AdicCompletionLocalRing
import Theorems.Thm_IsDiscreteValuationRing_ringEquiv_apply_eq_pow_of_isPrimitiveRoot_of_pow_sq_sub_one_eq_of_apply_eq_mul
import Theorems.Thm_ModularCurve_exists_ringEquiv_restrict_coeffMap_laurentBaseChange_of_normal
import Theorems.Thm_AdicCompletion_ringHom_eq_of_map_maximalIdeal_le_of_forall_apply_algebraMap_eq
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_exists_stalk_iso_localization_atPrime_of_iotaFin_apply_eq
import Theorems.Thm_IsLocalRing_exists_ringEquiv_adicCompletion_maximalIdeal_comp_algebraMap_of_ringEquiv
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_finiteType_chartAlgFin_and_chartAlgInf
import Theorems.Thm_ModularCurve_FullLevel_AuxLevel_transcendental_and_finiteDimensional_and_isSeparable_adjoin_of_coe_eq_coeffEmb_jq
import Theorems.Thm_AdicCompletion_isNoetherianRing_of_isNoetherianRing
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_AuxLevel_inertia_drinfeldChart_baseChange_semilinear_linearPart_of_cyclotomicWitness_inertia_of_isAlgClosed
p2m_attr_erase "instance" "ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt"
p2m_attr_erase "simp" "ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.coe_cuspidalDivisor₀ ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff"
p2m_attr_erase "simp" "ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply"
p2m_attr_erase "simp" "AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal"

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

open scoped MatrixGroups TensorProduct

set_option synthInstance.maxHeartbeats 1600000

namespace INERTGlue

open IsLocalRing

theorem injective_of_iso {X Y : CommRingCat} (e : X ≅ Y) : Function.Injective e.hom.hom := by
  intro a b h
  have ha : e.inv.hom (e.hom.hom a) = a := by
    have := congrArg (fun φ : X ⟶ X => φ.hom a) e.hom_inv_id; simpa using this
  have hb : e.inv.hom (e.hom.hom b) = b := by
    have := congrArg (fun φ : X ⟶ X => φ.hom b) e.hom_inv_id; simpa using this
  rw [← ha, ← hb, h]

theorem iso_inv_hom {X Y : CommRingCat} (e : X ≅ Y) (a : X) : e.inv.hom (e.hom.hom a) = a := by
  have := congrArg (fun φ : X ⟶ X => φ.hom a) e.hom_inv_id; simpa using this

theorem iso_hom_inv {X Y : CommRingCat} (e : X ≅ Y) (b : Y) : e.hom.hom (e.inv.hom b) = b := by
  have := congrArg (fun φ : Y ⟶ Y => φ.hom b) e.inv_hom_id; simpa using this

theorem isNoetherianRing_of_baseChange (A₀ A C₀ C : Type*) [CommRing A₀] [CommRing A] [Algebra A₀ A]
    [IsNoetherianRing A] [CommRing C₀] [Algebra A₀ C₀] [Algebra.FiniteType A₀ C₀] [CommRing C] [Algebra A C]
    (c : C₀ →+* C) (β : A ⊗[A₀] C₀ ≃+* C) (hβ : ∀ (a : A) (b : C₀), β (a ⊗ₜ[A₀] b) = algebraMap A C a * c b) :
    IsNoetherianRing C := by
  haveI hft : Algebra.FiniteType A (A ⊗[A₀] C₀) := inferInstance
  let βₐ : A ⊗[A₀] C₀ →ₐ[A] C :=
    { toRingHom := β.toRingHom
      commutes' := fun a => by
        show β (algebraMap A (A ⊗[A₀] C₀) a) = algebraMap A C a
        rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply, hβ, map_one,
          mul_one] }
  haveI : Algebra.FiniteType A C := Algebra.FiniteType.of_surjective βₐ (fun x => β.surjective x)
  exact Algebra.FiniteType.isNoetherianRing A C

theorem core_fin {A K C₀ : Type} [CommRing A] [CommRing K] [Algebra A K] [CommRing C₀]
    (C : Subalgebra A K) (τK : K →+* K) (cc : C₀ →+* ↥C)
    (hτalg : ∀ a : A, ∃ a' : A, τK (algebraMap A K a) = algebraMap A K a')
    (hτc : ∀ b : C₀, ∃ b' : C₀, τK ((cc b : ↥C) : K) = ((cc b' : ↥C) : K))
    (hgen : ∀ x : ↥C, x ∈ Subring.closure (Set.range (algebraMap A ↥C) ∪ Set.range cc)) :
    ∀ a : K, a ∈ C → τK a ∈ C := by
  intro a ha
  have key : ∀ x : ↥C, x ∈ Subring.closure (Set.range (algebraMap A ↥C) ∪ Set.range cc) → τK (x : K) ∈ C := by
    intro x hx
    induction hx using Subring.closure_induction with
    | mem x hx =>
      rcases hx with ⟨a, rfl⟩ | ⟨b, rfl⟩
      · obtain ⟨a', ha'⟩ := hτalg a
        rw [Subalgebra.coe_algebraMap, ha']
        exact C.algebraMap_mem a'
      · obtain ⟨b', hb'⟩ := hτc b
        rw [hb']
        exact (cc b').2
    | zero => rw [ZeroMemClass.coe_zero, map_zero]; exact C.zero_mem
    | one => rw [OneMemClass.coe_one, map_one]; exact C.one_mem
    | add x y _ _ hx hy => rw [Subalgebra.coe_add, map_add]; exact C.add_mem hx hy
    | neg x _ hx => rw [Subalgebra.coe_neg, map_neg]; exact C.neg_mem hx
    | mul x y _ _ hx hy => rw [Subalgebra.coe_mul, map_mul]; exact C.mul_mem hx hy
  exact key ⟨a, ha⟩ (hgen ⟨a, ha⟩)

theorem core_fix {A C C₀ : Type} [CommRing A] [CommRing C] [Algebra A C] [CommRing C₀]
    (I : Ideal C) (τ' : C →+* C) (cc : C₀ →+* C)
    (hτalg : ∀ a : A, τ' (algebraMap A C a) - algebraMap A C a ∈ I)
    (hτc : ∀ b : C₀, τ' (cc b) - cc b ∈ I)
    (hgen : ∀ x : C, x ∈ Subring.closure (Set.range (algebraMap A C) ∪ Set.range cc)) :
    ∀ x : C, τ' x - x ∈ I := by
  intro x
  have hx := hgen x
  induction hx using Subring.closure_induction with
  | mem x hx =>
    rcases hx with ⟨a, rfl⟩ | ⟨b, rfl⟩
    · exact hτalg a
    · exact hτc b
  | zero => rw [map_zero, sub_self]; exact I.zero_mem
  | one => rw [map_one, sub_self]; exact I.zero_mem
  | add x y _ _ hx hy =>
    have : τ' (x + y) - (x + y) = (τ' x - x) + (τ' y - y) := by rw [map_add]; ring
    rw [this]; exact I.add_mem hx hy
  | neg x _ hx =>
    have : τ' (-x) - (-x) = -(τ' x - x) := by rw [map_neg]; ring
    rw [this]; exact I.neg_mem hx
  | mul x y _ _ hx hy =>
    have : τ' (x * y) - x * y = (τ' x - x) * τ' y + x * (τ' y - y) := by rw [map_mul]; ring
    rw [this]; exact I.add_mem (I.mul_mem_right _ hx) (I.mul_mem_left _ hy)

theorem core_lin {A C C₀ S : Type} [CommRing A] [CommRing C] [Algebra A C] [CommRing C₀] [CommRing S]
    (f g : C →+* S) (cc : C₀ →+* C)
    (halg : ∀ a : A, f (algebraMap A C a) = g (algebraMap A C a))
    (hc : ∀ b : C₀, f (cc b) = g (cc b))
    (hgen : ∀ x : C, x ∈ Subring.closure (Set.range (algebraMap A C) ∪ Set.range cc)) :
    ∀ x : C, f x = g x := by
  intro x
  have hx := hgen x
  induction hx using Subring.closure_induction with
  | mem x hx =>
    rcases hx with ⟨a, rfl⟩ | ⟨b, rfl⟩
    · exact halg a
    · exact hc b
  | zero => rw [map_zero, map_zero]
  | one => rw [map_one, map_one]
  | add x y _ _ hx hy => rw [map_add, map_add, hx, hy]
  | neg x _ hx => rw [map_neg, map_neg, hx]
  | mul x y _ _ hx hy => rw [map_mul, map_mul, hx, hy]

theorem symm_apply_eq_pow_of_apply_eq_pow {R : Type*} [CommRing R] {q : ℕ} [Fact q.Prime]
    {ζ : R} (hζ : IsPrimitiveRoot ζ q) (σ : R ≃+* R) (d : (ZMod q)ˣ)
    (h : σ ζ = ζ ^ ((d : ZMod q).val)) :
    σ.symm ζ = ζ ^ (((d⁻¹ : (ZMod q)ˣ) : ZMod q).val) := by
  have hqp : q.Prime := Fact.out
  haveI : Fact (1 < q) := ⟨hqp.one_lt⟩
  have hpm : ∀ n : ℕ, ζ ^ n = ζ ^ (n % q) := fun n => by
    conv_lhs => rw [← Nat.div_add_mod n q]
    rw [pow_add, pow_mul, hζ.pow_eq_one, one_pow, one_mul]
  have hmod : ((d : ZMod q).val * ((d⁻¹ : (ZMod q)ˣ) : ZMod q).val) % q = 1 := by
    rw [← ZMod.val_mul, Units.mul_inv, ZMod.val_one]
  have key : σ (ζ ^ (((d⁻¹ : (ZMod q)ˣ) : ZMod q).val)) = ζ := by
    rw [map_pow, h, ← pow_mul, hpm, hmod, pow_one]
  have h2 := congrArg σ.symm key
  rw [RingEquiv.symm_apply_apply] at h2
  exact h2.symm

end INERTGlue

set_option maxHeartbeats 32000000 in
theorem solution
    (q : ℕ) [Fact q.Prime] (hq : 5 ≤ q) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ3 : 3 ≤ ℓ) (hℓq : ℓ ≠ q) (hℓM' : ¬ ℓ ∣ M')
    (L : Type) [Field L] [CharZero L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ q)
    (ξ : L) (hξ : IsPrimitiveRoot ξ (q * ℓ))
    (hι : ∃ ι : L →+* ℂ, ι ξ = Complex.exp (2 * Real.pi * Complex.I / (q * ℓ)))
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L
      (ModularCurve.xHFunctionField ((q * ℓ) ^ 2 * M')
        (ModularCurve.FullLevel.levelH (q * ℓ) M')))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    [IsAlgClosed (IsLocalRing.ResidueField A)]
    (hAq : (q : A) ∈ IsLocalRing.maximalIdeal A) (hζA : ∃ x : A, algebraMap A L x = ζ)
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)]
    (ϖ : A) (hϖ : IsLocalRing.maximalIdeal A = Ideal.span {ϖ})

    (t : A) (ht : ∃ w : A, IsUnit w ∧ t ^ (q - 1) = (q : A) * w)
    (z : ↥(AlgebraicCurve.TwoChartIntegralModel A (↥K) j))
    (ϖz : (AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)
    (hϖz : ϖz = ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.germ ⊤ z trivial).hom
      (((AlgebraicCurve.TwoChartIntegralModel.toBase A (↥K) j).appTop).hom
        ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom ϖ)))
    (hz : ϖz ∈ IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z))
    (y : ↥(AlgebraicCurve.TwoChartIntegralModel.XFin A (↥K) j))
    (hy : (AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K) j).base y = z)
    (hss : ∀ (Ω : Type) [Field Ω] [CharP Ω q] [IsAlgClosed Ω] [DecidableEq Ω]
      (φ : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) →+* Ω),
      RingHom.ker φ = y.asIdeal →
        φ (AlgebraicCurve.TwoChartIntegralModel.jChartFin A (↥K) j) ∈ ModularCurve.ssJSet q Ω)

    (L₀ : Type) [Field L₀] [CharZero L₀] [IsCyclotomicExtension {q * ℓ} ℚ L₀]
    (ζ₀ : L₀) (hζ₀ : IsPrimitiveRoot ζ₀ q)
    (ξ₀ : L₀) (hξ₀ : IsPrimitiveRoot ξ₀ (q * ℓ))
    (K₀ : IntermediateField L₀ (LaurentSeries L₀))
    (hK₀ : K₀ = ModularCurve.laurentBaseChange L₀
      (ModularCurve.xHFunctionField ((q * ℓ) ^ 2 * M')
        (ModularCurve.FullLevel.levelH (q * ℓ) M')))
    (A₀ : Type) [CommRing A₀] [IsDomain A₀] [IsDiscreteValuationRing A₀] [Algebra A₀ L₀] [IsFractionRing A₀ L₀]
    (hA₀q : (q : A₀) ∈ IsLocalRing.maximalIdeal A₀) (hζ₀A : ∃ x : A₀, algebraMap A₀ L₀ x = ζ₀)
    [Algebra A₀ ↥K₀] [IsScalarTower A₀ L₀ ↥K₀]
    (j₀ : ↥K₀) (hj₀ : ((j₀ : LaurentSeries L₀)) = ModularCurve.coeffEmb L₀ ModularCurve.jq) [Fact (j₀ ≠ 0)]
    (ϖ₀ : A₀) (hϖ₀ : IsLocalRing.maximalIdeal A₀ = Ideal.span {ϖ₀})
    (z₀ : ↥(AlgebraicCurve.TwoChartIntegralModel A₀ (↥K₀) j₀))
    (ϖz₀ : (AlgebraicCurve.TwoChartIntegralModel A₀ (↥K₀) j₀).presheaf.stalk z₀)
    (hϖz₀ : ϖz₀ = ((AlgebraicCurve.TwoChartIntegralModel A₀ (↥K₀) j₀).presheaf.germ ⊤ z₀ trivial).hom
      (((AlgebraicCurve.TwoChartIntegralModel.toBase A₀ (↥K₀) j₀).appTop).hom
        ((Scheme.ΓSpecIso (CommRingCat.of A₀)).inv.hom ϖ₀)))
    (hz₀ : ϖz₀ ∈ IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A₀ (↥K₀) j₀).presheaf.stalk z₀))
    (y₀ : ↥(AlgebraicCurve.TwoChartIntegralModel.XFin A₀ (↥K₀) j₀))
    (hy₀ : (AlgebraicCurve.TwoChartIntegralModel.ιFin A₀ (↥K₀) j₀).base y₀ = z₀)
    (hss₀ : ∀ (Ω : Type) [Field Ω] [CharP Ω q] [IsAlgClosed Ω] [DecidableEq Ω]
      (φ : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₀ (↥K₀) j₀) →+* Ω),
      RingHom.ker φ = y₀.asIdeal →
        φ (AlgebraicCurve.TwoChartIntegralModel.jChartFin A₀ (↥K₀) j₀) ∈ ModularCurve.ssJSet q Ω)

    (i : L₀ →+* L) (hiζ : i ζ₀ = ζ) (hiξ : i ξ₀ = ξ)
    [Algebra A₀ A] [IsLocalHom (algebraMap A₀ A)] (hinj : Function.Injective (algebraMap A₀ A))
    (hA₀A : ∀ a : A₀, algebraMap A L (algebraMap A₀ A a) = i (algebraMap A₀ L₀ a))
    (hϖ₀t : ∃ w : A, IsUnit w ∧ algebraMap A₀ A ϖ₀ = t * w)
    (cK : ↥K₀ →+* ↥K)
    (hcK : ∀ x : ↥K₀, ((cK x : ↥K) : LaurentSeries L) = ModularCurve.coeffMap i ((x : ↥K₀) : LaurentSeries L₀))
    (hcKj : cK j₀ = j)
    (c : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₀ (↥K₀) j₀) →+* ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j))
    (hc : ∀ a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₀ (↥K₀) j₀),
      ((c a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)) : ↥K) = cK (a : ↥K₀))
    (hcy : Ideal.comap c y.asIdeal = y₀.asIdeal)

    (β : (A ⊗[A₀] ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₀ (↥K₀) j₀)) ≃+*
      ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j))
    (hβ : ∀ (a : A) (b : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₀ (↥K₀) j₀)),
      β (a ⊗ₜ[A₀] b) = algebraMap A ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) a * c b)

    (W₀ : Type) [CommRing W₀] [IsDomain W₀] [IsDiscreteValuationRing W₀]
    [IsAdicComplete (IsLocalRing.maximalIdeal W₀) W₀] (σ₀ : A₀ →+* W₀)
    (hσ₀ϖ : IsLocalRing.maximalIdeal W₀ = Ideal.span {σ₀ ϖ₀})
    (f₀ u₀ v₀ : MvPowerSeries (Fin 2) W₀) (hu₀ : IsUnit u₀) (hv₀ : IsUnit v₀)
    (hf₀ : f₀ - DrinfeldCurve.LocalChart.drinfeldForm q W₀ ∈
      (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W₀), MvPowerSeries.X 1}) ^ (q + 2))
    (e₀ : AdicCompletion (IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A₀ (↥K₀) j₀).presheaf.stalk z₀)) ((AlgebraicCurve.TwoChartIntegralModel A₀ (↥K₀) j₀).presheaf.stalk z₀) ≃+*
      MvPowerSeries (Fin 2) W₀ ⧸ Ideal.span {MvPowerSeries.C (σ₀ ϖ₀) * v₀ - f₀ * u₀})
    (hconst₀ :
      let STK₀ := ((AlgebraicCurve.TwoChartIntegralModel A₀ (↥K₀) j₀).presheaf.stalk z₀)
      let CMP₀ := (AdicCompletion (IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A₀ (↥K₀) j₀).presheaf.stalk z₀)) ((AlgebraicCurve.TwoChartIntegralModel A₀ (↥K₀) j₀).presheaf.stalk z₀))
      let toC₀ : STK₀ →+* CMP₀ := algebraMap STK₀ CMP₀
      let S₀ := (MvPowerSeries (Fin 2) W₀ ⧸ Ideal.span {MvPowerSeries.C (σ₀ ϖ₀) * v₀ - f₀ * u₀})
      let mkS₀ : MvPowerSeries (Fin 2) W₀ →+* S₀ := Ideal.Quotient.mk (Ideal.span {MvPowerSeries.C (σ₀ ϖ₀) * v₀ - f₀ * u₀})
      let germY₀ : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₀ (↥K₀) j₀) →+* STK₀ :=
        ((AlgebraicCurve.TwoChartIntegralModel A₀ (↥K₀) j₀).presheaf.germ
            ((AlgebraicCurve.TwoChartIntegralModel.ιFin A₀ (↥K₀) j₀) ''ᵁ ⊤) z₀ ⟨y₀, trivial, hy₀⟩).hom.comp
          ((((AlgebraicCurve.TwoChartIntegralModel.ιFin A₀ (↥K₀) j₀).appIso ⊤).inv.hom).comp
            (Scheme.ΓSpecIso (CommRingCat.of ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₀ (↥K₀) j₀))).inv.hom)

      (∀ a : A₀, e₀ (algebraMap ((AlgebraicCurve.TwoChartIntegralModel A₀ (↥K₀) j₀).presheaf.stalk z₀)
            (AdicCompletion (IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A₀ (↥K₀) j₀).presheaf.stalk z₀)) ((AlgebraicCurve.TwoChartIntegralModel A₀ (↥K₀) j₀).presheaf.stalk z₀))
          (((AlgebraicCurve.TwoChartIntegralModel A₀ (↥K₀) j₀).presheaf.germ ⊤ z₀ trivial).hom
            (((AlgebraicCurve.TwoChartIntegralModel.toBase A₀ (↥K₀) j₀).appTop).hom
              ((Scheme.ΓSpecIso (CommRingCat.of A₀)).inv.hom a)))) =
        Ideal.Quotient.mk _ (MvPowerSeries.C (σ₀ a))))
    (hinert₀ :
      let STK₀ := ((AlgebraicCurve.TwoChartIntegralModel A₀ (↥K₀) j₀).presheaf.stalk z₀)
      let CMP₀ := (AdicCompletion (IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A₀ (↥K₀) j₀).presheaf.stalk z₀)) ((AlgebraicCurve.TwoChartIntegralModel A₀ (↥K₀) j₀).presheaf.stalk z₀))
      let toC₀ : STK₀ →+* CMP₀ := algebraMap STK₀ CMP₀
      let S₀ := (MvPowerSeries (Fin 2) W₀ ⧸ Ideal.span {MvPowerSeries.C (σ₀ ϖ₀) * v₀ - f₀ * u₀})
      let mkS₀ : MvPowerSeries (Fin 2) W₀ →+* S₀ := Ideal.Quotient.mk (Ideal.span {MvPowerSeries.C (σ₀ ϖ₀) * v₀ - f₀ * u₀})
      let germY₀ : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₀ (↥K₀) j₀) →+* STK₀ :=
        ((AlgebraicCurve.TwoChartIntegralModel A₀ (↥K₀) j₀).presheaf.germ
            ((AlgebraicCurve.TwoChartIntegralModel.ιFin A₀ (↥K₀) j₀) ''ᵁ ⊤) z₀ ⟨y₀, trivial, hy₀⟩).hom.comp
          ((((AlgebraicCurve.TwoChartIntegralModel.ιFin A₀ (↥K₀) j₀).appIso ⊤).inv.hom).comp
            (Scheme.ΓSpecIso (CommRingCat.of ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₀ (↥K₀) j₀))).inv.hom)

      (∀ (d : (ZMod q)ˣ) (σL : L₀ ≃+* L₀) (σA : A₀ ≃+* A₀),
        (∀ a : A₀, algebraMap A₀ L₀ (σA a) = σL (algebraMap A₀ L₀ a)) →

        (∀ a : A₀, σA a - a ∈ IsLocalRing.maximalIdeal A₀) →

        σL ζ₀ = ζ₀ ^ ((d : ZMod q).val) →
        ∀ τ : ↥K₀ ≃+* ↥K₀,

          (∀ x : ↥K₀, ((τ x : ↥K₀) : LaurentSeries L₀) = ModularCurve.coeffMap σL.toRingHom ((x : ↥K₀) : LaurentSeries L₀)) →

          (∀ a : ↥K₀, a ∈ (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₀ (↥K₀) j₀) →
            τ a ∈ (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₀ (↥K₀) j₀)) ∧
          ∀ hpres : (∀ a : ↥K₀, a ∈ (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₀ (↥K₀) j₀) →
              τ a ∈ (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₀ (↥K₀) j₀)),

            (∀ a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₀ (↥K₀) j₀),
              (((τ.toRingHom.restrict (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₀ (↥K₀) j₀)
                (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₀ (↥K₀) j₀) hpres) a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₀ (↥K₀) j₀)) - a ∈ y₀.asIdeal)) ∧

            ∃ (θ : S₀ ≃+* S₀) (σW : W₀ ≃+* W₀) (M : Matrix (Fin 2) (Fin 2) W₀),
              (∀ a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₀ (↥K₀) j₀),
                θ (e₀ (toC₀ (germY₀ a))) = e₀ (toC₀ (germY₀ ((τ.toRingHom.restrict (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₀ (↥K₀) j₀)
                (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₀ (↥K₀) j₀) hpres) a)))) ∧
              (∀ a : A₀, σW (σ₀ a) = σ₀ (σA a)) ∧
              (∀ w : W₀, σW w - w ∈ IsLocalRing.maximalIdeal W₀) ∧
              (∀ w : W₀, θ (mkS₀ (MvPowerSeries.C w)) = mkS₀ (MvPowerSeries.C (σW w))) ∧
              (∀ jj : Fin 2, θ (mkS₀ (MvPowerSeries.X jj)) -
                  mkS₀ (∑ ii : Fin 2, MvPowerSeries.C (M ii jj) * MvPowerSeries.X ii) ∈
                (Ideal.span {mkS₀ (MvPowerSeries.X 0), mkS₀ (MvPowerSeries.X 1)}) ^ 2) ∧
              (∀ ii jj : Fin 2, M ii jj -
                  ((((d : ZMod q) * ((ModularCurve.FullLevel.diagOneElem q (d ^ q)⁻¹ : CuspidalType.GL2 q) :
                      Matrix (Fin 2) (Fin 2) (ZMod q)) ii jj).val : ℕ) : W₀) ∈ IsLocalRing.maximalIdeal W₀)))

    (ψ : W₀ →+* (AdicCompletion (IsLocalRing.maximalIdeal A) A))
    (f u v : MvPowerSeries (Fin 2) (AdicCompletion (IsLocalRing.maximalIdeal A) A)) (hu : IsUnit u) (hv : IsUnit v)
    (hf : f - DrinfeldCurve.LocalChart.drinfeldForm q (AdicCompletion (IsLocalRing.maximalIdeal A) A) ∈
      (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) (AdicCompletion (IsLocalRing.maximalIdeal A) A)), MvPowerSeries.X 1}) ^ (q + 2))
    (e : AdicCompletion (IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)) ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z) ≃+*
      MvPowerSeries (Fin 2) (AdicCompletion (IsLocalRing.maximalIdeal A) A) ⧸ Ideal.span {MvPowerSeries.C ((algebraMap A (AdicCompletion (IsLocalRing.maximalIdeal A) A)) t) * v - f * u}) :
      let STK := ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)
      let CMP := (AdicCompletion (IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)) ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z))
      let toC : STK →+* CMP := algebraMap STK CMP
      let S := (MvPowerSeries (Fin 2) (AdicCompletion (IsLocalRing.maximalIdeal A) A) ⧸ Ideal.span {MvPowerSeries.C ((algebraMap A (AdicCompletion (IsLocalRing.maximalIdeal A) A)) t) * v - f * u})
      let mkS : MvPowerSeries (Fin 2) (AdicCompletion (IsLocalRing.maximalIdeal A) A) →+* S := Ideal.Quotient.mk (Ideal.span {MvPowerSeries.C ((algebraMap A (AdicCompletion (IsLocalRing.maximalIdeal A) A)) t) * v - f * u})
      let germY : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) →+* STK :=
        ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.germ
            ((AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K) j) ''ᵁ ⊤) z ⟨y, trivial, hy⟩).hom.comp
          ((((AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K) j).appIso ⊤).inv.hom).comp
            (Scheme.ΓSpecIso (CommRingCat.of ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j))).inv.hom)

      (∀ a : A₀, ψ (σ₀ a) = (algebraMap A (AdicCompletion (IsLocalRing.maximalIdeal A) A)) (algebraMap A₀ A a)) →
      (∀ w : W₀, w ∈ IsLocalRing.maximalIdeal W₀ → ψ w ∈ IsLocalRing.maximalIdeal (AdicCompletion (IsLocalRing.maximalIdeal A) A)) →
      f = MvPowerSeries.map ψ f₀ →

      (∀ (x : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₀ (↥K₀) j₀)) (s : MvPowerSeries (Fin 2) W₀),
        e₀ (algebraMap _ (AdicCompletion (IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A₀ (↥K₀) j₀).presheaf.stalk z₀)) ((AlgebraicCurve.TwoChartIntegralModel A₀ (↥K₀) j₀).presheaf.stalk z₀))
          ((((AlgebraicCurve.TwoChartIntegralModel A₀ (↥K₀) j₀).presheaf.germ
              ((AlgebraicCurve.TwoChartIntegralModel.ιFin A₀ (↥K₀) j₀) ''ᵁ ⊤) z₀ ⟨y₀, trivial, hy₀⟩).hom.comp
            ((((AlgebraicCurve.TwoChartIntegralModel.ιFin A₀ (↥K₀) j₀).appIso ⊤).inv.hom).comp
              (Scheme.ΓSpecIso (CommRingCat.of ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₀ (↥K₀) j₀))).inv.hom)) x)) =
          Ideal.Quotient.mk _ s →
        e (toC (germY (c x))) = mkS (MvPowerSeries.map ψ s)) →

      (∀ a : A, e (algebraMap ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)
            (AdicCompletion (IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)) ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z))
          (((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.germ ⊤ z trivial).hom
            (((AlgebraicCurve.TwoChartIntegralModel.toBase A (↥K) j).appTop).hom
              ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom a)))) =
        Ideal.Quotient.mk _ (MvPowerSeries.C ((algebraMap A (AdicCompletion (IsLocalRing.maximalIdeal A) A)) a))) →

    ∀ (d : (ZMod q)ˣ) (σL : L ≃+* L) (σA : A ≃+* A),
      (∀ a : A, algebraMap A L (σA a) = σL (algebraMap A L a)) →

      (∀ a : A, σA a - a ∈ IsLocalRing.maximalIdeal A) →

      ∀ (π : A), π ^ (q ^ 2 - 1) = (q : A) → ∀ (αt : A), σA π = αt * π →
      αt ^ (q + 1) - (((d : ZMod q).val : ℕ) : A) ∈ IsLocalRing.maximalIdeal A →
      ∀ τ : ↥K ≃+* ↥K,

        (∀ x : ↥K, ((τ x : ↥K) : LaurentSeries L) = ModularCurve.coeffMap σL.toRingHom ((x : ↥K) : LaurentSeries L)) →

        (∀ a : ↥K, a ∈ (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) →
          τ a ∈ (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)) ∧
        ∀ hpres : (∀ a : ↥K, a ∈ (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) →
            τ a ∈ (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)),

          (∀ a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j),
            (((τ.toRingHom.restrict (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)
              (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) hpres) a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)) - a ∈ y.asIdeal)) ∧

          ∃ (θ : S ≃+* S) (σW : (AdicCompletion (IsLocalRing.maximalIdeal A) A) ≃+* (AdicCompletion (IsLocalRing.maximalIdeal A) A)) (ct : (AdicCompletion (IsLocalRing.maximalIdeal A) A)) (M : Matrix (Fin 2) (Fin 2) (AdicCompletion (IsLocalRing.maximalIdeal A) A)),
            (∀ a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j),
              θ (e (toC (germY a))) = e (toC (germY ((τ.toRingHom.restrict (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)
              (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) hpres) a)))) ∧
            (∀ a : A, σW ((algebraMap A (AdicCompletion (IsLocalRing.maximalIdeal A) A)) a) = (algebraMap A (AdicCompletion (IsLocalRing.maximalIdeal A) A)) (σA a)) ∧
            (∀ w : (AdicCompletion (IsLocalRing.maximalIdeal A) A), σW w - w ∈ IsLocalRing.maximalIdeal (AdicCompletion (IsLocalRing.maximalIdeal A) A)) ∧
            (∀ w : (AdicCompletion (IsLocalRing.maximalIdeal A) A), θ (mkS (MvPowerSeries.C w)) = mkS (MvPowerSeries.C (σW w))) ∧
            (∀ jj : Fin 2, θ (mkS (MvPowerSeries.X jj)) -
                mkS (∑ ii : Fin 2, MvPowerSeries.C (M ii jj) * MvPowerSeries.X ii) ∈
              (Ideal.span {mkS (MvPowerSeries.X 0), mkS (MvPowerSeries.X 1)}) ^ 2) ∧

            (ct - (algebraMap A (AdicCompletion (IsLocalRing.maximalIdeal A) A)) (αt ^ (q + 1)) ∈ IsLocalRing.maximalIdeal (AdicCompletion (IsLocalRing.maximalIdeal A) A)) ∧
            (∀ ii jj : Fin 2, M ii jj -
                ct * (((((ModularCurve.FullLevel.diagOneElem q (d ^ q)⁻¹ : CuspidalType.GL2 q) :
                    Matrix (Fin 2) (Fin 2) (ZMod q)) ii jj).val : ℕ) : (AdicCompletion (IsLocalRing.maximalIdeal A) A)) ∈ IsLocalRing.maximalIdeal (AdicCompletion (IsLocalRing.maximalIdeal A) A)) := by

  classical
  intro STK CMP toC S mkS germY hψσ hψloc hfmap hCOMPAT hCONST
  have hqp : q.Prime := Fact.out
  haveI : NeZero q := ⟨hqp.ne_zero⟩
  haveI : NeZero (q * ℓ) := ⟨Nat.mul_ne_zero hqp.ne_zero (Fact.out : ℓ.Prime).ne_zero⟩

  haveI : Module.Finite ℚ L₀ := IsCyclotomicExtension.finite {q * ℓ} ℚ L₀
  haveI : Algebra.IsAlgebraic ℚ L₀ := Algebra.IsAlgebraic.of_finite ℚ L₀
  haveI hGal₀ : IsGalois ℚ L₀ := IsCyclotomicExtension.isGalois {q * ℓ} ℚ L₀
  obtain ⟨htj₀, hFD₀, hsep₀⟩ :=
    ModularCurve.FullLevel.AuxLevel.transcendental_and_finiteDimensional_and_isSeparable_adjoin_of_coe_eq_coeffEmb_jq
      q M' ℓ L₀ K₀ hK₀ A₀ j₀ hj₀
  haveI hFT₀ : Algebra.FiniteType A₀ ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₀ (↥K₀) j₀) :=
    (AlgebraicCurve.TwoChartIntegralModel.finiteType_chartAlgFin_and_chartAlgInf A₀ L₀ (↥K₀) j₀ htj₀ hFD₀ hsep₀).1
  have hnoethC : IsNoetherianRing ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) :=
    INERTGlue.isNoetherianRing_of_baseChange A₀ A ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₀ (↥K₀) j₀) ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) c β hβ
  haveI hnoethC₀ : IsNoetherianRing ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₀ (↥K₀) j₀) := Algebra.FiniteType.isNoetherianRing A₀ _

  obtain ⟨E₀, hE₀const, hE₀Y⟩ :=
    AlgebraicCurve.TwoChartIntegralModel.exists_stalk_iso_localization_atPrime_of_iotaFin_apply_eq A₀ (↥K₀) j₀ z₀ y₀ hy₀
  obtain ⟨E₁, hE₁const, hE₁Y⟩ :=
    AlgebraicCurve.TwoChartIntegralModel.exists_stalk_iso_localization_atPrime_of_iotaFin_apply_eq A (↥K) j z y hy
  let E₁e : STK ≃+* (Localization.AtPrime y.asIdeal) := E₁.commRingCatIsoToRingEquiv
  let E₀e : (((AlgebraicCurve.TwoChartIntegralModel A₀ (↥K₀) j₀)).presheaf.stalk z₀) ≃+* (Localization.AtPrime y₀.asIdeal) :=
    E₀.commRingCatIsoToRingEquiv
  have hE₁e : ∀ a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j), E₁e (germY a) = algebraMap _ (Localization.AtPrime y.asIdeal) a := fun a => hE₁Y a
  haveI hnoethLoc : IsNoetherianRing (Localization.AtPrime y.asIdeal) := inferInstance
  haveI hnoethLoc₀ : IsNoetherianRing (Localization.AtPrime y₀.asIdeal) := inferInstance
  haveI hnoethSTK : IsNoetherianRing STK := isNoetherianRing_of_ringEquiv (Localization.AtPrime y.asIdeal) E₁e.symm
  haveI hnoethSTK₀ : IsNoetherianRing (((AlgebraicCurve.TwoChartIntegralModel A₀ (↥K₀) j₀)).presheaf.stalk z₀) :=
    isNoetherianRing_of_ringEquiv (Localization.AtPrime y₀.asIdeal) E₀e.symm

  have hgermconst : ∀ a : A, (((AlgebraicCurve.TwoChartIntegralModel A (↥K) j)).presheaf.germ ⊤ z trivial).hom
        (((AlgebraicCurve.TwoChartIntegralModel.toBase A (↥K) j).appTop).hom ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom a))
      = germY (algebraMap A ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) a) := by
    intro a
    apply INERTGlue.injective_of_iso E₁
    change E₁.hom.hom _ = E₁e (germY _)
    rw [hE₁const, hE₁e, IsScalarTower.algebraMap_apply A ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) (Localization.AtPrime y.asIdeal)]
  have hmemY : ∀ w : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j), w ∈ y.asIdeal → germY w ∈ IsLocalRing.maximalIdeal STK := by
    intro w hw
    have h1 : algebraMap ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) (Localization.AtPrime y.asIdeal) w ∈ IsLocalRing.maximalIdeal (Localization.AtPrime y.asIdeal) :=
      (IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime y.asIdeal) y.asIdeal w).mpr hw
    rw [← hE₁e] at h1
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at h1 ⊢
    exact fun hu => h1 (hu.map E₁e)
  have hϖy : algebraMap A ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) ϖ ∈ y.asIdeal := by
    by_contra hnot
    have hu : IsUnit (algebraMap ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) (Localization.AtPrime y.asIdeal) (algebraMap A ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) ϖ)) :=
      (IsLocalization.AtPrime.isUnit_to_map_iff (Localization.AtPrime y.asIdeal) y.asIdeal _).mpr hnot
    rw [← hE₁e, ← hgermconst, ← hϖz] at hu
    exact (IsLocalRing.mem_maximalIdeal _).mp hz ((isUnit_map_iff E₁e ϖz).mp hu)
  have h𝔪y : ∀ m : A, m ∈ IsLocalRing.maximalIdeal A → algebraMap A ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) m ∈ y.asIdeal := by
    intro m hm
    rw [hϖ] at hm
    obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton'.mp hm
    rw [map_mul]; exact Ideal.mul_mem_left _ _ hϖy

  have hgen : ∀ x : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j), x ∈ Subring.closure (Set.range (algebraMap A ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)) ∪ Set.range c) := by
    intro x
    obtain ⟨t', rfl⟩ := β.surjective x
    induction t' using TensorProduct.induction_on with
    | zero => rw [map_zero]; exact Subring.zero_mem _
    | tmul a b =>
      rw [hβ]
      exact Subring.mul_mem _ (Subring.subset_closure (Or.inl ⟨a, rfl⟩)) (Subring.subset_closure (Or.inr ⟨b, rfl⟩))
    | add x y hx hy => rw [map_add]; exact Subring.add_mem _ hx hy

  obtain ⟨ζA, hζA'⟩ := hζA
  have hζAprim : IsPrimitiveRoot ζA q := by
    have h := hζ; rw [← hζA'] at h
    exact h.of_map_of_injective (IsFractionRing.injective A L)

  have hcoeK : ∀ x : L, ((algebraMap L ↥K x : ↥K) : LaurentSeries L) = algebraMap L (LaurentSeries L) x := fun x => rfl
  have hτA_of : ∀ (σL' : L ≃+* L) (σA' : A ≃+* A) (τ' : ↥K ≃+* ↥K),
      (∀ a : A, algebraMap A L (σA' a) = σL' (algebraMap A L a)) →
      (∀ x : ↥K, ((τ' x : ↥K) : LaurentSeries L) = ModularCurve.coeffMap σL'.toRingHom ((x : ↥K) : LaurentSeries L)) →
      ∀ a : A, τ' (algebraMap A ↥K a) = algebraMap A ↥K (σA' a) := by
    intro σL' σA' τ' hσ' hτ' a
    apply Subtype.ext
    rw [hτ', IsScalarTower.algebraMap_apply A L ↥K, IsScalarTower.algebraMap_apply A L ↥K, hcoeK, hcoeK,
      ModularCurve.coeffMap_algebraMap, hσ']
    rfl

  have hfin_of : ∀ (τ' : ↥K ≃+* ↥K) (σA' : A ≃+* A) (τ₀' : ↥K₀ ≃+* ↥K₀),
      (∀ a : A, τ' (algebraMap A ↥K a) = algebraMap A ↥K (σA' a)) →
      (∀ x : ↥K₀, cK (τ₀' x) = τ' (cK x)) →
      (∀ a : ↥K₀, a ∈ (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₀ (↥K₀) j₀) → τ₀' a ∈ (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₀ (↥K₀) j₀)) →
      ∀ x : ↥K, x ∈ (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) → τ' x ∈ (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) := by
    intro τ' σA' τ₀' hτ'A hτ'c hfin₀'
    refine INERTGlue.core_fin (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) τ'.toRingHom c (fun a => ⟨σA' a, hτ'A a⟩) (fun b => ?_) hgen
    refine ⟨(τ₀'.toRingHom.restrict (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₀ (↥K₀) j₀) (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₀ (↥K₀) j₀) hfin₀') b, ?_⟩
    show τ' ((c b : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)) : ↥K) = _
    rw [hc, hc, ← hτ'c]
    rfl

  intro d σL σA hσ hσm π hπ αt hσπ hd τ hτ

  have hζd : σA ζA = ζA ^ ((d : ZMod q).val) :=
    IsDiscreteValuationRing.ringEquiv_apply_eq_pow_of_isPrimitiveRoot_of_pow_sq_sub_one_eq_of_apply_eq_mul
      q hAq ζA hζAprim π hπ σA hσm αt hσπ _ hd
  have hσLζ : σL ζ = ζ ^ ((d : ZMod q).val) := by rw [← hζA', ← hσ, hζd, map_pow]

  haveI : Normal ℚ L₀ := hGal₀.to_normal
  obtain ⟨σL₀, σA₀, τ₀, hiσ, hσA₀A, hσA₀L, hσA₀m, hτ₀, hcτ₀⟩ :=
    ModularCurve.exists_ringEquiv_restrict_coeffMap_laurentBaseChange_of_normal L₀ L i A A₀ hinj hA₀A
      (ModularCurve.xHFunctionField ((q * ℓ) ^ 2 * M') (ModularCurve.FullLevel.levelH (q * ℓ) M')) K₀ hK₀ K hK cK hcK
      σL σA hσ hσm τ hτ
  have hσL₀ζ : σL₀ ζ₀ = ζ₀ ^ ((d : ZMod q).val) := by
    apply i.injective; rw [hiσ, hiζ, map_pow, hiζ, hσLζ]

  obtain ⟨hfin₀, hrest₀⟩ := hinert₀ d σL₀ σA₀ hσA₀L hσA₀m hσL₀ζ τ₀ hτ₀
  obtain ⟨hfix₀, θ₀, σW₀, M₀, hθ₀e, hσW₀σ, hσW₀m, hθ₀C, hθ₀X, hM₀⟩ := hrest₀ hfin₀

  have hτA : ∀ a : A, τ (algebraMap A ↥K a) = algebraMap A ↥K (σA a) := hτA_of σL σA τ hσ hτ
  have hfin : ∀ x : ↥K, x ∈ (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) → τ x ∈ (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) := hfin_of τ σA τ₀ hτA hcτ₀ hfin₀
  refine ⟨hfin, fun hpres => ?_⟩

  let τC : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) →+* ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) := τ.toRingHom.restrict (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) hpres
  let τ₀C : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₀ (↥K₀) j₀) →+* ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₀ (↥K₀) j₀) := τ₀.toRingHom.restrict (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₀ (↥K₀) j₀) (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₀ (↥K₀) j₀) hfin₀
  have hτC_coe : ∀ w : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j), ((τC w : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)) : ↥K) = τ (w : ↥K) := fun w => rfl
  have hτ₀C_coe : ∀ w : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₀ (↥K₀) j₀), ((τ₀C w : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₀ (↥K₀) j₀)) : ↥K₀) = τ₀ (w : ↥K₀) := fun w => rfl
  have hcτ : ∀ b : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₀ (↥K₀) j₀), τC (c b) = c (τ₀C b) := by
    intro b; apply Subtype.ext; rw [hτC_coe, hc, hc, hτ₀C_coe, hcτ₀]
  have hτCA : ∀ a : A, τC (algebraMap A ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) a) = algebraMap A ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) (σA a) := by
    intro a; apply Subtype.ext; rw [hτC_coe, Subalgebra.coe_algebraMap, Subalgebra.coe_algebraMap, hτA]

  have hfix : ∀ w : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j), τC w - w ∈ y.asIdeal := by
    refine INERTGlue.core_fix y.asIdeal τC c (fun a => ?_) (fun b => ?_) hgen
    · rw [hτCA, ← map_sub]; exact h𝔪y _ (hσm a)
    · rw [hcτ, ← map_sub]
      have hb : τ₀C b - b ∈ y₀.asIdeal := hfix₀ b
      rw [← hcy] at hb
      exact hb
  refine ⟨hfix, ?_⟩

  have hσL₀ζ' : σL₀.symm ζ₀ = ζ₀ ^ (((d⁻¹ : (ZMod q)ˣ) : ZMod q).val) :=
    INERTGlue.symm_apply_eq_pow_of_apply_eq_pow hζ₀ σL₀ d hσL₀ζ
  have hσA₀L' : ∀ a : A₀, algebraMap A₀ L₀ (σA₀.symm a) = σL₀.symm (algebraMap A₀ L₀ a) := by
    intro a; apply σL₀.injective
    rw [← hσA₀L, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]
  have hσA₀m' : ∀ a : A₀, σA₀.symm a - a ∈ IsLocalRing.maximalIdeal A₀ := by
    intro a
    have h := hσA₀m (σA₀.symm a)
    rw [RingEquiv.apply_symm_apply] at h
    rw [show σA₀.symm a - a = -(a - σA₀.symm a) by ring]
    exact Submodule.neg_mem _ h
  have hτ₀' : ∀ x : ↥K₀, ((τ₀.symm x : ↥K₀) : LaurentSeries L₀) =
      ModularCurve.coeffMap σL₀.symm.toRingHom ((x : ↥K₀) : LaurentSeries L₀) := by
    intro x
    conv_rhs => rw [← τ₀.apply_symm_apply x, hτ₀, ModularCurve.coeffMap_coeffMap]
    rw [ModularCurve.coeffMap_congr (g := RingHom.id L₀) (RingHom.ext fun t => σL₀.symm_apply_apply t),
      ModularCurve.coeffMap_id]
  obtain ⟨hfin₀', -⟩ := hinert₀ d⁻¹ σL₀.symm σA₀.symm hσA₀L' hσA₀m' hσL₀ζ' τ₀.symm hτ₀'
  have hτA' : ∀ a : A, τ.symm (algebraMap A ↥K a) = algebraMap A ↥K (σA.symm a) := by
    intro a; apply τ.injective; rw [RingEquiv.apply_symm_apply, hτA, RingEquiv.apply_symm_apply]
  have hcτ₀' : ∀ x : ↥K₀, cK (τ₀.symm x) = τ.symm (cK x) := by
    intro x; apply τ.injective; rw [RingEquiv.apply_symm_apply, ← hcτ₀, RingEquiv.apply_symm_apply]
  have hpres' : ∀ x : ↥K, x ∈ (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) → τ.symm x ∈ (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) :=
    hfin_of τ.symm σA.symm τ₀.symm hτA' hcτ₀' hfin₀'

  let τCe : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) ≃+* ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) :=
    RingEquiv.ofRingHom τC (τ.symm.toRingHom.restrict (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) hpres')
      (RingHom.ext fun w => Subtype.ext (τ.apply_symm_apply (w : ↥K)))
      (RingHom.ext fun w => Subtype.ext (τ.symm_apply_apply (w : ↥K)))
  have hτCe : ∀ w, τCe w = τC w := fun w => rfl
  have hy_iff : ∀ w : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j), τC w ∈ y.asIdeal ↔ w ∈ y.asIdeal := by
    intro w; constructor
    · intro h; have h2 := Ideal.sub_mem _ h (hfix w); rwa [sub_sub_cancel] at h2
    · intro h; have h2 := Ideal.add_mem _ (hfix w) h; rwa [sub_add_cancel] at h2
  have hmapCompl : y.asIdeal.primeCompl.map τCe.toMonoidHom = y.asIdeal.primeCompl := by
    ext w
    simp only [Submonoid.mem_map]
    constructor
    · rintro ⟨w', hw', rfl⟩
      exact fun h => hw' ((hy_iff w').mp h)
    · intro hw
      refine ⟨τCe.symm w, fun h => hw ?_, τCe.apply_symm_apply w⟩
      have h2 := (hy_iff (τCe.symm w)).mpr h
      rwa [← hτCe, RingEquiv.apply_symm_apply] at h2
  let τLoc : (Localization.AtPrime y.asIdeal) ≃+* (Localization.AtPrime y.asIdeal) := IsLocalization.ringEquivOfRingEquiv (Localization.AtPrime y.asIdeal) (Localization.AtPrime y.asIdeal) τCe hmapCompl
  have hτLoc : ∀ w : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j), τLoc (algebraMap ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) (Localization.AtPrime y.asIdeal) w) = algebraMap ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) (Localization.AtPrime y.asIdeal) (τC w) :=
    fun w => IsLocalization.ringEquivOfRingEquiv_eq hmapCompl w
  let τSTK : STK ≃+* STK := E₁e.trans (τLoc.trans E₁e.symm)
  have hτSTK : ∀ w : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j), τSTK (germY w) = germY (τC w) := by
    intro w
    show E₁e.symm (τLoc (E₁e (germY w))) = germY (τC w)
    rw [hE₁e, hτLoc, ← hE₁e, RingEquiv.symm_apply_apply]
  obtain ⟨τhat, hτhat⟩ :=
    IsLocalRing.exists_ringEquiv_adicCompletion_maximalIdeal_comp_algebraMap_of_ringEquiv τSTK
  let θ : S ≃+* S := (e.symm.trans τhat).trans e
  have hθe : ∀ x : CMP, θ (e x) = e (τhat x) := fun x => by
    show e (τhat (e.symm (e x))) = e (τhat x); rw [RingEquiv.symm_apply_apply]
  have hθcompat : ∀ a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j), θ (e (toC (germY a))) = e (toC (germY (τC a))) := by
    intro a; rw [hθe, ← hτSTK a]; exact congrArg e (hτhat (germY a))

  obtain ⟨σW, hσW⟩ := IsLocalRing.exists_ringEquiv_adicCompletion_maximalIdeal_comp_algebraMap_of_ringEquiv σA

  haveI : IsNoetherianRing CMP := AdicCompletion.isNoetherianRing_of_isNoetherianRing _
  haveI : Nontrivial S := e.injective.nontrivial
  haveI hlocS : IsLocalRing S := IsLocalRing.of_surjective' (e : CMP →+* S) e.surjective
  haveI : IsNoetherianRing S := isNoetherianRing_of_ringEquiv CMP e
  have hunitS : ∀ {x : S}, ¬ IsUnit x ↔ x ∈ IsLocalRing.maximalIdeal S := fun {x} => Iff.rfl
  have heloc : ∀ x : CMP, x ∈ IsLocalRing.maximalIdeal CMP → e x ∈ IsLocalRing.maximalIdeal S := by
    intro x hx
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hx ⊢
    exact fun hu => hx ((isUnit_map_iff e x).mp hu)
  have hθloc : ∀ s : S, s ∈ IsLocalRing.maximalIdeal S → θ s ∈ IsLocalRing.maximalIdeal S := by
    intro s hs
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hs ⊢
    exact fun hu => hs ((isUnit_map_iff θ s).mp hu)
  have hmemS : ∀ w : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j), w ∈ y.asIdeal → e (toC (germY w)) ∈ IsLocalRing.maximalIdeal S := by
    intro w hw
    refine heloc _ ?_
    rw [AdicCompletion.maximalIdeal_eq_map]
    exact Ideal.mem_map_of_mem _ (hmemY w hw)

  have hlamwd : ∀ s ∈ (Ideal.span {MvPowerSeries.C (σ₀ ϖ₀) * v₀ - f₀ * u₀}), (mkS.comp (MvPowerSeries.map ψ)) s = 0 := by
    intro s hs
    have h0 := hCOMPAT 0 s (by
      rw [map_zero, map_zero, map_zero]
      exact ((Ideal.Quotient.eq_zero_iff_mem).mpr hs).symm)
    rw [map_zero, map_zero, map_zero, map_zero] at h0
    exact h0.symm
  let lam : (MvPowerSeries (Fin 2) W₀ ⧸ Ideal.span {MvPowerSeries.C (σ₀ ϖ₀) * v₀ - f₀ * u₀}) →+* S := Ideal.Quotient.lift _ (mkS.comp (MvPowerSeries.map ψ)) hlamwd
  have hlammk : ∀ s : MvPowerSeries (Fin 2) W₀, lam (Ideal.Quotient.mk _ s) = mkS (MvPowerSeries.map ψ s) :=
    fun s => Ideal.Quotient.lift_mk _ _ _
  have hlame₀ : ∀ b : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₀ (↥K₀) j₀), lam (e₀ ((algebraMap ((((AlgebraicCurve.TwoChartIntegralModel A₀ (↥K₀) j₀)).presheaf.stalk z₀)) (AdicCompletion (IsLocalRing.maximalIdeal ((((AlgebraicCurve.TwoChartIntegralModel A₀ (↥K₀) j₀)).presheaf.stalk z₀))) ((((AlgebraicCurve.TwoChartIntegralModel A₀ (↥K₀) j₀)).presheaf.stalk z₀)))) (((((AlgebraicCurve.TwoChartIntegralModel A₀ (↥K₀) j₀)).presheaf.germ ((AlgebraicCurve.TwoChartIntegralModel.ιFin A₀ (↥K₀) j₀) ''ᵁ ⊤) z₀ ⟨y₀, trivial, hy₀⟩).hom.comp ((((AlgebraicCurve.TwoChartIntegralModel.ιFin A₀ (↥K₀) j₀).appIso ⊤).inv.hom).comp (Scheme.ΓSpecIso (CommRingCat.of ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₀ (↥K₀) j₀))).inv.hom)) b))) = e (toC (germY (c b))) := by
    intro b
    obtain ⟨s, hs⟩ := Ideal.Quotient.mk_surjective (e₀ ((algebraMap ((((AlgebraicCurve.TwoChartIntegralModel A₀ (↥K₀) j₀)).presheaf.stalk z₀)) (AdicCompletion (IsLocalRing.maximalIdeal ((((AlgebraicCurve.TwoChartIntegralModel A₀ (↥K₀) j₀)).presheaf.stalk z₀))) ((((AlgebraicCurve.TwoChartIntegralModel A₀ (↥K₀) j₀)).presheaf.stalk z₀)))) (((((AlgebraicCurve.TwoChartIntegralModel A₀ (↥K₀) j₀)).presheaf.germ ((AlgebraicCurve.TwoChartIntegralModel.ιFin A₀ (↥K₀) j₀) ''ᵁ ⊤) z₀ ⟨y₀, trivial, hy₀⟩).hom.comp ((((AlgebraicCurve.TwoChartIntegralModel.ιFin A₀ (↥K₀) j₀).appIso ⊤).inv.hom).comp (Scheme.ΓSpecIso (CommRingCat.of ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₀ (↥K₀) j₀))).inv.hom)) b)))
    rw [← hs, hlammk, hCOMPAT b s hs.symm]

  have hE₀e : ∀ b : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₀ (↥K₀) j₀), E₀e (((((AlgebraicCurve.TwoChartIntegralModel A₀ (↥K₀) j₀)).presheaf.germ ((AlgebraicCurve.TwoChartIntegralModel.ιFin A₀ (↥K₀) j₀) ''ᵁ ⊤) z₀ ⟨y₀, trivial, hy₀⟩).hom.comp ((((AlgebraicCurve.TwoChartIntegralModel.ιFin A₀ (↥K₀) j₀).appIso ⊤).inv.hom).comp (Scheme.ΓSpecIso (CommRingCat.of ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₀ (↥K₀) j₀))).inv.hom)) b) = algebraMap ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₀ (↥K₀) j₀) (Localization.AtPrime y₀.asIdeal) b := fun b => hE₀Y b
  have hE₀e' : ∀ b : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₀ (↥K₀) j₀), E₀e.symm (algebraMap ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₀ (↥K₀) j₀) (Localization.AtPrime y₀.asIdeal) b) = ((((AlgebraicCurve.TwoChartIntegralModel A₀ (↥K₀) j₀)).presheaf.germ ((AlgebraicCurve.TwoChartIntegralModel.ιFin A₀ (↥K₀) j₀) ''ᵁ ⊤) z₀ ⟨y₀, trivial, hy₀⟩).hom.comp ((((AlgebraicCurve.TwoChartIntegralModel.ιFin A₀ (↥K₀) j₀).appIso ⊤).inv.hom).comp (Scheme.ΓSpecIso (CommRingCat.of ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₀ (↥K₀) j₀))).inv.hom)) b := by
    intro b; rw [← hE₀e, RingEquiv.symm_apply_apply]
  let G₁ : (AdicCompletion (IsLocalRing.maximalIdeal ((((AlgebraicCurve.TwoChartIntegralModel A₀ (↥K₀) j₀)).presheaf.stalk z₀))) ((((AlgebraicCurve.TwoChartIntegralModel A₀ (↥K₀) j₀)).presheaf.stalk z₀))) →+* S := ((θ : S →+* S).comp lam).comp (e₀ : (AdicCompletion (IsLocalRing.maximalIdeal ((((AlgebraicCurve.TwoChartIntegralModel A₀ (↥K₀) j₀)).presheaf.stalk z₀))) ((((AlgebraicCurve.TwoChartIntegralModel A₀ (↥K₀) j₀)).presheaf.stalk z₀))) →+* (MvPowerSeries (Fin 2) W₀ ⧸ Ideal.span {MvPowerSeries.C (σ₀ ϖ₀) * v₀ - f₀ * u₀}))
  let G₂ : (AdicCompletion (IsLocalRing.maximalIdeal ((((AlgebraicCurve.TwoChartIntegralModel A₀ (↥K₀) j₀)).presheaf.stalk z₀))) ((((AlgebraicCurve.TwoChartIntegralModel A₀ (↥K₀) j₀)).presheaf.stalk z₀))) →+* S := (lam.comp (θ₀ : (MvPowerSeries (Fin 2) W₀ ⧸ Ideal.span {MvPowerSeries.C (σ₀ ϖ₀) * v₀ - f₀ * u₀}) →+* (MvPowerSeries (Fin 2) W₀ ⧸ Ideal.span {MvPowerSeries.C (σ₀ ϖ₀) * v₀ - f₀ * u₀}))).comp (e₀ : (AdicCompletion (IsLocalRing.maximalIdeal ((((AlgebraicCurve.TwoChartIntegralModel A₀ (↥K₀) j₀)).presheaf.stalk z₀))) ((((AlgebraicCurve.TwoChartIntegralModel A₀ (↥K₀) j₀)).presheaf.stalk z₀))) →+* (MvPowerSeries (Fin 2) W₀ ⧸ Ideal.span {MvPowerSeries.C (σ₀ ϖ₀) * v₀ - f₀ * u₀}))
  let Φ₁ : (Localization.AtPrime y₀.asIdeal) →+* S := (G₁.comp (algebraMap ((((AlgebraicCurve.TwoChartIntegralModel A₀ (↥K₀) j₀)).presheaf.stalk z₀)) (AdicCompletion (IsLocalRing.maximalIdeal ((((AlgebraicCurve.TwoChartIntegralModel A₀ (↥K₀) j₀)).presheaf.stalk z₀))) ((((AlgebraicCurve.TwoChartIntegralModel A₀ (↥K₀) j₀)).presheaf.stalk z₀))))).comp (E₀e.symm : (Localization.AtPrime y₀.asIdeal) →+* (((AlgebraicCurve.TwoChartIntegralModel A₀ (↥K₀) j₀)).presheaf.stalk z₀))
  let Φ₂ : (Localization.AtPrime y₀.asIdeal) →+* S := (G₂.comp (algebraMap ((((AlgebraicCurve.TwoChartIntegralModel A₀ (↥K₀) j₀)).presheaf.stalk z₀)) (AdicCompletion (IsLocalRing.maximalIdeal ((((AlgebraicCurve.TwoChartIntegralModel A₀ (↥K₀) j₀)).presheaf.stalk z₀))) ((((AlgebraicCurve.TwoChartIntegralModel A₀ (↥K₀) j₀)).presheaf.stalk z₀))))).comp (E₀e.symm : (Localization.AtPrime y₀.asIdeal) →+* (((AlgebraicCurve.TwoChartIntegralModel A₀ (↥K₀) j₀)).presheaf.stalk z₀))
  have hΦ₁ : ∀ b : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₀ (↥K₀) j₀), Φ₁ (algebraMap ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₀ (↥K₀) j₀) (Localization.AtPrime y₀.asIdeal) b) = e (toC (germY (τC (c b)))) := by
    intro b
    show θ (lam (e₀ ((algebraMap ((((AlgebraicCurve.TwoChartIntegralModel A₀ (↥K₀) j₀)).presheaf.stalk z₀)) (AdicCompletion (IsLocalRing.maximalIdeal ((((AlgebraicCurve.TwoChartIntegralModel A₀ (↥K₀) j₀)).presheaf.stalk z₀))) ((((AlgebraicCurve.TwoChartIntegralModel A₀ (↥K₀) j₀)).presheaf.stalk z₀)))) (E₀e.symm (algebraMap ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₀ (↥K₀) j₀) (Localization.AtPrime y₀.asIdeal) b))))) = _
    rw [hE₀e', hlame₀, hθcompat]
  have hΦ₂ : ∀ b : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₀ (↥K₀) j₀), Φ₂ (algebraMap ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₀ (↥K₀) j₀) (Localization.AtPrime y₀.asIdeal) b) = e (toC (germY (c (τ₀C b)))) := by
    intro b
    show lam (θ₀ (e₀ ((algebraMap ((((AlgebraicCurve.TwoChartIntegralModel A₀ (↥K₀) j₀)).presheaf.stalk z₀)) (AdicCompletion (IsLocalRing.maximalIdeal ((((AlgebraicCurve.TwoChartIntegralModel A₀ (↥K₀) j₀)).presheaf.stalk z₀))) ((((AlgebraicCurve.TwoChartIntegralModel A₀ (↥K₀) j₀)).presheaf.stalk z₀)))) (E₀e.symm (algebraMap ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₀ (↥K₀) j₀) (Localization.AtPrime y₀.asIdeal) b))))) = _
    rw [hE₀e', hθ₀e b, hlame₀ (τ₀C b)]
  have hΦeq : Φ₁ = Φ₂ := by
    refine IsLocalization.ringHom_ext y₀.asIdeal.primeCompl (RingHom.ext fun b => ?_)
    show Φ₁ (algebraMap ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₀ (↥K₀) j₀) (Localization.AtPrime y₀.asIdeal) b) = Φ₂ (algebraMap ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₀ (↥K₀) j₀) (Localization.AtPrime y₀.asIdeal) b)
    rw [hΦ₁, hΦ₂, hcτ]
  have hΦloc : ∀ (Φ : (Localization.AtPrime y₀.asIdeal) →+* S), (∀ b : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₀ (↥K₀) j₀), b ∈ y₀.asIdeal → Φ (algebraMap ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₀ (↥K₀) j₀) (Localization.AtPrime y₀.asIdeal) b) ∈ IsLocalRing.maximalIdeal S) →
      ∀ m : (Localization.AtPrime y₀.asIdeal), m ∈ IsLocalRing.maximalIdeal (Localization.AtPrime y₀.asIdeal) → Φ m ∈ IsLocalRing.maximalIdeal S := by
    intro Φ hΦ m hm
    rw [← Localization.AtPrime.map_eq_maximalIdeal] at hm
    have : (y₀.asIdeal.map (algebraMap ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₀ (↥K₀) j₀) (Localization.AtPrime y₀.asIdeal))).map Φ ≤ IsLocalRing.maximalIdeal S := by
      rw [Ideal.map_map, Ideal.map_le_iff_le_comap]
      intro b hb; exact hΦ b hb
    exact this (Ideal.mem_map_of_mem Φ hm)
  have hGloc : ∀ (G : (AdicCompletion (IsLocalRing.maximalIdeal ((((AlgebraicCurve.TwoChartIntegralModel A₀ (↥K₀) j₀)).presheaf.stalk z₀))) ((((AlgebraicCurve.TwoChartIntegralModel A₀ (↥K₀) j₀)).presheaf.stalk z₀))) →+* S),
      (∀ m : (Localization.AtPrime y₀.asIdeal), m ∈ IsLocalRing.maximalIdeal (Localization.AtPrime y₀.asIdeal) → ((G.comp (algebraMap ((((AlgebraicCurve.TwoChartIntegralModel A₀ (↥K₀) j₀)).presheaf.stalk z₀)) (AdicCompletion (IsLocalRing.maximalIdeal ((((AlgebraicCurve.TwoChartIntegralModel A₀ (↥K₀) j₀)).presheaf.stalk z₀))) ((((AlgebraicCurve.TwoChartIntegralModel A₀ (↥K₀) j₀)).presheaf.stalk z₀))))).comp (E₀e.symm : (Localization.AtPrime y₀.asIdeal) →+* (((AlgebraicCurve.TwoChartIntegralModel A₀ (↥K₀) j₀)).presheaf.stalk z₀))) m ∈ IsLocalRing.maximalIdeal S) →
      ∀ x : (AdicCompletion (IsLocalRing.maximalIdeal ((((AlgebraicCurve.TwoChartIntegralModel A₀ (↥K₀) j₀)).presheaf.stalk z₀))) ((((AlgebraicCurve.TwoChartIntegralModel A₀ (↥K₀) j₀)).presheaf.stalk z₀))), x ∈ IsLocalRing.maximalIdeal (AdicCompletion (IsLocalRing.maximalIdeal ((((AlgebraicCurve.TwoChartIntegralModel A₀ (↥K₀) j₀)).presheaf.stalk z₀))) ((((AlgebraicCurve.TwoChartIntegralModel A₀ (↥K₀) j₀)).presheaf.stalk z₀))) → G x ∈ IsLocalRing.maximalIdeal S := by
    intro G hG x hx
    rw [AdicCompletion.maximalIdeal_eq_map] at hx
    have : ((IsLocalRing.maximalIdeal ((((AlgebraicCurve.TwoChartIntegralModel A₀ (↥K₀) j₀)).presheaf.stalk z₀))).map (algebraMap ((((AlgebraicCurve.TwoChartIntegralModel A₀ (↥K₀) j₀)).presheaf.stalk z₀)) (AdicCompletion (IsLocalRing.maximalIdeal ((((AlgebraicCurve.TwoChartIntegralModel A₀ (↥K₀) j₀)).presheaf.stalk z₀))) ((((AlgebraicCurve.TwoChartIntegralModel A₀ (↥K₀) j₀)).presheaf.stalk z₀))))).map G ≤ IsLocalRing.maximalIdeal S := by
      rw [Ideal.map_map, Ideal.map_le_iff_le_comap]
      intro m hm
      have hm' : E₀e m ∈ IsLocalRing.maximalIdeal (Localization.AtPrime y₀.asIdeal) := by
        rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hm ⊢
        exact fun hu => hm ((isUnit_map_iff E₀e m).mp hu)
      have := hG (E₀e m) hm'
      rwa [RingHom.comp_apply, RingHom.comp_apply, RingEquiv.coe_toRingHom, RingEquiv.symm_apply_apply] at this
    exact this (Ideal.mem_map_of_mem G hx)
  have hG₁loc : ∀ x : (AdicCompletion (IsLocalRing.maximalIdeal ((((AlgebraicCurve.TwoChartIntegralModel A₀ (↥K₀) j₀)).presheaf.stalk z₀))) ((((AlgebraicCurve.TwoChartIntegralModel A₀ (↥K₀) j₀)).presheaf.stalk z₀))), x ∈ IsLocalRing.maximalIdeal (AdicCompletion (IsLocalRing.maximalIdeal ((((AlgebraicCurve.TwoChartIntegralModel A₀ (↥K₀) j₀)).presheaf.stalk z₀))) ((((AlgebraicCurve.TwoChartIntegralModel A₀ (↥K₀) j₀)).presheaf.stalk z₀))) → G₁ x ∈ IsLocalRing.maximalIdeal S := by
    refine hGloc G₁ (hΦloc Φ₁ fun b hb => ?_)
    rw [hΦ₁, hcτ]
    refine hmemS _ ?_
    have hb' : τ₀C b ∈ y₀.asIdeal := by
      have h2 := Ideal.add_mem _ (hfix₀ b) hb; rwa [sub_add_cancel] at h2
    rw [← hcy] at hb'; exact hb'
  have hG₂loc : ∀ x : (AdicCompletion (IsLocalRing.maximalIdeal ((((AlgebraicCurve.TwoChartIntegralModel A₀ (↥K₀) j₀)).presheaf.stalk z₀))) ((((AlgebraicCurve.TwoChartIntegralModel A₀ (↥K₀) j₀)).presheaf.stalk z₀))), x ∈ IsLocalRing.maximalIdeal (AdicCompletion (IsLocalRing.maximalIdeal ((((AlgebraicCurve.TwoChartIntegralModel A₀ (↥K₀) j₀)).presheaf.stalk z₀))) ((((AlgebraicCurve.TwoChartIntegralModel A₀ (↥K₀) j₀)).presheaf.stalk z₀))) → G₂ x ∈ IsLocalRing.maximalIdeal S := by
    refine hGloc G₂ (hΦloc Φ₂ fun b hb => ?_)
    rw [hΦ₂]
    refine hmemS _ ?_
    have hb' : τ₀C b ∈ y₀.asIdeal := by
      have h2 := Ideal.add_mem _ (hfix₀ b) hb; rwa [sub_add_cancel] at h2
    rw [← hcy] at hb'; exact hb'
  have hGeq : G₁ = G₂ := by
    refine AdicCompletion.ringHom_eq_of_map_maximalIdeal_le_of_forall_apply_algebraMap_eq G₁ G₂ hG₁loc hG₂loc fun m => ?_
    have h1 : G₁ ((algebraMap ((((AlgebraicCurve.TwoChartIntegralModel A₀ (↥K₀) j₀)).presheaf.stalk z₀)) (AdicCompletion (IsLocalRing.maximalIdeal ((((AlgebraicCurve.TwoChartIntegralModel A₀ (↥K₀) j₀)).presheaf.stalk z₀))) ((((AlgebraicCurve.TwoChartIntegralModel A₀ (↥K₀) j₀)).presheaf.stalk z₀)))) m) = Φ₁ (E₀e m) := by
      show _ = G₁ ((algebraMap ((((AlgebraicCurve.TwoChartIntegralModel A₀ (↥K₀) j₀)).presheaf.stalk z₀)) (AdicCompletion (IsLocalRing.maximalIdeal ((((AlgebraicCurve.TwoChartIntegralModel A₀ (↥K₀) j₀)).presheaf.stalk z₀))) ((((AlgebraicCurve.TwoChartIntegralModel A₀ (↥K₀) j₀)).presheaf.stalk z₀)))) (E₀e.symm (E₀e m))); rw [RingEquiv.symm_apply_apply]
    have h2 : G₂ ((algebraMap ((((AlgebraicCurve.TwoChartIntegralModel A₀ (↥K₀) j₀)).presheaf.stalk z₀)) (AdicCompletion (IsLocalRing.maximalIdeal ((((AlgebraicCurve.TwoChartIntegralModel A₀ (↥K₀) j₀)).presheaf.stalk z₀))) ((((AlgebraicCurve.TwoChartIntegralModel A₀ (↥K₀) j₀)).presheaf.stalk z₀)))) m) = Φ₂ (E₀e m) := by
      show _ = G₂ ((algebraMap ((((AlgebraicCurve.TwoChartIntegralModel A₀ (↥K₀) j₀)).presheaf.stalk z₀)) (AdicCompletion (IsLocalRing.maximalIdeal ((((AlgebraicCurve.TwoChartIntegralModel A₀ (↥K₀) j₀)).presheaf.stalk z₀))) ((((AlgebraicCurve.TwoChartIntegralModel A₀ (↥K₀) j₀)).presheaf.stalk z₀)))) (E₀e.symm (E₀e m))); rw [RingEquiv.symm_apply_apply]
    rw [h1, h2, hΦeq]
  have hθlam : ∀ s₀ : (MvPowerSeries (Fin 2) W₀ ⧸ Ideal.span {MvPowerSeries.C (σ₀ ϖ₀) * v₀ - f₀ * u₀}), θ (lam s₀) = lam (θ₀ s₀) := by
    intro s₀
    have := RingHom.congr_fun hGeq (e₀.symm s₀)
    simpa [G₁, G₂] using this

  refine ⟨θ, σW, (((d : ZMod q).val : ℕ) : (AdicCompletion (IsLocalRing.maximalIdeal A) A)), fun ii jj => ψ (M₀ ii jj), hθcompat, hσW, ?_, ?_, ?_, ?_, ?_⟩
  ·
    intro w
    obtain ⟨a, y', hy', rfl⟩ := AdicCompletion.exists_eq_algebraMap_add (IsLocalRing.maximalIdeal A)
      (AdicCompletion.maximalIdeal_fg (A := A)) 1 w
    rw [pow_one, ← AdicCompletion.maximalIdeal_eq_map] at hy'
    have h1 : σW y' ∈ IsLocalRing.maximalIdeal (AdicCompletion (IsLocalRing.maximalIdeal A) A) := by
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hy' ⊢
      exact fun hu => hy' ((isUnit_map_iff σW y').mp hu)
    rw [map_add, hσW, show algebraMap A (AdicCompletion (IsLocalRing.maximalIdeal A) A) (σA a) + σW y' - (algebraMap A (AdicCompletion (IsLocalRing.maximalIdeal A) A) a + y')
        = algebraMap A (AdicCompletion (IsLocalRing.maximalIdeal A) A) (σA a - a) + (σW y' - y') by rw [map_sub]; ring]
    refine Ideal.add_mem _ ?_ (Ideal.sub_mem _ h1 hy')
    rw [AdicCompletion.maximalIdeal_eq_map]; exact Ideal.mem_map_of_mem _ (hσm a)
  ·
    have hCϖ : mkS (MvPowerSeries.C (algebraMap A (AdicCompletion (IsLocalRing.maximalIdeal A) A) ϖ)) ∈ IsLocalRing.maximalIdeal S := by
      rw [← hCONST ϖ, ← hϖz]
      refine heloc _ ?_
      rw [AdicCompletion.maximalIdeal_eq_map]; exact Ideal.mem_map_of_mem _ hz
    have hmkC : ∀ x : (AdicCompletion (IsLocalRing.maximalIdeal A) A), x ∈ IsLocalRing.maximalIdeal (AdicCompletion (IsLocalRing.maximalIdeal A) A) → mkS (MvPowerSeries.C x) ∈ IsLocalRing.maximalIdeal S := by
      intro x hx
      rw [AdicCompletion.maximalIdeal_eq_map] at hx
      have hle : (IsLocalRing.maximalIdeal A).map (algebraMap A (AdicCompletion (IsLocalRing.maximalIdeal A) A)) ≤ Ideal.span {algebraMap A (AdicCompletion (IsLocalRing.maximalIdeal A) A) ϖ} := by
        rw [Ideal.map_le_iff_le_comap]
        intro m hm
        rw [hϖ, Ideal.mem_span_singleton'] at hm
        obtain ⟨r, rfl⟩ := hm
        rw [Ideal.mem_comap, map_mul]
        exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)
      obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.mp (hle hx)
      rw [← hr, map_mul, map_mul]; exact Ideal.mul_mem_left _ _ hCϖ
    have hσWloc : ∀ x : (AdicCompletion (IsLocalRing.maximalIdeal A) A), x ∈ IsLocalRing.maximalIdeal (AdicCompletion (IsLocalRing.maximalIdeal A) A) → σW x ∈ IsLocalRing.maximalIdeal (AdicCompletion (IsLocalRing.maximalIdeal A) A) := by
      intro x hx
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hx ⊢
      exact fun hu => hx ((isUnit_map_iff σW x).mp hu)
    let g₁ : (AdicCompletion (IsLocalRing.maximalIdeal A) A) →+* S := (θ : S →+* S).comp (mkS.comp (MvPowerSeries.C : (AdicCompletion (IsLocalRing.maximalIdeal A) A) →+* MvPowerSeries (Fin 2) (AdicCompletion (IsLocalRing.maximalIdeal A) A)))
    let g₂ : (AdicCompletion (IsLocalRing.maximalIdeal A) A) →+* S := (mkS.comp (MvPowerSeries.C : (AdicCompletion (IsLocalRing.maximalIdeal A) A) →+* MvPowerSeries (Fin 2) (AdicCompletion (IsLocalRing.maximalIdeal A) A))).comp (σW : (AdicCompletion (IsLocalRing.maximalIdeal A) A) →+* (AdicCompletion (IsLocalRing.maximalIdeal A) A))
    have hg : g₁ = g₂ := by
      refine AdicCompletion.ringHom_eq_of_map_maximalIdeal_le_of_forall_apply_algebraMap_eq g₁ g₂
        (fun x hx => hθloc _ (hmkC x hx)) (fun x hx => hmkC _ (hσWloc x hx)) fun a => ?_
      show θ (mkS (MvPowerSeries.C (algebraMap A (AdicCompletion (IsLocalRing.maximalIdeal A) A) a))) = mkS (MvPowerSeries.C (σW (algebraMap A (AdicCompletion (IsLocalRing.maximalIdeal A) A) a)))
      rw [← hCONST a, hgermconst, hθcompat, hτCA, ← hgermconst, hCONST, hσW]
    intro w
    exact RingHom.congr_fun hg w
  ·
    intro jj
    have h1 := Ideal.mem_map_of_mem lam (hθ₀X jj)
    rw [map_sub, ← hθlam, hlammk, hlammk, MvPowerSeries.map_X, Ideal.map_pow, Ideal.map_span, Set.image_pair,
      hlammk, hlammk, MvPowerSeries.map_X, MvPowerSeries.map_X] at h1
    have h2 : MvPowerSeries.map ψ (∑ ii : Fin 2, MvPowerSeries.C (M₀ ii jj) * MvPowerSeries.X ii)
        = ∑ ii : Fin 2, MvPowerSeries.C (ψ (M₀ ii jj)) * MvPowerSeries.X ii := by
      rw [map_sum]
      refine Finset.sum_congr rfl fun ii _ => ?_
      rw [map_mul, MvPowerSeries.map_C, MvPowerSeries.map_X]
    rw [h2] at h1
    exact h1
  ·
    have h1 : algebraMap A (AdicCompletion (IsLocalRing.maximalIdeal A) A) (αt ^ (q + 1) - (((d : ZMod q).val : ℕ) : A)) ∈ IsLocalRing.maximalIdeal (AdicCompletion (IsLocalRing.maximalIdeal A) A) := by
      rw [AdicCompletion.maximalIdeal_eq_map]; exact Ideal.mem_map_of_mem _ hd
    rw [map_sub, map_natCast] at h1
    rw [show (((d : ZMod q).val : ℕ) : (AdicCompletion (IsLocalRing.maximalIdeal A) A)) - algebraMap A (AdicCompletion (IsLocalRing.maximalIdeal A) A) (αt ^ (q + 1))
        = -(algebraMap A (AdicCompletion (IsLocalRing.maximalIdeal A) A) (αt ^ (q + 1)) - (((d : ZMod q).val : ℕ) : (AdicCompletion (IsLocalRing.maximalIdeal A) A))) by ring]
    exact Submodule.neg_mem _ h1
  ·
    intro ii jj
    have h1 := hψloc _ (hM₀ ii jj)
    rw [map_sub, map_natCast] at h1
    have hq𝔪 : ((q : ℕ) : (AdicCompletion (IsLocalRing.maximalIdeal A) A)) ∈ IsLocalRing.maximalIdeal (AdicCompletion (IsLocalRing.maximalIdeal A) A) := by
      rw [AdicCompletion.maximalIdeal_eq_map, ← map_natCast (algebraMap A (AdicCompletion (IsLocalRing.maximalIdeal A) A))]
      exact Ideal.mem_map_of_mem _ hAq
    have h2 : ((((d : ZMod q) * (((ModularCurve.FullLevel.diagOneElem q (d ^ q)⁻¹ : CuspidalType.GL2 q) :
          Matrix (Fin 2) (Fin 2) (ZMod q)) ii jj)).val : ℕ) : (AdicCompletion (IsLocalRing.maximalIdeal A) A))
        - (((d : ZMod q).val : ℕ) : (AdicCompletion (IsLocalRing.maximalIdeal A) A)) * (((((ModularCurve.FullLevel.diagOneElem q (d ^ q)⁻¹ : CuspidalType.GL2 q) :
          Matrix (Fin 2) (Fin 2) (ZMod q)) ii jj).val : ℕ) : (AdicCompletion (IsLocalRing.maximalIdeal A) A)) ∈ IsLocalRing.maximalIdeal (AdicCompletion (IsLocalRing.maximalIdeal A) A) := by
      rw [ZMod.val_mul]
      set n : ℕ := (d : ZMod q).val * (((ModularCurve.FullLevel.diagOneElem q (d ^ q)⁻¹ : CuspidalType.GL2 q) :
          Matrix (Fin 2) (Fin 2) (ZMod q)) ii jj).val with hn
      have hdiv : ((n % q : ℕ) : (AdicCompletion (IsLocalRing.maximalIdeal A) A)) = (n : (AdicCompletion (IsLocalRing.maximalIdeal A) A)) - (q : (AdicCompletion (IsLocalRing.maximalIdeal A) A)) * ((n / q : ℕ) : (AdicCompletion (IsLocalRing.maximalIdeal A) A)) := by
        have h := congrArg (Nat.cast : ℕ → (AdicCompletion (IsLocalRing.maximalIdeal A) A)) (Nat.mod_add_div n q)
        simp only [Nat.cast_add, Nat.cast_mul] at h
        rw [eq_sub_iff_add_eq]; exact h
      rw [hdiv, hn, Nat.cast_mul]
      rw [show ((d : ZMod q).val : (AdicCompletion (IsLocalRing.maximalIdeal A) A)) * _ - (q : (AdicCompletion (IsLocalRing.maximalIdeal A) A)) * ((n / q : ℕ) : (AdicCompletion (IsLocalRing.maximalIdeal A) A)) - ((d : ZMod q).val : (AdicCompletion (IsLocalRing.maximalIdeal A) A)) * _
          = -((q : (AdicCompletion (IsLocalRing.maximalIdeal A) A)) * ((n / q : ℕ) : (AdicCompletion (IsLocalRing.maximalIdeal A) A))) by ring]
      exact Submodule.neg_mem _ (Ideal.mul_mem_right _ _ hq𝔪)
    have h3 := Ideal.add_mem _ h1 h2
    rwa [sub_add_sub_cancel] at h3

end S_ModularCurve_FullLevel_AuxLevel_inertia_drinfeldChart_baseChange_semilinear_linearPart_of_cyclotomicWitness_inertia_of_isAlgClosed
end P2MW
export P2MW.S_ModularCurve_FullLevel_AuxLevel_inertia_drinfeldChart_baseChange_semilinear_linearPart_of_cyclotomicWitness_inertia_of_isAlgClosed (solution)
