-- Prove2me | solution 1 for ModularCurve.NodeLocalized.exists_place_fieldOver_mem_iff_of_height_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/aed8ba0b-626b-5d38-9fa8-8ff5491c5a43

import Mathlib
import Theorems.Thm_IsIntegrallyClosed_exists_valuationSubring_mem_iff_of_height_eq_one
import Theorems.Thm_ModularCurve_jIntegralClosure_isNoetherian_and_isLocalization
import Theorems.Thm_ModularCurve_nonempty_modularPolynomialData
import Definitions.Def_ModularCurve_NodeDescent
import Definitions.Def_ModularCurve_NodeDescentTower
import Definitions.Def_AlgebraicCurve_ConstantFieldPullback
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_NodeLocalized_exists_place_fieldOver_mem_iff_of_height_one
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy ModularCurve.PhiGen.instNeZeroPhiGenCosetA"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply"
p2m_attr_erase "simp" "ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar"
set_option autoImplicit false

open AlgebraicCurve ModularCurve ModularCurve.NodeLocalized

theorem solution
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] (red : ↥A →+* k)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    (𝔭 : Ideal ↥(jIntegralClosure (1 * q) A K)) [𝔭.IsPrime] (h𝔭 : 𝔭.height = 1)
    (h𝔭K : ∀ b : ↥(coeffSubring A K), (b : AlgebraicClosure ℚ) ≠ 0 →
      ∀ hb : CharPReduction.constSeries (coeffSubring A K) b ∈ jIntegralClosure (1 * q) A K,
        (⟨_, hb⟩ : ↥(jIntegralClosure (1 * q) A K)) ∉ 𝔭) :
    ∃ V : Place ↥K ↥(fieldOver (1 * q) K), ∀ g : ↥(fieldOver (1 * q) K),
      g ∈ V.toValuationSubring ↔ ∃ r s : ↥(jIntegralClosure (1 * q) A K), s ∉ 𝔭 ∧
        (g : LaurentSeries (AlgebraicClosure ℚ)) * (s : LaurentSeries (AlgebraicClosure ℚ)) = r := by
  classical

  obtain ⟨data⟩ := ModularCurve.nonempty_modularPolynomialData q
  obtain ⟨hnoeth, hic, hfrac, -⟩ :=
    ModularCurve.jIntegralClosure_isNoetherian_and_isLocalization red (0 : k) data K
  haveI : IsNoetherianRing ↥(jIntegralClosure (1 * q) A K) := hnoeth
  haveI : IsIntegrallyClosed ↥(jIntegralClosure (1 * q) A K) := hic

  have hjF : jRing A K ≤ (fieldOver (1 * q) K).toSubring := by
    rw [jRing, Subring.closure_le]
    rintro x (⟨a, rfl⟩ | rfl)
    · exact Subfield.subset_closure (Or.inl ⟨⟨(a : AlgebraicClosure ℚ), a.2.2⟩, rfl⟩)
    · exact Subfield.subset_closure (Or.inr (Set.mem_insert _ _))
  have hjC : jRing A K ≤ jIntegralClosure (1 * q) A K := by
    intro y hy
    exact ⟨hjF hy, isIntegral_algebraMap (A := LaurentSeries (AlgebraicClosure ℚ))
      (x := (⟨y, hy⟩ : ↥(jRing A K)))⟩
  have hCF : jIntegralClosure (1 * q) A K ≤ (fieldOver (1 * q) K).toSubring := fun x hx => hx.1

  let ι : ↥(jIntegralClosure (1 * q) A K) →+* ↥(fieldOver (1 * q) K) :=
    { toFun := fun x => ⟨(x : LaurentSeries (AlgebraicClosure ℚ)), hCF x.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  letI : Algebra ↥(jIntegralClosure (1 * q) A K) ↥(fieldOver (1 * q) K) := ι.toAlgebra
  have hιcoe : ∀ x : ↥(jIntegralClosure (1 * q) A K), ((algebraMap ↥(jIntegralClosure (1 * q) A K) ↥(fieldOver (1 * q) K) x : ↥(fieldOver (1 * q) K)) :
      LaurentSeries (AlgebraicClosure ℚ)) = x := fun x => rfl
  have hιinj : Function.Injective (algebraMap ↥(jIntegralClosure (1 * q) A K) ↥(fieldOver (1 * q) K)) := by
    intro x y h
    exact Subtype.ext (congrArg (fun z : ↥(fieldOver (1 * q) K) => (z : LaurentSeries (AlgebraicClosure ℚ))) h)

  haveI : IsFractionRing ↥(jIntegralClosure (1 * q) A K) ↥(fieldOver (1 * q) K) := by
    refine ⟨?_, ?_, ?_⟩
    · rintro ⟨y, hy⟩
      apply IsUnit.mk0
      intro h0
      apply nonZeroDivisors.ne_zero hy
      exact hιinj (h0.trans (map_zero _).symm)
    · intro z
      obtain ⟨c, s, hc, hs, hs0, hzs⟩ := hfrac (z : LaurentSeries (AlgebraicClosure ℚ)) z.2
      have hs' : (⟨s, hjC hs⟩ : ↥(jIntegralClosure (1 * q) A K)) ≠ 0 := fun h => hs0 (congrArg Subtype.val h)
      refine ⟨⟨⟨c, hc⟩, ⟨⟨s, hjC hs⟩, mem_nonZeroDivisors_of_ne_zero hs'⟩⟩, ?_⟩
      exact Subtype.ext hzs
    · intro x y h
      exact ⟨1, by rw [hιinj h]⟩

  obtain ⟨V, hPIR, hne, hmem⟩ :=
    IsIntegrallyClosed.exists_valuationSubring_mem_iff_of_height_eq_one ↥(fieldOver (1 * q) K) 𝔭 h𝔭
  have hmem' : ∀ g : ↥(fieldOver (1 * q) K),
      (∃ r s : ↥(jIntegralClosure (1 * q) A K), s ∉ 𝔭 ∧ (g : LaurentSeries (AlgebraicClosure ℚ)) *
          (s : LaurentSeries (AlgebraicClosure ℚ)) = r) ↔ g ∈ V := by
    intro g
    rw [hmem]
    constructor
    · rintro ⟨r, s, hs, h⟩
      exact ⟨r, s, hs, Subtype.ext h⟩
    · rintro ⟨r, s, hs, h⟩
      exact ⟨r, s, hs, congrArg Subtype.val h⟩

  let ι₀ : ↥(coeffSubring A K) →+* ↥(jIntegralClosure (1 * q) A K) :=
    { toFun := fun a => ⟨CharPReduction.constSeries (coeffSubring A K) a,
        hjC (Subring.subset_closure (Or.inl ⟨a, rfl⟩))⟩
      map_one' := Subtype.ext (map_one _)
      map_mul' := fun x y => Subtype.ext (map_mul _ x y)
      map_zero' := Subtype.ext (map_zero _)
      map_add' := fun x y => Subtype.ext (map_add _ x y) }
  have hι₀coe : ∀ a : ↥(coeffSubring A K), ((ι₀ a : ↥(jIntegralClosure (1 * q) A K)) : LaurentSeries (AlgebraicClosure ℚ)) =
      algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) (a : AlgebraicClosure ℚ) :=
    fun a => rfl
  have h1not : (1 : ↥(jIntegralClosure (1 * q) A K)) ∉ 𝔭 := fun h =>
    (inferInstance : 𝔭.IsPrime).ne_top ((Ideal.eq_top_iff_one 𝔭).mpr h)

  have hK : ∀ c : ↥K, algebraMap ↥K ↥(fieldOver (1 * q) K) c ∈ V := by
    intro c
    rw [← hmem']
    by_cases hcA : (c : AlgebraicClosure ℚ) ∈ A
    · refine ⟨ι₀ ⟨c, hcA, c.2⟩, 1, h1not, ?_⟩
      rw [OneMemClass.coe_one, mul_one, hι₀coe, algebraMap_fieldOver_coe]
    · have hc0 : (c : AlgebraicClosure ℚ) ≠ 0 := fun h => hcA (h ▸ A.zero_mem)
      have hcinv : (c : AlgebraicClosure ℚ)⁻¹ ∈ A := (A.mem_or_inv_mem _).resolve_left hcA
      have hcinvK : (c : AlgebraicClosure ℚ)⁻¹ ∈ K.toSubalgebra.toSubring := (c⁻¹ : ↥K).2
      let x : ↥(coeffSubring A K) := ⟨(c : AlgebraicClosure ℚ)⁻¹, hcinv, hcinvK⟩
      have hx0 : x ≠ 0 := fun h => inv_ne_zero hc0 (congrArg Subtype.val h)
      have hxp : ι₀ x ∉ 𝔭 := h𝔭K x (inv_ne_zero hc0) _
      refine ⟨1, ι₀ x, hxp, ?_⟩
      rw [OneMemClass.coe_one, hι₀coe, algebraMap_fieldOver_coe, ← map_mul, mul_inv_cancel₀ hc0, map_one]
  exact ⟨⟨V, hK, hne, hPIR⟩, fun g => (hmem' g).symm⟩

end S_ModularCurve_NodeLocalized_exists_place_fieldOver_mem_iff_of_height_one
end P2MW
export P2MW.S_ModularCurve_NodeLocalized_exists_place_fieldOver_mem_iff_of_height_one (solution)
