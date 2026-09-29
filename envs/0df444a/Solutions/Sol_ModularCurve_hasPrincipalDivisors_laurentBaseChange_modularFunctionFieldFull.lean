-- Prove2me | solution 1 for ModularCurve.hasPrincipalDivisors_laurentBaseChange_modularFunctionFieldFull
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/4482b742-e52e-5fc5-a0f0-53e2ebb1b589

import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_PhiGen
import Theorems.Thm_AlgebraicCurve_hasPrincipalDivisors_adjoin_of_transcendental
import Theorems.Thm_ModularCurve_isIntegral_jqNModC_all_of_modularPolynomialFamily
import Theorems.Thm_ModularCurve_laurentBaseChange_modularFunctionFieldFull
import Theorems.Thm_ModularCurve_transcendental_jqModC
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_hasPrincipalDivisors_laurentBaseChange_modularFunctionFieldFull
p2m_attr_erase "instance" "AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy"
p2m_attr_erase "simp" "AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply"

noncomputable section
open IntermediateField

namespace ModularCurve
p2m_export "ModularCurve" "modularFunctionFieldFull laurentBaseChange jqModC jqNModC jqNModC_one ModularPolynomialFamily isIntegral_jqNModC_all_of_modularPolynomialFamily laurentBaseChange_modularFunctionFieldFull transcendental_jqModC"
p2m_open "ModularCurve"
namespace R8

def gens (L : Type*) [Field L] (N : ℕ) : Finset (LaurentSeries L) := by
  classical
  exact Finset.univ.image fun d : {d // d ∈ N.divisors} =>
    @jqNModC L _ d.1 ⟨Nat.ne_of_gt (Nat.pos_of_mem_divisors d.2)⟩

theorem mem_gens_iff (L : Type*) [Field L] (N : ℕ) [NeZero N] (x : LaurentSeries L) :
    x ∈ gens L N ↔ ∃ (d : ℕ) (_ : NeZero d), d ∣ N ∧ x = jqNModC L d := by
  classical
  unfold gens
  constructor
  · intro hx
    obtain ⟨d, -, rfl⟩ := Finset.mem_image.mp hx
    exact ⟨d.1, ⟨Nat.ne_of_gt (Nat.pos_of_mem_divisors d.2)⟩, Nat.dvd_of_mem_divisors d.2, rfl⟩
  · rintro ⟨d, hd, hdN, rfl⟩
    exact Finset.mem_image.mpr ⟨⟨d, Nat.mem_divisors.mpr ⟨hdN, NeZero.ne N⟩⟩, Finset.mem_univ _, rfl⟩

theorem insert_gens (L : Type*) [Field L] (N : ℕ) [NeZero N] :
    insert (jqModC L) (gens L N : Set (LaurentSeries L)) = {x | ∃ (d : ℕ) (_ : NeZero d), d ∣ N ∧ x = jqNModC L d} := by
  ext x
  simp only [Set.mem_insert_iff, Finset.mem_coe, mem_gens_iff, Set.mem_setOf_eq]
  constructor
  · rintro (rfl | h)
    · exact ⟨1, inferInstance, one_dvd N, (jqNModC_one L).symm⟩
    · exact h
  · exact Or.inr

end R8
end ModularCurve

p2m_open "ModularCurve P2MW.S_ModularCurve_hasPrincipalDivisors_laurentBaseChange_modularFunctionFieldFull.ModularCurve AlgebraicCurve"

theorem solution (L : Type*) [Field L] [Algebra ℚ L]
    (hΦ : ModularPolynomialFamily) (N : ℕ) [NeZero N] :
    HasPrincipalDivisors L (laurentBaseChange L (modularFunctionFieldFull N)) := by
  haveI : CharZero L := charZero_of_injective_algebraMap (algebraMap ℚ L).injective
  rw [laurentBaseChange_modularFunctionFieldFull, ← ModularCurve.R8.insert_gens]
  refine AlgebraicCurve.hasPrincipalDivisors_adjoin_of_transcendental L (jqModC L) (transcendental_jqModC L)
    (ModularCurve.R8.gens L N) ?_
  intro t ht
  obtain ⟨d, hd, -, rfl⟩ := (ModularCurve.R8.mem_gens_iff L N t).mp ht
  exact isIntegral_jqNModC_all_of_modularPolynomialFamily L hΦ d

end

end S_ModularCurve_hasPrincipalDivisors_laurentBaseChange_modularFunctionFieldFull
end P2MW
export P2MW.S_ModularCurve_hasPrincipalDivisors_laurentBaseChange_modularFunctionFieldFull (solution)
