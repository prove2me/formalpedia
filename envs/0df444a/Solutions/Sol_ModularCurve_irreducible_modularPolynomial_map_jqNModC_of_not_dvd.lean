-- Prove2me | solution 1 for ModularCurve.irreducible_modularPolynomial_map_jqNModC_of_not_dvd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/f3c6c3a8-9a8a-5a1a-88ed-f641f7eb3841

import Mathlib
import Definitions.Def_ModularCurve_X0
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_X0ModL
import Theorems.Thm_ModularCurve_modularFunctionFieldC_eq_modularFunctionFieldFullC
import Theorems.Thm_ModularCurve_ModularPolynomialData_eval_jqNModC_mul_eq_zero
import Theorems.Thm_ModularCurve_dedekindPsi_mul_prime
import Theorems.Thm_ModularCurve_relfinrank_modularFunctionFieldFullC_mul_dedekindPsi
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_irreducible_modularPolynomial_map_jqNModC_of_not_dvd
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instSMulAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instDistribMulActionAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.baseAut_arithmeticGalois ModularCurve.JZero.torsionGaloisRep_apply ModularCurve.coe_arithmeticRingAut_apply ModularCurve.toRingAut_arithmeticGalois AlgebraicCurve.SemilinearAut.toRingAut_inv"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul ModularCurve.coe_jGeomGen ModularCurve.coe_jNGeomGen ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion"
p2m_attr_erase "simp" "AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply ModularCurve.charLGeomModuliDictionary_single ModularCurve.specializeModuli_single ModularCurve.specializePlace_def AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one"

set_option autoImplicit false

noncomputable section

open Polynomial IntermediateField

namespace ModularCurve
p2m_export "ModularCurve" "dedekindPsi ModularPolynomialData jqModC jqNModC modularFunctionFieldC jqModC_mem jqNModC_mem jqModCd_mem_full jqModC_mem_full modularFunctionFieldC_eq_modularFunctionFieldFullC dedekindPsi_mul_prime relfinrank_modularFunctionFieldFullC_mul_dedekindPsi"
p2m_open "ModularCurve~dedekindPsi_prime"

namespace DegRel

section Shortcuts
variable (K : Type*) [Field K]

noncomputable scoped instance (priority := high) instMulActionLaurentSeriesShortcut :
    MulAction K (LaurentSeries K) :=
  (Module.toDistribMulAction (R := K) (M := LaurentSeries K)).toMulAction
end Shortcuts

variable (κ : Type*) [Field κ] (N : ℕ) [NeZero N] (ℓ : ℕ) [Fact ℓ.Prime]

abbrev F : IntermediateField κ (LaurentSeries κ) := modularFunctionFieldC κ N

abbrev xN : F κ N := ⟨jqNModC κ N, jqNModC_mem κ N⟩

variable {ℓ} in

abbrev P (dataℓ : ModularPolynomialData ℓ) : Polynomial (F κ N) :=
  dataℓ.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom (F κ N)) (xN κ N))

theorem dedekindPsi_pos (M : ℕ) [NeZero M] : 0 < dedekindPsi M := by
  unfold dedekindPsi
  have h1 : (1 : ℕ) ∈ M.divisors.filter Squarefree :=
    Finset.mem_filter.mpr ⟨Nat.one_mem_divisors.mpr (NeZero.ne M), squarefree_one⟩
  calc 0 < M / 1 := by rw [Nat.div_one]; exact Nat.pos_of_ne_zero (NeZero.ne M)
    _ ≤ ∑ d ∈ M.divisors.filter Squarefree, M / d :=
        Finset.single_le_sum (f := fun d => M / d) (fun _ _ => Nat.zero_le _) h1

theorem aeval_P (dataℓ : ModularPolynomialData ℓ) :
    Polynomial.aeval (jqNModC κ (N * ℓ)) (P κ N dataℓ) = 0 := by
  have hcomp : (algebraMap (F κ N) (LaurentSeries κ)).comp
        (Polynomial.eval₂RingHom (Int.castRingHom (F κ N)) (xN κ N)) =
      Polynomial.eval₂RingHom (Int.castRingHom (LaurentSeries κ)) (jqNModC κ N) := by
    refine Polynomial.ringHom_ext' (RingHom.ext_int _ _) ?_
    simp only [RingHom.coe_comp, Function.comp_apply, Polynomial.coe_eval₂RingHom,
      Polynomial.eval₂_X]
    rfl
  have hhom : (Polynomial.aeval (R := ℤ) (jqNModC κ N)).toRingHom =
      Polynomial.eval₂RingHom (Int.castRingHom (LaurentSeries κ)) (jqNModC κ N) := by
    refine Polynomial.ringHom_ext' (RingHom.ext_int _ _) ?_
    show Polynomial.aeval (jqNModC κ N) (Polynomial.X : Polynomial ℤ) = _
    rw [Polynomial.aeval_X, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X]
  rw [Polynomial.aeval_def, Polynomial.eval₂_map, hcomp, ← hhom]
  exact dataℓ.eval_jqNModC_mul_eq_zero κ N

theorem F_le (p : ℕ) [Fact p.Prime] [CharP κ p] (hpNℓ : ¬ p ∣ N * ℓ) :
    F κ N ≤ modularFunctionFieldC κ (N * ℓ) := by
  rw [modularFunctionFieldC_eq_modularFunctionFieldFullC κ p (N * ℓ) hpNℓ]
  show modularFunctionFieldC κ N ≤ _
  unfold modularFunctionFieldC
  rw [IntermediateField.adjoin_le_iff]
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl
  · exact jqModC_mem_full κ (N * ℓ)
  · exact jqModCd_mem_full κ (N * ℓ) (dvd_mul_right N ℓ)

theorem adjoin_eq_extendScalars (p : ℕ) [Fact p.Prime] [CharP κ p] (hpNℓ : ¬ p ∣ N * ℓ) :
    IntermediateField.adjoin (F κ N) ({jqNModC κ (N * ℓ)} : Set (LaurentSeries κ)) =
      IntermediateField.extendScalars (F_le κ N ℓ p hpNℓ) := by
  apply le_antisymm
  · rw [IntermediateField.adjoin_simple_le_iff, IntermediateField.mem_extendScalars]
    exact jqNModC_mem κ (N * ℓ)
  · intro x hx
    rw [IntermediateField.mem_extendScalars] at hx
    have ha : jqModC κ ∈ IntermediateField.adjoin (F κ N) ({jqNModC κ (N * ℓ)} : Set (LaurentSeries κ)) := by
      have h := (IntermediateField.adjoin (F κ N)
        ({jqNModC κ (N * ℓ)} : Set (LaurentSeries κ))).algebraMap_mem (⟨jqModC κ, jqModC_mem κ N⟩ : F κ N)
      rwa [IntermediateField.algebraMap_apply] at h
    have hb : jqNModC κ (N * ℓ) ∈
        IntermediateField.adjoin (F κ N) ({jqNModC κ (N * ℓ)} : Set (LaurentSeries κ)) :=
      IntermediateField.mem_adjoin_simple_self (F κ N) (jqNModC κ (N * ℓ))
    have hle : modularFunctionFieldC κ (N * ℓ) ≤
        (IntermediateField.adjoin (F κ N) ({jqNModC κ (N * ℓ)} : Set (LaurentSeries κ))).restrictScalars κ := by
      unfold modularFunctionFieldC
      exact IntermediateField.adjoin_le_iff.mpr
        (Set.insert_subset_iff.mpr ⟨ha, Set.singleton_subset_iff.mpr hb⟩)
    exact (IntermediateField.mem_restrictScalars κ).mp (hle hx)

theorem finrank_adjoin (p : ℕ) [Fact p.Prime] [CharP κ p] (hℓN : ¬ ℓ ∣ N)
    (hpN : ¬ p ∣ N) (hpNℓ : ¬ p ∣ N * ℓ) :
    Module.finrank (F κ N) (IntermediateField.adjoin (F κ N) ({jqNModC κ (N * ℓ)} : Set (LaurentSeries κ))) =
      ℓ + 1 := by
  rw [adjoin_eq_extendScalars κ N ℓ p hpNℓ, ← IntermediateField.relfinrank_eq_finrank_of_le (F_le κ N ℓ p hpNℓ)]
  have hNℓ : ((N * ℓ : ℕ) : κ) ≠ 0 := by
    rw [Ne, CharP.cast_eq_zero_iff κ p]
    exact hpNℓ
  have h1 := (relfinrank_modularFunctionFieldFullC_mul_dedekindPsi κ N ℓ hNℓ).1
  rw [← modularFunctionFieldC_eq_modularFunctionFieldFullC κ p N hpN,
    ← modularFunctionFieldC_eq_modularFunctionFieldFullC κ p (N * ℓ) hpNℓ,
    dedekindPsi_mul_prime N ℓ Fact.out, if_neg hℓN] at h1
  exact Nat.eq_of_mul_eq_mul_right (dedekindPsi_pos N) h1

theorem dedekindPsi_prime : dedekindPsi ℓ = ℓ + 1 := by
  have hℓ : ℓ.Prime := Fact.out
  have h := dedekindPsi_mul_prime 1 ℓ hℓ
  rw [one_mul, if_neg (fun hd => hℓ.ne_one (Nat.dvd_one.mp hd))] at h
  have h1 : dedekindPsi 1 = 1 := by
    simp [dedekindPsi, Finset.filter_singleton, squarefree_one]
  rw [h1, mul_one] at h
  exact h

theorem main (p : ℕ) [Fact p.Prime] [CharP κ p] (hℓN : ¬ ℓ ∣ N) (hpN : ¬ p ∣ N) (hpℓ : p ≠ ℓ)
    (dataℓ : ModularPolynomialData ℓ) : Irreducible (P κ N dataℓ) := by
  have hp : p.Prime := Fact.out
  have hℓ : ℓ.Prime := Fact.out
  have hpNℓ : ¬ p ∣ N * ℓ := by
    intro h
    rcases (Nat.Prime.dvd_mul hp).1 h with h1 | h2
    · exact hpN h1
    · exact hpℓ ((Nat.prime_dvd_prime_iff_eq hp hℓ).1 h2)
  have hmonic : (P κ N dataℓ).Monic := dataℓ.monic.map _
  have hint : IsIntegral (F κ N) (jqNModC κ (N * ℓ)) :=
    ⟨P κ N dataℓ, hmonic, by rw [← Polynomial.aeval_def]; exact aeval_P κ N ℓ dataℓ⟩
  have hPdeg : (P κ N dataℓ).natDegree = ℓ + 1 := by
    show (dataℓ.Φ.map _).natDegree = _
    rw [dataℓ.monic.natDegree_map, dataℓ.natDegree_eq, dedekindPsi_prime ℓ]
  have hdeg : (minpoly (F κ N) (jqNModC κ (N * ℓ))).natDegree = (P κ N dataℓ).natDegree := by
    rw [← IntermediateField.adjoin.finrank hint, finrank_adjoin κ N ℓ p hℓN hpN hpNℓ, hPdeg]
  have heq : P κ N dataℓ = minpoly (F κ N) (jqNModC κ (N * ℓ)) :=
    (Polynomial.eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hint) hmonic
      (minpoly.dvd _ _ (aeval_P κ N ℓ dataℓ)) (le_of_eq hdeg.symm))
  rw [heq]
  exact minpoly.irreducible hint

end DegRel
p2m_reactivate "P2MW.S_ModularCurve_irreducible_modularPolynomial_map_jqNModC_of_not_dvd.ModularCurve.DegRel"

end ModularCurve
p2m_reactivate "P2MW.S_ModularCurve_irreducible_modularPolynomial_map_jqNModC_of_not_dvd.ModularCurve.DegRel P2MW.S_ModularCurve_irreducible_modularPolynomial_map_jqNModC_of_not_dvd.ModularCurve"

end
p2m_reactivate "P2MW.S_ModularCurve_irreducible_modularPolynomial_map_jqNModC_of_not_dvd.ModularCurve.DegRel P2MW.S_ModularCurve_irreducible_modularPolynomial_map_jqNModC_of_not_dvd.ModularCurve"

theorem solution
    (κ : Type*) [Field κ] (p : ℕ) [Fact p.Prime] [CharP κ p]
    (N : ℕ) [NeZero N] (ℓ : ℕ) [Fact ℓ.Prime] (hℓN : ¬ ℓ ∣ N) (hpN : ¬ p ∣ N) (hpℓ : p ≠ ℓ)
    (dataℓ : ModularCurve.ModularPolynomialData ℓ) :
    Irreducible (dataℓ.Φ.map (Polynomial.eval₂RingHom
      (Int.castRingHom ↥(ModularCurve.modularFunctionFieldC κ N))
      ⟨ModularCurve.jqNModC κ N, ModularCurve.jqNModC_mem κ N⟩)) :=
  ModularCurve.DegRel.main κ N ℓ p hℓN hpN hpℓ dataℓ

#print axioms solution

end S_ModularCurve_irreducible_modularPolynomial_map_jqNModC_of_not_dvd
end P2MW
export P2MW.S_ModularCurve_irreducible_modularPolynomial_map_jqNModC_of_not_dvd (solution)
