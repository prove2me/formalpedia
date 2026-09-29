-- Prove2me | solution 1 for ModularCurve.XHDRLevel.relfinrank_qExpFunctionFieldC_gammaH_infSubgroup_gammaH_eq_add_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/a6b99a31-442d-562b-ba61-c893520ab807

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_GaloisRep_RatLocalizedAtResidue
import Theorems.Thm_ModularCurve_relfinrank_qExpFunctionFieldC_gamma0_gammaH_eq_index_of_charZero
import Theorems.Thm_ModularCurve_dedekindPsi_le_finrank_adjoin_qExpFunctionFieldC_gamma0
import Theorems.Thm_ModularCurve_finiteDimensional_and_finrank_adjoin_jqModC_qExpFunctionFieldC_le_index
import Theorems.Thm_ModularCurve_card_quotient_gamma0_eq_index
import Theorems.Thm_ModularCurve_card_quotient_gamma0_le_dedekindPsi
import Theorems.Thm_ModularCurve_dedekindPsi_mul_prime
import Theorems.Thm_ModularCurve_GammaH_le_GammaH_div_infSubgroup
import Theorems.Thm_ModularCurve_modularFunctionFieldFullC_le_qExpFunctionFieldC_gamma0
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XHDRLevel_relfinrank_qExpFunctionFieldC_gammaH_infSubgroup_gammaH_eq_add_one
p2m_attr_erase "instance" "ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid"
p2m_attr_erase "simp" "WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply"
p2m_attr_erase "simp" "AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.ProjectiveLine.map_mk"

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1600000

open ModularCurve ModularCurve.XHDRLevel IntermediateField CongruenceSubgroup
open scoped MatrixGroups

namespace Gamma2Sol

theorem relfinrank_adjoin_eq_finrank {K E : Type*} [Field K] [Field E] [Algebra K E]
    (B : IntermediateField K E) (x : B) :
    relfinrank (adjoin K ({(x : E)} : Set E)) B = Module.finrank (adjoin K ({x} : Set B)) B := by
  have hc : (adjoin K ({(x : E)} : Set E)).comap B.val = adjoin K ({x} : Set B) := by
    apply le_antisymm
    · intro y hy
      change B.val y ∈ adjoin K ({(x : E)} : Set E) at hy
      have h' : (y : E) ∈ lift (adjoin K ({x} : Set B)) := by
        rw [lift_adjoin_simple]; exact hy
      exact (IntermediateField.mem_lift y).mp h'
    · rw [adjoin_le_iff, Set.singleton_subset_iff, SetLike.mem_coe]
      change B.val x ∈ adjoin K ({(x : E)} : Set E)
      exact mem_adjoin_simple_self K (x : E)
  have h := IntermediateField.finrank_comap B.val (A := adjoin K ({(x : E)} : Set E))
  rw [fieldRange_val] at h
  rw [← h]
  exact congrArg (fun C : IntermediateField K B => Module.finrank C B) hc

theorem relfinrank_gamma0_eq_dedekindPsi (N : ℕ) [NeZero N] (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (Gamma0 N)) :
    relfinrank (adjoin ℚ ({jqModC ℚ} : Set (LaurentSeries ℚ))) (qExpFunctionFieldC ℚ (Gamma0 N)) = dedekindPsi N := by
  let x : ↥(qExpFunctionFieldC ℚ (Gamma0 N)) := ⟨jqModC ℚ, hj⟩
  have hT : ModularGroup.T ∈ Gamma0 N := by rw [Gamma0_mem]; simp [ModularGroup.T]
  obtain ⟨hfd, hle⟩ := ModularCurve.finiteDimensional_and_finrank_adjoin_jqModC_qExpFunctionFieldC_le_index ℚ (Gamma0 N) hT
    (Gamma0 N) le_rfl (fun γ h => Or.inl h) x rfl
  haveI := hfd
  have hlow := ModularCurve.dedekindPsi_le_finrank_adjoin_qExpFunctionFieldC_gamma0 ℚ N (NeZero.natCast_ne N ℚ) x rfl
  have hidx : (Gamma0 N).index ≤ dedekindPsi N := by
    rw [← ModularCurve.card_quotient_gamma0_eq_index N]
    exact ModularCurve.card_quotient_gamma0_le_dedekindPsi N
  rw [show (jqModC ℚ) = ((x : ↥(qExpFunctionFieldC ℚ (Gamma0 N))) : LaurentSeries ℚ) from rfl, relfinrank_adjoin_eq_finrank]
  exact le_antisymm (hle.trans hidx) hlow

theorem index_sup_eq (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) :
    (H ⊔ Subgroup.zpowers (-1 : (ZMod M)ˣ)).index =
      (infSubgroup p M H hpM ⊔ Subgroup.zpowers (-1 : (ZMod (M / p))ˣ)).index := by
  haveI : NeZero (M / p) := neZero_div p M hpM
  set π := ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) with hπ
  have hsurj : Function.Surjective π := ZMod.unitsMap_surjective _
  have hπneg : π (-1) = -1 := by
    apply Units.ext
    rw [hπ, ZMod.unitsMap_def, Units.coe_map, Units.val_neg, Units.val_one, MonoidHom.coe_coe, map_neg, map_one,
      Units.val_neg, Units.val_one]
  have hcomap : (infSubgroup p M H hpM ⊔ Subgroup.zpowers (-1 : (ZMod (M / p))ˣ)).comap π =
      H ⊔ Subgroup.zpowers (-1 : (ZMod M)ˣ) := by
    apply le_antisymm
    · intro u hu
      rw [Subgroup.mem_comap] at hu
      obtain ⟨y, hy, z, hz, hyz⟩ := Subgroup.mem_sup.mp hu
      rw [mem_infSubgroup_iff] at hy
      obtain ⟨d, hdH, rfl⟩ := hy
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz

      have hker : π (u * (d * (-1) ^ k)⁻¹) = 1 := by
        rw [map_mul, map_inv, map_mul, map_zpow, hπneg, hyz, mul_inv_cancel]
      have hmem : u * (d * (-1) ^ k)⁻¹ ∈ H := hHp _ hker
      have : u = (u * (d * (-1) ^ k)⁻¹ * d) * (-1) ^ k := by group
      rw [this]
      exact Subgroup.mem_sup.mpr ⟨_, H.mul_mem hmem hdH, (-1) ^ k, Subgroup.zpow_mem_zpowers _ k, rfl⟩
    · rw [sup_le_iff]
      constructor
      · intro d hd
        rw [Subgroup.mem_comap]
        exact Subgroup.mem_sup_left ((mem_infSubgroup_iff p M H hpM _).mpr ⟨d, hd, rfl⟩)
      · rw [Subgroup.zpowers_le, Subgroup.mem_comap, hπneg]
        exact Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
  rw [← hcomap, Subgroup.index_comap_of_surjective _ hsurj]

end Gamma2Sol

open Gamma2Sol in
theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) :
    IntermediateField.relfinrank (qExpFunctionFieldC ℚ (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM)))
      (qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) = p + 1 := by
  haveI : NeZero (M / p) := neZero_div p M hpM
  have hp : p.Prime := Fact.out

  have hndvd : ¬ p ∣ M / p := by
    intro hd; apply hpM2
    obtain ⟨k, hk⟩ := hd
    exact ⟨k, by calc M = p * (M / p) := (Nat.mul_div_cancel' hpM).symm
      _ = p ^ 2 * k := by rw [hk]; ring⟩

  have hj0 : ∀ (K : ℕ) [NeZero K], jqModC ℚ ∈ qExpFunctionFieldC ℚ (Gamma0 K) := by
    intro K _
    have h := ModularCurve.jqModCd_mem_full (K := ℚ) (N := K) (d := 1) (one_dvd K)
    rw [qExpand_one_apply] at h
    exact ModularCurve.modularFunctionFieldFullC_le_qExpFunctionFieldC_gamma0 ℚ K h

  set J : IntermediateField ℚ (LaurentSeries ℚ) := adjoin ℚ ({jqModC ℚ} : Set (LaurentSeries ℚ)) with hJ
  set F0N := qExpFunctionFieldC ℚ (Gamma0 (M / p)) with hF0N
  set F0M := qExpFunctionFieldC ℚ (Gamma0 M) with hF0M
  set FN := qExpFunctionFieldC ℚ (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM)) with hFN
  set FM := qExpFunctionFieldC ℚ (CohCarrier.GammaH M H) with hFM
  have hJ0N : J ≤ F0N := by rw [hJ, adjoin_le_iff, Set.singleton_subset_iff]; exact hj0 (M / p)
  have hJ0M : J ≤ F0M := by rw [hJ, adjoin_le_iff, Set.singleton_subset_iff]; exact hj0 M
  have h0N_N : F0N ≤ FN := qExpFunctionFieldC_mono ℚ (CohCarrier.GammaH_le_Gamma0 _)
  have h0M_M : F0M ≤ FM := qExpFunctionFieldC_mono ℚ (CohCarrier.GammaH_le_Gamma0 _)
  have hN_M : FN ≤ FM := qExpFunctionFieldC_mono ℚ (ModularCurve.GammaH_le_GammaH_div_infSubgroup p M H hpM)

  have dN : relfinrank J F0N = dedekindPsi (M / p) := relfinrank_gamma0_eq_dedekindPsi (M / p) (hj0 _)
  have dM : relfinrank J F0M = dedekindPsi M := relfinrank_gamma0_eq_dedekindPsi M (hj0 _)
  have eN : relfinrank F0N FN = (infSubgroup p M H hpM ⊔ Subgroup.zpowers (-1 : (ZMod (M / p))ˣ)).index :=
    ModularCurve.relfinrank_qExpFunctionFieldC_gamma0_gammaH_eq_index_of_charZero ℚ (M / p) (infSubgroup p M H hpM)
  have eM : relfinrank F0M FM = (H ⊔ Subgroup.zpowers (-1 : (ZMod M)ˣ)).index :=
    ModularCurve.relfinrank_qExpFunctionFieldC_gamma0_gammaH_eq_index_of_charZero ℚ M H
  have hidx : (H ⊔ Subgroup.zpowers (-1 : (ZMod M)ˣ)).index =
      (infSubgroup p M H hpM ⊔ Subgroup.zpowers (-1 : (ZMod (M / p))ˣ)).index := index_sup_eq p M H hpM hHp
  have hpsi : dedekindPsi M = (p + 1) * dedekindPsi (M / p) := by
    conv_lhs => rw [← Nat.div_mul_cancel hpM]
    rw [ModularCurve.dedekindPsi_mul_prime (M / p) p hp, if_neg hndvd]

  have t1 := relfinrank_mul_relfinrank hJ0M h0M_M
  have t2 := relfinrank_mul_relfinrank hJ0N h0N_N
  have t3 := relfinrank_mul_relfinrank (hJ0N.trans h0N_N) hN_M
  rw [dM, eM, hidx, hpsi] at t1
  rw [dN, eN] at t2
  rw [← t2, ← t1] at t3

  have hψ : 0 < dedekindPsi (M / p) := by
    haveI : (Gamma0 (M / p)).FiniteIndex := Subgroup.finiteIndex_of_le (Gamma1_in_Gamma0 _)
    have h1 : 0 < (Gamma0 (M / p)).index := Nat.pos_of_ne_zero Subgroup.FiniteIndex.index_ne_zero
    have h2 : (Gamma0 (M / p)).index ≤ dedekindPsi (M / p) := by
      rw [← ModularCurve.card_quotient_gamma0_eq_index]; exact ModularCurve.card_quotient_gamma0_le_dedekindPsi _
    omega
  have hpos : 0 < dedekindPsi (M / p) * (infSubgroup p M H hpM ⊔ Subgroup.zpowers (-1 : (ZMod (M / p))ˣ)).index :=
    Nat.mul_pos hψ (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite)
  have : dedekindPsi (M / p) * (infSubgroup p M H hpM ⊔ Subgroup.zpowers (-1 : (ZMod (M / p))ˣ)).index *
      relfinrank FN FM =
      dedekindPsi (M / p) * (infSubgroup p M H hpM ⊔ Subgroup.zpowers (-1 : (ZMod (M / p))ˣ)).index * (p + 1) := by
    rw [t3]; ring
  exact Nat.eq_of_mul_eq_mul_left hpos this

end S_ModularCurve_XHDRLevel_relfinrank_qExpFunctionFieldC_gammaH_infSubgroup_gammaH_eq_add_one
end P2MW
export P2MW.S_ModularCurve_XHDRLevel_relfinrank_qExpFunctionFieldC_gammaH_infSubgroup_gammaH_eq_add_one (solution)
