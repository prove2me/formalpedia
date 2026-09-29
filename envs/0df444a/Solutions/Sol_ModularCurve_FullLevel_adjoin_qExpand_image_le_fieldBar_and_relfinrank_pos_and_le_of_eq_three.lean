-- Prove2me | solution 1 for ModularCurve.FullLevel.adjoin_qExpand_image_le_fieldBar_and_relfinrank_pos_and_le_of_eq_three
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.339302+00:00
-- url     : https://prove2.me/submissions/b8f3e8b0-f687-5277-a25b-e5c47c7f25d0

import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_ModularCurve_JqCoeff
import Theorems.Thm_ModularCurve_finrank_adjoin_jqModC_laurentBaseChange_qExpFunctionFieldC_gamma0_eq_index
import Theorems.Thm_ModularCurve_Gamma0_index
import Theorems.Thm_ModularCurve_dedekindPsi_mul_prime
import Theorems.Thm_ModularCurve_FullLevel_qExpand_coe_mem_fieldBar_of_mem
import Theorems.Thm_ModularCurve_jqModC_mem_intFormRatiosC
import Theorems.Thm_ModularCurve_FullLevel_relfinrank_adjoin_qExpand_image_laurentBaseChange_gamma0_fieldBar_le_of_eq_three
import Theorems.Thm_ModularCurve_FullLevel_relfinrank_adjoin_qExpand_image_laurentBaseChange_gamma0_fieldBar_ne_zero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_adjoin_qExpand_image_le_fieldBar_and_relfinrank_pos_and_le_of_eq_three
p2m_attr_erase "instance" "ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid"
p2m_attr_erase "simp" "ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal"
p2m_attr_erase "simp" "AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen"
p2m_attr_erase "simp" "ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.qExpandAlgHomC_apply WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply ModularCurve.ProjectiveLine.map_mk"

set_option autoImplicit false

p2m_open "ModularCurve P2MW.S_ModularCurve_FullLevel_adjoin_qExpand_image_le_fieldBar_and_relfinrank_pos_and_le_of_eq_three.ModularCurve ModularCurve.FullLevel P2MW.S_ModularCurve_FullLevel_adjoin_qExpand_image_le_fieldBar_and_relfinrank_pos_and_le_of_eq_three.ModularCurve.FullLevel CongruenceSubgroup"
open scoped MatrixGroups

noncomputable section

namespace ModularCurve
p2m_export "ModularCurve" "qExpFunctionFieldC intFormRatiosC_subset qExpFunctionFieldC_mono qExpand qExpand_C dedekindPsi coeffEmb laurentBaseChange coeffEmb_mem_laurentBaseChange jqModC map_jqModC finrank_adjoin_jqModC_laurentBaseChange_qExpFunctionFieldC_gamma0_eq_index Gamma0_index dedekindPsi_mul_prime FullLevel.qExpand_coe_mem_fieldBar_of_mem jqModC_mem_intFormRatiosC FullLevel.relfinrank_adjoin_qExpand_image_laurentBaseChange_gamma0_fieldBar_le_of_eq_three FullLevel.relfinrank_adjoin_qExpand_image_laurentBaseChange_gamma0_fieldBar_ne_zero"
namespace FullLevel
p2m_export "ModularCurve.FullLevel" "fieldBar qExpand_coe_mem_fieldBar_of_mem relfinrank_adjoin_qExpand_image_laurentBaseChange_gamma0_fieldBar_le_of_eq_three relfinrank_adjoin_qExpand_image_laurentBaseChange_gamma0_fieldBar_ne_zero"
namespace DegRoad
p2m_open "ModularCurve.FullLevel ModularCurve"

open IntermediateField

variable (q : ℕ) [Fact q.Prime]

abbrev KL (N : ℕ) : IntermediateField (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) :=
  laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (Gamma0 N))

def qExpandBar (N : ℕ) [NeZero N] :
    LaurentSeries (AlgebraicClosure ℚ) →ₐ[AlgebraicClosure ℚ] LaurentSeries (AlgebraicClosure ℚ) where
  __ := qExpand (AlgebraicClosure ℚ) N
  commutes' r := by
    show qExpand (AlgebraicClosure ℚ) N (algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) r) =
      algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) r
    have h1 : algebraMap (AlgebraicClosure ℚ) (PowerSeries (AlgebraicClosure ℚ)) r = PowerSeries.C r := by
      simp
    rw [HahnSeries.algebraMap_apply', h1, HahnSeries.ofPowerSeries_C, qExpand_C]

@[scoped simp] theorem qExpandBar_apply (N : ℕ) [NeZero N] (f : LaurentSeries (AlgebraicClosure ℚ)) :
    qExpandBar N f = qExpand (AlgebraicClosure ℚ) N f := rfl

def KX (N : ℕ) : IntermediateField (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) :=
  (KL N).map (qExpandBar q)

theorem mem_KX_iff (N : ℕ) (x : LaurentSeries (AlgebraicClosure ℚ)) :
    x ∈ KX q N ↔ ∃ g ∈ KL N, qExpand (AlgebraicClosure ℚ) q g = x := by
  simp [KX, IntermediateField.mem_map]

theorem KX_eq_adjoin (N : ℕ) :
    KX q N = IntermediateField.adjoin (AlgebraicClosure ℚ)
      (qExpand (AlgebraicClosure ℚ) q ''
        (laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (Gamma0 N)) :
          Set (LaurentSeries (AlgebraicClosure ℚ)))) := by
  rw [KX]
  conv_lhs => rw [← IntermediateField.adjoin_self (AlgebraicClosure ℚ) (KL N)]
  rw [IntermediateField.adjoin_map]
  congr 1

omit [Fact q.Prime] in

theorem Gamma0_mul_le (M' : ℕ) : Gamma0 (q * M') ≤ Gamma0 M' := by
  intro A hA
  rw [CongruenceSubgroup.Gamma0_mem] at hA ⊢
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at hA ⊢
  exact dvd_trans (by exact_mod_cast Dvd.intro_left q rfl) hA

omit [Fact q.Prime] in
theorem KL_mono {N N' : ℕ} (h : Gamma0 N' ≤ Gamma0 N) : KL N ≤ KL N' := by
  show laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (Gamma0 N)) ≤
    laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (Gamma0 N'))
  rw [laurentBaseChange, laurentBaseChange]
  exact IntermediateField.adjoin.mono _ _ _
    (Set.image_mono (SetLike.coe_subset_coe.mpr (qExpFunctionFieldC_mono ℚ h)))

variable (M' : ℕ) [NeZero M']

omit [NeZero M'] in
theorem KX_le : KX q M' ≤ KX q (q * M') :=
  IntermediateField.map_mono _ (KL_mono (Gamma0_mul_le q M'))

theorem KX_le_fieldBar (hqM' : ¬ q ∣ M') : KX q (q * M') ≤ fieldBar q M' := by
  intro x hx
  obtain ⟨g, hg, rfl⟩ := (mem_KX_iff q (q * M') x).mp hx
  exact ModularCurve.FullLevel.qExpand_coe_mem_fieldBar_of_mem q M' hqM' g hg

theorem relfinrank_adjoin_singleton_eq_finrank {K E : Type*} [Field K] [Field E] [Algebra K E]
    (X : IntermediateField K E) (y : ↥X) :
    (IntermediateField.adjoin K {(y : E)}).relfinrank X =
      Module.finrank ↥(IntermediateField.adjoin K ({y} : Set ↥X)) ↥X := by
  have h := IntermediateField.relfinrank_map_map (IntermediateField.adjoin K ({y} : Set ↥X))
    (⊤ : IntermediateField K ↥X) X.val
  have htop : (⊤ : IntermediateField K ↥X).map X.val = X := by
    rw [← AlgHom.fieldRange_eq_map, IntermediateField.fieldRange_val]
  rw [IntermediateField.adjoin_map, Set.image_singleton, IntermediateField.relfinrank_top_right, htop] at h
  exact h

def J : IntermediateField (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) :=
  IntermediateField.adjoin (AlgebraicClosure ℚ) {jqModC (AlgebraicClosure ℚ)}

theorem jqModC_mem_laurentBaseChange (Γ : Subgroup SL(2, ℤ)) :
    jqModC (AlgebraicClosure ℚ) ∈ laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ Γ) := by
  have h1 : jqModC ℚ ∈ (qExpFunctionFieldC ℚ Γ : Set (LaurentSeries ℚ)) :=
    intFormRatiosC_subset ℚ _ (ModularCurve.jqModC_mem_intFormRatiosC ℚ _)
  have h2 := coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) h1
  rwa [show coeffEmb (AlgebraicClosure ℚ) (jqModC ℚ) = jqModC (AlgebraicClosure ℚ) from map_jqModC _] at h2

omit [Fact q.Prime] in
theorem J_le_KL (N : ℕ) : J ≤ KL N := by
  rw [J, IntermediateField.adjoin_le_iff, Set.singleton_subset_iff]
  exact jqModC_mem_laurentBaseChange _

omit [Fact q.Prime] in

theorem relfinrank_J_KL (N : ℕ) [NeZero N] :
    (J).relfinrank (KL N) = (Gamma0 N ⊔ Subgroup.zpowers (-1 : SL(2, ℤ))).index := by
  let y : ↥(KL N) := ⟨jqModC (AlgebraicClosure ℚ), jqModC_mem_laurentBaseChange _⟩
  have h := relfinrank_adjoin_singleton_eq_finrank (KL N) y
  exact h.trans (ModularCurve.finrank_adjoin_jqModC_laurentBaseChange_qExpFunctionFieldC_gamma0_eq_index
    (AlgebraicClosure ℚ) N y rfl)

omit [Fact q.Prime] in
theorem index_Gamma0_sup (N : ℕ) [NeZero N] :
    (Gamma0 N ⊔ Subgroup.zpowers (-1 : SL(2, ℤ))).index = dedekindPsi N := by
  have h : Subgroup.zpowers (-1 : SL(2, ℤ)) ≤ Gamma0 N := by
    rw [Subgroup.zpowers_le]
    rw [CongruenceSubgroup.Gamma0_mem]
    simp
  rw [sup_eq_left.mpr h, ModularCurve.Gamma0_index]

omit [Fact q.Prime] in
theorem dedekindPsi_pos : 0 < dedekindPsi M' := by
  have h1 : (1 : ℕ) ∈ M'.divisors.filter Squarefree :=
    Finset.mem_filter.mpr ⟨Nat.one_mem_divisors.mpr (NeZero.ne M'), squarefree_one⟩
  have h := Finset.single_le_sum (f := fun d => M' / d) (fun _ _ => Nat.zero_le _) h1
  simp only [Nat.div_one] at h
  exact lt_of_lt_of_le (Nat.pos_of_ne_zero (NeZero.ne M')) h

theorem dedekindPsi_q_mul (hqM' : ¬ q ∣ M') : dedekindPsi (q * M') = (q + 1) * dedekindPsi M' := by
  rw [mul_comm q M', ModularCurve.dedekindPsi_mul_prime M' q (Fact.out : q.Prime), if_neg hqM']

theorem relfinrank_KL (hqM' : ¬ q ∣ M') : (KL M').relfinrank (KL (q * M')) = q + 1 := by
  haveI : NeZero (q * M') := ⟨mul_ne_zero (Fact.out : q.Prime).ne_zero (NeZero.ne M')⟩
  have t := IntermediateField.relfinrank_mul_relfinrank (J_le_KL M') (KL_mono (Gamma0_mul_le q M'))
  rw [relfinrank_J_KL, relfinrank_J_KL, index_Gamma0_sup, index_Gamma0_sup,
    dedekindPsi_q_mul q M' hqM', mul_comm (q + 1) (dedekindPsi M')] at t
  exact Nat.eq_of_mul_eq_mul_left (dedekindPsi_pos M') t

theorem relfinrank_KX (hqM' : ¬ q ∣ M') : (KX q M').relfinrank (KX q (q * M')) = q + 1 := by
  rw [KX, KX, IntermediateField.relfinrank_map_map, relfinrank_KL q M' hqM']

theorem main (hq3 : q = 3) (hqM' : ¬ q ∣ M') :
    KX q M' ≤ fieldBar q M' ∧ 0 < (KX q M').relfinrank (fieldBar q M') ∧
      2 * (KX q M').relfinrank (fieldBar q M') ≤ q * (q ^ 2 - 1) := by
  have hle1 := KX_le q M'
  have hle2 := KX_le_fieldBar q M' hqM'
  have hB := ModularCurve.FullLevel.relfinrank_adjoin_qExpand_image_laurentBaseChange_gamma0_fieldBar_le_of_eq_three
    q hq3 M' hqM'
  have hB0 := ModularCurve.FullLevel.relfinrank_adjoin_qExpand_image_laurentBaseChange_gamma0_fieldBar_ne_zero
    q M' hqM'
  rw [← KX_eq_adjoin q (q * M')] at hB hB0
  have t := IntermediateField.relfinrank_mul_relfinrank hle1 hle2
  rw [relfinrank_KX q M' hqM'] at t
  refine ⟨hle1.trans hle2, ?_, ?_⟩
  · rw [← t]
    exact Nat.mul_pos (Nat.succ_pos q) (Nat.pos_of_ne_zero hB0)
  · rw [← t]
    have h2 : 2 * (q * (q - 1) / 2) ≤ q * (q - 1) := Nat.mul_div_le _ _
    have e : q ^ 2 - 1 = (q + 1) * (q - 1) := by
      obtain ⟨k, rfl⟩ : ∃ k, q = k + 1 := ⟨q - 1, by omega⟩
      rw [Nat.add_sub_cancel, show (k + 1) ^ 2 = (k + 1 + 1) * k + 1 by ring, Nat.add_sub_cancel]
    calc 2 * ((q + 1) * (KX q (q * M')).relfinrank (fieldBar q M'))
        = (q + 1) * (2 * (KX q (q * M')).relfinrank (fieldBar q M')) := by ring
      _ ≤ (q + 1) * (2 * (q * (q - 1) / 2)) := by gcongr
      _ ≤ (q + 1) * (q * (q - 1)) := Nat.mul_le_mul_left _ h2
      _ = q * (q ^ 2 - 1) := by rw [e]; ring

end ModularCurve.FullLevel.DegRoad
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_adjoin_qExpand_image_le_fieldBar_and_relfinrank_pos_and_le_of_eq_three.ModularCurve P2MW.S_ModularCurve_FullLevel_adjoin_qExpand_image_le_fieldBar_and_relfinrank_pos_and_le_of_eq_three.ModularCurve.FullLevel P2MW.S_ModularCurve_FullLevel_adjoin_qExpand_image_le_fieldBar_and_relfinrank_pos_and_le_of_eq_three.ModularCurve.FullLevel.DegRoad"
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_adjoin_qExpand_image_le_fieldBar_and_relfinrank_pos_and_le_of_eq_three.ModularCurve P2MW.S_ModularCurve_FullLevel_adjoin_qExpand_image_le_fieldBar_and_relfinrank_pos_and_le_of_eq_three.ModularCurve.FullLevel"
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_adjoin_qExpand_image_le_fieldBar_and_relfinrank_pos_and_le_of_eq_three.ModularCurve"

end
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_adjoin_qExpand_image_le_fieldBar_and_relfinrank_pos_and_le_of_eq_three.ModularCurve P2MW.S_ModularCurve_FullLevel_adjoin_qExpand_image_le_fieldBar_and_relfinrank_pos_and_le_of_eq_three.ModularCurve.FullLevel P2MW.S_ModularCurve_FullLevel_adjoin_qExpand_image_le_fieldBar_and_relfinrank_pos_and_le_of_eq_three.ModularCurve.FullLevel.DegRoad"

open ModularCurve.FullLevel.DegRoad in

theorem solution
    (q : ℕ) [Fact q.Prime] (hq3 : q = 3) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M') :
    IntermediateField.adjoin (AlgebraicClosure ℚ)
        (qExpand (AlgebraicClosure ℚ) q ''
          (laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (Gamma0 M')) :
            Set (LaurentSeries (AlgebraicClosure ℚ)))) ≤ fieldBar q M' ∧
    0 < (IntermediateField.adjoin (AlgebraicClosure ℚ)
        (qExpand (AlgebraicClosure ℚ) q ''
          (laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (Gamma0 M')) :
            Set (LaurentSeries (AlgebraicClosure ℚ))))).relfinrank (fieldBar q M') ∧
    2 * (IntermediateField.adjoin (AlgebraicClosure ℚ)
        (qExpand (AlgebraicClosure ℚ) q ''
          (laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (Gamma0 M')) :
            Set (LaurentSeries (AlgebraicClosure ℚ))))).relfinrank (fieldBar q M') ≤ q * (q ^ 2 - 1) := by
  have h := main q M' hq3 hqM'
  rw [KX_eq_adjoin q M'] at h
  exact h

end S_ModularCurve_FullLevel_adjoin_qExpand_image_le_fieldBar_and_relfinrank_pos_and_le_of_eq_three
end P2MW
export P2MW.S_ModularCurve_FullLevel_adjoin_qExpand_image_le_fieldBar_and_relfinrank_pos_and_le_of_eq_three (solution)
