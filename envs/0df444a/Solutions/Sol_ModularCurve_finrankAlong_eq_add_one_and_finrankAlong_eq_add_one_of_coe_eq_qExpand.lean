-- Prove2me | solution 1 for ModularCurve.finrankAlong_eq_add_one_and_finrankAlong_eq_add_one_of_coe_eq_qExpand
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/927e0e56-3d33-5e72-a1a9-48592cdd217e

import Mathlib
import Definitions.Def_ModularCurve_XH
import Definitions.Def_ModularCurve_XHDifferentialsModL
import Definitions.Def_ModularCurve_X0
import Definitions.Def_ModularCurve_X0ModL
import Definitions.Def_AlgebraicCurve_Correspondence
import Theorems.Thm_ModularCurve_relfinrank_laurentBaseChange
import Theorems.Thm_ModularCurve_XHDRLevel_relfinrank_qExpFunctionFieldC_gammaH_infSubgroup_gammaH_eq_add_one
import Theorems.Thm_AlgebraicCurve_finrankAlong_eq_relfinrank_fieldRange
import Theorems.Thm_AlgebraicCurve_finrankAlong_comp
import Theorems.Thm_ModularCurve_finiteDimensional_and_finrank_adjoin_jqModC_qExpFunctionFieldC_le_index
import Theorems.Thm_ModularCurve_modularFunctionFieldFullC_le_qExpFunctionFieldC_gamma0
import Theorems.Thm_ModularCurve_transcendental_jqModC
import Theorems.Thm_ModularCurve_GammaH_le_GammaH_div_infSubgroup
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_finrankAlong_eq_add_one_and_finrankAlong_eq_add_one_of_coe_eq_qExpand
p2m_attr_erase "instance" "ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid"
p2m_attr_erase "simp" "ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal"
p2m_attr_erase "simp" "AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply ModularCurve.ProjectiveLine.map_mk ModularCurve.coe_towerInclBar"
p2m_attr_erase "simp" "ModularCurve.coe_towerSubstBar"

set_option autoImplicit false

open ModularCurve AlgebraicCurve IntermediateField CongruenceSubgroup
open scoped MatrixGroups

namespace FinrankSol

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

end FinrankSol

open FinrankSol in
theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]
    (θ : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hθ : haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
      ∀ (f : ↥(xHFunctionFieldBar M H)) (u : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))), (f : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)) →
        ((θ f : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = qExpand (AlgebraicClosure ℚ) p (u : LaurentSeries (AlgebraicClosure ℚ)))
    (αH βH : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hα : ∀ u : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)), ((αH u : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)))
    (hβ : haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
      ∀ u : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)), ((βH u : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = qExpand (AlgebraicClosure ℚ) p (u : LaurentSeries (AlgebraicClosure ℚ))) :
    finrankAlong (AlgebraicClosure ℚ) αH = p + 1 ∧ finrankAlong (AlgebraicClosure ℚ) βH = p + 1 := by

  have hA : xHFunctionFieldBar (M / p) (infSubgroup p M H hpM) = laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM))) := rfl
  have hB : xHFunctionFieldBar M H = laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) := rfl
  have hNM : (qExpFunctionFieldC ℚ (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM))) ≤ (qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) := qExpFunctionFieldC_mono ℚ (ModularCurve.GammaH_le_GammaH_div_infSubgroup p M H hpM)
  have hAB : xHFunctionFieldBar (M / p) (infSubgroup p M H hpM) ≤ xHFunctionFieldBar M H := by
    rw [hA, hB]
    exact IntermediateField.adjoin.mono _ _ _ (Set.image_mono hNM)

  have hrange : ((xHFunctionFieldBar M H).val.comp αH).fieldRange = xHFunctionFieldBar (M / p) (infSubgroup p M H hpM) := by
    ext x
    rw [AlgHom.mem_fieldRange]
    constructor
    · rintro ⟨u, rfl⟩
      show ((αH u : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) ∈ xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)
      rw [hα u]; exact u.2
    · intro hx
      exact ⟨⟨x, hx⟩, by show ((αH ⟨x, hx⟩ : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = x; rw [hα]⟩
  have h1 : finrankAlong (AlgebraicClosure ℚ) αH =
      relfinrank (xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) (xHFunctionFieldBar M H) := by
    rw [show relfinrank (xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) (xHFunctionFieldBar M H) =
      relfinrank ((xHFunctionFieldBar M H).val.comp αH).fieldRange (xHFunctionFieldBar M H) from by rw [hrange]]
    exact AlgebraicCurve.finrankAlong_eq_relfinrank_fieldRange _ _ αH

  have hj0 : jqModC ℚ ∈ (qExpFunctionFieldC ℚ (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM))) := by
    have h := ModularCurve.jqModC_mem_full ℚ (M / p)
    exact qExpFunctionFieldC_mono ℚ (CohCarrier.GammaH_le_Gamma0 _)
      (ModularCurve.modularFunctionFieldFullC_le_qExpFunctionFieldC_gamma0 ℚ (M / p) h)
  set J : IntermediateField ℚ (LaurentSeries ℚ) := adjoin ℚ ({jqModC ℚ} : Set (LaurentSeries ℚ)) with hJ
  set Jb : IntermediateField (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) :=
    adjoin (AlgebraicClosure ℚ) ({coeffEmb (AlgebraicClosure ℚ) (jqModC ℚ)} : Set (LaurentSeries (AlgebraicClosure ℚ))) with hJb
  have hJN : J ≤ (qExpFunctionFieldC ℚ (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM))) := by rw [hJ, adjoin_le_iff, Set.singleton_subset_iff]; exact hj0
  have hJbA : Jb ≤ xHFunctionFieldBar (M / p) (infSubgroup p M H hpM) := by
    rw [hJb, adjoin_le_iff, Set.singleton_subset_iff]
    exact coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hj0
  have htr : Transcendental ℚ (jqModC ℚ) := ModularCurve.transcendental_jqModC ℚ
  have eA : relfinrank Jb (xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) = relfinrank J (qExpFunctionFieldC ℚ (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM))) :=
    ModularCurve.relfinrank_laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM))) (jqModC ℚ) hj0 htr
  have eB : relfinrank Jb (xHFunctionFieldBar M H) = relfinrank J (qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) :=
    ModularCurve.relfinrank_laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) (jqModC ℚ) (hNM hj0) htr
  have eNM : relfinrank (qExpFunctionFieldC ℚ (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM))) (qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) = p + 1 :=
    ModularCurve.XHDRLevel.relfinrank_qExpFunctionFieldC_gammaH_infSubgroup_gammaH_eq_add_one p M H hpM hpM2 hHp
  have tQ := relfinrank_mul_relfinrank hJN hNM
  have tL := relfinrank_mul_relfinrank hJbA hAB
  rw [eA, eB, ← tQ, eNM] at tL
  have hpos : 0 < relfinrank J (qExpFunctionFieldC ℚ (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM))) := by
    let x : ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM))) := ⟨jqModC ℚ, hj0⟩
    have hT : ModularGroup.T ∈ CohCarrier.GammaH (M / p) (infSubgroup p M H hpM) := by
      apply ModularCurve.Gamma1_le_GammaH
      rw [Gamma1_mem]
      simp [ModularGroup.T]
    haveI : (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM)).FiniteIndex :=
      Subgroup.finiteIndex_of_le (ModularCurve.Gamma1_le_GammaH (M / p) (infSubgroup p M H hpM))
    obtain ⟨hfd, -⟩ := ModularCurve.finiteDimensional_and_finrank_adjoin_jqModC_qExpFunctionFieldC_le_index ℚ
      (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM)) hT _ le_rfl (fun γ h => Or.inl h) x rfl
    rw [hJ, show (jqModC ℚ) = ((x : ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM)))) : LaurentSeries ℚ) from rfl, relfinrank_adjoin_eq_finrank]
    exact @Module.finrank_pos _ _ _ _ _ _ hfd _ _ _
  have hAB' : relfinrank (xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) (xHFunctionFieldBar M H) = p + 1 :=
    Nat.eq_of_mul_eq_mul_left hpos tL

  have hβα : βH = θ.toAlgHom.comp αH := by
    apply AlgHom.ext
    intro u
    apply Subtype.ext
    show ((βH u : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) =
      ((θ (αH u) : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ))
    rw [hβ u, hθ (αH u) u (hα u)]
  have hθ1 : finrankAlong (AlgebraicClosure ℚ) θ.toAlgHom = 1 := by
    have hr : ((xHFunctionFieldBar M H).val.comp θ.toAlgHom).fieldRange = xHFunctionFieldBar M H := by
      ext x
      rw [AlgHom.mem_fieldRange]
      constructor
      · rintro ⟨u, rfl⟩; exact (θ u).2
      · intro hx
        refine ⟨θ.symm ⟨x, hx⟩, ?_⟩
        show ((θ (θ.symm ⟨x, hx⟩) : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = x
        rw [AlgEquiv.apply_symm_apply]
    rw [← relfinrank_self (xHFunctionFieldBar M H)]
    rw [show relfinrank (xHFunctionFieldBar M H) (xHFunctionFieldBar M H) =
      relfinrank ((xHFunctionFieldBar M H).val.comp θ.toAlgHom).fieldRange (xHFunctionFieldBar M H) from by rw [hr]]
    exact AlgebraicCurve.finrankAlong_eq_relfinrank_fieldRange _ _ θ.toAlgHom
  refine ⟨h1.trans hAB', ?_⟩
  rw [hβα, AlgebraicCurve.finrankAlong_comp, h1, hAB', hθ1, mul_one]

#print axioms solution

end S_ModularCurve_finrankAlong_eq_add_one_and_finrankAlong_eq_add_one_of_coe_eq_qExpand
end P2MW
export P2MW.S_ModularCurve_finrankAlong_eq_add_one_and_finrankAlong_eq_add_one_of_coe_eq_qExpand (solution)
