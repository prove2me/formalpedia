-- Prove2me | solution 1 for ModularCurve.degeneracyPair_pushforwardAlong_correspondence_levelPrime_identities
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/850ce36d-470b-5294-bdd3-8dbd76fd9c55

import Mathlib
import Definitions.Def_ModularCurve_CharLDegeneracyHecke
import Definitions.Def_AlgebraicCurve_PlacesOverDVR
import Definitions.Def_ModularCurve_QAdicPlaceMod
import Theorems.Thm_AlgebraicCurve_Divisor_pushforwardAlong_pushforwardAlong
import Theorems.Thm_AlgebraicCurve_Divisor_pullbackAlong_pullbackAlong
import Theorems.Thm_AlgebraicCurve_Divisor_pushforwardAlong_pullbackAlong_of_surjective
import Theorems.Thm_AlgebraicCurve_Divisor_correspondence_single_eq_finrankAlong_smul
import Theorems.Thm_ModularCurve_finiteAlong_heckeAlphaC
import Theorems.Thm_ModularCurve_separableAlong_heckeAlphaC_heckeBetaC
import Theorems.Thm_ModularCurve_inertiaDegAlong_heckeAlphaC_eq_one
import Theorems.Thm_AlgebraicCurve_finrankAlong_eq_relfinrank_fieldRange
import Theorems.Thm_ModularCurve_modularFunctionFieldC_eq_modularFunctionFieldFullC
import Theorems.Thm_ModularCurve_charLDegeneracyRoof_eq_modularFunctionFieldFullC_mul
import Theorems.Thm_ModularCurve_relfinrank_modularFunctionFieldFullC_mul_dedekindPsi
import Theorems.Thm_ModularCurve_dedekindPsi_mul_of_coprime
import Theorems.Thm_ModularCurve_dedekindPsi_prime_pow
import Theorems.Thm_ModularCurve_dedekindPsi_prime
import Theorems.Thm_ModularCurve_dedekindPsi_pos
import Theorems.Thm_Algebra_algebraMap_norm_eq_norm_mul_norm_of_adjoin_eq_top
import Theorems.Thm_AlgebraicCurve_Place_ord_norm_eq_sum_fiberOver_of_isSeparable
import Theorems.Thm_AlgebraicCurve_Place_exists_forall_ord_eq
import Theorems.Thm_ModularCurve_exists_algEquiv_atkinLehner_fullC_of_prime_of_not_dvd
import Theorems.Thm_ModularCurve_degeneracyPair_finiteSeparableDeg_ssPlaces_preserved_reflected
import Theorems.Thm_ModularCurve_finiteAlong_heckeBetaC
import Theorems.Thm_AlgebraicCurve_finiteAlong_of_surjective
import Theorems.Thm_AlgebraicCurve_finrankAlong_id
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_degeneracyPair_pushforwardAlong_correspondence_levelPrime_identities
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instSMulAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instDistribMulActionAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar ModularCurve.baseAut_arithmeticGalois ModularCurve.JZero.torsionGaloisRep_apply ModularCurve.coe_arithmeticRingAut_apply ModularCurve.toRingAut_arithmeticGalois ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.coe_cuspidalDivisor₀ ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven"
p2m_attr_erase "simp" "ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluX_empty WeierstrassCurve.veluY_empty WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm AddMonoid.End.dualEndDataOfSurjective_trace AddMonoid.End.dualEndDataOfSurjective_norm WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one"
p2m_attr_erase "simp" "WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero ModularCurve.ProjectiveLine.map_mk"
set_option autoImplicit false
open AlgebraicCurve ModularCurve

namespace DegeneracyLevelPrime

variable {k : Type*} [Field k]

private theorem pushforwardAlong_congr {F F' : Type*} [Field F] [Field F'] [Algebra k F] [Algebra k F']
    {φ ψ : F →ₐ[k] F'} (h : φ = ψ) (hφ : φ.toRingHom.IsIntegral) (hψ : ψ.toRingHom.IsIntegral)
    (D : Divisor k F') :
    Divisor.pushforwardAlong φ hφ D = Divisor.pushforwardAlong ψ hψ D := by
  subst h
  rfl

private theorem betaC_comp_eq_alphaC_comp (M s : ℕ) [NeZero M] [NeZero s] [NeZero (M * s)]
    (φ : Fin 2 → (↥(modularFunctionFieldC k M) →ₐ[k] ↥(modularFunctionFieldC k (M * s))))
    (hφα : ∀ x, ((φ 0 x : ↥(modularFunctionFieldC k (M * s))) : LaurentSeries k) = x)
    (hφβ : ∀ x, ((φ 1 x : ↥(modularFunctionFieldC k (M * s))) : LaurentSeries k) = qExpand k s x) :
    (heckeBetaC k (M * s) s).comp (φ 0) = (heckeAlphaC k (M * s) s).comp (φ 1) := by
  ext x
  simp only [AlgHom.comp_apply, coe_heckeBetaC, coe_heckeAlphaC, hφα, hφβ]

private theorem fieldRange_val_comp_alphaC (N q : ℕ) [NeZero N] [NeZero q] :
    ((charLDegeneracyRoof k N q).val.comp (heckeAlphaC k N q)).fieldRange = modularFunctionFieldC k N := by
  ext x
  simp only [AlgHom.mem_fieldRange, AlgHom.comp_apply, IntermediateField.coe_val, coe_heckeAlphaC]
  exact ⟨fun ⟨y, hy⟩ => hy ▸ y.2, fun hx => ⟨⟨x, hx⟩, rfl⟩⟩

private theorem not_dvd_mul_mul (M s q' : ℕ) (hs : s.Prime) [Fact q'.Prime] (hsq' : s ≠ q')
    (hq'M : ¬ q' ∣ M) : ¬ q' ∣ M * s * s := by
  have hq'p : q'.Prime := Fact.out
  have hq's : ¬ q' ∣ s := fun h => hsq' ((Nat.prime_dvd_prime_iff_eq hq'p hs).mp h).symm
  intro h
  rcases (Nat.Prime.dvd_mul hq'p).mp h with h1 | h1
  · rcases (Nat.Prime.dvd_mul hq'p).mp h1 with h2 | h2
    · exact hq'M h2
    · exact hq's h2
  · exact hq's h1

private theorem dedekindPsi_mul_mul (M s : ℕ) [NeZero M] (hs : s.Prime) (hsM : ¬ s ∣ M) :
    dedekindPsi (M * s * s) = dedekindPsi (M * s) * s := by
  have hcop : Nat.Coprime M s := ((Nat.Prime.coprime_iff_not_dvd hs).mpr hsM).symm
  rw [show M * s * s = M * s ^ 2 by ring, dedekindPsi_mul_of_coprime M (s ^ 2) (Nat.Coprime.pow_right 2 hcop),
    dedekindPsi_prime_pow s 2 hs two_ne_zero, dedekindPsi_mul_of_coprime M s hcop, dedekindPsi_prime hs]
  norm_num
  ring

private theorem finrankAlong_alphaC_eq (M s q' : ℕ) [NeZero M] [NeZero s] [NeZero (M * s)]
    (hs : s.Prime) [Fact q'.Prime] [CharP k q'] (hsq' : s ≠ q') (hq'M : ¬ q' ∣ M) (hsM : ¬ s ∣ M) :
    finrankAlong k (heckeAlphaC k (M * s) s) = s := by
  have hnd : ¬ q' ∣ M * s * s := not_dvd_mul_mul M s q' hs hsq' hq'M
  have hndMs : ¬ q' ∣ M * s := fun h => hnd (Dvd.dvd.mul_right h s)
  have h1 : finrankAlong k (heckeAlphaC k (M * s) s)
      = IntermediateField.relfinrank (modularFunctionFieldC k (M * s)) (charLDegeneracyRoof k (M * s) s) :=
    (finrankAlong_eq_relfinrank_fieldRange (modularFunctionFieldC k (M * s)) (charLDegeneracyRoof k (M * s) s)
      (heckeAlphaC k (M * s) s)).trans
      (congrArg (fun S => IntermediateField.relfinrank S (charLDegeneracyRoof k (M * s) s))
        (fieldRange_val_comp_alphaC (M * s) s))
  rw [h1, modularFunctionFieldC_eq_modularFunctionFieldFullC k q' (M * s) hndMs,
    charLDegeneracyRoof_eq_modularFunctionFieldFullC_mul k q' (M * s) s hnd]
  have hcast : ((M * s * s : ℕ) : k) ≠ 0 := fun h0 => hnd ((CharP.cast_eq_zero_iff k q' _).mp h0)
  have h8 := (relfinrank_modularFunctionFieldFullC_mul_dedekindPsi k (M * s) s hcast).1
  rw [dedekindPsi_mul_mul M s hs hsM] at h8
  exact Nat.eq_of_mul_eq_mul_right (dedekindPsi_pos (M * s) (NeZero.ne (M * s))) (h8.trans (mul_comm _ _))

private theorem correspondence_alphaC_alphaC_single [IsAlgClosed k] (M s q' : ℕ) [NeZero M] [NeZero s]
    [NeZero (M * s)] (hs : s.Prime) [Fact q'.Prime] [CharP k q'] (hsq' : s ≠ q') (hq'M : ¬ q' ∣ M) (hsM : ¬ s ∣ M)
    [HasPrincipalDivisors k ↥(charLDegeneracyRoof k (M * s) s)]
    (hα : HeckeAlphaCIntegral k (M * s) s) (v : Place k ↥(modularFunctionFieldC k (M * s))) (n : ℤ) :
    Divisor.correspondence (heckeAlphaC k (M * s) s) (heckeAlphaC k (M * s) s) hα hα (Finsupp.single v n)
      = (s : ℤ) • Finsupp.single v n := by
  have hnd : ¬ q' ∣ M * s * s := not_dvd_mul_mul M s q' hs hsq' hq'M
  haveI : Fact s.Prime := ⟨hs⟩
  rw [Divisor.correspondence_single_eq_finrankAlong_smul (heckeAlphaC k (M * s) s) (heckeAlphaC k (M * s) s)
      hα hα (finiteAlong_heckeAlphaC k (M * s) s)
      (separableAlong_heckeAlphaC_heckeBetaC k (ℓ := q') (M * s) s hnd).1 v
      (fun w hw => Place.mem_fiberAlong.mp hw)
      (fun w _ => inertiaDegAlong_heckeAlphaC_eq_one k (M * s) s hα w)
      (fun w _ => inertiaDegAlong_heckeAlphaC_eq_one k (M * s) s hα w) n,
    finrankAlong_alphaC_eq M s q' hs hsq' hq'M hsM]

private theorem jq_mem (M : ℕ) [NeZero M] : jqModC k ∈ modularFunctionFieldC k M :=
  IntermediateField.subset_adjoin k _ (Set.mem_insert _ _)

private theorem jqN_mem (M : ℕ) [NeZero M] : jqNModC k M ∈ modularFunctionFieldC k M :=
  IntermediateField.subset_adjoin k _ (Set.mem_insert_of_mem _ rfl)

private theorem pullbackAlong_congr {F F' : Type*} [Field F] [Field F'] [Algebra k F] [Algebra k F']
    [HasPrincipalDivisors k F'] {φ ψ : F →ₐ[k] F'} (h : φ = ψ) (hφ : φ.toRingHom.IsIntegral)
    (hψ : ψ.toRingHom.IsIntegral) (D : Divisor k F) :
    Divisor.pullbackAlong φ hφ D = Divisor.pullbackAlong ψ hψ D := by
  subst h
  rfl

private theorem charLDegeneracyRoof_eq (M s : ℕ) [NeZero M] [NeZero s] [NeZero (M * s)]
    (φ : Fin 2 → (↥(modularFunctionFieldC k M) →ₐ[k] ↥(modularFunctionFieldC k (M * s))))
    (hφα : ∀ x, ((φ 0 x : ↥(modularFunctionFieldC k (M * s))) : LaurentSeries k) = x)
    (hφβ : ∀ x, ((φ 1 x : ↥(modularFunctionFieldC k (M * s))) : LaurentSeries k) = qExpand k s x) :
    charLDegeneracyRoof k M s = modularFunctionFieldC k (M * s) := by
  apply le_antisymm
  · unfold charLDegeneracyRoof
    rw [IntermediateField.adjoin_le_iff]
    have hj : jqModC k ∈ modularFunctionFieldC k M :=
      IntermediateField.subset_adjoin k _ (Set.mem_insert _ _)
    have hjM : jqNModC k M ∈ modularFunctionFieldC k M :=
      IntermediateField.subset_adjoin k _ (Set.mem_insert_of_mem _ rfl)
    rintro x (rfl | rfl | rfl | rfl)
    ·
      have := (φ 0 ⟨jqModC k, hj⟩).2
      rwa [hφα] at this
    · have := (φ 0 ⟨jqNModC k M, hjM⟩).2
      rwa [hφα] at this
    ·
      have := (φ 1 ⟨jqModC k, hj⟩).2
      rwa [hφβ] at this
    ·
      exact jqN_mem (M * s)
  · show IntermediateField.adjoin k {jqModC k, jqNModC k (M * s)} ≤ _
    rw [IntermediateField.adjoin_le_iff]
    rintro x (rfl | rfl)
    · exact IntermediateField.subset_adjoin k _ (Set.mem_insert _ _)
    · exact IntermediateField.subset_adjoin k _
        (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ rfl)))

private theorem correspondence_level_eq (M s : ℕ) [NeZero M] [NeZero s] [NeZero (M * s)]
    [hP : HasPrincipalDivisors k ↥(charLDegeneracyRoof k M s)]
    (φ : Fin 2 → (↥(modularFunctionFieldC k M) →ₐ[k] ↥(modularFunctionFieldC k (M * s))))
    (hφ : ∀ i, (φ i).toRingHom.IsIntegral)
    (hφα : ∀ x, ((φ 0 x : ↥(modularFunctionFieldC k (M * s))) : LaurentSeries k) = x)
    (hφβ : ∀ x, ((φ 1 x : ↥(modularFunctionFieldC k (M * s))) : LaurentSeries k) = qExpand k s x)
    (hα₀ : HeckeAlphaCIntegral k M s) (hβ₀ : HeckeBetaCIntegral k M s)
    [HasPrincipalDivisors k ↥(modularFunctionFieldC k (M * s))]
    (E : Divisor k ↥(modularFunctionFieldC k M)) :
    Divisor.correspondence (heckeAlphaC k M s) (heckeBetaC k M s) hα₀ hβ₀ E
      = Divisor.pushforwardAlong (φ 1) (hφ 1) (Divisor.pullbackAlong (φ 0) (hφ 0) E) := by
  have hEq := charLDegeneracyRoof_eq M s φ hφα hφβ
  let e : ↥(charLDegeneracyRoof k M s) ≃ₐ[k] ↥(modularFunctionFieldC k (M * s)) := IntermediateField.equivOfEq hEq
  have he : e.toAlgHom.toRingHom.IsIntegral := RingHom.isIntegral_of_surjective _ e.surjective
  have hα' : e.toAlgHom.comp (heckeAlphaC k M s) = φ 0 := AlgHom.ext fun x => Subtype.ext <| by
    show ((heckeAlphaC k M s x : ↥(charLDegeneracyRoof k M s)) : LaurentSeries k) = (φ 0 x : LaurentSeries k)
    rw [coe_heckeAlphaC k M s x, hφα x]
  have hβ' : e.toAlgHom.comp (heckeBetaC k M s) = φ 1 := AlgHom.ext fun x => Subtype.ext <| by
    show ((heckeBetaC k M s x : ↥(charLDegeneracyRoof k M s)) : LaurentSeries k) = (φ 1 x : LaurentSeries k)
    rw [coe_heckeBetaC k M s x, hφβ x]
  have hα'' : (e.toAlgHom.comp (heckeAlphaC k M s)).toRingHom.IsIntegral := by rw [hα']; exact hφ 0
  have hβ'' : (e.toAlgHom.comp (heckeBetaC k M s)).toRingHom.IsIntegral := by rw [hβ']; exact hφ 1
  rw [Divisor.correspondence_apply, pullbackAlong_congr hα'.symm (hφ 0) hα'',
    ← Divisor.pullbackAlong_pullbackAlong (heckeAlphaC k M s) e.toAlgHom hα₀ he hα'',
    pushforwardAlong_congr hβ'.symm (hφ 1) hβ'',
    ← Divisor.pushforwardAlong_pushforwardAlong (heckeBetaC k M s) e.toAlgHom hβ₀ he hβ'',
    Divisor.pushforwardAlong_pullbackAlong_of_surjective e.toAlgHom he e.surjective]

private theorem correspondence_alphaC_alphaC [IsAlgClosed k] (M s q' : ℕ) [NeZero M] [NeZero s]
    [NeZero (M * s)] (hs : s.Prime) [Fact q'.Prime] [CharP k q'] (hsq' : s ≠ q') (hq'M : ¬ q' ∣ M) (hsM : ¬ s ∣ M)
    [HasPrincipalDivisors k ↥(charLDegeneracyRoof k (M * s) s)]
    (hα : HeckeAlphaCIntegral k (M * s) s) (D : Divisor k ↥(modularFunctionFieldC k (M * s))) :
    Divisor.correspondence (heckeAlphaC k (M * s) s) (heckeAlphaC k (M * s) s) hα hα D = (s : ℤ) • D := by
  induction D using Finsupp.induction_linear with
  | zero => simp only [map_zero, smul_zero]
  | add f g hf hg => rw [map_add, hf, hg, smul_add]
  | single v n => exact correspondence_alphaC_alphaC_single M s q' hs hsq' hq'M hsM hα v n

private theorem exchange_add_of_isSeparable
    {K F F₁ F₂ Z Z' : Type*} [Field K] [Field F] [Field F₁] [Field F₂] [Field Z] [Field Z']
    [Algebra K F] [Algebra K F₁] [Algebra K F₂] [Algebra K Z] [Algebra K Z']
    [Algebra F F₁] [Algebra F F₂] [Algebra F Z] [Algebra F₁ Z] [Algebra F₂ Z]
    [Algebra F Z'] [Algebra F₁ Z'] [Algebra F₂ Z']
    [IsScalarTower K F F₁] [IsScalarTower K F F₂] [IsScalarTower K F Z] [IsScalarTower K F Z']
    [IsScalarTower K F₁ Z] [IsScalarTower K F₂ Z] [IsScalarTower K F₁ Z'] [IsScalarTower K F₂ Z']
    [IsScalarTower F F₁ Z] [IsScalarTower F F₂ Z] [IsScalarTower F F₁ Z'] [IsScalarTower F F₂ Z']
    [FiniteDimensional F F₁] [FiniteDimensional F F₂]
    [FiniteDimensional F₁ Z] [FiniteDimensional F₂ Z] [FiniteDimensional F₁ Z'] [FiniteDimensional F₂ Z']
    [Algebra.IsSeparable F F₁] [Algebra.IsSeparable F₂ Z] [Algebra.IsSeparable F₂ Z']
    (hgen : Algebra.adjoin F (Set.range (algebraMap F₁ Z) ∪ Set.range (algebraMap F₂ Z)) = ⊤)
    (hgen' : Algebra.adjoin F (Set.range (algebraMap F₁ Z') ∪ Set.range (algebraMap F₂ Z')) = ⊤)
    (hdeg : Module.finrank F₁ Z + Module.finrank F₁ Z' = Module.finrank F F₂)
    (hne : ∃ (a : F₂) (b : F₁), algebraMap F₂ Z' a = algebraMap F₁ Z' b ∧
      algebraMap F₂ Z a ≠ algebraMap F₁ Z b)
    (w₁ : Place K F₁) (w₂ : Place K F₂) (hw : w₁.restrict F = w₂.restrict F)
    (T : Finset (Place K Z)) (hT : ∀ W, W ∈ T ↔ W.restrict F₁ = w₁ ∧ W.restrict F₂ = w₂)
    (T' : Finset (Place K Z')) (hT' : ∀ W, W ∈ T' ↔ W.restrict F₁ = w₁ ∧ W.restrict F₂ = w₂) :
    ∑ W ∈ T, W.ramificationIndex F₁ * W.inertiaDeg F₂
        + ∑ W ∈ T', W.ramificationIndex F₁ * W.inertiaDeg F₂
      = w₁.inertiaDeg F * w₂.ramificationIndex F := by
  classical

  have hrr : ∀ W : Place K Z, (W.restrict F₁).restrict F = (W.restrict F₂).restrict F := fun W =>
    Place.ext (by simp only [Place.restrict_toValuationSubring, ValuationSubring.comap_comap,
      ← IsScalarTower.algebraMap_eq])
  have hrr' : ∀ W : Place K Z', (W.restrict F₁).restrict F = (W.restrict F₂).restrict F := fun W =>
    Place.ext (by simp only [Place.restrict_toValuationSubring, ValuationSubring.comap_comap,
      ← IsScalarTower.algebraMap_eq])
  set v : Place K F := w₁.restrict F with hv

  obtain ⟨g, hg0, hg⟩ := Place.exists_forall_ord_eq (v.fiberOver F₁)
    (fun w => if w = w₁ then (1 : ℤ) else 0)
  have hg1 : w₁.ord g = 1 := by
    have := hg w₁ ((Place.mem_fiberOver _).mpr rfl)
    simpa using this
  have hgz : ∀ w ∈ v.fiberOver F₁, w ≠ w₁ → w.ord g = 0 := fun w hw hne => by
    have := hg w hw
    simpa [hne] using this
  have hgZ : algebraMap F₁ Z g ≠ 0 := by simpa using hg0
  have hgZ' : algebraMap F₁ Z' g ≠ 0 := by simpa using hg0

  have hN := Algebra.algebraMap_norm_eq_norm_mul_norm_of_adjoin_eq_top hgen hgen' hdeg hne g

  have h1 : w₂.ord (algebraMap F F₂ (Algebra.norm F g))
      = (w₂.ramificationIndex F : ℤ) * (w₁.inertiaDeg F : ℤ) := by
    rw [Place.ord_restrict, ← hw, Place.ord_norm_eq_sum_fiberOver_of_isSeparable (w₁.restrict F) hg0,
      Finset.sum_eq_single_of_mem w₁ ((Place.mem_fiberOver _).mpr rfl)]
    · rw [hg1, mul_one]
    · intro w hw hne
      rw [hgz w hw hne, mul_zero]

  have h2 : w₂.ord (Algebra.norm F₂ (algebraMap F₁ Z g))
      = ∑ W ∈ T, ((W.ramificationIndex F₁ : ℤ) * (W.inertiaDeg F₂ : ℤ)) := by
    rw [Place.ord_norm_eq_sum_fiberOver_of_isSeparable w₂ hgZ]
    have hTeq : T = (w₂.fiberOver Z).filter (fun W => W.restrict F₁ = w₁) := by
      ext W
      rw [hT, Finset.mem_filter, Place.mem_fiberOver, and_comm]
    rw [hTeq, Finset.sum_filter]
    refine Finset.sum_congr rfl fun W hW => ?_
    have hW : W.restrict F₂ = w₂ := (Place.mem_fiberOver _).mp hW
    rw [Place.ord_restrict]
    by_cases h : W.restrict F₁ = w₁
    · rw [if_pos h, h, hg1, mul_one, mul_comm]
    · rw [if_neg h, hgz (W.restrict F₁) ?_ h, mul_zero, mul_zero]
      rw [Place.mem_fiberOver, hrr, hW, ← hw]
  have h3 : w₂.ord (Algebra.norm F₂ (algebraMap F₁ Z' g))
      = ∑ W ∈ T', ((W.ramificationIndex F₁ : ℤ) * (W.inertiaDeg F₂ : ℤ)) := by
    rw [Place.ord_norm_eq_sum_fiberOver_of_isSeparable w₂ hgZ']
    have hTeq : T' = (w₂.fiberOver Z').filter (fun W => W.restrict F₁ = w₁) := by
      ext W
      rw [hT', Finset.mem_filter, Place.mem_fiberOver, and_comm]
    rw [hTeq, Finset.sum_filter]
    refine Finset.sum_congr rfl fun W hW => ?_
    have hW : W.restrict F₂ = w₂ := (Place.mem_fiberOver _).mp hW
    rw [Place.ord_restrict]
    by_cases h : W.restrict F₁ = w₁
    · rw [if_pos h, h, hg1, mul_one, mul_comm]
    · rw [if_neg h, hgz (W.restrict F₁) ?_ h, mul_zero, mul_zero]
      rw [Place.mem_fiberOver, hrr', hW, ← hw]

  have hprod : w₂.ord (algebraMap F F₂ (Algebra.norm F g))
      = w₂.ord (Algebra.norm F₂ (algebraMap F₁ Z g)) + w₂.ord (Algebra.norm F₂ (algebraMap F₁ Z' g)) := by
    rw [hN, Place.ord_mul _ (Algebra.norm_ne_zero_iff.mpr hgZ) (Algebra.norm_ne_zero_iff.mpr hgZ')]
  rw [h1, h2, h3] at hprod
  have : ((∑ W ∈ T, W.ramificationIndex F₁ * W.inertiaDeg F₂
      + ∑ W ∈ T', W.ramificationIndex F₁ * W.inertiaDeg F₂ : ℕ) : ℤ)
      = ((w₁.inertiaDeg F * w₂.ramificationIndex F : ℕ) : ℤ) := by
    push_cast
    rw [← hprod, mul_comm]
  exact_mod_cast this

private theorem algebra_adjoin_eq_top_of_intermediateField {K F E : Type*} [Field K] [Field F] [Field E]
    [Algebra K F] [Algebra K E] [Algebra F E] [IsScalarTower K F E] [FiniteDimensional F E]
    {S : Set E} (hS : IntermediateField.adjoin K S = ⊤) : Algebra.adjoin F S = ⊤ := by
  have hS' : IntermediateField.adjoin F S = ⊤ := by
    rw [eq_top_iff]
    intro x _
    have hx : x ∈ IntermediateField.adjoin K S := hS ▸ IntermediateField.mem_top
    have hle : IntermediateField.adjoin K S ≤ (IntermediateField.adjoin F S).restrictScalars K :=
      IntermediateField.adjoin_le_iff.mpr fun y hy => IntermediateField.subset_adjoin F S hy
    exact hle hx
  rw [← IntermediateField.adjoin_toSubalgebra_of_isAlgebraic
    (fun x _ => Algebra.IsAlgebraic.isAlgebraic x), hS', IntermediateField.top_toSubalgebra]

private theorem pullbackAlong_pushforwardAlong_eq_add_of_separable
    {K F F₁ F₂ Z Z' : Type*} [Field K] [Field F] [Field F₁] [Field F₂] [Field Z] [Field Z']
    [Algebra K F] [Algebra K F₁] [Algebra K F₂] [Algebra K Z] [Algebra K Z']
    [HasPrincipalDivisors K F₁] [HasPrincipalDivisors K Z] [HasPrincipalDivisors K Z']
    (φ : F →ₐ[K] F₁) (ψ' : F →ₐ[K] F₂)
    (u : F₁ →ₐ[K] Z) (u' : F₂ →ₐ[K] Z) (s : F₁ →ₐ[K] Z') (s' : F₂ →ₐ[K] Z')
    (hsq : u.comp φ = u'.comp ψ') (hsq' : s.comp φ = s'.comp ψ')
    (hφ : φ.toRingHom.IsIntegral) (hψ' : ψ'.toRingHom.IsIntegral)
    (hu : u.toRingHom.IsIntegral) (hu' : u'.toRingHom.IsIntegral)
    (hs : s.toRingHom.IsIntegral) (hs' : s'.toRingHom.IsIntegral)
    (hφfin : FiniteAlong K φ) (hψ'fin : FiniteAlong K ψ')
    (hufin : FiniteAlong K u) (hu'fin : FiniteAlong K u')
    (hsfin : FiniteAlong K s) (hs'fin : FiniteAlong K s')
    (hψ'sep : SeparableAlong K ψ') (husep : SeparableAlong K u) (hssep : SeparableAlong K s)
    (hgen : IntermediateField.adjoin K (Set.range u ∪ Set.range u') = ⊤)
    (hgen' : IntermediateField.adjoin K (Set.range s ∪ Set.range s') = ⊤)
    (hdeg : finrankAlong K u' + finrankAlong K s' = finrankAlong K φ)
    (hne : ∃ (a : F₁) (b : F₂), s a = s' b ∧ u a ≠ u' b)
    (D : Divisor K F₂) :
    Divisor.pullbackAlong φ hφ (Divisor.pushforwardAlong ψ' hψ' D)
      = Divisor.pushforwardAlong u hu (Divisor.pullbackAlong u' hu' D)
        + Divisor.pushforwardAlong s hs (Divisor.pullbackAlong s' hs' D) := by
  classical

  letI : Algebra F F₁ := algebraAlong φ
  letI : Algebra F F₂ := algebraAlong ψ'
  letI : Algebra F₁ Z := algebraAlong u
  letI : Algebra F₂ Z := algebraAlong u'
  letI : Algebra F₁ Z' := algebraAlong s
  letI : Algebra F₂ Z' := algebraAlong s'
  letI : Algebra F Z := algebraAlong (u.comp φ)
  letI : Algebra F Z' := algebraAlong (s.comp φ)
  haveI : IsScalarTower K F F₁ := isScalarTower_along φ
  haveI : IsScalarTower K F F₂ := isScalarTower_along ψ'
  haveI : IsScalarTower K F₁ Z := isScalarTower_along u
  haveI : IsScalarTower K F₂ Z := isScalarTower_along u'
  haveI : IsScalarTower K F₁ Z' := isScalarTower_along s
  haveI : IsScalarTower K F₂ Z' := isScalarTower_along s'
  haveI : IsScalarTower K F Z := isScalarTower_along (u.comp φ)
  haveI : IsScalarTower K F Z' := isScalarTower_along (s.comp φ)
  haveI : IsScalarTower F F₁ Z := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower F F₂ Z := IsScalarTower.of_algebraMap_eq fun x => AlgHom.congr_fun hsq x
  haveI : IsScalarTower F F₁ Z' := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower F F₂ Z' := IsScalarTower.of_algebraMap_eq fun x => AlgHom.congr_fun hsq' x
  haveI : Algebra.IsIntegral F F₁ := isIntegral_along φ hφ
  haveI : Algebra.IsIntegral F F₂ := isIntegral_along ψ' hψ'
  haveI : Algebra.IsIntegral F₁ Z := isIntegral_along u hu
  haveI : Algebra.IsIntegral F₂ Z := isIntegral_along u' hu'
  haveI : Algebra.IsIntegral F₁ Z' := isIntegral_along s hs
  haveI : Algebra.IsIntegral F₂ Z' := isIntegral_along s' hs'
  haveI : FiniteDimensional F F₁ := hφfin
  haveI : FiniteDimensional F F₂ := hψ'fin
  haveI : FiniteDimensional F₁ Z := hufin
  haveI : FiniteDimensional F₂ Z := hu'fin
  haveI : FiniteDimensional F₁ Z' := hsfin
  haveI : FiniteDimensional F₂ Z' := hs'fin
  haveI : FiniteDimensional F Z := Module.Finite.trans F₁ Z
  haveI : FiniteDimensional F Z' := Module.Finite.trans F₁ Z'
  haveI : Algebra.IsSeparable F F₂ := hψ'sep
  haveI : Algebra.IsSeparable F₁ Z := husep
  haveI : Algebra.IsSeparable F₁ Z' := hssep

  have hgenZ : Algebra.adjoin F (Set.range (algebraMap F₂ Z) ∪ Set.range (algebraMap F₁ Z)) = ⊤ := by
    rw [Set.union_comm]; exact algebra_adjoin_eq_top_of_intermediateField (K := K) hgen
  have hgenZ' : Algebra.adjoin F (Set.range (algebraMap F₂ Z') ∪ Set.range (algebraMap F₁ Z')) = ⊤ := by
    rw [Set.union_comm]; exact algebra_adjoin_eq_top_of_intermediateField (K := K) hgen'
  have hdeg' : Module.finrank F₂ Z + Module.finrank F₂ Z' = Module.finrank F F₁ := hdeg
  have hne' : ∃ (a : F₁) (b : F₂), algebraMap F₁ Z' a = algebraMap F₂ Z' b ∧
      algebraMap F₁ Z a ≠ algebraMap F₂ Z b := hne

  have eZ : ∀ W : Place K Z, Place.ramificationIndexAlong u' W = W.ramificationIndex F₂ := fun _ => rfl
  have fZ : ∀ W : Place K Z, W.inertiaDegAlong u hu = W.inertiaDeg F₁ := fun _ => rfl
  have eZ' : ∀ W : Place K Z', Place.ramificationIndexAlong s' W = W.ramificationIndex F₂ := fun _ => rfl
  have fZ' : ∀ W : Place K Z', W.inertiaDegAlong s hs = W.inertiaDeg F₁ := fun _ => rfl
  have fF : ∀ w : Place K F₂, w.inertiaDegAlong ψ' hψ' = w.inertiaDeg F := fun _ => rfl
  have eF : ∀ w : Place K F₁, Place.ramificationIndexAlong φ w = w.ramificationIndex F := fun _ => rfl

  have hrr : ∀ W : Place K Z, (W.restrict F₁).restrict F = (W.restrict F₂).restrict F := fun W =>
    Place.ext (by simp only [Place.restrict_toValuationSubring, ValuationSubring.comap_comap,
      ← IsScalarTower.algebraMap_eq])
  have hrr' : ∀ W : Place K Z', (W.restrict F₁).restrict F = (W.restrict F₂).restrict F := fun W =>
    Place.ext (by simp only [Place.restrict_toValuationSubring, ValuationSubring.comap_comap,
      ← IsScalarTower.algebraMap_eq])

  suffices h : (Divisor.pullbackAlong φ hφ).comp (Divisor.pushforwardAlong ψ' hψ') =
      (Divisor.pushforwardAlong u hu).comp (Divisor.pullbackAlong u' hu')
        + (Divisor.pushforwardAlong s hs).comp (Divisor.pullbackAlong s' hs') from
    DFunLike.congr_fun h D
  refine Finsupp.addHom_ext fun wA n => ?_
  simp only [AddMonoidHom.coe_comp, AddMonoidHom.add_apply, Function.comp_apply]
  rw [Divisor.pushforwardAlong_single, Divisor.pullbackAlong_single, Divisor.pullbackAlong_single,
    Divisor.pullbackAlong_single, map_sum, map_sum]
  simp only [Divisor.pushforwardAlong_single]

  ext wB
  rw [Finsupp.add_apply, Finset.sum_apply', Finset.sum_apply', Finset.sum_apply']
  simp only [Finsupp.single_apply, Finset.sum_ite_eq', eZ, fZ, eZ', fZ', fF, eF]
  by_cases hv : wB.restrictAlong φ hφ = wA.restrictAlong ψ' hψ'
  · rw [if_pos (Place.mem_fiberAlong.mpr hv), ← Finset.sum_filter, ← Finset.sum_filter]
    have hT : ∀ W, W ∈ (Place.fiberAlong u' hu' wA).filter (fun W => W.restrictAlong u hu = wB)
        ↔ W.restrict F₂ = wA ∧ W.restrict F₁ = wB := fun W => by
      rw [Finset.mem_filter, Place.mem_fiberAlong]
      exact Iff.rfl
    have hT' : ∀ W, W ∈ (Place.fiberAlong s' hs' wA).filter (fun W => W.restrictAlong s hs = wB)
        ↔ W.restrict F₂ = wA ∧ W.restrict F₁ = wB := fun W => by
      rw [Finset.mem_filter, Place.mem_fiberAlong]
      exact Iff.rfl
    have key := exchange_add_of_isSeparable
      (K := K) (F := F) (F₁ := F₂) (F₂ := F₁) (Z := Z) (Z' := Z')
      hgenZ hgenZ' hdeg' hne' wA wB (Eq.symm hv) _ hT _ hT'
    rw [Finset.sum_congr rfl fun W _ => mul_assoc n _ _,
      Finset.sum_congr rfl fun W _ => mul_assoc n _ _, ← Finset.mul_sum, ← Finset.mul_sum,
      ← mul_add, mul_assoc]
    congr 1
    exact_mod_cast key.symm
  ·
    rw [if_neg (fun h => hv (Place.mem_fiberAlong.mp h))]
    have h0 : ∑ W ∈ Place.fiberAlong u' hu' wA,
        (if Place.restrictAlong u hu W = wB then n * (W.ramificationIndex F₂ : ℤ) * (W.inertiaDeg F₁ : ℤ)
          else 0) = 0 := by
      refine Finset.sum_eq_zero fun W hW => ?_
      rw [if_neg]
      intro hWB
      apply hv
      have h₁ : W.restrict F₂ = wA := Place.mem_fiberAlong.mp hW
      have h₂ : W.restrict F₁ = wB := hWB
      show wB.restrict F = wA.restrict F
      rw [← h₁, ← h₂, hrr]
    have h0' : ∑ W ∈ Place.fiberAlong s' hs' wA,
        (if Place.restrictAlong s hs W = wB then n * (W.ramificationIndex F₂ : ℤ) * (W.inertiaDeg F₁ : ℤ)
          else 0) = 0 := by
      refine Finset.sum_eq_zero fun W hW => ?_
      rw [if_neg]
      intro hWB
      apply hv
      have h₁ : W.restrict F₂ = wA := Place.mem_fiberAlong.mp hW
      have h₂ : W.restrict F₁ = wB := hWB
      show wB.restrict F = wA.restrict F
      rw [← h₁, ← h₂, hrr']
    rw [h0, h0', add_zero]

private theorem separableAlong_of_surjective {F F' : Type*} [Field F] [Field F'] [Algebra k F] [Algebra k F']
    (ψ : F →ₐ[k] F') (h : Function.Surjective ψ) : SeparableAlong k ψ := by
  letI := algebraAlong ψ
  exact ⟨fun y => by
    obtain ⟨x, rfl⟩ := h y
    exact isSeparable_algebraMap (K := F') x⟩

private theorem exists_atkinLehner (M s q' : ℕ) [NeZero M] [NeZero s] [NeZero (M * s)] (hs : s.Prime)
    [Fact q'.Prime] [CharP k q'] (hsq' : s ≠ q') (hq'M : ¬ q' ∣ M) (hsM : ¬ s ∣ M)
    (φ : Fin 2 → (↥(modularFunctionFieldC k M) →ₐ[k] ↥(modularFunctionFieldC k (M * s))))
    (hφα : ∀ x, ((φ 0 x : ↥(modularFunctionFieldC k (M * s))) : LaurentSeries k) = x)
    (hφβ : ∀ x, ((φ 1 x : ↥(modularFunctionFieldC k (M * s))) : LaurentSeries k) = qExpand k s x) :
    ∃ w : ↥(modularFunctionFieldC k (M * s)) →ₐ[k] ↥(modularFunctionFieldC k (M * s)), Function.Surjective w ∧ w.comp (φ 0) = φ 1 ∧ w.comp (φ 1) = φ 0 ∧
      ∀ a : ↥(modularFunctionFieldC k (M * s)), (a : LaurentSeries k) = jqNModC k (M * s) → (w a : LaurentSeries k) = jqNModC k M := by
  have hq'p : q'.Prime := Fact.out
  have hq's : ¬ q' ∣ s := fun h => hsq' ((Nat.prime_dvd_prime_iff_eq hq'p hs).mp h).symm
  have hq'Ms : ¬ q' ∣ M * s := fun h => (hq'p.dvd_mul.mp h).elim hq'M hq's
  have hMk : (M : k) ≠ 0 := (CharP.cast_eq_zero_iff k q' M).not.mpr hq'M
  have hsk : (s : k) ≠ 0 := (CharP.cast_eq_zero_iff k q' s).not.mpr hq's
  obtain ⟨σ, hσ⟩ := exists_algEquiv_atkinLehner_fullC_of_prime_of_not_dvd k M s hs hsM hMk hsk
  have hCF := modularFunctionFieldC_eq_modularFunctionFieldFullC k q' (M * s) hq'Ms
  let e : ↥(modularFunctionFieldC k (M * s)) ≃ₐ[k] ↥(modularFunctionFieldFullC k (M * s)) := IntermediateField.equivOfEq hCF
  let w : ↥(modularFunctionFieldC k (M * s)) ≃ₐ[k] ↥(modularFunctionFieldC k (M * s)) := (e.trans σ).trans e.symm
  have he_coe : ∀ a : ↥(modularFunctionFieldC k (M * s)), ((e a : ↥(modularFunctionFieldFullC k (M * s))) : LaurentSeries k) = a :=
    fun a => rfl

  have h00 : e (φ 0 ⟨jqModC k, jq_mem M⟩)
      = ⟨qExpand k 1 (jqModC k), jqModCd_mem_full k (M * s) (Dvd.dvd.mul_right (one_dvd M) s)⟩ :=
    Subtype.ext (by rw [he_coe, hφα]; exact (qExpand_one_apply _).symm)
  have h0M : e (φ 0 ⟨jqNModC k M, jqN_mem M⟩)
      = ⟨qExpand k M (jqModC k), jqModCd_mem_full k (M * s) (Dvd.dvd.mul_right dvd_rfl s)⟩ :=
    Subtype.ext (by rw [he_coe, hφα]; rfl)
  have h10 : e (φ 1 ⟨jqModC k, jq_mem M⟩)
      = ⟨qExpand k (1 * s) (jqModC k), jqModCd_mem_full k (M * s) (Nat.mul_dvd_mul_right (one_dvd M) s)⟩ :=
    Subtype.ext (by rw [he_coe, hφβ]; simp only [one_mul])
  have h1M : e (φ 1 ⟨jqNModC k M, jqN_mem M⟩)
      = ⟨qExpand k (M * s) (jqModC k), jqModCd_mem_full k (M * s) (Nat.mul_dvd_mul_right dvd_rfl s)⟩ :=
    Subtype.ext (by
      rw [he_coe, hφβ]
      show qExpand k s (qExpand k M (jqModC k)) = qExpand k (M * s) (jqModC k)
      rw [qExpand_qExpand]
      exact qExpand_congr (Nat.mul_comm s M) _)
  refine ⟨w.toAlgHom, w.surjective, ?_, ?_, ?_⟩
  ·
    apply IntermediateField.adjoin_algHom_ext
    rintro x (rfl | rfl)
    · apply Subtype.ext
      show (σ (e (φ 0 ⟨jqModC k, jq_mem M⟩)) : LaurentSeries k) = (φ 1 ⟨jqModC k, jq_mem M⟩ : LaurentSeries k)
      rw [h00, (hσ 1 inferInstance (one_dvd M)).1, hφβ]
      exact qExpand_congr (one_mul s) _
    · apply Subtype.ext
      show (σ (e (φ 0 ⟨jqNModC k M, jqN_mem M⟩)) : LaurentSeries k)
        = (φ 1 ⟨jqNModC k M, jqN_mem M⟩ : LaurentSeries k)
      rw [h0M, (hσ M inferInstance dvd_rfl).1, hφβ]
      show qExpand k (M * s) (jqModC k) = qExpand k s (qExpand k M (jqModC k))
      rw [qExpand_qExpand]
      exact qExpand_congr (Nat.mul_comm M s) _
  ·
    apply IntermediateField.adjoin_algHom_ext
    rintro x (rfl | rfl)
    · apply Subtype.ext
      show (σ (e (φ 1 ⟨jqModC k, jq_mem M⟩)) : LaurentSeries k) = (φ 0 ⟨jqModC k, jq_mem M⟩ : LaurentSeries k)
      rw [h10, (hσ 1 inferInstance (one_dvd M)).2, hφα]
      exact qExpand_one_apply _
    · apply Subtype.ext
      show (σ (e (φ 1 ⟨jqNModC k M, jqN_mem M⟩)) : LaurentSeries k)
        = (φ 0 ⟨jqNModC k M, jqN_mem M⟩ : LaurentSeries k)
      rw [h1M, (hσ M inferInstance dvd_rfl).2, hφα]
      rfl
  ·
    intro a ha
    have hea : e a = ⟨qExpand k (M * s) (jqModC k), jqModCd_mem_full k (M * s) (Nat.mul_dvd_mul_right dvd_rfl s)⟩ :=
      Subtype.ext (by rw [he_coe, ha]; rfl)
    show (σ (e a) : LaurentSeries k) = jqNModC k M
    rw [hea, (hσ M inferInstance dvd_rfl).2]
    rfl

private theorem roof_adjoin_ranges_eq_top (M s : ℕ) [NeZero M] [NeZero s] [NeZero (M * s)] :
    IntermediateField.adjoin k
        (Set.range (heckeBetaC k (M * s) s) ∪ Set.range (heckeAlphaC k (M * s) s)) = ⊤ := by
  have hgen : ({jqModC k, jqNModC k (M * s), jqNModC k s, jqNModC k (M * s * s)} : Set (LaurentSeries k))
      ⊆ (charLDegeneracyRoof k (M * s) s).val ''
          (Set.range (heckeBetaC k (M * s) s) ∪ Set.range (heckeAlphaC k (M * s) s)) := by
    rintro x (rfl | rfl | rfl | rfl)
    · exact ⟨heckeAlphaC k (M * s) s ⟨jqModC k, jq_mem (M * s)⟩,
        Or.inr ⟨⟨jqModC k, jq_mem (M * s)⟩, rfl⟩, coe_heckeAlphaC k (M * s) s ⟨jqModC k, jq_mem (M * s)⟩⟩
    · exact ⟨heckeAlphaC k (M * s) s ⟨jqNModC k (M * s), jqN_mem (M * s)⟩,
        Or.inr ⟨⟨jqNModC k (M * s), jqN_mem (M * s)⟩, rfl⟩,
        coe_heckeAlphaC k (M * s) s ⟨jqNModC k (M * s), jqN_mem (M * s)⟩⟩
    · exact ⟨heckeBetaC k (M * s) s ⟨jqModC k, jq_mem (M * s)⟩, Or.inl ⟨⟨jqModC k, jq_mem (M * s)⟩, rfl⟩, rfl⟩
    · refine ⟨heckeBetaC k (M * s) s ⟨jqNModC k (M * s), jqN_mem (M * s)⟩,
        Or.inl ⟨⟨jqNModC k (M * s), jqN_mem (M * s)⟩, rfl⟩, ?_⟩
      show qExpand k s (qExpand k (M * s) (jqModC k)) = qExpand k (M * s * s) (jqModC k)
      rw [qExpand_qExpand]
      exact qExpand_congr (Nat.mul_comm s (M * s)) _
  rw [eq_top_iff]
  intro z _
  have hz : (z : LaurentSeries k) ∈ IntermediateField.adjoin k ((charLDegeneracyRoof k (M * s) s).val ''
      (Set.range (heckeBetaC k (M * s) s) ∪ Set.range (heckeAlphaC k (M * s) s))) :=
    (IntermediateField.adjoin_le_iff.mpr (hgen.trans (IntermediateField.subset_adjoin k _))) z.2
  rw [← IntermediateField.adjoin_map] at hz
  obtain ⟨y, hy, hyz⟩ := (IntermediateField.mem_map _).mp hz
  exact (Subtype.ext hyz : y = z) ▸ hy

private theorem jqN_mul_mul_ne (M s : ℕ) [NeZero M] [NeZero s] [NeZero (M * s)]
    (hs : s.Prime) : qExpand k s (jqNModC k (M * s)) ≠ jqNModC k M := by
  intro h
  have h1 : qExpand k s (jqNModC k (M * s)) = jqNModC k (M * s * s) := by
    show qExpand k s (qExpand k (M * s) (jqModC k)) = qExpand k (M * s * s) (jqModC k)
    rw [qExpand_qExpand]
    exact qExpand_congr (Nat.mul_comm s (M * s)) _
  rw [h1] at h
  have h2 := congrArg HahnSeries.order h
  rw [order_jqNModC, order_jqNModC] at h2
  have h3 : M * s * s = M := by exact_mod_cast neg_injective h2
  have h4 : M * 2 * 2 ≤ M * s * s := Nat.mul_le_mul (Nat.mul_le_mul_left M hs.two_le) hs.two_le
  rw [h3] at h4
  have hM := NeZero.pos M
  omega

private theorem square_formula [IsAlgClosed k] (M s q' : ℕ) [NeZero M] [NeZero s] [NeZero (M * s)] (hs : s.Prime)
    [Fact q'.Prime] [CharP k q'] (hsq' : s ≠ q') (hq'M : ¬ q' ∣ M) (hsM : ¬ s ∣ M)
    [HasPrincipalDivisors k ↥(charLDegeneracyRoof k (M * s) s)] [HasPrincipalDivisors k ↥(modularFunctionFieldC k (M * s))]
    (φ : Fin 2 → (↥(modularFunctionFieldC k M) →ₐ[k] ↥(modularFunctionFieldC k (M * s))))
    (hφ : ∀ i, (φ i).toRingHom.IsIntegral)
    (hφα : ∀ x, ((φ 0 x : ↥(modularFunctionFieldC k (M * s))) : LaurentSeries k) = x)
    (hφβ : ∀ x, ((φ 1 x : ↥(modularFunctionFieldC k (M * s))) : LaurentSeries k) = qExpand k s x)
    (hα₁ : HeckeAlphaCIntegral k (M * s) s) (hβ₁ : HeckeBetaCIntegral k (M * s) s)
    (w : ↥(modularFunctionFieldC k (M * s)) →ₐ[k] ↥(modularFunctionFieldC k (M * s))) (hwsurj : Function.Surjective w) (hw0 : w.comp (φ 0) = φ 1)
    (hwj : ∀ a : ↥(modularFunctionFieldC k (M * s)), (a : LaurentSeries k) = jqNModC k (M * s) → (w a : LaurentSeries k) = jqNModC k M)
    (hw : w.toRingHom.IsIntegral) (hid : (AlgHom.id k ↥(modularFunctionFieldC k (M * s))).toRingHom.IsIntegral)
    (D : Divisor k ↥(modularFunctionFieldC k (M * s))) :
    Divisor.pullbackAlong (φ 0) (hφ 0) (Divisor.pushforwardAlong (φ 1) (hφ 1) D)
      = Divisor.pushforwardAlong (heckeBetaC k (M * s) s) hβ₁
          (Divisor.pullbackAlong (heckeAlphaC k (M * s) s) hα₁ D)
        + Divisor.pushforwardAlong w hw (Divisor.pullbackAlong (AlgHom.id k _) hid D) := by
  classical
  haveI : Fact s.Prime := ⟨hs⟩
  obtain ⟨hfin, hsep, hdeg1, -, -⟩ :=
    degeneracyPair_finiteSeparableDeg_ssPlaces_preserved_reflected M s q' hs hsq' hq'M hsM (k := k) φ hφ hφα hφβ
  have hnd : ¬ q' ∣ M * s * s := not_dvd_mul_mul M s q' hs hsq' hq'M
  exact pullbackAlong_pushforwardAlong_eq_add_of_separable (φ 0) (φ 1)
    (heckeBetaC k (M * s) s) (heckeAlphaC k (M * s) s) w (AlgHom.id k _)
    (betaC_comp_eq_alphaC_comp M s φ hφα hφβ) (by rw [hw0, AlgHom.id_comp])
    (hφ 0) (hφ 1) hβ₁ hα₁ hw hid (hfin 0) (hfin 1)
    (finiteAlong_heckeBetaC k (M * s) s) (finiteAlong_heckeAlphaC k (M * s) s)
    (finiteAlong_of_surjective w hwsurj) (finiteAlong_of_surjective _ Function.surjective_id)
    (hsep 1) (separableAlong_heckeAlphaC_heckeBetaC k (ℓ := q') (M * s) s hnd).2
    (separableAlong_of_surjective _ hwsurj)
    (roof_adjoin_ranges_eq_top M s)
    (by
      rw [eq_top_iff]
      intro x _
      exact IntermediateField.subset_adjoin k _ (Set.mem_union_right _ ⟨x, rfl⟩))
    (by rw [finrankAlong_alphaC_eq M s q' hs hsq' hq'M hsM, finrankAlong_id, hdeg1 0])
    ⟨⟨jqNModC k (M * s), jqN_mem (M * s)⟩, w ⟨jqNModC k (M * s), jqN_mem (M * s)⟩, rfl, fun h => by
      have h' := congrArg (fun z : ↥(charLDegeneracyRoof k (M * s) s) => (z : LaurentSeries k)) h
      simp only [coe_heckeBetaC, coe_heckeAlphaC] at h'
      rw [hwj _ rfl] at h'
      exact jqN_mul_mul_ne M s hs h'⟩
    D

private theorem graph_term (M s : ℕ) [NeZero M] [NeZero s] [NeZero (M * s)]
    [HasPrincipalDivisors k ↥(modularFunctionFieldC k (M * s))]
    (φ : Fin 2 → (↥(modularFunctionFieldC k M) →ₐ[k] ↥(modularFunctionFieldC k (M * s))))
    (hφ : ∀ i, (φ i).toRingHom.IsIntegral)
    (w : ↥(modularFunctionFieldC k (M * s)) →ₐ[k] ↥(modularFunctionFieldC k (M * s))) (hw1 : w.comp (φ 1) = φ 0)
    (hw : w.toRingHom.IsIntegral) (hid : (AlgHom.id k ↥(modularFunctionFieldC k (M * s))).toRingHom.IsIntegral)
    (D : Divisor k ↥(modularFunctionFieldC k (M * s))) :
    Divisor.pushforwardAlong (φ 1) (hφ 1)
        (Divisor.pushforwardAlong w hw (Divisor.pullbackAlong (AlgHom.id k _) hid D))
      = Divisor.pushforwardAlong (φ 0) (hφ 0) D := by
  have hw1' : (w.comp (φ 1)).toRingHom.IsIntegral := by rw [hw1]; exact hφ 0
  have hid0 : ((AlgHom.id k ↥(modularFunctionFieldC k (M * s))).comp (φ 0)).toRingHom.IsIntegral := by
    rw [AlgHom.id_comp]; exact hφ 0
  rw [Divisor.pushforwardAlong_pushforwardAlong (φ 1) w (hφ 1) hw hw1', pushforwardAlong_congr hw1 hw1' (hφ 0)]
  conv_rhs => rw [← Divisor.pushforwardAlong_pullbackAlong_of_surjective (AlgHom.id k _) hid Function.surjective_id D,
    Divisor.pushforwardAlong_pushforwardAlong (φ 0) (AlgHom.id k _) (hφ 0) hid hid0,
    pushforwardAlong_congr (AlgHom.id_comp (φ 0)) hid0 (hφ 0)]

end DegeneracyLevelPrime

open DegeneracyLevelPrime in

private theorem DegeneracyLevelPrime.leg_one
    (M s q' : ℕ) [NeZero M] [NeZero s] (hs : s.Prime) [Fact q'.Prime]
    (hsq' : s ≠ q') (hq'M : ¬ q' ∣ M) (hsM : ¬ s ∣ M)
    {k : Type*} [Field k] [CharP k q'] [IsAlgClosed k] :
    haveI : NeZero (M * s) := ⟨Nat.mul_ne_zero (NeZero.ne M) (NeZero.ne s)⟩
    ∀ [HasPrincipalDivisors k ↥(charLDegeneracyRoof k (M * s) s)]
      [HasPrincipalDivisors k ↥(charLDegeneracyRoof k M s)]
      (φ : Fin 2 → (↥(modularFunctionFieldC k M) →ₐ[k] ↥(modularFunctionFieldC k (M * s))))
      (hφ : ∀ i, (φ i).toRingHom.IsIntegral)
      (hφα : ∀ x, ((φ 0 x : ↥(modularFunctionFieldC k (M * s))) : LaurentSeries k) = x)
      (hφβ : ∀ x, ((φ 1 x : ↥(modularFunctionFieldC k (M * s))) : LaurentSeries k)
        = qExpand k s x)
      (hα₁ : HeckeAlphaCIntegral k (M * s) s) (hβ₁ : HeckeBetaCIntegral k (M * s) s)
      (hα₀ : HeckeAlphaCIntegral k M s) (hβ₀ : HeckeBetaCIntegral k M s)
      (D : Divisor k ↥(modularFunctionFieldC k (M * s))),
      Divisor.pushforwardAlong (φ 0) (hφ 0)
          (Divisor.correspondence (heckeAlphaC k (M * s) s) (heckeBetaC k (M * s) s) hα₁ hβ₁ D)
        = (s : ℤ) • Divisor.pushforwardAlong (φ 1) (hφ 1) D := by
  intro _ _ φ hφ hφα hφβ hα₁ hβ₁ hα₀ hβ₀ D
  haveI : NeZero (M * s) := ⟨Nat.mul_ne_zero (NeZero.ne M) (NeZero.ne s)⟩
  have hβφ : ((heckeBetaC k (M * s) s).comp (φ 0)).toRingHom.IsIntegral :=
    RingHom.IsIntegral.trans (φ 0).toRingHom (heckeBetaC k (M * s) s).toRingHom (hφ 0) hβ₁
  have hαφ : ((heckeAlphaC k (M * s) s).comp (φ 1)).toRingHom.IsIntegral :=
    RingHom.IsIntegral.trans (φ 1).toRingHom (heckeAlphaC k (M * s) s).toRingHom (hφ 1) hα₁
  rw [Divisor.correspondence_apply,
    Divisor.pushforwardAlong_pushforwardAlong (φ 0) (heckeBetaC k (M * s) s) (hφ 0) hβ₁ hβφ,
    pushforwardAlong_congr (betaC_comp_eq_alphaC_comp M s φ hφα hφβ) hβφ hαφ,
    ← Divisor.pushforwardAlong_pushforwardAlong (φ 1) (heckeAlphaC k (M * s) s) (hφ 1) hα₁ hαφ,
    ← Divisor.correspondence_apply, correspondence_alphaC_alphaC M s q' hs hsq' hq'M hsM hα₁ D, map_zsmul]

private theorem DegeneracyLevelPrime.leg_two
    (M s q' : ℕ) [NeZero M] [NeZero s] (hs : s.Prime) [Fact q'.Prime]
    (hsq' : s ≠ q') (hq'M : ¬ q' ∣ M) (hsM : ¬ s ∣ M)
    {k : Type*} [Field k] [CharP k q'] [IsAlgClosed k] :
    haveI : NeZero (M * s) := ⟨Nat.mul_ne_zero (NeZero.ne M) (NeZero.ne s)⟩
    ∀ [HasPrincipalDivisors k ↥(charLDegeneracyRoof k (M * s) s)]
      [HasPrincipalDivisors k ↥(charLDegeneracyRoof k M s)]
      (φ : Fin 2 → (↥(modularFunctionFieldC k M) →ₐ[k] ↥(modularFunctionFieldC k (M * s))))
      (hφ : ∀ i, (φ i).toRingHom.IsIntegral)
      (hφα : ∀ x, ((φ 0 x : ↥(modularFunctionFieldC k (M * s))) : LaurentSeries k) = x)
      (hφβ : ∀ x, ((φ 1 x : ↥(modularFunctionFieldC k (M * s))) : LaurentSeries k)
        = qExpand k s x)
      (hα₁ : HeckeAlphaCIntegral k (M * s) s) (hβ₁ : HeckeBetaCIntegral k (M * s) s)
      (hα₀ : HeckeAlphaCIntegral k M s) (hβ₀ : HeckeBetaCIntegral k M s)
      (D : Divisor k ↥(modularFunctionFieldC k (M * s))),
      Divisor.pushforwardAlong (φ 1) (hφ 1)
          (Divisor.correspondence (heckeAlphaC k (M * s) s) (heckeBetaC k (M * s) s) hα₁ hβ₁ D)
        = Divisor.correspondence (heckeAlphaC k M s) (heckeBetaC k M s) hα₀ hβ₀
            (Divisor.pushforwardAlong (φ 1) (hφ 1) D)
          - Divisor.pushforwardAlong (φ 0) (hφ 0) D  := by
  intro _ _ φ hφ hφα hφβ hα₁ hβ₁ hα₀ hβ₀ D
  haveI : NeZero (M * s) := ⟨Nat.mul_ne_zero (NeZero.ne M) (NeZero.ne s)⟩
  have hEq := charLDegeneracyRoof_eq M s φ hφα hφβ
  haveI hPC : HasPrincipalDivisors k ↥(modularFunctionFieldC k (M * s)) := by rw [← hEq]; infer_instance
  obtain ⟨w, hwsurj, hw0, hw1, hwj⟩ := exists_atkinLehner M s q' hs hsq' hq'M hsM φ hφα hφβ
  have hw : w.toRingHom.IsIntegral := RingHom.isIntegral_of_surjective _ hwsurj
  have hid : (AlgHom.id k ↥(modularFunctionFieldC k (M * s))).toRingHom.IsIntegral :=
    RingHom.isIntegral_of_surjective _ Function.surjective_id
  rw [correspondence_level_eq M s φ hφ hφα hφβ hα₀ hβ₀ (Divisor.pushforwardAlong (φ 1) (hφ 1) D),
    square_formula M s q' hs hsq' hq'M hsM φ hφ hφα hφβ hα₁ hβ₁ w hwsurj hw0 hwj hw hid D, map_add,
    graph_term M s φ hφ w hw1 hw hid D, Divisor.correspondence_apply, add_sub_cancel_right]

open DegeneracyLevelPrime in

theorem solution
    (M s q' : ℕ) [NeZero M] [NeZero s] (hs : s.Prime) [Fact q'.Prime]
    (hsq' : s ≠ q') (hq'M : ¬ q' ∣ M) (hsM : ¬ s ∣ M)
    {k : Type*} [Field k] [CharP k q'] [IsAlgClosed k] :
    haveI : NeZero (M * s) := ⟨Nat.mul_ne_zero (NeZero.ne M) (NeZero.ne s)⟩
    ∀ [HasPrincipalDivisors k ↥(charLDegeneracyRoof k (M * s) s)]
      [HasPrincipalDivisors k ↥(charLDegeneracyRoof k M s)]
      (φ : Fin 2 → (↥(modularFunctionFieldC k M) →ₐ[k] ↥(modularFunctionFieldC k (M * s))))
      (hφ : ∀ i, (φ i).toRingHom.IsIntegral)
      (hφα : ∀ x, ((φ 0 x : ↥(modularFunctionFieldC k (M * s))) : LaurentSeries k) = x)
      (hφβ : ∀ x, ((φ 1 x : ↥(modularFunctionFieldC k (M * s))) : LaurentSeries k)
        = qExpand k s x)
      (hα₁ : HeckeAlphaCIntegral k (M * s) s) (hβ₁ : HeckeBetaCIntegral k (M * s) s)
      (hα₀ : HeckeAlphaCIntegral k M s) (hβ₀ : HeckeBetaCIntegral k M s)
      (D : Divisor k ↥(modularFunctionFieldC k (M * s))),
      Divisor.pushforwardAlong (φ 0) (hφ 0)
          (Divisor.correspondence (heckeAlphaC k (M * s) s) (heckeBetaC k (M * s) s) hα₁ hβ₁ D)
        = (s : ℤ) • Divisor.pushforwardAlong (φ 1) (hφ 1) D ∧
      Divisor.pushforwardAlong (φ 1) (hφ 1)
          (Divisor.correspondence (heckeAlphaC k (M * s) s) (heckeBetaC k (M * s) s) hα₁ hβ₁ D)
        = Divisor.correspondence (heckeAlphaC k M s) (heckeBetaC k M s) hα₀ hβ₀
            (Divisor.pushforwardAlong (φ 1) (hφ 1) D)
          - Divisor.pushforwardAlong (φ 0) (hφ 0) D := by
  intro _ _ φ hφ hφα hφβ hα₁ hβ₁ hα₀ hβ₀ D
  exact ⟨leg_one M s q' hs hsq' hq'M hsM φ hφ hφα hφβ hα₁ hβ₁ hα₀ hβ₀ D,
    leg_two M s q' hs hsq' hq'M hsM φ hφ hφα hφβ hα₁ hβ₁ hα₀ hβ₀ D⟩

#print axioms solution

end S_ModularCurve_degeneracyPair_pushforwardAlong_correspondence_levelPrime_identities
end P2MW
export P2MW.S_ModularCurve_degeneracyPair_pushforwardAlong_correspondence_levelPrime_identities (solution)
