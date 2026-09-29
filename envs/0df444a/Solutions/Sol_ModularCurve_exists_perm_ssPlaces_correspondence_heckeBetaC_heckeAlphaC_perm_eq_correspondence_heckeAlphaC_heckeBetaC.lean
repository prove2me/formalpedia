-- Prove2me | solution 1 for ModularCurve.exists_perm_ssPlaces_correspondence_heckeBetaC_heckeAlphaC_perm_eq_correspondence_heckeAlphaC_heckeBetaC
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/8ea20428-68ff-57be-8f1b-cb19b76cec9e

import Mathlib
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_ModularCurve_CoeffSemilinearAut
import Definitions.Def_ModularCurve_X0ModL
import Definitions.Def_ModularCurve_FibrePoly
import Theorems.Thm_ModularCurve_mem_ssJSet_of_mem_roots_fibrePoly
import Theorems.Thm_ModularCurve_nonempty_modularPolynomialData
import Theorems.Thm_ModularCurve_modularFunctionFieldC_eq_modularFunctionFieldFullC
import Definitions.Def_ModularCurve_CharLDegeneracyHecke
import Theorems.Thm_ModularCurve_exists_algEquiv_modularFunctionFieldC_swap_and_charLDegeneracyRoof_swap
import Theorems.Thm_AlgebraicCurve_Divisor_ofAlgAut_smul_correspondence_eq_correspondence_ofAlgAut_smul_of_comp_eq_comp
import Theorems.Thm_ModularCurve_ringHom_ext_of_apply_jGeomGen_eq_of_apply_jNGeomGen_eq
import Theorems.Thm_ModularCurve_hasPrincipalDivisors_modularFunctionFieldC_of_perfectField
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_perm_ssPlaces_correspondence_heckeBetaC_heckeAlphaC_perm_eq_correspondence_heckeAlphaC_heckeBetaC
p2m_attr_erase "instance" "WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.instSMulAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instDistribMulActionAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange"
p2m_attr_erase "simp" "WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluX_empty WeierstrassCurve.veluY_empty WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm AddMonoid.End.dualEndDataOfSurjective_trace AddMonoid.End.dualEndDataOfSurjective_norm WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec"
p2m_attr_erase "simp" "compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero"
p2m_attr_erase "simp" "ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero ModularCurve.ProjectiveLine.map_mk ModularCurve.coe_jqNGen ModularCurve.baseAut_arithmeticGalois ModularCurve.JZero.torsionGaloisRep_apply ModularCurve.coe_arithmeticRingAut_apply ModularCurve.toRingAut_arithmeticGalois ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar"

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

p2m_open "ModularCurve P2MW.S_ModularCurve_exists_perm_ssPlaces_correspondence_heckeBetaC_heckeAlphaC_perm_eq_correspondence_heckeAlphaC_heckeBetaC.ModularCurve AlgebraicCurve Polynomial"

namespace ModularCurve
p2m_export "ModularCurve" "isSupersingularPlace_iff ssPlaces mem_ssPlaces_iff jGeomGen jNGeomGen evalModularPair map_evalModularPair evalModularPair_jq_eq_zero IsCentreOf exists_isCentreOf_of_isRational qExpand qExpand_congr qExpand_qExpand ModularPolynomialData jqModC jqNModC jqNModC_one modularFunctionFieldC fibrePoly ssJSet arithFrobC arithFrobC_smul_jq arithFrobC_smul_jqN jqModCd_mem_full mem_ssJSet_of_mem_roots_fibrePoly nonempty_modularPolynomialData modularFunctionFieldC_eq_modularFunctionFieldFullC charLDegeneracyRoof heckeAlphaC heckeBetaC exists_algEquiv_modularFunctionFieldC_swap_and_charLDegeneracyRoof_swap ringHom_ext_of_apply_jGeomGen_eq_of_apply_jNGeomGen_eq hasPrincipalDivisors_modularFunctionFieldC_of_perfectField"
p2m_open "ModularCurve"
namespace FrickeB1

section ModularEquations

variable {K : Type*} [Field K]

theorem evalModularPair_eq_zero_of_coe (F : IntermediateField K (LaurentSeries K)) (x y : F)
    (Φ : Polynomial (Polynomial ℤ)) (h : evalModularPair (x : LaurentSeries K) (y : LaurentSeries K) Φ = 0) :
    evalModularPair x y Φ = 0 := by
  have hval := map_evalModularPair F.val.toRingHom x y Φ
  refine (map_eq_zero_iff _ F.val.toRingHom.injective).mp ?_
  rw [hval]
  exact h

theorem evalModularPair_j_jn (F : IntermediateField K (LaurentSeries K)) {n : ℕ} [NeZero n]
    (data : ModularPolynomialData n) (hj : jqModC K ∈ F) (hjn : jqNModC K n ∈ F) :
    evalModularPair (⟨jqModC K, hj⟩ : F) ⟨jqNModC K n, hjn⟩ data.Φ = 0 :=
  evalModularPair_eq_zero_of_coe F _ _ _ (evalModularPair_jq_eq_zero K data)

end ModularEquations

section IntegralityFromRelation

theorem isIntegral_of_evalModularPair_eq_zero {A R : Type*} [CommRing A] [CommRing R] [Algebra A R]
    (Φ : Polynomial (Polynomial ℤ)) (hΦ : Φ.Monic) (a : A) (y : R)
    (h : evalModularPair (algebraMap A R a) y Φ = 0) : IsIntegral A y := by
  refine ⟨Φ.map (Polynomial.eval₂RingHom (Int.castRingHom A) a), hΦ.map _, ?_⟩
  rw [Polynomial.eval₂_map]
  have hcomp : (algebraMap A R).comp (Polynomial.eval₂RingHom (Int.castRingHom A) a) =
      Polynomial.eval₂RingHom (Int.castRingHom R) (algebraMap A R a) := by
    refine Polynomial.ringHom_ext' (Subsingleton.elim _ _) ?_
    rw [RingHom.comp_apply, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X, Polynomial.coe_eval₂RingHom,
      Polynomial.eval₂_X]
  rw [hcomp]
  exact h

theorem mem_valuationSubring_of_isIntegral {F : Type*} [Field F] (O : ValuationSubring F) {x : F}
    (hx : IsIntegral O x) : x ∈ O := by
  have hv : O.valuation.Integers O :=
    { hom_inj := Subtype.val_injective
      map_le_one := fun a => O.valuation_le_one a
      exists_of_le_one := fun r hr => ⟨⟨r, O.mem_of_valuation_le_one r hr⟩, rfl⟩ }
  exact (O.valuation_le_one_iff x).mp (hv.mem_of_integral hx)

theorem mem_valuationSubring_of_evalModularPair_eq_zero {F : Type*} [Field F] (O : ValuationSubring F)
    (Φ : Polynomial (Polynomial ℤ)) (hΦ : Φ.Monic) {x y : F} (hx : x ∈ O)
    (h : evalModularPair x y Φ = 0) : y ∈ O :=
  mem_valuationSubring_of_isIntegral O
    (isIntegral_of_evalModularPair_eq_zero (A := O) Φ hΦ ⟨x, hx⟩ y h)

variable {K : Type*} [Field K]

theorem jn_mem_valuationSubring (F : IntermediateField K (LaurentSeries K)) (n : ℕ) [NeZero n]
    (hj : jqModC K ∈ F) (hjn : jqNModC K n ∈ F) (O : ValuationSubring F)
    (hjO : (⟨jqModC K, hj⟩ : F) ∈ O) : (⟨jqNModC K n, hjn⟩ : F) ∈ O := by
  obtain ⟨data⟩ := ModularCurve.nonempty_modularPolynomialData n
  exact mem_valuationSubring_of_evalModularPair_eq_zero O data.Φ data.monic hjO
    (evalModularPair_j_jn F data hj hjn)

end IntegralityFromRelation

section SupersingularStep

variable {p : ℕ} [Fact p.Prime] {K : Type*} [Field K] [CharP K p] [IsAlgClosed K] [DecidableEq K]
variable {F : Type*} [Field F] [Algebra K F]

theorem evalAt_mem_ssJSet_of_evalModularPair_eq_zero {s : ℕ} [Fact s.Prime] (hsp : s ≠ p)
    (data : ModularPolynomialData s) (W : Place K F) (hrat : W.IsRational) {x y : F}
    (hx : x ∈ W.toValuationSubring) (hy : y ∈ W.toValuationSubring)
    (h : evalModularPair x y data.Φ = 0) (hss : W.evalAt x ∈ ssJSet p K) : W.evalAt y ∈ ssJSet p K := by

  have hO : evalModularPair (⟨x, hx⟩ : W.toValuationSubring) ⟨y, hy⟩ data.Φ = 0 := by
    have hval := map_evalModularPair (SubringClass.subtype W.toValuationSubring)
      (⟨x, hx⟩ : W.toValuationSubring) ⟨y, hy⟩ data.Φ
    refine (map_eq_zero_iff (SubringClass.subtype W.toValuationSubring) Subtype.val_injective).mp ?_
    rw [hval]
    exact h

  have hK : evalModularPair (W.evalAt x) (W.evalAt y) data.Φ = 0 := by
    have hres := congrArg (IsLocalRing.residue W.toValuationSubring) hO
    rw [map_zero, map_evalModularPair, ← W.algebraMap_evalAt hrat hx, ← W.algebraMap_evalAt hrat hy,
      ← map_evalModularPair] at hres
    exact (map_eq_zero_iff _ (algebraMap K W.ResidueField).injective).mp hres

  have hroot : W.evalAt y ∈ (fibrePoly data.Φ (W.evalAt x)).roots := by
    unfold fibrePoly
    rw [Polynomial.mem_roots ((data.monic.map _).ne_zero), Polynomial.IsRoot.def, Polynomial.eval_map]
    exact hK
  exact ModularCurve.mem_ssJSet_of_mem_roots_fibrePoly p hsp data hss hroot

end SupersingularStep

section Chain0

variable (K : Type*) [Field K]

theorem evalModularPair_jqNModC_jqNModC_mul (d s : ℕ) [NeZero d] [NeZero s] [NeZero (s * d)]
    (data : ModularPolynomialData s) :
    evalModularPair (jqNModC K d) (jqNModC K (s * d)) data.Φ = 0 := by
  have h := congrArg (qExpand K d) (evalModularPair_jq_eq_zero K data)
  rw [map_zero, map_evalModularPair] at h
  have e1 : qExpand K d (jqModC K) = jqNModC K d := rfl
  haveI : NeZero (d * s) := ⟨mul_ne_zero (NeZero.ne d) (NeZero.ne s)⟩
  have e2 : qExpand K d (jqNModC K s) = jqNModC K (s * d) := by
    show qExpand K d (qExpand K s (jqModC K)) = qExpand K (s * d) (jqModC K)
    rw [qExpand_qExpand, qExpand_congr (mul_comm d s)]
  rwa [e1, e2] at h

end Chain0

section Chain

variable {p : ℕ} [Fact p.Prime] {K : Type*} [Field K] [CharP K p] [IsAlgClosed K] [DecidableEq K]

theorem jqNModC_mem_of_dvd (L : ℕ) [NeZero L] (hpL : ¬ p ∣ L) {d : ℕ} [NeZero d] (hd : d ∣ L) :
    jqNModC K d ∈ modularFunctionFieldC K L := by
  rw [ModularCurve.modularFunctionFieldC_eq_modularFunctionFieldFullC K p L hpL]
  exact jqModCd_mem_full K L hd

theorem jqNModC_mem_and_evalAt_mem_ssJSet (L : ℕ) [NeZero L] (hpL : ¬ p ∣ L)
    (W : Place K (modularFunctionFieldC K L)) (hrat : W.IsRational)
    (hj : jGeomGen K L ∈ W.toValuationSubring) (hss : W.evalAt (jGeomGen K L) ∈ ssJSet p K) :
    ∀ (d : ℕ) [NeZero d] (hd : d ∣ L),
      (⟨jqNModC K d, jqNModC_mem_of_dvd (p := p) L hpL hd⟩ : modularFunctionFieldC K L) ∈ W.toValuationSubring ∧
      W.evalAt (⟨jqNModC K d, jqNModC_mem_of_dvd (p := p) L hpL hd⟩ : modularFunctionFieldC K L) ∈ ssJSet p K := by
  intro d
  induction d using UniqueFactorizationMonoid.induction_on_prime with
  | h₁ =>
    intro inst _
    exact absurd rfl (NeZero.ne (0 : ℕ))
  | h₂ x hx =>
    intro inst hdvd
    have hx1 : x = 1 := Nat.isUnit_iff.mp hx
    subst hx1
    have e : (⟨jqNModC K 1, jqNModC_mem_of_dvd (p := p) L hpL hdvd⟩ : modularFunctionFieldC K L) = jGeomGen K L :=
      Subtype.ext (jqNModC_one K)
    rw [e]
    exact ⟨hj, hss⟩
  | h₃ a s ha hs IH =>
    intro inst hdvd
    haveI : NeZero a := ⟨ha⟩
    have hsP : s.Prime := Nat.prime_iff.mpr hs
    haveI : Fact s.Prime := ⟨hsP⟩
    haveI : NeZero s := ⟨hsP.ne_zero⟩
    have haL : a ∣ L := dvd_trans (Dvd.intro_left s rfl) hdvd
    have hsL : s ∣ L := dvd_trans (Dvd.intro a rfl) hdvd
    have hsp : s ≠ p := by
      rintro rfl
      exact hpL hsL
    obtain ⟨hxO, hxss⟩ := IH haL
    obtain ⟨data⟩ := ModularCurve.nonempty_modularPolynomialData s

    have hrel : evalModularPair
        (⟨jqNModC K a, jqNModC_mem_of_dvd (p := p) L hpL haL⟩ : modularFunctionFieldC K L)
        ⟨jqNModC K (s * a), jqNModC_mem_of_dvd (p := p) L hpL hdvd⟩ data.Φ = 0 :=
      evalModularPair_eq_zero_of_coe _ _ _ _ (evalModularPair_jqNModC_jqNModC_mul K a s data)
    have hyO := mem_valuationSubring_of_evalModularPair_eq_zero W.toValuationSubring data.Φ data.monic hxO hrel
    exact ⟨hyO, evalAt_mem_ssJSet_of_evalModularPair_eq_zero hsp data W hrat hxO hyO hrel hxss⟩

theorem evalAt_jNGeomGen_mem_ssJSet (L : ℕ) [NeZero L] (hpL : ¬ p ∣ L)
    {W : Place K (modularFunctionFieldC K L)} (hW : W ∈ ssPlaces p L K) :
    W.evalAt (jNGeomGen K L) ∈ ssJSet p K := by
  obtain ⟨hrat, haff, hss⟩ := (isSupersingularPlace_iff p L K W).mp ((mem_ssPlaces_iff p L K).mp hW)
  have h := (jqNModC_mem_and_evalAt_mem_ssJSet L hpL W hrat haff.1 hss L dvd_rfl).2
  have e : (⟨jqNModC K L, jqNModC_mem_of_dvd (p := p) L hpL dvd_rfl⟩ : modularFunctionFieldC K L) = jNGeomGen K L :=
    Subtype.ext rfl
  rwa [e] at h

end Chain

section Swap

variable {K : Type*} [Field K]

theorem isRational_smul {F : Type*} [Field F] [Algebra K F] (g : SemilinearAut K F) {v : Place K F}
    (hv : v.IsRational) : (g • v).IsRational := by
  intro y
  obtain ⟨a, ha⟩ := hv ((SemilinearAut.smulResidueRingEquiv g v).symm y)
  refine ⟨SemilinearAut.baseAut g a, ?_⟩
  rw [← SemilinearAut.smulResidueRingEquiv_algebraMap, ha, RingEquiv.apply_symm_apply]

variable {N : ℕ} [NeZero N]

theorem isCentreOf_smul_of_swap (g : SemilinearAut K (modularFunctionFieldC K N))
    (hj : g • jGeomGen K N = jNGeomGen K N) (hjN : g • jNGeomGen K N = jGeomGen K N)
    {c : K × K} {w : Place K (modularFunctionFieldC K N)} (h : IsCentreOf K N c w) :
    IsCentreOf K N (SemilinearAut.baseAut g c.2, SemilinearAut.baseAut g c.1) (g • w) := by
  constructor
  · show 0 < (g • w).ord (jGeomGen K N
      - algebraMap K (modularFunctionFieldC K N) (SemilinearAut.baseAut g c.2))
    have e : jGeomGen K N - algebraMap K (modularFunctionFieldC K N) (SemilinearAut.baseAut g c.2)
        = g • (jNGeomGen K N - algebraMap K (modularFunctionFieldC K N) c.2) := by
      rw [smul_sub, hjN, SemilinearAut.smul_algebraMap]
    rw [e, SemilinearAut.ord_smul]
    exact h.2
  · show 0 < (g • w).ord (jNGeomGen K N
      - algebraMap K (modularFunctionFieldC K N) (SemilinearAut.baseAut g c.1))
    have e : jNGeomGen K N - algebraMap K (modularFunctionFieldC K N) (SemilinearAut.baseAut g c.1)
        = g • (jGeomGen K N - algebraMap K (modularFunctionFieldC K N) c.1) := by
      rw [smul_sub, hj, SemilinearAut.smul_algebraMap]
    rw [e, SemilinearAut.ord_smul]
    exact h.1

variable {p : ℕ} [Fact p.Prime] [CharP K p] [IsAlgClosed K] [DecidableEq K]

theorem ofAlgAut_smul_mem_ssPlaces_of_swap (hpN : ¬ p ∣ N)
    (σ : ↥(modularFunctionFieldC K N) ≃ₐ[K] ↥(modularFunctionFieldC K N))
    (hj : σ (jGeomGen K N) = jNGeomGen K N) (hjN : σ (jNGeomGen K N) = jGeomGen K N)
    (W : Place K (modularFunctionFieldC K N)) (hW : W ∈ ssPlaces p N K) :
    SemilinearAut.ofAlgAut σ • W ∈ ssPlaces p N K := by
  set g := SemilinearAut.ofAlgAut σ with hg
  obtain ⟨hrat, haff, hss⟩ := (isSupersingularPlace_iff p N K W).mp ((mem_ssPlaces_iff p N K).mp hW)
  have hj' : g • jGeomGen K N = jNGeomGen K N := by
    rw [hg, SemilinearAut.smul_def, SemilinearAut.toRingAut_ofAlgAut]; exact hj
  have hjN' : g • jNGeomGen K N = jGeomGen K N := by
    rw [hg, SemilinearAut.smul_def, SemilinearAut.toRingAut_ofAlgAut]; exact hjN
  have hc' := isCentreOf_smul_of_swap g hj' hjN' (exists_isCentreOf_of_isRational hrat haff)
  refine (mem_ssPlaces_iff p N K).mpr ⟨isRational_smul g hrat, hc'.isAffineGeomPlace, ?_⟩
  rw [hc'.evalAt_jGeomGen]
  have hb : SemilinearAut.baseAut g = 1 := rfl
  show SemilinearAut.baseAut g (W.evalAt (jNGeomGen K N)) ∈ ssJSet p K
  rw [hb]
  exact evalAt_jNGeomGen_mem_ssJSet N hpN hW

end Swap

end FrickeB1
end ModularCurve

end

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

noncomputable section

p2m_open "AlgebraicCurve ModularCurve P2MW.S_ModularCurve_exists_perm_ssPlaces_correspondence_heckeBetaC_heckeAlphaC_perm_eq_correspondence_heckeAlphaC_heckeBetaC.ModularCurve"

namespace ModularCurve
p2m_export "ModularCurve" "isSupersingularPlace_iff ssPlaces mem_ssPlaces_iff jGeomGen jNGeomGen evalModularPair map_evalModularPair evalModularPair_jq_eq_zero IsCentreOf exists_isCentreOf_of_isRational qExpand qExpand_congr qExpand_qExpand ModularPolynomialData jqModC jqNModC jqNModC_one modularFunctionFieldC fibrePoly ssJSet arithFrobC arithFrobC_smul_jq arithFrobC_smul_jqN jqModCd_mem_full mem_ssJSet_of_mem_roots_fibrePoly nonempty_modularPolynomialData modularFunctionFieldC_eq_modularFunctionFieldFullC charLDegeneracyRoof heckeAlphaC heckeBetaC exists_algEquiv_modularFunctionFieldC_swap_and_charLDegeneracyRoof_swap ringHom_ext_of_apply_jGeomGen_eq_of_apply_jNGeomGen_eq hasPrincipalDivisors_modularFunctionFieldC_of_perfectField"
p2m_open "ModularCurve"
namespace FrickeB1

section Fricke

variable (κ : Type*) [Field κ] [IsAlgClosed κ] [DecidableEq κ] (p : ℕ) [Fact p.Prime] [CharP κ p]
  (L : ℕ) [NeZero L]

theorem exists_fricke (hpL : ¬ p ∣ L) :
    ∃ w : ↥(modularFunctionFieldC κ L) ≃ₐ[κ] ↥(modularFunctionFieldC κ L),
      w (jGeomGen κ L) = jNGeomGen κ L ∧ w (jNGeomGen κ L) = jGeomGen κ L := by
  obtain ⟨ℓ, hℓ, hprime⟩ := Nat.exists_infinite_primes (p + 1)
  haveI : Fact ℓ.Prime := ⟨hprime⟩
  have hℓp : ℓ ≠ p := by omega
  obtain ⟨⟨w, h1, h2⟩, -, -⟩ :=
    ModularCurve.exists_algEquiv_modularFunctionFieldC_swap_and_charLDegeneracyRoof_swap κ p L hpL ℓ hℓp
  exact ⟨w, h1, h2⟩

variable {κ p L}

theorem fricke_involutive (w : ↥(modularFunctionFieldC κ L) ≃ₐ[κ] ↥(modularFunctionFieldC κ L))
    (h1 : w (jGeomGen κ L) = jNGeomGen κ L) (h2 : w (jNGeomGen κ L) = jGeomGen κ L) :
    ∀ x, w (w x) = x := by
  have h := ModularCurve.ringHom_ext_of_apply_jGeomGen_eq_of_apply_jNGeomGen_eq κ L
    (w.toAlgHom.toRingHom.comp w.toAlgHom.toRingHom) (RingHom.id _)
    (fun a => by
      show w (w (algebraMap κ _ a)) = algebraMap κ _ a
      rw [AlgEquiv.commutes, AlgEquiv.commutes])
    (by show w (w (jGeomGen κ L)) = jGeomGen κ L; rw [h1, h2])
    (by show w (w (jNGeomGen κ L)) = jNGeomGen κ L; rw [h2, h1])
  intro x
  exact RingHom.congr_fun h x

theorem arithFrobC_mul_ofAlgAut_eq (w : ↥(modularFunctionFieldC κ L) ≃ₐ[κ] ↥(modularFunctionFieldC κ L))
    (h1 : w (jGeomGen κ L) = jNGeomGen κ L) (h2 : w (jNGeomGen κ L) = jGeomGen κ L) :
    arithFrobC p κ L * SemilinearAut.ofAlgAut w = SemilinearAut.ofAlgAut w * arithFrobC p κ L := by
  have fj : arithFrobC p κ L • jGeomGen κ L = jGeomGen κ L := arithFrobC_smul_jq p κ L
  have fjN : arithFrobC p κ L • jNGeomGen κ L = jNGeomGen κ L := arithFrobC_smul_jqN p κ L
  have hring : ∀ x, SemilinearAut.toRingAut (arithFrobC p κ L) (w x) =
      w (SemilinearAut.toRingAut (arithFrobC p κ L) x) := by
    have h := ModularCurve.ringHom_ext_of_apply_jGeomGen_eq_of_apply_jNGeomGen_eq κ L
      ((SemilinearAut.toRingAut (arithFrobC p κ L)).toRingHom.comp w.toAlgHom.toRingHom)
      (w.toAlgHom.toRingHom.comp (SemilinearAut.toRingAut (arithFrobC p κ L)).toRingHom)
      (fun a => by
        show SemilinearAut.toRingAut (arithFrobC p κ L) (w (algebraMap κ _ a)) =
          w (SemilinearAut.toRingAut (arithFrobC p κ L) (algebraMap κ _ a))
        rw [AlgEquiv.commutes, SemilinearAut.commutes, AlgEquiv.commutes])
      (by
        show SemilinearAut.toRingAut (arithFrobC p κ L) (w (jGeomGen κ L)) =
          w (SemilinearAut.toRingAut (arithFrobC p κ L) (jGeomGen κ L))
        rw [h1, ← SemilinearAut.smul_def, ← SemilinearAut.smul_def, fjN, fj, h1])
      (by
        show SemilinearAut.toRingAut (arithFrobC p κ L) (w (jNGeomGen κ L)) =
          w (SemilinearAut.toRingAut (arithFrobC p κ L) (jNGeomGen κ L))
        rw [h2, ← SemilinearAut.smul_def, ← SemilinearAut.smul_def, fj, fjN, h2])
    intro x
    exact RingHom.congr_fun h x
  apply Subtype.ext
  apply Prod.ext
  · apply RingEquiv.ext
    intro x
    exact hring x
  · show SemilinearAut.baseAut (arithFrobC p κ L) * SemilinearAut.baseAut (SemilinearAut.ofAlgAut w) =
      SemilinearAut.baseAut (SemilinearAut.ofAlgAut w) * SemilinearAut.baseAut (arithFrobC p κ L)
    rw [SemilinearAut.baseAut_ofAlgAut, mul_one, one_mul]

end Fricke

end FrickeB1
end ModularCurve

end

open AlgebraicCurve _root_.ModularCurve _root_.P2MW.S_ModularCurve_exists_perm_ssPlaces_correspondence_heckeBetaC_heckeAlphaC_perm_eq_correspondence_heckeAlphaC_heckeBetaC.ModularCurve ModularCurve.FrickeB1 in

theorem solution
    (κ : Type*) [Field κ] [IsAlgClosed κ] [DecidableEq κ] (p : ℕ) [Fact p.Prime] [CharP κ p]
    (L : ℕ) [NeZero L] (hpL : ¬ p ∣ L) :
    ∃ P : Equiv.Perm ↥(ssPlaces p L κ),
      (∀ x : ↥(ssPlaces p L κ), P (P x) = x) ∧
      (∀ y x : ↥(ssPlaces p L κ),
        arithFrobC p κ L • ((P y).1 : Place κ ↥(modularFunctionFieldC κ L)) = (P x).1 ↔
          arithFrobC p κ L • (y.1 : Place κ ↥(modularFunctionFieldC κ L)) = x.1) ∧
      (∀ (ℓ : ℕ) [Fact ℓ.Prime] [NeZero ℓ], ℓ ≠ p →
        ∀ [HasPrincipalDivisors κ ↥(charLDegeneracyRoof κ L ℓ)]
          (hα : (heckeAlphaC κ L ℓ).toRingHom.IsIntegral) (hβ : (heckeBetaC κ L ℓ).toRingHom.IsIntegral)
          (y x : ↥(ssPlaces p L κ)),
          Divisor.correspondence (heckeBetaC κ L ℓ) (heckeAlphaC κ L ℓ) hβ hα (Finsupp.single (P x).1 1) (P y).1 =
            Divisor.correspondence (heckeAlphaC κ L ℓ) (heckeBetaC κ L ℓ) hα hβ (Finsupp.single x.1 1) y.1) := by
  obtain ⟨w, h1, h2⟩ := exists_fricke κ p L hpL
  have hww := fricke_involutive w h1 h2
  set g : SemilinearAut κ ↥(modularFunctionFieldC κ L) := SemilinearAut.ofAlgAut w with hg
  have hw2 : w * w = 1 := AlgEquiv.ext (fun x => by rw [AlgEquiv.mul_apply, hww]; rfl)
  have hg2 : g * g = 1 := by rw [hg, ← map_mul, hw2, map_one]
  have hmem : ∀ W ∈ ssPlaces p L κ, g • W ∈ ssPlaces p L κ :=
    ofAlgAut_smul_mem_ssPlaces_of_swap hpL w h1 h2
  have hgg : ∀ W : Place κ ↥(modularFunctionFieldC κ L), g • (g • W) = W := fun W => by
    rw [smul_smul, hg2, one_smul]
  let P : Equiv.Perm ↥(ssPlaces p L κ) :=
    { toFun := fun x => ⟨g • x.1, hmem x.1 x.2⟩
      invFun := fun x => ⟨g • x.1, hmem x.1 x.2⟩
      left_inv := fun x => Subtype.ext (hgg x.1)
      right_inv := fun x => Subtype.ext (hgg x.1) }
  have hP : ∀ x : ↥(ssPlaces p L κ), ((P x).1 : Place κ ↥(modularFunctionFieldC κ L)) = g • x.1 := fun _ => rfl
  refine ⟨P, fun x => Subtype.ext (hgg x.1), ?_, ?_⟩
  · intro y x
    rw [hP, hP, smul_smul, arithFrobC_mul_ofAlgAut_eq w h1 h2, ← smul_smul]
    exact (MulAction.injective g).eq_iff
  · intro ℓ _ _ hℓp _ hα hβ y x
    haveI : HasPrincipalDivisors κ ↥(modularFunctionFieldC κ L) :=
      ModularCurve.hasPrincipalDivisors_modularFunctionFieldC_of_perfectField κ L
    obtain ⟨-, hroof, -⟩ :=
      ModularCurve.exists_algEquiv_modularFunctionFieldC_swap_and_charLDegeneracyRoof_swap κ p L hpL ℓ hℓp
    obtain ⟨w', hw'α, hw'β⟩ := hroof w h1 h2
    have key :=
      AlgebraicCurve.Divisor.ofAlgAut_smul_correspondence_eq_correspondence_ofAlgAut_smul_of_comp_eq_comp
        (heckeAlphaC κ L ℓ) (heckeBetaC κ L ℓ) hα hβ w' w w
        (AlgHom.ext fun z => hw'β z) (AlgHom.ext fun z => hw'α z) (Finsupp.single x.1 1)
    rw [SemilinearAut.smul_single] at key
    have hev := congrArg (fun D : Divisor κ ↥(modularFunctionFieldC κ L) => D (g • y.1)) key
    try simp only at hev
    rw [SemilinearAut.divisor_smul_apply_smul] at hev
    rw [hP, hP]
    exact hev.symm

#print axioms solution

end S_ModularCurve_exists_perm_ssPlaces_correspondence_heckeBetaC_heckeAlphaC_perm_eq_correspondence_heckeAlphaC_heckeBetaC
end P2MW
export P2MW.S_ModularCurve_exists_perm_ssPlaces_correspondence_heckeBetaC_heckeAlphaC_perm_eq_correspondence_heckeAlphaC_heckeBetaC (solution)
