-- Prove2me | solution 1 for ModularCurve.ModularPolynomialData.separable_map_eval2_of_not_isIntegral_of_isAlgClosed
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/9e57416d-bb4f-55d7-9cac-9a7f9c36ab0f

import Definitions.Def_ModularCurve_X0
import Definitions.Def_WeierstrassCurve_Velu
import Definitions.Def_WeierstrassCurve_OddOrderSummingSet
import Definitions.Def_Isogeny_ConditionalCurrency
import Definitions.Def_WeierstrassCurve_GenusOnePlaceGateCentred
import Mathlib
import Theorems.Thm_ModularCurve_ModularPolynomialData_separable_map_eval2_of_not_isIntegral_of_isAlgClosed_two
import Theorems.Thm_WeierstrassCurve_Affine_exists_genusOnePlaceGate_isCentred_abelTheorem
import Theorems.Thm_WeierstrassCurve_Affine_forall_normFormulaAlong_of_isAlgClosed_of_charZero
import Theorems.Thm_WeierstrassCurve_Affine_IsogenyEndDatum_exists_forall_pointEnd_eq_zsmul_of_not_isIntegral_j
import Theorems.Thm_WeierstrassCurve_zmultiples_eq_of_veluQuotient_j_eq_of_forall_pointEnd_eq_zsmul
import Theorems.Thm_WeierstrassCurve_veluQuotient_oddOrderSummingSet_discriminant_ne_zero
import Theorems.Thm_WeierstrassCurve_natCard_addSubgroup_isAddCyclic_card_eq_dedekindPsi_of_isAlgClosed
import Theorems.Thm_ModularCurve_ModularPolynomialData_isRoot_map_j_veluQuotient_j_of_addOrderOf_eq_of_isAlgClosed
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_ModularPolynomialData_separable_map_eval2_of_not_isIntegral_of_isAlgClosed
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid"
p2m_attr_erase "simp" "ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single ModularCurve.jqNModC_one ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL WeierstrassCurve.veluX_empty WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm"
p2m_attr_erase "simp" "AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec"
p2m_attr_erase "simp" "WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero WeierstrassCurve.veluY_empty ModularCurve.ProjectiveLine.map_mk"

p2m_open "Polynomial P2MW.S_ModularCurve_ModularPolynomialData_separable_map_eval2_of_not_isIntegral_of_isAlgClosed.Polynomial ModularCurve~dedekindPsi_prime P2MW.S_ModularCurve_ModularPolynomialData_separable_map_eval2_of_not_isIntegral_of_isAlgClosed.ModularCurve WeierstrassCurve WeierstrassCurve.Affine AlgebraicCurve"

set_option maxHeartbeats 9600000
set_option autoImplicit false

section Helpers

namespace ModularCurve p2m_export "ModularCurve" "dedekindPsi ModularPolynomialData ModularPolynomialData.separable_map_eval2_of_not_isIntegral_of_isAlgClosed_two ModularPolynomialData.isRoot_map_j_veluQuotient_j_of_addOrderOf_eq_of_isAlgClosed" end ModularCurve
p2m_open_scoped "ModularCurve" in
private lemma ModularCurve.dedekindPsi_prime {p : ℕ} (hp : p.Prime) :
    dedekindPsi p = p + 1 := by
  have h1 : p.divisors.filter Squarefree = {1, p} := by
    ext d
    simp only [Finset.mem_filter, Nat.mem_divisors, Finset.mem_insert, Finset.mem_singleton]
    refine ⟨fun ⟨⟨hd, _⟩, _⟩ ↦ hp.eq_one_or_self_of_dvd d hd, fun h ↦ ?_⟩
    rcases h with rfl | rfl
    · exact ⟨⟨one_dvd _, hp.ne_zero⟩, squarefree_one⟩
    · exact ⟨⟨dvd_refl _, hp.ne_zero⟩, hp.squarefree⟩
  have hne : (1 : ℕ) ∉ ({p} : Finset ℕ) := by
    simp only [Finset.mem_singleton]; exact hp.one_lt.ne
  unfold dedekindPsi
  rw [h1, Finset.sum_insert hne, Finset.sum_singleton,
      Nat.div_one, Nat.div_self hp.pos, add_comm]

namespace Polynomial p2m_export "Polynomial" "C X leadingCoeff Splits map mem_roots Monic roots natDegree_eq_card_roots Separable natDegree natDegree_map ext IsRoot separable_prod_X_sub_C_iff' eval₂RingHom" namespace Monic p2m_export "Polynomial.Monic" "leadingCoeff natDegree_map ne_zero map" end Polynomial.Monic
namespace Polynomial.Monic
p2m_open_scoped "Polynomial Polynomial.Monic" in
private lemma _root_.Polynomial.Monic.separable_of_splits_of_nodup_roots
    {F : Type*} [Field F] {P : F[X]} (hm : P.Monic)
    (hsp : P.Splits) (hnd : P.roots.Nodup) : P.Separable := by
  classical
  have heq : P = (P.roots.map (fun r ↦ X - C r)).prod := by
    have h := hsp.eq_prod_roots
    rwa [hm.leadingCoeff, map_one, one_mul] at h
  have hval : P.roots.toFinset.1 = P.roots := by
    rw [Multiset.toFinset_val, Multiset.Nodup.dedup hnd]
  rw [heq, ← hval]
  show (Multiset.map (fun r ↦ X - C r) P.roots.toFinset.1).prod.Separable
  rw [show (Multiset.map (fun r ↦ X - C r) P.roots.toFinset.1).prod
        = ∏ r ∈ P.roots.toFinset, (X - C r) from (Finset.prod_map_val _ _).symm]
  exact separable_prod_X_sub_C_iff'.mpr (fun _ _ _ _ h ↦ h)

end Polynomial.Monic
p2m_export "" "Polynomial.Monic.separable_of_splits_of_nodup_roots"
namespace Multiset p2m_export "Multiset" "toFinset Nodup.dedup card mem_toFinset sum_singleton toFinset_card_le filter mem_filter map choose eq_of_le_of_card_le dedup toFinset_val mem_singleton dedup_le prod nodup_dedup Nodup ext" end Multiset
p2m_open_scoped "Multiset" in
private lemma Multiset.nodup_of_toFinset_card_eq_card {α : Type*} [DecidableEq α] {s : Multiset α}
    (h : s.toFinset.card = s.card) : s.Nodup := by
  have hc : s.dedup.card = s.toFinset.card := by
    show s.dedup.card = s.toFinset.val.card; rw [Multiset.toFinset_val]
  have heq : s.dedup = s :=
    Multiset.eq_of_le_of_card_le s.dedup_le (by rw [hc, h])
  exact heq ▸ s.nodup_dedup

end Helpers

theorem solution
    {F : Type*} [Field F] [CharZero F] [IsAlgClosed F] (p : ℕ) [Fact p.Prime]
    (data : ModularPolynomialData p) (jv : F) (hjv : ¬ _root_.IsIntegral ℤ jv) :
    (data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom F) jv)).Separable := by
  classical
  have hp : p.Prime := Fact.out
  haveI : DecidableEq F := Classical.decEq F
  set P : F[X] := data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom F) jv) with hPdef
  have hmonic : P.Monic := data.monic.map _
  have hsplits : P.Splits := IsAlgClosed.splits P
  have hdeg : P.natDegree = dedekindPsi p := by
    rw [hPdef, data.monic.natDegree_map, data.natDegree_eq]
  rcases hp.eq_two_or_odd' with hp2 | hpodd
  · subst hp2
    exact ModularCurve.ModularPolynomialData.separable_map_eval2_of_not_isIntegral_of_isAlgClosed_two
      data jv hjv
  · obtain ⟨n, hn⟩ := hpodd

    let W : WeierstrassCurve F := WeierstrassCurve.ofJ jv
    haveI : W.IsElliptic := WeierstrassCurve.instIsEllipticOfJ jv
    have hjW : W.j = jv := WeierstrassCurve.ofJ_j jv

    obtain ⟨g, hcent, habel⟩ :=
      WeierstrassCurve.Affine.exists_genusOnePlaceGate_isCentred_abelTheorem (F := F) W.toAffine
    letI : GenusOnePlaceGate W.toAffine := g
    haveI : GenusOnePlaceGate.IsCentred W.toAffine := hcent
    haveI : AbelTheorem W.toAffine := habel

    have hNs : ∀ D : IsogenyEndDatum W.toAffine, NormFormulaAlong F D.ι D.hfin :=
      WeierstrassCurve.Affine.forall_normFormulaAlong_of_isAlgClosed_of_charZero W.toAffine
    have hjW' : ¬ _root_.IsIntegral ℤ W.j := hjW ▸ hjv
    have hEnd : ∀ D : IsogenyEndDatum W.toAffine, ∃ m : ℤ, ∀ Q : W.toAffine.Point,
        D.pointEnd (hNs D) Q = m • Q := fun D ↦
      WeierstrassCurve.Affine.IsogenyEndDatum.exists_forall_pointEnd_eq_zsmul_of_not_isIntegral_j
        W hNs hjW' D
    have h2F : (2 : F) ≠ 0 := two_ne_zero

    subst hn

    have hΔ : ∀ Q : W.toAffine.Point, addOrderOf Q = 2 * n + 1 →
        (W.veluQuotient (W.oddOrderSummingSet Q n)).Δ ≠ 0 := fun Q hQ ↦
      WeierstrassCurve.veluQuotient_oddOrderSummingSet_discriminant_ne_zero h2F W n Q hQ
    let jvq : {Q : W.toAffine.Point // addOrderOf Q = 2 * n + 1} → F := fun ⟨Q, hQ⟩ ↦
      haveI : (W.veluQuotient (W.oddOrderSummingSet Q n)).IsElliptic :=
        ⟨isUnit_iff_ne_zero.mpr (hΔ Q hQ)⟩
      (W.veluQuotient (W.oddOrderSummingSet Q n)).j
    have hroot : ∀ Q : {Q // addOrderOf Q = 2 * n + 1}, P.IsRoot (jvq Q) := fun ⟨Q, hQ⟩ ↦ by
      have h := ModularCurve.ModularPolynomialData.isRoot_map_j_veluQuotient_j_of_addOrderOf_eq_of_isAlgClosed
        W n Q hQ (hΔ Q hQ) data
      simpa only [hPdef, hjW] using h
    have hinj : ∀ Q Q' : {Q // addOrderOf Q = 2 * n + 1},
        jvq Q = jvq Q' → AddSubgroup.zmultiples Q.1 = AddSubgroup.zmultiples Q'.1 := by
      rintro ⟨Q, hQ⟩ ⟨Q', hQ'⟩ hj
      exact WeierstrassCurve.zmultiples_eq_of_veluQuotient_j_eq_of_forall_pointEnd_eq_zsmul
        W hNs hEnd n Q Q' hQ hQ' (hΔ Q hQ) (hΔ Q' hQ') hj

    set 𝒞 := {H : AddSubgroup W.toAffine.Point // IsAddCyclic H ∧ Nat.card H = 2 * n + 1}

    have hgen : ∀ H : 𝒞, ∃ Q : W.toAffine.Point,
        addOrderOf Q = 2 * n + 1 ∧ AddSubgroup.zmultiples Q = H.1 := by
      rintro ⟨H, hcyc, hcard⟩
      obtain ⟨g0, hg0⟩ := hcyc.exists_generator
      refine ⟨(g0 : W.toAffine.Point), ?_, ?_⟩
      ·
        have h1 : addOrderOf g0 = Nat.card H := addOrderOf_eq_card_of_forall_mem_zmultiples hg0
        have h2 : addOrderOf (g0 : W.toAffine.Point) = addOrderOf g0 :=
          AddSubgroup.addOrderOf_coe g0
        rw [h2, h1, hcard]
      ·
        refine le_antisymm (AddSubgroup.zmultiples_le_of_mem g0.2) ?_
        intro x hx
        obtain ⟨k, hk⟩ := hg0 ⟨x, hx⟩
        exact ⟨k, by simpa using congrArg Subtype.val hk⟩
    choose genQ hgenOrd hgenEq using hgen
    let φH : 𝒞 → F := fun H ↦ jvq ⟨genQ H, hgenOrd H⟩
    have hφHroot : ∀ H, φH H ∈ P.roots.toFinset := fun H ↦
      Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hmonic.ne_zero).mpr (hroot ⟨genQ H, hgenOrd H⟩))
    have hφHinj : Function.Injective φH := fun H H' heq ↦ by
      have := hinj ⟨genQ H, hgenOrd H⟩ ⟨genQ H', hgenOrd H'⟩ heq
      exact Subtype.ext ((hgenEq H).symm.trans (this.trans (hgenEq H')))

    have hcount : Nat.card 𝒞 = dedekindPsi (2 * n + 1) := by
      have h := WeierstrassCurve.natCard_addSubgroup_isAddCyclic_card_eq_dedekindPsi_of_isAlgClosed
        (F := F) (K := F) W (n := 2 * n + 1) (by exact_mod_cast hp.ne_zero)

      convert h using 2
      all_goals first | rfl | simp [𝒞]

    have hψpos : 0 < dedekindPsi (2 * n + 1) := by
      rw [dedekindPsi_prime hp]; omega
    haveI : Finite 𝒞 := Nat.finite_of_card_ne_zero (hcount ▸ hψpos.ne')
    haveI : Fintype 𝒞 := Fintype.ofFinite 𝒞

    have hψle : dedekindPsi (2 * n + 1) ≤ P.roots.toFinset.card := by
      calc dedekindPsi (2 * n + 1)
          = Nat.card 𝒞 := hcount.symm
        _ = Fintype.card 𝒞 := Nat.card_eq_fintype_card
        _ ≤ P.roots.toFinset.card :=
            Finset.card_le_card_of_injOn φH (fun H _ ↦ hφHroot H) hφHinj.injOn
              |>.trans_eq' Finset.card_univ.symm

    have hcardRoots : P.roots.card = dedekindPsi (2 * n + 1) := by
      rw [← hdeg, hsplits.natDegree_eq_card_roots]

    have hnd : P.roots.Nodup := by
      apply Multiset.nodup_of_toFinset_card_eq_card
      have h1 : P.roots.toFinset.card ≤ P.roots.card := P.roots.toFinset_card_le
      omega
    exact hmonic.separable_of_splits_of_nodup_roots hsplits hnd

end S_ModularCurve_ModularPolynomialData_separable_map_eval2_of_not_isIntegral_of_isAlgClosed
end P2MW
export P2MW.S_ModularCurve_ModularPolynomialData_separable_map_eval2_of_not_isIntegral_of_isAlgClosed (solution)
