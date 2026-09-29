-- Prove2me | solution 1 for ModularCurve.JZero.chordFun_evalAt_eq_smul_chordVec
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/01083d20-81b1-5d86-b969-1699523a4d36

import Definitions.Def_ModularCurve_JZeroHeightForm
import Theorems.Thm_ModularCurve_deg_eq_one_modularFunctionFieldBar
import Theorems.Thm_AlgebraicCurve_Place_isRational_iff_deg_eq_one
import Theorems.Thm_AlgebraicCurve_Place_evalAt_mul
import Theorems.Thm_AlgebraicCurve_Place_evalAt_algebraMap
import Theorems.Thm_AlgebraicCurve_Place_evalAt_ne_zero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_JZero_chordFun_evalAt_eq_smul_chordVec
p2m_attr_erase "instance" "AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy ModularCurve.PhiGen.instNeZeroPhiGenCosetA"
p2m_attr_erase "simp" "AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.jqNModC_one ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong"
p2m_attr_erase "simp" "AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen"
p2m_attr_erase "simp" "ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ"
set_option Elab.async false
set_option autoImplicit false

noncomputable section

p2m_open "ModularCurve P2MW.S_ModularCurve_JZero_chordFun_evalAt_eq_smul_chordVec.ModularCurve AlgebraicCurve"

namespace ModularCurve
p2m_export "ModularCurve" "embDivisor IsEmbBasis cuspInftyBar modularFunctionFieldBar JZero deg_eq_one_modularFunctionFieldBar"
p2m_open "ModularCurve"

section Core

variable {F : Type} [Field F] [Algebra (AlgebraicClosure ℚ) F]

private theorem mem_of_adicValuation_le_one (w : Place (AlgebraicClosure ℚ) F) {x : F}
    (hx : w.adicValuation x ≤ 1) : x ∈ w.toValuationSubring := by
  obtain ⟨a, rfl⟩ := IsDiscreteValuationRing.exists_lift_of_le_one hx
  exact a.2

private theorem evalAt_sub_of_mem (w : Place (AlgebraicClosure ℚ) F) (hw : w.IsRational)
    {f g : F} (hf : f ∈ w.toValuationSubring) (hg : g ∈ w.toValuationSubring) :
    w.evalAt (f - g) = w.evalAt f - w.evalAt g := by
  apply w.algebraMap_residueField_injective
  rw [map_sub, w.algebraMap_evalAt hw (sub_mem hf hg), w.algebraMap_evalAt hw hf,
    w.algebraMap_evalAt hw hg,
    show (⟨f - g, sub_mem hf hg⟩ : w.toValuationSubring) = ⟨f, hf⟩ - ⟨g, hg⟩ from rfl,
    map_sub]

private theorem evalAt_smul_of_mem (w : Place (AlgebraicClosure ℚ) F) (hw : w.IsRational)
    {f : F} (hf : f ∈ w.toValuationSubring) (c : AlgebraicClosure ℚ) :
    w.evalAt (c • f) = c * w.evalAt f := by
  rw [Algebra.smul_def, w.evalAt_mul hw (w.algebraMap_mem' c) hf, w.evalAt_algebraMap c]

private theorem evalAt_smul_sub_smul (w : Place (AlgebraicClosure ℚ) F) (hw : w.IsRational)
    {f g P : F} (hf : f ∈ w.toValuationSubring) (hg : g ∈ w.toValuationSubring)
    (hP0 : P ≠ 0) (hPord : w.ord P = 0) (a b : AlgebraicClosure ℚ) :
    w.evalAt (a • f - b • g)
      = w.evalAt P * (a * w.evalAt (f * P⁻¹) - b * w.evalAt (g * P⁻¹)) := by
  have hvalP : w.adicValuation P = 1 := by
    rw [w.adicValuation_eq_exp_neg_ord hP0, hPord, neg_zero, WithZero.exp_zero]
  have hPmem : P ∈ w.toValuationSubring := mem_of_adicValuation_le_one w (le_of_eq hvalP)
  have hdiv : ∀ {x : F}, x ∈ w.toValuationSubring → x * P⁻¹ ∈ w.toValuationSubring := by
    intro x hx
    refine mem_of_adicValuation_le_one w ?_
    rw [map_mul, map_inv₀, hvalP, inv_one, mul_one]
    exact w.adicValuation_le_one_of_mem hx
  have hsmulmem : ∀ (c : AlgebraicClosure ℚ) {x : F}, x ∈ w.toValuationSubring →
      c • x ∈ w.toValuationSubring := by
    intro c x hx
    rw [Algebra.smul_def]
    exact mul_mem (w.algebraMap_mem' c) hx
  have hfac : a • f - b • g = (a • (f * P⁻¹) - b • (g * P⁻¹)) * P := by
    rw [sub_mul, smul_mul_assoc, smul_mul_assoc, inv_mul_cancel_right₀ hP0,
      inv_mul_cancel_right₀ hP0]
  rw [hfac, w.evalAt_mul hw (sub_mem (hsmulmem a (hdiv hf)) (hsmulmem b (hdiv hg))) hPmem,
    evalAt_sub_of_mem w hw (hsmulmem a (hdiv hf)) (hsmulmem b (hdiv hg)),
    evalAt_smul_of_mem w hw (hdiv hf) a, evalAt_smul_of_mem w hw (hdiv hg) b]
  ring

private theorem ord_pivot_eq_zero (w : Place (AlgebraicClosure ℚ) F) {r : ℕ}
    {s : Fin r → F} (hr : 0 < r) (hne : ∀ i, s i ≠ 0) (hreg : ∀ i, 0 ≤ w.ord (s i))
    (h1 : (1 : F) ∈ Submodule.span (AlgebraicClosure ℚ) (Set.range s)) :
    w.ord (s (pivotIndex s w hr)) = 0 := by
  have hex : ∃ i : Fin r, ∀ j : Fin r, w.ord (s i) ≤ w.ord (s j) := by
    obtain ⟨i, -, hi⟩ := Finset.exists_min_image (Finset.univ : Finset (Fin r))
      (fun i => w.ord (s i)) ⟨⟨0, hr⟩, Finset.mem_univ _⟩
    exact ⟨i, fun j => hi j (Finset.mem_univ j)⟩
  have hpiveq : pivotIndex s w hr = Classical.choose hex := by
    unfold pivotIndex
    exact dif_pos hex
  have hpiv : ∀ j : Fin r, w.ord (s (pivotIndex s w hr)) ≤ w.ord (s j) := by
    rw [hpiveq]
    exact Classical.choose_spec hex
  have hvle : w.adicValuation (s (pivotIndex s w hr)) ≤ 1 :=
    w.adicValuation_le_one_iff.mpr (Or.inr (hreg _))
  have hvge : w.adicValuation (1 : F) ≤ w.adicValuation (s (pivotIndex s w hr)) := by
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun _).mp h1
    calc w.adicValuation (1 : F)
        = w.adicValuation (∑ i, c i • s i) := by rw [hc]
      _ ≤ w.adicValuation (s (pivotIndex s w hr)) := by
          apply Valuation.map_sum_le
          intro i _
          calc w.adicValuation (c i • s i) ≤ w.adicValuation (s i) := by
                rw [Algebra.smul_def, map_mul]
                exact mul_le_of_le_one_left' (w.adicValuation_algebraMap_le_one (c i))
            _ ≤ _ := by
                rw [w.adicValuation_eq_exp_neg_ord (hne i),
                  w.adicValuation_eq_exp_neg_ord (hne _), WithZero.exp_le_exp]
                exact neg_le_neg (hpiv i)
  have hval : w.adicValuation (s (pivotIndex s w hr)) = 1 :=
    le_antisymm hvle (le_trans (le_of_eq (map_one w.adicValuation).symm) hvge)
  have hexp := w.adicValuation_eq_exp_neg_ord (hne (pivotIndex s w hr))
  rw [hval] at hexp
  have hlog := congrArg WithZero.log hexp
  rw [WithZero.log_one, WithZero.log_exp] at hlog
  exact neg_eq_zero.mp hlog.symm

end Core

p2m_open_scoped "ModularCurve.JZero" in
private theorem JZero.chordFun_evalAt_eq_smul_chordVec_engine (N : ℕ) [NeZero N] {r : ℕ}
    (s : Fin r → modularFunctionFieldBar N) (hs : IsEmbBasis N s)
    (v w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) (hw : w ≠ cuspInftyBar N) :
    ∃ c : AlgebraicClosure ℚ, c ≠ 0 ∧
      (fun p : Fin r × Fin r => w.evalAt (evalVec s v p.1 • s p.2 - evalVec s v p.2 • s p.1))
        = c • chordVec s v w := by
  have hne : ∀ i, s i ≠ 0 := fun i => hs.1.ne_zero i
  have hDw : embDivisor N w = 0 := by
    unfold embDivisor
    rw [Finsupp.smul_apply, Finsupp.single_eq_of_ne hw, smul_zero]
  have hreg : ∀ i, 0 ≤ w.ord (s i) := by
    intro i
    have hmem : s i ∈ riemannRochSpace (embDivisor N) := by
      rw [← hs.2]
      exact Submodule.subset_span (Set.mem_range_self i)
    rcases mem_riemannRochSpace_iff.mp hmem w with h0 | hle
    · exact absurd h0 (hne i)
    · rwa [hDw, neg_zero] at hle
  have h1mem : (1 : modularFunctionFieldBar N) ∈
      Submodule.span (AlgebraicClosure ℚ) (Set.range s) := by
    classical
    rw [hs.2, mem_riemannRochSpace_iff]
    intro u
    refine Or.inr ?_
    rw [Place.ord_one]
    have hD : 0 ≤ embDivisor N u := by
      unfold embDivisor
      rw [Finsupp.smul_apply, Finsupp.single_apply]
      split_ifs <;> simp
    exact neg_nonpos.mpr hD
  have hr : 0 < r := by
    by_cases hr0 : r = 0
    · exfalso
      subst hr0
      rw [Set.range_eq_empty s, Submodule.span_empty, Submodule.mem_bot] at h1mem
      exact one_ne_zero h1mem
    · exact Nat.pos_of_ne_zero hr0
  have hrat : w.IsRational :=
    w.isRational_iff_deg_eq_one.mpr (deg_eq_one_modularFunctionFieldBar N w)
  have hpivord : w.ord (s (pivotIndex s w hr)) = 0 :=
    ord_pivot_eq_zero w hr hne hreg h1mem
  have hsmem : ∀ i, s i ∈ w.toValuationSubring := fun i =>
    mem_of_adicValuation_le_one w (w.adicValuation_le_one_iff.mpr (Or.inr (hreg i)))
  have hvecw : ∀ i : Fin r, evalVec s w i
      = w.evalAt (s i * (s (pivotIndex s w hr))⁻¹) := by
    intro i
    simp only [evalVec]
    exact dif_pos hr
  refine ⟨w.evalAt (s (pivotIndex s w hr)),
    w.evalAt_ne_zero hrat (hne _) hpivord, ?_⟩
  funext p
  show w.evalAt (evalVec s v p.1 • s p.2 - evalVec s v p.2 • s p.1)
      = w.evalAt (s (pivotIndex s w hr)) * chordVec s v w p
  simp only [chordVec]
  rw [hvecw p.1, hvecw p.2]
  exact evalAt_smul_sub_smul w hrat (hsmem p.2) (hsmem p.1)
    (hne (pivotIndex s w hr)) hpivord (evalVec s v p.1) (evalVec s v p.2)

end ModularCurve

theorem solution (N : ℕ) [NeZero N] {r : ℕ}
    (s : Fin r → modularFunctionFieldBar N) (hs : IsEmbBasis N s)
    (v w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) (hw : w ≠ cuspInftyBar N) :
    ∃ c : AlgebraicClosure ℚ, c ≠ 0 ∧
      (fun p : Fin r × Fin r => w.evalAt (evalVec s v p.1 • s p.2 - evalVec s v p.2 • s p.1))
        = c • chordVec s v w :=
  ModularCurve.JZero.chordFun_evalAt_eq_smul_chordVec_engine N s hs v w hw

end

end S_ModularCurve_JZero_chordFun_evalAt_eq_smul_chordVec
end P2MW
export P2MW.S_ModularCurve_JZero_chordFun_evalAt_eq_smul_chordVec (solution)
