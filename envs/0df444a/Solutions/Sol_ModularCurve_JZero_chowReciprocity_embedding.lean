-- Prove2me | solution 1 for ModularCurve.JZero.chowReciprocity_embedding
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/60f14005-35e0-5cec-8ef0-5420d03252f7

import Definitions.Def_AlgebraicCurve_ChordalProximity
import Definitions.Def_AlgebraicCurve_PlaceEvaluationAlgebra
import Definitions.Def_ModularCurve_JZeroHeightForm
import Definitions.Def_AlgebraicCurve_CycleChowForm
import Theorems.Thm_AlgebraicCurve_weilReciprocity
import Theorems.Thm_AlgebraicCurve_Place_isRational_of_isAlgClosed
import Theorems.Thm_ModularCurve_transcendental_coeffEmb_jq
import Theorems.Thm_ModularCurve_exists_rational_presentation_modularFunctionFieldBar
import Theorems.Thm_ModularCurve_hasPrincipalDivisors_modularFunctionFieldBar_unconditional
import Theorems.Thm_ModularCurve_exists_adapted_family_modularFunctionFieldBar
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_JZero_chowReciprocity_embedding
p2m_attr_erase "instance" "AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.PhiGen.instNeZeroPhiGenCosetA"
p2m_attr_erase "simp" "AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X"
p2m_attr_erase "simp" "ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.coe_cuspidalDivisor₀ ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ"
p2m_attr_erase "simp" "ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar"

set_option autoImplicit false

noncomputable section

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "secVal pivotIndex evalVec Place Divisor Place.IsRational Divisor.evalFun WeilReciprocity riemannRochSpace mem_riemannRochSpace_iff Divisor.evalFun_ne_zero_of_forall_ne_zero Divisor.evalFun_add_of_forall_ne_zero Divisor.support_smul_subset Divisor.evalFun_zsmul_divisor linSec chowForm secProd ChowReciprocity eval_chowForm weilReciprocity Place.isRational_of_isAlgClosed"
p2m_open "AlgebraicCurve"

namespace Place
p2m_export "AlgebraicCurve.Place" "ord ord_one ord_mul ord_inv ord_zpow algebraMap_mem' toValuationSubring IsRational algebraMap_residueField_injective evalAt algebraMap_evalAt evalAt_one evalAt_ne_zero_of_ord_eq_zero evalAt_mul_of_mem evalAt_algebraMap_eq mem_toValuationSubring_of_ord_nonneg_alt isRational_of_isAlgClosed"
p2m_open "AlgebraicCurve.Place"

variable {K F : Type} [Field K] [Field F] [Algebra K F] (v : Place K F)

private theorem _root_.AlgebraicCurve.Place.evalAt_zero' : v.evalAt (0 : F) = 0 := by
  simpa using v.evalAt_algebraMap_eq (0 : K)

p2m_export "AlgebraicCurve.Place" "evalAt_zero'"

private theorem _root_.AlgebraicCurve.Place.evalAt_add_of_mem (hv : v.IsRational) {f g : F} (hf : f ∈ v.toValuationSubring)
    (hg : g ∈ v.toValuationSubring) : v.evalAt (f + g) = v.evalAt f + v.evalAt g := by
  apply v.algebraMap_residueField_injective
  rw [map_add, v.algebraMap_evalAt hv (add_mem hf hg), v.algebraMap_evalAt hv hf, v.algebraMap_evalAt hv hg,
    ← map_add]
  rfl

p2m_export "AlgebraicCurve.Place" "evalAt_add_of_mem"

private theorem _root_.AlgebraicCurve.Place.evalAt_smul_of_mem (hv : v.IsRational) (a : K) {f : F} (hf : f ∈ v.toValuationSubring) :
    v.evalAt (a • f) = a * v.evalAt f := by
  rw [Algebra.smul_def, v.evalAt_mul_of_mem hv (v.algebraMap_mem' a) hf, v.evalAt_algebraMap_eq]

p2m_export "AlgebraicCurve.Place" "evalAt_smul_of_mem"

private theorem _root_.AlgebraicCurve.Place.evalAt_sum_of_mem (hv : v.IsRational) {ι : Type} (t : Finset ι) (f : ι → F)
    (hf : ∀ i ∈ t, f i ∈ v.toValuationSubring) : v.evalAt (∑ i ∈ t, f i) = ∑ i ∈ t, v.evalAt (f i) := by
  classical
  induction t using Finset.induction_on with
  | empty => simp [v.evalAt_zero']
  | insert i t hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi,
      v.evalAt_add_of_mem hv (hf i (Finset.mem_insert_self i t))
        (Subring.sum_mem _ fun j hj => hf j (Finset.mem_insert_of_mem hj)),
      ih fun j hj => hf j (Finset.mem_insert_of_mem hj)]

p2m_export "AlgebraicCurve.Place" "evalAt_sum_of_mem"

theorem evalAt_inv_of_ord_eq_zero (hv : v.IsRational) {f : F} (hf : f ≠ 0) (h : v.ord f = 0) :
    v.evalAt f⁻¹ = (v.evalAt f)⁻¹ := by
  have hmem : f ∈ v.toValuationSubring := v.mem_toValuationSubring_of_ord_nonneg_alt hf h.ge
  have hmem' : f⁻¹ ∈ v.toValuationSubring :=
    v.mem_toValuationSubring_of_ord_nonneg_alt (inv_ne_zero hf) (by rw [v.ord_inv, h, neg_zero])
  have hne : v.evalAt f ≠ 0 := v.evalAt_ne_zero_of_ord_eq_zero hv hf h
  have hmul : v.evalAt f * v.evalAt f⁻¹ = 1 := by
    rw [← v.evalAt_mul_of_mem hv hmem hmem', mul_inv_cancel₀ hf, v.evalAt_one]
  exact (eq_inv_of_mul_eq_one_right hmul)

end Place

section Pivot

variable {F : Type} [Field F] [Algebra (AlgebraicClosure ℚ) F] {r : ℕ}

theorem ord_pivotIndex_le (s : Fin r → F) (v : Place (AlgebraicClosure ℚ) F) (hr : 0 < r) (j : Fin r) :
    v.ord (s (pivotIndex s v hr)) ≤ v.ord (s j) := by
  have h : ∃ i : Fin r, ∀ j : Fin r, v.ord (s i) ≤ v.ord (s j) := by
    obtain ⟨i, -, hi⟩ := Finset.exists_min_image Finset.univ (fun i => v.ord (s i)) ⟨⟨0, hr⟩, Finset.mem_univ _⟩
    exact ⟨i, fun j => hi j (Finset.mem_univ j)⟩
  rw [pivotIndex, dif_pos h]
  exact Classical.choose_spec h j

theorem div_pivot_mem (s : Fin r → F) (hs : ∀ i, s i ≠ 0) (v : Place (AlgebraicClosure ℚ) F)
    (hr : 0 < r) (i : Fin r) : s i * (s (pivotIndex s v hr))⁻¹ ∈ v.toValuationSubring := by
  refine v.mem_toValuationSubring_of_ord_nonneg_alt (mul_ne_zero (hs i) (inv_ne_zero (hs _))) ?_
  rw [v.ord_mul (hs i) (inv_ne_zero (hs _)), v.ord_inv]
  linarith [ord_pivotIndex_le s v hr i]

theorem evalAt_linSec_div_pivot (s : Fin r → F) (hs : ∀ i, s i ≠ 0) (v : Place (AlgebraicClosure ℚ) F)
    (hv : v.IsRational) (hr : 0 < r) (a : Fin r → AlgebraicClosure ℚ) :
    v.evalAt (linSec s a * (s (pivotIndex s v hr))⁻¹) = ∑ i, evalVec s v i * a i := by
  have hmem := div_pivot_mem s hs v hr
  rw [linSec, Finset.sum_mul,
    v.evalAt_sum_of_mem hv Finset.univ _ fun i _ => ?_]
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_mul_assoc, v.evalAt_smul_of_mem hv (a i) (hmem i), evalVec, dif_pos hr, mul_comm]
  · rw [smul_mul_assoc, Algebra.smul_def]
    exact mul_mem (v.algebraMap_mem' (a i)) (hmem i)

theorem prod_evalAt_linSec_div_pivot (s : Fin r → F) (hs : ∀ i, s i ≠ 0) (hr : 0 < r)
    (Z : Divisor (AlgebraicClosure ℚ) F) (hZ : ∀ w, 0 ≤ Z w) (hrat : ∀ w ∈ Z.support, Place.IsRational w)
    (a : Fin r → AlgebraicClosure ℚ) :
    (Z.prod fun w n => w.evalAt (linSec s a * (s (pivotIndex s w hr))⁻¹) ^ n)
      = MvPolynomial.eval a (chowForm s Z) := by
  rw [eval_chowForm, Finsupp.prod, Finsupp.prod]
  refine Finset.prod_congr rfl fun w hw => ?_
  rw [evalAt_linSec_div_pivot s hs w (hrat w hw) hr a]
  conv_lhs => rw [← Int.toNat_of_nonneg (hZ w), zpow_natCast]

theorem prod_evalAt_div_pivot_pow (s : Fin r → F) (hr : 0 < r) (k : ℕ) (u : F)
    (Z : Divisor (AlgebraicClosure ℚ) F) (hZ : ∀ w, 0 ≤ Z w) :
    (Z.prod fun w n => w.evalAt (u * (s (pivotIndex s w hr))⁻¹ ^ k) ^ n) = secProd s k u Z := by
  rw [secProd, Finsupp.prod, Finsupp.prod]
  refine Finset.prod_congr rfl fun w _ => ?_
  rw [secVal, dif_pos hr]
  conv_lhs => rw [← Int.toNat_of_nonneg (hZ w), zpow_natCast]

end Pivot

end AlgebraicCurve

end

noncomputable section

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "secVal pivotIndex evalVec Place Divisor Place.IsRational Divisor.evalFun WeilReciprocity riemannRochSpace mem_riemannRochSpace_iff Divisor.evalFun_ne_zero_of_forall_ne_zero Divisor.evalFun_add_of_forall_ne_zero Divisor.support_smul_subset Divisor.evalFun_zsmul_divisor linSec chowForm secProd ChowReciprocity eval_chowForm weilReciprocity Place.isRational_of_isAlgClosed"
p2m_open "AlgebraicCurve"

namespace Place p2m_export "AlgebraicCurve.Place" "ord ord_one ord_mul ord_inv ord_zpow algebraMap_mem' toValuationSubring IsRational algebraMap_residueField_injective evalAt algebraMap_evalAt evalAt_one evalAt_ne_zero_of_ord_eq_zero evalAt_mul_of_mem evalAt_algebraMap_eq mem_toValuationSubring_of_ord_nonneg_alt isRational_of_isAlgClosed" end Place
namespace Place
p2m_open_scoped "AlgebraicCurve.Place" in

private theorem _root_.AlgebraicCurve.Place.evalAt_pow_of_mem {K F : Type} [Field K] [Field F] [Algebra K F] (v : Place K F)
    (hv : v.IsRational) {f : F} (hf : f ∈ v.toValuationSubring) (n : ℕ) :
    v.evalAt (f ^ n) = v.evalAt f ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, v.evalAt_one]
  | succ n ih => rw [pow_succ, v.evalAt_mul_of_mem hv (pow_mem hf n) hf, ih, pow_succ]

end Place
p2m_export "AlgebraicCurve" "Place.evalAt_pow_of_mem"

theorem zpow_pow_comm' {K : Type} [Field K] (x : K) (n : ℤ) (k : ℕ) : (x ^ n) ^ k = (x ^ k) ^ n := by
  rw [← zpow_natCast (x ^ n) k, ← zpow_mul, ← zpow_natCast x k, ← zpow_mul, mul_comm]

section Assembly

variable {F : Type} [Field F] [Algebra (AlgebraicClosure ℚ) F] {r : ℕ}

theorem linSec_div_pivot_mem (s : Fin r → F) (hs : ∀ i, s i ≠ 0) (v : Place (AlgebraicClosure ℚ) F)
    (hr : 0 < r) (x : Fin r → AlgebraicClosure ℚ) :
    linSec s x * (s (pivotIndex s v hr))⁻¹ ∈ v.toValuationSubring := by
  rw [linSec, Finset.sum_mul]
  refine Subring.sum_mem _ fun i _ => ?_
  rw [smul_mul_assoc, Algebra.smul_def]
  exact mul_mem (v.algebraMap_mem' (x i)) (div_pivot_mem s hs v hr i)

theorem linSec_mem_riemannRochSpace (s : Fin r → F) (E : Divisor (AlgebraicClosure ℚ) F)
    (hsL : ∀ i, s i ∈ riemannRochSpace E) (x : Fin r → AlgebraicClosure ℚ) :
    linSec s x ∈ riemannRochSpace E :=
  Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ (x i) (hsL i)

theorem chowReciprocity_of_weilReciprocity (hWR : WeilReciprocity (AlgebraicClosure ℚ) F)
    (hrat : ∀ w : Place (AlgebraicClosure ℚ) F, w.IsRational) (s : Fin r → F) (hs0 : ∀ i, s i ≠ 0)
    (E : Divisor (AlgebraicClosure ℚ) F) (hsL : ∀ i, s i ∈ riemannRochSpace E) (k : ℕ) (u : F) (hu : u ≠ 0)
    (B : Divisor (AlgebraicClosure ℚ) F) (hB : ∀ w, B w = w.ord u + k * E w) (hB0 : ∀ w, 0 ≤ B w) :
    ChowReciprocity s E k u B := by
  intro a b c Za Zb Zc ha hb hc hZa hZb hZc hGP
  rcases Nat.eq_zero_or_pos r with hr0 | hr
  · subst hr0
    exact (ha (by simp [linSec])).elim

  have heff : ∀ (x : Fin r → AlgebraicClosure ℚ) (Z : Divisor (AlgebraicClosure ℚ) F), linSec s x ≠ 0 →
      (∀ w, Z w = w.ord (linSec s x) + E w) → ∀ w, 0 ≤ Z w := by
    intro x Z hx hZ w
    rcases mem_riemannRochSpace_iff.mp (linSec_mem_riemannRochSpace s E hsL x) w with h0 | hle
    · exact (hx h0).elim
    · rw [hZ w]
      linarith
  have hZa0 := heff a Za ha hZa
  have hZb0 := heff b Zb hb hZb

  set f : F := linSec s a * (linSec s b)⁻¹ with hf_def
  set g : F := u * (linSec s c)⁻¹ ^ k with hg_def
  have hf0 : f ≠ 0 := mul_ne_zero ha (inv_ne_zero hb)
  have hg0 : g ≠ 0 := mul_ne_zero hu (pow_ne_zero _ (inv_ne_zero hc))
  have hordf : ∀ v : Place (AlgebraicClosure ℚ) F, v.ord f = Za v - Zb v := by
    intro v
    rw [hf_def, v.ord_mul ha (inv_ne_zero hb), v.ord_inv, hZa v, hZb v]
    ring
  have hordg : ∀ v : Place (AlgebraicClosure ℚ) F, v.ord g = B v - k * Zc v := by
    intro v
    rw [hg_def, v.ord_mul hu (pow_ne_zero _ (inv_ne_zero hc)), ← zpow_natCast, v.ord_zpow, v.ord_inv, hB v,
      hZc v]
    ring

  have hB_gp : ∀ v ∈ B.support, Za v = 0 ∧ Zb v = 0 := fun v hv =>
    (hGP v).resolve_right fun h => (Finsupp.mem_support_iff.mp hv) h.1
  have hZc_gp : ∀ v ∈ Zc.support, Za v = 0 ∧ Zb v = 0 := fun v hv =>
    (hGP v).resolve_right fun h => (Finsupp.mem_support_iff.mp hv) h.2
  have hZa_gp : ∀ v ∈ Za.support, B v = 0 ∧ Zc v = 0 := fun v hv =>
    (hGP v).resolve_left fun h => (Finsupp.mem_support_iff.mp hv) h.1
  have hZb_gp : ∀ v ∈ Zb.support, B v = 0 ∧ Zc v = 0 := fun v hv =>
    (hGP v).resolve_left fun h => (Finsupp.mem_support_iff.mp hv) h.2
  have hfne : ∀ v : Place (AlgebraicClosure ℚ) F, Za v = 0 → Zb v = 0 → v.evalAt f ≠ 0 := fun v h1 h2 =>
    v.evalAt_ne_zero_of_ord_eq_zero (hrat v) hf0 (by rw [hordf, h1, h2, sub_zero])
  have hgne : ∀ v : Place (AlgebraicClosure ℚ) F, B v = 0 → Zc v = 0 → v.evalAt g ≠ 0 := fun v h1 h2 =>
    v.evalAt_ne_zero_of_ord_eq_zero (hrat v) hg0 (by rw [hordg, h1, h2, mul_zero, sub_zero])

  have hW := hWR f g (Za + (-1 : ℤ) • Zb) (B + (-(k : ℤ)) • Zc) hf0 hg0
    (fun v => by rw [Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul, hordf]; ring)
    (fun v => by rw [Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul, hordg]; ring)
    (fun v => by
      rcases hGP v with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · left
        rw [hordf, h1, h2, sub_zero]
      · right
        rw [hordg, h1, h2, mul_zero, sub_zero])
    (fun v _ => hrat v) (fun v _ => hrat v)
  rw [Divisor.evalFun_add_of_forall_ne_zero f (fun v hv => hfne v (hB_gp v hv).1 (hB_gp v hv).2)
        (fun v hv => hfne v (hZc_gp v (Divisor.support_smul_subset _ _ hv)).1
          (hZc_gp v (Divisor.support_smul_subset _ _ hv)).2),
      Divisor.evalFun_zsmul_divisor,
      Divisor.evalFun_add_of_forall_ne_zero g (fun v hv => hgne v (hZa_gp v hv).1 (hZa_gp v hv).2)
        (fun v hv => hgne v (hZb_gp v (Divisor.support_smul_subset _ _ hv)).1
          (hZb_gp v (Divisor.support_smul_subset _ _ hv)).2),
      Divisor.evalFun_zsmul_divisor] at hW

  have e1 : ∀ w : Place (AlgebraicClosure ℚ) F,
      f * (linSec s b * (s (pivotIndex s w hr))⁻¹) = linSec s a * (s (pivotIndex s w hr))⁻¹ := fun w => by
    rw [hf_def, mul_assoc, ← mul_assoc (linSec s b)⁻¹, inv_mul_cancel₀ hb, one_mul]
  have e2 : ∀ w : Place (AlgebraicClosure ℚ) F,
      g * (linSec s c * (s (pivotIndex s w hr))⁻¹) ^ k = u * (s (pivotIndex s w hr))⁻¹ ^ k := fun w => by
    rw [hg_def, mul_assoc, ← mul_pow, inv_mul_cancel_left₀ hc]
  have key_f : ∀ Z : Divisor (AlgebraicClosure ℚ) F, (∀ v ∈ Z.support, Za v = 0 ∧ Zb v = 0) →
      Divisor.evalFun f Z * (Z.prod fun w n => w.evalAt (linSec s b * (s (pivotIndex s w hr))⁻¹) ^ n)
        = Z.prod fun w n => w.evalAt (linSec s a * (s (pivotIndex s w hr))⁻¹) ^ n := by
    intro Z hZ
    rw [Divisor.evalFun, ← Finsupp.prod_mul]
    refine Finsupp.prod_congr fun w hw => ?_
    have hfmem : f ∈ w.toValuationSubring :=
      w.mem_toValuationSubring_of_ord_nonneg_alt hf0 (by rw [hordf, (hZ w hw).1, (hZ w hw).2, sub_zero])
    rw [← mul_zpow, ← w.evalAt_mul_of_mem (hrat w) hfmem (linSec_div_pivot_mem s hs0 w hr b), e1 w]
  have key_g : ∀ Z : Divisor (AlgebraicClosure ℚ) F, (∀ v ∈ Z.support, B v = 0 ∧ Zc v = 0) →
      Divisor.evalFun g Z
          * (Z.prod fun w n => (w.evalAt (linSec s c * (s (pivotIndex s w hr))⁻¹) ^ k) ^ n)
        = Z.prod fun w n => w.evalAt (u * (s (pivotIndex s w hr))⁻¹ ^ k) ^ n := by
    intro Z hZ
    rw [Divisor.evalFun, ← Finsupp.prod_mul]
    refine Finsupp.prod_congr fun w hw => ?_
    have hgmem : g ∈ w.toValuationSubring :=
      w.mem_toValuationSubring_of_ord_nonneg_alt hg0 (by rw [hordg, (hZ w hw).1, (hZ w hw).2, mul_zero, sub_zero])
    have hcmem := linSec_div_pivot_mem s hs0 w hr c
    rw [← mul_zpow, ← w.evalAt_pow_of_mem (hrat w) hcmem k,
      ← w.evalAt_mul_of_mem (hrat w) hgmem (pow_mem hcmem k), e2 w]
  have hpk : ∀ Z : Divisor (AlgebraicClosure ℚ) F,
      (Z.prod fun w n => (w.evalAt (linSec s c * (s (pivotIndex s w hr))⁻¹) ^ k) ^ n)
        = (Z.prod fun w n => w.evalAt (linSec s c * (s (pivotIndex s w hr))⁻¹) ^ n) ^ k := by
    intro Z
    rw [Finsupp.prod, Finsupp.prod, ← Finset.prod_pow]
    exact Finset.prod_congr rfl fun w _ => (zpow_pow_comm' _ _ _).symm

  have hX := key_f B hB_gp
  rw [prod_evalAt_linSec_div_pivot s hs0 hr B hB0 (fun w _ => hrat w) b,
    prod_evalAt_linSec_div_pivot s hs0 hr B hB0 (fun w _ => hrat w) a] at hX
  have hY := key_f Zc hZc_gp
  have hZc0 := heff c Zc hc hZc
  rw [prod_evalAt_linSec_div_pivot s hs0 hr Zc hZc0 (fun w _ => hrat w) b,
    prod_evalAt_linSec_div_pivot s hs0 hr Zc hZc0 (fun w _ => hrat w) a] at hY
  have hP := key_g Za hZa_gp
  rw [hpk Za, prod_evalAt_linSec_div_pivot s hs0 hr Za hZa0 (fun w _ => hrat w) c,
    prod_evalAt_div_pivot_pow s hr k u Za hZa0] at hP
  have hQ := key_g Zb hZb_gp
  rw [hpk Zb, prod_evalAt_linSec_div_pivot s hs0 hr Zb hZb0 (fun w _ => hrat w) c,
    prod_evalAt_div_pivot_pow s hr k u Zb hZb0] at hQ

  have hYne : Divisor.evalFun f Zc ≠ 0 :=
    Divisor.evalFun_ne_zero_of_forall_ne_zero fun v hv => hfne v (hZc_gp v hv).1 (hZc_gp v hv).2
  have hQne : Divisor.evalFun g Zb ≠ 0 :=
    Divisor.evalFun_ne_zero_of_forall_ne_zero fun v hv => hgne v (hZb_gp v hv).1 (hZb_gp v hv).2
  have hXQ : Divisor.evalFun f B * Divisor.evalFun g Zb = Divisor.evalFun g Za * Divisor.evalFun f Zc ^ k := by
    rw [zpow_neg, zpow_natCast, zpow_neg, zpow_one] at hW
    field_simp at hW
    linear_combination hW
  rw [← hX, ← hY, ← hP, ← hQ]
  linear_combination (MvPolynomial.eval b (chowForm s B) * MvPolynomial.eval b (chowForm s Zc) ^ k
    * MvPolynomial.eval c (chowForm s Za) ^ k * MvPolynomial.eval c (chowForm s Zb) ^ k) * hXQ

end Assembly

end AlgebraicCurve

end

set_option autoImplicit false

p2m_open "AlgebraicCurve P2MW.S_ModularCurve_JZero_chowReciprocity_embedding.AlgebraicCurve ModularCurve P2MW.S_ModularCurve_JZero_chowReciprocity_embedding.ModularCurve"

noncomputable section

namespace ModularCurve p2m_export "ModularCurve" "embDegree embDivisor IsEmbBasis jq_mem_full jq modularFunctionFieldBar JZero coeffEmb coeffEmb_mem_laurentBaseChange transcendental_coeffEmb_jq exists_rational_presentation_modularFunctionFieldBar hasPrincipalDivisors_modularFunctionFieldBar_unconditional exists_adapted_family_modularFunctionFieldBar" end ModularCurve
p2m_open_scoped "ModularCurve" in

def ModularCurve.jBar (N : ℕ) [NeZero N] : modularFunctionFieldBar N :=
  ⟨coeffEmb (AlgebraicClosure ℚ) jq, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jq_mem_full N)⟩

p2m_open_scoped "ModularCurve" in

theorem ModularCurve.transcendental_jBar' (N : ℕ) [NeZero N] :
    Transcendental (AlgebraicClosure ℚ) (jBar N) :=
  ModularCurve.transcendental_coeffEmb_jq (AlgebraicClosure ℚ) N

p2m_open_scoped "ModularCurve" in

def ModularCurve.ratFuncBarHom (N : ℕ) [NeZero N] :
    RatFunc (AlgebraicClosure ℚ) →ₐ[AlgebraicClosure ℚ] modularFunctionFieldBar N :=
  RatFunc.liftAlgHom (Polynomial.aeval (jBar N))
    (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _
      (transcendental_iff_injective.mp (transcendental_jBar' N)))

p2m_open_scoped "ModularCurve" in

@[reducible]
def ModularCurve.instAlgebraRatFuncBar (N : ℕ) [NeZero N] :
    Algebra (RatFunc (AlgebraicClosure ℚ)) (modularFunctionFieldBar N) :=
  (ratFuncBarHom N).toRingHom.toAlgebra

p2m_open_scoped "ModularCurve" in
set_option synthInstance.maxHeartbeats 1600000 in

@[reducible]
def ModularCurve.instIsScalarTowerRatFuncBar (N : ℕ) [NeZero N] :
    letI := instAlgebraRatFuncBar N
    IsScalarTower (AlgebraicClosure ℚ) (RatFunc (AlgebraicClosure ℚ)) (modularFunctionFieldBar N) :=
  letI := instAlgebraRatFuncBar N
  IsScalarTower.of_algebraMap_eq fun x => ((ratFuncBarHom N).commutes x).symm

p2m_open_scoped "ModularCurve" in

theorem ModularCurve.algebraMap_ratFuncBar_polynomial (N : ℕ) [NeZero N]
    (p : Polynomial (AlgebraicClosure ℚ)) :
    letI := instAlgebraRatFuncBar N
    algebraMap (RatFunc (AlgebraicClosure ℚ)) (modularFunctionFieldBar N)
        (algebraMap (Polynomial (AlgebraicClosure ℚ)) (RatFunc (AlgebraicClosure ℚ)) p)
      = Polynomial.aeval (jBar N) p := by
  letI := instAlgebraRatFuncBar N
  exact RatFunc.liftRingHom_algebraMap _ _ p

p2m_open_scoped "ModularCurve" in
set_option synthInstance.maxHeartbeats 1600000 in

@[reducible]
def ModularCurve.instFiniteDimensionalRatFuncBar (N : ℕ) [NeZero N] :
    letI := instAlgebraRatFuncBar N
    FiniteDimensional (RatFunc (AlgebraicClosure ℚ)) (modularFunctionFieldBar N) := by
  letI := instAlgebraRatFuncBar N
  obtain ⟨n, b, -, -, -, -, -, -, hspan, -⟩ :=
    ModularCurve.exists_rational_presentation_modularFunctionFieldBar N
  refine Module.Finite.of_surjective (Fintype.linearCombination (RatFunc (AlgebraicClosure ℚ)) b)
    fun x => ?_
  obtain ⟨q, c, hq, heq⟩ := hspan x

  have hjb : (⟨coeffEmb (AlgebraicClosure ℚ) jq, coeffEmb_mem_laurentBaseChange
      (AlgebraicClosure ℚ) (jq_mem_full N)⟩ : modularFunctionFieldBar N) = jBar N := rfl
  rw [hjb] at heq

  simp only [← algebraMap_ratFuncBar_polynomial N] at heq

  have hqR : (algebraMap (Polynomial (AlgebraicClosure ℚ)) (RatFunc (AlgebraicClosure ℚ)) q) ≠ 0 :=
    fun h => hq ((map_eq_zero_iff _ (IsFractionRing.injective _ _)).mp h)
  have hρq : algebraMap (RatFunc (AlgebraicClosure ℚ)) (modularFunctionFieldBar N)
      (algebraMap _ _ q) ≠ 0 := ((isUnit_iff_ne_zero.mpr hqR).map _).ne_zero
  refine ⟨fun i => (algebraMap _ (RatFunc (AlgebraicClosure ℚ)) (c i))
      / algebraMap _ (RatFunc (AlgebraicClosure ℚ)) q, ?_⟩

  simp only [Fintype.linearCombination_apply, Algebra.smul_def, map_div₀, div_mul_eq_mul_div,
    ← Finset.sum_div]
  rw [← heq, mul_div_cancel_right₀ _ hρq]

namespace ModularCurve
p2m_export "ModularCurve" "embDegree embDivisor IsEmbBasis jq_mem_full jq modularFunctionFieldBar JZero coeffEmb coeffEmb_mem_laurentBaseChange transcendental_coeffEmb_jq exists_rational_presentation_modularFunctionFieldBar hasPrincipalDivisors_modularFunctionFieldBar_unconditional exists_adapted_family_modularFunctionFieldBar"
p2m_open "ModularCurve"

theorem exists_isEmbBasis (N : ℕ) [NeZero N] :
    ∃ (r : ℕ) (s : Fin r → modularFunctionFieldBar N), IsEmbBasis N s := by
  obtain ⟨n, f, o, -, -, -, hrr⟩ :=
    ModularCurve.exists_adapted_family_modularFunctionFieldBar N (embDegree N)
  obtain ⟨hlin, hspan⟩ := hrr (embDegree N) le_rfl
  exact ⟨_, (fun i : {i // o i ≤ embDegree N} => f i) ∘ (Fintype.equivFin _).symm,
    hlin.comp _ (Fintype.equivFin _).symm.injective,
    by rw [Set.range_comp, Equiv.range_eq_univ, Set.image_univ]; exact hspan⟩

end ModularCurve

theorem solution (N : ℕ) [NeZero N] {r : ℕ}
    (s : Fin r → modularFunctionFieldBar N) (hs : IsEmbBasis N s) (k : ℕ) (u : modularFunctionFieldBar N)
    (hu : u ≠ 0) (huL : u ∈ riemannRochSpace ((k : ℤ) • embDivisor N))
    (B : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
    (hB : ∀ w, B w = w.ord u + ((k : ℤ) • embDivisor N) w) :
    ChowReciprocity s (embDivisor N) k u B := by
  letI := instAlgebraRatFuncBar N
  haveI := instIsScalarTowerRatFuncBar N
  haveI := instFiniteDimensionalRatFuncBar N
  haveI := ModularCurve.hasPrincipalDivisors_modularFunctionFieldBar_unconditional N
  have hsL : ∀ i, s i ∈ riemannRochSpace (embDivisor N) := fun i => by
    rw [← hs.2]
    exact Submodule.subset_span ⟨i, rfl⟩
  refine chowReciprocity_of_weilReciprocity
    (AlgebraicCurve.weilReciprocity (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
    (fun w => w.isRational_of_isAlgClosed) s (fun i => hs.1.ne_zero i) (embDivisor N) hsL k u hu B
    (fun w => by rw [hB w, Finsupp.smul_apply, smul_eq_mul]) (fun w => ?_)
  rcases mem_riemannRochSpace_iff.mp huL w with h0 | hle
  · exact (hu h0).elim
  · rw [hB w]
    rw [Finsupp.smul_apply, smul_eq_mul] at hle ⊢
    linarith

example (N : ℕ) [NeZero N] : True := by
  obtain ⟨r, s, hs⟩ := exists_isEmbBasis N
  have huL : (1 : modularFunctionFieldBar N) ∈ riemannRochSpace (((0 : ℕ) : ℤ) • embDivisor N) := by
    rw [mem_riemannRochSpace_iff]
    exact fun v => .inr (by simp [v.ord_one])
  have hB : ∀ w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N),
      (0 : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) w
        = w.ord 1 + (((0 : ℕ) : ℤ) • embDivisor N) w := fun w => by simp [w.ord_one]
  have := solution N s hs 0 1 one_ne_zero huL 0 hB
  trivial

example (N : ℕ) [NeZero N] :
    ∃ (r : ℕ) (s : Fin r → modularFunctionFieldBar N) (_ : IsEmbBasis N s) (k : ℕ)
      (u : modularFunctionFieldBar N) (_ : u ≠ 0) (_ : u ∈ riemannRochSpace ((k : ℤ) • embDivisor N))
      (B : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
      (_ : ∀ w, B w = w.ord u + ((k : ℤ) • embDivisor N) w), ChowReciprocity s (embDivisor N) k u B := by
  obtain ⟨r, s, hs⟩ := exists_isEmbBasis N
  have huL : (1 : modularFunctionFieldBar N) ∈ riemannRochSpace (((0 : ℕ) : ℤ) • embDivisor N) := by
    rw [mem_riemannRochSpace_iff]
    exact fun v => .inr (by simp [v.ord_one])
  have hB : ∀ w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N),
      (0 : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) w
        = w.ord 1 + (((0 : ℕ) : ℤ) • embDivisor N) w := fun w => by simp [w.ord_one]
  exact ⟨r, s, hs, 0, 1, one_ne_zero, huL, 0, hB, solution N s hs 0 1 one_ne_zero huL 0 hB⟩

end

#print axioms solution

end S_ModularCurve_JZero_chowReciprocity_embedding
end P2MW
export P2MW.S_ModularCurve_JZero_chowReciprocity_embedding (solution)
