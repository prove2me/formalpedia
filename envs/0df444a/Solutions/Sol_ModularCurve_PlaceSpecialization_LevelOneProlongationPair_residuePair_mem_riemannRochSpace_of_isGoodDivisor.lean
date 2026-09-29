-- Prove2me | solution 1 for ModularCurve.PlaceSpecialization.LevelOneProlongationPair.residuePair_mem_riemannRochSpace_of_isGoodDivisor
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/296bfd36-74a7-5286-99a9-399139b9adf6

import Mathlib
import Definitions.Def_ModularCurve_LevelOneProlongationPairRegularity
import Definitions.Def_ModularCurve_SupersingularNodes
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_GluedPic0
import Definitions.Def_AlgebraicCurve_RatFuncPlaceInfty
import Theorems.Thm_ModularCurve_PlaceSpecialization_isStrictTypeOne_or_isStrictTypeTwo_iff_ne
import Theorems.Thm_ModularCurve_not_isStrictType_of_isCuspidal
import Theorems.Thm_ModularCurve_not_isStrictType_of_isCuspidalSnd
import Theorems.Thm_ModularCurve_restrictAlong_heckeAlphaBar_frickeInvolutionBar_smul
import Theorems.Thm_ModularCurve_PlaceSpecialization_redFst_cuspInftyBar
import Theorems.Thm_ModularCurve_frobOnPlacesGeomLevel_charLGeomPlaceEquiv_placeInfty
import Theorems.Thm_ModularCurve_arithFrobC_smul_eq_frobOnPlacesGeomLevel
import Theorems.Thm_ModularCurve_arithFrobC_smul_charLGeomPlaceOfPoint
import Theorems.Thm_ModularCurve_pow_q_sq_eq_self_of_mem_ssJSet
import Theorems.Thm_ModularCurve_hasPrincipalDivisors_modularFunctionFieldBar_unconditional
import Theorems.Thm_ModularCurve_frickeInvolutionBar_frickeInvolutionBar
import Theorems.Thm_ValuationSubring_isAlgClosed_residueField
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_residuePair_mem_riemannRochSpace_of_isGoodDivisor
p2m_attr_erase "instance" "AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.PhiGen.instNeZeroPhiGenCosetA WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt"
p2m_attr_erase "simp" "AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one"
p2m_attr_erase "simp" "WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal"

set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000
set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.PlaceSpecialization

namespace FltWs24
namespace Img

section Finsupp

theorem neg_mapDomain_filter_le {α β : Type*} (r : α → β) (Q : α → Prop) {hQ : DecidablePred Q}
    (X Y : α →₀ ℤ) (hXY : ∀ a, -Y a ≤ X a) (b : β) :
    -(Finsupp.mapDomain r (Y.filter Q) b) ≤ Finsupp.mapDomain r (X.filter Q) b := by
  have h1 : -(Y.filter Q) ≤ X.filter Q := by
    intro a
    simp only [Finsupp.coe_neg, Pi.neg_apply, Finsupp.filter_apply]
    split_ifs
    · exact hXY a
    · simp
  have h2 := Finsupp.le_def.mp (Finsupp.mapDomain_mono (f := r) h1) b
  have h3 : Finsupp.mapDomain r (-(Y.filter Q)) = -Finsupp.mapDomain r (Y.filter Q) :=
    map_neg (Finsupp.mapDomain.addMonoidHom r) _
  rw [h3] at h2
  exact h2

theorem mapDomain_filter_nonneg {α β : Type*} (r : α → β) (Q : α → Prop) {hQ : DecidablePred Q}
    (X Y : α →₀ ℤ) (hXY : ∀ a, -Y a ≤ X a) (hY : ∀ a, Q a → Y a = 0) (b : β) :
    0 ≤ Finsupp.mapDomain r (X.filter Q) b := by
  have h := neg_mapDomain_filter_le r Q (hQ := hQ) X Y hXY b
  have hz : Y.filter Q = 0 := by
    ext a
    rw [Finsupp.filter_apply]
    split_ifs with ha
    · exact hY a ha
    · rfl
  rw [hz, Finsupp.mapDomain_zero] at h
  simpa using h

theorem mapDomain_nonneg {α β : Type*} (r : α → β) (X : α →₀ ℤ) (hX : ∀ a, 0 ≤ X a) (b : β) :
    0 ≤ Finsupp.mapDomain r X b := by
  have h : (0 : α →₀ ℤ) ≤ X := fun a => by simpa using hX a
  have h2 := Finsupp.le_def.mp (Finsupp.mapDomain_mono (f := r) h) b
  simpa using h2

theorem filter_nonneg {α : Type*} (Q : α → Prop) {hQ : DecidablePred Q} (X : α →₀ ℤ) (hX : ∀ a, 0 ≤ X a) (a : α) :
    0 ≤ X.filter Q a := by
  rw [Finsupp.filter_apply]
  split_ifs
  · exact hX a
  · exact le_rfl

end Finsupp

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
  {k : Type*} [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k]
  {red : A →+* k} {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}

theorem ord_nonneg_of_redFst_eq (P : PlaceSpecialization A q 1 data hKr k red hα hβ)
    {D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))} (hgood : P.IsGoodDivisor D)
    {G : modularFunctionFieldBar (1 * q)} (hG : G ∈ riemannRochSpace D)
    {v : Place k (modularFunctionFieldC k 1)}
    (hv : frobOnPlacesGeomLevel k 1 data hKr (frobOnPlacesGeomLevel k 1 data hKr v) = v)
    (W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))) (hW : P.redFst W = v) :
    0 ≤ W.ord G := by
  by_contra hneg
  push_neg at hneg
  have hG0 : G ≠ 0 := by
    rintro rfl
    rw [Place.ord_zero] at hneg
    exact lt_irrefl _ hneg
  have h1 := ((mem_riemannRochSpace_iff.mp hG) W).resolve_left hG0
  have hDW : D W ≠ 0 := by omega
  have htype := hgood W (Finsupp.mem_support_iff.mpr hDW)
  have h2 := (isStrictTypeOne_or_isStrictTypeTwo_iff_ne P W).mp htype
  rw [hW] at h2
  exact h2 hv

theorem redFst_frickeInvolutionBar_smul (P : PlaceSpecialization A q 1 data hKr k red hα hβ)
    (W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))) :
    P.redFst (frickeInvolutionBar (1 * q) • W) = P.redSnd W := by
  haveI : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
  show P.sp _ = P.sp _
  rw [restrictAlong_heckeAlphaBar_frickeInvolutionBar_smul q hα hβ W]

theorem frickeInvolutionBar_mul_self :
    frickeInvolutionBar (1 * q) * frickeInvolutionBar (1 * q) = 1 := by
  haveI : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
  refine AlgEquiv.ext fun y => ?_
  rw [AlgEquiv.mul_apply, AlgEquiv.one_apply]
  exact frickeInvolutionBar_frickeInvolutionBar (1 * q) y

theorem redSnd_cuspZeroBar (P : PlaceSpecialization A q 1 data hKr k red hα hβ) :
    P.redSnd (cuspZeroBar (1 * q)) = P.redFst (cuspInftyBar (1 * q)) := by
  rw [← redFst_frickeInvolutionBar_smul, cuspZeroBar_def, smul_smul, frickeInvolutionBar_mul_self, one_smul]

theorem frob_redFst_cuspInftyBar (P : PlaceSpecialization A q 1 data hKr k red hα hβ) :
    frobOnPlacesGeomLevel k 1 data hKr (P.redFst (cuspInftyBar (1 * q))) = P.redFst (cuspInftyBar (1 * q)) := by
  classical
  rw [redFst_cuspInftyBar P]
  exact frobOnPlacesGeomLevel_charLGeomPlaceEquiv_placeInfty k data hKr

theorem frob_frob_charLGeomPlaceOfPoint {a : k} (ha : a ∈ ssJSet q k) :
    frobOnPlacesGeomLevel k 1 data hKr (frobOnPlacesGeomLevel k 1 data hKr (charLGeomPlaceOfPoint k a))
      = charLGeomPlaceOfPoint k a := by
  haveI : PerfectField k := inferInstance
  rw [← arithFrobC_smul_eq_frobOnPlacesGeomLevel q k 1 data hKr (charLGeomPlaceOfPoint k a),
    arithFrobC_smul_charLGeomPlaceOfPoint q a,
    ← arithFrobC_smul_eq_frobOnPlacesGeomLevel q k 1 data hKr (charLGeomPlaceOfPoint k (a ^ q)),
    arithFrobC_smul_charLGeomPlaceOfPoint q (a ^ q), ← pow_mul, ← sq, pow_q_sq_eq_self_of_mem_ssJSet q ha]

theorem apply_eq_zero_of_isInftySide (P : PlaceSpecialization A q 1 data hKr k red hα hβ)
    {D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))} (hgood : P.IsGoodDivisor D)
    (W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))) (hW : P.IsInftySide W) : D W = 0 := by
  by_contra h
  have h1 := not_isStrictType_of_isCuspidal P W hW.1
  rcases hgood W (Finsupp.mem_support_iff.mpr h) with h2 | h2
  · exact h1.1 h2
  · exact h1.2 h2

theorem apply_eq_zero_of_isZeroSide (P : PlaceSpecialization A q 1 data hKr k red hα hβ)
    {D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))} (hgood : P.IsGoodDivisor D)
    (W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))) (hW : P.IsZeroSide W) : D W = 0 := by
  by_contra h
  have h1 := not_isStrictType_of_isCuspidalSnd P W hW.1
  rcases hgood W (Finsupp.mem_support_iff.mpr h) with h2 | h2
  · exact h1.1 h2
  · exact h1.2 h2

theorem fstPart_nonneg (P : PlaceSpecialization A q 1 data hKr k red hα hβ)
    {D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))} (hD : ∀ W, 0 ≤ D W) (W) :
    0 ≤ P.fstPart D W := by
  unfold PlaceSpecialization.fstPart
  exact filter_nonneg _ D hD W

theorem sndPart_nonneg (P : PlaceSpecialization A q 1 data hKr k red hα hβ)
    {D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))} (hD : ∀ W, 0 ≤ D W) (W) :
    0 ≤ P.sndPart D W := by
  unfold PlaceSpecialization.sndPart
  exact filter_nonneg _ D hD W

section Constants

variable {P : PlaceSpecialization A q 1 data hKr k red hα hβ} (R : P.LevelOneProlongationPair)

theorem algebraMap_mem_integers₁ (c : A) :
    algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (c : AlgebraicClosure ℚ) ∈ R.R₁.integers :=
  (R.R₁.algebraMap_mem_iff _).mpr c.2

theorem algebraMap_mem_integers₂ (c : A) :
    algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (c : AlgebraicClosure ℚ) ∈ R.R₂.integers :=
  (R.R₂.algebraMap_mem_iff _).mpr c.2

theorem ι_algebraMap (x : ResidueField A) :
    R.ι (algebraMap (ResidueField A) (modularFunctionFieldFullC (ResidueField A) 1) x)
      = algebraMap k (modularFunctionFieldC k 1) (R.redBar x) := by
  apply Subtype.ext
  rw [R.ι_coe]
  change coeffMap R.redBar (algebraMap (ResidueField A) (LaurentSeries (ResidueField A)) x)
    = algebraMap k (LaurentSeries k) (R.redBar x)
  rw [algebraMap_laurentSeries_eq_single, algebraMap_laurentSeries_eq_single, coeffMap_single]

theorem algebraMap_mem_riemannRochSpace {K L : Type*} [Field K] [Field L] [Algebra K L]
    {E : Divisor K L} (hE : ∀ v, 0 ≤ E v) (c : K) : algebraMap K L c ∈ riemannRochSpace E := by
  intro v
  refine (Place.adicValuation_algebraMap_le_one v c).trans ?_
  rw [← WithZero.exp_zero, WithZero.exp_le_exp]
  exact hE v

theorem exists_residue_add_ne_zero (G : modularFunctionFieldBar (1 * q))
    (h₁ : G ∈ R.R₁.integers) (h₂ : G ∈ R.R₂.integers) :
    ∃ c : A,
      R.R₁.residue ⟨G + algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (c : AlgebraicClosure ℚ),
        add_mem h₁ (algebraMap_mem_integers₁ R c)⟩ ≠ 0 ∧
      R.R₂.residue ⟨G + algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (c : AlgebraicClosure ℚ),
        add_mem h₂ (algebraMap_mem_integers₂ R c)⟩ ≠ 0 := by
  haveI : IsAlgClosed (ResidueField A) := ValuationSubring.isAlgClosed_residueField A
  haveI : Infinite (ResidueField A) := inferInstance

  let r₁ := R.R₁.residue ⟨G, h₁⟩
  let r₂ := R.R₂.residue ⟨G, h₂⟩

  obtain ⟨xbar, hx⟩ : ∃ xbar : ResidueField A,
      algebraMap (ResidueField A) (modularFunctionFieldFullC (ResidueField A) 1) xbar ≠ -r₁ ∧
      algebraMap (ResidueField A) (modularFunctionFieldFullC (ResidueField A) 1) xbar ≠ -r₂ := by
    by_contra hall
    push_neg at hall

    have hsub : (Set.univ : Set (ResidueField A)) ⊆
        ((algebraMap (ResidueField A) (modularFunctionFieldFullC (ResidueField A) 1)) ⁻¹' {-r₁, -r₂}) := by
      intro x _
      rcases eq_or_ne (algebraMap (ResidueField A) (modularFunctionFieldFullC (ResidueField A) 1) x) (-r₁) with h | h
      · exact Or.inl h
      · exact Or.inr (hall x h)
    have hfin : (Set.univ : Set (ResidueField A)).Finite :=
      ((Set.toFinite {-r₁, -r₂}).preimage
        ((algebraMap (ResidueField A) (modularFunctionFieldFullC (ResidueField A) 1)).injective.injOn)).subset hsub
    exact Set.infinite_univ hfin
  obtain ⟨c, rfl⟩ := IsLocalRing.residue_surjective xbar
  refine ⟨c, ?_, ?_⟩
  · have : (⟨G + algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (c : AlgebraicClosure ℚ),
        add_mem h₁ (algebraMap_mem_integers₁ R c)⟩ : R.R₁.integers)
        = ⟨G, h₁⟩ + ⟨_, algebraMap_mem_integers₁ R c⟩ := rfl
    rw [this, map_add, R.R₁.residue_algebraMap]
    intro h0
    exact hx.1 (eq_neg_of_add_eq_zero_right h0)
  · have : (⟨G + algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (c : AlgebraicClosure ℚ),
        add_mem h₂ (algebraMap_mem_integers₂ R c)⟩ : R.R₂.integers)
        = ⟨G, h₂⟩ + ⟨_, algebraMap_mem_integers₂ R c⟩ := rfl
    rw [this, map_add, R.R₂.residue_algebraMap]
    intro h0
    exact hx.2 (eq_neg_of_add_eq_zero_right h0)

end Constants

section Unit

variable {P : PlaceSpecialization A q 1 data hKr k red hα hβ} (R : P.LevelOneProlongationPair)

theorem residue₁_mem_of_ne_zero (hR : R.IsModel) (S₀ : Finset k) (hNR : R.RegularityLaw S₀)
    {D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))} (hD : ∀ W, 0 ≤ D W) (hgood : P.IsGoodDivisor D)
    {G : modularFunctionFieldBar (1 * q)} (hG : G ∈ riemannRochSpace D)
    (h₁ : G ∈ R.R₁.integers) (h₂ : G ∈ R.R₂.integers)
    (hne₁ : R.R₁.residue ⟨G, h₁⟩ ≠ 0) (hne₂ : R.R₂.residue ⟨G, h₂⟩ ≠ 0) :
    (R.residue₁ ⟨G, h₁⟩ : modularFunctionFieldC k 1) ∈ riemannRochSpace (Finsupp.mapDomain P.redFst (P.fstPart D)) := by
  classical
  haveI : NeZero (1 * q) := ⟨by rw [one_mul]; exact (Fact.out : q.Prime).ne_zero⟩
  have hG0 : G ≠ 0 := by
    rintro rfl
    apply hne₁
    have : (⟨(0 : modularFunctionFieldBar (1 * q)), h₁⟩ : R.R₁.integers) = 0 := rfl
    rw [this, map_zero]
  have hPD := hasPrincipalDivisors_modularFunctionFieldBar_unconditional (1 * q)
  obtain ⟨D', hD', -⟩ := HasPrincipalDivisors.exists_divisor (self := hPD) G hG0
  have hXY : ∀ W, -D W ≤ D' W := fun W => by
    rw [hD' W]
    exact ((mem_riemannRochSpace_iff.mp hG) W).resolve_left hG0
  rw [mem_riemannRochSpace_iff]
  intro v
  right
  have h0 : 0 ≤ Finsupp.mapDomain P.redFst (P.fstPart D) v :=
    mapDomain_nonneg _ _ (fstPart_nonneg P hD) _
  by_cases hv : frobOnPlacesGeomLevel k 1 data hKr (frobOnPlacesGeomLevel k 1 data hKr v) = v
  · by_cases hc : v = P.redFst (cuspInftyBar (1 * q))
    ·
      have hlaw := hR.2.2.1 G h₁ h₂ hne₁ hne₂ D' hD'
      have hb := (mapDomain_filter_nonneg P.redFst P.IsInftySide D' D hXY
        (fun W hW => apply_eq_zero_of_isInftySide P hgood W hW) (P.redFst (cuspInftyBar (1 * q)))).trans_eq hlaw
      rw [hc] at h0 ⊢
      omega
    ·
      have hreg := (hNR.1 G h₁ h₂ v hv hc
        (fun W hW => ord_nonneg_of_redFst_eq P hgood hG hv W hW)).1 (by
          rw [LevelOneProlongationPair.residue₁_apply]
          exact (map_ne_zero_iff R.ι R.ι.injective).mpr hne₁)
      omega
  ·
    have hlaw := hR.1 G h₁ h₂ hne₁ hne₂ D' hD' v hv
    exact (neg_mapDomain_filter_le P.redFst P.IsStrictTypeOne D' D hXY v).trans_eq hlaw

theorem residue₂_mem_of_ne_zero (hR : R.IsModel) (S₀ : Finset k) (hNR : R.RegularityLaw S₀)
    {D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))} (hD : ∀ W, 0 ≤ D W) (hgood : P.IsGoodDivisor D)
    {G : modularFunctionFieldBar (1 * q)} (hG : G ∈ riemannRochSpace D)
    (h₁ : G ∈ R.R₁.integers) (h₂ : G ∈ R.R₂.integers)
    (hne₁ : R.R₁.residue ⟨G, h₁⟩ ≠ 0) (hne₂ : R.R₂.residue ⟨G, h₂⟩ ≠ 0) :
    (R.residue₂ ⟨G, h₂⟩ : modularFunctionFieldC k 1) ∈ riemannRochSpace (Finsupp.mapDomain P.redSnd (P.sndPart D)) := by
  classical
  haveI : NeZero (1 * q) := ⟨by rw [one_mul]; exact (Fact.out : q.Prime).ne_zero⟩
  have hG0 : G ≠ 0 := by
    rintro rfl
    apply hne₁
    have : (⟨(0 : modularFunctionFieldBar (1 * q)), h₁⟩ : R.R₁.integers) = 0 := rfl
    rw [this, map_zero]
  have hPD := hasPrincipalDivisors_modularFunctionFieldBar_unconditional (1 * q)
  obtain ⟨D', hD', -⟩ := HasPrincipalDivisors.exists_divisor (self := hPD) G hG0
  have hXY : ∀ W, -D W ≤ D' W := fun W => by
    rw [hD' W]
    exact ((mem_riemannRochSpace_iff.mp hG) W).resolve_left hG0
  rw [mem_riemannRochSpace_iff]
  intro u
  right
  have h0 : 0 ≤ Finsupp.mapDomain P.redSnd (P.sndPart D) u :=
    mapDomain_nonneg _ _ (sndPart_nonneg P hD) _
  by_cases hu : frobOnPlacesGeomLevel k 1 data hKr (frobOnPlacesGeomLevel k 1 data hKr u) = u
  ·
    set v := frobOnPlacesGeomLevel k 1 data hKr u with hvdef
    have hφv : frobOnPlacesGeomLevel k 1 data hKr v = u := hu
    have hv : frobOnPlacesGeomLevel k 1 data hKr (frobOnPlacesGeomLevel k 1 data hKr v) = v := by
      rw [hφv]
    by_cases hc : v = P.redFst (cuspInftyBar (1 * q))
    ·
      have huc : u = P.redSnd (cuspZeroBar (1 * q)) := by
        rw [redSnd_cuspZeroBar, ← hφv, hc, frob_redFst_cuspInftyBar]
      have hlaw := hR.2.2.2 G h₁ h₂ hne₁ hne₂ D' hD'
      have hb := (mapDomain_filter_nonneg P.redSnd P.IsZeroSide D' D hXY
        (fun W hW => apply_eq_zero_of_isZeroSide P hgood W hW) (P.redSnd (cuspZeroBar (1 * q)))).trans_eq hlaw
      rw [← huc] at hb
      omega
    ·
      have hreg := (hNR.1 G h₁ h₂ v hv hc
        (fun W hW => ord_nonneg_of_redFst_eq P hgood hG hv W hW)).2 (by
          rw [LevelOneProlongationPair.residue₂_apply]
          exact (map_ne_zero_iff R.ι R.ι.injective).mpr hne₂)
      rw [hφv] at hreg
      omega
  · have hlaw := hR.2.1 G h₁ h₂ hne₁ hne₂ D' hD' u hu
    exact (neg_mapDomain_filter_le P.redSnd P.IsStrictTypeTwo D' D hXY u).trans_eq hlaw

end Unit

theorem main {P : PlaceSpecialization A q 1 data hKr k red hα hβ}
    (R : P.LevelOneProlongationPair) (hR : R.IsModel)
    (S₀ : Finset k) (hS₀ : ∀ a, a ∈ S₀ ↔ a ∈ ssJSet q k) (hNR : R.RegularityLaw S₀)
    (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)))
    (hD : ∀ W, 0 ≤ D W) (hgood : P.IsGoodDivisor D)
    (G : modularFunctionFieldBar (1 * q)) (hG : G ∈ riemannRochSpace D)
    (h₁ : G ∈ R.R₁.integers) (h₂ : G ∈ R.R₂.integers) :
    (R.ι (R.R₁.residue ⟨G, h₁⟩) : modularFunctionFieldC k 1) ∈
        riemannRochSpace (Finsupp.mapDomain P.redFst (P.fstPart D)) ∧
    (R.ι (R.R₂.residue ⟨G, h₂⟩) : modularFunctionFieldC k 1) ∈
        riemannRochSpace (Finsupp.mapDomain P.redSnd (P.sndPart D)) ∧
    ∀ a ∈ S₀, ∃ c : k,
      (frobNodePair q a).1.HasValue (R.ι (R.R₁.residue ⟨G, h₁⟩) : modularFunctionFieldC k 1) c ∧
      (frobNodePair q a).2.HasValue (R.ι (R.R₂.residue ⟨G, h₂⟩) : modularFunctionFieldC k 1) c := by
  classical

  obtain ⟨c, hc₁, hc₂⟩ := exists_residue_add_ne_zero R G h₁ h₂
  set G' := G + algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (c : AlgebraicClosure ℚ) with hG'
  have h₁' : G' ∈ R.R₁.integers := add_mem h₁ (algebraMap_mem_integers₁ R c)
  have h₂' : G' ∈ R.R₂.integers := add_mem h₂ (algebraMap_mem_integers₂ R c)
  have hG'mem : G' ∈ riemannRochSpace D := add_mem hG (algebraMap_mem_riemannRochSpace hD _)
  have hm₁ := residue₁_mem_of_ne_zero R hR S₀ hNR hD hgood hG'mem h₁' h₂' hc₁ hc₂
  have hm₂ := residue₂_mem_of_ne_zero R hR S₀ hNR hD hgood hG'mem h₁' h₂' hc₁ hc₂

  have hsub₁ : (⟨G, h₁⟩ : R.R₁.integers) = ⟨G', h₁'⟩ - ⟨_, algebraMap_mem_integers₁ R c⟩ := by
    apply Subtype.ext
    show G = G' - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (c : AlgebraicClosure ℚ)
    rw [hG', add_sub_cancel_right]
  have hsub₂ : (⟨G, h₂⟩ : R.R₂.integers) = ⟨G', h₂'⟩ - ⟨_, algebraMap_mem_integers₂ R c⟩ := by
    apply Subtype.ext
    show G = G' - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (c : AlgebraicClosure ℚ)
    rw [hG', add_sub_cancel_right]
  have hcst₁ : R.ι (R.R₁.residue ⟨G, h₁⟩) = R.residue₁ ⟨G', h₁'⟩
      - algebraMap k (modularFunctionFieldC k 1) (R.redBar (IsLocalRing.residue A c)) := by
    rw [LevelOneProlongationPair.residue₁_apply, ← ι_algebraMap R, ← R.R₁.residue_algebraMap c, ← map_sub,
      ← map_sub, ← hsub₁]
  have hcst₂ : R.ι (R.R₂.residue ⟨G, h₂⟩) = R.residue₂ ⟨G', h₂'⟩
      - algebraMap k (modularFunctionFieldC k 1) (R.redBar (IsLocalRing.residue A c)) := by
    rw [LevelOneProlongationPair.residue₂_apply, ← ι_algebraMap R, ← R.R₂.residue_algebraMap c, ← map_sub,
      ← map_sub, ← hsub₂]
  have hD₁ : ∀ v, 0 ≤ Finsupp.mapDomain P.redFst (P.fstPart D) v :=
    fun v => mapDomain_nonneg _ _ (fstPart_nonneg P hD) v
  have hD₂ : ∀ v, 0 ≤ Finsupp.mapDomain P.redSnd (P.sndPart D) v :=
    fun v => mapDomain_nonneg _ _ (sndPart_nonneg P hD) v
  refine ⟨?_, ?_, ?_⟩
  · rw [hcst₁]
    exact sub_mem hm₁ (algebraMap_mem_riemannRochSpace hD₁ _)
  · rw [hcst₂]
    exact sub_mem hm₂ (algebraMap_mem_riemannRochSpace hD₂ _)
  · intro a ha
    have ha' : a ∈ ssJSet q k := (hS₀ a).mp ha
    have hfix := frob_frob_charLGeomPlaceOfPoint (data := data) (hKr := hKr) ha'
    obtain ⟨c, hc⟩ := hNR.2 G h₁ h₂ a ha (pow_q_sq_eq_self_of_mem_ssJSet q ha')
      (fun W hW => ord_nonneg_of_redFst_eq P hgood hG hfix W (by rw [hW, frobNodePair_fst]))
    exact ⟨c, hc⟩

end FltWs24.Img

open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.PlaceSpecialization in
theorem solution
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k]
    {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
    {P : PlaceSpecialization A q 1 data hKr k red hα hβ}
    (R : P.LevelOneProlongationPair) (hR : R.IsModel)
    (S₀ : Finset k) (hS₀ : ∀ a, a ∈ S₀ ↔ a ∈ ssJSet q k) (hNR : R.RegularityLaw S₀)
    (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)))
    (hD : ∀ W, 0 ≤ D W) (hgood : P.IsGoodDivisor D)
    (G : modularFunctionFieldBar (1 * q)) (hG : G ∈ riemannRochSpace D)
    (h₁ : G ∈ R.R₁.integers) (h₂ : G ∈ R.R₂.integers) :
    (R.ι (R.R₁.residue ⟨G, h₁⟩) : modularFunctionFieldC k 1) ∈
        riemannRochSpace (Finsupp.mapDomain P.redFst (P.fstPart D)) ∧
    (R.ι (R.R₂.residue ⟨G, h₂⟩) : modularFunctionFieldC k 1) ∈
        riemannRochSpace (Finsupp.mapDomain P.redSnd (P.sndPart D)) ∧
    ∀ a ∈ S₀, ∃ c : k,
      (frobNodePair q a).1.HasValue (R.ι (R.R₁.residue ⟨G, h₁⟩) : modularFunctionFieldC k 1) c ∧
      (frobNodePair q a).2.HasValue (R.ι (R.R₂.residue ⟨G, h₂⟩) : modularFunctionFieldC k 1) c :=
  FltWs24.Img.main R hR S₀ hS₀ hNR D hD hgood G hG h₁ h₂

end S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_residuePair_mem_riemannRochSpace_of_isGoodDivisor
end P2MW
export P2MW.S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_residuePair_mem_riemannRochSpace_of_isGoodDivisor (solution)
