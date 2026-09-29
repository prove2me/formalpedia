-- Prove2me | solution 1 for ModularCurve.PlaceSpecialization.ProlongationTuple.xDepth_eq_and_yDepth_eq_of_nodeCoordinates
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/0c2abe43-fa12-59ee-9dff-6fe8d773c7cb

import Definitions.Def_ModularCurve_NodeDepth
import Theorems.Thm_ModularCurve_isCurveOver_modularFunctionFieldBar
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_valuation_pow_crossingExponent_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_xDepth_eq_and_yDepth_eq_of_nodeCoordinates
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar"
set_option synthInstance.maxHeartbeats 1600000
set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve
open ModularCurve.PlaceSpecialization ModularCurve.PlaceSpecialization.ProlongationTuple

namespace NodeDepthRatio

private theorem inv_mem_of_isUnit {F : Type*} [Field F] {S : ValuationSubring F} {y : F} (hy : y ∈ S)
    (hu : IsUnit (⟨y, hy⟩ : S)) : y⁻¹ ∈ S := by
  obtain ⟨v, hv⟩ := hu.exists_right_inv
  have hvF : y * (v : F) = 1 := by
    have h := congrArg Subtype.val hv
    simpa using h
  have hv' : (v : F) = y⁻¹ := eq_inv_of_mul_eq_one_right hvF
  exact hv' ▸ v.2

private theorem inv_mem_subring_of_isUnit {F : Type*} [Field F] {S : Subring F} {y : F} (hy : y ∈ S)
    (hu : IsUnit (⟨y, hy⟩ : S)) : y⁻¹ ∈ S := by
  obtain ⟨v, hv⟩ := hu.exists_right_inv
  have hvF : y * (v : F) = 1 := by
    have h := congrArg Subtype.val hv
    simpa using h
  have hv' : (v : F) = y⁻¹ := eq_inv_of_mul_eq_one_right hvF
  exact hv' ▸ v.2

private theorem ratio_eq {F : Type*} [Field F] {x y x' y' a u a' u' : F}
    (hxy : x * y = a * u) (hxy' : x' * y' = a' * u') (hy : y ≠ 0) (hy' : y' ≠ 0) (ha' : a' ≠ 0)
    (hu' : u' ≠ 0) : x * x'⁻¹ = a / a' * (u * u'⁻¹ * (y' * y⁻¹)) := by
  have hx : x = a * u / y := (eq_div_iff hy).mpr hxy
  have hx' : x' = a' * u' / y' := (eq_div_iff hy').mpr hxy'
  rw [hx, hx']
  field_simp

private theorem inv_eq {F : Type*} [Field F] {x' y' a' u' : F} (hxy' : x' * y' = a' * u') (ha' : a' ≠ 0)
    (hu' : u' ≠ 0) : x'⁻¹ = y' * (u'⁻¹ * a'⁻¹) := by
  have hy' : y' ≠ 0 := by
    rintro rfl
    exact mul_ne_zero ha' hu' (by rw [← hxy', mul_zero])
  have hx' : x' = a' * u' / y' := (eq_div_iff hy').mpr hxy'
  rw [hx']
  field_simp

private theorem evalAt_mul {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)
    (hv : v.IsRational) {f g : F} (hf : f ∈ v.toValuationSubring) (hg : g ∈ v.toValuationSubring) :
    v.evalAt (f * g) = v.evalAt f * v.evalAt g := by
  apply v.algebraMap_residueField_injective
  rw [map_mul, v.algebraMap_evalAt hv (mul_mem hf hg), v.algebraMap_evalAt hv hf, v.algebraMap_evalAt hv hg,
    ← map_mul]
  rfl

private theorem eq_one_of_mul_eq_one {Γ : Type*} [LinearOrderedCommGroupWithZero Γ] {a b : Γ} (ha : a ≤ 1)
    (hb : b ≤ 1) (hab : a * b = 1) : a = 1 :=
  le_antisymm ha (calc (1 : Γ) = a * b := hab.symm
    _ ≤ a * 1 := mul_le_mul_right hb a
    _ = a := mul_one a)

section

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
  {k : Type*} [Field k] [CharP k q] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
  {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
  {P : PlaceSpecialization A q N data hKr k red hα hβ}

private theorem isRational (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) :
    V.IsRational := by
  haveI := (ModularCurve.isCurveOver_modularFunctionFieldBar (N * q)).finiteResidue V
  exact (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := AlgebraicClosure ℚ) (K := V.ResidueField)).2

private theorem coe_nodeConst (R : ProlongationTuple P) (K : IntermediateField ℚ (AlgebraicClosure ℚ))
    (w : Place k (modularFunctionFieldC k N)) (z : ↥(NodeLocalized.coeffSubring A K)) :
    ((R.nodeConst K w z : ↥(R.nodeIntegersOver K w)) : ↥(modularFunctionFieldBar (N * q)))
      = algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (z : AlgebraicClosure ℚ) :=
  rfl

variable (R : ProlongationTuple P) [PerfectField k] {w : Place k (modularFunctionFieldC k N)}
  {K K' : IntermediateField ℚ (AlgebraicClosure ℚ)} (c : R.NodeCoordinates K w) (c' : R.NodeCoordinates K' w)

private theorem isUnit_y_fst :
    IsUnit (⟨((c.y : ↥(R.nodeIntegersOver K w)) : ↥(modularFunctionFieldBar (N * q))),
      R.mem_integersFst_of_mem_nodeIntegers c.y.2.1⟩ : R.R₁.integers) := by
  apply R.R₁.isUnit_of_residue_ne_zero
  intro h
  apply c.nodeResidue₁_y_ne_zero
  rw [nodeResidue₁_apply, residue₁_apply]
  exact (congrArg R.ι h).trans (map_zero _)

private theorem isUnit_x_snd :
    IsUnit (⟨((c.x : ↥(R.nodeIntegersOver K w)) : ↥(modularFunctionFieldBar (N * q))),
      R.mem_integersSnd_of_mem_nodeIntegers c.x.2.1⟩ : R.R₂.integers) := by
  apply R.R₂.isUnit_of_residue_ne_zero
  intro h
  apply c.nodeResidue₂_x_ne_zero
  rw [nodeResidue₂_apply, residue₂_apply]
  exact (congrArg R.ι h).trans (map_zero _)

private theorem y_ne_zero : ((c.y : ↥(R.nodeIntegersOver K w)) : ↥(modularFunctionFieldBar (N * q))) ≠ 0 :=
  fun h => (isUnit_y_fst R c).ne_zero (Subtype.ext h)

private theorem x_ne_zero : ((c.x : ↥(R.nodeIntegersOver K w)) : ↥(modularFunctionFieldBar (N * q))) ≠ 0 :=
  fun h => (isUnit_x_snd R c).ne_zero (Subtype.ext h)

private theorem ratio_x_mem (a a' : AlgebraicClosure ℚ) (u u' : ↥(modularFunctionFieldBar (N * q)))
    (hu : u ∈ R.nodeIntegers w) (hu'i : u'⁻¹ ∈ R.nodeIntegers w)
    (hxy : ((c.x : ↥(R.nodeIntegersOver K w)) : ↥(modularFunctionFieldBar (N * q))) * c.y
      = algebraMap (AlgebraicClosure ℚ) _ a * u)
    (hxy' : ((c'.x : ↥(R.nodeIntegersOver K' w)) : ↥(modularFunctionFieldBar (N * q))) * c'.y
      = algebraMap (AlgebraicClosure ℚ) _ a' * u')
    (ht : a / a' ∈ A) :
    ((c.x : ↥(R.nodeIntegersOver K w)) : ↥(modularFunctionFieldBar (N * q)))
        * ((c'.x : ↥(R.nodeIntegersOver K' w)) : ↥(modularFunctionFieldBar (N * q)))⁻¹ ∈ R.nodeIntegers w := by
  have hxy'0 : ((c'.x : ↥(R.nodeIntegersOver K' w)) : ↥(modularFunctionFieldBar (N * q))) * c'.y ≠ 0 :=
    mul_ne_zero (x_ne_zero R c') (y_ne_zero R c')
  have ha' : algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) a' ≠ 0 := by
    intro h; apply hxy'0; rw [hxy', h, zero_mul]
  have hu'0 : u' ≠ 0 := by
    intro h; apply hxy'0; rw [hxy', h, mul_zero]
  have hr := ratio_eq hxy hxy' (y_ne_zero R c) (y_ne_zero R c') ha' hu'0
  rw [← map_div₀] at hr
  refine ⟨?_, ?_, fun V hV => ?_⟩
  ·
    rw [hr]
    exact mul_mem ((R.R₁.algebraMap_mem_iff _).mpr ht) (mul_mem (mul_mem (R.mem_integersFst_of_mem_nodeIntegers hu)
      (R.mem_integersFst_of_mem_nodeIntegers hu'i)) (mul_mem (R.mem_integersFst_of_mem_nodeIntegers c'.y.2.1)
      (inv_mem_of_isUnit _ (isUnit_y_fst R c))))
  ·
    exact mul_mem (R.mem_integersSnd_of_mem_nodeIntegers c.x.2.1) (inv_mem_of_isUnit _ (isUnit_x_snd R c'))
  ·
    rw [inv_eq hxy' ha' hu'0]
    refine mul_mem (R.mem_toValuationSubring_of_mem_nodeIntegers c.x.2.1 hV)
      (mul_mem (R.mem_toValuationSubring_of_mem_nodeIntegers c'.y.2.1 hV)
        (mul_mem (R.mem_toValuationSubring_of_mem_nodeIntegers hu'i hV) ?_))
    rw [← map_inv₀]
    exact V.algebraMap_mem' _

private theorem ratio_y_mem (a a' : AlgebraicClosure ℚ) (u u' : ↥(modularFunctionFieldBar (N * q)))
    (hu : u ∈ R.nodeIntegers w) (hu'i : u'⁻¹ ∈ R.nodeIntegers w)
    (hxy : ((c.x : ↥(R.nodeIntegersOver K w)) : ↥(modularFunctionFieldBar (N * q))) * c.y
      = algebraMap (AlgebraicClosure ℚ) _ a * u)
    (hxy' : ((c'.x : ↥(R.nodeIntegersOver K' w)) : ↥(modularFunctionFieldBar (N * q))) * c'.y
      = algebraMap (AlgebraicClosure ℚ) _ a' * u')
    (ht : a / a' ∈ A) :
    ((c.y : ↥(R.nodeIntegersOver K w)) : ↥(modularFunctionFieldBar (N * q)))
        * ((c'.y : ↥(R.nodeIntegersOver K' w)) : ↥(modularFunctionFieldBar (N * q)))⁻¹ ∈ R.nodeIntegers w := by
  have hxy'0 : ((c'.x : ↥(R.nodeIntegersOver K' w)) : ↥(modularFunctionFieldBar (N * q))) * c'.y ≠ 0 :=
    mul_ne_zero (x_ne_zero R c') (y_ne_zero R c')
  have ha' : algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) a' ≠ 0 := by
    intro h; apply hxy'0; rw [hxy', h, zero_mul]
  have hu'0 : u' ≠ 0 := by
    intro h; apply hxy'0; rw [hxy', h, mul_zero]
  have hyx : ((c.y : ↥(R.nodeIntegersOver K w)) : ↥(modularFunctionFieldBar (N * q))) * c.x
      = algebraMap (AlgebraicClosure ℚ) _ a * u := (mul_comm _ _).trans hxy
  have hyx' : ((c'.y : ↥(R.nodeIntegersOver K' w)) : ↥(modularFunctionFieldBar (N * q))) * c'.x
      = algebraMap (AlgebraicClosure ℚ) _ a' * u' := (mul_comm _ _).trans hxy'
  have hr := ratio_eq hyx hyx' (x_ne_zero R c) (x_ne_zero R c') ha' hu'0
  rw [← map_div₀] at hr
  refine ⟨?_, ?_, fun V hV => ?_⟩
  ·
    exact mul_mem (R.mem_integersFst_of_mem_nodeIntegers c.y.2.1) (inv_mem_of_isUnit _ (isUnit_y_fst R c'))
  ·
    rw [hr]
    exact mul_mem ((R.R₂.algebraMap_mem_iff _).mpr ht) (mul_mem (mul_mem (R.mem_integersSnd_of_mem_nodeIntegers hu)
      (R.mem_integersSnd_of_mem_nodeIntegers hu'i)) (mul_mem (R.mem_integersSnd_of_mem_nodeIntegers c'.x.2.1)
      (inv_mem_of_isUnit _ (isUnit_x_snd R c))))
  · rw [inv_eq hyx' ha' hu'0]
    refine mul_mem (R.mem_toValuationSubring_of_mem_nodeIntegers c.y.2.1 hV)
      (mul_mem (R.mem_toValuationSubring_of_mem_nodeIntegers c'.x.2.1 hV)
        (mul_mem (R.mem_toValuationSubring_of_mem_nodeIntegers hu'i hV) ?_))
    rw [← map_inv₀]
    exact V.algebraMap_mem' _

omit [PerfectField k] in

private theorem inv_mem_nodeIntegers_of_isUnit {u : ↥(R.nodeIntegersOver K w)} (hu : IsUnit u) :
    (u : ↥(modularFunctionFieldBar (N * q)))⁻¹ ∈ R.nodeIntegers w :=
  R.nodeIntegersOver_le K w (inv_mem_subring_of_isUnit u.2 (by simpa using hu))

private theorem nodeEquation (ϖ : ↥(NodeLocalized.coeffSubring A K)) (E : ℕ) (u : ↥(R.nodeIntegersOver K w))
    (hxy : c.x * c.y = R.nodeConst K w ϖ ^ E * u) :
    ((c.x : ↥(R.nodeIntegersOver K w)) : ↥(modularFunctionFieldBar (N * q))) * c.y
      = algebraMap (AlgebraicClosure ℚ) _ ((ϖ : AlgebraicClosure ℚ) ^ E) * u := by
  have h := congrArg Subtype.val hxy
  simp only [Subring.coe_mul, SubmonoidClass.coe_pow, coe_nodeConst] at h
  rw [map_pow]
  exact h

omit [PerfectField k] in

private theorem valuation_evalAt_eq_one (hvalA : R.ValueIntegralityLaw w)
    {f : ↥(modularFunctionFieldBar (N * q))} (hf0 : f ≠ 0) (hf : f ∈ R.nodeIntegers w) (hfi : f⁻¹ ∈ R.nodeIntegers w)
    (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) (hVw : P.reduceFst V = w) :
    A.valuation (V.evalAt f) = 1 := by
  have hprod : V.evalAt f * V.evalAt f⁻¹ = 1 := by
    rw [← evalAt_mul V (isRational V) (R.mem_toValuationSubring_of_mem_nodeIntegers hf hVw)
      (R.mem_toValuationSubring_of_mem_nodeIntegers hfi hVw), mul_inv_cancel₀ hf0, Place.evalAt_one]
  refine eq_one_of_mul_eq_one ((A.valuation_le_one_iff _).mpr (hvalA f hf V hVw))
    ((A.valuation_le_one_iff _).mpr (hvalA f⁻¹ hfi V hVw)) ?_
  rw [← map_mul, hprod, map_one]

end

end NodeDepthRatio

open NodeDepthRatio in

theorem solution
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    {P : PlaceSpecialization A q N data hKr k red hα hβ}
    (R : ProlongationTuple P) [IsAlgClosed k] [DecidableEq k] (hqN : ¬ q ∣ N)
    (hmodel : R.IsModel)
    (W : Finset (Place k (modularFunctionFieldC k N))) (hW : ∀ w ∈ W, w ∈ ssPlaces q N k)
    (hreg : R.RegularityLaw W) (hval : R.NodeValueLaw W)
    (w : Place k (modularFunctionFieldC k N)) (hw : w ∈ W)
    (hvalA : R.ValueIntegralityLaw w)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    (c : R.NodeCoordinates K w)
    (ϖ : ↥(NodeLocalized.coeffSubring A K))
    (E : ℕ) (u : ↥(R.nodeIntegersOver K w)) (hu : IsUnit u)
    (hxy : c.x * c.y = R.nodeConst K w ϖ ^ E * u)
    (K₀ : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K₀]
    (c₁ : R.NodeCoordinates K₀ w)
    (E₀ : ℕ) (u₀ : ↥(R.nodeIntegersOver K₀ w)) (hu₀ : IsUnit u₀)
    (hxy₁ : c₁.x * c₁.y = R.nodeConst K₀ w ((q : ℕ) : ↥(NodeLocalized.coeffSubring A K₀)) ^ E₀ * u₀)
    (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)))
    (hVw : P.reduceFst V = w) :
    c.xDepth V = c₁.xDepth V ∧ c.yDepth V = c₁.yDepth V := by

  have hE := R.valuation_pow_crossingExponent_eq hqN hmodel W hW hreg hval w hw hvalA K ϖ c E u hu hxy K₀ c₁ E₀
    u₀ hu₀ hxy₁
  have hxyF := NodeDepthRatio.nodeEquation R c ϖ E u hxy
  have hxyF₁ := NodeDepthRatio.nodeEquation R c₁ _ E₀ u₀ hxy₁
  have hui := NodeDepthRatio.inv_mem_nodeIntegers_of_isUnit R hu
  have hu₀i := NodeDepthRatio.inv_mem_nodeIntegers_of_isUnit R hu₀
  have hq0 : (((q : ℕ) : ↥(NodeLocalized.coeffSubring A K₀)) : AlgebraicClosure ℚ) ≠ 0 := by
    have h : ((q : ℕ) : AlgebraicClosure ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : q.Prime).ne_zero
    exact_mod_cast h
  have hva' : A.valuation ((((q : ℕ) : ↥(NodeLocalized.coeffSubring A K₀)) : AlgebraicClosure ℚ) ^ E₀) ≠ 0 := (map_ne_zero _).mpr (pow_ne_zero _ hq0)
  have hvt : A.valuation ((ϖ : AlgebraicClosure ℚ) ^ E / (((q : ℕ) : ↥(NodeLocalized.coeffSubring A K₀)) : AlgebraicClosure ℚ) ^ E₀) = 1 := by
    rw [map_div₀, div_eq_one_iff_eq hva', map_pow, map_pow]
    simpa using hE
  have hva : A.valuation ((ϖ : AlgebraicClosure ℚ) ^ E) ≠ 0 := by
    intro h0; rw [map_div₀, h0, zero_div] at hvt; exact zero_ne_one hvt
  have hvt' : A.valuation ((((q : ℕ) : ↥(NodeLocalized.coeffSubring A K₀)) : AlgebraicClosure ℚ) ^ E₀ / (ϖ : AlgebraicClosure ℚ) ^ E) = 1 := by
    rw [← inv_div, map_inv₀, hvt, inv_one]
  have ht : (ϖ : AlgebraicClosure ℚ) ^ E / (((q : ℕ) : ↥(NodeLocalized.coeffSubring A K₀)) : AlgebraicClosure ℚ) ^ E₀ ∈ A :=
    A.mem_of_valuation_le_one _ hvt.le
  have ht' : (((q : ℕ) : ↥(NodeLocalized.coeffSubring A K₀)) : AlgebraicClosure ℚ) ^ E₀ / (ϖ : AlgebraicClosure ℚ) ^ E ∈ A :=
    A.mem_of_valuation_le_one _ hvt'.le

  have hr := NodeDepthRatio.ratio_x_mem R c c₁ _ _ _ _ (R.nodeIntegersOver_le K w u.2) hu₀i hxyF hxyF₁ ht
  have hr' := NodeDepthRatio.ratio_x_mem R c₁ c _ _ _ _ (R.nodeIntegersOver_le K₀ w u₀.2) hui hxyF₁ hxyF ht'
  have hs := NodeDepthRatio.ratio_y_mem R c c₁ _ _ _ _ (R.nodeIntegersOver_le K w u.2) hu₀i hxyF hxyF₁ ht
  have hs' := NodeDepthRatio.ratio_y_mem R c₁ c _ _ _ _ (R.nodeIntegersOver_le K₀ w u₀.2) hui hxyF₁ hxyF ht'
  have hx0 := NodeDepthRatio.x_ne_zero R c
  have hx₁0 := NodeDepthRatio.x_ne_zero R c₁
  have hy0 := NodeDepthRatio.y_ne_zero R c
  have hy₁0 := NodeDepthRatio.y_ne_zero R c₁
  have hrinv : (((c.x : ↥(R.nodeIntegersOver K w)) : ↥(modularFunctionFieldBar (N * q)))
      * ((c₁.x : ↥(R.nodeIntegersOver K₀ w)) : ↥(modularFunctionFieldBar (N * q)))⁻¹)⁻¹
      = ((c₁.x : ↥(R.nodeIntegersOver K₀ w)) : ↥(modularFunctionFieldBar (N * q)))
        * ((c.x : ↥(R.nodeIntegersOver K w)) : ↥(modularFunctionFieldBar (N * q)))⁻¹ := by
    rw [mul_inv, inv_inv]; exact mul_comm _ _
  have hsinv : (((c.y : ↥(R.nodeIntegersOver K w)) : ↥(modularFunctionFieldBar (N * q)))
      * ((c₁.y : ↥(R.nodeIntegersOver K₀ w)) : ↥(modularFunctionFieldBar (N * q)))⁻¹)⁻¹
      = ((c₁.y : ↥(R.nodeIntegersOver K₀ w)) : ↥(modularFunctionFieldBar (N * q)))
        * ((c.y : ↥(R.nodeIntegersOver K w)) : ↥(modularFunctionFieldBar (N * q)))⁻¹ := by
    rw [mul_inv, inv_inv]; exact mul_comm _ _
  rw [← hrinv] at hr'
  rw [← hsinv] at hs'
  have hratV := isRational V
  constructor
  · show A.valuation (V.evalAt _) = A.valuation (V.evalAt _)
    calc A.valuation (V.evalAt ((c.x : ↥(R.nodeIntegersOver K w)) : ↥(modularFunctionFieldBar (N * q))))
        = A.valuation (V.evalAt ((((c.x : ↥(R.nodeIntegersOver K w)) : ↥(modularFunctionFieldBar (N * q)))
            * ((c₁.x : ↥(R.nodeIntegersOver K₀ w)) : ↥(modularFunctionFieldBar (N * q)))⁻¹)
            * ((c₁.x : ↥(R.nodeIntegersOver K₀ w)) : ↥(modularFunctionFieldBar (N * q))))) := by
          rw [inv_mul_cancel_right₀ hx₁0]
      _ = A.valuation (V.evalAt (((c.x : ↥(R.nodeIntegersOver K w)) : ↥(modularFunctionFieldBar (N * q)))
            * ((c₁.x : ↥(R.nodeIntegersOver K₀ w)) : ↥(modularFunctionFieldBar (N * q)))⁻¹))
            * A.valuation (V.evalAt ((c₁.x : ↥(R.nodeIntegersOver K₀ w)) : ↥(modularFunctionFieldBar (N * q)))) := by
          rw [evalAt_mul V hratV (R.mem_toValuationSubring_of_mem_nodeIntegers hr hVw)
            (R.mem_toValuationSubring_of_mem_nodeIntegers c₁.x.2.1 hVw), map_mul]
      _ = A.valuation (V.evalAt ((c₁.x : ↥(R.nodeIntegersOver K₀ w)) : ↥(modularFunctionFieldBar (N * q)))) := by
          rw [NodeDepthRatio.valuation_evalAt_eq_one R hvalA (mul_ne_zero hx0 (inv_ne_zero hx₁0)) hr hr' V hVw, one_mul]
  · show A.valuation (V.evalAt _) = A.valuation (V.evalAt _)
    calc A.valuation (V.evalAt ((c.y : ↥(R.nodeIntegersOver K w)) : ↥(modularFunctionFieldBar (N * q))))
        = A.valuation (V.evalAt ((((c.y : ↥(R.nodeIntegersOver K w)) : ↥(modularFunctionFieldBar (N * q)))
            * ((c₁.y : ↥(R.nodeIntegersOver K₀ w)) : ↥(modularFunctionFieldBar (N * q)))⁻¹)
            * ((c₁.y : ↥(R.nodeIntegersOver K₀ w)) : ↥(modularFunctionFieldBar (N * q))))) := by
          rw [inv_mul_cancel_right₀ hy₁0]
      _ = A.valuation (V.evalAt (((c.y : ↥(R.nodeIntegersOver K w)) : ↥(modularFunctionFieldBar (N * q)))
            * ((c₁.y : ↥(R.nodeIntegersOver K₀ w)) : ↥(modularFunctionFieldBar (N * q)))⁻¹))
            * A.valuation (V.evalAt ((c₁.y : ↥(R.nodeIntegersOver K₀ w)) : ↥(modularFunctionFieldBar (N * q)))) := by
          rw [evalAt_mul V hratV (R.mem_toValuationSubring_of_mem_nodeIntegers hs hVw)
            (R.mem_toValuationSubring_of_mem_nodeIntegers c₁.y.2.1 hVw), map_mul]
      _ = A.valuation (V.evalAt ((c₁.y : ↥(R.nodeIntegersOver K₀ w)) : ↥(modularFunctionFieldBar (N * q)))) := by
          rw [NodeDepthRatio.valuation_evalAt_eq_one R hvalA (mul_ne_zero hy0 (inv_ne_zero hy₁0)) hs hs' V hVw, one_mul]

end S_ModularCurve_PlaceSpecialization_ProlongationTuple_xDepth_eq_and_yDepth_eq_of_nodeCoordinates
end P2MW
export P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_xDepth_eq_and_yDepth_eq_of_nodeCoordinates (solution)
