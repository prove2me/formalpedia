-- Prove2me | solution 1 for ModularCurve.PlaceSpecialization.LevelOneProlongationPair.sum_ord_pencil_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/9c5da3d8-59a5-5edf-b610-a561c5292d8f

import Mathlib
import Definitions.Def_ModularCurve_LevelOneProlongationPair
import Definitions.Def_ModularCurve_SpecializeModuli
import Theorems.Thm_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_sum_filter_value_eq_ord_add_sum_roots
import Theorems.Thm_ModularCurve_PlaceSpecialization_exists_ord_jqFun_sub_pos_of_ord_jFun_sub_pos
import Theorems.Thm_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_sum_filter_value_eq_sum_roots_add_pencil
import Theorems.Thm_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_exists_ord_jFun_sub_pos_of_ord_jFun_add_mul_jqFun_sub_pos
import Theorems.Thm_ModularCurve_PlaceSpecialization_jFun_add_C_mul_jqFun_sub_algebraMap_ne_zero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_sum_ord_pencil_eq
p2m_attr_erase "instance" "instFieldLaurentSeriesAlgClosureRat instAlgebraModularFunctionFieldBar ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instAlgebraResidueFieldSubtypeMemValuationSubringGaussBaseResOne ModularCurve.PlaceSpecialization.LevelOneProlongationPair.algGaussBase instAlgebraModularFunctionFieldFullC ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instAlgebraSubtypeMemValuationSubringGaussBaseResOne ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instAlgebraSubtypeMemValuationSubringGaussBaseResTwo instFieldModularFunctionFieldC ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isScalarTower_resOne instFieldLaurentSeries' ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isScalarTower_resTwo instModuleModularFunctionFieldBar ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isLocalHom_resBase₁ instAlgebraModularFunctionFieldC ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isLocalHom_constToGaussBase ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instFieldResOne instFieldModularFunctionFieldBar ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instAlgebraResidueFieldSubtypeMemValuationSubringGaussBaseResTwo ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instFieldResTwo instFieldModularFunctionFieldFullC ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isScalarTower_gaussBase instAlgebraLaurentSeriesAlgClosureRat ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isLocalHom_resBase₂ ModularCurve.PlaceSpecialization.LevelOneProlongationPair.algResidueConst instCommRingModularFunctionFieldBar ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "ModularCurve.PlaceSpecialization.LevelOneProlongationPair.coe_gaussOrderToIntegers₂ ModularCurve.PlaceSpecialization.LevelOneProlongationPair.coe_gaussOrderToIntegers₁ ModularCurve.PlaceSpecialization.LevelOneProlongationPair.coe_toIntegers₁ ModularCurve.PlaceSpecialization.LevelOneProlongationPair.coe_constToGaussBase ModularCurve.PlaceSpecialization.LevelOneProlongationPair.coe_toIntegers₂ ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ"
p2m_attr_erase "simp" "HahnSeries.ramScale_apply AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

section InstanceShortcuts
p2m_open "ModularCurve P2MW.S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_sum_ord_pencil_eq.ModularCurve"

noncomputable scoped instance (priority := high) instFieldLaurentSeriesAlgClosureRatLocal :
    Field (LaurentSeries (AlgebraicClosure ℚ)) := inferInstance
noncomputable scoped instance (priority := high) instAlgebraLaurentSeriesAlgClosureRatLocal :
    Algebra (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) := inferInstance
noncomputable scoped instance (priority := high) instFieldModularFunctionFieldBarLocal (N : ℕ) :
    Field ↥(modularFunctionFieldBar N) := inferInstance
noncomputable scoped instance (priority := high) instAlgebraModularFunctionFieldBarLocal (N : ℕ) :
    Algebra (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N) := inferInstance
noncomputable scoped instance (priority := high) instModuleModularFunctionFieldBarLocal (N : ℕ) :
    Module (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N) := inferInstance
noncomputable scoped instance (priority := high) instCommRingModularFunctionFieldBarLocal (N : ℕ) :
    CommRing ↥(modularFunctionFieldBar N) := inferInstance
noncomputable scoped instance (priority := high) instFieldModularFunctionFieldCLocal (k : Type*) [Field k] (N : ℕ) [NeZero N] :
    Field ↥(modularFunctionFieldC k N) := inferInstance
noncomputable scoped instance (priority := high) instAlgebraModularFunctionFieldCLocal (k : Type*) [Field k] (N : ℕ) [NeZero N] :
    Algebra k ↥(modularFunctionFieldC k N) := inferInstance
noncomputable scoped instance (priority := high) instFieldModularFunctionFieldFullCLocal (k : Type*) [Field k] (N : ℕ) [NeZero N] :
    Field ↥(modularFunctionFieldFullC k N) := inferInstance
noncomputable scoped instance (priority := high) instAlgebraModularFunctionFieldFullCLocal (k : Type*) [Field k] (N : ℕ) [NeZero N] :
    Algebra k ↥(modularFunctionFieldFullC k N) := inferInstance
noncomputable scoped instance (priority := high) instFieldLaurentSeriesLocal' (k : Type*) [Field k] :
    Field (LaurentSeries k) := inferInstance

end InstanceShortcuts

section
open AlgebraicCurve

set_option autoImplicit false

namespace GaussPencil
namespace B6

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)

theorem min_ord_le_ord_add {f g : F} (hf : f ≠ 0) (hg : g ≠ 0) (hfg : f + g ≠ 0) :
    min (v.ord f) (v.ord g) ≤ v.ord (f + g) := by
  have h := Valuation.map_add (v.adicValuation) f g
  change min (-(WithZero.log (v.adicValuation f))) (-(WithZero.log (v.adicValuation g)))
    ≤ -(WithZero.log (v.adicValuation (f + g)))
  rcases le_max_iff.mp h with h' | h'
  · have h2 := (WithZero.log_le_log (v.adicValuation_ne_zero hfg) (v.adicValuation_ne_zero hf)).mpr h'
    exact (min_le_left _ _).trans (neg_le_neg h2)
  · have h2 := (WithZero.log_le_log (v.adicValuation_ne_zero hfg) (v.adicValuation_ne_zero hg)).mpr h'
    exact (min_le_right _ _).trans (neg_le_neg h2)

theorem ord_add_pos {f g : F} (hf : 0 < v.ord f) (hg : 0 < v.ord g) (hfg : f + g ≠ 0) : 0 < v.ord (f + g) := by
  have hf0 : f ≠ 0 := by rintro rfl; rw [Place.ord_zero] at hf; exact lt_irrefl 0 hf
  have hg0 : g ≠ 0 := by rintro rfl; rw [Place.ord_zero] at hg; exact lt_irrefl 0 hg
  exact lt_of_lt_of_le (lt_min hf hg) (min_ord_le_ord_add v hf0 hg0 hfg)

theorem ord_neg' (f : F) : v.ord (-f) = v.ord f := by
  change -(WithZero.log (v.adicValuation (-f))) = -(WithZero.log (v.adicValuation f))
  rw [Valuation.map_neg]

theorem ord_algebraMap_eq_zero {c : K} (hc : c ≠ 0) : v.ord (algebraMap K F c) = 0 := by
  have hu : IsUnit (⟨algebraMap K F c, v.algebraMap_mem' c⟩ : v.toValuationSubring) :=
    isUnit_iff_exists_inv.mpr ⟨⟨algebraMap K F c⁻¹, v.algebraMap_mem' _⟩, Subtype.ext (by
      show algebraMap K F c * algebraMap K F c⁻¹ = 1
      rw [← map_mul, mul_inv_cancel₀ hc, map_one])⟩
  obtain ⟨u, hu⟩ := hu
  have h := v.ord_coe_unit u
  rwa [hu] at h

theorem algebraMap_eq_of_ord_sub_pos (g : F) {a a' : K} (h : 0 < v.ord (g - algebraMap K F a))
    (h' : 0 < v.ord (g - algebraMap K F a')) : a = a' := by
  by_contra hne
  have hd : algebraMap K F (a' - a) ≠ 0 :=
    (_root_.map_ne_zero _).mpr (sub_ne_zero.mpr (Ne.symm hne))
  have heq : (g - algebraMap K F a) + (-(g - algebraMap K F a')) = algebraMap K F (a' - a) := by
    rw [map_sub]; ring
  have hpos := ord_add_pos v h (by rw [ord_neg']; exact h') (by rw [heq]; exact hd)
  rw [heq, ord_algebraMap_eq_zero v (sub_ne_zero.mpr (Ne.symm hne))] at hpos
  exact lt_irrefl 0 hpos

theorem ord_const_mul_pos {c : K} (hc : c ≠ 0) {f : F} (hf : 0 < v.ord f) : 0 < v.ord (algebraMap K F c * f) := by
  have hf0 : f ≠ 0 := by rintro rfl; rw [Place.ord_zero] at hf; exact lt_irrefl 0 hf
  rw [v.ord_mul ((_root_.map_ne_zero _).mpr hc) hf0, ord_algebraMap_eq_zero v hc, zero_add]
  exact hf

end GaussPencil.B6

end

p2m_open "AlgebraicCurve IsLocalRing ModularCurve P2MW.S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_sum_ord_pencil_eq.ModularCurve"

namespace ModularCurve
p2m_export "ModularCurve" "PlaceSpecialization.LevelOneProlongationPair modularFunctionFieldBar ModularPolynomialData modularFunctionFieldC PlaceSpecialization HeckeAlphaBarIntegral HeckeBetaBarIntegral KroneckerCongruence charLGeomPlaceOfPoint modularFunctionFieldFullC PlaceSpecialization.jFun_add_C_mul_jqFun_sub_algebraMap_ne_zero"
namespace PlaceSpecialization
p2m_export "ModularCurve.PlaceSpecialization" "LevelOneProlongationPair jFun jqFun exists_ord_jqFun_sub_pos_of_ord_jFun_sub_pos jFun_add_C_mul_jqFun_sub_algebraMap_ne_zero"
namespace LevelOneProlongationPair
p2m_export "ModularCurve.PlaceSpecialization.LevelOneProlongationPair" "residue₁ residue₂ R₂ R₁ sum_filter_value_eq_ord_add_sum_roots sum_filter_value_eq_sum_roots_add_pencil exists_ord_jFun_sub_pos_of_ord_jFun_add_mul_jqFun_sub_pos"
p2m_open "ModularCurve.PlaceSpecialization.LevelOneProlongationPair ModularCurve.PlaceSpecialization ModularCurve"

section Final

open Polynomial AlgebraicCurve.RationalFunctionField

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
  {k : Type*} [Field k] [CharP k q] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
  {P : PlaceSpecialization A q 1 data hKr k red hα hβ}

variable (R : LevelOneProlongationPair P)

theorem pencil_sub_algebraMap (μ x y : A) :
    jFun (q := q)
        + algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (μ : AlgebraicClosure ℚ) * jqFun (q := q)
        - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) ((x + μ * y : A) : AlgebraicClosure ℚ)
      = (jFun (q := q) - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (x : AlgebraicClosure ℚ))
        + algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (μ : AlgebraicClosure ℚ)
          * (jqFun (q := q) - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (y : AlgebraicClosure ℚ)) := by
  rw [show ((x + μ * y : A) : AlgebraicClosure ℚ) = (x : AlgebraicClosure ℚ) + (μ : AlgebraicClosure ℚ) * (y : AlgebraicClosure ℚ)
      from rfl, map_add, map_mul]
  ring

open Classical in

private theorem _root_.ModularCurve.PlaceSpecialization.LevelOneProlongationPair.sum_ord_pencil_eq_impl [DecidableEq k]
    (f : modularFunctionFieldBar (1 * q)) (h₁ : f ∈ R.R₁.integers) (h₂ : f ∈ R.R₂.integers)
    (hu₁ : R.R₁.residue ⟨f, h₁⟩ ≠ 0) (hu₂ : R.R₂.residue ⟨f, h₂⟩ ≠ 0)
    (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))) (hD : ∀ W, D W = W.ord f)
    (μ : A) (hμ : red μ ≠ 0 ∨ μ = 0) (c : k) :
    (D.support.filter fun W => ∃ x y : A, red x + red μ * red y = c ∧
        0 < W.ord (jFun (q := q) - algebraMap _ _ (x : AlgebraicClosure ℚ)) ∧
        0 < W.ord (jqFun (q := q) - algebraMap _ _ (y : AlgebraicClosure ℚ))).sum D
    = ((Polynomial.C (red μ) * Polynomial.X ^ q + Polynomial.X - Polynomial.C c).roots.toFinset.sum
          fun a => (charLGeomPlaceOfPoint k a).ord (R.residue₁ ⟨f, h₁⟩))
      + ((Polynomial.X ^ q + Polynomial.C (red μ) * Polynomial.X - Polynomial.C c).roots.toFinset.sum
          fun b => (charLGeomPlaceOfPoint k b).ord (R.residue₂ ⟨f, h₂⟩)) := by
  classical
  rcases hμ with hμ | rfl
  ·
    have hμ0 : (μ : AlgebraicClosure ℚ) ≠ 0 := by
      intro h
      apply hμ
      have : μ = 0 := Subtype.ext h
      rw [this, map_zero]
    rw [← R.sum_filter_value_eq_sum_roots_add_pencil μ hμ f h₁ h₂ hu₁ hu₂ D hD c]
    refine Finset.sum_congr (Finset.filter_congr fun W hW => ⟨?_, ?_⟩) fun _ _ => rfl
    · rintro ⟨x, y, hxy, hx, hy⟩
      refine ⟨x + μ * y, by rw [map_add, map_mul, hxy], ?_⟩
      rw [pencil_sub_algebraMap]
      refine GaussPencil.B6.ord_add_pos W hx (GaussPencil.B6.ord_const_mul_pos W hμ0 hy) ?_
      rw [← pencil_sub_algebraMap]
      exact ModularCurve.PlaceSpecialization.jFun_add_C_mul_jqFun_sub_algebraMap_ne_zero _ _
    · rintro ⟨a, ha, hga⟩
      obtain ⟨x, hx⟩ := R.exists_ord_jFun_sub_pos_of_ord_jFun_add_mul_jqFun_sub_pos μ hμ W a hga
      obtain ⟨y, hy⟩ := P.exists_ord_jqFun_sub_pos_of_ord_jFun_sub_pos W x hx
      refine ⟨x, y, ?_, hx, hy⟩
      have hsum : 0 < W.ord (jFun (q := q)
          + algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (μ : AlgebraicClosure ℚ) * jqFun (q := q)
          - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) ((x + μ * y : A) : AlgebraicClosure ℚ)) := by
        rw [pencil_sub_algebraMap]
        refine GaussPencil.B6.ord_add_pos W hx (GaussPencil.B6.ord_const_mul_pos W hμ0 hy) ?_
        rw [← pencil_sub_algebraMap]
        exact ModularCurve.PlaceSpecialization.jFun_add_C_mul_jqFun_sub_algebraMap_ne_zero _ _
      have hax : (a : AlgebraicClosure ℚ) = ((x + μ * y : A) : AlgebraicClosure ℚ) :=
        GaussPencil.B6.algebraMap_eq_of_ord_sub_pos W _ hga hsum
      rw [← ha, show a = x + μ * y from Subtype.ext hax, map_add, map_mul]
  ·
    have hr₁ : (C (red (0 : A)) * X ^ q + X - C c : k[X]) = X - C c := by
      rw [map_zero, map_zero, zero_mul, zero_add]
    have hr₂ : (X ^ q + C (red (0 : A)) * X - C c : k[X]) = X ^ q - C c := by
      rw [map_zero, map_zero, zero_mul, add_zero]
    rw [hr₁, hr₂, ← R.sum_filter_value_eq_ord_add_sum_roots f h₁ h₂ hu₁ hu₂ D hD c]
    refine Finset.sum_congr (Finset.filter_congr fun W _ => ⟨?_, ?_⟩) fun _ _ => rfl
    · rintro ⟨x, y, hxy, hx, -⟩
      refine ⟨x, ?_, hx⟩
      rw [map_zero, zero_mul, add_zero] at hxy
      exact hxy
    · rintro ⟨a, ha, hja⟩
      obtain ⟨y, hy⟩ := P.exists_ord_jqFun_sub_pos_of_ord_jFun_sub_pos W a hja
      exact ⟨a, y, by rw [map_zero, zero_mul, add_zero]; exact ha, hja, hy⟩

p2m_export "ModularCurve.PlaceSpecialization.LevelOneProlongationPair" "sum_ord_pencil_eq_impl"
end Final

end ModularCurve.PlaceSpecialization.LevelOneProlongationPair

open _root_.ModularCurve.PlaceSpecialization _root_.P2MW.S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_sum_ord_pencil_eq.ModularCurve.PlaceSpecialization in
open Classical in
theorem solution
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] [DecidableEq k] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
    {P : PlaceSpecialization A q 1 data hKr k red hα hβ} (R : P.LevelOneProlongationPair)
    (f : modularFunctionFieldBar (1 * q)) (h₁ : f ∈ R.R₁.integers) (h₂ : f ∈ R.R₂.integers)
    (hu₁ : R.R₁.residue ⟨f, h₁⟩ ≠ 0) (hu₂ : R.R₂.residue ⟨f, h₂⟩ ≠ 0)
    (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))) (hD : ∀ W, D W = W.ord f)
    (μ : A) (hμ : red μ ≠ 0 ∨ μ = 0) (c : k) :
    (D.support.filter fun W => ∃ x y : A, red x + red μ * red y = c ∧
        0 < W.ord (jFun (q := q) - algebraMap _ _ (x : AlgebraicClosure ℚ)) ∧
        0 < W.ord (jqFun (q := q) - algebraMap _ _ (y : AlgebraicClosure ℚ))).sum D
    = ((Polynomial.C (red μ) * Polynomial.X ^ q + Polynomial.X - Polynomial.C c).roots.toFinset.sum
          fun a => (charLGeomPlaceOfPoint k a).ord (R.residue₁ ⟨f, h₁⟩))
      + ((Polynomial.X ^ q + Polynomial.C (red μ) * Polynomial.X - Polynomial.C c).roots.toFinset.sum
          fun b => (charLGeomPlaceOfPoint k b).ord (R.residue₂ ⟨f, h₂⟩)) :=
  R.sum_ord_pencil_eq_impl f h₁ h₂ hu₁ hu₂ D hD μ hμ c

end S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_sum_ord_pencil_eq
end P2MW
export P2MW.S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_sum_ord_pencil_eq (solution)
