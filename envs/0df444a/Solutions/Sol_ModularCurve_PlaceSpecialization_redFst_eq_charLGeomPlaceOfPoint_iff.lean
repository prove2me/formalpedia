-- Prove2me | solution 1 for ModularCurve.PlaceSpecialization.redFst_eq_charLGeomPlaceOfPoint_iff
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/43b30a94-46e4-579c-8f89-25ad28581735

import Mathlib
import Definitions.Def_ModularCurve_LevelOneProlongationPair
import Definitions.Def_ModularCurve_SpecializeModuli
import Definitions.Def_AlgebraicCurve_RatFuncPlaces
import Definitions.Def_AlgebraicCurve_RatFuncPlaceInfty
import Theorems.Thm_ModularCurve_PlaceSpecialization_redFst_eq_charLGeomPlaceOfPoint_of_ord_pos
import Theorems.Thm_ModularCurve_PlaceSpecialization_redFst_eq_placeInfty_of_forall_ord_le_zero
import Theorems.Thm_ModularCurve_coeffMap_qExpand
import Theorems.Thm_ModularCurve_laurentBaseChange_adjoin
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_PlaceSpecialization_redFst_eq_charLGeomPlaceOfPoint_iff
p2m_attr_erase "instance" "AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

section InstanceShortcuts
p2m_open "ModularCurve P2MW.S_ModularCurve_PlaceSpecialization_redFst_eq_charLGeomPlaceOfPoint_iff.ModularCurve"

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
p2m_open "Polynomial AlgebraicCurve AlgebraicCurve.RationalFunctionField~placeOfPoint_ne_placeInfty"

namespace GaussPencil
namespace B14

theorem mapDomain_apply_eq_sum_filter {α β M : Type*} [AddCommMonoid M] [DecidableEq β]
    (f : α → β) (D : α →₀ M) (b : β) :
    Finsupp.mapDomain f D b = ((D.support.filter fun a => f a = b).sum fun a => D a) := by
  classical
  rw [Finsupp.mapDomain, Finsupp.sum_apply, Finset.sum_filter]
  refine Finset.sum_congr rfl fun a _ => ?_
  by_cases h : f a = b <;> simp [Finsupp.single_apply, h]

theorem placeOfPoint_ne_placeInfty (K : Type*) [Field K] [DecidableEq (RatFunc K)] (a : K) :
    placeOfPoint K a ≠ placeInfty K := by
  intro h
  have hX : (RatFunc.X : RatFunc K) ∈ (placeOfPoint K a).toValuationSubring := by
    rw [placeOfPoint_eq_ofHeightOneSpectrum]
    have := algebraMap_mem_ofHeightOneSpectrum K
      (heightOneSpectrumOfIrreducible K (Polynomial.irreducible_X_sub_C a)) Polynomial.X
    rwa [RatFunc.algebraMap_X] at this
  rw [h, placeInfty_toValuationSubring, Valuation.mem_valuationSubring_iff,
    RatFunc.inftyValuation.X, ← WithZero.exp_zero, WithZero.exp_le_exp] at hX
  norm_num at hX

end GaussPencil.B14

end

p2m_open "AlgebraicCurve IsLocalRing ModularCurve P2MW.S_ModularCurve_PlaceSpecialization_redFst_eq_charLGeomPlaceOfPoint_iff.ModularCurve"

namespace ModularCurve
p2m_export "ModularCurve" "PlaceSpecialization.LevelOneProlongationPair PlaceSpecialization.jFun modularFunctionFieldBar qExpand qExpand_one_apply qExpand_congr jq ModularPolynomialData jq_mem divisorExpansions modularFunctionField_le_full coeffEmb laurentBaseChange coeffEmb_mem_laurentBaseChange modularFunctionFieldC PlaceSpecialization heckeAlphaBar coe_heckeAlphaBar heckeBetaBar coe_heckeBetaBar HeckeAlphaBarIntegral HeckeBetaBarIntegral KroneckerCongruence charLGeomPlaceEquiv charLGeomPlaceOfPoint charLGeomPlaceOfPoint_injective modularFunctionFieldFullC coeffMap_qExpand laurentBaseChange_adjoin PlaceSpecialization.redFst_eq_charLGeomPlaceOfPoint_iff_impl"
namespace PlaceSpecialization
p2m_export "ModularCurve.PlaceSpecialization" "LevelOneProlongationPair jFun jqFun redFst redFst_eq_charLGeomPlaceOfPoint_of_ord_pos redFst_eq_placeInfty_of_forall_ord_le_zero redFst_eq_charLGeomPlaceOfPoint_iff_impl"
namespace LevelOneProlongationPair
p2m_open "ModularCurve.PlaceSpecialization.LevelOneProlongationPair ModularCurve.PlaceSpecialization ModularCurve"

section InstanceJ

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
  {k : Type*} [Field k] [CharP k q] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
  {P : PlaceSpecialization A q 1 data hKr k red hα hβ}

@[reducible] noncomputable def algAlongAlpha (q : ℕ) [Fact q.Prime] :
    Algebra (modularFunctionFieldBar 1) (modularFunctionFieldBar (1 * q)) :=
  algebraAlong (heckeAlphaBar (AlgebraicClosure ℚ) 1 q)

attribute [local instance] algAlongAlpha

theorem algebraMap_levelOne_apply (x : modularFunctionFieldBar 1) :
    algebraMap (modularFunctionFieldBar 1) (modularFunctionFieldBar (1 * q)) x
      = heckeAlphaBar (AlgebraicClosure ℚ) 1 q x := rfl

theorem isScalarTower_levelOne :
    IsScalarTower (AlgebraicClosure ℚ) (modularFunctionFieldBar 1) (modularFunctionFieldBar (1 * q)) :=
  isScalarTower_along (heckeAlphaBar (AlgebraicClosure ℚ) 1 q)

attribute [local instance] isScalarTower_levelOne

noncomputable def jOne : modularFunctionFieldBar 1 :=
  ⟨coeffEmb (AlgebraicClosure ℚ) jq,
    coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full 1 (jq_mem 1))⟩

theorem algebraMap_jOne :
    algebraMap (modularFunctionFieldBar 1) (modularFunctionFieldBar (1 * q)) jOne = jFun (q := q) :=
  Subtype.ext (coe_heckeAlphaBar 1 q _)

theorem heckeBetaBar_jOne :
    heckeBetaBar (AlgebraicClosure ℚ) 1 q jOne = jqFun (q := q) := by
  apply Subtype.ext
  rw [coe_heckeBetaBar]
  show qExpand (AlgebraicClosure ℚ) q (coeffEmb (AlgebraicClosure ℚ) jq)
    = coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (1 * q) jq)
  rw [coeffEmb, coeffMap_qExpand]
  exact qExpand_congr (one_mul q).symm _

theorem mem_adjoin_jOne (x : modularFunctionFieldBar 1) :
    x ∈ IntermediateField.adjoin (AlgebraicClosure ℚ) ({jOne} : Set (modularFunctionFieldBar 1)) := by
  have hS : (⇑(coeffEmb (AlgebraicClosure ℚ)) '' (divisorExpansions 1 : Set (LaurentSeries ℚ)))
      = {coeffEmb (AlgebraicClosure ℚ) jq} := by
    ext y
    simp only [Set.mem_singleton_iff, Set.mem_image]
    constructor
    · rintro ⟨z, ⟨d, _, hd, rfl⟩, rfl⟩
      obtain rfl : d = 1 := Nat.dvd_one.mp hd
      rw [qExpand_one_apply]
    · rintro rfl
      exact ⟨jq, ⟨1, inferInstance, dvd_refl 1, (qExpand_one_apply jq).symm⟩, rfl⟩
  have hx : (x : LaurentSeries (AlgebraicClosure ℚ)) ∈
      IntermediateField.adjoin (AlgebraicClosure ℚ) {coeffEmb (AlgebraicClosure ℚ) jq} := by
    have h := x.2
    change (x : LaurentSeries (AlgebraicClosure ℚ)) ∈
      laurentBaseChange (AlgebraicClosure ℚ) (IntermediateField.adjoin ℚ (divisorExpansions 1)) at h
    rwa [laurentBaseChange_adjoin, hS] at h
  rw [IntermediateField.mem_adjoin_simple_iff] at hx ⊢
  obtain ⟨r, s, hrs⟩ := hx
  refine ⟨r, s, Subtype.ext ?_⟩
  have hval : ∀ p : Polynomial (AlgebraicClosure ℚ),
      Polynomial.aeval (coeffEmb (AlgebraicClosure ℚ) jq) p
        = ((Polynomial.aeval (jOne : modularFunctionFieldBar 1) p : modularFunctionFieldBar 1) :
            LaurentSeries (AlgebraicClosure ℚ)) := fun p =>
    Polynomial.aeval_algHom_apply (IntermediateField.val (modularFunctionFieldBar 1)) jOne p
  rw [hrs, hval r, hval s]
  exact (map_div₀ (IntermediateField.val (modularFunctionFieldBar 1)) _ _).symm

end InstanceJ

section PhaseB0

p2m_open "Polynomial AlgebraicCurve.RationalFunctionField~placeOfPoint_ne_placeInfty"

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
  {k : Type*} [Field k] [CharP k q] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
  {P : PlaceSpecialization A q 1 data hKr k red hα hβ}

attribute [local instance] algAlongAlpha isScalarTower_levelOne

private theorem _root_.ModularCurve.PlaceSpecialization.redFst_eq_charLGeomPlaceOfPoint_iff_impl
    (P : PlaceSpecialization A q 1 data hKr k red hα hβ)
    (W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))) (c₀ : k) :
    P.redFst W = charLGeomPlaceOfPoint k c₀ ↔ ∃ a : A, red a = c₀ ∧
      0 < W.ord (jFun (q := q) - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (a : AlgebraicClosure ℚ)) := by
  classical
  constructor
  · intro h
    by_cases hex : ∃ a : A, 0 < W.ord (jFun (q := q)
        - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (a : AlgebraicClosure ℚ))
    · obtain ⟨a, ha⟩ := hex
      refine ⟨a, ?_, ha⟩
      have h' := P.redFst_eq_charLGeomPlaceOfPoint_of_ord_pos W a (by rw [← algebraMap_jOne] at ha; exact ha)
      rw [h] at h'
      exact (charLGeomPlaceOfPoint_injective k h').symm
    · have hex' : ∀ a : A, W.ord (jFun (q := q)
          - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (a : AlgebraicClosure ℚ)) ≤ 0 :=
        fun a => not_lt.mp fun hlt => hex ⟨a, hlt⟩
      have h' := P.redFst_eq_placeInfty_of_forall_ord_le_zero W hex'
      rw [h] at h'
      exact absurd ((charLGeomPlaceEquiv k).injective h')
        (GaussPencil.B14.placeOfPoint_ne_placeInfty k c₀)
  · rintro ⟨a, rfl, ha⟩
    exact P.redFst_eq_charLGeomPlaceOfPoint_of_ord_pos W a (by rw [← algebraMap_jOne] at ha; exact ha)

p2m_alias "P2MW.S_ModularCurve_PlaceSpecialization_redFst_eq_charLGeomPlaceOfPoint_iff.ModularCurve.PlaceSpecialization.redFst_eq_charLGeomPlaceOfPoint_iff_impl" "ModularCurve.PlaceSpecialization.redFst_eq_charLGeomPlaceOfPoint_iff_impl"
end PhaseB0

end ModularCurve.PlaceSpecialization.LevelOneProlongationPair

theorem solution
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
    (P : PlaceSpecialization A q 1 data hKr k red hα hβ)
    (W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))) (c₀ : k) :
    P.redFst W = charLGeomPlaceOfPoint k c₀ ↔ ∃ a : A, red a = c₀ ∧
      0 < W.ord (PlaceSpecialization.jFun (q := q)
        - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (a : AlgebraicClosure ℚ)) :=
  ModularCurve.PlaceSpecialization.redFst_eq_charLGeomPlaceOfPoint_iff_impl P W c₀

end S_ModularCurve_PlaceSpecialization_redFst_eq_charLGeomPlaceOfPoint_iff
end P2MW
export P2MW.S_ModularCurve_PlaceSpecialization_redFst_eq_charLGeomPlaceOfPoint_iff (solution)
