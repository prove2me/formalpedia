-- Prove2me | solution 1 for ModularCurve.exists_leadingCoeff_eq_mul_pow_of_aeval_jFull_eq_norm_aeval_modularUnitSeries
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/81b14d29-69cf-555f-b2c4-0e7ae8ec8e5f

import Mathlib
import Definitions.Def_ModularCurve_ModularUnit
import Definitions.Def_ModularCurve_IgusaScheme
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_CuspidalClass
import Definitions.Def_ModularCurve_JLinePlacesBar
import Definitions.Def_ModularCurve_GeometricBaseChange
import Definitions.Def_AlgebraicCurve_PlacesOverDVR
import Definitions.Def_AlgebraicCurve_DivisorPushPull
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import Definitions.Def_AlgebraicCurve_PlaceEvaluationAlgebra
import Theorems.Thm_ModularCurve_isCusp_cuspInftyBar
import Theorems.Thm_ModularCurve_isCusp_cuspZeroBar
import Theorems.Thm_ModularCurve_ord_cuspInftyBar_coeffEmb_jq
import Theorems.Thm_ModularCurve_ord_cuspInftyBar
import Theorems.Thm_ModularCurve_finiteDimensional_adjoin_coeffEmb_jq_of_neZero
import Theorems.Thm_ModularCurve_eq_cuspInftyBar_or_eq_cuspZeroBar
import Theorems.Thm_ModularCurve_ord_cuspInftyBar_coeffEmb_modularUnitSeries
import Theorems.Thm_ModularCurve_ord_cuspZeroBar_coeffEmb_modularUnitSeries
import Theorems.Thm_ModularCurve_isFrickeAutFull_frickeInvolutionFull_prime
import Theorems.Thm_ModularCurve_isCurveOver_modularFunctionFieldBar
import Theorems.Thm_AlgebraicCurve_Place_ord_norm_eq_sum_fiberOver
import Theorems.Thm_AlgebraicCurve_RationalFunctionField_eq_placeInfty_of_ord_X_neg
import Theorems.Thm_ModularCurve_finrank_adjoin_jqModC_modularFunctionFieldFullC_eq_dedekindPsi
import Theorems.Thm_AlgebraicCurve_Place_inertiaDeg_eq_one_of_isRational
import Theorems.Thm_AlgebraicCurve_Place_isRational_iff_deg_eq_one
import Theorems.Thm_AlgebraicCurve_Place_ord_algebraMap
import Theorems.Thm_AlgebraicCurve_Place_ord_add_eq_of_lt
import Theorems.Thm_AlgebraicCurve_Place_evalAt_norm_eq_prod_fiber
import Theorems.Thm_AlgebraicCurve_Place_sum_ramificationIndex_mul_inertiaDeg_fiberOver
import Theorems.Thm_ModularCurve_frickeInvolutionBar_coeffEmb_modularUnitSeries
import Theorems.Thm_ModularCurve_frickeInvolutionFull_apply_apply
import Theorems.Thm_ModularCurve_natDegree_eq_mul_of_aeval_jFull_eq_norm_aeval_modularUnitSeries
import Theorems.Thm_ModularCurve_coe_frickeInvolutionFull_modularUnitSeries
import Theorems.Thm_ModularCurve_modularUnitSeries_mem_chartAlgFin_int
import Theorems.Thm_ModularCurve_exists_aeval_jFull_eq_norm_of_mem_chartAlgFin
import Definitions.Def_ModularCurve_X0ModL
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_leadingCoeff_eq_mul_pow_of_aeval_jFull_eq_norm_aeval_modularUnitSeries
p2m_attr_erase "instance" "AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.toRingAut_coeffSemilinearAut ModularCurve.baseAut_arithFrobC_apply ModularCurve.coe_coeffRingAut_apply ModularCurve.baseAut_coeffSemilinearAut ModularCurve.coe_jGeomGen ModularCurve.coe_jNGeomGen ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring ModularCurve.charLGeomModuliDictionary_single ModularCurve.specializeModuli_single ModularCurve.specializePlace_def ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord"

set_option autoImplicit false

p2m_open "ModularCurve~dedekindPsi_prime~order_coeffEmb Polynomial AlgebraicCurve IntermediateField"

noncomputable section

namespace CU2i
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

set_option quotPrecheck false
local notation "ℚb" => AlgebraicClosure ℚ
local notation "FF" p => ↥(ModularCurve.modularFunctionFieldFull p)
local notation "FB" p => ↥(ModularCurve.modularFunctionFieldBar p)
local notation "jB" p => (⟨coeffEmb (AlgebraicClosure ℚ) jq, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jq_mem_full p)⟩ : ↥(ModularCurve.modularFunctionFieldBar p))
local notation "EF" p => IntermediateField.adjoin ℚ ({IgusaScheme.jFull p} : Set ↥(ModularCurve.modularFunctionFieldFull p))
local notation "EB" p => ModularCurve.jLineBar p

variable (p : ℕ) [Fact p.Prime]

def ι : (FF p) →+* (FB p) where
  toFun x := ⟨coeffEmb (AlgebraicClosure ℚ) (x : LaurentSeries ℚ),
    coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) x.2⟩
  map_one' := by apply Subtype.ext; simp
  map_mul' x y := by apply Subtype.ext; simp
  map_zero' := by apply Subtype.ext; simp
  map_add' x y := by apply Subtype.ext; simp

@[scoped simp] theorem coe_ι (x : FF p) :
    ((ι p x : FB p) : LaurentSeries (AlgebraicClosure ℚ)) = coeffEmb (AlgebraicClosure ℚ) x := rfl

theorem ι_injective : Function.Injective (ι p) := (ι p).injective

theorem ι_jF : ι p (IgusaScheme.jFull p) = jB p := by
  apply Subtype.ext; simp [IgusaScheme.coe_jFull]

theorem ι_ratCast (c : ℚ) :
    ι p (c : FF p) = algebraMap (AlgebraicClosure ℚ) (FB p) (c : AlgebraicClosure ℚ) := by
  rw [map_ratCast, map_ratCast]

theorem ι_mem_EB (x : FF p) (hx : x ∈ EF p) : ι p x ∈ EB p := by

  induction hx using IntermediateField.adjoin_induction with
  | mem y hy =>
      rw [Set.mem_singleton_iff] at hy; subst hy
      rw [ι_jF]; exact IntermediateField.mem_adjoin_simple_self _ _
  | algebraMap c =>
      rw [eq_ratCast, ι_ratCast]; exact IntermediateField.algebraMap_mem _ _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy
  | inv x _ hx => rw [map_inv₀]; exact inv_mem hx

def ιE : ↥(EF p) →+* ↥(EB p) where
  toFun x := ⟨ι p x, ι_mem_EB p x x.2⟩
  map_one' := by apply Subtype.ext; simp
  map_mul' x y := by apply Subtype.ext; simp
  map_zero' := by apply Subtype.ext; simp
  map_add' x y := by apply Subtype.ext; simp

@[scoped simp] theorem coe_ιE (x : EF p) : ((ιE p x : EB p) : FB p) = ι p x := rfl

theorem ι_algebraMap_EF (x : EF p) : ι p (algebraMap (EF p) (FF p) x) = algebraMap (EB p) (FB p) (ιE p x) := rfl

end CU2i
p2m_reactivate "P2MW.S_ModularCurve_exists_leadingCoeff_eq_mul_pow_of_aeval_jFull_eq_norm_aeval_modularUnitSeries.CU2i"

namespace CU2i
section PolyOrd
variable {K F : Type*} [Field K] [Field F] [Algebra K F] (w : Place K F)

theorem ord_intCast (n : ℤ) : w.ord (n : F) = 0 := by
  rw [← map_intCast (algebraMap K F)]; exact Place.ord_algebraMap w n

theorem ord_pow' (f : F) (n : ℕ) : w.ord (f ^ n) = n * w.ord f := by
  have := w.ord_zpow f n
  rwa [zpow_natCast] at this

theorem ord_nonneg_of_mem {f : F} (hf : f ∈ w.toValuationSubring) : 0 ≤ w.ord f := by
  rcases eq_or_ne f 0 with rfl | hf0
  · simp
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible w.toValuationSubring
  obtain ⟨n, u, hu⟩ :=
    IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
      (x := (⟨f, hf⟩ : w.toValuationSubring)) (by simpa [Subtype.ext_iff] using hf0) hπ
  have hcoe : f = ((u : w.toValuationSubring) : F) * ((π : F) ^ (n : ℤ)) := by
    have h := congrArg (Subtype.val) hu
    push_cast at h
    rw [zpow_natCast]
    exact h
  rw [hcoe, w.ord_unit_smul_zpow u hπ (n : ℤ)]
  exact Int.natCast_nonneg n

theorem not_mem_of_ord_neg {f : F} (hf : w.ord f < 0) : f ∉ w.toValuationSubring :=
  fun h => absurd (ord_nonneg_of_mem w h) (not_le.mpr hf)

theorem ne_zero_of_ord_ne_zero {f : F} (hf : w.ord f ≠ 0) : f ≠ 0 := by
  rintro rfl; exact hf (by simp)

theorem ord_aeval_of_ord_neg [CharZero F] (t : F) (ht : w.ord t < 0) :
    ∀ (P : Polynomial ℤ), P ≠ 0 → w.ord (aeval t P) = P.natDegree * w.ord t := by
  intro P
  induction hn : P.natDegree using Nat.strong_induction_on generalizing P with
  | _ n ih =>
    intro hP
    have ht0 : t ≠ 0 := ne_zero_of_ord_ne_zero w ht.ne

    have hdecomp := P.eraseLead_add_C_mul_X_pow
    have hlead : w.ord (aeval t (C P.leadingCoeff * X ^ P.natDegree)) = P.natDegree * w.ord t := by
      rw [map_mul, map_pow, aeval_C, aeval_X, algebraMap_int_eq, eq_intCast,
        w.ord_mul (by exact_mod_cast (leadingCoeff_ne_zero.mpr hP)) (pow_ne_zero _ ht0),
        ord_intCast, ord_pow', zero_add]
    have hlead0 : aeval t (C P.leadingCoeff * X ^ P.natDegree) ≠ 0 := by
      rw [map_mul, map_pow, aeval_C, aeval_X, algebraMap_int_eq, eq_intCast]
      exact mul_ne_zero (by exact_mod_cast (leadingCoeff_ne_zero.mpr hP)) (pow_ne_zero _ ht0)
    by_cases hQ : P.eraseLead = 0
    · rw [← hdecomp, hQ, zero_add, hlead, hn]
    · have hlt : P.eraseLead.natDegree < n := by
        rcases P.eraseLead_natDegree_lt_or_eraseLead_eq_zero with h | h
        · exact hn ▸ h
        · exact absurd h hQ
      have hQord := ih _ hlt P.eraseLead rfl hQ
      by_cases haQ : aeval t P.eraseLead = 0
      · rw [← hdecomp, map_add, haQ, zero_add, hlead, hn]
      · have hcmp : w.ord (aeval t (C P.leadingCoeff * X ^ P.natDegree)) < w.ord (aeval t P.eraseLead) := by
          rw [hlead, hQord, hn]
          exact Int.mul_lt_mul_of_neg_right (by exact_mod_cast hlt) ht
        rw [← hdecomp, map_add, add_comm, w.ord_add_eq_of_lt hlead0 haQ hcmp, hlead, hn]

theorem aeval_mem_of_mem {t : F} (ht : t ∈ w.toValuationSubring) (P : Polynomial ℤ) :
    aeval t P ∈ w.toValuationSubring := by
  induction P using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add]; exact add_mem hp hq
  | monomial n c =>
      rw [aeval_monomial, algebraMap_int_eq, eq_intCast]
      exact mul_mem (intCast_mem _ c) (pow_mem ht n)

theorem ord_aeval_of_ord_pos [CharZero F] (t : F) (ht : 0 < w.ord t) (P : Polynomial ℤ) (h0 : P.coeff 0 ≠ 0) :
    w.ord (aeval t P) = 0 := by
  have ht0 : t ≠ 0 := ne_zero_of_ord_ne_zero w ht.ne'
  have htmem : t ∈ w.toValuationSubring := Place.mem_toValuationSubring_of_ord_nonneg_alt w ht0 ht.le
  have hdecomp := P.X_mul_divX_add
  have hc : w.ord ((P.coeff 0 : ℤ) : F) = 0 := ord_intCast w _
  have hc0 : ((P.coeff 0 : ℤ) : F) ≠ 0 := by exact_mod_cast h0
  by_cases hq : t * aeval t P.divX = 0
  · rw [← hdecomp, map_add, map_mul, aeval_X, aeval_C, algebraMap_int_eq, eq_intCast, hq, zero_add, hc]
  · have hqmem : aeval t P.divX ∈ w.toValuationSubring := aeval_mem_of_mem w htmem _
    have hlt : w.ord ((P.coeff 0 : ℤ) : F) < w.ord (t * aeval t P.divX) := by
      rw [hc, w.ord_mul ht0 (right_ne_zero_of_mul hq)]
      have := ord_nonneg_of_mem w hqmem
      omega
    rw [← hdecomp, map_add, map_mul, aeval_X, aeval_C, algebraMap_int_eq, eq_intCast, add_comm,
      w.ord_add_eq_of_lt hc0 hq hlt, hc]

end PolyOrd
p2m_reactivate "P2MW.S_ModularCurve_exists_leadingCoeff_eq_mul_pow_of_aeval_jFull_eq_norm_aeval_modularUnitSeries.CU2i"
end CU2i
p2m_reactivate "P2MW.S_ModularCurve_exists_leadingCoeff_eq_mul_pow_of_aeval_jFull_eq_norm_aeval_modularUnitSeries.CU2i"

namespace CU2i
section Cusps
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

set_option quotPrecheck false
local notation "ℚb" => AlgebraicClosure ℚ
local notation "FB" p => ↥(ModularCurve.modularFunctionFieldBar p)
local notation "jB" p => (⟨coeffEmb (AlgebraicClosure ℚ) jq, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jq_mem_full p)⟩ : ↥(ModularCurve.modularFunctionFieldBar p))
local notation "EB" p => ModularCurve.jLineBar p

variable (p : ℕ) [Fact p.Prime]

attribute [local instance] ModularCurve.instDecidableEqRatFuncAlgebraicClosure

abbrev jE : ↥(EB p) := ⟨jB p, IntermediateField.mem_adjoin_simple_self _ _⟩

theorem jB_ne_zero : (jB p) ≠ 0 := by
  intro h
  have := ord_cuspInftyBar_coeffEmb_jq p
  rw [h, Place.ord_zero] at this
  exact absurd this (by norm_num)

theorem jE_ne_zero : jE p ≠ 0 := fun h => jB_ne_zero p (congrArg Subtype.val h)

theorem eq_jLineBarPlaceInfty_of_not_mem (v' : Place (AlgebraicClosure ℚ) ↥(EB p))
    (hv : (jE p : ↥(EB p)) ∉ v'.toValuationSubring) : v' = jLineBarPlaceInfty p := by
  set e := jLineBarRingEquiv p with he_def
  have he := jLineBarRingEquiv_algebraMap p
  set v'' : Place (AlgebraicClosure ℚ) (RatFunc (AlgebraicClosure ℚ)) :=
    Place.congrRingEquiv e.symm (Place.symm_algebraMap_comm e he) v' with hv''
  have heX : e RatFunc.X = jE p := Subtype.ext (jLineBarRingEquiv_X p)
  have hord : v'.ord (jE p) < 0 := by
    by_contra h
    push Not at h
    exact hv (Place.mem_toValuationSubring_of_ord_nonneg_alt v' (jE_ne_zero p) h)
  have hX : v''.ord (RatFunc.X : RatFunc (AlgebraicClosure ℚ)) < 0 := by
    have h := Place.ord_congrRingEquiv e.symm (Place.symm_algebraMap_comm e he) v' (e RatFunc.X)
    rw [e.symm_apply_apply] at h
    rw [hv'', h, heX]
    exact hord
  have hinf := RationalFunctionField.eq_placeInfty_of_ord_X_neg v'' hX
  have h1 : Place.congrRingEquiv e he v'' = v' := (Place.congrEquiv e he).apply_symm_apply v'
  calc v' = Place.congrRingEquiv e he v'' := h1.symm
    _ = Place.congrRingEquiv e he (RationalFunctionField.placeInfty (AlgebraicClosure ℚ)) := by rw [hinf]
    _ = jLineBarPlaceInfty p := rfl

variable [Algebra.IsIntegral ↥(ModularCurve.jLineBar p) ↥(ModularCurve.modularFunctionFieldBar p)]

theorem restrict_eq_of_isCusp (c : Place (AlgebraicClosure ℚ) (FB p)) (hc : IsCusp (jB p) c) :
    c.restrict ↥(EB p) = jLineBarPlaceInfty p := by
  apply eq_jLineBarPlaceInfty_of_not_mem
  rw [Place.restrict_toValuationSubring, ValuationSubring.mem_comap]
  exact (isCusp_iff _ _).mp hc

theorem isCusp_of_restrict_eq (w : Place (AlgebraicClosure ℚ) (FB p))
    (hw : w.restrict ↥(EB p) = jLineBarPlaceInfty p) : IsCusp (jB p) w := by
  rw [isCusp_iff]
  intro hmem
  have h1 : (jE p : ↥(EB p)) ∈ (w.restrict ↥(EB p)).toValuationSubring := by
    rw [Place.restrict_toValuationSubring, ValuationSubring.mem_comap]; exact hmem
  have h2 : (jE p : ↥(EB p)) ∉ ((cuspInftyBar p).restrict ↥(EB p)).toValuationSubring := by
    rw [Place.restrict_toValuationSubring, ValuationSubring.mem_comap]
    exact (isCusp_iff _ _).mp (isCusp_cuspInftyBar p)
  rw [hw, ← restrict_eq_of_isCusp p (cuspInftyBar p) (isCusp_cuspInftyBar p)] at h1
  exact h2 h1

theorem cuspInftyBar_ne_cuspZeroBar (hmem : modularUnitSeries p ∈ modularFunctionFieldFull p) :
    cuspInftyBar p ≠ cuspZeroBar p := by
  intro h
  have h1 := ord_cuspInftyBar_coeffEmb_modularUnitSeries p hmem
  have h2 := ord_cuspZeroBar_coeffEmb_modularUnitSeries p hmem
  rw [h] at h1
  rw [h1] at h2
  have hp : 2 ≤ p := (Fact.out : p.Prime).two_le
  omega

variable [FiniteDimensional ↥(ModularCurve.jLineBar p) ↥(ModularCurve.modularFunctionFieldBar p)]
  [Algebra.IsSeparable ↥(ModularCurve.jLineBar p) ↥(ModularCurve.modularFunctionFieldBar p)]

theorem mem_fiberOver_iff (w : Place (AlgebraicClosure ℚ) (FB p)) :
    w ∈ (jLineBarPlaceInfty p).fiberOver (FB p) ↔ w = cuspInftyBar p ∨ w = cuspZeroBar p := by
  rw [Place.mem_fiberOver]
  constructor
  · intro hw
    exact eq_cuspInftyBar_or_eq_cuspZeroBar p w (isCusp_of_restrict_eq p w hw)
  · rintro (rfl | rfl)
    · exact restrict_eq_of_isCusp p _ (isCusp_cuspInftyBar p)
    · exact restrict_eq_of_isCusp p _ (isCusp_cuspZeroBar p (isFrickeAutFull_frickeInvolutionFull_prime p))

open scoped Classical in
theorem fiberOver_eq (hmem : modularUnitSeries p ∈ modularFunctionFieldFull p) :
    (jLineBarPlaceInfty p).fiberOver (FB p) = {cuspInftyBar p, cuspZeroBar p} := by
  ext w
  rw [mem_fiberOver_iff, Finset.mem_insert, Finset.mem_singleton]

theorem inertiaDeg_eq_one (w : Place (AlgebraicClosure ℚ) (FB p)) : w.inertiaDeg ↥(EB p) = 1 := by
  haveI : IsCurveOver (AlgebraicClosure ℚ) (FB p) := isCurveOver_modularFunctionFieldBar p
  have hw : w.deg = 1 := IsCurveOver.deg_eq_one_of_isAlgClosed w
  have h := Place.deg_restrict_mul_inertiaDeg (F := ↥(EB p)) w
  rw [hw] at h
  have hv : (w.restrict ↥(EB p)).deg = 1 := Nat.eq_one_of_mul_eq_one_right h
  exact Place.inertiaDeg_eq_one_of_isRational w ((Place.isRational_iff_deg_eq_one _).mpr hw)
    ((Place.isRational_iff_deg_eq_one _).mpr hv)

theorem ramificationIndex_cuspInftyBar : (cuspInftyBar p).ramificationIndex ↥(EB p) = 1 := by
  have h := Place.ord_restrict (F := ↥(EB p)) (cuspInftyBar p) (jE p)
  have hj : algebraMap ↥(EB p) (FB p) (jE p) = jB p := rfl
  rw [hj, ord_cuspInftyBar_coeffEmb_jq] at h
  have hpos := Place.ramificationIndex_pos (F := ↥(EB p)) (cuspInftyBar p)

  have : ((cuspInftyBar p).ramificationIndex ↥(EB p) : ℤ) ∣ 1 := by
    refine ⟨-((cuspInftyBar p).restrict ↥(EB p)).ord (jE p), ?_⟩
    linarith [h]
  have := Int.eq_one_of_dvd_one (by positivity) this
  exact_mod_cast this

end Cusps
p2m_reactivate "P2MW.S_ModularCurve_exists_leadingCoeff_eq_mul_pow_of_aeval_jFull_eq_norm_aeval_modularUnitSeries.CU2i"
end CU2i
p2m_reactivate "P2MW.S_ModularCurve_exists_leadingCoeff_eq_mul_pow_of_aeval_jFull_eq_norm_aeval_modularUnitSeries.CU2i"

namespace CU2i
section Descent
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

set_option quotPrecheck false
local notation "ℚb" => AlgebraicClosure ℚ
local notation "FF" p => ↥(ModularCurve.modularFunctionFieldFull p)
local notation "FB" p => ↥(ModularCurve.modularFunctionFieldBar p)
local notation "jB" p => (⟨coeffEmb (AlgebraicClosure ℚ) jq, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jq_mem_full p)⟩ : ↥(ModularCurve.modularFunctionFieldBar p))
local notation "EF" p => IntermediateField.adjoin ℚ ({IgusaScheme.jFull p} : Set ↥(ModularCurve.modularFunctionFieldFull p))
local notation "EB" p => ModularCurve.jLineBar p

variable (p : ℕ) [Fact p.Prime]

theorem finrank_key (K : Type) [Field K] [CharZero K]
    (X : IntermediateField K (LaurentSeries K)) (hX : X = modularFunctionFieldFullC K p)
    (y : ↥X) (hy : (y : LaurentSeries K) = jqModC K) :
    Module.finrank ↥(IntermediateField.adjoin K ({y} : Set ↥X)) ↥X = dedekindPsi p := by
  subst hX
  obtain rfl : y = ⟨jqModC K, jqModC_mem_full K p⟩ := Subtype.ext hy
  exact finrank_adjoin_jqModC_modularFunctionFieldFullC_eq_dedekindPsi K p (by exact_mod_cast (NeZero.ne p))

theorem finrank_EF : Module.finrank ↥(EF p) (FF p) = dedekindPsi p := by
  convert finrank_key p ℚ (modularFunctionFieldFull p) (modularFunctionFieldFullC_rat p).symm (IgusaScheme.jFull p) rfl <;>
    exact Subsingleton.elim _ _

theorem dedekindPsi_pos' : 0 < dedekindPsi p := by
  unfold dedekindPsi
  have h1 : 1 ∈ p.divisors.filter Squarefree := by
    simp [Nat.mem_divisors, NeZero.ne p]
  exact lt_of_lt_of_le (Nat.div_pos (Nat.one_le_iff_ne_zero.mpr (NeZero.ne p)) one_pos)
    (Finset.single_le_sum (f := fun d => p / d) (fun _ _ => Nat.zero_le _) h1)

scoped instance finiteDimensional_EF : FiniteDimensional ↥(EF p) (FF p) :=
  Module.finite_of_finrank_pos (by rw [finrank_EF]; exact dedekindPsi_pos' p)

theorem bar_eq_fullC : ModularCurve.modularFunctionFieldBar p = modularFunctionFieldFullC (AlgebraicClosure ℚ) p := by
  apply le_antisymm
  ·
    change IntermediateField.adjoin _ _ ≤ _
    rw [IntermediateField.adjoin_le_iff]
    rintro _ ⟨x, hx, rfl⟩
    change x ∈ modularFunctionFieldFull p at hx
    change x ∈ IntermediateField.adjoin ℚ (divisorExpansions p) at hx
    induction hx using IntermediateField.adjoin_induction with
    | mem y hy =>
        obtain ⟨d, hd, hdvd, rfl⟩ := hy
        change coeffMap (algebraMap ℚ (AlgebraicClosure ℚ)) (qExpand ℚ d jq) ∈ _
        rw [coeffMap_qExpand, show jq = jqModC ℚ from rfl, coeffMap_jqModC]
        exact jqModCd_mem_full _ _ hdvd
    | algebraMap c =>
        rw [eq_ratCast, map_ratCast, ← map_ratCast (algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)))]
        exact IntermediateField.algebraMap_mem _ _
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy
    | inv x _ hx => rw [map_inv₀]; exact inv_mem hx
  · change IntermediateField.adjoin _ _ ≤ _
    rw [IntermediateField.adjoin_le_iff]
    rintro _ ⟨d, hd, hdvd, rfl⟩
    have : qExpand (AlgebraicClosure ℚ) d (jqModC (AlgebraicClosure ℚ)) =
        coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ d jq) := by
      change _ = coeffMap _ _
      rw [coeffMap_qExpand, show jq = jqModC ℚ from rfl, coeffMap_jqModC]
    rw [this]
    exact coeffEmb_mem_laurentBaseChange _ (jqd_mem_full p hdvd)

theorem finrank_EB : Module.finrank ↥(EB p) (FB p) = dedekindPsi p := by
  have hj : coeffEmb (AlgebraicClosure ℚ) jq = jqModC (AlgebraicClosure ℚ) := by
    change coeffMap _ _ = _
    rw [show jq = jqModC ℚ from rfl, coeffMap_jqModC]
  exact finrank_key p (AlgebraicClosure ℚ) (modularFunctionFieldBar p) (bar_eq_fullC p) _ hj

theorem ι_smul (a : ↥(EF p)) (x : FF p) : ι p (a • x) = ιE p a • ι p x := by
  rw [Algebra.smul_def, Algebra.smul_def, map_mul, ι_algebraMap_EF]

theorem span_ι_eq_top {s : Set (FF p)} (hs : Submodule.span ↥(EF p) s = ⊤) :
    Submodule.span ↥(EB p) (ι p '' s) = ⊤ := by
  rw [eq_top_iff]
  rintro y -

  obtain ⟨z, rfl⟩ := (baseChangeEquiv (AlgebraicClosure ℚ) (modularFunctionFieldFull p)).surjective y
  induction z using TensorProduct.induction_on with
  | zero => rw [map_zero]; exact zero_mem _
  | add a b ha hb => rw [map_add]; exact add_mem ha hb
  | tmul c f =>
      rw [baseChangeEquiv_tmul]
      have hf : ι p f ∈ Submodule.span ↥(EB p) (ι p '' s) := by
        have hf0 : f ∈ Submodule.span ↥(EF p) s := by rw [hs]; trivial
        induction hf0 using Submodule.span_induction with
        | mem x hx => exact Submodule.subset_span ⟨x, hx, rfl⟩
        | zero => rw [map_zero]; exact zero_mem _
        | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
        | smul a x _ hx => rw [ι_smul]; exact Submodule.smul_mem _ _ hx
      have : algebraMap (AlgebraicClosure ℚ) (laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull p)) c *
          (⟨coeffEmb (AlgebraicClosure ℚ) f, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) f.2⟩) =
          (algebraMap (AlgebraicClosure ℚ) ↥(EB p) c) • ι p f := by
        rw [Algebra.smul_def, IsScalarTower.algebraMap_apply (AlgebraicClosure ℚ) ↥(EB p) (FB p)]
        rfl
      rw [this]
      exact Submodule.smul_mem _ _ hf

def basisBar {ι' : Type*} [Fintype ι'] (b : Module.Basis ι' ↥(EF p) (FF p)) : Module.Basis ι' ↥(EB p) (FB p) :=
  haveI : FiniteDimensional ↥(EB p) (FB p) := finiteDimensional_adjoin_coeffEmb_jq_of_neZero p
  basisOfTopLeSpanOfCardEqFinrank (ι p ∘ b)
    (by rw [Set.range_comp, ← span_ι_eq_top p b.span_eq])
    (by rw [finrank_EB, ← finrank_EF, Module.finrank_eq_card_basis b])

theorem basisBar_apply {ι' : Type*} [Fintype ι'] (b : Module.Basis ι' ↥(EF p) (FF p)) (i : ι') :
    basisBar p b i = ι p (b i) := by
  rw [basisBar, coe_basisOfTopLeSpanOfCardEqFinrank]; rfl

theorem leftMulMatrix_ι {ι' : Type*} [Fintype ι'] [DecidableEq ι'] (b : Module.Basis ι' ↥(EF p) (FF p)) (x : FF p) :
    Algebra.leftMulMatrix (basisBar p b) (ι p x) = (Algebra.leftMulMatrix b x).map (ιE p) := by
  ext i j
  rw [Matrix.map_apply, Algebra.leftMulMatrix_eq_repr_mul, Algebra.leftMulMatrix_eq_repr_mul, basisBar_apply,
    ← map_mul]

  conv_lhs => rw [← b.sum_repr (x * b j)]
  rw [map_sum]
  simp_rw [ι_smul, ← basisBar_apply p b]
  rw [(basisBar p b).repr_sum_self]

theorem norm_ι (x : FF p) :
    Algebra.norm ↥(EB p) (ι p x) = ιE p (Algebra.norm ↥(EF p) x) := by
  classical
  let b := Module.finBasis ↥(EF p) (FF p)
  rw [Algebra.norm_eq_matrix_det (basisBar p b), Algebra.norm_eq_matrix_det b, leftMulMatrix_ι,
    RingHom.map_det, RingHom.mapMatrix_apply]

end Descent
p2m_reactivate "P2MW.S_ModularCurve_exists_leadingCoeff_eq_mul_pow_of_aeval_jFull_eq_norm_aeval_modularUnitSeries.CU2i"
end CU2i
p2m_reactivate "P2MW.S_ModularCurve_exists_leadingCoeff_eq_mul_pow_of_aeval_jFull_eq_norm_aeval_modularUnitSeries.CU2i"

namespace CU2i
section ValCalc
variable {K F : Type*} [Field K] [Field F] [Algebra K F]

def residueEquiv (v : Place K F) (hv : v.IsRational) : K ≃ₐ[K] v.ResidueField :=
  AlgEquiv.ofBijective (Algebra.ofId K v.ResidueField) ⟨(algebraMap K v.ResidueField).injective, hv⟩

def evalHom (v : Place K F) (hv : v.IsRational) : v.toValuationSubring →+* K :=
  ((residueEquiv v hv).symm : v.ResidueField →+* K).comp (IsLocalRing.residue v.toValuationSubring)

theorem evalAt_eq_evalHom (v : Place K F) (hv : v.IsRational) {f : F} (hf : f ∈ v.toValuationSubring) :
    v.evalAt f = evalHom v hv ⟨f, hf⟩ := by
  apply (algebraMap K v.ResidueField).injective
  rw [v.algebraMap_evalAt hv hf, evalHom, RingHom.comp_apply]
  change _ = (residueEquiv v hv) ((residueEquiv v hv).symm _)
  rw [AlgEquiv.apply_symm_apply]

theorem evalAt_sub (v : Place K F) (hv : v.IsRational) {f g : F} (hf : f ∈ v.toValuationSubring)
    (hg : g ∈ v.toValuationSubring) : v.evalAt (f - g) = v.evalAt f - v.evalAt g := by
  rw [evalAt_eq_evalHom v hv hf, evalAt_eq_evalHom v hv hg, evalAt_eq_evalHom v hv (sub_mem hf hg),
    ← map_sub]
  rfl

theorem evalAt_eq_zero_of_ord_pos (v : Place K F) (hv : v.IsRational) {f : F} (hf0 : f ≠ 0)
    (h : 0 < v.ord f) : v.evalAt f = 0 := by
  have hmem := Place.mem_toValuationSubring_of_ord_nonneg_alt v hf0 h.le
  have hmax : (⟨f, hmem⟩ : v.toValuationSubring) ∈ IsLocalRing.maximalIdeal v.toValuationSubring := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    have := v.ord_coe_unit hu.unit
    rw [IsUnit.unit_spec] at this
    change v.ord f = 0 at this
    omega
  rw [evalAt_eq_evalHom v hv hmem, evalHom, RingHom.comp_apply,
    (IsLocalRing.residue_eq_zero_iff _).mpr hmax, map_zero]

theorem evalAt_eq_of_ord_sub_pos (v : Place K F) (hv : v.IsRational) {f : F} (c : K)
    (hf : f ∈ v.toValuationSubring) (h : f = algebraMap K F c ∨ 0 < v.ord (f - algebraMap K F c)) :
    v.evalAt f = c := by
  rcases h with h | h
  · rw [h, Place.evalAt_algebraMap_eq]
  · have hc : algebraMap K F c ∈ v.toValuationSubring := v.algebraMap_mem' c
    have hsub := evalAt_sub v hv hf hc
    rw [evalAt_eq_zero_of_ord_pos v hv (ne_zero_of_ord_ne_zero v h.ne') h, Place.evalAt_algebraMap_eq] at hsub
    linear_combination -hsub

theorem eq_or_ord_pos_of_evalAt_eq_zero (v : Place K F) (hv : v.IsRational) {f : F}
    (hf : f ∈ v.toValuationSubring) (h : v.evalAt f = 0) : f = 0 ∨ 0 < v.ord f := by
  rcases eq_or_ne f 0 with rfl | hf0
  · exact Or.inl rfl
  · right
    have h0 := ord_nonneg_of_mem v hf
    rcases h0.lt_or_eq with hlt | heq
    · exact hlt
    · exact absurd h (Place.evalAt_ne_zero_of_ord_eq_zero v hv hf0 heq.symm)

theorem evalAt_inv' (v : Place K F) (hv : v.IsRational) {f : F} (hf0 : f ≠ 0) (h0 : v.ord f = 0) :
    v.evalAt f⁻¹ = (v.evalAt f)⁻¹ := by
  have hf := Place.mem_toValuationSubring_of_ord_nonneg_alt v hf0 h0.ge
  have hfi : f⁻¹ ∈ v.toValuationSubring :=
    Place.mem_toValuationSubring_of_ord_nonneg_alt v (inv_ne_zero hf0) (by rw [Place.ord_inv, h0]; rfl)
  have hmul := Place.evalAt_mul_of_mem v hv hf hfi
  rw [mul_inv_cancel₀ hf0, Place.evalAt_one] at hmul
  have hne := Place.evalAt_ne_zero_of_ord_eq_zero v hv hf0 h0
  exact (eq_inv_of_mul_eq_one_right hmul.symm)

theorem evalAt_pow' (v : Place K F) (hv : v.IsRational) {f : F} (hf : f ∈ v.toValuationSubring) (n : ℕ) :
    v.evalAt (f ^ n) = v.evalAt f ^ n := by
  induction n with
  | zero => simp [Place.evalAt_one]
  | succ n ih => rw [pow_succ, Place.evalAt_mul_of_mem v hv (pow_mem hf n) hf, ih, pow_succ]

theorem evalAt_zpow' (v : Place K F) (hv : v.IsRational) {f : F} (hf0 : f ≠ 0) (h0 : v.ord f = 0) (n : ℤ) :
    v.evalAt (f ^ n) = v.evalAt f ^ n := by
  have hf := Place.mem_toValuationSubring_of_ord_nonneg_alt v hf0 h0.ge
  rcases n with n | n
  · simp [evalAt_pow' v hv hf]
  · rw [zpow_negSucc, zpow_negSucc, ← evalAt_pow' v hv hf,
      evalAt_inv' v hv (pow_ne_zero _ hf0) (by rw [ord_pow', h0, mul_zero])]

theorem evalAt_div_of_ord_eq_zero (v : Place K F) (hv : v.IsRational) {f g : F}
    (hf : f ∈ v.toValuationSubring) (hg0 : g ≠ 0) (hg : v.ord g = 0) :
    v.evalAt (f / g) = v.evalAt f / v.evalAt g := by
  have hgm := Place.mem_toValuationSubring_of_ord_nonneg_alt v hg0 hg.ge
  have hgi : g⁻¹ ∈ v.toValuationSubring :=
    Place.mem_toValuationSubring_of_ord_nonneg_alt v (inv_ne_zero hg0) (by rw [Place.ord_inv, hg]; rfl)
  rw [div_eq_mul_inv, Place.evalAt_mul_of_mem v hv hf hgi, evalAt_inv' v hv hg0 hg, div_eq_mul_inv]

theorem evalAt_smul_place (σ : F ≃ₐ[K] F) (v : Place K F) (hv : v.IsRational) (hσv : (σ • v).IsRational)
    {f : F} (hf : f ∈ v.toValuationSubring) : (σ • v).evalAt (σ f) = v.evalAt f := by
  set c := v.evalAt f with hc
  have hcm : algebraMap K F c ∈ v.toValuationSubring := v.algebraMap_mem' c
  have h0 : v.evalAt (f - algebraMap K F c) = 0 := by
    rw [evalAt_sub v hv hf hcm, Place.evalAt_algebraMap_eq, hc, sub_self]
  have hσf : σ f ∈ (σ • v).toValuationSubring := by
    rcases eq_or_ne f 0 with rfl | hf0
    · rw [map_zero]; exact zero_mem _
    · exact Place.mem_toValuationSubring_of_ord_nonneg_alt _ (by simpa using hf0)
        (by rw [Place.ord_smul]; exact ord_nonneg_of_mem v hf)
  apply evalAt_eq_of_ord_sub_pos _ hσv c hσf
  rcases eq_or_ord_pos_of_evalAt_eq_zero v hv (sub_mem hf hcm) h0 with h | h
  · left; rw [sub_eq_zero] at h; rw [h, AlgEquiv.commutes]
  · right
    have : σ f - algebraMap K F c = σ (f - algebraMap K F c) := by rw [map_sub, AlgEquiv.commutes]
    rw [this, Place.ord_smul]; exact h

theorem evalAt_aeval_of_ord_pos (v : Place K F) (hv : v.IsRational) [CharZero F] (t : F) (ht : 0 < v.ord t)
    (P : Polynomial ℤ) : v.evalAt (aeval t P) = (P.coeff 0 : K) := by
  have ht0 : t ≠ 0 := ne_zero_of_ord_ne_zero v ht.ne'
  have htmem : t ∈ v.toValuationSubring := Place.mem_toValuationSubring_of_ord_nonneg_alt v ht0 ht.le
  apply evalAt_eq_of_ord_sub_pos v hv _ (aeval_mem_of_mem v htmem P)
  have haeval : aeval t P = t * aeval t P.divX + ((P.coeff 0 : ℤ) : F) := by
    conv_lhs => rw [← P.X_mul_divX_add]
    rw [map_add, map_mul, aeval_X, aeval_C, algebraMap_int_eq, eq_intCast]
  by_cases hq : t * aeval t P.divX = 0
  · left; rw [haeval, hq, zero_add, map_intCast]
  · right
    rw [haeval, map_intCast, add_sub_cancel_right, v.ord_mul ht0 (right_ne_zero_of_mul hq)]
    have := ord_nonneg_of_mem v (aeval_mem_of_mem v htmem P.divX)
    omega

theorem evalAt_aeval_div_aeval_of_ord_neg (v : Place K F) (hv : v.IsRational) [CharZero F] (t : F) (ht : v.ord t < 0)
    (P Q : Polynomial ℤ) (hP : P.Monic) (hQ : Q.Monic) (hdeg : P.natDegree = Q.natDegree) :
    v.evalAt (aeval t P / aeval t Q) = 1 := by
  have ht0 : t ≠ 0 := ne_zero_of_ord_ne_zero v ht.ne
  have hQ0 : aeval t Q ≠ 0 := by
    rcases eq_or_ne Q.natDegree 0 with hd | hd
    · rw [hQ.natDegree_eq_zero] at hd; rw [hd, map_one]; exact one_ne_zero
    · apply ne_zero_of_ord_ne_zero v
      rw [ord_aeval_of_ord_neg v t ht Q hQ.ne_zero]
      exact (Int.mul_neg_of_pos_of_neg (by exact_mod_cast Nat.pos_of_ne_zero hd) ht).ne
  have hordQ : v.ord (aeval t Q) = Q.natDegree * v.ord t := ord_aeval_of_ord_neg v t ht Q hQ.ne_zero
  have hordP : v.ord (aeval t P) = P.natDegree * v.ord t := ord_aeval_of_ord_neg v t ht P hP.ne_zero

  have hP0 : aeval t P ≠ 0 := by
    rcases eq_or_ne P.natDegree 0 with hd | hd
    · rw [hP.natDegree_eq_zero] at hd; rw [hd, map_one]; exact one_ne_zero
    · apply ne_zero_of_ord_ne_zero v
      rw [hordP]; exact (Int.mul_neg_of_pos_of_neg (by exact_mod_cast Nat.pos_of_ne_zero hd) ht).ne
  have hunit : v.ord (aeval t P / aeval t Q) = 0 := by
    rw [div_eq_mul_inv, v.ord_mul hP0 (inv_ne_zero hQ0), Place.ord_inv, hordP, hordQ, hdeg]; ring
  have hmem := Place.mem_toValuationSubring_of_ord_nonneg_alt v (div_ne_zero hP0 hQ0) hunit.ge
  apply evalAt_eq_of_ord_sub_pos v hv 1 hmem

  have hsub : aeval t P / aeval t Q - algebraMap K F 1 = aeval t (P - Q) / aeval t Q := by
    rw [map_one, map_sub, sub_div, div_self hQ0]
  by_cases hz : aeval t (P - Q) / aeval t Q = 0
  · left; exact sub_eq_zero.mp (hsub.trans hz)
  · right
    rw [hsub]
    have hPQ : P - Q ≠ 0 := by rintro h; rw [h, map_zero, zero_div] at hz; exact hz rfl
    have hnum : aeval t (P - Q) ≠ 0 := fun h => hz (by rw [h, zero_div])
    have hlt : (P - Q).natDegree < Q.natDegree := by
      rw [← hdeg]
      apply Polynomial.natDegree_lt_natDegree hPQ
      exact Polynomial.degree_sub_lt (by rw [Polynomial.degree_eq_natDegree hP.ne_zero, Polynomial.degree_eq_natDegree hQ.ne_zero, hdeg])
        hP.ne_zero (by rw [hP.leadingCoeff, hQ.leadingCoeff])
    rw [div_eq_mul_inv, v.ord_mul hnum (inv_ne_zero hQ0), Place.ord_inv, ord_aeval_of_ord_neg v t ht _ hPQ, hordQ]
    have : ((P - Q).natDegree : ℤ) < Q.natDegree := by exact_mod_cast hlt
    nlinarith

theorem evalAt_aeval_mul_zpow_neg_natDegree (v : Place K F) (hv : v.IsRational) [CharZero F] (t : F) (ht : v.ord t = -1)
    (P : Polynomial ℤ) (hP : P ≠ 0) : v.evalAt (aeval t P * t ^ (-(P.natDegree : ℤ))) = (P.leadingCoeff : K) := by
  have ht0 : t ≠ 0 := ne_zero_of_ord_ne_zero v (by rw [ht]; norm_num)
  have htn : v.ord t < 0 := by rw [ht]; norm_num
  have hordP : v.ord (aeval t P) = -P.natDegree := by rw [ord_aeval_of_ord_neg v t htn P hP, ht]; ring
  have haP0 : aeval t P ≠ 0 := by
    rcases eq_or_ne P.natDegree 0 with hd | hd
    · have hc : P.coeff 0 ≠ 0 := by
        intro h; apply hP; rw [Polynomial.eq_C_of_natDegree_eq_zero hd, h, map_zero]
      rw [Polynomial.eq_C_of_natDegree_eq_zero hd, aeval_C, algebraMap_int_eq, eq_intCast]
      exact_mod_cast hc
    · exact ne_zero_of_ord_ne_zero v (by rw [hordP]; omega)
  have hunit : v.ord (aeval t P * t ^ (-(P.natDegree : ℤ))) = 0 := by
    rw [v.ord_mul haP0 (zpow_ne_zero _ ht0), Place.ord_zpow, hordP, ht]; ring
  have hmem := Place.mem_toValuationSubring_of_ord_nonneg_alt v (mul_ne_zero haP0 (zpow_ne_zero _ ht0)) hunit.ge
  apply evalAt_eq_of_ord_sub_pos v hv _ hmem

  have haeval : aeval t P = aeval t P.eraseLead + (P.leadingCoeff : F) * t ^ P.natDegree := by
    conv_lhs => rw [← P.eraseLead_add_C_mul_X_pow]
    rw [map_add, map_mul, map_pow, aeval_C, aeval_X, algebraMap_int_eq, eq_intCast]
  have hsub : aeval t P * t ^ (-(P.natDegree : ℤ)) - algebraMap K F (P.leadingCoeff : K) =
      aeval t P.eraseLead * t ^ (-(P.natDegree : ℤ)) := by
    rw [haeval, add_mul, mul_assoc, ← zpow_natCast, ← zpow_add₀ ht0, add_neg_cancel, zpow_zero, mul_one,
      map_intCast]
    ring
  by_cases hz : aeval t P.eraseLead * t ^ (-(P.natDegree : ℤ)) = 0
  · left; exact sub_eq_zero.mp (hsub.trans hz)
  · right
    rw [hsub]
    have hQ : P.eraseLead ≠ 0 := by rintro h; rw [h, map_zero, zero_mul] at hz; exact hz rfl
    have hnum : aeval t P.eraseLead ≠ 0 := fun h => hz (by rw [h, zero_mul])
    have hlt : P.eraseLead.natDegree < P.natDegree := by
      rcases P.eraseLead_natDegree_lt_or_eraseLead_eq_zero with h | h
      · exact h
      · exact absurd h hQ
    rw [v.ord_mul hnum (zpow_ne_zero _ ht0), Place.ord_zpow, ord_aeval_of_ord_neg v t htn _ hQ, ht]
    have : (P.eraseLead.natDegree : ℤ) < P.natDegree := by exact_mod_cast hlt
    linarith

end ValCalc
p2m_reactivate "P2MW.S_ModularCurve_exists_leadingCoeff_eq_mul_pow_of_aeval_jFull_eq_norm_aeval_modularUnitSeries.CU2i"
end CU2i
p2m_reactivate "P2MW.S_ModularCurve_exists_leadingCoeff_eq_mul_pow_of_aeval_jFull_eq_norm_aeval_modularUnitSeries.CU2i"

namespace CU2i
section QCoeff

theorem isMonicOfOrder_jq : IsMonicOfOrder jq (-1) :=
  ⟨order_jq, by rw [HahnSeries.leadingCoeff_eq, order_jq, coeff_jq_neg_one]⟩

theorem isMonicOfOrder_one : IsMonicOfOrder (1 : LaurentSeries ℚ) 0 := by
  have := IsMonicOfOrder.single 0
  rwa [HahnSeries.single_zero_one] at this

theorem isMonicOfOrder_pow {f : LaurentSeries ℚ} {m : ℤ} (hf : IsMonicOfOrder f m) (n : ℕ) :
    IsMonicOfOrder (f ^ n) (n * m) := by
  induction n with
  | zero => rw [pow_zero, Nat.cast_zero, zero_mul]; exact isMonicOfOrder_one
  | succ n ih =>
      rw [pow_succ, show ((n + 1 : ℕ) : ℤ) * m = n * m + m by push_cast; ring]
      exact ih.mul hf

theorem order_sub_gt_of_isMonicOfOrder {f g : LaurentSeries ℚ} {m : ℤ} (hf : IsMonicOfOrder f m)
    (hg : IsMonicOfOrder g m) (hne : f - g ≠ 0) : m < (f - g).order := by
  by_contra h
  push Not at h
  have hc := (HahnSeries.coeff_order_eq_zero.not.mpr hne)
  rcases h.lt_or_eq with hlt | heq
  · rw [HahnSeries.coeff_sub, hf.coeff_of_lt hlt, hg.coeff_of_lt hlt, sub_self] at hc; exact hc rfl
  · rw [heq, HahnSeries.coeff_sub, hf.coeff_self, hg.coeff_self, sub_self] at hc; exact hc rfl

theorem order_coeffEmb (L : Type*) [Field L] [Algebra ℚ L] {x : LaurentSeries ℚ} (hx : x ≠ 0) :
    (coeffEmb L x).order = x.order := by
  have h1 : (coeffEmb L x).coeff x.order ≠ 0 := by
    rw [coeffEmb_coeff]; exact (_root_.map_ne_zero _).mpr ((HahnSeries.coeff_order_eq_zero.not.mpr hx))
  have h0 : coeffEmb L x ≠ 0 := fun h => h1 (by rw [h, HahnSeries.coeff_zero])
  refine le_antisymm (HahnSeries.order_le_of_coeff_ne_zero h1) ?_
  by_contra! h
  exact (HahnSeries.coeff_order_eq_zero.not.mpr h0) (by rw [coeffEmb_coeff, HahnSeries.coeff_eq_zero_of_lt_order h, map_zero])

variable (p : ℕ) [Fact p.Prime]

theorem order_u_sub_jq_pow :
    modularUnitSeries p - jq ^ (p - 1) = 0 ∨ (1 - (p : ℤ)) < (modularUnitSeries p - jq ^ (p - 1)).order := by
  by_cases h : modularUnitSeries p - jq ^ (p - 1) = 0
  · exact Or.inl h
  · right
    have h1 := isMonicOfOrder_modularUnitSeries p
    have h2 : IsMonicOfOrder (jq ^ (p - 1)) (1 - (p : ℤ)) := by
      have := isMonicOfOrder_pow isMonicOfOrder_jq (p - 1)
      have hp : 1 ≤ p := (Fact.out : p.Prime).one_le
      rwa [show ((p - 1 : ℕ) : ℤ) * (-1) = 1 - (p : ℤ) by push_cast [hp]; ring] at this
    exact order_sub_gt_of_isMonicOfOrder h1 h2 h

theorem order_u_pow_sub_jqp_pow :
    modularUnitSeries p ^ p - (qExpand ℚ p jq) ^ (p - 1) = 0 ∨
      ((p : ℤ) * (1 - p)) < (modularUnitSeries p ^ p - (qExpand ℚ p jq) ^ (p - 1)).order := by
  by_cases h : modularUnitSeries p ^ p - (qExpand ℚ p jq) ^ (p - 1) = 0
  · exact Or.inl h
  · right
    have hp : 1 ≤ p := (Fact.out : p.Prime).one_le
    have h1 : IsMonicOfOrder (modularUnitSeries p ^ p) ((p : ℤ) * (1 - p)) :=
      isMonicOfOrder_pow (isMonicOfOrder_modularUnitSeries p) p
    have h2 : IsMonicOfOrder ((qExpand ℚ p jq) ^ (p - 1)) ((p : ℤ) * (1 - p)) := by
      have := isMonicOfOrder_pow (isMonicOfOrder_jq.qExpand p) (p - 1)
      rwa [show ((p - 1 : ℕ) : ℤ) * ((p : ℤ) * (-1)) = (p : ℤ) * (1 - p) by push_cast [hp]; ring] at this
    exact order_sub_gt_of_isMonicOfOrder h1 h2 h

end QCoeff
p2m_reactivate "P2MW.S_ModularCurve_exists_leadingCoeff_eq_mul_pow_of_aeval_jFull_eq_norm_aeval_modularUnitSeries.CU2i"
end CU2i
p2m_reactivate "P2MW.S_ModularCurve_exists_leadingCoeff_eq_mul_pow_of_aeval_jFull_eq_norm_aeval_modularUnitSeries.CU2i"

namespace CU2i
section Fricke
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

set_option quotPrecheck false
local notation "ℚb" => AlgebraicClosure ℚ
local notation "FF" p => ↥(ModularCurve.modularFunctionFieldFull p)
local notation "FB" p => ↥(ModularCurve.modularFunctionFieldBar p)
local notation "jB" p => (⟨coeffEmb (AlgebraicClosure ℚ) jq, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jq_mem_full p)⟩ : ↥(ModularCurve.modularFunctionFieldBar p))

variable (p : ℕ) [Fact p.Prime]

def jpF : FF p := ⟨qExpand ℚ p jq, jqd_mem_full p (dvd_refl p)⟩

abbrev wB : (FB p) ≃ₐ[AlgebraicClosure ℚ] (FB p) := frickeInvolutionBar p

theorem wB_ι (x : FF p) : wB p (ι p x) = ι p (frickeInvolutionFull p x) := by
  rw [wB, frickeInvolutionBar_def]
  exact geomAut_coeffEmb (AlgebraicClosure ℚ) (modularFunctionFieldFull p) (frickeInvolutionFull p) x

theorem frickeInvolutionFull_jF : frickeInvolutionFull p (IgusaScheme.jFull p) = jpF p := by
  have h := isFrickeAutFull_frickeInvolutionFull_prime p 1 p (one_mul p) inferInstance inferInstance
  have h1 : (⟨qExpand ℚ 1 jq, jqd_mem_full p (Dvd.intro p (one_mul p))⟩ : FF p) = IgusaScheme.jFull p :=
    Subtype.ext (qExpand_one_apply jq)
  rw [h1] at h
  rw [h]; rfl

theorem wB_jB : wB p (jB p) = ι p (jpF p) := by
  rw [← ι_jF, wB_ι, frickeInvolutionFull_jF]

theorem frickeInvolutionFull_u (hmem : modularUnitSeries p ∈ modularFunctionFieldFull p) :
    frickeInvolutionFull p ⟨modularUnitSeries p, hmem⟩ =
      (p : FF p) ^ 12 * (⟨modularUnitSeries p, hmem⟩ : FF p)⁻¹ := by
  apply Subtype.ext
  rw [coe_frickeInvolutionFull_modularUnitSeries p hmem]
  push_cast
  rw [← HahnSeries.C_mul_eq_smul, map_pow, map_natCast]

theorem wB_wB (y : FB p) : wB p (wB p y) = y := by
  have hσ : frickeInvolutionFull p * frickeInvolutionFull p = 1 :=
    AlgEquiv.ext (frickeInvolutionFull_apply_apply p)
  have : wB p * wB p = 1 := by
    rw [wB, frickeInvolutionBar_def, ← map_mul, hσ, map_one]
  exact congrArg (fun f : (FB p) ≃ₐ[AlgebraicClosure ℚ] (FB p) => f y) this

theorem evalAt_cuspZeroBar (y : FB p) (hy : wB p y ∈ (cuspInftyBar p).toValuationSubring) :
    (cuspZeroBar p).evalAt y = (cuspInftyBar p).evalAt (wB p y) := by
  haveI : IsCurveOver (AlgebraicClosure ℚ) (FB p) := isCurveOver_modularFunctionFieldBar p
  have hr0 : (cuspZeroBar p).IsRational :=
    (Place.isRational_iff_deg_eq_one _).mpr (IsCurveOver.deg_eq_one_of_isAlgClosed _)
  have hri : (cuspInftyBar p).IsRational :=
    (Place.isRational_iff_deg_eq_one _).mpr (IsCurveOver.deg_eq_one_of_isAlgClosed _)
  conv_lhs => rw [← wB_wB p y, cuspZeroBar_def]
  exact evalAt_smul_place (wB p) (cuspInftyBar p) hri (by rw [← cuspZeroBar_def]; exact hr0) hy

theorem ord_cuspZeroBar (y : FB p) : (cuspZeroBar p).ord y = (cuspInftyBar p).ord (wB p y) := by
  conv_lhs => rw [← wB_wB p y, cuspZeroBar_def]
  exact Place.ord_smul (wB p) (cuspInftyBar p) (wB p y)

end Fricke
p2m_reactivate "P2MW.S_ModularCurve_exists_leadingCoeff_eq_mul_pow_of_aeval_jFull_eq_norm_aeval_modularUnitSeries.CU2i"
end CU2i
p2m_reactivate "P2MW.S_ModularCurve_exists_leadingCoeff_eq_mul_pow_of_aeval_jFull_eq_norm_aeval_modularUnitSeries.CU2i"

namespace CU2i
section CuspValues
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

set_option quotPrecheck false
local notation "ℚb" => AlgebraicClosure ℚ
local notation "FF" p => ↥(ModularCurve.modularFunctionFieldFull p)
local notation "FB" p => ↥(ModularCurve.modularFunctionFieldBar p)
local notation "jB" p => (⟨coeffEmb (AlgebraicClosure ℚ) jq, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jq_mem_full p)⟩ : ↥(ModularCurve.modularFunctionFieldBar p))
local notation "EB" p => ModularCurve.jLineBar p

variable (p : ℕ) [Fact p.Prime]

theorem isRational_FB (w : Place (AlgebraicClosure ℚ) (FB p)) : w.IsRational := by
  haveI : IsCurveOver (AlgebraicClosure ℚ) (FB p) := isCurveOver_modularFunctionFieldBar p
  exact (Place.isRational_iff_deg_eq_one _).mpr (IsCurveOver.deg_eq_one_of_isAlgClosed w)

variable [Algebra.IsIntegral ↥(ModularCurve.jLineBar p) ↥(ModularCurve.modularFunctionFieldBar p)]

theorem isRational_jLineBarPlaceInfty : (jLineBarPlaceInfty p).IsRational := by
  haveI : IsCurveOver (AlgebraicClosure ℚ) (FB p) := isCurveOver_modularFunctionFieldBar p
  have hw : (cuspInftyBar p).deg = 1 := IsCurveOver.deg_eq_one_of_isAlgClosed _
  have h := Place.deg_restrict_mul_inertiaDeg (F := ↥(EB p)) (cuspInftyBar p)
  rw [hw, restrict_eq_of_isCusp p _ (isCusp_cuspInftyBar p)] at h
  exact (Place.isRational_iff_deg_eq_one _).mpr (Nat.eq_one_of_mul_eq_one_right h)

variable [FiniteDimensional ↥(ModularCurve.jLineBar p) ↥(ModularCurve.modularFunctionFieldBar p)]
  [Algebra.IsSeparable ↥(ModularCurve.jLineBar p) ↥(ModularCurve.modularFunctionFieldBar p)] in
theorem ord_jLineBarPlaceInfty_jE : (jLineBarPlaceInfty p).ord (jE p) = -1 := by
  have h := Place.ord_restrict (F := ↥(EB p)) (cuspInftyBar p) (jE p)
  have hj : algebraMap ↥(EB p) (FB p) (jE p) = jB p := rfl
  rw [hj, ord_cuspInftyBar_coeffEmb_jq, restrict_eq_of_isCusp p _ (isCusp_cuspInftyBar p),
    ramificationIndex_cuspInftyBar, Nat.cast_one, one_mul] at h
  exact h.symm

theorem dedekindPsi_prime : dedekindPsi p = p + 1 := by
  have hp : p.Prime := Fact.out
  rw [dedekindPsi, Nat.Prime.divisors hp]
  have h1 : Squarefree 1 := squarefree_one
  have h2 : Squarefree p := hp.squarefree
  rw [Finset.filter_insert, if_pos h1, Finset.filter_singleton, if_pos h2,
    Finset.sum_insert (by simp [hp.one_lt.ne]), Finset.sum_singleton, Nat.div_one, Nat.div_self hp.pos]

variable [FiniteDimensional ↥(ModularCurve.jLineBar p) ↥(ModularCurve.modularFunctionFieldBar p)]
  [Algebra.IsSeparable ↥(ModularCurve.jLineBar p) ↥(ModularCurve.modularFunctionFieldBar p)]

theorem ramificationIndex_cuspZeroBar (hmem : modularUnitSeries p ∈ modularFunctionFieldFull p) :
    (cuspZeroBar p).ramificationIndex ↥(EB p) = p := by
  classical
  have h := Place.sum_ramificationIndex_mul_inertiaDeg_fiberOver (K := AlgebraicClosure ℚ) (F := ↥(EB p))
    (F' := FB p) (jLineBarPlaceInfty p)
  rw [fiberOver_eq p hmem, Finset.sum_pair (cuspInftyBar_ne_cuspZeroBar p hmem), inertiaDeg_eq_one,
    inertiaDeg_eq_one, ramificationIndex_cuspInftyBar, finrank_EB, dedekindPsi_prime] at h
  push_cast at h
  have : ((cuspZeroBar p).ramificationIndex ↥(EB p) : ℤ) = p := by linarith
  exact_mod_cast this

end CuspValues
p2m_reactivate "P2MW.S_ModularCurve_exists_leadingCoeff_eq_mul_pow_of_aeval_jFull_eq_norm_aeval_modularUnitSeries.CU2i"
end CU2i
p2m_reactivate "P2MW.S_ModularCurve_exists_leadingCoeff_eq_mul_pow_of_aeval_jFull_eq_norm_aeval_modularUnitSeries.CU2i"

namespace CU2i
section UnitRatios
variable {K F : Type*} [Field K] [Field F] [Algebra K F] [CharZero F] (v : Place K F)

theorem evalAt_zero' (v : Place K F) : v.evalAt (0 : F) = 0 := by
  rw [← map_zero (algebraMap K F), Place.evalAt_algebraMap_eq]

theorem ord_eq_zero_of_evalAt_ne_zero (hv : v.IsRational) {f : F}
    (hf : f ∈ v.toValuationSubring) (hne : v.evalAt f ≠ 0) : v.ord f = 0 := by
  by_contra h
  have hpos : 0 < v.ord f := lt_of_le_of_ne (ord_nonneg_of_mem v hf) (Ne.symm h)
  have hf0 : f ≠ 0 := by rintro rfl; exact hne (evalAt_zero' v)
  exact hne (evalAt_eq_zero_of_ord_pos v hv hf0 hpos)

theorem pole_part (hv : v.IsRational) (t : F) (ht : v.ord t < 0) (P Q : Polynomial ℤ) (hP : P.Monic) (hQ : Q.Monic)
    (hdeg : P.natDegree = Q.natDegree) :
    aeval t P / aeval t Q ∈ v.toValuationSubring ∧ v.ord (aeval t P / aeval t Q) = 0 ∧
      aeval t P / aeval t Q ≠ 0 ∧ v.evalAt (aeval t P / aeval t Q) = 1 := by
  have hval := evalAt_aeval_div_aeval_of_ord_neg v hv t ht P Q hP hQ hdeg
  have ht0 : t ≠ 0 := ne_zero_of_ord_ne_zero v ht.ne
  have hne : ∀ (R : Polynomial ℤ), R.Monic → aeval t R ≠ 0 := by
    intro R hR
    rcases eq_or_ne R.natDegree 0 with hd | hd
    · rw [hR.natDegree_eq_zero] at hd; rw [hd, map_one]; exact one_ne_zero
    · apply ne_zero_of_ord_ne_zero v
      rw [ord_aeval_of_ord_neg v t ht R hR.ne_zero]
      exact (Int.mul_neg_of_pos_of_neg (by exact_mod_cast Nat.pos_of_ne_zero hd) ht).ne
  have hord : v.ord (aeval t P / aeval t Q) = 0 := by
    rw [div_eq_mul_inv, v.ord_mul (hne P hP) (inv_ne_zero (hne Q hQ)), Place.ord_inv,
      ord_aeval_of_ord_neg v t ht P hP.ne_zero, ord_aeval_of_ord_neg v t ht Q hQ.ne_zero, hdeg]; ring
  have hne' : aeval t P / aeval t Q ≠ 0 := div_ne_zero (hne P hP) (hne Q hQ)
  exact ⟨Place.mem_toValuationSubring_of_ord_nonneg_alt v hne' hord.ge, hord, hne', hval⟩

theorem zero_part (hv : v.IsRational) (t : F) (ht : 0 < v.ord t) (P Q : Polynomial ℤ) (hP0 : (P.coeff 0 : K) ≠ 0)
    (hQ0 : Q.coeff 0 = 1) :
    aeval t P / aeval t Q ∈ v.toValuationSubring ∧ v.ord (aeval t P / aeval t Q) = 0 ∧
      aeval t P / aeval t Q ≠ 0 ∧ v.evalAt (aeval t P / aeval t Q) = (P.coeff 0 : K) := by
  have ht0 : t ≠ 0 := ne_zero_of_ord_ne_zero v ht.ne'
  have htmem : t ∈ v.toValuationSubring := Place.mem_toValuationSubring_of_ord_nonneg_alt v ht0 ht.le
  have hPval := evalAt_aeval_of_ord_pos v hv t ht P
  have hQval : v.evalAt (aeval t Q) = 1 := by rw [evalAt_aeval_of_ord_pos v hv t ht Q, hQ0]; simp
  have hPmem := aeval_mem_of_mem v htmem P
  have hQmem := aeval_mem_of_mem v htmem Q
  have hQord : v.ord (aeval t Q) = 0 := ord_eq_zero_of_evalAt_ne_zero v hv hQmem (by rw [hQval]; exact one_ne_zero)
  have hPord : v.ord (aeval t P) = 0 := ord_eq_zero_of_evalAt_ne_zero v hv hPmem (by rw [hPval]; exact hP0)
  have hQne : aeval t Q ≠ 0 := by intro h; rw [h, evalAt_zero'] at hQval; exact zero_ne_one hQval
  have hPne : aeval t P ≠ 0 := by intro h; rw [h, evalAt_zero'] at hPval; exact hP0 hPval.symm
  have hval : v.evalAt (aeval t P / aeval t Q) = (P.coeff 0 : K) := by
    rw [evalAt_div_of_ord_eq_zero v hv hPmem hQne hQord, hPval, hQval, div_one]
  have hord : v.ord (aeval t P / aeval t Q) = 0 := by
    rw [div_eq_mul_inv, v.ord_mul hPne (inv_ne_zero hQne), Place.ord_inv, hPord, hQord]; ring
  have hne' : aeval t P / aeval t Q ≠ 0 := div_ne_zero hPne hQne
  exact ⟨Place.mem_toValuationSubring_of_ord_nonneg_alt v hne' hord.ge, hord, hne', hval⟩

theorem lead_part (t : F) (ht : v.ord t = -1) (P : Polynomial ℤ) (hP : P ≠ 0) :
    aeval t P * t ^ (-(P.natDegree : ℤ)) ∈ v.toValuationSubring ∧ v.ord (aeval t P * t ^ (-(P.natDegree : ℤ))) = 0 ∧
      aeval t P * t ^ (-(P.natDegree : ℤ)) ≠ 0 := by
  have ht0 : t ≠ 0 := ne_zero_of_ord_ne_zero v (by rw [ht]; norm_num)
  have htn : v.ord t < 0 := by rw [ht]; norm_num
  have hordP : v.ord (aeval t P) = -P.natDegree := by rw [ord_aeval_of_ord_neg v t htn P hP, ht]; ring
  have haP0 : aeval t P ≠ 0 := by
    rcases eq_or_ne P.natDegree 0 with hd | hd
    · have hc : P.coeff 0 ≠ 0 := by
        intro h; apply hP; rw [Polynomial.eq_C_of_natDegree_eq_zero hd, h, map_zero]
      rw [Polynomial.eq_C_of_natDegree_eq_zero hd, aeval_C, algebraMap_int_eq, eq_intCast]
      exact_mod_cast hc
    · exact ne_zero_of_ord_ne_zero v (by rw [hordP]; omega)
  have hne : aeval t P * t ^ (-(P.natDegree : ℤ)) ≠ 0 := mul_ne_zero haP0 (zpow_ne_zero _ ht0)
  have hord : v.ord (aeval t P * t ^ (-(P.natDegree : ℤ))) = 0 := by
    rw [v.ord_mul haP0 (zpow_ne_zero _ ht0), Place.ord_zpow, hordP, ht]; ring
  exact ⟨Place.mem_toValuationSubring_of_ord_nonneg_alt v hne hord.ge, hord, hne⟩

theorem regroup₁ {E : Type*} [Field E] (a b t : E) (ht : t ≠ 0) (m n : ℤ) (k : ℕ) :
    (a * t ^ m) * (b * t ^ n) ^ k = a * b ^ k * t ^ (m + k * n) := by
  rw [mul_pow, ← zpow_natCast (t ^ n), ← zpow_mul, zpow_add₀ ht]; ring

theorem regroup₂ {E : Type*} [Field E] (a b t : E) (ht : t ≠ 0) (n : ℤ) (k : ℕ) :
    a / b ^ k = (a * t ^ ((k : ℤ) * n)) / (b * t ^ n) ^ k := by
  rw [mul_pow, ← zpow_natCast (t ^ n), ← zpow_mul, mul_comm n, mul_div_mul_right _ _ (zpow_ne_zero _ ht)]

end UnitRatios
p2m_reactivate "P2MW.S_ModularCurve_exists_leadingCoeff_eq_mul_pow_of_aeval_jFull_eq_norm_aeval_modularUnitSeries.CU2i"
end CU2i
p2m_reactivate "P2MW.S_ModularCurve_exists_leadingCoeff_eq_mul_pow_of_aeval_jFull_eq_norm_aeval_modularUnitSeries.CU2i"

open CU2i in
set_option maxHeartbeats 12800000 in
set_option synthInstance.maxHeartbeats 1600000 in
theorem solution
    (p : ℕ) [Fact p.Prime] [NeZero p]
    (hmem : modularUnitSeries p ∈ modularFunctionFieldFull p)
    (v : ↥(ModularCurve.modularFunctionFieldFull p))
    (hv : v = ⟨modularUnitSeries p, hmem⟩ ∨
      v = (p : ↥(ModularCurve.modularFunctionFieldFull p)) ^ 12 * (⟨modularUnitSeries p, hmem⟩)⁻¹)
    (g : Polynomial ℤ) (hg : g.Monic) (hD : 1 ≤ g.natDegree) (h0 : g.coeff 0 ≠ 0)
    (N : Polynomial ℤ)
    (hN : (Polynomial.aeval (IgusaScheme.jFull p) N : ↥(ModularCurve.modularFunctionFieldFull p)) =
      algebraMap ↥(IntermediateField.adjoin ℚ ({IgusaScheme.jFull p} : Set ↥(ModularCurve.modularFunctionFieldFull p))) ↥(ModularCurve.modularFunctionFieldFull p)
        (Algebra.norm ↥(IntermediateField.adjoin ℚ ({IgusaScheme.jFull p} : Set ↥(ModularCurve.modularFunctionFieldFull p))) (Polynomial.aeval v g))) :
    ∃ (ε : ℤˣ) (k : ℕ), N.leadingCoeff = (ε : ℤ) * (g.coeff 0) ^ k := by
  classical

  set u : ↥(modularFunctionFieldFull p) := ⟨modularUnitSeries p, hmem⟩ with hu
  set u' : ↥(modularFunctionFieldFull p) := (p : ↥(modularFunctionFieldFull p)) ^ 12 * u⁻¹ with hu'
  set x : ↥(modularFunctionFieldFull p) := Polynomial.aeval v g with hx
  haveI : FiniteDimensional ↥(jLineBar p) ↥(modularFunctionFieldBar p) :=
    finiteDimensional_adjoin_coeffEmb_jq_of_neZero p
  haveI : Algebra.IsIntegral ↥(jLineBar p) ↥(modularFunctionFieldBar p) := Algebra.IsIntegral.of_finite _ _
  haveI : Algebra.IsSeparable ↥(jLineBar p) ↥(modularFunctionFieldBar p) := Algebra.IsSeparable.of_integral _ _
  haveI : IsCurveOver (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar p) := isCurveOver_modularFunctionFieldBar p
  have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
  have hp1 : 1 ≤ p := by omega
  have hpm1 : ((p - 1 : ℕ) : ℤ) = (p : ℤ) - 1 := by push_cast [hp1]; ring
  have hri := isRational_FB p (cuspInftyBar p)
  have hvI := isRational_jLineBarPlaceInfty p

  have hιcomp : (ι p).comp (algebraMap ℤ ↥(modularFunctionFieldFull p)) = algebraMap ℤ ↥(modularFunctionFieldBar p) :=
    RingHom.ext_int _ _
  have hιaeval : ∀ (t : ↥(modularFunctionFieldFull p)) (P : Polynomial ℤ),
      ι p (Polynomial.aeval t P) = Polynomial.aeval (ι p t) P := by
    intro t P; rw [Polynomial.aeval_def, Polynomial.hom_eval₂, hιcomp, ← Polynomial.aeval_def]
  have hwcomp : ((wB p : ↥(modularFunctionFieldBar p) ≃ₐ[AlgebraicClosure ℚ] ↥(modularFunctionFieldBar p)) :
      ↥(modularFunctionFieldBar p) →+* ↥(modularFunctionFieldBar p)).comp (algebraMap ℤ ↥(modularFunctionFieldBar p)) =
      algebraMap ℤ ↥(modularFunctionFieldBar p) := RingHom.ext_int _ _
  have hwaeval : ∀ (t : ↥(modularFunctionFieldBar p)) (P : Polynomial ℤ),
      wB p (Polynomial.aeval t P) = Polynomial.aeval (wB p t) P := by
    intro t P
    have h := Polynomial.hom_eval₂ P (algebraMap ℤ ↥(modularFunctionFieldBar p))
      ((wB p : ↥(modularFunctionFieldBar p) ≃ₐ[AlgebraicClosure ℚ] ↥(modularFunctionFieldBar p)) :
        ↥(modularFunctionFieldBar p) →+* ↥(modularFunctionFieldBar p)) t
    rw [hwcomp] at h
    rw [Polynomial.aeval_def, Polynomial.aeval_def]
    exact h
  have hEcomp : (algebraMap ↥(jLineBar p) ↥(modularFunctionFieldBar p)).comp (algebraMap ℤ ↥(jLineBar p)) =
      algebraMap ℤ ↥(modularFunctionFieldBar p) := RingHom.ext_int _ _
  have hEaeval : ∀ (P : Polynomial ℤ), algebraMap ↥(jLineBar p) ↥(modularFunctionFieldBar p) (Polynomial.aeval (jE p) P) =
      Polynomial.aeval (⟨coeffEmb (AlgebraicClosure ℚ) jq, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jq_mem_full p)⟩ : ↥(modularFunctionFieldBar p)) P := by
    intro P; rw [Polynomial.aeval_def, Polynomial.hom_eval₂, hEcomp, ← Polynomial.aeval_def]; rfl

  have hnormE : ∀ (y : ↥(modularFunctionFieldFull p)) (M : Polynomial ℤ),
      (Polynomial.aeval (IgusaScheme.jFull p) M : ↥(modularFunctionFieldFull p)) =
        algebraMap _ _ (Algebra.norm ↥(IntermediateField.adjoin ℚ ({IgusaScheme.jFull p} : Set ↥(modularFunctionFieldFull p))) y) →
      Algebra.norm ↥(jLineBar p) (ι p y) = Polynomial.aeval (jE p) M := by
    intro y M hM
    rw [norm_ι]
    apply (algebraMap ↥(jLineBar p) ↥(modularFunctionFieldBar p)).injective
    rw [← ι_algebraMap_EF, ← hM, hιaeval, ι_jF, hEaeval]

  obtain ⟨hu_ch, hu'_ch⟩ := modularUnitSeries_mem_chartAlgFin_int p hmem
  have h1u : (1 + u) ∈ AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) :=
    add_mem (one_mem _) hu_ch
  have h1u' : (1 + u') ∈ AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) :=
    add_mem (one_mem _) hu'_ch
  obtain ⟨M₁, hM₁⟩ := exists_aeval_jFull_eq_norm_of_mem_chartAlgFin p (1 + u) h1u
  obtain ⟨M₁', hM₁'⟩ := exists_aeval_jFull_eq_norm_of_mem_chartAlgFin p (1 + u') h1u'

  have hX1m : (X + 1 : Polynomial ℤ).Monic := Polynomial.monic_X_add_C 1
  have hX1d : (X + 1 : Polynomial ℤ).natDegree = 1 := Polynomial.natDegree_X_add_C 1
  have hX1c : (X + 1 : Polynomial ℤ).coeff 0 ≠ 0 := by simp
  have haev1 : ∀ {R : Type} [CommRing R] [Algebra ℤ R] (t : R), Polynomial.aeval t (X + 1 : Polynomial ℤ) = 1 + t := by
    intro R _ _ t; rw [map_add, Polynomial.aeval_X, map_one, add_comm]
  have hdeg₁ : M₁.natDegree = 1 * (p - 1) := by
    have h := natDegree_eq_mul_of_aeval_jFull_eq_norm_aeval_modularUnitSeries p hmem u (Or.inl rfl) (X + 1) hX1m
      (by rw [hX1d]) hX1c M₁ (by rw [haev1]; exact hM₁)
    rwa [hX1d] at h
  have hdeg₁' : M₁'.natDegree = 1 * (p - 1) := by
    have h := natDegree_eq_mul_of_aeval_jFull_eq_norm_aeval_modularUnitSeries p hmem u' (Or.inr rfl) (X + 1) hX1m
      (by rw [hX1d]) hX1c M₁' (by rw [haev1]; exact hM₁')
    rwa [hX1d] at h
  have hdegN : N.natDegree = g.natDegree * (p - 1) :=
    natDegree_eq_mul_of_aeval_jFull_eq_norm_aeval_modularUnitSeries p hmem v hv g hg hD h0 N hN
  have hM₁0 : M₁ ≠ 0 := by intro h; rw [h, Polynomial.natDegree_zero] at hdeg₁; omega
  have hM₁'0 : M₁' ≠ 0 := by intro h; rw [h, Polynomial.natDegree_zero] at hdeg₁'; omega
  have hN0 : N ≠ 0 := by intro h; rw [h, Polynomial.natDegree_zero] at hdegN; have : 1 ≤ g.natDegree * (p - 1) := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega)); omega
  set κ : ℤ := M₁.leadingCoeff with hκ
  set κ' : ℤ := M₁'.leadingCoeff with hκ'

  set ub : ↥(modularFunctionFieldBar p) := ι p u with hub
  set ub' : ↥(modularFunctionFieldBar p) := ι p u' with hub'
  set jb : ↥(modularFunctionFieldBar p) :=
    (⟨coeffEmb (AlgebraicClosure ℚ) jq, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jq_mem_full p)⟩ : ↥(modularFunctionFieldBar p)) with hjb
  set jbp : ↥(modularFunctionFieldBar p) := ι p (jpF p) with hjbp
  have hub'_eq : ub' = (p : ↥(modularFunctionFieldBar p)) ^ 12 * ub⁻¹ := by
    rw [hub', hu', map_mul, map_pow, map_natCast, map_inv₀]

  have hwu : wB p ub = ub' := by rw [hub, wB_ι, frickeInvolutionFull_u p hmem, ← hu, ← hu']
  have hwu' : wB p ub' = ub := by rw [← hwu, wB_wB]
  have hwj : wB p jb = jbp := wB_jB p

  have ho_u : (cuspInftyBar p).ord ub = 1 - p := ord_cuspInftyBar_coeffEmb_modularUnitSeries p hmem
  have hub0 : ub ≠ 0 := ne_zero_of_ord_ne_zero _ (by rw [ho_u]; omega)
  have ho_j : (cuspInftyBar p).ord jb = -1 := ord_cuspInftyBar_coeffEmb_jq p
  have hjb0 : jb ≠ 0 := ne_zero_of_ord_ne_zero _ (by rw [ho_j]; omega)
  have hpb0 : ((p : ↥(modularFunctionFieldBar p))) ^ 12 ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.mpr (NeZero.ne p))
  have hordp : ∀ w : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar p),
      w.ord (((p : ↥(modularFunctionFieldBar p))) ^ 12) = 0 := fun w => by
    rw [ord_pow', show ((p : ↥(modularFunctionFieldBar p))) = ((p : ℤ) : ↥(modularFunctionFieldBar p)) from
      (Int.cast_natCast p).symm, ord_intCast, mul_zero]
  have ho_u' : (cuspInftyBar p).ord ub' = p - 1 := by
    rw [hub'_eq, Place.ord_mul _ hpb0 (inv_ne_zero hub0), hordp, Place.ord_inv, ho_u]; ring
  have hub'0 : ub' ≠ 0 := ne_zero_of_ord_ne_zero _ (by rw [ho_u']; omega)
  have ho_jp : (cuspInftyBar p).ord jbp = -p := by
    rw [ord_cuspInftyBar, hjbp, coe_ι]
    change (coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ p jq)).order = _
    rw [order_coeffEmb _ (IsMonicOfOrder.ne_zero (isMonicOfOrder_jq.qExpand p)), (isMonicOfOrder_jq.qExpand p).1]; ring
  have hjbp0 : jbp ≠ 0 := ne_zero_of_ord_ne_zero _ (by rw [ho_jp]; omega)

  have ho0_u : (cuspZeroBar p).ord ub = p - 1 := by rw [ord_cuspZeroBar, hwu, ho_u']
  have ho0_u' : (cuspZeroBar p).ord ub' = 1 - p := by rw [ord_cuspZeroBar, hwu', ho_u]

  have hmem_u' : ub' ∈ (cuspInftyBar p).toValuationSubring :=
    Place.mem_toValuationSubring_of_ord_nonneg_alt _ hub'0 (by rw [ho_u']; omega)

  have hmem_a : (1 + ub) * ub⁻¹ ∈ (cuspInftyBar p).toValuationSubring := by
    have heq : (1 + ub) * ub⁻¹ = 1 + ub⁻¹ := by rw [add_mul, one_mul, mul_inv_cancel₀ hub0, add_comm]
    rw [heq]
    exact add_mem (one_mem _) (Place.mem_toValuationSubring_of_ord_nonneg_alt _ (inv_ne_zero hub0)
      (by rw [Place.ord_inv, ho_u]; omega))
  have hVa : (cuspInftyBar p).evalAt ((1 + ub) * ub⁻¹) = 1 := by
    apply evalAt_eq_of_ord_sub_pos _ hri 1 hmem_a
    right
    rw [map_one, show (1 + ub) * ub⁻¹ - 1 = ub⁻¹ by rw [add_mul, one_mul, mul_inv_cancel₀ hub0, add_sub_cancel_right],
      Place.ord_inv, ho_u]; omega

  have hmem_b : 1 + ub' ∈ (cuspInftyBar p).toValuationSubring := add_mem (one_mem _) hmem_u'
  have hVb : (cuspInftyBar p).evalAt (1 + ub') = 1 := by
    apply evalAt_eq_of_ord_sub_pos _ hri 1 hmem_b
    right; rw [map_one, add_sub_cancel_left, ho_u']; omega

  have hmem_c : ub * jb ^ (1 - (p : ℤ)) ∈ (cuspInftyBar p).toValuationSubring :=
    Place.mem_toValuationSubring_of_ord_nonneg_alt _ (mul_ne_zero hub0 (zpow_ne_zero _ hjb0))
      (by rw [Place.ord_mul _ hub0 (zpow_ne_zero _ hjb0), Place.ord_zpow, ho_u, ho_j]; ring_nf; rfl)
  have hVc : (cuspInftyBar p).evalAt (ub * jb ^ (1 - (p : ℤ))) = 1 := by
    apply evalAt_eq_of_ord_sub_pos _ hri 1 hmem_c
    have hfac : ub * jb ^ (1 - (p : ℤ)) - algebraMap (AlgebraicClosure ℚ) _ 1 = (ub - jb ^ (p - 1)) * jb ^ (1 - (p : ℤ)) := by
      rw [map_one, sub_mul, ← zpow_natCast, ← zpow_add₀ hjb0, hpm1]; norm_num
    have hcoe : ((ub - jb ^ (p - 1) : ↥(modularFunctionFieldBar p)) : LaurentSeries (AlgebraicClosure ℚ)) =
        coeffEmb (AlgebraicClosure ℚ) (modularUnitSeries p - jq ^ (p - 1)) := by
      rw [map_sub, map_pow]; rfl
    by_cases hne : ub - jb ^ (p - 1) = 0
    · left; rw [← sub_eq_zero, hfac, hne, zero_mul]
    · right
      have hd : modularUnitSeries p - jq ^ (p - 1) ≠ 0 := by
        intro h; apply hne; apply Subtype.ext; rw [hcoe, h, map_zero]; rfl
      have hord : (1 - (p : ℤ)) < (modularUnitSeries p - jq ^ (p - 1)).order := by
        rcases order_u_sub_jq_pow p with hz | hord
        · exact absurd hz hd
        · exact hord
      rw [hfac, Place.ord_mul _ hne (zpow_ne_zero _ hjb0), Place.ord_zpow, ho_j, ord_cuspInftyBar, hcoe,
        order_coeffEmb _ hd]
      nlinarith

  have hmem_f : ub ^ p * jbp ^ (1 - (p : ℤ)) ∈ (cuspInftyBar p).toValuationSubring :=
    Place.mem_toValuationSubring_of_ord_nonneg_alt _ (mul_ne_zero (pow_ne_zero _ hub0) (zpow_ne_zero _ hjbp0))
      (by rw [Place.ord_mul _ (pow_ne_zero _ hub0) (zpow_ne_zero _ hjbp0), Place.ord_zpow, ord_pow', ho_u, ho_jp]; ring_nf; rfl)
  have hVf : (cuspInftyBar p).evalAt (ub ^ p * jbp ^ (1 - (p : ℤ))) = 1 := by
    apply evalAt_eq_of_ord_sub_pos _ hri 1 hmem_f
    have hfac : ub ^ p * jbp ^ (1 - (p : ℤ)) - algebraMap (AlgebraicClosure ℚ) _ 1 =
        (ub ^ p - jbp ^ (p - 1)) * jbp ^ (1 - (p : ℤ)) := by
      rw [map_one, sub_mul, ← zpow_natCast (jbp) (p - 1), ← zpow_add₀ hjbp0, hpm1]; norm_num
    have hcoe : ((ub ^ p - jbp ^ (p - 1) : ↥(modularFunctionFieldBar p)) : LaurentSeries (AlgebraicClosure ℚ)) =
        coeffEmb (AlgebraicClosure ℚ) (modularUnitSeries p ^ p - (qExpand ℚ p jq) ^ (p - 1)) := by
      rw [map_sub, map_pow, map_pow]; rfl
    by_cases hne : ub ^ p - jbp ^ (p - 1) = 0
    · left; rw [← sub_eq_zero, hfac, hne, zero_mul]
    · right
      have hd : modularUnitSeries p ^ p - (qExpand ℚ p jq) ^ (p - 1) ≠ 0 := by
        intro h; apply hne; apply Subtype.ext; rw [hcoe, h, map_zero]; rfl
      have hord : ((p : ℤ) * (1 - p)) < (modularUnitSeries p ^ p - (qExpand ℚ p jq) ^ (p - 1)).order := by
        rcases order_u_pow_sub_jqp_pow p with hz | hord
        · exact absurd hz hd
        · exact hord
      rw [hfac, Place.ord_mul _ hne (zpow_ne_zero _ hjbp0), Place.ord_zpow, ho_jp, ord_cuspInftyBar, hcoe,
        order_coeffEmb _ hd]
      nlinarith

  set A : ↥(modularFunctionFieldBar p) := (1 + ub) * (1 + ub') ^ p * jb ^ (1 - (p : ℤ)) with hA
  have hA_fac : A = ((1 + ub) * ub⁻¹) * (1 + ub') ^ p * (ub * jb ^ (1 - (p : ℤ))) := by
    rw [hA, show ((1 + ub) * ub⁻¹) * (1 + ub') ^ p * (ub * jb ^ (1 - (p : ℤ))) =
      (1 + ub) * (1 + ub') ^ p * jb ^ (1 - (p : ℤ)) * (ub⁻¹ * ub) by ring, inv_mul_cancel₀ hub0, mul_one]
  have hmem_A : A ∈ (cuspInftyBar p).toValuationSubring := by
    rw [hA_fac]; exact mul_mem (mul_mem hmem_a (pow_mem hmem_b p)) hmem_c
  have hAinf : (cuspInftyBar p).evalAt A = 1 := by
    rw [hA_fac, Place.evalAt_mul_of_mem _ hri (mul_mem hmem_a (pow_mem hmem_b p)) hmem_c,
      Place.evalAt_mul_of_mem _ hri hmem_a (pow_mem hmem_b p), evalAt_pow' _ hri hmem_b, hVa, hVb, hVc]
    ring

  have hwA : wB p A = (1 + ub') * ((1 + ub) * ub⁻¹) ^ p * (ub ^ p * jbp ^ (1 - (p : ℤ))) := by
    rw [mul_pow, show (1 + ub') * ((1 + ub) ^ p * ub⁻¹ ^ p) * (ub ^ p * jbp ^ (1 - (p : ℤ))) =
        (1 + ub') * (1 + ub) ^ p * jbp ^ (1 - (p : ℤ)) * ((ub⁻¹) ^ p * ub ^ p) by ring,
      ← mul_pow, inv_mul_cancel₀ hub0, one_pow, mul_one, hA, map_mul, map_mul, map_pow, map_add, map_add,
      map_one, map_zpow₀, hwu, hwu', hwj]
  have hmem_wA : wB p A ∈ (cuspInftyBar p).toValuationSubring := by
    rw [hwA]; exact mul_mem (mul_mem hmem_b (pow_mem hmem_a p)) hmem_f
  have hwAval : (cuspInftyBar p).evalAt (wB p A) = 1 := by
    rw [hwA, Place.evalAt_mul_of_mem _ hri (mul_mem hmem_b (pow_mem hmem_a p)) hmem_f,
      Place.evalAt_mul_of_mem _ hri hmem_b (pow_mem hmem_a p), evalAt_pow' _ hri hmem_a, hVa, hVb, hVf]
    ring
  have hA0 : (cuspZeroBar p).evalAt A = 1 := by rw [evalAt_cuspZeroBar p A hmem_wA, hwAval]
  have hA_ordinf : (cuspInftyBar p).ord A = 0 :=
    ord_eq_zero_of_evalAt_ne_zero _ hri hmem_A (by rw [hAinf]; exact one_ne_zero)
  have hA_ord0 : (cuspZeroBar p).ord A = 0 := by
    rw [ord_cuspZeroBar]
    exact ord_eq_zero_of_evalAt_ne_zero _ hri hmem_wA (by rw [hwAval]; exact one_ne_zero)
  have hAne : A ≠ 0 := by intro h; rw [h, evalAt_zero'] at hAinf; exact zero_ne_one hAinf

  have hfib : (jLineBarPlaceInfty p).fiber ↥(modularFunctionFieldBar p) = {cuspInftyBar p, cuspZeroBar p} := by
    rw [Place.fiber_eq_fiberOver, fiberOver_eq p hmem]
  have hrat : ∀ w ∈ (jLineBarPlaceInfty p).fiber ↥(modularFunctionFieldBar p), Place.IsRational w :=
    fun w _ => isRational_FB p w
  have hccbA := Place.evalAt_norm_eq_prod_fiber (K := AlgebraicClosure ℚ) (F := ↥(jLineBar p))
    (F' := ↥(modularFunctionFieldBar p)) (jLineBarPlaceInfty p) A hAne hvI hrat (by
      intro w hw
      rw [hfib, Finset.mem_insert, Finset.mem_singleton] at hw
      rcases hw with rfl | rfl
      exacts [hA_ordinf, hA_ord0])
  rw [hfib, Finset.prod_pair (cuspInftyBar_ne_cuspZeroBar p hmem), ramificationIndex_cuspInftyBar,
    ramificationIndex_cuspZeroBar p hmem, pow_one, hAinf, hA0, one_pow, one_mul] at hccbA

  have hjE0 : jE p ≠ 0 := jE_ne_zero p
  have hn1 : Algebra.norm ↥(jLineBar p) (1 + ub) = Polynomial.aeval (jE p) M₁ := by
    rw [show 1 + ub = ι p (1 + u) by rw [map_add, map_one]]; exact hnormE _ _ hM₁
  have hn1' : Algebra.norm ↥(jLineBar p) (1 + ub') = Polynomial.aeval (jE p) M₁' := by
    rw [show 1 + ub' = ι p (1 + u') by rw [map_add, map_one]]; exact hnormE _ _ hM₁'
  have hnj : Algebra.norm ↥(jLineBar p) (jb ^ (1 - (p : ℤ))) = (jE p) ^ ((1 - (p : ℤ)) * (p + 1)) := by
    rw [show jb = algebraMap ↥(jLineBar p) ↥(modularFunctionFieldBar p) (jE p) from rfl, ← map_zpow₀,
      Algebra.norm_algebraMap, finrank_EB, dedekindPsi_prime, ← zpow_natCast, ← zpow_mul]
    push_cast; ring_nf
  have hNA : Algebra.norm ↥(jLineBar p) A =
      (Polynomial.aeval (jE p) M₁ * (jE p) ^ (-(M₁.natDegree : ℤ))) *
        (Polynomial.aeval (jE p) M₁' * (jE p) ^ (-(M₁'.natDegree : ℤ))) ^ p := by
    rw [hA, map_mul, map_mul, map_pow, hn1, hn1', hnj, regroup₁ _ _ _ hjE0, hdeg₁, hdeg₁']
    congr 1
    push_cast [hp1]; ring
  obtain ⟨hK1m, hK1o, hK1ne⟩ := lead_part (jLineBarPlaceInfty p) (jE p) (ord_jLineBarPlaceInfty_jE p) M₁ hM₁0
  obtain ⟨hK1m', hK1o', hK1ne'⟩ := lead_part (jLineBarPlaceInfty p) (jE p) (ord_jLineBarPlaceInfty_jE p) M₁' hM₁'0
  have hevA : (jLineBarPlaceInfty p).evalAt (Algebra.norm ↥(jLineBar p) A) =
      ((M₁.leadingCoeff : ℤ) : AlgebraicClosure ℚ) * ((M₁'.leadingCoeff : ℤ) : AlgebraicClosure ℚ) ^ p := by
    rw [hNA]
    erw [Place.evalAt_mul_of_mem _ hvI hK1m (pow_mem hK1m' p), evalAt_pow' _ hvI hK1m',
      evalAt_aeval_mul_zpow_neg_natDegree _ hvI (jE p) (ord_jLineBarPlaceInfty_jE p) M₁ hM₁0,
      evalAt_aeval_mul_zpow_neg_natDegree _ hvI (jE p) (ord_jLineBarPlaceInfty_jE p) M₁' hM₁'0]
  erw [hevA] at hccbA

  have hκκ' : κ * κ' ^ p = 1 := by rw [hκ, hκ']; exact_mod_cast hccbA
  have hκu : IsUnit κ := IsUnit.of_mul_eq_one _ hκκ'
  have hκ'u : IsUnit κ' := by
    have : IsUnit (κ' ^ p) := IsUnit.of_mul_eq_one κ (by rw [mul_comm]; exact hκκ')
    exact (isUnit_pow_iff (by omega)).mp this

  set D := g.natDegree with hDdef
  set Q : Polynomial ℤ := (X + 1) ^ D with hQ
  have hQm : Q.Monic := hX1m.pow D
  have hQd : Q.natDegree = D := by rw [hQ, Polynomial.natDegree_pow, hX1d, mul_one]
  have hQc : Q.coeff 0 = 1 := by rw [hQ, Polynomial.coeff_zero_eq_eval_zero]; simp
  have hg0K : ((g.coeff 0 : ℤ) : AlgebraicClosure ℚ) ≠ 0 := by exact_mod_cast h0
  have haevQ : ∀ (t : ↥(modularFunctionFieldFull p)), Polynomial.aeval (ι p t) Q = ι p (1 + t) ^ D := by
    intro t; rw [hQ, map_pow, haev1, map_add, map_one]
  have hnorm_div : ∀ (a b : ↥(modularFunctionFieldBar p)), b ≠ 0 →
      Algebra.norm ↥(jLineBar p) (a / b) = Algebra.norm ↥(jLineBar p) a / Algebra.norm ↥(jLineBar p) b := by
    intro a b hb
    rw [eq_div_iff (Algebra.norm_ne_zero_iff.mpr hb), ← map_mul, div_mul_cancel₀ _ hb]
  rcases hv with rfl | rfl
  ·
    set f : ↥(modularFunctionFieldBar p) := Polynomial.aeval ub g / Polynomial.aeval ub Q with hf
    obtain ⟨hfm, hfo, hfne, hfval⟩ := pole_part (cuspInftyBar p) hri ub (by rw [ho_u]; omega) g Q hg hQm (by rw [hQd])
    have hwf : wB p f = Polynomial.aeval ub' g / Polynomial.aeval ub' Q := by
      rw [hf, map_div₀, hwaeval, hwaeval, hwu]
    obtain ⟨hwfm, hwfo, hwfne, hwfval⟩ := zero_part (cuspInftyBar p) hri ub' (by rw [ho_u']; omega) g Q hg0K hQc
    have hf0 : (cuspZeroBar p).evalAt f = (g.coeff 0 : AlgebraicClosure ℚ) := by
      rw [evalAt_cuspZeroBar p f (by rw [hwf]; exact hwfm), hwf, hwfval]
    have hford0 : (cuspZeroBar p).ord f = 0 := by rw [ord_cuspZeroBar, hwf]; exact hwfo
    have hccbf := Place.evalAt_norm_eq_prod_fiber (K := AlgebraicClosure ℚ) (F := ↥(jLineBar p))
      (F' := ↥(modularFunctionFieldBar p)) (jLineBarPlaceInfty p) f hfne hvI hrat (by
        intro w hw
        rw [hfib, Finset.mem_insert, Finset.mem_singleton] at hw
        rcases hw with rfl | rfl
        exacts [hfo, hford0])
    rw [hfib, Finset.prod_pair (cuspInftyBar_ne_cuspZeroBar p hmem), ramificationIndex_cuspInftyBar,
      ramificationIndex_cuspZeroBar p hmem, pow_one, hfval, hf0, one_mul] at hccbf

    have hNf : Algebra.norm ↥(jLineBar p) f =
        (Polynomial.aeval (jE p) N * (jE p) ^ (-(N.natDegree : ℤ))) /
          (Polynomial.aeval (jE p) M₁ * (jE p) ^ (-(M₁.natDegree : ℤ))) ^ D := by
      have hexp : ((D : ℕ) : ℤ) * -((M₁.natDegree : ℕ) : ℤ) = -((N.natDegree : ℕ) : ℤ) := by
        rw [hdegN, hdeg₁]; push_cast [hp1]; ring
      rw [hf, hnorm_div _ _ (div_ne_zero_iff.mp hfne).2,
        ← hιaeval, ← hx, hnormE x N hN, haevQ, map_pow,
        ← show 1 + ub = ι p (1 + u) by rw [map_add, map_one], hn1,
        regroup₂ _ _ _ hjE0 (-(M₁.natDegree : ℤ)) D, hexp]
    obtain ⟨hKNm, hKNo, hKNne⟩ := lead_part (jLineBarPlaceInfty p) (jE p) (ord_jLineBarPlaceInfty_jE p) N hN0
    have hevf : (jLineBarPlaceInfty p).evalAt (Algebra.norm ↥(jLineBar p) f) =
        ((N.leadingCoeff : ℤ) : AlgebraicClosure ℚ) / ((M₁.leadingCoeff : ℤ) : AlgebraicClosure ℚ) ^ D := by
      have hden0 : (Polynomial.aeval (jE p) M₁ * (jE p) ^ (-(M₁.natDegree : ℤ))) ^ D ≠ 0 := pow_ne_zero D hK1ne
      have hdeno : (jLineBarPlaceInfty p).ord ((Polynomial.aeval (jE p) M₁ * (jE p) ^ (-(M₁.natDegree : ℤ))) ^ D) = 0 := by
        have h := ord_pow' (jLineBarPlaceInfty p) (Polynomial.aeval (jE p) M₁ * (jE p) ^ (-(M₁.natDegree : ℤ))) D
        erw [h, hK1o, mul_zero]
      rw [hNf]
      erw [evalAt_div_of_ord_eq_zero _ hvI hKNm hden0 hdeno, evalAt_pow' _ hvI hK1m,
        evalAt_aeval_mul_zpow_neg_natDegree _ hvI (jE p) (ord_jLineBarPlaceInfty_jE p) N hN0,
        evalAt_aeval_mul_zpow_neg_natDegree _ hvI (jE p) (ord_jLineBarPlaceInfty_jE p) M₁ hM₁0]
    erw [hevf] at hccbf

    have hκD0 : ((κ : ℤ) : AlgebraicClosure ℚ) ^ D ≠ 0 := pow_ne_zero _ (by exact_mod_cast hκu.ne_zero)
    rw [← hκ, div_eq_iff hκD0] at hccbf
    have key : N.leadingCoeff = (g.coeff 0) ^ p * κ ^ D := by exact_mod_cast hccbf
    obtain ⟨ε, hε⟩ := hκu.pow D
    exact ⟨ε, p, by rw [key, hε]; ring⟩
  ·
    set f : ↥(modularFunctionFieldBar p) := Polynomial.aeval ub' g / Polynomial.aeval ub' Q with hf
    obtain ⟨hfm, hfo, hfne, hfval⟩ := zero_part (cuspInftyBar p) hri ub' (by rw [ho_u']; omega) g Q hg0K hQc
    have hwf : wB p f = Polynomial.aeval ub g / Polynomial.aeval ub Q := by
      rw [hf, map_div₀, hwaeval, hwaeval, hwu']
    obtain ⟨hwfm, hwfo, hwfne, hwfval⟩ := pole_part (cuspInftyBar p) hri ub (by rw [ho_u]; omega) g Q hg hQm (by rw [hQd])
    have hf0 : (cuspZeroBar p).evalAt f = 1 := by
      rw [evalAt_cuspZeroBar p f (by rw [hwf]; exact hwfm), hwf, hwfval]
    have hford0 : (cuspZeroBar p).ord f = 0 := by rw [ord_cuspZeroBar, hwf]; exact hwfo
    have hccbf := Place.evalAt_norm_eq_prod_fiber (K := AlgebraicClosure ℚ) (F := ↥(jLineBar p))
      (F' := ↥(modularFunctionFieldBar p)) (jLineBarPlaceInfty p) f hfne hvI hrat (by
        intro w hw
        rw [hfib, Finset.mem_insert, Finset.mem_singleton] at hw
        rcases hw with rfl | rfl
        exacts [hfo, hford0])
    rw [hfib, Finset.prod_pair (cuspInftyBar_ne_cuspZeroBar p hmem), ramificationIndex_cuspInftyBar,
      ramificationIndex_cuspZeroBar p hmem, pow_one, hfval, hf0, one_pow, mul_one] at hccbf
    have hNf : Algebra.norm ↥(jLineBar p) f =
        (Polynomial.aeval (jE p) N * (jE p) ^ (-(N.natDegree : ℤ))) /
          (Polynomial.aeval (jE p) M₁' * (jE p) ^ (-(M₁'.natDegree : ℤ))) ^ D := by
      have hexp : ((D : ℕ) : ℤ) * -((M₁'.natDegree : ℕ) : ℤ) = -((N.natDegree : ℕ) : ℤ) := by
        rw [hdegN, hdeg₁']; push_cast [hp1]; ring
      rw [hf, hnorm_div _ _ (div_ne_zero_iff.mp hfne).2,
        ← hιaeval, ← hx, hnormE x N hN, haevQ, map_pow,
        ← show 1 + ub' = ι p (1 + u') by rw [map_add, map_one], hn1',
        regroup₂ _ _ _ hjE0 (-(M₁'.natDegree : ℤ)) D, hexp]
    obtain ⟨hKNm, hKNo, hKNne⟩ := lead_part (jLineBarPlaceInfty p) (jE p) (ord_jLineBarPlaceInfty_jE p) N hN0
    have hevf : (jLineBarPlaceInfty p).evalAt (Algebra.norm ↥(jLineBar p) f) =
        ((N.leadingCoeff : ℤ) : AlgebraicClosure ℚ) / ((M₁'.leadingCoeff : ℤ) : AlgebraicClosure ℚ) ^ D := by
      have hden0 : (Polynomial.aeval (jE p) M₁' * (jE p) ^ (-(M₁'.natDegree : ℤ))) ^ D ≠ 0 := pow_ne_zero D hK1ne'
      have hdeno : (jLineBarPlaceInfty p).ord ((Polynomial.aeval (jE p) M₁' * (jE p) ^ (-(M₁'.natDegree : ℤ))) ^ D) = 0 := by
        have h := ord_pow' (jLineBarPlaceInfty p) (Polynomial.aeval (jE p) M₁' * (jE p) ^ (-(M₁'.natDegree : ℤ))) D
        erw [h, hK1o', mul_zero]
      rw [hNf]
      erw [evalAt_div_of_ord_eq_zero _ hvI hKNm hden0 hdeno, evalAt_pow' _ hvI hK1m',
        evalAt_aeval_mul_zpow_neg_natDegree _ hvI (jE p) (ord_jLineBarPlaceInfty_jE p) N hN0,
        evalAt_aeval_mul_zpow_neg_natDegree _ hvI (jE p) (ord_jLineBarPlaceInfty_jE p) M₁' hM₁'0]
    erw [hevf] at hccbf
    have hκD0 : ((κ' : ℤ) : AlgebraicClosure ℚ) ^ D ≠ 0 := pow_ne_zero _ (by exact_mod_cast hκ'u.ne_zero)
    rw [← hκ', div_eq_iff hκD0] at hccbf
    have key : N.leadingCoeff = (g.coeff 0) * κ' ^ D := by exact_mod_cast hccbf
    obtain ⟨ε, hε⟩ := hκ'u.pow D
    exact ⟨ε, 1, by rw [key, hε, pow_one]; ring⟩

end
p2m_reactivate "P2MW.S_ModularCurve_exists_leadingCoeff_eq_mul_pow_of_aeval_jFull_eq_norm_aeval_modularUnitSeries.CU2i"

end S_ModularCurve_exists_leadingCoeff_eq_mul_pow_of_aeval_jFull_eq_norm_aeval_modularUnitSeries
end P2MW
export P2MW.S_ModularCurve_exists_leadingCoeff_eq_mul_pow_of_aeval_jFull_eq_norm_aeval_modularUnitSeries (solution)
