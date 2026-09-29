-- Prove2me | solution 1 for ModularCurve.natDegree_eq_mul_of_aeval_jFull_eq_norm_aeval_modularUnitSeries
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/2b617503-3d3c-5e11-8eb4-6d10c867a6d0

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
import Definitions.Def_ModularCurve_X0ModL
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_natDegree_eq_mul_of_aeval_jFull_eq_norm_aeval_modularUnitSeries
p2m_attr_erase "instance" "AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none"

set_option autoImplicit false

open ModularCurve Polynomial AlgebraicCurve IntermediateField

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
p2m_reactivate "P2MW.S_ModularCurve_natDegree_eq_mul_of_aeval_jFull_eq_norm_aeval_modularUnitSeries.CU2i"

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
p2m_reactivate "P2MW.S_ModularCurve_natDegree_eq_mul_of_aeval_jFull_eq_norm_aeval_modularUnitSeries.CU2i"
end CU2i
p2m_reactivate "P2MW.S_ModularCurve_natDegree_eq_mul_of_aeval_jFull_eq_norm_aeval_modularUnitSeries.CU2i"

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
p2m_reactivate "P2MW.S_ModularCurve_natDegree_eq_mul_of_aeval_jFull_eq_norm_aeval_modularUnitSeries.CU2i"
end CU2i
p2m_reactivate "P2MW.S_ModularCurve_natDegree_eq_mul_of_aeval_jFull_eq_norm_aeval_modularUnitSeries.CU2i"

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
p2m_reactivate "P2MW.S_ModularCurve_natDegree_eq_mul_of_aeval_jFull_eq_norm_aeval_modularUnitSeries.CU2i"
end CU2i
p2m_reactivate "P2MW.S_ModularCurve_natDegree_eq_mul_of_aeval_jFull_eq_norm_aeval_modularUnitSeries.CU2i"

open CU2i in
set_option maxHeartbeats 6400000 in
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
    N.natDegree = g.natDegree * (p - 1) := by
  classical

  set u : ↥(modularFunctionFieldFull p) := ⟨modularUnitSeries p, hmem⟩ with hu
  set x : ↥(modularFunctionFieldFull p) := Polynomial.aeval v g with hx
  haveI : FiniteDimensional ↥(jLineBar p) ↥(modularFunctionFieldBar p) :=
    finiteDimensional_adjoin_coeffEmb_jq_of_neZero p
  haveI : Algebra.IsIntegral ↥(jLineBar p) ↥(modularFunctionFieldBar p) := Algebra.IsIntegral.of_finite _ _
  haveI : Algebra.IsSeparable ↥(jLineBar p) ↥(modularFunctionFieldBar p) := Algebra.IsSeparable.of_integral _ _
  have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le

  have hιcomp : (ι p).comp (algebraMap ℤ ↥(modularFunctionFieldFull p)) = algebraMap ℤ ↥(modularFunctionFieldBar p) :=
    RingHom.ext_int _ _
  have hιaeval : ∀ (t : ↥(modularFunctionFieldFull p)) (P : Polynomial ℤ),
      ι p (Polynomial.aeval t P) = Polynomial.aeval (ι p t) P := by
    intro t P
    rw [Polynomial.aeval_def, Polynomial.hom_eval₂, hιcomp, ← Polynomial.aeval_def]

  have hu_inf : (cuspInftyBar p).ord (ι p u) = 1 - p := ord_cuspInftyBar_coeffEmb_modularUnitSeries p hmem
  have hu_zero : (cuspZeroBar p).ord (ι p u) = p - 1 := ord_cuspZeroBar_coeffEmb_modularUnitSeries p hmem
  have hu0 : ι p u ≠ 0 := ne_zero_of_ord_ne_zero _ (by rw [hu_inf]; omega)

  have hsum : (cuspInftyBar p).ord (ι p x) + (cuspZeroBar p).ord (ι p x) = g.natDegree * (1 - (p : ℤ)) := by
    rw [hx, hιaeval]
    rcases hv with rfl | rfl
    · rw [ord_aeval_of_ord_neg _ (ι p u) (by rw [hu_inf]; omega) g hg.ne_zero,
        ord_aeval_of_ord_pos _ (ι p u) (by rw [hu_zero]; omega) g h0, hu_inf]
      ring
    · have hp0 : ((p : ↥(modularFunctionFieldBar p))) ^ 12 ≠ 0 :=
        pow_ne_zero _ (Nat.cast_ne_zero.mpr (NeZero.ne p))
      have hordp : ∀ w : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar p),
          w.ord (((p : ↥(modularFunctionFieldBar p))) ^ 12) = 0 := fun w => by
        rw [ord_pow', show ((p : ↥(modularFunctionFieldBar p))) = ((p : ℤ) : ↥(modularFunctionFieldBar p)) by norm_cast,
          ord_intCast, mul_zero]
      have hιv : ι p ((p : ↥(modularFunctionFieldFull p)) ^ 12 * u⁻¹) =
          ((p : ↥(modularFunctionFieldBar p))) ^ 12 * (ι p u)⁻¹ := by
        rw [map_mul, map_pow, map_natCast, map_inv₀]
      have hv_inf : (cuspInftyBar p).ord (ι p ((p : ↥(modularFunctionFieldFull p)) ^ 12 * u⁻¹)) = p - 1 := by
        rw [hιv, Place.ord_mul _ hp0 (inv_ne_zero hu0), hordp, Place.ord_inv, hu_inf]; ring
      have hv_zero : (cuspZeroBar p).ord (ι p ((p : ↥(modularFunctionFieldFull p)) ^ 12 * u⁻¹)) = 1 - p := by
        rw [hιv, Place.ord_mul _ hp0 (inv_ne_zero hu0), hordp, Place.ord_inv, hu_zero]; ring
      rw [ord_aeval_of_ord_pos _ _ (by rw [hv_inf]; omega) g h0,
        ord_aeval_of_ord_neg _ _ (by rw [hv_zero]; omega) g hg.ne_zero, hv_zero]
      ring

  have hιx0 : ι p x ≠ 0 := by
    intro h
    rw [h, Place.ord_zero, Place.ord_zero] at hsum
    have h1 : (1 : ℤ) - p < 0 := by omega
    have h2 : (1 : ℤ) ≤ g.natDegree := by exact_mod_cast hD
    nlinarith

  have hnv := Place.ord_norm_eq_sum_fiberOver (K := AlgebraicClosure ℚ) (F := ↥(jLineBar p))
    (F' := ↥(modularFunctionFieldBar p)) (jLineBarPlaceInfty p) hιx0
  rw [fiberOver_eq p hmem, Finset.sum_pair (cuspInftyBar_ne_cuspZeroBar p hmem), inertiaDeg_eq_one,
    inertiaDeg_eq_one, Nat.cast_one, one_mul, one_mul, hsum, norm_ι] at hnv

  have hN0 : N ≠ 0 := by
    rintro rfl
    rw [map_zero, eq_comm, map_eq_zero_iff _ (FaithfulSMul.algebraMap_injective _ _), Algebra.norm_eq_zero_iff] at hN
    exact hιx0 (by rw [hN, map_zero])
  have hjN : (cuspInftyBar p).ord (algebraMap ↥(jLineBar p) ↥(modularFunctionFieldBar p)
      (ιE p (Algebra.norm ↥(IntermediateField.adjoin ℚ ({IgusaScheme.jFull p} : Set ↥(modularFunctionFieldFull p))) x))) =
      - N.natDegree := by
    rw [← ι_algebraMap_EF, ← hN, hιaeval, ι_jF,
      ord_aeval_of_ord_neg _ _ (by rw [ord_cuspInftyBar_coeffEmb_jq]; norm_num) N hN0, ord_cuspInftyBar_coeffEmb_jq]
    ring
  rw [Place.ord_restrict (F := ↥(jLineBar p)), restrict_eq_of_isCusp p _ (isCusp_cuspInftyBar p),
    ramificationIndex_cuspInftyBar, Nat.cast_one, one_mul, hnv] at hjN

  have hp1 : 1 ≤ p := by omega
  zify [hp1]
  linarith

end
p2m_reactivate "P2MW.S_ModularCurve_natDegree_eq_mul_of_aeval_jFull_eq_norm_aeval_modularUnitSeries.CU2i"

end S_ModularCurve_natDegree_eq_mul_of_aeval_jFull_eq_norm_aeval_modularUnitSeries
end P2MW
export P2MW.S_ModularCurve_natDegree_eq_mul_of_aeval_jFull_eq_norm_aeval_modularUnitSeries (solution)
