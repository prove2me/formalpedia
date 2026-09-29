-- Prove2me | solution 1 for ModularCurve.place_eq_of_modularPolynomial_rootMultiplicity_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/8098e41f-a666-5b29-8248-5db0e18806f7

import Definitions.Def_ModularCurve_MazurStepThreeInputs
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_AlgebraicCurve_PlacesOverDVR
import Theorems.Thm_P2M_Dup_AlgebraicCurve_Place_mem_iff_ord_nonneg
import Theorems.Thm_AlgebraicCurve_Place_inertiaDeg_pos_of_finiteDimensional
import Theorems.Thm_AlgebraicCurve_normFormulaAlong
import Theorems.Thm_AlgebraicCurve_separableAlong_of_charZero
import Theorems.Thm_ModularCurve_hasPrincipalDivisors_modularFunctionFieldBar_unconditional
import Theorems.Thm_ModularCurve_modularFunctionFieldBar_eq_restrictScalars
import Theorems.Thm_ModularCurve_finiteDimensional_adjoin_coeffEmb_jq
import Theorems.Thm_ModularCurve_transcendental_coeffEmb_jq
import Theorems.Thm_ModularCurve_coeffEmb_jq
import Theorems.Thm_ModularCurve_coeffEmb_jqN
import Theorems.Thm_ModularCurve_ModularPolynomialData_eval_jqNModC_mul_eq_zero
import Definitions.Def_ModularCurve_JqCoeff
import Theorems.Thm_ModularCurve_finrank_adjoin_jqNModC_eq_of_prime
import Theorems.Thm_ModularCurve_isIntegral_jqNModC_of_modularPolynomialData
import Theorems.Thm_ModularCurve_transcendental_jqModC
import Mathlib.RingTheory.Norm.Transitivity
import Mathlib.RingTheory.Localization.Integral
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_place_eq_of_modularPolynomial_rootMultiplicity_eq_one
p2m_attr_erase "instance" "AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation"
p2m_attr_erase "simp" "AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.eisensteinNumerator_nineteen"
p2m_attr_erase "simp" "ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000

noncomputable section

p2m_open "AlgebraicCurve ModularCurve~dedekindPsi_prime Polynomial IsDedekindDomain"

namespace N4dSol

namespace SR

private theorem eq_singleton_of_sum_eq_one {ι : Type*} (S : Finset ι) (g : ι → ℕ) (hg : ∀ x ∈ S, 1 ≤ g x)
    (h : ∑ x ∈ S, g x = 1) : ∃ a, S = {a} ∧ g a = 1 := by
  have hcard : S.card ≤ 1 :=
    calc S.card = ∑ x ∈ S, 1 := Finset.card_eq_sum_ones S
      _ ≤ ∑ x ∈ S, g x := Finset.sum_le_sum hg
      _ = 1 := h
  have hne : S.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    rintro rfl
    simp at h
  have hc1 : S.card = 1 := le_antisymm hcard (Finset.card_pos.mpr hne)
  obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp hc1
  exact ⟨a, rfl, by simpa using h⟩

section OnePlace

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

private theorem ord_coe_eq_zero_of_isUnit (v : Place K F) {u : v.toValuationSubring} (hu : IsUnit u) :
    ((u : F) ≠ 0) ∧ v.ord (u : F) = 0 := by
  have hu0 : (u : F) ≠ 0 := by
    intro h
    have : u = 0 := Subtype.ext h
    rw [this] at hu
    exact not_isUnit_zero hu
  refine ⟨hu0, ?_⟩
  have hnonneg : 0 ≤ v.ord (u : F) := (v.mem_iff_ord_nonneg hu0).mp u.2
  have hnotmax : u ∉ IsLocalRing.maximalIdeal v.toValuationSubring := fun h => h hu
  have : ¬ 0 < v.ord (u : F) := by
    intro hpos
    exact hnotmax ((v.mem_maximalIdeal_iff_ord_pos hu0 u.2).mpr hpos)
  omega

private theorem ord_add_eq_zero (w : Place K F) {u z : F} (hu0 : u ≠ 0) (hu : w.ord u = 0)
    (humem : u ∈ w.toValuationSubring) (hz : z ∈ w.toValuationSubring) (hzpos : z = 0 ∨ 0 < w.ord z) :
    u + z ≠ 0 ∧ w.ord (u + z) = 0 := by
  rcases hzpos with rfl | hzpos
  · simpa using ⟨hu0, hu⟩
  have hz0 : z ≠ 0 := by rintro rfl; simp at hzpos
  have hzmax : (⟨z, hz⟩ : w.toValuationSubring) ∈ IsLocalRing.maximalIdeal w.toValuationSubring :=
    (w.mem_maximalIdeal_iff_ord_pos hz0 hz).mpr hzpos
  have humax : (⟨u, humem⟩ : w.toValuationSubring) ∉ IsLocalRing.maximalIdeal w.toValuationSubring := by
    rw [w.mem_maximalIdeal_iff_ord_pos hu0 humem]; omega
  have hsmem : u + z ∈ w.toValuationSubring := add_mem humem hz
  have hne : u + z ≠ 0 := by
    intro h
    apply humax
    have : (⟨u, humem⟩ : w.toValuationSubring) = -⟨z, hz⟩ :=
      Subtype.ext (eq_neg_of_add_eq_zero_left h)
    rw [this]; exact neg_mem hzmax
  refine ⟨hne, ?_⟩
  have hnonneg : 0 ≤ w.ord (u + z) := (w.mem_iff_ord_nonneg hne).mp hsmem
  by_contra hcon
  have hpos : 0 < w.ord (u + z) := lt_of_le_of_ne hnonneg (Ne.symm hcon)
  have hsmax : (⟨u + z, hsmem⟩ : w.toValuationSubring) ∈ IsLocalRing.maximalIdeal w.toValuationSubring :=
    (w.mem_maximalIdeal_iff_ord_pos hne hsmem).mpr hpos
  apply humax
  have : (⟨u, humem⟩ : w.toValuationSubring) = ⟨u + z, hsmem⟩ - ⟨z, hz⟩ := Subtype.ext (by simp)
  rw [this]; exact sub_mem hsmax hzmax

private theorem exists_taylor (v : Place K F) (Q : Polynomial v.toValuationSubring) (b : v.toValuationSubring) :
    ∃ S : Polynomial v.toValuationSubring,
      Q - C (Q.eval b) = (X - C b) * S ∧ S.eval b = Q.derivative.eval b := by
  have h : (X - C b) * ((Q - C (Q.eval b)) /ₘ (X - C b)) = Q - C (Q.eval b) := by
    rw [mul_divByMonic_eq_iff_isRoot]; simp [IsRoot]
  refine ⟨(Q - C (Q.eval b)) /ₘ (X - C b), h.symm, ?_⟩
  have hd := congrArg Polynomial.derivative h
  simp only [derivative_mul, derivative_sub, derivative_C, derivative_X, sub_zero, one_mul] at hd
  have he := congrArg (Polynomial.eval b) hd
  simp only [eval_add, eval_mul, eval_sub, eval_X, eval_C, sub_self, zero_mul, add_zero] at he
  exact he

end OnePlace

section Engine

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
  [Algebra F F'] [IsScalarTower K F F']

omit [Algebra K F'] [IsScalarTower K F F'] in

private theorem aeval_taylor (v : Place K F) {Q S : Polynomial v.toValuationSubring} {b : v.toValuationSubring}
    (hS : Q - C (Q.eval b) = (X - C b) * S) (x : F') :
    aeval x (Q.map (algebraMap v.toValuationSubring F)) - algebraMap F F' ((Q.eval b : v.toValuationSubring) : F)
      = (x - algebraMap F F' (b : F)) * aeval x (S.map (algebraMap v.toValuationSubring F)) := by
  have h := congrArg (fun P : Polynomial v.toValuationSubring => aeval x (P.map (algebraMap v.toValuationSubring F))) hS
  simpa [Polynomial.map_sub, Polynomial.map_mul, aeval_C, aeval_X, ← IsScalarTower.algebraMap_apply] using h

variable [Algebra.IsIntegral F F']

private theorem algebraMap_mem_of_restrict_eq {w : Place K F'} {v : Place K F} (hw : w.restrict F = v)
    (r : v.toValuationSubring) : algebraMap F F' (r : F) ∈ w.toValuationSubring := by
  have : (r : F) ∈ (w.restrict F).toValuationSubring := by rw [hw]; exact r.2
  exact (Place.mem_restrict_iff w).mp this

private theorem aeval_mem_of_restrict_eq {w : Place K F'} {v : Place K F} (hw : w.restrict F = v)
    (S : Polynomial v.toValuationSubring) {x : F'} (hxmem : x ∈ w.toValuationSubring) :
    aeval x (S.map (algebraMap v.toValuationSubring F)) ∈ w.toValuationSubring := by
  rw [aeval_eq_sum_range]
  refine Subring.sum_mem _ fun i _ => ?_
  rw [coeff_map, Algebra.smul_def]
  exact mul_mem (algebraMap_mem_of_restrict_eq hw _) (pow_mem hxmem i)

private theorem root_mem_of_restrict_eq {w : Place K F'} {v : Place K F} (hw : w.restrict F = v)
    {Q : Polynomial v.toValuationSubring} (hQ : Q.Monic) {x : F'}
    (hx : aeval x (Q.map (algebraMap v.toValuationSubring F)) = 0) : x ∈ w.toValuationSubring := by
  have hmonic : ((Q.map (algebraMap v.toValuationSubring F)).map (algebraMap F F')).Monic := (hQ.map _).map _
  refine w.mem_of_eval_monic_eq_zero hmonic ?_ (x := x) ?_
  · intro i
    rw [coeff_map, coeff_map]
    exact algebraMap_mem_of_restrict_eq hw _
  · rwa [eval_map, ← aeval_def]

private theorem ord_sub_eq_ramificationIndex_mul (v : Place K F) (Q : Polynomial v.toValuationSubring)
    {x : F'} (hx : aeval x (Q.map (algebraMap v.toValuationSubring F)) = 0)
    (b : v.toValuationSubring) (hsimple : IsUnit (Q.derivative.eval b))
    {w : Place K F'} (hw : w.restrict F = v) (hxb : 0 < w.ord (x - algebraMap F F' (b : F))) :
    w.ord (x - algebraMap F F' (b : F))
      = Place.ramificationIndex (F := F) w * v.ord ((Q.eval b : v.toValuationSubring) : F) := by
  obtain ⟨S, hS, hSb⟩ := exists_taylor v Q b
  obtain ⟨T, hT, -⟩ := exists_taylor v S b
  set y := x - algebraMap F F' (b : F) with hy
  have hy0 : y ≠ 0 := by
    intro h; rw [h] at hxb; simp at hxb
  have hymem : y ∈ w.toValuationSubring := (w.mem_iff_ord_nonneg hy0).mpr hxb.le
  have hxmem : x ∈ w.toValuationSubring := by
    have : x = y + algebraMap F F' (b : F) := by rw [hy]; ring
    rw [this]; exact add_mem hymem (algebraMap_mem_of_restrict_eq hw b)

  obtain ⟨hu0, hu⟩ := ord_coe_eq_zero_of_isUnit v hsimple
  set u : F' := algebraMap F F' ((Q.derivative.eval b : v.toValuationSubring) : F) with hu_def
  have hu0' : u ≠ 0 := (map_ne_zero_iff _ (algebraMap F F').injective).mpr hu0
  have huord : w.ord u = 0 := by
    rw [hu_def, w.ord_restrict (F := F), hw, hu, mul_zero]
  have humem : u ∈ w.toValuationSubring := algebraMap_mem_of_restrict_eq hw _
  set t := aeval x (T.map (algebraMap v.toValuationSubring F)) with ht
  have htmem : t ∈ w.toValuationSubring := aeval_mem_of_restrict_eq hw T hxmem
  have hSx : aeval x (S.map (algebraMap v.toValuationSubring F)) = u + y * t := by
    have h := aeval_taylor v hT x
    rw [hSb] at h
    rw [← ht, ← hy] at h
    rw [← hu_def] at h
    linear_combination h
  have hyt : y * t = 0 ∨ 0 < w.ord (y * t) := by
    rcases eq_or_ne t 0 with ht0 | ht0
    · left; rw [ht0, mul_zero]
    · right
      rw [w.ord_mul hy0 ht0]
      have : 0 ≤ w.ord t := (w.mem_iff_ord_nonneg ht0).mp htmem
      omega
  obtain ⟨hs0, hsord⟩ := ord_add_eq_zero w hu0' huord humem (mul_mem hymem htmem) hyt

  have hmain : y * (u + y * t) = -algebraMap F F' ((Q.eval b : v.toValuationSubring) : F) := by
    have h := aeval_taylor v hS x
    rw [hx, hSx, ← hy] at h
    linear_combination -h
  have hQb0 : algebraMap F F' ((Q.eval b : v.toValuationSubring) : F) ≠ 0 := by
    intro h
    rw [h, neg_zero] at hmain
    exact (mul_ne_zero hy0 hs0) hmain
  have h1 : w.ord (y * (u + y * t)) = w.ord y := by rw [w.ord_mul hy0 hs0, hsord, add_zero]
  rw [hmain, Place.ord_neg, w.ord_restrict (F := F), hw] at h1
  exact h1.symm

variable [Module.Finite F F'] [HasPrincipalDivisors K F']

private theorem exists_place_of_simple_root (H : Divisor.PushforwardNormFormula K F F') (v : Place K F)
    {Q : Polynomial v.toValuationSubring} (hQ : Q.Monic) {x : F'}
    (hx : aeval x (Q.map (algebraMap v.toValuationSubring F)) = 0)
    (b : v.toValuationSubring) (hroot : 0 < v.ord ((Q.eval b : v.toValuationSubring) : F))
    (hsimple : IsUnit (Q.derivative.eval b))
    (hnorm : v.ord (Algebra.norm F (x - algebraMap F F' (b : F))) = v.ord ((Q.eval b : v.toValuationSubring) : F)) :
    ∃ w₀ : Place K F', w₀.restrict F = v ∧ 0 < w₀.ord (x - algebraMap F F' (b : F)) ∧
      Place.ramificationIndex (F := F) w₀ = 1 ∧ w₀.inertiaDeg F = 1 ∧
      ∀ w : Place K F', w.restrict F = v → 0 < w.ord (x - algebraMap F F' (b : F)) → w = w₀ := by
  classical
  have hQb0 : ((Q.eval b : v.toValuationSubring) : F) ≠ 0 := by
    intro h; rw [h, Place.ord_zero] at hroot; exact lt_irrefl _ hroot
  set y := x - algebraMap F F' (b : F) with hy
  have hy0 : y ≠ 0 := by
    intro h0
    obtain ⟨S, hS, -⟩ := exists_taylor v Q b
    have h := aeval_taylor v hS x
    rw [hx, ← hy, h0, zero_mul, zero_sub, neg_eq_zero] at h
    exact hQb0 ((map_eq_zero_iff _ (algebraMap F F').injective).mp h)
  obtain ⟨D, hD, -⟩ := HasPrincipalDivisors.exists_divisor (K := K) y hy0
  have hpush := H y hy0 D hD v
  rw [hnorm, Divisor.pushforward_apply, ← Finset.sum_filter] at hpush
  set T : Finset (Place K F') := D.support.filter (fun w => w.restrict F = v) with hT
  have hmemT : ∀ w, w ∈ T ↔ w.restrict F = v ∧ 0 < w.ord y := by
    intro w
    rw [hT, Finset.mem_filter, Finsupp.mem_support_iff, hD w]
    constructor
    · rintro ⟨hne, hw⟩
      have hymem : y ∈ w.toValuationSubring :=
        sub_mem (root_mem_of_restrict_eq hw hQ hx) (algebraMap_mem_of_restrict_eq hw b)
      exact ⟨hw, lt_of_le_of_ne ((w.mem_iff_ord_nonneg hy0).mp hymem) (Ne.symm hne)⟩
    · rintro ⟨hw, hpos⟩
      exact ⟨by omega, hw⟩

  have hterm : ∀ w ∈ T, D w * (w.inertiaDeg F : ℤ)
      = v.ord ((Q.eval b : v.toValuationSubring) : F) * ((Place.ramificationIndex (F := F) w * w.inertiaDeg F : ℕ) : ℤ) := by
    intro w hwT
    obtain ⟨hw, hpos⟩ := (hmemT w).mp hwT
    rw [hD w, ord_sub_eq_ramificationIndex_mul v Q hx b hsimple hw hpos]
    push_cast
    ring
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum] at hpush

  have hm0 : v.ord ((Q.eval b : v.toValuationSubring) : F) ≠ 0 := by omega
  have hsum1 : ∑ w ∈ T, (Place.ramificationIndex (F := F) w * w.inertiaDeg F) = 1 := by
    have h := hpush
    have h2 : v.ord ((Q.eval b : v.toValuationSubring) : F)
        * ((∑ w ∈ T, (Place.ramificationIndex (F := F) w * w.inertiaDeg F : ℕ) : ℤ) - 1) = 0 := by
      push_cast at h ⊢
      linear_combination h
    rcases mul_eq_zero.mp h2 with h3 | h3
    · exact absurd h3 hm0
    · exact_mod_cast sub_eq_zero.mp h3
  obtain ⟨w₀, hT0, hw₀⟩ := eq_singleton_of_sum_eq_one T _ (fun w _ =>
    Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (w.ramificationIndex_pos (F := F)).ne'
      (w.inertiaDeg_pos_of_finiteDimensional (F := F)).ne')) hsum1
  have hw₀T : w₀ ∈ T := by rw [hT0]; exact Finset.mem_singleton_self _
  obtain ⟨hres, hpos⟩ := (hmemT w₀).mp hw₀T
  refine ⟨w₀, hres, hpos, Nat.eq_one_of_mul_eq_one_right hw₀, Nat.eq_one_of_mul_eq_one_left hw₀, ?_⟩
  intro w hw hwpos
  have : w ∈ T := (hmemT w).mpr ⟨hw, hwpos⟩
  rw [hT0] at this
  exact Finset.mem_singleton.mp this

end Engine

section Along

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F'] [CharZero F]
  [HasPrincipalDivisors K F']

private theorem exists_place_of_simple_root_along (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (hfin : FiniteAlong K φ)
    (v : Place K F) {Q : Polynomial v.toValuationSubring} (hQ : Q.Monic) {x : F'}
    (hx : (Q.map (algebraMap v.toValuationSubring F)).eval₂ φ.toRingHom x = 0)
    (b : v.toValuationSubring) (hroot : 0 < v.ord ((Q.eval b : v.toValuationSubring) : F))
    (hsimple : IsUnit (Q.derivative.eval b))
    (hnorm : letI := algebraAlong φ; v.ord (Algebra.norm F (x - φ (b : F))) = v.ord ((Q.eval b : v.toValuationSubring) : F)) :
    ∃ w₀ : Place K F', w₀.restrictAlong φ hφ = v ∧ 0 < w₀.ord (x - φ (b : F)) ∧
      w₀.ramificationIndexAlong φ = 1 ∧ w₀.inertiaDegAlong φ hφ = 1 ∧
      ∀ w : Place K F', w.restrictAlong φ hφ = v → 0 < w.ord (x - φ (b : F)) → w = w₀ := by
  letI := algebraAlong φ
  haveI := isScalarTower_along φ
  haveI := isIntegral_along φ hφ
  haveI : Module.Finite F F' := hfin
  have H : Divisor.PushforwardNormFormula K F F' := normFormulaAlong φ hfin (separableAlong_of_charZero φ hφ)
  have hx' : aeval x (Q.map (algebraMap v.toValuationSubring F)) = 0 := by
    rw [aeval_def]; exact hx
  exact exists_place_of_simple_root H v hQ hx' b hroot hsimple hnorm

end Along

end SR

namespace NR

open IntermediateField

section Norm

variable {F F' : Type*} [Field F] [Field F'] [Algebra F F'] [Module.Finite F F']

private theorem norm_algebraMap_sub (x : F') (hdeg : (minpoly F x).natDegree = Module.finrank F F') (c : F) :
    Algebra.norm F (algebraMap F F' c - x) = (minpoly F x).eval c := by
  set y := x - algebraMap F F' c with hy
  have hyint : IsIntegral F y := Algebra.IsIntegral.isIntegral y
  have hminy : minpoly F y = (minpoly F x).comp (X + C c) := minpoly.sub_algebraMap x c
  have hdegy : (minpoly F y).natDegree = Module.finrank F F' := by
    rw [hminy, natDegree_comp, natDegree_X_add_C, mul_one, hdeg]

  have htower : Module.finrank F F' = Module.finrank F F⟮y⟯ * Module.finrank F⟮y⟯ F' :=
    (Module.finrank_mul_finrank F F⟮y⟯ F').symm
  rw [adjoin.finrank hyint, hdegy] at htower
  have hn : 0 < Module.finrank F F' := Module.finrank_pos
  have hm : Module.finrank F⟮y⟯ F' = 1 := by
    have h : Module.finrank F F' * Module.finrank F⟮y⟯ F' = Module.finrank F F' * 1 := by
      rw [mul_one]; exact htower.symm
    exact Nat.eq_of_mul_eq_mul_left hn h

  have hnormy : Algebra.norm F y = (-1) ^ Module.finrank F F' * (minpoly F x).eval c := by
    rw [Algebra.norm_eq_norm_adjoin, hm, pow_one, ← adjoin.powerBasis_gen hyint,
      Algebra.PowerBasis.norm_gen_eq_coeff_zero_minpoly, adjoin.powerBasis_gen, minpoly_gen, adjoin.powerBasis_dim,
      hdegy, hminy, coeff_zero_eq_eval_zero, eval_comp, eval_add, eval_X, eval_C, zero_add]
  have hneg : algebraMap F F' c - x = algebraMap F F' (-1) * y := by
    rw [map_neg, map_one, neg_one_mul, hy, neg_sub]
  rw [hneg, map_mul, Algebra.norm_algebraMap, hnormy, ← mul_assoc, ← mul_pow, neg_one_mul, neg_neg, one_pow,
    one_mul]

end Norm

section Ord

open AlgebraicCurve

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra F F'] [Module.Finite F F']

private theorem ord_norm_sub_eq (v : Place K F) (Q : Polynomial v.toValuationSubring) {x : F'}
    (hQ : Q.map (algebraMap v.toValuationSubring F) = minpoly F x)
    (hdeg : (minpoly F x).natDegree = Module.finrank F F') (b : v.toValuationSubring) :
    v.ord (Algebra.norm F (x - algebraMap F F' (b : F))) = v.ord ((Q.eval b : v.toValuationSubring) : F) := by
  have h1 : x - algebraMap F F' (b : F) = -(algebraMap F F' (b : F) - x) := (neg_sub _ _).symm
  have h2 : Algebra.norm F (-(algebraMap F F' (b : F) - x))
      = (-1) ^ Module.finrank F F' * Algebra.norm F (algebraMap F F' (b : F) - x) := by
    have hneg1 : (-1 : F') = algebraMap F F' (-1) := by simp
    rw [neg_eq_neg_one_mul, map_mul, hneg1, Algebra.norm_algebraMap]
  have h3 : ((Q.eval b : v.toValuationSubring) : F) = (minpoly F x).eval (b : F) := by
    rw [← hQ, eval_map]
    exact (eval₂_at_apply (algebraMap v.toValuationSubring F) b).symm
  rw [h1, h2, norm_algebraMap_sub x hdeg, h3]
  rcases neg_one_pow_eq_or F (Module.finrank F F') with h | h
  · rw [h, one_mul]
  · rw [h, neg_one_mul, Place.ord_neg]

end Ord

end NR

local notation "Qbar" => AlgebraicClosure ℚ
local notation "Lq" => LaurentSeries (AlgebraicClosure ℚ)

private theorem intPolyHom_ext {T : Type*} [CommRing T] {f g : Polynomial ℤ →+* T}
    (hX : f Polynomial.X = g Polynomial.X) : f = g :=
  Polynomial.ringHom_ext' (Subsingleton.elim _ _) hX

section RatSide

private def P₁ (j₁ : Qbar) : HeightOneSpectrum (Polynomial Qbar) where
  asIdeal := Ideal.span {Polynomial.X - Polynomial.C j₁}
  isPrime := (PrincipalIdealRing.isMaximal_of_irreducible
    (Polynomial.irreducible_X_sub_C j₁)).isPrime
  ne_bot := by
    simpa [Ideal.span_singleton_eq_bot] using Polynomial.X_sub_C_ne_zero j₁

private abbrev vP (j₁ : Qbar) : Place Qbar (RatFunc Qbar) :=
  Place.ofHeightOneSpectrum (P₁ j₁)

private theorem algebraMap_poly_mem (j₁ : Qbar) (q : Polynomial Qbar) :
    algebraMap (Polynomial Qbar) (RatFunc Qbar) q ∈ (vP j₁).toValuationSubring := by
  show _ ∈ ((P₁ j₁).valuation (RatFunc Qbar)).valuationSubring
  rw [Valuation.mem_valuationSubring_iff]
  exact (P₁ j₁).valuation_le_one q

private def xV (j₁ : Qbar) : (vP j₁).toValuationSubring :=
  ⟨algebraMap (Polynomial Qbar) (RatFunc Qbar) Polynomial.X,
    algebraMap_poly_mem j₁ Polynomial.X⟩

private def cf (j₁ : Qbar) : Polynomial ℤ →+* (vP j₁).toValuationSubring :=
  (Polynomial.aeval (xV j₁)).toRingHom

private theorem cf_X (j₁ : Qbar) :
    algebraMap (vP j₁).toValuationSubring (RatFunc Qbar) ((cf j₁) Polynomial.X)
      = RatFunc.X := by
  have h1 : (cf j₁) Polynomial.X = xV j₁ := by
    show (Polynomial.aeval (xV j₁)) Polynomial.X = xV j₁
    exact Polynomial.aeval_X _
  rw [h1]
  exact RatFunc.algebraMap_X

private def QΦ {p : ℕ} [NeZero p] (data : ModularPolynomialData p) (j₁ : Qbar) :
    Polynomial ((vP j₁).toValuationSubring) :=
  data.Φ.map (cf j₁)

private theorem QΦ_monic {p : ℕ} [NeZero p] (data : ModularPolynomialData p) (j₁ : Qbar) :
    (QΦ data j₁).Monic :=
  data.monic.map _

private def bC (j₁ j₂ : Qbar) : (vP j₁).toValuationSubring :=
  ⟨algebraMap Qbar (RatFunc Qbar) j₂, (vP j₁).algebraMap_mem' j₂⟩

private def pswap (G : Polynomial (Polynomial ℤ)) (j₂ : Qbar) : Polynomial Qbar :=
  (G.map (Polynomial.mapRingHom (Int.castRingHom Qbar))).eval (Polynomial.C j₂)

private theorem coe_bC (j₁ j₂ : Qbar) :
    ((bC j₁ j₂ : (vP j₁).toValuationSubring) : RatFunc Qbar)
      = algebraMap Qbar (RatFunc Qbar) j₂ := rfl

private theorem coe_eval_eq (j₁ j₂ : Qbar) (G : Polynomial (Polynomial ℤ)) :
    (((G.map (cf j₁)).eval (bC j₁ j₂) : (vP j₁).toValuationSubring) : RatFunc Qbar)
      = algebraMap (Polynomial Qbar) (RatFunc Qbar) (pswap G j₂) := by
  have hL : (((G.map (cf j₁)).eval (bC j₁ j₂) : (vP j₁).toValuationSubring) : RatFunc Qbar)
      = G.eval₂ ((algebraMap (vP j₁).toValuationSubring (RatFunc Qbar)).comp (cf j₁))
          (algebraMap (vP j₁).toValuationSubring (RatFunc Qbar) (bC j₁ j₂)) :=
    calc (((G.map (cf j₁)).eval (bC j₁ j₂) : (vP j₁).toValuationSubring) : RatFunc Qbar)
        = algebraMap (vP j₁).toValuationSubring (RatFunc Qbar)
            ((G.map (cf j₁)).eval (bC j₁ j₂)) := rfl
      _ = (G.map (cf j₁)).eval₂ (algebraMap (vP j₁).toValuationSubring (RatFunc Qbar))
            (algebraMap (vP j₁).toValuationSubring (RatFunc Qbar) (bC j₁ j₂)) :=
          (Polynomial.eval₂_at_apply _ _).symm
      _ = G.eval₂ ((algebraMap (vP j₁).toValuationSubring (RatFunc Qbar)).comp (cf j₁))
            (algebraMap (vP j₁).toValuationSubring (RatFunc Qbar) (bC j₁ j₂)) :=
          Polynomial.eval₂_map _ _ _
  have hR : algebraMap (Polynomial Qbar) (RatFunc Qbar) (pswap G j₂)
      = G.eval₂ ((algebraMap (Polynomial Qbar) (RatFunc Qbar)).comp
          (Polynomial.mapRingHom (Int.castRingHom Qbar)))
          (algebraMap (Polynomial Qbar) (RatFunc Qbar) (Polynomial.C j₂)) :=
    calc algebraMap (Polynomial Qbar) (RatFunc Qbar) (pswap G j₂)
        = algebraMap (Polynomial Qbar) (RatFunc Qbar)
            ((G.map (Polynomial.mapRingHom (Int.castRingHom Qbar))).eval (Polynomial.C j₂)) :=
          rfl
      _ = (G.map (Polynomial.mapRingHom (Int.castRingHom Qbar))).eval₂
            (algebraMap (Polynomial Qbar) (RatFunc Qbar))
            (algebraMap (Polynomial Qbar) (RatFunc Qbar) (Polynomial.C j₂)) :=
          (Polynomial.eval₂_at_apply _ _).symm
      _ = G.eval₂ ((algebraMap (Polynomial Qbar) (RatFunc Qbar)).comp
            (Polynomial.mapRingHom (Int.castRingHom Qbar)))
            (algebraMap (Polynomial Qbar) (RatFunc Qbar) (Polynomial.C j₂)) :=
          Polynomial.eval₂_map _ _ _
  rw [hL, hR]
  have harg : algebraMap (vP j₁).toValuationSubring (RatFunc Qbar) (bC j₁ j₂)
      = algebraMap (Polynomial Qbar) (RatFunc Qbar) (Polynomial.C j₂) := by
    rw [← Polynomial.algebraMap_eq, ← IsScalarTower.algebraMap_apply]
    rfl
  rw [harg]
  congr 1
  refine intPolyHom_ext ?_
  simp only [RingHom.coe_comp, Function.comp_apply, Polynomial.coe_mapRingHom,
    Polynomial.map_X, RatFunc.algebraMap_X]
  exact cf_X j₁

private theorem pswap_eval (G : Polynomial (Polynomial ℤ)) (j₁ j₂ : Qbar) :
    (pswap G j₂).eval j₁ = G.eval₂ (Polynomial.aeval (R := ℤ) j₁).toRingHom j₂ := by
  have h1 : (pswap G j₂).eval j₁
      = (Polynomial.evalRingHom j₁)
          ((G.map (Polynomial.mapRingHom (Int.castRingHom Qbar))).eval (Polynomial.C j₂)) :=
    rfl
  have h2 := Polynomial.eval₂_at_apply
    (p := G.map (Polynomial.mapRingHom (Int.castRingHom Qbar)))
    (Polynomial.evalRingHom j₁) (Polynomial.C j₂)
  rw [h1, ← h2, Polynomial.eval₂_map,
    show (Polynomial.evalRingHom j₁) (Polynomial.C j₂) = j₂ by simp]
  congr 1
  refine intPolyHom_ext ?_
  simp

private theorem ord_nonneg_of_mem {K F : Type*} [Field K] [Field F] [Algebra K F]
    (v : Place K F) {f : F} (hf : f ∈ v.toValuationSubring) : 0 ≤ v.ord f := by
  rcases eq_or_ne f 0 with rfl | hf0
  · simp
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  obtain ⟨n, u, hu⟩ :=
    IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
      (x := (⟨f, hf⟩ : v.toValuationSubring)) (by simpa [Subtype.ext_iff] using hf0) hπ
  have hcoe : f = ((u : v.toValuationSubring) : F) * ((π : F) ^ (n : ℤ)) := by
    have h := congrArg (Subtype.val) hu
    push_cast at h
    rw [zpow_natCast]
    exact h
  rw [hcoe, v.ord_unit_smul_zpow u hπ (n : ℤ)]
  exact Int.natCast_nonneg n

private theorem mem_of_ord_pos {K F : Type*} [Field K] [Field F] [Algebra K F]
    (w : Place K F) {f : F} (h : 0 < w.ord f) : f ∈ w.toValuationSubring := by
  rcases eq_or_ne f 0 with rfl | _
  · exact zero_mem _
  by_contra hnot
  have hinv : f⁻¹ ∈ w.toValuationSubring :=
    (w.toValuationSubring.mem_or_inv_mem f).resolve_left hnot
  have h1 : w.ord f⁻¹ = - w.ord f := w.ord_inv f
  have h2 : 0 ≤ w.ord f⁻¹ := ord_nonneg_of_mem w hinv
  omega

private theorem ord_pos_iff_isRoot (j₁ : Qbar) {q : Polynomial Qbar} (hq : q ≠ 0) :
    0 < (vP j₁).ord (algebraMap (Polynomial Qbar) (RatFunc Qbar) q) ↔ q.IsRoot j₁ := by
  have hne : algebraMap (Polynomial Qbar) (RatFunc Qbar) q ≠ 0 := by
    intro h0
    exact hq ((map_eq_zero_iff _
      (IsFractionRing.injective (Polynomial Qbar) (RatFunc Qbar))).mp h0)
  have hmem := algebraMap_poly_mem j₁ q
  rw [← (vP j₁).mem_maximalIdeal_iff_ord_pos hne hmem]
  constructor
  · intro hmx
    have hlt' := (ValuationSubring.valuation_lt_one_iff _ _).mp hmx
    have hlt := ((P₁ j₁).valuation
      (RatFunc Qbar)).isEquiv_valuation_valuationSubring.lt_one_iff_lt_one.mpr hlt'
    have hmemI : q ∈ (P₁ j₁).asIdeal := ((P₁ j₁).valuation_lt_one_iff_mem q).mp hlt
    have hdvd : (Polynomial.X - Polynomial.C j₁) ∣ q := by
      rwa [show (P₁ j₁).asIdeal = Ideal.span {Polynomial.X - Polynomial.C j₁} from rfl,
        Ideal.mem_span_singleton] at hmemI
    exact Polynomial.dvd_iff_isRoot.mp hdvd
  · intro hroot
    have hdvd : (Polynomial.X - Polynomial.C j₁) ∣ q := Polynomial.dvd_iff_isRoot.mpr hroot
    have hmemI : q ∈ (P₁ j₁).asIdeal := by
      rw [show (P₁ j₁).asIdeal = Ideal.span {Polynomial.X - Polynomial.C j₁} from rfl,
        Ideal.mem_span_singleton]
      exact hdvd
    have hlt : (P₁ j₁).valuation (RatFunc Qbar)
        (algebraMap (Polynomial Qbar) (RatFunc Qbar) q) < 1 :=
      ((P₁ j₁).valuation_lt_one_iff_mem q).mpr hmemI
    have hlt' := ((P₁ j₁).valuation
      (RatFunc Qbar)).isEquiv_valuation_valuationSubring.lt_one_iff_lt_one.mp hlt
    exact (ValuationSubring.valuation_lt_one_iff _ _).mpr hlt'

private theorem ord_eq_zero_of_not_isRoot (j₁ : Qbar) {q : Polynomial Qbar} (hq : q ≠ 0)
    (h : ¬ q.IsRoot j₁) :
    (vP j₁).ord (algebraMap (Polynomial Qbar) (RatFunc Qbar) q) = 0 := by
  have hnn := ord_nonneg_of_mem (vP j₁) (algebraMap_poly_mem j₁ q)
  have hnp : ¬ 0 < (vP j₁).ord (algebraMap (Polynomial Qbar) (RatFunc Qbar) q) :=
    fun hp => h ((ord_pos_iff_isRoot j₁ hq).mp hp)
  omega

end RatSide

section Modular

variable (p : ℕ) [NeZero p]

private theorem jqNModC_one_mul : jqNModC Qbar (1 * p) = jqNModC Qbar p := by
  have : NeZero (1 * p) := by rwa [one_mul]
  show qExpand Qbar (1 * p) (jqModC Qbar) = qExpand Qbar p (jqModC Qbar)
  exact qExpand_congr (one_mul p) _

private theorem core_identity (data : ModularPolynomialData p) :
    data.Φ.eval₂ (Polynomial.aeval (R := ℤ) (jqModC Qbar)).toRingHom (jqNModC Qbar p) = 0 := by
  have h := ModularPolynomialData.eval_jqNModC_mul_eq_zero data Qbar 1
  rwa [jqNModC_one, jqNModC_one_mul] at h

private theorem eval₂_Φ_bar (data : ModularPolynomialData p) :
    data.Φ.eval₂ (Polynomial.aeval (R := ℤ)
      (jBar p : modularFunctionFieldBar p)).toRingHom (jpBar p) = 0 := by
  apply (algebraMap (modularFunctionFieldBar p) Lq).injective
  rw [map_zero, Polynomial.hom_eval₂]
  have hhom : (algebraMap (modularFunctionFieldBar p) Lq).comp
        (Polynomial.aeval (R := ℤ) (jBar p : modularFunctionFieldBar p)).toRingHom =
      (Polynomial.aeval (R := ℤ) (coeffEmb Qbar jq)).toRingHom := by
    refine intPolyHom_ext ?_
    simp
  rw [hhom]
  have h := congrArg (coeffEmb Qbar) data.eval_eq_zero
  rw [map_zero, Polynomial.hom_eval₂] at h
  have hhom2 : (coeffEmb Qbar).comp evalAtJ =
      (Polynomial.aeval (R := ℤ) (coeffEmb Qbar jq)).toRingHom := by
    refine intPolyHom_ext ?_
    simp [evalAtJ]
  rw [hhom2] at h
  have hjp : (algebraMap (modularFunctionFieldBar p) Lq) (jpBar p)
      = coeffEmb Qbar (qExpand ℚ p jq) := rfl
  rw [hjp]
  exact h

private theorem hx_engine (data : ModularPolynomialData p) (j₁ : Qbar)
    (φ : RatFunc Qbar →ₐ[Qbar] modularFunctionFieldBar p)
    (hφX : φ (algebraMap (Polynomial Qbar) (RatFunc Qbar) Polynomial.X) = jBar p) :
    ((QΦ data j₁).map (algebraMap (vP j₁).toValuationSubring (RatFunc Qbar))).eval₂
      φ.toRingHom (jpBar p) = 0 := by
  have hφX' : φ RatFunc.X = jBar p := by
    rw [← RatFunc.algebraMap_X]
    exact hφX
  rw [QΦ, Polynomial.map_map, Polynomial.eval₂_map,
    show φ.toRingHom.comp ((algebraMap (vP j₁).toValuationSubring (RatFunc Qbar)).comp (cf j₁))
        = (Polynomial.aeval (R := ℤ) (jBar p : modularFunctionFieldBar p)).toRingHom from
      intPolyHom_ext (by
        show φ (algebraMap (vP j₁).toValuationSubring (RatFunc Qbar) ((cf j₁) Polynomial.X))
            = (Polynomial.aeval (R := ℤ) (jBar p : modularFunctionFieldBar p)) Polynomial.X
        rw [cf_X, hφX', Polynomial.aeval_X])]
  exact eval₂_Φ_bar p data

end Modular

section RootSimple

variable {p : ℕ} [NeZero p]

private theorem hroot_engine (data : ModularPolynomialData p) (j₁ j₂ : Qbar)
    (hroot : data.Φ.eval₂ (Polynomial.aeval (R := ℤ) j₁).toRingHom j₂ = 0)
    (hPne : pswap data.Φ j₂ ≠ 0) :
    0 < (vP j₁).ord
      (((QΦ data j₁).eval (bC j₁ j₂) : (vP j₁).toValuationSubring) : RatFunc Qbar) := by
  rw [QΦ, coe_eval_eq j₁ j₂ data.Φ]
  refine (ord_pos_iff_isRoot j₁ hPne).mpr ?_
  show (pswap data.Φ j₂).eval j₁ = 0
  rw [pswap_eval]
  exact hroot

private theorem hsimple_engine (data : ModularPolynomialData p) (j₁ j₂ : Qbar)
    (hmult : (data.Φ.map
      (Polynomial.aeval (R := ℤ) j₁).toRingHom).rootMultiplicity j₂ = 1) :
    IsUnit ((Polynomial.derivative (QΦ data j₁)).eval (bC j₁ j₂)) := by

  set W : Polynomial Qbar := data.Φ.map (Polynomial.aeval (R := ℤ) j₁).toRingHom with hW
  have hW0 : W ≠ 0 := by
    intro h0
    rw [h0] at hmult
    simp at hmult
  have hWroot : W.IsRoot j₂ :=
    (Polynomial.rootMultiplicity_pos hW0).mp (by omega)
  have hnd : ¬ (Polynomial.derivative W).IsRoot j₂ := by
    intro hd
    have h1 := (Polynomial.one_lt_rootMultiplicity_iff_isRoot hW0).mpr ⟨hWroot, hd⟩
    omega

  have hder : Polynomial.derivative (QΦ data j₁)
      = (Polynomial.derivative data.Φ).map (cf j₁) := by
    rw [QΦ, Polynomial.derivative_map]
  have hkey : (pswap (Polynomial.derivative data.Φ) j₂).eval j₁
      = (Polynomial.derivative W).eval j₂ := by
    rw [pswap_eval, hW, Polynomial.derivative_map, Polynomial.eval_map]
  have hvalne : (pswap (Polynomial.derivative data.Φ) j₂).eval j₁ ≠ 0 := by
    rw [hkey]
    exact hnd
  have hPne' : pswap (Polynomial.derivative data.Φ) j₂ ≠ 0 := by
    intro h0
    exact hvalne (by rw [h0, Polynomial.eval_zero])

  have hco : (((Polynomial.derivative (QΦ data j₁)).eval (bC j₁ j₂) :
        (vP j₁).toValuationSubring) : RatFunc Qbar)
      = algebraMap (Polynomial Qbar) (RatFunc Qbar)
          (pswap (Polynomial.derivative data.Φ) j₂) := by
    rw [hder, coe_eval_eq]
  have hne : (((Polynomial.derivative (QΦ data j₁)).eval (bC j₁ j₂) :
        (vP j₁).toValuationSubring) : RatFunc Qbar) ≠ 0 := by
    rw [hco]
    intro h0
    exact hPne' ((map_eq_zero_iff _
      (IsFractionRing.injective (Polynomial Qbar) (RatFunc Qbar))).mp h0)
  have hord0 : (vP j₁).ord (((Polynomial.derivative (QΦ data j₁)).eval (bC j₁ j₂) :
        (vP j₁).toValuationSubring) : RatFunc Qbar) = 0 := by
    rw [hco]
    exact ord_eq_zero_of_not_isRoot j₁ hPne' (fun hroot' => hvalne hroot')

  have hmem : (((Polynomial.derivative (QΦ data j₁)).eval (bC j₁ j₂) :
        (vP j₁).toValuationSubring) : RatFunc Qbar) ∈ (vP j₁).toValuationSubring := by
    rw [hco]
    exact algebraMap_poly_mem j₁ _
  have hiff := (vP j₁).mem_maximalIdeal_iff_ord_pos hne hmem
  have heta : (⟨(((Polynomial.derivative (QΦ data j₁)).eval (bC j₁ j₂) :
        (vP j₁).toValuationSubring) : RatFunc Qbar), hmem⟩ : (vP j₁).toValuationSubring)
      = (Polynomial.derivative (QΦ data j₁)).eval (bC j₁ j₂) :=
    Subtype.ext rfl
  rw [heta] at hiff
  have hnotmax : (Polynomial.derivative (QΦ data j₁)).eval (bC j₁ j₂)
      ∉ IsLocalRing.maximalIdeal (vP j₁).toValuationSubring := by
    rw [hiff, hord0]
    omega
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not] at hnotmax
  exact hnotmax

end RootSimple

section Restrict

private theorem hos_ext {R : Type*} [CommRing R] [IsDedekindDomain R]
    {w w' : HeightOneSpectrum R} (h : w.asIdeal = w'.asIdeal) : w = w' := by
  cases w
  cases w'
  cases h
  rfl

private theorem restrictAlong_eq_vP {p : ℕ} [NeZero p] (j₁ : Qbar)
    (φ : RatFunc Qbar →ₐ[Qbar] modularFunctionFieldBar p) (hφ : φ.toRingHom.IsIntegral)
    (hφX : φ (algebraMap (Polynomial Qbar) (RatFunc Qbar) Polynomial.X) = jBar p)
    (x : Place Qbar (modularFunctionFieldBar p))
    (hx₁ : 0 < x.ord (jBar p - algebraMap Qbar (modularFunctionFieldBar p) j₁)) :
    x.restrictAlong φ hφ = vP j₁ := by
  set u := x.restrictAlong φ hφ with hu

  have hφval : φ (algebraMap (Polynomial Qbar) (RatFunc Qbar)
        (Polynomial.X - Polynomial.C j₁))
      = jBar p - algebraMap Qbar (modularFunctionFieldBar p) j₁ := by
    rw [map_sub, map_sub, hφX]
    congr 1
    rw [← Polynomial.algebraMap_eq, ← IsScalarTower.algebraMap_apply]
    exact φ.commutes j₁

  have hordpos : 0 < u.ord
      (algebraMap (Polynomial Qbar) (RatFunc Qbar) (Polynomial.X - Polynomial.C j₁)) := by
    have h := Place.ord_restrictAlong φ hφ x
      (algebraMap (Polynomial Qbar) (RatFunc Qbar) (Polynomial.X - Polynomial.C j₁))
    rw [hφval] at h
    rcases lt_or_ge 0 (u.ord
      (algebraMap (Polynomial Qbar) (RatFunc Qbar) (Polynomial.X - Polynomial.C j₁))) with
      hpos | hge
    · exact hpos
    · exfalso
      have hle : u.ord
          (algebraMap (Polynomial Qbar) (RatFunc Qbar) (Polynomial.X - Polynomial.C j₁))
          ≤ 0 := hge
      have hnn : (0 : ℤ) ≤ (Place.ramificationIndexAlong φ x : ℤ) := Int.natCast_nonneg _
      have hmul : (Place.ramificationIndexAlong φ x : ℤ) * u.ord
          (algebraMap (Polynomial Qbar) (RatFunc Qbar) (Polynomial.X - Polynomial.C j₁))
          ≤ (Place.ramificationIndexAlong φ x : ℤ) * 0 :=
        mul_le_mul_of_nonneg_left hle hnn
      rw [mul_zero] at hmul
      have hcontra : x.ord (jBar p - algebraMap Qbar (modularFunctionFieldBar p) j₁) ≤ 0 := by
        rw [h]
        exact hmul
      omega

  have hXmem : algebraMap (Polynomial Qbar) (RatFunc Qbar) Polynomial.X
      ∈ u.toValuationSubring := by
    have h1 : algebraMap (Polynomial Qbar) (RatFunc Qbar)
        (Polynomial.X - Polynomial.C j₁) ∈ u.toValuationSubring :=
      mem_of_ord_pos u hordpos
    have h2 : algebraMap Qbar (RatFunc Qbar) j₁ ∈ u.toValuationSubring :=
      u.algebraMap_mem' j₁
    have h3 := add_mem h1 h2
    have h4 : algebraMap (Polynomial Qbar) (RatFunc Qbar) (Polynomial.X - Polynomial.C j₁)
        + algebraMap Qbar (RatFunc Qbar) j₁
        = algebraMap (Polynomial Qbar) (RatFunc Qbar) Polynomial.X := by
      rw [map_sub, ← Polynomial.algebraMap_eq, ← IsScalarTower.algebraMap_apply,
        sub_add_cancel]
    rwa [h4] at h3
  have hw : ∀ q : Polynomial Qbar,
      algebraMap (Polynomial Qbar) (RatFunc Qbar) q ∈ u.toValuationSubring := by
    intro q
    induction q using Polynomial.induction_on' with
    | add f g hf hg =>
        rw [map_add]
        exact add_mem hf hg
    | monomial n a =>
        rw [← Polynomial.C_mul_X_pow_eq_monomial, map_mul, map_pow]
        refine mul_mem ?_ (pow_mem hXmem n)
        rw [← Polynomial.algebraMap_eq, ← IsScalarTower.algebraMap_apply]
        exact u.algebraMap_mem' a

  have hmemc : (Polynomial.X - Polynomial.C j₁) ∈ Place.center (Polynomial Qbar) u hw :=
    (Place.mem_center_iff_ord_pos u hw (Polynomial.X_sub_C_ne_zero j₁)).mpr hordpos
  have hle : Ideal.span {Polynomial.X - Polynomial.C j₁}
      ≤ Place.center (Polynomial Qbar) u hw :=
    (Ideal.span_singleton_le_iff_mem _).mpr hmemc
  have hmax : (Ideal.span ({Polynomial.X - Polynomial.C j₁} :
      Set (Polynomial Qbar))).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible (Polynomial.irreducible_X_sub_C j₁)
  have hcne : Place.center (Polynomial Qbar) u hw ≠ ⊤ :=
    (inferInstance : (Place.center (Polynomial Qbar) u hw).IsPrime).ne_top
  have hceq : Place.center (Polynomial Qbar) u hw
      = Ideal.span {Polynomial.X - Polynomial.C j₁} :=
    (hmax.eq_of_le hcne hle).symm

  have hspec : Place.centerHeightOneSpectrum (Polynomial Qbar) u hw = P₁ j₁ :=
    hos_ext (by rw [Place.centerHeightOneSpectrum_asIdeal, hceq]; rfl)
  refine Place.ext ?_
  rw [Place.toValuationSubring_eq_of_forall_mem u hw, hspec,
    show (vP j₁).toValuationSubring
      = ((P₁ j₁).valuation (RatFunc Qbar)).valuationSubring from rfl]
  exact HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring (K := RatFunc Qbar)
    (P₁ j₁)

end Restrict

section Phi

variable (p : ℕ) [NeZero p]

private abbrev E : IntermediateField Qbar (modularFunctionFieldBar p) :=
  IntermediateField.adjoin Qbar ({(jBar p : modularFunctionFieldBar p)} :
    Set (modularFunctionFieldBar p))

private theorem transcendental_jBar :
    Transcendental Qbar (jBar p : modularFunctionFieldBar p) :=
  ModularCurve.transcendental_coeffEmb_jq (AlgebraicClosure ℚ) p

private def eRE : RatFunc Qbar ≃ₐ[Qbar] E p :=
  RatFunc.algEquivOfTranscendental (jBar p : modularFunctionFieldBar p) (transcendental_jBar p)

private def phi : RatFunc Qbar →ₐ[Qbar] modularFunctionFieldBar p :=
  (E p).val.comp (eRE p).toAlgHom

private theorem phi_apply (r : RatFunc Qbar) : phi p r = ((eRE p r : E p) : modularFunctionFieldBar p) :=
  rfl

private theorem phi_X :
    phi p (algebraMap (Polynomial Qbar) (RatFunc Qbar) Polynomial.X) = jBar p := by
  rw [RatFunc.algebraMap_X, phi_apply]
  exact RatFunc.algEquivOfTranscendental_X _ _

private theorem phi_isIntegral [Fact p.Prime] : (phi p).toRingHom.IsIntegral := by
  haveI : FiniteDimensional (E p) (modularFunctionFieldBar p) :=
    ModularCurve.finiteDimensional_adjoin_coeffEmb_jq p
  have h1 : (eRE p).toAlgHom.toRingHom.IsIntegral :=
    RingHom.isIntegral_of_surjective _ (eRE p).surjective
  have h2 : (E p).val.toRingHom.IsIntegral := by
    have : (algebraMap (E p) (modularFunctionFieldBar p)).IsIntegral :=
      algebraMap_isIntegral_iff.mpr inferInstance
    exact this
  exact RingHom.IsIntegral.trans _ _ h1 h2

private theorem phi_finiteAlong [Fact p.Prime] : FiniteAlong Qbar (phi p) := by
  haveI hfd : FiniteDimensional (E p) (modularFunctionFieldBar p) :=
    ModularCurve.finiteDimensional_adjoin_coeffEmb_jq p
  letI : Algebra (RatFunc Qbar) (modularFunctionFieldBar p) := algebraAlong (phi p)
  show Module.Finite (RatFunc Qbar) (modularFunctionFieldBar p)
  obtain ⟨S, hS⟩ := Module.finite_def.mp hfd
  refine Module.finite_def.mpr ⟨S, ?_⟩
  rw [eq_top_iff]
  intro z _
  have hz : z ∈ Submodule.span (E p) (S : Set (modularFunctionFieldBar p)) := by
    rw [hS]; exact Submodule.mem_top
  refine Submodule.span_induction (p := fun y _ => y ∈ Submodule.span (RatFunc Qbar)
      (S : Set (modularFunctionFieldBar p))) ?_ ?_ ?_ ?_ hz
  · intro y hy
    exact Submodule.subset_span hy
  · exact Submodule.zero_mem _
  · intro y y' _ _ hy hy'
    exact Submodule.add_mem _ hy hy'
  · intro e y _ hy
    have he : e • y = ((eRE p).symm e) • y := by
      show (e : modularFunctionFieldBar p) * y = phi p ((eRE p).symm e) * y
      rw [phi_apply, AlgEquiv.apply_symm_apply]
    rw [he]
    exact Submodule.smul_mem _ _ hy

private theorem adjoin_jpBar_eq_top [Fact p.Prime] :
    letI := algebraAlong (phi p)
    IntermediateField.adjoin (RatFunc Qbar)
      ({(jpBar p : modularFunctionFieldBar p)} : Set (modularFunctionFieldBar p)) = ⊤ := by
  letI : Algebra (RatFunc Qbar) (modularFunctionFieldBar p) := algebraAlong (phi p)
  haveI : IsScalarTower Qbar (RatFunc Qbar) (modularFunctionFieldBar p) := isScalarTower_along (phi p)
  set S : IntermediateField (RatFunc Qbar) (modularFunctionFieldBar p) :=
    IntermediateField.adjoin (RatFunc Qbar)
      ({(jpBar p : modularFunctionFieldBar p)} : Set (modularFunctionFieldBar p)) with hS
  rw [eq_top_iff]
  intro z _

  let T : IntermediateField Qbar Lq := (S.restrictScalars Qbar).map (modularFunctionFieldBar p).val
  have hjS : (jBar p : modularFunctionFieldBar p) ∈ S := by
    rw [← phi_X p]
    exact S.algebraMap_mem _
  have hjpS : (jpBar p : modularFunctionFieldBar p) ∈ S :=
    IntermediateField.subset_adjoin _ _ (Set.mem_singleton _)
  have hT : IntermediateField.adjoin Qbar ({jqModC Qbar, jqNModC Qbar p} : Set Lq) ≤ T := by
    rw [IntermediateField.adjoin_le_iff]
    intro y hy
    rcases hy with rfl | rfl
    · refine (IntermediateField.mem_map _).mpr ⟨jBar p, ?_, ?_⟩
      · exact (IntermediateField.mem_restrictScalars Qbar).mpr hjS
      · show ((jBar p : modularFunctionFieldBar p) : Lq) = jqModC Qbar
        exact ModularCurve.coeffEmb_jq Qbar
    · refine (IntermediateField.mem_map _).mpr ⟨jpBar p, ?_, ?_⟩
      · exact (IntermediateField.mem_restrictScalars Qbar).mpr hjpS
      · show ((jpBar p : modularFunctionFieldBar p) : Lq) = jqNModC Qbar p
        exact ModularCurve.coeffEmb_jqN Qbar p
  have hbar : modularFunctionFieldBar p
      = IntermediateField.adjoin Qbar ({jqModC Qbar, jqNModC Qbar p} : Set Lq) :=
    (ModularCurve.modularFunctionFieldBar_eq_restrictScalars p).trans
      (IntermediateField.adjoin_simple_adjoin_simple
        (F := Qbar) (E := Lq) (α := jqModC Qbar) (jqNModC Qbar p))
  have hz : (z : Lq) ∈ IntermediateField.adjoin Qbar ({jqModC Qbar, jqNModC Qbar p} : Set Lq) := by
    rw [← hbar]
    exact z.2
  obtain ⟨s, hs, hsz⟩ := (IntermediateField.mem_map _).mp (hT hz)
  have hsz' : s = z := Subtype.ext hsz
  rw [← hsz']
  exact (IntermediateField.mem_restrictScalars Qbar).mp hs

private theorem hdeg_engine [Fact p.Prime] :
    letI := algebraAlong (phi p)
    (minpoly (RatFunc Qbar) (jpBar p : modularFunctionFieldBar p)).natDegree
      = Module.finrank (RatFunc Qbar) (modularFunctionFieldBar p) := by
  letI : Algebra (RatFunc Qbar) (modularFunctionFieldBar p) := algebraAlong (phi p)
  haveI : IsScalarTower Qbar (RatFunc Qbar) (modularFunctionFieldBar p) := isScalarTower_along (phi p)
  haveI : Module.Finite (RatFunc Qbar) (modularFunctionFieldBar p) := phi_finiteAlong p
  have hint : IsIntegral (RatFunc Qbar) (jpBar p : modularFunctionFieldBar p) :=
    Algebra.IsIntegral.isIntegral _
  rw [← IntermediateField.adjoin.finrank hint, adjoin_jpBar_eq_top p,
    IntermediateField.finrank_top']

end Phi

namespace Cap

local notation "F'" => modularFunctionFieldBar

section Crux
open Polynomial

private abbrev E1 : IntermediateField Qbar Lq := IntermediateField.adjoin Qbar {jqModC Qbar}

private def jgen : E1 := ⟨jqModC Qbar, IntermediateField.subset_adjoin _ _ rfl⟩

@[scoped simp] private theorem coe_jgen : (jgen : Lq) = jqModC Qbar := rfl

private theorem intPolyHom_ext {T : Type*} [CommRing T] {f g : Polynomial ℤ →+* T}
    (hX : f Polynomial.X = g Polynomial.X) : f = g :=
  Polynomial.ringHom_ext' (Subsingleton.elim _ _) hX

private theorem dedekindPsi_prime {p : ℕ} (hp : p.Prime) : dedekindPsi p = p + 1 := by
  have h1p : (1 : ℕ) ≠ p := hp.one_lt.ne
  rw [dedekindPsi, Nat.Prime.divisors hp]
  rw [show ({1, p} : Finset ℕ) = insert 1 {p} from rfl]
  rw [Finset.filter_insert, if_pos squarefree_one, Finset.filter_singleton,
    if_pos hp.squarefree, Finset.sum_insert (by simp [h1p]), Finset.sum_singleton,
    Nat.div_one, Nat.div_self hp.pos]

private theorem jqNModC_one_mul (p : ℕ) [NeZero p] : jqNModC Qbar (1 * p) = jqNModC Qbar p := by
  have : NeZero (1 * p) := by rwa [one_mul]
  show qExpand Qbar (1 * p) (jqModC Qbar) = qExpand Qbar p (jqModC Qbar)
  exact qExpand_congr (one_mul p) _

private theorem core_identity {p : ℕ} [NeZero p] (data : ModularPolynomialData p) :
    data.Φ.eval₂ (Polynomial.aeval (R := ℤ) (jqModC Qbar)).toRingHom (jqNModC Qbar p) = 0 := by
  have h := ModularPolynomialData.eval_jqNModC_mul_eq_zero data Qbar 1
  rwa [jqNModC_one, jqNModC_one_mul] at h

private def phi0 : Polynomial ℤ →+* E1 := (Polynomial.aeval jgen).toRingHom

private def phiHat {p : ℕ} [NeZero p] (data : ModularPolynomialData p) : Polynomial E1 :=
  data.Φ.map phi0

private theorem phiHat_monic {p : ℕ} [NeZero p] (data : ModularPolynomialData p) :
    (phiHat data).Monic := data.monic.map phi0

private theorem phiHat_natDegree {p : ℕ} [NeZero p] (hp : p.Prime) (data : ModularPolynomialData p) :
    (phiHat data).natDegree = p + 1 := by
  rw [phiHat, data.monic.natDegree_map, data.natDegree_eq, dedekindPsi_prime hp]

private theorem aeval_phiHat_eq_zero {p : ℕ} [NeZero p] (data : ModularPolynomialData p) :
    Polynomial.aeval (R := E1) (jqNModC Qbar p) (phiHat data) = 0 := by
  rw [phiHat, Polynomial.aeval_def, Polynomial.eval₂_map,
    show (algebraMap E1 Lq).comp phi0 = (Polynomial.aeval (R := ℤ) (jqModC Qbar)).toRingHom from
      intPolyHom_ext (by simp [phi0])]
  exact core_identity data

private theorem minpoly_jqNModC_eq_phiHat {p : ℕ} [NeZero p] [hfp : Fact p.Prime]
    (data : ModularPolynomialData p) :
    minpoly E1 (jqNModC Qbar p) = phiHat data := by
  have hint : IsIntegral E1 (jqNModC Qbar p) :=
    isIntegral_jqNModC_of_modularPolynomialData Qbar data
  have hdvd : minpoly E1 (jqNModC Qbar p) ∣ phiHat data :=
    minpoly.dvd E1 _ (aeval_phiHat_eq_zero data)
  have hmm : (minpoly E1 (jqNModC Qbar p)).Monic := minpoly.monic hint
  have hdegmin : (minpoly E1 (jqNModC Qbar p)).natDegree = p + 1 := by
    have hfr := finrank_adjoin_jqNModC_eq_of_prime p
    rw [IntermediateField.adjoin.finrank hint] at hfr
    exact hfr
  obtain ⟨c, hc⟩ := hdvd
  have hc0 : c ≠ 0 := by
    intro h
    exact (phiHat_monic data).ne_zero (by rw [hc, h, mul_zero])
  have hdegc : c.natDegree = 0 := by
    have h2 := phiHat_natDegree hfp.out data
    rw [hc, Polynomial.natDegree_mul hmm.ne_zero hc0, hdegmin] at h2
    omega
  obtain ⟨a, rfl⟩ := Polynomial.natDegree_eq_zero.mp hdegc
  have hlead := congrArg Polynomial.leadingCoeff hc
  rw [Polynomial.leadingCoeff_mul, hmm.leadingCoeff, one_mul,
    (phiHat_monic data).leadingCoeff, Polynomial.leadingCoeff_C] at hlead
  rw [hc, ← hlead, map_one, mul_one]

private theorem natDegree_minpoly_jqNModC {p : ℕ} [NeZero p] [Fact p.Prime]
    (data : ModularPolynomialData p) :
    (minpoly E1 (jqNModC Qbar p)).natDegree = p + 1 := by
  rw [minpoly_jqNModC_eq_phiHat data]
  exact phiHat_natDegree ‹Fact p.Prime›.out data

private def phi1 : Polynomial Qbar →+* E1 := (Polynomial.aeval (R := Qbar) jgen).toRingHom

private theorem algebraMap_comp_phi1 :
    (algebraMap E1 Lq).comp phi1 = (Polynomial.aeval (R := Qbar) (jqModC Qbar)).toRingHom := by
  refine Polynomial.ringHom_ext' ?_ ?_
  · refine RingHom.ext fun c => ?_
    show algebraMap E1 Lq (phi1 (Polynomial.C c))
      = (Polynomial.aeval (R := Qbar) (jqModC Qbar)) (Polynomial.C c)
    have h1 : phi1 (Polynomial.C c) = algebraMap Qbar E1 c := by
      show (Polynomial.aeval (R := Qbar) jgen) (Polynomial.C c) = _
      rw [Polynomial.aeval_C]
    rw [h1, ← IsScalarTower.algebraMap_apply, Polynomial.aeval_C]
  · show algebraMap E1 Lq (phi1 Polynomial.X)
      = (Polynomial.aeval (R := Qbar) (jqModC Qbar)) Polynomial.X
    have h1 : phi1 Polynomial.X = jgen := by
      show (Polynomial.aeval (R := Qbar) jgen) Polynomial.X = _
      rw [Polynomial.aeval_X]
    rw [h1, Polynomial.aeval_X]
    rfl

private theorem phi1_injective : Function.Injective phi1 := by
  have htr : Transcendental Qbar (jqModC Qbar) := transcendental_jqModC Qbar
  have hinj : Function.Injective ⇑((algebraMap E1 Lq).comp phi1) := by
    rw [algebraMap_comp_phi1]
    exact transcendental_iff_injective.mp htr
  rw [RingHom.coe_comp] at hinj
  exact Function.Injective.of_comp hinj

private theorem eq_zero_of_natDegree_lt_of_eval_bar_eq_zero {p : ℕ} [NeZero p] [Fact p.Prime]
    (data : ModularPolynomialData p) (r : Polynomial (Polynomial Qbar))
    (hdeg : r.natDegree < p + 1)
    (hr : r.eval₂ (Polynomial.aeval (R := Qbar) (jqModC Qbar)).toRingHom (jqNModC Qbar p) = 0) :
    r = 0 := by
  have haev : Polynomial.aeval (R := E1) (jqNModC Qbar p) (r.map phi1) = 0 := by
    rw [Polynomial.aeval_def, Polynomial.eval₂_map, algebraMap_comp_phi1]
    exact hr
  have hdvd : minpoly E1 (jqNModC Qbar p) ∣ r.map phi1 := minpoly.dvd E1 _ haev
  have hmap0 : r.map phi1 = 0 := by
    by_contra hne
    have hle := Polynomial.natDegree_le_of_dvd hdvd hne
    have hlt : (r.map phi1).natDegree < p + 1 :=
      lt_of_le_of_lt (Polynomial.natDegree_map_le) hdeg
    rw [natDegree_minpoly_jqNModC data] at hle
    omega
  exact Polynomial.map_eq_zero_iff phi1_injective |>.mp hmap0

end Crux

section RatFuncWorld
open Polynomial

variable {p : ℕ} [NeZero p]

private def ΦF (data : ModularPolynomialData p) : Polynomial (RatFunc Qbar) :=
  data.Φ.map (Polynomial.aeval (R := ℤ) (RatFunc.X : RatFunc Qbar)).toRingHom

private theorem ΦF_monic (data : ModularPolynomialData p) : (ΦF data).Monic := data.monic.map _

private theorem ΦF_natDegree (hp : p.Prime) (data : ModularPolynomialData p) :
    (ΦF data).natDegree = p + 1 := by
  rw [ΦF, data.monic.natDegree_map, data.natDegree_eq, dedekindPsi_prime hp]

private theorem eval₂_Φ_bar (data : ModularPolynomialData p) :
    data.Φ.eval₂ (Polynomial.aeval (R := ℤ) (jBar p : F' p)).toRingHom (jpBar p) = 0 := by
  apply (algebraMap (F' p) Lq).injective
  rw [map_zero, Polynomial.hom_eval₂]
  have hhom : (algebraMap (F' p) Lq).comp
        (Polynomial.aeval (R := ℤ) (jBar p : F' p)).toRingHom =
      (Polynomial.aeval (R := ℤ) (jqModC Qbar)).toRingHom :=
    intPolyHom_ext (by rw [← ModularCurve.coeffEmb_jq]; simp)
  rw [hhom,
    show algebraMap (F' p) Lq (jpBar p) = jqNModC Qbar p
      by rw [← ModularCurve.coeffEmb_jqN]; rfl]
  exact core_identity data

variable (φ : RatFunc Qbar →ₐ[Qbar] F' p)
variable (hφX : φ (algebraMap (Polynomial Qbar) (RatFunc Qbar) X) = jBar p)

include hφX

private theorem aeval_ΦF_eq_zero (data : ModularPolynomialData p) :
    letI := algebraAlong φ
    Polynomial.aeval (R := RatFunc Qbar) (jpBar p : F' p) (ΦF data) = 0 := by
  letI := algebraAlong φ
  rw [ΦF, Polynomial.aeval_def, Polynomial.eval₂_map,
    show (algebraMap (RatFunc Qbar) (F' p)).comp
        (Polynomial.aeval (R := ℤ) (RatFunc.X : RatFunc Qbar)).toRingHom
      = (Polynomial.aeval (R := ℤ) (jBar p : F' p)).toRingHom from
      intPolyHom_ext (by
        show φ (Polynomial.aeval (R := ℤ) (RatFunc.X : RatFunc Qbar) X) = _
        rw [aeval_X]; simpa [← RatFunc.algebraMap_X] using hφX)]
  exact eval₂_Φ_bar data

private theorem isIntegral_jpBar (data : ModularPolynomialData p) :
    letI := algebraAlong φ
    IsIntegral (RatFunc Qbar) (jpBar p : F' p) :=
  ⟨ΦF data, ΦF_monic data, aeval_ΦF_eq_zero φ hφX data⟩

private theorem eq_zero_of_natDegree_lt_of_aeval_eq_zero_F [Fact p.Prime]
    (data : ModularPolynomialData p) (r : Polynomial (RatFunc Qbar))
    (hdeg : r.natDegree < p + 1)
    (hr : letI := algebraAlong φ
      Polynomial.aeval (R := RatFunc Qbar) (jpBar p : F' p) r = 0) :
    r = 0 := by
  letI := algebraAlong φ

  rcases eq_or_ne r 0 with rfl | hr0
  · rfl

  set r' : Polynomial (Polynomial Qbar) :=
    IsLocalization.integerNormalization (nonZeroDivisors (Polynomial Qbar)) r with hr'

  have hdeg' : r'.natDegree < p + 1 := by
    refine lt_of_le_of_lt ?_ hdeg
    rcases eq_or_ne r' 0 with h0 | h0
    · simp [h0]
    · exact Polynomial.le_natDegree_of_mem_supp r'.natDegree
        (IsLocalization.integerNormalization_support _ r (Polynomial.natDegree_mem_support_of_nonzero h0))

  have hr'0 : r'.eval₂ (Polynomial.aeval (R := Qbar) (jqModC Qbar)).toRingHom
      (jqNModC Qbar p) = 0 := by

    have h1 : r'.eval₂ ((algebraMap (RatFunc Qbar) (F' p)).comp
        (algebraMap (Polynomial Qbar) (RatFunc Qbar))) (jpBar p) = 0 := by
      rw [Polynomial.aeval_def] at hr
      exact IsLocalization.integerNormalization_eval₂_eq_zero _ _ r hr

    have hhom : (algebraMap (RatFunc Qbar) (F' p)).comp
        (algebraMap (Polynomial Qbar) (RatFunc Qbar))
        = (Polynomial.aeval (R := Qbar) (jBar p : F' p)).toRingHom := by
      refine Polynomial.ringHom_ext' ?_ ?_
      · refine RingHom.ext fun c => ?_
        show φ (algebraMap (Polynomial Qbar) (RatFunc Qbar) (Polynomial.C c)) = _
        rw [RatFunc.algebraMap_C, ← RatFunc.algebraMap_eq_C, φ.commutes]
        simp
      · show φ (algebraMap (Polynomial Qbar) (RatFunc Qbar) X) = _
        rw [hφX]; simp
    rw [hhom] at h1

    have h2 := congrArg (algebraMap (F' p) Lq) h1
    rw [map_zero, Polynomial.hom_eval₂] at h2
    have hhom2 : (algebraMap (F' p) Lq).comp
        (Polynomial.aeval (R := Qbar) (jBar p : F' p)).toRingHom
        = (Polynomial.aeval (R := Qbar) (jqModC Qbar)).toRingHom := by
      refine Polynomial.ringHom_ext' ?_ ?_
      · exact RingHom.ext fun c => by
          simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe,
            AlgHom.coe_toRingHom, Polynomial.aeval_C]
          exact (IsScalarTower.algebraMap_apply _ _ _ c).symm
      · rw [← ModularCurve.coeffEmb_jq]; simp
    rw [hhom2,
      show algebraMap (F' p) Lq (jpBar p) = jqNModC Qbar p
        by rw [← ModularCurve.coeffEmb_jqN]; rfl] at h2
    exact h2

  have : r' = 0 := eq_zero_of_natDegree_lt_of_eval_bar_eq_zero data r' hdeg' hr'0
  rwa [hr', IsLocalization.integerNormalization_eq_zero_iff (le_refl _)] at this

private theorem minpoly_jpBar_eq_ΦF [hfp : Fact p.Prime] (data : ModularPolynomialData p) :
    letI := algebraAlong φ
    minpoly (RatFunc Qbar) (jpBar p : F' p) = ΦF data := by
  letI := algebraAlong φ
  have hint : IsIntegral (RatFunc Qbar) (jpBar p : F' p) := isIntegral_jpBar φ hφX data
  have hdvd : minpoly (RatFunc Qbar) (jpBar p) ∣ ΦF data :=
    minpoly.dvd (RatFunc Qbar) _ (aeval_ΦF_eq_zero φ hφX data)
  have hmm : (minpoly (RatFunc Qbar) (jpBar p : F' p)).Monic := minpoly.monic hint
  obtain ⟨c, hc⟩ := hdvd
  have hc0 : c ≠ 0 := by
    intro h
    exact (ΦF_monic data).ne_zero (by rw [hc, h, mul_zero])
  have hdegc : c.natDegree = 0 := by
    by_contra hne

    have hlt : (minpoly (RatFunc Qbar) (jpBar p : F' p)).natDegree < p + 1 := by
      have h2 := ΦF_natDegree hfp.out data
      rw [hc, Polynomial.natDegree_mul hmm.ne_zero hc0] at h2
      omega
    have h0 : minpoly (RatFunc Qbar) (jpBar p : F' p) = 0 :=
      eq_zero_of_natDegree_lt_of_aeval_eq_zero_F φ hφX data _ hlt (minpoly.aeval _ _)
    exact hmm.ne_zero h0
  obtain ⟨a, rfl⟩ := Polynomial.natDegree_eq_zero.mp hdegc
  have hlead := congrArg Polynomial.leadingCoeff hc
  rw [Polynomial.leadingCoeff_mul, hmm.leadingCoeff, one_mul,
    (ΦF_monic data).leadingCoeff, Polynomial.leadingCoeff_C] at hlead
  rw [hc, ← hlead, map_one, mul_one]

private theorem natDegree_minpoly_jpBar [Fact p.Prime] (data : ModularPolynomialData p) :
    letI := algebraAlong φ
    (minpoly (RatFunc Qbar) (jpBar p : F' p)).natDegree = p + 1 := by
  rw [minpoly_jpBar_eq_ΦF φ hφX data]
  exact ΦF_natDegree ‹Fact p.Prime›.out data

end RatFuncWorld

end Cap
p2m_reactivate "P2MW.S_ModularCurve_place_eq_of_modularPolynomial_rootMultiplicity_eq_one.N4dSol.Cap"

section Dock

variable (p : ℕ) [NeZero p]

private theorem dedekindPsi_prime' {q : ℕ} (hq : q.Prime) : dedekindPsi q = q + 1 := by
  have h1q : (1 : ℕ) ≠ q := hq.one_lt.ne
  rw [dedekindPsi, Nat.Prime.divisors hq]
  rw [show ({1, q} : Finset ℕ) = insert 1 {q} from rfl]
  rw [Finset.filter_insert, if_pos squarefree_one, Finset.filter_singleton,
    if_pos hq.squarefree, Finset.sum_insert (by simp [h1q]), Finset.sum_singleton,
    Nat.div_one, Nat.div_self hq.pos]

private theorem QΦ_map_eq (data : ModularPolynomialData p) (j₁ : Qbar)
    (ψ : Polynomial ℤ →+* RatFunc Qbar) (hψ : ψ Polynomial.X = RatFunc.X) :
    (QΦ data j₁).map (algebraMap (vP j₁).toValuationSubring (RatFunc Qbar)) = data.Φ.map ψ := by
  rw [QΦ, Polynomial.map_map]
  congr 1
  exact intPolyHom_ext (by rw [RingHom.comp_apply, cf_X, hψ])

private theorem hQ_engine [Fact p.Prime] (data : ModularPolynomialData p) (j₁ : Qbar) :
    letI := algebraAlong (phi p)
    (QΦ data j₁).map (algebraMap (vP j₁).toValuationSubring (RatFunc Qbar))
      = minpoly (RatFunc Qbar) (jpBar p : modularFunctionFieldBar p) := by
  rw [QΦ_map_eq p data j₁ (Polynomial.aeval (R := ℤ) (RatFunc.X : RatFunc Qbar)).toRingHom
    (show (Polynomial.aeval (R := ℤ) (RatFunc.X : RatFunc Qbar)) Polynomial.X = RatFunc.X from
      Polynomial.aeval_X _)]
  exact (Cap.minpoly_jpBar_eq_ΦF (phi p) (phi_X p) data).symm

private theorem pswap_ne_zero [Fact p.Prime] (data : ModularPolynomialData p) (j₁ j₂ : Qbar) :
    pswap data.Φ j₂ ≠ 0 := by
  letI : Algebra (RatFunc Qbar) (modularFunctionFieldBar p) := algebraAlong (phi p)
  haveI : Module.Finite (RatFunc Qbar) (modularFunctionFieldBar p) := phi_finiteAlong p
  intro h0
  have hQ := hQ_engine p data j₁
  have hirr : Irreducible (minpoly (RatFunc Qbar) (jpBar p : modularFunctionFieldBar p)) :=
    minpoly.irreducible (Algebra.IsIntegral.isIntegral _)
  have hroot' : (minpoly (RatFunc Qbar) (jpBar p : modularFunctionFieldBar p)).IsRoot
      (algebraMap (vP j₁).toValuationSubring (RatFunc Qbar) (bC j₁ j₂)) := by
    rw [← hQ, Polynomial.IsRoot, Polynomial.eval_map, Polynomial.eval₂_at_apply,
      show algebraMap (vP j₁).toValuationSubring (RatFunc Qbar) ((QΦ data j₁).eval (bC j₁ j₂))
        = (((QΦ data j₁).eval (bC j₁ j₂) : (vP j₁).toValuationSubring) : RatFunc Qbar) from rfl,
      QΦ, coe_eval_eq, h0, map_zero]
  have hdeg1 := Polynomial.degree_eq_one_of_irreducible_of_root hirr hroot'
  have hnat : (minpoly (RatFunc Qbar) (jpBar p : modularFunctionFieldBar p)).natDegree = p + 1 := by
    rw [← hQ, (QΦ_monic data j₁).natDegree_map, QΦ, data.monic.natDegree_map, data.natDegree_eq,
      dedekindPsi_prime' (Fact.out : p.Prime)]
  have h1 : (minpoly (RatFunc Qbar) (jpBar p : modularFunctionFieldBar p)).natDegree = 1 :=
    Polynomial.natDegree_eq_of_degree_eq_some hdeg1
  have h2 := (Fact.out : p.Prime).two_le
  omega

end Dock
p2m_reactivate "P2MW.S_ModularCurve_place_eq_of_modularPolynomial_rootMultiplicity_eq_one.N4dSol.Cap"

section Assembly

variable (p : ℕ) [NeZero p]

private theorem hnorm_engine [Fact p.Prime] (data : ModularPolynomialData p) (j₁ j₂ : Qbar) :
    letI := algebraAlong (phi p)
    (vP j₁).ord (Algebra.norm (RatFunc Qbar)
        ((jpBar p : modularFunctionFieldBar p) - phi p ((bC j₁ j₂ : (vP j₁).toValuationSubring) : RatFunc Qbar)))
      = (vP j₁).ord (((QΦ data j₁).eval (bC j₁ j₂) : (vP j₁).toValuationSubring) : RatFunc Qbar) := by
  letI : Algebra (RatFunc Qbar) (modularFunctionFieldBar p) := algebraAlong (phi p)
  haveI : Module.Finite (RatFunc Qbar) (modularFunctionFieldBar p) := phi_finiteAlong p
  exact NR.ord_norm_sub_eq (vP j₁) (QΦ data j₁) (hQ_engine p data j₁) (hdeg_engine p) (bC j₁ j₂)

private theorem main (hp : p.Prime) (data : ModularCurve.ModularPolynomialData p)
    (j₁ j₂ : AlgebraicClosure ℚ)
    (hroot : data.Φ.eval₂ (Polynomial.aeval (R := ℤ) j₁).toRingHom j₂ = 0)
    (hmult : (data.Φ.map (Polynomial.aeval (R := ℤ) j₁).toRingHom).rootMultiplicity j₂ = 1)
    (x x' : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar p))
    (hx₁ : 0 < x.ord (jBar p - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar p) j₁))
    (hx₂ : 0 < x.ord (jpBar p - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar p) j₂))
    (hx'₁ : 0 < x'.ord (jBar p - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar p) j₁))
    (hx'₂ : 0 < x'.ord (jpBar p - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar p) j₂)) :
    x = x' := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : HasPrincipalDivisors Qbar (modularFunctionFieldBar p) :=
    ModularCurve.hasPrincipalDivisors_modularFunctionFieldBar_unconditional p
  have hb : phi p ((bC j₁ j₂ : (vP j₁).toValuationSubring) : RatFunc Qbar)
      = algebraMap Qbar (modularFunctionFieldBar p) j₂ := by
    rw [coe_bC]
    exact (phi p).commutes j₂
  obtain ⟨w₀, -, -, -, -, huniq⟩ :=
    SR.exists_place_of_simple_root_along (K := Qbar) (phi p) (phi_isIntegral p)
      (phi_finiteAlong p) (vP j₁) (QΦ_monic data j₁) (hx_engine p data j₁ (phi p) (phi_X p))
      (bC j₁ j₂) (hroot_engine data j₁ j₂ hroot (pswap_ne_zero p data j₁ j₂))
      (hsimple_engine data j₁ j₂ hmult) (hnorm_engine p data j₁ j₂)
  have e1 : x = w₀ :=
    huniq x (restrictAlong_eq_vP j₁ (phi p) (phi_isIntegral p) (phi_X p) x hx₁)
      (by rw [hb]; exact hx₂)
  have e2 : x' = w₀ :=
    huniq x' (restrictAlong_eq_vP j₁ (phi p) (phi_isIntegral p) (phi_X p) x' hx'₁)
      (by rw [hb]; exact hx'₂)
  exact e1.trans e2.symm

end Assembly
p2m_reactivate "P2MW.S_ModularCurve_place_eq_of_modularPolynomial_rootMultiplicity_eq_one.N4dSol.Cap"

end N4dSol
p2m_reactivate "P2MW.S_ModularCurve_place_eq_of_modularPolynomial_rootMultiplicity_eq_one.N4dSol.Cap P2MW.S_ModularCurve_place_eq_of_modularPolynomial_rootMultiplicity_eq_one.N4dSol"

end
p2m_reactivate "P2MW.S_ModularCurve_place_eq_of_modularPolynomial_rootMultiplicity_eq_one.N4dSol.Cap P2MW.S_ModularCurve_place_eq_of_modularPolynomial_rootMultiplicity_eq_one.N4dSol"

p2m_open "WeierstrassCurve AlgebraicCurve ModularCurve~dedekindPsi_prime"

theorem solution
    (p : ℕ) [NeZero p] (hp : p.Prime) (data : ModularCurve.ModularPolynomialData p)
    (j₁ j₂ : AlgebraicClosure ℚ)
    (hroot : data.Φ.eval₂ (Polynomial.aeval (R := ℤ) j₁).toRingHom j₂ = 0)
    (hmult : (data.Φ.map (Polynomial.aeval (R := ℤ) j₁).toRingHom).rootMultiplicity j₂ = 1)
    (x x' : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar p))
    (hx₁ : 0 < x.ord (jBar p - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar p) j₁))
    (hx₂ : 0 < x.ord (jpBar p - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar p) j₂))
    (hx'₁ : 0 < x'.ord (jBar p - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar p) j₁))
    (hx'₂ : 0 < x'.ord (jpBar p - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar p) j₂)) :
    x = x' :=
  N4dSol.main p hp data j₁ j₂ hroot hmult x x' hx₁ hx₂ hx'₁ hx'₂

end S_ModularCurve_place_eq_of_modularPolynomial_rootMultiplicity_eq_one
end P2MW
export P2MW.S_ModularCurve_place_eq_of_modularPolynomial_rootMultiplicity_eq_one (solution)
