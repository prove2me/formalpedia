-- Prove2me | solution 1 for GlobalTheory.Nef.functionFieldPlace_exists_const_sub_lt_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T01:43:58.963979+00:00
-- url     : https://prove2.me/submissions/730a3807-9e6a-4666-aa3e-579493f4c201

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsAdmissibleIntegralBasisChangeOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FunctionFieldOneVariableTranscendentalFiniteAndEStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FunctionFieldPlaceIsDVRAndResidueEqGround
import Theorems.Thm_GlobalTheory_Nef_place_le_one_const
import Theorems.Thm_GlobalTheory_T_functionFieldOneVariable_transcendental_finite_and_ext
import Theorems.Thm_GroundTheory_FunctionField_Place_ordHom_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.FunctionField.Place.ordHom_apply



set_option autoImplicit false
open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef
open GlobalTheory GlobalTheory.Nef
namespace GlobalTheory.Nef
theorem _root_.solution {k F : Type} [Field k] [IsAlgClosed k] [Field F] [Algebra k F]
    (hF : IsFF k F) (v : Place k F) (x : F) (hx : v.1 x ≤ 1) :
    ∃ c : k, v.1 (x - algebraMap k F c) < 1 := by
  by_contra hne
  push_neg at hne
  have h1 : ∀ c : k, v.1 (x - algebraMap k F c) = 1 := fun c =>
    le_antisymm ((v.1.map_sub _ _).trans (max_le hx (place_le_one_const v c))) (hne c)
  have hq : ∀ q : k[X], q ≠ 0 → v.1 (Polynomial.aeval x q) = 1 := by
    intro q hq0
    have hs := Polynomial.C_leadingCoeff_mul_prod_multiset_X_sub_C (p := q) IsAlgClosed.card_roots_eq_natDegree
    rw [← hs, map_mul, map_multiset_prod, Multiset.map_map, map_mul, map_multiset_prod]
    simp only [Polynomial.aeval_C, Function.comp_def, map_sub, Polynomial.aeval_X, Multiset.map_map]
    rw [(v.2.2 _ (Polynomial.leadingCoeff_ne_zero.mpr hq0)), one_mul]
    simp [h1]
  have htr : Transcendental k x := by
    rintro ⟨q, hq0, hqx⟩
    have := hq q hq0
    rw [hqx, map_zero] at this
    exact zero_ne_one this
  haveI hfin : FiniteDimensional k⟮x⟯ F := (GlobalTheory.T.functionFieldOneVariable_transcendental_finite_and_ext k F hF).1 x htr
  have hK : ∀ y ∈ k⟮x⟯, v.1 y ≤ 1 := by
    intro y hy
    obtain ⟨r, s, rfl⟩ := (IntermediateField.mem_adjoin_simple_iff k y).1 hy
    have hle : ∀ q : k[X], v.1 (Polynomial.aeval x q) ≤ 1 := fun q => by
      by_cases h0 : q = 0
      · simp [h0]
      · exact (hq q h0).le
    by_cases hs0 : s = 0
    · simp [hs0]
    · rw [map_div₀, hq s hs0, div_one]
      exact hle r
  have hint : ∀ y : F, v.1 y ≤ 1 := by
    intro y
    obtain ⟨f, hm, hf⟩ := Algebra.IsIntegral.isIntegral (R := k⟮x⟯) y
    have hc : ∀ i, v.1 (algebraMap k⟮x⟯ F (f.coeff i)) ≤ 1 := fun i => hK _ (f.coeff i).2
    by_cases hn : f.natDegree = 0
    · rw [Polynomial.natDegree_eq_zero] at hn
      obtain ⟨c, rfl⟩ := hn
      simp [hm.ne_zero_of_C] at hf
    simp only [Polynomial.eval₂_eq_sum_range, Finset.sum_range_succ, hm.coeff_natDegree, map_one,
      one_mul, add_eq_zero_iff_eq_neg] at hf
    apply_fun v.1 at hf
    rw [Valuation.map_neg, Valuation.map_pow] at hf
    contrapose! hf
    refine ne_of_lt (v.1.map_sum_lt ?_ ?_)
    · simp [hn, (hf.trans' (zero_lt_one)).ne']
    · intro i hi
      rw [Finset.mem_range] at hi
      rw [Valuation.map_mul, Valuation.map_pow]
      exact mul_lt_of_le_one_of_lt (hc _) <| pow_lt_pow_right₀ hf hi
  obtain ⟨z, hz⟩ := v.2.1 ((Multiplicative.ofAdd (1:ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))
  have := hint z
  rw [hz] at this
  exact absurd this (by decide)
end GlobalTheory.Nef
