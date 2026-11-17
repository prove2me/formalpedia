-- Prove2me | solution 1 for N25.cusp_complex_simple_poles_card_le_five
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:44:20.431442+00:00
-- url     : https://prove2.me/submissions/1b469106-95c3-447f-9ce5-ee972c019050

import Mathlib
import Definitions.Def_N25
import Definitions.Def_ModularCurve_ComplexPlaceDictionaryOf
import Theorems.Thm_N25_cusp_complex_endpoints
import Definitions.Def_ModularCurve_JqCoeff
import Theorems.Thm_ModularCurve_jqModC_mem_intFormRatiosC
import Theorems.Thm_ModularCurve_exists_ringHom_place_order_eq_mul_ord_of_qExpansion_slash
import Theorems.Thm_ModularCurve_ord_eq_neg_width_of_order_eq_mul_ord_of_qExpansion_slash
import Theorems.Thm_ModularCurve_finrank_adjoin_jqModC_laurentBaseChange_qExpFunctionFieldC_gammaH_eq_index
import Theorems.Thm_N25_cusp_complex_endpoint_exhausts_poles
import Theorems.Thm_ModularCurve_exists_tendsto_realizeOf_mul_exp_of_not_mem_toValuationSubring
import Theorems.Thm_N25_cusp_complex_endpoint_left_GammaH
import Theorems.Thm_N25_Gamma025_label13_factorization
import Theorems.Thm_KeystoneLadder_SameP1Vec_trans

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency.types false

open ModularCurve AlgebraicCurve CongruenceSubgroup

open scoped MatrixGroups Topology

namespace N25

/-- There are at most five actual complex simple poles of the literal j-series. -/
theorem _root_.solution
    (j : laurentBaseChange ℂ (xHFunctionField 25 N25.H25))
    (hj : (j : LaurentSeries ℂ) = jqModC ℂ) :
    Finite {P : Place ℂ (laurentBaseChange ℂ (xHFunctionField 25 N25.H25)) // P.ord j = -1} ∧
      Nat.card {P : Place ℂ (laurentBaseChange ℂ (xHFunctionField 25 N25.H25)) // P.ord j = -1} ≤ 5 := by
  classical
  obtain ⟨jC, endpoint, hjC, hwidth, hmem, _⟩ := cusp_complex_endpoints
  have heqj : jC = j := Subtype.ext (hjC.trans hj.symm)
  subst jC
  let A : SL(2, ℤ) := ⟨!![13,1;25,2], by norm_num [Matrix.det_fin_two]⟩
  let T : Gamma0 25 := ⟨A, by
    apply Gamma0_mem.mpr
    change ((25 : ℤ) : ZMod 25) = 0
    decide⟩
  have hT : CohCarrier.gamma0Units 25 T = (ZMod.unitOfCoprime 13 (by decide))⁻¹ := by
    apply eq_inv_iff_mul_eq_one.mpr
    apply Units.ext
    change (2 : ZMod 25) * 13 = 1
    decide
  let S := {P : Place ℂ (laurentBaseChange ℂ (xHFunctionField 25 N25.H25)) // P.ord j = -1}
  have hall (P : S) : ∃ k : Fin 5, endpoint (A ^ k.val) = P.val := by
    have hp : P.val.ord j < 0 := by rw [P.property]; norm_num
    obtain ⟨B, hB⟩ := cusp_complex_endpoint_exhausts_poles endpoint hmem j hj P.val hp
    have hw := hwidth B
    rw [hB, P.property] at hw
    have hc : (B 1 0 : ZMod 25).val = 0 := by
      by_contra hn
      simp only [hn, ↓reduceIte] at hw
      split_ifs at hw <;> norm_num at hw
    have hBG : B ∈ Gamma0 25 := by
      apply Gamma0_mem.mpr
      exact (ZMod.val_eq_zero _).mp hc
    obtain ⟨k, C, hC, hBC⟩ := N25.Gamma025_label13_factorization T hT ⟨B, hBG⟩
    refine ⟨k, ?_⟩
    change B = C * A ^ k.val at hBC
    rw [hBC] at hB
    exact (cusp_complex_endpoint_left_GammaH endpoint hmem C (A ^ k.val) hC).symm.trans hB
  choose index hindex using hall
  have hinj : Function.Injective index := by
    intro P Q h
    apply Subtype.ext
    exact (hindex P).symm.trans ((congrArg (fun k : Fin 5 => endpoint (A ^ k.val)) h).trans (hindex Q))
  let : Finite S := Finite.of_injective index hinj
  refine ⟨inferInstance, ?_⟩
  simpa only [Nat.card_fin] using Nat.card_le_card_of_injective index hinj

end N25
