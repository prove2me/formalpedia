-- Prove2me | solution 1 for N25.cyclotomic_gamma
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:44:26.668657+00:00
-- url     : https://prove2.me/submissions/b97acacc-8dea-4baa-8d41-5c1635605372

import Mathlib
import Definitions.Def_N25
import Theorems.Thm_N25_gamma0_field_degree
import Theorems.Thm_ModularCurve_relfinrank_qExpFunctionFieldC_gamma0_gammaH_eq_index_of_charZero
import Theorems.Thm_ModularCurve_relfinrank_adjoin_image_coeffMap_eq_relfinrank_of_le
import Theorems.Thm_N25_gamma_field_fixes_gamma0
import Theorems.Thm_ModularCurve_exists_monoidHom_gamma0_algEquiv_qExpFunctionFieldC_gammaH_of_charZero
import Theorems.Thm_ModularCurve_diamondAutHBar_apply_coeffEmb_eq_coeffEmb_ringAut_apply
import Theorems.Thm_N25_gamma_field_order
import Theorems.Thm_ModularCurve_diamondAutHBar_mul_and_diamondAutHBar_one
import Theorems.Thm_N25_gamma0_genus_zero
import Definitions.Def_ModularCurve_JqCoeff
import Theorems.Thm_ModularCurve_jqModC_mem_intFormRatiosC
import Theorems.Thm_ModularCurve_finrank_adjoin_jqModC_laurentBaseChange_qExpFunctionFieldC_gammaH_eq_index
import Theorems.Thm_ModularCurve_natCard_fibres_jqModC_eq_natCard_doubleCoset_of_finrank_eq_index
import Theorems.Thm_ModularCurve_two_mul_genusFF_add_card_fibres_eq_finrank_add_two_of_gamma1_le
import Theorems.Thm_AlgebraicCurve_Pic0_sum_five_smul_eq_zero
import Definitions.Def_AlgebraicCurve_BaseChangeGalois
import Definitions.Def_AlgebraicCurve_DivisorPushPull
import Theorems.Thm_AlgebraicCurve_Divisor_sum_galois_smul_eq_pullback_pushforward
import Theorems.Thm_AlgebraicCurve_Pic0_subsingleton_of_genusFF_eq_zero
import Theorems.Thm_ModularCurve_isCurveOver_and_essFiniteType_laurentBaseChange_xHFunctionField

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency.types false

noncomputable section

open AlgebraicCurve ModularCurve

namespace N25

/-- The degree-five diamond cover has genus-zero quotient, so its trace
vanishes on every geometric degree-zero divisor class. -/
theorem _root_.solution (x : N25.J) :
    x + N25.gamma x + N25.gamma (N25.gamma x) + N25.gamma (N25.gamma (N25.gamma x))
      + N25.gamma (N25.gamma (N25.gamma (N25.gamma x))) = 0 := by
  classical
  let K := AlgebraicClosure ℚ
  let F₀ := laurentBaseChange K (qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 25))
  let F := xHFunctionFieldBar 25 H25
  have hle : F₀ ≤ F := gamma0_field_degree.1
  let g := diamondAutHBar 25 H25 (ZMod.unitOfCoprime 13 (by decide))
  have htop : F₀ = xHFunctionFieldBar 25 (⊤ : Subgroup (ZMod 25)ˣ) := by
    dsimp [F₀, xHFunctionFieldBar, xHFunctionField, xHFunctionFieldC]
    rw [CohCarrier.GammaH_top]
  obtain ⟨hcurve,hfinite⟩ :=
    isCurveOver_and_essFiniteType_laurentBaseChange_xHFunctionField K 25 ⊤
  have : IsCurveOver K F₀ := htop.symm ▸ hcurve
  have : Algebra.EssFiniteType K F₀ := htop.symm ▸ hfinite
  let : Subsingleton (Pic0 K F₀) := Pic0.subsingleton_of_genusFF_eq_zero gamma0_genus_zero
  have : HasPrincipalDivisors K F := (isCurveOver_and_essFiniteType_laurentBaseChange_xHFunctionField K 25 H25).1.toHasPrincipalDivisors
  have htrace := Pic0.sum_five_smul_eq_zero F₀ F hle g gamma_field_order
    gamma0_field_degree.2 (fun a => gamma_field_fixes_gamma0 1 ⟨a.val, hle a.property⟩ a.property) x
  have hp (n : ℕ) :
      SemilinearAut.ofAlgAut (g ^ n) • x = (gamma^[n]) x := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ', map_mul, mul_smul, Function.iterate_succ_apply']
      exact congrArg gamma ih
  simp only [hp] at htrace
  simpa only [Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ, Fin.sum_univ_zero,
    Function.iterate_zero_apply, Function.iterate_succ_apply', add_zero, Nat.reduceAdd,
    add_assoc] using htrace

end N25
