-- Prove2me | solution 1 for GlobalTheory.WpFam.ExpP.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:29:13.31998+00:00
-- url     : https://prove2.me/submissions/63b894a3-2f09-4a0d-a880-6d39a1892982

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ZetaActRefl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_WeierstrassDivisionValueQExpansionStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_WeierstrassConstantQExpansionStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasQExpansionNormalizedWeierstrassPTorsion
import Theorems.Thm_GlobalTheory_T_weierstrass_constant_q_expansion
import Theorems.Thm_GlobalTheory_T_weierstrass_division_value_q_expansion


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open GlobalTheory.QFam GlobalTheory.WpFam
open GlobalTheory GlobalTheory.WpFam GlobalTheory.WpFam.ExpP
namespace GlobalTheory.WpFam.ExpP
theorem _root_.solution : ∀ (N : ℕ) [NeZero N] (x : Fin 2 → ZMod N), HasQ N (wp N x) (cP N x) := by
  intro N _ x τ
  by_cases hx : x = 0
  · subst hx
    have h0 : wp N 0 τ = 0 := by
      simp [wp, tors, PeriodPair.weierstrassP_zero]
    simp only [cP, h0, if_true]
    simpa using (hasSum_zero : HasSum (fun _ : ℕ => (0 : ℂ)) 0)
  · have hB := GlobalTheory.T.weierstrass_division_value_q_expansion N x hx τ
    have hG := GlobalTheory.T.weierstrass_constant_q_expansion N τ
    have hd := hB.sub hG
    have hw : wp N x τ = wB N x τ - gN τ := by simp [wB]
    have hf : (fun n : ℕ => cP N x n * Complex.exp (2 * Real.pi * Complex.I * n * τ / N)) =
        fun n : ℕ => cB N x n * Complex.exp (2 * Real.pi * Complex.I * n * τ / N) -
          cG N n * Complex.exp (2 * Real.pi * Complex.I * n * τ / N) := by
      funext n
      simp [cP, hx, sub_mul]
    rw [hw, hf]
    exact hd
end GlobalTheory.WpFam.ExpP
