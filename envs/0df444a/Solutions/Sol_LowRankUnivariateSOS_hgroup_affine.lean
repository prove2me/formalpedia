-- Prove2me | solution 1 for LowRankUnivariateSOS.hgroup_affine
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:02:35.18507+00:00
-- url     : https://prove2.me/submissions/80a4d0fa-67a2-4baf-a0e8-6af833538d0f

import Definitions.Def_LowRankUnivariateSOS_UnivariateAlgebraCore
import Mathlib.Tactic.Ring
import Definitions.Def_LowRankUnivariateSOS_UnivariateSOS
import Theorems.Thm_LowRankUnivariateSOS_isSOS_mul
import Theorems.Thm_LowRankUnivariateSOS_A_scalePair_left
import Theorems.Thm_LowRankUnivariateSOS_A_smul_right
import Theorems.Thm_LowRankUnivariateSOS_perpPair_fst
import Theorems.Thm_LowRankUnivariateSOS_perpPair_snd
import Theorems.Thm_LowRankUnivariateSOS_scalePair_fst
import Theorems.Thm_LowRankUnivariateSOS_scalePair_snd
import Theorems.Thm_LowRankUnivariateSOS_sigma2_perpPair
import Theorems.Thm_LowRankUnivariateSOS_sigma2_scalePair
import Theorems.Thm_LowRankUnivariateSOS_sigma2_smul
import Theorems.Thm_LowRankUnivariateSOS_smul_fst
import Theorems.Thm_LowRankUnivariateSOS_smul_snd
attribute [local simp] LowRankUnivariateSOS.A_scalePair_left
attribute [local simp] LowRankUnivariateSOS.A_smul_right
attribute [local simp] LowRankUnivariateSOS.perpPair_fst
attribute [local simp] LowRankUnivariateSOS.perpPair_snd
attribute [local simp] LowRankUnivariateSOS.scalePair_fst
attribute [local simp] LowRankUnivariateSOS.scalePair_snd
attribute [local simp] LowRankUnivariateSOS.sigma2_perpPair
attribute [local simp] LowRankUnivariateSOS.sigma2_scalePair
attribute [local simp] LowRankUnivariateSOS.sigma2_smul
attribute [local simp] LowRankUnivariateSOS.smul_fst
attribute [local simp] LowRankUnivariateSOS.smul_snd



set_option autoImplicit true
noncomputable section
open LowRankUnivariateSOS
namespace LowRankUnivariateSOS
theorem _root_.solution
    (g p q : Poly) :
    IsSOS p → IsSOS q → IsCoprime g q →
      ∃ s t : Poly, IsSOS s ∧ p = g * t + s * q := by
  intro hp hq hcop
  rcases hcop with ⟨a, b, hbez⟩
  let s : Poly := b ^ 2 * p * q
  let t : Poly := p * (2 * a - a ^ 2 * g)
  refine ⟨s, t, ?_, ?_⟩
  · have hb2 : IsSOS (b ^ 2) := ⟨b, 0, by simp [pow_two]⟩
    exact isSOS_mul (isSOS_mul hb2 hp) hq
  · apply Eq.symm
    have hbq : b * q = 1 - a * g := by
      calc
        b * q = (a * g + b * q) - a * g := by ring
        _ = 1 - a * g := by rw [hbez]
    calc
      g * t + s * q
          = p * (g * (2 * a - a ^ 2 * g) + b ^ 2 * q ^ 2) := by
              simp [s, t]
              ring
      _ = p * (a * g * (2 - a * g) + (b * q) ^ 2) := by
            ring
      _ = p * (a * g * (2 - a * g) + (1 - a * g) ^ 2) := by
            rw [hbq]
      _ = p := by
            ring
end LowRankUnivariateSOS
