-- Prove2me | solution 1 for OAI.SevenEighths.CubicDyadicDecay.poisson_envelope_descendant_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:18:55.006361+00:00
-- url     : https://prove2.me/submissions/80da55e1-6f8f-409b-afd5-8a0c0b18482d

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Definitions.Def_OAI_NumberTheory_DirichletL_CubicDyadicDecay
import Theorems.Thm_OAI_SevenEighths_CubicDyadicDecay_mixed_descendant_le
import Theorems.Thm_OAI_SevenEighths_CubicDyadicDecay_secondary_descendant_le

set_option autoImplicit false
open OAI
open OAI.SevenEighths OAI.SevenEighths.CubicDyadicDecay
open scoped BigOperators
noncomputable section
namespace OAI.SevenEighths.CubicDyadicDecay
theorem _root_.solution (M N e d δ ξ P Q : ℝ)
    (hM : 0 < M) (hN : 0 < N) (he : 1 ≤ e) (hed : e ≤ d)
    (hδ : 0 ≤ δ) (hξ : 1 ≤ ξ) (hP : 0 ≤ P) (hQ : 0 ≤ Q) :
    (N/d)^(3*δ)*(M/e)^(-δ) *
        (P*((M/e)*(N/d))^(2/3 : ℝ) + Q*(M/e)^(1-ξ)*(N/d)^(2*ξ-1)) ≤
      N^(3*δ)*M^(-δ) * (P*(M*N)^(2/3 : ℝ)+Q*M^(1-ξ)*N^(2*ξ-1)) := by
  have hm := mul_le_mul_of_nonneg_left (mixed_descendant_le M N e d δ hM hN he hed hδ) hP
  have hs := mul_le_mul_of_nonneg_left
    (secondary_descendant_le M N e d δ ξ hM hN he hed hδ hξ) hQ
  nlinarith [hm, hs]
end OAI.SevenEighths.CubicDyadicDecay
