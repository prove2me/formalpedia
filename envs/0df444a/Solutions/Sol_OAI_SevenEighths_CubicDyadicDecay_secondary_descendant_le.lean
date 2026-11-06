-- Prove2me | solution 1 for OAI.SevenEighths.CubicDyadicDecay.secondary_descendant_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:02:11.848357+00:00
-- url     : https://prove2.me/submissions/c3b16dd9-78ec-421e-98b5-02ffbfb25e51

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Definitions.Def_OAI_NumberTheory_DirichletL_CubicDyadicDecay
import Theorems.Thm_OAI_SevenEighths_CubicDyadicDecay_monomial_descendant_le
import Theorems.Thm_OAI_SevenEighths_CubicDyadicDecay_secondary_monomial_identity

set_option autoImplicit false
open OAI
open OAI.SevenEighths OAI.SevenEighths.CubicDyadicDecay
open scoped BigOperators
noncomputable section
namespace OAI.SevenEighths.CubicDyadicDecay
theorem _root_.solution (M N e d δ ξ : ℝ) (hM : 0 < M) (hN : 0 < N)
    (he : 1 ≤ e) (hed : e ≤ d) (hδ : 0 ≤ δ) (hξ : 1 ≤ ξ) :
    (N/d)^(3*δ)*(M/e)^(-δ)*(M/e)^(1-ξ)*(N/d)^(2*ξ-1) ≤
      N^(3*δ)*M^(-δ)*M^(1-ξ)*N^(2*ξ-1) := by
  have he0 : 0 < e := by linarith
  have hd0 : 0 < d := by linarith
  rw [secondary_monomial_identity (M/e) (N/d) δ ξ (div_pos hM he0) (div_pos hN hd0),
    secondary_monomial_identity M N δ ξ hM hN]
  exact monomial_descendant_le M N e d (1-ξ-δ) (2*ξ-1+3*δ) hM hN he hed
    (by linarith) (by linarith)
end OAI.SevenEighths.CubicDyadicDecay
