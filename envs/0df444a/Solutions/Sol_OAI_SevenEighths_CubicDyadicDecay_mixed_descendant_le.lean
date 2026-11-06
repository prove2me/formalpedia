-- Prove2me | solution 1 for OAI.SevenEighths.CubicDyadicDecay.mixed_descendant_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:02:11.092206+00:00
-- url     : https://prove2.me/submissions/6132bf38-1fd3-41ad-b58b-07d54db4f4ca

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
import Theorems.Thm_OAI_SevenEighths_CubicDyadicDecay_mixed_monomial_identity

set_option autoImplicit false
open OAI
open OAI.SevenEighths OAI.SevenEighths.CubicDyadicDecay
open scoped BigOperators
noncomputable section
namespace OAI.SevenEighths.CubicDyadicDecay
theorem _root_.solution (M N e d δ : ℝ) (hM : 0 < M) (hN : 0 < N)
    (he : 1 ≤ e) (hed : e ≤ d) (hδ : 0 ≤ δ) :
    (N/d)^(3*δ)*(M/e)^(-δ)*((M/e)*(N/d))^(2/3 : ℝ) ≤
      N^(3*δ)*M^(-δ)*(M*N)^(2/3 : ℝ) := by
  have he0 : 0 < e := by linarith
  have hd0 : 0 < d := by linarith
  rw [mixed_monomial_identity (M/e) (N/d) δ (div_pos hM he0) (div_pos hN hd0),
    mixed_monomial_identity M N δ hM hN]
  exact monomial_descendant_le M N e d (2/3-δ) (2/3+3*δ) hM hN he hed
    (by linarith) (by linarith)
end OAI.SevenEighths.CubicDyadicDecay
