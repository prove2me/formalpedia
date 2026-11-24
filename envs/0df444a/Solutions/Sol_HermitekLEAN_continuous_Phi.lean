-- Prove2me | solution 1 for HermitekLEAN.continuous_Phi
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:00:19.179664+00:00
-- url     : https://prove2.me/submissions/4450688c-0bfd-423a-9440-dd6cb80a3248

module
public import Definitions.Def_LeanPool_PhaseRetrieval_FourierParseval
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite_Definitions
public import Mathlib.Analysis.Complex.Isometry
public import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
public import Mathlib.MeasureTheory.Integral.Gamma
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermitek_TrueLevelBasis
public import Theorems.Thm_HermitekLEAN_qkn_real
attribute [local simp] HermitekLEAN.qkn_real

set_option autoImplicit true
@[expose] public section
public section
open Complex MeasureTheory Real Finset
open scoped BigOperators Topology
noncomputable section
open HermitekLEAN
namespace HermitekLEAN
theorem _root_.solution (k n : ℕ) : Continuous (Phi k n) := by
  unfold Phi
  refine continuous_const.mul ?_
  refine continuous_finsetSum _ ?_
  intro j hj
  have hpow : Continuous (fun z : ℂ => z ^ (n - j) * (star z) ^ (k - j)) :=
    (continuous_id.pow (n - j)).mul (continuous_star.pow (k - j))
  have hterm : Continuous (fun z : ℂ =>
      (((-1 : ℂ) ^ j) * (Nat.choose k j : ℂ) *
          ((Nat.factorial n : ℂ) / (Nat.factorial (n - j) : ℂ))) *
        (z ^ (n - j) * (star z) ^ (k - j))) := continuous_const.mul hpow
  simpa only [mul_assoc, RCLike.star_def] using hterm
end HermitekLEAN
