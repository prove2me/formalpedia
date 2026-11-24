-- Prove2me | solution 1 for HermitekLEAN.qkn_structure
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:49:20.281917+00:00
-- url     : https://prove2.me/submissions/67cba891-169a-47fe-95c1-b6f35fc7c8ed

module
public import Definitions.Def_LeanPool_PhaseRetrieval_FourierParseval
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite_Definitions
public import Mathlib.Analysis.Complex.Isometry
public import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
public import Mathlib.MeasureTheory.Integral.Gamma
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermitek_TrueLevelBasis
public import Theorems.Thm_HermitekLEAN_qkn_explicit

set_option autoImplicit true
@[expose] public section
public section
open Complex MeasureTheory Real Finset
open scoped BigOperators Topology
noncomputable section
open HermitekLEAN
namespace HermitekLEAN
theorem _root_.solution :
    ∀ {k n : ℕ} {r : ℝ},
      0 < r →
        qkn k n r =
          (1 / Real.sqrt (Nat.factorial n : ℝ)) *
            Finset.sum (Finset.range (min k n + 1)) (fun j =>
              ((-1 : ℝ) ^ j) * (Nat.choose k j : ℝ) *
                ((Nat.factorial n : ℝ) / (Nat.factorial (n - j) : ℝ)) *
                r ^ ((n : ℤ) - 2 * (j : ℤ))) := by
  intro k n r hr
  exact qkn_explicit (k := k) (n := n) (r := r) hr
end HermitekLEAN
