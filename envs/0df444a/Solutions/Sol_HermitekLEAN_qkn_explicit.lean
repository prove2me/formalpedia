-- Prove2me | solution 1 for HermitekLEAN.qkn_explicit
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:06:09.67039+00:00
-- url     : https://prove2.me/submissions/7dc672f7-ed1d-432a-bab4-798f3f523c60

module
public import Definitions.Def_LeanPool_PhaseRetrieval_FourierParseval
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite_Definitions
public import Mathlib.Analysis.Complex.Isometry
public import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
public import Mathlib.MeasureTheory.Integral.Gamma
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermitek_TrueLevelBasis

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
  rfl
end HermitekLEAN
