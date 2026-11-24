-- Prove2me | solution 1 for HermitekLEAN.phi_explicit
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:00:15.282269+00:00
-- url     : https://prove2.me/submissions/2422abee-d02b-4215-8f8e-41c1fc3cc594

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
    ∀ {k n : ℕ} {z : ℂ},
      Phi k n z =
        ((1 / Real.sqrt ((Nat.factorial k : ℝ) * (Nat.factorial n : ℝ))) : ℂ) *
          Finset.sum (Finset.range (min k n + 1)) (fun j =>
            ((-1 : ℂ) ^ j) * (Nat.choose k j : ℂ) *
              ((Nat.factorial n : ℂ) / (Nat.factorial (n - j) : ℂ)) *
              z ^ (n - j) * (star z) ^ (k - j)) := by
  intro k n z
  rfl
end HermitekLEAN
