-- Prove2me | solution 1 for HermiteLEAN.annulus_distance_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:51:33.703807+00:00
-- url     : https://prove2.me/submissions/85d9ffa4-8a85-412c-9d45-530e8974157d

module
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite_Definitions
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite_MissingMathlib

set_option autoImplicit true
@[expose] public section
public section
open Complex MeasureTheory Real Finset Filter
open scoped BigOperators ComplexConjugate Topology
noncomputable section
open HermiteLEAN
namespace HermiteLEAN
theorem _root_.solution (j : ℕ) (x : ℝ) :
    posPart (|((j : ℕ) : ℝ) - x| - 1)
      ≤ min |((j : ℕ) : ℝ) - x| |(((j + 1 : ℕ) : ℝ) - x)| := by
  dsimp [posPart]
  set a : ℝ := |((j : ℕ) : ℝ) - x|
  set b : ℝ := |(((j + 1 : ℕ) : ℝ) - x)|
  have ha0 : 0 ≤ a := by simp [a]
  have hb0 : 0 ≤ b := by simp [b]
  have habs : |a - b| ≤ 1 := by
    have h := abs_abs_sub_abs_le_abs_sub ((j : ℝ) - x) ((((j + 1 : ℕ) : ℝ) - x))
    have hrhs : |((j : ℝ) - x) - ((((j + 1 : ℕ) : ℝ) - x))| = 1 := by
      simp_all
    simpa [a, b, hrhs] using h
  rw [le_min_iff]
  refine ⟨max_le (by linarith only []) ha0, max_le ?_ hb0⟩
  linarith only [habs, (abs_sub_le_iff.mp habs).1]
end HermiteLEAN
