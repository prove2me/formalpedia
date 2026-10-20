-- Prove2me | solution 1 for OAI.SingleFold.GrowthEstimate.bracket_log
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T18:22:35.315247+00:00
-- url     : https://prove2.me/submissions/09f0c183-7397-4cb5-86df-6370daf640c6

import Mathlib
import Definitions.Def_SingleFold
import Definitions.Def_OAI_NumberTheory_SingleFold_PolynomialCompiler
import Definitions.Def_OAI_NumberTheory_SingleFold_RationalCodes
import Definitions.Def_OAI_NumberTheory_SingleFold_EllipticCoordinates
import Definitions.Def_OAI_NumberTheory_SingleFold_FunctionalCompiler
import Definitions.Def_OAI_NumberTheory_SingleFold_DescentMap
import Definitions.Def_OAI_NumberTheory_SingleFold_SquareSupport
import Definitions.Def_OAI_NumberTheory_SingleFold_LocalDescent
import Definitions.Def_OAI_NumberTheory_SingleFold_EllipticHeight
import Definitions.Def_OAI_NumberTheory_SingleFold_QuadraticHeight
import Definitions.Def_OAI_NumberTheory_SingleFold_FiniteGeneration
import Definitions.Def_OAI_NumberTheory_SingleFold_Rank
import Definitions.Def_OAI_NumberTheory_SingleFold_Duplication
import Definitions.Def_OAI_NumberTheory_SingleFold_Torsion

open OAI OAI.SingleFold
open Filter
open scoped Topology
variable {W : ℕ → ℕ} {a c : ℝ}


theorem solution {u k : ℕ} (hW : ∀ j, 0<W j) (ha : 0<a)
    (happrox : ∀ j, 1≤j → |Real.log (W j:ℝ)-a*(j:ℝ)^2|≤c)
    (hk : 1≤k) (hb : W k≤u+W 1 ∧ u+W 1<W (k+1)) :
      a*(k:ℝ)^2-c ≤ Real.log (u+W 1:ℕ) ∧
      Real.log (u+W 1:ℕ) < 4*a*(k:ℝ)^2+c := by
  have h1 := happrox k hk
  have h2 := happrox (k+1) (by omega)
  rw [abs_le] at h1 h2
  have hWk : (0:ℝ) < W k := by exact_mod_cast hW k
  have hle : (W k : ℝ) ≤ ((u + W 1 : ℕ) : ℝ) := by exact_mod_cast hb.1
  have hlt : ((u + W 1 : ℕ) : ℝ) < (W (k+1) : ℝ) := by exact_mod_cast hb.2
  have l1 := Real.log_le_log hWk hle
  have l2 := Real.log_lt_log (lt_of_lt_of_le hWk hle) hlt
  have hk1 : (1:ℝ) ≤ k := by exact_mod_cast hk
  have hsq : ((k:ℝ)+1)^2 ≤ 4*(k:ℝ)^2 := by nlinarith
  push_cast at h2
  constructor
  · linarith
  · nlinarith

