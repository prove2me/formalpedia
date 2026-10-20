-- Prove2me | solution 2 for OAI.SingleFold.GrowthEstimate.bracket_log
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T18:23:39.253804+00:00
-- url     : https://prove2.me/submissions/b7e257de-6f89-4b65-a19e-7dd42815dd41

-- Generated from openai/math@1581d4c lean/OAI/NumberTheory/SingleFold/HeightGrowth.lean:L66-L82
-- (upload_full_project.md Phase 4): solution for node OAI.SingleFold.GrowthEstimate.bracket_log. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
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

-- ---- from OAI.NumberTheory.SingleFold.HeightGrowth ----
namespace OAI

namespace SingleFold.GrowthEstimate
open Filter
open scoped Topology

variable {W : ℕ → ℕ} {a c : ℝ}

lemma bracket_log {u k : ℕ} (hW : ∀ j, 0<W j) (ha : 0<a)
    (happrox : ∀ j, 1≤j → |Real.log (W j:ℝ)-a*(j:ℝ)^2|≤c)
    (hk : 1≤k) (hb : W k≤u+W 1 ∧ u+W 1<W (k+1)) :
      a*(k:ℝ)^2-c ≤ Real.log (u+W 1:ℕ) ∧
      Real.log (u+W 1:ℕ) < 4*a*(k:ℝ)^2+c := by
  have hp : (0:ℝ)<W k := by exact_mod_cast hW k
  have hU : (0:ℝ)<(u+W 1:ℕ) := by exact_mod_cast (show 0<u+W 1 by have := hW 1; omega)
  have hlo : Real.log (W k:ℝ)≤Real.log (u+W 1:ℕ) := Real.log_le_log hp (by exact_mod_cast hb.1)
  have hhi : Real.log (u+W 1:ℕ)<Real.log (W (k+1):ℝ) := Real.log_lt_log hU (by exact_mod_cast hb.2)
  have ha₁ := abs_le.mp (happrox k hk)
  have ha₂ := abs_le.mp (happrox (k+1) (by omega))
  have hk' : (1:ℝ)≤k := by exact_mod_cast hk
  constructor
  · linarith
  · have : ((k:ℝ)+1)^2≤4*(k:ℝ)^2 := by nlinarith
    push_cast at ha₂
    nlinarith [mul_le_mul_of_nonneg_left this ha.le]

end SingleFold.GrowthEstimate

namespace SingleFold.HeightWindow

end SingleFold.HeightWindow

end OAI

-- ---- platform node ----
open OAI OAI.SingleFold OAI.SingleFold.GrowthEstimate
open Filter
open scoped Topology


theorem solution : type_of% @_root_.OAI.SingleFold.GrowthEstimate.bracket_log := @_root_.OAI.SingleFold.GrowthEstimate.bracket_log
