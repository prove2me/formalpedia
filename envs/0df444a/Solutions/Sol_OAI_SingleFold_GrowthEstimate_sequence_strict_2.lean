-- Prove2me | solution 2 for OAI.SingleFold.GrowthEstimate.sequence_strict
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T18:20:36.86998+00:00
-- url     : https://prove2.me/submissions/10cefaf2-3f57-4919-82a0-23c49a733e0a

-- Generated from openai/math@1581d4c lean/OAI/NumberTheory/SingleFold/HeightGrowth.lean:L11-L26
-- (upload_full_project.md Phase 4): solution for node OAI.SingleFold.GrowthEstimate.sequence_strict. The node keeps its source
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

lemma sequence_strict (hW : ∀ j, 0<W j) (hzero : W 0=1) (hc : 0≤c) (ha : 2*c<a)
    (happrox : ∀ j, 1≤j → |Real.log (W j:ℝ)-a*(j:ℝ)^2|≤c) : StrictMono W := by
  apply strictMono_nat_of_lt_succ
  intro n
  have hp (j : ℕ) : (0:ℝ)<W j := by exact_mod_cast hW j
  apply_mod_cast (Real.log_lt_log_iff (hp n) (hp (n+1))).mp (show Real.log (W n:ℝ)<Real.log (W (n+1):ℝ) from ?_)
  have ha' : 0<a := by linarith
  rcases n with _|n
  · have hh := (abs_le.mp (happrox 1 (by omega))).1
    simpa only [hzero,Nat.cast_one,Real.log_one,one_pow,mul_one] using (show (0:ℝ)<Real.log (W 1:ℝ) by
      norm_num at hh
      linarith)
  · have hh := abs_le.mp (happrox (n+1) (by omega))
    have hh' := abs_le.mp (happrox (n+1+1) (by omega))
    push_cast at hh hh'
    nlinarith [show (0:ℝ)≤n by positivity]

end SingleFold.GrowthEstimate

namespace SingleFold.HeightWindow

end SingleFold.HeightWindow

end OAI

-- ---- platform node ----
open OAI OAI.SingleFold OAI.SingleFold.GrowthEstimate
open Filter
open scoped Topology


theorem solution : type_of% @_root_.OAI.SingleFold.GrowthEstimate.sequence_strict := @_root_.OAI.SingleFold.GrowthEstimate.sequence_strict
