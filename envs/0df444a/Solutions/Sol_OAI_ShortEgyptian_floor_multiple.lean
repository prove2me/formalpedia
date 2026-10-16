-- Prove2me | solution 1 for OAI.ShortEgyptian.floor_multiple
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T04:10:35.891746+00:00
-- url     : https://prove2.me/submissions/22fdf186-5a71-4454-b17e-cd695eb7a2c0

-- Generated from openai/math@1581d4c lean/OAI/NumberTheory/ShortEgyptian/DenseSplit.lean:L50-L63
-- (upload_full_project.md Phase 4): solution for node OAI.ShortEgyptian.floor_multiple. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_ShortEgyptianFractions
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_Basic
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_FirstDerivative
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_ReciprocalDifferences
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_IntervalDifferencing
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_IteratedDifferencing
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_ParameterBounds
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_FourierDiscrepancy
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_WindowSpectrum
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_WindowDiscrepancy
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_EmpiricalDiscrepancy
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_DivisorWeights
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_TruncatedDivisors
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_SmoothBounds
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_DivisorMoments
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_PrimeLists
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_PrimeProducts
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_HammingDistance
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_SamplePartitions
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_ProductCorrelations
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_ListSelection
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_LevelSelection
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_ListConstruction
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_ScaleGeometry
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_ScaleBounds
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_ResidueSystem
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_TerminalScale
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_DescentSets
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_MomentRecurrence
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_Density
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_GreedyPreparation

-- ---- from OAI.NumberTheory.ShortEgyptian.DenseSplit ----
namespace OAI

namespace ShortEgyptian

attribute [local instance] scaleFinDecidableEq

open scoped BigOperators
open Finset Classical

lemma floor_multiple (X : ℝ) (P : ℕ) (hP : 0<P) (hPX : (P:ℝ)≤X) :
    let g := ⌊X/(P:ℝ)⌋₊
    0<g ∧ X/2 ≤ ((g*P:ℕ):ℝ) ∧ ((g*P:ℕ):ℝ)≤X := by
  dsimp
  have hPR : (0:ℝ)<P := by exact_mod_cast hP
  have hx : 1≤X/(P:ℝ) := (le_div_iff₀ hPR).mpr (by simpa using hPX)
  have hg : 0<⌊X/(P:ℝ)⌋₊ := Nat.floor_pos.mpr hx
  have hgR : (1:ℝ) ≤ ⌊X/(P:ℝ)⌋₊ := by exact_mod_cast hg
  have hi := Nat.lt_floor_add_one (X/(P:ℝ))
  have hlo : X/(P:ℝ) ≤ 2*(⌊X/(P:ℝ)⌋₊:ℝ) := by linarith
  have hhi := Nat.floor_le (show 0≤X/(P:ℝ) by linarith)
  have hlo' := (div_le_iff₀ hPR).mp hlo
  have hhi' := (le_div_iff₀ hPR).mp hhi
  refine ⟨hg,?_,?_⟩ <;> push_cast <;> nlinarith

end ShortEgyptian

end OAI

-- ---- platform node ----
open OAI OAI.ShortEgyptian
attribute [local instance] scaleFinDecidableEq
open scoped BigOperators
open Finset Classical


theorem solution : type_of% @_root_.OAI.ShortEgyptian.floor_multiple := @_root_.OAI.ShortEgyptian.floor_multiple
