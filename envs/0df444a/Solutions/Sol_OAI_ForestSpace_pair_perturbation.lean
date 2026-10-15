-- Prove2me | solution 1 for OAI.ForestSpace.pair_perturbation
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T04:59:08.3097+00:00
-- url     : https://prove2.me/submissions/e7ad15c5-7a20-4ee2-a316-7b8d920dd8a6

-- Generated from openai/math@1581d4c lean/OAI/Analysis/ForestSpace/ModulusProofs.lean:L107-L127
-- (upload_full_project.md Phase 4): solution for node OAI.ForestSpace.pair_perturbation. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_ForestSpace
import Definitions.Def_OAI_Analysis_ForestSpace_Moduli
import Definitions.Def_OAI_Analysis_ForestSpace_Segments
import Definitions.Def_OAI_Analysis_ForestSpace_FiniteGeometry
import Definitions.Def_OAI_Analysis_ForestSpace_Paired
import Definitions.Def_OAI_Analysis_ForestSpace_Norm
import Definitions.Def_OAI_Analysis_ForestSpace_Completion
import Definitions.Def_OAI_Analysis_ForestSpace_Polar
import Definitions.Def_OAI_Analysis_ForestSpace_Projections

-- ---- from OAI.Analysis.ForestSpace.ModulusProofs ----
namespace OAI

open scoped BigOperators
open Finset

namespace ForestSpace

noncomputable section
attribute [local instance] Classical.propDecidable

section ModulusDefinitions

variable (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]

variable {E}

end ModulusDefinitions

section ForestModulus
variable {V : Type} [PartialOrder V]

 theorem sqrt_perturbation {a b δ : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hδ : 0 ≤ δ)
    (h1 : 1 ≤ a+δ) : Real.sqrt (1+b) ≤ Real.sqrt (a^2+b)+δ := by
  have hs := Real.sq_sqrt (show 0 ≤ a^2+b by positivity)
  have has : a ≤ Real.sqrt (a^2+b) := (Real.le_sqrt ha (show 0 ≤ a^2+b by positivity)).mpr (by linarith)
  apply Real.sqrt_le_iff.mpr
  constructor
  · positivity
  · nlinarith [mul_nonneg hδ (sub_nonneg.mpr has), sq_nonneg (a+δ-1)]

theorem pair_perturbation {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (x a y : E) (b : ℝ) (hb : 0 ≤ b) (hx : ‖x‖ = 1)
    (hpair : Real.sqrt (‖a‖^2+b) ≤ (‖a+y‖+‖a-y‖)/2) :
    Real.sqrt (1+b) ≤ (‖x+y‖+‖x-y‖)/2+2*‖x-a‖ := by
  let δ : ℝ := ‖x-a‖
  have hc : 1 ≤ ‖a‖+δ := by
    have hh := norm_add_le a (x-a)
    have he : a+(x-a) = x := by abel
    rw [he, hx] at hh
    exact hh
  have hroot := sqrt_perturbation (norm_nonneg a) hb (norm_nonneg (x-a)) hc
  have hp : ‖a+y‖ ≤ ‖x+y‖+δ := by
    have hh := norm_sub_le (x+y) (x-a)
    have he : x+y-(x-a) = a+y := by abel
    rwa [he] at hh
  have hm : ‖a-y‖ ≤ ‖x-y‖+δ := by
    have hh := norm_sub_le (x-y) (x-a)
    have he : x-y-(x-a) = a-y := by abel
    rwa [he] at hh
  change Real.sqrt (1+b) ≤ (‖x+y‖+‖x-y‖)/2+2*δ
  linarith

end ForestModulus

end

end ForestSpace

end OAI

-- ---- platform node ----
open OAI OAI.ForestSpace
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable


theorem solution : type_of% @_root_.OAI.ForestSpace.pair_perturbation := @_root_.OAI.ForestSpace.pair_perturbation
