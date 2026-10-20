-- Prove2me | solution 2 for OAI.SingleFold.GrowthEstimate.bracket_unique
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T18:22:13.996662+00:00
-- url     : https://prove2.me/submissions/5b80478d-ffbe-4a69-8798-3f0eb55e3af8

-- Generated from openai/math@1581d4c lean/OAI/NumberTheory/SingleFold/HeightGrowth.lean:L41-L64
-- (upload_full_project.md Phase 4): solution for node OAI.SingleFold.GrowthEstimate.bracket_unique. The node keeps its source
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

lemma bracket_unique (hW : StrictMono W) (hunb : ∀ U, ∃ j, U<W j) (u : ℕ) :
    ∃! k : ℕ, 1≤k ∧ W k≤u+W 1 ∧ u+W 1<W (k+1) := by
  let j := Nat.find (hunb (u+W 1))
  have hj : u+W 1<W j := Nat.find_spec (hunb (u+W 1))
  have hj2 : 2≤j := by
    by_contra hn
    have hj1 : j≤1 := by omega
    have hh := hW.monotone hj1
    omega
  have hprev : W (j-1)≤u+W 1 := by
    by_contra h
    have : j≤j-1 := Nat.find_min' (hunb (u+W 1)) (m:=j-1) (by omega)
    omega
  refine ⟨j-1,⟨by omega,hprev,by simpa only [show j-1+1=j by omega] using hj⟩,?_⟩
  rintro k ⟨_,hk,hk'⟩
  apply le_antisymm
  · by_contra hn
    have hjk : j≤k := by omega
    have hh := hW.monotone hjk
    omega
  · by_contra hn
    have hkj : k+1≤j-1 := by omega
    have hh := hW.monotone hkj
    omega

end SingleFold.GrowthEstimate

namespace SingleFold.HeightWindow

end SingleFold.HeightWindow

end OAI

-- ---- platform node ----
open OAI OAI.SingleFold OAI.SingleFold.GrowthEstimate
open Filter
open scoped Topology


theorem solution : type_of% @_root_.OAI.SingleFold.GrowthEstimate.bracket_unique := @_root_.OAI.SingleFold.GrowthEstimate.bracket_unique
