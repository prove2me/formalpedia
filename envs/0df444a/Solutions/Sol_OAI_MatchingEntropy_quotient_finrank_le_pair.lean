-- Prove2me | solution 1 for OAI.MatchingEntropy.quotient_finrank_le_pair
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T01:54:58.383826+00:00
-- url     : https://prove2.me/submissions/dc4baea5-f97c-4989-a0c0-11a9a06efa07

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/PerfectMatching/Polyhedron.lean:L98-L113
-- (upload_full_project.md Phase 4): solution for node OAI.MatchingEntropy.quotient_finrank_le_pair. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` restates it and is proved by it.
import Mathlib
import Definitions.Def_MatchingEntropy
import Definitions.Def_OAI_Combinatorics_PerfectMatching_Model
import Definitions.Def_OAI_Combinatorics_PerfectMatching_Basic
import Definitions.Def_OAI_Combinatorics_PerfectMatching_Duality
import Definitions.Def_OAI_Combinatorics_PerfectMatching_Calculus
import Definitions.Def_OAI_Combinatorics_PerfectMatching_SecondVariation
import Definitions.Def_OAI_Combinatorics_PerfectMatching_OddCuts
import Definitions.Def_OAI_Combinatorics_PerfectMatching_Coupling
import Definitions.Def_OAI_Combinatorics_PerfectMatching_Contraction

-- ---- from OAI.Combinatorics.PerfectMatching.Polyhedron ----
namespace OAI

/-!
Finite polyhedra, local perturbations, and quotient dimension bounds.
-/

noncomputable section

open scoped BigOperators Topology
open Filter

namespace MatchingEntropy

section PolyhedralPrelude
variable {I J : Type*} [Fintype I] [Fintype J]

section LinearHelper
open Module
variable {A B C : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
  [Module ℝ A] [Module ℝ B] [Module ℝ C]
  [FiniteDimensional ℝ A] [FiniteDimensional ℝ B] [FiniteDimensional ℝ C]

theorem quotient_finrank_le_of_ker_le (U : Submodule ℝ A) (f : A →ₗ[ℝ] B)
    (h : f.ker ≤ U) : finrank ℝ (A ⧸ U) ≤ finrank ℝ B := by
  have h1 := U.finrank_quotient_add_finrank
  have h2 := f.finrank_range_add_finrank_ker
  have h3 := Submodule.finrank_mono h
  have h4 : finrank ℝ f.range ≤ finrank ℝ B := Submodule.finrank_le _
  omega

theorem quotient_finrank_le_pair (U : Submodule ℝ A) (W : Submodule ℝ B) (Z : Submodule ℝ C)
    (f : A →ₗ[ℝ] B) (g : A →ₗ[ℝ] C)
    (h : ∀ u, f u ∈ W → g u ∈ Z → u ∈ U) :
    finrank ℝ (A ⧸ U) ≤ finrank ℝ (B ⧸ W)+finrank ℝ (C ⧸ Z) := by
  let F := (W.mkQ.comp f).prod (Z.mkQ.comp g)
  have hk : F.ker ≤ U := by
    intro u hu
    have hh : (W.mkQ (f u), Z.mkQ (g u))=0 := hu
    have hW : f u ∈ W := by
      have hq := congrArg Prod.fst hh
      simpa using hq
    have hZ : g u ∈ Z := by
      have hq := congrArg Prod.snd hh
      simpa using hq
    exact h u hW hZ
  simpa using quotient_finrank_le_of_ker_le U F hk

end LinearHelper
end PolyhedralPrelude

end MatchingEntropy

end

end OAI

-- ---- platform node ----
open OAI OAI.MatchingEntropy
open scoped BigOperators Topology
open Filter
variable {I J : Type*} [Fintype I] [Fintype J]
open Module
variable {A B C : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
  [Module ℝ A] [Module ℝ B] [Module ℝ C]
  [FiniteDimensional ℝ A] [FiniteDimensional ℝ B] [FiniteDimensional ℝ C]

theorem solution (U : Submodule ℝ A) (W : Submodule ℝ B) (Z : Submodule ℝ C)
    (f : A →ₗ[ℝ] B) (g : A →ₗ[ℝ] C)
    (h : ∀ u, f u ∈ W → g u ∈ Z → u ∈ U) :
    finrank ℝ (A ⧸ U) ≤ finrank ℝ (B ⧸ W)+finrank ℝ (C ⧸ Z) := by
  first
    | exact OAI.MatchingEntropy.quotient_finrank_le_pair U W Z f g h
    | exact OAI.MatchingEntropy.quotient_finrank_le_pair
    | (apply OAI.MatchingEntropy.quotient_finrank_le_pair <;> assumption)
    | (intros; apply OAI.MatchingEntropy.quotient_finrank_le_pair <;> assumption)
