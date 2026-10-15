-- Prove2me | solution 1 for OAI.MatchingEntropy.extreme_point_direction_zero
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T01:53:27.038984+00:00
-- url     : https://prove2.me/submissions/c85c7eca-1f92-489f-8c36-b9e852163788

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/PerfectMatching/Polyhedron.lean:L60-L81
-- (upload_full_project.md Phase 4): solution for node OAI.MatchingEntropy.extreme_point_direction_zero. The node keeps its source
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

omit [Fintype J] in
theorem extreme_point_direction_zero (P : Set (J → ℝ)) {x : J → ℝ}
    (hx : x ∈ Set.extremePoints ℝ P) (u : J → ℝ)
    (hu : ∀ᶠ t : ℝ in 𝓝 0, x+t • u ∈ P) : u=0 := by
  have hu' : ∀ᶠ t : ℝ in 𝓝 0, x+(-t) • u ∈ P := by
    have hc : Tendsto (fun t : ℝ => -t) (𝓝 0) (𝓝 0) := by simpa using (continuous_neg.tendsto (0:ℝ))
    exact hc.eventually hu
  -- choose a strictly positive point using the right-hand punctured neighborhood
  have hh : ∀ᶠ t : ℝ in 𝓝[>] 0, (x+t • u ∈ P ∧ x+(-t) • u ∈ P) ∧ 0<t :=
    ((hu.and hu').filter_mono nhdsWithin_le_nhds).and eventually_mem_nhdsWithin
  obtain ⟨a,⟨ha,hna⟩,ha0⟩ := hh.exists
  have hseg : x ∈ openSegment ℝ (x+a • u) (x+(-a) • u) := by
    refine ⟨1/2,1/2,by norm_num,by norm_num,by norm_num,?_⟩
    ext j
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have he := (mem_extremePoints.mp hx).2 _ ha _ hna hseg |>.1
  ext j
  have hj := congrFun he j
  change x j+a*u j=x j at hj
  change u j=0
  exact (mul_eq_zero.mp (by linarith : a*u j=0)).resolve_left (ne_of_gt ha0)

section LinearHelper
open Module
variable {A B C : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
  [Module ℝ A] [Module ℝ B] [Module ℝ C]
  [FiniteDimensional ℝ A] [FiniteDimensional ℝ B] [FiniteDimensional ℝ C]

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

omit [Fintype J] in
theorem solution (P : Set (J → ℝ)) {x : J → ℝ}
    (hx : x ∈ Set.extremePoints ℝ P) (u : J → ℝ)
    (hu : ∀ᶠ t : ℝ in 𝓝 0, x+t • u ∈ P) : u=0 := by
  first
    | exact OAI.MatchingEntropy.extreme_point_direction_zero P hx u hu
    | exact OAI.MatchingEntropy.extreme_point_direction_zero
    | (apply OAI.MatchingEntropy.extreme_point_direction_zero <;> assumption)
    | (intros; apply OAI.MatchingEntropy.extreme_point_direction_zero <;> assumption)
