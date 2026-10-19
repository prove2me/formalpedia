-- Prove2me | solution 2 for OAI.ArnoldCounterexample.Descent.uniform_drop
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T10:03:38.454475+00:00
-- url     : https://prove2.me/submissions/6651af66-c164-40a1-b873-b641f51fdc41

-- Generated from openai/math@1581d4c lean/OAI/Geometry/Arnold/Descent.lean:L107-L144
-- (upload_full_project.md Phase 4): solution for node OAI.ArnoldCounterexample.Descent.uniform_drop. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_ArnoldCounterexample
import Definitions.Def_OAI_Geometry_Arnold_Involution
import Definitions.Def_OAI_Geometry_Arnold_Projective
import Definitions.Def_OAI_Geometry_Arnold_Rotation
import Definitions.Def_OAI_Geometry_Arnold_Tangent
import Definitions.Def_OAI_Geometry_Arnold_Haar
import Definitions.Def_OAI_Geometry_Arnold_Differentiation
import Definitions.Def_OAI_Geometry_Arnold_Orbit
import Definitions.Def_OAI_Geometry_Arnold_Symplectic
import Definitions.Def_OAI_Geometry_Arnold_Coordinates
import Definitions.Def_OAI_Geometry_Arnold_Extension

-- ---- from OAI.Geometry.Arnold.Descent ----
namespace OAI

universe uE uX

noncomputable section
open scoped BigOperators ContDiff
open MeasureTheory Set Filter
open scoped Matrix.Norms.Operator
open scoped Topology

open Set
open scoped ContDiff

namespace ArnoldCounterexample.Descent

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]

end ArnoldCounterexample.Descent

open Set Function

namespace ArnoldCounterexample.Descent

variable {X : Type uX} [TopologicalSpace X] [CompactSpace X]

omit [TopologicalSpace X] [CompactSpace X] in
/-- Values of a Lyapunov function are nonincreasing under iteration. -/
lemma iterate_le {D : X → X} {f : X → ℝ}
    (hdec : ∀ x, f (D x) ≤ f x) (n : ℕ) (x : X) : f (D^[n] x) ≤ f x := by
  induction n with
  | zero => exact le_rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact (hdec _).trans ih

/-- A compact band without stationary points is crossed in a uniform finite
number of iterations. The conclusion is strict, as needed by the level-cover argument. -/
theorem uniform_drop {D : X → X} {f : X → ℝ}
    (hD : Continuous D) (hf : Continuous f)
    (hdec : ∀ x, f (D x) ≤ f x) (a b : ℝ)
    (hstrict : ∀ x, a ≤ f x → f x ≤ b → f (D x) < f x) :
    ∃ N : ℕ, ∀ x, f x ≤ b → f (D^[N] x) < a := by
  let K : Set X := {x | a ≤ f x ∧ f x ≤ b}
  have hK : IsCompact K := (isClosed_le continuous_const hf |>.inter
    (isClosed_le hf continuous_const)).isCompact
  by_cases hne : K.Nonempty
  · obtain ⟨z, hz, hmin⟩ := hK.exists_isMinOn hne (hf.sub (hf.comp hD)).continuousOn
    let δ := f z - f (D z)
    have hδ : 0 < δ := sub_pos.mpr (hstrict z hz.1 hz.2)
    obtain ⟨N, hN⟩ := exists_nat_gt ((b - a) / δ)
    refine ⟨N, fun x hx ↦ ?_⟩
    by_contra hn
    have ha : a ≤ f (D^[N] x) := le_of_not_gt hn
    have hp : ∀ n, a ≤ f (D^[n] x) → f (D^[n] x) ≤ f x - n * δ := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        intro han
        rw [Function.iterate_succ_apply'] at han ⊢
        have hprev : a ≤ f (D^[n] x) := han.trans (hdec _)
        have hbprev : f (D^[n] x) ≤ b := (iterate_le hdec n x).trans hx
        have hgap := hmin (show D^[n] x ∈ K from ⟨hprev, hbprev⟩)
        have hi := ih hprev
        push_cast
        dsimp [δ] at *
        linarith
    have hnum : b - a < N * δ := (div_lt_iff₀ hδ).mp hN
    have hlast := hp N ha
    linarith
  · refine ⟨0, fun x hx ↦ ?_⟩
    by_contra ha
    exact hne ⟨x, le_of_not_gt ha, hx⟩

end ArnoldCounterexample.Descent

end

end OAI

-- ---- platform node ----
open OAI OAI.ArnoldCounterexample OAI.ArnoldCounterexample.Descent
open scoped BigOperators ContDiff
open MeasureTheory Set Filter
open scoped Matrix.Norms.Operator
open scoped Topology
open Set
open scoped ContDiff
open Set Function


theorem solution.{uX} : type_of% @_root_.OAI.ArnoldCounterexample.Descent.uniform_drop.{uX} := @_root_.OAI.ArnoldCounterexample.Descent.uniform_drop.{uX}
