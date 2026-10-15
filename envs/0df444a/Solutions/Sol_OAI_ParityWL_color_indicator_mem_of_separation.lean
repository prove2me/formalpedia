-- Prove2me | solution 1 for OAI.ParityWL.color_indicator_mem_of_separation
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T05:37:48.926009+00:00
-- url     : https://prove2.me/submissions/6a30b3de-ea48-448c-9be7-304466000eb8

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/ParityLifts/Interpolation.lean:L17-L51
-- (upload_full_project.md Phase 4): solution for node OAI.ParityWL.color_indicator_mem_of_separation. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_ParityLifts
import Definitions.Def_OAI_Combinatorics_ParityLifts_LiftCounts
import Definitions.Def_OAI_Combinatorics_ParityLifts_WeightedDual
import Definitions.Def_OAI_Combinatorics_ParityLifts_Masses
import Definitions.Def_OAI_Combinatorics_ParityLifts_BaseLabels
import Definitions.Def_OAI_Combinatorics_ParityLifts_BalancedBags
import Definitions.Def_OAI_Combinatorics_ParityLifts_DecompositionCuts
import Definitions.Def_OAI_Combinatorics_ParityLifts_Witnesses
import Definitions.Def_OAI_Combinatorics_ParityLifts_BagTrees
import Definitions.Def_OAI_Combinatorics_ParityLifts_TagSizes
import Definitions.Def_OAI_Combinatorics_ParityLifts_Detection
import Definitions.Def_OAI_Combinatorics_ParityLifts_RankedTrees
import Definitions.Def_OAI_Combinatorics_ParityLifts_RootedTests
import Definitions.Def_OAI_Combinatorics_ParityLifts_GlueTrees
import Definitions.Def_OAI_Combinatorics_ParityLifts_GlueVertices
import Definitions.Def_OAI_Combinatorics_ParityLifts_Rerooting
import Definitions.Def_OAI_Combinatorics_ParityLifts_TestAlgebra
import Definitions.Def_OAI_Combinatorics_ParityLifts_Interpolation

-- ---- from OAI.Combinatorics.ParityLifts.Interpolation ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

namespace OAI

namespace ParityWL

open scoped BigOperators

section FiniteInterpolation

open scoped Classical

lemma color_indicator_mem_of_separation {X D : Type} [Fintype X] [DecidableEq D]
    (A : Subalgebra ℚ (X → ℚ)) (c : X → D)
    (hsep : ∀ x y, c x ≠ c y → ∃ f ∈ A,
      (∀ z w, c z = c w → f z = f w) ∧ f x ≠ f y) (d : D) :
    (fun x => if c x = d then (1 : ℚ) else 0) ∈ A := by
  by_cases hex : ∃ x, c x = d
  · obtain ⟨x₀, hx₀⟩ := hex
    let Y := {y : X // c x₀ ≠ c y}
    choose f hf hinv hne using (fun y : Y => hsep x₀ y.1 y.2)
    let p : X → ℚ := ∏ y : Y, (f y x₀ - f y y.1)⁻¹ • (f y - (f y y.1) • 1)
    have hp : p ∈ A := A.prod_mem (fun y _ =>
      A.smul_mem (A.sub_mem (hf y) (A.smul_mem A.one_mem (f y y.1))) _)
    have he : p = fun x => if c x = d then (1 : ℚ) else 0 := by
      funext x
      dsimp only [p]
      rw [Finset.prod_apply]
      by_cases hx : c x = d
      · rw [ite_eq_left hx]
        apply Finset.prod_eq_one
        intro y _
        simp only [Pi.smul_apply, Pi.sub_apply, Pi.one_apply, smul_eq_mul, mul_one]
        rw [hinv y x x₀ (hx.trans hx₀.symm)]
        exact inv_mul_cancel₀ (sub_ne_zero.mpr (hne y))
      · rw [ite_eq_right hx]
        let y : Y := ⟨x, fun he => hx (he.symm.trans hx₀)⟩
        apply Finset.prod_eq_zero (Finset.mem_univ y)
        simp only [Pi.smul_apply, Pi.sub_apply, Pi.one_apply, smul_eq_mul, mul_one]
        change _ * (f y x - f y x) = 0
        rw [sub_self, mul_zero]
    rwa [he] at hp
  · have he : (fun x => if c x = d then (1 : ℚ) else 0) = 0 := by
      funext x
      exact ite_eq_right (fun h => hex ⟨x, h⟩)
    rw [he]
    exact A.zero_mem

end FiniteInterpolation

section RefinementOperators

open scoped Classical

variable {V W : Type} [Fintype V] [Fintype W]
variable (G : SimpleGraph V) (H : SimpleGraph W)

end RefinementOperators

end ParityWL

end OAI

-- ---- platform node ----
open OAI OAI.ParityWL
open scoped BigOperators
open scoped Classical


theorem solution : type_of% @_root_.OAI.ParityWL.color_indicator_mem_of_separation := @_root_.OAI.ParityWL.color_indicator_mem_of_separation
