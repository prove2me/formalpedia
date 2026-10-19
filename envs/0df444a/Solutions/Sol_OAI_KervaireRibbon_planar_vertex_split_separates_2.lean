-- Prove2me | solution 2 for OAI.KervaireRibbon.planar_vertex_split_separates
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T19:20:34.877738+00:00
-- url     : https://prove2.me/submissions/530786cc-bf31-4e4f-95b4-f0a0ca7e1bbe

-- Generated from openai/math@1581d4c lean/OAI/GroupTheory/Kervaire/Suppression.lean:L156-L170
-- (upload_full_project.md Phase 4): solution for node OAI.KervaireRibbon.planar_vertex_split_separates. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_Kervaire
import Definitions.Def_OAI_GroupTheory_Kervaire_Reductions
import Definitions.Def_OAI_GroupTheory_Kervaire_PermutationCycles
import Definitions.Def_OAI_GroupTheory_Kervaire_Components
import Definitions.Def_OAI_GroupTheory_Kervaire_Suppression

-- ---- from OAI.GroupTheory.Kervaire.Suppression ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section

namespace KervaireRibbon

section
open Equiv Equiv.Perm
open scoped Classical
variable {D : Type*} [Fintype D] [DecidableEq D]

end
section
open Equiv Equiv.Perm
open scoped Classical
variable {D : Type*} [Fintype D] [DecidableEq D]

lemma planar_vertex_split_separates (σ θ : Equiv.Perm D) {x y : D} (hne : x ≠ y)
    (hxy : σ.SameCycle x y) (hφ : (σ*θ).SameCycle x y) (hp : planar σ θ) :
    ¬ components (swap x y * σ) θ x y := by
  intro hc
  have hr : components (swap x y * σ) θ = components σ θ := by
    have hh := components_swap_sup σ θ x y
    rw [joinPair_eq _ hc] at hh
    have he := joinPair_eq (components σ θ) ((le_sup_left : SameCycle.setoid σ ≤ components σ θ) hxy)
    exact hh.trans he
  have hv := numCycles_swap_split σ hne hxy
  have hf := numCycles_swap_split (σ*θ) hne hφ
  have he := planar_vertex_split σ θ hne hxy hp
  unfold planar at he hp
  rw [mul_assoc,hv,hf,hr] at he
  omega

end
open Equiv Equiv.Perm
open scoped Classical
variable {D : Type*} [Fintype D] [DecidableEq D]

end KervaireRibbon

end

end OAI

-- ---- platform node ----
open OAI OAI.KervaireRibbon
open Equiv Equiv.Perm
open scoped Classical


theorem solution : type_of% @_root_.OAI.KervaireRibbon.planar_vertex_split_separates := @_root_.OAI.KervaireRibbon.planar_vertex_split_separates
