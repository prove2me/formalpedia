-- Prove2me | solution 2 for OAI.KervaireRibbon.suppress_involutive
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T19:22:31.09157+00:00
-- url     : https://prove2.me/submissions/c15598b8-3341-4ca9-acab-20e7abe1124b

-- Generated from openai/math@1581d4c lean/OAI/GroupTheory/Kervaire/Suppression.lean:L197-L214
-- (upload_full_project.md Phase 4): solution for node OAI.KervaireRibbon.suppress_involutive. The node keeps its source
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

omit [Fintype D] in
lemma suppress_apply (θ : Equiv.Perm D) (hθ : ∀ d, θ (θ d) = d)
    {x y : D} (hxy : x ≠ y) (hx : θ x ≠ x) (hxy' : θ x ≠ y) (hy : θ y ≠ y) :
    suppress θ x y x = x ∧ suppress θ x y y = y ∧
    suppress θ x y (θ x) = θ y ∧ suppress θ x y (θ y) = θ x := by
  have hyx : θ y ≠ x := fun he ↦ hxy' (by simpa only [hθ] using (congrArg θ he).symm)
  have hpq : θ x ≠ θ y := fun he ↦ hxy (θ.injective he)
  simp only [suppress,mul_apply,swap_apply_of_ne_of_ne hxy hx.symm,
    swap_apply_left,swap_apply_right,hθ,swap_apply_of_ne_of_ne hy hpq.symm,
    swap_apply_of_ne_of_ne hyx hy,swap_apply_of_ne_of_ne hx hxy',true_and]

omit [Fintype D] in
lemma suppress_other (θ : Equiv.Perm D) (hθ : ∀ d, θ (θ d) = d)
    {x y d : D} (hdx : d ≠ x) (hdy : d ≠ y) (hdp : d ≠ θ x) (hdq : d ≠ θ y) :
    suppress θ x y d = θ d := by
  have htx : θ d ≠ x := fun h ↦ hdp (by simpa only [hθ] using congrArg θ h)
  have hty : θ d ≠ y := fun h ↦ hdq (by simpa only [hθ] using congrArg θ h)
  have htp : θ d ≠ θ x := fun h ↦ hdx (θ.injective h)
  simp only [suppress,mul_apply,swap_apply_of_ne_of_ne hdy hdp,
    swap_apply_of_ne_of_ne hty htp,swap_apply_of_ne_of_ne htx hty]

omit [Fintype D] in
lemma suppress_involutive (θ : Equiv.Perm D) (hθ : ∀ d, θ (θ d) = d)
    {x y : D} (hxy : x ≠ y) (hx : θ x ≠ x) (hxy' : θ x ≠ y) (hy : θ y ≠ y) :
    ∀ d, suppress θ x y (suppress θ x y d) = d := by
  have hh := suppress_apply θ hθ hxy hx hxy' hy
  intro d
  by_cases hdx : d = x
  · subst d; rw [hh.1,hh.1]
  by_cases hdy : d = y
  · subst d; rw [hh.2.1,hh.2.1]
  by_cases hdp : d = θ x
  · subst d; rw [hh.2.2.1,hh.2.2.2]
  by_cases hdq : d = θ y
  · subst d; rw [hh.2.2.2,hh.2.2.1]
  rw [suppress_other θ hθ hdx hdy hdp hdq]
  have htx : θ d ≠ x := fun h ↦ hdp (by simpa only [hθ] using (congrArg θ h))
  have hty : θ d ≠ y := fun h ↦ hdq (by simpa only [hθ] using (congrArg θ h))
  rw [suppress_other θ hθ htx hty (fun h ↦ hdx (θ.injective h)) (fun h ↦ hdy (θ.injective h)),hθ]

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


theorem solution : type_of% @_root_.OAI.KervaireRibbon.suppress_involutive := @_root_.OAI.KervaireRibbon.suppress_involutive
