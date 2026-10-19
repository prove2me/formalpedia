-- Prove2me | solution 2 for OAI.KervaireRibbon.components_suppress
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T19:23:58.631587+00:00
-- url     : https://prove2.me/submissions/24fbe5e6-9f3d-479f-8dbe-3dcf5c9e96b3

-- Generated from openai/math@1581d4c lean/OAI/GroupTheory/Kervaire/Suppression.lean:L263-L292
-- (upload_full_project.md Phase 4): solution for node OAI.KervaireRibbon.components_suppress. The node keeps its source
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

end
open Equiv Equiv.Perm
open scoped Classical
variable {D : Type*} [Fintype D] [DecidableEq D]

lemma components_suppress (σ θ : Equiv.Perm D) {x y : D} (hsx : σ x = y) :
    joinPair (joinPair (components (swap x y * σ) (suppress θ x y)) x (θ x)) y (θ x) =
      components σ θ := by
  let r := components σ θ
  let r' := components (swap x y * σ) (suppress θ x y)
  let R := joinPair (joinPair r' x (θ x)) y (θ x)
  have hrxy : r x y := (le_sup_left : SameCycle.setoid σ ≤ r) (hsx ▸ SameCycle.rfl.apply_right)
  have hrxp : r x (θ x) := (le_sup_right : SameCycle.setoid θ ≤ r) SameCycle.rfl.apply_right
  have ha : SameCycle.setoid (swap x y) ≤ r := cycle_swap_le r x y hrxy
  have hb : SameCycle.setoid (swap y (θ x)) ≤ r := cycle_swap_le r y (θ x) (r.trans' (r.symm' hrxy) hrxp)
  have hr' : r' ≤ r := by
    apply sup_le
    · exact cycles_mul_le _ _ r ha le_sup_left
    · exact cycles_mul_le _ _ r ha (cycles_mul_le _ _ r (cycles_mul_le _ _ r hb le_sup_right) hb)
  have hRr : R ≤ r := sup_le (sup_le hr' (cycle_swap_le r x (θ x) hrxp)) hb
  have hr'R : r' ≤ R := (le_joinPair r' x (θ x)).trans (le_joinPair _ y (θ x))
  have hRyp : R y (θ x) := joinPair_rel _ _ _
  have hRxp : R x (θ x) := le_joinPair _ _ _ (joinPair_rel _ _ _)
  have hRa : SameCycle.setoid (swap x y) ≤ R := cycle_swap_le R x y (R.trans' hRxp (R.symm' hRyp))
  have hRb : SameCycle.setoid (swap y (θ x)) ≤ R := cycle_swap_le R y (θ x) hRyp
  have hs : SameCycle.setoid σ ≤ R := by
    have hh := cycles_mul_le (swap x y) (swap x y * σ) R hRa (le_sup_left.trans hr'R)
    simpa only [← mul_assoc,swap_mul_self,one_mul] using hh
  have ht : SameCycle.setoid θ ≤ R := by
    have hh := cycles_mul_le _ (swap y (θ x)) R
      (cycles_mul_le (swap y (θ x)) _ R hRb
        (cycles_mul_le (swap x y) (suppress θ x y) R hRa (le_sup_right.trans hr'R))) hRb
    simp only [suppress,← mul_assoc,swap_mul_self,one_mul] at hh
    simpa only [mul_assoc,swap_mul_self,mul_one] using hh
  exact le_antisymm hRr (sup_le hs ht)

end KervaireRibbon

end

end OAI

-- ---- platform node ----
open OAI OAI.KervaireRibbon
open Equiv Equiv.Perm
open scoped Classical


theorem solution : type_of% @_root_.OAI.KervaireRibbon.components_suppress := @_root_.OAI.KervaireRibbon.components_suppress
