-- Prove2me | solution 2 for OAI.Saxl.staircase_projected_high_positions
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T01:07:01.878988+00:00
-- url     : https://prove2.me/submissions/030b4a58-5dd7-4279-b493-fd38baae6a86

-- Generated from openai/math@1581d4c lean/OAI/RepresentationTheory/Saxl/HighProjection.lean:L132-L171
-- (upload_full_project.md Phase 4): solution for node OAI.Saxl.staircase_projected_high_positions. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_Saxl
import Definitions.Def_OAI_RepresentationTheory_Saxl_Basic
import Definitions.Def_OAI_RepresentationTheory_Saxl_Polytabloid
import Definitions.Def_OAI_RepresentationTheory_Saxl_SpechtSubmodule
import Definitions.Def_OAI_RepresentationTheory_Saxl_SpechtDuality
import Definitions.Def_OAI_RepresentationTheory_Saxl_TableauTransport
import Definitions.Def_OAI_RepresentationTheory_Saxl_StaircaseTensor
import Definitions.Def_OAI_RepresentationTheory_Saxl_HighProjection
import Theorems.Thm_OAI_Saxl_high_positions_rigidity

-- ---- from OAI.RepresentationTheory.Saxl.HighProjection ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section

open scoped TensorProduct

namespace Saxl
/- Translate the high part of each row to the smaller staircase. -/
lemma polytabloid_support {n : ℕ} {μ : YoungDiagram} (t : Tableau n μ)
    (a : Fin n → Fin (μ.colLen 0)) (ha : polytabloid t a ≠ 0) :
    ∃ g : columnGroup t, a = rowWord t ∘ (g : Equiv.Perm (Fin n)) := by
  classical
  have hex : ∃ g : columnGroup t, a ∘ (g : Equiv.Perm (Fin n)) = rowWord t := by
    by_contra! hh
    apply ha
    unfold polytabloid
    simp only [Finset.sum_apply, Pi.smul_apply, wordRep, MonoidHom.coe_mk,
      OneHom.coe_mk, LinearMap.coe_mk, AddHom.coe_mk, Pi.single_apply]
    simp [hh]
  obtain ⟨g, hg⟩ := hex
  refine ⟨g⁻¹, ?_⟩
  funext i
  have he := congrFun hg ((g : Equiv.Perm (Fin n))⁻¹ i)
  simpa using he

/- Local same-high projection in the ordinary pair-letter coordinate space. -/
theorem staircase_projected_high_positions (h s : ℕ)
    (w : Fin (staircase (h+s)).card → Fin ((staircase (h+s)).colLen 0 * (staircase (h+s)).colLen 0))
    (hw : sameHighProjection _ _ _ s (staircaseWord (h+s)) w ≠ 0) :
    ∀ i, s ≤ (splitLeft w i).val ↔
      ((stairTableau (h+s) i).val.1 + (stairTableau (h+s) i).val.2 < h) := by
  classical
  have heq : ∀ i, s ≤ (splitLeft w i).val ↔ s ≤ (splitRight w i).val := by
    by_contra hh
    apply hw
    simp [sameHighProjection, hh]
  have hww : staircaseWord (h+s) w ≠ 0 := by
    simpa [sameHighProjection, heq] using hw
  have hp : polytabloid (stairRowTableau (h+s)) (splitLeft w) *
      polytabloid (stairTableau (h+s)) (splitRight w) ≠ 0 := by
    simpa only [staircaseWord, wordTensor_tmul] using hww
  obtain ⟨g, hg⟩ := polytabloid_support (stairRowTableau (h+s)) _ (mul_ne_zero_iff.mp hp).1
  obtain ⟨k, hk⟩ := polytabloid_support (stairTableau (h+s)) _ (mul_ne_zero_iff.mp hp).2
  let t := stairTableau (h+s)
  let gc : Equiv.Perm (staircase (h+s)).cells := (t.symm.trans (g : Equiv.Perm _)).trans t
  let kc : Equiv.Perm (staircase (h+s)).cells := (t.symm.trans (k : Equiv.Perm _)).trans t
  have hgc : ∀ x, (gc x).val.1 = x.val.1 := by
    intro x
    have hh := g.property (t.symm x)
    change (t ((g : Equiv.Perm _) (t.symm x))).val.1 = (t (t.symm x)).val.1 at hh
    simpa [gc] using hh
  have hkc : ∀ x, (kc x).val.2 = x.val.2 := by
    intro x
    have hh := k.property (t.symm x)
    change (t ((k : Equiv.Perm _) (t.symm x))).val.2 = (t (t.symm x)).val.2 at hh
    simpa [kc] using hh
  have hcommon : ∀ x, s ≤ (gc x).val.2 ↔ s ≤ (kc x).val.1 := by
    intro x
    have hh := heq (t.symm x)
    rw [hg, hk] at hh
    exact hh
  have hr := high_positions_rigidity h s gc kc hgc hkc hcommon
  intro i
  have hh := hr (t i)
  rw [hg]
  simpa [gc, t, rowWord, stairRowTableau, staircaseSwap] using hh

/- Move low row letters to the band and high row letters to B_h. -/
/- The projected generator is genuinely nonzero for every band width,
without assuming a tensor factorization. -/
end Saxl

end

end OAI

-- ---- platform node ----
open OAI OAI.Saxl
open scoped TensorProduct


theorem solution : type_of% @_root_.OAI.Saxl.staircase_projected_high_positions := @_root_.OAI.Saxl.staircase_projected_high_positions
