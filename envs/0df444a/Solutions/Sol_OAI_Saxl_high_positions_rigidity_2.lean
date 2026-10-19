-- Prove2me | solution 2 for OAI.Saxl.high_positions_rigidity
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T01:05:01.360199+00:00
-- url     : https://prove2.me/submissions/30099e76-5968-4ae4-88f6-537f42706a00

-- Generated from openai/math@1581d4c lean/OAI/RepresentationTheory/Saxl/HighProjection.lean:L46-L96
-- (upload_full_project.md Phase 4): solution for node OAI.Saxl.high_positions_rigidity. The node keeps its source
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
import Theorems.Thm_OAI_Saxl_finset_eq_of_signed_sum

-- ---- from OAI.RepresentationTheory.Saxl.HighProjection ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section

open scoped TensorProduct

namespace Saxl
/- Translate the high part of each row to the smaller staircase. -/
theorem high_positions_rigidity (h s : ℕ)
    (g k : Equiv.Perm (staircase (h+s)).cells)
    (hg : ∀ x, (g x).val.1 = x.val.1)
    (hk : ∀ x, (k x).val.2 = x.val.2)
    (hc : ∀ x, s ≤ (g x).val.2 ↔ s ≤ (k x).val.1) :
    ∀ x, s ≤ (g x).val.2 ↔ x.val.1 + x.val.2 < h := by
  classical
  let A : Finset (staircase (h+s)).cells := Finset.univ.filter (fun x => s ≤ (g x).val.2)
  let B : Finset (staircase (h+s)).cells := Finset.univ.filter (fun x => x.val.1 + x.val.2 < h)
  let eR : A ≃ (staircase h).cells :=
    (Equiv.subtypeEquiv g (by intro x; simp only [A, Finset.mem_filter, Finset.mem_univ, true_and])).trans
      (highRowEquiv h s)
  let eC : A ≃ (staircase h).cells :=
    (Equiv.subtypeEquiv k (by intro x; simp only [A, Finset.mem_filter, Finset.mem_univ, true_and]; exact hc x)).trans
      (highColEquiv h s)
  let eB : B ≃ (staircase h).cells :=
    { toFun := fun x => ⟨x.val.val, mem_staircase.mpr (by simpa [B] using x.property)⟩
      invFun := fun x => ⟨⟨x.val, mem_staircase.mpr (by
        have hx := mem_staircase.mp x.property; omega)⟩, by simp [B, mem_staircase.mp x.property]⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hcard : A.card = B.card := by
    have he := Fintype.card_congr (eR.trans eB.symm)
    simpa using he
  have hrow : ∑ x ∈ A, (x.val.1 : ℤ) = ∑ x ∈ B, (x.val.1 : ℤ) := by
    rw [← Finset.sum_coe_sort A, ← Finset.sum_coe_sort B]
    have hR := Equiv.sum_comp eR (fun x => (x.val.1 : ℤ))
    have hB := Equiv.sum_comp eB (fun x => (x.val.1 : ℤ))
    simpa [eR, eB, highRowEquiv, hg] using hR.trans hB.symm
  have hcol : ∑ x ∈ A, (x.val.2 : ℤ) = ∑ x ∈ B, (x.val.2 : ℤ) := by
    rw [← Finset.sum_coe_sort A, ← Finset.sum_coe_sort B]
    have hC := Equiv.sum_comp eC (fun x => (x.val.2 : ℤ))
    have hB := Equiv.sum_comp eB (fun x => (x.val.2 : ℤ))
    simpa [eC, eB, highColEquiv, hk] using hC.trans hB.symm
  let w := fun x : (staircase (h+s)).cells =>
    2 * (h : ℤ) - 1 - 2 * (x.val.1 : ℤ) - 2 * (x.val.2 : ℤ)
  have he : ∑ x ∈ A, w x = ∑ x ∈ B, w x := by
    simp only [w, Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul]
    rw [hcard, hrow, hcol]
  have hab := finset_eq_of_signed_sum A B w
    (fun x hx => by
      have hh : x.val.1 + x.val.2 < h := by simpa [B] using hx
      dsimp [w]
      omega)
    (fun x hx => by
      have hh : ¬x.val.1 + x.val.2 < h := by simpa [B] using hx
      dsimp [w]
      omega) he
  intro x
  have := Finset.ext_iff.mp hab x
  simpa [A, B] using this

/- Local same-high projection in the ordinary pair-letter coordinate space. -/
/- Move low row letters to the band and high row letters to B_h. -/
/- The projected generator is genuinely nonzero for every band width,
without assuming a tensor factorization. -/
end Saxl

end

end OAI

-- ---- platform node ----
open OAI OAI.Saxl
open scoped TensorProduct


theorem solution : type_of% @_root_.OAI.Saxl.high_positions_rigidity := @_root_.OAI.Saxl.high_positions_rigidity
