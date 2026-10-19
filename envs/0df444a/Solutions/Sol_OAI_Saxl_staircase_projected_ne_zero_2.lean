-- Prove2me | solution 2 for OAI.Saxl.staircase_projected_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T01:08:51.0319+00:00
-- url     : https://prove2.me/submissions/c4842780-abe5-4e1a-a859-3359c362e2bf

-- Generated from openai/math@1581d4c lean/OAI/RepresentationTheory/Saxl/HighProjection.lean:L260-L289
-- (upload_full_project.md Phase 4): solution for node OAI.Saxl.staircase_projected_ne_zero. The node keeps its source
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
import Theorems.Thm_OAI_Saxl_polytabloid_rowWord

-- ---- from OAI.RepresentationTheory.Saxl.Polytabloid ----
namespace OAI

noncomputable section

open scoped TensorProduct

universe uX

namespace Saxl

/- A finite set is the unique maximizer of its strictly signed separator.
Used below for the Ferrers equality case in the Specht submodule theorem. -/
/- A column-injective rearrangement of the canonical row word has precisely
Ferrers support. This is the equality-of-margins argument, without using
unproved Specht or Young-rule inputs. -/
/- The complex-valued sign character. -/
/- Actual column antisymmetrizer on the word-coordinate module. -/
lemma columnAlt_row {n : ℕ} {μ : YoungDiagram} (t : Tableau n μ) :
    columnAlt t (Pi.single (rowWord t) 1) = polytabloid t := by
  simp [columnAlt, polytabloid, LinearMap.sum_apply]

/- Construction of the witnessing column rearrangement. -/
end Saxl

end

end OAI

-- ---- from OAI.RepresentationTheory.Saxl.HighProjection ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e

namespace OAI

noncomputable section

open scoped TensorProduct

namespace Saxl
/- Translate the high part of each row to the smaller staircase. -/
/- Local same-high projection in the ordinary pair-letter coordinate space. -/
lemma columnAlt_left {n d : ℕ} {μ : YoungDiagram} (t : Tableau n μ)
    (h : columnGroup t) :
    wordRep n d (h : Equiv.Perm (Fin n)) * columnAlt (d := d) t =
      signC (h : Equiv.Perm (Fin n)) • columnAlt t := by
  classical
  let := Fintype.ofFinite (columnGroup t)
  unfold columnAlt
  simp only [Finset.mul_sum, mul_smul_comm, Finset.smul_sum]
  symm
  apply (Equiv.sum_comp (Equiv.mulLeft h) _).symm.trans
  apply Finset.sum_congr rfl
  intro g hg
  change signC (h : Equiv.Perm (Fin n)) •
    signC ((h * g : columnGroup t) : Equiv.Perm (Fin n)) •
      wordRep n d ((h * g : columnGroup t) : Equiv.Perm (Fin n)) = _
  simp only [Subgroup.coe_mul, map_mul, smul_smul]
  rw [← mul_assoc, signC_mul_self, one_mul]

lemma polytabloid_alternating {n : ℕ} {μ : YoungDiagram} (t : Tableau n μ)
    (h : columnGroup t) : wordRep n (μ.colLen 0) (h : Equiv.Perm (Fin n))
      (polytabloid t) = signC (h : Equiv.Perm (Fin n)) • polytabloid t := by
  rw [← columnAlt_row]
  exact congrArg (fun L : Module.End ℂ (WordSpace n (μ.colLen 0)) =>
    L (Pi.single (rowWord t) 1)) (columnAlt_left t h)

/- Move low row letters to the band and high row letters to B_h. -/
lemma rotateRow_high (h s : ℕ) (x : (staircase (h+s)).cells) :
    s ≤ (rotateRow h s x).val.2 ↔ x.val.1 + x.val.2 < h := by
  have hx : x.val.1 + x.val.2 < h+s := mem_staircase.mp x.property
  change s ≤ (if x.val.2 < h - x.val.1 then x.val.2+s else x.val.2-(h-x.val.1)) ↔ _
  split_ifs <;> omega

lemma rotateColumn_high (h s : ℕ) (x : (staircase (h+s)).cells) :
    s ≤ (rotateColumn h s x).val.1 ↔ x.val.1 + x.val.2 < h := by
  have hh := rotateRow_high h s (staircaseSwap (h+s) x)
  change s ≤ (rotateRow h s (staircaseSwap (h+s) x)).val.2 ↔ _
  simpa [staircaseSwap, Nat.add_comm] using hh

lemma polytabloid_column_coeff {n : ℕ} {μ : YoungDiagram} (t : Tableau n μ)
    (g : columnGroup t) :
    polytabloid t (rowWord t ∘ (g : Equiv.Perm (Fin n))) = signC (g : Equiv.Perm (Fin n)) := by
  have hh := congrFun (polytabloid_alternating t g) (rowWord t)
  change polytabloid t (rowWord t ∘ (g : Equiv.Perm (Fin n))) =
    signC (g : Equiv.Perm (Fin n)) * polytabloid t (rowWord t) at hh
  simpa [polytabloid_rowWord] using hh

/- The projected generator is genuinely nonzero for every band width,
without assuming a tensor factorization. -/
theorem staircase_projected_ne_zero (h s : ℕ) :
    sameHighProjection _ _ _ s (staircaseWord (h+s)) ≠ 0 := by
  classical
  let a := rowWord (stairRowTableau (h+s)) ∘ (rotateRowPositions h s : Equiv.Perm _)
  let b := rowWord (stairTableau (h+s)) ∘ (rotateColumnPositions h s : Equiv.Perm _)
  let w := mergeWords a b
  have ha (i) : s ≤ (a i).val ↔ (stairTableau (h+s) i).val.1 + (stairTableau (h+s) i).val.2 < h := by
    have hh := rotateRow_high h s (stairTableau (h+s) i)
    simpa [a, rowWord, stairRowTableau, rotateRowPositions, staircaseSwap] using hh
  have hb (i) : s ≤ (b i).val ↔ (stairTableau (h+s) i).val.1 + (stairTableau (h+s) i).val.2 < h := by
    have hh := rotateColumn_high h s (stairTableau (h+s) i)
    simpa [b, rowWord, rotateColumnPositions] using hh
  have hp : ∀ i, s ≤ (splitLeft w i).val ↔ s ≤ (splitRight w i).val := by
    intro i
    simp only [w, splitLeft_merge, splitRight_merge]
    exact (ha i).trans (hb i).symm
  intro hz
  have he := congrFun hz w
  change sameHighProjection _ _ _ s (staircaseWord (h+s)) w = 0 at he
  simp only [sameHighProjection, Representation.IntertwiningMap.coe_mk, LinearMap.coe_mk,
    AddHom.coe_mk, staircaseWord, wordTensor_tmul, w, splitLeft_merge, splitRight_merge,
    a, b, polytabloid_column_coeff] at he
  have hn (g : Equiv.Perm (Fin (staircase (h+s)).card)) : signC g ≠ 0 := by
    intro hz
    have hh := signC_mul_self g
    rw [hz, zero_mul] at hh
    exact zero_ne_one hh
  have hpab : ∀ i, s ≤ (a i).val ↔ s ≤ (b i).val := fun i => (ha i).trans (hb i).symm
  rw [ite_eq_left hpab] at he
  exact mul_ne_zero (hn _) (hn _) he

end Saxl

end

end OAI

-- ---- platform node ----
open OAI OAI.Saxl
open scoped TensorProduct


theorem solution : type_of% @_root_.OAI.Saxl.staircase_projected_ne_zero := @_root_.OAI.Saxl.staircase_projected_ne_zero
