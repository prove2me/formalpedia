-- Prove2me | solution 1 for OAI.Saxl.staircase_projected_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T00:29:20.679203+00:00
-- url     : https://prove2.me/submissions/13c91478-ace2-4f00-8b29-b789a4544e0c

import Mathlib
import Definitions.Def_Saxl
import Definitions.Def_OAI_RepresentationTheory_Saxl_Basic
import Definitions.Def_OAI_RepresentationTheory_Saxl_Polytabloid
import Definitions.Def_OAI_RepresentationTheory_Saxl_SpechtSubmodule
import Definitions.Def_OAI_RepresentationTheory_Saxl_SpechtDuality
import Definitions.Def_OAI_RepresentationTheory_Saxl_TableauTransport
import Definitions.Def_OAI_RepresentationTheory_Saxl_StaircaseTensor
import Definitions.Def_OAI_RepresentationTheory_Saxl_HighProjection

open OAI OAI.Saxl
open scoped TensorProduct
theorem h42_poly_at {n : ℕ} {μ : YoungDiagram} (t : Tableau n μ) (g : Equiv.Perm (Fin n))
    (hg : g ∈ columnGroup t) : polytabloid t (rowWord t ∘ g) ≠ 0 := by
  classical
  unfold polytabloid
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_eq_single (⟨g⁻¹, inv_mem hg⟩ : columnGroup t)]
  · change _ * (Pi.single (rowWord t) (1:ℂ) : WordSpace n _)
      ((rowWord t ∘ g) ∘ (g⁻¹ : Equiv.Perm (Fin n))) ≠ 0
    rw [show (rowWord t ∘ g) ∘ (g⁻¹ : Equiv.Perm (Fin n)) = rowWord t by funext i; simp,
      Pi.single_eq_same, mul_one]
    simp
  · intro k _ hk
    have key : (rowWord t ∘ g) ∘ (k : Equiv.Perm (Fin n)) ≠ rowWord t := by
      intro h
      apply hk
      have hgk : g * (k : Equiv.Perm (Fin n)) ∈ columnGroup t := mul_mem hg k.2
      have hone : g * (k : Equiv.Perm (Fin n)) = 1 := by
        ext i : 1
        have h1 := congrFun h i
        have h2 := hgk i
        rw [Equiv.Perm.mul_apply] at h2
        have h3 : (t (g ((k : Equiv.Perm (Fin n)) i))).val = (t i).val := by
          simp only [rowWord, Function.comp_apply, Fin.mk.injEq] at h1
          exact Prod.ext h1 h2
        have := t.injective (Subtype.ext h3)
        simpa using this
      apply Subtype.ext
      exact eq_inv_of_mul_eq_one_right hone
    change _ * (Pi.single (rowWord t) (1:ℂ) : WordSpace n _)
      ((rowWord t ∘ g) ∘ (k : Equiv.Perm (Fin n))) = 0
    rw [Pi.single_apply, if_neg key, mul_zero]
  · intro h; exact absurd (by simp) h

theorem solution (h s : ℕ) :
    sameHighProjection _ _ _ s (staircaseWord (h+s)) ≠ 0 := by
  classical
  intro H
  let T := stairTableau (h+s)
  let a1 := rowWord (stairRowTableau (h+s)) ∘ ((rotateRowPositions h s : columnGroup _) : Equiv.Perm _)
  let a2 := rowWord (stairTableau (h+s)) ∘ ((rotateColumnPositions h s : columnGroup _) : Equiv.Perm _)
  let w0 := mergeWords a1 a2
  have hrot : ∀ x : (staircase (h+s)).cells,
      s ≤ (rotateRow h s x).val.2 ↔ x.val.1 + x.val.2 < h := by
    intro x
    have hx : x.val.1 + x.val.2 < h+s := mem_staircase.mp x.property
    change s ≤ (rotateRowCell h s x).val.2 ↔ _
    simp only [rotateRowCell]
    split_ifs <;> constructor <;> intro <;> omega
  have h1 : ∀ i, (a1 i).val = (rotateRow h s (T i)).val.2 := by
    intro i
    simp [a1, T, rowWord, stairRowTableau, staircaseSwap, rotateRowPositions]
  have h2 : ∀ i, (a2 i).val = (rotateRow h s (staircaseSwap _ (T i))).val.2 := by
    intro i
    simp [a2, T, rowWord, rotateColumnPositions, rotateColumn, staircaseSwap]
  have hcond : ∀ i, s ≤ (splitLeft w0 i).val ↔ s ≤ (splitRight w0 i).val := by
    intro i
    simp only [w0, splitLeft_merge, splitRight_merge]
    rw [h1, h2, hrot, hrot]
    simp only [staircaseSwap, Equiv.coe_fn_mk]
    constructor <;> intro <;> omega
  have hv := congrFun H w0
  change (if (∀ i, s ≤ (splitLeft w0 i).val ↔ s ≤ (splitRight w0 i).val)
    then staircaseWord (h+s) w0 else 0) = 0 at hv
  rw [if_pos hcond, staircaseWord, wordTensor_tmul, splitLeft_merge, splitRight_merge] at hv
  exact mul_ne_zero (h42_poly_at _ _ (rotateRowPositions h s).2)
    (h42_poly_at _ _ (rotateColumnPositions h s).2) hv

