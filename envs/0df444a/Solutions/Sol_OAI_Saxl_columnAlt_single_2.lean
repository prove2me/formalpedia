-- Prove2me | solution 2 for OAI.Saxl.columnAlt_single
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T00:58:27.149492+00:00
-- url     : https://prove2.me/submissions/94f891e4-1b4f-45b1-ac1d-4bfba4c10bd7

-- Generated from openai/math@1581d4c lean/OAI/RepresentationTheory/Saxl/Polytabloid.lean:L207-L225
-- (upload_full_project.md Phase 4): solution for node OAI.Saxl.columnAlt_single. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_Saxl
import Definitions.Def_OAI_RepresentationTheory_Saxl_Basic
import Definitions.Def_OAI_RepresentationTheory_Saxl_Polytabloid
import Theorems.Thm_OAI_Saxl_columnAlt_collision
import Theorems.Thm_OAI_Saxl_columnAlt_mul
import Theorems.Thm_OAI_Saxl_finset_eq_of_signed_sum

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
lemma ferrers_rearrangement {n : ℕ} {μ : YoungDiagram} (t : Tableau n μ)
    (g : Equiv.Perm (Fin n))
    (hinj : Function.Injective (fun i => ((t (g i)).val.1, (t i).val.2))) :
    ∀ i, ((t (g i)).val.1, (t i).val.2) ∈ μ := by
  classical
  let f : Fin n → ℕ × ℕ := fun i => ((t (g i)).val.1, (t i).val.2)
  let w : ℕ × ℕ → ℤ := fun c => 2 * (μ.rowLen c.1 : ℤ) - 2 * c.2 - 1
  have ht : Function.Injective (fun i : Fin n => (t i).val) :=
    Subtype.val_injective.comp t.injective
  have himage : Finset.univ.image (fun i : Fin n => (t i).val) = μ.cells := by
    ext x
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨i, rfl⟩
      exact (t i).property
    · intro hx
      exact ⟨t.symm ⟨x, hx⟩, by simp⟩
  have he : ∑ x ∈ Finset.univ.image f, w x = ∑ x ∈ μ.cells, w x := by
    rw [← himage, Finset.sum_image (fun _ _ _ _ h => hinj h),
      Finset.sum_image (fun _ _ _ _ h => ht h)]
    simp only [w, Finset.sum_sub_distrib, ← Finset.mul_sum]
    rw [Equiv.sum_comp g (fun i => (μ.rowLen (t i).val.1 : ℤ))]
  have heq := finset_eq_of_signed_sum (Finset.univ.image f) μ.cells w
    (fun c hc => by
      have h := YoungDiagram.mem_iff_lt_rowLen.mp hc
      dsimp [w]
      omega)
    (fun c hc => by
      have h : μ.rowLen c.1 ≤ c.2 :=
        le_of_not_gt (fun h => hc (YoungDiagram.mem_iff_lt_rowLen.mpr h))
      dsimp [w]
      omega) he
  intro i
  exact (le_of_eq heq) (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)

/- The complex-valued sign character. -/
/- Actual column antisymmetrizer on the word-coordinate module. -/
lemma columnAlt_row {n : ℕ} {μ : YoungDiagram} (t : Tableau n μ) :
    columnAlt t (Pi.single (rowWord t) 1) = polytabloid t := by
  simp [columnAlt, polytabloid, LinearMap.sum_apply]

/- Construction of the witnessing column rearrangement. -/
lemma column_rearrangement {n : ℕ} {μ : YoungDiagram} (t : Tableau n μ)
    (g : Equiv.Perm (Fin n))
    (hinj : Function.Injective (fun i => ((t (g i)).val.1, (t i).val.2))) :
    ∃ h : columnGroup t, rowWord t ∘ g = rowWord t ∘ (h : Equiv.Perm (Fin n)) := by
  classical
  let f : Fin n → Fin n := fun i =>
    t.symm ⟨((t (g i)).val.1, (t i).val.2), ferrers_rearrangement t g hinj i⟩
  have hf : Function.Injective f := by
    intro i j hij
    apply hinj
    have hh := congrArg (fun k => (t k).val) hij
    simpa [f] using hh
  let h : Equiv.Perm (Fin n) := Equiv.ofBijective f ⟨hf, Finite.surjective_of_injective hf⟩
  have hcol : h ∈ columnGroup t := by
    intro i
    change (t (f i)).val.2 = _
    simp [f]
  refine ⟨⟨h, hcol⟩, ?_⟩
  funext i
  apply Fin.ext
  change (t (g i)).val.1 = (t (f i)).val.1
  simp [f]

lemma columnAlt_column {n : ℕ} {μ : YoungDiagram} (t : Tableau n μ)
    (h : columnGroup t) :
    columnAlt t (Pi.single (rowWord t ∘ (h : Equiv.Perm (Fin n))) 1) =
      signC (h : Equiv.Perm (Fin n)) • polytabloid t := by
  classical
  have he : wordRep n (μ.colLen 0) ((h⁻¹ : columnGroup t) : Equiv.Perm (Fin n))
      (Pi.single (rowWord t) 1) =
      Pi.single (rowWord t ∘ (h : Equiv.Perm (Fin n))) 1 := by
    rw [wordRep_single]
    simp only [Subgroup.coe_inv, inv_inv]
  rw [← he, ← Module.End.mul_apply, columnAlt_mul, LinearMap.smul_apply,
    columnAlt_row, Subgroup.coe_inv, signC_inv]

lemma columnAlt_single {n : ℕ} {μ : YoungDiagram} (t : Tableau n μ)
    (g : Equiv.Perm (Fin n)) :
    columnAlt t (Pi.single (rowWord t ∘ g) 1) ∈
      Submodule.span ℂ {polytabloid t} := by
  classical
  by_cases hi : Function.Injective (fun i : Fin n => ((t (g i)).val.1, (t i).val.2))
  · obtain ⟨h, hh⟩ := column_rearrangement t g hi
    rw [hh, columnAlt_column]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton _))
  · simp only [Function.Injective] at hi
    push Not at hi
    obtain ⟨i, j, hc, hij⟩ := hi
    have ha : (rowWord t ∘ g) i = (rowWord t ∘ g) j := by
      apply Fin.ext
      have hh := congrArg Prod.fst hc
      exact hh
    have hcol := congrArg Prod.snd hc
    rw [columnAlt_collision t _ i j hij hcol ha]
    exact Submodule.zero_mem _

end Saxl

end

end OAI

-- ---- platform node ----
open OAI OAI.Saxl
open scoped TensorProduct


theorem solution : type_of% @_root_.OAI.Saxl.columnAlt_single := @_root_.OAI.Saxl.columnAlt_single
