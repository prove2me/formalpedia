-- Prove2me | solution 2 for OAI.Saxl.specht_irreducible
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T01:01:41.577061+00:00
-- url     : https://prove2.me/submissions/bbb31332-9291-4117-b527-763006f79bad

-- Generated from openai/math@1581d4c lean/OAI/RepresentationTheory/Saxl/SpechtSubmodule.lean:L196-L226
-- (upload_full_project.md Phase 4): solution for node OAI.Saxl.specht_irreducible. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_Saxl
import Definitions.Def_OAI_RepresentationTheory_Saxl_Basic
import Definitions.Def_OAI_RepresentationTheory_Saxl_Polytabloid
import Definitions.Def_OAI_RepresentationTheory_Saxl_SpechtSubmodule
import Theorems.Thm_OAI_Saxl_columnAlt_tabloid
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

-- ---- from OAI.RepresentationTheory.Saxl.SpechtSubmodule ----
namespace OAI

noncomputable section

open scoped TensorProduct

universe uG uV

namespace Saxl

/- The actual row-tabloid permutation module, embedded in the word space. -/
lemma columnAlt_mem {n d : ℕ} {μ : YoungDiagram} (t : Tableau n μ)
    (P : Subrepresentation (wordRep n d)) {x : WordSpace n d} (hx : x ∈ P) :
    columnAlt t x ∈ P := by
  classical
  unfold columnAlt
  simp only [LinearMap.sum_apply, LinearMap.smul_apply]
  exact Submodule.sum_mem _ (fun g _ =>
    Submodule.smul_mem _ _ (P.apply_mem_toSubmodule (g : Equiv.Perm (Fin n)) hx))

lemma spechtSub_le_tabloidSub {n : ℕ} {μ : YoungDiagram} (t : Tableau n μ) :
    spechtSub t ≤ tabloidSub t := by
  apply (cyclic_le _ _ _).mpr
  rw [← columnAlt_row]
  exact columnAlt_mem t (tabloidSub t) (mem_cyclic _ _)

/- The Ferrers shape forces the column antisymmetrizer to have rank one
on the row-tabloid module. -/
/- On words, precomposition by a position permutation is a bijection. -/
lemma columnAlt_pair {n d : ℕ} {μ : YoungDiagram} (t : Tableau n μ)
    (x y : WordSpace n d) :
    dotProduct (columnAlt t x) y = dotProduct x (columnAlt t y) := by
  classical
  let := Fintype.ofFinite (columnGroup t)
  unfold columnAlt
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, sum_dotProduct,
    dotProduct_sum, smul_dotProduct, dotProduct_smul, wordPair_move]
  apply (Equiv.sum_comp (Equiv.inv (columnGroup t)) _).symm.trans
  apply Finset.sum_congr rfl
  intro g hg
  simp only [Equiv.inv_apply, Subgroup.coe_inv, signC_inv, inv_inv]

lemma columnAlt_coefficient {n : ℕ} {μ : YoungDiagram} (t : Tableau n μ)
    (x : WordSpace n (μ.colLen 0)) :
    columnAlt t x (rowWord t) = dotProduct x (polytabloid t) := by
  classical
  rw [← dotProduct_single_one (columnAlt t x), columnAlt_pair, columnAlt_row]

lemma polytabloid_ne_zero {n : ℕ} {μ : YoungDiagram} (t : Tableau n μ) :
    polytabloid t ≠ 0 := by
  intro h
  have hh := congrFun h (rowWord t)
  rw [polytabloid_rowWord] at hh
  exact one_ne_zero hh

lemma specht_detect {n : ℕ} {μ : YoungDiagram} (t : Tableau n μ)
    {x : WordSpace n (μ.colLen 0)} (hx : x ∈ spechtSub t) (hx0 : x ≠ 0) :
    ∃ g : Equiv.Perm (Fin n), dotProduct (wordRep n (μ.colLen 0) g x) (polytabloid t) ≠ 0 := by
  classical
  by_contra h
  push Not at h
  have hy : ∀ y ∈ (spechtSub t).toSubmodule, dotProduct x y = 0 := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨g, rfl⟩ := hy
      have hh := wordPair_move g⁻¹ x (polytabloid t)
      rw [inv_inv] at hh
      exact hh.symm.trans (h g⁻¹)
    | zero => exact dotProduct_zero _
    | add y z hy hz ihy ihz => rw [dotProduct_add, ihy, ihz, add_zero]
    | smul c y hy ih => rw [dotProduct_smul, ih, smul_zero]
  have hs : star x ∈ (spechtSub t).toSubmodule :=
    cyclic_star (polytabloid t) (polytabloid_real t) hx
  let : PartialOrder ℂ := RCLike.toPartialOrder
  let : StarOrderedRing ℂ := RCLike.toStarOrderedRing
  exact hx0 (dotProduct_self_star_eq_zero.mp (hy (star x) hs))

/- Every nonzero vector in the genuine complex Specht cyclic subspace
again generates that whole subspace. -/
theorem specht_cyclic_of_ne_zero {n : ℕ} {μ : YoungDiagram} (t : Tableau n μ)
    {x : WordSpace n (μ.colLen 0)} (hx : x ∈ spechtSub t) (hx0 : x ≠ 0) :
    cyclic (wordRep n (μ.colLen 0)) x = spechtSub t := by
  classical
  apply le_antisymm ((cyclic_le _ _ _).mpr hx)
  apply (cyclic_le _ _ _).mpr
  obtain ⟨g, hg⟩ := specht_detect t hx hx0
  have he : wordRep n (μ.colLen 0) g x ∈ spechtSub t :=
    (spechtSub t).apply_mem_toSubmodule g hx
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp
    (columnAlt_tabloid t (spechtSub_le_tabloidSub t he))
  have hc0 : c ≠ 0 := by
    intro h0
    rw [h0, zero_smul] at hc
    apply hg
    rw [← columnAlt_coefficient, ← hc]
    rfl
  have hh := columnAlt_mem t (cyclic (wordRep n (μ.colLen 0)) x)
    ((cyclic (wordRep n (μ.colLen 0)) x).apply_mem_toSubmodule g (mem_cyclic _ _))
  rw [← hc] at hh
  exact (Submodule.smul_mem_iff _ hc0).mp hh

/- Inclusion of a subrepresentation of a subrepresentation into the ambient space. -/
/- The complex polytabloid module is irreducible. -/
theorem specht_irreducible {n : ℕ} {μ : YoungDiagram} (t : Tableau n μ) :
    Representation.IsIrreducible (spechtRep t) := by
  classical
  have hb : (⊥ : Subrepresentation (spechtRep t)) ≠ ⊤ := by
    intro h
    have hp : (⟨polytabloid t, mem_cyclic _ _⟩ : Specht t) ∈
        (⊥ : Subrepresentation (spechtRep t)).toSubmodule := by
      rw [h]
      trivial
    have he : (⟨polytabloid t, mem_cyclic _ _⟩ : Specht t) = 0 :=
      (Submodule.mem_bot ℂ).mp hp
    exact polytabloid_ne_zero t (congrArg Subtype.val he)
  let : Nontrivial (Subrepresentation (spechtRep t)) := ⟨⟨⊥, ⊤, hb⟩⟩
  apply IsSimpleOrder.of_forall_eq_top
  intro S hS
  have hn : S.toSubmodule ≠ ⊥ := by
    intro h
    exact hS (Subrepresentation.toSubmodule_injective h)
  obtain ⟨x, hx, hx0⟩ := (Submodule.ne_bot_iff S.toSubmodule).mp hn
  have hv : (x : WordSpace n (μ.colLen 0)) ≠ 0 := by
    intro h
    exact hx0 (Subtype.ext h)
  have hl : cyclic (wordRep n (μ.colLen 0)) x.val ≤ subrepAmbient (spechtSub t) S :=
    (cyclic_le _ _ _).mpr ⟨x, hx, rfl⟩
  rw [specht_cyclic_of_ne_zero t x.property hv] at hl
  apply le_antisymm le_top
  intro y hy
  have hm := hl y.property
  obtain ⟨z, hz, he⟩ := hm
  have he' : z = y := Subtype.ext he
  exact he' ▸ hz

end Saxl

end

end OAI

-- ---- platform node ----
open OAI OAI.Saxl
open scoped TensorProduct


theorem solution : type_of% @_root_.OAI.Saxl.specht_irreducible := @_root_.OAI.Saxl.specht_irreducible
