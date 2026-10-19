-- Prove2me | solution 1 for OAI.Saxl.specht_rows_of_hom
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T01:30:49.700586+00:00
-- url     : https://prove2.me/submissions/99781937-1972-4197-a528-464707bd6f2b

-- Generated from openai/math@1581d4c lean/OAI/RepresentationTheory/Saxl/SpechtClassification.lean:L237-L251
-- (upload_full_project.md Phase 4): solution for node OAI.Saxl.specht_rows_of_hom. The node keeps its source
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
import Definitions.Def_OAI_RepresentationTheory_Saxl_CoordinateSector
import Definitions.Def_OAI_RepresentationTheory_Saxl_PositionSplit
import Definitions.Def_OAI_RepresentationTheory_Saxl_BandFactorization
import Definitions.Def_OAI_RepresentationTheory_Saxl_PathAlternation
import Definitions.Def_OAI_RepresentationTheory_Saxl_BandMatrices
import Definitions.Def_OAI_RepresentationTheory_Saxl_PathContraction
import Definitions.Def_OAI_RepresentationTheory_Saxl_ColumnContraction
import Definitions.Def_OAI_RepresentationTheory_Saxl_BandPairing
import Definitions.Def_OAI_RepresentationTheory_Saxl_CyclicSector
import Definitions.Def_OAI_RepresentationTheory_Saxl_BandSupport
import Definitions.Def_OAI_RepresentationTheory_Saxl_ShapeRigidity
import Definitions.Def_OAI_RepresentationTheory_Saxl_SpechtClassification
import Theorems.Thm_OAI_Saxl_columnAlt_collision
import Theorems.Thm_OAI_Saxl_polytabloid_rowWord
import Theorems.Thm_OAI_Saxl_specht_irreducible

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

/- Every nonzero vector in the genuine complex Specht cyclic subspace
again generates that whole subspace. -/
/- Inclusion of a subrepresentation of a subrepresentation into the ambient space. -/
/- The complex polytabloid module is irreducible. -/
end Saxl

end

end OAI

-- ---- from OAI.RepresentationTheory.Saxl.ShapeRigidity ----
namespace OAI

noncomputable section

open scoped TensorProduct

universe uX uV uW

namespace Saxl

/- Zero-based row-index statistic of a partition. -/
lemma columnAlt_polytabloid_ne_zero {n : ℕ} {μ : YoungDiagram} (t : Tableau n μ) :
    columnAlt t (polytabloid t) ≠ 0 := by
  intro hz
  have h := congrFun hz (rowWord t)
  rw [columnAlt_coefficient] at h
  change dotProduct (polytabloid t) (polytabloid t) = 0 at h
  conv at h => lhs; rhs; rw [← polytabloid_real t]
  let : PartialOrder ℂ := RCLike.toPartialOrder
  let : StarOrderedRing ℂ := RCLike.toStarOrderedRing
  exact polytabloid_ne_zero t (dotProduct_self_star_eq_zero.mp h)

/- The column operator on any genuine representation of the same group. -/
lemma columnOperator_intertwining {n : ℕ} {μ : YoungDiagram} (t : Tableau n μ)
    {V : Type uV} {W : Type uW} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {ρ : Representation ℂ (Equiv.Perm (Fin n)) V}
    {σ : Representation ℂ (Equiv.Perm (Fin n)) W}
    (f : Representation.IntertwiningMap ρ σ) (x : V) :
    f (columnOperator t ρ x) = columnOperator t σ (f x) := by
  classical
  simp only [columnOperator, LinearMap.sum_apply, LinearMap.smul_apply,
    map_sum, map_smul, Representation.IntertwiningMap.isIntertwining]

lemma columnOperator_subtype {n d : ℕ} {μ : YoungDiagram} (t : Tableau n μ)
    (S : Subrepresentation (wordRep n d)) (x : S.toSubmodule) :
    (columnOperator t S.toRepresentation x).val = columnAlt t x.val := by
  let inc : Representation.IntertwiningMap S.toRepresentation (wordRep n d) :=
    { toLinearMap := S.toSubmodule.subtype
      isIntertwining' := fun g => rfl }
  exact columnOperator_intertwining t inc x

/- Distinct genuine complex Specht shapes are inequivalent. -/
end Saxl

end

end OAI

-- ---- from OAI.RepresentationTheory.Saxl.SpechtClassification ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section

open scoped TensorProduct

universe uV uG

namespace Saxl

/- Rows enumerate exactly the actual cells, including the empty diagram. -/
/- Conversion from Mathlib's partition type to its Young diagram. -/
/- Cycle-type partition, with only the definitional `card (Fin n)=n` transport. -/
/- Class functions on the symmetric group, indexed by cycle type. -/
/- Select one representative where a cycle partition is realized; unused
coordinates are zero. This gives an injection even without surjectivity of
cycle-type realization. -/
/- Character of the actual Specht module as an actual class function. -/
/- Bilinear character scalar product used by the finite-group orthogonality theorem. -/
lemma columnAlt_eq_zero_of_rows {n d : ℕ} {μ : YoungDiagram} (t : Tableau n μ)
    (hd : d < μ.colLen 0) : columnAlt (d := d) t = 0 := by
  classical
  have hz : ∀ a : Fin n → Fin d, columnAlt t (Pi.single a (1 : ℂ)) = 0 := by
    intro a
    let j : Fin (μ.colLen 0) → Fin n := fun i => t.symm
      ⟨(i.val, 0), YoungDiagram.mem_iff_lt_colLen.mpr i.isLt⟩
    have hnot : ¬ Function.Injective (a ∘ j) := by
      intro hi
      have hh := Fintype.card_le_of_injective _ hi
      simp only [Fintype.card_fin] at hh
      omega
    simp only [Function.Injective] at hnot
    push Not at hnot
    obtain ⟨i, k, ha, hik⟩ := hnot
    have hj : j i ≠ j k := by
      intro he
      apply hik
      apply Fin.ext
      have hh := congrArg (fun l => (t l).val.1) he
      simpa [j] using hh
    exact columnAlt_collision t a (j i) (j k) hj (by simp [j]) ha
  apply LinearMap.ext
  intro x
  have he : x = ∑ a, x a • Pi.single a (1 : ℂ) := by
    ext b
    simp [Pi.single_apply]
  rw [he, map_sum]
  simp only [map_smul, hz, smul_zero, Finset.sum_const_zero, LinearMap.zero_apply]

/- A Specht constituent of a `d`-letter position representation has at most
`d` rows, proved by the genuine first-column antisymmetrizer. -/
theorem specht_rows_of_hom {n d : ℕ} {μ : YoungDiagram} (t : Tableau n μ)
    (f : Representation.IntertwiningMap (spechtRep t) (wordRep n d)) (hf : f ≠ 0) :
    μ.colLen 0 ≤ d := by
  classical
  let := specht_irreducible t
  have hi := (Representation.IsIrreducible.injective_or_eq_zero f).resolve_right hf
  by_contra h
  have hd : d < μ.colLen 0 := lt_of_not_ge h
  let p : Specht t := ⟨polytabloid t, mem_cyclic _ _⟩
  have he := columnOperator_intertwining t f p
  change f (columnOperator t (spechtRep t) p) = columnAlt t (f p) at he
  rw [columnAlt_eq_zero_of_rows t hd, LinearMap.zero_apply] at he
  have hz : columnOperator t (spechtRep t) p = 0 := hi (he.trans (map_zero f).symm)
  exact columnAlt_polytabloid_ne_zero t
    ((columnOperator_subtype t (spechtSub t) p).symm.trans (congrArg Subtype.val hz))

end Saxl

end

end OAI

-- ---- platform node ----
open OAI OAI.Saxl
open scoped TensorProduct


theorem solution : type_of% @_root_.OAI.Saxl.specht_rows_of_hom := @_root_.OAI.Saxl.specht_rows_of_hom
