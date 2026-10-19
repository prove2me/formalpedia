-- Prove2me | solution 1 for OAI.Saxl.irreducible_equiv_specht
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T01:28:39.719978+00:00
-- url     : https://prove2.me/submissions/86d56056-b2a9-4630-9a98-ab4ce43d33bb

-- Generated from openai/math@1581d4c lean/OAI/RepresentationTheory/Saxl/SpechtClassification.lean:L175-L201
-- (upload_full_project.md Phase 4): solution for node OAI.Saxl.irreducible_equiv_specht. The node keeps its source
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
import Theorems.Thm_OAI_Saxl_finset_eq_of_signed_sum
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

lemma tableau_image {n : ℕ} {μ : YoungDiagram} (t : Tableau n μ) :
    Finset.univ.image (fun i : Fin n => (t i).val) = μ.cells := by
  classical
  ext x
  simp only [Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨i, rfl⟩; exact (t i).property
  · intro hx; exact ⟨t.symm ⟨x, hx⟩, by simp⟩

lemma tableau_sum {n : ℕ} {μ : YoungDiagram} (t : Tableau n μ) (f : ℕ × ℕ → ℤ) :
    ∑ i, f (t i).val = ∑ c ∈ μ.cells, f c := by
  classical
  conv_rhs => rw [← tableau_image t]
  rw [Finset.sum_image]
  intro i hi j hj h
  exact t.injective (Subtype.val_injective h)

/- Zero-based row-index statistic of a partition. -/
lemma finset_signed_sum_le {X : Type uX} [DecidableEq X]
    (A B : Finset X) (w : X → ℤ)
    (hp : ∀ x ∈ B, 0 ≤ w x) (hn : ∀ x ∉ B, w x ≤ 0) :
    ∑ x ∈ A, w x ≤ ∑ x ∈ B, w x := by
  classical
  have hle : ∀ x ∈ A ∪ B,
      (if x ∈ A then w x else 0) ≤ (if x ∈ B then w x else 0) := by
    intro x hx
    split_ifs with ha hb hb
    · rfl
    · exact hn x hb
    · exact hp x hb
    · rfl
  simpa [← Finset.sum_filter] using Finset.sum_le_sum hle

lemma mixed_moment_le {n : ℕ} {μ ν : YoungDiagram}
    (t : Tableau n μ) (u : Tableau n ν) (g : Equiv.Perm (Fin n))
    (hi : Function.Injective (fun i => ((u (g i)).val.1, (t i).val.2))) :
    rowMoment μ ≤ rowMoment ν := by
  classical
  let f : Fin n → ℕ × ℕ := fun i => ((u (g i)).val.1, (t i).val.2)
  let w : ℕ × ℕ → ℤ := fun c => 2 * (μ.colLen c.2 : ℤ) - 2 * c.1 - 1
  have h := finset_signed_sum_le (Finset.univ.image f) μ.cells w
    (fun c hc => by have hh := YoungDiagram.mem_iff_lt_colLen.mp hc; dsimp [w]; omega)
    (fun c hc => by
      have hh : μ.colLen c.2 ≤ c.1 :=
        le_of_not_gt (fun h => hc (YoungDiagram.mem_iff_lt_colLen.mpr h))
      dsimp [w]; omega)
  rw [Finset.sum_image (fun _ _ _ _ h => hi h), ← tableau_sum t w] at h
  simp only [w, Finset.sum_sub_distrib, ← Finset.mul_sum] at h
  rw [Equiv.sum_comp g (fun i => ((u i).val.1 : ℤ))] at h
  have ht := tableau_sum t (fun c => (c.1 : ℤ))
  have hu := tableau_sum u (fun c => (c.1 : ℤ))
  change _ = rowMoment μ at ht
  change _ = rowMoment ν at hu
  omega

lemma mixed_support_eq {n : ℕ} {μ ν : YoungDiagram}
    (t : Tableau n μ) (u : Tableau n ν) (g : Equiv.Perm (Fin n))
    (hi : Function.Injective (fun i => ((u (g i)).val.1, (t i).val.2)))
    (hm : rowMoment μ = rowMoment ν) :
    Finset.univ.image (fun i => ((u (g i)).val.1, (t i).val.2)) = μ.cells := by
  classical
  let f : Fin n → ℕ × ℕ := fun i => ((u (g i)).val.1, (t i).val.2)
  let w : ℕ × ℕ → ℤ := fun c => 2 * (μ.colLen c.2 : ℤ) - 2 * c.1 - 1
  apply finset_eq_of_signed_sum _ _ w
    (fun c hc => by have hh := YoungDiagram.mem_iff_lt_colLen.mp hc; dsimp [w]; omega)
    (fun c hc => by
      have hh : μ.colLen c.2 ≤ c.1 :=
        le_of_not_gt (fun h => hc (YoungDiagram.mem_iff_lt_colLen.mpr h))
      dsimp [w]; omega)
  rw [Finset.sum_image (fun _ _ _ _ h => hi h), ← tableau_sum t w]
  simp only [w, Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [Equiv.sum_comp g (fun i => ((u i).val.1 : ℤ))]
  have ht := tableau_sum t (fun c => (c.1 : ℤ))
  have hu := tableau_sum u (fun c => (c.1 : ℤ))
  change _ = rowMoment μ at ht
  change _ = rowMoment ν at hu
  rw [ht, hu, hm]

lemma rowLen_eq_count {n : ℕ} {μ : YoungDiagram} (t : Tableau n μ) (r : ℕ) :
    μ.rowLen r = (Finset.univ.filter (fun i => (t i).val.1 = r)).card := by
  classical
  rw [YoungDiagram.rowLen_eq_card]
  have hf : μ.row r = (Finset.univ.filter (fun i => (t i).val.1 = r)).image
      (fun i => (t i).val) := by
    unfold YoungDiagram.row
    conv_lhs => rw [← tableau_image t]
    rw [Finset.filter_image]
  rw [hf, Finset.card_image_iff.mpr]
  intro i hi j hj h
  exact t.injective (Subtype.val_injective h)

lemma shapes_eq_of_mixed {n : ℕ} {μ ν : YoungDiagram}
    (t : Tableau n μ) (u : Tableau n ν) (g : Equiv.Perm (Fin n))
    (hi : Function.Injective (fun i => ((u (g i)).val.1, (t i).val.2)))
    (hm : rowMoment μ = rowMoment ν) : μ = ν := by
  classical
  have hs := mixed_support_eq t u g hi hm
  have hrow : ∀ r, μ.rowLen r = ν.rowLen r := by
    intro r
    rw [YoungDiagram.rowLen_eq_card, YoungDiagram.row, ← hs,
      Finset.filter_image, Finset.card_image_iff.mpr (fun i _ j _ h => hi h),
      rowLen_eq_count u r]
    apply Finset.card_equiv g
    intro i
    simp
  apply YoungDiagram.ext
  ext c
  rcases c with ⟨r, s⟩
  change (r, s) ∈ μ ↔ (r, s) ∈ ν
  simp only [YoungDiagram.mem_iff_lt_rowLen, hrow]

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

lemma mixed_injective_of_columnAlt_ne_zero {n : ℕ} {μ ν : YoungDiagram}
    (t : Tableau n μ) (u : Tableau n ν)
    {x : WordSpace n (ν.colLen 0)} (hx : x ∈ tabloidSub u)
    (hz : columnAlt t x ≠ 0) :
    ∃ g : Equiv.Perm (Fin n),
      Function.Injective (fun i => ((u (g i)).val.1, (t i).val.2)) := by
  classical
  by_contra h
  push Not at h
  have hall : ∀ g : Equiv.Perm (Fin n),
      columnAlt t (wordRep n (ν.colLen 0) g (Pi.single (rowWord u) 1)) = 0 := by
    intro g
    have hh := h g⁻¹
    simp only [Function.Injective] at hh
    push Not at hh
    obtain ⟨i, j, he, hij⟩ := hh
    rw [wordRep_single]
    exact columnAlt_collision t _ i j hij (Prod.mk.inj he).2
      (Fin.ext (Prod.mk.inj he).1)
  apply hz
  clear hz
  induction hx using Submodule.span_induction with
  | mem y hy => obtain ⟨g, rfl⟩ := hy; exact hall g
  | zero => exact map_zero _
  | add y z hy hz ihy ihz => rw [map_add, ihy, ihz, add_zero]
  | smul c y hy ih => rw [map_smul, ih, smul_zero]

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

lemma mixed_injective_of_equiv {n : ℕ} {μ ν : YoungDiagram}
    (t : Tableau n μ) (u : Tableau n ν)
    (e : Representation.Equiv (spechtRep t) (spechtRep u)) :
    ∃ g : Equiv.Perm (Fin n),
      Function.Injective (fun i => ((u (g i)).val.1, (t i).val.2)) := by
  let p : Specht t := ⟨polytabloid t, mem_cyclic _ _⟩
  apply mixed_injective_of_columnAlt_ne_zero t u
    (spechtSub_le_tabloidSub u (e p).property)
  intro hz
  have he := columnOperator_intertwining t e.toIntertwiningMap p
  have hy : columnOperator t (spechtRep u) (e p) = 0 := by
    apply Subtype.ext
    exact (columnOperator_subtype t (spechtSub u) (e p)).trans hz
  change e (columnOperator t (spechtRep t) p) = columnOperator t (spechtRep u) (e p) at he
  rw [hy] at he
  have ht : columnOperator t (spechtRep t) p = 0 := e.injective (he.trans (map_zero e).symm)
  have hh := congrArg Subtype.val ht
  exact columnAlt_polytabloid_ne_zero t
    ((columnOperator_subtype t (spechtSub t) p).symm.trans hh)

/- Distinct genuine complex Specht shapes are inequivalent. -/
theorem specht_shape_rigidity {n : ℕ} {μ ν : YoungDiagram}
    (t : Tableau n μ) (u : Tableau n ν)
    (e : Representation.Equiv (spechtRep t) (spechtRep u)) : μ = ν := by
  obtain ⟨g, hg⟩ := mixed_injective_of_equiv t u e
  obtain ⟨h, hh⟩ := mixed_injective_of_equiv u t e.symm
  exact shapes_eq_of_mixed t u g hg
    (le_antisymm (mixed_moment_le t u g hg) (mixed_moment_le u t h hh))

end Saxl

end

end OAI

-- ---- from OAI.RepresentationTheory.Saxl.SpechtClassification ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e
private theorem dite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α} {e : ¬c → α} : (dite c t e) = t hc := @dif_pos c h hc α t e

namespace OAI

noncomputable section

open scoped TensorProduct

universe uV uG

namespace Saxl

/- Rows enumerate exactly the actual cells, including the empty diagram. -/
/- Conversion from Mathlib's partition type to its Young diagram. -/
lemma partitionDiagram_injective {n : ℕ} :
    Function.Injective (partitionDiagram (n := n)) := by
  intro p q h
  apply Nat.Partition.ext
  have he := congrArg (fun μ => (μ.rowLens : Multiset ℕ)) h
  simpa only [partitionDiagram_rowLens, Multiset.sort_eq] using he

/- Cycle-type partition, with only the definitional `card (Fin n)=n` transport. -/
/- Class functions on the symmetric group, indexed by cycle type. -/
/- Select one representative where a cycle partition is realized; unused
coordinates are zero. This gives an injection even without surjectivity of
cycle-type realization. -/
lemma classEvaluation_injective (n : ℕ) : Function.Injective (classEvaluation n) := by
  intro f h he
  apply Subtype.ext
  funext g
  have hh := congrFun he (permPartition g)
  have hex : ∃ k : Equiv.Perm (Fin n), permPartition k = permPartition g := ⟨g, rfl⟩
  change (if hc : ∃ k : Equiv.Perm (Fin n), permPartition k = permPartition g then
    f.val hc.choose else 0) = (if hc : ∃ k : Equiv.Perm (Fin n), permPartition k = permPartition g then
    h.val hc.choose else 0) at hh
  rw [dite_eq_left hex, dite_eq_left hex] at hh
  exact (f.property _ _ hex.choose_spec).symm.trans (hh.trans (h.property _ _ hex.choose_spec))

lemma classFunctions_finrank_le (n : ℕ) :
    Module.finrank ℂ (classFunctions n) ≤ Fintype.card (Nat.Partition n) := by
  have h := LinearMap.finrank_le_finrank_of_injective (classEvaluation_injective n)
  simpa using h

/- Character of the actual Specht module as an actual class function. -/
/- Bilinear character scalar product used by the finite-group orthogonality theorem. -/
lemma complex_card_ne_zero (G : Type uG) [Group G] [Fintype G] : (Nat.card G : ℂ) ≠ 0 := by
  exact_mod_cast Nat.card_pos.ne'

lemma spechtCharacter_orthonormal {n : ℕ} (p q : Nat.Partition n) :
    charFunctional (spechtCharacter q).val (spechtCharacter p).val = if p = q then 1 else 0 := by
  classical
  let : Invertible (Nat.card (Equiv.Perm (Fin n)) : ℂ) :=
    invertibleOfNonzero (complex_card_ne_zero _)
  let := specht_irreducible (partitionTableau p)
  let := specht_irreducible (partitionTableau q)
  have h := Representation.char_orthonormal (spechtRep (partitionTableau p))
    (spechtRep (partitionTableau q))
  change _ = _ at h
  have he : Nonempty ((spechtRep (partitionTableau q)).Equiv
      (spechtRep (partitionTableau p))) ↔ p = q := by
    constructor
    · rintro ⟨e⟩
      exact (partitionDiagram_injective
        (specht_shape_rigidity (partitionTableau q) (partitionTableau p) e)).symm
    · rintro rfl
      exact ⟨Representation.Equiv.refl _⟩
  simpa only [he, charFunctional, spechtCharacter, LinearMap.coe_mk, AddHom.coe_mk] using h

lemma spechtCharacter_linearIndependent (n : ℕ) :
    LinearIndependent ℂ (spechtCharacter (n := n)) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro c hc p
  have h := congrArg (fun f : classFunctions n => charFunctional (spechtCharacter p).val f.val) hc
  change charFunctional (spechtCharacter p).val
    ((classFunctions n).subtype (∑ i, c i • spechtCharacter i)) =
    charFunctional (spechtCharacter p).val ((classFunctions n).subtype 0) at h
  simp only [map_sum, map_smul, map_zero] at h
  change (∑ i, c i * charFunctional (spechtCharacter p).val (spechtCharacter i).val) = 0 at h
  simp_rw [spechtCharacter_orthonormal] at h
  simpa using h

lemma spechtCharacter_span (n : ℕ) :
    Submodule.span ℂ (Set.range (spechtCharacter (n := n))) = ⊤ := by
  apply (spechtCharacter_linearIndependent n).span_eq_top_of_card_eq_finrank'
  exact le_antisymm (spechtCharacter_linearIndependent n).fintype_card_le_finrank
    (classFunctions_finrank_le n)

theorem irreducible_equiv_specht {n : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]
    [Module.Finite ℂ V] (ρ : Representation ℂ (Equiv.Perm (Fin n)) V)
    [Representation.IsIrreducible ρ] :
    ∃ p : Nat.Partition n, Nonempty (ρ.Equiv (spechtRep (partitionTableau p))) := by
  classical
  let : Invertible (Nat.card (Equiv.Perm (Fin n)) : ℂ) :=
    invertibleOfNonzero (complex_card_ne_zero _)
  by_contra h
  push Not at h
  let f : (classFunctions n) →ₗ[ℂ] ℂ :=
    (charFunctional ρ.character).comp (classFunctions n).subtype
  have hf : ∀ p : Nat.Partition n, f (spechtCharacter p) = 0 := by
    intro p
    let := specht_irreducible (partitionTableau p)
    have hp := Representation.char_orthonormal (spechtRep (partitionTableau p)) ρ
    rw [ite_eq_right (fun he => (h p).false he.some)] at hp
    exact hp
  have hk : Submodule.span ℂ (Set.range (spechtCharacter (n := n))) ≤ LinearMap.ker f := by
    rw [Submodule.span_le]
    rintro _ ⟨p, rfl⟩
    exact hf p
  rw [spechtCharacter_span] at hk
  have hz := hk (show (⟨ρ.character, char_mem_classFunctions ρ⟩ : classFunctions n) ∈ ⊤ from trivial)
  change charFunctional ρ.character ρ.character = 0 at hz
  have hone := Representation.char_orthonormal ρ ρ
  rw [ite_eq_left ⟨Representation.Equiv.refl ρ⟩] at hone
  exact one_ne_zero (hone.symm.trans hz)

/- A Specht constituent of a `d`-letter position representation has at most
`d` rows, proved by the genuine first-column antisymmetrizer. -/
end Saxl

end

end OAI

-- ---- platform node ----
open OAI OAI.Saxl
open scoped TensorProduct


theorem solution.{uV} : type_of% @_root_.OAI.Saxl.irreducible_equiv_specht.{uV} := @_root_.OAI.Saxl.irreducible_equiv_specht.{uV}
