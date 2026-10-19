-- Prove2me | solution 1 for OAI.Saxl.dominated_support
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T02:30:42.056599+00:00
-- url     : https://prove2.me/submissions/206b9c3a-485c-43d6-b689-4d7420d58ed1

-- Generated from openai/math@1581d4c lean/OAI/RepresentationTheory/Saxl/DominatedSupport.lean:L158-L208
-- (upload_full_project.md Phase 4): solution for node OAI.Saxl.dominated_support. The node keeps its source
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
import Definitions.Def_OAI_RepresentationTheory_Saxl_SupportSeparation
import Definitions.Def_OAI_RepresentationTheory_Saxl_PositionTensor
import Definitions.Def_OAI_RepresentationTheory_Saxl_BandOrbit
import Definitions.Def_OAI_RepresentationTheory_Saxl_BandGlue
import Definitions.Def_OAI_RepresentationTheory_Saxl_SignEquivalence
import Definitions.Def_OAI_RepresentationTheory_Saxl_PieriRestriction
import Definitions.Def_OAI_RepresentationTheory_Saxl_StripExtension
import Definitions.Def_OAI_RepresentationTheory_Saxl_SizedStrips
import Definitions.Def_OAI_RepresentationTheory_Saxl_HorizontalRemoval
import Definitions.Def_OAI_RepresentationTheory_Saxl_YoungRule
import Definitions.Def_OAI_RepresentationTheory_Saxl_CyclicTensor
import Definitions.Def_OAI_RepresentationTheory_Saxl_RepeatedProjection
import Definitions.Def_OAI_RepresentationTheory_Saxl_StaircaseSign
import Definitions.Def_OAI_RepresentationTheory_Saxl_DominatedQuotient
import Definitions.Def_OAI_RepresentationTheory_Saxl_DominatedSupport
import Theorems.Thm_OAI_Saxl_colTruncate_rowLen
import Theorems.Thm_OAI_Saxl_polytabloid_rowWord
import Theorems.Thm_OAI_Saxl_repeatedTarget_in_quotient
import Theorems.Thm_OAI_Saxl_specht_irreducible
import Theorems.Thm_OAI_Saxl_specht_sign_transpose
import Theorems.Thm_OAI_Saxl_staircase_sign_equiv
import Theorems.Thm_OAI_Saxl_young_orbit_map

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

-- ---- from OAI.RepresentationTheory.Saxl.CyclicSector ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section

open scoped TensorProduct

universe uG uX uY uZ uV

namespace Saxl

/- Explicit finite-group induction on a linear map. -/
/- Coordinate-sector induction, in precisely the nonzero-Hom form used in
the staircase induction. The projector kills translates outside the stabilizer. -/
open scoped MonoidAlgebra

theorem intertwining_lift_surjective {G : Type uG} {X : Type uX} {Y : Type uY} {Z : Type uZ}
    [Group G] [Finite G] [AddCommGroup X] [Module ℂ X]
    [AddCommGroup Y] [Module ℂ Y] [AddCommGroup Z] [Module ℂ Z]
    {ρ : Representation ℂ G X} {σ : Representation ℂ G Y}
    {τ : Representation ℂ G Z}
    (F : Representation.IntertwiningMap ρ σ) (hF : Function.Surjective F)
    (f : Representation.IntertwiningMap τ σ) :
    ∃ h : Representation.IntertwiningMap τ ρ, F.comp h = f := by
  let EF := Representation.IntertwiningMap.equivLinearMapAsModule ρ σ
  let EH := Representation.IntertwiningMap.equivLinearMapAsModule τ ρ
  let Ef := Representation.IntertwiningMap.equivLinearMapAsModule τ σ
  obtain ⟨h, hh⟩ := IsSemisimpleModule.lifting_property (EF F) hF (Ef f)
  refine ⟨EH.symm h, ?_⟩
  ext z
  exact LinearMap.congr_fun hh z

end Saxl

namespace Saxl

/- Concrete sector averaging produces a constituent of the full cyclic
module from an equivariant map on its coordinate sector. -/
/- A genuine equivariant projection of a cyclic generator transfers every
nonzero constituent map back to the original cyclic module by Maschke. -/
end Saxl

end

end OAI

-- ---- from OAI.RepresentationTheory.Saxl.HorizontalRemoval ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e

namespace OAI

noncomputable section

open scoped TensorProduct

namespace Saxl
lemma rowLen_zero_of_height_le (μ : YoungDiagram) {i : ℕ} (hi : μ.colLen 0 ≤ i) :
    μ.rowLen i = 0 := by
  apply Nat.eq_zero_of_not_pos
  intro h
  have hm := YoungDiagram.mem_iff_lt_rowLen.mpr h
  have hh := YoungDiagram.mem_iff_lt_colLen.mp hm
  omega

lemma rowPrefix_eq_card (μ : YoungDiagram) {k : ℕ} (hk : μ.colLen 0 ≤ k) :
    rowPrefix μ k = μ.card := by
  have he : μ.card = ∑ i : Fin (μ.colLen 0), μ.rowLen i := by
    have hh := Fintype.card_congr (rowCellEquiv μ)
    simpa using hh
  rw [he, Fin.sum_univ_eq_sum_range]
  symm
  apply Finset.sum_subset (Finset.range_mono hk)
  intro i hik hin
  exact rowLen_zero_of_height_le μ (by simpa using hin)

/- Tallest-column bottom deletion, expressed by interlacing rows. -/
lemma rowTruncate_rowLen (μ : YoungDiagram) (k i : ℕ) :
    (rowTruncate μ k).rowLen i = if i < k then μ.rowLen i else 0 := by
  have hh : ∀ j, j < (rowTruncate μ k).rowLen i ↔ j < if i < k then μ.rowLen i else 0 := by
    intro j
    rw [← YoungDiagram.mem_iff_lt_rowLen, mem_rowTruncate, YoungDiagram.mem_iff_lt_rowLen]
    split_ifs <;> simp_all
  have h₁ := hh ((rowTruncate μ k).rowLen i)
  have h₂ := hh (if i < k then μ.rowLen i else 0)
  omega

lemma rowTruncate_height (μ : YoungDiagram) (k : ℕ) : (rowTruncate μ k).colLen 0 ≤ k := by
  by_contra h
  have hm : (k,0) ∈ rowTruncate μ k := YoungDiagram.mem_iff_lt_colLen.mpr (by omega)
  exact Nat.lt_irrefl k (mem_rowTruncate.mp hm).2

lemma rowTruncate_prefix (μ : YoungDiagram) (k q : ℕ) (hq : q ≤ k) :
    rowPrefix (rowTruncate μ k) q = rowPrefix μ q := by
  apply Finset.sum_congr rfl
  intro i hi
  rw [rowTruncate_rowLen, ite_eq_left (lt_of_lt_of_le (Finset.mem_range.mp hi) hq)]

lemma rowTruncate_card (μ : YoungDiagram) (k : ℕ) :
    (rowTruncate μ k).card = rowPrefix μ k := by
  rw [← rowPrefix_eq_card _ (rowTruncate_height μ k), rowTruncate_prefix _ _ _ le_rfl]

end Saxl

end

end OAI

-- ---- from OAI.RepresentationTheory.Saxl.DominatedSupport ----
namespace OAI

noncomputable section

open scoped TensorProduct

universe uX uY

namespace Saxl

lemma transpose_card (μ : YoungDiagram) : μ.transpose.card = μ.card := by
  change ((Equiv.prodComm ℕ ℕ).finsetCongr μ.cells).card = μ.cells.card
  simp only [Equiv.finsetCongr_apply, Finset.card_map]

lemma colTruncate_height (μ : YoungDiagram) (k : ℕ) :
    (colTruncate μ k).colLen 0 ≤ μ.colLen 0 := by
  by_contra h
  have hm : (μ.colLen 0,0) ∈ colTruncate μ k := YoungDiagram.mem_iff_lt_colLen.mpr (by omega)
  have hr := YoungDiagram.mem_iff_lt_rowLen.mp hm
  rw [colTruncate_rowLen, rowLen_zero_of_height_le μ le_rfl] at hr
  simp at hr

lemma sum_range_if_lt (f : ℕ → ℕ) {r H : ℕ} (hr : r ≤ H) :
    (∑ i ∈ Finset.range H, if i < r then f i else 0) = ∑ i ∈ Finset.range r, f i := by
  classical
  rw [← Finset.sum_filter]
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_range]
  omega

lemma corner_inequality (μ : YoungDiagram) (k r : ℕ) :
    rowPrefix μ.transpose k + rowPrefix μ r ≤ μ.card + r*k := by
  let H := max (μ.colLen 0) r
  have hh : μ.colLen 0 ≤ H := Nat.le_max_left _ _
  have hr : r ≤ H := Nat.le_max_right _ _
  have hm : rowPrefix μ.transpose k = ∑ i ∈ Finset.range H, min k (μ.rowLen i) := by
    rw [← rowTruncate_card, ← transpose_card (rowTruncate μ.transpose k)]
    change (colTruncate μ k).card = _
    rw [← rowPrefix_eq_card _ ((colTruncate_height μ k).trans hh)]
    exact Finset.sum_congr rfl (fun i _ => colTruncate_rowLen μ k i)
  rw [hm, ← rowPrefix_eq_card μ hh]
  change _ + (∑ i ∈ Finset.range r, μ.rowLen i) ≤ (∑ i ∈ Finset.range H, μ.rowLen i) + r*k
  have hconst : (∑ i ∈ Finset.range r, k) = r*k := by simp
  rw [← hconst, ← sum_range_if_lt μ.rowLen hr, ← sum_range_if_lt (fun _ => k) hr,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i hi
  split_ifs <;> omega

lemma corner_equality (μ : YoungDiagram) (k : ℕ) :
    rowPrefix μ.transpose k + rowPrefix μ (μ.colLen k) = μ.card + μ.colLen k*k := by
  let r := μ.colLen k
  let H := μ.colLen 0
  have hr : r ≤ H := μ.colLen_anti 0 k (Nat.zero_le _)
  have hm : rowPrefix μ.transpose k = ∑ i ∈ Finset.range H, min k (μ.rowLen i) := by
    rw [← rowTruncate_card, ← transpose_card (rowTruncate μ.transpose k)]
    change (colTruncate μ k).card = _
    rw [← rowPrefix_eq_card _ (colTruncate_height μ k)]
    exact Finset.sum_congr rfl (fun i _ => colTruncate_rowLen μ k i)
  change rowPrefix μ.transpose k + rowPrefix μ r = μ.card + r*k
  rw [hm, ← rowPrefix_eq_card μ (le_refl H)]
  change _ + (∑ i ∈ Finset.range r, μ.rowLen i) = (∑ i ∈ Finset.range H, μ.rowLen i) + r*k
  have hconst : (∑ i ∈ Finset.range r, k) = r*k := by simp
  rw [← hconst, ← sum_range_if_lt μ.rowLen hr, ← sum_range_if_lt (fun _ => k) hr,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  have he : i < r ↔ k < μ.rowLen i := by
    exact YoungDiagram.mem_iff_lt_colLen.symm.trans YoungDiagram.mem_iff_lt_rowLen
  split_ifs with h
  · have hh := he.mp h
    omega
  · have hh := not_congr he |>.mp h
    omega

/- Ordinary conjugation reverses dominance, including empty diagrams. -/
theorem dominates_transpose {μ ν : YoungDiagram} (hc : μ.card = ν.card)
    (h : Dominates μ ν) : Dominates ν.transpose μ.transpose := by
  intro k
  have h₁ := corner_inequality μ k (ν.colLen k)
  have h₂ := corner_equality ν k
  have h₃ := h (ν.colLen k)
  omega

open scoped MonoidAlgebra

end Saxl

namespace Saxl

lemma rowWord_content {n : ℕ} {μ : YoungDiagram} (t : Tableau n μ)
    (j : Fin (μ.colLen 0)) :
    (Finset.univ.filter (fun i => rowWord t i = j)).card = μ.rowLen j := by
  classical
  let e : {i // rowWord t i = j} ≃ Fin (μ.rowLen j) :=
    { toFun := fun i => ⟨(t i.val).val.2, by
        have hh := YoungDiagram.mem_iff_lt_rowLen.mp (t i.val).property
        have hj := congrArg Fin.val i.property
        change (t i.val).val.1 = j.val at hj
        simpa only [hj] using hh⟩
      invFun := fun k => ⟨t.symm ⟨(j.val,k.val), YoungDiagram.mem_iff_lt_rowLen.mpr k.isLt⟩,
        by apply Fin.ext; change (t (t.symm _)).val.1 = _; simp only [Equiv.apply_symm_apply]⟩
      left_inv := by
        intro i
        apply Subtype.ext
        apply t.injective
        simp only [Equiv.apply_symm_apply]
        apply Subtype.ext
        apply Prod.ext
        · exact (congrArg Fin.val i.property).symm
        · rfl
      right_inv := by intro k; apply Fin.ext; simp only [Equiv.apply_symm_apply] }
  simpa only [Fintype.card_subtype, Fintype.card_fin] using Fintype.card_congr e

theorem dominated_support (m : ℕ) (_hm : 1 ≤ m) (μ : YoungDiagram)
    (t : Tableau (staircase m).card μ) (hμ : Dominates (staircase m) μ) :
    ∃ f : Representation.IntertwiningMap (spechtRep t)
      (staircaseCyclic m).toRepresentation, f ≠ 0 := by
  classical
  have hc : μ.card = (staircase m).card := by
    simpa only [Fintype.card_fin, Fintype.card_coe] using (Fintype.card_congr t).symm
  have ht : μ.transpose.card = (staircase m).card := by rw [transpose_card, hc]
  have hd : Dominates μ.transpose (staircase m) := by
    simpa only [staircase_transpose] using dominates_transpose hc.symm hμ
  have hw (j : Fin ((staircase m).colLen 0)) :
      (Finset.univ.filter (fun i => repeatedTarget m i = Fin.rev j)).card = (staircase m).rowLen j := by
    simpa only [repeatedTarget, Fin.rev_inj] using rowWord_content (stairTableau m) j
  obtain ⟨F,hF⟩ := young_orbit_map (staircase m) μ.transpose (transposeTableau t)
    ht hd (repeatedTarget m) Fin.revPerm hw
  obtain ⟨φ⟩ := staircase_sign_equiv m
  let Q := F.comp (dominatedQuotient m φ)
  have hQ : Q ≠ 0 := by
    obtain ⟨x,hx⟩ := repeatedTarget_in_quotient m φ
    intro hz
    apply hF
    have hh := congrArg (fun l => l x) hz
    change F (dominatedQuotient m φ x) = 0 at hh
    change dominatedQuotient m φ x = Pi.single (repeatedTarget m) 1 at hx
    rwa [hx] at hh
  obtain ⟨E⟩ := specht_sign_transpose t
  let R := E.symm.toIntertwiningMap.comp (signCancelMap Q)
  have hR : R ≠ 0 := by
    intro hz
    apply hQ
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro x
    have hh := congrArg (fun l => l x) hz
    change E.symm (Q x) = 0 at hh
    exact E.symm.injective (hh.trans (map_zero _).symm)
  let := specht_irreducible t
  have hRs : Function.Surjective R :=
    (Representation.IsIrreducible.surjective_or_eq_zero R).resolve_right hR
  obtain ⟨f,hf⟩ := intertwining_lift_surjective R hRs (Representation.IntertwiningMap.id (spechtRep t))
  refine ⟨f, ?_⟩
  intro hz
  have hzero : (Representation.IntertwiningMap.id (spechtRep t)) = 0 := by
    rw [← hf, hz]
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro x
    exact map_zero R
  have he := congrArg (fun l : Representation.IntertwiningMap (spechtRep t) (spechtRep t) =>
    l ⟨polytabloid t, mem_cyclic _ _⟩) hzero
  exact polytabloid_ne_zero t (congrArg Subtype.val he)

end Saxl

end

end OAI

-- ---- platform node ----
open OAI OAI.Saxl
open scoped TensorProduct


theorem solution : type_of% @_root_.OAI.Saxl.dominated_support := @_root_.OAI.Saxl.dominated_support
