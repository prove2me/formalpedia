-- Prove2me | solution 2 for OAI.Saxl.signEquiv_rowAverage
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T02:22:55.28012+00:00
-- url     : https://prove2.me/submissions/90b38500-f3f9-4110-9210-5e2cc3c0199f

-- Generated from openai/math@1581d4c lean/OAI/RepresentationTheory/Saxl/StaircaseSign.lean:L212-L229
-- (upload_full_project.md Phase 4): solution for node OAI.Saxl.signEquiv_rowAverage. The node keeps its source
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
/- Every nonzero vector in the genuine complex Specht cyclic subspace
again generates that whole subspace. -/
/- Inclusion of a subrepresentation of a subrepresentation into the ambient space. -/
/- The complex polytabloid module is irreducible. -/
end Saxl

end

end OAI

-- ---- from OAI.RepresentationTheory.Saxl.StaircaseSign ----
namespace OAI

noncomputable section

open scoped TensorProduct

universe uX uY uZ

namespace Saxl

lemma alternating_specht_line {n : ℕ} {μ : YoungDiagram} (t : Tableau n μ)
    (y : Specht t) (hy : ∀ g : columnGroup t,
      spechtRep t g.val y = signC g.val • y) :
    ∃ c : ℂ, y.val = c • polytabloid t := by
  classical
  let := Fintype.ofFinite (columnGroup t)
  have he : columnAlt t y.val = (Fintype.card (columnGroup t) : ℂ) • y.val := by
    change (∑ g : columnGroup t, signC g.val • wordRep n (μ.colLen 0) g.val) y.val = _
    simp only [LinearMap.sum_apply, LinearMap.smul_apply]
    have hh (g : columnGroup t) : wordRep n (μ.colLen 0) g.val y.val = signC g.val • y.val :=
      congrArg Subtype.val (hy g)
    simp only [hh, smul_smul, signC_mul_self, one_smul, Finset.sum_const,
      Finset.card_univ, Nat.cast_smul_eq_nsmul]
  have hm := columnAlt_tabloid t (spechtSub_le_tabloidSub t y.property)
  rw [he] at hm
  have hc : (Fintype.card (columnGroup t) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hx : y.val ∈ Submodule.span ℂ {polytabloid t} :=
    (Submodule.smul_mem_iff _ hc).mp hm
  obtain ⟨c,hc⟩ := Submodule.mem_span_singleton.mp hx
  exact ⟨c,hc.symm⟩

lemma rowAverage_nonzero (m : ℕ) : rowAverage m ≠ 0 := by
  classical
  let := Fintype.ofFinite (columnGroup (stairRowTableau m))
  intro he
  have hh := congrArg (fun y : Specht (stairTableau m) => y.val (rowWord (stairTableau m))) he
  have hg (g : columnGroup (stairRowTableau m)) :
      rowWord (stairTableau m) ∘ g.val = rowWord (stairTableau m) := by
    funext i
    apply Fin.ext
    exact g.property i
  simp only [rowAverage, Submodule.coe_sum, Finset.sum_apply] at hh
  change (∑ g : columnGroup (stairRowTableau m),
    polytabloid (stairTableau m) (rowWord (stairTableau m) ∘ g.val)) = 0 at hh
  simp only [hg, polytabloid_rowWord, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] at hh
  exact Nat.cast_ne_zero.mpr Fintype.card_ne_zero hh

lemma rowAverage_fixed (m : ℕ) (g : columnGroup (stairRowTableau m)) :
    spechtRep (stairTableau m) g.val (rowAverage m) = rowAverage m := by
  classical
  let := Fintype.ofFinite (columnGroup (stairRowTableau m))
  unfold rowAverage
  rw [map_sum]
  simp only [← Module.End.mul_apply, ← map_mul]
  exact Equiv.sum_comp (Equiv.mulLeft g) (fun h : columnGroup (stairRowTableau m) =>
    spechtRep (stairTableau m) h.val ⟨polytabloid (stairTableau m), mem_cyclic _ _⟩)

lemma signEquiv_rowAverage (m : ℕ)
    (φ : (spechtRep (stairTableau m)).Equiv (signTwist (spechtRep (stairRowTableau m)))) :
    ∃ c : ℂ, c ≠ 0 ∧ (φ (rowAverage m)).val = c • polytabloid (stairRowTableau m) := by
  have ha (g : columnGroup (stairRowTableau m)) :
      spechtRep (stairRowTableau m) g.val (φ (rowAverage m)) = signC g.val • φ (rowAverage m) := by
    have he := LinearMap.congr_fun (φ.isIntertwining' g.val) (rowAverage m)
    change φ (spechtRep (stairTableau m) g.val (rowAverage m)) =
      signC g.val • spechtRep (stairRowTableau m) g.val (φ (rowAverage m)) at he
    rw [rowAverage_fixed] at he
    have hh := congrArg (fun x => signC g.val • x) he
    simpa only [smul_smul, signC_mul_self, one_smul] using hh.symm
  obtain ⟨c,hc⟩ := alternating_specht_line (stairRowTableau m) (φ (rowAverage m)) ha
  refine ⟨c, ?_, hc⟩
  intro hz
  rw [hz, zero_smul] at hc
  apply rowAverage_nonzero m
  apply φ.injective
  exact (Subtype.ext hc).trans (map_zero φ).symm

/- A sign intertwiner in the second factor twists the diagonal product. -/
end Saxl

end

end OAI

-- ---- platform node ----
open OAI OAI.Saxl
open scoped TensorProduct


theorem solution : type_of% @_root_.OAI.Saxl.signEquiv_rowAverage := @_root_.OAI.Saxl.signEquiv_rowAverage
