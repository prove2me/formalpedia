-- Prove2me | solution 1 for OAI.Saxl.pieri_strip_restriction
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T01:46:49.247988+00:00
-- url     : https://prove2.me/submissions/ce757984-4454-43aa-a790-9784b7e8c34e

-- Generated from openai/math@1581d4c lean/OAI/RepresentationTheory/Saxl/PieriRestriction.lean:L201-L222
-- (upload_full_project.md Phase 4): solution for node OAI.Saxl.pieri_strip_restriction. The node keeps its source
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
import Theorems.Thm_OAI_Saxl_wordRestrict_equivariant

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

/- Every nonzero vector in the genuine complex Specht cyclic subspace
again generates that whole subspace. -/
/- Inclusion of a subrepresentation of a subrepresentation into the ambient space. -/
/- The complex polytabloid module is irreducible. -/
end Saxl

end

end OAI

-- ---- from OAI.RepresentationTheory.Saxl.SpechtDuality ----
namespace OAI

noncomputable section

open scoped TensorProduct

namespace Saxl

/- The ordinary bilinear coordinate pairing restricted to any invariant word subspace. -/
/- Complex conjugation-stable invariant word subspaces are canonically self-dual
via bilinear evaluation, yielding equivariant projections. -/
/- Actual self-duality of every complex Specht representation. -/
/- Restriction of the ambient bilinear coordinate pairing to an invariant subspace. -/
/- The genuine equivariant orthogonal-coordinate projection. -/
lemma subrepProject_pair {n d : ℕ} (S : Subrepresentation (wordRep n d))
    (hS : ∀ x ∈ S.toSubmodule, star x ∈ S.toSubmodule)
    (x : WordSpace n d) (y : S.toSubmodule) :
    dotProduct (subrepProject S hS x).val y.val = dotProduct x y.val := by
  have hh := (subrepSelfDual S hS).apply_symm_apply (subrepPairFromAmbient S x)
  exact congrArg (fun f : Module.Dual ℂ S.toSubmodule => f y) hh

/- A tensor power of a single letter-linear map, in ordinary word coordinates. -/
/- A nonzero contraction with a real cyclic vector gives an actual nonzero
intertwiner into its cyclic representation. -/
end Saxl

end

end OAI

-- ---- from OAI.RepresentationTheory.Saxl.HighProjection ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
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
/- The projected generator is genuinely nonzero for every band width,
without assuming a tensor factorization. -/
end Saxl

end

end OAI

-- ---- from OAI.RepresentationTheory.Saxl.PieriRestriction ----
namespace OAI

noncomputable section

open scoped TensorProduct

namespace Saxl
/- A horizontal strip removes at most one cell in each column. -/
/- Position embedding induced by inclusion of the actual Young diagrams. -/
/- Restrict letters on a specified position set, and sum over all other letters.
This is precisely contraction with the all-ones functional at deleted positions. -/
lemma wordRestrict_single {a n d e : ℕ} (i : Fin a ↪ Fin n) (j : Fin d ↪ Fin e)
    (c : Fin n → Fin e) (b : Fin a → Fin d) :
    wordRestrict i j (Pi.single c 1) b = if c ∘ i = j ∘ b then 1 else 0 := by
  classical
  change (∑ z : Fin n → Fin e, if z ∘ i = j ∘ b then (Pi.single c (1 : ℂ) : WordSpace n e) z else 0) = _
  rw [Finset.sum_eq_single c]
  · simp
  · intro z hz hzc
    simp [hzc]
  · simp

lemma column_fixed_of_strip {a n : ℕ} {ν μ : YoungDiagram}
    (s : Tableau a ν) (t : Tableau n μ) (hs : HorizontalStrip ν μ)
    (g : columnGroup t) (hg : ∀ i, (g : Equiv.Perm (Fin n)) (tableauInclusion s t hs.1 i) =
      tableauInclusion s t hs.1 i) : g = 1 := by
  have hin (k : Fin n) (hk : (t k).val ∈ ν) : (g : Equiv.Perm (Fin n)) k = k := by
    let i := s.symm ⟨(t k).val, hk⟩
    have he : tableauInclusion s t hs.1 i = k := by
      apply t.injective
      apply Subtype.ext
      rw [tableauInclusion_cell]
      simp [i]
    simpa only [he] using hg i
  apply Subtype.ext
  apply Equiv.ext
  intro k
  by_cases hk : (t k).val ∈ ν
  · exact hin k hk
  · have ho : (t ((g : Equiv.Perm (Fin n)) k)).val ∉ ν := by
      intro hh
      have he := hin ((g : Equiv.Perm (Fin n)) k) hh
      have he' := (g : Equiv.Perm (Fin n)).injective he
      exact hk (he' ▸ hh)
    apply t.injective
    apply Subtype.ext
    exact hs.2 _ (t _).property ho _ (t _).property hk (g.property k)

lemma strip_contraction_coefficient {a n : ℕ} {ν μ : YoungDiagram}
    (s : Tableau a ν) (t : Tableau n μ) (hs : HorizontalStrip ν μ) :
    wordRestrict (tableauInclusion s t hs.1) (rowLetterInclusion hs.1)
      (polytabloid t) (rowWord s) = 1 := by
  classical
  let i := tableauInclusion s t hs.1
  let j := rowLetterInclusion hs.1
  have he (g : columnGroup t) :
      (rowWord t ∘ ((g : Equiv.Perm (Fin n))⁻¹ : Equiv.Perm (Fin n))) ∘ i = j ∘ rowWord s ↔ g = 1 := by
    constructor
    · intro hh
      have hf : ∀ k, ((g : Equiv.Perm (Fin n))⁻¹) (i k) = i k := by
        intro k
        apply t.injective
        apply Subtype.ext
        apply Prod.ext
        · have hh' := congrArg Fin.val (congrFun hh k)
          simpa [rowWord, j, rowLetterInclusion, i] using hh'
        · exact (g⁻¹).property (i k)
      have hh' : (g⁻¹ : columnGroup t) = 1 := column_fixed_of_strip s t hs (g⁻¹) hf
      simpa using congrArg Inv.inv hh'
    · rintro rfl
      funext k
      apply Fin.ext
      exact congrArg Prod.fst (tableauInclusion_cell s t hs.1 k)
  let := Fintype.ofFinite (columnGroup t)
  change wordRestrict i j (∑ g : columnGroup t,
    signC (g : Equiv.Perm (Fin n)) • wordRep n (μ.colLen 0)
      (g : Equiv.Perm (Fin n)) (Pi.single (rowWord t) 1)) (rowWord s) = _
  simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    wordRep_single, wordRestrict_single, he]
  simp

lemma column_viaEmbedding {a n : ℕ} {ν μ : YoungDiagram}
    (s : Tableau a ν) (t : Tableau n μ) (h : ν ≤ μ) (g : columnGroup s) :
    (g : Equiv.Perm (Fin a)).viaEmbedding (tableauInclusion s t h) ∈ columnGroup t := by
  intro k
  by_cases hk : k ∈ Set.range (tableauInclusion s t h)
  · obtain ⟨l, rfl⟩ := hk
    rw [Equiv.Perm.viaEmbedding_apply]
    simpa only [tableauInclusion_cell] using g.property l
  · rw [Equiv.Perm.viaEmbedding_apply_of_notMem _ _ _ hk]

lemma signC_viaEmbedding {a n : ℕ} (i : Fin a ↪ Fin n) (g : Equiv.Perm (Fin a)) :
    signC (g.viaEmbedding i) = signC g := by
  classical
  simp [signC_def, Equiv.Perm.viaEmbedding, Equiv.Perm.sign_extendDomain]

lemma strip_contraction_pair {a n : ℕ} {ν μ : YoungDiagram}
    (s : Tableau a ν) (t : Tableau n μ) (hs : HorizontalStrip ν μ) :
    dotProduct (wordRestrict (tableauInclusion s t hs.1) (rowLetterInclusion hs.1)
      (polytabloid t)) (polytabloid s) ≠ 0 := by
  classical
  let i := tableauInclusion s t hs.1
  let j := rowLetterInclusion hs.1
  let x := wordRestrict i j (polytabloid t)
  have hx (g : columnGroup s) : wordRep a (ν.colLen 0) (g : Equiv.Perm (Fin a)) x =
      signC (g : Equiv.Perm (Fin a)) • x := by
    rw [← wordRestrict_equivariant i j ((g : Equiv.Perm (Fin a)).viaEmbedding i)
      (g : Equiv.Perm (Fin a)) (Equiv.Perm.viaEmbedding_apply _ _) (polytabloid t)]
    rw [polytabloid_alternating t ⟨_, column_viaEmbedding s t hs.1 g⟩]
    rw [map_smul, signC_viaEmbedding]
  rw [← columnAlt_coefficient]
  let := Fintype.ofFinite (columnGroup s)
  have he : columnAlt s x = (Fintype.card (columnGroup s) : ℂ) • x := by
    change (∑ g : columnGroup s, signC (g : Equiv.Perm (Fin a)) •
      wordRep a (ν.colLen 0) (g : Equiv.Perm (Fin a))) x = _
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, hx, smul_smul,
      signC_mul_self, one_smul, Finset.sum_const, Finset.card_univ, Nat.cast_smul_eq_nsmul]
  change columnAlt s x (rowWord s) ≠ 0
  rw [he]
  change (Fintype.card (columnGroup s) : ℂ) *
    wordRestrict (tableauInclusion s t hs.1) (rowLetterInclusion hs.1) (polytabloid t) (rowWord s) ≠ 0
  rw [strip_contraction_coefficient s t hs, mul_one]
  exact Nat.cast_ne_zero.mpr Fintype.card_ne_zero

/- Positive horizontal-strip Pieri map, equivariant for the full Young subgroup. -/
theorem pieri_strip_restriction {a n : ℕ} {ν μ : YoungDiagram}
    (s : Tableau a ν) (t : Tableau n μ) (hs : HorizontalStrip ν μ) :
    ∃ F : Specht t →ₗ[ℂ] Specht s, F ≠ 0 ∧
      ∀ (g : Equiv.Perm (Fin n)) (h : Equiv.Perm (Fin a)),
        (∀ k, g (tableauInclusion s t hs.1 k) = tableauInclusion s t hs.1 (h k)) →
        ∀ x, F (spechtRep t g x) = spechtRep s h (F x) := by
  let pr := subrepProject (spechtSub s) (fun _ hx => cyclic_star _ (polytabloid_real s) hx)
  let T := wordRestrict (tableauInclusion s t hs.1) (rowLetterInclusion hs.1)
  let F := pr.toLinearMap.comp (T.comp (spechtSub t).toSubmodule.subtype)
  refine ⟨F, ?_, ?_⟩
  · intro hF
    have hp := subrepProject_pair (spechtSub s)
      (fun _ hx => cyclic_star _ (polytabloid_real s) hx)
      (T (polytabloid t)) ⟨polytabloid s, mem_cyclic _ _⟩
    have he : pr (T (polytabloid t)) = 0 := by
      exact congrArg (fun L : Specht t →ₗ[ℂ] Specht s => L ⟨polytabloid t, mem_cyclic _ _⟩) hF
    rw [he] at hp
    exact strip_contraction_pair s t hs (hp.symm.trans (zero_dotProduct _))
  · intro g h hh x
    change pr (T (wordRep n (μ.colLen 0) g x.val)) = spechtRep s h (pr (T x.val))
    rw [wordRestrict_equivariant _ _ g h hh x.val]
    exact LinearMap.congr_fun (pr.isIntertwining' h) (T x.val)

end Saxl

end

end OAI

-- ---- platform node ----
open OAI OAI.Saxl
open scoped TensorProduct


theorem solution : type_of% @_root_.OAI.Saxl.pieri_strip_restriction := @_root_.OAI.Saxl.pieri_strip_restriction
