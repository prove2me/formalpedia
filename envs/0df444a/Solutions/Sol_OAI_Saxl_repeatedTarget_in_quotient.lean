-- Prove2me | solution 1 for OAI.Saxl.repeatedTarget_in_quotient
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T02:24:41.653331+00:00
-- url     : https://prove2.me/submissions/76ed2dc6-ea71-4cd6-8703-520a0492bd3c

-- Generated from openai/math@1581d4c lean/OAI/RepresentationTheory/Saxl/DominatedQuotient.lean:L93-L119
-- (upload_full_project.md Phase 4): solution for node OAI.Saxl.repeatedTarget_in_quotient. The node keeps its source
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
import Theorems.Thm_OAI_Saxl_repeated_alt_projection
import Theorems.Thm_OAI_Saxl_signEquiv_rowAverage

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

-- ---- from OAI.RepresentationTheory.Saxl.StaircaseSign ----
namespace OAI

noncomputable section

open scoped TensorProduct

universe uX uY uZ

namespace Saxl

lemma repeatedTarget_fixed (m : ℕ) (g : columnGroup (stairRowTableau m)) (i) :
    repeatedTarget m (g.val i) = repeatedTarget m i := by
  apply congrArg Fin.rev
  apply Fin.ext
  exact g.property i

lemma repeated_letters_injective (m : ℕ) :
    Function.Injective (fun i => (repeatedTarget m i, rowWord (stairRowTableau m) i)) := by
  intro i j he
  apply (stairTableau m).injective
  apply Subtype.ext
  apply Prod.ext
  · have hh : Fin.rev (rowWord (stairTableau m) i) = Fin.rev (rowWord (stairTableau m) j) :=
      congrArg Prod.fst he
    exact congrArg Fin.val (Fin.rev_injective hh)
  · exact congrArg Fin.val (congrArg Prod.snd he)

lemma repeated_complement (m : ℕ) (i) :
    (rowWord (stairRowTableau m) i).val +
      (rowWord (stairRowTableau m) ((rowReversal m).val i)).val =
      (repeatedTarget m i).val := by
  have hi : (stairTableau m i).val.1 + (stairTableau m i).val.2 < m :=
    mem_staircase.mp (stairTableau m i).property
  simp only [rowWord, stairRowTableau, rowReversal, Equiv.trans_apply,
    Equiv.apply_symm_apply, repeatedTarget, Fin.val_rev, staircase_colLen, Nat.sub_zero]
  change (stairTableau m i).val.2 + (m-1-(stairTableau m i).val.1-(stairTableau m i).val.2) =
    m-((stairTableau m i).val.1+1)
  omega

theorem staircase_repeated_projection (m : ℕ) :
    orbitProjection (repeatedTarget m)
      (pairSumMap (staircase m).card ((staircase m).colLen 0) ((staircase m).colLen 0)
        (wordTensor _ _ _ (polytabloid (stairRowTableau m) ⊗ₜ[ℂ] polytabloid (stairRowTableau m)))) =
      ((Nat.card (columnGroup (stairRowTableau m)) : ℂ) * signC (rowReversal m).val) •
        Pi.single (repeatedTarget m) 1 := by
  exact repeated_alt_projection (columnGroup (stairRowTableau m))
    (rowWord (stairRowTableau m)) (repeatedTarget m) (rowReversal m)
    (repeatedTarget_fixed m) (repeated_letters_injective m) (repeated_complement m)

/- A sign intertwiner in the second factor twists the diagonal product. -/
end Saxl

end

end OAI

-- ---- from OAI.RepresentationTheory.Saxl.DominatedQuotient ----
namespace OAI

noncomputable section

open scoped TensorProduct

namespace Saxl

lemma subrepProject_subtype {n d : ℕ} (S : Subrepresentation (wordRep n d))
    (hS : ∀ x ∈ S.toSubmodule, star x ∈ S.toSubmodule) (x : S) :
    subrepProject S hS x.val = x := by
  change (subrepSelfDual S hS).symm (subrepSelfDual S hS x) = x
  exact (subrepSelfDual S hS).symm_apply_apply x

lemma ambientSignMap_subtype (m : ℕ)
    (φ : (spechtRep (stairTableau m)).Equiv (signTwist (spechtRep (stairRowTableau m))))
    (x : Specht (stairTableau m)) : ambientSignMap m φ x.val = (φ x).val := by
  change (φ (subrepProject (spechtSub (stairTableau m)) _ x.val)).val = _
  exact congrArg (fun y : Specht (stairTableau m) => (φ y).val)
    (subrepProject_subtype (spechtSub (stairTableau m)) _ x)

lemma pairAntiMap_tensor (m : ℕ)
    (φ : (spechtRep (stairTableau m)).Equiv (signTwist (spechtRep (stairRowTableau m))))
    (x y : WordSpace (staircase m).card ((staircase m).colLen 0)) :
    pairAntiMap m φ (wordTensor _ _ _ (x ⊗ₜ[ℂ] y)) =
      wordTensor _ _ _ (x ⊗ₜ[ℂ] ambientSignMap m φ y) := by
  change wordTensor _ _ _ (TensorProduct.map LinearMap.id (ambientSignMap m φ).toLinearMap
    ((wordTensor _ _ _).symm (wordTensor _ _ _ (x ⊗ₜ[ℂ] y)))) = _
  rw [LinearEquiv.symm_apply_apply, TensorProduct.map_tmul, LinearMap.id_apply]
  rfl

lemma signed_average_staircase (m : ℕ) :
    letI := Fintype.ofFinite (columnGroup (stairRowTableau m))
    ∑ g : columnGroup (stairRowTableau m), signC g.val •
      wordRep (staircase m).card ((staircase m).colLen 0 * (staircase m).colLen 0) g.val (staircaseWord m) =
    wordTensor _ _ _ (polytabloid (stairRowTableau m) ⊗ₜ[ℂ] (rowAverage m).val) := by
  classical
  let := Fintype.ofFinite (columnGroup (stairRowTableau m))
  change _ = wordTensor _ _ _ (polytabloid (stairRowTableau m) ⊗ₜ[ℂ]
    (∑ g : columnGroup (stairRowTableau m),
      spechtRep (stairTableau m) g.val ⟨polytabloid (stairTableau m), mem_cyclic _ _⟩).val)
  rw [Submodule.coe_sum, TensorProduct.tmul_sum, map_sum]
  apply Finset.sum_congr rfl
  intro g hg
  change signC g.val • wordRep _ _ g.val (wordTensor _ _ _
    (polytabloid (stairRowTableau m) ⊗ₜ[ℂ] polytabloid (stairTableau m))) = _
  rw [← wordTensor_equivariant]
  change signC g.val • wordTensor _ _ _
    (wordRep _ _ g.val (polytabloid (stairRowTableau m)) ⊗ₜ[ℂ]
      wordRep _ _ g.val (polytabloid (stairTableau m))) = _
  rw [polytabloid_alternating _ g, TensorProduct.smul_tmul, TensorProduct.tmul_smul, map_smul,
    smul_smul, signC_mul_self, one_smul]
  rfl

/- The exact staircase permutation generator occurs in the image of the
sign-twisted cyclic staircase module, with no Young-rule input. -/
theorem repeatedTarget_in_quotient (m : ℕ)
    (φ : (spechtRep (stairTableau m)).Equiv (signTwist (spechtRep (stairRowTableau m)))) :
    Pi.single (repeatedTarget m) (1:ℂ) ∈ (dominatedQuotient m φ).range := by
  classical
  let := Fintype.ofFinite (columnGroup (stairRowTableau m))
  obtain ⟨c,hc,hφ⟩ := signEquiv_rowAverage m φ
  let x : (staircaseCyclic m).toSubmodule := ∑ g : columnGroup (stairRowTableau m), signC g.val •
    (staircaseCyclic m).toRepresentation g.val ⟨staircaseWord m, mem_cyclic _ _⟩
  have hx : x.val = wordTensor _ _ _ (polytabloid (stairRowTableau m) ⊗ₜ[ℂ] (rowAverage m).val) := by
    change (∑ g : columnGroup (stairRowTableau m), signC g.val •
      (staircaseCyclic m).toRepresentation g.val ⟨staircaseWord m, mem_cyclic _ _⟩).val = _
    simp only [Submodule.coe_sum, Submodule.coe_smul_of_tower]
    exact signed_average_staircase m
  let q : ℂ := (Nat.card (columnGroup (stairRowTableau m)) : ℂ) * signC (rowReversal m).val
  have hq : q ≠ 0 := by
    apply mul_ne_zero (Nat.cast_ne_zero.mpr (Nat.card_pos (α := columnGroup (stairRowTableau m))).ne')
    intro hz
    have hh := signC_mul_self (rowReversal m).val
    rw [hz, zero_mul] at hh
    exact zero_ne_one hh
  have hF : dominatedQuotient m φ x = (c*q) • Pi.single (repeatedTarget m) (1:ℂ) := by
    change orbitProjection (repeatedTarget m) (pairSumMap _ _ _ (pairAntiMap m φ x.val)) = _
    rw [hx, pairAntiMap_tensor, ambientSignMap_subtype, hφ,
      TensorProduct.tmul_smul, map_smul, map_smul, map_smul, staircase_repeated_projection, smul_smul]
  have hm : (c*q) • Pi.single (repeatedTarget m) (1:ℂ) ∈ (dominatedQuotient m φ).range :=
    ⟨x,hF⟩
  exact (Submodule.smul_mem_iff _ (mul_ne_zero hc hq)).mp hm

end Saxl

end

end OAI

-- ---- platform node ----
open OAI OAI.Saxl
open scoped TensorProduct


theorem solution : type_of% @_root_.OAI.Saxl.repeatedTarget_in_quotient := @_root_.OAI.Saxl.repeatedTarget_in_quotient
