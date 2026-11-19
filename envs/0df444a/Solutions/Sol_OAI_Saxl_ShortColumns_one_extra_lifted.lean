-- Prove2me | solution 1 for OAI.Saxl.ShortColumns.one_extra_lifted
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T00:36:03.425207+00:00
-- url     : https://prove2.me/submissions/f5623624-2814-44d2-ae09-66387a83b33c

import Mathlib
import Definitions.Def_UniversalTensorSquares
import Definitions.Def_OAIQ259US021
import Theorems.Thm_OAI_Saxl_ShortColumns_even_columnSquare_support
import Theorems.Thm_OAI_Saxl_ShortColumns_one_extra_odd
import Definitions.Def_OAIQ259US000
import Definitions.Def_OAIQ259US001
import Definitions.Def_OAIQ259US006
import Theorems.Thm_OAI_Saxl_specht_sign_transpose_uts

section
-- module Solutions.OAIQ259_US.Saxl_HighProjection
attribute [-instance] _root_.OAI.Saxl.Columns.cellsDecEq _root_.OAI.Saxl.Columns.cellsFintype _root_.OAI.Saxl.Columns.permsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped TensorProduct

namespace Saxl
/- Translate the high part of each row to the smaller staircase. -/


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

end Saxl

end

end OAI
end

section
-- module Solutions.OAIQ259_US.Saxl_CyclicSector
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped TensorProduct

universe uG uX uY uZ uV

namespace Saxl

theorem cyclic_projection_support {G : Type uG} {X : Type uX} {Y : Type uY} {Z : Type uZ} [Group G] [Finite G]
    [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
    [AddCommGroup Z] [Module ℂ Z]
    {ρ : Representation ℂ G X} {σ : Representation ℂ G Y} {τ : Representation ℂ G Z}
    (F : Representation.IntertwiningMap ρ σ) (v : X)
    (f : Representation.IntertwiningMap τ (cyclic σ (F v)).toRepresentation) (hf : f ≠ 0) :
    ∃ g : Representation.IntertwiningMap τ (cyclic ρ v).toRepresentation, g ≠ 0 := by
  obtain ⟨g,hg⟩ := intertwining_lift_surjective (cyclicMap F v) (cyclicMap_surjective F v) f
  refine ⟨g, ?_⟩
  intro hz
  apply hf
  rw [← hg,hz]
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro x
  exact map_zero (cyclicMap F v)



end Saxl

end

end OAI
end

section
-- module Solutions.OAIQ259_US.Saxl_StaircaseSign
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

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

end Saxl

end

end OAI
end

section
-- module Solutions.OAIQ259_US.Saxl_DominatedQuotient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped TensorProduct

namespace Saxl

lemma subrepProject_subtype {n d : ℕ} (S : Subrepresentation (wordRep n d))
    (hS : ∀ x ∈ S.toSubmodule, star x ∈ S.toSubmodule) (x : S) :
    subrepProject S hS x.val = x := by
  change (subrepSelfDual S hS).symm (subrepSelfDual S hS x) = x
  exact (subrepSelfDual S hS).symm_apply_apply x

end Saxl

end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Support_AttachmentTransfer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Attachment Transfer. -/

section

noncomputable section
open scoped TensorProduct

namespace Saxl

lemma transposeColumnAverage_nonzero {n : ℕ} {α : YoungDiagram} (t : Tableau n α) :
    transposeColumnAverage t ≠ 0 := by
  classical
  let := Fintype.ofFinite (columnGroup (transposeTableau t))
  intro he
  have hh := congrArg (fun y : Specht t => y.val (rowWord t)) he
  have hg (g : columnGroup (transposeTableau t)) : rowWord t ∘ g.val = rowWord t := by
    funext i
    apply Fin.ext
    exact g.property i
  simp only [transposeColumnAverage, Submodule.coe_sum, Finset.sum_apply] at hh
  change (∑ g : columnGroup (transposeTableau t),
    polytabloid t (rowWord t ∘ g.val)) = 0 at hh
  simp only [hg, polytabloid_rowWord, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, mul_one] at hh
  exact Nat.cast_ne_zero.mpr Fintype.card_ne_zero hh

lemma transposeColumnAverage_fixed {n : ℕ} {α : YoungDiagram} (t : Tableau n α)
    (g : columnGroup (transposeTableau t)) :
    spechtRep t g.val (transposeColumnAverage t) = transposeColumnAverage t := by
  classical
  let := Fintype.ofFinite (columnGroup (transposeTableau t))
  unfold transposeColumnAverage
  rw [map_sum]
  simp only [← Module.End.mul_apply, ← map_mul]
  exact Equiv.sum_comp (Equiv.mulLeft g) (fun h : columnGroup (transposeTableau t) =>
    spechtRep t h.val ⟨polytabloid t, mem_cyclic _ _⟩)

lemma signEquiv_transposeColumnAverage {n : ℕ} {α : YoungDiagram} (t : Tableau n α)
    (φ : (spechtRep t).Equiv (signTwist (spechtRep (transposeTableau t)))) :
    ∃ c : ℂ, c ≠ 0 ∧ (φ (transposeColumnAverage t)).val =
      c • polytabloid (transposeTableau t) := by
  have ha (g : columnGroup (transposeTableau t)) :
      spechtRep (transposeTableau t) g.val (φ (transposeColumnAverage t)) =
        signC g.val • φ (transposeColumnAverage t) := by
    have he := LinearMap.congr_fun (φ.isIntertwining' g.val) (transposeColumnAverage t)
    change φ (spechtRep t g.val (transposeColumnAverage t)) =
      signC g.val • spechtRep (transposeTableau t) g.val (φ (transposeColumnAverage t)) at he
    rw [transposeColumnAverage_fixed] at he
    have hh := congrArg (fun x => signC g.val • x) he
    simpa only [smul_smul, signC_mul_self, one_smul] using hh.symm
  obtain ⟨c,hc⟩ := alternating_specht_line (transposeTableau t)
    (φ (transposeColumnAverage t)) ha
  refine ⟨c, ?_, hc⟩
  intro hz
  rw [hz, zero_smul] at hc
  apply transposeColumnAverage_nonzero t
  apply φ.injective
  exact (Subtype.ext hc).trans (map_zero φ).symm

lemma columnAmbientSignMap_subtype {n : ℕ} {α : YoungDiagram} (t : Tableau n α)
    (φ : (spechtRep t).Equiv (signTwist (spechtRep (transposeTableau t))))
    (x : Specht t) : columnAmbientSignMap t φ x.val = (φ x).val := by
  change (φ (subrepProject (spechtSub t) _ x.val)).val = _
  exact congrArg (fun y : Specht t => (φ y).val) (subrepProject_subtype (spechtSub t) _ x)

lemma columnPairAntiMap_tensor {n : ℕ} {α : YoungDiagram} (t : Tableau n α)
    (φ : (spechtRep t).Equiv (signTwist (spechtRep (transposeTableau t))))
    (x : WordSpace n (α.transpose.colLen 0)) (y : WordSpace n (α.colLen 0)) :
    columnPairAntiMap t φ (wordTensor _ _ _ (x ⊗ₜ[ℂ] y)) =
      wordTensor _ _ _ (x ⊗ₜ[ℂ] columnAmbientSignMap t φ y) := by
  change wordTensor _ _ _ (TensorProduct.map LinearMap.id
    (columnAmbientSignMap t φ).toLinearMap
    ((wordTensor _ _ _).symm (wordTensor _ _ _ (x ⊗ₜ[ℂ] y)))) = _
  rw [LinearEquiv.symm_apply_apply, TensorProduct.map_tmul, LinearMap.id_apply]
  rfl

lemma signed_average_rowColumn {n : ℕ} {α : YoungDiagram} (t : Tableau n α) :
    letI := Fintype.ofFinite (columnGroup (transposeTableau t))
    ∑ g : columnGroup (transposeTableau t), signC g.val •
      wordRep n (α.transpose.colLen 0 * α.colLen 0) g.val (rowColumnWord t) =
      wordTensor _ _ _
        (polytabloid (transposeTableau t) ⊗ₜ[ℂ] (transposeColumnAverage t).val) := by
  classical
  let := Fintype.ofFinite (columnGroup (transposeTableau t))
  change _ = wordTensor _ _ _ (polytabloid (transposeTableau t) ⊗ₜ[ℂ]
    (∑ g : columnGroup (transposeTableau t),
      spechtRep t g.val ⟨polytabloid t, mem_cyclic _ _⟩).val)
  rw [Submodule.coe_sum, TensorProduct.tmul_sum, map_sum]
  apply Finset.sum_congr rfl
  intro g hg
  change signC g.val • wordRep _ _ g.val (wordTensor _ _ _
    (polytabloid (transposeTableau t) ⊗ₜ[ℂ] polytabloid t)) = _
  rw [← wordTensor_equivariant]
  change signC g.val • wordTensor _ _ _
    (wordRep _ _ g.val (polytabloid (transposeTableau t)) ⊗ₜ[ℂ]
      wordRep _ _ g.val (polytabloid t)) = _
  rw [polytabloid_alternating _ g, TensorProduct.smul_tmul, TensorProduct.tmul_smul,
    map_smul, smul_smul, signC_mul_self, one_smul]
  rfl

theorem polytabloid_square_in_rowColumn_image {n : ℕ} {α : YoungDiagram} (t : Tableau n α)
    (φ : (spechtRep t).Equiv (signTwist (spechtRep (transposeTableau t)))) :
    wordTensor _ _ _ (polytabloid (transposeTableau t) ⊗ₜ[ℂ]
      polytabloid (transposeTableau t)) ∈ (rowColumnToSquare t φ).range := by
  classical
  let := Fintype.ofFinite (columnGroup (transposeTableau t))
  obtain ⟨c,hc,hφ⟩ := signEquiv_transposeColumnAverage t φ
  let x : (rowColumnCyclic t).toSubmodule :=
    ∑ g : columnGroup (transposeTableau t), signC g.val •
      (rowColumnCyclic t).toRepresentation g.val ⟨rowColumnWord t, mem_cyclic _ _⟩
  have hx : x.val = wordTensor _ _ _ (polytabloid (transposeTableau t) ⊗ₜ[ℂ]
      (transposeColumnAverage t).val) := by
    change (∑ g : columnGroup (transposeTableau t), signC g.val •
      (rowColumnCyclic t).toRepresentation g.val ⟨rowColumnWord t, mem_cyclic _ _⟩).val = _
    simp only [Submodule.coe_sum, Submodule.coe_smul_of_tower]
    exact signed_average_rowColumn t
  have hF : rowColumnToSquare t φ x = c • wordTensor _ _ _
      (polytabloid (transposeTableau t) ⊗ₜ[ℂ] polytabloid (transposeTableau t)) := by
    change columnPairAntiMap t φ x.val = _
    rw [hx, columnPairAntiMap_tensor, columnAmbientSignMap_subtype, hφ,
      TensorProduct.tmul_smul, map_smul]
  exact (Submodule.smul_mem_iff _ hc).mp ⟨x,hF⟩

theorem square_cyclic_embeds_sign_rowColumn {n : ℕ} {α : YoungDiagram} (t : Tableau n α) :
    ∃ f : Representation.IntertwiningMap
      (cyclic (wordRep n (α.transpose.colLen 0 * α.transpose.colLen 0))
        (wordTensor _ _ _ (polytabloid (transposeTableau t) ⊗ₜ[ℂ]
          polytabloid (transposeTableau t)))).toRepresentation
      (signTwist (rowColumnCyclic t).toRepresentation), Function.Injective f := by
  obtain ⟨φ⟩ := specht_sign_transpose_uts t
  apply subrepresentation_embeds_of_le_range (rowColumnToSquare t φ)
  exact (cyclic_le _ _ _).mpr (polytabloid_square_in_rowColumn_image t φ)

end Saxl
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Band_OneExtra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! One Extra. -/

section

noncomputable section
open scoped TensorProduct
namespace Saxl

lemma intertwining_comp_ne_zero {G X Y Z : Type*} [Group G]
    [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
    [AddCommGroup Z] [Module ℂ Z]
    {ρ : Representation ℂ G X} {σ : Representation ℂ G Y} {τ : Representation ℂ G Z}
    (F : Representation.IntertwiningMap σ τ) (hF : Function.Injective F)
    (f : Representation.IntertwiningMap ρ σ) (hf : f ≠ 0) : F.comp f ≠ 0 := by
  intro hz
  apply hf
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro x
  apply hF
  have hh := congrArg (fun H => H x) hz
  exact hh.trans (map_zero F).symm

theorem sign_rowColumn_support_of_columnSquare {n : ℕ} {α : YoungDiagram} (t : Tableau n α)
    {X : Type*} [AddCommGroup X] [Module ℂ X]
    (ρ : Representation ℂ (Equiv.Perm (Fin n)) X)
    (f : Representation.IntertwiningMap ρ (columnSquareCyclic t).toRepresentation) (hf : f ≠ 0) :
    ∃ g : Representation.IntertwiningMap ρ (signTwist (rowColumnCyclic t).toRepresentation),
      g ≠ 0 := by
  let T := transposeTableau (transposeTableau t)
  let F := pairWordMap (n := n) (letterLift (Fin.cast (congrArg (fun ν : YoungDiagram => ν.colLen 0)
    (YoungDiagram.transpose_transpose α))))
    (letterLift (Fin.cast (congrArg (fun ν : YoungDiagram => ν.colLen 0)
    (YoungDiagram.transpose_transpose α))))
  have hF : F (columnSquareWord T) = columnSquareWord t := by
    change pairWordMap _ _ (wordTensor _ _ _ (_ ⊗ₜ[ℂ] _)) = _
    rw [pairWordMap_tensor, polytabloid_doubleTranspose]
    rfl
  have hs : ∃ g : Representation.IntertwiningMap ρ
      (cyclic (wordRep n (α.colLen 0 * α.colLen 0)) (F (columnSquareWord T))).toRepresentation,
        g ≠ 0 := by
    rw [hF]
    exact ⟨f,hf⟩
  obtain ⟨f',hf'⟩ := hs
  obtain ⟨f'',hf''⟩ := cyclic_projection_support F (columnSquareWord T) f' hf'
  obtain ⟨A,hA⟩ := square_cyclic_embeds_sign_rowColumn (transposeTableau t)
  let B := signTwistMap (rowColumnTransposeCyclicMap t)
  refine ⟨B.comp (A.comp f''), intertwining_comp_ne_zero B ?_ _
    (intertwining_comp_ne_zero A hA f'' hf'')⟩
  exact rowColumnTransposeCyclicMap_injective t

lemma transposeTableau_move {n : ℕ} {α : YoungDiagram} (s t : Tableau n α) :
    tableauMove (transposeTableau s) (transposeTableau t) = tableauMove s t := by
  ext i
  rfl

lemma rowColumnWord_move {n : ℕ} {α : YoungDiagram} (s t : Tableau n α) :
    wordRep n _ (tableauMove s t) (rowColumnWord s) = rowColumnWord t := by
  unfold rowColumnWord
  rw [← wordTensor_equivariant]
  change wordTensor _ _ _ (wordRep _ _ (tableauMove s t) (polytabloid (transposeTableau s))
    ⊗ₜ[ℂ] wordRep _ _ (tableauMove s t) (polytabloid s)) = _
  rw [← polytabloid_move s t, ← transposeTableau_move s t,
    ← polytabloid_move (transposeTableau s) (transposeTableau t)]

lemma cyclic_translate_eq {G X : Type*} [Group G] [AddCommGroup X] [Module ℂ X]
    (ρ : Representation ℂ G X) (g : G) (v : X) : cyclic ρ (ρ g v) = cyclic ρ v := by
  apply le_antisymm
  · exact (cyclic_le _ _ _).mpr ((cyclic ρ v).apply_mem_toSubmodule g (mem_cyclic _ _))
  · apply (cyclic_le _ _ _).mpr
    have h := (cyclic ρ (ρ g v)).apply_mem_toSubmodule g⁻¹ (mem_cyclic _ _)
    change v ∈ (cyclic ρ (ρ g v)).toSubmodule
    simpa only [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
      Module.End.one_apply] using h

lemma rowColumnCyclic_tableau_independent {n : ℕ} {α : YoungDiagram} (s t : Tableau n α) :
    rowColumnCyclic s = rowColumnCyclic t := by
  unfold rowColumnCyclic
  rw [← rowColumnWord_move s t, cyclic_translate_eq]

theorem rowColumn_support_change_tableau {n : ℕ} {α : YoungDiagram} (s t : Tableau n α)
    {X : Type*} [AddCommGroup X] [Module ℂ X]
    (ρ : Representation ℂ (Equiv.Perm (Fin n)) X)
    (f : Representation.IntertwiningMap ρ (signTwist (rowColumnCyclic s).toRepresentation))
    (hf : f ≠ 0) :
    ∃ g : Representation.IntertwiningMap ρ (signTwist (rowColumnCyclic t).toRepresentation),
      g ≠ 0 := by
  rw [← rowColumnCyclic_tableau_independent s t]
  exact ⟨f,hf⟩

namespace ShortColumns

theorem one_extra_even (b : ℕ) (s : Tableau (2*b) (shape b 0))
    (μ : YoungDiagram) (t : Tableau (2*b) μ)
    (he : ∀ i, Even (μ.rowLen i)) (hd : μ.colLen 0 ≤ 4) :
    ∃ F : Representation.IntertwiningMap (spechtRep t)
      (signTwist (rowColumnCyclic s).toRepresentation), F ≠ 0 := by
  obtain ⟨f,hf⟩ := even_columnSquare_support b μ t he hd
  obtain ⟨g,hg⟩ := sign_rowColumn_support_of_columnSquare (evenTableau b) (spechtRep t) f hf
  exact rowColumn_support_change_tableau (evenTableau b) s (spechtRep t) g hg

theorem one_extra (b δ : ℕ) (hδ : δ ≤ 1) (s : Tableau (2*b+δ) (shape b δ))
    (μ : YoungDiagram) (t : Tableau (2*b+δ) μ) (hp : RowParity δ μ)
    (hd : μ.colLen 0 ≤ 4) :
    ∃ F : Representation.IntertwiningMap (spechtRep t)
      (signTwist (rowColumnCyclic s).toRepresentation), F ≠ 0 := by
  have h : δ = 0 ∨ δ = 1 := by omega
  rcases h with rfl | rfl
  · simp only [RowParity, ↓reduceIte] at hp
    exact one_extra_even b s μ t hp hd
  · simp only [RowParity, Nat.one_ne_zero, ↓reduceIte] at hp
    obtain ⟨k,hk,he⟩ := hp
    exact one_extra_odd b s μ t k hk he hd

end ShortColumns
end Saxl
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Band_TwoExtras
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Two Extras. -/

section

noncomputable section
open scoped TensorProduct
namespace Saxl

lemma cyclicMap_injective {G X Y : Type*} [Group G] [AddCommGroup X] [Module ℂ X]
    [AddCommGroup Y] [Module ℂ Y] {ρ : Representation ℂ G X} {σ : Representation ℂ G Y}
    (F : Representation.IntertwiningMap ρ σ) (v : X) (hF : Function.Injective F) :
    Function.Injective (cyclicMap F v) := by
  intro x y h
  apply Subtype.ext
  exact hF (congrArg Subtype.val h)

namespace ShortColumns

lemma one_extra_degree (b δ n : ℕ) (hδ : δ ≤ 1) (hn : 2*b+δ = n)
    (s : Tableau n (shape b δ)) (μ : YoungDiagram) (t : Tableau n μ)
    (hp : RowParity δ μ) (hd : μ.colLen 0 ≤ 4) :
    ∃ F : Representation.IntertwiningMap (spechtRep t)
      (signTwist (rowColumnCyclic s).toRepresentation), F ≠ 0 := by
  subst n
  exact one_extra b δ hδ s μ t hp hd

lemma one_extra_lifted_oai (r d : ℕ) (s : Tableau r (shape (r/2) (r%2)))
    (φ : Fin ((shape (r/2) (r%2)).transpose.colLen 0 *
      (shape (r/2) (r%2)).colLen 0) → Fin d) (hφ : Function.Injective φ)
    (μ : YoungDiagram) (t : Tableau r μ) (hp : RowParity (r%2) μ)
    (hd : μ.colLen 0 ≤ 4) :
    ∃ F : Representation.IntertwiningMap (spechtRep t)
      (signTwist (cyclic (wordRep r d) (letterLift φ (rowColumnWord s))).toRepresentation),
      Function.Injective F := by
  obtain ⟨f,hf⟩ := one_extra_degree (r/2) (r%2) r (by omega) (by omega) s μ t hp hd
  let G := signTwistMap (cyclicMap (letterLift φ) (rowColumnWord s))
  have hG : Function.Injective G := cyclicMap_injective _ _ (letterLift_injective φ hφ)
  let := specht_irreducible t
  exact ⟨G.comp f, hG.comp ((Representation.IsIrreducible.injective_or_eq_zero f).resolve_right hf)⟩

end ShortColumns
end Saxl
end
end

end OAI
end

theorem solution : type_of% @OAI.Saxl.ShortColumns.one_extra_lifted_oai := @OAI.Saxl.ShortColumns.one_extra_lifted_oai
