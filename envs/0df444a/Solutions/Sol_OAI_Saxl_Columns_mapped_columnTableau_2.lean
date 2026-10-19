-- Prove2me | solution 2 for OAI.Saxl.Columns.mapped_columnTableau
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T01:18:37.055247+00:00
-- url     : https://prove2.me/submissions/eaf092eb-fd28-4775-ab27-50897ae60ea9

-- Generated from openai/math@1581d4c lean/OAI/RepresentationTheory/Saxl/ColumnContraction.lean:L272-L304
-- (upload_full_project.md Phase 4): solution for node OAI.Saxl.Columns.mapped_columnTableau. The node keeps its source
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

-- ---- from OAI.RepresentationTheory.Saxl.ColumnContraction ----
namespace OAI

noncomputable section

open scoped TensorProduct

namespace Saxl.Columns
/- A concrete ordered disjoint union of consecutive columns. -/
lemma sign_perm {rs : List ℕ} (π : Perms rs) :
    (((Equiv.Perm.sign (perm π) : ℤ) : ℂ)) = sg π := by
  induction rs with
  | nil => simp [perm, sg]
  | cons r rs ih =>
    obtain ⟨π, σ⟩ := π
    have hh := congrArg (fun u : ℤˣ => ((u : ℤ) : ℂ))
      (Equiv.Perm.sign_sumCongr π (perm σ))
    exact hh.trans (by simp only [Units.val_mul, Int.cast_mul, ih]; rfl)

/- The matrix product indexed by the actual consecutive position order. -/
/- Ordered product of independent alternating column segments. -/
/- Factorization over independent column permutations, without commuting factors. -/
/- The column-recursive coordinates enumerate the actual Ferrers cells. -/
lemma columnPerm_sign (μ : YoungDiagram) (π : Perms μ.transpose.rowLens) :
    signC (columnPerm μ π).val = sg π := by
  change (((Equiv.Perm.sign ((enumerate μ.transpose.rowLens).symm.permCongr (perm π)) : ℤ) : ℂ)) = sg π
  rw [Equiv.Perm.sign_permCongr]
  exact sign_perm π

lemma mapped_columnTableau (μ : YoungDiagram) (N : ℕ → Band.Mat) :
    wordMap (fun (i : Fin (μ.colLen 0)) (a : Fin 4) =>
      N i.val (Path.parts a).1 (Path.parts a).2) (polytabloid (columnTableau μ)) =
    ∑ π : Perms μ.transpose.rowLens, sg π • Path.pureWord
      (fun q => N (row (perm π (enumerate μ.transpose.rowLens q)))) := by
  classical
  let := Fintype.ofFinite (columnGroup (columnTableau μ))
  unfold polytabloid
  rw [map_sum]
  let e : Perms μ.transpose.rowLens ≃ columnGroup (columnTableau μ) :=
    (columnEquiv μ).trans (Equiv.inv _)
  symm
  apply Fintype.sum_equiv e
  intro π
  rw [map_smul, wordRep_single]
  have hs : signC (e π).val = sg π := by
    change signC (columnPerm μ π).val⁻¹ = sg π
    rw [signC_inv, columnPerm_sign]
  change sg π • _ = signC (e π).val • _
  rw [hs]
  congr 1
  funext w
  rw [wordMap_single]
  unfold Path.pureWord
  apply Finset.prod_congr rfl
  intro q hq
  have hr : row (perm π (enumerate μ.transpose.rowLens q)) =
      ((columnTableau μ) ((e π).val⁻¹ q)).val.1 := by
    change _ = ((columnTableau μ) (((columnPerm μ π).val⁻¹)⁻¹ q)).val.1
    rw [inv_inv, columnTableau_val]
    dsimp only [columnPerm, Equiv.permCongr_apply]
    rw [Equiv.apply_symm_apply, Equiv.symm_symm]
  exact congrArg (fun j => N j (Path.parts (w q)).1 (Path.parts (w q)).2) hr

end Saxl.Columns

end

end OAI

-- ---- platform node ----
open OAI OAI.Saxl OAI.Saxl.Columns
open scoped TensorProduct


theorem solution : type_of% @_root_.OAI.Saxl.Columns.mapped_columnTableau := @_root_.OAI.Saxl.Columns.mapped_columnTableau
