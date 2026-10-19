-- Prove2me | solution 1 for OAI.Saxl.Columns.mapped_columnTableau
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T00:30:20.812603+00:00
-- url     : https://prove2.me/submissions/47ffbd75-775d-42d0-8619-9a88dcd48fd8

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

open OAI OAI.Saxl OAI.Saxl.Columns
open scoped TensorProduct
theorem h42_sign_perm (rs : List ℕ) (π : Saxl.Columns.Perms rs) :
    ((Equiv.Perm.sign (Saxl.Columns.perm π) : ℤ) : ℂ) = Saxl.Columns.sg π := by
  induction rs with
  | nil => simp [Saxl.Columns.perm, Saxl.Columns.sg]
  | cons r rs ih =>
    obtain ⟨π, σ⟩ := π
    simp [Saxl.Columns.perm, Saxl.Columns.sg, Equiv.Perm.sign_sumCongr, ← ih]

theorem solution (μ : YoungDiagram) (N : ℕ → Band.Mat) :
    wordMap (fun (i : Fin (μ.colLen 0)) (a : Fin 4) =>
      N i.val (Path.parts a).1 (Path.parts a).2) (polytabloid (columnTableau μ)) =
    ∑ π : Perms μ.transpose.rowLens, sg π • Path.pureWord
      (fun q => N (row (perm π (enumerate μ.transpose.rowLens q)))) := by
  classical
  unfold polytabloid
  rw [map_sum]
  refine Finset.sum_nbij' (fun g => (columnEquiv μ).symm g⁻¹) (fun π => (columnEquiv μ π)⁻¹)
    (by simp) (by simp) (by simp) (by simp) (fun g _ => ?_)
  obtain ⟨π, hπ⟩ := (columnEquiv μ).surjective g⁻¹
  have hg : g = (columnEquiv μ π)⁻¹ := by rw [hπ, inv_inv]
  subst hg
  simp only [inv_inv, Equiv.symm_apply_apply]
  rw [map_smul, wordRep_single]
  funext v
  simp only [Pi.smul_apply, smul_eq_mul, wordMap_single]
  have hcol : ((columnEquiv μ π : columnGroup _) : Equiv.Perm _) =
      (enumerate μ.transpose.rowLens).symm.permCongr (perm π) := rfl
  congr 1
  · rw [Subgroup.coe_inv, Equiv.Perm.sign_inv, hcol, Equiv.Perm.sign_permCongr, h42_sign_perm]
  · unfold Path.pureWord
    apply Finset.prod_congr rfl
    intro q _
    simp [rowWord, hcol, Equiv.permCongr_apply]

