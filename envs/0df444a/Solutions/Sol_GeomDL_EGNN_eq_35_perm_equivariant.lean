-- Prove2me | solution 1 for GeomDL.EGNN.eq_35_perm_equivariant
-- status  : ACCEPTED   (prove)
-- author  : @涼宮 ハルヒ
-- created : 2026-10-22T03:42:07.665717+00:00
-- url     : https://prove2.me/submissions/98c5fd27-9df0-43fa-81ee-8a9c26cb1649

import Definitions.Def_GeomDL_EGNN_Defs
import Mathlib.Data.Finset.Image

set_option autoImplicit false

namespace D22EGNNPermutation

open GeomDL.EGNN

/-- Relabelling carries precisely the original neighbours to the new neighbours. -/
theorem nbhd_permuted {n : ℕ} (σ : Equiv.Perm (Fin n))
    (A : Matrix (Fin n) (Fin n) ℝ) (u : Fin n) :
    nbhd (GeomDL.Sets.permAdj σ A) u =
      (nbhd A (σ.symm u)).map σ.toEmbedding := by
  classical
  apply Finset.ext
  intro v
  rw [Finset.mem_map_equiv]
  change
    v ∈ Finset.univ.filter (fun w =>
      A (σ.symm u) (σ.symm w) ≠ 0 ∨ A (σ.symm w) (σ.symm u) ≠ 0) ↔
    σ.symm v ∈ Finset.univ.filter (fun w =>
      A (σ.symm u) w ≠ 0 ∨ A w (σ.symm u) ≠ 0)
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

end D22EGNNPermutation

/-- A shared message map and multiset aggregation commute with relabelling. -/
theorem solution {n : ℕ} {α M M' β : Type*} (φ : α → M' → β)
    (agg : Multiset M → M') (ψ : α → α → M) (σ : Equiv.Perm (Fin n)) (X : Fin n → α)
    (A : Matrix (Fin n) (Fin n) ℝ) :
    GeomDL.EGNN.mpLayer φ agg ψ (GeomDL.EGNN.permRows σ X) (GeomDL.Sets.permAdj σ A) =
      GeomDL.EGNN.permRows σ (GeomDL.EGNN.mpLayer φ agg ψ X A) := by
  classical
  funext u
  change φ (X (σ.symm u))
      (agg ((GeomDL.EGNN.nbhd (GeomDL.Sets.permAdj σ A) u).val.map
        (fun v => ψ (X (σ.symm u)) (X (σ.symm v))))) =
    φ (X (σ.symm u))
      (agg ((GeomDL.EGNN.nbhd A (σ.symm u)).val.map
        (fun v => ψ (X (σ.symm u)) (X v))))
  apply congrArg (φ (X (σ.symm u)))
  apply congrArg agg
  rw [D22EGNNPermutation.nbhd_permuted]
  simp only [Finset.map_val, Multiset.map_map, Function.comp_def,
    Equiv.toEmbedding_apply, Equiv.symm_apply_apply]

#print axioms solution
