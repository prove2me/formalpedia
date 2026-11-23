-- Prove2me | solution 1 for GlobalTheory.exists_cols_det_ne_zero_of_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:37:13.015605+00:00
-- url     : https://prove2.me/submissions/c20dba1f-eab3-477b-8203-2f8aa32bc259

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GenericRegularity_ExistsColsDetNeZeroOfMul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open Matrix
namespace GlobalTheory
theorem _root_.solution {Ω : Type} [Field Ω] {n r : ℕ}
    (R : Matrix (Fin r) (Fin n) Ω) (u : Matrix (Fin n) (Fin r) Ω) (hd : (R * u).det ≠ 0) :
    ∃ κ : Fin r → Fin n, (R.submatrix id κ).det ≠ 0 := by
  have hu : IsUnit (R * u).det := isUnit_iff_ne_zero.mpr hd
  have hrA : (R * u).rank = r := by
    have := Matrix.rank_of_isUnit _ ((Matrix.isUnit_iff_isUnit_det _).mpr hu)
    simpa using this
  have hrR : R.rank = r := by
    apply le_antisymm
    · simpa using Matrix.rank_le_card_height R
    · calc r = (R * u).rank := hrA.symm
        _ ≤ R.rank := Matrix.rank_mul_le_left _ _
  obtain ⟨K, a, ha, hspan, hli⟩ := exists_linearIndependent' Ω R.col
  haveI : Fintype K := Fintype.ofInjective a ha
  have hcard : Fintype.card K = r := by
    rw [← finrank_span_eq_card hli, hspan, ← Matrix.rank_eq_finrank_span_cols, hrR]
  let e : Fin r ≃ K := (Fintype.equivFinOfCardEq hcard).symm
  refine ⟨a ∘ e, ?_⟩
  have h3 : LinearIndependent Ω (R.submatrix id (a ∘ e)).col := hli.comp e e.injective
  rw [Matrix.linearIndependent_cols_iff_isUnit] at h3
  exact isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det _).mp h3)
end GlobalTheory
