-- Prove2me | solution 1 for Kyprianou.Ch01.firstNegativePassageAfterNonnegativeOpenInterval
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T15:23:29.195559+00:00
-- url     : https://prove2.me/submissions/bd17d7fa-4bc2-4f71-aea0-2b9586aa14da

import Mathlib
import Definitions.Def_Kyprianou_Ch01_LampertiInverse
open Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    {Ω : Type*} (X : ℝ≥0 → Ω → ℤ) (ω : Ω) (c : ℝ≥0)
    (hNonneg : ∀ u : ℝ≥0, u < c → 0 ≤ X u ω) :
    (c : WithTop ℝ≥0) ≤ firstNegativePassage X ω := by
  unfold firstNegativePassage
  split_ifs with h
  · obtain ⟨u, hu⟩ := h
    apply WithTop.coe_le_coe.mpr
    apply le_csInf ⟨u, hu⟩
    rintro s ⟨hsPos, hsNeg⟩
    by_contra hlt0
    have hlt : s < c := not_le.mp hlt0
    exact (not_lt.mpr (hNonneg s hlt)) hsNeg
  · exact le_top
