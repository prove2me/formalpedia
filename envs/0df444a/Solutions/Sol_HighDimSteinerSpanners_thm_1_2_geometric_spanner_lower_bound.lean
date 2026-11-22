-- Prove2me | solution 1 for HighDimSteinerSpanners.thm_1_2_geometric_spanner_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:59:41.038428+00:00
-- url     : https://prove2.me/submissions/35ea14af-5a62-4e51-9a41-cffd146268fb

module
public import Definitions.Def_LeanPool_SteinerSpanners_Defs
public import Definitions.Def_LeanPool_SteinerSpanners_Glue
public import Definitions.Def_LeanPool_SteinerSpanners_Projection
public import Definitions.Def_LeanPool_SteinerSpanners_Combinatorics
public import Definitions.Def_LeanPool_SteinerSpanners_CSP
public import Definitions.Def_LeanPool_SteinerSpanners_Bucketing
public import Definitions.Def_LeanPool_SteinerSpanners_Hamming
public import Definitions.Def_LeanPool_SteinerSpanners_Dvoretzky
public import Definitions.Def_LeanPool_SteinerSpanners
public import Theorems.Thm_HighDimSteinerSpanners_lpDist_eq_toLp_dist
public import Theorems.Thm_HighDimSteinerSpanners_thm_1_3_non_metric_steiner_spanner_lower_bound
public import Theorems.Thm_HighDimSteinerSpanners_Proofs_Geometry_lpDist_eq_toLp_dist
public import Theorems.Thm_HighDimSteinerSpanners_Proofs_Projection_thm_1_2_from_1_3


set_option autoImplicit true
@[expose] public section
public section
open scoped ENNReal
open HighDimSteinerSpanners
open HighDimSteinerSpanners
namespace HighDimSteinerSpanners
theorem _root_.solution :
    ∃ M : ℝ, 0 < M ∧
      ∀ (p : ℝ), 1 ≤ p →
        ∀ (C : ℝ), 1 ≤ C →
          ∃ (c c₀ A β₁ β₂ : ℝ),
            (2 : ℝ) ^ (-M * C ^ (4 * p)) ≤ (2 : ℝ) ^ (-M * C ^ (3 * p) * Real.logb 2 (C ^ p + 1)) ∧
            (2 : ℝ) ^ (-M * C ^ (3 * p) * Real.logb 2 (C ^ p + 1)) ≤ c ∧
            0 < c₀ ∧ 0 < A ∧ 0 < β₁ ∧ β₁ ≤ β₂ ∧
            ∃ nSeq : ℕ → ℕ, StrictMono nSeq ∧ (∀ j : ℕ, 2 ≤ nSeq j) ∧
              ∀ j : ℕ,
                ∃ (d : ℕ) (P : Fin (nSeq j) → (Fin d → ℝ)),
                  1 ≤ d ∧
                  β₁ * Real.logb 2 (nSeq j : ℝ) ≤ (d : ℝ) ∧
                  (d : ℝ) ≤ β₂ * Real.logb 2 (nSeq j : ℝ) ∧
                  (∀ i : Fin (nSeq j), ∀ k : Fin d, P i k = 0 ∨ P i k = 1) ∧
                  Function.Injective P ∧
                  aspectRatio p P ≤ A ∧
                  ∀ (G : SimpleGraph (Fin (nSeq j))),
                    IsGeometricSpanner p P C G →
                    c₀ * (nSeq j : ℝ) ^ (1 + c) ≤ (Nat.card G.edgeSet : ℝ) :=
  HighDimSteinerSpanners.Proofs.Projection.thm_1_2_from_1_3
    lpDist_eq_toLp_dist
    thm_1_3_non_metric_steiner_spanner_lower_bound
end HighDimSteinerSpanners
