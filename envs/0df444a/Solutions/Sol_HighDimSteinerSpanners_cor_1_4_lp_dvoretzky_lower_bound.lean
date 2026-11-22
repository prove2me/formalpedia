-- Prove2me | solution 1 for HighDimSteinerSpanners.cor_1_4_lp_dvoretzky_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:59:41.428743+00:00
-- url     : https://prove2.me/submissions/f7a32545-44ad-4149-b9c5-187a7f82b475

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
public import Theorems.Thm_HighDimSteinerSpanners_Proofs_Dvoretzky_cor_1_4_from_1_3
public import Theorems.Thm_HighDimSteinerSpanners_Proofs_Geometry_lpDist_eq_toLp_dist


set_option autoImplicit true
@[expose] public section
public section
open scoped ENNReal
open HighDimSteinerSpanners
open HighDimSteinerSpanners
namespace HighDimSteinerSpanners
theorem _root_.solution :
    ∃ (M : ℝ) (c c₀ A : ℝ → ℝ),
      0 < M ∧
      (∀ C : ℝ, 1 ≤ C →
        (2 : ℝ) ^ (-M * C ^ (6 : ℕ) * Real.logb 2 (C + 1)) ≤ c C ∧ 0 < c₀ C ∧ 0 < A C) ∧
      ∀ (p : ℝ), 2 < p →
        ∀ (C : ℝ), 1 ≤ C →
          ∃ (β₁ β₂ : ℝ), 0 < β₁ ∧ β₁ ≤ β₂ ∧
            ∃ nSeq : ℕ → ℕ, StrictMono nSeq ∧ (∀ j : ℕ, 2 ≤ nSeq j) ∧
              ∀ j : ℕ,
                ∃ (d : ℕ) (P : Fin (nSeq j) → (Fin d → ℝ)),
                  1 ≤ d ∧
                  β₁ * (Real.logb 2 (nSeq j : ℝ)) ^ (p / 2) ≤ (d : ℝ) ∧
                  (d : ℝ) ≤ β₂ * (Real.logb 2 (nSeq j : ℝ)) ^ (p / 2) ∧
                  Function.Injective P ∧
                  aspectRatio p P ≤ A C ∧
                  (∀ (S : Type) [Fintype S]
                    (H : SimpleGraph (Fin (nSeq j) ⊕ S))
                    (w : Sym2 (Fin (nSeq j) ⊕ S) → ℝ),
                    IsNonMetricSteinerSpanner p P C H w →
                    c₀ C * (nSeq j : ℝ) ^ (1 + c C) ≤ (Nat.card H.edgeSet : ℝ)) ∧
                  (∀ (G : SimpleGraph (Fin (nSeq j))),
                    IsGeometricSpanner p P C G →
                    c₀ C * (nSeq j : ℝ) ^ (1 + c C) ≤ (Nat.card G.edgeSet : ℝ)) :=
  HighDimSteinerSpanners.Proofs.Dvoretzky.cor_1_4_from_1_3
    lpDist_eq_toLp_dist
    thm_1_3_non_metric_steiner_spanner_lower_bound
end HighDimSteinerSpanners
