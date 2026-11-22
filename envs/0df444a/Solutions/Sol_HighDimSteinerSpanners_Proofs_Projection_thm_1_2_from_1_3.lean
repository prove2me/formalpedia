-- Prove2me | solution 1 for HighDimSteinerSpanners.Proofs.Projection.thm_1_2_from_1_3
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:48:59.458727+00:00
-- url     : https://prove2.me/submissions/428e5c31-7308-463b-b335-b13a86f1e148

module
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.NormNum
public import Mathlib.Combinatorics.SimpleGraph.Paths
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Analysis.Normed.Lp.PiLp
public import Definitions.Def_LeanPool_SteinerSpanners_Defs
public import Definitions.Def_LeanPool_SteinerSpanners_Geometry
public import Definitions.Def_LeanPool_SteinerSpanners_Projection
public import Theorems.Thm_HighDimSteinerSpanners_Proofs_Geometry_geometric_spanner_to_steiner


set_option autoImplicit true
@[expose] public section
public section
open scoped ENNReal
open HighDimSteinerSpanners
open HighDimSteinerSpanners HighDimSteinerSpanners.Proofs HighDimSteinerSpanners.Proofs.Projection
namespace HighDimSteinerSpanners.Proofs.Projection
theorem _root_.solution
    (h_lp : ∀ (p : ℝ), 1 ≤ p →
      ∀ {d : ℕ} (x y : Fin d → ℝ),
        lpDist p x y =
          dist (WithLp.toLp (ENNReal.ofReal p) x) (WithLp.toLp (ENNReal.ofReal p) y))
    (h_1_3 : ∃ (M : ℝ) (c c₀ β₁ β₂ A : ℕ → ℝ),
      0 < M ∧
      (∀ C₁ : ℕ, 3 ≤ C₁ →
        (2 : ℝ) ^ (-M * (C₁ : ℝ) ^ 3 * Real.logb 2 (C₁ : ℝ)) ≤ c C₁ ∧
        0 < c₀ C₁ ∧ 0 < β₁ C₁ ∧ β₁ C₁ ≤ β₂ C₁ ∧ 0 < A C₁) ∧
      ∀ (p : ℝ), 1 ≤ p →
        ∀ (C : ℝ), 1 ≤ C →
          let C₁ : ℕ := max 3 ⌈C ^ p⌉₊
          (2 : ℝ) ^ (-(81 * M) * C ^ (4 * p)) ≤
            (2 : ℝ) ^ (-(81 * M) * C ^ (3 * p) * Real.logb 2 (C ^ p + 1)) ∧
          (2 : ℝ) ^ (-(81 * M) * C ^ (3 * p) * Real.logb 2 (C ^ p + 1)) ≤ c C₁ ∧
          ∃ nSeq : ℕ → ℕ, StrictMono nSeq ∧ (∀ j : ℕ, 2 ≤ nSeq j) ∧
            ∀ j : ℕ,
              ∃ (d : ℕ) (P : Fin (nSeq j) → (Fin d → ℝ)),
                1 ≤ d ∧
                β₁ C₁ * Real.logb 2 (nSeq j : ℝ) ≤ (d : ℝ) ∧
                (d : ℝ) ≤ β₂ C₁ * Real.logb 2 (nSeq j : ℝ) ∧
                (∀ i : Fin (nSeq j), ∀ k : Fin d, P i k = 0 ∨ P i k = 1) ∧
                Function.Injective P ∧
                aspectRatio p P ≤ A C₁ ∧
                ∀ (S : Type) [Fintype S]
                  (H : SimpleGraph (Fin (nSeq j) ⊕ S))
                  (w : Sym2 (Fin (nSeq j) ⊕ S) → ℝ),
                  IsNonMetricSteinerSpanner p P C H w →
                  c₀ C₁ * (nSeq j : ℝ) ^ (1 + c C₁) ≤ (Nat.card H.edgeSet : ℝ)) :
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
                    c₀ * (nSeq j : ℝ) ^ (1 + c) ≤ (Nat.card G.edgeSet : ℝ) := by
  obtain ⟨M₁, c, c₀, β₁, β₂, A, hM₁_pos, h_consts, h_main⟩ := h_1_3
  refine ⟨81 * M₁, by positivity, ?_⟩
  intro p hp C hC
  let C₁ : ℕ := max 3 ⌈C ^ p⌉₊
  obtain ⟨_, hc₀_pos, hβ₁_pos, hβ₁_le, hA_pos⟩ := h_consts C₁ (le_max_left 3 _)
  obtain ⟨hc_4p, hc_3p, nSeq, hn_strict, hn_ge2, h_inst⟩ := h_main p hp C hC
  refine ⟨c C₁, c₀ C₁, A C₁, β₁ C₁, β₂ C₁, hc_4p, hc_3p, hc₀_pos, hA_pos, hβ₁_pos, hβ₁_le,
    nSeq, hn_strict, hn_ge2, ?_⟩
  intro j
  obtain ⟨d, P, hd_pos, hd_lo, hd_hi, hP_bool, hP_inj, hP_ar, h_span⟩ := h_inst j
  refine ⟨d, P, hd_pos, hd_lo, hd_hi, hP_bool, hP_inj, hP_ar, ?_⟩
  intro G hGeom
  obtain ⟨H, w, hSpan, hEdge_le⟩ :=
    Geometry.geometric_spanner_to_steiner h_lp hp P C G hGeom
  exact le_trans (h_span PEmpty H w hSpan) hEdge_le
end HighDimSteinerSpanners.Proofs.Projection
