-- Prove2me | solution 1 for HighDimSteinerSpanners.thm_2_1a_metric_nearest_terminal_projection
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:53:50.505449+00:00
-- url     : https://prove2.me/submissions/52bfaed5-9a76-49af-b408-838a49b52d7e

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
public import Theorems.Thm_HighDimSteinerSpanners_Proofs_Projection_thm_2_1a_proof


set_option autoImplicit true
@[expose] public section
public section
open scoped ENNReal
open HighDimSteinerSpanners
open HighDimSteinerSpanners
namespace HighDimSteinerSpanners
theorem _root_.solution :
    ∀ (P : Type) [MetricSpace P] [Fintype P],
      2 ≤ Fintype.card P →
      ∀ (C r : ℝ), 1 ≤ C → 0 < r →
        ∀ (S : Type) [Fintype S]
          (H : SimpleGraph (P ⊕ S)) (w : Sym2 (P ⊕ S) → ℝ),
          IsGeneralNonMetricSteinerSpanner C H w →
          ∃ G_hat : SimpleGraph P,
            Nat.card G_hat.edgeSet ≤ Nat.card H.edgeSet ∧
            (∀ a b : P, G_hat.Adj a b → 0 < dist a b ∧ dist a b ≤ C * r) ∧
            (∀ x y : P, 0 < dist x y → dist x y ≤ r →
              ∃ q : G_hat.Walk x y, q.IsPath ∧ ∀ z ∈ q.support, dist x z ≤ C * r) :=
  HighDimSteinerSpanners.Proofs.Projection.thm_2_1a_proof
end HighDimSteinerSpanners
