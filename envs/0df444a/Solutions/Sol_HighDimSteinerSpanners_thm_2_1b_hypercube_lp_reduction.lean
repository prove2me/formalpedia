-- Prove2me | solution 1 for HighDimSteinerSpanners.thm_2_1b_hypercube_lp_reduction
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:53:29.099028+00:00
-- url     : https://prove2.me/submissions/4d9212d5-927f-4610-8f4b-2e54951d5188

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
public import Theorems.Thm_HighDimSteinerSpanners_Proofs_Projection_thm_2_1b_proof


set_option autoImplicit true
@[expose] public section
public section
open scoped ENNReal
open HighDimSteinerSpanners
open HighDimSteinerSpanners
namespace HighDimSteinerSpanners
theorem _root_.solution :
    ∀ (N q L rStar C₁ : ℕ), 2 ≤ N → 2 ≤ q → 1 ≤ rStar → N = 2 ^ L * rStar →
      ∀ (p C : ℝ), 1 ≤ p → 1 ≤ C → ⌈C ^ p⌉₊ ≤ C₁ →
        (∀ x y : Fin N → Fin q,
          lpDist p (oneHotEmbed x) (oneHotEmbed y) = (2 * (hammingDist x y : ℝ)) ^ (1 / p)) ∧
        (∀ (X : Finset (Fin N → Fin q)),
          2 ≤ X.card →
          (∀ x ∈ X, ∀ y ∈ X, x ≠ y → (rStar : ℝ) / 2 ≤ (hammingDist x y : ℝ)) →
          ∀ (e : Fin X.card ≃ ↥X),
            let P : Fin X.card → (Fin (N * q) → ℝ) := fun i => oneHotEmbed (e i).val
            (∀ i : Fin X.card, ∀ k : Fin (N * q), P i k = 0 ∨ P i k = 1) ∧
            Function.Injective P ∧
            aspectRatio p P ≤ (2 : ℝ) ^ (L + 1) ∧
            ∀ (S : Type) [Fintype S]
              (H : SimpleGraph (Fin X.card ⊕ S))
              (w : Sym2 (Fin X.card ⊕ S) → ℝ),
              IsNonMetricSteinerSpanner p P C H w →
              ∃ G_hat : SimpleGraph ↥X,
                Nat.card G_hat.edgeSet ≤ Nat.card H.edgeSet ∧
                (∀ a b : ↥X, G_hat.Adj a b →
                  0 < hammingDist a.val b.val ∧ hammingDist a.val b.val ≤ C₁ * rStar) ∧
                (∀ x y : ↥X, hammingDist x.val y.val = rStar →
                  ∃ q_walk : G_hat.Walk x y,
                    q_walk.IsPath ∧
                    ∀ z ∈ q_walk.support, hammingDist x.val z.val ≤ C₁ * rStar)) :=
  HighDimSteinerSpanners.Proofs.Projection.thm_2_1b_proof
end HighDimSteinerSpanners
