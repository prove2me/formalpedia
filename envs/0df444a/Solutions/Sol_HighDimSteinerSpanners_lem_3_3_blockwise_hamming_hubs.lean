-- Prove2me | solution 1 for HighDimSteinerSpanners.lem_3_3_blockwise_hamming_hubs
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:53:41.340149+00:00
-- url     : https://prove2.me/submissions/5ab13e9d-2446-4be7-9209-98211341d493

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
public import Theorems.Thm_HighDimSteinerSpanners_Proofs_Hamming_lem_3_3_proof


set_option autoImplicit true
@[expose] public section
public section
open scoped ENNReal
open HighDimSteinerSpanners
open HighDimSteinerSpanners
namespace HighDimSteinerSpanners
theorem _root_.solution :
    ∀ (r d : ℕ), 4 ≤ r → 1 ≤ d →
      ∀ (p : ℝ), 1 ≤ p →
        let b_r : ℝ := (2 : ℝ) ^ r - 1
        let ρ_r : ℝ := 1 / (64 * b_r)
        ∀ (P : Finset (Fin d → Bool)),
          2 ≤ P.card →
          (2 : ℝ) ^ ((1 - (r : ℝ) / (2 * b_r)) * (d : ℝ)) ≤ (P.card : ℝ) →
          ∃ (S_r : Finset (Fin d → Bool)),
            Disjoint P S_r ∧
            ∃ (H_r : SimpleGraph ↥(P ∪ S_r)),
              let w := cubeSubgraphWeight p (P ∪ S_r)
              Nat.card H_r.edgeSet ≤ 2 * P.card ∧
              (∀ (x y : Fin d → Bool) (hx : x ∈ P) (hy : y ∈ P),
                ENNReal.ofReal (cubeLpDist p x y) ≤
                  graphDist H_r w ⟨x, Finset.mem_union_left S_r hx⟩
                    ⟨y, Finset.mem_union_left S_r hy⟩) ∧
              (∀ (x y : Fin d → Bool) (hx : x ∈ P) (hy : y ∈ P),
                (1 : ℝ) / 3 * ρ_r * (d : ℝ) ≤ (hammingDist x y : ℝ) →
                (hammingDist x y : ℝ) ≤ (9 : ℝ) / 4 * ρ_r * (d : ℝ) →
                ∃ q : H_r.Walk ⟨x, Finset.mem_union_left S_r hx⟩
                    ⟨y, Finset.mem_union_left S_r hy⟩,
                  q.IsPath ∧ q.length ≤ 3 ∧ walkWeight w q ≤ 387 * cubeLpDist p x y) :=
  HighDimSteinerSpanners.Proofs.Hamming.lem_3_3_proof
end HighDimSteinerSpanners
