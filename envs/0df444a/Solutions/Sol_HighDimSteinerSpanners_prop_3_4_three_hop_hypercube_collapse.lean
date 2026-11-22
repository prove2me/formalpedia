-- Prove2me | solution 1 for HighDimSteinerSpanners.prop_3_4_three_hop_hypercube_collapse
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:53:32.044936+00:00
-- url     : https://prove2.me/submissions/5ebda7a7-8b22-46b6-82da-e0d17cf07d29

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
public import Theorems.Thm_HighDimSteinerSpanners_Proofs_Hamming_prop_3_4_proof


set_option autoImplicit true
@[expose] public section
public section
open scoped ENNReal
open HighDimSteinerSpanners
open HighDimSteinerSpanners
namespace HighDimSteinerSpanners
theorem _root_.solution :
    ∀ (p : ℝ), 1 ≤ p →
      ((∀ ρ : ℝ, 0 < ρ → ρ < 1 →
        ∃ ε : ℝ, 0 < ε ∧
          ∀ d : ℕ, 1 ≤ d →
            ∀ P : Finset (Fin d → Bool),
              2 ≤ P.card →
              (2 : ℝ) ^ ((1 - ε) * (d : ℝ)) ≤ (P.card : ℝ) →
              (∃ (S : Finset (Fin d → Bool)),
                Disjoint P S ∧
                ∃ H : SimpleGraph ↥(P ∪ S),
                  let w := cubeSubgraphWeight p (P ∪ S)
                  Nat.card H.edgeSet ≤ 2 * P.card ∧
                  (∀ (x y : Fin d → Bool) (hx : x ∈ P) (hy : y ∈ P),
                    ENNReal.ofReal (cubeLpDist p x y) ≤
                      graphDist H w ⟨x, Finset.mem_union_left S hx⟩
                        ⟨y, Finset.mem_union_left S hy⟩) ∧
                  (∀ (x y : Fin d → Bool) (hx : x ∈ P) (hy : y ∈ P),
                    (1 : ℝ) / 3 * ρ * (d : ℝ) ≤ (hammingDist x y : ℝ) →
                    (hammingDist x y : ℝ) ≤ ρ * (d : ℝ) →
                    ∃ q : H.Walk ⟨x, Finset.mem_union_left S hx⟩
                        ⟨y, Finset.mem_union_left S hy⟩,
                      q.IsPath ∧ q.length ≤ 3 ∧
                      walkWeight w q ≤ 5760 * cubeLpDist p x y)) ∧
              ((∀ x ∈ P, ∀ y ∈ P, x ≠ y →
                  (1 : ℝ) / 3 * ρ * (d : ℝ) ≤ (hammingDist x y : ℝ)) →
                ∃ (S : Finset (Fin d → Bool)),
                  Disjoint P S ∧
                  ∃ H : SimpleGraph ↥(P ∪ S),
                    let w := cubeSubgraphWeight p (P ∪ S)
                    (Nat.card H.edgeSet : ℝ) ≤ 2 * (P.card : ℝ) * Real.logb 2 (2 / ρ) ∧
                    (∀ (x y : Fin d → Bool) (hx : x ∈ P) (hy : y ∈ P),
                      ENNReal.ofReal (cubeLpDist p x y) ≤
                        graphDist H w ⟨x, Finset.mem_union_left S hx⟩
                          ⟨y, Finset.mem_union_left S hy⟩) ∧
                    (∀ (x y : Fin d → Bool) (hx : x ∈ P) (hy : y ∈ P), x ≠ y →
                      ∃ q : H.Walk ⟨x, Finset.mem_union_left S hx⟩
                          ⟨y, Finset.mem_union_left S hy⟩,
                        q.IsPath ∧ q.length ≤ 3 ∧
                        walkWeight w q ≤ 5760 * cubeLpDist p x y))) ∧
      (∀ d : ℕ, 2 ≤ d →
        ∃ H : SimpleGraph (Fin d → Bool),
          let w : Sym2 (Fin d → Bool) → ℝ :=
            Sym2.lift ⟨fun u v => cubeLpDist p u v, fun u v => by
              simp only [cubeLpDist, lpDist, abs_sub_comm]⟩
          (Nat.card H.edgeSet : ℝ) ≤ 4 * (2 : ℝ) ^ d * Real.logb 2 (d : ℝ) ∧
          (∀ x y : Fin d → Bool, ENNReal.ofReal (cubeLpDist p x y) ≤ graphDist H w x y) ∧
          (∀ x y : Fin d → Bool, x ≠ y →
            ∃ q : H.Walk x y,
              q.IsPath ∧ q.length ≤ 3 ∧ walkWeight w q ≤ 5760 * cubeLpDist p x y))) :=
  HighDimSteinerSpanners.Proofs.Hamming.prop_3_4_proof
end HighDimSteinerSpanners
