-- Prove2me | solution 1 for HighDimSteinerSpanners.lem_6_3_biclique_list_hit
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:54:27.38395+00:00
-- url     : https://prove2.me/submissions/6d52530e-be01-4154-89ae-9a5aaae1fdec

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
public import Theorems.Thm_HighDimSteinerSpanners_thm_2_2b_biclique_bottleneck
public import Theorems.Thm_HighDimSteinerSpanners_Proofs_Glue_lem_6_3_from_2_2b


set_option autoImplicit true
@[expose] public section
public section
open scoped ENNReal
open HighDimSteinerSpanners
open HighDimSteinerSpanners
namespace HighDimSteinerSpanners
theorem _root_.solution :
    ∀ (N q C₁ rStar : ℕ), 2 ≤ N → 2 ≤ q → 3 ≤ C₁ → 1 ≤ rStar →
      ∀ (R : Fin N → Fin N → Fin q → Fin q → Prop),
        Symmetric2CSP R →
        ∀ (X : Finset (Fin N → Fin q)),
          X ⊆ satisfyingSet R →
          let η₀ : ℝ := 1 / 80
          (∀ x ∈ X, ∀ u ∈ X, ∀ z ∈ satisfyingSet R,
            hammingDist x u ≤ C₁ * rStar →
            hammingDist x z ≤ C₁ * rStar →
            ((threeWayDisagree x u z).card : ℝ) ≤ η₀ * (rStar : ℝ)) →
          let L_X : ↥X → ↥X → Finset ↥X := fun a b =>
            if 0 < hammingDist a.val b.val ∧ hammingDist a.val b.val ≤ C₁ * rStar then
              Finset.univ.filter (fun x : ↥X => x.val ∈ bicliqueWitnessList R C₁ rStar a.val b.val)
            else ∅
          ListHitCond C₁ rStar X L_X :=
  HighDimSteinerSpanners.Proofs.Glue.lem_6_3_from_2_2b thm_2_2b_biclique_bottleneck
end HighDimSteinerSpanners
