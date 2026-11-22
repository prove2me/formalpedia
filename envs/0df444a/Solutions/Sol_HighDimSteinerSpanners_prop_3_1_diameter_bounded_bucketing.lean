-- Prove2me | solution 1 for HighDimSteinerSpanners.prop_3_1_diameter_bounded_bucketing
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:53:31.261174+00:00
-- url     : https://prove2.me/submissions/3d799c0b-1846-4b7c-8fa0-25d058e611c9

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
public import Theorems.Thm_HighDimSteinerSpanners_Proofs_Bucketing_prop_3_1_proof


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
      ∀ (C : ℝ), 1 ≤ C →
        ∀ (I : Type) [Fintype I] (B : I → Finset P),
          (∀ i : I, 2 ≤ (B i).card) →
          (Nat.card (bucketingGraph B).edgeSet = ∑ i : I, (B i).card ∧
            ∀ x y : P,
              ENNReal.ofReal (dist x y) ≤
                graphDist (bucketingGraph B) (bucketingWeight B) (.inl x) (.inl y)) ∧
          ((∀ x y : P, x ≠ y → ∃ i : I, x ∈ B i ∧ y ∈ B i ∧ bucketDiam (B i) ≤ C * dist x y) →
            IsGeneralNonMetricSteinerSpanner C (bucketingGraph B) (bucketingWeight B) ∧
            ∀ x y : P, x ≠ y →
              ∃ q : (bucketingGraph B).Walk (.inl x) (.inl y),
                q.IsPath ∧ q.length ≤ 2 ∧
                walkWeight (bucketingWeight B) q ≤ C * dist x y) :=
  HighDimSteinerSpanners.Proofs.Bucketing.prop_3_1_proof
end HighDimSteinerSpanners
