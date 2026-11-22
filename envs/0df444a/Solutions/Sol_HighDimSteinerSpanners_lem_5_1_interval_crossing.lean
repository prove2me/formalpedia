-- Prove2me | solution 1 for HighDimSteinerSpanners.lem_5_1_interval_crossing
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:53:39.722154+00:00
-- url     : https://prove2.me/submissions/0e5cba38-f62b-4ce6-a859-2a1577929845

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
public import Theorems.Thm_HighDimSteinerSpanners_Proofs_Glue_lem_5_1_proof


set_option autoImplicit true
@[expose] public section
public section
open scoped ENNReal
open HighDimSteinerSpanners
open HighDimSteinerSpanners
namespace HighDimSteinerSpanners
theorem _root_.solution :
    ∀ (α β : ℤ), 1 ≤ α → α ≤ β →
      ∀ (L R : ℤ → ℤ),
        (∀ s : ℤ, α ≤ s → s ≤ β →
          α - 1 ≤ L s ∧ L s ≤ s - 1 ∧ s ≤ R s ∧ R s ≤ β ∧ (L s, R s) ≠ (α - 1, β)) →
        ∃ s t : ℤ,
          α ≤ s ∧ s < t ∧ t ≤ β ∧
          L s < L t ∧ L t ≤ s ∧ t ≤ R s + 1 ∧ R s + 1 ≤ R t :=
  HighDimSteinerSpanners.Proofs.Glue.lem_5_1_proof
end HighDimSteinerSpanners
