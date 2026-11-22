-- Prove2me | solution 1 for HighDimSteinerSpanners.Proofs.CSP.bernWeight_nonnegative
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:49:10.675274+00:00
-- url     : https://prove2.me/submissions/53472def-6d46-4197-b74d-099cfa04c8ac

module
public import Mathlib.Tactic.Ring
public import Definitions.Def_LeanPool_SteinerSpanners_CSP_WitnessProjection
public import Definitions.Def_LeanPool_SteinerSpanners_CSP_Bernoulli

set_option autoImplicit true
@[expose] public section
public section
open scoped ENNReal
open HighDimSteinerSpanners
open HighDimSteinerSpanners HighDimSteinerSpanners.Proofs HighDimSteinerSpanners.Proofs.CSP
noncomputable section
namespace HighDimSteinerSpanners.Proofs.CSP
theorem _root_.solution {ι : Type} [Fintype ι] (p : ι → ℝ)
  (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1) : ∀ ω : ι → Bool, 0 ≤ bernWeight p ω := by
  intro ω
  unfold bernWeight
  refine Finset.prod_nonneg (fun i _ => ?_)
  split_ifs
  · exact (hp i).1
  · exact sub_nonneg.mpr (hp i).2
end HighDimSteinerSpanners.Proofs.CSP
