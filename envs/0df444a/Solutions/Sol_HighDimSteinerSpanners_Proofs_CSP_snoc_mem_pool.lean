-- Prove2me | solution 1 for HighDimSteinerSpanners.Proofs.CSP.snoc_mem_pool
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:49:26.873721+00:00
-- url     : https://prove2.me/submissions/5fc13cde-b85e-4ea6-9b14-eb3ce1da0fef

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
theorem _root_.solution {β : Type} (Pool : Finset β) : ∀ (m : ℕ) (z_prev : Fin m → β),
    (∀ t : Fin m, z_prev t ∈ Pool) →
    ∀ b ∈ Pool, ∀ u : Fin (m + 1), (Fin.snoc z_prev b : Fin (m + 1) → β) u ∈ Pool := by
  intro m z_prev hz_pool b hb
  refine Fin.lastCases ?_ (fun i => ?_)
  · simpa [Fin.snoc_last] using hb
  · simpa [Fin.snoc_castSucc] using hz_pool i
end HighDimSteinerSpanners.Proofs.CSP
