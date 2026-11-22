-- Prove2me | solution 1 for HighDimSteinerSpanners.Proofs.CSP.candMFresh_subset_union
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:48:38.080617+00:00
-- url     : https://prove2.me/submissions/92a9649d-2910-43ff-8814-5061a372635c

module
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.NormNum
public import Definitions.Def_LeanPool_SteinerSpanners_CSP_CalibrationBounds
public import Definitions.Def_LeanPool_SteinerSpanners_CSP_WitnessCardinality

set_option autoImplicit true
@[expose] public section
public section
open scoped ENNReal
open HighDimSteinerSpanners
open HighDimSteinerSpanners HighDimSteinerSpanners.Proofs HighDimSteinerSpanners.Proofs.CSP
noncomputable section
namespace HighDimSteinerSpanners.Proofs.CSP
theorem _root_.solution {N q : ℕ} (a b : Fin N → Fin q)
    (m : ℕ) (z_prev : Fin m → (Fin N → Fin q)) (x : Fin N → Fin q) :
    candMFresh a b m z_prev x ⊆ disagreeSet x a ∪ disagreeSet x b := by
  intro v hv
  simp only [candMFresh, cspRvc, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_union, Finset.mem_image] at hv
  simp only [disagreeSet, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
  exact Or.inl (fun hxa => hv (Or.inl (Or.inl ⟨v, hxa.symm ▸ rfl⟩)))
end HighDimSteinerSpanners.Proofs.CSP
