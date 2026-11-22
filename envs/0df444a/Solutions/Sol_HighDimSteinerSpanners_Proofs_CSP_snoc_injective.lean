-- Prove2me | solution 1 for HighDimSteinerSpanners.Proofs.CSP.snoc_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:49:08.645953+00:00
-- url     : https://prove2.me/submissions/7146118a-c784-44b6-9695-56397eb5d8f0

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
theorem _root_.solution {β : Type} [DecidableEq β] (Pool : Finset β) : ∀ (m : ℕ) (z_prev : Fin m → β),
    Function.Injective z_prev →
    ∀ b ∈ Pool \ Finset.univ.image z_prev,
    Function.Injective (Fin.snoc z_prev b) := by
  intro m z_prev hinj b hb u₁ u₂ heq
  have hb_fresh : b ∉ Finset.univ.image z_prev := (Finset.mem_sdiff.mp hb).2
  revert heq
  refine Fin.lastCases ?_ (fun i₁ => ?_) u₁
  · refine Fin.lastCases ?_ (fun i₂ => ?_) u₂
    · intro _
      rfl
    · intro heq
      rw [Fin.snoc_last, Fin.snoc_castSucc] at heq
      exact absurd (Finset.mem_image.mpr ⟨i₂, Finset.mem_univ i₂, heq.symm⟩) hb_fresh
  · refine Fin.lastCases ?_ (fun i₂ => ?_) u₂
    · intro heq
      rw [Fin.snoc_castSucc, Fin.snoc_last] at heq
      exact absurd (Finset.mem_image.mpr ⟨i₁, Finset.mem_univ i₁, heq⟩) hb_fresh
    · intro heq
      rw [Fin.snoc_castSucc, Fin.snoc_castSucc] at heq
      exact congr_arg Fin.castSucc (hinj heq)
end HighDimSteinerSpanners.Proofs.CSP
