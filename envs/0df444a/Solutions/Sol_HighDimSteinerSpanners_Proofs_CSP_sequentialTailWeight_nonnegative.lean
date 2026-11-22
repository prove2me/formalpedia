-- Prove2me | solution 1 for HighDimSteinerSpanners.Proofs.CSP.sequentialTailWeight_nonnegative
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:49:20.351714+00:00
-- url     : https://prove2.me/submissions/9aa013d8-843d-4b6e-87a8-282e5ca9412f

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
theorem _root_.solution {ι β γ : Type} [Fintype ι] [DecidableEq ι]
  [DecidableEq β] (p : ι → ℝ) (Pool : Finset β)
  (M_wit : (m : ℕ) → (Fin m → β) → β → Finset γ)
  (Q : (m : ℕ) → (Fin m → β) → β → γ → Finset ι)
  (hW_nn : ∀ ω, 0 ≤ bernWeight p ω) : ∀ (r m : ℕ) (z_prev : Fin m → β) (Acc : Finset ι) (ω : ι →
      Bool),
    0 ≤ sequentialTailWeight p Pool M_wit Q r m z_prev Acc ω := by
  intro r
  induction r with
  | zero =>
    intro m z_prev Acc ω
    dsimp [sequentialTailWeight]
    split_ifs
    · exact hW_nn ω
    · exact le_rfl
  | succ r ih =>
    intro m z_prev Acc ω
    dsimp [sequentialTailWeight]
    exact Finset.sum_nonneg (fun b _ =>
      Finset.sum_nonneg (fun w _ => ih (m + 1) (Fin.snoc z_prev b) (Acc ∪ Q m z_prev b w) ω))
end HighDimSteinerSpanners.Proofs.CSP
