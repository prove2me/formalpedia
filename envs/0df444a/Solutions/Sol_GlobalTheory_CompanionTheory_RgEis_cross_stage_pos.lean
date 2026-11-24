-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.RgEis.cross_stage_pos
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T13:03:13.808948+00:00
-- url     : https://prove2.me/submissions/e062edee-efdd-4d01-9bdd-3ec59b018968

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_StripEntire
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CosetSeriesSummableShifted

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.RgEis
open PositivityTheory.RgEis
namespace GlobalTheory.CompanionTheory.RgEis
theorem _root_.solution : PositivityTheory.RgEis.PiLocalization₂ → ∀ (G : Type) [Group G] (Γ Q P : Subgroup G) (ξ lam : G → ℝ) (t : ℝ),
    P ≤ Q → (∀ γ ∈ Γ, γ ∈ Q → ∀ x, ξ (γ * x) = ξ x) → (∀ γ ∈ Γ, γ ∈ P → ∀ x, lam (γ * x) = lam x) →
    PositivityTheory.RgEis.Conv Γ P (fun x => lam x + t * ξ x) → ∀ g : G,
    Summable fun r : PositivityTheory.RgEis.Cos (Γ ⊓ Q) Γ => Real.exp (t * ξ (PositivityTheory.RgEis.rep r * g)) *
      PositivityTheory.RgEis.pos (Γ ⊓ Q) P lam (PositivityTheory.RgEis.rep r * g) := by
  intro hS G _ Γ Q P ξ lam t hPQ hξ hlam hc g
  have key := (hS G ℝ P (Γ ⊓ Q) Γ (fun x => Real.exp (lam x + t * ξ x)) inf_le_left
    (fun γ h1 h2 => ⟨h1, hPQ h2⟩)
    (fun γ h1 h2 x => by
      show Real.exp (lam (γ * x) + t * ξ (γ * x)) = Real.exp (lam x + t * ξ x)
      rw [hlam γ h1 h2 x, hξ γ h1 (hPQ h2) x]) g
    (by
      have h := hc g
      refine h.congr (fun q => ?_)
      simp only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)])).2.1
  refine key.congr (fun r => ?_)
  rw [pos, ← tsum_mul_left]
  refine tsum_congr (fun q => ?_)
  have hq : rep q ∈ Γ ⊓ Q := (Quotient.out q).2
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), hξ _ hq.1 hq.2, ← Real.exp_add, add_comm]
end GlobalTheory.CompanionTheory.RgEis
