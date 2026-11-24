-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.GapPolyProof.dd_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:48:33.498873+00:00
-- url     : https://prove2.me/submissions/bfdc426f-9fac-4656-9f0c-6377d1896729

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ResidualSpectrum_ExponentialNegativity_GapAbsOf
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CountLeOfDvd
import Theorems.Thm_GlobalTheory_CompanionTheory_GapPolyProof_dd_step

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Polynomial
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.GapPolyProof
variable {E : Type*} [AddCommGroup E] [Module ℂ E]
namespace GlobalTheory.CompanionTheory.GapPolyProof
theorem _root_.solution (S : Multiset ℂ) (n : ℕ) (hS : Multiset.card S = n + 1) (T : Module.End ℂ E) (v : ℕ → E) (x : E)
    (h0 : v 0 = x) (hn : v (n + 1) = 0)
    (hrec : ∀ j ≤ n, v (j + 1) - T (v j) = (((-1 : ℂ) ^ (j + 1)) * S.esymm (j + 1)) • x) (k : ℕ) :
    ∀ ψ : E →ₗ[ℂ] ℂ, (S.map (fun t => X - C t)).prod ∣ X ^ k * dd n v ψ - dd n v (ψ ∘ₗ (T ^ k)) := by
  induction k with
  | zero => intro ψ; simp [Module.End.one_eq_id]
  | succ k ih =>
    intro ψ
    have e : ψ ∘ₗ (T ^ (k + 1)) = (ψ ∘ₗ (T ^ k)) ∘ₗ T := by
      rw [pow_succ]; rfl
    have : X ^ (k + 1) * dd n v ψ - dd n v (ψ ∘ₗ (T ^ (k + 1))) =
        X * (X ^ k * dd n v ψ - dd n v (ψ ∘ₗ (T ^ k))) +
          (X * dd n v (ψ ∘ₗ (T ^ k)) - dd n v ((ψ ∘ₗ (T ^ k)) ∘ₗ T)) := by
      rw [e]; ring
    rw [this, dd_step S n hS T v x h0 hn hrec]
    exact dvd_add (Dvd.dvd.mul_left (ih ψ) _) (Dvd.intro_left _ rfl)
end GlobalTheory.CompanionTheory.GapPolyProof
