-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.GapPolyProof.dd_aeval
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T13:05:20.349986+00:00
-- url     : https://prove2.me/submissions/1611b862-2b48-4684-80db-15b58a32c9a6

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ResidualSpectrum_ExponentialNegativity_GapAbsOf
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CountLeOfDvd
import Theorems.Thm_GlobalTheory_CompanionTheory_GapPolyProof_dd_add
import Theorems.Thm_GlobalTheory_CompanionTheory_GapPolyProof_dd_smul
import Theorems.Thm_GlobalTheory_CompanionTheory_GapPolyProof_dd_pow

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
    (hrec : ∀ j ≤ n, v (j + 1) - T (v j) = (((-1 : ℂ) ^ (j + 1)) * S.esymm (j + 1)) • x) (p : ℂ[X])
    (ψ : E →ₗ[ℂ] ℂ) :
    (S.map (fun t => X - C t)).prod ∣ p * dd n v ψ - dd n v (ψ ∘ₗ (aeval T p)) := by
  induction p using Polynomial.induction_on' with
  | add p r hp hr =>
    have : (p + r) * dd n v ψ - dd n v (ψ ∘ₗ (aeval T (p + r))) =
        (p * dd n v ψ - dd n v (ψ ∘ₗ (aeval T p))) + (r * dd n v ψ - dd n v (ψ ∘ₗ (aeval T r))) := by
      rw [map_add, LinearMap.comp_add, dd_add]; ring
    rw [this]; exact dvd_add hp hr
  | monomial k a =>
    have e : ψ ∘ₗ (aeval T (monomial k a)) = a • (ψ ∘ₗ (T ^ k)) := by
      rw [aeval_monomial]
      ext y
      simp [Algebra.algebraMap_eq_smul_one]
    have : monomial k a * dd n v ψ - dd n v (ψ ∘ₗ (aeval T (monomial k a))) =
        C a * (X ^ k * dd n v ψ - dd n v (ψ ∘ₗ (T ^ k))) := by
      rw [e, dd_smul, ← C_mul_X_pow_eq_monomial]; ring
    rw [this]
    exact Dvd.dvd.mul_left (dd_pow S n hS T v x h0 hn hrec k ψ) _
end GlobalTheory.CompanionTheory.GapPolyProof
