-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.GapPolyProof.dvd_minpoly_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T13:21:25.713962+00:00
-- url     : https://prove2.me/submissions/c627aa7d-7766-477a-ab3d-30ccdda3b128

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ResidualSpectrum_ExponentialNegativity_GapAbsOf
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CountLeOfDvd
import Theorems.Thm_GlobalTheory_CompanionTheory_GapPolyProof_dd_zero
import Theorems.Thm_GlobalTheory_CompanionTheory_GapPolyProof_dd_aeval

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
theorem _root_.solution [FiniteDimensional ℂ E] (S : Multiset ℂ) (n : ℕ) (hS : Multiset.card S = n + 1)
    (T : Module.End ℂ E) (v : ℕ → E) (x : E)
    (h0 : v 0 = x) (hn : v (n + 1) = 0)
    (hrec : ∀ j ≤ n, v (j + 1) - T (v j) = (((-1 : ℂ) ^ (j + 1)) * S.esymm (j + 1)) • x)
    (ψ : E →ₗ[ℂ] ℂ) :
    (S.map (fun t => X - C t)).prod ∣ minpoly ℂ T * dd n v ψ := by
  have h := dd_aeval S n hS T v x h0 hn hrec (minpoly ℂ T) ψ
  rwa [minpoly.aeval, LinearMap.comp_zero, dd_zero, sub_zero] at h
end GlobalTheory.CompanionTheory.GapPolyProof
