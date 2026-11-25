-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.orbit_rep_lift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T14:41:37.307335+00:00
-- url     : https://prove2.me/submissions/dc5310ea-ea22-4276-a6c1-74cc4c88a2ff

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_FiniteMinimalPrimes
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_SncResolutionCoverAndCone
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_Cmp_SncRes_lift_vec
import Theorems.Thm_ReciprocityTheory_AnForm_R_sameOrbit_affCoord


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.Cmp.SncRes
open MvPolynomial ReciprocityTheory.AnForm.R
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
namespace GlobalTheory.CompanionTheory.Ar.Cmp.SncRes
theorem _root_.solution {P : Ideal (MvPolynomial (Σ k, ι k) ℂ)} (p : (k : K) → ι k) (x : Pts P)
    (hx : x ∈ src P p) :
    SameOrbit (rep x) (fun q => eval (coord P p x) (lift p q)) := by
  rw [lift_vec p x hx]
  exact sameOrbit_affCoord p (rep x) hx
end GlobalTheory.CompanionTheory.Ar.Cmp.SncRes
