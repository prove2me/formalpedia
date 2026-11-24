-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.JStable.eq_extendByZero_restrict_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T13:01:43.035566+00:00
-- url     : https://prove2.me/submissions/d6980aae-5d8e-4fe0-9198-04ad17e851ea

import Mathlib
import Definitions.Def_Formalism_RealPlaceAnalysis_SmoothOnGVIff
import Definitions.Def_Formalism_FormalDegreeBessel_StatementG
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_ExistsOrthogonalHermitianSubspace

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.JStable
variable {n : ℕ} (ε : Fin n → Bool)
namespace GlobalTheory.CompanionTheory.JStable
theorem _root_.solution (v : Fin n → ℂ) :
    v = ext0 ε true (res0 ε true v) + ext0 ε false (res0 ε false v) := by
  funext a
  simp only [Pi.add_apply, ext0, LinearMap.coe_mk, AddHom.coe_mk, res0]
  cases h : ε a <;> simp
end GlobalTheory.CompanionTheory.JStable
