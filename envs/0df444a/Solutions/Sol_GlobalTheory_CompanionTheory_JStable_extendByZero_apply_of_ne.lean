-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.JStable.extendByZero_apply_of_ne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:57:44.973933+00:00
-- url     : https://prove2.me/submissions/cdf989d2-460b-4de7-bcb8-3ebf6ba6166b

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
theorem _root_.solution {s : Bool} (x : EuclideanSpace ℂ {i : Fin n // ε i = s}) {a : Fin n}
    (h : ε a ≠ s) : ext0 ε s x a = 0 := by
  simp only [ext0, LinearMap.coe_mk, AddHom.coe_mk, dif_neg h]
end GlobalTheory.CompanionTheory.JStable
