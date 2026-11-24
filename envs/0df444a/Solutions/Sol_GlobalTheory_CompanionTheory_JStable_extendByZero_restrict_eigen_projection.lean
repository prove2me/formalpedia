-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.JStable.extendByZero_restrict_eigen_projection
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T13:08:21.480315+00:00
-- url     : https://prove2.me/submissions/e9844198-0771-487d-99c9-7ea8d5432975

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
theorem _root_.solution (s : Bool) (v : Fin n → ℂ) :
    ext0 ε s (res0 ε s v) =
      (1 / 2 : ℂ) • (v + (if s then (1 : ℂ) else -1) • (Formalism.REAL.Jm ε *ᵥ v)) := by
  funext a
  have hJ : (Formalism.REAL.Jm ε *ᵥ v) a = (if ε a then 1 else -1) * v a := by
    simp [Formalism.REAL.Jm, Matrix.mulVec_diagonal]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hJ, ext0, LinearMap.coe_mk, AddHom.coe_mk, res0]
  cases s <;> cases h : ε a <;> simp <;> ring
end GlobalTheory.CompanionTheory.JStable
