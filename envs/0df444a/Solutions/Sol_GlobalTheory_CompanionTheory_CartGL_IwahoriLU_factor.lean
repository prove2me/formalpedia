-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.CartGL.IwahoriLU.factor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:21:41.181315+00:00
-- url     : https://prove2.me/submissions/a0e1cf19-63f0-4886-9745-3bbdda0eb591

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_EntryMulSubOne
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_FactorizationBis
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_NearIdentityUpperLowerFactorization
import Theorems.Thm_UpperTheory_Reformulated_B_TriangularFactorizationNearIdentity_factor


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.CartGL GlobalTheory.CompanionTheory.CartGL.IwahoriLU
variable {L : Type} [NontriviallyNormedField L] [IsUltrametricDist L] {n : ℕ}
namespace GlobalTheory.CompanionTheory.CartGL.IwahoriLU
theorem _root_.solution (n : ℕ) (r : ℝ) (h0 : 0 ≤ r) (h1 : r < 1) :
    ∀ A : Matrix (Fin n) (Fin n) L, (∀ i j, ‖(A - 1) i j‖ ≤ r) →
      ∃ U W : Matrix (Fin n) (Fin n) L, (∀ i j, j < i → U i j = 0) ∧ (∀ i j, i < j → W i j = 0) ∧
        (∀ i j, ‖(U - 1) i j‖ ≤ r) ∧ (∀ i j, ‖(W - 1) i j‖ ≤ r) ∧ A = U * W :=
  _root_.UpperTheory.Reformulated.B.TriangularFactorizationNearIdentity.factor n r h0 h1
end GlobalTheory.CompanionTheory.CartGL.IwahoriLU
