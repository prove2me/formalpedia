-- Prove2me | solution 1 for GlobalTheory.T.exists_isotropic_idempotent_centralizer_hermitian
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:08:13.982049+00:00
-- url     : https://prove2.me/submissions/a9fd1d97-42a9-49bf-b4a8-41bf653efd3c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsIsotropicIdempotentCentralizerHermitian
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsIsotropicIdempotentCentralizerHermitianStatement
import Theorems.Thm_GlobalTheory_IsoIdem_isoIdem


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (E : Type) [Field E] [StarRing E] (r : ℕ) (A₀ : Matrix (Fin r) (Fin r) E), A₀.IsHermitian → A₀.charpoly.Separable → ∃ f : Matrix (Fin r) (Fin r) E, f * A₀ = A₀ * f ∧ f * f = f ∧ f * star f = 0 ∧ ∀ y : Matrix (Fin r) (Fin r) E, y * A₀ = A₀ * y → y * (1 - f - star f) * star (y * (1 - f - star f)) = 0 → y * (1 - f - star f) = 0 := by
  first | exact @GlobalTheory.IsoIdem.isoIdem | exact GlobalTheory.IsoIdem.isoIdem | (intros; apply GlobalTheory.IsoIdem.isoIdem <;> assumption)
end _root_.GlobalTheory.T
