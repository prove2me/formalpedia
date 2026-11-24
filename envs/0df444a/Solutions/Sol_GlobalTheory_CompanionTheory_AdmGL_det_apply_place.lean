-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.AdmGL.det_apply_place
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:17:01.022849+00:00
-- url     : https://prove2.me/submissions/3682ccbb-399b-4f4c-9d0f-4e2bf4cb1b83

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_BlkConjTranspose

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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.AdmGL
variable {ι : Type} [Fintype ι] [DecidableEq ι] {a n : ℕ}
namespace GlobalTheory.CompanionTheory.AdmGL
theorem _root_.solution (M : Matrix (Fin a) (Fin a) (ι → ℂ)) (w : ι) : M.det w = (atPlace M w).det :=
  RingHom.map_det (Pi.evalRingHom (fun _ : ι => ℂ) w) M
end GlobalTheory.CompanionTheory.AdmGL
