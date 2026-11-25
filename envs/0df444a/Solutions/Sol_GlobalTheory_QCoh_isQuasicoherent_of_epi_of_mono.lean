-- Prove2me | solution 1 for GlobalTheory.QCoh.isQuasicoherent_of_epi_of_mono
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T18:06:27.127835+00:00
-- url     : https://prove2.me/submissions/ed301296-a1a8-4ec8-b0e5-e33c622254f1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsQuasicoherentOfForallExistsAffine
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExactAndSurjectiveAppOfExactOfEpi

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite
universe w' w u
noncomputable section
open GlobalTheory GlobalTheory.QCoh
variable {X : Scheme.{u}} {M N P : X.Modules} {U V : X.Opens}
namespace GlobalTheory.QCoh
theorem _root_.solution {I : X.Modules} (e : M ⟶ I) (m : I ⟶ N) [Epi e] [Mono m]
    [M.IsQuasicoherent] [N.IsQuasicoherent] : I.IsQuasicoherent :=
  haveI := strongEpi_of_epi e
  isQuasicoherent_of_iso (image.isoStrongEpiMono e m rfl).symm
end GlobalTheory.QCoh
