-- Prove2me | solution 1 for GlobalTheory.QCoh.shortExact_map_pushforward
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T07:42:57.756257+00:00
-- url     : https://prove2.me/submissions/62ee755c-76d6-4f8a-b27d-f25d7feb3844

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsQuasicoherentOfForallExistsAffine
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_RestrictPullbackIsoHomAppPullbackSections
import Theorems.Thm_GlobalTheory_QCoh_epi_pushforward_map

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite TensorProduct
universe u
noncomputable section
open GlobalTheory GlobalTheory.QCoh
variable {X Y : Scheme.{u}} {F F' : X.Modules}
variable (f : X ⟶ Y)
namespace GlobalTheory.QCoh
theorem _root_.solution [IsAffineHom f] {S : ShortComplex X.Modules}
    (hS : S.ShortExact) [S.X₂.IsQuasicoherent] [S.X₃.IsQuasicoherent] :
    (S.map (Scheme.Modules.pushforward f)).ShortExact := by
  have := hS.mono_f
  have := hS.epi_g
  exact ShortComplex.ShortExact.mk'
    (hS.exact.map_of_mono_of_preservesKernel _ hS.mono_f inferInstance)
    (inferInstanceAs (Mono ((Scheme.Modules.pushforward f).map S.f))) (epi_pushforward_map f S.g)
end GlobalTheory.QCoh
