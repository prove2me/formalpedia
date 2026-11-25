-- Prove2me | solution 1 for GlobalTheory.QCoh.exact_map_pullback
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T05:56:34.606479+00:00
-- url     : https://prove2.me/submissions/23416cbc-1b1c-42b7-a500-21ee088d212c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsQuasicoherentOfForallExistsAffine
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_RestrictPullbackIsoHomAppPullbackSections

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
theorem _root_.solution {S : ShortComplex Y.Modules} (hS : S.Exact) [Epi S.g] :
    (S.map (Scheme.Modules.pullback f)).Exact ∧ Epi (S.map (Scheme.Modules.pullback f)).g :=
  ⟨hS.map_of_epi_of_preservesCokernel _ inferInstance inferInstance,
    inferInstanceAs (Epi ((Scheme.Modules.pullback f).map S.g))⟩
end GlobalTheory.QCoh
