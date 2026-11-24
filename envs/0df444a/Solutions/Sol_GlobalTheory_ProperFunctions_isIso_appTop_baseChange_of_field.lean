-- Prove2me | solution 1 for GlobalTheory.ProperFunctions.isIso_appTop_baseChange_of_field
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T20:28:29.197709+00:00
-- url     : https://prove2.me/submissions/435ec3e5-6ea0-4ada-853e-f2acca08d43a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsIsoAppTopOfIsPullbackOfSurjective
import Theorems.Thm_GlobalTheory_ProperFunctions_isIso_appTop_of_isPullback
import Theorems.Thm_GlobalTheory_ProperFunctions_isIso_appTop_of_field

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits AlgebraicGeometry TensorProduct Opposite
universe u
open GlobalTheory
open GlobalTheory.ProperFunctions
variable {X Y S T : Scheme.{u}}
namespace GlobalTheory.ProperFunctions
theorem _root_.solution {k : Type u} [Field k] {p : X ⟶ Spec (.of k)}
    {f : T ⟶ Spec (.of k)} {g : Y ⟶ X} {q : Y ⟶ T} (H : IsPullback g q p f) [IsAffine T]
    [GeometricallyIntegral p] [UniversallyClosed p] [QuasiSeparated p] : IsIso q.appTop :=
  have := isIso_appTop_of_field p
  isIso_appTop_of_isPullback H
end GlobalTheory.ProperFunctions
