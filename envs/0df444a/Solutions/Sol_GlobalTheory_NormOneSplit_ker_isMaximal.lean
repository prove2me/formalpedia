-- Prove2me | solution 1 for GlobalTheory.NormOneSplit.ker_isMaximal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T03:34:25.700806+00:00
-- url     : https://prove2.me/submissions/a12d1429-8f21-404b-a77a-bde3990a53c1

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_DataSpaces
import Definitions.Def_Formalism_FlagUnipotentLattices_CardSubmodulesAndLinearEquivBounds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsForallHomEq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module Matrix Formalism.BasicNotions
open scoped ENNReal
open GlobalTheory GlobalTheory.NormOneSplit
open NumberField Module Matrix
open scoped ENNReal
namespace GlobalTheory.NormOneSplit
namespace _root_.GlobalTheory.NormOneSplit
theorem _root_.solution {R : Type} [CommRing R] {T : ℕ} [Fact T.Prime]
    (φ : R →+* ZMod T) :
    (RingHom.ker φ).IsMaximal :=
  RingHom.ker_isMaximal_of_surjective φ (ZMod.ringHom_surjective φ)
end _root_.GlobalTheory.NormOneSplit
end GlobalTheory.NormOneSplit
