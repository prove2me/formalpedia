-- Prove2me | solution 1 for GlobalTheory.Mem.LevDual.sigR_inclE
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T05:39:28.23114+00:00
-- url     : https://prove2.me/submissions/70919e31-5ca9-404b-85c3-b9ba12338ba5

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_DataLevel
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Afsplit
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_UnitaryCarryDual

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.UG Matrix
open scoped TensorProduct
noncomputable section
open GlobalTheory GlobalTheory.Mem GlobalTheory.Mem.LevDual
namespace GlobalTheory.Mem.LevDual
theorem _root_.solution {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (e : E) :
    sigR σ (FiniteAdeleRing (𝓞 F) F) (inclE (F := F) (FiniteAdeleRing (𝓞 F) F) e) =
      inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (σ e) := rfl
end GlobalTheory.Mem.LevDual
