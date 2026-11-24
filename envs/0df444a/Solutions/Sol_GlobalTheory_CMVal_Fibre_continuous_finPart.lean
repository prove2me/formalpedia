-- Prove2me | solution 1 for GlobalTheory.CMVal.Fibre.continuous_finPart
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:05:32.222048+00:00
-- url     : https://prove2.me/submissions/6579b671-b05c-4700-8089-30986279d8d3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_EntireEqOfHalfPlane
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FinPartEqOneOfFibres

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Filter Topology
open GlobalTheory GlobalTheory.CMVal GlobalTheory.CMVal.Fibre
variable {E : Type} [Field E] [NumberField E]
namespace GlobalTheory.CMVal.Fibre
theorem _root_.solution (χ : HChar E) : Continuous (finPart χ) :=
  χ.2.1.comp (Continuous.units_map (MonoidHom.inr (InfiniteAdeleRing E) (Af E)) (continuous_const.prodMk continuous_id))
end GlobalTheory.CMVal.Fibre
