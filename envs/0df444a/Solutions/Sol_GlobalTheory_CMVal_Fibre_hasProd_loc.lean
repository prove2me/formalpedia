-- Prove2me | solution 1 for GlobalTheory.CMVal.Fibre.hasProd_loc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:29:15.850466+00:00
-- url     : https://prove2.me/submissions/81fe2068-4200-4be5-94a2-16b67ff31012

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_EntireEqOfHalfPlane
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FinPartEqOneOfFibres
import Theorems.Thm_GlobalTheory_CMVal_Fibre_hasProd_single
import Theorems.Thm_GlobalTheory_CMVal_Fibre_continuous_finPart

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
theorem _root_.solution (χ : HChar E) (y : (Af E)ˣ) : HasProd (fun P => χ.loc P (coord P y)) (finPart χ y) :=
  (hasProd_single y).map (finPart χ) (continuous_finPart χ)
end GlobalTheory.CMVal.Fibre
