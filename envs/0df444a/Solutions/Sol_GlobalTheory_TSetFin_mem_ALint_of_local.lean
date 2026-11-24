-- Prove2me | solution 1 for GlobalTheory.TSetFin.mem_ALint_of_local
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:26:09.150804+00:00
-- url     : https://prove2.me/submissions/0239cac8-1f29-4940-968e-4643d7c7ef11

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_GaloisLevelStructure_DefsAut
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_ExistsIntegerUnitSplitPlaceConjugatePrimeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_CmFieldAdeleSplitPlaceSupportIntegralStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_HeckeDoubleCosetAdicCompletionInvMulIntegralStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_FiniteCosetsHeckeSetAtSplitPlaceOutsideLevel
import Theorems.Thm_GlobalTheory_T_cmField_adele_split_place_support_integral


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain ReciprocityTheory.Aut
noncomputable section
open GlobalTheory GlobalTheory.TSetFin
variable {L : Type} [Field L] [NumberField L] [IsCMField L]
local notation3 "L⁺" => maximalRealSubfield L
namespace GlobalTheory.TSetFin
theorem _root_.solution (s : SplitPlace L) (e : 𝓞 L) (he : Valued.v (s.i (e : L)) = 1)
    (he' : Valued.v (s.i (IsCMField.complexConj L (e : L))) < 1) (z : AL L)
    (hz : ∀ w, w ≠ s.v → compAt L w z = 0) (h1 : Valued.v (s.proj z) ≤ 1)
    (h2 : Valued.v (s.proj (conjAL L z)) ≤ 1) : z ∈ ALint L := GlobalTheory.T.cmField_adele_split_place_support_integral L s e he he' z hz h1 h2
end GlobalTheory.TSetFin
