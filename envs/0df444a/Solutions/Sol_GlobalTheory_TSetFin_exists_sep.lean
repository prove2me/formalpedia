-- Prove2me | solution 1 for GlobalTheory.TSetFin.exists_sep
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:36:10.425463+00:00
-- url     : https://prove2.me/submissions/2cfefbfd-bbcf-4e2b-a1bd-7a89841419de

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_GaloisLevelStructure_DefsAut
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_ExistsIntegerUnitSplitPlaceConjugatePrimeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_CmFieldAdeleSplitPlaceSupportIntegralStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_HeckeDoubleCosetAdicCompletionInvMulIntegralStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_FiniteCosetsHeckeSetAtSplitPlaceOutsideLevel
import Theorems.Thm_GlobalTheory_T_exists_integer_unit_split_place_conjugate_prime


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
theorem _root_.solution (s : SplitPlace L) : ∃ e : 𝓞 L, Valued.v (s.i (e : L)) = 1 ∧
    Valued.v (s.i (IsCMField.complexConj L (e : L))) < 1 := GlobalTheory.T.exists_integer_unit_split_place_conjugate_prime L s
end GlobalTheory.TSetFin
