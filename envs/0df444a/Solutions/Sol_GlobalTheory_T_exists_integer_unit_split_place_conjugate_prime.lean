-- Prove2me | solution 1 for GlobalTheory.T.exists_integer_unit_split_place_conjugate_prime
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:22:02.849806+00:00
-- url     : https://prove2.me/submissions/23ebb695-2de5-41e3-a66f-946a538caa12

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_ExistsIntegerUnitSplitPlaceConjugatePrime
import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_GaloisLevelStructure_DefsAut
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_ExistsIntegerUnitSplitPlaceConjugatePrimeStatement
import Theorems.Thm_GlobalTheory_SplitSep_exists_sep


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (s : ReciprocityTheory.Aut.SplitPlace L), ∃ e : 𝓞 L, Valued.v (s.i (e : L)) = 1 ∧ Valued.v (s.i (IsCMField.complexConj L (e : L))) < 1 := by
  first | exact @GlobalTheory.SplitSep.exists_sep | exact GlobalTheory.SplitSep.exists_sep | (intros; apply GlobalTheory.SplitSep.exists_sep <;> assumption)
end _root_.GlobalTheory.T
