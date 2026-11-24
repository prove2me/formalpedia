-- Prove2me | solution 1 for GlobalTheory.T.cmField_adele_split_place_support_integral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:05:25.929838+00:00
-- url     : https://prove2.me/submissions/f7d04f4d-9911-4e2f-b1be-25907b174641

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_CmFieldAdeleSplitPlaceSupportIntegral
import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_GaloisLevelStructure_DefsAut
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_CmFieldAdeleSplitPlaceSupportIntegralStatement
import Theorems.Thm_GlobalTheory_mem_ALint_of_supported_at_split


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
theorem _root_.solution : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (s : ReciprocityTheory.Aut.SplitPlace L) (e : 𝓞 L), Valued.v (s.i (e : L)) = 1 → Valued.v (s.i (IsCMField.complexConj L (e : L))) < 1 → ∀ z : ReciprocityTheory.Aut.AL L, (∀ w, w ≠ s.v → ReciprocityTheory.Aut.compAt L w z = 0) → Valued.v (s.proj z) ≤ 1 → Valued.v (s.proj (ReciprocityTheory.Aut.conjAL L z)) ≤ 1 → z ∈ ReciprocityTheory.Aut.ALint L := by
  first | exact @GlobalTheory.mem_ALint_of_supported_at_split | exact GlobalTheory.mem_ALint_of_supported_at_split | (intros; apply GlobalTheory.mem_ALint_of_supported_at_split <;> assumption)
end _root_.GlobalTheory.T
