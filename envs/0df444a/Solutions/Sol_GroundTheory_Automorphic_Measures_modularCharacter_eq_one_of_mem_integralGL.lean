-- Prove2me | solution 1 for GroundTheory.Automorphic.Measures.modularCharacter_eq_one_of_mem_integralGL
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:13:49.10997+00:00
-- url     : https://prove2.me/submissions/ae4d99f7-9384-4e89-a2e9-56cd8eeca320

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_MeasuresGL
import Definitions.Def_GroundTheory_AutomorphicForms_Iwasawa
import Definitions.Def_GroundTheory_AutomorphicForms_MeasuresParabolic
import Theorems.Thm_GroundTheory_Automorphic_GLnLocal_isCompact_integralGL
import Theorems.Thm_GroundTheory_Automorphic_Measures_LinearChart_modularCharacter_eq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open MeasureTheory Measure Topology Filter Set ValuativeRel Iwasawa
open scoped NNReal ENNReal Pointwise
set_option linter.unusedSectionVars false
open GroundTheory.Automorphic.Measures
variable (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  (n : ℕ) {α : Type*} [LinearOrder α] (β : Fin n → α)
variable {F n β}
variable (F n β)
variable {F n β}
namespace GroundTheory.Automorphic.Measures
theorem _root_.solution (p : blockUpper F n β)
    (hp : (p : GL (Fin n) F) ∈ GLnLocal.integralGL F n) : modularCharacter p = 1 := by
  borelize F ↥(blockUpper F n β)
  let V : OpenSubgroup (blockUpper F n β) :=
    ⟨(GLnLocal.integralGL F n).subgroupOf (blockUpper F n β),
      (GLnLocal.isOpen_integralGL F n).preimage continuous_subtype_val⟩
  have hV : IsCompact (V : Set (blockUpper F n β)) :=
    (isClosed_blockUpper F n β).isClosedEmbedding_subtypeVal.isCompact_preimage
      (GLnLocal.isCompact_integralGL F n)
  obtain ⟨h1, h2⟩ := (parabolicChart F n β).modulus_eq_one_of_mem hV (v := p) hp
  rw [(parabolicChart F n β).modularCharacter_eq, h1, h2, div_one]
end GroundTheory.Automorphic.Measures
