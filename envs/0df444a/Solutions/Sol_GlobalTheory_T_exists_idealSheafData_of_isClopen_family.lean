-- Prove2me | solution 1 for GlobalTheory.T.exists_idealSheafData_of_isClopen_family
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T18:21:56.436286+00:00
-- url     : https://prove2.me/submissions/565681b9-1a63-4638-8145-7d75dc27c5d4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsIdealSheafDataOfIsClopenFamily
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IsOpenOfMemIrreducibleComponentsOfFinite
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormIdeal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FamIdeal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsIdealSheafDataOfIsClopenFamilyStatement
import Theorems.Thm_GlobalTheory_ClopenIdealSheaf_exists_idealSheafData_of_isClopen


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (Z : Scheme.{0}) (W : Set Z), IsClopen W → ∀ (F : ∀ U : Z.affineOpens, Ideal Γ(Z, U)),
    (∀ (U : Z.affineOpens) (f : Γ(Z, U)), (U : Set Z) ⊆ W →
      (F U).map (Z.presheaf.map (homOfLE (Z.basicOpen_le f)).op).hom = F (Z.affineBasicOpen f)) →
    ∃ J : Z.IdealSheafData, (∀ U : Z.affineOpens, (U : Set Z) ⊆ W → J.ideal U = F U) ∧
      (J.support : Set Z) ⊆ W := by
  first | exact @GlobalTheory.ClopenIdealSheaf.exists_idealSheafData_of_isClopen | exact GlobalTheory.ClopenIdealSheaf.exists_idealSheafData_of_isClopen | (intros; apply GlobalTheory.ClopenIdealSheaf.exists_idealSheafData_of_isClopen <;> assumption)
end _root_.GlobalTheory.T
