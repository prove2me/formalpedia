-- Prove2me | solution 1 for GlobalTheory.UnRep.Compare.repStatement_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:54:11.397874+00:00
-- url     : https://prove2.me/submissions/8451596a-4b04-471e-a8c3-e1d9fb8ef0bc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_IsHermForm
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_AdelicCMFields_SupportedAtSplit
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsLatticeRationalVectorsInAdelicTranslate
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IsSplitPlaceOfSplitPl
import Theorems.Thm_GlobalTheory_UnRep_Compare_isHermForm_iff
import Theorems.Thm_GlobalTheory_UnRep_Compare_hasRep_of
import Theorems.Thm_GlobalTheory_UnRep_Compare_of_hasRep

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.UnRep GlobalTheory.UnRep.Compare
open NumberField IsDedekindDomain GlobalTheory.AdLat GlobalTheory.UnRep GlobalTheory.IndefiniteRowSideFullHecke.SplitPlaceUnitaryEvaluation
open scoped TensorProduct Matrix
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
namespace GlobalTheory.UnRep.Compare
theorem _root_.solution : RepStatement 2 ↔ SplitRepresentatives := by
  constructor
  · intro H F E _ _ _ _ _ c h2 hc n hn G hG hdet L hfg hsp N D hN hD
    exact of_hasRep c h2 hc hdet L N D (H F E c n hn G ((isHermForm_iff c h2 G).2 ⟨hc, hG, hdet⟩) h2 L hfg hsp
      _ (Nat.pos_of_ne_zero (mul_ne_zero hN hD)))
  · intro H F E _ _ _ _ _ c n hn G hG h2 L hfg hsp N hN
    obtain ⟨hc, hG, hdet⟩ := (isHermForm_iff c h2 G).1 hG
    exact hasRep_of c h2 hc hdet L hN.ne' (H F E c h2 hc n hn G hG hdet L hfg hsp N N hN.ne' hN.ne')
end GlobalTheory.UnRep.Compare
