-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.TfLoc.Iw.iwahori_compact_open_galois
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:37:09.526361+00:00
-- url     : https://prove2.me/submissions/016de54a-8b9c-409b-ac73-e1df33e636c6

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_TwistedFactors_IntegralUnitBaseChange_Development
import Definitions.Def_GroundTheory_LocalFields_Integers
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IwahoriFactorization
import Theorems.Thm_GlobalTheory_CompanionTheory_TfLoc_Iw_exists_subgroup
import Theorems.Thm_GlobalTheory_CompanionTheory_TfLoc_Iw_torusO_subset
import Theorems.Thm_GlobalTheory_CompanionTheory_TfLoc_Iw_isClopen_iwahori
import Theorems.Thm_GlobalTheory_CompanionTheory_TfLoc_Iw_isCompact_iwahori
import Theorems.Thm_GlobalTheory_CompanionTheory_TfLoc_Iw_incl_mem_iff
import Theorems.Thm_GlobalTheory_CompanionTheory_TfLoc_Iw_sigma_mem_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel PositivityTheory.Rg.Tf.Loc Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.TfLoc GlobalTheory.CompanionTheory.TfLoc.Iw
namespace GlobalTheory.CompanionTheory.TfLoc.Iw
theorem _root_.solution : PositivityTheory.Rg.Tf.Loc.I0 := by
  refine ⟨fun F _ _ _ _ n => ⟨exists_subgroup, isClopen_iwahori.isOpen, isCompact_iwahori,
    torusO_subset⟩, fun k E _ _ _ _ _ _ _ _ _ _ _ _ _ n =>
      ⟨incl_mem_iff, fun τ g => sigma_mem_iff τ g⟩⟩
end GlobalTheory.CompanionTheory.TfLoc.Iw
