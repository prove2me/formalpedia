-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.RgEis.bdetLaw
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T15:31:22.595601+00:00
-- url     : https://prove2.me/submissions/c7063af6-1050-4252-b67f-09adc6e701d7

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_ConvGrOf
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_BlockDeterminantLaw
import Theorems.Thm_GlobalTheory_CompanionTheory_RgEis_bdet_mul
import Theorems.Thm_GlobalTheory_CompanionTheory_RgEis_bdet_univ
import Theorems.Thm_GlobalTheory_CompanionTheory_RgEis_isClosed_stab
import Theorems.Thm_GlobalTheory_CompanionTheory_RgEis_continuousOn_bdet
import Theorems.Thm_GlobalTheory_CompanionTheory_RgEis_bdet_rat
import Theorems.Thm_GlobalTheory_CompanionTheory_RgEis_lg_bdet

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open scoped ComplexConjugate
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.RgEis
open PositivityTheory.RgEis
variable {R : Type} [CommRing R] {ι : Type} [Fintype ι] [DecidableEq ι]
namespace GlobalTheory.CompanionTheory.RgEis
theorem _root_.solution : BdetLaw := by
  intro E R _ _ _ _ _ _ _ A hA ι _ _ s
  exact ⟨isClosed_stab s, fun p hp q hq => bdet_mul s hp hq, continuousOn_bdet s,
    fun p hp hr => bdet_rat A hA.iinj s hp hr, fun p hp hk => lg_bdet A hA s hp hk, bdet_univ⟩
end GlobalTheory.CompanionTheory.RgEis
