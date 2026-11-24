-- Prove2me | solution 1 for GlobalTheory.T.local_haar_measure_singleton
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:18:21.125804+00:00
-- url     : https://prove2.me/submissions/feb59ed7-40f4-45e0-806c-2fec470e749b

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_LocalHaarMeasureSingleton
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_TsumNeZeroEqSum
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_LocalHaarMeasureSingletonStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_Mass_MeanV_isStdV_measure_singleton_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.Mass.MeanV PositivityTheory.Rg.Mass NumberField IsDedekindDomain MeasureTheory Topology Filter
open scoped ENNReal NNReal Classical
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (lam : Measure (Fv F v)), IsStdV v lam → lam {0} = 0 := by
  first | exact @GlobalTheory.CompanionTheory.Mass.MeanV.isStdV_measure_singleton_zero | exact GlobalTheory.CompanionTheory.Mass.MeanV.isStdV_measure_singleton_zero | (intros; apply GlobalTheory.CompanionTheory.Mass.MeanV.isStdV_measure_singleton_zero <;> assumption)
end _root_.GlobalTheory.T
