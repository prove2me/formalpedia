-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Mass.MeanV.Sandwich.antitone_ballV
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:34:02.569112+00:00
-- url     : https://prove2.me/submissions/e3be0a90-a622-4696-849d-d3b7d3f96cd0

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_TruncSum
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CasimirVolumeRatios_AdeleLC
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_LocalFactorSandwichApprox

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
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Mass GlobalTheory.CompanionTheory.Mass.MeanV GlobalTheory.CompanionTheory.Mass.MeanV.Sandwich
variable {F : Type} [Field F] [NumberField F]
namespace GlobalTheory.CompanionTheory.Mass.MeanV.Sandwich
theorem _root_.solution (v : HeightOneSpectrum (𝓞 F)) : Antitone (ballV (F := F) v) := by
  intro m n hmn y hy
  show Valued.v y ≤ _
  refine le_trans (show Valued.v y ≤ _ from hy) ?_
  rw [WithZero.exp_le_exp]
  omega
end GlobalTheory.CompanionTheory.Mass.MeanV.Sandwich
