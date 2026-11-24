-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Mass.MeanV.Sandwich.tendsto_real_ballV
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T13:08:35.664802+00:00
-- url     : https://prove2.me/submissions/721960bb-a08d-4fd7-a3ce-498efdcd30ee

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_TruncSum
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CasimirVolumeRatios_AdeleLC
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_LocalFactorSandwichApprox
import Theorems.Thm_GlobalTheory_CompanionTheory_Mass_MeanV_Sandwich_isClopen_ballV
import Theorems.Thm_GlobalTheory_CompanionTheory_Mass_MeanV_Sandwich_ballV_subset
import Theorems.Thm_GlobalTheory_CompanionTheory_Mass_MeanV_Sandwich_antitone_ballV
import Theorems.Thm_GlobalTheory_CompanionTheory_Mass_MeanV_Sandwich_iInter_ballV
import Theorems.Thm_GlobalTheory_CompanionTheory_Mass_MeanV_Sandwich_nhdsNE_Fv

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
theorem _root_.solution {v : HeightOneSpectrum (𝓞 F)} {lam : Measure (Fv F v)} (hstd : IsStdV v lam) :
    Tendsto (fun n => lam.real (ballV v n)) atTop (𝓝 0) := by
  haveI : BorelSpace (Fv F v) := ⟨rfl⟩
  haveI := hstd.1
  haveI := nhdsNE_Fv v
  have hfin : ∀ n, lam (ballV v n) ≠ ∞ := fun n =>
    ne_top_of_le_ne_top (by rw [hstd.2]; exact ENNReal.one_ne_top) (measure_mono (ballV_subset v n))
  have h := tendsto_measure_iInter_atTop (μ := lam) (s := ballV v)
    (fun n => (isClopen_ballV v n).isOpen.measurableSet.nullMeasurableSet) (antitone_ballV v) ⟨0, hfin 0⟩
  rw [iInter_ballV, measure_singleton] at h
  have h2 := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h
  simpa [Measure.real, Function.comp_def] using h2
end GlobalTheory.CompanionTheory.Mass.MeanV.Sandwich
