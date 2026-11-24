-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Mass.SumDev.mem_asIdeal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:51:15.452832+00:00
-- url     : https://prove2.me/submissions/3452f6a0-e91d-4f99-874f-9261f49a3a52

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_TruncSum
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_EulerProductConvergenceBound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.Mass.MeanV PositivityTheory.Rg.Mass NumberField IsDedekindDomain MeasureTheory Topology Filter
open scoped ENNReal NNReal Classical
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Mass GlobalTheory.CompanionTheory.Mass.SumDev
variable {F : Type} [Field F] [NumberField F]
namespace GlobalTheory.CompanionTheory.Mass.SumDev
theorem _root_.solution (v : HeightOneSpectrum (𝓞 F)) {x : F}
    (hxi : algebraMap F (Fv F v) x ∈ v.adicCompletionIntegers F)
    (h1 : Valued.v (algebraMap F (Fv F v) x) ≠ 1) {N : ℕ} {y : 𝓞 F} (hy : (y : F) = (N : F) * x) :
    y ∈ v.asIdeal := by
  have hval : Valued.v (algebraMap F (Fv F v) x) = v.valuation F x :=
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v x
  have hle : v.valuation F x ≤ 1 := by
    rw [← hval]
    exact (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 F) F v).mp hxi
  have hlt : v.valuation F x < 1 := lt_of_le_of_ne hle (by rw [← hval]; exact h1)
  refine (HeightOneSpectrum.valuation_lt_one_iff_mem (K := F) v y).mp ?_
  have hN : v.valuation F (N : F) ≤ 1 := by
    have h := HeightOneSpectrum.valuation_le_one (K := F) v (N : 𝓞 F)
    exact_mod_cast h
  have hNx : v.valuation F ((N : F) * x) < 1 := by
    rw [map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_left' hN) hlt
  convert hNx using 2
end GlobalTheory.CompanionTheory.Mass.SumDev
