-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Mass.MeanV.Sandwich.iInter_ballV
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:34:14.220098+00:00
-- url     : https://prove2.me/submissions/9547afd6-7d1c-4b77-ad39-cf41dd6d5ba4

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
theorem _root_.solution (v : HeightOneSpectrum (𝓞 F)) : ⋂ n, ballV (F := F) v n = {0} := by
  ext y
  simp only [Set.mem_iInter, Set.mem_singleton_iff]
  constructor
  · intro h
    by_contra hy
    have hv0 : Valued.v y ≠ 0 := (Valuation.ne_zero_iff _).2 hy
    have h1 := h (-(Valued.v y).log + 1).toNat
    have h2 : Valued.v y ≤ WithZero.exp (-(((-(Valued.v y).log + 1).toNat : ℕ) : ℤ)) := h1
    conv_lhs at h2 => rw [← WithZero.exp_log hv0]
    rw [WithZero.exp_le_exp] at h2
    have := Int.self_le_toNat (-(Valued.v y).log + 1)
    omega
  · rintro rfl n
    simp [ballV]
end GlobalTheory.CompanionTheory.Mass.MeanV.Sandwich
