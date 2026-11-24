-- Prove2me | solution 1 for GlobalTheory.AllClasses.dvd_of_parts
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T19:08:34.474061+00:00
-- url     : https://prove2.me/submissions/0e24ecfa-ddcc-4c2a-bae2-1978e29907df

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_TestObj
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_IsCoprimeTwoSubRtTwoAddRt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_OneAddZeta21PowSevenAddPowFourteenEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_ToMatrixTrFormBaseChange
import Definitions.Def_Development_AbelianVarietyTheory_Statements_HyperbolicHypotheses_HypothesesInhabitedHyperbolic

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory
open GlobalTheory.AllClasses
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
namespace GlobalTheory.AllClasses
theorem _root_.solution {n : ℕ} (hn : 0 < n) {x : ℤ} (h₁ : ((ordProj[2] n : ℕ) : ℤ) ∣ x)
    (h₂ : ((ordCompl[2] n : ℕ) : ℤ) ∣ x) : (n : ℤ) ∣ x := by
  have hc : IsCoprime ((ordProj[2] n : ℕ) : ℤ) ((ordCompl[2] n : ℕ) : ℤ) :=
    Nat.isCoprime_iff_coprime.mpr ((Nat.coprime_ordCompl Nat.prime_two hn.ne').pow_left _)
  have := hc.mul_dvd h₁ h₂
  rwa [← Nat.cast_mul, Nat.ordProj_mul_ordCompl_eq_self] at this
end GlobalTheory.AllClasses
