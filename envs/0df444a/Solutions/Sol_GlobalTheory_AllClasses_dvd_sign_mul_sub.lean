-- Prove2me | solution 1 for GlobalTheory.AllClasses.dvd_sign_mul_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T19:26:02.601825+00:00
-- url     : https://prove2.me/submissions/e6c32f9c-74e2-42e3-bcd1-677773649901

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_TestObj
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_IsCoprimeTwoSubRtTwoAddRt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_OneAddZeta21PowSevenAddPowFourteenEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_ToMatrixTrFormBaseChange
import Definitions.Def_Development_AbelianVarietyTheory_Statements_HyperbolicHypotheses_HypothesesInhabitedHyperbolic
import Theorems.Thm_GlobalTheory_AllClasses_sign_spec
import Theorems.Thm_GlobalTheory_AllClasses_dvd_of_parts
import Theorems.Thm_GlobalTheory_HostModel_host_d
import Theorems.Thm_GlobalTheory_HostModel_host_rt
import Theorems.Thm_GlobalTheory_HostModel_host_rt0_eq_I_mul_sqrt_seven
import Theorems.Thm_GlobalTheory_HostModel_host_w0_eq_halfSqrtNegSeven
import Theorems.Thm_GlobalTheory_HostModel_hypDatum_p
import Theorems.Thm_GlobalTheory_HostModel_hypDatum_q
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.HostModel.host_d
attribute [local simp] GlobalTheory.HostModel.host_rt
attribute [local simp] GlobalTheory.HostModel.host_rt0_eq_I_mul_sqrt_seven
attribute [local simp] GlobalTheory.HostModel.host_w0_eq_halfSqrtNegSeven
attribute [local simp] GlobalTheory.HostModel.hypDatum_p
attribute [local simp] GlobalTheory.HostModel.hypDatum_q



set_option autoImplicit false
noncomputable section
open NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory
open GlobalTheory.AllClasses
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
namespace GlobalTheory.AllClasses
theorem _root_.solution {n m : ℕ} (hn : 0 < n) (hm : 0 < m) : (n : ℤ) ∣ sign (n * m) - sign n := by
  obtain ⟨h₁, h₂⟩ := sign_spec hn
  obtain ⟨k₁, k₂⟩ := sign_spec (Nat.mul_pos hn hm)
  have d₁ : ((ordProj[2] n : ℕ) : ℤ) ∣ ((ordProj[2] (n * m) : ℕ) : ℤ) :=
    Int.natCast_dvd_natCast.mpr (Nat.ordProj_dvd_ordProj_of_dvd (Nat.mul_pos hn hm).ne' (dvd_mul_right n m) 2)
  have d₂ : ((ordCompl[2] n : ℕ) : ℤ) ∣ ((ordCompl[2] (n * m) : ℕ) : ℤ) :=
    Int.natCast_dvd_natCast.mpr (Nat.ordCompl_dvd_ordCompl_of_dvd (dvd_mul_right n m) 2)
  refine dvd_of_parts hn ?_ ?_
  · simpa using (d₁.trans k₁).sub h₁
  · simpa using (d₂.trans k₂).sub h₂
end GlobalTheory.AllClasses
