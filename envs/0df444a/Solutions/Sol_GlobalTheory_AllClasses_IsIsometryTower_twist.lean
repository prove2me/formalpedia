-- Prove2me | solution 1 for GlobalTheory.AllClasses.IsIsometryTower.twist
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:41:26.358061+00:00
-- url     : https://prove2.me/submissions/0989e599-6720-4c59-a859-7585e3d0e507

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_TestObj
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_IsCoprimeTwoSubRtTwoAddRt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_OneAddZeta21PowSevenAddPowFourteenEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_ToMatrixTrFormBaseChange
import Definitions.Def_Development_AbelianVarietyTheory_Statements_HyperbolicHypotheses_HypothesesInhabitedHyperbolic
import Theorems.Thm_GlobalTheory_AllClasses_dvd_sign_sq
import Theorems.Thm_GlobalTheory_AllClasses_dvd_sign_mul_sub
import Theorems.Thm_GlobalTheory_AllClasses_exists_eq_add_nsmul
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
namespace IsIsometryTower
theorem _root_.solution {D D' : Datum H} {f : ℕ → D.La →ₗ[𝓞 E] D'.La} (hf : IsIsometryTower D D' f) :
    IsIsometryTower D D' fun n => sign n • f n := by
  obtain ⟨⟨h₁, h₂⟩, h₃⟩ := hf
  refine ⟨⟨fun n m hn hm a => ?_, fun n hn => ⟨fun a => ?_, fun a' => ?_⟩⟩, fun n hn a a' => ?_⟩
  · obtain ⟨e, he⟩ := h₁ n m hn hm a
    obtain ⟨e', he'⟩ := exists_eq_add_nsmul (dvd_sign_mul_sub hn hm) (f n a)
    refine ⟨e' + sign (n * m) • e, ?_⟩
    simp only [LinearMap.smul_apply]
    rw [he, smul_add, he', smul_add, smul_comm n (sign (n * m)) e, add_assoc]
  · rw [← (h₂ n hn).1 a]
    simp only [LinearMap.smul_apply]
    constructor
    · rintro ⟨e, he⟩
      obtain ⟨e', he'⟩ := exists_eq_add_nsmul (dvd_sign_sq hn) (f n a)
      refine ⟨sign n • e - e', ?_⟩
      rw [smul_sub, smul_comm n (sign n) e, ← he, smul_smul, he', one_smul, add_sub_cancel_right]
    · rintro ⟨e, he⟩
      exact ⟨sign n • e, by rw [he, smul_comm]⟩
  · obtain ⟨a, e, he⟩ := (h₂ n hn).2 a'
    obtain ⟨e', he'⟩ := exists_eq_add_nsmul (dvd_sign_sq hn) (f n a)
    refine ⟨sign n • a, e - e', ?_⟩
    simp only [LinearMap.smul_apply]
    rw [map_zsmul, smul_smul, he', one_smul, he, smul_sub]
    abel
  · simp only [LinearMap.smul_apply, map_zsmul, smul_eq_mul]
    have := ((dvd_sign_sq hn).mul_right (D'.EF (f n a) (f n a'))).add (h₃ n hn a a')
    rwa [show (sign n * sign n - 1) * D'.EF (f n a) (f n a') + (D'.EF (f n a) (f n a') - D.EF a a') =
      sign n * (sign n * D'.EF (f n a) (f n a')) - D.EF a a' by ring] at this
end IsIsometryTower
end GlobalTheory.AllClasses
