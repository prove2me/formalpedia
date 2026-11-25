-- Prove2me | solution 1 for GlobalTheory.AllClasses.Occurs.twist
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:32:33.755995+00:00
-- url     : https://prove2.me/submissions/6084ea78-bf7a-4ea8-9b3d-48430061efda

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_TestObj
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_IsCoprimeTwoSubRtTwoAddRt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_OneAddZeta21PowSevenAddPowFourteenEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_ToMatrixTrFormBaseChange
import Definitions.Def_Development_AbelianVarietyTheory_Statements_HyperbolicHypotheses_HypothesesInhabitedHyperbolic
import Theorems.Thm_GlobalTheory_AllClasses_dvd_sign_add_one
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
variable {D : Datum H} {l : Level H} {Xo : Moduli D l} {σ : KA l →+* ℂ} {g : ℕ} {ty : Fin g → (E →+* ℂ)}
namespace GlobalTheory.AllClasses
namespace Occurs
theorem _root_.solution {U : FamilyUnif Xo σ ty} {D' : Datum H} {f : ℕ → D.La →ₗ[𝓞 E] D'.La}
    (h : Occurs U D' (f l.M)) : Occurs U D' ((fun n => sign n • f n) l.M) := by
  obtain ⟨i, gam, h₁, h₂⟩ := h
  refine ⟨i, gam.trans (LinearEquiv.neg _), fun a a' => by simp [h₁], fun a ha => ?_⟩
  obtain ⟨e, he⟩ := h₂ a ha
  obtain ⟨e', he'⟩ := exists_eq_add_nsmul (x := sign l.M) (y := -1) (by simpa using dvd_sign_add_one l.odd)
    (gam (f l.M a))
  refine ⟨e - e', ?_⟩
  simp only [LinearMap.smul_apply, LinearEquiv.trans_apply, LinearEquiv.neg_apply, map_zsmul] at he ⊢
  rw [smul_neg, he', neg_one_zsmul, he, smul_sub]
  abel
end Occurs
end GlobalTheory.AllClasses
