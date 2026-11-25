-- Prove2me | solution 1 for GlobalTheory.HostModel.equiv_refl_witP
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T18:22:29.616317+00:00
-- url     : https://prove2.me/submissions/6121304f-9d5b-4412-8e5d-de4e2a15ccd5

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DataRigidSt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_IsPrimitiveRootArcRoot
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_ArcVarZpowInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExistsWitDataLevelAgree
import Theorems.Thm_GlobalTheory_HostModel_arcIn_be_even
import Theorems.Thm_GlobalTheory_ToricData_isAdd_pt
import Theorems.Thm_GlobalTheory_ToricData_isIota_pt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HostModel
open ToricData
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
variable {l : Level H} (c : Coeff l) (k : Type) [Field k] (bF : c.F →+* k)
variable (F : Type) [Field F] [Algebra (FractionRing (PowerSeries k)) F]
namespace GlobalTheory.HostModel
theorem _root_.solution {n : ℕ} (p : QkPt (witP c k bF).toPre F n) : QkPt.Equiv _ F p p := by
  obtain ⟨t, ht⟩ := (pt_bijective (arcExp (X := 𝓞 E) k (arcForm l)) F).2 p.g
  refine ⟨(0 : 𝓞 E), ((congrArg (p.y + ·) (nsmul_zero n)).trans (add_zero _)).symm, pt _ F 1,
    (isIota_pt _ F _ _).2 fun χ => ?_, ?_⟩
  · rw [polar_arcExp (X := 𝓞 E) k (arcForm l) (arcIn c k bF).be_symm (arcIn_be_even c k bF), map_zero,
      LinearMap.zero_apply, zpow_zero, Units.val_one, map_one]
    rfl
  · rw [← ht]
    exact (isAdd_pt _ F _ _ _).2 (mul_one t).symm
end GlobalTheory.HostModel
