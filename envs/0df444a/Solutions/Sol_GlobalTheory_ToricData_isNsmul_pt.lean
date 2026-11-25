-- Prove2me | solution 1 for GlobalTheory.ToricData.isNsmul_pt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T15:39:00.549282+00:00
-- url     : https://prove2.me/submissions/2615d4ae-883e-4c9d-badc-b8fa1c053e56

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_PsiWeightZeroLinearCombination
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ZeroFLeftExt
import Theorems.Thm_GlobalTheory_ToricData_isZero_pt
import Theorems.Thm_GlobalTheory_ToricData_isAdd_pt
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
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Out.Inh ReciprocityTheory.ChartRestriction.G.Out.InhTate ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ToricData
variable {K : Type} [CommRing K] [IsDomain K] {X : Type} [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X]
variable (q : X → (FractionRing K)ˣ) (F : Type) [Field F] [Algebra (FractionRing K) F]
namespace GlobalTheory.ToricData
theorem _root_.solution (n : ℕ) (t t') : GtPtF.IsNsmul n (pt q F t) (pt q F t') ↔ t' = t ^ n := by
  constructor
  · rintro ⟨gs, h0, hs, hl⟩
    choose u hu using fun i => (pt_bijective q F).2 (gs i)
    have key : ∀ i : Fin (n + 1), u i = t ^ (i : ℕ) := by
      intro i
      induction i using Fin.induction with
      | zero =>
        rw [← hu] at h0
        exact ((isZero_pt q F _).1 h0).trans (pow_zero t).symm
      | succ i ih =>
        have h := hs i
        rw [← hu, ← hu, isAdd_pt] at h
        rw [h, ih, Fin.val_succ, pow_succ]
        rfl
    rw [← hu] at hl
    exact ((pt_bijective q F).1 hl).symm.trans (key _)
  · rintro rfl
    exact ⟨fun i => pt q F (t ^ (i : ℕ)), (isZero_pt q F _).2 (pow_zero t),
      fun i => (isAdd_pt q F _ _ _).2 (pow_succ t i), rfl⟩
end GlobalTheory.ToricData
