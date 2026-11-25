-- Prove2me | solution 1 for GlobalTheory.BK.isOfType_rankOneDat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:32:24.508798+00:00
-- url     : https://prove2.me/submissions/97c6d094-962b-440e-9486-7bd4d39b7a6a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_ExistsEqMulAddOfIsAdicComplete
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_ExistsAlgebraMapEqRoot
import Theorems.Thm_GlobalTheory_BK_jumps_rankOne
import Theorems.Thm_GlobalTheory_BK_Hom_onPol_cls
import Theorems.Thm_GlobalTheory_BK_coe_Eunit
import Theorems.Thm_GlobalTheory_BK_hat_coe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.BK.Hom.onPol_cls
attribute [local simp] GlobalTheory.BK.coe_Eunit
attribute [local simp] GlobalTheory.BK.hat_coe



set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.BK
open PowerSeries Filter Topology Matrix
variable (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι]
  [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a]
variable {O K l e a ι} {κ : Type} [Fintype κ] [DecidableEq κ] {η H η' H' : ℕ}
namespace GlobalTheory.BK
theorem _root_.solution [CompleteSpace K] {j : ℤ} (h₁ : -(η : ℤ) ≤ j) (h₂ : j ≤ H) :
    (rankOneDat O K l e a η H j h₁ h₂ 1).IsOfType {0} {j} where
  chars_subset := by
    rintro τ c ⟨d, hd, h⟩
    obtain ⟨ζ, hζ⟩ := TameDescentExponentData.prim (K := K) (l := l) (e := e) (a := a)
    have h1 := congrFun (h (powL l τ (rootsOfUnity.mkOfPowEq ζ hζ.pow_eq_one))) ()
    have h2 := (congrArg constantCoeff (rankOneDesc_act j 1 _ _ τ)).symm.trans h1
    have h3 : (TameGal.inertia (powL l τ (rootsOfUnity.mkOfPowEq ζ hζ.pow_eq_one)) :
        TameGal K l e a).root τ = ζ := by
      rw [TameGal.root, SemidirectProduct.left_inl, ← powL_add, neg_add_cancel, powL_zero]
      rfl
    have h4 : d τ () ≠ 0 := fun h0 => hd (funext fun _ => h0)
    rw [h3, ← coeff_zero_eq_constantCoeff_apply] at h2
    have h5 : ζ ^ c.val = 1 := by simpa [h4, eq_comm] using h2
    exact (ZMod.val_eq_zero c).1 (Nat.eq_zero_of_dvd_of_lt ((hζ.pow_eq_one_iff_dvd _).1 h5) c.val_lt)
  jumps_subset := (jumps_rankOne j).le
end GlobalTheory.BK
