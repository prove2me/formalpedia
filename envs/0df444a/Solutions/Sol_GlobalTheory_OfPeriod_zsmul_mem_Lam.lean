-- Prove2me | solution 1 for GlobalTheory.OfPeriod.zsmul_mem_Lam
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T18:04:06.052538+00:00
-- url     : https://prove2.me/submissions/098e71de-210b-4f5a-b7b6-2daf5a625715

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_TorusProjPeriodZeroEqReal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsEquivOfSumEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_FinrankHomComplex
import Theorems.Thm_GlobalTheory_OfPeriod_reForm_apply
import Theorems.Thm_GlobalTheory_AnArc_H_im_symm
import Theorems.Thm_GlobalTheory_AnArc_H_pos
import Theorems.Thm_GlobalTheory_AnArc_H_smul_right
import Theorems.Thm_GlobalTheory_EigenSplit_coe_eigenBaseChangeEquiv_tmul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.EigenSplit.coe_eigenBaseChangeEquiv_tmul


attribute [local simp] GlobalTheory.OfPeriod.reForm_apply

set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.OfPeriod
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (hermForm)
open Complex
variable {W : Type} [AddCommGroup W] [Module ℂ W] [Module ℝ W] [IsScalarTower ℝ ℂ W]
variable {S : W →ₗ[ℂ] W →ₗ⋆[ℂ] ℂ} {R : Submodule ℝ W}
namespace GlobalTheory.OfPeriod
theorem _root_.solution {O : Type} [CommRing O] [StarRing O] (A : AnArc O) (k : ℤ) (z : Fin A.gB → ℂ)
    (h : ∀ l : A.abelian₂, ∃ n : ℤ, k * (A.H l z).im = n) : k • z ∈ A.abelian₂ := by
  choose n hn using h
  let φ : A.abelian₂ →+ ℤ := AddMonoidHom.mk' (fun l => -n l) fun l l' => by
    have : ((n (l + l') : ℤ) : ℝ) = n l + n l' := by
      rw [← hn, ← hn, ← hn, Submodule.coe_add, A.H_add_left, add_im, mul_add]
    have : n (l + l') = n l + n l' := by exact_mod_cast this
    simp only [this]; ring
  obtain ⟨l₀, hl₀⟩ := A.Ef_bij.2 φ.toIntLinearMap
  have h1 : ∀ l : A.abelian₂, imForm (sesq A.Hm) (l₀ - k • z) l = 0 := fun l => by
    have h2 : (A.Ef l₀ l : ℝ) = -n l := by rw [hl₀]; simp [φ]
    rw [map_sub, map_zsmul, LinearMap.sub_apply, LinearMap.smul_apply]
    change (A.H l₀ l).im - k • (A.H z l).im = 0
    rw [← A.Ef_eq_im, h2, ← hn, A.H_im_symm z l]
    simp
  have h3 : imForm (sesq A.Hm) (l₀ - k • z) = 0 := LinearMap.ext_on A.full fun l hl => h1 ⟨l, hl⟩
  have h4 : (l₀ : Fin A.gB → ℂ) - k • z = 0 := by
    by_contra hne
    have h5 := A.H_pos hne
    have h6 : (A.H (l₀ - k • z) (I • (l₀ - k • z))).im = 0 := congr($h3 (I • (l₀ - k • z)))
    rw [A.H_smul_right] at h6
    generalize A.H (l₀ - k • z) (l₀ - k • z) = c at h5 h6
    simp at h6
    linarith
  rw [← sub_eq_zero.1 h4]
  exact l₀.2
end GlobalTheory.OfPeriod
