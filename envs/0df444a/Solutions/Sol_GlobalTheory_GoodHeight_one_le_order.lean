-- Prove2me | solution 1 for GlobalTheory.GoodHeight.one_le_order
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:37:40.862871+00:00
-- url     : https://prove2.me/submissions/08a81f41-3d35-4ad6-b748-50eda8dccbc0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_LogDerivLFunctionStrip
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ImportsMore
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ExistsBoundRight

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.GoodHeight
namespace GlobalTheory.GoodHeight
theorem _root_.solution {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {w : ℂ} (h1 : w ≠ 1)
    (hw : LFunction χ w = 0) : 1 ≤ analyticOrderNatAt (LFunction χ) w := by
  have hU : IsPreconnected ({1}ᶜ : Set ℂ) :=
    (isConnected_compl_singleton_of_one_lt_rank (by rw [Complex.rank_real_complex]; norm_num) 1).isPreconnected
  have han : AnalyticOnNhd ℂ (LFunction χ) ({1}ᶜ : Set ℂ) := by
    intro z hz
    have hd : DifferentiableOn ℂ (LFunction χ) ({1}ᶜ : Set ℂ) := fun u hu =>
      (differentiableAt_LFunction χ u (.inl hu)).differentiableWithinAt
    exact hd.analyticAt (isOpen_compl_singleton.mem_nhds hz)
  have h2 : (2 : ℂ) ∈ ({1}ᶜ : Set ℂ) := by norm_num
  have hw1 : w ∈ ({1}ᶜ : Set ℂ) := h1
  have hne2 : analyticOrderAt (LFunction χ) 2 ≠ ⊤ := by
    rw [(han 2 h2).analyticOrderAt_eq_zero.mpr
      (LFunction_ne_zero_of_one_le_re χ (.inr (by norm_num)) (by norm_num))]
    exact ENat.zero_ne_top
  have hnetop := han.analyticOrderAt_ne_top_of_isPreconnected hU h2 hw1 hne2
  have hne0 : analyticOrderAt (LFunction χ) w ≠ 0 := (han w hw1).analyticOrderAt_ne_zero.mpr hw
  unfold analyticOrderNatAt
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp hnetop
  rw [← hn] at hne0 ⊢
  simp only [ENat.toNat_natCast]
  have : n ≠ 0 := by rintro rfl; exact hne0 rfl
  omega
end GlobalTheory.GoodHeight
