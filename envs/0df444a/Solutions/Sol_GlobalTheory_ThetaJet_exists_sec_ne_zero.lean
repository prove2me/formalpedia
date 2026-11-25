-- Prove2me | solution 1 for GlobalTheory.ThetaJet.exists_sec_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T16:36:54.49815+00:00
-- url     : https://prove2.me/submissions/e8ab9b4e-ba17-4a4e-a9f2-9f8d8416562b

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TBNFinal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_LevelThreeSeparatesTangents
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_MemAnalyticAtZeroOfEventuallyDifferentiableAt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_PredMulSumPadicValNatFactorialAddCardLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExistsTranslateJetNeZero
import Theorems.Thm_GlobalTheory_ThetaJet_twistedLaw_zero_iff
import Theorems.Thm_GlobalTheory_ThetaJet_TwistedLaw_mul
import Theorems.Thm_GlobalTheory_ThetaJet_twistedLaw_translate
import Theorems.Thm_GlobalTheory_ThetaJet_TwistedLaw_pow
import Theorems.Thm_GlobalTheory_constDerivEval_X
import Theorems.Thm_GlobalTheory_exists_mem_four_of_open_dense
import Theorems.Thm_GlobalTheory_lineDerivList_nil
import Theorems.Thm_GlobalTheory_lineDerivList_zero
import Theorems.Thm_GlobalTheory_pderivEval_X
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.constDerivEval_X
attribute [local simp] GlobalTheory.lineDerivList_nil
attribute [local simp] GlobalTheory.lineDerivList_zero
attribute [local simp] GlobalTheory.pderivEval_X



set_option autoImplicit false
open Complex ReciprocityTheory.ChartRestriction.G.I2 Filter Topology
open GlobalTheory
open GlobalTheory.ThetaJet
variable {ι : Type} [Fintype ι]
namespace GlobalTheory.ThetaJet
theorem _root_.solution {Y : GT ι} {θ : EuclideanSpace ℂ ι → ℂ} (hθ : θ ∈ Y.Sec 1)
    (h0 : θ ≠ 0) {r : ℕ} (hr : 2 ≤ r) : ∃ F ∈ (powTorus Y r).Sec r, F 0 ≠ 0 := by
  obtain ⟨p, rfl⟩ : ∃ p, r = p + 1 := ⟨r - 1, by omega⟩
  have hp : -(p : ℂ) ≠ 0 := by
    rw [neg_ne_zero, Nat.cast_ne_zero]; omega
  have hd : Differentiable ℂ θ := hθ.1
  have han : AnalyticOnNhd ℂ θ Set.univ := fun x _ => analyticAt_of_differentiable hd x
  set U : Set (EuclideanSpace ℂ ι) := {x | θ x ≠ 0} with hU
  have ho : IsOpen U := isOpen_ne_fun hd.continuous continuous_const
  have hden : Dense U := by
    intro x
    by_contra hx
    apply h0
    refine han.eq_of_eventuallyEq (g := 0) (z₀ := x) analyticOnNhd_const ?_
    filter_upwards [isClosed_closure.isOpen_compl.mem_nhds hx] with y hy
    by_contra hy'
    exact hy (subset_closure hy')
  obtain ⟨a, ha, hb, -⟩ := exists_mem_four_of_open_dense ho hden (Homeomorph.refl _)
    (Homeomorph.smulOfNeZero _ hp) (Homeomorph.refl _) (Homeomorph.refl _)
  have ha' : θ a ≠ 0 := ha
  have hb' : θ (-(p • a)) ≠ 0 := by
    have : θ ((-(p : ℂ)) • a) ≠ 0 := hb
    rwa [neg_smul, Nat.cast_smul_eq_nsmul] at this
  have h := ((twistedLaw_translate hθ a).pow p).mul (twistedLaw_translate hθ (-(p • a)))
  rw [add_neg_cancel, twistedLaw_zero_iff] at h
  exact ⟨_, h, by simp [ha', hb']⟩
end GlobalTheory.ThetaJet
