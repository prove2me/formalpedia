-- Prove2me | solution 1 for GlobalTheory.ThetaJet.jets_three
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T16:27:11.594509+00:00
-- url     : https://prove2.me/submissions/d28d0fe7-30c0-411d-93fc-c8af4a55b102

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
import Theorems.Thm_GlobalTheory_ThetaJet_coeff_single_taylorDir
import Theorems.Thm_GlobalTheory_ThetaJet_sub_affine_mem_sq
import Theorems.Thm_GlobalTheory_constDerivEval_X
import Theorems.Thm_GlobalTheory_level_three_separates_tangents
import Theorems.Thm_GlobalTheory_lineDerivList_nil
import Theorems.Thm_GlobalTheory_lineDerivList_zero
import Theorems.Thm_GlobalTheory_pderivEval_X
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_DimC_key
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
theorem _root_.solution {Y : GT ι} {θ : EuclideanSpace ℂ ι → ℂ} (hθ : θ ∈ Y.Sec 1) (h0 : θ ≠ 0)
    (x : MvPowerSeries ι ℂ) : ∃ s ∈ jets Y 3, x - s ∈ germIdeal ι ℂ ^ 2 := by
  classical
  have key : jets Y 3 ⊔ (germIdeal ι ℂ ^ 2).restrictScalars ℂ = ⊤ := by
    by_contra hne
    obtain ⟨φ, hφ0, hφ⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.2 hne)
    have hform : ∀ y, φ y = MvPowerSeries.constantCoeff y * φ 1 +
        ∑ i, MvPowerSeries.coeff (Finsupp.single i 1) y * φ (MvPowerSeries.X i) := by
      intro y
      have := hφ (Submodule.mem_sup_right (T := (germIdeal ι ℂ ^ 2).restrictScalars ℂ)
        (sub_affine_mem_sq y))
      rw [LinearMap.mem_ker, map_sub, sub_eq_zero] at this
      rw [this]
      simp
    set c : EuclideanSpace ℂ ι := ∑ i, φ (MvPowerSeries.X i) • EuclideanSpace.single i (1 : ℂ)
      with hc
    obtain ⟨h1, h2⟩ := level_three_separates_tangents Y θ hθ h0 (φ 1) c fun a b => by
      have h := ((twistedLaw_translate hθ a).mul (twistedLaw_translate hθ b)).mul
        (twistedLaw_translate hθ (-a - b))
      rw [show a + b + (-a - b) = 0 by abel, twistedLaw_zero_iff] at h
      have e : (((fun v => θ (v + a)) * fun v => θ (v + b)) * fun v => θ (v + (-a - b))) =
          fun v => θ (v + a) * θ (v + b) * θ (v - a - b) := by
        funext v
        simp only [Pi.mul_apply]
        congr 2
        abel
      rw [e] at h
      have h3 := hφ (Submodule.mem_sup_left (S := jets Y 3) ⟨_, h, rfl⟩)
      rw [LinearMap.mem_ker, hform, constantCoeff_taylorDir] at h3
      simp only [coeff_single_taylorDir _ (analyticAt_of_differentiable h.1 0)] at h3
      rw [hc, map_sum, ← h3]
      simp only [map_smul, smul_eq_mul, zero_add, zero_sub]
      congr 1
      · ring
      · exact Finset.sum_congr rfl fun i _ => mul_comm _ _
    have h3 : ∀ i, φ (MvPowerSeries.X i) = 0 := fun i => by
      have := congrArg (fun v : EuclideanSpace ℂ ι => v i) (hc.symm.trans h1)
      simpa [Pi.single_apply] using this
    apply hφ0
    ext y
    rw [hform]
    simp [h2, h3]
  obtain ⟨s, hs, w, hw, e⟩ := Submodule.mem_sup.1 (key ▸ Submodule.mem_top (x := x))
  exact ⟨s, hs, by rw [← e, add_sub_cancel_left]; exact hw⟩
end GlobalTheory.ThetaJet
