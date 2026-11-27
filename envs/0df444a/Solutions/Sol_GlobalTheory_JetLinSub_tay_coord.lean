-- Prove2me | solution 1 for GlobalTheory.JetLinSub.tay_coord
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:34:48.826368+00:00
-- url     : https://prove2.me/submissions/89d4107a-5550-4afc-ac42-19e2d2fe3275

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_ThConst
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ThExprUniqOfChartIndep2
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_AnHolFamOfHolTo
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_JetReadingLinearSubstitutionPoints
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_TM_mD_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_TM_pderiv_tay
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_TM_tay_const
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_constantCoeff_tay


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
open scoped ContDiff
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.JetLinSub
namespace GlobalTheory.JetLinSub
theorem _root_.solution {N : ℕ} (k : Fin N) :
    tay (fun v : Fin N → ℂ => v k) 0 = MvPowerSeries.X ((0 : Fin 1), k) := by
  classical
  have hθ : ContDiffAt ℂ ω (fun v : Fin N → ℂ => v k) 0 :=
    (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin N => ℂ) k).contDiff.contDiffAt
  ext n
  by_cases hn : n = 0
  · subst hn
    rw [MvPowerSeries.coeff_zero_eq_constantCoeff_apply, MvPowerSeries.coeff_zero_eq_constantCoeff_apply,
      constantCoeff_tay, TM.mD_zero]
    simp
  · obtain ⟨⟨a, j⟩, hp⟩ : ∃ p, n p ≠ 0 := by
      by_contra hc; push Not at hc; exact hn (Finsupp.ext hc)
    obtain rfl : a = 0 := Subsingleton.elim _ _
    obtain ⟨n', rfl⟩ : ∃ n', n = n' + Finsupp.single ((0 : Fin 1), j) 1 :=
      ⟨n - Finsupp.single ((0 : Fin 1), j) 1, (tsub_add_cancel_of_le
        (Finsupp.single_le_iff.2 (Nat.one_le_iff_ne_zero.2 hp))).symm⟩
    have h1 := TM.pderiv_tay hθ j
    have h2 : (fun y : Fin N → ℂ => fderiv ℂ (fun v : Fin N → ℂ => v k) y (Pi.single j 1)) =
        fun _ => (Pi.single j 1 : Fin N → ℂ) k := by
      funext y
      have := (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin N => ℂ) k).fderiv (x := y)
      exact congrArg (fun T : (Fin N → ℂ) →L[ℂ] ℂ => T (Pi.single j 1)) this
    rw [h2, TM.tay_const] at h1
    have h3 : MvPowerSeries.pderiv ℂ ((0 : Fin 1), j) (MvPowerSeries.X ((0 : Fin 1), k) :
        MvPowerSeries (Fin 1 × Fin N) ℂ) = MvPowerSeries.C ((Pi.single j 1 : Fin N → ℂ) k) := by
      rw [MvPowerSeries.pderiv_X]
      by_cases h : k = j
      · subst h; simp
      · simp [Prod.ext_iff, h]
    have h4 := congrArg (MvPowerSeries.coeff n') (h1.trans h3.symm)
    rw [MvPowerSeries.coeff_pderiv, MvPowerSeries.coeff_pderiv] at h4
    exact mul_right_cancel₀ (Nat.cast_add_one_ne_zero _) h4
end GlobalTheory.JetLinSub
