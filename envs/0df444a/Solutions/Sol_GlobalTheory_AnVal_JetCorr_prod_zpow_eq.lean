-- Prove2me | solution 1 for GlobalTheory.AnVal.JetCorr.prod_zpow_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:50:36.137348+00:00
-- url     : https://prove2.me/submissions/4d1bc267-4869-4b19-96cd-1be9383ce34d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_ThConst
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ThExprUniqOfChartIndep2
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_FderivEqOfJetOf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_CorrOfJetsOfAnalyticFrameProducts
import Theorems.Thm_GlobalTheory_AnVal_JetCorr_prod_zpow_fiber

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
open GlobalTheory GlobalTheory.AnVal GlobalTheory.AnVal.JetCorr
open scoped Classical
namespace GlobalTheory.AnVal.JetCorr
theorem _root_.solution {M T K K' : Type*} [CommGroup M] [Fintype K] [Fintype K'] (φ : K → T) (ε : K → ℤ)
    (φ' : K' → T) (ε' : K' → ℤ) (u : K → M) (u' : K' → M)
    (h₁ : ∀ k l, φ k = φ l → u k = u l) (h₂ : ∀ k l, φ' k = φ' l → u' k = u' l)
    (h₃ : ∀ k l, φ k = φ' l → u k = u' l)
    (hs : ∀ ψ, (∑ k, if φ k = ψ then ε k else 0) = ∑ k', if φ' k' = ψ then ε' k' else 0) :
    ∏ k, u k ^ ε k = ∏ k, u' k ^ ε' k := by
  let w : T → M := fun ψ => if h : ∃ k, φ k = ψ then u h.choose else if h' : ∃ k, φ' k = ψ then u' h'.choose else 1
  have hw : ∀ k, u k = w (φ k) := fun k => by
    have h : ∃ l, φ l = φ k := ⟨k, rfl⟩
    simp only [w, dif_pos h]
    exact h₁ _ _ h.choose_spec.symm
  have hw' : ∀ k, u' k = w (φ' k) := fun k => by
    by_cases h : ∃ l, φ l = φ' k
    · simp only [w, dif_pos h]
      exact (h₃ _ _ h.choose_spec).symm
    · have h' : ∃ l, φ' l = φ' k := ⟨k, rfl⟩
      simp only [w, dif_neg h, dif_pos h']
      exact h₂ _ _ h'.choose_spec.symm
  simp only [hw, hw']
  rw [prod_zpow_fiber (Finset.univ.image φ ∪ Finset.univ.image φ') φ (fun k => by simp) ε w,
    prod_zpow_fiber (Finset.univ.image φ ∪ Finset.univ.image φ') φ' (fun k => by simp) ε' w]
  simp only [hs]
end GlobalTheory.AnVal.JetCorr
