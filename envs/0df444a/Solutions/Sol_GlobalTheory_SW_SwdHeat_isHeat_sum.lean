-- Prove2me | solution 1 for GlobalTheory.SW.SwdHeat.isHeat_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:42:27.315287+00:00
-- url     : https://prove2.me/submissions/830032d7-1534-4e54-a699-7465b9c9736b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_IsHeatThHStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_EisensteinSeriesOfSchwartzIsHolomorphic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_EisensteinSeriesOfSchwartzIsHolomorphicStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_FiniteClsAndStab
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_IsHeatSwd
import Theorems.Thm_GlobalTheory_SW_EisHeat_isHeat_tsum
import Theorems.Thm_GlobalTheory_SW_EisHeat_isOpen_dom
import Theorems.Thm_GlobalTheory_SW_ExpSum_isOpen_dom
import Theorems.Thm_GlobalTheory_SW_rowEmb_apply
import Theorems.Thm_GlobalTheory_spanCovol_bot
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.SW.rowEmb_apply
attribute [local simp] GlobalTheory.spanCovol_bot



set_option autoImplicit false
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.SwdHeat
open GlobalTheory.SW.EisHeat
variable {E : Type} [Field E] (Ψ : Finset (E →+* ℂ)) {n N : ℕ}
namespace GlobalTheory.SW.SwdHeat
theorem _root_.solution {ι : Type} [Fintype ι] {D : ι → CM Ψ N N → CM Ψ n N → CM Ψ n N → ℂ}
    (hD : ∀ i, IsHeat Ψ (D i)) : IsHeat Ψ fun Z z z' => ∑ i, D i Z z z' := by
  have h := isHeat_tsum Ψ hD fun p hp => by
    have hc : ∀ i, ∀ᶠ q : CF Ψ N N × CF Ψ n N × CF Ψ n N in 𝓝 p,
        ‖D i q.1 q.2.1 q.2.2‖ < ‖D i p.1 p.2.1 p.2.2‖ + 1 := fun i =>
      ((hD i).1.differentiableAt
        ((isOpen_dom Ψ).mem_nhds hp)).continuousAt.norm.eventually_lt_const (lt_add_one _)
    exact ⟨_, Filter.eventually_all.2 hc, fun i => ‖D i p.1 p.2.1 p.2.2‖ + 1,
      Summable.of_finite, fun i q hq => (hq i).le⟩
  simpa only [tsum_fintype] using h
end GlobalTheory.SW.SwdHeat
