-- Prove2me | solution 1 for GlobalTheory.ActionLimit.exists_low
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T05:53:02.022228+00:00
-- url     : https://prove2.me/submissions/f5d47e4d-50ac-4b4c-80fd-4b322e30d9a7

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NondegenerateCharts
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieSelf
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BlockAdmissibleChart
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NegMem
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_StChartF
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TeichmullerDepth_HasTeich
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_ConstantCoeffEv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ActionConvergesLadicCauchyAndStar
import Theorems.Thm_GlobalTheory_ActionLimit_Low_mono
import Theorems.Thm_GlobalTheory_ActionLimit_exists_ge
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_mono
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_mono


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped BigOperators
open NumberField Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open GlobalTheory GlobalTheory.ActionLimit
open MvPowerSeries GlobalTheory.GaugeAdjoint
variable {C : Type} [Field C] {V : VF C} {σ τ : Type}
namespace GlobalTheory.ActionLimit
theorem _root_.solution (V : VF C) [Finite τ] {ι : Type} [Finite ι] (D : ℕ) (f : ι → MvPowerSeries τ C) :
    ∃ c : ℝ, ∀ i, Low V D c (f i) := by
  have hfin : {μ : τ →₀ ℕ | μ.degree ≤ D}.Finite := Finsupp.finite_of_degree_le D
  haveI := hfin.to_subtype
  choose c hc using fun p : ι × {μ : τ →₀ ℕ | μ.degree ≤ D} => exists_ge V (coeff p.2.1 (f p.1))
  obtain ⟨m, hm⟩ := (Set.finite_range c).bddBelow
  exact ⟨m, fun i μ hμ => (hc (i, ⟨μ, hμ⟩)).mono (hm ⟨_, rfl⟩)⟩
end GlobalTheory.ActionLimit
