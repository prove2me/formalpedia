-- Prove2me | solution 1 for GlobalTheory.RowLaw.CvGroup.rescale_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T05:44:31.481743+00:00
-- url     : https://prove2.me/submissions/d9865383-56c3-471e-9b6d-e3479a5a426c

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NondegenerateCharts
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieSelf
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BlockAdmissibleChart
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NegMem
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_StChartF
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TeichmullerDepth_HasTeich
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_AddCurveStableOfIntegralGaugedFormalGroupLawStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_GaugedFormalGroupCurveLogarithmsAddSubgroupResca
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_X
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_pow
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_mul_int
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_pow
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_alongCv_repar
import Theorems.Thm_ReciprocityTheory_PGsh_L2_h1
import Theorems.Thm_ReciprocityTheory_PGsh_L2_h2
import Theorems.Thm_ReciprocityTheory_PGsh_Up_MulStable_pow
import Theorems.Thm_ReciprocityTheory_PGsh_Up_Smith_blockOne_succ_succ_alt
import Theorems.Thm_ReciprocityTheory_PGsh_Up_Smith_blockOne_succ_zero_alt
import Theorems.Thm_ReciprocityTheory_PGsh_Up_Smith_blockOne_zero_succ_alt
import Theorems.Thm_ReciprocityTheory_PGsh_Up_Smith_blockOne_zero_zero_alt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.PGsh.Up.Smith.blockOne_succ_succ_alt
attribute [local simp] ReciprocityTheory.PGsh.Up.Smith.blockOne_succ_zero_alt
attribute [local simp] ReciprocityTheory.PGsh.Up.Smith.blockOne_zero_succ_alt
attribute [local simp] ReciprocityTheory.PGsh.Up.Smith.blockOne_zero_zero_alt



set_option autoImplicit false
open scoped BigOperators
open NumberField Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
noncomputable section
open GlobalTheory GlobalTheory.RowLaw GlobalTheory.RowLaw.CvGroup
variable {C : Type} [Field C]
variable {V : VF C} {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)] {κ : Type} [Fintype κ] {X : RawChart C d I κ}
namespace GlobalTheory.RowLaw.CvGroup
theorem _root_.solution (g : Fin 2) (s : C) (hs : V.Ge 0 s) : ∀ a ∈ Cv X V g,
    ((fun i => PowerSeries.rescale s (a.1 i), fun q => PowerSeries.rescale s (a.2 q)) :
      ((κ → PowerSeries C) × (JJ I g → PowerSeries C))) ∈ Cv X V g := by
  rintro a ⟨γ, lam, hγ, hlam, h1, h2⟩
  have hτ : PowerSeries.constantCoeff (s • (PowerSeries.X : PowerSeries C)) = 0 := by simp
  have hcv : ∀ {σ : Type} (δ : σ → PowerSeries C), IsCv V δ → IsCv V fun i => PowerSeries.rescale s (δ i) := by
    intro σ δ hδ i
    refine ⟨?_, fun n => ?_⟩
    · rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_rescale,
        PowerSeries.coeff_zero_eq_constantCoeff_apply, (hδ i).1, mul_zero]
    · rw [PowerSeries.coeff_rescale]
      exact (hs.pow n).mul_int ((hδ i).2 n)
  have hal : ∀ f, alongCv (fun i => PowerSeries.rescale s (γ i)) f = PowerSeries.rescale s (alongCv γ f) := by
    intro f
    simp only [PowerSeries.rescale_eq_subst]
    exact alongCv_repar (fun i => (hγ i).1) hτ f
  refine ⟨fun i => PowerSeries.rescale s (γ i), fun q => PowerSeries.rescale s (lam q), hcv γ hγ, hcv lam hlam, ?_, ?_⟩
  · intro i
    rw [hal, h1 i]
  · intro q
    show PowerSeries.rescale s (a.2 q) = _
    rw [hal, h2 q, map_sub]
end GlobalTheory.RowLaw.CvGroup
