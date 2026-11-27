-- Prove2me | solution 1 for GlobalTheory.RowLaw.coeff_alongCv_congr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T05:23:19.465829+00:00
-- url     : https://prove2.me/submissions/2c5ab11a-adcd-4736-9655-f96b91756f4d

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NondegenerateCharts
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieSelf
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BlockAdmissibleChart
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NegMem
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_StChartF
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TeichmullerDepth_HasTeich
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_GaugedCurveLogarithmsClosedUnderTadicLimits
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_X
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_prod
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_Van_subst
import Theorems.Thm_ReciprocityTheory_PGsh_L2_h1
import Theorems.Thm_ReciprocityTheory_PGsh_L2_h2
import Theorems.Thm_ReciprocityTheory_PGsh_Up_MulStable_prod
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
open GlobalTheory GlobalTheory.RowLaw
namespace GlobalTheory.RowLaw
theorem _root_.solution {C : Type} [Field C] {κ : Type} [Finite κ] {a b : κ → PowerSeries C}
    (ha : ∀ i, PowerSeries.constantCoeff (a i) = 0) (hb : ∀ i, PowerSeries.constantCoeff (b i) = 0)
    (f : MvPowerSeries κ C) (m : ℕ)
    (h : ∀ i, ∀ k ≤ m, PowerSeries.coeff k (a i) = PowerSeries.coeff k (b i)) :
    PowerSeries.coeff m (alongCv a f) = PowerSeries.coeff m (alongCv b f) := by
  have hsa : MvPowerSeries.HasSubst a := MvPowerSeries.hasSubst_of_constantCoeff_zero ha
  have hsb : MvPowerSeries.HasSubst b := MvPowerSeries.hasSubst_of_constantCoeff_zero hb
  have hq : ∀ i, Ideal.Quotient.mk (Ideal.span {(PowerSeries.X : PowerSeries C) ^ (m + 1)}) (a i) =
      Ideal.Quotient.mk (Ideal.span {(PowerSeries.X : PowerSeries C) ^ (m + 1)}) (b i) := by
    intro i
    rw [Ideal.Quotient.eq, Ideal.mem_span_singleton, PowerSeries.X_pow_dvd_iff]
    intro k hk
    rw [map_sub, h i k (by omega), sub_self]
  have hp : ∀ e : κ →₀ ℕ, PowerSeries.coeff m (e.prod fun s n => a s ^ n) =
      PowerSeries.coeff m (e.prod fun s n => b s ^ n) := by
    intro e
    have h1 : Ideal.Quotient.mk (Ideal.span {(PowerSeries.X : PowerSeries C) ^ (m + 1)}) (e.prod fun s n => a s ^ n) =
        Ideal.Quotient.mk (Ideal.span {(PowerSeries.X : PowerSeries C) ^ (m + 1)}) (e.prod fun s n => b s ^ n) := by
      simp only [Finsupp.prod, map_prod, map_pow, hq]
    rw [Ideal.Quotient.eq, Ideal.mem_span_singleton, PowerSeries.X_pow_dvd_iff] at h1
    have h2 := h1 m (by omega)
    rwa [map_sub, sub_eq_zero] at h2
  show MvPowerSeries.coeff (Finsupp.single () m) (MvPowerSeries.subst a f) =
    MvPowerSeries.coeff (Finsupp.single () m) (MvPowerSeries.subst b f)
  rw [MvPowerSeries.coeff_subst hsa, MvPowerSeries.coeff_subst hsb]
  refine finsum_congr fun e => ?_
  exact congrArg (fun z => MvPowerSeries.coeff e f • z) (hp e)
end GlobalTheory.RowLaw
