-- Prove2me | solution 1 for GlobalTheory.RowLaw.CvGroup.alongCv_congr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T05:36:45.773809+00:00
-- url     : https://prove2.me/submissions/9d3a21bb-367f-4c12-a492-e3a159f9d178

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
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_prod
import Theorems.Thm_ReciprocityTheory_PGsh_Up_MulStable_prod


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
noncomputable section
open GlobalTheory GlobalTheory.RowLaw GlobalTheory.RowLaw.CvGroup
variable {C : Type} [Field C]
namespace GlobalTheory.RowLaw.CvGroup
theorem _root_.solution {σ : Type} [Finite σ] {a b : σ → PowerSeries C}
    (ha : ∀ i, PowerSeries.constantCoeff (a i) = 0) (hb : ∀ i, PowerSeries.constantCoeff (b i) = 0) {n : ℕ}
    (hab : ∀ i, ∀ m < n, PowerSeries.coeff m (a i) = PowerSeries.coeff m (b i)) (f : MvPowerSeries σ C)
    (m : ℕ) (hm : m < n) :
    PowerSeries.coeff m (alongCv a f) = PowerSeries.coeff m (alongCv b f) := by
  unfold alongCv
  show MvPowerSeries.coeff (Finsupp.single () m) _ = MvPowerSeries.coeff (Finsupp.single () m) _
  rw [MvPowerSeries.coeff_subst (MvPowerSeries.hasSubst_of_constantCoeff_zero ha),
    MvPowerSeries.coeff_subst (MvPowerSeries.hasSubst_of_constantCoeff_zero hb)]
  refine finsum_congr fun e => ?_
  congr 1
  set J : Ideal (PowerSeries C) := Ideal.span {(PowerSeries.X : PowerSeries C) ^ n} with hJ
  have hq : ∀ i, Ideal.Quotient.mk J (a i) = Ideal.Quotient.mk J (b i) := by
    intro i
    rw [Ideal.Quotient.eq, hJ, Ideal.mem_span_singleton, PowerSeries.X_pow_dvd_iff]
    intro k hk
    rw [map_sub, hab i k hk, sub_self]
  have hp : Ideal.Quotient.mk J (e.prod fun s k => a s ^ k) = Ideal.Quotient.mk J (e.prod fun s k => b s ^ k) := by
    unfold Finsupp.prod
    rw [map_prod, map_prod]
    refine Finset.prod_congr rfl fun s _ => ?_
    rw [map_pow, map_pow, hq]
  rw [Ideal.Quotient.eq, hJ, Ideal.mem_span_singleton, PowerSeries.X_pow_dvd_iff] at hp
  have := hp m hm
  rw [map_sub, sub_eq_zero] at this
  exact this
end GlobalTheory.RowLaw.CvGroup
