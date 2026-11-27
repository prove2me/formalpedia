-- Prove2me | solution 1 for GlobalTheory.RowLaw.cv_closed_under_limits
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T05:47:33.456597+00:00
-- url     : https://prove2.me/submissions/a05e8d09-c8de-4896-8a13-9815676ad945

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NondegenerateCharts
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieSelf
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BlockAdmissibleChart
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NegMem
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_StChartF
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TeichmullerDepth_HasTeich
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_GaugedCurveLogarithmsClosedUnderTadicLimits
import Theorems.Thm_GlobalTheory_RowLaw_coeff_alongCv_congr
import Theorems.Thm_GlobalTheory_RowLaw_exists_forall_le_of_eventually
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_X
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_Van_subst
import Theorems.Thm_ReciprocityTheory_PGsh_L2_h1
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
theorem _root_.solution : ∀ (C : Type) [Field C] (V : VF C) (d : ℕ) [NeZero d] (I : Fin 2 → Type) [∀ g, Fintype (I g)] (κ : Type) [Fintype κ] (X : RawChart C d I κ), RLaw X V → ∀ g (a : ℕ → ((κ → PowerSeries C) × (JJ I g → PowerSeries C))) (b : ((κ → PowerSeries C) × (JJ I g → PowerSeries C))), (∀ n, a n ∈ Cv X V g) → (∀ m, ∃ n0, ∀ n ≥ n0, (∀ i, PowerSeries.coeff m ((a n).1 i) = PowerSeries.coeff m (b.1 i)) ∧ ∀ q, PowerSeries.coeff m ((a n).2 q) = PowerSeries.coeff m (b.2 q)) → b ∈ Cv X V g := by
  intro C _ V d _ I _ κ _ X hR g a b ha hlim
  choose γ lam hγ hlam hlg hsg using ha
  have hlg0 : ∀ i, MvPowerSeries.constantCoeff (X.lg i) = 0 := by
    intro i
    have := hR.lin i 0 (by simp)
    simpa using this
  have hslg : MvPowerSeries.HasSubst X.lg := MvPowerSeries.hasSubst_of_constantCoeff_zero hlg0
  have hsex : MvPowerSeries.HasSubst X.ex := MvPowerSeries.hasSubst_of_constantCoeff_zero hR.exc
  have hsγ : ∀ n, MvPowerSeries.HasSubst (γ n) := fun n =>
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun i => (hγ n i).1
  have ha0 : ∀ n i, PowerSeries.constantCoeff ((a n).1 i) = 0 := by
    intro n i
    rw [← hlg n i]
    exact MvPowerSeries.constantCoeff_subst_eq_zero (hsγ n) (fun i => (hγ n i).1) (hlg0 i)
  have hb0 : ∀ i, PowerSeries.constantCoeff (b.1 i) = 0 := by
    intro i
    obtain ⟨n, hn⟩ := hlim 0
    have := (hn n le_rfl).1 i
    rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_zero_eq_constantCoeff_apply] at this
    rw [← this, ha0]
  have hsb : MvPowerSeries.HasSubst b.1 := MvPowerSeries.hasSubst_of_constantCoeff_zero hb0
  have hγeq : ∀ n i, γ n i = alongCv (a n).1 (X.ex i) := by
    intro n i
    have h1 : (a n).1 = fun j => MvPowerSeries.subst (γ n) (X.lg j) := funext fun j => (hlg n j).symm
    rw [h1]
    show γ n i = MvPowerSeries.subst (fun j => MvPowerSeries.subst (γ n) (X.lg j)) (X.ex i)
    rw [← MvPowerSeries.subst_comp_subst_apply hslg (hsγ n), hR.exlg, MvPowerSeries.subst_X (hsγ n)]
  let Γ : κ → PowerSeries C := fun i => alongCv b.1 (X.ex i)
  have hΓ0 : ∀ i, PowerSeries.constantCoeff (Γ i) = 0 := fun i =>
    MvPowerSeries.constantCoeff_subst_eq_zero hsb hb0 (hR.exc i)
  have key : ∀ m, ∃ n, (∀ i, ∀ k ≤ m, PowerSeries.coeff k (γ n i) = PowerSeries.coeff k (Γ i)) ∧
      ∀ q, PowerSeries.coeff m (lam n q) = PowerSeries.coeff m (b.2 q + alongCv Γ (X.sg (X.u (1 - g) q))) := by
    intro m
    obtain ⟨n, hn⟩ := exists_forall_le_of_eventually hlim m
    have h1 : ∀ i, ∀ k ≤ m, PowerSeries.coeff k (γ n i) = PowerSeries.coeff k (Γ i) := by
      intro i k hk
      rw [hγeq]
      exact coeff_alongCv_congr (ha0 n) hb0 _ k fun j k' hk' => (hn k' (hk'.trans hk)).1 j
    refine ⟨n, h1, fun q => ?_⟩
    rw [map_add, ← (hn m le_rfl).2 q, hsg n q, map_sub,
      coeff_alongCv_congr (fun i => (hγ n i).1) hΓ0 _ m h1, sub_add_cancel]
  refine ⟨Γ, fun q => b.2 q + alongCv Γ (X.sg (X.u (1 - g) q)), fun i => ⟨hΓ0 i, fun m => ?_⟩,
    fun q => ⟨?_, fun m => ?_⟩, fun i => ?_, fun q => by simp⟩
  · obtain ⟨n, hn, -⟩ := key m
    rw [← hn i m le_rfl]
    exact (hγ n i).2 m
  · obtain ⟨n, -, hn⟩ := key 0
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, ← hn q, PowerSeries.coeff_zero_eq_constantCoeff_apply]
    exact (hlam n q).1
  · obtain ⟨n, -, hn⟩ := key m
    rw [← hn q]
    exact (hlam n q).2 m
  · show MvPowerSeries.subst (fun j => MvPowerSeries.subst b.1 (X.ex j)) (X.lg i) = b.1 i
    rw [← MvPowerSeries.subst_comp_subst_apply hsex hsb, hR.lgex, MvPowerSeries.subst_X hsb]
end GlobalTheory.RowLaw
