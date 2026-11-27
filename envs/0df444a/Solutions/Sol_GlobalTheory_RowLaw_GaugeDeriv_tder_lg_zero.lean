-- Prove2me | solution 1 for GlobalTheory.RowLaw.GaugeDeriv.tder_lg_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T05:55:21.459967+00:00
-- url     : https://prove2.me/submissions/482e251d-7c14-44be-aa24-d764937083e2

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NondegenerateCharts
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieSelf
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BlockAdmissibleChart
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NegMem
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_StChartF
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_LogChain
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TeichmullerDepth_HasTeich
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_GaugeDerivEqPairingOfIntegralGaugedLaw
import Theorems.Thm_P2M_GlobalTheory_RowLaw_GaugeDeriv_subst_zero__1393311a9232
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_X
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_Van_subst
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_van_univ
import Theorems.Thm_ReciprocityTheory_PGsh_L2_h1
import Theorems.Thm_ReciprocityTheory_PGsh_L2_h2
import Theorems.Thm_ReciprocityTheory_PGsh_L2_h3
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
noncomputable section
open scoped BigOperators
open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds MvPowerSeries
open GlobalTheory GlobalTheory.RowLaw GlobalTheory.RowLaw.GaugeDeriv
variable {C : Type} [Field C] {V : VF C} {σ τ υ : Type}
variable {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)] {κ : Type} [Fintype κ] {Y : RawChart C d I κ}
variable (R : RLaw Y V)
include R
namespace GlobalTheory.RowLaw.GaugeDeriv
theorem _root_.solution (v : κ → C) (x : κ) :
    tder (fun _ : κ => (0 : MvPowerSeries τ C)) (fun i => MvPowerSeries.C (v i)) (Y.lg x) = MvPowerSeries.C (v x) := by
  classical
  have h1 : ∀ s, subst (fun _ : κ => (0 : MvPowerSeries τ C)) (pderiv C s (Y.lg x)) = if s = x then 1 else 0 := by
    intro s
    have h2 : constantCoeff (pderiv C s (Y.lg x - X x)) = 0 := by
      rw [← coeff_zero_eq_constantCoeff_apply, coeff_pderiv, map_sub, R.lin x _ (by simp), sub_self, zero_mul]
    have h3 : subst (fun _ : κ => (0 : MvPowerSeries τ C)) (pderiv C s (Y.lg x - X x)) = 0 := by
      ext μ
      exact Van.subst (T := ∅) Set.univ (fun _ => map_zero _) (fun _ _ ν _ => by simp) (van_univ h2) μ (by simp)
    have hs : HasSubst (fun _ : κ => (0 : MvPowerSeries τ C)) := hasSubst_of_constantCoeff_zero fun _ => map_zero _
    rw [map_sub, subst_sub hs, sub_eq_zero] at h3
    rw [h3]
    split_ifs with h
    · rw [h, pderiv_X_self, ← coe_substAlgHom hs, map_one]
    · rw [pderiv_X_of_ne (Ne.symm h), subst_zero' fun _ => map_zero _]
  simp [tder, h1]
end GlobalTheory.RowLaw.GaugeDeriv
