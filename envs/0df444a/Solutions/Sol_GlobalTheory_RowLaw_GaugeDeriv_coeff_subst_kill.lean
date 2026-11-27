-- Prove2me | solution 1 for GlobalTheory.RowLaw.GaugeDeriv.coeff_subst_kill
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T05:21:22.645284+00:00
-- url     : https://prove2.me/submissions/81f1ba00-614e-40ba-90c1-28310a5c0b16

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NondegenerateCharts
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieSelf
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BlockAdmissibleChart
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NegMem
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_StChartF
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_LogChain
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TeichmullerDepth_HasTeich
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_GaugeDerivEqPairingOfIntegralGaugedLaw
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_X
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_prod
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_Van_subst
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
noncomputable section
open scoped BigOperators
open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds MvPowerSeries
open GlobalTheory GlobalTheory.RowLaw GlobalTheory.RowLaw.GaugeDeriv
variable {C : Type} [Field C] {V : VF C} {σ τ υ : Type}
namespace GlobalTheory.RowLaw.GaugeDeriv
theorem _root_.solution [Finite τ] (e : σ ↪ τ) (f : MvPowerSeries τ C)
    (a : τ → MvPowerSeries σ C) (ha : ∀ t, a t = killCompl e (X t)) (x : σ →₀ ℕ) :
    coeff x (subst a f) = coeff (Finsupp.embDomain e x) f := by
  classical
  have hc : ∀ t, constantCoeff (a t) = 0 := fun t => by
    rw [ha, ← coeff_zero_eq_constantCoeff_apply, coeff_killCompl, Finsupp.embDomain_zero, coeff_zero_X]
  have hs : HasSubst a := hasSubst_of_constantCoeff_zero hc
  rw [coeff_subst hs, finsum_eq_single _ (Finsupp.embDomain e x)]
  · have : (Finsupp.embDomain e x).prod (fun s n => a s ^ n) = killCompl e (monomial (Finsupp.embDomain e x) 1) := by
      rw [monomial_one_eq, map_finsuppProd]; simp only [map_pow, ha]
    rw [this, coeff_killCompl, coeff_monomial_same, smul_eq_mul, mul_one]
  · intro d hd
    have : d.prod (fun s n => a s ^ n) = killCompl e (monomial d 1) := by
      rw [monomial_one_eq, map_finsuppProd]; simp only [map_pow, ha]
    rw [this, coeff_killCompl, coeff_monomial, if_neg (Ne.symm hd), smul_zero]
end GlobalTheory.RowLaw.GaugeDeriv
