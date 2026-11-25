-- Prove2me | solution 1 for GlobalTheory.MainTerm.Axis.vanishes_hM
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:50:43.604768+00:00
-- url     : https://prove2.me/submissions/d876597f-f8af-4a3a-8c5d-78c29b2b0291

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LatticeInclusionFormsInjective
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CartesianBoundOnCurves
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CoeffIterateZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_TwoMulChainStartIndexAddOneOfOdd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_CoeffLeafGaugeSubMainTermEqZeroOnFirstAxis
import Theorems.Thm_GlobalTheory_MainTerm_Axis_VanishesOnFirstAxis_smul
import Theorems.Thm_GlobalTheory_MainTerm_Axis_VanishesOnFirstAxis_sum
import Theorems.Thm_GlobalTheory_MainTerm_Axis_vanishes_X_inr
import Theorems.Thm_GlobalTheory_MainTerm_Axis_VanishesOnFirstAxis_of_dvd
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_X
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_sum
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_prod
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_sum


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds GlobalTheory.MainTerm Classical
open GlobalTheory GlobalTheory.MainTerm GlobalTheory.MainTerm.Axis
variable {C : Type} [Field C] {ι ι' : Type}
namespace GlobalTheory.MainTerm.Axis
theorem _root_.solution {V : VF C} {d : ℕ} [NeZero d] {I J : Fin 2 → Type} [∀ g, Fintype (I g)]
    [∀ g, Fintype (J g)] (X : RowData C V d I J) (g : Fin 2) (a : ZMod d) (i : ℕ)
    [Fintype ι] [Fintype ι'] (e : ι → I g → C) (v' : ι' → I (1 - g) → C) :
    VanishesOnFirstAxis (X.hM g a i e v') := by
  intro μ hμ
  unfold RowData.hM hPullW
  rw [MvPowerSeries.coeff_subst (MvPowerSeries.hasSubst_of_constantCoeff_zero (by
    intro w
    simp [map_sum]))]
  refine finsum_eq_zero_of_forall_eq_zero fun ν => ?_
  by_cases hν : ∀ w ∈ ν.support, w.1 = g
  · rw [X.hL_axes g _ _ ν (Or.inl hν), zero_smul]
  · push Not at hν
    obtain ⟨w, hw, hg⟩ := hν
    have h1 : VanishesOnFirstAxis
        ((∑ c : ι, toW g (e c) w • (MvPowerSeries.X (Sum.inl c) : MvPowerSeries (ι ⊕ ι') C)) +
          ∑ b : ι', toW (1 - g) (v' b) w •
            (MvPowerSeries.X (Sum.inr b) : MvPowerSeries (ι ⊕ ι') C)) := by
      have h0 : ∀ c, toW g (e c) w = 0 := fun c => by simp [toW, hg]
      simp only [h0, zero_smul, Finset.sum_const_zero, zero_add]
      exact VanishesOnFirstAxis.sum _ fun b => (vanishes_X_inr b).smul _
    rw [h1.of_dvd _ μ hμ, smul_zero]
    unfold Finsupp.prod
    exact (dvd_pow_self _ (Finsupp.mem_support_iff.1 hw)).trans (Finset.dvd_prod_of_mem _ hw)
end GlobalTheory.MainTerm.Axis
