-- Prove2me | solution 1 for GlobalTheory.T.coeff_leafGauge_sub_mainTerm_eq_zero_on_first_axis
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T01:08:21.893891+00:00
-- url     : https://prove2.me/submissions/6cb707f7-fa76-4d5f-a7c5-16c9e5b8b067

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_CoeffLeafGaugeSubMainTermEqZeroOnFirstAxis
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LatticeInclusionFormsInjective
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CartesianBoundOnCurves
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CoeffIterateZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_TwoMulChainStartIndexAddOneOfOdd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_CoeffLeafGaugeSubMainTermEqZeroOnFirstAxisStatement
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_X
import Theorems.Thm_GlobalTheory_MainTerm_Axis_coeff_hM_sub_mainM_eq_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds GlobalTheory.MainTerm Classical
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (C : Type) [Field C] (V : VF C) (d : ℕ) [NeZero d] (I J : Fin 2 → Type) [∀ g, Fintype (I g)] [∀ g, Fintype (J g)] (X : RowData C V d I J) (g : Fin 2) (a : ZMod d) (i : ℕ) (ι ι' : Type) [Fintype ι] [Fintype ι'] (e : ι → I g → C) (v' : ι' → I (1 - g) → C) (Φ : ι' → ι → C) (μ : ι ⊕ ι' →₀ ℕ), (∀ b, μ (Sum.inr b) = 0) → MvPowerSeries.coeff μ (X.hM g a i e v' - mainM V i Φ) = 0 := by
  first | exact @GlobalTheory.MainTerm.Axis.coeff_hM_sub_mainM_eq_zero | exact GlobalTheory.MainTerm.Axis.coeff_hM_sub_mainM_eq_zero | (intros; apply GlobalTheory.MainTerm.Axis.coeff_hM_sub_mainM_eq_zero <;> assumption)
end _root_.GlobalTheory.T
