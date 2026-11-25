-- Prove2me | solution 1 for GlobalTheory.MainTerm.Axis.coeff_hM_sub_mainM_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:59:56.293786+00:00
-- url     : https://prove2.me/submissions/d87fbce2-fac4-4d61-82d0-3bf9f79f3b22

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LatticeInclusionFormsInjective
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CartesianBoundOnCurves
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CoeffIterateZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_TwoMulChainStartIndexAddOneOfOdd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_CoeffLeafGaugeSubMainTermEqZeroOnFirstAxis
import Theorems.Thm_GlobalTheory_MainTerm_Axis_vanishes_mainM
import Theorems.Thm_GlobalTheory_MainTerm_Axis_vanishes_hM
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_X


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
theorem _root_.solution : ∀ (C : Type) [Field C] (V : VF C) (d : ℕ) [NeZero d]
    (I J : Fin 2 → Type) [∀ g, Fintype (I g)] [∀ g, Fintype (J g)] (X : RowData C V d I J)
    (g : Fin 2) (a : ZMod d) (i : ℕ) (ι ι' : Type) [Fintype ι] [Fintype ι'] (e : ι → I g → C)
    (v' : ι' → I (1 - g) → C) (Φ : ι' → ι → C) (μ : ι ⊕ ι' →₀ ℕ), (∀ b, μ (Sum.inr b) = 0) →
    MvPowerSeries.coeff μ (X.hM g a i e v' - mainM V i Φ) = 0 := by
  intro C _ V d _ I J _ _ X g a i ι ι' _ _ e v' Φ μ hμ
  rw [map_sub, vanishes_hM X g a i e v' μ hμ, vanishes_mainM V i Φ μ hμ, sub_zero]
end GlobalTheory.MainTerm.Axis
