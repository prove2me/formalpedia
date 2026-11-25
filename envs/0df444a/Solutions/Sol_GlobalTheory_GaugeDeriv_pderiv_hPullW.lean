-- Prove2me | solution 1 for GlobalTheory.GaugeDeriv.pderiv_hPullW
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:54:22.647821+00:00
-- url     : https://prove2.me/submissions/f7881fd0-f63b-4629-b064-a3725a0de80c

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LatticeInclusionFormsInjective
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CartesianBoundOnCurves
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CoeffIterateZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_TwoMulChainStartIndexAddOneOfOdd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_SubstEqOfCoeffEqOfKilled
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_NatCastMulCoeffOfPderivEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_PderivLeafGaugeEqPairingAddIntegral
import Theorems.Thm_GlobalTheory_GaugeDeriv_hPullW_eq
import Theorems.Thm_GlobalTheory_GaugeDeriv_hasSubst_linForm
import Theorems.Thm_GlobalTheory_GaugeDeriv_pderiv_linForm
import Theorems.Thm_GlobalTheory_GaugeDeriv_dVar_eq
import Theorems.Thm_GlobalTheory_GaugeDeriv_sum_toW
import Theorems.Thm_GlobalTheory_FormalCalc_pderiv_subst


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds GlobalTheory.MainTerm Classical
noncomputable section
open GlobalTheory GlobalTheory.GaugeDeriv
variable {C : Type} [Field C] {I : Fin 2 → Type} [∀ g, Fintype (I g)]
variable {ι ι' : Type} [Fintype ι] [Fintype ι']
namespace GlobalTheory.GaugeDeriv
theorem _root_.solution (H : MvPowerSeries (WV I) C) (e : ι → WV I → C) (g : Fin 2)
    (v' : ι' → I g → C) (b : ι') :
    MvPowerSeries.pderiv C (Sum.inr b) (hPullW H e (fun b => toW g (v' b))) =
      ∑ k, v' b k • hPullW (dVar ⟨g, k⟩ H) e (fun b => toW g (v' b)) := by
  have hs := hasSubst_linForm e (fun b => toW g (v' b))
  rw [hPullW_eq, GlobalTheory.FormalCalc.pderiv_subst hs]
  have key : ∀ w : WV I,
      MvPowerSeries.subst (linForm e (fun b => toW g (v' b))) (MvPowerSeries.pderiv C w H) *
          MvPowerSeries.pderiv C (Sum.inr b) (linForm e (fun b => toW g (v' b)) w) =
        toW g (v' b) w • hPullW (dVar w H) e (fun b => toW g (v' b)) := by
    intro w
    rw [pderiv_linForm, hPullW_eq, dVar_eq, MvPowerSeries.smul_eq_C_mul, mul_comm]
  rw [Finset.sum_congr rfl (fun w _ => key w)]
  exact sum_toW g (v' b) (fun w => hPullW (dVar w H) e (fun b => toW g (v' b)))
end GlobalTheory.GaugeDeriv
