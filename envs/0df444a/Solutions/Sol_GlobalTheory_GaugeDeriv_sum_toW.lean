-- Prove2me | solution 1 for GlobalTheory.GaugeDeriv.sum_toW
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:35:07.547391+00:00
-- url     : https://prove2.me/submissions/fadaa194-836d-4aa2-a96e-236b4dbdc90d

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LatticeInclusionFormsInjective
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CartesianBoundOnCurves
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CoeffIterateZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_TwoMulChainStartIndexAddOneOfOdd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_SubstEqOfCoeffEqOfKilled
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_NatCastMulCoeffOfPderivEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_PderivLeafGaugeEqPairingAddIntegral

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
theorem _root_.solution {M : Type} [AddCommGroup M] [Module C M] (g : Fin 2) (u : I g → C) (F : WV I → M) :
    ∑ w, toW g u w • F w = ∑ k, u k • F ⟨g, k⟩ := by
  rw [Fintype.sum_sigma, Finset.sum_eq_single g]
  · refine Finset.sum_congr rfl (fun k _ => ?_)
    simp [toW]
  · intro g' _ hg'
    refine Finset.sum_eq_zero (fun k _ => ?_)
    simp [toW, hg']
  · simp
end GlobalTheory.GaugeDeriv
