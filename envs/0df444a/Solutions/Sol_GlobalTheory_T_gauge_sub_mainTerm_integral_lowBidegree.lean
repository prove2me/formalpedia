-- Prove2me | solution 1 for GlobalTheory.T.gauge_sub_mainTerm_integral_lowBidegree
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T18:21:07.917238+00:00
-- url     : https://prove2.me/submissions/97a7d7a7-d47d-4156-8bde-4666d4e5042a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_GaugeSubMainTermIntegralLowBidegree
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LatticeInclusionFormsInjective
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CartesianBoundOnCurves
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CoeffIterateZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_TwoMulChainStartIndexAddOneOfOdd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_GaugeSubMainTermIntegralLowBidegreeStatement
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_X
import Theorems.Thm_GlobalTheory_MainTerm_mPlus_of_good_tangents


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
theorem _root_.solution : ∀ (C : Type) [Field C] (V : VF C) (d : ℕ) [NeZero d] (I J : Fin 2 → Type) [∀ g, Fintype (I g)] [∀ g, Fintype (J g)] (X : RowData C V d I J), X.Alt → 1 < d → ∀ (g : Fin 2) (a : ZMod d) (S : ∀ g, Sys (X.G g)) (t : ∀ g, I g → MvPowerSeries (I g) C), (∀ g, (S g).IsT (t g)) → ∀ (N : ℕ) (em : Fin N ↪ I g) (v' : Fin X.n → I (1 - g) → C), (∀ δ, (X.G g).ty (Sum.inl (em δ)) = a) → (∀ δ x, (S g).al (em δ) 1 x = 0) → (∀ b k, V.Ge 0 (v' b k)) → (∀ b k, (X.G (1 - g)).ty (Sum.inl k) ≠ a + ((1 : ℕ) : ZMod d) → v' b k = 0) → X.MPlusConcl g a N (fun δ => (S g).tan (em δ)) v' (fun b c => ∑ κ : J g, ∑ k : I (1 - g), -((V.l : C) * (S g).be (em c) 1 κ) * X.pair g κ k * v' b k) := by
  first | exact @GlobalTheory.MainTerm.mPlus_of_good_tangents | exact GlobalTheory.MainTerm.mPlus_of_good_tangents | (intros; apply GlobalTheory.MainTerm.mPlus_of_good_tangents <;> assumption)
end _root_.GlobalTheory.T
