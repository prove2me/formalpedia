-- Prove2me | solution 1 for GlobalTheory.ChainStep.big_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:43:50.844211+00:00
-- url     : https://prove2.me/submissions/6c0f5c24-0353-41bb-9a33-9fdc32130698

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LatticeInclusionFormsInjective
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CartesianBoundOnCurves
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CoeffIterateZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_TwoMulChainStartIndexAddOneOfOdd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ChainStepKernelRankLeModMaxIdeal
import Theorems.Thm_GlobalTheory_ChainStep_even_val_add
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
noncomputable section
open GlobalTheory GlobalTheory.ChainStep
variable {C : Type} [Field C] {V : VF C}
namespace GlobalTheory.ChainStep
theorem _root_.solution {d : ℕ} [NeZero d] {I J : Fin 2 → Type} [∀ g, Fintype (I g)] [∀ g, Fintype (J g)]
    (X : RowData C V d I J) (hA : X.Alt) (g : Fin 2) (a : ZMod d) (h : X.big g a) (s : ℕ) :
    X.big g (a + ((2 * s : ℕ) : ZMod d)) := by
  fin_cases g
  · exact (hA.2 _).2 ((even_val_add hA.1 a s).2 ((hA.2 _).1 h))
  · have h1 : ∀ b, X.big 1 b ↔ ¬ X.big 0 b := fun b => by simpa using X.big_compl 0 b
    refine (h1 _).2 fun h2 => (h1 _).1 h ?_
    exact (hA.2 _).2 ((even_val_add hA.1 a s).1 ((hA.2 _).1 h2))
end GlobalTheory.ChainStep
