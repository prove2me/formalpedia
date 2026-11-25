-- Prove2me | solution 1 for GlobalTheory.MainTerm.chainMat_succ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:27:26.420275+00:00
-- url     : https://prove2.me/submissions/355c3077-38f3-4701-bdd2-e9d8fc22685d

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LatticeInclusionFormsInjective
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CartesianBoundOnCurves
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CoeffIterateZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_TwoMulChainStartIndexAddOneOfOdd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds
open Formalism.BaseCaseIdentities (Data Kn s0)
open Classical
noncomputable section
open GlobalTheory GlobalTheory.MainTerm
variable {C : Type} [Field C]
namespace GlobalTheory.MainTerm
theorem _root_.solution {Z I : Type} [Fintype I] (D : Data C Z I) (s : ℕ) (e c0 : I) :
    chainMat D (s + 1) e c0 = ∑ c ∈ Finset.univ.filter (fun c => D.lev c = s ∧ s < Kn D.i),
      (D.l : C) * D.al c 2 e * chainMat D s c c0 ^ (D.l ^ 2) := rfl
end GlobalTheory.MainTerm
