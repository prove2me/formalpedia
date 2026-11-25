-- Prove2me | solution 1 for GlobalTheory.MainTerm.Kn_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:36:00.668441+00:00
-- url     : https://prove2.me/submissions/29b2e3f3-2e18-43e8-906b-1ae703e3a97f

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
variable {V : VF C} {d : ℕ} {I J : Type} [Fintype I] [Fintype J]
open Classical
variable {C : Type} [Field C]
variable {V : _root_.Formalism.L2.FormalSeriesBounds.VF C} {d : ℕ} {I J : Type} [Fintype I] [Fintype J]
namespace GlobalTheory.MainTerm
namespace _root_.GlobalTheory.MainTerm
theorem _root_.solution {i : ℕ} (hi : Odd i) :
    _root_.Formalism.BaseCaseIdentities.Kn i = _root_.Formalism.BaseCaseIdentities.s0 i + 1 := by
  obtain ⟨k, rfl⟩ := hi
  unfold _root_.Formalism.BaseCaseIdentities.s0 _root_.Formalism.BaseCaseIdentities.Kn
  omega
end _root_.GlobalTheory.MainTerm
end GlobalTheory.MainTerm
