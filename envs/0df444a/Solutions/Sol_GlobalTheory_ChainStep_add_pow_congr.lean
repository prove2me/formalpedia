-- Prove2me | solution 1 for GlobalTheory.ChainStep.add_pow_congr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:43:48.898502+00:00
-- url     : https://prove2.me/submissions/c3446711-c284-4582-b6e0-e4eb5efc6774

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LatticeInclusionFormsInjective
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CartesianBoundOnCurves
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CoeffIterateZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_TwoMulChainStartIndexAddOneOfOdd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ChainStepKernelRankLeModMaxIdeal
import Theorems.Thm_GlobalTheory_ChainStep_mm_mul_int
import Theorems.Thm_GlobalTheory_ChainStep_mm_l

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
theorem _root_.solution {a b : C} (ha : V.Ge 0 a) (hb : V.Ge 0 b) (n : ℕ) :
    V.MM ((a + b) ^ (V.l ^ n) - (a ^ (V.l ^ n) + b ^ (V.l ^ n))) := by
  have h : ∃ r : intRing V, ((⟨a, ha⟩ : intRing V) + ⟨b, hb⟩) ^ (V.l ^ n) =
      (⟨a, ha⟩ : intRing V) ^ (V.l ^ n) + (⟨b, hb⟩ : intRing V) ^ (V.l ^ n) + (V.l : intRing V) * r := by
    obtain ⟨r, hr⟩ := exists_add_pow_prime_pow_eq V.l_prime (⟨a, ha⟩ : intRing V) ⟨b, hb⟩ n
    first
      | exact ⟨r, hr⟩
      | exact ⟨_, by rw [hr, mul_assoc, mul_assoc]⟩
  obtain ⟨r, hr⟩ := h
  have h2 := congrArg (fun z : intRing V => (z : C)) hr
  push_cast at h2
  rw [h2, add_sub_cancel_left]
  exact mm_mul_int mm_l r.2
end GlobalTheory.ChainStep
