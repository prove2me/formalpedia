-- Prove2me | solution 1 for GlobalTheory.eq_zero_of_forall_rat_smul_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:37:04.402617+00:00
-- url     : https://prove2.me/submissions/828fb9ce-ee5a-49d0-98e7-4cb19d397afe

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FiniteAndNcardSetOfSubmoduleLeRelIndexEqLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_RelIndexDualSubmoduleInfOfSelfDual

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module
open GlobalTheory
variable {V : Type*} [AddCommGroup V] [Module ℚ V]
namespace GlobalTheory
theorem _root_.solution (L : Submodule ℤ V) (hL : L.FG) {x : V}
    (hx : ∀ q : ℚ, q • x ∈ L) : x = 0 := by
  haveI : Module.Finite ℤ L := Module.Finite.iff_fg.2 hL
  haveI := Module.IsTorsionFree.trans_faithfulSMul ℤ ℚ V
  let b := Module.Free.chooseBasis ℤ L
  have h1 : x ∈ L := by simpa using hx 1
  have h2 : (⟨x, h1⟩ : L) = 0 := by
    refine b.repr.injective (Finsupp.ext fun i => ?_)
    rw [map_zero, Finsupp.zero_apply]
    set a := b.repr ⟨x, h1⟩ i with ha
    have hn : (0 : ℤ) < |a| + 1 := by positivity
    have h3 : (⟨x, h1⟩ : L) = (|a| + 1) • (⟨((|a| + 1 : ℤ) : ℚ)⁻¹ • x, hx _⟩ : L) := by
      apply Subtype.ext
      rw [Submodule.coe_smul, ← Int.cast_smul_eq_zsmul ℚ, smul_smul,
        mul_inv_cancel₀ (by exact_mod_cast hn.ne'), one_smul]
    refine Int.eq_zero_of_abs_lt_dvd (m := |a| + 1) ⟨b.repr ⟨_, hx ((|a| + 1 : ℤ) : ℚ)⁻¹⟩ i, ?_⟩
      (lt_add_one _)
    rw [← smul_eq_mul, ← Finsupp.smul_apply, ← map_smul, ← h3]
  exact congrArg Subtype.val h2
end GlobalTheory
