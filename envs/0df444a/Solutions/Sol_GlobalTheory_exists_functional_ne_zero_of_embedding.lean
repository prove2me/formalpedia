-- Prove2me | solution 1 for GlobalTheory.exists_functional_ne_zero_of_embedding
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:42:37.998344+00:00
-- url     : https://prove2.me/submissions/ef01d773-2902-4016-80b1-7aefa748e1c1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsRationalMultiplierOfComplexMultiplier

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open Module
namespace GlobalTheory
theorem _root_.solution (K : Type) [Field K] (σ : K →+* ℂ) (m : ℂ)
    (hm : m ≠ 0) : ∃ φ : ℂ →+ K, (∀ (a : K) (c : ℂ), φ (σ a * c) = a * φ c) ∧ φ m ≠ 0 := by
  let _ : Algebra K ℂ := σ.toAlgebra
  obtain ⟨f, hf⟩ : ∃ f : Module.Dual K ℂ, f m ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hm ((Module.forall_dual_apply_eq_zero_iff K m).mp hcon)
  refine ⟨f.toAddMonoidHom, fun a c => ?_, hf⟩
  have hsmul : σ a * c = a • c := by
    rw [Algebra.smul_def, RingHom.algebraMap_toAlgebra]
  simp only [LinearMap.toAddMonoidHom_coe, hsmul, LinearMap.map_smul, smul_eq_mul]
end GlobalTheory
