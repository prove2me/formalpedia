-- Prove2me | solution 1 for GlobalTheory.subsingleton_zmod_tensor_torsion
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:35:33.598334+00:00
-- url     : https://prove2.me/submissions/1590a1d3-2c30-420d-b07c-b06a4c7d6ee5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FinrankZmodTensorHomologyZeroOfNoPTorsion
import Theorems.Thm_GlobalTheory_exists_torsion_eq_prime_smul_of_noPTorsion

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {M : Type*} [AddCommGroup M] (p : ℕ) [Fact p.Prime]
    (hM : ∀ x : M, (p : ℤ) • x = 0 → x = 0) :
    Subsingleton (TensorProduct ℤ (ZMod p) (Submodule.torsion ℤ M)) := by
  refine subsingleton_of_forall_eq 0 fun z => ?_
  induction z using TensorProduct.induction_on with
  | zero => rfl
  | tmul c t =>
    obtain ⟨s, hs, hts⟩ := exists_torsion_eq_prime_smul_of_noPTorsion p hM t.1 t.2
    have : t = (p : ℤ) • (⟨s, hs⟩ : Submodule.torsion ℤ M) := Subtype.ext hts
    rw [this, ← TensorProduct.smul_tmul]
    have hc : (p : ℤ) • c = 0 := by
      rw [zsmul_eq_mul, Int.cast_natCast, ZMod.natCast_self, zero_mul]
    rw [hc, TensorProduct.zero_tmul]
  | add x y hx hy => rw [hx, hy, add_zero]
end GlobalTheory
