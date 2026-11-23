-- Prove2me | solution 1 for GlobalTheory.TorsionFourier.add_nsmul_injective
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:52:33.695537+00:00
-- url     : https://prove2.me/submissions/4397460a-4457-494b-ac39-41f96014a001

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_FourierExtractionTsumClass

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
open GlobalTheory.TorsionFourier
variable {K X : Type} [Field K] [AddCommGroup X]
variable [Module.Free ℤ X] [Module.Finite ℤ X]
open Module
variable {K X : Type} [Field K] [AddCommGroup X]
variable [Module.Free ℤ X] [Module.Finite ℤ X]
omit [Module.Finite ℤ X]
namespace GlobalTheory.TorsionFourier
namespace _root_.GlobalTheory.TorsionFourier
theorem _root_.solution {N : ℕ} (hN : 0 < N) (α : X) :
    Function.Injective fun μ : X => α + N • μ := by
  intro μ ν h
  have h' : N • μ = N • ν := add_left_cancel h
  have h'' : (N : ℤ) • μ = (N : ℤ) • ν := by
    rw [Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul, h']
  exact smul_right_injective X (by exact_mod_cast hN.ne' : (N : ℤ) ≠ 0) h''
end _root_.GlobalTheory.TorsionFourier
end GlobalTheory.TorsionFourier
