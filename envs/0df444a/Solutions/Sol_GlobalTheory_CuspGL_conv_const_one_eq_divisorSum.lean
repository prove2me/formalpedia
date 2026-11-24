-- Prove2me | solution 1 for GlobalTheory.CuspGL.conv_const_one_eq_divisorSum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T14:04:03.085817+00:00
-- url     : https://prove2.me/submissions/96a49869-5088-47c0-8ac4-05aea5f06fc5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_AdditiveEqPolynomialVonMangoldtConvolutionOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open GlobalTheory GlobalTheory.CuspGL
variable {F : Type} [Field F]
namespace GlobalTheory.CuspGL
theorem _root_.solution (a : F[X] → ℂ) (P : F[X]) (hP : P.Monic) :
    conv a (fun _ => 1) P = ∑ᶠ D ∈ {D : F[X] | D.Monic ∧ D ∣ P}, a D := by
  unfold conv
  refine finsum_mem_eq_of_bijOn (fun x => x.1) ⟨?_, ?_, ?_⟩ ?_
  · rintro ⟨D, E⟩ ⟨hD, _, h⟩
    exact ⟨hD, E, h.symm⟩
  · rintro ⟨D, E⟩ ⟨hD, _, h⟩ ⟨D', E'⟩ ⟨_, _, h'⟩ h''
    simp only at h h' h'' hD
    subst h''
    rw [mul_left_cancel₀ hD.ne_zero (h.trans h'.symm)]
  · rintro D ⟨hD, E, h⟩
    exact ⟨(D, E), ⟨hD, hD.of_mul_monic_left (h ▸ hP), h.symm⟩, rfl⟩
  · intro x _
    simp
end GlobalTheory.CuspGL
