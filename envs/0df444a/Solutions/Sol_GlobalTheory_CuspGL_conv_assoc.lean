-- Prove2me | solution 1 for GlobalTheory.CuspGL.conv_assoc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T14:03:51.909432+00:00
-- url     : https://prove2.me/submissions/2bcfdc8b-2524-4d78-b99c-1b0a7c844fc8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_MonicFactorizationConvolutionFiniteCommAssocAdd
import Theorems.Thm_GlobalTheory_CuspGL_conv_eq_sum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial GlobalTheory.CuspGL
open GlobalTheory GlobalTheory.CuspGL
variable {F : Type} [Field F]
namespace GlobalTheory.CuspGL
theorem _root_.solution (a b c : F[X] → ℂ) (P : F[X]) :
    conv (conv a b) c P = conv a (conv b c) P := by
  rw [conv_eq_sum, conv_eq_sum]
  simp only [conv_eq_sum, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_sigma', Finset.sum_sigma']
  refine Finset.sum_nbij' (fun z => ⟨(z.2.1, z.2.2 * z.1.2), (z.2.2, z.1.2)⟩)
    (fun z => ⟨(z.1.1 * z.2.1, z.2.2), (z.1.1, z.2.1)⟩) ?_ ?_ ?_ ?_ ?_
  · rintro ⟨⟨D, E⟩, ⟨A, B⟩⟩ hx
    simp only [Finset.mem_sigma, Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hx ⊢
    obtain ⟨⟨h1, h2, h3⟩, h4, h5, h6⟩ := hx
    exact ⟨⟨h4, h5.mul h2, by rw [← mul_assoc, h6, h3]⟩, h5, h2, trivial⟩
  · rintro ⟨⟨D, E⟩, ⟨A, B⟩⟩ hx
    simp only [Finset.mem_sigma, Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hx ⊢
    obtain ⟨⟨h1, h2, h3⟩, h4, h5, h6⟩ := hx
    exact ⟨⟨h1.mul h4, h5, by rw [mul_assoc, h6, h3]⟩, h1, h4, trivial⟩
  · rintro ⟨⟨D, E⟩, ⟨A, B⟩⟩ hx
    simp only [Finset.mem_sigma, Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hx
    obtain ⟨⟨h1, h2, h3⟩, h4, h5, h6⟩ := hx
    subst h6
    rfl
  · rintro ⟨⟨D, E⟩, ⟨A, B⟩⟩ hx
    simp only [Finset.mem_sigma, Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hx
    obtain ⟨⟨h1, h2, h3⟩, h4, h5, h6⟩ := hx
    subst h6
    rfl
  · rintro ⟨⟨D, E⟩, ⟨A, B⟩⟩ _
    exact mul_assoc _ _ _
end GlobalTheory.CuspGL
