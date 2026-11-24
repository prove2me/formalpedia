-- Prove2me | solution 1 for GlobalTheory.CuspGL.IsAdditive.eq_divisorSum_mangoldt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T14:43:03.046284+00:00
-- url     : https://prove2.me/submissions/ed9cc360-39da-4c74-9a0a-4166f7371623

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_AdditiveEqPolynomialVonMangoldtConvolutionOne
import Theorems.Thm_GlobalTheory_CuspGL_mangoldt_eq_zero
import Theorems.Thm_GlobalTheory_CuspGL_mangoldt_divisorSum_mul

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
namespace IsAdditive
theorem _root_.solution {s : F[X] → ℂ} (hs : IsAdditive s) (P : F[X]) (hP : P.Monic) :
    s P = ∑ᶠ D ∈ {D : F[X] | D.Monic ∧ D ∣ P}, mangoldt s D := by
  induction hn : P.natDegree using Nat.strong_induction_on generalizing P with
  | _ n ih =>
    by_cases hu : IsUnit P
    · have h1 : P = 1 := hP.isUnit_iff.mp hu
      subst h1
      have h0 : s 1 = 0 := by
        have := hs 1 1 monic_one monic_one
        rw [mul_one] at this
        exact left_eq_add.mp this
      rw [h0]
      symm
      refine finsum_mem_of_eqOn_zero fun D hD => ?_
      refine mangoldt_eq_zero s D ?_
      rintro ⟨g, m, _, hg', hm, rfl⟩
      exact hg'.not_isUnit (isUnit_of_dvd_one ((dvd_pow_self g hm.ne').trans hD.2))
    · obtain ⟨f, hf, hf', Q, rfl⟩ := Polynomial.exists_monic_irreducible_factor P hu
      have hQ : Q.Monic := hf.of_mul_monic_left hP
      have hlt : Q.natDegree < n := by
        rw [← hn, hf.natDegree_mul hQ]
        have := hf'.natDegree_pos
        omega
      rw [mangoldt_divisorSum_mul s f Q hf hf' hQ, hs f Q hf hQ, ih _ hlt Q hQ rfl]
end IsAdditive
end GlobalTheory.CuspGL
