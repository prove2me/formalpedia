-- Prove2me | solution 1 for NumberField.InfPlaceDecomp.eq_one_of_mem_decomp_of_sq_eq_neg_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/cc4c04f7-ca00-5a65-8fc7-cd9f7aaad455

import Mathlib
import Definitions.Def_NumberField_ArchimedeanIdeleModule
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_InfPlaceDecomp_eq_one_of_mem_decomp_of_sq_eq_neg_one

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 1600000
open NumberField
open scoped NumberField.InfPlaceDecomp

theorem solution
    (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] [Algebra E K] [IsGalois E K]
    (i : E) (hi : i ^ 2 = -1)
    (v : InfinitePlace K) (g : K ≃ₐ[E] K) (hg : g ∈ NumberField.InfPlaceDecomp.decomp E K v) : g = 1 := by
  classical
  by_cases hunr : InfinitePlace.IsUnramified E v
  ·
    have hbot := hunr.stabilizer_eq_bot
    have hg' : g ∈ MulAction.stabilizer (K ≃ₐ[E] K) v := hg
    rw [hbot] at hg'
    exact Subgroup.mem_bot.1 hg'
  · exfalso

    obtain ⟨-, hvR⟩ := InfinitePlace.not_isUnramified_iff.1 hunr
    set w := v.comap (algebraMap E K) with hw
    have hreal : ComplexEmbedding.IsReal w.embedding := InfinitePlace.isReal_iff.1 hvR
    have hconj : ComplexEmbedding.conjugate w.embedding = w.embedding := ComplexEmbedding.isReal_iff.1 hreal
    have h2 : starRingEnd ℂ (w.embedding i) = w.embedding i := by
      simpa [ComplexEmbedding.conjugate_coe_eq] using RingHom.congr_fun hconj i
    have h1 : (w.embedding i) ^ 2 = -1 := by rw [← map_pow, hi, map_neg, map_one]
    have hre : ((w.embedding i).re : ℂ) = w.embedding i := Complex.conj_eq_iff_re.1 h2
    rw [← hre, ← Complex.ofReal_pow, ← Complex.ofReal_one, ← Complex.ofReal_neg, Complex.ofReal_inj] at h1
    nlinarith [sq_nonneg (w.embedding i).re]

end S_NumberField_InfPlaceDecomp_eq_one_of_mem_decomp_of_sq_eq_neg_one
end P2MW
export P2MW.S_NumberField_InfPlaceDecomp_eq_one_of_mem_decomp_of_sq_eq_neg_one (solution)
