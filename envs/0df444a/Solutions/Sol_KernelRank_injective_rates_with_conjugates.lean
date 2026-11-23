-- Prove2me | solution 1 for KernelRank.injective_rates_with_conjugates
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T02:32:09.977682+00:00
-- url     : https://prove2.me/submissions/0d013c70-9c9f-41b8-a7fb-6f0fce7e471d

import Definitions.Def_KernelRankLean_ExpPoly
import Definitions.Def_KernelRankLean_RealExpPoly
import Theorems.Thm_KernelRank_expPoly_zero
attribute [local simp] KernelRank.expPoly_zero



set_option autoImplicit true
open Complex Polynomial
open KernelRank
namespace KernelRank
theorem _root_.solution {ι : Type*} {rate : ι → ℂ}
    (hinj : Function.Injective rate) (hup : ∀ i, 0 ≤ (rate i).im) :
    Function.Injective
      (Sum.elim rate (fun j : {i // 0 < (rate i).im} => starRingEnd ℂ (rate j.1))) := by
  rintro (a | a) (b | b) hab
  · exact congrArg Sum.inl (hinj hab)
  · have := congrArg Complex.im hab
    simp only [Sum.elim_inl, Sum.elim_inr, Complex.conj_im] at this
    linarith [hup a, b.2]
  · have := congrArg Complex.im hab
    simp only [Sum.elim_inl, Sum.elim_inr, Complex.conj_im] at this
    linarith [hup b, a.2]
  · exact congrArg Sum.inr
      (Subtype.ext (hinj (by simpa using congrArg (starRingEnd ℂ) hab)))
end KernelRank
