-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Eis.line_tube_convex
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:26:16.272926+00:00
-- url     : https://prove2.me/submissions/0021c492-0848-41c2-a682-6d7fd2132c91

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_StripEntire
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IdentityTubeHolds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology PositivityTheory.RgEis
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Eis
namespace GlobalTheory.CompanionTheory.Eis
theorem _root_.solution {Ω : Set (ℝ × ℝ)} (hc : Convex ℝ Ω) (p v : ℂ × ℂ) :
    Convex ℝ {τ : ℂ | p + τ • v ∈ tube Ω} := by
  intro x hx y hy a b ha hb hab
  have key := hc hx hy ha hb hab
  simp only [tube, Set.mem_ofPred_eq] at hx hy key ⊢
  convert key using 1
  ext
  · simp only [Prod.fst_add, Prod.smul_fst, Complex.add_re, smul_eq_mul, Complex.real_smul,
      Complex.mul_re, Complex.mul_im, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, Prod.fst_add, Prod.smul_mk, Prod.mk_add_mk]
    linear_combination (-p.1.re) * hab
  · simp only [Prod.snd_add, Prod.smul_snd, Complex.add_re, smul_eq_mul, Complex.real_smul,
      Complex.mul_re, Complex.mul_im, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, Prod.smul_mk, Prod.mk_add_mk]
    linear_combination (-p.2.re) * hab
end GlobalTheory.CompanionTheory.Eis
