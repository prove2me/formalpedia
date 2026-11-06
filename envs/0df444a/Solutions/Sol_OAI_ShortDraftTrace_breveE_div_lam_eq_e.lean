-- Prove2me | solution 1 for OAI.ShortDraftTrace.breveE_div_lam_eq_e
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:05:23.586356+00:00
-- url     : https://prove2.me/submissions/ba54bfc4-7c63-4c20-a10b-503f5f2f67be

import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_LogProfiles
import Definitions.Def_OAI_NumberTheory_DirichletL_ChineseRemainder_AdditiveCharacters
section
namespace OAI
open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
namespace ShortDraftCRT
open AddChar
variable {K : Type*} [Field K]
variable {R : Type*} [CommRing R]
end ShortDraftCRT
namespace ShortDraftDescent
end ShortDraftDescent
namespace ShortDraftTrace
open Complex
open scoped ComplexConjugate
section Generic
variable (ω : ℂ) (hω : ω ^ 2 + ω + 1 = 0)
  (hconj : conj ω = ω ^ 2)
include hω hconj
end Generic
private theorem lam_eq_sqrt3_mul_I :
    1 + 2 * ω₃ = (Real.sqrt 3 : ℝ) * Complex.I := by
  unfold ω₃
  ring
private theorem sub_conj_eq (z : ℂ) :
    z - conj z = 2 * (z.im : ℂ) * Complex.I := by
  apply Complex.ext
  · simp [Complex.mul_re]
  · simp [Complex.mul_im]
    ring
end ShortDraftTrace
end OAI
end

set_option autoImplicit false
open OAI
open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open OAI.ShortDraftTrace
open Complex
open scoped ComplexConjugate
namespace OAI.ShortDraftTrace
theorem _root_.solution (z : ℂ) :
    breveE (z / (1 + 2 * ω₃)) =
      Complex.exp (4 * Real.pi * Complex.I * (z.im / Real.sqrt 3)) := by
  have hs : (Real.sqrt 3 : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  have hl : ((Real.sqrt 3 : ℝ) : ℂ) * Complex.I ≠ 0 :=
    mul_ne_zero (by exact_mod_cast hs) Complex.I_ne_zero
  change Complex.exp (2 * Real.pi * Complex.I *
    (z / (1 + 2 * ω₃) + conj (z / (1 + 2 * ω₃)))) = _
  rw [lam_eq_sqrt3_mul_I]
  have hc : conj (((Real.sqrt 3 : ℝ) : ℂ) * Complex.I) =
      -(((Real.sqrt 3 : ℝ) : ℂ) * Complex.I) := by
    simp [map_mul, Complex.conj_ofReal, Complex.conj_I]
  rw [map_div₀, hc, div_neg, ← sub_eq_add_neg, ← sub_div, sub_conj_eq]
  congr 1
  field_simp
  ring
end OAI.ShortDraftTrace
