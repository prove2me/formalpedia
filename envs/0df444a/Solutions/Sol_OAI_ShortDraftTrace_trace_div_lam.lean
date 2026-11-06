-- Prove2me | solution 1 for OAI.ShortDraftTrace.trace_div_lam
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:31:46.886414+00:00
-- url     : https://prove2.me/submissions/e176f4f8-20db-4d0c-8091-cd213aa7d794

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
omit hconj in
private lemma lam_ne_zero : (1 + 2 * ω : ℂ) ≠ 0 := by
  intro h
  have hw : ω = -(1 : ℂ) / 2 := by linear_combination h / 2
  rw [hw] at hω
  norm_num at hω
private lemma conj_lam : conj (1 + 2 * ω) = -(1 + 2 * ω) := by
  rw [map_add, map_one, map_mul, map_ofNat, hconj]
  linear_combination 2 * hω
omit hconj in
private lemma omega_sub_square : ω - ω ^ 2 = 1 + 2 * ω := by
  linear_combination -hω
end Generic
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
variable (ω : ℂ) (hω : ω ^ 2 + ω + 1 = 0)
  (hconj : conj ω = ω ^ 2)
include hω hconj
namespace OAI.ShortDraftTrace
theorem _root_.solution (a b : ℤ) :
    ((a : ℂ) + (b : ℂ) * ω) / (1 + 2 * ω) +
      conj (((a : ℂ) + (b : ℂ) * ω) / (1 + 2 * ω)) = (b : ℂ) := by
  have hl := lam_ne_zero ω hω
  simp only [map_div₀, map_add, map_intCast, map_mul, hconj,
    conj_lam ω hω hconj]
  rw [div_neg, ← sub_eq_add_neg, ← sub_div]
  calc
    ((a : ℂ) + (b : ℂ) * ω - ((a : ℂ) + (b : ℂ) * ω ^ 2)) /
        (1 + 2 * ω) = (b : ℂ) * (ω - ω ^ 2) / (1 + 2 * ω) := by ring
    _ = (b : ℂ) := by rw [omega_sub_square ω hω]; field_simp
end OAI.ShortDraftTrace
