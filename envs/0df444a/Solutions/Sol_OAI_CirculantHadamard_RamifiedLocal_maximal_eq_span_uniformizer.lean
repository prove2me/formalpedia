-- Prove2me | solution 1 for OAI.CirculantHadamard.RamifiedLocal.maximal_eq_span_uniformizer
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T10:18:07.460046+00:00
-- url     : https://prove2.me/submissions/edf25fba-1f23-4414-8090-2881ca7902d5

import Mathlib
import Definitions.Def_CirculantHadamard
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_Basic
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_Witnesses
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_MatrixBridge
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclicRing
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclicNorm
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclicProjection
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_LocalDVR
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_IntegerTwoLocal
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclicEvaluation
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclicPolynomial
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_RamifiedConjugation
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclotomicIntegerEvaluation
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_DyadicRemainder
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_RamifiedEisenstein
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_RamifiedLocal

open OAI OAI.CirculantHadamard OAI.CirculantHadamard.RamifiedLocal
universe uA
open Polynomial
variable (A : Type uA) [CommRing A] [IsDomain A] [CharZero A]
  [IsDiscreteValuationRing A] {p : ℕ} (hp : p.Prime) (k : ℕ)
  (hmax : IsLocalRing.maximalIdeal A = Ideal.span {(p : A)})
include hp hmax
omit [CharZero A] in
theorem solution [CharZero A] (M : Ideal (Extension A p k)) [M.IsMaximal] :
    M = Ideal.span {uniformizer A p k} := by
  haveI : Fact p.Prime := ⟨hp⟩
  set u := uniformizer A p k with hu
  have hint : Algebra.IsIntegral A (Extension A p k) := Algebra.IsIntegral.of_finite A _
  have hcomap : M.comap (algebraMap A (Extension A p k)) = Ideal.span {(p : A)} := by
    rw [← hmax]
    exact IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal M)
  have hpM : (p : Extension A p k) ∈ M := by
    have : (p : A) ∈ M.comap (algebraMap A (Extension A p k)) := by
      rw [hcomap]; exact Ideal.subset_span rfl
    simpa using this
  -- p ∈ span {u}
  have hpu : (p : Extension A p k) ∈ Ideal.span {u} := by
    obtain ⟨q, hq⟩ := X_sub_C_dvd_sub_C_eval (a := (1 : A)) (p := cyclotomic (p ^ (k + 1)) A)
    rw [eval_one_cyclotomic_prime_pow] at hq
    have h1 := congrArg (AdjoinRoot.mk (cyclotomic (p ^ (k + 1)) A)) hq
    rw [map_sub, AdjoinRoot.mk_self, map_mul, map_sub, AdjoinRoot.mk_X, AdjoinRoot.mk_C,
      AdjoinRoot.mk_C, map_one, zero_sub, map_natCast] at h1
    rw [Ideal.mem_span_singleton]
    exact ⟨-AdjoinRoot.mk _ q, by rw [hu, uniformizer]; linear_combination -h1⟩
  -- u ∈ M
  have huM : u ∈ M := by
    let Q := Extension A p k ⧸ M
    haveI : Field Q := Ideal.Quotient.field M
    haveI : CharP Q p := (CharP.charP_iff_prime_eq_zero hp).2 (by
      rw [← map_natCast (Ideal.Quotient.mk M), Ideal.Quotient.eq_zero_iff_mem]; exact hpM)
    have hroot : (AdjoinRoot.root (cyclotomic (p ^ (k + 1)) A)) ^ (p ^ (k + 1)) = 1 := by
      have h : AdjoinRoot.mk (cyclotomic (p ^ (k + 1)) A) (X ^ (p ^ (k + 1)) - 1) = 0 :=
        AdjoinRoot.mk_eq_zero.mpr (cyclotomic.dvd_X_pow_sub_one _ A)
      simpa only [map_sub, map_pow, map_one, AdjoinRoot.mk_X, sub_eq_zero] using h
    have h0 : (Ideal.Quotient.mk M u) ^ (p ^ (k + 1)) = 0 := by
      rw [hu, uniformizer, map_sub, map_one, sub_pow_char_pow, ← map_pow, hroot, map_one, one_pow,
        sub_self]
    have := pow_eq_zero_iff (n := p ^ (k + 1)) (pow_ne_zero _ hp.ne_zero) |>.1 h0
    exact Ideal.Quotient.eq_zero_iff_mem.1 this
  apply le_antisymm
  · intro x hx
    obtain ⟨g, rfl⟩ := AdjoinRoot.mk_surjective x
    obtain ⟨q, hq⟩ := X_sub_C_dvd_sub_C_eval (a := (1 : A)) (p := g)
    have hg : AdjoinRoot.mk _ g = algebraMap A (Extension A p k) (g.eval 1) + u * AdjoinRoot.mk _ q := by
      have : g = C (g.eval 1) + (X - C 1) * q := by rw [← hq]; ring
      conv_lhs => rw [this]
      simp [hu, uniformizer, AdjoinRoot.mk_C, AdjoinRoot.algebraMap_eq]
    have ha : algebraMap A (Extension A p k) (g.eval 1) ∈ M := by
      have := M.sub_mem hx (M.mul_mem_right (AdjoinRoot.mk _ q) huM)
      rw [hg] at this; simpa using this
    have ha' : g.eval 1 ∈ Ideal.span {(p : A)} := by rw [← hcomap]; exact ha
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 ha'
    rw [hg, ← hc, map_mul, map_natCast]
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hpu)
      (Ideal.mul_mem_right _ _ (Ideal.subset_span rfl))
  · rw [Ideal.span_le, Set.singleton_subset_iff]; exact huM
