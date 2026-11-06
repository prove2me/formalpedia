-- Prove2me | solution 1 for OAI.PrimitiveTrace.eisTraceModChar_breveE_ne_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:37:39.88448+00:00
-- url     : https://prove2.me/submissions/ce71a77a-a013-4ce3-80e3-ad4e6622ca38

import Definitions.Def_OAI_NumberTheory_DirichletL_ChineseRemainder_AdditiveCharacters
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_FiniteFourier
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_ChineseRemainder
import Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_EisensteinEmbedding
import Theorems.Thm_OAI_IdealGaussCRT_traceProdChar_mk
import Theorems.Thm_OAI_ShortDraftTrace_omega_conj
attribute [local simp] OAI.IdealGaussCRT.traceProdChar_mk


section
namespace OAI
noncomputable section
open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
namespace EisensteinEmbedding
end EisensteinEmbedding
namespace ConcreteTraceCRT
open EisensteinEmbedding IdealGaussCRT
end ConcreteTraceCRT
namespace ConcreteBreveE
open EisensteinEmbedding ConcreteTraceCRT
end ConcreteBreveE
namespace ActualEisensteinCubic
open AddChar MulChar
open AddChar MulChar
end ActualEisensteinCubic
namespace PrimitiveTrace
open Complex
open scoped ComplexConjugate
open EisensteinEmbedding ConcreteTraceCRT
private theorem complex_exp_trace_integer {t : ℂ}
    (ht : Complex.exp (2 * Real.pi * Complex.I * t) = 1) :
    ∃ n : ℤ, t = n := by
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp ht
  refine ⟨n, ?_⟩
  have hnonzero : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
    exact mul_ne_zero (by exact_mod_cast mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) Real.pi_ne_zero) Complex.I_ne_zero
  apply mul_left_cancel₀ hnonzero
  calc
    (2 * Real.pi * Complex.I : ℂ) * t = n * (2 * Real.pi * Complex.I) := by
      simpa only [mul_assoc] using hn
    _ = (2 * Real.pi * Complex.I : ℂ) * n := by ring
private theorem phase_integer {z : ℂ}
    (hz : ShortDraftTrace.breveE (z / eisLam) = 1) :
    ∃ n : ℤ, z / eisLam + conj (z / eisLam) = n := by
  apply complex_exp_trace_integer
  exact hz
private theorem omega_conj : conj omega3 = omega3 ^ 2 := by
  have hs : omega3 ^ 2 = -omega3 - 1 := by
    linear_combination omega3_sq
  rw [hs]
  unfold omega3
  simp only [map_div₀, map_add, map_neg, map_one, map_mul,
    Complex.conj_ofReal, Complex.conj_I, map_ofNat]
  ring
private theorem reconstruction (z : ℂ) :
    z = (z / eisLam + conj (z / eisLam)) +
      (omega3 * z / eisLam + conj (omega3 * z / eisLam)) +
      (z / eisLam + conj (z / eisLam)) * omega3 := by
  have hquad := omega3_sq
  have hl : eisLam ≠ 0 := eisLam_ne_zero
  have hcl : conj eisLam = -eisLam := by
    simp only [eisLam, map_add, map_one, map_mul, map_ofNat, omega_conj]
    linear_combination 2 * hquad
  simp only [map_div₀, map_mul, omega_conj, hcl, div_neg]
  dsimp [eisLam] at *
  field_simp
  linear_combination (conj z) * hquad
private theorem in_coordinate_lattice_of_two_phases (z : ℂ)
    (hz : ShortDraftTrace.breveE (z / eisLam) = 1)
    (hwz : ShortDraftTrace.breveE (omega3 * z / eisLam) = 1) :
    z ∈ coordinateSubring := by
  obtain ⟨b, hb⟩ := phase_integer hz
  obtain ⟨c, hc⟩ := phase_integer hwz
  change ∃ a b : ℤ, z = (a : ℂ) + (b : ℂ) * omega3
  refine ⟨b + c, b, ?_⟩
  calc
    z = (z / eisLam + conj (z / eisLam)) +
      (omega3 * z / eisLam + conj (omega3 * z / eisLam)) +
      (z / eisLam + conj (z / eisLam)) * omega3 := reconstruction z
    _ = ((b + c : ℤ) : ℂ) + (b : ℂ) * omega3 := by
      rw [hb, hc]
      push_cast
      ring
end PrimitiveTrace
end
end OAI
end

set_option autoImplicit false
open OAI
noncomputable section
open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open OAI.PrimitiveTrace
open Complex
open scoped ComplexConjugate
open EisensteinEmbedding ConcreteTraceCRT
namespace OAI.PrimitiveTrace
theorem _root_.solution
    (P : Ideal O) [P.IsMaximal] (p : O)
    (hP : P = Ideal.span {p}) (hp : p ≠ 0) :
    eisTraceModChar ShortDraftTrace.breveE
      ConcreteBreveE.breveE_period_coordinates p hp ≠ 1 := by
  intro hψ
  let ι := eisEmbedding
  let z : ℂ := (ι p)⁻¹
  have hpι : ι p ≠ 0 := eisEmbedding_ne_zero hp
  have hbase1 : ∀ x : O,
      ShortDraftTrace.breveE (ι x / (ι p * eisLam)) = 1 := by
    intro x
    have hpoint := congrArg
      (fun f : AddChar (O ⧸ Ideal.span {p}) ℂ =>
        f (Ideal.Quotient.mk (Ideal.span {p}) x)) hψ
    simpa only [eisTraceModChar, IdealGaussCRT.traceModChar_mk,
      AddChar.one_apply] using hpoint
  have h1 : ShortDraftTrace.breveE (z / eisLam) = 1 := by
    convert hbase1 1 using 1 ; dsimp [z, ι] ; simp ; field_simp
  have hw : ShortDraftTrace.breveE (omega3 * z / eisLam) = 1 := by
    convert hbase1 pb.gen using 1
    · rw [show ι pb.gen = omega3 from embedding_gen omega3 omega3_sq]
      dsimp [z]
      field_simp
  have hz := in_coordinate_lattice_of_two_phases z h1 hw
  obtain ⟨q, hq⟩ := toCoordinateSubring_surjective ⟨z, hz⟩
  have hιq : ι q = z := congrArg Subtype.val hq
  have hpq : p * q = 1 := by
    apply eisEmbedding_injective
    rw [map_mul, map_one, hιq]
    dsimp [z]
    exact mul_inv_cancel₀ hpι
  have hunit : IsUnit p := isUnit_iff_dvd_one.mpr ⟨q, hpq.symm⟩
  have htop : P = ⊤ := by
    rw [hP]
    exact Ideal.span_singleton_eq_top.mpr hunit
  exact (inferInstance : P.IsMaximal).ne_top htop
end OAI.PrimitiveTrace
