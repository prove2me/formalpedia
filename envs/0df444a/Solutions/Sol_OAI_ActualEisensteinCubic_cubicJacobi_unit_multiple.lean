-- Prove2me | solution 1 for OAI.ActualEisensteinCubic.cubicJacobi_unit_multiple
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:40:03.308103+00:00
-- url     : https://prove2.me/submissions/d29c36eb-0f81-4790-b773-384d324b023c

import Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_EisensteinIdeals
import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_LogProfiles
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_FiniteFourier
import Theorems.Thm_OAI_ActualEisensteinCubic_cubicJacobi_mem_prime
import Theorems.Thm_OAI_ActualEisensteinCubic_cubicJacobi_mul_conj

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
open OAI.ActualEisensteinCubic
namespace OAI.ActualEisensteinCubic
theorem _root_.solution (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) (p : O) (hP : P = Ideal.span {p})
    (hnorm : p * conjO p = (Nat.card (O ⧸ P) : O)) :
    ∃ u : Oˣ, jacobiSum (cubicChar P hgood) (cubicChar P hgood) = p * u := by
  classical
  let J := jacobiSum (cubicChar P hgood) (cubicChar P hgood)
  have hdiv : p ∣ J := (Ideal.mem_span_singleton).mp (hP ▸ cubicJacobi_mem_prime P hgood)
  obtain ⟨v, hv⟩ := hdiv
  have hqne : (Nat.card (O ⧸ P) : O) ≠ 0 := by
    exact_mod_cast Nat.card_pos.ne'
  have hpne : p * conjO p ≠ 0 := by rw [hnorm]; exact hqne
  have hvnorm : v * conjO v = 1 := by
    apply mul_left_cancel₀ hpne
    calc
      (p * conjO p) * (v * conjO v) = (p * v) * conjO (p * v) := by
        rw [map_mul]; ring
      _ = J * conjO J := by rw [hv]
      _ = (Nat.card (O ⧸ P) : O) := cubicJacobi_mul_conj P hgood
      _ = (p * conjO p) * 1 := by rw [← hnorm, mul_one]
  have hvunit : IsUnit v := IsUnit.of_mul_eq_one (conjO v) hvnorm
  refine ⟨hvunit.unit, ?_⟩
  simpa only [hvunit.unit_spec] using hv
end OAI.ActualEisensteinCubic
