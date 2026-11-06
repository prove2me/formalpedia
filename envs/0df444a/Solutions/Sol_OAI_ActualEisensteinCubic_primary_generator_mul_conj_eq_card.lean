-- Prove2me | solution 1 for OAI.ActualEisensteinCubic.primary_generator_mul_conj_eq_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:42:47.735007+00:00
-- url     : https://prove2.me/submissions/3656d9dd-ffe3-4cc5-91b7-70710b2f5f01

import Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_EisensteinIdeals
import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_LogProfiles
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_FiniteFourier
import Theorems.Thm_OAI_ActualEisensteinCubic_cubicJacobi_mul_conj
import Theorems.Thm_OAI_ActualEisensteinCubic_cubicJacobi_eq_neg_primary_generator_of_principal

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
    (hprimary : lambda ^ 2 ∣ p - 1) :
    p * conjO p = (Nat.card (O ⧸ P) : O) := by
  have h := cubicJacobi_mul_conj P hgood
  rw [cubicJacobi_eq_neg_primary_generator_of_principal P hgood p hP hprimary,
    map_neg] at h
  simpa only [neg_mul_neg] using h
end OAI.ActualEisensteinCubic
