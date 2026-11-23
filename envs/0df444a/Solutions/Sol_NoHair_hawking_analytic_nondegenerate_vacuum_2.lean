-- Prove2me | solution 2 for NoHair.hawking_analytic_nondegenerate_vacuum
-- status  : ACCEPTED   (disprove)
-- author  : @Igor Valuev
-- created : 2026-11-23T09:37:49.604533+00:00
-- url     : https://prove2.me/submissions/37bcc00d-051c-4ca9-9f28-705b71175e74

import Definitions.Def_NoHair_RegularCausalJoins
import Definitions.Def_NoHair_KerrNewmanEinstein_Ricci4
import Definitions.Def_NoHair_KerrNewmanEinstein_Ricci5
import Definitions.Def_NoHair_KerrNewmanEinstein_Ricci6
import Definitions.Def_NoHair_KerrNewmanEinstein_Christoffel
import Definitions.Def_NoHair_KerrNewmanEinstein_Div1
import Definitions.Def_NoHair_KerrNewmanEinstein_Div2
import Definitions.Def_NoHair_KerrNewmanEinstein_Div3
import Definitions.Def_NoHair_KerrNewmanEinstein_Div4
import Definitions.Def_NoHair_KerrNewmanEinstein_Atoms
import Definitions.Def_NoHair_KerrNewmanEinstein_Base
import Definitions.Def_NoHair_PseudoRiemannianNormalCoordinates
import Definitions.Def_NoHair_kerrNewman
import Definitions.Def_NoHair_kerrNewmanTimeDirection

/-!
# A vacuum Kerr inner horizon gives a counterexample to the stated milestone

The spacetime has mass 5/2, rotation parameter 2, zero charge, and reference
end r > 1. The inner-horizon geometry and causal estimates are adapted from
Prove2Me's Kerr inner-horizon counterexample and the standalone submission
01f94a82-9e5f-4091-9fb0-484b68a15e59. The time components of the Ricci tensor, its 11 component,
and the four connection traces are checked in the polynomial ring at these parameters.
-/
set_option linter.all false
set_option linter.unusedSimpArgs false
set_option Elab.async true

section
open scoped BigOperators
open NoHair NoHair.KNE
set_option maxRecDepth 12000
set_option maxHeartbeats 1000000

theorem NoHair.KNE.vacuumRic00 (R K1 K2 K3 W : ℝ) (hrel : K1 ^ 2 + K2 ^ 2 + K3 ^ 2 = 1)
    (hW : W * (R ^ 2 + (2 : ℝ) ^ 2 * K3 ^ 2) = 1) :
    RicS 2 (5/2) 0 R K1 K2 K3 W 0 0 = RicA 2 (5/2) 0 R K1 K2 K3 W 0 0 := by
  simp only [RicS, RicA, Gam, dDivT, Ric00, Matrix.cons_val, Fin.sum_univ_four]
  simp only [G000, G001, G002, G003, G011, G012, G013, G022, G023, G033, G100, G101, G102, G103, G111, G112, G113, G122, G123, G133, G200, G201, G202, G203, G211, G212, G213, G222, G223, G233, G300, G301, G302, G303, G311, G312, G313, G322, G323, G333, DD100, DD101, DD102, DD103, DD111, DD112, DD113, DD122, DD123, DD133, DD200, DD201, DD202, DD203, DD211, DD212, DD213, DD222, DD223, DD233, DD300, DD301, DD302, DD303, DD311, DD312, DD313, DD322, DD323, DD333]
  simp only [zero_pow (by decide : 2 ≠ 0), zero_pow (by decide : 4 ≠ 0), zero_mul, mul_zero, add_zero, zero_add, sub_zero, neg_zero]
  grobner

theorem NoHair.KNE.vacuumRic01 (R K1 K2 K3 W : ℝ) (hrel : K1 ^ 2 + K2 ^ 2 + K3 ^ 2 = 1)
    (hW : W * (R ^ 2 + (2 : ℝ) ^ 2 * K3 ^ 2) = 1) :
    RicS 2 (5/2) 0 R K1 K2 K3 W 0 1 = RicA 2 (5/2) 0 R K1 K2 K3 W 0 1 := by
  simp only [RicS, RicA, Gam, dDivT, Ric01, Matrix.cons_val, Fin.sum_univ_four]
  simp only [G000, G001, G002, G003, G011, G012, G013, G022, G023, G033, G100, G101, G102, G103, G111, G112, G113, G122, G123, G133, G200, G201, G202, G203, G211, G212, G213, G222, G223, G233, G300, G301, G302, G303, G311, G312, G313, G322, G323, G333, DD100, DD101, DD102, DD103, DD111, DD112, DD113, DD122, DD123, DD133, DD200, DD201, DD202, DD203, DD211, DD212, DD213, DD222, DD223, DD233, DD300, DD301, DD302, DD303, DD311, DD312, DD313, DD322, DD323, DD333]
  simp only [zero_pow (by decide : 2 ≠ 0), zero_pow (by decide : 4 ≠ 0), zero_mul, mul_zero, add_zero, zero_add, sub_zero, neg_zero]
  grobner

theorem NoHair.KNE.vacuumRic02 (R K1 K2 K3 W : ℝ) (hrel : K1 ^ 2 + K2 ^ 2 + K3 ^ 2 = 1)
    (hW : W * (R ^ 2 + (2 : ℝ) ^ 2 * K3 ^ 2) = 1) :
    RicS 2 (5/2) 0 R K1 K2 K3 W 0 2 = RicA 2 (5/2) 0 R K1 K2 K3 W 0 2 := by
  simp only [RicS, RicA, Gam, dDivT, Ric02, Matrix.cons_val, Fin.sum_univ_four]
  simp only [G000, G001, G002, G003, G011, G012, G013, G022, G023, G033, G100, G101, G102, G103, G111, G112, G113, G122, G123, G133, G200, G201, G202, G203, G211, G212, G213, G222, G223, G233, G300, G301, G302, G303, G311, G312, G313, G322, G323, G333, DD100, DD101, DD102, DD103, DD111, DD112, DD113, DD122, DD123, DD133, DD200, DD201, DD202, DD203, DD211, DD212, DD213, DD222, DD223, DD233, DD300, DD301, DD302, DD303, DD311, DD312, DD313, DD322, DD323, DD333]
  simp only [zero_pow (by decide : 2 ≠ 0), zero_pow (by decide : 4 ≠ 0), zero_mul, mul_zero, add_zero, zero_add, sub_zero, neg_zero]
  grobner

theorem NoHair.KNE.vacuumRic03 (R K1 K2 K3 W : ℝ) (hrel : K1 ^ 2 + K2 ^ 2 + K3 ^ 2 = 1)
    (hW : W * (R ^ 2 + (2 : ℝ) ^ 2 * K3 ^ 2) = 1) :
    RicS 2 (5/2) 0 R K1 K2 K3 W 0 3 = RicA 2 (5/2) 0 R K1 K2 K3 W 0 3 := by
  simp only [RicS, RicA, Gam, dDivT, Ric03, Matrix.cons_val, Fin.sum_univ_four]
  simp only [G000, G001, G002, G003, G011, G012, G013, G022, G023, G033, G100, G101, G102, G103, G111, G112, G113, G122, G123, G133, G200, G201, G202, G203, G211, G212, G213, G222, G223, G233, G300, G301, G302, G303, G311, G312, G313, G322, G323, G333, DD100, DD101, DD102, DD103, DD111, DD112, DD113, DD122, DD123, DD133, DD200, DD201, DD202, DD203, DD211, DD212, DD213, DD222, DD223, DD233, DD300, DD301, DD302, DD303, DD311, DD312, DD313, DD322, DD323, DD333]
  simp only [zero_pow (by decide : 2 ≠ 0), zero_pow (by decide : 4 ≠ 0), zero_mul, mul_zero, add_zero, zero_add, sub_zero, neg_zero]
  grobner

theorem NoHair.KNE.vacuumRic11 (R K1 K2 K3 W : ℝ) (hrel : K1 ^ 2 + K2 ^ 2 + K3 ^ 2 = 1)
    (hW : W * (R ^ 2 + (2 : ℝ) ^ 2 * K3 ^ 2) = 1) :
    RicS 2 (5/2) 0 R K1 K2 K3 W 1 1 = RicA 2 (5/2) 0 R K1 K2 K3 W 1 1 := by
  simp only [RicS, RicA, Gam, dDivT, Ric11, Matrix.cons_val, Fin.sum_univ_four]
  simp only [G000, G001, G002, G003, G011, G012, G013, G022, G023, G033, G100, G101, G102, G103, G111, G112, G113, G122, G123, G133, G200, G201, G202, G203, G211, G212, G213, G222, G223, G233, G300, G301, G302, G303, G311, G312, G313, G322, G323, G333, DD100, DD101, DD102, DD103, DD111, DD112, DD113, DD122, DD123, DD133, DD200, DD201, DD202, DD203, DD211, DD212, DD213, DD222, DD223, DD233, DD300, DD301, DD302, DD303, DD311, DD312, DD313, DD322, DD323, DD333]
  simp only [zero_pow (by decide : 2 ≠ 0), zero_pow (by decide : 4 ≠ 0), zero_mul, mul_zero, add_zero, zero_add, sub_zero, neg_zero]
  grobner

end

section
set_option autoImplicit false

open scoped BigOperators
open NoHair NoHair.KNE

theorem NoHair.KNE.thm_christoffel (z : E4) (hz : 0 < ksRadius (2:ℝ) z) (i j k : Fin 4) :
    christoffel (kerrNewmanMetric (5/2:ℝ) (2:ℝ) (0:ℝ)) z i j k = Gam (2:ℝ) (5/2:ℝ) (0:ℝ) (ksRadius (2:ℝ) z) (ksNull (2:ℝ) z 1) (ksNull (2:ℝ) z 2) (ksNull (2:ℝ) z 3) (Wf (2:ℝ) z) i j k :=
  NoHair.KNE.chr_closed (5/2) 2 0 z hz i j k

end

section
set_option autoImplicit false

open scoped BigOperators
open NoHair NoHair.KNE

theorem NoHair.KNE.thm_div_one (y : E4) (hy : 0 < ksRadius (2:ℝ) y) :
    (∀ σ, DifferentiableAt ℝ (fun w => Gam (2:ℝ) (5/2:ℝ) (0:ℝ) (ksRadius (2:ℝ) w) (ksNull (2:ℝ) w 1) (ksNull (2:ℝ) w 2) (ksNull (2:ℝ) w 3) (Wf (2:ℝ) w) 0 0 σ) y) ∧
    (∀ σ, DifferentiableAt ℝ (fun w => Gam (2:ℝ) (5/2:ℝ) (0:ℝ) (ksRadius (2:ℝ) w) (ksNull (2:ℝ) w 1) (ksNull (2:ℝ) w 2) (ksNull (2:ℝ) w 3) (Wf (2:ℝ) w) 1 1 σ) y) ∧
    (∀ ν σ, coordPartial (fun w => Gam (2:ℝ) (5/2:ℝ) (0:ℝ) (ksRadius (2:ℝ) w) (ksNull (2:ℝ) w 1) (ksNull (2:ℝ) w 2) (ksNull (2:ℝ) w 3) (Wf (2:ℝ) w) 1 ν σ) 1 y = dDivT (2:ℝ) (5/2:ℝ) (0:ℝ) (ksRadius (2:ℝ) y) (ksNull (2:ℝ) y 1) (ksNull (2:ℝ) y 2) (ksNull (2:ℝ) y 3) (Wf (2:ℝ) y) 1 ν σ) := by
  refine ⟨?_, ?_, ?_⟩
  · intro σ
    fin_cases σ <;> simp only [Gam, Matrix.cons_val, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk]
    · exact NoHair.KNE.dG000 (5/2) 2 0 y hy
    · exact NoHair.KNE.dG001 (5/2) 2 0 y hy
    · exact NoHair.KNE.dG002 (5/2) 2 0 y hy
    · exact NoHair.KNE.dG003 (5/2) 2 0 y hy
  · intro σ
    fin_cases σ <;> simp only [Gam, Matrix.cons_val, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk]
    · exact (NoHair.KNE.dG101 (5/2) 2 0 y hy).1
    · exact (NoHair.KNE.dG111 (5/2) 2 0 y hy).1
    · exact (NoHair.KNE.dG112 (5/2) 2 0 y hy).1
    · exact (NoHair.KNE.dG113 (5/2) 2 0 y hy).1
  · intro ν σ
    fin_cases ν <;> fin_cases σ <;> simp only [Gam, dDivT, Matrix.cons_val, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk]
    · exact (NoHair.KNE.dG100 (5/2) 2 0 y hy).2
    · exact (NoHair.KNE.dG101 (5/2) 2 0 y hy).2
    · exact (NoHair.KNE.dG102 (5/2) 2 0 y hy).2
    · exact (NoHair.KNE.dG103 (5/2) 2 0 y hy).2
    · exact (NoHair.KNE.dG101 (5/2) 2 0 y hy).2
    · exact (NoHair.KNE.dG111 (5/2) 2 0 y hy).2
    · exact (NoHair.KNE.dG112 (5/2) 2 0 y hy).2
    · exact (NoHair.KNE.dG113 (5/2) 2 0 y hy).2
    · exact (NoHair.KNE.dG102 (5/2) 2 0 y hy).2
    · exact (NoHair.KNE.dG112 (5/2) 2 0 y hy).2
    · exact (NoHair.KNE.dG122 (5/2) 2 0 y hy).2
    · exact (NoHair.KNE.dG123 (5/2) 2 0 y hy).2
    · exact (NoHair.KNE.dG103 (5/2) 2 0 y hy).2
    · exact (NoHair.KNE.dG113 (5/2) 2 0 y hy).2
    · exact (NoHair.KNE.dG123 (5/2) 2 0 y hy).2
    · exact (NoHair.KNE.dG133 (5/2) 2 0 y hy).2

end

section
set_option autoImplicit false

open scoped BigOperators
open NoHair NoHair.KNE

theorem NoHair.KNE.thm_div_two (y : E4) (hy : 0 < ksRadius (2:ℝ) y) :
    (∀ σ, DifferentiableAt ℝ (fun w => Gam (2:ℝ) (5/2:ℝ) (0:ℝ) (ksRadius (2:ℝ) w) (ksNull (2:ℝ) w 1) (ksNull (2:ℝ) w 2) (ksNull (2:ℝ) w 3) (Wf (2:ℝ) w) 2 2 σ) y) ∧
    (∀ ν σ, coordPartial (fun w => Gam (2:ℝ) (5/2:ℝ) (0:ℝ) (ksRadius (2:ℝ) w) (ksNull (2:ℝ) w 1) (ksNull (2:ℝ) w 2) (ksNull (2:ℝ) w 3) (Wf (2:ℝ) w) 2 ν σ) 2 y = dDivT (2:ℝ) (5/2:ℝ) (0:ℝ) (ksRadius (2:ℝ) y) (ksNull (2:ℝ) y 1) (ksNull (2:ℝ) y 2) (ksNull (2:ℝ) y 3) (Wf (2:ℝ) y) 2 ν σ) := by
  refine ⟨?_, ?_⟩
  · intro σ
    fin_cases σ <;> simp only [Gam, Matrix.cons_val, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk]
    · exact (NoHair.KNE.dG202 (5/2) 2 0 y hy).1
    · exact (NoHair.KNE.dG212 (5/2) 2 0 y hy).1
    · exact (NoHair.KNE.dG222 (5/2) 2 0 y hy).1
    · exact (NoHair.KNE.dG223 (5/2) 2 0 y hy).1
  · intro ν σ
    fin_cases ν <;> fin_cases σ <;> simp only [Gam, dDivT, Matrix.cons_val, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk]
    · exact (NoHair.KNE.dG200 (5/2) 2 0 y hy).2
    · exact (NoHair.KNE.dG201 (5/2) 2 0 y hy).2
    · exact (NoHair.KNE.dG202 (5/2) 2 0 y hy).2
    · exact (NoHair.KNE.dG203 (5/2) 2 0 y hy).2
    · exact (NoHair.KNE.dG201 (5/2) 2 0 y hy).2
    · exact (NoHair.KNE.dG211 (5/2) 2 0 y hy).2
    · exact (NoHair.KNE.dG212 (5/2) 2 0 y hy).2
    · exact (NoHair.KNE.dG213 (5/2) 2 0 y hy).2
    · exact (NoHair.KNE.dG202 (5/2) 2 0 y hy).2
    · exact (NoHair.KNE.dG212 (5/2) 2 0 y hy).2
    · exact (NoHair.KNE.dG222 (5/2) 2 0 y hy).2
    · exact (NoHair.KNE.dG223 (5/2) 2 0 y hy).2
    · exact (NoHair.KNE.dG203 (5/2) 2 0 y hy).2
    · exact (NoHair.KNE.dG213 (5/2) 2 0 y hy).2
    · exact (NoHair.KNE.dG223 (5/2) 2 0 y hy).2
    · exact (NoHair.KNE.dG233 (5/2) 2 0 y hy).2

end

section
set_option autoImplicit false

open scoped BigOperators
open NoHair NoHair.KNE

theorem NoHair.KNE.thm_div_three (y : E4) (hy : 0 < ksRadius (2:ℝ) y) :
    (∀ σ, DifferentiableAt ℝ (fun w => Gam (2:ℝ) (5/2:ℝ) (0:ℝ) (ksRadius (2:ℝ) w) (ksNull (2:ℝ) w 1) (ksNull (2:ℝ) w 2) (ksNull (2:ℝ) w 3) (Wf (2:ℝ) w) 3 3 σ) y) ∧
    (∀ ν σ, coordPartial (fun w => Gam (2:ℝ) (5/2:ℝ) (0:ℝ) (ksRadius (2:ℝ) w) (ksNull (2:ℝ) w 1) (ksNull (2:ℝ) w 2) (ksNull (2:ℝ) w 3) (Wf (2:ℝ) w) 3 ν σ) 3 y = dDivT (2:ℝ) (5/2:ℝ) (0:ℝ) (ksRadius (2:ℝ) y) (ksNull (2:ℝ) y 1) (ksNull (2:ℝ) y 2) (ksNull (2:ℝ) y 3) (Wf (2:ℝ) y) 3 ν σ) := by
  refine ⟨?_, ?_⟩
  · intro σ
    fin_cases σ <;> simp only [Gam, Matrix.cons_val, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk]
    · exact (NoHair.KNE.dG303 (5/2) 2 0 y hy).1
    · exact (NoHair.KNE.dG313 (5/2) 2 0 y hy).1
    · exact (NoHair.KNE.dG323 (5/2) 2 0 y hy).1
    · exact (NoHair.KNE.dG333 (5/2) 2 0 y hy).1
  · intro ν σ
    fin_cases ν <;> fin_cases σ <;> simp only [Gam, dDivT, Matrix.cons_val, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk]
    · exact (NoHair.KNE.dG300 (5/2) 2 0 y hy).2
    · exact (NoHair.KNE.dG301 (5/2) 2 0 y hy).2
    · exact (NoHair.KNE.dG302 (5/2) 2 0 y hy).2
    · exact (NoHair.KNE.dG303 (5/2) 2 0 y hy).2
    · exact (NoHair.KNE.dG301 (5/2) 2 0 y hy).2
    · exact (NoHair.KNE.dG311 (5/2) 2 0 y hy).2
    · exact (NoHair.KNE.dG312 (5/2) 2 0 y hy).2
    · exact (NoHair.KNE.dG313 (5/2) 2 0 y hy).2
    · exact (NoHair.KNE.dG302 (5/2) 2 0 y hy).2
    · exact (NoHair.KNE.dG312 (5/2) 2 0 y hy).2
    · exact (NoHair.KNE.dG322 (5/2) 2 0 y hy).2
    · exact (NoHair.KNE.dG323 (5/2) 2 0 y hy).2
    · exact (NoHair.KNE.dG303 (5/2) 2 0 y hy).2
    · exact (NoHair.KNE.dG313 (5/2) 2 0 y hy).2
    · exact (NoHair.KNE.dG323 (5/2) 2 0 y hy).2
    · exact (NoHair.KNE.dG333 (5/2) 2 0 y hy).2

end

section
set_option autoImplicit false

open scoped BigOperators
open NoHair NoHair.KNE

theorem NoHair.KNE.thm_ricci_a (R K1 K2 K3 W : ℝ) (hrel : K1 ^ 2 + K2 ^ 2 + K3 ^ 2 = 1) (hW : W * (R ^ 2 + (2:ℝ) ^ 2 * K3 ^ 2) = 1) :
    RicS (2:ℝ) (5/2:ℝ) (0:ℝ) R K1 K2 K3 W 0 0 = RicA (2:ℝ) (5/2:ℝ) (0:ℝ) R K1 K2 K3 W 0 0 ∧
    RicS (2:ℝ) (5/2:ℝ) (0:ℝ) R K1 K2 K3 W 0 1 = RicA (2:ℝ) (5/2:ℝ) (0:ℝ) R K1 K2 K3 W 0 1 ∧
    RicS (2:ℝ) (5/2:ℝ) (0:ℝ) R K1 K2 K3 W 0 2 = RicA (2:ℝ) (5/2:ℝ) (0:ℝ) R K1 K2 K3 W 0 2 ∧
    RicS (2:ℝ) (5/2:ℝ) (0:ℝ) R K1 K2 K3 W 0 3 = RicA (2:ℝ) (5/2:ℝ) (0:ℝ) R K1 K2 K3 W 0 3 :=
  ⟨NoHair.KNE.vacuumRic00 R K1 K2 K3 W hrel hW, NoHair.KNE.vacuumRic01 R K1 K2 K3 W hrel hW, NoHair.KNE.vacuumRic02 R K1 K2 K3 W hrel hW, NoHair.KNE.vacuumRic03 R K1 K2 K3 W hrel hW⟩

end

section
set_option autoImplicit false

open scoped BigOperators
open NoHair NoHair.KNE

theorem NoHair.KNE.thm_ricci_b (R K1 K2 K3 W : ℝ) (hrel : K1 ^ 2 + K2 ^ 2 + K3 ^ 2 = 1) (hW : W * (R ^ 2 + (2:ℝ) ^ 2 * K3 ^ 2) = 1) :
    RicS (2:ℝ) (5/2:ℝ) (0:ℝ) R K1 K2 K3 W 1 1 = RicA (2:ℝ) (5/2:ℝ) (0:ℝ) R K1 K2 K3 W 1 1 ∧
    RicS (2:ℝ) (5/2:ℝ) (0:ℝ) R K1 K2 K3 W 1 2 = RicA (2:ℝ) (5/2:ℝ) (0:ℝ) R K1 K2 K3 W 1 2 :=
  ⟨NoHair.KNE.vacuumRic11 R K1 K2 K3 W hrel hW, NoHair.KNE.ricS_12 2 (5/2) 0 R K1 K2 K3 W hrel hW⟩

end

section
set_option autoImplicit false

open scoped BigOperators
open NoHair NoHair.KNE

theorem NoHair.KNE.thm_ricci_c (R K1 K2 K3 W : ℝ) (hrel : K1 ^ 2 + K2 ^ 2 + K3 ^ 2 = 1) (hW : W * (R ^ 2 + (2:ℝ) ^ 2 * K3 ^ 2) = 1) :
    RicS (2:ℝ) (5/2:ℝ) (0:ℝ) R K1 K2 K3 W 1 3 = RicA (2:ℝ) (5/2:ℝ) (0:ℝ) R K1 K2 K3 W 1 3 ∧
    RicS (2:ℝ) (5/2:ℝ) (0:ℝ) R K1 K2 K3 W 2 2 = RicA (2:ℝ) (5/2:ℝ) (0:ℝ) R K1 K2 K3 W 2 2 ∧
    RicS (2:ℝ) (5/2:ℝ) (0:ℝ) R K1 K2 K3 W 2 3 = RicA (2:ℝ) (5/2:ℝ) (0:ℝ) R K1 K2 K3 W 2 3 ∧
    RicS (2:ℝ) (5/2:ℝ) (0:ℝ) R K1 K2 K3 W 3 3 = RicA (2:ℝ) (5/2:ℝ) (0:ℝ) R K1 K2 K3 W 3 3 :=
  ⟨NoHair.KNE.ricS_13 2 (5/2) 0 R K1 K2 K3 W hrel hW, NoHair.KNE.ricS_22 2 (5/2) 0 R K1 K2 K3 W hrel hW, NoHair.KNE.ricS_23 2 (5/2) 0 R K1 K2 K3 W hrel hW, NoHair.KNE.ricS_33 2 (5/2) 0 R K1 K2 K3 W hrel hW⟩

end

section
/-!
# Kerr–Newman satisfies the Einstein equation

Assembly of the Einstein equation from the closed-form facts proved in the platform theorems
`NoHair.KNE.thm_christoffel`, `thm_div_one/two/three`, `thm_ricci_a/b/c` and `thm_maxwell`
(statements over the definition block `NoHair_KerrNewmanEinstein_Base`). Here: the trace of the
Christoffel symbols vanishes, so its derivative does; the Ricci tensor and the scalar curvature at (2:ℝ)
point with `r > 0`; and `maxwellSource` in closed form.
-/

set_option autoImplicit false
set_option linter.all false

open scoped BigOperators
open NoHair

namespace NoHair.KNE

theorem trGam_0 (R K1 K2 K3 W : ℝ) (hrel : K1 ^ 2 + K2 ^ 2 + K3 ^ 2 = 1) (hW : W * (R ^ 2 + (2:ℝ) ^ 2 * K3 ^ 2) = 1) :
    ∑ ρ, Gam (2:ℝ) (5/2:ℝ) (0:ℝ) R K1 K2 K3 W ρ ρ 0 = 0 := by
  simp only [Gam, G000, G101, G202, G303, Matrix.cons_val, Fin.sum_univ_four]
  simp only [zero_pow (by decide : 2 ≠ 0), zero_pow (by decide : 4 ≠ 0), zero_mul, mul_zero, add_zero, zero_add, sub_zero, neg_zero]
  grobner
theorem trGam_1 (R K1 K2 K3 W : ℝ) (hrel : K1 ^ 2 + K2 ^ 2 + K3 ^ 2 = 1) (hW : W * (R ^ 2 + (2:ℝ) ^ 2 * K3 ^ 2) = 1) :
    ∑ ρ, Gam (2:ℝ) (5/2:ℝ) (0:ℝ) R K1 K2 K3 W ρ ρ 1 = 0 := by
  simp only [Gam, G001, G111, G212, G313, Matrix.cons_val, Fin.sum_univ_four]
  simp only [zero_pow (by decide : 2 ≠ 0), zero_pow (by decide : 4 ≠ 0), zero_mul, mul_zero, add_zero, zero_add, sub_zero, neg_zero]
  grobner
theorem trGam_2 (R K1 K2 K3 W : ℝ) (hrel : K1 ^ 2 + K2 ^ 2 + K3 ^ 2 = 1) (hW : W * (R ^ 2 + (2:ℝ) ^ 2 * K3 ^ 2) = 1) :
    ∑ ρ, Gam (2:ℝ) (5/2:ℝ) (0:ℝ) R K1 K2 K3 W ρ ρ 2 = 0 := by
  simp only [Gam, G002, G112, G222, G323, Matrix.cons_val, Fin.sum_univ_four]
  simp only [zero_pow (by decide : 2 ≠ 0), zero_pow (by decide : 4 ≠ 0), zero_mul, mul_zero, add_zero, zero_add, sub_zero, neg_zero]
  grobner
theorem trGam_3 (R K1 K2 K3 W : ℝ) (hrel : K1 ^ 2 + K2 ^ 2 + K3 ^ 2 = 1) (hW : W * (R ^ 2 + (2:ℝ) ^ 2 * K3 ^ 2) = 1) :
    ∑ ρ, Gam (2:ℝ) (5/2:ℝ) (0:ℝ) R K1 K2 K3 W ρ ρ 3 = 0 := by
  simp only [Gam, G003, G113, G223, G333, Matrix.cons_val, Fin.sum_univ_four]
  simp only [zero_pow (by decide : 2 ≠ 0), zero_pow (by decide : 4 ≠ 0), zero_mul, mul_zero, add_zero, zero_add, sub_zero, neg_zero]
  grobner
theorem trGam (R K1 K2 K3 W : ℝ) (hrel : K1 ^ 2 + K2 ^ 2 + K3 ^ 2 = 1) (hW : W * (R ^ 2 + (2:ℝ) ^ 2 * K3 ^ 2) = 1) (σ : Fin 4) :
    ∑ ρ, Gam (2:ℝ) (5/2:ℝ) (0:ℝ) R K1 K2 K3 W ρ ρ σ = 0 := by
  fin_cases σ
  · exact trGam_0 R K1 K2 K3 W hrel hW
  · exact trGam_1 R K1 K2 K3 W hrel hW
  · exact trGam_2 R K1 K2 K3 W hrel hW
  · exact trGam_3 R K1 K2 K3 W hrel hW

theorem ricS (R K1 K2 K3 W : ℝ) (hrel : K1 ^ 2 + K2 ^ 2 + K3 ^ 2 = 1) (hW : W * (R ^ 2 + (2:ℝ) ^ 2 * K3 ^ 2) = 1) (μ ν : Fin 4) :
    RicS (2:ℝ) (5/2:ℝ) (0:ℝ) R K1 K2 K3 W μ ν = RicA (2:ℝ) (5/2:ℝ) (0:ℝ) R K1 K2 K3 W μ ν := by
  fin_cases μ <;> fin_cases ν
  · exact (thm_ricci_a R K1 K2 K3 W hrel hW).1
  · exact (thm_ricci_a R K1 K2 K3 W hrel hW).2.1
  · exact (thm_ricci_a R K1 K2 K3 W hrel hW).2.2.1
  · exact (thm_ricci_a R K1 K2 K3 W hrel hW).2.2.2
  · rw [RicS_symm, RicA_symm]; exact (thm_ricci_a R K1 K2 K3 W hrel hW).2.1
  · exact (thm_ricci_b R K1 K2 K3 W hrel hW).1
  · exact (thm_ricci_b R K1 K2 K3 W hrel hW).2
  · exact (thm_ricci_c R K1 K2 K3 W hrel hW).1
  · rw [RicS_symm, RicA_symm]; exact (thm_ricci_a R K1 K2 K3 W hrel hW).2.2.1
  · rw [RicS_symm, RicA_symm]; exact (thm_ricci_b R K1 K2 K3 W hrel hW).2
  · exact (thm_ricci_c R K1 K2 K3 W hrel hW).2.1
  · exact (thm_ricci_c R K1 K2 K3 W hrel hW).2.2.1
  · rw [RicS_symm, RicA_symm]; exact (thm_ricci_a R K1 K2 K3 W hrel hW).2.2.2
  · rw [RicS_symm, RicA_symm]; exact (thm_ricci_c R K1 K2 K3 W hrel hW).1
  · rw [RicS_symm, RicA_symm]; exact (thm_ricci_c R K1 K2 K3 W hrel hW).2.2.1
  · exact (thm_ricci_c R K1 K2 K3 W hrel hW).2.2.2

theorem cp_div (y : E4) (hy : 0 < ksRadius (2:ℝ) y) (ρ ν σ : Fin 4) :
    coordPartial (fun w => Gam (2:ℝ) (5/2:ℝ) (0:ℝ) (ksRadius (2:ℝ) w) (ksNull (2:ℝ) w 1) (ksNull (2:ℝ) w 2) (ksNull (2:ℝ) w 3) (Wf (2:ℝ) w) ρ ν σ) ρ y = dDivT (2:ℝ) (5/2:ℝ) (0:ℝ) (ksRadius (2:ℝ) y) (ksNull (2:ℝ) y 1) (ksNull (2:ℝ) y 2) (ksNull (2:ℝ) y 3) (Wf (2:ℝ) y) ρ ν σ := by
  fin_cases ρ
  · fin_cases ν <;> fin_cases σ <;> simp only [dDivT, Matrix.cons_val, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk] <;>
      exact cp_time (2:ℝ) (fun R K1 K2 K3 => Gam (2:ℝ) (5/2:ℝ) (0:ℝ) R K1 K2 K3 (1 / (R ^ 2 + (2:ℝ) ^ 2 * K3 ^ 2)) 0 _ _) y
  · exact (thm_div_one y hy).2.2 ν σ
  · exact (thm_div_two y hy).2 ν σ
  · exact (thm_div_three y hy).2 ν σ

theorem diff_tr (y : E4) (hy : 0 < ksRadius (2:ℝ) y) (ρ σ : Fin 4) :
    DifferentiableAt ℝ (fun w => Gam (2:ℝ) (5/2:ℝ) (0:ℝ) (ksRadius (2:ℝ) w) (ksNull (2:ℝ) w 1) (ksNull (2:ℝ) w 2) (ksNull (2:ℝ) w 3) (Wf (2:ℝ) w) ρ ρ σ) y := by
  fin_cases ρ
  · exact (thm_div_one y hy).1 σ
  · exact (thm_div_one y hy).2.1 σ
  · exact (thm_div_two y hy).1 σ
  · exact (thm_div_three y hy).1 σ

/-! ## Curvature at the point `y` -/

theorem isOpen_U : IsOpen {z : E4 | 0 < ksRadius (2:ℝ) z} :=
  isOpen_lt continuous_const (continuous_ksRadius (2:ℝ))

theorem cp_chr (y : E4) (hy : 0 < ksRadius (2:ℝ) y) (i j k c : Fin 4) :
    coordPartial (fun z => christoffel (kerrNewmanMetric (5/2:ℝ) (2:ℝ) (0:ℝ)) z i j k) c y
      = coordPartial (fun w => Gam (2:ℝ) (5/2:ℝ) (0:ℝ) (ksRadius (2:ℝ) w) (ksNull (2:ℝ) w 1) (ksNull (2:ℝ) w 2)
          (ksNull (2:ℝ) w 3) (Wf (2:ℝ) w) i j k) c y := by
  unfold coordPartial
  rw [Filter.EventuallyEq.fderiv_eq]
  filter_upwards [(isOpen_U).mem_nhds hy] with z hz
  exact thm_christoffel z hz i j k

theorem trace_cp_zero (y : E4) (hy : 0 < ksRadius (2:ℝ) y) (σ ν : Fin 4) :
    ∑ ρ, coordPartial (fun z => christoffel (kerrNewmanMetric (5/2:ℝ) (2:ℝ) (0:ℝ)) z ρ ρ σ) ν y = 0 := by
  simp only [cp_chr y hy]
  have hsum : (fun w => ∑ ρ, Gam (2:ℝ) (5/2:ℝ) (0:ℝ) (ksRadius (2:ℝ) w) (ksNull (2:ℝ) w 1) (ksNull (2:ℝ) w 2)
      (ksNull (2:ℝ) w 3) (Wf (2:ℝ) w) ρ ρ σ) =ᶠ[nhds y] fun _ => (0 : ℝ) := by
    filter_upwards [(isOpen_U).mem_nhds hy] with z hz
    exact trGam _ _ _ _ _ (ks_rel (2:ℝ) z hz) (ks_W (2:ℝ) z hz) σ
  have h1 := fderiv_fun_sum (𝕜 := ℝ) (u := Finset.univ) (x := y)
    (A := fun ρ w => Gam (2:ℝ) (5/2:ℝ) (0:ℝ) (ksRadius (2:ℝ) w) (ksNull (2:ℝ) w 1) (ksNull (2:ℝ) w 2) (ksNull (2:ℝ) w 3)
      (Wf (2:ℝ) w) ρ ρ σ)
    (fun ρ _ => diff_tr y hy ρ σ)
  unfold coordPartial
  rw [← ContinuousLinearMap.sum_apply, ← h1, hsum.fderiv_eq]
  simp

theorem ricci_eq (y : E4) (hy : 0 < ksRadius (2:ℝ) y) (σ ν : Fin 4) :
    ricci (kerrNewmanMetric (5/2:ℝ) (2:ℝ) (0:ℝ)) y σ ν
      = RicA (2:ℝ) (5/2:ℝ) (0:ℝ) (ksRadius (2:ℝ) y) (ksNull (2:ℝ) y 1) (ksNull (2:ℝ) y 2) (ksNull (2:ℝ) y 3) (Wf (2:ℝ) y) σ ν := by
  have hrel := ks_rel (2:ℝ) y hy
  have hW := ks_W (2:ℝ) y hy
  unfold ricci riemann
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, trace_cp_zero y hy σ ν]
  simp only [cp_chr y hy, cp_div y hy, thm_christoffel y hy, Finset.sum_sub_distrib]
  have htr : ∑ ρ, ∑ l, Gam (2:ℝ) (5/2:ℝ) (0:ℝ) (ksRadius (2:ℝ) y) (ksNull (2:ℝ) y 1) (ksNull (2:ℝ) y 2) (ksNull (2:ℝ) y 3) (Wf (2:ℝ) y) ρ ρ l
      * Gam (2:ℝ) (5/2:ℝ) (0:ℝ) (ksRadius (2:ℝ) y) (ksNull (2:ℝ) y 1) (ksNull (2:ℝ) y 2) (ksNull (2:ℝ) y 3) (Wf (2:ℝ) y) l ν σ = 0 := by
    rw [Finset.sum_comm]
    simp only [← Finset.sum_mul, trGam _ _ _ _ _ hrel hW, zero_mul, Finset.sum_const_zero]
  rw [htr, ← ricS _ _ _ _ _ hrel hW σ ν]
  unfold RicS
  ring

end NoHair.KNE

open NoHair NoHair.KNE in
theorem hcrCoordinateEinstein (y : E4) (hy : 0 < ksRadius (2:ℝ) y) :
    ∀ μ ν, einsteinTensor (kerrNewmanMetric (5/2:ℝ) (2:ℝ) 0) y μ ν =
      maxwellSource (kerrNewmanMetric (5/2:ℝ) (2:ℝ) 0) (kerrNewmanField (2:ℝ) 0) y μ ν := by
  intro μ ν
  have hr (i j : Fin 4) : ricci (kerrNewmanMetric (5/2:ℝ) (2:ℝ) 0) y i j = 0 := by
    rw [NoHair.KNE.ricci_eq y hy]
    fin_cases i <;> fin_cases j <;>
      simp [RicA, Ric00, Ric01, Ric02, Ric03, Ric11, Ric12, Ric13, Ric22, Ric23, Ric33]
  have hf (z : E4) : kerrNewmanField (2:ℝ) 0 z = 0 := by
    ext i j
    simp [kerrNewmanField, kerrNewmanPotential, coordPartial]
  simp [einsteinTensor, scalarCurvature, maxwellSource, hf, hr]

end

namespace InnerChartEquations
open NoHair Set
open scoped ContDiff Manifold BigOperators Topology

private theorem partial_eq_on_open {s : Set E4} (hs : IsOpen s) {f g : E4 → ℝ}
    (h : EqOn f g s) (k : Fin 4) {z : E4} (hz : z ∈ s) :
    coordPartial f k z = coordPartial g k z :=
  congrArg (fun L : E4 →L[ℝ] ℝ => L (coordBasis k))
    (h.eventuallyEq_of_mem (hs.mem_nhds hz)).fderiv_eq

private theorem einsteinMaxwell_of_eqOn {s : Set E4} (hs : IsOpen s)
    {G' G F' F : E4 → Matrix (Fin 4) (Fin 4) ℝ}
    (hG : EqOn G' G s) (hF : EqOn F' F s) {y : E4} (hy : y ∈ s)
    (hem : EinsteinMaxwellAt G F y) : EinsteinMaxwellAt G' F' y := by
  have dG (z : E4) (hz : z ∈ s) (i j k : Fin 4) :
      coordPartial (fun w => G' w i j) k z = coordPartial (fun w => G w i j) k z :=
    partial_eq_on_open hs (fun w hw => congrArg (fun A : Matrix (Fin 4) (Fin 4) ℝ => A i j) (hG hw)) k hz
  have dF (z : E4) (hz : z ∈ s) (i j k : Fin 4) :
      coordPartial (fun w => F' w i j) k z = coordPartial (fun w => F w i j) k z :=
    partial_eq_on_open hs (fun w hw => congrArg (fun A : Matrix (Fin 4) (Fin 4) ℝ => A i j) (hF hw)) k hz
  have chr (z : E4) (hz : z ∈ s) (i j k : Fin 4) :
      christoffel G' z i j k = christoffel G z i j k := by
    simp only [christoffel, invMetric, hG hz, dG z hz]
  have dChr (z : E4) (hz : z ∈ s) (i j k l : Fin 4) :
      coordPartial (fun w => christoffel G' w i j k) l z =
      coordPartial (fun w => christoffel G w i j k) l z :=
    partial_eq_on_open hs (fun w hw => chr w hw i j k) l hz
  have ric (i j : Fin 4) : ricci G' y i j = ricci G y i j := by
    simp only [ricci, riemann, dChr y hy, chr y hy]
  have flux (i j : Fin 4) :
      coordPartial (fun z => Real.sqrt |(G' z).det| * raiseBoth G' F' z i j) i y =
      coordPartial (fun z => Real.sqrt |(G z).det| * raiseBoth G F z i j) i y := by
    apply partial_eq_on_open hs _ i hy
    intro z hz
    simp only [raiseBoth, invMetric, hG hz, hF hz]
  refine ⟨?_, ?_, ?_⟩
  · intro i j
    simpa only [einsteinTensor, scalarCurvature, maxwellSource, raiseBoth, invMetric,
      hG hy, hF hy, ric] using hem.1 i j
  · intro j
    simpa only [flux] using hem.2.1 j
  · intro i j k
    simpa only [dF y hy] using hem.2.2 i j k

theorem proved (U : TopologicalSpace.Opens E4) (G F : E4 → Matrix (Fin 4) (Fin 4) ℝ)
    (h : ∀ y ∈ U, EinsteinMaxwellAt G F y) :
    IsElectrovac (M := U) (fun x => matrixBilin (G x.val)) (fun x => matrixBilin (F x.val)) := by
  intro c hc y hy
  obtain ⟨p, hp⟩ := TopologicalSpace.Opens.chart_eq (H := E4) ⟨c.symm y⟩ hc
  have hchart (x : U) : c = chartAt E4 x := hp.trans (by rfl)
  have hval (z : E4) (hz : z ∈ c.target) : (c.symm z).val = z := by
    have eqval (x : U) : c x = x.val := by rw [hchart x] <;> rfl
    exact (eqval (c.symm z)).symm.trans (c.right_inv hz)
  have derivAt (x : U) :
      (mfderiv 𝓘(ℝ, E4) 𝓘(ℝ, E4) c.symm x.val : E4 →L[ℝ] E4) = ContinuousLinearMap.id ℝ E4 := by
    rw [hchart x]
    have hd := mfderivWithin_range_extChartAt_symm (I := 𝓘(ℝ, E4)) (x := x)
    simp only [modelWithCornersSelf_coe, range_id, mfderivWithin_univ] at hd
    exact hd
  have coeff (A : E4 → Matrix (Fin 4) (Fin 4) ℝ) :
      EqOn (pullbackCoeffs (M := U) (fun x => matrixBilin (A x.val)) c.symm) A c.target := by
    intro z hz
    have hd := derivAt (c.symm z)
    rw [hval z hz] at hd
    funext i j
    unfold pullbackCoeffs
    rw [hd]
    change matrixBilin (A (c.symm z).val) (coordBasis i) (coordBasis j) = A z i j
    rw [hval z hz]
    change Matrix.toLinearMap₂' ℝ (A z) (WithLp.ofLp (coordBasis i))
      (WithLp.ofLp (coordBasis j)) = A z i j
    simp only [coordBasis, EuclideanSpace.single, PiLp.ofLp_single]
    rw [Matrix.toLinearMap₂'_apply]
    simp_rw [← Finset.smul_sum]
    simp [Pi.single_apply, ite_smul, Finset.sum_ite_eq, Finset.sum_ite_eq']
  apply einsteinMaxwell_of_eqOn c.open_target (coeff G) (coeff F) hy
  apply h
  rw [← hval y hy]
  exact (c.symm y).property

end InnerChartEquations

namespace InnerRegularity
open NoHair Set
open scoped ContDiff Manifold BigOperators

private theorem matrix_eval (A : Matrix (Fin 4) (Fin 4) ℝ) (v w : E4) :
    matrixBilin A v w = ∑ i, ∑ j, v i * (w j * A i j) := by
  change Matrix.toLinearMap₂' ℝ A (WithLp.ofLp v) (WithLp.ofLp w) = _
  simp only [Matrix.toLinearMap₂'_apply, smul_eq_mul]

private theorem entry (A : Matrix (Fin 4) (Fin 4) ℝ) (i j : Fin 4) :
    matrixBilin A (coordBasis i) (coordBasis j) = A i j := by
  change Matrix.toLinearMap₂' ℝ A (WithLp.ofLp (coordBasis i)) (WithLp.ofLp (coordBasis j)) = _
  simp only [coordBasis, EuclideanSpace.single, PiLp.ofLp_single]
  rw [Matrix.toLinearMap₂'_apply]
  simp_rw [← Finset.smul_sum]
  simp [Pi.single_apply, ite_smul, Finset.sum_ite_eq, Finset.sum_ite_eq']

private noncomputable def shear (K : E4 →ₗ[ℝ] ℝ) (n : E4) (c : ℝ) (hn : K n = 0) : E4 ≃ₗ[ℝ] E4 where
  toLinearMap := LinearMap.id - K.smulRight (c • n)
  invFun w := w + K w • (c • n)
  left_inv w := by
    change w - K w • (c • n) + K (w - K w • (c • n)) • (c • n) = w
    simp [hn]
  right_inv w := by
    change w + K w • (c • n) - K (w + K w • (c • n)) • (c • n) = w
    simp [hn]

private theorem ks_basis (f : ℝ) (k : Fin 4 → ℝ)
    (hnull : -(k 0)^2 + (k 1)^2 + (k 2)^2 + (k 3)^2 = 0) :
    ∃ B : Module.Basis (Fin 4) ℝ E4, ∀ i j,
      matrixBilin (fun p q => minkowski p q + f * k p * k q) (B i) (B j) = minkowski i j := by
  let K : E4 →ₗ[ℝ] ℝ := k 0 • EuclideanSpace.projₗ 0 + k 1 • EuclideanSpace.projₗ 1 +
    k 2 • EuclideanSpace.projₗ 2 + k 3 • EuclideanSpace.projₗ 3
  let n : E4 := WithLp.toLp 2 ![-k 0, k 1, k 2, k 3]
  have kv (v : E4) : K v = k 0 * v 0 + k 1 * v 1 + k 2 * v 2 + k 3 * v 3 := rfl
  have hn : K n = 0 := by
    rw [kv]
    change k 0 * (-k 0) + k 1 * k 1 + k 2 * k 2 + k 3 * k 3 = 0
    nlinarith only [hnull]
  have hleft (w : E4) : matrixBilin minkowski n w = K w := by
    rw [matrix_eval, kv]
    simp [Fin.sum_univ_four, minkowski, n] <;> ring
  have hright (v : E4) : matrixBilin minkowski v n = K v := by
    rw [matrix_eval, kv]
    simp [Fin.sum_univ_four, minkowski, n] <;> ring
  have metric (v w : E4) : matrixBilin (fun p q => minkowski p q + f * k p * k q) v w =
      matrixBilin minkowski v w + f * K v * K w := by
    rw [matrix_eval (fun p q => minkowski p q + f * k p * k q) v w, matrix_eval minkowski v w]
    simp only [kv, Fin.sum_univ_four]
    ring
  let P := shear K n (f / 2) hn
  have iso (v w : E4) : matrixBilin (fun p q => minkowski p q + f * k p * k q) (P v) (P w) =
      matrixBilin minkowski v w := by
    rw [metric]
    change matrixBilin minkowski (v - K v • ((f / 2) • n)) (w - K w • ((f / 2) • n)) +
      f * K (v - K v • ((f / 2) • n)) * K (w - K w • ((f / 2) • n)) = matrixBilin minkowski v w
    simp [map_sub, map_smul, ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
      hleft, hright, hn, smul_eq_mul] <;> ring
  let B := (EuclideanSpace.basisFun (Fin 4) ℝ).toBasis
  refine ⟨B.map P, ?_⟩
  intro i j
  change matrixBilin _ (P (B i)) (P (B j)) = _
  rw [iso]
  have hb (l : Fin 4) : B l = coordBasis l := EuclideanSpace.basisFun_apply (Fin 4) ℝ l
  rw [hb, hb]
  exact entry minkowski i j

private theorem radius_analytic (a : ℝ) (z : E4) (hz : 0 < ksRadius a z) :
    ContDiffAt ℝ ω (ksRadius a) z := by
  have hD := (ks_D_pos a z hz).ne'
  have hQ := (ks_Q_pos a z hz).ne'
  rw [ksRadius_eq']
  fun_prop (disch := assumption)

private theorem null_analytic (a : ℝ) (z : E4) (hz : 0 < ksRadius a z) (i : Fin 4) :
    ContDiffAt ℝ ω (fun w => ksNull a w i) z := by
  have hr := radius_analytic a z hz
  have hne : ksRadius a z ^ 2 + a ^ 2 ≠ 0 := by positivity
  have hne' := hz.ne'
  fin_cases i
  · simp only [Fin.zero_eta, ksNull_zero]; fun_prop
  · simp only [Fin.mk_one, ksNull_one]; fun_prop (disch := assumption)
  · change ContDiffAt ℝ ω (fun w => ksNull a w 2) z
    simp only [ksNull_two]; fun_prop (disch := assumption)
  · change ContDiffAt ℝ ω (fun w => ksNull a w 3) z
    simp only [ksNull_three]; fun_prop (disch := assumption)

private theorem radius_smooth (a : ℝ) (z : E4) (hz : 0 < ksRadius a z) :
    ContDiffAt ℝ ∞ (ksRadius a) z :=
  (radius_analytic a z hz).of_le (by simp)

private theorem null_smooth (a : ℝ) (z : E4) (hz : 0 < ksRadius a z) (i : Fin 4) :
    ContDiffAt ℝ ∞ (fun w => ksNull a w i) z :=
  (null_analytic a z hz i).of_le (by simp)

theorem lorentz (m a e : ℝ) : IsLorentzian (kerrNewmanMetricField m a e) := by
  intro x
  exact ks_basis (ksProfile m a e x.val) (ksNull a x.val) (ks_null a x.val x.property)

end InnerRegularity

namespace InnerFrontier
open NoHair Set Metric
open scoped Topology

private abbrev Space3 := EuclideanSpace ℝ (Fin 3)

private noncomputable def ellipsoidChart (d b : ℝ) (hd : d ≠ 0) (hb : b ≠ 0) : E4 ≃ₜ ℝ × Space3 where
  toFun x := (x 0, WithLp.toLp 2 ![x 1 / d, x 2 / d, x 3 / b])
  invFun q := WithLp.toLp 2 ![q.1, q.2 0 * d, q.2 1 * d, q.2 2 * b]
  left_inv x := by
    ext i
    fin_cases i <;> simp [PiLp.toLp_apply, hd, hb]
  right_inv q := by
    apply Prod.ext
    · rfl
    · ext i
      fin_cases i <;> simp [PiLp.toLp_apply, hd, hb]
  continuous_toFun := by
    apply Continuous.prodMk
    · fun_prop
    · apply (PiLp.continuous_toLp 2 _).comp
      apply continuous_pi
      intro i
      fin_cases i <;> simp <;> fun_prop
  continuous_invFun := by
    apply (PiLp.continuous_toLp 2 _).comp
    apply continuous_pi
    intro i
    fin_cases i <;> simp <;> fun_prop

private theorem ellipsoid_compare (a b : ℝ) (hb : 0 < b) (x : E4)
    (d : ℝ) (hd : 0 < d) (hd2 : d ^ 2 = b ^ 2 + a ^ 2) :
    let w := (ellipsoidChart d b hd.ne' hb.ne' x).2
    (b < ksRadius a x ↔ 1 < ‖w‖) ∧ (ksRadius a x = b ↔ ‖w‖ = 1) := by
  let w := (ellipsoidChart d b hd.ne' hb.ne' x).2
  let c := x 1 ^ 2 + x 2 ^ 2 + x 3 ^ 2 - a ^ 2
  let s := Real.sqrt (c ^ 2 + 4 * a ^ 2 * x 3 ^ 2)
  have hs2 : s ^ 2 = c ^ 2 + 4 * a ^ 2 * x 3 ^ 2 := Real.sq_sqrt (by positivity)
  have habs : |c| ≤ s := calc
    |c| = Real.sqrt (c ^ 2) := (Real.sqrt_sq_eq_abs c).symm
    _ ≤ s := Real.sqrt_le_sqrt (by nlinarith only [sq_nonneg (a * x 3)])
  have hp : 0 ≤ (c + s) / 2 := by linarith [neg_abs_le c]
  have hr2 : ksRadius a x ^ 2 = (c + s) / 2 := Real.sq_sqrt hp
  have hneg : (c - s) / 2 ≤ 0 := by linarith [le_abs_self c]
  have hr : 0 ≤ ksRadius a x := Real.sqrt_nonneg _
  have hn : ‖w‖ ^ 2 = (x 1 / d) ^ 2 + (x 2 / d) ^ 2 + (x 3 / b) ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three]
    rfl
  have hid : (‖w‖ ^ 2 - 1) * (b ^ 2 * d ^ 2) =
      (ksRadius a x ^ 2 - b ^ 2) * (b ^ 2 - (c - s) / 2) := calc
    _ = (x 1 ^ 2 + x 2 ^ 2) * b ^ 2 + x 3 ^ 2 * d ^ 2 - b ^ 2 * d ^ 2 := by
      rw [hn]
      field_simp [hd.ne', hb.ne'] <;> ring
    _ = _ := by
      rw [hr2, hd2]
      dsimp only [c] at hs2 ⊢
      nlinarith only [hs2]
  have hsign : (‖w‖ - 1) * ((‖w‖ + 1) * (b ^ 2 * d ^ 2)) =
      (ksRadius a x - b) * ((ksRadius a x + b) * (b ^ 2 - (c - s) / 2)) := by
    linear_combination hid
  have hleft : 0 < (‖w‖ + 1) * (b ^ 2 * d ^ 2) := by positivity
  have hgap : 0 < b ^ 2 - (c - s) / 2 := sub_pos.mpr (hneg.trans_lt (sq_pos_of_pos hb))
  have hright : 0 < (ksRadius a x + b) * (b ^ 2 - (c - s) / 2) :=
    mul_pos (add_pos_of_nonneg_of_pos hr hb) hgap
  change (b < ksRadius a x ↔ 1 < ‖w‖) ∧ (ksRadius a x = b ↔ ‖w‖ = 1)
  constructor
  · have h := congrArg (fun v : ℝ => 0 < v) hsign
    simpa only [mul_pos_iff_of_pos_right hleft, mul_pos_iff_of_pos_right hright, sub_pos] using
      (Iff.of_eq h).symm
  · have h := congrArg (fun v : ℝ => v = 0) hsign
    simpa only [mul_eq_zero, hleft.ne', hright.ne', or_false, sub_eq_zero] using (Iff.of_eq h).symm

theorem proved (a b : ℝ) (hb : 0 < b) :
    frontier {x : kerrNewmanSpacetime a | b < ksRadius a x.val} =
        {x : kerrNewmanSpacetime a | ksRadius a x.val = b} ∧
      IsConnected {x : kerrNewmanSpacetime a | ksRadius a x.val = b} := by
  let d := Real.sqrt (b ^ 2 + a ^ 2)
  have hd : 0 < d := Real.sqrt_pos.mpr (by positivity)
  have hd2 : d ^ 2 = b ^ 2 + a ^ 2 := Real.sq_sqrt (by positivity)
  let H := ellipsoidChart d b hd.ne' hb.ne'
  let P : E4 → Space3 := fun x => (H x).2
  let V : Set E4 := {y | b < ksRadius a y}
  let L : Set E4 := {y | ksRadius a y = b}
  have hout : V = P ⁻¹' (closedBall (0 : Space3) 1)ᶜ := by
    ext y
    simpa [V, P, H, Metric.mem_closedBall, dist_zero_right] using (ellipsoid_compare a b hb y d hd hd2).1
  have hlevel : L = P ⁻¹' sphere (0 : Space3) 1 := by
    ext y
    simpa [L, P, H, Metric.mem_sphere, dist_zero_right] using (ellipsoid_compare a b hb y d hd hd2).2
  have op : IsOpenMap P := isOpenMap_snd.comp H.isOpenMap
  have co : Continuous P := continuous_snd.comp H.continuous
  have hfront : frontier V = L := by
    rw [hout, ← op.preimage_frontier_eq_frontier_preimage co, frontier_compl,
      frontier_closedBall (0 : Space3) one_ne_zero, hlevel]
  have hsph : IsConnected (sphere (0 : Space3) 1) := by
    apply isConnected_sphere _ _ zero_le_one
    apply Module.one_lt_rank_of_one_lt_finrank
    rw [finrank_euclideanSpace_fin]
    decide
  have hconn : IsConnected L := by
    have hp : IsConnected ((univ : Set ℝ) ×ˢ sphere (0 : Space3) 1) := isConnected_univ.prod hsph
    have he : P ⁻¹' sphere (0 : Space3) 1 = H ⁻¹' ((univ : Set ℝ) ×ˢ sphere (0 : Space3) 1) := by
      ext x
      simp [P]
    rw [hlevel, he]
    exact H.isConnected_preimage.mpr hp
  let U := kerrNewmanSpacetime a
  have hop : IsOpenMap (Subtype.val : U → E4) := U.isOpen.isOpenMap_subtype_val
  change frontier ((Subtype.val : U → E4) ⁻¹' V) = Subtype.val ⁻¹' L ∧ IsConnected ((Subtype.val : U → E4) ⁻¹' L)
  constructor
  · rw [← hop.preimage_frontier_eq_frontier_preimage continuous_subtype_val, hfront]
  · have him : (Subtype.val : U → E4) '' (Subtype.val ⁻¹' L) = L := by
      apply image_preimage_eq_of_subset
      intro y hy
      exact ⟨⟨y, show 0 < ksRadius a y from (show ksRadius a y = b from hy) ▸ hb⟩, rfl⟩
    have hc : IsConnected ((Subtype.val : U → E4) '' (Subtype.val ⁻¹' L)) := him.symm ▸ hconn
    exact ⟨hc.nonempty.of_image, Topology.IsInducing.subtypeVal.isPreconnected_image.mp hc.isPreconnected⟩

end InnerFrontier

namespace InnerTimeFlow
open NoHair Set
open scoped ContDiff Manifold BigOperators Topology

noncomputable section

private abbrev I4 := 𝓘(ℝ, E4)

private theorem inclusion_deriv (U : TopologicalSpace.Opens E4) (x : U) :
    (mfderiv I4 I4 (Subtype.val : U → E4) x : E4 →L[ℝ] E4) = ContinuousLinearMap.id ℝ E4 :=
  mfderiv_extChartAt_self (I := I4) (x := x)

private theorem inclusion_diff (U : TopologicalSpace.Opens E4) (x : U) :
    MDifferentiableAt I4 I4 (Subtype.val : U → E4) x :=
  (contMDiff_subtype_val (I := I4) (U := U) (n := ∞)).mdifferentiableAt (by simp)

private theorem translate_the_fields (m a e s : ℝ) (y : E4) :
    kerrNewmanMetric m a e (y + s • coordBasis 0) = kerrNewmanMetric m a e y ∧
    kerrNewmanField a e (y + s • coordBasis 0) = kerrNewmanField a e y := by
  have h3 (x : E4) : (x + s • coordBasis 0) 3 = x 3 := NoHair.KNE.time_shift x s 3 (by decide)
  have hA (j : Fin 4) : (fun x : E4 => kerrNewmanPotential a e (x + s • coordBasis 0) j) =
      (fun x : E4 => kerrNewmanPotential a e x j) := by
    funext x
    simp only [kerrNewmanPotential, NoHair.KNE.ksRadius_time, NoHair.KNE.ksNull_time, h3]
  have hd (j : Fin 4) : fderiv ℝ (fun x => kerrNewmanPotential a e x j) (y + s • coordBasis 0) =
      fderiv ℝ (fun x => kerrNewmanPotential a e x j) y := by
    rw [← fderiv_comp_add_right (f := fun x => kerrNewmanPotential a e x j), hA]
  constructor
  · funext i j
    simp only [kerrNewmanMetric, ksProfile, NoHair.KNE.ksRadius_time, NoHair.KNE.ksNull_time, h3]
  · funext i j
    simp only [kerrNewmanField, coordPartial, hd]

theorem stationary_translation (m a e : ℝ) :
    ∃ φ : ℝ → kerrNewmanSpacetime a → kerrNewmanSpacetime a,
      (∀ s x, (φ s x).val = x.val + s • coordBasis 0) ∧
      IsSymmetryFlow (kerrNewmanMetricField m a e) (kerrNewmanFieldField a e) φ := by
  let U := kerrNewmanSpacetime a
  let φ (s : ℝ) (x : U) : U := ⟨x.val + s • coordBasis 0, by
    change 0 < ksRadius a (x.val + s • coordBasis 0)
    rw [NoHair.KNE.ksRadius_time]
    exact x.property⟩
  have hV : ContMDiff I4 I4 ∞ (Subtype.val : U → E4) := contMDiff_subtype_val
  have hφ (t : ℝ) : ContMDiff I4 I4 ∞ (φ t) := by
    apply (ContMDiff.subtypeVal_comp_iff U (φ t)).mp
    exact hV.add contMDiff_const
  have hD (s : ℝ) (x : U) : (mfderiv I4 I4 (φ s) x : E4 →L[ℝ] E4) = ContinuousLinearMap.id ℝ E4 := by
    let shift (y : E4) := y + s • coordBasis 0
    have hs : HasFDerivAt shift (ContinuousLinearMap.id ℝ E4) x.val := (hasFDerivAt_id x.val).add_const _
    calc
      _ = (mfderiv I4 I4 (Subtype.val : U → E4) (φ s x)).comp (mfderiv I4 I4 (φ s) x) := by
        rw [inclusion_deriv]
        rfl
      _ = mfderiv I4 I4 ((Subtype.val : U → E4) ∘ φ s) x :=
        (mfderiv_comp x (inclusion_diff U _) ((hφ s).mdifferentiableAt (by simp))).symm
      _ = (mfderiv I4 I4 shift x.val).comp (mfderiv I4 I4 (Subtype.val : U → E4) x) :=
        mfderiv_comp x hs.differentiableAt.mdifferentiableAt (inclusion_diff U x)
      _ = _ := by
        rw [inclusion_deriv, mfderiv_eq_fderiv, hs.fderiv]
        rfl
  refine ⟨φ, fun _ _ => rfl, ?_, ?_, ?_, ?_, ?_⟩
  · intro x
    apply Subtype.ext
    simp [φ]
  · intro s t x
    apply Subtype.ext
    change x.val + (s + t) • coordBasis 0 = x.val + t • coordBasis 0 + s • coordBasis 0
    rw [add_smul]
    abel
  · apply (ContMDiff.subtypeVal_comp_iff U _).mp
    exact (hV.comp contMDiff_snd).add (contMDiff_fst.smul contMDiff_const)
  · intro s x v w
    rw [hD]
    change matrixBilin (kerrNewmanMetric m a e (x.val + s • coordBasis 0)) v w = _
    rw [(translate_the_fields m a e s x.val).1]
    rfl
  · intro s x v w
    rw [hD]
    change matrixBilin (kerrNewmanField a e (x.val + s • coordBasis 0)) v w = _
    rw [(translate_the_fields m a e s x.val).2]
    rfl
end
end InnerTimeFlow

namespace InnerChronology
open NoHair NoHair.KNE Set Filter
open scoped Topology
open scoped BigOperators Manifold ContDiff

noncomputable section

private abbrev U (a : ℝ) := kerrNewmanSpacetime a
private abbrev G (m a e : ℝ) := kerrNewmanMetricField m a e
private abbrev T (m a e : ℝ) := kerrNewmanTimeDirection m a e
private abbrev I4 := 𝓘(ℝ,E4)
private abbrev V3 := Fin 3 → ℝ
private def dot3 (v w : V3) := ∑ i, v i*w i
private def space (v : E4) : V3 := ![v 1,v 2,v 3]
private def axis (a : ℝ) (y : E4) : V3 := ![ksNull a y 1,ksNull a y 2,ksNull a y 3]
private def timeC (v : E4) := v 0

private theorem dot_symm (u v : V3) : dot3 u v = dot3 v u := by simp [dot3, mul_comm]
private theorem dot_add_l (u v w : V3) : dot3 (u+v) w = dot3 u w + dot3 v w := by
  simp [dot3, add_mul, Finset.sum_add_distrib]
private theorem dot_add_r (u v w : V3) : dot3 u (v+w) = dot3 u v + dot3 u w := by
  simp [dot3, mul_add, Finset.sum_add_distrib]
private theorem dot_scale_l (c : ℝ) (u v : V3) : dot3 (c • u) v = c*dot3 u v := by
  simp [dot3, Finset.mul_sum, mul_assoc]
private theorem dot_scale_r (c : ℝ) (u v : V3) : dot3 u (c • v) = c*dot3 u v := by
  simp [dot3, Finset.mul_sum, mul_left_comm, mul_comm, mul_assoc]
private theorem dot_cauchy (u v : V3) : (dot3 u v)^2 ≤ dot3 u u * dot3 v v := by
  simpa only [dot3, sq] using Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin 3)) u v
private theorem axis_unit (a : ℝ) (x : U a) : dot3 (axis a x.val) (axis a x.val) = 1 := by
  simpa [dot3, axis, Fin.sum_univ_three, sq] using ks_rel a x.val x.property

private theorem metric_formula (m a e : ℝ) (x : U a) (v w : E4) :
    G m a e x v w = -(timeC v*timeC w) + dot3 (space v) (space w) +
      ksProfile m a e x.val * (timeC v + dot3 (axis a x.val) (space v)) *
        (timeC w + dot3 (axis a x.val) (space w)) := by
  change Matrix.toLinearMap₂' ℝ (kerrNewmanMetric m a e x.val) (WithLp.ofLp v) (WithLp.ofLp w) = _
  simp only [Matrix.toLinearMap₂'_apply, smul_eq_mul, kerrNewmanMetric, Fin.sum_univ_four, ksNull_zero]
  simp [minkowski, dot3, space, timeC, axis, Fin.sum_univ_three] <;> ring

private theorem t_coords (m a e : ℝ) (x : U a) :
    timeC (T m a e x) = 1 + ksProfile m a e x.val / 2 ∧
    space (T m a e x) = -(ksProfile m a e x.val / 2) • axis a x.val := by
  refine ⟨rfl, ?_⟩
  ext i
  fin_cases i <;> rfl

private theorem metric_T (m a e : ℝ) (x : U a) (v : E4) :
    G m a e x v (T m a e x) = -timeC v + (ksProfile m a e x.val/2) *
      (timeC v + dot3 (axis a x.val) (space v)) := by
  obtain ⟨ht, hs⟩ := t_coords m a e x
  erw [metric_formula m a e x v (T m a e x), ht, hs, dot_scale_r, dot_scale_r, axis_unit, dot_symm (space v)]
  ring

theorem time_orientation (m a e : ℝ) : IsTimeOrientation (G m a e) (T m a e) := by
  constructor
  · have hc : Continuous (fun x : U a => (T m a e x : E4)) := by
      apply continuous_iff_continuousAt.mpr
      intro x
      have hr : Continuous (fun y : U a => ksRadius a y.val) := (continuous_ksRadius a).comp continuous_subtype_val
      have hk (i : Fin 4) : ContinuousAt (fun y : U a => ksNull a y.val i) x :=
        (ksNull_differentiableAt a x.val x.property i).continuousAt.comp continuous_subtype_val.continuousAt
      have hd := (ks_den_pos a x.val x.property).ne'
      have hf : ContinuousAt (fun y : U a => ksProfile m a e y.val) x := by
        unfold ksProfile
        fun_prop (disch := assumption)
      unfold T kerrNewmanTimeDirection
      apply (PiLp.continuous_toLp 2 _).continuousAt.comp
      apply continuousAt_pi.mpr
      intro i
      fin_cases i <;> simp only [Matrix.cons_val] <;> fun_prop
    apply continuous_iff_continuousAt.mpr
    intro x
    rw [FiberBundle.continuousAt_section]
    have htr (y : U a) : (trivializationAt E4 (TangentSpace I4) x ⟨y,T m a e y⟩).2 = (T m a e y : E4) := by
      change tangentCoordChange I4 y y y (T m a e y) = _
      exact tangentCoordChange_self (mem_extChartAt_source y)
    simpa only [htr] using hc.continuousAt (x := x)
  · intro x
    obtain ⟨ht,hs⟩ := t_coords m a e x
    erw [metric_T m a e x (T m a e x), ht, hs, dot_scale_r, axis_unit]
    nlinarith

private def radialNormal (a : ℝ) (y : E4) : V3 :=
  let r := ksRadius a y
  let k := axis a y
  let W := Wf a y
  ![r^2*k 0*W-r*k 1*W*a, r^2*k 1*W+r*k 0*W*a, (r^2+a^2)*k 2*W]

private theorem normal_geometry (a : ℝ) (x : U a) :
    dot3 (radialNormal a x.val) (axis a x.val) = 1 ∧
    dot3 (radialNormal a x.val) (radialNormal a x.val) = (ksRadius a x.val^2 + a^2)*Wf a x.val := by
  let r := ksRadius a x.val
  let k := axis a x.val
  let W := Wf a x.val
  have hrel : k 0^2+k 1^2+k 2^2=1 := ks_rel a x.val x.property
  have hW : W*(r^2+a^2*k 2^2)=1 := ks_W a x.val x.property
  let n : V3 := ![r^2*k 0*W-r*k 1*W*a, r^2*k 1*W+r*k 0*W*a, (r^2+a^2)*k 2*W]
  change dot3 n k = 1 ∧ dot3 n n = (r^2+a^2)*W
  constructor
  · calc
      dot3 n k = W*(r^2*(k 0^2+k 1^2+k 2^2)+a^2*k 2^2) := by simp [dot3, n, Fin.sum_univ_three]; ring
      _ = 1 := by rw [hrel, mul_one, hW]
  · calc
      dot3 n n = (r^2+a^2)*W*(W*(r^2*(k 0^2+k 1^2+k 2^2)+a^2*k 2^2)) := by
        simp [dot3, n, Fin.sum_univ_three]; ring
      _ = (r^2+a^2)*W := by rw [hrel, mul_one, hW, mul_one]

private theorem radial_derivative (a : ℝ) (x : U a) (v : E4) :
    fderiv ℝ (ksRadius a) x.val v = dot3 (radialNormal a x.val) (space v) := by
  have hv : ∑ i, v i • coordBasis i = v := by
    ext j
    fin_cases j <;> simp [Fin.sum_univ_four, coordBasis]
  have cp (i : Fin 4) := (hasCP_R a x.val x.property).eq i
  change ∀ (i : Fin 4), fderiv ℝ (ksRadius a) x.val (coordBasis i) = _ at cp
  calc
    _ = fderiv ℝ (ksRadius a) x.val (∑ i, v i • coordBasis i) := congrArg _ hv.symm
    _ = _ := by
      simp only [Fin.sum_univ_four, map_add, map_smul, smul_eq_mul]
      erw [cp 0, cp 1, cp 2, cp 3]
      simp [dot3, radialNormal, space, axis, dRt, Fin.sum_univ_three] <;> ring

private theorem horizon_profile (m a e b : ℝ)
    (hroot : 2*m*b-e^2=b^2+a^2) (x : U a) (hx : ksRadius a x.val=b) :
    ksProfile m a e x.val = (ksRadius a x.val ^ 2 + a^2) * Wf a x.val ∧ 0 < ksProfile m a e x.val := by
  have hc : 2*m*ksRadius a x.val-e^2 = ksRadius a x.val^2+a^2 := by rw [hx]; exact hroot
  have heq : ksProfile m a e x.val = (ksRadius a x.val^2+a^2)*Wf a x.val := by
    rw [profile_eq m a e x.val x.property]
    unfold fA
    rw [hc]
  have hr : 0 < ksRadius a x.val := x.property
  refine ⟨heq, ?_⟩
  rw [heq]
  unfold Wf
  positivity

private theorem inward (k n s : V3) (f t : ℝ) (hk : dot3 k k = 1)
    (hnk : dot3 n k = 1) (hn : dot3 n n = f) (hf : 0 < f)
    (htime : -t*t + dot3 s s + f*(t+dot3 k s)*(t+dot3 k s) < 0)
    (hfuture : -t+(f/2)*(t+dot3 k s) < 0) : dot3 n s < 0 := by
  let c := f/2
  let l := t+dot3 k s
  let τ := t-c*l
  let u := s+(c*l) • k
  let b := n+(-c) • k
  have hc : 0 < c := by dsimp [c]; linarith
  have hτ : 0 < τ := by dsimp [τ,c,l]; linarith only [hfuture]
  have ff : f=2*c := by dsimp [c]; ring
  have hu : dot3 u u < τ^2 := by
    have h : dot3 u u-τ^2 = -t*t+dot3 s s+f*l*l := by
      simp only [u, τ, l, dot_add_l, dot_add_r, dot_scale_l, dot_scale_r, hk, dot_symm s k]
      rw [ff]
      ring
    change -t*t + dot3 s s + f*l*l < 0 at htime
    linarith only [h,htime]
  have hb : dot3 b b = c^2 := by
    simp only [b, dot_add_l, dot_add_r, dot_scale_l, dot_scale_r, hk, hnk, dot_symm k n, hn]
    rw [ff]
    ring
  have he : dot3 n s = dot3 b u - c*τ := by
    simp only [b, u, τ, l, dot_add_l, dot_add_r, dot_scale_l, dot_scale_r, hnk, hk]
    ring
  have hcs := dot_cauchy b u
  rw [hb] at hcs
  have habs : |dot3 b u| < |c*τ| := sq_lt_sq.mp (by
    rw [mul_pow]
    exact hcs.trans_lt (mul_lt_mul_of_pos_left hu (sq_pos_of_pos hc)))
  rw [abs_of_pos (mul_pos hc hτ)] at habs
  rw [he]
  linarith [le_abs_self (dot3 b u)]

private theorem horizon_velocity (m a e b : ℝ) (hroot : 2*m*b-e^2=b^2+a^2)
    (x : U a) (hx : ksRadius a x.val = b) (v : E4)
    (hv : IsFutureTimelike (G m a e) (T m a e) x v) : fderiv ℝ (ksRadius a) x.val v < 0 := by
  obtain ⟨h1,h2⟩ := hv
  rw [metric_formula] at h1
  rw [metric_T] at h2
  obtain ⟨hnk,hn⟩ := normal_geometry a x
  obtain ⟨hf,hp'⟩ := horizon_profile m a e b hroot x hx
  rw [radial_derivative]
  apply inward (axis a x.val) (radialNormal a x.val) (space v) (ksProfile m a e x.val) (timeC v)
    (axis_unit a x) hnk (hn.trans hf.symm) hp' _ h2
  simpa only [neg_mul] using h1

private theorem trap (m a e b : ℝ) (hroot : 2*m*b-e^2=b^2+a^2) :
    ∀ γ : ℝ → kerrNewmanSpacetime a,
      IsFutureTimelikeCurveIn (G m a e) (T m a e) univ γ →
      ksRadius a (γ 0).val ≤ b → ksRadius a (γ 1).val ≤ b := by
  intro γ hγ h0
  let z : ℝ → E4 := Subtype.val ∘ γ
  let h (s : ℝ) := ksRadius a (z s)
  let d (s : ℝ) := fderiv ℝ (ksRadius a) (z s) (velocity γ s)
  have hval : ContMDiff I4 I4 1 (Subtype.val : U a → E4) := contMDiff_subtype_val
  have hz : ContDiff ℝ 1 z := (hval.comp hγ.1).contDiff
  have deriv (s : ℝ) : HasDerivAt h (d s) s := by
    have hcomp := mfderiv_comp s (hval.mdifferentiableAt (by simp) (x := γ s)) (hγ.1.mdifferentiableAt (by simp))
    have hinc : (mfderiv I4 I4 (Subtype.val : U a → E4) (γ s) : E4 →L[ℝ] E4) =
        ContinuousLinearMap.id ℝ E4 := mfderiv_extChartAt_self (I := I4) (x := γ s)
    rw [hinc] at hcomp
    have hh : fderiv ℝ z s = (mfderiv 𝓘(ℝ,ℝ) I4 γ s : ℝ →L[ℝ] E4) := by
      rw [← mfderiv_eq_fderiv]
      exact hcomp
    have hv := ((hz.differentiable (by simp) s).hasFDerivAt).hasDerivAt
    rw [hh] at hv
    exact (ksRadius_differentiableAt a (z s) (γ s).property).hasFDerivAt.comp_hasDerivAt s hv
  have fence := image_le_of_deriv_right_lt_deriv_boundary (f := h) (f' := d)
    (B := fun _ => b) (B' := fun _ => 0) (a := (0:ℝ)) (b := 1)
    ((continuous_ksRadius a).comp hz.continuous).continuousOn (fun s _ => (deriv s).hasDerivWithinAt) h0
    (fun s => hasDerivAt_const s b)
    (fun s hs he => horizon_velocity m a e b hroot (γ s) he (velocity γ s) (hγ.2 s (Ico_subset_Icc_self hs)).2)
  exact fence (right_mem_Icc.mpr zero_le_one)

private theorem ambient_velocity (a : ℝ) (γ : ℝ → U a) (hγ : ContMDiff 𝓘(ℝ,ℝ) I4 1 γ)
    (s : ℝ) (v : E4) (hd : HasDerivAt (fun t => (γ t).val) v s) : (velocity γ s : E4) = v := by
  have hval : ContMDiff I4 I4 1 (Subtype.val : U a → E4) := contMDiff_subtype_val
  have hcomp := mfderiv_comp s (hval.mdifferentiableAt (by simp) (x := γ s)) (hγ.mdifferentiableAt (by simp))
  have hinc : (mfderiv I4 I4 (Subtype.val : U a → E4) (γ s) : E4 →L[ℝ] E4) =
      ContinuousLinearMap.id ℝ E4 := mfderiv_extChartAt_self (I := I4) (x := γ s)
  rw [hinc] at hcomp
  have h : fderiv ℝ (fun t => (γ t).val) s = (mfderiv 𝓘(ℝ,ℝ) I4 γ s : ℝ →L[ℝ] E4) := by
    rw [← mfderiv_eq_fderiv]
    exact hcomp
  exact (congrArg (fun A : ℝ →L[ℝ] E4 => A 1) h).symm.trans hd.deriv

private theorem timelike_scale (m a e : ℝ) (x : U a) (v : E4) (N : ℝ) (hN : 0<N)
    (hv : IsFutureTimelike (G m a e) (T m a e) x v) :
    IsFutureTimelike (G m a e) (T m a e) x (N • v) := by
  let A := matrixBilin (kerrNewmanMetric m a e x.val)
  let w : E4 := T m a e x
  change A v v < 0 ∧ A v w < 0 at hv
  change A (N • v) (N • v)<0 ∧ A (N • v) w<0
  simp only [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]
  exact ⟨mul_neg_of_pos_of_neg hN (mul_neg_of_pos_of_neg hN hv.1),mul_neg_of_pos_of_neg hN hv.2⟩

private theorem nearby_events (p : U 2) (hp : 1 < ksRadius 2 p.val) (b : ℝ) :
    ∃ γ : ℝ → U 2, IsFutureTimelikeCurveIn (G (5/2) 2 0) (T (5/2) 2 0) univ γ ∧
      γ b=p ∧ ∀ t, 1 < ksRadius 2 (γ t).val := by
  let v : E4 := T (5/2) 2 0 p
  let K := fun y : E4 => dot3 (axis 2 y) (space v)
  let P := ksProfile (5/2) 2 0
  let Q := fun y : E4 => -(timeC v*timeC v)+dot3 (space v) (space v)+
    P y*(timeC v+K y)*(timeC v+K y)
  let J := fun y : E4 => -timeC v+(P y/2)*(timeC v+K y)
  have hT := (time_orientation (5/2) 2 0).2 p
  have hQ : Q p.val < 0 := by
    change G (5/2) 2 0 p v v < 0 at hT
    rw [metric_formula] at hT
    exact hT
  have hJ : J p.val < 0 := by
    change G (5/2) 2 0 p v (T (5/2) 2 0 p) < 0 at hT
    rw [metric_T] at hT
    exact hT
  have hk (i : Fin 4) : ContinuousAt (fun y => ksNull 2 y i) p.val :=
    (ksNull_differentiableAt 2 p.val p.property i).continuousAt
  have hK : ContinuousAt K p.val := by
    simp only [K,dot3,axis,Fin.sum_univ_three,Matrix.cons_val]
    fun_prop
  have hP : ContinuousAt P p.val := (hasCP_profile (5/2) 2 0 p.val p.property).diff.continuousAt
  have hQc : ContinuousAt Q p.val := by dsimp only [Q]; fun_prop
  have hJc : ContinuousAt J p.val := by dsimp only [J]; fun_prop
  let line := fun s : ℝ => p.val+s • v
  have hline : Continuous line := by dsimp [line]; fun_prop
  have hn : ∀ᶠ s in 𝓝 (0:ℝ), 1 < ksRadius 2 (line s) ∧ Q (line s)<0 ∧ J (line s)<0 := by
    change line ⁻¹' {y | 1 < ksRadius 2 y ∧ Q y<0 ∧ J y<0} ∈ 𝓝 (0:ℝ)
    apply hline.continuousAt.preimage_mem_nhds
    change {y | 1 < ksRadius 2 y ∧ Q y<0 ∧ J y<0} ∈ 𝓝 (line 0)
    rw [show line 0=p.val by simp [line]]
    exact ((continuous_ksRadius 2).continuousAt.eventually (lt_mem_nhds hp)).and
      ((hQc.eventually (gt_mem_nhds hQ)).and (hJc.eventually (gt_mem_nhds hJ)))
  obtain ⟨δ,hδ,hball⟩ := Metric.mem_nhds_iff.mp hn
  let f := fun t : ℝ => (δ/Real.pi)*Real.arctan (t-b)
  have hpos : 0 < δ/Real.pi := div_pos hδ Real.pi_pos
  have hbound (t : ℝ) : f t ∈ Metric.ball 0 δ := by
    rw [Metric.mem_ball,Real.dist_eq,sub_zero]
    change |δ/Real.pi*Real.arctan (t-b)|<δ
    rw [abs_mul,abs_of_pos hpos]
    have har : |Real.arctan (t-b)|<Real.pi := by
      apply abs_lt.mpr
      constructor <;> linarith [Real.neg_pi_div_two_lt_arctan (t-b),Real.arctan_lt_pi_div_two (t-b),Real.pi_pos]
    have hh := mul_lt_mul_of_pos_left har hpos
    rwa [div_mul_cancel₀ δ Real.pi_ne_zero] at hh
  have hsafe (t) : 1 < ksRadius 2 (line (f t)) ∧ Q (line (f t))<0 ∧ J (line (f t))<0 :=
    hball (hbound t)
  let γ (t : ℝ) : U 2 := ⟨line (f t), lt_trans zero_lt_one (hsafe t).1⟩
  have hsm : ContDiff ℝ ∞ (fun t => line (f t)) := by
    have hAr : ContDiff ℝ ∞ (fun t : ℝ => Real.arctan (t-b)) :=
      Real.contDiff_arctan.comp (contDiff_id.sub contDiff_const)
    dsimp only [line,f]
    fun_prop
  have hγinf : ContMDiff 𝓘(ℝ,ℝ) I4 ∞ γ :=
    (ContMDiff.subtypeVal_comp_iff (U 2) γ).mp hsm.contMDiff
  have hγ : ContMDiff 𝓘(ℝ,ℝ) I4 1 γ := hγinf.of_le (by simp)
  refine ⟨γ,⟨hγ,?_⟩,?_,fun t => (hsafe t).1⟩
  · intro t _
    refine ⟨mem_univ _,?_⟩
    let N := (δ/Real.pi)*(1/(1+(t-b)^2))
    have hN : 0 < N := mul_pos hpos (by positivity)
    have hf : HasDerivAt f N t := by
      apply ((((hasDerivAt_id' t).sub_const b).arctan).const_mul (δ/Real.pi)).congr_deriv
      simp only [mul_one] <;> rfl
    have hd : HasDerivAt (fun t => (γ t).val) (N • v) t := (hf.smul_const v).const_add p.val
    rw [ambient_velocity 2 γ hγ t (N • v) hd]
    apply timelike_scale (5/2) 2 0 (γ t) v N hN
    constructor
    · change G (5/2) 2 0 (γ t) v v<0
      rw [metric_formula]; exact (hsafe t).2.1
    · change G (5/2) 2 0 (γ t) v (T (5/2) 2 0 (γ t))<0
      rw [metric_T]; exact (hsafe t).2.2
  · apply Subtype.ext
    change line (f b)=_
    simp [f,line]

theorem proved :
    let A := {x : kerrNewmanSpacetime 2 | 1 < ksRadius 2 x.val}
    let g := kerrNewmanMetricField (5/2) 2 0
    let T := kerrNewmanTimeDirection (5/2) 2 0
    chronoPastSet g T A = A ∧ A ⊆ chronoFutureSet g T A := by
  let A := {x : U 2 | 1 < ksRadius 2 x.val}
  constructor
  · ext x
    constructor
    · intro hx
      obtain ⟨q,hq,hc⟩ := mem_iUnion₂.mp hx
      obtain ⟨γ,hγ,h0,h1⟩ := hc
      by_contra hn
      have hlo : ksRadius 2 x.val ≤ 1 := le_of_not_gt hn
      have hi := trap (5/2) 2 0 1 (by norm_num) γ hγ (by rw [h0]; exact hlo)
      rw [h1] at hi
      exact (not_lt_of_ge hi) hq
    · intro hx
      obtain ⟨γ,hγ,h0,hA⟩ := nearby_events x hx 0
      exact mem_iUnion₂.mpr ⟨γ 1,hA 1,γ,hγ,h0,rfl⟩
  · intro x hx
    obtain ⟨γ,hγ,h1,hA⟩ := nearby_events x hx 1
    exact mem_iUnion₂.mpr ⟨γ 0,hA 0,γ,hγ,rfl,h1⟩
end
end InnerChronology

namespace InnerHelix
open NoHair Set
open scoped ContDiff Manifold BigOperators
noncomputable section

private abbrev U := kerrNewmanSpacetime 2
open InnerChronology (I4)

private def four (t x y z : ℝ) : E4 := WithLp.toLp 2 ![t,x,y,z]
private def move (b c s : ℝ) (y : E4) :=
  four (y 0+b) (c*y 1-s*y 2) (s*y 1+c*y 2) (y 3)
private def rotL (c s : ℝ) : E4 →L[ℝ] E4 :=
  LinearMap.toContinuousLinearMap
    { toFun := fun y => four (y 0) (c*y 1-s*y 2) (s*y 1+c*y 2) (y 3)
      map_add' := by intro v w; ext i; fin_cases i <;> simp [four] <;> ring
      map_smul' := by intro d w; ext i; fin_cases i <;> simp [four,smul_eq_mul] <;> ring }

private theorem radius_move (b c s : ℝ) (h : c^2+s^2=1) (y : E4) :
    ksRadius 2 (move b c s y)=ksRadius 2 y := by
  have hr : (c*y 1-s*y 2)^2+(s*y 1+c*y 2)^2=y 1^2+y 2^2 := by
    linear_combination (y 1^2+y 2^2)*h
  rw [ksRadius_eq']
  dsimp only [move,four]
  change Real.sqrt (((c*y 1-s*y 2)^2+(s*y 1+c*y 2)^2+y 3^2-2^2+
    Real.sqrt (((c*y 1-s*y 2)^2+(s*y 1+c*y 2)^2+y 3^2-2^2)^2+4*2^2*y 3^2))/2)=_
  rw [hr]

private theorem move_derivative (b c s : ℝ) (y : E4) :
    HasFDerivAt (move b c s) (rotL c s) y := by
  have he : move b c s=(fun z : E4 => rotL c s z+four b 0 0 0) := by
    funext z; ext i; fin_cases i <;> simp [move,rotL,four] <;> ring
  rw [he]
  exact (rotL c s).hasFDerivAt.add_const _

private def kv (y v : E4) :=
  v 0+ksNull 2 y 1*v 1+ksNull 2 y 2*v 2+ksNull 2 y 3*v 3
private def flat (v w : E4) := -(v 0*w 0)+v 1*w 1+v 2*w 2+v 3*w 3

private theorem metric_coeff (y v w : E4) :
    matrixBilin (kerrNewmanMetric (5/2) 2 0 y) v w =
      flat v w+ksProfile (5/2) 2 0 y*kv y v*kv y w := by
  change Matrix.toLinearMap₂' ℝ (kerrNewmanMetric (5/2) 2 0 y) (WithLp.ofLp v) (WithLp.ofLp w)=_
  simp only [Matrix.toLinearMap₂'_apply, smul_eq_mul,kerrNewmanMetric,Fin.sum_univ_four,ksNull_zero]
  simp [minkowski,kv,flat] <;> ring

private theorem invariant (b c s : ℝ) (h : c^2+s^2=1) (y v w : E4) :
    matrixBilin (kerrNewmanMetric (5/2) 2 0 (move b c s y)) (rotL c s v) (rotL c s w)=
    matrixBilin (kerrNewmanMetric (5/2) 2 0 y) v w := by
  let y' := move b c s y
  let L := rotL c s
  have hr : ksRadius 2 y'=ksRadius 2 y := radius_move b c s h y
  have hF : ksProfile (5/2) 2 0 y'=ksProfile (5/2) 2 0 y := by
    unfold ksProfile; rw [hr]; rfl
  have h1 : ksNull 2 y' 1=c*ksNull 2 y 1-s*ksNull 2 y 2 := by
    rw [ksNull_one,hr,ksNull_one,ksNull_two]
    change (ksRadius 2 y*(c*y 1-s*y 2)+2*(s*y 1+c*y 2))/_=_
    ring
  have h2 : ksNull 2 y' 2=s*ksNull 2 y 1+c*ksNull 2 y 2 := by
    rw [ksNull_two,hr,ksNull_one,ksNull_two]
    change (ksRadius 2 y*(s*y 1+c*y 2)-2*(c*y 1-s*y 2))/_=_
    ring
  have h3 : ksNull 2 y' 3=ksNull 2 y 3 := by rw [ksNull_three,ksNull_three,hr]; rfl
  have hk (v : E4) : kv y' (L v)=kv y v := by
    change v 0+ksNull 2 y' 1*(c*v 1-s*v 2)+ksNull 2 y' 2*(s*v 1+c*v 2)+ksNull 2 y' 3*v 3=_
    rw [h1,h2,h3]; dsimp [kv]
    linear_combination (ksNull 2 y 1*v 1+ksNull 2 y 2*v 2)*h
  have hf : flat (L v) (L w)=flat v w := by
    change -(v 0*w 0)+(c*v 1-s*v 2)*(c*w 1-s*w 2)+(s*v 1+c*v 2)*(s*w 1+c*w 2)+v 3*w 3=_
    dsimp [flat]; linear_combination (v 1*w 1+v 2*w 2)*h
  rw [metric_coeff,metric_coeff]
  change flat (L v) (L w)+ksProfile (5/2) 2 0 y'*kv y' (L v)*kv y' (L w)=_
  rw [hf,hF,hk,hk]

private theorem ambient_velocity (γ : ℝ → U) (hγ : ContMDiff 𝓘(ℝ,ℝ) I4 1 γ) (v : E4)
    (hd : HasDerivAt (fun t => (γ t).val) v 0) : (velocity γ 0 : E4)=v :=
  InnerChronology.ambient_velocity 2 γ hγ 0 v hd

private theorem four_deriv {t x y z : ℝ → ℝ} {dt dx dy dz s : ℝ}
    (ht : HasDerivAt t dt s) (hx : HasDerivAt x dx s) (hy : HasDerivAt y dy s) (hz : HasDerivAt z dz s) :
    HasDerivAt (fun s => four (t s) (x s) (y s) (z s)) (four dt dx dy dz) s := by
  have h : HasDerivAt (fun s => (![t s,x s,y s,z s] : Fin 4 → ℝ)) ![dt,dx,dy,dz] s := by
    apply hasDerivAt_pi.mpr
    intro i
    fin_cases i
    · exact ht
    · exact hx
    · exact hy
    · exact hz
  exact (PiLp.hasFDerivAt_toLp (𝕜 := ℝ) 2 _).comp_hasDerivAt s h

theorem proved :
    let X : VecField (kerrNewmanSpacetime 2) := fun x => WithLp.toLp 2 ![1,-(2/5)*x.val 2,(2/5)*x.val 1,0]
    ∃ χ : ℝ → kerrNewmanSpacetime 2 → kerrNewmanSpacetime 2,
      IsSymmetryFlow (kerrNewmanMetricField (5/2) 2 0) (kerrNewmanFieldField 2 0) χ ∧
      flowGenerator χ=X := by
  let q : ℝ := 2/5
  let c := fun t => Real.cos (q*t)
  let s := fun t => Real.sin (q*t)
  have hc (t) : c t^2+s t^2=1 := Real.cos_sq_add_sin_sq _
  let χ (t : ℝ) (x : U) : U := ⟨move t (c t) (s t) x.val,by
    change 0<ksRadius 2 (move t (c t) (s t) x.val)
    rw [radius_move _ _ _ (hc t)]; exact x.property⟩
  let H := fun p : ℝ × E4 => move p.1 (c p.1) (s p.1) p.2
  have hH : ContDiff ℝ ∞ H := by
    apply (contDiff_piLp 2).2
    intro i; fin_cases i
    · change ContDiff ℝ ∞ (fun p : ℝ × E4 => p.2 0+p.1); fun_prop
    · change ContDiff ℝ ∞ (fun p : ℝ × E4 => c p.1*p.2 1-s p.1*p.2 2); dsimp [c,s]; fun_prop
    · change ContDiff ℝ ∞ (fun p : ℝ × E4 => s p.1*p.2 1+c p.1*p.2 2); dsimp [c,s]; fun_prop
    · change ContDiff ℝ ∞ (fun p : ℝ × E4 => p.2 3); fun_prop
  have hval : ContMDiff I4 I4 ∞ (Subtype.val : U → E4) := contMDiff_subtype_val
  have hχ : ContMDiff (𝓘(ℝ,ℝ).prod I4) I4 ∞ (fun p : ℝ × U => χ p.1 p.2) := by
    apply (ContMDiff.subtypeVal_comp_iff U _).mp
    have pair : ContMDiff (𝓘(ℝ,ℝ).prod I4) 𝓘(ℝ,ℝ × E4) ∞ (fun p : ℝ × U => (p.1,p.2.val)) :=
      (contMDiff_prod_module_iff _).2 ⟨contMDiff_fst,hval.comp contMDiff_snd⟩
    exact hH.contMDiff.comp pair
  have hds (t) (x : U) : (mfderiv I4 I4 (χ t) x : E4 →L[ℝ] E4)=rotL (c t) (s t) := by
    have hd := move_derivative t (c t) (s t) x.val
    have hh : ContMDiff I4 I4 ∞ (χ t) := hχ.comp (contMDiff_const.prodMk contMDiff_id)
    have inc (p : U) : (mfderiv I4 I4 (Subtype.val : U → E4) p : E4 →L[ℝ] E4)=
      ContinuousLinearMap.id ℝ E4 := mfderiv_extChartAt_self (I := I4) (x := p)
    calc
      _=(mfderiv I4 I4 (Subtype.val : U → E4) (χ t x)).comp (mfderiv I4 I4 (χ t) x) := by rw [inc]; rfl
      _=mfderiv I4 I4 ((Subtype.val : U → E4) ∘ χ t) x :=
        (mfderiv_comp x (hval.mdifferentiableAt (by simp)) (hh.mdifferentiableAt (by simp))).symm
      _=(mfderiv I4 I4 (move t (c t) (s t)) x.val).comp (mfderiv I4 I4 (Subtype.val : U → E4) x) :=
        mfderiv_comp x hd.differentiableAt.mdifferentiableAt (hval.mdifferentiableAt (by simp))
      _=_ := by rw [inc,mfderiv_eq_fderiv,hd.fderiv]; rfl
  have f0 (x : U) : kerrNewmanFieldField 2 0 x=0 := by
    have he : kerrNewmanField 2 0 x.val=0 := by
      ext i j; simp [kerrNewmanField,coordPartial,kerrNewmanPotential]
    change matrixBilin (kerrNewmanField 2 0 x.val)=0
    rw [he]; ext v w; simp [matrixBilin,Matrix.toLinearMap₂'_apply]
  refine ⟨χ,⟨?_,?_,hχ,?_,?_⟩,?_⟩
  · intro x
    apply Subtype.ext
    ext i; fin_cases i <;> simp [χ,move,four,c,s]
  · intro t u x
    apply Subtype.ext
    ext i; fin_cases i <;> simp [χ,move,four,c,s,mul_add,Real.sin_add,Real.cos_add] <;> ring
  · intro t x v w
    rw [hds]
    exact invariant t (c t) (s t) (hc t) x.val v w
  · intro t x v w; rw [f0,f0]; rfl
  · funext x
    have hh : ContMDiff 𝓘(ℝ,ℝ) I4 1 (fun t => χ t x) :=
      (hχ.comp (contMDiff_id.prodMk contMDiff_const)).of_le (by simp)
    apply ambient_velocity (fun t => χ t x) hh
    have hq : HasDerivAt (fun t : ℝ => q*t) q 0 := by simpa using (hasDerivAt_id' (0:ℝ)).const_mul q
    have hv := four_deriv ((hasDerivAt_id' (0:ℝ)).const_add (x.val 0))
      ((hq.cos.mul_const (x.val 1)).sub (hq.sin.mul_const (x.val 2)))
      ((hq.sin.mul_const (x.val 1)).add (hq.cos.mul_const (x.val 2))) (hasDerivAt_const (0:ℝ) (x.val 3))
    apply hv.congr_deriv
    ext i; fin_cases i <;> simp [four,q] <;> ring
end
end InnerHelix

namespace InnerSurfaceGravity
open NoHair NoHair.KNE Set Filter
open scoped Topology
open scoped BigOperators Manifold ContDiff

noncomputable section

open InnerChronology (U)

open InnerChronology (G)

open InnerChronology (T)

open InnerChronology (I4)

open InnerChronology (V3)

open InnerChronology (dot3)

open InnerChronology (space)

open InnerChronology (axis)

open InnerChronology (timeC)

open InnerChronology (dot_symm)

open InnerChronology (dot_add_l)

open InnerChronology (dot_add_r)

open InnerChronology (dot_scale_l)

open InnerChronology (dot_scale_r)

open InnerChronology (dot_cauchy)

open InnerChronology (axis_unit)

open InnerChronology (metric_formula)

open InnerChronology (radialNormal)

open InnerChronology (normal_geometry)

open InnerChronology (radial_derivative)

private theorem metric_entries (m a e : ℝ) (x : U a) (v w : E4) :
    G m a e x v w = -(v 0*w 0)+v 1*w 1+v 2*w 2+v 3*w 3+
      ksProfile m a e x.val * (v 0 + ksNull a x.val 1*v 1+ksNull a x.val 2*v 2+ksNull a x.val 3*v 3) *
        (w 0 + ksNull a x.val 1*w 1+ksNull a x.val 2*w 2+ksNull a x.val 3*w 3) := by
  change Matrix.toLinearMap₂' ℝ (kerrNewmanMetric m a e x.val) (WithLp.ofLp v) (WithLp.ofLp w) = _
  simp only [Matrix.toLinearMap₂'_apply, smul_eq_mul, kerrNewmanMetric, Fin.sum_univ_four, ksNull_zero]
  simp [minkowski] <;> ring


private def spiral (y : E4) : E4 := WithLp.toLp 2 ![1,-(2/5)*y 2,(2/5)*y 1,0]
private def poly (r c : ℝ) := 64*c^4+36*c^2+(r^3+r^2)*(4-4*c^2)+r*(-16*c^4-4*c^2-5)
private def factor (y : E4) :=
  let r := ksRadius 2 y
  let c := ksNull 2 y 3
  poly r c / (25*(r^2+4*c^2))
private def normFun (y : E4) := matrixBilin (kerrNewmanMetric (5/2) 2 0 y) (spiral y) (spiral y)

private theorem norm_factored (y : E4) (hy : 0 < ksRadius 2 y) :
    normFun y=(ksRadius 2 y-1)*factor y := by
  let r := ksRadius 2 y
  let l := ksNull 2 y
  let c := l 3
  let B := 1-c^2
  let S := r^2+4*c^2
  let x : U 2 := ⟨y,hy⟩
  have hS : 0<S := by have : 0<r := hy; dsimp [S]; positivity
  have h1 : y 1=r*l 1-2*l 2 := ks_x1 2 y hy
  have h2 : y 2=r*l 2+2*l 1 := by linear_combination ks_x2 2 y hy
  have h3 : l 1^2+l 2^2+c^2=1 := ks_rel 2 y hy
  have hQ : y 1^2+y 2^2=(r^2+4)*B := by rw [h1,h2]; dsimp [B]; linear_combination (r^2+4)*h3
  have hK : 1+l 1*(-(2/5)*y 2)+l 2*((2/5)*y 1)+c*0=1-(4/5)*B := by
    rw [h1,h2]; dsimp [B]; linear_combination -(4/5:ℝ)*h3
  have hP : ksProfile (5/2) 2 0 y=5*r/S := by
    rw [profile_eq _ _ _ _ hy]; dsimp only [fA,Wf]
    change ((2*(5/2)*r-0^2)*(1/(r^2+2^2*c^2)))=_
    dsimp [S]; ring
  have hflat : -(1*1:ℝ)+(-(2/5)*y 2)*(-(2/5)*y 2)+((2/5)*y 1)*((2/5)*y 1)+0*0 =
      -1+(4/25)*(r^2+4)*B := by linear_combination (4/25:ℝ)*hQ
  change G (5/2) 2 0 x (spiral y) (spiral y)=_
  rw [metric_entries]
  change -(1*1:ℝ)+(-(2/5)*y 2)*(-(2/5)*y 2)+((2/5)*y 1)*((2/5)*y 1)+0*0+
    ksProfile (5/2) 2 0 y * (1+l 1*(-(2/5)*y 2)+l 2*((2/5)*y 1)+c*0)*
      (1+l 1*(-(2/5)*y 2)+l 2*((2/5)*y 1)+c*0) = (r-1)*(poly r c/(25*S))
  rw [hflat,hP,hK]
  field_simp [hS.ne']
  dsimp only [S,B,poly]
  ring

private theorem on_level (x : U 2) (hr : ksRadius 2 x.val=1) :
    let c := ksNull 2 x.val 3
    factor x.val = 3*(1+4*c^2)/25 ∧
      ∀ v : E4, G (5/2) 2 0 x (spiral x.val) v =
        ((1+4*c^2)/5)*fderiv ℝ (ksRadius 2) x.val v := by
  let l := ksNull 2 x.val
  let c := l 3
  let S := 1+4*c^2
  have hs : 0<S := by dsimp [S]; positivity
  have hP : ksProfile (5/2) 2 0 x.val=5/S := by
    rw [profile_eq _ _ _ _ x.property]; dsimp only [fA,Wf]; rw [hr]
    change ((2*(5/2)*1-0^2)*(1/(1^2+2^2*c^2)))=_
    dsimp [S]; ring
  have h1 := ks_x1 2 x.val x.property
  have h2 := ks_x2 2 x.val x.property
  rw [hr,one_mul] at h1 h2
  change x.val 1=l 1-2*l 2 at h1
  change x.val 2=2*l 1+l 2 at h2
  have h3 : l 1^2+l 2^2+c^2=1 := ks_rel 2 x.val x.property
  have hK : 1+l 1*(-(2/5)*x.val 2)+l 2*((2/5)*x.val 1)+c*0=S/5 := by
    rw [h1,h2]; dsimp [S]; linear_combination -(4/5:ℝ)*h3
  constructor
  · change poly (ksRadius 2 x.val) c/(25*((ksRadius 2 x.val)^2+4*c^2))=_
    rw [hr,one_pow]; change poly 1 c/(25*S)=3*S/25
    field_simp [hs.ne']; dsimp [poly,S]; ring
  · intro v
    rw [metric_entries,radial_derivative]
    have hW : Wf 2 x.val=1/S := by
      unfold Wf; rw [hr]; change 1/(1^2+2^2*c^2)=1/S
      dsimp [S]; ring
    change -(1*v 0)+(-(2/5)*x.val 2)*v 1+((2/5)*x.val 1)*v 2+0*v 3+
      ksProfile (5/2) 2 0 x.val*(1+l 1*(-(2/5)*x.val 2)+l 2*((2/5)*x.val 1)+c*0)*
      (v 0+l 1*v 1+l 2*v 2+c*v 3)=S/5*dot3 (radialNormal 2 x.val) (space v)
    rw [hK,hP,h1,h2]
    simp only [dot3,radialNormal,space,axis,Fin.sum_univ_three,Matrix.cons_val,hr,hW]
    change _=S/5*((1^2*l 1*(1/S)-1*l 2*(1/S)*2)*v 1+
      (1^2*l 2*(1/S)+1*l 1*(1/S)*2)*v 2+((1^2+2^2)*c*(1/S))*v 3)
    field_simp [hs.ne'] <;> ring

private theorem norm_deriv (x : U 2) (hr : ksRadius 2 x.val=1) (v : E4) :
    fderiv ℝ normFun x.val v=(3/5)*G (5/2) 2 0 x (spiral x.val) v := by
  have hR := ksRadius_differentiableAt 2 x.val x.property
  have hC := ksNull_differentiableAt 2 x.val x.property 3
  have hs : 0 < (ksRadius 2 x.val)^2+4*(ksNull 2 x.val 3)^2 := by rw [hr]; positivity
  have hfactor : DifferentiableAt ℝ factor x.val := by
    have hn : 25*((ksRadius 2 x.val)^2+4*(ksNull 2 x.val 3)^2) ≠ 0 := by positivity
    unfold factor poly
    fun_prop (disch := assumption)
  let line := fun t : ℝ => x.val+t • v
  have h0 : line 0=x.val := by simp [line]
  have hline : HasDerivAt line v 0 := by
    simpa [line] using ((hasDerivAt_id (0:ℝ)).smul_const v).const_add x.val
  have hfun : normFun =ᶠ[𝓝 x.val] (fun y => (ksRadius 2 y-1)*factor y) := by
    filter_upwards [(continuous_ksRadius 2).continuousAt.eventually (lt_mem_nhds x.property)] with y hy
    exact norm_factored y hy
  have hdiff : DifferentiableAt ℝ normFun x.val :=
    ((hR.sub_const 1).mul hfactor).congr_of_eventuallyEq hfun
  have lineD (f : E4 → ℝ) (hd : DifferentiableAt ℝ f x.val) :
      HasDerivAt (fun t => f (line t)) (fderiv ℝ f x.val v) 0 := by
    have hh : HasFDerivAt f (fderiv ℝ f x.val) (line 0) := by rw [h0]; exact hd.hasFDerivAt
    exact hh.comp_hasDerivAt 0 hline
  have heq : (fun t => normFun (line t)) =ᶠ[𝓝 0] (fun t => (ksRadius 2 (line t)-1)*factor (line t)) :=
    hfun.comp_tendsto (by simpa only [h0] using hline.continuousAt.tendsto)
  have h := (lineD normFun hdiff).unique (((((lineD _ hR).sub_const 1).mul (lineD _ hfactor))).congr_of_eventuallyEq heq)
  rw [h0,hr] at h
  obtain ⟨hfac,hflat⟩ := on_level x hr
  rw [h,hfac,hflat]
  ring

theorem proved :
    let X : VecField (kerrNewmanSpacetime 2) := fun x => WithLp.toLp 2 ![1,-(2/5)*x.val 2,(2/5)*x.val 1,0]
    let g := kerrNewmanMetricField (5/2) 2 0
    ∀ x : kerrNewmanSpacetime 2, ksRadius 2 x.val=1 → g x (X x) (X x)=0 ∧
      ∀ e ∈ atlas E4 (kerrNewmanSpacetime 2), ∀ y ∈ e.target, e.symm y=x → ∀ i : Fin 4,
        coordPartial (fun z => g (e.symm z) (X (e.symm z)) (X (e.symm z))) i y =
          (3/5)*loweredCoeffs g X e.symm y i := by
  dsimp only
  intro x hx
  constructor
  · change normFun x.val=0
    rw [norm_factored _ x.property,hx]; ring
  · intro e he y hy hyx i
    obtain ⟨p,hp⟩ := TopologicalSpace.Opens.chart_eq (H := E4) ⟨e.symm y⟩ he
    have hchart (w : U 2) : e=chartAt E4 w := hp.trans (by rfl)
    have hval (z : E4) (hz : z ∈ e.target) : (e.symm z).val=z := by
      have h (w : U 2) : e w=w.val := by rw [hchart w]; rfl
      exact (h (e.symm z)).symm.trans (e.right_inv hz)
    have hxy : x.val=y := by simpa only [hyx] using hval y hy
    have hd : (mfderiv I4 I4 e.symm y : E4 →L[ℝ] E4)=ContinuousLinearMap.id ℝ E4 := by
      rw [← hxy,hchart x]
      have hh := mfderivWithin_range_extChartAt_symm (I := I4) (x := x)
      simp only [modelWithCornersSelf_coe,range_id,mfderivWithin_univ] at hh
      exact hh
    have heq : (fun z => normFun (e.symm z).val) =ᶠ[𝓝 y] normFun := by
      filter_upwards [e.open_target.mem_nhds hy] with z hz
      rw [hval z hz]
    change fderiv ℝ (fun z => normFun (e.symm z).val) y (coordBasis i) =
      (3/5)*G (5/2) 2 0 (e.symm y) (spiral (e.symm y).val) (mfderiv I4 I4 e.symm y (coordBasis i))
    rw [heq.fderiv_eq,hd,hyx,← hxy]
    exact norm_deriv x hx (coordBasis i)
end
end InnerSurfaceGravity

namespace InnerHorizonGeometry
open NoHair Set
open scoped ContDiff Manifold BigOperators Topology

open InnerRegularity (entry)

private theorem analytic_restrict (U : TopologicalSpace.Opens E4) (A : E4 → Matrix (Fin 4) (Fin 4) ℝ)
    (h : ∀ y ∈ U, ∀ i j, ContDiffAt ℝ ω (fun z => A z i j) y) :
    IsAnalyticBilinField (M := U) (fun x => matrixBilin (A x.val)) := by
  intro c hc i j y hy
  obtain ⟨p, hp⟩ := TopologicalSpace.Opens.chart_eq (H := E4) ⟨c.symm y⟩ hc
  have hchart (x : U) : c = chartAt E4 x := hp.trans (by rfl)
  have hval (z : E4) (hz : z ∈ c.target) : (c.symm z).val = z := by
    have eqval (x : U) : c x = x.val := by rw [hchart x] <;> rfl
    exact (eqval (c.symm z)).symm.trans (c.right_inv hz)
  have derivAt (x : U) :
      (mfderiv 𝓘(ℝ, E4) 𝓘(ℝ, E4) c.symm x.val : E4 →L[ℝ] E4) = ContinuousLinearMap.id ℝ E4 := by
    rw [hchart x]
    have hd := mfderivWithin_range_extChartAt_symm (I := 𝓘(ℝ, E4)) (x := x)
    simp only [modelWithCornersSelf_coe, range_id, mfderivWithin_univ] at hd
    exact hd
  have coeff (z : E4) (hz : z ∈ c.target) :
      pullbackCoeffs (M := U) (fun x => matrixBilin (A x.val)) c.symm z i j = A z i j := by
    have hd := derivAt (c.symm z)
    rw [hval z hz] at hd
    unfold pullbackCoeffs
    rw [hd]
    change matrixBilin (A (c.symm z).val) (coordBasis i) (coordBasis j) = A z i j
    rw [hval z hz, entry]
  have hs : ContDiffOn ℝ ω (fun z => A z i j) c.target := by
    intro z hz
    have hzU : z ∈ U := (hval z hz) ▸ (c.symm z).property
    exact (h z hzU i j).contDiffWithinAt
  exact (hs.congr coeff) y hy

open InnerRegularity (radius_analytic null_analytic)

theorem proved :
    let A := {x : kerrNewmanSpacetime 2 | 1 < ksRadius 2 x.val}
    let g := kerrNewmanMetricField (5/2) 2 0
    let F := kerrNewmanFieldField 2 0
    IsAnalyticBilinField g ∧ Aᶜ.Nonempty ∧ IsConnected (frontier A) ∧
      IsNondegenerateHorizon g F (frontier A) A := by
  let A := {x : kerrNewmanSpacetime 2 | 1 < ksRadius 2 x.val}
  let X : VecField (kerrNewmanSpacetime 2) :=
    fun x => WithLp.toLp 2 ![1,-(2/5)*x.val 2,(2/5)*x.val 1,0]
  obtain ⟨hfront,hlevel⟩ := InnerFrontier.proved 2 1 (by norm_num)
  have hfront' : frontier A={x : kerrNewmanSpacetime 2 | ksRadius 2 x.val=1} := hfront
  obtain ⟨x,hx⟩ := hlevel.nonempty
  have hx' : ksRadius 2 x.val=1 := hx
  have hxH : x ∈ frontier A := by rw [hfront']; exact hx
  obtain ⟨χ,hχ,hX⟩ := InnerHelix.proved
  refine ⟨?_,⟨x,not_lt_of_ge hx'.le⟩,(by change IsConnected (frontier A); rw [hfront']; exact hlevel),χ,-3/10,hχ,by norm_num,?_,?_⟩
  · apply analytic_restrict (kerrNewmanSpacetime 2) (kerrNewmanMetric (5/2) 2 0)
    intro y hy i j
    have hpos : 0 < ksRadius 2 y := hy
    have hr := radius_analytic 2 y hpos
    have hi := null_analytic 2 y hpos i
    have hj := null_analytic 2 y hpos j
    have hd := (ks_den_pos 2 y hpos).ne'
    unfold kerrNewmanMetric ksProfile
    fun_prop (disch := assumption)
  · refine ⟨x,⟨hxH,frontier_subset_closure hxH⟩,?_⟩
    rw [hX]
    intro hzero
    have he := congrArg (fun v : E4 => v 0) hzero
    change (1:ℝ)=0 at he
    norm_num at he
  · intro y hy
    have hmem := hy.1
    rw [hfront'] at hmem
    rw [hX]
    have h := InnerSurfaceGravity.proved y hmem
    simpa only [show (-2:ℝ)*(-3/10)=3/5 by norm_num] using h

end InnerHorizonGeometry

namespace InnerTrappedObservers
open NoHair NoHair.KNE Set Filter
open scoped Topology
open scoped BigOperators Manifold ContDiff

noncomputable section

open InnerChronology (U)

open InnerChronology (G)

open InnerChronology (T)

open InnerChronology (I4)

open InnerChronology (V3)

open InnerChronology (dot3)

open InnerChronology (space)

open InnerChronology (axis)

open InnerChronology (timeC)

open InnerChronology (dot_symm)

open InnerChronology (dot_add_l)

open InnerChronology (dot_add_r)

open InnerChronology (dot_scale_l)

open InnerChronology (dot_scale_r)

open InnerChronology (dot_cauchy)

open InnerChronology (axis_unit)

open InnerChronology (metric_formula)

open InnerChronology (radialNormal)

open InnerChronology (normal_geometry)

open InnerChronology (radial_derivative)

open InnerHelix (four)

private def oblate (a r t X Y Z : ℝ) := four t (r*X-a*Y) (a*X+r*Y) (r*Z)
private def sigma (a Z r : ℝ) := r^2+a^2*Z^2
private def bigP (a r : ℝ) := r^2+a^2
private def massTerm (m e r : ℝ) := 2*m*r-e^2

private theorem oblate_data (a r t X Y Z : ℝ) (hr : 0 < r) (hk : X^2+Y^2+Z^2=1) :
    let y := oblate a r t X Y Z
    ksRadius a y = r ∧ ksNull a y = ![1,X,Y,Z] ∧ r  ≤  spatialRadius y := by
  let ρ2 := (r*X-a*Y)^2+(a*X+r*Y)^2+(r*Z)^2
  have hρ : ρ2 = r^2+a^2*(1-Z^2) := by
    dsimp [ρ2]; linear_combination (r^2+a^2)*hk
  have hs : 0  ≤  r^2+a^2*Z^2 := by positivity
  have hc : ρ2-a^2 = r^2-a^2*Z^2 := by rw [hρ]; ring
  have hD : (ρ2-a^2)^2+4*a^2*(r*Z)^2 = (r^2+a^2*Z^2)^2 := by rw [hc]; ring
  have hrad : ksRadius a (oblate a r t X Y Z) = r := by
    change Real.sqrt ((ρ2-a^2+Real.sqrt ((ρ2-a^2)^2+4*a^2*(r*Z)^2))/2)=r
    rw [hD, Real.sqrt_sq hs, hc]
    convert Real.sqrt_sq hr.le using 2 <;> ring
  refine ⟨hrad, ?_, ?_⟩
  · unfold ksNull
    rw [hrad]
    have hden : r^2+a^2  ≠  0 := by positivity
    funext i
    fin_cases i <;> simp [four,oblate, hden, hr.ne'] <;> field_simp [hden,hr.ne'] <;> ring
  · change r  ≤  Real.sqrt ρ2
    have hxy : 0  ≤  1-Z^2 := by nlinarith only [hk,sq_nonneg X,sq_nonneg Y]
    apply Real.le_sqrt_of_sq_le
    rw [hρ]; linarith [mul_nonneg (sq_nonneg a) hxy]

private def velocityShape (a r X Y Z u : ℝ) : E4 :=
  four (bigP a r) (-a*(a*X+r*Y)+u*X) (a*(r*X-a*Y)+u*Y) (u*Z)

open InnerSurfaceGravity (metric_entries)

open InnerHelix (four_deriv)

open InnerChronology (ambient_velocity)

private theorem reverse_sq (c tau q B j : ℝ) (hq : 0 ≤ q) (hB : 0 ≤ B)
    (ht : tau^2=q+1) (hj : j^2≤B*q) : c^2-B ≤ (j-c*tau)^2 := by
  rcases hq.eq_or_lt with hz|hp
  · subst q
    have hj' : j=0 := by nlinarith only [hj,sq_nonneg j]
    rw [hj']
    nlinarith only [hB,show c^2*tau^2=c^2 by rw [ht]; ring]
  · apply (le_of_mul_le_mul_left (a := q) ?_ hp)
    have he : q*((j-c*tau)^2-(c^2-B)) = (tau*j-c*q)^2+(B*q-j^2) := by
      linear_combination (q*c^2-j^2)*ht
    nlinarith only [he,hj,sq_nonneg (tau*j-c*q)]

private theorem radial_unit (z : U 2) (v : E4) (hv : G (5/2) 2 0 z v v = -1)
    (hr1 : 1 < ksRadius 2 z.val) (hr2 : ksRadius 2 z.val ≤ 2) :
    ksRadius 2 z.val-1 ≤ 4*(fderiv ℝ (ksRadius 2) z.val v)^2 := by
  let r := ksRadius 2 z.val
  let k := axis 2 z.val
  let n := radialNormal 2 z.val
  let s := space v
  let t := timeC v
  let W := Wf 2 z.val
  let f := ksProfile (5/2) 2 0 z.val
  let c := f/2
  let l := t+dot3 k s
  let tau := t-c*l
  let u := s+(c*l) • k
  let b := n+(-c) • k
  have hk : dot3 k k=1 := axis_unit 2 z
  obtain ⟨hnk,hn⟩ := normal_geometry 2 z
  change dot3 n k=1 at hnk
  change dot3 n n=(r^2+2^2)*W at hn
  have ff : f=2*c := by dsimp only [c]; ring
  have ht : tau^2=dot3 u u+1 := by
    have he : dot3 u u-tau^2= -t*t+dot3 s s+f*l*l := by
      simp only [u,tau,l,dot_add_l,dot_add_r,dot_scale_l,dot_scale_r,hk,dot_symm s k]
      rw [ff]; ring
    rw [metric_formula] at hv
    change -(t*t)+dot3 s s+f*l*l= -1 at hv
    linarith
  have hb : dot3 b b=dot3 n n-f+c^2 := by
    simp only [b,dot_add_l,dot_add_r,dot_scale_l,dot_scale_r,hnk,dot_symm k n,hk]
    rw [ff]; ring
  have he : dot3 n s = dot3 b u-c*tau := by
    simp only [b,u,tau,l,dot_add_l,dot_add_r,dot_scale_l,dot_scale_r,hnk,hk]; ring
  have self (w : V3) : 0 ≤ dot3 w w := by
    unfold dot3; exact Finset.sum_nonneg (fun i _ => mul_self_nonneg _)
  have hcs := reverse_sq c tau (dot3 u u) (dot3 b b) (dot3 b u) (self u) (self b) ht (dot_cauchy b u)
  rw [← he,hb,hn] at hcs
  have hf : f=(5*r)*W := by
    change ksProfile (5/2) 2 0 z.val=_
    rw [profile_eq _ _ _ _ z.property]
    dsimp only [fA]; ring
  have hW : W*(r^2+2^2*(k 2)^2)=1 := ks_W 2 z.val z.property
  have hW0 : 0 < W := by dsimp only [W,Wf]; have := z.property; positivity
  have hrel : k 0^2+k 1^2+k 2^2=1 := ks_rel 2 z.val z.property
  have hZ : (k 2)^2 ≤ 1 := by nlinarith only [hrel,sq_nonneg (k 0),sq_nonneg (k 1)]
  have hs : r^2+2^2*(k 2)^2≤8 := by
    have hr : r≤2 := hr2
    have hz : 0≤r := z.property.le
    nlinarith only [hZ,mul_nonneg (sub_nonneg.mpr hr) (show 0≤2+r by linarith)]
  have hw8 : 1≤8*W := by nlinarith only [hW,mul_nonneg hW0.le (sub_nonneg.mpr hs)]
  have hr1' : 0≤r-1 := (sub_pos.mpr hr1).le
  have hmul : (r-1)*2≤(r-1)*(4-r) := by
    have hr : r≤2 := hr2
    exact mul_le_mul_of_nonneg_left (by linarith) hr1'
  rw [hf] at hcs
  rw [radial_derivative]
  change r-1≤4*(dot3 n s)^2
  nlinarith only [hcs,mul_nonneg hr1' (sub_nonneg.mpr hw8),
    mul_le_mul_of_nonneg_right hmul hW0.le]

/-- A positive function with the trapped-region radial rate cannot exist for all proper times. -/
private theorem no_trapped_line (r : ℝ → ℝ) (d : ℝ → ℝ) (h : ∀ t, HasDerivAt r (d t) t)
    (hp : ∀ t, 1 < r t) (h0 : r 0=2) (hrate : ∀ t, r t≤2 → r t-1 ≤ 4*(d t)^2) : False := by
  let f := fun t : ℝ => Real.sqrt (r t-1)+t^2/256
  have hs (t : ℝ) : HasDerivAt (fun t => Real.sqrt (r t-1)) (d t/(2*Real.sqrt (r t-1))) t :=
    ((h t).sub_const 1).sqrt (sub_pos.mpr (hp t)).ne'
  have hf (t : ℝ) : HasDerivAt f (d t/(2*Real.sqrt (r t-1))+t/128) t := by
    apply ((hs t).add (((hasDerivAt_id' t).pow 2).div_const 256)).congr_deriv
    simp <;> ring
  have hfc : Continuous f := continuous_iff_continuousAt.mpr (fun t => (hf t).continuousAt)
  obtain ⟨t,ht,hm⟩ := isCompact_Icc.exists_isMinOn (f := f)
    (nonempty_Icc.mpr (by norm_num : (-16:ℝ) ≤ 16)) hfc.continuousOn
  have hmin : f t≤1 := by
    have h' := hm (show (0:ℝ) ∈ Icc (-16) 16 by constructor <;> norm_num)
    norm_num [f,h0] at h' ⊢
    exact h'
  have hsp (w : ℝ) : 0 < Real.sqrt (r w-1) := Real.sqrt_pos.mpr (sub_pos.mpr (hp w))
  have hi : t ∈ Ioo (-16:ℝ) 16 := by
    have hpos := hsp t
    change Real.sqrt (r t-1)+t^2/256≤1 at hmin
    constructor
    · rcases ht.1.eq_or_lt with eq|lt
      · rw [← eq] at hpos hmin; norm_num at hmin; linarith
      · exact lt
    · rcases ht.2.eq_or_lt with eq|lt
      · rw [eq] at hpos hmin; norm_num at hmin; linarith
      · exact lt
  have hminlocal := hm.isLocalMin (Icc_mem_nhds hi.1 hi.2)
  have hvan := hminlocal.hasDerivAt_eq_zero (hf t)
  let v := Real.sqrt (r t-1)
  have hv : 0<v := hsp t
  have hv2 : v^2=r t-1 := Real.sq_sqrt (sub_pos.mpr (hp t)).le
  have hv1 : v≤1 := by
    change v+t^2/256≤1 at hmin
    nlinarith only [hmin,sq_nonneg t]
  have hrt : r t≤2 := by nlinarith only [hv2,mul_nonneg (sub_nonneg.mpr hv1) (show 0≤1+v by linarith)]
  have hd := hrate t hrt
  change d t/(2*v)+t/128=0 at hvan
  have he : d t= -(t*v)/64 := by
    field_simp [hv.ne'] at hvan
    linarith
  rw [he,← hv2] at hd
  have ht2 : t^2<256 := by nlinarith only [mul_pos (sub_pos.mpr hi.2) (show 0<t+16 by linarith [hi.1])]
  nlinarith only [hd,mul_lt_mul_of_pos_right ht2 (sq_pos_of_pos hv),sq_pos_of_pos hv]

private theorem orbit_norm (m a r t X Y Z : ℝ) (hr : 0<r) (hk : X^2+Y^2+Z^2=1) :
    let y := oblate a r t X Y Z
    let v := velocityShape a r X Y Z 0
    matrixBilin (kerrNewmanMetric m a 0 y) v v =
      -((r^2+a^2-2*m*r)*(r^2+a^2*Z^2)) := by
  let y := oblate a r t X Y Z
  let v := velocityShape a r X Y Z 0
  obtain ⟨hR,hK,_⟩ := oblate_data a r t X Y Z hr hk
  have hs : 0 < r^2+a^2*Z^2 := by positivity
  let x : U a := ⟨y,show 0<ksRadius a y by rw [hR]; exact hr⟩
  have hp : ksProfile m a 0 y*(r^2+a^2*Z^2)=2*m*r := by
    rw [profile_eq m a 0 y x.property]
    dsimp only [fA,Wf]
    rw [hR,hK]
    change ((2*m*r-0^2)*(1/(r^2+a^2*Z^2)))*(r^2+a^2*Z^2)=_
    field_simp [hs.ne'] <;> ring
  have hvk : v 0+X*v 1+Y*v 2+Z*v 3=r^2+a^2*Z^2 := by
    change r^2+a^2+X*(-a*(a*X+r*Y)+0*X)+Y*(a*(r*X-a*Y)+0*Y)+Z*(0*Z)=_
    linear_combination -a^2*hk
  have hη : -(v 0*v 0)+v 1*v 1+v 2*v 2+v 3*v 3= -(r^2+a^2)*(r^2+a^2*Z^2) := by
    change -((r^2+a^2)*(r^2+a^2))+(-a*(a*X+r*Y)+0*X)*(-a*(a*X+r*Y)+0*X)+
      (a*(r*X-a*Y)+0*Y)*(a*(r*X-a*Y)+0*Y)+(0*Z)*(0*Z)=_
    linear_combination (a^2*(r^2+a^2))*hk
  change G m a 0 x v v=_
  rw [metric_entries]; change _+ksProfile m a 0 y*_ * _=_
  rw [hη]
  change _+ksProfile m a 0 y*(v 0+ksNull a y 1*v 1+ksNull a y 2*v 2+ksNull a y 3*v 3)*
    (v 0+ksNull a y 1*v 1+ksNull a y 2*v 2+ksNull a y 3*v 3)=_
  rw [hK]; simp only [Matrix.cons_val]; rw [hvk,hp]; ring

private theorem exterior_orbit (m a : ℝ) (hp : IsKerrNewmanBlackHoleParams m a 0)
    (p : E4) (hpD : p ∈ kerrNewmanDOC m a 0) :
    ∃ z : ℝ → E4, ContDiff ℝ 1 z ∧ z 0=p ∧
      ∀ t, z t ∈ kerrNewmanDOC m a 0 ∧
        matrixBilin (kerrNewmanMetric m a 0 (z t)) (deriv z t) (deriv z t) = -1 := by
  let r := ksRadius a p
  let X₀ := ksNull a p 1
  let Y₀ := ksNull a p 2
  let Z := ksNull a p 3
  let k := Real.sqrt (m^2-a^2-0^2)
  change m+k<r at hpD
  have hk0 : 0≤k := Real.sqrt_nonneg _
  have hk : k^2=m^2-a^2-0^2 := Real.sq_sqrt (by nlinarith [hp.2])
  have hr : 0<r := (add_pos_of_pos_of_nonneg hp.1 hk0).trans hpD
  have hΔ : 0<r^2+a^2-2*m*r := by
    nlinarith only [hk,mul_pos (show 0<r-m-k by linarith) (show 0<r-m+k by linarith)]
  let C := (r^2+a^2-2*m*r)*(r^2+a^2*Z^2)
  let N := 1/Real.sqrt C
  have hC : 0<C := mul_pos hΔ (by positivity)
  have hN : N^2*C=1 := by
    dsimp only [N]
    rw [div_pow, Real.sq_sqrt hC.le]; field_simp [hC.ne']
  let X := fun s : ℝ => X₀*Real.cos (a*N*s)-Y₀*Real.sin (a*N*s)
  let Y := fun s : ℝ => X₀*Real.sin (a*N*s)+Y₀*Real.cos (a*N*s)
  let tm := fun s : ℝ => p 0+(N*(r^2+a^2))*s
  let z := fun s : ℝ => oblate a r (tm s) (X s) (Y s) Z
  have hk' (s) : X s^2+Y s^2+Z^2=1 := by
    have h0 : X₀^2+Y₀^2+Z^2=1 := ks_rel a p hr
    dsimp only [X,Y]
    linear_combination (X₀^2+Y₀^2)*Real.sin_sq_add_cos_sq (a*N*s)+h0
  have hdiff : ContDiff ℝ 1 z := by
    unfold z oblate four
    apply PiLp.contDiff_toLp.comp
    apply contDiff_pi.mpr
    intro i; fin_cases i
    · change ContDiff ℝ 1 tm; dsimp [tm]; fun_prop
    · change ContDiff ℝ 1 (fun s => r*X s-a*Y s); dsimp [X,Y]; fun_prop
    · change ContDiff ℝ 1 (fun s => a*X s+r*Y s); dsimp [X,Y]; fun_prop
    · exact contDiff_const
  have h0 : z 0=p := by
    have hh : z 0=oblate a r (p 0) X₀ Y₀ Z := by simp [z,tm,X,Y]
    rw [hh]; ext i; fin_cases i
    · rfl
    · exact (ks_x1 a p hr).symm
    · exact (ks_x2 a p hr).symm
    · exact (ks_x3 a p hr).symm
  refine ⟨z,hdiff,h0,?_⟩
  intro s
  have hR := (oblate_data a r (tm s) (X s) (Y s) Z hr (hk' s)).1
  refine ⟨?_,?_⟩
  · change m+k<ksRadius a (z s)
    rw [show ksRadius a (z s)=r from hR]; exact hpD
  · let V := velocityShape a r (X s) (Y s) Z 0
    have hl : HasDerivAt (fun w : ℝ => a*N*w) (a*N) s := by
      simpa using (hasDerivAt_id' s).const_mul (a*N)
    have hx : HasDerivAt X (-(a*N)*Y s) s := by
      apply ((hl.cos.const_mul X₀).sub (hl.sin.const_mul Y₀)).congr_deriv
      dsimp [Y]; ring
    have hy : HasDerivAt Y (a*N*X s) s := by
      apply ((hl.sin.const_mul X₀).add (hl.cos.const_mul Y₀)).congr_deriv
      dsimp [X]; ring
    have ht : HasDerivAt tm (N*(r^2+a^2)) s := by
      simpa only [tm,mul_one] using (((hasDerivAt_id' s).const_mul (N*(r^2+a^2))).const_add (p 0))
    have hd : HasDerivAt z (N • V) s := by
      apply (four_deriv ht ((hx.const_mul r).sub (hy.const_mul a))
        ((hx.const_mul a).add (hy.const_mul r)) (hasDerivAt_const s (r*Z))).congr_deriv
      ext i; fin_cases i <;> simp [V,velocityShape,four,bigP,smul_eq_mul] <;> ring
    have hv : matrixBilin (kerrNewmanMetric m a 0 (z s)) V V = -C :=
      orbit_norm m a r (tm s) (X s) (Y s) Z hr (hk' s)
    rw [hd.deriv]
    simp only [map_smul,ContinuousLinearMap.smul_apply,smul_eq_mul,hv]
    linear_combination -hN

private theorem basis_sum (v : E4) : ∑ i, v i • coordBasis i=v := by
  ext j
  fin_cases j <;> simp [Fin.sum_univ_four,coordBasis]

private theorem evaluate_in_basis (B : E4 →L[ℝ] E4 →L[ℝ] ℝ) (L : E4 →L[ℝ] E4) (v : E4) :
    matrixBilin (fun i j => B (L (coordBasis i)) (L (coordBasis j))) v v = B (L v) (L v) := by
  have hl : L v = ∑ i, v i • L (coordBasis i) := by
    calc
      L v = L (∑ i, v i • coordBasis i) := congrArg L (basis_sum v).symm
      _ = _ := by simp only [map_sum,map_smul]
  let M : Matrix (Fin 4) (Fin 4) ℝ := Matrix.of fun i j => B (L (coordBasis i)) (L (coordBasis j))
  change Matrix.toLinearMap₂' ℝ M (WithLp.ofLp v) (WithLp.ofLp v)=B (L v) (L v)
  rw [hl,Matrix.toLinearMap₂'_apply M (WithLp.ofLp v) (WithLp.ofLp v)]
  simp only [M,Matrix.of_apply,map_sum,map_smul,ContinuousLinearMap.sum_apply,ContinuousLinearMap.smul_apply,
    smul_eq_mul,Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

private theorem pullback_value {a : ℝ} (g : BilinField (U a)) (Ψ : E4 → U a) (y v : E4) :
    matrixBilin (pullbackCoeffs g Ψ y) v v =
      g (Ψ y) (mfderiv I4 I4 Ψ y v) (mfderiv I4 I4 Ψ y v) :=
  evaluate_in_basis (g (Ψ y)) (mfderiv I4 I4 Ψ y) v

private theorem radius_along (a : ℝ) (γ : ℝ → U a) (hγ : ContMDiff 𝓘(ℝ,ℝ) I4 1 γ) (s : ℝ) :
    HasDerivAt (fun t => ksRadius a (γ t).val)
      (fderiv ℝ (ksRadius a) (γ s).val (velocity γ s)) s := by
  let z : ℝ → E4 := Subtype.val ∘ γ
  have hval : ContMDiff I4 I4 1 (Subtype.val : U a → E4) := contMDiff_subtype_val
  have hz : ContDiff ℝ 1 z := (hval.comp hγ).contDiff
  have hd := (hz.differentiable_one s).hasDerivAt
  have he := ambient_velocity a γ hγ s (deriv z s) hd
  rw [he]
  exact (ksRadius_differentiableAt a (z s) (γ s).property).hasFDerivAt.comp_hasDerivAt s hd

theorem proved (μ b : ℝ) (hp : IsKerrNewmanBlackHoleParams μ b 0) :
    ¬ IsKerrNewmanDOC (kerrNewmanMetricField (5/2) 2 0) (kerrNewmanFieldField 2 0)
      {x : kerrNewmanSpacetime 2 | 1 < ksRadius 2 x.val} μ b 0 := by
  rintro ⟨_,Ψ,⟨χ,hΨ,hχ,hleft,hright,hsm,_⟩,hcoeff⟩
  let y := oblate 2 2 0 0 0 1
  have hy : ksRadius 2 y=2 := (oblate_data 2 2 0 0 0 1 (by norm_num) (by norm_num)).1
  let x : U 2 := ⟨y,by change 0<ksRadius 2 y; rw [hy]; norm_num⟩
  let A := {x : U 2 | 1 < ksRadius 2 x.val}
  have hx : x ∈ A := by change 1<ksRadius 2 y; rw [hy]; norm_num
  let p := χ x
  obtain ⟨z,hz,h0,hzD⟩ := exterior_orbit μ b hp p (hχ hx)
  let γ := Ψ ∘ z
  have hop : IsOpen (kerrNewmanDOC μ b 0) := isOpen_lt continuous_const (continuous_ksRadius b)
  have hΨs (s) : ContMDiffAt I4 I4 1 Ψ (z s) :=
    ((hsm (z s) (hzD s).1).contMDiffAt (hop.mem_nhds (hzD s).1)).of_le (by simp)
  have hγ : ContMDiff 𝓘(ℝ,ℝ) I4 1 γ :=
    fun s => (hΨs s).comp s (hz.contMDiff.contMDiffAt)
  have hγ0 : γ 0=x := by change Ψ (z 0)=x; rw [h0]; exact hright hx
  have hA (t) : 1<ksRadius 2 (γ t).val := hΨ (hzD t).1
  have hunit (t) : G (5/2) 2 0 (γ t) (velocity γ t) (velocity γ t)= -1 := by
    have he : (velocity γ t : E4)=mfderiv I4 I4 Ψ (z t) (deriv z t) := by
      unfold velocity γ
      rw [mfderiv_comp t ((hΨs t).mdifferentiableAt (by simp)) (hz.differentiable_one t).mdifferentiableAt]
      have hinner : (mfderiv 𝓘(ℝ,ℝ) I4 z t : ℝ →L[ℝ] E4) 1=deriv z t := by
        rw [mfderiv_eq_fderiv]; rfl
      exact congrArg (fun w : E4 => (mfderiv I4 I4 Ψ (z t) : E4 →L[ℝ] E4) w) hinner
    rw [he]
    change G (5/2) 2 0 (Ψ (z t)) _ _=_
    calc
      _=matrixBilin (pullbackCoeffs (G (5/2) 2 0) Ψ (z t)) (deriv z t) (deriv z t) :=
        (pullback_value (G (5/2) 2 0) Ψ (z t) (deriv z t)).symm
      _=_ := by rw [(hcoeff (z t) (hzD t).1).1]; exact (hzD t).2
  apply no_trapped_line (fun t => ksRadius 2 (γ t).val)
    (fun t => fderiv ℝ (ksRadius 2) (γ t).val (velocity γ t)) (radius_along 2 γ hγ) hA
    (by rw [hγ0]; exact hy)
  exact fun t ht => radial_unit (γ t) (velocity γ t) (hunit t) (hA t) ht
end
end InnerTrappedObservers

namespace OblateChartDecay
open NoHair NoHair.KNE Set Filter
open scoped ContDiff Manifold BigOperators Topology

noncomputable section

open InnerChronology (I4)

open InnerHelix (four)

open InnerTrappedObservers (oblate)

open InnerTrappedObservers (sigma)

open InnerTrappedObservers (bigP)

open InnerTrappedObservers (massTerm)

open InnerTrappedObservers (oblate_data)

private def raw (y : E4) : E4 :=
  four (y 0) (y 1-2*(y 2/spatialRadius y)) (y 2+2*(y 1/spatialRadius y)) (y 3)

private theorem radius_sq (y : E4) : spatialRadius y ^ 2 = y 1 ^ 2+y 2 ^ 2+y 3 ^ 2 :=
  Real.sq_sqrt (by positivity)

private theorem raw_data (y : E4) (hr : 0 < spatialRadius y) :
    ksRadius 2 (raw y)=spatialRadius y ∧ ksNull 2 (raw y)=
      ![1,y 1/spatialRadius y,y 2/spatialRadius y,y 3/spatialRadius y] := by
  let r := spatialRadius y
  have hu : (y 1/r)^2+(y 2/r)^2+(y 3/r)^2=1 := by
    field_simp [show r≠0 from hr.ne']; linear_combination -(radius_sq y)
  have he : raw y=oblate 2 r (y 0) (y 1/r) (y 2/r) (y 3/r) := by
    ext i; fin_cases i <;> simp [raw,oblate,four,r,hr.ne'] <;> field_simp [hr.ne'] <;> ring
  obtain ⟨h1,h2,_⟩ := oblate_data 2 r (y 0) _ _ _ hr hu
  rw [he]; exact ⟨h1,h2⟩

private theorem spatial_smooth (y : E4) (hy : 0 < spatialRadius y) : ContDiffAt ℝ ∞ spatialRadius y := by
  have hn : y 1^2+y 2^2+y 3^2 ≠ 0 := by rw [← radius_sq]; positivity
  unfold spatialRadius
  fun_prop (disch := assumption)

private theorem raw_smooth (y : E4) (hr : 0 < spatialRadius y) : ContDiffAt ℝ ∞ raw y := by
  have hd := spatial_smooth y hr
  have hn := hr.ne'
  apply (contDiffAt_piLp 2).mpr
  intro i
  fin_cases i
  · change ContDiffAt ℝ ∞ (fun w : E4 => w 0) y; fun_prop
  · change ContDiffAt ℝ ∞ (fun w : E4 => w 1-2*(w 2/spatialRadius w)) y; fun_prop (disch := assumption)
  · change ContDiffAt ℝ ∞ (fun w : E4 => w 2+2*(w 1/spatialRadius w)) y; fun_prop (disch := assumption)
  · change ContDiffAt ℝ ∞ (fun w : E4 => w 3) y; fun_prop
open InnerHelix (four_deriv)

private def normCoords (y : E4) := four (1/spatialRadius y) (y 1/spatialRadius y)
  (y 2/spatialRadius y) (y 3/spatialRadius y)
private def rate (z v : E4) := z 1*v 1+z 2*v 2+z 3*v 3
private def ang (z v : E4) (i : Fin 4) := v i-z i*rate z v
private def tangent (z v : E4) := four (-(z 0)*rate z v) (ang z v 1) (ang z v 2) (ang z v 3)
private def bend (z v : E4) := four 0 (-(2*ang z v 2)) (2*ang z v 1) 0
private def jac (z v : E4) := v+z 0 • bend z v
private def eta (v w : E4) : ℝ := -(v 0*w 0)+v 1*w 1+v 2*w 2+v 3*w 3
private def ell (z v : E4) : ℝ := v 0+rate z v
private def amp (z : E4) : ℝ := 5/(1+4*(z 0)^2*(z 3)^2)
private def oblateCorrection (i j : Fin 4) (z : E4) : ℝ :=
  let v := coordBasis i
  let w := coordBasis j
  eta (bend z v) w + eta v (bend z w) + z 0*eta (bend z v) (bend z w) +
    amp z * ell z (jac z v) * ell z (jac z w)

private theorem eta_basis (i j : Fin 4) : eta (coordBasis i) (coordBasis j)=minkowski i j := by
  fin_cases i <;> fin_cases j <;> simp [eta,coordBasis,minkowski]

private theorem resid_smooth (i j : Fin 4) : ContDiff ℝ ∞ (oblateCorrection i j) := by
  have hn (z : E4) : 1+4*(z 0)^2*(z 3)^2 ≠ 0 := by positivity
  unfold oblateCorrection amp ell eta jac bend ang rate four
  simp only [PiLp.add_apply,PiLp.smul_apply,WithLp.ofLp_toLp,Matrix.cons_val,smul_eq_mul]
  fun_prop (disch := exact hn _)

private def line (y v : E4) (s : ℝ) := y+s • v
private theorem line_zero (y v : E4) : line y v 0=y := by simp [line]
private theorem line_deriv (y v : E4) : HasDerivAt (line y v) v 0 := by
  change HasDerivAt (fun s : ℝ => y+s • v) v 0
  simpa only [id_eq,one_smul] using ((hasDerivAt_id (0:ℝ)).smul_const v).const_add y

private theorem along (f : E4 → ℝ) (y v : E4) (hf : DifferentiableAt ℝ f y) :
    HasDerivAt (fun s => f (line y v s)) (fderiv ℝ f y v) 0 := by
  have hh : HasFDerivAt f (fderiv ℝ f y) (line y v 0) := by rw [line_zero]; exact hf.hasFDerivAt
  exact hh.comp_hasDerivAt 0 (line_deriv y v)

private theorem chart_deriv (y v : E4) (hy : 0 < spatialRadius y) :
    HasDerivAt (fun s => normCoords (line y v s))
        ((normCoords y) 0 • tangent (normCoords y) v) 0 ∧
      HasDerivAt (fun s => raw (line y v s)) (jac (normCoords y) v) 0 := by
  let L := line y v
  let r := spatialRadius y
  let z := normCoords y
  have hz : L 0=y := line_zero y v
  have hd (i : Fin 4) : HasDerivAt (fun s => L s i) (v i) 0 :=
    (EuclideanSpace.proj (𝕜 := ℝ) i).hasFDerivAt.comp_hasDerivAt 0 (line_deriv y v)
  have hn : (L 0 1)^2+(L 0 2)^2+(L 0 3)^2 ≠ 0 := by rw [hz,← radius_sq]; positivity
  have hsum := (((hd 1).pow 2).add ((hd 2).pow 2)).add ((hd 3).pow 2)
  have hr : HasDerivAt (fun s => spatialRadius (L s)) (rate z v) 0 := by
    apply (hsum.sqrt hn).congr_deriv
    simp only [Pi.add_apply,Pi.pow_apply,hz]
    change _ / (2*spatialRadius y) = rate z v
    simp [rate,z,normCoords,four]
    field_simp [hy.ne'] <;> ring
  have hn' : spatialRadius (L 0) ≠ 0 := by rw [hz]; exact hy.ne'
  have hi : HasDerivAt (fun s => 1/spatialRadius (L s)) (z 0*(-(z 0)*rate z v)) 0 := by
    apply ((hasDerivAt_const (0:ℝ) 1).div hr hn').congr_deriv
    rw [hz]
    change (0*spatialRadius y-1*rate z v)/spatialRadius y^2 = (1/spatialRadius y)*(-(1/spatialRadius y)*rate z v)
    ring
  have ha (i : Fin 4) (h : i≠0) : HasDerivAt (fun s => L s i/spatialRadius (L s)) (z 0*ang z v i) 0 := by
    apply ((hd i).div hr hn').congr_deriv
    rw [hz]
    have zi : z i=y i/spatialRadius y := by fin_cases i <;> simp_all [z,normCoords,four]
    change _ = (1/spatialRadius y)*(v i-z i*rate z v)
    rw [zi]; field_simp [hy.ne'] <;> ring
  constructor
  · apply (four_deriv hi (ha 1 (by decide)) (ha 2 (by decide)) (ha 3 (by decide))).congr_deriv
    ext i; fin_cases i <;> rfl
  · apply (four_deriv (hd 0) ((hd 1).sub ((ha 2 (by decide)).const_mul 2))
      ((hd 2).add ((ha 1 (by decide)).const_mul 2)) (hd 3)).congr_deriv
    ext i; fin_cases i <;> simp [jac,bend,four,smul_eq_mul] <;> ring

private theorem chart_derivative (ψ : E4 → kerrNewmanSpacetime 2)
    (hψ : ∀ y ∈ exteriorRegion 1, (ψ y).val=raw y) (y : E4) (hy : y∈exteriorRegion 1) (v : E4) :
    mfderiv I4 I4 ψ y v=jac (normCoords y) v := by
  let U := kerrNewmanSpacetime 2
  have hr : 0 < spatialRadius y := zero_lt_one.trans hy
  have hS : IsOpen (exteriorRegion 1) := isOpen_lt continuous_const (by unfold spatialRadius; fun_prop)
  have he : ((Subtype.val : U → E4) ∘ ψ) =ᶠ[𝓝 y] raw := by
    filter_upwards [hS.mem_nhds hy] with w hw
    exact hψ w hw
  have hs : ContMDiffAt I4 I4 ∞ ψ y := by
    apply ContMDiffWithinAt.contMDiffAt (s := exteriorRegion 1) _ (hS.mem_nhds hy)
    apply (ContMDiffWithinAt.subtypeVal_comp_iff U ψ (exteriorRegion 1) y).mp
    exact (raw_smooth y hr).contMDiffAt.contMDiffWithinAt.congr (fun w hw => hψ w hw) (hψ y hy)
  have hval : ContMDiff I4 I4 ∞ (Subtype.val : U → E4) := contMDiff_subtype_val
  have hc := mfderiv_comp y (hval.mdifferentiableAt (by simp) (x := ψ y)) (hs.mdifferentiableAt (by simp))
  have hinc : (mfderiv I4 I4 (Subtype.val : U → E4) (ψ y) : E4 →L[ℝ] E4) =
      ContinuousLinearMap.id ℝ E4 := mfderiv_extChartAt_self (I := I4) (x := ψ y)
  rw [hinc] at hc
  change mfderiv I4 I4 ((Subtype.val : U → E4) ∘ ψ) y=(mfderiv I4 I4 ψ y : E4 →L[ℝ] E4) at hc
  rw [← hc,mfderiv_eq_fderiv,he.fderiv_eq]
  have h := (raw_smooth y hr).differentiableAt (by simp)
  have hraw : HasFDerivAt raw (fderiv ℝ raw y) (line y v 0) := by rw [line_zero]; exact h.hasFDerivAt
  exact (hraw.comp_hasDerivAt 0 (line_deriv y v)).unique (chart_deriv y v hr).2

private theorem metric_entries (x : kerrNewmanSpacetime 2) (v w : E4) :
    kerrNewmanMetricField (5/2) 2 0 x v w = eta v w +
      ksProfile (5/2) 2 0 x.val * (v 0+ksNull 2 x.val 1*v 1+ksNull 2 x.val 2*v 2+ksNull 2 x.val 3*v 3)*
        (w 0+ksNull 2 x.val 1*w 1+ksNull 2 x.val 2*w 2+ksNull 2 x.val 3*w 3) := by
  change Matrix.toLinearMap₂' ℝ (kerrNewmanMetric (5/2) 2 0 x.val) (WithLp.ofLp v) (WithLp.ofLp w) = _
  simp only [Matrix.toLinearMap₂'_apply,smul_eq_mul,kerrNewmanMetric,Fin.sum_univ_four,ksNull_zero]
  simp [minkowski,eta] <;> ring

private theorem coefficients (ψ : E4 → kerrNewmanSpacetime 2) (hψ : ∀ y∈exteriorRegion 1, (ψ y).val=raw y)
    (y : E4) (hy : y∈exteriorRegion 1) (i j : Fin 4) :
    pullbackCoeffs (kerrNewmanMetricField (5/2) 2 0) ψ y i j =
      minkowski i j+(normCoords y) 0*oblateCorrection i j (normCoords y) := by
  let z := normCoords y
  let r := spatialRadius y
  have hr : 0<r := zero_lt_one.trans hy
  obtain ⟨hR,hK⟩ := raw_data y hr
  have hpos : 0<ksRadius 2 (raw y) := hR.symm ▸ hr
  have hF : ksProfile (5/2) 2 0 (raw y)=z 0*amp z := by
    rw [profile_eq _ _ _ _ hpos]
    unfold fA Wf
    rw [hR,hK]
    change (2*(5/2)*r-0^2)*(1/(r^2+2^2*(y 3/r)^2))=(1/r)*(5/(1+4*(1/r)^2*(y 3/r)^2))
    have h1 : r^2+2^2*(y 3/r)^2 ≠ 0 := by positivity
    have h2 : 1+4*(1/r)^2*(y 3/r)^2 ≠ 0 := by positivity
    field_simp [h1,h2,hr.ne'] <;> ring
  let v := coordBasis i
  let w := coordBasis j
  have fact (q : E4) : q 0+ksNull 2 (raw y) 1*q 1+ksNull 2 (raw y) 2*q 2+ksNull 2 (raw y) 3*q 3=ell z q := by
    rw [hK]; dsimp [ell,rate,z,normCoords,four]; ring
  unfold pullbackCoeffs
  rw [chart_derivative ψ hψ y hy,chart_derivative ψ hψ y hy,metric_entries,hψ y hy,hF,fact,fact,← eta_basis]
  change eta (jac z v) (jac z w) + z 0*amp z*ell z (jac z v)*ell z (jac z w)=eta v w+z 0*oblateCorrection i j z
  unfold oblateCorrection
  change _=eta v w+z 0*(eta (bend z v) w+eta v (bend z w)+z 0*eta (bend z v) (bend z w)+amp z*ell z (jac z v)*ell z (jac z w))
  simp only [eta,jac,PiLp.add_apply,PiLp.smul_apply,smul_eq_mul]
  ring

private def derivResidual (i j k : Fin 4) (z : E4) : ℝ :=
  -rate z (coordBasis k)*oblateCorrection i j z + fderiv ℝ (oblateCorrection i j) z (tangent z (coordBasis k))
private theorem derivResidual_cont (i j k : Fin 4) : Continuous (derivResidual i j k) := by
  have hh := resid_smooth i j
  have ht : Continuous (fun z => tangent z (coordBasis k)) := by
    unfold tangent four ang rate
    apply (PiLp.continuous_toLp 2 _).comp
    apply continuous_pi; intro b
    fin_cases b <;> simp only [Matrix.cons_val] <;> fun_prop
  unfold derivResidual
  apply Continuous.add
  · unfold rate; fun_prop
  · exact (hh.continuous_fderiv_apply (by simp)).comp (continuous_id.prodMk ht)

private theorem coeff_partial (ψ : E4 → kerrNewmanSpacetime 2) (hψ : ∀ y∈exteriorRegion 1, (ψ y).val=raw y)
    (y : E4) (hy : y∈exteriorRegion 1) (i j k : Fin 4) :
    coordPartial (fun z => pullbackCoeffs (kerrNewmanMetricField (5/2) 2 0) ψ z i j) k y =
      (normCoords y 0)^2*derivResidual i j k (normCoords y) := by
  let z := normCoords y
  let v := coordBasis k
  let P := fun a : E4 => minkowski i j+normCoords a 0*oblateCorrection i j (normCoords a)
  have hr : 0<spatialRadius y := zero_lt_one.trans hy
  have hS : IsOpen (exteriorRegion 1) := isOpen_lt continuous_const (by unfold spatialRadius; fun_prop)
  have he : (fun z => pullbackCoeffs (kerrNewmanMetricField (5/2) 2 0) ψ z i j) =ᶠ[𝓝 y] P := by
    filter_upwards [hS.mem_nhds hy] with w hw; exact coefficients ψ hψ w hw i j
  have hNorm : ContDiffAt ℝ ∞ normCoords y := by
    have hs := spatial_smooth y hr
    have hn := hr.ne'
    apply (contDiffAt_piLp 2).mpr; intro a
    fin_cases a
    · change ContDiffAt ℝ ∞ (fun w => 1/spatialRadius w) y; fun_prop (disch := assumption)
    · change ContDiffAt ℝ ∞ (fun w : E4 => w 1/spatialRadius w) y; fun_prop (disch := assumption)
    · change ContDiffAt ℝ ∞ (fun w : E4 => w 2/spatialRadius w) y; fun_prop (disch := assumption)
    · change ContDiffAt ℝ ∞ (fun w : E4 => w 3/spatialRadius w) y; fun_prop (disch := assumption)
  have hDiff : DifferentiableAt ℝ P y := by
    apply ContDiffAt.differentiableAt (n:=∞) _ (by simp)
    apply ContDiffAt.add contDiffAt_const
    exact (((EuclideanSpace.proj (𝕜:=ℝ) 0).contDiff.contDiffAt.comp y hNorm).mul
      ((resid_smooth i j).contDiffAt.comp y hNorm))
  have hND := (chart_deriv y v hr).1
  have hC := (EuclideanSpace.proj (𝕜 := ℝ) 0).hasFDerivAt.comp_hasDerivAt 0 hND
  have hZ : normCoords (line y v 0)=z := by rw [line_zero]
  have hd := (resid_smooth i j).differentiable (by simp) (normCoords (line y v 0))
  have hRes := hd.hasFDerivAt.comp_hasDerivAt 0 hND
  have hTotal := (hC.mul hRes).const_add (minkowski i j)
  unfold coordPartial
  rw [he.fderiv_eq]
  have H := (along P y v hDiff).unique hTotal
  rw [hZ] at H
  rw [H]
  simp only [map_smul,smul_eq_mul,Function.comp_apply,line_zero]
  change (z 0*(-(z 0)*rate z v))*oblateCorrection i j z+z 0*(z 0*fderiv ℝ (oblateCorrection i j) z (tangent z v))=
    (z 0)^2*(-rate z v*oblateCorrection i j z+fderiv ℝ (oblateCorrection i j) z (tangent z v))
  ring

private theorem uniform_bound {ι : Type*} [Finite ι] (K : Set E4) (hK : IsCompact K) (f : ι → E4 → ℝ)
    (hf : ∀ i, Continuous (f i)) : ∃ C : ℝ, ∀ i z, z∈K → |f i z| ≤ C := by
  classical
  have bounds (i : ι) : BddAbove ((fun z => |f i z|) '' K) := hK.bddAbove_image (hf i).abs.continuousOn
  choose c hc using bounds
  obtain ⟨C,hC⟩ := (Set.finite_range c).bddAbove
  exact ⟨C,fun i z hz => (hc i ⟨z,hz,rfl⟩).trans (hC ⟨i,rfl⟩)⟩

theorem proved (ψ : E4 → kerrNewmanSpacetime 2)
    (hψ : ∀ y ∈ exteriorRegion 1, (ψ y).val = WithLp.toLp 2
      ![y 0, y 1-2*(y 2/spatialRadius y), y 2+2*(y 1/spatialRadius y), y 3]) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y ∈ exteriorRegion 1, ∀ i j : Fin 4,
      |pullbackCoeffs (kerrNewmanMetricField (5/2) 2 0) ψ y i j - minkowski i j| ≤ C / spatialRadius y ∧
      ∀ k : Fin 4, |coordPartial (fun z => pullbackCoeffs (kerrNewmanMetricField (5/2) 2 0) ψ z i j) k y| ≤
        C / spatialRadius y ^ 2  := by
  let box : Set (Fin 4 → ℝ) := Icc (fun _ => -1) (fun _ => 1)
  let K : Set E4 := WithLp.toLp 2 '' box
  have hK : IsCompact K := (show IsCompact box from isCompact_Icc).image (PiLp.continuous_toLp 2 _)
  have hmem (y : E4) (hy : y∈exteriorRegion 1) : normCoords y∈K := by
    have hr : 0<spatialRadius y := zero_lt_one.trans hy
    have hq : 0 ≤ 1/spatialRadius y := by positivity
    have hq' : 1/spatialRadius y ≤ 1 := (div_le_iff₀ hr).mpr (by simpa using hy.le)
    have hb (i : Fin 4) (hi : i≠0) : |y i/spatialRadius y| ≤ 1 := by
      rw [abs_div,abs_of_pos hr]
      apply (div_le_iff₀ hr).mpr
      rw [one_mul]
      apply (sq_le_sq₀ (abs_nonneg _) hr.le).mp
      rw [sq_abs,radius_sq]
      fin_cases i <;> simp_all <;> nlinarith [sq_nonneg (y 1),sq_nonneg (y 2),sq_nonneg (y 3)]
    refine ⟨WithLp.ofLp (normCoords y),⟨?_,?_⟩,rfl⟩
    · intro i
      fin_cases i
      · change -1≤1/spatialRadius y; linarith
      all_goals exact (abs_le.mp (hb _ (by decide))).1
    · intro i
      fin_cases i
      · exact hq'
      all_goals exact (abs_le.mp (hb _ (by decide))).2
  obtain ⟨C0,h0⟩ := uniform_bound K hK (fun a : Fin 4 × Fin 4 => oblateCorrection a.1 a.2) (fun a => (resid_smooth _ _).continuous)
  obtain ⟨C1,h1⟩ := uniform_bound K hK (fun a : Fin 4 × Fin 4 × Fin 4 => derivResidual a.1 a.2.1 a.2.2)
    (fun a => derivResidual_cont _ _ _)
  let C := max 0 (max C0 C1)
  refine ⟨C,le_max_left _ _,?_⟩
  intro y hy i j
  have hr : 0<spatialRadius y := zero_lt_one.trans hy
  have hz := hmem y hy
  have hq : 0≤1/spatialRadius y := by positivity
  constructor
  · rw [coefficients ψ hψ y hy i j,add_sub_cancel_left,abs_mul]
    change |1/spatialRadius y| * |oblateCorrection i j (normCoords y)| ≤ C/spatialRadius y
    rw [abs_of_nonneg hq]
    calc
      _ ≤ (1/spatialRadius y)*C := mul_le_mul_of_nonneg_left ((h0 (i,j) _ hz).trans ((le_max_left _ _).trans (le_max_right _ _))) hq
      _ = _ := by ring
  · intro k
    rw [coeff_partial ψ hψ y hy i j k,abs_mul,abs_of_nonneg (sq_nonneg _)]
    change (1/spatialRadius y)^2 * |derivResidual i j k (normCoords y)| ≤ C/spatialRadius y^2
    have hh := mul_le_mul_of_nonneg_left ((h1 (i,j,k) _ hz).trans
      ((le_max_right C0 C1).trans (le_max_right 0 _))) (sq_nonneg (1/spatialRadius y))
    calc
      _ ≤ (1/spatialRadius y)^2*C := hh
      _ = _ := by ring
end
end OblateChartDecay

namespace InnerAsymptoticEnd
open NoHair NoHair.KNE Set Filter
open scoped ContDiff Manifold BigOperators Topology

noncomputable section

open InnerChronology (I4)

open InnerHelix (four)

open InnerTrappedObservers (oblate)

open InnerTrappedObservers (sigma)

open InnerTrappedObservers (bigP)

open InnerTrappedObservers (massTerm)

open InnerTrappedObservers (oblate_data)

open OblateChartDecay (raw)

open OblateChartDecay (radius_sq)

open OblateChartDecay (raw_data)

open OblateChartDecay (spatial_smooth)

open OblateChartDecay (raw_smooth)

open InnerRegularity (radius_smooth)

open InnerRegularity (null_smooth)

private def inverseRaw (z : E4) : E4 :=
  four (z 0) (ksRadius 2 z*ksNull 2 z 1) (ksRadius 2 z*ksNull 2 z 2) (ksRadius 2 z*ksNull 2 z 3)

private theorem inverse_data (z : E4) (hr : 0 < ksRadius 2 z) :
    spatialRadius (inverseRaw z)=ksRadius 2 z ∧ raw (inverseRaw z)=z := by
  let r := ksRadius 2 z
  let k := ksNull 2 z
  have hunit := ks_rel 2 z hr
  have hs : spatialRadius (inverseRaw z)=r := by
    change Real.sqrt ((r*k 1)^2+(r*k 2)^2+(r*k 3)^2)=r
    have h : (r*k 1)^2+(r*k 2)^2+(r*k 3)^2=r^2 := by
      change k 1^2+k 2^2+k 3^2=1 at hunit
      linear_combination r^2*hunit
    rw [h,Real.sqrt_sq hr.le]
  refine ⟨hs,?_⟩
  unfold raw
  rw [hs]
  have h1 := ks_x1 2 z hr
  have h2 := ks_x2 2 z hr
  have h3 := ks_x3 2 z hr
  have hn : r ≠ 0 := hr.ne'
  ext i; fin_cases i
  · rfl
  · change r*k 1-2*(r*k 2/r)=z 1
    rw [show r*k 2/r = k 2 by field_simp]
    exact h1.symm
  · change r*k 2+2*(r*k 1/r)=z 2
    rw [show r*k 1/r=k 1 by field_simp,add_comm]
    exact h2.symm
  · exact h3.symm

private theorem inverse_after (y : E4) (hr : 0 < spatialRadius y) : inverseRaw (raw y)=y := by
  obtain ⟨hr',hk⟩ := raw_data y hr
  unfold inverseRaw
  rw [hr',hk]
  ext i; fin_cases i <;> simp [four,raw,hr.ne'] <;> field_simp [hr.ne']

private theorem inverse_smooth (z : E4) (hz : 0 < ksRadius 2 z) : ContDiffAt ℝ ∞ inverseRaw z := by
  have hr := radius_smooth 2 z hz
  have h1 := null_smooth 2 z hz 1
  have h2 := null_smooth 2 z hz 2
  have h3 := null_smooth 2 z hz 3
  apply (contDiffAt_piLp 2).mpr
  intro i
  fin_cases i
  · change ContDiffAt ℝ ∞ (fun w : E4 => w 0) z; fun_prop
  · exact hr.mul h1
  · exact hr.mul h2
  · exact hr.mul h3

theorem proved (φ : ℝ → kerrNewmanSpacetime 2 → kerrNewmanSpacetime 2)
    (hφ : ∀ s x, (φ s x).val = x.val+s • coordBasis 0) :
    ∃ E : AsymptoticallyFlatEnd (kerrNewmanMetricField (5/2) 2 0) (kerrNewmanFieldField 2 0) φ,
      E.region = {x : kerrNewmanSpacetime 2 | 1 < ksRadius 2 x.val}  := by
  classical
  let U := kerrNewmanSpacetime 2
  let A := {x : U | 1<ksRadius 2 x.val}
  let S := exteriorRegion 1
  have hS : IsOpen S := isOpen_lt continuous_const (by unfold spatialRadius; fun_prop)
  have hA : IsOpen A := isOpen_lt continuous_const ((continuous_ksRadius 2).comp continuous_subtype_val)
  let base := four 0 0 0 2
  have hbase : 0<spatialRadius base := by change 0 < Real.sqrt ((0:ℝ)^2+0^2+2^2); norm_num
  let x₀ : U := ⟨raw base,by change 0<ksRadius 2 (raw base); rwa [(raw_data base hbase).1]⟩
  let ψ (y : E4) : U := if h : raw y ∈ U then ⟨raw y,h⟩ else x₀
  have hv (y : E4) (hy : y ∈ S) : (ψ y).val=raw y := by
    have hr : 0<spatialRadius y := zero_lt_one.trans hy
    have hU : raw y∈U := by change 0<ksRadius 2 (raw y); rwa [(raw_data y hr).1]
    simp [ψ,hU]
  let χ (x : U) := inverseRaw x.val
  have hψ : MapsTo ψ S A := by
    intro y hy
    change 1<ksRadius 2 (ψ y).val
    rw [hv y hy,(raw_data y (zero_lt_one.trans hy)).1]; exact hy
  have hχ : MapsTo χ A S := by
    intro x hx
    change 1<spatialRadius (inverseRaw x.val)
    rwa [(inverse_data x.val x.property).1]
  have hl : LeftInvOn χ ψ S := by
    intro y hy
    change inverseRaw (ψ y).val=y
    rw [hv y hy]
    exact inverse_after y (zero_lt_one.trans hy)
  have hr : RightInvOn χ ψ A := by
    intro x hx
    apply Subtype.ext
    rw [hv _ (hχ hx)]
    exact (inverse_data x.val x.property).2
  have hImg : ψ '' S=A := Subset.antisymm hψ.image_subset (fun x hx => ⟨χ x,hχ hx,hr hx⟩)
  have hsψ : ContMDiffOn I4 I4 ∞ ψ S := by
    intro y hy
    apply (ContMDiffWithinAt.subtypeVal_comp_iff U ψ S y).mp
    exact (raw_smooth y (zero_lt_one.trans hy)).contMDiffAt.contMDiffWithinAt.congr
      (fun z hz => hv z hz) (hv y hy)
  have hsχ : ContMDiffOn I4 I4 ∞ χ A := by
    intro x _
    exact ((inverse_smooth x.val x.property).contMDiffAt.comp x
      (contMDiff_subtype_val (U := U)).contMDiffAt).contMDiffWithinAt
  obtain ⟨C,hC,hb⟩ := OblateChartDecay.proved ψ hv
  let E : AsymptoticallyFlatEnd (kerrNewmanMetricField (5/2) 2 0) (kerrNewmanFieldField 2 0) φ := {
    R := 1, ψ := ψ, C := C, R_pos := zero_lt_one
    diffeo := by change IsDiffeoOnto ψ S (ψ '' S); rw [hImg]; exact ⟨χ,hψ,hχ,hl,hr,hsψ,hsχ⟩
    isOpen_image := by change IsOpen (ψ '' S); rwa [hImg]
    equivariant := by
      intro t y hy
      have hsp : spatialRadius (y+t • coordBasis 0)=spatialRadius y := by
        unfold spatialRadius
        rw [time_shift _ _ 1 (by decide),time_shift _ _ 2 (by decide),time_shift _ _ 3 (by decide)]
      have hy' : y+t • coordBasis 0∈S := by change 1<spatialRadius _; rwa [hsp]
      apply Subtype.ext
      rw [hφ,hv _ hy',hv _ hy]
      unfold raw
      rw [hsp]
      ext i; fin_cases i <;> simp [four,coordBasis]
    metric_decay := fun y hy i j => (hb y hy i j).1
    metric_deriv_decay := fun y hy i j k => (hb y hy i j).2 k
    field_decay := by
      intro y hy i j
      have zeroField (x : U) : kerrNewmanFieldField 2 0 x=0 := by
        have hm : kerrNewmanField 2 0 x.val=0 := by ext μ ν; simp [kerrNewmanField,coordPartial,kerrNewmanPotential]
        change matrixBilin (kerrNewmanField 2 0 x.val)=0
        rw [hm]; ext v w; simp [matrixBilin,Matrix.toLinearMap₂'_apply]
      simp [pullbackCoeffs,zeroField,div_nonneg hC (sq_nonneg _)] }
  exact ⟨E,hImg⟩
end
end InnerAsymptoticEnd

section
noncomputable def innerRadialRegion (m a e : ℝ) : Set NoHair.E4 :=
  {z | max 1 (e^2/(2*m)) < NoHair.ksRadius a z}


open NoHair NoHair.KNE Set Filter
open OAI.WeakMTWGlobalSupport OAI.WeakMTWGlobalSupport.CoordinateGeometry
open OAI.WeakMTWGlobalSupport.NormalNeighborhood NoHair.PseudoNormal
open scoped ContDiff Manifold BigOperators Topology

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 270000

/-! The time and signed-energy tests for regular normal geodesics in the Kerr–Newman exterior. -/
namespace InnerRadialGeodesics
noncomputable section

abbrev U (a : ℝ) := kerrNewmanSpacetime a
abbrev D (m a e : ℝ) := (Subtype.val : U a → E4) ⁻¹' innerRadialRegion m a e
abbrev I4 := 𝓘(ℝ, E4)
abbrev G (m a e : ℝ) := kerrNewmanMetricField m a e
def timeComponent (v : E4) : ℝ := v 0
private def kEval (a : ℝ) (z u : E4) := ∑ i, ksNull a z i * u i

private theorem metric_formula (m a e : ℝ) (x : U a) (v w : E4) :
    G m a e x v w = -(v 0*w 0) + v 1*w 1 + v 2*w 2 + v 3*w 3
      + ksProfile m a e x.val * kEval a x.val v * kEval a x.val w := by
  change Matrix.toLinearMap₂' ℝ (kerrNewmanMetric m a e x.val) (WithLp.ofLp v) (WithLp.ofLp w) = _
  simp only [Matrix.toLinearMap₂'_apply, smul_eq_mul, kerrNewmanMetric, kEval, Fin.sum_univ_four]
  simp [minkowski] <;> ring

theorem exterior_profile (m a e : ℝ) (hp : IsKerrNewmanBlackHoleParams m a e)
    (x : U a) (hx : x ∈ D m a e) : 0 ≤ ksProfile m a e x.val := by
  change max 1 (e^2/(2*m)) < ksRadius a x.val at hx
  have hm := hp.1
  have h2m : 0 < 2*m := by linarith
  have hraw := (div_lt_iff₀ h2m).mp ((le_max_right 1 (e^2/(2*m))).trans_lt hx)
  have hnum : 0 ≤ 2*m*ksRadius a x.val - e^2 := by nlinarith only [hraw]
  unfold ksProfile
  exact div_nonneg (mul_nonneg (sq_nonneg _) hnum) (by positivity)

private theorem spatial_squares (m a e : ℝ) (x : U a) (hf : 0 ≤ ksProfile m a e x.val)
    (v : E4) (hv : G m a e x v v ≤ 0) :
    (v 1)^2 + (v 2)^2 + (v 3)^2 ≤ (v 0)^2 := by
  rw [metric_formula] at hv
  nlinarith only [hv, mul_nonneg hf (sq_nonneg (kEval a x.val v))]

private theorem spatial_kernel (m a e : ℝ) (x : U a) (hf : 0 ≤ ksProfile m a e x.val)
    (v : E4) (h0 : v 0 = 0) : 0 ≤ G m a e x v v := by
  rw [metric_formula, h0]
  nlinarith only [sq_nonneg (v 1), sq_nonneg (v 2), sq_nonneg (v 3),
    mul_nonneg hf (sq_nonneg (kEval a x.val v))]

theorem cone_estimates (m a e : ℝ) (x : U a) (hf : 0 ≤ ksProfile m a e x.val)
    (v w : E4) (hv : v ≠ 0) (hvv : G m a e x v v ≤ 0) (hvw : G m a e x v w < 0)
    (hww : G m a e x w w < 0) :
    (∀ i, |v i| ≤ |v 0|) ∧ 0 < (v 0)*(w 0) := by
  have hs := spatial_squares m a e x hf v hvv
  have hb (i : Fin 4) : |v i| ≤ |v 0| := by
    apply (sq_le_sq₀ (abs_nonneg _) (abs_nonneg _)).mp
    rw [sq_abs, sq_abs]
    fin_cases i <;> simp <;> nlinarith only [hs, sq_nonneg (v 1), sq_nonneg (v 2), sq_nonneg (v 3)]
  have hv0 : v 0 ≠ 0 := by
    intro h
    apply hv
    ext i
    exact abs_nonpos_iff.mp (by simpa only [h, abs_zero] using hb i)
  refine ⟨hb, ?_⟩
  by_contra! hprod
  have hkernel := spatial_kernel m a e x hf ((w 0) • v - (v 0) • w)
    (by simp [smul_eq_mul, mul_comm])
  have hsym : G m a e x w v = G m a e x v w := by rw [metric_formula, metric_formula]; ring
  let A := matrixBilin (kerrNewmanMetric m a e x.val)
  change 0 ≤ A ((w 0) • v - (v 0) • w) ((w 0) • v - (v 0) • w) at hkernel
  change A w v = A v w at hsym
  change A w w < 0 at hww
  change A v v ≤ 0 at hvv
  change A v w < 0 at hvw
  simp only [map_sub, map_smul, ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
    smul_eq_mul, hsym] at hkernel
  nlinarith only [hkernel, mul_nonpos_of_nonneg_of_nonpos (sq_nonneg (w 0)) hvv,
    mul_neg_of_pos_of_neg (sq_pos_iff.mpr hv0) hww, mul_nonneg_of_nonpos_of_nonpos hprod hvw.le]

open InnerRegularity (matrix_eval radius_smooth null_smooth)

theorem ambient_velocity (a : ℝ) (γ : ℝ → U a) (hγ : ContMDiff 𝓘(ℝ,ℝ) I4 1 γ)
    (s : ℝ) (v : E4) (hd : HasDerivAt (fun t => (γ t).val) v s) : (velocity γ s : E4) = v :=
  InnerChronology.ambient_velocity a γ hγ s v hd

export NoHair.CausalJoining (J F W W_on W_cont)

abbrev S (m a e : ℝ) := innerRadialRegion m a e
theorem openS (m a e : ℝ) : IsOpen (S m a e) := isOpen_lt continuous_const (continuous_ksRadius a)
theorem inU (m a e : ℝ) (hp : IsKerrNewmanBlackHoleParams m a e) {z : E4}
    (h : z∈S m a e) : z∈U a := by
  change max 1 (e^2/(2*m)) < ksRadius a z at h
  exact zero_lt_one.trans ((le_max_left 1 _).trans_lt h)

private theorem smooth_scalar_multiple {X Y : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {f : X → ℝ} {x : X} (hf : ContDiffAt ℝ ∞ f x) (v : Y) :
    ContDiffAt ℝ ∞ (fun z => f z • v) x := hf.smul_const v

set_option backward.defeqAttrib.useBackward true in
theorem field_smooth (m a e : ℝ) (hp : IsKerrNewmanBlackHoleParams m a e) :
    ContDiffOn ℝ ∞ (F m a e) (S m a e) := by
  let P (i : Fin 4) := EuclideanSpace.proj (𝕜:=ℝ) i
  have heP (i : Fin 4) (v : E4) : P i v = v i := rfl
  let B (i j : Fin 4) := (P i).smulRight (P j)
  have he (y : E4) : F m a e y = ∑ i, ∑ j, (kerrNewmanMetric m a e y i j) • B i j := by
    apply ContinuousLinearMap.ext
    intro v
    apply ContinuousLinearMap.ext
    intro w
    simp only [F,matrix_eval,ContinuousLinearMap.sum_apply,ContinuousLinearMap.smul_apply,
      smul_eq_mul,B,ContinuousLinearMap.smulRight_apply,heP]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  intro y hy
  have hy' : 0 < ksRadius a y := inU m a e hp hy
  apply ContDiffAt.contDiffWithinAt
  rw [show F m a e = fun z => ∑ i, ∑ j, (kerrNewmanMetric m a e z i j) • B i j from funext he]
  apply ContDiffAt.sum
  intro i _
  apply ContDiffAt.sum
  intro j _
  have hcoeff : ContDiffAt ℝ ∞ (fun z : E4 => kerrNewmanMetric m a e z i j) y := by
    have hR := radius_smooth a y hy'
    have hi := null_smooth a y hy' i
    have hj := null_smooth a y hy' j
    have hd := (ks_den_pos a y hy').ne'
    unfold kerrNewmanMetric ksProfile
    fun_prop (disch := assumption)
  first
  | exact smooth_scalar_multiple (Y:=MetricTensor E4) hcoeff (B i j)
  | convert! smooth_scalar_multiple (Y:=MetricTensor E4) hcoeff (B i j) using 1
  | let L : ℝ →L[ℝ] MetricTensor E4 := ContinuousLinearMap.toSpanSingleton ℝ (B i j)
    have hL := ContinuousLinearMap.contDiff (𝕜:=ℝ) (E:=ℝ) (F:=MetricTensor E4) (n:=∞) L
    exact hL.contDiffAt.comp (f:=fun z : E4 => kerrNewmanMetric m a e z i j) y hcoeff

theorem field_sym (m a e : ℝ) (hp : IsKerrNewmanBlackHoleParams m a e) {z : E4}
    (hz : z∈S m a e) (v w : E4) : F m a e z v w=F m a e z w v := by
  let x : U a := ⟨z,inU m a e hp hz⟩
  change G m a e x v w=G m a e x w v
  rw [metric_formula,metric_formula]; ring

theorem field_inv (m a e : ℝ) (hp : IsKerrNewmanBlackHoleParams m a e) {z : E4}
    (hz : z∈S m a e) : (F m a e z).IsInvertible := by
  let x : U a := ⟨z,inU m a e hp hz⟩
  obtain ⟨b,hb⟩ := InnerRegularity.lorentz m a e x
  let M := F m a e z
  change ∀ i j, M (b i) (b j) = minkowski i j at hb
  have hi : Function.Injective M := by
    apply (injective_iff_map_eq_zero M).mpr
    intro v hv
    have hs : (∑ i, b.repr v i • b i) = v := b.sum_repr v
    have hw (j : Fin 4) : (∑ i, b.repr v i * minkowski i j)=0 := by
      have eq := congrArg (fun L : E4 →L[ℝ] ℝ => L (b j)) hv
      change M v (b j)=0 at eq
      rw [←hs] at eq
      simpa only [map_sum,map_smul,ContinuousLinearMap.sum_apply,ContinuousLinearMap.smul_apply,smul_eq_mul,hb] using eq
    have h0 (i : Fin 4) : b.repr v i = 0 := by
      have h := hw i
      fin_cases i <;> simpa [minkowski,Fin.sum_univ_four] using h
    rw [←hs]
    simp [h0]
  have hdim : Module.finrank ℝ E4=Module.finrank ℝ (E4→L[ℝ]ℝ) := (InnerProductSpace.toDual ℝ E4).toLinearEquiv.finrank_eq
  have hs : Function.Surjective M := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hi
  exact ⟨ContinuousLinearEquiv.ofBijective M (LinearMap.ker_eq_bot.mpr hi) (LinearMap.range_eq_top.mpr hs),rfl⟩

theorem nonzero_time (m a e : ℝ) (hp : IsKerrNewmanBlackHoleParams m a e) {z v : E4}
    (hz : z∈S m a e) (hn : v≠0) (h : F m a e z v v ≤ 0) : v 0≠0 := by
  let x : U a := ⟨z,inU m a e hp hz⟩
  have hs := spatial_squares m a e x (exterior_profile m a e hp x hz) v h
  intro h0
  rw [h0] at hs
  apply hn
  ext i
  fin_cases i
  · exact h0
  · change v 1=0
    apply sq_eq_zero_iff.mp
    nlinarith only [hs,sq_nonneg (v 1),sq_nonneg (v 2),sq_nonneg (v 3)]
  · change v 2=0
    apply sq_eq_zero_iff.mp
    nlinarith only [hs,sq_nonneg (v 1),sq_nonneg (v 2),sq_nonneg (v 3)]
  · change v 3=0
    apply sq_eq_zero_iff.mp
    nlinarith only [hs,sq_nonneg (v 1),sq_nonneg (v 2),sq_nonneg (v 3)]

theorem cone_pair_negative (m a e : ℝ) (hp : IsKerrNewmanBlackHoleParams m a e)
    {z v w : E4} (hz : z∈S m a e) (hvv : F m a e z v v ≤ 0) (hww : F m a e z w w < 0)
    (hvw : 0 < v 0*w 0) : F m a e z v w < 0 := by
  let x : U a := ⟨z,inU m a e hp hz⟩
  have hk := spatial_kernel m a e x (exterior_profile m a e hp x hz) ((w 0) • v - (v 0) • w)
    (by simp [smul_eq_mul,mul_comm])
  let A := F m a e z
  change 0 ≤ A ((w 0) • v - (v 0) • w) ((w 0) • v - (v 0) • w) at hk
  have he : A w v = A v w := field_sym m a e hp hz w v
  simp only [map_sub,map_smul,ContinuousLinearMap.sub_apply,ContinuousLinearMap.smul_apply,smul_eq_mul,he] at hk
  by_contra! h
  change 0 ≤ A v w at h
  have hn := (mul_ne_zero_iff.mp hvw.ne').1
  nlinarith only [hk,mul_nonpos_of_nonneg_of_nonpos (sq_nonneg (w 0)) hvv,
    mul_neg_of_pos_of_neg (sq_pos_iff.mpr hn) hww, mul_nonneg hvw.le h]

theorem sign_prop {L : ℝ} {f : ℝ→ℝ} (hc : ContinuousOn f (Icc 0 L))
    (hne : ∀ s∈Icc 0 L, f s≠0) {u : ℝ} (hu : u∈Icc 0 L) (hpos : 0 < f u) :
    ∀ t∈Icc 0 L, 0 < f t := by
  intro t ht
  by_contra! h
  obtain ⟨r,hr,he⟩ := isPreconnected_Icc.intermediate_value ht hu hc (show (0:ℝ)∈Icc (f t) (f u) from ⟨h,hpos.le⟩)
  exact hne _ hr he

theorem time_deriv {c : ℝ→E4} {v : E4} {t : ℝ} (h : HasDerivAt c v t) :
    HasDerivAt (fun s => c s 0) (v 0) t := by
  let P : E4 →L[ℝ] ℝ := EuclideanSpace.proj 0
  have hh : HasDerivAt (P ∘ c) (P v) t := P.hasFDerivAt.comp_hasDerivAt t h
  exact hh

theorem clock_positive {L o : ℝ} (hL : 0 < L) (c v : ℝ→E4)
    (hc : ∀ t∈Icc 0 L, HasDerivAt c (v t) t) (hv : ContinuousOn v (Icc 0 L))
    (hne : ∀ t∈Icc 0 L, v t 0≠0) (hdisp : 0 < o*(c L 0-c 0 0)) :
    ∀ t∈Icc 0 L, 0 < o*v t 0 := by
  let d (t : ℝ) := o*(c t 0)
  have hd (t : ℝ) (ht : t∈Icc 0 L) : HasDerivAt d (o*v t 0) t :=
    (time_deriv (hc t ht)).const_mul o
  have hco : ContinuousOn d (Icc 0 L) := fun t ht => (hd t ht).continuousAt.continuousWithinAt
  obtain ⟨t,ht,he⟩ := exists_hasDerivAt_eq_slope d (fun s => o*v s 0) hL hco (fun s hs => hd s (Ioo_subset_Icc_self hs))
  have htd : 0 < o*v t 0 := by
    rw [he]
    exact div_pos (by dsimp [d]; linarith only [hdisp]) (sub_pos.mpr hL)
  have ho := (mul_ne_zero_iff.mp hdisp.ne').1
  exact sign_prop (continuousOn_const.mul ((EuclideanSpace.proj (𝕜:=ℝ) 0).continuous.comp_continuousOn hv))
    (fun s hs => mul_ne_zero ho (hne s hs)) (Ioo_subset_Icc_self ht) htd

theorem common_sign {o u v : ℝ} (h1 : 0 < o*u) (h2 : 0 < o*v) : 0 < u*v := by
  rcases mul_pos_iff.mp h1 with h|h <;> rcases mul_pos_iff.mp h2 with k|k
  · exact mul_pos h.2 k.2
  · linarith [h.1,k.1]
  · linarith [h.1,k.1]
  · exact mul_pos_of_neg_of_neg h.2 k.2

private theorem fit_clock {A : Set ℝ} (hA : IsOpen A) {L : ℝ} (hL : 0 < L) (hS : Icc 0 L⊆A) :
    ∃ f : ℝ→ℝ, ContDiff ℝ 1 f ∧ (∀ t, f t∈A) ∧ ∀ t∈Icc 0 L, f=ᶠ[𝓝 t] id := by
  obtain ⟨r₁,hr₁,h₁⟩ := Metric.mem_nhds_iff.mp (hA.mem_nhds (hS (left_mem_Icc.mpr hL.le)))
  obtain ⟨r₂,hr₂,h₂⟩ := Metric.mem_nhds_iff.mp (hA.mem_nhds (hS (right_mem_Icc.mpr hL.le)))
  let r := min r₁ r₂
  have hr : 0 < r := lt_min hr₁ hr₂
  let m := L/2
  let b : ContDiffBump m := ⟨m+r/2,m+r,by dsimp [m]; linarith,by linarith⟩
  let f (t : ℝ) := m+b t*(t-m)
  refine ⟨f,?_,?_,?_⟩
  · exact contDiff_const.add (b.contDiff.mul (contDiff_id.sub contDiff_const))
  · intro t
    have hb : |f t-m| < m+r := by
      by_cases h : b t=0
      · simp [f,h]; dsimp [m]; linarith
      · have hh : t∈Function.support b := h
        rw [b.support_eq,Metric.mem_ball,Real.dist_eq] at hh
        have he : f t-m=b t*(t-m) := by dsimp [f]; ring
        rw [he,abs_mul,abs_of_nonneg b.nonneg]
        exact (mul_le_mul_of_nonneg_right b.le_one (abs_nonneg _)).trans_lt (by simpa using hh)
    have hl := (abs_lt.mp hb).1
    have hu := (abs_lt.mp hb).2
    by_cases h0 : f t < 0
    · apply h₁
      rw [Metric.mem_ball,Real.dist_eq,sub_zero,abs_of_neg h0]
      dsimp [m] at hl; linarith only [hl,min_le_left r₁ r₂]
    · by_cases h1 : L < f t
      · apply h₂
        rw [Metric.mem_ball,Real.dist_eq,abs_of_pos (sub_pos.mpr h1)]
        dsimp [m] at hu; linarith only [hu,min_le_right r₁ r₂]
      · exact hS ⟨le_of_not_gt h0,le_of_not_gt h1⟩
  · intro t ht
    have hh : t∈Metric.ball m b.rIn := by
      rw [Metric.mem_ball,Real.dist_eq,abs_lt]
      change -(L/2+r/2) < t-L/2 ∧ t-L/2 < L/2+r/2
      constructor <;> linarith [ht.1,ht.2]
    filter_upwards [b.eventuallyEq_one_of_mem_ball hh] with z hz
    change b z=1 at hz
    simp [f,hz]

abbrev NF (m a e : ℝ) (x₀ : E4) := NormalFlow (F m a e) (S m a e) x₀
abbrev span {m a e : ℝ} {x₀ : E4} (N : NF m a e x₀) := Icc (0:ℝ) N.time
abbrev Z {m a e : ℝ} {x₀ : E4} (N : NF m a e x₀) (p v : E4) (t : ℝ) := (N.flow (t,(p,v))).1
abbrev Velo {m a e : ℝ} {x₀ : E4} (N : NF m a e x₀) (p v : E4) (t : ℝ) := (N.flow (t,(p,v))).2

theorem radial_data {m a e : ℝ} {x₀ : E4} (N : NF m a e x₀) {p v : E4}
    (hv : (p,v)∈N.normal.source) :
    (∀ t∈span N, Z N p v t∈S m a e ∧ HasDerivAt (Z N p v) (Velo N p v t) t) ∧
    ContinuousOn (Velo N p v) (span N) ∧ Z N p v 0=p ∧ Velo N p v 0=v := by
  have h0 := N.initial (p,v) (N.source_stays (p,v) hv 0 ⟨le_rfl,N.time_pos.le⟩)
  refine ⟨fun t ht => ⟨(N.ode _ (N.source_stays _ hv t ht)).1,?_⟩,?_,congrArg Prod.fst h0,congrArg Prod.snd h0⟩
  · exact (N.ode _ (N.source_stays _ hv t ht)).2.fst
  · exact (N.flow_smooth.continuousOn.comp (continuous_id.prodMk continuous_const).continuousOn (N.source_stays (p,v) hv)).snd

private theorem radial_nonzero {m a e : ℝ} (hp : IsKerrNewmanBlackHoleParams m a e) {x₀ : E4}
    (N : NF m a e x₀) {p v : E4} (hv : (p,v)∈N.normal.source) (hn : v≠0) {t : ℝ} (ht : t∈span N) :
    Velo N p v t≠0 := by
  intro hbad
  let f := geodesicSpray (F m a e)
  let u (s : ℝ) := N.flow (t-s,(p,v))
  let y := N.flow (t,(p,v))
  have htime {s : ℝ} (hs : s∈Icc 0 t) : t-s∈span N := ⟨sub_nonneg.mpr hs.2,by linarith [ht.2,hs.1]⟩
  have hdu (s : ℝ) (hs : s∈Icc 0 t) : HasDerivAt u (-f (u s)) s := by
    simpa [u,f,Function.comp_def] using ((N.ode _ (N.source_stays (p,v) hv _ (htime hs))).2.scomp s ((hasDerivAt_id s).const_sub t))
  have hy : f y=0 := by
    change (y.2,-OAI.WeakMTWGlobalSupport.CoordinateGeometry.christoffel (F m a e) y.1 y.2 y.2) = 0
    change y.2=0 at hbad
    simp [hbad]
  have hsmooth := contDiffOn_geodesicSpray_of_invertible (openS m a e) (field_smooth m a e hp) (fun z hz => field_inv m a e hp hz)
  have hz : EqOn u (fun _=>y) (Icc 0 t) := by
    apply FlowLinearization.unique_Icc (f:=fun z => -f z) (fun s hs => (hdu s hs).continuousAt.continuousWithinAt) continuousOn_const
    · intro z hz
      have hz' : z∈(S m a e) ×ˢ (univ : Set E4) := by
        rcases hz with ⟨s,hs,rfl⟩|⟨_,_,rfl⟩
        · exact ⟨(N.ode _ (N.source_stays (p,v) hv _ (htime hs))).1,mem_univ _⟩
        · exact ⟨(N.ode _ (N.source_stays (p,v) hv t ht)).1,mem_univ _⟩
      exact (((hsmooth z hz').contDiffAt (((openS m a e).prod isOpen_univ).mem_nhds hz')).of_le (by simp)).neg
    · exact fun s hs => (hdu s hs).hasDerivWithinAt
    · intro s _
      simpa only [hy,neg_zero] using hasDerivWithinAt_const s (Icc (0:ℝ) t) y
    · simp [u,y]
  have h := congrArg Prod.snd (hz (right_mem_Icc.mpr ht.1))
  have h0 := (radial_data N hv).2.2.2
  apply hn
  calc
    v = Velo N p v 0 := h0.symm
    _ = Velo N p v t := by simpa only [u,y,sub_self] using h
    _ = 0 := hbad

theorem radial_future (m a e : ℝ) (hp : IsKerrNewmanBlackHoleParams m a e)
    (T : VecField (U a)) (hT : IsTimeOrientation (G m a e) T) {x₀ : E4} (N : NF m a e x₀)
    (p q : U a) (htarget : (p.val,q.val)∈N.normal.target)
    (hE : initialEnergy N p.val q.val ≤ 0)
    (ho : 0 ≤ (q.val 0-p.val 0)*timeComponent (T p)) : q∈causalFuture (G m a e) T (D m a e) p := by
  by_cases hdiag : q=p
  · exact Or.inl (mem_singleton_iff.mpr hdiag)
  let v := logVec N p.val q.val
  let R := Z N p.val v
  let d := Velo N p.val v
  let o := timeComponent (T p)
  have hv : (p.val,v)∈N.normal.source := (N.normalAt p.val).map_target htarget
  have hlast : R N.time = q.val := by
    simpa only [N.normalAt_apply,R,Z,v,logVec] using (N.normalAt p.val).right_inv htarget
  have hvne : v≠0 := by
    intro hv0
    have hh : (p.val,(0:E4))∈N.normal.source := hv0 ▸ hv
    have he := normalAt_zero_of_invertible N (openS m a e) (field_smooth m a e hp)
      (fun z hz => field_inv m a e hp hz) hh
    apply hdiag
    apply Subtype.ext
    calc
      q.val = N.normalAt p.val v := ((N.normalAt p.val).right_inv htarget).symm
      _ = p.val := hv0 ▸ he
  obtain ⟨hR,hdc,hfirst,_⟩ := radial_data N hv
  have henergy (t : ℝ) (ht : t∈span N) : F m a e (R t) (d t) (d t) ≤ 0 :=
    (flow_energy N (openS m a e) (field_smooth m a e hp) (fun _ hz => field_sym m a e hp hz)
      (fun _ hz => field_inv m a e hp hz) hv ht).trans_le hE
  have hdn (t : ℝ) (ht : t∈span N) := radial_nonzero hp N hv hvne ht
  have hdt (t : ℝ) (ht : t∈span N) : d t 0≠0 := nonzero_time m a e hp (hR _ ht).1 (hdn t ht) (henergy t ht)
  have h₀ : (0:ℝ)∈span N := ⟨le_rfl,N.time_pos.le⟩
  have hpS := N.base_mem hv
  have hor : o≠0 := by
    apply nonzero_time m a e hp hpS _ (hT.2 p).le
    intro h
    have hh := hT.2 p
    change (T p : E4)=0 at h
    change F m a e p.val (T p : E4) (T p : E4) < 0 at hh
    simp [h] at hh
  have hdiff (s : ℝ) (hs : s∈span N) : HasDerivAt (fun t => R t 0) (d s 0) s :=
    time_deriv (hR s hs).2
  have hstrict : 0 < o*(R N.time 0-R 0 0) := by
    have h0' : R 0=p.val := hfirst
    have hs := exists_hasDerivAt_eq_slope (fun t => R t 0) (fun t => d t 0) N.time_pos
      (fun t ht => (hdiff t ht).continuousAt.continuousWithinAt) (fun t ht => hdiff t (Ioo_subset_Icc_self ht))
    obtain ⟨t,ht,he⟩ := hs
    have hdne : R N.time 0 - R 0 0 ≠ 0 := fun hh => hdt t (Ioo_subset_Icc_self ht) (by simpa [hh] using he)
    apply lt_of_le_of_ne _ ((mul_ne_zero hor hdne).symm)
    rw [hlast,h0',mul_comm]
    exact ho
  have hsign := clock_positive N.time_pos R d (fun s hs => (hR s hs).2) hdc hdt hstrict
  have horient (s : ℝ) (hs : s∈span N) : 0 < o*(W a T (R s)) 0 := by
    have hc : ContinuousOn (fun t => o*(W a T (R t)) 0) (span N) := by
      intro t ht
      let z : U a := ⟨R t,inU m a e hp (hR t ht).1⟩
      have hz : ContinuousAt (W a T) (R t) := W_cont m a e T hT z
      have hr : ContinuousAt R t := (hR t ht).2.continuousAt
      have ht' : ContinuousAt (fun s => W a T (R s)) t := hz.comp (f:=R) hr
      let proj : E4 →L[ℝ] ℝ := EuclideanSpace.proj 0
      have hh : ContinuousAt (fun s => proj (W a T (R s))) t :=
        proj.continuous.continuousAt.comp (f:=fun s => W a T (R s)) ht'
      exact (continuousAt_const.mul hh).continuousWithinAt
    have hn (t : ℝ) (ht : t∈span N) : o*(W a T (R t)) 0≠0 := by
      let z : U a := ⟨R t,inU m a e hp (hR t ht).1⟩
      have hg := hT.2 z
      change F m a e (R t) (T z : E4) (T z : E4) < 0 at hg
      have he : W a T (R t)=(T z:E4) := W_on a T z
      rw [he]
      exact mul_ne_zero hor (nonzero_time m a e hp (hR t ht).1 (fun hh => by simp [hh] at hg) hg.le)
    apply sign_prop hc hn h₀ _ s hs
    change 0 < o*(W a T (R 0)) 0
    rw [show R 0=p.val from hfirst,W_on]
    exact mul_self_pos.mpr hor
  let A : Set ℝ := {s | (s,(p.val,v))∈N.domain}
  have hA : IsOpen A := N.domain_open.preimage (continuous_id.prodMk continuous_const)
  obtain ⟨f,hf,hfA,hfe⟩ := fit_clock hA N.time_pos (N.source_stays (p.val,v) hv)
  let γ (t : ℝ) : U a := ⟨R (f (N.time*t)),inU m a e hp (N.ode _ (hfA _)).1⟩
  have hc : ContDiff ℝ 1 (Subtype.val ∘ γ) := by
    apply contDiff_iff_contDiffAt.mpr
    intro t
    let param (u : ℝ) : ℝ×(E4×E4) := (f (N.time*u),(p.val,v))
    have hparam : ContDiff ℝ 1 param := (hf.comp (contDiff_const.mul contDiff_id)).prodMk contDiff_const
    have hh : ContDiffAt ℝ 1 N.flow (param t) :=
      ((N.flow_smooth _ (hfA (N.time*t))).contDiffAt (N.domain_open.mem_nhds (hfA (N.time*t)))).of_le
        (show (1:ℕ∞ω) ≤ ∞ from WithTop.coe_le_coe.mpr le_top)
    have hh' : ContDiffAt ℝ 1 (N.flow ∘ param) t := hh.comp (f:=param) t hparam.contDiffAt
    exact hh'.fst
  have hγ : ContMDiff 𝓘(ℝ,ℝ) I4 1 γ := fun s =>
    (ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff γ univ s).mp (hc.contMDiff s)
  have eqF (s : ℝ) (hs : s∈span N) : f s=s := (hfe s hs).eq_of_nhds
  refine Or.inr ⟨γ,⟨hγ,?_⟩,Subtype.ext ?_,Subtype.ext ?_⟩
  · intro s hs
    have hts : N.time*s∈span N := ⟨mul_nonneg N.time_pos.le hs.1,by simpa using mul_le_mul_of_nonneg_left hs.2 N.time_pos.le⟩
    let t := N.time*s
    have hz : (γ s).val=R t := by change R (f t)=R t; rw [eqF t hts]
    have hb : HasDerivAt (fun u => f (N.time*u)) N.time s := by
      have hclock : HasDerivAt (fun u : ℝ => N.time*u) N.time s := by
        simpa only [id_eq,mul_one] using (hasDerivAt_id s).const_mul N.time
      have hequal : (fun u : ℝ => f (N.time*u)) =ᶠ[𝓝 s] (fun u : ℝ => N.time*u) :=
        (hfe t hts).comp_tendsto hclock.continuousAt.tendsto
      exact hclock.congr_of_eventuallyEq hequal
    have hr : HasDerivAt R (d t) (f t) := by rw [eqF t hts]; exact (hR t hts).2
    have hder : HasDerivAt (fun u => (γ u).val) (N.time • d t) s := by
      change HasDerivAt (R ∘ fun u => f (N.time*u)) (N.time • d t) s
      exact hr.scomp s hb
    have hv' := ambient_velocity a γ hγ s _ hder
    have htim := hT.2 (γ s)
    have heW : W a T (R t)=(T (γ s):E4) := hz ▸ W_on a T (γ s)
    have hpair := cone_pair_negative m a e hp (hR t hts).1 (henergy t hts)
      (w:=W a T (R t)) (by
        change F m a e (R t) (W a T (R t)) (W a T (R t)) < 0
        rw [heW,←hz]
        exact htim) (common_sign (hsign t hts) (horient t hts))
    refine ⟨show (γ s).val∈S m a e by rw [hz]; exact (hR t hts).1,?_,?_,?_⟩
    · change (velocity γ s:E4)≠0
      rw [hv']
      exact smul_ne_zero N.time_pos.ne' (hdn t hts)
    · change F m a e (γ s).val (velocity γ s:E4) (velocity γ s:E4) ≤ 0
      rw [hv',hz]
      simp only [map_smul,ContinuousLinearMap.smul_apply,smul_eq_mul]
      exact mul_nonpos_of_nonneg_of_nonpos N.time_pos.le (mul_nonpos_of_nonneg_of_nonpos N.time_pos.le (henergy t hts))
    · change F m a e (γ s).val (velocity γ s:E4) (T (γ s):E4) < 0
      rw [hv',hz,←heW]
      simp only [map_smul,ContinuousLinearMap.smul_apply,smul_eq_mul]
      exact mul_neg_of_pos_of_neg N.time_pos hpair
  · simpa only [γ,mul_zero,eqF 0 h₀] using hfirst
  · simpa only [γ,mul_one,eqF _ (right_mem_Icc.mpr N.time_pos.le)] using hlast

theorem energy_cont {m a e : ℝ} (hp : IsKerrNewmanBlackHoleParams m a e) {x₀ : E4}
    (N : NF m a e x₀) {p q : E4} (hpS : p∈S m a e) (ht : (p,q)∈N.normal.target) :
    ContinuousAt (fun k : E4×E4 => initialEnergy N k.1 k.2) (p,q) := by
  have hF := ((field_smooth m a e hp p hpS).continuousWithinAt.continuousAt ((openS m a e).mem_nhds hpS)).comp
    (continuous_fst.continuousAt (x:=(p,q)))
  exact (hF.clm_apply (logVec_continuousAt N ht)).clm_apply (logVec_continuousAt N ht)


end
end InnerRadialGeodesics


open NoHair NoHair.KNE Set Filter
open scoped ContDiff Manifold BigOperators Topology

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 350000

/-! Regular parametrized arcs and rounding of causal corners. Matching first derivatives
give a regular join. For a strict corner the quadratic middle arc matches both endpoint jets. -/
namespace InnerCausalJoining
noncomputable section

export NoHair.CausalJoining (U G kEval J F W W_on W_cont eval_smooth Arc join fromCurve middleTime middle)
abbrev D (m a e : ℝ) := (Subtype.val : U a → E4) ⁻¹' innerRadialRegion m a e
private abbrev I4 := 𝓘(ℝ, E4)
open InnerRadialGeodesics (timeComponent metric_formula exterior_profile spatial_squares cone_estimates ambient_velocity)

def Good (m a e : ℝ) (T : VecField (U a)) (z v : E4) : Prop :=
  z ∈ innerRadialRegion m a e ∧ F m a e z v v ≤ 0 ∧ F m a e z v (W a T z) < 0

private theorem good_scale (m a e : ℝ) (T : VecField (U a)) {z v : E4} (h : Good m a e T z v)
    {c : ℝ} (hc : 0<c) : Good m a e T z (c • v) := by
  obtain ⟨hz,hv,hw⟩ := h
  refine ⟨hz, ?_, ?_⟩
  · simp only [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]
    exact mul_nonpos_of_nonneg_of_nonpos hc.le (mul_nonpos_of_nonneg_of_nonpos hc.le hv)
  · simp only [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]
    exact mul_neg_of_pos_of_neg hc hw

theorem directions (m a e : ℝ) (hp : IsKerrNewmanBlackHoleParams m a e) (T : VecField (U a))
    (hT : IsTimeOrientation (G m a e) T) (x : U a) (v w : E4)
    (hv : Good m a e T x.val v) (hw : Good m a e T x.val w) :
    (∃ c : ℝ, 0<c ∧ v=c • w) ∨ F m a e x.val v w < 0 := by
  have hf := exterior_profile m a e hp x hv.1
  have vn (h : E4) (hh : Good m a e T x.val h) : h ≠ 0 := by
    intro he
    have hh' := hh.2.2
    simp [he] at hh'
  have ht (h : E4) (hh : Good m a e T x.val h) : 0 < h 0 * timeComponent (T x) := by
    apply (cone_estimates m a e x hf h (T x) (vn h hh) hh.2.1 _ (hT.2 x)).2
    exact (show F m a e x.val h (T x : E4)<0 by simpa only [W_on] using hh.2.2)
  have hprod : 0 < v 0*w 0 := by
    rcases mul_pos_iff.mp (ht v hv) with h₁|h₁ <;> rcases mul_pos_iff.mp (ht w hw) with h₂|h₂
    · exact mul_pos h₁.1 h₂.1
    · linarith [h₁.2,h₂.2]
    · linarith [h₁.2,h₂.2]
    · exact mul_pos_of_neg_of_neg h₁.1 h₂.1
  let u : E4 := (w 0) • v - (v 0) • w
  by_cases h : u=0
  · left
    have hw0 := (mul_ne_zero_iff.mp hprod.ne').2
    refine ⟨v 0/w 0, (div_pos_iff.mpr (mul_pos_iff.mp hprod)), ?_⟩
    have hh : (w 0) • v = (v 0) • w := sub_eq_zero.mp h
    ext i
    have ee := congrArg (fun k : E4 => k i) hh
    change w 0*v i = v 0*w i at ee
    change v i = v 0/w 0*w i
    field_simp [hw0]
    linarith
  · right
    have hu0 : u 0 = 0 := by simp [u, smul_eq_mul, mul_comm]
    have hpos : 0 < F m a e x.val u u := by
      by_contra! hle
      have hsq := spatial_squares m a e x hf u hle
      rw [hu0] at hsq
      apply h
      ext i
      fin_cases i
      · exact hu0
      · change u 1=0
        apply sq_eq_zero_iff.mp
        nlinarith only [hsq, sq_nonneg (u 1), sq_nonneg (u 2), sq_nonneg (u 3)]
      · change u 2=0
        apply sq_eq_zero_iff.mp
        nlinarith only [hsq, sq_nonneg (u 1), sq_nonneg (u 2), sq_nonneg (u 3)]
      · change u 3=0
        apply sq_eq_zero_iff.mp
        nlinarith only [hsq, sq_nonneg (u 1), sq_nonneg (u 2), sq_nonneg (u 3)]
    let A := F m a e x.val
    have hsym : A w v = A v w := by
      change G m a e x w v = G m a e x v w
      rw [metric_formula, metric_formula]; ring
    change 0 < A ((w 0) • v - (v 0) • w) ((w 0) • v - (v 0) • w) at hpos
    simp only [map_sub, map_smul, ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
      smul_eq_mul, hsym] at hpos
    by_contra! hn
    change 0 ≤ A v w at hn
    nlinarith only [hpos, mul_nonpos_of_nonneg_of_nonpos (sq_nonneg (w 0)) hv.2.1,
      mul_nonpos_of_nonneg_of_nonpos (sq_nonneg (v 0)) hw.2.1, mul_nonneg hprod.le hn]

private def arcReparam (P : Arc) (f d : ℝ → ℝ) (hd : ∀ s, HasDerivAt f (d s) s)
    (hc : Continuous d) : Arc where
  pos := fun t => P.pos (f t)
  vel := fun t => d t • P.vel (f t)
  hasDeriv s := (P.hasDeriv (f s)).scomp s (hd s)
  continuous_vel := hc.smul (P.continuous_vel.comp (continuous_iff_continuousAt.mpr fun s => (hd s).continuousAt))

private def arcAffine (P : Arc) (c b : ℝ) : Arc :=
  arcReparam P (fun s => c*(s-b)) (fun _ => c) (fun s => by
    simpa using (((hasDerivAt_id s).sub_const b).const_mul c)) continuous_const

theorem fromCurve_good (m a e : ℝ) (T : VecField (U a)) (γ : ℝ → U a)
    (hγ : IsFutureCausalCurveIn (G m a e) T (D m a e) γ) (s : ℝ) (hs : s∈J) :
    Good m a e T ((fromCurve γ hγ.1).pos s) ((fromCurve γ hγ.1).vel s) := by
  let P := fromCurve γ hγ.1
  have he := ambient_velocity a γ hγ.1 s (P.vel s) (P.hasDeriv s)
  change Good m a e T (γ s).val (P.vel s)
  rw [← he]
  obtain ⟨hx,_,hv,ht⟩ := hγ.2 s hs
  change F m a e (γ s).val (velocity γ s:E4) (T (γ s):E4)<0 at ht
  exact ⟨hx,hv,by rw [W_on]; exact ht⟩

private theorem realize (m a e : ℝ) (T : VecField (U a)) (P : Arc) (L : ℝ) (hL : 0<L)
    (p q : U a) (h0 : P.pos 0=p.val) (h1 : P.pos L=q.val) (hU : ∀ s, P.pos s∈U a)
    (hg : ∀ s ∈ Icc (0:ℝ) L, Good m a e T (P.pos s) (P.vel s)) :
    q∈causalFuture (G m a e) T (D m a e) p := by
  let γ (s : ℝ) : U a := ⟨P.pos (L*s),hU _⟩
  have hc : ContDiff ℝ 1 (Subtype.val ∘ γ) := P.smooth.comp (contDiff_const.mul contDiff_id)
  have hγ : ContMDiff 𝓘(ℝ,ℝ) I4 1 γ := by
    intro s
    exact (ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff γ univ s).mp (hc.contMDiff s)
  refine Or.inr ⟨γ,⟨hγ,?_⟩,Subtype.ext (by simpa [γ] using h0),Subtype.ext (by simpa [γ] using h1)⟩
  intro s hs
  have hls : L*s∈Icc (0:ℝ) L := ⟨mul_nonneg hL.le hs.1,by simpa using mul_le_mul_of_nonneg_left hs.2 hL.le⟩
  have h := good_scale m a e T (hg _ hls) hL
  have hd : HasDerivAt (fun t => (γ t).val) (L • P.vel (L*s)) s :=
    (P.hasDeriv (L*s)).scomp s (by simpa using (hasDerivAt_id s).const_mul L)
  have he := ambient_velocity a γ hγ s _ hd
  have htg : G m a e (γ s) (velocity γ s) (T (γ s)) < 0 := by
    change F m a e (γ s).val (velocity γ s : E4) (T (γ s) : E4) < 0
    rw [he, ← W_on a T (γ s)]
    exact h.2.2
  refine ⟨h.1,?_,?_,htg⟩
  · intro hh
    simp [hh] at htg
  · change F m a e (γ s).val (velocity γ s : E4) (velocity γ s : E4) ≤ 0
    rw [he]
    exact h.2.1

private theorem use_join (c : ℝ) (P Q : Arc) (h : P.pos c=Q.pos c) (h' : P.vel c=Q.vel c)
    (s : ℝ) (R : E4→E4→Prop) (hL : s ≤ c → R (P.pos s) (P.vel s))
    (hR : c ≤ s → R (Q.pos s) (Q.vel s)) :
    R ((join c P Q h h').pos s) ((join c P Q h h').vel s) := by
  by_cases hs : s ≤ c
  · simpa [join,hs] using hL hs
  · simpa [join,hs] using hR (le_of_not_ge hs)

theorem combine_parallel (m a e : ℝ) (T : VecField (U a)) (P Q : Arc) (p x q : U a)
    (h0 : P.pos 0=p.val) (h1 : P.pos 1=x.val) (g0 : Q.pos 0=x.val) (g1 : Q.pos 1=q.val)
    (pU : ∀ s, P.pos s∈U a) (qU : ∀ s, Q.pos s∈U a)
    (pG : ∀ s∈J, Good m a e T (P.pos s) (P.vel s)) (qG : ∀ s∈J, Good m a e T (Q.pos s) (Q.vel s))
    (c : ℝ) (hc : 0<c) (he : P.vel 1=c • Q.vel 0) : q∈causalFuture (G m a e) T (D m a e) p := by
  let B := arcAffine Q c 1
  have hj : P.pos 1=B.pos 1 := by simpa [B,arcAffine,arcReparam,g0] using h1
  have hv : P.vel 1=B.vel 1 := by simpa [B,arcAffine,arcReparam] using he
  let A := join 1 P B hj hv
  let L := 1+1/c
  have hL : 1<L := by dsimp [L]; linarith [one_div_pos.mpr hc]
  have hlast : c*(L-1)=1 := by dsimp [L]; field_simp [hc.ne'] <;> ring
  apply realize m a e T A L (by linarith) p q
  · simpa [A,join] using h0
  · simpa [A,join,hL.not_ge,B,arcAffine,arcReparam,hlast] using g1
  · intro s
    apply use_join 1 P B hj hv s (fun z _ => z∈U a) (fun _ => pU s) (fun _ => qU _)
  · intro s hs
    apply use_join 1 P B hj hv s (Good m a e T) (fun ht => pG s ⟨hs.1,ht⟩)
    intro ht
    apply good_scale m a e T _ hc
    apply qG _ ⟨mul_nonneg hc.le (sub_nonneg.mpr ht),?_⟩
    exact (mul_le_mul_of_nonneg_left (sub_le_sub_right hs.2 1) hc.le).trans_eq hlast

theorem combine_round (m a e : ℝ) (hp : IsKerrNewmanBlackHoleParams m a e)
    (T : VecField (U a)) (P Q : Arc) (p x q : U a)
    (h0 : P.pos 0=p.val) (h1 : P.pos 1=x.val) (g0 : Q.pos 0=x.val) (g1 : Q.pos 1=q.val)
    (pU : ∀ s, P.pos s∈U a) (qU : ∀ s, Q.pos s∈U a)
    (pG : ∀ s∈J, Good m a e T (P.pos s) (P.vel s)) (qG : ∀ s∈J, Good m a e T (Q.pos s) (Q.vel s))
    (d : ℝ) (hd : 0<d) (hd1 : d<1)
    (hmid : ∀ u∈J,
      let s := 1-d*(1-u)^2
      let t := d*u^2
      Good m a e T (P.pos s+Q.pos t-x.val) ((1-u) • P.vel s + u • Q.vel t)) :
    q∈causalFuture (G m a e) T (D m a e) p := by
  let M := middle d hd P Q x.val
  let B := arcAffine Q 1 1
  have hleft : middleTime d (1-d)=0 := by simp [middleTime]
  have hright : middleTime d (1+d)=1 := by unfold middleTime; field_simp [hd.ne']; ring
  have hj : P.pos (1-d)=M.pos (1-d) := by
    change P.pos (1-d) = P.pos (1-d*(1-middleTime d (1-d))^2)+Q.pos (d*middleTime d (1-d)^2)-x.val
    rw [hleft]
    simp [g0]
  have hv : P.vel (1-d)=M.vel (1-d) := by simp [M,middle,hleft]
  let A := join (1-d) P M hj hv
  have hlt : 1-d < 1+d := by linarith
  have hj' : A.pos (1+d)=B.pos (1+d) := by simp [A,join,hlt.not_ge,M,middle,hright,h1,B,arcAffine,arcReparam]
  have hv' : A.vel (1+d)=B.vel (1+d) := by simp [A,join,hlt.not_ge,M,middle,hright,B,arcAffine,arcReparam]
  let path := join (1+d) A B hj' hv'
  have hmg (s : ℝ) (hl : 1-d ≤ s) (hr : s ≤ 1+d) : Good m a e T (M.pos s) (M.vel s) := by
    apply hmid (middleTime d s)
    constructor
    · exact div_nonneg (sub_nonneg.mpr hl) (by positivity)
    · apply (div_le_iff₀ (by positivity : 0<2*d)).mpr
      linarith
  have hdu {z : E4} (h : z∈innerRadialRegion m a e) : z∈U a := by
    change max 1 (e^2/(2*m)) < ksRadius a z at h
    exact zero_lt_one.trans ((le_max_left 1 _).trans_lt h)
  apply realize m a e T path 2 (by norm_num) p q
  · simpa [path,A,join,show (0:ℝ) ≤ 1+d by linarith,show (0:ℝ) ≤ 1-d by linarith] using h0
  · simpa [path,join,show ¬ (2:ℝ) ≤ 1+d by linarith,B,arcAffine,arcReparam,show (2:ℝ)-1=1 by norm_num] using g1
  · intro s
    apply use_join _ A B hj' hv' s (fun z _ => z∈U a) _ (fun _ => qU _)
    intro hr
    exact use_join _ P M hj hv s (fun z _ => z∈U a) (fun _ => pU _) (fun hl => hdu (hmg s hl hr).1)
  · intro s hs
    apply use_join _ A B hj' hv' s (Good m a e T)
    · intro hr
      apply use_join _ P M hj hv s (Good m a e T) _ (fun hl => hmg s hl hr)
      intro hl
      exact pG s ⟨hs.1,by linarith⟩
    · intro hl
      have hJ : s-1∈J := ⟨by linarith,by linarith [hs.2]⟩
      simpa [B,arcAffine,arcReparam] using qG (s-1) hJ


end
end InnerCausalJoining

namespace InnerLocalOrder

open NoHair InnerRadialGeodesics Set Filter
open OAI.WeakMTWGlobalSupport OAI.WeakMTWGlobalSupport.CoordinateGeometry
open OAI.WeakMTWGlobalSupport.NormalNeighborhood NoHair.PseudoNormal
open scoped ContDiff Manifold BigOperators Topology
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 330000
noncomputable section

private theorem energy_barrier (m a e : ℝ) (hp : IsKerrNewmanBlackHoleParams m a e)
    {x₀ : E4} (N : NF m a e x₀) (base : E4) (c v : ℝ→E4) (o : ℝ)
    (hd : ∀ t, HasDerivAt c (v t) t) (hmemS : ∀ t∈J, c t∈S m a e)
    (htarget : ∀ t∈J, (base,c t)∈N.normal.target)
    (hcone : ∀ t∈J, F m a e (c t) (v t) (v t) ≤ 0)
    (hsign : ∀ t∈J, 0 < o*v t 0) (htime : ∀ t∈J, 0 < o*(c t 0-base 0))
    (hseed : initialEnergy N base (c 0) < 0) : initialEnergy N base (c 1) ≤ initialEnergy N base (c 0) := by
  have sG := field_smooth m a e hp
  have invG (z : E4) (hz : z∈S m a e) := field_inv m a e hp hz
  have symG (z : E4) (hz : z∈S m a e) := field_sym m a e hp hz
  let d (t : ℝ) := (2/N.time)*F m a e (c t) (terminalVelocity N base (c t)) (v t)
  have HE (t : ℝ) (ht : t∈J) : HasDerivAt (fun t => initialEnergy N base (c t)) (d t) t :=
    initialEnergy_deriv N (openS m a e) sG symG invG (htarget t ht) (hd t)
  have H := image_le_of_deriv_right_lt_deriv_boundary (f:=fun t => initialEnergy N base (c t))
    (f':=d) (B:=fun _ => initialEnergy N base (c 0)) (B':=fun _ => 0) (a:=(0:ℝ)) (b:=1)
    (fun t ht => (HE t ht).continuousAt.continuousWithinAt) (fun t ht => (HE t (Ico_subset_Icc_self ht)).hasDerivWithinAt)
    le_rfl (fun t => hasDerivAt_const t _) (by
      intro t hti ha
      have ht := Ico_subset_Icc_self hti
      let u := logVec N base (c t)
      have htar' := htarget t ht
      have hu : (base,u)∈N.normal.source := (N.normalAt base).map_target htar'
      obtain ⟨hR,hC,hfirst,_⟩ := radial_data N hu
      have hlast : Z N base u N.time=c t := by simpa only [N.normalAt_apply,Z,u,logVec] using (N.normalAt base).right_inv htar'
      have htim (r : ℝ) (hr : r∈span N) :
          F m a e (Z N base u r) (Velo N base u r) (Velo N base u r) < 0 :=
        (flow_energy N (openS m a e) sG symG invG hu hr).trans_lt (ha.trans_lt hseed)
      have hdt (r : ℝ) (hr : r∈span N) : Velo N base u r 0≠0 := by
        have hh := htim r hr
        exact nonzero_time m a e hp (hR r hr).1 (fun h => by simp [h] at hh) hh.le
      have hforward : 0 < o*(Z N base u N.time 0-Z N base u 0 0) := by
        rw [hlast,hfirst]
        exact htime t ht
      have hfin : N.time∈span N := right_mem_Icc.mpr N.time_pos.le
      have hsg := clock_positive N.time_pos (Z N base u) (Velo N base u) (fun r hr => (hR r hr).2) hC hdt hforward N.time hfin
      have hh := htim N.time hfin
      rw [hlast] at hh
      have hm := cone_pair_negative m a e hp (hmemS t ht) (hcone t ht) hh (common_sign (hsign t ht) hsg)
      dsimp only [d]
      apply mul_neg_of_pos_of_neg (div_pos (by norm_num) N.time_pos)
      rw [symG (c t) (hmemS t ht)]
      exact hm)
  exact H (right_mem_Icc.mpr zero_le_one)

private theorem past_shift_limit {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (p w : E) :
    Tendsto (fun t : ℝ => p-t • w) (𝓝[>] (0:ℝ)) (𝓝 p) := by
  have h : Continuous (fun t : ℝ => p-t • w) := continuous_const.sub (continuous_id.smul continuous_const)
  have hh := (h.tendsto 0).mono_left (nhdsWithin_le_nhds (s:=Ioi (0:ℝ)))
  simpa only [zero_smul,sub_zero] using hh

private theorem derivative_quotient {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ→E) (v : E) (hf : HasDerivAt f v 0) (h0 : f 0=0) :
    Tendsto (fun s : ℝ => s⁻¹ • f s) (𝓝[>] (0:ℝ)) (𝓝 v) := by
  have h := (hasDerivAt_iff_tendsto_slope_left_right.mp hf).2
  have he : slope f 0 = (fun s : ℝ => s⁻¹ • f s) := by
    funext s
    rw [slope_def_module,h0,sub_zero,sub_zero]
  rwa [he] at h

private theorem scaled_norm_negative {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : ℝ → E →L[ℝ] E →L[ℝ] ℝ) (g₀ : E →L[ℝ] E →L[ℝ] ℝ) (f : ℝ→E) (v : E)
    (hg : Tendsto g (𝓝[>] (0:ℝ)) (𝓝 g₀)) (hf : Tendsto (fun s : ℝ => s⁻¹ • f s) (𝓝[>] 0) (𝓝 v))
    (hneg : g₀ v v < 0) : ∀ᶠ s in 𝓝[>] (0:ℝ), g s (f s) (f s) < 0 := by
  have he : Continuous (fun k : (E →L[ℝ] E →L[ℝ] ℝ) × (E×E) => k.1 k.2.1 k.2.2) :=
    (continuous_fst.clm_apply (continuous_fst.comp continuous_snd)).clm_apply (continuous_snd.comp continuous_snd)
  have hlim : Tendsto (fun s : ℝ => g s (s⁻¹ • f s) (s⁻¹ • f s)) (𝓝[>] 0) (𝓝 (g₀ v v)) :=
    (he.tendsto (g₀,v,v)).comp (hg.prodMk_nhds (hf.prodMk_nhds hf))
  have hspos : ∀ᶠ s in 𝓝[>] (0:ℝ), 0<s := self_mem_nhdsWithin
  filter_upwards [hlim.eventually_lt_const hneg,hspos] with s hs hp
  change g s (s⁻¹ • f s) (s⁻¹ • f s) < 0 at hs
  simp only [map_smul,ContinuousLinearMap.smul_apply,smul_eq_mul] at hs
  exact neg_of_mul_neg_right (neg_of_mul_neg_right hs (inv_pos.mpr hp).le) (inv_pos.mpr hp).le

private theorem scale_timelike {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (G : E →L[ℝ] E →L[ℝ] ℝ) (v : E) (t : ℝ) (ht : 0 < t) (hv : G v v < 0) :
    G (t⁻¹ • v) (t⁻¹ • v) < 0 := by
  simp only [map_smul,ContinuousLinearMap.smul_apply,smul_eq_mul]
  exact mul_neg_of_pos_of_neg (inv_pos.mpr ht) (mul_neg_of_pos_of_neg (inv_pos.mpr ht) hv)

private theorem past_seed (m a e : ℝ) (hp : IsKerrNewmanBlackHoleParams m a e) {x₀ : E4} (N : NF m a e x₀)
    {p : E4} (hpS : p∈S m a e) (hsrc : (p,(0:E4))∈N.normal.source)
    (hlog : logVec N p p = 0) (w : E4) (hw : F m a e p w w < 0) :
    ∀ᶠ s in 𝓝[>] (0:ℝ), initialEnergy N (p-s • w) p < 0 := by
  let f (s : ℝ) := logVec N (p-s • w) p
  let g (s : ℝ) := F m a e (p-s • w)
  have sm := field_smooth m a e hp
  have hG : ContinuousAt (F m a e) p := (sm p hpS).continuousWithinAt.continuousAt ((openS m a e).mem_nhds hpS)
  have gL : Tendsto g (𝓝[>] (0:ℝ)) (𝓝 (F m a e p)) := hG.tendsto.comp (past_shift_limit p w)
  have hd : HasDerivAt f (N.time⁻¹ • w) 0 := logVec_base_deriv N (openS m a e) sm
    (fun z hz => field_inv m a e hp hz) hsrc w
  have f0 : f 0 = 0 := by simpa only [f,zero_smul,sub_zero] using hlog
  exact scaled_norm_negative g (F m a e p) f (N.time⁻¹ • w) gL
    (derivative_quotient f _ hd f0) (scale_timelike _ w N.time N.time_pos hw)

private theorem positive_shift {a p o s : ℝ} (h : 0 ≤ o*(a-p)) (ho : o≠0) (hs : 0<s) :
    0 < o*(a-(p-s*o)) := by
  nlinarith only [h,mul_pos hs (sq_pos_iff.mpr ho)]

private theorem past_energy_limit {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (k : E×E→ℝ) (p q w : E) (hc : ContinuousAt k (p,q))
    (hh : ∀ᶠ s in 𝓝[>] (0:ℝ), k (p-s • w,q) ≤ 0) : k (p,q) ≤ 0 := by
  have hpair : Tendsto (fun s : ℝ => (p-s • w,q)) (𝓝[>] 0) (𝓝 (p,q)) :=
    (past_shift_limit p w).prodMk_nhds tendsto_const_nhds
  exact le_of_tendsto (hc.tendsto.comp hpair) hh

private theorem clock_along (c v : ℝ→E4) (o : ℝ) (hd : ∀ t, HasDerivAt c (v t) t)
    (hc : Continuous v) (hn : ∀ t∈J, v t 0≠0) (hstart : 0 < o*v 0 0) :
    (∀ t∈J, 0 < o*v t 0) ∧ ∀ t∈J, 0 ≤ o*(c t 0-c 0 0) := by
  have h₀ : (0:ℝ)∈J := left_mem_Icc.mpr zero_le_one
  have hone := (mul_ne_zero_iff.mp hstart.ne').1
  have hsign : ∀ t∈J, 0 < o*v t 0 := sign_prop
    (continuous_const.mul ((EuclideanSpace.proj (𝕜:=ℝ) 0).continuous.comp hc)).continuousOn
    (fun t ht => mul_ne_zero hone (hn t ht)) h₀ hstart
  have hclock (t : ℝ) : HasDerivAt (fun s => o*c s 0) (o*v t 0) t :=
    (time_deriv (hd t)).const_mul o
  have hdiff : Differentiable ℝ (fun s => o*c s 0) := fun t => (hclock t).differentiableAt
  have hmono : MonotoneOn (fun s => o*c s 0) J := monotoneOn_of_deriv_nonneg (convex_Icc (0:ℝ) 1)
    hdiff.continuous.continuousOn hdiff.differentiableOn (fun t ht => (hclock t).deriv.symm ▸ (hsign t (interior_subset ht)).le)
  refine ⟨hsign,?_⟩
  intro t ht
  rw [mul_sub]
  exact sub_nonneg.mpr (hmono h₀ ht ht.1)

private theorem energy_of_arc (m a e : ℝ) (hp : IsKerrNewmanBlackHoleParams m a e)
    {x₀ : E4} (N : NF m a e x₀) (V : Set E4) (hV : IsOpen V) (hVS : V⊆S m a e)
    (htar : ∀ p∈V, ∀ q∈V, (p,q)∈N.normal.target) (p q w : E4)
    (hpV : p∈V) (hqV : q∈V) (hsrc : (p,(0:E4))∈N.normal.source)
    (hlog : logVec N p p = 0) (hw : F m a e p w w < 0)
    (c v : ℝ→E4) (hd : ∀ t, HasDerivAt c (v t) t)
    (hmem : ∀ t∈J, c t∈V) (he0 : c 0=p) (he1 : c 1=q)
    (hcone : ∀ t∈J, F m a e (c t) (v t) (v t) ≤ 0)
    (hsign : ∀ t∈J, 0 < w 0*v t 0) (hdisp : ∀ t∈J, 0 ≤ w 0*(c t 0-p 0)) :
    initialEnergy N p q ≤ 0 := by
  let o := w 0
  have h₀ : (0:ℝ)∈J := left_mem_Icc.mpr zero_le_one
  have hone : o≠0 := (mul_ne_zero_iff.mp (hsign 0 h₀).ne').1
  let b (s : ℝ) := p-s • w
  have bL : Tendsto b (𝓝[>] (0:ℝ)) (𝓝 p) := past_shift_limit p w
  have bV : ∀ᶠ s in 𝓝[>] (0:ℝ), b s∈V := bL (hV.mem_nhds hpV)
  have spos : ∀ᶠ s in 𝓝[>] (0:ℝ), 0<s := self_mem_nhdsWithin
  have hbase : ∀ᶠ s in 𝓝[>] (0:ℝ), initialEnergy N (b s) p < 0 :=
    past_seed m a e hp N (hVS hpV) hsrc hlog w hw
  have hbound : ∀ᶠ s in 𝓝[>] (0:ℝ), initialEnergy N (b s) q ≤ 0 := by
    filter_upwards [hbase,bV,spos] with s hseed hsV hspos
    have htime (t : ℝ) (ht : t∈J) : 0 < o*(c t 0-b s 0) := by
      change 0 < o*(c t 0-(p 0-s*o))
      exact positive_shift (hdisp t ht) hone hspos
    have h := energy_barrier m a e hp N (b s) c v o hd (fun t ht => hVS (hmem t ht))
      (fun t ht => htar _ hsV _ (hmem t ht)) hcone hsign htime (by rwa [he0])
    rw [he0,he1] at h
    exact h.trans hseed.le
  exact past_energy_limit (fun k : E4×E4 => initialEnergy N k.1 k.2) p q w
    (energy_cont hp N (hVS hpV) (htar _ hpV _ hqV)) hbound


private theorem curve_necessary (m a e : ℝ) (hp : IsKerrNewmanBlackHoleParams m a e)
    (T : VecField (U a)) (hT : IsTimeOrientation (G m a e) T) {x₀ : E4} (N : NF m a e x₀)
    (V : Set E4) (hV : IsOpen V) (hVS : V⊆S m a e) (hsrc : ∀ x∈V, (x,(0:E4))∈N.normal.source)
    (htar : ∀ p∈V, ∀ q∈V, (p,q)∈N.normal.target)
    (p q : U a) (hpV : p.val∈V) (hqV : q.val∈V)
    (hJ : q∈causalFuture (G m a e) T ((Subtype.val : U a → E4) ⁻¹' V) p) :
    initialEnergy N p.val q.val ≤ 0 ∧ 0 ≤ (q.val 0-p.val 0)*timeComponent (T p) := by
  have sG := field_smooth m a e hp
  have invG (z : E4) (hz : z∈S m a e) := field_inv m a e hp hz
  have hxsrc := hsrc p.val hpV
  have hlog0 : logVec N p.val p.val = 0 := by
    have he := normalAt_zero_of_invertible N (openS m a e) sG invG hxsrc
    simpa only [logVec,he] using (N.normalAt p.val).left_inv hxsrc
  rcases hJ with he|⟨γ,hγ,h0,h1⟩
  · have heq : q = p := mem_singleton_iff.mp he
    subst q
    constructor
    · change F m a e p.val (logVec N p.val p.val) (logVec N p.val p.val) ≤ 0
      simp only [hlog0,map_zero,ContinuousLinearMap.zero_apply,le_refl]
    · simp only [sub_self,zero_mul,le_refl]
  let c (t : ℝ) := (γ t).val
  let v := deriv c
  let w : E4 := T p
  let o := w 0
  have hval : ContMDiff I4 I4 1 (Subtype.val : U a→E4) := contMDiff_subtype_val
  have hc : ContDiff ℝ 1 c := (hval.comp hγ.1).contDiff
  have hd (t : ℝ) : HasDerivAt c (v t) t := (hc.differentiable (by simp) t).hasDerivAt
  have hvel (t : ℝ) := ambient_velocity a γ hγ.1 t (v t) (hd t)
  have hmem (t : ℝ) (ht : t∈J) : c t∈V := (hγ.2 t ht).1
  have he0 : c 0=p.val := congrArg Subtype.val h0
  have he1 : c 1=q.val := congrArg Subtype.val h1
  have hcone (t : ℝ) (ht : t∈J) : v t≠0 ∧ F m a e (c t) (v t) (v t) ≤ 0 ∧ 0 < (v t 0)*timeComponent (T (γ t)) := by
    obtain ⟨hx,hn,hv,hf⟩ := hγ.2 t ht
    have hh := (cone_estimates m a e (γ t) (exterior_profile m a e hp _ (hVS hx)) _ _ hn hv hf (hT.2 _)).2
    change 0 < timeComponent (velocity γ t) * timeComponent (T (γ t)) at hh
    rw [hvel] at hh
    change (velocity γ t:E4)≠0 at hn
    change F m a e (c t) (velocity γ t:E4) (velocity γ t:E4) ≤ 0 at hv
    rw [hvel] at hn hv
    exact ⟨hn,hv,hh⟩
  have h₀ : (0:ℝ)∈J := left_mem_Icc.mpr zero_le_one
  have h₁ : (1:ℝ)∈J := right_mem_Icc.mpr zero_le_one
  have hstart : 0 < o*v 0 0 := by
    have h := (hcone 0 h₀).2.2
    rw [h0,mul_comm] at h
    exact h
  have hn (t : ℝ) (ht : t∈J) : v t 0≠0 :=
    nonzero_time m a e hp (hVS (hmem t ht)) (hcone t ht).1 (hcone t ht).2.1
  obtain ⟨hsign,hdisp₀⟩ := clock_along c v o hd (hc.continuous_deriv le_rfl) hn hstart
  have hdisp (t : ℝ) (ht : t∈J) : 0 ≤ o*(c t 0-p.val 0) := by
    simpa only [he0] using hdisp₀ t ht
  refine ⟨energy_of_arc m a e hp N V hV hVS htar p.val q.val w hpV hqV hxsrc hlog0
    (hT.2 p) c v hd hmem he0 he1 (fun t ht => (hcone t ht).2.1) hsign hdisp,?_⟩
  rw [← he1,mul_comm]
  exact hdisp 1 h₁

theorem localClosure (m a e : ℝ) (hp : IsKerrNewmanBlackHoleParams m a e)
    (T : VecField (kerrNewmanSpacetime a)) (hT : IsTimeOrientation (kerrNewmanMetricField m a e) T) :
    let U := kerrNewmanSpacetime a
    let D := (Subtype.val : U → E4) ⁻¹' innerRadialRegion m a e
    let g := kerrNewmanMetricField m a e
    ∀ x ∈ D, ∃ V : Set U, IsOpen V ∧ x ∈ V ∧ V ⊆ D ∧
      ∀ z : U × U, z.1 ∈ V → z.2 ∈ V →
        z ∈ closure {y : U × U | y.1 ∈ V ∧ y.2 ∈ V ∧ y.2 ∈ causalFuture g T V y.1} →
          z.2 ∈ causalFuture g T D z.1 := by
  classical
  dsimp only
  intro x hx
  obtain ⟨N⟩ := exists_normalFlow_of_invertible (openS m a e) (field_smooth m a e hp)
    (fun z hz => field_inv m a e hp hz) (x₀:=x.val) hx
  have hdiag := normal_center N (openS m a e) (field_smooth m a e hp) (fun z hz => field_inv m a e hp hz) N.center_mem
  have htar : (x.val,x.val)∈N.normal.target := hdiag ▸ N.normal.map_source N.center_mem
  obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp (N.normal.open_target.mem_nhds htar)
  let V := Metric.ball x.val r ∩ (S m a e ∩ {p | (p,(0:E4))∈N.normal.source})
  have hV : IsOpen V := Metric.isOpen_ball.inter ((openS m a e).inter
    (N.normal.open_source.preimage (continuous_id.prodMk continuous_const)))
  have hVS {z : E4} (hz : z∈V) := hz.2.1
  have htr (p : E4) (hp : p∈V) (q : E4) (hq : q∈V) : (p,q)∈N.normal.target := by
    apply hball
    rw [Metric.mem_ball,Prod.dist_eq]
    exact max_lt (Metric.mem_ball.mp hp.1) (Metric.mem_ball.mp hq.1)
  refine ⟨(Subtype.val : U a→E4) ⁻¹' V,hV.preimage continuous_subtype_val,
    ⟨Metric.mem_ball_self hr,hx,N.center_mem⟩,fun _ hz => hVS hz,?_⟩
  intro z hpV hqV hcl
  obtain ⟨seq,hseq,hlim⟩ := mem_closure_iff_seq_limit.mp hcl
  have hnec (n : ℕ) := curve_necessary m a e hp T hT N V hV (fun _ hz => hVS hz)
    (fun _ hz => hz.2.2) htr (seq n).1 (seq n).2 (hseq n).1 (hseq n).2.1 (hseq n).2.2
  have hP : Tendsto (fun n => (seq n).1.val) atTop (𝓝 z.1.val) :=
    (continuous_subtype_val.tendsto z.1).comp ((continuous_fst.tendsto z).comp hlim)
  have hQ : Tendsto (fun n => (seq n).2.val) atTop (𝓝 z.2.val) :=
    (continuous_subtype_val.tendsto z.2).comp ((continuous_snd.tendsto z).comp hlim)
  apply radial_future m a e hp T hT N z.1 z.2 (htr _ hpV _ hqV)
  · exact le_of_tendsto ((energy_cont hp N (hVS hpV) (htr _ hpV _ hqV)).tendsto.comp
      (hP.prodMk_nhds hQ)) (Eventually.of_forall fun n => (hnec n).1)
  · have hTlim : Tendsto (fun n => W a T (seq n).1.val) atTop (𝓝 (W a T z.1.val)) :=
      (W_cont m a e T hT z.1).tendsto.comp hP
    have hproj : Continuous timeComponent := (EuclideanSpace.proj (𝕜:=ℝ) (0 : Fin 4)).continuous
    have hQ0 : Tendsto (fun n => timeComponent (seq n).2.val) atTop (𝓝 (timeComponent z.2.val)) :=
      (hproj.tendsto _).comp hQ
    have hP0 : Tendsto (fun n => timeComponent (seq n).1.val) atTop (𝓝 (timeComponent z.1.val)) :=
      (hproj.tendsto _).comp hP
    have ht0 : Tendsto (fun n => timeComponent (W a T (seq n).1.val)) atTop (𝓝 (timeComponent (W a T z.1.val))) :=
      (hproj.tendsto _).comp hTlim
    have hT0 : Tendsto (fun n => timeComponent (T (seq n).1)) atTop (𝓝 (timeComponent (T z.1))) := by
      simpa only [W_on] using ht0
    exact ge_of_tendsto ((hQ0.sub hP0).mul hT0) (Eventually.of_forall fun n => (hnec n).2)

end
end InnerLocalOrder

namespace InnerCausalOrder

open NoHair InnerCausalJoining Set Filter
open scoped ContDiff Manifold BigOperators Topology
noncomputable section
set_option maxHeartbeats 270000

private def patch (P Q : Arc) (y : E4) (k : ℝ×ℝ) : E4 := P.pos k.1 + Q.pos k.2-y
private abbrev corner := ((1:ℝ),(0:ℝ))

private abbrev CornerBilin := E4 → E4 →L[ℝ] E4 →L[ℝ] ℝ
private def Okay (S : Set E4) (g : CornerBilin) (O : E4→E4) (z v : E4) :=
  z∈S ∧ g z v v ≤ 0 ∧ g z v (O z) < 0
private def SmoothAt (g : CornerBilin) (y : E4) := ∀ v w : E4,
  ContDiffAt ℝ 1 (fun k : E4×E4×E4 => g k.1 k.2.1 k.2.2) (y,v,w)

private def OrientedNear (S : Set E4) (g : CornerBilin) (O : E4→E4) (P Q : Arc) (y : E4) (c : ℝ) (k : ℝ×ℝ) :=
  let z := patch P Q y k
  z∈S ∧
    g z (P.vel k.1) (O z) < 0 ∧ g z (Q.vel k.2) (O z) < 0 ∧
    g z (P.vel k.1) (Q.vel k.2) ≤ -c

private def MetricError (g : CornerBilin) (P Q : Arc) (y : E4) (C : ℝ) (k : ℝ×ℝ) :=
  let z := patch P Q y k
  let v := P.vel k.1
  let w := Q.vel k.2
  g z v v - g (P.pos k.1) v v ≤ C*|k.2| ∧
    g z w w - g (Q.pos k.2) w w ≤ C*|k.1-1|

private theorem orientation_near (S : Set E4) (g : CornerBilin) (O : E4→E4) (y : E4) (hdoc : IsOpen S) (hg : SmoothAt g y) (hw : ContinuousAt O y) (P Q : Arc) (hp : P.pos 1=y) (hq : Q.pos 0=y)
    (hP : ∀ s∈J, Okay S g O (P.pos s) (P.vel s)) (hQ : ∀ s∈J, Okay S g O (Q.pos s) (Q.vel s))
    (hcross : g y (P.vel 1) (Q.vel 0) < 0) :
    ∃ c : ℝ, 0<c ∧ ∀ᶠ k in 𝓝 corner, OrientedNear S g O P Q y c k := by
  let A := P.vel 1
  let B := Q.vel 0
  let c := -(g y A B)/2
  have hc : 0<c := by dsimp [c,A,B]; linarith only [hcross]
  have ha := hP 1 (right_mem_Icc.mpr zero_le_one)
  have hb := hQ 0 (left_mem_Icc.mpr zero_le_one)
  rw [hp] at ha
  rw [hq] at hb
  let l : Filter (ℝ×ℝ) := 𝓝 ((1:ℝ),(0:ℝ))
  let Z := patch P Q y
  let v (k : ℝ×ℝ) := P.vel k.1
  let w (k : ℝ×ℝ) := Q.vel k.2
  have pL : Tendsto (fun k : ℝ×ℝ => P.pos k.1) l (𝓝 y) := by
    simpa only [l,←hp,Function.comp_apply,Function.comp_def] using (P.smooth.continuous.comp continuous_fst).tendsto ((1:ℝ),(0:ℝ))
  have qL : Tendsto (fun k : ℝ×ℝ => Q.pos k.2) l (𝓝 y) := by
    simpa only [l,←hq,Function.comp_apply,Function.comp_def] using (Q.smooth.continuous.comp continuous_snd).tendsto ((1:ℝ),(0:ℝ))
  have zL : Tendsto Z l (𝓝 y) := by
    have hz : Z = (fun k : ℝ×ℝ => P.pos k.1 + Q.pos k.2 - y) := funext (fun _ => rfl)
    rw [hz]
    simpa only [add_sub_cancel_right,add_sub_cancel_left] using (pL.add qL).sub (tendsto_const_nhds (x:=y) (f:=l))
  have vL : Tendsto v l (𝓝 A) := (P.continuous_vel.comp continuous_fst).tendsto ((1:ℝ),(0:ℝ))
  have wL : Tendsto w l (𝓝 B) := (Q.continuous_vel.comp continuous_snd).tendsto ((1:ℝ),(0:ℝ))
  have tL : Tendsto (fun k => O (Z k)) l (𝓝 (O y)) := hw.tendsto.comp zL
  have ev {V V' : (ℝ×ℝ)→E4} {b b' : E4} (h : Tendsto V l (𝓝 b)) (h' : Tendsto V' l (𝓝 b')) :
      Tendsto (fun k => g (Z k) (V k) (V' k)) l (𝓝 (g y b b')) :=
    (hg b b').continuousAt.tendsto.comp (zL.prodMk_nhds (h.prodMk_nhds h'))
  have hcx : g y A B < -c := by dsimp [c,A,B]; linarith only [hcross]
  have hd : ∀ᶠ k in l, Z k∈S := zL (hdoc.mem_nhds ha.1)
  have h1 : ∀ᶠ k in l, g (Z k) (v k) (O (Z k))<0 := (ev vL tL).eventually_lt_const ha.2.2
  have h2 : ∀ᶠ k in l, g (Z k) (w k) (O (Z k))<0 := (ev wL tL).eventually_lt_const hb.2.2
  have h3 : ∀ᶠ k in l, g (Z k) (v k) (w k) < -c := (ev vL wL).eventually_lt_const hcx
  refine ⟨c,hc,?_⟩
  filter_upwards [hd,h1,h2,h3] with k hk h1 h2 h3 using ⟨hk,h1,h2,h3.le⟩

private theorem metric_error_near (g : CornerBilin) (y : E4) (hg : SmoothAt g y) (P Q : Arc) (hp : P.pos 1=y) (hq : Q.pos 0=y) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ k in 𝓝 corner, MetricError g P Q y C k := by
  let A := P.vel 1
  let B := Q.vel 0
  let l : Filter (ℝ×ℝ) := 𝓝 ((1:ℝ),(0:ℝ))
  let Z := patch P Q y
  let v (k : ℝ×ℝ) := P.vel k.1
  let w (k : ℝ×ℝ) := Q.vel k.2
  have pL : Tendsto (fun k : ℝ×ℝ => P.pos k.1) l (𝓝 y) := by
    simpa only [l,←hp,Function.comp_apply,Function.comp_def] using (P.smooth.continuous.comp continuous_fst).tendsto ((1:ℝ),(0:ℝ))
  have qL : Tendsto (fun k : ℝ×ℝ => Q.pos k.2) l (𝓝 y) := by
    simpa only [l,←hq,Function.comp_apply,Function.comp_def] using (Q.smooth.continuous.comp continuous_snd).tendsto ((1:ℝ),(0:ℝ))
  have zL : Tendsto Z l (𝓝 y) := by
    have hz : Z = (fun k : ℝ×ℝ => P.pos k.1 + Q.pos k.2 - y) := funext (fun _ => rfl)
    rw [hz]
    simpa only [add_sub_cancel_right,add_sub_cancel_left] using (pL.add qL).sub (tendsto_const_nhds (x:=y) (f:=l))
  have vL : Tendsto v l (𝓝 A) := (P.continuous_vel.comp continuous_fst).tendsto ((1:ℝ),(0:ℝ))
  have wL : Tendsto w l (𝓝 B) := (Q.continuous_vel.comp continuous_snd).tendsto ((1:ℝ),(0:ℝ))
  let H (p : E4×E4) := g p.1 p.2 p.2
  have qsm (b : E4) : ContDiffAt ℝ 1 H (y,b) :=
    (hg b b).comp (f:=fun k : E4×E4 => (k.1,k.2,k.2)) (y,b) (contDiffAt_fst.prodMk (contDiffAt_snd.prodMk contDiffAt_snd))
  obtain ⟨K₁,S₁,hS₁,hK₁⟩ := (qsm A).exists_lipschitzOnWith
  obtain ⟨K₂,S₂,hS₂,hK₂⟩ := (qsm B).exists_lipschitzOnWith
  obtain ⟨L₁,V₁,hV₁,hL₁⟩ := (P.smooth.contDiffAt (x:=1)).exists_lipschitzOnWith
  obtain ⟨L₂,V₂,hV₂,hL₂⟩ := (Q.smooth.contDiffAt (x:=0)).exists_lipschitzOnWith
  let C : ℝ := max ((K₁:ℝ)*L₂) ((K₂:ℝ)*L₁)
  have hC : 0 ≤ C := (mul_nonneg K₁.2 L₂.2).trans (le_max_left _ _)
  refine ⟨C,hC,?_⟩
  filter_upwards [(zL.prodMk_nhds vL) hS₁,(pL.prodMk_nhds vL) hS₁,(zL.prodMk_nhds wL) hS₂,
    (qL.prodMk_nhds wL) hS₂,(continuous_fst.tendsto corner) hV₁,
    (continuous_snd.tendsto corner) hV₂] with k h1 h2 h3 h4 h5 h6
  constructor
  · have hx := hK₁.dist_le_mul _ h1 _ h2
    have hh := hL₂.dist_le_mul _ h6 0 (mem_of_mem_nhds hV₂)
    rw [dist_prod_same_right, Real.dist_eq] at hx
    rw [Real.dist_eq,sub_zero,hq] at hh
    have he : dist (Z k) (P.pos k.1) = dist (Q.pos k.2) y := by
      simp only [Z,patch,dist_eq_norm]
      congr 1
      abel
    rw [he] at hx
    calc
      _ ≤ |H (Z k,v k)-H (P.pos k.1,v k)| := le_abs_self _
      _ ≤ _ := hx
      _ ≤ (K₁:ℝ)*((L₂:ℝ)*|k.2|) := mul_le_mul_of_nonneg_left hh K₁.2
      _ ≤ C*|k.2| := by rw [←mul_assoc]; exact mul_le_mul_of_nonneg_right (le_max_left _ _) (abs_nonneg _)
  · have hx := hK₂.dist_le_mul _ h3 _ h4
    have hh := hL₁.dist_le_mul _ h5 1 (mem_of_mem_nhds hV₁)
    rw [dist_prod_same_right, Real.dist_eq] at hx
    rw [Real.dist_eq,hp] at hh
    have he : dist (Z k) (Q.pos k.2) = dist (P.pos k.1) y := by
      simp only [Z,patch,dist_eq_norm]
      congr 1
      abel
    rw [he] at hx
    calc
      _ ≤ |H (Z k,w k)-H (Q.pos k.2,w k)| := le_abs_self _
      _ ≤ _ := hx
      _ ≤ (K₂:ℝ)*((L₁:ℝ)*|k.1-1|) := mul_le_mul_of_nonneg_left hh K₂.2
      _ ≤ C*|k.1-1| := by rw [←mul_assoc]; exact mul_le_mul_of_nonneg_right (le_max_right _ _) (abs_nonneg _)

private theorem round_window (S : Set E4) (g : CornerBilin) (O : E4→E4) (y : E4) (hdoc : IsOpen S) (hg : SmoothAt g y) (hw : ContinuousAt O y)
    (symm : ∀ z v w, g z v w = g z w v) (P Q : Arc) (hp : P.pos 1=y) (hq : Q.pos 0=y)
    (hP : ∀ s∈J, Okay S g O (P.pos s) (P.vel s)) (hQ : ∀ s∈J, Okay S g O (Q.pos s) (Q.vel s))
    (hcross : g y (P.vel 1) (Q.vel 0) < 0) :
    ∃ d : ℝ, 0 < d ∧ d<1 ∧ ∀ u∈J,
      let s := 1-d*(1-u)^2
      let t := d*u^2
      Okay S g O (P.pos s+Q.pos t-y) ((1-u) • P.vel s + u • Q.vel t) := by
  let Z := patch P Q y
  obtain ⟨c,hc,ho⟩ := orientation_near S g O y hdoc hg hw P Q hp hq hP hQ hcross
  obtain ⟨C,hC,he⟩ := metric_error_near g y hg P Q hp hq
  have near : ∀ᶠ k in 𝓝 corner, OrientedNear S g O P Q y c k ∧ MetricError g P Q y C k := ho.and he
  obtain ⟨r,hr,hrset⟩ := Metric.mem_nhds_iff.mp near
  have hCp : 0<C+1 := by linarith
  obtain ⟨d,hd,hdmax⟩ := exists_between (lt_min (lt_min hr zero_lt_one) (div_pos hc hCp))
  obtain ⟨hdr,hd1⟩ := lt_min_iff.mp (lt_min_iff.mp hdmax).1
  have hCd : C*d ≤ c := by
    have h := (lt_div_iff₀ hCp).mp (lt_min_iff.mp hdmax).2
    nlinarith only [h,hd]
  refine ⟨d,hd,hd1,?_⟩
  intro u hu
  let b := 1-u
  let s := 1-d*b^2
  let t := d*u^2
  have hb0 : 0 ≤ b := sub_nonneg.mpr hu.2
  have hb1 : b ≤ 1 := by dsimp [b]; linarith [hu.1]
  have hu2 : u^2 ≤ 1 := by nlinarith only [mul_nonneg hu.1 (sub_nonneg.mpr hu.2), hu.2]
  have hb2 : b^2 ≤ 1 := by nlinarith only [mul_nonneg hb0 (sub_nonneg.mpr hb1), hb1]
  have hs : s∈J := by
    constructor <;> dsimp [s]
    · linarith only [mul_le_mul_of_nonneg_left hb2 hd.le,hd1]
    · linarith only [mul_nonneg hd.le (sq_nonneg b)]
  have ht : t∈J := ⟨mul_nonneg hd.le (sq_nonneg u),by dsimp [t]; linarith only [mul_le_mul_of_nonneg_left hu2 hd.le,hd1]⟩
  have hm : (s,t)∈Metric.ball ((1:ℝ),(0:ℝ)) r := by
    rw [Metric.mem_ball,Prod.dist_eq,max_lt_iff,Real.dist_eq,Real.dist_eq,sub_zero,
      abs_of_nonpos (sub_nonpos.mpr hs.2),abs_of_nonneg ht.1]
    constructor
    · dsimp [s]; linarith only [mul_le_mul_of_nonneg_left hb2 hd.le,hdr]
    · dsimp [t]; linarith only [mul_le_mul_of_nonneg_left hu2 hd.le,hdr]
  obtain ⟨hOr,hEr⟩ := hrset hm
  obtain ⟨hD,horA,horB,hmix⟩ := hOr
  obtain ⟨heA,heB⟩ := hEr
  let z := Z (s,t)
  let M := g z
  let V := P.vel s
  let V' := Q.vel t
  change M V (O z)<0 at horA
  change M V' (O z)<0 at horB
  change M V V' ≤ -c at hmix
  change M V V - g (P.pos s) V V ≤ C*|t| at heA
  change M V' V' - g (Q.pos t) V' V' ≤ C*|s-1| at heB
  rw [abs_of_nonneg ht.1] at heA
  rw [abs_of_nonpos (sub_nonpos.mpr hs.2)] at heB
  have hA : M V V ≤ C*d*u^2 := by dsimp [t] at heA; nlinarith only [heA,(hP s hs).2.1]
  have hB : M V' V' ≤ C*d*b^2 := by dsimp [s] at heB; nlinarith only [heB,(hQ t ht).2.1]
  have hsym : M V' V = M V V' := symm z V' V
  change Okay S g O z (b • V + u • V')
  refine ⟨hD,?_,?_⟩
  · change M (b • V + u • V') (b • V + u • V') ≤ 0
    simp only [map_add,map_smul,ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,smul_eq_mul,hsym]
    have hbu := mul_nonneg hb0 hu.1
    have hbu1 : b*u ≤ 1 := (mul_le_mul_of_nonneg_left hu.2 hb0).trans (by simpa using hb1)
    have hsmall : C*d*(b*u) ≤ c := (mul_le_mul_of_nonneg_left hbu1 (mul_nonneg hC hd.le)).trans (by simpa using hCd)
    nlinarith only [mul_le_mul_of_nonneg_left hA (sq_nonneg b),mul_le_mul_of_nonneg_left hB (sq_nonneg u),
      mul_le_mul_of_nonneg_left hmix hbu, mul_nonpos_of_nonneg_of_nonpos hbu (sub_nonpos.mpr hsmall)]
  · change M (b • V + u • V') (O z)<0
    simp only [map_add,map_smul,ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,smul_eq_mul]
    by_cases h : u=0
    · simpa [b,h] using horA
    · exact add_neg_of_nonpos_of_neg (mul_nonpos_of_nonneg_of_nonpos hb0 horA.le)
        (mul_neg_of_pos_of_neg (lt_of_le_of_ne hu.1 (Ne.symm h)) horB)

private theorem cartesian_formula (m a e : ℝ) (y : E4) (v w : E4) :
    F m a e y v w = -(v 0*w 0) + v 1*w 1 + v 2*w 2 + v 3*w 3
      + ksProfile m a e y * kEval a y v * kEval a y w := by
  change Matrix.toLinearMap₂' ℝ (kerrNewmanMetric m a e y) (WithLp.ofLp v) (WithLp.ofLp w) = _
  simp only [Matrix.toLinearMap₂'_apply, smul_eq_mul, kerrNewmanMetric, kEval, Fin.sum_univ_four]
  simp [minkowski] <;> ring

theorem causalTransitivity (m a e : ℝ) (hp : IsKerrNewmanBlackHoleParams m a e)
    (T : VecField (kerrNewmanSpacetime a)) (hT : IsTimeOrientation (kerrNewmanMetricField m a e) T) :
    let U := kerrNewmanSpacetime a
    let D := (Subtype.val : U → E4) ⁻¹' innerRadialRegion m a e
    let g := kerrNewmanMetricField m a e
    ∀ p ∈ D, ∀ x ∈ D, ∀ q ∈ D,
      x ∈ causalFuture g T D p → q ∈ causalFuture g T D x → q ∈ causalFuture g T D p := by
  dsimp only
  intro p _ x _ q _ h1 h2
  rcases h1 with hid|⟨α,ha,ha0,ha1⟩
  · rcases mem_singleton_iff.mp hid with rfl
    exact h2
  rcases h2 with hid|⟨β,hb,hb0,hb1⟩
  · rcases mem_singleton_iff.mp hid with rfl
    exact Or.inr ⟨α,ha,ha0,ha1⟩
  let P := fromCurve α ha.1
  let Q := fromCurve β hb.1
  have p0 : P.pos 0=p.val := congrArg Subtype.val ha0
  have p1 : P.pos 1=x.val := congrArg Subtype.val ha1
  have q0 : Q.pos 0=x.val := congrArg Subtype.val hb0
  have q1 : Q.pos 1=q.val := congrArg Subtype.val hb1
  have pG := fromCurve_good m a e T α ha
  have qG := fromCurve_good m a e T β hb
  have ha' : Good m a e T x.val (P.vel 1) := p1 ▸ pG 1 (right_mem_Icc.mpr zero_le_one)
  have hb' : Good m a e T x.val (Q.vel 0) := q0 ▸ qG 0 (left_mem_Icc.mpr zero_le_one)
  rcases directions m a e hp T hT x (P.vel 1) (Q.vel 0) ha' hb' with ⟨c,hc,he⟩|hn
  · exact combine_parallel m a e T P Q p x q p0 p1 q0 q1 (fun s => (α s).property)
      (fun s => (β s).property) pG qG c hc he
  · obtain ⟨d,hd,hd1,hmid⟩ := round_window (innerRadialRegion m a e) (F m a e) (W a T) x.val
      (isOpen_lt continuous_const (continuous_ksRadius a)) (fun b b' => eval_smooth m a e x.val b b' x.property)
      (W_cont m a e T hT x) (fun z v w => by rw [cartesian_formula,cartesian_formula]; ring)
      P Q p1 q0 pG qG hn
    exact combine_round m a e hp T P Q p x q p0 p1 q0 q1 (fun s => (α s).property)
      (fun s => (β s).property) pG qG d hd hd1 hmid

end
end InnerCausalOrder

namespace InnerCompactOrder

open NoHair Set
open scoped ContDiff Manifold BigOperators

noncomputable section

open InnerRadialGeodesics (U D I4 G timeComponent exterior_profile cone_estimates)

private theorem sign_on_interval (f : ℝ → ℝ) (hf : Continuous f)
    (hn : ∀ t ∈ Icc (0 : ℝ) 1, f t ≠ 0) (u v : ℝ) (hu : u ∈ Icc (0 : ℝ) 1) (hv : v ∈ Icc (0 : ℝ) 1) :
    0 < f u ↔ 0 < f v := by
  have imp (s t : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1) (hp : 0 < f s) :
      0 < f t := by
    by_contra! h
    obtain ⟨z, hz, he⟩ := isPreconnected_Icc.intermediate_value ht hs hf.continuousOn
      (show (0:ℝ) ∈ Icc (f t) (f s) from ⟨h,hp.le⟩)
    exact hn z hz he
  exact ⟨imp u v hu hv, imp v u hv hu⟩


private abbrev J := Icc (0:ℝ) 1
private theorem monotone_from_deriv (f d : ℝ → ℝ) (hd : ∀ s, HasDerivAt f (d s) s)
    (h : ∀ s ∈ J, 0 ≤ d s) : MonotoneOn f J := by
  have hf : Differentiable ℝ f := fun s => (hd s).differentiableAt
  exact monotoneOn_of_deriv_nonneg (convex_Icc (0:ℝ) 1) hf.continuous.continuousOn hf.differentiableOn
    (fun s hs => (hd s).deriv.symm ▸ h s (interior_subset hs))


private theorem arc_displacement (m a e : ℝ) (hp : IsKerrNewmanBlackHoleParams m a e)
    (T : VecField (U a)) (hT : IsTimeOrientation (G m a e) T) (γ : ℝ → U a)
    (hγ : IsFutureCausalCurveIn (G m a e) T (D m a e) γ) (s : ℝ) (hs : s∈J) :
    dist (γ s) (γ 0) ≤ 2*|(γ 1).val 0-(γ 0).val 0| := by
  let f : ℝ → E4 := Subtype.val ∘ γ
  let v (t : ℝ) : E4 := velocity γ t
  have hval : ContMDiff I4 I4 1 (Subtype.val : U a → E4) := contMDiff_subtype_val
  have hf : ContDiff ℝ 1 f := (hval.comp hγ.1).contDiff
  have hd (t : ℝ) : fderiv ℝ f t = (mfderiv 𝓘(ℝ, ℝ) I4 γ t : ℝ →L[ℝ] E4) := by
    have h := mfderiv_comp t (hval.mdifferentiableAt (by simp) (x := γ t)) (hγ.1.mdifferentiableAt (by simp))
    have hinc : (mfderiv I4 I4 (Subtype.val : U a → E4) (γ t) : E4 →L[ℝ] E4) =
        ContinuousLinearMap.id ℝ E4 := mfderiv_extChartAt_self (I := I4) (x := γ t)
    rw [hinc] at h
    rw [← mfderiv_eq_fderiv]
    exact h
  have hc (i : Fin 4) : ContDiff ℝ 1 (fun t => f t i) := (EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.comp hf
  have hder (i : Fin 4) (t : ℝ) : HasDerivAt (fun s => f s i) (v t i) t := by
    have h := ((EuclideanSpace.proj (𝕜 := ℝ) i).hasFDerivAt.comp t ((hf.differentiable (by simp) t).hasFDerivAt)).hasDerivAt
    rw [hd] at h
    exact h
  have hcone (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) :
      (∀ i, |v t i| ≤ |v t 0|) ∧ 0 < (v t 0) * timeComponent (T (γ t)) := by
    obtain ⟨hx,hne,hvv,hvw⟩ := hγ.2 t ht
    exact cone_estimates m a e (γ t) (exterior_profile m a e hp _ hx)
      (v t) (T (γ t)) hne hvv hvw (hT.2 _)
  have hne (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) : v t 0 ≠ 0 := by
    have h := (hcone t ht).2
    intro he
    rw [he, zero_mul] at h
    exact (lt_irrefl _) h
  have hcont : Continuous (fun t => v t 0) := by
    have he : (fun t => v t 0) = deriv (fun t => f t 0) := funext (fun t => (hder 0 t).deriv.symm)
    rw [he]
    exact (hc 0).continuous_deriv le_rfl
  let o : ℝ := if 0 < v 0 0 then 1 else -1
  have ho : o=1 ∨ o= -1 := by unfold o; split <;> simp
  have h₀ : (0:ℝ) ∈ J := left_mem_Icc.mpr zero_le_one
  have h₁ : (1:ℝ) ∈ J := right_mem_Icc.mpr zero_le_one
  have hsign (s : ℝ) (hs : s ∈ J) : 0 < o*v s 0 := by
    have he := sign_on_interval (fun t => v t 0) hcont hne 0 s h₀ hs
    unfold o
    split_ifs with h
    · simpa using he.mp h
    · have hh : v s 0 < 0 := lt_of_le_of_ne (le_of_not_gt (fun h' => h (he.mpr h'))) (hne s hs)
      simpa using hh
  have hmag (s : ℝ) (hs : s ∈ J) : |v s 0| = o*v s 0 := by
    have hh := abs_of_pos (hsign s hs)
    rw [abs_mul] at hh
    rcases ho with h|h <;> simpa [h] using hh
  have htmono : MonotoneOn (fun s => o*f s 0) J :=
    monotone_from_deriv _ _ (fun s => (hder 0 s).const_mul o) (fun s hs => (hsign s hs).le)
  have ht01 := htmono h₀ h₁ zero_le_one
  change o*f 0 0 ≤ o*f 1 0 at ht01
  have hclock : o*(f 1 0-f 0 0) = |f 1 0-f 0 0| := by
    rcases ho with h|h <;> rw [h] at ht01 ⊢
    · rw [abs_of_nonneg (by linarith : 0 ≤ f 1 0-f 0 0)]; ring
    · rw [abs_of_nonpos (by linarith : f 1 0-f 0 0 ≤ 0)]; ring
  have hcoords (i : Fin 4) : |f s i-f 0 i| ≤ |f 1 0-f 0 0| := by
    have hplus : MonotoneOn (fun s => o*f s 0+f s i) J :=
      monotone_from_deriv _ _ (fun s => ((hder 0 s).const_mul o).add (hder i s)) (fun s hs => by
        have h := (hcone s hs).1 i
        rw [hmag s hs] at h
        linarith [neg_abs_le (v s i)])
    have hminus : MonotoneOn (fun s => o*f s 0-f s i) J :=
      monotone_from_deriv _ _ (fun s => ((hder 0 s).const_mul o).sub (hder i s)) (fun s hs => by
        have h := (hcone s hs).1 i
        rw [hmag s hs] at h
        linarith [le_abs_self (v s i)])
    have ha := hplus h₀ hs hs.1
    have hb := hminus h₀ hs hs.1
    have hc := htmono hs h₁ hs.2
    beta_reduce at ha hb hc
    change |f s i-f 0 i| ≤ |f 1 0-f 0 0|
    rw [← hclock]
    exact abs_le.mpr ⟨by nlinarith only [ha,hc],by nlinarith only [hb,hc]⟩
  let B := |f 1 0-f 0 0|
  have hb : 0 ≤ B := abs_nonneg _
  have hsq (i : Fin 4) : (f s i-f 0 i)^2 ≤ B^2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hb).mpr (hcoords i)
  change ‖f s-f 0‖ ≤ 2*B
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_four]
  change (f s 0-f 0 0)^2+(f s 1-f 0 1)^2+(f s 2-f 0 2)^2+(f s 3-f 0 3)^2 ≤ _
  nlinarith only [hsq 0,hsq 1,hsq 2,hsq 3]

private theorem restrict_arc (m a e : ℝ) (T : VecField (U a)) (K : Set (U a)) (γ : ℝ → U a)
    (hγ : IsFutureCausalCurveIn (G m a e) T K γ) (l h : ℝ) (hl : 0≤l) (hh : 0<h) (hlh : l+h≤1) :
    IsFutureCausalCurveIn (G m a e) T K (fun s => γ (l+h*s)) := by
  let φ (s : ℝ) := l+h*s
  have hφ : ContMDiff 𝓘(ℝ,ℝ) 𝓘(ℝ,ℝ) 1 φ := contMDiff_iff_contDiff.mpr (by dsimp [φ]; fun_prop)
  refine ⟨hγ.1.comp hφ,?_⟩
  intro s hs
  have hi : φ s ∈ J := ⟨by dsimp [φ]; linarith [mul_nonneg hh.le hs.1],by dsimp [φ]; nlinarith only [hlh,mul_le_mul_of_nonneg_left hs.2 hh.le]⟩
  obtain ⟨hK,hn,hvv,hvT⟩ := hγ.2 (φ s) hi
  have dφ : HasDerivAt φ h s := by simpa [φ] using (((hasDerivAt_id s).const_mul h).const_add l)
  have hvel : (velocity (γ ∘ φ) s : E4) = h • (velocity γ (φ s) : E4) := by
    unfold velocity
    rw [mfderiv_comp s (hγ.1.mdifferentiableAt (by simp)) (hφ.mdifferentiableAt (by simp)),mfderiv_eq_fderiv]
    change mfderiv 𝓘(ℝ,ℝ) I4 γ (φ s) (fderiv ℝ φ s 1) = _
    rw [show fderiv ℝ φ s 1 = h from dφ.deriv]
    let L : ℝ →L[ℝ] E4 := mfderiv 𝓘(ℝ,ℝ) I4 γ (φ s)
    change L h = h • L 1
    simpa only [smul_eq_mul,mul_one] using L.map_smul h (1:ℝ)
  let A := matrixBilin (kerrNewmanMetric m a e (γ (φ s)).val)
  let v : E4 := velocity γ (φ s)
  let w : E4 := T (γ (φ s))
  change v ≠ 0 at hn
  change A v v ≤ 0 at hvv
  change A v w < 0 at hvT
  refine ⟨hK,?_⟩
  change (velocity (γ ∘ φ) s : E4) ≠ 0 ∧ A (velocity (γ ∘ φ) s) (velocity (γ ∘ φ) s) ≤ 0 ∧
    A (velocity (γ ∘ φ) s) w<0
  rw [hvel]
  change (h • v : E4) ≠ 0 ∧ A (h • v) (h • v) ≤ 0 ∧ A (h • v) w < 0
  simp only [map_smul,ContinuousLinearMap.smul_apply,smul_eq_mul]
  exact ⟨smul_ne_zero hh.ne' hn,mul_nonpos_of_nonneg_of_nonpos hh.le (mul_nonpos_of_nonneg_of_nonpos hh.le hvv),
    mul_neg_of_pos_of_neg hh hvT⟩

private def composeRel {X : Type*} (A : Set (X × X)) : Set (X × X) := {z | ∃ x, (z.1,x)∈A ∧ (x,z.2)∈A}

private theorem compact_composition {X : Type*} [TopologicalSpace X] [T2Space X] {A : Set (X × X)}
    (hA : IsCompact A) : IsCompact (composeRel A) := by
  let S : Set ((X×X)×(X×X)) := {z | z.1.2=z.2.1}
  have hs : IsClosed S := isClosed_eq (continuous_snd.comp continuous_fst) (continuous_fst.comp continuous_snd)
  let F (z : (X×X)×(X×X)) := (z.1.1,z.2.2)
  have e : composeRel A = F '' ((A ×ˢ A) ∩ S) := by
    ext z
    constructor
    · rintro ⟨x,h1,h2⟩
      exact ⟨((z.1,x),(x,z.2)),⟨⟨h1,h2⟩,rfl⟩,rfl⟩
    · rintro ⟨⟨⟨p,x⟩,⟨y,q⟩⟩,⟨⟨hx,hy⟩,h⟩,rfl⟩
      change x=y at h
      subst y
      exact ⟨x,hx,hy⟩
  rw [e]
  exact ((hA.prod hA).inter_right hs).image ((continuous_fst.comp continuous_fst).prodMk (continuous_snd.comp continuous_snd))

private def shortRel (m a e : ℝ) (T : VecField (U a)) (K : Set (U a)) (d : ℝ) : Set (U a × U a) :=
  {z | z.1∈K ∧ z.2∈K ∧ z.2∈causalFuture (G m a e) T K z.1 ∧ |z.2.val 0-z.1.val 0|≤d}

private theorem bisect (m a e : ℝ) (T : VecField (U a)) (K : Set (U a)) (d : ℝ) (hd : 0≤d) :
    shortRel m a e T K (2*d) ⊆ composeRel (shortRel m a e T K d) := by
  rintro ⟨p,q⟩ ⟨hp,hq,hj,hlen⟩
  by_cases hshort : |q.val 0-p.val 0|≤d
  · exact ⟨p,⟨hp,hp,Or.inl rfl,by simpa⟩,⟨hp,hq,hj,hshort⟩⟩
  rcases hj with he|⟨γ,hγ,h0,h1⟩
  · have hqp : q = p := Set.mem_singleton_iff.mp he
    exact (hshort (by simpa [hqp] using hd)).elim
  let t (s : ℝ) := (γ s).val 0
  have hc : Continuous t := (PiLp.continuous_apply 2 _ 0).comp (continuous_subtype_val.comp hγ.1.continuous)
  have hne : t 0 ≠ t 1 := by
    intro h
    change (γ 0).val 0 = (γ 1).val 0 at h
    rw [h0,h1] at h
    change p.val 0 = q.val 0 at h
    exact hshort (by rw [h,sub_self,abs_zero]; exact hd)
  let mid := (t 0+t 1)/2
  have hmid : mid ∈ t '' J := by
    rcases le_total (t 0) (t 1) with h|h
    · apply intermediate_value_Icc zero_le_one hc.continuousOn
      exact ⟨by dsimp [mid]; linarith,by dsimp [mid]; linarith⟩
    · apply intermediate_value_Icc' zero_le_one hc.continuousOn
      exact ⟨by dsimp [mid]; linarith,by dsimp [mid]; linarith⟩
  obtain ⟨s,hs,he⟩ := hmid
  have hs0 : 0<s := lt_of_le_of_ne hs.1 (fun h => by
    subst s; dsimp [mid] at he; apply hne; linarith)
  have hs1 : s<1 := lt_of_le_of_ne hs.2 (fun h => by
    subst s; dsimp [mid] at he; apply hne; linarith)
  have hsK := (hγ.2 s hs).1
  have hγa := restrict_arc m a e T K γ hγ 0 s le_rfl hs0 (by linarith)
  have hγb := restrict_arc m a e T K γ hγ s (1-s) hs.1 (by linarith) (by linarith)
  have hpq : |t 1-t 0| ≤ 2*d := by simpa only [t,h0,h1] using hlen
  have hhalf : |(t 1-t 0)/2| ≤ d := by rw [abs_div,abs_of_pos (by norm_num : (0:ℝ)<2)]; linarith
  have ha : t s-t 0=(t 1-t 0)/2 := by rw [he]; dsimp [mid]; ring
  have hb : t 1-t s=(t 1-t 0)/2 := by rw [he]; dsimp [mid]; ring
  refine ⟨γ s,⟨hp,hsK,Or.inr ⟨_,hγa,by simpa using h0,by simp⟩,?_⟩,
    ⟨hsK,hq,Or.inr ⟨_,hγb,by simp,by convert h1 using 2 <;> ring⟩,?_⟩⟩
  · rw [← h0]; change |t s-t 0|≤d; rwa [ha]
  · rw [← h1]; change |t 1-t s|≤d; rwa [hb]

theorem compactLimit (m a e : ℝ) (hp : IsKerrNewmanBlackHoleParams m a e)
    (T : VecField (kerrNewmanSpacetime a)) (hT : IsTimeOrientation (kerrNewmanMetricField m a e) T) :
    let U := kerrNewmanSpacetime a
    let g := kerrNewmanMetricField m a e
    let D := (Subtype.val : U → E4) ⁻¹' innerRadialRegion m a e
    ∀ K : Set U, IsCompact K → K ⊆ D →
      closure {z : U × U | z.1 ∈ K ∧ z.2 ∈ K ∧ z.2 ∈ causalFuture g T K z.1} ⊆
        {z : U × U | z.2 ∈ causalFuture g T D z.1} := by
  dsimp only
  intro K hK hKD
  let R := shortRel m a e T K
  let JD : Set (U a × U a) := {z | z.2 ∈ causalFuture (G m a e) T (D m a e) z.1}
  have hloc (x : K) := InnerLocalOrder.localClosure m a e hp T hT x.val (hKD x.property)
  choose V hOpen hContain hDom hLocal using hloc
  have hc : K ⊆ ⋃ x : K, V x := fun x hx => mem_iUnion.mpr ⟨⟨x,hx⟩,hContain ⟨x,hx⟩⟩
  obtain ⟨δ,hδ,hLeb⟩ := lebesgue_number_lemma_of_metric hK hOpen hc
  let d := δ/8
  have hd : 0<d := by dsimp [d]; linarith
  have hcompact (b : ℝ) : IsCompact (closure (R b)) := (hK.prod hK).of_isClosed_subset isClosed_closure
    (closure_minimal (fun z hz => ⟨hz.1,hz.2.1⟩) (hK.isClosed.prod hK.isClosed))
  have hinside (b : ℝ) : closure (R b) ⊆ K ×ˢ K := closure_minimal (fun z hz => ⟨hz.1,hz.2.1⟩) (hK.isClosed.prod hK.isClosed)
  have hbase : closure (R d) ⊆ JD := by
    intro z hz
    obtain ⟨x,hx⟩ := hLeb z.1 (hinside d hz).1
    have hdist : ∀ y∈R d, dist y.2 y.1 ≤ 2*d := by
      rintro y ⟨_,_,hJ,ht⟩
      rcases hJ with he|⟨γ,hγ,h0,h1⟩
      · rw [Set.mem_singleton_iff.mp he,dist_self]; linarith
      · have hg : IsFutureCausalCurveIn (G m a e) T (D m a e) γ :=
          ⟨hγ.1,fun s hs => ⟨hKD (hγ.2 s hs).1,(hγ.2 s hs).2⟩⟩
        have h := arc_displacement m a e hp T hT γ hg 1 (right_mem_Icc.mpr zero_le_one)
        rw [h0,h1] at h; linarith
    have hs : dist z.2 z.1 ≤ 2*d := (closure_minimal (show R d ⊆ {y | dist y.2 y.1 ≤ 2*d} from hdist)
      (isClosed_le (continuous_snd.dist continuous_fst) continuous_const)) hz
    have hpx : z.1∈V x := hx (Metric.mem_ball_self hδ)
    have hqx : z.2∈V x := hx (show dist z.2 z.1<δ by dsimp [d] at hs; linarith)
    apply hLocal x z hpx hqx
    let N : Set (U a × U a) := {y | dist y.1 z.1 < d}
    have ho : IsOpen N := (Metric.isOpen_ball.preimage continuous_fst)
    have hzn : z ∈ N := by change dist z.1 z.1<d; simpa
    apply closure_mono _ (ho.inter_closure ⟨hzn,hz⟩)
    rintro y ⟨hy,hyR⟩
    change dist y.1 z.1<d at hy
    have near (v : U a) (hv : dist v y.1 ≤ 2*d) : v∈V x := hx (by
      change dist v z.1<δ
      have := dist_triangle v y.1 z.1
      dsimp [d] at hv hy
      linarith)
    refine ⟨near y.1 (by rw [dist_self]; linarith),near y.2 (hdist y hyR),?_⟩
    rcases hyR.2.2.1 with he|⟨γ,hγ,h0,h1⟩
    · exact Or.inl he
    · refine Or.inr ⟨γ,⟨hγ.1,?_⟩,h0,h1⟩
      intro t ht
      have hg : IsFutureCausalCurveIn (G m a e) T (D m a e) γ :=
        ⟨hγ.1,fun s hs => ⟨hKD (hγ.2 s hs).1,(hγ.2 s hs).2⟩⟩
      have hh := arc_displacement m a e hp T hT γ hg t ht
      rw [h0,h1] at hh
      exact ⟨near _ (by linarith [hyR.2.2.2]),(hγ.2 t ht).2⟩
  have hdyadic (n : ℕ) : closure (R ((2:ℝ)^n*d)) ⊆ JD := by
    induction n with
    | zero => simpa using hbase
    | succ n ih =>
      let b := (2:ℝ)^n*d
      have hsup : closure (R (2*b)) ⊆ composeRel (closure (R b)) := by
        apply closure_minimal _ (compact_composition (hcompact b)).isClosed
        intro z hz
        obtain ⟨x,hx,hy⟩ := bisect m a e T K b (by dsimp [b]; positivity) hz
        exact ⟨x,subset_closure hx,subset_closure hy⟩
      intro z hz
      have he : (2:ℝ)^(n+1)*d=2*b := by dsimp [b]; ring
      rw [he] at hz
      obtain ⟨x,hx,hy⟩ := hsup hz
      exact InnerCausalOrder.causalTransitivity m a e hp T hT z.1 (hKD (hinside b hx).1)
        x (hKD (hinside b hx).2) z.2 (hKD (hinside b hy).2) (ih hx) (ih hy)
  have hct : Continuous (fun z : U a => |z.val 0|) := by fun_prop
  obtain ⟨M,hM⟩ := hK.bddAbove_image hct.abs.continuousOn
  have bound (x : U a) (hx : x∈K) : |x.val 0|≤M := by
    simpa using hM (show |(|x.val 0|)| ∈ (fun z : U a => |(|z.val 0|)|) '' K from ⟨x,hx,rfl⟩)
  obtain ⟨n,hn⟩ := pow_unbounded_of_one_lt (2*M/d) (by norm_num : (1:ℝ)<2)
  apply (closure_mono ?_).trans (hdyadic n)
  rintro z ⟨h1,h2,hj⟩
  refine ⟨h1,h2,hj,?_⟩
  have ht := (div_lt_iff₀ hd).mp hn
  linarith [abs_sub (z.2.val 0) (z.1.val 0),bound z.1 h1,bound z.2 h2]

end
end InnerCompactOrder

open NoHair Set

theorem innerCompactLimit :
    let A := {x : kerrNewmanSpacetime 2 | 1 < ksRadius 2 x.val}
    let g := kerrNewmanMetricField (5/2) 2 0
    let T := kerrNewmanTimeDirection (5/2) 2 0
    ∀ K : Set (kerrNewmanSpacetime 2), IsCompact K → K ⊆ A →
      closure {z : (kerrNewmanSpacetime 2) × (kerrNewmanSpacetime 2) |
        z.1 ∈ K ∧ z.2 ∈ K ∧ z.2 ∈ causalFuture g T K z.1} ⊆
        {z | z.2 ∈ causalFuture g T A z.1}  := by
  have hp : IsKerrNewmanBlackHoleParams (5/2) 2 0 := by norm_num [IsKerrNewmanBlackHoleParams]
  have hT := InnerChronology.time_orientation (5/2) 2 0
  simpa only [innerRadialRegion,zero_pow (by decide : 2 ≠ 0),zero_div,max_eq_left (by norm_num : (0:ℝ) ≤ 1),
    Set.preimage_setOf_eq] using InnerCompactOrder.compactLimit (5/2) 2 0 hp (kerrNewmanTimeDirection _ _ _) hT

end

namespace InnerDiamondConfinement
open NoHair NoHair.KNE Set Filter
open scoped Topology
open scoped BigOperators Manifold ContDiff

noncomputable section

open InnerChronology (U)

open InnerChronology (G)

open InnerChronology (T)

open InnerChronology (I4)

open InnerChronology (V3)

open InnerChronology (dot3)

open InnerChronology (space)

open InnerChronology (axis)

open InnerChronology (timeC)

open InnerChronology (dot_symm)

open InnerChronology (dot_add_l)

open InnerChronology (dot_add_r)

open InnerChronology (dot_scale_l)

open InnerChronology (dot_scale_r)

open InnerChronology (dot_cauchy)

open InnerChronology (axis_unit)

open InnerChronology (metric_formula)

open InnerChronology (t_coords)

open InnerChronology (metric_T)

open InnerChronology (radialNormal)

open InnerChronology (normal_geometry)

open InnerChronology (radial_derivative)

private theorem inward (k n s : V3) (f t : ℝ) (hk : dot3 k k = 1)
    (hnk : dot3 n k = 1) (hn : dot3 n n < f) (hf : 0 < f)
    (htime : -t*t + dot3 s s + f*(t+dot3 k s)*(t+dot3 k s) ≤ 0)
    (hfuture : -t+(f/2)*(t+dot3 k s) < 0) : dot3 n s < 0 := by
  let c := f/2
  let l := t+dot3 k s
  let τ := t-c*l
  let u := s+(c*l) • k
  let b := n+(-c) • k
  have hc : 0 < c := by dsimp [c]; linarith
  have hτ : 0 < τ := by dsimp [τ,c,l]; linarith only [hfuture]
  have ff : f=2*c := by dsimp [c]; ring
  have hu : dot3 u u ≤ τ^2 := by
    have h : dot3 u u-τ^2 = -t*t+dot3 s s+f*l*l := by
      simp only [u, τ, l, dot_add_l, dot_add_r, dot_scale_l, dot_scale_r, hk, dot_symm s k]
      rw [ff]
      ring
    change -t*t + dot3 s s + f*l*l ≤ 0 at htime
    linarith only [h,htime]
  have hb : dot3 b b < c^2 := by
    simp only [b, dot_add_l, dot_add_r, dot_scale_l, dot_scale_r, hk, hnk, dot_symm k n]
    rw [ff] at hn
    linarith only [hn]
  have he : dot3 n s = dot3 b u - c*τ := by
    simp only [b, u, τ, l, dot_add_l, dot_add_r, dot_scale_l, dot_scale_r, hnk, hk]
    ring
  have hcs := dot_cauchy b u
  have habs : |dot3 b u| < |c*τ| := sq_lt_sq.mp (by
    rw [mul_pow]
    have hb0 : 0 ≤ dot3 b b := by unfold dot3; exact Finset.sum_nonneg fun i _ => mul_self_nonneg _
    exact hcs.trans_lt ((mul_le_mul_of_nonneg_left hu hb0).trans_lt (mul_lt_mul_of_pos_right hb (sq_pos_of_pos hτ))))
  rw [abs_of_pos (mul_pos hc hτ)] at habs
  rw [he]
  linarith [le_abs_self (dot3 b u)]

private theorem shell_velocity (x : U 2) (hl : 1 < ksRadius 2 x.val) (hu : ksRadius 2 x.val < 4)
    (v : E4) (hv : IsFutureCausal (G (5/2) 2 0) (T (5/2) 2 0) x v) :
    fderiv ℝ (ksRadius 2) x.val v < 0 := by
  obtain ⟨_,h1,h2⟩ := hv
  rw [metric_formula] at h1
  rw [metric_T] at h2
  obtain ⟨hnk,hn⟩ := normal_geometry 2 x
  let r := ksRadius 2 x.val
  have hr : 0 < r := x.property
  have hW : 0 < Wf 2 x.val := by unfold Wf; positivity
  have hgap : r^2+(2:ℝ)^2 < 2*(5/2)*r-0^2 := by
    change 1<r at hl
    change r<4 at hu
    nlinarith only [mul_pos (sub_pos.mpr hl) (sub_pos.mpr hu)]
  have hF : ksProfile (5/2) 2 0 x.val=(2*(5/2)*r-0^2)*Wf 2 x.val := profile_eq _ _ _ _ x.property
  have hnlt : dot3 (radialNormal 2 x.val) (radialNormal 2 x.val) < ksProfile (5/2) 2 0 x.val := by
    rw [hn,hF]
    exact mul_lt_mul_of_pos_right hgap hW
  have hFp : 0 < ksProfile (5/2) 2 0 x.val := by rw [hF]; simp only [zero_pow (by decide : 2 ≠ 0),sub_zero]; positivity
  rw [radial_derivative]
  apply inward (axis 2 x.val) (radialNormal 2 x.val) (space v) (ksProfile (5/2) 2 0 x.val) (timeC v)
    (axis_unit 2 x) hnk hnlt hFp _ h2
  simpa only [neg_mul] using h1

private abbrev Reg := {x : kerrNewmanSpacetime 2 | 1 < ksRadius 2 x.val}
private abbrev Met := kerrNewmanMetricField (5/2) 2 0
private abbrev Orient := kerrNewmanTimeDirection (5/2) 2 0
private abbrev UnitInterval := Icc (0:ℝ) 1

private def component (v : E4) (i : Fin 4) : ℝ := v i

private theorem clock_data (γ : ℝ → kerrNewmanSpacetime 2)
    (hγ : IsFutureCausalCurveIn Met Orient Reg γ) :
    (∀ i : Fin 4, ∀ t, HasDerivAt (fun s => (γ s).val i) (component (velocity γ t) i) t) ∧
      ∀ t∈UnitInterval, 0 < component (velocity γ t) 0 ∧ ∀ i : Fin 4, |component (velocity γ t) i| ≤ component (velocity γ t) 0 := by
  let f : ℝ → E4 := Subtype.val ∘ γ
  let I4 := 𝓘(ℝ,E4)
  have hval : ContMDiff I4 I4 1 (Subtype.val : kerrNewmanSpacetime 2 → E4) := contMDiff_subtype_val
  have hf : ContDiff ℝ 1 f := (hval.comp hγ.1).contDiff
  constructor
  · intro i t
    have hd := ((hf.differentiable_one t).hasFDerivAt).hasDerivAt
    have he := InnerRadialGeodesics.ambient_velocity 2 γ hγ.1 t (deriv f t) hd
    have hi := (EuclideanSpace.proj (𝕜 := ℝ) i).hasFDerivAt.comp_hasDerivAt t hd
    rw [he]
    exact hi
  · intro t ht
    let x := γ t
    have hr : 0 < ksRadius 2 x.val := x.property
    have hF : 0 ≤ ksProfile (5/2) 2 0 x.val := by
      unfold ksProfile
      simp only [zero_pow (by decide : 2 ≠ 0),sub_zero]
      positivity
    have hdir : 0 < component (Orient x) 0 := by change 0 < 1+ksProfile (5/2) 2 0 x.val/2; linarith
    obtain ⟨_,hn,hv,hfut⟩ := hγ.2 t ht
    have hp : IsKerrNewmanBlackHoleParams (5/2) 2 0 := by norm_num [IsKerrNewmanBlackHoleParams]
    have htime := InnerChronology.time_orientation (5/2) 2 0
    obtain ⟨hb,hs⟩ := InnerRadialGeodesics.cone_estimates (5/2) 2 0 x hF
      (velocity γ t) (Orient x) hn hv hfut (htime.2 x)
    have hpos : 0 < component (velocity γ t) 0 := by
      by_contra! h
      exact (not_lt_of_ge (mul_nonpos_of_nonpos_of_nonneg h hdir.le)) hs
    exact ⟨hpos,fun i => (hb i).trans_eq (abs_of_pos hpos)⟩

private theorem clock_strict (γ : ℝ → kerrNewmanSpacetime 2)
    (hγ : IsFutureCausalCurveIn Met Orient Reg γ) : StrictMonoOn (fun s => (γ s).val 0) UnitInterval := by
  obtain ⟨hd,hv⟩ := clock_data γ hγ
  exact strictMonoOn_of_deriv_pos (convex_Icc 0 1) (fun t _ => (hd 0 t).continuousAt.continuousWithinAt)
    (fun t ht => (hd 0 t).deriv.symm ▸ (hv t (interior_subset ht)).1)

private theorem backwards_barrier (b : ℝ) (hb1 : 1<b) (hb4 : b<4)
    (γ : ℝ → U 2) (hγ : IsFutureCausalCurveIn Met Orient Reg γ)
    (hlast : b<ksRadius 2 (γ 1).val) (t : ℝ) (ht : t ∈ UnitInterval) : b<ksRadius 2 (γ t).val := by
  by_contra! hbad
  let z : ℝ → E4 := Subtype.val ∘ γ
  let h (s : ℝ) := ksRadius 2 (z s)
  let d (s : ℝ) := fderiv ℝ (ksRadius 2) (z s) (velocity γ s)
  have hval : ContMDiff I4 I4 1 (Subtype.val : U 2 → E4) := contMDiff_subtype_val
  have hz : ContDiff ℝ 1 z := (hval.comp hγ.1).contDiff
  have deriv (s : ℝ) : HasDerivAt h (d s) s := by
    have hcomp := mfderiv_comp s (hval.mdifferentiableAt (by simp) (x := γ s)) (hγ.1.mdifferentiableAt (by simp))
    have hinc : (mfderiv I4 I4 (Subtype.val : U 2 → E4) (γ s) : E4 →L[ℝ] E4) =
        ContinuousLinearMap.id ℝ E4 := mfderiv_extChartAt_self (I := I4) (x := γ s)
    rw [hinc] at hcomp
    have hh : fderiv ℝ z s = (mfderiv 𝓘(ℝ,ℝ) I4 γ s : ℝ →L[ℝ] E4) := by
      rw [← mfderiv_eq_fderiv]
      exact hcomp
    have hv := ((hz.differentiable (by simp) s).hasFDerivAt).hasDerivAt
    rw [hh] at hv
    exact (ksRadius_differentiableAt 2 (z s) (γ s).property).hasFDerivAt.comp_hasDerivAt s hv
  have fence := image_le_of_deriv_right_lt_deriv_boundary (f := h) (f' := d)
    (B := fun _ => b) (B' := fun _ => 0) (a := t) (b := 1)
    ((continuous_ksRadius 2).comp hz.continuous).continuousOn (fun s _ => (deriv s).hasDerivWithinAt) hbad
    (fun s => hasDerivAt_const s b)
    (fun s hs he => shell_velocity (γ s) (by change 1<h s; rwa [he]) (by change h s<4; rwa [he]) (velocity γ s)
      (hγ.2 s ⟨ht.1.trans hs.1, hs.2.le⟩).2)
  exact hlast.not_ge (fence (right_mem_Icc.mpr ht.2))

private theorem coordinate_bound (γ : ℝ → U 2) (hγ : IsFutureCausalCurveIn Met Orient Reg γ)
    (t : ℝ) (ht : t ∈ UnitInterval) (i : Fin 4) :
    |(γ t).val i-(γ 0).val i| ≤ (γ 1).val 0-(γ 0).val 0 := by
  let f (t : ℝ) := (γ t).val
  let v (t : ℝ) : E4 := velocity γ t
  obtain ⟨hd,hv⟩ := clock_data γ hγ
  have mono (j d : ℝ → ℝ) (hj : ∀ s, HasDerivAt j (d s) s) (h : ∀ s∈UnitInterval, 0 ≤ d s) :
      MonotoneOn j UnitInterval := by
    have hdiff : Differentiable ℝ j := fun s => (hj s).differentiableAt
    exact monotoneOn_of_deriv_nonneg (convex_Icc 0 1) hdiff.continuous.continuousOn hdiff.differentiableOn
      (fun s hs => (hj s).deriv.symm ▸ h s (interior_subset hs))
  have hplus : MonotoneOn (fun s => f s 0 + f s i) UnitInterval :=
    mono _ _ (fun s => (hd 0 s).add (hd i s)) fun s hs => by
      have hh := (abs_le.mp ((hv s hs).2 i)).1
      change 0 ≤ v s 0+v s i
      change -(v s 0) ≤ v s i at hh
      linarith
  have hminus : MonotoneOn (fun s => f s 0-f s i) UnitInterval :=
    mono _ _ (fun s => (hd 0 s).sub (hd i s)) fun s hs => sub_nonneg.mpr (abs_le.mp ((hv s hs).2 i)).2
  have h0 : (0:ℝ) ∈ UnitInterval := left_mem_Icc.mpr zero_le_one
  have h1 : (1:ℝ) ∈ UnitInterval := right_mem_Icc.mpr zero_le_one
  have ha := hplus h0 ht ht.1
  have hb := hminus h0 ht ht.1
  have hc := (clock_strict γ hγ).monotoneOn ht h1 ht.2
  change f t 0 ≤ f 1 0 at hc
  change |f t i-f 0 i| ≤ f 1 0-f 0 0
  beta_reduce at ha hb
  exact abs_le.mpr ⟨by linarith only [ha,hc],by linarith only [hb,hc]⟩

private theorem leg (p q : U 2) (b : ℝ) (hb : 1<b) (hb' : b<4) (hq : b<ksRadius 2 q.val)
    (hJ : q∈causalFuture Met Orient Reg p) :
    b<ksRadius 2 p.val ∧ p.val 0 ≤ q.val 0 ∧ (∀ i : Fin 4, |q.val i-p.val i| ≤ q.val 0-p.val 0) ∧
    ∀ K : Set (U 2), (∀ z : U 2, b < ksRadius 2 z.val → (∀ i : Fin 4, |z.val i-p.val i| ≤ q.val 0-p.val 0) → z∈K) →
      q ∈ causalFuture Met Orient K p := by
  rcases hJ with he | ⟨γ,hγ,h0,h1⟩
  · rcases mem_singleton_iff.mp he with rfl
    exact ⟨hq,le_rfl,fun i => by simp,fun K _ => Or.inl rfl⟩
  have hzero : (0:ℝ) ∈ UnitInterval := left_mem_Icc.mpr zero_le_one
  have hone : (1:ℝ) ∈ UnitInterval := right_mem_Icc.mpr zero_le_one
  have hr := backwards_barrier b hb hb' γ hγ (by rwa [h1])
  have hrp := hr 0 hzero
  have htime := (clock_strict γ hγ).monotoneOn hzero hone zero_le_one
  change (γ 0).val 0 ≤ (γ 1).val 0 at htime
  rw [h0,h1] at htime
  rw [h0] at hrp
  have hc (s) (hs : s∈UnitInterval) (i : Fin 4) := coordinate_bound γ hγ s hs i
  simp only [h0,h1] at hc
  refine ⟨hrp,htime,fun i => by simpa only [h1] using hc 1 hone i,?_⟩
  intro K put
  exact Or.inr ⟨γ,⟨hγ.1,fun s hs => ⟨put _ (hr s hs) (hc s hs),(hγ.2 s hs).2⟩⟩,h0,h1⟩

theorem proved :
    let A := {x : kerrNewmanSpacetime 2 | 1 < ksRadius 2 x.val}
    let g := kerrNewmanMetricField (5/2) 2 0
    let T := kerrNewmanTimeDirection (5/2) 2 0
    ∀ p ∈ A, ∀ q ∈ A, ∃ K : Set (kerrNewmanSpacetime 2), IsCompact K ∧ K ⊆ A ∧ p ∈ K ∧ q ∈ K ∧
      ∀ x ∈ causalFuture g T A p ∩ causalPast g T A q,
        x ∈ K ∧ x ∈ causalFuture g T K p ∧ q ∈ causalFuture g T K x  := by
  dsimp only
  intro p hp q hq
  let r := fun x : U 2 => ksRadius 2 x.val
  let b := min 2 ((min (r p) (r q)+1)/2)
  have hmin : 1 < min (r p) (r q) := lt_min hp hq
  have hb : 1<b := lt_min (by norm_num) (by linarith)
  have hb' : b<4 := (min_le_left _ _).trans_lt (by norm_num)
  have hbelow : b < min (r p) (r q) := (min_le_right _ _).trans_lt (by linarith)
  have hbp := hbelow.trans_le (min_le_left _ _)
  have hbq := hbelow.trans_le (min_le_right _ _)
  let B := |q.val 0-p.val 0|
  let C (i : Fin 4) := |q.val i-p.val i|+2*B+1
  let box : Set (Fin 4 → ℝ) := Icc (fun i => p.val i-C i) (fun i => p.val i+C i)
  let H : Set E4 := (WithLp.toLp 2 '' box) ∩ {z | b ≤ ksRadius 2 z}
  let K := (Subtype.val : U 2 → E4) ⁻¹' H
  have hB : 0 ≤ B := abs_nonneg _
  have hC (i : Fin 4) : 2*B ≤ C i := by dsimp [C]; linarith [abs_nonneg (q.val i-p.val i)]
  have hH : IsCompact H := ((show IsCompact box from isCompact_Icc).image (PiLp.continuous_toLp 2 _)).inter_right
    (isClosed_le continuous_const (continuous_ksRadius 2))
  have hcompact : IsCompact K := by
    apply Subtype.isCompact_iff.mpr
    have himg : (Subtype.val : U 2 → E4) '' K = H := by
      ext z
      constructor
      · rintro ⟨x,hx,rfl⟩; exact hx
      · intro hz
        exact ⟨⟨z,(zero_lt_one.trans hb).trans_le hz.2⟩,hz,rfl⟩
    rwa [himg]
  have put (x : U 2) (hw : b ≤ r x) (h : ∀ i : Fin 4, |x.val i-p.val i| ≤ C i) : x∈K := by
    refine ⟨⟨WithLp.ofLp x.val,⟨?_,?_⟩,rfl⟩,hw⟩
    · intro i; have ha := (abs_le.mp (h i)).1; change p.val i-C i ≤ x.val i; linarith
    · intro i; have ha := (abs_le.mp (h i)).2; change x.val i ≤ p.val i+C i; linarith
  have hpK := put p hbp.le (fun i => by simp only [sub_self,abs_zero]; linarith [hC i])
  have hqK := put q hbq.le (fun i => by dsimp [C]; linarith)
  refine ⟨K,hcompact,fun x hx => hb.trans_le hx.2,hpK,hqK,?_⟩
  intro x hx
  obtain ⟨hbx,hxq,_,hqleg⟩ := leg x q b hb hb' hbq hx.2
  obtain ⟨_,hpx,hxi,hpleg⟩ := leg p x b hb hb' hbx hx.1
  have hdiff : q.val 0-p.val 0 ≤ B := le_abs_self _
  refine ⟨put x hbx.le (fun i => by linarith only [hxi i,hxq,hdiff,hC i,hB]),hpleg K ?_,hqleg K ?_⟩
  · intro z hz hi
    exact put z hz.le fun i => by linarith only [hi i,hxq,hdiff,hC i,hB]
  · intro z hz hi
    apply put z hz.le
    intro i
    have ht : |z.val i-p.val i| ≤ |z.val i-x.val i|+|x.val i-p.val i| := by
      simpa only [Real.dist_eq] using dist_triangle (z.val i) (x.val i) (p.val i)
    linarith only [ht,hi i,hxi i,hdiff,hC i,hB]
end
end InnerDiamondConfinement

namespace InnerGlobalHyperbolicity
open NoHair Set
open scoped Manifold ContDiff Topology
noncomputable section

open InnerDiamondConfinement (Reg)

open InnerDiamondConfinement (Met)

open InnerDiamondConfinement (Orient)

open InnerDiamondConfinement (UnitInterval)

open InnerDiamondConfinement (component)

open InnerDiamondConfinement (clock_data)

open InnerDiamondConfinement (clock_strict)

theorem proved :
    let A := {x : kerrNewmanSpacetime 2 | 1 < ksRadius 2 x.val}
    let g := kerrNewmanMetricField (5/2) 2 0
    let T := kerrNewmanTimeDirection (5/2) 2 0
    IsGloballyHyperbolicOn g T A  := by
  dsimp only
  constructor
  · intro p _ he
    obtain ⟨γ,hγ,h0,h1⟩ := he
    have h := clock_strict γ hγ (left_mem_Icc.mpr zero_le_one) (right_mem_Icc.mpr zero_le_one) zero_lt_one
    change (γ 0).val 0 < (γ 1).val 0 at h
    rw [h0,h1] at h
    exact (lt_irrefl _) h
  intro p hpD q hqD
  let E := causalFuture Met Orient Reg p ∩ causalPast Met Orient Reg q
  obtain ⟨K,hK,hKD,hpK,hqK,hconf⟩ := InnerDiamondConfinement.proved p hpD q hqD
  let J : Set ((kerrNewmanSpacetime 2) × (kerrNewmanSpacetime 2)) := {z | z.1 ∈ K ∧ z.2 ∈ K ∧ z.2 ∈ causalFuture Met Orient K z.1}
  let B : Set (kerrNewmanSpacetime 2) := (fun x => (p,x)) ⁻¹' closure J ∩ (fun x => (x,q)) ⁻¹' closure J
  have hB : IsClosed B := (isClosed_closure.preimage (continuous_const.prodMk continuous_id)).inter
    (isClosed_closure.preimage (continuous_id.prodMk continuous_const))
  have hlim := innerCompactLimit K hK hKD
  have hE : E = K ∩ B := by
    ext x
    constructor
    · intro hx
      obtain ⟨hxK,hpx,hxq⟩ := hconf x hx
      exact ⟨hxK,subset_closure (show (p,x) ∈ J from ⟨hpK,hxK,hpx⟩),
        subset_closure (show (x,q) ∈ J from ⟨hxK,hqK,hxq⟩)⟩
    · rintro ⟨_,hx,hx'⟩
      exact ⟨hlim (show (p,x) ∈ closure J from hx),hlim (show (x,q) ∈ closure J from hx')⟩
  change IsCompact E
  rw [hE]
  exact hK.inter_right hB
end
end InnerGlobalHyperbolicity

namespace InnerCausality
open NoHair Set

theorem proved :
    let A := {x : kerrNewmanSpacetime 2 | 1 < ksRadius 2 x.val}
    let g := kerrNewmanMetricField (5/2) 2 0
    ∃ T : VecField (kerrNewmanSpacetime 2), IsTimeOrientation g T ∧
      chronoPastSet g T A = A ∧ A ⊆ chronoFutureSet g T A ∧ IsGloballyHyperbolicOn g T A := by
  have hp : IsKerrNewmanBlackHoleParams (5/2) 2 0 := by norm_num [IsKerrNewmanBlackHoleParams]
  obtain ⟨hPast,hFuture⟩ := InnerChronology.proved
  exact ⟨kerrNewmanTimeDirection (5/2) 2 0,InnerChronology.time_orientation (5/2) 2 0,
    hPast,hFuture,InnerGlobalHyperbolicity.proved⟩

end InnerCausality

namespace InnerWitness
open NoHair Set
open scoped ContDiff Manifold

theorem proved :
    let g := (kerrNewmanMetricField (5/2) 2 0)
    let F := (kerrNewmanFieldField 2 0)
    ∃ (T : VecField (kerrNewmanSpacetime 2))
      (φ : ℝ → kerrNewmanSpacetime 2 → kerrNewmanSpacetime 2)
      (E : AsymptoticallyFlatEnd g F φ),
      IsStationaryBlackHole g F T φ E ∧ (∀ x, F x = 0) ∧ IsAnalyticBilinField g ∧
      IsNondegenerateHorizon g F (futureEventHorizon g T E.region)
        (domainOfOuterCommunications g T E.region) ∧
      ¬ ∃ μ b : ℝ, IsKerrNewmanBlackHoleParams μ b 0 ∧
        IsKerrNewmanDOC g F (domainOfOuterCommunications g T E.region) μ b 0 := by
  let g := kerrNewmanMetricField (5/2) 2 0
  let F := kerrNewmanFieldField 2 0
  let A := {x : kerrNewmanSpacetime 2 | 1 < ksRadius 2 x.val}
  have hp : IsKerrNewmanBlackHoleParams (5/2) 2 0 := by norm_num [IsKerrNewmanBlackHoleParams]
  have hlor := InnerRegularity.lorentz (5/2) 2 0
  obtain ⟨φ,hφ,hsym⟩ := InnerTimeFlow.stationary_translation (5/2) 2 0
  obtain ⟨E,hE⟩ := InnerAsymptoticEnd.proved φ hφ
  obtain ⟨T,hT,hP,hF,hGH⟩ := InnerCausality.proved
  obtain ⟨han,hB,hC,hn⟩ := InnerHorizonGeometry.proved
  have hD : domainOfOuterCommunications g T E.region = A := by
    rw [domainOfOuterCommunications,hE,hP]
    exact inter_eq_right.mpr hF
  have hH : futureEventHorizon g T E.region=frontier A := by rw [futureEventHorizon,hE,hP]
  have hmat (y : E4) : kerrNewmanField 2 0 y = 0 := by
    ext μ ν
    simp [kerrNewmanField,coordPartial,kerrNewmanPotential]
  have hzero (x : kerrNewmanSpacetime 2) : F x=0 := by
    change matrixBilin (kerrNewmanField 2 0 x.val)=0
    rw [hmat]
    ext v w
    simp [matrixBilin,Matrix.toLinearMap₂'_apply]
  have hmetric : IsSmoothBilinField g :=
    fun c hc i j => (han c hc i j).of_le (by simp)
  have hfield : IsSmoothBilinField F := by
    intro c _ i j
    have hcoeff : (fun y : E4 => pullbackCoeffs F c.symm y i j) = fun _ => 0 := by
      funext y
      simp [pullbackCoeffs, hzero]
    rw [hcoeff]
    exact contDiffOn_const
  have hev (y : E4) (hy : 0<ksRadius 2 y) :
      EinsteinMaxwellAt (kerrNewmanMetric (5/2) 2 0) (kerrNewmanField 2 0) y := by
    refine ⟨hcrCoordinateEinstein y hy,?_,?_⟩
    · intro ν
      simp [raiseBoth,hmat,coordPartial]
    · intro l μ ν
      simp [hmat,coordPartial]
  have hbh : IsStationaryBlackHole g F T φ E :=
    { lorentzian := hlor
      smooth_metric := hmetric
      smooth_field := hfield
      twoForm := by intro x v w; rw [hzero]; simp
      timeOrientation := hT
      electrovac := InnerChartEquations.proved (kerrNewmanSpacetime 2) (kerrNewmanMetric (5/2) 2 0) (kerrNewmanField 2 0) hev
      stationary := hsym
      globallyHyperbolic := hD.symm ▸ hGH
      blackHole_nonempty := by rw [blackHoleRegion,hE,hP]; exact hB
      horizon_connected := hH.symm ▸ hC }
  refine ⟨T,φ,E,hbh,hzero,han,?_,?_⟩
  · rw [hH,hD]; exact hn
  · rintro ⟨μ,b,hp',hdoc⟩
    change IsKerrNewmanDOC g F (domainOfOuterCommunications g T E.region) μ b 0 at hdoc
    rw [hD] at hdoc
    exact InnerTrappedObservers.proved μ b hp' hdoc

end InnerWitness


open NoHair Set
open scoped ContDiff Manifold BigOperators

theorem solution : ¬ (∀ {M : Type} [TopologicalSpace M] [ChartedSpace E4 M]
    [IsManifold 𝓘(ℝ,E4) ∞ M] [IsManifold 𝓘(ℝ,E4) ω M]
    (g F : BilinField M) (T : VecField M) (φ : ℝ → M → M) (E : AsymptoticallyFlatEnd g F φ),
    IsStationaryBlackHole g F T φ E → (∀ x, F x = 0) → IsAnalyticBilinField g →
      IsNondegenerateHorizon g F (futureEventHorizon g T E.region)
        (domainOfOuterCommunications g T E.region) →
      ∃ m a : ℝ, IsKerrNewmanBlackHoleParams m a 0 ∧
        IsKerrNewmanDOC g F (domainOfOuterCommunications g T E.region) m a 0) := by
  intro uniqueness
  obtain ⟨T,φ,E,h,hvac,han,hnd,hfalse⟩ := InnerWitness.proved
  exact hfalse (uniqueness _ _ T φ E h hvac han hnd)
