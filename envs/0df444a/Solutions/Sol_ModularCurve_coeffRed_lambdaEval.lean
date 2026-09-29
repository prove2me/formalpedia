-- Prove2me | solution 1 for ModularCurve.coeffRed_lambdaEval
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/e737fc6c-738d-5c88-be60-41d651e79b72

import Mathlib
import Definitions.Def_ModularCurve_LambdaNodeLocalized
import Definitions.Def_ModularCurve_CharPReduction
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_coeffRed_lambdaEval

set_option autoImplicit false

p2m_open "ModularCurve P2MW.S_ModularCurve_coeffRed_lambdaEval.ModularCurve ModularCurve.LambdaNodeLocalized ModularCurve.CharPReduction"

namespace ModularCurve
p2m_export "ModularCurve" "LambdaNodeLocalized.lambdaEval CharPReduction.integralCoeffs CharPReduction.coeffRed qExpand_coeff_mul qExpand_coeff_of_not_dvd lambdaInt lambdaModC lambdaNModC laurentMap_coeff"
namespace RedLambda
p2m_open "ModularCurve"

variable {L : Type*} [Field L] (A : Subring L) {k : Type*} [Field k] (red : A →+* k)

theorem algebraMap_eq_single {F : Type*} [Field F] (c : F) : algebraMap F (LaurentSeries F) c = HahnSeries.single 0 c := by
  ext m
  rw [HahnSeries.algebraMap_apply', show algebraMap F (PowerSeries F) c = PowerSeries.C c from by simp, HahnSeries.ofPowerSeries_C]
  rfl

theorem coeff_lambdaModC (F : Type*) [CommRing F] (n : ℤ) : (lambdaModC F).coeff n = ((lambdaInt.coeff n : ℤ) : F) := by
  rw [lambdaModC, laurentMap_coeff, eq_intCast]

theorem lambdaModC_mem : lambdaModC L ∈ integralCoeffs A := by
  intro n
  rw [coeff_lambdaModC]
  exact intCast_mem A _

theorem lambdaNModC_mem (N : ℕ) [NeZero N] : lambdaNModC L N ∈ integralCoeffs A := by
  intro n
  by_cases h : ((N : ℕ) : ℤ) ∣ n
  · obtain ⟨m, rfl⟩ := h
    rw [lambdaNModC, qExpand_coeff_mul]
    exact lambdaModC_mem A m
  · rw [lambdaNModC, qExpand_coeff_of_not_dvd _ _ h]
    exact A.zero_mem

theorem lambdaEval_mem (N : ℕ) [NeZero N] (p : MvPolynomial (Fin 2) A) : lambdaEval N A p ∈ integralCoeffs A := by
  induction p using MvPolynomial.induction_on with
  | C a => rw [lambdaEval, MvPolynomial.eval₂Hom_C]; exact constSeries_mem_integralCoeffs A a
  | add p q hp hq => rw [map_add]; exact (integralCoeffs A).add_mem hp hq
  | mul_X p i hp =>
    rw [map_mul, lambdaEval, MvPolynomial.eval₂Hom_X']
    refine (integralCoeffs A).mul_mem hp ?_
    fin_cases i
    · exact lambdaModC_mem A
    · exact lambdaNModC_mem A N

theorem red_mk_eq (x : L) (hx : x ∈ A) (y : A) (h : x = (y : L)) : red ⟨x, hx⟩ = red y := by
  congr 1; exact Subtype.ext h

theorem red_intCast (m : ℤ) (h : ((m : ℤ) : L) ∈ A) : red ⟨(m : L), h⟩ = (m : k) := by
  have : (⟨(m : L), h⟩ : A) = (m : A) := Subtype.ext (by push_cast; rfl)
  rw [this, map_intCast]

theorem coeffRed_lambdaModC : coeffRed A red ⟨lambdaModC L, lambdaModC_mem A⟩ = lambdaModC k := by
  ext n
  rw [coeffRed_coeff, red_mk_eq A red _ _ ((lambdaInt.coeff n : ℤ) : A) (by show (lambdaModC L).coeff _ = _; rw [coeff_lambdaModC]; push_cast; rfl),
    map_intCast, coeff_lambdaModC]

theorem coeffRed_lambdaNModC (N : ℕ) [NeZero N] : coeffRed A red ⟨lambdaNModC L N, lambdaNModC_mem A N⟩ = lambdaNModC k N := by
  ext n
  rw [coeffRed_coeff]
  by_cases h : ((N : ℕ) : ℤ) ∣ n
  · obtain ⟨m, rfl⟩ := h
    rw [red_mk_eq A red _ _ ((lambdaInt.coeff m : ℤ) : A)
        (by show (lambdaNModC L N).coeff _ = _; rw [lambdaNModC, qExpand_coeff_mul, coeff_lambdaModC]; push_cast; rfl),
      map_intCast, lambdaNModC, qExpand_coeff_mul, coeff_lambdaModC]
  · rw [red_mk_eq A red _ _ (0 : A) (by show (lambdaNModC L N).coeff _ = _; rw [lambdaNModC, qExpand_coeff_of_not_dvd _ _ h]; rfl), map_zero,
      lambdaNModC, qExpand_coeff_of_not_dvd _ _ h]

theorem coeffRed_constSeries (a : A) :
    coeffRed A red ⟨constSeries A a, constSeries_mem_integralCoeffs A a⟩ = algebraMap k (LaurentSeries k) (red a) := by
  ext n
  rw [coeffRed_coeff, algebraMap_eq_single, HahnSeries.coeff_single]
  have hc : ∀ m : ℤ, (constSeries A a).coeff m = if m = 0 then (a : L) else 0 := fun m => by
    show (algebraMap L (LaurentSeries L) (a : L)).coeff m = _
    rw [algebraMap_eq_single, HahnSeries.coeff_single]
    split_ifs <;> rfl
  by_cases hn : n = 0
  · subst hn
    rw [if_pos rfl, red_mk_eq A red _ _ a (by show (constSeries A a).coeff 0 = _; rw [hc, if_pos rfl])]
  · rw [if_neg hn, red_mk_eq A red _ _ (0 : A) (by show (constSeries A a).coeff n = _; rw [hc, if_neg hn]; rfl), map_zero]

theorem main (N : ℕ) [NeZero N] (p : MvPolynomial (Fin 2) A) :
    ∃ hp : lambdaEval N A p ∈ integralCoeffs A,
      coeffRed A red ⟨lambdaEval N A p, hp⟩
        = MvPolynomial.eval₂Hom ((algebraMap k (LaurentSeries k)).comp red) ![lambdaModC k, lambdaNModC k N] p := by
  refine ⟨lambdaEval_mem A N p, ?_⟩
  set F : MvPolynomial (Fin 2) A →+* LaurentSeries k :=
    (coeffRed A red).comp ((lambdaEval N A).codRestrict (integralCoeffs A) (lambdaEval_mem A N)) with hF
  have hFp : F p = coeffRed A red ⟨lambdaEval N A p, lambdaEval_mem A N p⟩ := rfl
  rw [← hFp]
  have hFE : F = MvPolynomial.eval₂Hom ((algebraMap k (LaurentSeries k)).comp red) ![lambdaModC k, lambdaNModC k N] := by
    refine MvPolynomial.ringHom_ext (fun a => ?_) (fun i => ?_)
    · rw [MvPolynomial.eval₂Hom_C]
      show coeffRed A red ⟨lambdaEval N A (MvPolynomial.C a), lambdaEval_mem A N _⟩ = algebraMap k (LaurentSeries k) (red a)
      rw [← coeffRed_constSeries A red a]
      congr 1
      exact Subtype.ext (by simp [lambdaEval])
    · rw [MvPolynomial.eval₂Hom_X']
      fin_cases i
      · show coeffRed A red ⟨lambdaEval N A (MvPolynomial.X 0), lambdaEval_mem A N _⟩ = lambdaModC k
        rw [← coeffRed_lambdaModC A red]
        congr 1
        exact Subtype.ext (by simp [lambdaEval])
      · show coeffRed A red ⟨lambdaEval N A (MvPolynomial.X 1), lambdaEval_mem A N _⟩ = lambdaNModC k N
        rw [← coeffRed_lambdaNModC A red N]
        congr 1
        exact Subtype.ext (by simp [lambdaEval])
  rw [hFE]

end ModularCurve.RedLambda

theorem solution (N : ℕ) [NeZero N] {L : Type*} [Field L] (A : Subring L)
    {k : Type*} [Field k] (red : A →+* k) (p : MvPolynomial (Fin 2) A) :
    ∃ hp : LambdaNodeLocalized.lambdaEval N A p ∈ CharPReduction.integralCoeffs A,
      CharPReduction.coeffRed A red ⟨LambdaNodeLocalized.lambdaEval N A p, hp⟩
        = MvPolynomial.eval₂Hom ((algebraMap k (LaurentSeries k)).comp red) ![lambdaModC k, lambdaNModC k N] p :=
  ModularCurve.RedLambda.main A red N p

end S_ModularCurve_coeffRed_lambdaEval
end P2MW
export P2MW.S_ModularCurve_coeffRed_lambdaEval (solution)
