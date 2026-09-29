-- Prove2me | solution 1 for ModularCurve.ModularPolynomialData.map_map_intCast_eq_of_charP
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/19329418-c1dc-536c-946c-591a85c57160

import Mathlib
import Definitions.Def_ModularCurve_X0
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_PhiGen
import Theorems.Thm_ModularCurve_qExpand_jqModC_eq_pow_unconditional
import Theorems.Thm_ModularCurve_transcendental_jqModC
import Theorems.Thm_ModularCurve_ModularPolynomialData_evalSymm_of_prime
import Theorems.Thm_ModularCurve_ModularPolynomialData_eval_jqNModC_mul_eq_zero
import Theorems.Thm_ModularCurve_ModularPolynomialData_eval_jqNModC_of_mul_eq_zero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_ModularPolynomialData_map_map_intCast_eq_of_charP
p2m_attr_erase "simp" "ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL"

set_option autoImplicit false

p2m_open "Polynomial ModularCurve~dedekindPsi_prime"
open scoped Polynomial.Bivariate

namespace KroneckerAsm

theorem dedekindPsi_prime (p : ℕ) [hp : Fact p.Prime] : dedekindPsi p = p + 1 := by
  unfold dedekindPsi
  rw [Nat.Prime.divisors hp.out, Finset.filter_true_of_mem, Finset.sum_pair hp.out.one_lt.ne, Nat.div_one,
    Nat.div_self hp.out.pos, add_comm]
  intro d hd
  simp only [Finset.mem_insert, Finset.mem_singleton] at hd
  rcases hd with rfl | rfl
  · exact squarefree_one
  · exact hp.out.squarefree

theorem aevalAeval_eq_eval₂ {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] (x y : A) (P : R[X][Y]) :
    aevalAeval x y P = P.eval₂ (aeval (R := R) x).toRingHom y := by
  induction P using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add, hp, hq, eval₂_add]
  | monomial n a =>
    rw [← C_mul_X_pow_eq_monomial, map_mul, map_pow, aevalAeval_C, aevalAeval_Y, eval₂_mul, eval₂_C, eval₂_pow,
      eval₂_X]
    rfl

end KroneckerAsm

open KroneckerAsm in
theorem solution
    (p : ℕ) [Fact p.Prime] (data : ModularCurve.ModularPolynomialData p)
    (R : Type) [CommRing R] [CharP R p] :
    data.Φ.map (Polynomial.mapRingHom (Int.castRingHom R)) =
      (Polynomial.X - Polynomial.C (Polynomial.X ^ p)) * (Polynomial.X ^ p - Polynomial.C Polynomial.X) := by
  classical
  have hp := (Fact.out : p.Prime)

  suffices hK : data.Φ.map (Polynomial.mapRingHom (Int.castRingHom (ZMod p))) =
      (Polynomial.X - Polynomial.C (Polynomial.X ^ p)) * (Polynomial.X ^ p - Polynomial.C Polynomial.X) by
    have hc : Int.castRingHom R = (ZMod.castHom (dvd_refl p) R).comp (Int.castRingHom (ZMod p)) :=
      RingHom.ext_int _ _
    rw [hc, ← Polynomial.mapRingHom_comp, ← Polynomial.map_map, hK]
    simp [Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_pow]
  set K := ZMod p with hKdef
  set ι : ℤ →+* K := Int.castRingHom K with hι
  set Φb : K[X][Y] := data.Φ.map (mapRingHom ι) with hΦb
  have hmon : Φb.Monic := data.monic.map _
  have hdeg : Φb.natDegree = p + 1 := by
    rw [hΦb, data.monic.natDegree_map, data.natDegree_eq, dedekindPsi_prime]
  set j : LaurentSeries K := jqModC K with hj
  have hjt : Transcendental K j := transcendental_jqModC K
  have hjinj : Function.Injective (aeval (R := K) j) := transcendental_iff_injective.mp hjt
  have hjp : jqNModC K p = j ^ p := qExpand_jqModC_eq_pow_unconditional K
  have hcomp : ∀ y : LaurentSeries K,
      ((aeval (R := K) y).toRingHom).comp (mapRingHom ι) = (aeval (R := ℤ) y).toRingHom := by
    intro y
    refine Polynomial.ringHom_ext (fun z => ?_) ?_
    · simp [hι]
    · simp
  have heval : ∀ x y : LaurentSeries K, Φb.eval₂ (aeval (R := K) x).toRingHom y =
      data.Φ.eval₂ (aeval (R := ℤ) x).toRingHom y := by
    intro x y
    rw [hΦb, Polynomial.eval₂_map, hcomp]

  have E1 : Φb.eval₂ (aeval (R := K) j).toRingHom (j ^ p) = 0 := by
    have h := data.eval_jqNModC_mul_eq_zero K 1
    simp only [one_mul, jqNModC_one] at h
    rw [heval, ← hjp]
    exact h
  have E2 : Φb.eval₂ (aeval (R := K) (j ^ p)).toRingHom j = 0 := by
    have h := data.eval_jqNModC_of_mul_eq_zero (ModularPolynomialData.evalSymm_of_prime p data) K 1
    simp only [one_mul, jqNModC_one] at h
    rw [heval, ← hjp]
    exact h

  have hroot1 : Φb.IsRoot ((Polynomial.X : K[X]) ^ p) := by
    show Φb.eval (Polynomial.X ^ p) = 0
    apply hjinj
    have hjX : (aeval (R := K) j).toRingHom (Polynomial.X ^ p) = j ^ p := by simp [map_pow, aeval_X]
    rw [map_zero, ← eval₂_id]
    change (aeval (R := K) j).toRingHom (Φb.eval₂ (RingHom.id _) (Polynomial.X ^ p)) = 0
    rw [hom_eval₂, RingHom.comp_id, hjX]
    exact E1
  have hdvd1 : (Polynomial.X - Polynomial.C ((Polynomial.X : K[X]) ^ p)) ∣ Φb := dvd_iff_isRoot.mpr hroot1

  have hroot2 : (Bivariate.swap Φb).IsRoot ((Polynomial.X : K[X]) ^ p) := by
    show (Bivariate.swap Φb).eval (Polynomial.X ^ p) = 0
    apply hjinj
    have hjX : (aeval (R := K) j).toRingHom (Polynomial.X ^ p) = j ^ p := by simp [map_pow, aeval_X]
    rw [map_zero, ← eval₂_id]
    change (aeval (R := K) j).toRingHom ((Bivariate.swap Φb).eval₂ (RingHom.id _) (Polynomial.X ^ p)) = 0
    rw [hom_eval₂, RingHom.comp_id, hjX, ← aevalAeval_eq_eval₂, Bivariate.aevalAeval_swap, aevalAeval_eq_eval₂]
    exact E2
  have hdvd2 : ((Polynomial.X : K[X][Y]) ^ p - Polynomial.C Polynomial.X) ∣ Φb := by
    have h := map_dvd (Bivariate.swap (R := K)) (dvd_iff_isRoot.mpr hroot2)
    rw [Bivariate.swap_swap_apply, map_sub, Bivariate.swap_Y, C_pow, map_pow, Bivariate.swap_X] at h
    rw [← neg_sub] at h
    exact dvd_trans ⟨-1, by ring⟩ h

  obtain ⟨G, hG⟩ := hdvd1
  obtain ⟨H, hH⟩ := hdvd2
  have hlin_ne : (Polynomial.X - Polynomial.C ((Polynomial.X : K[X]) ^ p)) ≠ 0 := X_sub_C_ne_zero _
  have hprime : Prime (Polynomial.X - Polynomial.C ((Polynomial.X : K[X]) ^ p)) := prime_X_sub_C _
  have hndvd : ¬ (Polynomial.X - Polynomial.C ((Polynomial.X : K[X]) ^ p)) ∣
      ((Polynomial.X : K[X][Y]) ^ p - Polynomial.C Polynomial.X) := by
    intro h
    have hr := dvd_iff_isRoot.mp h
    have hr' : ((Polynomial.X : K[X]) ^ p) ^ p - Polynomial.X = 0 := by
      simpa [IsRoot, eval_sub, eval_pow, eval_X, eval_C] using hr
    have hdeg' := congrArg Polynomial.natDegree (sub_eq_zero.mp hr')
    rw [← pow_mul, natDegree_X_pow, natDegree_X] at hdeg'
    have : 2 * 2 ≤ p * p := Nat.mul_le_mul hp.two_le hp.two_le
    omega
  have hH' : (Polynomial.X - Polynomial.C ((Polynomial.X : K[X]) ^ p)) ∣ H := by
    have : (Polynomial.X - Polynomial.C ((Polynomial.X : K[X]) ^ p)) ∣
        ((Polynomial.X : K[X][Y]) ^ p - Polynomial.C Polynomial.X) * H := by rw [← hH]; exact ⟨G, hG⟩
    exact (hprime.dvd_or_dvd this).resolve_left hndvd
  obtain ⟨H', hH''⟩ := hH'
  have hGeq : G = ((Polynomial.X : K[X][Y]) ^ p - Polynomial.C Polynomial.X) * H' := by
    apply mul_left_cancel₀ hlin_ne
    rw [← hG, hH, hH'']
    ring

  have hGmon : G.Monic := Monic.of_mul_monic_left (monic_X_sub_C _) (hG ▸ hmon)
  have hQmon : (((Polynomial.X : K[X][Y]) ^ p - Polynomial.C Polynomial.X)).Monic :=
    monic_X_pow_sub_C _ hp.ne_zero
  have hH'mon : H'.Monic := Monic.of_mul_monic_left hQmon (hGeq ▸ hGmon)
  have hGdeg : G.natDegree = p := by
    have h := congrArg Polynomial.natDegree hG
    rw [hdeg, (monic_X_sub_C _).natDegree_mul hGmon, natDegree_X_sub_C] at h
    omega
  have hH'deg : H'.natDegree = 0 := by
    have h := congrArg Polynomial.natDegree hGeq
    rw [hGdeg, hQmon.natDegree_mul hH'mon, natDegree_X_pow_sub_C] at h
    omega
  have hH'1 : H' = 1 := Polynomial.eq_one_of_monic_natDegree_zero hH'mon hH'deg
  rw [hG, hGeq, hH'1, mul_one]

end S_ModularCurve_ModularPolynomialData_map_map_intCast_eq_of_charP
end P2MW
export P2MW.S_ModularCurve_ModularPolynomialData_map_map_intCast_eq_of_charP (solution)
