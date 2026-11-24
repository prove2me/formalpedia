-- Prove2me | solution 1 for HodgeComputer.SymmetricSexticResidual.Proof.cover_E0_irreducible
-- status  : ACCEPTED   (prove)
-- author  : @benediamond
-- created : 2026-11-24T09:22:14.002812+00:00
-- url     : https://prove2.me/submissions/1500da36-4d9d-4808-8a21-2190193a0a05

import Definitions.Def_HodgeComputerSSR_CoverE0
import Theorems.Thm_HodgeComputer_SymmetricSexticResidual_Proof_cover_coprimalities_Q5
import Mathlib.FieldTheory.SplittingField.Construction
import Mathlib.RingTheory.AdjoinRoot

set_option autoImplicit false
set_option maxHeartbeats 4000000

noncomputable section
namespace SymmetricSexticResidual.CoverResidue
open SymmetricSexticResidual.K5Field SymmetricSexticResidual.CoverAlgebra QuadraticCovers CrossedRationalResidue Polynomial

private lemma isCoprime_Q5_disc_E0 : IsCoprime k5Params.Q5_z k5Params.disc_E0 :=
  HodgeComputer.SymmetricSexticResidual.Proof.cover_coprimalities_Q5.Q5_disc_E0

lemma E0_poly_irreducible : Irreducible E0_poly := by
  -- A monic degree-2 polynomial over a field is irreducible iff it has no root.
  by_contra hred
  have hdeg2 : E0_poly.natDegree = 2 := E0_poly_natDegree
  have hroot : ∃ w : RatFunc K5, E0_poly.eval w = 0 := by
    rw [irreducible_iff] at hred
    push Not at hred
    obtain ⟨p, q, hpq, hpu, hqu⟩ := hred (by
      intro hu; have := Polynomial.natDegree_eq_zero_of_isUnit hu; omega)
    have hp0 : p ≠ 0 := by intro h; rw [h, zero_mul] at hpq; exact E0_poly_monic.ne_zero hpq
    have hq0 : q ≠ 0 := by intro h; rw [h, mul_zero] at hpq; exact E0_poly_monic.ne_zero hpq
    have hsum : p.natDegree + q.natDegree = 2 := by rw [← natDegree_mul hp0 hq0, ← hpq, hdeg2]
    have hp1 : 1 ≤ p.natDegree := by
      by_contra hlt; push Not at hlt
      exact hpu (Polynomial.isUnit_iff_degree_eq_zero.mpr (by
        rw [Polynomial.degree_eq_natDegree hp0]; exact_mod_cast (by omega : p.natDegree = 0)))
    have hq1 : 1 ≤ q.natDegree := by
      by_contra hlt; push Not at hlt
      exact hqu (Polynomial.isUnit_iff_degree_eq_zero.mpr (by
        rw [Polynomial.degree_eq_natDegree hq0]; exact_mod_cast (by omega : q.natDegree = 0)))
    have hp_deg : p.natDegree = 1 := by omega
    set r0 := -p.coeff 0 / p.coeff 1
    refine ⟨r0, ?_⟩
    have hc1 : p.coeff 1 ≠ 0 := by rw [← hp_deg]; exact leadingCoeff_ne_zero.mpr hp0
    have hp_eq : p = C (p.coeff 1) * X + C (p.coeff 0) := by
      ext k
      rcases k with _ | _ | k
      · simp
      · simp
      · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega : p.natDegree < k + 2)]
        simp
    rw [hpq, eval_mul, hp_eq]
    simp only [eval_add, eval_mul, eval_C, eval_X, r0]
    rw [mul_div_cancel₀ _ hc1, neg_add_cancel, zero_mul]
  obtain ⟨w, hw⟩ := hroot
  simp only [E0_poly, eval_add, eval_mul, eval_pow, eval_C, eval_X] at hw
  have hsq : (2 * w + toRat k5Params.bW) ^ 2 = toRat k5Params.disc_E0 := by
    rw [CoverParams.disc_E0, map_sub, map_pow, map_mul, map_ofNat]
    linear_combination 4 * hw
  -- Clear denominator via coprime num/denom of `2 * w + toRat bW` in PID `K5[X]`.
  let u := 2 * w + toRat k5Params.bW
  let P := u.num; let Q := u.denom
  have hQ0 : Q ≠ 0 := u.denom_ne_zero
  have hu_eq : u = toRat P / toRat Q := u.num_div_denom.symm
  have hPQ : P ^ 2 = Q ^ 2 * k5Params.disc_E0 := by
    apply IsFractionRing.injective K5[X] (RatFunc K5)
    simp only [map_pow, map_mul]
    have hQrat : toRat Q ≠ 0 := polynomialMap_ne_zero hQ0
    have h2 : (toRat P / toRat Q) ^ 2 = toRat k5Params.disc_E0 := by rwa [← hu_eq]
    rw [div_pow, div_eq_iff (pow_ne_zero 2 hQrat)] at h2
    linear_combination h2
  have hcop : IsCoprime Q P := u.isCoprime_num_denom.symm
  have hQdvd : Q ∣ 1 := by
    have h1 : Q ∣ P ^ 2 := ⟨Q * k5Params.disc_E0, by linear_combination hPQ⟩
    exact (hcop.pow_right (n := 2)).dvd_of_dvd_mul_left (by simpa using h1)
  have hQunit : IsUnit Q := isUnit_of_dvd_one hQdvd
  obtain ⟨cQ, hcQ_u, hcQ⟩ := Polynomial.isUnit_iff.mp hQunit
  let f : K5[X] := C cQ⁻¹ * P
  have hf_sq : f ^ 2 = k5Params.disc_E0 := by
    dsimp only [f]
    rw [mul_pow, ← map_pow, hPQ, ← hcQ, ← map_pow, ← mul_assoc, ← map_mul,
      ← mul_pow, inv_mul_cancel₀ hcQ_u.ne_zero, one_pow, map_one, one_mul]
  -- Extract polynomial identity `d3 * (4 * c4^2 * d2 - d3^2) = 8 * c4^4 * d1` in `K5` and specialize via `evLoc`!
  have hdisc_deg : k5Params.disc_E0.natDegree ≤ 4 := by
    rw [CoverParams.disc_E0]
    refine (natDegree_sub_le _ _).trans (max_le ?_ ?_)
    · exact natDegree_pow_le.trans (by
        have hb : k5Params.bW.natDegree ≤ 2 := by
          rw [CoverParams.bW]; exact (natDegree_C_mul_le _ _).trans (by
            rw [CoverParams.Bv, CoverParams.quadU]
            refine (natDegree_add_le _ _).trans (max_le ((natDegree_add_le _ _).trans (max_le (by simp) ?_)) ?_)
            · exact (natDegree_C_mul_le _ _).trans (by simp)
            · exact (natDegree_C_mul_le _ _).trans (by simp))
        omega)
    · refine (natDegree_mul_le).trans ?_
      have hc : k5Params.cW.natDegree ≤ 2 := by
        rw [CoverParams.cW]; exact (natDegree_C_mul_le _ _).trans (by simp)
      simp only [natDegree_ofNat, zero_add]; omega
  have hdisc_c4_loc : evLoc (locParams.disc_E0.coeff 4) = 309 := by
    rw [← Polynomial.coeff_map, CoverParams.map_disc_E0, locParams_map_evLoc,
      ← Poly1009.toPoly_c_disc_E0, Poly1009.toPoly_coeff_getD]
    decide
  have hdisc_map : locParams.disc_E0.map LocK5.subtype = k5Params.disc_E0 :=
    CoverParams.map_disc_E0 locParams LocK5.subtype
  have hdisc_coeff (k : ℕ) : (locParams.disc_E0.coeff k : K5) = k5Params.disc_E0.coeff k := by
    rw [← hdisc_map, Polynomial.coeff_map]; rfl
  have hdisc_c4_ne : k5Params.disc_E0.coeff 4 ≠ 0 := by
    rw [← hdisc_coeff 4]
    exact LocK5.ne_zero_of_evLoc (by rw [hdisc_c4_loc]; decide)
  have hf_ne : f ≠ 0 := by
    intro h0; rw [h0, zero_pow (by omega)] at hf_sq
    exact hdisc_c4_ne (by rw [← hf_sq, Polynomial.coeff_zero])
  have hf_deg : f.natDegree = 2 := by
    have h4 : k5Params.disc_E0.natDegree = 4 :=
      le_antisymm hdisc_deg (Polynomial.le_natDegree_of_ne_zero hdisc_c4_ne)
    have h2 : 2 * f.natDegree = 4 := by
      rw [← h4, ← hf_sq, Polynomial.natDegree_pow]
    omega
  have hf_form : f = C (f.coeff 0) + C (f.coeff 1) * X + C (f.coeff 2) * X ^ 2 := by
    ext k
    rcases k with _ | _ | _ | k
    · simp
    · simp
    · simp
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega : f.natDegree < k + 3)]
      simp
  set f0 := f.coeff 0; set f1 := f.coeff 1; set f2 := f.coeff 2
  have hexp : f ^ 2 = C (f0 ^ 2) + C (2 * f0 * f1) * X + C (2 * f0 * f2 + f1 ^ 2) * X ^ 2 +
      C (2 * f1 * f2) * X ^ 3 + C (f2 ^ 2) * X ^ 4 := by
    rw [hf_form]
    simp only [map_add, map_mul, map_pow, map_ofNat]
    ring
  have hf_sq_exp : C (f0 ^ 2) + C (2 * f0 * f1) * X + C (2 * f0 * f2 + f1 ^ 2) * X ^ 2 +
      C (2 * f1 * f2) * X ^ 3 + C (f2 ^ 2) * X ^ 4 = k5Params.disc_E0 :=
    hexp.symm.trans hf_sq
  have hf2_sq : f2 ^ 2 = k5Params.disc_E0.coeff 4 := by
    have h := congrArg (fun p : K5[X] => p.coeff 4) hf_sq_exp
    simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_C,
      Polynomial.coeff_X, Polynomial.coeff_X_pow] at h
    simpa using h
  have hd3 : 2 * f1 * f2 = k5Params.disc_E0.coeff 3 := by
    have h := congrArg (fun p : K5[X] => p.coeff 3) hf_sq_exp
    simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_C,
      Polynomial.coeff_X, Polynomial.coeff_X_pow] at h
    simpa using h
  have hd2 : 2 * f0 * f2 + f1 ^ 2 = k5Params.disc_E0.coeff 2 := by
    have h := congrArg (fun p : K5[X] => p.coeff 2) hf_sq_exp
    simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_C,
      Polynomial.coeff_X, Polynomial.coeff_X_pow] at h
    simpa using h
  have hd1 : 2 * f0 * f1 = k5Params.disc_E0.coeff 1 := by
    have h := congrArg (fun p : K5[X] => p.coeff 1) hf_sq_exp
    simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_C,
      Polynomial.coeff_X, Polynomial.coeff_X_pow] at h
    simpa using h
  have hrel : k5Params.disc_E0.coeff 3 * (4 * k5Params.disc_E0.coeff 4 * k5Params.disc_E0.coeff 2 -
      k5Params.disc_E0.coeff 3 ^ 2) = 8 * k5Params.disc_E0.coeff 4 ^ 2 * k5Params.disc_E0.coeff 1 := by
    rw [← hf2_sq, ← hd3, ← hd2, ← hd1]; ring
  have hrel_loc : locParams.disc_E0.coeff 3 * (4 * locParams.disc_E0.coeff 4 * locParams.disc_E0.coeff 2 -
      locParams.disc_E0.coeff 3 ^ 2) = 8 * locParams.disc_E0.coeff 4 ^ 2 * locParams.disc_E0.coeff 1 := by
    apply Subtype.ext
    push_cast [hdisc_coeff]
    exact hrel
  have hev := congrArg evLoc hrel_loc
  simp only [map_mul, map_sub, map_pow, map_ofNat] at hev
  have hevk (k : ℕ) : evLoc (locParams.disc_E0.coeff k) = Poly1009.c_disc_E0.getD k 0 := by
    rw [← Polynomial.coeff_map, CoverParams.map_disc_E0, locParams_map_evLoc,
      ← Poly1009.toPoly_c_disc_E0, Poly1009.toPoly_coeff_getD]
  rw [hevk 1, hevk 2, hevk 3, hevk 4] at hev
  exact (by decide : Poly1009.c_disc_E0.getD 3 0 * (4 * Poly1009.c_disc_E0.getD 4 0 *
    Poly1009.c_disc_E0.getD 2 0 - Poly1009.c_disc_E0.getD 3 0 ^ 2) ≠
    8 * Poly1009.c_disc_E0.getD 4 0 ^ 2 * Poly1009.c_disc_E0.getD 1 0) hev


end SymmetricSexticResidual.CoverResidue

theorem solution : Irreducible SymmetricSexticResidual.CoverResidue.E0_poly :=
  SymmetricSexticResidual.CoverResidue.E0_poly_irreducible
