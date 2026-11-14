-- Prove2me | solution 1 for HararySachs.Hyper.phiPoly_vTensor_eval
-- status  : ACCEPTED   (prove)
-- author  : @milia
-- created : 2026-11-13T22:18:32.087872+00:00
-- url     : https://prove2.me/submissions/8fd356cf-4c45-43d5-b48e-0037e6397699

import Mathlib
import Definitions.Def_HararySachs_Hyper_CharPoly
import Definitions.Def_HararySachs_Hyper_Operators
import Definitions.Def_HararySachs_Hyper_TensorPhi

open HararySachs.Hyper Finset

namespace PhiEvalAux

/-- multinomial expansion of a power of a linear form, over words -/
lemma pow_expand {n : ℕ} (a : Fin n → ℂ) (r : ℕ) :
    (∑ l, MvPolynomial.C (a l) * MvPolynomial.X l : MvPolynomial (Fin n) ℂ) ^ r =
      ∑ t : Fin r → Fin n, MvPolynomial.monomial (∑ s, Finsupp.single (t s) 1) (∏ s, a (t s)) := by
  rw [← Fin.prod_const, Fintype.prod_sum]
  refine sum_congr rfl fun t _ => ?_
  rw [prod_mul_distrib, ← map_prod]
  have hX : ∏ s, (MvPolynomial.X (t s) : MvPolynomial (Fin n) ℂ) =
      MvPolynomial.monomial (∑ s, Finsupp.single (t s) 1) 1 := by
    rw [MvPolynomial.monomial_sum_one]; rfl
  rw [hX, MvPolynomial.C_mul_monomial, mul_one]

end PhiEvalAux

open PhiEvalAux in
theorem solution (n k : ℕ) (res : MvPolynomial (ResVar n (fun _ => k - 1)) ℤ)
    (x : Fin n × Fin n → ℂ) :
    MvPolynomial.eval x
        (((phiPoly (k := k) (vTensor n k) res).map
          (MvPolynomial.map (algebraMap ℚ ℂ))).eval 1) =
      MvPolynomial.aeval (fun v : ResVar n (fun _ => k - 1) =>
          MvPolynomial.coeff v.2.1
            ((MvPolynomial.X v.1 ^ (k - 1) -
              (∑ j, MvPolynomial.C (x (v.1, j)) * MvPolynomial.X j) ^ (k - 1) :
                MvPolynomial (Fin n) ℂ)))
        (MvPolynomial.map (Int.castRingHom ℂ) res) := by
  classical
  set ψ : Polynomial (AuxPoly n) →+* ℂ := (MvPolynomial.eval x).comp
    ((Polynomial.evalRingHom 1).comp
      (Polynomial.mapRingHom (MvPolynomial.map (algebraMap ℚ ℂ)))) with hψ
  have hL : MvPolynomial.eval x
      (((phiPoly (k := k) (vTensor n k) res).map
        (MvPolynomial.map (algebraMap ℚ ℂ))).eval 1) = ψ (phiPoly (k := k) (vTensor n k) res) :=
    rfl
  rw [hL]
  unfold phiPoly
  rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_map, MvPolynomial.eval₂_comp_left,
    MvPolynomial.aeval_def, MvPolynomial.eval₂_map]
  congr 1
  · exact RingHom.ext_int _ _
  · funext v
    obtain ⟨j, α⟩ := v
    simp only [Function.comp_apply]
    unfold zcoord
    rw [MvPolynomial.coeff_sub, MvPolynomial.coeff_monomial, MvPolynomial.coeff_sum,
      MvPolynomial.coeff_sub, MvPolynomial.coeff_X_pow, pow_expand, MvPolynomial.coeff_sum,
      map_sub, map_sum]
    congr 1
    · split_ifs <;> simp [hψ]
    · refine sum_congr rfl fun t _ => ?_
      rw [MvPolynomial.coeff_monomial, MvPolynomial.coeff_monomial]
      split_ifs
      · simp [hψ, vTensor, Polynomial.eval_prod]
      · simp
