-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.finiteDimensional_of_pairwiseComaximalProduct
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T16:05:23.141735+00:00
-- url     : https://prove2.me/submissions/5783cee9-0a79-47fc-9dd6-3a3b36577600

import Mathlib
import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.RingTheory.Ideal.Quotient.Operations

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation
theorem solution
    {m K : Nat}
    (I : Fin K → Ideal (MvPolynomial (Fin (m + 1)) Complex))
    (hfd : ∀ j, FiniteDimensional Complex
      (MvPolynomial (Fin (m + 1)) Complex ⧸ I j))
    (hcomax : ∀ j₁ j₂ : Fin K, j₁ ≠ j₂ →
      IsCoprime (I j₁) (I j₂)) :
    FiniteDimensional Complex
      (MvPolynomial (Fin (m + 1)) Complex ⧸ ∏ j, I j) := by
  classical
  have hprod : ∏ j, I j = ⨅ j, I j := by
    rw [Ideal.prod_eq_iInf_of_pairwise_isCoprime (s := Finset.univ)
      (fun a _ b _ hab => hcomax a b hab)]
    simp
  rw [hprod]
  haveI : ∀ j, FiniteDimensional Complex (MvPolynomial (Fin (m + 1)) Complex ⧸ I j) := hfd
  let φ := Ideal.quotientInfToPiQuotient I
  let L : (MvPolynomial (Fin (m + 1)) Complex ⧸ ⨅ j, I j) →ₗ[Complex]
      (∀ j, MvPolynomial (Fin (m + 1)) Complex ⧸ I j) :=
    { toFun := φ
      map_add' := φ.map_add
      map_smul' := by
        intro c x
        obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
        rw [← Ideal.Quotient.mkₐ_eq_mk Complex, ← map_smul, Ideal.Quotient.mkₐ_eq_mk]
        simp only [RingHom.id_apply]
        rw [Ideal.quotientInfToPiQuotient_mk, Ideal.quotientInfToPiQuotient_mk]
        funext i
        simp only [Pi.smul_apply]
        rw [← Ideal.Quotient.mkₐ_eq_mk Complex, map_smul] }
  exact Module.Finite.of_injective L (Ideal.quotientInfToPiQuotient_inj I)
