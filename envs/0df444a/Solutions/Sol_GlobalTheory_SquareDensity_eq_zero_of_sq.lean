-- Prove2me | solution 1 for GlobalTheory.SquareDensity.eq_zero_of_sq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:12:17.330036+00:00
-- url     : https://prove2.me/submissions/d1586607-9b18-4393-bb3a-47af710475d7

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsSqAddSubDvd
import Theorems.Thm_GlobalTheory_SquareDensity_exists_sq_add_sub_dvd
import Theorems.Thm_GlobalTheory_SquareDensity_dvd_aeval_sub_aeval
import Theorems.Thm_GlobalTheory_SquareDensity_eval_aeval

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory
open GlobalTheory.SquareDensity
namespace GlobalTheory.SquareDensity
theorem _root_.solution {K : Type*} [Field K] [CharZero K] (Ψ : Polynomial ℤ → K) (d : ℕ)
    (hΨ : ∀ r : ℕ, ∃ Φ : MvPolynomial (Fin r) K, Φ.totalDegree ≤ d ∧
      ∀ F : Polynomial ℤ, F.natDegree < r →
        Ψ F = MvPolynomial.eval (fun i : Fin r => ((F.coeff i : ℤ) : K)) Φ)
    (hsq : ∀ G, Ψ (G ^ 2) = 0) (F : Polynomial ℤ) : Ψ F = 0 := by
  set x : Polynomial (Polynomial ℤ) :=
    Polynomial.C Polynomial.X * (F - 1).map Polynomial.C with hx
  obtain ⟨w, -, hw⟩ := exists_sq_add_sub_dvd x (d + 1)
  set y : Polynomial (Polynomial ℤ) := 1 + 2 * w with hy
  obtain ⟨Φ, hd, hΦ⟩ := hΨ (max F.natDegree (y ^ 2).natDegree + 1)
  set a : Fin (max F.natDegree (y ^ 2).natDegree + 1) → Polynomial K :=
    fun i => ((1 + 4 * x).coeff i).map (Int.castRingHom K) with ha
  set b : Fin (max F.natDegree (y ^ 2).natDegree + 1) → Polynomial K :=
    fun i => ((y ^ 2).coeff i).map (Int.castRingHom K) with hb
  have hai : ∀ i, a i = Polynomial.C (((1 : Polynomial ℤ).coeff i : ℤ) : K) +
      Polynomial.C (4 * (((F - 1).coeff i : ℤ) : K)) * Polynomial.X := by
    intro i
    have h4 : (4 : Polynomial (Polynomial ℤ)) = Polynomial.C 4 := rfl
    simp only [ha, hx, h4, Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_map,
      Polynomial.coeff_one]
    split_ifs <;> simp [Polynomial.map_mul, map_ofNat] <;> ring
  have hb0 : MvPolynomial.aeval b Φ = 0 := by
    apply Polynomial.eq_zero_of_infinite_isRoot
    refine Set.infinite_of_injective_forall_mem (f := fun k : ℤ => (k : K))
      Int.cast_injective fun k => ?_
    show (MvPolynomial.aeval b Φ).eval (k : K) = 0
    rw [eval_aeval, ← hsq (y.map (Polynomial.evalRingHom k)), ← Polynomial.map_pow, hΦ]
    · congr 2
      funext i
      simp only [hb, Polynomial.coeff_map, Polynomial.coe_evalRingHom]
      exact Polynomial.eval_intCast_map (Int.castRingHom K) _ k
    · exact lt_of_le_of_lt (Polynomial.natDegree_map_le.trans (le_max_right _ _))
        (Nat.lt_succ_self _)
  have hdvd : (Polynomial.X : Polynomial K) ^ (d + 1) ∣ MvPolynomial.aeval a Φ := by
    rw [← sub_zero (MvPolynomial.aeval a Φ), ← hb0]
    apply dvd_aeval_sub_aeval
    intro i
    have h1 : Polynomial.C ((Polynomial.X : Polynomial ℤ) ^ (d + 1)) ∣ (1 + 4 * x) - y ^ 2 := by
      have h2 : (1 + 4 * x) - y ^ 2 = (w ^ 2 + w - x) * (-4) := by rw [hy]; ring
      rw [h2, map_pow]
      exact ((pow_dvd_pow_of_dvd (dvd_mul_right _ _) _).trans hw).mul_right _
    have h3 := (Polynomial.C_dvd_iff_dvd_coeff _ _).1 h1 i
    have h4 := Polynomial.map_dvd (Int.castRingHom K) h3
    simpa only [Polynomial.map_pow, Polynomial.map_X, Polynomial.coeff_sub,
      Polynomial.map_sub] using h4
  have hdeg : (MvPolynomial.aeval a Φ).natDegree ≤ d * 1 := by
    refine MvPolynomial.aeval_natDegree_le Φ hd a fun i => ?_
    rw [hai]
    compute_degree
  have ha0 : MvPolynomial.aeval a Φ = 0 :=
    Polynomial.eq_zero_of_dvd_of_natDegree_lt hdvd (by
      rw [Polynomial.natDegree_X_pow]; omega)
  have h := eval_aeval Φ a (1 / 4)
  rw [ha0, Polynomial.eval_zero] at h
  rw [hΦ F (lt_of_le_of_lt (le_max_left _ _) (Nat.lt_succ_self _)), h]
  congr 2
  funext i
  rw [hai]
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
    Polynomial.coeff_sub, Int.cast_sub]
  ring
end GlobalTheory.SquareDensity
