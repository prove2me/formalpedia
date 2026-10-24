-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.eventual_logarithmic_word_rigidity
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-24T00:13:44.627114+00:00
-- url     : https://prove2.me/submissions/6b7fe2b7-8800-4417-8af8-acba5e79c23a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_OAI_PiExponent_LogarithmicWordContact
import Definitions.Def_OAI_PiExponent_LogarithmicInterpolationNumerics
import Definitions.Def_OAI_PiExponent_LogarithmicNormalBases
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_logarithmic_word_persistent_prime
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_weighted_logarithmic_component_normal_basis_bound
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_normal_basis_separation_logarithmic_primitive
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_no_algebraic_logarithmic_primitive

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.FormalInterpolation

private theorem rigidity_prime_map_zero_iff
    {m : Nat} (P : Ideal (MvPolynomial (Fin (m + 1)) Complex)) [P.IsPrime]
    (F : MvPolynomial (Fin (m + 1)) Complex) :
    algebraMap (MvPolynomial (Fin (m + 1)) Complex)
      (logarithmicPrimeField P) F = 0 ↔ F ∈ P := by
  let R := MvPolynomial (Fin (m + 1)) Complex
  let K := logarithmicPrimeField P
  change algebraMap R K F = 0 ↔ F ∈ P
  rw [IsScalarTower.algebraMap_apply R (R ⧸ P) K F,
    Ideal.Quotient.algebraMap_eq]
  constructor
  · intro h
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    apply IsFractionRing.injective (R ⧸ P) K
    simpa only [map_zero] using h
  · intro h
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr h, map_zero]

/-
Reduction following the written persistent-component argument, with the
generic-point normal spaces encoded as finite spans of equation columns.
The last obstruction is separated into finite-column linear algebra and
a field-theoretic trace argument. All open obligations are named imports.
In fact these four children imply the stronger threshold N₀ = 0; the
finite-generation and curve hypotheses on the original E are not needed
by this reduction. Finite generation is used on the generic component's
own function field, which is a fraction field of a polynomial quotient.
-/
theorem solution
    {m : Nat} (hm : 1 ≤ m) (w v : Fin (m + 1) → Rat) (sigma : Rat)
    (hsigma : 0 < (sigma : Real))
    (hw : ∀ i, 0 < (w i : Real)) (hv : ∀ i, 0 < (v i : Real))
    (hseparated : ∀ A B : Finset (Fin (m + 1)), A.card = B.card →
      ∀ i, i ≠ 0 → i ∈ A → i ∉ B →
        (∀ j, i < j → (j ∈ A ↔ j ∈ B)) →
        interpolationSeparationConstant m sigma *
          (∏ j ∈ B, (v j : Real)) < ∏ j ∈ A, (w j : Real))
    (E : Type) [Field E] [Algebra Complex E] [Algebra.EssFiniteType Complex E]
    (htrdeg : Algebra.trdeg Complex E = 1) (x : Fin (m + 1) → E)
    (hgen : IntermediateField.adjoin Complex (Set.range x) = ⊤) :
    ∃ N₀ : Nat, ∀ N : Nat, N₀ ≤ N → 0 < N →
      ∀ F : MvPolynomial (Fin (m + 1)) Complex, F ≠ 0 →
        logarithmicDegreeBound w (N : Real) F →
        (∀ word : List (Fin (m + 1)),
          logarithmicFrameCost v word ≤ (sigma : Real) * (N : Real) →
          MvPolynomial.aeval x (logarithmicFrameWord word F) = 0) →
        ∃ a : Complex, x 0 = algebraMap Complex E a := by
  classical
  refine ⟨0, ?_⟩
  intro N _hN₀ hN F hF hdegree hwords
  by_cases hx0 : x 0 = 0
  · exact ⟨0, by simpa only [map_zero] using hx0⟩
  let R := MvPolynomial (Fin (m + 1)) Complex
  let Q : Ideal R := RingHom.ker (MvPolynomial.aeval x).toRingHom
  letI : Q.IsPrime := RingHom.ker_isPrime (MvPolynomial.aeval x).toRingHom
  have hYQ : MvPolynomial.X (0 : Fin (m + 1)) ∉ Q := by
    intro h
    have hz : MvPolynomial.aeval x (MvPolynomial.X (0 : Fin (m + 1))) = 0 :=
      RingHom.mem_ker.mp h
    exact hx0 (by simpa only [MvPolynomial.aeval_X] using hz)
  have hwordsQ : ∀ word : List (Fin (m + 1)),
      logarithmicFrameCost v word ≤ (sigma : Real) * (N : Real) →
        logarithmicFrameWord word F ∈ Q := by
    intro word hcost
    exact RingHom.mem_ker.mpr (hwords word hcost)
  obtain ⟨P, hPprime, hPne, hPQ, S, hminimal, hSdegree, hSwords⟩ :=
    logarithmic_word_persistent_prime w v sigma hsigma hw hv
      N hN F hF hdegree Q hwordsQ
  letI : P.IsPrime := hPprime
  have hYP : MvPolynomial.X (0 : Fin (m + 1)) ∉ P :=
    fun h => hYQ (hPQ h)
  have hcompare :=
    weighted_logarithmic_component_normal_basis_bound w v sigma hsigma hw hv
      N hN S P hPne hYP hminimal hSdegree hSwords
  have hexclusion :
      ∀ A B : Finset (Fin (m + 1)), A.card = B.card →
        coordinateNormalBasisAtPrime P A →
        logarithmicNormalBasisAtPrime P B →
        ∀ i, i ≠ 0 → i ∈ A → i ∉ B →
          (∀ j, i < j → (j ∈ A ↔ j ∈ B)) → False := by
    intro A B hcard hA hB i hi hiA hiB hhigher
    have hupper := hcompare A B hcard hA hB
    have hlower := hseparated A B hcard i hi hiA hiB hhigher
    exact (not_lt_of_ge hupper) hlower
  obtain ⟨z, hz⟩ :=
    normal_basis_separation_logarithmic_primitive P hPne hYP hexclusion
  let K := logarithmicPrimeField P
  obtain ⟨a, ha⟩ := no_algebraic_logarithmic_primitive K
    (algebraMap R K (MvPolynomial.X (0 : Fin (m + 1)))) z hz
  have hC : algebraMap R K (MvPolynomial.C a) = algebraMap Complex K a := by
    change algebraMap R K (algebraMap Complex R a) = algebraMap Complex K a
    exact (IsScalarTower.algebraMap_apply Complex R K a).symm
  have hzero :
      algebraMap R K
        (MvPolynomial.X (0 : Fin (m + 1)) - MvPolynomial.C a) = 0 := by
    rw [map_sub, hC]
    exact sub_eq_zero.mpr ha
  have hrelation :
      MvPolynomial.X (0 : Fin (m + 1)) - MvPolynomial.C a ∈ P :=
    (rigidity_prime_map_zero_iff P _).mp hzero
  have hxzero :
      MvPolynomial.aeval x
        (MvPolynomial.X (0 : Fin (m + 1)) - MvPolynomial.C a) = 0 :=
    RingHom.mem_ker.mp (hPQ hrelation)
  refine ⟨a, ?_⟩
  exact sub_eq_zero.mp (by
    simpa only [map_sub, MvPolynomial.aeval_X, MvPolynomial.aeval_C] using hxzero)
