-- Prove2me | solution 1 for MazurTransfer.genusFF_zero_of_principal_difference_of_distinct_places
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-09T21:22:37.045997+00:00
-- url     : https://prove2.me/submissions/e7cb62db-d3f3-4c82-a5ab-86dd76c19ef4

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
The pole and independent-power argument reuses official Anthropic FLT at
6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0. The original canonical-
differential genus theorem is unchanged; this separate perfect-field bridge
uses the checked Weil-canonical Riemann–Roch formula for genusFF instead.
Design boundary: distinct rational places have distinct Abel–Jacobi divisor
classes on a positive-genus function field. Named downstream consumer: the
literal order-13 rational-point injection into its actual arithmetic Pic0.
-/
import Theorems.Thm_AlgebraicCurve_exists_weilCanonical_riemannRoch
import Theorems.Thm_AlgebraicCurve_stichtenothGenusExists_of_isCurveOver
import Theorems.Thm_AlgebraicCurve_finiteDimensional_lSpace
import Theorems.Thm_AlgebraicCurve_ell_eq_zero_of_degree_neg

universe u v
open AlgebraicCurve Polynomial
namespace MazurTransfer.PublicRationalPlaceInjectionProof

private theorem independent_powers {K A : Type*} [CommRing K] [CommRing A] [Algebra K A]
    {x : A} (hx : Transcendental K x) : LinearIndependent K (fun j : ℕ => x ^ j) := by
  have hinj : Function.Injective (Polynomial.aeval x : K[X] →ₐ[K] A) :=
    transcendental_iff_injective.mp hx
  have hXj : LinearIndependent K (fun j : ℕ => (X : K[X]) ^ j) := by
    have hb := (Polynomial.basisMonomials K).linearIndependent
    simp only [Polynomial.coe_basisMonomials] at hb
    convert hb using 2 with j
    exact (Polynomial.monomial_one_right_eq_X_pow j).symm
  have heq : (fun j : ℕ => x ^ j) =
      (fun j : ℕ => (Polynomial.aeval x : K[X] →ₐ[K] A) (X ^ j)) := by
    funext j; simp
  rw [heq]
  exact hXj.map' (Polynomial.aeval x).toLinearMap (LinearMap.ker_eq_bot_of_injective hinj)

namespace Place
variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : AlgebraicCurve.Place K F)
private theorem ord_nonneg_of_mem {f : F} (hf : f ∈ v.toValuationSubring) : 0 ≤ v.ord f := by
  rcases eq_or_ne f 0 with rfl | hf0
  · simp
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
    (x := (⟨f, hf⟩ : v.toValuationSubring)) (by simpa [Subtype.ext_iff] using hf0) hπ
  have hcoe : f = ((u : v.toValuationSubring) : F) * ((π : F) ^ (n : ℤ)) := by
    have h := congrArg Subtype.val hu
    push_cast at h
    rw [zpow_natCast]
    exact h
  rw [hcoe, v.ord_unit_smul_zpow u hπ (n : ℤ)]
  exact Int.natCast_nonneg n
end Place

variable {K : Type u} {F : Type v} [Field K] [PerfectField K] [Field F] [Algebra K F]
variable [IsCurveOver K F] [Algebra.EssFiniteType K F]

theorem genusFF_eq_zero_of_principal_single_sub_single (hC : ConstantsAreBase K F)
    {P Q : AlgebraicCurve.Place K F} (hPQ : P ≠ Q) (hQ : Q.deg = 1)
    (h : Divisor.IsPrincipal (Finsupp.single P 1 - Finsupp.single Q 1)) :
    genusFF K F = 0 := by
  classical
  obtain ⟨f, hf0, hdiv⟩ := h
  have hordQ : Q.ord f = -1 := by
    have he := hdiv Q
    rw [Finsupp.sub_apply, Finsupp.single_apply, if_neg hPQ, Finsupp.single_eq_same] at he
    linarith [he]
  have hordv : ∀ w : AlgebraicCurve.Place K F, w ≠ Q → 0 ≤ w.ord f := by
    intro w hw
    have he := hdiv w
    rw [← he, Finsupp.sub_apply, Finsupp.single_apply, Finsupp.single_apply,
      if_neg (Ne.symm hw)]
    by_cases hwP : P = w
    · rw [if_pos hwP]; norm_num
    · rw [if_neg hwP]; norm_num
  letI : Nonempty (AlgebraicCurve.Place K F) := ⟨Q⟩
  obtain ⟨_, hfinite, _, _, _⟩ := stichtenothGenusExists_of_isCurveOver hC
  letI := hfinite
  have hftr : Transcendental K f := by
    intro halg
    have hint : IsIntegral K f := halg.isIntegral
    have hmem : f ∈ Q.toValuationSubring := by
      have hint' : IsIntegral Q.toValuationSubring f := hint.tower_top
      obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (R := Q.toValuationSubring) (K := F)).mp hint'
      rw [← hy]; exact y.2
    have hn := Place.ord_nonneg_of_mem Q hmem
    linarith
  have hpow : ∀ n k : ℕ, k ≤ n → f ^ k ∈ LSpace ((n : ℤ) • Finsupp.single Q (1 : ℤ)) := by
    intro n k hk
    rw [mem_lSpace_iff_ord]
    refine Or.inr fun w => ?_
    rw [← zpow_natCast, AlgebraicCurve.Place.ord_zpow]
    by_cases hw : w = Q
    · subst hw
      simp only [Finsupp.smul_apply, Finsupp.single_eq_same, smul_eq_mul, mul_one, hordQ]
      push_cast; omega
    · have h0 : ((n : ℤ) • Finsupp.single Q (1 : ℤ)) w = 0 := by
        rw [Finsupp.smul_apply, Finsupp.single_apply, if_neg (Ne.symm hw), smul_zero]
      rw [h0, neg_zero]
      exact mul_nonneg (by positivity) (hordv w hw)
  have hell : ∀ n : ℕ, (n : ℤ) + 1 ≤ (ell ((n : ℤ) • Finsupp.single Q (1 : ℤ)) : ℤ) := by
    intro n
    let E : Divisor K F := (n : ℤ) • Finsupp.single Q (1 : ℤ)
    letI : FiniteDimensional K (LSpace E) := finiteDimensional_lSpace E
    let g : Fin (n + 1) → LSpace E := fun k => ⟨f ^ (k : ℕ), hpow n k (Nat.lt_succ_iff.mp k.2)⟩
    have hli : LinearIndependent K g := by
      have hi : LinearIndependent K (fun k : Fin (n + 1) => f ^ (k : ℕ)) :=
        (independent_powers hftr).comp (fun k : Fin (n+1) => (k : ℕ))
          (fun a b hab => Fin.ext hab)
      exact LinearIndependent.of_comp (LSpace E).subtype hi
    have hi := hli.fintype_card_le_finrank
    simp only [Fintype.card_fin] at hi
    exact_mod_cast hi
  obtain ⟨W, hRR⟩ := exists_weilCanonical_riemannRoch K F hC
  have h0 := hRR 0
  have hW := hRR W
  rw [ell_zero_eq_one_of_constantsAreBase hC, sub_zero, map_zero] at h0
  rw [sub_self, ell_zero_eq_one_of_constantsAreBase hC] at hW
  have hdegW : Divisor.degree W = 2 * (genusFF K F : ℤ) - 2 := by omega
  let n := 2 * genusFF K F
  have hdegD : Divisor.degree ((n : ℤ) • Finsupp.single Q (1 : ℤ)) = (n : ℤ) := by
    rw [map_zsmul, Divisor.degree_single, hQ]; simp
  have hzero : ell (W - (n : ℤ) • Finsupp.single Q (1 : ℤ)) = 0 := by
    apply ell_eq_zero_of_degree_neg
    rw [map_sub, hdegW, hdegD]
    dsimp [n]
    push_cast
    omega
  have hRRD := hRR ((n : ℤ) • Finsupp.single Q (1 : ℤ))
  rw [hzero, hdegD] at hRRD
  have hlow := hell n
  omega

end MazurTransfer.PublicRationalPlaceInjectionProof

theorem solution {K : Type u} {F : Type v}
    [Field K] [PerfectField K] [Field F] [Algebra K F]
    [IsCurveOver K F] [Algebra.EssFiniteType K F]
    (hC : ConstantsAreBase K F) {P Q : AlgebraicCurve.Place K F}
    (hPQ : P ≠ Q) (hQ : Q.deg = 1)
    (h : Divisor.IsPrincipal (Finsupp.single P 1 - Finsupp.single Q 1)) :
    genusFF K F = 0 := by
  exact MazurTransfer.PublicRationalPlaceInjectionProof.genusFF_eq_zero_of_principal_single_sub_single
    hC hPQ hQ h
#print axioms solution
