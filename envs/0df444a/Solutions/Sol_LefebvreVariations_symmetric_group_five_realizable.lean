-- Prove2me | solution 1 for LefebvreVariations.symmetric_group_five_realizable
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-24T22:17:12.912382+00:00
-- url     : https://prove2.me/submissions/d5e5b4d0-00bb-40a3-bcb1-14a0cb6e503f

import Definitions.Def_InverseGalois_realizability

set_option autoImplicit false

open Polynomial Polynomial.Gal

attribute [local instance] splits_ℚ_ℂ

/-- The quintic `X⁵ - 4X + 2` over a commutative ring. -/
private noncomputable def Φ (R : Type*) [CommRing R] : R[X] :=
  X ^ 5 - C (4 : R) * X + C (2 : R)

private lemma map_Phi {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) :
    (Φ R).map f = Φ S := by
  simp [Φ, map_ofNat]

private lemma degree_Phi {R : Type*} [CommRing R] [Nontrivial R] :
    (Φ R).degree = ((5 : ℕ) : WithBot ℕ) := by
  unfold Φ; compute_degree!

private lemma natDegree_Phi {R : Type*} [CommRing R] [Nontrivial R] : (Φ R).natDegree = 5 :=
  natDegree_eq_of_degree_eq_some degree_Phi

private lemma monic_Phi {R : Type*} [CommRing R] [Nontrivial R] : (Φ R).Monic := by
  unfold Φ; monicity!

private lemma irreducible_Phi : Irreducible (Φ ℚ) := by
  rw [← map_Phi (Int.castRingHom ℚ), ← IsPrimitive.Int.irreducible_iff_irreducible_map_cast]
  on_goal 1 =>
    apply irreducible_of_eisenstein_criterion (P := Ideal.span {(2 : ℤ)})
    · rw [Ideal.span_singleton_prime (by norm_num), Int.prime_iff_natAbs_prime]
      norm_num
    · rw [monic_Phi.leadingCoeff, Ideal.mem_span_singleton]
      decide
    · intro n hn
      rw [Ideal.mem_span_singleton]
      rw [degree_Phi] at hn; norm_cast at hn
      interval_cases n <;> simp [Φ, coeff_X_pow, coeff_X]
    · rw [degree_Phi]; decide
    · rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton]
      simp [Φ, coeff_X_pow]
  all_goals exact Monic.isPrimitive monic_Phi

attribute [local simp] map_ofNat in
private lemma real_roots_Phi_le : Fintype.card ((Φ ℚ).rootSet ℝ) ≤ 3 := by
  rw [Φ, ← one_mul (X ^ 5), ← C_1]
  apply (card_rootSet_le_derivative _).trans
    (Nat.succ_le_succ ((card_rootSet_le_derivative _).trans (Nat.succ_le_succ _)))
  suffices (Polynomial.rootSet (C (20 : ℚ) * X ^ 3) ℝ).Subsingleton by
    norm_num [Fintype.card_le_one_iff_subsingleton, ← mul_assoc] at *
    exact this
  rw [rootSet_C_mul_X_pow] <;>
  norm_num

private lemma real_roots_Phi_ge : 2 ≤ Fintype.card ((Φ ℚ).rootSet ℝ) := by
  have q_ne_zero : Φ ℚ ≠ 0 := monic_Phi.ne_zero
  have hf : ∀ x : ℝ, aeval x (Φ ℚ) = x ^ 5 - 4 * x + 2 := fun x => by simp [Φ]
  have hc : ∀ s : Set ℝ, ContinuousOn (fun x : ℝ => aeval x (Φ ℚ)) s :=
    fun s => (Φ ℚ).continuousOn_aeval
  obtain ⟨x, ⟨-, hx1⟩, hx2⟩ := intermediate_value_Ico' (zero_le_one' ℝ) (hc _)
    (show (0 : ℝ) ∈ Set.Ioc (aeval (1 : ℝ) (Φ ℚ)) (aeval (0 : ℝ) (Φ ℚ)) by
      rw [hf, hf]; norm_num)
  obtain ⟨y, ⟨hy1, -⟩, hy2⟩ := intermediate_value_Ioc (show (1 : ℝ) ≤ 2 by norm_num) (hc _)
    (show (0 : ℝ) ∈ Set.Ioc (aeval (1 : ℝ) (Φ ℚ)) (aeval (2 : ℝ) (Φ ℚ)) by
      rw [hf, hf]; norm_num)
  simp only at hx2 hy2
  have hxy : x ≠ y := (hx1.trans hy1).ne
  have key : ↑({x, y} : Finset ℝ) ⊆ (Φ ℚ).rootSet ℝ := by
    simp [Set.insert_subset, mem_rootSet_of_ne q_ne_zero, hx2, hy2]
  convert! Fintype.card_le_of_embedding (Set.embeddingOfSubset _ _ key)
  simp only [Finset.coe_sort_coe, Fintype.card_coe, Finset.card_singleton,
    Finset.card_insert_of_notMem (mt Finset.mem_singleton.mp hxy)]

private lemma complex_roots_Phi : Fintype.card ((Φ ℚ).rootSet ℂ) = 5 :=
  (card_rootSet_eq_natDegree irreducible_Phi.separable (IsAlgClosed.splits _)).trans natDegree_Phi

private lemma gal_Phi : Function.Bijective (galActionHom (Φ ℚ) ℂ) := by
  apply galActionHom_bijective_of_prime_degree' irreducible_Phi
  · simp only [natDegree_Phi]; decide
  · rw [complex_roots_Phi, Nat.succ_le_succ_iff]
    exact real_roots_Phi_le.trans (Nat.le_succ 3)
  · simp_rw [complex_roots_Phi, Nat.succ_le_succ_iff]
    exact real_roots_Phi_ge

private lemma isGalois_Phi : IsGalois ℚ (Φ ℚ).SplittingField :=
  -- `inferInstance` gives `Algebra ℚ` through `DivisionRing.toRatAlgebra`, for which the
  -- splitting-field instance is not found by search; it is supplied by hand (defeq).
  @IsGalois.of_separable_splitting_field _ _ _ _ _ _ (IsSplittingField.splittingField _)
    irreducible_Phi.separable

theorem solution :
    InverseGalois.IsRealizable ℚ (Equiv.Perm (Fin 5)) :=
  ⟨⟨{ L := (Φ ℚ).SplittingField
      to_field := inferInstance
      to_algebra := inferInstance
      to_isGalois := isGalois_Phi
      iso := ((Fintype.equivFinOfCardEq complex_roots_Phi).symm.permCongrHom).trans
        (MulEquiv.ofBijective (galActionHom (Φ ℚ) ℂ) gal_Phi).symm }⟩⟩
