-- Prove2me | solution 1 for LPCA.localization_piece_dimension
-- status  : ACCEPTED   (prove)
-- author  : @kaiyue
-- created : 2026-10-20T22:44:50.584144+00:00
-- url     : https://prove2.me/submissions/26b6490e-7d03-4cb6-b459-1913278217e3

import Definitions.Def_LPCA
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Tactic
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.MvPolynomial.Division


set_option autoImplicit false

namespace LPCA

universe u

variable {V : Type u} [DecidableEq V]
variable (k : Type u) [Field k]

private noncomputable def indicatorExponent (F : Finset V) : V →₀ ℕ :=
  Finsupp.indicator F (fun _ _ => 1)

private theorem invertedMonomial_eq (K : Complex V) (F : Finset V) :
    invertedMonomial k K F = Ideal.Quotient.mk (srIdeal k K)
      (MvPolynomial.monomial (indicatorExponent F) (1 : k)) := by
  unfold invertedMonomial variableClass
  rw [← map_prod]
  congr 1
  simpa only [indicatorExponent, pow_one] using
    MvPolynomial.prod_X_pow (R := k) (fun _ : V => 1) F

private theorem invertedMonomial_pow (K : Complex V) (F : Finset V) (N : ℕ) :
    invertedMonomial k K F ^ N = Ideal.Quotient.mk (srIdeal k K)
      (MvPolynomial.monomial (N • indicatorExponent F) (1 : k)) := by
  rw [invertedMonomial_eq, ← map_pow, MvPolynomial.monomial_pow, one_pow]

theorem localizedMonomial_eq_of_degree
    (K : Complex V) (F : Finset V) (a : V → ℤ)
    (m m' : V →₀ ℕ) (N N' : ℕ)
    (hm : ∀ j : V, (m j : ℤ) - (if j ∈ F then (N : ℤ) else 0) = a j)
    (hm' : ∀ j : V, (m' j : ℤ) - (if j ∈ F then (N' : ℤ) else 0) = a j) :
    localizedMonomial k K F m N = localizedMonomial k K F m' N' := by
  have hexponents : m + N' • indicatorExponent F = m' + N • indicatorExponent F := by
    ext j
    have h := hm j
    have h' := hm' j
    by_cases hj : j ∈ F
    · simp only [if_pos hj] at h h'
      simp only [Finsupp.add_apply, Finsupp.smul_apply, indicatorExponent,
        Finsupp.indicator_of_mem hj, smul_eq_mul, mul_one]
      omega
    · simp only [if_neg hj, sub_zero] at h h'
      simp only [Finsupp.add_apply, Finsupp.smul_apply, indicatorExponent,
        Finsupp.indicator_of_notMem hj, smul_zero, add_zero]
      omega
  unfold localizedMonomial
  apply IsLocalization.mk'_eq_iff_eq'.mpr
  apply congrArg (algebraMap (FaceRing k K) (LocalizedFaceRing k K F))
  dsimp only [Subtype.coe_mk]
  rw [invertedMonomial_pow, invertedMonomial_pow, ← map_mul, ← map_mul,
    MvPolynomial.monomial_mul, MvPolynomial.monomial_mul, one_mul, hexponents]

theorem localizedPiece_eq_span_of_rep
    (K : Complex V) (F : Finset V) (a : V → ℤ) (m : V →₀ ℕ) (N : ℕ)
    (hm : ∀ j : V, (m j : ℤ) - (if j ∈ F then (N : ℤ) else 0) = a j) :
    localizedPiece k K F a = Submodule.span k {localizedMonomial k K F m N} := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro z ⟨m', N', hm', rfl⟩
    rw [localizedMonomial_eq_of_degree k K F a m' m N' N hm' hm]
    exact Submodule.subset_span (Set.mem_singleton _)
  · apply Submodule.span_le.mpr
    intro z hz
    obtain rfl := Set.mem_singleton_iff.mp hz
    exact Submodule.subset_span ⟨m, N, hm, rfl⟩

theorem localizedPiece_finite_finrank_le_one
    (K : Complex V) (F : Finset V) (a : V → ℤ) :
    Module.Finite k (localizedPiece k K F a) ∧
      Module.finrank k (localizedPiece k K F a) ≤ 1 := by
  classical
  by_cases h : ∃ (m : V →₀ ℕ) (N : ℕ),
      ∀ j : V, (m j : ℤ) - (if j ∈ F then (N : ℤ) else 0) = a j
  · obtain ⟨m, N, hm⟩ := h
    rw [localizedPiece_eq_span_of_rep k K F a m N hm]
    exact ⟨Module.Finite.span_of_finite k (Set.finite_singleton _),
      by simpa using (finrank_span_le_card (R := k)
        ({localizedMonomial k K F m N} : Set (LocalizedFaceRing k K F)))⟩
  · have hzero : localizedPiece k K F a = ⊥ := by
      apply le_antisymm ?_ bot_le
      apply Submodule.span_le.mpr
      rintro z ⟨m, N, hm, _⟩
      exact False.elim (h ⟨m, N, hm⟩)
    rw [hzero]
    exact ⟨inferInstance, by simp⟩

end LPCA



set_option autoImplicit false

namespace LPCA

universe u

variable {V : Type u} [DecidableEq V]
variable (k : Type u) [Field k]

private noncomputable def faceEvaluation
    (K : Complex V) (G : Finset V) (hG : G ∈ K.faces) : FaceRing k K →+* k := by
  classical
  let evaluation : MvPolynomial V k →+* k :=
    MvPolynomial.eval (fun j => if j ∈ G then 1 else 0)
  have hkernel : srIdeal k K ≤ RingHom.ker evaluation := by
    apply Ideal.span_le.mpr
    rintro p ⟨H, hH, rfl⟩
    change evaluation (∏ j ∈ H, MvPolynomial.X j) = 0
    have hnsub : ¬ H ⊆ G := fun hHG => hH (K.down_closed hG hHG)
    obtain ⟨j, hjH, hjG⟩ := Finset.not_subset.mp hnsub
    rw [map_prod]
    apply Finset.prod_eq_zero hjH
    simp [evaluation, hjG]
  exact Ideal.Quotient.lift (srIdeal k K) evaluation
    (fun p hp => RingHom.mem_ker.mp (hkernel hp))

private theorem faceEvaluation_monomial
    (K : Complex V) (G : Finset V) (hG : G ∈ K.faces)
    (m : V →₀ ℕ) (hm : m.support ⊆ G) :
    faceEvaluation k K G hG
      (Ideal.Quotient.mk (srIdeal k K) (MvPolynomial.monomial m (1 : k))) = 1 := by
  classical
  change MvPolynomial.eval (fun j => if j ∈ G then (1 : k) else 0)
    (MvPolynomial.monomial m 1) = 1
  rw [MvPolynomial.eval_monomial, one_mul]
  apply Finset.prod_eq_one
  intro j hj
  simp [hm hj]

private theorem faceEvaluation_inverted
    (K : Complex V) (G : Finset V) (hG : G ∈ K.faces)
    (F : Finset V) (hF : F ⊆ G) :
    faceEvaluation k K G hG (invertedMonomial k K F) = 1 := by
  classical
  unfold invertedMonomial
  rw [map_prod]
  apply Finset.prod_eq_one
  intro j hj
  change MvPolynomial.eval (fun j => if j ∈ G then (1 : k) else 0)
    (MvPolynomial.X j) = 1
  simp [hF hj]

theorem localizedMonomial_ne_zero_of_face
    (K : Complex V) (F : Finset V) (m : V →₀ ℕ) (N : ℕ)
    (hface : m.support ∈ K.faces) (hF : F ⊆ m.support) :
    localizedMonomial k K F m N ≠ 0 := by
  intro hz
  unfold localizedMonomial at hz
  rw [IsLocalization.mk'_eq_zero_iff] at hz
  obtain ⟨r, hr⟩ := hz
  obtain ⟨r, rN, rfl⟩ := r
  have heval := congrArg (faceEvaluation k K m.support hface) hr
  simp only [map_mul, map_pow, map_zero,
    faceEvaluation_inverted k K m.support hface F hF,
    faceEvaluation_monomial k K m.support hface m (Finset.Subset.refl _),
    one_pow, one_mul] at heval
  exact one_ne_zero heval

theorem monomial_zero_of_nonface
    (K : Complex V) (m : V →₀ ℕ) (hface : m.support ∉ K.faces) :
    Ideal.Quotient.mk (srIdeal k K) (MvPolynomial.monomial m (1 : k)) = 0 := by
  classical
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  let e : V →₀ ℕ := Finsupp.indicator m.support (fun _ _ => 1)
  have hproduct : (∏ j ∈ m.support, (MvPolynomial.X j : MvPolynomial V k)) =
      MvPolynomial.monomial e 1 := by
    simpa only [e, pow_one] using
      MvPolynomial.prod_X_pow (R := k) (fun _ : V => 1) m.support
  have hgen : MvPolynomial.monomial e (1 : k) ∈ srIdeal k K := by
    rw [← hproduct]
    exact Ideal.subset_span ⟨m.support, hface, rfl⟩
  have hle : e ≤ m := by
    intro j
    by_cases hj : j ∈ m.support
    · simpa only [e, Finsupp.indicator_of_mem hj] using
        Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hj)
    · simp [e, Finsupp.indicator_of_notMem hj]
  have hdiv : MvPolynomial.monomial e (1 : k) ∣ MvPolynomial.monomial m (1 : k) :=
    MvPolynomial.monomial_dvd_monomial.mpr ⟨Or.inr hle, dvd_refl 1⟩
  obtain ⟨p, hp⟩ := hdiv
  rw [hp]
  exact Ideal.mul_mem_right _ _ hgen

section FiniteVertices

variable [Fintype V]

theorem exists_positive_denominator_rep
    (F : Finset V) (a : V → ℤ) (hnonnegative : ∀ j : V, j ∉ F → 0 ≤ a j) :
    ∃ (m : V →₀ ℕ) (N : ℕ),
      (∀ j : V, (m j : ℤ) - (if j ∈ F then (N : ℤ) else 0) = a j) ∧
      m.support = positiveSupport a ∪ F := by
  classical
  let N : ℕ := (∑ j : V, (-a j).toNat) + 1
  have hpositive : ∀ j : V, 0 < a j + (N : ℤ) := by
    intro j
    have hsum : (-a j).toNat ≤ ∑ v : V, (-a v).toNat :=
      Finset.single_le_sum (f := fun v : V => (-a v).toNat)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
    have hcast : (-a j) ≤ ((-a j).toNat : ℤ) := Int.self_le_toNat _
    dsimp only [N]
    omega
  let m : V →₀ ℕ := Finsupp.equivFunOnFinite.symm
    (fun j => (a j + if j ∈ F then (N : ℤ) else 0).toNat)
  have hcast : ∀ j : V, (m j : ℤ) = a j + if j ∈ F then (N : ℤ) else 0 := by
    intro j
    have hz : 0 ≤ a j + if j ∈ F then (N : ℤ) else 0 := by
      by_cases hj : j ∈ F
      · simpa only [if_pos hj] using le_of_lt (hpositive j)
      · simpa only [if_neg hj, add_zero] using hnonnegative j hj
    simpa [m] using Int.toNat_of_nonneg hz
  refine ⟨m, N, ?_, ?_⟩
  · intro j
    rw [hcast]
    omega
  · ext j
    simp only [Finsupp.mem_support_iff, positiveSupport, Finset.mem_union,
      Finset.mem_filter, Finset.mem_univ, true_and]
    have hc := hcast j
    by_cases hj : j ∈ F
    · have hp := hpositive j
      simp only [if_pos hj] at hc
      simp only [hj, or_true, iff_true]
      have hmpositive : 0 < (m j : ℤ) := by simpa only [← hc] using hp
      exact_mod_cast ne_of_gt hmpositive
    · simp only [if_neg hj, add_zero] at hc
      simp only [hj, or_false]
      omega

attribute [local instance] Classical.propDecidable

theorem localization_piece_dimension_proved
    (K : Complex V) (F : Finset V) (a : V → ℤ) :
    Module.Finite k (localizedPiece k K F a) ∧
      Module.finrank k (localizedPiece k K F a) =
        (if LocalizationCriterion K F a then 1 else 0) := by
  classical
  refine ⟨(localizedPiece_finite_finrank_le_one k K F a).1, ?_⟩
  by_cases hnonnegative : ∀ j : V, j ∉ F → 0 ≤ a j
  · obtain ⟨m, N, hm, hsupp⟩ := exists_positive_denominator_rep F a hnonnegative
    rw [localizedPiece_eq_span_of_rep k K F a m N hm]
    by_cases hface : m.support ∈ K.faces
    · have hcriterion : LocalizationCriterion K F a := ⟨hnonnegative, hsupp ▸ hface⟩
      rw [if_pos hcriterion]
      apply finrank_span_singleton
      apply localizedMonomial_ne_zero_of_face k K F m N hface
      rw [hsupp]
      exact Finset.subset_union_right
    · have hcriterion : ¬ LocalizationCriterion K F a := by
        intro hc
        exact hface (hsupp.symm ▸ hc.2)
      rw [if_neg hcriterion]
      have hzero : localizedMonomial k K F m N = 0 := by
        unfold localizedMonomial
        rw [monomial_zero_of_nonface k K m hface, IsLocalization.mk'_zero]
      rw [hzero]
      simp
  · have hcriterion : ¬ LocalizationCriterion K F a := fun h => hnonnegative h.1
    rw [if_neg hcriterion]
    have hzero : localizedPiece k K F a = ⊥ := by
      apply le_antisymm ?_ bot_le
      apply Submodule.span_le.mpr
      rintro z ⟨m, N, hm, _⟩
      apply False.elim
      apply hnonnegative
      intro j hj
      have hd := hm j
      rw [if_neg hj, sub_zero] at hd
      exact hd ▸ Int.natCast_nonneg (m j)
    rw [hzero]
    simp

end FiniteVertices
end LPCA


attribute [local instance] Classical.propDecidable

universe u

theorem solution
    {V : Type u} [DecidableEq V] [Fintype V]
    (k : Type u) [Field k] (K : LPCA.Complex V) (F : Finset V) (a : V → ℤ) :
    Module.Finite k (LPCA.localizedPiece k K F a) ∧
      Module.finrank k (LPCA.localizedPiece k K F a) =
        (if LPCA.LocalizationCriterion K F a then 1 else 0) := by
  exact LPCA.localization_piece_dimension_proved k K F a

#print axioms solution
