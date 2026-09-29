-- Prove2me | solution 1 for MarkovEntanglement.separable_iff_resolvent_separable
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-07T17:53:32.303032+00:00
-- url     : https://prove2.me/submissions/f05be91c-ff24-46ad-bed2-4aa0a4f5e67d

import Definitions.Def_markov_entanglement_multi

open scoped BigOperators
open MarkovEntanglement Matrix

/-!
Chen and Peng, *Multi-agent Markov Entanglement*, arXiv:2506.02385v3, Lemma 4, p. 35.

The proof below avoids the source's spectral-radius / infinite-Neumann-series argument
entirely.  The observation is that the linear span `V` of the separable matrices is a
finite-dimensional unital subalgebra, and a finite-dimensional unital subalgebra is closed
under taking inverses: if `a ∈ V` is invertible in the full matrix algebra, then `v ↦ a * v`
is an injective linear endomorphism of `V`, hence surjective, so some `v ∈ V` has
`a * v = 1`, i.e. `a⁻¹ = v ∈ V`.

That gives membership in `V`, i.e. a *linear* combination of separables.  Upgrading to the
*affine* combination that `IsSeparableN` demands is free, via row sums: every separable
matrix has row sums one, so an element of `V` has row sums equal to its coefficient sum;
both `(1-γ)(1-γP)⁻¹` and `P` have row sums one, so in both directions the coefficients
automatically sum to one.
-/

namespace MarkovEntanglement

variable {N : ℕ} {S : Fin N → Type*} [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)]

/-! ### Algebraic closure properties of the separable set -/

theorem IsTransitionMatrix.mul' {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A B : Matrix ι ι ℝ} (hA : IsTransitionMatrix A) (hB : IsTransitionMatrix B) :
    IsTransitionMatrix (A * B) := by
  refine ⟨fun i j => Finset.sum_nonneg fun k _ => mul_nonneg (hA.1 i k) (hB.1 k j), fun i => ?_⟩
  simp only [Matrix.mul_apply]
  rw [Finset.sum_comm]
  calc ∑ k, ∑ j, A i k * B k j = ∑ k, A i k * ∑ j, B k j :=
        Finset.sum_congr rfl fun k _ => (Finset.mul_sum _ _ _).symm
    _ = ∑ k, A i k := Finset.sum_congr rfl fun k _ => by rw [hB.2 k, mul_one]
    _ = 1 := hA.2 i

theorem isTransitionMatrix_one' {ι : Type*} [Fintype ι] [DecidableEq ι] :
    IsTransitionMatrix (1 : Matrix ι ι ℝ) := by
  refine ⟨fun i j => ?_, fun i => by simp [Matrix.one_apply]⟩
  by_cases h : i = j <;> simp [Matrix.one_apply, h]

/-- Mixed-product property: `(⊗ᵢ Aᵢ)(⊗ᵢ Bᵢ) = ⊗ᵢ (Aᵢ Bᵢ)`. -/
theorem tensorProdN_mul' (A B : ∀ i, Matrix (S i) (S i) ℝ) :
    tensorProdN A * tensorProdN B = tensorProdN (fun i => A i * B i) := by
  classical
  ext p q
  simp only [Matrix.mul_apply, tensorProdN]
  calc ∑ u : Joint S, (∏ i, A i (p i) (u i)) * ∏ i, B i (u i) (q i)
      = ∑ u : Joint S, ∏ i, (A i (p i) (u i) * B i (u i) (q i)) :=
        Finset.sum_congr rfl fun u _ => (Finset.prod_mul_distrib).symm
    _ = ∏ i, ∑ t : S i, A i (p i) t * B i t (q i) :=
        (Fintype.prod_sum fun i t => A i (p i) t * B i t (q i)).symm
    _ = ∏ i, (A i * B i) (p i) (q i) := rfl

/-- An affine combination indexed by any `Fintype` witnesses separability. -/
theorem isSeparableN_of_fintype' {ι : Type*} [Fintype ι] {P : Matrix (Joint S) (Joint S) ℝ}
    (x : ι → ℝ) (Pj : ι → ∀ i, Matrix (S i) (S i) ℝ)
    (hPj : ∀ k i, IsTransitionMatrix (Pj k i)) (hx : ∑ k, x k = 1)
    (hP : P = ∑ k, x k • tensorProdN (Pj k)) : IsSeparableN P := by
  classical
  let e : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  refine ⟨Fintype.card ι, fun n => x (e n), fun n => Pj (e n), fun n i => hPj _ i, ?_, ?_⟩
  · rw [← hx]; exact Equiv.sum_comp e x
  · rw [hP]; exact (Equiv.sum_comp e (fun k => x k • tensorProdN (Pj k))).symm

theorem isSeparableN_one' : IsSeparableN (1 : Matrix (Joint S) (Joint S) ℝ) := by
  classical
  refine ⟨1, fun _ => 1, fun _ _ => 1, fun _ _ => isTransitionMatrix_one', by simp, ?_⟩
  ext p q
  simp only [Finset.univ_unique, Finset.sum_singleton, one_smul, tensorProdN]
  by_cases h : p = q
  · subst h; simp [Matrix.one_apply]
  · have hex : ∃ i, p i ≠ q i := by
      by_contra hc
      exact h (funext fun i => not_not.mp (fun hh => hc ⟨i, hh⟩))
    obtain ⟨i, hi⟩ := hex
    rw [Matrix.one_apply_ne h]
    symm
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [Matrix.one_apply, hi])

theorem isSeparableN_mul' {P Q : Matrix (Joint S) (Joint S) ℝ}
    (hP : IsSeparableN P) (hQ : IsSeparableN Q) : IsSeparableN (P * Q) := by
  classical
  obtain ⟨K, x, A, hA, hx, rfl⟩ := hP
  obtain ⟨L, y, B, hB, hy, rfl⟩ := hQ
  refine isSeparableN_of_fintype' (ι := Fin K × Fin L)
    (fun kl => x kl.1 * y kl.2) (fun kl i => A kl.1 i * B kl.2 i)
    (fun kl i => (hA _ i).mul' (hB _ i)) ?_ ?_
  · rw [Fintype.sum_prod_type]
    calc ∑ k, ∑ l, x k * y l = ∑ k, x k * ∑ l, y l :=
          Finset.sum_congr rfl fun k _ => (Finset.mul_sum _ _ _).symm
      _ = 1 := by rw [hy]; simpa using hx
  · rw [Fintype.sum_prod_type, Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by
      rw [smul_mul_smul_comm, tensorProdN_mul']

theorem tensorProdN_rowSum' (A : ∀ i, Matrix (S i) (S i) ℝ)
    (hA : ∀ i, IsTransitionMatrix (A i)) (p : Joint S) :
    ∑ q : Joint S, tensorProdN A p q = 1 := by
  classical
  calc ∑ q : Joint S, ∏ i, A i (p i) (q i)
      = ∏ i, ∑ t : S i, A i (p i) t := (Fintype.prod_sum fun i t => A i (p i) t).symm
    _ = 1 := Finset.prod_eq_one fun i _ => (hA i).2 (p i)

/-- Every separable matrix has row sums one. -/
theorem IsSeparableN.rowSum' {P : Matrix (Joint S) (Joint S) ℝ} (hP : IsSeparableN P)
    (p : Joint S) : ∑ q : Joint S, P p q = 1 := by
  classical
  obtain ⟨K, x, A, hA, hx, rfl⟩ := hP
  calc ∑ q : Joint S, (∑ k, x k • tensorProdN (A k)) p q
      = ∑ q : Joint S, ∑ k, x k * tensorProdN (A k) p q :=
        Finset.sum_congr rfl fun q _ => by rw [Matrix.sum_apply]; rfl
    _ = ∑ k, x k * ∑ q : Joint S, tensorProdN (A k) p q := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun k _ => (Finset.mul_sum _ _ _).symm
    _ = 1 := by
        rw [← hx]
        exact Finset.sum_congr rfl fun k _ => by
          rw [tensorProdN_rowSum' _ (fun i => hA k i) p, mul_one]

/-- The separable set is closed under affine combinations. -/
theorem isSeparableN_affineCombination' {ι : Type*} [Fintype ι] (c : ι → ℝ)
    (M : ι → Matrix (Joint S) (Joint S) ℝ) (hM : ∀ k, IsSeparableN (M k))
    (hc : ∑ k, c k = 1) : IsSeparableN (∑ k, c k • M k) := by
  classical
  choose K x A hA hx hrep using hM
  refine isSeparableN_of_fintype' (ι := Σ k : ι, Fin (K k))
    (fun kj => c kj.1 * x kj.1 kj.2) (fun kj i => A kj.1 kj.2 i)
    (fun kj i => hA kj.1 kj.2 i) ?_ ?_
  · rw [Fintype.sum_sigma]
    calc ∑ k, ∑ j, c k * x k j = ∑ k, c k * ∑ j, x k j :=
          Finset.sum_congr rfl fun k _ => (Finset.mul_sum _ _ _).symm
      _ = 1 := by rw [← hc]; exact Finset.sum_congr rfl fun k _ => by rw [hx k, mul_one]
  · rw [Fintype.sum_sigma]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hrep k, Finset.smul_sum]
    exact Finset.sum_congr rfl fun j _ => by rw [smul_smul]

/-! ### The span of the separable set -/

/-- Finite linear combinations of separable matrices. -/
def SepLin (M : Matrix (Joint S) (Joint S) ℝ) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι) (a : ι → ℝ) (T : ι → Matrix (Joint S) (Joint S) ℝ),
    (∀ k, IsSeparableN (T k)) ∧ M = ∑ k, a k • T k

theorem SepLin.of_separable {M : Matrix (Joint S) (Joint S) ℝ} (h : IsSeparableN M) :
    SepLin M :=
  ⟨PUnit, inferInstance, fun _ => 1, fun _ => M, fun _ => h, by simp⟩

theorem SepLin.zero : SepLin (0 : Matrix (Joint S) (Joint S) ℝ) :=
  ⟨Empty, inferInstance, fun k => k.elim, fun k => k.elim, fun k => k.elim, by simp⟩

theorem SepLin.add {M M' : Matrix (Joint S) (Joint S) ℝ} (h : SepLin M) (h' : SepLin M') :
    SepLin (M + M') := by
  obtain ⟨ι, _, a, T, hT, rfl⟩ := h
  obtain ⟨ι', _, a', T', hT', rfl⟩ := h'
  exact ⟨ι ⊕ ι', inferInstance, Sum.elim a a', Sum.elim T T',
    fun k => by cases k <;> simp [hT, hT'], by rw [Fintype.sum_sum_type]; simp⟩

theorem SepLin.smul (c : ℝ) {M : Matrix (Joint S) (Joint S) ℝ} (h : SepLin M) :
    SepLin (c • M) := by
  obtain ⟨ι, _, a, T, hT, rfl⟩ := h
  exact ⟨ι, inferInstance, fun k => c * a k, T, hT, by
    rw [Finset.smul_sum]; exact Finset.sum_congr rfl fun k _ => by rw [smul_smul]⟩

theorem SepLin.mul {M M' : Matrix (Joint S) (Joint S) ℝ} (h : SepLin M) (h' : SepLin M') :
    SepLin (M * M') := by
  obtain ⟨ι, _, a, T, hT, rfl⟩ := h
  obtain ⟨ι', _, a', T', hT', rfl⟩ := h'
  refine ⟨ι × ι', inferInstance, fun kl => a kl.1 * a' kl.2,
    fun kl => T kl.1 * T' kl.2, fun kl => isSeparableN_mul' (hT kl.1) (hT' kl.2), ?_⟩
  rw [Fintype.sum_prod_type, Finset.sum_mul_sum]
  exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by
    rw [smul_mul_smul_comm]

/-- The span of the separable set, as a submodule. -/
def SepSpan : Submodule ℝ (Matrix (Joint S) (Joint S) ℝ) where
  carrier := {M | SepLin M}
  add_mem' := SepLin.add
  zero_mem' := SepLin.zero
  smul_mem' := fun c _ h => SepLin.smul c h

theorem mem_sepSpan_iff {M : Matrix (Joint S) (Joint S) ℝ} :
    M ∈ (SepSpan (S := S)) ↔ SepLin M := Iff.rfl

/-- **A linear combination of separables with row sums one is separable.** Row sums pin the
coefficient sum, turning the linear combination into an affine one. -/
theorem isSeparableN_of_sepLin {M : Matrix (Joint S) (Joint S) ℝ} (h : SepLin M)
    (p₀ : Joint S) (hrow : ∀ p, ∑ q : Joint S, M p q = 1) : IsSeparableN M := by
  classical
  obtain ⟨ι, _, a, T, hT, rfl⟩ := h
  have hsum : ∑ k, a k = 1 := by
    have := hrow p₀
    calc ∑ k, a k = ∑ k, a k * ∑ q : Joint S, T k p₀ q :=
          Finset.sum_congr rfl fun k _ => by rw [(hT k).rowSum' p₀, mul_one]
      _ = ∑ q : Joint S, ∑ k, a k * T k p₀ q := by
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun k _ => Finset.mul_sum _ _ _
      _ = ∑ q : Joint S, (∑ k, a k • T k) p₀ q :=
          Finset.sum_congr rfl fun q _ => by rw [Matrix.sum_apply]; rfl
      _ = 1 := this
  exact isSeparableN_affineCombination' a T hT hsum

/-- **A finite-dimensional unital subalgebra is closed under inverses.** Left multiplication
by an invertible `a ∈ SepSpan` is an injective endomorphism of `SepSpan`, hence surjective,
so `1` is in its image. -/
theorem SepLin.inv {a : Matrix (Joint S) (Joint S) ℝ} (ha : SepLin a)
    (hu : IsUnit a.det) : SepLin a⁻¹ := by
  classical
  set V := SepSpan (S := S) with hV
  have haV : a ∈ V := ha
  have hone : (1 : Matrix (Joint S) (Joint S) ℝ) ∈ V := SepLin.of_separable isSeparableN_one'
  let f : V →ₗ[ℝ] V :=
    { toFun := fun v => ⟨a * (v : Matrix (Joint S) (Joint S) ℝ), SepLin.mul ha v.2⟩
      map_add' := fun x y => by ext : 1; simp [Matrix.mul_add]
      map_smul' := fun c x => by ext : 1; simp [Matrix.mul_smul] }
  have hinj : Function.Injective f := by
    intro x y hxy
    have h0 : a * (x : Matrix (Joint S) (Joint S) ℝ) = a * (y : Matrix _ _ ℝ) :=
      congrArg Subtype.val hxy
    have : (x : Matrix (Joint S) (Joint S) ℝ) = (y : Matrix _ _ ℝ) := by
      have := congrArg (fun M => a⁻¹ * M) h0
      simpa [← Matrix.mul_assoc, Matrix.nonsing_inv_mul a hu] using this
    exact Subtype.ext this
  obtain ⟨v, hv⟩ := LinearMap.injective_iff_surjective.mp hinj ⟨1, hone⟩
  have hav : a * (v : Matrix (Joint S) (Joint S) ℝ) = 1 := congrArg Subtype.val hv
  rw [Matrix.inv_eq_right_inv hav]
  exact v.2

/-! ### Invertibility of `1 - γ P` and the row-sum computations -/

/-- Unfolding `mulVec` to a plain sum. -/
theorem mulVec_apply' (M : Matrix (Joint S) (Joint S) ℝ) (w : Joint S → ℝ) (i : Joint S) :
    (M *ᵥ w) i = ∑ j, M i j * w j := rfl

/-- Rows of the identity sum to one. -/
theorem one_rowSum (q : Joint S) : ∑ r : Joint S, (1 : Matrix (Joint S) (Joint S) ℝ) q r = 1 := by
  classical
  simp [Matrix.one_apply]

/-- Rows of `1 - γ P` sum to `1 - γ`. -/
theorem one_sub_smul_rowSum (P : Matrix (Joint S) (Joint S) ℝ)
    (hP : IsTransitionMatrix P) (γ : ℝ) (q : Joint S) :
    ∑ r : Joint S, ((1 : Matrix (Joint S) (Joint S) ℝ) - γ • P) q r = 1 - γ := by
  classical
  have hpt : ∀ r, ((1 : Matrix (Joint S) (Joint S) ℝ) - γ • P) q r
      = (1 : Matrix (Joint S) (Joint S) ℝ) q r - γ * P q r := fun r => rfl
  simp_rw [hpt]
  rw [Finset.sum_sub_distrib, one_rowSum, ← Finset.mul_sum, hP.2 q, mul_one]

/-- For a transition matrix `P` and `0 ≤ γ < 1`, `1 - γ P` is invertible: a kernel vector
would attain its maximum modulus at some `i₀` and satisfy `|v i₀| ≤ γ |v i₀|` there. -/
theorem isUnit_det_one_sub_smul (P : Matrix (Joint S) (Joint S) ℝ)
    (hP : IsTransitionMatrix P) {γ : ℝ} (hγ : 0 ≤ γ) (hγ1 : γ < 1) [Nonempty (Joint S)] :
    IsUnit (1 - γ • P : Matrix (Joint S) (Joint S) ℝ).det := by
  classical
  rw [isUnit_iff_ne_zero]
  intro hdet
  obtain ⟨v, hv0, hker⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  obtain ⟨i₀, -, hmax⟩ :=
    Finset.exists_max_image (Finset.univ : Finset (Joint S)) (fun i => |v i|)
      Finset.univ_nonempty
  have hfix : ∀ i, v i = γ * ∑ j, P i j * v j := by
    intro i
    have h0 : ∑ j, ((1 : Matrix (Joint S) (Joint S) ℝ) - γ • P) i j * v j = 0 := by
      rw [← mulVec_apply', hker]; rfl
    have hpt : ∀ j, ((1 : Matrix (Joint S) (Joint S) ℝ) - γ • P) i j * v j
        = (1 : Matrix (Joint S) (Joint S) ℝ) i j * v j - γ * (P i j * v j) := by
      intro j; simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]; ring
    simp_rw [hpt] at h0
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum] at h0
    have hid : ∑ j, (1 : Matrix (Joint S) (Joint S) ℝ) i j * v j = v i := by
      simp [Matrix.one_apply]
    rw [hid] at h0
    linarith
  have hbound : |v i₀| ≤ γ * |v i₀| := by
    have h1 : |∑ j, P i₀ j * v j| ≤ ∑ j, P i₀ j * |v i₀| := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
      rw [abs_mul, abs_of_nonneg (hP.1 i₀ j)]
      exact mul_le_mul_of_nonneg_left (hmax j (Finset.mem_univ j)) (hP.1 i₀ j)
    have h2 : ∑ j, P i₀ j * |v i₀| = |v i₀| := by
      rw [← Finset.sum_mul, hP.2 i₀, one_mul]
    calc |v i₀| = |γ * ∑ j, P i₀ j * v j| := by rw [hfix i₀]
      _ = γ * |∑ j, P i₀ j * v j| := by rw [abs_mul, abs_of_nonneg hγ]
      _ ≤ γ * |v i₀| := mul_le_mul_of_nonneg_left (h1.trans_eq h2) hγ
  have hzero : |v i₀| = 0 := by nlinarith [abs_nonneg (v i₀)]
  exact hv0 (funext fun i => by
    have h := hmax i (Finset.mem_univ i)
    rw [hzero] at h
    exact abs_eq_zero.mp (le_antisymm h (abs_nonneg _)))

/-! ### Lemma 4 -/

theorem separable_iff_resolvent_separable_proof
    (P : Matrix (Joint S) (Joint S) ℝ) (γ : ℝ) (hγ : 0 < γ) (hγ1 : γ < 1)
    (hP : IsTransitionMatrix P) :
    IsSeparableN P ↔ IsSeparableN ((1 - γ) • (1 - γ • P)⁻¹) := by
  classical
  rcases isEmpty_or_nonempty (Joint S) with hE | hne
  · have huniv : ∀ M : Matrix (Joint S) (Joint S) ℝ, IsSeparableN M := by
      intro M
      exact ⟨1, fun _ => 1, fun _ _ => 1, fun _ _ => isTransitionMatrix_one', by simp,
        by ext p q; exact (hE.false p).elim⟩
    exact ⟨fun _ => huniv _, fun _ => huniv _⟩
  have hγ0 : (0:ℝ) ≤ γ := le_of_lt hγ
  have hone_sub : (0:ℝ) < 1 - γ := by linarith
  have hu : IsUnit (1 - γ • P : Matrix (Joint S) (Joint S) ℝ).det :=
    isUnit_det_one_sub_smul P hP hγ0 hγ1
  -- Row sums of the resolvent: from `A (1 - γP) = 1`, summing over the free index gives
  -- `(∑_q A p q) (1 - γ) = 1`.
  have hres_row : ∀ p, ∑ q : Joint S, ((1 - γ) • (1 - γ • P)⁻¹ : Matrix _ _ ℝ) p q = 1 := by
    intro p
    set A := (1 - γ • P : Matrix (Joint S) (Joint S) ℝ)⁻¹ with hA
    have hAI : A * (1 - γ • P) = 1 := Matrix.nonsing_inv_mul _ hu
    have hkey : (∑ q : Joint S, A p q) * (1 - γ) = 1 := by
      have h1 : ∑ r : Joint S, (A * (1 - γ • P)) p r = 1 := by rw [hAI]; exact one_rowSum p
      calc (∑ q : Joint S, A p q) * (1 - γ)
          = ∑ q : Joint S, A p q * (1 - γ) := by rw [Finset.sum_mul]
        _ = ∑ q : Joint S, A p q * ∑ r : Joint S,
              ((1 : Matrix (Joint S) (Joint S) ℝ) - γ • P) q r :=
            Finset.sum_congr rfl fun q _ => by rw [one_sub_smul_rowSum P hP γ q]
        _ = ∑ r : Joint S, (A * (1 - γ • P)) p r := by
            simp only [Matrix.mul_apply]
            rw [Finset.sum_comm]
            exact Finset.sum_congr rfl fun q _ => Finset.mul_sum _ _ _
        _ = 1 := h1
    have hApt : ∀ q, ((1 - γ) • A) p q = (1 - γ) * A p q := fun q => rfl
    simp_rw [hApt]
    rw [← Finset.mul_sum, mul_comm]
    exact hkey
  constructor
  · intro hsep
    have h2 : SepLin (-(γ • P) : Matrix (Joint S) (Joint S) ℝ) := by
      rw [← neg_smul]; exact SepLin.smul (-γ) (SepLin.of_separable hsep)
    have h1 : SepLin (1 - γ • P : Matrix (Joint S) (Joint S) ℝ) := by
      rw [sub_eq_add_neg]; exact SepLin.add (SepLin.of_separable isSeparableN_one') h2
    exact isSeparableN_of_sepLin (SepLin.smul _ (h1.inv hu)) (Classical.arbitrary _) hres_row
  · intro hsep
    have hUmul : ((1 - γ) • (1 - γ • P)⁻¹ : Matrix (Joint S) (Joint S) ℝ) *
        ((1 - γ)⁻¹ • (1 - γ • P)) = 1 := by
      rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul,
        Matrix.nonsing_inv_mul _ hu, mul_inv_cancel₀ (ne_of_gt hone_sub), one_smul]
    have hUdet : IsUnit ((1 - γ) • (1 - γ • P)⁻¹ : Matrix (Joint S) (Joint S) ℝ).det :=
      Matrix.isUnit_det_of_right_inverse hUmul
    have hUinv : ((1 - γ) • (1 - γ • P)⁻¹ : Matrix (Joint S) (Joint S) ℝ)⁻¹
        = (1 - γ)⁻¹ • (1 - γ • P) := Matrix.inv_eq_right_inv hUmul
    have hPlin : SepLin P := by
      have hUinvLin : SepLin ((1 - γ)⁻¹ • (1 - γ • P) : Matrix (Joint S) (Joint S) ℝ) := by
        rw [← hUinv]; exact (SepLin.of_separable hsep).inv hUdet
      have hExp : P = γ⁻¹ • ((1 : Matrix (Joint S) (Joint S) ℝ)
          + (-(1 - γ)) • ((1 - γ)⁻¹ • (1 - γ • P))) := by
        rw [smul_smul, neg_mul, mul_inv_cancel₀ (ne_of_gt hone_sub), neg_one_smul]
        have hcollapse : (1 : Matrix (Joint S) (Joint S) ℝ) + -(1 - γ • P) = γ • P := by abel
        rw [hcollapse, smul_smul, inv_mul_cancel₀ (ne_of_gt hγ), one_smul]
      rw [hExp]
      exact SepLin.smul _ (SepLin.add (SepLin.of_separable isSeparableN_one')
        (SepLin.smul _ hUinvLin))
    exact isSeparableN_of_sepLin hPlin (Classical.arbitrary _) (fun p => hP.2 p)

end MarkovEntanglement

/-- The submitted form. -/
theorem solution
    {N : ℕ} {S : Fin N → Type*} [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)]
    (P : Matrix (Joint S) (Joint S) ℝ) (γ : ℝ) (hγ : 0 < γ) (hγ1 : γ < 1)
    (hP : IsTransitionMatrix P) :
    IsSeparableN P ↔ IsSeparableN ((1 - γ) • (1 - γ • P)⁻¹) :=
  MarkovEntanglement.separable_iff_resolvent_separable_proof P γ hγ hγ1 hP
