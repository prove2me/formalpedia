-- Prove2me | solution 1 for OAI.Release075.main
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T15:29:52.749079+00:00
-- url     : https://prove2.me/submissions/069bf14c-875c-4feb-95bb-5c1ea4e99493

import Mathlib
import Definitions.Def_TorsionFreeHyperbolic

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : p) :
    (if p then a else b) = a := if_pos h
theorem ite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : ¬p) :
    (if p then a else b) = b := if_neg h
theorem dite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : p) :
    (if hp : p then a hp else b hp) = a h := dif_pos h
theorem dite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : ¬p) :
    (if hp : p then a hp else b hp) = b h := dif_neg h
/-- Mathlib's newer name for `measurable_pi_lambda` (with `f` implicit). -/
theorem Measurable.of_eval {δ ι : Type*} {π : ι → Type*} [MeasurableSpace δ]
    [∀ i, MeasurableSpace (π i)] {f : δ → ∀ i, π i}
    (h : ∀ i, Measurable fun a => f a i) : Measurable f := measurable_pi_lambda f h
alias Finset.prod_le_prod₀ := Finset.prod_le_prod
end OAICompat434

universe u v

section
section
namespace OAI

namespace Release075

end Release075

end OAI
end
end

section
section
namespace OAI

namespace Release075


open scoped BigOperators

theorem det_abs_le_prod_row_norm {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    |A.det| ≤ ∏ i, ‖(WithLp.toLp 2 (A i) : EuclideanSpace ℝ (Fin n))‖ := by
  let b := EuclideanSpace.basisFun (Fin n) ℝ
  let v : Fin n → EuclideanSpace ℝ (Fin n) := fun i => WithLp.toLp 2 (A i)
  have : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = n) := ⟨by simp⟩
  have h := b.toBasis.orientation.abs_volumeForm_apply_le v
  rw [b.toBasis.orientation.volumeForm_robust b rfl] at h
  have hmat : b.toBasis.toMatrix v = A.transpose := by
    ext i j
    simp [Module.Basis.toMatrix_apply, b, v, Matrix.transpose_apply]
  simpa [Module.Basis.det_apply, hmat, Matrix.det_transpose, v] using h

/-- A matrix has a spanning independent subset of its rows, with the expected size. -/
theorem exists_row_basis {ι κ K : Type*} [Fintype ι] [Fintype κ] [Field K]
    (M : Matrix ι κ K) :
    ∃ S : Finset ι, S.card = M.rank ∧
      LinearIndependent K (fun i : S => M i.val) ∧
      ∀ i, ∃ c : S → K, M i = ∑ j : S, c j • M j.val := by
  classical
  obtain ⟨T, _, _, hspan, hlin⟩ := exists_linearIndepOn_extension
    (linearIndepOn_empty K M.row) (Set.empty_subset (Set.univ : Set ι))
  let S := T.toFinset
  have hS : (S : Set ι) = T := Set.coe_toFinset T
  have hlinS : LinearIndepOn K M.row (S : Set ι) := by rw [hS]; exact hlin
  have hrange : Set.range (fun i : S => M.row i.val) = M.row '' (S : Set ι) := by
    ext x
    simp
  have hsp : Submodule.span K (Set.range (fun i : S => M.row i.val)) =
      Submodule.span K (Set.range M.row) := by
    rw [hrange]
    apply le_antisymm
    · exact Submodule.span_mono (Set.image_subset_range _ _)
    · apply Submodule.span_le.mpr
      rw [hS]
      simpa only [Set.image_univ] using hspan
  refine ⟨S, ?_, hlinS, ?_⟩
  · rw [M.rank_eq_finrank_span_row, ← hsp]
    simpa only [Finset.coe_sort_coe, Fintype.card_coe] using (finrank_span_eq_card hlinS).symm
  · intro i
    have hi : M.row i ∈ Submodule.span K (Set.range (fun j : S => M.row j.val)) := by
      rw [hsp]
      exact Submodule.subset_span (Set.mem_range_self i)
    rcases (Submodule.mem_span_range_iff_exists_fun K).mp hi with ⟨c, hc⟩
    exact ⟨c, hc.symm⟩

/-- Factoring a common divisor from all rows outside a specified set. -/
theorem pow_sub_card_dvd_det {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℤ) (S : Finset ι) (q : ℤ)
    (h : ∀ i, i ∉ S → ∀ j, q ∣ A i j) :
    q ^ (Fintype.card ι - S.card) ∣ A.det := by
  classical
  have hd : ∀ i j, (if i ∈ S then (1 : ℤ) else q) ∣ A i j := by
    intro i j
    split_ifs with hi
    · exact one_dvd _
    · exact h i hi j
  choose B hB using hd
  have hA : A = Matrix.of (fun i j => (if i ∈ S then (1 : ℤ) else q) * B i j) := by
    ext i j
    exact hB i j
  have hprod : (∏ i : ι, if i ∈ S then (1 : ℤ) else q) =
      q ^ (Fintype.card ι - S.card) := by
    simp only [Finset.prod_ite, Finset.prod_const_one, one_mul, Finset.prod_const]
    congr 1
    have hcard := Finset.card_filter_add_card_filter_not (s := Finset.univ) (· ∈ S)
    have hfilter : Finset.univ.filter (· ∈ S) = S := by ext; simp
    rw [hfilter, Finset.card_univ] at hcard
    omega
  refine ⟨Matrix.det (Matrix.of B), ?_⟩
  rw [hA]
  simpa only [hprod, Matrix.of_apply] using Matrix.det_mul_column (fun i => if i ∈ S then (1 : ℤ) else q) (Matrix.of B)

/-- The integral determinant detects the rank lost in reduction modulo a prime. -/
theorem pow_card_sub_rank_dvd_det {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℤ) (q : ℕ) [Fact q.Prime] :
    (q : ℤ) ^ (Fintype.card ι - (A.map (Int.cast : ℤ → ZMod q)).rank) ∣ A.det := by
  classical
  let M : Matrix ι ι (ZMod q) := A.map Int.cast
  obtain ⟨S, hScard, _, hspan⟩ := exists_row_basis M
  choose c hc using hspan
  let C : Matrix ι ι ℤ := fun i j =>
    if i ∈ S then 0 else if hj : j ∈ S then (c i ⟨j, hj⟩).cast else 0
  have hCC : C * C = 0 := by
    ext i j
    simp only [Matrix.mul_apply, Matrix.zero_apply]
    apply Finset.sum_eq_zero
    intro k _
    by_cases hk : k ∈ S
    · simp [C, hk]
    · by_cases hi : i ∈ S <;> simp [C, hi, hk]
  have hunit : IsUnit (1 - C).det := by
    apply isUnit_iff_dvd_one.mpr
    refine ⟨(1 + C).det, ?_⟩
    rw [← Matrix.det_mul]
    have hinv : (1 - C) * (1 + C) = 1 := by
      simp [mul_add, sub_mul, hCC]
    rw [hinv, Matrix.det_one]
  have hdiv : ∀ i, i ∉ S → ∀ j, (q : ℤ) ∣ ((1 - C) * A) i j := by
    intro i hi j
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ q).mp
    rw [sub_mul, one_mul]
    simp only [Matrix.sub_apply, Matrix.mul_apply, Int.cast_sub, Int.cast_sum, Int.cast_mul]
    apply sub_eq_zero.mpr
    have hrestrict : (∑ k : ι, (C i k : ZMod q) * (A k j : ZMod q)) =
        ∑ k ∈ S, (C i k : ZMod q) * (A k j : ZMod q) := by
      symm
      apply Finset.sum_subset (Finset.subset_univ S)
      intro k _ hk
      simp [C, hi, hk]
    rw [hrestrict, ← Finset.sum_coe_sort]
    have heval := congrArg (fun v : ι → ZMod q => v j) (hc i)
    simpa [C, hi, M, Matrix.map_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using heval
  have hd := pow_sub_card_dvd_det ((1 - C) * A) S (q : ℤ) hdiv
  rw [Matrix.det_mul] at hd
  rw [← hScard]
  exact hunit.dvd_mul_left.mp hd

/-- A full-rank minor exists over a field; both index maps are injective. -/
theorem exists_full_rank_minor {ι κ K : Type*} [Fintype ι] [Fintype κ] [Field K]
    (M : Matrix ι κ K) :
    ∃ (f : Fin M.rank → ι) (g : Fin M.rank → κ),
      Function.Injective f ∧ Function.Injective g ∧ (M.submatrix f g).det ≠ 0 := by
  classical
  obtain ⟨S, hScard, hSlin, _⟩ := exists_row_basis M
  have hScard' : Fintype.card S = M.rank := by simpa using hScard
  let eS : Fin M.rank ≃ S := (Fintype.equivFinOfCardEq hScard').symm
  let f : Fin M.rank → ι := fun i => (eS i).val
  let R : Matrix (Fin M.rank) κ K := M.submatrix f id
  have hRlin : LinearIndependent K R.row := hSlin.comp eS eS.injective
  have hRrank : R.rank = M.rank := by
    simpa only [Fintype.card_fin] using hRlin.rank_matrix
  obtain ⟨T, hTcard, hTlin, _⟩ := exists_row_basis R.transpose
  have hTcard' : Fintype.card T = M.rank := by
    simpa only [Fintype.card_coe, Matrix.rank_transpose, hRrank] using hTcard
  let eT : Fin M.rank ≃ T := (Fintype.equivFinOfCardEq hTcard').symm
  let g : Fin M.rank → κ := fun i => (eT i).val
  have hBlin : LinearIndependent K (M.submatrix f g).col := hTlin.comp eT eT.injective
  refine ⟨f, g, Subtype.val_injective.comp eS.injective,
    Subtype.val_injective.comp eT.injective, ?_⟩
  exact Matrix.nonsingular_iff_det_ne_zero.mp (Matrix.Nonsingular.of_linearIndependent_col hBlin)

/-- The squared form of Hadamard's inequality avoids fractional exponents. -/
theorem det_sq_le_pow_of_row_sq_le {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (r : ℝ) (hrow : ∀ i, ∑ j, A i j ^ 2 ≤ r) : A.det ^ 2 ≤ r ^ n := by
  have h := det_abs_le_prod_row_norm A
  have hsquare : A.det ^ 2 ≤
      (∏ i, ‖(WithLp.toLp 2 (A i) : EuclideanSpace ℝ (Fin n))‖) ^ 2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg A.det) h 2
  rw [← Finset.prod_pow] at hsquare
  apply hsquare.trans
  calc
    (∏ i, ‖(WithLp.toLp 2 (A i) : EuclideanSpace ℝ (Fin n))‖ ^ 2)
        ≤ ∏ _i : Fin n, r := by
      apply Finset.prod_le_prod₀
      · intro i _; positivity
      · intro i _
        simpa only [EuclideanSpace.real_norm_sq_eq] using hrow i
    _ = r ^ n := by simp

/-- A nonsingular integer matrix loses less than half its rank modulo a prime
larger than the common squared row-norm bound. -/
theorem nonsingular_rank_reduction_half {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ)
    (hdet : A.det ≠ 0) (r : ℝ) (hr : 1 ≤ r)
    (hrow : ∀ i, ∑ j, (A i j : ℝ) ^ 2 ≤ r)
    (q : ℕ) [Fact q.Prime] (hqr : r < q) :
    n ≤ 2 * (A.map (Int.cast : ℤ → ZMod q)).rank := by
  let AR : Matrix (Fin n) (Fin n) ℝ := A.map Int.cast
  let d := (A.map (Int.cast : ℤ → ZMod q)).rank
  have hcastdet : AR.det = (A.det : ℝ) := by
    simpa [AR] using (RingHom.map_det (Int.castRingHom ℝ) A).symm
  have hbound : AR.det ^ 2 ≤ r ^ n := det_sq_le_pow_of_row_sq_le AR r hrow
  have hdiv : (q : ℤ) ^ (n - d) ∣ A.det := by
    simpa only [Fintype.card_fin] using pow_card_sub_rank_dvd_det A q
  have hleI : (q : ℤ) ^ (n - d) ≤ |A.det| :=
    Int.le_of_dvd (abs_pos.mpr hdet) ((dvd_abs _ _).mpr hdiv)
  have hleR : (q : ℝ) ^ (n - d) ≤ |AR.det| := by
    rw [hcastdet]
    exact_mod_cast hleI
  have hsq := pow_le_pow_left₀ (pow_nonneg (Nat.cast_nonneg q) (n - d)) hleR 2
  rw [sq_abs, ← pow_mul] at hsq
  by_cases hn : n = 0
  · simp [hn]
  have hrnonneg : 0 ≤ r := le_trans zero_le_one hr
  have hstrict : (q : ℝ) ^ ((n - d) * 2) < (q : ℝ) ^ n :=
    (hsq.trans hbound).trans_lt (pow_lt_pow_left₀ hqr hrnonneg hn)
  have hexp : (n - d) * 2 < n :=
    (pow_lt_pow_iff_right₀ (lt_of_le_of_lt hr hqr)).mp hstrict
  change n ≤ 2 * d
  omega

theorem rank_reduction_half {ι κ : Type*} [Fintype ι] [Fintype κ]
    (M : Matrix ι κ ℤ) (r : ℝ) (hr : 1 ≤ r)
    (hrow : ∀ i, ∑ j, (M i j : ℝ) ^ 2 ≤ r)
    (q : ℕ) [Fact q.Prime] (hqr : r < q) :
    (M.map (Int.cast : ℤ → ℝ)).rank ≤
      2 * (M.map (Int.cast : ℤ → ZMod q)).rank := by
  classical
  let MR := M.map (Int.cast : ℤ → ℝ)
  obtain ⟨f, g, _, hg, hdet⟩ := exists_full_rank_minor MR
  let B := M.submatrix f g
  have hBR : B.map (Int.cast : ℤ → ℝ) = MR.submatrix f g := by
    rw [Matrix.submatrix_map]
  have hBdet : B.det ≠ 0 := by
    intro h
    apply hdet
    have hcast : (B.map (Int.cast : ℤ → ℝ)).det = (B.det : ℝ) := by
      simpa using (RingHom.map_det (Int.castRingHom ℝ) B).symm
    rw [← hBR, hcast, h]
    simp
  have hBrow : ∀ i, ∑ j, (B i j : ℝ) ^ 2 ≤ r := by
    intro i
    apply le_trans _ (hrow (f i))
    change (∑ j, (M (f i) (g j) : ℝ) ^ 2) ≤ _
    rw [← Finset.sum_image (f := fun j => (M (f i) j : ℝ) ^ 2)
      (s := Finset.univ) hg.injOn]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (by
      intro j _ _; positivity)
  have hh := nonsingular_rank_reduction_half B hBdet r hr hBrow q hqr
  apply hh.trans
  apply Nat.mul_le_mul_left
  change ((M.submatrix f g).map (Int.cast : ℤ → ZMod q)).rank ≤ _
  rw [← Matrix.submatrix_map]
  exact Matrix.rank_submatrix_le _ _ _

/-- The trace-rank inequality used on a Gram matrix in the finite quotient. -/
theorem trace_sq_le_rank_mul_trace_sq {ι : Type*} [Fintype ι]
    (A : Matrix ι ι ℝ) (hA : A.IsHermitian) :
    A.trace ^ 2 ≤ (A.rank : ℝ) * (A * A).trace := by
  classical
  have htrace : (A * A).trace = ∑ i, hA.eigenvalues i ^ 2 := by
    conv_lhs => rw [hA.spectral_theorem, ← map_mul, Matrix.diagonal_mul_diagonal,
      Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle, Unitary.coe_star_mul_self,
      one_mul, Matrix.trace_diagonal]
    simp [pow_two]
  rw [hA.trace_eq_sum_eigenvalues, htrace, hA.rank_eq_card_non_zero_eigs]
  let T : Finset ι := Finset.univ.filter (fun i => hA.eigenvalues i ≠ 0)
  have hcard : Fintype.card {i // hA.eigenvalues i ≠ 0} = T.card := by
    simp [T, Fintype.card_subtype]
  have hsum : (∑ i ∈ T, hA.eigenvalues i) = ∑ i, hA.eigenvalues i :=
    Finset.sum_filter_ne_zero _
  have hsum2 : (∑ i ∈ T, hA.eigenvalues i ^ 2) = ∑ i, hA.eigenvalues i ^ 2 := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro i _ hi
    have : hA.eigenvalues i = 0 := by simpa [T] using hi
    simp [this]
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq T (fun _ => (1 : ℝ)) hA.eigenvalues
  simpa [hsum, hsum2, hcard] using hcs

/-- Subadditivity of matrix rank over a field. -/
theorem rank_add_le {ι κ K : Type*} [Fintype ι] [Fintype κ] [Field K]
    (A B : Matrix ι κ K) : (A + B).rank ≤ A.rank + B.rank := by
  rw [Matrix.rank, Matrix.mulVecLin_add]
  exact (Submodule.finrank_mono (LinearMap.range_add_le _ _)).trans
    (Submodule.finrank_add_le_finrank_add_finrank _ _)

theorem rank_sum_le {ι κ τ K : Type*} [Fintype ι] [Fintype κ] [Field K]
    (s : Finset τ) (A : τ → Matrix ι κ K) : (∑ t ∈ s, A t).rank ≤ ∑ t ∈ s, (A t).rank := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Matrix.rank_zero]
  | @insert t s ht ih =>
    simp only [Finset.sum_insert ht]
    exact (rank_add_le _ _).trans (Nat.add_le_add_left ih _)

/-- The left regular permutation representation over any coefficient semiring. -/
def regularMatrix {F R : Type*} [Group F] [Fintype F] [DecidableEq F] [Semiring R] :
    F →* Matrix F F R := Matrix.permMatrixHom.comp (MulAction.toPermHom F F)

@[simp] theorem regularMatrix_apply {F R : Type*} [Group F] [Fintype F]
    [DecidableEq F] [Semiring R] (g a b : F) :
    regularMatrix (R := R) g a b = if a = g * b then 1 else 0 := by
  simp [regularMatrix, Matrix.permMatrixHom, Equiv.Perm.permMatrix,
    PEquiv.toMatrix, Equiv.toPEquiv_apply, inv_mul_eq_iff_eq_mul]

@[simp] theorem regularMatrix_transpose {F R : Type*} [Group F] [Fintype F]
    [DecidableEq F] [Semiring R] (g : F) :
    (regularMatrix (R := R) g).transpose = regularMatrix g⁻¹ := by
  ext a b
  simp [eq_inv_mul_iff_mul_eq, eq_comm]

@[simp] theorem regularMatrix_trace {F R : Type*} [Group F] [Fintype F]
    [DecidableEq F] [Semiring R] (g : F) :
    (regularMatrix (R := R) g).trace = if g = 1 then (Fintype.card F : R) else 0 := by
  by_cases hg : g = 1
  · subst g; simp
  · have hfix : ∀ a : F, a ≠ g * a := by
      intro a ha
      exact hg (mul_right_cancel (show g * a = 1 * a by simpa using ha.symm))
    simp [Matrix.trace, hfix, hg]

/-- Flatten a rectangular matrix of blocks, with the block index first. -/
def flattenMatrix {ι κ α β R : Type*} (A : Matrix ι κ (Matrix α β R)) :
    Matrix (ι × α) (κ × β) R := fun i j => A i.1 j.1 i.2 j.2

@[simp] theorem flattenMatrix_apply {ι κ α β R : Type*}
    (A : Matrix ι κ (Matrix α β R)) (i : ι × α) (j : κ × β) :
    flattenMatrix A i j = A i.1 j.1 i.2 j.2 := rfl

theorem flattenMatrix_mul {ι κ τ F R : Type*} [Fintype κ] [Fintype F]
    [DecidableEq F] [Semiring R] (A : Matrix ι κ (Matrix F F R))
    (B : Matrix κ τ (Matrix F F R)) :
    flattenMatrix (A * B) = flattenMatrix A * flattenMatrix B := by
  ext ⟨i,a⟩ ⟨j,b⟩
  simp [flattenMatrix, Matrix.mul_apply, Fintype.sum_prod_type, Matrix.sum_apply]

theorem flattenMatrix_transpose {ι κ α β R : Type*}
    (A : Matrix ι κ (Matrix α β R)) :
    (flattenMatrix A).transpose = flattenMatrix (Matrix.of fun i j => (A j i).transpose) := rfl

theorem flattenMatrix_trace {ι F R : Type*} [Fintype ι] [Fintype F]
    [AddCommMonoid R] (A : Matrix ι ι (Matrix F F R)) :
    (flattenMatrix A).trace = ∑ i, (A i i).trace := by
  simp [Matrix.trace, Fintype.sum_prod_type, flattenMatrix]

/-- The block regular-representation matrix attached to one line label. -/
def quotientMatrix {ι F R : Type*} [Group F] [Fintype F] [DecidableEq F]
    [Semiring R] (g : ι → ι → F) : Matrix (ι × F) (ι × F) R :=
    flattenMatrix (Matrix.of fun u v => regularMatrix (g u v))

theorem quotientMatrix_gram {ι F R : Type*} [Fintype ι] [Group F]
    [Fintype F] [DecidableEq F] [Semiring R] (g : ι → ι → F) :
    quotientMatrix (R := R) g * (quotientMatrix g).transpose =
      flattenMatrix (Matrix.of fun u u' => ∑ v, regularMatrix (g u v * (g u' v)⁻¹)) := by
  rw [quotientMatrix, flattenMatrix_transpose, ← flattenMatrix_mul]
  congr 1
  ext u u' a b
  simp [Matrix.of_apply, Matrix.mul_apply, Matrix.sum_apply, ← map_mul]

theorem quotientMatrix_gram_trace {ι F R : Type*} [Fintype ι] [Group F]
    [Fintype F] [DecidableEq F] [Semiring R] (g : ι → ι → F) :
    (quotientMatrix (R := R) g * (quotientMatrix g).transpose).trace =
      (Fintype.card ι : R) ^ 2 * Fintype.card F := by
  rw [quotientMatrix_gram, flattenMatrix_trace]
  simp only [Matrix.of_apply, mul_inv_cancel, map_one, Matrix.trace_sum]
  simp [pow_two, mul_assoc]

/-- The second trace expansion, before counting degenerate rectangles. -/
theorem quotientMatrix_gram_sq_trace {ι F R : Type*} [Fintype ι] [Group F]
    [Fintype F] [DecidableEq F] [Semiring R] (g : ι → ι → F) :
    ((quotientMatrix (R := R) g * (quotientMatrix g).transpose) *
      (quotientMatrix g * (quotientMatrix g).transpose)).trace =
        ∑ u, ∑ u', ∑ v, ∑ v', (regularMatrix (R := R)
          (g u v * (g u' v)⁻¹ * g u' v' * (g u v')⁻¹)).trace := by
  rw [quotientMatrix_gram, ← flattenMatrix_mul, flattenMatrix_trace]
  simp only [Matrix.mul_apply, Matrix.of_apply, Matrix.sum_mul, Matrix.mul_sum, ← map_mul,
    Matrix.trace_sum, mul_assoc]
  apply Finset.sum_congr rfl
  intro u _
  apply Finset.sum_congr rfl
  intro u' _
  exact Finset.sum_comm

/-- Nondegenerate rectangular words survive in the finite group. -/
def RectanglesSurvive {ι F : Type*} [Group F] (g : ι → ι → F) : Prop :=
  ∀ u u' v v', u ≠ u' → v ≠ v' →
    g u v * (g u' v)⁻¹ * g u' v' * (g u v')⁻¹ ≠ 1

/-- The exact count `2r^3-r^2` of degenerate index choices. -/
theorem quotientMatrix_gram_sq_trace_of_rectangles {ι F R : Type*} [Fintype ι]
    [Group F] [Fintype F] [DecidableEq F] [CommRing R]
    (g : ι → ι → F) (hg : RectanglesSurvive g) :
    ((quotientMatrix (R := R) g * (quotientMatrix g).transpose) *
      (quotientMatrix g * (quotientMatrix g).transpose)).trace =
      (2 * (Fintype.card ι : R) ^ 3 - (Fintype.card ι : R) ^ 2) * Fintype.card F := by
  classical
  rw [quotientMatrix_gram_sq_trace]
  have ht (u u' v v' : ι) :
      (regularMatrix (R := R) (g u v * (g u' v)⁻¹ * g u' v' * (g u v')⁻¹)).trace =
      (if u = u' then (Fintype.card F : R) else 0) +
      (if v = v' then (Fintype.card F : R) else 0) -
      (if u = u' ∧ v = v' then (Fintype.card F : R) else 0) := by
    by_cases hu : u = u'
    · subst u'
      simp only [mul_inv_cancel, one_mul, regularMatrix_trace,
        true_and, add_sub_cancel_right]
    · by_cases hv : v = v'
      · subst v'
        simp [mul_assoc, hu]
      · simp only [regularMatrix_trace, ite_eq_right (hg u u' v v' hu hv), ite_eq_right hu,
          ite_eq_right hv, ite_eq_right (not_and.mpr (fun h => (hu h).elim)), add_zero, sub_zero]
  simp only [ht, Finset.sum_sub_distrib, Finset.sum_add_distrib, ite_and]
  simp [pow_succ, mul_assoc, sub_mul]
  ring

/-- Each integral row has exactly one unit entry per block column. -/
theorem quotientMatrix_row_sq {ι F : Type*} [Fintype ι] [Group F]
    [Fintype F] [DecidableEq F] (g : ι → ι → F) (i : ι × F) :
    ∑ j, ((quotientMatrix (R := ℤ) g i j : ℤ) : ℝ) ^ 2 = Fintype.card ι := by
  rw [Fintype.sum_prod_type]
  simp [quotientMatrix, flattenMatrix, Matrix.of_apply, ← inv_mul_eq_iff_eq_mul]

/-- Casting the integral matrix gives the corresponding coefficient representation. -/
theorem quotientMatrix_map {ι F R : Type*} [Group F] [Fintype F]
    [DecidableEq F] [Ring R] (g : ι → ι → F) :
    (quotientMatrix (R := ℤ) g).map (Int.cast : ℤ → R) = quotientMatrix (R := R) g := by
  ext i j
  simp [quotientMatrix, flattenMatrix]

theorem quotientMatrix_rank_real_lower {ι F : Type*} [Fintype ι] [Group F]
    [Fintype F] [DecidableEq F] (g : ι → ι → F) (hg : RectanglesSurvive g) :
    Fintype.card ι * Fintype.card F ≤ 2 * (quotientMatrix (R := ℝ) g).rank := by
  by_cases hzero : Fintype.card ι = 0
  · simp [hzero]
  let Y := quotientMatrix (R := ℝ) g
  have hA : (Y * Y.transpose).IsHermitian := by
    exact Matrix.isHermitian_mul_conjTranspose_self Y
  have hArank : (Y * Y.transpose).rank = Y.rank := by
    exact Matrix.rank_self_mul_conjTranspose Y
  have h := trace_sq_le_rank_mul_trace_sq (Y * Y.transpose) hA
  rw [hArank] at h
  change (quotientMatrix (R := ℝ) g * (quotientMatrix g).transpose).trace ^ 2 ≤ _ at h
  rw [quotientMatrix_gram_trace] at h
  change _ ≤ (Y.rank : ℝ) * ((quotientMatrix (R := ℝ) g * (quotientMatrix g).transpose) *
    (quotientMatrix g * (quotientMatrix g).transpose)).trace at h
  rw [quotientMatrix_gram_sq_trace_of_rectangles g hg] at h
  let r : ℝ := Fintype.card ι
  let D : ℝ := Fintype.card F
  have hr : 0 < r := by
    dsimp [r]
    exact_mod_cast Nat.pos_of_ne_zero hzero
  have hD : 0 < D := by
    dsimp [D]
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card F)
  have hk : 0 ≤ (Y.rank : ℝ) := Nat.cast_nonneg _
  have hcancel : (r ^ 3 * D) * (r * D) ≤ (r ^ 3 * D) * (2 * (Y.rank : ℝ)) := by
    calc
      _ = (r ^ 2 * D) ^ 2 := by ring
      _ ≤ (Y.rank : ℝ) * ((2 * r ^ 3 - r ^ 2) * D) := h
      _ ≤ _ := by nlinarith [mul_nonneg (mul_nonneg hk (sq_nonneg r)) hD.le]
  have hf := (mul_le_mul_iff_right₀ (show 0 < r ^ 3 * D by positivity)).mp hcancel
  dsimp [r, D, Y] at hf
  exact_mod_cast hf

theorem quotientMatrix_rank_mod_lower {ι F : Type*} [Fintype ι] [Group F]
    [Fintype F] [DecidableEq F] (g : ι → ι → F) (hg : RectanglesSurvive g)
    (q : ℕ) [Fact q.Prime] (hq : Fintype.card ι < q) :
    Fintype.card ι * Fintype.card F ≤ 4 * (quotientMatrix (R := ZMod q) g).rank := by
  by_cases hzero : Fintype.card ι = 0
  · simp [hzero]
  have hr : (1 : ℝ) ≤ Fintype.card ι := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hzero
  have hqr : (Fintype.card ι : ℝ) < q := by exact_mod_cast hq
  have hred := rank_reduction_half (quotientMatrix (R := ℤ) g) (Fintype.card ι) hr
    (fun i => (quotientMatrix_row_sq g i).le) q hqr
  rw [quotientMatrix_map, quotientMatrix_map] at hred
  have hreal := quotientMatrix_rank_real_lower g hg
  omega

/-- Block direct sum with the line-label index first. -/
def diagonalBlocks {I ι κ K : Type*} [DecidableEq I] [Zero K]
    (Y : I → Matrix ι κ K) : Matrix (I × ι) (I × κ) K :=
    Matrix.of fun x y => if x.1 = y.1 then Y x.1 x.2 y.2 else 0

/-- The lower rank bound for a direct sum, proved by its full-rank block minors. -/
theorem sum_rank_le_rank_diagonalBlocks {I ι κ K : Type*} [Fintype I]
    [Fintype ι] [Fintype κ] [DecidableEq I] [Field K]
    (Y : I → Matrix ι κ K) : (∑ i, (Y i).rank) ≤ (diagonalBlocks Y).rank := by
  classical
  choose f g hf hg hdet using fun i => exists_full_rank_minor (Y i)
  let B : ∀ i, Matrix (Fin (Y i).rank) (Fin (Y i).rank) K :=
    fun i => (Y i).submatrix (f i) (g i)
  let rows : (Σ i, Fin (Y i).rank) → I × ι := fun x => (x.1, f x.1 x.2)
  let cols : (Σ i, Fin (Y i).rank) → I × κ := fun x => (x.1, g x.1 x.2)
  have hminor : (diagonalBlocks Y).submatrix rows cols = Matrix.blockDiagonal' B := by
    ext ⟨i,a⟩ ⟨j,b⟩
    by_cases hij : i = j
    · subst j
      simp [diagonalBlocks, rows, cols, B]
    · simp [diagonalBlocks, rows, cols, Matrix.blockDiagonal'_apply_ne _ _ _ hij, hij]
  have hBunit : IsUnit B := Pi.isUnit_iff.mpr (fun i =>
    (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr (hdet i)))
  have hunit : IsUnit (Matrix.blockDiagonal' B) :=
    hBunit.map (Matrix.blockDiagonal'RingHom (fun i => Fin (Y i).rank) K)
  have hrank := Matrix.rank_of_isUnit (Matrix.blockDiagonal' B) hunit
  calc
    (∑ i, (Y i).rank) = Fintype.card (Σ i, Fin (Y i).rank) := by simp
    _ = (Matrix.blockDiagonal' B).rank := hrank.symm
    _ ≤ (diagonalBlocks Y).rank := by
      rw [← hminor]
      exact Matrix.rank_submatrix_le _ _ _

theorem rank_neg {ι κ K : Type*} [Fintype ι] [Fintype κ] [Field K]
    (A : Matrix ι κ K) : (-A).rank = A.rank := by
  simpa using Matrix.rank_smul_of_mem_nonZeroDivisors A
    (mem_nonZeroDivisors_of_ne_zero (show (-1 : K) ≠ 0 by simp))

/-- The rank-one scalar matrix `f fᵀ` tensored with a matrix. -/
def weightedMatrix {I ι κ K : Type*} [Mul K] (f : I → K) (Z : Matrix ι κ K) :
    Matrix (I × ι) (I × κ) K := Matrix.of fun x y => f x.1 * f y.1 * Z x.2 y.2

/-- A rank-one tensor weight never increases rank. -/
theorem weightedMatrix_rank_le {I ι κ K : Type*} [Fintype I] [Fintype ι]
    [Fintype κ] [Field K] (f : I → K) (Z : Matrix ι κ K) :
    (weightedMatrix f Z).rank ≤ Z.rank := by
  classical
  let L : Matrix (I × ι) ι K := Matrix.of fun x a => if x.2 = a then f x.1 else 0
  let R : Matrix κ (I × κ) K := Matrix.of fun b y => if b = y.2 then f y.1 else 0
  have hfactor : weightedMatrix f Z = L * Z * R := by
    ext ⟨i,a⟩ ⟨j,b⟩
    simp [weightedMatrix, L, R, Matrix.mul_apply, mul_ite, ite_mul]
    ring
  rw [hfactor]
  exact (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)

/-- Exchanging the incidence sums turns the punctured-line certificate into a
block-diagonal matrix identity. The coefficient order in each matrix is unchanged. -/
theorem tensor_certificate {P I ι κ K : Type*} [Fintype P] [Fintype I]
    [DecidableEq I] [Field K] (inc : P → Finset I) (f : P → I → K)
    (Y : I → Matrix ι κ K)
    (hline : ∀ i j k, (∑ z, if i ∈ inc z then f z j * f z k else 0) =
      -(if j = i ∧ k = i then 1 else 0)) :
    (∑ z, weightedMatrix (f z) (∑ i ∈ inc z, Y i)) = -diagonalBlocks Y := by
  classical
  ext ⟨j,a⟩ ⟨k,b⟩
  simp only [Matrix.sum_apply, weightedMatrix, Matrix.of_apply, Matrix.neg_apply,
    diagonalBlocks]
  simp only [Finset.mul_sum]
  have hsum (z : P) : (∑ i ∈ inc z, f z j * f z k * Y i a b) =
      ∑ i, (if i ∈ inc z then f z j * f z k else 0) * Y i a b := by
    simp [ite_mul]
  simp_rw [hsum]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_mul, hline, neg_mul, ite_mul, one_mul, zero_mul]
  by_cases hjk : j = k
  · subst k
    simp
  · simp [hjk, show ∀ i, ¬(j = i ∧ k = i) by rintro i ⟨rfl,rfl⟩; exact hjk rfl]

theorem rank_budget_of_line_certificate {P I ι κ K : Type*} [Fintype P]
    [Fintype I] [Fintype ι] [Fintype κ] [DecidableEq I] [Field K]
    (inc : P → Finset I) (f : P → I → K) (Y : I → Matrix ι κ K)
    (hline : ∀ i j k, (∑ z, if i ∈ inc z then f z j * f z k else 0) =
      -(if j = i ∧ k = i then 1 else 0)) :
    (∑ i, (Y i).rank) ≤ ∑ z, (∑ i ∈ inc z, Y i).rank := by
  calc
    _ ≤ (diagonalBlocks Y).rank := sum_rank_le_rank_diagonalBlocks Y
    _ = (-diagonalBlocks Y).rank := (rank_neg _).symm
    _ = (∑ z, weightedMatrix (f z) (∑ i ∈ inc z, Y i)).rank := by
      rw [tensor_certificate inc f Y hline]
    _ ≤ ∑ z, (weightedMatrix (f z) (∑ i ∈ inc z, Y i)).rank := rank_sum_le _ _
    _ ≤ _ := Finset.sum_le_sum (fun z _ => weightedMatrix_rank_le _ _)

/-- A local Cartesian block factors through one copy of the finite regular module. -/
theorem quotientMatrix_sum_rank_le {ι s t F K : Type*} [Fintype ι]
    [Fintype s] [Fintype t] [Group F] [Fintype F] [DecidableEq F] [Field K]
    (L : ι → s → F) (R : ι → t → F) :
    (∑ j : s, ∑ k : t, quotientMatrix (R := K) (fun u v => (L u j)⁻¹ * R v k)).rank ≤
      Fintype.card F := by
  classical
  let A : Matrix (ι × F) F K := Matrix.of fun x a =>
    (∑ j, regularMatrix (R := K) (L x.1 j)⁻¹) x.2 a
  let B : Matrix F (ι × F) K := Matrix.of fun b y =>
    (∑ k, regularMatrix (R := K) (R y.1 k)) b y.2
  have hfactor :
      (∑ j : s, ∑ k : t, quotientMatrix (R := K) (fun u v => (L u j)⁻¹ * R v k)) =
      A * B := by
    ext ⟨u,a⟩ ⟨v,b⟩
    simp only [Matrix.sum_apply, quotientMatrix, flattenMatrix_apply, Matrix.of_apply,
      map_mul, Matrix.mul_apply, A, B]
    simp only [Finset.sum_mul, Finset.mul_sum]
    simp_rw [Finset.sum_comm (s := (Finset.univ : Finset t))
      (t := (Finset.univ : Finset F))]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    exact Finset.sum_comm
  rw [hfactor]
  exact (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_le_card_width _)

/-- An arbitrary relabeling of a Cartesian block does not affect its summed
regular-representation matrix. Opposite-index shifts are permitted independently. -/
theorem quotientMatrix_sum_reindex {ι B s t F K : Type*} [Fintype B]
    [Fintype s] [Fintype t] [Group F] [Fintype F] [DecidableEq F] [Semiring K]
    (g : B → ι → ι → F) (L : ι → s → F) (R : ι → t → F)
    (e : ι → ι → B ≃ s × t)
    (h : ∀ i u v, g i u v = (L u (e u v i).1)⁻¹ * R v (e u v i).2) :
    (∑ i, quotientMatrix (R := K) (g i)) =
      ∑ j : s, ∑ k : t, quotientMatrix (R := K) (fun u v => (L u j)⁻¹ * R v k) := by
  ext ⟨u,a⟩ ⟨v,b⟩
  simp only [Matrix.sum_apply, quotientMatrix, flattenMatrix_apply, Matrix.of_apply, h]
  exact (Equiv.sum_comp (e u v) (fun p : s × t =>
    (regularMatrix (R := K) ((L u p.1)⁻¹ * R v p.2)) a b)).trans
      (Fintype.sum_prod_type _)

/-- A polynomial below the finite-field power-sum threshold has zero total sum. -/
theorem polynomial_sum_eq_zero {K : Type*} [Field K] [Fintype K]
    (p : Polynomial K) (hdeg : p.natDegree < Fintype.card K - 1) :
    ∑ x, p.eval x = 0 := by
  simp only [Polynomial.eval_eq_sum_range]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro i hi
  rw [← Finset.mul_sum, FiniteField.sum_pow_lt_card_sub_one K i
    (lt_of_le_of_lt (Nat.le_of_lt_succ (Finset.mem_range.mp hi)) hdeg), mul_zero]

def gridLagrange {T K : Type*} [Fintype T] [Field K] [DecidableEq K]
    (S : Finset K) (a x : T → K) : K :=
    ∏ t, ∏ w ∈ S.erase (a t), (x t - w) / (a t - w)

@[simp] theorem gridLagrange_self {T K : Type*} [Fintype T] [Field K]
    [DecidableEq K] (S : Finset K) (a : T → K) : gridLagrange S a a = 1 := by
  apply Finset.prod_eq_one
  intro t _
  apply Finset.prod_eq_one
  intro w hw
  exact div_self (sub_ne_zero.mpr (Finset.mem_erase.mp hw).1.symm)

theorem gridLagrange_other {T K : Type*} [Fintype T] [Field K]
    [DecidableEq K] (S : Finset K) (a x : T → K) (hx : ∀ t, x t ∈ S)
    (hax : a ≠ x) : gridLagrange S a x = 0 := by
  classical
  obtain ⟨t, ht⟩ := Function.ne_iff.mp hax
  apply Finset.prod_eq_zero (Finset.mem_univ t)
  apply Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨ht.symm, hx t⟩)
  simp

/-- Restriction of the grid Lagrange basis along the parametrized affine line. -/
noncomputable def gridLagrangeLine {T K : Type*} [Fintype T] [Field K] [DecidableEq K]
    (S : Finset K) (a b v : T → K) : Polynomial K :=
    ∏ t, ∏ w ∈ S.erase (a t),
      (Polynomial.C (b t - w) + Polynomial.X * Polynomial.C (v t)) *
        Polynomial.C ((a t - w)⁻¹)

@[simp] theorem gridLagrangeLine_eval {T K : Type*} [Fintype T] [Field K]
    [DecidableEq K] (S : Finset K) (a b v : T → K) (x : K) :
    (gridLagrangeLine S a b v).eval x = gridLagrange S a (fun t => b t + x * v t) := by
  simp only [gridLagrangeLine, gridLagrange, Polynomial.eval_prod,
    Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_X,
    div_eq_mul_inv]
  apply Finset.prod_congr rfl
  intro t _
  apply Finset.prod_congr rfl
  intro w _
  ring

theorem gridLagrangeLine_natDegree_le {T K : Type*} [Fintype T] [Field K]
    [DecidableEq K] (S : Finset K) (a b v : T → K) (ha : ∀ t, a t ∈ S) :
    (gridLagrangeLine S a b v).natDegree ≤ Fintype.card T * (S.card - 1) := by
  apply (Polynomial.natDegree_prod_le _ _).trans
  calc
    _ ≤ ∑ t : T, (S.card - 1) := by
      apply Finset.sum_le_sum
      intro t _
      apply (Polynomial.natDegree_prod_le _ _).trans
      calc
        _ ≤ ∑ _w ∈ S.erase (a t), 1 := by
          apply Finset.sum_le_sum
          intro w _
          apply Polynomial.natDegree_mul_le.trans
          simp only [Polynomial.natDegree_C, add_zero]
          apply (Polynomial.natDegree_add_le _ _).trans
          apply max_le
          · simp
          · exact Polynomial.natDegree_mul_le.trans (by simp)
        _ = S.card - 1 := by simp [Finset.card_erase_of_mem (ha t)]
    _ = _ := by simp

/-- Every entry of the rank-one weight matrix has zero sum over a full line. -/
theorem polygon_weight_line_sum {T K : Type*} [Fintype T] [Field K] [Fintype K]
    [DecidableEq K] (S : Finset K) (a a' b v : T → K)
    (ha : ∀ t, a t ∈ S) (ha' : ∀ t, a' t ∈ S)
    (hdeg : 2 * (Fintype.card T * (S.card - 1)) < Fintype.card K - 1) :
    (∑ x : K, gridLagrange S a (fun t => b t + x * v t) *
      gridLagrange S a' (fun t => b t + x * v t)) = 0 := by
  have h := polynomial_sum_eq_zero (gridLagrangeLine S a b v * gridLagrangeLine S a' b v)
    (lt_of_le_of_lt (Polynomial.natDegree_mul_le.trans (Nat.add_le_add
      (gridLagrangeLine_natDegree_le S a b v ha)
      (gridLagrangeLine_natDegree_le S a' b v ha'))) (by omega))
  simpa only [Polynomial.eval_mul, gridLagrangeLine_eval] using h

/-- Finite separating families can be combined into one finite target. -/
theorem exists_finite_separating_family {G : Type u} {ι : Type v} [Group G] [Fintype ι]
    [Group.ResiduallyFinite G] (w : ι → G) (hw : ∀ i, w i ≠ 1) :
    ∃ (Q : Type (max u v)) (_ : Group Q) (_ : Fintype Q) (φ : G →* Q), ∀ i, φ (w i) ≠ 1 := by
  classical
  choose H hH using fun i => Group.exists_finiteIndexNormalSubgroup_notMem (w i) (hw i)
  let Q := ∀ i, G ⧸ (H i).toSubgroup
  let : ∀ i, Fintype (G ⧸ (H i).toSubgroup) := fun i => Fintype.ofFinite _
  let φ : G →* Q := MonoidHom.pi (fun i => QuotientGroup.mk' (H i).toSubgroup)
  refine ⟨Q, inferInstance, inferInstance, φ, ?_⟩
  intro i hi
  have h := congrFun hi i
  exact hH i ((QuotientGroup.eq_one_iff (w i)).mp h)

/-- Standard affine parametrization, with the marked point at parameter zero. -/
def affineLineMap {T K : Type*} [Field K] (a v : T → K) (x : K) : T → K :=
  fun t => a t + x * v t

theorem affineLineMap_injective {T K : Type*} [Field K] (a v : T → K)
    (hv : v ≠ 0) : Function.Injective (affineLineMap a v) := by
  classical
  obtain ⟨t, ht⟩ := Function.ne_iff.mp hv
  intro x y hxy
  have h := congrFun hxy t
  exact mul_right_cancel₀ ht (add_left_cancel h)

/-- The geometric affine line punctured only at its own marked point. -/
noncomputable def puncturedLine {T K : Type*} [Fintype T] [Field K] [Fintype K]
    (a v : T → K) : Finset (T → K) := by
  classical
  exact (Finset.univ.erase 0).image (affineLineMap a v)

/-- Summation on a punctured line subtracts exactly the value at its own mark. -/
theorem puncturedLine_sum {T K R : Type*} [Fintype T] [Field K] [Fintype K]
    [AddCommGroup R] (a v : T → K) (hv : v ≠ 0) (w : (T → K) → R) :
    (∑ z ∈ puncturedLine a v, w z) = (∑ x, w (affineLineMap a v x)) - w a := by
  classical
  have hzero : affineLineMap a v 0 = a := by ext t; simp [affineLineMap]
  rw [puncturedLine, Finset.sum_image (affineLineMap_injective a v hv).injOn,
    Finset.sum_erase_eq_sub (Finset.mem_univ 0), hzero]

noncomputable def lineIncidence {T I K : Type*} [Fintype T] [Fintype I]
    [Field K] [Fintype K] (a v : I → T → K) (z : T → K) : Finset I := by
  classical
  exact Finset.univ.filter (fun i => z ∈ puncturedLine (a i) (v i))

/-- The exact finite-field punctured-line matrix certificate, with no asymptotic
or characteristic assumption beyond its explicit degree threshold. -/
theorem grid_line_certificate {T I K : Type*} [Fintype T] [Fintype I]
    [DecidableEq T] [DecidableEq I] [Field K] [Fintype K] [DecidableEq K]
    (S : Finset K) (a v : I → T → K) (ha : ∀ i t, a i t ∈ S)
    (hinj : Function.Injective a) (hv : ∀ i, v i ≠ 0)
    (hdeg : 2 * (Fintype.card T * (S.card - 1)) < Fintype.card K - 1) :
    ∀ i j k, (∑ z, if i ∈ lineIncidence a v z then
      gridLagrange S (a j) z * gridLagrange S (a k) z else 0) =
      -(if j = i ∧ k = i then 1 else 0) := by
  classical
  intro i j k
  have heval (j : I) : gridLagrange S (a j) (a i) = if j = i then 1 else 0 := by
    by_cases hji : j = i
    · subst j; simp
    · rw [ite_eq_right hji]
      exact gridLagrange_other S (a j) (a i) (ha i) (fun h => hji (hinj h))
  have hs : (∑ z, if i ∈ lineIncidence a v z then
      gridLagrange S (a j) z * gridLagrange S (a k) z else 0) =
      ∑ z ∈ puncturedLine (a i) (v i), gridLagrange S (a j) z * gridLagrange S (a k) z := by
    simp [lineIncidence]
  rw [hs, puncturedLine_sum (a i) (v i) (hv i)]
  rw [show (∑ x, gridLagrange S (a j) (affineLineMap (a i) (v i) x) *
    gridLagrange S (a k) (affineLineMap (a i) (v i) x)) = 0 from
      polygon_weight_line_sum S (a j) (a k) (a i) (v i) (ha j) (ha k) hdeg]
  by_cases hj : j = i <;> by_cases hk : k = i <;> simp_all

theorem two_block_sizes (r d : ℕ) (hr : 0 < r) (hd : 4 * r ^ 2 ≤ d) :
    ∃ n₁ n₂ : ℕ, r ≤ n₁ ∧ r ≤ n₂ ∧ n₂ < 2 * r ∧
      d = r * n₁ + (r + 1) * n₂ := by
  have hmod : d % r < r := Nat.mod_lt d hr
  have hquot : 4 * r ≤ d / r := (Nat.le_div_iff_mul_le hr).mpr (by nlinarith)
  have hsub : r + 1 + d % r ≤ d / r := by omega
  refine ⟨d / r - (r + 1 + d % r), r + d % r, by omega, by omega, by omega, ?_⟩
  have hdecomp := Nat.div_add_mod d r
  have hdiff := Nat.sub_add_cancel hsub
  nlinarith

structure CartesianBlock (I : Type*) (r : ℕ) where
  s : ℕ
  t : ℕ
  hs : r ≤ s
  ht : r ≤ t
  spos : 0 < s
  tpos : 0 < t
  labels : Finset I
  coordinates : labels ≃ ZMod s × ZMod t

instance {I : Type*} {r : ℕ} (b : CartesianBlock I r) : NeZero b.s := ⟨b.spos.ne'⟩
instance {I : Type*} {r : ℕ} (b : CartesianBlock I r) : NeZero b.t := ⟨b.tpos.ne'⟩

/-- Opposite-index shifts are bijections of the block coordinates. -/
def CartesianBlock.shifted {I : Type*} {r : ℕ} (b : CartesianBlock I r)
    (u v : Fin r) : b.labels ≃ ZMod b.s × ZMod b.t :=
  b.coordinates.trans (Equiv.prodCongr (Equiv.addRight (v.val : ZMod b.s))
    (Equiv.addRight (u.val : ZMod b.t)))

theorem CartesianBlock.quotient_rank_le {I F K : Type*} {r : ℕ}
    [Group F] [Fintype F] [DecidableEq F] [Field K]
    (b : CartesianBlock I r) (g : I → Fin r → Fin r → F)
    (L : Fin r → ZMod b.s → F) (R : Fin r → ZMod b.t → F)
    (hrel : ∀ (i : b.labels) u v,
      g i u v = (L u ((b.coordinates i).1 + (v.val : ZMod b.s)))⁻¹ *
        R v ((b.coordinates i).2 + (u.val : ZMod b.t))) :
    (∑ i ∈ b.labels, quotientMatrix (R := K) (g i)).rank ≤ Fintype.card F := by
  classical
  rw [Finset.sum_subtype b.labels (fun _ => Iff.rfl)]
  rw [quotientMatrix_sum_reindex (fun i : b.labels => g i) L R b.shifted hrel]
  exact quotientMatrix_sum_rank_le L R

/-- Every sufficiently large finite set has the two Cartesian blocks required by
the construction; the coordinate bijections are chosen without deleting labels. -/
theorem exists_two_cartesian_blocks {I : Type*} [DecidableEq I] (r : ℕ) (hr : 0 < r)
    (A : Finset I) (hA : 4 * r ^ 2 ≤ A.card) :
    ∃ b₀ b₁ : CartesianBlock I r,
      Disjoint b₀.labels b₁.labels ∧ b₀.labels ∪ b₁.labels = A := by
  classical
  obtain ⟨n₁,n₂,hn₁,hn₂,_,heq⟩ := two_block_sizes r A.card hr hA
  obtain ⟨A₀,hA₀,hcard⟩ := Finset.exists_subset_card_eq (show r * n₁ ≤ A.card by omega)
  let A₁ := A \ A₀
  have hcard₁ : A₁.card = (r + 1) * n₂ := by rw [Finset.card_sdiff_of_subset hA₀, hcard, heq]; omega
  let : NeZero r := ⟨hr.ne'⟩
  let : NeZero n₁ := ⟨(hr.trans_le hn₁).ne'⟩
  let : NeZero n₂ := ⟨(hr.trans_le hn₂).ne'⟩
  let b₀ : CartesianBlock I r :=
    {s := r, t := n₁, hs := le_rfl, ht := hn₁, spos := hr, tpos := hr.trans_le hn₁,
     labels := A₀, coordinates := Fintype.equivOfCardEq (by simpa using hcard)}
  let b₁ : CartesianBlock I r :=
    {s := r+1, t := n₂, hs := Nat.le_succ r, ht := hn₂, spos := Nat.succ_pos r,
     tpos := hr.trans_le hn₂,
     labels := A₁, coordinates := Fintype.equivOfCardEq (by simpa using hcard₁)}
  refine ⟨b₀,b₁,?_,?_⟩
  · exact Finset.disjoint_sdiff
  · exact Finset.union_sdiff_of_subset hA₀

/-- The numerical rank contradiction. The exceptional incidences are retained;
the ambient dimension, not a deletion, bounds their matrices. -/
theorem finite_quotient_rank_obstruction {P I F : Type*} [Fintype P] [Fintype I]
    [DecidableEq I] [Group F] [Fintype F] [DecidableEq F]
    (r q : ℕ) [Fact q.Prime] (hq : r < q)
    (inc : P → Finset I) (f : P → I → ZMod q) (E : Finset P)
    (g : I → Fin r → Fin r → F) (hg : ∀ i, RectanglesSurvive (g i))
    (hline : ∀ i j k, (∑ z, if i ∈ inc z then f z j * f z k else 0) =
      -(if j = i ∧ k = i then 1 else 0))
    (hlocal : ∀ z, z ∉ E → (∑ i ∈ inc z, quotientMatrix (R := ZMod q) (g i)).rank ≤
      2 * Fintype.card F)
    (hbudget : 4 * (2 * Fintype.card P + r * E.card) < Fintype.card I * r) : False := by
  classical
  let D := Fintype.card F
  let Y := fun i => quotientMatrix (R := ZMod q) (g i)
  let Z := fun z => ∑ i ∈ inc z, Y i
  have lower : Fintype.card I * r * D ≤ 4 * ∑ i, (Y i).rank := by
    have h := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset I)) =>
      quotientMatrix_rank_mod_lower (g i) (hg i) q (by simpa using hq))
    simpa [Y, D, ← Finset.mul_sum, mul_assoc] using h
  have middle : (∑ i, (Y i).rank) ≤ ∑ z, (Z z).rank :=
    rank_budget_of_line_certificate inc f Y hline
  have upper : (∑ z, (Z z).rank) ≤ (2 * Fintype.card P + r * E.card) * D := by
    have hbound (z : P) : (Z z).rank ≤ 2 * D + if z ∈ E then r * D else 0 := by
      by_cases hz : z ∈ E
      · rw [ite_eq_left hz]
        have hrank : (Z z).rank ≤ r * D := by
          simpa [D] using Matrix.rank_le_card_height (Z z)
        omega
      · rw [ite_eq_right hz, add_zero]
        exact hlocal z hz
    calc
      _ ≤ ∑ z, (2 * D + if z ∈ E then r * D else 0) := Finset.sum_le_sum (fun z _ => hbound z)
      _ = _ := by simp [Finset.sum_add_distrib, add_mul]; ring
  have hc : Fintype.card I * r * D ≤ (4 * (2 * Fintype.card P + r * E.card)) * D := by
    calc
      _ ≤ 4 * ∑ i, (Y i).rank := lower
      _ ≤ 4 * ∑ z, (Z z).rank := Nat.mul_le_mul_left _ middle
      _ ≤ 4 * ((2 * Fintype.card P + r * E.card) * D) := Nat.mul_le_mul_left _ upper
      _ = _ := by ring
  exact (Nat.not_le_of_gt (Nat.mul_lt_mul_of_pos_right hbudget
    (Fintype.card_pos : 0 < D))) hc

/-- The exact defining relation of a single block, retaining the order `L⁻¹R`. -/
def CartesianBlock.Relations {I G : Type*} [Group G] {r : ℕ}
    (b : CartesianBlock I r) (g : I → Fin r → Fin r → G) : Prop :=
    ∃ (L : Fin r → ZMod b.s → G) (R : Fin r → ZMod b.t → G),
      ∀ (i : b.labels) u v, g i u v =
        (L u ((b.coordinates i).1 + (v.val : ZMod b.s)))⁻¹ *
         R v ((b.coordinates i).2 + (u.val : ZMod b.t))

theorem CartesianBlock.Relations.map {I G F : Type*} [Group G] [Group F] {r : ℕ}
    {b : CartesianBlock I r} {g : I → Fin r → Fin r → G}
    (h : b.Relations g) (φ : G →* F) : b.Relations (fun i u v => φ (g i u v)) := by
  obtain ⟨L,R,hrel⟩ := h
  refine ⟨fun u j => φ (L u j), fun v k => φ (R v k), ?_⟩
  intros
  simp [hrel]

theorem two_block_quotient_rank_le {I F K : Type*} [DecidableEq I]
    [Group F] [Fintype F] [DecidableEq F] [Field K] {r : ℕ}
    (A : Finset I) (g : I → Fin r → Fin r → F)
    (b₀ b₁ : CartesianBlock I r)
    (hdis : Disjoint b₀.labels b₁.labels) (hunion : b₀.labels ∪ b₁.labels = A)
    (h₀ : b₀.Relations g) (h₁ : b₁.Relations g) :
    (∑ i ∈ A, quotientMatrix (R := K) (g i)).rank ≤ 2 * Fintype.card F := by
  obtain ⟨L₀,R₀,h₀⟩ := h₀
  obtain ⟨L₁,R₁,h₁⟩ := h₁
  rw [← hunion, Finset.sum_union hdis]
  have h := (rank_add_le _ _).trans (Nat.add_le_add
    (b₀.quotient_rank_le (K := K) g L₀ R₀ h₀)
    (b₁.quotient_rank_le (K := K) g L₁ R₁ h₁))
  simpa [two_mul] using h

/-- All specified nontrivial rectangular words can be preserved in one finite
image if the group is residually finite. -/
theorem exists_finite_preserving_rectangles {I : Type u} {G : Type v} [Fintype I] [Group G]
    [Group.ResiduallyFinite G] {r : ℕ} (g : I → Fin r → Fin r → G)
    (hg : ∀ i, RectanglesSurvive (g i)) :
    ∃ (Q : Type (max u v)) (_ : Group Q) (_ : Fintype Q) (φ : G →* Q),
      ∀ i, RectanglesSurvive (fun u v => φ (g i u v)) := by
  classical
  let J := {x : I × Fin r × Fin r × Fin r × Fin r // x.2.1 ≠ x.2.2.1 ∧ x.2.2.2.1 ≠ x.2.2.2.2}
  let w : J → G := fun x => g x.val.1 x.val.2.1 x.val.2.2.2.1 *
    (g x.val.1 x.val.2.2.1 x.val.2.2.2.1)⁻¹ *
    g x.val.1 x.val.2.2.1 x.val.2.2.2.2 * (g x.val.1 x.val.2.1 x.val.2.2.2.2)⁻¹
  have hw (x : J) : w x ≠ 1 := hg _ _ _ _ _ x.property.1 x.property.2
  obtain ⟨Q,hQ,hfin,φ,hφ⟩ := exists_finite_separating_family w hw
  refine ⟨Q,hQ,hfin,φ,?_⟩
  intro i u u' v v' hu hv
  have h := hφ ⟨(i,u,u',v,v'),hu,hv⟩
  simpa [w] using h

theorem not_residuallyFinite_of_line_blocks {T I G : Type*}
    [Fintype T] [Fintype I] [DecidableEq T] [DecidableEq I] [Group G]
    (r q : ℕ) [Fact q.Prime] (hq : r < q)
    (S : Finset (ZMod q)) (a v : I → T → ZMod q)
    (ha : ∀ i t, a i t ∈ S) (hinj : Function.Injective a) (hv : ∀ i, v i ≠ 0)
    (hdeg : 2 * (Fintype.card T * (S.card - 1)) < q - 1)
    (E : Finset (T → ZMod q)) (g : I → Fin r → Fin r → G)
    (hg : ∀ i, RectanglesSurvive (g i))
    (hblocks : ∀ z, z ∉ E → ∃ b₀ b₁ : CartesianBlock I r,
      Disjoint b₀.labels b₁.labels ∧ b₀.labels ∪ b₁.labels = lineIncidence a v z ∧
      b₀.Relations g ∧ b₁.Relations g)
    (hbudget : 4 * (2 * Fintype.card (T → ZMod q) + r * E.card) < Fintype.card I * r) :
    ¬ Group.ResiduallyFinite G := by
  classical
  intro hRF
  let := hRF
  obtain ⟨Q,hQ,hfin,φ,hφ⟩ := exists_finite_preserving_rectangles g hg
  let := hQ
  let := hfin
  apply finite_quotient_rank_obstruction r q hq (lineIncidence a v)
    (fun z i => gridLagrange S (a i) z) E (fun i u v => φ (g i u v)) hφ
    (grid_line_certificate S a v ha hinj hv (by simpa using hdeg)) _ hbudget
  intro z hz
  obtain ⟨b₀,b₁,hd,hu,h₀,h₁⟩ := hblocks z hz
  exact two_block_quotient_rank_le _ _ b₀ b₁ hd hu (h₀.map φ) (h₁.map φ)

end Release075

end OAI
end
end

section
section
namespace OAI

namespace Release075
open scoped BigOperators

noncomputable section
attribute [local instance] Classical.propDecidable

/-- Independence of coordinates under the uniform average on a finite product. -/
theorem expect_pi_product {I D : Type*} [Fintype I] [DecidableEq I] [Fintype D]
    (f : I → D → ℝ) :
    (𝔼 ω : I → D, ∏ i, f i (ω i)) = ∏ i, 𝔼 d, f i d := by
  classical
  simp only [Fintype.expect_eq_sum_div_card]
  rw [← Fintype.prod_sum]
  simp only [Fintype.card_pi, Nat.cast_prod, Finset.prod_div_distrib]

/-- A coordinate of a uniform product has the uniform marginal. -/
theorem expect_coordinate {I D : Type*} [Fintype I] [DecidableEq I] [Fintype D] [Nonempty D]
    (i : I) (f : D → ℝ) : (𝔼 ω : I → D, f (ω i)) = 𝔼 d, f d := by
  classical
  have h := expect_pi_product (fun j d => if j = i then f d else 1)
  have hm (j : I) : (𝔼 d, if j = i then f d else (1 : ℝ)) =
      if j = i then (𝔼 d, f d) else 1 := by
    by_cases hj : j = i <;> simp [hj]
  simpa only [hm, Finset.prod_ite_eq', Finset.mem_univ, ite_true] using h

/-- Distinct coordinate functions have a factorized second moment. -/
theorem expect_two_coordinates {I D : Type*} [Fintype I] [DecidableEq I] [Fintype D] [Nonempty D]
    (i j : I) (hij : i ≠ j) (f g : D → ℝ) :
    (𝔼 ω : I → D, f (ω i) * g (ω j)) = (𝔼 d, f d) * (𝔼 d, g d) := by
  classical
  let F : I → D → ℝ := fun k d =>
    (if k = i then f d else 1) * (if k = j then g d else 1)
  have hprod (ω : I → D) : (∏ k, F k (ω k)) = f (ω i) * g (ω j) := by
    simp only [F, Finset.prod_mul_distrib]
    simp
  have hmean (k : I) : (𝔼 d, F k d) =
      (if k = i then (𝔼 d, f d) else 1) * (if k = j then (𝔼 d, g d) else 1) := by
    by_cases hi : k = i
    · subst k; simp [F, hij]
    · by_cases hj : k = j
      · subst k; simp [F, hi]
      · simp [F, hi, hj]
  have h := expect_pi_product F
  simpa only [hprod, hmean, Finset.prod_mul_distrib,
    Finset.prod_ite_eq', Finset.mem_univ, ite_true] using h

theorem expect_low_indicator_le {Ω : Type*} [Fintype Ω]
    (X : Ω → ℝ) (μ t : ℝ) (ht : t < μ) :
    (𝔼 ω, if X ω < t then (1 : ℝ) else 0) ≤
      (𝔼 ω, (X ω - μ)^2) / (μ-t)^2 := by
  classical
  have hd : 0 < (μ-t)^2 := sq_pos_of_pos (sub_pos.mpr ht)
  rw [le_div_iff₀ hd, Finset.expect_mul]
  apply Finset.expect_le_expect
  intro ω _
  split_ifs with h
  · have hh : (μ-t)^2 ≤ (μ-X ω)^2 :=
      (sq_le_sq₀ (by linarith : 0 ≤ μ-t) (by linarith : 0 ≤ μ-X ω)).mpr (by linarith)
    nlinarith
  · simpa only [zero_mul] using sq_nonneg (X ω - μ)

/-- Existence from a strict finite average bound, without measure-theoretic null sets. -/
theorem exists_of_expect_lt {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (X : Ω → ℝ) (a : ℝ) (h : (𝔼 ω, X ω) < a) : ∃ ω, X ω < a := by
  obtain ⟨ω,_,hω⟩ := Finset.exists_lt_of_expect_lt Finset.univ_nonempty h
  exact ⟨ω,hω⟩

/-- Variance of a sum of independent coordinates, proved by a finite double sum. -/
theorem expect_centered_sum_sq {I D : Type*} [Fintype I] [DecidableEq I]
    [Fintype D] [Nonempty D] (b : I → D → ℝ) (p : I → ℝ)
    (hp : ∀ i, (𝔼 d, b i d) = p i) :
    (𝔼 ω : I → D, ((∑ i, b i (ω i)) - ∑ i, p i)^2) =
      ∑ i, (𝔼 d, (b i d - p i)^2) := by
  classical
  let X : I → D → ℝ := fun i d => b i d - p i
  have hzero (i : I) : (𝔼 d, X i d) = 0 := by
    simp [X, Finset.expect_sub_distrib, hp]
  have hcross (i j : I) :
      (𝔼 ω : I → D, X i (ω i) * X j (ω j)) =
      if i = j then (𝔼 d, (X i d)^2) else 0 := by
    by_cases hij : i = j
    · subst j
      simp only [← sq]
      exact expect_coordinate i (fun d => (X i d)^2)
    · rw [ite_eq_right hij, expect_two_coordinates i j hij, hzero, zero_mul]
  calc
    _ = 𝔼 ω : I → D, ∑ i, ∑ j, X i (ω i) * X j (ω j) := by
      apply Finset.expect_congr rfl
      intro ω _
      rw [← Finset.sum_sub_distrib, sq, Finset.sum_mul_sum]
    _ = ∑ i, ∑ j, 𝔼 ω : I → D, X i (ω i) * X j (ω j) := by
      rw [Finset.expect_sum_comm]
      congr 1; ext i
      rw [Finset.expect_sum_comm]
    _ = _ := by simp [hcross, X]

theorem expect_bernoulli_sum_sq_le {I D : Type*} [Fintype I] [DecidableEq I]
    [Fintype D] [Nonempty D] (b : I → D → ℝ) (p : I → ℝ)
    (hb : ∀ i d, b i d = 0 ∨ b i d = 1)
    (hp : ∀ i, (𝔼 d, b i d) = p i) :
    (𝔼 ω : I → D, ((∑ i, b i (ω i)) - ∑ i, p i)^2) ≤ ∑ i, p i := by
  classical
  rw [expect_centered_sum_sq b p hp]
  apply Finset.sum_le_sum
  intro i _
  have heq : (𝔼 d, (b i d - p i)^2) = p i - (p i)^2 := by
    calc
      _ = 𝔼 d, (b i d - 2 * p i * b i d + (p i)^2) := by
        apply Finset.expect_congr rfl
        intro d _
        rcases hb i d with h | h <;> rw [h] <;> ring
      _ = _ := by
        rw [Finset.expect_add_distrib, Finset.expect_sub_distrib,
          ← Finset.mul_expect, hp]
        simp only [Fintype.expect_const]
        ring
  rw [heq]
  linarith [sq_nonneg (p i)]

/-- Joint moments of any injectively selected coordinates. -/
theorem expect_selected_product {A I D : Type*} [Fintype A] [Fintype I]
    [DecidableEq I] [Fintype D] [Nonempty D]
    (e : A ↪ I) (f : A → D → ℝ) :
    (𝔼 ω : I → D, ∏ a, f a (ω (e a))) = ∏ a, 𝔼 d, f a d := by
  classical
  let F : I → D → ℝ := fun i d => Function.extend e (fun a => f a d) (fun _ => 1) i
  have hin (a : A) (d : D) : F (e a) d = f a d := e.injective.extend_apply _ _ _
  have hout (i : I) (hi : i ∉ Set.range e) (d : D) : F i d = 1 :=
    Function.extend_apply' _ _ _ hi
  have hprod (ω : I → D) : (∏ a, f a (ω (e a))) = ∏ i, F i (ω i) :=
    Fintype.prod_of_injective e e.injective _ _ (fun i hi => hout i hi _) (fun a => (hin _ _).symm)
  have hmean : (∏ a, 𝔼 d, f a d) = ∏ i, 𝔼 d, F i d := by
    apply Fintype.prod_of_injective e e.injective
    · intro i hi; simp only [hout i hi, Fintype.expect_const]
    · intro a; simp only [hin]
  simp_rw [hprod, hmean]
  exact expect_pi_product F

section ProjectiveLines
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- A line through a mark, chosen by its projective direction. -/
def OnChosenLine (a z : V) (d : Projectivization K V) : Prop :=
  ∃ t : K, a + t • d.rep = z

/-- Only the chosen line's own mark is punctured. -/
def PuncturedIncidence (a z : V) (d : Projectivization K V) : Prop :=
  z ≠ a ∧ OnChosenLine a z d

/-- At a point different from the mark, exactly one direction gives incidence. -/
theorem puncturedIncidence_iff (a z : V) (hza : z ≠ a) (d : Projectivization K V) :
    PuncturedIncidence a z d ↔ d = Projectivization.mk K (z-a) (sub_ne_zero.mpr hza) := by
  have hd := d.mk_rep
  rw [PuncturedIncidence, and_iff_right hza]
  constructor
  · rintro ⟨t,ht⟩
    rw [← hd, Projectivization.mk_eq_mk_iff']
    have ht' : t • d.rep = z-a := by rw [← ht]; abel
    have ht0 : t ≠ 0 := by intro h; simp [h] at ht; exact hza ht.symm
    refine ⟨t⁻¹, ?_⟩
    rw [← ht', smul_smul, inv_mul_cancel₀ ht0, one_smul]
  · intro h
    have hh := (Projectivization.mk_eq_mk_iff' K (z-a) d.rep
      (sub_ne_zero.mpr hza) d.rep_nonzero).mp (h.symm.trans hd.symm)
    obtain ⟨t,ht⟩ := hh
    exact ⟨t, by rw [ht]; abel⟩

/-- Each geometric line contains exactly |K| points. -/
theorem lineMap_injective (a : V) (d : Projectivization K V) :
    Function.Injective (fun t : K => a + t • d.rep) := by
  intro t u h
  exact smul_left_injective K d.rep_nonzero (add_left_cancel h)

/-- The exact Bernoulli parameter of a uniformly chosen direction. -/
theorem expect_puncturedIncidence [Fintype (Projectivization K V)]
    (a z : V) (hza : z ≠ a) :
    (𝔼 d : Projectivization K V, if PuncturedIncidence a z d then (1 : ℝ) else 0) =
      1 / Fintype.card (Projectivization K V) := by
  classical
  simp only [puncturedIncidence_iff a z hza, Fintype.expect_eq_sum_div_card,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]

end ProjectiveLines

section CycleCount
variable {A K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- An attempted mark on the geometric line joining consecutive point vertices. -/
def candidateMark (σ : A → A) (p : A → V) (t : A → K) (a : A) : V :=
  p a + t a • (p (σ a) - p a)

/-- An over-count of short cycles: parameters, rather than marks, are enumerated.
Marks at punctured endpoints are deliberately permitted for the upper bound. -/
def CycleCandidate (S : Finset V) (σ : A → A) :=
  {c : (A → V) × (A → K) // Function.Injective c.1 ∧
    (∀ a, c.1 (σ a) ≠ c.1 a) ∧
    (∀ a, candidateMark σ c.1 c.2 a ∈ S) ∧
    Function.Injective (candidateMark σ c.1 c.2)}

instance [Fintype A] [Fintype K] [Fintype V] (S : Finset V) (σ : A → A) :
    Fintype (CycleCandidate (K := K) S σ) := by unfold CycleCandidate; infer_instance

namespace CycleCandidate
variable {S : Finset V} {σ : A → A}

def marks (c : CycleCandidate (K := K) S σ) : A ↪ S where
  toFun a := ⟨candidateMark σ c.val.1 c.val.2 a,c.property.2.2.1 a⟩
  inj' := fun _ _ h => c.property.2.2.2 (congrArg Subtype.val h)

def direction (c : CycleCandidate (K := K) S σ) (a : A) : Projectivization K V :=
  Projectivization.mk K (c.val.1 (σ a) - c.val.1 a) (sub_ne_zero.mpr (c.property.2.1 a))

def Occurs (c : CycleCandidate (K := K) S σ) (ω : S → Projectivization K V) : Prop :=
  ∀ a, ω (c.marks a) = c.direction a

/-- The displayed upper count still has independent prescribed directions because
its candidate marks are distinct. -/
theorem expect_occurs [Fintype A] [Fintype (Projectivization K V)] [Nontrivial V]
    (c : CycleCandidate (K := K) S σ) :
    (𝔼 ω : S → Projectivization K V, if c.Occurs ω then (1 : ℝ) else 0) =
      (1 / Fintype.card (Projectivization K V) : ℝ) ^ Fintype.card A := by
  calc
    _ = 𝔼 ω : S → Projectivization K V,
        ∏ a, if ω (c.marks a) = c.direction a then (1 : ℝ) else 0 := by
      apply Finset.expect_congr rfl
      intro ω _
      rw [Fintype.prod_boole]
      by_cases h : ∀ a : A, ω (c.marks a) = c.direction a
      · rw [ite_eq_left h]
        exact ite_eq_left h
      · rw [ite_eq_right h]
        exact ite_eq_right h
    _ = ∏ a, (𝔼 d : Projectivization K V, if d = c.direction a then (1 : ℝ) else 0) :=
      by
      exact expect_selected_product (D := Projectivization K V) c.marks
        (fun a d => if d = c.direction a then (1 : ℝ) else 0)
    _ = _ := by
      simp only [Fintype.expect_eq_sum_div_card, Finset.sum_ite_eq', Finset.mem_univ,
        ite_true, Finset.prod_const, Finset.card_univ]
end CycleCandidate

/-- All occurring encoded cycles for a given random outcome. -/
def badCycles [Fintype A] [Fintype K] [Fintype V]
    (S : Finset V) (σ : A → A) (ω : S → Projectivization K V) : Finset (CycleCandidate (K := K) S σ) :=
  Finset.univ.filter (fun c => c.Occurs ω)

/-- Expected cycle bound before specializing the finite field cardinalities. -/
theorem expect_badCycles_le [Fintype A] [Fintype K] [Fintype V]
    [Fintype (Projectivization K V)] [Nontrivial V]
    (S : Finset V) (σ : A → A) :
    (𝔼 ω : S → Projectivization K V, ((badCycles S σ ω).card : ℝ)) ≤
      (Fintype.card V : ℝ)^Fintype.card A * (Fintype.card K : ℝ)^Fintype.card A *
        (1 / Fintype.card (Projectivization K V) : ℝ)^Fintype.card A := by
  have hcard : Fintype.card (CycleCandidate (K := K) S σ) ≤
      Fintype.card V ^ Fintype.card A * Fintype.card K ^ Fintype.card A := by
    simpa [CycleCandidate] using Fintype.card_subtype_le
      (fun c : (A → V) × (A → K) => Function.Injective c.1 ∧
        (∀ a, c.1 (σ a) ≠ c.1 a) ∧ (∀ a, candidateMark σ c.1 c.2 a ∈ S) ∧
        Function.Injective (candidateMark σ c.1 c.2))
  calc
    _ = ∑ c : CycleCandidate (K := K) S σ, 𝔼 ω : S → Projectivization K V,
        if c.Occurs ω then (1 : ℝ) else 0 := by
      simp only [badCycles, ← Finset.sum_boole]
      exact Finset.expect_sum_comm _ _ _
    _ = (Fintype.card (CycleCandidate (K := K) S σ) : ℝ) *
        (1 / Fintype.card (Projectivization K V) : ℝ)^Fintype.card A := by
      simp only [CycleCandidate.expect_occurs, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact_mod_cast hcard

end CycleCount

section Degrees
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Fintype (Projectivization K V)] [Nontrivial V]

/-- Incidence degree before alteration, with the marked point removed from its line. -/
def pointDegree (S : Finset V) (ω : S → Projectivization K V) (z : V) : ℕ :=
  (Finset.univ.filter (fun a : S => PuncturedIncidence a.val z (ω a))).card

/-- Exact mean, including the missing self-mark when the point belongs to the grid. -/
def pointMean (S : Finset V) (z : V) : ℝ :=
  ∑ a : S, if z ≠ a.val then 1 / (Fintype.card (Projectivization K V) : ℝ) else 0

omit [Nontrivial V] in
theorem pointMean_formula (S : Finset V) (z : V) :
    pointMean (K := K) S z = (S.erase z).card / (Fintype.card (Projectivization K V) : ℝ) := by
  rw [pointMean, ← Finset.sum_subtype S (fun _ => Iff.rfl)
    (fun a : V => if z ≠ a then 1 / (Fintype.card (Projectivization K V) : ℝ) else 0)]
  rw [← Finset.sum_filter]
  have hf : S.filter (fun a => z ≠ a) = S.erase z := by
    ext a; simp [ne_comm, and_comm]
  rw [hf]
  simp [div_eq_mul_inv]

theorem expect_pointDegree (S : Finset V) (z : V) :
    (𝔼 ω : S → Projectivization K V, (pointDegree S ω z : ℝ)) = pointMean (K := K) S z := by
  have hm (a : S) : (𝔼 d : Projectivization K V,
      if PuncturedIncidence a.val z d then (1 : ℝ) else 0) =
      if z ≠ a.val then 1 / (Fintype.card (Projectivization K V) : ℝ) else 0 := by
    by_cases ha : z = a.val
    · simp [ha, PuncturedIncidence]
    · rw [ite_eq_left ha]; exact expect_puncturedIncidence a.val z ha
  simp only [pointDegree, ← Finset.sum_boole, pointMean]
  rw [Finset.expect_sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  exact (expect_coordinate a (fun d : Projectivization K V =>
    if PuncturedIncidence a.val z d then (1 : ℝ) else 0)).trans (hm a)

theorem variance_pointDegree_le (S : Finset V) (z : V) :
    (𝔼 ω : S → Projectivization K V,
      ((pointDegree S ω z : ℝ) - pointMean (K := K) S z)^2) ≤ pointMean (K := K) S z := by
  let b : S → Projectivization K V → ℝ := fun a d =>
    if PuncturedIncidence a.val z d then 1 else 0
  let p : S → ℝ := fun a => if z ≠ a.val then
    1 / (Fintype.card (Projectivization K V) : ℝ) else 0
  have hp (a : S) : (𝔼 d, b a d) = p a := by
    by_cases ha : z = a.val
    · simp [b,p,ha,PuncturedIncidence]
    · simp only [p, ite_eq_left ha, b]; exact expect_puncturedIncidence a.val z ha
  have h := expect_bernoulli_sum_sq_le b p (by intro a d; simp only [b]; split_ifs <;> simp) hp
  simpa only [b,p,Finset.sum_boole,pointDegree,pointMean] using h

/-- Expected size of the exceptional low-degree set in a completely finite form. -/
theorem expect_lowDegree_le [Fintype V] (S : Finset V) (T : ℕ) (μ : ℝ)
    (hμ : 0 < μ) (hT : 2 * (T : ℝ) ≤ μ)
    (hlower : ∀ z : V, μ ≤ pointMean (K := K) S z) :
    (𝔼 ω : S → Projectivization K V,
      ((Finset.univ.filter (fun z : V => pointDegree S ω z < T)).card : ℝ)) ≤
        4 * (Fintype.card V : ℝ) / μ := by
  have hpoint (z : V) : (𝔼 ω : S → Projectivization K V,
      if pointDegree S ω z < T then (1 : ℝ) else 0) ≤ 4 / μ := by
    have hz := hlower z
    have hm : 0 < pointMean (K := K) S z := hμ.trans_le hz
    have ht : (T : ℝ) < pointMean (K := K) S z := by linarith
    have hcheb := expect_low_indicator_le (fun ω : S → Projectivization K V =>
      (pointDegree S ω z : ℝ)) (pointMean (K := K) S z) (T : ℝ) ht
    have hvar := variance_pointDegree_le (K := K) S z
    have hden : 0 < (pointMean (K := K) S z - (T : ℝ))^2 := sq_pos_of_pos (by linarith)
    have hrat : pointMean (K := K) S z / (pointMean (K := K) S z - (T : ℝ))^2 ≤ 4 / μ := by
      apply (div_le_div_iff₀ hden hμ).mpr
      have hbound : 2 * (T : ℝ) ≤ pointMean (K := K) S z := hT.trans hz
      have hnon : 0 ≤ pointMean (K := K) S z - 2 * (T : ℝ) := by linarith
      have hsq := sq_nonneg (pointMean (K := K) S z - 2 * (T : ℝ))
      have hprod := mul_nonneg hnon (show 0 ≤ (T : ℝ) by positivity)
      have hmμ := mul_le_mul_of_nonneg_left hz hm.le
      nlinarith
    have h := hcheb.trans ((div_le_div_of_nonneg_right hvar hden.le).trans hrat)
    simpa only [Nat.cast_lt] using h
  simp only [← Finset.sum_boole]
  rw [Finset.expect_sum_comm]
  calc
    _ ≤ ∑ z : V, (4 / μ : ℝ) := Finset.sum_le_sum (fun z _ => hpoint z)
    _ = _ := by simp; ring
end Degrees

/-- The simple bipartite graph of a relation (the same definition used by the links). -/
def relationGraph {A B : Type*} (R : A → B → Prop) : SimpleGraph (A ⊕ B) where
  Adj x y := match x,y with
    | .inl a, .inr b => R a b
    | .inr b, .inl a => R a b
    | _,_ => False
  symm := ⟨by intro x y; cases x <;> cases y <;> simp⟩
  loopless := ⟨by intro x; cases x <;> simp⟩

def relationColoring {A B : Type*} (R : A → B → Prop) : (relationGraph R).Coloring Bool :=
  {toFun := Sum.elim (fun _ => false) (fun _ => true)
   map_rel' := by intro x y h; cases x <;> cases y <;> simp_all [relationGraph]}

theorem relationGraph_even_getVert {A B : Type*} (R : A → B → Prop) {a : A} {v : A ⊕ B}
    (w : (relationGraph R).Walk (.inl a) v) (k : ℕ) (hk : 2*k ≤ w.length) :
    ∃ b : A, w.getVert (2*k) = .inl b := by
  have h := (relationColoring R).even_length_iff_congr (w.take (2*k))
  rw [SimpleGraph.Walk.take_length, inf_eq_left.mpr hk] at h
  have he : Even (2*k) := ⟨k,by omega⟩
  have hh := h.mp he
  cases hv : w.getVert (2*k) with
  | inl b => exact ⟨b,rfl⟩
  | inr b => simp [hv,relationColoring] at hh

theorem relationGraph_odd_getVert {A B : Type*} (R : A → B → Prop) {a : A} {v : A ⊕ B}
    (w : (relationGraph R).Walk (.inl a) v) (k : ℕ) (hk : 2*k+1 ≤ w.length) :
    ∃ b : B, w.getVert (2*k+1) = .inr b := by
  obtain ⟨a',ha⟩ := relationGraph_even_getVert R w k (by omega)
  have h := w.adj_getVert_succ (by omega : 2*k < w.length)
  rw [ha] at h
  cases hv : w.getVert (2*k+1) with
  | inl b => rw [hv] at h; exact h.elim
  | inr b => exact ⟨b,rfl⟩

/-- The concrete alternating normal form of any simple bipartite cycle. -/
theorem relationGraph_cycle_encoding {A B : Type*} (R : A → B → Prop)
    {a : A} (w : (relationGraph R).Walk (.inl a) (.inl a)) (hw : w.IsCycle) :
    ∃ (s : ℕ) (_ : 2 ≤ s) (p : Fin s → A) (l : Fin s → B),
      w.length = 2*s ∧ Function.Injective p ∧ Function.Injective l ∧
      ∀ i, R (p i) (l i) ∧ R (p (finRotate s i)) (l i) := by
  have he := ((relationColoring R).even_length_iff_congr w).mpr Iff.rfl
  obtain ⟨s,hs⟩ := he
  have hlen : w.length = 2*s := by omega
  have hs2 : 2 ≤ s := by have := hw.three_le_length; omega
  let p : Fin s → A := fun i => (relationGraph_even_getVert R w i.val (by omega)).choose
  let l : Fin s → B := fun i => (relationGraph_odd_getVert R w i.val (by omega)).choose
  have hp (i : Fin s) : w.getVert (2*i.val) = .inl (p i) :=
    (relationGraph_even_getVert R w i.val (by omega)).choose_spec
  have hl (i : Fin s) : w.getVert (2*i.val+1) = .inr (l i) :=
    (relationGraph_odd_getVert R w i.val (by omega)).choose_spec
  have hpnext (i : Fin s) : w.getVert (2*i.val+2) = .inl (p (finRotate s i)) := by
    have hv : (finRotate s i).val = (i.val+1)%s := by
      have hs1 : 1 < s := by omega
      simp [finRotate_apply, Fin.add_def, Nat.mod_eq_of_lt hs1]
    by_cases hi : i.val+1 < s
    · rw [Nat.mod_eq_of_lt hi] at hv
      simpa only [hv, mul_add, mul_one] using hp (finRotate s i)
    · have hi' : i.val+1=s := by omega
      have hv' : (finRotate s i).val = 0 := by rw [hi',Nat.mod_self] at hv; exact hv
      have hzero := hp (finRotate s i)
      rw [hv',mul_zero,SimpleGraph.Walk.getVert_zero] at hzero
      rw [show 2*i.val+2=w.length by omega,SimpleGraph.Walk.getVert_length]
      exact hzero
  refine ⟨s,hs2,p,l,hlen,?_,?_,?_⟩
  · intro i j hij
    apply Fin.ext
    have heq : w.getVert (2*i.val) = w.getVert (2*j.val) := by rw [hp,hp,hij]
    have hh := hw.getVert_injOn' (by change 2*i.val ≤ w.length-1; omega)
      (by change 2*j.val ≤ w.length-1; omega) heq
    omega
  · intro i j hij
    apply Fin.ext
    have heq : w.getVert (2*i.val+1) = w.getVert (2*j.val+1) := by rw [hl,hl,hij]
    have hh := hw.getVert_injOn' (by change 2*i.val+1 ≤ w.length-1; omega)
      (by change 2*j.val+1 ≤ w.length-1; omega) heq
    omega
  · intro i
    have h₀ := w.adj_getVert_succ (by omega : 2*i.val < w.length)
    have h₁ := w.adj_getVert_succ (by omega : 2*i.val+1 < w.length)
    rw [hp,hl] at h₀
    rw [hl,show 2*i.val+1+1=2*i.val+2 by omega,hpnext] at h₁
    exact ⟨h₀,h₁⟩

/-- The same encoding without a restriction on the chosen starting vertex. -/
theorem relationGraph_any_cycle_encoding {A B : Type*} (R : A → B → Prop)
    {a : A ⊕ B} (w : (relationGraph R).Walk a a) (hw : w.IsCycle) :
    ∃ (s : ℕ) (_ : 2 ≤ s) (p : Fin s → A) (l : Fin s → B),
      w.length = 2*s ∧ Function.Injective p ∧ Function.Injective l ∧
      ∀ i, R (p i) (l i) ∧ R (p (finRotate s i)) (l i) := by
  cases a with
  | inl a => exact relationGraph_cycle_encoding R w hw
  | inr b =>
    have hn : 0 < w.length := by have := hw.three_le_length; omega
    have ha := w.adj_getVert_succ hn
    rw [SimpleGraph.Walk.getVert_zero] at ha
    cases hv : w.getVert 1 with
    | inr c => rw [hv] at ha; exact ha.elim
    | inl a =>
      have hm : Sum.inl a ∈ w.support := hv ▸ w.getVert_mem_support 1
      obtain ⟨s,hs,p,l,hlen,hp,hl,h⟩ := relationGraph_cycle_encoding R (w.rotate (.inl a) hm) (hw.rotate hm)
      exact ⟨s,hs,p,l,by simpa using hlen,hp,hl,h⟩

section EncodingIncidence
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- Two distinct points determine their direction and every mark on their line. -/
theorem line_two_points (a z z' : V) (d : Projectivization K V) (hzz : z' ≠ z)
    (hz : OnChosenLine a z d) (hz' : OnChosenLine a z' d) :
    ∃ t : K, a = z + t • (z'-z) ∧
      d = Projectivization.mk K (z'-z) (sub_ne_zero.mpr hzz) := by
  obtain ⟨u,hu⟩ := hz
  obtain ⟨v,hv⟩ := hz'
  have hdiff : z'-z = (v-u) • d.rep := by rw [← hu,← hv,sub_smul]; abel
  have hvu : v-u ≠ 0 := by
    intro h; rw [h,zero_smul] at hdiff; exact hzz (sub_eq_zero.mp hdiff)
  refine ⟨-u / (v-u),?_,?_⟩
  · rw [hdiff,smul_smul,div_mul_cancel₀ _ hvu,neg_smul,← hu]
    abel
  · rw [← d.mk_rep,Projectivization.mk_eq_mk_iff']
    refine ⟨(v-u)⁻¹,?_⟩
    rw [hdiff,smul_smul,inv_mul_cancel₀ hvu,one_smul]

end EncodingIncidence

/-- Rotation has no fixed point on a cycle with at least two entries. -/
theorem finRotate_ne_self {s : ℕ} (hs : 2 ≤ s) (i : Fin s) : finRotate s i ≠ i := by
  intro hi
  have hs1 : 1 < s := by omega
  have he := congrArg Fin.val hi
  have hv : (finRotate s i).val = (i.val+1)%s := by
    simp [finRotate_apply, Fin.add_def, Nat.mod_eq_of_lt hs1]
  rw [hv] at he
  by_cases h : i.val+1 < s
  · rw [Nat.mod_eq_of_lt h] at he; omega
  · have hi' : i.val+1=s := by omega
    rw [hi',Nat.mod_self] at he; omega

section Alteration
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- Any actual simple incidence cycle yields one of the counted attempts. -/
theorem cycleCandidate_of_incidence {S : Finset V} (ω : S → Projectivization K V)
    {s : ℕ} (hs : 2 ≤ s) (p : Fin s → V) (l : Fin s → S)
    (hp : Function.Injective p) (hl : Function.Injective l)
    (h : ∀ i, PuncturedIncidence (l i).val (p i) (ω (l i)) ∧
      PuncturedIncidence (l i).val (p (finRotate s i)) (ω (l i))) :
    ∃ c : CycleCandidate (K := K) S (finRotate s), c.Occurs ω ∧ ∀ i, c.marks i = l i := by
  have hneq (i : Fin s) : p (finRotate s i) ≠ p i := hp.ne (finRotate_ne_self hs i)
  have hex (i : Fin s) := line_two_points (l i).val (p i) (p (finRotate s i)) (ω (l i))
    (hneq i) (h i).1.2 (h i).2.2
  let t : Fin s → K := fun i => (hex i).choose
  have ht (i : Fin s) : candidateMark (finRotate s) p t i = (l i).val := (hex i).choose_spec.1.symm
  let c : CycleCandidate (K := K) S (finRotate s) :=
    ⟨(p,t),hp,hneq,(fun i => ht i ▸ (l i).property),by
      intro i j hij
      apply hl
      apply Subtype.ext
      simpa only [ht] using hij⟩
  have hc (i : Fin s) : c.marks i = l i := Subtype.ext (ht i)
  refine ⟨c,?_,hc⟩
  intro i
  rw [hc]
  exact (hex i).choose_spec.2

variable [Fintype K] [Fintype V]

/-- All marks lying on an occurring short-cycle attempt are discarded. -/
def deletedMarks (S : Finset V) (ω : S → Projectivization K V) : Finset S :=
  (Finset.Icc 2 6).biUnion fun s =>
    (badCycles S (finRotate s) ω).biUnion fun c => Finset.univ.image c.marks

theorem deletedMarks_card_le (S : Finset V) (ω : S → Projectivization K V) :
    (deletedMarks S ω).card ≤ 6 * ∑ s ∈ Finset.Icc 2 6, (badCycles S (finRotate s) ω).card := by
  apply Finset.card_biUnion_le.trans
  calc
    _ ≤ ∑ s ∈ Finset.Icc 2 6, 6 * (badCycles S (finRotate s) ω).card := by
      apply Finset.sum_le_sum
      intro s hs
      apply Finset.card_biUnion_le.trans
      calc
        _ ≤ ∑ _c ∈ badCycles S (finRotate s) ω, 6 := by
          apply Finset.sum_le_sum
          intro c _
          have hcard : (Finset.univ.image c.marks).card ≤ s := by
            exact Finset.card_image_le.trans (by simp)
          exact hcard.trans (Finset.mem_Icc.mp hs).2
        _ = _ := by simp [mul_comm]
    _ = _ := by rw [Finset.mul_sum]

def Retained (S : Finset V) (ω : S → Projectivization K V) := {a : S // a ∉ deletedMarks S ω}

/-- Deletion creates no cycle; exact girth >12 is obtained, including repeated
geometric lines with distinct labels. -/
theorem retained_girth (S : Finset V) (ω : S → Projectivization K V)
    (a : V ⊕ Retained S ω)
    (w : (relationGraph (fun z (i : Retained S ω) =>
      PuncturedIncidence i.val.val z (ω i.val))).Walk a a) (hw : w.IsCycle) : 12 < w.length := by
  by_contra hlen
  obtain ⟨s,hs,p,l,heq,hp,hl,h⟩ := relationGraph_any_cycle_encoding _ w hw
  have hs6 : s ≤ 6 := by omega
  let l' : Fin s → S := fun i => (l i).val
  have hl' : Function.Injective l' := by
    intro i j hh; apply hl; exact Subtype.ext hh
  obtain ⟨c,hc,hcl⟩ := cycleCandidate_of_incidence ω hs p l' hp hl' h
  let i : Fin s := ⟨0,by omega⟩
  have hdel : c.marks i ∈ deletedMarks S ω := by
    apply Finset.mem_biUnion.mpr
    refine ⟨s,Finset.mem_Icc.mpr ⟨hs,hs6⟩,?_⟩
    apply Finset.mem_biUnion.mpr
    refine ⟨c,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hc⟩,?_⟩
    exact Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩
  rw [hcl] at hdel
  exact (l i).property hdel
end Alteration

section Exceptional
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
variable [Fintype K] [Fintype V]

instance (S : Finset V) (ω : S → Projectivization K V) : Fintype (Retained S ω) := by
  unfold Retained
  infer_instance

def chosenLinePoints (a : V) (d : Projectivization K V) : Finset V :=
  Finset.univ.image (fun t : K => a+t • d.rep)

omit [Fintype V] in
theorem mem_chosenLinePoints (a z : V) (d : Projectivization K V) :
    z ∈ chosenLinePoints a d ↔ OnChosenLine a z d := by
  simp only [chosenLinePoints, Finset.mem_image, Finset.mem_univ, true_and, OnChosenLine]

omit [Fintype V] in
theorem chosenLinePoints_card (a : V) (d : Projectivization K V) :
    (chosenLinePoints a d).card = Fintype.card K := by
  exact (Finset.card_image_iff.mpr (lineMap_injective a d).injOn).trans (Finset.card_univ)

def deletedPoints (S : Finset V) (ω : S → Projectivization K V) : Finset V :=
  (deletedMarks S ω).biUnion (fun a => chosenLinePoints a.val (ω a))

theorem deletedPoints_card_le (S : Finset V) (ω : S → Projectivization K V) :
    (deletedPoints S ω).card ≤ Fintype.card K * (deletedMarks S ω).card := by
  apply Finset.card_biUnion_le.trans
  simp only [chosenLinePoints_card,Finset.sum_const,nsmul_eq_mul, Nat.cast_id]
  exact le_of_eq (Nat.mul_comm _ _)

def exceptionalPoints (S : Finset V) (ω : S → Projectivization K V) (T : ℕ) : Finset V :=
  Finset.univ.filter (fun z => pointDegree S ω z < T) ∪ deletedPoints S ω

theorem exceptionalPoints_card_le (S : Finset V) (ω : S → Projectivization K V) (T : ℕ) :
    (exceptionalPoints S ω T).card ≤
      (Finset.univ.filter (fun z => pointDegree S ω z < T)).card +
        Fintype.card K * (deletedMarks S ω).card :=
  (Finset.card_union_le _ _).trans (Nat.add_le_add_left (deletedPoints_card_le S ω) _)

def retainedIncidence (S : Finset V) (ω : S → Projectivization K V) (z : V) : Finset (Retained S ω) :=
  Finset.univ.filter (fun a => PuncturedIncidence a.val.val z (ω a.val))

theorem incidence_not_deleted (S : Finset V) (ω : S → Projectivization K V) (z : V)
    (hz : z ∉ deletedPoints S ω) (a : S) (ha : PuncturedIncidence a.val z (ω a)) :
    a ∉ deletedMarks S ω := by
  intro hdel
  apply hz
  exact Finset.mem_biUnion.mpr ⟨a,hdel,(mem_chosenLinePoints a.val z (ω a)).mpr ha.2⟩

/-- Outside the discarded geometric lines, no incidence is changed by alteration. -/
theorem retainedIncidence_card (S : Finset V) (ω : S → Projectivization K V) (z : V)
    (hz : z ∉ deletedPoints S ω) : (retainedIncidence S ω z).card = pointDegree S ω z := by
  let e : {a : Retained S ω // PuncturedIncidence a.val.val z (ω a.val)} ≃
      {a : S // PuncturedIncidence a.val z (ω a)} :=
    {toFun := fun a => ⟨a.val.val,a.property⟩
     invFun := fun a => ⟨⟨a.val,incidence_not_deleted S ω z hz a.val a.property⟩,a.property⟩
     left_inv := fun a => rfl
     right_inv := fun a => rfl}
  have h := Fintype.card_congr e
  simpa only [Fintype.card_subtype,pointDegree,retainedIncidence] using h

/-- The exact degree threshold needed for the two-block partition. -/
theorem retainedIncidence_card_ge (S : Finset V) (ω : S → Projectivization K V) (T : ℕ)
    (z : V) (hz : z ∉ exceptionalPoints S ω T) : T ≤ (retainedIncidence S ω z).card := by
  have hz' := not_or.mp ((Finset.mem_union).not.mp hz)
  rw [retainedIncidence_card S ω z hz'.2]
  have hh := hz'.1
  simpa only [Finset.mem_filter,Finset.mem_univ,true_and,not_lt] using hh

theorem retained_card (S : Finset V) (ω : S → Projectivization K V) :
    Fintype.card (Retained S ω) = S.card - (deletedMarks S ω).card := by
  change Fintype.card {a : S // ¬ a ∈ deletedMarks S ω} = _
  rw [Fintype.card_subtype_compl]
  simp
end Exceptional

section AlterationMean
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Fintype K] [Fintype V] [Nontrivial V] [Fintype (Projectivization K V)]

/-- A uniform expectation bound for all removed labels. -/
theorem expect_deletedMarks_le (S : Finset V) (q : ℝ)
    (hcycle : ∀ s ∈ Finset.Icc 2 6,
      (Fintype.card V : ℝ)^s * (Fintype.card K : ℝ)^s *
        (1 / Fintype.card (Projectivization K V) : ℝ)^s ≤ q^12) :
    (𝔼 ω : S → Projectivization K V, ((deletedMarks S ω).card : ℝ)) ≤ 30*q^12 := by
  have hpoint (ω : S → Projectivization K V) : ((deletedMarks S ω).card : ℝ) ≤
      6 * ∑ s ∈ Finset.Icc 2 6, ((badCycles S (finRotate s) ω).card : ℝ) := by
    exact_mod_cast deletedMarks_card_le S ω
  calc
    _ ≤ 𝔼 ω : S → Projectivization K V,
        6 * ∑ s ∈ Finset.Icc 2 6, ((badCycles S (finRotate s) ω).card : ℝ) :=
      Finset.expect_le_expect (fun ω _ => hpoint ω)
    _ = 6 * ∑ s ∈ Finset.Icc 2 6, 𝔼 ω : S → Projectivization K V,
        ((badCycles S (finRotate s) ω).card : ℝ) := by
      rw [← Finset.mul_expect, Finset.expect_sum_comm]
    _ ≤ 6 * ∑ _s ∈ Finset.Icc 2 6, q^12 := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply Finset.sum_le_sum
      intro s hs
      have hh := expect_badCycles_le (K := K) S (finRotate s)
      simp only [Fintype.card_fin] at hh
      exact hh.trans (hcycle s hs)
    _ = 30*q^12 := by norm_num [Finset.sum_const]; ring

/-- One finite averaging step obtains simultaneously the strict rank budget,
the degree bound, and the cycle-free alteration; no asymptotic or external
probabilistic result is being assumed. -/
theorem exists_alteration_budget (S : Finset V) (r T : ℕ) (μ B : ℝ)
    (hμ : 0 < μ) (hT : 2 * (T : ℝ) ≤ μ)
    (hlower : ∀ z : V, μ ≤ pointMean (K := K) S z)
    (hdel : (𝔼 ω : S → Projectivization K V, ((deletedMarks S ω).card : ℝ)) ≤ B)
    (hbudget : 8 * (Fintype.card V : ℝ) + 16*r*(Fintype.card V : ℝ)/μ +
        r*(4*(Fintype.card K : ℝ)+1)*B < (S.card : ℝ)*r) :
    ∃ ω : S → Projectivization K V,
      4 * (2 * Fintype.card V + r * (exceptionalPoints S ω T).card) <
        Fintype.card (Retained S ω) * r := by
  let cost : (S → Projectivization K V) → ℝ := fun ω =>
    4*r*((Finset.univ.filter (fun z : V => pointDegree S ω z < T)).card : ℝ) +
    r*(4*(Fintype.card K : ℝ)+1)*((deletedMarks S ω).card : ℝ)
  have hexp : (𝔼 ω, cost ω) ≤ 16*r*(Fintype.card V : ℝ)/μ +
      r*(4*(Fintype.card K : ℝ)+1)*B := by
    simp only [cost, Finset.expect_add_distrib, ← Finset.mul_expect]
    have hlow := expect_lowDegree_le (K := K) S T μ hμ hT hlower
    have h₁ := mul_le_mul_of_nonneg_left hlow (show 0 ≤ 4*(r : ℝ) by positivity)
    have h₂ := mul_le_mul_of_nonneg_left hdel
      (show 0 ≤ (r : ℝ)*(4*(Fintype.card K : ℝ)+1) by positivity)
    convert add_le_add h₁ h₂ using 2 <;> first | rfl | ring
  obtain ⟨ω,hω⟩ := exists_of_expect_lt cost ((S.card : ℝ)*r - 8*Fintype.card V)
    (hexp.trans_lt (by linarith))
  refine ⟨ω,?_⟩
  have hE := exceptionalPoints_card_le S ω T
  have hD : (deletedMarks S ω).card ≤ S.card :=
    (Finset.card_le_univ _).trans_eq (Fintype.card_coe _)
  have hN := retained_card S ω
  have hN' : (Fintype.card (Retained S ω) : ℝ) = S.card - (deletedMarks S ω).card := by
    rw [hN, Nat.cast_sub hD]
  have hE' : ((exceptionalPoints S ω T).card : ℝ) ≤
      (Finset.univ.filter (fun z : V => pointDegree S ω z < T)).card +
      (Fintype.card K : ℝ) * (deletedMarks S ω).card := by exact_mod_cast hE
  have hEm := mul_le_mul_of_nonneg_left hE' (show 0 ≤ 4*(r : ℝ) by positivity)
  have hh : 4 * (2 * (Fintype.card V : ℝ) + r*(exceptionalPoints S ω T).card) <
      (Fintype.card (Retained S ω) : ℝ) * r := by
    dsimp [cost] at hω
    rw [hN']
    nlinarith
  exact_mod_cast hh
end AlterationMean

/-- The direction-count bounds used in dimension twenty. -/
theorem geom_sum_twenty_bounds {q : ℝ} (hq : 2 ≤ q) :
    q^19 ≤ ∑ i ∈ Finset.range 20, q^i ∧
      ∑ i ∈ Finset.range 20, q^i ≤ 2*q^19 := by
  have hq0 : 0 < q := by linarith
  constructor
  · exact Finset.single_le_sum (fun i _ => pow_nonneg hq0.le i) (by norm_num)
  · have hg := geom_sum_mul q 20
    have hp : q^20 = q^19*q := by ring
    have hh : 2*q^19*(q-1) ≥ q^20-1 := by
      rw [hp]
      nlinarith [mul_nonneg (pow_nonneg hq0.le 19) (show 0 ≤ q-2 by linarith)]
    exact (mul_le_mul_iff_left₀ (show 0 < q-1 by linarith)).mp (by nlinarith [hg])

/-- A concrete bound for every short-cycle contribution. -/
theorem cycle_numeric_bound {q J : ℝ} (hq : 1 ≤ q) (hJ : q^19 ≤ J)
    {s : ℕ} (hs : s ≤ 6) : (q^20)^s * q^s * (1/J)^s ≤ q^12 := by
  have hq0 : 0 < q := by linarith
  have hJ0 : 0 < J := (pow_pos hq0 19).trans_le hJ
  have hf : q^20 * q / J ≤ q^2 := by
    apply (div_le_iff₀ hJ0).mpr
    have hj := mul_le_mul_of_nonneg_left hJ (sq_nonneg q)
    convert hj using 1; ring
  calc
    _ = (q^20*q/J)^s := by simp only [div_pow, mul_pow, one_pow]; ring
    _ ≤ (q^2)^s := pow_le_pow_left₀ (by positivity) hf s
    _ = q^(2*s) := by rw [pow_mul]
    _ ≤ q^12 := pow_le_pow_right₀ hq (by omega)

theorem incidence_numeric_budget {q d r M : ℝ} (hd : 1 ≤ d) (hr : r = 200*d)
    (hq : 1000*d*r^2 ≤ q) (hM : q^20 ≤ d*M) :
    0 < q/(4*d) ∧ 8*r^2 ≤ q/(4*d) ∧
      8*q^20 + 16*r*q^20/(q/(4*d)) + r*(4*q+1)*(30*q^12) < M*r := by
  have hd0 : 0 < d := by linarith
  have hr1 : 1 ≤ r := by rw [hr]; linarith
  have hr0 : 0 < r := by linarith
  have hrr : r ≤ r^2 := by nlinarith
  have hq128 : 128*r*d ≤ q := by
    calc
      _ ≤ 1000*d*r^2 := by nlinarith [mul_le_mul_of_nonneg_left hrr hd0.le]
      _ ≤ q := hq
  have hq300 : 300*r ≤ q := by
    have h₁ : 300*r ≤ 1000*d*r := by nlinarith
    exact h₁.trans ((mul_le_mul_of_nonneg_left hrr (by positivity : 0 ≤ 1000*d)).trans hq)
  have hq1 : 1 ≤ q := by linarith
  have hq0 : 0 < q := by linarith
  have hdp : 0 < 4*d := by positivity
  refine ⟨by positivity, (le_div_iff₀ hdp).mpr ?_, ?_⟩
  · nlinarith [mul_nonneg hd0.le (sq_nonneg r)]
  · have hfirst_eq : 16*r*q^20/(q/(4*d)) = 64*r*d*q^19 := by
      field_simp
      ring
    have hfirst : 2*(16*r*q^20/(q/(4*d))) ≤ q^20 := by
      rw [hfirst_eq]
      have h := mul_le_mul_of_nonneg_right hq128 (pow_nonneg hq0.le 19)
      nlinarith only [h]
    have hq7 : q ≤ q^7 := by simpa using pow_le_pow_right₀ hq1 (show 1 ≤ 7 by norm_num)
    have hsecond : 2*(r*(4*q+1)*(30*q^12)) ≤ q^20 := by
      calc
        _ ≤ 300*r*q^13 := by
          have hh := mul_nonneg (show 0 ≤ 60*r*q^12 by positivity) (show 0 ≤ q-1 by linarith)
          nlinarith only [hh]
        _ ≤ q^7*q^13 := by gcongr; exact hq300.trans hq7
        _ = q^20 := by ring
    have hbig : 200*q^20 ≤ M*r := by
      rw [hr]
      nlinarith [hM]
    have hpos : 0 < q^20 := pow_pos hq0 20
    linarith

/-- The grid is large enough uniformly in the prime. -/
theorem floor_grid_lower {q : ℕ} (hq : 200 ≤ q) :
    (q : ℝ)^20 ≤ (200 : ℝ)^20 * ((q/100 : ℕ) : ℝ)^20 := by
  have hh : q ≤ 200*(q/100) := by omega
  have hh' : (q : ℝ) ≤ 200*((q/100 : ℕ) : ℝ) := by exact_mod_cast hh
  have h := pow_le_pow_left₀ (by positivity : (0:ℝ) ≤ q) hh' 20
  simpa only [mul_pow] using h

section DimensionTwenty
variable (q : ℕ) [Fact q.Prime]

def gridMarks (S : Finset (ZMod q)) : Finset (Fin 20 → ZMod q) :=
  Fintype.piFinset (fun _ => S)

omit [Fact q.Prime] in
theorem gridMarks_card (S : Finset (ZMod q)) : (gridMarks q S).card = S.card^20 := by
  simp [gridMarks, Fintype.card_piFinset]

theorem directions_twenty_card [Fintype (Projectivization (ZMod q) (Fin 20 → ZMod q))] :
    Fintype.card (Projectivization (ZMod q) (Fin 20 → ZMod q)) =
      ∑ i ∈ Finset.range 20, q^i := by
  simpa only [Nat.card_eq_fintype_card,ZMod.card] using
    Projectivization.card_of_finrank (ZMod q) (Fin 20 → ZMod q)
      (Module.finrank_fin_fun (ZMod q))

variable [Fintype (Projectivization (ZMod q) (Fin 20 → ZMod q))]

theorem mean_grid_lower (hq : 200 ≤ q) (S : Finset (ZMod q)) (hS : S.card = q/100)
    (z : Fin 20 → ZMod q) :
    (q : ℝ)/(4*(200:ℝ)^20) ≤ pointMean (K := ZMod q) (gridMarks q S) z := by
  classical
  have hq2 : (2 : ℝ) ≤ q := by exact_mod_cast (show 2 ≤ q by omega)
  have hJ := geom_sum_twenty_bounds hq2
  have hJcast : (Fintype.card (Projectivization (ZMod q) (Fin 20 → ZMod q)) : ℝ) =
      ∑ i ∈ Finset.range 20, (q : ℝ)^i := by
    rw [directions_twenty_card]
    push_cast
    rfl
  rw [← hJcast] at hJ
  have hJpos : (0 : ℝ) < Fintype.card (Projectivization (ZMod q) (Fin 20 → ZMod q)) := by
    have hpow : (0 : ℝ) < (q:ℝ)^19 := by positivity
    exact hpow.trans_le hJ.1
  have hM : (q : ℝ)^20 ≤ (200:ℝ)^20 * (gridMarks q S).card := by
    rw [gridMarks_card,hS,Nat.cast_pow]
    exact floor_grid_lower hq
  have hM2 : 2 ≤ (gridMarks q S).card := by
    rw [gridMarks_card,hS]
    exact (show 2 ≤ q/100 by omega).trans (Nat.le_pow (by norm_num))
  have he : ((gridMarks q S).card : ℝ) ≤ 2*((gridMarks q S).erase z).card := by
    by_cases hz : z ∈ gridMarks q S
    · rw [Finset.card_erase_of_mem hz, Nat.cast_sub (by omega), Nat.cast_one]
      have hh : (2 : ℝ) ≤ (gridMarks q S).card := by exact_mod_cast hM2
      linarith
    · rw [Finset.erase_eq_of_notMem hz]
      have hh : (0 : ℝ) ≤ (gridMarks q S).card := by positivity
      linarith
  rw [pointMean_formula]
  apply (div_le_div_iff₀ (by positivity : (0:ℝ) < 4*(200:ℝ)^20) hJpos).mpr
  have h₁ := mul_le_mul_of_nonneg_left hJ.2 (show (0:ℝ) ≤ q by positivity)
  have h₂ := mul_le_mul_of_nonneg_left he (show (0:ℝ) ≤ (200:ℝ)^20 by positivity)
  calc
    _ ≤ (q : ℝ)*(2*(q : ℝ)^19) := h₁
    _ = 2*(q : ℝ)^20 := by ring
    _ ≤ 2*((200:ℝ)^20*(gridMarks q S).card) := mul_le_mul_of_nonneg_left hM (by norm_num)
    _ ≤ 2*((200:ℝ)^20*(2*((gridMarks q S).erase z).card)) :=
      mul_le_mul_of_nonneg_left h₂ (by norm_num)
    _ = _ := by ring_nf; congr 3; ext i; simp

/-- For a sufficiently large fixed prime, the alteration really attains the
strict finite rank budget. Every subsequent quotient uses this same prime. -/
theorem large_prime_grid_outcome (r : ℕ) (hr : r = 200*200^20)
    (hq200 : 200 ≤ q) (hq : 1000*200^20*r^2 ≤ q)
    (S : Finset (ZMod q)) (hS : S.card = q/100) :
    ∃ ω : gridMarks q S → Projectivization (ZMod q) (Fin 20 → ZMod q),
      4 * (2 * Fintype.card (Fin 20 → ZMod q) +
        r * (exceptionalPoints (gridMarks q S) ω (4*r^2)).card) <
      Fintype.card (Retained (gridMarks q S) ω) * r := by
  have hM : (q : ℝ)^20 ≤ (200:ℝ)^20 * (gridMarks q S).card := by
    rw [gridMarks_card,hS,Nat.cast_pow]
    exact floor_grid_lower hq200
  have hr' : (r : ℝ) = 200*(200:ℝ)^20 := by exact_mod_cast hr
  have hq' : 1000*(200:ℝ)^20*(r:ℝ)^2 ≤ q := by exact_mod_cast hq
  have hn := incidence_numeric_budget (by norm_num : (1:ℝ) ≤ (200:ℝ)^20) hr' hq' hM
  have hJ : (q : ℝ)^19 ≤ Fintype.card (Projectivization (ZMod q) (Fin 20 → ZMod q)) := by
    rw [directions_twenty_card]
    push_cast
    exact (geom_sum_twenty_bounds (by exact_mod_cast (show 2 ≤ q by omega))).1
  have hcycle := expect_deletedMarks_le (K := ZMod q) (gridMarks q S) (q : ℝ) (by
    intro s hs
    simp only [Fintype.card_fun, Fintype.card_fin, ZMod.card, Nat.cast_pow]
    exact cycle_numeric_bound (by exact_mod_cast (show 1 ≤ q by omega)) hJ (Finset.mem_Icc.mp hs).2)
  apply exists_alteration_budget (gridMarks q S) r (4*r^2) ((q:ℝ)/(4*(200:ℝ)^20))
    (30*(q:ℝ)^12) hn.1
  · simp only [Nat.cast_mul,Nat.cast_ofNat,Nat.cast_pow]
    nlinarith only [hn.2.1]
  · exact mean_grid_lower q hq200 S hS
  · exact hcycle
  · simpa only [Fintype.card_fun,Fintype.card_fin,ZMod.card,Nat.cast_pow] using hn.2.2
end DimensionTwenty

/-- Exact finite data fixed once for all before any finite quotient is chosen.
No geometric or group-theoretic conclusion is part of these data. -/
structure MarkedLineData (q r : ℕ) [Fact q.Prime] where
  scalarGrid : Finset (ZMod q)
  grid_card : scalarGrid.card = q/100
  Label : Type
  [labelFintype : Fintype Label]
  mark : Label → Fin 20 → ZMod q
  direction : Label → Projectivization (ZMod q) (Fin 20 → ZMod q)
  marks_mem : ∀ i t, mark i t ∈ scalarGrid
  marks_injective : Function.Injective mark
  exceptional : Finset (Fin 20 → ZMod q)
  degree : ∀ z, z ∉ exceptional → 4*r^2 ≤
    (Finset.univ.filter (fun i => PuncturedIncidence (mark i) z (direction i))).card
  budget : 4*(2*q^20+r*exceptional.card) < Fintype.card Label*r
  girth : ∀ a (w : (relationGraph (fun z i =>
    PuncturedIncidence (mark i) z (direction i))).Walk a a), w.IsCycle → 12 < w.length

attribute [instance] MarkedLineData.labelFintype

theorem exists_markedLineData :
    ∃ (q r : ℕ) (hq : q.Prime), let _ : Fact q.Prime := ⟨hq⟩
      0 < r ∧ r < q ∧ 100*100^20 ≤ r ∧ Nonempty (MarkedLineData q r) := by
  classical
  let r : ℕ := 200*200^20
  obtain ⟨q,hq,hprime⟩ := Nat.exists_infinite_primes (1000*200^20*r^2+400)
  let : Fact q.Prime := ⟨hprime⟩
  let : Fintype (Projectivization (ZMod q) (Fin 20 → ZMod q)) := Fintype.ofFinite _
  have hq200 : 200 ≤ q := by omega
  have hqbig : 1000*200^20*r^2 ≤ q := by omega
  have hr : 0 < r := by norm_num [r]
  have hrq : r < q := by
    have hh : r < 1000*200^20*r^2+400 := by norm_num [r]
    exact hh.trans_le hq
  have hrc : 100*100^20 ≤ r := by norm_num [r]
  obtain ⟨S,_,hS⟩ := Finset.exists_subset_card_eq
    (s := (Finset.univ : Finset (ZMod q))) (n := q/100) (by
      simpa only [Finset.card_univ,ZMod.card] using Nat.div_le_self q 100)
  obtain ⟨ω,hω⟩ := large_prime_grid_outcome q r rfl hq200 hqbig S hS
  refine ⟨q,r,hprime,hr,hrq,hrc,⟨?_⟩⟩
  exact
    { scalarGrid := S
      grid_card := hS
      Label := Retained (gridMarks q S) ω
      mark := fun i => i.val.val
      direction := fun i => ω i.val
      marks_mem := fun i => Fintype.mem_piFinset.mp i.val.property
      marks_injective := fun _ _ h => Subtype.ext (Subtype.ext h)
      exceptional := exceptionalPoints (gridMarks q S) ω (4*r^2)
      degree := retainedIncidence_card_ge (gridMarks q S) ω (4*r^2)
      budget := by simpa only [Fintype.card_fun,Fintype.card_fin,ZMod.card] using hω
      girth := retained_girth (gridMarks q S) ω }

namespace MarkedLineData
variable {q r : ℕ} [Fact q.Prime] (d : MarkedLineData q r)

/-- The marking grid gives an a priori upper bound on the number of labels. -/
theorem card_labels_le : Fintype.card d.Label ≤ q^20 := by
  simpa only [Fintype.card_fun,Fintype.card_fin,ZMod.card] using
    Fintype.card_le_of_injective d.mark d.marks_injective

theorem exists_regular : ∃ z, z ∉ d.exceptional := by
  classical
  by_contra! h
  have hE : d.exceptional = Finset.univ := Finset.eq_univ_of_forall h
  have hc : d.exceptional.card = q^20 := by simp only [hE,Finset.card_univ,
      Fintype.card_fun,Fintype.card_fin,ZMod.card]
  have hd := d.budget
  rw [hc] at hd
  have hm := Nat.mul_le_mul_right r d.card_labels_le
  rw [Nat.mul_comm (q^20) r] at hm
  omega

theorem degree_cutoff (hq : 200 ≤ q) : 2*(20*(d.scalarGrid.card-1)) < q-1 := by
  rw [d.grid_card]
  omega
end MarkedLineData

end
end Release075

end OAI
end
end

section
section
namespace OAI

namespace Release075

/-- Internal reduction of an edge walk; no condition is imposed at the closing seam. -/
def ReducedWalk {V : Type*} {G : SimpleGraph V} {a b : V} (p : G.Walk a b) : Prop :=
  ∀ n, n + 2 ≤ p.length → p.getVert n ≠ p.getVert (n + 2)

theorem ReducedWalk.tail {V : Type*} {G : SimpleGraph V} {a b c : V}
    {e : G.Adj a b} {p : G.Walk b c} (h : ReducedWalk (p.cons e)) : ReducedWalk p := by
  intro n hn
  have hh := h (n + 1) (by simpa using Nat.add_le_add_right hn 1)
  simpa only [SimpleGraph.Walk.getVert_cons_succ, Nat.add_right_comm n 1 2] using hh

/-- A locally injective graph homomorphism preserves internal reduction. -/
def LocallyInjective {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (f : G →g H) : Prop :=
  ∀ a b c, G.Adj a b → G.Adj a c → f b = f c → b = c

theorem ReducedWalk.map {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (f : G →g H) (hf : LocallyInjective f) {a b : V} {p : G.Walk a b}
    (hp : ReducedWalk p) : ReducedWalk (p.map f) := by
  intro n hn heq
  simp only [SimpleGraph.Walk.length_map] at hn
  simp only [SimpleGraph.Walk.getVert_map] at heq
  apply hp n hn
  apply hf (p.getVert (n+1)) _ _
    (p.adj_getVert_succ (by omega)).symm (p.adj_getVert_succ (by omega)) heq

/-- A reduced walk which is not a simple path contains a cycle of no greater length.
In particular, a nonempty reduced *closed* walk need not be reduced at its seam. -/
theorem reduced_path_or_cycle {V : Type*} {G : SimpleGraph V} {a b : V}
    (p : G.Walk a b) (hp : ReducedWalk p) :
    p.IsPath ∨ ∃ (c : V) (w : G.Walk c c), w.IsCycle ∧ w.length ≤ p.length := by
  classical
  induction p with
  | nil => exact Or.inl SimpleGraph.Walk.IsPath.nil
  | @cons a b c e p ih =>
    rcases ih hp.tail with hpath | ⟨d,w,hw,hlen⟩
    · by_cases ha : a ∈ p.support
      · right
        let t := p.takeUntil a ha
        have ht : t.IsPath := hpath.takeUntil ha
        have hedge : s(a,b) ∉ t.edges := by
          intro he
          have he' : s(b,a) ∈ t.edges := by simpa only [Sym2.eq_swap] using he
          have hlen : t.length = 1 := ht.length_eq_one_of_mem_edges he'
          have hget : p.getVert 1 = a := by
            change (p.takeUntil a ha).length = 1 at hlen
            simpa only [hlen] using p.getVert_length_takeUntil ha
          have hp0 := hp 0 (by
            simp only [SimpleGraph.Walk.length_cons]
            have hh := p.length_takeUntil_le_length ha
            change t.length ≤ p.length at hh
            omega)
          apply hp0
          simpa only [SimpleGraph.Walk.getVert_zero, SimpleGraph.Walk.getVert_cons_succ] using hget.symm
        exact ⟨a,t.cons e,(SimpleGraph.Walk.cons_isCycle_iff _ _).mpr ⟨ht,hedge⟩,
          Nat.add_le_add_right (p.length_takeUntil_le_length ha) 1⟩
      · exact Or.inl ((SimpleGraph.Walk.cons_isPath_iff _ _).mpr ⟨hpath,ha⟩)
    · exact Or.inr ⟨d,w,hw,hlen.trans (by simp)⟩

theorem reduced_closed_length_ge {V : Type*} {G : SimpleGraph V} (k : ℕ)
    (hgirth : ∀ a (w : G.Walk a a), w.IsCycle → k ≤ w.length)
    {a : V} (p : G.Walk a a) (hne : 0 < p.length) (hp : ReducedWalk p) :
    k ≤ p.length := by
  rcases reduced_path_or_cycle p hp with hpath | ⟨c,w,hw,hlen⟩
  · have h := SimpleGraph.Walk.length_eq_zero_iff.mpr (SimpleGraph.Walk.isPath_iff_nil.mp hpath)
    omega
  · exact (hgirth c w hw).trans hlen

/-- The same girth bound controls a reduced path between distinct vertices of one
fiber of an immersion, even without a closing-seam condition. -/
theorem immersion_fiber_distance {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (f : G →g H) (hf : LocallyInjective f) (k : ℕ)
    (hgirth : ∀ a (w : H.Walk a a), w.IsCycle → k ≤ w.length)
    {a b : V} (hneq : a ≠ b) (heq : f a = f b) (p : G.Walk a b)
    (hp : ReducedWalk p) : k ≤ p.length := by
  have hpos : 0 < p.length := Nat.pos_iff_ne_zero.mpr (fun h => hneq (p.eq_of_length_eq_zero h))
  let w := (p.map f).copy rfl heq.symm
  have hr : ReducedWalk w := by
    intro n hn
    simpa only [w, SimpleGraph.Walk.length_copy, SimpleGraph.Walk.getVert_copy] using
      (hp.map f hf n (by simpa only [w, SimpleGraph.Walk.length_copy] using hn))
  simpa [w] using reduced_closed_length_ge k hgirth w (by simpa [w] using hpos) hr

/-- Simple paths are internally reduced. -/
theorem ReducedWalk.of_isPath {V : Type*} {G : SimpleGraph V} {a b : V}
    {p : G.Walk a b} (hp : p.IsPath) : ReducedWalk p := by
  intro n hn he
  have hh := hp.getVert_injOn (by change n ≤ p.length; omega)
    (by change n + 2 ≤ p.length; omega) he
  omega

/-- Bipartiteness gives four as the least possible cycle length, without a finiteness assumption. -/
theorem relationGraph_cycle_length {A B : Type*} (R : A → B → Prop)
    (a : A ⊕ B) (p : (relationGraph R).Walk a a) (hp : p.IsCycle) : 4 ≤ p.length := by
  let c : (relationGraph R).Coloring Bool :=
    {toFun := Sum.elim (fun _ => false) (fun _ => true)
     map_rel' := by intro x y h; cases x <;> cases y <;> simp_all [relationGraph]}
  have he := (c.even_length_iff_congr p).mpr Iff.rfl
  have ht := hp.three_le_length
  obtain ⟨n,hn⟩ := he
  omega

/-- The shift by a number in [0,r) remains injective modulo any modulus at least r. -/
theorem fin_natCast_injective (r s : ℕ) (hs : r ≤ s) :
    Function.Injective (fun v : Fin r => (v.val : ZMod s)) := by
  intro v w h
  by_cases hsz : s = 0
  · have : r = 0 := by omega
    exact Fin.elim0 (this ▸ v)
  · let : NeZero s := ⟨hsz⟩
    apply Fin.ext
    have hh := congrArg ZMod.val h
    simpa only [ZMod.val_natCast, Nat.mod_eq_of_lt (v.isLt.trans_le hs),
      Nat.mod_eq_of_lt (w.isLt.trans_le hs)] using hh

/-- Data of either of the two small-angle links. At V use the first block coordinate;
at W use the second and swap u,v. The membership and uniqueness fields are exactly
the partition of I(z) into blocks, not geometric conclusions. -/
structure ShiftScheme (I P B : Type*) (r : ℕ) (inc : P → Finset I) where
  size : B → ℕ
  size_ge : ∀ b, r ≤ size b
  labels : B → Finset I
  coord : ∀ b, {i // i ∈ labels b} → ZMod (size b)
  point : B → P
  incident : ∀ b i, i ∈ labels b → i ∈ inc (point b)
  unique : ∀ b c i, point b = point c → i ∈ labels b → i ∈ labels c → b = c

namespace ShiftScheme
variable {I P B : Type*} {r : ℕ} {inc : P → Finset I} (d : ShiftScheme I P B r inc)

abbrev XDirection := I × Fin r × Fin r
abbrev LDirection := Σ b : B, Fin r × ZMod (d.size b)

def attached (x : XDirection (I := I) (r := r)) (l : d.LDirection) : Prop :=
  ∃ hi : x.1 ∈ d.labels l.1,
    x.2.1 = l.2.1 ∧ l.2.2 = d.coord l.1 ⟨x.1,hi⟩ + (x.2.2.val : ZMod (d.size l.1))

def link : SimpleGraph ((XDirection (I := I) (r := r)) ⊕ d.LDirection) :=
  relationGraph d.attached

def projection : d.link →g relationGraph (fun i z => i ∈ inc z) where
  toFun := Sum.map (fun x => x.1) (fun l => d.point l.1)
  map_rel' := by
    intro x y h
    cases x with
    | inl x => cases y with
      | inl y => exact h.elim
      | inr l => obtain ⟨hi,_,_⟩ := h; exact d.incident l.1 x.1 hi
    | inr l => cases y with
      | inr m => exact h.elim
      | inl x => obtain ⟨hi,_,_⟩ := h; exact d.incident l.1 x.1 hi

theorem projection_locallyInjective : LocallyInjective d.projection := by
  intro a b c hab hac heq
  cases a with
  | inl x =>
    cases b with
    | inl y => exact hab.elim
    | inr b =>
      cases c with
      | inl y => exact hac.elim
      | inr c =>
        obtain ⟨i,u,v⟩ := x
        obtain ⟨b,ub,j⟩ := b
        obtain ⟨c,uc,k⟩ := c
        obtain ⟨hi,hui,hj⟩ := hab
        obtain ⟨hi',hui',hk⟩ := hac
        have hbc : d.point b = d.point c := Sum.inr.inj heq
        have hbc' := d.unique b c i hbc hi hi'
        subst c
        have hu : ub = uc := hui.symm.trans hui'
        subst uc
        have hjk : j = k := hj.trans hk.symm
        subst k
        rfl
  | inr l =>
    cases b with
    | inr m => exact hab.elim
    | inl x =>
      cases c with
      | inr m => exact hac.elim
      | inl y =>
        obtain ⟨b,ub,j⟩ := l
        obtain ⟨i,u,v⟩ := x
        obtain ⟨i',u',v'⟩ := y
        have hii : i = i' := Sum.inl.inj heq
        subst i'
        obtain ⟨hi,hu,hj⟩ := hab
        obtain ⟨hi',hu',hj'⟩ := hac
        have huu : u = u' := hu.trans hu'.symm
        subst u'
        have hvv : (v.val : ZMod (d.size b)) = (v'.val : ZMod (d.size b)) :=
          add_left_cancel (hj.symm.trans hj')
        have hv := fin_natCast_injective r (d.size b) (d.size_ge b) hvv
        subst v'
        rfl

/-- Girth transfers through the locally injective projection. -/
theorem link_cycle_length (k : ℕ)
    (hgirth : ∀ a (w : (relationGraph (fun i z => i ∈ inc z)).Walk a a),
      w.IsCycle → k ≤ w.length)
    (a : XDirection (I := I) (r := r) ⊕ d.LDirection)
    (p : d.link.Walk a a) (hp : p.IsCycle) : k ≤ p.length := by
  have hred : ReducedWalk p := by
    intro n hn he
    have h3 := hp.three_le_length
    by_cases hn0 : n = 0
    · subst n
      have he' : p.getVert p.length = p.getVert 2 := by simpa using he
      have hh := hp.getVert_injOn (by exact ⟨by omega, le_rfl⟩)
        (by exact ⟨by omega, by omega⟩) he'
      omega
    · have hh := hp.getVert_injOn (by exact ⟨by omega, by omega⟩)
        (by exact ⟨by omega, hn⟩) he
      omega
  have hmap := hred.map d.projection d.projection_locallyInjective
  simpa using reduced_closed_length_ge k hgirth (p.map d.projection)
    (by have h3 := hp.three_le_length; simp only [SimpleGraph.Walk.length_map]; omega) hmap

/-- Distinct directions of one x-label are separated by the full incidence girth. -/
theorem same_label_path_length (k : ℕ)
    (hgirth : ∀ a (w : (relationGraph (fun i z => i ∈ inc z)).Walk a a),
      w.IsCycle → k ≤ w.length)
    (i : I) (u v u' v' : Fin r) (hne : (u,v) ≠ (u',v'))
    (p : d.link.Walk (.inl (i,u,v)) (.inl (i,u',v'))) (hp : p.IsPath) :
    k ≤ p.length := by
  have hn : (Sum.inl (i,u,v) : XDirection (I := I) (r := r) ⊕ d.LDirection) ≠
      Sum.inl (i,u',v') := by
    intro h
    exact hne (Prod.mk.inj (Sum.inl.inj h)).2
  exact immersion_fiber_distance d.projection d.projection_locallyInjective k hgirth
    hn rfl p (ReducedWalk.of_isPath hp)

end ShiftScheme

end Release075

namespace Release075

/-- Pick one block and one leaf index for the two edges in the spanning tree. -/
structure BlockPresentation (I B : Type*) (r : ℕ) where
  block : B → CartesianBlock I r
  baseBlock : B
  baseIndex : Fin r

namespace BlockPresentation
variable {I B : Type*} {r : ℕ} (d : BlockPresentation I B r)

abbrev XEdge := I × Fin r × Fin r
abbrev LEdge := Σ b : B, Fin r × ZMod (d.block b).s
abbrev REdge := Σ b : B, Fin r × ZMod (d.block b).t
abbrev Edge := XEdge (I := I) (r := r) ⊕ (d.LEdge ⊕ d.REdge)

/-- The orientation of a face is `L x R⁻¹`, not a permuted product. -/
def triangleWord (b : B) (i : (d.block b).labels) (u v : Fin r) : FreeGroup d.Edge :=
  FreeGroup.of (.inr (.inl ⟨b,u,((d.block b).coordinates i).1 + (v.val : ZMod (d.block b).s)⟩)) *
  FreeGroup.of (.inl (i.val,u,v)) *
  (FreeGroup.of (.inr (.inr ⟨b,v,((d.block b).coordinates i).2 + (u.val : ZMod (d.block b).t)⟩)))⁻¹

def treeL : d.Edge := .inr (.inl ⟨d.baseBlock,d.baseIndex,0⟩)
def treeR : d.Edge := .inr (.inr ⟨d.baseBlock,d.baseIndex,0⟩)

def relators : Set (FreeGroup d.Edge) :=
  {w | (∃ b i u v, w = d.triangleWord b i u v) ∨
    w = FreeGroup.of d.treeL ∨ w = FreeGroup.of d.treeR}

abbrev GroupType := PresentedGroup d.relators

def edge (e : d.Edge) : d.GroupType := PresentedGroup.of e

def x (i : I) (u v : Fin r) : d.GroupType := d.edge (.inl (i,u,v))
def l (b : B) (u : Fin r) (j : ZMod (d.block b).s) : d.GroupType :=
  d.edge (.inr (.inl ⟨b,u,j⟩))
def rr (b : B) (v : Fin r) (k : ZMod (d.block b).t) : d.GroupType :=
  d.edge (.inr (.inr ⟨b,v,k⟩))

/-- The triangle faces impose precisely the factorization used by the rank proof. -/
theorem triangle_relation (b : B) (i : (d.block b).labels) (u v : Fin r) :
    d.x i u v = (d.l b u (((d.block b).coordinates i).1 + (v.val : ZMod (d.block b).s)))⁻¹ *
      d.rr b v (((d.block b).coordinates i).2 + (u.val : ZMod (d.block b).t)) := by
  have h := PresentedGroup.one_of_mem (rels := d.relators)
    (show d.triangleWord b i u v ∈ d.relators from Or.inl ⟨b,i,u,v,rfl⟩)
  apply (eq_inv_mul_iff_mul_eq).mpr
  exact mul_inv_eq_one.mp (by simpa only [triangleWord,map_mul,map_inv,
    edge,x,l,rr,PresentedGroup.of] using h)

theorem block_relations (b : B) : (d.block b).Relations d.x :=
  ⟨d.l b,d.rr b,d.triangle_relation b⟩

theorem treeL_eq_one : d.edge d.treeL = 1 :=
  PresentedGroup.one_of_mem (Or.inr (Or.inl rfl))

theorem treeR_eq_one : d.edge d.treeR = 1 :=
  PresentedGroup.one_of_mem (Or.inr (Or.inr rfl))

theorem edge_closure : Subgroup.closure (Set.range d.edge) = ⊤ :=
  PresentedGroup.closure_range_of d.relators

/-- A rectangular word is nontrivial exactly when it lies outside the actual normal
closure of the triangle and tree relators. This does not assume that nonmembership. -/
theorem rectangle_ne_one_iff (i : I) (u u' v v' : Fin r) :
    d.x i u v * (d.x i u' v)⁻¹ * d.x i u' v' * (d.x i u v')⁻¹ ≠ 1 ↔
      FreeGroup.of (.inl (i,u,v) : d.Edge) * (FreeGroup.of (.inl (i,u',v) : d.Edge))⁻¹ *
      FreeGroup.of (.inl (i,u',v') : d.Edge) * (FreeGroup.of (.inl (i,u,v') : d.Edge))⁻¹ ∉
        Subgroup.normalClosure d.relators := by
  rw [← PresentedGroup.mk_eq_one_iff]
  simp only [map_mul,map_inv,x,edge,PresentedGroup.of]

end BlockPresentation

/-- Left translation is an automorphism of the right-generator Cayley graph. -/
def cayleyLeft {G : Type*} [Group G] (S : Set G) (a : G) :
    SimpleGraph.mulCayley S →g SimpleGraph.mulCayley S where
  toFun := (a * ·)
  map_rel' := by
    intro x y h
    exact (SimpleGraph.mulCayley_adj_mul_iff_right).mpr h

theorem cayley_reachable_mul_left {G : Type*} [Group G] (S : Set G) (a : G)
    {b c : G} (h : (SimpleGraph.mulCayley S).Reachable b c) :
    (SimpleGraph.mulCayley S).Reachable (a*b) (a*c) := h.map (cayleyLeft S a)

/-- The connected Cayley graph is derived from generation, not included as data. -/
theorem cayley_connected_of_closure {G : Type*} [Group G] (S : Set G)
    (hS : Subgroup.closure S = ⊤) : (SimpleGraph.mulCayley S).Connected := by
  classical
  have hreach (g : G) : (SimpleGraph.mulCayley S).Reachable 1 g := by
    have hg : g ∈ Subgroup.closure S := by rw [hS]; exact Subgroup.mem_top _
    induction hg using Subgroup.closure_induction with
    | mem g hg =>
      by_cases h : 1 = g
      · subst g; exact SimpleGraph.Reachable.refl _
      · exact (SimpleGraph.mulCayley_adj' S 1 g |>.mpr
          ⟨h,g,hg,Or.inl (one_mul g)⟩).reachable
    | one => exact SimpleGraph.Reachable.refl _
    | mul a b _ _ ha hb =>
      exact ha.trans (by simpa using cayley_reachable_mul_left S a hb)
    | inv a _ ha =>
      have hh := cayley_reachable_mul_left S a⁻¹ ha
      simpa using hh.symm
  exact ⟨fun a b => (hreach a).symm.trans (hreach b)⟩

namespace BlockPresentation
variable {I B : Type*} {r : ℕ} (d : BlockPresentation I B r)

instance [Fintype I] [Fintype B] : Fintype d.Edge := by
  unfold Edge LEdge REdge
  infer_instance

theorem generators_finite [Fintype I] [Fintype B] : (Set.range d.edge).Finite :=
  Set.finite_range d.edge

theorem cayley_connected : (SimpleGraph.mulCayley (Set.range d.edge)).Connected :=
  cayley_connected_of_closure _ d.edge_closure

end BlockPresentation
end Release075

namespace Release075
noncomputable section
open scoped BigOperators
local instance (α : Type*) : DecidableEq α := Classical.decEq α

/-- The two formalizations of puncturing remove exactly parameter zero / the
line's own mark. Other marked points are retained in both. -/
theorem mem_puncturedLine_iff_incidence {T K : Type*} [Fintype T] [Field K] [Fintype K]
    (a z : T → K) (d : Projectivization K (T → K)) :
    z ∈ puncturedLine a d.rep ↔ PuncturedIncidence a z d := by
  classical
  simp only [puncturedLine,Finset.mem_image,Finset.mem_erase,Finset.mem_univ,and_true]
  constructor
  · rintro ⟨t,ht,rfl⟩
    refine ⟨?_,t,?_⟩
    · intro h
      have hh : affineLineMap a d.rep t = affineLineMap a d.rep 0 := by
        rw [show affineLineMap a d.rep 0 = a by ext t; simp [affineLineMap]]
        exact h
      exact ht (affineLineMap_injective a d.rep d.rep_nonzero hh)
    · rfl
  · rintro ⟨hz,t,ht⟩
    refine ⟨t,?_,ht⟩
    intro he
    subst t
    simp only [zero_smul,add_zero] at ht
    exact hz ht.symm

/-- A chosen two-block partition. The fields contain only finite combinatorial
partition data, no geometric or group-theoretic conclusion. -/
structure TwoBlockPartition (I : Type*) (r : ℕ) (A : Finset I) where
  zero : CartesianBlock I r
  one : CartesianBlock I r
  disjoint : Disjoint zero.labels one.labels
  cover : zero.labels ∪ one.labels = A

namespace MarkedLineData
variable {q r : ℕ} [Fact q.Prime] (d : MarkedLineData q r)

def incidences (z : Fin 20 → ZMod q) : Finset d.Label :=
  lineIncidence d.mark (fun i => (d.direction i).rep) z

theorem mem_incidences (z : Fin 20 → ZMod q) (i : d.Label) :
    i ∈ d.incidences z ↔ PuncturedIncidence (d.mark i) z (d.direction i) := by
  classical
  simp only [incidences,lineIncidence,Finset.mem_filter,Finset.mem_univ,true_and]
  exact mem_puncturedLine_iff_incidence _ _ _

theorem incidences_card_ge (z : Fin 20 → ZMod q) (hz : z ∉ d.exceptional) :
    4*r^2 ≤ (d.incidences z).card := by
  convert d.degree z hz using 1
  congr 1
  ext i
  simp only [d.mem_incidences,Finset.mem_filter,Finset.mem_univ,true_and]

abbrev Regular := {z : Fin 20 → ZMod q // z ∉ d.exceptional}
abbrev BlockIndex := d.Regular × Bool

instance : Fintype d.Regular := Fintype.ofFinite _

noncomputable def partition (hr : 0 < r) (z : d.Regular) :
    TwoBlockPartition d.Label r (d.incidences z) := by
  classical
  have hn : Nonempty (TwoBlockPartition d.Label r (d.incidences z)) := by
    obtain ⟨b₀,b₁,hd,hu⟩ := exists_two_cartesian_blocks r hr (d.incidences z)
      (d.incidences_card_ge z z.property)
    exact ⟨⟨b₀,b₁,hd,hu⟩⟩
  exact Classical.choice hn

noncomputable def block (hr : 0 < r) (b : d.BlockIndex) : CartesianBlock d.Label r :=
  if b.2 then (d.partition hr b.1).one else (d.partition hr b.1).zero

theorem block_incident (hr : 0 < r) (b : d.BlockIndex) (i : d.Label)
    (hi : i ∈ (d.block hr b).labels) : i ∈ d.incidences b.1 := by
  rw [← (d.partition hr b.1).cover]
  rcases b with ⟨z,e⟩
  cases e with
  | false => exact Finset.mem_union_left _ hi
  | true => exact Finset.mem_union_right _ hi

theorem block_unique (hr : 0 < r) (b c : d.BlockIndex) (i : d.Label)
    (hz : b.1.val = c.1.val) (hi : i ∈ (d.block hr b).labels)
    (hi' : i ∈ (d.block hr c).labels) : b = c := by
  rcases b with ⟨z,e⟩
  rcases c with ⟨w,f⟩
  have hw : z = w := Subtype.ext hz
  subst w
  cases e <;> cases f
  · rfl
  · exact ((Finset.disjoint_left.mp (d.partition hr z).disjoint) hi hi').elim
  · exact ((Finset.disjoint_left.mp (d.partition hr z).disjoint) hi' hi).elim
  · rfl

/-- The presentation is fixed from the finite data, before any quotient or
putative separation homomorphism is considered. -/
noncomputable def presentation (hr : 0 < r) : BlockPresentation d.Label d.BlockIndex r where
  block := d.block hr
  baseBlock := (⟨d.exists_regular.choose,d.exists_regular.choose_spec⟩,false)
  baseIndex := ⟨0,hr⟩

def RectangularNontriviality (hr : 0 < r) : Prop :=
  ∀ i, RectanglesSurvive ((d.presentation hr).x i)

/-- The complete finite-quotient argument applied to the actual fixed
presentation. The geometric nontriviality premise is established below. -/
theorem presentation_not_residuallyFinite (hr : 0 < r) (hq : r < q) (hq200 : 200 ≤ q)
    (hrect : d.RectangularNontriviality hr) :
    ¬ Group.ResiduallyFinite (d.presentation hr).GroupType := by
  classical
  apply not_residuallyFinite_of_line_blocks r q hq d.scalarGrid d.mark
    (fun i => (d.direction i).rep) d.marks_mem d.marks_injective
    (fun i => (d.direction i).rep_nonzero) (by simpa only [Fintype.card_fin] using d.degree_cutoff hq200)
    d.exceptional (d.presentation hr).x hrect _ (by
      simpa only [Fintype.card_fun,Fintype.card_fin,ZMod.card] using d.budget)
  intro z hz
  let p := d.partition hr ⟨z,hz⟩
  refine ⟨p.zero,p.one,p.disjoint,p.cover,?_,?_⟩
  · exact (d.presentation hr).block_relations (⟨z,hz⟩,false)
  · exact (d.presentation hr).block_relations (⟨z,hz⟩,true)

/-- Small-angle link at V. -/
noncomputable def vShift (hr : 0 < r) :
    ShiftScheme d.Label (Fin 20 → ZMod q) d.BlockIndex r d.incidences where
  size b := (d.block hr b).s
  size_ge b := (d.block hr b).hs
  labels b := (d.block hr b).labels
  coord b i := ((d.block hr b).coordinates i).1
  point b := b.1
  incident := d.block_incident hr
  unique := d.block_unique hr

/-- Small-angle link at W, with u,v interchanged. -/
noncomputable def wShift (hr : 0 < r) :
    ShiftScheme d.Label (Fin 20 → ZMod q) d.BlockIndex r d.incidences where
  size b := (d.block hr b).t
  size_ge b := (d.block hr b).ht
  labels b := (d.block hr b).labels
  coord b i := ((d.block hr b).coordinates i).2
  point b := b.1
  incident := d.block_incident hr
  unique := d.block_unique hr

/-- Switch the two incidence-graph parts without altering any incidence. -/
def swapIncidence : relationGraph (fun i z => i ∈ d.incidences z) →g
    relationGraph (fun z i => PuncturedIncidence (d.mark i) z (d.direction i)) where
  toFun := Sum.swap
  map_rel' := by
    intro x y h
    cases x with
    | inl i => cases y with
      | inl j => exact h.elim
      | inr z => exact (d.mem_incidences z i).mp h
    | inr z => cases y with
      | inr w => exact h.elim
      | inl i => exact (d.mem_incidences z i).mp h

theorem incidences_girth (a : d.Label ⊕ (Fin 20 → ZMod q))
    (p : (relationGraph (fun i z => i ∈ d.incidences z)).Walk a a) (hp : p.IsCycle) :
    14 ≤ p.length := by
  have hi : Function.Injective d.swapIncidence := by
    intro x y h
    have hh := congrArg Sum.swap h
    simpa [swapIncidence] using hh
  have hh := d.girth _ (p.map d.swapIncidence) (hp.map hi)
  simp only [SimpleGraph.Walk.length_map] at hh
  have he := relationGraph_cycle_length (fun i z => i ∈ d.incidences z) a p hp
  let c : (relationGraph (fun i z => i ∈ d.incidences z)).Coloring Bool :=
    {toFun := Sum.elim (fun _ => false) (fun _ => true)
     map_rel' := by intro x y h; cases x <;> cases y <;> simp_all [relationGraph]}
  obtain ⟨n,hn⟩ := (c.even_length_iff_congr p).mpr Iff.rfl
  omega

theorem v_link_girth (hr : 0 < r) (a)
    (p : (d.vShift hr).link.Walk a a) (hp : p.IsCycle) : 14 ≤ p.length :=
  (d.vShift hr).link_cycle_length 14 d.incidences_girth a p hp

theorem w_link_girth (hr : 0 < r) (a)
    (p : (d.wShift hr).link.Walk a a) (hp : p.IsCycle) : 14 ≤ p.length :=
  (d.wShift hr).link_cycle_length 14 d.incidences_girth a p hp

theorem v_same_label_distance (hr : 0 < r) (i : d.Label)
    (u v u' v' : Fin r) (hne : (u,v) ≠ (u',v'))
    (p : (d.vShift hr).link.Walk (.inl (i,u,v)) (.inl (i,u',v'))) (hp : p.IsPath) :
    14 ≤ p.length :=
  (d.vShift hr).same_label_path_length 14 d.incidences_girth i u v u' v' hne p hp

theorem w_same_label_distance (hr : 0 < r) (i : d.Label)
    (u v u' v' : Fin r) (hne : (u,v) ≠ (u',v'))
    (p : (d.wShift hr).link.Walk (.inl (i,u,v)) (.inl (i,u',v'))) (hp : p.IsPath) :
    14 ≤ p.length :=
  (d.wShift hr).same_label_path_length 14 d.incidences_girth i u v u' v' hne p hp

end MarkedLineData

end
end Release075

end OAI
end
end

section
section
namespace OAI

namespace Release075
/-! A combinatorial fundamental groupoid of the **un-collapsed** triangle complex.
The quotient imposes only its triangular faces. Tree edges are used for basing,
not mistaken for triangular two-cells in a van Kampen diagram. -/
namespace BlockPresentation
open CategoryTheory

variable {I B : Type} {r : ℕ} (d : BlockPresentation I B r)

inductive Vertex (d : BlockPresentation I B r) : Type
  | o | v | w

inductive Arrow : d.Vertex → d.Vertex → Type
  | x (e : XEdge (I := I) (r := r)) : Arrow .v .w
  | l (e : d.LEdge) : Arrow .o .v
  | rr (e : d.REdge) : Arrow .o .w

instance vertexQuiver : Quiver d.Vertex := ⟨d.Arrow⟩

abbrev FreePaths := Quiver.FreeGroupoid d.Vertex

def freeVertex (a : d.Vertex) : d.FreePaths := (Quiver.FreeGroupoid.of d.Vertex).obj a

def freeX (e : XEdge (I := I) (r := r)) : d.freeVertex .v ⟶ d.freeVertex .w :=
  (Quiver.FreeGroupoid.of d.Vertex).map (.x e)
def freeL (e : d.LEdge) : d.freeVertex .o ⟶ d.freeVertex .v :=
  (Quiver.FreeGroupoid.of d.Vertex).map (.l e)
def freeR (e : d.REdge) : d.freeVertex .o ⟶ d.freeVertex .w :=
  (Quiver.FreeGroupoid.of d.Vertex).map (.rr e)

inductive FaceRelation : HomRel d.FreePaths
  | triangle (b : B) (i : (d.block b).labels) (u v : Fin r) :
      FaceRelation
        (d.freeL ⟨b,u,((d.block b).coordinates i).1 + (v.val : ZMod (d.block b).s)⟩ ≫
          d.freeX (i.val,u,v))
        (d.freeR ⟨b,v,((d.block b).coordinates i).2 + (u.val : ZMod (d.block b).t)⟩)

abbrev FundamentalGroupoid := CategoryTheory.Quotient d.FaceRelation

def vertex (a : d.Vertex) : d.FundamentalGroupoid :=
  (CategoryTheory.Quotient.functor d.FaceRelation).obj (d.freeVertex a)

def pathX (e : XEdge (I := I) (r := r)) : d.vertex .v ⟶ d.vertex .w :=
  (CategoryTheory.Quotient.functor d.FaceRelation).map (d.freeX e)
def pathL (e : d.LEdge) : d.vertex .o ⟶ d.vertex .v :=
  (CategoryTheory.Quotient.functor d.FaceRelation).map (d.freeL e)
def pathR (e : d.REdge) : d.vertex .o ⟶ d.vertex .w :=
  (CategoryTheory.Quotient.functor d.FaceRelation).map (d.freeR e)

theorem path_triangle (b : B) (i : (d.block b).labels) (u v : Fin r) :
    d.pathL ⟨b,u,((d.block b).coordinates i).1 + (v.val : ZMod (d.block b).s)⟩ ≫
        d.pathX (i.val,u,v) =
      d.pathR ⟨b,v,((d.block b).coordinates i).2 + (u.val : ZMod (d.block b).t)⟩ := by
  have h := CategoryTheory.Quotient.sound d.FaceRelation (FaceRelation.triangle (d := d) b i u v)
  simpa only [Functor.map_comp,pathX,pathL,pathR,vertex] using h

/-- Path-order multiplication is the opposite of Mathlib's End multiplication. -/
abbrev FundamentalGroup := (End (d.vertex .o))ᵐᵒᵖ

def treePathV : d.vertex .o ⟶ d.vertex .v := d.pathL ⟨d.baseBlock,d.baseIndex,0⟩
def treePathW : d.vertex .o ⟶ d.vertex .w := d.pathR ⟨d.baseBlock,d.baseIndex,0⟩

def basedEdge : d.Edge → d.FundamentalGroup
  | .inl e => MulOpposite.op (d.treePathV ≫ d.pathX e ≫ Groupoid.inv d.treePathW)
  | .inr (.inl e) => MulOpposite.op (d.pathL e ≫ Groupoid.inv d.treePathV)
  | .inr (.inr e) => MulOpposite.op (d.pathR e ≫ Groupoid.inv d.treePathW)

theorem based_triangle (b : B) (i : (d.block b).labels) (u v : Fin r) :
    (FreeGroup.lift d.basedEdge) (d.triangleWord b i u v) = 1 := by
  simp only [triangleWord,map_mul,map_inv,FreeGroup.lift_apply_of]
  apply (mul_inv_eq_one (G := d.FundamentalGroup)).mpr
  apply MulOpposite.unop_injective
  change (d.pathL _ ≫ Groupoid.inv d.treePathV) ≫
      (d.treePathV ≫ d.pathX _ ≫ Groupoid.inv d.treePathW) =
    d.pathR _ ≫ Groupoid.inv d.treePathW
  simp only [Category.assoc,Groupoid.inv_eq_inv,IsIso.inv_hom_id_assoc]
  rw [← Category.assoc,d.path_triangle]

theorem based_treeL : d.basedEdge d.treeL = 1 := by
  apply MulOpposite.unop_injective
  change d.treePathV ≫ Groupoid.inv d.treePathV = 𝟙 _
  simp

theorem based_treeR : d.basedEdge d.treeR = 1 := by
  apply MulOpposite.unop_injective
  change d.treePathW ≫ Groupoid.inv d.treePathW = 𝟙 _
  simp

def toFundamentalGroup : d.GroupType →* d.FundamentalGroup :=
  PresentedGroup.toGroup (f := d.basedEdge) (fun w hw => by
    rcases hw with ⟨b,i,u,v,rfl⟩ | rfl | rfl
    · exact d.based_triangle b i u v
    · simpa only [FreeGroup.lift_apply_of] using d.based_treeL
    · simpa only [FreeGroup.lift_apply_of] using d.based_treeR)

@[simp] theorem toFundamentalGroup_edge (e : d.Edge) :
    d.toFundamentalGroup (d.edge e) = d.basedEdge e := PresentedGroup.toGroup.of _

/-- Evaluation in the displayed group presentation, before quotienting faces. -/
def edgeEvaluation : d.Vertex ⥤q SingleObj d.GroupTypeᵐᵒᵖ where
  obj _ := SingleObj.star _
  map f := match f with
    | .x e => MulOpposite.op (d.edge (.inl e))
    | .l e => MulOpposite.op (d.edge (.inr (.inl e)))
    | .rr e => MulOpposite.op (d.edge (.inr (.inr e)))

def freeEvaluation : d.FreePaths ⥤ SingleObj d.GroupTypeᵐᵒᵖ :=
  Quiver.FreeGroupoid.lift d.edgeEvaluation

@[simp] theorem freeEvaluation_generator {a c : d.Vertex} (e : a ⟶ c) :
    d.freeEvaluation.map ((Quiver.FreeGroupoid.of d.Vertex).map e) =
      d.edgeEvaluation.map e := by
  exact Prefunctor.congr_hom (Quiver.FreeGroupoid.lift_spec d.edgeEvaluation) e

def evaluation : d.FundamentalGroupoid ⥤ SingleObj d.GroupTypeᵐᵒᵖ :=
  CategoryTheory.Quotient.lift d.FaceRelation d.freeEvaluation (by
    intro a c f g h
    cases h with
    | triangle b i u v =>
      simp only [freeL,freeX,freeR]
      apply MulOpposite.unop_injective
      change d.l b u _ * d.x i u v = d.rr b v _
      exact (eq_inv_mul_iff_mul_eq).mp (d.triangle_relation b i u v))

@[simp] theorem evaluation_pathX (e : XEdge (I := I) (r := r)) :
    d.evaluation.map (d.pathX e) = MulOpposite.op (d.edge (.inl e)) := by
  change d.freeEvaluation.map ((Quiver.FreeGroupoid.of d.Vertex).map (.x e)) = _
  exact d.freeEvaluation_generator (.x e)

@[simp] theorem evaluation_pathL (e : d.LEdge) :
    d.evaluation.map (d.pathL e) = MulOpposite.op (d.edge (.inr (.inl e))) := by
  change d.freeEvaluation.map ((Quiver.FreeGroupoid.of d.Vertex).map (.l e)) = _
  exact d.freeEvaluation_generator (.l e)

@[simp] theorem evaluation_pathR (e : d.REdge) :
    d.evaluation.map (d.pathR e) = MulOpposite.op (d.edge (.inr (.inr e))) := by
  change d.freeEvaluation.map ((Quiver.FreeGroupoid.of d.Vertex).map (.rr e)) = _
  exact d.freeEvaluation_generator (.rr e)

def fromFundamentalGroup : d.FundamentalGroup →* d.GroupType where
  toFun g := MulOpposite.unop (d.evaluation.map (MulOpposite.unop g))
  map_one' := by
    change MulOpposite.unop (d.evaluation.map (𝟙 _)) = 1
    rw [CategoryTheory.Functor.map_id]
    rfl
  map_mul' g h := by
    change MulOpposite.unop (d.evaluation.map (MulOpposite.unop g ≫ MulOpposite.unop h)) = _
    rw [Functor.map_comp]
    rfl

@[simp] theorem fromFundamentalGroup_basedEdge (e : d.Edge) :
    d.fromFundamentalGroup (d.basedEdge e) = d.edge e := by
  rcases e with e | e | e
  all_goals
    simp only [fromFundamentalGroup,basedEdge,MonoidHom.coe_mk,OneHom.coe_mk,
      MulOpposite.unop_op,Functor.map_comp,Groupoid.inv_eq_inv,Functor.map_inv]
  all_goals
    simp only [treePathV,treePathW,evaluation_pathX,evaluation_pathL,evaluation_pathR,
      SingleObj.comp_as_mul,SingleObj.inv_as_inv]
  · change d.edge d.treeL * (d.edge (.inl e) * (d.edge d.treeR)⁻¹) = _
    rw [d.treeL_eq_one,d.treeR_eq_one]
    simp
  · change d.edge (.inr (.inl e)) * (d.edge d.treeL)⁻¹ = _
    rw [d.treeL_eq_one]
    simp
  · change d.edge (.inr (.inr e)) * (d.edge d.treeR)⁻¹ = _
    rw [d.treeR_eq_one]
    simp

theorem from_to_fundamental : d.fromFundamentalGroup.comp d.toFundamentalGroup =
    MonoidHom.id d.GroupType := by
  apply PresentedGroup.ext
  intro e
  change d.fromFundamentalGroup (d.toFundamentalGroup (d.edge e)) = d.edge e
  rw [d.toFundamentalGroup_edge,d.fromFundamentalGroup_basedEdge]

theorem toFundamentalGroup_injective : Function.Injective d.toFundamentalGroup := by
  intro a b h
  have h' := congrArg d.fromFundamentalGroup h
  have hi (g : d.GroupType) : d.fromFundamentalGroup (d.toFundamentalGroup g) = g :=
    DFunLike.congr_fun d.from_to_fundamental g
  simpa only [hi] using h'

/-! A finite, purely combinatorial nullhomotopy follows from equality in the actual
fundamental groupoid. This is the starting point for the planar reduction,
not an assumed existence of a reduced diagram. -/
abbrev RawPaths := CategoryTheory.Paths (Quiver.Symmetrify d.Vertex)

def rawVertex (a : d.Vertex) : d.RawPaths := (CategoryTheory.Paths.of _).obj a

def rawX (e : XEdge (I := I) (r := r)) : d.rawVertex .v ⟶ d.rawVertex .w :=
  @Quiver.Hom.toPosPath d.Vertex inferInstance .v .w (.x e)
def rawL (e : d.LEdge) : d.rawVertex .o ⟶ d.rawVertex .v :=
  @Quiver.Hom.toPosPath d.Vertex inferInstance .o .v (.l e)
def rawR (e : d.REdge) : d.rawVertex .o ⟶ d.rawVertex .w :=
  @Quiver.Hom.toPosPath d.Vertex inferInstance .o .w (.rr e)

inductive RawMove : HomRel d.RawPaths
  | backtrack {a c : d.RawPaths} {p q : a ⟶ c} :
      Quiver.FreeGroupoid.redStep p q → RawMove p q
  | triangle (b : B) (i : (d.block b).labels) (u v : Fin r) :
      RawMove
        (d.rawL ⟨b,u,((d.block b).coordinates i).1 + (v.val : ZMod (d.block b).s)⟩ ≫
          d.rawX (i.val,u,v))
        (d.rawR ⟨b,v,((d.block b).coordinates i).2 + (u.val : ZMod (d.block b).t)⟩)

def RawHomotopic {a c : d.RawPaths} (p q : a ⟶ c) : Prop :=
  Relation.EqvGen (@HomRel.CompClosure _ _ d.RawMove a c) p q

abbrev RawQuotient := CategoryTheory.Quotient d.RawMove

def freeToRawQuotient : d.FreePaths ⥤ d.RawQuotient :=
  CategoryTheory.Quotient.lift Quiver.FreeGroupoid.redStep
    (CategoryTheory.Quotient.functor d.RawMove) (by
      intro a c p q h
      exact CategoryTheory.Quotient.sound d.RawMove (RawMove.backtrack h))

def fundamentalToRawQuotient : d.FundamentalGroupoid ⥤ d.RawQuotient :=
  CategoryTheory.Quotient.lift d.FaceRelation d.freeToRawQuotient (by
    intro a c p q h
    cases h with
    | triangle b i u v =>
      change (CategoryTheory.Quotient.functor d.RawMove).map
          (d.rawL _ ≫ d.rawX _) = (CategoryTheory.Quotient.functor d.RawMove).map (d.rawR _)
      exact CategoryTheory.Quotient.sound d.RawMove (RawMove.triangle b i u v))

def rawToFundamental : d.RawPaths ⥤ d.FundamentalGroupoid :=
  CategoryTheory.Quotient.functor Quiver.FreeGroupoid.redStep ⋙
    CategoryTheory.Quotient.functor d.FaceRelation

theorem rawMove_sound {a c : d.RawPaths} {p q : a ⟶ c} (h : d.RawMove p q) :
    d.rawToFundamental.map p = d.rawToFundamental.map q := by
  cases h with
  | backtrack h =>
    exact congrArg ((CategoryTheory.Quotient.functor d.FaceRelation).map)
      (CategoryTheory.Quotient.sound Quiver.FreeGroupoid.redStep h)
  | triangle b i u v =>
    exact CategoryTheory.Quotient.sound d.FaceRelation (FaceRelation.triangle b i u v)

def rawQuotientToFundamental : d.RawQuotient ⥤ d.FundamentalGroupoid :=
  CategoryTheory.Quotient.lift d.RawMove d.rawToFundamental (fun _ _ _ _ h => d.rawMove_sound h)

/-- Equality in the two-stage groupoid quotient is **exactly** a finite chain of
triangle moves and backtrack moves in arbitrary typed path contexts. -/
theorem raw_equality_iff {a c : d.RawPaths} (p q : a ⟶ c) :
    d.rawToFundamental.map p = d.rawToFundamental.map q ↔ d.RawHomotopic p q := by
  constructor
  · intro h
    have hh := congrArg (d.fundamentalToRawQuotient.map) h
    change (CategoryTheory.Quotient.functor d.RawMove).map p =
      (CategoryTheory.Quotient.functor d.RawMove).map q at hh
    exact Quot.eq.mp hh
  · intro h
    have hh : (CategoryTheory.Quotient.functor d.RawMove).map p =
        (CategoryTheory.Quotient.functor d.RawMove).map q := Quot.eq.mpr h
    exact congrArg (d.rawQuotientToFundamental.map) hh

def rawRectangle (i : I) (u u' v v' : Fin r) : d.rawVertex .v ⟶ d.rawVertex .v :=
  d.rawX (i,u,v) ≫ Quiver.Path.reverse (d.rawX (i,u',v)) ≫
    d.rawX (i,u',v') ≫ Quiver.Path.reverse (d.rawX (i,u,v'))

@[simp] theorem rawToFundamental_X (e : XEdge (I := I) (r := r)) :
    d.rawToFundamental.map (d.rawX e) = d.pathX e := rfl

@[simp] theorem rawToFundamental_reverse {a c : d.RawPaths} (p : a ⟶ c) :
    d.rawToFundamental.map (Quiver.Path.reverse p) =
      Groupoid.inv (d.rawToFundamental.map p) := rfl

private theorem based_rectangle_formula {C : Type*} [Groupoid C] {a b c : C}
    (A : a ⟶ b) (B : a ⟶ c) (f g h k : b ⟶ c) :
    (MulOpposite.op (End.of (A ≫ f ≫ Groupoid.inv B)) : (End a)ᵐᵒᵖ) *
        (MulOpposite.op (End.of (A ≫ g ≫ Groupoid.inv B)))⁻¹ *
        MulOpposite.op (End.of (A ≫ h ≫ Groupoid.inv B)) *
        (MulOpposite.op (End.of (A ≫ k ≫ Groupoid.inv B)))⁻¹ =
      MulOpposite.op (End.of (A ≫ (f ≫ Groupoid.inv g ≫ h ≫ Groupoid.inv k) ≫ Groupoid.inv A)) := by
  apply MulOpposite.unop_injective
  change (((A ≫ f ≫ Groupoid.inv B) ≫ Groupoid.inv (A ≫ g ≫ Groupoid.inv B)) ≫
    (A ≫ h ≫ Groupoid.inv B)) ≫ Groupoid.inv (A ≫ k ≫ Groupoid.inv B) = _
  simp [Groupoid.inv_eq_inv,Category.assoc]

/-- If a rectangular word vanished in the actual presentation, the unbased
four-edge rectangle would have a finite triangle/backtrack nullhomotopy. -/
theorem rawRectangle_nullhomotopic_of_eq_one (i : I) (u u' v v' : Fin r)
    (h : d.x i u v * (d.x i u' v)⁻¹ * d.x i u' v' * (d.x i u v')⁻¹ = 1) :
    d.RawHomotopic (d.rawRectangle i u u' v v') (𝟙 _) := by
  have hh := congrArg d.toFundamentalGroup h
  simp only [map_mul,map_inv,map_one,x,toFundamentalGroup_edge,basedEdge] at hh
  rw [based_rectangle_formula] at hh
  have hu := congrArg MulOpposite.unop hh
  change d.treePathV ≫
      (d.pathX (i,u,v) ≫ Groupoid.inv (d.pathX (i,u',v)) ≫
        d.pathX (i,u',v') ≫ Groupoid.inv (d.pathX (i,u,v'))) ≫
      Groupoid.inv d.treePathV = 𝟙 _ at hu
  apply (d.raw_equality_iff _ _).mp
  simp only [rawRectangle,Functor.map_comp,rawToFundamental_X,rawToFundamental_reverse,
    CategoryTheory.Functor.map_id]
  change d.pathX (i,u,v) ≫ Groupoid.inv (d.pathX (i,u',v)) ≫
    d.pathX (i,u',v') ≫ Groupoid.inv (d.pathX (i,u,v')) = 𝟙 (d.vertex .v)
  have hc := congrArg (fun f => Groupoid.inv d.treePathV ≫ f ≫ d.treePathV) hu
  simpa [Groupoid.inv_eq_inv,Category.assoc] using hc

end BlockPresentation
end Release075

end OAI
end
end

section
section
namespace OAI

namespace Release075
open scoped BigOperators
open Equiv

namespace PermCycles
attribute [local instance] Classical.propDecidable Classical.decEq
variable {A : Type*} [Fintype A]

abbrev Cycles (f : Perm A) := Quotient (Perm.SameCycle.setoid f)
noncomputable instance (f : Perm A) : Fintype (Cycles f) := Fintype.ofFinite _

def cl (f : Perm A) (a : A) : Cycles f := Quotient.mk _ a

omit [Fintype A] in
@[simp] theorem cl_eq_iff (f : Perm A) (a b : A) :
    cl f a = cl f b ↔ f.SameCycle a b := Quotient.eq

omit [Fintype A] in
theorem cl_surjective (f : Perm A) : Function.Surjective (cl f) := Quotient.mk_surjective

noncomputable def orbit (f : Perm A) (a : A) : Finset A := by
  classical
  exact Finset.univ.filter (f.SameCycle a)

@[simp] theorem mem_orbit (f : Perm A) (a b : A) : b ∈ orbit f a ↔ f.SameCycle a b := by
  classical
  simp [orbit]

theorem orbit_eq_image (f : Perm A) (a : A) {n : ℕ} (hn : 0 < n)
    (hp : (f^n) a = a) :
    orbit f a = Finset.univ.image (fun i : Fin n => (f^i.val) a) := by
  classical
  ext b
  rw [mem_orbit,Finset.mem_image]
  constructor
  · intro hb
    obtain ⟨k,hk⟩ := hb.exists_nat_pow_eq
    refine ⟨⟨k % n,Nat.mod_lt _ hn⟩,Finset.mem_univ _,?_⟩
    have hp' : Function.IsPeriodicPt (f : A → A) n a := by
      change f^[n] a = a
      simpa only [← Perm.coe_pow] using hp
    calc
      (f^(k%n)) a = f^[k%n] a := rfl
      _ = f^[k] a := hp'.iterate_mod_apply k
      _ = b := hk
  · rintro ⟨⟨k,hk⟩,_,rfl⟩
    exact (Perm.sameCycle_pow_right).mpr (Perm.SameCycle.refl f a)

theorem orbit_card_of_period (f : Perm A) (a : A) {n : ℕ} (hn : 0 < n)
    (hp : (f^n) a = a) (hinj : Function.Injective (fun i : Fin n => (f^i.val) a)) :
    (orbit f a).card = n := by
  classical
  rw [orbit_eq_image f a hn hp,Finset.card_image_of_injective _ hinj,Finset.card_univ,
    Fintype.card_fin]

noncomputable def fiberOrbitEquiv (f : Perm A) (a : A) :
    {b : A // cl f b = cl f a} ≃ (orbit f a) where
  toFun b := ⟨b, by simpa only [mem_orbit] using (cl_eq_iff f b a).mp b.property |>.symm⟩
  invFun b := ⟨b, (cl_eq_iff f b a).mpr ((mem_orbit f a b).mp b.property).symm⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem card_fiber (f : Perm A) (a : A) :
    Fintype.card {b : A // cl f b = cl f a} = (orbit f a).card := by
  classical
  simpa only [Fintype.card_coe] using Fintype.card_congr (fiberOrbitEquiv f a)

theorem sum_card_fibers (f : Perm A) :
    (∑ c : Cycles f, Fintype.card {a : A // cl f a = c}) = Fintype.card A := by
  classical
  rw [← Fintype.card_sigma]
  exact Fintype.card_congr (Equiv.sigmaFiberEquiv (cl f))

theorem card_eq_mul_cycles (f : Perm A) (n : ℕ)
    (h : ∀ a, (orbit f a).card = n) :
    Fintype.card A = n * Fintype.card (Cycles f) := by
  classical
  rw [← sum_card_fibers f]
  have hf (c : Cycles f) : Fintype.card {a : A // cl f a = c} = n := by
    obtain ⟨a,rfl⟩ := cl_surjective f c
    rw [card_fiber f a,h a]
  simp [hf,mul_comm]

/-- A fixed-point-free involution has precisely two darts in each edge orbit. -/
theorem orbit_card_involution (f : Perm A) (h : Function.Involutive f)
    (hne : ∀ a, f a ≠ a) (a : A) : (orbit f a).card = 2 := by
  apply orbit_card_of_period f a (by omega : 0 < 2)
  · simpa [pow_two] using h a
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [pow_one,pow_zero,eq_comm]

/-- A three-cycle orbit is counted with all corners, not merely its moved support. -/
theorem orbit_card_three (f : Perm A) (a : A) (hp : (f^3) a = a)
    (hne : f a ≠ a) : (orbit f a).card = 3 := by
  apply orbit_card_of_period f a (by omega : 0 < 3) hp
  have h2 : (f^2) a ≠ a := by
    intro he
    have hx := congrArg f he
    have hh : f ((f^2) a) = a := by simpa [pow_succ',Perm.mul_apply] using hp
    rw [hh] at hx
    exact hne hx.symm
  intro i j hij
  fin_cases i <;> fin_cases j
  · rfl
  · exact False.elim (hne (by simpa using hij.symm))
  · exact False.elim (h2 (by simpa using hij.symm))
  · exact False.elim (hne (by simpa using hij))
  · rfl
  · have hx : f a = f (f a) := by simpa [pow_two] using hij
    exact False.elim (hne (f.injective hx).symm)
  · exact False.elim (h2 (by simpa using hij))
  · have hx : f (f a) = f a := by simpa [pow_two] using hij
    exact False.elim (hne (f.injective hx))
  · rfl

theorem minimalPeriod_pos (f : Perm A) (a : A) :
    0 < Function.minimalPeriod (f : A → A) a :=
  Function.minimalPeriod_pos_of_mem_periodicPts (f.injective.mem_periodicPts a)

theorem orbit_card_eq_minimalPeriod (f : Perm A) (a : A) :
    (orbit f a).card = Function.minimalPeriod (f : A → A) a := by
  apply orbit_card_of_period f a (minimalPeriod_pos f a)
  · exact Function.iterate_minimalPeriod
  · intro i j hij
    apply Fin.ext
    exact Function.iterate_injOn_Iio_minimalPeriod i.isLt j.isLt hij

omit [Fintype A] in
@[simp] theorem cl_apply (f : Perm A) (a : A) : cl f (f a) = cl f a :=
  (cl_eq_iff f _ _).mpr ((Perm.sameCycle_apply_left).mpr (Perm.SameCycle.refl f a))

end PermCycles
end Release075

namespace Release075.PermCycles
open Equiv
attribute [local instance] Classical.propDecidable Classical.decEq
variable {A : Type*} [Fintype A]

/-- Any function invariant under one permutation step is constant on entire
cycles. This includes negative powers without any infinite search. -/
theorem invariant_sameCycle {B : Type*} (f : Perm A) (q : A → B)
    (h : ∀ x, q (f x) = q x) {x y : A} (hxy : f.SameCycle x y) : q x = q y := by
  obtain ⟨n,rfl⟩ := hxy.exists_nat_pow_eq
  clear hxy
  induction n with
  | zero => rfl
  | succ n ih =>
    simpa only [pow_succ',Perm.mul_apply,h] using ih

noncomputable def descend {B : Type*} (f : Perm A) (q : A → B)
    (h : ∀ x, q (f x) = q x) : Cycles f → B :=
  Quotient.lift q (fun _ _ hh => invariant_sameCycle f q h hh)

@[simp] theorem descend_cl {B : Type*} (f : Perm A) (q : A → B)
    (h : ∀ x, q (f x) = q x) (a : A) : descend f q h (cl f a) = q a := rfl

/-- Switching the two outgoing cycle destinations joins distinct cycles. This
is the elementary surgery used when gluing or cancelling planar picture arcs. -/
theorem swap_merges (f : Perm A) {a b : A} (hab : ¬ f.SameCycle a b) :
    (Equiv.swap a b * f).SameCycle a b := by
  let g := Equiv.swap a b * f
  let n := Function.minimalPeriod (f : A → A) a
  have hn : 0 < n := minimalPeriod_pos f a
  have ha : (f^n) a = a := Function.iterate_minimalPeriod
  have hnfix (k : ℕ) (hk : 0 < k) (hkn : k < n) : (f^k) a ≠ a := by
    intro he
    have hij := Function.iterate_injOn_Iio_minimalPeriod (f := (f : A → A))
      (x := a) hkn hn he
    omega
  have hnb (k : ℕ) : (f^k) a ≠ b := by
    intro he
    apply hab
    exact he ▸ ((Perm.sameCycle_pow_right).mpr (Perm.SameCycle.refl f a))
  have hm (k : ℕ) (hk : k < n) : (g^k) a = (f^k) a := by
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [pow_succ',Perm.mul_apply,ih (by omega),pow_succ',Perm.mul_apply]
      change Equiv.swap a b (f ((f^k) a)) = f ((f^k) a)
      apply Equiv.swap_apply_of_ne_of_ne
      · simpa only [pow_succ',Perm.mul_apply] using hnfix (k+1) (by omega) hk
      · simpa only [pow_succ',Perm.mul_apply] using hnb (k+1)
  have hg : (g^n) a = b := by
    obtain ⟨k,hk⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
    rw [hk,pow_succ',Perm.mul_apply,hm k (by omega)]
    change Equiv.swap a b (f ((f^k) a)) = b
    have hh : f ((f^k) a) = a := by simpa only [hk,pow_succ',Perm.mul_apply] using ha
    rw [hh,Equiv.swap_apply_left]
  exact ⟨(n : ℤ), by simpa only [zpow_natCast] using hg⟩

theorem old_cycles_of_swap_merged (f : Perm A) (a b : A)
    (hm : (Equiv.swap a b * f).SameCycle a b) {x y : A}
    (hxy : f.SameCycle x y) : (Equiv.swap a b * f).SameCycle x y := by
  let g := Equiv.swap a b * f
  have step (z : A) : cl g (f z) = cl g z := by
    have hz := cl_apply g z
    change cl g (Equiv.swap a b (f z)) = cl g z at hz
    by_cases ha : f z = a
    · rw [ha,Equiv.swap_apply_left] at hz
      rw [ha]
      exact ((cl_eq_iff g a b).mpr hm).trans hz
    by_cases hb : f z = b
    · rw [hb,Equiv.swap_apply_right] at hz
      rw [hb]
      exact ((cl_eq_iff g a b).mpr hm).symm.trans hz
    · simpa only [Equiv.swap_apply_of_ne_of_ne ha hb] using hz
  exact (cl_eq_iff g x y).mp (invariant_sameCycle f (cl g) step hxy)

theorem card_subtype_ne_add_one {C : Type*} [Fintype C] (c : C) :
    Nat.card {x : C // x ≠ c} + 1 = Fintype.card C := by
  classical
  have he : Finset.univ.filter (fun x : C => x ≠ c) = Finset.univ.erase c := by
    ext x
    simp
  rw [Nat.card_eq_fintype_card,Fintype.card_subtype,he]
  simpa only [Finset.card_univ] using Finset.card_erase_add_one (Finset.mem_univ c)

/-- Exact cycle count for merging two different cycles by one swap. Fixed points
are included in the count, unlike the support-cycle count in permutation sign. -/
theorem cycles_card_swap_of_not_same (f : Perm A) {a b : A} (hab : ¬ f.SameCycle a b) :
    Fintype.card (Cycles (Equiv.swap a b * f)) + 1 = Fintype.card (Cycles f) := by
  let g := Equiv.swap a b * f
  have hm : g.SameCycle a b := swap_merges f hab
  have hc : cl f a ≠ cl f b := fun h => hab ((cl_eq_iff f a b).mp h)
  let collapse : Cycles f → Cycles f := fun c => if c = cl f b then cl f a else c
  have ha : collapse (cl f a) = cl f a := by simp [collapse]
  have hb : collapse (cl f b) = cl f a := by simp [collapse]
  have hne (c : Cycles f) : collapse c ≠ cl f b := by
    by_cases h : c = cl f b
    · simpa only [collapse,ite_eq_left h] using hc
    · simpa only [collapse,ite_eq_right h] using h
  have hswap (z : A) : collapse (cl f (Equiv.swap a b z)) = collapse (cl f z) := by
    by_cases hza : z = a
    · subst z; simp only [Equiv.swap_apply_left,ha,hb]
    by_cases hzb : z = b
    · subst z; simp only [Equiv.swap_apply_right,ha,hb]
    · rw [Equiv.swap_apply_of_ne_of_ne hza hzb]
  let q : A → {c : Cycles f // c ≠ cl f b} := fun x => ⟨collapse (cl f x),hne _⟩
  have hq (x : A) : q (g x) = q x := by
    apply Subtype.ext
    change collapse (cl f (Equiv.swap a b (f x))) = collapse (cl f x)
    rw [hswap,cl_apply]
  let Q := descend g q hq
  let j : Cycles f → Cycles g := Quotient.lift (cl g) (by
    intro x y h
    exact (cl_eq_iff g x y).mpr (old_cycles_of_swap_merged f a b hm h))
  have hj : j (cl f a) = j (cl f b) := (cl_eq_iff g a b).mpr hm
  have hjc (c : Cycles f) : j (collapse c) = j c := by
    by_cases h : c = cl f b
    · simpa [collapse,h] using hj
    · simp only [collapse,ite_eq_right h]
  have hleft : Function.LeftInverse (fun c => j c.val) Q := by
    intro c
    induction c using Quotient.inductionOn with
    | h x => exact hjc (cl f x)
  have hsurj : Function.Surjective Q := by
    intro c
    obtain ⟨x,hx⟩ := cl_surjective f c.val
    refine ⟨cl g x,?_⟩
    apply Subtype.ext
    change collapse (cl f x) = c.val
    rw [hx]
    simp only [collapse,ite_eq_right c.property]
  have hcard := Fintype.card_congr (Equiv.ofBijective Q ⟨hleft.injective,hsurj⟩)
  rw [hcard]
  rw [← Nat.card_eq_fintype_card]
  exact card_subtype_ne_add_one (cl f b)

/-- Switching the destinations within one cycle cuts it into two. The proof
uses the initial orbit segment from `a` to `b`, rather than assuming an
unproved topological separation statement. -/
theorem swap_splits (f : Perm A) {a b : A} (hne : a ≠ b) (hab : f.SameCycle a b) :
    ¬ (Equiv.swap a b * f).SameCycle a b := by
  let n := Function.minimalPeriod (f : A → A) a
  have hn : 0 < n := minimalPeriod_pos f a
  have hp : (f^n) a = a := Function.iterate_minimalPeriod
  have hb : b ∈ orbit f a := (mem_orbit f a b).mpr hab
  rw [orbit_eq_image f a hn hp,Finset.mem_image] at hb
  obtain ⟨⟨k,hkn⟩,_,hk⟩ := hb
  have hk0 : 0 < k := by
    by_contra hh
    have hz : k = 0 := by omega
    simp only [hz,pow_zero,Perm.one_apply] at hk
    exact hne hk
  have hfb (j : ℕ) (hjk : j < k) : (f^j) a ≠ b := by
    intro hj
    have he : (f^j) a = (f^k) a := hj.trans hk.symm
    have hinj := Function.iterate_injOn_Iio_minimalPeriod (f := (f : A → A))
      (x := a) (by omega : j < n) hkn he
    omega
  have hfa (j : ℕ) (hj : 0 < j) (hjk : j < k) : (f^j) a ≠ a := by
    intro he
    have hinj := Function.iterate_injOn_Iio_minimalPeriod (f := (f : A → A))
      (x := a) (by omega : j < n) hn he
    omega
  let g := Equiv.swap a b * f
  have hgf (j : ℕ) (hjk : j < k) : (g^j) a = (f^j) a := by
    induction j with
    | zero => rfl
    | succ j ih =>
      rw [pow_succ',Perm.mul_apply,ih (by omega),pow_succ',Perm.mul_apply]
      change Equiv.swap a b (f ((f^j) a)) = f ((f^j) a)
      apply Equiv.swap_apply_of_ne_of_ne
      · simpa only [pow_succ',Perm.mul_apply] using hfa (j+1) (by omega) hjk
      · simpa only [pow_succ',Perm.mul_apply] using hfb (j+1) hjk
  have hgk : (g^k) a = a := by
    obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
    rw [pow_succ',Perm.mul_apply,hgf j (by omega)]
    change Equiv.swap a b (f ((f^j) a)) = a
    have hh : f ((f^j) a) = b := by simpa only [pow_succ',Perm.mul_apply] using hk
    rw [hh,Equiv.swap_apply_right]
  intro hgab
  have hmem := (mem_orbit g a b).mpr hgab
  rw [orbit_eq_image g a hk0 hgk,Finset.mem_image] at hmem
  obtain ⟨⟨j,hjk⟩,_,hj⟩ := hmem
  exact hfb j hjk ((hgf j hjk).symm.trans hj)

theorem cycles_card_swap_of_same (f : Perm A) {a b : A} (hne : a ≠ b)
    (hab : f.SameCycle a b) :
    Fintype.card (Cycles (Equiv.swap a b * f)) = Fintype.card (Cycles f) + 1 := by
  have h := cycles_card_swap_of_not_same (Equiv.swap a b * f) (swap_splits f hne hab)
  have he : Equiv.swap a b * (Equiv.swap a b * f) = f := by
    rw [← mul_assoc,Equiv.swap_mul_self,one_mul]
  rw [he] at h
  exact h.symm

end Release075.PermCycles

namespace Release075.PermCycles
open Equiv
attribute [local instance] Classical.propDecidable Classical.decEq
variable {A : Type*} [Fintype A]

/-- Join just two classes of a partition. -/
def joinPair (s : Setoid A) (a b : A) : Setoid A :=
  Relation.EqvGen.setoid (fun x y => s x y ∨ (x = a ∧ y = b))

omit [Fintype A] in
theorem le_joinPair (s : Setoid A) (a b : A) : s ≤ joinPair s a b :=
  fun x y h => Relation.EqvGen.rel x y (Or.inl h)

omit [Fintype A] in
theorem joinPair_rel (s : Setoid A) (a b : A) : joinPair s a b a b :=
  Relation.EqvGen.rel a b (Or.inr ⟨rfl,rfl⟩)

omit [Fintype A] in
theorem joinPair_le {s t : Setoid A} {a b : A} (h : s ≤ t) (hab : t a b) :
    joinPair s a b ≤ t := by
  apply Setoid.eqvGen_le
  intro x y hh
  rcases hh with hh | ⟨rfl,rfl⟩
  · exact h hh
  · exact hab

omit [Fintype A] in
theorem joinPair_eq_of_rel (s : Setoid A) {a b : A} (hab : s a b) :
    joinPair s a b = s := le_antisymm (joinPair_le le_rfl hab) (le_joinPair s a b)

/-- The exact loss of one component when two distinct classes are joined. -/
theorem card_joinPair (s : Setoid A) {a b : A} (hab : ¬ s a b) :
    Nat.card (Quotient (joinPair s a b)) + 1 = Nat.card (Quotient s) := by
  let : Fintype (Quotient s) := Fintype.ofFinite _
  let : Fintype (Quotient (joinPair s a b)) := Fintype.ofFinite _
  let c : A → Quotient s := Quotient.mk s
  have hc : c a ≠ c b := fun h => hab (Quotient.exact h)
  let collapse : Quotient s → Quotient s := fun v => if v = c b then c a else v
  have hne (v : Quotient s) : collapse v ≠ c b := by
    by_cases h : v = c b
    · simpa only [collapse,ite_eq_left h] using hc
    · simpa only [collapse,ite_eq_right h] using h
  let q : A → {v : Quotient s // v ≠ c b} := fun x => ⟨collapse (c x),hne _⟩
  have hq : joinPair s a b ≤ Setoid.ker q := by
    apply joinPair_le
    · intro x y h
      apply Subtype.ext
      change collapse (c x) = collapse (c y)
      rw [show c x = c y from Quotient.sound h]
    · apply Subtype.ext
      change collapse (c a) = collapse (c b)
      simp [collapse]
  let Q : Quotient (joinPair s a b) → {v : Quotient s // v ≠ c b} :=
    Quotient.lift q (fun _ _ h => hq h)
  let j : Quotient s → Quotient (joinPair s a b) := Setoid.map_of_le (le_joinPair s a b)
  have hj : j (c a) = j (c b) := Quotient.sound (joinPair_rel s a b)
  have hjc (v : Quotient s) : j (collapse v) = j v := by
    by_cases h : v = c b
    · simpa [collapse,h] using hj
    · simp only [collapse,ite_eq_right h]
  have hleft : Function.LeftInverse (fun v => j v.val) Q := by
    intro v
    induction v using Quotient.inductionOn with
    | h x => exact hjc (c x)
  have hsurj : Function.Surjective Q := by
    intro v
    obtain ⟨x,hx⟩ := Quotient.mk_surjective v.val
    refine ⟨Quotient.mk _ x,?_⟩
    apply Subtype.ext
    change collapse (c x) = v.val
    rw [show c x = v.val from hx]
    simp only [collapse,ite_eq_right v.property]
  rw [Nat.card_congr (Equiv.ofBijective Q ⟨hleft.injective,hsurj⟩)]
  simpa only [Nat.card_eq_fintype_card] using card_subtype_ne_add_one (c b)

/-- Components of the graph generated by two permutations; cycles of their
product are contained in these components. -/
abbrev components (f g : Perm A) : Setoid A :=
  Perm.SameCycle.setoid f ⊔ Perm.SameCycle.setoid g

noncomputable def cycleCount (f : Perm A) : ℕ := Nat.card (Cycles f)
noncomputable def componentCount (f g : Perm A) : ℕ := Nat.card (Quotient (components f g))

theorem sameCycle_le_of_step (f : Perm A) (s : Setoid A) (h : ∀ a, s a (f a)) :
    Perm.SameCycle.setoid f ≤ s := by
  intro x y hxy
  obtain ⟨n,rfl⟩ := hxy.exists_nat_pow_eq
  clear hxy
  induction n with
  | zero => exact s.refl x
  | succ n ih =>
    rw [pow_succ',Perm.mul_apply]
    exact s.trans ih (h _)

theorem sameCycle_mul_le_components (f g : Perm A) :
    Perm.SameCycle.setoid (f*g) ≤ components f g := by
  apply sameCycle_le_of_step
  intro a
  exact (components f g).trans
    ((show Perm.SameCycle.setoid g ≤ components f g from le_sup_right)
      ((Perm.sameCycle_apply_right).mpr (Perm.SameCycle.refl g a)))
    ((show Perm.SameCycle.setoid f ≤ components f g from le_sup_left)
      ((Perm.sameCycle_apply_right).mpr (Perm.SameCycle.refl f (g a))))

theorem components_swap_of_not_same (f g : Perm A) {a b : A}
    (hab : ¬ f.SameCycle a b) :
    components (Equiv.swap a b * f) g = joinPair (components f g) a b := by
  let t := joinPair (components f g) a b
  have oldle : components f g ≤ t := le_joinPair _ a b
  have hswap (z : A) : t z (Equiv.swap a b z) := by
    by_cases ha : z = a
    · subst z
      rw [Equiv.swap_apply_left]
      exact joinPair_rel _ a b
    by_cases hb : z = b
    · subst z
      rw [Equiv.swap_apply_right]
      exact t.symm (joinPair_rel _ a b)
    · rw [Equiv.swap_apply_of_ne_of_ne ha hb]
  apply le_antisymm
  · apply sup_le
    · apply sameCycle_le_of_step
      intro z
      exact t.trans (oldle ((show Perm.SameCycle.setoid f ≤ components f g from le_sup_left)
        ((Perm.sameCycle_apply_right).mpr (Perm.SameCycle.refl f z)))) (hswap (f z))
    · exact le_trans le_sup_right oldle
  · apply joinPair_le
    · apply sup_le
      · intro x y hxy
        exact (show Perm.SameCycle.setoid (Equiv.swap a b * f) ≤
          components (Equiv.swap a b * f) g from le_sup_left)
          (old_cycles_of_swap_merged f a b (swap_merges f hab) hxy)
      · exact le_sup_right
    · exact (show Perm.SameCycle.setoid (Equiv.swap a b * f) ≤
        components (Equiv.swap a b * f) g from le_sup_left) (swap_merges f hab)

theorem cycleCount_one : cycleCount (1 : Perm A) = Fintype.card A := by
  have hinj : Function.Injective (cl (1 : Perm A)) := by
    intro x y h
    exact Perm.sameCycle_one.mp ((cl_eq_iff 1 x y).mp h)
  have hh := Nat.card_congr (Equiv.ofBijective (cl (1 : Perm A)) ⟨hinj,cl_surjective 1⟩)
  simpa only [cycleCount,Nat.card_eq_fintype_card] using hh.symm

omit [Fintype A] in
theorem components_one (g : Perm A) : components 1 g = Perm.SameCycle.setoid g := by
  apply sup_eq_right.mpr
  intro x y h
  have he := Perm.sameCycle_one.mp h
  subst y
  exact Perm.SameCycle.refl g x

omit [Fintype A] in
theorem componentCount_one (g : Perm A) : componentCount 1 g = cycleCount g := by
  simp only [componentCount,components_one,cycleCount,Cycles]

theorem cycleCount_swap_of_not_same (f : Perm A) {a b : A} (hab : ¬ f.SameCycle a b) :
    cycleCount (Equiv.swap a b * f) + 1 = cycleCount f := by
  simpa only [cycleCount,Nat.card_eq_fintype_card] using cycles_card_swap_of_not_same f hab

theorem cycleCount_swap_le (f : Perm A) (a b : A) :
    cycleCount (Equiv.swap a b * f) ≤ cycleCount f + 1 := by
  by_cases h : a = b
  · subst b
    simp only [Equiv.swap_self]
    change cycleCount (1*f) ≤ cycleCount f + 1
    rw [one_mul]
    omega
  by_cases hab : f.SameCycle a b
  · have hs := cycles_card_swap_of_same f h hab
    simpa only [cycleCount,Nat.card_eq_fintype_card] using hs.le
  · have hs := cycleCount_swap_of_not_same f hab
    omega

/-- Euler's upper bound for an arbitrary oriented combinatorial map, allowing
multiple components and positive genus. No planarity theorem is assumed. -/
theorem euler_bound (f g : Perm A) :
    cycleCount f + cycleCount g + cycleCount (f*g) ≤
      Fintype.card A + 2 * componentCount f g := by
  generalize hn : f.support.card = n
  induction n using Nat.strong_induction_on generalizing f with
  | h n ih =>
    by_cases hf : f = 1
    · subst f
      simp only [cycleCount_one,one_mul,componentCount_one]
      omega
    have hex : ∃ x, f x ≠ x := by
      by_contra hh
      push Not at hh
      exact hf (Equiv.ext hh)
    obtain ⟨x,hx⟩ := hex
    let f' := Equiv.swap x (f x) * f
    have hsm : f.SameCycle x (f x) :=
      Perm.sameCycle_apply_right.mpr (Perm.SameCycle.refl f x)
    have hns : ¬ f'.SameCycle x (f x) := swap_splits f hx.symm hsm
    have hdec : f'.support.card < n := by
      rw [← hn]
      exact Perm.card_support_swap_mul hx
    have hi := ih _ hdec (f := f') rfl
    have hret : Equiv.swap x (f x) * f' = f := by
      dsimp [f']
      rw [← mul_assoc,Equiv.swap_mul_self,one_mul]
    have hc : cycleCount f + 1 = cycleCount f' := by
      have h := cycleCount_swap_of_not_same f' hns
      rwa [hret] at h
    have hj : components f g = joinPair (components f' g) x (f x) := by
      have h := components_swap_of_not_same f' g hns
      rwa [hret] at h
    have hprod : Equiv.swap x (f x) * (f'*g) = f*g := by rw [← mul_assoc,hret]
    by_cases hxy : components f' g x (f x)
    · have hcomp : componentCount f g = componentCount f' g := by
        simp only [componentCount,hj,joinPair_eq_of_rel _ hxy]
      have hp := cycleCount_swap_le (f'*g) x (f x)
      rw [hprod] at hp
      omega
    · have hcomp : componentCount f g + 1 = componentCount f' g := by
        simpa only [componentCount,hj] using card_joinPair (components f' g) hxy
      have hnp : ¬ (f'*g).SameCycle x (f x) := fun h =>
        hxy (sameCycle_mul_le_components f' g h)
      have hp := cycleCount_swap_of_not_same (f'*g) hnp
      rw [hprod] at hp
      omega

end Release075.PermCycles

end OAI
end
end

section
section
namespace OAI

namespace Release075.PermCycles
open Equiv
attribute [local instance] Classical.propDecidable Classical.decEq
variable {A : Type*} [Fintype A]

/-- A swap supported in other colors leaves this entire orbit unchanged. -/
theorem swap_sameCycle_away {C : Type*} (f : Perm A) (color : A → C)
    (hcolor : ∀ z, color (f z) = color z) (a b x y : A)
    (ha : color x ≠ color a) (hb : color x ≠ color b) :
    (Equiv.swap a b * f).SameCycle x y ↔ f.SameCycle x y := by
  have hp (n : ℕ) : color ((f^n) x) = color x := by
    induction n with
    | zero => rfl
    | succ n ih => simpa only [pow_succ',Perm.mul_apply,hcolor] using ih
  have he (n : ℕ) : ((Equiv.swap a b * f)^n) x = (f^n) x := by
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [pow_succ',Perm.mul_apply,ih,pow_succ',Perm.mul_apply]
      change Equiv.swap a b (f ((f^n) x)) = f ((f^n) x)
      apply Equiv.swap_apply_of_ne_of_ne
      · intro h
        exact ha (((hcolor _).trans (hp n)).symm.trans (congrArg color h))
      · intro h
        exact hb (((hcolor _).trans (hp n)).symm.trans (congrArg color h))
  constructor
  · intro h
    obtain ⟨n,hn⟩ := h.exists_nat_pow_eq
    exact ⟨(n : ℤ),by simpa only [zpow_natCast,he] using hn⟩
  · intro h
    obtain ⟨n,hn⟩ := h.exists_nat_pow_eq
    exact ⟨(n : ℤ),by simpa only [zpow_natCast,he] using hn⟩

omit [Fintype A] in
theorem swap_rel (s : Setoid A) {a b : A} (hab : s a b) (z : A) :
    s z (Equiv.swap a b z) := by
  by_cases ha : z = a
  · subst z
    simpa only [Equiv.swap_apply_left] using hab
  by_cases hb : z = b
  · subst z
    simpa only [Equiv.swap_apply_right] using s.symm hab
  · rw [Equiv.swap_apply_of_ne_of_ne ha hb]

theorem sameCycle_conjugate_swap_le (f : Perm A) (s : Setoid A) {a b : A}
    (hf : Perm.SameCycle.setoid f ≤ s) (hab : s a b) :
    Perm.SameCycle.setoid (Equiv.swap a b * f * Equiv.swap a b) ≤ s := by
  apply sameCycle_le_of_step
  intro z
  exact s.trans (swap_rel s hab z) (s.trans
    (hf (Perm.sameCycle_apply_right.mpr (Perm.SameCycle.refl f _)))
    (swap_rel s hab _))

/-- A local re-pairing can only split off one further component, provided its
slots belonged to the same old component. This includes reconnected slots. -/
theorem components_conjugate_swap (f g : Perm A) {a b : A}
    (hab : components f g a b) :
    components f g = joinPair (components (Equiv.swap a b * f * Equiv.swap a b) g) a b := by
  let f' := Equiv.swap a b * f * Equiv.swap a b
  have hret : Equiv.swap a b * f' * Equiv.swap a b = f := by
    dsimp [f']
    simp only [mul_assoc,Equiv.swap_mul_self,mul_one]
    rw [← mul_assoc,Equiv.swap_mul_self,one_mul]
  have hnew : components f' g ≤ components f g := by
    apply sup_le
    · exact sameCycle_conjugate_swap_le f _ le_sup_left hab
    · exact le_sup_right
  apply le_antisymm
  · let s := joinPair (components f' g) a b
    have hs : components f' g ≤ s := le_joinPair _ a b
    apply sup_le
    · have hh := sameCycle_conjugate_swap_le f' s (le_trans le_sup_left hs) (joinPair_rel _ a b)
      rwa [hret] at hh
    · exact le_trans le_sup_right hs
  · exact joinPair_le hnew hab

/-- Change the pairing on two edges, creating pairs `(a,b)` and `(reverse a,
reverse b)`. Formulated by conjugation, so involutivity and absence of fixed
points are inherited rather than assumed for the result. -/
noncomputable def rePair (reverse : Perm A) (a b : A) : Perm A :=
  Equiv.swap (reverse a) b * reverse * Equiv.swap (reverse a) b

omit [Fintype A] in
theorem rePair_vertex (reverse face : Perm A) (hi : Function.Involutive reverse) (a b : A) :
    rePair reverse a b * face =
      Equiv.swap (reverse a) b * Equiv.swap a (reverse b) * (reverse * face) := by
  unfold rePair
  rw [mul_assoc (Equiv.swap (reverse a) b) reverse (Equiv.swap (reverse a) b),
    Equiv.mul_swap_eq_swap_mul reverse (reverse a) b,hi a]
  simp only [mul_assoc]

omit [Fintype A] in
theorem cycleCount_conj (f t : Perm A) : cycleCount (t*f*t⁻¹) = cycleCount f := by
  let e : Cycles f ≃ Cycles (t*f*t⁻¹) := Quotient.congr t (by
    intro x y
    change f.SameCycle x y ↔ (t*f*t⁻¹).SameCycle (t x) (t y)
    simp [Perm.sameCycle_conj])
  exact (Nat.card_congr e).symm

omit [Fintype A] in
theorem cycleCount_rePair (reverse : Perm A) (a b : A) :
    cycleCount (rePair reverse a b) = cycleCount reverse := by
  simpa only [rePair,Equiv.swap_inv] using cycleCount_conj reverse (Equiv.swap (reverse a) b)

omit [Fintype A] in
theorem rePair_involutive (reverse : Perm A) (hi : Function.Involutive reverse) (a b : A) :
    Function.Involutive (rePair reverse a b) := by
  intro z
  simp only [rePair,Perm.mul_apply,Equiv.swap_apply_self]
  rw [hi,Equiv.swap_apply_self]

omit [Fintype A] in
theorem rePair_ne (reverse : Perm A) (hn : ∀ z, reverse z ≠ z) (a b z : A) :
    rePair reverse a b z ≠ z := by
  intro h
  have hh := congrArg (Equiv.swap (reverse a) b) h
  simp only [rePair,Perm.mul_apply,Equiv.swap_apply_self] at hh
  exact hn _ hh

omit [Fintype A] in
theorem color_swap {C : Type*} (color : A → C) {a b : A}
    (hab : color a = color b) (z : A) : color (Equiv.swap a b z) = color z := by
  by_cases ha : z = a
  · subst z
    simpa only [Equiv.swap_apply_left] using hab.symm
  by_cases hb : z = b
  · subst z
    simpa only [Equiv.swap_apply_right] using hab
  · rw [Equiv.swap_apply_of_ne_of_ne ha hb]

omit [Fintype A] in
theorem rePair_apply_a (reverse : Perm A) (hn : ∀ z, reverse z ≠ z) {a b : A}
    (hab : a ≠ b) : rePair reverse a b a = b := by
  simp only [rePair,Perm.mul_apply,
    Equiv.swap_apply_of_ne_of_ne (hn a).symm hab,Equiv.swap_apply_left]

omit [Fintype A] in
theorem rePair_apply_reverse_a (reverse : Perm A) (hn : ∀ z, reverse z ≠ z) {a b : A}
    (hab : a ≠ b) : rePair reverse a b (reverse a) = reverse b := by
  simp only [rePair,Perm.mul_apply,Equiv.swap_apply_left]
  exact Equiv.swap_apply_of_ne_of_ne (reverse.injective.ne hab.symm) (hn b)

/-- Genus zero for every connected component, expressed without an embedding or
an unproved Jordan-curve theorem. This uses the universal Euler upper bound. -/
def PlanarMap (reverse face : Perm A) : Prop :=
  cycleCount reverse + cycleCount face + cycleCount (reverse*face) =
    Fintype.card A + 2*componentCount reverse face

theorem planar_rePair {C : Type*} (reverse face : Perm A)
    (hi : Function.Involutive reverse) (hn : ∀ z, reverse z ≠ z)
    (color : A → C) (hcolor : ∀ z, color ((reverse*face) z) = color z)
    {a b : A} (hab : color a ≠ color b)
    (hleft : color (reverse a) = color b) (hright : color a = color (reverse b))
    (hpair : reverse a ≠ b) (hcycle : (reverse*face).SameCycle (reverse a) b)
    (hplanar : PlanarMap reverse face) : PlanarMap (rePair reverse a b) face := by
  let v := reverse * face
  let r' := rePair reverse a b
  let v' := r' * face
  let u := Equiv.swap a (reverse b) * v
  have hab' : a ≠ b := fun h => hab (congrArg color h)
  have hcountR : cycleCount r' = cycleCount reverse := cycleCount_rePair reverse a b
  have hv' : v' = Equiv.swap (reverse a) b * u := rePair_vertex reverse face hi a b
  have haway1 : color (reverse a) ≠ color a := by rw [hleft]; exact hab.symm
  have haway2 : color (reverse a) ≠ color (reverse b) := by rw [← hright]; exact haway1
  have hucycle : u.SameCycle (reverse a) b :=
    (swap_sameCycle_away v color hcolor a (reverse b) (reverse a) b haway1 haway2).mpr hcycle
  have hsplit : cycleCount v' = cycleCount u + 1 := by
    have h := cycles_card_swap_of_same u hpair hucycle
    simpa only [← hv',cycleCount,Nat.card_eq_fintype_card] using h
  have hnab : a ≠ reverse b := by
    intro h
    apply hpair
    rw [h,hi b]
  have hge : cycleCount v ≤ cycleCount v' := by
    by_cases hc : v.SameCycle a (reverse b)
    · have hh := cycles_card_swap_of_same v hnab hc
      have hh' : cycleCount u = cycleCount v + 1 := by
        simpa only [cycleCount,Nat.card_eq_fintype_card] using hh
      omega
    · have hh : cycleCount u + 1 = cycleCount v := cycleCount_swap_of_not_same v hc
      omega
  have hj : components reverse face = joinPair (components r' face) (reverse a) b :=
    components_conjugate_swap reverse face (sameCycle_mul_le_components reverse face hcycle)
  have hvcolor : ∀ z, color (v' z) = color z := by
    intro z
    rw [hv']
    change color (Equiv.swap (reverse a) b (Equiv.swap a (reverse b) (v z))) = color z
    rw [color_swap color hleft,color_swap color hright,hcolor]
  by_cases hc : components r' face (reverse a) b
  · have hcomp : componentCount reverse face = componentCount r' face := by
      simp only [componentCount,hj,joinPair_eq_of_rel _ hc]
    have hbound := euler_bound r' face
    dsimp [PlanarMap] at hplanar ⊢
    change cycleCount reverse + cycleCount face + cycleCount v =
      Fintype.card A + 2*componentCount reverse face at hplanar
    change cycleCount r' + cycleCount face + cycleCount v' ≤
      Fintype.card A + 2*componentCount r' face at hbound
    change cycleCount r' + cycleCount face + cycleCount v' =
      Fintype.card A + 2*componentCount r' face
    omega
  · have hcomp : componentCount reverse face + 1 = componentCount r' face := by
      simpa only [componentCount,hj] using card_joinPair (components r' face) hc
    have hrab : components r' face a b := by
      have hh : r'.SameCycle a (r' a) :=
        Perm.sameCycle_apply_right.mpr (Perm.SameCycle.refl r' a)
      rw [rePair_apply_a reverse hn hab'] at hh
      exact (show Perm.SameCycle.setoid r' ≤ components r' face from le_sup_left) hh
    have hrAB : components r' face (reverse a) (reverse b) := by
      have hh : r'.SameCycle (reverse a) (r' (reverse a)) :=
        Perm.sameCycle_apply_right.mpr (Perm.SameCycle.refl r' (reverse a))
      rw [rePair_apply_reverse_a reverse hn hab'] at hh
      exact (show Perm.SameCycle.setoid r' ≤ components r' face from le_sup_left) hh
    have hsep : ¬ v'.SameCycle a (reverse b) := by
      intro h
      have hh := sameCycle_mul_le_components r' face h
      exact hc ((components r' face).trans hrAB ((components r' face).trans
        ((components r' face).symm hh) hrab))
    have hawayA : color a ≠ color (reverse a) := by rw [hleft]; exact hab
    have hret1 : Equiv.swap (reverse a) b * v' = u := by
      rw [hv',← mul_assoc,Equiv.swap_mul_self,one_mul]
    have hns : ¬ u.SameCycle a (reverse b) := by
      rw [← hret1]
      exact fun h => hsep ((swap_sameCycle_away v' color hvcolor (reverse a) b a
        (reverse b) hawayA hab).mp h)
    have hret2 : Equiv.swap a (reverse b) * u = v := by
      dsimp [u]
      rw [← mul_assoc,Equiv.swap_mul_self,one_mul]
    have hmerge := cycleCount_swap_of_not_same u hns
    rw [hret2] at hmerge
    dsimp [PlanarMap] at hplanar ⊢
    change cycleCount reverse + cycleCount face + cycleCount v =
      Fintype.card A + 2*componentCount reverse face at hplanar
    change cycleCount r' + cycleCount face + cycleCount v' =
      Fintype.card A + 2*componentCount r' face
    omega

end Release075.PermCycles

namespace Release075.PermCycles
open Equiv
attribute [local instance] Classical.propDecidable Classical.decEq
variable {A : Type*} [Fintype A]

theorem invariant_pred_sameCycle (f : Perm A) (p : A → Prop)
    (hp : ∀ a, p (f a) ↔ p a) {a b : A} (h : f.SameCycle a b) : p a ↔ p b := by
  obtain ⟨n,rfl⟩ := h.exists_nat_pow_eq
  clear h
  induction n with
  | zero => rfl
  | succ n ih => simpa only [pow_succ',Perm.mul_apply,hp] using ih

/-- Decompose the number of classes along a union of equivalence classes. -/
theorem card_quotient_partition (s : Setoid A) (p : A → Prop)
    (hp : ∀ a b, s a b → (p a ↔ p b)) :
    Nat.card (Quotient s) = Nat.card (Quotient (s.comap (Subtype.val : {a // p a} → A))) +
      Nat.card (Quotient (s.comap (Subtype.val : {a // ¬p a} → A))) := by
  let q : Quotient s → Prop := Quotient.lift p (fun a b h => propext (hp a b h))
  let e₁ := Equiv.subtypeQuotientEquivQuotientSubtype p (s₁ := s)
    (s₂ := s.comap Subtype.val) q (fun _ => Iff.rfl) (fun _ _ => Iff.rfl)
  let e₂ := Equiv.subtypeQuotientEquivQuotientSubtype (fun a => ¬p a) (s₁ := s)
    (s₂ := s.comap Subtype.val) (fun a => ¬ q a) (fun _ => Iff.rfl) (fun _ _ => Iff.rfl)
  rw [← Nat.card_congr e₁,← Nat.card_congr e₂,← Nat.card_sum]
  exact (Nat.card_congr (Equiv.sumCompl q)).symm

theorem cycleCount_partition (f : Perm A) (p : A → Prop) (hp : ∀ a, p (f a) ↔ p a) :
    cycleCount f = cycleCount (f.subtypePerm hp) +
      cycleCount (f.subtypePerm (p := fun a => ¬p a) (fun a => not_congr (hp a))) := by
  have h := card_quotient_partition (Perm.SameCycle.setoid f) p
    (fun _ _ h => invariant_pred_sameCycle f p hp h)
  have hs : Perm.SameCycle.setoid (f.subtypePerm hp) =
      (Perm.SameCycle.setoid f).comap Subtype.val := by
    ext; exact Perm.sameCycle_subtypePerm
  have ht : Perm.SameCycle.setoid (f.subtypePerm (p := fun a => ¬p a) (fun a => not_congr (hp a))) =
      (Perm.SameCycle.setoid f).comap Subtype.val := by
    ext; exact Perm.sameCycle_subtypePerm
  simpa only [cycleCount,Cycles,hs,ht] using h

/-- Restriction to an invariant set commutes with connected components. -/
theorem components_subtype (f g : Perm A) (p : A → Prop)
    (hf : ∀ a, p (f a) ↔ p a) (hg : ∀ a, p (g a) ↔ p a) :
    components (f.subtypePerm hf) (g.subtypePerm hg) = (components f g).comap Subtype.val := by
  have hinv : ∀ a b, components f g a b → (p a ↔ p b) := by
    intro a b h
    have hh : components f g ≤ Setoid.ker p := by
      apply sup_le
      · intro a b h; exact propext (invariant_pred_sameCycle f p hf h)
      · intro a b h; exact propext (invariant_pred_sameCycle g p hg h)
    exact propext_iff.mp (hh h)
  apply le_antisymm
  · apply sup_le
    · intro x y h
      exact (show Perm.SameCycle.setoid f ≤ components f g from le_sup_left)
        (Perm.sameCycle_subtypePerm.mp h)
    · intro x y h
      exact (show Perm.SameCycle.setoid g ≤ components f g from le_sup_right)
        (Perm.sameCycle_subtypePerm.mp h)
  · intro x y h
    change components f g x.val y.val at h
    rw [components,Setoid.sup_def] at h
    have hh (a b : A) (h : Relation.EqvGen (⇑(Perm.SameCycle.setoid f) ⊔
        ⇑(Perm.SameCycle.setoid g)) a b) :
        ∀ ha : p a, ∀ hb : p b,
          components (f.subtypePerm hf) (g.subtypePerm hg) ⟨a,ha⟩ ⟨b,hb⟩ := by
      induction h with
      | rel a b h =>
        intro ha hb
        rcases h with h | h
        · exact (show Perm.SameCycle.setoid (f.subtypePerm hf) ≤ _ from le_sup_left)
            (Perm.sameCycle_subtypePerm.mpr h)
        · exact (show Perm.SameCycle.setoid (g.subtypePerm hg) ≤ _ from le_sup_right)
            (Perm.sameCycle_subtypePerm.mpr h)
      | refl a => intros; exact (components (f.subtypePerm hf) (g.subtypePerm hg)).refl _
      | symm a b h ih => intros; exact (components (f.subtypePerm hf) (g.subtypePerm hg)).symm (ih _ _)
      | trans a b c hab hbc ih₁ ih₂ =>
        intro ha hc
        have hab' : components f g a b := by rwa [components,Setoid.sup_def]
        have hb : p b := (hinv a b hab').mp ha
        exact (components (f.subtypePerm hf) (g.subtypePerm hg)).trans (ih₁ ha hb) (ih₂ hb hc)
    exact hh _ _ h x.property y.property

theorem componentCount_partition (f g : Perm A) (p : A → Prop)
    (hf : ∀ a, p (f a) ↔ p a) (hg : ∀ a, p (g a) ↔ p a) :
    componentCount f g = componentCount (f.subtypePerm hf) (g.subtypePerm hg) +
      componentCount (f.subtypePerm (p := fun a => ¬p a) (fun a => not_congr (hf a)))
        (g.subtypePerm (p := fun a => ¬p a) (fun a => not_congr (hg a))) := by
  have hh : components f g ≤ Setoid.ker p := by
    apply sup_le
    · intro a b h; exact propext (invariant_pred_sameCycle f p hf h)
    · intro a b h; exact propext (invariant_pred_sameCycle g p hg h)
  simpa only [componentCount,components_subtype] using
    card_quotient_partition (components f g) p (fun _ _ h => propext_iff.mp (hh h))

/-- Genus-zero is inherited by every union of connected components. -/
theorem PlanarMap.restrict {f g : Perm A} (h : PlanarMap f g) (p : A → Prop)
    (hf : ∀ a, p (f a) ↔ p a) (hg : ∀ a, p (g a) ↔ p a) :
    PlanarMap (f.subtypePerm hf) (g.subtypePerm hg) := by
  have hfg : ∀ a, p ((f*g) a) ↔ p a := fun a => (hf (g a)).trans (hg a)
  have hF := cycleCount_partition f p hf
  have hG := cycleCount_partition g p hg
  have hFG := cycleCount_partition (f*g) p hfg
  rw [← Perm.subtypePerm_mul f g hf hg,
    ← Perm.subtypePerm_mul (p := fun a => ¬p a) f g (fun a => not_congr (hf a))
      (fun a => not_congr (hg a))] at hFG
  have hC := componentCount_partition f g p hf hg
  have hA : Fintype.card A = Fintype.card {a // p a} + Fintype.card {a // ¬p a} := by
    simpa only [Fintype.card_sum] using (Fintype.card_congr (Equiv.sumCompl p)).symm
  have hB := euler_bound (f.subtypePerm (p := fun a => ¬p a) (fun a => not_congr (hf a)))
    (g.subtypePerm (p := fun a => ¬p a) (fun a => not_congr (hg a)))
  have hB' := euler_bound (f.subtypePerm hf) (g.subtypePerm hg)
  unfold PlanarMap at h ⊢
  omega

end Release075.PermCycles

namespace Release075.PermCycles
open Equiv
attribute [local instance] Classical.propDecidable Classical.decEq
variable {A B : Type*} [Fintype A] [Fintype B]

omit [Fintype A] [Fintype B] in
theorem pow_intertwine (f : Perm A) (g : Perm B) (e : A → B)
    (he : ∀ a, e (f a) = g (e a)) (n : ℕ) (a : A) :
    e ((f^n) a) = (g^n) (e a) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [pow_succ',Perm.mul_apply,he,ih,pow_succ',Perm.mul_apply]

theorem sameCycle_intertwine (f : Perm A) (g : Perm B) (e : A ≃ B)
    (he : ∀ a, e (f a) = g (e a)) (a b : A) : f.SameCycle a b ↔ g.SameCycle (e a) (e b) := by
  constructor
  · intro h
    obtain ⟨n,hn⟩ := h.exists_nat_pow_eq
    exact ⟨(n:ℤ),by rw [zpow_natCast,← pow_intertwine f g e he,hn]⟩
  · intro h
    obtain ⟨n,hn⟩ := h.exists_nat_pow_eq
    refine ⟨(n:ℤ),e.injective ?_⟩
    rwa [zpow_natCast,pow_intertwine f g e he]

theorem cycleCount_intertwine (f : Perm A) (g : Perm B) (e : A ≃ B)
    (he : ∀ a, e (f a) = g (e a)) : cycleCount f = cycleCount g :=
  Nat.card_congr (Quotient.congr e (sameCycle_intertwine f g e he))

omit [Fintype B] in
theorem components_map (f g : Perm A) (f' g' : Perm B) (e : A → B)
    (hf : ∀ a, e (f a) = f' (e a)) (hg : ∀ a, e (g a) = g' (e a)) :
    components f g ≤ (components f' g').comap e := by
  apply sup_le
  · apply sameCycle_le_of_step
    intro a
    change components f' g' (e a) (e (f a))
    rw [hf]
    exact (show Perm.SameCycle.setoid f' ≤ components f' g' from le_sup_left)
      (Perm.sameCycle_apply_right.mpr (Perm.SameCycle.refl f' _))
  · apply sameCycle_le_of_step
    intro a
    change components f' g' (e a) (e (g a))
    rw [hg]
    exact (show Perm.SameCycle.setoid g' ≤ components f' g' from le_sup_right)
      (Perm.sameCycle_apply_right.mpr (Perm.SameCycle.refl g' _))

theorem components_intertwine (f g : Perm A) (f' g' : Perm B) (e : A ≃ B)
    (hf : ∀ a, e (f a) = f' (e a)) (hg : ∀ a, e (g a) = g' (e a)) (a b : A) :
    components f g a b ↔ components f' g' (e a) (e b) := by
  constructor
  · exact fun h => components_map f g f' g' e hf hg h
  · intro h
    have hf' (b : B) : e.symm (f' b) = f (e.symm b) := by
      apply e.injective
      simp only [e.apply_symm_apply,hf]
    have hg' (b : B) : e.symm (g' b) = g (e.symm b) := by
      apply e.injective
      simp only [e.apply_symm_apply,hg]
    have hh := components_map f' g' f g e.symm hf' hg' h
    simpa only [Setoid.comap_rel,e.symm_apply_apply] using hh

theorem componentCount_intertwine (f g : Perm A) (f' g' : Perm B) (e : A ≃ B)
    (hf : ∀ a, e (f a) = f' (e a)) (hg : ∀ a, e (g a) = g' (e a)) :
    componentCount f g = componentCount f' g' :=
  Nat.card_congr (Quotient.congr e (components_intertwine f g f' g' e hf hg))

def leftPred : A ⊕ B → Prop := Sum.elim (fun _ => True) (fun _ => False)

def leftEquiv : {z : A ⊕ B // leftPred z} ≃ A where
  toFun z := match z with
    | ⟨.inl a,_⟩ => a
    | ⟨.inr _,h⟩ => False.elim h
  invFun a := ⟨.inl a,True.intro⟩
  left_inv z := by rcases z with ⟨a|b,h⟩; rfl; exact h.elim
  right_inv _ := rfl

def rightEquiv : {z : A ⊕ B // ¬leftPred z} ≃ B where
  toFun z := match z with
    | ⟨.inl _,h⟩ => False.elim (h True.intro)
    | ⟨.inr b,_⟩ => b
  invFun b := ⟨.inr b,not_false⟩
  left_inv z := by rcases z with ⟨a|b,h⟩; exact (h True.intro).elim; rfl
  right_inv _ := rfl

omit [Fintype A] [Fintype B] in
theorem leftPred_sumCongr (f : Perm A) (g : Perm B) (z : A ⊕ B) :
    leftPred ((f.sumCongr g) z) ↔ leftPred z := by cases z <;> rfl

omit [Fintype A] [Fintype B] in
theorem leftEquiv_intertwine (f : Perm A) (g : Perm B)
    (z : {z : A ⊕ B // leftPred z}) :
    leftEquiv ((f.sumCongr g).subtypePerm (leftPred_sumCongr f g) z) = f (leftEquiv z) := by
  rcases z with ⟨a|b,h⟩; rfl; exact h.elim

omit [Fintype A] [Fintype B] in
theorem rightEquiv_intertwine (f : Perm A) (g : Perm B)
    (z : {z : A ⊕ B // ¬ leftPred z}) :
    rightEquiv ((f.sumCongr g).subtypePerm (p := fun z => ¬leftPred z)
      (fun z => not_congr (leftPred_sumCongr f g z)) z) = g (rightEquiv z) := by
  rcases z with ⟨a|b,h⟩; exact (h True.intro).elim; rfl

theorem cycleCount_sum (f : Perm A) (g : Perm B) :
    cycleCount (f.sumCongr g) = cycleCount f + cycleCount g := by
  rw [cycleCount_partition (f.sumCongr g) leftPred (leftPred_sumCongr f g),
    cycleCount_intertwine _ f leftEquiv (leftEquiv_intertwine f g),
    cycleCount_intertwine _ g rightEquiv (rightEquiv_intertwine f g)]

theorem componentCount_sum (f g : Perm A) (f' g' : Perm B) :
    componentCount (f.sumCongr f') (g.sumCongr g') = componentCount f g + componentCount f' g' := by
  rw [componentCount_partition (f.sumCongr f') (g.sumCongr g') leftPred
    (leftPred_sumCongr f f') (leftPred_sumCongr g g'),
    componentCount_intertwine _ _ f g leftEquiv (leftEquiv_intertwine f f')
      (leftEquiv_intertwine g g'),
    componentCount_intertwine _ _ f' g' rightEquiv (rightEquiv_intertwine f f')
      (rightEquiv_intertwine g g')]

omit [Fintype A] [Fintype B] in
theorem sum_mul (f g : Perm A) (f' g' : Perm B) :
    (f.sumCongr f') * (g.sumCongr g') = (f*g).sumCongr (f'*g') := by
  ext z; cases z <;> rfl

theorem PlanarMap.sum {f g : Perm A} {f' g' : Perm B}
    (h : PlanarMap f g) (h' : PlanarMap f' g') :
    PlanarMap (f.sumCongr f') (g.sumCongr g') := by
  unfold PlanarMap at *
  rw [sum_mul,cycleCount_sum,cycleCount_sum,cycleCount_sum,componentCount_sum,Fintype.card_sum]
  omega

end Release075.PermCycles

end OAI
end
end

section
section
namespace OAI

namespace Release075.PermCycles
open Equiv
attribute [local instance] Classical.propDecidable Classical.decEq
variable {A : Type*} [Fintype A]

theorem cycleCount_mul_comm (f g : Perm A) : cycleCount (f*g) = cycleCount (g*f) :=
  cycleCount_intertwine (f*g) (g*f) g (fun _ => rfl)

omit [Fintype A] in
theorem components_comm (f g : Perm A) : components f g = components g f := sup_comm _ _

omit [Fintype A] in
theorem componentCount_comm (f g : Perm A) : componentCount f g = componentCount g f := by
  simp only [componentCount,components_comm f g]

theorem PlanarMap.symm {f g : Perm A} (h : PlanarMap f g) : PlanarMap g f := by
  simpa only [PlanarMap,cycleCount_mul_comm g f,componentCount_comm g f,
    Nat.add_comm (cycleCount g) (cycleCount f)] using h

/-- Cutting a cycle does not create positive genus. The component split is proved,
not presumed from a drawing. -/
theorem PlanarMap.swap_left {f g : Perm A} (hp : PlanarMap f g) {a b : A}
    (hab : f.SameCycle a b) : PlanarMap (Equiv.swap a b * f) g := by
  by_cases he : a = b
  · subst b
    rw [Equiv.swap_self]
    change PlanarMap (1*f) g
    rwa [one_mul]
  let f' := Equiv.swap a b * f
  have hc : cycleCount f' = cycleCount f + 1 := by
    simpa only [cycleCount,Nat.card_eq_fintype_card] using cycles_card_swap_of_same f he hab
  have hns : ¬ f'.SameCycle a b := swap_splits f he hab
  have hret : Equiv.swap a b * f' = f := by
    dsimp [f']; rw [←mul_assoc,Equiv.swap_mul_self,one_mul]
  have hj : components f g = joinPair (components f' g) a b := by
    have h := components_swap_of_not_same f' g hns
    rwa [hret] at h
  have hprod : Equiv.swap a b * (f'*g) = f*g := by rw [←mul_assoc,hret]
  by_cases hrel : components f' g a b
  · have hcomp : componentCount f g = componentCount f' g := by
      simp only [componentCount,hj,joinPair_eq_of_rel _ hrel]
    have hb := euler_bound f' g
    have hh := cycleCount_swap_le (f'*g) a b
    rw [hprod] at hh
    change PlanarMap f' g
    dsimp [PlanarMap] at hp ⊢
    omega
  · have hcomp : componentCount f g + 1 = componentCount f' g := by
      simpa only [componentCount,hj] using card_joinPair (components f' g) hrel
    have hh : cycleCount (f*g) + 1 = cycleCount (f'*g) := by
      have h := cycleCount_swap_of_not_same (f'*g)
        (fun h => hrel (sameCycle_mul_le_components f' g h))
      rwa [hprod] at h
    change PlanarMap f' g
    dsimp [PlanarMap] at hp ⊢
    omega

theorem PlanarMap.swap_right {f g : Perm A} (hp : PlanarMap f g) {a b : A}
    (hab : g.SameCycle a b) : PlanarMap f (Equiv.swap a b * g) :=
  (hp.symm.swap_left hab).symm

/-- Joining two separate planar components along a chosen cycle slot is planar. -/
theorem PlanarMap.join_left {f g : Perm A} (hp : PlanarMap f g) {a b : A}
    (hab : ¬ components f g a b) : PlanarMap (Equiv.swap a b * f) g := by
  have hnf : ¬ f.SameCycle a b := fun h => hab
    ((show Perm.SameCycle.setoid f ≤ components f g from le_sup_left) h)
  have hnp : ¬ (f*g).SameCycle a b := fun h => hab (sameCycle_mul_le_components f g h)
  have hc := cycleCount_swap_of_not_same f hnf
  have hd := cycleCount_swap_of_not_same (f*g) hnp
  have hj := components_swap_of_not_same f g hnf
  have hcomp : componentCount (Equiv.swap a b*f) g + 1 = componentCount f g := by
    simpa only [componentCount,hj] using card_joinPair (components f g) hab
  rw [←mul_assoc] at hd
  dsimp [PlanarMap] at hp ⊢
  omega

theorem PlanarMap.join_right {f g : Perm A} (hp : PlanarMap f g) {a b : A}
    (hab : ¬ components f g a b) : PlanarMap f (Equiv.swap a b * g) := by
  apply PlanarMap.symm
  apply hp.symm.join_left
  rwa [components_comm]

omit [Fintype A] in
theorem swap_color_preserving {C : Type*} (r f : Perm A) (color : A → C)
    (hc : ∀ a, color ((r*f) a) = color a) {a b : A}
    (hab : color (r a) = color (r b)) :
    ∀ z, color ((r*(Equiv.swap a b * f)) z) = color z := by
  intro z
  change (color ∘ r) (Equiv.swap a b (f z)) = color z
  rw [color_swap (color ∘ r) hab]
  exact hc z

end Release075.PermCycles

namespace Release075.PermCycles
open Equiv
attribute [local instance] Classical.propDecidable Classical.decEq
variable {A : Type*} [Fintype A]

omit [Fintype A] in
theorem rePair_color {C : Type*} (r f : Perm A) (hi : Function.Involutive r)
    (color : A → C) (hc : ∀ z, color ((r*f) z) = color z) {a b : A}
    (hl : color (r a) = color b) (hr : color a = color (r b)) :
    ∀ z, color ((rePair r a b*f) z) = color z := by
  intro z
  rw [rePair_vertex r f hi]
  change color (Equiv.swap (r a) b (Equiv.swap a (r b) ((r*f) z))) = color z
  rw [color_swap color hl,color_swap color hr,hc]

theorem planar_rePair_allow {C : Type*} (r f : Perm A)
    (hi : Function.Involutive r) (hn : ∀ z, r z ≠ z)
    (color : A → C) (hc : ∀ z, color ((r*f) z) = color z)
    {a b : A} (hab : color a ≠ color b)
    (hl : color (r a) = color b) (hr : color a = color (r b))
    (hcy : (r*f).SameCycle (r a) b) (hp : PlanarMap r f) :
    PlanarMap (rePair r a b) f := by
  by_cases h : r a = b
  · have hr : rePair r a b = r := by
      unfold rePair
      rw [h,Equiv.swap_self]
      change 1 * r * 1 = r
      simp
    rwa [hr]
  · exact planar_rePair r f hi hn color hc hab hl hr h hcy hp

omit [Fintype A] in
theorem rePair_other_edge (r : Perm A) (hi : Function.Involutive r) {a b z : A}
    (hza : z ≠ a) (hzb : z ≠ b) (hra : r z ≠ a) (hrb : r z ≠ b) :
    rePair r a b z = r z := by
  have hzra : z ≠ r a := by intro h; apply hra; rw [h,hi]
  simp only [rePair,Perm.mul_apply,Equiv.swap_apply_of_ne_of_ne hzra hzb,
    Equiv.swap_apply_of_ne_of_ne (r.injective.ne hza) hrb]

/-- Two oppositely oriented triangular faces. -/
noncomputable def dipoleFace : Perm (Fin 6) :=
  Equiv.swap 0 2 * Equiv.swap 0 1 * Equiv.swap 3 5 * Equiv.swap 3 4

@[simp] theorem dipoleFace_zero : dipoleFace 0 = 1 := by norm_num [dipoleFace,Perm.mul_apply,Equiv.swap_apply_def,Fin.ext_iff]
@[simp] theorem dipoleFace_one : dipoleFace 1 = 2 := by norm_num [dipoleFace,Perm.mul_apply,Equiv.swap_apply_def,Fin.ext_iff]
@[simp] theorem dipoleFace_two : dipoleFace 2 = 0 := by norm_num [dipoleFace,Perm.mul_apply,Equiv.swap_apply_def,Fin.ext_iff]
@[simp] theorem dipoleFace_three : dipoleFace 3 = 4 := by norm_num [dipoleFace,Perm.mul_apply,Equiv.swap_apply_def,Fin.ext_iff]
@[simp] theorem dipoleFace_four : dipoleFace 4 = 5 := by norm_num [dipoleFace,Perm.mul_apply,Equiv.swap_apply_def,Fin.ext_iff]
@[simp] theorem dipoleFace_five : dipoleFace 5 = 3 := by norm_num [dipoleFace,Perm.mul_apply,Equiv.swap_apply_def,Fin.ext_iff]

noncomputable def dipoleReverse : Perm (Fin 6) :=
  Equiv.swap 0 3 * Equiv.swap 1 5 * Equiv.swap 2 4

@[simp] theorem dipoleReverse_zero : dipoleReverse 0 = 3 := by norm_num [dipoleReverse,Perm.mul_apply,Equiv.swap_apply_def,Fin.ext_iff]
@[simp] theorem dipoleReverse_one : dipoleReverse 1 = 5 := by norm_num [dipoleReverse,Perm.mul_apply,Equiv.swap_apply_def,Fin.ext_iff]
@[simp] theorem dipoleReverse_two : dipoleReverse 2 = 4 := by norm_num [dipoleReverse,Perm.mul_apply,Equiv.swap_apply_def,Fin.ext_iff]
@[simp] theorem dipoleReverse_three : dipoleReverse 3 = 0 := by norm_num [dipoleReverse,Perm.mul_apply,Equiv.swap_apply_def,Fin.ext_iff]
@[simp] theorem dipoleReverse_four : dipoleReverse 4 = 2 := by norm_num [dipoleReverse,Perm.mul_apply,Equiv.swap_apply_def,Fin.ext_iff]
@[simp] theorem dipoleReverse_five : dipoleReverse 5 = 1 := by norm_num [dipoleReverse,Perm.mul_apply,Equiv.swap_apply_def,Fin.ext_iff]

theorem dipoleFace_count : cycleCount dipoleFace = 2 := by
  have h := card_eq_mul_cycles dipoleFace 3 (fun a => orbit_card_three dipoleFace a
    (by fin_cases a <;> norm_num [pow_succ',Perm.mul_apply,dipoleFace,Equiv.swap_apply_def,Fin.ext_iff])
    (by fin_cases a <;> norm_num [dipoleFace,Perm.mul_apply,Equiv.swap_apply_def,Fin.ext_iff]))
  have hh : (6:ℕ) = 3 * cycleCount dipoleFace := by
    simpa only [Fintype.card_fin,cycleCount,Nat.card_eq_fintype_card] using h
  omega

omit [Fintype A] in
theorem range_invariant {B : Type*} (r : Perm A) (t : Perm B) (e : B → A)
    (he : ∀ b, r (e b) = e (t b)) (a : A) : r a ∈ Set.range e ↔ a ∈ Set.range e := by
  constructor
  · rintro ⟨b,hb⟩
    refine ⟨t⁻¹ b,r.injective ?_⟩
    rw [he]
    change e (t (t.symm b)) = r a
    rwa [t.apply_symm_apply]
  · rintro ⟨b,rfl⟩
    exact ⟨t b,(he b).symm⟩

theorem components_rePair_le (r f : Perm A) {a b : A}
    (h : components r f (r a) b) : components (rePair r a b) f ≤ components r f := by
  rw [components_conjugate_swap r f h]
  exact le_joinPair _ _ _

/-- The actual two re-pairings isolate the cancellable six darts. This lemma
retains arbitrary outside reconnections; it does not postulate an empty outside
neighborhood. All unaffected face orbits, including the exterior, are unchanged. -/
theorem isolate_dipole {C : Type*} (r f : Perm A)
    (hi : Function.Involutive r) (hn : ∀ z, r z ≠ z)
    (color : A → C) (hc : ∀ z, color ((r*f) z) = color z)
    (e : Fin 6 ↪ A) (hf : ∀ j, f (e j) = e (dipoleFace j))
    (he : r (e 0) = e 3)
    (h10 : color (e 1) ≠ color (e 0)) (h21 : color (e 2) ≠ color (e 1))
    (h14 : color (e 1) = color (e 4)) (hp : PlanarMap r f) :
    ∃ r' : Perm A, Function.Involutive r' ∧ (∀ z, r' z ≠ z) ∧
      PlanarMap r' f ∧ (∀ z, color ((r'*f) z) = color z) ∧
      (∀ j, r' (e j) = e (dipoleReverse j)) ∧
      r' = rePair (rePair r (e 1) (e 5)) (e 2) (e 4) ∧
      components r' f ≤ components r f := by
  have h3 : r (e 3) = e 0 := by rw [← he,hi]
  have hne {i j : Fin 6} (h : i ≠ j) : e i ≠ e j := e.injective.ne h
  have hF0 : f (e 0) = e 1 := by simpa using hf 0
  have hF1 : f (e 1) = e 2 := by simpa using hf 1
  have hF2 : f (e 2) = e 0 := by simpa using hf 2
  have hF3 : f (e 3) = e 4 := by simpa using hf 3
  have hF4 : f (e 4) = e 5 := by simpa using hf 4
  have hF5 : f (e 5) = e 3 := by simpa using hf 5
  have h50 : color (e 5) = color (e 0) := by
    simpa only [Perm.mul_apply,hF5,h3] using (hc (e 5)).symm
  have h23 : color (e 2) = color (e 3) := by
    simpa only [Perm.mul_apply,hF2,he] using (hc (e 2)).symm
  have hl₁ : color (r (e 1)) = color (e 5) := by
    rw [h50]
    simpa only [Perm.mul_apply,hF0] using hc (e 0)
  have hr₁ : color (e 1) = color (r (e 5)) := by
    rw [h14]
    simpa only [Perm.mul_apply,hF4] using (hc (e 4)).symm
  have hcy₁ : (r*f).SameCycle (r (e 1)) (e 5) := by
    have hA : (r*f).SameCycle (e 0) (r (e 1)) := by
      simpa only [Perm.mul_apply,hF0] using
        (Perm.sameCycle_apply_right.mpr (Perm.SameCycle.refl (r*f) (e 0)))
    have hB : (r*f).SameCycle (e 5) (e 0) := by
      simpa only [Perm.mul_apply,hF5,h3] using
        (Perm.sameCycle_apply_right.mpr (Perm.SameCycle.refl (r*f) (e 5)))
    exact (hB.trans hA).symm
  let r₁ := rePair r (e 1) (e 5)
  have hi₁ : Function.Involutive r₁ := rePair_involutive r hi _ _
  have hn₁ : ∀ z, r₁ z ≠ z := rePair_ne r hn _ _
  have hp₁ : PlanarMap r₁ f := planar_rePair_allow r f hi hn color hc
    (by rwa [h50]) hl₁ hr₁ hcy₁ hp
  have hc₁ : ∀ z, color ((r₁*f) z) = color z := rePair_color r f hi color hc hl₁ hr₁
  have h01 : r₁ (e 0) = e 3 := by
    rw [rePair_other_edge r hi (hne (by decide)) (hne (by decide))
      (by rw [he]; exact hne (by decide)) (by rw [he]; exact hne (by decide)),he]
  have h31 : r₁ (e 3) = e 0 := by rw [← h01,hi₁]
  have h15 : r₁ (e 1) = e 5 := rePair_apply_a r hn (hne (by decide))
  have h51 : r₁ (e 5) = e 1 := by rw [← h15,hi₁]
  have hl₂ : color (r₁ (e 2)) = color (e 4) := by
    rw [← h14]
    simpa only [Perm.mul_apply,hF1] using hc₁ (e 1)
  have hr₂ : color (e 2) = color (r₁ (e 4)) := by
    rw [h23]
    simpa only [Perm.mul_apply,hF3] using (hc₁ (e 3)).symm
  have hcy₂ : (r₁*f).SameCycle (r₁ (e 2)) (e 4) := by
    have hA : (r₁*f).SameCycle (e 1) (r₁ (e 2)) := by
      simpa only [Perm.mul_apply,hF1] using
        (Perm.sameCycle_apply_right.mpr (Perm.SameCycle.refl (r₁*f) (e 1)))
    have hB : (r₁*f).SameCycle (e 4) (e 1) := by
      simpa only [Perm.mul_apply,hF4,h51] using
        (Perm.sameCycle_apply_right.mpr (Perm.SameCycle.refl (r₁*f) (e 4)))
    exact (hB.trans hA).symm
  let r₂ := rePair r₁ (e 2) (e 4)
  have hi₂ : Function.Involutive r₂ := rePair_involutive r₁ hi₁ _ _
  have hn₂ : ∀ z, r₂ z ≠ z := rePair_ne r₁ hn₁ _ _
  have hp₂ : PlanarMap r₂ f := planar_rePair_allow r₁ f hi₁ hn₁ color hc₁
    (by rwa [← h14]) hl₂ hr₂ hcy₂ hp₁
  have hc₂ : ∀ z, color ((r₂*f) z) = color z := rePair_color r₁ f hi₁ color hc₁ hl₂ hr₂
  have h02 : r₂ (e 0) = e 3 := by
    rw [rePair_other_edge r₁ hi₁ (hne (by decide)) (hne (by decide))
      (by rw [h01]; exact hne (by decide)) (by rw [h01]; exact hne (by decide)),h01]
  have h12 : r₂ (e 1) = e 5 := by
    rw [rePair_other_edge r₁ hi₁ (hne (by decide)) (hne (by decide))
      (by rw [h15]; exact hne (by decide)) (by rw [h15]; exact hne (by decide)),h15]
  have h24 : r₂ (e 2) = e 4 := rePair_apply_a r₁ hn₁ (hne (by decide))
  refine ⟨r₂,hi₂,hn₂,hp₂,hc₂,?_,rfl,?_⟩
  · intro j
    fin_cases j
    · simpa using h02
    · simpa using h12
    · simpa using h24
    · change r₂ (e 3) = e (dipoleReverse 3)
      simp only [dipoleReverse_three]; rw [← h02,hi₂]
    · change r₂ (e 4) = e (dipoleReverse 4)
      simp only [dipoleReverse_four]; rw [← h24,hi₂]
    · change r₂ (e 5) = e (dipoleReverse 5)
      simp only [dipoleReverse_five]; rw [← h12,hi₂]
  · exact (components_rePair_le r₁ f (sameCycle_mul_le_components r₁ f hcy₂)).trans
      (components_rePair_le r f (sameCycle_mul_le_components r f hcy₁))

end Release075.PermCycles

namespace Release075.PermCycles
open Equiv
attribute [local instance] Classical.propDecidable Classical.decEq
variable {A B : Type*} [Fintype A] [Fintype B]

/-- Deleting an invariant finite family of face cycles has its exact effect on
area; no ambient topological disk is presumed in the count. -/
theorem cycleCount_delete_range (f : Perm A) (t : Perm B) (e : B ↪ A)
    (he : ∀ b, f (e b) = e (t b)) :
    cycleCount f = cycleCount t + cycleCount
      (f.subtypePerm (p := fun a => a ∉ Set.range e)
        (fun a => not_congr (range_invariant f t e he a))) := by
  have h := cycleCount_partition f (fun a => a ∈ Set.range e) (range_invariant f t e he)
  have hh : cycleCount t = cycleCount (f.subtypePerm (range_invariant f t e he)) := by
    apply cycleCount_intertwine t _ (Equiv.ofInjective e e.injective)
    intro b
    apply Subtype.ext
    exact (he b).symm
  rw [← hh] at h
  exact h

omit [Fintype A] [Fintype B] in
theorem rePair_labels {E : Type*} (r : Perm A) (label : A → E) (flip : E → E)
    (hr : ∀ a, label (r a) = flip (label a)) {a b : A}
    (hl : label (r a) = label b) :
    ∀ z, label (rePair r a b z) = flip (label z) := by
  intro z
  simp only [rePair,Perm.mul_apply,color_swap label hl,hr]

omit [Fintype B] in
theorem cancel_dipole {C : Type*} (r f : Perm A)
    (hi : Function.Involutive r) (hn : ∀ z, r z ≠ z)
    (color : A → C) (hc : ∀ z, color ((r*f) z) = color z)
    (e : Fin 6 ↪ A) (hf : ∀ j, f (e j) = e (dipoleFace j))
    (he : r (e 0) = e 3)
    (h10 : color (e 1) ≠ color (e 0)) (h21 : color (e 2) ≠ color (e 1))
    (h14 : color (e 1) = color (e 4)) (hp : PlanarMap r f) :
    ∃ (r' : Perm A) (hr : ∀ a, (r' a ∉ Set.range e) ↔ (a ∉ Set.range e)),
      Function.Involutive (r'.subtypePerm (p := fun a => a ∉ Set.range e) hr) ∧
      (∀ z, r'.subtypePerm (p := fun a => a ∉ Set.range e) hr z ≠ z) ∧
      PlanarMap (r'.subtypePerm (p := fun a => a ∉ Set.range e) hr)
        (f.subtypePerm (p := fun a => a ∉ Set.range e)
          (fun a => not_congr (range_invariant f dipoleFace e hf a))) ∧
      cycleCount (f.subtypePerm (p := fun a => a ∉ Set.range e)
        (fun a => not_congr (range_invariant f dipoleFace e hf a))) + 2 = cycleCount f := by
  obtain ⟨r',hi',hn',hp',hc',he',_,_⟩ := isolate_dipole r f hi hn color hc e hf he h10 h21 h14 hp
  let hr : ∀ a, (r' a ∉ Set.range e) ↔ (a ∉ Set.range e) :=
    fun a => not_congr (range_invariant r' dipoleReverse e he' a)
  refine ⟨r',hr,?_,?_,?_,?_⟩
  · intro a
    apply Subtype.ext
    exact hi' a.val
  · intro a h
    exact hn' a.val (congrArg Subtype.val h)
  · simpa only [PlanarMap, ← Nat.card_eq_fintype_card] using
      hp'.restrict (fun a => a ∉ Set.range e) hr
        (fun a => not_congr (range_invariant f dipoleFace e hf a))
  · have h := cycleCount_delete_range f dipoleFace e hf
    rw [dipoleFace_count] at h
    omega

end Release075.PermCycles

namespace Release075
open Equiv
attribute [local instance] Classical.propDecidable Classical.decEq
variable {A : Type*}

theorem formPerm_append_cons (x y : A) (xs ys : List A) :
    (x :: xs ++ y :: ys).formPerm = (x :: xs).formPerm *
      Equiv.swap ((x::xs).getLast (by simp)) y * (y::ys).formPerm := by
  induction xs generalizing x with
  | nil => simp only [List.cons_append,List.nil_append,List.formPerm_cons_cons,List.formPerm_singleton,
      List.getLast_singleton,one_mul]
  | cons z xs ih =>
    simpa only [List.cons_append,List.formPerm_cons_cons,List.getLast_cons_cons,mul_assoc] using
      congrArg (fun p : Perm A => Equiv.swap x z * p) (ih z)

theorem formPerm_concat (x y : A) (xs ys : List A) (hy : y ∉ x::xs) :
    (x :: xs ++ y :: ys).formPerm =
      Equiv.swap x y * ((x::xs).formPerm * (y::ys).formPerm) := by
  rw [formPerm_append_cons,Equiv.mul_swap_eq_swap_mul,
    List.formPerm_apply_getLast,List.formPerm_apply_of_notMem hy,mul_assoc]

/-- A specified exterior cycle, including the empty boundary. Its entries are
incidences (darts), not necessarily distinct vertices or geometric edges. -/
def IsBoundary (f : Perm A) (l : List A) : Prop :=
  l.Nodup ∧ ∀ a ∈ l, f a = l.formPerm a

theorem IsBoundary.mem_iff {f : Perm A} {l : List A} (h : IsBoundary f l) (a : A) :
    f a ∈ l ↔ a ∈ l := by
  constructor
  · intro ha
    let b := l.formPerm.symm (f a)
    have hb : b ∈ l := by
      apply List.mem_of_formPerm_apply_mem (l := l)
      simpa only [b,Equiv.apply_symm_apply] using ha
    have he : f b = f a := by rw [h.2 b hb]; exact l.formPerm.apply_symm_apply _
    rwa [f.injective he] at hb
  · intro ha
    rw [h.2 a ha]
    exact List.formPerm_apply_mem_of_mem ha

theorem IsBoundary.not_mem_iff {f : Perm A} {l : List A} (h : IsBoundary f l) (a : A) :
    f a ∉ l ↔ a ∉ l := not_congr (h.mem_iff a)

theorem formPerm_embedding {B : Type*} (e : A ↪ B) (l : List A) (a : A) :
    (l.map e).formPerm (e a) = e (l.formPerm a) := by
  induction l using List.twoStepInduction with
  | nil => rfl
  | singleton x => rfl
  | cons_cons x y xs _ ih =>
    change Equiv.swap (e x) (e y) (((y::xs).map e).formPerm (e a)) =
      e (Equiv.swap x y ((y::xs).formPerm a))
    rw [ih y,e.injective.swap_apply]

theorem IsBoundary.conjugate {B : Type*} {f : Perm A} {g : Perm B} {l : List A}
    (h : IsBoundary f l) (e : A ↪ B) (he : ∀ a, g (e a) = e (f a)) :
    IsBoundary g (l.map e) := by
  refine ⟨h.1.map e.injective,?_⟩
  intro b hb
  obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hb
  rw [he,h.2 a ha]
  exact (formPerm_embedding e l a).symm

theorem IsBoundary.rotate {f : Perm A} {l : List A} (h : IsBoundary f l) (n : ℕ) :
    IsBoundary f (l.rotate n) := by
  refine ⟨List.nodup_rotate.mpr h.1,?_⟩
  intro a ha
  rw [List.formPerm_rotate l h.1 n]
  exact h.2 a (List.mem_rotate.mp ha)

end Release075

namespace Release075.PermCycles
open Equiv
attribute [local instance] Classical.propDecidable Classical.decEq
variable {A : Type*} [Fintype A]

theorem components_split_right_le (r f : Perm A) {a b : A}
    (h : f.SameCycle a b) : components r (Equiv.swap a b*f) ≤ components r f := by
  by_cases he : a = b
  · subst b
    simp only [Equiv.swap_self]
    change components r (1*f) ≤ components r f
    rw [one_mul]
  have hn := swap_splits f he h
  have hj := components_swap_of_not_same (Equiv.swap a b*f) r hn
  have hr : Equiv.swap a b * (Equiv.swap a b*f) = f := by
    rw [←mul_assoc,Equiv.swap_mul_self,one_mul]
  rw [hr,components_comm f r,components_comm (Equiv.swap a b*f) r] at hj
  rw [hj]
  exact le_joinPair _ a b

/-- Fold two consecutive inverse boundary incidences. Darts are first paired,
then split off as their own isolated tree component. The surviving outside word
is unchanged; no disjointness of the former outside partners is assumed. -/
theorem fold_pair {C E : Type*} (r f : Perm A)
    (hi : Function.Involutive r) (hn : ∀ a, r a ≠ a)
    (label : A → E) (flip : E → E) (hflip : Function.Involutive flip)
    (color : E → C) (hedge : ∀ e, color e ≠ color (flip e))
    (hl : ∀ a, label (r a) = flip (label a))
    (hc : ∀ a, color (label ((r*f) a)) = color (label a))
    (hp : PlanarMap r f) {a b : A} (hab : a ≠ b)
    (hf : f b = a) (he : label a = flip (label b)) :
    ∃ r' f' : Perm A,
      Function.Involutive r' ∧ (∀ z, r' z ≠ z) ∧ PlanarMap r' f' ∧
      (∀ z, label (r' z) = flip (label z)) ∧
      (∀ z, color (label ((r'*f') z)) = color (label z)) ∧
      r' a = b ∧ r' b = a ∧ f' a = b ∧ f' b = a ∧
      components r' f' ≤ components r f ∧
      (∀ z, f z ≠ b → f z ≠ f a → f' z = f z) ∧
      f' = Equiv.swap b (f a) * f := by
  have hleft : (color ∘ label) (r a) = (color ∘ label) b := by
    dsimp; rw [hl,he,hflip]
  have hright : (color ∘ label) a = (color ∘ label) (r b) := by
    dsimp; rw [hl,he]
  have hcol : (color ∘ label) a ≠ (color ∘ label) b := by
    dsimp; rw [he]; exact (hedge (label b)).symm
  have hcy : (r*f).SameCycle (r a) b := by
    have h := Perm.sameCycle_apply_right.mpr (Perm.SameCycle.refl (r*f) b)
    simpa only [Perm.mul_apply,hf] using h.symm
  let r' := rePair r a b
  have hi' := rePair_involutive r hi a b
  have hn' := rePair_ne r hn a b
  have hp' : PlanarMap r' f := planar_rePair_allow r f hi hn (color ∘ label) hc
    hcol hleft hright hcy hp
  have hc' : ∀ z, color (label ((r'*f) z)) = color (label z) :=
    rePair_color r f hi (color ∘ label) hc hleft hright
  have ha : r' a = b := rePair_apply_a r hn hab
  have hb : r' b = a := by rw [←ha,hi']
  have hlabel : ∀ z, label (r' z) = flip (label z) := rePair_labels r label flip hl
    (by rw [hl,he,hflip])
  let f' := Equiv.swap b (f a) * f
  have hcyf : f.SameCycle b (f a) := by
    have hh : f.SameCycle b a := by
      simpa only [hf] using (Perm.sameCycle_apply_right.mpr (Perm.SameCycle.refl f b))
    exact Perm.sameCycle_apply_right.mpr hh
  have hp'' : PlanarMap r' f' := hp'.swap_right hcyf
  have ha' : f' a = b := Equiv.swap_apply_right b (f a)
  have hb' : f' b = a := by
    change Equiv.swap b (f a) (f b) = a
    rw [hf,Equiv.swap_apply_of_ne_of_ne hab]
    intro h
    have := f.injective (h.symm.trans hf.symm)
    exact hab this
  have hswap : color (label (r' b)) = color (label (r' (f a))) := by
    rw [hb]
    exact (hc' a).symm
  have hmono : components r' f' ≤ components r f :=
    (components_split_right_le r' f hcyf).trans
      (components_rePair_le r f (sameCycle_mul_le_components r f hcy))
  refine ⟨r',f',hi',hn',hp'',hlabel,
    swap_color_preserving r' f (color ∘ label) hc' hswap,ha,hb,ha',hb',hmono,?_,rfl⟩
  intro z hz₁ hz₂
  exact Equiv.swap_apply_of_ne_of_ne hz₁ hz₂

end Release075.PermCycles

end OAI
end
end

section
section
namespace OAI

namespace Release075
open Equiv PermCycles
attribute [local instance] Classical.propDecidable Classical.decEq

/-- A finite genus-zero map with a prescribed exterior walk. Other components
are allowed but ignored; only the component meeting the boundary must be filled.
This handles components detached by folds, spurs, and empty boundary words. -/
structure TriangleFilling {E V : Type} (flip : E → E) (color : E → V)
    (face : E → E → E → Prop) (w : List E) where
  Dart : Type
  [finiteDart : Fintype Dart]
  reverse : Perm Dart
  next : Perm Dart
  reverse_involutive : Function.Involutive reverse
  reverse_ne : ∀ d, reverse d ≠ d
  label : Dart → E
  reverse_label : ∀ d, label (reverse d) = flip (label d)
  color_next : ∀ d, color (label ((reverse*next) d)) = color (label d)
  planar : PlanarMap reverse next
  boundary : List Dart
  boundary_cycle : IsBoundary next boundary
  boundary_word : boundary.map label = w
  triangular : ∀ d, (∃ b ∈ boundary, components reverse next d b) → d ∉ boundary →
    (next^3) d = d ∧ next d ≠ d ∧ face (label d) (label (next d)) (label ((next^2) d))

attribute [instance] TriangleFilling.finiteDart

namespace TriangleFilling
variable {E V : Type} {flip : E → E} {color : E → V} {face : E → E → E → Prop}

noncomputable def empty : TriangleFilling flip color face [] where
  Dart := Fin 0
  reverse := 1
  next := 1
  reverse_involutive := fun _ => rfl
  reverse_ne := by intro d; exact Fin.elim0 d
  label := Fin.elim0
  reverse_label := by intro d; exact Fin.elim0 d
  color_next := by intro d; exact Fin.elim0 d
  planar := by
    simp only [PlanarMap,one_mul,cycleCount_one,componentCount_one,Fintype.card_fin]
  boundary := []
  boundary_cycle := ⟨by simp,by simp⟩
  boundary_word := rfl
  triangular := by intro d; exact Fin.elim0 d

noncomputable def rotate {w : List E} (D : TriangleFilling flip color face w) (n : ℕ) :
    TriangleFilling flip color face (w.rotate n) where
  Dart := D.Dart
  reverse := D.reverse
  next := D.next
  reverse_involutive := D.reverse_involutive
  reverse_ne := D.reverse_ne
  label := D.label
  reverse_label := D.reverse_label
  color_next := D.color_next
  planar := D.planar
  boundary := D.boundary.rotate n
  boundary_cycle := D.boundary_cycle.rotate n
  boundary_word := by rw [List.map_rotate,D.boundary_word]
  triangular := by
    intro d hd hn
    apply D.triangular d
    · obtain ⟨b,hb,hdb⟩ := hd
      exact ⟨b,List.mem_rotate.mp hb,hdb⟩
    · simpa only [List.mem_rotate] using hn

end TriangleFilling
end Release075

namespace Release075.PermCycles
open Equiv
attribute [local instance] Classical.propDecidable Classical.decEq
variable {A : Type*} [Fintype A]

theorem PlanarMap.involution (r : Perm A) (h : Function.Involutive r) : PlanarMap r r := by
  have hr : r*r = 1 := Equiv.ext h
  have hc : componentCount r r = cycleCount r := by
    simp only [componentCount,components,sup_idem,cycleCount,Cycles]
  simp only [PlanarMap,hr,cycleCount_one,hc]
  omega

end Release075.PermCycles

namespace Release075.TriangleFilling
open Equiv PermCycles
attribute [local instance] Classical.propDecidable Classical.decEq
variable {E V : Type} {flip : E → E} {color : E → V} {face : E → E → E → Prop}

noncomputable def backtrack (hflip : Function.Involutive flip) (e : E) :
    TriangleFilling flip color face [e,flip e] where
  Dart := Fin 2
  reverse := Equiv.swap 0 1
  next := Equiv.swap 0 1
  reverse_involutive := Equiv.swap_apply_self 0 1
  reverse_ne := by intro a; fin_cases a <;> norm_num [Equiv.swap_apply_def,Fin.ext_iff]
  label := fun d => if d = 0 then e else flip e
  reverse_label := by
    intro d
    fin_cases d <;> norm_num [Equiv.swap_apply_def,Fin.ext_iff]
    exact (hflip e).symm
  color_next := by intro d; simp only [Perm.mul_apply,Equiv.swap_apply_self]
  planar := PlanarMap.involution _ (Equiv.swap_apply_self 0 1)
  boundary := [0,1]
  boundary_cycle := ⟨by decide,by intro a _; fin_cases a <;> simp⟩
  boundary_word := by simp
  triangular := by intro d _ hn; fin_cases d <;> simp at hn

end Release075.TriangleFilling

namespace Release075
open Equiv PermCycles
attribute [local instance] Classical.propDecidable Classical.decEq
variable {A : Type*}

theorem IsBoundary.step {f : Perm A} {l : List A} (h : IsBoundary f l)
    (n : ℕ) (hn : n+1 < l.length) : f l[n] = l[n+1] := by
  rw [h.2 _ (List.getElem_mem _)]
  exact List.formPerm_apply_lt_getElem l h.1 n hn

theorem IsBoundary.erase_pair {f : Perm A} {a b : A} {l : List A}
    (h : IsBoundary f (b::a::l)) :
    IsBoundary (Equiv.swap b (f a)*f) l ∧
    (∀ z, z ∉ b::a::l → (Equiv.swap b (f a)*f) z = f z) := by
  constructor
  · refine ⟨h.1.of_cons.of_cons,?_⟩
    intro z hz
    cases l with
    | nil => simp at hz
    | cons c cs =>
      have hfa : f a = c := h.step 1 (by simp)
      have hcb : c ∉ [b,a] := by
        have hh := h.1
        simp only [List.nodup_cons,List.mem_cons] at hh ⊢
        tauto
      have hperm : (b::a::c::cs : List A).formPerm =
          Equiv.swap b c * (Equiv.swap b a * (c::cs).formPerm) := by
        simpa only [List.formPerm_pair, List.cons_append, List.nil_append] using formPerm_concat b c [a] cs hcb
      have hmem : (c::cs).formPerm z ∈ c::cs := List.formPerm_apply_mem_of_mem hz
      have hnb : (c::cs).formPerm z ≠ b := by
        intro he; apply h.1.notMem; rw [←he]; exact List.mem_cons_of_mem a hmem
      have hna : (c::cs).formPerm z ≠ a := by
        intro he; apply h.1.of_cons.notMem; rwa [←he]
      have hzfull : z ∈ b::a::c::cs := List.mem_cons_of_mem b (List.mem_cons_of_mem a hz)
      rw [Perm.mul_apply, hfa, h.2 z hzfull, hperm]
      simp only [Perm.mul_apply, Equiv.swap_apply_self,
        Equiv.swap_apply_of_ne_of_ne hnb hna]
  · intro z hz
    have hfz := (h.not_mem_iff z).mpr hz
    have hfa := (h.mem_iff a).mpr (by simp)
    apply Equiv.swap_apply_of_ne_of_ne
    · intro he; apply hfz; simp [he]
    · intro he; apply hfz; rwa [he]

theorem same_outside_boundary_pow {f g : Perm A} {l : List A}
    (hb : IsBoundary f l) (he : ∀ z, z ∉ l → g z = f z)
    {a : A} (ha : a ∉ l) (n : ℕ) : (g^n) a = (f^n) a := by
  have ho (k : ℕ) : (f^k) a ∉ l := by
    induction k with
    | zero => exact ha
    | succ k ih =>
      rw [pow_succ',Perm.mul_apply]
      exact (hb.not_mem_iff _).mpr ih
  induction n with
  | zero => rfl
  | succ n ih => simp only [pow_succ',Perm.mul_apply,ih,he _ (ho n)]

end Release075

namespace Release075.PermCycles
open Equiv
attribute [local instance] Classical.propDecidable Classical.decEq
variable {A : Type*}

theorem components_pred [Fintype A] (r f : Perm A) (p : A → Prop)
    (hr : ∀ a, p (r a) ↔ p a) (hf : ∀ a, p (f a) ↔ p a)
    {a b : A} (h : components r f a b) : p a ↔ p b := by
  have hh : components r f ≤ Setoid.ker p := by
    apply sup_le
    · intro x y h; exact propext (invariant_pred_sameCycle r p hr h)
    · intro x y h; exact propext (invariant_pred_sameCycle f p hf h)
  exact propext_iff.mp (hh h)

theorem pair_invariant (f : Perm A) {a b : A} (ha : f a = b) (hb : f b = a) (z : A) :
    (f z = a ∨ f z = b) ↔ (z = a ∨ z = b) := by
  constructor
  · rintro (h | h)
    · exact Or.inr (f.injective (h.trans hb.symm))
    · exact Or.inl (f.injective (h.trans ha.symm))
  · rintro (rfl | rfl)
    · exact Or.inr ha
    · exact Or.inl hb

end Release075.PermCycles

namespace Release075.TriangleFilling
open Equiv PermCycles
attribute [local instance] Classical.propDecidable Classical.decEq
variable {E V : Type} {flip : E → E} {color : E → V} {face : E → E → E → Prop}

/-- A genuine reverse-edge deletion, retaining the external word even when the
outside partners reconnect. The detached tree is an ignored separate component. -/
theorem fold {w : List E} (D : TriangleFilling flip color face w)
    (hflip : Function.Involutive flip) (hne : ∀ e, color e ≠ color (flip e))
    {a b : D.Dart} {l : List D.Dart} (hb : D.boundary = b::a::l)
    (hl : D.label a = flip (D.label b)) :
    Nonempty (TriangleFilling flip color face (l.map D.label)) := by
  have hbound : IsBoundary D.next (b::a::l) := hb ▸ D.boundary_cycle
  have hab : a ≠ b := fun h => hbound.1.notMem (by simp [h])
  have hba : D.next b = a := by simpa using hbound.step 0 (by simp)
  obtain ⟨r',f',hi',hn',hp',hl',hc',hra,hrb,hfa,hfb,hm,_,heq⟩ :=
    fold_pair D.reverse D.next D.reverse_involutive D.reverse_ne D.label flip hflip
      color hne D.reverse_label D.color_next D.planar hab hba hl
  have hrest := hbound.erase_pair
  rw [←heq] at hrest
  have hnot (z : D.Dart) (hz : z ∈ l) : ¬(z = a ∨ z = b) := by
    rintro (rfl | rfl)
    · exact hbound.1.of_cons.notMem hz
    · exact hbound.1.notMem (List.mem_cons_of_mem a hz)
  refine ⟨{
    Dart := D.Dart
    reverse := r'
    next := f'
    reverse_involutive := hi'
    reverse_ne := hn'
    label := D.label
    reverse_label := hl'
    color_next := hc'
    planar := hp'
    boundary := l
    boundary_cycle := hrest.1
    boundary_word := rfl
    triangular := ?_ }⟩
  intro z hz hzl
  obtain ⟨c,hcl,hzc⟩ := hz
  have hnotpair : ¬(z = a ∨ z = b) := by
    intro hp
    exact hnot c hcl ((components_pred r' f' (fun x => x=a ∨ x=b)
      (pair_invariant r' hra hrb) (pair_invariant f' hfa hfb) hzc).mp hp)
  have hzo : z ∉ b::a::l := by simp only [List.mem_cons]; tauto
  have htri := D.triangular z ⟨c,by rw [hb]; simp only [List.mem_cons]; tauto,hm hzc⟩
    (by rwa [hb])
  have he (n : ℕ) := same_outside_boundary_pow hbound hrest.2 hzo n
  refine ⟨?_,?_,?_⟩
  · rw [he 3]; exact htri.1
  · have hstep : f' z = D.next z := hrest.2 z hzo
    rw [hstep]
    exact htri.2.1
  · simpa only [hrest.2 z hzo,he 2] using htri.2.2

end Release075.TriangleFilling

namespace Release075
open Equiv PermCycles
attribute [local instance] Classical.propDecidable Classical.decEq
variable {A : Type*}

theorem IsBoundary.join {f : Perm A} {x y : A} {xs ys : List A}
    (hx : IsBoundary f (x::xs)) (hy : IsBoundary f (y::ys))
    (hd : List.Disjoint (x::xs) (y::ys)) :
    IsBoundary (Equiv.swap x y * f) ((x::xs) ++ (y::ys)) := by
  refine ⟨List.nodup_append.mpr ⟨hx.1,hy.1,by rintro z hz t ht rfl; exact hd hz ht⟩,?_⟩
  intro z hz
  rw [formPerm_concat x y xs ys (fun h => hd h (by simp))]
  simp only [Perm.mul_apply]
  congr 1
  rcases List.mem_append.mp hz with hz|hz
  · rw [List.formPerm_apply_of_notMem (fun h => hd hz h),hx.2 z hz]
  · rw [List.formPerm_apply_of_notMem (fun h => hd h (List.formPerm_apply_mem_of_mem hz)),
      hy.2 z hz]

theorem IsBoundary.swap_outside {f : Perm A} {x y : A} {xs ys : List A}
    (hx : IsBoundary f (x::xs)) (hy : IsBoundary f (y::ys))
    (z : A) (hz : z ∉ (x::xs) ++ (y::ys)) :
    (Equiv.swap x y * f) z = f z := by
  have hn := not_or.mp (List.mem_append.not.mp hz)
  apply Equiv.swap_apply_of_ne_of_ne
  · intro he; apply (hx.not_mem_iff z).mpr hn.1; simp [he]
  · intro he; apply (hy.not_mem_iff z).mpr hn.2; simp [he]

end Release075

namespace Release075.TriangleFilling
open Equiv PermCycles
attribute [local instance] Classical.propDecidable Classical.decEq
variable {E V : Type} {flip : E → E} {color : E → V} {face : E → E → E → Prop}

def Active {w : List E} (D : TriangleFilling flip color face w) (a : D.Dart) : Prop :=
  ∃ b ∈ D.boundary, components D.reverse D.next a b

theorem active_iff_of_components {w : List E} (D : TriangleFilling flip color face w)
    {a b : D.Dart} (h : components D.reverse D.next a b) : D.Active a ↔ D.Active b := by
  constructor <;> rintro ⟨c,hc,hc'⟩
  · exact ⟨c,hc,(components D.reverse D.next).trans ((components D.reverse D.next).symm h) hc'⟩
  · exact ⟨c,hc,(components D.reverse D.next).trans h hc'⟩

theorem active_reverse {w : List E} (D : TriangleFilling flip color face w) (a : D.Dart) :
    D.Active (D.reverse a) ↔ D.Active a :=
  D.active_iff_of_components ((show Perm.SameCycle.setoid D.reverse ≤
    components D.reverse D.next from le_sup_left)
      (Perm.sameCycle_apply_left.mpr (Perm.SameCycle.refl _ _)))

theorem active_next {w : List E} (D : TriangleFilling flip color face w) (a : D.Dart) :
    D.Active (D.next a) ↔ D.Active a :=
  D.active_iff_of_components ((show Perm.SameCycle.setoid D.next ≤
    components D.reverse D.next from le_sup_right)
      (Perm.sameCycle_apply_left.mpr (Perm.SameCycle.refl _ _)))

theorem active_of_mem {w : List E} (D : TriangleFilling flip color face w)
    {a : D.Dart} (ha : a ∈ D.boundary) : D.Active a :=
  ⟨a,ha,(components D.reverse D.next).refl _⟩

/-- Wedge two disks at their initial boundary corner. No component of either
input that was disjoint from its boundary becomes an active component. -/
theorem wedge {w w' : List E} (D : TriangleFilling flip color face w)
    (D' : TriangleFilling flip color face w')
    {a : D.Dart} {b : D'.Dart} {l : List D.Dart} {l' : List D'.Dart}
    (ha : D.boundary = a::l) (hb : D'.boundary = b::l')
    (hc : color (flip (D.label a)) = color (flip (D'.label b))) :
    Nonempty (TriangleFilling flip color face (w++w')) := by
  let : DecidableEq (D.Dart ⊕ D'.Dart) := Classical.decEq _
  let r := D.reverse.sumCongr D'.reverse
  let f := D.next.sumCongr D'.next
  let lab : D.Dart ⊕ D'.Dart → E := Sum.elim D.label D'.label
  let g := Equiv.swap (Sum.inl a) (Sum.inr b) * f
  let bd := (D.boundary.map Sum.inl) ++ (D'.boundary.map Sum.inr)
  have hleft : IsBoundary f ((a::l).map Sum.inl) :=
    (ha ▸ D.boundary_cycle).conjugate ⟨Sum.inl,Sum.inl_injective⟩ (fun _ => rfl)
  have hright : IsBoundary f ((b::l').map Sum.inr) :=
    (hb ▸ D'.boundary_cycle).conjugate ⟨Sum.inr,Sum.inr_injective⟩ (fun _ => rfl)
  have hdis : List.Disjoint ((a::l).map (@Sum.inl D.Dart D'.Dart))
      ((b::l').map Sum.inr) := by
    intro z hz hz'
    obtain ⟨x,_,rfl⟩ := List.mem_map.mp hz
    obtain ⟨y,_,hy⟩ := List.mem_map.mp hz'
    cases hy
  have hbd : IsBoundary g bd := by
    dsimp [g,bd]
    rw [ha,hb]
    exact hleft.join hright hdis
  have hsep : ¬ components r f (Sum.inl a) (Sum.inr b) := by
    intro h
    exact (components_pred r f leftPred (leftPred_sumCongr _ _)
      (leftPred_sumCongr _ _) h).mp True.intro
  have hr : ∀ z, lab (r z) = flip (lab z) := by
    intro z; cases z with
    | inl x => exact D.reverse_label x
    | inr x => exact D'.reverse_label x
  have hcol : ∀ z, color (lab ((r*f) z)) = color (lab z) := by
    intro z; cases z with
    | inl x => exact D.color_next x
    | inr x => exact D'.color_next x
  have hcg : ∀ z, color (lab ((r*g) z)) = color (lab z) := by
    apply swap_color_preserving r f (color ∘ lab) hcol
    change color (lab (r (Sum.inl a))) = color (lab (r (Sum.inr b)))
    rw [hr,hr]
    exact hc
  have hsame : ∀ z, z ∉ bd → g z = f z := by
    intro z hz
    apply hleft.swap_outside hright z
    simpa only [bd,ha,hb,List.map_cons] using hz
  let act : D.Dart ⊕ D'.Dart → Prop := Sum.elim D.Active D'.Active
  have har : ∀ z, act (r z) ↔ act z := by
    intro z; cases z with
    | inl x => exact D.active_reverse x
    | inr x => exact D'.active_reverse x
  have haf : ∀ z, act (f z) ↔ act z := by
    intro z; cases z with
    | inl x => exact D.active_next x
    | inr x => exact D'.active_next x
  have haa : act (Sum.inl a) := D.active_of_mem (by rw [ha]; simp)
  have hab : act (Sum.inr b) := D'.active_of_mem (by rw [hb]; simp)
  have hag : ∀ z, act (g z) ↔ act z := by
    intro z
    change act (Equiv.swap (Sum.inl a) (Sum.inr b) (f z)) ↔ act z
    rw [color_swap act (propext (iff_of_true haa hab))]
    exact haf z
  have hact : ∀ z, (∃ c ∈ bd, components r g z c) → act z := by
    rintro z ⟨c,hc,hzc⟩
    apply (components_pred r g act har hag hzc).mpr
    rcases List.mem_append.mp hc with hc|hc
    · obtain ⟨d,hd,rfl⟩ := List.mem_map.mp hc
      exact D.active_of_mem hd
    · obtain ⟨d,hd,rfl⟩ := List.mem_map.mp hc
      exact D'.active_of_mem hd
  refine ⟨{
    Dart := D.Dart ⊕ D'.Dart
    reverse := r
    next := g
    reverse_involutive := ?_
    reverse_ne := ?_
    label := lab
    reverse_label := hr
    color_next := hcg
    planar := (D.planar.sum D'.planar).join_right hsep
    boundary := bd
    boundary_cycle := hbd
    boundary_word := ?_
    triangular := ?_ }⟩
  · intro z
    cases z with
    | inl x => exact congrArg Sum.inl (D.reverse_involutive x)
    | inr x => exact congrArg Sum.inr (D'.reverse_involutive x)
  · intro z he
    cases z with
    | inl x => exact D.reverse_ne x (Sum.inl.inj he)
    | inr x => exact D'.reverse_ne x (Sum.inr.inj he)
  · simp only [bd,List.map_append,List.map_map]
    change D.boundary.map D.label ++ D'.boundary.map D'.label = w++w'
    rw [D.boundary_word,D'.boundary_word]
  · intro z hz hn
    have hzact := hact z hz
    have hpow (n : ℕ) : (g^n) z = (f^n) z := by
      symm
      apply same_outside_boundary_pow hbd
      · intro z hz; exact (hsame z hz).symm
      · exact hn

    cases z with
    | inl x =>
      have hxn : x ∉ D.boundary := by
        intro hx; apply hn; exact List.mem_append_left _ (List.mem_map.mpr ⟨x,hx,rfl⟩)
      have ht := D.triangular x hzact hxn
      have he (n : ℕ) : (f^n) (Sum.inl x) = Sum.inl ((D.next^n) x) :=
        (pow_intertwine D.next f Sum.inl (fun _ => rfl) n x).symm
      refine ⟨?_,?_,?_⟩
      · rw [hpow 3,he 3,ht.1]
      · rw [hsame _ hn]; intro hh; exact ht.2.1 (Sum.inl.inj hh)
      · rw [hsame _ hn,hpow 2,he 2]
        exact ht.2.2
    | inr x =>
      have hxn : x ∉ D'.boundary := by
        intro hx; apply hn; exact List.mem_append_right _ (List.mem_map.mpr ⟨x,hx,rfl⟩)
      have ht := D'.triangular x hzact hxn
      have he (n : ℕ) : (f^n) (Sum.inr x) = Sum.inr ((D'.next^n) x) :=
        (pow_intertwine D'.next f Sum.inr (fun _ => rfl) n x).symm
      refine ⟨?_,?_,?_⟩
      · rw [hpow 3,he 3,ht.1]
      · rw [hsame _ hn]; intro hh; exact ht.2.1 (Sum.inr.inj hh)
      · rw [hsame _ hn,hpow 2,he 2]
        exact ht.2.2

end Release075.TriangleFilling

namespace Release075.PermCycles
open Equiv
attribute [local instance] Classical.propDecidable Classical.decEq

theorem dipoleReverse_involutive : Function.Involutive dipoleReverse := by
  intro j; fin_cases j <;> simp

theorem dipoleReverse_ne (j : Fin 6) : dipoleReverse j ≠ j := by
  fin_cases j <;> norm_num [dipoleReverse,Perm.mul_apply,Equiv.swap_apply_def,Fin.ext_iff]

theorem dipoleReverse_count : cycleCount dipoleReverse = 3 := by
  have h := card_eq_mul_cycles dipoleReverse 2 (orbit_card_involution dipoleReverse
    dipoleReverse_involutive dipoleReverse_ne)
  have hh : (6:ℕ) = 2 * cycleCount dipoleReverse := by
    simpa only [Fintype.card_fin,cycleCount,Nat.card_eq_fintype_card] using h
  omega

theorem dipoleVertex_count : cycleCount (dipoleReverse*dipoleFace) = 3 := by
  have hi : Function.Involutive (dipoleReverse*dipoleFace) := by
    intro j; fin_cases j <;> simp [Perm.mul_apply]
  have hn : ∀ j, (dipoleReverse*dipoleFace) j ≠ j := by
    intro j; fin_cases j <;> norm_num [dipoleReverse,dipoleFace,Perm.mul_apply,Equiv.swap_apply_def,Fin.ext_iff]
  have h := card_eq_mul_cycles (dipoleReverse*dipoleFace) 2
    (orbit_card_involution _ hi hn)
  have hh : (6:ℕ) = 2 * cycleCount (dipoleReverse*dipoleFace) := by
    simpa only [Fintype.card_fin,cycleCount,Nat.card_eq_fintype_card] using h
  omega

theorem dipole_components (a b : Fin 6) : components dipoleReverse dipoleFace a b := by
  let s := components dipoleReverse dipoleFace
  have hr (j : Fin 6) : s j (dipoleReverse j) :=
    (show Perm.SameCycle.setoid dipoleReverse ≤ s from le_sup_left)
      (Perm.sameCycle_apply_right.mpr (Perm.SameCycle.refl _ _))
  have hf (j : Fin 6) : s j (dipoleFace j) :=
    (show Perm.SameCycle.setoid dipoleFace ≤ s from le_sup_right)
      (Perm.sameCycle_apply_right.mpr (Perm.SameCycle.refl _ _))
  have h01 : s 0 1 := by simpa only [dipoleFace_zero] using hf 0
  have h12 : s 1 2 := by simpa only [dipoleFace_one] using hf 1
  have h03 : s 0 3 := by simpa only [dipoleReverse_zero] using hr 0
  have h34 : s 3 4 := by simpa only [dipoleFace_three] using hf 3
  have h45 : s 4 5 := by simpa only [dipoleFace_four] using hf 4
  have h0 (j : Fin 6) : s 0 j := by
    fin_cases j
    · exact s.refl 0
    · exact h01
    · exact s.trans h01 h12
    · exact h03
    · exact s.trans h03 h34
    · exact s.trans (s.trans h03 h34) h45
  exact s.trans (s.symm (h0 a)) (h0 b)

theorem dipoleComponent_count : componentCount dipoleReverse dipoleFace = 1 := by
  apply Nat.card_eq_one_iff_exists.mpr
  refine ⟨Quotient.mk _ 0,?_⟩
  intro z
  obtain ⟨j,rfl⟩ := Quotient.mk_surjective z
  exact Quotient.sound (dipole_components j 0)

theorem dipole_planar : PlanarMap dipoleReverse dipoleFace := by
  simp only [PlanarMap,dipoleReverse_count,dipoleFace_count,dipoleVertex_count,
    dipoleComponent_count,Fintype.card_fin]

end Release075.PermCycles

namespace Release075.TriangleFilling
open Equiv PermCycles
attribute [local instance] Classical.propDecidable Classical.decEq
variable {E V : Type} {flip : E → E} {color : E → V} {face : E → E → E → Prop}

def triLabel (a b c : E) (j : Fin 6) : E :=
  if j=0 then a else if j=1 then b else if j=2 then c else
  if j=3 then flip a else if j=4 then flip c else flip b

noncomputable def triangle (hflip : Function.Involutive flip)
    (hrot : ∀ a b c, face a b c → face b c a)
    (a b c : E) (hab : color a = color (flip b))
    (hbc : color b = color (flip c)) (hca : color c = color (flip a))
    (hface : face (flip a) (flip c) (flip b)) :
    TriangleFilling flip color face [a,b,c] where
  Dart := Fin 6
  reverse := dipoleReverse
  next := dipoleFace
  reverse_involutive := dipoleReverse_involutive
  reverse_ne := dipoleReverse_ne
  label := triLabel (flip := flip) a b c
  reverse_label := by
    intro j; fin_cases j <;> simp [triLabel]
    all_goals exact (hflip _).symm
  color_next := by
    intro j; fin_cases j <;> simp [Perm.mul_apply,triLabel,hab,hbc,hca]
  planar := dipole_planar
  boundary := [0,1,2]
  boundary_cycle := by
    constructor
    · decide
    · intro j hj
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hj
      rcases hj with rfl|rfl|rfl <;> simp [List.formPerm_cons_cons,Equiv.swap_apply_def]
  boundary_word := by simp [triLabel]
  triangular := by
    intro j _ hj
    fin_cases j
    · simp at hj
    · simp at hj
    · simp at hj
    · norm_num [pow_succ',Perm.mul_apply,triLabel,dipoleFace,Equiv.swap_apply_def,Fin.ext_iff]
      exact hface
    · norm_num [pow_succ',Perm.mul_apply,triLabel,dipoleFace,Equiv.swap_apply_def,Fin.ext_iff]
      exact hrot _ _ _ hface
    · norm_num [pow_succ',Perm.mul_apply,triLabel,dipoleFace,Equiv.swap_apply_def,Fin.ext_iff]
      exact hrot _ _ _ (hrot _ _ _ hface)

end Release075.TriangleFilling

namespace Release075.PermCycles
open Equiv
attribute [local instance] Classical.propDecidable Classical.decEq
variable {A : Type*} [Fintype A]

omit [Fintype A] in
theorem cycleCount_inv (f : Perm A) : cycleCount f⁻¹ = cycleCount f := by
  apply Nat.card_congr
  exact Quotient.congr (Equiv.refl A) (fun _ _ => Perm.sameCycle_inv)

omit [Fintype A] in
theorem components_inv_right (r f : Perm A) : components r f⁻¹ = components r f := by
  have hf : Perm.SameCycle.setoid f⁻¹ = Perm.SameCycle.setoid f :=
    Setoid.ext (fun _ _ => Perm.sameCycle_inv)
  simp only [components,hf]

theorem PlanarMap.inv_right {r f : Perm A} (hi : Function.Involutive r)
    (hp : PlanarMap r f) : PlanarMap r f⁻¹ := by
  have hr : r⁻¹ = r := by
    apply inv_eq_of_mul_eq_one_left
    exact Equiv.ext hi
  have hc : cycleCount (r*f⁻¹) = cycleCount (r*f) := by
    rw [cycleCount_mul_comm]
    have he : f⁻¹*r = (r*f)⁻¹ := by rw [mul_inv_rev,hr]
    rw [he,cycleCount_inv]
  simpa only [PlanarMap,cycleCount_inv,hc,componentCount,components_inv_right] using hp

omit [Fintype A] in
theorem perm_apply_inv (f : Perm A) (a : A) : f (f⁻¹ a) = a := f.apply_symm_apply a

omit [Fintype A] in
theorem inv_cycle_three (f : Perm A) {a : A} (h : (f^3) a = a) :
    f⁻¹ a = (f^2) a ∧ (f⁻¹^2) a = f a ∧ (f⁻¹^3) a = a := by
  have he : f⁻¹ a = (f^2) a := by
    apply f.injective
    rw [perm_apply_inv]
    exact h.symm
  refine ⟨he,?_,?_⟩
  · rw [pow_two,Perm.mul_apply,he]
    change f⁻¹ (f (f a)) = f a
    exact f.symm_apply_apply _
  · rw [inv_pow]
    apply (f^3).injective
    rw [perm_apply_inv,h]

end Release075.PermCycles

namespace Release075
open Equiv PermCycles
attribute [local instance] Classical.propDecidable Classical.decEq
variable {A : Type*}

theorem IsBoundary.reverse {f : Perm A} {l : List A} (h : IsBoundary f l) :
    IsBoundary f⁻¹ l.reverse := by
  refine ⟨List.nodup_reverse.mpr h.1,?_⟩
  intro a ha
  have ha' := List.mem_reverse.mp ha
  have hb : f⁻¹ a ∈ l := by
    apply (h.mem_iff _).mp
    simpa only [perm_apply_inv] using ha'
  rw [List.formPerm_reverse]
  apply l.formPerm.injective
  rw [←h.2 _ hb,perm_apply_inv,perm_apply_inv]

end Release075

namespace Release075.TriangleFilling
open Equiv PermCycles
attribute [local instance] Classical.propDecidable Classical.decEq
variable {E V : Type} {flip : E → E} {color : E → V} {face : E → E → E → Prop}

/-- Reverse the orientation of the whole filling, not just its boundary word. -/
noncomputable def mirror {w : List E} (D : TriangleFilling flip color face w)
    (hflip : Function.Involutive flip)
    (hface : ∀ a b c, face a b c → face (flip a) (flip c) (flip b)) :
    TriangleFilling flip color face (w.reverse.map flip) where
  Dart := D.Dart
  reverse := D.reverse
  next := D.next⁻¹
  reverse_involutive := D.reverse_involutive
  reverse_ne := D.reverse_ne
  label := flip ∘ D.label
  reverse_label := by
    intro a
    simp only [Function.comp_apply,D.reverse_label]
  color_next := by
    intro a
    simp only [Function.comp_apply,Perm.mul_apply,D.reverse_label]
    rw [hflip]
    have h := D.color_next (D.next⁻¹ a)
    simpa only [Perm.mul_apply,perm_apply_inv,D.reverse_label] using h.symm
  planar := D.planar.inv_right D.reverse_involutive
  boundary := D.boundary.reverse
  boundary_cycle := D.boundary_cycle.reverse
  boundary_word := by rw [←List.map_map,List.map_reverse,D.boundary_word]
  triangular := by
    intro a ha hn
    have ha' : ∃ b ∈ D.boundary, components D.reverse D.next a b := by
      obtain ⟨b,hb,hab⟩ := ha
      refine ⟨b,List.mem_reverse.mp hb,?_⟩
      rw [components_inv_right] at hab
      exact hab
    have ht := D.triangular a ha' (by simpa only [List.mem_reverse] using hn)
    have he := inv_cycle_three D.next ht.1
    refine ⟨he.2.2,?_,?_⟩
    · intro h
      apply ht.2.1
      have hh := congrArg D.next h
      simpa only [perm_apply_inv] using hh.symm
    · simp only [Function.comp_apply,he.1,he.2.1]
      exact hface _ _ _ ht.2.2

end Release075.TriangleFilling

namespace Release075
open Equiv PermCycles
attribute [local instance] Classical.propDecidable Classical.decEq
variable {E V : Type} {flip : E → E} {color : E → V} {face : E → E → E → Prop}

/-- Existence of a finite labelled genus-zero filling. This abbreviation contains
no geometric assertion outside the fully specified finite map. -/
def Fillable (flip : E → E) (color : E → V) (face : E → E → E → Prop) (w : List E) : Prop :=
  Nonempty (TriangleFilling flip color face w)

namespace Fillable

theorem empty : Fillable flip color face [] := ⟨TriangleFilling.empty⟩

theorem rotateAppend {u v : List E} (h : Fillable flip color face (u++v)) :
    Fillable flip color face (v++u) := by
  obtain ⟨D⟩ := h
  have h' : Nonempty (TriangleFilling flip color face ((u++v).rotate u.length)) :=
    ⟨D.rotate u.length⟩
  simpa only [Fillable, List.rotate_append_length_eq] using h'

theorem mirror {w : List E} (h : Fillable flip color face w)
    (hi : Function.Involutive flip)
    (hf : ∀ a b c, face a b c → face (flip a) (flip c) (flip b)) :
    Fillable flip color face (w.reverse.map flip) := by
  obtain ⟨D⟩ := h
  exact ⟨D.mirror hi hf⟩

theorem foldHead (hi : Function.Involutive flip) (hn : ∀ e, color e ≠ color (flip e))
    {e : E} {w : List E} (h : Fillable flip color face (e::flip e::w)) :
    Fillable flip color face w := by
  obtain ⟨D⟩ := h
  obtain ⟨b,bs,hb,he,hbs⟩ := List.map_eq_cons_iff.mp D.boundary_word
  obtain ⟨a,l,ha,hae,hl⟩ := List.map_eq_cons_iff.mp hbs
  have hbound : D.boundary = b::a::l := by rw [hb,ha]
  have hab : D.label a = flip (D.label b) := by rw [he,hae]
  have hf := D.fold hi hn hbound hab
  rwa [hl] at hf

theorem erase (hi : Function.Involutive flip) (hn : ∀ e, color e ≠ color (flip e))
    (u v : List E) (e : E) (h : Fillable flip color face (u++e::flip e::v)) :
    Fillable flip color face (u++v) := by
  have h' : Fillable flip color face (e::flip e::(v++u)) := h.rotateAppend
  exact (h'.foldHead hi hn).rotateAppend

/-- Concatenate loops based at the same boundary corner. Empty words are allowed. -/
theorem app {u v : List E} (hu : Fillable flip color face u) (hv : Fillable flip color face v)
    (hbase : ∀ e es f fs, u = e::es → v = f::fs →
      color (flip e) = color (flip f)) : Fillable flip color face (u++v) := by
  cases u with
  | nil => exact hv
  | cons e es =>
    cases v with
    | nil => simpa only [List.append_nil] using hu
    | cons f fs =>
      obtain ⟨D⟩ := hu
      obtain ⟨D'⟩ := hv
      obtain ⟨a,l,ha,hal,_⟩ := List.map_eq_cons_iff.mp D.boundary_word
      obtain ⟨b,l',hb,hbl,_⟩ := List.map_eq_cons_iff.mp D'.boundary_word
      apply D.wedge D' ha hb
      rw [hal,hbl]
      exact hbase e es f fs rfl rfl

theorem backtrack (hi : Function.Involutive flip) (e : E) :
    Fillable flip color face [e,flip e] := ⟨TriangleFilling.backtrack hi e⟩

/-- Attach a stem, retaining its two directed traversals in the prescribed walk. -/
theorem stem (hi : Function.Involutive flip) {w : List E}
    (h : Fillable flip color face w) (e : E)
    (hc : ∀ a l, w = a::l → color (flip a) = color e) :
    Fillable flip color face (e::w++[flip e]) := by
  have hb : Fillable flip color face [flip e,e] := by
    have h' := backtrack (color := color) (face := face) hi (flip e)
    rwa [hi e] at h'
  have hh : Fillable flip color face ([flip e,e]++w) := hb.app h (by
    intro a l b m ha hm
    have hae : a = flip e := (List.cons.inj ha).1.symm
    rw [hae,hi]
    exact (hc b m hm).symm)
  exact rotateAppend (u := [flip e]) (v := e::w) hh

end Fillable
end Release075

end OAI
end
end

section
section
namespace OAI

namespace Release075
attribute [local instance] Classical.propDecidable Classical.decEq
variable {E V : Type} {flip : E → E} {color : E → V} {face : E → E → E → Prop}

inductive WordPath (flip : E → E) (color : E → V) : V → V → List E → Prop
  | nil (v : V) : WordPath flip color v v []
  | cons (e : E) {v : V} {w : List E} : WordPath flip color (color e) v w →
      WordPath flip color (color (flip e)) v (e::w)

def reverseWord (flip : E → E) (w : List E) : List E := w.reverse.map flip

@[simp] theorem reverseWord_nil : reverseWord flip [] = [] := rfl
@[simp] theorem reverseWord_cons (e : E) (w : List E) :
    reverseWord flip (e::w) = reverseWord flip w ++ [flip e] := by
  simp [reverseWord]
@[simp] theorem reverseWord_append (w z : List E) :
    reverseWord flip (w++z) = reverseWord flip z ++ reverseWord flip w := by
  simp [reverseWord]

theorem reverseWord_reverse (hi : Function.Involutive flip) (w : List E) :
    reverseWord flip (reverseWord flip w) = w := by
  simp only [reverseWord,List.map_reverse,List.reverse_reverse,List.map_map]
  rw [show flip ∘ flip = id from funext hi]
  exact List.map_id w

namespace WordPath
variable {a b c : V} {u v : List E}

theorem source {e : E} {w : List E} (h : WordPath flip color a b (e::w)) :
    color (flip e) = a := by cases h; rfl

theorem append (h : WordPath flip color a b u) (h' : WordPath flip color b c v) :
    WordPath flip color a c (u++v) := by
  induction h with
  | nil => exact h'
  | cons e _ ih => exact .cons e (ih h')

theorem singleton (e : E) : WordPath flip color (color (flip e)) (color e) [e] :=
  .cons e (.nil _)

theorem reverse (hi : Function.Involutive flip) (h : WordPath flip color a b u) :
    WordPath flip color b a (reverseWord flip u) := by
  induction h with
  | nil => exact .nil _
  | cons e _ ih =>
    rw [reverseWord_cons]
    apply ih.append
    have hh := singleton (color := color) (flip := flip) (flip e)
    rwa [hi] at hh

end WordPath

namespace Fillable
variable (hi : Function.Involutive flip)
variable (hn : ∀ e, color e ≠ color (flip e))

include hi hn in
/-- Erase a reversed path followed by the path, in any boundary context. -/
theorem erase_reverse (u v p : List E)
    (h : Fillable flip color face (u ++ reverseWord flip p ++ p ++ v)) :
    Fillable flip color face (u++v) := by
  induction p generalizing u with
  | nil => simpa only [reverseWord_nil,List.append_nil,List.nil_append] using h
  | cons e p ih =>
    simp only [reverseWord_cons,List.append_assoc,List.singleton_append] at h
    have h' : Fillable flip color face
        ((u++reverseWord flip p) ++ flip e :: flip (flip e) :: (p++v)) := by
      rw [hi e]
      simpa only [List.append_assoc,List.cons_append] using h
    exact ih u (by simpa only [List.append_assoc] using
      (h'.erase hi hn (u++reverseWord flip p) (p++v) (flip e)))

include hi in
/-- Attach a whole typed stem; each corner identification is type checked. -/
theorem stemPath {a b : V} {p w : List E} (hp : WordPath flip color a b p)
    (hw : WordPath flip color b b w) (h : Fillable flip color face w) :
    Fillable flip color face (p++w++reverseWord flip p) := by
  induction hp with
  | nil => simpa only [reverseWord_nil,List.nil_append,List.append_nil] using h
  | @cons e b p hp ih =>
    have hloop : WordPath flip color (color e) (color e)
        (p++w++reverseWord flip p) := (hp.append hw).append (hp.reverse hi)
    have hh := (ih hw).stem hi e (fun x xs hx => by
      rw [hx] at hloop
      exact hloop.source)
    simpa only [reverseWord_cons,List.cons_append,List.append_assoc] using hh

include hi in
theorem palindrome {a b : V} {p : List E} (hp : WordPath flip color a b p) :
    Fillable flip color face (p++reverseWord flip p) := by
  simpa only [List.append_nil] using (stemPath hi hp (.nil b)
    (empty (flip := flip) (color := color) (face := face)))

end Fillable

/-- Filling the two paths glued along their common endpoints. -/
def FilledBetween (flip : E → E) (color : E → V) (face : E → E → E → Prop)
    (p q : List E) : Prop := Fillable flip color face (p++reverseWord flip q)

namespace FilledBetween
variable (hi : Function.Involutive flip)
variable (hn : ∀ e, color e ≠ color (flip e))
variable (hf : ∀ a b c, face a b c → face (flip a) (flip c) (flip b))
variable {a b c d : V} {p q r u v : List E}

include hi in
theorem refl (hp : WordPath flip color a b p) : FilledBetween flip color face p p :=
  Fillable.palindrome hi hp

include hi hf in
theorem symm (h : FilledBetween flip color face p q) : FilledBetween flip color face q p := by
  have hm := Fillable.mirror h hi hf
  change Fillable flip color face (reverseWord flip (p++reverseWord flip q)) at hm
  simpa only [FilledBetween,reverseWord_append,reverseWord_reverse hi] using hm

include hi hn in
theorem trans (hp : WordPath flip color a b p) (hq : WordPath flip color a b q)
    (hr : WordPath flip color a b r)
    (h : FilledBetween flip color face p q) (h' : FilledBetween flip color face q r) :
    FilledBetween flip color face p r := by
  have hloop := hp.append (hq.reverse hi)
  have hloop' := hq.append (hr.reverse hi)
  have hh := Fillable.app h h' (by
    intro e es f fs he hf
    rw [he] at hloop
    rw [hf] at hloop'
    exact hloop.source.trans hloop'.source.symm)
  apply Fillable.erase_reverse hi hn p (reverseWord flip r) q
  simpa only [List.append_assoc] using hh

include hi in
theorem whiskerLeft (hu : WordPath flip color c a u)
    (hp : WordPath flip color a b p) (hq : WordPath flip color a b q)
    (h : FilledBetween flip color face p q) :
    FilledBetween flip color face (u++p) (u++q) := by
  have hh := Fillable.stemPath hi hu (hp.append (hq.reverse hi)) h
  simpa only [FilledBetween,reverseWord_append,List.append_assoc] using hh

include hi in
theorem whiskerRight (hp : WordPath flip color a b p) (hq : WordPath flip color a b q)
    (hv : WordPath flip color b c v) (h : FilledBetween flip color face p q) :
    FilledBetween flip color face (p++v) (q++v) := by
  have h' : FilledBetween flip color face (reverseWord flip q) (reverseWord flip p) := by
    simpa only [FilledBetween,reverseWord_reverse hi] using
      (Fillable.rotateAppend (u := p) (v := reverseWord flip q) h)
  have hh := whiskerLeft hi (hv.reverse hi) (hq.reverse hi) (hp.reverse hi) h'
  have hh' := Fillable.rotateAppend hh
  simpa only [FilledBetween,reverseWord_append,reverseWord_reverse hi,List.append_assoc] using hh'

end FilledBetween
end Release075

namespace Release075.BlockPresentation
open CategoryTheory
variable {I B : Type} {r : ℕ} (d : BlockPresentation I B r)

abbrev OrientedEdge := d.Edge × Bool

def flipEdge : d.OrientedEdge → d.OrientedEdge := fun ⟨e,s⟩ => (e,!s)

@[simp] theorem flipEdge_flipEdge (e : d.OrientedEdge) : d.flipEdge (d.flipEdge e) = e := by
  rcases e with ⟨e,s⟩
  cases s <;> rfl

def edgeTarget : d.OrientedEdge → d.Vertex
  | (.inl _, true) => .w
  | (.inl _, false) => .v
  | (.inr (.inl _), true) => .v
  | (.inr (.inl _), false) => .o
  | (.inr (.inr _), true) => .w
  | (.inr (.inr _), false) => .o

theorem edgeTarget_ne (e : d.OrientedEdge) : d.edgeTarget e ≠ d.edgeTarget (d.flipEdge e) := by
  rcases e with ⟨e,s⟩
  rcases e with x|l|rr <;> cases s <;> simp [edgeTarget,flipEdge]

def arrowLabel {a c : d.Vertex} : d.Arrow a c → d.Edge
  | .x e => .inl e
  | .l e => .inr (.inl e)
  | .rr e => .inr (.inr e)

def orientedLabel {a c : Quiver.Symmetrify d.Vertex} (f : a ⟶ c) : d.OrientedEdge :=
  match f with
  | .inl e => (d.arrowLabel e,true)
  | .inr e => (d.arrowLabel e,false)

@[simp] theorem orientedLabel_reverse {a c : Quiver.Symmetrify d.Vertex} (f : a ⟶ c) :
    d.orientedLabel (Quiver.reverse f) = d.flipEdge (d.orientedLabel f) := by
  change d.Arrow a c ⊕ d.Arrow c a at f
  cases f <;> rfl

@[simp] theorem orientedLabel_target {a c : Quiver.Symmetrify d.Vertex} (f : a ⟶ c) :
    d.edgeTarget (d.orientedLabel f) = c := by
  change d.Arrow a c ⊕ d.Arrow c a at f
  rcases f with f|f
  · change d.Arrow a c at f
    cases f <;> rfl
  · change d.Arrow c a at f
    cases f <;> rfl

@[simp] theorem orientedLabel_source {a c : Quiver.Symmetrify d.Vertex} (f : a ⟶ c) :
    d.edgeTarget (d.flipEdge (d.orientedLabel f)) = a := by
  rw [← d.orientedLabel_reverse]
  exact d.orientedLabel_target _

def rawWord {a : Quiver.Symmetrify d.Vertex} :
    ∀ {c : Quiver.Symmetrify d.Vertex},
      @Quiver.Path (Quiver.Symmetrify d.Vertex) (Quiver.symmetrifyQuiver d.Vertex) a c →
        List d.OrientedEdge
  | _, .nil => []
  | _, .cons p f => rawWord p ++ [d.orientedLabel f]

@[simp] theorem rawWord_nil (a : d.RawPaths) : d.rawWord (𝟙 a) = [] := rfl

@[simp] theorem rawWord_comp {a b c : d.RawPaths} (p : a ⟶ b) (q : b ⟶ c) :
    d.rawWord (p ≫ q) = d.rawWord p ++ d.rawWord q := by
  change @Quiver.Path (Quiver.Symmetrify d.Vertex) (Quiver.symmetrifyQuiver d.Vertex) b c at q
  induction q with
  | nil =>
    change d.rawWord p = d.rawWord p ++ []
    exact (List.append_nil _).symm
  | cons q f ih =>
    change d.rawWord (p ≫ q) ++ [d.orientedLabel f] =
      d.rawWord p ++ (d.rawWord q ++ [d.orientedLabel f])
    rw [ih,List.append_assoc]

theorem rawWord_path_comp {a b c : Quiver.Symmetrify d.Vertex}
    (p : Quiver.Path a b) (q : Quiver.Path b c) :
    d.rawWord (p.comp q) = d.rawWord p ++ d.rawWord q := by
  induction q with
  | nil => exact (List.append_nil _).symm
  | cons q f ih =>
    change d.rawWord (p.comp q) ++ [d.orientedLabel f] =
      d.rawWord p ++ (d.rawWord q ++ [d.orientedLabel f])
    rw [ih,List.append_assoc]

@[simp] theorem rawWord_toPath {a c : Quiver.Symmetrify d.Vertex} (f : a ⟶ c) :
    d.rawWord f.toPath = [d.orientedLabel f] := rfl

@[simp] theorem rawWord_reverse {a c : Quiver.Symmetrify d.Vertex}
    (p : Quiver.Path a c) :
    d.rawWord p.reverse = reverseWord d.flipEdge (d.rawWord p) := by
  change @Quiver.Path (Quiver.Symmetrify d.Vertex) (Quiver.symmetrifyQuiver d.Vertex) a c at p
  induction p with
  | nil => rfl
  | cons p f ih =>
    change d.rawWord (Quiver.Path.comp (Quiver.reverse f).toPath p.reverse) =
      reverseWord d.flipEdge (d.rawWord p ++ [d.orientedLabel f])
    rw [d.rawWord_path_comp,d.rawWord_toPath,d.orientedLabel_reverse,ih]
    simp only [reverseWord_append,reverseWord_cons,reverseWord_nil,List.nil_append]

theorem rawWord_typed {a c : Quiver.Symmetrify d.Vertex} (p : Quiver.Path a c) :
    WordPath d.flipEdge d.edgeTarget a c (d.rawWord p) := by
  change @Quiver.Path (Quiver.Symmetrify d.Vertex) (Quiver.symmetrifyQuiver d.Vertex) a c at p
  induction p with
  | nil => exact .nil _
  | cons p f ih =>
    apply ih.append
    have hs := d.orientedLabel_source f
    have ht := d.orientedLabel_target f
    have hh := WordPath.singleton (flip := d.flipEdge) (color := d.edgeTarget) (d.orientedLabel f)
    simpa only [hs,ht] using hh

def orientedL (b : B) (i : (d.block b).labels) (u v : Fin r) : d.OrientedEdge :=
  (.inr (.inl ⟨b,u,((d.block b).coordinates i).1 + (v.val : ZMod (d.block b).s)⟩),true)
def orientedX (i : I) (u v : Fin r) : d.OrientedEdge := (.inl (i,u,v),true)
def orientedR (b : B) (i : (d.block b).labels) (u v : Fin r) : d.OrientedEdge :=
  (.inr (.inr ⟨b,v,((d.block b).coordinates i).2 + (u.val : ZMod (d.block b).t)⟩),true)

inductive TriangleFace : d.OrientedEdge → d.OrientedEdge → d.OrientedEdge → Prop
  | pos₀ (b : B) (i : (d.block b).labels) (u v : Fin r) :
    TriangleFace (d.orientedL b i u v) (d.orientedX i u v) (d.flipEdge (d.orientedR b i u v))
  | pos₁ (b : B) (i : (d.block b).labels) (u v : Fin r) :
    TriangleFace (d.orientedX i u v) (d.flipEdge (d.orientedR b i u v)) (d.orientedL b i u v)
  | pos₂ (b : B) (i : (d.block b).labels) (u v : Fin r) :
    TriangleFace (d.flipEdge (d.orientedR b i u v)) (d.orientedL b i u v) (d.orientedX i u v)
  | neg₀ (b : B) (i : (d.block b).labels) (u v : Fin r) :
    TriangleFace (d.flipEdge (d.orientedL b i u v)) (d.orientedR b i u v) (d.flipEdge (d.orientedX i u v))
  | neg₁ (b : B) (i : (d.block b).labels) (u v : Fin r) :
    TriangleFace (d.orientedR b i u v) (d.flipEdge (d.orientedX i u v)) (d.flipEdge (d.orientedL b i u v))
  | neg₂ (b : B) (i : (d.block b).labels) (u v : Fin r) :
    TriangleFace (d.flipEdge (d.orientedX i u v)) (d.flipEdge (d.orientedL b i u v)) (d.orientedR b i u v)

theorem TriangleFace.rotate {a b c : d.OrientedEdge} (h : d.TriangleFace a b c) :
    d.TriangleFace b c a := by
  cases h with
  | pos₀ b i u v => exact .pos₁ b i u v
  | pos₁ b i u v => exact .pos₂ b i u v
  | pos₂ b i u v => exact .pos₀ b i u v
  | neg₀ b i u v => exact .neg₁ b i u v
  | neg₁ b i u v => exact .neg₂ b i u v
  | neg₂ b i u v => exact .neg₀ b i u v

theorem TriangleFace.mirror {a b c : d.OrientedEdge} (h : d.TriangleFace a b c) :
    d.TriangleFace (d.flipEdge a) (d.flipEdge c) (d.flipEdge b) := by
  cases h with
  | pos₀ b i u v => simpa only [flipEdge_flipEdge] using TriangleFace.neg₀ (d := d) b i u v
  | pos₁ b i u v => simpa only [flipEdge_flipEdge] using TriangleFace.neg₂ (d := d) b i u v
  | pos₂ b i u v => simpa only [flipEdge_flipEdge] using TriangleFace.neg₁ (d := d) b i u v
  | neg₀ b i u v => simpa only [flipEdge_flipEdge] using TriangleFace.pos₀ (d := d) b i u v
  | neg₁ b i u v => simpa only [flipEdge_flipEdge] using TriangleFace.pos₂ (d := d) b i u v
  | neg₂ b i u v => simpa only [flipEdge_flipEdge] using TriangleFace.pos₁ (d := d) b i u v

theorem rawMove_filled {a c : d.RawPaths} {p q : a ⟶ c} (h : d.RawMove p q) :
    FilledBetween d.flipEdge d.edgeTarget d.TriangleFace (d.rawWord p) (d.rawWord q) := by
  cases h with
  | backtrack h =>
    cases h with
    | step a c f =>
      change Fillable d.flipEdge d.edgeTarget d.TriangleFace
        (reverseWord d.flipEdge [d.orientedLabel f,d.orientedLabel (Quiver.reverse f)])
      rw [d.orientedLabel_reverse]
      simp only [reverseWord_cons,reverseWord_nil,List.nil_append,
        flipEdge_flipEdge,List.singleton_append]
      exact ⟨TriangleFilling.backtrack (d.flipEdge_flipEdge) (d.orientedLabel f)⟩
  | triangle b i u v =>
    change Nonempty (TriangleFilling d.flipEdge d.edgeTarget d.TriangleFace
      [d.orientedL b i u v, d.orientedX i u v, d.flipEdge (d.orientedR b i u v)])
    exact ⟨TriangleFilling.triangle d.flipEdge_flipEdge (fun _ _ _ => TriangleFace.rotate d)
      _ _ _ rfl rfl rfl (by simpa only [flipEdge_flipEdge] using TriangleFace.neg₀ (d := d) b i u v)⟩

theorem rawHomotopic_filled {a c : d.RawPaths} {p q : a ⟶ c} (h : d.RawHomotopic p q) :
    FilledBetween d.flipEdge d.edgeTarget d.TriangleFace (d.rawWord p) (d.rawWord q) := by
  induction h with
  | rel p q h =>
    cases h with
    | intro a c u p q v h =>
      rw [d.rawWord_comp,d.rawWord_comp,d.rawWord_comp,d.rawWord_comp]
      exact FilledBetween.whiskerLeft d.flipEdge_flipEdge (d.rawWord_typed u)
        ((d.rawWord_typed p).append (d.rawWord_typed v))
        ((d.rawWord_typed q).append (d.rawWord_typed v))
        (FilledBetween.whiskerRight d.flipEdge_flipEdge (d.rawWord_typed p)
          (d.rawWord_typed q) (d.rawWord_typed v) (d.rawMove_filled h))
  | refl p => exact FilledBetween.refl d.flipEdge_flipEdge (d.rawWord_typed p)
  | symm p q _ ih =>
    exact FilledBetween.symm d.flipEdge_flipEdge
      (fun _ _ _ => TriangleFace.mirror d) ih
  | trans p q s _ _ ih ih' =>
    exact FilledBetween.trans d.flipEdge_flipEdge d.edgeTarget_ne
      (d.rawWord_typed p) (d.rawWord_typed q) (d.rawWord_typed s) ih ih'

theorem nullhomotopic_fillable {a : d.RawPaths} {p : a ⟶ a} (h : d.RawHomotopic p (𝟙 a)) :
    Fillable d.flipEdge d.edgeTarget d.TriangleFace (d.rawWord p) := by
  simpa only [FilledBetween,rawWord_nil,reverseWord_nil,List.append_nil] using
    d.rawHomotopic_filled h

/-- The actual presented rectangular word, if trivial, has a finite labelled
planar triangular filling. This lemma has no geometric hypothesis. -/
theorem rectangle_fillable_of_eq_one (i : I) (u u' v v' : Fin r)
    (h : d.x i u v * (d.x i u' v)⁻¹ * d.x i u' v' * (d.x i u v')⁻¹ = 1) :
    Fillable d.flipEdge d.edgeTarget d.TriangleFace
      [d.orientedX i u v, d.flipEdge (d.orientedX i u' v),
       d.orientedX i u' v', d.flipEdge (d.orientedX i u v')] := by
  exact d.nullhomotopic_fillable (d.rawRectangle_nullhomotopic_of_eq_one i u u' v v' h)

end Release075.BlockPresentation

namespace Release075.BlockPresentation
variable {I B : Type} {r : ℕ} (d : BlockPresentation I B r)

def vertexColor : d.Vertex ≃ Fin 3 where
  toFun | .o => 0 | .v => 1 | .w => 2
  invFun j := if j = 0 then .o else if j = 1 then .v else .w
  left_inv a := by cases a <;> rfl
  right_inv j := by fin_cases j <;> rfl

theorem TriangleFace.colors {a b c : d.OrientedEdge} (h : d.TriangleFace a b c) :
    d.edgeTarget a ≠ d.edgeTarget b ∧ d.edgeTarget b ≠ d.edgeTarget c ∧
    d.edgeTarget c ≠ d.edgeTarget a := by
  cases h <;> simp [orientedL,orientedX,orientedR,flipEdge,edgeTarget]

theorem TriangleFace.typed {a b c : d.OrientedEdge} (h : d.TriangleFace a b c) :
    d.edgeTarget (d.flipEdge b) = d.edgeTarget a ∧
    d.edgeTarget (d.flipEdge c) = d.edgeTarget b ∧
    d.edgeTarget (d.flipEdge a) = d.edgeTarget c := by
  cases h <;> simp [orientedL,orientedX,orientedR,flipEdge,edgeTarget]

theorem TriangleFace.unique_aux {a b c a' b' c' : d.OrientedEdge}
    (h : d.TriangleFace a b c) (h' : d.TriangleFace a' b' c')
    (ha : a = a') (hb : b = b') : c = c' := by
  cases h <;> cases h' <;>
    simp only [orientedL,orientedX,orientedR,flipEdge,Prod.mk.injEq,
      Sum.inl.injEq,Sum.inr.injEq,Sum.inl_ne_inr,Sum.inr_ne_inl,
      Bool.not_true,and_true,false_and] at ha hb ⊢
  all_goals
    first
    | have hbb := congrArg Sigma.fst ha; cases hbb
    | have hbb := congrArg Sigma.fst hb; cases hbb
  all_goals simp only [Sigma.mk.inj_iff,heq_eq_eq,Prod.mk.injEq,Subtype.val_inj,true_and] at ha hb ⊢
  case pos₀.pos₀ b i u v u' v' i' =>
    rcases hb with ⟨rfl,rfl,rfl⟩
    simp
  case pos₁.pos₁ b i u v u' v' i' =>
    rcases ha with ⟨rfl,rfl,rfl⟩
    simp
  case pos₂.pos₂ b i u v u' v' i' =>
    rcases ha with ⟨rfl,hβ⟩
    rcases hb with ⟨rfl,hα⟩
    have hi := (d.block b).coordinates.injective
      (Prod.ext (add_right_cancel hα) (add_right_cancel hβ))
    subst i'
    exact ⟨rfl,rfl,rfl⟩
  case neg₀.neg₀ b i u v u' v' i' =>
    rcases ha with ⟨rfl,hα⟩
    rcases hb with ⟨rfl,hβ⟩
    have hi := (d.block b).coordinates.injective
      (Prod.ext (add_right_cancel hα) (add_right_cancel hβ))
    subst i'
    exact ⟨rfl,rfl,rfl⟩
  case neg₁.neg₁ b i u v u' v' i' =>
    rcases hb with ⟨rfl,rfl,rfl⟩
    simp
  case neg₂.neg₂ b i u v u' v' i' =>
    rcases ha with ⟨rfl,rfl,rfl⟩
    simp

theorem TriangleFace.unique {a b c c' : d.OrientedEdge}
    (h : d.TriangleFace a b c) (h' : d.TriangleFace a b c') : c = c' :=
  TriangleFace.unique_aux d h h' rfl rfl

end Release075.BlockPresentation

end OAI
end
end

section
section
namespace OAI

namespace Release075.TriangleFilling
open Equiv PermCycles
attribute [local instance] Classical.propDecidable Classical.decEq
variable {E V : Type} {flip : E → E} {color : E → V} {face : E → E → E → Prop}

noncomputable def activeCount {w : List E} (D : TriangleFilling flip color face w) : ℕ :=
  (Finset.univ.filter D.Active).card

/-- The six oriented incidences of two faces which cancel across their common
edge. Outside partners may reconnect arbitrarily elsewhere in the filling. -/
structure Dipole {w : List E} (D : TriangleFilling flip color face w) where
  dart : Fin 6 ↪ D.Dart
  next_dart : ∀ j, D.next (dart j) = dart (dipoleFace j)
  reverse_zero : D.reverse (dart 0) = dart 3
  not_boundary : ∀ j, dart j ∉ D.boundary
  active : D.Active (dart 0)
  color10 : color (D.label (dart 1)) ≠ color (D.label (dart 0))
  color21 : color (D.label (dart 2)) ≠ color (D.label (dart 1))
  label51 : D.label (dart 5) = flip (D.label (dart 1))
  label42 : D.label (dart 4) = flip (D.label (dart 2))

/-- A labeled cancellation decreases the number of active darts. The isolated
pair remains harmlessly as a component disjoint from the prescribed boundary. -/
theorem Dipole.cancel {w : List E} {D : TriangleFilling flip color face w} (P : D.Dipole) :
    ∃ D' : TriangleFilling flip color face w, D'.activeCount < D.activeCount := by
  let e := P.dart
  have h14 : color (D.label (e 1)) = color (D.label (e 4)) := by
    have h := D.color_next (P.dart 1)
    simp only [Perm.mul_apply,P.next_dart,dipoleFace_one,D.reverse_label] at h
    exact h.symm.trans (congrArg color P.label42.symm)
  obtain ⟨r',hi',hn',hp',hc',he',heq,hm⟩ :=
    isolate_dipole D.reverse D.next D.reverse_involutive D.reverse_ne
      (color ∘ D.label) D.color_next e P.next_dart P.reverse_zero
      P.color10 P.color21 h14 D.planar
  have hl₁ : ∀ z, D.label (rePair D.reverse (e 1) (e 5) z) = flip (D.label z) :=
    rePair_labels D.reverse D.label flip D.reverse_label
      ((D.reverse_label (e 1)).trans P.label51.symm)
  have hl' : ∀ z, D.label (r' z) = flip (D.label z) := by
    rw [heq]
    exact rePair_labels _ D.label flip hl₁ ((hl₁ (e 2)).trans P.label42.symm)
  let D' : TriangleFilling flip color face w := {
    Dart := D.Dart
    reverse := r'
    next := D.next
    reverse_involutive := hi'
    reverse_ne := hn'
    label := D.label
    reverse_label := hl'
    color_next := hc'
    planar := hp'
    boundary := D.boundary
    boundary_cycle := D.boundary_cycle
    boundary_word := D.boundary_word
    triangular := by
      intro z hz hn
      obtain ⟨b,hb,hzb⟩ := hz
      exact D.triangular z ⟨b,hb,hm hzb⟩ hn }
  refine ⟨D',?_⟩
  have hle : ∀ z, D'.Active z → D.Active z := by
    rintro z ⟨b,hb,hzb⟩
    exact ⟨b,hb,hm hzb⟩
  have hnot : ¬ D'.Active (e 0) := by
    rintro ⟨b,hb,heb⟩
    have hmem : b ∈ Set.range e := (components_pred r' D.next (fun z => z ∈ Set.range e)
      (range_invariant r' dipoleReverse e he')
      (range_invariant D.next dipoleFace e P.next_dart) heb).mp ⟨0,rfl⟩
    obtain ⟨j,rfl⟩ := hmem
    exact P.not_boundary j hb
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  constructor
  · intro z hz
    simp only [Finset.mem_filter,Finset.mem_univ,true_and] at hz ⊢
    exact hle z hz
  · intro he
    have hmem : e 0 ∈ Finset.univ.filter D.Active := by
      simp only [Finset.mem_filter,Finset.mem_univ,true_and]
      exact P.active
    rw [← he] at hmem
    exact hnot (Finset.mem_filter.mp hmem).2

/-- Minimizing active size, not an assumed reduced-diagram axiom, produces a
filling with no cancellable adjacent labelled pair. -/
theorem exists_noDipole {w : List E} (h : Fillable flip color face w) :
    ∃ D : TriangleFilling flip color face w, IsEmpty D.Dipole := by
  have hex : ∃ n : ℕ, ∃ D : TriangleFilling flip color face w, D.activeCount = n := by
    obtain ⟨D⟩ := h
    exact ⟨D.activeCount,D,rfl⟩
  obtain ⟨D,hD⟩ := Nat.find_spec hex
  refine ⟨D,⟨fun P => ?_⟩⟩
  obtain ⟨D',hless⟩ := P.cancel
  have hmin := Nat.find_min' hex (show ∃ A : TriangleFilling flip color face w,
      A.activeCount = D'.activeCount from ⟨D',rfl⟩)
  omega

end Release075.TriangleFilling

namespace Release075.PermCycles
open Equiv
attribute [local instance] Classical.propDecidable Classical.decEq
variable {A : Type*} [Fintype A]

noncomputable def triangleEmbedding (f : Perm A) (a : A)
    (hp : (f^3) a = a) (hn : f a ≠ a) : Fin 3 ↪ A where
  toFun i := (f^i.val) a
  inj' := by
    intro i j h
    apply Fin.ext
    have hm : Function.minimalPeriod (f : A → A) a = 3 :=
      (orbit_card_eq_minimalPeriod f a).symm.trans (orbit_card_three f a hp hn)
    exact Function.iterate_injOn_Iio_minimalPeriod (f := (f : A → A))
      (x := a) (by rw [hm]; exact i.isLt) (by rw [hm]; exact j.isLt) h

noncomputable def trianglePairEmbedding (f : Perm A) (a b : A)
    (hpa : (f^3) a = a) (hna : f a ≠ a) (hpb : (f^3) b = b) (hnb : f b ≠ b)
    (hab : ¬ f.SameCycle a b) : Fin 6 ↪ A :=
  let ca := triangleEmbedding f a hpa hna
  let cb := triangleEmbedding f b hpb hnb
  let e : Fin 3 ⊕ Fin 3 ↪ A := {
    toFun := Sum.elim ca cb
    inj' := by
      intro i j h
      cases i with
      | inl i => cases j with
        | inl j => exact congrArg Sum.inl (ca.injective h)
        | inr j =>
          change ca i = cb j at h
          have hh : f.SameCycle a b := by
            have hi : f.SameCycle a (ca i) := (Perm.SameCycle.refl f a).pow_right
            have hj : f.SameCycle b (cb j) := (Perm.SameCycle.refl f b).pow_right
            exact hi.trans (by rw [h]; exact hj.symm)
          exact (hab hh).elim
      | inr i => cases j with
        | inl j =>
          change cb i = ca j at h
          have hh : f.SameCycle b a := by
            have hi : f.SameCycle b (cb i) := (Perm.SameCycle.refl f b).pow_right
            have hj : f.SameCycle a (ca j) := (Perm.SameCycle.refl f a).pow_right
            exact hi.trans (by rw [h]; exact hj.symm)
          exact (hab hh.symm).elim
        | inr j => exact congrArg Sum.inr (cb.injective h) }
  finSumFinEquiv.symm.toEmbedding.trans e

 theorem trianglePairEmbedding_values (f : Perm A) (a b : A)
    (hpa : (f^3) a = a) (hna : f a ≠ a) (hpb : (f^3) b = b) (hnb : f b ≠ b)
    (hab : ¬ f.SameCycle a b) :
    let e := trianglePairEmbedding f a b hpa hna hpb hnb hab
    e 0 = a ∧ e 1 = f a ∧ e 2 = (f^2) a ∧
    e 3 = b ∧ e 4 = f b ∧ e 5 = (f^2) b := by
  exact ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩

end Release075.PermCycles

namespace Release075.TriangleFilling
open Equiv PermCycles
attribute [local instance] Classical.propDecidable Classical.decEq
variable {E V : Type} {flip : E → E} {color : E → V} {face : E → E → E → Prop}
variable {w : List E} (D : TriangleFilling flip color face w)

/-- A genuinely triangular face cannot use both orientations of one geometric
edge: its three differently colored vertices and the endpoint matching forbid it. -/
theorem reverse_not_sameCycle (a : D.Dart) (ha : D.Active a) (hna : a ∉ D.boundary)
    (hf : ∀ a b c, face a b c → color a ≠ color b ∧ color b ≠ color c ∧ color c ≠ color a) :
    ¬ D.next.SameCycle a (D.reverse a) := by
  obtain ⟨hp,hn,hface⟩ := D.triangular a ha hna
  obtain ⟨h01,h12,h20⟩ := hf _ _ _ hface
  intro h
  have hm : D.reverse a ∈ orbit D.next a := (mem_orbit _ _ _).mpr h
  rw [orbit_eq_image D.next a (by omega : 0 < 3) hp] at hm
  obtain ⟨i,_,hi⟩ := Finset.mem_image.mp hm
  fin_cases i
  · exact D.reverse_ne a hi.symm
  · have h := D.color_next ((D.next^2) a)
    have h3 : D.next ((D.next^2) a) = a := by simpa only [pow_succ',Perm.mul_apply] using hp
    simp only [Perm.mul_apply,h3,← hi] at h
    exact h12 h
  · have h := D.color_next (D.next a)
    have hr : D.reverse ((D.next^2) a) = a := by rw [hi,D.reverse_involutive]
    change color (D.label (D.reverse ((D.next^2) a))) = color (D.label (D.next a)) at h
    rw [hr] at h
    exact h01 h

/-- Internal reversal of a link walk creates a cancellable pair, when the face
labels are determined by two consecutive sides. -/
theorem dipole_of_link_backtrack
    (hf : ∀ a b c, face a b c → color a ≠ color b ∧ color b ≠ color c ∧ color c ≠ color a)
    (hflip : ∀ e, flip (flip e) = e)
    (hmirror : ∀ a b c, face a b c → face (flip a) (flip c) (flip b))
    (hunique : ∀ a b c c', face a b c → face a b c' → c = c')
    (x : D.Dart) (hx : D.Active x) (hnx : x ∉ D.boundary)
    (hnb : (D.reverse*D.next) x ∉ D.boundary)
    (hback : D.label x = D.label ((D.reverse*D.next) ((D.reverse*D.next) x))) :
    Nonempty D.Dipole := by
  let a := D.next x
  let b := D.reverse a
  have ha : D.Active a := (D.active_next x).mpr hx
  have hna : a ∉ D.boundary := (D.boundary_cycle.not_mem_iff x).mpr hnx
  have hb : D.Active b := (D.active_reverse a).mpr ha
  obtain ⟨hp,hne,hfa⟩ := D.triangular a ha hna
  obtain ⟨hp',hne',hfb⟩ := D.triangular b hb hnb
  have hx3 := (D.triangular x hx hnx).1
  have hax : (D.next^2) a = x := by
    change (D.next^2) (D.next x) = x
    simpa only [pow_succ,Perm.mul_apply] using hx3
  have h42 : D.label (D.next b) = flip (D.label ((D.next^2) a)) := by
    have he : D.label x = flip (D.label (D.next b)) := hback.trans (D.reverse_label (D.next b))
    rw [hax,he,hflip]
  have h51 : D.label ((D.next^2) b) = flip (D.label (D.next a)) := by
    apply hunique (D.label b) (D.label (D.next b)) _ _ hfb
    rw [h42]
    change face (D.label (D.reverse a)) (flip (D.label ((D.next^2) a))) (flip (D.label (D.next a)))
    rw [D.reverse_label]
    exact hmirror _ _ _ hfa
  have hab : ¬ D.next.SameCycle a b := D.reverse_not_sameCycle a ha hna hf
  let e := trianglePairEmbedding D.next a b hp hne hp' hne' hab
  obtain ⟨he0,he1,he2,he3,he4,he5⟩ := trianglePairEmbedding_values D.next a b hp hne hp' hne' hab
  have hnext : ∀ j, D.next (e j) = e (dipoleFace j) := by
    have h3 : D.next ((D.next^2) a) = a := by simpa only [pow_succ',Perm.mul_apply] using hp
    have h3' : D.next ((D.next^2) b) = b := by simpa only [pow_succ',Perm.mul_apply] using hp'
    intro j
    fin_cases j <;> first | rfl | exact h3 | exact h3'
  have hnb' : b ∉ D.boundary := hnb
  have hn2a : (D.next^2) a ∉ D.boundary := by
    rw [hax]; exact hnx
  have hn1a : D.next a ∉ D.boundary := (D.boundary_cycle.not_mem_iff a).mpr hna
  have hn1b : D.next b ∉ D.boundary := (D.boundary_cycle.not_mem_iff b).mpr hnb'
  have hn2b : (D.next^2) b ∉ D.boundary :=
    (D.boundary_cycle.not_mem_iff (D.next b)).mpr hn1b
  obtain ⟨h01,h12,_⟩ := hf _ _ _ hfa
  refine ⟨{
    dart := e
    next_dart := hnext
    reverse_zero := by rw [he0,he3]
    not_boundary := by
      intro j
      fin_cases j <;> assumption
    active := by rw [he0]; exact ha
    color10 := by rw [he1,he0]; exact h01.symm
    color21 := by rw [he2,he1]; exact h12.symm
    label51 := by rw [he5,he1]; exact h51
    label42 := by rw [he4,he2]; exact h42 }⟩

theorem noDipole_link_reduced
    (hf : ∀ a b c, face a b c → color a ≠ color b ∧ color b ≠ color c ∧ color c ≠ color a)
    (hflip : ∀ e, flip (flip e) = e)
    (hmirror : ∀ a b c, face a b c → face (flip a) (flip c) (flip b))
    (hunique : ∀ a b c c', face a b c → face a b c' → c = c')
    (hD : IsEmpty D.Dipole)
    (x : D.Dart) (hx : D.Active x) (hnx : x ∉ D.boundary)
    (hnb : (D.reverse*D.next) x ∉ D.boundary) :
    D.label x ≠ D.label ((D.reverse*D.next) ((D.reverse*D.next) x)) := by
  intro h
  obtain ⟨P⟩ := D.dipole_of_link_backtrack hf hflip hmirror hunique x hx hnx hnb h
  exact hD.false P

end Release075.TriangleFilling

namespace Release075
namespace CyclicLink
variable {A V : Type*} {G : SimpleGraph V}

/-- The actual link walk traced by successive corners, without assuming its image
is simple. This is why reduced closed walks, rather than only cycles, are needed. -/
def walk (f : A → A) (label : A → V) (adj : ∀ a, G.Adj (label a) (label (f a)))
    (n : ℕ) (a : A) : G.Walk (label a) (label (f^[n] a)) :=
  match n with
  | 0 => .nil
  | n+1 => (walk f label adj n (f a)).cons (adj a)

@[simp] theorem length_walk (f : A → A) (label : A → V)
    (adj : ∀ a, G.Adj (label a) (label (f a))) (n : ℕ) (a : A) :
    (walk f label adj n a).length = n := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih => simp [walk,ih]

theorem getVert_walk (f : A → A) (label : A → V)
    (adj : ∀ a, G.Adj (label a) (label (f a))) (n : ℕ) (a : A)
    (i : ℕ) (hi : i ≤ n) : (walk f label adj n a).getVert i = label (f^[i] a) := by
  induction n generalizing a i with
  | zero =>
    have : i = 0 := by omega
    subst i
    rfl
  | succ n ih =>
    cases i with
    | zero => rfl
    | succ i =>
      simpa only [walk,SimpleGraph.Walk.getVert_cons_succ,Function.iterate_succ_apply]
        using ih (f a) i (by omega)

theorem reduced_walk (f : A → A) (label : A → V)
    (adj : ∀ a, G.Adj (label a) (label (f a)))
    (reduced : ∀ a, label a ≠ label (f (f a))) (n : ℕ) (a : A) :
    ReducedWalk (walk f label adj n a) := by
  intro i hi he
  simp only [length_walk] at hi
  rw [getVert_walk _ _ _ _ _ _ (by omega),getVert_walk _ _ _ _ _ _ hi] at he
  apply reduced (f^[i] a)
  simpa only [show i+2 = (i+1)+1 by omega,Function.iterate_succ_apply'] using he

/-- A finite corner orbit mapping without link reversals has at least the link's
actual girth. No injectivity of the whole orbit image is needed. -/
theorem orbit_card_ge [Fintype A] (f : Equiv.Perm A) (label : A → V)
    (adj : ∀ a, G.Adj (label a) (label (f a)))
    (reduced : ∀ a, label a ≠ label (f (f a)))
    (k : ℕ) (hgirth : ∀ v (p : G.Walk v v), p.IsCycle → k ≤ p.length) (a : A) :
    k ≤ (PermCycles.orbit f a).card := by
  rw [PermCycles.orbit_card_eq_minimalPeriod]
  let n := Function.minimalPeriod (f : A → A) a
  have hn : 0 < n := PermCycles.minimalPeriod_pos f a
  have hp : f^[n] a = a := Function.iterate_minimalPeriod
  let p := (walk f label adj n a).copy rfl (congrArg label hp)
  have hr : ReducedWalk p := by
    intro i hi
    simpa only [p,SimpleGraph.Walk.length_copy,SimpleGraph.Walk.getVert_copy] using
      reduced_walk f label adj reduced n a i (by simpa only [p,SimpleGraph.Walk.length_copy] using hi)
  have hh := reduced_closed_length_ge k hgirth p (by simpa [p] using hn) hr
  simpa [p] using hh

end CyclicLink
end Release075

end OAI
end
end

section
section
namespace OAI

namespace Release075
open scoped BigOperators

/-- The numerical incidence identities of a nonempty planar triangle disk, with
boundary visits counted with multiplicity (including both sides of naked edges).
All fields are finite counts or angle data. No group conclusion is assumed. -/
structure AngleDiskCounts where
  Vertex : Type
  [vertexFintype : Fintype Vertex]
  edges : ℕ
  faces : ℕ
  visits : Vertex → ℕ
  angles : Vertex → ℝ
  angles_nonneg : ∀ v, 0 ≤ angles v
  euler : Fintype.card Vertex + faces = edges + 1
  exterior : (∑ v, visits v) + 3*faces = 2*edges
  angle_sum : (∑ v, angles v) = 5*faces

attribute [instance] AngleDiskCounts.vertexFintype
namespace AngleDiskCounts
variable (D : AngleDiskCounts)

def curvature (v : D.Vertex) : ℝ := 10 - 5*(D.visits v) - D.angles v

/-- Gauss--Bonnet includes repeated boundary visits and naked edges. -/
theorem gauss_bonnet : ∑ v, D.curvature v = 10 := by
  have he : (Fintype.card D.Vertex : ℝ) + D.faces = D.edges + 1 := by exact_mod_cast D.euler
  have hb : (∑ v, (D.visits v : ℝ)) + 3*D.faces = 2*D.edges := by exact_mod_cast D.exterior
  simp only [curvature,Finset.sum_sub_distrib,Finset.sum_const,Finset.card_univ,
    nsmul_eq_mul,← Finset.mul_sum]
  linarith [D.angle_sum]

/-- Curvature obstruction for a boundary all of whose cyclic turns have link
length >=π: an interior reduced link contributes >=2π and a single exterior
visit contributes >=π. Multiple visits require no turn estimate. -/
theorem cannot_have_geodesic_boundary
    (hinterior : ∀ v, D.visits v = 0 → 10 ≤ D.angles v)
    (hboundary : ∀ v, D.visits v = 1 → 5 ≤ D.angles v) : False := by
  have hnonpos (v : D.Vertex) : D.curvature v ≤ 0 := by
    by_cases h0 : D.visits v = 0
    · have h := hinterior v h0
      simp only [curvature,h0,Nat.cast_zero,mul_zero,sub_zero]
      linarith
    by_cases h1 : D.visits v = 1
    · have h := hboundary v h1
      simp only [curvature,h1,Nat.cast_one,mul_one]
      linarith
    · have h2 : (2 : ℝ) ≤ D.visits v := by exact_mod_cast (show 2 ≤ D.visits v by omega)
      have ha := D.angles_nonneg v
      dsimp [curvature]
      linarith
  have hs : (∑ v, D.curvature v) ≤ 0 := Finset.sum_nonpos (fun v _ => hnonpos v)
  rw [D.gauss_bonnet] at hs
  norm_num at hs

noncomputable def interior : Finset D.Vertex := by
  classical
  exact Finset.univ.filter (fun v => D.visits v = 0)

noncomputable def boundary : Finset D.Vertex := by
  classical
  exact Finset.univ.filter (fun v => D.visits v ≠ 0)

def boundaryLength : ℕ := ∑ v, D.visits v

theorem vertices_partition : D.interior.card + D.boundary.card = Fintype.card D.Vertex := by
  classical
  simpa only [interior,boundary,Finset.card_univ] using
    Finset.card_filter_add_card_filter_not (s := Finset.univ) (fun v => D.visits v = 0)

theorem boundary_card_le_length : D.boundary.card ≤ D.boundaryLength := by
  classical
  calc
    D.boundary.card = ∑ v ∈ D.boundary, 1 := by simp
    _ ≤ ∑ v ∈ D.boundary, D.visits v := by
      apply Finset.sum_le_sum
      intro v hv
      have h : D.visits v ≠ 0 := (Finset.mem_filter.mp hv).2
      omega
    _ ≤ D.boundaryLength := Finset.sum_le_sum_of_subset (Finset.subset_univ _)

/-- The Euler/incidence formula in terms of interior and boundary vertices. -/
theorem face_vertex_formula :
    D.faces + D.boundaryLength + 2 = 2*D.interior.card + 2*D.boundary.card := by
  have he := D.euler
  have hb := D.exterior
  have hp := D.vertices_partition
  change D.boundaryLength + 3*D.faces = 2*D.edges at hb
  omega

theorem linear_face_bound
    (hinterior : ∀ v, D.visits v = 0 → 12 ≤ D.angles v) :
    D.faces + 12 ≤ 6*D.boundaryLength := by
  classical
  have ha : (12 : ℝ)*D.interior.card ≤ 5*D.faces := by
    calc
      (12 : ℝ)*D.interior.card = ∑ _v ∈ D.interior, (12 : ℝ) := by simp [mul_comm]
      _ ≤ ∑ v ∈ D.interior, D.angles v := by
        apply Finset.sum_le_sum
        intro v hv
        exact hinterior v (Finset.mem_filter.mp hv).2
      _ ≤ ∑ v, D.angles v := Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.subset_univ _) (fun v _ _ => D.angles_nonneg v)
      _ = 5*D.faces := D.angle_sum
  have ha' : 12*D.interior.card ≤ 5*D.faces := by exact_mod_cast ha
  have hp := D.face_vertex_formula
  have hb := D.boundary_card_le_length
  omega

/-- For a simple geodesic polygon only its designated corners can contribute
positive boundary curvature. Original interior vertices cost two angle units.
This is the exact quantitative count used for uniform inradius. -/
theorem polygon_original_vertex_bound (original corners : Finset D.Vertex)
    (hvisits : ∀ v, D.visits v ≤ 1)
    (hcorner : ∀ v ∈ corners, D.visits v = 1)
    (horiginal : ∀ v ∈ original, D.visits v = 0)
    (hstrict : ∀ v ∈ original, 12 ≤ D.angles v)
    (hinterior : ∀ v, D.visits v = 0 → 10 ≤ D.angles v)
    (hboundary : ∀ v, D.visits v = 1 → v ∉ corners → 5 ≤ D.angles v) :
    2*(original.card : ℝ) + 10 ≤ 5*corners.card := by
  classical
  have hpoint (v : D.Vertex) : D.curvature v ≤
      (if v ∈ corners then (5 : ℝ) else 0) - (if v ∈ original then 2 else 0) := by
    by_cases ho : v ∈ original
    · have hv := horiginal v ho
      have ha := hstrict v ho
      have hc : v ∉ corners := by intro hc; have := hcorner v hc; omega
      simp only [curvature,hv,Nat.cast_zero,mul_zero,sub_zero,ite_eq_right hc,ite_eq_left ho]
      linarith
    · by_cases hc : v ∈ corners
      · have hv := hcorner v hc
        have ha := D.angles_nonneg v
        simp only [curvature,hv,Nat.cast_one,mul_one,ite_eq_left hc,ite_eq_right ho,sub_zero]
        linarith
      · simp only [ite_eq_right hc,ite_eq_right ho,sub_zero]
        rcases Nat.le_one_iff_eq_zero_or_eq_one.mp (hvisits v) with hv | hv
        · have ha := hinterior v hv
          simp only [curvature,hv,Nat.cast_zero,mul_zero,sub_zero]
          linarith
        · have ha := hboundary v hv hc
          simp only [curvature,hv,Nat.cast_one,mul_one]
          linarith
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun v _ => hpoint v)
  rw [D.gauss_bonnet,Finset.sum_sub_distrib] at hs
  have hc : (∑ v : D.Vertex, if v ∈ corners then (5 : ℝ) else 0) = 5*corners.card := by
    rw [← Finset.sum_filter]
    have he : Finset.univ.filter (· ∈ corners) = corners := by ext; simp
    simp [he,mul_comm]
  have ho : (∑ v : D.Vertex, if v ∈ original then (2 : ℝ) else 0) = 2*original.card := by
    rw [← Finset.sum_filter]
    have he : Finset.univ.filter (· ∈ original) = original := by ext; simp
    simp [he,mul_comm]
  rw [hc,ho] at hs
  linarith

end AngleDiskCounts
end Release075

namespace Release075
open scoped BigOperators
open Equiv PermCycles
attribute [local instance] Classical.propDecidable Classical.decEq

/-- An oriented combinatorial triangle filling. Darts are incoming at the
corner they carry; `reverse * face` rotates those corners about a vertex.
This records finite incidence data, NOT existence of a filling for a nullword.
Its single distinguished face is the prescribed exterior walk, including spurs. -/
structure TriangleRibbon where
  Dart : Type
  [dartFintype : Fintype Dart]
  reverse : Perm Dart
  face : Perm Dart
  reverse_involution : Function.Involutive reverse
  reverse_ne : ∀ d, reverse d ≠ d
  outer : Cycles face
  color : Cycles (reverse * face) → Fin 3
  face_colors : ∀ c : Cycles face, c ≠ outer →
    Function.Bijective (fun d : {d : Dart // cl face d = c} => color (cl (reverse * face) d))
  euler : Fintype.card (Cycles (reverse * face)) +
      Fintype.card {c : Cycles face // c ≠ outer} = Fintype.card (Cycles reverse) + 1
attribute [instance] TriangleRibbon.dartFintype

namespace TriangleRibbon
variable (R : TriangleRibbon)
abbrev vertexPerm := R.reverse * R.face
abbrev Vertex := Cycles R.vertexPerm
abbrev Edge := Cycles R.reverse
abbrev Face := {c : Cycles R.face // c ≠ R.outer}

noncomputable def weight (c : Fin 3) : ℝ := if c = 0 then 3 else 1

noncomputable def cornerAngle (d : R.Dart) : ℝ :=
  if cl R.face d = R.outer then 0 else weight (R.color (cl R.vertexPerm d))

noncomputable def visits (v : R.Vertex) : ℕ :=
  ∑ d : R.Dart, if cl R.vertexPerm d = v ∧ cl R.face d = R.outer then 1 else 0

noncomputable def angles (v : R.Vertex) : ℝ :=
  ∑ d : R.Dart, if cl R.vertexPerm d = v then R.cornerAngle d else 0

@[simp] theorem cornerAngle_nonneg (d : R.Dart) : 0 ≤ R.cornerAngle d := by
  dsimp [cornerAngle,weight]
  split_ifs <;> norm_num

theorem angles_nonneg (v : R.Vertex) : 0 ≤ R.angles v := by
  apply Finset.sum_nonneg
  intro d _
  split_ifs
  · exact R.cornerAngle_nonneg d
  · rfl

theorem card_face_fiber (c : Cycles R.face) (hc : c ≠ R.outer) :
    Fintype.card {d : R.Dart // cl R.face d = c} = 3 := by
  have h := Fintype.card_congr (Equiv.ofBijective _ (R.face_colors c hc))
  simpa only [Fintype.card_fin] using h

theorem face_angle_sum (c : Cycles R.face) (hc : c ≠ R.outer) :
    (∑ d : {d : R.Dart // cl R.face d = c}, R.cornerAngle d) = 5 := by
  have hh : (∑ d : {d : R.Dart // cl R.face d = c},
      weight (R.color (cl R.vertexPerm d))) = ∑ i : Fin 3, weight i :=
    (Equiv.ofBijective _ (R.face_colors c hc)).sum_comp weight
  have he (d : {d : R.Dart // cl R.face d = c}) : R.cornerAngle d =
      weight (R.color (cl R.vertexPerm d)) := by
    simp only [cornerAngle,d.property,ite_eq_right hc]
  simp only [he]
  rw [hh]
  norm_num [Fin.sum_univ_succ,weight]

theorem dart_card : Fintype.card R.Dart = 2 * Fintype.card R.Edge :=
  card_eq_mul_cycles R.reverse 2 (orbit_card_involution R.reverse R.reverse_involution R.reverse_ne)

theorem visits_sum : (∑ v : R.Vertex, R.visits v) =
    Fintype.card {d : R.Dart // cl R.face d = R.outer} := by
  simp only [visits]
  rw [Finset.sum_comm]
  have hs (d : R.Dart) :
      (∑ v : R.Vertex, if cl R.vertexPerm d = v ∧ cl R.face d = R.outer then 1 else 0) =
      if cl R.face d = R.outer then 1 else 0 := by
    by_cases h : cl R.face d = R.outer <;> simp [h]
  simp only [hs]
  rw [← Finset.card_filter]
  exact (Fintype.card_subtype _).symm

theorem exterior_count : (∑ v : R.Vertex, R.visits v) + 3 * Fintype.card R.Face =
    2 * Fintype.card R.Edge := by
  rw [R.visits_sum,← R.dart_card,← sum_card_fibers R.face,
    Fintype.sum_eq_add_sum_subtype_ne _ R.outer]
  congr 1
  have h3 (c : R.Face) : Fintype.card {d : R.Dart // cl R.face d = c.val} = 3 :=
    R.card_face_fiber c.val c.property
  simp only [h3,Finset.sum_const,Finset.card_univ,smul_eq_mul,mul_comm]

theorem all_angles_sum : (∑ v : R.Vertex, R.angles v) = 5 * Fintype.card R.Face := by
  simp only [angles]
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq,Finset.mem_univ,ite_true]
  have hh : (∑ c : Cycles R.face, ∑ d : {d : R.Dart // cl R.face d = c},
      R.cornerAngle d) = ∑ d : R.Dart, R.cornerAngle d := by
    simpa only [Fintype.sum_sigma, Equiv.sigmaFiberEquiv_apply] using
      (Equiv.sigmaFiberEquiv (cl R.face)).sum_comp R.cornerAngle
  rw [← hh,Fintype.sum_eq_add_sum_subtype_ne _ R.outer]
  have h0 : (∑ d : {d : R.Dart // cl R.face d = R.outer}, R.cornerAngle d) = 0 := by
    apply Finset.sum_eq_zero
    intro d _
    simp [cornerAngle,d.property]
  rw [h0,zero_add]
  have h5 (c : R.Face) : (∑ d : {d : R.Dart // cl R.face d = c.val}, R.cornerAngle d) = 5 :=
    R.face_angle_sum c.val c.property
  simp only [h5,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_comm]

/-- All arithmetic hypotheses of the earlier curvature identity are now derived
from actual edge/face/vertex permutations and face-color bijections. -/
noncomputable def counts : AngleDiskCounts where
  Vertex := R.Vertex
  edges := Fintype.card R.Edge
  faces := Fintype.card R.Face
  visits := R.visits
  angles := R.angles
  angles_nonneg := R.angles_nonneg
  euler := R.euler
  exterior := R.exterior_count
  angle_sum := R.all_angles_sum

end TriangleRibbon
end Release075

namespace Release075.SumWalk
variable {U V : Type*} {G : SimpleGraph U} {H : SimpleGraph V}

/-- Forget the disjoint summand tag from a walk in the left component. -/
def left {a b : U} : (G.sum H).Walk (.inl a) (.inl b) → G.Walk a b
  | .nil => .nil
  | .cons (v := .inl _) h p => (left p).cons (SimpleGraph.sum_adj_inl.mp h)
  | .cons (v := .inr _) h _ => by simp at h

@[simp] theorem left_length {a b : U} (p : (G.sum H).Walk (.inl a) (.inl b)) :
    (left p).length = p.length := by
  fun_induction left p <;> simp_all only [SimpleGraph.Walk.length_cons,SimpleGraph.Walk.length_nil]

@[simp] theorem map_left {a b : U} (p : (G.sum H).Walk (.inl a) (.inl b)) :
    (left p).map SimpleGraph.Embedding.sumInl.toHom = p := by
  fun_induction left p <;> simp_all only [SimpleGraph.Walk.map_cons,SimpleGraph.Walk.map_nil] <;> rfl

 theorem left_reduced {a b : U} {p : (G.sum H).Walk (.inl a) (.inl b)}
    (hp : ReducedWalk p) : ReducedWalk (left p) := by
  intro i hi heq
  apply hp i (by simpa only [left_length] using hi)
  have hh := congrArg (fun x : U => (Sum.inl x : U ⊕ V)) heq
  have hm (j : ℕ) : Sum.inl ((left p).getVert j) = p.getVert j := by
    have h := SimpleGraph.Walk.getVert_map (SimpleGraph.Embedding.sumInl (G := G) (H := H)).toHom (left p) j
    rw [map_left p] at h
    exact h.symm
  simpa only [hm] using hh

/-- The right-component extraction is left extraction after the graph sum swap. -/
def right {a b : V} (p : (G.sum H).Walk (.inr a) (.inr b)) : H.Walk a b :=
  left (p.map SimpleGraph.Iso.sumComm.toHom)

@[simp] theorem right_length {a b : V} (p : (G.sum H).Walk (.inr a) (.inr b)) :
    (right p).length = p.length :=
  (left_length _).trans (SimpleGraph.Walk.length_map _ _)

 theorem right_reduced {a b : V} {p : (G.sum H).Walk (.inr a) (.inr b)}
    (hp : ReducedWalk p) : ReducedWalk (right p) := by
  apply left_reduced
  exact hp.map _ (fun _ _ _ _ _ h => SimpleGraph.Iso.sumComm.injective h)

end Release075.SumWalk

namespace Release075
open Equiv PermCycles
attribute [local instance] Classical.propDecidable Classical.decEq
variable {A : Type*} [Fintype A]

theorem IsBoundary.sameCycle {f : Perm A} {l : List A} (h : IsBoundary f l)
    {a b : A} (ha : a ∈ l) (hb : b ∈ l) : f.SameCycle a b := by
  by_cases hab : a = b
  · subst b; exact .refl _ _
  have hlen : 2 ≤ l.length := by
    cases l with
    | nil => simp at ha
    | cons x xs =>
      cases xs with
      | nil => simp_all
      | cons y ys => simp
  have hform : l.formPerm.SameCycle a b :=
    (List.isCycle_formPerm h.1 hlen).sameCycle
      ((List.formPerm_apply_mem_ne_self_iff l h.1 a ha).mpr hlen)
      ((List.formPerm_apply_mem_ne_self_iff l h.1 b hb).mpr hlen)
  apply sameCycle_le_of_step l.formPerm (Perm.SameCycle.setoid f) _ hform
  intro x
  by_cases hx : x ∈ l
  · rw [← h.2 x hx]
    exact (Perm.SameCycle.refl f x).apply_right
  · rw [List.formPerm_apply_of_notMem hx]

theorem IsBoundary.mem_iff_sameCycle {f : Perm A} {l : List A} (h : IsBoundary f l)
    {b : A} (hb : b ∈ l) (a : A) : a ∈ l ↔ f.SameCycle a b := by
  refine ⟨fun ha => h.sameCycle ha hb,fun hh => ?_⟩
  exact (invariant_pred_sameCycle f (· ∈ l) h.mem_iff hh).mpr hb

end Release075

namespace Release075.PermCycles
open Equiv
attribute [local instance] Classical.propDecidable Classical.decEq
variable {A : Type*} [Fintype A]

theorem three_color_bijective (f : Perm A) (a : A) (q : A → Fin 3)
    (hp : (f^3) a = a) (hne : f a ≠ a)
    (hab : q a ≠ q (f a)) (hbc : q (f a) ≠ q ((f^2) a))
    (hca : q ((f^2) a) ≠ q a) :
    Function.Bijective (fun x : {x : A // cl f x = cl f a} => q x) := by
  apply (Fintype.bijective_iff_injective_and_card _).mpr
  constructor
  · intro x y hxy
    have hx : x.val ∈ orbit f a := (mem_orbit f a x).mpr ((cl_eq_iff f _ _).mp x.property).symm
    have hy : y.val ∈ orbit f a := (mem_orbit f a y).mpr ((cl_eq_iff f _ _).mp y.property).symm
    rw [orbit_eq_image f a (by omega : 0 < 3) hp] at hx hy
    obtain ⟨i,_,hi⟩ := Finset.mem_image.mp hx
    obtain ⟨j,_,hj⟩ := Finset.mem_image.mp hy
    apply Subtype.ext
    rw [← hi,← hj]
    change q x.val = q y.val at hxy
    rw [← hi,← hj] at hxy
    fin_cases i <;> fin_cases j <;>
      norm_num only [pow_zero,pow_one,Perm.one_apply] at hxy ⊢
    all_goals first | exact (hab hxy).elim | exact (hab hxy.symm).elim |
      exact (hbc hxy).elim | exact (hbc hxy.symm).elim |
      exact (hca hxy).elim | exact (hca hxy.symm).elim
  · rw [card_fiber,orbit_card_three f a hp hne,Fintype.card_fin]

end Release075.PermCycles

namespace Release075.TriangleFilling
open Equiv PermCycles
attribute [local instance] Classical.propDecidable Classical.decEq
variable {E V : Type} {flip : E → E} {color : E → V} {face : E → E → E → Prop}
variable {w : List E} (D : TriangleFilling flip color face w)

abbrev ActiveDart := {a : D.Dart // D.Active a}
noncomputable def activeReverse : Perm D.ActiveDart := D.reverse.subtypePerm D.active_reverse
noncomputable def activeNext : Perm D.ActiveDart := D.next.subtypePerm D.active_next

@[simp] theorem activeReverse_val (a : D.ActiveDart) : (D.activeReverse a).val = D.reverse a := rfl
@[simp] theorem activeNext_val (a : D.ActiveDart) : (D.activeNext a).val = D.next a := rfl

 theorem activeReverse_involutive : Function.Involutive D.activeReverse := by
  intro a
  apply Subtype.ext
  exact D.reverse_involutive a

 theorem activeReverse_ne (a : D.ActiveDart) : D.activeReverse a ≠ a := by
  intro h
  exact D.reverse_ne a (congrArg Subtype.val h)

 theorem active_planar : PlanarMap D.activeReverse D.activeNext :=
  D.planar.restrict D.Active D.active_reverse D.active_next

 theorem active_components (a b : D.ActiveDart) :
    components D.activeReverse D.activeNext a b := by
  rw [activeReverse,activeNext,components_subtype]
  obtain ⟨x,hx,hax⟩ := a.property
  obtain ⟨y,hy,hby⟩ := b.property
  have hxy : components D.reverse D.next x y :=
    (show Perm.SameCycle.setoid D.next ≤ components D.reverse D.next from le_sup_right)
      (D.boundary_cycle.sameCycle hx hy)
  exact (components D.reverse D.next).trans hax
    ((components D.reverse D.next).trans hxy ((components D.reverse D.next).symm hby))

 theorem active_componentCount {b : D.Dart} (hb : b ∈ D.boundary) :
    componentCount D.activeReverse D.activeNext = 1 := by
  apply Nat.card_eq_one_iff_unique.mpr
  constructor
  · refine ⟨?_⟩
    intro x y
    induction x using Quotient.inductionOn with | h x =>
      induction y using Quotient.inductionOn with | h y =>
        exact Quotient.sound (D.active_components x y)
  · exact ⟨Quotient.mk _ ⟨b,D.active_of_mem hb⟩⟩

 theorem active_color_step (q : V → Fin 3) (a : D.ActiveDart) :
    q (color (D.label ((D.activeReverse*D.activeNext) a))) = q (color (D.label a)) :=
  congrArg q (D.color_next a)

noncomputable def activeColor (q : V → Fin 3) : Cycles (D.activeReverse*D.activeNext) → Fin 3 :=
  descend _ (fun a => q (color (D.label a))) (D.active_color_step q)

 theorem active_boundary_iff {b : D.Dart} (hb : b ∈ D.boundary) (a : D.ActiveDart) :
    cl D.activeNext a = cl D.activeNext ⟨b,D.active_of_mem hb⟩ ↔ a.val ∈ D.boundary := by
  rw [cl_eq_iff,activeNext,Perm.sameCycle_subtypePerm]
  exact (D.boundary_cycle.mem_iff_sameCycle hb a.val).symm

/-- A nonempty labeled filling has its connected boundary component as an actual
Euler-characteristic-one triangle ribbon. No geometric embedding is postulated. -/
noncomputable def ribbon (q : V ≃ Fin 3)
    (hf : ∀ a b c, face a b c → color a ≠ color b ∧ color b ≠ color c ∧ color c ≠ color a)
    (b : D.Dart) (hb : b ∈ D.boundary) : TriangleRibbon where
  Dart := D.ActiveDart
  reverse := D.activeReverse
  face := D.activeNext
  reverse_involution := D.activeReverse_involutive
  reverse_ne := D.activeReverse_ne
  outer := cl D.activeNext ⟨b,D.active_of_mem hb⟩
  color := D.activeColor q
  face_colors := by
    intro c hc
    obtain ⟨a,rfl⟩ := cl_surjective D.activeNext c
    have ha : a.val ∉ D.boundary := fun h => hc ((D.active_boundary_iff hb a).mpr h)
    obtain ⟨hp,hn,hface⟩ := D.triangular a a.property ha
    obtain ⟨h01,h12,h20⟩ := hf _ _ _ hface
    have hp' : (D.activeNext^3) a = a := by
      apply Subtype.ext
      exact hp
    have hn' : D.activeNext a ≠ a := fun h => hn (congrArg Subtype.val h)
    exact three_color_bijective D.activeNext a (fun x => q (color (D.label x))) hp' hn'
      (fun h => h01 (q.injective h)) (fun h => h12 (q.injective h))
      (fun h => h20 (q.injective h))
  euler := by
    have hp := D.active_planar
    have hr := card_eq_mul_cycles D.activeReverse 2
      (orbit_card_involution D.activeReverse D.activeReverse_involutive D.activeReverse_ne)
    have hc := D.active_componentCount hb
    have hf' := card_subtype_ne_add_one (cl D.activeNext ⟨b,D.active_of_mem hb⟩)
    simp only [PlanarMap,cycleCount,Nat.card_eq_fintype_card] at hp hc hf'
    omega

end Release075.TriangleFilling

namespace Release075.SequenceWalk
variable {E : Type*} (L : SimpleGraph E)

def walk (a : ℕ → E) : (n : ℕ) → (∀ i, i < n → L.Adj (a i) (a (i+1))) → L.Walk (a 0) (a n)
  | 0, _ => .nil
  | n+1, h => (walk (fun i => a (i+1)) n (fun i hi => h (i+1) (by omega))).cons (h 0 (by omega))

@[simp] theorem length_walk (a : ℕ → E) (n : ℕ) (h) : (walk L a n h).length = n := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih => simp only [walk,SimpleGraph.Walk.length_cons,ih]

theorem getVert_walk (a : ℕ → E) (n : ℕ) (h) (i : ℕ) (hi : i ≤ n) :
    (walk L a n h).getVert i = a i := by
  induction n generalizing a i with
  | zero => have : i = 0 := by omega
            subst i
            rfl
  | succ n ih =>
    cases i with
    | zero => rfl
    | succ i => exact ih (fun j => a (j+1)) _ i (by omega)

theorem reduced_walk (a : ℕ → E) (n : ℕ) (h)
    (hr : ∀ i, i+2 ≤ n → a i ≠ a (i+2)) : ReducedWalk (walk L a n h) := by
  intro i hi
  simp only [length_walk] at hi
  rw [getVert_walk L a n h i (by omega),getVert_walk L a n h (i+2) hi]
  exact hr i hi

end Release075.SequenceWalk

namespace Release075.PermCycles
open Equiv
attribute [local instance] Classical.propDecidable Classical.decEq
variable {A : Type*} [Fintype A]

theorem class_filter (f : Perm A) (a : A) :
    Finset.univ.filter (fun d => cl f d = cl f a) = orbit f a := by
  ext d
  simp only [Finset.mem_filter,Finset.mem_univ,true_and,cl_eq_iff,mem_orbit,Perm.sameCycle_comm]

theorem pow_card_orbit (f : Perm A) (a : A) : (f^(orbit f a).card) a = a := by
  rw [orbit_card_eq_minimalPeriod]
  exact Function.iterate_minimalPeriod

theorem pow_ne_of_lt_card_orbit (f : Perm A) (a : A) (n : ℕ)
    (hn : 0 < n) (hlt : n < (orbit f a).card) : (f^n) a ≠ a := by
  intro h
  rw [orbit_card_eq_minimalPeriod] at hlt
  have hz : 0 < Function.minimalPeriod (f : A → A) a := minimalPeriod_pos f a
  have hh : n = 0 := Function.iterate_injOn_Iio_minimalPeriod (f := (f : A → A))
    (x := a) hlt hz h
  omega

end Release075.PermCycles

namespace Release075.TriangleRibbon
open Equiv PermCycles
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq
variable (R : TriangleRibbon)

def IsOuter (a : R.Dart) : Prop := cl R.face a = R.outer

noncomputable def outerCorners (a : R.Dart) : Finset R.Dart :=
  (orbit R.vertexPerm a).filter R.IsOuter
noncomputable def innerCorners (a : R.Dart) : Finset R.Dart :=
  (orbit R.vertexPerm a).filter (fun b => ¬ R.IsOuter b)

theorem visits_cl (a : R.Dart) : R.visits (cl R.vertexPerm a) = (R.outerCorners a).card := by
  unfold visits outerCorners IsOuter
  rw [← class_filter,Finset.filter_filter,Finset.card_filter]
  apply Finset.sum_congr rfl
  intro d _
  split_ifs <;> rfl

theorem angles_cl (a : R.Dart) :
    R.angles (cl R.vertexPerm a) = weight (R.color (cl R.vertexPerm a)) * (R.innerCorners a).card := by
  have hs : R.angles (cl R.vertexPerm a) =
      ∑ d ∈ R.innerCorners a, weight (R.color (cl R.vertexPerm a)) := by
    rw [angles,innerCorners,← class_filter,Finset.filter_filter,Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro d _
    simp only [cornerAngle,IsOuter]
    by_cases h : cl R.vertexPerm d = cl R.vertexPerm a <;>
      by_cases ho : cl R.face d = R.outer <;> simp [h,ho]
  rw [hs]
  simp only [Finset.sum_const,nsmul_eq_mul,mul_comm]

theorem corner_count (a : R.Dart) :
    (R.innerCorners a).card + (R.outerCorners a).card = (orbit R.vertexPerm a).card := by
  have h := Finset.card_filter_add_card_filter_not (s := orbit R.vertexPerm a) R.IsOuter
  change (R.outerCorners a).card + (R.innerCorners a).card = _ at h
  omega

theorem no_outer_of_visits_zero (a : R.Dart) (h : R.visits (cl R.vertexPerm a) = 0)
    {b : R.Dart} (hb : R.vertexPerm.SameCycle a b) : ¬ R.IsOuter b := by
  intro ho
  rw [R.visits_cl,Finset.card_eq_zero] at h
  have hm : b ∈ R.outerCorners a := Finset.mem_filter.mpr ⟨(mem_orbit _ _ _).mpr hb,ho⟩
  rw [h] at hm
  exact Finset.notMem_empty _ hm

theorem unique_outer_of_visits_one (a : R.Dart) (ha : R.IsOuter a)
    (h : R.visits (cl R.vertexPerm a) = 1) {b : R.Dart}
    (hb : R.vertexPerm.SameCycle a b) (ho : R.IsOuter b) : b = a := by
  rw [R.visits_cl,Finset.card_eq_one] at h
  obtain ⟨c,hc⟩ := h
  have hma : a ∈ R.outerCorners a := Finset.mem_filter.mpr ⟨(mem_orbit _ _ _).mpr (.refl _ _),ha⟩
  have hmb : b ∈ R.outerCorners a := Finset.mem_filter.mpr ⟨(mem_orbit _ _ _).mpr hb,ho⟩
  rw [hc,Finset.mem_singleton] at hma hmb
  exact hmb.trans hma.symm

variable {E : Type*} (L : SimpleGraph E) (label : R.Dart → E)
variable (hadj : ∀ a, ¬ R.IsOuter a → L.Adj (label a) (label (R.vertexPerm a)))
variable (hred : ∀ a, ¬ R.IsOuter a → ¬ R.IsOuter (R.vertexPerm a) →
  label a ≠ label (R.vertexPerm (R.vertexPerm a)))

include hadj hred

/-- The full corner orbit at a vertex disjoint from the exterior is a genuinely
reduced nonempty closed link walk. -/
theorem interior_angle_lower (M : ℝ)
    (hclosed : ∀ a (p : L.Walk (label a) (label a)), 0 < p.length → ReducedWalk p →
      M ≤ weight (R.color (cl R.vertexPerm a)) * p.length)
    (v : R.Vertex) (hv : R.visits v = 0) : M ≤ R.angles v := by
  obtain ⟨a,rfl⟩ := cl_surjective R.vertexPerm v
  let n := (orbit R.vertexPerm a).card
  let seq := fun i : ℕ => label ((R.vertexPerm^i) a)
  have hn : 0 < n := by
    change 0 < (orbit R.vertexPerm a).card
    rw [orbit_card_eq_minimalPeriod]
    exact minimalPeriod_pos _ _
  have hout (i : ℕ) : ¬ R.IsOuter ((R.vertexPerm^i) a) :=
    R.no_outer_of_visits_zero a hv ((Perm.SameCycle.refl _ _).pow_right)
  have hadj' (i : ℕ) (_hi : i < n) : L.Adj (seq i) (seq (i+1)) := by
    simpa only [seq,pow_succ',Perm.mul_apply] using hadj _ (hout i)
  have hred' (i : ℕ) (_hi : i+2 ≤ n) : seq i ≠ seq (i+2) := by
    have hh := hred ((R.vertexPerm^i) a) (hout i)
      (by simpa only [pow_succ',Perm.mul_apply] using hout (i+1))
    simpa only [seq,show i+2 = (i+1)+1 by omega,pow_succ',Perm.mul_apply] using hh
  have hend : seq n = label a := congrArg label (pow_card_orbit R.vertexPerm a)
  have hstart : seq 0 = label a := rfl
  let p := (SequenceWalk.walk L seq n hadj').copy hstart hend
  have hlen : p.length = n := (SimpleGraph.Walk.length_copy _ _ _).trans
    (SequenceWalk.length_walk L seq n hadj')
  have hr : ReducedWalk p := by
    intro i hi
    simpa only [p,SimpleGraph.Walk.getVert_copy] using
      SequenceWalk.reduced_walk L seq n hadj' hred' i
        (by simpa only [p,SimpleGraph.Walk.length_copy] using hi)
  have hh := hclosed a p (by rw [hlen]; exact hn) hr
  have hc : (R.innerCorners a).card = n := by
    have hc := R.corner_count a
    rw [← R.visits_cl,hv] at hc
    omega
  rw [R.angles_cl,hc]
  simpa only [hlen] using hh

/-- A vertex with exactly one exterior corner has a reduced interior-sector
path from the outgoing boundary direction back to the incoming one. -/
theorem boundary_angle_lower
    (hboundary : ∀ a, R.IsOuter a →
      ∀ p : L.Walk (label (R.vertexPerm a)) (label a), ReducedWalk p →
        5 ≤ weight (R.color (cl R.vertexPerm a)) * p.length)
    (v : R.Vertex) (hv : R.visits v = 1) : 5 ≤ R.angles v := by
  obtain ⟨a,ha⟩ : ∃ a, cl R.vertexPerm a = v ∧ R.IsOuter a := by
    obtain ⟨b,rfl⟩ := cl_surjective R.vertexPerm v
    rw [R.visits_cl,Finset.card_eq_one] at hv
    obtain ⟨a,ha⟩ := hv
    have hm : a ∈ R.outerCorners b := by rw [ha]; simp
    obtain ⟨hc,ho⟩ := Finset.mem_filter.mp hm
    exact ⟨a,(cl_eq_iff _ _ _).mpr ((mem_orbit _ _ _).mp hc).symm,ho⟩
  obtain ⟨rfl,ha⟩ := ha
  let n := (orbit R.vertexPerm a).card
  let seq := fun i : ℕ => label ((R.vertexPerm^(i+1)) a)
  have hn : 0 < n := by
    change 0 < (orbit R.vertexPerm a).card
    rw [orbit_card_eq_minimalPeriod]
    exact minimalPeriod_pos _ _
  have hout (i : ℕ) (hi : 0 < i) (hin : i < n) : ¬ R.IsOuter ((R.vertexPerm^i) a) := by
    intro ho
    have hh := R.unique_outer_of_visits_one a ha hv
      ((Perm.SameCycle.refl _ _).pow_right) ho
    exact pow_ne_of_lt_card_orbit R.vertexPerm a i hi hin hh
  have hadj' (i : ℕ) (hi : i < n-1) : L.Adj (seq i) (seq (i+1)) := by
    simpa only [seq,pow_succ',Perm.mul_apply] using
      hadj ((R.vertexPerm^(i+1)) a) (hout (i+1) (by omega) (by omega))
  have hred' (i : ℕ) (hi : i+2 ≤ n-1) : seq i ≠ seq (i+2) := by
    have hh := hred ((R.vertexPerm^(i+1)) a) (hout (i+1) (by omega) (by omega))
      (by simpa only [pow_succ',Perm.mul_apply] using hout (i+2) (by omega) (by omega))
    simpa only [seq,show i+2+1 = (i+1)+1+1 by omega,pow_succ',Perm.mul_apply] using hh
  have hstart : seq 0 = label (R.vertexPerm a) := rfl
  have hend : seq (n-1) = label a := by
    dsimp [seq]
    rw [Nat.sub_add_cancel hn,pow_card_orbit]
  let p := (SequenceWalk.walk L seq (n-1) hadj').copy hstart hend
  have hr : ReducedWalk p := by
    intro i hi
    simpa only [p,SimpleGraph.Walk.getVert_copy] using
      SequenceWalk.reduced_walk L seq (n-1) hadj' hred' i
        (by simpa only [p,SimpleGraph.Walk.length_copy] using hi)
  have hh := hboundary a ha p hr
  have hc : (R.innerCorners a).card = n-1 := by
    have hc := R.corner_count a
    rw [← R.visits_cl,hv] at hc
    omega
  rw [R.angles_cl,hc]
  simpa only [p,SimpleGraph.Walk.length_copy,SequenceWalk.length_walk] using hh

/-- Gauss--Bonnet on the actual permutation ribbon now rules out a filling whose
boundary turns are all separated by angle at least π in their target links. -/
theorem not_all_turns_geodesic
    (hclosed : ∀ a (p : L.Walk (label a) (label a)), 0 < p.length → ReducedWalk p →
      10 ≤ weight (R.color (cl R.vertexPerm a)) * p.length)
    (hboundary : ∀ a, R.IsOuter a →
      ∀ p : L.Walk (label (R.vertexPerm a)) (label a), ReducedWalk p →
        5 ≤ weight (R.color (cl R.vertexPerm a)) * p.length) : False :=
  R.counts.cannot_have_geodesic_boundary
    (R.interior_angle_lower L label hadj hred 10 hclosed)
    (R.boundary_angle_lower L label hadj hred hboundary)

end Release075.TriangleRibbon

end OAI
end
end

section
section
namespace OAI

namespace Release075.MarkedLineData
variable {q r : ℕ} [Fact q.Prime] (d : MarkedLineData q r) (hr : 0 < r)

abbrev ODirections := (d.presentation hr).LEdge ⊕ (d.presentation hr).REdge
abbrev VDirections := ShiftScheme.XDirection (I := d.Label) (r := r) ⊕ (d.vShift hr).LDirection
abbrev WDirections := ShiftScheme.XDirection (I := d.Label) (r := r) ⊕ (d.wShift hr).LDirection
abbrev AllDirections := d.ODirections hr ⊕ (d.VDirections hr ⊕ d.WDirections hr)

/-- At O a larger complete bipartite graph suffices for the four-edge girth bound;
at V and W we use precisely the shifted incidence links. -/
noncomputable def allLink : SimpleGraph (d.AllDirections hr) :=
  (relationGraph (fun (_ : (d.presentation hr).LEdge) (_ : (d.presentation hr).REdge) => True)).sum
    ((d.vShift hr).link.sum (d.wShift hr).link)

def linkDirection : (d.presentation hr).OrientedEdge → d.AllDirections hr
  | (.inl (i,u,v),false) => .inr (.inl (.inl (i,u,v)))
  | (.inl (i,u,v),true) => .inr (.inr (.inl (i,v,u)))
  | (.inr (.inl l),false) => .inl (.inl l)
  | (.inr (.inl l),true) => .inr (.inl (.inr l))
  | (.inr (.inr s),false) => .inl (.inr s)
  | (.inr (.inr s),true) => .inr (.inr (.inr s))

def linkColor : d.AllDirections hr → Fin 3
  | .inl _ => 0
  | .inr (.inl _) => 1
  | .inr (.inr _) => 2

 theorem linkDirection_color (a : (d.presentation hr).OrientedEdge) :
    d.linkColor hr (d.linkDirection hr a) =
      (d.presentation hr).vertexColor ((d.presentation hr).edgeTarget a) := by
  rcases a with ⟨a,s⟩
  rcases a with ⟨i,u,v⟩|l|s' <;> cases s <;> rfl

 theorem linkDirection_injective : Function.Injective (d.linkDirection hr) := by
  rintro ⟨a,s⟩ ⟨b,t⟩ h
  rcases a with ⟨i,u,v⟩|l|s'
  all_goals rcases b with ⟨j,u',v'⟩|l'|t'
  all_goals cases s <;> cases t <;> simp_all [linkDirection]
  all_goals exact Sum.inr.inj h

 theorem face_corner_adj {a b c : (d.presentation hr).OrientedEdge}
    (h : (d.presentation hr).TriangleFace a b c) :
    (d.allLink hr).Adj (d.linkDirection hr a)
      (d.linkDirection hr ((d.presentation hr).flipEdge b)) := by
  cases h <;>
    simp only [BlockPresentation.orientedL,BlockPresentation.orientedX,
      BlockPresentation.orientedR,BlockPresentation.flipEdge, Bool.not_true,
      Bool.not_false, linkDirection,allLink,SimpleGraph.sum_adj_inl,SimpleGraph.sum_adj_inr]
  all_goals first | exact True.intro | exact ⟨Subtype.prop _,rfl,rfl⟩

 theorem allLink_closed (a : d.AllDirections hr) (p : (d.allLink hr).Walk a a)
    (hn : 0 < p.length) (hp : ReducedWalk p) :
    12 ≤ TriangleRibbon.weight (d.linkColor hr a) * p.length := by
  rcases a with a|a|a
  · let p' := SumWalk.left p
    have hlen : p'.length = p.length := SumWalk.left_length p
    have hg := reduced_closed_length_ge 4 (relationGraph_cycle_length _) p'
      (by rw [hlen]; exact hn) (SumWalk.left_reduced hp)
    rw [hlen] at hg
    norm_num only [linkColor,TriangleRibbon.weight,Fin.zero_eta,ite_true]
    exact_mod_cast (by omega : 12 ≤ 3*p.length)
  · let p' := SumWalk.left (SumWalk.right p)
    have hlen : p'.length = p.length := (SumWalk.left_length _).trans (SumWalk.right_length p)
    have hg := reduced_closed_length_ge 14 (d.v_link_girth hr) p'
      (by rw [hlen]; exact hn) (SumWalk.left_reduced (SumWalk.right_reduced hp))
    rw [hlen] at hg
    norm_num only [linkColor,TriangleRibbon.weight,show (1 : Fin 3) ≠ 0 by decide,ite_false,one_mul]
    exact_mod_cast (by omega : 12 ≤ p.length)
  · let p' := SumWalk.right (SumWalk.right p)
    have hlen : p'.length = p.length := (SumWalk.right_length _).trans (SumWalk.right_length p)
    have hg := reduced_closed_length_ge 14 (d.w_link_girth hr) p'
      (by rw [hlen]; exact hn) (SumWalk.right_reduced (SumWalk.right_reduced hp))
    rw [hlen] at hg
    norm_num only [linkColor,TriangleRibbon.weight,show (2 : Fin 3) ≠ 0 by decide,ite_false,one_mul]
    exact_mod_cast (by omega : 12 ≤ p.length)

 theorem v_reduced_same_label (i : d.Label) (u v u' v' : Fin r)
    (hne : (u,v) ≠ (u',v'))
    (p : (d.allLink hr).Walk (.inr (.inl (.inl (i,u,v)))) (.inr (.inl (.inl (i,u',v')))))
    (hp : ReducedWalk p) : 14 ≤ p.length := by
  let p' := SumWalk.left (SumWalk.right p)
  have hr' : ReducedWalk p' := SumWalk.left_reduced (SumWalk.right_reduced hp)
  have hh := immersion_fiber_distance (d.vShift hr).projection
    (d.vShift hr).projection_locallyInjective 14 d.incidences_girth
    (a := .inl (i,u,v)) (b := .inl (i,u',v'))
    (by simpa only [ne_eq,Sum.inl.injEq,Prod.mk.injEq,true_and] using hne) rfl p' hr'
  have hlen : p'.length = p.length := (SumWalk.left_length _).trans (SumWalk.right_length p)
  exact hlen ▸ hh

 theorem w_reduced_same_label (i : d.Label) (u v u' v' : Fin r)
    (hne : (u,v) ≠ (u',v'))
    (p : (d.allLink hr).Walk (.inr (.inr (.inl (i,u,v)))) (.inr (.inr (.inl (i,u',v')))))
    (hp : ReducedWalk p) : 14 ≤ p.length := by
  let p' := SumWalk.right (SumWalk.right p)
  have hr' : ReducedWalk p' := SumWalk.right_reduced (SumWalk.right_reduced hp)
  have hh := immersion_fiber_distance (d.wShift hr).projection
    (d.wShift hr).projection_locallyInjective 14 d.incidences_girth
    (a := .inl (i,u,v)) (b := .inl (i,u',v'))
    (by simpa only [ne_eq,Sum.inl.injEq,Prod.mk.injEq,true_and] using hne) rfl p' hr'
  have hlen : p'.length = p.length := (SumWalk.right_length _).trans (SumWalk.right_length p)
  exact hlen ▸ hh

end Release075.MarkedLineData

namespace Release075.MarkedLineData
open Equiv PermCycles
attribute [local instance] Classical.propDecidable Classical.decEq
variable {q r : ℕ} [Fact q.Prime] (d : MarkedLineData q r) (hr : 0 < r)

 theorem x_turn_large (i : d.Label) (u v u' v' : Fin r) (s t : Bool)
    (ht : (d.presentation hr).edgeTarget ((d.presentation hr).flipEdge (.inl (i,u',v'),t)) =
      (d.presentation hr).edgeTarget (.inl (i,u,v),s))
    (hne : (u,v) ≠ (u',v'))
    (p : (d.allLink hr).Walk
      (d.linkDirection hr ((d.presentation hr).flipEdge (.inl (i,u',v'),t)))
      (d.linkDirection hr (.inl (i,u,v),s)))
    (hp : ReducedWalk p) :
    5 ≤ TriangleRibbon.weight (d.linkColor hr (d.linkDirection hr (.inl (i,u,v),s))) * p.length := by
  cases s <;> cases t <;>
    simp only [BlockPresentation.flipEdge,BlockPresentation.edgeTarget,Bool.not_false,Bool.not_true] at ht
  · cases ht
  · have hh := d.v_reduced_same_label hr i u' v' u v hne.symm p hp
    change (5 : ℝ) ≤ 1 * p.length
    rw [one_mul]
    change 14 ≤ p.length at hh
    exact_mod_cast (le_trans (by decide : 5 ≤ 14) hh)
  · have hh := d.w_reduced_same_label hr i v' u' v u
      (by simpa only [ne_eq,Prod.mk.injEq,and_comm] using hne.symm) p hp
    change (5 : ℝ) ≤ 1 * p.length
    rw [one_mul]
    change 14 ≤ p.length at hh
    exact_mod_cast (le_trans (by decide : 5 ≤ 14) hh)
  · cases ht

variable {w : List (d.presentation hr).OrientedEdge}
variable (D : TriangleFilling (d.presentation hr).flipEdge (d.presentation hr).edgeTarget
  (d.presentation hr).TriangleFace w) (b : D.Dart) (hb : b ∈ D.boundary)

noncomputable abbrev concreteRibbon := D.ribbon (d.presentation hr).vertexColor
  (fun _ _ _ => BlockPresentation.TriangleFace.colors _) b hb

def dartDirection (a : D.ActiveDart) : d.AllDirections hr :=
  d.linkDirection hr (D.label a)

theorem ribbon_outer_iff (a : D.ActiveDart) :
    (d.concreteRibbon hr D b hb).IsOuter a ↔ a.val ∈ D.boundary :=
  D.active_boundary_iff hb a

theorem ribbon_color (a : D.ActiveDart) :
    (d.concreteRibbon hr D b hb).color (cl (d.concreteRibbon hr D b hb).vertexPerm a) =
      d.linkColor hr (d.dartDirection hr D a) := by
  change (D.activeColor (d.presentation hr).vertexColor) (cl (D.activeReverse*D.activeNext) a) = _
  rw [TriangleFilling.activeColor,descend_cl]
  exact (d.linkDirection_color hr (D.label a)).symm

theorem ribbon_direction_step (a : D.ActiveDart) :
    d.dartDirection hr D ((d.concreteRibbon hr D b hb).vertexPerm a) =
      d.linkDirection hr ((d.presentation hr).flipEdge (D.label (D.next a))) := by
  change d.linkDirection hr (D.label (D.reverse (D.next a))) = _
  rw [D.reverse_label]

theorem ribbon_adj (a : D.ActiveDart)
    (ha : ¬(d.concreteRibbon hr D b hb).IsOuter a) :
    (d.allLink hr).Adj (d.dartDirection hr D a)
      (d.dartDirection hr D ((d.concreteRibbon hr D b hb).vertexPerm a)) := by
  rw [d.ribbon_direction_step hr D b hb a]
  exact d.face_corner_adj hr (D.triangular a a.property
    (fun h => ha ((d.ribbon_outer_iff hr D b hb a).mpr h))).2.2

theorem ribbon_reduced (hD : IsEmpty D.Dipole) (a : D.ActiveDart)
    (ha : ¬(d.concreteRibbon hr D b hb).IsOuter a)
    (ha' : ¬(d.concreteRibbon hr D b hb).IsOuter ((d.concreteRibbon hr D b hb).vertexPerm a)) :
    d.dartDirection hr D a ≠
      d.dartDirection hr D ((d.concreteRibbon hr D b hb).vertexPerm
        ((d.concreteRibbon hr D b hb).vertexPerm a)) := by
  intro he
  apply D.noDipole_link_reduced
    (fun _ _ _ => BlockPresentation.TriangleFace.colors _)
    (d.presentation hr).flipEdge_flipEdge
    (fun _ _ _ => BlockPresentation.TriangleFace.mirror _)
    (fun _ _ _ _ => BlockPresentation.TriangleFace.unique _) hD a a.property
    (fun h => ha ((d.ribbon_outer_iff hr D b hb a).mpr h))
    (fun h => ha' ((d.ribbon_outer_iff hr D b hb _).mpr h))
  exact d.linkDirection_injective hr he

theorem ribbon_closed (a : D.ActiveDart)
    (p : (d.allLink hr).Walk (d.dartDirection hr D a) (d.dartDirection hr D a))
    (hn : 0 < p.length) (hp : ReducedWalk p) :
    10 ≤ TriangleRibbon.weight ((d.concreteRibbon hr D b hb).color
      (cl (d.concreteRibbon hr D b hb).vertexPerm a)) * p.length := by
  rw [d.ribbon_color hr D b hb a]
  exact le_trans (by norm_num) (d.allLink_closed hr _ p hn hp)

end Release075.MarkedLineData

end OAI
end
end

section
section
namespace OAI

namespace Release075.MarkedLineData
attribute [local instance] Classical.propDecidable Classical.decEq
variable {q r : ℕ} [Fact q.Prime] (d : MarkedLineData q r) (hr : 0 < r)

theorem rectangle_turn_large (i : d.Label) (u u' v v' : Fin r)
    (hu : u ≠ u') (hv : v ≠ v')
    (a b : (d.presentation hr).OrientedEdge)
    (ha : a ∈ [(d.presentation hr).orientedX i u v,
      (d.presentation hr).flipEdge ((d.presentation hr).orientedX i u' v),
      (d.presentation hr).orientedX i u' v',
      (d.presentation hr).flipEdge ((d.presentation hr).orientedX i u v')])
    (hb : b ∈ [(d.presentation hr).orientedX i u v,
      (d.presentation hr).flipEdge ((d.presentation hr).orientedX i u' v),
      (d.presentation hr).orientedX i u' v',
      (d.presentation hr).flipEdge ((d.presentation hr).orientedX i u v')])
    (ht : (d.presentation hr).edgeTarget ((d.presentation hr).flipEdge b) =
      (d.presentation hr).edgeTarget a)
    (p : (d.allLink hr).Walk (d.linkDirection hr ((d.presentation hr).flipEdge b))
      (d.linkDirection hr a)) (hp : ReducedWalk p) :
    5 ≤ TriangleRibbon.weight (d.linkColor hr (d.linkDirection hr a)) * p.length := by
  simp only [List.mem_cons,List.not_mem_nil,or_false] at ha hb
  rcases ha with rfl|rfl|rfl|rfl
  all_goals rcases hb with rfl|rfl|rfl|rfl
  all_goals simp only [BlockPresentation.orientedX,BlockPresentation.flipEdge,
    BlockPresentation.edgeTarget,Bool.not_true,Bool.not_false] at ht
  all_goals cases ht
  all_goals
    first
    | exact d.x_turn_large hr i u v u' v true false rfl
        (by intro he; exact hu (congrArg Prod.fst he)) p hp
    | exact d.x_turn_large hr i u v u v' true false rfl
        (by intro he; exact hv (congrArg Prod.snd he)) p hp
    | exact d.x_turn_large hr i u' v u v false true rfl
        (by intro he; exact hu.symm (congrArg Prod.fst he)) p hp
    | exact d.x_turn_large hr i u' v u' v' false true rfl
        (by intro he; exact hv (congrArg Prod.snd he)) p hp
    | exact d.x_turn_large hr i u' v' u' v true false rfl
        (by intro he; exact hv.symm (congrArg Prod.snd he)) p hp
    | exact d.x_turn_large hr i u' v' u v' true false rfl
        (by intro he; exact hu.symm (congrArg Prod.fst he)) p hp
    | exact d.x_turn_large hr i u v' u v false true rfl
        (by intro he; exact hv.symm (congrArg Prod.snd he)) p hp
    | exact d.x_turn_large hr i u v' u' v' false true rfl
        (by intro he; exact hu (congrArg Prod.fst he)) p hp

/-- Every actual rectangular word in the fixed presentation is nontrivial:
nullhomotopy gives a minimal labelled planar filling, whose reduced link sectors
contradict its Euler-characteristic-one angular identity. -/
theorem rectangular_nontriviality : d.RectangularNontriviality hr := by
  intro i u u' v v' hu hv he
  have hf := (d.presentation hr).rectangle_fillable_of_eq_one i u u' v v' he
  obtain ⟨D,hD⟩ := TriangleFilling.exists_noDipole hf
  have hn : D.boundary ≠ [] := by
    intro hz
    have hh := D.boundary_word
    rw [hz] at hh
    cases hh
  obtain ⟨b,hb⟩ := List.exists_mem_of_ne_nil D.boundary hn
  apply (d.concreteRibbon hr D b hb).not_all_turns_geodesic
    (d.allLink hr) (d.dartDirection hr D)
    (d.ribbon_adj hr D b hb) (d.ribbon_reduced hr D b hb hD)
    (d.ribbon_closed hr D b hb)
  intro a ha p hp
  have ha' : a.val ∈ D.boundary := (d.ribbon_outer_iff hr D b hb a).mp ha
  have hb' : D.next a.val ∈ D.boundary := (D.boundary_cycle.mem_iff a.val).mpr ha'
  have hal : D.label a.val ∈ _ := List.mem_map.mpr ⟨a.val,ha',rfl⟩
  have hbl : D.label (D.next a.val) ∈ _ := List.mem_map.mpr ⟨D.next a.val,hb',rfl⟩
  rw [D.boundary_word] at hal hbl
  rw [d.ribbon_color hr D b hb a]
  have ht : (d.presentation hr).edgeTarget ((d.presentation hr).flipEdge (D.label (D.next a.val))) =
      (d.presentation hr).edgeTarget (D.label a.val) := by
    rw [← D.reverse_label]
    exact D.color_next a.val
  have hs := d.ribbon_direction_step hr D b hb a
  let p' := p.copy hs rfl
  have hp' : ReducedWalk p' := by
    intro j hj
    simpa only [p',SimpleGraph.Walk.getVert_copy] using
      hp j (by simpa only [p',SimpleGraph.Walk.length_copy] using hj)
  have hh := d.rectangle_turn_large hr i u u' v v' hu hv _ _ hal hbl ht p' hp'
  have hlen : p'.length = p.length := SimpleGraph.Walk.length_copy p hs rfl
  change 5 ≤ TriangleRibbon.weight (d.linkColor hr (d.linkDirection hr (D.label a.val))) * p'.length at hh
  rw [hlen] at hh
  exact hh

end Release075.MarkedLineData

namespace Release075.MarkedLineData
open Equiv PermCycles
attribute [local instance] Classical.propDecidable Classical.decEq
variable {q r : ℕ} [Fact q.Prime] (d : MarkedLineData q r) (hr : 0 < r)
variable {w : List (d.presentation hr).OrientedEdge}
variable (D : TriangleFilling (d.presentation hr).flipEdge (d.presentation hr).edgeTarget
  (d.presentation hr).TriangleFace w) (b : D.Dart) (hb : b ∈ D.boundary)

theorem ribbon_closed_strict (a : D.ActiveDart)
    (p : (d.allLink hr).Walk (d.dartDirection hr D a) (d.dartDirection hr D a))
    (hn : 0 < p.length) (hp : ReducedWalk p) :
    12 ≤ TriangleRibbon.weight ((d.concreteRibbon hr D b hb).color
      (cl (d.concreteRibbon hr D b hb).vertexPerm a)) * p.length := by
  rw [d.ribbon_color hr D b hb a]
  exact d.allLink_closed hr _ p hn hp

theorem ribbon_boundary_length : (d.concreteRibbon hr D b hb).counts.boundaryLength = w.length := by
  let R := d.concreteRibbon hr D b hb
  change (∑ v : R.Vertex, R.visits v) = _
  rw [R.visits_sum]
  let e : {a : R.Dart // cl R.face a = R.outer} ≃ {a : D.Dart // a ∈ D.boundary} := {
    toFun a := ⟨a.val.val,(d.ribbon_outer_iff hr D b hb a.val).mp a.property⟩
    invFun a := ⟨⟨a.val,D.active_of_mem a.property⟩,
      (d.ribbon_outer_iff hr D b hb _).mpr a.property⟩
    left_inv _ := rfl
    right_inv _ := rfl }
  rw [Fintype.card_congr e,Fintype.card_subtype]
  have hset : Finset.univ.filter (fun a => a ∈ D.boundary) = D.boundary.toFinset := by
    ext a; simp
  rw [hset,List.toFinset_card_of_nodup D.boundary_cycle.1]
  exact (List.length_map D.label).symm.trans (congrArg List.length D.boundary_word)

include b hb in
theorem reduced_linear_active_bound (hD : IsEmpty D.Dipole) :
    D.activeCount + 36 ≤ 19*w.length := by
  let R := d.concreteRibbon hr D b hb
  have hstrict := R.interior_angle_lower (d.allLink hr) (d.dartDirection hr D)
    (d.ribbon_adj hr D b hb) (d.ribbon_reduced hr D b hb hD) 12
    (d.ribbon_closed_strict hr D b hb)
  have hface := R.counts.linear_face_bound hstrict
  have hlen := d.ribbon_boundary_length hr D b hb
  change R.counts.boundaryLength = w.length at hlen
  rw [hlen] at hface
  have hdart : Fintype.card R.Dart = D.activeCount := by
    change Fintype.card D.ActiveDart = _
    exact Fintype.card_subtype _
  have he := R.exterior_count
  rw [← R.dart_card,hdart] at he
  change R.counts.boundaryLength + 3*R.counts.faces = D.activeCount at he
  rw [hlen] at he
  omega

/-- An actual finite nullhomotopy has a genuine planar filling of linearly
bounded size, not an assumed Dehn-function estimate. This estimate is a necessary
bridge to the uniform Cayley thinness argument below. -/
theorem exists_linear_filling (hf : Fillable (d.presentation hr).flipEdge
    (d.presentation hr).edgeTarget (d.presentation hr).TriangleFace w) :
    ∃ D : TriangleFilling (d.presentation hr).flipEdge (d.presentation hr).edgeTarget
      (d.presentation hr).TriangleFace w, D.activeCount ≤ 19*w.length := by
  by_cases hw : w = []
  · subst w
    refine ⟨TriangleFilling.empty,?_⟩
    unfold TriangleFilling.activeCount
    apply (Finset.card_le_univ _).trans
    change 0 ≤ _
    exact Nat.zero_le _
  · obtain ⟨D,hD⟩ := TriangleFilling.exists_noDipole hf
    have hn : D.boundary ≠ [] := by
      intro he
      apply hw
      rw [← D.boundary_word,he,List.map_nil]
    obtain ⟨b,hb⟩ := List.exists_mem_of_ne_nil D.boundary hn
    exact ⟨D,by have hh := d.reduced_linear_active_bound hr D b hb hD; omega⟩

/-- The fixed presentation's non-residual-finiteness is now unconditional in
its finite incidence data; no rectangular nontriviality premise remains. -/
theorem actual_presentation_not_residuallyFinite (hq : r < q) (hq200 : 200 ≤ q) :
    ¬ Group.ResiduallyFinite (d.presentation hr).GroupType :=
  d.presentation_not_residuallyFinite hr hq hq200 (d.rectangular_nontriviality hr)

end Release075.MarkedLineData

end OAI
end
end

section
section
namespace OAI

namespace Release075.BlockPresentation
open CategoryTheory
variable {I B : Type} {r : ℕ} (d : BlockPresentation I B r)

/-- The signed displacement of an oriented original edge, with the two tree
edges already killed in the actual presentation. -/
def edgeValue (e : d.OrientedEdge) : d.GroupType :=
  if e.2 then d.edge e.1 else (d.edge e.1)⁻¹

@[simp] theorem edgeValue_flip (e : d.OrientedEdge) :
    d.edgeValue (d.flipEdge e) = (d.edgeValue e)⁻¹ := by
  rcases e with ⟨e,s⟩
  cases s <;> simp [edgeValue,flipEdge]

def wordValue (w : List d.OrientedEdge) : d.GroupType := (w.map d.edgeValue).prod

@[simp] theorem wordValue_nil : d.wordValue [] = 1 := rfl
@[simp] theorem wordValue_cons (e : d.OrientedEdge) (w : List d.OrientedEdge) :
    d.wordValue (e::w) = d.edgeValue e * d.wordValue w := rfl
@[simp] theorem wordValue_append (u v : List d.OrientedEdge) :
    d.wordValue (u++v) = d.wordValue u * d.wordValue v := by
  simp only [wordValue,List.map_append,List.prod_append]

abbrev LiftedEdge := d.OrientedEdge × d.GroupType
abbrev LiftedVertex := d.Vertex × d.GroupType

def liftedFlip (e : d.LiftedEdge) : d.LiftedEdge :=
  (d.flipEdge e.1,e.2 * (d.edgeValue e.1)⁻¹)

def liftedTarget (e : d.LiftedEdge) : d.LiftedVertex := (d.edgeTarget e.1,e.2)

@[simp] theorem liftedFlip_flip (e : d.LiftedEdge) :
    d.liftedFlip (d.liftedFlip e) = e := by
  rcases e with ⟨e,g⟩
  simp [liftedFlip]

theorem liftedTarget_ne (e : d.LiftedEdge) :
    d.liftedTarget e ≠ d.liftedTarget (d.liftedFlip e) := by
  intro h
  exact d.edgeTarget_ne e.1 (congrArg Prod.fst h)

/-- A genuine lift of a triangular face: all three corners are glued at the
same group coordinates, not merely at the same original vertex colors. -/
def LiftedFace (a b c : d.LiftedEdge) : Prop :=
  d.TriangleFace a.1 b.1 c.1 ∧
  d.liftedTarget (d.liftedFlip b) = d.liftedTarget a ∧
  d.liftedTarget (d.liftedFlip c) = d.liftedTarget b ∧
  d.liftedTarget (d.liftedFlip a) = d.liftedTarget c

theorem LiftedFace.rotate {a b c : d.LiftedEdge} (h : d.LiftedFace a b c) :
    d.LiftedFace b c a := ⟨TriangleFace.rotate d h.1,h.2.2.1,h.2.2.2,h.2.1⟩

theorem LiftedFace.mirror {a b c : d.LiftedEdge} (h : d.LiftedFace a b c) :
    d.LiftedFace (d.liftedFlip a) (d.liftedFlip c) (d.liftedFlip b) := by
  refine ⟨TriangleFace.mirror d h.1,?_,?_,?_⟩
  · simpa only [liftedFlip_flip] using h.2.2.2.symm
  · simpa only [liftedFlip_flip] using h.2.2.1.symm
  · simpa only [liftedFlip_flip] using h.2.1.symm

theorem LiftedFace.colors {a b c : d.LiftedEdge} (h : d.LiftedFace a b c) :
    d.liftedTarget a ≠ d.liftedTarget b ∧ d.liftedTarget b ≠ d.liftedTarget c ∧
      d.liftedTarget c ≠ d.liftedTarget a := by
  obtain ⟨hab,hbc,hca⟩ := TriangleFace.colors d h.1
  exact ⟨fun he => hab (congrArg Prod.fst he),
    fun he => hbc (congrArg Prod.fst he),fun he => hca (congrArg Prod.fst he)⟩

theorem LiftedFace.unique {a b c c' : d.LiftedEdge}
    (h : d.LiftedFace a b c) (h' : d.LiftedFace a b c') : c = c' := by
  have hc : d.liftedTarget c = d.liftedTarget c' := h.2.2.2.symm.trans h'.2.2.2
  exact Prod.ext (TriangleFace.unique d h.1 h'.1)
    (congrArg (fun x : d.LiftedVertex => x.2) hc)

def liftWord (g : d.GroupType) : List d.OrientedEdge → List d.LiftedEdge
  | [] => []
  | e::w => (e,g*d.edgeValue e)::liftWord (g*d.edgeValue e) w

@[simp] theorem liftWord_nil (g : d.GroupType) : d.liftWord g [] = [] := rfl
@[simp] theorem liftWord_cons (g : d.GroupType) (e : d.OrientedEdge) (w) :
    d.liftWord g (e::w) = (e,g*d.edgeValue e)::d.liftWord (g*d.edgeValue e) w := rfl

@[simp] theorem liftWord_length (g : d.GroupType) (w) :
    (d.liftWord g w).length = w.length := by
  induction w generalizing g with
  | nil => rfl
  | cons e w ih => simp only [liftWord,List.length_cons,ih]

@[simp] theorem liftWord_forget (g : d.GroupType) (w) :
    (d.liftWord g w).map Prod.fst = w := by
  induction w generalizing g with
  | nil => rfl
  | cons e w ih => simp only [liftWord,List.map_cons,ih]

theorem liftWord_append (g : d.GroupType) (u v) :
    d.liftWord g (u++v) = d.liftWord g u ++ d.liftWord (g*d.wordValue u) v := by
  induction u generalizing g with
  | nil => simp only [List.nil_append,liftWord_nil,wordValue_nil,mul_one]
  | cons e u ih =>
    simp only [List.cons_append,liftWord_cons,ih,wordValue_cons,mul_assoc]

theorem liftWord_typed {a c : d.Vertex} {w : List d.OrientedEdge}
    (h : WordPath d.flipEdge d.edgeTarget a c w) (g : d.GroupType) :
    WordPath d.liftedFlip d.liftedTarget (a,g) (c,g*d.wordValue w) (d.liftWord g w) := by
  induction h generalizing g with
  | nil a => simpa only [wordValue_nil,mul_one,liftWord_nil] using
      (WordPath.nil (flip := d.liftedFlip) (color := d.liftedTarget) (a,g))
  | @cons e tgt w h ih =>
    simp only [liftWord_cons,wordValue_cons,← mul_assoc]
    have hh := WordPath.cons (e,g*d.edgeValue e) (ih _)
    simpa only [liftedTarget,liftedFlip,mul_inv_cancel_right] using hh

theorem TriangleFace.value {a b c : d.OrientedEdge} (h : d.TriangleFace a b c) :
    d.edgeValue a * d.edgeValue b * d.edgeValue c = 1 := by
  cases h <;>
    simp only [edgeValue,orientedL,orientedX,orientedR,flipEdge,Bool.not_true,
      Bool.false_eq_true,↓reduceIte]
  all_goals
    rw [show d.edge (.inl _) = _ from d.triangle_relation _ _ _ _]
  all_goals simp only [l,rr,edge] at *
  all_goals group

theorem TriangleFace.lift {a b c : d.OrientedEdge} (h : d.TriangleFace a b c)
    (g : d.GroupType) :
    d.LiftedFace (a,g*d.edgeValue a) (b,g*d.edgeValue a*d.edgeValue b) (c,g) := by
  obtain ⟨hab,hbc,hca⟩ := TriangleFace.typed d h
  have hv := TriangleFace.value d h
  refine ⟨h,Prod.ext hab ?_,Prod.ext hbc ?_,Prod.ext hca ?_⟩
  · change g*d.edgeValue a*d.edgeValue b*(d.edgeValue b)⁻¹ = g*d.edgeValue a
    group
  · change g*(d.edgeValue c)⁻¹ = g*d.edgeValue a*d.edgeValue b
    rw [mul_assoc]
    exact congrArg (g*·) (eq_inv_iff_mul_eq_one.mpr hv).symm
  · change g*d.edgeValue a*(d.edgeValue a)⁻¹ = g
    group

theorem rawMove_wordValue {a c : d.RawPaths} {p q : a ⟶ c} (h : d.RawMove p q) :
    d.wordValue (d.rawWord p) = d.wordValue (d.rawWord q) := by
  cases h with
  | backtrack h =>
    cases h with
    | step a c f =>
      change d.wordValue [] = d.wordValue [d.orientedLabel f,d.orientedLabel (Quiver.reverse f)]
      simp only [wordValue_nil,wordValue_cons,orientedLabel_reverse,edgeValue_flip,mul_one,mul_inv_cancel]
  | triangle b i u v =>
    change d.edgeValue (d.orientedL b i u v) * d.edgeValue (d.orientedX i u v) * 1 =
      d.edgeValue (d.orientedR b i u v) * 1
    simp only [edgeValue,orientedL,orientedX,orientedR,↓reduceIte,mul_one]
    exact (eq_inv_mul_iff_mul_eq).mp (d.triangle_relation b i u v)

theorem rawHomotopic_wordValue {a c : d.RawPaths} {p q : a ⟶ c}
    (h : d.RawHomotopic p q) : d.wordValue (d.rawWord p) = d.wordValue (d.rawWord q) := by
  induction h with
  | rel p q h =>
    cases h with
    | intro a c u p q v h =>
      simp only [rawWord_comp,wordValue_append,d.rawMove_wordValue h]
  | refl p => rfl
  | symm p q _ ih => exact ih.symm
  | trans p q s _ _ ih ih' => exact ih.trans ih'

theorem rawMove_lifted_filled {a c : d.RawPaths} {p q : a ⟶ c}
    (h : d.RawMove p q) (g : d.GroupType) :
    FilledBetween d.liftedFlip d.liftedTarget d.LiftedFace
      (d.liftWord g (d.rawWord p)) (d.liftWord g (d.rawWord q)) := by
  cases h with
  | backtrack h =>
    cases h with
    | step a c f =>
      change Fillable d.liftedFlip d.liftedTarget d.LiftedFace
        (reverseWord d.liftedFlip (d.liftWord g
          [d.orientedLabel f,d.orientedLabel (Quiver.reverse f)]))
      simp only [liftWord_cons,liftWord_nil,orientedLabel_reverse,edgeValue_flip,
        reverseWord_cons,reverseWord_nil,List.nil_append,List.singleton_append]
      have he : (d.flipEdge (d.orientedLabel f),g*d.edgeValue (d.orientedLabel f)*
          (d.edgeValue (d.orientedLabel f))⁻¹) =
          d.liftedFlip (d.orientedLabel f,g*d.edgeValue (d.orientedLabel f)) := rfl
      rw [he,d.liftedFlip_flip]
      exact Fillable.backtrack d.liftedFlip_flip _
  | triangle b i u v =>
    have hh := TriangleFace.lift d (TriangleFace.pos₀ (d := d) b i u v) g
    change Fillable d.liftedFlip d.liftedTarget d.LiftedFace
      (d.liftWord g [d.orientedL b i u v,d.orientedX i u v] ++
        reverseWord d.liftedFlip (d.liftWord g [d.orientedR b i u v]))
    simp only [liftWord_cons,liftWord_nil,reverseWord_cons,reverseWord_nil,List.nil_append,
      List.cons_append]
    have hr : d.liftedFlip (d.orientedR b i u v,g*d.edgeValue (d.orientedR b i u v)) =
        (d.flipEdge (d.orientedR b i u v),g) := by
      simp only [liftedFlip,mul_inv_cancel_right]
    rw [hr]
    exact ⟨TriangleFilling.triangle d.liftedFlip_flip
      (fun _ _ _ => LiftedFace.rotate d) _ _ _
      hh.2.1.symm hh.2.2.1.symm hh.2.2.2.symm (LiftedFace.mirror d hh)⟩

theorem rawHomotopic_lifted_filled {a c : d.RawPaths} {p q : a ⟶ c}
    (h : d.RawHomotopic p q) (g : d.GroupType) :
    FilledBetween d.liftedFlip d.liftedTarget d.LiftedFace
      (d.liftWord g (d.rawWord p)) (d.liftWord g (d.rawWord q)) := by
  induction h generalizing g with
  | rel p q h =>
    cases h with
    | intro a c u p q v h =>
      have he := d.rawMove_wordValue h
      have hu := d.liftWord_typed (d.rawWord_typed u) g
      have hp := d.liftWord_typed (d.rawWord_typed p) (g*d.wordValue (d.rawWord u))
      have hq := d.liftWord_typed (d.rawWord_typed q) (g*d.wordValue (d.rawWord u))
      rw [← he] at hq
      have hv := d.liftWord_typed (d.rawWord_typed v)
        (g*d.wordValue (d.rawWord u)*d.wordValue (d.rawWord p))
      have hf := FilledBetween.whiskerLeft d.liftedFlip_flip hu (hp.append hv) (hq.append hv)
        (FilledBetween.whiskerRight d.liftedFlip_flip hp hq hv
          (d.rawMove_lifted_filled h (g*d.wordValue (d.rawWord u))))
      simpa only [rawWord_comp,liftWord_append,wordValue_append,← he,mul_assoc,List.append_assoc]
        using hf
  | refl p => exact FilledBetween.refl d.liftedFlip_flip (d.liftWord_typed (d.rawWord_typed p) g)
  | symm p q _ ih =>
    exact FilledBetween.symm d.liftedFlip_flip (fun _ _ _ => LiftedFace.mirror d) (ih g)
  | trans p q s hpq hqs ih ih' =>
    have hq := d.liftWord_typed (d.rawWord_typed q) g
    have hs := d.liftWord_typed (d.rawWord_typed s) g
    rw [← d.rawHomotopic_wordValue hpq] at hq
    rw [← d.rawHomotopic_wordValue hqs,← d.rawHomotopic_wordValue hpq] at hs
    exact FilledBetween.trans d.liftedFlip_flip d.liftedTarget_ne
      (d.liftWord_typed (d.rawWord_typed p) g) hq hs (ih g) (ih' g)

theorem nullhomotopic_lifted_fillable {a : d.RawPaths} {p : a ⟶ a}
    (h : d.RawHomotopic p (𝟙 a)) (g : d.GroupType) :
    Fillable d.liftedFlip d.liftedTarget d.LiftedFace (d.liftWord g (d.rawWord p)) := by
  simpa only [FilledBetween,rawWord_nil,liftWord_nil,reverseWord_nil,List.append_nil] using
    d.rawHomotopic_lifted_filled h g

end Release075.BlockPresentation

namespace Release075.TriangleFilling
open Equiv PermCycles
variable {I B : Type} {r : ℕ} {d : BlockPresentation I B r}
variable {w : List d.LiftedEdge}

/-- Forgetting group coordinates keeps every dart, incidence, boundary and
planar component. The metric labels can therefore be tracked through reduction. -/
def forgetLift (D : TriangleFilling d.liftedFlip d.liftedTarget d.LiftedFace w) :
    TriangleFilling d.flipEdge d.edgeTarget d.TriangleFace (w.map Prod.fst) where
  Dart := D.Dart
  reverse := D.reverse
  next := D.next
  reverse_involutive := D.reverse_involutive
  reverse_ne := D.reverse_ne
  label a := (D.label a).1
  reverse_label a := congrArg Prod.fst (D.reverse_label a)
  color_next a := congrArg Prod.fst (D.color_next a)
  planar := D.planar
  boundary := D.boundary
  boundary_cycle := D.boundary_cycle
  boundary_word := by
    simpa only [List.map_map,Function.comp_def] using congrArg (List.map Prod.fst) D.boundary_word
  triangular a ha hb := let ht := D.triangular a ha hb; ⟨ht.1,ht.2.1,ht.2.2.1⟩

@[simp] theorem forgetLift_activeCount
    (D : TriangleFilling d.liftedFlip d.liftedTarget d.LiftedFace w) :
    D.forgetLift.activeCount = D.activeCount := rfl

/-- Matching opposite face labels at a shared lifted edge forces matching group
coordinates on the other two edges. Thus reduction cannot hide a downstairs dipole. -/
def Dipole.lift {D : TriangleFilling d.liftedFlip d.liftedTarget d.LiftedFace w}
    (P : D.forgetLift.Dipole) : D.Dipole := by
  have hn (j) : D.next (P.dart j) = P.dart (dipoleFace j) := P.next_dart j
  have hc (j) : d.liftedTarget (d.liftedFlip (D.label (P.dart (dipoleFace j)))) =
      d.liftedTarget (D.label (P.dart j)) := by
    have hh := D.color_next (P.dart j)
    change d.liftedTarget (D.label (D.reverse (D.next (P.dart j)))) =
      d.liftedTarget (D.label (P.dart j)) at hh
    exact (congrArg d.liftedTarget (D.reverse_label (P.dart (dipoleFace j)))).symm.trans
      (by simpa only [hn] using hh)
  have hrev : D.label (P.dart 3) = d.liftedFlip (D.label (P.dart 0)) := by
    rw [← P.reverse_zero]
    exact D.reverse_label _
  have h0 := hc 0
  have h5 := hc 5
  simp only [dipoleFace_zero] at h0
  simp only [dipoleFace_five,hrev,d.liftedFlip_flip] at h5
  have h51 : D.label (P.dart 5) = d.liftedFlip (D.label (P.dart 1)) :=
    Prod.ext P.label51 (congrArg (fun x : d.LiftedVertex => x.2) (h5.symm.trans h0.symm))
  have h1 := hc 1
  have h4 := hc 4
  simp only [dipoleFace_one] at h1
  simp only [dipoleFace_four,h51,d.liftedFlip_flip] at h4
  have h42 : D.label (P.dart 4) = d.liftedFlip (D.label (P.dart 2)) :=
    Prod.ext P.label42 (congrArg (fun x : d.LiftedVertex => x.2) (h4.symm.trans h1.symm))
  exact {
    dart := P.dart
    next_dart := P.next_dart
    reverse_zero := P.reverse_zero
    not_boundary := P.not_boundary
    active := P.active
    color10 := fun h => P.color10 (congrArg Prod.fst h)
    color21 := fun h => P.color21 (congrArg Prod.fst h)
    label51 := h51
    label42 := h42 }

theorem noDipole_forgetLift {D : TriangleFilling d.liftedFlip d.liftedTarget d.LiftedFace w}
    (h : IsEmpty D.Dipole) : IsEmpty D.forgetLift.Dipole := ⟨fun P => h.false P.lift⟩

end Release075.TriangleFilling

namespace Release075.MarkedLineData
variable {q r : ℕ} [Fact q.Prime] (d : MarkedLineData q r) (hr : 0 < r)
variable {w : List (d.presentation hr).LiftedEdge}

theorem exists_lifted_linear_filling (hf : Fillable (d.presentation hr).liftedFlip
    (d.presentation hr).liftedTarget (d.presentation hr).LiftedFace w) :
    ∃ D : TriangleFilling (d.presentation hr).liftedFlip (d.presentation hr).liftedTarget
      (d.presentation hr).LiftedFace w, D.activeCount ≤ 19*w.length := by
  classical
  by_cases hw : w = []
  · subst w
    refine ⟨TriangleFilling.empty,?_⟩
    unfold TriangleFilling.activeCount
    apply (Finset.card_le_univ _).trans
    change 0 ≤ _
    exact Nat.zero_le _
  · obtain ⟨D,hD⟩ := TriangleFilling.exists_noDipole hf
    have hn : D.boundary ≠ [] := by
      intro he
      apply hw
      rw [← D.boundary_word,he,List.map_nil]
    obtain ⟨b,hb⟩ := List.exists_mem_of_ne_nil D.boundary hn
    have hbound := d.reduced_linear_active_bound hr D.forgetLift b hb
      (TriangleFilling.noDipole_forgetLift hD)
    rw [TriangleFilling.forgetLift_activeCount,List.length_map] at hbound
    exact ⟨D,by omega⟩

end Release075.MarkedLineData

end OAI
end
end

section
section
namespace OAI

namespace Release075
open Equiv PermCycles

/-- A finite labelled spherical map, possibly with several connected components.
All faces are triangles; there is no distinguished outer face. -/
structure TriangleSphere {E V : Type} (flip : E → E) (color : E → V)
    (face : E → E → E → Prop) where
  Dart : Type
  [dartFintype : Fintype Dart]
  reverse : Perm Dart
  next : Perm Dart
  reverse_involutive : Function.Involutive reverse
  reverse_ne : ∀ a, reverse a ≠ a
  label : Dart → E
  reverse_label : ∀ a, label (reverse a) = flip (label a)
  color_next : ∀ a, color (label ((reverse*next) a)) = color (label a)
  planar : PlanarMap reverse next
  triangular : ∀ a, (next^3) a = a ∧ next a ≠ a ∧
    face (label a) (label (next a)) (label ((next^2) a))

attribute [instance] TriangleSphere.dartFintype

namespace TriangleSphere
attribute [local instance] Classical.propDecidable Classical.decEq
variable {E V : Type} {flip : E → E} {color : E → V} {face : E → E → E → Prop}
variable (D : TriangleSphere flip color face)

structure Dipole where
  dart : Fin 6 ↪ D.Dart
  next_dart : ∀ j, D.next (dart j) = dart (dipoleFace j)
  reverse_zero : D.reverse (dart 0) = dart 3
  color10 : color (D.label (dart 1)) ≠ color (D.label (dart 0))
  color21 : color (D.label (dart 2)) ≠ color (D.label (dart 1))
  label51 : D.label (dart 5) = flip (D.label (dart 1))
  label42 : D.label (dart 4) = flip (D.label (dart 2))

theorem reverse_not_sameCycle (a : D.Dart)
    (hf : ∀ a b c, face a b c → color a ≠ color b ∧ color b ≠ color c ∧ color c ≠ color a) :
    ¬ D.next.SameCycle a (D.reverse a) := by
  obtain ⟨hp,hn,hface⟩ := D.triangular a
  obtain ⟨h01,h12,h20⟩ := hf _ _ _ hface
  intro h
  have hm : D.reverse a ∈ orbit D.next a := (mem_orbit _ _ _).mpr h
  rw [orbit_eq_image D.next a (by omega : 0 < 3) hp] at hm
  obtain ⟨i,_,hi⟩ := Finset.mem_image.mp hm
  fin_cases i
  · exact D.reverse_ne a hi.symm
  · have h := D.color_next ((D.next^2) a)
    have h3 : D.next ((D.next^2) a) = a := by simpa only [pow_succ',Perm.mul_apply] using hp
    simp only [Perm.mul_apply,h3,← hi] at h
    exact h12 h
  · have h := D.color_next (D.next a)
    have hr : D.reverse ((D.next^2) a) = a := by rw [hi,D.reverse_involutive]
    change color (D.label (D.reverse ((D.next^2) a))) = color (D.label (D.next a)) at h
    rw [hr] at h
    exact h01 h

/-- Internal reversal of a link walk creates a cancellable pair, when the face
labels are determined by two consecutive sides. -/
theorem dipole_of_link_backtrack
    (hf : ∀ a b c, face a b c → color a ≠ color b ∧ color b ≠ color c ∧ color c ≠ color a)
    (hflip : ∀ e, flip (flip e) = e)
    (hmirror : ∀ a b c, face a b c → face (flip a) (flip c) (flip b))
    (hunique : ∀ a b c c', face a b c → face a b c' → c = c')
    (x : D.Dart)
    (hback : D.label x = D.label ((D.reverse*D.next) ((D.reverse*D.next) x))) :
    Nonempty D.Dipole := by
  let a := D.next x
  let b := D.reverse a
  obtain ⟨hp,hne,hfa⟩ := D.triangular a
  obtain ⟨hp',hne',hfb⟩ := D.triangular b
  have hx3 := (D.triangular x).1
  have hax : (D.next^2) a = x := by
    change (D.next^2) (D.next x) = x
    simpa only [pow_succ,Perm.mul_apply] using hx3
  have h42 : D.label (D.next b) = flip (D.label ((D.next^2) a)) := by
    have he : D.label x = flip (D.label (D.next b)) := hback.trans (D.reverse_label (D.next b))
    rw [hax,he,hflip]
  have h51 : D.label ((D.next^2) b) = flip (D.label (D.next a)) := by
    apply hunique (D.label b) (D.label (D.next b)) _ _ hfb
    rw [h42]
    change face (D.label (D.reverse a)) (flip (D.label ((D.next^2) a))) (flip (D.label (D.next a)))
    rw [D.reverse_label]
    exact hmirror _ _ _ hfa
  have hab : ¬ D.next.SameCycle a b := D.reverse_not_sameCycle a hf
  let e := trianglePairEmbedding D.next a b hp hne hp' hne' hab
  obtain ⟨he0,he1,he2,he3,he4,he5⟩ := trianglePairEmbedding_values D.next a b hp hne hp' hne' hab
  have hnext : ∀ j, D.next (e j) = e (dipoleFace j) := by
    have h3 : D.next ((D.next^2) a) = a := by simpa only [pow_succ',Perm.mul_apply] using hp
    have h3' : D.next ((D.next^2) b) = b := by simpa only [pow_succ',Perm.mul_apply] using hp'
    intro j
    fin_cases j <;> first | rfl | exact h3 | exact h3'
  obtain ⟨h01,h12,_⟩ := hf _ _ _ hfa
  refine ⟨{
    dart := e
    next_dart := hnext
    reverse_zero := by rw [he0,he3]
    color10 := by rw [he1,he0]; exact h01.symm
    color21 := by rw [he2,he1]; exact h12.symm
    label51 := by rw [he5,he1]; exact h51
    label42 := by rw [he4,he2]; exact h42 }⟩

theorem noDipole_link_reduced
    (hf : ∀ a b c, face a b c → color a ≠ color b ∧ color b ≠ color c ∧ color c ≠ color a)
    (hflip : ∀ e, flip (flip e) = e)
    (hmirror : ∀ a b c, face a b c → face (flip a) (flip c) (flip b))
    (hunique : ∀ a b c c', face a b c → face a b c' → c = c')
    (hD : IsEmpty D.Dipole)
    (x : D.Dart) :
    D.label x ≠ D.label ((D.reverse*D.next) ((D.reverse*D.next) x)) := by
  intro h
  obtain ⟨P⟩ := D.dipole_of_link_backtrack hf hflip hmirror hunique x h
  exact hD.false P

abbrev vertexPerm : Perm D.Dart := D.reverse*D.next

noncomputable def paint (q : V → Fin 3) : Cycles D.vertexPerm → Fin 3 :=
  descend D.vertexPerm (fun a => q (color (D.label a)))
    (fun a => congrArg q (D.color_next a))

@[simp] theorem paint_cl (q : V → Fin 3) (a : D.Dart) :
    D.paint q (cl D.vertexPerm a) = q (color (D.label a)) := descend_cl _ _ _ _

noncomputable def vertexAngle (q : V → Fin 3) (v : Cycles D.vertexPerm) : ℝ :=
  TriangleRibbon.weight (D.paint q v) * Fintype.card {a : D.Dart // cl D.vertexPerm a = v}

theorem sum_angles (q : V ≃ Fin 3)
    (hf : ∀ a b c, face a b c → color a ≠ color b ∧ color b ≠ color c ∧ color c ≠ color a) :
    ∑ v, D.vertexAngle q v = 5 * Fintype.card (Cycles D.next) := by
  have hfiber (c : Cycles D.next) :
      (∑ a : {a : D.Dart // cl D.next a = c},
        TriangleRibbon.weight (q (color (D.label a)))) = 5 := by
    obtain ⟨a,rfl⟩ := cl_surjective D.next c
    obtain ⟨hp,hn,hface⟩ := D.triangular a
    obtain ⟨hab,hbc,hca⟩ := hf _ _ _ hface
    have hb := three_color_bijective D.next a (fun a => q (color (D.label a))) hp hn
      (fun h => hab (q.injective h)) (fun h => hbc (q.injective h))
      (fun h => hca (q.injective h))
    have he := (Equiv.ofBijective _ hb).sum_comp TriangleRibbon.weight
    have he' : (∑ x : {x : D.Dart // cl D.next x = cl D.next a},
        TriangleRibbon.weight (q (color (D.label x)))) = ∑ i, TriangleRibbon.weight i := he
    rw [he']
    norm_num [Fin.sum_univ_succ,TriangleRibbon.weight]
  have hv : ∑ v, D.vertexAngle q v =
      ∑ a : D.Dart, TriangleRibbon.weight (q (color (D.label a))) := by
    have he := (Equiv.sigmaFiberEquiv (cl D.vertexPerm)).sum_comp
      (fun a => TriangleRibbon.weight (q (color (D.label a))))
    simp only [Fintype.sum_sigma,Equiv.sigmaFiberEquiv_apply] at he
    rw [← he]
    apply Finset.sum_congr rfl
    intro v _
    have hie (a : {a : D.Dart // cl D.vertexPerm a = v}) :
        q (color (D.label a)) = D.paint q v := by
      rw [← D.paint_cl q a,a.property]
    simp only [hie,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,vertexAngle,mul_comm]
  rw [hv]
  have he := (Equiv.sigmaFiberEquiv (cl D.next)).sum_comp
    (fun a => TriangleRibbon.weight (q (color (D.label a))))
  simp only [Fintype.sum_sigma,Equiv.sigmaFiberEquiv_apply] at he
  rw [← he]
  simp only [hfiber,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_comm]

theorem local_angle_lower (q : V → Fin 3) (L : SimpleGraph E)
    (hadj : ∀ a b c, face a b c → L.Adj a (flip b))
    (hred : ∀ a, D.label a ≠ D.label (D.vertexPerm (D.vertexPerm a)))
    (hclosed : ∀ a (p : L.Walk a a), 0 < p.length → ReducedWalk p →
      10 ≤ TriangleRibbon.weight (q (color a)) * p.length)
    (v : Cycles D.vertexPerm) : 10 ≤ D.vertexAngle q v := by
  obtain ⟨a,rfl⟩ := cl_surjective D.vertexPerm v
  let n := (orbit D.vertexPerm a).card
  let seq := fun i : ℕ => D.label ((D.vertexPerm^i) a)
  have hn : 0 < n := by
    change 0 < (orbit D.vertexPerm a).card
    rw [orbit_card_eq_minimalPeriod]
    exact minimalPeriod_pos _ _
  have hstep (b : D.Dart) : L.Adj (D.label b) (D.label (D.vertexPerm b)) := by
    change L.Adj (D.label b) (D.label (D.reverse (D.next b)))
    rw [D.reverse_label]
    exact hadj _ _ _ (D.triangular b).2.2
  have hs (i : ℕ) (_hi : i < n) : L.Adj (seq i) (seq (i+1)) := by
    simpa only [seq,pow_succ',Perm.mul_apply] using hstep ((D.vertexPerm^i) a)
  have hres (i : ℕ) (_hi : i+2 ≤ n) : seq i ≠ seq (i+2) := by
    simpa only [seq,show i+2 = (i+1)+1 by omega,pow_succ',Perm.mul_apply] using
      hred ((D.vertexPerm^i) a)
  have hend : seq n = D.label a := congrArg D.label (pow_card_orbit D.vertexPerm a)
  let p := (SequenceWalk.walk L seq n hs).copy (show seq 0 = D.label a from rfl) hend
  have hlen : p.length = n := (SimpleGraph.Walk.length_copy _ _ _).trans
    (SequenceWalk.length_walk L seq n hs)
  have hp : ReducedWalk p := by
    intro i hi
    simpa only [p,SimpleGraph.Walk.getVert_copy] using
      SequenceWalk.reduced_walk L seq n hs hres i
        (by simpa only [p,SimpleGraph.Walk.length_copy] using hi)
  have h := hclosed (D.label a) p (by rw [hlen]; exact hn) hp
  simpa only [vertexAngle,paint_cl,card_fiber,hlen,n] using h

/-- Angular Gauss--Bonnet on a closed genus-zero map forbids a nonempty reduced
sphere. This is a statement about actual finite permutation maps, not an
asphericity or torsion-freeness assumption. -/
theorem empty_of_angles (q : V ≃ Fin 3)
    (hf : ∀ a b c, face a b c → color a ≠ color b ∧ color b ≠ color c ∧ color c ≠ color a)
    (hmin : ∀ v, 10 ≤ D.vertexAngle q v) : IsEmpty D.Dart := by
  have hs := D.sum_angles q hf
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun v _ => hmin v)
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul] at hsum
  rw [hs] at hsum
  have hr := card_eq_mul_cycles D.reverse 2
    (orbit_card_involution D.reverse D.reverse_involutive D.reverse_ne)
  have hfcard := card_eq_mul_cycles D.next 3
    (fun a => orbit_card_three D.next a (D.triangular a).1 (D.triangular a).2.1)
  have he := D.planar
  simp only [PlanarMap,cycleCount,Nat.card_eq_fintype_card] at he
  have hzero : Fintype.card (Quotient (components D.reverse D.next)) = 0 := by
    have hs' : 2 * Fintype.card (Cycles D.vertexPerm) ≤ Fintype.card (Cycles D.next) := by
      have : (2 : ℝ) * Fintype.card (Cycles D.vertexPerm) ≤ Fintype.card (Cycles D.next) := by
        linarith
      exact_mod_cast this
    change 2 * Fintype.card (Cycles (D.reverse * D.next)) ≤ Fintype.card (Cycles D.next) at hs'
    unfold componentCount at he
    rw [Nat.card_eq_fintype_card] at he
    omega
  exact ⟨fun a => (Fintype.card_pos_iff.mpr ⟨Quotient.mk _ a⟩).ne' hzero⟩

end TriangleSphere
end Release075

namespace Release075.MarkedLineData
open Equiv PermCycles
variable {q r : ℕ} [Fact q.Prime] (d : MarkedLineData q r) (hr : 0 < r)

/-- Every nonempty spherical map over the actual presentation has a dipole. -/
theorem sphere_empty_of_noDipole
    (D : TriangleSphere (d.presentation hr).flipEdge (d.presentation hr).edgeTarget
      (d.presentation hr).TriangleFace) (hD : IsEmpty D.Dipole) : IsEmpty D.Dart := by
  let L := (d.allLink hr).comap (d.linkDirection hr)
  apply D.empty_of_angles (d.presentation hr).vertexColor
    (fun _ _ _ => BlockPresentation.TriangleFace.colors _)
  apply D.local_angle_lower (d.presentation hr).vertexColor L
    (fun _ _ _ h => d.face_corner_adj hr h)
    (D.noDipole_link_reduced
      (fun _ _ _ => BlockPresentation.TriangleFace.colors _)
      (d.presentation hr).flipEdge_flipEdge
      (fun _ _ _ => BlockPresentation.TriangleFace.mirror _)
      (fun _ _ _ _ => BlockPresentation.TriangleFace.unique _) hD)
  intro a p hn hp
  let f : L →g d.allLink hr := SimpleGraph.Hom.comap (d.linkDirection hr) (d.allLink hr)
  have h := d.allLink_closed hr _ (p.map f)
    (by simpa only [SimpleGraph.Walk.length_map] using hn)
    (hp.map f (fun _ _ _ _ _ h => d.linkDirection_injective hr h))
  simp only [SimpleGraph.Walk.length_map] at h
  change 12 ≤ TriangleRibbon.weight (d.linkColor hr (d.linkDirection hr a)) * p.length at h
  rw [d.linkDirection_color hr] at h
  linarith

end Release075.MarkedLineData

namespace Release075.TriangleSphere
open Equiv PermCycles
attribute [local instance] Classical.propDecidable Classical.decEq
variable {E V M : Type} [AddCommGroup M]
variable {flip : E → E} {color : E → V} {face : E → E → E → Prop}

/-- Evaluate once at every oriented corner. For cyclic face values this is three
 times the ordinary integral face chain; no unproved chain-complex property is used. -/
def cornerSum (D : TriangleSphere flip color face) (F : E → E → E → M) : M :=
  ∑ a, F (D.label a) (D.label (D.next a)) (D.label ((D.next^2) a))

/-- Remove an actual dipole, preserving every additive cyclic antisymmetric
face evaluation. -/
theorem Dipole.delete {D : TriangleSphere flip color face} (P : D.Dipole)
    (F : E → E → E → M)
    (hrot : ∀ a b c, face a b c → F b c a = F a b c)
    (hmir : ∀ a b c, face a b c → F (flip a) (flip c) (flip b) = -F a b c) :
    ∃ D' : TriangleSphere flip color face,
      Fintype.card D'.Dart < Fintype.card D.Dart ∧ D'.cornerSum F = D.cornerSum F := by
  let e := P.dart
  have h14 : color (D.label (e 1)) = color (D.label (e 4)) := by
    have h := D.color_next (P.dart 1)
    simp only [Perm.mul_apply,P.next_dart,dipoleFace_one,D.reverse_label] at h
    exact h.symm.trans (congrArg color P.label42.symm)
  obtain ⟨r',hi',hn',hp',hc',he',heq,_⟩ :=
    isolate_dipole D.reverse D.next D.reverse_involutive D.reverse_ne
      (color ∘ D.label) D.color_next e P.next_dart P.reverse_zero
      P.color10 P.color21 h14 D.planar
  have hl₁ : ∀ z, D.label (rePair D.reverse (e 1) (e 5) z) = flip (D.label z) :=
    rePair_labels D.reverse D.label flip D.reverse_label
      ((D.reverse_label (e 1)).trans P.label51.symm)
  have hl' : ∀ z, D.label (r' z) = flip (D.label z) := by
    rw [heq]
    exact rePair_labels _ D.label flip hl₁ ((hl₁ (e 2)).trans P.label42.symm)
  let hr : ∀ a, (r' a ∉ Set.range e) ↔ (a ∉ Set.range e) :=
    fun a => not_congr (range_invariant r' dipoleReverse e he' a)
  let hf : ∀ a, (D.next a ∉ Set.range e) ↔ (a ∉ Set.range e) :=
    fun a => not_congr (range_invariant D.next dipoleFace e P.next_dart a)
  let D' : TriangleSphere flip color face := {
    Dart := {a : D.Dart // a ∉ Set.range e}
    reverse := r'.subtypePerm hr
    next := D.next.subtypePerm hf
    reverse_involutive := fun a => Subtype.ext (hi' a.val)
    reverse_ne := fun a h => hn' a.val (congrArg Subtype.val h)
    label := D.label ∘ Subtype.val
    reverse_label := fun a => hl' a.val
    color_next := fun a => hc' a.val
    planar := by
      simpa only [PlanarMap,← Nat.card_eq_fintype_card] using
        hp'.restrict (fun a => a ∉ Set.range e) hr hf
    triangular := fun a => ⟨Subtype.ext (D.triangular a.val).1,
      fun h => (D.triangular a.val).2.1 (congrArg Subtype.val h),(D.triangular a.val).2.2⟩ }
  refine ⟨D',?_,?_⟩
  · exact Fintype.card_subtype_lt (x := e 0) (not_not.mpr ⟨0,rfl⟩)
  let f : D.Dart → M := fun a => F (D.label a) (D.label (D.next a)) (D.label ((D.next^2) a))
  have hcycle (a : D.Dart) : f (D.next a) = f a := by
    have h3' : (D.next^2) (D.next a) = a := by
      simpa only [pow_succ,Perm.mul_apply] using (D.triangular a).1
    change F (D.label (D.next a)) (D.label ((D.next^2) a))
      (D.label ((D.next^2) (D.next a))) = _
    rw [h3']
    exact hrot _ _ _ (D.triangular a).2.2
  have hecycle (j : Fin 6) : f (e (dipoleFace j)) = f (e j) := by
    rw [← P.next_dart]
    exact hcycle _
  have heNext (j : Fin 6) : D.next (e j) = e (dipoleFace j) := P.next_dart j
  have he42 : D.label (e 4) = flip (D.label (e 2)) := P.label42
  have he51 : D.label (e 5) = flip (D.label (e 1)) := P.label51
  have h03 : f (e 3) = - f (e 0) := by
    have hz : D.label (e 3) = flip (D.label (e 0)) := by
      rw [← P.reverse_zero,D.reverse_label]
    have hs (j : Fin 6) : (D.next^2) (e j) = e (dipoleFace (dipoleFace j)) := by
      simp only [pow_two,Perm.mul_apply,heNext]
    simp only [f,heNext,hs,dipoleFace_zero,dipoleFace_one,
      dipoleFace_three,dipoleFace_four]
    rw [hz,he42,he51]
    exact hmir _ _ _ (by simpa only [heNext,hs,dipoleFace_zero,dipoleFace_one] using
      (D.triangular (e 0)).2.2)
  have hsix : ∑ j : Fin 6, f (e j) = 0 := by
    have h1 := hecycle 0
    have h2 := hecycle 1
    have h4 := hecycle 3
    have h5 := hecycle 4
    simp only [dipoleFace_zero,dipoleFace_one,dipoleFace_three,dipoleFace_four] at h1 h2 h4 h5
    simp only [Fin.sum_univ_succ,Fin.succ_zero_eq_one]
    change f (e 0)+(f (e 1)+(f (e 2)+(f (e 3)+(f (e 4)+(f (e 5)+0))))) = 0
    rw [h2,h1,h5,h4,h03]
    abel
  have hrange : ∑ a : {a : D.Dart // a ∈ Set.range e}, f a = 0 := by
    have h := (Equiv.ofInjective e e.injective).sum_comp (fun a => f a.val)
    exact h.symm.trans hsix
  have hpart : (∑ a : {a : D.Dart // a ∈ Set.range e}, f a.val) +
      (∑ a : {a : D.Dart // a ∉ Set.range e}, f a.val) = ∑ a, f a := by
    simpa only [Fintype.sum_sum_type,Equiv.sumCompl_apply_inl,Equiv.sumCompl_apply_inr] using
      (Equiv.sumCompl (fun a => a ∈ Set.range e)).sum_comp f
  rw [hrange,zero_add] at hpart
  exact hpart

/-- Diagrammatic reducibility annihilates integral spherical face chains. -/
theorem cornerSum_eq_zero
    (hempty : ∀ D : TriangleSphere flip color face, IsEmpty D.Dipole → IsEmpty D.Dart)
    (F : E → E → E → M)
    (hrot : ∀ a b c, face a b c → F b c a = F a b c)
    (hmir : ∀ a b c, face a b c → F (flip a) (flip c) (flip b) = -F a b c)
    (D : TriangleSphere flip color face) : D.cornerSum F = 0 := by
  generalize hn : Fintype.card D.Dart = n
  induction n using Nat.strong_induction_on generalizing D with
  | h n ih =>
    by_cases hd : Nonempty D.Dipole
    · obtain ⟨P⟩ := hd
      obtain ⟨D',hlt,he⟩ := P.delete F hrot hmir
      rw [← he]
      exact ih (Fintype.card D'.Dart) (hn ▸ hlt) D' rfl
    · have : IsEmpty D.Dart := hempty D (not_nonempty_iff.mp hd)
      exact Finset.sum_eq_zero (fun b _ => isEmptyElim b)

end Release075.TriangleSphere

namespace Release075.TriangleSphere
open Equiv PermCycles
variable {I B : Type} {r : ℕ} {d : BlockPresentation I B r}

def forgetLift (D : TriangleSphere d.liftedFlip d.liftedTarget d.LiftedFace) :
    TriangleSphere d.flipEdge d.edgeTarget d.TriangleFace where
  Dart := D.Dart
  reverse := D.reverse
  next := D.next
  reverse_involutive := D.reverse_involutive
  reverse_ne := D.reverse_ne
  label a := (D.label a).1
  reverse_label a := congrArg Prod.fst (D.reverse_label a)
  color_next a := congrArg Prod.fst (D.color_next a)
  planar := D.planar
  triangular a := let ht := D.triangular a; ⟨ht.1,ht.2.1,ht.2.2.1⟩

/-- Matching opposite face labels at a shared lifted edge forces matching group
coordinates on the other two edges. Thus reduction cannot hide a downstairs dipole. -/
def Dipole.lift {D : TriangleSphere d.liftedFlip d.liftedTarget d.LiftedFace}
    (P : D.forgetLift.Dipole) : D.Dipole := by
  have hn (j) : D.next (P.dart j) = P.dart (dipoleFace j) := P.next_dart j
  have hc (j) : d.liftedTarget (d.liftedFlip (D.label (P.dart (dipoleFace j)))) =
      d.liftedTarget (D.label (P.dart j)) := by
    have hh := D.color_next (P.dart j)
    change d.liftedTarget (D.label (D.reverse (D.next (P.dart j)))) =
      d.liftedTarget (D.label (P.dart j)) at hh
    exact (congrArg d.liftedTarget (D.reverse_label (P.dart (dipoleFace j)))).symm.trans
      (by simpa only [hn] using hh)
  have hrev : D.label (P.dart 3) = d.liftedFlip (D.label (P.dart 0)) := by
    rw [← P.reverse_zero]
    exact D.reverse_label _
  have h0 := hc 0
  have h5 := hc 5
  simp only [dipoleFace_zero] at h0
  simp only [dipoleFace_five,hrev,d.liftedFlip_flip] at h5
  have h51 : D.label (P.dart 5) = d.liftedFlip (D.label (P.dart 1)) :=
    Prod.ext P.label51 (congrArg (fun x : d.LiftedVertex => x.2) (h5.symm.trans h0.symm))
  have h1 := hc 1
  have h4 := hc 4
  simp only [dipoleFace_one] at h1
  simp only [dipoleFace_four,h51,d.liftedFlip_flip] at h4
  have h42 : D.label (P.dart 4) = d.liftedFlip (D.label (P.dart 2)) :=
    Prod.ext P.label42 (congrArg (fun x : d.LiftedVertex => x.2) (h4.symm.trans h1.symm))
  exact {
    dart := P.dart
    next_dart := P.next_dart
    reverse_zero := P.reverse_zero
    color10 := fun h => P.color10 (congrArg Prod.fst h)
    color21 := fun h => P.color21 (congrArg Prod.fst h)
    label51 := h51
    label42 := h42 }

theorem noDipole_forgetLift {D : TriangleSphere d.liftedFlip d.liftedTarget d.LiftedFace}
    (h : IsEmpty D.Dipole) : IsEmpty D.forgetLift.Dipole := ⟨fun P => h.false P.lift⟩

end Release075.TriangleSphere

namespace Release075.MarkedLineData
variable {q r : ℕ} [Fact q.Prime] (d : MarkedLineData q r) (hr : 0 < r)

theorem lifted_sphere_empty_of_noDipole
    (D : TriangleSphere (d.presentation hr).liftedFlip (d.presentation hr).liftedTarget
      (d.presentation hr).LiftedFace) (hD : IsEmpty D.Dipole) : IsEmpty D.Dart :=
  d.sphere_empty_of_noDipole hr D.forgetLift (TriangleSphere.noDipole_forgetLift hD)

end Release075.MarkedLineData

end OAI
end
end

section
section
namespace OAI

namespace Release075
open Equiv PermCycles

/-- Unlike an ordinary filling, this records *every* connected component.
The only nontriangular interior faces allowed are isolated two-dart spheres,
created when an exterior cancellable pair is folded. -/
structure FullFilling {E V : Type} (flip : E → E) (color : E → V)
    (face : E → E → E → Prop) (w : List E) where
  Dart : Type
  [dartFintype : Fintype Dart]
  reverse : Perm Dart
  next : Perm Dart
  reverse_involutive : Function.Involutive reverse
  reverse_ne : ∀ a, reverse a ≠ a
  label : Dart → E
  reverse_label : ∀ a, label (reverse a) = flip (label a)
  color_next : ∀ a, color (label ((reverse*next) a)) = color (label a)
  planar : PlanarMap reverse next
  boundary : List Dart
  boundary_cycle : IsBoundary next boundary
  boundary_word : boundary.map label = w
  cells : ∀ a, a ∉ boundary →
    ((next^3) a = a ∧ next a ≠ a ∧ face (label a) (label (next a)) (label ((next^2) a))) ∨
      (next a = reverse a ∧ (next^2) a = a)

attribute [instance] FullFilling.dartFintype

theorem IsBoundary.of_injective_map {A B : Type*} {f : Perm A} {g : Perm B}
    {l : List B} {e : B → A} (he : Function.Injective e) (hg : ∀ b, e (g b) = f (e b))
    (h : IsBoundary f (l.map e)) : IsBoundary g l := by
  classical
  refine ⟨h.1.of_map _,?_⟩
  intro b hb
  apply he
  rw [hg,h.2 _ (List.mem_map.mpr ⟨b,hb,rfl⟩)]
  exact formPerm_embedding ⟨e,he⟩ l b

namespace TriangleFilling
attribute [local instance] Classical.propDecidable Classical.decEq
variable {E V : Type} {flip : E → E} {color : E → V} {face : E → E → E → Prop}

/-- Discarding components disjoint from the outer face makes an ordinary
filling into a full filling, with no exceptional faces. -/
noncomputable abbrev full {w : List E} (D : TriangleFilling flip color face w) :
    FullFilling flip color face w where
  Dart := D.ActiveDart
  reverse := D.activeReverse
  next := D.activeNext
  reverse_involutive := D.activeReverse_involutive
  reverse_ne := D.activeReverse_ne
  label a := D.label a.val
  reverse_label a := D.reverse_label a.val
  color_next a := D.color_next a.val
  planar := D.active_planar
  boundary := D.boundary.pmap (fun a h => ⟨a,D.active_of_mem h⟩) (fun _ h => h)
  boundary_cycle := by
    apply IsBoundary.of_injective_map (f := D.next) Subtype.val_injective (fun _ => rfl)
    simpa only [List.map_pmap,List.pmap_eq_map,List.map_id_fun',id_eq] using D.boundary_cycle
  boundary_word := by simpa only [List.map_pmap,List.pmap_eq_map] using D.boundary_word
  cells := by
    intro a ha
    have hn : a.val ∉ D.boundary := by
      intro h
      apply ha
      exact List.mem_pmap.mpr ⟨a.val,h,rfl⟩
    have ht := D.triangular a.val a.property hn
    exact Or.inl ⟨Subtype.ext ht.1,fun he => ht.2.1 (congrArg Subtype.val he),ht.2.2⟩

end TriangleFilling

namespace FullFilling
attribute [local instance] Classical.propDecidable Classical.decEq
variable {E V M : Type} [AddCommGroup M]
variable {flip : E → E} {color : E → V} {face : E → E → E → Prop}
variable {w : List E} (D : FullFilling flip color face w)

def Bigon (a : D.Dart) : Prop := D.next a = D.reverse a ∧ (D.next^2) a = a

theorem bigon_reverse (a : D.Dart) : D.Bigon (D.reverse a) ↔ D.Bigon a := by
  have step (a : D.Dart) (h : D.Bigon a) : D.Bigon (D.reverse a) := by
    have hna : D.next (D.reverse a) = a := by
      rw [← h.1]
      exact h.2
    exact ⟨hna.trans (D.reverse_involutive a).symm,by
      simp only [pow_two,Perm.mul_apply,hna,h.1]⟩
  exact ⟨fun h => D.reverse_involutive a ▸ step _ h,step _⟩

theorem bigon_next (a : D.Dart) : D.Bigon (D.next a) ↔ D.Bigon a := by
  constructor
  · intro h
    have hna : D.next a = D.reverse a := by
      have h2 : D.next (D.next a) = a := D.next.injective h.2
      have hh : D.reverse (D.next a) = a := h.1.symm.trans h2
      exact (D.reverse_involutive (D.next a)).symm.trans (congrArg D.reverse hh)
    exact ⟨hna,D.next.injective h.2⟩
  · intro h
    rw [h.1]
    exact (D.bigon_reverse a).mpr h

/-- Integral corner evaluation, with the outer face omitted. -/
noncomputable def trace (F : E → E → E → M) : M :=
  ∑ a, if a ∈ D.boundary then 0 else
    F (D.label a) (D.label (D.next a)) (D.label ((D.next^2) a))

noncomputable abbrev rotate (n : ℕ) : FullFilling flip color face (w.rotate n) where
  Dart := D.Dart
  reverse := D.reverse
  next := D.next
  reverse_involutive := D.reverse_involutive
  reverse_ne := D.reverse_ne
  label := D.label
  reverse_label := D.reverse_label
  color_next := D.color_next
  planar := D.planar
  boundary := D.boundary.rotate n
  boundary_cycle := D.boundary_cycle.rotate n
  boundary_word := by rw [List.map_rotate,D.boundary_word]
  cells := by intro a ha; exact D.cells a (by simpa only [List.mem_rotate] using ha)

theorem trace_rotate (n : ℕ) (F : E → E → E → M) : (D.rotate n).trace F = D.trace F := by
  unfold trace
  dsimp only [rotate]
  simp only [List.mem_rotate]

noncomputable abbrev mirror (hflip : Function.Involutive flip)
    (hface : ∀ a b c, face a b c → face (flip a) (flip c) (flip b)) :
    FullFilling flip color face (w.reverse.map flip) where
  Dart := D.Dart
  reverse := D.reverse
  next := D.next⁻¹
  reverse_involutive := D.reverse_involutive
  reverse_ne := D.reverse_ne
  label := flip ∘ D.label
  reverse_label := by intro a; simp only [Function.comp_apply,D.reverse_label]
  color_next := by
    intro a
    simp only [Function.comp_apply,Perm.mul_apply,D.reverse_label]
    rw [hflip]
    have h := D.color_next (D.next⁻¹ a)
    simpa only [Perm.mul_apply,perm_apply_inv,D.reverse_label] using h.symm
  planar := D.planar.inv_right D.reverse_involutive
  boundary := D.boundary.reverse
  boundary_cycle := D.boundary_cycle.reverse
  boundary_word := by rw [← List.map_map,List.map_reverse,D.boundary_word]
  cells := by
    intro a hn
    rcases D.cells a (by simpa only [List.mem_reverse] using hn) with ht | hb
    · have he := inv_cycle_three D.next ht.1
      refine Or.inl ⟨he.2.2,?_,?_⟩
      · intro h
        apply ht.2.1
        have hh := congrArg D.next h
        simpa only [perm_apply_inv] using hh.symm
      · simp only [Function.comp_apply,he.1,he.2.1]
        exact hface _ _ _ ht.2.2
    · have he : D.next⁻¹ a = D.next a := by
        apply D.next.injective
        simpa only [perm_apply_inv,pow_two,Perm.mul_apply] using hb.2.symm
      refine Or.inr ⟨he.trans hb.1,?_⟩
      rw [pow_two,Perm.mul_apply,he]
      exact D.next.symm_apply_apply a

theorem trace_mirror (hflip : Function.Involutive flip)
    (hface : ∀ a b c, face a b c → face (flip a) (flip c) (flip b))
    (F : E → E → E → M)
    (hmir : ∀ a b c, face a b c → F (flip a) (flip c) (flip b) = -F a b c)
    (hdeg : ∀ a b, F a b a = 0) :
    (D.mirror hflip hface).trace F = - D.trace F := by
  rw [trace,trace,← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro a _
  dsimp only [mirror,Function.comp_apply]
  by_cases ha : a ∈ D.boundary
  · simp only [List.mem_reverse,ha,ite_true,neg_zero]
  simp only [List.mem_reverse,ha,ite_false]
  rcases D.cells a ha with ht | hb
  · have he := inv_cycle_three D.next ht.1
    rw [he.1,he.2.1]
    exact hmir _ _ _ ht.2.2
  · have he : ((D.next⁻¹)^2) a = a := by
      rw [inv_pow]
      apply (D.next^2).injective
      simpa only [perm_apply_inv,pow_two,Perm.mul_apply] using hb.2.symm
    rw [he,hb.2,hdeg,hdeg,neg_zero]

end FullFilling
end Release075

namespace Release075.FullFilling
open Equiv PermCycles
attribute [local instance] Classical.propDecidable Classical.decEq
variable {E V M : Type} [AddCommGroup M]
variable {flip : E → E} {color : E → V} {face : E → E → E → Prop}

/-- A closed full filling is a disjoint union of triangular spheres and the
explicit isolated bigons. Consequently its integral cyclic evaluation vanishes. -/
theorem trace_empty
    (hempty : ∀ D : TriangleSphere flip color face, IsEmpty D.Dipole → IsEmpty D.Dart)
    (F : E → E → E → M)
    (hrot : ∀ a b c, face a b c → F b c a = F a b c)
    (hmir : ∀ a b c, face a b c → F (flip a) (flip c) (flip b) = -F a b c)
    (hdeg : ∀ a b, F a b a = 0)
    (D : FullFilling flip color face []) : D.trace F = 0 := by
  have hb : D.boundary = [] := List.map_eq_nil_iff.mp D.boundary_word
  let hr : ∀ a, ¬D.Bigon (D.reverse a) ↔ ¬D.Bigon a := fun a => not_congr (D.bigon_reverse a)
  let hf : ∀ a, ¬D.Bigon (D.next a) ↔ ¬D.Bigon a := fun a => not_congr (D.bigon_next a)
  let S : TriangleSphere flip color face := {
    Dart := {a : D.Dart // ¬D.Bigon a}
    reverse := D.reverse.subtypePerm hr
    next := D.next.subtypePerm hf
    reverse_involutive := fun a => Subtype.ext (D.reverse_involutive a.val)
    reverse_ne := fun a h => D.reverse_ne a.val (congrArg Subtype.val h)
    label := D.label ∘ Subtype.val
    reverse_label := fun a => D.reverse_label a.val
    color_next := fun a => D.color_next a.val
    planar := by
      simpa only [PlanarMap,← Nat.card_eq_fintype_card] using
        D.planar.restrict (fun a => ¬D.Bigon a) hr hf
    triangular := by
      intro a
      have ht := (D.cells a.val (by simp [hb])).resolve_right a.property
      exact ⟨Subtype.ext ht.1,fun h => ht.2.1 (congrArg Subtype.val h),ht.2.2⟩ }
  have hz := TriangleSphere.cornerSum_eq_zero hempty F hrot hmir S
  let f : D.Dart → M := fun a => F (D.label a) (D.label (D.next a)) (D.label ((D.next^2) a))
  have hpart := (Equiv.sumCompl D.Bigon).sum_comp f
  have hsum : (∑ a : {a : D.Dart // D.Bigon a}, f a.val) +
      (∑ a : {a : D.Dart // ¬D.Bigon a}, f a.val) = ∑ a, f a := by
    simpa only [Fintype.sum_sum_type,Equiv.sumCompl_apply_inl,Equiv.sumCompl_apply_inr] using hpart
  have hbig : (∑ a : {a : D.Dart // D.Bigon a}, f a.val) = 0 := by
    apply Finset.sum_eq_zero
    intro a _
    dsimp only [f]
    rw [a.property.2,hdeg]
  have htri : (∑ a : {a : D.Dart // ¬D.Bigon a}, f a.val) = 0 := hz
  rw [hbig,htri,zero_add] at hsum
  simpa only [trace,hb,List.not_mem_nil,ite_false] using hsum.symm

end Release075.FullFilling

namespace Release075.FullFilling
open Equiv PermCycles
attribute [local instance] Classical.propDecidable Classical.decEq
variable {E V M : Type} [AddCommGroup M]
variable {flip : E → E} {color : E → V} {face : E → E → E → Prop}

omit [AddCommGroup M] in
theorem bigon_component {w : List E} (D : FullFilling flip color face w)
    {a b : D.Dart} (ha : D.Bigon a) (h : components D.reverse D.next a b) :
    b = a ∨ b = D.reverse a := by
  have hn : D.next (D.reverse a) = a := by rw [← ha.1]; exact ha.2
  exact (components_pred D.reverse D.next (fun z => z=a ∨ z=D.reverse a)
    (pair_invariant D.reverse rfl (D.reverse_involutive a))
    (pair_invariant D.next ha.1 hn) h).mp (Or.inl rfl)

/-- Exterior cancellation retains all components and preserves the face chain. -/
theorem fold {w : List E} (D : FullFilling flip color face w)
    (hflip : Function.Involutive flip) (hne : ∀ e, color e ≠ color (flip e))
    {a b : D.Dart} {l : List D.Dart} (hb : D.boundary = b::a::l)
    (hl : D.label a = flip (D.label b)) (F : E → E → E → M)
    (hdeg : ∀ a b, F a b a = 0) :
    ∃ D' : FullFilling flip color face (l.map D.label), D'.trace F = D.trace F := by
  have hbound : IsBoundary D.next (b::a::l) := hb ▸ D.boundary_cycle
  have hab : a ≠ b := fun h => hbound.1.notMem (by simp [h])
  have hba : D.next b = a := by simpa using hbound.step 0 (by simp)
  obtain ⟨r',f',hi',hn',hp',hl',hc',hra,hrb,hfa,hfb,hm,_,heq⟩ :=
    fold_pair D.reverse D.next D.reverse_involutive D.reverse_ne D.label flip hflip
      color hne D.reverse_label D.color_next D.planar hab hba hl
  have hrest := hbound.erase_pair
  rw [←heq] at hrest
  let D' : FullFilling flip color face (l.map D.label) := {
    Dart := D.Dart
    reverse := r'
    next := f'
    reverse_involutive := hi'
    reverse_ne := hn'
    label := D.label
    reverse_label := hl'
    color_next := hc'
    planar := hp'
    boundary := l
    boundary_cycle := hrest.1
    boundary_word := rfl
    cells := by
      intro z hz
      by_cases hza : z = a
      · subst z
        exact Or.inr ⟨hfa.trans hra.symm,by simp only [pow_two,Perm.mul_apply,hfa,hfb]⟩
      by_cases hzb : z = b
      · subst z
        exact Or.inr ⟨hfb.trans hrb.symm,by simp only [pow_two,Perm.mul_apply,hfa,hfb]⟩
      have hzo : z ∉ b::a::l := by simp only [List.mem_cons]; tauto
      have hstep := hrest.2 z hzo
      have he (n : ℕ) := same_outside_boundary_pow hbound hrest.2 hzo n
      rcases D.cells z (by rwa [hb]) with ht | hg
      · exact Or.inl ⟨(he 3).trans ht.1,hstep ▸ ht.2.1,by
          simpa only [hstep,he 2] using ht.2.2⟩
      · have hrz : r' z = D.reverse z := by
          apply (D.bigon_component hg (hm ?_)).resolve_left (hn' z)
          exact (show Perm.SameCycle.setoid r' ≤ components r' f' from le_sup_left)
            (Perm.sameCycle_apply_right.mpr (Perm.SameCycle.refl r' z))
        exact Or.inr ⟨hstep.trans (hg.1.trans hrz.symm),(he 2).trans hg.2⟩ }
  refine ⟨D',?_⟩
  unfold trace
  apply Finset.sum_congr rfl
  intro z _
  change (if z ∈ l then 0 else F (D.label z) (D.label (f' z)) (D.label ((f'^2) z))) = _
  by_cases hz : z ∈ l
  · have hzo : z ∈ D.boundary := by rw [hb]; simp only [List.mem_cons]; tauto
    simp only [hz,hzo,ite_true]
  by_cases hza : z = a
  · subst z
    have hzo : a ∈ D.boundary := by rw [hb]; simp
    simp only [hz,hzo,ite_false,ite_true,pow_two,Perm.mul_apply,hfa,hfb,hdeg]
  by_cases hzb : z = b
  · subst z
    have hzo : b ∈ D.boundary := by rw [hb]; simp
    simp only [hz,hzo,ite_false,ite_true,pow_two,Perm.mul_apply,hfa,hfb,hdeg]
  have hzo : z ∉ b::a::l := by simp only [List.mem_cons]; tauto
  have hD : z ∉ D.boundary := by rwa [hb]
  simp only [hz,hD,ite_false,hrest.2 z hzo,
    same_outside_boundary_pow hbound hrest.2 hzo 2]

end Release075.FullFilling

end OAI
end
end

section
section
namespace OAI

namespace Release075.FullFilling
open Equiv PermCycles
attribute [local instance] Classical.propDecidable Classical.decEq
variable {E V M : Type} [AddCommGroup M]
variable {flip : E → E} {color : E → V} {face : E → E → E → Prop}

theorem wedge {w w' : List E} (D : FullFilling flip color face w)
    (D' : FullFilling flip color face w')
    {a : D.Dart} {b : D'.Dart} {l : List D.Dart} {l' : List D'.Dart}
    (ha : D.boundary = a::l) (hb : D'.boundary = b::l')
    (hc : color (flip (D.label a)) = color (flip (D'.label b)))
    (F : E → E → E → M) :
    ∃ C : FullFilling flip color face (w++w'), C.trace F = D.trace F + D'.trace F := by
  let : DecidableEq (D.Dart ⊕ D'.Dart) := Classical.decEq _
  let r := D.reverse.sumCongr D'.reverse
  let f := D.next.sumCongr D'.next
  let lab : D.Dart ⊕ D'.Dart → E := Sum.elim D.label D'.label
  let g := Equiv.swap (Sum.inl a) (Sum.inr b) * f
  let bd := (D.boundary.map Sum.inl) ++ (D'.boundary.map Sum.inr)
  have hleft : IsBoundary f ((a::l).map Sum.inl) :=
    (ha ▸ D.boundary_cycle).conjugate ⟨Sum.inl,Sum.inl_injective⟩ (fun _ => rfl)
  have hright : IsBoundary f ((b::l').map Sum.inr) :=
    (hb ▸ D'.boundary_cycle).conjugate ⟨Sum.inr,Sum.inr_injective⟩ (fun _ => rfl)
  have hdis : List.Disjoint ((a::l).map (@Sum.inl D.Dart D'.Dart))
      ((b::l').map Sum.inr) := by
    intro z hz hz'
    obtain ⟨x,_,rfl⟩ := List.mem_map.mp hz
    obtain ⟨y,_,hy⟩ := List.mem_map.mp hz'
    cases hy
  have hbd : IsBoundary g bd := by
    dsimp [g,bd]
    rw [ha,hb]
    exact hleft.join hright hdis
  have hsep : ¬ components r f (Sum.inl a) (Sum.inr b) := by
    intro h
    exact (components_pred r f leftPred (leftPred_sumCongr _ _)
      (leftPred_sumCongr _ _) h).mp True.intro
  have hr : ∀ z, lab (r z) = flip (lab z) := by
    intro z; cases z with
    | inl x => exact D.reverse_label x
    | inr x => exact D'.reverse_label x
  have hcol : ∀ z, color (lab ((r*f) z)) = color (lab z) := by
    intro z; cases z with
    | inl x => exact D.color_next x
    | inr x => exact D'.color_next x
  have hcg : ∀ z, color (lab ((r*g) z)) = color (lab z) := by
    apply swap_color_preserving r f (color ∘ lab) hcol
    change color (lab (r (Sum.inl a))) = color (lab (r (Sum.inr b)))
    rw [hr,hr]
    exact hc
  have hsame : ∀ z, z ∉ bd → g z = f z := by
    intro z hz
    apply hleft.swap_outside hright z
    simpa only [bd,ha,hb,List.map_cons] using hz
  let C : FullFilling flip color face (w++w') := {
    Dart := D.Dart ⊕ D'.Dart
    reverse := r
    next := g
    reverse_involutive := by
      intro z
      cases z with
      | inl x => exact congrArg Sum.inl (D.reverse_involutive x)
      | inr x => exact congrArg Sum.inr (D'.reverse_involutive x)
    reverse_ne := by
      intro z he
      cases z with
      | inl x => exact D.reverse_ne x (Sum.inl.inj he)
      | inr x => exact D'.reverse_ne x (Sum.inr.inj he)
    label := lab
    reverse_label := hr
    color_next := hcg
    planar := (D.planar.sum D'.planar).join_right hsep
    boundary := bd
    boundary_cycle := hbd
    boundary_word := by
      simp only [bd,List.map_append,List.map_map]
      change D.boundary.map D.label ++ D'.boundary.map D'.label = w++w'
      rw [D.boundary_word,D'.boundary_word]
    cells := by
      intro z hn
      have hpow (n : ℕ) : (g^n) z = (f^n) z := by
        symm
        apply same_outside_boundary_pow hbd
        · intro z hz; exact (hsame z hz).symm
        · exact hn
      cases z with
      | inl x =>
        have hxn : x ∉ D.boundary := by
          intro hx; apply hn; exact List.mem_append_left _ (List.mem_map.mpr ⟨x,hx,rfl⟩)
        have he (n : ℕ) : (f^n) (Sum.inl x) = Sum.inl ((D.next^n) x) :=
          (pow_intertwine D.next f Sum.inl (fun _ => rfl) n x).symm
        rcases D.cells x hxn with ht | hb
        · refine Or.inl ⟨?_,?_,?_⟩
          · rw [hpow 3,he 3,ht.1]
          · rw [hsame _ hn]; intro hh; exact ht.2.1 (Sum.inl.inj hh)
          · rw [hsame _ hn,hpow 2,he 2]
            exact ht.2.2
        · refine Or.inr ⟨?_,?_⟩
          · rw [hsame _ hn]; exact congrArg Sum.inl hb.1
          · rw [hpow 2,he 2,hb.2]
      | inr x =>
        have hxn : x ∉ D'.boundary := by
          intro hx; apply hn; exact List.mem_append_right _ (List.mem_map.mpr ⟨x,hx,rfl⟩)
        have he (n : ℕ) : (f^n) (Sum.inr x) = Sum.inr ((D'.next^n) x) :=
          (pow_intertwine D'.next f Sum.inr (fun _ => rfl) n x).symm
        rcases D'.cells x hxn with ht | hb
        · refine Or.inl ⟨?_,?_,?_⟩
          · rw [hpow 3,he 3,ht.1]
          · rw [hsame _ hn]; intro hh; exact ht.2.1 (Sum.inr.inj hh)
          · rw [hsame _ hn,hpow 2,he 2]
            exact ht.2.2
        · refine Or.inr ⟨?_,?_⟩
          · rw [hsame _ hn]; exact congrArg Sum.inr hb.1
          · rw [hpow 2,he 2,hb.2] }
  refine ⟨C,?_⟩
  unfold trace
  rw [Fintype.sum_sum_type]
  apply congrArg₂ (·+·)
  · apply Finset.sum_congr rfl
    intro x _
    have hx : Sum.inl x ∈ bd ↔ x ∈ D.boundary := by
      simp only [bd,List.mem_append,List.mem_map,Sum.inl.injEq]
      simp only [Sum.inr_ne_inl,exists_false,and_false,or_false,exists_eq_right]
    by_cases hxb : x ∈ D.boundary
    · simp only [C,hx,hxb,ite_true]
    have hn := not_congr hx |>.mpr hxb
    have hpow (n : ℕ) : (g^n) (Sum.inl x) = Sum.inl ((D.next^n) x) := by
      exact (same_outside_boundary_pow hbd (fun z hz => (hsame z hz).symm) hn n).symm.trans
        (pow_intertwine D.next f Sum.inl (fun _ => rfl) n x).symm
    simp only [C,hx,hxb,ite_false,hpow 2,hsame _ hn]
    rfl
  · apply Finset.sum_congr rfl
    intro x _
    have hx : Sum.inr x ∈ bd ↔ x ∈ D'.boundary := by
      simp only [bd,List.mem_append,List.mem_map,Sum.inr.injEq]
      simp only [Sum.inl_ne_inr,exists_false,and_false,false_or,exists_eq_right]
    by_cases hxb : x ∈ D'.boundary
    · simp only [C,hx,hxb,ite_true]
    have hn := not_congr hx |>.mpr hxb
    have hpow (n : ℕ) : (g^n) (Sum.inr x) = Sum.inr ((D'.next^n) x) := by
      exact (same_outside_boundary_pow hbd (fun z hz => (hsame z hz).symm) hn n).symm.trans
        (pow_intertwine D'.next f Sum.inr (fun _ => rfl) n x).symm
    simp only [C,hx,hxb,ite_false,hpow 2,hsame _ hn]
    rfl

end Release075.FullFilling

namespace Release075.FullFilling
attribute [local instance] Classical.propDecidable Classical.decEq
variable {E V M : Type} [AddCommGroup M]
variable {flip : E → E} {color : E → V} {face : E → E → E → Prop}

noncomputable abbrev reword {w w' : List E} (D : FullFilling flip color face w)
    (h : w = w') : FullFilling flip color face w' := h ▸ D

theorem trace_reword {w w' : List E} (D : FullFilling flip color face w)
    (h : w = w') (F : E → E → E → M) : (D.reword h).trace F = D.trace F := by
  subst w'; rfl

theorem rotateAppend {u v : List E} (D : FullFilling flip color face (u++v))
    (F : E → E → E → M) :
    ∃ D' : FullFilling flip color face (v++u), D'.trace F = D.trace F := by
  refine ⟨(D.rotate u.length).reword (List.rotate_append_length_eq u v),?_⟩
  rw [trace_reword,trace_rotate]

theorem foldHead (hi : Function.Involutive flip) (hn : ∀ e, color e ≠ color (flip e))
    {e : E} {w : List E} (D : FullFilling flip color face (e::flip e::w))
    (F : E → E → E → M) (hdeg : ∀ a b, F a b a = 0) :
    ∃ D' : FullFilling flip color face w, D'.trace F = D.trace F := by
  obtain ⟨b,bs,hb,he,hbs⟩ := List.map_eq_cons_iff.mp D.boundary_word
  obtain ⟨a,l,ha,hae,hl⟩ := List.map_eq_cons_iff.mp hbs
  have hbound : D.boundary = b::a::l := by rw [hb,ha]
  have hab : D.label a = flip (D.label b) := by rw [he,hae]
  obtain ⟨D',ht⟩ := D.fold hi hn hbound hab F hdeg
  exact ⟨D'.reword hl,(trace_reword D' hl F).trans ht⟩

theorem erase (hi : Function.Involutive flip) (hn : ∀ e, color e ≠ color (flip e))
    (u v : List E) (e : E) (D : FullFilling flip color face (u++e::flip e::v))
    (F : E → E → E → M) (hdeg : ∀ a b, F a b a = 0) :
    ∃ D' : FullFilling flip color face (u++v), D'.trace F = D.trace F := by
  obtain ⟨D₁,h₁⟩ := D.rotateAppend F
  change FullFilling flip color face (e::flip e::(v++u)) at D₁
  obtain ⟨D₂,h₂⟩ := D₁.foldHead hi hn F hdeg
  obtain ⟨D₃,h₃⟩ := D₂.rotateAppend (u := v) (v := u) F
  exact ⟨D₃,h₃.trans (h₂.trans h₁)⟩

theorem erase_reverse (hi : Function.Involutive flip) (hn : ∀ e, color e ≠ color (flip e))
    (u v p : List E) (D : FullFilling flip color face (u ++ reverseWord flip p ++ p ++ v))
    (F : E → E → E → M) (hdeg : ∀ a b, F a b a = 0) :
    ∃ D' : FullFilling flip color face (u++v), D'.trace F = D.trace F := by
  induction p generalizing u with
  | nil =>
    have he : u ++ reverseWord flip [] ++ [] ++ v = u++v := by
      simp only [reverseWord_nil,List.append_nil]
    exact ⟨D.reword he,trace_reword D he F⟩
  | cons e p ih =>
    have he : u ++ reverseWord flip (e::p) ++ (e::p) ++ v =
        (u++reverseWord flip p) ++ flip e :: flip (flip e) :: (p++v) := by
      simp only [reverseWord_cons,List.append_assoc,List.nil_append,List.cons_append,hi e]
    obtain ⟨D₁,h₁⟩ := (D.reword he).erase hi hn (u++reverseWord flip p) (p++v) (flip e) F hdeg
    have he' : (u++reverseWord flip p) ++ (p++v) =
        u ++ reverseWord flip p ++ p ++ v := by simp only [List.append_assoc]
    obtain ⟨D₂,h₂⟩ := ih u (D₁.reword he')
    exact ⟨D₂,h₂.trans ((trace_reword D₁ he' F).trans (h₁.trans (trace_reword D he F)))⟩

theorem trace_palindrome
    (hempty : ∀ D : TriangleSphere flip color face, IsEmpty D.Dipole → IsEmpty D.Dart)
    (hi : Function.Involutive flip) (hn : ∀ e, color e ≠ color (flip e))
    (F : E → E → E → M)
    (hrot : ∀ a b c, face a b c → F b c a = F a b c)
    (hmir : ∀ a b c, face a b c → F (flip a) (flip c) (flip b) = -F a b c)
    (hdeg : ∀ a b, F a b a = 0)
    (w : List E) (D : FullFilling flip color face (reverseWord flip w ++ w)) :
    D.trace F = 0 := by
  have he : reverseWord flip w ++ w = [] ++ reverseWord flip w ++ w ++ [] := by
    simp only [List.nil_append,List.append_nil]
  obtain ⟨D',h⟩ := (D.reword he).erase_reverse hi hn [] [] w F hdeg
  rw [trace_reword] at h
  exact h.symm.trans (D'.trace_empty hempty F hrot hmir hdeg)

/-- The signed triangle chain of a full disk depends only on its typed boundary.
This is proved by actual exterior folds, retaining detached components. -/
theorem trace_unique
    (hempty : ∀ D : TriangleSphere flip color face, IsEmpty D.Dipole → IsEmpty D.Dart)
    (hi : Function.Involutive flip) (hn : ∀ e, color e ≠ color (flip e))
    (hf : ∀ a b c, face a b c → face (flip a) (flip c) (flip b))
    (F : E → E → E → M)
    (hrot : ∀ a b c, face a b c → F b c a = F a b c)
    (hmir : ∀ a b c, face a b c → F (flip a) (flip c) (flip b) = -F a b c)
    (hdeg : ∀ a b, F a b a = 0)
    {x : V} {w : List E} (hw : WordPath flip color x x w)
    (D D' : FullFilling flip color face w) : D.trace F = D'.trace F := by
  cases w with
  | nil => rw [trace_empty hempty F hrot hmir hdeg,trace_empty hempty F hrot hmir hdeg]
  | cons e es =>
    let B := D.mirror hi hf
    have hne : reverseWord flip (e::es) ≠ [] := by
      simp only [reverseWord,List.map_eq_nil_iff,List.reverse_eq_nil_iff,
        ne_eq,List.cons_ne_nil,not_false_eq_true]
    obtain ⟨f,fs,he⟩ := List.exists_cons_of_ne_nil hne
    obtain ⟨a,l,ha,hal,_⟩ := List.map_eq_cons_iff.mp (B.boundary_word.trans he)
    obtain ⟨b,l',hb,hbl,_⟩ := List.map_eq_cons_iff.mp D'.boundary_word
    have hrev := hw.reverse hi
    rw [he] at hrev
    obtain ⟨C,hC⟩ := B.wedge D' ha hb (by rw [hal,hbl]; exact hrev.source.trans hw.source.symm) F
    have hzero := C.trace_palindrome hempty hi hn F hrot hmir hdeg (e::es)
    have hz : B.trace F + D'.trace F = 0 := hC.symm.trans hzero
    have hm : B.trace F = -D.trace F := D.trace_mirror hi hf F hmir hdeg
    rw [hm] at hz
    exact neg_add_eq_zero.mp hz

end Release075.FullFilling

namespace Release075.FullFilling
open Equiv
attribute [local instance] Classical.propDecidable Classical.decEq
variable {E V M : Type} [AddCommGroup M]
variable {flip : E → E} {color : E → V} {face : E → E → E → Prop}

/-- Cyclic reindexing of corners of genuine triangles. -/
theorem trace_cyclic {w : List E} (D : FullFilling flip color face w)
    (ht : ∀ a, a ∉ D.boundary → (D.next^3) a = a)
    (F : E → E → E → M) : D.trace (fun a b c => F b c a) = D.trace F := by
  let f : D.Dart → M := fun a => if a ∈ D.boundary then 0 else
    F (D.label a) (D.label (D.next a)) (D.label ((D.next^2) a))
  have hsum := Equiv.sum_comp D.next f
  rw [trace]
  change _ = ∑ a, f a
  rw [← hsum]
  apply Finset.sum_congr rfl
  intro a _
  have hm := D.boundary_cycle.mem_iff a
  by_cases ha : a ∈ D.boundary
  · simp only [f,ha,hm,ite_true]
  · have h3 : (D.next^2) (D.next a) = a := by
      simpa only [pow_succ,Perm.mul_apply] using ht a ha
    simp only [f,ha,hm,ite_false,h3]
    rw [pow_two,Perm.mul_apply]

theorem trace_add {w : List E} (D : FullFilling flip color face w)
    (F H : E → E → E → M) : D.trace (fun a b c => F a b c + H a b c) = D.trace F + D.trace H := by
  unfold trace
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a _
  split_ifs <;> simp only [add_zero]

theorem trace_cyclic_sum {w : List E} (D : FullFilling flip color face w)
    (ht : ∀ a, a ∉ D.boundary → (D.next^3) a = a)
    (F : E → E → E → M) :
    D.trace (fun a b c => F a b c + F b c a + F c a b) = 3 • D.trace F := by
  rw [trace_add,trace_add,trace_cyclic D ht F]
  have hh : D.trace (fun a b c => F c a b) = D.trace F :=
    (D.trace_cyclic ht (fun a b c => F b c a)).trans (D.trace_cyclic ht F)
  rw [hh]
  simp only [succ_nsmul,zero_nsmul,zero_add]

end Release075.FullFilling

namespace Release075.FullFilling
attribute [local instance] Classical.propDecidable Classical.decEq
variable {E V M N : Type} [AddCommGroup M] [AddCommGroup N]
variable {flip : E → E} {color : E → V} {face : E → E → E → Prop}

theorem trace_map {w : List E} (D : FullFilling flip color face w)
    (F : E → E → E → M) (f : M →+ N) :
    f (D.trace F) = D.trace (fun a b c => f (F a b c)) := by
  unfold trace
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro a _
  split_ifs <;> simp only [map_zero]

theorem trace_congr {w : List E} (D : FullFilling flip color face w)
    {F H : E → E → E → M}
    (h : ∀ a, a ∉ D.boundary →
      F (D.label a) (D.label (D.next a)) (D.label ((D.next^2) a)) =
      H (D.label a) (D.label (D.next a)) (D.label ((D.next^2) a))) : D.trace F = D.trace H := by
  unfold trace
  apply Finset.sum_congr rfl
  intro a _
  split_ifs with ha
  · rfl
  · exact h a ha

/-- Integral Stokes accounting for an antisymmetric edge evaluation. -/
theorem trace_edge {w : List E} (D : FullFilling flip color face w)
    (F : E → M) (hf : ∀ e, F (flip e) = -F e) :
    D.trace (fun a _ _ => F a) = -(w.map F).sum := by
  let f : D.Dart → M := F ∘ D.label
  have hz : ∑ a, f a = 0 := by
    apply Finset.sum_involution (fun a _ => D.reverse a)
    · intro a _
      simp only [f,Function.comp_apply,D.reverse_label,hf,add_neg_cancel]
    · intro a _ _; exact D.reverse_ne a
    · intro a _; exact Finset.mem_univ _
    · intro a _; exact D.reverse_involutive a
  have hb : (∑ a, if a ∈ D.boundary then f a else 0) = (w.map F).sum := by
    rw [← Finset.sum_filter]
    have he : Finset.univ.filter (fun a => a ∈ D.boundary) = D.boundary.toFinset := by ext; simp
    rw [he,List.sum_toFinset _ D.boundary_cycle.1]
    change (D.boundary.map (F ∘ D.label)).sum = _
    rw [← List.map_map,D.boundary_word]
  have hpart : (∑ a, if a ∈ D.boundary then f a else 0) +
      D.trace (fun a _ _ => F a) = ∑ a, f a := by
    rw [trace,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro a _
    split_ifs <;> simp only [add_zero,zero_add,f,Function.comp_apply]
  rw [hb,hz] at hpart
  apply eq_neg_iff_add_eq_zero.mpr
  rw [add_comm]
  exact hpart

end Release075.FullFilling

namespace Release075.TriangleFilling
attribute [local instance] Classical.propDecidable Classical.decEq
variable {E V : Type} {flip : E → E} {color : E → V} {face : E → E → E → Prop}

theorem full_triangular {w : List E} (D : TriangleFilling flip color face w)
    (a : D.full.Dart) (ha : a ∉ D.full.boundary) :
    (D.full.next^3) a = a ∧ D.full.next a ≠ a ∧
      face (D.full.label a) (D.full.label (D.full.next a)) (D.full.label ((D.full.next^2) a)) := by
  have hn : a.val ∉ D.boundary := by
    intro h
    apply ha
    exact List.mem_pmap.mpr ⟨a.val,h,rfl⟩
  have ht := D.triangular a.val a.property hn
  exact ⟨Subtype.ext ht.1,fun he => ht.2.1 (congrArg Subtype.val he),ht.2.2⟩

end Release075.TriangleFilling

end OAI
end
end

section
section
namespace OAI

namespace Release075

/-- The free integral module on copies of the regular left group action. -/
abbrev FreeChain (A G : Type) := (A × G) →₀ ℤ

noncomputable def chainShift {A G : Type} [Group G] (g : G) :
    FreeChain A G ≃ₗ[ℤ] FreeChain A G :=
  Finsupp.domLCongr (Equiv.prodCongr (Equiv.refl A) (Equiv.mulLeft g))

@[simp] theorem chainShift_single {A G : Type} [Group G] (g : G) (a : A) (h : G) (n : ℤ) :
    chainShift g (Finsupp.single (a,h) n) = Finsupp.single (a,g*h) n :=
  Finsupp.domLCongr_single _ _ _

namespace BlockPresentation
attribute [local instance] Classical.propDecidable Classical.decEq
variable {I B : Type} {r : ℕ} (d : BlockPresentation I B r)

abbrev C₀ := FreeChain d.Vertex d.GroupType
abbrev C₁ := FreeChain d.Edge d.GroupType

def PositiveFace (t : d.OrientedEdge × d.OrientedEdge × d.OrientedEdge) : Prop :=
  d.TriangleFace t.1 t.2.1 t.2.2 ∧ d.edgeTarget t.1 = .v ∧
    d.edgeTarget t.2.1 = .w ∧ d.edgeTarget t.2.2 = .o

abbrev FaceBase := {t : d.OrientedEdge × d.OrientedEdge × d.OrientedEdge // d.PositiveFace t}
abbrev C₂ := FreeChain d.FaceBase d.GroupType

/-- An oriented edge is represented in a free module on the positive orientations. -/
noncomputable def edgeChain (e : d.LiftedEdge) : d.C₁ :=
  if e.1.2 then Finsupp.single (e.1.1,e.2) 1 else
    -Finsupp.single (e.1.1,(d.liftedFlip e).2) 1

@[simp] theorem edgeChain_flip (e : d.LiftedEdge) :
    d.edgeChain (d.liftedFlip e) = -d.edgeChain e := by
  rcases e with ⟨⟨e,s⟩,g⟩
  cases s <;> simp [edgeChain,liftedFlip,flipEdge,edgeValue]

noncomputable def boundary₁ : d.C₁ →ₗ[ℤ] d.C₀ :=
  Finsupp.linearCombination ℤ (fun e =>
    Finsupp.single (d.edgeTarget (e.1,true), e.2) 1 -
      Finsupp.single (d.edgeTarget (d.flipEdge (e.1,true)),e.2*(d.edge (e.1))⁻¹) 1)

theorem boundary₁_edgeChain (e : d.LiftedEdge) :
    d.boundary₁ (d.edgeChain e) = Finsupp.single (d.liftedTarget e) 1 -
      Finsupp.single (d.liftedTarget (d.liftedFlip e)) 1 := by
  rcases e with ⟨⟨e,s⟩,g⟩
  cases s <;> simp [edgeChain,boundary₁,liftedFlip,liftedTarget,flipEdge,edgeValue]

noncomputable def boundary₂ : d.C₂ →ₗ[ℤ] d.C₁ :=
  Finsupp.linearCombination ℤ (fun t =>
    d.edgeChain (t.1.val.1,t.2*d.edgeValue t.1.val.1) +
      d.edgeChain (t.1.val.2.1,t.2*d.edgeValue t.1.val.1*d.edgeValue t.1.val.2.1) +
        d.edgeChain (t.1.val.2.2,t.2))

theorem boundary₁_boundary₂ (c : d.C₂) : d.boundary₁ (d.boundary₂ c) = 0 := by
  have he : d.boundary₁.comp d.boundary₂ = 0 := by
    apply Finsupp.lhom_ext
    intro t n
    obtain ⟨t,g⟩ := t
    have h := TriangleFace.lift d t.property.1 g
    simp only [LinearMap.comp_apply,boundary₂,Finsupp.linearCombination_single,map_smul,
      map_add,boundary₁_edgeChain,LinearMap.zero_apply]
    rw [h.2.1,h.2.2.1,h.2.2.2]
    have hz :
        (Finsupp.single (d.liftedTarget (t.val.1,g*d.edgeValue t.val.1)) 1 -
          Finsupp.single (d.liftedTarget (t.val.2.2,g)) 1) +
        (Finsupp.single (d.liftedTarget (t.val.2.1,g*d.edgeValue t.val.1*d.edgeValue t.val.2.1)) 1 -
          Finsupp.single (d.liftedTarget (t.val.1,g*d.edgeValue t.val.1)) 1) +
        (Finsupp.single (d.liftedTarget (t.val.2.2,g)) 1 -
          Finsupp.single (d.liftedTarget (t.val.2.1,g*d.edgeValue t.val.1*d.edgeValue t.val.2.1)) 1) = (0 : d.C₀) := by abel
    rw [hz,smul_zero]
  exact LinearMap.congr_fun he c

/-- The positively oriented, O-based atom. Nonfaces give zero. -/
noncomputable def positiveAtom (a b c : d.LiftedEdge) : d.C₂ :=
  if h : d.PositiveFace (a.1,b.1,c.1) then Finsupp.single (⟨(a.1,b.1,c.1),h⟩,c.2) 1 else 0

/-- Exactly one O-corner, with its orientation sign. -/
noncomputable def orderedEval (a b c : d.LiftedEdge) : d.C₂ :=
  d.positiveAtom a b c - d.positiveAtom (d.liftedFlip c) (d.liftedFlip b) (d.liftedFlip a)

/-- Cyclic evaluation of one oriented face. -/
noncomputable def faceEval (a b c : d.LiftedEdge) : d.C₂ :=
  d.orderedEval a b c + d.orderedEval b c a + d.orderedEval c a b

theorem faceEval_rotate (a b c : d.LiftedEdge) : d.faceEval b c a = d.faceEval a b c := by
  unfold faceEval
  abel

theorem orderedEval_mirror (a b c : d.LiftedEdge) :
    d.orderedEval (d.liftedFlip a) (d.liftedFlip c) (d.liftedFlip b) = - d.orderedEval b c a := by
  simp only [orderedEval,liftedFlip_flip]
  abel

theorem faceEval_mirror (a b c : d.LiftedEdge) :
    d.faceEval (d.liftedFlip a) (d.liftedFlip c) (d.liftedFlip b) = -d.faceEval a b c := by
  simp only [faceEval,orderedEval_mirror]
  abel

theorem positiveAtom_eq_zero {a b c : d.LiftedEdge}
    (h : ¬d.TriangleFace a.1 b.1 c.1) : d.positiveAtom a b c = 0 := by
  simp only [positiveAtom]
  split_ifs with hh
  · exact False.elim (h hh.1)
  · rfl

theorem positiveAtom_degenerate (a b : d.LiftedEdge) :
    d.positiveAtom a b a = 0 ∧ d.positiveAtom a a b = 0 ∧ d.positiveAtom b a a = 0 := by
  refine ⟨d.positiveAtom_eq_zero ?_,d.positiveAtom_eq_zero ?_,d.positiveAtom_eq_zero ?_⟩
  · intro h; exact (TriangleFace.colors d h).2.2 rfl
  · intro h; exact (TriangleFace.colors d h).1 rfl
  · intro h; exact (TriangleFace.colors d h).2.1 rfl

theorem faceEval_degenerate (a b : d.LiftedEdge) : d.faceEval a b a = 0 := by
  obtain ⟨ha,hb,hc⟩ := d.positiveAtom_degenerate a b
  obtain ⟨ha',hb',hc'⟩ := d.positiveAtom_degenerate (d.liftedFlip a) (d.liftedFlip b)
  simp only [faceEval,orderedEval,ha,hb,hc,ha',hb',hc',sub_self,add_zero]

end BlockPresentation
end Release075

namespace Release075.BlockPresentation
attribute [local instance] Classical.propDecidable Classical.decEq
variable {I B : Type} {r : ℕ} (d : BlockPresentation I B r)

theorem positiveAtom_zero_first {a b c : d.LiftedEdge} (h : d.edgeTarget a.1 ≠ .v) :
    d.positiveAtom a b c = 0 := by
  unfold positiveAtom
  split_ifs with hh
  · exact False.elim (h hh.2.1)
  · rfl

theorem positiveAtom_zero_second {a b c : d.LiftedEdge} (h : d.edgeTarget b.1 ≠ .w) :
    d.positiveAtom a b c = 0 := by
  unfold positiveAtom
  split_ifs with hh
  · exact False.elim (h hh.2.2.1)
  · rfl

theorem faceEval_positive {a b c : d.LiftedEdge} (h : d.LiftedFace a b c)
    (hp : d.PositiveFace (a.1,b.1,c.1)) : d.faceEval a b c = d.positiveAtom a b c := by
  have hva : d.edgeTarget (d.liftedFlip a).1 = .o :=
    (congrArg Prod.fst h.2.2.2).trans hp.2.2.2
  have hvc : d.edgeTarget (d.liftedFlip c).1 = .w :=
    (congrArg Prod.fst h.2.2.1).trans hp.2.2.1
  have hb := d.positiveAtom_zero_first (a := b) (b := c) (c := a) (by rw [hp.2.2.1]; intro he; cases he)
  have hc := d.positiveAtom_zero_first (a := c) (b := a) (c := b) (by rw [hp.2.2.2]; intro he; cases he)
  have h₁ := d.positiveAtom_zero_first (a := d.liftedFlip c) (b := d.liftedFlip b)
    (c := d.liftedFlip a) (by rw [hvc]; intro he; cases he)
  have h₂ := d.positiveAtom_zero_first (a := d.liftedFlip a) (b := d.liftedFlip c)
    (c := d.liftedFlip b) (by rw [hva]; intro he; cases he)
  have h₃ := d.positiveAtom_zero_second (a := d.liftedFlip b) (b := d.liftedFlip a)
    (c := d.liftedFlip c) (by rw [hva]; intro he; cases he)
  simp only [faceEval,orderedEval,hb,hc,h₁,h₂,h₃,sub_zero,add_zero]

theorem boundary₂_positiveAtom {a b c : d.LiftedEdge} (h : d.LiftedFace a b c)
    (hp : d.PositiveFace (a.1,b.1,c.1)) :
    d.boundary₂ (d.positiveAtom a b c) = d.edgeChain a + d.edgeChain b + d.edgeChain c := by
  have ha : a.2 = c.2*d.edgeValue a.1 :=
    mul_inv_eq_iff_eq_mul.mp (congrArg Prod.snd h.2.2.2)
  have hb : b.2 = a.2*d.edgeValue b.1 :=
    mul_inv_eq_iff_eq_mul.mp (congrArg Prod.snd h.2.1)
  simp only [positiveAtom,dite_eq_left hp,boundary₂,Finsupp.linearCombination_single,one_smul]
  rw [← ha,← hb]

theorem TriangleFace.positive_orient {a b c : d.OrientedEdge} (h : d.TriangleFace a b c) :
    d.PositiveFace (a,b,c) ∨ d.PositiveFace (b,c,a) ∨ d.PositiveFace (c,a,b) ∨
    d.PositiveFace (d.flipEdge a,d.flipEdge c,d.flipEdge b) ∨
    d.PositiveFace (d.flipEdge b,d.flipEdge a,d.flipEdge c) ∨
    d.PositiveFace (d.flipEdge c,d.flipEdge b,d.flipEdge a) := by
  have hp (b : B) (i : (d.block b).labels) (u v : Fin r) :
      d.PositiveFace (d.orientedL b i u v,d.orientedX i u v,d.flipEdge (d.orientedR b i u v)) := by
    refine ⟨TriangleFace.pos₀ _ _ _ _,?_,?_,?_⟩ <;> rfl
  cases h with
  | pos₀ b i u v => exact Or.inl (hp _ _ _ _)
  | pos₁ b i u v => exact Or.inr (Or.inr (Or.inl (hp _ _ _ _)))
  | pos₂ b i u v => exact Or.inr (Or.inl (hp _ _ _ _))
  | neg₀ b i u v =>
    exact Or.inr (Or.inr (Or.inr (Or.inl (by simpa only [flipEdge_flipEdge] using hp b i u v))))
  | neg₁ b i u v =>
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by simpa only [flipEdge_flipEdge] using hp b i u v)))))
  | neg₂ b i u v =>
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by simpa only [flipEdge_flipEdge] using hp b i u v)))))

theorem boundary₂_faceEval {a b c : d.LiftedEdge} (h : d.LiftedFace a b c) :
    d.boundary₂ (d.faceEval a b c) = d.edgeChain a + d.edgeChain b + d.edgeChain c := by
  have pos {a b c : d.LiftedEdge} (h : d.LiftedFace a b c)
      (hp : d.PositiveFace (a.1,b.1,c.1)) :
      d.boundary₂ (d.faceEval a b c) = d.edgeChain a + d.edgeChain b + d.edgeChain c := by
    rw [d.faceEval_positive h hp]
    exact d.boundary₂_positiveAtom h hp
  have circ {a b c : d.LiftedEdge}
      (hp : d.boundary₂ (d.faceEval b c a) = d.edgeChain b + d.edgeChain c + d.edgeChain a) :
      d.boundary₂ (d.faceEval a b c) = d.edgeChain a + d.edgeChain b + d.edgeChain c := by
    rw [faceEval_rotate] at hp
    rw [hp]
    abel
  have mir {a b c : d.LiftedEdge}
      (hp : d.boundary₂ (d.faceEval (d.liftedFlip a) (d.liftedFlip c) (d.liftedFlip b)) =
        d.edgeChain (d.liftedFlip a) + d.edgeChain (d.liftedFlip c) + d.edgeChain (d.liftedFlip b)) :
      d.boundary₂ (d.faceEval a b c) = d.edgeChain a + d.edgeChain b + d.edgeChain c := by
    rw [faceEval_mirror,map_neg,edgeChain_flip,edgeChain_flip,edgeChain_flip] at hp
    apply neg_injective
    rw [hp]
    abel
  rcases TriangleFace.positive_orient d h.1 with hp | hp | hp | hp | hp | hp
  · exact pos h hp
  · exact circ (pos (h.rotate d) hp)
  · exact circ (circ (pos ((h.rotate d).rotate d) hp))
  · exact mir (pos (h.mirror d) hp)
  · exact circ (mir (pos ((h.rotate d).mirror d) hp))
  · exact circ (circ (mir (pos (((h.rotate d).rotate d).mirror d) hp)))

end Release075.BlockPresentation

namespace Release075.BlockPresentation
attribute [local instance] Classical.propDecidable Classical.decEq
variable {I B : Type} {r : ℕ} (d : BlockPresentation I B r)

noncomputable def wordChain (w : List d.LiftedEdge) : d.C₁ := (w.map d.edgeChain).sum

noncomputable def diskChain {w : List d.LiftedEdge}
    (D : TriangleFilling d.liftedFlip d.liftedTarget d.LiftedFace w) : d.C₂ :=
  -D.full.trace d.orderedEval

theorem triple_diskChain {w : List d.LiftedEdge}
    (D : TriangleFilling d.liftedFlip d.liftedTarget d.LiftedFace w) :
    3 • d.diskChain D = -D.full.trace d.faceEval := by
  rw [diskChain,smul_neg]
  refine congrArg Neg.neg ?_
  exact (D.full.trace_cyclic_sum (fun a ha => (D.full_triangular a ha).1) d.orderedEval).symm

theorem boundary₂_diskChain {w : List d.LiftedEdge}
    (D : TriangleFilling d.liftedFlip d.liftedTarget d.LiftedFace w) :
    d.boundary₂ (d.diskChain D) = d.wordChain w := by
  apply nsmul_right_injective (by decide : 3 ≠ 0)
  change (3 : ℕ) • d.boundary₂ (d.diskChain D) = 3 • d.wordChain w
  rw [← map_nsmul,triple_diskChain,map_neg]
  change -d.boundary₂.toAddMonoidHom (D.full.trace d.faceEval) = _
  rw [D.full.trace_map d.faceEval d.boundary₂.toAddMonoidHom]
  have he : D.full.trace (fun a b c => d.boundary₂ (d.faceEval a b c)) =
      D.full.trace (fun a b c => d.edgeChain a + d.edgeChain b + d.edgeChain c) := by
    apply D.full.trace_congr
    intro a ha
    exact d.boundary₂_faceEval (D.full_triangular a ha).2.2
  change -D.full.trace (fun a b c => d.boundary₂ (d.faceEval a b c)) = _
  rw [he,D.full.trace_cyclic_sum (fun a ha => (D.full_triangular a ha).1)
    (fun a _ _ => d.edgeChain a),FullFilling.trace_edge _ d.edgeChain d.edgeChain_flip]
  simp only [smul_neg,neg_neg,wordChain]

end Release075.BlockPresentation

namespace Release075.MarkedLineData
variable {q r : ℕ} [Fact q.Prime] (d : MarkedLineData q r) (hr : 0 < r)

theorem diskChain_unique {w : List (d.presentation hr).LiftedEdge}
    {x : (d.presentation hr).LiftedVertex}
    (hw : WordPath (d.presentation hr).liftedFlip (d.presentation hr).liftedTarget x x w)
    (D D' : TriangleFilling (d.presentation hr).liftedFlip (d.presentation hr).liftedTarget
      (d.presentation hr).LiftedFace w) :
    (d.presentation hr).diskChain D = (d.presentation hr).diskChain D' := by
  let P := d.presentation hr
  apply nsmul_right_injective (by decide : 3 ≠ 0)
  change (3 : ℕ) • (d.presentation hr).diskChain D = 3 • (d.presentation hr).diskChain D'
  rw [BlockPresentation.triple_diskChain,BlockPresentation.triple_diskChain]
  apply congrArg Neg.neg
  exact FullFilling.trace_unique (d.lifted_sphere_empty_of_noDipole hr)
    P.liftedFlip_flip P.liftedTarget_ne (fun _ _ _ h => h.mirror P) P.faceEval
    (fun a b c _ => P.faceEval_rotate a b c) (fun a b c _ => P.faceEval_mirror a b c)
    P.faceEval_degenerate hw D.full D'.full

end Release075.MarkedLineData

end OAI
end
end

section
section
namespace OAI

namespace Release075
namespace FreeChain
attribute [local instance] Classical.propDecidable Classical.decEq
variable {A G : Type} [Group G]

@[simp] theorem shift_apply (g : G) (c : FreeChain A G) (a : A) (x : G) :
    chainShift g c (a,x) = c (a,g⁻¹*x) := by
  simp [chainShift,Finsupp.domLCongr_apply]

@[simp] theorem shift_one (c : FreeChain A G) : chainShift (1 : G) c = c := by
  ext ⟨a,x⟩; simp

@[simp] theorem shift_mul (g h : G) (c : FreeChain A G) :
    chainShift (g*h) c = chainShift g (chainShift h c) := by
  ext ⟨a,x⟩; simp [mul_assoc]

abbrev RightCosets (H : Subgroup G) := Quotient (QuotientGroup.rightRel H)

def coset (H : Subgroup G) (x : G) : RightCosets H := Quotient.mk _ x

noncomputable def cosetCoord (H : Subgroup G) (x : G) : H :=
  ⟨x * (coset H x).out⁻¹, QuotientGroup.rightRel_apply.mp
    (Quotient.exact (Quotient.out_eq (coset H x)))⟩

@[simp] theorem coset_mul (H : Subgroup G) (h : H) (x : G) :
    coset H ((h : G)*x) = coset H x := by
  apply Quotient.sound
  change QuotientGroup.rightRel H ((h:G)*x) x
  rw [QuotientGroup.rightRel_apply]
  simp [mul_inv_rev]

noncomputable def rightCosetEquiv (H : Subgroup G) : G ≃ RightCosets H × H where
  toFun x := (coset H x,cosetCoord H x)
  invFun q := q.2 * q.1.out
  left_inv x := by simp [cosetCoord]
  right_inv q := by
    rcases q with ⟨q,h⟩
    have hc : coset H ((h:G)*q.out) = q := by
      rw [coset_mul]; exact Quotient.out_eq q
    apply Prod.ext hc
    apply Subtype.ext
    simp only [cosetCoord, hc]
    simp

noncomputable def chainCosetEquiv (H : Subgroup G) :
    FreeChain A G ≃ₗ[ℤ] (A × RightCosets H) →₀ MonoidAlgebra ℤ H :=
  (Finsupp.domLCongr ((Equiv.prodCongr (Equiv.refl A) (rightCosetEquiv H)).trans
    (Equiv.prodAssoc A (RightCosets H) H).symm)).trans
    ((Finsupp.curryLinearEquiv ℤ).trans
      (Finsupp.mapRange.linearEquiv (MonoidAlgebra.coeffLinearEquiv ℤ).symm))

@[simp] theorem chainCosetEquiv_coeff (H : Subgroup G) (c : FreeChain A G)
    (a : A) (q : RightCosets H) (h : H) :
    ((chainCosetEquiv H c) (a,q)).coeff h = c (a,(h:G)*q.out) := by
  rfl

@[simp] theorem chainCosetEquiv_shift (H : Subgroup G) (h : H) (c : FreeChain A G)
    (i : A × RightCosets H) :
    chainCosetEquiv H (chainShift (h:G) c) i =
      Representation.leftRegular ℤ H h (chainCosetEquiv H c i) := by
  apply MonoidAlgebra.ext
  ext k
  rcases i with ⟨a,q⟩
  simp only [chainCosetEquiv_coeff,shift_apply,Representation.coeff_ofMulAction]
  simp [mul_assoc]

noncomputable def subgroupNorm (H : Subgroup G) [Fintype H] :
    FreeChain A G →ₗ[ℤ] FreeChain A G := ∑ h : H, (chainShift (h:G)).toLinearMap

@[simp] theorem chainCosetEquiv_norm (H : Subgroup G) [Fintype H] (c : FreeChain A G)
    (i : A × RightCosets H) :
    chainCosetEquiv H (subgroupNorm H c) i =
      (Representation.leftRegular ℤ H).norm (chainCosetEquiv H c i) := by
  simp only [subgroupNorm,LinearMap.sum_apply,map_sum,Representation.norm]
  rw [Finsupp.coe_finsetSum,Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro h _
  exact chainCosetEquiv_shift H h c i

end FreeChain
end Release075

namespace Release075
open CategoryTheory
attribute [local instance] Classical.propDecidable Classical.decEq

private theorem finsupp_preimages {J M N : Type} [AddCommGroup M] [AddCommGroup N]
    [Module ℤ M] [Module ℤ N] (f : M →ₗ[ℤ] N) (c : J →₀ N)
    (h : ∀ i, ∃ b, f b = c i) : ∃ b : J →₀ M, ∀ i, f (b i) = c i := by
  choose b hb using h
  let w : J →₀ M := Finsupp.onFinset c.support
    (fun i => if i ∈ c.support then b i else 0)
    (by intro i; split_ifs <;> simp_all)
  refine ⟨w,fun i => ?_⟩
  change f (if i ∈ c.support then b i else 0) = c i
  split_ifs with hi
  · exact hb i
  · simpa only [map_zero] using (Finsupp.notMem_support_iff.mp hi).symm

private theorem regular_invariant_norm {H : Type} [CommGroup H] [Fintype H]
    (g : H) (hg : ∀ x, x ∈ Subgroup.zpowers g) (c : MonoidAlgebra ℤ H)
    (hc : Representation.leftRegular ℤ H g c = c) :
    ∃ b, (Representation.leftRegular ℤ H).norm b = c := by
  have hm : c ∈ LinearMap.ker
      (Rep.applyAsHom (Rep.leftRegular ℤ H) g - 𝟙 _).hom.toLinearMap := by
    simpa [Rep.sub_hom,Rep.applyAsHom,sub_eq_zero] using hc
  rw [← Rep.FiniteCyclicGroup.leftRegular.range_norm_eq_ker_applyAsHom_sub ℤ g hg] at hm
  exact hm

private theorem regular_norm_zero {H : Type} [CommGroup H] [Fintype H]
    (g : H) (hg : ∀ x, x ∈ Subgroup.zpowers g) (c : MonoidAlgebra ℤ H)
    (hc : (Representation.leftRegular ℤ H).norm c = 0) :
    ∃ b, Representation.leftRegular ℤ H g b - b = c := by
  have hm : c ∈ LinearMap.ker (Rep.leftRegular ℤ H).norm.hom.toLinearMap := hc
  rw [← Rep.FiniteCyclicGroup.leftRegular.range_applyAsHom_sub_eq_ker_norm ℤ g hg] at hm
  obtain ⟨b,hb⟩ := hm
  exact ⟨b, by simpa [Rep.sub_hom,Rep.applyAsHom] using hb⟩

namespace FreeChain
variable {A G : Type} [Group G] (H : Subgroup G) [Fintype H] [IsCyclic H]
    (g : H) (hg : ∀ x, x ∈ Subgroup.zpowers g)

include hg in
theorem invariant_is_norm (c : FreeChain A G) (hc : chainShift (g:G) c = c) :
    ∃ b, subgroupNorm H b = c := by
  let : CommGroup H := IsCyclic.commGroup
  have hi (i : A × RightCosets H) : Representation.leftRegular ℤ H g
      (chainCosetEquiv H c i) = chainCosetEquiv H c i := by
    rw [← chainCosetEquiv_shift,hc]
  obtain ⟨b,hb⟩ := finsupp_preimages (Representation.leftRegular ℤ H).norm
    (chainCosetEquiv H c) (fun i => regular_invariant_norm g hg _ (hi i))
  refine ⟨(chainCosetEquiv H).symm b,?_⟩
  apply (chainCosetEquiv H).injective
  apply Finsupp.ext
  intro i
  rw [chainCosetEquiv_norm,LinearEquiv.apply_symm_apply,hb]

include hg in
theorem norm_zero_is_difference (c : FreeChain A G) (hc : subgroupNorm H c = 0) :
    ∃ b, chainShift (g:G) b - b = c := by
  let : CommGroup H := IsCyclic.commGroup
  have hi (i : A × RightCosets H) : (Representation.leftRegular ℤ H).norm
      (chainCosetEquiv H c i) = 0 := by
    rw [← chainCosetEquiv_norm,hc,map_zero,Finsupp.zero_apply]
  obtain ⟨b,hb⟩ := finsupp_preimages (Representation.leftRegular ℤ H g - LinearMap.id)
    (chainCosetEquiv H c) (fun i => regular_norm_zero g hg _ (hi i))
  refine ⟨(chainCosetEquiv H).symm b,?_⟩
  apply (chainCosetEquiv H).injective
  apply Finsupp.ext
  intro i
  rw [map_sub,Finsupp.sub_apply,chainCosetEquiv_shift,LinearEquiv.apply_symm_apply]
  exact hb i

end FreeChain
end Release075

namespace Release075.FreeChain
attribute [local instance] Classical.propDecidable Classical.decEq
variable {A B G : Type} [Group G]

noncomputable def augmentation : FreeChain A G →ₗ[ℤ] ℤ :=
  Finsupp.linearCombination ℤ (fun _ => (1:ℤ))

omit [Group G] in
@[simp] theorem augmentation_single (a : A) (x : G) (n : ℤ) :
    augmentation (Finsupp.single (a,x) n) = n := by
  simp [augmentation]

@[simp] theorem augmentation_shift (g : G) (c : FreeChain A G) :
    augmentation (chainShift g c) = augmentation c := by
  have he : (augmentation (A:=A)).comp (chainShift g).toLinearMap = augmentation := by
    apply Finsupp.lhom_ext
    intro ⟨a,x⟩ n
    simp [chainShift]
  exact LinearMap.congr_fun he c

theorem norm_map (H : Subgroup G) [Fintype H]
    (f : FreeChain A G →ₗ[ℤ] FreeChain B G)
    (hf : ∀ (h : H) c, f (chainShift (h:G) c) = chainShift (h:G) (f c))
    (c : FreeChain A G) : subgroupNorm H (f c) = f (subgroupNorm H c) := by
  simp only [subgroupNorm,LinearMap.sum_apply,map_sum,LinearEquiv.coe_coe]
  simp only [hf]

@[simp] theorem augmentation_norm (H : Subgroup G) [Fintype H] (c : FreeChain A G) :
    augmentation (subgroupNorm H c) = (Fintype.card H : ℤ) * augmentation c := by
  simp [subgroupNorm,LinearMap.sum_apply]

theorem cyclic_chain_obstruction {A₀ A₁ A₂ : Type} (H : Subgroup G)
    [Fintype H] [IsCyclic H] (g : H) (hg : ∀ x, x ∈ Subgroup.zpowers g)
    (b₁ : FreeChain A₁ G →ₗ[ℤ] FreeChain A₀ G)
    (b₂ : FreeChain A₂ G →ₗ[ℤ] FreeChain A₁ G)
    (h₁ : ∀ (h : H) c, b₁ (chainShift (h:G) c) = chainShift (h:G) (b₁ c))
    (h₂ : ∀ (h : H) c, b₂ (chainShift (h:G) c) = chainShift (h:G) (b₂ c))
    (hbb : ∀ c, b₁ (b₂ c) = 0)
    (haug : ∀ c, augmentation (b₁ c) = 0)
    (v : FreeChain A₀ G) (hv : augmentation v = 1)
    (c : FreeChain A₁ G) (hc : b₁ c = chainShift (g:G) v - v)
    (D : FreeChain A₂ G) (hD : b₂ D = subgroupNorm H c)
    (hDi : chainShift (g:G) D = D) : (g:G) = 1 := by
  obtain ⟨B,hB⟩ := invariant_is_norm H g hg D hDi
  have hz : subgroupNorm H (c - b₂ B) = 0 := by
    rw [map_sub,norm_map H b₂ h₂,hB,← hD,sub_self]
  obtain ⟨E,hE⟩ := norm_zero_is_difference H g hg (c-b₂ B) hz
  have hi : chainShift (g:G) (v - b₁ E) = v - b₁ E := by
    have he := congrArg b₁ hE
    rw [map_sub,h₁,map_sub,hbb,sub_zero,hc] at he
    rw [map_sub]
    rw [sub_eq_iff_eq_add.mp he]
    abel
  obtain ⟨w,hw⟩ := invariant_is_norm H g hg (v-b₁ E) hi
  have ha : (Fintype.card H : ℤ) * augmentation w = 1 := by
    rw [← augmentation_norm,hw,map_sub,hv,haug,sub_zero]
  have hcard : Fintype.card H = 1 := by
    have hd : (Fintype.card H : ℤ) ∣ 1 := ⟨augmentation w,ha.symm⟩
    have := Int.natCast_nonneg (Fintype.card H)
    have hpm := Int.eq_one_or_neg_one_of_mul_eq_one ha
    omega
  have : Subsingleton H := Fintype.card_le_one_iff_subsingleton.mp (hcard.le)
  exact congrArg (fun h : H => (h:G)) (Subsingleton.elim g 1)

end Release075.FreeChain

end OAI
end
end

section
section
namespace OAI

namespace Release075.BlockPresentation
attribute [local instance] Classical.propDecidable Classical.decEq
variable {I B : Type} {r : ℕ} (d : BlockPresentation I B r)

def shiftEdge (g : d.GroupType) (e : d.LiftedEdge) : d.LiftedEdge := (e.1,g*e.2)
def shiftVertex (g : d.GroupType) (x : d.LiftedVertex) : d.LiftedVertex := (x.1,g*x.2)

@[simp] theorem shiftEdge_one (e : d.LiftedEdge) : d.shiftEdge 1 e = e := by
  simp [shiftEdge]

@[simp] theorem shiftEdge_mul (g h : d.GroupType) (e : d.LiftedEdge) :
    d.shiftEdge (g*h) e = d.shiftEdge g (d.shiftEdge h e) := by
  simp only [shiftEdge,mul_assoc]

@[simp] theorem shiftEdge_flip (g : d.GroupType) (e : d.LiftedEdge) :
    d.shiftEdge g (d.liftedFlip e) = d.liftedFlip (d.shiftEdge g e) := by
  simp only [shiftEdge,liftedFlip,mul_assoc]

@[simp] theorem shiftEdge_target (g : d.GroupType) (e : d.LiftedEdge) :
    d.liftedTarget (d.shiftEdge g e) = d.shiftVertex g (d.liftedTarget e) := rfl

theorem LiftedFace.shift {a b c : d.LiftedEdge} (h : d.LiftedFace a b c) (g : d.GroupType) :
    d.LiftedFace (d.shiftEdge g a) (d.shiftEdge g b) (d.shiftEdge g c) := by
  refine ⟨h.1,?_,?_,?_⟩
  all_goals rw [← shiftEdge_flip,shiftEdge_target,shiftEdge_target]
  · exact congrArg (d.shiftVertex g) h.2.1
  · exact congrArg (d.shiftVertex g) h.2.2.1
  · exact congrArg (d.shiftVertex g) h.2.2.2

@[simp] theorem edgeChain_shift (g : d.GroupType) (e : d.LiftedEdge) :
    d.edgeChain (d.shiftEdge g e) = chainShift g (d.edgeChain e) := by
  unfold edgeChain
  change (if e.1.2 then _ else _) = _
  split_ifs <;> simp [shiftEdge,liftedFlip,chainShift_single,mul_assoc]

@[simp] theorem positiveAtom_shift (g : d.GroupType) (a b c : d.LiftedEdge) :
    d.positiveAtom (d.shiftEdge g a) (d.shiftEdge g b) (d.shiftEdge g c) =
      chainShift g (d.positiveAtom a b c) := by
  unfold positiveAtom
  change (if h : d.PositiveFace (a.1,b.1,c.1) then _ else _) = _
  split_ifs <;> simp [shiftEdge,chainShift_single]

@[simp] theorem orderedEval_shift (g : d.GroupType) (a b c : d.LiftedEdge) :
    d.orderedEval (d.shiftEdge g a) (d.shiftEdge g b) (d.shiftEdge g c) =
      chainShift g (d.orderedEval a b c) := by
  simp only [orderedEval,←shiftEdge_flip,positiveAtom_shift,map_sub]

@[simp] theorem faceEval_shift (g : d.GroupType) (a b c : d.LiftedEdge) :
    d.faceEval (d.shiftEdge g a) (d.shiftEdge g b) (d.shiftEdge g c) =
      chainShift g (d.faceEval a b c) := by
  simp only [faceEval,orderedEval_shift,map_add]

@[simp] theorem boundary₁_shift (g : d.GroupType) (c : d.C₁) :
    d.boundary₁ (chainShift g c) = chainShift g (d.boundary₁ c) := by
  have he : d.boundary₁.comp (chainShift g).toLinearMap =
      (chainShift g).toLinearMap.comp d.boundary₁ := by
    apply Finsupp.lhom_ext
    intro ⟨e,x⟩ n
    simp [boundary₁,chainShift_single,mul_assoc]
  exact LinearMap.congr_fun he c

@[simp] theorem boundary₂_shift (g : d.GroupType) (c : d.C₂) :
    d.boundary₂ (chainShift g c) = chainShift g (d.boundary₂ c) := by
  have he : d.boundary₂.comp (chainShift g).toLinearMap =
      (chainShift g).toLinearMap.comp d.boundary₂ := by
    apply Finsupp.lhom_ext
    intro ⟨t,x⟩ n
    simp only [LinearMap.comp_apply,LinearEquiv.coe_coe,chainShift_single,boundary₂,
      Finsupp.linearCombination_single,map_smul,map_add]
    simp only [← d.edgeChain_shift,shiftEdge,mul_assoc]
  exact LinearMap.congr_fun he c

@[simp] theorem augmentation_boundary₁ (c : d.C₁) :
    FreeChain.augmentation (d.boundary₁ c) = 0 := by
  have he : FreeChain.augmentation.comp d.boundary₁ = 0 := by
    apply Finsupp.lhom_ext
    intro ⟨e,x⟩ n
    simp [boundary₁]
  exact LinearMap.congr_fun he c

@[simp] theorem wordChain_append (u v : List d.LiftedEdge) :
    d.wordChain (u++v) = d.wordChain u + d.wordChain v := by
  simp [wordChain]

@[simp] theorem wordChain_shift (g : d.GroupType) (w : List d.LiftedEdge) :
    d.wordChain (w.map (d.shiftEdge g)) = chainShift g (d.wordChain w) := by
  simp only [wordChain,List.map_map,Function.comp_def,edgeChain_shift,map_list_sum]

end Release075.BlockPresentation

namespace Release075.FullFilling
attribute [local instance] Classical.propDecidable Classical.decEq
variable {I B : Type} {r : ℕ} {d : BlockPresentation I B r}
variable {w : List d.LiftedEdge} (D : FullFilling d.liftedFlip d.liftedTarget d.LiftedFace w)

def AllTriangles : Prop := ∀ a, a ∉ D.boundary → (D.next^3) a = a ∧ D.next a ≠ a ∧
  d.LiftedFace (D.label a) (D.label (D.next a)) (D.label ((D.next^2) a))

noncomputable def faceChain : d.C₂ := -D.trace d.orderedEval

theorem triple_faceChain (hD : D.AllTriangles) : 3 • D.faceChain = -D.trace d.faceEval := by
  rw [faceChain,smul_neg]
  refine congrArg Neg.neg ?_
  exact (D.trace_cyclic_sum (fun a ha => (hD a ha).1) d.orderedEval).symm

theorem boundary₂_faceChain (hD : D.AllTriangles) : d.boundary₂ D.faceChain = d.wordChain w := by
  apply nsmul_right_injective (by decide : 3 ≠ 0)
  change (3:ℕ) • d.boundary₂ D.faceChain = 3 • d.wordChain w
  rw [← map_nsmul,D.triple_faceChain hD,map_neg]
  change -d.boundary₂.toAddMonoidHom (D.trace d.faceEval) = _
  rw [D.trace_map d.faceEval d.boundary₂.toAddMonoidHom]
  have he : D.trace (fun a b c => d.boundary₂ (d.faceEval a b c)) =
      D.trace (fun a b c => d.edgeChain a + d.edgeChain b + d.edgeChain c) := by
    apply D.trace_congr
    intro a ha
    exact d.boundary₂_faceEval (hD a ha).2.2
  change -D.trace (fun a b c => d.boundary₂ (d.faceEval a b c)) = _
  rw [he,D.trace_cyclic_sum (fun a ha => (hD a ha).1) (fun a _ _ => d.edgeChain a),
    trace_edge _ d.edgeChain d.edgeChain_flip]
  simp only [smul_neg,neg_neg,BlockPresentation.wordChain]

noncomputable abbrev shift (g : d.GroupType) :
    FullFilling d.liftedFlip d.liftedTarget d.LiftedFace (w.map (d.shiftEdge g)) where
  Dart := D.Dart
  reverse := D.reverse
  next := D.next
  reverse_involutive := D.reverse_involutive
  reverse_ne := D.reverse_ne
  label a := d.shiftEdge g (D.label a)
  reverse_label a := by rw [D.reverse_label,d.shiftEdge_flip]
  color_next a := by simp only [d.shiftEdge_target,D.color_next]
  planar := D.planar
  boundary := D.boundary
  boundary_cycle := D.boundary_cycle
  boundary_word := by
    simpa only [List.map_map,Function.comp_def] using
      congrArg (List.map (d.shiftEdge g)) D.boundary_word
  cells := by
    intro a ha
    rcases D.cells a ha with ht | ht
    · exact Or.inl ⟨ht.1,ht.2.1,ht.2.2.shift d g⟩
    · exact Or.inr ht

theorem allTriangles_shift (hD : D.AllTriangles) (g : d.GroupType) : (D.shift g).AllTriangles :=
  fun a ha => ⟨(hD a ha).1,(hD a ha).2.1,(hD a ha).2.2.shift d g⟩

theorem allTriangles_rotate (hD : D.AllTriangles) (n : ℕ) : (D.rotate n).AllTriangles := by
  intro a ha
  exact hD a (by simpa only [List.mem_rotate] using ha)

@[simp] theorem faceChain_rotate (n : ℕ) : (D.rotate n).faceChain = D.faceChain := by
  rw [faceChain,trace_rotate,faceChain]

@[simp] theorem faceChain_shift (g : d.GroupType) :
    (D.shift g).faceChain = chainShift g D.faceChain := by
  unfold faceChain
  rw [map_neg]
  apply congrArg Neg.neg
  calc
    (D.shift g).trace d.orderedEval =
        D.trace (fun a b c => chainShift g (d.orderedEval a b c)) := by
      unfold trace
      apply Finset.sum_congr rfl
      intro a _
      split_ifs <;> simp only [BlockPresentation.orderedEval_shift]
    _ = chainShift g (D.trace d.orderedEval) :=
      (D.trace_map d.orderedEval (chainShift g).toAddMonoidHom).symm

end Release075.FullFilling

namespace Release075.MarkedLineData
variable {q r : ℕ} [Fact q.Prime] (d : MarkedLineData q r) (hr : 0 < r)

theorem fullChain_unique {w : List (d.presentation hr).LiftedEdge}
    {x : (d.presentation hr).LiftedVertex}
    (hw : WordPath (d.presentation hr).liftedFlip (d.presentation hr).liftedTarget x x w)
    (D D' : FullFilling (d.presentation hr).liftedFlip (d.presentation hr).liftedTarget
      (d.presentation hr).LiftedFace w) (ht : D.AllTriangles) (ht' : D'.AllTriangles) :
    D.faceChain = D'.faceChain := by
  let P := d.presentation hr
  apply nsmul_right_injective (by decide : 3 ≠ 0)
  change (3 : ℕ) • D.faceChain = 3 • D'.faceChain
  rw [D.triple_faceChain ht,D'.triple_faceChain ht']
  apply congrArg Neg.neg
  exact FullFilling.trace_unique (d.lifted_sphere_empty_of_noDipole hr)
    P.liftedFlip_flip P.liftedTarget_ne (fun _ _ _ h => h.mirror P) P.faceEval
    (fun a b c _ => P.faceEval_rotate a b c) (fun a b c _ => P.faceEval_mirror a b c)
    P.faceEval_degenerate hw D D'

end Release075.MarkedLineData

end OAI
end
end

section
section
namespace OAI

namespace Release075.BlockPresentation
open CategoryTheory
variable {I B : Type} {r : ℕ} (d : BlockPresentation I B r)

def basePath : (a : d.Vertex) → (d.vertex .o ⟶ d.vertex a)
  | .o => 𝟙 _
  | .v => d.treePathV
  | .w => d.treePathW

private theorem based_comp_formula {C : Type*} [Groupoid C] {o a b c : C}
    (A : o ⟶ a) (B : o ⟶ b) (C' : o ⟶ c) (f : a ⟶ b) (g : b ⟶ c) :
    (MulOpposite.op (End.of (A ≫ f ≫ Groupoid.inv B)) : (End o)ᵐᵒᵖ) *
      MulOpposite.op (End.of (B ≫ g ≫ Groupoid.inv C')) =
      MulOpposite.op (End.of (A ≫ (f ≫ g) ≫ Groupoid.inv C')) := by
  apply MulOpposite.unop_injective
  change (A ≫ f ≫ Groupoid.inv B) ≫ (B ≫ g ≫ Groupoid.inv C') = _
  simp [Category.assoc,Groupoid.inv_eq_inv]

private theorem based_id_formula {C : Type*} [Groupoid C] {o a : C} (A : o ⟶ a) :
    (1 : (End o)ᵐᵒᵖ) = MulOpposite.op (End.of (A ≫ (𝟙 a) ≫ Groupoid.inv A)) := by
  apply MulOpposite.unop_injective
  change 𝟙 _ = A ≫ (𝟙 a) ≫ Groupoid.inv A
  simp

private theorem based_eq_id {C : Type*} [Groupoid C] {o a : C} (A : o ⟶ a)
    (f : a ⟶ a) (h : A ≫ f ≫ Groupoid.inv A = 𝟙 o) : f = 𝟙 a := by
  have hh := congrArg (fun f => Groupoid.inv A ≫ f ≫ A) h
  simpa [Groupoid.inv_eq_inv,Category.assoc] using hh

theorem based_oriented_arrow {a c : Quiver.Symmetrify d.Vertex} (f : a ⟶ c) :
    d.toFundamentalGroup (d.edgeValue (d.orientedLabel f)) =
      MulOpposite.op (End.of (d.basePath a ≫ d.rawToFundamental.map f.toPath ≫
        Groupoid.inv (d.basePath c))) := by
  change d.Arrow a c ⊕ d.Arrow c a at f
  rcases f with f | f
  · change d.Arrow a c at f
    cases f with
    | x e => exact d.toFundamentalGroup_edge (.inl e)
    | l e =>
      have h := d.toFundamentalGroup_edge (.inr (.inl e))
      change d.toFundamentalGroup (d.edge (.inr (.inl e))) =
        MulOpposite.op (End.of ((𝟙 _) ≫ d.pathL e ≫ Groupoid.inv d.treePathV))
      simpa only [Category.id_comp,basedEdge] using h
    | rr e =>
      have h := d.toFundamentalGroup_edge (.inr (.inr e))
      change d.toFundamentalGroup (d.edge (.inr (.inr e))) =
        MulOpposite.op (End.of ((𝟙 _) ≫ d.pathR e ≫ Groupoid.inv d.treePathW))
      simpa only [Category.id_comp,basedEdge] using h
  · change d.Arrow c a at f
    cases f with
    | x e =>
      change d.toFundamentalGroup ((d.edge (.inl e))⁻¹) = _
      rw [map_inv,d.toFundamentalGroup_edge]
      apply MulOpposite.unop_injective
      change Groupoid.inv (d.treePathV ≫ d.pathX e ≫ Groupoid.inv d.treePathW) =
        d.treePathW ≫ Groupoid.inv (d.pathX e) ≫ Groupoid.inv d.treePathV
      simp [Groupoid.inv_eq_inv,Category.assoc]
    | l e =>
      change d.toFundamentalGroup ((d.edge (.inr (.inl e)))⁻¹) = _
      rw [map_inv,d.toFundamentalGroup_edge]
      apply MulOpposite.unop_injective
      change Groupoid.inv (d.pathL e ≫ Groupoid.inv d.treePathV) =
        d.treePathV ≫ Groupoid.inv (d.pathL e) ≫ Groupoid.inv (𝟙 _)
      simp [Groupoid.inv_eq_inv]
    | rr e =>
      change d.toFundamentalGroup ((d.edge (.inr (.inr e)))⁻¹) = _
      rw [map_inv,d.toFundamentalGroup_edge]
      apply MulOpposite.unop_injective
      change Groupoid.inv (d.pathR e ≫ Groupoid.inv d.treePathW) =
        d.treePathW ≫ Groupoid.inv (d.pathR e) ≫ Groupoid.inv (𝟙 _)
      simp [Groupoid.inv_eq_inv]

theorem based_rawWord {a c : Quiver.Symmetrify d.Vertex} (p : Quiver.Path a c) :
    d.toFundamentalGroup (d.wordValue (d.rawWord p)) =
      MulOpposite.op (End.of (d.basePath a ≫ d.rawToFundamental.map p ≫
        Groupoid.inv (d.basePath c))) := by
  induction p with
  | nil =>
    change 1 = MulOpposite.op (End.of (d.basePath a ≫
      d.rawToFundamental.map (𝟙 (d.rawVertex a)) ≫ Groupoid.inv (d.basePath a)))
    exact (based_id_formula (d.basePath a)).trans
      (congrArg (fun f : d.vertex a ⟶ d.vertex a =>
          MulOpposite.op (End.of (d.basePath a ≫ f ≫ Groupoid.inv (d.basePath a))))
        (CategoryTheory.Functor.map_id d.rawToFundamental (d.rawVertex a)).symm)
  | @cons c e p f ih =>
    change d.toFundamentalGroup (d.wordValue (d.rawWord p ++ [d.orientedLabel f])) = _
    rw [wordValue_append,wordValue_cons,wordValue_nil,mul_one,map_mul,ih,d.based_oriented_arrow]
    exact (based_comp_formula (d.basePath a) (d.basePath c) (d.basePath e) _ _).trans
      (congrArg (fun z : d.vertex a ⟶ d.vertex e =>
          MulOpposite.op (End.of (d.basePath a ≫ z ≫ Groupoid.inv (d.basePath e))))
        (CategoryTheory.Functor.map_comp d.rawToFundamental
          (show d.rawVertex a ⟶ d.rawVertex c from p)
          (show d.rawVertex c ⟶ d.rawVertex e from f.toPath)).symm)

theorem rawWord_nullhomotopic {a : Quiver.Symmetrify d.Vertex}
    (p : Quiver.Path a a) (h : d.wordValue (d.rawWord p) = 1) :
    d.RawHomotopic p (𝟙 (d.rawVertex a)) := by
  have hh := congrArg d.toFundamentalGroup h
  rw [d.based_rawWord,map_one] at hh
  have hu := congrArg MulOpposite.unop hh
  change d.basePath a ≫ d.rawToFundamental.map p ≫ Groupoid.inv (d.basePath a) = 𝟙 _ at hu
  apply (d.raw_equality_iff _ _).mp
  exact (based_eq_id (d.basePath a) _ hu).trans
    (CategoryTheory.Functor.map_id d.rawToFundamental (d.rawVertex a)).symm

end Release075.BlockPresentation

namespace Release075.BlockPresentation
open CategoryTheory
variable {I B : Type} {r : ℕ} (d : BlockPresentation I B r)

/-- The original oriented edges really are arrows in the symmetrified quiver. -/
def rawEdge (e : d.OrientedEdge) :
    (show Quiver.Symmetrify d.Vertex from d.edgeTarget (d.flipEdge e)) ⟶
      (show Quiver.Symmetrify d.Vertex from d.edgeTarget e) := by
  rcases e with ⟨e,s⟩
  rcases e with x | l | rr <;> cases s
  · exact Sum.inr (Arrow.x x)
  · exact Sum.inl (Arrow.x x)
  · exact Sum.inr (Arrow.l l)
  · exact Sum.inl (Arrow.l l)
  · exact Sum.inr (Arrow.rr rr)
  · exact Sum.inl (Arrow.rr rr)

@[simp] theorem orientedLabel_rawEdge (e : d.OrientedEdge) :
    d.orientedLabel (d.rawEdge e) = e := by
  rcases e with ⟨e,s⟩
  rcases e with x | l | rr <;> cases s <;> rfl

theorem WordPath.exists_raw {a c : d.Vertex} {w : List d.OrientedEdge}
    (h : Release075.WordPath d.flipEdge d.edgeTarget a c w) :
    ∃ p : (d.rawVertex a ⟶ d.rawVertex c), d.rawWord p = w := by
  induction h with
  | nil a => exact ⟨𝟙 _,rfl⟩
  | cons e h ih =>
    obtain ⟨p,hp⟩ := ih
    refine ⟨(d.rawEdge e).toPath ≫ p,?_⟩
    exact (d.rawWord_path_comp (d.rawEdge e).toPath p).trans
      (congrArg₂ List.append
        ((d.rawWord_toPath (d.rawEdge e)).trans
          (congrArg (fun e => [e]) (d.orientedLabel_rawEdge e))) hp)

theorem typed_nullword_lifted_fillable {a : d.Vertex} {w : List d.OrientedEdge}
    (ht : Release075.WordPath d.flipEdge d.edgeTarget a a w)
    (hv : d.wordValue w = 1) (g : d.GroupType) :
    Fillable d.liftedFlip d.liftedTarget d.LiftedFace (d.liftWord g w) := by
  obtain ⟨p,rfl⟩ := WordPath.exists_raw d ht
  exact d.nullhomotopic_lifted_fillable (d.rawWord_nullhomotopic p hv) g

end Release075.BlockPresentation

namespace Release075.BlockPresentation
attribute [local instance] Classical.propDecidable Classical.decEq
variable {I B : Type} {r : ℕ} (d : BlockPresentation I B r)

theorem wordValue_reverse (w : List d.OrientedEdge) :
    d.wordValue (reverseWord d.flipEdge w) = (d.wordValue w)⁻¹ := by
  induction w with
  | nil => simp
  | cons e w ih => simp [reverseWord_cons,ih,mul_inv_rev]

theorem exists_based_word (g : d.GroupType) :
    ∃ w, WordPath d.flipEdge d.edgeTarget .o .o w ∧ d.wordValue w = g := by
  let K : Subgroup d.GroupType := {
    carrier := {g | ∃ w, WordPath d.flipEdge d.edgeTarget .o .o w ∧ d.wordValue w = g}
    one_mem' := ⟨[],.nil _,rfl⟩
    mul_mem' := by
      rintro g h ⟨u,hu,rfl⟩ ⟨v,hv,rfl⟩
      exact ⟨u++v,hu.append hv,d.wordValue_append u v⟩
    inv_mem' := by
      rintro g ⟨w,hw,rfl⟩
      exact ⟨reverseWord d.flipEdge w,hw.reverse d.flipEdge_flipEdge,d.wordValue_reverse w⟩ }
  apply PresentedGroup.generated_by d.relators K _ g
  intro e
  change ∃ w, WordPath d.flipEdge d.edgeTarget .o .o w ∧ d.wordValue w = d.edge e
  rcases e with e | e | e
  · refine ⟨[(d.treeL,true),(.inl e,true),(d.treeR,false)],?_,?_⟩
    · exact WordPath.cons (flip:=d.flipEdge) (color:=d.edgeTarget) (d.treeL,true)
        (WordPath.cons (flip:=d.flipEdge) (color:=d.edgeTarget) (Sum.inl e,true)
          (WordPath.cons (flip:=d.flipEdge) (color:=d.edgeTarget) (d.treeR,false) (WordPath.nil Vertex.o)))
    · simp [wordValue,edgeValue,d.treeL_eq_one,d.treeR_eq_one]
  · refine ⟨[(.inr (.inl e),true),(d.treeL,false)],?_,?_⟩
    · exact WordPath.cons (flip:=d.flipEdge) (color:=d.edgeTarget)
        (.inr (.inl e),true) (WordPath.cons (flip:=d.flipEdge) (color:=d.edgeTarget) (d.treeL,false) (WordPath.nil Vertex.o))
    · simp [wordValue,edgeValue,d.treeL_eq_one]
  · refine ⟨[(.inr (.inr e),true),(d.treeR,false)],?_,?_⟩
    · exact WordPath.cons (flip:=d.flipEdge) (color:=d.edgeTarget)
        (.inr (.inr e),true) (WordPath.cons (flip:=d.flipEdge) (color:=d.edgeTarget) (d.treeR,false) (WordPath.nil Vertex.o))
    · simp [wordValue,edgeValue,d.treeR_eq_one]

theorem WordPath.shift {x y : d.LiftedVertex} {w : List d.LiftedEdge}
    (hw : WordPath d.liftedFlip d.liftedTarget x y w) (g : d.GroupType) :
    WordPath d.liftedFlip d.liftedTarget (d.shiftVertex g x) (d.shiftVertex g y)
      (w.map (d.shiftEdge g)) := by
  induction hw with
  | nil x => exact .nil _
  | cons e hw ih =>
    have hh := WordPath.cons (flip:=d.liftedFlip) (color:=d.liftedTarget) (d.shiftEdge g e) ih
    simpa only [List.map_cons,←d.shiftEdge_flip,d.shiftEdge_target] using hh

theorem WordPath.forget {x y : d.LiftedVertex} {w : List d.LiftedEdge}
    (hw : WordPath d.liftedFlip d.liftedTarget x y w) :
    WordPath d.flipEdge d.edgeTarget x.1 y.1 (w.map Prod.fst) := by
  induction hw with
  | nil x => exact .nil _
  | cons e hw ih => exact .cons e.1 ih

theorem WordPath.displacement {x y : d.LiftedVertex} {w : List d.LiftedEdge}
    (hw : WordPath d.liftedFlip d.liftedTarget x y w) :
    x.2 * d.wordValue (w.map Prod.fst) = y.2 := by
  induction hw with
  | nil x => simp
  | cons e hw ih =>
    change (e.2*(d.edgeValue e.1)⁻¹) *
      (d.edgeValue e.1 * d.wordValue (_:List d.OrientedEdge)) = _
    simpa only [mul_assoc,inv_mul_cancel_left,liftedTarget] using ih

theorem WordPath.liftWord_eq {x y : d.LiftedVertex} {w : List d.LiftedEdge}
    (hw : WordPath d.liftedFlip d.liftedTarget x y w) :
    d.liftWord x.2 (w.map Prod.fst) = w := by
  induction hw with
  | nil x => rfl
  | cons e hw ih =>
    change d.liftWord (e.2 * (d.edgeValue e.1)⁻¹) (e.1::_) = e::_
    simpa only [liftWord_cons,inv_mul_cancel_right,Prod.mk.eta,liftedTarget] using congrArg (e::·) ih

theorem lifted_closed_fillable {x : d.LiftedVertex} {w : List d.LiftedEdge}
    (hw : WordPath d.liftedFlip d.liftedTarget x x w) :
    Fillable d.liftedFlip d.liftedTarget d.LiftedFace w := by
  have hv : d.wordValue (w.map Prod.fst) = 1 :=
    mul_left_cancel ((WordPath.displacement d hw).trans (mul_one x.2).symm)
  have hf := d.typed_nullword_lifted_fillable (WordPath.forget d hw) hv x.2
  rwa [WordPath.liftWord_eq d hw] at hf

theorem exists_lifted_path (g : d.GroupType) :
    ∃ w, WordPath d.liftedFlip d.liftedTarget (.o,1) (.o,g) w := by
  obtain ⟨w,hw,hv⟩ := d.exists_based_word g
  exact ⟨d.liftWord 1 w,by simpa only [hv,one_mul] using d.liftWord_typed hw 1⟩

theorem boundary₁_wordChain {x y : d.LiftedVertex} {w : List d.LiftedEdge}
    (hw : WordPath d.liftedFlip d.liftedTarget x y w) :
    d.boundary₁ (d.wordChain w) = Finsupp.single y 1 - Finsupp.single x 1 := by
  induction hw with
  | nil x => simp [wordChain]
  | cons e hw ih =>
    change d.boundary₁ (d.edgeChain e + d.wordChain _) = _
    rw [map_add,d.boundary₁_edgeChain,ih]
    abel

def powerWord (g : d.GroupType) (w : List d.LiftedEdge) : ℕ → List d.LiftedEdge
  | 0 => []
  | n+1 => powerWord g w n ++ w.map (d.shiftEdge (g^n))

@[simp] theorem powerWord_zero (g : d.GroupType) (w : List d.LiftedEdge) :
    d.powerWord g w 0 = [] := rfl

theorem powerWord_succ (g : d.GroupType) (w : List d.LiftedEdge) (n : ℕ) :
    d.powerWord g w (n+1) = d.powerWord g w n ++ w.map (d.shiftEdge (g^n)) := rfl

theorem powerWord_succ_left (g : d.GroupType) (w : List d.LiftedEdge) (n : ℕ) :
    d.powerWord g w (n+1) = w ++ (d.powerWord g w n).map (d.shiftEdge g) := by
  induction n with
  | zero => simpa only [powerWord,pow_zero,List.nil_append,List.map_nil,List.append_nil] using
      (List.map_id'' (d.shiftEdge_one) w)
  | succ n ih =>
    rw [powerWord_succ]
    conv_lhs => rw [ih]
    conv_rhs => rw [powerWord_succ]
    rw [List.map_append,List.map_map,List.append_assoc]
    congr 2
    apply List.map_congr_left
    intro e _
    simp only [Function.comp_def,←shiftEdge_mul,←pow_succ']

theorem powerWord_typed (g : d.GroupType) {w : List d.LiftedEdge}
    (hw : WordPath d.liftedFlip d.liftedTarget (.o,1) (.o,g) w) (n : ℕ) :
    WordPath d.liftedFlip d.liftedTarget (.o,1) (.o,g^n) (d.powerWord g w n) := by
  induction n with
  | zero => simpa only [powerWord_zero,pow_zero] using
      (WordPath.nil (flip:=d.liftedFlip) (color:=d.liftedTarget) (.o,1))
  | succ n ih =>
    rw [powerWord_succ]
    apply ih.append
    simpa only [shiftVertex,mul_one,pow_succ] using WordPath.shift d hw (g^n)

theorem powerWord_chain (g : d.GroupType) (w : List d.LiftedEdge) (n : ℕ) :
    d.wordChain (d.powerWord g w n) = ∑ i ∈ Finset.range n, chainShift (g^i) (d.wordChain w) := by
  induction n with
  | zero => simp [wordChain]
  | succ n ih => rw [powerWord_succ,wordChain_append,wordChain_shift,ih,Finset.sum_range_succ]

theorem powerWord_shift_rotate (g : d.GroupType) (w : List d.LiftedEdge) {n : ℕ}
    (hn : 0 < n) (hg : g^n = 1) :
    (d.powerWord g w n).map (d.shiftEdge g) = (d.powerWord g w n).rotate w.length := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  conv_rhs => rw [powerWord_succ_left,List.rotate_append_length_eq]
  rw [powerWord_succ,List.map_append,List.map_map]
  congr 1
  have he : (d.shiftEdge g) ∘ (d.shiftEdge (g^k)) = id := by
    funext e
    simp only [Function.comp_def,← shiftEdge_mul,← pow_succ',hg,shiftEdge_one,id_eq]
  rw [he,List.map_id]

theorem powerWord_chain_norm (g : d.GroupType) (hg : IsOfFinOrder g)
    [Fintype (Subgroup.zpowers g)] (w : List d.LiftedEdge) :
    d.wordChain (d.powerWord g w (orderOf g)) =
      FreeChain.subgroupNorm (Subgroup.zpowers g) (d.wordChain w) := by
  rw [powerWord_chain]
  simp only [FreeChain.subgroupNorm,LinearMap.sum_apply,LinearEquiv.coe_coe]
  rw [← Equiv.sum_comp (finEquivZPowers hg)]
  exact (Fin.sum_univ_eq_sum_range (fun i => chainShift (g^i) (d.wordChain w)) (orderOf g)).symm

end Release075.BlockPresentation

namespace Release075.FullFilling
variable {I B : Type} {r : ℕ} {d : BlockPresentation I B r}
variable {w w' : List d.LiftedEdge}
  (D : FullFilling d.liftedFlip d.liftedTarget d.LiftedFace w)

theorem allTriangles_reword (hD : D.AllTriangles) (h : w = w') :
    (D.reword h).AllTriangles := by subst w'; exact hD

@[simp] theorem faceChain_reword (h : w = w') : (D.reword h).faceChain = D.faceChain := by
  subst w'; rfl

end Release075.FullFilling

end OAI
end
end

section
section
namespace OAI

namespace Release075.MarkedLineData
attribute [local instance] Classical.propDecidable Classical.decEq
variable {q r : ℕ} [Fact q.Prime] (d : MarkedLineData q r) (hr : 0 < r)

theorem presentation_finiteOrder_eq_one (g : (d.presentation hr).GroupType)
    (hg : IsOfFinOrder g) : g = 1 := by
  let P := d.presentation hr
  let H := Subgroup.zpowers g
  let : Finite H := hg.finite_zpowers
  let : Fintype H := Fintype.ofFinite H
  let t : H := ⟨g,Subgroup.mem_zpowers g⟩
  have ht : ∀ x : H, x ∈ Subgroup.zpowers t := by
    intro x
    obtain ⟨n,hn⟩ := Subgroup.mem_zpowers_iff.mp x.property
    exact Subgroup.mem_zpowers_iff.mpr ⟨n,Subtype.ext hn⟩
  obtain ⟨w,hw⟩ := P.exists_lifted_path g
  let W := P.powerWord g w (orderOf g)
  have hW : WordPath P.liftedFlip P.liftedTarget (.o,1) (.o,1) W := by
    simpa only [pow_orderOf_eq_one] using P.powerWord_typed g hw (orderOf g)
  obtain ⟨D⟩ := P.lifted_closed_fillable hW
  have hD : D.full.AllTriangles := D.full_triangular
  have hrot : W.map (P.shiftEdge g) = W.rotate w.length :=
    P.powerWord_shift_rotate g w hg.orderOf_pos (pow_orderOf_eq_one g)
  have hinv : chainShift g D.full.faceChain = D.full.faceChain := by
    have hu := d.fullChain_unique hr (BlockPresentation.WordPath.shift P hW g)
      (D.full.shift g) ((D.full.rotate w.length).reword hrot.symm)
      (D.full.allTriangles_shift hD g)
      ((D.full.rotate w.length).allTriangles_reword
        (D.full.allTriangles_rotate hD w.length) hrot.symm)
    simpa only [FullFilling.faceChain_shift,FullFilling.faceChain_reword,
      FullFilling.faceChain_rotate] using hu
  apply FreeChain.cyclic_chain_obstruction H t ht P.boundary₁ P.boundary₂
    (fun h c => P.boundary₁_shift h c) (fun h c => P.boundary₂_shift h c)
    P.boundary₁_boundary₂ P.augmentation_boundary₁
    (Finsupp.single (.o,1) 1) (by simp) (P.wordChain w) _ D.full.faceChain _ hinv
  · simpa only [chainShift_single,one_mul,mul_one] using P.boundary₁_wordChain hw
  · exact (D.full.boundary₂_faceChain hD).trans (P.powerWord_chain_norm g hg w)

theorem presentation_torsionFree : TorsionFree (d.presentation hr).GroupType := by
  intro g n hn hg
  exact d.presentation_finiteOrder_eq_one hr g (isOfFinOrder_iff_pow_eq_one.mpr ⟨n,hn,hg⟩)

end Release075.MarkedLineData

end OAI
end
end

section
section
namespace OAI

namespace Release075.Discrete

structure Metric (V : Type) where
  dist : V → V → ℕ
  self : ∀ x, dist x x = 0
  symm : ∀ x y, dist x y = dist y x
  triangle : ∀ x y z, dist x z ≤ dist x y + dist y z

variable {V : Type} (M : Metric V)

structure Path (a b : V) where
  length : ℕ
  point : ℕ → V
  zero : point 0 = a
  stable : ∀ i, length ≤ i → point i = b
  step : ∀ i, i < length → M.dist (point i) (point (i+1)) ≤ 1

namespace Path
variable {M} {a b c : V}

@[simp] theorem last (p : Path M a b) : p.point p.length = b := p.stable _ le_rfl

@[simp] theorem at_min (p : Path M a b) (i : ℕ) : p.point (min i p.length) = p.point i := by
  by_cases h : i ≤ p.length
  · rw [min_eq_left h]
  · rw [min_eq_right (by omega),p.last,p.stable i (by omega)]

def Geodesic (p : Path M a b) : Prop := p.length = M.dist a b

def Mem (p : Path M a b) (x : V) : Prop := ∃ i ≤ p.length, p.point i = x

@[simp] theorem start_mem (p : Path M a b) : p.Mem a := ⟨0,Nat.zero_le _,p.zero⟩
@[simp] theorem end_mem (p : Path M a b) : p.Mem b := ⟨p.length,le_rfl,p.last⟩

def nil (a : V) : Path M a a where
  length := 0
  point _ := a
  zero := rfl
  stable _ _ := rfl
  step := by intro i hi; omega

def append (p : Path M a b) (q : Path M b c) : Path M a c where
  length := p.length + q.length
  point i := if i < p.length then p.point i else q.point (i-p.length)
  zero := by
    split_ifs with h
    · exact p.zero
    · simpa only [Nat.zero_sub,q.zero] using
        (p.stable 0 (by omega)).symm.trans p.zero
  stable i hi := by
    rw [ite_eq_right (by omega),q.stable _ (by omega)]
  step i hi := by
    by_cases h : i+1 < p.length
    · simpa only [ite_eq_left h,ite_eq_left (show i < p.length by omega)] using p.step i (by omega)
    · by_cases h' : i < p.length
      · have he : i+1 = p.length := by omega
        simpa only [ite_eq_left h',ite_eq_right h,he,Nat.sub_self,q.zero,p.last,ite_self] using p.step i h'
      · simpa only [ite_eq_right h',ite_eq_right h,show i+1-p.length = (i-p.length)+1 by omega] using
          q.step (i-p.length) (by omega)

@[simp] theorem length_append (p : Path M a b) (q : Path M b c) :
    (p.append q).length = p.length+q.length := rfl

@[simp] theorem append_at_left (p : Path M a b) (q : Path M b c) {i : ℕ} (hi : i ≤ p.length) :
    (p.append q).point i = p.point i := by
  change (if i < p.length then _ else _) = _
  split_ifs with h
  · rfl
  · have he : i = p.length := by omega
    simp only [he,Nat.sub_self,q.zero,p.last]

@[simp] theorem append_at_right (p : Path M a b) (q : Path M b c) (i : ℕ) :
    (p.append q).point (p.length+i) = q.point i := by
  change (if p.length+i < p.length then _ else _) = _
  simp

def reverse (p : Path M a b) : Path M b a where
  length := p.length
  point i := p.point (p.length-i)
  zero := by simpa only [Nat.sub_zero] using p.last
  stable i hi := by simpa only [Nat.sub_eq_zero_of_le hi] using p.zero
  step i hi := by
    rw [M.symm]
    have he : p.length-i = (p.length-(i+1))+1 := by omega
    rw [he]
    exact p.step _ (by omega)

def sub (p : Path M a b) (i j : ℕ) (hij : i ≤ j) (hj : j ≤ p.length) :
    Path M (p.point i) (p.point j) where
  length := j-i
  point k := p.point (min (i+k) j)
  zero := by simp only [Nat.add_zero,min_eq_left hij]
  stable k hk := by rw [min_eq_right (by omega)]
  step k hk := by
    rw [min_eq_left (show i+k ≤ j by omega),min_eq_left (show i+(k+1) ≤ j by omega)]
    simpa only [Nat.add_assoc] using p.step (i+k) (by omega)

@[simp] theorem sub_at (p : Path M a b) {i j k : ℕ} (hij : i ≤ j) (hj : j ≤ p.length)
    (hk : k ≤ j-i) : (p.sub i j hij hj).point k = p.point (i+k) := by
  change p.point (min (i+k) j) = _
  rw [min_eq_left (by omega)]

theorem mem_reverse_iff (p : Path M a b) (x : V) : p.reverse.Mem x ↔ p.Mem x := by
  constructor
  · rintro ⟨i,hi,hx⟩; exact ⟨p.length-i,Nat.sub_le _ _,hx⟩
  · rintro ⟨i,hi,hx⟩
    exact ⟨p.length-i,Nat.sub_le _ _,by simpa only [reverse,Nat.sub_sub_self hi] using hx⟩

theorem mem_sub (p : Path M a b) {i j : ℕ} (hij : i ≤ j) (hj : j ≤ p.length)
    {x : V} (hx : (p.sub i j hij hj).Mem x) : p.Mem x := by
  obtain ⟨k,hk,hx⟩ := hx
  exact ⟨i+k,by change k ≤ j-i at hk; omega,(p.sub_at hij hj hk).symm.trans hx⟩

theorem mem_append_iff (p : Path M a b) (q : Path M b c) (x : V) :
    (p.append q).Mem x ↔ p.Mem x ∨ q.Mem x := by
  constructor
  · rintro ⟨i,hi,hx⟩
    by_cases h : i ≤ p.length
    · exact Or.inl ⟨i,h,(p.append_at_left q h).symm.trans hx⟩
    · refine Or.inr ⟨i-p.length,by change i ≤ p.length+q.length at hi; omega,?_⟩
      have he : p.length+(i-p.length) = i := by omega
      have hh := p.append_at_right q (i-p.length)
      rw [he] at hh
      exact hh.symm.trans hx
  · rintro (⟨i,hi,rfl⟩ | ⟨i,hi,rfl⟩)
    · exact ⟨i,by change i ≤ p.length+q.length; omega,p.append_at_left q hi⟩
    · exact ⟨p.length+i,by change p.length+i ≤ p.length+q.length; omega,p.append_at_right q i⟩

theorem dist_at_le (p : Path M a b) {i j : ℕ} (hij : i ≤ j) (hj : j ≤ p.length) :
    M.dist (p.point i) (p.point j) ≤ j-i := by
  induction j, hij using Nat.le_induction with
  | base => simp only [M.self,Nat.sub_self,le_refl]
  | succ j hij ih =>
    have h := M.triangle (p.point i) (p.point j) (p.point (j+1))
    have h' := p.step j (by omega)
    have hh := ih (by omega)
    omega

theorem dist_le_length (p : Path M a b) : M.dist a b ≤ p.length := by
  simpa only [p.zero,p.last,Nat.sub_zero] using p.dist_at_le (Nat.zero_le _) le_rfl

theorem geodesic_dist_at (p : Path M a b) (hp : p.Geodesic)
    {i j : ℕ} (hij : i ≤ j) (hj : j ≤ p.length) :
    M.dist (p.point i) (p.point j) = j-i := by
  have h₁ := p.dist_at_le (i:=0) (j:=i) (Nat.zero_le _) (hij.trans hj)
  have h₂ := p.dist_at_le (i:=j) (j:=p.length) hj le_rfl
  have h₃ := p.dist_at_le hij hj
  rw [p.zero,Nat.sub_zero] at h₁
  rw [p.last] at h₂
  have h₄ := M.triangle a (p.point i) b
  have h₅ := M.triangle (p.point i) (p.point j) b
  change p.length = M.dist a b at hp
  omega

theorem geodesic_start_dist (p : Path M a b) (hp : p.Geodesic) {i : ℕ} (hi : i ≤ p.length) :
    M.dist a (p.point i) = i := by
  simpa only [p.zero,Nat.sub_zero] using p.geodesic_dist_at hp (Nat.zero_le _) hi

theorem geodesic_end_dist (p : Path M a b) (hp : p.Geodesic) {i : ℕ} (hi : i ≤ p.length) :
    M.dist (p.point i) b = p.length-i := by
  simpa only [p.last] using p.geodesic_dist_at hp hi le_rfl

theorem geodesic_reverse (p : Path M a b) (hp : p.Geodesic) : p.reverse.Geodesic := by
  change p.length = M.dist b a
  rw [M.symm]
  exact hp

theorem geodesic_sub (p : Path M a b) (hp : p.Geodesic)
    {i j : ℕ} (hij : i ≤ j) (hj : j ≤ p.length) : (p.sub i j hij hj).Geodesic :=
  (p.geodesic_dist_at hp hij hj).symm

def integral (p : Path M a b) (F : V → V → ℤ) : ℤ :=
  ∑ i ∈ Finset.range p.length, F (p.point i) (p.point (i+1))

@[simp] theorem integral_nil (a : V) (F : V → V → ℤ) : (nil (M:=M) a).integral F = 0 := by
  simp [integral,nil]

theorem integral_append (p : Path M a b) (q : Path M b c) (F : V → V → ℤ) :
    (p.append q).integral F = p.integral F+q.integral F := by
  unfold integral
  rw [length_append,Finset.sum_range_add]
  congr 1
  · apply Finset.sum_congr rfl
    intro i hi
    rw [p.append_at_left q (by have := Finset.mem_range.mp hi; omega),
      p.append_at_left q (by have := Finset.mem_range.mp hi; omega)]
  · apply Finset.sum_congr rfl
    intro i _
    rw [p.append_at_right q i,show p.length+i+1 = p.length+(i+1) by omega,p.append_at_right]

end Path

namespace Metric
variable {M}

theorem int_dist_sub_le (x y z : V) : |(M.dist x y : ℤ)-M.dist x z| ≤ M.dist y z := by
  have h₁ := M.triangle x y z
  have h₂ := M.triangle x z y
  rw [M.symm z y] at h₂
  rw [abs_le]
  constructor <;> omega

def tent (o : V) (R : ℕ) (x : V) : ℤ := max 0 ((R:ℤ)-M.dist o x)

theorem tent_nonneg (o : V) (R : ℕ) (x : V) : 0 ≤ M.tent o R x := le_max_left _ _

theorem tent_zero {o x : V} {R : ℕ} (h : R ≤ M.dist o x) : M.tent o R x = 0 := by
  unfold tent
  omega

theorem tent_lipschitz (o : V) (R : ℕ) (x y : V) :
    |M.tent o R x - M.tent o R y| ≤ M.dist x y := by
  have h := M.int_dist_sub_le o x y
  unfold tent
  rw [abs_le] at h ⊢
  omega

def form (o a : V) (R : ℕ) (x y : V) : ℤ :=
  (M.tent o R x+M.tent o R y)*((M.dist a y:ℤ)-M.dist a x)

theorem form_flip (o a : V) (R : ℕ) (x y : V) : M.form o a R y x = -M.form o a R x y := by
  unfold form
  ring

theorem form_self (o a x : V) (R : ℕ) : M.form o a R x x = 0 := by simp [form]

theorem form_zero {o a x y : V} {R : ℕ} (hx : R ≤ M.dist o x) (hy : R ≤ M.dist o y) :
    M.form o a R x y = 0 := by rw [form,M.tent_zero hx,M.tent_zero hy,zero_add,zero_mul]

theorem form_triangle_bound (o a x y z : V) (R : ℕ)
    (hxy : M.dist x y ≤ 1) (_hyz : M.dist y z ≤ 1) (hzx : M.dist z x ≤ 1) :
    |M.form o a R x y+M.form o a R y z+M.form o a R z x| ≤ 2 := by
  have hF₁ : |M.tent o R y-M.tent o R x| ≤ 1 :=
    (M.tent_lipschitz o R y x).trans (by rw [M.symm y x]; exact_mod_cast hxy)
  have hF₂ : |M.tent o R z-M.tent o R x| ≤ 1 :=
    (M.tent_lipschitz o R z x).trans (by exact_mod_cast hzx)
  have hG₁ : |(M.dist a y:ℤ)-M.dist a x| ≤ 1 :=
    (M.int_dist_sub_le a y x).trans (by rw [M.symm y x]; exact_mod_cast hxy)
  have hG₂ : |(M.dist a z:ℤ)-M.dist a x| ≤ 1 :=
    (M.int_dist_sub_le a z x).trans (by exact_mod_cast hzx)
  have he : M.form o a R x y+M.form o a R y z+M.form o a R z x =
      (M.tent o R y-M.tent o R x)*((M.dist a z:ℤ)-M.dist a x) -
      (M.tent o R z-M.tent o R x)*((M.dist a y:ℤ)-M.dist a x) := by unfold form; ring
  rw [he]
  calc
    _ ≤ |(M.tent o R y-M.tent o R x)*((M.dist a z:ℤ)-M.dist a x)| +
        |(M.tent o R z-M.tent o R x)*((M.dist a y:ℤ)-M.dist a x)| := abs_sub _ _
    _ ≤ 1*1+1*1 := by
      rw [abs_mul,abs_mul]
      exact add_le_add (mul_le_mul hF₁ hG₂ (abs_nonneg _) (by omega))
        (mul_le_mul hF₂ hG₁ (abs_nonneg _) (by omega))
    _ = 2 := by norm_num

end Metric
end Release075.Discrete

namespace Release075.Discrete
variable {V : Type} {M : Metric V}

namespace Path
variable {a b c d e f : V}

theorem dist_start_mem (p : Path M a b) {x : V} (hx : p.Mem x) : M.dist a x ≤ p.length := by
  obtain ⟨i,hi,rfl⟩ := hx
  have h := p.dist_at_le (Nat.zero_le i) hi
  rw [p.zero,Nat.sub_zero] at h
  omega

theorem dist_end_mem (p : Path M a b) {x : V} (hx : p.Mem x) : M.dist b x ≤ p.length := by
  exact p.reverse.dist_start_mem ((p.mem_reverse_iff x).mpr hx)

def SideNear (T : ℕ) (p : Path M a b) (q : Path M c d) (s : Path M e f) : Prop :=
  ∀ x, p.Mem x → ∃ y, (q.Mem y ∨ s.Mem y) ∧ M.dist x y ≤ T

theorem SideNear.reverse (T : ℕ) {p : Path M a b} {q : Path M c d} {s : Path M e f}
    (h : SideNear T p q s) : SideNear T p.reverse q s := by
  intro x hx
  exact h x ((p.mem_reverse_iff x).mp hx)

theorem SideNear.swap (T : ℕ) {p : Path M a b} {q : Path M c d} {s : Path M e f}
    (h : SideNear T p q s) : SideNear T p s q := by
  intro x hx
  obtain ⟨y,hy,hd⟩ := h x hx
  exact ⟨y,hy.symm,hd⟩

theorem SideNear.reverse_left (T : ℕ) {p : Path M a b} {q : Path M c d} {s : Path M e f}
    (h : SideNear T p q s) : SideNear T p q.reverse s := by
  intro x hx
  obtain ⟨y,hy,hd⟩ := h x hx
  exact ⟨y,hy.imp ((q.mem_reverse_iff y).mpr) id,hd⟩

theorem SideNear.reverse_right (T : ℕ) {p : Path M a b} {q : Path M c d} {s : Path M e f}
    (h : SideNear T p q s) : SideNear T p q s.reverse := by
  exact ((h.swap T).reverse_left T).swap T

def TriangleNear (T : ℕ) (p : Path M a b) (q : Path M b c) (s : Path M a c) : Prop :=
  SideNear T p q s ∧ SideNear T q s p ∧ SideNear T s p q

theorem synchronous_of_near {p : Path M a b} {s : Path M a c}
    (hp : p.Geodesic) (hs : s.Geodesic) {i j T : ℕ}
    (hi : i ≤ p.length) (hi' : i ≤ s.length) (hj : j ≤ s.length)
    (h : M.dist (p.point i) (s.point j) ≤ T) :
    M.dist (p.point i) (s.point i) ≤ 2*T := by
  have h₁ := M.triangle a (p.point i) (s.point j)
  have h₂ := M.triangle a (s.point j) (p.point i)
  rw [p.geodesic_start_dist hp hi,s.geodesic_start_dist hs hj] at h₁ h₂
  rw [M.symm (s.point j) (p.point i)] at h₂
  have h₃ := M.triangle (p.point i) (s.point j) (s.point i)
  by_cases hij : i ≤ j
  · rw [M.symm (s.point j) (s.point i),s.geodesic_dist_at hs hij hj] at h₃
    omega
  · rw [s.geodesic_dist_at hs (by omega : j ≤ i) hi'] at h₃
    omega

/-- The elementary tripod comparison: synchronous precentral points have width O(T). -/
theorem synchronous {p : Path M a b} {q : Path M b c} {s : Path M a c}
    (hp : p.Geodesic) (hq : q.Geodesic) (hs : s.Geodesic) {T i : ℕ}
    (hthin : SideNear T p q s) (hi : i ≤ (p.length+s.length-q.length)/2) :
    M.dist (p.point i) (s.point i) ≤ 4*T+2 := by
  have hA : p.length ≤ q.length+s.length := by
    have h := M.triangle a c b
    change p.length = M.dist a b at hp
    change q.length = M.dist b c at hq
    change s.length = M.dist a c at hs
    rw [M.symm c b] at h
    omega
  have hC : s.length ≤ p.length+q.length := by
    have h := M.triangle a b c
    change p.length = M.dist a b at hp
    change q.length = M.dist b c at hq
    change s.length = M.dist a c at hs
    omega
  have hB : q.length ≤ p.length+s.length := by
    have h := M.triangle b a c
    change p.length = M.dist a b at hp
    change q.length = M.dist b c at hq
    change s.length = M.dist a c at hs
    rw [M.symm b a] at h
    omega
  let α := (p.length+s.length-q.length)/2
  have hiA : i ≤ p.length := by omega
  have hiC : i ≤ s.length := by omega
  by_cases hsmall : α ≤ T
  · have h := M.triangle (p.point i) a (s.point i)
    rw [M.symm (p.point i) a,p.geodesic_start_dist hp hiA,
      s.geodesic_start_dist hs hiC] at h
    change i ≤ α at hi
    omega
  · let k := min i (α-(T+1))
    have hki : k ≤ i := min_le_left _ _
    have hkA : k ≤ p.length := hki.trans hiA
    have hkC : k ≤ s.length := hki.trans hiC
    obtain ⟨x,hx,hd⟩ := hthin (p.point k) ⟨k,hkA,rfl⟩
    have hnq : ¬ q.Mem x := by
      rintro ⟨j,hj,rfl⟩
      have h₁ := M.triangle a (p.point k) b
      have h₂ := M.triangle (p.point k) (q.point j) b
      have h₃ := M.triangle a (p.point k) c
      have h₄ := M.triangle (p.point k) (q.point j) c
      rw [p.geodesic_start_dist hp hkA] at h₁ h₃
      rw [M.symm (q.point j) b,q.geodesic_start_dist hq hj] at h₂
      rw [q.geodesic_end_dist hq hj] at h₄
      change p.length = M.dist a b at hp
      change s.length = M.dist a c at hs
      dsimp [k,α] at *
      omega
    obtain ⟨j,hj,hjx⟩ := hx.resolve_left hnq
    rw [←hjx] at hd
    have hsync := synchronous_of_near hp hs hkA hkC hj hd
    have h₁ := M.triangle (p.point i) (p.point k) (s.point i)
    have h₂ := M.triangle (p.point k) (s.point k) (s.point i)
    rw [M.symm (p.point i) (p.point k),p.geodesic_dist_at hp hki hiA] at h₁
    rw [s.geodesic_dist_at hs hki hiC] at h₂
    change i ≤ α at hi
    dsimp [k] at *
    omega

theorem integral_form_nonneg (p : Path M a b) (hp : p.Geodesic) (o : V) (T : ℕ) :
    0 ≤ p.integral (M.form o a T) := by
  apply Finset.sum_nonneg
  intro i hi
  have hi' := Finset.mem_range.mp hi
  rw [Metric.form,p.geodesic_start_dist hp (by omega : i+1 ≤ p.length),
    p.geodesic_start_dist hp (by omega : i ≤ p.length)]
  have h₁ := M.tent_nonneg o T (p.point i)
  have h₂ := M.tent_nonneg o T (p.point (i+1))
  push_cast
  nlinarith

theorem integral_form_quadratic (p : Path M a b) (hp : p.Geodesic) {t T : ℕ}
    (ht : t ≤ p.length) (hend : T ≤ M.dist (p.point t) b) :
    ((T/2:ℕ):ℤ)^2 ≤ p.integral (M.form (p.point t) a T) := by
  let k := T/2
  have htk : t+k ≤ p.length := by
    rw [p.geodesic_end_dist hp ht] at hend
    dsimp [k]
    omega
  have hnneg : ∀ i ∈ Finset.range p.length,
      0 ≤ M.form (p.point t) a T (p.point i) (p.point (i+1)) := by
    intro i hi
    have hi' := Finset.mem_range.mp hi
    rw [Metric.form,p.geodesic_start_dist hp (by omega : i+1 ≤ p.length),
      p.geodesic_start_dist hp (by omega : i ≤ p.length)]
    have h₁ := M.tent_nonneg (p.point t) T (p.point i)
    have h₂ := M.tent_nonneg (p.point t) T (p.point (i+1))
    push_cast
    nlinarith
  have hsub : Finset.Ico t (t+k) ⊆ Finset.range p.length := by
    intro i hi
    simp only [Finset.mem_Ico,Finset.mem_range] at *
    omega
  have hlarge : ∀ i ∈ Finset.Ico t (t+k),
      (k:ℤ) ≤ M.form (p.point t) a T (p.point i) (p.point (i+1)) := by
    intro i hi
    obtain ⟨hti,hit⟩ := Finset.mem_Ico.mp hi
    have hiA : i+1 ≤ p.length := by omega
    have hdi := p.geodesic_dist_at hp hti (by omega : i ≤ p.length)
    rw [Metric.form,p.geodesic_start_dist hp hiA,
      p.geodesic_start_dist hp (by omega : i ≤ p.length)]
    have h₁ : (k:ℤ) ≤ M.tent (p.point t) T (p.point i) := by
      rw [Metric.tent,hdi]
      dsimp [k] at *
      omega
    have h₂ := M.tent_nonneg (p.point t) T (p.point (i+1))
    push_cast
    nlinarith
  calc
    ((T/2:ℕ):ℤ)^2 = ∑ _i ∈ Finset.Ico t (t+k), (k:ℤ) := by
      simp [Nat.card_Ico,k,pow_two]
    _ ≤ ∑ i ∈ Finset.Ico t (t+k), M.form (p.point t) a T (p.point i) (p.point (i+1)) :=
      Finset.sum_le_sum hlarge
    _ ≤ p.integral (M.form (p.point t) a T) := by
      exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i hi _ => hnneg i hi)

theorem integral_form_zero (p : Path M a b) {o z : V} {T : ℕ}
    (hfar : ∀ x, p.Mem x → T ≤ M.dist o x) : p.integral (M.form o z T) = 0 := by
  apply Finset.sum_eq_zero
  intro i hi
  have hi' := Finset.mem_range.mp hi
  exact M.form_zero (hfar _ ⟨i,by omega,rfl⟩) (hfar _ ⟨i+1,by omega,rfl⟩)

end Path

/-- A linear bound on the integral, for every clipped distance cochain. -/
def CochainBound (M : Metric V) (B : ℕ) : Prop :=
  ∀ (o a x : V) (T : ℕ) (p : Path M x x),
    |p.integral (M.form o a T)| ≤ (B:ℤ)*p.length

/-- A geodesic arc through `o`, closed by a short bypass outside the open T-ball. -/
def ShortBypass (M : Metric V) (T : ℕ) (o : V) (K : ℕ) : Prop :=
  ∃ (a b : V) (p : Path M a b) (q : Path M b a),
    p.Geodesic ∧ p.Mem o ∧ (∀ x, q.Mem x → T ≤ M.dist o x) ∧
      p.length+q.length ≤ K

theorem shortBypass_quadratic {B T K : ℕ} {o : V}
    (hB : CochainBound M B) (h : ShortBypass M T o K) :
    ((T/2:ℕ):ℤ)^2 ≤ (B:ℤ)*K := by
  obtain ⟨a,b,p,q,hp,⟨t,ht,rfl⟩,hfar,hK⟩ := h
  have h₁ := p.integral_form_quadratic hp ht (hfar b q.start_mem)
  have h₂ := hB (p.point t) a a T (p.append q)
  rw [p.integral_append,q.integral_form_zero hfar,add_zero] at h₂
  have h₃ := le_abs_self (p.integral (M.form (p.point t) a T))
  have hlen : ((p.append q).length:ℤ) ≤ K := by exact_mod_cast hK
  have hmul := mul_le_mul_of_nonneg_left hlen (Nat.cast_nonneg B : (0:ℤ) ≤ B)
  omega

end Release075.Discrete

end OAI
end
end

section
section
namespace OAI

namespace Release075.Discrete
variable {V : Type} {M : Metric V}

def GeodesicSpace (M : Metric V) : Prop := ∀ a b, ∃ p : Path M a b, p.Geodesic

noncomputable def shortPath (h : GeodesicSpace M) (a b : V) : Path M a b := (h a b).choose

theorem shortPath_geodesic (h : GeodesicSpace M) (a b : V) : (shortPath h a b).Geodesic :=
  (h a b).choose_spec

@[simp] theorem shortPath_length (h : GeodesicSpace M) (a b : V) :
    (shortPath h a b).length = M.dist a b := shortPath_geodesic h a b

namespace Path
variable {a b c : V}

def Outside (p : Path M a b) (o : V) (T : ℕ) : Prop := ∀ x, p.Mem x → T ≤ M.dist o x

theorem Outside.append {p : Path M a b} {q : Path M b c} {o : V} {T : ℕ}
    (hp : p.Outside o T) (hq : q.Outside o T) : (p.append q).Outside o T := by
  intro x hx
  rcases (p.mem_append_iff q x).mp hx with hx | hx
  · exact hp x hx
  · exact hq x hx

theorem Outside.reverse {p : Path M a b} {o : V} {T : ℕ}
    (hp : p.Outside o T) : p.reverse.Outside o T := by
  intro x hx
  exact hp x ((p.mem_reverse_iff x).mp hx)

theorem Outside.sub {p : Path M a b} {o : V} {T i j : ℕ}
    (hp : p.Outside o T) (hij : i ≤ j) (hj : j ≤ p.length) :
    (p.sub i j hij hj).Outside o T := by
  intro x hx
  exact hp x (p.mem_sub hij hj hx)

theorem outside_of_start (p : Path M a b) {o : V} {T : ℕ}
    (h : T+p.length ≤ M.dist o a) : p.Outside o T := by
  intro x hx
  have h₁ := p.dist_start_mem hx
  have h₂ := M.triangle o x a
  rw [M.symm x a] at h₂
  omega

theorem outside_of_end (p : Path M a b) {o : V} {T : ℕ}
    (h : T+p.length ≤ M.dist o b) : p.Outside o T := by
  intro x hx
  have h₁ := p.dist_end_mem hx
  have h₂ := M.triangle o x b
  rw [M.symm x b] at h₂
  omega

theorem triangle_lengths {p : Path M a b} {q : Path M b c} {s : Path M a c}
    (hp : p.Geodesic) (hq : q.Geodesic) (hs : s.Geodesic) :
    p.length ≤ q.length+s.length ∧ q.length ≤ p.length+s.length ∧
      s.length ≤ p.length+q.length := by
  have h₁ := M.triangle a c b
  have h₂ := M.triangle b a c
  have h₃ := M.triangle a b c
  rw [M.symm c b] at h₁
  rw [M.symm b a] at h₂
  change p.length = M.dist a b at hp
  change q.length = M.dist b c at hq
  change s.length = M.dist a c at hs
  omega

/-- Localization in a long arm of the comparison tripod. -/
theorem shortBypass_arm (hgeo : GeodesicSpace M)
    {p : Path M a b} {q : Path M b c} {s : Path M a c}
    (hp : p.Geodesic) (hq : q.Geodesic) (hs : s.Geodesic)
    {T R t : ℕ} (hR : 4*T+2 ≤ R) (ht : t ≤ p.length)
    (hthin : SideNear T p q s)
    (hfar : ∀ x, q.Mem x ∨ s.Mem x → T ≤ M.dist (p.point t) x)
    (harm : t+4*R < (p.length+s.length-q.length)/2) :
    ShortBypass M T (p.point t) (10*R) := by
  obtain ⟨hA,hB,hC⟩ := triangle_lengths hp hq hs
  let l := t-2*R
  let u := t+2*R
  have hlu : l ≤ u := by dsimp [l,u]; omega
  have huα : u ≤ (p.length+s.length-q.length)/2 := by dsimp [u]; omega
  have hlα : l ≤ (p.length+s.length-q.length)/2 := hlu.trans huα
  have huA : u ≤ p.length := by omega
  have huC : u ≤ s.length := by omega
  have hlt : l ≤ t := Nat.sub_le _ _
  have htu : t ≤ u := by dsimp [u]; omega
  let A := p.sub l u hlu huA
  let S := s.sub l u hlu huC
  let U := shortPath hgeo (p.point u) (s.point u)
  let L := shortPath hgeo (s.point l) (p.point l)
  have hU : U.length ≤ R := by
    rw [show U.length = M.dist (p.point u) (s.point u) from shortPath_length hgeo _ _]
    exact (synchronous hp hq hs hthin huα).trans hR
  have hL : L.length ≤ R := by
    rw [show L.length = M.dist (s.point l) (p.point l) from shortPath_length hgeo _ _,M.symm]
    exact (synchronous hp hq hs hthin hlα).trans hR
  have outU : U.Outside (p.point t) T := by
    apply U.outside_of_start
    rw [p.geodesic_dist_at hp htu huA]
    dsimp [u]
    omega
  have outL : L.Outside (p.point t) T := by
    apply L.outside_of_end
    by_cases hl : l = 0
    · have hL0 : L.length = 0 := by
        change (shortPath hgeo (s.point l) (p.point l)).length = 0
        rw [shortPath_length,hl,p.zero,s.zero,M.self]
      have h := hfar a (Or.inr s.start_mem)
      simpa only [hL0,Nat.add_zero,hl,p.zero] using h
    · rw [M.symm (p.point t) (p.point l),p.geodesic_dist_at hp hlt ht]
      dsimp [l] at *
      omega
  have outS : S.reverse.Outside (p.point t) T := by
    apply Outside.reverse
    exact (show s.Outside (p.point t) T from fun x hx => hfar x (Or.inr hx)).sub hlu huC
  refine ⟨p.point l,p.point u,A,(U.append S.reverse).append L,
    p.geodesic_sub hp hlu huA,?_,(outU.append outS).append outL,?_⟩
  · refine ⟨t-l,?_,?_⟩
    · change t-l ≤ u-l
      omega
    · rw [show A.point (t-l) = p.point (l+(t-l)) from p.sub_at hlu huA (by omega)]
      rw [Nat.add_sub_of_le hlt]
  · change (u-l)+(U.length+(u-l)+L.length) ≤ 10*R
    dsimp [u,l]
    omega

/-- Localization near the three-pronged center of the comparison tripod. -/
theorem shortBypass_center (hgeo : GeodesicSpace M)
    {p : Path M a b} {q : Path M b c} {s : Path M a c}
    (hp : p.Geodesic) (hq : q.Geodesic) (hs : s.Geodesic)
    {T R t : ℕ} (hR : 4*T+2 ≤ R) (ht : t ≤ p.length)
    (hthin : TriangleNear T p q s)
    (hfar : ∀ x, q.Mem x ∨ s.Mem x → T ≤ M.dist (p.point t) x)
    (hcenter₁ : (p.length+s.length-q.length)/2 ≤ t+4*R)
    (hcenter₂ : (p.length+q.length-s.length)/2 ≤ p.length-t+4*R) :
    ShortBypass M T (p.point t) (60*R) := by
  obtain ⟨hA,hB,hC⟩ := triangle_lengths hp hq hs
  let α := (p.length+s.length-q.length)/2
  let β := (p.length+q.length-s.length)/2
  let γ := (q.length+s.length-p.length)/2
  have hcoords : α+β ≤ p.length ∧ p.length ≤ α+β+1 ∧
      β+γ ≤ q.length ∧ q.length ≤ β+γ+1 ∧
      α+γ ≤ s.length ∧ s.length ≤ α+γ+1 := by
    dsimp [α,β,γ]
    omega
  change α ≤ t+4*R at hcenter₁
  change β ≤ p.length-t+4*R at hcenter₂
  let x := α-8*R
  let y := β-8*R
  let z := γ-8*R
  have hxα : x ≤ α := Nat.sub_le _ _
  have hyβ : y ≤ β := Nat.sub_le _ _
  have hzγ : z ≤ γ := Nat.sub_le _ _
  have hxt : x ≤ t := by dsimp [x]; omega
  have hty : t ≤ p.length-y := by dsimp [y]; omega
  have hxp : x ≤ p.length-y := hxt.trans hty
  have hyp : p.length-y ≤ p.length := Nat.sub_le _ _
  have hyq : y ≤ q.length-z := by omega
  have hzq : q.length-z ≤ q.length := Nat.sub_le _ _
  have hxs : x ≤ s.length-z := by omega
  have hzs : s.length-z ≤ s.length := Nat.sub_le _ _
  let P := p.sub x (p.length-y) hxp hyp
  let Q := q.sub y (q.length-z) hyq hzq
  let S := s.sub x (s.length-z) hxs hzs
  let X := shortPath hgeo (s.point x) (p.point x)
  let Y := shortPath hgeo (p.point (p.length-y)) (q.point y)
  let Z := shortPath hgeo (q.point (q.length-z)) (s.point (s.length-z))
  have hX : X.length ≤ R := by
    rw [show X.length = M.dist (s.point x) (p.point x) from shortPath_length hgeo _ _,M.symm]
    exact (synchronous hp hq hs hthin.1 hxα).trans hR
  have hY : Y.length ≤ R := by
    have hn : SideNear T p.reverse s q := (hthin.1.reverse T).swap T
    have hd := synchronous (p.geodesic_reverse hp) hs hq hn hyβ
    change M.dist (p.point (p.length-y)) (q.point y) ≤ 4*T+2 at hd
    rw [show Y.length = M.dist (p.point (p.length-y)) (q.point y) from shortPath_length hgeo _ _]
    exact hd.trans hR
  have hZ : Z.length ≤ R := by
    have hn : SideNear T q.reverse p.reverse s.reverse :=
      (((hthin.2.1.swap T).reverse_left T).reverse_right T).reverse T
    have hd := synchronous (q.geodesic_reverse hq) (p.geodesic_reverse hp)
      (s.geodesic_reverse hs) hn hzγ
    change M.dist (q.point (q.length-z)) (s.point (s.length-z)) ≤ 4*T+2 at hd
    rw [show Z.length = M.dist (q.point (q.length-z)) (s.point (s.length-z))
      from shortPath_length hgeo _ _]
    exact hd.trans hR
  have outX : X.Outside (p.point t) T := by
    apply X.outside_of_end
    by_cases hx : x = 0
    · have hl : X.length = 0 := by
        change (shortPath hgeo (s.point x) (p.point x)).length = 0
        rw [shortPath_length,hx,p.zero,s.zero,M.self]
      have hf := hfar a (Or.inr s.start_mem)
      simpa only [hl,Nat.add_zero,hx,p.zero] using hf
    · rw [M.symm (p.point t) (p.point x),p.geodesic_dist_at hp hxt ht]
      dsimp [x] at *
      omega
  have outY : Y.Outside (p.point t) T := by
    apply Y.outside_of_start
    by_cases hy : y = 0
    · have hl : Y.length = 0 := by
        change (shortPath hgeo (p.point (p.length-y)) (q.point y)).length = 0
        rw [shortPath_length,hy,Nat.sub_zero,p.last,q.zero,M.self]
      have hf := hfar b (Or.inl q.start_mem)
      simpa only [hl,Nat.add_zero,hy,Nat.sub_zero,p.last] using hf
    · rw [p.geodesic_dist_at hp hty hyp]
      dsimp [y] at *
      omega
  have outZ : Z.Outside (p.point t) T := by
    apply Z.outside_of_start
    by_cases hz : z = 0
    · have hl : Z.length = 0 := by
        change (shortPath hgeo (q.point (q.length-z)) (s.point (s.length-z))).length = 0
        simp only [shortPath_length,hz,Nat.sub_zero,q.last,s.last,M.self]
      have hf := hfar c (Or.inl q.end_mem)
      simpa only [hl,Nat.add_zero,hz,Nat.sub_zero,q.last] using hf
    · have ha := M.triangle a (p.point t) c
      rw [p.geodesic_start_dist hp ht] at ha
      have hc := M.triangle (p.point t) (q.point (q.length-z)) c
      rw [q.geodesic_end_dist hq hzq] at hc
      have hzz : z ≤ q.length := by omega
      rw [Nat.sub_sub_self hzz] at hc
      change s.length = M.dist a c at hs
      dsimp [z] at *
      omega
  have outQ : Q.Outside (p.point t) T :=
    (show q.Outside (p.point t) T from fun v hv => hfar v (Or.inl hv)).sub hyq hzq
  have outS : S.reverse.Outside (p.point t) T :=
    ((show s.Outside (p.point t) T from fun v hv => hfar v (Or.inr hv)).sub hxs hzs).reverse
  refine ⟨p.point x,p.point (p.length-y),P,(((Y.append Q).append Z).append S.reverse).append X,
    p.geodesic_sub hp hxp hyp,?_,(((outY.append outQ).append outZ).append outS).append outX,?_⟩
  · refine ⟨t-x,?_,?_⟩
    · change t-x ≤ p.length-y-x
      omega
    · rw [show P.point (t-x) = p.point (x+(t-x)) from p.sub_at hxp hyp (by omega)]
      rw [Nat.add_sub_of_le hxt]
  · change (p.length-y-x)+(Y.length+(q.length-z-y)+Z.length+(s.length-z-x)+X.length) ≤ 60*R
    dsimp [x,y,z] at *
    omega

/-- A maximally fat point of a T-thin triangle has a bypass of length at most 1000(T+1). -/
theorem shortBypass_triangle (hgeo : GeodesicSpace M)
    {p : Path M a b} {q : Path M b c} {s : Path M a c}
    (hp : p.Geodesic) (hq : q.Geodesic) (hs : s.Geodesic)
    {T : ℕ} (hthin : TriangleNear T p q s) {o : V} (ho : p.Mem o)
    (hfar : ∀ x, q.Mem x ∨ s.Mem x → T ≤ M.dist o x) :
    ShortBypass M T o (1000*(T+1)) := by
  obtain ⟨t,ht,rfl⟩ := ho
  let R := 4*T+4
  have hR : 4*T+2 ≤ R := by dsimp [R]; omega
  have enlarge {K : ℕ} (hK : K ≤ 1000*(T+1))
      (h : ShortBypass M T (p.point t) K) : ShortBypass M T (p.point t) (1000*(T+1)) := by
    obtain ⟨a,b,A,Q,hA,ho,hfar,hlen⟩ := h
    exact ⟨a,b,A,Q,hA,ho,hfar,hlen.trans hK⟩
  by_cases hleft : t+4*R < (p.length+s.length-q.length)/2
  · apply enlarge (K:=10*R) (by dsimp [R]; omega)
    exact shortBypass_arm hgeo hp hq hs hR ht hthin.1 hfar hleft
  by_cases hright : p.length-t+4*R < (p.length+q.length-s.length)/2
  · have hn : SideNear T p.reverse s q := (hthin.1.reverse T).swap T
    have hr := shortBypass_arm hgeo (p.geodesic_reverse hp) hs hq hR
      (t:=p.length-t) (Nat.sub_le _ _) hn
      (fun x hx => by
        change T ≤ M.dist (p.point (p.length-(p.length-t))) x
        rw [Nat.sub_sub_self ht]
        exact hfar x hx.symm) hright
    change ShortBypass M T (p.point (p.length-(p.length-t))) (10*R) at hr
    rw [Nat.sub_sub_self ht] at hr
    exact enlarge (by dsimp [R]; omega) hr
  · apply enlarge (K:=60*R) (by dsimp [R]; omega)
    exact shortBypass_center hgeo hp hq hs hR ht hthin hfar (by omega) (by omega)

end Path

theorem quadratic_bound {B T : ℕ}
    (h : ((T/2:ℕ):ℤ)^2 ≤ (B:ℤ)*(1000*(T+1))) : T ≤ 10000*(B+1) := by
  by_contra hn
  let k := T/2
  have hk : T ≤ 2*k+1 := by dsimp [k]; omega
  have hkT : k ≤ T := Nat.div_le_self _ _
  have hT : (8000:ℤ)*B+10000 ≤ T := by omega
  have hm := mul_nonneg (sub_nonneg.mpr hT) (show (0:ℤ) ≤ (T:ℤ)+1 by omega)
  have hs : (T:ℤ)^2 ≤ (2*(k:ℤ)+1)^2 := by
    apply sq_le_sq₀ (by positivity) (by positivity) |>.mpr
    exact_mod_cast hk
  change (k:ℤ)^2 ≤ (B:ℤ)*(1000*(T+1)) at h
  have hkt : (k:ℤ) ≤ T := by exact_mod_cast hkT
  nlinarith

namespace Path
variable {a b c : V}

theorem SideNear.mono {T U : ℕ} {p : Path M a b} {q : Path M b c} {s : Path M a c}
    (h : SideNear T p q s) (hTU : T ≤ U) : SideNear U p q s := by
  intro x hx
  obtain ⟨y,hy,hd⟩ := h x hx
  exact ⟨y,hy,hd.trans hTU⟩

theorem sideNear_shrink (hgeo : GeodesicSpace M) {B T : ℕ}
    (hB : CochainBound M B) (hlarge : 10000*(B+1) < T)
    {p : Path M a b} {q : Path M b c} {s : Path M a c}
    (hp : p.Geodesic) (hq : q.Geodesic) (hs : s.Geodesic)
    (hthin : TriangleNear T p q s) : SideNear (T-1) p q s := by
  classical
  intro o ho
  by_contra hn
  have hfar : ∀ x, q.Mem x ∨ s.Mem x → T ≤ M.dist o x := by
    intro x hx
    have hnot : ¬ M.dist o x ≤ T-1 := fun h => hn ⟨x,hx,h⟩
    omega
  have hb := shortBypass_triangle hgeo hp hq hs hthin ho hfar
  have hh := quadratic_bound (shortBypass_quadratic hB hb)
  omega

theorem triangleNear_shrink (hgeo : GeodesicSpace M) {B T : ℕ}
    (hB : CochainBound M B) (hlarge : 10000*(B+1) < T)
    {p : Path M a b} {q : Path M b c} {s : Path M a c}
    (hp : p.Geodesic) (hq : q.Geodesic) (hs : s.Geodesic)
    (hthin : TriangleNear T p q s) : TriangleNear (T-1) p q s := by
  refine ⟨sideNear_shrink hgeo hB hlarge hp hq hs hthin,?_,?_⟩
  · have hn : TriangleNear T q s.reverse p.reverse :=
      ⟨(hthin.2.1.reverse_left T).reverse_right T,
        (hthin.2.2.reverse T).reverse_left T,
        (hthin.1.reverse T).reverse_right T⟩
    have hh := sideNear_shrink hgeo hB hlarge hq (s.geodesic_reverse hs)
      (p.geodesic_reverse hp) hn
    intro x hx
    obtain ⟨y,hy,hd⟩ := hh x hx
    exact ⟨y,hy.imp ((s.mem_reverse_iff y).mp) ((p.mem_reverse_iff y).mp),hd⟩
  · have hn : TriangleNear T s q.reverse p :=
      ⟨(hthin.2.2.swap T).reverse_left T,
        (hthin.2.1.swap T).reverse T,
        (hthin.1.swap T).reverse_right T⟩
    have hh := sideNear_shrink hgeo hB hlarge hs (q.geodesic_reverse hq) hp hn
    intro x hx
    obtain ⟨y,hy,hd⟩ := hh x hx
    exact ⟨y,(hy.imp ((q.mem_reverse_iff y).mp) id).symm,hd⟩

/-- Discrete linear filling implies genuine uniform thinness of geodesic triangles. -/
theorem triangleNear_of_cochainBound (hgeo : GeodesicSpace M) {B : ℕ}
    (hB : CochainBound M B) {p : Path M a b} {q : Path M b c} {s : Path M a c}
    (hp : p.Geodesic) (hq : q.Geodesic) (hs : s.Geodesic) :
    TriangleNear (10000*(B+1)) p q s := by
  classical
  have hex : ∃ T, TriangleNear T p q s := by
    refine ⟨p.length+q.length+s.length,?_,?_,?_⟩
    · intro x hx
      refine ⟨a,Or.inr s.start_mem,?_⟩
      rw [M.symm]
      exact (p.dist_start_mem hx).trans (by omega)
    · intro x hx
      refine ⟨b,Or.inr p.end_mem,?_⟩
      rw [M.symm]
      exact (q.dist_start_mem hx).trans (by omega)
    · intro x hx
      refine ⟨a,Or.inl p.start_mem,?_⟩
      rw [M.symm]
      exact (s.dist_start_mem hx).trans (by omega)
  let T := Nat.find hex
  have hthin : TriangleNear T p q s := Nat.find_spec hex
  have hT : T ≤ 10000*(B+1) := by
    by_contra hn
    have hshrink := triangleNear_shrink hgeo hB (by omega : 10000*(B+1) < T) hp hq hs hthin
    have hf := Nat.find_min' hex hshrink
    change T ≤ T-1 at hf
    omega
  exact ⟨hthin.1.mono hT,by
    intro x hx
    obtain ⟨y,hy,hd⟩ := hthin.2.1 x hx
    exact ⟨y,hy,hd.trans hT⟩,by
    intro x hx
    obtain ⟨y,hy,hd⟩ := hthin.2.2 x hx
    exact ⟨y,hy,hd.trans hT⟩⟩

end Path
end Release075.Discrete

end OAI
end
end

section
section
namespace OAI

namespace Release075.Discrete
variable {V : Type} (X : SimpleGraph V) (hX : X.Connected)

noncomputable def graphMetric : Metric V where
  dist := X.dist
  self _ := X.dist_self
  symm _ _ := X.dist_comm
  triangle _ _ _ := hX.dist_triangle

noncomputable def walkPath {a b : V} (p : X.Walk a b) : Path (graphMetric X hX) a b where
  length := p.length
  point := p.getVert
  zero := p.getVert_zero
  stable _ h := p.getVert_of_length_le h
  step _ h := by
    change X.dist _ _ ≤ 1
    exact (X.dist_eq_one_iff_adj.mpr (p.adj_getVert_succ h)).le

@[simp] theorem walkPath_mem {a b x : V} (p : X.Walk a b) :
    (walkPath X hX p).Mem x ↔ x ∈ p.support := by
  classical
  constructor
  · rintro ⟨i,_,rfl⟩
    exact p.getVert_mem_support i
  · intro hx
    obtain ⟨i,hi,he⟩ := List.mem_iff_getElem.mp hx
    refine ⟨i,by change i ≤ p.length; rw [p.length_support] at hi; omega,?_⟩
    exact (p.getVert_eq_support_getElem (by rw [p.length_support] at hi; omega)).trans he

theorem graphMetric_geodesicSpace : GeodesicSpace (graphMetric X hX) := by
  intro a b
  obtain ⟨p,hp⟩ := hX.exists_walk_length_eq_dist a b
  exact ⟨walkPath X hX p,hp⟩

end Release075.Discrete

namespace Release075.BlockPresentation
variable {I B : Type} {r : ℕ} (d : BlockPresentation I B r)

abbrev cayley : SimpleGraph d.GroupType := SimpleGraph.mulCayley (Set.range d.edge)
noncomputable abbrev cayleyMetric : Discrete.Metric d.GroupType :=
  Discrete.graphMetric d.cayley d.cayley_connected

theorem cayley_dist_mul (g : d.GroupType) (e : d.OrientedEdge) :
    d.cayleyMetric.dist g (g*d.edgeValue e) ≤ 1 := by
  by_cases he : g = g*d.edgeValue e
  · rw [←he]
    exact (d.cayleyMetric.self g).le.trans (by omega)
  · suffices d.cayley.Adj g (g*d.edgeValue e) by
      exact (d.cayley.dist_eq_one_iff_adj.mpr this).le
    apply (SimpleGraph.mulCayley_adj' _ _ _).mpr
    refine ⟨he,d.edge e.1,⟨e.1,rfl⟩,?_⟩
    rcases e with ⟨e,s⟩
    cases s
    · right
      simp [edgeValue]
    · left
      simp [edgeValue]

theorem cayley_dist_liftedEdge (e : d.LiftedEdge) :
    d.cayleyMetric.dist (d.liftedFlip e).2 e.2 ≤ 1 := by
  have h := d.cayley_dist_mul (e.2*(d.edgeValue e.1)⁻¹) e.1
  simpa only [inv_mul_cancel_right,liftedFlip] using h

noncomputable def liftedForm (o a : d.GroupType) (T : ℕ) (e : d.LiftedEdge) : ℤ :=
  d.cayleyMetric.form o a T (d.liftedFlip e).2 e.2

theorem liftedForm_flip (o a : d.GroupType) (T : ℕ) (e : d.LiftedEdge) :
    d.liftedForm o a T (d.liftedFlip e) = -d.liftedForm o a T e := by
  rw [liftedForm,d.liftedFlip_flip,Discrete.Metric.form_flip]
  rfl

theorem liftedForm_face_bound (o z : d.GroupType) (T : ℕ)
    {a b c : d.LiftedEdge} (hf : d.LiftedFace a b c) :
    |d.liftedForm o z T a+d.liftedForm o z T b+d.liftedForm o z T c| ≤ 2 := by
  have hab := congrArg Prod.snd hf.2.1
  have hbc := congrArg Prod.snd hf.2.2.1
  have hca := congrArg Prod.snd hf.2.2.2
  change (d.liftedFlip b).2 = a.2 at hab
  change (d.liftedFlip c).2 = b.2 at hbc
  change (d.liftedFlip a).2 = c.2 at hca
  have ha := d.cayley_dist_liftedEdge a
  have hb := d.cayley_dist_liftedEdge b
  have hc := d.cayley_dist_liftedEdge c
  rw [hca] at ha
  rw [hab] at hb
  rw [hbc] at hc
  simpa only [liftedForm,hab,hbc,hca] using
    d.cayleyMetric.form_triangle_bound o z c.2 a.2 b.2 T ha hb hc

end Release075.BlockPresentation

namespace Release075.TriangleFilling
variable {E V : Type} {flip : E → E} {color : E → V} {face : E → E → E → Prop}

/-- Bounded triangular coboundary gives a bound on every actual disk boundary. -/
theorem edge_sum_bound {w : List E} (D : TriangleFilling flip color face w)
    (F : E → ℤ) (hflip : ∀ e, F (flip e) = -F e)
    (hface : ∀ a b c, face a b c → |F a+F b+F c| ≤ 2) :
    |(w.map F).sum| ≤ 2*D.activeCount := by
  classical
  have hcyc := D.full.trace_cyclic_sum (fun a ha => (D.full_triangular a ha).1)
    (fun a _ _ => F a)
  rw [D.full.trace_edge F hflip] at hcyc
  have hcard : Fintype.card D.full.Dart = D.activeCount := Fintype.card_subtype _
  have hbound : |D.full.trace (fun a b c => F a+F b+F c)| ≤ 2*D.activeCount := by
    unfold FullFilling.trace
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    calc
      _ ≤ ∑ _a : D.full.Dart, (2:ℤ) := by
        apply Finset.sum_le_sum
        intro a _
        split_ifs with ha
        · norm_num
        · exact hface _ _ _ (D.full_triangular a ha).2.2
      _ = 2*D.activeCount := by simp only [Finset.sum_const,Finset.card_univ,hcard,nsmul_eq_mul]; ring
  rw [hcyc] at hbound
  norm_num only [nsmul_eq_mul,abs_mul,abs_neg] at hbound
  have hn := abs_nonneg ((w.map F).sum)
  omega

end Release075.TriangleFilling

namespace Release075.MarkedLineData
variable {q r : ℕ} [Fact q.Prime] (d : MarkedLineData q r) (hr : 0 < r)

theorem liftedForm_loop_bound {x : (d.presentation hr).LiftedVertex}
    {w : List (d.presentation hr).LiftedEdge}
    (hw : WordPath (d.presentation hr).liftedFlip (d.presentation hr).liftedTarget x x w)
    (o a : (d.presentation hr).GroupType) (T : ℕ) :
    |(w.map ((d.presentation hr).liftedForm o a T)).sum| ≤ 38*w.length := by
  obtain ⟨D,hD⟩ := d.exists_lifted_linear_filling hr ((d.presentation hr).lifted_closed_fillable hw)
  have h := D.edge_sum_bound ((d.presentation hr).liftedForm o a T)
    ((d.presentation hr).liftedForm_flip o a T)
    (fun _ _ _ hf => (d.presentation hr).liftedForm_face_bound o a T hf)
  omega

end Release075.MarkedLineData

end OAI
end
end

section
section
namespace OAI

namespace Release075.BlockPresentation
variable {I B : Type} {r : ℕ} (d : BlockPresentation I B r)

/-- The original edge is based using the fixed two-edge spanning tree. -/
def generatorWord : d.Edge → List d.OrientedEdge
  | .inl e => [(d.treeL,true),(.inl e,true),(d.treeR,false)]
  | .inr (.inl e) => [(.inr (.inl e),true),(d.treeL,false)]
  | .inr (.inr e) => [(.inr (.inr e),true),(d.treeR,false)]

theorem generatorWord_typed (e : d.Edge) :
    WordPath d.flipEdge d.edgeTarget .o .o (d.generatorWord e) := by
  rcases e with e | e | e
  · exact WordPath.cons (flip:=d.flipEdge) (color:=d.edgeTarget) (d.treeL,true)
      (WordPath.cons (flip:=d.flipEdge) (color:=d.edgeTarget) (Sum.inl e,true)
        (WordPath.cons (flip:=d.flipEdge) (color:=d.edgeTarget) (d.treeR,false) (WordPath.nil Vertex.o)))
  · exact WordPath.cons (flip:=d.flipEdge) (color:=d.edgeTarget)
      (.inr (.inl e),true) (WordPath.cons (flip:=d.flipEdge) (color:=d.edgeTarget) (d.treeL,false) (WordPath.nil Vertex.o))
  · exact WordPath.cons (flip:=d.flipEdge) (color:=d.edgeTarget)
      (.inr (.inr e),true) (WordPath.cons (flip:=d.flipEdge) (color:=d.edgeTarget) (d.treeR,false) (WordPath.nil Vertex.o))

@[simp] theorem generatorWord_value (e : d.Edge) : d.wordValue (d.generatorWord e) = d.edge e := by
  rcases e with e | e | e <;>
    simp [generatorWord,edgeValue,d.treeL_eq_one,d.treeR_eq_one]

theorem generatorWord_length (e : d.Edge) : (d.generatorWord e).length ≤ 3 := by
  rcases e with e | e | e <;> simp [generatorWord]

/-- Collapsed tree edges have zero integral, leaving precisely the Cayley edge. -/
theorem generatorWord_integral (e : d.Edge) (g o a : d.GroupType) (T : ℕ) :
    ((d.liftWord g (d.generatorWord e)).map (d.liftedForm o a T)).sum =
      d.cayleyMetric.form o a T g (g*d.edge e) := by
  rcases e with e | e | e <;>
    simp [generatorWord,liftWord,liftedForm,liftedFlip,edgeValue,
      d.treeL_eq_one,d.treeR_eq_one,Discrete.Metric.form_self]

theorem liftedForm_reverse (w : List d.LiftedEdge) (o a : d.GroupType) (T : ℕ) :
    ((reverseWord d.liftedFlip w).map (d.liftedForm o a T)).sum =
      -(w.map (d.liftedForm o a T)).sum := by
  induction w with
  | nil => simp
  | cons e w ih =>
    rw [reverseWord_cons,List.map_append,List.sum_append,ih]
    simp only [d.liftedForm_flip,List.map_cons,List.sum_cons]
    abel

theorem exists_generator_step (g : d.GroupType) (e : d.Edge) :
    ∃ w : List d.LiftedEdge,
      WordPath d.liftedFlip d.liftedTarget (.o,g) (.o,g*d.edge e) w ∧
      w.length ≤ 3 ∧ ∀ (o a : d.GroupType) (T : ℕ),
        (w.map (d.liftedForm o a T)).sum = d.cayleyMetric.form o a T g (g*d.edge e) := by
  refine ⟨d.liftWord g (d.generatorWord e),?_,?_,d.generatorWord_integral e g⟩
  · simpa only [generatorWord_value] using d.liftWord_typed (d.generatorWord_typed e) g
  · simpa only [liftWord_length] using d.generatorWord_length e

theorem exists_cayley_step {g h : d.GroupType} (hgh : d.cayleyMetric.dist g h ≤ 1) :
    ∃ w : List d.LiftedEdge,
      WordPath d.liftedFlip d.liftedTarget (.o,g) (.o,h) w ∧
      w.length ≤ 3 ∧ ∀ (o a : d.GroupType) (T : ℕ),
        (w.map (d.liftedForm o a T)).sum = d.cayleyMetric.form o a T g h := by
  by_cases he : g = h
  · subst h
    exact ⟨[],.nil _,by simp,fun o a T => by simp [Discrete.Metric.form_self]⟩
  have hadj : d.cayley.Adj g h := by
    apply d.cayley.dist_eq_one_iff_adj.mp
    have hpos := d.cayley_connected.pos_dist_of_ne he
    change d.cayley.dist g h ≤ 1 at hgh
    exact Nat.le_antisymm hgh hpos
  obtain ⟨_,v,⟨e,rfl⟩,he|he⟩ := (SimpleGraph.mulCayley_adj' _ _ _).mp hadj
  · subst h
    exact d.exists_generator_step g e
  · subst g
    obtain ⟨w,hw,hlen,hwF⟩ := d.exists_generator_step h e
    refine ⟨reverseWord d.liftedFlip w,hw.reverse d.liftedFlip_flip,?_,?_⟩
    · simpa only [reverseWord,List.length_map,List.length_reverse] using hlen
    · intro o a T
      rw [d.liftedForm_reverse,hwF,d.cayleyMetric.form_flip,neg_neg]

theorem exists_path_word {g h : d.GroupType} (p : Discrete.Path d.cayleyMetric g h) :
    ∃ w : List d.LiftedEdge,
      WordPath d.liftedFlip d.liftedTarget (.o,g) (.o,h) w ∧
      w.length ≤ 3*p.length ∧ ∀ (o a : d.GroupType) (T : ℕ),
        (w.map (d.liftedForm o a T)).sum = p.integral (d.cayleyMetric.form o a T) := by
  have hprefix : ∀ n, n ≤ p.length → ∃ w : List d.LiftedEdge,
      WordPath d.liftedFlip d.liftedTarget (.o,p.point 0) (.o,p.point n) w ∧
      w.length ≤ 3*n ∧ ∀ (o a : d.GroupType) (T : ℕ),
        (w.map (d.liftedForm o a T)).sum =
          ∑ i ∈ Finset.range n, d.cayleyMetric.form o a T (p.point i) (p.point (i+1)) := by
    intro n
    induction n with
    | zero =>
      intro _
      exact ⟨[],.nil _,by simp,fun o a T => by simp⟩
    | succ n ih =>
      intro hn
      obtain ⟨u,hu,hulen,huF⟩ := ih (by omega)
      obtain ⟨v,hv, hvlen,hvF⟩ := d.exists_cayley_step (p.step n (by omega))
      refine ⟨u++v,hu.append hv,?_,?_⟩
      · rw [List.length_append]
        omega
      · intro o a T
        rw [List.map_append,List.sum_append,huF,hvF,Finset.sum_range_succ]
  obtain ⟨w,hw,hlen,hF⟩ := hprefix p.length le_rfl
  exact ⟨w,by simpa only [p.zero,p.last] using hw,hlen,hF⟩

end Release075.BlockPresentation

end OAI
end
end

section
section
namespace OAI

namespace Release075.MarkedLineData
variable {q r : ℕ} [Fact q.Prime] (d : MarkedLineData q r) (hr : 0 < r)

/-- Honest linear filling estimate on *all* lazy Cayley loops, not just original edges. -/
theorem presentation_cochainBound : Discrete.CochainBound (d.presentation hr).cayleyMetric 114 := by
  intro o a x T p
  obtain ⟨w,hw,hlen,hF⟩ := (d.presentation hr).exists_path_word p
  have h := d.liftedForm_loop_bound hr hw o a T
  rw [hF] at h
  have hlen' : (w.length:ℤ) ≤ 3*p.length := by exact_mod_cast hlen
  omega

/-- The constructed finite presentation is word hyperbolic in the literal thin-triangle sense. -/
theorem presentation_wordHyperbolic : WordHyperbolic (d.presentation hr).GroupType := by
  let P := d.presentation hr
  refine ⟨Set.range P.edge,P.generators_finite,P.cayley_connected,10000*(114+1),?_⟩
  intro x y z p q s hp hq hs
  let p' := Discrete.walkPath P.cayley P.cayley_connected p
  let q' := Discrete.walkPath P.cayley P.cayley_connected q
  let s' := Discrete.walkPath P.cayley P.cayley_connected s.reverse
  have hp' : p'.Geodesic := hp
  have hq' : q'.Geodesic := hq
  have hs' : s'.Geodesic := by
    change s.reverse.length = P.cayley.dist x z
    rw [SimpleGraph.Walk.length_reverse,P.cayley.dist_comm]
    exact hs
  have hthin := Discrete.Path.triangleNear_of_cochainBound
    (Discrete.graphMetric_geodesicSpace P.cayley P.cayley_connected)
    (d.presentation_cochainBound hr) hp' hq' hs'
  have hpMem (v : P.GroupType) : p'.Mem v ↔ v ∈ p.support :=
    Discrete.walkPath_mem P.cayley P.cayley_connected p
  have hqMem (v : P.GroupType) : q'.Mem v ↔ v ∈ q.support :=
    Discrete.walkPath_mem P.cayley P.cayley_connected q
  have hsMem (v : P.GroupType) : s'.Mem v ↔ v ∈ s.support := by
    rw [Discrete.walkPath_mem,SimpleGraph.Walk.support_reverse,List.mem_reverse]
  refine ⟨?_,?_,?_⟩
  · intro v hv
    obtain ⟨w,hw,hd⟩ := hthin.1 v ((hpMem v).mpr hv)
    exact ⟨w,hw.imp ((hqMem w).mp) ((hsMem w).mp),hd⟩
  · intro v hv
    obtain ⟨w,hw,hd⟩ := hthin.2.1 v ((hqMem v).mpr hv)
    exact ⟨w,hw.imp ((hsMem w).mp) ((hpMem w).mp),hd⟩
  · intro v hv
    obtain ⟨w,hw,hd⟩ := hthin.2.2 v ((hsMem v).mpr hv)
    exact ⟨w,hw.imp ((hpMem w).mp) ((hqMem w).mp),hd⟩

end Release075.MarkedLineData

end OAI
end
end

section
section
namespace OAI

namespace Release075

theorem main_oai : ∃ (G : Type) (_ : Group G),
    TorsionFree G ∧ WordHyperbolic G ∧ ¬ Group.ResiduallyFinite G := by
  obtain ⟨q,r,hq,hr,hrq,hrb,⟨d⟩⟩ := exists_markedLineData
  let : Fact q.Prime := ⟨hq⟩
  have hq200 : 200 ≤ q := by
    have hb : 200 ≤ 100*100^20 := by norm_num
    omega
  exact ⟨(d.presentation hr).GroupType, inferInstance,
    d.presentation_torsionFree hr, d.presentation_wordHyperbolic hr,
    d.actual_presentation_not_residuallyFinite hr hrq hq200⟩

end Release075

end OAI
end
end

theorem solution : type_of% @OAI.Release075.main_oai := @OAI.Release075.main_oai
