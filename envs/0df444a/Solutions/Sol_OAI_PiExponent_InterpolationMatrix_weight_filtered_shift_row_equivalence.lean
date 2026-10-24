-- Prove2me | solution 1 for OAI.PiExponent.InterpolationMatrix.weight_filtered_shift_row_equivalence
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T05:54:26.246597+00:00
-- url     : https://prove2.me/submissions/c2a53b01-eeef-4a0b-a67e-c198933e800f

import Definitions.Def_PiExponent_FiniteMinorComparison
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
open OAI.PiExponent
open scoped BigOperators

namespace S105WF
open MvPolynomial

variable {m : ℕ}

/-- the coefficient polynomial of the shift -/
noncomputable def D (Δ : Fin m → Polynomial ℂ) (b b' : Fin m → ℕ) : Polynomial ℂ :=
  ∏ i, ((b' i).choose (b i) : Polynomial ℂ) * Δ i ^ (b' i - b i)

lemma coeff_prod_shift (Δ : Fin m → Polynomial ℂ) (b' : Fin m → ℕ) (A : Fin m →₀ ℕ) :
    MvPolynomial.coeff A (∏ i : Fin m, (X i + C (Δ i)) ^ b' i : MvPolynomial (Fin m) (Polynomial ℂ)) =
      D Δ (⇑A) b' := by
  classical
  set g : Fin m → ℕ → Polynomial ℂ := fun i k => Δ i ^ (b' i - k) * ((b' i).choose k : Polynomial ℂ)
  have h1 : ∀ i, (X i + C (Δ i) : MvPolynomial (Fin m) (Polynomial ℂ)) ^ (b' i) =
      ∑ k ∈ Finset.range (b' i + 1), monomial (Finsupp.single i k) (g i k) := by
    intro i
    rw [add_pow]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [g, X_pow_eq_monomial, ← C_pow]
    rw [← map_natCast (C : Polynomial ℂ →+* MvPolynomial (Fin m) (Polynomial ℂ))]
    rw [mul_assoc, ← map_mul, mul_comm, C_mul_monomial, mul_one]
  rw [Finset.prod_congr rfl (fun i _ => h1 i), Finset.prod_univ_sum]
  simp_rw [← monomial_sum_prod, coeff_sum, coeff_monomial]
  have hfs : ∀ κ : Fin m → ℕ, (∑ i, Finsupp.single i (κ i) = A) ↔ κ = ⇑A := by
    intro κ
    constructor
    · rintro h; funext i; rw [← h]; simp [Finsupp.finsetSum_apply, Finsupp.single_apply]
    · rintro rfl; ext j; simp [Finsupp.finsetSum_apply, Finsupp.single_apply]
  simp_rw [hfs]
  rw [Finset.sum_ite_eq']
  unfold D
  split_ifs with hA
  · simp only [g]
    exact Finset.prod_congr rfl fun i _ => mul_comm _ _
  · have : ∃ i, b' i < A i := by
      by_contra h; push Not at h
      exact hA (Fintype.mem_piFinset.2 fun i => Finset.mem_range.2 (Nat.lt_succ_of_le (h i)))
    obtain ⟨i, hi⟩ := this
    rw [Finset.prod_eq_zero (Finset.mem_univ i) (by rw [Nat.choose_eq_zero_of_lt hi]; simp)]

/-- coefficient of a shifted polynomial -/
lemma coeff_shift (Δ : Fin m → Polynomial ℂ) (Q : MvPolynomial (Fin m) (Polynomial ℂ)) (A : Fin m →₀ ℕ) :
    MvPolynomial.coeff A (aeval (fun i => X i + C (Δ i)) Q) =
      ∑ b ∈ Q.support, Q.coeff b * D Δ (⇑A) (⇑b) := by
  classical
  conv_lhs => rw [Q.as_sum]
  rw [map_sum, coeff_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [aeval_monomial, Finsupp.prod_fintype _ _ (fun i => pow_zero _), Algebra.algebraMap_eq_smul_one,
    smul_mul_assoc, one_mul, coeff_smul, coeff_prod_shift, smul_eq_mul]

lemma coeff_D_ne_zero (Δ : Fin m → Polynomial ℂ) (o : Fin m → ℕ)
    (ho : ∀ i, Polynomial.X ^ o i ∣ Δ i) (b b' : Fin m → ℕ) (n : ℕ)
    (hn : (D Δ b b').coeff n ≠ 0) :
    (∀ i, b i ≤ b' i) ∧ ∑ i, o i * (b' i - b i) ≤ n := by
  have hle : ∀ i, b i ≤ b' i := by
    intro i
    by_contra h
    apply hn
    unfold D
    rw [Finset.prod_eq_zero (Finset.mem_univ i) (by rw [Nat.choose_eq_zero_of_lt (by omega)]; simp)]
    simp
  refine ⟨hle, ?_⟩
  have hdvd : Polynomial.X ^ (∑ i, o i * (b' i - b i)) ∣ D Δ b b' := by
    unfold D
    rw [← Finset.prod_pow_eq_pow_sum]
    apply Finset.prod_dvd_prod_of_dvd
    intro i _
    rw [pow_mul]
    exact Dvd.dvd.mul_left (pow_dvd_pow_of_dvd (ho i) _) _
  obtain ⟨q, hq⟩ := hdvd
  by_contra h
  apply hn
  rw [hq, Polynomial.coeff_X_pow_mul', if_neg (by omega)]


open InterpolationMatrix

lemma shift_monomialImage (r : Fin m → ℂ) (G G' : Fin m → Polynomial ℂ) (j h : ℕ) (a : Fin m → ℕ) :
    aeval (fun i => X i + C (G i - G' i)) (monomialImage r G' j h a) = monomialImage r G j h a := by
  unfold monomialImage
  rw [map_mul, map_prod, aeval_C]
  congr 1
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [map_pow, map_add, aeval_C, aeval_X]
  congr 1
  simp only [Polynomial.algebraMap_apply, algebraMap_eq, map_add, map_sub]
  ring

lemma mem_sws {m : ℕ} (v0 θ : ℝ) (w : Fin m → ℝ) (H : ℝ) (hv0 : 0 < v0) (htheta : 0 < θ)
    (hw : ∀ i, 0 < w i) (e : Fin (m + 1) → ℕ) :
    e ∈ OAI.PiExponent.strictWeightedSimplex (rowWeights v0 θ w) H ↔
      v0 * (e 0 : ℝ) + ∑ i : Fin m, w i / θ * (e i.succ : ℝ) < H := by
  classical
  have hpos : ∀ i, 0 < rowWeights v0 θ w i := by
    intro i
    refine Fin.cases ?_ (fun i => ?_) i
    · simpa [rowWeights] using hv0
    · simpa [rowWeights] using div_pos (hw i) htheta
  have hsum : ∑ i, rowWeights v0 θ w i * (e i : ℝ) = v0 * (e 0 : ℝ) + ∑ i : Fin m, w i / θ * (e i.succ : ℝ) := by
    rw [Fin.sum_univ_succ]; simp [rowWeights]
  unfold OAI.PiExponent.strictWeightedSimplex OAI.PiExponent.realWeightedSimplex
  simp only [Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_range, ← hsum]
  constructor
  · exact fun h => h.2
  · intro hs
    refine ⟨⟨fun i => ?_, hs.le⟩, hs⟩
    have hle : rowWeights v0 θ w i * (e i : ℝ) ≤ ∑ j, rowWeights v0 θ w j * (e j : ℝ) :=
      Finset.single_le_sum (f := fun j => rowWeights v0 θ w j * (e j : ℝ))
        (fun j _ => mul_nonneg (hpos j).le (Nat.cast_nonneg _)) (Finset.mem_univ i)
    have : (e i : ℝ) ≤ H / rowWeights v0 θ w i := by rw [le_div_iff₀ (hpos i)]; linarith
    have := Nat.le_floor this
    omega


variable {K : ℕ} {v0 θ : ℝ} {w : Fin m → ℝ} {H : ℝ}

def tl (e : Fin (m + 1) → ℕ) : Fin m → ℕ := fun i => e i.succ

noncomputable def U (Δ : Fin m → Polynomial ℂ) : Matrix (Row K v0 θ w H) (Row K v0 θ w H) ℂ :=
  fun ρ ρ' => if ρ.1 = ρ'.1 ∧ ρ'.2.1 0 ≤ ρ.2.1 0 then
    (D Δ (tl ρ.2.1) (tl ρ'.2.1)).coeff (ρ.2.1 0 - ρ'.2.1 0) else 0

lemma D_self (Δ : Fin m → Polynomial ℂ) (b : Fin m → ℕ) : D Δ b b = 1 := by
  unfold D; simp

lemma U_ne_zero (Δ : Fin m → Polynomial ℂ) (ρ ρ' : Row K v0 θ w H) (h : U Δ ρ ρ' ≠ 0) :
    ρ.1 = ρ'.1 ∧ ρ'.2.1 0 ≤ ρ.2.1 0 ∧ ∀ i, tl ρ.2.1 i ≤ tl ρ'.2.1 i := by
  unfold U at h
  split_ifs at h with hc
  · exact ⟨hc.1, hc.2, (coeff_D_ne_zero Δ (fun _ => 0) (fun i => by simp) _ _ _ h).1⟩
  · exact absurd rfl h

lemma U_bij (Δ : Fin m → Polynomial ℂ) : Function.Bijective (U (K := K) (v0 := v0) (θ := θ) (w := w) (H := H) Δ).mulVecLin := by
  classical
  set M := U (K := K) (v0 := v0) (θ := θ) (w := w) (H := H) Δ
  let β : Row K v0 θ w H → ℕ := fun ρ => ∑ i, tl ρ.2.1 i
  have hbt : Matrix.BlockTriangular M β := by
    intro ρ ρ' hlt
    by_contra h
    obtain ⟨-, -, hle⟩ := U_ne_zero Δ ρ ρ' h
    have : β ρ ≤ β ρ' := Finset.sum_le_sum fun i _ => hle i
    omega
  have hblock : ∀ k, M.toSquareBlock β k = 1 := by
    intro k
    ext ρ ρ'
    rw [Matrix.toSquareBlock_def, Matrix.of_apply, Matrix.one_apply]
    by_cases hρ : ρ = ρ'
    · subst hρ
      rw [if_pos rfl]
      simp only [M, U, true_and, le_refl, if_true, Nat.sub_self, D_self, Polynomial.coeff_one_zero]
    · rw [if_neg hρ]
      by_contra h
      obtain ⟨hj, hs, hle⟩ := U_ne_zero Δ _ _ h
      have heq : β ρ.1 = β ρ'.1 := ρ.2.trans ρ'.2.symm
      have htl : tl ρ.1.2.1 = tl ρ'.1.2.1 := by
        funext i
        by_contra hne
        have hlt : tl ρ.1.2.1 i < tl ρ'.1.2.1 i := lt_of_le_of_ne (hle i) hne
        have : β ρ.1 < β ρ'.1 := Finset.sum_lt_sum (fun i _ => hle i) ⟨i, Finset.mem_univ _, hlt⟩
        omega
      have h2 : M ρ.1 ρ'.1 = (1 : Polynomial ℂ).coeff (ρ.1.2.1 0 - ρ'.1.2.1 0) := by
        simp only [M, U, if_pos (And.intro hj hs), htl, D_self]
      rw [h2, Polynomial.coeff_one] at h
      have h0 : ρ.1.2.1 0 = ρ'.1.2.1 0 := by
        by_contra hne; apply h; rw [if_neg (by omega)]
      apply hρ
      apply Subtype.ext
      apply Prod.ext hj
      apply Subtype.ext
      funext i
      refine Fin.cases h0 (fun i => congrFun htl i) i
  have hdet : M.det = 1 := by
    rw [hbt.det]
    exact Finset.prod_eq_one fun k _ => by rw [hblock k, Matrix.det_one]
  have hu : IsUnit M := (Matrix.isUnit_iff_isUnit_det M).2 (by rw [hdet]; exact isUnit_one)
  exact ⟨Matrix.mulVec_injective_iff_isUnit.2 hu, Matrix.mulVec_surjective_iff_isUnit.2 hu⟩


lemma weight_le (θ' : ℝ) (v0' : ℝ) (w' : Fin m → ℝ) (hv0 : 0 ≤ v0') (o : Fin m → ℕ) (hov : ∀ i, w' i / θ' ≤ v0' * o i)
    (b b'' : Fin m → ℕ) (hle : ∀ i, b i ≤ b'' i) (s1 s2 : ℕ) (hsum : ∑ i, o i * (b'' i - b i) ≤ s2) :
    v0' * (s1 : ℝ) + ∑ i, w' i / θ' * (b'' i : ℝ) ≤ v0' * ((s1 + s2 : ℕ) : ℝ) + ∑ i, w' i / θ' * (b i : ℝ) := by
  have hsum' : (∑ i, (o i : ℝ) * ((b'' i : ℝ) - b i)) ≤ s2 := by
    have := (Nat.cast_le (α := ℝ)).2 hsum
    push_cast [Nat.cast_sum, Nat.cast_mul, Nat.cast_sub (hle _)] at this
    exact this
  have key : ∑ i, w' i / θ' * (b'' i : ℝ) ≤ ∑ i, w' i / θ' * (b i : ℝ) + v0' * ∑ i, (o i : ℝ) * ((b'' i : ℝ) - b i) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun i _ => ?_
    have h1 : (0 : ℝ) ≤ (b'' i : ℝ) - b i := by have := hle i; rw [sub_nonneg]; exact_mod_cast this
    have := mul_le_mul_of_nonneg_right (hov i) h1
    nlinarith
  have := mul_le_mul_of_nonneg_left hsum' hv0
  push_cast
  nlinarith

lemma entry_eq (r : Fin m → ℂ) (G G' : Fin m → Polynomial ℂ) (j s : ℕ) (b : Fin m → ℕ) (h : ℕ) (a : Fin m → ℕ) :
    entry r G j s b h a = ∑ x ∈ (monomialImage r G' j h a).support ×ˢ Finset.antidiagonal s,
      ((monomialImage r G' j h a).coeff x.1).coeff x.2.1 * (D (fun i => G i - G' i) b ⇑x.1).coeff x.2.2 := by
  unfold entry
  rw [← shift_monomialImage r G G' j h a, coeff_shift, Polynomial.finset_sum_coeff, Finset.sum_product]
  have hb : ⇑(exponentVector b) = b := by simp [exponentVector]
  rw [hb]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Polynomial.coeff_mul]

theorem main (K : ℕ) (w0 v0 θ : ℝ) (w : Fin m → ℝ) (H : ℝ) (r : Fin m → ℂ) (G G' : Fin m → Polynomial ℂ)
    (hv0 : 0 < v0) (htheta : 0 < θ) (hw : ∀ i, 0 < w i)
    (hcoeff : ∀ (i : Fin m) (k : ℕ), v0 * (k : ℝ) < w i / θ → (G i).coeff k = (G' i).coeff k) :
    matrix K w0 v0 θ w H r G = U (fun i => G i - G' i) * matrix K w0 v0 θ w H r G' := by
  classical
  set Δ : Fin m → Polynomial ℂ := fun i => G i - G' i with hΔ
  set o : Fin m → ℕ := fun i => ⌈w i / (θ * v0)⌉₊ with ho
  have hov : ∀ i, w i / θ ≤ v0 * o i := by
    intro i
    have := Nat.le_ceil (w i / (θ * v0))
    rw [div_le_iff₀ (mul_pos htheta hv0)] at this
    rw [div_le_iff₀ htheta]; simp only [ho]; nlinarith
  have hdvd : ∀ i, Polynomial.X ^ o i ∣ Δ i := by
    intro i
    rw [Polynomial.X_pow_dvd_iff]
    intro d hd
    have h1 : (d : ℝ) < w i / (θ * v0) := Nat.lt_ceil.1 hd
    rw [lt_div_iff₀ (mul_pos htheta hv0)] at h1
    have h2 : v0 * (d : ℝ) < w i / θ := by rw [lt_div_iff₀ htheta]; linarith
    simp only [hΔ, Polynomial.coeff_sub, hcoeff i d h2, sub_self]
  ext ρ c
  rw [Matrix.mul_apply]
  have hL : matrix K w0 v0 θ w H r G ρ c = entry r G ρ.1.val (ρ.2.1 0) (fun i => ρ.2.1 i.succ) (c.1 0) (fun i => c.1 i.succ) := rfl
  rw [hL, entry_eq r G G']
  have hρmem := (mem_sws v0 θ w H hv0 htheta hw ρ.2.1).1 ρ.2.2
  have hmem : ∀ x ∈ (monomialImage r G' ρ.1.val (c.1 0) (fun i => c.1 i.succ)).support ×ˢ
      Finset.antidiagonal (ρ.2.1 0),
      ((monomialImage r G' ρ.1.val (c.1 0) (fun i => c.1 i.succ)).coeff x.1).coeff x.2.1 *
        (D Δ (fun i => ρ.2.1 i.succ) ⇑x.1).coeff x.2.2 ≠ 0 →
      (Fin.cons x.2.1 ⇑x.1 : Fin (m + 1) → ℕ) ∈ OAI.PiExponent.strictWeightedSimplex (rowWeights v0 θ w) H := by
    intro x hx hne
    have hD := right_ne_zero_of_mul hne
    obtain ⟨hle, hsum⟩ := coeff_D_ne_zero Δ o hdvd _ _ _ hD
    have hx2 := (Finset.mem_antidiagonal.1 (Finset.mem_product.1 hx).2)
    rw [mem_sws v0 θ w H hv0 htheta hw]
    simp only [Fin.cons_zero, Fin.cons_succ]
    have := weight_le θ v0 w hv0.le o hov _ _ hle x.2.1 x.2.2 hsum
    rw [hx2] at this
    linarith
  refine Finset.sum_bij_ne_zero (fun x hx hne => (ρ.1, ⟨Fin.cons x.2.1 ⇑x.1, hmem x hx hne⟩))
    (fun _ _ _ => Finset.mem_univ _) ?_ ?_ ?_
  · intro x hx hne y hy hne' heq
    simp only [Prod.mk.injEq, Subtype.mk.injEq, true_and] at heq
    have h0 := congrFun heq 0
    simp only [Fin.cons_zero] at h0
    have h1 : (⇑x.1 : Fin m → ℕ) = ⇑y.1 := funext fun i => by simpa using congrFun heq i.succ
    have hx2 := (Finset.mem_antidiagonal.1 (Finset.mem_product.1 hx).2)
    have hy2 := (Finset.mem_antidiagonal.1 (Finset.mem_product.1 hy).2)
    ext1
    · exact DFunLike.coe_injective h1
    · ext1
      · exact h0
      · omega
  · intro ρ' _ hne
    have hU := left_ne_zero_of_mul hne
    obtain ⟨hj, hs', -⟩ := U_ne_zero Δ ρ ρ' hU
    have hM := right_ne_zero_of_mul hne
    have hM' : ((monomialImage r G' ρ.1.val (c.1 0) (fun i => c.1 i.succ)).coeff
        (exponentVector (fun i => ρ'.2.1 i.succ))).coeff (ρ'.2.1 0) ≠ 0 := by
      rw [hj]; exact hM
    refine ⟨(exponentVector (fun i => ρ'.2.1 i.succ), (ρ'.2.1 0, ρ.2.1 0 - ρ'.2.1 0)), ?_, ?_, ?_⟩
    · refine Finset.mem_product.2 ⟨?_, Finset.mem_antidiagonal.2 (by simp; omega)⟩
      rw [MvPolynomial.mem_support_iff]
      intro h0; rw [h0, Polynomial.coeff_zero] at hM'; exact hM' rfl
    · have hb : ⇑(exponentVector (fun i => ρ'.2.1 i.succ)) = fun i => ρ'.2.1 i.succ := by
        simp [exponentVector]
      simp only [hb]
      have hU' : U Δ ρ ρ' = (D Δ (fun i => ρ.2.1 i.succ) (fun i => ρ'.2.1 i.succ)).coeff (ρ.2.1 0 - ρ'.2.1 0) := by
        simp only [U, if_pos (And.intro hj hs')]; rfl
      rw [← hU']
      exact mul_ne_zero hM' hU
    · refine Prod.ext hj ?_
      apply Subtype.ext
      simp only
      have hb : ⇑(exponentVector (fun i => ρ'.2.1 i.succ)) = fun i => ρ'.2.1 i.succ := by
        simp [exponentVector]
      rw [hb]
      exact Fin.cons_self_tail _
  · intro x hx hne
    have hx2 := (Finset.mem_antidiagonal.1 (Finset.mem_product.1 hx).2)
    have hle : x.2.1 ≤ ρ.2.1 0 := by omega
    have hsub : ρ.2.1 0 - x.2.1 = x.2.2 := by omega
    simp only [U, tl, Fin.cons_zero, Fin.cons_succ, true_and, if_pos hle, hsub]
    have hM : matrix K w0 v0 θ w H r G' (ρ.1, ⟨Fin.cons x.2.1 ⇑x.1, hmem x hx hne⟩) c =
        entry r G' ρ.1.val x.2.1 (fun i => (Fin.cons x.2.1 ⇑x.1 : Fin (m + 1) → ℕ) i.succ) (c.1 0)
          (fun i => c.1 i.succ) := rfl
    rw [hM]
    unfold entry
    simp only [Fin.cons_succ]
    have hb : exponentVector (fun i => x.1 i) = x.1 := by
      ext i; simp [exponentVector]
    rw [hb, mul_comm]
    rfl

end S105WF

theorem solution
    {m : ℕ} (K : ℕ) (w0 v0 theta : ℝ) (w : Fin m → ℝ)
    (H : ℝ) (r : Fin m → ℂ) (G G' : Fin m → Polynomial ℂ)
    (hv0 : 0 < v0) (htheta : 0 < theta) (hw : ∀ i, 0 < w i)
    (hcoeff : ∀ (i : Fin m) (k : ℕ),
      v0 * (k : ℝ) < w i / theta → (G i).coeff k = (G' i).coeff k) :
    ∃ U : Matrix
        (OAI.PiExponent.InterpolationMatrix.Row K v0 theta w H)
        (OAI.PiExponent.InterpolationMatrix.Row K v0 theta w H) ℂ,
      Function.Bijective U.mulVecLin ∧
      OAI.PiExponent.InterpolationMatrix.matrix K w0 v0 theta w H r G =
        U * OAI.PiExponent.InterpolationMatrix.matrix K w0 v0 theta w H r G' :=
  ⟨S105WF.U (fun i => G i - G' i), S105WF.U_bij _,
    S105WF.main K w0 v0 theta w H r G G' hv0 htheta hw hcoeff⟩
