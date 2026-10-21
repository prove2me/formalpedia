-- Prove2me | solution 1 for NetPriceDisc.Random.eq_14
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T16:03:35.392443+00:00
-- url     : https://prove2.me/submissions/d568c9ff-6506-41ae-abb1-45e60078c0b3

import Mathlib
import Definitions.Def_NetPriceDisc_Random_Model

set_option autoImplicit false
open Matrix NetPriceDisc.Random
open scoped Matrix.Norms.L2Operator

lemma bil {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (x y : Fin n → ℝ) :
    |x ⬝ᵥ (A *ᵥ y)| ≤ ‖A‖ * ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin n))‖ *
      ‖(WithLp.toLp 2 y : EuclideanSpace ℝ (Fin n))‖ := by
  have h1 : ‖(WithLp.toLp 2 (A *ᵥ y) : EuclideanSpace ℝ (Fin n))‖ ≤
      ‖A‖ * ‖(WithLp.toLp 2 y : EuclideanSpace ℝ (Fin n))‖ :=
    Matrix.l2_opNorm_mulVec A (WithLp.toLp 2 y : EuclideanSpace ℝ (Fin n))
  have h2 := abs_real_inner_le_norm (WithLp.toLp 2 x : EuclideanSpace ℝ (Fin n))
    (WithLp.toLp 2 (A *ᵥ y) : EuclideanSpace ℝ (Fin n))
  rw [EuclideanSpace.inner_eq_star_dotProduct] at h2
  simp only [star_trivial] at h2
  rw [dotProduct_comm] at h2
  calc |x ⬝ᵥ (A *ᵥ y)| ≤ ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin n))‖ *
        ‖(WithLp.toLp 2 (A *ᵥ y) : EuclideanSpace ℝ (Fin n))‖ := h2
    _ ≤ ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin n))‖ *
        (‖A‖ * ‖(WithLp.toLp 2 y : EuclideanSpace ℝ (Fin n))‖) :=
        mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
    _ = _ := by ring

lemma nrm_ones (n : ℕ) : ‖(WithLp.toLp 2 (ones n) : EuclideanSpace ℝ (Fin n))‖ ^ 2 = n := by
  rw [EuclideanSpace.norm_sq_eq]
  simp [ones]

lemma ones_dot (n : ℕ) : ones n ⬝ᵥ ones n = n := by simp [ones, dotProduct]

lemma walks_le {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (k : ℕ) :
    walks A k ≤ ‖A ^ k‖ * n := by
  have h := bil (A ^ k) (ones n) (ones n)
  have h2 := nrm_ones n
  have h3 : ‖(WithLp.toLp 2 (ones n) : EuclideanSpace ℝ (Fin n))‖ *
      ‖(WithLp.toLp 2 (ones n) : EuclideanSpace ℝ (Fin n))‖ = n := by rw [← sq]; exact h2
  calc walks A k ≤ |ones n ⬝ᵥ ((A ^ k) *ᵥ ones n)| := le_abs_self _
    _ ≤ _ := h
    _ = ‖A ^ k‖ * n := by rw [mul_assoc, h3]

lemma nrm_single {n : ℕ} (i : Fin n) :
    ‖(WithLp.toLp 2 (Pi.single i (1 : ℝ)) : EuclideanSpace ℝ (Fin n))‖ = 1 := by
  have : ‖(WithLp.toLp 2 (Pi.single i (1 : ℝ)) : EuclideanSpace ℝ (Fin n))‖ ^ 2 = 1 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp [Pi.single_apply]
  nlinarith [norm_nonneg (WithLp.toLp 2 (Pi.single i (1 : ℝ)) : EuclideanSpace ℝ (Fin n))]

lemma entry_le {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) : |A i j| ≤ ‖A‖ := by
  have h := bil A (Pi.single i 1) (Pi.single j 1)
  rw [nrm_single, nrm_single] at h
  have e : (Pi.single i (1 : ℝ) : Fin n → ℝ) ⬝ᵥ (A *ᵥ Pi.single j 1) = A i j := by
    simp [Matrix.mulVec_single_one]
  rw [e] at h
  simpa using h

lemma vec_nonneg {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : ∀ i j, 0 ≤ A i j) (k : ℕ) :
    ∀ i, 0 ≤ ((A ^ k) *ᵥ ones n) i := by
  induction k with
  | zero => intro i; simp [ones]
  | succ k ih =>
    intro i
    have : (A ^ (k + 1)) *ᵥ ones n = A *ᵥ ((A ^ k) *ᵥ ones n) := by
      rw [pow_succ', ← Matrix.mulVec_mulVec]
    rw [this]
    simp only [Matrix.mulVec, dotProduct]
    exact Finset.sum_nonneg (fun m _ => mul_nonneg (hA i m) (ih m))


lemma coercive {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ) (ρ : ℝ)
    (hq : ∀ x, x ⬝ᵥ (B *ᵥ x) ≤ ρ * (x ⬝ᵥ x)) (x : Fin n → ℝ) :
    (1 - ρ) * (x ⬝ᵥ x) ≤ x ⬝ᵥ ((1 - B) *ᵥ x) := by
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, dotProduct_sub]
  nlinarith [hq x]

lemma isUnit_of_coercive {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ) (ρ : ℝ) (hρ : ρ < 1)
    (hq : ∀ x, x ⬝ᵥ (B *ᵥ x) ≤ ρ * (x ⬝ᵥ x)) : IsUnit (1 - B) := by
  rw [← Matrix.mulVec_injective_iff_isUnit]
  intro x y hxy
  rw [← sub_eq_zero]
  have hx' : (1 - B) *ᵥ (x - y) = 0 := by rw [Matrix.mulVec_sub]; exact sub_eq_zero.mpr hxy
  have h1 := coercive B ρ hq (x - y)
  suffices hz : x - y = 0 from hz
  generalize x - y = x at hx' h1 ⊢
  rw [hx', dotProduct_zero] at h1
  have h2 : 0 ≤ x ⬝ᵥ x := Finset.sum_nonneg (fun j _ => mul_self_nonneg (x j))
  have h3 : x ⬝ᵥ x = 0 := by
    by_contra hne
    have : 0 < x ⬝ᵥ x := lt_of_le_of_ne h2 (Ne.symm hne)
    nlinarith
  exact dotProduct_self_eq_zero.mp h3

lemma series_exists {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ) (hB : ∀ i j, 0 ≤ B i j) (ρ : ℝ)
    (hρ : ρ < 1) (hq : ∀ x, x ⬝ᵥ (B *ᵥ x) ≤ ρ * (x ⬝ᵥ x)) :
    ∃ u : Fin n → ℝ, HasSum (fun k : ℕ => (B ^ k) *ᵥ ones n) u ∧ (1 - B) *ᵥ u = ones n ∧
      ∀ i, 1 ≤ u i := by
  set f : ℕ → Fin n → ℝ := fun k => (B ^ k) *ᵥ ones n with hf
  have hf0 : ∀ k i, 0 ≤ f k i := fun k i => vec_nonneg B hB k i
  have hfs : ∀ k, f (k + 1) = B *ᵥ f k := by
    intro k; simp only [hf]; rw [pow_succ', ← Matrix.mulVec_mulVec]
  have hs : ∀ K, (1 - B) *ᵥ (∑ k ∈ Finset.range K, f k) = ones n - f K := by
    intro K
    induction K with
    | zero => simp [hf]
    | succ K ih =>
      rw [Finset.sum_range_succ, Matrix.mulVec_add, ih, hfs K, Matrix.sub_mulVec,
        Matrix.one_mulVec]
      abel
  have hρ' : 0 < 1 - ρ := by linarith
  have hbound : ∀ K i, (∑ k ∈ Finset.range K, f k) i ≤ 1 + n / (1 - ρ) ^ 2 := by
    intro K i
    set s : Fin n → ℝ := ∑ k ∈ Finset.range K, f k with hsdef
    have hs0 : ∀ j, 0 ≤ s j := fun j => by
      simp only [hsdef, Finset.sum_apply]; exact Finset.sum_nonneg (fun k _ => hf0 k j)
    have h1 := coercive B ρ hq s
    rw [hs K, dotProduct_sub] at h1
    have h2 : 0 ≤ s ⬝ᵥ f K := Finset.sum_nonneg (fun j _ => mul_nonneg (hs0 j) (hf0 K j))
    have h3 : (1 - ρ) * (s ⬝ᵥ s) ≤ s ⬝ᵥ ones n := by linarith
    have h4 : s ⬝ᵥ ones n ≤ ((1 - ρ) * (s ⬝ᵥ s) + n / (1 - ρ)) / 2 := by
      have hj : ∀ j, s j ≤ ((1 - ρ) * (s j * s j) + 1 / (1 - ρ)) / 2 := by
        intro j
        rw [← sub_nonneg]
        have : ((1 - ρ) * (s j * s j) + 1 / (1 - ρ)) / 2 - s j
            = ((1 - ρ) * s j - 1) ^ 2 / (2 * (1 - ρ)) := by
          field_simp; ring
        rw [this]; positivity
      calc s ⬝ᵥ ones n = ∑ j, s j := by simp [dotProduct, ones]
        _ ≤ ∑ j, ((1 - ρ) * (s j * s j) + 1 / (1 - ρ)) / 2 := Finset.sum_le_sum (fun j _ => hj j)
        _ = ((1 - ρ) * (s ⬝ᵥ s) + n / (1 - ρ)) / 2 := by
          rw [← Finset.sum_div, Finset.sum_add_distrib, ← Finset.mul_sum]
          simp [dotProduct]; ring
    have h5 : s ⬝ᵥ s ≤ n / (1 - ρ) ^ 2 := by
      have : (1 - ρ) * (s ⬝ᵥ s) ≤ n / (1 - ρ) := by linarith
      rw [le_div_iff₀ (by positivity), sq, ← mul_assoc]
      have h6 : (1 - ρ) * (s ⬝ᵥ s) * (1 - ρ) ≤ n / (1 - ρ) * (1 - ρ) :=
        mul_le_mul_of_nonneg_right this hρ'.le
      rw [div_mul_cancel₀ _ hρ'.ne'] at h6
      linarith
    have h6 : s i * s i ≤ s ⬝ᵥ s :=
      Finset.single_le_sum (f := fun j => s j * s j) (fun j _ => mul_self_nonneg _)
        (Finset.mem_univ i)
    nlinarith [sq_nonneg (s i - 1)]
  have hsum : ∀ i, Summable (fun k => f k i) := fun i =>
    summable_of_sum_range_le (fun k => hf0 k i) (c := 1 + n / (1 - ρ) ^ 2) (fun K => by
      have := hbound K i
      simpa [Finset.sum_apply] using this)
  have hsm : Summable f := Pi.summable.mpr hsum
  set u := ∑' k, f k with hu
  have hU : HasSum f u := hsm.hasSum
  have hU1 : HasSum (fun k => f (k + 1)) (u - f 0) := by
    have := (hasSum_nat_add_iff' 1).mpr hU
    simpa using this
  have hcont : Continuous (Matrix.mulVecLin B : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)) :=
    LinearMap.continuous_of_finiteDimensional _
  have hU2 : HasSum (fun k => B *ᵥ f k) (B *ᵥ u) := by
    have := hU.map (Matrix.mulVecLin B : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)) hcont
    simpa [Function.comp_def, Matrix.mulVecLin_apply] using this
  have hBu : B *ᵥ u = u - f 0 := by
    refine hU2.unique ?_
    simpa [hfs] using hU1
  have hf00 : f 0 = ones n := by simp [hf]
  refine ⟨u, hU, ?_, ?_⟩
  · rw [Matrix.sub_mulVec, Matrix.one_mulVec, hBu, hf00]; abel
  · intro i
    have := le_hasSum (Pi.hasSum.mp hU i) 0 (fun j _ => hf0 j i)
    simpa [hf00, ones] using this


lemma form_le {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) :
    x ⬝ᵥ (A *ᵥ x) ≤ ‖A‖ * (x ⬝ᵥ x) := by
  have h := bil A x x
  have hvv : ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin n))‖ ^ 2 = x ⬝ᵥ x := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simp [dotProduct, sq]
  calc x ⬝ᵥ (A *ᵥ x) ≤ |x ⬝ᵥ (A *ᵥ x)| := le_abs_self _
    _ ≤ _ := h
    _ = ‖A‖ * (x ⬝ᵥ x) := by rw [mul_assoc, ← sq, hvv]

lemma quad_T {n : ℕ} (G : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) :
    x ⬝ᵥ (Gᵀ *ᵥ x) = x ⬝ᵥ (G *ᵥ x) := by
  rw [Matrix.mulVec_transpose, dotProduct_comm, Matrix.dotProduct_mulVec]

lemma quad_A {n : ℕ} (G : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) :
    x ⬝ᵥ ((G + Gᵀ) *ᵥ x) = 2 * (x ⬝ᵥ (G *ᵥ x)) := by
  rw [Matrix.add_mulVec, dotProduct_add, quad_T]; ring

lemma tN_le {n : ℕ} (G : Matrix (Fin n) (Fin n) ℝ) (ρ : ℝ) (hρ : 0 ≤ ρ) :
    ρ / specNorm (G + Gᵀ) * specNorm (G + Gᵀ) ≤ ρ := by
  rcases eq_or_ne (specNorm (G + Gᵀ)) 0 with h | h
  · rw [h]; simpa using hρ
  · rw [div_mul_cancel₀ _ h]

lemma hqA {n : ℕ} (G : Matrix (Fin n) (Fin n) ℝ) (ρ : ℝ) (hρ : 0 ≤ ρ) (x : Fin n → ℝ) :
    x ⬝ᵥ (((ρ / specNorm (G + Gᵀ)) • (G + Gᵀ)) *ᵥ x) ≤ ρ * (x ⬝ᵥ x) := by
  rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]
  have h1 := form_le (G + Gᵀ) x
  have h2 := tN_le G ρ hρ
  have h3 : 0 ≤ x ⬝ᵥ x := Finset.sum_nonneg (fun j _ => mul_self_nonneg (x j))
  have h4 : 0 ≤ ρ / specNorm (G + Gᵀ) := div_nonneg hρ (norm_nonneg _)
  calc ρ / specNorm (G + Gᵀ) * (x ⬝ᵥ ((G + Gᵀ) *ᵥ x))
      ≤ ρ / specNorm (G + Gᵀ) * (specNorm (G + Gᵀ) * (x ⬝ᵥ x)) := mul_le_mul_of_nonneg_left h1 h4
    _ = (ρ / specNorm (G + Gᵀ) * specNorm (G + Gᵀ)) * (x ⬝ᵥ x) := by ring
    _ ≤ ρ * (x ⬝ᵥ x) := mul_le_mul_of_nonneg_right h2 h3

lemma hqG {n : ℕ} (G : Matrix (Fin n) (Fin n) ℝ) (ρ : ℝ) (hρ : 0 ≤ ρ) (x : Fin n → ℝ) :
    x ⬝ᵥ (((2 * ρ / specNorm (G + Gᵀ)) • G) *ᵥ x) ≤ ρ * (x ⬝ᵥ x) := by
  have h := hqA G ρ hρ x
  rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul] at h ⊢
  rw [quad_A] at h
  have : 2 * ρ / specNorm (G + Gᵀ) * (x ⬝ᵥ (G *ᵥ x)) =
      ρ / specNorm (G + Gᵀ) * (2 * (x ⬝ᵥ (G *ᵥ x))) := by ring
  rw [this]; exact h

lemma nonnegA {n : ℕ} (G : Matrix (Fin n) (Fin n) ℝ) (hG : ∀ i j, 0 ≤ G i j) (ρ : ℝ)
    (hρ : 0 ≤ ρ) (i j : Fin n) : 0 ≤ ((ρ / specNorm (G + Gᵀ)) • (G + Gᵀ)) i j := by
  have h4 : 0 ≤ ρ / specNorm (G + Gᵀ) := div_nonneg hρ (norm_nonneg _)
  simp only [Matrix.smul_apply, Matrix.add_apply, Matrix.transpose_apply, smul_eq_mul]
  exact mul_nonneg h4 (add_nonneg (hG i j) (hG j i))

lemma nonnegG {n : ℕ} (G : Matrix (Fin n) (Fin n) ℝ) (hG : ∀ i j, 0 ≤ G i j) (ρ : ℝ)
    (hρ : 0 ≤ ρ) (i j : Fin n) : 0 ≤ ((2 * ρ / specNorm (G + Gᵀ)) • G) i j := by
  have h4 : 0 ≤ 2 * ρ / specNorm (G + Gᵀ) := div_nonneg (by linarith) (norm_nonneg _)
  simp only [Matrix.smul_apply, smul_eq_mul]
  exact mul_nonneg h4 (hG i j)

lemma inv_ones {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (hM : IsUnit M) (u : Fin n → ℝ)
    (hu : M *ᵥ u = ones n) : M⁻¹ *ᵥ ones n = u := by
  rw [← hu, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp hM),
    Matrix.one_mulVec]

lemma walks_hasSum {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ) (u : Fin n → ℝ)
    (h : HasSum (fun k : ℕ => (B ^ k) *ᵥ ones n) u) :
    HasSum (fun k : ℕ => walks B k) (ones n ⬝ᵥ u) := by
  have h2 := hasSum_sum (s := Finset.univ) (f := fun (i : Fin n) (k : ℕ) => ((B ^ k) *ᵥ ones n) i)
    (a := fun i => u i) (fun i _ => Pi.hasSum.mp h i)
  have e : ∀ k, walks B k = ∑ i, ((B ^ k) *ᵥ ones n) i := by
    intro k; simp [walks, dotProduct, ones]
  simp only [e]
  have e2 : ones n ⬝ᵥ u = ∑ i, u i := by simp [dotProduct, ones]
  rw [e2]; exact h2


lemma walks_smul {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (c : ℝ) (k : ℕ) :
    walks (c • A) k = c ^ k * walks A k := by
  unfold walks
  rw [smul_pow, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]

lemma symm_dot {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : Aᵀ = A) (x y : Fin n → ℝ) :
    (A *ᵥ x) ⬝ᵥ y = x ⬝ᵥ (A *ᵥ y) := by
  rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hA, dotProduct_comm]

lemma profit_unfold {n : ℕ} (a c ρ : ℝ) (G : Matrix (Fin n) (Fin n) ℝ) (p : Fin n → ℝ) :
    profit a c ρ G p = (1 / 2 : ℝ) * ((p - c • ones n) ⬝ᵥ
      ((1 - (2 * ρ / specNorm (G + Gᵀ)) • G)⁻¹ *ᵥ (a • ones n - p))) := by
  unfold profit xStar
  rw [dotProduct_smul, smul_eq_mul]

lemma opt_main {n : ℕ} (a c ρ : ℝ) (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (G : Matrix (Fin n) (Fin n) ℝ) (hG : ∀ i j, 0 ≤ G i j) :
    ∃ w : Fin n → ℝ,
      (1 - (ρ / specNorm (G + Gᵀ)) • (G + Gᵀ))⁻¹ *ᵥ ones n = w ∧
      HasSum (fun k : ℕ => (ρ / specNorm (G + Gᵀ)) ^ k * walks (G + Gᵀ) k) (ones n ⬝ᵥ w) ∧
      (∀ i, 1 ≤ w i) ∧ ones n ⬝ᵥ w ≤ n / (1 - ρ) ∧
      IsGreatest (Set.range (profit a c ρ G))
        (1 / 2 * ((a - c) / 2) ^ 2 * (ones n ⬝ᵥ w)) := by
  set A := G + Gᵀ with hA
  set N := specNorm A with hN
  set t := ρ / N with ht
  set BA := t • A with hBA
  set BG := (2 * ρ / N) • G with hBG
  set S := 1 - BA with hS
  set M := 1 - BG with hM
  have hAs : Aᵀ = A := by simp [hA, add_comm]
  have hSs : Sᵀ = S := by
    rw [hS, hBA, Matrix.transpose_sub, Matrix.transpose_one, Matrix.transpose_smul, hAs]
  obtain ⟨w, hwS, hw1, hw2⟩ := series_exists BA (nonnegA G hG ρ hρ0.le) ρ hρ1 (hqA G ρ hρ0.le)
  obtain ⟨u, huS, hu1, hu2⟩ := series_exists BG (nonnegG G hG ρ hρ0.le) ρ hρ1 (hqG G ρ hρ0.le)
  have hSu : IsUnit S := isUnit_of_coercive BA ρ hρ1 (hqA G ρ hρ0.le)
  have hMu : IsUnit M := isUnit_of_coercive BG ρ hρ1 (hqG G ρ hρ0.le)
  have hSinv : S⁻¹ *ᵥ ones n = w := inv_ones S hSu w hw1
  have hMS : ∀ z, z ⬝ᵥ (M *ᵥ z) = z ⬝ᵥ (S *ᵥ z) := by
    intro z
    have h1 : z ⬝ᵥ (A *ᵥ z) = 2 * (z ⬝ᵥ (G *ᵥ z)) := quad_A G z
    simp only [hM, hS, hBG, hBA, Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec,
      dotProduct_sub, dotProduct_smul, smul_eq_mul]
    rw [h1]
    have : 2 * ρ / N = t * 2 := by rw [ht]; ring
    rw [this]; ring
  have hSsym : ∀ x y, (S *ᵥ x) ⬝ᵥ y = x ⬝ᵥ (S *ᵥ y) := symm_dot S hSs
  have hSw : S *ᵥ w = ones n := hw1
  set W := ones n ⬝ᵥ w with hW
  set e := (a - c) / 2 with he
  have hMz : ∀ p : Fin n → ℝ, M *ᵥ (M⁻¹ *ᵥ (a • ones n - p)) = a • ones n - p := by
    intro p
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hMu),
      Matrix.one_mulVec]
  have hpi : ∀ p : Fin n → ℝ, 2 * profit a c ρ G p =
      e ^ 2 * W - (M⁻¹ *ᵥ (a • ones n - p) - e • w) ⬝ᵥ (S *ᵥ (M⁻¹ *ᵥ (a • ones n - p) - e • w)) := by
    intro p
    rw [profit_unfold]
    change 2 * (1 / 2 * ((p - c • ones n) ⬝ᵥ (M⁻¹ *ᵥ (a • ones n - p)))) = _
    generalize hz : M⁻¹ *ᵥ (a • ones n - p) = z
    have hMz' : M *ᵥ z = a • ones n - p := by rw [← hz]; exact hMz p
    have h1 : p - c • ones n = (a - c) • ones n - M *ᵥ z := by
      rw [hMz', sub_smul]; abel
    have hones : ∀ y : Fin n → ℝ, ones n ⬝ᵥ y = w ⬝ᵥ (S *ᵥ y) := by
      intro y
      calc ones n ⬝ᵥ y = (S *ᵥ w) ⬝ᵥ y := by rw [hSw]
        _ = _ := hSsym w y
    have h2 : ((a - c) • ones n - M *ᵥ z) ⬝ᵥ z = (a - c) * (w ⬝ᵥ (S *ᵥ z)) - z ⬝ᵥ (S *ᵥ z) := by
      rw [sub_dotProduct, smul_dotProduct, smul_eq_mul, dotProduct_comm (M *ᵥ z) z, hMS z,
        hones z]
    have h3 : (z - e • w) ⬝ᵥ (S *ᵥ (z - e • w)) =
        z ⬝ᵥ (S *ᵥ z) - 2 * e * (w ⬝ᵥ (S *ᵥ z)) + e ^ 2 * W := by
      have c1 : z ⬝ᵥ ones n = w ⬝ᵥ (S *ᵥ z) := by rw [dotProduct_comm]; exact hones z
      have c2 : w ⬝ᵥ ones n = W := dotProduct_comm _ _
      simp only [Matrix.mulVec_sub, Matrix.mulVec_smul, hSw, dotProduct_sub, sub_dotProduct,
        smul_dotProduct, dotProduct_smul, smul_eq_mul, c1, c2]
      ring
    rw [h1, h2, h3, he]
    ring
  have hsol : ∀ p : Fin n → ℝ, profit a c ρ G p ≤ 1 / 2 * e ^ 2 * W := by
    intro p
    have h := hpi p
    generalize M⁻¹ *ᵥ (a • ones n - p) - e • w = d at h
    have hd := coercive BA ρ (hqA G ρ hρ0.le) d
    have hd0 : 0 ≤ d ⬝ᵥ d := Finset.sum_nonneg (fun j _ => mul_self_nonneg (d j))
    have : (1 - ρ) * (d ⬝ᵥ d) ≥ 0 := mul_nonneg (by linarith) hd0
    have hd' : 0 ≤ d ⬝ᵥ (S *ᵥ d) := le_trans this hd
    linarith
  refine ⟨w, hSinv, ?_, hw2, ?_, ?_⟩
  · have := walks_hasSum BA w hwS
    simpa [hBA, walks_smul] using this
  · have h1 := coercive BA ρ (hqA G ρ hρ0.le) w
    have h2 : w ⬝ᵥ (S *ᵥ w) = W := by rw [hSw, dotProduct_comm]
    have h3 : (1 - ρ) * (w ⬝ᵥ w) ≤ W := by rw [← h2]; exact h1
    have h4 : W ^ 2 ≤ n * (w ⬝ᵥ w) := by
      have := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin n))) (f := w)
      simpa [hW, dotProduct, ones, sq] using this
    have hW0 : 0 ≤ W := Finset.sum_nonneg (fun j _ => by simpa [ones] using le_trans zero_le_one (hw2 j))
    have hρ' : 0 < 1 - ρ := by linarith
    show W ≤ (n : ℝ) / (1 - ρ)
    rw [le_div_iff₀ hρ']
    have h5 : (1 - ρ) * W ^ 2 ≤ n * W := by
      have : (1 - ρ) * W ^ 2 ≤ (1 - ρ) * (n * (w ⬝ᵥ w)) := mul_le_mul_of_nonneg_left h4 hρ'.le
      have h6 : (n : ℝ) * ((1 - ρ) * (w ⬝ᵥ w)) ≤ n * W :=
        mul_le_mul_of_nonneg_left h3 (Nat.cast_nonneg n)
      nlinarith
    rcases hW0.eq_or_lt with h0 | h0
    · rw [← h0]; simp
    · nlinarith
  · refine ⟨⟨a • ones n - M *ᵥ (e • w), ?_⟩, ?_⟩
    · have hz : M⁻¹ *ᵥ (a • ones n - (a • ones n - M *ᵥ (e • w))) = e • w := by
        rw [sub_sub_cancel, Matrix.mulVec_mulVec,
          Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp hMu), Matrix.one_mulVec]
      have h := hpi (a • ones n - M *ᵥ (e • w))
      rw [hz, sub_self, Matrix.mulVec_zero, dotProduct_zero] at h
      linarith
    · rintro _ ⟨p, rfl⟩
      exact hsol p


lemma opt_uniform {n : ℕ} (a c ρ : ℝ) (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (G : Matrix (Fin n) (Fin n) ℝ) (hG : ∀ i j, 0 ≤ G i j) :
    ∃ u : Fin n → ℝ,
      (1 - (2 * ρ / specNorm (G + Gᵀ)) • G)⁻¹ *ᵥ ones n = u ∧
      HasSum (fun k : ℕ => (2 * ρ / specNorm (G + Gᵀ)) ^ k * walks G k) (ones n ⬝ᵥ u) ∧
      IsGreatest (Set.range fun s : ℝ => profit a c ρ G (s • ones n))
        (profit a c ρ G (uniformPrice n a c)) ∧
      profit a c ρ G (uniformPrice n a c) = 1 / 2 * ((a - c) / 2) ^ 2 * (ones n ⬝ᵥ u) := by
  set BG := (2 * ρ / specNorm (G + Gᵀ)) • G with hBG
  obtain ⟨u, huS, hu1, hu2⟩ := series_exists BG (nonnegG G hG ρ hρ0.le) ρ hρ1 (hqG G ρ hρ0.le)
  have hMu : IsUnit (1 - BG) := isUnit_of_coercive BG ρ hρ1 (hqG G ρ hρ0.le)
  have hinv : (1 - BG)⁻¹ *ᵥ ones n = u := inv_ones _ hMu u hu1
  have hWu : 0 ≤ ones n ⬝ᵥ u :=
    Finset.sum_nonneg (fun j _ => by simpa [ones] using le_trans zero_le_one (hu2 j))
  have hprof : ∀ s : ℝ, profit a c ρ G (s • ones n) = 1 / 2 * ((s - c) * (a - s)) * (ones n ⬝ᵥ u) := by
    intro s
    rw [profit_unfold]
    change 1 / 2 * ((s • ones n - c • ones n) ⬝ᵥ ((1 - BG)⁻¹ *ᵥ (a • ones n - s • ones n))) = _
    have h1 : a • ones n - s • ones n = (a - s) • ones n := by rw [sub_smul]
    rw [h1, Matrix.mulVec_smul, hinv, ← sub_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul,
      smul_eq_mul]
    ring
  refine ⟨u, hinv, ?_, ⟨⟨(a + c) / 2, rfl⟩, ?_⟩, ?_⟩
  · have := walks_hasSum BG u huS
    simpa [hBG, walks_smul] using this
  · rintro _ ⟨s, rfl⟩
    show profit a c ρ G (s • ones n) ≤ profit a c ρ G (((a + c) / 2) • ones n)
    rw [hprof, hprof]
    have : (s - c) * (a - s) ≤ ((a + c) / 2 - c) * (a - (a + c) / 2) := by
      nlinarith [sq_nonneg (s - (a + c) / 2)]
    have h2 : 1 / 2 * ((s - c) * (a - s)) ≤ 1 / 2 * (((a + c) / 2 - c) * (a - (a + c) / 2)) := by
      linarith
    exact mul_le_mul_of_nonneg_right h2 hWu
  · have : uniformPrice n a c = ((a + c) / 2) • ones n := rfl
    rw [this, hprof]
    ring

theorem solution (a c ρ : ℝ) (ha : 0 < a) (hca : c < a) (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    {n : ℕ} (G : Matrix (Fin n) (Fin n) ℝ) (hG : ∀ i j, 0 ≤ G i j) :
    (n : ℝ) / 2 * ((a - c) / 2) ^ 2 ≤ optProfit a c ρ G ∧
      optProfit a c ρ G ≤ 1 / 2 * ((a - c) / 2) ^ 2 * ((n : ℝ) / (1 - ρ)) := by
  obtain ⟨w, -, -, hw1, hw2, hmax⟩ := opt_main a c ρ hρ0 hρ1 G hG
  have hopt : optProfit a c ρ G = 1 / 2 * ((a - c) / 2) ^ 2 * (ones n ⬝ᵥ w) := hmax.csSup_eq
  rw [hopt]
  have hn : (n : ℝ) ≤ ones n ⬝ᵥ w := by
    have : ∑ _i : Fin n, (1 : ℝ) ≤ ∑ i, w i := Finset.sum_le_sum (fun i _ => hw1 i)
    simpa [dotProduct, ones] using this
  have hsq : 0 ≤ 1 / 2 * ((a - c) / 2) ^ 2 := by positivity
  constructor
  · calc (n : ℝ) / 2 * ((a - c) / 2) ^ 2 = 1 / 2 * ((a - c) / 2) ^ 2 * n := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hn hsq
  · exact mul_le_mul_of_nonneg_left hw2 hsq
