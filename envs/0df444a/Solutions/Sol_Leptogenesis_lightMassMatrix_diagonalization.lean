-- Prove2me | solution 1 for Leptogenesis.lightMassMatrix_diagonalization
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-26T09:04:11.387535+00:00
-- url     : https://prove2.me/submissions/2253081c-f219-423c-930f-d2f5a9a2c84b

import Mathlib
import Definitions.Def_Leptogenesis_SeesawDefs

set_option autoImplicit false

open Matrix ComplexOrder in
/-- Takagi vector: a complex symmetric matrix `A` has a nonzero `x` and `σ ≥ 0` with
`A x̄ = σ x`. -/
theorem lepto_takagi_vec_dg {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (hA : Aᵀ = A) :
    ∃ (x : Fin (n + 1) → ℂ) (σ : ℝ), x ≠ 0 ∧ 0 ≤ σ ∧ A *ᵥ star x = (σ : ℂ) • x := by
  have hH : (A * Aᴴ).PosSemidef := posSemidef_self_mul_conjTranspose A
  have hAH : Aᴴ = A.map star := by
    rw [conjTranspose, hA]
  have hstar : ∀ v : Fin (n + 1) → ℂ, star (A *ᵥ star v) = Aᴴ *ᵥ v := by
    intro v
    ext i
    simp only [hAH, Pi.star_apply, Matrix.mulVec, dotProduct, star_sum, star_mul', star_star,
      Matrix.map_apply]
  set y : Fin (n + 1) → ℂ := ⇑(hH.1.eigenvectorBasis 0) with hy
  set lam : ℝ := hH.1.eigenvalues 0 with hlam
  have hlam0 : 0 ≤ lam := hH.eigenvalues_nonneg 0
  have hey : (A * Aᴴ) *ᵥ y = lam • y := hH.1.mulVec_eigenvectorBasis 0
  have hy0 : y ≠ 0 := by
    intro h
    apply (hH.1.eigenvectorBasis).orthonormal.ne_zero 0
    ext i
    simpa using congrFun h i
  set z : Fin (n + 1) → ℂ := A *ᵥ star y with hz
  have hAz : A *ᵥ star z = (lam : ℂ) • y := by
    rw [hz, hstar, mulVec_mulVec, hey]
    ext i
    simp [Complex.real_smul]
  rcases hlam0.eq_or_lt with hl | hl
  · have hAy : Aᴴ *ᵥ y = 0 := by
      have h1 : star (Aᴴ *ᵥ y) ⬝ᵥ (Aᴴ *ᵥ y) = star y ⬝ᵥ ((A * Aᴴ) *ᵥ y) := by
        rw [star_mulVec, conjTranspose_conjTranspose, ← mulVec_mulVec]
        simp only [dotProduct_mulVec]
      rw [hey, ← hl, zero_smul, dotProduct_zero] at h1
      exact dotProduct_star_self_eq_zero.mp h1
    have hz0 : z = 0 := by
      have h2 : star z = 0 := by rw [hz, hstar, hAy]
      have h3 := congrArg star h2
      rwa [star_star, star_zero] at h3
    refine ⟨y, 0, hy0, le_refl _, ?_⟩
    rw [← hz, hz0]
    simp
  · set σ : ℝ := Real.sqrt lam with hσdef
    have hσ : 0 < σ := Real.sqrt_pos.mpr hl
    have hσσ : (σ : ℂ) * σ = lam := by rw [← Complex.ofReal_mul, Real.mul_self_sqrt hl.le]
    have hσC : (σ : ℂ) ≠ 0 := by exact_mod_cast hσ.ne'
    have e2 : (σ : ℂ) * (σ : ℂ)⁻¹ = 1 := mul_inv_cancel₀ hσC
    have hsinv : star ((σ : ℂ)⁻¹) = (σ : ℂ)⁻¹ := by
      rw [star_inv₀, Complex.star_def, Complex.conj_ofReal]
    by_cases hx1 : y + (σ : ℂ)⁻¹ • z = 0
    · refine ⟨Complex.I • y, σ, smul_ne_zero Complex.I_ne_zero hy0, hσ.le, ?_⟩
      have hzy : z = -(σ : ℂ) • y := by
        ext i
        have e := congrFun hx1 i
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at e
        simp only [Pi.smul_apply, smul_eq_mul]
        linear_combination (σ : ℂ) * e - z i * e2
      rw [star_smul, mulVec_smul, ← hz, hzy]
      ext i
      simp only [Pi.smul_apply, smul_eq_mul, Complex.star_def, Complex.conj_I]
      ring
    · refine ⟨y + (σ : ℂ)⁻¹ • z, σ, hx1, hσ.le, ?_⟩
      rw [star_add, star_smul, mulVec_add, mulVec_smul, ← hz, hAz, hsinv]
      ext i
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      linear_combination (-(z i) + (σ : ℂ) * y i) * e2 - (σ : ℂ)⁻¹ * y i * hσσ

open Matrix in
/-- Extend a unit vector of `ℂⁿ⁺¹` to a unitary matrix whose first column is that vector. -/
theorem lepto_ext_dg {n : ℕ} (u : EuclideanSpace ℂ (Fin (n + 1))) (hu1 : ‖u‖ = 1) :
    ∃ W0 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ, W0 ∈ unitaryGroup (Fin (n + 1)) ℂ ∧
      ∀ i, W0 i 0 = u i := by
  have hon : Orthonormal ℂ (({0} : Set (Fin (n + 1))).domRestrict
      (fun _ : Fin (n + 1) => u)) := by
    rw [orthonormal_iff_ite]
    intro i j
    have hij : i = j := Subsingleton.elim i j
    subst hij
    simp [Set.domRestrict, inner_self_eq_norm_sq_to_K, hu1]
  obtain ⟨b, hb⟩ := hon.exists_orthonormalBasis_extension_of_card_eq
    (by rw [finrank_euclideanSpace])
  have hb0 : b 0 = u := hb 0 rfl
  refine ⟨(EuclideanSpace.basisFun (Fin (n + 1)) ℂ).toBasis.toMatrix b.toBasis,
    (EuclideanSpace.basisFun (Fin (n + 1)) ℂ).toMatrix_orthonormalBasis_mem_unitary b, ?_⟩
  intro i
  rw [Module.Basis.toMatrix_apply, OrthonormalBasis.coe_toBasis, hb0]
  rfl

open Matrix in
/-- Block step: if `B` has first row/column `σ e₀` and its lower block is `W' D' W'ᵀ`, then
`B = V D Vᵀ` with `V = 1 ⊕ W'` unitary and `D = diag(σ, D')`. -/
theorem lepto_block_dg {n : ℕ} (B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (σ : ℝ)
    (hB00 : B 0 0 = σ) (hBs0 : ∀ i : Fin n, B i.succ 0 = 0) (hB0s : ∀ j : Fin n, B 0 j.succ = 0)
    (W' : Matrix (Fin n) (Fin n) ℂ) (d' : Fin n → ℝ) (hW' : W' ∈ unitaryGroup (Fin n) ℂ)
    (hB' : B.submatrix Fin.succ Fin.succ = W' * diagonal (fun i => (d' i : ℂ)) * W'ᵀ) :
    ∃ V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ, V ∈ unitaryGroup (Fin (n + 1)) ℂ ∧
      B = V * diagonal (fun i => ((Fin.cons σ d' : Fin (n + 1) → ℝ) i : ℂ)) * Vᵀ := by
  have hW'1 : W' * W'ᴴ = 1 := by
    have := (Matrix.mem_unitaryGroup_iff).mp hW'
    simpa [Matrix.star_eq_conjTranspose] using this
  refine ⟨Matrix.of fun i j => Fin.cases (motive := fun _ => ℂ)
    (Fin.cases (motive := fun _ => ℂ) 1 (fun _ => 0) j)
    (fun i' => Fin.cases (motive := fun _ => ℂ) 0 (fun j' => W' i' j') j) i, ?_, ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose]
    ext i j
    rw [Matrix.mul_apply, Fin.sum_univ_succ]
    refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j
    · simp
    · rw [Matrix.one_apply_ne (Fin.succ_ne_zero j).symm]
      simp
    · simp
    · have h1 := congrFun (congrFun hW'1 i) j
      simp only [Matrix.mul_apply, Matrix.conjTranspose_apply] at h1
      simpa [Matrix.one_apply] using h1
  · ext i j
    rw [Matrix.mul_apply, Fin.sum_univ_succ]
    simp only [Matrix.mul_diagonal, Matrix.transpose_apply]
    refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j
    · simp [hB00]
    · simp [hB0s]
    · simp [hBs0]
    · have h1 := congrFun (congrFun hB' i) j
      simp only [Matrix.submatrix_apply] at h1
      rw [h1, Matrix.mul_apply]
      simp only [Matrix.mul_diagonal, Matrix.transpose_apply]
      simp

open Matrix in
/-- Autonne–Takagi factorisation: every complex symmetric matrix is `W D Wᵀ` with `W` unitary
and `D` real, nonnegative, diagonal. -/
theorem lepto_takagi_dg : ∀ (n : ℕ) (A : Matrix (Fin n) (Fin n) ℂ), Aᵀ = A →
    ∃ (W : Matrix (Fin n) (Fin n) ℂ) (d : Fin n → ℝ), W ∈ unitaryGroup (Fin n) ℂ ∧
      (∀ i, 0 ≤ d i) ∧ A = W * diagonal (fun i => (d i : ℂ)) * Wᵀ
  | 0, A, _ => ⟨1, fun _ => 0, one_mem _, fun _ => le_refl _, by ext i; exact Fin.elim0 i⟩
  | n + 1, A, hA => by
    obtain ⟨x, σ, hx0, hσ, hx⟩ := lepto_takagi_vec_dg A hA
    obtain ⟨xe, hxe⟩ : ∃ xe : EuclideanSpace ℂ (Fin (n + 1)), xe = WithLp.toLp 2 x := ⟨_, rfl⟩
    have hxe0 : xe ≠ 0 := by
      intro h
      apply hx0
      ext i
      have h1 := congrArg (fun w : EuclideanSpace ℂ (Fin (n + 1)) => w i) h
      simpa [hxe] using h1
    obtain ⟨c, hc⟩ : ∃ c : ℂ, c = ((‖xe‖ : ℂ))⁻¹ := ⟨_, rfl⟩
    obtain ⟨u, hu⟩ : ∃ u : EuclideanSpace ℂ (Fin (n + 1)), u = c • xe := ⟨_, rfl⟩
    have hu1 : ‖u‖ = 1 := by
      rw [hu, hc]
      exact norm_smul_inv_norm hxe0
    have hux : (⇑u : Fin (n + 1) → ℂ) = c • x := by
      ext i
      simp [hu, hxe]
    have hcs : star c = c := by rw [hc, star_inv₀, Complex.star_def, Complex.conj_ofReal]
    have huA : A *ᵥ star (⇑u : Fin (n + 1) → ℂ) = (σ : ℂ) • (⇑u : Fin (n + 1) → ℂ) := by
      rw [hux, star_smul, hcs, mulVec_smul, hx, smul_comm]
    obtain ⟨W0, hW0, hW0col⟩ := lepto_ext_dg u hu1
    have hW1 : W0ᴴ * W0 = 1 := by
      have := (Matrix.mem_unitaryGroup_iff').mp hW0
      simpa [Matrix.star_eq_conjTranspose] using this
    have hW2 : W0 * W0ᴴ = 1 := by
      have := (Matrix.mem_unitaryGroup_iff).mp hW0
      simpa [Matrix.star_eq_conjTranspose] using this
    obtain ⟨B, hBdef⟩ : ∃ B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ, B = W0ᴴ * A * (W0ᴴ)ᵀ :=
      ⟨_, rfl⟩
    have hBsym : Bᵀ = B := by
      rw [hBdef, transpose_mul, transpose_mul, transpose_transpose, hA, Matrix.mul_assoc]
    have hAB : A = W0 * B * W0ᵀ := by
      have h3 : (W0ᴴ)ᵀ * W0ᵀ = 1 := by
        rw [← transpose_mul, hW2, transpose_one]
      calc A = (W0 * W0ᴴ) * A * ((W0ᴴ)ᵀ * W0ᵀ) := by rw [hW2, h3, Matrix.one_mul, Matrix.mul_one]
        _ = W0 * B * W0ᵀ := by rw [hBdef]; simp only [Matrix.mul_assoc]
    have hcol : W0 *ᵥ Pi.single 0 1 = ⇑u := by
      ext i
      rw [mulVec_single_one]
      exact hW0col i
    have hcolc : (W0ᴴ)ᵀ *ᵥ Pi.single 0 1 = star ⇑u := by
      ext i
      rw [mulVec_single_one]
      simp [hW0col]
    have hBe0 : B *ᵥ Pi.single 0 1 = (σ : ℂ) • Pi.single 0 1 := by
      rw [hBdef, ← mulVec_mulVec, ← mulVec_mulVec, hcolc, huA, mulVec_smul, ← hcol,
        mulVec_mulVec, hW1, one_mulVec]
    have hBcol : ∀ i, B i 0 = (σ : ℂ) * (Pi.single 0 1 : Fin (n + 1) → ℂ) i := by
      intro i
      have h1 := congrFun hBe0 i
      rw [mulVec_single_one] at h1
      simpa using h1
    have hB00 : B 0 0 = σ := by
      rw [hBcol 0]
      simp
    have hBs0 : ∀ i : Fin n, B i.succ 0 = 0 := by
      intro i
      rw [hBcol]
      simp
    have hB0s : ∀ j : Fin n, B 0 j.succ = 0 := by
      intro j
      have h1 := congrFun (congrFun hBsym j.succ) 0
      rw [transpose_apply] at h1
      rw [h1, hBs0 j]
    have hB'sym : (B.submatrix Fin.succ Fin.succ)ᵀ = B.submatrix Fin.succ Fin.succ := by
      rw [transpose_submatrix, hBsym]
    obtain ⟨W', d', hW', hd', hB'⟩ := lepto_takagi_dg n _ hB'sym
    obtain ⟨V, hV, hBV⟩ := lepto_block_dg B σ hB00 hBs0 hB0s W' d' hW' hB'
    refine ⟨W0 * V, Fin.cons σ d', mul_mem hW0 hV, ?_, ?_⟩
    · intro i
      refine Fin.cases ?_ (fun i => ?_) i
      · simpa using hσ
      · simpa using hd' i
    · rw [hAB, hBV, transpose_mul]
      simp only [Matrix.mul_assoc]

open Leptogenesis Matrix in
theorem solution (v : ℝ) (hv : 0 < v) (M : Fin 3 → ℝ)
    (hM : ∀ k, 0 < M k) (lam : Matrix (Fin 3) (Fin 3) ℂ) :
    ∃ (U : Matrix (Fin 3) (Fin 3) ℂ) (masses : Fin 3 → ℝ),
      IsLightMassDiagonalization (lightMassMatrix v M lam) U masses := by
  have hsym : (lightMassMatrix v M lam)ᵀ = lightMassMatrix v M lam := by
    ext i j
    simp only [transpose_apply, lightMassMatrix]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    ring
  obtain ⟨W, d, hW, hd, hWd⟩ := lepto_takagi_dg 3 _ hsym
  have hW2 : W * Wᴴ = 1 := by
    have := (Matrix.mem_unitaryGroup_iff).mp hW
    simpa [Matrix.star_eq_conjTranspose] using this
  refine ⟨W.map (starRingEnd ℂ), d, ?_, hd, ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose]
    have hc : (W.map (starRingEnd ℂ))ᴴ = Wᵀ := by
      ext i j
      simp
    have hc2 : W.map (starRingEnd ℂ) = (Wᴴ)ᵀ := by
      ext i j
      simp
    rw [hc, hc2, ← transpose_mul, hW2, transpose_one]
  · have hc : (W.map (starRingEnd ℂ))ᴴ = Wᵀ := by
      ext i j
      simp
    have hcc : (W.map (starRingEnd ℂ)).map (starRingEnd ℂ) = W := by
      ext i j
      simp
    rw [hc, hcc]
    exact hWd
