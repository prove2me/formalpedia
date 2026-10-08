-- Prove2me | solution 1 for HryniewiczCriterion.graphUnitary4_positive_path
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-07T08:39:38.723552+00:00
-- url     : https://prove2.me/submissions/23c860bf-8865-44f8-a799-4ddff28ae1b7

import Definitions.Def_HryniewiczCriterion_GraphAngle
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic
import Mathlib.Analysis.Matrix.PosDef

open HryniewiczCriterion
open scoped ContDiff ComplexOrder

/-!
# Leaf C1, calculus: entrywise derivatives of matrix-valued paths

`HasMatDerivAt M M' t` says every entry of `s ↦ M s` has derivative the matching entry of `M'`
at `t`. Product rule, conjugate transpose, and the inverse `(M⁻¹)' = -M⁻¹ M' M⁻¹` (Cramer's rule
gives differentiability, the product rule gives the value).
-/

namespace HryniewiczCriterion

open Matrix

noncomputable section

variable {n : Type} [Fintype n] [DecidableEq n]

/-- Entrywise derivative of a path of matrices. -/
def HasMatDerivAt {𝕜 : Type} [NontriviallyNormedField 𝕜] [NormedAlgebra ℝ 𝕜]
    (M : ℝ → Matrix n n 𝕜) (M' : Matrix n n 𝕜) (t : ℝ) : Prop :=
  ∀ i j, HasDerivAt (fun s => M s i j) (M' i j) t

section general

variable {𝕜 : Type} [NontriviallyNormedField 𝕜] [NormedAlgebra ℝ 𝕜]

lemma HasMatDerivAt.mul {M N : ℝ → Matrix n n 𝕜} {M' N' : Matrix n n 𝕜} {t : ℝ}
    (hM : HasMatDerivAt M M' t) (hN : HasMatDerivAt N N' t) :
    HasMatDerivAt (fun s => M s * N s) (M' * N t + M t * N') t := by
  intro i j
  simp only [Matrix.mul_apply, Matrix.add_apply, ← Finset.sum_add_distrib]
  exact HasDerivAt.fun_sum fun k _ => (hM i k).mul (hN k j)

lemma HasMatDerivAt.add {M N : ℝ → Matrix n n 𝕜} {M' N' : Matrix n n 𝕜} {t : ℝ}
    (hM : HasMatDerivAt M M' t) (hN : HasMatDerivAt N N' t) :
    HasMatDerivAt (fun s => M s + N s) (M' + N') t :=
  fun i j => (hM i j).add (hN i j)

lemma HasMatDerivAt.const (C : Matrix n n 𝕜) (t : ℝ) :
    HasMatDerivAt (fun _ => C) 0 t :=
  fun i j => hasDerivAt_const t (C i j)

lemma HasMatDerivAt.unique {M : ℝ → Matrix n n 𝕜} {M₁ M₂ : Matrix n n 𝕜} {t : ℝ}
    (h₁ : HasMatDerivAt M M₁ t) (h₂ : HasMatDerivAt M M₂ t) : M₁ = M₂ := by
  ext i j; exact (h₁ i j).unique (h₂ i j)

end general

lemma HasMatDerivAt.conjTranspose {M : ℝ → Matrix n n ℂ} {M' : Matrix n n ℂ} {t : ℝ}
    (hM : HasMatDerivAt M M' t) : HasMatDerivAt (fun s => (M s)ᴴ) M'ᴴ t :=
  fun i j => by simpa [Matrix.conjTranspose_apply] using (hM j i).star

lemma differentiableAt_det {M : ℝ → Matrix n n ℂ} {t : ℝ}
    (hM : ∀ i j, DifferentiableAt ℝ (fun s => M s i j) t) :
    DifferentiableAt ℝ (fun s => (M s).det) t := by
  simp only [Matrix.det_apply']
  fun_prop

lemma differentiableAt_inv_apply {M : ℝ → Matrix n n ℂ} {t : ℝ}
    (hM : ∀ i j, DifferentiableAt ℝ (fun s => M s i j) t) (ht : (M t).det ≠ 0) (i j : n) :
    DifferentiableAt ℝ (fun s => (M s)⁻¹ i j) t := by
  simp only [Matrix.inv_def, Matrix.smul_apply, Ring.inverse_eq_inv', smul_eq_mul,
    Matrix.adjugate_apply]
  refine ((differentiableAt_det hM).inv ht).mul (differentiableAt_det fun r c => ?_)
  simp only [Matrix.updateRow_apply]
  split_ifs
  · exact differentiableAt_const _
  · exact hM r c

lemma HasMatDerivAt.inv {M : ℝ → Matrix n n ℂ} {M' : Matrix n n ℂ} {t : ℝ}
    (hM : HasMatDerivAt M M' t) (hdet : ∀ s, (M s).det ≠ 0) :
    HasMatDerivAt (fun s => (M s)⁻¹) (-((M t)⁻¹ * M' * (M t)⁻¹)) t := by
  have hd : HasMatDerivAt (fun s => (M s)⁻¹) (Matrix.of fun i j => deriv (fun s => (M s)⁻¹ i j) t) t :=
    fun i j => (differentiableAt_inv_apply (fun a b => (hM a b).differentiableAt) (hdet t) i j).hasDerivAt
  have hprod := hM.mul hd
  have h1 : HasMatDerivAt (fun s => M s * (M s)⁻¹) 0 t := by
    have : (fun s => M s * (M s)⁻¹) = fun _ => (1 : Matrix n n ℂ) := by
      funext s; exact Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr (hdet s))
    rw [this]; exact HasMatDerivAt.const _ t
  have heq := hprod.unique h1
  have hu : IsUnit (M t).det := isUnit_iff_ne_zero.mpr (hdet t)
  have key : (Matrix.of fun i j => deriv (fun s => (M s)⁻¹ i j) t) = -((M t)⁻¹ * M' * (M t)⁻¹) := by
    have h2 : M t * (Matrix.of fun i j => deriv (fun s => (M s)⁻¹ i j) t) = -(M' * (M t)⁻¹) :=
      eq_neg_of_add_eq_zero_right heq
    calc (Matrix.of fun i j => deriv (fun s => (M s)⁻¹ i j) t)
        = (M t)⁻¹ * (M t * (Matrix.of fun i j => deriv (fun s => (M s)⁻¹ i j) t)) := by
          rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hu, Matrix.one_mul]
      _ = -((M t)⁻¹ * M' * (M t)⁻¹) := by rw [h2, Matrix.mul_neg, Matrix.mul_assoc]
  rwa [key] at hd

end

end HryniewiczCriterion

/-!
# Leaf C1, algebra: the graph unitary of a symplectic matrix

`graphBasis4 g = E + F g` with constant `E, F`. For `gᵀ K g = K` (`K = -J`) the Gram matrices of
`A = graphBasis4 g` and `B = Ā` are both `1 + gᵀ g`, so `W = (Aᴴ)⁻¹ Bᴴ = lagUnitary A` is unitary.
Along a path, `W' = i Q W` with `Q = (Aᴴ)⁻¹ N A⁻¹`, `N = -i (B'ᴴ B - A'ᴴ A)`.
-/

namespace HryniewiczCriterion

open Matrix Complex

open scoped ComplexOrder

noncomputable section

/-- Real matrices as complex matrices. -/
abbrev cmH : Matrix (Fin 4) (Fin 4) ℝ →+* Matrix (Fin 4) (Fin 4) ℂ := Complex.ofRealHom.mapMatrix

/-- `K = -J`, the matrix of `ω₀`. -/
def omK : Matrix (Fin 4) (Fin 4) ℝ := !![0, 1, 0, 0; -1, 0, 0, 0; 0, 0, 0, 1; 0, 0, -1, 0]

def gbE : Matrix (Fin 4) (Fin 4) ℂ := !![1, -I, 0, 0; 0, 0, 1, -I; 0, 0, 0, 0; 0, 0, 0, 0]
def gbF : Matrix (Fin 4) (Fin 4) ℂ := !![0, 0, 0, 0; 0, 0, 0, 0; 1, I, 0, 0; 0, 0, 1, I]
def gbEb : Matrix (Fin 4) (Fin 4) ℂ := !![1, I, 0, 0; 0, 0, 1, I; 0, 0, 0, 0; 0, 0, 0, 0]
def gbFb : Matrix (Fin 4) (Fin 4) ℂ := !![0, 0, 0, 0; 0, 0, 0, 0; 1, -I, 0, 0; 0, 0, 1, -I]

lemma symplJ4_eq : symplJ4 = -omK := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [symplJ4, omK]

lemma omK_transpose : omKᵀ = -omK := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [omK]

lemma omK_mul_self : omK * omK = -1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [omK, Matrix.mul_apply, Fin.sum_univ_four]

lemma graphBasis4_eq_add (g : Matrix (Fin 4) (Fin 4) ℝ) : graphBasis4 g = gbE + gbF * cmH g := by
  ext r k; fin_cases r <;> fin_cases k <;>
    simp [graphBasis4, gbE, gbF, Matrix.mul_apply, Fin.sum_univ_four, Matrix.vecMul, dotProduct]

lemma graphBasis4_map_star (g : Matrix (Fin 4) (Fin 4) ℝ) :
    (graphBasis4 g).map (starRingEnd ℂ) = gbEb + gbFb * cmH g := by
  ext r k; fin_cases r <;> fin_cases k <;>
    simp [graphBasis4, gbEb, gbFb, Matrix.mul_apply, Fin.sum_univ_four, Matrix.vecMul,
      dotProduct] <;> ring

lemma conjTranspose_map_star (A : Matrix (Fin 4) (Fin 4) ℂ) : (A.map (starRingEnd ℂ))ᴴ = Aᵀ := by
  ext i j; simp [Matrix.conjTranspose_apply]

lemma cmH_conjTranspose (g : Matrix (Fin 4) (Fin 4) ℝ) : (cmH g)ᴴ = cmH gᵀ := by
  ext i j; simp [Matrix.conjTranspose_apply]

lemma gbE_gram : gbEᴴ * gbE = 1 - I • cmH omK := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [gbE, omK, Matrix.mul_apply, Fin.sum_univ_four, Matrix.conjTranspose_apply]
lemma gbF_gram : gbFᴴ * gbF = 1 + I • cmH omK := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [gbF, omK, Matrix.mul_apply, Fin.sum_univ_four, Matrix.conjTranspose_apply]
lemma gbEb_gram : gbEbᴴ * gbEb = 1 + I • cmH omK := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [gbEb, omK, Matrix.mul_apply, Fin.sum_univ_four, Matrix.conjTranspose_apply]
lemma gbFb_gram : gbFbᴴ * gbFb = 1 - I • cmH omK := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [gbFb, omK, Matrix.mul_apply, Fin.sum_univ_four, Matrix.conjTranspose_apply]
lemma gbE_F : gbEᴴ * gbF = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [gbE, gbF, Matrix.mul_apply, Fin.sum_univ_four, Matrix.conjTranspose_apply]
lemma gbF_E : gbFᴴ * gbE = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [gbE, gbF, Matrix.mul_apply, Fin.sum_univ_four, Matrix.conjTranspose_apply]
lemma gbEb_Fb : gbEbᴴ * gbFb = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [gbEb, gbFb, Matrix.mul_apply, Fin.sum_univ_four, Matrix.conjTranspose_apply]
lemma gbFb_Eb : gbFbᴴ * gbEb = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [gbEb, gbFb, Matrix.mul_apply, Fin.sum_univ_four, Matrix.conjTranspose_apply]

/-- Gram matrix of `E + F G` for a block-orthogonal pair. -/
lemma gram_add {E F G : Matrix (Fin 4) (Fin 4) ℂ} (hEF : Eᴴ * F = 0) (hFE : Fᴴ * E = 0) :
    (E + F * G)ᴴ * (E + F * G) = Eᴴ * E + Gᴴ * (Fᴴ * F) * G := by
  rw [conjTranspose_add, conjTranspose_mul, Matrix.add_mul, Matrix.mul_add, Matrix.mul_add,
    ← Matrix.mul_assoc Eᴴ F G, hEF, Matrix.zero_mul, add_zero, Matrix.mul_assoc Gᴴ Fᴴ E, hFE,
    Matrix.mul_zero, zero_add, Matrix.mul_assoc Gᴴ Fᴴ, Matrix.mul_assoc Gᴴ, ← Matrix.mul_assoc Fᴴ]

lemma gram_graphBasis4 {g : Matrix (Fin 4) (Fin 4) ℝ} (hg : gᵀ * omK * g = omK) :
    (graphBasis4 g)ᴴ * graphBasis4 g = cmH (1 + gᵀ * g) := by
  rw [graphBasis4_eq_add, gram_add gbE_F gbF_E, gbE_gram, gbF_gram, cmH_conjTranspose]
  have h : cmH (gᵀ * omK * g) = cmH omK := by rw [hg]
  simp only [map_mul, map_add, map_one] at h ⊢
  rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.mul_smul, Matrix.smul_mul, h]
  abel

lemma gram_graphBasis4_star {g : Matrix (Fin 4) (Fin 4) ℝ} (hg : gᵀ * omK * g = omK) :
    ((graphBasis4 g).map (starRingEnd ℂ))ᴴ * (graphBasis4 g).map (starRingEnd ℂ) =
      cmH (1 + gᵀ * g) := by
  rw [graphBasis4_map_star, gram_add gbEb_Fb gbFb_Eb, gbEb_gram, gbFb_gram, cmH_conjTranspose]
  have h : cmH (gᵀ * omK * g) = cmH omK := by rw [hg]
  simp only [map_mul, map_add, map_one] at h ⊢
  rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.mul_smul, Matrix.smul_mul, h]
  abel

lemma posDef_one_add_transpose_mul (g : Matrix (Fin 4) (Fin 4) ℝ) : (1 + gᵀ * g).PosDef := by
  have h1 : (1 : Matrix (Fin 4) (Fin 4) ℝ).PosDef := PosDef.one
  have h2 : (gᵀ * g).PosSemidef := by
    simpa [conjTranspose_eq_transpose_of_trivial] using posSemidef_conjTranspose_mul_self g
  exact h1.add_posSemidef h2

lemma det_cmH (M : Matrix (Fin 4) (Fin 4) ℝ) : (cmH M).det = ((M.det : ℝ) : ℂ) :=
  (RingHom.map_det Complex.ofRealHom M).symm

lemma det_ne_zero_of_gram {A : Matrix (Fin 4) (Fin 4) ℂ} {M : Matrix (Fin 4) (Fin 4) ℝ}
    (h : Aᴴ * A = cmH M) (hM : M.PosDef) : A.det ≠ 0 := by
  intro h0
  have := congrArg Matrix.det h
  rw [det_mul, h0, mul_zero, det_cmH] at this
  exact (hM.det_pos.ne') (by exact_mod_cast this.symm)

lemma gram_aux {A B : Matrix (Fin 4) (Fin 4) ℂ} (hB : B.det ≠ 0) (h : Aᴴ * A = Bᴴ * B) :
    A⁻¹ * ((Aᴴ)⁻¹ * Bᴴ) = B⁻¹ := by
  have hBh : IsUnit Bᴴ.det := by rw [det_conjTranspose]; exact (isUnit_iff_ne_zero.mpr hB).star
  rw [← Matrix.mul_assoc, ← Matrix.mul_inv_rev, h, Matrix.mul_inv_rev, Matrix.mul_assoc,
    Matrix.nonsing_inv_mul _ hBh, Matrix.mul_one]

/-- `W = (Aᴴ)⁻¹ Bᴴ` is unitary when `Aᴴ A = Bᴴ B` and `B` is invertible. -/
lemma unitary_of_gram {A B : Matrix (Fin 4) (Fin 4) ℂ} (hB : B.det ≠ 0)
    (h : Aᴴ * A = Bᴴ * B) : ((Aᴴ)⁻¹ * Bᴴ)ᴴ * ((Aᴴ)⁻¹ * Bᴴ) = 1 := by
  rw [conjTranspose_mul, conjTranspose_conjTranspose, conjTranspose_nonsing_inv,
    conjTranspose_conjTranspose, Matrix.mul_assoc, gram_aux hB h,
    Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hB)]

/-- The key identity `W' = i Q W` with `Q = (Aᴴ)⁻¹ N A⁻¹`, `N = -i (B'ᴴ B - A'ᴴ A)`. -/
lemma deriv_identity {A B A' B' : Matrix (Fin 4) (Fin 4) ℂ} (hA : A.det ≠ 0) (hB : B.det ≠ 0)
    (h : Aᴴ * A = Bᴴ * B) :
    -((Aᴴ)⁻¹ * A'ᴴ * (Aᴴ)⁻¹) * Bᴴ + (Aᴴ)⁻¹ * B'ᴴ =
      I • ((Aᴴ)⁻¹ * ((-I) • (B'ᴴ * B - A'ᴴ * A)) * A⁻¹ * ((Aᴴ)⁻¹ * Bᴴ)) := by
  have hA' : IsUnit A.det := isUnit_iff_ne_zero.mpr hA
  have hB' : IsUnit B.det := isUnit_iff_ne_zero.mpr hB
  have hAB := gram_aux hB h
  have hAB2 : A * B⁻¹ = (Aᴴ)⁻¹ * Bᴴ := by
    rw [← hAB, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hA', Matrix.one_mul]
  have hII : I * -I = 1 := by rw [mul_neg, I_mul_I, neg_neg]
  calc -((Aᴴ)⁻¹ * A'ᴴ * (Aᴴ)⁻¹) * Bᴴ + (Aᴴ)⁻¹ * B'ᴴ
      = (Aᴴ)⁻¹ * B'ᴴ - (Aᴴ)⁻¹ * (A'ᴴ * ((Aᴴ)⁻¹ * Bᴴ)) := by
        simp only [Matrix.neg_mul, Matrix.mul_assoc]; abel
    _ = (Aᴴ)⁻¹ * ((B'ᴴ * B - A'ᴴ * A) * B⁻¹) := by
        simp only [Matrix.sub_mul, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hB', hAB2,
          Matrix.mul_one, Matrix.mul_sub]
    _ = (Aᴴ)⁻¹ * (B'ᴴ * B - A'ᴴ * A) * A⁻¹ * ((Aᴴ)⁻¹ * Bᴴ) := by
        rw [Matrix.mul_assoc _ A⁻¹, hAB, Matrix.mul_assoc]
    _ = I • ((Aᴴ)⁻¹ * ((-I) • (B'ᴴ * B - A'ᴴ * A)) * A⁻¹ * ((Aᴴ)⁻¹ * Bᴴ)) := by
        rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_mul, smul_smul, hII, one_smul]

/-- A real positive definite matrix is positive definite as a complex matrix. -/
lemma posDef_cmH {M : Matrix (Fin 4) (Fin 4) ℝ} (hM : M.PosDef) : (cmH M).PosDef := by
  have hs : Mᵀ = M := by
    have := hM.1; rwa [IsHermitian, conjTranspose_eq_transpose_of_trivial] at this
  refine PosDef.of_dotProduct_mulVec_pos ?_ fun x hx => ?_
  · rw [IsHermitian, cmH_conjTranspose, hs]
  set u : Fin 4 → ℝ := fun i => (x i).re
  set v : Fin 4 → ℝ := fun i => (x i).im
  have hsym : ∀ i j, M j i = M i j := fun i j => by
    rw [← Matrix.transpose_apply M i j, hs]
  have key : star x ⬝ᵥ (cmH M *ᵥ x) = ((u ⬝ᵥ (M *ᵥ u) + v ⬝ᵥ (M *ᵥ v) : ℝ) : ℂ) := by
    apply Complex.ext
    · simp [dotProduct, mulVec, Fin.sum_univ_four, u, v]; ring
    · simp [dotProduct, mulVec, Fin.sum_univ_four, u, v, hsym 0 1, hsym 0 2, hsym 0 3,
        hsym 1 2, hsym 1 3, hsym 2 3]; ring
  rw [key, Complex.zero_lt_real]
  have hu : 0 ≤ u ⬝ᵥ (M *ᵥ u) := by
    by_cases h : u = 0
    · simp [h]
    · simpa using (hM.dotProduct_mulVec_pos h).le
  have hv : 0 ≤ v ⬝ᵥ (M *ᵥ v) := by
    by_cases h : v = 0
    · simp [h]
    · simpa using (hM.dotProduct_mulVec_pos h).le
  by_cases h : u = 0
  · have hv0 : v ≠ 0 := by
      intro hv0; apply hx; funext i; apply Complex.ext
      · simpa [u] using congrFun h i
      · simpa [v] using congrFun hv0 i
    have := hM.dotProduct_mulVec_pos hv0
    simp only [star_trivial] at this
    linarith
  · have := hM.dotProduct_mulVec_pos h
    simp only [star_trivial] at this
    linarith

end

end HryniewiczCriterion

/-!
# Leaf C1: the graph unitary of a positive symplectic path is a positive unitary path

`Ŷ' = J S Ŷ`, `Ŷ(0) = 1` keeps `Ŷᵀ K Ŷ = K`. With `A = graphBasis4 Ŷ`, `B = Ā`:
`graphUnitary4 Ŷ = (Aᴴ)⁻¹ Bᴴ · W₁⁻¹` is unitary and `V' = i Q V` with
`Q = (A⁻¹)ᴴ (2 Ŷᵀ S Ŷ) A⁻¹ > 0`.
-/

namespace HryniewiczCriterion

open Matrix Complex

open scoped ComplexOrder

noncomputable section

lemma HasMatDerivAt.transpose {M : ℝ → Matrix (Fin 4) (Fin 4) ℝ} {M' : Matrix (Fin 4) (Fin 4) ℝ}
    {t : ℝ} (h : HasMatDerivAt M M' t) : HasMatDerivAt (fun s => (M s)ᵀ) M'ᵀ t :=
  fun i j => h j i

lemma HasMatDerivAt.cmH {M : ℝ → Matrix (Fin 4) (Fin 4) ℝ} {M' : Matrix (Fin 4) (Fin 4) ℝ}
    {t : ℝ} (h : HasMatDerivAt M M' t) : HasMatDerivAt (fun s => cmH (M s)) (cmH M') t :=
  fun i j => by simpa using (h i j).ofReal_comp

lemma lagUnitary_eq' {A : Matrix (Fin 4) (Fin 4) ℂ} (hA : A.det ≠ 0) :
    lagUnitary A = (Aᴴ)⁻¹ * (A.map (starRingEnd ℂ))ᴴ := by
  unfold lagUnitary
  rw [conjTranspose_map_star, Matrix.mul_inv_rev, ← Matrix.mul_assoc,
    Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hA), Matrix.one_mul]

lemma graphBasis4_det_ne_zero {g : Matrix (Fin 4) (Fin 4) ℝ} (hg : gᵀ * omK * g = omK) :
    (graphBasis4 g).det ≠ 0 :=
  det_ne_zero_of_gram (gram_graphBasis4 hg) (posDef_one_add_transpose_mul g)

lemma graphBasis4_star_det_ne_zero {g : Matrix (Fin 4) (Fin 4) ℝ} (hg : gᵀ * omK * g = omK) :
    ((graphBasis4 g).map (starRingEnd ℂ)).det ≠ 0 :=
  det_ne_zero_of_gram (gram_graphBasis4_star hg) (posDef_one_add_transpose_mul g)

lemma gram_eq {g : Matrix (Fin 4) (Fin 4) ℝ} (hg : gᵀ * omK * g = omK) :
    (graphBasis4 g)ᴴ * graphBasis4 g =
      ((graphBasis4 g).map (starRingEnd ℂ))ᴴ * (graphBasis4 g).map (starRingEnd ℂ) := by
  rw [gram_graphBasis4 hg, gram_graphBasis4_star hg]

lemma lagUnitary_graphBasis4_unitary {g : Matrix (Fin 4) (Fin 4) ℝ} (hg : gᵀ * omK * g = omK) :
    (lagUnitary (graphBasis4 g))ᴴ * lagUnitary (graphBasis4 g) = 1 := by
  rw [lagUnitary_eq' (graphBasis4_det_ne_zero hg)]
  exact unitary_of_gram (graphBasis4_star_det_ne_zero hg) (gram_eq hg)

lemma one_sp : (1 : Matrix (Fin 4) (Fin 4) ℝ)ᵀ * omK * 1 = omK := by simp

lemma omK_mul_self_assoc (X : Matrix (Fin 4) (Fin 4) ℝ) : omK * (omK * X) = -X := by
  rw [← Matrix.mul_assoc, omK_mul_self, Matrix.neg_mul, Matrix.one_mul]

lemma half_gram {E F G G' : Matrix (Fin 4) (Fin 4) ℂ} (hFE : Fᴴ * E = 0) :
    (F * G')ᴴ * (E + F * G) = G'ᴴ * (Fᴴ * F) * G := by
  rw [conjTranspose_mul, Matrix.mul_add, Matrix.mul_assoc G'ᴴ Fᴴ E, hFE, Matrix.mul_zero,
    zero_add]
  simp only [Matrix.mul_assoc]

lemma N_eq (g S : Matrix (Fin 4) (Fin 4) ℝ) (hS : Sᵀ = S) :
    (-I) • ((gbFb * cmH (symplJ4 * S * g))ᴴ * (gbEb + gbFb * cmH g) -
      (gbF * cmH (symplJ4 * S * g))ᴴ * (gbE + gbF * cmH g)) =
      cmH (gᵀ * S * g + gᵀ * S * g) := by
  have hreal : (symplJ4 * S * g)ᵀ * omK * g = -(gᵀ * S * g) := by
    rw [Matrix.transpose_mul, Matrix.transpose_mul, hS, symplJ4_eq, Matrix.transpose_neg,
      omK_transpose, neg_neg]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc omK omK g, omK_mul_self]
    simp
  have hc : cmH (symplJ4 * S * g)ᵀ * (cmH omK * cmH g) = -cmH (gᵀ * S * g) := by
    rw [← map_mul, ← map_mul, ← Matrix.mul_assoc, hreal, map_neg]
  rw [half_gram gbFb_Eb, half_gram gbF_E, gbFb_gram, gbF_gram, cmH_conjTranspose, map_add]
  set P := cmH (symplJ4 * S * g)ᵀ
  set Z := cmH (gᵀ * S * g)
  set Kc := cmH omK
  set Gc := cmH g
  simp only [Matrix.mul_sub, Matrix.mul_add, Matrix.sub_mul, Matrix.add_mul, Matrix.mul_one,
    Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc, hc]
  simp only [smul_sub, smul_add, smul_neg, smul_smul, neg_mul, mul_neg, I_mul_I, neg_neg,
    one_smul]
  abel

theorem graphUnitary4_positive_path' (Ŷ S : ℝ → Matrix (Fin 4) (Fin 4) ℝ)
    (hSpos : ∀ t, (S t).PosDef) (h0 : Ŷ 0 = 1)
    (hd : ∀ t : ℝ, ∀ i j : Fin 4, HasDerivAt (fun s => Ŷ s i j) ((symplJ4 * S t * Ŷ t) i j) t) :
    graphUnitary4 (Ŷ 0) = 1 ∧ (∀ t, star (graphUnitary4 (Ŷ t)) * graphUnitary4 (Ŷ t) = 1) ∧
      ∃ Q : ℝ → Matrix (Fin 4) (Fin 4) ℂ, ∀ t, (Q t).PosDef ∧
        ∀ i j : Fin 4, HasDerivAt (fun s => graphUnitary4 (Ŷ s) i j)
          ((Complex.I • (Q t * graphUnitary4 (Ŷ t))) i j) t := by
  have hSs : ∀ t, (S t)ᵀ = S t := fun t => by
    have := (hSpos t).1; rwa [IsHermitian, conjTranspose_eq_transpose_of_trivial] at this
  have hY : ∀ t, HasMatDerivAt Ŷ (symplJ4 * S t * Ŷ t) t := hd
  -- symplecticity of `Ŷ`
  have hsp : ∀ s, (Ŷ s)ᵀ * omK * Ŷ s = omK := by
    have hder : ∀ t, HasMatDerivAt (fun s => (Ŷ s)ᵀ * omK * Ŷ s) 0 t := by
      intro t
      have h := (((hY t).transpose).mul (HasMatDerivAt.const omK t)).mul (hY t)
      convert h using 1
      rw [Matrix.transpose_mul, Matrix.transpose_mul, hSs, symplJ4_eq, Matrix.transpose_neg,
        omK_transpose, neg_neg]
      simp only [Matrix.mul_zero, add_zero, Matrix.mul_assoc, Matrix.neg_mul, Matrix.mul_neg,
        omK_mul_self_assoc]
      abel
    intro s
    ext i j
    have hc := is_const_of_deriv_eq_zero (f := fun s => ((Ŷ s)ᵀ * omK * Ŷ s) i j)
      (fun t => (hder t i j).differentiableAt) (fun t => (hder t i j).deriv) s 0
    rw [hc, h0]; simp
  -- the two complex bases
  set A : ℝ → Matrix (Fin 4) (Fin 4) ℂ := fun s => graphBasis4 (Ŷ s) with hAdef
  set B : ℝ → Matrix (Fin 4) (Fin 4) ℂ := fun s => (A s).map (starRingEnd ℂ) with hBdef
  have hAdet : ∀ s, (A s).det ≠ 0 := fun s => graphBasis4_det_ne_zero (hsp s)
  have hBdet : ∀ s, (B s).det ≠ 0 := fun s => graphBasis4_star_det_ne_zero (hsp s)
  have hAhdet : ∀ s, (A s)ᴴ.det ≠ 0 := fun s => by
    rw [det_conjTranspose]; exact star_ne_zero.mpr (hAdet s)
  have hG : ∀ s, (A s)ᴴ * A s = (B s)ᴴ * B s := fun s => gram_eq (hsp s)
  set W₁ := lagUnitary (graphBasis4 1) with hW₁
  have hU₁ : W₁ᴴ * W₁ = 1 := lagUnitary_graphBasis4_unitary one_sp
  have hW₁inv : W₁⁻¹ = W₁ᴴ := Matrix.inv_eq_left_inv hU₁
  have hV : ∀ s, graphUnitary4 (Ŷ s) = ((A s)ᴴ)⁻¹ * (B s)ᴴ * W₁⁻¹ := fun s => by
    unfold graphUnitary4; rw [lagUnitary_eq' (hAdet s)]
  refine ⟨?_, ?_, ?_⟩
  · rw [h0]; unfold graphUnitary4; rw [← hW₁, hW₁inv]
    exact mul_eq_one_comm.mp hU₁
  · intro t
    have hU := lagUnitary_graphBasis4_unitary (hsp t)
    unfold graphUnitary4
    rw [← hW₁, hW₁inv, star_eq_conjTranspose, conjTranspose_mul, conjTranspose_conjTranspose,
      Matrix.mul_assoc, ← Matrix.mul_assoc _ (lagUnitary _), hU, Matrix.one_mul]
    exact mul_eq_one_comm.mp hU₁
  -- derivative
  set Yd : ℝ → Matrix (Fin 4) (Fin 4) ℝ := fun t => symplJ4 * S t * Ŷ t with hYd
  have hA' : ∀ t, HasMatDerivAt A (gbF * cmH (Yd t)) t := fun t => by
    have h := (HasMatDerivAt.const gbE t).add ((HasMatDerivAt.const gbF t).mul (hY t).cmH)
    have e : A = fun s => gbE + gbF * cmH (Ŷ s) := by funext s; exact graphBasis4_eq_add _
    rw [e]; convert h using 1; simp only [Matrix.zero_mul, zero_add]; rfl
  have hB' : ∀ t, HasMatDerivAt B (gbFb * cmH (Yd t)) t := fun t => by
    have h := (HasMatDerivAt.const gbEb t).add ((HasMatDerivAt.const gbFb t).mul (hY t).cmH)
    have e : B = fun s => gbEb + gbFb * cmH (Ŷ s) := by funext s; exact graphBasis4_map_star _
    rw [e]; convert h using 1; simp only [Matrix.zero_mul, zero_add]; rfl
  let Q : ℝ → Matrix (Fin 4) (Fin 4) ℂ := fun t =>
    ((A t)ᴴ)⁻¹ * cmH ((Ŷ t)ᵀ * S t * Ŷ t + (Ŷ t)ᵀ * S t * Ŷ t) * (A t)⁻¹
  refine ⟨Q, fun t => ⟨?_, ?_⟩⟩
  · -- positivity
    have hYu : IsUnit (Ŷ t) := by
      refine (Matrix.isUnit_iff_isUnit_det _).mpr (Matrix.isUnit_det_of_left_inverse
        (B := -(omK * (Ŷ t)ᵀ * omK)) ?_)
      rw [Matrix.neg_mul, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc _ omK, hsp t,
        omK_mul_self, neg_neg]
    have hP : ((Ŷ t)ᵀ * S t * Ŷ t).PosDef := by
      have := (hSpos t).conjTranspose_mul_mul_same (Matrix.mulVec_injective_of_isUnit hYu)
      rwa [conjTranspose_eq_transpose_of_trivial] at this
    have hAu : IsUnit (A t)⁻¹ :=
      Matrix.isUnit_nonsing_inv_iff.mpr ((Matrix.isUnit_iff_isUnit_det _).mpr
        (isUnit_iff_ne_zero.mpr (hAdet t)))
    have := (posDef_cmH (hP.add hP)).conjTranspose_mul_mul_same
      (Matrix.mulVec_injective_of_isUnit hAu)
    simpa only [Q, conjTranspose_nonsing_inv] using this
  · intro i j
    have hWd := ((hA' t).conjTranspose.inv hAhdet).mul (hB' t).conjTranspose
    have hVd := hWd.mul (HasMatDerivAt.const W₁⁻¹ t)
    have e : (fun s => graphUnitary4 (Ŷ s)) = fun s => ((A s)ᴴ)⁻¹ * (B s)ᴴ * W₁⁻¹ := funext hV
    rw [← e] at hVd
    have hN : (-I) • ((gbFb * cmH (Yd t))ᴴ * B t - (gbF * cmH (Yd t))ᴴ * A t) =
        cmH ((Ŷ t)ᵀ * S t * Ŷ t + (Ŷ t)ᵀ * S t * Ŷ t) := by
      rw [show B t = gbEb + gbFb * cmH (Ŷ t) from graphBasis4_map_star _,
        show A t = gbE + gbF * cmH (Ŷ t) from graphBasis4_eq_add _]
      exact N_eq _ _ (hSs t)
    have key : (-(((A t)ᴴ)⁻¹ * (gbF * cmH (Yd t))ᴴ * ((A t)ᴴ)⁻¹) * (B t)ᴴ +
        ((A t)ᴴ)⁻¹ * (gbFb * cmH (Yd t))ᴴ) * W₁⁻¹ + ((A t)ᴴ)⁻¹ * (B t)ᴴ * 0 =
        I • (Q t * graphUnitary4 (Ŷ t)) := by
      rw [Matrix.mul_zero, add_zero, deriv_identity (hAdet t) (hBdet t) (hG t), hN, hV t]
      simp only [Q, Matrix.smul_mul, Matrix.mul_assoc]
    rw [key] at hVd
    exact hVd i j

end

end HryniewiczCriterion

open HryniewiczCriterion

theorem solution (Ŷ S : ℝ → Matrix (Fin 4) (Fin 4) ℝ)
    (hSpos : ∀ t, (S t).PosDef) (h0 : Ŷ 0 = 1)
    (hd : ∀ t : ℝ, ∀ i j : Fin 4, HasDerivAt (fun s => Ŷ s i j) ((symplJ4 * S t * Ŷ t) i j) t) :
    graphUnitary4 (Ŷ 0) = 1 ∧ (∀ t, star (graphUnitary4 (Ŷ t)) * graphUnitary4 (Ŷ t) = 1) ∧
      ∃ Q : ℝ → Matrix (Fin 4) (Fin 4) ℂ, ∀ t, (Q t).PosDef ∧
        ∀ i j : Fin 4, HasDerivAt (fun s => graphUnitary4 (Ŷ s) i j)
          ((Complex.I • (Q t * graphUnitary4 (Ŷ t))) i j) t :=
  graphUnitary4_positive_path' Ŷ S hSpos h0 hd
