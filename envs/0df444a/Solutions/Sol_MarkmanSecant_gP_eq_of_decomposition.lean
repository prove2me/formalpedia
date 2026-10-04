-- Prove2me | solution 1 for MarkmanSecant.gP_eq_of_decomposition
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-04T05:51:52.99019+00:00
-- url     : https://prove2.me/submissions/146b3439-e8e7-47a9-b071-3665ed04b369

import Mathlib
import Definitions.Def_MarkmanSecant

open MarkmanSecant
open scoped ExteriorAlgebra

namespace P5862075c

open MarkmanSecant Matrix

theorem wPart_IV {n : ℕ} (J : Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ) (x : VC n) :
    wPart ((IV J) *ᵥ x) = cMat J *ᵥ wPart x := by
  ext i
  simp [wPart, IV, Matrix.fromBlocks_mulVec]
  rfl

theorem tPart_IV {n : ℕ} (J : Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ) (x : VC n) :
    tPart ((IV J) *ᵥ x) = (-(cMat J).transpose) *ᵥ tPart x := by
  ext i
  simp [tPart, IV, Matrix.fromBlocks_mulVec]
  rfl

theorem wPart_add {n : ℕ} (x y : VC n) : wPart (x + y) = wPart x + wPart y := rfl
theorem tPart_add {n : ℕ} (x y : VC n) : tPart (x + y) = tPart x + tPart y := rfl
theorem wPart_smul {n : ℕ} (c : ℂ) (x : VC n) : wPart (c • x) = c • wPart x := rfl
theorem tPart_smul {n : ℕ} (c : ℂ) (x : VC n) : tPart (c • x) = c • tPart x := rfl

theorem pairV_add_left {n : ℕ} (x y z : VC n) : pairV (x + y) z = pairV x z + pairV y z := by
  simp only [pairV, wPart_add, tPart_add, add_dotProduct, dotProduct_add]; ring

theorem pairV_add_right {n : ℕ} (x y z : VC n) : pairV z (x + y) = pairV z x + pairV z y := by
  simp only [pairV, wPart_add, tPart_add, add_dotProduct, dotProduct_add]; ring

theorem pairV_smul_left {n : ℕ} (c : ℂ) (x z : VC n) : pairV (c • x) z = c * pairV x z := by
  simp only [pairV, wPart_smul, tPart_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul]; ring

theorem pairV_comm {n : ℕ} (x y : VC n) : pairV x y = pairV y x := by
  simp only [pairV]; ring

theorem eig_of_mem {n : ℕ} (J : Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ) (μ : ℂ) (x : VC n)
    (hx : x ∈ LinearMap.ker ((IV J).mulVecLin - μ • LinearMap.id)) : (IV J) *ᵥ x = μ • x := by
  rw [LinearMap.mem_ker] at hx
  simpa [sub_eq_zero] using hx

theorem eig_of_mem' {n : ℕ} (J : Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ) (μ : ℂ) (x : VC n)
    (hx : x ∈ LinearMap.ker ((IV J).mulVecLin + μ • LinearMap.id)) : (IV J) *ᵥ x = (-μ) • x := by
  rw [LinearMap.mem_ker] at hx
  simp only [LinearMap.add_apply, Matrix.mulVecLin_apply, LinearMap.smul_apply,
    LinearMap.id_apply] at hx
  rw [neg_smul, eq_neg_iff_add_eq_zero]
  exact hx

theorem isotropic {n : ℕ} (J : Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ) (μ : ℂ) (hμ : μ ≠ 0)
    (x y : VC n) (hx : (IV J) *ᵥ x = μ • x) (hy : (IV J) *ᵥ y = μ • y) : pairV x y = 0 := by
  have hwx : cMat J *ᵥ wPart x = μ • wPart x := by rw [← wPart_IV, hx]; rfl
  have hwy : cMat J *ᵥ wPart y = μ • wPart y := by rw [← wPart_IV, hy]; rfl
  have htx : (-(cMat J).transpose) *ᵥ tPart x = μ • tPart x := by rw [← tPart_IV, hx]; rfl
  have hty : (-(cMat J).transpose) *ᵥ tPart y = μ • tPart y := by rw [← tPart_IV, hy]; rfl
  have key : ∀ t w : H1 n, cMat J *ᵥ w = μ • w → (-(cMat J).transpose) *ᵥ t = μ • t →
      t ⬝ᵥ w = 0 := by
    intro t w hw ht
    have h1 : t ⬝ᵥ (cMat J *ᵥ w) = μ * (t ⬝ᵥ w) := by rw [hw, dotProduct_smul, smul_eq_mul]
    have h2 : t ⬝ᵥ (cMat J *ᵥ w) = ((cMat J).transpose *ᵥ t) ⬝ᵥ w := by
      rw [dotProduct_mulVec, Matrix.mulVec_transpose]
    have h3 : (cMat J).transpose *ᵥ t = (-μ) • t := by
      rw [Matrix.neg_mulVec] at ht
      rw [neg_smul, ← ht, neg_neg]
    rw [h3, smul_dotProduct, smul_eq_mul, h1] at h2
    have : (2 * μ) * (t ⬝ᵥ w) = 0 := by linear_combination h2
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h (mul_ne_zero two_ne_zero hμ)
    · exact h
  simp only [pairV, key _ _ hwy htx, key _ _ hwx hty, add_zero]

end P5862075c

open MarkmanSecant in
theorem solution (n : ℕ)
    (J : Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ) (hJ : J * J = -1)
    (d : ℚ) (hd : 0 < d) (a b : Spinor n)
    (ha : IsInHodgeRing J a) (hb : IsInHodgeRing J b)
    (h₁ : IsEvenPureSpinor (a + sqrtNeg d • b)) (h₂ : IsEvenPureSpinor (a - sqrtNeg d • b))
    (h₁₂ : annih (a + sqrtNeg d • b) ⊓ annih (a - sqrtNeg d • b) = ⊥)
    (F : Matrix (VIdx n) (VIdx n) ℚ)
    (hF₁ : ∀ v ∈ annih (a + sqrtNeg d • b), (ratMatV F).mulVec v = sqrtNeg d • v)
    (hF₂ : ∀ v ∈ annih (a - sqrtNeg d • b), (ratMatV F).mulVec v = (-sqrtNeg d) • v)
    (v : VIdx n → ℚ) (v₁₁₀ v₂₁₀ v₁₀₁ v₂₀₁ : VC n)
    (h₁₁₀ : v₁₁₀ ∈ annih (a + sqrtNeg d • b) ⊓ V10 J)
    (h₂₁₀ : v₂₁₀ ∈ annih (a - sqrtNeg d • b) ⊓ V10 J)
    (h₁₀₁ : v₁₀₁ ∈ annih (a + sqrtNeg d • b) ⊓ V01 J)
    (h₂₀₁ : v₂₀₁ ∈ annih (a - sqrtNeg d • b) ⊓ V01 J)
    (hv : ratV v = v₁₁₀ + v₂₁₀ + v₁₀₁ + v₂₀₁) :
    pairV ((ratMatV F).mulVec ((IV J).mulVec (ratV v))) (ratV v) =
      2 * ((Real.sqrt (d : ℝ) : ℝ) : ℂ) * (-pairV v₁₁₀ v₂₀₁ + pairV v₁₀₁ v₂₁₀) := by
  rw [Submodule.mem_inf] at h₁₁₀ h₂₁₀ h₁₀₁ h₂₀₁
  have eA := P5862075c.eig_of_mem J Complex.I _ h₁₁₀.2
  have eB := P5862075c.eig_of_mem J Complex.I _ h₂₁₀.2
  have eC := P5862075c.eig_of_mem' J Complex.I _ h₁₀₁.2
  have eD := P5862075c.eig_of_mem' J Complex.I _ h₂₀₁.2
  have fA := hF₁ _ h₁₁₀.1
  have fB := hF₂ _ h₂₁₀.1
  have fC := hF₁ _ h₁₀₁.1
  have fD := hF₂ _ h₂₀₁.1
  set s : ℂ := ((Real.sqrt (d : ℝ) : ℝ) : ℂ) with hs
  have hsq : sqrtNeg d = Complex.I * s := rfl
  have hI : Complex.I ≠ 0 := Complex.I_ne_zero
  have hnI : -Complex.I ≠ 0 := neg_ne_zero.mpr Complex.I_ne_zero
  have pAB := P5862075c.isotropic J _ hI _ _ eA eB
  have pCD := P5862075c.isotropic J _ hnI _ _ eC eD
  have pAA := P5862075c.isotropic J _ hI _ _ eA eA
  have pBB := P5862075c.isotropic J _ hI _ _ eB eB
  have pCC := P5862075c.isotropic J _ hnI _ _ eC eC
  have pDD := P5862075c.isotropic J _ hnI _ _ eD eD
  have hFIv : (ratMatV F).mulVec ((IV J).mulVec (ratV v)) =
      (Complex.I * sqrtNeg d) • v₁₁₀ + (Complex.I * (-sqrtNeg d)) • v₂₁₀ +
        (-Complex.I * sqrtNeg d) • v₁₀₁ + (-Complex.I * (-sqrtNeg d)) • v₂₀₁ := by
    rw [hv]
    simp only [Matrix.mulVec_add, Matrix.mulVec_smul, eA, eB, eC, eD, fA, fB, fC, fD, smul_smul]
  rw [hFIv, hv]
  simp only [P5862075c.pairV_add_left, P5862075c.pairV_add_right, P5862075c.pairV_smul_left, pAB, pCD, pAA, pBB, pCC, pDD,
    P5862075c.pairV_comm v₂₁₀ v₁₁₀, P5862075c.pairV_comm v₂₀₁ v₁₀₁, P5862075c.pairV_comm v₁₀₁ v₁₁₀, P5862075c.pairV_comm v₂₀₁ v₁₁₀,
    P5862075c.pairV_comm v₂₀₁ v₂₁₀, P5862075c.pairV_comm v₁₀₁ v₂₁₀, hsq]
  have hII : Complex.I * Complex.I = -1 := Complex.I_mul_I
  linear_combination (2 * s * pairV v₁₁₀ v₂₀₁ - 2 * s * pairV v₂₁₀ v₁₀₁) * hII
