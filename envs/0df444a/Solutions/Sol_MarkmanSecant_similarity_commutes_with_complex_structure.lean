-- Prove2me | solution 1 for MarkmanSecant.similarity_commutes_with_complex_structure
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T20:12:00.345751+00:00
-- url     : https://prove2.me/submissions/11519d8d-6234-4150-905e-cf073f5f6def

import Mathlib
import Definitions.Def_MarkmanSecant

open MarkmanSecant
open scoped ExteriorAlgebra
open Matrix

namespace MKAux
variable {n : ℕ}

lemma dual_apply (t w : H1 n) : dualLin t w = ∑ i, t i * w i := by
  simp [dualLin, LinearMap.sum_apply, LinearMap.smulRight_apply]

lemma contract_map (f : H1 n →ₗ[ℂ] H1 n) (d : Module.Dual ℂ (H1 n)) (x : Spinor n) :
    CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm ℂ (H1 n))) d (ExteriorAlgebra.map f x) =
    ExteriorAlgebra.map f (CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm ℂ (H1 n))) (d ∘ₗ f) x) := by
  induction x using CliffordAlgebra.left_induction with
  | algebraMap r =>
    simp only [AlgHom.commutes, CliffordAlgebra.contractLeft_algebraMap, map_zero]
  | add x y hx hy => simp only [map_add, hx, hy]
  | ι_mul x m hx =>
    rw [map_mul]
    have h1 : ExteriorAlgebra.map f (CliffordAlgebra.ι (0 : QuadraticForm ℂ (H1 n)) m) =
        CliffordAlgebra.ι (0 : QuadraticForm ℂ (H1 n)) (f m) := ExteriorAlgebra.map_apply_ι f m
    rw [h1, CliffordAlgebra.contractLeft_ι_mul, CliffordAlgebra.contractLeft_ι_mul, hx, map_sub,
      map_smul, map_mul, h1]
    rfl

lemma cliffAt_apply (s : Spinor n) (v : VC n) :
    cliffAt s v = ExteriorAlgebra.ι ℂ (wPart v) * s +
      CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm ℂ (H1 n))) (dualLin (tPart v)) s := by
  rfl

/-- The complex structure `J` acting on `H¹`. -/
noncomputable def Jl (J : Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ) : H1 n →ₗ[ℂ] H1 n :=
  Matrix.mulVecLin (cMat J)

lemma scal_I (J : Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ) : scal J Complex.I = Jl J := by
  simp [scal, Jl]

lemma cMat_sq (J : Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ) (hJ : J * J = -1) :
    cMat J * cMat J = -1 := by
  ext i j
  have h := congrArg (fun M : Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ => ((M i j : ℝ) : ℂ)) hJ
  simp only [Matrix.mul_apply, Complex.ofReal_sum, Complex.ofReal_mul] at h
  simp only [cMat, Matrix.mul_apply, Matrix.map_apply, h]
  by_cases hij : i = j <;> simp [hij, Matrix.one_apply]

lemma hodge_fixed (J : Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ) (s : Spinor n) (hs : IsInHodgeRing J s) :
    ExteriorAlgebra.map (Jl J) s = s := by
  obtain ⟨c, hc, rfl⟩ := hs
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro p _
  have h := (hc p).2 Complex.I
  rw [scal_I] at h
  rw [h]
  have : Complex.I ^ p * (starRingEnd ℂ) Complex.I ^ p = 1 := by
    rw [← mul_pow, Complex.conj_I]; simp
  rw [this, one_smul]

lemma wPart_IV (J : Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ) (v : VC n) :
    wPart (IV J *ᵥ v) = cMat J *ᵥ wPart v := by
  ext i
  simp [wPart, IV, Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Matrix.fromBlocks]

lemma tPart_IV (J : Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ) (v : VC n) :
    tPart (IV J *ᵥ v) = -((cMat J).transpose *ᵥ tPart v) := by
  ext i
  simp [tPart, IV, Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Matrix.fromBlocks]

lemma annih_inv (J : Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ) (hJ : J * J = -1) (s : Spinor n)
    (hs : ExteriorAlgebra.map (Jl J) s = s) (v : VC n) (hv : v ∈ annih s) :
    IV J *ᵥ v ∈ annih s := by
  have hv' : cliffAt s v = 0 := hv
  show cliffAt s (IV J *ᵥ v) = 0
  have h0 := congrArg (ExteriorAlgebra.map (Jl J)) hv'
  rw [map_zero, cliffAt_apply, map_add, map_mul, ExteriorAlgebra.map_apply_ι, hs] at h0
  -- the contraction term
  set G : H1 n →ₗ[ℂ] H1 n := -(Jl J) with hG
  have hGJ : G ∘ₗ Jl J = LinearMap.id := by
    apply LinearMap.ext; intro y
    simp only [hG, LinearMap.comp_apply, LinearMap.neg_apply, LinearMap.id_apply, Jl,
      Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, cMat_sq J hJ]
    rw [Matrix.neg_mulVec, Matrix.one_mulVec, neg_neg]
  have hc := contract_map (Jl J) (dualLin (tPart v) ∘ₗ G) s
  rw [hs, LinearMap.comp_assoc, hGJ, LinearMap.comp_id] at hc
  rw [← hc] at h0
  rw [cliffAt_apply, wPart_IV, tPart_IV]
  have hd : dualLin (-((cMat J).transpose *ᵥ tPart v)) = dualLin (tPart v) ∘ₗ G := by
    apply LinearMap.ext; intro y
    rw [dual_apply, LinearMap.comp_apply, dual_apply]
    simp only [hG, LinearMap.neg_apply, Jl, Matrix.mulVecLin_apply]
    simp only [Pi.neg_apply, Matrix.mulVec, dotProduct, Matrix.transpose_apply, neg_mul,
      Finset.sum_neg_distrib, mul_neg, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    congr 1
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro j _
    ring
  rw [hd]
  exact h0

end MKAux

open MKAux in
theorem solution (n : ℕ)
    (J : Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ) (hJ : J * J = -1)
    (d : ℚ) (hd : 0 < d) (a b : Spinor n)
    (ha : IsInHodgeRing J a) (hb : IsInHodgeRing J b)
    (h₁ : IsEvenPureSpinor (a + sqrtNeg d • b)) (h₂ : IsEvenPureSpinor (a - sqrtNeg d • b))
    (h₁₂ : annih (a + sqrtNeg d • b) ⊓ annih (a - sqrtNeg d • b) = ⊥)
    (F : Matrix (VIdx n) (VIdx n) ℚ)
    (hF₁ : ∀ v ∈ annih (a + sqrtNeg d • b), (ratMatV F).mulVec v = sqrtNeg d • v)
    (hF₂ : ∀ v ∈ annih (a - sqrtNeg d • b), (ratMatV F).mulVec v = (-sqrtNeg d) • v) :
    ratMatV F * IV J = IV J * ratMatV F := by
  have hfa := hodge_fixed J a ha
  have hfb := hodge_fixed J b hb
  have hp : ExteriorAlgebra.map (Jl J) (a + sqrtNeg d • b) = a + sqrtNeg d • b := by
    rw [map_add, map_smul, hfa, hfb]
  have hm : ExteriorAlgebra.map (Jl J) (a - sqrtNeg d • b) = a - sqrtNeg d • b := by
    rw [map_sub, map_smul, hfa, hfb]
  -- the two annihilators span
  have hdim : Module.finrank ℂ (VC n) = 2 * n + 2 * n := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]
  have hsup : annih (a + sqrtNeg d • b) ⊔ annih (a - sqrtNeg d • b) = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    have := Submodule.finrank_sup_add_finrank_inf_eq (annih (a + sqrtNeg d • b))
      (annih (a - sqrtNeg d • b))
    rw [h₁₂, finrank_bot, h₁.2.2, h₂.2.2] at this
    rw [hdim]; omega
  apply Matrix.toLin'.injective
  apply LinearMap.ext
  intro v
  simp only [Matrix.toLin'_apply]
  have hv : v ∈ annih (a + sqrtNeg d • b) ⊔ annih (a - sqrtNeg d • b) := by rw [hsup]; trivial
  obtain ⟨u, hu, u', hu', rfl⟩ := Submodule.mem_sup.1 hv
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.mulVec_add, Matrix.mulVec_add,
    Matrix.mulVec_add, Matrix.mulVec_add]
  rw [hF₁ _ (annih_inv J hJ _ hp u hu), hF₂ _ (annih_inv J hJ _ hm u' hu'), hF₁ u hu, hF₂ u' hu',
    Matrix.mulVec_smul, Matrix.mulVec_smul]
