-- Prove2me | solution 1 for MarkmanSecant.exists_rational_similarity_of_secant
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T04:33:09.239749+00:00
-- url     : https://prove2.me/submissions/1ead4797-0eba-4915-8bee-709909e2779f

import Theorems.Thm_MarkmanSecant_similarity_of_opposite_annihilator_action
import Theorems.Thm_MarkmanSecant_exists_rational_annihilator_action

open MarkmanSecant Matrix

private lemma sqrtNeg_sq (d : ℚ) (hd : 0 < d) : (sqrtNeg d) ^ 2 = -(d : ℂ) := by
  unfold sqrtNeg
  rw [mul_pow, Complex.I_sq, ← Complex.ofReal_pow,
    Real.sq_sqrt (show 0 ≤ (d : ℝ) by exact_mod_cast hd.le)]
  push_cast
  ring

private lemma ratMat_mulVec {n : ℕ} (F : Matrix (VIdx n) (VIdx n) ℚ)
    (x : VIdx n → ℚ) : ratV (F.mulVec x) = (ratMatV F).mulVec (ratV x) := by
  ext i
  exact RingHom.map_mulVec (algebraMap ℚ ℂ) F x i

private theorem rational_consequences (n : ℕ) (d : ℚ) (hd : 0 < d) (a b : Spinor n)
    (h₁ : IsEvenPureSpinor (a + sqrtNeg d • b))
    (h₂ : IsEvenPureSpinor (a - sqrtNeg d • b))
    (h₁₂ : annih (a + sqrtNeg d • b) ⊓ annih (a - sqrtNeg d • b) = ⊥)
    (F : Matrix (VIdx n) (VIdx n) ℚ)
    (hF₁ : ∀ v ∈ annih (a + sqrtNeg d • b), (ratMatV F).mulVec v = sqrtNeg d • v)
    (hF₂ : ∀ v ∈ annih (a - sqrtNeg d • b), (ratMatV F).mulVec v = (-sqrtNeg d) • v) :
    F * F = -(d • (1 : Matrix (VIdx n) (VIdx n) ℚ)) ∧
      ∀ x y : VIdx n → ℚ,
        pairV (ratV (F.mulVec x)) (ratV (F.mulVec y)) =
          (d : ℂ) * pairV (ratV x) (ratV y) := by
  have h := MarkmanSecant.similarity_of_opposite_annihilator_action n
    (a + sqrtNeg d • b) (a - sqrtNeg d • b) h₁ h₂ h₁₂ (sqrtNeg d)
    (ratMatV F).mulVecLin hF₁ hF₂
  rw [sqrtNeg_sq d hd] at h
  constructor
  · have hm : ratMatV F * ratMatV F = -(d : ℂ) •
        (1 : Matrix (VIdx n) (VIdx n) ℂ) := by
      apply Matrix.toLin'.injective
      rw [Matrix.toLin'_mul, map_smul, Matrix.toLin'_one]
      exact h.1
    ext i j
    apply (Rat.cast_injective (α := ℂ))
    have hh := congrArg (fun M => M i j) hm
    by_cases hij : i = j <;>
      simpa [ratMatV, Matrix.mul_apply, Matrix.one_apply, Matrix.smul_apply,
        Matrix.neg_apply, smul_eq_mul, hij] using hh
  · intro x y
    rw [ratMat_mulVec, ratMat_mulVec]
    simpa only [neg_neg, Matrix.mulVecLin_apply] using h.2 (ratV x) (ratV y)




theorem solution (n : ℕ) (d : ℚ) (hd : 0 < d) (a b : Spinor n)
    (ha : IsRationalClass a) (hb : IsRationalClass b)
    (h₁ : IsEvenPureSpinor (a + sqrtNeg d • b)) (h₂ : IsEvenPureSpinor (a - sqrtNeg d • b))
    (h₁₂ : annih (a + sqrtNeg d • b) ⊓ annih (a - sqrtNeg d • b) = ⊥) :
    ∃ F : Matrix (VIdx n) (VIdx n) ℚ,
      (∀ v ∈ annih (a + sqrtNeg d • b), (ratMatV F).mulVec v = sqrtNeg d • v) ∧
      (∀ v ∈ annih (a - sqrtNeg d • b), (ratMatV F).mulVec v = (-sqrtNeg d) • v) ∧
      F * F = -(d • (1 : Matrix (VIdx n) (VIdx n) ℚ)) ∧
      ∀ x y : VIdx n → ℚ,
        pairV (ratV (F.mulVec x)) (ratV (F.mulVec y)) = (d : ℂ) * pairV (ratV x) (ratV y) := by
  obtain ⟨F, hF₁, hF₂⟩ := MarkmanSecant.exists_rational_annihilator_action
    n d hd a b ha hb h₁ h₂ h₁₂
  obtain ⟨hsq, hpair⟩ := rational_consequences n d hd a b h₁ h₂ h₁₂ F hF₁ hF₂
  exact ⟨F, hF₁, hF₂, hsq, hpair⟩


#print axioms solution
