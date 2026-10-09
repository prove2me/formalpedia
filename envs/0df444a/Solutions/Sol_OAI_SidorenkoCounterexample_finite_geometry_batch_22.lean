-- Prove2me | solution 1 for OAI.SidorenkoCounterexample.finite_geometry_batch_22
-- status  : ACCEPTED   (prove)
-- author  : @abcdefg
-- created : 2026-10-09T06:14:06.043581+00:00
-- url     : https://prove2.me/submissions/fa51a3ab-1e89-4415-b9d8-ef200db2952b

import Definitions.Def_SidorenkoCertificateBundleA
set_option linter.unusedVariables false
section
variable [p0 : OAI.SidorenkoCounterexample.ProofCertificate_0583]
  [p1 : OAI.SidorenkoCounterexample.ProofCertificate_0591]
  [p2 : OAI.SidorenkoCounterexample.ProofCertificate_0609]
  [p3 : OAI.SidorenkoCounterexample.ProofCertificate_0613]
include p0 p1 p2 p3

namespace OAI
namespace SidorenkoCounterexample
open Module
open scoped BigOperators
section PairBound
variable {K E : Type} [Field K] [AddCommGroup E] [Module K E] [Fintype K] [Finite E]
variable (ω : LinearMap.BilinForm K E)
end PairBound
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
open scoped BigOperators
section Actual
variable {K E : Type} [Field K] [AddCommGroup E] [Module K E] [Fintype K] [Finite E]
variable (ω : LinearMap.BilinForm K E)
end Actual
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
open scoped BigOperators
section Actual
variable {K E : Type} [Field K] [AddCommGroup E] [Module K E] [Fintype K] [Finite E]
variable (ω : LinearMap.BilinForm K E)
end Actual
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
open scoped BigOperators
section Actual
variable {K E : Type} [Field K] [AddCommGroup E] [Module K E] [Fintype K] [Finite E]
variable (ω : LinearMap.BilinForm K E)
end Actual
section ActualProduct
variable {K E : Type} [Field K] [AddCommGroup E] [Module K E] [Fintype K] [Finite E]
variable (ω : LinearMap.BilinForm K E)
end ActualProduct
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
open scoped BigOperators
section ActiveFace
variable {K E : Type} [Field K] [AddCommGroup E] [Module K E] [Fintype K] [Finite E]
variable (ω : LinearMap.BilinForm K E)
end ActiveFace
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
open scoped BigOperators
section ActiveFaceBound
variable {K E : Type} [Field K] [AddCommGroup E] [Module K E] [Fintype K] [Finite E]
variable (ω : LinearMap.BilinForm K E)
end ActiveFaceBound
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
open scoped BigOperators
section Integrated
variable {K E : Type} [Field K] [AddCommGroup E] [Module K E] [Fintype K] [Finite E]
variable (ω : LinearMap.BilinForm K E)
end Integrated
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
open scoped BigOperators
section IntegratedBound
variable {K E : Type} [Field K] [AddCommGroup E] [Module K E] [Fintype K] [Finite E]
variable (ω : LinearMap.BilinForm K E)
end IntegratedBound
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
open scoped BigOperators
section ActualProfile
variable {K E : Type} [Field K] [AddCommGroup E] [Module K E]
  [Finite E]
variable (ω : LinearMap.BilinForm K E) (hω : ω.Nondegenerate)
variable (D : ℕ) (hD : 2 * D = finrank K E)
theorem certificate_proof_0614 (r : ℕ) (A : SymplecticLagrangian ω)
    (T : Fin 22 → Finset (Fin 3)) : 0 ≤ actualSingularTail ω r A T := by
  classical
  unfold actualSingularTail
  apply div_nonneg _ (by positivity)
  apply Finset.sum_nonneg
  intro L _
  split_ifs
  · exact Finset.prod_nonneg (fun j _ => activeFaceDensity_nonneg ω r A _ (T j))
  · rfl

private instance certificate_instance_0614 : OAI.SidorenkoCounterexample.ProofCertificate_0614 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9
  exact @certificate_proof_0614 p0 p1 p2 p3 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9

include hω hD in
theorem certificate_proof_0615 [Fintype K] [Invertible (2 : K)]
    (h2 : (2 : K) ≠ 0) (ha : ω.IsAlt) (r : ℕ) (hr : D = 2*r)
    (hlarge : singularTailThreshold ≤ D)
    (hq : 4*lagrangianConstant D ≤ (Fintype.card K : ℝ))
    (A : SymplecticLagrangian ω) (T : Fin 22 → Finset (Fin 3)) :
    actualSingularTail ω r A T ≤
      integratedTailMajorant D r (fun j => decide (T j = Finset.univ)) (Fintype.card K) := by
  rw [actualSingularTail_eq_integrated ω hω D hD]
  exact integratedActiveTail_bound ω h2 ha hω D r hD hr hlarge hq A T

private instance certificate_instance_0615 : OAI.SidorenkoCounterexample.ProofCertificate_0615 := by
  constructor
  intro c0 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19
  exact @certificate_proof_0615 p0 p1 p2 p3 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19

end ActualProfile
end SidorenkoCounterexample
end OAI
namespace OAI
section
namespace SidorenkoCounterexample
open Module LinearMap
section Forms
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
theorem certificate_proof_0616 (B : LinearMap.BilinForm K V) (hB : B.IsSymm)
    (x y : V) : radicalQuotientForm B hB
      (Submodule.Quotient.mk x) (Submodule.Quotient.mk y) = B x y := rfl

private instance certificate_instance_0616 : OAI.SidorenkoCounterexample.ProofCertificate_0616 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8
  exact @certificate_proof_0616 p0 p1 p2 p3 q0 q1 q2 q3 q4 q5 q6 q7 q8

theorem certificate_proof_0617 [FiniteDimensional K V]
    (B : LinearMap.BilinForm K V) (hB : B.IsSymm) :
    (radicalQuotientForm B hB).Nondegenerate := by
  apply LinearMap.BilinForm.nondegenerate_iff_ker_eq_bot.mpr
  apply bot_unique
  intro x hx
  induction x using Submodule.Quotient.induction_on with
  | H x =>
    apply (Submodule.Quotient.mk_eq_zero B.ker).mpr
    apply LinearMap.mem_ker.mpr
    ext y
    have h := congrArg (fun f => f (Submodule.Quotient.mk y)) hx
    exact h

private instance certificate_instance_0617 : OAI.SidorenkoCounterexample.ProofCertificate_0617 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7
  exact @certificate_proof_0617 p0 p1 p2 p3 q0 q1 q2 q3 q4 q5 q6 q7

theorem certificate_proof_0618 (B : LinearMap.BilinForm K V) (hB : B.IsSymm) :
    (radicalQuotientForm B hB).IsSymm := by
  constructor
  intro x y
  induction x using Submodule.Quotient.induction_on with
  | H x =>
    induction y using Submodule.Quotient.induction_on with
    | H y => exact hB.eq x y

private instance certificate_instance_0618 : OAI.SidorenkoCounterexample.ProofCertificate_0618 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6
  exact @certificate_proof_0618 p0 p1 p2 p3 q0 q1 q2 q3 q4 q5 q6

theorem certificate_proof_0619 (B : LinearMap.BilinForm K V) (hB : B.IsSymm) :
    (-B).IsSymm := by
  constructor
  intro x y
  change -(B x y) = -(B y x)
  rw [hB.eq x y]

private instance certificate_instance_0619 : OAI.SidorenkoCounterexample.ProofCertificate_0619 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6
  exact @certificate_proof_0619 p0 p1 p2 p3 q0 q1 q2 q3 q4 q5 q6

theorem certificate_proof_0620 (B : LinearMap.BilinForm K V) (hB : B.IsSymm)
    (x y : V ⧸ (-B).ker) :
    radicalQuotientForm (-B) (form_isSymm_neg B hB) x y =
      -(radicalQuotientForm B hB (radicalNegEquiv B x) (radicalNegEquiv B y)) := by
  induction x using Submodule.Quotient.induction_on with
  | H x =>
    induction y using Submodule.Quotient.induction_on with
    | H y => rfl

private instance certificate_instance_0620 : OAI.SidorenkoCounterexample.ProofCertificate_0620 := by
  constructor
  intro c0 q0 q1 q2 q3 q4 q5 q6 q7 q8
  exact @certificate_proof_0620 p0 p1 p2 p3 q0 q1 q2 q3 q4 q5 q6 q7 q8

variable [FiniteDimensional K V] [Fintype K] [DecidableEq K]
theorem certificate_proof_0621 (B : LinearMap.BilinForm K V) (hB : B.IsSymm) :
    discriminantSign B hB ≠ 0 := by
  apply mt quadraticChar_eq_zero_iff.mp
  exact (LinearMap.BilinForm.nondegenerate_iff_det_ne_zero _).mp
    (radicalQuotientForm_nondegenerate B hB)

private instance certificate_instance_0621 : OAI.SidorenkoCounterexample.ProofCertificate_0621 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9
  exact @certificate_proof_0621 p0 p1 p2 p3 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9

theorem certificate_proof_0622 (B : LinearMap.BilinForm K V) (hB : B.IsSymm) :
    discriminantSign B hB ^ 2 = 1 := by
  apply quadraticChar_sq_one
  exact (LinearMap.BilinForm.nondegenerate_iff_det_ne_zero _).mp
    (radicalQuotientForm_nondegenerate B hB)

private instance certificate_instance_0622 : OAI.SidorenkoCounterexample.ProofCertificate_0622 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9
  exact @certificate_proof_0622 p0 p1 p2 p3 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9

theorem certificate_proof_0623 (B : LinearMap.BilinForm K V) (hB : B.IsSymm) :
    discriminantSign B hB = 1 ∨ discriminantSign B hB = -1 := by
  apply quadraticChar_dichotomy
  exact (LinearMap.BilinForm.nondegenerate_iff_det_ne_zero _).mp
    (radicalQuotientForm_nondegenerate B hB)

private instance certificate_instance_0623 : OAI.SidorenkoCounterexample.ProofCertificate_0623 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9
  exact @certificate_proof_0623 p0 p1 p2 p3 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9

omit [FiniteDimensional K V] in
theorem certificate_proof_0624 {ι : Type}
    [Fintype ι] [DecidableEq ι] (b c : Basis ι K V) (B : LinearMap.BilinForm K V) :
    quadraticChar K (B.toMatrix b).det = quadraticChar K (B.toMatrix c).det := by
  have hu : (b.toMatrix c).det ≠ 0 := (b.isUnit_det c).ne_zero
  rw [← B.toMatrix_mul_basis_toMatrix b c, Matrix.det_mul, Matrix.det_mul,
    Matrix.det_transpose, map_mul, map_mul]
  have hsq := quadraticChar_sq_one (F := K) hu
  linear_combination -(quadraticChar K (B.toMatrix b).det) * hsq

private instance certificate_instance_0624 : OAI.SidorenkoCounterexample.ProofCertificate_0624 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12
  exact @certificate_proof_0624 p0 p1 p2 p3 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12

omit [FiniteDimensional K V] in
theorem certificate_proof_0625 {ι κ : Type}
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (b : Basis ι K V) (c : Basis κ K V) (B : LinearMap.BilinForm K V) :
    quadraticChar K (B.toMatrix b).det = quadraticChar K (B.toMatrix c).det := by
  classical
  let e := b.indexEquiv c
  have h : B.toMatrix (b.reindex e) = Matrix.reindex e e (B.toMatrix b) := by
    ext i j
    simp [LinearMap.BilinForm.toMatrix_apply, Matrix.reindex_apply]
  calc
    quadraticChar K (B.toMatrix b).det =
        quadraticChar K (B.toMatrix (b.reindex e)).det := by
      rw [h, Matrix.det_reindex_self]
    _ = quadraticChar K (B.toMatrix c).det :=
      determinant_character_basis_independent _ _ _

private instance certificate_instance_0625 : OAI.SidorenkoCounterexample.ProofCertificate_0625 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15
  exact @certificate_proof_0625 p0 p1 p2 p3 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15

theorem certificate_proof_0626 (B : LinearMap.BilinForm K V) (hB : B.IsSymm)
    {ι : Type} [Fintype ι] [DecidableEq ι] (b : Basis ι K (V ⧸ B.ker)) :
    discriminantSign B hB = quadraticChar K ((radicalQuotientForm B hB).toMatrix b).det :=
  determinant_character_basis_independent_indices _ _ _

private instance certificate_instance_0626 : OAI.SidorenkoCounterexample.ProofCertificate_0626 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13
  exact @certificate_proof_0626 p0 p1 p2 p3 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13

theorem certificate_proof_0627 (B : LinearMap.BilinForm K V) (hB : B.IsSymm) :
    discriminantSign (-B) (form_isSymm_neg B hB) =
      quadraticChar K ((-1 : K) ^ finrank K (V ⧸ B.ker)) * discriminantSign B hB := by
  classical
  let b := Module.finBasis K (V ⧸ B.ker)
  rw [discriminantSign_eq (-B) (form_isSymm_neg B hB)
    (b.map (radicalNegEquiv B).symm)]
  have hm : (radicalQuotientForm (-B) (form_isSymm_neg B hB)).toMatrix
      (b.map (radicalNegEquiv B).symm) = -(radicalQuotientForm B hB).toMatrix b := by
    ext i j
    simp only [LinearMap.BilinForm.toMatrix_apply, Basis.map_apply, Matrix.neg_apply]
    rw [radicalQuotientForm_neg B hB]
    simp only [LinearEquiv.apply_symm_apply]
  rw [hm, Matrix.det_neg, map_mul, Fintype.card_fin]
  rfl

private instance certificate_instance_0627 : OAI.SidorenkoCounterexample.ProofCertificate_0627 := by
  constructor
  intro c0 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9
  exact @certificate_proof_0627 p0 p1 p2 p3 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9

end Forms
section Pullback
variable {K V W : Type} [Field K] [AddCommGroup V] [Module K V]
  [AddCommGroup W] [Module K W]
theorem certificate_proof_0628 (B : LinearMap.BilinForm K W) (hB : B.IsSymm)
    (f : V →ₗ[K] W) : LinearMap.BilinForm.IsSymm (B.compl₁₂ f f) := by
  constructor
  intro x y
  exact hB.eq (f x) (f y)

private instance certificate_instance_0628 : OAI.SidorenkoCounterexample.ProofCertificate_0628 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10
  exact @certificate_proof_0628 p0 p1 p2 p3 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10

theorem certificate_proof_0629 (B : LinearMap.BilinForm K W) (hB : B.Nondegenerate)
    (f : V →ₗ[K] W) (hf : Function.Surjective f) :
    (B.compl₁₂ f f).ker = f.ker := by
  ext x
  simp only [LinearMap.mem_ker]
  constructor
  · intro hx
    apply hB.1
    intro y
    obtain ⟨z, rfl⟩ := hf y
    exact congrArg (fun g => g z) hx
  · intro hx
    ext y
    simp [hx]

private instance certificate_instance_0629 : OAI.SidorenkoCounterexample.ProofCertificate_0629 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11
  exact @certificate_proof_0629 p0 p1 p2 p3 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11

theorem certificate_proof_0630 (B : LinearMap.BilinForm K W)
    (hB : B.Nondegenerate) (f : V →ₗ[K] W) (hf : Function.Surjective f) (x : V) :
    pullbackQuotientEquiv B hB f hf (Submodule.Quotient.mk x) = f x := rfl

private instance certificate_instance_0630 : OAI.SidorenkoCounterexample.ProofCertificate_0630 := by
  constructor
  intro c0 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12
  exact @certificate_proof_0630 p0 p1 p2 p3 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12

theorem certificate_proof_0631 (B : LinearMap.BilinForm K W)
    (hBs : B.IsSymm) (hB : B.Nondegenerate)
    (f : V →ₗ[K] W) (hf : Function.Surjective f)
    (x y : V ⧸ (B.compl₁₂ f f).ker) :
    radicalQuotientForm (B.compl₁₂ f f) (pullback_isSymm B hBs f) x y =
      B (pullbackQuotientEquiv B hB f hf x) (pullbackQuotientEquiv B hB f hf y) := by
  induction x using Submodule.Quotient.induction_on with
  | H x =>
    induction y using Submodule.Quotient.induction_on with
    | H y => rfl

private instance certificate_instance_0631 : OAI.SidorenkoCounterexample.ProofCertificate_0631 := by
  constructor
  intro c0 c1 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14
  exact @certificate_proof_0631 p0 p1 p2 p3 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14

variable [FiniteDimensional K V] [Fintype K] [DecidableEq K]
theorem certificate_proof_0632 (B : LinearMap.BilinForm K W)
    (hBs : B.IsSymm) (hB : B.Nondegenerate)
    (f : V →ₗ[K] W) (hf : Function.Surjective f)
    {ι : Type} [Fintype ι] [DecidableEq ι] (b : Basis ι K W) :
    discriminantSign (B.compl₁₂ f f) (pullback_isSymm B hBs f) =
      quadraticChar K (B.toMatrix b).det := by
  classical
  let e := pullbackQuotientEquiv B hB f hf
  rw [discriminantSign_eq _ _ (b.map e.symm)]
  congr 2
  ext i j
  simp only [LinearMap.BilinForm.toMatrix_apply, Basis.map_apply]
  rw [pullbackQuotientForm B hBs hB f hf]
  simp only [e, LinearEquiv.apply_symm_apply]

private instance certificate_instance_0632 : OAI.SidorenkoCounterexample.ProofCertificate_0632 := by
  constructor
  intro c0 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19
  exact @certificate_proof_0632 p0 p1 p2 p3 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19

end Pullback
section MatrixForms
variable {K n : Type} [Field K] [Fintype n] [DecidableEq n]
theorem certificate_proof_0633 (M : Matrix n n K) (x y : n → K) :
    M.toBilin' x y = (M.transpose.mulVec x) ⬝ᵥ y := by
  rw [Matrix.toBilin'_apply]
  simp only [dotProduct, Matrix.mulVec, Matrix.transpose_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  ring

private instance certificate_instance_0633 : OAI.SidorenkoCounterexample.ProofCertificate_0633 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7
  exact @certificate_proof_0633 p0 p1 p2 p3 q0 q1 q2 q3 q4 q5 q6 q7

theorem certificate_proof_0634 (M : Matrix n n K) :
    M.toBilin'.ker = M.transpose.toLin'.ker := by
  ext x
  simp only [LinearMap.mem_ker, LinearMap.ext_iff, LinearMap.zero_apply,
    matrix_bilin_eval, Matrix.toLin'_apply]
  exact dotProduct_eq_zero_iff

private instance certificate_instance_0634 : OAI.SidorenkoCounterexample.ProofCertificate_0634 := by
  constructor
  intro q0 q1 q2 q3 q4 q5
  exact @certificate_proof_0634 p0 p1 p2 p3 q0 q1 q2 q3 q4 q5

theorem certificate_proof_0635 (M : Matrix n n K) :
    finrank K ((n → K) ⧸ M.toBilin'.ker) = M.rank := by
  have h₁ := M.toBilin'.ker.finrank_quotient_add_finrank
  have h₂ := M.transpose.toLin'.finrank_range_add_finrank_ker
  rw [matrix_bilin_ker] at h₁
  have hr : finrank K M.transpose.toLin'.range = M.transpose.rank := rfl
  rw [hr, Matrix.rank_transpose] at h₂
  rw [matrix_bilin_ker]
  omega

private instance certificate_instance_0635 : OAI.SidorenkoCounterexample.ProofCertificate_0635 := by
  constructor
  intro q0 q1 q2 q3 q4 q5
  exact @certificate_proof_0635 p0 p1 p2 p3 q0 q1 q2 q3 q4 q5

theorem certificate_proof_0636 (M : Matrix n n K) : (-M).rank = M.rank := by
  change finrank K (Matrix.toLin' (-M)).range = finrank K (Matrix.toLin' M).range
  rw [map_neg, LinearMap.range_neg]

private instance certificate_instance_0636 : OAI.SidorenkoCounterexample.ProofCertificate_0636 := by
  constructor
  intro q0 q1 q2 q3 q4 q5
  exact @certificate_proof_0636 p0 p1 p2 p3 q0 q1 q2 q3 q4 q5

end MatrixForms
end SidorenkoCounterexample
namespace SidorenkoCounterexample
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
section FiniteLayer
variable (K : Type) [Field K] (D : ℕ)
variable [Fintype K] [DecidableEq K]
noncomputable instance : Fintype (SymMatrix K D) := Fintype.ofFinite _
theorem certificate_proof_0637 {r : ℕ} (hrD : r ≤ D)
    (R : Matrix (Fin r) (Fin r) K) (hRs : R.IsSymm) (hR : R.det ≠ 0) :
    ∃ Z : SymMatrix K D, Z.val.rank = r ∧
      matrixSign K D Z = quadraticChar K R.det := by
  classical
  let f : (Fin D → K) →ₗ[K] (Fin r → K) :=
    LinearMap.funLeft K K (Fin.castLE hrD)
  have hf : Function.Surjective f :=
    LinearMap.funLeft_surjective_of_injective K K _ (Fin.castLE_injective hrD)
  have hbs : R.toBilin'.IsSymm := Matrix.isSymm_toBilin'_iff_isSymm.mpr hRs
  have hb : R.toBilin'.Nondegenerate :=
    LinearMap.BilinForm.nondegenerate_toBilin'_iff_det_ne_zero.mpr hR
  let B : LinearMap.BilinForm K (Fin D → K) := R.toBilin'.compl₁₂ f f
  have hB : B.IsSymm := pullback_isSymm _ hbs f
  let Z : SymMatrix K D := ⟨B.toMatrix',
    LinearMap.BilinForm.isSymm_toMatrix'_iff_isSymm.mpr hB⟩
  have hz : Z.val.toBilin' = B := Matrix.toBilin'_toMatrix' B
  refine ⟨Z, ?_, ?_⟩
  · rw [← matrix_radical_quotient_rank, hz]
    calc
      finrank K ((Fin D → K) ⧸ B.ker) = finrank K (Fin r → K) :=
        (pullbackQuotientEquiv R.toBilin' hb f hf).finrank_eq
      _ = r := by simp
  · unfold matrixSign
    simp only [hz]
    have he := discriminantSign_pullback R.toBilin' hbs hb f hf
      (Pi.basisFun K (Fin r))
    convert he using 1
    exact congrArg (fun M : Matrix (Fin r) (Fin r) K => quadraticChar K M.det)
      (LinearMap.BilinForm.toMatrix'_toBilin' R).symm

private instance certificate_instance_0637 : OAI.SidorenkoCounterexample.ProofCertificate_0637 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9
  exact @certificate_proof_0637 p0 p1 p2 p3 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9

theorem certificate_proof_0638 {r : ℕ} (hr : 0 < r) (hrD : r ≤ D)
    (hK : ringChar K ≠ 2) {ξ : ℤ} (hξ : ξ = 1 ∨ ξ = -1) :
    ∃ Z : SymMatrix K D, Z.val.rank = r ∧ matrixSign K D Z = ξ := by
  classical
  have ha : ∃ a : K, a ≠ 0 ∧ quadraticChar K a = ξ := by
    rcases hξ with rfl | rfl
    · exact ⟨1, one_ne_zero, map_one _⟩
    · obtain ⟨a, ha⟩ := quadraticChar_exists_neg_one (F := K) hK
      refine ⟨a, ?_, ha⟩
      intro haz
      simp [haz] at ha
  obtain ⟨a, ha, hax⟩ := ha
  let i₀ : Fin r := ⟨0, hr⟩
  let R : Matrix (Fin r) (Fin r) K :=
    Matrix.diagonal fun i => if i = i₀ then a else 1
  have hdet : R.det = a := by
    simp [R, Matrix.det_diagonal]
  obtain ⟨Z, hz, hs⟩ := exists_matrix_of_nonsingular K D hrD R
    (Matrix.isSymm_diagonal _) (hdet ▸ ha)
  exact ⟨Z, hz, hs.trans (hdet ▸ hax)⟩

private instance certificate_instance_0638 : OAI.SidorenkoCounterexample.ProofCertificate_0638 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10
  exact @certificate_proof_0638 p0 p1 p2 p3 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10

theorem certificate_proof_0639 (Z : SymMatrix K D) :
    matrixSign K D (-Z) = quadraticChar K ((-1 : K) ^ Z.val.rank) *
      matrixSign K D Z := by
  have hs := discriminantSign_neg Z.val.toBilin'
    (Matrix.isSymm_toBilin'_iff_isSymm.mpr Z.property)
  simpa only [matrixSign, Submodule.coe_neg, map_neg, matrix_radical_quotient_rank] using hs

private instance certificate_instance_0639 : OAI.SidorenkoCounterexample.ProofCertificate_0639 := by
  constructor
  intro q0 q1 q2 q3 q4 q5
  exact @certificate_proof_0639 p0 p1 p2 p3 q0 q1 q2 q3 q4 q5

theorem certificate_proof_0640 (r : ℕ) (ξ : ℤ) (Z : SymMatrix K D) :
    Z ∈ signedLayer K D r ξ ↔ Z.val.rank = r ∧ matrixSign K D Z = ξ := by
  classical
  simp [signedLayer]

private instance certificate_instance_0640 : OAI.SidorenkoCounterexample.ProofCertificate_0640 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7
  exact @certificate_proof_0640 p0 p1 p2 p3 q0 q1 q2 q3 q4 q5 q6 q7

theorem certificate_proof_0641 {r : ℕ} (hr : 0 < r) (hrD : r ≤ D)
    (hK : ringChar K ≠ 2) {ξ : ℤ} (hξ : ξ = 1 ∨ ξ = -1) :
    (signedLayer K D r ξ).Nonempty := by
  obtain ⟨Z, hz, hs⟩ := exists_matrix_rank_sign K D hr hrD hK hξ
  exact ⟨Z, (mem_signedLayer K D r ξ Z).mpr ⟨hz, hs⟩⟩

private instance certificate_instance_0641 : OAI.SidorenkoCounterexample.ProofCertificate_0641 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10
  exact @certificate_proof_0641 p0 p1 p2 p3 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10

theorem certificate_proof_0642 {r : ℕ} (hr : 0 < r) (hrD : r ≤ D)
    (hK : ringChar K ≠ 2) {ξ : ℤ} (hξ : ξ = 1 ∨ ξ = -1) :
    0 < layerMass K D r ξ := by
  apply div_pos
  · exact_mod_cast (signedLayer_nonempty K D hr hrD hK hξ).card_pos
  · exact_mod_cast Fintype.card_pos (α := SymMatrix K D)

private instance certificate_instance_0642 : OAI.SidorenkoCounterexample.ProofCertificate_0642 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10
  exact @certificate_proof_0642 p0 p1 p2 p3 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10

theorem certificate_proof_0643 (r : ℕ) (ξ : ℤ) (Z : SymMatrix K D) :
    0 ≤ rankKernel K D r ξ Z := by
  classical
  unfold rankKernel layerMass
  split_ifs <;> positivity

private instance certificate_instance_0643 : OAI.SidorenkoCounterexample.ProofCertificate_0643 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7
  exact @certificate_proof_0643 p0 p1 p2 p3 q0 q1 q2 q3 q4 q5 q6 q7

theorem certificate_proof_0644 (r : ℕ) (ξ : ℤ) (Z : SymMatrix K D) :
    -Z ∈ signedLayer K D r ξ ↔
      Z ∈ signedLayer K D r (quadraticChar K ((-1 : K) ^ r) * ξ) := by
  rw [mem_signedLayer, mem_signedLayer]
  have hc := quadraticChar_sq_one (F := K) (pow_ne_zero r (neg_ne_zero.mpr one_ne_zero))
  simp only [Submodule.coe_neg, matrix_rank_neg, matrixSign_neg]
  constructor
  · rintro ⟨hz, hs⟩
    rw [hz] at hs
    refine ⟨hz, ?_⟩
    linear_combination quadraticChar K ((-1 : K) ^ r) * hs -
      matrixSign K D Z * hc
  · rintro ⟨hz, hs⟩
    refine ⟨hz, ?_⟩
    rw [hz, hs]
    linear_combination ξ * hc

private instance certificate_instance_0644 : OAI.SidorenkoCounterexample.ProofCertificate_0644 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7
  exact @certificate_proof_0644 p0 p1 p2 p3 q0 q1 q2 q3 q4 q5 q6 q7

theorem certificate_proof_0645 (r : ℕ) (ξ : ℤ) :
    (signedLayer K D r ξ).card =
      (signedLayer K D r (quadraticChar K ((-1 : K) ^ r) * ξ)).card := by
  classical
  apply Finset.card_bij (fun Z _ => -Z)
  · intro Z hZ
    exact (neg_mem_signedLayer K D r ξ (-Z)).mp (by simpa using hZ)
  · intro Z _ W _ h
    exact neg_injective h
  · intro Z hZ
    exact ⟨-Z, (neg_mem_signedLayer K D r ξ Z).mpr hZ, neg_neg Z⟩

private instance certificate_instance_0645 : OAI.SidorenkoCounterexample.ProofCertificate_0645 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6
  exact @certificate_proof_0645 p0 p1 p2 p3 q0 q1 q2 q3 q4 q5 q6

theorem certificate_proof_0646 (r : ℕ) (ξ : ℤ) (Z : SymMatrix K D) :
    rankKernel K D r ξ (-Z) =
      rankKernel K D r (quadraticChar K ((-1 : K) ^ r) * ξ) Z := by
  classical
  unfold rankKernel
  simp only [neg_mem_signedLayer]
  congr 1
  unfold layerMass
  rw [signedLayer_card_neg]

private instance certificate_instance_0646 : OAI.SidorenkoCounterexample.ProofCertificate_0646 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7
  exact @certificate_proof_0646 p0 p1 p2 p3 q0 q1 q2 q3 q4 q5 q6 q7

end FiniteLayer
theorem certificate_proof_0647 {K : Type} [Field K] [Fintype K] [DecidableEq K]
    (D r : ℕ) (hr : 0 < r) (hrD : r ≤ D) (hK : ringChar K ≠ 2)
    {ξ : ℤ} (hξ : ξ = 1 ∨ ξ = -1) :
    uniformMean (rankKernel K D r ξ) = 1 := by
  classical
  have hs := (signedLayer_nonempty K D hr hrD hK hξ).card_pos
  have hc := Fintype.card_pos (α := SymMatrix K D)
  unfold uniformMean rankKernel
  rw [Finset.sum_ite_mem]
  simp only [Finset.univ_inter, Finset.sum_const, nsmul_eq_mul]
  unfold layerMass
  have hs' : ((signedLayer K D r ξ).card : ℝ) ≠ 0 := by exact_mod_cast hs.ne'
  have hc' : (Fintype.card (SymMatrix K D) : ℝ) ≠ 0 := by exact_mod_cast hc.ne'
  field_simp

private instance certificate_instance_0647 : OAI.SidorenkoCounterexample.ProofCertificate_0647 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10
  exact @certificate_proof_0647 p0 p1 p2 p3 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10

instance (q : OddPrime) : Fact q.val.Prime := ⟨q.property.1⟩
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module LinearMap
theorem certificate_proof_0648 {K V : Type} [Field K] [AddCommGroup V]
    [Module K V] (f : V →ₗ[K] V) :
    LinearMap.range f ⊔ LinearMap.range (LinearMap.id - f) = ⊤ := by
  apply top_unique
  intro x _
  exact Submodule.mem_sup.mpr ⟨f x, ⟨x, rfl⟩, x-f x, ⟨x, rfl⟩, by abel⟩

private instance certificate_instance_0648 : OAI.SidorenkoCounterexample.ProofCertificate_0648 := by
  constructor
  intro q0 q1 q2 q3 q4 q5
  exact @certificate_proof_0648 p0 p1 p2 p3 q0 q1 q2 q3 q4 q5

theorem certificate_proof_0649 {K V : Type} [Field K] [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] (f : V →ₗ[K] V) :
    finrank K (LinearMap.range f) + finrank K (LinearMap.range (LinearMap.id-f)) =
      finrank K V ↔ IsIdempotentElem f := by
  constructor
  · intro h
    have hsum := Submodule.finrank_sup_add_finrank_inf_eq
      (LinearMap.range f) (LinearMap.range (LinearMap.id-f))
    rw [range_sup_complement, finrank_top] at hsum
    have hz : finrank K (LinearMap.range f ⊓ LinearMap.range (LinearMap.id-f) :
        Submodule K V) = 0 := by omega
    have hinf := Submodule.finrank_eq_zero.mp hz
    change f*f = f
    ext x
    have hx₁ : f x-f (f x) ∈ LinearMap.range f := ⟨x-f x, map_sub f x (f x)⟩
    have hx₂ : f x-f (f x) ∈ LinearMap.range (LinearMap.id-f) := ⟨f x, rfl⟩
    have hx : f x-f (f x) ∈ (⊥ : Submodule K V) := by
      rw [← hinf]
      exact ⟨hx₁, hx₂⟩
    have hzero : f x-f (f x) = 0 := hx
    exact (sub_eq_zero.mp hzero).symm
  · intro h
    rw [← h.ker_eq_range]
    exact f.finrank_range_add_finrank_ker

private instance certificate_instance_0649 : OAI.SidorenkoCounterexample.ProofCertificate_0649 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6
  exact @certificate_proof_0649 p0 p1 p2 p3 q0 q1 q2 q3 q4 q5 q6

theorem certificate_proof_0650 {K n : Type} [Field K] [Fintype n]
    [DecidableEq n] (P : Matrix n n K) :
    P.rank + (1-P).rank = Fintype.card n ↔ P*P=P := by
  have h := complementary_rank_iff (Matrix.toLin' P)
  have hdim : finrank K (n → K) = Fintype.card n := Module.finrank_fintype_fun_eq_card K
  rw [← Matrix.toLin'_one, ← map_sub Matrix.toLin'] at h
  change P.rank+(1-P).rank = finrank K (n → K) ↔ IsIdempotentElem (Matrix.toLin' P) at h
  rw [hdim] at h
  rw [h]
  change (Matrix.toLin' P).comp (Matrix.toLin' P) = Matrix.toLin' P ↔ _
  rw [← Matrix.toLin'_mul, Matrix.toLin'.injective.eq_iff]

private instance certificate_instance_0650 : OAI.SidorenkoCounterexample.ProofCertificate_0650 := by
  constructor
  intro q0 q1 q2 q3 q4 q5
  exact @certificate_proof_0650 p0 p1 p2 p3 q0 q1 q2 q3 q4 q5

theorem certificate_proof_0651 {K n : Type} [Field K] [Fintype n] [DecidableEq n]
    (r : ℕ) (hdim : Fintype.card n = 2*r) (A B : Matrix n n K)
    (hB : B.det ≠ 0) (hA : A.rank = r) :
    (B-A).rank = r ↔ A*B⁻¹*A=A := by
  have hu : IsUnit B.det := isUnit_iff_ne_zero.mpr hB
  have hBi : B⁻¹.det ≠ 0 := by simpa [Matrix.det_nonsing_inv] using inv_ne_zero hB
  have hPr : (A*B⁻¹).rank = r := (Matrix.rank_mul_eq_left_of_det_ne_zero _ _ hBi).trans hA
  have hQr : (1-A*B⁻¹).rank = (B-A).rank := by
    rw [show 1-A*B⁻¹ = (B-A)*B⁻¹ by rw [sub_mul, Matrix.mul_nonsing_inv B hu]]
    exact Matrix.rank_mul_eq_left_of_det_ne_zero _ _ hBi
  have hmain := matrix_complementary_rank_iff (A*B⁻¹)
  rw [hPr, hQr, hdim] at hmain
  have hsum : r+(B-A).rank=2*r ↔ (B-A).rank=r := by omega
  rw [hsum] at hmain
  rw [hmain]
  constructor
  · intro h
    have hm := congrArg (fun M => M*B) h
    simpa only [Matrix.mul_assoc, Matrix.nonsing_inv_mul B hu, Matrix.mul_one] using hm
  · intro h
    calc
      (A*B⁻¹)*(A*B⁻¹) = (A*B⁻¹*A)*B⁻¹ := by simp only [Matrix.mul_assoc]
      _ = A*B⁻¹ := by rw [h]

private instance certificate_instance_0651 : OAI.SidorenkoCounterexample.ProofCertificate_0651 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10
  exact @certificate_proof_0651 p0 p1 p2 p3 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10

end SidorenkoCounterexample
end
section
namespace SidorenkoCounterexample
open Module
open scoped BigOperators
section Border
variable {K : Type} [Field K]
theorem certificate_proof_0652 {n : ℕ} (M : SymMatrix K n) (z : Fin n → K) (a : K)
    (hM : M.val.det ≠ 0) :
    (symmetricBorder M z a).val.det = M.val.det * (a - z ⬝ᵥ (M.val⁻¹.mulVec z)) := by
  classical
  let := Matrix.invertibleOfIsUnitDet M.val (isUnit_iff_ne_zero.mpr hM)
  rw [symmetricBorder,Matrix.det_submatrix_equiv_self]
  dsimp only [borderRaw]
  rw [Matrix.det_fromBlocks₁₁]
  congr 1
  rw [Matrix.det_unique]
  simp only [Matrix.sub_apply, Matrix.mul_apply, Matrix.of_apply,
    Matrix.invOf_eq_nonsing_inv, dotProduct, Matrix.mulVec, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  simp only [mul_assoc]

private instance certificate_instance_0652 : OAI.SidorenkoCounterexample.ProofCertificate_0652 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6
  exact @certificate_proof_0652 p0 p1 p2 p3 q0 q1 q2 q3 q4 q5 q6

end Border
end SidorenkoCounterexample
end
section
namespace SidorenkoCounterexample
open scoped BigOperators
section Mean
variable {A B : Type} [Fintype A] [Fintype B]
theorem certificate_proof_0653 {f g : A → ℝ} (h : ∀ a, f a = g a) :
    uniformMean f = uniformMean g := by
  unfold uniformMean
  congr 1
  exact Finset.sum_congr rfl fun a _ => h a

private instance certificate_instance_0653 : OAI.SidorenkoCounterexample.ProofCertificate_0653 := by
  constructor
  intro q0 q1 q2 q3 q4
  exact @certificate_proof_0653 p0 p1 p2 p3 q0 q1 q2 q3 q4

end Mean
end SidorenkoCounterexample
end
end OAI

theorem solution : OAI.SidorenkoCounterexample.ProofCertificate_0614 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0615 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0616 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0617 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0618 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0619 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0620 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0621 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0622 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0623 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0624 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0625 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0626 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0627 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0628 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0629 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0630 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0631 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0632 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0633 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0634 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0635 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0636 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0637 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0638 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0639 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0640 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0641 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0642 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0643 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0644 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0645 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0646 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0647 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0648 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0649 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0650 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0651 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0652 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0653 := by
  exact ⟨inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance⟩
end

