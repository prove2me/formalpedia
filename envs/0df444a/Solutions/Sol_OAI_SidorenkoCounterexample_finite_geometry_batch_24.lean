-- Prove2me | solution 1 for OAI.SidorenkoCounterexample.finite_geometry_batch_24
-- status  : ACCEPTED   (prove)
-- author  : @abcdefg
-- created : 2026-10-09T06:23:31.905203+00:00
-- url     : https://prove2.me/submissions/65c89bd2-d697-4551-851f-d8608db1f123

import Definitions.Def_SidorenkoCertificateBundleB
set_option linter.unusedVariables false
section
variable [p0 : OAI.SidorenkoCounterexample.ProofCertificate_0006]
  [p1 : OAI.SidorenkoCounterexample.ProofCertificate_0044]
  [p2 : OAI.SidorenkoCounterexample.ProofCertificate_0059]
  [p3 : OAI.SidorenkoCounterexample.ProofCertificate_0635]
  [p4 : OAI.SidorenkoCounterexample.ProofCertificate_0653]
  [p5 : OAI.SidorenkoCounterexample.ProofCertificate_0654]
  [p6 : OAI.SidorenkoCounterexample.ProofCertificate_0664]
  [p7 : OAI.SidorenkoCounterexample.ProofCertificate_0678]
  [p8 : OAI.SidorenkoCounterexample.ProofCertificate_0682]
  [p9 : OAI.SidorenkoCounterexample.ProofCertificate_0683]
  [p10 : OAI.SidorenkoCounterexample.ProofCertificate_0684]
  [p11 : OAI.SidorenkoCounterexample.ProofCertificate_0685]
  [p12 : OAI.SidorenkoCounterexample.ProofCertificate_0686]
  [p13 : OAI.SidorenkoCounterexample.ProofCertificate_0687]
  [p14 : OAI.SidorenkoCounterexample.ProofCertificate_0694]
include p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14

namespace OAI
section
namespace SidorenkoCounterexample
open scoped BigOperators
section Scalar
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
end Scalar
section MatrixSign
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
end MatrixSign
end SidorenkoCounterexample
end
section
namespace SidorenkoCounterexample
open Module LinearMap
section NondegSign
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
variable [FiniteDimensional K V] [Fintype K] [DecidableEq K]
end NondegSign
section SumForms
variable {K V W : Type} [Field K] [AddCommGroup V] [Module K V]
  [AddCommGroup W] [Module K W]
variable [FiniteDimensional K V] [Fintype K] [DecidableEq K]
end SumForms
section PairSign
variable {K n : Type} [Field K] [Fintype n] [DecidableEq n]
variable [Fintype K] [DecidableEq K]
end PairSign
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module LinearMap
section RadicalCount
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Fintype K] [DecidableEq K]
end RadicalCount
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module LinearMap
open scoped BigOperators
section RankCard
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Fintype K] [DecidableEq K]
end RankCard
section LayerCard
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
theorem certificate_proof_0695 (D r : ℕ) (hrD : r ≤ D) {ξ : ℤ} (hξ : ξ = 1 ∨ ξ = -1) :
    (signedLayer K D r ξ).card =
      Nat.card (DimSubspace K (Fin D → K) (D-r)) *
        Nat.card {M : SymMatrix K r // quadraticChar K M.val.det = ξ} := by
  classical
  have e : {M : SymMatrix K D // M.val.rank = r ∧ matrixSign K D M = ξ} ≃
      {B : SymForm K (Fin D → K) // finrank K B.val.ker = D-r ∧
        discriminantSign B.val B.property = ξ} := by
    apply (matrixFormEquiv D).subtypeEquiv
    intro M
    change (M.val.rank = r ∧ matrixSign K D M = ξ) ↔
      (finrank K M.val.toBilin'.ker = D-r ∧ matrixSign K D M = ξ)
    have h := M.val.toBilin'.ker.finrank_quotient_add_finrank
    rw [matrix_radical_quotient_rank] at h
    simp only [Module.finrank_pi, Fintype.card_fin] at h
    omega
  calc
    _ = Nat.card {M : SymMatrix K D // M.val.rank = r ∧ matrixSign K D M = ξ} := by
      simp only [signedLayer, Nat.card_eq_fintype_card, Fintype.card_subtype]
    _ = _ := by
      rw [Nat.card_congr e, signedNullityForm_card (D-r) (by simp) hξ]
      have hd : finrank K (Fin D → K) = D := by simp
      rw [hd, Nat.sub_sub_self hrD]

private instance certificate_instance_0695 : OAI.SidorenkoCounterexample.ProofCertificate_0695 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8
  exact @certificate_proof_0695 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 q0 q1 q2 q3 q4 q5 q6 q7 q8

theorem certificate_proof_0696 (r : ℕ) (ξ : ℤ) :
    symmetricSignProb (K := K) r ξ =
      (Nat.card {M : SymMatrix K r // quadraticChar K M.val.det = ξ} : ℝ) /
        (Fintype.card K : ℝ)^((r+1).choose 2) := by
  unfold symmetricSignProb characterSignIndicator
  rw [uniformMean_indicator, ← Nat.card_eq_fintype_card (α := SymMatrix K r), symMatrix_card]
  simp only [Nat.card_eq_fintype_card, Nat.cast_pow]

private instance certificate_instance_0696 : OAI.SidorenkoCounterexample.ProofCertificate_0696 := by
  constructor
  intro q0 q1 q2 q3 q4 q5
  exact @certificate_proof_0696 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 q0 q1 q2 q3 q4 q5

theorem certificate_proof_0697 (D r : ℕ) (hrD : r ≤ D) {ξ : ℤ} (hξ : ξ = 1 ∨ ξ = -1) :
    layerMass K D r ξ =
      (Nat.card (DimSubspace K (Fin D → K) (D-r)) : ℝ) *
        (Fintype.card K : ℝ)^((r+1).choose 2) * symmetricSignProb (K := K) r ξ /
        (Fintype.card K : ℝ)^((D+1).choose 2) := by
  unfold layerMass
  rw [signedLayer_card_exact D r hrD hξ, ← Nat.card_eq_fintype_card, symMatrix_card,
    symmetricSignProb_card]
  push_cast
  have hq : (Fintype.card K : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  field_simp

private instance certificate_instance_0697 : OAI.SidorenkoCounterexample.ProofCertificate_0697 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8
  exact @certificate_proof_0697 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 q0 q1 q2 q3 q4 q5 q6 q7 q8

end LayerCard
end SidorenkoCounterexample
end
section
namespace SidorenkoCounterexample
open Module LinearMap
open scoped BigOperators
section Binary
variable {K : Type} [Field K] [Fintype K]
theorem certificate_proof_0698 (hK : ringChar K ≠ 2) (a b t : K)
    (ha : a ≠ 0) (hb : b ≠ 0) : ∃ x y : K, a*x^2+b*y^2=t := by
  open Polynomial in
  have hf : (C a * X^2 : K[X]).degree = 2 := degree_C_mul_X_pow 2 ha
  open Polynomial in
  have hg : (C b * X^2 - C t : K[X]).degree = 2 := by
    rw [degree_sub_C (by rw [degree_C_mul_X_pow 2 hb]; decide), degree_C_mul_X_pow 2 hb]
    norm_num
  obtain ⟨x,y,hxy⟩ := FiniteField.exists_root_sum_quadratic hf hg
    (FiniteField.odd_card_of_char_ne_two hK)
  refine ⟨x,y,?_⟩
  simpa only [Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X,
    ← add_sub_assoc, sub_eq_zero] using hxy

private instance certificate_instance_0698 : OAI.SidorenkoCounterexample.ProofCertificate_0698 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8
  exact @certificate_proof_0698 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 q0 q1 q2 q3 q4 q5 q6 q7 q8

end Binary
section Norms
variable {K E : Type} [Field K] [AddCommGroup E] [Module K E]
  [FiniteDimensional K E]
theorem certificate_proof_0699 (B : LinearMap.BilinForm K E)
    (hB : B.Nondegenerate) (hd : 0 < finrank K E) : B ≠ 0 := by
  intro h
  have hz : ∀ x : E, x=0 := by
    intro x
    apply hB.1
    intro y
    rw [h]
    rfl
  have hzdim : finrank K E=0 := (finrank_zero_iff_forall_zero).mpr hz
  omega

private instance certificate_instance_0699 : OAI.SidorenkoCounterexample.ProofCertificate_0699 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8
  exact @certificate_proof_0699 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 q0 q1 q2 q3 q4 q5 q6 q7 q8

theorem certificate_proof_0700 (B : LinearMap.BilinForm K E) {x : E}
    (hx : B x x ≠ 0) : finrank K (B.orthogonal (K ∙ x)) + 1 = finrank K E := by
  have hx0 : x ≠ 0 := by intro h; subst x; simp at hx
  have h := Submodule.finrank_add_eq_of_isCompl (B.isCompl_span_singleton_orthogonal hx)
  rw [finrank_span_singleton hx0] at h
  omega

private instance certificate_instance_0700 : OAI.SidorenkoCounterexample.ProofCertificate_0700 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8
  exact @certificate_proof_0700 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 q0 q1 q2 q3 q4 q5 q6 q7 q8

variable [Fintype K]
theorem certificate_proof_0701 (B : LinearMap.BilinForm K E) (hs : B.IsSymm)
    (hB : B.Nondegenerate) (hD : 2 ≤ finrank K E) (hK : ringChar K ≠ 2) (t : K) :
    ∃ v : E, B v v = t := by
  let : Invertible (2 : K) := invertibleOfNonzero (Ring.two_ne_zero hK)
  obtain ⟨x,hx⟩ := LinearMap.BilinForm.exists_bilinForm_self_ne_zero
    (nondegenerate_ne_zero_of_pos B hB (by omega)) (LinearMap.BilinForm.isSymm_iff.mp hs)
  let P := B.orthogonal (K ∙ x)
  have hPs : (B.restrict P).IsSymm := by constructor; intro u v; exact hs.eq _ _
  have hP := B.restrict_nondegenerate_orthogonal_spanSingleton hB hs.isRefl hx
  have hd : 0 < finrank K P := by have := orthogonal_line_finrank B hx; dsimp [P]; omega
  obtain ⟨y,hy⟩ := LinearMap.BilinForm.exists_bilinForm_self_ne_zero
    (nondegenerate_ne_zero_of_pos (B.restrict P) hP hd) (LinearMap.BilinForm.isSymm_iff.mp hPs)
  obtain ⟨a,b,hab⟩ := binary_norm_surjective hK (B x x) (B y.val y.val) t hx hy
  have hxy : B x y.val = 0 := y.property x (Submodule.mem_span_singleton_self x)
  have hyx : B y.val x = 0 := (hs.eq _ _).trans hxy
  refine ⟨a • x + b • y.val, ?_⟩
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
    hxy, hyx, mul_zero, add_zero, zero_add]
  linear_combination hab

private instance certificate_instance_0701 : OAI.SidorenkoCounterexample.ProofCertificate_0701 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12
  exact @certificate_proof_0701 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12

end Norms
section Equivalences
variable {K E F : Type} [Field K] [AddCommGroup E] [Module K E]
  [AddCommGroup F] [Module K F]
theorem certificate_proof_0702 (a x y : K) : scalarBilin a x y = a*x*y := by
  simp only [scalarBilin, LinearMap.smul_apply, LinearMap.mul_apply', smul_eq_mul]
  ring

private instance certificate_instance_0702 : OAI.SidorenkoCounterexample.ProofCertificate_0702 := by
  constructor
  intro q0 q1 q2 q3 q4
  exact @certificate_proof_0702 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 q0 q1 q2 q3 q4

theorem certificate_proof_0703 (a : K) : (scalarBilin a).IsSymm := by
  constructor; intro x y; simp only [scalarBilin_apply]; ring

private instance certificate_instance_0703 : OAI.SidorenkoCounterexample.ProofCertificate_0703 := by
  constructor
  intro q0 q1 q2
  exact @certificate_proof_0703 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 q0 q1 q2

theorem certificate_proof_0704 (a : K) (ha : a≠0) : (scalarBilin a).Nondegenerate := by
  constructor
  · intro x hx; have h := hx 1; simpa only [scalarBilin_apply, mul_one, mul_eq_zero,ha,false_or] using h
  · intro x hx; have h := hx 1; simpa only [scalarBilin_apply, mul_one, mul_eq_zero,ha,false_or] using h

private instance certificate_instance_0704 : OAI.SidorenkoCounterexample.ProofCertificate_0704 := by
  constructor
  intro q0 q1 q2 q3
  exact @certificate_proof_0704 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 q0 q1 q2 q3

theorem certificate_proof_0705 (B : LinearMap.BilinForm K E) (x : E)
    (hx : B x x ≠ 0) (z : K × B.orthogonal (K ∙ x)) :
    lineOrthogonalEquiv B x hx z = z.1 • x + z.2.val := rfl

private instance certificate_instance_0705 : OAI.SidorenkoCounterexample.ProofCertificate_0705 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8
  exact @certificate_proof_0705 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 q0 q1 q2 q3 q4 q5 q6 q7 q8

theorem certificate_proof_0706 (B : LinearMap.BilinForm K E) (hs : B.IsSymm)
    (x : E) (hx : B x x ≠ 0) (z w : K × B.orthogonal (K ∙ x)) :
    B (lineOrthogonalEquiv B x hx z) (lineOrthogonalEquiv B x hx w) =
      B x x * z.1 * w.1 + B z.2.val w.2.val := by
  have h1 : B x w.2.val = 0 := w.2.property x (Submodule.mem_span_singleton_self x)
  have h2 : B z.2.val x = 0 := (hs.eq _ _).trans (z.2.property x (Submodule.mem_span_singleton_self x))
  rw [lineOrthogonalEquiv_apply, lineOrthogonalEquiv_apply]
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
    smul_eq_mul,h1,h2,mul_zero,add_zero,zero_add]
  ring

private instance certificate_instance_0706 : OAI.SidorenkoCounterexample.ProofCertificate_0706 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10
  exact @certificate_proof_0706 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10

variable [FiniteDimensional K E] [FiniteDimensional K F] [Fintype K] [DecidableEq K]
theorem certificate_proof_0707 (B : LinearMap.BilinForm K E)
    (C : LinearMap.BilinForm K F) (hs : B.IsSymm) (ht : C.IsSymm)
    (hB : B.Nondegenerate) (hC : C.Nondegenerate)
    (e : E ≃ₗ[K] F) (he : ∀ x y, C (e x) (e y) = B x y) :
    discriminantSign B hs = discriminantSign C ht := by
  rw [discriminantSign_nondegenerate B hs hB (Module.finBasis K E),
    discriminantSign_nondegenerate C ht hC ((Module.finBasis K E).map e)]
  congr 2
  ext i j
  simp only [LinearMap.BilinForm.toMatrix_apply, Basis.map_apply, he]

private instance certificate_instance_0707 : OAI.SidorenkoCounterexample.ProofCertificate_0707 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19
  exact @certificate_proof_0707 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19

theorem certificate_proof_0708 (B : LinearMap.BilinForm K E)
    (C : LinearMap.BilinForm K F) (hs : B.IsSymm) (ht : C.IsSymm)
    (hB : B.Nondegenerate) (hC : C.Nondegenerate) :
    discriminantSign (orthogonalSumForm B C) (orthogonalSumForm_isSymm B C hs ht) =
      discriminantSign B hs * discriminantSign C ht := by
  rw [discriminantSign_nondegenerate _ _ (orthogonalSumForm_nondegenerate B C hB hC)
      ((Module.finBasis K E).prod (Module.finBasis K F)), orthogonalSumForm_matrix,
    Matrix.det_fromBlocks_zero₂₁, map_mul,
    discriminantSign_nondegenerate B hs hB (Module.finBasis K E),
    discriminantSign_nondegenerate C ht hC (Module.finBasis K F)]

private instance certificate_instance_0708 : OAI.SidorenkoCounterexample.ProofCertificate_0708 := by
  constructor
  intro c0 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17
  exact @certificate_proof_0708 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17

theorem certificate_proof_0709 (a : K) (ha : a≠0) :
    discriminantSign (scalarBilin a) (scalarBilin_symm a) = quadraticChar K a := by
  rw [discriminantSign_nondegenerate _ _ (scalarBilin_nondegenerate a ha)
    (Basis.singleton Unit K), Matrix.det_unique]
  simp only [LinearMap.BilinForm.toMatrix_apply, Basis.singleton_apply, scalarBilin_apply, mul_one]

private instance certificate_instance_0709 : OAI.SidorenkoCounterexample.ProofCertificate_0709 := by
  constructor
  intro c0 q0 q1 q2 q3 q4 q5
  exact @certificate_proof_0709 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 q0 q1 q2 q3 q4 q5

theorem certificate_proof_0710 (B : LinearMap.BilinForm K E)
    (hs : B.IsSymm) (hB : B.Nondegenerate) (x : E) (hx : B x x ≠ 0) :
    discriminantSign B hs = quadraticChar K (B x x) *
      discriminantSign (B.restrict (B.orthogonal (K ∙ x)))
        (by constructor; intro u v; exact hs.eq u.val v.val) := by
  let P := B.orthogonal (K ∙ x)
  have hp : (B.restrict P).IsSymm := by constructor; intro u v; exact hs.eq _ _
  have hP := B.restrict_nondegenerate_orthogonal_spanSingleton hB hs.isRefl hx
  have he : discriminantSign (orthogonalSumForm (scalarBilin (B x x)) (B.restrict P))
      (orthogonalSumForm_isSymm _ _ (scalarBilin_symm _) hp) = discriminantSign B hs :=
    discriminantSign_isometry _ _ _ hs
      (orthogonalSumForm_nondegenerate _ _ (scalarBilin_nondegenerate _ hx) hP) hB
      (lineOrthogonalEquiv B x hx) (fun z w => by
        simpa only [orthogonalSumForm_apply,scalarBilin_apply,LinearMap.BilinForm.restrict_apply,LinearMap.domRestrict_apply] using lineOrthogonalEquiv_form B hs x hx z w)
  rw [← he, discriminantSign_orthogonalSum _ _ (scalarBilin_symm _) hp (scalarBilin_nondegenerate _ hx) hP,
    discriminantSign_scalar _ hx]

private instance certificate_instance_0710 : OAI.SidorenkoCounterexample.ProofCertificate_0710 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12
  exact @certificate_proof_0710 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12

end Equivalences
section Classification
variable {K E F : Type} [Field K] [AddCommGroup E] [Module K E]
  [AddCommGroup F] [Module K F] [FiniteDimensional K E] [FiniteDimensional K F]
  [Fintype K] [DecidableEq K]
theorem certificate_proof_0711 (a b : K) (ha : a≠0) (hb : b≠0)
    (h : quadraticChar K a = quadraticChar K b) : BilinEquivalent (scalarBilin a) (scalarBilin b) := by
  have hc : quadraticChar K (a*b) = 1 := by
    rw [map_mul,h,←pow_two,quadraticChar_sq_one hb]
  obtain ⟨t,ht⟩ := (quadraticChar_one_iff_isSquare (mul_ne_zero ha hb)).mp hc
  have ht0 : t≠0 := by intro hz; rw [hz,mul_zero] at ht; exact mul_ne_zero ha hb ht
  have hscale : b*(t/b)^2=a := by
    field_simp
    linear_combination ht.symm
  refine ⟨LinearEquiv.smulOfNeZero K K (t/b) (div_ne_zero ht0 hb), ?_⟩
  intro x y
  simp only [LinearEquiv.smulOfNeZero_apply,smul_eq_mul,scalarBilin_apply]
  linear_combination x*y*hscale

private instance certificate_instance_0711 : OAI.SidorenkoCounterexample.ProofCertificate_0711 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8
  exact @certificate_proof_0711 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 q0 q1 q2 q3 q4 q5 q6 q7 q8

omit [Fintype K] [DecidableEq K] in
theorem certificate_proof_0712 (B : LinearMap.BilinForm K E) (hD : finrank K E=1) :
    ∃ e : K ≃ₗ[K] E, ∀ s t : K, B (e s) (e t) = B (e 1) (e 1)*s*t := by
  let e := LinearEquiv.ofFinrankEq (R := K) K E (by simpa using hD.symm)
  refine ⟨e,?_⟩
  intro s t
  have hs : e s = s • e 1 := by rw [←map_smul]; simp
  have ht : e t = t • e 1 := by rw [←map_smul]; simp
  rw [hs,ht]
  simp only [map_smul,LinearMap.smul_apply,smul_eq_mul]
  ring

private instance certificate_instance_0712 : OAI.SidorenkoCounterexample.ProofCertificate_0712 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7
  exact @certificate_proof_0712 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 q0 q1 q2 q3 q4 q5 q6 q7

theorem certificate_proof_0713 (B : LinearMap.BilinForm K E) (C : LinearMap.BilinForm K F)
    (hs : B.IsSymm) (ht : C.IsSymm) (hB : B.Nondegenerate) (hC : C.Nondegenerate)
    (hE : finrank K E=1) (hF : finrank K F=1)
    (h : discriminantSign B hs = discriminantSign C ht) : BilinEquivalent B C := by
  obtain ⟨e,he⟩ := one_dimensional_form B hE
  obtain ⟨f,hf⟩ := one_dimensional_form C hF
  have ha : B (e 1) (e 1)≠0 := by
    intro hz
    have he1 : e 1=0 := hB.1 _ (fun y => by
      obtain ⟨s,rfl⟩ := e.surjective y
      rw [he,hz]; simp)
    have : (1:K)=0 := e.injective (he1.trans e.map_zero.symm)
    exact one_ne_zero this
  have hb : C (f 1) (f 1)≠0 := by
    intro hz
    have hf1 : f 1=0 := hC.1 _ (fun y => by
      obtain ⟨s,rfl⟩ := f.surjective y
      rw [hf,hz]; simp)
    exact one_ne_zero (f.injective (hf1.trans f.map_zero.symm))
  have hsa := discriminantSign_isometry (scalarBilin (B (e 1) (e 1))) B
    (scalarBilin_symm _) hs (scalarBilin_nondegenerate _ ha) hB e
    (fun s t => by simpa only [scalarBilin_apply] using he s t)
  have hsb := discriminantSign_isometry (scalarBilin (C (f 1) (f 1))) C
    (scalarBilin_symm _) ht (scalarBilin_nondegenerate _ hb) hC f
    (fun s t => by simpa only [scalarBilin_apply] using hf s t)
  rw [discriminantSign_scalar _ ha] at hsa
  rw [discriminantSign_scalar _ hb] at hsb
  obtain ⟨g,hg⟩ := scalarBilin_equivalent_of_sign _ _ ha hb (hsa.trans (h.trans hsb.symm))
  refine ⟨e.symm.trans (g.trans f), ?_⟩
  intro x y
  change C (f (g (e.symm x))) (f (g (e.symm y))) = B x y
  rw [hf]
  have hg' := hg (e.symm x) (e.symm y)
  simp only [scalarBilin_apply] at hg'
  rw [hg']
  have hx := he (e.symm x) (e.symm y)
  simpa only [e.apply_symm_apply,scalarBilin_apply] using hx.symm

private instance certificate_instance_0713 : OAI.SidorenkoCounterexample.ProofCertificate_0713 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19 q20
  exact @certificate_proof_0713 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19 q20

theorem certificate_proof_0714 (B : LinearMap.BilinForm K E)
    (C : LinearMap.BilinForm K F) (hs : B.IsSymm) (ht : C.IsSymm)
    (hB : B.Nondegenerate) (hC : C.Nondegenerate) (hK : ringChar K≠2)
    (hd : finrank K E = finrank K F)
    (h : discriminantSign B hs = discriminantSign C ht) : BilinEquivalent B C := by
  suffices ∀ n, finrank K E=n → finrank K F=n → BilinEquivalent B C by exact this _ rfl hd.symm
  intro n hnE hnF
  induction n using Nat.strong_induction_on generalizing E F with
  | h n ih =>
    by_cases hn0 : n=0
    · let e := LinearEquiv.ofFinrankEq E F (hnE.trans hnF.symm)
      have hzero : Subsingleton E := Module.finrank_zero_iff.mp (hnE.trans hn0)
      refine ⟨e,?_⟩
      intro x y
      have hx : x=0 := Subsingleton.elim _ _
      simp only [hx,map_zero,LinearMap.zero_apply]
    by_cases hn1 : n=1
    · exact one_dimensional_equivalent B C hs ht hB hC (hnE.trans hn1) (hnF.trans hn1) h
    have hn2 : 2≤n := by omega
    obtain ⟨x,hx⟩ := symmetric_norm_surjective B hs hB (by omega) hK 1
    obtain ⟨y,hy⟩ := symmetric_norm_surjective C ht hC (by omega) hK 1
    have hx0 : B x x≠0 := hx ▸ one_ne_zero
    have hy0 : C y y≠0 := hy ▸ one_ne_zero
    let P := B.orthogonal (K ∙ x)
    let Q := C.orthogonal (K ∙ y)
    have hp : (B.restrict P).IsSymm := by constructor; intro u v; exact hs.eq _ _
    have hq : (C.restrict Q).IsSymm := by constructor; intro u v; exact ht.eq _ _
    have hP := B.restrict_nondegenerate_orthogonal_spanSingleton hB hs.isRefl hx0
    have hQ := C.restrict_nondegenerate_orthogonal_spanSingleton hC ht.isRefl hy0
    have hdP : finrank K P=n-1 := by have := orthogonal_line_finrank B hx0; dsimp [P]; omega
    have hdQ : finrank K Q=n-1 := by have := orthogonal_line_finrank C hy0; dsimp [Q]; omega
    have hdPQ : finrank K P=finrank K Q := hdP.trans hdQ.symm
    have hsP := discriminantSign_line_complement B hs hB x hx0
    have hsQ := discriminantSign_line_complement C ht hC y hy0
    rw [hx,map_one,one_mul] at hsP
    rw [hy,map_one,one_mul] at hsQ
    have hh : discriminantSign (B.restrict P) hp = discriminantSign (C.restrict Q) hq :=
      hsP.symm.trans (h.trans hsQ)
    obtain ⟨g,hg⟩ := ih (n-1) (by omega) (B.restrict P) (C.restrict Q) hp hq hP hQ hdPQ hh hdP hdQ
    let e := (lineOrthogonalEquiv B x hx0).symm.trans
      (((LinearEquiv.refl K K).prodCongr g).trans (lineOrthogonalEquiv C y hy0))
    refine ⟨e,?_⟩
    intro v w
    let a := (lineOrthogonalEquiv B x hx0).symm v
    let b := (lineOrthogonalEquiv B x hx0).symm w
    change C (lineOrthogonalEquiv C y hy0 (a.1,g a.2))
      (lineOrthogonalEquiv C y hy0 (b.1,g b.2)) = B v w
    rw [lineOrthogonalEquiv_form C ht,hy]
    change 1*a.1*b.1 + (C.restrict Q) (g a.2) (g b.2) = B v w
    rw [hg]
    have he := lineOrthogonalEquiv_form B hs x hx0 a b
    rw [hx] at he
    simpa only [a,b,LinearEquiv.apply_symm_apply,LinearMap.BilinForm.restrict_apply,LinearMap.domRestrict_apply] using he.symm

private instance certificate_instance_0714 : OAI.SidorenkoCounterexample.ProofCertificate_0714 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19 q20
  exact @certificate_proof_0714 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19 q20

end Classification
end SidorenkoCounterexample
end
section
namespace SidorenkoCounterexample
open Module
open scoped BigOperators
section LinearMean
variable {K U W : Type} [Field K] [AddCommGroup U] [Module K U]
  [AddCommGroup W] [Module K W] [Fintype U] [Fintype W]
theorem certificate_proof_0715 (f : U →ₗ[K] W) (hf : Function.Surjective f)
    (g : W → ℝ) : uniformMean (g ∘ f) = uniformMean g := by
  classical
  have hcard (y : W) : Fintype.card {x : U // f x = y} = Fintype.card f.ker := by
    simpa [Fintype.card_subtype, LinearMap.mem_ker] using
      AddMonoidHom.card_fiber_eq_of_mem_range f (hf y) (hf 0)
  have hc : Fintype.card U = Fintype.card W * Fintype.card f.ker := by
    simpa only [Nat.card_eq_fintype_card] using surjective_linear_card f hf
  unfold uniformMean
  simp only [Function.comp_def]
  rw [←Fintype.sum_fiberwise f (fun x => g (f x))]
  have hs (y : W) : (∑ x : {x : U // f x=y}, g (f x.val)) =
      (Fintype.card f.ker : ℝ)*g y := by
    have he (x : {x : U // f x=y}) : g (f x.val)=g y := congrArg g x.property
    simp only [he,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,hcard]
  simp only [hs]
  rw [←Finset.mul_sum, hc, Nat.cast_mul]
  have hk : (Fintype.card f.ker : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  field_simp

private instance certificate_instance_0715 : OAI.SidorenkoCounterexample.ProofCertificate_0715 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12
  exact @certificate_proof_0715 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12

end LinearMean
section Forms
variable {K V : Type} [Field K] [Fintype K] [DecidableEq K]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]
theorem certificate_proof_0716 {ι : Type} [Fintype ι] [DecidableEq ι]
    (b : Basis ι K V) {ξ : ℤ} (hξ : ξ=1 ∨ ξ = -1) (Q : SymForm K V) :
    formSignIndicator ξ Q = characterSignIndicator ξ (Q.val.toMatrix b).det := by
  by_cases h : Q.val.Nondegenerate
  · simp only [formSignIndicator,h,ite_true,characterSignIndicator,
      discriminantSign_nondegenerate Q.val Q.property h b]
  · have hd : (Q.val.toMatrix b).det=0 := by
      simpa only [LinearMap.BilinForm.nondegenerate_iff_det_ne_zero b,not_not] using h
    rcases hξ with rfl | rfl <;>
      simp [formSignIndicator,h,characterSignIndicator,hd]

private instance certificate_instance_0716 : OAI.SidorenkoCounterexample.ProofCertificate_0716 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14
  exact @certificate_proof_0716 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14

omit [Fintype K] [FiniteDimensional K V] in
theorem certificate_proof_0717 {ι : Type} [Fintype ι] [DecidableEq ι]
    (b : Basis ι K V) (Q : SymForm K V) :
    formSingularIndicator Q = if (Q.val.toMatrix b).det=0 then 1 else 0 := by
  simp only [formSingularIndicator,LinearMap.BilinForm.nondegenerate_iff_det_ne_zero b]
  split <;> simp_all

private instance certificate_instance_0717 : OAI.SidorenkoCounterexample.ProofCertificate_0717 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10
  exact @certificate_proof_0717 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10

theorem certificate_proof_0718 (ξ : ℤ) (Q : SymForm K V) : 0 ≤ formSignIndicator ξ Q := by
  unfold formSignIndicator; split <;> (try split) <;> norm_num

private instance certificate_instance_0718 : OAI.SidorenkoCounterexample.ProofCertificate_0718 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9
  exact @certificate_proof_0718 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9

theorem certificate_proof_0719 (ξ : ℤ) (Q : SymForm K V) : formSignIndicator ξ Q ≤ 1 := by
  unfold formSignIndicator; split <;> (try split) <;> norm_num

private instance certificate_instance_0719 : OAI.SidorenkoCounterexample.ProofCertificate_0719 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9
  exact @certificate_proof_0719 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9

omit [Fintype K] [DecidableEq K] [FiniteDimensional K V] in
theorem certificate_proof_0720 (Q : SymForm K V) : 0 ≤ formSingularIndicator Q := by
  unfold formSingularIndicator; split <;> norm_num

private instance certificate_instance_0720 : OAI.SidorenkoCounterexample.ProofCertificate_0720 := by
  constructor
  intro q0 q1 q2 q3 q4 q5
  exact @certificate_proof_0720 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 q0 q1 q2 q3 q4 q5

theorem certificate_proof_0721 :
    uniformMean (formSingularIndicator (K := K) (V := V)) ≤
      (finrank K V : ℝ)/(Fintype.card K : ℝ) := by
  have h := uniformMean_equiv (symFormMatrix K V)
    (fun M : SymMatrix K (finrank K V) => if M.val.det=0 then 1 else 0)
  have he : uniformMean (formSingularIndicator (K := K) (V := V)) =
      symmetricSingularProb (K := K) (finrank K V) := by
    unfold symmetricSingularProb
    rw [←h]; apply uniformMean_congr
    intro Q; exact formSingularIndicator_matrix (Module.finBasis K V) Q
  rw [he]; exact symmetricSingularProb_bound _

private instance certificate_instance_0721 : OAI.SidorenkoCounterexample.ProofCertificate_0721 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7
  exact @certificate_proof_0721 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 q0 q1 q2 q3 q4 q5 q6 q7

theorem certificate_proof_0722 (hK : ringChar K ≠ 2) (hd : 0 < finrank K V)
    {ξ : ℤ} (hξ : ξ=1 ∨ ξ = -1) :
    |uniformMean (formSignIndicator (K := K) (V := V) ξ)-1/2| ≤
      (finrank K V : ℝ)/(Fintype.card K : ℝ) := by
  have h := uniformMean_equiv (symFormMatrix K V)
    (fun M : SymMatrix K (finrank K V) => characterSignIndicator ξ M.val.det)
  have he : uniformMean (formSignIndicator (K := K) (V := V) ξ) =
      symmetricSignProb (K := K) (finrank K V) ξ := by
    unfold symmetricSignProb
    rw [←h]; apply uniformMean_congr
    intro Q; exact formSignIndicator_matrix (Module.finBasis K V) hξ Q
  rw [he]; exact symmetricSignProb_error _ hd hK hξ

private instance certificate_instance_0722 : OAI.SidorenkoCounterexample.ProofCertificate_0722 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11
  exact @certificate_proof_0722 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11

variable {W : Type} [AddCommGroup W] [Module K W] [FiniteDimensional K W]
omit [DecidableEq K] in
theorem certificate_proof_0723 (f : W →ₗ[K] V) (hf : Function.Injective f)
    (g : SymForm K W → ℝ) :
    uniformMean (fun Q : SymForm K V => g (symFormPull f Q)) = uniformMean g :=
  uniformMean_surjective_linear (symFormPull f) (symFormPull_surjective f hf) g

private instance certificate_instance_0723 : OAI.SidorenkoCounterexample.ProofCertificate_0723 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13
  exact @certificate_proof_0723 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13

end Forms
end SidorenkoCounterexample
end
end OAI
namespace OAI
section
namespace SidorenkoCounterexample
open Module LinearMap
section Projections
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
theorem certificate_proof_0724 (Q : LinearMap.BilinForm K V) (hQ : Q.Nondegenerate)
    (T : V →ₗ[K] V) (hT : FormSelfAdjoint Q T) :
    T.ker = Q.orthogonal T.range := by
  ext x
  constructor
  · intro hx y hy
    obtain ⟨z,rfl⟩ := hy
    rw [hT,show T x=0 from hx,map_zero]
  · intro hx
    apply hQ.2
    intro y
    rw [←hT]
    exact hx (T y) ⟨y,rfl⟩

private instance certificate_instance_0724 : OAI.SidorenkoCounterexample.ProofCertificate_0724 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8
  exact @certificate_proof_0724 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 q0 q1 q2 q3 q4 q5 q6 q7 q8

variable [FiniteDimensional K V]
theorem certificate_proof_0725 (Q : LinearMap.BilinForm K V)
    (hs : Q.IsSymm) (hQ : Q.Nondegenerate) (T : V →ₗ[K] V)
    (hT : FormSelfAdjoint Q T) (hi : IsIdempotentElem T) :
    (Q.restrict T.range).Nondegenerate := by
  apply (Q.restrict_nondegenerate_iff_isCompl_orthogonal hs.isRefl).mpr
  rw [←selfAdjoint_projection_ker Q hQ T hT]
  exact hi.isCompl

private instance certificate_instance_0725 : OAI.SidorenkoCounterexample.ProofCertificate_0725 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11
  exact @certificate_proof_0725 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11

theorem certificate_proof_0726 (Q : LinearMap.BilinForm K V) (hs : Q.IsSymm)
    (U : Submodule K V) (hU : (Q.restrict U).Nondegenerate) :
    IsIdempotentElem (formProjection Q hs U hU) := Submodule.isIdempotentElem_projection _

private instance certificate_instance_0726 : OAI.SidorenkoCounterexample.ProofCertificate_0726 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9
  exact @certificate_proof_0726 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9

theorem certificate_proof_0727 (Q : LinearMap.BilinForm K V) (hs : Q.IsSymm)
    (U : Submodule K V) (hU : (Q.restrict U).Nondegenerate) :
    (formProjection Q hs U hU).range=U := Submodule.range_projection _

private instance certificate_instance_0727 : OAI.SidorenkoCounterexample.ProofCertificate_0727 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9
  exact @certificate_proof_0727 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9

theorem certificate_proof_0728 (Q : LinearMap.BilinForm K V) (hs : Q.IsSymm)
    (U : Submodule K V) (hU : (Q.restrict U).Nondegenerate) :
    FormSelfAdjoint Q (formProjection Q hs U hU) := by
  intro x y
  let h := Q.isCompl_orthogonal_of_restrict_nondegenerate hs.isRefl hU
  let p := U.projection (Q.orthogonal U) h
  have hx : x-p x ∈ Q.orthogonal U := Submodule.sub_projection_mem h x
  have hy : y-p y ∈ Q.orthogonal U := Submodule.sub_projection_mem h y
  have hpx : p x ∈ U := Submodule.projection_apply_mem h x
  have hpy : p y ∈ U := Submodule.projection_apply_mem h y
  have h1 := hy (p x) hpx
  have h2 := hx (p y) hpy
  simp only [map_sub] at h1 h2
  change Q (p x) y=Q x (p y)
  calc
    _ = Q (p x) (p y) := sub_eq_zero.mp h1
    _ = Q (p y) (p x) := hs.eq _ _
    _ = Q (p y) x := (sub_eq_zero.mp h2).symm
    _ = _ := hs.eq _ _

private instance certificate_instance_0728 : OAI.SidorenkoCounterexample.ProofCertificate_0728 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9
  exact @certificate_proof_0728 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9

end Projections
end SidorenkoCounterexample
end
section
namespace SidorenkoCounterexample
open Module LinearMap
open scoped Matrix
section MatrixProjection
variable {K n : Type} [Field K] [Fintype n] [DecidableEq n]
theorem certificate_proof_0729 (Q : Matrix n n K) (T : (n → K) →ₗ[K] (n → K)) :
    FormSelfAdjoint Q.toBilin' T ↔ T.toMatrix'ᵀ*Q=Q*T.toMatrix' := by
  change (∀ x y, Q.toBilin'.compLeft T x y = Q.toBilin'.compRight T x y) ↔ _
  rw [←LinearMap.BilinForm.ext_iff]
  rw [←LinearMap.BilinForm.toMatrix'.injective.eq_iff]
  simp only [LinearMap.BilinForm.toMatrix'_compLeft,LinearMap.BilinForm.toMatrix'_compRight,
    LinearMap.BilinForm.toMatrix'_toBilin']

private instance certificate_instance_0729 : OAI.SidorenkoCounterexample.ProofCertificate_0729 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6
  exact @certificate_proof_0729 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 q0 q1 q2 q3 q4 q5 q6

theorem certificate_proof_0730 (Q A : Matrix n n K) (hQ : Q.IsSymm) (hA : A.IsSymm) :
    FormSelfAdjoint Q.toBilin' (A*Q).toLin' := by
  rw [matrix_formSelfAdjoint_iff,LinearMap.toMatrix'_toLin',Matrix.transpose_mul,hQ,hA,
    Matrix.mul_assoc]

private instance certificate_instance_0730 : OAI.SidorenkoCounterexample.ProofCertificate_0730 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8
  exact @certificate_proof_0730 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 q0 q1 q2 q3 q4 q5 q6 q7 q8

theorem certificate_proof_0731 (Q A : Matrix n n K) (hA : A*Q*A=A) :
    IsIdempotentElem (A*Q).toLin' := by
  change (A*Q).toLin'.comp (A*Q).toLin' = (A*Q).toLin'
  rw [←Matrix.toLin'_mul]
  congr 1
  rw [←Matrix.mul_assoc,hA]

private instance certificate_instance_0731 : OAI.SidorenkoCounterexample.ProofCertificate_0731 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7
  exact @certificate_proof_0731 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 q0 q1 q2 q3 q4 q5 q6 q7

end MatrixProjection
end SidorenkoCounterexample
end
section
namespace SidorenkoCounterexample
open Module LinearMap
open scoped Matrix
section Range
variable {K n : Type} [Field K] [Fintype n] [DecidableEq n]
variable [Fintype K] [DecidableEq K]
end Range
end SidorenkoCounterexample
end
section
namespace SidorenkoCounterexample
open Module LinearMap
open scoped Matrix
section FormSum
variable {K V : Type} [Field K] [Fintype K] [DecidableEq K]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]
end FormSum
section Complement
variable {K n : Type} [Field K] [Fintype n] [DecidableEq n]
end Complement
section Signs
variable {K n : Type} [Field K] [Fintype K] [DecidableEq K] [Fintype n] [DecidableEq n]
end Signs
end SidorenkoCounterexample
end
section
namespace SidorenkoCounterexample
open Module
open scoped BigOperators
section Split
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
end Split
section Signs
variable {K V : Type} [Field K] [Fintype K] [DecidableEq K]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]
end Signs
end SidorenkoCounterexample
end
end OAI

theorem solution : OAI.SidorenkoCounterexample.ProofCertificate_0695 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0696 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0697 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0698 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0699 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0700 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0701 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0702 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0703 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0704 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0705 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0706 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0707 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0708 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0709 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0710 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0711 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0712 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0713 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0714 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0715 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0716 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0717 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0718 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0719 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0720 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0721 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0722 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0723 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0724 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0725 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0726 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0727 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0728 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0729 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0730 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0731 := by
  exact ⟨inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance⟩
end

