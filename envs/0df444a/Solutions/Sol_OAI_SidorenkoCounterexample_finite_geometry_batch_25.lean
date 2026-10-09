-- Prove2me | solution 1 for OAI.SidorenkoCounterexample.finite_geometry_batch_25
-- status  : ACCEPTED   (prove)
-- author  : @abcdefg
-- created : 2026-10-09T06:29:06.699806+00:00
-- url     : https://prove2.me/submissions/3c93bbe9-744b-4049-b3b1-8f3b3c7ee536

import Definitions.Def_SidorenkoCertificateBundleB
set_option linter.unusedVariables false
section
variable [p0 : OAI.SidorenkoCounterexample.ProofCertificate_0628]
  [p1 : OAI.SidorenkoCounterexample.ProofCertificate_0632]
  [p2 : OAI.SidorenkoCounterexample.ProofCertificate_0652]
  [p3 : OAI.SidorenkoCounterexample.ProofCertificate_0653]
  [p4 : OAI.SidorenkoCounterexample.ProofCertificate_0654]
  [p5 : OAI.SidorenkoCounterexample.ProofCertificate_0656]
  [p6 : OAI.SidorenkoCounterexample.ProofCertificate_0657]
  [p7 : OAI.SidorenkoCounterexample.ProofCertificate_0658]
  [p8 : OAI.SidorenkoCounterexample.ProofCertificate_0659]
  [p9 : OAI.SidorenkoCounterexample.ProofCertificate_0660]
  [p10 : OAI.SidorenkoCounterexample.ProofCertificate_0661]
  [p11 : OAI.SidorenkoCounterexample.ProofCertificate_0662]
  [p12 : OAI.SidorenkoCounterexample.ProofCertificate_0663]
  [p13 : OAI.SidorenkoCounterexample.ProofCertificate_0671]
  [p14 : OAI.SidorenkoCounterexample.ProofCertificate_0672]
  [p15 : OAI.SidorenkoCounterexample.ProofCertificate_0683]
  [p16 : OAI.SidorenkoCounterexample.ProofCertificate_0684]
  [p17 : OAI.SidorenkoCounterexample.ProofCertificate_0685]
  [p18 : OAI.SidorenkoCounterexample.ProofCertificate_0686]
  [p19 : OAI.SidorenkoCounterexample.ProofCertificate_0707]
  [p20 : OAI.SidorenkoCounterexample.ProofCertificate_0708]
  [p21 : OAI.SidorenkoCounterexample.ProofCertificate_0716]
  [p22 : OAI.SidorenkoCounterexample.ProofCertificate_0718]
  [p23 : OAI.SidorenkoCounterexample.ProofCertificate_0719]
  [p24 : OAI.SidorenkoCounterexample.ProofCertificate_0721]
  [p25 : OAI.SidorenkoCounterexample.ProofCertificate_0723]
  [p26 : OAI.SidorenkoCounterexample.ProofCertificate_0724]
  [p27 : OAI.SidorenkoCounterexample.ProofCertificate_0725]
  [p28 : OAI.SidorenkoCounterexample.ProofCertificate_0726]
  [p29 : OAI.SidorenkoCounterexample.ProofCertificate_0727]
  [p30 : OAI.SidorenkoCounterexample.ProofCertificate_0728]
  [p31 : OAI.SidorenkoCounterexample.ProofCertificate_0729]
  [p32 : OAI.SidorenkoCounterexample.ProofCertificate_0730]
  [p33 : OAI.SidorenkoCounterexample.ProofCertificate_0731]
include p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33

namespace OAI
section
namespace SidorenkoCounterexample
open Module LinearMap
section Projections
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
variable [FiniteDimensional K V]
end Projections
end SidorenkoCounterexample
end
section
namespace SidorenkoCounterexample
open Module LinearMap
open scoped Matrix
section MatrixProjection
variable {K n : Type} [Field K] [Fintype n] [DecidableEq n]
theorem certificate_proof_0732 (Q : Matrix n n K) (hQ : Q.IsSymm)
    (hdet : Q.det≠0) (T : SelfAdjointIdempotent Q.toBilin') :
    (T.val.toMatrix'*Q⁻¹).IsSymm := by
  have h := (matrix_formSelfAdjoint_iff Q T.val).mp T.property.2
  have hu : IsUnit Q.det := isUnit_iff_ne_zero.mpr hdet
  change (T.val.toMatrix'*Q⁻¹)ᵀ=T.val.toMatrix'*Q⁻¹
  rw [Matrix.transpose_mul,hQ.inv]
  calc
    Q⁻¹*T.val.toMatrix'ᵀ = Q⁻¹*(T.val.toMatrix'ᵀ*Q)*Q⁻¹ := by
      simp only [Matrix.mul_assoc,Matrix.mul_nonsing_inv Q hu,Matrix.mul_one]
    _ = Q⁻¹*(Q*T.val.toMatrix')*Q⁻¹ := by rw [h]
    _ = _ := by rw [←Matrix.mul_assoc Q⁻¹ Q,Matrix.nonsing_inv_mul Q hu,Matrix.one_mul]

private instance certificate_instance_0732 : OAI.SidorenkoCounterexample.ProofCertificate_0732 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8
  exact @certificate_proof_0732 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 q0 q1 q2 q3 q4 q5 q6 q7 q8

theorem certificate_proof_0733 (Q : Matrix n n K) (hdet : Q.det≠0)
    (T : SelfAdjointIdempotent Q.toBilin') :
    (T.val.toMatrix'*Q⁻¹)*Q*(T.val.toMatrix'*Q⁻¹)=T.val.toMatrix'*Q⁻¹ := by
  have hi : T.val.toMatrix'*T.val.toMatrix'=T.val.toMatrix' := by
    rw [←LinearMap.toMatrix'_comp]
    exact congrArg LinearMap.toMatrix' T.property.1
  have hu : IsUnit Q.det := isUnit_iff_ne_zero.mpr hdet
  rw [Matrix.mul_assoc _ Q⁻¹ Q,Matrix.nonsing_inv_mul Q hu,Matrix.mul_one,
    ←Matrix.mul_assoc,hi]

private instance certificate_instance_0733 : OAI.SidorenkoCounterexample.ProofCertificate_0733 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7
  exact @certificate_proof_0733 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 q0 q1 q2 q3 q4 q5 q6 q7

end MatrixProjection
end SidorenkoCounterexample
end
section
namespace SidorenkoCounterexample
open Module LinearMap
open scoped Matrix
section Range
variable {K n : Type} [Field K] [Fintype n] [DecidableEq n]
theorem certificate_proof_0734 (Q : Matrix n n K) (hQ : Q.det≠0) :
    Function.Surjective Q.toLin' := by
  intro x
  refine ⟨Q⁻¹.toLin' x,?_⟩
  change (Q.toLin'.comp Q⁻¹.toLin') x=x
  rw [←Matrix.toLin'_mul,Matrix.mul_nonsing_inv Q (isUnit_iff_ne_zero.mpr hQ),Matrix.toLin'_one]
  rfl

private instance certificate_instance_0734 : OAI.SidorenkoCounterexample.ProofCertificate_0734 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6
  exact @certificate_proof_0734 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 q0 q1 q2 q3 q4 q5 q6

theorem certificate_proof_0735 (A Q : Matrix n n K) (hQ : Q.det≠0) :
    (A*Q).toLin'.range=A.toLin'.range := by
  rw [Matrix.toLin'_mul,LinearMap.range_comp_of_range_eq_top _
    (LinearMap.range_eq_top.mpr (matrix_toLin_surjective Q hQ))]

private instance certificate_instance_0735 : OAI.SidorenkoCounterexample.ProofCertificate_0735 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7
  exact @certificate_proof_0735 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 q0 q1 q2 q3 q4 q5 q6 q7

theorem certificate_proof_0736 (Q : Matrix n n K) (hQ : Q.IsSymm) (hdet : Q.det≠0)
    (A : CenterProjection Q) : (centerSubspaceEquiv Q hQ hdet A).val=A.val.toLin'.range :=
  matrix_mul_range A.val Q hdet

private instance certificate_instance_0736 : OAI.SidorenkoCounterexample.ProofCertificate_0736 := by
  constructor
  intro c0 c1 c2 c3 c4 c5 c6 c7 c8 q0 q1 q2 q3 q4 q5 q6 q7 q8
  exact @certificate_proof_0736 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 q0 q1 q2 q3 q4 q5 q6 q7 q8

theorem certificate_proof_0737 (Q A : Matrix n n K) (hQ : Q.IsSymm)
    (hdet : Q.det≠0) (hA : A.IsSymm) (hi : A*Q*A=A) :
    (Q.toBilin'.restrict A.toLin'.range).Nondegenerate := by
  have h := (centerSubspaceEquiv Q hQ hdet ⟨A,hA,hi⟩).property
  rw [centerSubspaceEquiv_val Q hQ hdet ⟨A,hA,hi⟩] at h
  exact h

private instance certificate_instance_0737 : OAI.SidorenkoCounterexample.ProofCertificate_0737 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10
  exact @certificate_proof_0737 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10

theorem certificate_proof_0738 (Q A : Matrix n n K) (hA : A.IsSymm) (hi : A*Q*A=A) :
    (Q.toBilin'.restrict A.toLin'.range).compl₁₂ A.toLin'.rangeRestrict A.toLin'.rangeRestrict =
      A.toBilin' := by
  change Q.toBilin'.comp A.toLin' A.toLin' = _
  rw [Matrix.toBilin'_comp,hA,hi]

private instance certificate_instance_0738 : OAI.SidorenkoCounterexample.ProofCertificate_0738 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8
  exact @certificate_proof_0738 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 q0 q1 q2 q3 q4 q5 q6 q7 q8

theorem certificate_proof_0739 (Q R A : Matrix n n K) (hA : A.IsSymm) (hi : A*Q*A=A) :
    A*R*A=A ↔ ((Q-R).toBilin'.restrict A.toLin'.range)=0 := by
  have hp : (Q-R).toBilin'.comp A.toLin' A.toLin' = (A-A*R*A).toBilin' := by
    rw [Matrix.toBilin'_comp,hA,mul_sub,sub_mul,hi]
  constructor
  · intro h
    rw [h,sub_self,map_zero] at hp
    apply LinearMap.ext
    intro x
    apply LinearMap.ext
    intro y
    obtain ⟨x0,hx⟩ := x.property
    obtain ⟨y0,hy⟩ := y.property
    change (Q-R).toBilin' x.val y.val=0
    rw [←hx,←hy]
    exact congrArg (fun B : LinearMap.BilinForm K (n → K) => B x0 y0) hp
  · intro h
    have hz : (Q-R).toBilin'.comp A.toLin' A.toLin'=0 := by
      apply LinearMap.ext
      intro x
      apply LinearMap.ext
      intro y
      exact congrArg (fun B : LinearMap.BilinForm K A.toLin'.range =>
        B (A.toLin'.rangeRestrict x) (A.toLin'.rangeRestrict y)) h
    rw [hz] at hp
    have he := Matrix.toBilin'.injective (hp.symm.trans (map_zero Matrix.toBilin').symm)
    exact (sub_eq_zero.mp he).symm

private instance certificate_instance_0739 : OAI.SidorenkoCounterexample.ProofCertificate_0739 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9
  exact @certificate_proof_0739 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9

variable [Fintype K] [DecidableEq K]
theorem certificate_proof_0740 (Q A : Matrix n n K) (hQ : Q.IsSymm) (hdet : Q.det≠0)
    (hA : A.IsSymm) (hi : A*Q*A=A) :
    discriminantSign A.toBilin' (Matrix.isSymm_toBilin'_iff_isSymm.mpr hA) =
      discriminantSign (Q.toBilin'.restrict A.toLin'.range)
        ((Matrix.isSymm_toBilin'_iff_isSymm.mpr hQ).restrict _) := by
  let f := A.toLin'.rangeRestrict
  let B := Q.toBilin'.restrict A.toLin'.range
  have hs : B.IsSymm := (Matrix.isSymm_toBilin'_iff_isSymm.mpr hQ).restrict _
  have hb : B.Nondegenerate := center_restriction_nondegenerate Q A hQ hdet hA hi
  have h := discriminantSign_pullback B hs hb f A.toLin'.surjective_rangeRestrict
    (Module.finBasis K A.toLin'.range)
  rw [discriminantSign_nondegenerate B hs hb (Module.finBasis K A.toLin'.range)]
  rw [←h]
  congr 1
  exact (center_form_pullback Q A hA hi).symm

private instance certificate_instance_0740 : OAI.SidorenkoCounterexample.ProofCertificate_0740 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12
  exact @certificate_proof_0740 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12

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
theorem certificate_proof_0741 (Q : LinearMap.BilinForm K V) (hs : Q.IsSymm)
    (hQ : Q.Nondegenerate) (U W : Submodule K V) (hc : IsCompl U W)
    (hU : (Q.restrict U).Nondegenerate) (hW : (Q.restrict W).Nondegenerate)
    (ho : ∀ u : U, ∀ w : W, Q u.val w.val=0) :
    discriminantSign Q hs = discriminantSign (Q.restrict U) (hs.restrict U) *
      discriminantSign (Q.restrict W) (hs.restrict W) := by
  have he := discriminantSign_isometry
    (orthogonalSumForm (Q.restrict U) (Q.restrict W)) Q
    (orthogonalSumForm_isSymm _ _ (hs.restrict U) (hs.restrict W)) hs
    (orthogonalSumForm_nondegenerate _ _ hU hW) hQ (U.prodEquivOfIsCompl W hc)
    (fun x y => by
      simp only [Submodule.coe_prodEquivOfIsCompl',map_add,LinearMap.add_apply,
        orthogonalSumForm_apply,LinearMap.BilinForm.restrict_apply,LinearMap.domRestrict_apply]
      rw [ho x.1 y.2,hs.eq x.2.val y.1.val,ho y.1 x.2]
      ring)
  rw [discriminantSign_orthogonalSum _ _ _ _ hU hW] at he
  exact he.symm

private instance certificate_instance_0741 : OAI.SidorenkoCounterexample.ProofCertificate_0741 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16
  exact @certificate_proof_0741 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16

end FormSum
section Complement
variable {K n : Type} [Field K] [Fintype n] [DecidableEq n]
theorem certificate_proof_0742 (B A : Matrix n n K) (hB : B.det≠0)
    (hi : A*B⁻¹*A=A) : (B-A)*B⁻¹*(B-A)=B-A := by
  have hu : IsUnit B.det := isUnit_iff_ne_zero.mpr hB
  rw [sub_mul,Matrix.mul_nonsing_inv B hu,sub_mul,one_mul,mul_sub,hi,
    Matrix.mul_assoc A B⁻¹ B,Matrix.nonsing_inv_mul B hu,Matrix.mul_one]
  abel

private instance certificate_instance_0742 : OAI.SidorenkoCounterexample.ProofCertificate_0742 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8
  exact @certificate_proof_0742 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 q0 q1 q2 q3 q4 q5 q6 q7 q8

theorem certificate_proof_0743 (B A : Matrix n n K) (hB : B.det≠0)
    (hi : A*B⁻¹*A=A) : IsCompl A.toLin'.range (B-A).toLin'.range := by
  let T := (A*B⁻¹).toLin'
  have ht := matrix_projection_idempotent B⁻¹ A hi
  have hiB : B⁻¹.det≠0 := by simpa only [Matrix.det_nonsing_inv, Ring.inverse_eq_inv] using inv_ne_zero hB
  have hr := matrix_mul_range A B⁻¹ hiB
  have hc : (B-A).toLin'.range = T.ker := by
    rw [ht.ker_eq_range,←matrix_mul_range (B-A) B⁻¹ hiB]
    congr 1
    change ((B-A)*B⁻¹).toLin' = LinearMap.id-(A*B⁻¹).toLin'
    rw [sub_mul,Matrix.mul_nonsing_inv B (isUnit_iff_ne_zero.mpr hB),map_sub,Matrix.toLin'_one]
  rw [hc]
  simpa only [T,hr] using (matrix_projection_idempotent B⁻¹ A hi).isCompl

private instance certificate_instance_0743 : OAI.SidorenkoCounterexample.ProofCertificate_0743 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8
  exact @certificate_proof_0743 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 q0 q1 q2 q3 q4 q5 q6 q7 q8

theorem certificate_proof_0744 (B A : Matrix n n K) (hB : B.det≠0)
    (hA : A.IsSymm) (hi : A*B⁻¹*A=A) :
    ∀ u : A.toLin'.range, ∀ w : (B-A).toLin'.range, B⁻¹.toBilin' u.val w.val=0 := by
  have hp : B⁻¹.toBilin'.comp A.toLin' (B-A).toLin'=0 := by
    rw [Matrix.toBilin'_comp,hA,mul_sub,hi,
      Matrix.mul_assoc A B⁻¹ B,Matrix.nonsing_inv_mul B (isUnit_iff_ne_zero.mpr hB),
      Matrix.mul_one,sub_self,map_zero]
  intro u w
  obtain ⟨x,hx⟩ := u.property
  obtain ⟨y,hy⟩ := w.property
  rw [←hx,←hy]
  exact congrArg (fun Q : LinearMap.BilinForm K (n → K) => Q x y) hp

private instance certificate_instance_0744 : OAI.SidorenkoCounterexample.ProofCertificate_0744 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11
  exact @certificate_proof_0744 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11

end Complement
section Signs
variable {K n : Type} [Field K] [Fintype K] [DecidableEq K] [Fintype n] [DecidableEq n]
theorem certificate_proof_0745 {a : K} (ha : a≠0) : quadraticChar K a⁻¹=quadraticChar K a := by
  have hm : quadraticChar K a * quadraticChar K a⁻¹=1 := by
    rw [←map_mul,mul_inv_cancel₀ ha,map_one]
  rcases quadraticChar_dichotomy ha with h | h <;> rw [h] at hm ⊢ <;> linarith

private instance certificate_instance_0745 : OAI.SidorenkoCounterexample.ProofCertificate_0745 := by
  constructor
  intro q0 q1 q2 q3 q4 q5
  exact @certificate_proof_0745 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 q0 q1 q2 q3 q4 q5

theorem certificate_proof_0746 (B A : Matrix n n K) (hs : B.IsSymm) (hB : B.det≠0)
    (hA : A.IsSymm) (hi : A*B⁻¹*A=A) :
    quadraticChar K B.det =
      discriminantSign A.toBilin' (Matrix.isSymm_toBilin'_iff_isSymm.mpr hA) *
        discriminantSign (B-A).toBilin' (Matrix.isSymm_toBilin'_iff_isSymm.mpr (hs.sub hA)) := by
  have hsQ : B⁻¹.IsSymm := hs.inv
  have hnQ : B⁻¹.det≠0 := by simpa only [Matrix.det_nonsing_inv, Ring.inverse_eq_inv] using inv_ne_zero hB
  have hiC := center_complement_equation B A hB hi
  rw [center_discriminant B⁻¹ A hsQ hnQ hA hi,
    center_discriminant B⁻¹ (B-A) hsQ hnQ (hs.sub hA) hiC]
  rw [←discriminantSign_complements B⁻¹.toBilin'
    (Matrix.isSymm_toBilin'_iff_isSymm.mpr hsQ)
    (Matrix.nondegenerate_toBilin'_iff.mpr (Matrix.nondegenerate_iff_det_ne_zero.mpr hnQ))
    A.toLin'.range (B-A).toLin'.range (center_complement_ranges B A hB hi)
    (center_restriction_nondegenerate B⁻¹ A hsQ hnQ hA hi)
    (center_restriction_nondegenerate B⁻¹ (B-A) hsQ hnQ (hs.sub hA) hiC)
    (center_complement_orthogonal B A hB hA hi)]
  rw [discriminantSign_nondegenerate _ _
    (Matrix.nondegenerate_toBilin'_iff.mpr (Matrix.nondegenerate_iff_det_ne_zero.mpr hnQ))
    (Pi.basisFun K n)]
  change quadraticChar K B.det = quadraticChar K (B⁻¹.toBilin'.toMatrix').det
  rw [LinearMap.BilinForm.toMatrix'_toBilin',Matrix.det_nonsing_inv,Ring.inverse_eq_inv,quadraticChar_inverse hB]

private instance certificate_instance_0746 : OAI.SidorenkoCounterexample.ProofCertificate_0746 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12
  exact @certificate_proof_0746 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12

end Signs
end SidorenkoCounterexample
end
section
namespace SidorenkoCounterexample
open Module
open scoped BigOperators
section Split
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
theorem certificate_proof_0747 (φ : V →ₗ[K] K) (x : V) (hx : φ x=1)
    (p : φ.ker × K) : dualKerEquiv φ x hx p = p.1.val + p.2 • x := rfl

private instance certificate_instance_0747 : OAI.SidorenkoCounterexample.ProofCertificate_0747 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8
  exact @certificate_proof_0747 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 q0 q1 q2 q3 q4 q5 q6 q7 q8

theorem certificate_proof_0748 (φ : V →ₗ[K] K) (x y : V) :
    (rankOneForm φ).val x y = φ x * φ y := rfl

private instance certificate_instance_0748 : OAI.SidorenkoCounterexample.ProofCertificate_0748 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7
  exact @certificate_proof_0748 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 q0 q1 q2 q3 q4 q5 q6 q7

theorem certificate_proof_0749 [FiniteDimensional K V] (φ : V →ₗ[K] K) (x : V) (hx : φ x=1) :
    finrank K φ.ker+1=finrank K V := by
  have h := (dualKerEquiv φ x hx).finrank_eq
  simpa only [Module.finrank_prod,Module.finrank_self] using h

private instance certificate_instance_0749 : OAI.SidorenkoCounterexample.ProofCertificate_0749 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8
  exact @certificate_proof_0749 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 q0 q1 q2 q3 q4 q5 q6 q7 q8

end Split
section Signs
variable {K V : Type} [Field K] [Fintype K] [DecidableEq K]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]
omit [Fintype K] [DecidableEq K] [FiniteDimensional K V] in
theorem certificate_proof_0750 (φ : V →ₗ[K] K) (x : V) (hx : φ x=1)
    {ι : Type} (b : Basis ι K φ.ker) (i : ι) : dualKerBasis φ x hx b (.inl i) = (b i).val := by
  simp [dualKerBasis,Basis.prod_apply]

private instance certificate_instance_0750 : OAI.SidorenkoCounterexample.ProofCertificate_0750 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10
  exact @certificate_proof_0750 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10

omit [Fintype K] [DecidableEq K] [FiniteDimensional K V] in
theorem certificate_proof_0751 (φ : V →ₗ[K] K) (x : V) (hx : φ x=1)
    {ι : Type} (b : Basis ι K φ.ker) (i : PUnit.{1}) : dualKerBasis φ x hx b (.inr i) = x := by
  simp [dualKerBasis,Basis.prod_apply]

private instance certificate_instance_0751 : OAI.SidorenkoCounterexample.ProofCertificate_0751 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10
  exact @certificate_proof_0751 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10

omit [Fintype K] [DecidableEq K] in
theorem certificate_proof_0752 (φ : V →ₗ[K] K) (x : V) (hx : φ x=1)
    (Q : SymForm K V) (a : K) :
    (Q+a • rankOneForm φ).val.toMatrix (dualKerBasis φ x hx (Module.finBasis K φ.ker)) =
      borderRaw ((symFormPull φ.ker.subtype Q).val.toMatrix (Module.finBasis K φ.ker))
        (fun i => Q.val (Module.finBasis K φ.ker i).val x) (Q.val x x+a) := by
  ext i j
  cases i with
  | inl i => cases j with
    | inl j =>
      simp only [LinearMap.BilinForm.toMatrix_apply,dualKerBasis_inl,borderRaw,
        Matrix.fromBlocks_apply₁₁]
      change Q.val _ _ + a * (φ (Module.finBasis K φ.ker i).val * φ (Module.finBasis K φ.ker j).val) = _
      rw [show φ (Module.finBasis K φ.ker i).val=0 from (Module.finBasis K φ.ker i).property]
      simp only [zero_mul,mul_zero,add_zero]; rfl
    | inr j =>
      simp only [LinearMap.BilinForm.toMatrix_apply,dualKerBasis_inl,dualKerBasis_inr,borderRaw,
        Matrix.fromBlocks_apply₁₂,Matrix.of_apply]
      change Q.val _ x+a*(φ (Module.finBasis K φ.ker i).val * φ x) = _
      rw [show φ (Module.finBasis K φ.ker i).val=0 from (Module.finBasis K φ.ker i).property]
      simp
  | inr i => cases j with
    | inl j =>
      simp only [LinearMap.BilinForm.toMatrix_apply,dualKerBasis_inl,dualKerBasis_inr,borderRaw,
        Matrix.fromBlocks_apply₂₁,Matrix.of_apply]
      change Q.val x _+a*(φ x * φ (Module.finBasis K φ.ker j).val) = _
      rw [show φ (Module.finBasis K φ.ker j).val=0 from (Module.finBasis K φ.ker j).property]
      simpa using Q.property.eq x (Module.finBasis K φ.ker j).val
    | inr j =>
      simp only [LinearMap.BilinForm.toMatrix_apply,dualKerBasis_inr,borderRaw,
        Matrix.fromBlocks_apply₂₂,Matrix.of_apply]
      change Q.val x x+a*(φ x * φ x) = Q.val x x+a
      rw [hx,one_mul,mul_one]

private instance certificate_instance_0752 : OAI.SidorenkoCounterexample.ProofCertificate_0752 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10
  exact @certificate_proof_0752 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10

theorem certificate_proof_0753 (φ : V →ₗ[K] K) (x : V) (hx : φ x=1)
    (Q : SymForm K V) (hQ : (symFormPull φ.ker.subtype Q).val.Nondegenerate)
    (hK : ringChar K ≠ 2) {ξ : ℤ} (hξ : ξ=1 ∨ ξ = -1) :
    uniformMean (fun a : K => formSignIndicator ξ (Q+a • rankOneForm φ)) =
      (1-1/(Fintype.card K : ℝ))/2 := by
  let b := Module.finBasis K φ.ker
  let M : SymMatrix K (finrank K φ.ker) := ⟨(symFormPull φ.ker.subtype Q).val.toMatrix b,
    ((symFormPull φ.ker.subtype Q).val.isSymm_toMatrix_iff_isSymm b).mpr
      (symFormPull φ.ker.subtype Q).property⟩
  let z : Fin (finrank K φ.ker) → K := fun i => Q.val (b i).val x
  have hM : M.val.det ≠ 0 := (LinearMap.BilinForm.nondegenerate_iff_det_ne_zero b).mp hQ
  have he (a : K) : formSignIndicator ξ (Q+a • rankOneForm φ) =
      characterSignIndicator ξ (M.val.det * (a- (z ⬝ᵥ (M.val⁻¹.mulVec z)-Q.val x x))) := by
    rw [formSignIndicator_matrix (dualKerBasis φ x hx b) hξ,rankOne_shift_matrix]
    have hd : (borderRaw M.val z (Q.val x x+a)).det =
        (symmetricBorder M z (Q.val x x+a)).val.det := by
      symm; exact Matrix.det_submatrix_equiv_self _ _
    rw [show (symFormPull φ.ker.subtype Q).val.toMatrix (Module.finBasis K φ.ker)=M.val from rfl,
      show (fun i => Q.val (Module.finBasis K φ.ker i).val x)=z from rfl,hd,
      symmetricBorder_det M z _ hM]
    congr 2; ring
  rw [uniformMean_congr he,uniformMean_affine _ _ hM,uniformMean_characterSignIndicator hK hξ]

private instance certificate_instance_0753 : OAI.SidorenkoCounterexample.ProofCertificate_0753 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15
  exact @certificate_proof_0753 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15

end Signs
end SidorenkoCounterexample
end
end OAI
namespace OAI
section
namespace SidorenkoCounterexample
open Module
open scoped BigOperators
section Means
variable {A B : Type} [Fintype A] [Fintype B]
theorem certificate_proof_0754 (f : A → B → ℝ) :
    uniformMean (fun a => uniformMean (f a)) =
      uniformMean (fun b => uniformMean fun a => f a b) := by
  unfold uniformMean
  simp only [←Finset.sum_div]
  rw [Finset.sum_comm]
  ring

private instance certificate_instance_0754 : OAI.SidorenkoCounterexample.ProofCertificate_0754 := by
  constructor
  intro q0 q1 q2 q3 q4
  exact @certificate_proof_0754 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 q0 q1 q2 q3 q4

variable [AddGroup A]
theorem certificate_proof_0755 (f : A → ℝ) (t : A) :
    uniformMean (fun a => f (a+t)) = uniformMean f := uniformMean_equiv (Equiv.addRight t) f

private instance certificate_instance_0755 : OAI.SidorenkoCounterexample.ProofCertificate_0755 := by
  constructor
  intro q0 q1 q2 q3 q4
  exact @certificate_proof_0755 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 q0 q1 q2 q3 q4

theorem certificate_proof_0756 [Nonempty B] (f : A → ℝ) (t : B → A) :
    uniformMean (fun a => uniformMean fun b => f (a+t b)) = uniformMean f := by
  rw [uniformMean_swap]
  simp_rw [uniformMean_translate,uniformMean_const]

private instance certificate_instance_0756 : OAI.SidorenkoCounterexample.ProofCertificate_0756 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7
  exact @certificate_proof_0756 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 q0 q1 q2 q3 q4 q5 q6 q7

end Means
section ShiftError
variable {K U : Type} [Field K] [Fintype K] [DecidableEq K]
  [AddCommGroup U] [Module K U] [FiniteDimensional K U]
theorem certificate_proof_0757 (φ : U →ₗ[K] K) (x : U) (hx : φ x=1)
    (Q : SymForm K U) (hK : ringChar K ≠ 2) {ξ : ℤ} (hξ : ξ=1 ∨ ξ= -1) :
    |uniformMean (fun a : K => formSignIndicator ξ (Q+a • rankOneForm φ))-1/2| ≤
      formSingularIndicator (symFormPull φ.ker.subtype Q)+1/(Fintype.card K : ℝ) := by
  have hq : 0 < (Fintype.card K : ℝ) := Nat.cast_pos.mpr Fintype.card_pos
  by_cases hQ : (symFormPull φ.ker.subtype Q).val.Nondegenerate
  · rw [rankOne_shift_mean φ x hx Q hQ hK hξ]
    simp only [formSingularIndicator,hQ,ite_true,zero_add]
    apply abs_le.mpr
    constructor <;> nlinarith [one_div_pos.mpr hq]
  · have h0 := uniformMean_nonneg fun a : K => formSignIndicator_nonneg ξ (Q+a • rankOneForm φ)
    have h1 := uniformMean_bound fun a : K => formSignIndicator_le_one ξ (Q+a • rankOneForm φ)
    simp only [formSingularIndicator,hQ,ite_false]
    apply abs_le.mpr
    constructor <;> linarith [one_div_pos.mpr hq]

private instance certificate_instance_0757 : OAI.SidorenkoCounterexample.ProofCertificate_0757 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14
  exact @certificate_proof_0757 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14

theorem certificate_proof_0758 (ξ : ℤ) (Q : SymForm K U) :
    |formSignIndicator ξ Q-1/2| ≤ 1 := by
  have h0 := formSignIndicator_nonneg ξ Q
  have h1 := formSignIndicator_le_one ξ Q
  exact abs_le.mpr ⟨by linarith,by linarith⟩

private instance certificate_instance_0758 : OAI.SidorenkoCounterexample.ProofCertificate_0758 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9
  exact @certificate_proof_0758 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9

end ShiftError
section Separate
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
theorem certificate_proof_0759 (U W : Submodule K V)
    (hd : finrank K U=finrank K W) (hne : U≠W) :
    ∃ (φ : V →ₗ[K] K) (x : U), φ x.val=1 ∧ φ.comp W.subtype=0 := by
  have hle : ¬ U ≤ W := by
    intro h
    exact hne (Submodule.eq_of_le_of_finrank_eq h hd)
  have hex : ∃ x : V, x ∈ U ∧ x ∉ W := by
    by_contra! hn
    exact hle hn
  obtain ⟨x,hx,hxW⟩ := hex
  obtain ⟨φ,hφ,hW⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hxW inferInstance
  refine ⟨φ,(φ x)⁻¹ • (⟨x,hx⟩ : U),?_,?_⟩
  · simp only [Submodule.coe_smul,map_smul,smul_eq_mul,inv_mul_cancel₀ hφ]
  · ext w
    have hz : φ w.val ∈ W.map φ := Submodule.mem_map_of_mem w.property
    rw [hW] at hz
    exact hz

private instance certificate_instance_0759 : OAI.SidorenkoCounterexample.ProofCertificate_0759 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9
  exact @certificate_proof_0759 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9

end Separate
section Covariance
variable {K V : Type} [Field K] [Fintype K] [DecidableEq K]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]
omit [Fintype K] [DecidableEq K] [FiniteDimensional K V] in
theorem certificate_proof_0760 (φ : V →ₗ[K] K) (U : Submodule K V) :
    symFormPull U.subtype (rankOneForm φ) = rankOneForm (φ.comp U.subtype) := rfl

private instance certificate_instance_0760 : OAI.SidorenkoCounterexample.ProofCertificate_0760 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6
  exact @certificate_proof_0760 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 q0 q1 q2 q3 q4 q5 q6

omit [Fintype K] [DecidableEq K] [FiniteDimensional K V] in
theorem certificate_proof_0761 (φ : V →ₗ[K] K) (W : Submodule K V)
    (h : φ.comp W.subtype=0) : symFormPull W.subtype (rankOneForm φ)=0 := by
  rw [rankOne_restrict,h]
  apply Subtype.ext
  ext x y
  change (0 : K)*0=0
  ring

private instance certificate_instance_0761 : OAI.SidorenkoCounterexample.ProofCertificate_0761 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7
  exact @certificate_proof_0761 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 q0 q1 q2 q3 q4 q5 q6 q7

theorem certificate_proof_0762 (U W : Submodule K V)
    (hd : finrank K U=finrank K W) (hne : U≠W) (hK : ringChar K ≠ 2)
    {ξ ζ : ℤ} (hξ : ξ=1 ∨ ξ= -1) :
    |uniformMean (fun Q : SymForm K V =>
      (formSignIndicator ξ (symFormPull U.subtype Q)-1/2) *
      (formSignIndicator ζ (symFormPull W.subtype Q)-1/2))| ≤
      (finrank K U : ℝ)/(Fintype.card K : ℝ) := by
  obtain ⟨φ,x,hx,hW⟩ := equal_dimension_separating_dual U W hd hne
  let f : SymForm K V → ℝ := fun Q => formSignIndicator ξ (symFormPull U.subtype Q)-1/2
  let g : SymForm K V → ℝ := fun Q => formSignIndicator ζ (symFormPull W.subtype Q)-1/2
  let R := rankOneForm φ
  let φU := φ.comp U.subtype
  have hxU : φU x=1 := hx
  have hg (Q : SymForm K V) (a : K) : g (Q+a • R)=g Q := by
    dsimp [g]
    rw [map_add,map_smul,rankOne_restrict_zero φ W hW,smul_zero,add_zero]
  have he : uniformMean (fun Q => f Q*g Q) =
      uniformMean (fun Q => (uniformMean fun a : K => f (Q+a • R))*g Q) := by
    rw [←uniformMean_average_translate (fun Q => f Q*g Q) (fun a : K => a • R)]
    apply uniformMean_congr
    intro Q
    simp only [hg]
    have h := uniformMean_mul (g Q) (fun a : K => f (Q+a • R))
    simpa only [mul_comm] using h
  have hf (Q : SymForm K V) : |uniformMean fun a : K => f (Q+a • R)| ≤
      formSingularIndicator (symFormPull φU.ker.subtype (symFormPull U.subtype Q))+
        1/(Fintype.card K : ℝ) := by
    dsimp only [f]
    simp only [map_add,map_smul]
    rw [uniformMean_sub,uniformMean_const]
    exact rankOne_shift_error φU x hxU (symFormPull U.subtype Q) hK hξ
  have hgs (Q : SymForm K V) : |g Q| ≤ 1 := centered_formSign_abs ζ _
  change |uniformMean (fun Q => f Q*g Q)| ≤ _
  rw [he]
  calc
    _ ≤ uniformMean (fun Q => |(uniformMean fun a : K => f (Q+a • R))*g Q|) := abs_uniformMean_le _
    _ ≤ uniformMean (fun Q => formSingularIndicator
        (symFormPull φU.ker.subtype (symFormPull U.subtype Q))+1/(Fintype.card K : ℝ)) := by
      apply uniformMean_mono
      intro Q
      rw [abs_mul]
      calc
        _ ≤ |uniformMean fun a : K => f (Q+a • R)| * 1 :=
          mul_le_mul_of_nonneg_left (hgs Q) (abs_nonneg _)
        _ ≤ _ := by simpa only [mul_one] using hf Q
    _ = uniformMean (formSingularIndicator (K := K) (V := φU.ker))+
          1/(Fintype.card K : ℝ) := by
      rw [uniformMean_add,uniformMean_const]
      rw [uniformMean_restrict U.subtype U.subtype_injective
        (fun T => formSingularIndicator (symFormPull φU.ker.subtype T)),
        uniformMean_restrict φU.ker.subtype φU.ker.subtype_injective]
    _ ≤ (finrank K φU.ker : ℝ)/(Fintype.card K : ℝ)+1/(Fintype.card K : ℝ) :=
      add_le_add formSingularMean_bound le_rfl
    _ = _ := by
      rw [←add_div,←Nat.cast_one,←Nat.cast_add,dualKer_finrank φU x hxU]

private instance certificate_instance_0762 : OAI.SidorenkoCounterexample.ProofCertificate_0762 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15
  exact @certificate_proof_0762 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15

end Covariance
end SidorenkoCounterexample
end
section
namespace SidorenkoCounterexample
open Module
open scoped BigOperators
section Variance
variable {A I : Type} [Fintype A] [Fintype I] [Nonempty I]
omit [Nonempty I] in
theorem certificate_proof_0763 (f : I → ℝ) :
    (uniformMean f)^2 = uniformMean fun i => uniformMean fun j => f i*f j := by
  simp only [uniformMean_mul]
  have h := uniformMean_mul (uniformMean f) f
  simpa only [mul_comm,sq] using h.symm

private instance certificate_instance_0763 : OAI.SidorenkoCounterexample.ProofCertificate_0763 := by
  constructor
  intro q0 q1 q2
  exact @certificate_proof_0763 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 q0 q1 q2

theorem certificate_proof_0764 (f : A → ℝ) :
    (uniformMean fun a => |f a|)^2 ≤ uniformMean fun a => (f a)^2 := by
  simpa only [uniformMean,Finset.card_univ,sq_abs] using
    (sum_div_card_sq_le_sum_sq_div_card (s := Finset.univ) (f := fun a => |f a|))

private instance certificate_instance_0764 : OAI.SidorenkoCounterexample.ProofCertificate_0764 := by
  constructor
  intro q0 q1 q2
  exact @certificate_proof_0764 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 q0 q1 q2

theorem certificate_proof_0765 (f : I → A → ℝ) (ε : ℝ) (hε : 0≤ε)
    (hb : ∀ i a, |f i a| ≤ 1)
    (hc : ∀ i j, i≠j → |uniformMean fun a => f i a*f j a| ≤ ε) [Nonempty A] :
    uniformMean (fun a => (uniformMean fun i => f i a)^2) ≤ ε+1/(Fintype.card I : ℝ) := by
  classical
  have he : uniformMean (fun a => (uniformMean fun i => f i a)^2) =
      uniformMean fun i => uniformMean fun j => uniformMean fun a => f i a*f j a := by
    simp only [uniformMean_square]
    rw [uniformMean_swap]
    apply uniformMean_congr
    intro i
    exact uniformMean_swap _
  rw [he]
  calc
    _ ≤ uniformMean (fun i => uniformMean fun j => ε+(if i=j then 1 else 0)) := by
      apply uniformMean_mono
      intro i
      apply uniformMean_mono
      intro j
      by_cases hij : i=j
      · subst j
        simp only [ite_true]
        apply (uniformMean_bound (fun a => ?_)).trans (le_add_of_nonneg_left hε)
        calc
          f i a*f i a ≤ |f i a| * |f i a| := le_abs_self _ |>.trans_eq (abs_mul _ _)
          _ ≤ 1*1 := mul_le_mul (hb i a) (hb i a) (abs_nonneg _) (by norm_num)
          _ = 1 := one_mul _
      · simp only [if_neg hij,add_zero]
        exact (le_abs_self _).trans (hc i j hij)
    _ = _ := by
      simp only [uniformMean_add,uniformMean_const]
      have hi (i : I) : uniformMean (fun j : I => if i=j then (1 : ℝ) else 0) =
          1/(Fintype.card I : ℝ) := by simp [uniformMean]
      simp only [hi,uniformMean_const]

private instance certificate_instance_0765 : OAI.SidorenkoCounterexample.ProofCertificate_0765 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10
  exact @certificate_proof_0765 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10

end Variance
section Restriction
variable {K V I : Type} [Field K] [Fintype K] [DecidableEq K]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Fintype I] [Nonempty I]
theorem certificate_proof_0766 (U : I → Submodule K V) (hinj : Function.Injective U)
    (r : ℕ) (hd : ∀ i, finrank K (U i)=r) (hK : ringChar K ≠ 2)
    {ξ : ℤ} (hξ : ξ=1 ∨ ξ= -1) :
    uniformMean (fun Q : SymForm K V =>
      (uniformMean (fun i => formSignIndicator ξ (symFormPull (U i).subtype Q))-1/2)^2) ≤
      (r : ℝ)/(Fintype.card K : ℝ)+1/(Fintype.card I : ℝ) := by
  have h := family_variance_bound
    (fun i Q => formSignIndicator ξ (symFormPull (U i).subtype Q)-1/2)
    ((r : ℝ)/(Fintype.card K : ℝ)) (by positivity)
    (fun i Q => centered_formSign_abs ξ _)
    (fun i j hij => by
      have hne : U i≠U j := fun h => hij (hinj h)
      simpa only [hd] using restriction_covariance_bound (U i) (U j)
        ((hd i).trans (hd j).symm) hne hK hξ (ζ := ξ))
  simpa only [uniformMean_sub,uniformMean_const] using h

private instance certificate_instance_0766 : OAI.SidorenkoCounterexample.ProofCertificate_0766 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17
  exact @certificate_proof_0766 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17

end Restriction
end SidorenkoCounterexample
end
section
namespace SidorenkoCounterexample
open Module
section AlternatingTwo
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
variable [FiniteDimensional K V] [Fintype K]
end AlternatingTwo
end SidorenkoCounterexample
end
section
namespace SidorenkoCounterexample
open Module
section OrthogonalCharts
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
variable [FiniteDimensional K V]
end OrthogonalCharts
end SidorenkoCounterexample
end
section
namespace SidorenkoCounterexample
open Module
section SplitSign
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
variable [FiniteDimensional K V] [Fintype K] [DecidableEq K]
end SplitSign
end SidorenkoCounterexample
end
end OAI

theorem solution : OAI.SidorenkoCounterexample.ProofCertificate_0732 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0733 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0734 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0735 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0736 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0737 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0738 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0739 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0740 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0741 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0742 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0743 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0744 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0745 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0746 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0747 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0748 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0749 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0750 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0751 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0752 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0753 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0754 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0755 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0756 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0757 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0758 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0759 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0760 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0761 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0762 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0763 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0764 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0765 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0766 := by
  exact ⟨inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance⟩
end

