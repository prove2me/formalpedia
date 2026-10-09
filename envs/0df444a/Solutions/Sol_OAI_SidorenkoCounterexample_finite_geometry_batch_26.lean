-- Prove2me | solution 1 for OAI.SidorenkoCounterexample.finite_geometry_batch_26
-- status  : ACCEPTED   (prove)
-- author  : @abcdefg
-- created : 2026-10-09T06:29:27.1958+00:00
-- url     : https://prove2.me/submissions/fcb34893-e7b5-4296-ae2b-7ea9cfcc2f58

import Definitions.Def_SidorenkoCertificateBundleB
set_option linter.unusedVariables false
section
variable [p0 : OAI.SidorenkoCounterexample.ProofCertificate_0004]
  [p1 : OAI.SidorenkoCounterexample.ProofCertificate_0016]
  [p2 : OAI.SidorenkoCounterexample.ProofCertificate_0020]
  [p3 : OAI.SidorenkoCounterexample.ProofCertificate_0153]
  [p4 : OAI.SidorenkoCounterexample.ProofCertificate_0621]
  [p5 : OAI.SidorenkoCounterexample.ProofCertificate_0636]
  [p6 : OAI.SidorenkoCounterexample.ProofCertificate_0639]
  [p7 : OAI.SidorenkoCounterexample.ProofCertificate_0651]
  [p8 : OAI.SidorenkoCounterexample.ProofCertificate_0682]
  [p9 : OAI.SidorenkoCounterexample.ProofCertificate_0683]
  [p10 : OAI.SidorenkoCounterexample.ProofCertificate_0697]
  [p11 : OAI.SidorenkoCounterexample.ProofCertificate_0714]
  [p12 : OAI.SidorenkoCounterexample.ProofCertificate_0724]
  [p13 : OAI.SidorenkoCounterexample.ProofCertificate_0725]
  [p14 : OAI.SidorenkoCounterexample.ProofCertificate_0726]
  [p15 : OAI.SidorenkoCounterexample.ProofCertificate_0727]
  [p16 : OAI.SidorenkoCounterexample.ProofCertificate_0728]
  [p17 : OAI.SidorenkoCounterexample.ProofCertificate_0730]
  [p18 : OAI.SidorenkoCounterexample.ProofCertificate_0731]
  [p19 : OAI.SidorenkoCounterexample.ProofCertificate_0732]
  [p20 : OAI.SidorenkoCounterexample.ProofCertificate_0733]
  [p21 : OAI.SidorenkoCounterexample.ProofCertificate_0736]
  [p22 : OAI.SidorenkoCounterexample.ProofCertificate_0740]
  [p23 : OAI.SidorenkoCounterexample.ProofCertificate_0746]
  [p24 : OAI.SidorenkoCounterexample.ProofCertificate_0764]
  [p25 : OAI.SidorenkoCounterexample.ProofCertificate_0766]
include p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25

namespace OAI
section
namespace SidorenkoCounterexample
open Module
open scoped BigOperators
section Means
variable {A B : Type} [Fintype A] [Fintype B]
variable [AddGroup A]
end Means
section ShiftError
variable {K U : Type} [Field K] [Fintype K] [DecidableEq K]
  [AddCommGroup U] [Module K U] [FiniteDimensional K U]
end ShiftError
section Separate
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
end Separate
section Covariance
variable {K V : Type} [Field K] [Fintype K] [DecidableEq K]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]
end Covariance
end SidorenkoCounterexample
end
section
namespace SidorenkoCounterexample
open Module
open scoped BigOperators
section Variance
variable {A I : Type} [Fintype A] [Fintype I] [Nonempty I]
end Variance
section Restriction
variable {K V I : Type} [Field K] [Fintype K] [DecidableEq K]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Fintype I] [Nonempty I]
theorem certificate_proof_0767 (U : I → Submodule K V) (hinj : Function.Injective U)
    (r : ℕ) (hd : ∀ i, finrank K (U i)=r) (hK : ringChar K ≠ 2)
    {ξ : ℤ} (hξ : ξ=1 ∨ ξ= -1) :
    (uniformMean (fun Q : SymForm K V =>
      |uniformMean (fun i => formSignIndicator ξ (symFormPull (U i).subtype Q))-1/2|))^2 ≤
      (r : ℝ)/(Fintype.card K : ℝ)+1/(Fintype.card I : ℝ) :=
  (uniformMean_abs_sq_le _).trans (restriction_family_variance U hinj r hd hK hξ)

private instance certificate_instance_0767 : OAI.SidorenkoCounterexample.ProofCertificate_0767 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17
  exact @certificate_proof_0767 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17

end Restriction
end SidorenkoCounterexample
end
section
namespace SidorenkoCounterexample
open Module
section AlternatingTwo
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
omit [AddCommGroup V] in
theorem certificate_proof_0768 (x y z : V) : Function.update ![x,y] (0 : Fin 2) z = ![z,y] := by
  ext i
  fin_cases i <;> simp

private instance certificate_instance_0768 : OAI.SidorenkoCounterexample.ProofCertificate_0768 := by
  constructor
  intro q0 q1 q2 q3
  exact @certificate_proof_0768 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 q0 q1 q2 q3

omit [AddCommGroup V] in
theorem certificate_proof_0769 (x y z : V) : Function.update ![x,y] (1 : Fin 2) z = ![x,z] := by
  ext i
  fin_cases i <;> simp

private instance certificate_instance_0769 : OAI.SidorenkoCounterexample.ProofCertificate_0769 := by
  constructor
  intro q0 q1 q2 q3
  exact @certificate_proof_0769 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 q0 q1 q2 q3

variable [FiniteDimensional K V] [Fintype K]
theorem certificate_proof_0770 : Nat.card (AltForm (K := K) (V := V)) =
    Fintype.card K ^ (finrank K V).choose 2 := by
  rw [Nat.card_congr (altFormMapEquiv (K := K) (V := V)),
    Nat.card_congr (exteriorPower.alternatingMapLinearEquiv (R := K) (M := V) (N := K) (n := 2)).toEquiv]
  rw [Module.natCard_eq_pow_finrank (K := K), Subspace.dual_finrank_eq, exteriorPower.finrank_eq,
    Nat.card_eq_fintype_card]

private instance certificate_instance_0770 : OAI.SidorenkoCounterexample.ProofCertificate_0770 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6
  exact @certificate_proof_0770 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 q0 q1 q2 q3 q4 q5 q6

end AlternatingTwo
end SidorenkoCounterexample
end
section
namespace SidorenkoCounterexample
open Module
section OrthogonalCharts
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
theorem certificate_proof_0771 (p q : V × Module.Dual K V) :
    canonicalOrthogonal p q = q.2 p.1 + p.2 q.1 := rfl

private instance certificate_instance_0771 : OAI.SidorenkoCounterexample.ProofCertificate_0771 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6
  exact @certificate_proof_0771 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 q0 q1 q2 q3 q4 q5 q6

theorem certificate_proof_0772 : (canonicalOrthogonal (K := K) (V := V)).IsSymm := by
  constructor
  intro p q
  simp only [canonicalOrthogonal_apply, add_comm]

private instance certificate_instance_0772 : OAI.SidorenkoCounterexample.ProofCertificate_0772 := by
  constructor
  intro q0 q1 q2 q3 q4
  exact @certificate_proof_0772 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 q0 q1 q2 q3 q4

theorem certificate_proof_0773 :
    (canonicalOrthogonal (K := K) (V := V)).Nondegenerate := by
  have hleft : ∀ p : V × Module.Dual K V,
      (∀ q, canonicalOrthogonal p q = 0) → p = 0 := by
    rintro ⟨x,f⟩ hp
    have hx : x = 0 := (Module.forall_dual_apply_eq_zero_iff K x).mp (fun g => by
      simpa using hp (0,g))
    have hf : f = 0 := by
      ext y
      simpa using hp (y,0)
    simp [hx,hf]
  refine ⟨hleft, ?_⟩
  intros p hp
  apply hleft
  intro q
  exact canonicalOrthogonal_symm.isRefl _ _ (hp q)

private instance certificate_instance_0773 : OAI.SidorenkoCounterexample.ProofCertificate_0773 := by
  constructor
  intro q0 q1 q2 q3 q4
  exact @certificate_proof_0773 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 q0 q1 q2 q3 q4

variable [FiniteDimensional K V]
theorem certificate_proof_0774 (L : MaxOrthogonal (K := K) (V := V)) :
    finrank K L.val = finrank K V := by
  have h := LinearMap.BilinForm.finrank_orthogonal canonicalOrthogonal_nondegenerate L.val
  rw [L.property, Module.finrank_prod, Subspace.dual_finrank_eq] at h
  have hle := Submodule.finrank_le L.val
  rw [Module.finrank_prod, Subspace.dual_finrank_eq] at hle
  omega

private instance certificate_instance_0774 : OAI.SidorenkoCounterexample.ProofCertificate_0774 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6
  exact @certificate_proof_0774 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 q0 q1 q2 q3 q4 q5 q6

omit [FiniteDimensional K V] in
theorem certificate_proof_0775 (U : Submodule K V) (B : AltForm (K := K) (V := U)) :
    formGraph U B.val ≤ canonicalOrthogonal.orthogonal (formGraph U B.val) := by
  rintro p ⟨u,hu,hf⟩ q ⟨v,hv,hg⟩
  change p.2 q.1 + q.2 p.1 = 0
  rw [←hu,←hv]
  have hf' := congrArg (fun l : Module.Dual K U => l v) hf
  have hg' := congrArg (fun l : Module.Dual K U => l u) hg
  change p.2 v.val = B.val u v at hf'
  change q.2 u.val = B.val v u at hg'
  rw [hf',hg',← B.property.neg_eq u v]
  exact add_neg_cancel _

private instance certificate_instance_0775 : OAI.SidorenkoCounterexample.ProofCertificate_0775 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6
  exact @certificate_proof_0775 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 q0 q1 q2 q3 q4 q5 q6

theorem certificate_proof_0776 (U : Submodule K V) :
    Function.Injective (graphMaxOrthogonal (K := K) U) := by
  intro B C h
  apply Subtype.ext
  apply LinearMap.ext
  intro u
  obtain ⟨f,hf⟩ := Subspace.dualRestrict_surjective (W := U) (B.val u)
  have hp : (u.val,f) ∈ formGraph U B.val := ⟨u,rfl,hf⟩
  have he : formGraph U B.val = formGraph U C.val := congrArg Subtype.val h
  rw [he] at hp
  obtain ⟨v,hv,hg⟩ := hp
  have hv' : v = u := Subtype.ext hv
  exact hf.symm.trans (hv' ▸ hg)

private instance certificate_instance_0776 : OAI.SidorenkoCounterexample.ProofCertificate_0776 := by
  constructor
  intro c0 c1 c2 q0 q1 q2 q3 q4 q5 q6
  exact @certificate_proof_0776 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 q0 q1 q2 q3 q4 q5 q6

omit [FiniteDimensional K V] in
theorem certificate_proof_0777 (L : MaxOrthogonal (K := K) (V := V))
    {p q : V × Module.Dual K V} (hp : p ∈ L.val) (hq : q ∈ L.val) :
    canonicalOrthogonal p q = 0 := by
  have hq' : q ∈ canonicalOrthogonal.orthogonal L.val := L.property.symm ▸ hq
  exact hq' p hp

private instance certificate_instance_0777 : OAI.SidorenkoCounterexample.ProofCertificate_0777 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9
  exact @certificate_proof_0777 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9

theorem certificate_proof_0778 (hK : ringChar K ≠ 2) :
    Function.Surjective (fun S : Σ U : Submodule K V, AltForm (K := K) (V := U) => graphMaxOrthogonal S.1 S.2) := by
  intro L
  let U := L.val.map (LinearMap.fst K V (Module.Dual K V))
  let p : L.val →ₗ[K] U := {
    toFun := fun x => ⟨x.val.1, ⟨x.val,x.property,rfl⟩⟩
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }
  have hp : Function.Surjective p := by
    rintro ⟨x,y,hy,hyx⟩
    exact ⟨⟨y,hy⟩,Subtype.ext hyx⟩
  obtain ⟨s,hs⟩ := p.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr hp)
  have hsfst (u : U) : (s u).val.1 = u.val := congrArg Subtype.val (LinearMap.congr_fun hs u)
  let C : LinearMap.BilinForm K U :=
    (((LinearMap.snd K V (Module.Dual K V)).comp L.val.subtype).comp s).compl₂ U.subtype
  have hC : C.IsAlt := by
    intro u
    have h := maxOrthogonal_pairing_zero L (s u).property (s u).property
    change (s u).val.2 (s u).val.1 + (s u).val.2 (s u).val.1 = 0 at h
    rw [hsfst] at h
    change C u u + C u u = 0 at h
    exact (mul_eq_zero.mp ((two_mul (C u u)).trans h)).resolve_left (Ring.two_ne_zero hK)
  refine ⟨⟨U,⟨C,hC⟩⟩, ?_⟩
  apply Subtype.ext
  symm
  apply Submodule.eq_of_le_of_finrank_eq
  · intro x hx
    let u : U := ⟨x.1,⟨x,hx,rfl⟩⟩
    refine ⟨u,rfl,?_⟩
    apply LinearMap.ext
    intro y
    have h := maxOrthogonal_pairing_zero L hx (s y).property
    change (s y).val.2 x.1 + x.2 (s y).val.1 = 0 at h
    rw [hsfst] at h
    change x.2 y.val = (s u).val.2 y.val
    have hh : x.2 y.val = -(s y).val.2 u.val := (eq_neg_iff_add_eq_zero.mpr (by simpa only [add_comm] using h))
    exact hh.trans (hC.neg_eq y u)
  · exact (maxOrthogonal_finrank L).trans (formGraph_finrank U C).symm

private instance certificate_instance_0778 : OAI.SidorenkoCounterexample.ProofCertificate_0778 := by
  constructor
  intro c0 c1 c2 q0 q1 q2 q3 q4 q5 q6
  exact @certificate_proof_0778 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 q0 q1 q2 q3 q4 q5 q6

theorem certificate_proof_0779 [Fintype K] [Finite V] (hK : ringChar K ≠ 2) :
    letI := Fintype.ofFinite (Submodule K V)
    Nat.card (MaxOrthogonal (K := K) (V := V)) =
      ∑ U : Submodule K V, (Fintype.card K)^((finrank K U).choose 2) := by
  classical
  let := Fintype.ofFinite (Submodule K V)
  rw [← Nat.card_congr (maxOrthogonalGraphEquiv (K := K) (V := V) hK), Nat.card_sigma]
  simp only [altForm_card]

private instance certificate_instance_0779 : OAI.SidorenkoCounterexample.ProofCertificate_0779 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8
  exact @certificate_proof_0779 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 q0 q1 q2 q3 q4 q5 q6 q7 q8

end OrthogonalCharts
end SidorenkoCounterexample
end
section
namespace SidorenkoCounterexample
open Module
section SplitSign
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
theorem certificate_proof_0780 {ι : Type} [Fintype ι] [DecidableEq ι]
    (b : Basis ι K V) :
    canonicalOrthogonal.toMatrix (b.prod b.dualBasis) =
      Matrix.fromBlocks (0 : Matrix ι ι K) 1 1 0 := by
  ext i j
  cases i <;> cases j <;>
    simp [LinearMap.BilinForm.toMatrix_apply, Basis.prod_apply, Matrix.one_apply,
      Finsupp.single_apply, eq_comm]

private instance certificate_instance_0780 : OAI.SidorenkoCounterexample.ProofCertificate_0780 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8
  exact @certificate_proof_0780 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 q0 q1 q2 q3 q4 q5 q6 q7 q8

theorem certificate_proof_0781 {ι : Type} [Fintype ι] [DecidableEq ι] :
    (Matrix.fromBlocks (0 : Matrix ι ι K) (1 : Matrix ι ι K) (1 : Matrix ι ι K) 0).det = (-1 : K) ^ Fintype.card ι := by
  have hmul : Matrix.fromBlocks (0 : Matrix ι ι K) (1 : Matrix ι ι K) (1 : Matrix ι ι K) 0 *
      Matrix.fromBlocks (1 : Matrix ι ι K) (1 : Matrix ι ι K) (0 : Matrix ι ι K) 1 =
      Matrix.fromBlocks (0 : Matrix ι ι K) (1 : Matrix ι ι K) (1 : Matrix ι ι K) 1 := by
    rw [Matrix.fromBlocks_multiply]
    simp
  have h := congrArg Matrix.det hmul
  rw [Matrix.det_mul, Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, one_mul,
    mul_one, Matrix.det_fromBlocks_one₂₂] at h
  simpa only [Matrix.one_mul, zero_sub, Matrix.det_neg, Matrix.det_one, mul_one] using h

private instance certificate_instance_0781 : OAI.SidorenkoCounterexample.ProofCertificate_0781 := by
  constructor
  intro q0 q1 q2 q3 q4
  exact @certificate_proof_0781 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 q0 q1 q2 q3 q4

variable [FiniteDimensional K V] [Fintype K] [DecidableEq K]
theorem certificate_proof_0782 :
    discriminantSign (canonicalOrthogonal (K := K) (V := V)) canonicalOrthogonal_symm =
      quadraticChar K ((-1 : K) ^ finrank K V) := by
  rw [discriminantSign_nondegenerate _ _ canonicalOrthogonal_nondegenerate
    ((Module.finBasis K V).prod (Module.finBasis K V).dualBasis),
    canonicalOrthogonal_matrix, hyperbolic_block_det, Fintype.card_fin]

private instance certificate_instance_0782 : OAI.SidorenkoCounterexample.ProofCertificate_0782 := by
  constructor
  intro c0 q0 q1 q2 q3 q4 q5 q6 q7
  exact @certificate_proof_0782 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 q0 q1 q2 q3 q4 q5 q6 q7

theorem certificate_proof_0783 {E : Type} [AddCommGroup E] [Module K E]
    [FiniteDimensional K E] (B : LinearMap.BilinForm K E)
    (hs : B.IsSymm) (hB : B.Nondegenerate) (hK : ringChar K ≠ 2)
    (r : ℕ) (hd : finrank K E = 2*r)
    (hc : discriminantSign B hs = quadraticChar K ((-1 : K)^r)) :
    BilinEquivalent B (canonicalOrthogonal (K := K) (V := Fin r → K)) := by
  apply symmetric_equivalent_of_dim_sign B _ hs canonicalOrthogonal_symm hB
    canonicalOrthogonal_nondegenerate hK
  · simpa only [Module.finrank_prod, Subspace.dual_finrank_eq, Module.finrank_pi,
      Fintype.card_fin, two_mul] using hd
  · simpa only [canonicalOrthogonal_sign, Module.finrank_pi, Fintype.card_fin] using hc

private instance certificate_instance_0783 : OAI.SidorenkoCounterexample.ProofCertificate_0783 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14
  exact @certificate_proof_0783 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14

theorem certificate_proof_0784 {E : Type} [AddCommGroup E] [Module K E]
    [FiniteDimensional K E] (B : LinearMap.BilinForm K E)
    (hs : B.IsSymm) (hB : B.Nondegenerate) (hK : ringChar K ≠ 2)
    (r : ℕ) (hd : finrank K E = 2*r)
    (hc : discriminantSign B hs = quadraticChar K ((-1 : K)^r)) :
    Nat.card (SymplecticLagrangian B) =
      Nat.card (MaxOrthogonal (K := K) (V := Fin r → K)) := by
  obtain ⟨e,he⟩ := split_form_equivalent B hs hB hK r hd hc
  exact Nat.card_congr (symplecticLagrangianEquiv _ _ e he)

private instance certificate_instance_0784 : OAI.SidorenkoCounterexample.ProofCertificate_0784 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14
  exact @certificate_proof_0784 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14

end SplitSign
end SidorenkoCounterexample
end
end OAI
namespace OAI
section
namespace SidorenkoCounterexample
open scoped BigOperators
open Module Filter
theorem certificate_proof_0785 (D k i : ℕ) (hik : i ≤ k) (hkD : k ≤ D)
    (q : ℝ) (hq : q ≠ 0) :
    (q^D - q^i)/(q^k-q^i) = q^(D-k) *
      ((1 - 1/q^(D-i)) / (1 - 1/q^(k-i))) := by
  have hf (n : ℕ) (hi : i ≤ n) : q^n-q^i=q^n*(1-1/q^(n-i)) := by
    rw [mul_sub, mul_one, mul_one_div, div_eq_mul_inv,
      ← pow_sub₀ q hq (Nat.sub_le n i), Nat.sub_sub_self hi]
  rw [hf D (hik.trans hkD), hf k hik, mul_div_mul_comm,
    div_eq_mul_inv (q^D), ← pow_sub₀ q hq hkD]

private instance certificate_instance_0785 : OAI.SidorenkoCounterexample.ProofCertificate_0785 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6
  exact @certificate_proof_0785 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 q0 q1 q2 q3 q4 q5 q6

theorem certificate_proof_0786 {K V : Type} [Field K] [AddCommGroup V]
    [Module K V] [Fintype K] [Finite V] (k : ℕ) (hk : k ≤ finrank K V) :
    (Nat.card (DimSubspace K V k) : ℝ) =
      (Fintype.card K : ℝ)^(k*(finrank K V-k)) *
        grassmannFactor (finrank K V) k (Fintype.card K) := by
  rw [subspace_count_real k hk]
  have hf (i : Fin k) := grassmann_single_factor (finrank K V) k i.val i.isLt.le hk
    (Fintype.card K : ℝ) (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
  simp_rw [hf]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin, ← pow_mul, Nat.mul_comm (finrank K V-k) k]
  rfl

private instance certificate_instance_0786 : OAI.SidorenkoCounterexample.ProofCertificate_0786 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8
  exact @certificate_proof_0786 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 q0 q1 q2 q3 q4 q5 q6 q7 q8

theorem certificate_proof_0787 (n : ℕ) (hn : 0<n) :
    Tendsto (fun q : ℝ => 1/q^n) atTop (nhds 0) := by
  simpa only [one_div, inv_pow, zero_pow (Nat.ne_zero_of_lt hn)] using
    (tendsto_inv_atTop_zero (𝕜 := ℝ)).pow n

private instance certificate_instance_0787 : OAI.SidorenkoCounterexample.ProofCertificate_0787 := by
  constructor
  intro q0 q1
  exact @certificate_proof_0787 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 q0 q1

theorem certificate_proof_0788 (D k : ℕ) (hk : k ≤ D) :
    Tendsto (grassmannFactor D k) atTop (nhds 1) := by
  unfold grassmannFactor
  have h (i : Fin k) : Tendsto (fun q : ℝ =>
      (1 - 1/q^(D-i.val))/(1-1/q^(k-i.val))) atTop (nhds 1) := by
    have hD := inverse_power_tendsto_zero (D-i.val) (by omega)
    have hk' := inverse_power_tendsto_zero (k-i.val) (by omega)
    have ha : Tendsto (fun q : ℝ => 1-1/q^(D-i.val)) atTop (nhds (1-0:ℝ)) :=
      tendsto_const_nhds.sub hD
    have hb : Tendsto (fun q : ℝ => 1-1/q^(k-i.val)) atTop (nhds (1-0:ℝ)) :=
      tendsto_const_nhds.sub hk'
    have hc : Tendsto (fun q : ℝ =>
        (1-1/q^(D-i.val))/(1-1/q^(k-i.val))) atTop (nhds ((1-0:ℝ)/(1-0))) :=
      (ha.div hb (by norm_num)).congr (fun _ => rfl)
    simpa only [sub_zero, div_self (one_ne_zero : (1:ℝ) ≠ 0)] using hc
  simpa using tendsto_finsetProd Finset.univ (fun i _ => h i)

private instance certificate_instance_0788 : OAI.SidorenkoCounterexample.ProofCertificate_0788 := by
  constructor
  intro q0 q1 q2
  exact @certificate_proof_0788 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 q0 q1 q2

theorem certificate_proof_0789 (r k : ℕ) :
    (r+k+1).choose 2 = (r+1).choose 2 + (k+1).choose 2 + r*k := by
  have h : (((r+k+1).choose 2 : ℕ) : ℚ) =
      ((r+1).choose 2 : ℚ) + ((k+1).choose 2 : ℚ) + (r:ℚ)*k := by
    simp only [Nat.cast_choose_two, Nat.cast_add, Nat.cast_one]
    ring
  exact_mod_cast h

private instance certificate_instance_0789 : OAI.SidorenkoCounterexample.ProofCertificate_0789 := by
  constructor
  intro q0 q1
  exact @certificate_proof_0789 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 q0 q1

theorem certificate_proof_0790 {K : Type} [Field K] [Fintype K] [DecidableEq K]
    (D r : ℕ) (hrD : r ≤ D) {ξ : ℤ} (hξ : ξ = 1 ∨ ξ = -1) :
    layerMass K D r ξ * (Fintype.card K : ℝ)^((D-r+1).choose 2) =
      grassmannFactor D (D-r) (Fintype.card K) * symmetricSignProb (K := K) r ξ := by
  rw [layerMass_exact D r hrD hξ, subspace_count_normalized _ (by simp)]
  simp only [Module.finrank_pi, Fintype.card_fin, Nat.sub_sub_self hrD]
  have he : (D+1).choose 2 = (r+1).choose 2 + (D-r+1).choose 2 + (D-r)*r := by
    simpa only [Nat.add_sub_of_le hrD, Nat.mul_comm r (D-r)] using triangular_nat_add r (D-r)
  rw [he, pow_add, pow_add]
  have hq : (Fintype.card K : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  field_simp

private instance certificate_instance_0790 : OAI.SidorenkoCounterexample.ProofCertificate_0790 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8
  exact @certificate_proof_0790 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 q0 q1 q2 q3 q4 q5 q6 q7 q8

theorem certificate_proof_0791 :
    Tendsto (fun q : OddPrime => (q.val : ℝ)) primeInfinity atTop :=
  tendsto_natCast_atTop_atTop.comp Filter.tendsto_comap

private instance certificate_instance_0791 : OAI.SidorenkoCounterexample.ProofCertificate_0791 := by
  constructor
  exact @certificate_proof_0791 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25

theorem certificate_proof_0792 (r : ℕ) (hr : 0<r) {ξ : ℤ} (hξ : ξ=1 ∨ ξ= -1) :
    Tendsto (fun q : OddPrime => symmetricSignProb (K := ZMod q.val) r ξ)
      primeInfinity (nhds (1/2)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hlim : Tendsto (fun q : OddPrime => (r:ℝ)/q.val) primeInfinity (nhds 0) := by
    simpa only [div_eq_mul_inv,mul_zero, Function.comp_def] using
      ((tendsto_inv_atTop_zero (𝕜 := ℝ)).comp primeInfinity_real_tendsto).const_mul (r:ℝ)
  apply squeeze_zero (fun _ => norm_nonneg _) _ hlim
  intro q
  simpa only [Real.norm_eq_abs,ZMod.card] using
    symmetricSignProb_error (K := ZMod q.val) r hr
      (by simpa only [ZMod.ringChar_zmod_n] using q.property.2) hξ

private instance certificate_instance_0792 : OAI.SidorenkoCounterexample.ProofCertificate_0792 := by
  constructor
  intro q0 q1 q2 q3
  exact @certificate_proof_0792 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 q0 q1 q2 q3

theorem certificate_proof_0793 (D r : ℕ) (hr : 0<r) (hrD : r ≤ D)
    {ξ : ℤ} (hξ : ξ=1 ∨ ξ= -1) :
    Tendsto (fun q : OddPrime => layerMass (ZMod q.val) D r ξ *
      (q.val:ℝ)^((D-r+1).choose 2)) primeInfinity (nhds (1/2)) := by
  have he (q : OddPrime) := layerMass_normalized (K := ZMod q.val) D r hrD hξ
  simp only [ZMod.card] at he
  simp_rw [he]
  simpa only [one_mul, Function.comp_def] using
    ((grassmannFactor_tendsto D (D-r) (Nat.sub_le ..)).comp
      primeInfinity_real_tendsto).mul (symmetricSignProb_tendsto r hr hξ)

private instance certificate_instance_0793 : OAI.SidorenkoCounterexample.ProofCertificate_0793 := by
  constructor
  intro q0 q1 q2 q3 q4 q5
  exact @certificate_proof_0793 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 q0 q1 q2 q3 q4 q5

end SidorenkoCounterexample
end
section
namespace SidorenkoCounterexample
open Module Filter Topology
open scoped BigOperators
section CountDimension
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Fintype K] [Finite V]
theorem certificate_proof_0794 (hK : ringChar K ≠ 2) :
    Nat.card (MaxOrthogonal (K := K) (V := V)) =
      ∑ k : Fin (finrank K V+1), Nat.card (DimSubspace K V k.val) *
        Fintype.card K ^ k.val.choose 2 := by
  classical
  let := Fintype.ofFinite (Submodule K V)
  let d : Submodule K V → Fin (finrank K V+1) :=
    fun U => ⟨finrank K U,Nat.lt_succ_of_le (Submodule.finrank_le U)⟩
  rw [maxOrthogonal_card_sum hK,← Fintype.sum_fiberwise d]
  apply Finset.sum_congr rfl
  intro k _
  have hc : Nat.card {U : Submodule K V // d U = k} = Nat.card (DimSubspace K V k.val) :=
    Nat.card_congr (Equiv.subtypeEquivRight (fun U => by
      change (⟨finrank K U,_⟩ : Fin _)=k ↔ finrank K U=k.val
      exact Fin.ext_iff))
  have he (U : {U : Submodule K V // d U = k}) : finrank K U.val = k.val :=
    congrArg Fin.val U.property
  simp only [he,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,←Nat.card_eq_fintype_card,hc,Nat.cast_id]

private instance certificate_instance_0794 : OAI.SidorenkoCounterexample.ProofCertificate_0794 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8
  exact @certificate_proof_0794 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 q0 q1 q2 q3 q4 q5 q6 q7 q8

end CountDimension
theorem certificate_proof_0795 (a b : ℕ) : (a+b).choose 2 = a.choose 2+b.choose 2+a*b := by
  have h : (((a+b).choose 2 : ℕ) : ℚ) = (a.choose 2 : ℚ)+(b.choose 2 : ℚ)+(a:ℚ)*b := by
    simp only [Nat.cast_choose_two, Nat.cast_add]
    ring
  exact_mod_cast h

private instance certificate_instance_0795 : OAI.SidorenkoCounterexample.ProofCertificate_0795 := by
  constructor
  intro q0 q1
  exact @certificate_proof_0795 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 q0 q1

theorem certificate_proof_0796 {K : Type} [Field K] [Fintype K]
    (hK : ringChar K ≠ 2) (r : ℕ) :
    (Nat.card (MaxOrthogonal (K := K) (V := Fin r → K)) : ℝ) /
      (Fintype.card K : ℝ)^r.choose 2 = orthogonalFactor r (Fintype.card K) := by
  classical
  rw [maxOrthogonal_card_by_dimension hK,Module.finrank_fin_fun]
  simp only [Nat.cast_sum,Nat.cast_mul,Nat.cast_pow]
  rw [Finset.sum_div]
  unfold orthogonalFactor
  apply Finset.sum_congr rfl
  intro k _
  rw [subspace_count_normalized k.val (by simp; omega)]
  simp only [Module.finrank_fin_fun]
  have hr : (k.val+(r-k.val)).choose 2 = r.choose 2 := by rw [Nat.add_sub_of_le (by omega)]
  have he : r.choose 2 = k.val.choose 2 + (r-k.val).choose 2 + k.val*(r-k.val) := by
    rw [←hr,choose_two_add]
  rw [he,pow_add,pow_add]
  have hq : (Fintype.card K : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  field_simp

private instance certificate_instance_0796 : OAI.SidorenkoCounterexample.ProofCertificate_0796 := by
  constructor
  intro q0 q1 q2 q3 q4
  exact @certificate_proof_0796 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 q0 q1 q2 q3 q4

theorem certificate_proof_0797 (r : ℕ) (hr : 0<r) :
    Tendsto (orthogonalFactor r) atTop (nhds 2) := by
  obtain ⟨n,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hr)
  have hrest (k : Fin n) : Tendsto (fun q : ℝ =>
      grassmannFactor (n+1) k.val q / q^((n+1-k.val).choose 2)) atTop (nhds 0) := by
    have hp : 0 < (n+1-k.val).choose 2 := Nat.choose_pos (by omega)
    have h := (grassmannFactor_tendsto (n+1) k.val (by omega)).mul
      (inverse_power_tendsto_zero _ hp)
    simpa only [one_mul,div_eq_mul_inv,one_div] using h
  have hsum := tendsto_finsetSum Finset.univ (fun k (_ : k ∈ Finset.univ) => hrest k)
  have hn : Tendsto (fun q : ℝ => grassmannFactor (n+1) n q /
      q^((n+1-n).choose 2)) atTop (nhds 1) := by
    simpa using grassmannFactor_tendsto (n+1) n (Nat.le_succ n)
  have hn1 : Tendsto (fun q : ℝ => grassmannFactor (n+1) (n+1) q /
      q^((n+1-(n+1)).choose 2)) atTop (nhds 1) := by
    simpa using grassmannFactor_tendsto (n+1) (n+1) le_rfl
  have h := (hsum.add hn).add hn1
  simp only [Finset.sum_const_zero,zero_add] at h
  norm_num only [one_add_one_eq_two] at h
  convert h using 1
  funext q
  unfold orthogonalFactor
  rw [Fin.sum_univ_castSucc,Fin.sum_univ_castSucc]
  rfl

private instance certificate_instance_0797 : OAI.SidorenkoCounterexample.ProofCertificate_0797 := by
  constructor
  intro q0 q1
  exact @certificate_proof_0797 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 q0 q1

theorem certificate_proof_0798 {K E : Type} [Field K] [Fintype K] [DecidableEq K]
    [AddCommGroup E] [Module K E] [FiniteDimensional K E]
    (B : LinearMap.BilinForm K E) (hs : B.IsSymm) (hB : B.Nondegenerate)
    (hK : ringChar K ≠ 2) (r : ℕ) (hd : finrank K E=2*r)
    (hc : discriminantSign B hs = quadraticChar K ((-1 : K)^r)) :
    (Nat.card (SymplecticLagrangian B) : ℝ)/(Fintype.card K : ℝ)^r.choose 2 =
      orthogonalFactor r (Fintype.card K) := by
  rw [split_form_card B hs hB hK r hd hc]
  exact maxOrthogonal_normalized hK r

private instance certificate_instance_0798 : OAI.SidorenkoCounterexample.ProofCertificate_0798 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14
  exact @certificate_proof_0798 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14

end SidorenkoCounterexample
end
section
namespace SidorenkoCounterexample
open Module LinearMap
open scoped Matrix BigOperators
section PairSigns
variable {K : Type} [Field K] [Fintype K] [DecidableEq K] {D r : ℕ}
theorem certificate_proof_0799 (hd : D=2*r) (A B : SymMatrix K D)
    (hB : B.val.det≠0) (ha : A.val.rank=r) (hb : (A-B).val.rank=r) :
    quadraticChar K B.val.det = quadraticChar K ((-1 : K)^r) *
      matrixSign K D A * matrixSign K D (A-B) := by
  have hba : (B.val-A.val).rank=r := by
    have he : B.val-A.val= -(A-B).val := by simp
    rw [he,matrix_rank_neg,hb]
  have hi := (half_rank_projection r (by simpa using hd) A.val B.val hB ha).mp hba
  have hs := center_complement_sign B.val A.val B.property hB A.property hi
  have he : (⟨B.val-A.val,B.property.sub A.property⟩ : SymMatrix K D)= -(A-B) := by
    apply Subtype.ext; simp
  change quadraticChar K B.val.det = matrixSign K D A *
    matrixSign K D ⟨B.val-A.val,B.property.sub A.property⟩ at hs
  rw [he,matrixSign_neg,hb] at hs
  rw [hs]; ring

private instance certificate_instance_0799 : OAI.SidorenkoCounterexample.ProofCertificate_0799 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11
  exact @certificate_proof_0799 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11

theorem certificate_proof_0800 (hd : D=2*r) (A B : SymMatrix K D)
    (hB : B.val.det≠0) (ha : A.val.rank=r) {ξ ζ : ℤ} (hx : matrixSign K D A=ξ)
    (hm : quadraticChar K B.val.det=quadraticChar K ((-1 : K)^r)*ξ*ζ) :
    ((A-B).val.rank=r ∧ matrixSign K D (A-B)=ζ) ↔ A.val*B.val⁻¹*A.val=A.val := by
  have hr : (A-B).val.rank=r ↔ A.val*B.val⁻¹*A.val=A.val := by
    rw [←half_rank_projection r (by simpa using hd) A.val B.val hB ha]
    have he : (A-B).val= -(B.val-A.val) := by simp
    rw [he,matrix_rank_neg]
  constructor
  · exact fun h => hr.mp h.1
  · intro hi
    have hb := hr.mpr hi
    refine ⟨hb,?_⟩
    have hp := signed_pair_compatibility hd A B hB ha hb
    rw [hx,hm] at hp
    have hc : quadraticChar K ((-1 : K)^r)≠0 := by
      exact mt quadraticChar_eq_zero_iff.mp (pow_ne_zero r (neg_ne_zero.mpr (one_ne_zero : (1 : K)≠0)))
    have hn : ξ≠0 := by rw [←hx]; exact discriminantSign_ne_zero _ _
    exact mul_left_cancel₀ (mul_ne_zero hc hn) hp.symm

private instance certificate_instance_0800 : OAI.SidorenkoCounterexample.ProofCertificate_0800 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14
  exact @certificate_proof_0800 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14

end PairSigns
section Equiv
variable {K n : Type} [Field K] [Fintype K] [DecidableEq K] [Fintype n] [DecidableEq n]
omit [Fintype K] [DecidableEq K] in
theorem certificate_proof_0801 (Q : Matrix n n K) (hQ : Q.IsSymm) (hdet : Q.det≠0)
    (A : CenterProjection Q) : finrank K (centerSubspaceEquiv Q hQ hdet A).val = A.val.rank := by
  rw [centerSubspaceEquiv_val]
  rfl

private instance certificate_instance_0801 : OAI.SidorenkoCounterexample.ProofCertificate_0801 := by
  constructor
  intro c0 c1 c2 c3 c4 c5 c6 c7 c8 q0 q1 q2 q3 q4 q5 q6 q7 q8
  exact @certificate_proof_0801 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 q0 q1 q2 q3 q4 q5 q6 q7 q8

theorem certificate_proof_0802 (Q : Matrix n n K) (hQ : Q.IsSymm) (hdet : Q.det≠0)
    (A : CenterProjection Q) :
    discriminantSign A.val.toBilin' (Matrix.isSymm_toBilin'_iff_isSymm.mpr A.property.1) =
    discriminantSign (Q.toBilin'.restrict (centerSubspaceEquiv Q hQ hdet A).val)
      ((Matrix.isSymm_toBilin'_iff_isSymm.mpr hQ).restrict _) := by
  rw [centerSubspaceEquiv_val]
  exact center_discriminant Q A.val hQ hdet A.property.1 A.property.2

private instance certificate_instance_0802 : OAI.SidorenkoCounterexample.ProofCertificate_0802 := by
  constructor
  intro c0 c1 c2 c3 c4 c5 c6 c7 c8 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10
  exact @certificate_proof_0802 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10

end Equiv
end SidorenkoCounterexample
end
section
namespace SidorenkoCounterexample
open Module LinearMap
open scoped Matrix BigOperators
section SignedProjector
variable {K : Type} [Field K] [Fintype K] [DecidableEq K] {D r : ℕ}
end SignedProjector
end SidorenkoCounterexample
end
section
namespace SidorenkoCounterexample
open Module LinearMap
open scoped Matrix BigOperators
section Isotropic
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
theorem certificate_proof_0803 (L : LinearMap.BilinForm K V) (U : Submodule K V) :
    L.restrict U=0 ↔ U ≤ L.orthogonal U := by
  constructor
  · intro h x hx y hy
    have he := congrArg (fun B : LinearMap.BilinForm K U => B ⟨y,hy⟩ ⟨x,hx⟩) h
    exact he
  · intro h
    apply LinearMap.ext
    intro x
    apply LinearMap.ext
    intro y
    exact h y.property x.val x.property

private instance certificate_instance_0803 : OAI.SidorenkoCounterexample.ProofCertificate_0803 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6
  exact @certificate_proof_0803 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 q0 q1 q2 q3 q4 q5 q6

variable [FiniteDimensional K V]
theorem certificate_proof_0804 (L : LinearMap.BilinForm K V) (hL : L.Nondegenerate)
    (r : ℕ) (hd : finrank K V=2*r) (U : Submodule K V) (hu : finrank K U=r) :
    L.restrict U=0 ↔ L.orthogonal U=U := by
  rw [restrict_eq_zero_iff_isotropic]
  constructor
  · intro h
    symm
    apply Submodule.eq_of_le_of_finrank_eq h
    have hr := L.finrank_orthogonal hL U
    omega
  · intro h; rw [h]

private instance certificate_instance_0804 : OAI.SidorenkoCounterexample.ProofCertificate_0804 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11
  exact @certificate_proof_0804 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11

end Isotropic
section Triple
variable {K : Type} [Field K] [Fintype K] [DecidableEq K] {D r : ℕ}
end Triple
end SidorenkoCounterexample
end
end OAI

theorem solution : OAI.SidorenkoCounterexample.ProofCertificate_0767 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0768 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0769 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0770 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0771 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0772 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0773 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0774 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0775 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0776 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0777 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0778 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0779 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0780 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0781 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0782 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0783 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0784 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0785 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0786 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0787 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0788 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0789 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0790 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0791 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0792 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0793 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0794 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0795 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0796 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0797 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0798 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0799 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0800 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0801 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0802 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0803 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0804 := by
  exact ⟨inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance⟩
end

