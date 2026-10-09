-- Prove2me | solution 1 for OAI.SidorenkoCounterexample.finite_geometry_batch_06
-- status  : ACCEPTED   (prove)
-- author  : @abcdefg
-- created : 2026-10-09T05:45:14.234975+00:00
-- url     : https://prove2.me/submissions/d84ff65d-0140-4c7f-b4ff-4f20e27d0177

import Definitions.Def_SidorenkoFiniteGeometryCertificates05
set_option linter.unusedVariables false
section
variable [p0 : OAI.SidorenkoCounterexample.ProofCertificate_0012]
  [p1 : OAI.SidorenkoCounterexample.ProofCertificate_0014]
  [p2 : OAI.SidorenkoCounterexample.ProofCertificate_0017]
  [p3 : OAI.SidorenkoCounterexample.ProofCertificate_0020]
  [p4 : OAI.SidorenkoCounterexample.ProofCertificate_0033]
  [p5 : OAI.SidorenkoCounterexample.ProofCertificate_0034]
  [p6 : OAI.SidorenkoCounterexample.ProofCertificate_0107]
  [p7 : OAI.SidorenkoCounterexample.ProofCertificate_0108]
  [p8 : OAI.SidorenkoCounterexample.ProofCertificate_0110]
  [p9 : OAI.SidorenkoCounterexample.ProofCertificate_0128]
  [p10 : OAI.SidorenkoCounterexample.ProofCertificate_0150]
include p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10

namespace OAI
namespace SidorenkoCounterexample
open Module
section Reduction
variable {K E : Type} [Field K] [AddCommGroup E] [Module K E]
variable (ω : LinearMap.BilinForm K E) (S : Submodule K E)
end Reduction
section IsotropicExtension
variable {K E : Type} [Field K] [AddCommGroup E] [Module K E] [Finite E]
variable (ω : LinearMap.BilinForm K E)
end IsotropicExtension
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
section QuotientExtension
variable {K E : Type} [Field K] [AddCommGroup E] [Module K E]
variable [FiniteDimensional K E]
variable (ω : LinearMap.BilinForm K E) (S : Submodule K E)
end QuotientExtension
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
section ReductionLaws
variable {K E : Type} [Field K] [AddCommGroup E] [Module K E]
variable (ω : LinearMap.BilinForm K E) (S : Submodule K E)
variable [FiniteDimensional K E]
variable [Finite E]
end ReductionLaws
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
section IsotropicTransitivity
variable {K E : Type} [Field K] [AddCommGroup E] [Module K E]
  [FiniteDimensional K E] [Finite E]
variable (ω : LinearMap.BilinForm K E)
end IsotropicTransitivity
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
section TransversePairs
variable {K E : Type} [Field K] [AddCommGroup E] [Module K E]
  [FiniteDimensional K E]
variable (ω : LinearMap.BilinForm K E)
end TransversePairs
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
section PairTransitivity
variable {K E : Type} [Field K] [AddCommGroup E] [Module K E]
  [FiniteDimensional K E]
variable (ω : LinearMap.BilinForm K E)
end PairTransitivity
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
section PairReduction
variable {K E : Type} [Field K] [AddCommGroup E] [Module K E]
variable (ω : LinearMap.BilinForm K E) (S : Submodule K E)
variable [FiniteDimensional K E]
end PairReduction
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
section OrderedPairTransitivity
variable {K E : Type} [Field K] [AddCommGroup E] [Module K E]
  [FiniteDimensional K E] [Finite E]
variable (ω : LinearMap.BilinForm K E)
end OrderedPairTransitivity
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
section TripleBlocks
variable {K E : Type} [Field K] [AddCommGroup E] [Module K E]
  [FiniteDimensional K E]
variable (ω : LinearMap.BilinForm K E)
theorem certificate_proof_0151 (ha : ω.IsAlt)
    (B L : Submodule K E) (hB : (ω.restrict B).Nondegenerate)
    (hL : L ≤ ω.orthogonal L) (T : Submodule K B)
    (hT : (ω.restrict B).orthogonal T = T) (hTL : T.map B.subtype ≤ L) :
    L = T.map B.subtype ⊔ (L ⊓ ω.orthogonal B) := by
  let c := B.prodEquivOfIsCompl (ω.orthogonal B)
    (ω.isCompl_orthogonal_of_restrict_nondegenerate ha.isRefl hB)
  apply le_antisymm
  · intro x hx
    let b := (c.symm x).1
    let p := (c.symm x).2
    have hxp : b.val + p.val = x := c.apply_symm_apply x
    have hbT : b ∈ T := by
      apply hT.le
      intro t ht
      have htL : t.val ∈ L := hTL ⟨t,ht,rfl⟩
      have htx : ω t.val x = 0 := hL hx t.val htL
      have htp : ω t.val p.val = 0 := p.property t.val t.property
      rw [← hxp,map_add,htp,add_zero] at htx
      exact htx
    have hbL : b.val ∈ L := hTL ⟨b,hbT,rfl⟩
    have hpL : p.val ∈ L := by
      have hp : p.val = x - b.val := by rw [← hxp]; abel
      rw [hp]
      exact L.sub_mem hx hbL
    exact Submodule.mem_sup.mpr ⟨b.val,⟨b,hbT,rfl⟩,p.val,⟨hpL,p.property⟩,hxp⟩
  · exact sup_le hTL inf_le_left

private instance certificate_instance_0151 : OAI.SidorenkoCounterexample.ProofCertificate_0151 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14
  exact @certificate_proof_0151 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14

theorem certificate_proof_0152 (ha : ω.IsAlt)
    (B L : Submodule K E) (hB : (ω.restrict B).Nondegenerate)
    (hL : ω.orthogonal L = L) (T : Submodule K B)
    (hT : (ω.restrict B).orthogonal T = T) (hTL : T.map B.subtype ≤ L) :
    (ω.restrict (ω.orthogonal B)).orthogonal
      (L.comap (ω.orthogonal B).subtype) = L.comap (ω.orthogonal B).subtype := by
  have hs := forced_orthogonal_splitting ω ha B L hB hL.ge T hT hTL
  ext x
  constructor
  · intro hx
    change x.val ∈ L
    apply hL.le
    intro y hy
    rw [hs] at hy
    obtain ⟨b,⟨bt,hbt,rfl⟩,p,hp,rfl⟩ := Submodule.mem_sup.mp hy
    rw [map_add,LinearMap.add_apply]
    have hb : ω bt.val x.val = 0 := x.property bt.val bt.property
    have hq : ω p x.val = 0 := hx (⟨p,hp.2⟩ : ω.orthogonal B) hp.1
    change ω bt.val x.val + ω p x.val = 0
    rw [hb,hq,add_zero]
  · intro hx y hy
    exact hL.ge hx y.val hy

private instance certificate_instance_0152 : OAI.SidorenkoCounterexample.ProofCertificate_0152 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14
  exact @certificate_proof_0152 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14

end TripleBlocks
end SidorenkoCounterexample
end OAI
namespace OAI
namespace SidorenkoCounterexample
open Module
section GeneralIsometry
variable {K E F : Type} [Field K] [AddCommGroup E] [Module K E]
  [AddCommGroup F] [Module K F]
theorem certificate_proof_0153
    (ω : LinearMap.BilinForm K E) (η : LinearMap.BilinForm K F)
    (e : E ≃ₗ[K] F) (he : ∀ x y, η (e x) (e y) = ω x y)
    (U : Submodule K E) :
    η.orthogonal (U.map e.toLinearMap) = (ω.orthogonal U).map e.toLinearMap := by
  ext x
  constructor
  · intro hx
    refine ⟨e.symm x,?_,e.apply_symm_apply x⟩
    intro u hu
    rw [← he,e.apply_symm_apply]
    exact hx (e u) ⟨u,hu,rfl⟩
  · rintro ⟨y,hy,rfl⟩ _ ⟨u,hu,rfl⟩
    change η (e u) (e y) = 0
    rw [he]
    exact hy u hu

private instance certificate_instance_0153 : OAI.SidorenkoCounterexample.ProofCertificate_0153 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12
  exact @certificate_proof_0153 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12

end GeneralIsometry
section Horizontal
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
theorem certificate_proof_0154 (p : V × Module.Dual K V) :
    p ∈ horizontalSpace (K := K) ↔ p.2 = 0 := Iff.rfl

private instance certificate_instance_0154 : OAI.SidorenkoCounterexample.ProofCertificate_0154 := by
  constructor
  intro q0 q1 q2 q3 q4 q5
  exact @certificate_proof_0154 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 q0 q1 q2 q3 q4 q5

theorem certificate_proof_0155 :
    canonicalSymplectic.orthogonal (horizontalSpace (K := K) (V := V)) = horizontalSpace := by
  ext x
  constructor
  · intro hx
    change x.2 = 0
    ext v
    have hh := hx (v,0) (by rfl)
    simpa only [canonicalSymplectic_apply,LinearMap.zero_apply,sub_zero] using hh
  · intro hx v hv
    change x.2 v.1 - v.2 x.1 = 0
    rw [(mem_horizontalSpace x).mp hx,(mem_horizontalSpace v).mp hv]
    simp

private instance certificate_instance_0155 : OAI.SidorenkoCounterexample.ProofCertificate_0155 := by
  constructor
  intro q0 q1 q2 q3 q4
  exact @certificate_proof_0155 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 q0 q1 q2 q3 q4

end Horizontal
section TripleOneBlock
variable {K E : Type} [Field K] [AddCommGroup E] [Module K E]
  [FiniteDimensional K E]
variable (ω : LinearMap.BilinForm K E)
theorem certificate_proof_0156 (ha : ω.IsAlt)
    (L M N : Submodule K E) (hL : ω.orthogonal L = L)
    (hM : ω.orthogonal M = M) (hN : ω.orthogonal N = N)
    (hzero : (L ⊓ M) ⊓ N = ⊥) :
    ∃ B Q : Submodule K E,
      (ω.restrict B).Nondegenerate ∧ (L ⊓ M) ≤ B ∧ Q ≤ B ∧ Q ≤ N ∧
      finrank K Q = finrank K ↥(L ⊓ M) ∧
      B = (L ⊓ M) ⊔ Q ∧
      L = (L ⊓ M) ⊔ (L ⊓ ω.orthogonal B) ∧
      M = (L ⊓ M) ⊔ (M ⊓ ω.orthogonal B) ∧
      N = Q ⊔ (N ⊓ ω.orthogonal B) ∧
      L ⊓ N ≤ ω.orthogonal B ∧ M ⊓ N ≤ ω.orthogonal B ∧
      (L ⊓ ω.orthogonal B) ⊓ (M ⊓ ω.orthogonal B) = ⊥ ∧
      (∀ A ∈ ({L,M,N} : Set (Submodule K E)),
        (ω.restrict (ω.orthogonal B)).orthogonal (A.comap (ω.orthogonal B).subtype) =
          A.comap (ω.orthogonal B).subtype) ∧
      ∃ e : (↥(L ⊓ M) × Module.Dual K ↥(L ⊓ M)) ≃ₗ[K] B,
        (∀ s : ↥(L ⊓ M), (e (s,0)).val = s.val) ∧
        (verticalSpace.map e.toLinearMap).map B.subtype = Q ∧
        ∀ x y, ω (e x).val (e y).val = canonicalSymplectic x y := by
  let S := L ⊓ M
  have hS : S ≤ ω.orthogonal S := by
    intro s hs t ht
    exact hL.ge hs.1 t ht.1
  obtain ⟨B,hB,hSB,e,heS,heN,heform⟩ := exists_pair_block ω ha S N hS hN hzero
  let T : Submodule K B := (horizontalSpace (K := K) (V := S)).map e.toLinearMap
  let U : Submodule K B := (verticalSpace (K := K) (V := S)).map e.toLinearMap
  let Q := U.map B.subtype
  have hT : (ω.restrict B).orthogonal T = T := by
    change (ω.restrict B).orthogonal (horizontalSpace.map e.toLinearMap) = horizontalSpace.map e.toLinearMap
    rw [orthogonal_map_isometry_between (canonicalSymplectic (K := K) (V := S))
      (ω.restrict B) e (fun x y => heform x y),horizontalSpace_selforthogonal]
  have hU : (ω.restrict B).orthogonal U = U := by
    change (ω.restrict B).orthogonal (verticalSpace.map e.toLinearMap) = verticalSpace.map e.toLinearMap
    rw [orthogonal_map_isometry_between (canonicalSymplectic (K := K) (V := S))
      (ω.restrict B) e (fun x y => heform x y)]
    exact congrArg (fun U : Submodule K (S × Module.Dual K S) => U.map e.toLinearMap)
      (verticalLagrangian (K := K) (V := S)).property
  have hTS : T.map B.subtype = S := by
    ext x
    constructor
    · rintro ⟨b,⟨z,hz,rfl⟩,rfl⟩
      obtain ⟨s,f⟩ := z
      have hf : f = 0 := hz
      subst f
      change (e (s,0)).val ∈ S
      rw [heS]
      exact s.property
    · intro hx
      refine ⟨e (⟨x,hx⟩,0),⟨(⟨x,hx⟩,0),rfl,rfl⟩,?_⟩
      exact heS ⟨x,hx⟩
  have hQN : Q ≤ N := by
    rintro x ⟨b,⟨z,hz,rfl⟩,rfl⟩
    obtain ⟨s,f⟩ := z
    have hs : s = 0 := hz
    subst s
    exact heN f
  have hQB : Q ≤ B := by rintro x ⟨b,_,rfl⟩; exact b.property
  have hdim : finrank K Q = finrank K S := by
    change finrank K (U.map B.subtype) = finrank K S
    rw [← (Submodule.equivMapOfInjective B.subtype B.injective_subtype U).finrank_eq]
    change finrank K (verticalSpace.map e.toLinearMap) = finrank K S
    rw [e.finrank_map_eq]
    rw [← (verticalSpaceEquiv (K := K) (V := S)).finrank_eq,Subspace.dual_finrank_eq]
  have hBQ : B = S ⊔ Q := by
    apply le_antisymm
    · intro x hx
      obtain ⟨z,hz⟩ := e.surjective ⟨x,hx⟩
      have hsum : x = z.1.val + (e (0,z.2)).val := by
        have headd := e.map_add (z.1,0) (0,z.2)
        have headd' := congrArg Subtype.val headd
        simp only [Prod.mk_add_mk,add_zero,zero_add] at headd'
        rw [hz] at headd'
        change x = (e (z.1,0)).val + (e (0,z.2)).val at headd'
        rw [heS] at headd'
        exact headd'
      rw [hsum]
      exact Submodule.add_mem_sup z.1.property ⟨e (0,z.2),⟨(0,z.2),rfl,rfl⟩,rfl⟩
    · exact sup_le hSB hQB
  have hsplitL : L = S ⊔ (L ⊓ ω.orthogonal B) := by
    simpa only [hTS] using forced_orthogonal_splitting ω ha B L hB hL.ge T hT
      (by rw [hTS]; exact inf_le_left)
  have hsplitM : M = S ⊔ (M ⊓ ω.orthogonal B) := by
    simpa only [hTS] using forced_orthogonal_splitting ω ha B M hB hM.ge T hT
      (by rw [hTS]; exact inf_le_right)
  have hsplitN : N = Q ⊔ (N ⊓ ω.orthogonal B) :=
    forced_orthogonal_splitting ω ha B N hB hN.ge U hU hQN
  have hsurvive (A : Submodule K E) (hA : ω.orthogonal A = A) (hSA : S ≤ A) :
      A ⊓ N ≤ ω.orthogonal B := by
    intro x hx b hb
    rw [hBQ] at hb
    obtain ⟨s,hs,q,hq,rfl⟩ := Submodule.mem_sup.mp hb
    simp only [map_add,LinearMap.add_apply]
    rw [hA.ge hx.1 s (hSA hs),hN.ge hx.2 q (hQN hq),add_zero]
  have hdisj : (L ⊓ ω.orthogonal B) ⊓ (M ⊓ ω.orthogonal B) = ⊥ := by
    apply (Submodule.eq_bot_iff _).mpr
    intro x hx
    have hb : x ∈ B := hSB ⟨hx.1.1,hx.2.1⟩
    exact (ω.isCompl_orthogonal_of_restrict_nondegenerate ha.isRefl hB).disjoint.le_bot
      ⟨hb,hx.1.2⟩
  refine ⟨B,Q,hB,hSB,hQB,hQN,hdim,hBQ,hsplitL,hsplitM,hsplitN,
    hsurvive L hL inf_le_left,hsurvive M hM inf_le_right,hdisj,?_,e,heS,rfl,heform⟩
  intro A hA
  rcases (show A = L ∨ A = M ∨ A = N from hA) with hA | hA | hA
  · subst A
    exact split_residual_lagrangian ω ha B L hB hL T hT (by rw [hTS]; exact inf_le_left)
  · subst A
    exact split_residual_lagrangian ω ha B M hB hM T hT (by rw [hTS]; exact inf_le_right)
  · subst A
    exact split_residual_lagrangian ω ha B N hB hN U hU hQN

private instance certificate_instance_0156 : OAI.SidorenkoCounterexample.ProofCertificate_0156 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14
  exact @certificate_proof_0156 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14

end TripleOneBlock
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
section OrthogonalReduction
variable {K E : Type} [Field K] [AddCommGroup E] [Module K E]
  [FiniteDimensional K E]
variable (ω : LinearMap.BilinForm K E)
theorem certificate_proof_0157 (ha : ω.IsAlt)
    (S B : Submodule K E) (hB : (ω.restrict B).Nondegenerate)
    (hSB : S ≤ B) (hBS : B ⊓ ω.orthogonal S = S) :
    ∃ e : ω.orthogonal B ≃ₗ[K] ReducedSpace ω S,
      (∀ x : ω.orthogonal B, e x = (reductionKernel ω S).mkQ
        ⟨x.val,by intro s hs; exact x.property s (hSB hs)⟩) ∧
      (∀ x y, symplecticReductionForm ω S ha (e x) (e y) = ω x.val y.val) ∧
      ∀ L : Submodule K E, L = (L ⊓ B) ⊔ (L ⊓ ω.orthogonal B) →
        (L.comap (ω.orthogonal B).subtype).map e.toLinearMap = reduceSubspace ω S L := by
  let U := ω.orthogonal B
  have hUS : U ≤ ω.orthogonal S := by
    intro x hx s hs
    exact hx s (hSB hs)
  let f : U →ₗ[K] ReducedSpace ω S :=
    (reductionKernel ω S).mkQ.comp (Submodule.inclusion hUS)
  have hf (x : U) : f x = (reductionKernel ω S).mkQ ⟨x.val,hUS x.property⟩ := rfl
  have hc := ω.isCompl_orthogonal_of_restrict_nondegenerate ha.isRefl hB
  have hinj : Function.Injective f := by
    apply LinearMap.ker_eq_bot.mp
    apply (Submodule.eq_bot_iff _).mpr
    intro x hx
    have hxS : x.val ∈ S := (Submodule.Quotient.mk_eq_zero (reductionKernel ω S)).mp hx
    apply Subtype.ext
    exact hc.disjoint.le_bot ⟨hSB hxS,x.property⟩
  have hsurj : Function.Surjective f := by
    intro z
    induction z using Submodule.Quotient.induction_on with
    | H z =>
      have hz : z.val ∈ B ⊔ U := hc.sup_eq_top.symm ▸ Submodule.mem_top
      obtain ⟨b,hb,u,hu,hbu⟩ := Submodule.mem_sup.mp hz
      have hbS : b ∈ S := by
        apply hBS.le
        refine ⟨hb,?_⟩
        have hbval : b = z.val-u := by rw [←hbu]; abel
        rw [hbval]
        exact (ω.orthogonal S).sub_mem z.property (hUS hu)
      refine ⟨⟨u,hu⟩,?_⟩
      apply (Submodule.Quotient.eq (reductionKernel ω S)).mpr
      change u-z.val ∈ S
      have huval : u-z.val = -b := by rw [←hbu]; abel
      rw [huval]
      exact S.neg_mem hbS
  let e : U ≃ₗ[K] ReducedSpace ω S := LinearEquiv.ofBijective f ⟨hinj,hsurj⟩
  refine ⟨e,fun _ => rfl,fun _ _ => rfl,?_⟩
  intro L hL
  ext z
  constructor
  · rintro ⟨u,hu,rfl⟩
    exact ⟨⟨u.val,hUS u.property⟩,hu,rfl⟩
  · rintro ⟨x,hx,rfl⟩
    have hx' : x.val ∈ (L ⊓ B) ⊔ (L ⊓ U) := hL ▸ hx
    obtain ⟨b,hb,u,hu,hbu⟩ := Submodule.mem_sup.mp hx'
    have hbS : b ∈ S := by
      apply hBS.le
      refine ⟨hb.2,?_⟩
      have hbval : b = x.val-u := by rw [←hbu]; abel
      rw [hbval]
      exact (ω.orthogonal S).sub_mem x.property (hUS hu.2)
    refine ⟨⟨u,hu.2⟩,hu.1,?_⟩
    change (reductionKernel ω S).mkQ ⟨u,hUS hu.2⟩ = (reductionKernel ω S).mkQ x
    apply (Submodule.Quotient.eq (reductionKernel ω S)).mpr
    change u-x.val ∈ S
    have huval : u-x.val = -b := by rw [←hbu]; abel
    rw [huval]
    exact S.neg_mem hbS

private instance certificate_instance_0157 : OAI.SidorenkoCounterexample.ProofCertificate_0157 := by
  constructor
  intro c0 c1 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12
  exact @certificate_proof_0157 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12

end OrthogonalReduction
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
section ReductionInStages
variable {K E : Type} [Field K] [AddCommGroup E] [Module K E]
variable (ω : LinearMap.BilinForm K E) (ha : ω.IsAlt)
theorem certificate_proof_0158 (S T : Submodule K E)
    (hST : S ≤ T) (hT : T ≤ ω.orthogonal T) :
    ∃ e : ReducedSpace ω T ≃ₗ[K]
        ReducedSpace (symplecticReductionForm ω S ha) (reduceSubspace ω S T),
      (∀ x y, symplecticReductionForm (symplecticReductionForm ω S ha)
          (reduceSubspace ω S T) (symplecticReductionForm_alt ω S ha) (e x) (e y) =
        symplecticReductionForm ω T ha x y) ∧
      ∀ L : Submodule K E,
        (reduceSubspace ω T L).map e.toLinearMap =
          reduceSubspace (symplecticReductionForm ω S ha)
            (reduceSubspace ω S T) (reduceSubspace ω S L) := by
  let α := symplecticReductionForm ω S ha
  let R := reduceSubspace ω S T
  have hPS : ω.orthogonal T ≤ ω.orthogonal S := by
    intro x hx s hs
    exact hx s (hST hs)
  have hmem (x : ω.orthogonal S) :
      (reductionKernel ω S).mkQ x ∈ α.orthogonal R ↔ x.val ∈ ω.orthogonal T := by
    constructor
    · intro hx t ht
      have htS : t ∈ ω.orthogonal S := hPS (hT ht)
      exact hx ((reductionKernel ω S).mkQ ⟨t,htS⟩) ⟨⟨t,htS⟩,ht,rfl⟩
    · intro hx z hz
      obtain ⟨t,ht,rfl⟩ := hz
      exact hx t.val ht
  let p : ω.orthogonal T →ₗ[K] α.orthogonal R :=
    { toFun := fun x => ⟨(reductionKernel ω S).mkQ ⟨x.val,hPS x.property⟩,
          (hmem _).mpr x.property⟩
      map_add' := by
        intro x y
        apply Subtype.ext
        exact (reductionKernel ω S).mkQ.map_add
          ⟨x.val,hPS x.property⟩ ⟨y.val,hPS y.property⟩
      map_smul' := by
        intro c x
        apply Subtype.ext
        exact (reductionKernel ω S).mkQ.map_smul c ⟨x.val,hPS x.property⟩ }
  let g : ω.orthogonal T →ₗ[K] ReducedSpace α R := (reductionKernel α R).mkQ.comp p
  have hker : reductionKernel ω T ≤ g.ker := by
    intro x hx
    apply (Submodule.Quotient.mk_eq_zero (reductionKernel α R)).mpr
    exact ⟨⟨x.val,hPS x.property⟩,hx,rfl⟩
  let f : ReducedSpace ω T →ₗ[K] ReducedSpace α R := (reductionKernel ω T).liftQ g hker
  have hf (x : ω.orthogonal T) : f ((reductionKernel ω T).mkQ x) =
      (reductionKernel α R).mkQ (p x) := rfl
  have hinj : Function.Injective f := by
    apply LinearMap.ker_eq_bot.mp
    apply (Submodule.eq_bot_iff _).mpr
    intro z hz
    induction z using Submodule.Quotient.induction_on with
    | H x =>
      have hxR : (p x).val ∈ R :=
        (Submodule.Quotient.mk_eq_zero (reductionKernel α R)).mp hz
      obtain ⟨t,ht,heq⟩ := hxR
      have hdiff : t.val-x.val ∈ S :=
        (Submodule.Quotient.eq (reductionKernel ω S)).mp heq
      apply (Submodule.Quotient.mk_eq_zero (reductionKernel ω T)).mpr
      have hxT := T.sub_mem ht (hST hdiff)
      change x.val ∈ T
      simpa only [Submodule.subtype_apply,sub_sub_cancel] using hxT
  have hsurj : Function.Surjective f := by
    intro z
    induction z using Submodule.Quotient.induction_on with
    | H y =>
      obtain ⟨x,hx⟩ := (reductionKernel ω S).mkQ_surjective y.val
      have hxT : x.val ∈ ω.orthogonal T := (hmem x).mp (hx.symm ▸ y.property)
      refine ⟨(reductionKernel ω T).mkQ ⟨x.val,hxT⟩,?_⟩
      rw [hf]
      apply congrArg (reductionKernel α R).mkQ
      apply Subtype.ext
      exact hx
  let e : ReducedSpace ω T ≃ₗ[K] ReducedSpace α R := LinearEquiv.ofBijective f ⟨hinj,hsurj⟩
  refine ⟨e,?_,?_⟩
  · intro x y
    induction x using Submodule.Quotient.induction_on with
    | H x =>
      induction y using Submodule.Quotient.induction_on with
      | H y => rfl
  · intro L
    ext z
    constructor
    · rintro ⟨y,⟨x,hx,rfl⟩,rfl⟩
      refine ⟨p x,?_,rfl⟩
      exact ⟨⟨x.val,hPS x.property⟩,hx,rfl⟩
    · rintro ⟨y,hy,rfl⟩
      obtain ⟨x,hx,hxy⟩ := hy
      have hxT : x.val ∈ ω.orthogonal T := (hmem x).mp (hxy.symm ▸ y.property)
      refine ⟨(reductionKernel ω T).mkQ ⟨x.val,hxT⟩,
        ⟨⟨x.val,hxT⟩,hx,rfl⟩,?_⟩
      change (reductionKernel α R).mkQ (p ⟨x.val,hxT⟩) = (reductionKernel α R).mkQ y
      congr 1
      apply Subtype.ext
      exact hxy

private instance certificate_instance_0158 : OAI.SidorenkoCounterexample.ProofCertificate_0158 := by
  constructor
  intro c0 c1 c2 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10
  exact @certificate_proof_0158 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10

end ReductionInStages
end SidorenkoCounterexample
namespace SidorenkoCounterexample
section ReductionIsometry
variable {K E F : Type} [Field K] [AddCommGroup E] [Module K E]
  [AddCommGroup F] [Module K F]
theorem certificate_proof_0159
    (ω : LinearMap.BilinForm K E) (η : LinearMap.BilinForm K F)
    (ha : ω.IsAlt) (hb : η.IsAlt) (e : E ≃ₗ[K] F)
    (he : ∀ x y, η (e x) (e y) = ω x y)
    (S : Submodule K E) (T : Submodule K F) (hST : S.map e.toLinearMap = T) :
    ∃ f : ReducedSpace ω S ≃ₗ[K] ReducedSpace η T,
      (∀ x y, symplecticReductionForm η T hb (f x) (f y) =
        symplecticReductionForm ω S ha x y) ∧
      ∀ L : Submodule K E,
        (reduceSubspace ω S L).map f.toLinearMap = reduceSubspace η T (L.map e.toLinearMap) := by
  have hP : (ω.orthogonal S).map e.toLinearMap = η.orthogonal T := by
    ext y
    constructor
    · rintro ⟨x,hx,rfl⟩ t ht
      rw [←hST] at ht
      obtain ⟨s,hs,rfl⟩ := ht
      change η (e s) (e x) = 0
      rw [he]
      exact hx s hs
    · intro hy
      refine ⟨e.symm y,?_,e.apply_symm_apply y⟩
      intro s hs
      rw [←he,e.apply_symm_apply]
      exact hy (e s) (hST.le ⟨s,hs,rfl⟩)
  let p : ω.orthogonal S ≃ₗ[K] η.orthogonal T := e.ofSubmodules _ _ hP
  have hp (x : ω.orthogonal S) : (p x).val = e x.val := rfl
  have hker : (reductionKernel ω S).map p.toLinearMap = reductionKernel η T := by
    ext y
    constructor
    · rintro ⟨x,hx,rfl⟩
      exact hST.le ⟨x.val,hx,rfl⟩
    · intro hy
      obtain ⟨x,rfl⟩ := p.surjective y
      have hex : e x.val ∈ T := hy
      rw [←hST] at hex
      obtain ⟨s,hs,hse⟩ := hex
      have hsx : s = x.val := e.injective hse
      refine ⟨x,?_,rfl⟩
      change x.val ∈ S
      exact hsx ▸ hs
  let f := Submodule.Quotient.equiv (reductionKernel ω S) (reductionKernel η T) p hker
  have hf (x : ω.orthogonal S) : f ((reductionKernel ω S).mkQ x) =
      (reductionKernel η T).mkQ (p x) := rfl
  refine ⟨f,?_,?_⟩
  · intro x y
    induction x using Submodule.Quotient.induction_on with
    | H x =>
      induction y using Submodule.Quotient.induction_on with
      | H y => exact he x.val y.val
  · intro L
    ext z
    constructor
    · rintro ⟨y,⟨x,hx,rfl⟩,rfl⟩
      refine ⟨p x,?_,rfl⟩
      exact ⟨x.val,hx,rfl⟩
    · rintro ⟨y,hy,rfl⟩
      obtain ⟨x,rfl⟩ := p.surjective y
      obtain ⟨l,hl,hlx⟩ := hy
      have hlx' : l = x.val := e.injective hlx
      refine ⟨(reductionKernel ω S).mkQ x,⟨x,?_,rfl⟩,rfl⟩
      change x.val ∈ L
      exact hlx' ▸ hl

private instance certificate_instance_0159 : OAI.SidorenkoCounterexample.ProofCertificate_0159 := by
  constructor
  intro c0 c1 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16
  exact @certificate_proof_0159 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16

end ReductionIsometry
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
section OrthogonalIsometries
variable {K E F : Type} [Field K] [AddCommGroup E] [Module K E]
  [AddCommGroup F] [Module K F] [FiniteDimensional K E] [FiniteDimensional K F]
theorem certificate_proof_0160
    (ω : LinearMap.BilinForm K E) (η : LinearMap.BilinForm K F)
    (ha : ω.IsAlt) (hb : η.IsAlt)
    (B : Submodule K E) (C : Submodule K F)
    (hB : (ω.restrict B).Nondegenerate) (hC : (η.restrict C).Nondegenerate)
    (f : B ≃ₗ[K] C) (g : ω.orthogonal B ≃ₗ[K] η.orthogonal C)
    (hf : ∀ x y, η (f x).val (f y).val = ω x.val y.val)
    (hg : ∀ x y, η (g x).val (g y).val = ω x.val y.val) :
    ∃ e : E ≃ₗ[K] F, (∀ x y, η (e x) (e y) = ω x y) ∧
      (∀ x : B, e x.val = (f x).val) ∧
      (∀ x : ω.orthogonal B, e x.val = (g x).val) := by
  let c := B.prodEquivOfIsCompl (ω.orthogonal B)
    (ω.isCompl_orthogonal_of_restrict_nondegenerate ha.isRefl hB)
  let d := C.prodEquivOfIsCompl (η.orthogonal C)
    (η.isCompl_orthogonal_of_restrict_nondegenerate hb.isRefl hC)
  let e := c.symm.trans ((f.prodCongr g).trans d)
  have he (x : B × ω.orthogonal B) : e (c x) = d (f x.1,g x.2) := by simp [e]
  refine ⟨e,?_,?_,?_⟩
  · intro x y
    obtain ⟨x,rfl⟩ := c.surjective x
    obtain ⟨y,rfl⟩ := c.surjective y
    rw [he,he]
    change η ((f x.1).val + (g x.2).val) ((f y.1).val + (g y.2).val) =
      ω (x.1.val + x.2.val) (y.1.val + y.2.val)
    rw [form_orthogonal_sum η hb C (f x.1,g x.2) (f y.1,g y.2),
      form_orthogonal_sum ω ha B x y,hf,hg]
  · intro x
    have h := he (x,0)
    simpa [c,d] using h
  · intro x
    have h := he (0,x)
    simpa [c,d] using h

private instance certificate_instance_0160 : OAI.SidorenkoCounterexample.ProofCertificate_0160 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19 q20 q21
  exact @certificate_proof_0160 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19 q20 q21

omit [FiniteDimensional K E] [FiniteDimensional K F] in
theorem certificate_proof_0161 (e : E ≃ₗ[K] F)
    (B : Submodule K E) (C : Submodule K F)
    (f : B ≃ₗ[K] C) (heB : ∀ x : B, e x.val = (f x).val)
    (U : Submodule K E) (W : Submodule K F)
    (g : U ≃ₗ[K] W) (heU : ∀ x : U, e x.val = (g x).val)
    (L : Submodule K E) (M : Submodule K F)
    (hL : L = (L ⊓ B) ⊔ (L ⊓ U)) (hM : M = (M ⊓ C) ⊔ (M ⊓ W))
    (hf : (L.comap B.subtype).map f.toLinearMap = M.comap C.subtype)
    (hg : (L.comap U.subtype).map g.toLinearMap = M.comap W.subtype) :
    L.map e.toLinearMap = M := by
  have hblock : (L ⊓ B).map e.toLinearMap = M ⊓ C := by
    ext y
    constructor
    · rintro ⟨x,hx,rfl⟩
      have hy : f ⟨x,hx.2⟩ ∈ M.comap C.subtype := hf.le ⟨⟨x,hx.2⟩,hx.1,rfl⟩
      change e x ∈ M ⊓ C
      rw [heB ⟨x,hx.2⟩]
      exact ⟨hy,(f ⟨x,hx.2⟩).property⟩
    · intro hy
      have hy' : (⟨y,hy.2⟩ : C) ∈ (L.comap B.subtype).map f.toLinearMap := hf.ge hy.1
      obtain ⟨x,hx,hxy⟩ := hy'
      refine ⟨x.val,⟨hx,x.property⟩,?_⟩
      change e x.val = y
      exact (heB x).trans (congrArg Subtype.val hxy)
  have hres : (L ⊓ U).map e.toLinearMap = M ⊓ W := by
    ext y
    constructor
    · rintro ⟨x,hx,rfl⟩
      have hy : g ⟨x,hx.2⟩ ∈ M.comap W.subtype := hg.le ⟨⟨x,hx.2⟩,hx.1,rfl⟩
      change e x ∈ M ⊓ W
      rw [heU ⟨x,hx.2⟩]
      exact ⟨hy,(g ⟨x,hx.2⟩).property⟩
    · intro hy
      have hy' : (⟨y,hy.2⟩ : W) ∈ (L.comap U.subtype).map g.toLinearMap := hg.ge hy.1
      obtain ⟨x,hx,hxy⟩ := hy'
      refine ⟨x.val,⟨hx,x.property⟩,?_⟩
      change e x.val = y
      exact (heU x).trans (congrArg Subtype.val hxy)
  calc
    L.map e.toLinearMap = ((L ⊓ B) ⊔ (L ⊓ U)).map e.toLinearMap := congrArg _ hL
    _ = (M ⊓ C) ⊔ (M ⊓ W) := by rw [Submodule.map_sup,hblock,hres]
    _ = M := hM.symm

private instance certificate_instance_0161 : OAI.SidorenkoCounterexample.ProofCertificate_0161 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19 q20 q21 q22
  exact @certificate_proof_0161 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19 q20 q21 q22

end OrthogonalIsometries
end SidorenkoCounterexample
namespace SidorenkoCounterexample
section SplitHelpers
variable {K E : Type} [Field K] [AddCommGroup E] [Module K E]
theorem certificate_proof_0162 (L A B U : Submodule K E)
    (hBU : Disjoint B U) (hAB : A ≤ B) (hL : L = A ⊔ (L ⊓ U)) :
    L ⊓ B = A := by
  apply le_antisymm
  · intro x hx
    have hxL : x ∈ A ⊔ (L ⊓ U) := hL ▸ hx.1
    obtain ⟨a,ha,u,hu,hau⟩ := Submodule.mem_sup.mp hxL
    have huB : u ∈ B := by
      have huval : u = x-a := by rw [←hau]; abel
      rw [huval]
      exact B.sub_mem hx.2 (hAB ha)
    have hu0 : u = 0 := hBU.le_bot ⟨huB,hu.2⟩
    rw [hu0,add_zero] at hau
    exact hau ▸ ha
  · exact le_inf (hL.symm ▸ le_sup_left) hAB

private instance certificate_instance_0162 : OAI.SidorenkoCounterexample.ProofCertificate_0162 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11
  exact @certificate_proof_0162 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11

theorem certificate_proof_0163 (L A B U : Submodule K E)
    (hAB : A ≤ B) (hL : L = A ⊔ (L ⊓ U)) :
    L = (L ⊓ B) ⊔ (L ⊓ U) := by
  apply le_antisymm
  · calc
      L = A ⊔ (L ⊓ U) := hL
      _ ≤ (L ⊓ B) ⊔ (L ⊓ U) :=
        sup_le_sup (le_inf (hL.symm ▸ le_sup_left) hAB) le_rfl
  · exact sup_le inf_le_left inf_le_left

private instance certificate_instance_0163 : OAI.SidorenkoCounterexample.ProofCertificate_0163 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10
  exact @certificate_proof_0163 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10

end SplitHelpers
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
section TripleBlockData
variable {K E : Type} [Field K] [AddCommGroup E] [Module K E]
  [FiniteDimensional K E]
variable (ω : LinearMap.BilinForm K E)
end TripleBlockData
end SidorenkoCounterexample
namespace SidorenkoCounterexample
section MapTransport
variable {K E F E' F' : Type} [Field K]
  [AddCommGroup E] [Module K E] [AddCommGroup F] [Module K F]
  [AddCommGroup E'] [Module K E'] [AddCommGroup F'] [Module K F']
end MapTransport
open Module
section TripleOneBlockLift
variable {K E F : Type} [Field K]
  [AddCommGroup E] [Module K E] [AddCommGroup F] [Module K F]
  [FiniteDimensional K E] [FiniteDimensional K F]
end TripleOneBlockLift
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
section ReductionIntersections
variable {K E : Type} [Field K] [AddCommGroup E] [Module K E]
variable (ω : LinearMap.BilinForm K E) (S : Submodule K E)
end ReductionIntersections
section PairSum
variable {K E : Type} [Field K] [AddCommGroup E] [Module K E]
variable (ω : LinearMap.BilinForm K E)
end PairSum
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
section ClassificationPredicates
variable {K E F : Type} [Field K]
  [AddCommGroup E] [Module K E] [AddCommGroup F] [Module K F]
end ClassificationPredicates
section ResidualClassificationStep
variable {K E F : Type} [Field K]
  [AddCommGroup E] [Module K E] [AddCommGroup F] [Module K F]
  [FiniteDimensional K E] [FiniteDimensional K F]
end ResidualClassificationStep
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
section FullClassification
variable {K E F : Type} [Field K]
  [AddCommGroup E] [Module K E] [AddCommGroup F] [Module K F]
  [FiniteDimensional K E] [FiniteDimensional K F]
end FullClassification
end SidorenkoCounterexample
end OAI

theorem solution : OAI.SidorenkoCounterexample.ProofCertificate_0151 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0152 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0153 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0154 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0155 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0156 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0157 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0158 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0159 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0160 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0161 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0162 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0163 := by
  exact ⟨inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance⟩
end

