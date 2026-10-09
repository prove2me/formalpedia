-- Prove2me | solution 1 for OAI.SidorenkoCounterexample.finite_geometry_batch_07
-- status  : ACCEPTED   (prove)
-- author  : @abcdefg
-- created : 2026-10-09T05:45:14.644548+00:00
-- url     : https://prove2.me/submissions/bcafd1b2-ec6f-4093-9525-d1b2bf228d15

import Definitions.Def_SidorenkoFiniteGeometryCertificates05
set_option linter.unusedVariables false
section
variable [p0 : OAI.SidorenkoCounterexample.ProofCertificate_0012]
  [p1 : OAI.SidorenkoCounterexample.ProofCertificate_0107]
  [p2 : OAI.SidorenkoCounterexample.ProofCertificate_0108]
  [p3 : OAI.SidorenkoCounterexample.ProofCertificate_0110]
  [p4 : OAI.SidorenkoCounterexample.ProofCertificate_0111]
  [p5 : OAI.SidorenkoCounterexample.ProofCertificate_0121]
  [p6 : OAI.SidorenkoCounterexample.ProofCertificate_0123]
  [p7 : OAI.SidorenkoCounterexample.ProofCertificate_0125]
  [p8 : OAI.SidorenkoCounterexample.ProofCertificate_0142]
  [p9 : OAI.SidorenkoCounterexample.ProofCertificate_0153]
  [p10 : OAI.SidorenkoCounterexample.ProofCertificate_0155]
  [p11 : OAI.SidorenkoCounterexample.ProofCertificate_0156]
  [p12 : OAI.SidorenkoCounterexample.ProofCertificate_0157]
  [p13 : OAI.SidorenkoCounterexample.ProofCertificate_0158]
  [p14 : OAI.SidorenkoCounterexample.ProofCertificate_0160]
  [p15 : OAI.SidorenkoCounterexample.ProofCertificate_0161]
  [p16 : OAI.SidorenkoCounterexample.ProofCertificate_0162]
  [p17 : OAI.SidorenkoCounterexample.ProofCertificate_0163]
include p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17

namespace OAI
namespace SidorenkoCounterexample
open Module
section GeneralIsometry
variable {K E F : Type} [Field K] [AddCommGroup E] [Module K E]
  [AddCommGroup F] [Module K F]
end GeneralIsometry
section Horizontal
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
end Horizontal
section TripleOneBlock
variable {K E : Type} [Field K] [AddCommGroup E] [Module K E]
  [FiniteDimensional K E]
variable (ω : LinearMap.BilinForm K E)
end TripleOneBlock
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
section OrthogonalReduction
variable {K E : Type} [Field K] [AddCommGroup E] [Module K E]
  [FiniteDimensional K E]
variable (ω : LinearMap.BilinForm K E)
end OrthogonalReduction
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
section ReductionInStages
variable {K E : Type} [Field K] [AddCommGroup E] [Module K E]
variable (ω : LinearMap.BilinForm K E) (ha : ω.IsAlt)
end ReductionInStages
end SidorenkoCounterexample
namespace SidorenkoCounterexample
section ReductionIsometry
variable {K E F : Type} [Field K] [AddCommGroup E] [Module K E]
  [AddCommGroup F] [Module K F]
end ReductionIsometry
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
section OrthogonalIsometries
variable {K E F : Type} [Field K] [AddCommGroup E] [Module K E]
  [AddCommGroup F] [Module K F] [FiniteDimensional K E] [FiniteDimensional K F]
end OrthogonalIsometries
end SidorenkoCounterexample
namespace SidorenkoCounterexample
section SplitHelpers
variable {K E : Type} [Field K] [AddCommGroup E] [Module K E]
end SplitHelpers
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
section TripleBlockData
variable {K E : Type} [Field K] [AddCommGroup E] [Module K E]
  [FiniteDimensional K E]
variable (ω : LinearMap.BilinForm K E)
theorem certificate_proof_0164 (ha : ω.IsAlt)
    (L M N : Submodule K E) (hL : ω.orthogonal L = L)
    (hM : ω.orthogonal M = M) (hN : ω.orthogonal N = N)
    (hzero : (L ⊓ M) ⊓ N = ⊥) :
    ∃ B : Submodule K E, (ω.restrict B).Nondegenerate ∧
      ∃ e : (↥(L ⊓ M) × Module.Dual K ↥(L ⊓ M)) ≃ₗ[K] B,
      ∃ f : ω.orthogonal B ≃ₗ[K] ReducedSpace ω (L ⊓ M),
        (∀ x y, ω (e x).val (e y).val = canonicalSymplectic x y) ∧
        (∀ x y, symplecticReductionForm ω (L ⊓ M) ha (f x) (f y) = ω x.val y.val) ∧
        L.comap B.subtype = horizontalSpace.map e.toLinearMap ∧
        M.comap B.subtype = horizontalSpace.map e.toLinearMap ∧
        N.comap B.subtype = verticalSpace.map e.toLinearMap ∧
        ∀ A ∈ ({L,M,N} : Set (Submodule K E)),
          A = (A ⊓ B) ⊔ (A ⊓ ω.orthogonal B) ∧
          (A.comap (ω.orthogonal B).subtype).map f.toLinearMap =
            reduceSubspace ω (L ⊓ M) A := by
  obtain ⟨B,Q,hB,hSB,hQB,_hQN,_hdim,_hBQ,hSL,hSM,hSN,_hsL,_hsM,_hdisj,_hres,
    e,heS,heQ,heform⟩ := triple_pair_block ω ha L M N hL hM hN hzero
  let S := L ⊓ M
  let T : Submodule K B := horizontalSpace.map e.toLinearMap
  have hTS : T.map B.subtype = S := by
    ext x
    constructor
    · rintro ⟨b,⟨z,hz,rfl⟩,rfl⟩
      obtain ⟨s,g⟩ := z
      have hg : g = 0 := hz
      subst g
      change (e (s,0)).val ∈ S
      rw [heS]
      exact s.property
    · intro hx
      refine ⟨e (⟨x,hx⟩,0),⟨(⟨x,hx⟩,0),rfl,rfl⟩,?_⟩
      exact heS ⟨x,hx⟩
  have hT : (ω.restrict B).orthogonal T = T := by
    rw [orthogonal_map_isometry_between (canonicalSymplectic (K := K) (V := S))
      (ω.restrict B) e (fun x y => heform x y),horizontalSpace_selforthogonal]
  have hBS : B ⊓ ω.orthogonal S = S := by
    apply le_antisymm
    · intro x hx
      have hxT : (⟨x,hx.1⟩ : B) ∈ T := by
        apply hT.le
        intro b hb
        exact hx.2 b.val (hTS.le ⟨b,hb,rfl⟩)
      exact hTS.le ⟨⟨x,hx.1⟩,hxT,rfl⟩
    · refine le_inf hSB ?_
      intro s hs t ht
      exact hL.ge hs.1 t ht.1
  have hLU := split_over_block L S B (ω.orthogonal B) hSB hSL
  have hMU := split_over_block M S B (ω.orthogonal B) hSB hSM
  have hNU := split_over_block N Q B (ω.orthogonal B) hQB hSN
  obtain ⟨f,_hf,hfform,hfred⟩ := exists_complement_reduction_equiv ω ha S B hB hSB hBS
  have hcompl := ω.isCompl_orthogonal_of_restrict_nondegenerate ha.isRefl hB
  have hLB := split_inter_block L S B (ω.orthogonal B) hcompl.disjoint hSB hSL
  have hMB := split_inter_block M S B (ω.orthogonal B) hcompl.disjoint hSB hSM
  have hNB := split_inter_block N Q B (ω.orthogonal B) hcompl.disjoint hQB hSN
  refine ⟨B,hB,e,f,heform,hfform,?_,?_,?_,?_⟩
  · apply Submodule.map_injective_of_injective B.injective_subtype
    rw [Submodule.map_comap_subtype,inf_comm,hLB]
    exact hTS.symm
  · apply Submodule.map_injective_of_injective B.injective_subtype
    rw [Submodule.map_comap_subtype,inf_comm,hMB]
    exact hTS.symm
  · apply Submodule.map_injective_of_injective B.injective_subtype
    rw [Submodule.map_comap_subtype,inf_comm,hNB]
    exact heQ.symm
  · intro A hA
    rcases (show A = L ∨ A = M ∨ A = N from hA) with heq | heq | heq
    · subst A; exact ⟨hLU,hfred L hLU⟩
    · subst A; exact ⟨hMU,hfred M hMU⟩
    · subst A; exact ⟨hNU,hfred N hNU⟩

private instance certificate_instance_0164 : OAI.SidorenkoCounterexample.ProofCertificate_0164 := by
  constructor
  intro c0 c1 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14
  exact @certificate_proof_0164 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14

end TripleBlockData
end SidorenkoCounterexample
namespace SidorenkoCounterexample
section MapTransport
variable {K E F E' F' : Type} [Field K]
  [AddCommGroup E] [Module K E] [AddCommGroup F] [Module K F]
  [AddCommGroup E'] [Module K E'] [AddCommGroup F'] [Module K F']
theorem certificate_proof_0165 (u : E ≃ₗ[K] E') (v : F ≃ₗ[K] F')
    (r : E' ≃ₗ[K] F') (A : Submodule K E) (B : Submodule K F)
    (h : (A.map u.toLinearMap).map r.toLinearMap = B.map v.toLinearMap) :
    A.map (u.trans (r.trans v.symm)).toLinearMap = B := by
  apply Submodule.map_injective_of_injective v.injective
  calc
    (A.map (u.trans (r.trans v.symm)).toLinearMap).map v.toLinearMap =
        (A.map u.toLinearMap).map r.toLinearMap := by
      simp only [← Submodule.map_comp]
      congr 1
      ext x
      simp
    _ = B.map v.toLinearMap := h

private instance certificate_instance_0165 : OAI.SidorenkoCounterexample.ProofCertificate_0165 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19
  exact @certificate_proof_0165 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19

theorem certificate_proof_0166 (u : E ≃ₗ[K] E') (v : F ≃ₗ[K] F')
    (r : E ≃ₗ[K] F) (A : Submodule K E) :
    (A.map u.toLinearMap).map (u.symm.trans (r.trans v)).toLinearMap =
      (A.map r.toLinearMap).map v.toLinearMap := by
  simp only [← Submodule.map_comp]
  congr 1
  ext x
  simp

private instance certificate_instance_0166 : OAI.SidorenkoCounterexample.ProofCertificate_0166 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17
  exact @certificate_proof_0166 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17

end MapTransport
open Module
section TripleOneBlockLift
variable {K E F : Type} [Field K]
  [AddCommGroup E] [Module K E] [AddCommGroup F] [Module K F]
  [FiniteDimensional K E] [FiniteDimensional K F]
theorem certificate_proof_0167
    (ω : LinearMap.BilinForm K E) (η : LinearMap.BilinForm K F)
    (ha : ω.IsAlt) (hb : η.IsAlt)
    (L M N : Submodule K E) (L' M' N' : Submodule K F)
    (hL : ω.orthogonal L = L) (hM : ω.orthogonal M = M) (hN : ω.orthogonal N = N)
    (hL' : η.orthogonal L' = L') (hM' : η.orthogonal M' = M')
    (hN' : η.orthogonal N' = N')
    (hzero : (L ⊓ M) ⊓ N = ⊥) (hzero' : (L' ⊓ M') ⊓ N' = ⊥)
    (hdim : finrank K ↥(L ⊓ M) = finrank K ↥(L' ⊓ M'))
    (r : ReducedSpace ω (L ⊓ M) ≃ₗ[K] ReducedSpace η (L' ⊓ M'))
    (hr : ∀ x y, symplecticReductionForm η (L' ⊓ M') hb (r x) (r y) =
      symplecticReductionForm ω (L ⊓ M) ha x y)
    (hrL : (reduceSubspace ω (L ⊓ M) L).map r.toLinearMap =
      reduceSubspace η (L' ⊓ M') L')
    (hrM : (reduceSubspace ω (L ⊓ M) M).map r.toLinearMap =
      reduceSubspace η (L' ⊓ M') M')
    (hrN : (reduceSubspace ω (L ⊓ M) N).map r.toLinearMap =
      reduceSubspace η (L' ⊓ M') N') :
    ∃ e : E ≃ₗ[K] F, (∀ x y, η (e x) (e y) = ω x y) ∧
      L.map e.toLinearMap = L' ∧ M.map e.toLinearMap = M' ∧
      N.map e.toLinearMap = N' := by
  obtain ⟨B,hB,b,f,hbform,hfform,hLb,hMb,hNb,hsplit⟩ :=
    triple_block_reduction_data ω ha L M N hL hM hN hzero
  obtain ⟨C,hC,c,g,hcform,hgform,hLc,hMc,hNc,hsplit'⟩ :=
    triple_block_reduction_data η hb L' M' N' hL' hM' hN' hzero'
  let t : ↥(L ⊓ M) ≃ₗ[K] ↥(L' ⊓ M') := LinearEquiv.ofFinrankEq _ _ hdim
  let w := t.prodCongr t.symm.dualMap
  have hw (x y : ↥(L ⊓ M) × Module.Dual K ↥(L ⊓ M)) :
      canonicalSymplectic (w x) (w y) = canonicalSymplectic x y := by
    simp [w,canonicalSymplectic_apply]
  have hwH : horizontalSpace.map w.toLinearMap = horizontalSpace := by
    apply subspace_map_eq_of_mem_iff
    intro x
    change t.symm.dualMap x.2 = 0 ↔ x.2 = 0
    exact t.symm.dualMap.map_eq_zero_iff
  have hwV : verticalSpace.map w.toLinearMap = verticalSpace := by
    apply subspace_map_eq_of_mem_iff
    intro x
    change t x.1 = 0 ↔ x.1 = 0
    exact t.map_eq_zero_iff
  let u := b.symm.trans (w.trans c)
  let v := f.trans (r.trans g.symm)
  have hu (x y : B) : η (u x).val (u y).val = ω x.val y.val := by
    change η (c (w (b.symm x))).val (c (w (b.symm y))).val = _
    rw [hcform,hw,←hbform,b.apply_symm_apply,b.apply_symm_apply]
  have hv (x y : ω.orthogonal B) : η (v x).val (v y).val = ω x.val y.val := by
    rw [← hgform]
    change symplecticReductionForm η (L' ⊓ M') hb
      (g (g.symm (r (f x)))) (g (g.symm (r (f y)))) = _
    rw [g.apply_symm_apply,g.apply_symm_apply,hr,hfform]
  obtain ⟨e,he,heB,heU⟩ := exists_orthogonal_isometry_between ω η ha hb B C hB hC u v hu hv
  have hblockH : (horizontalSpace.map b.toLinearMap).map u.toLinearMap =
      horizontalSpace.map c.toLinearMap := by
    rw [map_conjugate_equiv b c w,hwH]
  have hblockV : (verticalSpace.map b.toLinearMap).map u.toLinearMap =
      verticalSpace.map c.toLinearMap := by
    rw [map_conjugate_equiv b c w,hwV]
  have hmap (A : Submodule K E) (A' : Submodule K F)
      (hA : A ∈ ({L,M,N} : Set (Submodule K E)))
      (hA' : A' ∈ ({L',M',N'} : Set (Submodule K F)))
      (hblock : (A.comap B.subtype).map u.toLinearMap = A'.comap C.subtype)
      (hres : (reduceSubspace ω (L ⊓ M) A).map r.toLinearMap =
        reduceSubspace η (L' ⊓ M') A') : A.map e.toLinearMap = A' := by
    obtain ⟨hAs,hAr⟩ := hsplit A hA
    obtain ⟨hAs',hAr'⟩ := hsplit' A' hA'
    apply map_orthogonal_split e B C u heB (ω.orthogonal B) (η.orthogonal C)
      v heU A A' hAs hAs' hblock
    apply map_transport_equiv f g r
    rw [hAr,hAr',hres]
  refine ⟨e,he,?_,?_,?_⟩
  · exact hmap L L' (by simp) (by simp) (by rw [hLb,hLc]; exact hblockH) hrL
  · exact hmap M M' (by simp) (by simp) (by rw [hMb,hMc]; exact hblockH) hrM
  · exact hmap N N' (by simp) (by simp) (by rw [hNb,hNc]; exact hblockV) hrN

private instance certificate_instance_0167 : OAI.SidorenkoCounterexample.ProofCertificate_0167 := by
  constructor
  intro c0 c1 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19 q20 q21 q22 q23 q24 q25 q26 q27 q28 q29 q30 q31 q32 q33
  exact @certificate_proof_0167 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19 q20 q21 q22 q23 q24 q25 q26 q27 q28 q29 q30 q31 q32 q33

end TripleOneBlockLift
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
section ReductionIntersections
variable {K E : Type} [Field K] [AddCommGroup E] [Module K E]
variable (ω : LinearMap.BilinForm K E) (S : Submodule K E)
theorem certificate_proof_0168 : reduceSubspace ω S S = ⊥ := by
  apply (Submodule.eq_bot_iff _).mpr
  rintro x ⟨y,hy,rfl⟩
  exact (Submodule.Quotient.mk_eq_zero (reductionKernel ω S)).mpr hy

private instance certificate_instance_0168 : OAI.SidorenkoCounterexample.ProofCertificate_0168 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6
  exact @certificate_proof_0168 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 q0 q1 q2 q3 q4 q5 q6

theorem certificate_proof_0169 (L N : Submodule K E) (hSL : S ≤ L) :
    reduceSubspace ω S (L ⊓ N) =
      reduceSubspace ω S L ⊓ reduceSubspace ω S N := by
  apply le_antisymm
  · rintro x ⟨y,hy,rfl⟩
    exact ⟨⟨y,hy.1,rfl⟩,⟨y,hy.2,rfl⟩⟩
  · rintro x ⟨⟨l,hl,hlx⟩,⟨n,hn,hnx⟩⟩
    have heq : (reductionKernel ω S).mkQ (l-n) = 0 := by
      rw [map_sub,hlx,hnx,sub_self]
    have hln : l.val-n.val ∈ S :=
      (Submodule.Quotient.mk_eq_zero (reductionKernel ω S)).mp heq
    have hnL : n.val ∈ L := by
      have h := L.sub_mem hl (hSL hln)
      simpa using h
    exact ⟨n,⟨hnL,hn⟩,hnx⟩

private instance certificate_instance_0169 : OAI.SidorenkoCounterexample.ProofCertificate_0169 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9
  exact @certificate_proof_0169 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9

theorem certificate_proof_0170 [FiniteDimensional K E]
    (A : Submodule K E) (hAP : A ≤ ω.orthogonal S) (hAS : Disjoint A S) :
    finrank K (reduceSubspace ω S A) = finrank K A := by
  let f : A →ₗ[K] ReducedSpace ω S :=
    (reductionKernel ω S).mkQ.comp ((Submodule.inclusion hAP))
  have hf : Function.Injective f := by
    apply LinearMap.ker_eq_bot.mp
    apply (Submodule.eq_bot_iff _).mpr
    intro x hx
    apply Subtype.ext
    have hxS : x.val ∈ S :=
      (Submodule.Quotient.mk_eq_zero (reductionKernel ω S)).mp hx
    exact hAS.le_bot ⟨x.property,hxS⟩
  have hfr : LinearMap.range f = reduceSubspace ω S A := by
    ext y
    constructor
    · rintro ⟨x,rfl⟩
      exact ⟨⟨x.val,hAP x.property⟩,x.property,rfl⟩
    · rintro ⟨x,hx,rfl⟩
      exact ⟨⟨x.val,hx⟩,rfl⟩
  rw [←hfr]
  exact (LinearEquiv.ofInjective f hf).finrank_eq.symm

private instance certificate_instance_0170 : OAI.SidorenkoCounterexample.ProofCertificate_0170 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10
  exact @certificate_proof_0170 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10

theorem certificate_proof_0171 (A B : Submodule K E)
    (hA : A ≤ ω.orthogonal S) (hB : B ≤ ω.orthogonal S) :
    reduceSubspace ω S (A ⊔ B) = reduceSubspace ω S A ⊔ reduceSubspace ω S B := by
  have hcomap : (A ⊔ B).comap (ω.orthogonal S).subtype =
      A.comap (ω.orthogonal S).subtype ⊔ B.comap (ω.orthogonal S).subtype := by
    ext x
    constructor
    · intro hx
      obtain ⟨a,ha,b,hb,hab⟩ := Submodule.mem_sup.mp hx
      exact Submodule.mem_sup.mpr
        ⟨⟨a,hA ha⟩,ha,⟨b,hB hb⟩,hb,Subtype.ext hab⟩
    · intro hx
      obtain ⟨a,ha,b,hb,rfl⟩ := Submodule.mem_sup.mp hx
      exact Submodule.mem_sup.mpr ⟨a.val,ha,b.val,hb,rfl⟩
  unfold reduceSubspace
  rw [hcomap,Submodule.map_sup]

private instance certificate_instance_0171 : OAI.SidorenkoCounterexample.ProofCertificate_0171 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10
  exact @certificate_proof_0171 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10

end ReductionIntersections
section PairSum
variable {K E : Type} [Field K] [AddCommGroup E] [Module K E]
variable (ω : LinearMap.BilinForm K E)
theorem certificate_proof_0172 (L M N : Submodule K E)
    (hL : ω.orthogonal L = L) (hM : ω.orthogonal M = M)
    (hN : ω.orthogonal N = N) :
    triplePairSum L M N ≤ ω.orthogonal (triplePairSum L M N) := by
  rw [triplePairSum,orthogonal_sup_eq,orthogonal_sup_eq]
  refine sup_le (sup_le (le_inf (le_inf ?_ ?_) ?_) (le_inf (le_inf ?_ ?_) ?_))
    (le_inf (le_inf ?_ ?_) ?_)
  all_goals intro x hx y hy
  · exact hL.ge hx.1 y hy.1
  · exact hL.ge hx.1 y hy.1
  · exact hM.ge hx.2 y hy.1
  · exact hL.ge hx.1 y hy.1
  · exact hL.ge hx.1 y hy.1
  · exact hN.ge hx.2 y hy.2
  · exact hM.ge hx.1 y hy.2
  · exact hN.ge hx.2 y hy.2
  · exact hM.ge hx.1 y hy.1

private instance certificate_instance_0172 : OAI.SidorenkoCounterexample.ProofCertificate_0172 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11
  exact @certificate_proof_0172 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11

theorem certificate_proof_0173 [FiniteDimensional K E]
    (L M N : Submodule K E)
    (hL : ω.orthogonal L = L) (hM : ω.orthogonal M = M)
    (hzero : (L ⊓ M) ⊓ N = ⊥) :
    let S := L ⊓ M
    let P := reduceSubspace ω S L
    let Q := reduceSubspace ω S M
    let R := reduceSubspace ω S N
    P ⊓ Q = ⊥ ∧
      P ⊓ R = reduceSubspace ω S (L ⊓ N) ∧
      Q ⊓ R = reduceSubspace ω S (M ⊓ N) ∧
      finrank K ↥(P ⊓ R) = finrank K ↥(L ⊓ N) ∧
      finrank K ↥(Q ⊓ R) = finrank K ↥(M ⊓ N) ∧
      triplePairSum P Q R = reduceSubspace ω S (triplePairSum L M N) := by
  dsimp only
  have hLM := reduceSubspace_inf ω (L ⊓ M) L M inf_le_left
  have hLN := reduceSubspace_inf ω (L ⊓ M) L N inf_le_left
  have hMN := reduceSubspace_inf ω (L ⊓ M) M N inf_le_right
  have hLP : L ≤ ω.orthogonal (L ⊓ M) := lagrangian_le_orthogonal ω _ L hL inf_le_left
  have hMP : M ≤ ω.orthogonal (L ⊓ M) := lagrangian_le_orthogonal ω _ M hM inf_le_right
  have hLNdis : Disjoint (L ⊓ N) (L ⊓ M) := by
    apply disjoint_iff.mpr
    apply (Submodule.eq_bot_iff _).mpr
    intro x hx
    exact hzero.le ⟨hx.2,hx.1.2⟩
  have hMNdis : Disjoint (M ⊓ N) (L ⊓ M) := by
    apply disjoint_iff.mpr
    apply (Submodule.eq_bot_iff _).mpr
    intro x hx
    exact hzero.le ⟨hx.2,hx.1.2⟩
  rw [←hLM,reduceSubspace_self,←hLN,←hMN]
  refine ⟨rfl,rfl,rfl,?_,?_,?_⟩
  · exact reduceSubspace_finrank_of_disjoint ω _ _ (inf_le_left.trans hLP) hLNdis
  · exact reduceSubspace_finrank_of_disjoint ω _ _ (inf_le_left.trans hMP) hMNdis
  · rw [triplePairSum,triplePairSum,
      reduceSubspace_sup ω _ _ _ (sup_le (inf_le_left.trans hLP)
        (inf_le_left.trans hLP)) (inf_le_left.trans hMP),
      reduceSubspace_sup ω _ _ _ (inf_le_left.trans hLP) (inf_le_left.trans hLP),
      reduceSubspace_self,←hLM,←hLN,←hMN,reduceSubspace_self]

private instance certificate_instance_0173 : OAI.SidorenkoCounterexample.ProofCertificate_0173 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12
  exact @certificate_proof_0173 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12

end PairSum
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
section ClassificationPredicates
variable {K E F : Type} [Field K]
  [AddCommGroup E] [Module K E] [AddCommGroup F] [Module K F]
theorem certificate_proof_0174
    {ω : LinearMap.BilinForm K E} {η : LinearMap.BilinForm K F}
    {ha : ω.IsAlt} {hb : η.IsAlt}
    {L M N : Submodule K E} {L' M' N' : Submodule K F}
    (h : TripleResidualIsometry ω η ha hb L M N L' M' N') :
    TripleResidualIsometry ω η ha hb L N M L' N' M' := by
  have hs : triplePairSum L N M = triplePairSum L M N := by unfold triplePairSum; ac_rfl
  have hs' : triplePairSum L' N' M' = triplePairSum L' M' N' := by unfold triplePairSum; ac_rfl
  unfold TripleResidualIsometry at *
  rw [hs,hs']
  obtain ⟨e,he,hL,hM,hN⟩ := h
  exact ⟨e,he,hL,hN,hM⟩

private instance certificate_instance_0174 : OAI.SidorenkoCounterexample.ProofCertificate_0174 := by
  constructor
  intro c0 c1 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18
  exact @certificate_proof_0174 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18

theorem certificate_proof_0175
    {ω : LinearMap.BilinForm K E} {η : LinearMap.BilinForm K F}
    {ha : ω.IsAlt} {hb : η.IsAlt}
    {L M N : Submodule K E} {L' M' N' : Submodule K F}
    (h : TripleResidualIsometry ω η ha hb L M N L' M' N') :
    TripleResidualIsometry ω η ha hb M N L M' N' L' := by
  have hs : triplePairSum M N L = triplePairSum L M N := by unfold triplePairSum; ac_rfl
  have hs' : triplePairSum M' N' L' = triplePairSum L' M' N' := by unfold triplePairSum; ac_rfl
  unfold TripleResidualIsometry at *
  rw [hs,hs']
  obtain ⟨e,he,hL,hM,hN⟩ := h
  exact ⟨e,he,hM,hN,hL⟩

private instance certificate_instance_0175 : OAI.SidorenkoCounterexample.ProofCertificate_0175 := by
  constructor
  intro c0 c1 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18
  exact @certificate_proof_0175 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18

end ClassificationPredicates
section ResidualClassificationStep
variable {K E F : Type} [Field K]
  [AddCommGroup E] [Module K E] [AddCommGroup F] [Module K F]
  [FiniteDimensional K E] [FiniteDimensional K F]
theorem certificate_proof_0176
    (ω : LinearMap.BilinForm K E) (η : LinearMap.BilinForm K F)
    (ha : ω.IsAlt) (hb : η.IsAlt)
    (L M N : Submodule K E) (L' M' N' : Submodule K F)
    (hL : ω.orthogonal L = L) (hM : ω.orthogonal M = M) (hN : ω.orthogonal N = N)
    (hL' : η.orthogonal L' = L') (hM' : η.orthogonal M' = M') (hN' : η.orthogonal N' = N')
    (hzero : (L ⊓ M) ⊓ N = ⊥) (hzero' : (L' ⊓ M') ⊓ N' = ⊥)
    (h : TripleResidualIsometry ω η ha hb L M N L' M' N') :
    TripleResidualIsometry (symplecticReductionForm ω (L ⊓ M) ha)
      (symplecticReductionForm η (L' ⊓ M') hb)
      (symplecticReductionForm_alt ω (L ⊓ M) ha)
      (symplecticReductionForm_alt η (L' ⊓ M') hb)
      (reduceSubspace ω (L ⊓ M) L) (reduceSubspace ω (L ⊓ M) M)
      (reduceSubspace ω (L ⊓ M) N) (reduceSubspace η (L' ⊓ M') L')
      (reduceSubspace η (L' ⊓ M') M') (reduceSubspace η (L' ⊓ M') N') := by
  have hs := (triple_pair_reduction_intersections ω L M N hL hM hzero).2.2.2.2.2
  have hs' := (triple_pair_reduction_intersections η L' M' N' hL' hM' hzero').2.2.2.2.2

  unfold TripleResidualIsometry
  rw [hs,hs']
  obtain ⟨u,hu,huA⟩ := exists_reduction_in_stages ω ha (L ⊓ M) (triplePairSum L M N)
    (le_sup_left.trans le_sup_left) (triplePairSum_isotropic ω L M N hL hM hN)
  obtain ⟨v,hv,hvA⟩ := exists_reduction_in_stages η hb (L' ⊓ M') (triplePairSum L' M' N')
    (le_sup_left.trans le_sup_left) (triplePairSum_isotropic η L' M' N' hL' hM' hN')
  obtain ⟨r,hr,hrL,hrM,hrN⟩ := h
  let e := u.symm.trans (r.trans v)
  refine ⟨e,?_,?_,?_,?_⟩
  · intro x y
    change symplecticReductionForm (symplecticReductionForm η (L' ⊓ M') hb)
      (reduceSubspace η (L' ⊓ M') (triplePairSum L' M' N'))
      (symplecticReductionForm_alt η (L' ⊓ M') hb)
      (v (r (u.symm x))) (v (r (u.symm y))) = _
    rw [hv,hr,←hu,u.apply_symm_apply,u.apply_symm_apply]
  · rw [←huA L,←hvA L',map_conjugate_equiv,hrL]
  · rw [←huA M,←hvA M',map_conjugate_equiv,hrM]
  · rw [←huA N,←hvA N',map_conjugate_equiv,hrN]

private instance certificate_instance_0176 : OAI.SidorenkoCounterexample.ProofCertificate_0176 := by
  constructor
  intro c0 c1 c2 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19 q20 q21 q22 q23 q24 q25 q26 q27 q28
  exact @certificate_proof_0176 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19 q20 q21 q22 q23 q24 q25 q26 q27 q28

theorem certificate_proof_0177
    (ω : LinearMap.BilinForm K E) (η : LinearMap.BilinForm K F)
    (ha : ω.IsAlt) (hb : η.IsAlt)
    (L M N : Submodule K E) (L' M' N' : Submodule K F)
    (hL : ω.orthogonal L = L) (hM : ω.orthogonal M = M) (hN : ω.orthogonal N = N)
    (hL' : η.orthogonal L' = L') (hM' : η.orthogonal M' = M') (hN' : η.orthogonal N' = N')
    (hLM : L ⊓ M = ⊥) (hLN : L ⊓ N = ⊥) (hMN : M ⊓ N = ⊥)
    (hLM' : L' ⊓ M' = ⊥) (hLN' : L' ⊓ N' = ⊥) (hMN' : M' ⊓ N' = ⊥)
    (h : TripleResidualIsometry ω η ha hb L M N L' M' N') :
    TripleIsometry ω η L M N L' M' N' := by
  have hs : triplePairSum L M N = L ⊓ M := by simp [triplePairSum,hLM,hLN,hMN]
  have hs' : triplePairSum L' M' N' = L' ⊓ M' := by simp [triplePairSum,hLM',hLN',hMN']
  unfold TripleResidualIsometry at h
  rw [hs,hs'] at h
  obtain ⟨r,hr,hrL,hrM,hrN⟩ := h
  exact triple_one_block_lift ω η ha hb L M N L' M' N' hL hM hN hL' hM' hN'
    (by rw [hLM,bot_inf_eq]) (by rw [hLM',bot_inf_eq]) (by rw [hLM,hLM']; simp)
    r hr hrL hrM hrN

private instance certificate_instance_0177 : OAI.SidorenkoCounterexample.ProofCertificate_0177 := by
  constructor
  intro c0 c1 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19 q20 q21 q22 q23 q24 q25 q26 q27 q28 q29 q30 q31 q32
  exact @certificate_proof_0177 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19 q20 q21 q22 q23 q24 q25 q26 q27 q28 q29 q30 q31 q32

end ResidualClassificationStep
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
section FullClassification
variable {K E F : Type} [Field K]
  [AddCommGroup E] [Module K E] [AddCommGroup F] [Module K F]
  [FiniteDimensional K E] [FiniteDimensional K F]
omit [FiniteDimensional K E] in
theorem certificate_proof_0178 (ω : LinearMap.BilinForm K E) (S : Submodule K E) :
    reduceSubspace ω S ⊥ = ⊥ := by
  unfold reduceSubspace
  simp

private instance certificate_instance_0178 : OAI.SidorenkoCounterexample.ProofCertificate_0178 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6
  exact @certificate_proof_0178 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 q0 q1 q2 q3 q4 q5 q6

theorem certificate_proof_0179
    (ω : LinearMap.BilinForm K E) (η : LinearMap.BilinForm K F)
    (ha : ω.IsAlt) (hb : η.IsAlt) (hω : ω.Nondegenerate) (hη : η.Nondegenerate)
    (L M N : Submodule K E) (L' M' N' : Submodule K F)
    (hL : ω.orthogonal L = L) (hM : ω.orthogonal M = M) (hN : ω.orthogonal N = N)
    (hL' : η.orthogonal L' = L') (hM' : η.orthogonal M' = M') (hN' : η.orthogonal N' = N')
    (hLM : L ⊓ M = ⊥) (hLN : L ⊓ N = ⊥)
    (hLM' : L' ⊓ M' = ⊥) (hLN' : L' ⊓ N' = ⊥)
    (hdim : finrank K ↥(M ⊓ N) = finrank K ↥(M' ⊓ N'))
    (h : TripleResidualIsometry ω η ha hb L M N L' M' N') :
    TripleIsometry ω η L M N L' M' N' := by
  have hz : (M ⊓ N) ⊓ L = ⊥ := by
    calc
      _ = (L ⊓ M) ⊓ N := by ac_rfl
      _ = ⊥ := by rw [hLM,bot_inf_eq]
  have hz' : (M' ⊓ N') ⊓ L' = ⊥ := by
    calc
      _ = (L' ⊓ M') ⊓ N' := by ac_rfl
      _ = ⊥ := by rw [hLM',bot_inf_eq]
  have hS : M ⊓ N ≤ ω.orthogonal (M ⊓ N) := by
    intro x hx y hy
    exact hM.ge hx.1 y hy.1
  have hS' : M' ⊓ N' ≤ η.orthogonal (M' ⊓ N') := by
    intro x hx y hy
    exact hM'.ge hx.1 y hy.1
  let α := symplecticReductionForm ω (M ⊓ N) ha
  let β := symplecticReductionForm η (M' ⊓ N') hb
  have ha' := symplecticReductionForm_alt ω (M ⊓ N) ha
  have hb' := symplecticReductionForm_alt η (M' ⊓ N') hb
  have hred := general_lagrangian_reduction ω (M ⊓ N) ha hω hS
  have hred' := general_lagrangian_reduction η (M' ⊓ N') hb hη hS'
  obtain ⟨hpq,hpr,hqr,_hd1,_hd2,_hs⟩ :=
    triple_pair_reduction_intersections ω M N L hM hN hz
  obtain ⟨hpq',hpr',hqr',_hd1',_hd2',_hs'⟩ :=
    triple_pair_reduction_intersections η M' N' L' hM' hN' hz'
  have hh := triple_residual_isometry_reduce_pair ω η ha hb M N L M' N' L'
    hM hN hL hM' hN' hL' hz hz' h.rotate
  obtain ⟨r,hr,hrM,hrN,hrL⟩ := triple_isometry_of_zero_pairs α β ha' hb'
    _ _ _ _ _ _ (hred M hM) (hred N hN) (hred L hL)
    (hred' M' hM') (hred' N' hN') (hred' L' hL') hpq
    (by rw [hpr,inf_comm M L,hLM,reduceSubspace_bot])
    (by rw [hqr,inf_comm N L,hLN,reduceSubspace_bot]) hpq'
    (by rw [hpr',inf_comm M' L',hLM',reduceSubspace_bot])
    (by rw [hqr',inf_comm N' L',hLN',reduceSubspace_bot]) hh
  obtain ⟨e,he,heM,heN,heL⟩ := triple_one_block_lift ω η ha hb M N L M' N' L'
    hM hN hL hM' hN' hL' hz hz' hdim r hr hrM hrN hrL
  exact ⟨e,he,heL,heM,heN⟩

private instance certificate_instance_0179 : OAI.SidorenkoCounterexample.ProofCertificate_0179 := by
  constructor
  intro c0 c1 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19 q20 q21 q22 q23 q24 q25 q26 q27 q28 q29 q30 q31 q32 q33
  exact @certificate_proof_0179 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19 q20 q21 q22 q23 q24 q25 q26 q27 q28 q29 q30 q31 q32 q33

theorem certificate_proof_0180
    (ω : LinearMap.BilinForm K E) (η : LinearMap.BilinForm K F)
    (ha : ω.IsAlt) (hb : η.IsAlt) (hω : ω.Nondegenerate) (hη : η.Nondegenerate)
    (L M N : Submodule K E) (L' M' N' : Submodule K F)
    (hL : ω.orthogonal L = L) (hM : ω.orthogonal M = M) (hN : ω.orthogonal N = N)
    (hL' : η.orthogonal L' = L') (hM' : η.orthogonal M' = M') (hN' : η.orthogonal N' = N')
    (hLM : L ⊓ M = ⊥) (hLM' : L' ⊓ M' = ⊥)
    (hdimLN : finrank K ↥(L ⊓ N) = finrank K ↥(L' ⊓ N'))
    (hdimMN : finrank K ↥(M ⊓ N) = finrank K ↥(M' ⊓ N'))
    (h : TripleResidualIsometry ω η ha hb L M N L' M' N') :
    TripleIsometry ω η L M N L' M' N' := by
  have hz : (L ⊓ N) ⊓ M = ⊥ := by
    calc
      _ = (L ⊓ M) ⊓ N := by ac_rfl
      _ = ⊥ := by rw [hLM,bot_inf_eq]
  have hz' : (L' ⊓ N') ⊓ M' = ⊥ := by
    calc
      _ = (L' ⊓ M') ⊓ N' := by ac_rfl
      _ = ⊥ := by rw [hLM',bot_inf_eq]
  have hS : L ⊓ N ≤ ω.orthogonal (L ⊓ N) := by
    intro x hx y hy
    exact hL.ge hx.1 y hy.1
  have hS' : L' ⊓ N' ≤ η.orthogonal (L' ⊓ N') := by
    intro x hx y hy
    exact hL'.ge hx.1 y hy.1
  let α := symplecticReductionForm ω (L ⊓ N) ha
  let β := symplecticReductionForm η (L' ⊓ N') hb
  have ha' := symplecticReductionForm_alt ω (L ⊓ N) ha
  have hb' := symplecticReductionForm_alt η (L' ⊓ N') hb
  have hω' := symplecticReductionForm_nondegenerate ω (L ⊓ N) ha hω
  have hη' := symplecticReductionForm_nondegenerate η (L' ⊓ N') hb hη
  have hred := general_lagrangian_reduction ω (L ⊓ N) ha hω hS
  have hred' := general_lagrangian_reduction η (L' ⊓ N') hb hη hS'
  obtain ⟨hpq,hpr,_hqr,_hd1,hd2,_hs⟩ :=
    triple_pair_reduction_intersections ω L N M hL hN hz
  obtain ⟨hpq',hpr',_hqr',_hd1',hd2',_hs'⟩ :=
    triple_pair_reduction_intersections η L' N' M' hL' hN' hz'
  have hh := triple_residual_isometry_reduce_pair ω η ha hb L N M L' N' M'
    hL hN hM hL' hN' hM' hz hz' h.swap_right
  obtain ⟨r,hr,hrL,hrN,hrM⟩ := triple_isometry_of_two_zero_pairs α β ha' hb' hω' hη'
    _ _ _ _ _ _ (hred L hL) (hred N hN) (hred M hM)
    (hred' L' hL') (hred' N' hN') (hred' M' hM') hpq
    (by rw [hpr,hLM,reduceSubspace_bot]) hpq'
    (by rw [hpr',hLM',reduceSubspace_bot])
    (by rw [hd2,hd2',inf_comm N M,inf_comm N' M']; exact hdimMN) hh
  obtain ⟨e,he,heL,heN,heM⟩ := triple_one_block_lift ω η ha hb L N M L' N' M'
    hL hN hM hL' hN' hM' hz hz' hdimLN r hr hrL hrN hrM
  exact ⟨e,he,heL,heM,heN⟩

private instance certificate_instance_0180 : OAI.SidorenkoCounterexample.ProofCertificate_0180 := by
  constructor
  intro c0 c1 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19 q20 q21 q22 q23 q24 q25 q26 q27 q28 q29 q30 q31 q32
  exact @certificate_proof_0180 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19 q20 q21 q22 q23 q24 q25 q26 q27 q28 q29 q30 q31 q32

theorem certificate_proof_0181
    (ω : LinearMap.BilinForm K E) (η : LinearMap.BilinForm K F)
    (ha : ω.IsAlt) (hb : η.IsAlt) (hω : ω.Nondegenerate) (hη : η.Nondegenerate)
    (L M N : Submodule K E) (L' M' N' : Submodule K F)
    (hL : ω.orthogonal L = L) (hM : ω.orthogonal M = M) (hN : ω.orthogonal N = N)
    (hL' : η.orthogonal L' = L') (hM' : η.orthogonal M' = M') (hN' : η.orthogonal N' = N')
    (hzero : (L ⊓ M) ⊓ N = ⊥) (hzero' : (L' ⊓ M') ⊓ N' = ⊥)
    (hdimLM : finrank K ↥(L ⊓ M) = finrank K ↥(L' ⊓ M'))
    (hdimLN : finrank K ↥(L ⊓ N) = finrank K ↥(L' ⊓ N'))
    (hdimMN : finrank K ↥(M ⊓ N) = finrank K ↥(M' ⊓ N'))
    (h : TripleResidualIsometry ω η ha hb L M N L' M' N') :
    TripleIsometry ω η L M N L' M' N' := by
  have hS : L ⊓ M ≤ ω.orthogonal (L ⊓ M) := by
    intro x hx y hy
    exact hL.ge hx.1 y hy.1
  have hS' : L' ⊓ M' ≤ η.orthogonal (L' ⊓ M') := by
    intro x hx y hy
    exact hL'.ge hx.1 y hy.1
  let α := symplecticReductionForm ω (L ⊓ M) ha
  let β := symplecticReductionForm η (L' ⊓ M') hb
  have ha' := symplecticReductionForm_alt ω (L ⊓ M) ha
  have hb' := symplecticReductionForm_alt η (L' ⊓ M') hb
  have hω' := symplecticReductionForm_nondegenerate ω (L ⊓ M) ha hω
  have hη' := symplecticReductionForm_nondegenerate η (L' ⊓ M') hb hη
  have hred := general_lagrangian_reduction ω (L ⊓ M) ha hω hS
  have hred' := general_lagrangian_reduction η (L' ⊓ M') hb hη hS'
  obtain ⟨hpq,_hpr,_hqr,hd1,hd2,_hs⟩ :=
    triple_pair_reduction_intersections ω L M N hL hM hzero
  obtain ⟨hpq',_hpr',_hqr',hd1',hd2',_hs'⟩ :=
    triple_pair_reduction_intersections η L' M' N' hL' hM' hzero'
  have hh := triple_residual_isometry_reduce_pair ω η ha hb L M N L' M' N'
    hL hM hN hL' hM' hN' hzero hzero' h
  obtain ⟨r,hr,hrL,hrM,hrN⟩ := triple_isometry_of_one_zero_pair α β ha' hb' hω' hη'
    _ _ _ _ _ _ (hred L hL) (hred M hM) (hred N hN)
    (hred' L' hL') (hred' M' hM') (hred' N' hN') hpq hpq'
    (by rw [hd1,hd1']; exact hdimLN) (by rw [hd2,hd2']; exact hdimMN) hh
  exact triple_one_block_lift ω η ha hb L M N L' M' N' hL hM hN hL' hM' hN'
    hzero hzero' hdimLM r hr hrL hrM hrN

private instance certificate_instance_0181 : OAI.SidorenkoCounterexample.ProofCertificate_0181 := by
  constructor
  intro c0 c1 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19 q20 q21 q22 q23 q24 q25 q26 q27 q28 q29 q30 q31 q32 q33
  exact @certificate_proof_0181 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19 q20 q21 q22 q23 q24 q25 q26 q27 q28 q29 q30 q31 q32 q33

end FullClassification
end SidorenkoCounterexample
end OAI

theorem solution : OAI.SidorenkoCounterexample.ProofCertificate_0164 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0165 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0166 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0167 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0168 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0169 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0170 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0171 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0172 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0173 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0174 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0175 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0176 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0177 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0178 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0179 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0180 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0181 := by
  exact ⟨inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance⟩
end

