-- Prove2me | solution 1 for OAI.SidorenkoCounterexample.finite_geometry_batch_05
-- status  : ACCEPTED   (prove)
-- author  : @abcdefg
-- created : 2026-10-09T05:27:36.627987+00:00
-- url     : https://prove2.me/submissions/0222c9ad-4c5f-488b-bf39-5613ecbecdcb

import Definitions.Def_SidorenkoFiniteGeometryCertificates04
set_option linter.unusedVariables false
section
variable [p0 : OAI.SidorenkoCounterexample.ProofCertificate_0012]
  [p1 : OAI.SidorenkoCounterexample.ProofCertificate_0014]
  [p2 : OAI.SidorenkoCounterexample.ProofCertificate_0027]
  [p3 : OAI.SidorenkoCounterexample.ProofCertificate_0029]
  [p4 : OAI.SidorenkoCounterexample.ProofCertificate_0030]
  [p5 : OAI.SidorenkoCounterexample.ProofCertificate_0031]
  [p6 : OAI.SidorenkoCounterexample.ProofCertificate_0032]
  [p7 : OAI.SidorenkoCounterexample.ProofCertificate_0107]
  [p8 : OAI.SidorenkoCounterexample.ProofCertificate_0108]
  [p9 : OAI.SidorenkoCounterexample.ProofCertificate_0110]
  [p10 : OAI.SidorenkoCounterexample.ProofCertificate_0111]
  [p11 : OAI.SidorenkoCounterexample.ProofCertificate_0113]
  [p12 : OAI.SidorenkoCounterexample.ProofCertificate_0119]
  [p13 : OAI.SidorenkoCounterexample.ProofCertificate_0120]
  [p14 : OAI.SidorenkoCounterexample.ProofCertificate_0121]
  [p15 : OAI.SidorenkoCounterexample.ProofCertificate_0122]
  [p16 : OAI.SidorenkoCounterexample.ProofCertificate_0125]
  [p17 : OAI.SidorenkoCounterexample.ProofCertificate_0127]
  [p18 : OAI.SidorenkoCounterexample.ProofCertificate_0129]
  [p19 : OAI.SidorenkoCounterexample.ProofCertificate_0130]
include p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19

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
theorem certificate_proof_0131 (ha : ω.IsAlt)
    (hω : ω.Nondegenerate)
    (f : ReducedSpace ω S ≃ₗ[K] ReducedSpace ω S)
    (hf : ∀ x y, symplecticReductionForm ω S ha (f x) (f y) =
      symplecticReductionForm ω S ha x y) :
    ∃ e : E ≃ₗ[K] E,
      (∀ x y, ω (e x) (e y) = ω x y) ∧
      (∀ x : S, e x.val = x.val) ∧
      (∀ x : ω.orthogonal S, e x.val ∈ ω.orthogonal S) ∧
      (∀ x y : ω.orthogonal S, e x.val = y.val →
        (reductionKernel ω S).mkQ y = f ((reductionKernel ω S).mkQ x)) := by
  let π := (reductionKernel ω S).mkQ
  obtain ⟨s,hs⟩ := π.exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.mpr (Submodule.mkQ_surjective _))
  let g : ReducedSpace ω S →ₗ[K] E := (ω.orthogonal S).subtype.comp s
  have hπ (x : ReducedSpace ω S) : π (s x) = x := LinearMap.congr_fun hs x
  have hg (x y : ReducedSpace ω S) : ω (g x) (g y) =
      symplecticReductionForm ω S ha x y :=
    reduction_section_isometry ω S ha s hs x y
  have hginj : Function.Injective g := by
    intro x y h
    have h' : s x = s y := Subtype.ext h
    simpa only [hπ] using congrArg π h'
  let U := g.range
  let j : ReducedSpace ω S ≃ₗ[K] U := LinearEquiv.ofInjective g hginj
  have hj (x : ReducedSpace ω S) : (j x).val = g x := rfl
  have hUn : (ω.restrict U).Nondegenerate := by
    have hn := symplecticReductionForm_nondegenerate ω S ha hω
    have left (x : U) (hx : ∀ y : U, ω x.val y.val = 0) : x = 0 := by
      obtain ⟨x,rfl⟩ := j.surjective x
      have hx0 : x = 0 := hn.1 x (fun y => by
        rw [← hg]
        exact hx (j y))
      simp [hx0]
    refine ⟨left, ?_⟩
    intro x hx
    apply left
    intro y
    exact ha.isRefl _ _ (hx y)
  let fU := j.symm.trans (f.trans j)
  have hfU (x y : U) : ω (fU x).val (fU y).val = ω x.val y.val := by
    obtain ⟨x,rfl⟩ := j.surjective x
    obtain ⟨y,rfl⟩ := j.surjective y
    change ω (j (f (j.symm (j x)))).val (j (f (j.symm (j y)))).val = ω (j x).val (j y).val
    simp only [j.symm_apply_apply,hj,hg,hf]
  obtain ⟨e,he,heU,heO⟩ := exists_orthogonal_extension ω ha U hUn fU hfU
  have hSO : S ≤ ω.orthogonal U := by
    intro x hx y hy
    obtain ⟨z,rfl⟩ := hy
    exact ha.isRefl _ _ ((s z).property x hx)
  have heS (x : S) : e x.val = x.val := heO ⟨x.val,hSO x.property⟩
  have heP (x : ω.orthogonal S) : e x.val ∈ ω.orthogonal S := by
    intro y hy
    have hyfix : e y = y := heS ⟨y,hy⟩
    rw [← hyfix,he]
    exact x.property y hy
  refine ⟨e,he,heS,heP,?_⟩
  intro x y hxy
  apply sub_eq_zero.mp
  apply (symplecticReductionForm_nondegenerate ω S ha hω).1
  intro z
  have hpair (a : ω.orthogonal S) (b : ReducedSpace ω S) :
      symplecticReductionForm ω S ha (π a) b = ω a.val (g b) := by
    calc
      _ = symplecticReductionForm ω S ha (π a) (π (s b)) := by rw [hπ]
      _ = _ := rfl
  have hegj (z : ReducedSpace ω S) : e (g z) = g (f z) := by
    have h := heU (j z)
    simpa only [fU,LinearEquiv.trans_apply,j.symm_apply_apply,hj] using h
  change symplecticReductionForm ω S ha (π y - f (π x)) z = 0
  rw [map_sub,LinearMap.sub_apply,sub_eq_zero]
  rw [hpair]
  calc
    ω y.val (g z) = ω (e x.val) (e (g (f.symm z))) := by
      rw [hxy,hegj,f.apply_symm_apply]
    _ = ω x.val (g (f.symm z)) := he _ _
    _ = symplecticReductionForm ω S ha (π x) (f.symm z) := (hpair x _).symm
    _ = symplecticReductionForm ω S ha (f (π x)) z := by
      simpa only [f.apply_symm_apply] using (hf (π x) (f.symm z)).symm

private instance certificate_instance_0131 : OAI.SidorenkoCounterexample.ProofCertificate_0131 := by
  constructor
  intro c0 c1 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11
  exact @certificate_proof_0131 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11

end QuotientExtension
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
theorem certificate_proof_0132 {A B : Type} [Finite A] [Finite B]
    (f : A → B) (b : B)
    (h : ∀ c : B, Nonempty ({a : A // f a = b} ≃ {a : A // f a = c})) :
    Nat.card {a : A // f a = b} * Nat.card B = Nat.card A := by
  classical
  let := Fintype.ofFinite A
  let := Fintype.ofFinite B
  have hc (c : B) : Nat.card {a : A // f a = c} = Nat.card {a : A // f a = b} :=
    (Nat.card_congr (h c).some).symm
  calc
    _ = ∑ c : B, Nat.card {a : A // f a = c} := by
      simp only [hc,Finset.sum_const,Finset.card_univ,smul_eq_mul,Nat.card_eq_fintype_card]
      exact Nat.mul_comm _ _
    _ = Nat.card (Σ c : B, {a : A // f a = c}) := by
      simp only [Nat.card_eq_fintype_card,Fintype.card_sigma]
    _ = Nat.card A := Nat.card_congr (Equiv.sigmaFiberEquiv f)

private instance certificate_instance_0132 : OAI.SidorenkoCounterexample.ProofCertificate_0132 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6
  exact @certificate_proof_0132 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 q0 q1 q2 q3 q4 q5 q6

section ReductionLaws
variable {K E : Type} [Field K] [AddCommGroup E] [Module K E]
variable (ω : LinearMap.BilinForm K E) (S : Submodule K E)
theorem certificate_proof_0133 (e : E ≃ₗ[K] E)
    (f : ReducedSpace ω S ≃ₗ[K] ReducedSpace ω S)
    (hP : (ω.orthogonal S).map e.toLinearMap = ω.orthogonal S)
    (hQ : ∀ x y : ω.orthogonal S, e x.val = y.val →
      (reductionKernel ω S).mkQ y = f ((reductionKernel ω S).mkQ x))
    (L : Submodule K E) :
    reduceSubspace ω S (L.map e.toLinearMap) =
      (reduceSubspace ω S L).map f.toLinearMap := by
  ext z
  constructor
  · rintro ⟨y,⟨x,hx,hxy⟩,rfl⟩
    have hxP : x ∈ ω.orthogonal S := by
      have hyP : y.val ∈ (ω.orthogonal S).map e.toLinearMap := hP.symm ▸ y.property
      obtain ⟨x',hx',hx'y⟩ := hyP
      have heq : x' = x := e.injective (hx'y.trans hxy.symm)
      exact heq ▸ hx'
    refine ⟨(reductionKernel ω S).mkQ ⟨x,hxP⟩,⟨⟨x,hxP⟩,hx,rfl⟩,?_⟩
    exact (hQ ⟨x,hxP⟩ y hxy).symm
  · rintro ⟨w,⟨x,hx,rfl⟩,rfl⟩
    have hyP : e x.val ∈ ω.orthogonal S := hP.le ⟨x.val,x.property,rfl⟩
    refine ⟨⟨e x.val,hyP⟩,⟨x.val,hx,rfl⟩,?_⟩
    exact hQ x ⟨e x.val,hyP⟩ rfl

private instance certificate_instance_0133 : OAI.SidorenkoCounterexample.ProofCertificate_0133 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11
  exact @certificate_proof_0133 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11

theorem certificate_proof_0134 (e : E ≃ₗ[K] E) (U : Submodule K E)
    (h : ∀ x : U, e x.val = x.val) : U.map e.toLinearMap = U := by
  ext x
  constructor
  · rintro ⟨y,hy,rfl⟩
    change e y ∈ U
    rw [h ⟨y,hy⟩]
    exact hy
  · intro hx
    exact ⟨x,hx,h ⟨x,hx⟩⟩

private instance certificate_instance_0134 : OAI.SidorenkoCounterexample.ProofCertificate_0134 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7
  exact @certificate_proof_0134 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 q0 q1 q2 q3 q4 q5 q6 q7

variable [FiniteDimensional K E]
theorem certificate_proof_0135 (h2 : (2 : K) ≠ 0) (ha : ω.IsAlt)
    (hω : ω.Nondegenerate) (hS : S ≤ ω.orthogonal S)
    (A : Submodule K E) (hAS : A ≤ S)
    (T U : {T : Submodule K (ReducedSpace ω S) //
      (symplecticReductionForm ω S ha).orthogonal T = T}) :
    Nonempty ({L : AvoidanceSpace ω S A // avoidanceReduction ω S ha hω hS A L = T} ≃
      {L : AvoidanceSpace ω S A // avoidanceReduction ω S ha hω hS A L = U}) := by
  let B := symplecticReductionForm ω S ha
  obtain ⟨f,hf,hTU⟩ := lagrangian_transitivity B T.val h2
    (symplecticReductionForm_alt ω S ha)
    (symplecticReductionForm_nondegenerate ω S ha hω) T.property U.val U.property
  obtain ⟨e,he,heS,_,heQ⟩ := exists_reduction_isometry_extension ω S ha hω f hf
  let a := avoidanceIsometryEquiv ω S A hAS e he heS
  have hPm : (ω.orthogonal S).map e.toLinearMap = ω.orthogonal S := by
    rw [← orthogonal_map_of_isometry ω e he,subspace_map_eq_of_fixed e S heS]
  have hred (L : AvoidanceSpace ω S A) :
      (avoidanceReduction ω S ha hω hS A (a L)).val =
        (avoidanceReduction ω S ha hω hS A L).val.map f.toLinearMap :=
    reduceSubspace_map ω S e f hPm heQ L.val
  refine ⟨a.subtypeEquiv ?_⟩
  intro L
  constructor
  · intro hL
    apply Subtype.ext
    rw [hred,hL]
    exact hTU
  · intro hL
    apply Subtype.ext
    apply (Submodule.orderIsoMapComap f).injective
    change (avoidanceReduction ω S ha hω hS A L).val.map f.toLinearMap = T.val.map f.toLinearMap
    rw [← hred,hL,hTU]

private instance certificate_instance_0135 : OAI.SidorenkoCounterexample.ProofCertificate_0135 := by
  constructor
  intro c0 c1 c2 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15
  exact @certificate_proof_0135 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15

variable [Finite E]
theorem certificate_proof_0136 (h2 : (2 : K) ≠ 0) (ha : ω.IsAlt)
    (hω : ω.Nondegenerate) (hS : S ≤ ω.orthogonal S)
    (A : Submodule K E) (hAS : A ≤ S)
    (T : {T : Submodule K (ReducedSpace ω S) //
      (symplecticReductionForm ω S ha).orthogonal T = T}) :
    Nat.card {L : AvoidanceSpace ω S A // avoidanceReduction ω S ha hω hS A L = T} *
      Nat.card {U : Submodule K (ReducedSpace ω S) //
        (symplecticReductionForm ω S ha).orthogonal U = U} =
        Nat.card (AvoidanceSpace ω S A) := by
  classical
  let := Fintype.ofFinite E
  let := Fintype.ofFinite (ω.orthogonal S)
  exact equal_fiber_card_identity (avoidanceReduction ω S ha hω hS A) T
    (avoidanceReduction_fiber_equiv ω S h2 ha hω hS A hAS T)

private instance certificate_instance_0136 : OAI.SidorenkoCounterexample.ProofCertificate_0136 := by
  constructor
  intro c0 c1 c2 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15
  exact @certificate_proof_0136 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15

end ReductionLaws
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
theorem certificate_proof_0137
    {K E F : Type} [Field K] [AddCommGroup E] [Module K E]
    [AddCommGroup F] [Module K F] [FiniteDimensional K E] [FiniteDimensional K F]
    (U : Submodule K E) (W : Submodule K F)
    (hEF : finrank K E = finrank K F) (f : U ≃ₗ[K] W) :
    ∃ e : E ≃ₗ[K] F, ∀ u : U, e u.val = (f u).val := by
  obtain ⟨U',hU⟩ := U.exists_isCompl
  obtain ⟨W',hW⟩ := W.exists_isCompl
  let cU := Submodule.prodEquivOfIsCompl U U' hU
  let cW := Submodule.prodEquivOfIsCompl W W' hW
  have hdim : finrank K U' = finrank K W' := by
    have h1 := Submodule.finrank_add_eq_of_isCompl hU
    have h2 := Submodule.finrank_add_eq_of_isCompl hW
    have h3 := f.finrank_eq
    omega
  let g : U' ≃ₗ[K] W' := LinearEquiv.ofFinrankEq U' W' hdim
  let e := cU.symm.trans ((f.prodCongr g).trans cW)
  refine ⟨e, ?_⟩
  intro u
  have hu : cU (u,0) = u.val := by simp [cU]
  change cW ((f.prodCongr g) (cU.symm u.val)) = (f u).val
  rw [← hu, cU.symm_apply_apply]
  simp [cW]

private instance certificate_instance_0137 : OAI.SidorenkoCounterexample.ProofCertificate_0137 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13
  exact @certificate_proof_0137 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13

theorem certificate_proof_0138
    {K E F : Type} [Field K] [AddCommGroup E] [Module K E]
    [AddCommGroup F] [Module K F] [FiniteDimensional K E] [FiniteDimensional K F]
    (U : Submodule K E) (W : Submodule K F)
    (hEF : finrank K E = finrank K F) (hUW : finrank K U = finrank K W) :
    ∃ e : E ≃ₗ[K] F, U.map e.toLinearMap = W := by
  let f : U ≃ₗ[K] W := LinearEquiv.ofFinrankEq U W hUW
  obtain ⟨e,he⟩ := exists_linearEquiv_extension U W hEF f
  refine ⟨e, ?_⟩
  ext x
  constructor
  · rintro ⟨y,hy,rfl⟩
    change e y ∈ W
    rw [he ⟨y,hy⟩]
    exact (f ⟨y,hy⟩).property
  · intro hx
    let u := f.symm ⟨x,hx⟩
    refine ⟨u.val,u.property, ?_⟩
    change e u.val = x
    rw [he]
    exact congrArg Subtype.val (f.apply_symm_apply ⟨x,hx⟩)

private instance certificate_instance_0138 : OAI.SidorenkoCounterexample.ProofCertificate_0138 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13
  exact @certificate_proof_0138 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13

end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
section IsotropicTransitivity
variable {K E : Type} [Field K] [AddCommGroup E] [Module K E]
  [FiniteDimensional K E] [Finite E]
variable (ω : LinearMap.BilinForm K E)
theorem certificate_proof_0139 (h2 : (2 : K) ≠ 0) (ha : ω.IsAlt)
    (hω : ω.Nondegenerate) (S T : Submodule K E)
    (hS : S ≤ ω.orthogonal S) (hT : T ≤ ω.orthogonal T)
    (hST : finrank K S = finrank K T) :
    ∃ e : E ≃ₗ[K] E, (∀ x y, ω (e x) (e y) = ω x y) ∧ S.map e.toLinearMap = T := by
  obtain ⟨L,hSL,hL⟩ := exists_containing_lagrangian ω ha S hS
  obtain ⟨M,hTM,hM⟩ := exists_containing_lagrangian ω ha T hT
  obtain ⟨eL,hEL,hωL⟩ := exists_lagrangian_coordinates ω L h2 ha hω hL
  obtain ⟨eM,hEM,hωM⟩ := exists_lagrangian_coordinates ω M h2 ha hω hM
  have hdim : finrank K L = finrank K M := by
    have h1 := self_orthogonal_twice_finrank ω L hω hL
    have h2 := self_orthogonal_twice_finrank ω M hω hM
    omega
  let U := S.comap L.subtype
  let W := T.comap M.subtype
  have hUW : finrank K U = finrank K W := by
    exact (Submodule.comapSubtypeEquivOfLe hSL).finrank_eq.trans
      (hST.trans (Submodule.comapSubtypeEquivOfLe hTM).finrank_eq.symm)
  obtain ⟨f,hf⟩ := subspace_transitivity U W hdim hUW
  let c : (L × Module.Dual K L) ≃ₗ[K] (M × Module.Dual K M) :=
    f.prodCongr f.symm.dualMap
  have hc (x y : L × Module.Dual K L) :
      canonicalSymplectic (c x) (c y) = canonicalSymplectic x y := by
    simp [c,canonicalSymplectic_apply]
  let e := eL.symm.trans (c.trans eM)
  have he (l : L) : e l.val = (f l).val := by
    change eM (c (eL.symm l.val)) = (f l).val
    rw [← hEL l, eL.symm_apply_apply]
    simpa [c] using hEM (f l)
  refine ⟨e, ?_, ?_⟩
  · intro x y
    change ω (eM (c (eL.symm x))) (eM (c (eL.symm y))) = ω x y
    rw [hωM, hc, ← hωL, eL.apply_symm_apply, eL.apply_symm_apply]
  · ext x
    constructor
    · rintro ⟨y,hy,rfl⟩
      change e y ∈ T
      rw [he ⟨y,hSL hy⟩]
      have hfu : f ⟨y,hSL hy⟩ ∈ U.map f.toLinearMap := ⟨⟨y,hSL hy⟩,hy,rfl⟩
      exact hf.le hfu
    · intro hx
      have hw : (⟨x,hTM hx⟩ : M) ∈ W := hx
      obtain ⟨l,hl,hel⟩ := hf.ge hw
      refine ⟨l.val,hl, ?_⟩
      change e l.val = x
      rw [he]
      exact congrArg Subtype.val hel

private instance certificate_instance_0139 : OAI.SidorenkoCounterexample.ProofCertificate_0139 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15
  exact @certificate_proof_0139 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15

end IsotropicTransitivity
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
section TransversePairs
variable {K E : Type} [Field K] [AddCommGroup E] [Module K E]
  [FiniteDimensional K E]
variable (ω : LinearMap.BilinForm K E)
theorem certificate_proof_0140 (hω : ω.Nondegenerate)
    (L M : Submodule K E) (hL : ω.orthogonal L = L) (hM : ω.orthogonal M = M)
    (hLM : L ⊓ M = ⊥) : IsCompl L M := by
  have h1 := self_orthogonal_twice_finrank ω L hω hL
  have h2 := self_orthogonal_twice_finrank ω M hω hM
  apply (Submodule.isCompl_iff_disjoint L M (by omega)).mpr
  exact disjoint_iff.mpr hLM

private instance certificate_instance_0140 : OAI.SidorenkoCounterexample.ProofCertificate_0140 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12
  exact @certificate_proof_0140 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12

theorem certificate_proof_0141 (ha : ω.IsAlt) (hω : ω.Nondegenerate)
    (L M : Submodule K E) (hL : ω.orthogonal L = L) (hM : ω.orthogonal M = M)
    (hLM : L ⊓ M = ⊥) :
    ∃ e : (L × Module.Dual K L) ≃ₗ[K] E,
      (∀ x, e x ∈ L ↔ x.2 = 0) ∧ (∀ x, e x ∈ M ↔ x.1 = 0) ∧
      ∀ x y, ω (e x) (e y) = canonicalSymplectic x y := by
  let p := (symplecticProjection ω L).comp M.subtype
  have hp : Function.Injective p := by
    apply (LinearMap.ker_eq_bot).mp
    apply (Submodule.eq_bot_iff _).mpr
    intro m hm
    apply Subtype.ext
    have hml : m.val ∈ L := (symplecticProjection_ker ω L hL).le hm
    have hz : m.val ∈ L ⊓ M := ⟨hml,m.property⟩
    change m.val = 0
    simpa only [hLM,Submodule.mem_bot] using hz
  have hd : finrank K M = finrank K (Module.Dual K L) := by
    rw [Subspace.dual_finrank_eq]
    have h1 := self_orthogonal_twice_finrank ω L hω hL
    have h2 := self_orthogonal_twice_finrank ω M hω hM
    omega
  let f : M ≃ₗ[K] Module.Dual K L := LinearEquiv.ofBijective p
    ⟨hp,(LinearMap.injective_iff_surjective_of_finrank_eq_finrank hd).mp hp⟩
  let d := Submodule.prodEquivOfIsCompl L M (transverse_isCompl ω hω L M hL hM hLM)
  let e := ((LinearEquiv.refl K L).prodCongr f.symm).trans d
  have he (x : L × Module.Dual K L) : e x = x.1.val + (f.symm x.2).val := rfl
  have hproj (x : L × Module.Dual K L) : symplecticProjection ω L (e x) = x.2 := by
    rw [he,map_add]
    have hl : symplecticProjection ω L x.1.val = 0 :=
      (symplecticProjection_ker ω L hL).ge x.1.property
    rw [hl,zero_add]
    exact f.apply_symm_apply x.2
  refine ⟨e, ?_, ?_, ?_⟩
  · intro x
    constructor
    · intro hx
      have hz : symplecticProjection ω L (e x) = 0 :=
        (symplecticProjection_ker ω L hL).ge hx
      rwa [hproj] at hz
    · intro hx
      apply (symplecticProjection_ker ω L hL).le
      change symplecticProjection ω L (e x) = 0
      rw [hproj,hx]
  · intro x
    constructor
    · intro hx
      have hv : x.1.val ∈ M := by
        have hh := M.sub_mem hx (f.symm x.2).property
        simpa only [he,add_sub_cancel_right] using hh
      have hz : x.1.val ∈ L ⊓ M := ⟨x.1.property,hv⟩
      apply Subtype.ext
      change x.1.val = 0
      simpa only [hLM,Submodule.mem_bot] using hz
    · intro hx
      rw [he,hx]
      simp
  · intro x y
    have hLL : ω x.1.val y.1.val = 0 := (hL.ge y.1.property) x.1.val x.1.property
    have hMM : ω (f.symm x.2).val (f.symm y.2).val = 0 :=
      (hM.ge (f.symm y.2).property) (f.symm x.2).val (f.symm x.2).property
    have hfg (g : Module.Dual K L) (l : L) : ω l.val (f.symm g).val = g l :=
      LinearMap.congr_fun (f.apply_symm_apply g) l
    rw [he,he]
    simp only [map_add,LinearMap.add_apply,hLL,hMM,
      ← ha.neg_eq y.1.val (f.symm x.2).val,hfg,canonicalSymplectic_apply]
    ring

private instance certificate_instance_0141 : OAI.SidorenkoCounterexample.ProofCertificate_0141 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13
  exact @certificate_proof_0141 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13

end TransversePairs
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
theorem certificate_proof_0142
    {K E F : Type} [Field K] [AddCommGroup E] [Module K E]
    [AddCommGroup F] [Module K F] (e : E ≃ₗ[K] F)
    (U : Submodule K E) (W : Submodule K F)
    (h : ∀ x, e x ∈ W ↔ x ∈ U) : U.map e.toLinearMap = W := by
  ext x
  constructor
  · rintro ⟨y,hy,rfl⟩
    exact (h y).mpr hy
  · intro hx
    refine ⟨e.symm x,(h (e.symm x)).mp ?_,e.apply_symm_apply x⟩
    simpa only [e.apply_symm_apply] using hx

private instance certificate_instance_0142 : OAI.SidorenkoCounterexample.ProofCertificate_0142 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11
  exact @certificate_proof_0142 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11

section PairTransitivity
variable {K E : Type} [Field K] [AddCommGroup E] [Module K E]
  [FiniteDimensional K E]
variable (ω : LinearMap.BilinForm K E)
theorem certificate_proof_0143 (ha : ω.IsAlt) (hω : ω.Nondegenerate)
    (L M L' M' : Submodule K E)
    (hL : ω.orthogonal L = L) (hM : ω.orthogonal M = M)
    (hL' : ω.orthogonal L' = L') (hM' : ω.orthogonal M' = M')
    (hLM : L ⊓ M = ⊥) (hLM' : L' ⊓ M' = ⊥) :
    ∃ e : E ≃ₗ[K] E, (∀ x y, ω (e x) (e y) = ω x y) ∧
      L.map e.toLinearMap = L' ∧ M.map e.toLinearMap = M' := by
  obtain ⟨eL,hEL,hEM,hωL⟩ := exists_transverse_pair_coordinates ω ha hω L M hL hM hLM
  obtain ⟨eM,hEL',hEM',hωM⟩ := exists_transverse_pair_coordinates ω ha hω L' M' hL' hM' hLM'
  have hdim : finrank K L = finrank K L' := by
    have h1 := self_orthogonal_twice_finrank ω L hω hL
    have h2 := self_orthogonal_twice_finrank ω L' hω hL'
    omega
  let f : L ≃ₗ[K] L' := LinearEquiv.ofFinrankEq L L' hdim
  let c : (L × Module.Dual K L) ≃ₗ[K] (L' × Module.Dual K L') :=
    f.prodCongr f.symm.dualMap
  have hc (x y : L × Module.Dual K L) :
      canonicalSymplectic (c x) (c y) = canonicalSymplectic x y := by
    simp [c,canonicalSymplectic_apply]
  let e := eL.symm.trans (c.trans eM)
  refine ⟨e, ?_, ?_, ?_⟩
  · intro x y
    change ω (eM (c (eL.symm x))) (eM (c (eL.symm y))) = ω x y
    rw [hωM, hc, ← hωL, eL.apply_symm_apply, eL.apply_symm_apply]
  · apply subspace_map_eq_of_mem_iff e
    intro x
    change eM (c (eL.symm x)) ∈ L' ↔ x ∈ L
    rw [hEL']
    change f.symm.dualMap ((eL.symm x).2) = 0 ↔ x ∈ L
    rw [LinearEquiv.map_eq_zero_iff]
    simpa only [eL.apply_symm_apply] using (hEL (eL.symm x)).symm
  · apply subspace_map_eq_of_mem_iff e
    intro x
    change eM (c (eL.symm x)) ∈ M' ↔ x ∈ M
    rw [hEM']
    change f ((eL.symm x).1) = 0 ↔ x ∈ M
    rw [LinearEquiv.map_eq_zero_iff]
    simpa only [eL.apply_symm_apply] using (hEM (eL.symm x)).symm

private instance certificate_instance_0143 : OAI.SidorenkoCounterexample.ProofCertificate_0143 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18
  exact @certificate_proof_0143 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18

end PairTransitivity
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
section PairReduction
variable {K E : Type} [Field K] [AddCommGroup E] [Module K E]
variable (ω : LinearMap.BilinForm K E) (S : Submodule K E)
theorem certificate_proof_0144 (T U : Submodule K (ReducedSpace ω S)) :
    liftReduction ω S (T ⊓ U) = liftReduction ω S T ⊓ liftReduction ω S U := by
  ext x
  simp only [mem_liftReduction,Submodule.mem_inf]
  tauto

private instance certificate_instance_0144 : OAI.SidorenkoCounterexample.ProofCertificate_0144 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8
  exact @certificate_proof_0144 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 q0 q1 q2 q3 q4 q5 q6 q7 q8

theorem certificate_proof_0145 (hS : S ≤ ω.orthogonal S) :
    liftReduction ω S ⊥ = S := by
  ext x
  constructor
  · intro hx
    obtain ⟨hxP,hxQ⟩ := (mem_liftReduction ω S ⊥ x).mp hx
    exact (Submodule.Quotient.mk_eq_zero (reductionKernel ω S)).mp hxQ
  · intro hx
    apply (mem_liftReduction ω S ⊥ x).mpr
    refine ⟨hS hx, ?_⟩
    exact (Submodule.Quotient.mk_eq_zero (reductionKernel ω S)).mpr hx

private instance certificate_instance_0145 : OAI.SidorenkoCounterexample.ProofCertificate_0145 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7
  exact @certificate_proof_0145 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 q0 q1 q2 q3 q4 q5 q6 q7

theorem certificate_proof_0146 (hS : S ≤ ω.orthogonal S)
    (L M : Submodule K E) (hL : ω.orthogonal L = L) (hM : ω.orthogonal M = M)
    (hLM : L ⊓ M = S) :
    reduceSubspace ω S L ⊓ reduceSubspace ω S M = ⊥ := by
  have hSL : S ≤ L := hLM.ge.trans inf_le_left
  have hSM : S ≤ M := hLM.ge.trans inf_le_right
  apply liftReduction_injective ω S
  rw [liftReduction_inf,lift_reduce ω S L hSL (lagrangian_le_orthogonal ω S L hL hSL),
    lift_reduce ω S M hSM (lagrangian_le_orthogonal ω S M hM hSM),
    liftReduction_bot ω S hS,hLM]

private instance certificate_instance_0146 : OAI.SidorenkoCounterexample.ProofCertificate_0146 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12
  exact @certificate_proof_0146 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12

variable [FiniteDimensional K E]
theorem certificate_proof_0147 (ha : ω.IsAlt) (hω : ω.Nondegenerate)
    (hS : S ≤ ω.orthogonal S) (L M L' M' : Submodule K E)
    (hL : ω.orthogonal L = L) (hM : ω.orthogonal M = M)
    (hL' : ω.orthogonal L' = L') (hM' : ω.orthogonal M' = M')
    (hLM : L ⊓ M = S) (hLM' : L' ⊓ M' = S) :
    ∃ e : E ≃ₗ[K] E, (∀ x y, ω (e x) (e y) = ω x y) ∧
      L.map e.toLinearMap = L' ∧ M.map e.toLinearMap = M' := by
  have hSL : S ≤ L := hLM.ge.trans inf_le_left
  have hSM : S ≤ M := hLM.ge.trans inf_le_right
  have hSL' : S ≤ L' := hLM'.ge.trans inf_le_left
  have hSM' : S ≤ M' := hLM'.ge.trans inf_le_right
  let Ω := symplecticReductionForm ω S ha
  have hΩa : Ω.IsAlt := symplecticReductionForm_alt ω S ha
  have hΩ : Ω.Nondegenerate := symplecticReductionForm_nondegenerate ω S ha hω
  obtain ⟨f,hf,hfL,hfM⟩ := transverse_pair_transitivity Ω hΩa hΩ
    (reduceSubspace ω S L) (reduceSubspace ω S M)
    (reduceSubspace ω S L') (reduceSubspace ω S M')
    (reduce_lagrangian ω S ha hS L hL hSL)
    (reduce_lagrangian ω S ha hS M hM hSM)
    (reduce_lagrangian ω S ha hS L' hL' hSL')
    (reduce_lagrangian ω S ha hS M' hM' hSM')
    (reduced_pair_transverse ω S hS L M hL hM hLM)
    (reduced_pair_transverse ω S hS L' M' hL' hM' hLM')
  obtain ⟨e,he,heS,heP,heQ⟩ := exists_reduction_isometry_extension ω S ha hω f hf
  have hSe : S.map e.toLinearMap = S := subspace_map_eq_of_fixed e S heS
  have hPe : (ω.orthogonal S).map e.toLinearMap = ω.orthogonal S := by
    rw [← orthogonal_map_of_isometry ω e he,hSe]
  have hmap (U W : Submodule K E) (hU : ω.orthogonal U = U)
      (hW : ω.orthogonal W = W) (hSU : S ≤ U) (hSW : S ≤ W)
      (hfU : (reduceSubspace ω S U).map f.toLinearMap = reduceSubspace ω S W) :
      U.map e.toLinearMap = W := by
    have hSUe : S ≤ U.map e.toLinearMap := by
      rw [← hSe]
      exact Submodule.map_mono hSU
    have hUe : ω.orthogonal (U.map e.toLinearMap) = U.map e.toLinearMap := by
      rw [orthogonal_map_of_isometry ω e he,hU]
    calc
      U.map e.toLinearMap = liftReduction ω S (reduceSubspace ω S (U.map e.toLinearMap)) :=
        (lift_reduce ω S _ hSUe (lagrangian_le_orthogonal ω S _ hUe hSUe)).symm
      _ = liftReduction ω S (reduceSubspace ω S W) := by
        rw [reduceSubspace_map ω S e f hPe heQ,hfU]
      _ = W := lift_reduce ω S W hSW (lagrangian_le_orthogonal ω S W hW hSW)
  exact ⟨e,he,hmap L L' hL hL' hSL hSL' hfL,hmap M M' hM hM' hSM hSM' hfM⟩

private instance certificate_instance_0147 : OAI.SidorenkoCounterexample.ProofCertificate_0147 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19 q20
  exact @certificate_proof_0147 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19 q20

end PairReduction
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
section OrderedPairTransitivity
variable {K E : Type} [Field K] [AddCommGroup E] [Module K E]
  [FiniteDimensional K E] [Finite E]
variable (ω : LinearMap.BilinForm K E)
theorem certificate_proof_0148 (h2 : (2 : K) ≠ 0) (ha : ω.IsAlt)
    (hω : ω.Nondegenerate) (L M L' M' : Submodule K E)
    (hL : ω.orthogonal L = L) (hM : ω.orthogonal M = M)
    (hL' : ω.orthogonal L' = L') (hM' : ω.orthogonal M' = M')
    (hdim : finrank K ↥(L ⊓ M) = finrank K ↥(L' ⊓ M')) :
    ∃ e : E ≃ₗ[K] E, (∀ x y, ω (e x) (e y) = ω x y) ∧
      L.map e.toLinearMap = L' ∧ M.map e.toLinearMap = M' := by
  have hi (U V : Submodule K E) (hU : ω.orthogonal U = U) :
      U ⊓ V ≤ ω.orthogonal (U ⊓ V) := by
    intro x hx y hy
    exact (hU.ge hx.1) y hy.1
  obtain ⟨e0,he0,hS⟩ := isotropic_transitivity ω h2 ha hω
    (L ⊓ M) (L' ⊓ M') (hi L M hL) (hi L' M' hL') hdim
  have hLe : ω.orthogonal (L.map e0.toLinearMap) = L.map e0.toLinearMap := by
    rw [orthogonal_map_of_isometry ω e0 he0,hL]
  have hMe : ω.orthogonal (M.map e0.toLinearMap) = M.map e0.toLinearMap := by
    rw [orthogonal_map_of_isometry ω e0 he0,hM]
  have hLM : L.map e0.toLinearMap ⊓ M.map e0.toLinearMap = L' ⊓ M' := by
    rw [← Submodule.map_inf e0.toLinearMap e0.injective,hS]
  obtain ⟨e1,he1,hL1,hM1⟩ := pair_transitivity_fixed_intersection ω (L' ⊓ M') ha hω
    (hi L' M' hL') (L.map e0.toLinearMap) (M.map e0.toLinearMap) L' M'
    hLe hMe hL' hM' hLM rfl
  refine ⟨e0.trans e1, ?_, ?_, ?_⟩
  · intro x y
    exact (he1 (e0 x) (e0 y)).trans (he0 x y)
  · change L.map (e1.toLinearMap.comp e0.toLinearMap) = L'
    rw [Submodule.map_comp,hL1]
  · change M.map (e1.toLinearMap.comp e0.toLinearMap) = M'
    rw [Submodule.map_comp,hM1]

private instance certificate_instance_0148 : OAI.SidorenkoCounterexample.ProofCertificate_0148 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19
  exact @certificate_proof_0148 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19

end OrderedPairTransitivity
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
section TripleBlocks
variable {K E : Type} [Field K] [AddCommGroup E] [Module K E]
  [FiniteDimensional K E]
variable (ω : LinearMap.BilinForm K E)
theorem certificate_proof_0149 (ha : ω.IsAlt)
    (S N : Submodule K E) (hN : ω.orthogonal N = N) (hSN : S ⊓ N = ⊥) :
    Function.Surjective ((symplecticProjection ω S).comp N.subtype) := by
  let p := (symplecticProjection ω S).comp N.subtype
  apply LinearMap.dualMap_injective_iff.mp
  apply (LinearMap.ker_eq_bot).mp
  apply (Submodule.eq_bot_iff _).mpr
  intro z hz
  obtain ⟨s,rfl⟩ := (Module.evalEquiv K S).surjective z
  have hsN : s.val ∈ N := by
    apply hN.le
    intro n hn
    have hh := LinearMap.congr_fun (LinearMap.mem_ker.mp hz) (⟨n,hn⟩ : N)
    change ω s.val n = 0 at hh
    exact ha.isRefl _ _ hh
  have hs0 : s = 0 := by
    apply Subtype.ext
    change s.val = 0
    exact hSN.le ⟨s.property,hsN⟩
  rw [hs0,map_zero]

private instance certificate_instance_0149 : OAI.SidorenkoCounterexample.ProofCertificate_0149 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11
  exact @certificate_proof_0149 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11

theorem certificate_proof_0150 (ha : ω.IsAlt)
    (S N : Submodule K E) (hS : S ≤ ω.orthogonal S)
    (hN : ω.orthogonal N = N) (hSN : S ⊓ N = ⊥) :
    ∃ B : Submodule K E, (ω.restrict B).Nondegenerate ∧ S ≤ B ∧
      ∃ e : (S × Module.Dual K S) ≃ₗ[K] B,
        (∀ s : S, (e (s,0)).val = s.val) ∧
        (∀ f : Module.Dual K S, (e (0,f)).val ∈ N) ∧
        ∀ x y, ω (e x).val (e y).val = canonicalSymplectic x y := by
  let p := (symplecticProjection ω S).comp N.subtype
  obtain ⟨s,hs⟩ := p.exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.mpr (pairing_from_lagrangian_surjective ω ha S N hN hSN))
  let g := N.subtype.comp s
  have hpair (l : S) (f : Module.Dual K S) : ω l.val (g f) = f l :=
    LinearMap.congr_fun (LinearMap.congr_fun hs f) l
  let f : (S × Module.Dual K S) →ₗ[K] E :=
    S.subtype.comp (LinearMap.fst K S (Module.Dual K S)) +
    g.comp (LinearMap.snd K S (Module.Dual K S))
  have hf (x : S × Module.Dual K S) : f x = x.1.val + g x.2 := rfl
  have hform (x y : S × Module.Dual K S) :
      ω (f x) (f y) = canonicalSymplectic x y := by
    have hSS : ω x.1.val y.1.val = 0 := hS y.1.property x.1.val x.1.property
    have hNN : ω (g x.2) (g y.2) = 0 := (hN.ge (s y.2).property) _ (s x.2).property
    rw [hf,hf]
    simp only [map_add,LinearMap.add_apply,hSS,hNN,
      ← ha.neg_eq y.1.val (g x.2),hpair,canonicalSymplectic_apply]
    ring
  have hinj : Function.Injective f := by
    apply (LinearMap.ker_eq_bot).mp
    apply (Submodule.eq_bot_iff _).mpr
    intro x hx
    apply canonicalSymplectic_nondegenerate.1
    intro y
    rw [← hform,hx]
    simp
  let B := f.range
  let e : (S × Module.Dual K S) ≃ₗ[K] B := LinearEquiv.ofInjective f hinj
  have he (x : S × Module.Dual K S) : (e x).val = f x := rfl
  have hleft (x : B) (hx : ∀ y : B, ω x.val y.val = 0) : x = 0 := by
    obtain ⟨z,rfl⟩ := e.surjective x
    have hz : z = 0 := canonicalSymplectic_nondegenerate.1 z (fun w => by
      rw [← hform]
      exact hx (e w))
    rw [hz,map_zero]
  refine ⟨B,⟨hleft, ?_⟩, ?_,e, ?_, ?_, ?_⟩
  · intro x hx
    apply hleft
    intro y
    exact ha.isRefl _ _ (hx y)
  · intro x hx
    refine ⟨(⟨x,hx⟩,0),?_⟩
    simp [hf]
  · intro l
    simp [he,hf]
  · intro l
    change (0 : E) + (s l).val ∈ N
    simpa only [zero_add] using (s l).property
  · intro x y
    exact hform x y

private instance certificate_instance_0150 : OAI.SidorenkoCounterexample.ProofCertificate_0150 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12
  exact @certificate_proof_0150 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12

end TripleBlocks
end SidorenkoCounterexample
end OAI

theorem solution : OAI.SidorenkoCounterexample.ProofCertificate_0131 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0132 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0133 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0134 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0135 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0136 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0137 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0138 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0139 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0140 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0141 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0142 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0143 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0144 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0145 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0146 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0147 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0148 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0149 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0150 := by
  exact ⟨inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance⟩
end

