-- Prove2me | solution 1 for OAI.SidorenkoCounterexample.finite_geometry_batch_12
-- status  : ACCEPTED   (prove)
-- author  : @abcdefg
-- created : 2026-10-09T06:25:00.057782+00:00
-- url     : https://prove2.me/submissions/999c4950-f978-4268-95f4-eb45e1ec8677

import Definitions.Def_SidorenkoCertificateBundleA
set_option linter.unusedVariables false
section
variable [p0 : OAI.SidorenkoCounterexample.ProofCertificate_0032]
  [p1 : OAI.SidorenkoCounterexample.ProofCertificate_0107]
  [p2 : OAI.SidorenkoCounterexample.ProofCertificate_0108]
  [p3 : OAI.SidorenkoCounterexample.ProofCertificate_0110]
  [p4 : OAI.SidorenkoCounterexample.ProofCertificate_0111]
  [p5 : OAI.SidorenkoCounterexample.ProofCertificate_0112]
  [p6 : OAI.SidorenkoCounterexample.ProofCertificate_0114]
  [p7 : OAI.SidorenkoCounterexample.ProofCertificate_0117]
  [p8 : OAI.SidorenkoCounterexample.ProofCertificate_0118]
  [p9 : OAI.SidorenkoCounterexample.ProofCertificate_0119]
  [p10 : OAI.SidorenkoCounterexample.ProofCertificate_0120]
  [p11 : OAI.SidorenkoCounterexample.ProofCertificate_0121]
  [p12 : OAI.SidorenkoCounterexample.ProofCertificate_0122]
  [p13 : OAI.SidorenkoCounterexample.ProofCertificate_0139]
  [p14 : OAI.SidorenkoCounterexample.ProofCertificate_0144]
  [p15 : OAI.SidorenkoCounterexample.ProofCertificate_0145]
  [p16 : OAI.SidorenkoCounterexample.ProofCertificate_0168]
  [p17 : OAI.SidorenkoCounterexample.ProofCertificate_0169]
  [p18 : OAI.SidorenkoCounterexample.ProofCertificate_0172]
  [p19 : OAI.SidorenkoCounterexample.ProofCertificate_0207]
  [p20 : OAI.SidorenkoCounterexample.ProofCertificate_0216]
  [p21 : OAI.SidorenkoCounterexample.ProofCertificate_0217]
  [p22 : OAI.SidorenkoCounterexample.ProofCertificate_0220]
  [p23 : OAI.SidorenkoCounterexample.ProofCertificate_0221]
  [p24 : OAI.SidorenkoCounterexample.ProofCertificate_0227]
  [p25 : OAI.SidorenkoCounterexample.ProofCertificate_0228]
  [p26 : OAI.SidorenkoCounterexample.ProofCertificate_0229]
  [p27 : OAI.SidorenkoCounterexample.ProofCertificate_0238]
  [p28 : OAI.SidorenkoCounterexample.ProofCertificate_0242]
  [p29 : OAI.SidorenkoCounterexample.ProofCertificate_0252]
  [p30 : OAI.SidorenkoCounterexample.ProofCertificate_0257]
  [p31 : OAI.SidorenkoCounterexample.ProofCertificate_0262]
  [p32 : OAI.SidorenkoCounterexample.ProofCertificate_0263]
  [p33 : OAI.SidorenkoCounterexample.ProofCertificate_0264]
  [p34 : OAI.SidorenkoCounterexample.ProofCertificate_0265]
  [p35 : OAI.SidorenkoCounterexample.ProofCertificate_0270]
  [p36 : OAI.SidorenkoCounterexample.ProofCertificate_0271]
  [p37 : OAI.SidorenkoCounterexample.ProofCertificate_0272]
  [p38 : OAI.SidorenkoCounterexample.ProofCertificate_0273]
  [p39 : OAI.SidorenkoCounterexample.ProofCertificate_0275]
  [p40 : OAI.SidorenkoCounterexample.ProofCertificate_0276]
include p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40

namespace OAI
namespace SidorenkoCounterexample
open Module
section CommonOrbitGeometry
variable {K E : Type} [Field K] [AddCommGroup E] [Module K E]
  [FiniteDimensional K E]
variable (ω : LinearMap.BilinForm K E)
theorem certificate_proof_0277 (S A : Submodule K E)
    (hSA : S ≤ A) (hAP : A ≤ ω.orthogonal S) :
    finrank K (reduceSubspace ω S A) + finrank K S = finrank K A := by
  let f : A →ₗ[K] ReducedSpace ω S := (reductionKernel ω S).mkQ.comp (Submodule.inclusion hAP)
  have hk : LinearMap.ker f = S.comap A.subtype := by
    ext x
    exact Submodule.Quotient.mk_eq_zero (reductionKernel ω S)
  have hr : LinearMap.range f = reduceSubspace ω S A := by
    ext y
    constructor
    · rintro ⟨x,rfl⟩
      exact ⟨⟨x.val,hAP x.property⟩,x.property,rfl⟩
    · rintro ⟨x,hx,rfl⟩
      exact ⟨⟨x.val,hx⟩,rfl⟩
  have hh := f.finrank_range_add_finrank_ker
  rw [hk,hr,(Submodule.comapSubtypeEquivOfLe hSA).finrank_eq] at hh
  exact hh

private instance certificate_instance_0277 : OAI.SidorenkoCounterexample.ProofCertificate_0277 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10
  exact @certificate_proof_0277 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10

theorem certificate_proof_0278 [Finite E] (h2 : (2:K) ≠ 0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
    (L M N : SymplecticLagrangian ω) :
    let S := (L.val ⊓ M.val) ⊓ N.val
    ∃ f : IsotropicDimspace ω (finrank K S) ×
      OrderedTripleOrbit (symplecticReductionForm ω S ha)
        (reduceSubspace ω S L.val) (reduceSubspace ω S M.val) (reduceSubspace ω S N.val) →
      OrderedTripleOrbit ω L.val M.val N.val, Function.Injective f := by
  dsimp only
  classical
  let S := (L.val ⊓ M.val) ⊓ N.val
  have hSL : S ≤ L.val := inf_le_left.trans inf_le_left
  have hSM : S ≤ M.val := inf_le_left.trans inf_le_right
  have hSN : S ≤ N.val := inf_le_right
  have hS : S ≤ ω.orthogonal S := by
    intro x hx y hy
    exact L.property.ge (hSL hx) y (hSL hy)
  let η := symplecticReductionForm ω S ha
  let L' := commonReductionLagrangian ω S ha hS L hSL
  let M' := commonReductionLagrangian ω S ha hS M hSM
  let N' := commonReductionLagrangian ω S ha hS N hSN
  have hzero : (L'.val ⊓ M'.val) ⊓ N'.val = ⊥ := by
    change (reduceSubspace ω S L.val ⊓ reduceSubspace ω S M.val) ⊓ reduceSubspace ω S N.val = ⊥
    rw [←reduceSubspace_inf ω S L.val M.val hSL,
      ←reduceSubspace_inf ω S (L.val ⊓ M.val) N.val inf_le_left]
    exact reduceSubspace_self ω S
  have ht (T : IsotropicDimspace ω (finrank K S)) := isotropic_transitivity ω h2 ha hω
    S T.val hS T.property.1 T.property.2.symm
  let e (T : IsotropicDimspace ω (finrank K S)) := (ht T).choose
  have he (T : IsotropicDimspace ω (finrank K S)) := (ht T).choose_spec
  let Orb := OrderedTripleOrbit η L'.val M'.val N'.val
  have hpLag (p : Orb) := orderedTripleOrbit_lagrangians η L' M' N' p
  have hpzero (p : Orb) : (p.val.1 ⊓ p.val.2.1) ⊓ p.val.2.2 = ⊥ := by
    obtain ⟨g,_,hgL,hgM,hgN⟩ := p.property
    rw [←hgL,←hgM,←hgN,←Submodule.map_inf g.toLinearMap g.injective,
      ←Submodule.map_inf g.toLinearMap g.injective,hzero,Submodule.map_bot]
  have hgood (p : Orb) : TripleIsometry ω ω L.val M.val N.val
      (liftReduction ω S p.val.1) (liftReduction ω S p.val.2.1) (liftReduction ω S p.val.2.2) := by
    apply triple_containing_isometry_lift ω S ha hω hS L.val M.val N.val
      (liftReduction ω S p.val.1) (liftReduction ω S p.val.2.1) (liftReduction ω S p.val.2.2)
      L.property M.property N.property
      (liftReduction_lagrangian ω S ha hS _ (hpLag p).1)
      (liftReduction_lagrangian ω S ha hS _ (hpLag p).2.1)
      (liftReduction_lagrangian ω S ha hS _ (hpLag p).2.2)
      hSL hSM hSN (le_liftReduction ω S hS _) (le_liftReduction ω S hS _) (le_liftReduction ω S hS _)
    rw [reduce_lift,reduce_lift,reduce_lift]
    exact p.property
  have hgood' (T : IsotropicDimspace ω (finrank K S)) (p : Orb) : TripleIsometry ω ω L.val M.val N.val
      ((liftReduction ω S p.val.1).map (e T).toLinearMap)
      ((liftReduction ω S p.val.2.1).map (e T).toLinearMap)
      ((liftReduction ω S p.val.2.2).map (e T).toLinearMap) := by
    obtain ⟨g,hg,hgL,hgM,hgN⟩ := hgood p
    refine ⟨g.trans (e T),?_,?_,?_,?_⟩
    · intro x y
      exact ((he T).1 (g x) (g y)).trans (hg x y)
    · rw [submodule_map_trans,hgL]
    · rw [submodule_map_trans,hgM]
    · rw [submodule_map_trans,hgN]
  let f : IsotropicDimspace ω (finrank K S) × Orb → OrderedTripleOrbit ω L.val M.val N.val := fun p =>
    ⟨((liftReduction ω S p.2.val.1).map (e p.1).toLinearMap,
      (liftReduction ω S p.2.val.2.1).map (e p.1).toLinearMap,
      (liftReduction ω S p.2.val.2.2).map (e p.1).toLinearMap),hgood' p.1 p.2⟩
  have hrec (p) : ((f p).val.1 ⊓ (f p).val.2.1) ⊓ (f p).val.2.2 = p.1.val := by
    change (((liftReduction ω S p.2.val.1).map (e p.1).toLinearMap) ⊓
      ((liftReduction ω S p.2.val.2.1).map (e p.1).toLinearMap)) ⊓
      ((liftReduction ω S p.2.val.2.2).map (e p.1).toLinearMap) = _
    rw [←Submodule.map_inf (e p.1).toLinearMap (e p.1).injective,
      ←Submodule.map_inf (e p.1).toLinearMap (e p.1).injective,
      ←liftReduction_inf,←liftReduction_inf,hpzero, liftReduction_bot ω S hS]
    exact (he p.1).2
  refine ⟨f,?_⟩
  rintro ⟨T,p⟩ ⟨T',p'⟩ h
  have hT : T = T' := by
    apply Subtype.ext
    exact (hrec (T,p)).symm.trans ((congrArg (fun x : OrderedTripleOrbit ω L.val M.val N.val =>
      (x.val.1 ⊓ x.val.2.1) ⊓ x.val.2.2) h).trans (hrec (T',p')))
  subst T'
  have hv := congrArg Subtype.val h
  have hinj := (Submodule.map_injective_of_injective (e T).injective).comp (liftReduction_injective ω S)
  have hp : p = p' := Subtype.ext (Prod.ext (hinj (congrArg Prod.fst hv))
    (Prod.ext (hinj (congrArg (fun x => x.2.1) hv)) (hinj (congrArg (fun x => x.2.2) hv))))
  subst p'
  rfl

private instance certificate_instance_0278 : OAI.SidorenkoCounterexample.ProofCertificate_0278 := by
  constructor
  intro c0 c1 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13
  exact @certificate_proof_0278 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13

variable [Finite E]
theorem certificate_proof_0279 (h2 : (2:K) ≠ 0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
    (L M N : SymplecticLagrangian ω) :
    let S := (L.val ⊓ M.val) ⊓ N.val
    Nat.card (IsotropicDimspace ω (finrank K S)) *
      Nat.card (OrderedTripleOrbit (symplecticReductionForm ω S ha)
        (reduceSubspace ω S L.val) (reduceSubspace ω S M.val) (reduceSubspace ω S N.val)) ≤
      Nat.card (OrderedTripleOrbit ω L.val M.val N.val) := by
  obtain ⟨f,hf⟩ := commonOrbit_injection ω h2 ha hω L M N
  simpa only [Nat.card_prod] using Nat.card_le_card_of_injective f hf

private instance certificate_instance_0279 : OAI.SidorenkoCounterexample.ProofCertificate_0279 := by
  constructor
  intro c0 c1 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13
  exact @certificate_proof_0279 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13

end CommonOrbitGeometry
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
section AllOrbitMass
variable {K E : Type} [Field K] [AddCommGroup E] [Module K E]
  [Fintype K] [Finite E] [Invertible (2:K)]
variable (ω : LinearMap.BilinForm K E)
theorem certificate_proof_0280 : Monotone pairOrbitConstant := by
  intro m n h
  unfold pairOrbitConstant
  have hm := lagrangianConstant_pos m
  have hn := lagrangianConstant_pos n
  have hc := lagrangianConstant_mono h
  gcongr <;> norm_num

private instance certificate_instance_0280 : OAI.SidorenkoCounterexample.ProofCertificate_0280 := by
  constructor
  exact @certificate_proof_0280 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40

theorem certificate_proof_0281 (D : ℕ) : 0 < orbitMassConstant D :=
  mul_pos (lagrangianConstant_pos D) (pairOrbitConstant_pos D)

private instance certificate_instance_0281 : OAI.SidorenkoCounterexample.ProofCertificate_0281 := by
  constructor
  intro q0
  exact @certificate_proof_0281 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 q0

theorem certificate_proof_0282 (ha : ω.IsAlt) (hω : ω.Nondegenerate)
    (D : ℕ) (hD : 2*D = finrank K E)
    (hq : 4*lagrangianConstant D ≤ (Fintype.card K : ℝ))
    (L M N : SymplecticLagrangian ω) :
    (Fintype.card K : ℝ)^(3*(D+1).choose 2) ≤
      orbitMassConstant D * (Fintype.card K : ℝ)^(tripleDefect D L.val M.val N.val) *
        Nat.card (OrderedTripleOrbit ω L.val M.val N.val) := by
  let S := (L.val ⊓ M.val) ⊓ N.val
  have hSL : S ≤ L.val := inf_le_left.trans inf_le_left
  have hSM : S ≤ M.val := inf_le_left.trans inf_le_right
  have hSN : S ≤ N.val := inf_le_right
  have hS : S ≤ ω.orthogonal S := by
    intro x hx y hy
    exact L.property.ge (hSL hx) y (hSL hy)
  let c := finrank K S
  have hc : c ≤ D := isotropic_finrank_le_half ω hω D hD S hS
  let η := symplecticReductionForm ω S ha
  let L' := commonReductionLagrangian ω S ha hS L hSL
  let M' := commonReductionLagrangian ω S ha hS M hSM
  let N' := commonReductionLagrangian ω S ha hS N hSN
  let : Finite (ReducedSpace ω S) := Module.finite_of_finite K
  have hzero : (L'.val ⊓ M'.val) ⊓ N'.val = ⊥ := by
    change (reduceSubspace ω S L.val ⊓ reduceSubspace ω S M.val) ⊓ reduceSubspace ω S N.val = ⊥
    rw [←reduceSubspace_inf ω S L.val M.val hSL,
      ←reduceSubspace_inf ω S (L.val ⊓ M.val) N.val inf_le_left]
    exact reduceSubspace_self ω S
  have hdim : 2*(D-c) = finrank K (ReducedSpace ω S) := by
    have hh := reducedSpace_finrank ω S hω hS
    change _ + 2*c = _ at hh
    omega
  have hq' : 4*lagrangianConstant (D-c) ≤ (Fintype.card K : ℝ) :=
    (mul_le_mul_of_nonneg_left (lagrangianConstant_mono (Nat.sub_le D c)) (by norm_num)).trans hq
  have hp := commonZeroOrbit_card_lower η (symplecticReductionForm_alt ω S ha)
    (symplecticReductionForm_nondegenerate ω S ha hω) (D-c) hdim hq' L' M' N' hzero
  have hpair (P Q : SymplecticLagrangian ω) (hSP : S ≤ P.val) (hSQ : S ≤ Q.val) :
      finrank K ↥(reduceSubspace ω S P.val ⊓ reduceSubspace ω S Q.val) =
        finrank K ↥(P.val ⊓ Q.val)-c := by
    rw [←reduceSubspace_inf ω S P.val Q.val hSP]
    have hh := reduceSubspace_finrank_containing ω S (P.val ⊓ Q.val) (le_inf hSP hSQ)
      (inf_le_left.trans (lagrangian_le_orthogonal ω S P.val P.property hSP))
    change _ + c = _ at hh
    omega
  change (Fintype.card K : ℝ)^(3*(D-c+1).choose 2) ≤ pairOrbitConstant (D-c) *
    (Fintype.card K : ℝ)^((finrank K ↥(reduceSubspace ω S L.val ⊓ reduceSubspace ω S M.val)+1).choose 2 +
      (finrank K ↥(reduceSubspace ω S L.val ⊓ reduceSubspace ω S N.val)+1).choose 2 +
      (finrank K ↥(reduceSubspace ω S M.val ⊓ reduceSubspace ω S N.val)+1).choose 2) * _ at hp
  rw [hpair L M hSL hSM,hpair L N hSL hSN,hpair M N hSM hSN] at hp
  have h2 := (isUnit_of_invertible (2:K)).ne_zero
  have hi := (isotropic_card_bounds ω h2 ha hω D hD c hc).1
  have hm : (Nat.card (IsotropicDimspace ω c) : ℝ) *
    Nat.card (OrderedTripleOrbit η L'.val M'.val N'.val) ≤
      Nat.card (OrderedTripleOrbit ω L.val M.val N.val) := by
    exact_mod_cast commonOrbit_card_lower ω h2 ha hω L M N
  let δ := (finrank K ↥(L.val ⊓ M.val)-c+1).choose 2 +
    (finrank K ↥(L.val ⊓ N.val)-c+1).choose 2 + (finrank K ↥(M.val ⊓ N.val)-c+1).choose 2
  have hconst : lagrangianConstant (D-c)*pairOrbitConstant (D-c) ≤ orbitMassConstant D :=
    mul_le_mul (lagrangianConstant_mono (Nat.sub_le D c)) (pairOrbitConstant_mono (Nat.sub_le D c))
      (le_of_lt (pairOrbitConstant_pos _)) (le_of_lt (lagrangianConstant_pos _))
  have hm' := mul_le_mul hconst hm (by positivity) (le_of_lt (orbitMassConstant_pos D))
  have hbase : (Fintype.card K : ℝ)^(isotropicExponent D c+3*(D-c+1).choose 2) ≤
      orbitMassConstant D * (Fintype.card K : ℝ)^δ * Nat.card (OrderedTripleOrbit ω L.val M.val N.val) := by
    calc
      _ ≤ (lagrangianConstant (D-c)*Nat.card (IsotropicDimspace ω c)) *
        (pairOrbitConstant (D-c)*(Fintype.card K : ℝ)^δ * Nat.card (OrderedTripleOrbit η L'.val M'.val N'.val)) := by
          rw [pow_add]
          exact mul_le_mul hi hp (by positivity) (mul_nonneg (le_of_lt (lagrangianConstant_pos _)) (Nat.cast_nonneg _))
      _ = ((lagrangianConstant (D-c)*pairOrbitConstant (D-c))*
        ((Nat.card (IsotropicDimspace ω c) : ℝ)*Nat.card (OrderedTripleOrbit η L'.val M'.val N'.val)))*
          (Fintype.card K : ℝ)^δ := by ring
      _ ≤ (orbitMassConstant D*Nat.card (OrderedTripleOrbit ω L.val M.val N.val))*
          (Fintype.card K : ℝ)^δ := mul_le_mul_of_nonneg_right hm' (by positivity)
      _ = _ := by ring
  have hh := mul_le_mul_of_nonneg_right hbase (show 0 ≤ (Fintype.card K : ℝ)^((D+1)*c) by positivity)
  rw [←pow_add,common_cost_cancellation D c hc] at hh
  change _ ≤ orbitMassConstant D * (Fintype.card K : ℝ)^((D+1)*c+δ) * _
  rw [pow_add]
  calc
    _ ≤ (orbitMassConstant D*(Fintype.card K : ℝ)^δ*Nat.card (OrderedTripleOrbit ω L.val M.val N.val))*
      (Fintype.card K : ℝ)^((D+1)*c) := hh
    _ = _ := by ring

private instance certificate_instance_0282 : OAI.SidorenkoCounterexample.ProofCertificate_0282 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16
  exact @certificate_proof_0282 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16

end AllOrbitMass
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
section ConfigurationUpper
variable {K E : Type} [Field K] [AddCommGroup E] [Module K E] [Finite E]
variable (ω : LinearMap.BilinForm K E)
theorem certificate_proof_0283 (h2 : (2:K) ≠ 0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
    (S U V W : Submodule K E) (hS : S ≤ ω.orthogonal S)
    (hU : U ≤ S) (hV : V ≤ S) (hW : W ≤ S) (_hsum : U ⊔ V ⊔ W = S) :
    ∃ f : IsotropicDimspace ω (finrank K S) ×
      TripleLinearOrbit (U.comap S.subtype) (V.comap S.subtype) (W.comap S.subtype) →
        OrderedTripleOrbit ω U V W, Function.Surjective f := by
  classical
  have ht (T : IsotropicDimspace ω (finrank K S)) := isotropic_transitivity ω h2 ha hω
    S T.val hS T.property.1 T.property.2.symm
  let e (T : IsotropicDimspace ω (finrank K S)) := (ht T).choose
  have he (T) := (ht T).choose_spec
  have hgood (T : IsotropicDimspace ω (finrank K S))
      (p : TripleLinearOrbit (U.comap S.subtype) (V.comap S.subtype) (W.comap S.subtype)) :
      ∃ f : E ≃ₗ[K] E, (∀ x y, ω (f x) (f y) = ω x y) ∧
        U.map f.toLinearMap = (p.val.1.map S.subtype).map (e T).toLinearMap ∧
        V.map f.toLinearMap = (p.val.2.1.map S.subtype).map (e T).toLinearMap ∧
        W.map f.toLinearMap = (p.val.2.2.map S.subtype).map (e T).toLinearMap := by
    obtain ⟨g,hgU,hgV,hgW⟩ := p.property
    obtain ⟨r,hr,hrg⟩ := exists_isotropic_isometry_extension ω h2 ha hω S S hS hS g
    refine ⟨r.trans (e T),?_,?_,?_,?_⟩
    · intro x y
      exact ((he T).1 (r x) (r y)).trans (hr x y)
    · rw [submodule_map_trans,subspace_map_extension S S U hU r g hrg,hgU]
    · rw [submodule_map_trans,subspace_map_extension S S V hV r g hrg,hgV]
    · rw [submodule_map_trans,subspace_map_extension S S W hW r g hrg,hgW]
  let f : IsotropicDimspace ω (finrank K S) ×
      TripleLinearOrbit (U.comap S.subtype) (V.comap S.subtype) (W.comap S.subtype) →
        OrderedTripleOrbit ω U V W := fun p =>
    ⟨((p.2.val.1.map S.subtype).map (e p.1).toLinearMap,
      (p.2.val.2.1.map S.subtype).map (e p.1).toLinearMap,
      (p.2.val.2.2.map S.subtype).map (e p.1).toLinearMap),hgood p.1 p.2⟩
  refine ⟨f,?_⟩
  intro p
  obtain ⟨g,hg,hgU,hgV,hgW⟩ := p.property
  have hT : S.map g.toLinearMap ≤ ω.orthogonal (S.map g.toLinearMap) := by
    rw [orthogonal_map_of_isometry ω g hg]
    exact Submodule.map_mono hS
  let T : IsotropicDimspace ω (finrank K S) :=
    ⟨S.map g.toLinearMap,hT,g.finrank_map_eq S⟩
  let r := g.trans (e T).symm
  have hrS : S.map r.toLinearMap = S := by
    rw [submodule_map_trans]
    change T.val.map (e T).symm.toLinearMap = S
    rw [←(he T).2,submodule_map_symm_cancel]
  let rS : S ≃ₗ[K] S := r.ofSubmodules S S hrS
  let q := tripleLinearOrbitMap (U.comap S.subtype) (V.comap S.subtype) (W.comap S.subtype) rS
  have heq : r.trans (e T) = g := by
    ext x
    simp only [r,LinearEquiv.trans_apply,LinearEquiv.apply_symm_apply]
  have hmap (A : Submodule K E) (hA : A ≤ S) :
      ((((A.comap S.subtype).map rS.toLinearMap).map S.subtype).map (e T).toLinearMap) = A.map g.toLinearMap := by
    rw [←subspace_map_extension S S A hA r rS (fun _ => rfl),←submodule_map_trans,heq]
  refine ⟨(T,q),Subtype.ext ?_⟩
  change (((((U.comap S.subtype).map rS.toLinearMap).map S.subtype).map (e T).toLinearMap),
    ((((V.comap S.subtype).map rS.toLinearMap).map S.subtype).map (e T).toLinearMap),
    ((((W.comap S.subtype).map rS.toLinearMap).map S.subtype).map (e T).toLinearMap)) = p.val
  rw [hmap U hU,hmap V hV,hmap W hW,hgU,hgV,hgW]

private instance certificate_instance_0283 : OAI.SidorenkoCounterexample.ProofCertificate_0283 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18
  exact @certificate_proof_0283 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18

theorem certificate_proof_0284 (h2 : (2:K) ≠ 0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
    (S U V W : Submodule K E) (hS : S ≤ ω.orthogonal S)
    (hU : U ≤ S) (hV : V ≤ S) (hW : W ≤ S) (hsum : U ⊔ V ⊔ W = S) :
    Nat.card (OrderedTripleOrbit ω U V W) = Nat.card (IsotropicDimspace ω (finrank K S)) *
      Nat.card (TripleLinearOrbit (U.comap S.subtype) (V.comap S.subtype) (W.comap S.subtype)) := by
  apply le_antisymm
  · obtain ⟨f,hf⟩ := triple_subspace_orbit_surjection ω h2 ha hω S U V W hS hU hV hW hsum
    simpa only [Nat.card_prod] using Nat.card_le_card_of_surjective f hf
  · obtain ⟨f,hf⟩ := triple_subspace_orbit_injection ω h2 ha hω S U V W hS hU hV hW hsum
    simpa only [Nat.card_prod] using Nat.card_le_card_of_injective f hf

private instance certificate_instance_0284 : OAI.SidorenkoCounterexample.ProofCertificate_0284 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18
  exact @certificate_proof_0284 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18

end ConfigurationUpper
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
section DecompositionTransitivity
variable {K E F : Type} [Field K] [AddCommGroup E] [Module K E] [AddCommGroup F] [Module K F]
theorem certificate_proof_0285 (U : Submodule K E) (V : Submodule K F)
    (e : E ≃ₗ[K] F) (g : U ≃ₗ[K] V) (h : ∀ x : U, e x.val = (g x).val) :
    U.map e.toLinearMap = V := by
  ext y
  constructor
  · rintro ⟨x,hx,rfl⟩
    change e (⟨x,hx⟩ : U).val ∈ V
    rw [h ⟨x,hx⟩]
    exact (g ⟨x,hx⟩).property
  · intro hy
    obtain ⟨x,hx⟩ := g.surjective ⟨y,hy⟩
    exact ⟨x.val,x.property,(h x).trans (congrArg Subtype.val hx)⟩

private instance certificate_instance_0285 : OAI.SidorenkoCounterexample.ProofCertificate_0285 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12
  exact @certificate_proof_0285 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12

variable [FiniteDimensional K E] [FiniteDimensional K F]
private instance certificate_extra_0234 : OAI.SidorenkoCounterexample.ProofCertificate_0234 := by
  constructor
  intros
  rfl

theorem certificate_proof_0286 (U V W : Submodule K E) (U' V' W' : Submodule K F)
    (hU : IsCompl U (V ⊔ W)) (hVW : Disjoint V W)
    (hU' : IsCompl U' (V' ⊔ W')) (hVW' : Disjoint V' W')
    (hu : finrank K U = finrank K U') (hv : finrank K V = finrank K V') (hw : finrank K W = finrank K W') :
    ∃ e : E ≃ₗ[K] F, U.map e.toLinearMap = U' ∧ V.map e.toLinearMap = V' ∧ W.map e.toLinearMap = W' := by
  let gu := LinearEquiv.ofFinrankEq U U' hu
  let gv := LinearEquiv.ofFinrankEq V V' hv
  let gw := LinearEquiv.ofFinrankEq W W' hw
  let a := tripleSumEquiv U V W hU hVW
  let b := tripleSumEquiv U' V' W' hU' hVW'
  let e := a.symm.trans ((gu.prodCongr (gv.prodCongr gw)).trans b)
  have heU (x : U) : e x.val = (gu x).val := by
    have hax : a (x,(0,0)) = x.val := by simp [a]
    rw [←hax]
    simp [e,b]
  have heV (x : V) : e x.val = (gv x).val := by
    have hax : a (0,(x,0)) = x.val := by simp [a]
    rw [←hax]
    simp [e,b]
  have heW (x : W) : e x.val = (gw x).val := by
    have hax : a (0,(0,x)) = x.val := by simp [a]
    rw [←hax]
    simp [e,b]
  exact ⟨e,subspace_map_eq_of_restriction_equiv U U' e gu heU,
    subspace_map_eq_of_restriction_equiv V V' e gv heV,subspace_map_eq_of_restriction_equiv W W' e gw heW⟩

private instance certificate_instance_0286 : OAI.SidorenkoCounterexample.ProofCertificate_0286 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19 q20 q21 q22
  exact @certificate_proof_0286 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19 q20 q21 q22

end DecompositionTransitivity
section ConfigTransitivity
variable {K E : Type} [Field K] [AddCommGroup E] [Module K E] [Finite E]
variable (ω : LinearMap.BilinForm K E)
omit [Finite E] in
theorem certificate_proof_0287 (S U V W : Submodule K E)
    (hU : U ≤ S) (hV : V ≤ S) (hW : W ≤ S)
    (hsum : U ⊔ V ⊔ W = S) (hdis : Disjoint U (V ⊔ W)) :
    IsCompl (U.comap S.subtype) (V.comap S.subtype ⊔ W.comap S.subtype) := by
  constructor
  · apply disjoint_iff.mpr
    rw [←subspace_comap_sup_of_le S V W hV hW,←Submodule.comap_inf,disjoint_iff.mp hdis]
    simp
  · apply codisjoint_iff.mpr
    rw [←sup_assoc,←subspace_comap_sup_of_le S U V hU hV,
      ←subspace_comap_sup_of_le S (U ⊔ V) W (sup_le hU hV) hW,hsum]
    simp

private instance certificate_instance_0287 : OAI.SidorenkoCounterexample.ProofCertificate_0287 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13
  exact @certificate_proof_0287 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13

theorem certificate_proof_0288 (h2 : (2:K) ≠ 0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
    (U V W U' V' W' : Submodule K E)
    (hS : U ⊔ V ⊔ W ≤ ω.orthogonal (U ⊔ V ⊔ W))
    (hS' : U' ⊔ V' ⊔ W' ≤ ω.orthogonal (U' ⊔ V' ⊔ W'))
    (hdis : Disjoint U (V ⊔ W)) (hVW : Disjoint V W)
    (hdis' : Disjoint U' (V' ⊔ W')) (hVW' : Disjoint V' W')
    (hu : finrank K U = finrank K U') (hv : finrank K V = finrank K V') (hw : finrank K W = finrank K W') :
    TripleIsometry ω ω U V W U' V' W' := by
  let S := U ⊔ V ⊔ W
  let T := U' ⊔ V' ⊔ W'
  have hU : U ≤ S := le_sup_of_le_left le_sup_left
  have hV : V ≤ S := le_sup_of_le_left le_sup_right
  have hW : W ≤ S := le_sup_right
  have hU' : U' ≤ T := le_sup_of_le_left le_sup_left
  have hV' : V' ≤ T := le_sup_of_le_left le_sup_right
  have hW' : W' ≤ T := le_sup_right
  have hd : Disjoint (V.comap S.subtype) (W.comap S.subtype) := by
    apply disjoint_iff.mpr
    rw [←Submodule.comap_inf,hVW.eq_bot]
    simp
  have hd' : Disjoint (V'.comap T.subtype) (W'.comap T.subtype) := by
    apply disjoint_iff.mpr
    rw [←Submodule.comap_inf,hVW'.eq_bot]
    simp
  obtain ⟨g,hgU,hgV,hgW⟩ := triple_decomposition_equiv
    (U.comap S.subtype) (V.comap S.subtype) (W.comap S.subtype)
    (U'.comap T.subtype) (V'.comap T.subtype) (W'.comap T.subtype)
    (triple_comap_isCompl S U V W hU hV hW rfl hdis) hd
    (triple_comap_isCompl T U' V' W' hU' hV' hW' rfl hdis') hd'
    (by rw [(Submodule.comapSubtypeEquivOfLe hU).finrank_eq,(Submodule.comapSubtypeEquivOfLe hU').finrank_eq]; exact hu)
    (by rw [(Submodule.comapSubtypeEquivOfLe hV).finrank_eq,(Submodule.comapSubtypeEquivOfLe hV').finrank_eq]; exact hv)
    (by rw [(Submodule.comapSubtypeEquivOfLe hW).finrank_eq,(Submodule.comapSubtypeEquivOfLe hW').finrank_eq]; exact hw)
  obtain ⟨e,he,heg⟩ := exists_isotropic_isometry_extension ω h2 ha hω S T hS hS' g
  refine ⟨e,he,?_,?_,?_⟩
  · rw [subspace_map_extension S T U hU e g heg,hgU,subtype_map_comap_of_le T U' hU']
  · rw [subspace_map_extension S T V hV e g heg,hgV,subtype_map_comap_of_le T V' hV']
  · rw [subspace_map_extension S T W hW e g heg,hgW,subtype_map_comap_of_le T W' hW']

private instance certificate_instance_0288 : OAI.SidorenkoCounterexample.ProofCertificate_0288 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19 q20 q21 q22 q23 q24
  exact @certificate_proof_0288 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19 q20 q21 q22 q23 q24

end ConfigTransitivity
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
section ConfigurationBound
variable {K E : Type} [Field K] [AddCommGroup E] [Module K E] [Fintype K] [Finite E]
variable (ω : LinearMap.BilinForm K E)
theorem certificate_proof_0289 (h2 : (2:K) ≠ 0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
    (D : ℕ) (hD : 2*D = finrank K E)
    (S U V W : Submodule K E) (hS : S ≤ ω.orthogonal S)
    (hU : U ≤ S) (hV : V ≤ S) (hW : W ≤ S) (hsum : U ⊔ V ⊔ W = S)
    (hdis : Disjoint U (V ⊔ W)) (hVW : Disjoint V W) :
    (Nat.card (OrderedTripleOrbit ω U V W) : ℝ) ≤
      (lagrangianConstant D * 4^D) * (Fintype.card K : ℝ)^(isotropicExponent D (finrank K S) +
        2*(finrank K U*finrank K V+finrank K U*finrank K W+finrank K V*finrank K W)) := by
  have hconst := lagrangianConstant_pos D
  let U' := U.comap S.subtype
  let V' := V.comap S.subtype
  let W' := W.comap S.subtype
  have hc : IsCompl U' (V' ⊔ W') := triple_comap_isCompl S U V W hU hV hW hsum hdis
  have hvw : Disjoint V' W' := by
    apply disjoint_iff.mpr
    change V.comap S.subtype ⊓ W.comap S.subtype = ⊥
    rw [←Submodule.comap_inf,disjoint_iff.mp hVW]
    simp
  have hu' : finrank K U' = finrank K U := (Submodule.comapSubtypeEquivOfLe hU).finrank_eq
  have hv' : finrank K V' = finrank K V := (Submodule.comapSubtypeEquivOfLe hV).finrank_eq
  have hw' : finrank K W' = finrank K W := (Submodule.comapSubtypeEquivOfLe hW).finrank_eq
  have hb := (tripleLinearOrbit_card_bounds U' V' W' hc hvw).2
  rw [hu',hv',hw'] at hb
  have hs := isotropic_finrank_le_half ω hω D hD S hS
  have hi := (isotropic_card_bounds ω h2 ha hω D hD (finrank K S) hs).2
  have hk : (2:ℝ)^(finrank K S) * 2^(finrank K S) ≤ 4^D := by
    calc
      _ = (4:ℝ)^(finrank K S) := by rw [←mul_pow]; norm_num
      _ ≤ _ := pow_le_pow_right₀ (by norm_num) hs
  rw [triple_subspace_orbit_card_identity ω h2 ha hω S U V W hS hU hV hW hsum,Nat.cast_mul]
  calc
    _ ≤ ((lagrangianConstant D*2^(finrank K S))*(Fintype.card K : ℝ)^isotropicExponent D (finrank K S)) *
      (2^(finrank K S)*(Fintype.card K : ℝ)^(2*(finrank K U*finrank K V+finrank K U*finrank K W+finrank K V*finrank K W))) :=
        mul_le_mul hi hb (Nat.cast_nonneg _) (by positivity)
    _ = (lagrangianConstant D*(2^(finrank K S)*2^(finrank K S))) * (Fintype.card K : ℝ)^(isotropicExponent D (finrank K S) +
        2*(finrank K U*finrank K V+finrank K U*finrank K W+finrank K V*finrank K W)) := by rw [pow_add]; ring
    _ ≤ _ := by gcongr

private instance certificate_instance_0289 : OAI.SidorenkoCounterexample.ProofCertificate_0289 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19 q20 q21 q22 q23
  exact @certificate_proof_0289 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19 q20 q21 q22 q23

end ConfigurationBound
section CommonZeroProfiles
variable {K E : Type} [Field K] [AddCommGroup E] [Module K E] [FiniteDimensional K E]
variable (ω : LinearMap.BilinForm K E)
variable [Finite E]
omit [FiniteDimensional K E] in
theorem certificate_proof_0290 (h2 : (2:K) ≠ 0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
    (L M N : SymplecticLagrangian ω) (h0 : (L.val ⊓ M.val) ⊓ N.val = ⊥) :
    ∃ f : CommonZeroDimProfile ω L M N →
      OrderedTripleOrbit ω (L.val ⊓ M.val) (L.val ⊓ N.val) (M.val ⊓ N.val) ×
      {P : SymplecticLagrangian ω // (L.val ⊓ M.val) ⊔ (L.val ⊓ N.val) ≤ P.val} ×
      {P : SymplecticLagrangian ω // (L.val ⊓ M.val) ⊔ (M.val ⊓ N.val) ≤ P.val} ×
      {P : SymplecticLagrangian ω // (L.val ⊓ N.val) ⊔ (M.val ⊓ N.val) ≤ P.val},
      Function.Injective f := by
  classical
  let O := OrderedTripleOrbit ω (L.val ⊓ M.val) (L.val ⊓ N.val) (M.val ⊓ N.val)
  have ht (p : CommonZeroDimProfile ω L M N) :
      TripleIsometry ω ω (L.val ⊓ M.val) (L.val ⊓ N.val) (M.val ⊓ N.val)
        (p.val.1.val ⊓ p.val.2.1.val) (p.val.1.val ⊓ p.val.2.2.val) (p.val.2.1.val ⊓ p.val.2.2.val) := by
    have hd := triple_pairs_disjoint L.val M.val N.val h0
    have hd' := triple_pairs_disjoint p.val.1.val p.val.2.1.val p.val.2.2.val p.property.1
    exact triple_isotropic_config_transitivity ω h2 ha hω _ _ _ _ _ _
      (triplePairSum_isotropic ω _ _ _ L.property M.property N.property)
      (triplePairSum_isotropic ω _ _ _ p.val.1.property p.val.2.1.property p.val.2.2.property)
      hd.1 hd.2 hd'.1 hd'.2 p.property.2.1.symm p.property.2.2.1.symm p.property.2.2.2.symm
  let orb (p : CommonZeroDimProfile ω L M N) : O :=
    ⟨(p.val.1.val ⊓ p.val.2.1.val,p.val.1.val ⊓ p.val.2.2.val,p.val.2.1.val ⊓ p.val.2.2.val),ht p⟩
  let e (o : O) := o.property.choose
  have he (o : O) := o.property.choose_spec
  have hes (o : O) (x y : E) : ω ((e o).symm x) ((e o).symm y) = ω x y := by
    simpa only [e,LinearEquiv.apply_symm_apply] using ((he o).1 ((e o).symm x) ((e o).symm y)).symm
  let g (o : O) := lagrangianIsometryEquiv ω (e o).symm (hes o)
  have hg (o : O) (P : SymplecticLagrangian ω) : (g o P).val = P.val.map (e o).symm.toLinearMap := rfl
  have hpL (p : CommonZeroDimProfile ω L M N) :
      (L.val ⊓ M.val) ⊔ (L.val ⊓ N.val) ≤ (g (orb p) p.val.1).val := by
    rw [hg,←Submodule.orderIsoMapComap_symm_apply']
    apply (Submodule.orderIsoMapComap (e (orb p))).le_symm_apply.mpr
    change ((L.val ⊓ M.val) ⊔ (L.val ⊓ N.val)).map (e (orb p)).toLinearMap ≤ p.val.1.val
    rw [Submodule.map_sup,(he (orb p)).2.1,(he (orb p)).2.2.1]
    exact sup_le inf_le_left inf_le_left
  have hpM (p : CommonZeroDimProfile ω L M N) :
      (L.val ⊓ M.val) ⊔ (M.val ⊓ N.val) ≤ (g (orb p) p.val.2.1).val := by
    rw [hg,←Submodule.orderIsoMapComap_symm_apply']
    apply (Submodule.orderIsoMapComap (e (orb p))).le_symm_apply.mpr
    change ((L.val ⊓ M.val) ⊔ (M.val ⊓ N.val)).map (e (orb p)).toLinearMap ≤ p.val.2.1.val
    rw [Submodule.map_sup,(he (orb p)).2.1,(he (orb p)).2.2.2]
    exact sup_le inf_le_right inf_le_left
  have hpN (p : CommonZeroDimProfile ω L M N) :
      (L.val ⊓ N.val) ⊔ (M.val ⊓ N.val) ≤ (g (orb p) p.val.2.2).val := by
    rw [hg,←Submodule.orderIsoMapComap_symm_apply']
    apply (Submodule.orderIsoMapComap (e (orb p))).le_symm_apply.mpr
    change ((L.val ⊓ N.val) ⊔ (M.val ⊓ N.val)).map (e (orb p)).toLinearMap ≤ p.val.2.2.val
    rw [Submodule.map_sup,(he (orb p)).2.2.1,(he (orb p)).2.2.2]
    exact sup_le inf_le_right inf_le_right
  let f (p : CommonZeroDimProfile ω L M N) :=
    (orb p,(⟨g (orb p) p.val.1,hpL p⟩ : {P : SymplecticLagrangian ω // (L.val ⊓ M.val) ⊔ (L.val ⊓ N.val) ≤ P.val}),
      (⟨g (orb p) p.val.2.1,hpM p⟩ : {P : SymplecticLagrangian ω // (L.val ⊓ M.val) ⊔ (M.val ⊓ N.val) ≤ P.val}),
      (⟨g (orb p) p.val.2.2,hpN p⟩ : {P : SymplecticLagrangian ω // (L.val ⊓ N.val) ⊔ (M.val ⊓ N.val) ≤ P.val}))
  refine ⟨f,?_⟩
  intro p q hpq
  have ho : orb p = orb q := congrArg Prod.fst hpq
  have hL : g (orb p) p.val.1 = g (orb p) q.val.1 := by
    simpa only [f,ho] using congrArg (fun r => r.2.1.val) hpq
  have hM : g (orb p) p.val.2.1 = g (orb p) q.val.2.1 := by
    simpa only [f,ho] using congrArg (fun r => r.2.2.1.val) hpq
  have hN : g (orb p) p.val.2.2 = g (orb p) q.val.2.2 := by
    simpa only [f,ho] using congrArg (fun r => r.2.2.2.val) hpq
  exact Subtype.ext (Prod.ext ((g (orb p)).injective hL)
    (Prod.ext ((g (orb p)).injective hM) ((g (orb p)).injective hN)))

private instance certificate_instance_0290 : OAI.SidorenkoCounterexample.ProofCertificate_0290 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13
  exact @certificate_proof_0290 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13

end CommonZeroProfiles
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
theorem certificate_proof_0291 (D : ℕ) : 0 < profileMassConstant D := by
  unfold profileMassConstant
  have := lagrangianConstant_pos D
  positivity

private instance certificate_instance_0291 : OAI.SidorenkoCounterexample.ProofCertificate_0291 := by
  constructor
  intro q0
  exact @certificate_proof_0291 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 q0

theorem certificate_proof_0292 : Monotone profileMassConstant := by
  intro a b hab
  unfold profileMassConstant
  exact mul_le_mul (pow_le_pow_left₀ (le_of_lt (lagrangianConstant_pos a)) (lagrangianConstant_mono hab) 4)
    (pow_le_pow_right₀ (by norm_num) hab) (by positivity) (by positivity)

private instance certificate_instance_0292 : OAI.SidorenkoCounterexample.ProofCertificate_0292 := by
  constructor
  exact @certificate_proof_0292 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40

section CommonZeroMass
variable {K E : Type} [Field K] [AddCommGroup E] [Module K E] [Fintype K] [Finite E]
variable (ω : LinearMap.BilinForm K E)
theorem certificate_proof_0293 (h2 : (2:K) ≠ 0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
    (D : ℕ) (hD : 2*D = finrank K E)
    (L M N : SymplecticLagrangian ω) (h0 : (L.val ⊓ M.val) ⊓ N.val = ⊥) :
    (Fintype.card K : ℝ)^((finrank K ↥(L.val ⊓ M.val)+1).choose 2 +
      (finrank K ↥(L.val ⊓ N.val)+1).choose 2 + (finrank K ↥(M.val ⊓ N.val)+1).choose 2) *
      Nat.card (CommonZeroDimProfile ω L M N) ≤ profileMassConstant D * (Fintype.card K : ℝ)^(3*(D+1).choose 2) := by
  have hconst := lagrangianConstant_pos D
  let u := finrank K ↥(L.val ⊓ M.val)
  let v := finrank K ↥(L.val ⊓ N.val)
  let w := finrank K ↥(M.val ⊓ N.val)
  let S := triplePairSum L.val M.val N.val
  let A := (L.val ⊓ M.val) ⊔ (L.val ⊓ N.val)
  let B := (L.val ⊓ M.val) ⊔ (M.val ⊓ N.val)
  let C := (L.val ⊓ N.val) ⊔ (M.val ⊓ N.val)
  have hA : A ≤ L.val := sup_le inf_le_left inf_le_left
  have hB : B ≤ M.val := sup_le inf_le_right inf_le_left
  have hC : C ≤ N.val := sup_le inf_le_right inf_le_right
  have his (P : SymplecticLagrangian ω) (T : Submodule K E) (hT : T ≤ P.val) : T ≤ ω.orthogonal T := by
    intro x hx y hy
    exact P.property.ge (hT hx) y (hT hy)
  have hd := triple_pairs_disjoint L.val M.val N.val h0
  have hdimA : finrank K A = u+v := finrank_sup_of_disjoint _ _ (hd.1.mono_right le_sup_left)
  have hdimB : finrank K B = u+w := finrank_sup_of_disjoint _ _ (hd.1.mono_right le_sup_right)
  have hdimC : finrank K C = v+w := finrank_sup_of_disjoint _ _ hd.2
  have hdim : finrank K S = u+v+w := triplePairSum_finrank L.val M.val N.val h0
  have hs : S ≤ ω.orthogonal S := triplePairSum_isotropic ω _ _ _ L.property M.property N.property
  have haD : u+v+w ≤ D := hdim ▸ isotropic_finrank_le_half ω hω D hD S hs
  have hc := triple_isotropic_orbit_card_upper ω h2 ha hω D hD S
    (L.val ⊓ M.val) (L.val ⊓ N.val) (M.val ⊓ N.val) hs
    (le_sup_of_le_left le_sup_left) (le_sup_of_le_left le_sup_right) le_sup_right rfl hd.1 hd.2
  rw [hdim] at hc
  have hcont (P : SymplecticLagrangian ω) (T : Submodule K E) (hT : T ≤ P.val) :
      (Nat.card {Q : SymplecticLagrangian ω // T ≤ Q.val} : ℝ) ≤
        lagrangianConstant D * (Fintype.card K : ℝ)^((D-finrank K T+1).choose 2) :=
    ((containingLagrangian_card_bounds ω h2 ha hω D hD T (his P T hT)).2).trans
      (mul_le_mul_of_nonneg_right (lagrangianConstant_mono (Nat.sub_le _ _)) (by positivity))
  have h₁ := hcont L A hA
  have h₂ := hcont M B hB
  have h₃ := hcont N C hC
  rw [hdimA] at h₁
  rw [hdimB] at h₂
  rw [hdimC] at h₃
  obtain ⟨f,hf⟩ := commonZeroProfile_injection ω h2 ha hω L M N h0
  have hcard : (Nat.card (CommonZeroDimProfile ω L M N) : ℝ) ≤
      Nat.card (OrderedTripleOrbit ω (L.val ⊓ M.val) (L.val ⊓ N.val) (M.val ⊓ N.val)) *
        ((Nat.card {Q : SymplecticLagrangian ω // A ≤ Q.val} : ℝ) *
          (Nat.card {Q : SymplecticLagrangian ω // B ≤ Q.val} * Nat.card {Q : SymplecticLagrangian ω // C ≤ Q.val})) := by
    have hh := Nat.card_le_card_of_injective f hf
    rw [Nat.card_prod,Nat.card_prod,Nat.card_prod] at hh
    exact_mod_cast hh
  have hb : (Nat.card (CommonZeroDimProfile ω L M N) : ℝ) ≤
      profileMassConstant D * (Fintype.card K : ℝ)^(isotropicExponent D (u+v+w)+2*(u*v+u*w+v*w)+
        ((D-(u+v)+1).choose 2+(D-(u+w)+1).choose 2+(D-(v+w)+1).choose 2)) := by
    calc
      _ ≤ _ := hcard
      _ ≤ ((lagrangianConstant D*4^D)*(Fintype.card K : ℝ)^(isotropicExponent D (u+v+w)+2*(u*v+u*w+v*w))) *
        ((lagrangianConstant D*(Fintype.card K : ℝ)^((D-(u+v)+1).choose 2))*
          ((lagrangianConstant D*(Fintype.card K : ℝ)^((D-(u+w)+1).choose 2))*
            (lagrangianConstant D*(Fintype.card K : ℝ)^((D-(v+w)+1).choose 2)))) := by
          gcongr
      _ = _ := by unfold profileMassConstant; simp only [pow_add]; ring
  have hh := mul_le_mul_of_nonneg_right hb
    (show 0 ≤ (Fintype.card K : ℝ)^((u+1).choose 2+(v+1).choose 2+(w+1).choose 2) by positivity)
  rw [mul_assoc,←pow_add,pair_cost_cancellation D u v w haD] at hh
  simpa only [mul_comm] using hh

private instance certificate_instance_0293 : OAI.SidorenkoCounterexample.ProofCertificate_0293 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16
  exact @certificate_proof_0293 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16

end CommonZeroMass
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
section ProfileQuotient
variable {K E : Type} [Field K] [AddCommGroup E] [Module K E] [FiniteDimensional K E]
variable (ω : LinearMap.BilinForm K E)
theorem certificate_proof_0294 (S : Submodule K E) (P Q : SymplecticLagrangian ω)
    (hSP : S ≤ P.val) (hSQ : S ≤ Q.val) :
    finrank K ↥(reduceSubspace ω S P.val ⊓ reduceSubspace ω S Q.val) =
      finrank K ↥(P.val ⊓ Q.val)-finrank K S := by
  rw [←reduceSubspace_inf ω S P.val Q.val hSP]
  have hh := reduceSubspace_finrank_containing ω S (P.val ⊓ Q.val) (le_inf hSP hSQ)
    (inf_le_left.trans (lagrangian_le_orthogonal ω S P.val P.property hSP))
  omega

private instance certificate_instance_0294 : OAI.SidorenkoCounterexample.ProofCertificate_0294 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11
  exact @certificate_proof_0294 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11

omit [FiniteDimensional K E] in
theorem certificate_proof_0295 (S : Submodule K E) :
    Function.Injective (fun P : {P : SymplecticLagrangian ω // S ≤ P.val} => reduceSubspace ω S P.val.val) := by
  intro P Q h
  apply Subtype.ext
  apply Subtype.ext
  have hh := congrArg (liftReduction ω S) h
  simpa only [lift_reduce ω S P.val.val P.property (lagrangian_le_orthogonal ω S P.val.val P.val.property P.property),
    lift_reduce ω S Q.val.val Q.property (lagrangian_le_orthogonal ω S Q.val.val Q.val.property Q.property)] using hh

private instance certificate_instance_0295 : OAI.SidorenkoCounterexample.ProofCertificate_0295 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6
  exact @certificate_proof_0295 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 q0 q1 q2 q3 q4 q5 q6

end ProfileQuotient
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
open scoped BigOperators
section AllProfileMass
variable {K E : Type} [Field K] [AddCommGroup E] [Module K E] [Fintype K] [Finite E]
variable (ω : LinearMap.BilinForm K E)
end AllProfileMass
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
open scoped BigOperators
section GeneralPairCounts
variable {K E : Type} [Field K] [AddCommGroup E] [Module K E] [Fintype K] [Finite E]
variable (ω : LinearMap.BilinForm K E)
end GeneralPairCounts
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
section ConditionalProfile
variable {K E : Type} [Field K] [AddCommGroup E] [Module K E] [FiniteDimensional K E]
variable (ω : LinearMap.BilinForm K E)
variable [Finite E]
variable [Fintype K]
end ConditionalProfile
end SidorenkoCounterexample
end OAI

theorem solution : OAI.SidorenkoCounterexample.ProofCertificate_0277 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0278 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0279 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0280 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0281 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0282 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0283 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0284 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0285 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0286 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0287 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0288 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0289 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0290 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0291 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0292 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0293 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0294 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0295 := by
  exact ⟨inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance⟩
end

