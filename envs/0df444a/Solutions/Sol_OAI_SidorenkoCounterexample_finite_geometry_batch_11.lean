-- Prove2me | solution 1 for OAI.SidorenkoCounterexample.finite_geometry_batch_11
-- status  : ACCEPTED   (prove)
-- author  : @abcdefg
-- created : 2026-10-09T06:01:52.967055+00:00
-- url     : https://prove2.me/submissions/dce0e111-691b-4026-8aba-a95754dac4d9

import Definitions.Def_SidorenkoFiniteGeometryCertificates08
set_option linter.unusedVariables false
section
variable [p0 : OAI.SidorenkoCounterexample.ProofCertificate_0012]
  [p1 : OAI.SidorenkoCounterexample.ProofCertificate_0029]
  [p2 : OAI.SidorenkoCounterexample.ProofCertificate_0030]
  [p3 : OAI.SidorenkoCounterexample.ProofCertificate_0107]
  [p4 : OAI.SidorenkoCounterexample.ProofCertificate_0108]
  [p5 : OAI.SidorenkoCounterexample.ProofCertificate_0112]
  [p6 : OAI.SidorenkoCounterexample.ProofCertificate_0125]
  [p7 : OAI.SidorenkoCounterexample.ProofCertificate_0127]
  [p8 : OAI.SidorenkoCounterexample.ProofCertificate_0137]
  [p9 : OAI.SidorenkoCounterexample.ProofCertificate_0139]
  [p10 : OAI.SidorenkoCounterexample.ProofCertificate_0172]
  [p11 : OAI.SidorenkoCounterexample.ProofCertificate_0181]
  [p12 : OAI.SidorenkoCounterexample.ProofCertificate_0207]
  [p13 : OAI.SidorenkoCounterexample.ProofCertificate_0216]
  [p14 : OAI.SidorenkoCounterexample.ProofCertificate_0217]
  [p15 : OAI.SidorenkoCounterexample.ProofCertificate_0219]
  [p16 : OAI.SidorenkoCounterexample.ProofCertificate_0220]
  [p17 : OAI.SidorenkoCounterexample.ProofCertificate_0221]
  [p18 : OAI.SidorenkoCounterexample.ProofCertificate_0226]
  [p19 : OAI.SidorenkoCounterexample.ProofCertificate_0228]
  [p20 : OAI.SidorenkoCounterexample.ProofCertificate_0238]
  [p21 : OAI.SidorenkoCounterexample.ProofCertificate_0241]
  [p22 : OAI.SidorenkoCounterexample.ProofCertificate_0242]
  [p23 : OAI.SidorenkoCounterexample.ProofCertificate_0243]
  [p24 : OAI.SidorenkoCounterexample.ProofCertificate_0249]
  [p25 : OAI.SidorenkoCounterexample.ProofCertificate_0251]
  [p26 : OAI.SidorenkoCounterexample.ProofCertificate_0255]
include p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26

namespace OAI
namespace SidorenkoCounterexample
open Module
section PairSpaceFacts
variable {K E : Type} [Field K] [AddCommGroup E] [Module K E]
end PairSpaceFacts
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
section GenericTransverseMass
variable {K E F : Type} [Field K]
  [AddCommGroup E] [Module K E] [AddCommGroup F] [Module K F]
variable [Fintype K] [Finite E]
variable (ω : LinearMap.BilinForm K E)
end GenericTransverseMass
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
section ResidualTransversality
variable {K E : Type} [Field K] [AddCommGroup E] [Module K E]
variable (ω : LinearMap.BilinForm K E)
end ResidualTransversality
section LagrangianTripleOrbit
variable {K E : Type} [Field K] [AddCommGroup E] [Module K E]
variable (ω : LinearMap.BilinForm K E) (L M N : SymplecticLagrangian ω)
end LagrangianTripleOrbit
section AvoidanceTripleCount
variable {K E : Type} [Field K] [AddCommGroup E] [Module K E]
  [Fintype K] [Finite E]
variable (ω : LinearMap.BilinForm K E) (S : Submodule K E)
variable (ha : ω.IsAlt) (hω : ω.Nondegenerate) (hS : S ≤ ω.orthogonal S)
end AvoidanceTripleCount
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
section AvoidanceTripleBound
variable {K E : Type} [Field K] [AddCommGroup E] [Module K E]
  [Fintype K] [Finite E] [Invertible (2 : K)]
variable (ω : LinearMap.BilinForm K E) (S : Submodule K E)
theorem certificate_proof_0256 (ha : ω.IsAlt) (hω : ω.Nondegenerate)
    (hS : S ≤ ω.orthogonal S) (D : ℕ) (hD : 2*D = finrank K E)
    (hq : 4 * lagrangianConstant D ≤ (Fintype.card K : ℝ))
    (A B C : Submodule K E) (hA : A ≤ S) (hB : B ≤ S) (hC : C ≤ S)
    (L M N : SymplecticLagrangian (symplecticReductionForm ω S ha))
    (hLM : L.val ⊓ M.val = ⊥) (hLN : L.val ⊓ N.val = ⊥) (hMN : M.val ⊓ N.val = ⊥) :
    (Nat.card {L : SymplecticLagrangian ω // A ≤ L.val} : ℝ) *
      (Nat.card {L : SymplecticLagrangian ω // B ≤ L.val} *
        Nat.card {L : SymplecticLagrangian ω // C ≤ L.val}) ≤
      (8 * (4^D * lagrangianConstant D^2)) * Nat.card (AvoidanceOrbitFiber ω S ha A B C L M N) := by
  have h2 := (isUnit_of_invertible (2 : K)).ne_zero
  have h₁ : (Nat.card {L : SymplecticLagrangian ω // A ≤ L.val} : ℝ) ≤
      2*Nat.card (AvoidanceSpace ω S A) := by
    exact_mod_cast avoidance_card_lower ω h2 ha hω D hD A S hA hS hq
  have h₂ : (Nat.card {L : SymplecticLagrangian ω // B ≤ L.val} : ℝ) ≤
      2*Nat.card (AvoidanceSpace ω S B) := by
    exact_mod_cast avoidance_card_lower ω h2 ha hω D hD B S hB hS hq
  have h₃ : (Nat.card {L : SymplecticLagrangian ω // C ≤ L.val} : ℝ) ≤
      2*Nat.card (AvoidanceSpace ω S C) := by
    exact_mod_cast avoidance_card_lower ω h2 ha hω D hD C S hC hS hq
  have hr := reducedSpace_finrank ω S hω hS
  have hs := isotropic_finrank_le_half ω hω D hD S hS
  have hb := avoidanceOrbitFiber_card_lower ω S ha hω hS (D-finrank K S) (by omega)
    A B C hA hB hC L M N hLM hLN hMN
  have hk : (4:ℝ)^(D-finrank K S) * lagrangianConstant (D-finrank K S)^2 ≤
      4^D * lagrangianConstant D^2 := by
    gcongr
    · norm_num
    · exact Nat.sub_le D _
    · exact le_of_lt (lagrangianConstant_pos _)
    · exact lagrangianConstant_mono (Nat.sub_le D _)
  calc
    _ ≤ ((2:ℝ)*Nat.card (AvoidanceSpace ω S A)) *
      ((2*Nat.card (AvoidanceSpace ω S B)) * (2*Nat.card (AvoidanceSpace ω S C))) := by gcongr
    _ = 8 * ((Nat.card (AvoidanceSpace ω S A) : ℝ) *
      (Nat.card (AvoidanceSpace ω S B) * Nat.card (AvoidanceSpace ω S C))) := by ring
    _ ≤ 8 * (((4:ℝ)^(D-finrank K S) * lagrangianConstant (D-finrank K S)^2) *
      Nat.card (AvoidanceOrbitFiber ω S ha A B C L M N)) := mul_le_mul_of_nonneg_left hb (by norm_num)
    _ ≤ 8 * ((4^D * lagrangianConstant D^2) *
      Nat.card (AvoidanceOrbitFiber ω S ha A B C L M N)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hk (by positivity)) (by norm_num)
    _ = _ := by ring

private instance certificate_instance_0256 : OAI.SidorenkoCounterexample.ProofCertificate_0256 := by
  constructor
  intro c0 c1 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19 q20 q21 q22 q23 q24 q25 q26 q27
  exact @certificate_proof_0256 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19 q20 q21 q22 q23 q24 q25 q26 q27

end AvoidanceTripleBound
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
section IsotropicExtension
variable {K E : Type} [Field K] [AddCommGroup E] [Module K E]
  [FiniteDimensional K E] [Finite E]
variable (ω : LinearMap.BilinForm K E)
theorem certificate_proof_0257 (h2 : (2 : K) ≠ 0) (ha : ω.IsAlt)
    (hω : ω.Nondegenerate) (S T : Submodule K E)
    (hS : S ≤ ω.orthogonal S) (hT : T ≤ ω.orthogonal T) (g : S ≃ₗ[K] T) :
    ∃ e : E ≃ₗ[K] E, (∀ x y, ω (e x) (e y) = ω x y) ∧
      ∀ x : S, e x.val = (g x).val := by
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
  let g₀ : U ≃ₗ[K] W := (Submodule.comapSubtypeEquivOfLe hSL).trans
    (g.trans (Submodule.comapSubtypeEquivOfLe hTM).symm)
  obtain ⟨f,hf⟩ := exists_linearEquiv_extension U W hdim g₀
  let c : (L × Module.Dual K L) ≃ₗ[K] (M × Module.Dual K M) := f.prodCongr f.symm.dualMap
  have hc (x y : L × Module.Dual K L) :
      canonicalSymplectic (c x) (c y) = canonicalSymplectic x y := by
    simp [c,canonicalSymplectic_apply]
  let e := eL.symm.trans (c.trans eM)
  have he (l : L) : e l.val = (f l).val := by
    change eM (c (eL.symm l.val)) = (f l).val
    rw [←hEL l,eL.symm_apply_apply]
    simpa [c] using hEM (f l)
  refine ⟨e,?_,?_⟩
  · intro x y
    change ω (eM (c (eL.symm x))) (eM (c (eL.symm y))) = ω x y
    rw [hωM,hc,←hωL,eL.apply_symm_apply,eL.apply_symm_apply]
  · intro x
    let u : U := ⟨⟨x.val,hSL x.property⟩,x.property⟩
    change e u.val.val = (g x).val
    rw [he,hf u]
    rfl

private instance certificate_instance_0257 : OAI.SidorenkoCounterexample.ProofCertificate_0257 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15
  exact @certificate_proof_0257 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15

end IsotropicExtension
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
section FixedPairs
variable {K E : Type} [Field K] [AddCommGroup E] [Module K E]
variable (ω : LinearMap.BilinForm K E) (L M N : SymplecticLagrangian ω)
theorem certificate_proof_0258 (P Q R : Submodule K E) :
    (P ⊓ triplePairSum P Q R) ⊓ (Q ⊓ triplePairSum P Q R) = P ⊓ Q := by
  apply le_antisymm (inf_le_inf inf_le_left inf_le_left)
  intro x hx
  have hs : x ∈ triplePairSum P Q R :=
    (show P ⊓ Q ≤ triplePairSum P Q R from le_sup_left.trans le_sup_left) hx
  exact ⟨⟨hx.1,hs⟩,⟨hx.2,hs⟩⟩

private instance certificate_instance_0258 : OAI.SidorenkoCounterexample.ProofCertificate_0258 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7
  exact @certificate_proof_0258 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 q0 q1 q2 q3 q4 q5 q6 q7

theorem certificate_proof_0259 (P Q R : Submodule K E) :
    let S := triplePairSum P Q R
    ((P ⊓ S) ⊔ (Q ⊓ S) = S) ∧ ((P ⊓ S) ⊔ (R ⊓ S) = S) ∧
      ((Q ⊓ S) ⊔ (R ⊓ S) = S) := by
  dsimp only
  have h₁ : triplePairSum P R Q = triplePairSum P Q R := by unfold triplePairSum; ac_rfl
  have h₂ : triplePairSum Q R P = triplePairSum P Q R := by unfold triplePairSum; ac_rfl
  exact ⟨triplePairSum_split P Q R,by simpa only [h₁] using triplePairSum_split P R Q,
    by simpa only [h₂] using triplePairSum_split Q R P⟩

private instance certificate_instance_0259 : OAI.SidorenkoCounterexample.ProofCertificate_0259 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7
  exact @certificate_proof_0259 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 q0 q1 q2 q3 q4 q5 q6 q7

theorem certificate_proof_0260 (P Q R : Submodule K E) :
    let S := triplePairSum P Q R
    ((P ⊓ S) ⊓ (Q ⊓ S) = P ⊓ Q) ∧ ((P ⊓ S) ⊓ (R ⊓ S) = P ⊓ R) ∧
      ((Q ⊓ S) ⊓ (R ⊓ S) = Q ⊓ R) := by
  dsimp only
  have h₁ : triplePairSum P R Q = triplePairSum P Q R := by unfold triplePairSum; ac_rfl
  have h₂ : triplePairSum Q R P = triplePairSum P Q R := by unfold triplePairSum; ac_rfl
  exact ⟨triplePair_inter_own P Q R,by simpa only [h₁] using triplePair_inter_own P R Q,
    by simpa only [h₂] using triplePair_inter_own Q R P⟩

private instance certificate_instance_0260 : OAI.SidorenkoCounterexample.ProofCertificate_0260 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7
  exact @certificate_proof_0260 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 q0 q1 q2 q3 q4 q5 q6 q7

variable [FiniteDimensional K E]
variable (ha : ω.IsAlt) (hω : ω.Nondegenerate)
theorem certificate_proof_0261 (p : OwnAvoidanceOrbitFiber ω L M N ha hω) :
    p.val.1.val ⊓ p.val.2.1.val = L.val ⊓ M.val ∧
    p.val.1.val ⊓ p.val.2.2.val = L.val ⊓ N.val ∧
    p.val.2.1.val ⊓ p.val.2.2.val = M.val ⊓ N.val := by
  let S := triplePairSum L.val M.val N.val
  have hs := triplePairSum_split_all L.val M.val N.val
  have hi := triplePair_inter_all L.val M.val N.val
  have ht := triplePairSum_reductions_transverse ω L.val M.val N.val L.property M.property N.property
  obtain ⟨e,he,h₁,h₂,h₃⟩ := p.property
  dsimp only [tripleResidualLagrangian] at h₁ h₂ h₃
  have hp₁ : reduceSubspace ω S p.val.1.val ⊓ reduceSubspace ω S p.val.2.1.val = ⊥ := by
    rw [←h₁,←h₂,←Submodule.map_inf e.toLinearMap e.injective,ht.1,Submodule.map_bot]
  have hp₂ : reduceSubspace ω S p.val.1.val ⊓ reduceSubspace ω S p.val.2.2.val = ⊥ := by
    rw [←h₁,←h₃,←Submodule.map_inf e.toLinearMap e.injective,ht.2.1,Submodule.map_bot]
  have hp₃ : reduceSubspace ω S p.val.2.1.val ⊓ reduceSubspace ω S p.val.2.2.val = ⊥ := by
    rw [←h₂,←h₃,←Submodule.map_inf e.toLinearMap e.injective,ht.2.2,Submodule.map_bot]
  refine ⟨?_,?_,?_⟩
  · exact (avoidance_exact_intersection ω S _ _ _ _ p.val.1.property.1 p.val.2.1.property.1
      p.val.1.property.2 p.val.2.1.property.2 hs.1 hp₁).trans hi.1
  · exact (avoidance_exact_intersection ω S _ _ _ _ p.val.1.property.1 p.val.2.2.property.1
      p.val.1.property.2 p.val.2.2.property.2 hs.2.1 hp₂).trans hi.2.1
  · exact (avoidance_exact_intersection ω S _ _ _ _ p.val.2.1.property.1 p.val.2.2.property.1
      p.val.2.1.property.2 p.val.2.2.property.2 hs.2.2 hp₃).trans hi.2.2

private instance certificate_instance_0261 : OAI.SidorenkoCounterexample.ProofCertificate_0261 := by
  constructor
  intro c0 c1 c2 c3 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12
  exact @certificate_proof_0261 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12

end FixedPairs
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
section ConfigurationOrbit
variable {K E : Type} [Field K] [AddCommGroup E] [Module K E]
variable (ω : LinearMap.BilinForm K E)
theorem certificate_proof_0262 (S T U : Submodule K E) (hU : U ≤ S)
    (e : E ≃ₗ[K] E) (g : S ≃ₗ[K] T) (he : ∀ x : S, e x.val = (g x).val) :
    U.map e.toLinearMap = ((U.comap S.subtype).map g.toLinearMap).map T.subtype := by
  ext x
  constructor
  · rintro ⟨y,hy,rfl⟩
    exact ⟨g ⟨y,hU hy⟩,⟨⟨y,hU hy⟩,hy,rfl⟩,(he ⟨y,hU hy⟩).symm⟩
  · rintro ⟨y,⟨z,hz,rfl⟩,rfl⟩
    exact ⟨z.val,hz,he z⟩

private instance certificate_instance_0262 : OAI.SidorenkoCounterexample.ProofCertificate_0262 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11
  exact @certificate_proof_0262 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11

theorem certificate_proof_0263 (S U : Submodule K E) (hU : U ≤ S) :
    (U.comap S.subtype).map S.subtype = U := by
  ext x
  exact ⟨fun ⟨y,hy,hyx⟩ => hyx ▸ hy,fun hx => ⟨⟨x,hU hx⟩,hx,rfl⟩⟩

private instance certificate_instance_0263 : OAI.SidorenkoCounterexample.ProofCertificate_0263 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7
  exact @certificate_proof_0263 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 q0 q1 q2 q3 q4 q5 q6 q7

theorem certificate_proof_0264 (S U V : Submodule K E) (hU : U ≤ S) (hV : V ≤ S) :
    (U ⊔ V).comap S.subtype = U.comap S.subtype ⊔ V.comap S.subtype := by
  apply Submodule.map_injective_of_injective S.subtype_injective
  rw [Submodule.map_sup,subtype_map_comap_of_le S U hU,subtype_map_comap_of_le S V hV,
    subtype_map_comap_of_le S (U ⊔ V) (sup_le hU hV)]

private instance certificate_instance_0264 : OAI.SidorenkoCounterexample.ProofCertificate_0264 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9
  exact @certificate_proof_0264 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9

variable [FiniteDimensional K E] [Finite E]
theorem certificate_proof_0265 (h2 : (2:K) ≠ 0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
    (S U V W : Submodule K E) (hS : S ≤ ω.orthogonal S)
    (hU : U ≤ S) (hV : V ≤ S) (hW : W ≤ S) (hsum : U ⊔ V ⊔ W = S) :
    ∃ f : IsotropicDimspace ω (finrank K S) ×
      TripleLinearOrbit (U.comap S.subtype) (V.comap S.subtype) (W.comap S.subtype) →
        OrderedTripleOrbit ω U V W, Function.Injective f := by
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
  have hsum' (p : TripleLinearOrbit (U.comap S.subtype) (V.comap S.subtype) (W.comap S.subtype)) :
      p.val.1 ⊔ p.val.2.1 ⊔ p.val.2.2 = ⊤ := by
    obtain ⟨g,hgU,hgV,hgW⟩ := p.property
    rw [←hgU,←hgV,←hgW,←Submodule.map_sup,←Submodule.map_sup,
      ←subspace_comap_sup_of_le S U V hU hV,
      ←subspace_comap_sup_of_le S (U ⊔ V) W (sup_le hU hV) hW,hsum]
    simp
  have hrecover (p) : (f p).val.1 ⊔ (f p).val.2.1 ⊔ (f p).val.2.2 = p.1.val := by
    change ((p.2.val.1.map S.subtype).map (e p.1).toLinearMap) ⊔
      ((p.2.val.2.1.map S.subtype).map (e p.1).toLinearMap) ⊔
      ((p.2.val.2.2.map S.subtype).map (e p.1).toLinearMap) = _
    rw [←Submodule.map_sup,←Submodule.map_sup,←Submodule.map_sup,←Submodule.map_sup,hsum']
    simpa only [Submodule.map_top,Submodule.range_subtype] using (he p.1).2
  refine ⟨f,?_⟩
  rintro ⟨T,p⟩ ⟨T',p'⟩ h
  have hT : T = T' := by
    apply Subtype.ext
    exact (hrecover (T,p)).symm.trans ((congrArg (fun x : OrderedTripleOrbit ω U V W =>
      x.val.1 ⊔ x.val.2.1 ⊔ x.val.2.2) h).trans (hrecover (T',p')))
  subst T'
  have hv := congrArg Subtype.val h
  have hinj := (Submodule.map_injective_of_injective (e T).injective).comp
    (Submodule.map_injective_of_injective S.subtype_injective)
  have hp : p = p' := Subtype.ext (Prod.ext (hinj (congrArg Prod.fst hv))
    (Prod.ext (hinj (congrArg (fun x => x.2.1) hv)) (hinj (congrArg (fun x => x.2.2) hv))))
  subst p'
  rfl

private instance certificate_instance_0265 : OAI.SidorenkoCounterexample.ProofCertificate_0265 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19
  exact @certificate_proof_0265 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19

end ConfigurationOrbit
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
section PairOrbitAssembly
variable {K E : Type} [Field K] [AddCommGroup E] [Module K E]
variable (ω : LinearMap.BilinForm K E) (L M N : SymplecticLagrangian ω)
theorem certificate_proof_0266 :
    ∃ f : OrderedTripleOrbit ω (L.val ⊓ M.val) (L.val ⊓ N.val) (M.val ⊓ N.val) ×
      FixedPairTripleOrbit ω L M N → OrderedTripleOrbit ω L.val M.val N.val,
      Function.Injective f := by
  classical
  let e (p : OrderedTripleOrbit ω (L.val ⊓ M.val) (L.val ⊓ N.val) (M.val ⊓ N.val)) :=
    p.property.choose
  have he (p : OrderedTripleOrbit ω (L.val ⊓ M.val) (L.val ⊓ N.val) (M.val ⊓ N.val)) := p.property.choose_spec
  have hgood (p : OrderedTripleOrbit ω (L.val ⊓ M.val) (L.val ⊓ N.val) (M.val ⊓ N.val))
      (q : FixedPairTripleOrbit ω L M N) :
      TripleIsometry ω ω L.val M.val N.val (q.val.val.1.val.map (e p).toLinearMap)
        (q.val.val.2.1.val.map (e p).toLinearMap) (q.val.val.2.2.val.map (e p).toLinearMap) := by
    obtain ⟨g,hg,hgL,hgM,hgN⟩ := q.val.property
    refine ⟨g.trans (e p),?_,?_,?_,?_⟩
    · intro x y
      exact ((he p).1 (g x) (g y)).trans (hg x y)
    · rw [submodule_map_trans,hgL]
    · rw [submodule_map_trans,hgM]
    · rw [submodule_map_trans,hgN]
  let f : OrderedTripleOrbit ω (L.val ⊓ M.val) (L.val ⊓ N.val) (M.val ⊓ N.val) ×
      FixedPairTripleOrbit ω L M N → OrderedTripleOrbit ω L.val M.val N.val := fun p =>
    ⟨(p.2.val.val.1.val.map (e p.1).toLinearMap,
      p.2.val.val.2.1.val.map (e p.1).toLinearMap,
      p.2.val.val.2.2.val.map (e p.1).toLinearMap),hgood p.1 p.2⟩
  have hrec (p) : ((f p).val.1 ⊓ (f p).val.2.1,
      (f p).val.1 ⊓ (f p).val.2.2,(f p).val.2.1 ⊓ (f p).val.2.2) = p.1.val := by
    change ((p.2.val.val.1.val.map (e p.1).toLinearMap) ⊓ (p.2.val.val.2.1.val.map (e p.1).toLinearMap),
      (p.2.val.val.1.val.map (e p.1).toLinearMap) ⊓ (p.2.val.val.2.2.val.map (e p.1).toLinearMap),
      (p.2.val.val.2.1.val.map (e p.1).toLinearMap) ⊓ (p.2.val.val.2.2.val.map (e p.1).toLinearMap)) = _
    rw [←Submodule.map_inf (e p.1).toLinearMap (e p.1).injective,
      ←Submodule.map_inf (e p.1).toLinearMap (e p.1).injective,
      ←Submodule.map_inf (e p.1).toLinearMap (e p.1).injective,
      p.2.property.1,p.2.property.2.1,p.2.property.2.2,
      (he p.1).2.1,(he p.1).2.2.1,(he p.1).2.2.2]
  refine ⟨f,?_⟩
  rintro ⟨p,q⟩ ⟨p',q'⟩ h
  have hp : p = p' := by
    apply Subtype.ext
    exact (hrec (p,q)).symm.trans ((congrArg (fun x : OrderedTripleOrbit ω L.val M.val N.val =>
      (x.val.1 ⊓ x.val.2.1,x.val.1 ⊓ x.val.2.2,x.val.2.1 ⊓ x.val.2.2)) h).trans (hrec (p',q')))
  subst p'
  have hv := congrArg Subtype.val h
  have hinj := Submodule.map_injective_of_injective (e p).injective
  have hq : q = q' := Subtype.ext (Subtype.ext
    (Prod.ext (Subtype.ext (hinj (congrArg Prod.fst hv)))
      (Prod.ext (Subtype.ext (hinj (congrArg (fun x => x.2.1) hv)))
        (Subtype.ext (hinj (congrArg (fun x => x.2.2) hv))))))
  subst q'
  rfl

private instance certificate_instance_0266 : OAI.SidorenkoCounterexample.ProofCertificate_0266 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8
  exact @certificate_proof_0266 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 q0 q1 q2 q3 q4 q5 q6 q7 q8

variable [Finite E]
theorem certificate_proof_0267 :
    Nat.card (OrderedTripleOrbit ω (L.val ⊓ M.val) (L.val ⊓ N.val) (M.val ⊓ N.val)) *
        Nat.card (FixedPairTripleOrbit ω L M N) ≤ Nat.card (OrderedTripleOrbit ω L.val M.val N.val) := by
  obtain ⟨f,hf⟩ := fullTripleOrbit_fixedPair_injection ω L M N
  simpa only [Nat.card_prod] using Nat.card_le_card_of_injective f hf

private instance certificate_instance_0267 : OAI.SidorenkoCounterexample.ProofCertificate_0267 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9
  exact @certificate_proof_0267 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9

end PairOrbitAssembly
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
section ConfigurationCount
variable {K E : Type} [Field K] [AddCommGroup E] [Module K E]
  [Fintype K] [Finite E]
variable (ω : LinearMap.BilinForm K E)
theorem certificate_proof_0268 (h2 : (2:K) ≠ 0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
    (D : ℕ) (hD : 2*D = finrank K E)
    (S U V W : Submodule K E) (hS : S ≤ ω.orthogonal S)
    (hU : U ≤ S) (hV : V ≤ S) (hW : W ≤ S) (hsum : U ⊔ V ⊔ W = S)
    (hdis : Disjoint U (V ⊔ W)) (hVW : Disjoint V W) :
    (Fintype.card K : ℝ)^(isotropicExponent D (finrank K S) +
      2*(finrank K U*finrank K V+finrank K U*finrank K W+finrank K V*finrank K W)) ≤
      (lagrangianConstant D * 2^D) * Nat.card (OrderedTripleOrbit ω U V W) := by
  let U' := U.comap S.subtype
  let V' := V.comap S.subtype
  let W' := W.comap S.subtype
  have hc : IsCompl U' (V' ⊔ W') := by
    constructor
    · apply disjoint_iff.mpr
      change U.comap S.subtype ⊓ (V.comap S.subtype ⊔ W.comap S.subtype) = ⊥
      rw [←subspace_comap_sup_of_le S V W hV hW,←Submodule.comap_inf,disjoint_iff.mp hdis]
      simp
    · apply codisjoint_iff.mpr
      change U.comap S.subtype ⊔ (V.comap S.subtype ⊔ W.comap S.subtype) = ⊤
      rw [←sup_assoc,←subspace_comap_sup_of_le S U V hU hV,
        ←subspace_comap_sup_of_le S (U ⊔ V) W (sup_le hU hV) hW,hsum]
      simp
  have hvw : Disjoint V' W' := by
    apply disjoint_iff.mpr
    change V.comap S.subtype ⊓ W.comap S.subtype = ⊥
    rw [←Submodule.comap_inf,disjoint_iff.mp hVW]
    simp
  have hu' : finrank K U' = finrank K U := (Submodule.comapSubtypeEquivOfLe hU).finrank_eq
  have hv' : finrank K V' = finrank K V := (Submodule.comapSubtypeEquivOfLe hV).finrank_eq
  have hw' : finrank K W' = finrank K W := (Submodule.comapSubtypeEquivOfLe hW).finrank_eq
  have hb := (tripleLinearOrbit_card_bounds U' V' W' hc hvw).1
  rw [hu',hv',hw'] at hb
  have hs := isotropic_finrank_le_half ω hω D hD S hS
  have hi := (isotropic_card_bounds ω h2 ha hω D hD (finrank K S) hs).1
  obtain ⟨f,hf⟩ := triple_subspace_orbit_injection ω h2 ha hω S U V W hS hU hV hW hsum
  have hcard : (Nat.card (IsotropicDimspace ω (finrank K S)) : ℝ)*
      Nat.card (TripleLinearOrbit U' V' W') ≤ Nat.card (OrderedTripleOrbit ω U V W) := by
    have hh := Nat.card_le_card_of_injective f hf
    rw [Nat.card_prod] at hh
    exact_mod_cast hh
  have hk : lagrangianConstant (D-finrank K S) * (2:ℝ)^(finrank K S) ≤ lagrangianConstant D * 2^D := by
    exact mul_le_mul (lagrangianConstant_mono (Nat.sub_le D _))
      (pow_le_pow_right₀ (by norm_num) hs) (by positivity)
      (le_of_lt (lagrangianConstant_pos D))
  calc
    _ = (Fintype.card K : ℝ)^isotropicExponent D (finrank K S) *
      (Fintype.card K : ℝ)^(2*(finrank K U*finrank K V+finrank K U*finrank K W+finrank K V*finrank K W)) := by rw [pow_add]
    _ ≤ (lagrangianConstant (D-finrank K S)*Nat.card (IsotropicDimspace ω (finrank K S))) *
      (2^(finrank K S)*Nat.card (TripleLinearOrbit U' V' W')) :=
        mul_le_mul hi hb (by positivity)
          (mul_nonneg (le_of_lt (lagrangianConstant_pos _)) (Nat.cast_nonneg _))
    _ = (lagrangianConstant (D-finrank K S)*2^(finrank K S))*
      ((Nat.card (IsotropicDimspace ω (finrank K S)) : ℝ)*Nat.card (TripleLinearOrbit U' V' W')) := by ring
    _ ≤ (lagrangianConstant D*2^D)*Nat.card (OrderedTripleOrbit ω U V W) :=
      mul_le_mul hk hcard (by positivity)
        (mul_nonneg (le_of_lt (lagrangianConstant_pos _)) (by positivity))

private instance certificate_instance_0268 : OAI.SidorenkoCounterexample.ProofCertificate_0268 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19 q20 q21 q22 q23
  exact @certificate_proof_0268 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19 q20 q21 q22 q23

end ConfigurationCount
section FixedPairCount
variable {K E : Type} [Field K] [AddCommGroup E] [Module K E]
  [Fintype K] [Finite E] [Invertible (2:K)]
variable (ω : LinearMap.BilinForm K E)
theorem certificate_proof_0269 (ha : ω.IsAlt) (hω : ω.Nondegenerate)
    (D : ℕ) (hD : 2*D = finrank K E)
    (hq : 4*lagrangianConstant D ≤ (Fintype.card K : ℝ))
    (L M N : SymplecticLagrangian ω) (h0 : (L.val ⊓ M.val) ⊓ N.val = ⊥) :
    let S := triplePairSum L.val M.val N.val
    (Fintype.card K : ℝ)^((D-finrank K ↥(L.val ⊓ S)+1).choose 2 +
      (D-finrank K ↥(M.val ⊓ S)+1).choose 2 + (D-finrank K ↥(N.val ⊓ S)+1).choose 2) ≤
      (8 * (4^D * lagrangianConstant D^2)) * Nat.card (FixedPairTripleOrbit ω L M N) := by
  dsimp only
  let S := triplePairSum L.val M.val N.val
  have hs : S ≤ ω.orthogonal S := triplePairSum_isotropic ω _ _ _ L.property M.property N.property
  have his (P : SymplecticLagrangian ω) : P.val ⊓ S ≤ ω.orthogonal (P.val ⊓ S) := by
    intro x hx y hy
    exact P.property.ge hx.1 y hy.1
  have h2 := (isUnit_of_invertible (2:K)).ne_zero
  have h₁ := (containingLagrangian_card_bounds ω h2 ha hω D hD (L.val ⊓ S) (his L)).1
  have h₂ := (containingLagrangian_card_bounds ω h2 ha hω D hD (M.val ⊓ S) (his M)).1
  have h₃ := (containingLagrangian_card_bounds ω h2 ha hω D hD (N.val ⊓ S) (his N)).1
  have ht := triplePairSum_reductions_transverse ω L.val M.val N.val L.property M.property N.property
  have hb := containmentOrbitFiber_card_lower ω S ha hω hs D hD hq
    (L.val ⊓ S) (M.val ⊓ S) (N.val ⊓ S) inf_le_right inf_le_right inf_le_right
    (tripleResidualLagrangian ω L M N ha hω L)
    (tripleResidualLagrangian ω L M N ha hω M) (tripleResidualLagrangian ω L M N ha hω N)
    ht.1 ht.2.1 ht.2.2
  have he := ownAvoidanceOrbitFiberEmbedding ω L M N ha hω h0
  have hc : (Nat.card (OwnAvoidanceOrbitFiber ω L M N ha hω) : ℝ) ≤
      Nat.card (FixedPairTripleOrbit ω L M N) := by exact_mod_cast Nat.card_le_card_of_injective he he.injective
  calc
    _ = (Fintype.card K : ℝ)^((D-finrank K ↥(L.val ⊓ S)+1).choose 2) *
      ((Fintype.card K : ℝ)^((D-finrank K ↥(M.val ⊓ S)+1).choose 2) *
        (Fintype.card K : ℝ)^((D-finrank K ↥(N.val ⊓ S)+1).choose 2)) := by simp only [pow_add]; ring
    _ ≤ (Nat.card {P : SymplecticLagrangian ω // L.val ⊓ S ≤ P.val} : ℝ)*
      (Nat.card {P : SymplecticLagrangian ω // M.val ⊓ S ≤ P.val} *
        Nat.card {P : SymplecticLagrangian ω // N.val ⊓ S ≤ P.val}) := by gcongr
    _ ≤ _ := hb
    _ ≤ _ := mul_le_mul_of_nonneg_left hc (by positivity)

private instance certificate_instance_0269 : OAI.SidorenkoCounterexample.ProofCertificate_0269 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17
  exact @certificate_proof_0269 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17

end FixedPairCount
end SidorenkoCounterexample
namespace SidorenkoCounterexample
theorem certificate_proof_0270 (D u v w : ℕ) (h : u+v+w ≤ D) :
    isotropicExponent D (u+v+w) + 2*(u*v+u*w+v*w) +
      ((D-(u+v)+1).choose 2 + (D-(u+w)+1).choose 2 + (D-(v+w)+1).choose 2) +
      ((u+1).choose 2 + (v+1).choose 2 + (w+1).choose 2) = 3*(D+1).choose 2 := by
  have hu : u+v ≤ D := by omega
  have hv : u+w ≤ D := by omega
  have hw : v+w ≤ D := by omega
  have hi := isotropicExponent_add D (u+v+w) h
  have hi' : (isotropicExponent D (u+v+w) : ℚ) =
      ((D+1).choose 2 : ℚ) + (u+v+w)*(D-(u+v+w)) - ((D-(u+v+w)+1).choose 2 : ℚ) := by
    have hiq := congrArg (fun x : ℕ => (x:ℚ)) hi
    simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_sub h] at hiq
    linarith
  apply @Nat.cast_injective ℚ
  simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,hi',Nat.cast_choose_two,Nat.cast_one,
    Nat.cast_sub hu,Nat.cast_sub hv,Nat.cast_sub hw,Nat.cast_sub h]
  ring

private instance certificate_instance_0270 : OAI.SidorenkoCounterexample.ProofCertificate_0270 := by
  constructor
  intro q0 q1 q2 q3 q4
  exact @certificate_proof_0270 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 q0 q1 q2 q3 q4

theorem certificate_proof_0271 (D c : ℕ) (hc : c ≤ D) :
    isotropicExponent D c + 3*(D-c+1).choose 2 + (D+1)*c = 3*(D+1).choose 2 := by
  have hi := isotropicExponent_add D c hc
  have h : 2*((D-c+1).choose 2) + (D+1)*c + c*(D-c) = 2*((D+1).choose 2) := by
    apply @Nat.cast_injective ℚ
    simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_choose_two,Nat.cast_one,Nat.cast_sub hc]
    ring
  omega

private instance certificate_instance_0271 : OAI.SidorenkoCounterexample.ProofCertificate_0271 := by
  constructor
  intro q0 q1 q2
  exact @certificate_proof_0271 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 q0 q1 q2

open Module
section PairMass
variable {K E : Type} [Field K] [AddCommGroup E] [Module K E]
  [FiniteDimensional K E]
variable (ω : LinearMap.BilinForm K E)
theorem certificate_proof_0272 (U V : Submodule K E) (h : Disjoint U V) :
    finrank K ↥(U ⊔ V) = finrank K U + finrank K V := by
  have hh := U.finrank_sup_add_finrank_inf_eq V
  rw [disjoint_iff.mp h,finrank_bot,add_zero] at hh
  exact hh

private instance certificate_instance_0272 : OAI.SidorenkoCounterexample.ProofCertificate_0272 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8
  exact @certificate_proof_0272 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 q0 q1 q2 q3 q4 q5 q6 q7 q8

theorem certificate_proof_0273 (L M N : Submodule K E) (h0 : (L ⊓ M) ⊓ N = ⊥) :
    finrank K ↥(triplePairSum L M N) = finrank K ↥(L ⊓ M) + finrank K ↥(L ⊓ N) + finrank K ↥(M ⊓ N) := by
  have hd := triple_pairs_disjoint L M N h0
  change finrank K ↥(((L ⊓ M) ⊔ (L ⊓ N)) ⊔ (M ⊓ N)) = _
  rw [sup_assoc,finrank_sup_of_disjoint _ _ hd.1,finrank_sup_of_disjoint _ _ hd.2,add_assoc]

private instance certificate_instance_0273 : OAI.SidorenkoCounterexample.ProofCertificate_0273 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9
  exact @certificate_proof_0273 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9

theorem certificate_proof_0274 (L M N : Submodule K E) (h0 : (L ⊓ M) ⊓ N = ⊥) :
    finrank K ↥(L ⊓ triplePairSum L M N) = finrank K ↥(L ⊓ M) + finrank K ↥(L ⊓ N) := by
  rw [triple_own_avoidance L M N h0]
  exact finrank_sup_of_disjoint _ _ ((triple_pairs_disjoint L M N h0).1.mono_right le_sup_left)

private instance certificate_instance_0274 : OAI.SidorenkoCounterexample.ProofCertificate_0274 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9
  exact @certificate_proof_0274 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9

theorem certificate_proof_0275 (D : ℕ) : 0 < pairOrbitConstant D := by
  unfold pairOrbitConstant
  have h := lagrangianConstant_pos D
  positivity

private instance certificate_instance_0275 : OAI.SidorenkoCounterexample.ProofCertificate_0275 := by
  constructor
  intro q0
  exact @certificate_proof_0275 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 q0

variable [Fintype K] [Finite E] [Invertible (2:K)]
theorem certificate_proof_0276 (ha : ω.IsAlt) (hω : ω.Nondegenerate)
    (D : ℕ) (hD : 2*D = finrank K E)
    (hq : 4*lagrangianConstant D ≤ (Fintype.card K : ℝ))
    (L M N : SymplecticLagrangian ω) (h0 : (L.val ⊓ M.val) ⊓ N.val = ⊥) :
    (Fintype.card K : ℝ)^(3*(D+1).choose 2) ≤
      pairOrbitConstant D * (Fintype.card K : ℝ)^((finrank K ↥(L.val ⊓ M.val)+1).choose 2 +
        (finrank K ↥(L.val ⊓ N.val)+1).choose 2 + (finrank K ↥(M.val ⊓ N.val)+1).choose 2) *
      Nat.card (OrderedTripleOrbit ω L.val M.val N.val) := by
  let S := triplePairSum L.val M.val N.val
  let u := finrank K ↥(L.val ⊓ M.val)
  let v := finrank K ↥(L.val ⊓ N.val)
  let w := finrank K ↥(M.val ⊓ N.val)
  have hs : S ≤ ω.orthogonal S := triplePairSum_isotropic ω _ _ _ L.property M.property N.property
  have hdim : finrank K S = u+v+w := triplePairSum_finrank _ _ _ h0
  have hdimL : finrank K ↥(L.val ⊓ S) = u+v := triplePairSum_inter_finrank _ _ _ h0
  have h0M : (M.val ⊓ L.val) ⊓ N.val = ⊥ := by simpa only [inf_comm] using h0
  have h0N : (N.val ⊓ L.val) ⊓ M.val = ⊥ := by simpa only [inf_assoc,inf_left_comm,inf_comm] using h0
  have hSM : triplePairSum M.val L.val N.val = S := by dsimp [S,triplePairSum]; ac_rfl
  have hSN : triplePairSum N.val L.val M.val = S := by dsimp [S,triplePairSum]; ac_rfl
  have hdimM : finrank K ↥(M.val ⊓ S) = u+w := by
    have hh := triplePairSum_inter_finrank M.val L.val N.val h0M
    rw [hSM,inf_comm M.val L.val] at hh
    exact hh
  have hdimN : finrank K ↥(N.val ⊓ S) = v+w := by
    have hh := triplePairSum_inter_finrank N.val L.val M.val h0N
    rw [hSN,inf_comm N.val L.val,inf_comm N.val M.val] at hh
    exact hh
  have haD : u+v+w ≤ D := hdim ▸ isotropic_finrank_le_half ω hω D hD S hs
  have hd := triple_pairs_disjoint L.val M.val N.val h0
  have hc := triple_isotropic_orbit_card_lower ω (isUnit_of_invertible (2:K)).ne_zero ha hω D hD S
    (L.val ⊓ M.val) (L.val ⊓ N.val) (M.val ⊓ N.val) hs
    (le_sup_of_le_left le_sup_left) (le_sup_of_le_left le_sup_right) le_sup_right rfl hd.1 hd.2
  rw [hdim] at hc
  have hf := fixedPairTripleOrbit_card_lower ω ha hω D hD hq L M N h0
  change (Fintype.card K : ℝ)^((D-finrank K ↥(L.val ⊓ S)+1).choose 2 +
      (D-finrank K ↥(M.val ⊓ S)+1).choose 2 + (D-finrank K ↥(N.val ⊓ S)+1).choose 2) ≤ _ at hf
  rw [hdimL,hdimM,hdimN] at hf
  have hm : (Nat.card (OrderedTripleOrbit ω (L.val ⊓ M.val) (L.val ⊓ N.val) (M.val ⊓ N.val)) : ℝ) *
      Nat.card (FixedPairTripleOrbit ω L M N) ≤ Nat.card (OrderedTripleOrbit ω L.val M.val N.val) := by
    exact_mod_cast fullTripleOrbit_fixedPair_card_lower ω L M N
  have hn : 0 ≤ lagrangianConstant D*2^D := mul_nonneg (le_of_lt (lagrangianConstant_pos D)) (by positivity)
  have hp := mul_le_mul hc hf (by positivity)
    (mul_nonneg hn (Nat.cast_nonneg _))
  have hh : (Fintype.card K : ℝ)^(isotropicExponent D (u+v+w)+2*(u*v+u*w+v*w)+
      ((D-(u+v)+1).choose 2+(D-(u+w)+1).choose 2+(D-(v+w)+1).choose 2)) ≤
      pairOrbitConstant D * Nat.card (OrderedTripleOrbit ω L.val M.val N.val) := by
    calc
      _ ≤ (lagrangianConstant D*2^D)*Nat.card (OrderedTripleOrbit ω (L.val ⊓ M.val) (L.val ⊓ N.val) (M.val ⊓ N.val)) *
          ((8*(4^D*lagrangianConstant D^2))*Nat.card (FixedPairTripleOrbit ω L M N)) := by
        simpa only [pow_add] using hp
      _ = pairOrbitConstant D * ((Nat.card (OrderedTripleOrbit ω (L.val ⊓ M.val) (L.val ⊓ N.val) (M.val ⊓ N.val)) : ℝ)*
          Nat.card (FixedPairTripleOrbit ω L M N)) := by unfold pairOrbitConstant; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hm (le_of_lt (pairOrbitConstant_pos D))
  have hh' := mul_le_mul_of_nonneg_right hh
    (show 0 ≤ (Fintype.card K : ℝ)^((u+1).choose 2+(v+1).choose 2+(w+1).choose 2) by positivity)
  rw [←pow_add,pair_cost_cancellation D u v w haD] at hh'
  simpa only [mul_assoc,mul_left_comm,mul_comm] using hh'

private instance certificate_instance_0276 : OAI.SidorenkoCounterexample.ProofCertificate_0276 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18
  exact @certificate_proof_0276 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18

end PairMass
end SidorenkoCounterexample
end OAI

theorem solution : OAI.SidorenkoCounterexample.ProofCertificate_0256 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0257 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0258 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0259 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0260 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0261 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0262 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0263 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0264 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0265 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0266 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0267 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0268 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0269 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0270 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0271 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0272 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0273 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0274 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0275 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0276 := by
  exact ⟨inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance⟩
end

