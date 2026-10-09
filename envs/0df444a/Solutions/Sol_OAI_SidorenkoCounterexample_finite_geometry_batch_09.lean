-- Prove2me | solution 1 for OAI.SidorenkoCounterexample.finite_geometry_batch_09
-- status  : ACCEPTED   (prove)
-- author  : @abcdefg
-- created : 2026-10-09T05:57:49.908761+00:00
-- url     : https://prove2.me/submissions/1d655690-a1b5-4f4f-b283-437606b6fe9e

import Definitions.Def_SidorenkoFiniteGeometryCertificates07
set_option linter.unusedVariables false
section
variable [p0 : OAI.SidorenkoCounterexample.ProofCertificate_0005]
  [p1 : OAI.SidorenkoCounterexample.ProofCertificate_0010]
  [p2 : OAI.SidorenkoCounterexample.ProofCertificate_0013]
  [p3 : OAI.SidorenkoCounterexample.ProofCertificate_0014]
  [p4 : OAI.SidorenkoCounterexample.ProofCertificate_0015]
  [p5 : OAI.SidorenkoCounterexample.ProofCertificate_0029]
  [p6 : OAI.SidorenkoCounterexample.ProofCertificate_0030]
  [p7 : OAI.SidorenkoCounterexample.ProofCertificate_0032]
  [p8 : OAI.SidorenkoCounterexample.ProofCertificate_0038]
  [p9 : OAI.SidorenkoCounterexample.ProofCertificate_0069]
  [p10 : OAI.SidorenkoCounterexample.ProofCertificate_0107]
  [p11 : OAI.SidorenkoCounterexample.ProofCertificate_0108]
  [p12 : OAI.SidorenkoCounterexample.ProofCertificate_0110]
  [p13 : OAI.SidorenkoCounterexample.ProofCertificate_0111]
  [p14 : OAI.SidorenkoCounterexample.ProofCertificate_0112]
  [p15 : OAI.SidorenkoCounterexample.ProofCertificate_0114]
  [p16 : OAI.SidorenkoCounterexample.ProofCertificate_0117]
  [p17 : OAI.SidorenkoCounterexample.ProofCertificate_0118]
  [p18 : OAI.SidorenkoCounterexample.ProofCertificate_0120]
  [p19 : OAI.SidorenkoCounterexample.ProofCertificate_0121]
  [p20 : OAI.SidorenkoCounterexample.ProofCertificate_0122]
  [p21 : OAI.SidorenkoCounterexample.ProofCertificate_0127]
  [p22 : OAI.SidorenkoCounterexample.ProofCertificate_0131]
  [p23 : OAI.SidorenkoCounterexample.ProofCertificate_0133]
  [p24 : OAI.SidorenkoCounterexample.ProofCertificate_0134]
  [p25 : OAI.SidorenkoCounterexample.ProofCertificate_0143]
  [p26 : OAI.SidorenkoCounterexample.ProofCertificate_0144]
  [p27 : OAI.SidorenkoCounterexample.ProofCertificate_0145]
  [p28 : OAI.SidorenkoCounterexample.ProofCertificate_0153]
  [p29 : OAI.SidorenkoCounterexample.ProofCertificate_0168]
  [p30 : OAI.SidorenkoCounterexample.ProofCertificate_0169]
  [p31 : OAI.SidorenkoCounterexample.ProofCertificate_0205]
  [p32 : OAI.SidorenkoCounterexample.ProofCertificate_0207]
  [p33 : OAI.SidorenkoCounterexample.ProofCertificate_0208]
  [p34 : OAI.SidorenkoCounterexample.ProofCertificate_0209]
include p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34

namespace OAI
namespace SidorenkoCounterexample
open Module
open scoped BigOperators
section NormSphere
variable {K E : Type} [Field K] [Fintype K] [AddCommGroup E] [Module K E]
  [FiniteDimensional K E] [Finite E]
end NormSphere
section Isometries
variable {K E : Type} [Field K] [AddCommGroup E] [Module K E]
  [FiniteDimensional K E]
instance (B : LinearMap.BilinForm K E) [Finite E] : Finite (BilinAut B) := by
  apply Finite.of_injective (fun e : BilinAut B => (e.val : E → E))
  intro e f h
  apply Subtype.ext
  exact LinearEquiv.ext (congrFun h)
variable [Finite E]
variable [Fintype K] [Invertible (2 : K)]
end Isometries
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
open scoped BigOperators
section FormOrbits
variable {K E : Type} [Field K] [AddCommGroup E] [Module K E]
  [FiniteDimensional K E]
variable [Fintype K] [Finite E]
variable [Invertible (2 : K)]
end FormOrbits
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
section TransverseForms
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
end TransverseForms
section TransverseTripleCoordinates
variable {K E : Type} [Field K] [AddCommGroup E] [Module K E]
  [FiniteDimensional K E]
variable (ω : LinearMap.BilinForm K E)
end TransverseTripleCoordinates
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
section FixedPairOrbit
variable {K E : Type} [Field K] [AddCommGroup E] [Module K E]
variable (ω : LinearMap.BilinForm K E) (L M N : Submodule K E)
variable [FiniteDimensional K E]
variable [Fintype K] [Finite E] [Invertible (2 : K)]
end FixedPairOrbit
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
open scoped BigOperators
section UniformCountingBounds
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [Fintype K] [Finite V]
end UniformCountingBounds
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
section FullTripleOrbit
variable {K E : Type} [Field K] [AddCommGroup E] [Module K E]
variable (ω : LinearMap.BilinForm K E)
variable [FiniteDimensional K E]
theorem certificate_proof_0210 (ha : ω.IsAlt) (hω : ω.Nondegenerate)
    (L M N : Submodule K E) (hL : ω.orthogonal L = L) (hM : ω.orthogonal M = M)
    (hLM : L ⊓ M = ⊥) :
    ∃ f : OrderedTransversePair ω × FixedPairOrbit ω L M N → OrderedTripleOrbit ω L M N,
      Function.Injective f := by
  classical
  have ht (p : OrderedTransversePair ω) := transverse_pair_transitivity ω ha hω
    L M p.val.1.val p.val.2.val hL hM p.val.1.property p.val.2.property hLM p.property
  let e (p : OrderedTransversePair ω) := (ht p).choose
  have he (p) := (ht p).choose_spec
  have hgood (p : OrderedTransversePair ω) (N' : FixedPairOrbit ω L M N) :
      ∃ f : E ≃ₗ[K] E, (∀ x y, ω (f x) (f y) = ω x y) ∧
        L.map f.toLinearMap = p.val.1.val ∧ M.map f.toLinearMap = p.val.2.val ∧
        N.map f.toLinearMap = N'.val.map (e p).toLinearMap := by
    obtain ⟨g,hg,hgL,hgM,hgN⟩ := N'.property
    refine ⟨g.trans (e p),?_,?_,?_,?_⟩
    · intro x y
      exact ((he p).1 (g x) (g y)).trans (hg x y)
    · change L.map ((e p).toLinearMap.comp g.toLinearMap) = _
      rw [Submodule.map_comp,hgL]
      exact (he p).2.1
    · change M.map ((e p).toLinearMap.comp g.toLinearMap) = _
      rw [Submodule.map_comp,hgM]
      exact (he p).2.2
    · change N.map ((e p).toLinearMap.comp g.toLinearMap) = _
      rw [Submodule.map_comp,hgN]
  let f : OrderedTransversePair ω × FixedPairOrbit ω L M N → OrderedTripleOrbit ω L M N :=
    fun x => ⟨(x.1.val.1.val,x.1.val.2.val,x.2.val.map (e x.1).toLinearMap),hgood x.1 x.2⟩
  refine ⟨f,?_⟩
  rintro ⟨p,A⟩ ⟨q,B⟩ h
  have hv := congrArg Subtype.val h
  have hp : p = q := by
    apply Subtype.ext
    apply Prod.ext
    · exact Subtype.ext (congrArg Prod.fst hv)
    · exact Subtype.ext (congrArg (fun x => x.2.1) hv)
  subst q
  have hab : A = B := by
    apply Subtype.ext
    exact Submodule.map_injective_of_injective (e p).injective
      (congrArg (fun x => x.2.2) hv)
  subst B
  rfl

private instance certificate_instance_0210 : OAI.SidorenkoCounterexample.ProofCertificate_0210 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14
  exact @certificate_proof_0210 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14

end FullTripleOrbit
section CanonicalTripleMass
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [Fintype K] [Finite V]
local notation "ω" => (canonicalSymplectic (K := K) (V := V))
theorem certificate_proof_0211 (h2 : (2 : K) ≠ 0) (A : Lagrangian (K := K) (V := V)) :
    Nat.card {B : Lagrangian (K := K) (V := V) // A.val ⊓ B.val = ⊥} =
      Fintype.card K^((finrank K V+1).choose 2) := by
  have h := lagrangian_pair_count h2 A 0 (Nat.zero_le _)
  have hc : Nat.card {U : Submodule K V // finrank K U = finrank K V} = 1 := by
    let : Unique {U : Submodule K V // finrank K U = finrank K V} :=
      ⟨⟨⊤,finrank_top K V⟩,fun U => Subtype.ext (Submodule.eq_top_of_finrank_eq U.property)⟩
    exact Nat.card_unique
  have he : {B : Lagrangian (K := K) (V := V) // A.val ⊓ B.val = ⊥} ≃
      {B : Lagrangian (K := K) (V := V) // finrank K ↥(B.val ⊓ A.val) = 0} :=
    Equiv.subtypeEquiv (Equiv.refl _) (by
      intro B
      change A.val ⊓ B.val = ⊥ ↔ finrank K ↥(B.val ⊓ A.val) = 0
      rw [Submodule.finrank_eq_zero,inf_comm])
  rw [Nat.card_congr he,h]
  simp only [Nat.sub_zero,hc,one_mul]

private instance certificate_instance_0211 : OAI.SidorenkoCounterexample.ProofCertificate_0211 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8
  exact @certificate_proof_0211 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 q0 q1 q2 q3 q4 q5 q6 q7 q8

theorem certificate_proof_0212 (h2 : (2 : K) ≠ 0) :
    Nat.card (OrderedTransversePair ω) = Nat.card (Lagrangian (K := K) (V := V)) *
      Fintype.card K^((finrank K V+1).choose 2) := by
  classical
  let : Finite (Module.Dual K V) := Module.finite_of_finite K
  let := Fintype.ofFinite (Lagrangian (K := K) (V := V))
  let e : OrderedTransversePair ω ≃
      Σ A : Lagrangian (K := K) (V := V), {B : Lagrangian (K := K) (V := V) // A.val ⊓ B.val = ⊥} :=
    { toFun := fun p => ⟨p.val.1,⟨p.val.2,p.property⟩⟩
      invFun := fun p => ⟨(p.1,p.2.val),p.2.property⟩
      left_inv := fun p => rfl
      right_inv := fun p => rfl }
  rw [Nat.card_congr e,Nat.card_sigma]
  simp only [transverse_to_card h2,Finset.sum_const,Finset.card_univ,smul_eq_mul,
    Nat.card_eq_fintype_card]

private instance certificate_instance_0212 : OAI.SidorenkoCounterexample.ProofCertificate_0212 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7
  exact @certificate_proof_0212 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 q0 q1 q2 q3 q4 q5 q6 q7

theorem certificate_proof_0213 [Invertible (2 : K)]
    (L M N : Lagrangian (K := K) (V := V))
    (hLM : L.val ⊓ M.val = ⊥) (hLN : L.val ⊓ N.val = ⊥) (hMN : M.val ⊓ N.val = ⊥) :
    Nat.card (Lagrangian (K := K) (V := V)) *
        (Fintype.card K^((finrank K V+1).choose 2)) ^ 2 ≤
      4^finrank K V * Nat.card (OrderedTripleOrbit ω L.val M.val N.val) := by
  let : Finite (Module.Dual K V) := Module.finite_of_finite K
  have hcard := fixedPairOrbit_card_lower ω L.val M.val N.val
    canonicalSymplectic_alt canonicalSymplectic_nondegenerate
    L.property M.property N.property hLM hLN hMN
  rw [lagrangian_finrank L] at hcard
  obtain ⟨f,hf⟩ := orderedTripleOrbit_pair_injection ω canonicalSymplectic_alt
    canonicalSymplectic_nondegenerate L.val M.val N.val L.property M.property hLM
  have hi := Nat.card_le_card_of_injective f hf
  rw [Nat.card_prod,orderedTransversePair_card (isUnit_of_invertible (2 : K)).ne_zero] at hi
  calc
    _ = (Nat.card (Lagrangian (K := K) (V := V)) * Fintype.card K^((finrank K V+1).choose 2)) *
        Fintype.card K^((finrank K V+1).choose 2) := by rw [pow_two]; ac_rfl
    _ ≤ (Nat.card (Lagrangian (K := K) (V := V)) * Fintype.card K^((finrank K V+1).choose 2)) *
        (4^finrank K V * Nat.card (FixedPairOrbit ω L.val M.val N.val)) := Nat.mul_le_mul_left _ hcard
    _ = 4^finrank K V * (Nat.card (Lagrangian (K := K) (V := V)) *
        Fintype.card K^((finrank K V+1).choose 2) * Nat.card (FixedPairOrbit ω L.val M.val N.val)) := by ring
    _ ≤ _ := Nat.mul_le_mul_left _ hi

private instance certificate_instance_0213 : OAI.SidorenkoCounterexample.ProofCertificate_0213 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13
  exact @certificate_proof_0213 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13

end CanonicalTripleMass
end SidorenkoCounterexample
end OAI
namespace OAI
namespace SidorenkoCounterexample
open Module
open scoped BigOperators
section GenericCounts
variable {K E F : Type} [Field K] [AddCommGroup E] [Module K E]
  [AddCommGroup F] [Module K F]
variable [Fintype K] [Finite E]
variable (ω : LinearMap.BilinForm K E)
theorem certificate_proof_0214 (h2 : (2 : K) ≠ 0)
    (ha : ω.IsAlt) (hω : ω.Nondegenerate) (D : ℕ) (hD : 2*D = finrank K E) :
    (Fintype.card K : ℝ)^((D+1).choose 2) ≤ Nat.card (SymplecticLagrangian ω) ∧
      (Nat.card (SymplecticLagrangian ω) : ℝ) ≤
        lagrangianConstant D * (Fintype.card K : ℝ)^((D+1).choose 2) := by
  obtain ⟨L,_,hL⟩ := exists_containing_lagrangian ω ha ⊥ bot_le
  have hd : finrank K L = D := by
    have h := self_orthogonal_twice_finrank ω L hω hL
    omega
  obtain ⟨e,_,he⟩ := exists_lagrangian_coordinates ω L h2 ha hω hL
  have hc := Nat.card_congr (symplecticLagrangianEquiv canonicalSymplectic ω e he)
  change Nat.card (Lagrangian (K := K) (V := L)) = _ at hc
  rw [←hc,←hd]
  exact ⟨lagrangian_card_lower,lagrangian_card_upper⟩

private instance certificate_instance_0214 : OAI.SidorenkoCounterexample.ProofCertificate_0214 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12
  exact @certificate_proof_0214 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12

omit [Fintype K] in
theorem certificate_proof_0215 (ha : ω.IsAlt) :
    0 < Nat.card (SymplecticLagrangian ω) := by
  obtain ⟨L,_,hL⟩ := exists_containing_lagrangian ω ha ⊥ bot_le
  let : Nonempty (SymplecticLagrangian ω) := ⟨⟨L,hL⟩⟩
  exact Nat.card_pos

private instance certificate_instance_0215 : OAI.SidorenkoCounterexample.ProofCertificate_0215 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7
  exact @certificate_proof_0215 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 q0 q1 q2 q3 q4 q5 q6 q7

omit [Fintype K] in
theorem certificate_proof_0216 (hω : ω.Nondegenerate)
    (D : ℕ) (hD : 2*D = finrank K E) (S : Submodule K E)
    (hS : S ≤ ω.orthogonal S) : finrank K S ≤ D := by
  have h := ω.finrank_orthogonal hω S
  have hl := Submodule.finrank_mono hS
  omega

private instance certificate_instance_0216 : OAI.SidorenkoCounterexample.ProofCertificate_0216 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11
  exact @certificate_proof_0216 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11

theorem certificate_proof_0217 (h2 : (2 : K) ≠ 0)
    (ha : ω.IsAlt) (hω : ω.Nondegenerate) (D : ℕ) (hD : 2*D = finrank K E)
    (S : Submodule K E) (hS : S ≤ ω.orthogonal S) :
    (Fintype.card K : ℝ)^((D-finrank K S+1).choose 2) ≤
        Nat.card {L : SymplecticLagrangian ω // S ≤ L.val} ∧
      (Nat.card {L : SymplecticLagrangian ω // S ≤ L.val} : ℝ) ≤
        lagrangianConstant (D-finrank K S) *
          (Fintype.card K : ℝ)^((D-finrank K S+1).choose 2) := by
  let e : {L : SymplecticLagrangian ω // S ≤ L.val} ≃
      {L : Submodule K E // ω.orthogonal L = L ∧ S ≤ L} :=
    { toFun := fun L => ⟨L.val.val,L.val.property,L.property⟩
      invFun := fun L => ⟨⟨L.val,L.property.1⟩,L.property.2⟩
      left_inv := fun L => rfl
      right_inv := fun L => rfl }
  have he := Nat.card_congr (e.trans (containingLagrangianEquiv ω S ha hS))
  have hc := reducedSpace_finrank ω S hω hS
  have hs := isotropic_finrank_le_half ω hω D hD S hS
  let : Finite (ReducedSpace ω S) := Module.finite_of_finite K
  rw [he]
  exact symplecticLagrangian_card_bounds (symplecticReductionForm ω S ha) h2
    (symplecticReductionForm_alt ω S ha) (symplecticReductionForm_nondegenerate ω S ha hω)
    (D-finrank K S) (by omega)

private instance certificate_instance_0217 : OAI.SidorenkoCounterexample.ProofCertificate_0217 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14
  exact @certificate_proof_0217 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14

omit [Fintype K] [Finite E] in
theorem certificate_proof_0218 (c : ℕ) :
    Nat.card (Σ S : IsotropicDimspace ω c, {L : SymplecticLagrangian ω // S.val ≤ L.val}) =
      Nat.card (Σ L : SymplecticLagrangian ω, DimSubspace K L.val c) :=
  Nat.card_congr (isotropicIncidenceEquiv ω c)

private instance certificate_instance_0218 : OAI.SidorenkoCounterexample.ProofCertificate_0218 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6
  exact @certificate_proof_0218 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 q0 q1 q2 q3 q4 q5 q6

end GenericCounts
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
open scoped BigOperators
theorem certificate_proof_0219 (D c : ℕ) (hc : c ≤ D) :
    isotropicExponent D c + (D-c+1).choose 2 = (D+1).choose 2 + c*(D-c) := by
  have h := symmetric_nullity_exponent D c hc
  exact Nat.sub_add_cancel (by omega)

private instance certificate_instance_0219 : OAI.SidorenkoCounterexample.ProofCertificate_0219 := by
  constructor
  intro q0 q1 q2
  exact @certificate_proof_0219 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 q0 q1 q2

section IsotropicCounts
variable {K E : Type} [Field K] [AddCommGroup E] [Module K E]
  [Fintype K] [Finite E]
variable (ω : LinearMap.BilinForm K E)
theorem certificate_proof_0220 (h2 : (2 : K) ≠ 0)
    (ha : ω.IsAlt) (hω : ω.Nondegenerate) (D : ℕ) (hD : 2*D = finrank K E)
    (c : ℕ) (hc : c ≤ D) :
    (Fintype.card K : ℝ)^(isotropicExponent D c) ≤
        lagrangianConstant (D-c) * Nat.card (IsotropicDimspace ω c) ∧
      (Nat.card (IsotropicDimspace ω c) : ℝ) ≤
        (lagrangianConstant D * 2^c) * (Fintype.card K : ℝ)^(isotropicExponent D c) := by
  classical
  let := Fintype.ofFinite (IsotropicDimspace ω c)
  let := Fintype.ofFinite (SymplecticLagrangian ω)
  let q : ℝ := Fintype.card K
  have hq : 0 < q := by
    dsimp [q]
    exact_mod_cast Fintype.card_pos (α := K)
  have hdim (L : SymplecticLagrangian ω) : finrank K L.val = D := by
    have h := self_orthogonal_twice_finrank ω L.val hω L.property
    omega
  have hs (S : IsotropicDimspace ω c) :=
    containingLagrangian_card_bounds ω h2 ha hω D hD S.val S.property.1
  have hs' (S : IsotropicDimspace ω c) :
      q^((D-c+1).choose 2) ≤ Nat.card {L : SymplecticLagrangian ω // S.val ≤ L.val} ∧
      (Nat.card {L : SymplecticLagrangian ω // S.val ≤ L.val} : ℝ) ≤
        lagrangianConstant (D-c)*q^((D-c+1).choose 2) := by
    simpa only [S.property.2] using hs S
  have hsum : (∑ S : IsotropicDimspace ω c,
      (Nat.card {L : SymplecticLagrangian ω // S.val ≤ L.val} : ℝ)) =
        ∑ L : SymplecticLagrangian ω, (Nat.card (DimSubspace K L.val c) : ℝ) := by
    have h := isotropic_incidence_card ω c
    rw [Nat.card_sigma,Nat.card_sigma] at h
    exact_mod_cast h
  have hgrass (L : SymplecticLagrangian ω) :
      q^(c*(D-c)) ≤ Nat.card (DimSubspace K L.val c) ∧
        (Nat.card (DimSubspace K L.val c) : ℝ) ≤ 2^c*q^(c*(D-c)) := by
    have hcL : c ≤ finrank K L.val := (hdim L).symm ▸ hc
    constructor
    · simpa only [hdim L] using subspace_count_lower (K := K) (V := L.val) c hcL
    · simpa only [hdim L] using subspace_count_upper (K := K) (V := L.val) c hcL
  have hu : (Nat.card (IsotropicDimspace ω c) : ℝ)*q^((D-c+1).choose 2) ≤
      (Nat.card (SymplecticLagrangian ω) : ℝ)*(2^c*q^(c*(D-c))) := by
    calc
      _ = ∑ _S : IsotropicDimspace ω c, q^((D-c+1).choose 2) := by
        simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Nat.card_eq_fintype_card]
      _ ≤ ∑ S : IsotropicDimspace ω c,
          (Nat.card {L : SymplecticLagrangian ω // S.val ≤ L.val} : ℝ) :=
        Finset.sum_le_sum (fun S _ => (hs' S).1)
      _ = _ := hsum
      _ ≤ ∑ _L : SymplecticLagrangian ω, 2^c*q^(c*(D-c)) :=
        Finset.sum_le_sum (fun L _ => (hgrass L).2)
      _ = _ := by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Nat.card_eq_fintype_card]
  have hl : (Nat.card (SymplecticLagrangian ω) : ℝ)*q^(c*(D-c)) ≤
      (Nat.card (IsotropicDimspace ω c) : ℝ)*(lagrangianConstant (D-c)*q^((D-c+1).choose 2)) := by
    calc
      _ = ∑ _L : SymplecticLagrangian ω, q^(c*(D-c)) := by
        simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Nat.card_eq_fintype_card]
      _ ≤ ∑ L : SymplecticLagrangian ω, (Nat.card (DimSubspace K L.val c) : ℝ) :=
        Finset.sum_le_sum (fun L _ => (hgrass L).1)
      _ = _ := hsum.symm
      _ ≤ ∑ _S : IsotropicDimspace ω c, lagrangianConstant (D-c)*q^((D-c+1).choose 2) :=
        Finset.sum_le_sum (fun S _ => (hs' S).2)
      _ = _ := by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Nat.card_eq_fintype_card]
  have hlag := symplecticLagrangian_card_bounds ω h2 ha hω D hD
  have he : q^(isotropicExponent D c)*q^((D-c+1).choose 2) =
      q^((D+1).choose 2)*q^(c*(D-c)) := by
    rw [←pow_add,isotropicExponent_add D c hc,pow_add]
  constructor
  · apply (mul_le_mul_iff_left₀ (pow_pos hq ((D-c+1).choose 2))).mp
    calc
      _ = q^((D+1).choose 2)*q^(c*(D-c)) := he
      _ ≤ (Nat.card (SymplecticLagrangian ω) : ℝ)*q^(c*(D-c)) :=
        mul_le_mul_of_nonneg_right hlag.1 (by positivity)
      _ ≤ _ := hl
      _ = _ := by ring
  · apply (mul_le_mul_iff_left₀ (pow_pos hq ((D-c+1).choose 2))).mp
    calc
      _ ≤ _ := hu
      _ ≤ (lagrangianConstant D*q^((D+1).choose 2))*(2^c*q^(c*(D-c))) :=
        mul_le_mul_of_nonneg_right hlag.2 (by positivity)
      _ = (lagrangianConstant D*2^c)*(q^((D+1).choose 2)*q^(c*(D-c))) := by ring
      _ = _ := by rw [←he]; ring

private instance certificate_instance_0220 : OAI.SidorenkoCounterexample.ProofCertificate_0220 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14
  exact @certificate_proof_0220 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14

end IsotropicCounts
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
open scoped BigOperators
theorem certificate_proof_0221 : Monotone lagrangianConstant := by
  intro m n h
  unfold lagrangianConstant
  exact mul_le_mul (by exact_mod_cast Nat.add_le_add_right h 1)
    (pow_le_pow_right₀ (by norm_num) h) (by positivity) (by positivity)

private instance certificate_instance_0221 : OAI.SidorenkoCounterexample.ProofCertificate_0221 := by
  constructor
  exact @certificate_proof_0221 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34

section AvoidanceCounts
variable {K E : Type} [Field K] [AddCommGroup E] [Module K E]
  [Fintype K] [Finite E]
variable (ω : LinearMap.BilinForm K E)
theorem certificate_proof_0222 (h2 : (2 : K) ≠ 0)
    (ha : ω.IsAlt) (hω : ω.Nondegenerate) (D : ℕ) (hD : 2*D = finrank K E)
    (S : Submodule K E) (hS : S ≤ ω.orthogonal S) (hpos : 0 < finrank K S) :
    (Nat.card {L : SymplecticLagrangian ω // ¬ Disjoint L.val S} : ℝ) ≤
      (2*(Fintype.card K : ℝ)^(finrank K S-1)) *
        (lagrangianConstant (D-1)*(Fintype.card K : ℝ)^((D-1+1).choose 2)) := by
  classical
  let Line := DimSubspace K S 1
  let B := {L : SymplecticLagrangian ω // ¬ Disjoint L.val S}
  let Inc := Σ ℓ : Line, {L : SymplecticLagrangian ω // ℓ.val.map S.subtype ≤ L.val}
  let := Fintype.ofFinite Line
  have hex (L : B) : ∃ ℓ : Line, ℓ.val.map S.subtype ≤ L.val.val := by
    have hne : L.val.val ⊓ S ≠ ⊥ := by simpa only [disjoint_iff] using L.property
    obtain ⟨x,hx,hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
    let v : S := ⟨x,hx.2⟩
    have hv : v ≠ 0 := by intro h; exact hx0 (congrArg Subtype.val h)
    refine ⟨⟨K ∙ v, finrank_span_singleton hv⟩,?_⟩
    rintro y ⟨z,hz,rfl⟩
    obtain ⟨a,rfl⟩ := Submodule.mem_span_singleton.mp hz
    exact L.val.val.smul_mem a hx.1
  let f : B → Inc := fun L => ⟨(hex L).choose,⟨L.val,(hex L).choose_spec⟩⟩
  have hfi : Function.Injective f := by
    intro L M h
    apply Subtype.ext
    exact congrArg (fun i : Inc => i.2.val) h
  have hi (ℓ : Line) : (Nat.card {L : SymplecticLagrangian ω //
      ℓ.val.map S.subtype ≤ L.val} : ℝ) ≤
      lagrangianConstant (D-1)*(Fintype.card K : ℝ)^((D-1+1).choose 2) := by
    have hle : ℓ.val.map S.subtype ≤ S := by rintro x ⟨y,_,rfl⟩; exact y.property
    have hiso : ℓ.val.map S.subtype ≤ ω.orthogonal (ℓ.val.map S.subtype) :=
      hle.trans (hS.trans (ω.orthogonal_le hle))
    have hd : finrank K (ℓ.val.map S.subtype) = 1 := by
      exact (Submodule.equivMapOfInjective S.subtype S.subtype_injective ℓ.val).finrank_eq.symm.trans ℓ.property
    simpa only [hd] using (containingLagrangian_card_bounds ω h2 ha hω D hD
      (ℓ.val.map S.subtype) hiso).2
  have hinc : (Nat.card Inc : ℝ) ≤ (Nat.card Line : ℝ)*
      (lagrangianConstant (D-1)*(Fintype.card K : ℝ)^((D-1+1).choose 2)) := by
    rw [Nat.card_sigma,Nat.cast_sum]
    calc
      _ ≤ ∑ _ℓ : Line, lagrangianConstant (D-1)*(Fintype.card K : ℝ)^((D-1+1).choose 2) :=
        Finset.sum_le_sum (fun ℓ _ => hi ℓ)
      _ = _ := by simp [Nat.card_eq_fintype_card]
  have hl : (Nat.card Line : ℝ) ≤ 2*(Fintype.card K : ℝ)^(finrank K S-1) := by
    simpa [Line] using subspace_count_upper (K := K) (V := S) 1 hpos
  calc
    _ ≤ (Nat.card Inc : ℝ) := by exact_mod_cast Nat.card_le_card_of_injective f hfi
    _ ≤ _ := hinc
    _ ≤ _ := mul_le_mul_of_nonneg_right hl (by
      exact mul_nonneg (lagrangianConstant_pos _).le (by positivity))

private instance certificate_instance_0222 : OAI.SidorenkoCounterexample.ProofCertificate_0222 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15
  exact @certificate_proof_0222 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15

theorem certificate_proof_0223 (h2 : (2 : K) ≠ 0)
    (ha : ω.IsAlt) (hω : ω.Nondegenerate) (D : ℕ) (hD : 2*D = finrank K E)
    (S : Submodule K E) (hS : S ≤ ω.orthogonal S) :
    (Nat.card {L : SymplecticLagrangian ω // ¬ Disjoint L.val S} : ℝ) *
      Fintype.card K ≤ 2*lagrangianConstant D*Nat.card (SymplecticLagrangian ω) := by
  classical
  let q : ℝ := Fintype.card K
  have hq : 1 ≤ q := by dsimp [q]; exact_mod_cast Fintype.card_pos (α := K)
  by_cases hp : 0 < finrank K S
  · have hs := isotropic_finrank_le_half ω hω D hD S hS
    have hDpos : 0 < D := lt_of_lt_of_le hp hs
    have he : (D-1+1).choose 2 + D = (D+1).choose 2 := by
      rw [Nat.sub_add_cancel hDpos, Nat.choose_succ_succ,Nat.choose_one_right]
      change D.choose 2 + D = D + D.choose 2
      omega
    have hpow : q^((finrank K S-1)+(D-1+1).choose 2+1) ≤ q^((D+1).choose 2) := by
      apply pow_le_pow_right₀ hq
      omega
    have hc : lagrangianConstant (D-1) ≤ lagrangianConstant D := lagrangianConstant_mono (Nat.sub_le _ _)
    calc
      _ ≤ (2*q^(finrank K S-1))*(lagrangianConstant (D-1)*q^((D-1+1).choose 2))*q :=
        mul_le_mul_of_nonneg_right (lagrangian_bad_intersection_card ω h2 ha hω D hD S hS hp) (by positivity)
      _ = 2*lagrangianConstant (D-1)*q^((finrank K S-1)+(D-1+1).choose 2+1) := by
        simp only [pow_add,pow_one]; ring
      _ ≤ 2*lagrangianConstant D*q^((D+1).choose 2) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hc (by norm_num)) hpow
          (by positivity) (by exact mul_nonneg (by norm_num) (lagrangianConstant_pos D).le)
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (symplecticLagrangian_card_bounds ω h2 ha hω D hD).1
        (mul_nonneg (by norm_num) (lagrangianConstant_pos D).le)
  · have hfin : finrank K S = 0 := by omega
    have hbot : S = ⊥ := Submodule.finrank_eq_zero.mp hfin
    have he : IsEmpty {L : SymplecticLagrangian ω // ¬ Disjoint L.val S} := by
      rw [hbot]
      exact ⟨fun L => L.property disjoint_bot_right⟩
    have := he
    simp only [Nat.card_of_isEmpty,Nat.cast_zero,zero_mul]
    exact mul_nonneg (mul_nonneg (by norm_num) (lagrangianConstant_pos D).le) (by positivity)

private instance certificate_instance_0223 : OAI.SidorenkoCounterexample.ProofCertificate_0223 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14
  exact @certificate_proof_0223 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14

theorem certificate_proof_0224 (h2 : (2 : K) ≠ 0)
    (ha : ω.IsAlt) (hω : ω.Nondegenerate) (D : ℕ) (hD : 2*D = finrank K E)
    (S : Submodule K E) (hS : S ≤ ω.orthogonal S)
    (hq : 4*lagrangianConstant D ≤ (Fintype.card K : ℝ)) :
    (Nat.card (SymplecticLagrangian ω) : ℝ) ≤
      2*Nat.card {L : SymplecticLagrangian ω // Disjoint L.val S} := by
  classical
  let := Fintype.ofFinite (SymplecticLagrangian ω)
  have hsum : Nat.card {L : SymplecticLagrangian ω // Disjoint L.val S} +
      Nat.card {L : SymplecticLagrangian ω // ¬ Disjoint L.val S} =
        Nat.card (SymplecticLagrangian ω) := by
    simp only [Nat.card_eq_fintype_card,Fintype.card_subtype_compl]
    exact Nat.add_sub_of_le (Fintype.card_subtype_le _)
  have hsumR := congrArg (fun n : ℕ => (n : ℝ)) hsum
  push_cast at hsumR
  have hbad := lagrangian_bad_intersection_scaled ω h2 ha hω D hD S hS
  have hC := lagrangianConstant_pos D
  have hbad0 : (0 : ℝ) ≤ Nat.card {L : SymplecticLagrangian ω // ¬ Disjoint L.val S} := by positivity
  nlinarith

private instance certificate_instance_0224 : OAI.SidorenkoCounterexample.ProofCertificate_0224 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15
  exact @certificate_proof_0224 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15

end AvoidanceCounts
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
section ContainmentAvoidance
variable {K E : Type} [Field K] [AddCommGroup E] [Module K E]
variable (ω : LinearMap.BilinForm K E)
theorem certificate_proof_0225 (ha : ω.IsAlt) (A S : Submodule K E)
    (hS : S ≤ ω.orthogonal S) :
    reduceSubspace ω A S ≤ (symplecticReductionForm ω A ha).orthogonal (reduceSubspace ω A S) := by
  rintro x ⟨x,hx,rfl⟩ y ⟨y,hy,rfl⟩
  exact hS hx y.val hy

private instance certificate_instance_0225 : OAI.SidorenkoCounterexample.ProofCertificate_0225 := by
  constructor
  intro c0 c1 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9
  exact @certificate_proof_0225 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9

variable [Fintype K] [Finite E]
theorem certificate_proof_0226 (h2 : (2 : K) ≠ 0) (ha : ω.IsAlt)
    (hω : ω.Nondegenerate) (D : ℕ) (hD : 2*D = finrank K E)
    (A S : Submodule K E) (hAS : A ≤ S) (hS : S ≤ ω.orthogonal S)
    (hq : 4*lagrangianConstant D ≤ (Fintype.card K : ℝ)) :
    (Nat.card {L : SymplecticLagrangian ω // A ≤ L.val} : ℝ) ≤
      2*Nat.card (AvoidanceSpace ω S A) := by
  have hAP : A ≤ ω.orthogonal A := hAS.trans (hS.trans (ω.orthogonal_le hAS))
  have hdim := reducedSpace_finrank ω A hω hAP
  have hle := isotropic_finrank_le_half ω hω D hD A hAP
  let Ω := symplecticReductionForm ω A ha
  have hΩa : Ω.IsAlt := symplecticReductionForm_alt ω A ha
  have hΩ : Ω.Nondegenerate := symplecticReductionForm_nondegenerate ω A ha hω
  let : Finite (ReducedSpace ω A) := Module.finite_of_finite K
  have h := lagrangian_disjoint_card_lower Ω h2 hΩa hΩ (D-finrank K A) (by omega)
    (reduceSubspace ω A S) (reduceSubspace_isotropic ω ha A S hS)
    ((mul_le_mul_of_nonneg_left (lagrangianConstant_mono (Nat.sub_le D _)) (by norm_num)).trans hq)
  have he₁ := Nat.card_congr (containmentAvoidanceEquiv ω ha A S hAS hS)
  have e₂ : {L : SymplecticLagrangian ω // A ≤ L.val} ≃
      {L : Submodule K E // ω.orthogonal L = L ∧ A ≤ L} :=
    { toFun := fun L => ⟨L.val.val,L.val.property,L.property⟩
      invFun := fun L => ⟨⟨L.val,L.property.1⟩,L.property.2⟩
      left_inv := fun L => rfl
      right_inv := fun L => rfl }
  have he₂ := Nat.card_congr (e₂.trans (containingLagrangianEquiv ω A ha hAP))
  rwa [he₁,he₂]

private instance certificate_instance_0226 : OAI.SidorenkoCounterexample.ProofCertificate_0226 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17
  exact @certificate_proof_0226 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17

end ContainmentAvoidance
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
section CommonSpaceLift
variable {K E : Type} [Field K] [AddCommGroup E] [Module K E]
  [FiniteDimensional K E]
variable (ω : LinearMap.BilinForm K E) (S : Submodule K E)
theorem certificate_proof_0227 (ha : ω.IsAlt) (hω : ω.Nondegenerate)
    (_hS : S ≤ ω.orthogonal S) (L M N L' M' N' : Submodule K E)
    (hL : ω.orthogonal L = L) (hM : ω.orthogonal M = M) (hN : ω.orthogonal N = N)
    (hL' : ω.orthogonal L' = L') (hM' : ω.orthogonal M' = M') (hN' : ω.orthogonal N' = N')
    (hSL : S ≤ L) (hSM : S ≤ M) (hSN : S ≤ N)
    (hSL' : S ≤ L') (hSM' : S ≤ M') (hSN' : S ≤ N')
    (hres : TripleIsometry (symplecticReductionForm ω S ha) (symplecticReductionForm ω S ha)
      (reduceSubspace ω S L) (reduceSubspace ω S M) (reduceSubspace ω S N)
      (reduceSubspace ω S L') (reduceSubspace ω S M') (reduceSubspace ω S N')) :
    TripleIsometry ω ω L M N L' M' N' := by
  obtain ⟨f,hf,hfL,hfM,hfN⟩ := hres
  obtain ⟨e,he,heS,heP,heQ⟩ := exists_reduction_isometry_extension ω S ha hω f hf
  have hSe : S.map e.toLinearMap = S := subspace_map_eq_of_fixed e S heS
  have hPe : (ω.orthogonal S).map e.toLinearMap = ω.orthogonal S := by
    rw [←orthogonal_map_of_isometry ω e he,hSe]
  have hmap (U W : Submodule K E) (hU : ω.orthogonal U = U)
      (hW : ω.orthogonal W = W) (hSU : S ≤ U) (hSW : S ≤ W)
      (hfU : (reduceSubspace ω S U).map f.toLinearMap = reduceSubspace ω S W) :
      U.map e.toLinearMap = W := by
    have hSUe : S ≤ U.map e.toLinearMap := by
      rw [←hSe]
      exact Submodule.map_mono hSU
    have hUe : ω.orthogonal (U.map e.toLinearMap) = U.map e.toLinearMap := by
      rw [orthogonal_map_of_isometry ω e he,hU]
    calc
      U.map e.toLinearMap = liftReduction ω S (reduceSubspace ω S (U.map e.toLinearMap)) :=
        (lift_reduce ω S _ hSUe (lagrangian_le_orthogonal ω S _ hUe hSUe)).symm
      _ = liftReduction ω S (reduceSubspace ω S W) := by
        rw [reduceSubspace_map ω S e f hPe heQ,hfU]
      _ = W := lift_reduce ω S W hSW (lagrangian_le_orthogonal ω S W hW hSW)
  exact ⟨e,he,hmap L L' hL hL' hSL hSL' hfL,
    hmap M M' hM hM' hSM hSM' hfM,hmap N N' hN hN' hSN hSN' hfN⟩

private instance certificate_instance_0227 : OAI.SidorenkoCounterexample.ProofCertificate_0227 := by
  constructor
  intro c0 c1 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19 q20 q21 q22 q23 q24 q25 q26 q27 q28 q29
  exact @certificate_proof_0227 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19 q20 q21 q22 q23 q24 q25 q26 q27 q28 q29

end CommonSpaceLift
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
open scoped BigOperators
section Decompositions
variable {K E : Type} [Field K] [AddCommGroup E] [Module K E]
theorem certificate_proof_0228 (U : Submodule K E) (e f : E ≃ₗ[K] E) :
    U.map (e.trans f).toLinearMap = (U.map e.toLinearMap).map f.toLinearMap := by
  exact Submodule.map_comp _ _ _

private instance certificate_instance_0228 : OAI.SidorenkoCounterexample.ProofCertificate_0228 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7
  exact @certificate_proof_0228 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 q0 q1 q2 q3 q4 q5 q6 q7

theorem certificate_proof_0229 (U : Submodule K E) (e : E ≃ₗ[K] E) :
    (U.map e.toLinearMap).map e.symm.toLinearMap = U := by
  rw [←Submodule.map_comp]
  simp

private instance certificate_instance_0229 : OAI.SidorenkoCounterexample.ProofCertificate_0229 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6
  exact @certificate_proof_0229 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 q0 q1 q2 q3 q4 q5 q6

theorem certificate_proof_0230 (U V : Submodule K E) (hUV : IsCompl U V) :
    Function.Bijective (pairLinearStabilizerRestriction U V) := by
  constructor
  · intro e f hh
    apply Subtype.ext
    ext x
    have hx : x ∈ U ⊔ V := by rw [hUV.sup_eq_top]; trivial
    obtain ⟨u,hu,v,hv,rfl⟩ := Submodule.mem_sup.mp hx
    have hU := congrArg (fun p : (U ≃ₗ[K] U) × (V ≃ₗ[K] V) => (p.1 ⟨u,hu⟩).val) hh
    have hV := congrArg (fun p : (U ≃ₗ[K] U) × (V ≃ₗ[K] V) => (p.2 ⟨v,hv⟩).val) hh
    change e.val u = f.val u at hU
    change e.val v = f.val v at hV
    simp only [map_add,hU,hV]
  · intro g
    let c := Submodule.prodEquivOfIsCompl U V hUV
    let e : E ≃ₗ[K] E := c.symm.trans ((g.1.prodCongr g.2).trans c)
    have heU (u : U) : e u.val = (g.1 u).val := by
      have hc : c (u,0) = u.val := by simp [c]
      change c ((g.1.prodCongr g.2) (c.symm u.val)) = _
      rw [←hc,c.symm_apply_apply]
      simp [c]
    have heV (v : V) : e v.val = (g.2 v).val := by
      have hc : c (0,v) = v.val := by simp [c]
      change c ((g.1.prodCongr g.2) (c.symm v.val)) = _
      rw [←hc,c.symm_apply_apply]
      simp [c]
    have hU : U.map e.toLinearMap = U := by
      ext x
      constructor
      · rintro ⟨u,hu,rfl⟩
        change e u ∈ U
        rw [heU ⟨u,hu⟩]
        exact (g.1 ⟨u,hu⟩).property
      · intro hx
        refine ⟨(g.1.symm ⟨x,hx⟩).val,(g.1.symm ⟨x,hx⟩).property,?_⟩
        exact (heU _).trans (congrArg Subtype.val (g.1.apply_symm_apply ⟨x,hx⟩))
    have hV : V.map e.toLinearMap = V := by
      ext x
      constructor
      · rintro ⟨v,hv,rfl⟩
        change e v ∈ V
        rw [heV ⟨v,hv⟩]
        exact (g.2 ⟨v,hv⟩).property
      · intro hx
        refine ⟨(g.2.symm ⟨x,hx⟩).val,(g.2.symm ⟨x,hx⟩).property,?_⟩
        exact (heV _).trans (congrArg Subtype.val (g.2.apply_symm_apply ⟨x,hx⟩))
    refine ⟨⟨e,hU,hV⟩,?_⟩
    apply Prod.ext
    · ext u
      exact heU u
    · ext v
      exact heV v

private instance certificate_instance_0230 : OAI.SidorenkoCounterexample.ProofCertificate_0230 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7
  exact @certificate_proof_0230 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 q0 q1 q2 q3 q4 q5 q6 q7

variable [Fintype K] [Finite E]
omit [Fintype K] in
theorem certificate_proof_0231 (U V : Submodule K E) (hUV : IsCompl U V) :
    Nat.card (PairLinearOrbit U V) *
      (Nat.card (U ≃ₗ[K] U)*Nat.card (V ≃ₗ[K] V)) = Nat.card (E ≃ₗ[K] E) := by
  classical
  let := Fintype.ofFinite (PairLinearOrbit U V)
  have hc : Nat.card (PairLinearStabilizer U V) =
      Nat.card (U ≃ₗ[K] U)*Nat.card (V ≃ₗ[K] V) := by
    rw [Nat.card_congr (Equiv.ofBijective _ (pairLinearStabilizerRestriction_bijective U V hUV)),Nat.card_prod]
  have he := (Nat.card_congr (Equiv.sigmaFiberEquiv (pairLinearOrbitMap U V))).symm
  rw [Nat.card_sigma] at he
  have hf (p : PairLinearOrbit U V) : Nat.card {e : E ≃ₗ[K] E // pairLinearOrbitMap U V e = p} =
      Nat.card (U ≃ₗ[K] U)*Nat.card (V ≃ₗ[K] V) :=
    (Nat.card_congr (pairLinearOrbitFiberEquiv U V p)).trans hc
  simpa only [hf,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Nat.card_eq_fintype_card,Nat.cast_id] using he.symm

private instance certificate_instance_0231 : OAI.SidorenkoCounterexample.ProofCertificate_0231 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8
  exact @certificate_proof_0231 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 q0 q1 q2 q3 q4 q5 q6 q7 q8

end Decompositions
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
open scoped BigOperators
section TripleDecompositions
variable {K E : Type} [Field K] [AddCommGroup E] [Module K E]
variable [Finite E]
variable [Fintype K]
end TripleDecompositions
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
open scoped BigOperators
section UniformCounts
variable {A B C D E F : Type}
end UniformCounts
section ExactPairs
variable {K E : Type} [Field K] [AddCommGroup E] [Module K E]
variable (ω : LinearMap.BilinForm K E) (S L M A B : Submodule K E)
end ExactPairs
end SidorenkoCounterexample
end OAI

theorem solution : OAI.SidorenkoCounterexample.ProofCertificate_0210 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0211 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0212 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0213 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0214 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0215 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0216 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0217 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0218 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0219 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0220 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0221 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0222 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0223 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0224 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0225 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0226 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0227 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0228 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0229 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0230 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0231 := by
  exact ⟨inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance⟩
end

