-- Prove2me | solution 1 for OAI.SidorenkoCounterexample.finite_geometry_batch_20
-- status  : ACCEPTED   (prove)
-- author  : @abcdefg
-- created : 2026-10-09T06:12:55.940395+00:00
-- url     : https://prove2.me/submissions/81de84b7-86a5-408e-b5eb-1e3c63bff17a

import Definitions.Def_SidorenkoCertificateBundleA
set_option linter.unusedVariables false
section
variable [p0 : OAI.SidorenkoCounterexample.ProofCertificate_0207]
  [p1 : OAI.SidorenkoCounterexample.ProofCertificate_0216]
  [p2 : OAI.SidorenkoCounterexample.ProofCertificate_0281]
  [p3 : OAI.SidorenkoCounterexample.ProofCertificate_0334]
  [p4 : OAI.SidorenkoCounterexample.ProofCertificate_0351]
  [p5 : OAI.SidorenkoCounterexample.ProofCertificate_0352]
  [p6 : OAI.SidorenkoCounterexample.ProofCertificate_0356]
  [p7 : OAI.SidorenkoCounterexample.ProofCertificate_0407]
  [p8 : OAI.SidorenkoCounterexample.ProofCertificate_0411]
  [p9 : OAI.SidorenkoCounterexample.ProofCertificate_0412]
  [p10 : OAI.SidorenkoCounterexample.ProofCertificate_0413]
  [p11 : OAI.SidorenkoCounterexample.ProofCertificate_0414]
  [p12 : OAI.SidorenkoCounterexample.ProofCertificate_0436]
  [p13 : OAI.SidorenkoCounterexample.ProofCertificate_0437]
  [p14 : OAI.SidorenkoCounterexample.ProofCertificate_0439]
  [p15 : OAI.SidorenkoCounterexample.ProofCertificate_0458]
  [p16 : OAI.SidorenkoCounterexample.ProofCertificate_0468]
  [p17 : OAI.SidorenkoCounterexample.ProofCertificate_0492]
  [p18 : OAI.SidorenkoCounterexample.ProofCertificate_0494]
  [p19 : OAI.SidorenkoCounterexample.ProofCertificate_0498]
  [p20 : OAI.SidorenkoCounterexample.ProofCertificate_0506]
  [p21 : OAI.SidorenkoCounterexample.ProofCertificate_0508]
  [p22 : OAI.SidorenkoCounterexample.ProofCertificate_0514]
  [p23 : OAI.SidorenkoCounterexample.ProofCertificate_0515]
  [p24 : OAI.SidorenkoCounterexample.ProofCertificate_0517]
  [p25 : OAI.SidorenkoCounterexample.ProofCertificate_0518]
  [p26 : OAI.SidorenkoCounterexample.ProofCertificate_0522]
  [p27 : OAI.SidorenkoCounterexample.ProofCertificate_0528]
  [p28 : OAI.SidorenkoCounterexample.ProofCertificate_0531]
  [p29 : OAI.SidorenkoCounterexample.ProofCertificate_0533]
  [p30 : OAI.SidorenkoCounterexample.ProofCertificate_0534]
include p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30

namespace OAI
namespace SidorenkoCounterexample
open Module
section Span
variable {K V P : Type} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Fintype P] [DecidableEq P]
end Span
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
open scoped BigOperators
section FiniteSpans
variable {K E I : Type} [Field K] [AddCommGroup E] [Module K E] [FiniteDimensional K E]
end FiniteSpans
instance (e f : Fin 33) : Decidable (pairRelated e f) := inferInstanceAs (Decidable (¬Disjoint _ _))
section GraphSpans
variable {K E : Type} [Field K] [AddCommGroup E] [Module K E]
variable [FiniteDimensional K E]
end GraphSpans
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open scoped BigOperators
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open scoped BigOperators
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
open scoped BigOperators
section Containment
variable {K E : Type} [Field K] [AddCommGroup E] [Module K E]
variable (ω : LinearMap.BilinForm K E)
theorem certificate_proof_0535 (h : Fin 33 → ℕ) :
    Function.Injective (directPairProfileCoding ω h) := by
  let recover : (Σ A : DirectFamily ω h pairRelated, FamilyContainment ω (fun e=>(A.val e).val)) →
      (Fin 13 → SymplecticLagrangian ω) := fun x i=>(x.2 i).val
  intro x y hxy
  exact Subtype.ext (Subtype.ext (congrArg recover hxy))

private instance certificate_instance_0535 : OAI.SidorenkoCounterexample.ProofCertificate_0535 := by
  constructor
  intro c0 c1 q0 q1 q2 q3 q4 q5 q6
  exact @certificate_proof_0535 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 q0 q1 q2 q3 q4 q5 q6

variable [Fintype K] [Finite E]
theorem certificate_proof_0536 (h2 : (2:K)≠0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
    (D : ℕ) (hD : 2*D=finrank K E) (A : Fin 33 → Submodule K E) (ki : Fin 13 → ℕ)
    (hk : ∀ i,finrank K (incidentSpan A i)=ki i) :
    (Nat.card (FamilyContainment ω A):ℝ) ≤ (lagrangianConstant D)^13*
      (Nat.card (SymplecticLagrangian ω):ℝ)^13*(Fintype.card K:ℝ)^(containmentExponent D ki) := by
  have hq : 0<(Fintype.card K:ℝ) := by exact_mod_cast Fintype.card_pos (α:=K)
  have hp (i : Fin 13) : (Nat.card {L : SymplecticLagrangian ω // incidentSpan A i≤L.val}:ℝ) ≤
      lagrangianConstant D*(Nat.card (SymplecticLagrangian ω):ℝ)*
        (Fintype.card K:ℝ)^(-(D:ℝ)*ki i+(ki i:ℝ)*(ki i-1)/2) := by
    simpa only [hk i] using containingLagrangian_card_rpow ω h2 ha hω D hD (incidentSpan A i)
  have hh := Finset.prod_le_prod (s:=Finset.univ) (fun i _=>Nat.cast_nonneg (Nat.card {L : SymplecticLagrangian ω // incidentSpan A i≤L.val})) (fun i _=>hp i)
  rw [FamilyContainment,Nat.card_pi,Nat.cast_prod]
  calc _ ≤ _ := hh
       _ = _ := by
        rw [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,Fintype.card_fin,
          mul_pow,←Real.rpow_sum_of_pos hq]
        rfl

private instance certificate_instance_0536 : OAI.SidorenkoCounterexample.ProofCertificate_0536 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15
  exact @certificate_proof_0536 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15

theorem certificate_proof_0537 (h2 : (2:K)≠0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
    (D : ℕ) (hD : 2*D=finrank K E) (h : Fin 33 → ℕ) (hn : (∑ e,h e)≤2*D) :
    (Nat.card (DirectPairProfile ω h):ℝ) ≤
      2^(∑ e,h e)*(lagrangianConstant D)^13*(Nat.card (SymplecticLagrangian ω):ℝ)^13*
        (Fintype.card K:ℝ)^(-(∑ e,triangular (h e))) := by
  have hq : 0<(Fintype.card K:ℝ) := by exact_mod_cast Fintype.card_pos (α:=K)
  have hs : ∀ A : DirectFamily ω h pairRelated, (Nat.card (FamilyContainment ω (fun e=>(A.val e).val)):ℝ) ≤
      (lagrangianConstant D)^13*(Nat.card (SymplecticLagrangian ω):ℝ)^13*
        (Fintype.card K:ℝ)^(containmentExponent D (localPairDim h)) := by
    intro A
    exact familyContainment_card_bound ω h2 ha hω D hD _ _ (incidentSpan_finrank_direct h A.val A.property.1)
  have hi : (Nat.card (DirectPairProfile ω h):ℝ)≤
      Nat.card (Σ A : DirectFamily ω h pairRelated,FamilyContainment ω (fun e=>(A.val e).val)) := by
    exact_mod_cast Nat.card_le_card_of_injective _ (directPairProfileCoding_injective ω h)
  have hn' : (∑ e,h e)≤finrank K E := hD ▸ hn
  have hf := directFamily_card_bound ω hω h pairRelated pairRelated_symm hn'
  rw [←hD,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_sum] at hf
  have hc : 0 ≤ (lagrangianConstant D)^13*(Nat.card (SymplecticLagrangian ω):ℝ)^13*
      (Fintype.card K:ℝ)^(containmentExponent D (localPairDim h)) :=
    mul_nonneg (mul_nonneg (pow_nonneg (lagrangianConstant_pos D).le _)
      (pow_nonneg (Nat.cast_nonneg _) _)) (Real.rpow_nonneg hq.le _)
  calc _ ≤ _ := hi.trans (real_card_sigma_le _ hs)
       _ ≤ _ := mul_le_mul_of_nonneg_right hf hc
       _ = _ := by
        have he := residual_direct_exponent D h
        change _+containmentExponent D (localPairDim h)=_ at he
        rw [←he,Real.rpow_add hq]
        ring

private instance certificate_instance_0537 : OAI.SidorenkoCounterexample.ProofCertificate_0537 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14
  exact @certificate_proof_0537 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14

end Containment
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
open scoped BigOperators
section Nondirect
variable {K E : Type} [Field K] [AddCommGroup E] [Module K E]
variable (ω : LinearMap.BilinForm K E)
variable [Fintype K] [Finite E]
omit [Fintype K] [Finite E] in
theorem certificate_proof_0538 (h : Fin 33 → ℕ) (k : ℕ) (ki : Fin 13 → ℕ) :
    Function.Injective (pairSpanStratumCoding ω h k ki) := by
  let recover : (Σ A : LocalFamilyStratum (K:=K) (E:=E) h k ki,
      FamilyContainment ω (fun e=>(A.val.val e).val)) → (Fin 13 → SymplecticLagrangian ω) :=
    fun x i=>(x.2 i).val
  intro x y hxy
  exact Subtype.ext (Subtype.ext (congrArg recover hxy))

private instance certificate_instance_0538 : OAI.SidorenkoCounterexample.ProofCertificate_0538 := by
  constructor
  intro c0 q0 q1 q2 q3 q4 q5 q6 q7 q8
  exact @certificate_proof_0538 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 q0 q1 q2 q3 q4 q5 q6 q7 q8

theorem certificate_proof_0539 (h : Fin 33 → ℕ) (k : ℕ) (ki : Fin 13 → ℕ)
    (hk : k≤finrank K E) (hh : ∀ e,h e≤k) :
    (Nat.card (LocalFamilyStratum (K:=K) (E:=E) h k ki):ℝ)≤
      2^(k+∑ e,h e)*(Fintype.card K:ℝ)^(k*(finrank K E-k)+∑ e,h e*(k-h e)) := by
  have hi : Nat.card (LocalFamilyStratum (K:=K) (E:=E) h k ki)≤
      Nat.card (FamilySpanStratum (K:=K) (E:=E) h k) :=
    Nat.card_le_card_of_injective Subtype.val Subtype.val_injective
  exact (Nat.cast_le.mpr hi).trans (familySpan_card_upper h k hk hh)

private instance certificate_instance_0539 : OAI.SidorenkoCounterexample.ProofCertificate_0539 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11
  exact @certificate_proof_0539 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11

theorem certificate_proof_0540 (h : Fin 33 → ℕ) (k n : ℕ) (hk : k≤n) (hh : ∀ e,h e≤k) :
    ((k*(n-k)+∑ e,h e*(k-h e):ℕ):ℝ)=
      (k:ℝ)*(n-k)+∑ e,(h e:ℝ)*(k-h e) := by
  simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_sub hk,Nat.cast_sum,Nat.cast_sub (hh _)]

private instance certificate_instance_0540 : OAI.SidorenkoCounterexample.ProofCertificate_0540 := by
  constructor
  intro q0 q1 q2 q3 q4
  exact @certificate_proof_0540 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 q0 q1 q2 q3 q4

theorem certificate_proof_0541 (h2 : (2:K)≠0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
    (D : ℕ) (hD : 2*D=finrank K E) (h : Fin 33 → ℕ) (k : ℕ) (ki : Fin 13 → ℕ)
    (hk : k≤2*D) (hh : ∀ e,h e≤k) :
    (Nat.card (PairSpanStratum ω h k ki):ℝ)≤
      2^(k+∑ e,h e)*(lagrangianConstant D)^13*(Nat.card (SymplecticLagrangian ω):ℝ)^13*
      (Fintype.card K:ℝ)^((k:ℝ)*(2*D-k)+(∑ e,(h e:ℝ)*(k-h e))+containmentExponent D ki) := by
  have hq : 0<(Fintype.card K:ℝ) := by exact_mod_cast Fintype.card_pos (α:=K)
  have hs : ∀ A : LocalFamilyStratum (K:=K) (E:=E) h k ki,
      (Nat.card (FamilyContainment ω (fun e=>(A.val.val e).val)):ℝ) ≤
      (lagrangianConstant D)^13*(Nat.card (SymplecticLagrangian ω):ℝ)^13*
        (Fintype.card K:ℝ)^(containmentExponent D ki) := by
    intro A
    exact familyContainment_card_bound ω h2 ha hω D hD _ _ A.property
  have hi : (Nat.card (PairSpanStratum ω h k ki):ℝ)≤
      Nat.card (Σ A : LocalFamilyStratum (K:=K) (E:=E) h k ki,FamilyContainment ω (fun e=>(A.val.val e).val)) := by
    exact_mod_cast Nat.card_le_card_of_injective _ (pairSpanStratumCoding_injective ω h k ki)
  have hn : k≤finrank K E := hD ▸ hk
  have hf := localFamilyStratum_card_bound h k ki hn hh
  rw [←Real.rpow_natCast (Fintype.card K:ℝ),familySpan_exponent_cast h k _ hn hh,←hD,
    Nat.cast_mul,Nat.cast_ofNat] at hf
  have hc : 0 ≤ (lagrangianConstant D)^13*(Nat.card (SymplecticLagrangian ω):ℝ)^13*
      (Fintype.card K:ℝ)^(containmentExponent D ki) :=
    mul_nonneg (mul_nonneg (pow_nonneg (lagrangianConstant_pos D).le _)
      (pow_nonneg (Nat.cast_nonneg _) _)) (Real.rpow_nonneg hq.le _)
  calc _ ≤ _ := hi.trans (real_card_sigma_le _ hs)
       _ ≤ _ := mul_le_mul_of_nonneg_right hf hc
       _ = _ := by simp only [Real.rpow_add hq];ring

private instance certificate_instance_0541 : OAI.SidorenkoCounterexample.ProofCertificate_0541 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17
  exact @certificate_proof_0541 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17

theorem certificate_proof_0542 (h : Fin 33 → ℕ) (hh : ∀ e,h e=0 ∨ h e=2) : (∑ e,h e)≤66 := by
  calc _ ≤ ∑ _e : Fin 33,2 := Finset.sum_le_sum (fun e _=>by rcases hh e with he|he <;> omega)
       _ = _ := by decide

private instance certificate_instance_0542 : OAI.SidorenkoCounterexample.ProofCertificate_0542 := by
  constructor
  intro q0 q1
  exact @certificate_proof_0542 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 q0 q1

omit [Fintype K] in
theorem certificate_proof_0543 (h : Fin 33 → ℕ) (L : PairDimProfile ω h) :
    finrank K ↥(⨆ e,pairSpaces ω L.val e)≤∑ e,h e := by
  have hh := finrank_finite_iSup_le (pairSpaces ω L.val)
  simpa only [L.property] using hh

private instance certificate_instance_0543 : OAI.SidorenkoCounterexample.ProofCertificate_0543 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8
  exact @certificate_proof_0543 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 q0 q1 q2 q3 q4 q5 q6 q7 q8

omit [Fintype K] in
theorem certificate_proof_0544 (h : Fin 33 → ℕ) (L : PairDimProfile ω h) (i : Fin 13) :
    finrank K (incidentSpan (pairSpaces ω L.val) i)≤localPairDim h i :=
  incidentSpan_finrank_le h (fun e=>⟨_,L.property e⟩) i

private instance certificate_instance_0544 : OAI.SidorenkoCounterexample.ProofCertificate_0544 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9
  exact @certificate_proof_0544 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9

omit [Fintype K] in
theorem certificate_proof_0545 (h : Fin 33 → ℕ) (hh : ∀ e,h e=0 ∨ h e=2)
    (b : ResidualDimensionBox) : Function.Injective (nondirectFiberInjection ω h hh b) := by
  intro x y hxy
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg (fun X : PairSpanStratum ω h b.1.val (fun i=>(b.2 i).val)=>X.val) hxy

private instance certificate_instance_0545 : OAI.SidorenkoCounterexample.ProofCertificate_0545 := by
  constructor
  intro c0 c1 c2 c3 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9
  exact @certificate_proof_0545 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9

theorem certificate_proof_0546 (h2 : (2:K)≠0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
    (D : ℕ) (hD : 2*D=finrank K E) (h : Fin 33 → ℕ) (hh : ∀ e,h e=0 ∨ h e=2)
    (b : ResidualDimensionBox) (hk : b.1.val≤2*D) (he : ∀ e,h e≤b.1.val)
    (hki : ∀ i,(b.2 i).val≤2*(incidentPairs i).card) (hs : 2*b.1.val+1≤∑ i,(b.2 i).val) :
    (Nat.card (PairSpanStratum ω h b.1.val (fun i=>(b.2 i).val)):ℝ)≤
      2^132*(lagrangianConstant D)^13*(Nat.card (SymplecticLagrangian ω):ℝ)^13*
        (Fintype.card K:ℝ)^(-(D:ℝ)+1575) := by
  have hf := pairSpanStratum_card_bound ω h2 ha hω D hD h b.1.val (fun i=>(b.2 i).val) hk he
  have hq : 1≤(Fintype.card K:ℝ) := by exact_mod_cast Fintype.card_pos (α:=K)
  have hfexp := Real.rpow_le_rpow_of_exponent_le hq
    (residual_nondirect_exponent D b.1.val h (fun i=>(b.2 i).val) hh hki hs)
  have hbpow : (2:ℝ)^(b.1.val+∑ e,h e)≤2^132 := by
    apply pow_le_pow_right₀ (by norm_num)
    have := b.1.isLt
    have := residual_h_sum_le h hh
    omega
  have hC := pow_nonneg (lagrangianConstant_pos D).le 13
  have hL : 0≤(Nat.card (SymplecticLagrangian ω):ℝ)^13 := pow_nonneg (Nat.cast_nonneg _) _
  have hP : (0:ℝ)≤2^132 := pow_nonneg (by norm_num) _
  refine hf.trans ?_
  exact mul_le_mul (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hbpow hC) hL)
    hfexp (Real.rpow_nonneg (le_trans (by norm_num) hq) _) (mul_nonneg (mul_nonneg hP hC) hL)

private instance certificate_instance_0546 : OAI.SidorenkoCounterexample.ProofCertificate_0546 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19
  exact @certificate_proof_0546 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19

theorem certificate_proof_0547 (h2 : (2:K)≠0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
    (D : ℕ) (hD : 2*D=finrank K E) (h : Fin 33 → ℕ) (hh : ∀ e,h e=0 ∨ h e=2)
    (b : ResidualDimensionBox) :
    (Nat.card {L : NonDirectPairProfile ω h // nondirectDimension ω h hh L=b}:ℝ)≤
      2^132*(lagrangianConstant D)^13*(Nat.card (SymplecticLagrangian ω):ℝ)^13*
        (Fintype.card K:ℝ)^(-(D:ℝ)+1575) := by
  classical
  by_cases hex : Nonempty {L : NonDirectPairProfile ω h // nondirectDimension ω h hh L=b}
  · obtain ⟨L⟩ := hex
    let A := pairSpaces ω L.val.val.val
    have hb := (nondirectFiberInjection ω h hh b L).property
    change finrank K ↥(⨆ e,pairSpaces ω L.val.val.val e)=b.1.val ∧
      (∀ i,finrank K (incidentSpan (pairSpaces ω L.val.val.val) i)=(b.2 i).val) at hb
    have hk : b.1.val≤2*D := by
      rw [hD,←hb.1]
      exact Submodule.finrank_le _
    have he : ∀ e,h e≤b.1.val := by
      intro e
      rw [←L.val.val.property e,←hb.1]
      exact Submodule.finrank_mono (le_iSup (pairSpaces ω L.val.val.val) e)
    have hki : ∀ i,(b.2 i).val≤2*(incidentPairs i).card := by
      intro i
      rw [←hb.2 i]
      exact (pairProfile_local_dim_le ω h L.val.val i).trans
        (localPairDim_le h (fun e=>by rcases hh e with he|he <;> omega) i)
    have hs : 2*b.1.val+1≤∑ i,(b.2 i).val := by
      have hs := indexed_strict_span A L.val.property
      change 2*finrank K ↥(⨆ e,pairSpaces ω L.val.val.val e)+1≤
        ∑ i,finrank K (incidentSpan (pairSpaces ω L.val.val.val) i) at hs
      simpa only [hb.1,hb.2] using hs
    have hi : (Nat.card {L : NonDirectPairProfile ω h // nondirectDimension ω h hh L=b}:ℝ)≤
        Nat.card (PairSpanStratum ω h b.1.val (fun i=>(b.2 i).val)) := by
      exact_mod_cast Nat.card_le_card_of_injective _ (nondirectFiberInjection_injective ω h hh b)
    exact hi.trans (pairStratum_residual_bound ω h2 ha hω D hD h hh b hk he hki hs)
  · have : IsEmpty {L : NonDirectPairProfile ω h // nondirectDimension ω h hh L=b} := not_nonempty_iff.mp hex
    rw [Nat.card_of_isEmpty,Nat.cast_zero]
    exact mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg (by norm_num) _)
      (pow_nonneg (lagrangianConstant_pos D).le _)) (pow_nonneg (Nat.cast_nonneg _) _))
        (Real.rpow_nonneg (Nat.cast_nonneg _) _)

private instance certificate_instance_0547 : OAI.SidorenkoCounterexample.ProofCertificate_0547 := by
  constructor
  intro c0 c1 c2 c3 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15
  exact @certificate_proof_0547 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15

theorem certificate_proof_0548 (h2 : (2:K)≠0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
    (D : ℕ) (hD : 2*D=finrank K E) (h : Fin 33 → ℕ) (hh : ∀ e,h e=0 ∨ h e=2) :
    (Nat.card (NonDirectPairProfile ω h):ℝ)≤
      (67*13^13)*2^132*(lagrangianConstant D)^13*(Nat.card (SymplecticLagrangian ω):ℝ)^13*
        (Fintype.card K:ℝ)^(-(D:ℝ)+1575) := by
  have he := Nat.card_congr (Equiv.sigmaFiberEquiv (nondirectDimension ω h hh))
  rw [←he]
  have hb := real_card_sigma_le _ (nondirectFiber_card_bound ω h2 ha hω D hD h hh)
  convert hb using 1
  simp only [ResidualDimensionBox,Nat.card_prod,Nat.card_fin,Nat.card_fun,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat]
  ring

private instance certificate_instance_0548 : OAI.SidorenkoCounterexample.ProofCertificate_0548 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14
  exact @certificate_proof_0548 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14

end Nondirect
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
open scoped BigOperators
theorem certificate_proof_0549 (D r c : ℕ) (s : Fin 3 → ℕ) (x : FullTailChoice D r c s) :
    0 ≤ fullTailConstant D r c s x := by
  have h₀ := (orbitMassConstant_pos D).le
  have h₁ := (lagrangianConstant_pos D).le
  have h₂ := (lagrangianConstant_pos (D-x.1.val.val)).le
  unfold fullTailConstant reducedPlantedConstant
  positivity

private instance certificate_instance_0549 : OAI.SidorenkoCounterexample.ProofCertificate_0549 := by
  constructor
  intro q0 q1 q2 q3 q4
  exact @certificate_proof_0549 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 q0 q1 q2 q3 q4

theorem certificate_proof_0550 (D r c : ℕ) (s : Fin 3 → ℕ) (q : ℝ) (hq : 0≤q) :
    0 ≤ fullTailMajorant D r c s q := by
  apply Finset.sum_nonneg
  intro x _
  exact mul_nonneg (fullTailConstant_nonneg _ _ _ _ _) (Real.rpow_nonneg hq _)

private instance certificate_instance_0550 : OAI.SidorenkoCounterexample.ProofCertificate_0550 := by
  constructor
  intro q0 q1 q2 q3 q4 q5
  exact @certificate_proof_0550 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 q0 q1 q2 q3 q4 q5

theorem certificate_proof_0551 (D r c : ℕ) (s : Fin 3 → ℕ) (q : ℝ)
    (hD : D=2*r) (hc : c≤D) (hq : 0<q) :
    fullTailMajorant D r c s q =
      (orbitMassConstant D*(lagrangianConstant D)^2)*
      q^(((D:ℝ)+1)*c+(∑ i,triangular (s i))+3*triangular r-4*triangular D)*
      ((lagrangianConstant D*2^c)*q^(isotropicExponent D c)*
        ∑ u : CommonParameters D r c,
          ((2^u.val.val*lagrangianConstant (D-u.val.val))*2^(3*(D-c)))*
          q^((u.val.val:ℝ)*(c-u.val.val:ℕ)+triangular (D-u.val.val:ℕ)+
            3*triangular (D-c:ℕ)-3*triangular (r-u.val.val:ℕ))*
          reducedPlantedSum (D-c) (r-u.val.val) (s 0) (s 1) (s 2) q) := by
  classical
  unfold fullTailMajorant
  rw [Fintype.sum_sigma]
  simp_rw [←fullPlantedExponent_eq D c r hD hc s,fullPlantedExponent,Real.rpow_add hq,
    Real.rpow_sub hq,reducedPlantedSum,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u _
  apply Finset.sum_congr rfl
  intro θ _
  unfold fullTailConstant
  simp only [Real.rpow_add hq,Real.rpow_sub hq,Real.rpow_natCast]
  ring

private instance certificate_instance_0551 : OAI.SidorenkoCounterexample.ProofCertificate_0551 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7
  exact @certificate_proof_0551 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 q0 q1 q2 q3 q4 q5 q6 q7

section Actual
variable {K E : Type} [Field K] [AddCommGroup E] [Module K E] [Fintype K] [Finite E]
variable (ω : LinearMap.BilinForm K E)
theorem certificate_proof_0552 [Invertible (2:K)]
    (h2 : (2:K)≠0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
    (D r : ℕ) (hD : 2*D=finrank K E) (hr : D=2*r)
    (hq : 4*lagrangianConstant D≤(Fintype.card K:ℝ)) (A L M N : SymplecticLagrangian ω) :
    let c := finrank K ↥((L.val⊓M.val)⊓N.val)
    let s : Fin 3 → ℕ := ![finrank K ↥(L.val⊓M.val)-c,finrank K ↥(L.val⊓N.val)-c,
      finrank K ↥(M.val⊓N.val)-c]
    tripleFaceDensity ω r A L M N ≤ fullTailMajorant D r c s (Fintype.card K) := by
  dsimp only
  have hc : finrank K ↥((L.val⊓M.val)⊓N.val)≤D :=
    isotropic_finrank_le_half ω hω D hD _ (by intro x hx y hy; exact L.property.ge hx.1.1 y hy.1.1)
  have hq0 : (0:ℝ)<Fintype.card K := by exact_mod_cast Fintype.card_pos (α:=K)
  rw [fullTailMajorant_eq _ _ _ _ _ hr hc hq0]
  have hh := tripleFaceDensity_full_bound ω h2 ha hω D hD hq r (by omega) A L M N
  dsimp only at hh
  refine hh.trans_eq ?_
  simp only [tripleDefect,commonPlantedTerm,Fin.sum_univ_three,Matrix.cons_val_zero,
    Matrix.cons_val_one,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons,
    Nat.cast_add,Nat.cast_mul,Nat.cast_one,Nat.cast_ofNat,triangular_nat]

private instance certificate_instance_0552 : OAI.SidorenkoCounterexample.ProofCertificate_0552 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19 q20
  exact @certificate_proof_0552 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19 q20

end Actual
end SidorenkoCounterexample
end OAI
namespace OAI
namespace SidorenkoCounterexample
open Module
open scoped BigOperators
theorem certificate_proof_0553 (c : ℕ) (s : Fin 3 → ℕ) (i : Fin 3) :
    (lowerTailTuple c s).s i=s i := Nat.add_zero _

private instance certificate_instance_0553 : OAI.SidorenkoCounterexample.ProofCertificate_0553 := by
  constructor
  intro q0 q1 q2
  exact @certificate_proof_0553 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 q0 q1 q2

theorem certificate_proof_0554 (D c : ℕ) (s : Fin 3 → ℕ) (hc : c≤D) (hs : (∑ i,s i)≤D-c) :
    TailFeasible D false (lowerTailTuple c s) := by
  refine ⟨hc,?_,by simp⟩
  change (∑ i,s i+0)≤D-c
  simpa only [Nat.add_zero] using hs

private instance certificate_instance_0554 : OAI.SidorenkoCounterexample.ProofCertificate_0554 := by
  constructor
  intro q0 q1 q2 q3 q4
  exact @certificate_proof_0554 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 q0 q1 q2 q3 q4

theorem certificate_proof_0555 (D r : ℕ) : 0<lowerTailConstant D r :=
  lt_of_lt_of_le zero_lt_one (le_max_left _ _)

private instance certificate_instance_0555 : OAI.SidorenkoCounterexample.ProofCertificate_0555 := by
  constructor
  intro q0 q1
  exact @certificate_proof_0555 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 q0 q1

theorem certificate_proof_0556 (r h : ℕ) : Nat.card (PairParameters r h)≤r+1 := by
  exact (Nat.card_le_card_of_injective _ Subtype.val_injective).trans_eq (Nat.card_fin _)

private instance certificate_instance_0556 : OAI.SidorenkoCounterexample.ProofCertificate_0556 := by
  constructor
  intro q0 q1
  exact @certificate_proof_0556 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 q0 q1

section PairBound
variable {K E : Type} [Field K] [AddCommGroup E] [Module K E] [Fintype K] [Finite E]
variable (ω : LinearMap.BilinForm K E)
theorem certificate_proof_0557 (h2 : (2:K)≠0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
    (D r : ℕ) (hD : 2*D=finrank K E) (hr : D=2*r) (c : ℕ) (s : Fin 3 → ℕ)
    (A L M : SymplecticLagrangian ω) (i : Fin 3)
    (hh : finrank K ↥(L.val⊓M.val)=c+s i) :
    pairFaceDensity ω r A L M≤lowerTailConstant D r*
      (Fintype.card K:ℝ)^(tailGain D false (lowerTailTuple c s)) := by
  have hq : (1:ℝ)≤Fintype.card K := by exact_mod_cast Fintype.card_pos (α:=K)
  have hb := pairFaceDensity_gain_bound ω h2 ha hω r (hr ▸ hD) A L M
  rw [←hr] at hb
  have hd : finrank K ↥(L.val⊓M.val)≤D :=
    isotropic_finrank_le_half ω hω D hD _ (by intro x hx y hy; exact L.property.ge hx.1 y hy.1)
  have hcard : (Nat.card (PairParameters r (finrank K ↥(L.val⊓M.val))):ℝ)≤r+1 := by
    exact_mod_cast pairParameters_card_le r (finrank K ↥(L.val⊓M.val))
  have hpow : (2:ℝ)^(D+finrank K ↥(L.val⊓M.val))≤2^(2*D) :=
    pow_le_pow_right₀ (by norm_num) (by omega)
  have hH : finrank K ↥(L.val⊓M.val)≤(lowerTailTuple c s).maxH := by
    rw [hh]
    exact (lowerTailTuple c s).h_le_max i
  have hg : ((finrank K ↥(L.val⊓M.val)/2+1).choose 2:ℝ) ≤
      tailGain D false (lowerTailTuple c s) := by
    simp only [tailGain,Bool.false_eq_true,reduceIte,triangular_nat]
    exact triangular_mono (by positivity) (by exact_mod_cast Nat.div_le_div_right hH)
  have hp : (Fintype.card K:ℝ)^((finrank K ↥(L.val⊓M.val)/2+1).choose 2) ≤
      (Fintype.card K:ℝ)^(tailGain D false (lowerTailTuple c s)) := by
    rw [←Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hq hg
  calc
    _ ≤ _ := hb
    _ ≤ ((lagrangianConstant D)^2*((r:ℝ)+1)*2^(2*D))*
        (Fintype.card K:ℝ)^(tailGain D false (lowerTailTuple c s)) := by
      have hs := mul_le_mul (mul_le_mul hcard hpow (by positivity) (by positivity)) hp (by positivity)
        (mul_nonneg (by positivity) (by positivity))
      have hi := mul_le_mul_of_nonneg_left hs (sq_nonneg (lagrangianConstant D))
      nlinarith only [hi]
    _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg (by positivity) _)

private instance certificate_instance_0557 : OAI.SidorenkoCounterexample.ProofCertificate_0557 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19 q20 q21
  exact @certificate_proof_0557 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19 q20 q21

end PairBound
theorem certificate_proof_0558 (D r c : ℕ) (s : Fin 3 → ℕ) (b : Bool)
    (x : FaceTailChoice D r c s b) : 0≤faceTailConstant D r c s b x := by
  cases b
  · exact (lowerTailConstant_pos D r).le
  · exact fullTailConstant_nonneg D r c s x

private instance certificate_instance_0558 : OAI.SidorenkoCounterexample.ProofCertificate_0558 := by
  constructor
  intro q0 q1 q2 q3 q4 q5
  exact @certificate_proof_0558 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 q0 q1 q2 q3 q4 q5

theorem certificate_proof_0559 (D r c : ℕ) (s : Fin 3 → ℕ) (b : Bool)
    (x : FaceTailChoice D r c s b) : (faceTailTuple D r c s b x).c=c := by cases b <;> rfl

private instance certificate_instance_0559 : OAI.SidorenkoCounterexample.ProofCertificate_0559 := by
  constructor
  intro q0 q1 q2 q3 q4 q5
  exact @certificate_proof_0559 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 q0 q1 q2 q3 q4 q5

theorem certificate_proof_0560 (D r c : ℕ) (s : Fin 3 → ℕ) (b : Bool)
    (x : FaceTailChoice D r c s b) (i : Fin 3) : (faceTailTuple D r c s b x).s i=s i := by
  cases b
  · exact lowerTailTuple_s _ _ _
  · exact plantedTailTuple_s _ _ _ _ _ _ _

private instance certificate_instance_0560 : OAI.SidorenkoCounterexample.ProofCertificate_0560 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6
  exact @certificate_proof_0560 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 q0 q1 q2 q3 q4 q5 q6

theorem certificate_proof_0561 (D r c : ℕ) (s : Fin 3 → ℕ) (hr : D=2*r)
    (hc : c≤D) (hs : (∑ i,s i)≤D-c) (b : Bool) (x : FaceTailChoice D r c s b) :
    TailFeasible D b (faceTailTuple D r c s b x) := by
  cases b
  · exact lowerTailTuple_feasible D c s hc hs
  · exact plantedTailTuple_feasible D r c hr hc s hs x.1 x.2

private instance certificate_instance_0561 : OAI.SidorenkoCounterexample.ProofCertificate_0561 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8
  exact @certificate_proof_0561 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 q0 q1 q2 q3 q4 q5 q6 q7 q8

theorem certificate_proof_0562 (D r c : ℕ) (s : Fin 3 → ℕ) (q : ℝ) :
    faceTailMajorant D r c s true q=fullTailMajorant D r c s q := rfl

private instance certificate_instance_0562 : OAI.SidorenkoCounterexample.ProofCertificate_0562 := by
  constructor
  intro q0 q1 q2 q3 q4
  exact @certificate_proof_0562 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 q0 q1 q2 q3 q4

theorem certificate_proof_0563 (D r c : ℕ) (s : Fin 3 → ℕ) (q : ℝ) :
    faceTailMajorant D r c s false q=lowerTailConstant D r*q^(tailGain D false (lowerTailTuple c s)) := by
  let : Unique (FaceTailChoice D r c s false) := inferInstanceAs (Unique Unit)
  rw [faceTailMajorant,Fintype.sum_unique]
  rfl

private instance certificate_instance_0563 : OAI.SidorenkoCounterexample.ProofCertificate_0563 := by
  constructor
  intro q0 q1 q2 q3 q4
  exact @certificate_proof_0563 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 q0 q1 q2 q3 q4

theorem certificate_proof_0564 (D r c : ℕ) (s : Fin 3 → ℕ) (b : Bool) (q : ℝ) (hq : 0≤q) :
    0≤faceTailMajorant D r c s b q := by
  apply Finset.sum_nonneg
  intro x _
  exact mul_nonneg (faceTailConstant_pos _ _ _ _ _ _) (Real.rpow_nonneg hq _)

private instance certificate_instance_0564 : OAI.SidorenkoCounterexample.ProofCertificate_0564 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6
  exact @certificate_proof_0564 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 q0 q1 q2 q3 q4 q5 q6

end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
open scoped BigOperators
section Actual
variable {K E : Type} [Field K] [AddCommGroup E] [Module K E] [Fintype K] [Finite E]
variable (ω : LinearMap.BilinForm K E)
omit [Fintype K] [Finite E] in
theorem certificate_proof_0565 {c : Fin 22 → ℕ} {h : Fin 33 → ℕ} {L : Fin 13 → SymplecticLagrangian ω}
    (hL : PointProfile ω c h L) (j : Fin 22) :
    LocalProfile ω (c j) (h (facePair j 0)) (h (facePair j 1)) (h (facePair j 2))
      (L (faceVertex j 0)) (L (faceVertex j 1)) (L (faceVertex j 2)) := by
  apply PointProfile.local ω hL j (faceVertex j 0) (faceVertex j 1) (faceVertex j 2)
    (facePair j 0) (facePair j 1) (facePair j 2) (faceVertex_correct j)
  · exact faceVertex_pairs j 0
  · exact faceVertex_pairs j 1
  · exact faceVertex_pairs j 2

private instance certificate_instance_0565 : OAI.SidorenkoCounterexample.ProofCertificate_0565 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10
  exact @certificate_proof_0565 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10

theorem certificate_proof_0566 (ha : ω.IsAlt) (hω : ω.Nondegenerate)
    (D : ℕ) (hD : 2*D=finrank K E) {c : Fin 22 → ℕ} {h : Fin 33 → ℕ}
    {L : Fin 13 → SymplecticLagrangian ω} (hL : PointProfile ω c h L) : GeometricProfile D c h := by
  have hl := hL.faceLocal ω
  have hc (j : Fin 22) : c j≤D := by
    rw [←(hl j).1]
    exact isotropic_finrank_le_half ω hω D hD _
      (by intro x hx y hy; exact (L (faceVertex j 0)).property.ge hx.1.1 y hy.1.1)
  refine ⟨hc,?_,?_⟩
  · intro j i
    have hp := hl j
    fin_cases i
    · change c j≤h (facePair j 0)
      rw [←hp.1,←hp.2.1]; exact Submodule.finrank_mono inf_le_left
    · change c j≤h (facePair j 1)
      rw [←hp.1,←hp.2.2.1]; exact Submodule.finrank_mono (inf_le_inf inf_le_left le_rfl)
    · change c j≤h (facePair j 2)
      rw [←hp.1,←hp.2.2.2]; exact Submodule.finrank_mono (inf_le_inf inf_le_right le_rfl)
  · intro j
    have hp := actual_profile_pair_sum_le ω ha hω D (c j) (h (facePair j 0))
      (h (facePair j 1)) (h (facePair j 2)) hD
      ⟨⟨L (faceVertex j 0),L (faceVertex j 1),L (faceVertex j 2)⟩,hl j⟩
    simpa only [profileS,Fin.sum_univ_three] using hp

private instance certificate_instance_0566 : OAI.SidorenkoCounterexample.ProofCertificate_0566 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15
  exact @certificate_proof_0566 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15

end Actual
theorem certificate_proof_0567 (D : ℕ) (c : Fin 22 → ℕ) (h : Fin 33 → ℕ)
    (hc : ∀ j i,c j≤h (facePair j i)) :
    profileCost D c h=(∑ j,faceBaseline D (c j) (fun i=>profileS c h j i))+separationExcess h := by
  have he (j : Fin 22) (i : Fin 3) : (c j:ℝ)+((h (facePair j i)-c j:ℕ):ℝ)=(h (facePair j i):ℝ) := by
    rw [Nat.cast_sub (hc j i)]
    ring
  unfold profileCost faceNaturalCost faceBaseline
  simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_one,Nat.cast_sum,triangular_nat,Finset.sum_sub_distrib,
    ←Finset.sum_div,profileS,he]
  rw [sum_face_pairs (fun e=>triangular (h e))]
  unfold separationExcess
  simp only [div_mul_eq_mul_div,←Finset.sum_div,sub_mul,Finset.sum_sub_distrib,one_mul,←Finset.mul_sum]
  ring

private instance certificate_instance_0567 : OAI.SidorenkoCounterexample.ProofCertificate_0567 := by
  constructor
  intro q0 q1 q2 q3
  exact @certificate_proof_0567 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 q0 q1 q2 q3

theorem certificate_proof_0568 (D r : ℕ) (c : Fin 22 → ℕ) (h : Fin 33 → ℕ) (full : Fin 22 → Bool)
    (x : GlobalTailChoice D r c h full) : 0≤globalTailConstant D r c h full x :=
  Finset.prod_nonneg (fun j _=>faceTailConstant_pos D r (c j) (profileS c h j) (full j) (x j))

private instance certificate_instance_0568 : OAI.SidorenkoCounterexample.ProofCertificate_0568 := by
  constructor
  intro q0 q1 q2 q3 q4 q5
  exact @certificate_proof_0568 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 q0 q1 q2 q3 q4 q5

theorem certificate_proof_0569 (D r : ℕ) (hr : D=2*r) (c : Fin 22 → ℕ) (h : Fin 33 → ℕ)
    (hp : GeometricProfile D c h) (full : Fin 22 → Bool) (x : GlobalTailChoice D r c h full) :
    GlobalTailFeasible D full (globalTailTuple D r c h full x) h := by
  refine ⟨fun j=>faceTailTuple_feasible D r (c j) (profileS c h j) hr (hp.1 j) (hp.2.2 j) (full j) (x j),?_⟩
  intro j i
  simp only [globalTailTuple,TailTuple.h,faceTailTuple_c,faceTailTuple_s,profileS]
  exact Nat.add_sub_of_le (hp.2.1 j i)

private instance certificate_instance_0569 : OAI.SidorenkoCounterexample.ProofCertificate_0569 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7
  exact @certificate_proof_0569 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 q0 q1 q2 q3 q4 q5 q6 q7

theorem certificate_proof_0570 (D r : ℕ) (c : Fin 22 → ℕ) (h : Fin 33 → ℕ)
    (hp : GeometricProfile D c h) (full : Fin 22 → Bool) (x : GlobalTailChoice D r c h full) :
    profileCost D c h-globalTailGain D r c h full x=
      (∑ j,tailSlack D (full j) (globalTailTuple D r c h full x j))+separationExcess h := by
  rw [profileCost_baseline D c h hp.2.1]
  simp only [tailSlack,globalTailTuple,faceTailTuple_c,faceTailTuple_s,Finset.sum_sub_distrib,globalTailGain]
  ring

private instance certificate_instance_0570 : OAI.SidorenkoCounterexample.ProofCertificate_0570 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6
  exact @certificate_proof_0570 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 q0 q1 q2 q3 q4 q5 q6

theorem certificate_proof_0571 (D r : ℕ) (c : Fin 22 → ℕ) (h : Fin 33 → ℕ) (full : Fin 22 → Bool)
    (q : ℝ) (hq : 0<q) :
    (∏ j,faceTailMajorant D r (c j) (profileS c h j) (full j) q)=
      ∑ x : GlobalTailChoice D r c h full,globalTailConstant D r c h full x*q^(globalTailGain D r c h full x) := by
  classical
  unfold faceTailMajorant
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.prod_mul_distrib,←Real.rpow_sum_of_pos hq]
  rfl

private instance certificate_instance_0571 : OAI.SidorenkoCounterexample.ProofCertificate_0571 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6
  exact @certificate_proof_0571 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 q0 q1 q2 q3 q4 q5 q6

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
end ActualProfile
end SidorenkoCounterexample
end OAI

theorem solution : OAI.SidorenkoCounterexample.ProofCertificate_0535 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0536 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0537 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0538 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0539 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0540 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0541 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0542 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0543 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0544 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0545 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0546 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0547 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0548 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0549 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0550 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0551 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0552 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0553 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0554 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0555 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0556 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0557 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0558 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0559 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0560 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0561 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0562 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0563 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0564 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0565 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0566 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0567 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0568 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0569 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0570 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0571 := by
  exact ⟨inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance⟩
end

