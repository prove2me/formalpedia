-- Prove2me | solution 1 for OAI.SidorenkoCounterexample.finite_geometry_batch_13
-- status  : ACCEPTED   (prove)
-- author  : @abcdefg
-- created : 2026-10-09T06:19:32.996212+00:00
-- url     : https://prove2.me/submissions/0330c74e-0856-42db-a26e-81299b370070

import Definitions.Def_SidorenkoCertificateBundleA
set_option linter.unusedVariables false
section
variable [p0 : OAI.SidorenkoCounterexample.ProofCertificate_0005]
  [p1 : OAI.SidorenkoCounterexample.ProofCertificate_0010]
  [p2 : OAI.SidorenkoCounterexample.ProofCertificate_0013]
  [p3 : OAI.SidorenkoCounterexample.ProofCertificate_0014]
  [p4 : OAI.SidorenkoCounterexample.ProofCertificate_0017]
  [p5 : OAI.SidorenkoCounterexample.ProofCertificate_0020]
  [p6 : OAI.SidorenkoCounterexample.ProofCertificate_0029]
  [p7 : OAI.SidorenkoCounterexample.ProofCertificate_0030]
  [p8 : OAI.SidorenkoCounterexample.ProofCertificate_0031]
  [p9 : OAI.SidorenkoCounterexample.ProofCertificate_0032]
  [p10 : OAI.SidorenkoCounterexample.ProofCertificate_0034]
  [p11 : OAI.SidorenkoCounterexample.ProofCertificate_0038]
  [p12 : OAI.SidorenkoCounterexample.ProofCertificate_0069]
  [p13 : OAI.SidorenkoCounterexample.ProofCertificate_0106]
  [p14 : OAI.SidorenkoCounterexample.ProofCertificate_0107]
  [p15 : OAI.SidorenkoCounterexample.ProofCertificate_0108]
  [p16 : OAI.SidorenkoCounterexample.ProofCertificate_0110]
  [p17 : OAI.SidorenkoCounterexample.ProofCertificate_0111]
  [p18 : OAI.SidorenkoCounterexample.ProofCertificate_0112]
  [p19 : OAI.SidorenkoCounterexample.ProofCertificate_0122]
  [p20 : OAI.SidorenkoCounterexample.ProofCertificate_0148]
  [p21 : OAI.SidorenkoCounterexample.ProofCertificate_0153]
  [p22 : OAI.SidorenkoCounterexample.ProofCertificate_0168]
  [p23 : OAI.SidorenkoCounterexample.ProofCertificate_0169]
  [p24 : OAI.SidorenkoCounterexample.ProofCertificate_0172]
  [p25 : OAI.SidorenkoCounterexample.ProofCertificate_0207]
  [p26 : OAI.SidorenkoCounterexample.ProofCertificate_0214]
  [p27 : OAI.SidorenkoCounterexample.ProofCertificate_0216]
  [p28 : OAI.SidorenkoCounterexample.ProofCertificate_0217]
  [p29 : OAI.SidorenkoCounterexample.ProofCertificate_0220]
  [p30 : OAI.SidorenkoCounterexample.ProofCertificate_0221]
  [p31 : OAI.SidorenkoCounterexample.ProofCertificate_0271]
  [p32 : OAI.SidorenkoCounterexample.ProofCertificate_0273]
  [p33 : OAI.SidorenkoCounterexample.ProofCertificate_0291]
  [p34 : OAI.SidorenkoCounterexample.ProofCertificate_0292]
  [p35 : OAI.SidorenkoCounterexample.ProofCertificate_0293]
  [p36 : OAI.SidorenkoCounterexample.ProofCertificate_0294]
  [p37 : OAI.SidorenkoCounterexample.ProofCertificate_0295]
include p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37

namespace OAI
namespace SidorenkoCounterexample
open Module
section CommonOrbitGeometry
variable {K E : Type} [Field K] [AddCommGroup E] [Module K E]
  [FiniteDimensional K E]
variable (ω : LinearMap.BilinForm K E)
variable [Finite E]
end CommonOrbitGeometry
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
section AllOrbitMass
variable {K E : Type} [Field K] [AddCommGroup E] [Module K E]
  [Fintype K] [Finite E] [Invertible (2:K)]
variable (ω : LinearMap.BilinForm K E)
end AllOrbitMass
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
section ConfigurationUpper
variable {K E : Type} [Field K] [AddCommGroup E] [Module K E] [Finite E]
variable (ω : LinearMap.BilinForm K E)
end ConfigurationUpper
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
section DecompositionTransitivity
variable {K E F : Type} [Field K] [AddCommGroup E] [Module K E] [AddCommGroup F] [Module K F]
variable [FiniteDimensional K E] [FiniteDimensional K F]
end DecompositionTransitivity
section ConfigTransitivity
variable {K E : Type} [Field K] [AddCommGroup E] [Module K E] [Finite E]
variable (ω : LinearMap.BilinForm K E)
end ConfigTransitivity
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
section ConfigurationBound
variable {K E : Type} [Field K] [AddCommGroup E] [Module K E] [Fintype K] [Finite E]
variable (ω : LinearMap.BilinForm K E)
end ConfigurationBound
section CommonZeroProfiles
variable {K E : Type} [Field K] [AddCommGroup E] [Module K E] [FiniteDimensional K E]
variable (ω : LinearMap.BilinForm K E)
variable [Finite E]
end CommonZeroProfiles
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
section CommonZeroMass
variable {K E : Type} [Field K] [AddCommGroup E] [Module K E] [Fintype K] [Finite E]
variable (ω : LinearMap.BilinForm K E)
end CommonZeroMass
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
section ProfileQuotient
variable {K E : Type} [Field K] [AddCommGroup E] [Module K E] [FiniteDimensional K E]
variable (ω : LinearMap.BilinForm K E)
theorem certificate_proof_0296 (ha : ω.IsAlt) {c u v w : ℕ}
    (S : IsotropicDimspace ω c)
    (p₀ : {p : TripleDimProfile ω c u v w // tripleProfileCommon ω p = S}) :
    ∃ L M N : SymplecticLagrangian (symplecticReductionForm ω S.val ha),
      (L.val ⊓ M.val) ⊓ N.val = ⊥ ∧
      finrank K ↥(L.val ⊓ M.val) = u-c ∧
      finrank K ↥(L.val ⊓ N.val) = v-c ∧
      finrank K ↥(M.val ⊓ N.val) = w-c ∧
      ∃ f : {p : TripleDimProfile ω c u v w // tripleProfileCommon ω p = S} →
        CommonZeroDimProfile (symplecticReductionForm ω S.val ha) L M N, Function.Injective f := by
  let F := {p : TripleDimProfile ω c u v w // tripleProfileCommon ω p = S}
  have heq (p : F) : (p.val.val.1.val ⊓ p.val.val.2.1.val) ⊓ p.val.val.2.2.val = S.val :=
    congrArg Subtype.val p.property
  have hL (p : F) : S.val ≤ p.val.val.1.val := (heq p).symm ▸ inf_le_left.trans inf_le_left
  have hM (p : F) : S.val ≤ p.val.val.2.1.val := (heq p).symm ▸ inf_le_left.trans inf_le_right
  have hN (p : F) : S.val ≤ p.val.val.2.2.val := (heq p).symm ▸ inf_le_right
  let L (p : F) := commonReductionLagrangian ω S.val ha S.property.1 p.val.val.1 (hL p)
  let M (p : F) := commonReductionLagrangian ω S.val ha S.property.1 p.val.val.2.1 (hM p)
  let N (p : F) := commonReductionLagrangian ω S.val ha S.property.1 p.val.val.2.2 (hN p)
  have hzero (p : F) : ((L p).val ⊓ (M p).val) ⊓ (N p).val = ⊥ := by
    change (reduceSubspace ω S.val p.val.val.1.val ⊓ reduceSubspace ω S.val p.val.val.2.1.val) ⊓
      reduceSubspace ω S.val p.val.val.2.2.val = ⊥
    rw [←reduceSubspace_inf ω S.val _ _ (hL p),←reduceSubspace_inf ω S.val _ _ (le_inf (hL p) (hM p)),heq p]
    exact reduceSubspace_self ω S.val
  have hu (p : F) : finrank K ↥((L p).val ⊓ (M p).val) = u-c := by
    change finrank K ↥(reduceSubspace ω S.val p.val.val.1.val ⊓ reduceSubspace ω S.val p.val.val.2.1.val) = _
    rw [reducePair_finrank ω S.val _ _ (hL p) (hM p),p.val.property.2.1,S.property.2]
  have hv (p : F) : finrank K ↥((L p).val ⊓ (N p).val) = v-c := by
    change finrank K ↥(reduceSubspace ω S.val p.val.val.1.val ⊓ reduceSubspace ω S.val p.val.val.2.2.val) = _
    rw [reducePair_finrank ω S.val _ _ (hL p) (hN p),p.val.property.2.2.1,S.property.2]
  have hw (p : F) : finrank K ↥((M p).val ⊓ (N p).val) = w-c := by
    change finrank K ↥(reduceSubspace ω S.val p.val.val.2.1.val ⊓ reduceSubspace ω S.val p.val.val.2.2.val) = _
    rw [reducePair_finrank ω S.val _ _ (hM p) (hN p),p.val.property.2.2.2,S.property.2]
  let f (p : F) : CommonZeroDimProfile (symplecticReductionForm ω S.val ha) (L p₀) (M p₀) (N p₀) :=
    ⟨(L p,M p,N p),hzero p,(hu p).trans (hu p₀).symm,(hv p).trans (hv p₀).symm,(hw p).trans (hw p₀).symm⟩
  refine ⟨L p₀,M p₀,N p₀,hzero p₀,hu p₀,hv p₀,hw p₀,f,?_⟩
  intro p q hpq
  have heL : (L p).val = (L q).val := congrArg (fun r => r.val.1.val) hpq
  have heM : (M p).val = (M q).val := congrArg (fun r => r.val.2.1.val) hpq
  have heN : (N p).val = (N q).val := congrArg (fun r => r.val.2.2.val) hpq
  have hpL : p.val.val.1 = q.val.val.1 := congrArg Subtype.val
    (reduceLagrangian_injective ω S.val (a₁ := ⟨p.val.val.1,hL p⟩) (a₂ := ⟨q.val.val.1,hL q⟩) heL)
  have hpM : p.val.val.2.1 = q.val.val.2.1 := congrArg Subtype.val
    (reduceLagrangian_injective ω S.val (a₁ := ⟨p.val.val.2.1,hM p⟩) (a₂ := ⟨q.val.val.2.1,hM q⟩) heM)
  have hpN : p.val.val.2.2 = q.val.val.2.2 := congrArg Subtype.val
    (reduceLagrangian_injective ω S.val (a₁ := ⟨p.val.val.2.2,hN p⟩) (a₂ := ⟨q.val.val.2.2,hN q⟩) heN)
  exact Subtype.ext (Subtype.ext (Prod.ext hpL (Prod.ext hpM hpN)))

private instance certificate_instance_0296 : OAI.SidorenkoCounterexample.ProofCertificate_0296 := by
  constructor
  intro c0 c1 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13
  exact @certificate_proof_0296 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13

end ProfileQuotient
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
open scoped BigOperators
section AllProfileMass
variable {K E : Type} [Field K] [AddCommGroup E] [Module K E] [Fintype K] [Finite E]
variable (ω : LinearMap.BilinForm K E)
theorem certificate_proof_0297 (h2 : (2:K) ≠ 0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
    (D : ℕ) (hD : 2*D = finrank K E) {c u v w : ℕ} (S : IsotropicDimspace ω c) :
    (Fintype.card K : ℝ)^((u-c+1).choose 2+(v-c+1).choose 2+(w-c+1).choose 2) *
      Nat.card {p : TripleDimProfile ω c u v w // tripleProfileCommon ω p = S} ≤
        profileMassConstant (D-c) * (Fintype.card K : ℝ)^(3*(D-c+1).choose 2) := by
  classical
  let F := {p : TripleDimProfile ω c u v w // tripleProfileCommon ω p = S}
  by_cases hF : Nonempty F
  · obtain ⟨p₀⟩ := hF
    obtain ⟨L,M,N,hzero,hu,hv,hw,f,hf⟩ := fixedCommonProfile_injection ω ha S p₀
    let : Finite (ReducedSpace ω S.val) := Module.finite_of_finite K
    have hc : c ≤ D := S.property.2 ▸ isotropic_finrank_le_half ω hω D hD S.val S.property.1
    have hdim : 2*(D-c) = finrank K (ReducedSpace ω S.val) := by
      have hh := reducedSpace_finrank ω S.val hω S.property.1
      rw [S.property.2,←hD] at hh
      omega
    have hp := commonZeroProfile_card_upper (symplecticReductionForm ω S.val ha) h2
      (symplecticReductionForm_alt ω S.val ha) (symplecticReductionForm_nondegenerate ω S.val ha hω)
      (D-c) hdim L M N hzero
    rw [hu,hv,hw] at hp
    have hc : (Nat.card F : ℝ) ≤ Nat.card (CommonZeroDimProfile (symplecticReductionForm ω S.val ha) L M N) := by
      exact_mod_cast Nat.card_le_card_of_injective f hf
    exact (mul_le_mul_of_nonneg_left hc (by positivity)).trans hp
  · have h_empty : IsEmpty F := not_nonempty_iff.mp hF
    have hc : Nat.card F = 0 := Nat.card_eq_zero.mpr (Or.inl h_empty)
    change _ * (Nat.card F : ℝ) ≤ _
    rw [hc,Nat.cast_zero,mul_zero]
    exact mul_nonneg (le_of_lt (profileMassConstant_pos _)) (by positivity)

private instance certificate_instance_0297 : OAI.SidorenkoCounterexample.ProofCertificate_0297 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17
  exact @certificate_proof_0297 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17

theorem certificate_proof_0298 (D : ℕ) : 0 < fullProfileConstant D :=
  mul_pos (mul_pos (lagrangianConstant_pos _) (by positivity)) (profileMassConstant_pos _)

private instance certificate_instance_0298 : OAI.SidorenkoCounterexample.ProofCertificate_0298 := by
  constructor
  intro q0
  exact @certificate_proof_0298 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 q0

theorem certificate_proof_0299 (h2 : (2:K) ≠ 0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
    (D : ℕ) (hD : 2*D = finrank K E) (c u v w : ℕ) (hc : c ≤ D) :
    (Fintype.card K : ℝ)^((D+1)*c + ((u-c+1).choose 2+(v-c+1).choose 2+(w-c+1).choose 2)) *
      Nat.card (TripleDimProfile ω c u v w) ≤ fullProfileConstant D * (Fintype.card K : ℝ)^(3*(D+1).choose 2) := by
  classical
  let := Fintype.ofFinite (IsotropicDimspace ω c)
  let δ := (u-c+1).choose 2+(v-c+1).choose 2+(w-c+1).choose 2
  let q : ℝ := Fintype.card K
  have hi := (isotropic_card_bounds ω h2 ha hω D hD c hc).2
  have hsum : (Nat.card (TripleDimProfile ω c u v w) : ℝ) =
      ∑ S : IsotropicDimspace ω c, (Nat.card {p : TripleDimProfile ω c u v w // tripleProfileCommon ω p = S} : ℝ) := by
    have hh := (Nat.card_congr (Equiv.sigmaFiberEquiv (tripleProfileCommon ω (c := c) (u := u) (v := v) (w := w)))).symm
    rw [Nat.card_sigma] at hh
    exact_mod_cast hh
  have hbase : q^δ * Nat.card (TripleDimProfile ω c u v w) ≤
      (Nat.card (IsotropicDimspace ω c) : ℝ) * (profileMassConstant (D-c)*q^(3*(D-c+1).choose 2)) := by
    rw [hsum,Finset.mul_sum]
    calc
      _ ≤ ∑ _S : IsotropicDimspace ω c, profileMassConstant (D-c)*q^(3*(D-c+1).choose 2) :=
        Finset.sum_le_sum (fun S _ => fixedCommonProfile_card_upper ω h2 ha hω D hD S)
      _ = _ := by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Nat.card_eq_fintype_card]
  have hk : (lagrangianConstant D*2^c)*profileMassConstant (D-c) ≤ fullProfileConstant D := by
    exact mul_le_mul
      (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by norm_num) hc) (le_of_lt (lagrangianConstant_pos _)))
      (profileMassConstant_mono (Nat.sub_le D c)) (le_of_lt (profileMassConstant_pos _))
      (mul_nonneg (le_of_lt (lagrangianConstant_pos _)) (by positivity))
  have hconst := fullProfileConstant_pos D
  calc
    _ = q^((D+1)*c) * (q^δ * Nat.card (TripleDimProfile ω c u v w)) := by rw [pow_add,mul_assoc]
    _ ≤ q^((D+1)*c) * ((Nat.card (IsotropicDimspace ω c) : ℝ)*(profileMassConstant (D-c)*q^(3*(D-c+1).choose 2))) :=
      mul_le_mul_of_nonneg_left hbase (by positivity)
    _ ≤ q^((D+1)*c) * (((lagrangianConstant D*2^c)*q^isotropicExponent D c)*(profileMassConstant (D-c)*q^(3*(D-c+1).choose 2))) := by
      gcongr
      exact mul_nonneg (le_of_lt (profileMassConstant_pos _)) (by positivity)
    _ = ((lagrangianConstant D*2^c)*profileMassConstant (D-c))*q^(isotropicExponent D c+3*(D-c+1).choose 2+(D+1)*c) := by
      simp only [pow_add]; ring
    _ = ((lagrangianConstant D*2^c)*profileMassConstant (D-c))*q^(3*(D+1).choose 2) := by
      rw [common_cost_cancellation D c hc]
    _ ≤ _ := mul_le_mul_of_nonneg_right hk (by positivity)

private instance certificate_instance_0299 : OAI.SidorenkoCounterexample.ProofCertificate_0299 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17
  exact @certificate_proof_0299 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17

end AllProfileMass
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
open scoped BigOperators
section GeneralPairCounts
variable {K E : Type} [Field K] [AddCommGroup E] [Module K E] [Fintype K] [Finite E]
variable (ω : LinearMap.BilinForm K E)
theorem certificate_proof_0300 (h2 : (2:K) ≠ 0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
    (A : SymplecticLagrangian ω) (h : ℕ) (hh : h ≤ finrank K A.val) :
    Nat.card {L : SymplecticLagrangian ω // finrank K ↥(L.val ⊓ A.val) = h} =
      Nat.card (DimSubspace K A.val (finrank K A.val-h)) * (Fintype.card K)^((finrank K A.val-h+1).choose 2) := by
  classical
  obtain ⟨e,_,he⟩ := exists_lagrangian_coordinates ω A.val h2 ha hω A.property
  let f := symplecticLagrangianEquiv canonicalSymplectic ω e he
  let A₀ := f.symm A
  have hm : A₀.val.map e.toLinearMap = A.val := congrArg Subtype.val (f.apply_symm_apply A)
  have hd (L : Lagrangian (K := K) (V := A.val)) :
      finrank K ↥((f L).val ⊓ A.val) = finrank K ↥(L.val ⊓ A₀.val) := by
    change finrank K ↥(L.val.map e.toLinearMap ⊓ A.val) = _
    calc
      _ = finrank K ↥(L.val.map e.toLinearMap ⊓ A₀.val.map e.toLinearMap) :=
        congrArg (fun S : Submodule K E => finrank K ↥(L.val.map e.toLinearMap ⊓ S)) hm.symm
      _ = _ := by rw [←Submodule.map_inf e.toLinearMap e.injective]; exact e.finrank_map_eq _
  have hc : Nat.card {L : Lagrangian (K := K) (V := A.val) // finrank K ↥(L.val ⊓ A₀.val) = h} =
      Nat.card {L : SymplecticLagrangian ω // finrank K ↥(L.val ⊓ A.val) = h} :=
    Nat.card_congr (f.subtypeEquiv (fun L => by rw [hd]))
  rw [←hc]
  exact lagrangian_pair_count h2 A₀ h hh

private instance certificate_instance_0300 : OAI.SidorenkoCounterexample.ProofCertificate_0300 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13
  exact @certificate_proof_0300 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13

theorem certificate_proof_0301 (h2 : (2:K) ≠ 0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
    (D : ℕ) (hD : 2*D = finrank K E) (A : SymplecticLagrangian ω) (h : ℕ) (hh : h ≤ D) :
    (Fintype.card K : ℝ)^((D+1).choose 2) ≤ (Fintype.card K : ℝ)^((h+1).choose 2) *
      Nat.card {L : SymplecticLagrangian ω // finrank K ↥(L.val ⊓ A.val) = h} ∧
    (Fintype.card K : ℝ)^((h+1).choose 2) *
      Nat.card {L : SymplecticLagrangian ω // finrank K ↥(L.val ⊓ A.val) = h} ≤
        2^D*(Fintype.card K : ℝ)^((D+1).choose 2) := by
  have hd : finrank K A.val = D := by
    have h := self_orthogonal_twice_finrank ω A.val hω A.property
    omega
  have hhA : h ≤ finrank K A.val := by omega
  have hcount := symplectic_pair_count ω h2 ha hω A h hhA
  rw [hd] at hcount
  rw [hcount,Nat.cast_mul,Nat.cast_pow]
  have hl := subspace_count_lower (K := K) (V := A.val) (D-h) (by omega)
  have hu := subspace_count_upper (K := K) (V := A.val) (D-h) (by omega)
  rw [hd,Nat.sub_sub_self hh] at hl hu
  have he : (Fintype.card K : ℝ)^((h+1).choose 2) *
      ((Fintype.card K : ℝ)^((D-h)*h)*(Fintype.card K : ℝ)^((D-h+1).choose 2)) =
      (Fintype.card K : ℝ)^((D+1).choose 2) := by
    rw [←pow_add,←pow_add]
    congr 1
    have hexp := symmetric_nullity_exponent D h hh
    rw [Nat.mul_comm h (D-h)] at hexp
    omega
  constructor
  · rw [←he]
    gcongr
  · calc
      _ ≤ (Fintype.card K : ℝ)^((h+1).choose 2) *
        ((2^(D-h)*(Fintype.card K : ℝ)^((D-h)*h))*(Fintype.card K : ℝ)^((D-h+1).choose 2)) := by gcongr
      _ = 2^(D-h)*(Fintype.card K : ℝ)^((D+1).choose 2) := by rw [←he]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (pow_le_pow_right₀ (by norm_num) (Nat.sub_le D h)) (by positivity)

private instance certificate_instance_0301 : OAI.SidorenkoCounterexample.ProofCertificate_0301 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15
  exact @certificate_proof_0301 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15

theorem certificate_proof_0302 (h2 : (2:K) ≠ 0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
    (D : ℕ) (hD : 2*D = finrank K E) (h : ℕ) (hh : h ≤ D) :
    (Fintype.card K : ℝ)^(2*(D+1).choose 2) ≤ (Fintype.card K : ℝ)^((h+1).choose 2) * Nat.card (OrderedPairDim ω h) := by
  classical
  let := Fintype.ofFinite (SymplecticLagrangian ω)
  have hc : (Nat.card (OrderedPairDim ω h) : ℝ) =
      ∑ A : SymplecticLagrangian ω, (Nat.card {L : SymplecticLagrangian ω // finrank K ↥(L.val ⊓ A.val) = h} : ℝ) := by
    rw [Nat.card_congr (orderedPairDimEquiv ω h),Nat.card_sigma,Nat.cast_sum]
  rw [hc,Finset.mul_sum]
  have he : 2*(D+1).choose 2 = (D+1).choose 2+(D+1).choose 2 := by omega
  rw [he,pow_add]
  calc
    _ ≤ (Nat.card (SymplecticLagrangian ω) : ℝ)*(Fintype.card K : ℝ)^((D+1).choose 2) :=
      mul_le_mul_of_nonneg_right (symplecticLagrangian_card_bounds ω h2 ha hω D hD).1 (by positivity)
    _ = ∑ _A : SymplecticLagrangian ω, (Fintype.card K : ℝ)^((D+1).choose 2) := by
      simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Nat.card_eq_fintype_card]
    _ ≤ _ := Finset.sum_le_sum (fun A _ => (symplectic_pair_card_bounds ω h2 ha hω D hD A h hh).1)

private instance certificate_instance_0302 : OAI.SidorenkoCounterexample.ProofCertificate_0302 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14
  exact @certificate_proof_0302 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14

end GeneralPairCounts
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
section ConditionalProfile
variable {K E : Type} [Field K] [AddCommGroup E] [Module K E] [FiniteDimensional K E]
variable (ω : LinearMap.BilinForm K E)
omit [FiniteDimensional K E] in
theorem certificate_proof_0303 (L M L' M' : SymplecticLagrangian ω)
    (e : E ≃ₗ[K] E) (he : ∀ x y, ω (e x) (e y) = ω x y)
    (hL : L.val.map e.toLinearMap = L'.val) (hM : M.val.map e.toLinearMap = M'.val) (c v w : ℕ) :
    Nat.card (PairCompletion ω L M c v w) = Nat.card (PairCompletion ω L' M' c v w) := by
  let f := lagrangianIsometryEquiv ω e he
  have hp (A B : Submodule K E) : finrank K ↥(A.map e.toLinearMap ⊓ B.map e.toLinearMap) = finrank K ↥(A ⊓ B) := by
    rw [←Submodule.map_inf e.toLinearMap e.injective]
    exact e.finrank_map_eq _
  have hc (P : SymplecticLagrangian ω) : finrank K ↥((L'.val ⊓ M'.val) ⊓ (f P).val) =
      finrank K ↥((L.val ⊓ M.val) ⊓ P.val) := by
    change finrank K ↥((L'.val ⊓ M'.val) ⊓ P.val.map e.toLinearMap) = _
    rw [←hL,←hM,←Submodule.map_inf e.toLinearMap e.injective,hp]
  have hv (P : SymplecticLagrangian ω) : finrank K ↥(L'.val ⊓ (f P).val) = finrank K ↥(L.val ⊓ P.val) := by
    change finrank K ↥(L'.val ⊓ P.val.map e.toLinearMap) = _
    rw [←hL,hp]
  have hw (P : SymplecticLagrangian ω) : finrank K ↥(M'.val ⊓ (f P).val) = finrank K ↥(M.val ⊓ P.val) := by
    change finrank K ↥(M'.val ⊓ P.val.map e.toLinearMap) = _
    rw [←hM,hp]
  exact Nat.card_congr (f.subtypeEquiv (fun P => by rw [hc,hv,hw]))

private instance certificate_instance_0303 : OAI.SidorenkoCounterexample.ProofCertificate_0303 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16
  exact @certificate_proof_0303 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16

variable [Finite E]
theorem certificate_proof_0304 (h2 : (2:K) ≠ 0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
    (L M : SymplecticLagrangian ω) (c v w : ℕ) :
    Nat.card (TripleDimProfile ω c (finrank K ↥(L.val ⊓ M.val)) v w) =
      Nat.card (OrderedPairDim ω (finrank K ↥(L.val ⊓ M.val))) * Nat.card (PairCompletion ω L M c v w) := by
  classical
  let := Fintype.ofFinite (OrderedPairDim ω (finrank K ↥(L.val ⊓ M.val)))
  rw [Nat.card_congr (profilePairCompletionEquiv ω c (finrank K ↥(L.val ⊓ M.val)) v w),Nat.card_sigma]
  have hc (p : OrderedPairDim ω (finrank K ↥(L.val ⊓ M.val))) :
      Nat.card (PairCompletion ω p.val.1 p.val.2 c v w) = Nat.card (PairCompletion ω L M c v w) := by
    obtain ⟨e,he,hL,hM⟩ := ordered_pair_transitivity ω h2 ha hω
      p.val.1.val p.val.2.val L.val M.val p.val.1.property p.val.2.property L.property M.property p.property
    exact pairCompletion_card_congr ω p.val.1 p.val.2 L M e he hL hM c v w
  simp only [hc,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Nat.card_eq_fintype_card]
  simp only [Nat.cast_id]

private instance certificate_instance_0304 : OAI.SidorenkoCounterexample.ProofCertificate_0304 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15
  exact @certificate_proof_0304 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15

variable [Fintype K]
theorem certificate_proof_0305 (h2 : (2:K) ≠ 0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
    (D : ℕ) (hD : 2*D = finrank K E) (L M : SymplecticLagrangian ω) (c v w : ℕ) (hc : c ≤ D) :
    (Fintype.card K : ℝ)^((D+1)*c + ((finrank K ↥(L.val ⊓ M.val)-c+1).choose 2+
      (v-c+1).choose 2+(w-c+1).choose 2)) * Nat.card (PairCompletion ω L M c v w) ≤
        fullProfileConstant D * (Fintype.card K : ℝ)^((finrank K ↥(L.val ⊓ M.val)+1).choose 2+(D+1).choose 2) := by
  let u := finrank K ↥(L.val ⊓ M.val)
  let δ := (D+1)*c + ((u-c+1).choose 2+(v-c+1).choose 2+(w-c+1).choose 2)
  let q : ℝ := Fintype.card K
  have hq : 0 < q := by dsimp [q]; exact_mod_cast Fintype.card_pos (α := K)
  have hu : u ≤ D := by
    have h := self_orthogonal_twice_finrank ω L.val hω L.property
    have hle := Submodule.finrank_mono (show L.val ⊓ M.val ≤ L.val from inf_le_left)
    dsimp [u]
    omega
  have hp := orderedPairDim_card_lower ω h2 ha hω D hD u hu
  have ht := tripleProfile_card_upper ω h2 ha hω D hD c u v w hc
  have hi : (Nat.card (TripleDimProfile ω c u v w) : ℝ) =
      (Nat.card (OrderedPairDim ω u) : ℝ)*Nat.card (PairCompletion ω L M c v w) := by
    exact_mod_cast tripleProfile_completion_card ω h2 ha hω L M c v w
  apply (mul_le_mul_iff_right₀ (pow_pos hq (2*(D+1).choose 2))).mp
  calc
    _ = q^δ*(q^(2*(D+1).choose 2)*Nat.card (PairCompletion ω L M c v w)) := by ring
    _ ≤ q^δ*((q^((u+1).choose 2)*Nat.card (OrderedPairDim ω u))*Nat.card (PairCompletion ω L M c v w)) := by gcongr
    _ = q^((u+1).choose 2)*(q^δ*Nat.card (TripleDimProfile ω c u v w)) := by rw [hi]; ring
    _ ≤ q^((u+1).choose 2)*(fullProfileConstant D*q^(3*(D+1).choose 2)) :=
      mul_le_mul_of_nonneg_left ht (by positivity)
    _ = q^(2*(D+1).choose 2)*(fullProfileConstant D*q^((u+1).choose 2+(D+1).choose 2)) := by
      have he : 3*(D+1).choose 2 = 2*(D+1).choose 2+(D+1).choose 2 := by omega
      rw [he,pow_add,pow_add]
      ring

private instance certificate_instance_0305 : OAI.SidorenkoCounterexample.ProofCertificate_0305 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19
  exact @certificate_proof_0305 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19

end ConditionalProfile
end SidorenkoCounterexample
end OAI
namespace OAI
namespace SidorenkoCounterexample
open Module
open scoped BigOperators
section PlantedQuotient
variable {K E : Type} [Field K] [AddCommGroup E] [Module K E] [FiniteDimensional K E]
variable (ω : LinearMap.BilinForm K E) (S : Submodule K E)
theorem certificate_proof_0306 (A : Submodule K E) (hAP : A ≤ ω.orthogonal S) :
    finrank K (reduceSubspace ω S A) + finrank K ↥(S ⊓ A) = finrank K A := by
  let f : A →ₗ[K] ReducedSpace ω S := (reductionKernel ω S).mkQ.comp (Submodule.inclusion hAP)
  have hk : LinearMap.ker f = (S ⊓ A).comap A.subtype := by
    ext x
    constructor
    · intro hx
      exact ⟨(Submodule.Quotient.mk_eq_zero (reductionKernel ω S)).mp hx,x.property⟩
    · intro hx
      exact (Submodule.Quotient.mk_eq_zero (reductionKernel ω S)).mpr hx.1
  have hr : LinearMap.range f = reduceSubspace ω S A := by
    ext y
    constructor
    · rintro ⟨x,rfl⟩
      exact ⟨⟨x.val,hAP x.property⟩,x.property,rfl⟩
    · rintro ⟨x,hx,rfl⟩
      exact ⟨⟨x.val,hx⟩,rfl⟩
  have hh := f.finrank_range_add_finrank_ker
  rw [hk,hr,(Submodule.comapSubtypeEquivOfLe (inf_le_right : S ⊓ A ≤ A)).finrank_eq] at hh
  exact hh

private instance certificate_instance_0306 : OAI.SidorenkoCounterexample.ProofCertificate_0306 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9
  exact @certificate_proof_0306 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9

theorem certificate_proof_0307 (L Y : Submodule K E)
    (hSL : S ≤ L) (hLP : L ≤ ω.orthogonal S) :
    finrank K ↥(reduceSubspace ω S L ⊓ reduceSubspace ω S Y) + finrank K ↥(S ⊓ Y) =
      finrank K ↥(L ⊓ Y) := by
  rw [←reduceSubspace_inf ω S L Y hSL]
  have hh := reduceSubspace_finrank_general ω S (L ⊓ Y) (inf_le_left.trans hLP)
  have he : S ⊓ (L ⊓ Y) = S ⊓ Y := by rw [←inf_assoc,inf_eq_left.mpr hSL]
  rwa [he] at hh

private instance certificate_instance_0307 : OAI.SidorenkoCounterexample.ProofCertificate_0307 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11
  exact @certificate_proof_0307 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11

end PlantedQuotient
section CenterDisintegration
variable {K E : Type} [Field K] [AddCommGroup E] [Module K E]
variable (ω : LinearMap.BilinForm K E)
theorem certificate_proof_0308 (r : ℕ) (L M N : Submodule K E)
    (P : OrderedTripleOrbit ω L M N) :
    Nat.card (TripleCenterSet ω r P.val.1 P.val.2.1 P.val.2.2) =
      Nat.card (TripleCenterSet ω r L M N) := by
  obtain ⟨e,he,hL,hM,hN⟩ := P.property
  rw [←hL,←hM,←hN]
  exact (Nat.card_congr (tripleCenterIsometryEquiv ω r L M N e he)).symm

private instance certificate_instance_0308 : OAI.SidorenkoCounterexample.ProofCertificate_0308 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10
  exact @certificate_proof_0308 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10

theorem certificate_proof_0309 [Finite E] (r : ℕ) (L M N : Submodule K E) :
    Nat.card (Σ P : OrderedTripleOrbit ω L M N, TripleCenterSet ω r P.val.1 P.val.2.1 P.val.2.2) =
      Nat.card (OrderedTripleOrbit ω L M N) * Nat.card (TripleCenterSet ω r L M N) := by
  classical
  let := Fintype.ofFinite (OrderedTripleOrbit ω L M N)
  rw [Nat.card_sigma]
  simp_rw [tripleCenter_orbit_card ω r L M N]
  simp only [Finset.sum_const,Finset.card_univ,smul_eq_mul,Nat.card_eq_fintype_card]

private instance certificate_instance_0309 : OAI.SidorenkoCounterexample.ProofCertificate_0309 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10
  exact @certificate_proof_0309 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10

end CenterDisintegration
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
open scoped BigOperators
section GenericReducedCount
variable {K E V : Type} [Field K] [AddCommGroup E] [Module K E]
  [AddCommGroup V] [Module K V]
variable (ω : LinearMap.BilinForm K E)
theorem certificate_proof_0310 [FiniteDimensional K E] (h2 : (2:K) ≠ 0)
    (ha : ω.IsAlt) (hω : ω.Nondegenerate) (Y : SymplecticLagrangian ω) :
    ∃ e : (Y.val × Module.Dual K Y.val) ≃ₗ[K] E,
      (∀ x y, ω (e x) (e y) = canonicalSymplectic x y) ∧
      (verticalSpace (K := K) (V := Y.val)).map e.toLinearMap = Y.val := by
  obtain ⟨e,_,he⟩ := exists_lagrangian_coordinates ω Y.val h2 ha hω Y.property
  let f := symplecticLagrangianEquiv canonicalSymplectic ω e he
  let A := f.symm Y
  have hm : A.val.map e.toLinearMap = Y.val := congrArg Subtype.val (f.apply_symm_apply Y)
  obtain ⟨a,ha,hA⟩ := lagrangian_transitivity canonicalSymplectic verticalLagrangian.val h2
    canonicalSymplectic_alt canonicalSymplectic_nondegenerate verticalLagrangian.property A.val A.property
  refine ⟨a.trans e,?_,?_⟩
  · intro x y
    change ω (e (a x)) (e (a y)) = _
    rw [he,ha]
  · change verticalSpace.map (e.toLinearMap.comp a.toLinearMap) = _
    rw [Submodule.map_comp]
    change (verticalLagrangian.val.map a.toLinearMap).map e.toLinearMap = _
    rw [hA,hm]

private instance certificate_instance_0310 : OAI.SidorenkoCounterexample.ProofCertificate_0310 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10
  exact @certificate_proof_0310 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10

theorem certificate_proof_0311 (e : V ≃ₗ[K] E) (A B : Submodule K V) :
    finrank K ↥(A.map e.toLinearMap ⊓ B.map e.toLinearMap) = finrank K ↥(A ⊓ B) := by
  rw [←Submodule.map_inf e.toLinearMap e.injective]
  exact e.finrank_map_eq _

private instance certificate_instance_0311 : OAI.SidorenkoCounterexample.ProofCertificate_0311 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10
  exact @certificate_proof_0311 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10

theorem certificate_proof_0312 (e : V ≃ₗ[K] E) (A B C : Submodule K V) :
    (A.map e.toLinearMap ⊓ B.map e.toLinearMap) ⊓ C.map e.toLinearMap = ⊥ ↔ (A ⊓ B) ⊓ C = ⊥ := by
  rw [←Submodule.map_inf e.toLinearMap e.injective,←Submodule.map_inf e.toLinearMap e.injective]
  constructor
  · intro h
    apply (Submodule.orderIsoMapComap e).injective
    simpa only [Submodule.orderIsoMapComap_apply,Submodule.map_bot] using h
  · intro h
    rw [h,Submodule.map_bot]

private instance certificate_instance_0312 : OAI.SidorenkoCounterexample.ProofCertificate_0312 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11
  exact @certificate_proof_0312 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11

theorem certificate_proof_0313 [Fintype K] [Finite E]
    (h2 : (2:K) ≠ 0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
    (Y : SymplecticLagrangian ω) (r s₀ s₁ s₂ : ℕ) (hr : r ≤ finrank K Y.val) :
    (Nat.card (SymplecticCenterProfile ω Y r s₀ s₁ s₂) : ℝ) /
      (Nat.card (SymplecticCenterStratum ω Y r) : ℝ)^3 ≤
    ∑ θ : BaseParameters (finrank K Y.val) r s₀ s₁ s₂,
      reducedPlantedConstant r s₀ s₁ s₂ θ.val *
        (Fintype.card K : ℝ)^(reducedPlantedExponent (finrank K Y.val) r s₀ s₁ s₂ θ.val) := by
  obtain ⟨e,he,hY⟩ := exists_center_coordinates ω h2 ha hω Y
  rw [←Nat.card_congr (symplecticCenterProfileEquiv ω Y e he hY r s₀ s₁ s₂),
    ←Nat.card_congr (symplecticCenterStratumEquiv ω Y e he hY r)]
  exact canonical_center_profile_probability_bound r s₀ s₁ s₂ hr

private instance certificate_instance_0313 : OAI.SidorenkoCounterexample.ProofCertificate_0313 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16
  exact @certificate_proof_0313 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16

theorem certificate_proof_0314 [Fintype K] [Finite E]
    (hω : ω.Nondegenerate) (D : ℕ) (hD : 2*D = finrank K E)
    (L M N : SymplecticLagrangian ω) (h0 : (L.val ⊓ M.val) ⊓ N.val = ⊥) :
    finrank K ↥(L.val ⊓ M.val)+finrank K ↥(L.val ⊓ N.val)+finrank K ↥(M.val ⊓ N.val) ≤ D := by
  rw [←triplePairSum_finrank _ _ _ h0]
  exact isotropic_finrank_le_half ω hω D hD _ (triplePairSum_isotropic ω _ _ _ L.property M.property N.property)

private instance certificate_instance_0314 : OAI.SidorenkoCounterexample.ProofCertificate_0314 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14
  exact @certificate_proof_0314 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14

end GenericReducedCount
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
open scoped BigOperators
section CommonCenterCounts
variable {K E : Type} [Field K] [AddCommGroup E] [Module K E] [Fintype K] [Finite E]
variable (ω : LinearMap.BilinForm K E)
theorem certificate_proof_0315 (h2 : (2:K) ≠ 0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
    (D : ℕ) (hD : 2*D = finrank K E) (S : Submodule K E)
    (hS : S ≤ ω.orthogonal S) (u : ℕ) (hu : u ≤ finrank K S) :
    (Nat.card (CommonCenterSet ω S u) : ℝ) ≤
      2^u * lagrangianConstant (D-u) *
        (Fintype.card K : ℝ)^(u*(finrank K S-u)+(D-u+1).choose 2) := by
  classical
  let B := CommonCenterSet ω S u
  let Inc := Σ U : DimSubspace K S u, {Y : SymplecticLagrangian ω // U.val.map S.subtype ≤ Y.val}
  let f (Y : B) : Inc :=
    ⟨⟨(S ⊓ Y.val.val).comap S.subtype,
      (Submodule.comapSubtypeEquivOfLe (inf_le_left : S ⊓ Y.val.val ≤ S)).finrank_eq.trans Y.property⟩,
      ⟨Y.val,by rintro x ⟨y,hy,rfl⟩; exact hy.2⟩⟩
  have hf : Function.Injective f := by
    intro Y Z h
    exact Subtype.ext (congrArg (fun i : Inc => i.2.val) h)
  have hb (U : DimSubspace K S u) :
      (Nat.card {Y : SymplecticLagrangian ω // U.val.map S.subtype ≤ Y.val} : ℝ) ≤
      lagrangianConstant (D-u)*(Fintype.card K : ℝ)^((D-u+1).choose 2) := by
    have hle : U.val.map S.subtype ≤ S := by rintro x ⟨y,_,rfl⟩; exact y.property
    have his : U.val.map S.subtype ≤ ω.orthogonal (U.val.map S.subtype) :=
      hle.trans (hS.trans (ω.orthogonal_le hle))
    have hd : finrank K (U.val.map S.subtype) = u :=
      (Submodule.equivMapOfInjective S.subtype S.subtype_injective U.val).finrank_eq.symm.trans U.property
    simpa only [hd] using (containingLagrangian_card_bounds ω h2 ha hω D hD _ his).2
  let := Fintype.ofFinite (DimSubspace K S u)
  have hi : (Nat.card Inc : ℝ) ≤ (Nat.card (DimSubspace K S u) : ℝ)*
      (lagrangianConstant (D-u)*(Fintype.card K : ℝ)^((D-u+1).choose 2)) := by
    rw [Nat.card_sigma,Nat.cast_sum]
    calc
      _ ≤ ∑ U : DimSubspace K S u, lagrangianConstant (D-u)*(Fintype.card K : ℝ)^((D-u+1).choose 2) :=
        Finset.sum_le_sum (fun U _ => hb U)
      _ = _ := by simp [Nat.card_eq_fintype_card]
  calc
    _ ≤ (Nat.card Inc : ℝ) := Nat.cast_le.mpr (Nat.card_le_card_of_injective f hf)
    _ ≤ _ := hi
    _ ≤ (2^u*(Fintype.card K : ℝ)^(u*(finrank K S-u))) *
        (lagrangianConstant (D-u)*(Fintype.card K : ℝ)^((D-u+1).choose 2)) :=
      mul_le_mul_of_nonneg_right (subspace_count_upper u hu)
        (mul_nonneg (lagrangianConstant_pos (D-u)).le (by positivity))
    _ = _ := by rw [pow_add]; ring

private instance certificate_instance_0315 : OAI.SidorenkoCounterexample.ProofCertificate_0315 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16
  exact @certificate_proof_0315 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16

theorem certificate_proof_0316 (h2 : (2:K) ≠ 0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
    (D : ℕ) (hD : 2*D = finrank K E) (S : Submodule K E)
    (hS : S ≤ ω.orthogonal S) (u : ℕ) (hu : u ≤ finrank K S) :
    (Fintype.card K : ℝ)^(u*(D-finrank K S)+(u+1).choose 2) *
      (Nat.card (CommonCenterSet ω S u) : ℝ) ≤
      2^D * lagrangianConstant D * (Fintype.card K : ℝ)^((D+1).choose 2) := by
  have hc := isotropic_finrank_le_half ω hω D hD S hS
  have hud : u ≤ D := hu.trans hc
  have he : u*(D-finrank K S)+(u+1).choose 2+
      (u*(finrank K S-u)+(D-u+1).choose 2) = (D+1).choose 2 := by
    have hh := symmetric_nullity_exponent D u hud
    have hmul : u*(D-finrank K S)+u*(finrank K S-u) = u*(D-u) := by
      rw [←Nat.mul_add]; congr 1; omega
    omega
  have hh := mul_le_mul_of_nonneg_left (commonCenter_card_upper ω h2 ha hω D hD S hS u hu)
    (show 0 ≤ (Fintype.card K : ℝ)^(u*(D-finrank K S)+(u+1).choose 2) by positivity)
  calc
    _ ≤ _ := hh
    _ = (2^u*lagrangianConstant (D-u))*(Fintype.card K : ℝ)^((D+1).choose 2) := by
      rw [←he,pow_add]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul (pow_le_pow_right₀ (show (1:ℝ) ≤ 2 by norm_num) hud)
        (lagrangianConstant_mono (Nat.sub_le D u))
        (lagrangianConstant_pos (D-u)).le (by positivity)) (by positivity)

private instance certificate_instance_0316 : OAI.SidorenkoCounterexample.ProofCertificate_0316 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16
  exact @certificate_proof_0316 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16

end CommonCenterCounts
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
section ReducedCenterInjection
variable {K E : Type} [Field K] [AddCommGroup E] [Module K E] [FiniteDimensional K E]
variable (ω : LinearMap.BilinForm K E)
end ReducedCenterInjection
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
open scoped BigOperators
section ReducedCardBound
variable {K E : Type} [Field K] [AddCommGroup E] [Module K E] [Fintype K] [Finite E]
variable (ω : LinearMap.BilinForm K E)
end ReducedCardBound
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
section FullCenterCoding
variable {K E : Type} [Field K] [AddCommGroup E] [Module K E] [Fintype K] [Finite E]
variable (ω : LinearMap.BilinForm K E)
noncomputable instance (D r c : ℕ) : Fintype (CommonParameters D r c) := Fintype.ofFinite _
end FullCenterCoding
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
open scoped BigOperators
section CommonCountSummation
variable {K E : Type} [Field K] [AddCommGroup E] [Module K E] [Fintype K] [Finite E]
variable (ω : LinearMap.BilinForm K E)
end CommonCountSummation
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
open scoped BigOperators
section FullProfileCenterBound
variable {K E : Type} [Field K] [AddCommGroup E] [Module K E] [Fintype K] [Finite E]
variable (ω : LinearMap.BilinForm K E)
end FullProfileCenterBound
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
section OrbitCenterProfile
variable {K E : Type} [Field K] [AddCommGroup E] [Module K E] [FiniteDimensional K E]
variable (ω : LinearMap.BilinForm K E)
end OrbitCenterProfile
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
open scoped BigOperators
section PointwisePlanted
variable {K E : Type} [Field K] [AddCommGroup E] [Module K E] [Fintype K] [Finite E]
variable (ω : LinearMap.BilinForm K E)
end PointwisePlanted
end SidorenkoCounterexample
end OAI

theorem solution : OAI.SidorenkoCounterexample.ProofCertificate_0296 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0297 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0298 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0299 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0300 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0301 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0302 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0303 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0304 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0305 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0306 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0307 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0308 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0309 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0310 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0311 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0312 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0313 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0314 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0315 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0316 := by
  exact ⟨inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance⟩
end

