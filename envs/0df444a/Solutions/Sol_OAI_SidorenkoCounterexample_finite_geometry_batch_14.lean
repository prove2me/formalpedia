-- Prove2me | solution 1 for OAI.SidorenkoCounterexample.finite_geometry_batch_14
-- status  : ACCEPTED   (prove)
-- author  : @abcdefg
-- created : 2026-10-09T06:17:58.394852+00:00
-- url     : https://prove2.me/submissions/6f7d9a1d-686f-47ef-9373-02ea674c1bde

import Definitions.Def_SidorenkoCertificateBundleA
set_option linter.unusedVariables false
section
variable [p0 : OAI.SidorenkoCounterexample.ProofCertificate_0030]
  [p1 : OAI.SidorenkoCounterexample.ProofCertificate_0032]
  [p2 : OAI.SidorenkoCounterexample.ProofCertificate_0107]
  [p3 : OAI.SidorenkoCounterexample.ProofCertificate_0108]
  [p4 : OAI.SidorenkoCounterexample.ProofCertificate_0110]
  [p5 : OAI.SidorenkoCounterexample.ProofCertificate_0111]
  [p6 : OAI.SidorenkoCounterexample.ProofCertificate_0112]
  [p7 : OAI.SidorenkoCounterexample.ProofCertificate_0121]
  [p8 : OAI.SidorenkoCounterexample.ProofCertificate_0122]
  [p9 : OAI.SidorenkoCounterexample.ProofCertificate_0125]
  [p10 : OAI.SidorenkoCounterexample.ProofCertificate_0168]
  [p11 : OAI.SidorenkoCounterexample.ProofCertificate_0169]
  [p12 : OAI.SidorenkoCounterexample.ProofCertificate_0207]
  [p13 : OAI.SidorenkoCounterexample.ProofCertificate_0214]
  [p14 : OAI.SidorenkoCounterexample.ProofCertificate_0216]
  [p15 : OAI.SidorenkoCounterexample.ProofCertificate_0220]
  [p16 : OAI.SidorenkoCounterexample.ProofCertificate_0281]
  [p17 : OAI.SidorenkoCounterexample.ProofCertificate_0282]
  [p18 : OAI.SidorenkoCounterexample.ProofCertificate_0294]
  [p19 : OAI.SidorenkoCounterexample.ProofCertificate_0295]
  [p20 : OAI.SidorenkoCounterexample.ProofCertificate_0301]
  [p21 : OAI.SidorenkoCounterexample.ProofCertificate_0307]
  [p22 : OAI.SidorenkoCounterexample.ProofCertificate_0309]
  [p23 : OAI.SidorenkoCounterexample.ProofCertificate_0311]
  [p24 : OAI.SidorenkoCounterexample.ProofCertificate_0313]
  [p25 : OAI.SidorenkoCounterexample.ProofCertificate_0315]
include p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25

namespace OAI
namespace SidorenkoCounterexample
open Module
open scoped BigOperators
section PlantedQuotient
variable {K E : Type} [Field K] [AddCommGroup E] [Module K E] [FiniteDimensional K E]
variable (ω : LinearMap.BilinForm K E) (S : Submodule K E)
end PlantedQuotient
section CenterDisintegration
variable {K E : Type} [Field K] [AddCommGroup E] [Module K E]
variable (ω : LinearMap.BilinForm K E)
end CenterDisintegration
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
open scoped BigOperators
section GenericReducedCount
variable {K E V : Type} [Field K] [AddCommGroup E] [Module K E]
  [AddCommGroup V] [Module K V]
variable (ω : LinearMap.BilinForm K E)
end GenericReducedCount
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
open scoped BigOperators
section CommonCenterCounts
variable {K E : Type} [Field K] [AddCommGroup E] [Module K E] [Fintype K] [Finite E]
variable (ω : LinearMap.BilinForm K E)
end CommonCenterCounts
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
section ReducedCenterInjection
variable {K E : Type} [Field K] [AddCommGroup E] [Module K E] [FiniteDimensional K E]
variable (ω : LinearMap.BilinForm K E)
theorem certificate_proof_0317 (ha : ω.IsAlt) (hω : ω.Nondegenerate)
    {c h₀ h₁ h₂ r u : ℕ} (S : IsotropicDimspace ω c) (Y : CommonCenterSet ω S.val u) :
    ∃ f : FixedCommonCenterProfile ω c h₀ h₁ h₂ S Y.val r →
      SymplecticCenterProfile (symplecticReductionForm ω S.val ha)
        (generalReductionLagrangian ω ha hω S.val S.property.1 Y.val)
        (r-u) (h₀-c) (h₁-c) (h₂-c), Function.Injective f := by
  let F := FixedCommonCenterProfile ω c h₀ h₁ h₂ S Y.val r
  let Y' := generalReductionLagrangian ω ha hω S.val S.property.1 Y.val
  have heq (p : F) : (p.val.val.1.val ⊓ p.val.val.2.1.val) ⊓ p.val.val.2.2.val = S.val :=
    congrArg Subtype.val p.property.1
  have hL (p : F) : S.val ≤ p.val.val.1.val := (le_of_eq (heq p).symm).trans (inf_le_left.trans inf_le_left)
  have hM (p : F) : S.val ≤ p.val.val.2.1.val := (le_of_eq (heq p).symm).trans (inf_le_left.trans inf_le_right)
  have hN (p : F) : S.val ≤ p.val.val.2.2.val := (le_of_eq (heq p).symm).trans inf_le_right
  let L (p : F) := commonReductionLagrangian ω S.val ha S.property.1 p.val.val.1 (hL p)
  let M (p : F) := commonReductionLagrangian ω S.val ha S.property.1 p.val.val.2.1 (hM p)
  let N (p : F) := commonReductionLagrangian ω S.val ha S.property.1 p.val.val.2.2 (hN p)
  have hd (P : SymplecticLagrangian ω) (hSP : S.val ≤ P.val)
      (hPr : finrank K ↥(P.val ⊓ Y.val.val) = r) :
      finrank K ↥((commonReductionLagrangian ω S.val ha S.property.1 P hSP).val ⊓ Y'.val) = r-u := by
    have hh := reduce_center_intersection_finrank ω S.val P.val Y.val.val hSP
      (lagrangian_le_orthogonal ω S.val P.val P.property hSP)
    rw [Y.property,hPr] at hh
    change finrank K ↥(reduceSubspace ω S.val P.val ⊓ reduceSubspace ω S.val Y.val.val) = _
    omega
  let L' (p : F) : SymplecticCenterStratum (symplecticReductionForm ω S.val ha) Y' (r-u) :=
    ⟨L p,hd _ _ p.property.2.1⟩
  let M' (p : F) : SymplecticCenterStratum (symplecticReductionForm ω S.val ha) Y' (r-u) :=
    ⟨M p,hd _ _ p.property.2.2.1⟩
  let N' (p : F) : SymplecticCenterStratum (symplecticReductionForm ω S.val ha) Y' (r-u) :=
    ⟨N p,hd _ _ p.property.2.2.2⟩
  have hzero (p : F) : ((L p).val ⊓ (M p).val) ⊓ (N p).val = ⊥ := by
    change (reduceSubspace ω S.val p.val.val.1.val ⊓ reduceSubspace ω S.val p.val.val.2.1.val) ⊓
      reduceSubspace ω S.val p.val.val.2.2.val = ⊥
    rw [←reduceSubspace_inf ω S.val _ _ (hL p),←reduceSubspace_inf ω S.val _ _ (le_inf (hL p) (hM p)),heq p]
    exact reduceSubspace_self ω S.val
  have hp0 (p : F) : finrank K ↥((L p).val ⊓ (M p).val) = h₀-c := by
    change finrank K ↥(reduceSubspace ω S.val p.val.val.1.val ⊓ reduceSubspace ω S.val p.val.val.2.1.val) = _
    rw [reducePair_finrank ω S.val _ _ (hL p) (hM p),p.val.property.2.1,S.property.2]
  have hp1 (p : F) : finrank K ↥((L p).val ⊓ (N p).val) = h₁-c := by
    change finrank K ↥(reduceSubspace ω S.val p.val.val.1.val ⊓ reduceSubspace ω S.val p.val.val.2.2.val) = _
    rw [reducePair_finrank ω S.val _ _ (hL p) (hN p),p.val.property.2.2.1,S.property.2]
  have hp2 (p : F) : finrank K ↥((M p).val ⊓ (N p).val) = h₂-c := by
    change finrank K ↥(reduceSubspace ω S.val p.val.val.2.1.val ⊓ reduceSubspace ω S.val p.val.val.2.2.val) = _
    rw [reducePair_finrank ω S.val _ _ (hM p) (hN p),p.val.property.2.2.2,S.property.2]
  let f (p : F) : SymplecticCenterProfile (symplecticReductionForm ω S.val ha) Y'
      (r-u) (h₀-c) (h₁-c) (h₂-c) :=
    ⟨(L' p,M' p,N' p),hzero p,hp0 p,hp1 p,hp2 p⟩
  refine ⟨f,?_⟩
  intro p q hpq
  have heL : (L p).val = (L q).val := congrArg (fun r => r.val.1.val.val) hpq
  have heM : (M p).val = (M q).val := congrArg (fun r => r.val.2.1.val.val) hpq
  have heN : (N p).val = (N q).val := congrArg (fun r => r.val.2.2.val.val) hpq
  have hpL : p.val.val.1 = q.val.val.1 := congrArg Subtype.val
    (reduceLagrangian_injective ω S.val (a₁ := ⟨p.val.val.1,hL p⟩) (a₂ := ⟨q.val.val.1,hL q⟩) heL)
  have hpM : p.val.val.2.1 = q.val.val.2.1 := congrArg Subtype.val
    (reduceLagrangian_injective ω S.val (a₁ := ⟨p.val.val.2.1,hM p⟩) (a₂ := ⟨q.val.val.2.1,hM q⟩) heM)
  have hpN : p.val.val.2.2 = q.val.val.2.2 := congrArg Subtype.val
    (reduceLagrangian_injective ω S.val (a₁ := ⟨p.val.val.2.2,hN p⟩) (a₂ := ⟨q.val.val.2.2,hN q⟩) heN)
  exact Subtype.ext (Subtype.ext (Prod.ext hpL (Prod.ext hpM hpN)))

private instance certificate_instance_0317 : OAI.SidorenkoCounterexample.ProofCertificate_0317 := by
  constructor
  intro c0 c1 c2 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16
  exact @certificate_proof_0317 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16

end ReducedCenterInjection
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
open scoped BigOperators
theorem certificate_proof_0318 (d r s₀ s₁ s₂ : ℕ) (q : ℝ) (hq : 0 ≤ q) :
    0 ≤ reducedPlantedSum d r s₀ s₁ s₂ q := by
  unfold reducedPlantedSum
  apply Finset.sum_nonneg
  intro θ _
  unfold reducedPlantedConstant
  positivity

private instance certificate_instance_0318 : OAI.SidorenkoCounterexample.ProofCertificate_0318 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6
  exact @certificate_proof_0318 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 q0 q1 q2 q3 q4 q5 q6

section ReducedCardBound
variable {K E : Type} [Field K] [AddCommGroup E] [Module K E] [Fintype K] [Finite E]
variable (ω : LinearMap.BilinForm K E)
theorem certificate_proof_0319 (h2 : (2:K) ≠ 0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
    (D : ℕ) (hD : 2*D = finrank K E) (Y : SymplecticLagrangian ω)
    (r s₀ s₁ s₂ : ℕ) (hr : r ≤ D) :
    (Fintype.card K : ℝ)^(3*((r+1).choose 2)) *
      (Nat.card (SymplecticCenterProfile ω Y r s₀ s₁ s₂) : ℝ) ≤
      2^(3*D)*(Fintype.card K : ℝ)^(3*((D+1).choose 2))*
        reducedPlantedSum D r s₀ s₁ s₂ (Fintype.card K) := by
  have hd : finrank K Y.val = D := by
    have hh := self_orthogonal_twice_finrank ω Y.val hω Y.property
    omega
  have hp := symplectic_pair_card_bounds ω h2 ha hω D hD Y r hr
  have hq : (0:ℝ) < Fintype.card K := Nat.cast_pos.mpr Fintype.card_pos
  have hc : (0:ℝ) < Nat.card (SymplecticCenterStratum ω Y r) := by
    have hn : (0:ℝ) < (Fintype.card K : ℝ)^((r+1).choose 2) *
      Nat.card (SymplecticCenterStratum ω Y r) := (by positivity : (0:ℝ) <
        (Fintype.card K : ℝ)^((D+1).choose 2)).trans_le hp.1
    exact (mul_pos_iff_of_pos_left (pow_pos hq _)).mp hn
  have hb := symplectic_center_profile_probability_bound ω h2 ha hω Y r s₀ s₁ s₂ (by omega)
  rw [hd] at hb
  change (_ / _) ≤ reducedPlantedSum D r s₀ s₁ s₂ (Fintype.card K) at hb
  have hcount := (div_le_iff₀ (pow_pos hc 3)).mp hb
  have hpair : ((Fintype.card K : ℝ)^((r+1).choose 2) *
      Nat.card (SymplecticCenterStratum ω Y r))^3 ≤
      (2^D*(Fintype.card K : ℝ)^((D+1).choose 2))^3 := by
    exact pow_le_pow_left₀ (by positivity) hp.2 3
  calc
    _ ≤ (Fintype.card K : ℝ)^(3*((r+1).choose 2)) *
        (reducedPlantedSum D r s₀ s₁ s₂ (Fintype.card K)*
          (Nat.card (SymplecticCenterStratum ω Y r) : ℝ)^3) :=
      mul_le_mul_of_nonneg_left hcount (by positivity)
    _ = ((Fintype.card K : ℝ)^((r+1).choose 2) *
        Nat.card (SymplecticCenterStratum ω Y r))^3 *
        reducedPlantedSum D r s₀ s₁ s₂ (Fintype.card K) := by
      rw [mul_pow,←pow_mul,Nat.mul_comm 3]; ring
    _ ≤ (2^D*(Fintype.card K : ℝ)^((D+1).choose 2))^3 *
        reducedPlantedSum D r s₀ s₁ s₂ (Fintype.card K) :=
      mul_le_mul_of_nonneg_right hpair (reducedPlantedSum_nonneg _ _ _ _ _ _ (by positivity))
    _ = _ := by rw [mul_pow,←pow_mul,←pow_mul]; congr 2 <;> rw [Nat.mul_comm]

private instance certificate_instance_0319 : OAI.SidorenkoCounterexample.ProofCertificate_0319 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18
  exact @certificate_proof_0319 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18

theorem certificate_proof_0320 (h2 : (2:K) ≠ 0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
    (D : ℕ) (hD : 2*D = finrank K E) {c h₀ h₁ h₂ r u : ℕ}
    (S : IsotropicDimspace ω c) (Y : CommonCenterSet ω S.val u) (hr : r-u ≤ D-c) :
    (Fintype.card K : ℝ)^(3*((r-u+1).choose 2)) *
      (Nat.card (FixedCommonCenterProfile ω c h₀ h₁ h₂ S Y.val r) : ℝ) ≤
      2^(3*(D-c))*(Fintype.card K : ℝ)^(3*((D-c+1).choose 2))*
        reducedPlantedSum (D-c) (r-u) (h₀-c) (h₁-c) (h₂-c) (Fintype.card K) := by
  let := Module.finite_of_finite K (M := ReducedSpace ω S.val)
  have hc := isotropic_finrank_le_half ω hω D hD S.val S.property.1
  rw [S.property.2] at hc
  have hd := reducedSpace_finrank ω S.val hω S.property.1
  rw [S.property.2] at hd
  obtain ⟨f,hf⟩ := fixedCommonCenter_injection ω ha hω (h₀ := h₀) (h₁ := h₁) (h₂ := h₂) (r := r) S Y
  have hh := symplectic_center_profile_card_upper (symplecticReductionForm ω S.val ha) h2
    (symplecticReductionForm_alt ω S.val ha) (symplecticReductionForm_nondegenerate ω S.val ha hω)
    (D-c) (by omega) (generalReductionLagrangian ω ha hω S.val S.property.1 Y.val)
    (r-u) (h₀-c) (h₁-c) (h₂-c) hr
  exact (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (Nat.card_le_card_of_injective f hf)) (by positivity)).trans hh

private instance certificate_instance_0320 : OAI.SidorenkoCounterexample.ProofCertificate_0320 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19 q20 q21
  exact @certificate_proof_0320 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19 q20 q21

end ReducedCardBound
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
section FullCenterCoding
variable {K E : Type} [Field K] [AddCommGroup E] [Module K E] [Fintype K] [Finite E]
variable (ω : LinearMap.BilinForm K E)
noncomputable instance (D r c : ℕ) : Fintype (CommonParameters D r c) := Fintype.ofFinite _
theorem certificate_proof_0321 (ha : ω.IsAlt) (hω : ω.Nondegenerate)
    (D : ℕ) (hD : 2*D = finrank K E) (c h₀ h₁ h₂ r : ℕ) :
    ∃ f : ProfileCenterSet ω c h₀ h₁ h₂ r → PlantedCommonData ω D c h₀ h₁ h₂ r,
      Function.Injective f := by
  let F := ProfileCenterSet ω c h₀ h₁ h₂ r
  let S (p : F) := tripleProfileCommon ω p.1
  let u (p : F) := finrank K ↥((S p).val ⊓ p.2.val.val)
  have hS (p : F) : (S p).val ≤ p.1.val.1.val := inf_le_left.trans inf_le_left
  have hu (p : F) : u p ≤ c :=
    (Submodule.finrank_mono (inf_le_left : (S p).val ⊓ p.2.val.val ≤ (S p).val)).trans_eq (S p).property.2
  have hur (p : F) : u p ≤ r :=
    (Submodule.finrank_mono (inf_le_inf_right p.2.val.val (hS p))).trans_eq p.2.property.1
  have hdr (p : F) : r-u p ≤ D-c := by
    have hi := (S p).property.1
    have hc := isotropic_finrank_le_half ω hω D hD (S p).val hi
    have hd := reducedSpace_finrank ω (S p).val hω hi
    rw [(S p).property.2,hD.symm] at hd
    rw [(S p).property.2] at hc
    let Y' := generalReductionLagrangian ω ha hω (S p).val hi p.2.val
    let := Module.finite_of_finite K (M := ReducedSpace ω (S p).val)
    have hy := self_orthogonal_twice_finrank (symplecticReductionForm ω (S p).val ha) Y'.val
      (symplecticReductionForm_nondegenerate ω (S p).val ha hω) Y'.property
    have he := reduce_center_intersection_finrank ω (S p).val p.1.val.1.val p.2.val.val
      (hS p) (lagrangian_le_orthogonal ω (S p).val p.1.val.1.val p.1.val.1.property (hS p))
    rw [p.2.property.1] at he
    have hm := Submodule.finrank_mono (inf_le_right :
      reduceSubspace ω (S p).val p.1.val.1.val ⊓ Y'.val ≤ Y'.val)
    change finrank K ↥(reduceSubspace ω (S p).val p.1.val.1.val ⊓ Y'.val) + u p = r at he
    omega
  let f (p : F) : PlantedCommonData ω D c h₀ h₁ h₂ r :=
    ⟨S p,⟨⟨u p,by have := hu p; omega⟩,hur p,hdr p⟩,⟨p.2.val,rfl⟩,
      ⟨p.1,rfl,p.2.property⟩⟩
  refine ⟨f,?_⟩
  intro p q hpq
  have hprofile : p.1 = q.1 := congrArg (fun x : PlantedCommonData ω D c h₀ h₁ h₂ r => x.2.2.2.val) hpq
  have hcenter : p.2.val = q.2.val := congrArg (fun x : PlantedCommonData ω D c h₀ h₁ h₂ r => x.2.2.1.val) hpq
  cases p with
  | mk p Y =>
    cases q with
    | mk q Z =>
      dsimp only at hprofile hcenter
      subst q
      exact congrArg (Sigma.mk p) (Subtype.ext hcenter)

private instance certificate_instance_0321 : OAI.SidorenkoCounterexample.ProofCertificate_0321 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16
  exact @certificate_proof_0321 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16

end FullCenterCoding
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
open scoped BigOperators
theorem certificate_proof_0322 {q x C y : ℝ} (hq : 0 < q) (a b : ℕ)
    (h : q^a*x ≤ C*q^b*y) : x ≤ C*q^((b:ℝ)-a)*y := by
  apply le_of_mul_le_mul_left (a := q^a) ?_ (pow_pos hq _)
  refine h.trans_eq ?_
  rw [Real.rpow_sub hq,Real.rpow_natCast,Real.rpow_natCast]
  field_simp

private instance certificate_instance_0322 : OAI.SidorenkoCounterexample.ProofCertificate_0322 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7
  exact @certificate_proof_0322 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 q0 q1 q2 q3 q4 q5 q6 q7

section CommonCountSummation
variable {K E : Type} [Field K] [AddCommGroup E] [Module K E] [Fintype K] [Finite E]
variable (ω : LinearMap.BilinForm K E)
theorem certificate_proof_0323 (h2 : (2:K) ≠ 0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
    (D : ℕ) (hD : 2*D = finrank K E) {c h₀ h₁ h₂ r u : ℕ}
    (S : IsotropicDimspace ω c) (Y : CommonCenterSet ω S.val u) (hr : r-u ≤ D-c) :
    (Nat.card (FixedCommonCenterProfile ω c h₀ h₁ h₂ S Y.val r) : ℝ) ≤
      2^(3*(D-c))*(Fintype.card K : ℝ)^((3*((D-c+1).choose 2):ℕ)-(3*((r-u+1).choose 2):ℝ))*
        reducedPlantedSum (D-c) (r-u) (h₀-c) (h₁-c) (h₂-c) (Fintype.card K) :=
by
  simpa only [Nat.cast_mul,Nat.cast_ofNat] using
    unweight_count_bound (Nat.cast_pos.mpr Fintype.card_pos) _ _
      (fixedCommonCenter_card_upper ω h2 ha hω D hD (h₀ := h₀) (h₁ := h₁) (h₂ := h₂) S Y hr)

private instance certificate_instance_0323 : OAI.SidorenkoCounterexample.ProofCertificate_0323 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19 q20 q21
  exact @certificate_proof_0323 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19 q20 q21

theorem certificate_proof_0324 (h2 : (2:K) ≠ 0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
    (D : ℕ) (hD : 2*D = finrank K E) {c h₀ h₁ h₂ r : ℕ}
    (S : IsotropicDimspace ω c) (u : CommonParameters D r c) :
    (Nat.card (Σ Y : CommonCenterSet ω S.val u.val.val,
      FixedCommonCenterProfile ω c h₀ h₁ h₂ S Y.val r) : ℝ) ≤
      (2^u.val.val*lagrangianConstant (D-u.val.val))*2^(3*(D-c)) *
        (Fintype.card K : ℝ)^((u.val.val*(c-u.val.val)+(D-u.val.val+1).choose 2:ℕ)+
          (3*((D-c+1).choose 2):ℕ)-(3*((r-u.val.val+1).choose 2):ℝ))*
        reducedPlantedSum (D-c) (r-u.val.val) (h₀-c) (h₁-c) (h₂-c) (Fintype.card K) := by
  classical
  let := Fintype.ofFinite (CommonCenterSet ω S.val u.val.val)
  have hq : (0:ℝ) < Fintype.card K := Nat.cast_pos.mpr Fintype.card_pos
  let A : ℝ := 2^(3*(D-c))*(Fintype.card K : ℝ)^((3*((D-c+1).choose 2):ℕ)-(3*((r-u.val.val+1).choose 2):ℝ))*
        reducedPlantedSum (D-c) (r-u.val.val) (h₀-c) (h₁-c) (h₂-c) (Fintype.card K)
  have hA : 0 ≤ A := mul_nonneg (mul_nonneg (by positivity) (Real.rpow_nonneg hq.le _))
    (reducedPlantedSum_nonneg _ _ _ _ _ _ hq.le)
  have hu : u.val.val ≤ finrank K S.val := by rw [S.property.2]; exact Nat.le_of_lt_succ u.val.isLt
  have hc := commonCenter_card_upper ω h2 ha hω D hD S.val S.property.1 u.val.val hu
  rw [S.property.2] at hc
  calc
    _ = ∑ Y : CommonCenterSet ω S.val u.val.val,
        (Nat.card (FixedCommonCenterProfile ω c h₀ h₁ h₂ S Y.val r) : ℝ) := by rw [Nat.card_sigma,Nat.cast_sum]
    _ ≤ ∑ _Y : CommonCenterSet ω S.val u.val.val, A :=
      Finset.sum_le_sum (fun Y _ => fixedCommonCenter_card_rpow_upper ω h2 ha hω D hD S Y u.property.2)
    _ = (Nat.card (CommonCenterSet ω S.val u.val.val) : ℝ)*A := by simp [Nat.card_eq_fintype_card]
    _ ≤ (2^u.val.val*lagrangianConstant (D-u.val.val)*
        (Fintype.card K : ℝ)^(u.val.val*(c-u.val.val)+(D-u.val.val+1).choose 2))*A :=
      mul_le_mul_of_nonneg_right hc hA
    _ = _ := by
      let a := u.val.val*(c-u.val.val)+(D-u.val.val+1).choose 2
      let b := 3*((D-c+1).choose 2)
      let e : ℝ := 3*((r-u.val.val+1).choose 2:ℝ)
      change (_*(Fintype.card K : ℝ)^a)*A = _*(Fintype.card K : ℝ)^((a:ℝ)+b-e)*_
      rw [show (a:ℝ)+b-e = a+((b:ℝ)-e) by ring,Real.rpow_add hq,Real.rpow_natCast]
      dsimp [A,a,b,e]
      ring

private instance certificate_instance_0324 : OAI.SidorenkoCounterexample.ProofCertificate_0324 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19
  exact @certificate_proof_0324 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19

end CommonCountSummation
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
open scoped BigOperators
theorem certificate_proof_0325 (D c r h₀ h₁ h₂ : ℕ) (u : CommonParameters D r c) (q : ℝ)
    (hq : 0 ≤ q) : 0 ≤ commonPlantedTerm D c r h₀ h₁ h₂ u q := by
  unfold commonPlantedTerm
  exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by positivity)
    (lagrangianConstant_pos _).le) (by positivity)) (Real.rpow_nonneg hq _))
    (reducedPlantedSum_nonneg _ _ _ _ _ _ hq)

private instance certificate_instance_0325 : OAI.SidorenkoCounterexample.ProofCertificate_0325 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8
  exact @certificate_proof_0325 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 q0 q1 q2 q3 q4 q5 q6 q7 q8

section FullProfileCenterBound
variable {K E : Type} [Field K] [AddCommGroup E] [Module K E] [Fintype K] [Finite E]
variable (ω : LinearMap.BilinForm K E)
theorem certificate_proof_0326 (h2 : (2:K) ≠ 0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
    (D : ℕ) (hD : 2*D = finrank K E) (c h₀ h₁ h₂ r : ℕ) (hc : c ≤ D) :
    (Nat.card (ProfileCenterSet ω c h₀ h₁ h₂ r) : ℝ) ≤
      (lagrangianConstant D*2^c)*(Fintype.card K : ℝ)^(isotropicExponent D c) *
        ∑ u : CommonParameters D r c, commonPlantedTerm D c r h₀ h₁ h₂ u (Fintype.card K) := by
  classical
  let := Fintype.ofFinite (IsotropicDimspace ω c)
  obtain ⟨f,hf⟩ := profileCenter_injection ω ha hω D hD c h₀ h₁ h₂ r
  have hs (S : IsotropicDimspace ω c) :
      (Nat.card (Σ u : CommonParameters D r c, Σ Y : CommonCenterSet ω S.val u.val.val,
        FixedCommonCenterProfile ω c h₀ h₁ h₂ S Y.val r) : ℝ) ≤
      ∑ u : CommonParameters D r c, commonPlantedTerm D c r h₀ h₁ h₂ u (Fintype.card K) := by
    rw [Nat.card_sigma,Nat.cast_sum]
    exact Finset.sum_le_sum (fun u _ => commonData_fixed_card_upper ω h2 ha hω D hD S u)
  calc
    _ ≤ (Nat.card (PlantedCommonData ω D c h₀ h₁ h₂ r) : ℝ) :=
      Nat.cast_le.mpr (Nat.card_le_card_of_injective f hf)
    _ = ∑ S : IsotropicDimspace ω c,
        (Nat.card (Σ u : CommonParameters D r c, Σ Y : CommonCenterSet ω S.val u.val.val,
          FixedCommonCenterProfile ω c h₀ h₁ h₂ S Y.val r) : ℝ) := by rw [Nat.card_sigma,Nat.cast_sum]
    _ ≤ ∑ _S : IsotropicDimspace ω c,
        ∑ u : CommonParameters D r c, commonPlantedTerm D c r h₀ h₁ h₂ u (Fintype.card K) :=
      Finset.sum_le_sum (fun S _ => hs S)
    _ = (Nat.card (IsotropicDimspace ω c) : ℝ)*
        ∑ u : CommonParameters D r c, commonPlantedTerm D c r h₀ h₁ h₂ u (Fintype.card K) := by
      simp [Nat.card_eq_fintype_card]
    _ ≤ _ := mul_le_mul_of_nonneg_right (isotropic_card_bounds ω h2 ha hω D hD c hc).2
      (Finset.sum_nonneg (fun u _ => commonPlantedTerm_nonneg _ _ _ _ _ _ _ _ (by positivity)))

private instance certificate_instance_0326 : OAI.SidorenkoCounterexample.ProofCertificate_0326 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18
  exact @certificate_proof_0326 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18

end FullProfileCenterBound
end SidorenkoCounterexample
namespace SidorenkoCounterexample
theorem certificate_proof_0327 {p t s O Z T A L C B : ℝ}
    (hp : 0 < p) (hA : 0 < A) (hZ : 0 ≤ Z) (hT : 0 ≤ T) (_hO : 0 ≤ O)
    (hL : 0 ≤ L) (hC : 0 ≤ C) (_hB : 0 ≤ B) (hs : 0 ≤ s) (_ht : 0 ≤ t)
    (hOrbit : p^3 ≤ C*s*O) (hCenter : O*Z ≤ T)
    (hPair : p ≤ t*A) (hLag : L ≤ B*p) :
    Z*L^2/A^3 ≤ C*B^2*s*t^3*T/p^4 := by
  have hbar : p^3*Z ≤ C*s*T := by
    calc
      _ ≤ (C*s*O)*Z := mul_le_mul_of_nonneg_right hOrbit hZ
      _ = (C*s)*(O*Z) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hCenter (mul_nonneg hC hs)
  have hl : L^2 ≤ (B*p)^2 := pow_le_pow_left₀ hL hLag 2
  have htt : p^3 ≤ (t*A)^3 := pow_le_pow_left₀ hp.le hPair 3
  apply (div_le_div_iff₀ (pow_pos hA 3) (pow_pos hp 4)).mpr
  calc
    Z*L^2*p^4 ≤ Z*(B*p)^2*p^4 := by gcongr
    _ = (p^3*Z)*B^2*p^3 := by ring
    _ ≤ (C*s*T)*B^2*(t*A)^3 := by
      exact mul_le_mul (mul_le_mul_of_nonneg_right hbar (sq_nonneg B)) htt
        (by positivity) (by positivity)
    _ = _ := by ring

private instance certificate_instance_0327 : OAI.SidorenkoCounterexample.ProofCertificate_0327 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19 q20 q21 q22 q23
  exact @certificate_proof_0327 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19 q20 q21 q22 q23

open Module
section OrbitCenterProfile
variable {K E : Type} [Field K] [AddCommGroup E] [Module K E] [FiniteDimensional K E]
variable (ω : LinearMap.BilinForm K E)
omit [FiniteDimensional K E] in
theorem certificate_proof_0328 (L M N : SymplecticLagrangian ω)
    (P : OrderedTripleOrbit ω L.val M.val N.val) :
    ω.orthogonal P.val.1 = P.val.1 ∧ ω.orthogonal P.val.2.1 = P.val.2.1 ∧
    ω.orthogonal P.val.2.2 = P.val.2.2 ∧
    finrank K ↥((P.val.1 ⊓ P.val.2.1) ⊓ P.val.2.2) = finrank K ↥((L.val ⊓ M.val) ⊓ N.val) ∧
    finrank K ↥(P.val.1 ⊓ P.val.2.1) = finrank K ↥(L.val ⊓ M.val) ∧
    finrank K ↥(P.val.1 ⊓ P.val.2.2) = finrank K ↥(L.val ⊓ N.val) ∧
    finrank K ↥(P.val.2.1 ⊓ P.val.2.2) = finrank K ↥(M.val ⊓ N.val) := by
  obtain ⟨e,he,hL,hM,hN⟩ := P.property
  rw [←hL,←hM,←hN]
  refine ⟨(lagrangianIsometryEquiv ω e he L).property,
    (lagrangianIsometryEquiv ω e he M).property,
    (lagrangianIsometryEquiv ω e he N).property,?_,map_pair_finrank e _ _,map_pair_finrank e _ _,map_pair_finrank e _ _⟩
  rw [←Submodule.map_inf e.toLinearMap e.injective,←Submodule.map_inf e.toLinearMap e.injective,e.finrank_map_eq]

private instance certificate_instance_0328 : OAI.SidorenkoCounterexample.ProofCertificate_0328 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9
  exact @certificate_proof_0328 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9

omit [FiniteDimensional K E] in
theorem certificate_proof_0329 (L M N : SymplecticLagrangian ω) (r : ℕ) :
    ∃ f : (Σ P : OrderedTripleOrbit ω L.val M.val N.val,
      TripleCenterSet ω r P.val.1 P.val.2.1 P.val.2.2) →
      ProfileCenterSet ω (finrank K ↥((L.val ⊓ M.val) ⊓ N.val))
        (finrank K ↥(L.val ⊓ M.val)) (finrank K ↥(L.val ⊓ N.val)) (finrank K ↥(M.val ⊓ N.val)) r,
      Function.Injective f := by
  let F := Σ P : OrderedTripleOrbit ω L.val M.val N.val,
      TripleCenterSet ω r P.val.1 P.val.2.1 P.val.2.2
  let G := ProfileCenterSet ω (finrank K ↥((L.val ⊓ M.val) ⊓ N.val))
        (finrank K ↥(L.val ⊓ M.val)) (finrank K ↥(L.val ⊓ N.val)) (finrank K ↥(M.val ⊓ N.val)) r
  let f (p : F) : G :=
    let hp := orbit_member_profile ω L M N p.1
    ⟨⟨(⟨p.1.val.1,hp.1⟩,⟨p.1.val.2.1,hp.2.1⟩,⟨p.1.val.2.2,hp.2.2.1⟩),hp.2.2.2⟩,p.2⟩
  refine ⟨f,?_⟩
  intro p q h
  have he : p.1 = q.1 := Subtype.ext (congrArg (fun s : G => (s.1.val.1.val,s.1.val.2.1.val,s.1.val.2.2.val)) h)
  have hy : p.2.val = q.2.val := congrArg (fun s : G => s.2.val) h
  cases p with
  | mk p Y =>
    cases q with
    | mk q Z =>
      dsimp only at he hy
      subst q
      exact congrArg (Sigma.mk p) (Subtype.ext hy)

private instance certificate_instance_0329 : OAI.SidorenkoCounterexample.ProofCertificate_0329 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9
  exact @certificate_proof_0329 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9

omit [FiniteDimensional K E] in
theorem certificate_proof_0330 [Finite E] (L M N : SymplecticLagrangian ω) (r : ℕ) :
    Nat.card (OrderedTripleOrbit ω L.val M.val N.val) * Nat.card (TripleCenterSet ω r L.val M.val N.val) ≤
      Nat.card (ProfileCenterSet ω (finrank K ↥((L.val ⊓ M.val) ⊓ N.val))
        (finrank K ↥(L.val ⊓ M.val)) (finrank K ↥(L.val ⊓ N.val)) (finrank K ↥(M.val ⊓ N.val)) r) := by
  rw [←tripleCenterOrbit_card]
  obtain ⟨f,hf⟩ := orbitCenter_profile_injection ω L M N r
  exact Nat.card_le_card_of_injective f hf

private instance certificate_instance_0330 : OAI.SidorenkoCounterexample.ProofCertificate_0330 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10
  exact @certificate_proof_0330 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10

end OrbitCenterProfile
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
open scoped BigOperators
section PointwisePlanted
variable {K E : Type} [Field K] [AddCommGroup E] [Module K E] [Fintype K] [Finite E]
variable (ω : LinearMap.BilinForm K E)
omit [Fintype K] [Finite E] in
theorem certificate_proof_0331 (r : ℕ) (A L M N : SymplecticLagrangian ω) :
    0 ≤ tripleFaceDensity ω r A L M N := by unfold tripleFaceDensity; positivity

private instance certificate_instance_0331 : OAI.SidorenkoCounterexample.ProofCertificate_0331 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10
  exact @certificate_proof_0331 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10

theorem certificate_proof_0332 (h2 : (2:K) ≠ 0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
    (D : ℕ) (hD : 2*D = finrank K E) (A : SymplecticLagrangian ω) (r : ℕ) (hr : r ≤ D) :
    (0:ℝ) < Nat.card (SymplecticCenterStratum ω A r) := by
  have hp := (symplectic_pair_card_bounds ω h2 ha hω D hD A r hr).1
  have hq : (0:ℝ) < Fintype.card K := Nat.cast_pos.mpr Fintype.card_pos
  have hn : (0:ℝ) < (Fintype.card K : ℝ)^((r+1).choose 2) *
      Nat.card (SymplecticCenterStratum ω A r) := (by positivity : (0:ℝ) <
        (Fintype.card K : ℝ)^((D+1).choose 2)).trans_le hp
  exact (mul_pos_iff_of_pos_left (pow_pos hq _)).mp hn

private instance certificate_instance_0332 : OAI.SidorenkoCounterexample.ProofCertificate_0332 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15
  exact @certificate_proof_0332 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15

theorem certificate_proof_0333 [Invertible (2:K)]
    (h2 : (2:K) ≠ 0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
    (D : ℕ) (hD : 2*D = finrank K E) (hq : 4*lagrangianConstant D ≤ (Fintype.card K : ℝ))
    (r : ℕ) (hr : r ≤ D) (A L M N : SymplecticLagrangian ω) :
    tripleFaceDensity ω r A L M N ≤
      (orbitMassConstant D*(lagrangianConstant D)^2) *
        (Fintype.card K : ℝ)^((tripleDefect D L.val M.val N.val : ℝ)+
          (3*((r+1).choose 2):ℕ)-(4*((D+1).choose 2):ℕ)) *
        (Nat.card (ProfileCenterSet ω (finrank K ↥((L.val ⊓ M.val) ⊓ N.val))
          (finrank K ↥(L.val ⊓ M.val)) (finrank K ↥(L.val ⊓ N.val)) (finrank K ↥(M.val ⊓ N.val)) r) : ℝ) := by
  let q : ℝ := Fintype.card K
  have hq0 : 0 < q := Nat.cast_pos.mpr Fintype.card_pos
  have hOrbit := tripleOrbit_card_lower ω ha hω D hD hq L M N
  have hCenter := orbit_center_count_le_profile ω L M N r
  have hPair := (symplectic_pair_card_bounds ω h2 ha hω D hD A r hr).1
  have hLag := (symplecticLagrangian_card_bounds ω h2 ha hω D hD).2
  have hi := normalized_count_ratio_bound
    (p := q^((D+1).choose 2)) (t := q^((r+1).choose 2))
    (s := q^(tripleDefect D L.val M.val N.val))
    (O := Nat.card (OrderedTripleOrbit ω L.val M.val N.val))
    (Z := Nat.card (TripleCenterSet ω r L.val M.val N.val))
    (T := Nat.card (ProfileCenterSet ω (finrank K ↥((L.val ⊓ M.val) ⊓ N.val))
      (finrank K ↥(L.val ⊓ M.val)) (finrank K ↥(L.val ⊓ N.val)) (finrank K ↥(M.val ⊓ N.val)) r))
    (A := Nat.card (SymplecticCenterStratum ω A r)) (L := Nat.card (SymplecticLagrangian ω))
    (C := orbitMassConstant D) (B := lagrangianConstant D)
    (pow_pos hq0 _) (symplectic_center_stratum_card_pos ω h2 ha hω D hD A r hr)
    (by positivity) (by positivity) (by positivity) (by positivity)
    (orbitMassConstant_pos D).le (lagrangianConstant_pos D).le (by positivity) (by positivity)
    (by simpa only [←pow_mul,Nat.mul_comm] using hOrbit)
    (by exact_mod_cast hCenter) hPair hLag
  refine hi.trans_eq ?_
  change _ = _*q^((tripleDefect D L.val M.val N.val : ℝ)+(3*((r+1).choose 2):ℕ)-(4*((D+1).choose 2):ℕ))*_
  rw [Real.rpow_sub hq0,Real.rpow_add hq0,Real.rpow_natCast,Real.rpow_natCast,Real.rpow_natCast]
  simp only [pow_mul,pow_succ]
  ring

private instance certificate_instance_0333 : OAI.SidorenkoCounterexample.ProofCertificate_0333 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19 q20
  exact @certificate_proof_0333 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19 q20

theorem certificate_proof_0334 [Invertible (2:K)]
    (h2 : (2:K) ≠ 0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
    (D : ℕ) (hD : 2*D = finrank K E) (hq : 4*lagrangianConstant D ≤ (Fintype.card K : ℝ))
    (r : ℕ) (hr : r ≤ D) (A L M N : SymplecticLagrangian ω) :
    let c := finrank K ↥((L.val ⊓ M.val) ⊓ N.val)
    let h₀ := finrank K ↥(L.val ⊓ M.val)
    let h₁ := finrank K ↥(L.val ⊓ N.val)
    let h₂ := finrank K ↥(M.val ⊓ N.val)
    tripleFaceDensity ω r A L M N ≤
      (orbitMassConstant D*(lagrangianConstant D)^2) *
        (Fintype.card K : ℝ)^((tripleDefect D L.val M.val N.val : ℝ)+
          (3*((r+1).choose 2):ℕ)-(4*((D+1).choose 2):ℕ)) *
        ((lagrangianConstant D*2^c)*(Fintype.card K : ℝ)^(isotropicExponent D c) *
          ∑ u : CommonParameters D r c, commonPlantedTerm D c r h₀ h₁ h₂ u (Fintype.card K)) := by
  dsimp only
  have hc : finrank K ↥((L.val ⊓ M.val) ⊓ N.val) ≤ D :=
    isotropic_finrank_le_half ω hω D hD _ (by intro x hx y hy; exact L.property.ge hx.1.1 y hy.1.1)
  have hh := profileCenter_card_upper ω h2 ha hω D hD
    (finrank K ↥((L.val ⊓ M.val) ⊓ N.val))
    (finrank K ↥(L.val ⊓ M.val)) (finrank K ↥(L.val ⊓ N.val)) (finrank K ↥(M.val ⊓ N.val)) r hc
  have hq0 : (0:ℝ) ≤ Fintype.card K := by positivity
  exact (tripleFaceDensity_profile_bound ω h2 ha hω D hD hq r hr A L M N).trans
    (mul_le_mul_of_nonneg_left hh (mul_nonneg (mul_nonneg (orbitMassConstant_pos D).le (sq_nonneg _))
      (Real.rpow_nonneg hq0 _)))

private instance certificate_instance_0334 : OAI.SidorenkoCounterexample.ProofCertificate_0334 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19 q20
  exact @certificate_proof_0334 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19 q20

end PointwisePlanted
end SidorenkoCounterexample
end OAI
namespace OAI
namespace SidorenkoCounterexample
theorem certificate_proof_0335 (A B C x b : ℝ)
    (hA : 0 ≤ A) (hxb : x ≤ b) (hderiv : 2 * A * b + B ≤ 0) :
    A * b ^ 2 + B * b + C ≤ A * x ^ 2 + B * x + C := by
  have h : 0 ≤ -A * (x + b) - B := by
    nlinarith [mul_nonneg hA (sub_nonneg.mpr hxb)]
  have := mul_nonneg (sub_nonneg.mpr hxb) h
  nlinarith

private instance certificate_instance_0335 : OAI.SidorenkoCounterexample.ProofCertificate_0335 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7
  exact @certificate_proof_0335 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 q0 q1 q2 q3 q4 q5 q6 q7

theorem certificate_proof_0336 (A B C a b x k : ℝ)
    (hA : A ≤ 0) (hax : a ≤ x) (hxb : x ≤ b)
    (ha : k ≤ A * a ^ 2 + B * a + C)
    (hb : k ≤ A * b ^ 2 + B * b + C) :
    k ≤ A * x ^ 2 + B * x + C := by
  by_cases hab : a = b
  · have : x = a := by linarith
    simpa [this] using ha
  have hab' : 0 < b - a := sub_pos.mpr (lt_of_le_of_ne (hax.trans hxb) hab)
  have h₁ := mul_nonneg (sub_nonneg.mpr hxb) (sub_nonneg.mpr ha)
  have h₂ := mul_nonneg (sub_nonneg.mpr hax) (sub_nonneg.mpr hb)
  have h₃ := mul_nonneg (mul_nonneg (neg_nonneg.mpr hA)
    (mul_nonneg (sub_nonneg.mpr hax) (sub_nonneg.mpr hxb)))
    (le_of_lt hab')
  have hsum : 0 ≤ (b - a) * (A * x ^ 2 + B * x + C - k) := by
    nlinarith only [h₁, h₂, h₃]
  exact le_of_sub_nonneg ((nonneg_of_mul_nonneg_right hsum hab'))

private instance certificate_instance_0336 : OAI.SidorenkoCounterexample.ProofCertificate_0336 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11
  exact @certificate_proof_0336 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11

theorem certificate_proof_0337 (P T δ : ℝ) (hP : 0 ≤ P) (hδ : 0 ≤ δ)
    (_hT : 0 ≤ T) (hTP : T ≤ P + 3 * δ) :
    (P ^ 2 + δ ^ 2) / 18 ≤
      3 * δ ^ 2 / 4 + (2 * P - T) ^ 2 / 18 + (5 * P - T) * δ / 6 -
        (min (P / 3 + δ) ((P - T + 3 * δ) / 2)) ^ 2 / 2 := by
  have hPd := mul_nonneg hP hδ
  by_cases ht : T ≤ P / 3 + δ
  · rw [min_eq_left (by linarith)]
    have hmono := quadratic_ge_right (1/18) (-2*P/9-δ/6)
      (3*δ^2/4+2*P^2/9+5*P*δ/6-(P/3+δ)^2/2)
      T (P/3+δ) (by norm_num) ht (by nlinarith)
    nlinarith [sq_nonneg P, sq_nonneg δ]
  · rw [min_eq_right (by linarith)]
    have hl : P / 3 + δ ≤ T := by linarith
    have hem := quadratic_ge_endpoints (-5/72) (P/36+7*δ/12)
      (7*P^2/72+P*δ/12-3*δ^2/8) (P/3+δ) (P+3*δ) T
      ((P^2+δ^2)/18) (by norm_num) hl hTP
      (by nlinarith [sq_nonneg P, sq_nonneg δ])
      (by nlinarith [sq_nonneg P, sq_nonneg δ])
    nlinarith only [hem]

private instance certificate_instance_0337 : OAI.SidorenkoCounterexample.ProofCertificate_0337 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6
  exact @certificate_proof_0337 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 q0 q1 q2 q3 q4 q5 q6

theorem certificate_proof_0338 (x T y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (_hT : 0 ≤ T) (hTx : T ≤ x) :
    (x ^ 2 + y ^ 2) / 18 ≤
      y ^ 2 / 4 + (2*x-T)*y/3 + (2*x-T)^2/18 -
        (min (x/3) ((x-T)/2))^2/2 := by
  have hxy := mul_nonneg hx hy
  by_cases ht : T ≤ x/3
  · rw [min_eq_left (by linarith)]
    have hmono := quadratic_ge_right (1/18) (-2*x/9-y/3)
      (y^2/4+2*x*y/3+x^2/6) T (x/3) (by norm_num) ht (by nlinarith)
    nlinarith [sq_nonneg x, sq_nonneg y]
  · rw [min_eq_right (by linarith)]
    have hem := quadratic_ge_endpoints (-5/72) (x/36-y/3)
      (y^2/4+2*x*y/3+7*x^2/72) (x/3) x T ((x^2+y^2)/18)
      (by norm_num) (by linarith) hTx
      (by nlinarith [sq_nonneg x, sq_nonneg y])
      (by nlinarith [sq_nonneg x, sq_nonneg y])
    nlinarith only [hem]

private instance certificate_instance_0338 : OAI.SidorenkoCounterexample.ProofCertificate_0338 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6
  exact @certificate_proof_0338 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 q0 q1 q2 q3 q4 q5 q6

theorem certificate_proof_0339 (c d P T δ : ℝ) (hc : |δ| ≤ c)
    (hd : P + T ≤ d) (hP : 0 ≤ P) (hT : 0 ≤ T) (hTP : T ≤ P+3*δ) :
    (P^2+T^2+δ^2)/342 + (c-|δ|)*(d+3*δ)/12 ≤ scalarForm c d P T δ := by
  have hsplit : scalarForm |δ| d P T δ + (c-|δ|)*(d+3*δ)/12 ≤
      scalarForm c d P T δ := by
    have hm := mul_nonneg (sub_nonneg.mpr hc) (sub_nonneg.mpr hd)
    dsimp [scalarForm]
    nlinarith only [hm]
  suffices h : (P^2+T^2+δ^2)/342 ≤ scalarForm |δ| d P T δ by linarith only [h, hsplit]
  by_cases hδ : 0 ≤ δ
  · rw [abs_of_nonneg hδ]
    have hs := coercivity_scalar_pos P T δ hP hδ hT hTP
    have hsquare := mul_nonneg (sub_nonneg.mpr hTP) (show 0 ≤ P+3*δ+T by linarith)
    have hsize : P^2+T^2+δ^2 ≤ 19*(P^2+δ^2) := by
      nlinarith only [hsquare, sq_nonneg (P-3*δ), sq_nonneg P]
    dsimp [scalarForm]
    nlinarith only [hs, hsize]
  · have hδ' : δ ≤ 0 := le_of_not_ge hδ
    rw [abs_of_nonpos hδ']
    have hx : 0 ≤ P+3*δ := by linarith
    have hs := coercivity_scalar_neg (P+3*δ) T (-δ) hx (neg_nonneg.mpr hδ') hT hTP
    rw [show (P+3*δ)/3 = P/3+δ by ring,
      show (P+3*δ-T)/2 = (P-T+3*δ)/2 by ring] at hs
    have hsquare := mul_nonneg (sub_nonneg.mpr hTP) (show 0 ≤ P+3*δ+T by linarith)
    have hsize : P^2+T^2+δ^2 ≤ 19*((P+3*δ)^2+δ^2) := by
      nlinarith only [hsquare, sq_nonneg (P+6*δ), sq_nonneg (P+3*δ)]
    have hdim := mul_nonneg (neg_nonneg.mpr hδ') (sub_nonneg.mpr hd)
    dsimp [scalarForm]
    nlinarith only [hs, hsize, hdim]

private instance certificate_instance_0339 : OAI.SidorenkoCounterexample.ProofCertificate_0339 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9
  exact @certificate_proof_0339 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9

open scoped BigOperators
theorem certificate_proof_0340 (z : Fin 3 → ℝ) : (∑ i, z i)^2 ≤ 3*∑ i, (z i)^2 := by
  simp only [Fin.sum_univ_three]
  nlinarith [sq_nonneg (z 0-z 1), sq_nonneg (z 0-z 2), sq_nonneg (z 1-z 2)]

private instance certificate_instance_0340 : OAI.SidorenkoCounterexample.ProofCertificate_0340 := by
  constructor
  intro q0
  exact @certificate_proof_0340 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 q0

end SidorenkoCounterexample
namespace SidorenkoCounterexample
open scoped BigOperators
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open scoped BigOperators
end SidorenkoCounterexample
namespace SidorenkoCounterexample
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open scoped BigOperators
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open scoped BigOperators
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open scoped BigOperators
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open scoped BigOperators
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open scoped BigOperators
end SidorenkoCounterexample
end OAI

theorem solution : OAI.SidorenkoCounterexample.ProofCertificate_0317 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0318 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0319 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0320 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0321 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0322 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0323 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0324 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0325 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0326 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0327 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0328 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0329 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0330 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0331 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0332 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0333 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0334 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0335 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0336 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0337 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0338 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0339 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0340 := by
  exact ⟨inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance⟩
end

