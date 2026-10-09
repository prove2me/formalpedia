-- Prove2me | solution 1 for OAI.SidorenkoCounterexample.finite_geometry_batch_21
-- status  : ACCEPTED   (prove)
-- author  : @abcdefg
-- created : 2026-10-09T06:21:36.390986+00:00
-- url     : https://prove2.me/submissions/b20f9de9-d06a-4f26-8fb7-d1c7f208582e

import Definitions.Def_SidorenkoCertificateBundleA
set_option linter.unusedVariables false
section
variable [p0 : OAI.SidorenkoCounterexample.ProofCertificate_0030]
  [p1 : OAI.SidorenkoCounterexample.ProofCertificate_0207]
  [p2 : OAI.SidorenkoCounterexample.ProofCertificate_0214]
  [p3 : OAI.SidorenkoCounterexample.ProofCertificate_0298]
  [p4 : OAI.SidorenkoCounterexample.ProofCertificate_0332]
  [p5 : OAI.SidorenkoCounterexample.ProofCertificate_0349]
  [p6 : OAI.SidorenkoCounterexample.ProofCertificate_0350]
  [p7 : OAI.SidorenkoCounterexample.ProofCertificate_0371]
  [p8 : OAI.SidorenkoCounterexample.ProofCertificate_0372]
  [p9 : OAI.SidorenkoCounterexample.ProofCertificate_0410]
  [p10 : OAI.SidorenkoCounterexample.ProofCertificate_0432]
  [p11 : OAI.SidorenkoCounterexample.ProofCertificate_0478]
  [p12 : OAI.SidorenkoCounterexample.ProofCertificate_0537]
  [p13 : OAI.SidorenkoCounterexample.ProofCertificate_0542]
  [p14 : OAI.SidorenkoCounterexample.ProofCertificate_0548]
  [p15 : OAI.SidorenkoCounterexample.ProofCertificate_0552]
  [p16 : OAI.SidorenkoCounterexample.ProofCertificate_0557]
  [p17 : OAI.SidorenkoCounterexample.ProofCertificate_0559]
  [p18 : OAI.SidorenkoCounterexample.ProofCertificate_0562]
  [p19 : OAI.SidorenkoCounterexample.ProofCertificate_0563]
  [p20 : OAI.SidorenkoCounterexample.ProofCertificate_0565]
  [p21 : OAI.SidorenkoCounterexample.ProofCertificate_0566]
  [p22 : OAI.SidorenkoCounterexample.ProofCertificate_0568]
  [p23 : OAI.SidorenkoCounterexample.ProofCertificate_0569]
  [p24 : OAI.SidorenkoCounterexample.ProofCertificate_0570]
  [p25 : OAI.SidorenkoCounterexample.ProofCertificate_0571]
include p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25

namespace OAI
namespace SidorenkoCounterexample
open Module
open scoped BigOperators
section PairBound
variable {K E : Type} [Field K] [AddCommGroup E] [Module K E] [Fintype K] [Finite E]
variable (ω : LinearMap.BilinForm K E)
end PairBound
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
theorem certificate_proof_0572 (D : ℕ) (h : Fin 33 → ℕ) : 0≤residualDirectConstant D h := by
  exact mul_nonneg (pow_nonneg (by norm_num) _) (pow_nonneg (lagrangianConstant_pos D).le _)

private instance certificate_instance_0572 : OAI.SidorenkoCounterexample.ProofCertificate_0572 := by
  constructor
  intro q0 q1
  exact @certificate_proof_0572 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 q0 q1

theorem certificate_proof_0573 (D : ℕ) : 0≤residualNondirectConstant D := by
  exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg (by norm_num) _))
    (pow_nonneg (by norm_num) _)) (pow_nonneg (lagrangianConstant_pos D).le _)

private instance certificate_instance_0573 : OAI.SidorenkoCounterexample.ProofCertificate_0573 := by
  constructor
  intro q0
  exact @certificate_proof_0573 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 q0

section Actual
variable {K E : Type} [Field K] [AddCommGroup E] [Module K E] [Fintype K] [Finite E]
variable (ω : LinearMap.BilinForm K E)
omit [Fintype K] in
theorem certificate_proof_0574 (h : Fin 33 → ℕ) :
    Nat.card (PairDimProfile ω h)=Nat.card (DirectPairProfile ω h)+Nat.card (NonDirectPairProfile ω h) := by
  classical
  exact (Nat.card_congr (Equiv.sumCompl (fun L : PairDimProfile ω h=>iSupIndep (pairSpaces ω L.val)))).symm.trans Nat.card_sum

private instance certificate_instance_0574 : OAI.SidorenkoCounterexample.ProofCertificate_0574 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7
  exact @certificate_proof_0574 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 q0 q1 q2 q3 q4 q5 q6 q7

theorem certificate_proof_0575 (h2 : (2:K)≠0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
    (D : ℕ) (hD : 2*D=finrank K E) (h : Fin 33 → ℕ) (hh : ∀ e,h e=0 ∨ h e=2) (hlarge : 33≤D) :
    (Nat.card (PairDimProfile ω h):ℝ)≤(Nat.card (SymplecticLagrangian ω):ℝ)^13*
      (residualDirectConstant D h*(Fintype.card K:ℝ)^(-(∑ e,triangular (h e)))+
        residualNondirectConstant D*(Fintype.card K:ℝ)^(-(D:ℝ)+1575)) := by
  rw [pairDimProfile_card_split,Nat.cast_add]
  have hd := directPairProfile_card_bound ω h2 ha hω D hD h
    ((residual_h_sum_le h hh).trans (by omega))
  have hn := nondirectPairProfile_card_bound ω h2 ha hω D hD h hh
  exact (add_le_add hd hn).trans_eq (by unfold residualDirectConstant residualNondirectConstant;ring)

private instance certificate_instance_0575 : OAI.SidorenkoCounterexample.ProofCertificate_0575 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15
  exact @certificate_proof_0575 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15

omit [Fintype K] in
theorem certificate_proof_0576 (c : Fin 22 → ℕ) (h : Fin 33 → ℕ) :
    Nat.card {L : Fin 13 → SymplecticLagrangian ω // PointProfile ω c h L}≤Nat.card (PairDimProfile ω h) := by
  let f : {L : Fin 13 → SymplecticLagrangian ω // PointProfile ω c h L} → PairDimProfile ω h :=
    fun L=>⟨L.val,L.property.2⟩
  exact Nat.card_le_card_of_injective f (fun x y hxy=>Subtype.ext (congrArg (fun L : PairDimProfile ω h=>L.val) hxy))

private instance certificate_instance_0576 : OAI.SidorenkoCounterexample.ProofCertificate_0576 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8
  exact @certificate_proof_0576 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 q0 q1 q2 q3 q4 q5 q6 q7 q8

omit [Fintype K] [Finite E] in
theorem certificate_proof_0577 (c : Fin 22 → ℕ) (h : Fin 33 → ℕ) :
    0≤normalizedPointProfileCount ω c h := by unfold normalizedPointProfileCount; positivity

private instance certificate_instance_0577 : OAI.SidorenkoCounterexample.ProofCertificate_0577 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7
  exact @certificate_proof_0577 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 q0 q1 q2 q3 q4 q5 q6 q7

theorem certificate_proof_0578 (h2 : (2:K)≠0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
    (D : ℕ) (hD : 2*D=finrank K E) : (0:ℝ)<Nat.card (SymplecticLagrangian ω) := by
  have hq : (0:ℝ)<Fintype.card K := by exact_mod_cast Fintype.card_pos (α:=K)
  exact (pow_pos hq _).trans_le (symplecticLagrangian_card_bounds ω h2 ha hω D hD).1

private instance certificate_instance_0578 : OAI.SidorenkoCounterexample.ProofCertificate_0578 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12
  exact @certificate_proof_0578 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12

theorem certificate_proof_0579 (h2 : (2:K)≠0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
    (D : ℕ) (hD : 2*D=finrank K E) (c : Fin 22 → ℕ) (h : Fin 33 → ℕ) (hc : ∀ j,c j≤D) :
    normalizedPointProfileCount ω c h≤(fullProfileConstant D)^11*(Fintype.card K:ℝ)^(-profileCost D c h) := by
  apply (div_le_iff₀ (pow_pos (lagrangianRealCard_pos ω h2 ha hω D hD) 13)).mpr
  exact (pointProfile_card_bound ω h2 ha hω D hD c h hc).trans_eq (by ring)

private instance certificate_instance_0579 : OAI.SidorenkoCounterexample.ProofCertificate_0579 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15
  exact @certificate_proof_0579 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15

theorem certificate_proof_0580 (h2 : (2:K)≠0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
    (D : ℕ) (hD : 2*D=finrank K E) (c : Fin 22 → ℕ) (h : Fin 33 → ℕ)
    (hh : ∀ e,h e=0 ∨ h e=2) (hlarge : 33≤D) :
    normalizedPointProfileCount ω c h≤
      residualDirectConstant D h*(Fintype.card K:ℝ)^(-(∑ e,triangular (h e)))+
        residualNondirectConstant D*(Fintype.card K:ℝ)^(-(D:ℝ)+1575) := by
  apply (div_le_iff₀ (pow_pos (lagrangianRealCard_pos ω h2 ha hω D hD) 13)).mpr
  have hi : (Nat.card {L : Fin 13 → SymplecticLagrangian ω // PointProfile ω c h L}:ℝ)≤Nat.card (PairDimProfile ω h) :=
    by exact_mod_cast pointProfile_card_le_pair ω c h
  exact (hi.trans (pairDimProfile_residual_card_bound ω h2 ha hω D hD h hh hlarge)).trans_eq (mul_comm _ _)

private instance certificate_instance_0580 : OAI.SidorenkoCounterexample.ProofCertificate_0580 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16
  exact @certificate_proof_0580 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16

end Actual
theorem certificate_proof_0581 (h : Fin 33 → ℕ) (hh : ∀ e,h e=0 ∨ h e=2) :
    (∑ e,triangular (h e))≤99 := by
  calc _ ≤ ∑ _e : Fin 33,(3:ℝ) := by
         apply Finset.sum_le_sum
         intro e _
         rcases hh e with he|he <;> norm_num [he,triangular]
       _ = _ := by norm_num

private instance certificate_instance_0581 : OAI.SidorenkoCounterexample.ProofCertificate_0581 := by
  constructor
  intro q0 q1
  exact @certificate_proof_0581 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 q0 q1

theorem certificate_proof_0582 (h : Fin 33 → ℕ) (hs : ∃ e,h e≠0) :
    0<(∑ e,triangular (h e)) := by
  obtain ⟨e,he⟩ := hs
  exact (triangular_pos (by exact_mod_cast Nat.pos_of_ne_zero he)).trans_le
    (Finset.single_le_sum (fun f _=>triangular_nonneg (Nat.cast_nonneg _)) (Finset.mem_univ e))

private instance certificate_instance_0582 : OAI.SidorenkoCounterexample.ProofCertificate_0582 := by
  constructor
  intro q0 q1
  exact @certificate_proof_0582 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 q0 q1

theorem certificate_proof_0583 : ∃ D₀ : ℕ, 1642≤D₀ ∧ ∀ D≥D₀,
    ∀ (r : ℕ), D=2*r → ∀ (c : Fin 22 → ℕ) (h : Fin 33 → ℕ), GeometricProfile D c h →
    ∀ (full : Fin 22 → Bool) (x : GlobalTailChoice D r c h full),
    0<profileCost D c h-globalTailGain D r c h full x ∨
      ((∀ j,c j=0) ∧ (∀ e,h e=0 ∨ h e=2) ∧
        globalTailGain D r c h full x=(2/3:ℝ)*∑ e,triangular (h e)) := by
  obtain ⟨D₀,hD₀⟩ := uniform_tail_dichotomy
  refine ⟨max 1642 D₀,le_max_left _ _,?_⟩
  intro D hD r hr c h hp full x
  by_cases hs : 0<profileCost D c h-globalTailGain D r c h full x
  · exact Or.inl hs
  · right
    have hi := hD₀ D ((le_max_right _ _).trans hD) full (globalTailTuple D r c h full x) h
      (globalTailTuple_feasible D r hr c h hp full x)
      (by rw [←globalTailGain_cost D r c h hp full x]; exact le_of_not_gt hs)
    exact ⟨by simpa only [globalTailTuple,faceTailTuple_c] using hi.1,hi.2.1,hi.2.2.2.2⟩

private instance certificate_instance_0583 : OAI.SidorenkoCounterexample.ProofCertificate_0583 := by
  constructor
  exact @certificate_proof_0583 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25

end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
open scoped BigOperators
theorem certificate_proof_0584 (D r : ℕ) (c : Fin 22 → ℕ) (h : Fin 33 → ℕ)
    (full : Fin 22 → Bool) (x : GlobalTailChoice D r c h full) (q : ℝ) (hq : 0≤q) :
    0≤profileTermMajorant D r c h full x q := by
  unfold profileTermMajorant
  split
  · exact mul_nonneg (pow_nonneg (fullProfileConstant_pos D).le _) (Real.rpow_nonneg hq _)
  · exact add_nonneg (mul_nonneg (residualDirectConstant_nonneg D h) (Real.rpow_nonneg hq _))
      (mul_nonneg (residualNondirectConstant_nonneg D) (Real.rpow_nonneg hq _))

private instance certificate_instance_0584 : OAI.SidorenkoCounterexample.ProofCertificate_0584 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7
  exact @certificate_proof_0584 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 q0 q1 q2 q3 q4 q5 q6 q7

theorem certificate_proof_0585 (e : ℝ) (he : e<0) :
    Filter.Tendsto (fun q : ℝ=>q^e) Filter.atTop (nhds 0) := by
  simpa only [neg_neg] using tendsto_rpow_neg_atTop (neg_pos.mpr he)

private instance certificate_instance_0585 : OAI.SidorenkoCounterexample.ProofCertificate_0585 := by
  constructor
  intro q0 q1
  exact @certificate_proof_0585 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 q0 q1

theorem certificate_proof_0586 (D r : ℕ) (c : Fin 22 → ℕ) (h : Fin 33 → ℕ)
    (full : Fin 22 → Bool) (x : GlobalTailChoice D r c h full) (hD : 1642≤D) (hh : ∃ e,h e≠0) :
    Filter.Tendsto (profileTermMajorant D r c h full x) Filter.atTop (nhds 0) := by
  unfold profileTermMajorant
  split_ifs with hs
  · have he : globalTailGain D r c h full x-profileCost D c h<0 := by linarith
    convert (negative_rpow_tendsto_zero _ he).const_mul ((fullProfileConstant D)^11) using 1; simp
  · have he : -(∑ e,triangular (h e))/3<0 := by have := singular_triangular_sum_pos h hh; linarith
    have hD' : -(D:ℝ)+1641<0 := by
      have hDc : (1642:ℝ)≤D := by exact_mod_cast hD
      linarith
    convert ((negative_rpow_tendsto_zero _ he).const_mul (residualDirectConstant D h)).add
      ((negative_rpow_tendsto_zero _ hD').const_mul (residualNondirectConstant D)) using 1; simp

private instance certificate_instance_0586 : OAI.SidorenkoCounterexample.ProofCertificate_0586 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7
  exact @certificate_proof_0586 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 q0 q1 q2 q3 q4 q5 q6 q7

theorem certificate_proof_0587 (q N A B D S G : ℝ) (hq : 1≤q) (hB : 0≤B)
    (hN : N≤A*q^(-S)+B*q^(-D+1575)) (hg : G=(2/3:ℝ)*S) (hS : S≤99) :
    N*q^G≤A*q^(-S/3)+B*q^(-D+1641) := by
  have hq0 : 0<q := zero_lt_one.trans_le hq
  rw [hg]
  have he : -D+1575+(2/3:ℝ)*S≤-D+1641 := by linarith
  calc _ ≤ (A*q^(-S)+B*q^(-D+1575))*q^((2/3:ℝ)*S) :=
        mul_le_mul_of_nonneg_right hN (Real.rpow_nonneg hq0.le _)
       _ = A*q^(-S/3)+B*q^(-D+1575+(2/3:ℝ)*S) := by
        rw [add_mul,mul_assoc,mul_assoc,←Real.rpow_add hq0,←Real.rpow_add hq0,
          show -S+(2/3:ℝ)*S=-S/3 by ring]
       _ ≤ _ := add_le_add le_rfl (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hq he) hB)

private instance certificate_instance_0587 : OAI.SidorenkoCounterexample.ProofCertificate_0587 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11
  exact @certificate_proof_0587 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11

section Actual
variable {K E : Type} [Field K] [AddCommGroup E] [Module K E] [Fintype K] [Finite E]
variable (ω : LinearMap.BilinForm K E)
theorem certificate_proof_0588 (h2 : (2:K)≠0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
    (D r : ℕ) (hD : 2*D=finrank K E) (c : Fin 22 → ℕ) (h : Fin 33 → ℕ) (hc : ∀ j,c j≤D)
    (full : Fin 22 → Bool) (x : GlobalTailChoice D r c h full) (hlarge : 33≤D)
    (hdich : 0<profileCost D c h-globalTailGain D r c h full x ∨
      ((∀ e,h e=0 ∨ h e=2) ∧ globalTailGain D r c h full x=(2/3:ℝ)*∑ e,triangular (h e))) :
    normalizedPointProfileCount ω c h*(Fintype.card K:ℝ)^(globalTailGain D r c h full x)≤
      profileTermMajorant D r c h full x (Fintype.card K) := by
  have hq0 : (0:ℝ)<Fintype.card K := by exact_mod_cast Fintype.card_pos (α:=K)
  have hq1 : (1:ℝ)≤Fintype.card K := by exact_mod_cast Fintype.card_pos (α:=K)
  unfold profileTermMajorant
  split_ifs with hs
  · calc _ ≤ ((fullProfileConstant D)^11*(Fintype.card K:ℝ)^(-profileCost D c h))*
          (Fintype.card K:ℝ)^(globalTailGain D r c h full x) :=
        mul_le_mul_of_nonneg_right (normalizedPointProfileCount_exposure ω h2 ha hω D hD c h hc)
          (Real.rpow_nonneg hq0.le _)
         _ = _ := by rw [mul_assoc,←Real.rpow_add hq0]; congr 2; ring
  · obtain ⟨hh,hg⟩ := hdich.resolve_left hs
    exact residual_gain_bound _ _ _ _ _ _ _ hq1 (residualNondirectConstant_nonneg D)
      (normalizedPointProfileCount_residual ω h2 ha hω D hD c h hh hlarge) hg
      (residual_triangular_sum_le h hh)

private instance certificate_instance_0588 : OAI.SidorenkoCounterexample.ProofCertificate_0588 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19 q20
  exact @certificate_proof_0588 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19 q20

end Actual
theorem certificate_proof_0589 (D r : ℕ) (c : Fin 22 → ℕ) (h : Fin 33 → ℕ)
    (full : Fin 22 → Bool) (hD : 1642≤D) (hh : ∃ e,h e≠0) :
    Filter.Tendsto (profileTailMajorant D r c h full) Filter.atTop (nhds 0) := by
  have ht (x : GlobalTailChoice D r c h full) : Filter.Tendsto
      (fun q=>globalTailConstant D r c h full x*profileTermMajorant D r c h full x q) Filter.atTop (nhds 0) := by
    convert (profileTermMajorant_tendsto_zero D r c h full x hD hh).const_mul
      (globalTailConstant D r c h full x) using 1; simp
  change Filter.Tendsto (fun q=>∑ x : GlobalTailChoice D r c h full,
    globalTailConstant D r c h full x*profileTermMajorant D r c h full x q) _ _
  simpa only [Finset.sum_const_zero] using tendsto_finsetSum Finset.univ (fun x _=>ht x)

private instance certificate_instance_0589 : OAI.SidorenkoCounterexample.ProofCertificate_0589 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6
  exact @certificate_proof_0589 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 q0 q1 q2 q3 q4 q5 q6

section ActualProduct
variable {K E : Type} [Field K] [AddCommGroup E] [Module K E] [Fintype K] [Finite E]
variable (ω : LinearMap.BilinForm K E)
theorem certificate_proof_0590 (h2 : (2:K)≠0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
    (D r : ℕ) (hD : 2*D=finrank K E) (c : Fin 22 → ℕ) (h : Fin 33 → ℕ) (hc : ∀ j,c j≤D)
    (full : Fin 22 → Bool) (hlarge : 33≤D)
    (hdich : ∀ x : GlobalTailChoice D r c h full, 0<profileCost D c h-globalTailGain D r c h full x ∨
      ((∀ e,h e=0 ∨ h e=2) ∧ globalTailGain D r c h full x=(2/3:ℝ)*∑ e,triangular (h e))) :
    normalizedPointProfileCount ω c h*(∏ j,faceTailMajorant D r (c j) (profileS c h j) (full j) (Fintype.card K))≤
      profileTailMajorant D r c h full (Fintype.card K) := by
  have hq : (0:ℝ)<Fintype.card K := by exact_mod_cast Fintype.card_pos (α:=K)
  rw [prod_faceTailMajorant _ _ _ _ _ _ hq,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro x _
  have ht := mul_le_mul_of_nonneg_left
    (normalizedPointProfile_term_bound ω h2 ha hω D r hD c h hc full x hlarge (hdich x))
    (globalTailConstant_nonneg D r c h full x)
  exact (le_of_eq (by ring)).trans ht

private instance certificate_instance_0590 : OAI.SidorenkoCounterexample.ProofCertificate_0590 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19
  exact @certificate_proof_0590 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19

end ActualProduct
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
open scoped BigOperators
section ActiveFace
variable {K E : Type} [Field K] [AddCommGroup E] [Module K E] [Fintype K] [Finite E]
variable (ω : LinearMap.BilinForm K E)
omit [Fintype K] [Finite E] in
theorem certificate_proof_0591 (r : ℕ) (A : SymplecticLagrangian ω)
    (L : Fin 3 → SymplecticLagrangian ω) (T : Finset (Fin 3)) :
    0 ≤ activeFaceDensity ω r A L T := by unfold activeFaceDensity; positivity

private instance certificate_instance_0591 : OAI.SidorenkoCounterexample.ProofCertificate_0591 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9
  exact @certificate_proof_0591 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9

omit [Fintype K] in
theorem certificate_proof_0592 (A : SymplecticLagrangian ω) :
    (0:ℝ)<Nat.card (SymplecticLagrangian ω) := by
  let : Nonempty (SymplecticLagrangian ω) := ⟨A⟩
  exact_mod_cast Nat.card_pos

private instance certificate_instance_0592 : OAI.SidorenkoCounterexample.ProofCertificate_0592 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7
  exact @certificate_proof_0592 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 q0 q1 q2 q3 q4 q5 q6 q7

omit [Fintype K] in
theorem certificate_proof_0593 (r : ℕ) (A : SymplecticLagrangian ω)
    (L : Fin 3 → SymplecticLagrangian ω) : activeFaceDensity ω r A L ∅=1 := by
  have hc : Nat.card (ActiveCenterSet ω r L ∅)=Nat.card (SymplecticLagrangian ω) :=
    Nat.card_congr (Equiv.subtypeUnivEquiv (by simp))
  simp only [activeFaceDensity,hc,Finset.card_empty,pow_zero,mul_one]
  exact div_self (lagrangian_card_pos ω A).ne'

private instance certificate_instance_0593 : OAI.SidorenkoCounterexample.ProofCertificate_0593 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9
  exact @certificate_proof_0593 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9

theorem certificate_proof_0594 (h2 : (2:K)≠0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
    (D r : ℕ) (hD : 2*D=finrank K E) (hr : r ≤ D) (A : SymplecticLagrangian ω)
    (L : Fin 3 → SymplecticLagrangian ω) (i : Fin 3) : activeFaceDensity ω r A L {i}=1 := by
  classical
  have hc : Nat.card (ActiveCenterSet ω r L {i})=Nat.card (SymplecticCenterStratum ω (L i) r) :=
    Nat.card_congr (Equiv.subtypeEquivRight (by
      intro Y
      simp only [Finset.mem_singleton,forall_eq]
      rw [inf_comm]))
  rw [symplectic_center_stratum_card_eq ω h2 ha hω (L i) A r] at hc
  simp only [activeFaceDensity,hc,Finset.card_singleton,pow_one]
  have hL := (lagrangian_card_pos ω A).ne'
  have hA := (symplectic_center_stratum_card_pos ω h2 ha hω D hD A r hr).ne'
  field_simp

private instance certificate_instance_0594 : OAI.SidorenkoCounterexample.ProofCertificate_0594 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17
  exact @certificate_proof_0594 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17

omit [Fintype K] in
theorem certificate_proof_0595 (r : ℕ) (A : SymplecticLagrangian ω)
    (L : Fin 3 → SymplecticLagrangian ω) (i k : Fin 3) (hik : i≠k) :
    activeFaceDensity ω r A L {i,k}=pairFaceDensity ω r A (L i) (L k) := by
  classical
  have hc : Nat.card (ActiveCenterSet ω r L {i,k})=Nat.card (PairCenterSet ω r (L i).val (L k).val) :=
    Nat.card_congr (Equiv.subtypeEquivRight (by intro Y; simp))
  simp only [activeFaceDensity,hc,Finset.card_pair hik,pairFaceDensity]
  have hL := (lagrangian_card_pos ω A).ne'
  field_simp

private instance certificate_instance_0595 : OAI.SidorenkoCounterexample.ProofCertificate_0595 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12
  exact @certificate_proof_0595 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12

omit [Fintype K] in
theorem certificate_proof_0596 (r : ℕ) (A : SymplecticLagrangian ω)
    (L : Fin 3 → SymplecticLagrangian ω) :
    activeFaceDensity ω r A L Finset.univ=tripleFaceDensity ω r A (L 0) (L 1) (L 2) := by
  classical
  have hc : Nat.card (ActiveCenterSet ω r L Finset.univ)=Nat.card (TripleCenterSet ω r (L 0).val (L 1).val (L 2).val) :=
    Nat.card_congr (Equiv.subtypeEquivRight (by intro Y; simp [Fin.forall_fin_succ]))
  simp only [activeFaceDensity,hc,Finset.card_univ,Fintype.card_fin,tripleFaceDensity]
  have hL := (lagrangian_card_pos ω A).ne'
  field_simp

private instance certificate_instance_0596 : OAI.SidorenkoCounterexample.ProofCertificate_0596 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9
  exact @certificate_proof_0596 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9

theorem certificate_proof_0597 (D r c : ℕ) (s : Fin 3 → ℕ) (q : ℝ) (hq : 1 ≤ q) :
    1 ≤ faceTailMajorant D r c s false q := by
  rw [faceTailMajorant_false]
  have hc : 1 ≤ lowerTailConstant D r := le_max_left _ _
  have hg : 0 ≤ tailGain D false (lowerTailTuple c s) := by
    simp only [tailGain,Bool.false_eq_true,reduceIte]
    exact triangular_nonneg (by positivity)
  exact one_le_mul_of_one_le_of_one_le hc (Real.one_le_rpow hq hg)

private instance certificate_instance_0597 : OAI.SidorenkoCounterexample.ProofCertificate_0597 := by
  constructor
  intro q0 q1 q2 q3 q4 q5
  exact @certificate_proof_0597 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 q0 q1 q2 q3 q4 q5

end ActiveFace
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
open scoped BigOperators
section ActiveFaceBound
variable {K E : Type} [Field K] [AddCommGroup E] [Module K E] [Fintype K] [Finite E]
variable (ω : LinearMap.BilinForm K E)
theorem certificate_proof_0598 (T : Finset (Fin 3)) : T=∅ ∨ T={0} ∨ T={1} ∨ T={2} ∨
    T={0,1} ∨ T={0,2} ∨ T={1,2} ∨ T=Finset.univ := by
  revert T; decide

private instance certificate_instance_0598 : OAI.SidorenkoCounterexample.ProofCertificate_0598 := by
  constructor
  intro q0
  exact @certificate_proof_0598 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 q0

theorem certificate_proof_0599 (h2 : (2:K)≠0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
    (D r : ℕ) (hD : 2*D=finrank K E) (hr : D=2*r) (c : ℕ) (s : Fin 3 → ℕ)
    (A : SymplecticLagrangian ω) (L : Fin 3 → SymplecticLagrangian ω)
    (hL : LocalProfile ω c (c+s 0) (c+s 1) (c+s 2) (L 0) (L 1) (L 2))
    (T : Finset (Fin 3)) (hT : T≠Finset.univ) :
    activeFaceDensity ω r A L T ≤ faceTailMajorant D r c s false (Fintype.card K) := by
  have hq : (1:ℝ) ≤ Fintype.card K := by exact_mod_cast Fintype.card_pos (α:=K)
  have hr' : r ≤ D := by omega
  rcases fin3_subsets T with ht|ht|ht|ht|ht|ht|ht|ht
  · rw [ht,activeFaceDensity_empty]; exact one_le_lowerTailMajorant D r c s _ hq
  · rw [ht,activeFaceDensity_singleton ω h2 ha hω D r hD hr']; exact one_le_lowerTailMajorant D r c s _ hq
  · rw [ht,activeFaceDensity_singleton ω h2 ha hω D r hD hr']; exact one_le_lowerTailMajorant D r c s _ hq
  · rw [ht,activeFaceDensity_singleton ω h2 ha hω D r hD hr']; exact one_le_lowerTailMajorant D r c s _ hq
  · rw [ht,activeFaceDensity_pair ω r A L 0 1 (by decide),faceTailMajorant_false]
    exact pairFaceDensity_lower_tail ω h2 ha hω D r hD hr c s A (L 0) (L 1) 0 hL.2.1
  · rw [ht,activeFaceDensity_pair ω r A L 0 2 (by decide),faceTailMajorant_false]
    exact pairFaceDensity_lower_tail ω h2 ha hω D r hD hr c s A (L 0) (L 2) 1 hL.2.2.1
  · rw [ht,activeFaceDensity_pair ω r A L 1 2 (by decide),faceTailMajorant_false]
    exact pairFaceDensity_lower_tail ω h2 ha hω D r hD hr c s A (L 1) (L 2) 2 hL.2.2.2
  · exact (hT ht).elim

private instance certificate_instance_0599 : OAI.SidorenkoCounterexample.ProofCertificate_0599 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19 q20 q21
  exact @certificate_proof_0599 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19 q20 q21

theorem certificate_proof_0600 [Invertible (2:K)]
    (h2 : (2:K)≠0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
    (D r : ℕ) (hD : 2*D=finrank K E) (hr : D=2*r) (c : ℕ) (s : Fin 3 → ℕ)
    (hq : 4*lagrangianConstant D ≤ (Fintype.card K:ℝ))
    (A : SymplecticLagrangian ω) (L : Fin 3 → SymplecticLagrangian ω)
    (hL : LocalProfile ω c (c+s 0) (c+s 1) (c+s 2) (L 0) (L 1) (L 2))
    (T : Finset (Fin 3)) :
    activeFaceDensity ω r A L T ≤ faceTailMajorant D r c s (decide (T=Finset.univ)) (Fintype.card K) := by
  classical
  by_cases ht : T=Finset.univ
  · simp only [ht,decide_true,faceTailMajorant_true,activeFaceDensity_full]
    have hb := tripleFaceDensity_tail_bound ω h2 ha hω D r hD hr hq A (L 0) (L 1) (L 2)
    dsimp only at hb
    rw [hL.1,hL.2.1,hL.2.2.1,hL.2.2.2] at hb
    have hs : ![c+s 0-c,c+s 1-c,c+s 2-c]=s := by funext i; fin_cases i <;> simp
    rwa [hs] at hb
  · simp only [ht,decide_false]
    exact activeFaceDensity_lower_bound ω h2 ha hω D r hD hr c s A L hL T ht

private instance certificate_instance_0600 : OAI.SidorenkoCounterexample.ProofCertificate_0600 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19 q20 q21 q22
  exact @certificate_proof_0600 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19 q20 q21 q22

end ActiveFaceBound
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
open scoped BigOperators
section Integrated
variable {K E : Type} [Field K] [AddCommGroup E] [Module K E] [Fintype K] [Finite E]
variable (ω : LinearMap.BilinForm K E)
omit [Fintype K] in
theorem certificate_proof_0601 (r : ℕ) (A : SymplecticLagrangian ω)
    (T : Fin 22 → Finset (Fin 3)) (c : Fin 22 → ℕ) (h : Fin 33 → ℕ) :
    0 ≤ profileActiveDensity ω r A T c h := by
  classical
  unfold profileActiveDensity
  exact div_nonneg (Finset.sum_nonneg (fun L _=>Finset.prod_nonneg
    (fun j _=>activeFaceDensity_nonneg ω r A _ (T j)))) (by positivity)

private instance certificate_instance_0601 : OAI.SidorenkoCounterexample.ProofCertificate_0601 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11
  exact @certificate_proof_0601 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11

theorem certificate_proof_0602 [Invertible (2:K)]
    (h2 : (2:K)≠0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
    (D r : ℕ) (hD : 2*D=finrank K E) (hr : D=2*r)
    (hq : 4*lagrangianConstant D ≤ (Fintype.card K:ℝ))
    (A : SymplecticLagrangian ω) (T : Fin 22 → Finset (Fin 3)) (c : Fin 22 → ℕ) (h : Fin 33 → ℕ) :
    profileActiveDensity ω r A T c h ≤ normalizedPointProfileCount ω c h*
      ∏ j,faceTailMajorant D r (c j) (profileS c h j) (decide (T j=Finset.univ)) (Fintype.card K) := by
  classical
  let := Fintype.ofFinite {L : Fin 13 → SymplecticLagrangian ω // PointProfile ω c h L}
  unfold profileActiveDensity normalizedPointProfileCount
  rw [div_mul_eq_mul_div]
  apply div_le_div_of_nonneg_right _ (by positivity)
  calc _  ≤  ∑ _L : {L : Fin 13 → SymplecticLagrangian ω // PointProfile ω c h L},
      ∏ j,faceTailMajorant D r (c j) (profileS c h j) (decide (T j=Finset.univ)) (Fintype.card K) := by
        apply Finset.sum_le_sum
        intro L _
        apply Finset.prod_le_prod
        · intro j _; exact activeFaceDensity_nonneg ω r A _ (T j)
        · intro j _
          have hl := L.property.faceLocal ω j
          have hp := L.property.geometric ω ha hω D hD
          have hs (i : Fin 3) : c j+profileS c h j i=h (facePair j i) :=
            Nat.add_sub_of_le (hp.2.1 j i)
          exact activeFaceDensity_tail_bound ω h2 ha hω D r hD hr (c j) (profileS c h j) hq A
            (fun i=>L.val (faceVertex j i)) (by simpa only [hs] using hl) (T j)
       _ = _ := by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Nat.card_eq_fintype_card]

private instance certificate_instance_0602 : OAI.SidorenkoCounterexample.ProofCertificate_0602 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19 q20
  exact @certificate_proof_0602 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19 q20

end Integrated
theorem certificate_proof_0603 (D r : ℕ) (c : Fin 22 → ℕ) (h : Fin 33 → ℕ)
    (full : Fin 22 → Bool) (q : ℝ) (hq : 0 ≤ q) : 0 ≤ profileTailMajorant D r c h full q := by
  exact Finset.sum_nonneg (fun x _=>mul_nonneg (globalTailConstant_nonneg _ _ _ _ _ _)
    (profileTermMajorant_nonneg _ _ _ _ _ _ _ hq))

private instance certificate_instance_0603 : OAI.SidorenkoCounterexample.ProofCertificate_0603 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6
  exact @certificate_proof_0603 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 q0 q1 q2 q3 q4 q5 q6

theorem certificate_proof_0604 (D r : ℕ) (full : Fin 22 → Bool) (hD : 1642 ≤ D) :
    Filter.Tendsto (integratedTailMajorant D r full) Filter.atTop (nhds 0) := by
  classical
  have ht (p : DimProfile D) : Filter.Tendsto
      (fun q=>if ∃ e,p.h e≠0 then profileTailMajorant D r p.c p.h full q else 0) Filter.atTop (nhds 0) := by
    by_cases hp : ∃ e,p.h e≠0
    · simpa only [hp,reduceIte] using profileTailMajorant_tendsto_zero D r p.c p.h full hD hp
    · simpa only [hp,reduceIte] using (tendsto_const_nhds (x:=(0:ℝ)) (f:=Filter.atTop))
  change Filter.Tendsto (fun q=>∑ p : DimProfile D, if ∃ e,p.h e≠0 then profileTailMajorant D r p.c p.h full q else 0) _ _
  simpa only [Finset.sum_const_zero] using tendsto_finsetSum Finset.univ (fun p _=>ht p)

private instance certificate_instance_0604 : OAI.SidorenkoCounterexample.ProofCertificate_0604 := by
  constructor
  intro q0 q1 q2 q3
  exact @certificate_proof_0604 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 q0 q1 q2 q3

end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
open scoped BigOperators
theorem certificate_proof_0605 : 1642 ≤ singularTailThreshold := (Classical.choose_spec globalTail_dichotomy).1

private instance certificate_instance_0605 : OAI.SidorenkoCounterexample.ProofCertificate_0605 := by
  constructor
  intro c0
  exact @certificate_proof_0605 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25

theorem certificate_proof_0606 (D : ℕ) (hD : singularTailThreshold ≤ D)
    (r : ℕ) (hr : D=2*r) (c : Fin 22 → ℕ) (h : Fin 33 → ℕ) (hp : GeometricProfile D c h)
    (full : Fin 22 → Bool) (x : GlobalTailChoice D r c h full) :
    0<profileCost D c h-globalTailGain D r c h full x ∨
      ((∀ e,h e=0 ∨ h e=2) ∧ globalTailGain D r c h full x=(2/3:ℝ)*∑ e,triangular (h e)) := by
  rcases (Classical.choose_spec globalTail_dichotomy).2 D hD r hr c h hp full x with hs|hs
  · exact Or.inl hs
  · exact Or.inr hs.2

private instance certificate_instance_0606 : OAI.SidorenkoCounterexample.ProofCertificate_0606 := by
  constructor
  intro c0 q0 q1 q2 q3 q4 q5 q6 q7 q8
  exact @certificate_proof_0606 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 q0 q1 q2 q3 q4 q5 q6 q7 q8

section IntegratedBound
variable {K E : Type} [Field K] [AddCommGroup E] [Module K E] [Fintype K] [Finite E]
variable (ω : LinearMap.BilinForm K E)
theorem certificate_proof_0607 [Invertible (2:K)]
    (h2 : (2:K)≠0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
    (D r : ℕ) (hD : 2*D=finrank K E) (hr : D=2*r) (hlarge : singularTailThreshold ≤ D)
    (hq : 4*lagrangianConstant D ≤ (Fintype.card K:ℝ))
    (A : SymplecticLagrangian ω) (T : Fin 22 → Finset (Fin 3)) (c : Fin 22 → ℕ) (h : Fin 33 → ℕ) :
    profileActiveDensity ω r A T c h ≤ profileTailMajorant D r c h (fun j=>decide (T j=Finset.univ)) (Fintype.card K) := by
  classical
  by_cases hp : Nonempty {L : Fin 13 → SymplecticLagrangian ω // PointProfile ω c h L}
  · obtain ⟨L⟩ := hp
    have hg := L.property.geometric ω ha hω D hD
    refine (profileActiveDensity_bound ω h2 ha hω D r hD hr hq A T c h).trans ?_
    apply normalizedPointProfile_product_bound ω h2 ha hω D r hD c h hg.1 _
      (by have := singularTailThreshold_large; omega)
    exact singularTailThreshold_dichotomy D hlarge r hr c h hg _
  · let : IsEmpty {L : Fin 13 → SymplecticLagrangian ω // PointProfile ω c h L} := not_nonempty_iff.mp hp
    have hz : profileActiveDensity ω r A T c h=0 := by simp [profileActiveDensity]
    rw [hz]
    exact profileTailMajorant_nonneg _ _ _ _ _ _ (Nat.cast_nonneg _)

private instance certificate_instance_0607 : OAI.SidorenkoCounterexample.ProofCertificate_0607 := by
  constructor
  intro c0 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19 q20 q21
  exact @certificate_proof_0607 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19 q20 q21

omit [Fintype K] in
theorem certificate_proof_0608 (D r : ℕ) (A : SymplecticLagrangian ω)
    (T : Fin 22 → Finset (Fin 3)) : 0 ≤ integratedActiveTail ω D r A T := by
  classical
  unfold integratedActiveTail
  exact Finset.sum_nonneg (fun p _=>by split_ifs; exact profileActiveDensity_nonneg _ _ _ _ _ _; rfl)

private instance certificate_instance_0608 : OAI.SidorenkoCounterexample.ProofCertificate_0608 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10
  exact @certificate_proof_0608 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10

theorem certificate_proof_0609 [Invertible (2:K)]
    (h2 : (2:K)≠0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
    (D r : ℕ) (hD : 2*D=finrank K E) (hr : D=2*r) (hlarge : singularTailThreshold ≤ D)
    (hq : 4*lagrangianConstant D ≤ (Fintype.card K:ℝ))
    (A : SymplecticLagrangian ω) (T : Fin 22 → Finset (Fin 3)) :
    integratedActiveTail ω D r A T ≤ integratedTailMajorant D r (fun j=>decide (T j=Finset.univ)) (Fintype.card K) := by
  classical
  unfold integratedActiveTail integratedTailMajorant
  apply Finset.sum_le_sum
  intro p _
  split_ifs
  · exact profileActiveDensity_tail_bound ω h2 ha hω D r hD hr hlarge hq A T p.c p.h
  · rfl

private instance certificate_instance_0609 : OAI.SidorenkoCounterexample.ProofCertificate_0609 := by
  constructor
  intro c0 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19
  exact @certificate_proof_0609 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19

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
include hω hD in
theorem certificate_proof_0610 (L : Fin 13 → SymplecticLagrangian ω)
    (s : Finset (Fin 13)) (hs : s.Nonempty) :
    finrank K ↥(s.inf fun i => (L i).val : Submodule K E) ≤ D := by
  obtain ⟨i, hi⟩ := hs
  have hd := self_orthogonal_twice_finrank ω (L i).val hω (L i).property
  have hb : (s.inf fun i => (L i).val : Submodule K E) ≤ (L i).val := Finset.inf_le hi
  have := Submodule.finrank_mono hb
  omega

private instance certificate_instance_0610 : OAI.SidorenkoCounterexample.ProofCertificate_0610 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12
  exact @certificate_proof_0610 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12

theorem certificate_proof_0611 (L : Fin 13 → SymplecticLagrangian ω) :
    PointProfile ω (configProfile ω hω D hD L).c (configProfile ω hω D hD L).h L :=
  ⟨fun _ => rfl, fun _ => rfl⟩

private instance certificate_instance_0611 : OAI.SidorenkoCounterexample.ProofCertificate_0611 := by
  constructor
  intro c0 c1 c2 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10
  exact @certificate_proof_0611 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10

theorem certificate_proof_0612 (L : Fin 13 → SymplecticLagrangian ω) (p : DimProfile D) :
    configProfile ω hω D hD L = p ↔ PointProfile ω p.c p.h L := by
  constructor
  · intro h; rw [← h]; exact configProfile_property ω hω D hD L
  · intro h
    apply Prod.ext
    · funext j; exact Fin.ext (h.1 j)
    · funext e; exact Fin.ext (h.2 e)

private instance certificate_instance_0612 : OAI.SidorenkoCounterexample.ProofCertificate_0612 := by
  constructor
  intro c0 c1 c2 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11
  exact @certificate_proof_0612 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11

include hω hD in
theorem certificate_proof_0613 (r : ℕ) (A : SymplecticLagrangian ω)
    (T : Fin 22 → Finset (Fin 3)) :
    actualSingularTail ω r A T = integratedActiveTail ω D r A T := by
  classical
  let := Fintype.ofFinite (Fin 13 → SymplecticLagrangian ω)
  let := fun p : DimProfile D => Fintype.ofFinite
    {L : Fin 13 → SymplecticLagrangian ω // PointProfile ω p.c p.h L}
  let w (L : Fin 13 → SymplecticLagrangian ω) : ℝ :=
    ∏ j, activeFaceDensity ω r A (fun i => L (faceVertex j i)) (T j)
  let f (L : Fin 13 → SymplecticLagrangian ω) : ℝ :=
    if ∃ e, (configProfile ω hω D hD L).h e ≠ 0 then w L else 0
  have he (p : DimProfile D) :
      (∑ L : {L // configProfile ω hω D hD L = p}, f L.val) =
      if ∃ e, p.h e ≠ 0 then
        ∑ L : {L // PointProfile ω p.c p.h L}, w L.val else 0 := by
    let e : {L // configProfile ω hω D hD L = p} ≃ {L // PointProfile ω p.c p.h L} :=
      Equiv.subtypeEquivRight (fun L => configProfile_eq_iff ω hω D hD L p)
    have hf (L : {L // configProfile ω hω D hD L = p}) :
        f L.val = if ∃ e, p.h e ≠ 0 then w (e L).val else 0 := by
      dsimp only [f]; rw [L.property]; rfl
    simp_rw [hf]
    by_cases hp : ∃ e, p.h e ≠ 0
    · simp only [hp,reduceIte]; exact Equiv.sum_comp e (fun L => w L.val)
    · simp only [hp,reduceIte,Finset.sum_const_zero]
  have hsum : (∑ L, f L) = ∑ p : DimProfile D,
      if ∃ e, p.h e ≠ 0 then ∑ L : {L // PointProfile ω p.c p.h L}, w L.val else 0 := by
    rw [← Fintype.sum_fiberwise (configProfile ω hω D hD) f]
    exact Finset.sum_congr rfl (fun p _ => he p)
  change (∑ L, f L) / (Nat.card (SymplecticLagrangian ω) : ℝ)^13 =
    ∑ p : DimProfile D, if ∃ e, p.h e ≠ 0 then
      (∑ L : {L // PointProfile ω p.c p.h L}, w L.val) /
        (Nat.card (SymplecticLagrangian ω) : ℝ)^13 else 0
  rw [hsum,Finset.sum_div]
  apply Finset.sum_congr rfl
  intro p _
  split_ifs <;> simp

private instance certificate_instance_0613 : OAI.SidorenkoCounterexample.ProofCertificate_0613 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12
  exact @certificate_proof_0613 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12

end ActualProfile
end SidorenkoCounterexample
end OAI

theorem solution : OAI.SidorenkoCounterexample.ProofCertificate_0572 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0573 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0574 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0575 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0576 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0577 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0578 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0579 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0580 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0581 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0582 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0583 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0584 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0585 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0586 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0587 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0588 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0589 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0590 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0591 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0592 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0593 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0594 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0595 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0596 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0597 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0598 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0599 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0600 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0601 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0602 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0603 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0604 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0605 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0606 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0607 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0608 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0609 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0610 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0611 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0612 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0613 := by
  exact ⟨inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance⟩
end

