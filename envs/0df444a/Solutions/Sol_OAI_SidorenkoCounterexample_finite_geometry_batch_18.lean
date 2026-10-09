-- Prove2me | solution 1 for OAI.SidorenkoCounterexample.finite_geometry_batch_18
-- status  : ACCEPTED   (prove)
-- author  : @abcdefg
-- created : 2026-10-09T06:14:29.87903+00:00
-- url     : https://prove2.me/submissions/608231b8-3593-4b3b-9ff3-88bdec32d406

import Definitions.Def_SidorenkoCertificateBundleA
set_option linter.unusedVariables false
section
variable [p0 : OAI.SidorenkoCounterexample.ProofCertificate_0000]
  [p1 : OAI.SidorenkoCounterexample.ProofCertificate_0005]
  [p2 : OAI.SidorenkoCounterexample.ProofCertificate_0207]
  [p3 : OAI.SidorenkoCounterexample.ProofCertificate_0214]
  [p4 : OAI.SidorenkoCounterexample.ProofCertificate_0216]
  [p5 : OAI.SidorenkoCounterexample.ProofCertificate_0217]
  [p6 : OAI.SidorenkoCounterexample.ProofCertificate_0221]
  [p7 : OAI.SidorenkoCounterexample.ProofCertificate_0298]
  [p8 : OAI.SidorenkoCounterexample.ProofCertificate_0352]
  [p9 : OAI.SidorenkoCounterexample.ProofCertificate_0374]
  [p10 : OAI.SidorenkoCounterexample.ProofCertificate_0383]
  [p11 : OAI.SidorenkoCounterexample.ProofCertificate_0414]
  [p12 : OAI.SidorenkoCounterexample.ProofCertificate_0438]
  [p13 : OAI.SidorenkoCounterexample.ProofCertificate_0440]
  [p14 : OAI.SidorenkoCounterexample.ProofCertificate_0442]
  [p15 : OAI.SidorenkoCounterexample.ProofCertificate_0443]
  [p16 : OAI.SidorenkoCounterexample.ProofCertificate_0444]
  [p17 : OAI.SidorenkoCounterexample.ProofCertificate_0445]
  [p18 : OAI.SidorenkoCounterexample.ProofCertificate_0446]
  [p19 : OAI.SidorenkoCounterexample.ProofCertificate_0447]
  [p20 : OAI.SidorenkoCounterexample.ProofCertificate_0448]
  [p21 : OAI.SidorenkoCounterexample.ProofCertificate_0452]
  [p22 : OAI.SidorenkoCounterexample.ProofCertificate_0455]
  [p23 : OAI.SidorenkoCounterexample.ProofCertificate_0456]
  [p24 : OAI.SidorenkoCounterexample.ProofCertificate_0459]
  [p25 : OAI.SidorenkoCounterexample.ProofCertificate_0460]
  [p26 : OAI.SidorenkoCounterexample.ProofCertificate_0461]
  [p27 : OAI.SidorenkoCounterexample.ProofCertificate_0462]
  [p28 : OAI.SidorenkoCounterexample.ProofCertificate_0464]
  [p29 : OAI.SidorenkoCounterexample.ProofCertificate_0465]
include p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29

namespace OAI
namespace SidorenkoCounterexample
open scoped BigOperators
section Sequential
variable {A : Type} [Finite A]
end Sequential
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open scoped BigOperators
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
section RawProfile
variable {K E : Type} [Field K] [AddCommGroup E] [Module K E] [Fintype K] [Finite E]
variable (ω : LinearMap.BilinForm K E)
end RawProfile
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
open scoped BigOperators
theorem certificate_proof_0466 (D : ℕ) (c : Fin 22 → ℕ) (h : Fin 33 → ℕ) (j : Fin 22) :
    naturalProfileCost D (c j) (h (facePair j 0)) (h (facePair j 1)) (h (facePair j 2))=faceNaturalCost D c h j := by
  simp only [naturalProfileCost,faceNaturalCost,Fin.sum_univ_three]

private instance certificate_instance_0466 : OAI.SidorenkoCounterexample.ProofCertificate_0466 := by
  constructor
  intro q0 q1 q2 q3
  exact @certificate_proof_0466 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 q0 q1 q2 q3

theorem certificate_proof_0467 (D : ℕ) (c : Fin 22 → ℕ) (h : Fin 33 → ℕ) (κ : Fin 6) (n : Fin 10) :
    naturalProfileCost D (c (classFace κ n.succ)) (h (classOldPair κ n))
      (h (classNewPairZero κ n)) (h (classNewPairOne κ n))=faceNaturalCost D c h (classFace κ n.succ) := by
  let f (e : Fin 33) := (h e-c (classFace κ n.succ)+1).choose 2
  have hs : (∑ e ∈ Finset.univ.image (facePair (classFace κ n.succ)), f e)=
      ∑ k : Fin 3, f (facePair (classFace κ n.succ) k) :=
    Finset.sum_image (fun a _ b _ hab => facePair_injective _ hab)
  rw [classStep_pairs] at hs
  obtain ⟨h01,h02,h12⟩ := classStep_pairs_distinct κ n
  simp only [Finset.sum_insert,Finset.mem_insert,Finset.mem_singleton,h01,h02,h12,
    or_self,not_false_eq_true,Finset.sum_singleton] at hs
  unfold naturalProfileCost faceNaturalCost
  change _ = (D+1)*c (classFace κ n.succ)+∑ k, f (facePair (classFace κ n.succ) k)
  rw [←hs]
  simp only [f]
  omega

private instance certificate_instance_0467 : OAI.SidorenkoCounterexample.ProofCertificate_0467 := by
  constructor
  intro q0 q1 q2 q3 q4
  exact @certificate_proof_0467 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 q0 q1 q2 q3 q4

section ExposureProfile
variable {K E : Type} [Field K] [AddCommGroup E] [Module K E]
variable (ω : LinearMap.BilinForm K E)
theorem certificate_proof_0468 {c : Fin 22 → ℕ} {h : Fin 33 → ℕ} {L : Fin 13 → SymplecticLagrangian ω}
    (hL : PointProfile ω c h L) (j : Fin 22) (i k l : Fin 13) (e f g : Fin 33)
    (hj : faces j={i,k,l}) (he : pairVertices e={i,k}) (hf : pairVertices f={i,l})
    (hg : pairVertices g={k,l}) : LocalProfile ω (c j) (h e) (h f) (h g) (L i) (L k) (L l) := by
  classical
  unfold PointProfile at hL
  refine ⟨?_,?_,?_,?_⟩
  · have hh := hL.1 j
    rw [hj,Finset.inf_insert,Finset.inf_insert,Finset.inf_singleton,←inf_assoc] at hh
    exact hh
  · have hh := hL.2 e
    rw [he,Finset.inf_insert,Finset.inf_singleton] at hh
    exact hh
  · have hh := hL.2 f
    rw [hf,Finset.inf_insert,Finset.inf_singleton] at hh
    exact hh
  · have hh := hL.2 g
    rw [hg,Finset.inf_insert,Finset.inf_singleton] at hh
    exact hh

private instance certificate_instance_0468 : OAI.SidorenkoCounterexample.ProofCertificate_0468 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19 q20
  exact @certificate_proof_0468 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19 q20

variable [Fintype K] [Finite E]
omit [Finite E] in
theorem certificate_proof_0469 (D : ℕ) (c : Fin 22 → ℕ) (h : Fin 33 → ℕ) (κ : Fin 6) (n : ℕ) :
    0≤classStepBound ω D c h κ n := by
  unfold classStepBound
  split_ifs
  · exact mul_nonneg (mul_nonneg (fullProfileConstant_pos D).le (by positivity)) (Real.rpow_nonneg (by positivity) _)
  · exact le_rfl

private instance certificate_instance_0469 : OAI.SidorenkoCounterexample.ProofCertificate_0469 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11
  exact @certificate_proof_0469 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11

theorem certificate_proof_0470 (h2 : (2:K)≠0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
    (D : ℕ) (hD : 2*D=finrank K E) (c : Fin 22 → ℕ) (h : Fin 33 → ℕ) (hc : ∀ j, c j≤D)
    (κ : Fin 6) (n : ℕ) (x : Fin (3+n) → SymplecticLagrangian ω) :
    (Nat.card {Y : SymplecticLagrangian ω // classStepConstraint ω c h κ n x Y}:ℝ) ≤ classStepBound ω D c h κ n := by
  classical
  by_cases hn : n<10
  · let L := x ⟨(classOldZero κ ⟨n,hn⟩).val,classOldZero_lt κ ⟨n,hn⟩⟩
    let M := x ⟨(classOldOne κ ⟨n,hn⟩).val,classOldOne_lt κ ⟨n,hn⟩⟩
    let j : Fin 22 := classFace κ ⟨n+1,by omega⟩
    let e := classOldPair κ ⟨n,hn⟩
    let f := classNewPairZero κ ⟨n,hn⟩
    let g := classNewPairOne κ ⟨n,hn⟩
    have hp : ∀ Y, classStepConstraint ω c h κ n x Y ↔ LocalProfile ω (c j) (h e) (h f) (h g) L M Y := by
      intro Y; simp only [classStepConstraint,dif_pos hn]; rfl
    by_cases hh : finrank K ↥(L.val ⊓ M.val)=h e
    · have heq : Nat.card {Y // classStepConstraint ω c h κ n x Y}=Nat.card (PairCompletion ω L M (c j) (h f) (h g)) := by
        apply Nat.card_congr
        exact Equiv.subtypeEquivRight (fun Y => by rw [hp]; exact ⟨fun hY => ⟨hY.1,hY.2.2⟩,fun hY => ⟨hY.1,hh,hY.2⟩⟩)
      rw [heq]
      have hb := conditionalProfile_card_raw ω h2 ha hω D hD L M (c j) (h f) (h g) (hc j)
      rw [hh] at hb
      have hcost := step_natural_cost D c h κ ⟨n,hn⟩
      change naturalProfileCost D (c j) (h e) (h f) (h g)=faceNaturalCost D c h j at hcost
      rw [hcost] at hb
      simpa only [classStepBound,dif_pos hn, e,j] using hb
    · have hem : IsEmpty {Y // classStepConstraint ω c h κ n x Y} := ⟨fun Y => hh ((hp Y.val).mp Y.property).2.1⟩
      have hz := Nat.card_eq_zero.mpr (Or.inl hem)
      rw [hz,Nat.cast_zero]
      exact classStepBound_nonneg ω D c h κ n
  · have hem : IsEmpty {Y // classStepConstraint ω c h κ n x Y} :=
      ⟨fun Y => by simpa only [classStepConstraint,dif_neg hn] using Y.property⟩
    rw [Nat.card_eq_zero.mpr (Or.inl hem),Nat.cast_zero,classStepBound,dif_neg hn]

private instance certificate_instance_0470 : OAI.SidorenkoCounterexample.ProofCertificate_0470 := by
  constructor
  intro c0 c1 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18
  exact @certificate_proof_0470 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18

omit [Fintype K] [Finite E] in
theorem certificate_proof_0471 {c : Fin 22 → ℕ} {h : Fin 33 → ℕ}
    {L : Fin 13 → SymplecticLagrangian ω} (hL : PointProfile ω c h L)
    (κ : Fin 6) (n : ℕ) (hn : n≤10) :
    SeqValid 3 (classRootConstraint ω c h κ) (classStepConstraint ω c h κ) n (classPrefix ω κ L n hn) := by
  induction n with
  | zero =>
    exact PointProfile.local ω hL _ _ _ _ _ _ _ (classRoot_correct κ)
      (classRootPairZero κ) (classRootPairOne κ) (classRootPairTwo κ)
  | succ n ih =>
    have hn' : n<10 := by omega
    refine ⟨?_,?_⟩
    · exact ih (by omega)
    · simp only [classStepConstraint,dif_pos hn']
      exact PointProfile.local ω hL _ _ _ _ _ _ _ (classStep_correct κ ⟨n,hn'⟩)
        (classOldPair_correct κ ⟨n,hn'⟩) (classNewPairZero_correct κ ⟨n,hn'⟩)
        (classNewPairOne_correct κ ⟨n,hn'⟩)

private instance certificate_instance_0471 : OAI.SidorenkoCounterexample.ProofCertificate_0471 := by
  constructor
  intro c0 c1 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12
  exact @certificate_proof_0471 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12

theorem certificate_proof_0472 (h2 : (2:K)≠0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
    (D : ℕ) (hD : 2*D=finrank K E) (c : Fin 22 → ℕ) (h : Fin 33 → ℕ) (hc : ∀ j, c j≤D)
    (κ : Fin 6) : (Nat.card {x : Fin 3 → SymplecticLagrangian ω // classRootConstraint ω c h κ x}:ℝ) ≤
      fullProfileConstant D*(Nat.card (SymplecticLagrangian ω):ℝ)^3*
        (Fintype.card K:ℝ)^(-(faceNaturalCost D c h (classFace κ 0):ℝ)) := by
  rw [Nat.card_congr (rootConstraintEquiv ω c h κ)]
  have hb := tripleProfile_card_raw ω h2 ha hω D hD (c (classFace κ 0))
    (h (facePair (classFace κ 0) 0)) (h (facePair (classFace κ 0) 1))
    (h (facePair (classFace κ 0) 2)) (hc _)
  simpa only [root_natural_cost] using hb

private instance certificate_instance_0472 : OAI.SidorenkoCounterexample.ProofCertificate_0472 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16
  exact @certificate_proof_0472 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16

omit [Finite E] in
theorem certificate_proof_0473 (D : ℕ) (c : Fin 22 → ℕ) (h : Fin 33 → ℕ) (κ : Fin 6) :
    (∏ n : Fin 10, classStepBound ω D c h κ n.val)=
      (fullProfileConstant D*(Nat.card (SymplecticLagrangian ω):ℝ))^10*
        (Fintype.card K:ℝ)^(∑ n : Fin 10,
          (((h (classOldPair κ n)+1).choose 2:ℝ)-(faceNaturalCost D c h (classFace κ n.succ):ℝ))) := by
  have hq : 0<(Fintype.card K:ℝ) := by exact_mod_cast Fintype.card_pos (α:=K)
  simp only [classStepBound,dif_pos (Fin.isLt _),Fin.eta,Finset.prod_mul_distrib,
    Finset.prod_const,Finset.card_univ,Fintype.card_fin]
  rw [Real.rpow_sum_of_pos hq,mul_pow]
  rfl

private instance certificate_instance_0473 : OAI.SidorenkoCounterexample.ProofCertificate_0473 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10
  exact @certificate_proof_0473 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10

theorem certificate_proof_0474 (h2 : (2:K)≠0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
    (D : ℕ) (hD : 2*D=finrank K E) (c : Fin 22 → ℕ) (h : Fin 33 → ℕ) (hc : ∀ j, c j≤D)
    (κ : Fin 6) : (Nat.card {L : Fin 13 → SymplecticLagrangian ω // PointProfile ω c h L}:ℝ) ≤
      (fullProfileConstant D)^11*(Nat.card (SymplecticLagrangian ω):ℝ)^13*
        (Fintype.card K:ℝ)^(classExponent D c h κ) := by
  have hq : 0<(Fintype.card K:ℝ) := by exact_mod_cast Fintype.card_pos (α:=K)
  have hs := validSeq_card_bound 3 (classRootConstraint ω c h κ) (classStepConstraint ω c h κ)
    (classStepBound ω D c h κ) (classStepBound_nonneg ω D c h κ)
    (fun n x => classStep_card_bound ω h2 ha hω D hD c h hc κ n x.val) 10
  have hr := classRoot_card_bound ω h2 ha hω D hD c h hc κ
  have hi : (Nat.card {L : Fin 13 → SymplecticLagrangian ω // PointProfile ω c h L}:ℝ) ≤
      Nat.card (ValidSeq 3 (classRootConstraint ω c h κ) (classStepConstraint ω c h κ) 10) := by
    exact_mod_cast Nat.card_le_card_of_injective _ (pointProfile_class_injection ω c h κ).injective
  calc
    _ ≤ _ := hi.trans hs
    _ ≤ (fullProfileConstant D*(Nat.card (SymplecticLagrangian ω):ℝ)^3*
        (Fintype.card K:ℝ)^(-(faceNaturalCost D c h (classFace κ 0):ℝ)))*
        ∏ n : Fin 10,classStepBound ω D c h κ n.val :=
      mul_le_mul_of_nonneg_right hr (Finset.prod_nonneg fun n _ => classStepBound_nonneg ω D c h κ n.val)
    _ = _ := by
      rw [classStepBound_product]
      have he : -(faceNaturalCost D c h (classFace κ 0):ℝ)+
          (∑ n : Fin 10, (((h (classOldPair κ n)+1).choose 2:ℝ)-
            (faceNaturalCost D c h (classFace κ n.succ):ℝ)))=classExponent D c h κ := by
        unfold classExponent
        rw [Fin.sum_univ_succ (fun i : Fin 11 => (faceNaturalCost D c h (classFace κ i):ℝ)),Finset.sum_sub_distrib]
        ring
      rw [←he,Real.rpow_add hq]
      ring

private instance certificate_instance_0474 : OAI.SidorenkoCounterexample.ProofCertificate_0474 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16
  exact @certificate_proof_0474 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16

end ExposureProfile
theorem certificate_proof_0475 (f : Fin 22 → ℝ) :
    (∑ κ : Fin 6, ∑ n : Fin 11, f (classFace κ n))=3*∑ j, f j := by
  rw [←Fintype.sum_prod_type (fun p : Fin 6 × Fin 11 => f (classFace p.1 p.2))]
  rw [←Finset.sum_fiberwise Finset.univ (fun p : Fin 6 × Fin 11 => classFace p.1 p.2)]
  have he (j : Fin 22) : (∑ p ∈ Finset.univ.filter (fun p : Fin 6 × Fin 11 => classFace p.1 p.2=j),
      f (classFace p.1 p.2))=3*f j := by
    calc _ = ∑ _p ∈ Finset.univ.filter (fun p : Fin 6 × Fin 11 => classFace p.1 p.2=j), f j := by
            apply Finset.sum_congr rfl
            intro p hp
            rw [(Finset.mem_filter.mp hp).2]
         _ = _ := by rw [Finset.sum_const,classFace_occurs]; simp only [nsmul_eq_mul,Nat.cast_ofNat]
  simp_rw [he]
  rw [Finset.mul_sum]

private instance certificate_instance_0475 : OAI.SidorenkoCounterexample.ProofCertificate_0475 := by
  constructor
  intro q0
  exact @certificate_proof_0475 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 q0

theorem certificate_proof_0476 (f : Fin 33 → ℝ) :
    (∑ κ : Fin 6, ∑ n : Fin 10, f (classOldPair κ n))=∑ e, (3-(separationCount e:ℝ))*f e := by
  rw [←Fintype.sum_prod_type (fun p : Fin 6 × Fin 10 => f (classOldPair p.1 p.2))]
  rw [←Finset.sum_fiberwise Finset.univ (fun p : Fin 6 × Fin 10 => classOldPair p.1 p.2)]
  apply Finset.sum_congr rfl
  intro e _
  calc _ = ∑ _p ∈ Finset.univ.filter (fun p : Fin 6 × Fin 10 => classOldPair p.1 p.2=e), f e := by
          apply Finset.sum_congr rfl
          intro p hp
          rw [(Finset.mem_filter.mp hp).2]
       _ = _ := by rw [Finset.sum_const,classTree_occurs]; simp only [nsmul_eq_mul,Nat.cast_sub (separationCount_le e),Nat.cast_ofNat]

private instance certificate_instance_0476 : OAI.SidorenkoCounterexample.ProofCertificate_0476 := by
  constructor
  intro q0
  exact @certificate_proof_0476 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 q0

theorem certificate_proof_0477 (D : ℕ) (c : Fin 22 → ℕ) (h : Fin 33 → ℕ) :
    (∑ κ, classExponent D c h κ)= -6*profileCost D c h := by
  simp only [classExponent,Finset.sum_add_distrib,Finset.sum_neg_distrib,triangular_nat]
  rw [sum_class_faces (fun j => (faceNaturalCost D c h j:ℝ)),sum_class_old_pairs (fun e => triangular (h e))]
  unfold profileCost
  ring

private instance certificate_instance_0477 : OAI.SidorenkoCounterexample.ProofCertificate_0477 := by
  constructor
  intro q0 q1 q2
  exact @certificate_proof_0477 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 q0 q1 q2

section GlobalExposure
variable {K E : Type} [Field K] [AddCommGroup E] [Module K E] [Fintype K] [Finite E]
variable (ω : LinearMap.BilinForm K E)
theorem certificate_proof_0478 (h2 : (2:K)≠0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
    (D : ℕ) (hD : 2*D=finrank K E) (c : Fin 22 → ℕ) (h : Fin 33 → ℕ) (hc : ∀ j, c j≤D) :
    (Nat.card {L : Fin 13 → SymplecticLagrangian ω // PointProfile ω c h L}:ℝ) ≤
      (fullProfileConstant D)^11*(Nat.card (SymplecticLagrangian ω):ℝ)^13*
        (Fintype.card K:ℝ)^(-profileCost D c h) := by
  have hq : 0<(Fintype.card K:ℝ) := by exact_mod_cast Fintype.card_pos (α:=K)
  have hb := Finset.prod_le_prod (s:=Finset.univ) (f:=fun _κ : Fin 6 =>
      (Nat.card {L : Fin 13 → SymplecticLagrangian ω // PointProfile ω c h L}:ℝ))
    (fun _κ _ => Nat.cast_nonneg _) (fun κ _ => pointProfile_class_card_bound ω h2 ha hω D hD c h hc κ)
  simp only [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,Fintype.card_fin] at hb
  rw [←Real.rpow_sum_of_pos hq,sum_class_exponent] at hb
  have he : -6*profileCost D c h=(-profileCost D c h)*(6:ℕ) := by norm_num; ring
  rw [he,Real.rpow_mul_natCast hq.le] at hb
  have hC := fullProfileConstant_pos D
  apply (pow_le_pow_iff_left₀ (Nat.cast_nonneg _) (by positivity) (by norm_num : (6:ℕ)≠0)).mp
  simpa only [mul_pow] using hb

private instance certificate_instance_0478 : OAI.SidorenkoCounterexample.ProofCertificate_0478 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15
  exact @certificate_proof_0478 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15

end GlobalExposure
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open scoped BigOperators
section ZeroSequential
variable {A : Type} [Finite A]
theorem certificate_proof_0479
    (P : (n : ℕ) → (Fin n → A) → A → Prop) (B : ℕ → ℝ)
    (hB : ∀ n, 0≤B n) (hb : ∀ n (x : ZeroValidSeq P n), (Nat.card {a : A // P n x.val a}:ℝ) ≤ B n)
    (n : ℕ) : (Nat.card (ZeroValidSeq P n):ℝ) ≤
      ∏ i : Fin n, B i.val := by
  classical
  induction n with
  | zero =>
    rw [Fin.prod_univ_zero]
    norm_num [ZeroValidSeq,ZeroSeqValid,Nat.card_eq_fintype_card,Fintype.card_subtype]
  | succ n ih =>
    let := Fintype.ofFinite (ZeroValidSeq P n)
    rw [Nat.card_congr (zeroValidSeqSuccEquiv P n),Nat.card_sigma,Nat.cast_sum]
    calc
      _ ≤ ∑ _x : ZeroValidSeq P n, B n := Finset.sum_le_sum (fun x _ => hb n x)
      _ = (Nat.card (ZeroValidSeq P n):ℝ)*B n := by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Nat.card_eq_fintype_card]
      _ ≤ (∏ i : Fin n, B i.val)*B n := mul_le_mul_of_nonneg_right ih (hB n)
      _ = _ := by rw [Fin.prod_univ_castSucc]; simp only [Fin.val_castSucc,Fin.val_last]

private instance certificate_instance_0479 : OAI.SidorenkoCounterexample.ProofCertificate_0479 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6
  exact @certificate_proof_0479 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 q0 q1 q2 q3 q4 q5 q6

end ZeroSequential
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
open scoped BigOperators
section OrthogonalTuple
variable {K E : Type} [Field K] [AddCommGroup E] [Module K E]
variable (ω : LinearMap.BilinForm K E)
theorem certificate_proof_0480 (R : ℕ → ℕ → Prop) (n : ℕ)
    (x : ZeroValidSeq (OrthogonalStep ω R) n) : LinearIndependent K x.val := by
  cases n with
  | zero =>
    exact linearIndependent_empty_type
  | succ n =>
    have hx := x.property.2.1
    rwa [Fin.snoc_init_self] at hx

private instance certificate_instance_0480 : OAI.SidorenkoCounterexample.ProofCertificate_0480 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8
  exact @certificate_proof_0480 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 q0 q1 q2 q3 q4 q5 q6 q7 q8

theorem certificate_proof_0481 (R : ℕ → ℕ → Prop) (n : ℕ) (x : OrthogonalTuple ω R n) :
    ZeroSeqValid (OrthogonalStep ω R) n x.val := by
  induction n with
  | zero => trivial
  | succ n ih =>
    have hli : LinearIndependent K (Fin.init x.val) := x.property.1.comp Fin.castSucc (Fin.castSucc_injective n)
    have hrel : ∀ i j : Fin n, i.val<j.val → R i.val j.val → ω (Fin.init x.val i) (Fin.init x.val j)=0 := by
      intro i j hij hr
      exact x.property.2 i.castSucc j.castSucc hij hr
    refine ⟨ih ⟨Fin.init x.val,hli,hrel⟩,?_,?_⟩
    · simpa only [Fin.snoc_init_self] using x.property.1
    · intro i hir
      exact x.property.2 i.castSucc (Fin.last n) i.isLt (by simpa only [Fin.val_castSucc,Fin.val_last,Nat.zero_add] using hir)

private instance certificate_instance_0481 : OAI.SidorenkoCounterexample.ProofCertificate_0481 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8
  exact @certificate_proof_0481 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 q0 q1 q2 q3 q4 q5 q6 q7 q8

variable [Fintype K] [Finite E]
theorem certificate_proof_0482 (hω : ω.Nondegenerate) {n : ℕ} (x : Fin n → E)
    (hx : LinearIndependent K x) (s : Finset (Fin n)) :
    Nat.card {y : E // ∀ i∈s, ω (x i) y=0}=(Fintype.card K)^(finrank K E-s.card) := by
  classical
  let z : s → E := fun i => x i.val
  let S : Submodule K E := Submodule.span K (Set.range z)
  have hli : LinearIndependent K z := hx.comp (fun i : s => i.val) Subtype.val_injective
  have hdim : finrank K S=s.card := by rw [finrank_span_eq_card hli,Fintype.card_coe]
  have he : {y : E // ∀ i∈s, ω (x i) y=0} ≃ ω.orthogonal S :=
    Equiv.subtypeEquivRight (fun y => by
      constructor
      · intro hy
        rw [LinearMap.BilinForm.mem_orthogonal_iff]
        have hh : S ≤ LinearMap.ker (ω.flip y) := by
          apply Submodule.span_le.mpr
          rintro _ ⟨i,rfl⟩
          exact hy i.val i.property
        intro v hv
        exact hh hv
      · intro hy i hi
        exact hy (x i) (Submodule.subset_span ⟨⟨i,hi⟩,rfl⟩))
  rw [Nat.card_congr he,Module.natCard_eq_pow_finrank (K := K),Nat.card_eq_fintype_card,
    ω.finrank_orthogonal hω S,hdim]

private instance certificate_instance_0482 : OAI.SidorenkoCounterexample.ProofCertificate_0482 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12
  exact @certificate_proof_0482 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12

theorem certificate_proof_0483 (hω : ω.Nondegenerate) (R : ℕ → ℕ → Prop)
    (n : ℕ) (x : ZeroValidSeq (OrthogonalStep ω R) n) :
    (Nat.card {y : E // OrthogonalStep ω R n x.val y}:ℝ) ≤
      (Fintype.card K:ℝ)^(finrank K E-priorConstraintCount R n) := by
  classical
  let s : Finset (Fin n) := Finset.univ.filter fun i => R i.val n
  have he : s.card=priorConstraintCount R n := by
    rw [priorConstraintCount,Nat.card_eq_fintype_card,Fintype.card_subtype]
  have hi : Nat.card {y : E // OrthogonalStep ω R n x.val y} ≤ Nat.card {y : E // ∀ i∈s, ω (x.val i) y=0} :=
    Nat.card_le_card_of_injective (fun y => ⟨y.val,fun i hi => y.property.2 i (Finset.mem_filter.mp hi).2⟩)
      (by
        intro a b h
        apply Subtype.ext
        exact congrArg (fun z : {y : E // ∀ i∈s, ω (x.val i) y=0} => z.val) h)
  rw [independent_orthogonal_card ω hω x.val (orthogonalSeq_independent ω R n x),he] at hi
  exact_mod_cast hi

private instance certificate_instance_0483 : OAI.SidorenkoCounterexample.ProofCertificate_0483 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11
  exact @certificate_proof_0483 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11

theorem certificate_proof_0484 (hω : ω.Nondegenerate) (R : ℕ → ℕ → Prop) (n : ℕ) :
    (Nat.card (OrthogonalTuple ω R n):ℝ) ≤
      (Fintype.card K:ℝ)^(∑ i : Fin n, (finrank K E-priorConstraintCount R i.val)) := by
  classical
  have hs := zeroValidSeq_card_bound (OrthogonalStep ω R)
    (fun i => (Fintype.card K:ℝ)^(finrank K E-priorConstraintCount R i))
    (fun _ => by positivity) (orthogonalStep_card_bound ω hω R) n
  rw [Finset.prod_pow_eq_pow_sum] at hs
  have hh : (Nat.card (OrthogonalTuple ω R n):ℝ) ≤ Nat.card (ZeroValidSeq (OrthogonalStep ω R) n) := by
    exact_mod_cast Nat.card_le_card_of_injective _ (orthogonalTupleToSeq ω R n).injective
  exact hh.trans hs

private instance certificate_instance_0484 : OAI.SidorenkoCounterexample.ProofCertificate_0484 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10
  exact @certificate_proof_0484 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10

end OrthogonalTuple
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
open scoped BigOperators
theorem certificate_proof_0485 (R : ℕ → ℕ → Prop) (n : ℕ) :
    (∑ i : Fin n, priorConstraintCount R i.val)=constraintPairCount R n := by
  classical
  apply Finset.sum_congr rfl
  intro j _
  let e : {i : Fin j.val // R i.val j.val} ≃ {i : Fin n // i.val<j.val ∧ R i.val j.val} :=
    { toFun := fun i => ⟨⟨i.val.val,lt_trans (by simpa only [Nat.zero_add] using i.val.isLt) j.isLt⟩,by simpa only [Nat.zero_add] using i.val.isLt,i.property⟩
      invFun := fun i => ⟨⟨i.val.val,by simpa only [Nat.zero_add] using i.property.1⟩,i.property.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [priorConstraintCount,Nat.card_congr e,Nat.card_eq_fintype_card,Fintype.card_subtype]
  simp only [Finset.sum_boole,Nat.cast_id]

private instance certificate_instance_0485 : OAI.SidorenkoCounterexample.ProofCertificate_0485 := by
  constructor
  intro q0 q1
  exact @certificate_proof_0485 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 q0 q1

section TupleRpow
variable {K E : Type} [Field K] [AddCommGroup E] [Module K E] [Fintype K] [Finite E]
variable (ω : LinearMap.BilinForm K E)
theorem certificate_proof_0486 (hω : ω.Nondegenerate) (R : ℕ → ℕ → Prop) (n : ℕ)
    (hn : n≤finrank K E) :
    (Nat.card {x : Fin n → E // LinearIndependent K x ∧
      ∀ i j : Fin n, i.val<j.val → R i.val j.val → ω (x i) (x j)=0}:ℝ) ≤
      (Fintype.card K:ℝ)^((n:ℝ)*finrank K E-constraintPairCount R n) := by
  classical
  have hb := orthogonalTuple_card_bound ω hω R n
  have hle (i : Fin n) : priorConstraintCount R i.val≤finrank K E := by
    have hh : Nat.card {j : Fin i.val // R j.val i.val} ≤ Nat.card (Fin i.val) :=
      Nat.card_le_card_of_injective _ Subtype.val_injective
    simp only [Nat.card_eq_fintype_card,Fintype.card_fin] at hh
    simpa only [priorConstraintCount,Nat.card_eq_fintype_card] using hh.trans (i.isLt.le.trans hn)
  have he : ((∑ i : Fin n, (finrank K E-priorConstraintCount R i.val):ℕ):ℝ)=
      (n:ℝ)*finrank K E-constraintPairCount R n := by
    rw [Nat.cast_sum]
    simp only [Nat.cast_sub (hle _),Finset.sum_sub_distrib,Finset.sum_const,Finset.card_univ,
      Fintype.card_fin,nsmul_eq_mul,←Nat.cast_sum,sum_priorConstraintCount]
  rw [←Real.rpow_natCast,he] at hb
  unfold OrthogonalTuple at hb
  exact hb

private instance certificate_instance_0486 : OAI.SidorenkoCounterexample.ProofCertificate_0486 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11
  exact @certificate_proof_0486 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11

end TupleRpow
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
open scoped BigOperators
theorem certificate_proof_0487 {A : Type} [Fintype A] (P : A → Prop) [DecidablePred P] :
    Nat.card {a : A // P a}=∑ a : A, if P a then (1:ℕ) else 0 := by
  classical
  simp only [Nat.card_eq_fintype_card,Fintype.card_subtype,Finset.sum_boole,Nat.cast_id]

private instance certificate_instance_0487 : OAI.SidorenkoCounterexample.ProofCertificate_0487 := by
  constructor
  intro q0 q1 q2 q3
  exact @certificate_proof_0487 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 q0 q1 q2 q3

theorem certificate_proof_0488 (R : ℕ → ℕ → Prop) (n : ℕ)
    (hR : ∀ i j, R i j → R j i) :
    2*constraintPairCount R n = Nat.card {p : Fin n × Fin n // p.1≠p.2 ∧ R p.1.val p.2.val} := by
  classical
  rw [nat_card_subtype_sum,Fintype.sum_prod_type]
  have he (i j : Fin n) :
      (if i≠j ∧ R i.val j.val then (1:ℕ) else 0)=
      (if i.val<j.val ∧ R i.val j.val then 1 else 0)+
      (if j.val < i.val ∧ R j.val i.val then 1 else 0) := by
    have hr : R i.val j.val ↔ R j.val i.val := ⟨hR _ _,hR _ _⟩
    rcases lt_trichotomy i.val j.val with h|h|h
    · have hne : i≠j := fun hh => by subst j; exact (lt_irrefl _ h)
      simp [hne,h,not_lt.mpr h.le]
    · have hij : i=j := Fin.ext h
      simp [hij]
    · have hne : i≠j := fun hh => by subst j; exact (lt_irrefl _ h)
      simp [hne,h,not_lt.mpr h.le,←hr]
  simp_rw [he,Finset.sum_add_distrib]
  rw [Finset.sum_comm (f:=fun i j : Fin n => if i.val<j.val ∧ R i.val j.val then (1:ℕ) else 0)]
  unfold constraintPairCount
  omega

private instance certificate_instance_0488 : OAI.SidorenkoCounterexample.ProofCertificate_0488 := by
  constructor
  intro q0 q1 q2
  exact @certificate_proof_0488 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 q0 q1 q2

section AbstractTuple
variable {K E A : Type} [Field K] [AddCommGroup E] [Module K E] [Fintype K] [Finite E] [Fintype A]
variable (ω : LinearMap.BilinForm K E)
theorem certificate_proof_0489 (R : A → A → Prop) (hR : ∀ a b, R a b → R b a)
    (e : Fin (Fintype.card A) ≃ A) (i j : ℕ) :
    enumeratedRelation R e i j → enumeratedRelation R e j i := by
  rintro ⟨hi,hj,h⟩
  exact ⟨hj,hi,hR _ _ h⟩

private instance certificate_instance_0489 : OAI.SidorenkoCounterexample.ProofCertificate_0489 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7
  exact @certificate_proof_0489 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 q0 q1 q2 q3 q4 q5 q6 q7

theorem certificate_proof_0490 (hω : ω.Nondegenerate) (R : A → A → Prop)
    (hR : ∀ a b, R a b → R b a) (hn : Fintype.card A≤finrank K E) :
    (Nat.card (ConstrainedTuple ω R):ℝ) ≤
      (Fintype.card K:ℝ)^((Fintype.card A:ℝ)*finrank K E-
        (Nat.card {p : A×A // p.1≠p.2 ∧ R p.1 p.2}:ℝ)/2) := by
  classical
  let e : Fin (Fintype.card A) ≃ A := (Fintype.equivFin A).symm
  let Q := enumeratedRelation R e
  have hb := orthogonalTuple_card_rpow ω hω Q (Fintype.card A) hn
  let f : ConstrainedTuple ω R →
      {x : Fin (Fintype.card A) → E // LinearIndependent K x ∧ ∀ i j, i.val<j.val → Q i.val j.val → ω (x i) (x j)=0} :=
    fun x => ⟨fun i=>x.val (e i),x.property.1.comp e e.injective,by
      intro i j _ hij
      obtain ⟨hi,hj,h⟩ := hij
      exact x.property.2 _ _ h⟩
  have hf : Function.Injective f := by
    intro x y h
    apply Subtype.ext
    funext a
    have hh := congrArg (fun z => z.val (e.symm a)) h
    simpa only [f,Equiv.apply_symm_apply] using hh
  have hc := Nat.card_le_card_of_injective f hf
  have he : {p : Fin (Fintype.card A) × Fin (Fintype.card A) // p.1≠p.2 ∧ Q p.1.val p.2.val} ≃
      {p : A×A // p.1≠p.2 ∧ R p.1 p.2} :=
    (e.prodCongr e).subtypeEquiv (by
      intro p
      change (p.1≠p.2 ∧ enumeratedRelation R e p.1.val p.2.val) ↔ (e p.1≠e p.2 ∧ R (e p.1) (e p.2))
      simp only [e.injective.ne_iff,enumeratedRelation]
      constructor
      · rintro ⟨hne,hi,hj,h⟩
        exact ⟨hne,h⟩
      · rintro ⟨hne,h⟩
        exact ⟨hne,p.1.isLt,p.2.isLt,h⟩)
  have hd := double_constraintPairCount Q (Fintype.card A) (enumeratedRelation_symm R hR e)
  rw [Nat.card_congr he] at hd
  have hd' : (constraintPairCount Q (Fintype.card A):ℝ)=
      (Nat.card {p : A×A // p.1≠p.2 ∧ R p.1 p.2}:ℝ)/2 := by
    have hdc : (2:ℝ)*constraintPairCount Q (Fintype.card A)=(Nat.card {p : A×A // p.1≠p.2 ∧ R p.1 p.2}:ℝ) := by exact_mod_cast hd
    linarith
  rw [hd'] at hb
  exact (by exact_mod_cast hc : (Nat.card (ConstrainedTuple ω R):ℝ)≤_).trans hb

private instance certificate_instance_0490 : OAI.SidorenkoCounterexample.ProofCertificate_0490 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13
  exact @certificate_proof_0490 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13

end AbstractTuple
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
open scoped BigOperators
section ResidualCount
variable {K E : Type} [Field K] [AddCommGroup E] [Module K E] [Fintype K] [Finite E]
theorem certificate_proof_0491 (k : ℕ) (hE : finrank K E=k) :
    (Fintype.card K:ℝ)^(k*k) ≤ 2^k*(Nat.card (IndependentTuple K E k):ℝ) := by
  classical
  have hq : (2:ℝ)≤Fintype.card K := by exact_mod_cast (Fintype.one_lt_card (α:=K))
  have hq0 : (0:ℝ)<Fintype.card K := by linarith
  have hle (i : Fin k) : Fintype.card K ^ i.val ≤ Fintype.card K ^ k :=
    Nat.pow_le_pow_right Fintype.card_pos i.isLt.le
  have hp (i : Fin k) : (Fintype.card K:ℝ)^k ≤
      2*((Fintype.card K:ℝ)^k-(Fintype.card K:ℝ)^i.val) := by
    have h₁ : 2*(Fintype.card K:ℝ)^i.val ≤ (Fintype.card K:ℝ)^(i.val+1) := by
      rw [pow_succ]
      nlinarith [pow_nonneg hq0.le i.val]
    have h₂ : (Fintype.card K:ℝ)^(i.val+1) ≤ (Fintype.card K:ℝ)^k :=
      pow_le_pow_right₀ (by linarith) i.isLt
    linarith
  have h := Finset.prod_le_prod (s:=Finset.univ) (fun _i : Fin k => fun _ => pow_nonneg hq0.le k)
    (fun i _ => hp i)
  rw [IndependentTuple,card_linearIndependent (by omega),hE,Nat.cast_prod]
  simp only [Nat.cast_sub (hle _),Nat.cast_pow]
  simpa only [Finset.prod_const,Finset.card_univ,Fintype.card_fin,←pow_mul,Finset.prod_mul_distrib] using h

private instance certificate_instance_0491 : OAI.SidorenkoCounterexample.ProofCertificate_0491 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8
  exact @certificate_proof_0491 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 q0 q1 q2 q3 q4 q5 q6 q7 q8

variable (ω : LinearMap.BilinForm K E)
theorem certificate_proof_0492 (h2 : (2:K)≠0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
    (D : ℕ) (hD : 2*D=finrank K E) (S : Submodule K E) :
    (Nat.card {L : SymplecticLagrangian ω // S≤L.val}:ℝ) ≤
      lagrangianConstant D * (Nat.card (SymplecticLagrangian ω):ℝ) *
        (Fintype.card K:ℝ)^(-(D:ℝ)*finrank K S+(finrank K S:ℝ)*(finrank K S-1)/2) := by
  classical
  have hq : 0<(Fintype.card K:ℝ) := by exact_mod_cast Fintype.card_pos (α:=K)
  by_cases his : S≤ω.orthogonal S
  · have hs := isotropic_finrank_le_half ω hω D hD S his
    have h := (containingLagrangian_card_bounds ω h2 ha hω D hD S his).2
    have hl := (symplecticLagrangian_card_bounds ω h2 ha hω D hD).1
    have hC := lagrangianConstant_mono (Nat.sub_le D (finrank K S))
    have he : (((D-finrank K S+1).choose 2:ℕ):ℝ) =
        ((D+1).choose 2:ℕ) + (-(D:ℝ)*finrank K S+(finrank K S:ℝ)*(finrank K S-1)/2) := by
      rw [Nat.cast_choose_two,Nat.cast_choose_two]
      simp only [Nat.cast_add,Nat.cast_one,Nat.cast_sub hs]
      ring
    rw [←Real.rpow_natCast,he,Real.rpow_add hq] at h
    calc
      _ ≤ _ := h
      _ ≤ _ := by
        rw [Real.rpow_natCast,←mul_assoc]
        exact mul_le_mul_of_nonneg_right (mul_le_mul hC hl (by positivity) (lagrangianConstant_pos D).le) (Real.rpow_nonneg hq.le _)
  · have hz : Nat.card {L : SymplecticLagrangian ω // S≤L.val}=0 := by
      let : IsEmpty {L : SymplecticLagrangian ω // S≤L.val} := ⟨fun L => his (by
        calc
          S ≤ L.val.val := L.property
          _ = ω.orthogonal L.val.val := L.val.property.symm
          _ ≤ ω.orthogonal S := ω.orthogonal_le L.property)⟩
      exact Nat.card_eq_zero.mpr (Or.inl inferInstance)
    rw [hz,Nat.cast_zero]
    exact mul_nonneg (mul_nonneg (lagrangianConstant_pos D).le (Nat.cast_nonneg _)) (Real.rpow_nonneg hq.le _)

private instance certificate_instance_0492 : OAI.SidorenkoCounterexample.ProofCertificate_0492 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13
  exact @certificate_proof_0492 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13

end ResidualCount
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
open scoped BigOperators
section FamilySpan
variable {K E I : Type} [Field K] [AddCommGroup E] [Module K E] [Fintype I]
variable [Finite E]
omit [Fintype I] [Finite E] in
theorem certificate_proof_0493 (h : I → ℕ) (k : ℕ) :
    Function.Injective (familySpanCoding (K:=K) (E:=E) h k) := by
  let recover : (Σ W : DimSubspace K E k, (i : I) → DimSubspace K W.val (h i)) → (I → Submodule K E) :=
    fun x i => (x.2 i).val.map x.1.val.subtype
  have he (A : FamilySpanStratum (K:=K) (E:=E) h k) : recover (familySpanCoding h k A)=fun i => (A.val i).val := by
    funext i
    change ((A.val i).val.comap (⨆ j, (A.val j).val).subtype).map (⨆ j, (A.val j).val).subtype = _
    rw [Submodule.map_comap_subtype]
    exact inf_eq_right.mpr (le_iSup (fun j => (A.val j).val) i)
  intro A B hAB
  have hh := congrArg recover hAB
  rw [he,he] at hh
  apply Subtype.ext
  funext i
  exact Subtype.ext (congrFun hh i)

private instance certificate_instance_0493 : OAI.SidorenkoCounterexample.ProofCertificate_0493 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7
  exact @certificate_proof_0493 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 q0 q1 q2 q3 q4 q5 q6 q7

variable [Fintype K]
theorem certificate_proof_0494 (h : I → ℕ) (k : ℕ) (hk : k≤finrank K E) (hh : ∀ i, h i≤k) :
    (Nat.card (FamilySpanStratum (K:=K) (E:=E) h k):ℝ) ≤
      2^(k+∑ i, h i)*(Fintype.card K:ℝ)^(k*(finrank K E-k)+∑ i, h i*(k-h i)) := by
  classical
  let := Fintype.ofFinite (DimSubspace K E k)
  have hf (W : DimSubspace K E k) :
      (Nat.card ((i : I) → DimSubspace K W.val (h i)):ℝ) ≤
      (2:ℝ)^(∑ i, h i)*(Fintype.card K:ℝ)^(∑ i, h i*(k-h i)) := by
    rw [Nat.card_pi,Nat.cast_prod]
    have hh' (i : I) := subspace_count_upper (K:=K) (V:=W.val) (h i) (by rw [W.property];exact hh i)
    simp only [W.property] at hh'
    have hp := Finset.prod_le_prod (s:=Finset.univ) (fun i _ => Nat.cast_nonneg (Nat.card (DimSubspace K W.val (h i)))) (fun i _ => hh' i)
    simpa only [Finset.prod_mul_distrib,Finset.prod_pow_eq_pow_sum] using hp
  have hs := real_card_sigma_le (B:=DimSubspace K E k) _ hf
  have hi : (Nat.card (FamilySpanStratum (K:=K) (E:=E) h k):ℝ) ≤
      Nat.card (Σ W : DimSubspace K E k, (i : I) → DimSubspace K W.val (h i)) := by
    exact_mod_cast Nat.card_le_card_of_injective _ (familySpanCoding_injective (K:=K) (E:=E) h k)
  calc
    _ ≤ _ := hi.trans hs
    _ ≤ (2^k*(Fintype.card K:ℝ)^(k*(finrank K E-k))) *
        (2^(∑ i, h i)*(Fintype.card K:ℝ)^(∑ i, h i*(k-h i))) :=
      mul_le_mul_of_nonneg_right (subspace_count_upper k hk) (by positivity)
    _ = _ := by rw [pow_add,pow_add];ring

private instance certificate_instance_0494 : OAI.SidorenkoCounterexample.ProofCertificate_0494 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12
  exact @certificate_proof_0494 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12

end FamilySpan
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
open scoped BigOperators
section DirectFamilies
variable {K E I : Type} [Field K] [AddCommGroup E] [Module K E] [Fintype I]
variable [Finite E]
variable (ω : LinearMap.BilinForm K E)
omit [Fintype I] in
theorem certificate_proof_0495 {h : I → ℕ} {R : I → I → Prop}
    (A : DirectFamily ω h R) (b : FamilyBases ω A) :
    LinearIndependent K (fun x : Σ i, Fin (h i) => (((b x.1).val x.2 : (A.val x.1).val):E)) := by
  classical
  apply linearIndependent_iUnion_finite (f := fun (i : I) (a : Fin (h i)) => ((b i).val a:E))
  · intro i
    exact (b i).property.map' (A.val i).val.subtype (Submodule.ker_subtype _)
  · intro i t _ hi
    have he (j : I) : Submodule.span K (Set.range (fun a => (((b j).val a : (A.val j).val):E)))=(A.val j).val :=
      tuple_spans (h j) (A.val j) (b j)
    simp_rw [he]
    exact A.property.1.disjoint_biSup hi

private instance certificate_instance_0495 : OAI.SidorenkoCounterexample.ProofCertificate_0495 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11
  exact @certificate_proof_0495 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11

variable [Fintype K]
end DirectFamilies
end SidorenkoCounterexample
end OAI

theorem solution : OAI.SidorenkoCounterexample.ProofCertificate_0466 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0467 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0468 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0469 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0470 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0471 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0472 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0473 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0474 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0475 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0476 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0477 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0478 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0479 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0480 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0481 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0482 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0483 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0484 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0485 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0486 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0487 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0488 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0489 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0490 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0491 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0492 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0493 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0494 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0495 := by
  exact ⟨inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance⟩
end

