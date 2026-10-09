-- Prove2me | solution 1 for OAI.SidorenkoCounterexample.finite_geometry_batch_27
-- status  : ACCEPTED   (prove)
-- author  : @abcdefg
-- created : 2026-10-09T06:35:05.819401+00:00
-- url     : https://prove2.me/submissions/87e9bca7-cfb1-45fc-bb89-d8c2b829f300

import Definitions.Def_SidorenkoCertificateBundleB
set_option linter.unusedVariables false
section
variable [p0 : OAI.SidorenkoCounterexample.ProofCertificate_0006]
  [p1 : OAI.SidorenkoCounterexample.ProofCertificate_0020]
  [p2 : OAI.SidorenkoCounterexample.ProofCertificate_0030]
  [p3 : OAI.SidorenkoCounterexample.ProofCertificate_0069]
  [p4 : OAI.SidorenkoCounterexample.ProofCertificate_0640]
  [p5 : OAI.SidorenkoCounterexample.ProofCertificate_0654]
  [p6 : OAI.SidorenkoCounterexample.ProofCertificate_0655]
  [p7 : OAI.SidorenkoCounterexample.ProofCertificate_0656]
  [p8 : OAI.SidorenkoCounterexample.ProofCertificate_0659]
  [p9 : OAI.SidorenkoCounterexample.ProofCertificate_0661]
  [p10 : OAI.SidorenkoCounterexample.ProofCertificate_0663]
  [p11 : OAI.SidorenkoCounterexample.ProofCertificate_0664]
  [p12 : OAI.SidorenkoCounterexample.ProofCertificate_0683]
  [p13 : OAI.SidorenkoCounterexample.ProofCertificate_0718]
  [p14 : OAI.SidorenkoCounterexample.ProofCertificate_0719]
  [p15 : OAI.SidorenkoCounterexample.ProofCertificate_0724]
  [p16 : OAI.SidorenkoCounterexample.ProofCertificate_0725]
  [p17 : OAI.SidorenkoCounterexample.ProofCertificate_0726]
  [p18 : OAI.SidorenkoCounterexample.ProofCertificate_0727]
  [p19 : OAI.SidorenkoCounterexample.ProofCertificate_0728]
  [p20 : OAI.SidorenkoCounterexample.ProofCertificate_0730]
  [p21 : OAI.SidorenkoCounterexample.ProofCertificate_0731]
  [p22 : OAI.SidorenkoCounterexample.ProofCertificate_0732]
  [p23 : OAI.SidorenkoCounterexample.ProofCertificate_0733]
  [p24 : OAI.SidorenkoCounterexample.ProofCertificate_0736]
  [p25 : OAI.SidorenkoCounterexample.ProofCertificate_0739]
  [p26 : OAI.SidorenkoCounterexample.ProofCertificate_0745]
  [p27 : OAI.SidorenkoCounterexample.ProofCertificate_0754]
  [p28 : OAI.SidorenkoCounterexample.ProofCertificate_0767]
  [p29 : OAI.SidorenkoCounterexample.ProofCertificate_0770]
  [p30 : OAI.SidorenkoCounterexample.ProofCertificate_0773]
  [p31 : OAI.SidorenkoCounterexample.ProofCertificate_0775]
  [p32 : OAI.SidorenkoCounterexample.ProofCertificate_0776]
  [p33 : OAI.SidorenkoCounterexample.ProofCertificate_0784]
  [p34 : OAI.SidorenkoCounterexample.ProofCertificate_0786]
  [p35 : OAI.SidorenkoCounterexample.ProofCertificate_0788]
  [p36 : OAI.SidorenkoCounterexample.ProofCertificate_0789]
  [p37 : OAI.SidorenkoCounterexample.ProofCertificate_0791]
  [p38 : OAI.SidorenkoCounterexample.ProofCertificate_0793]
  [p39 : OAI.SidorenkoCounterexample.ProofCertificate_0796]
  [p40 : OAI.SidorenkoCounterexample.ProofCertificate_0797]
  [p41 : OAI.SidorenkoCounterexample.ProofCertificate_0799]
  [p42 : OAI.SidorenkoCounterexample.ProofCertificate_0800]
  [p43 : OAI.SidorenkoCounterexample.ProofCertificate_0801]
  [p44 : OAI.SidorenkoCounterexample.ProofCertificate_0802]
  [p45 : OAI.SidorenkoCounterexample.ProofCertificate_0803]
  [p46 : OAI.SidorenkoCounterexample.ProofCertificate_0804]
include p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 p45 p46

namespace OAI
section
namespace SidorenkoCounterexample
open Module LinearMap
open scoped Matrix BigOperators
section Count
variable {I K V : Type} [Fintype I] [Field K] [Fintype K] [DecidableEq K]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]
theorem certificate_proof_0805 (f : I → ℝ) :
    (Fintype.card I : ℝ)*uniformMean f=∑ i, f i := by
  by_cases h : Fintype.card I=0
  · have := Fintype.card_eq_zero_iff.mp h
    simp [uniformMean]
  · unfold uniformMean
    field_simp

private instance certificate_instance_0805 : OAI.SidorenkoCounterexample.ProofCertificate_0805 := by
  constructor
  intro q0 q1 q2
  exact @certificate_proof_0805 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 p45 p46 q0 q1 q2

theorem certificate_proof_0806 (U : I → Submodule K V) (Q : SymForm K V) (ξ : ℤ) :
    (Nat.card {i : I // (Q.val.restrict (U i)).Nondegenerate ∧
      discriminantSign (Q.val.restrict (U i)) (Q.property.restrict (U i))=ξ} : ℝ) =
    (Fintype.card I : ℝ)*uniformMean (fun i => formSignIndicator ξ (symFormPull (U i).subtype Q)) := by
  classical
  rw [uniformMean_mul_card,Nat.card_eq_fintype_card,Fintype.card_subtype,←Finset.sum_boole]
  apply Finset.sum_congr rfl
  intro i _
  change (if (Q.val.restrict (U i)).Nondegenerate ∧
    discriminantSign (Q.val.restrict (U i)) (Q.property.restrict (U i))=ξ then 1 else 0 : ℝ) =
    if (Q.val.restrict (U i)).Nondegenerate then
      if discriminantSign (Q.val.restrict (U i)) (Q.property.restrict (U i))=ξ then 1 else 0 else 0
  split_ifs <;> simp_all

private instance certificate_instance_0806 : OAI.SidorenkoCounterexample.ProofCertificate_0806 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12
  exact @certificate_proof_0806 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 p45 p46 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12

end Count
section Identities
variable {K : Type} [Field K] [Fintype K] [DecidableEq K] {D r : ℕ}
theorem certificate_proof_0807 (hd : D=2*r) (B : SymMatrix K D) (hB : B.val.det≠0)
    (ξ ζ : ℤ) (hm : quadraticChar K B.val.det=quadraticChar K ((-1 : K)^r)*ξ*ζ) :
    (Nat.card {A : SymMatrix K D // A ∈ signedLayer K D r ξ ∧ A-B ∈ signedLayer K D r ζ} : ℝ) =
    (Nat.card (DimSubspace K (Fin D → K) r) : ℝ) *
      pairRestrictionFraction (⟨B.val⁻¹,B.property.inv⟩ : SymMatrix K D) r ξ := by
  classical
  let := Fintype.ofFinite (DimSubspace K (Fin D → K) r)
  have hn : B.val⁻¹.det≠0 := by simpa [Matrix.det_nonsing_inv] using inv_ne_zero hB
  rw [Nat.card_congr ((pairSignedCenterEquiv hd B hB ξ ζ hm).trans
    (signedProjectorSubspaceEquiv B.val⁻¹ B.property.inv hn r ξ))]
  exact (restrictionSign_count (fun U : DimSubspace K (Fin D → K) r => U.val)
    (matrixFormEquiv D ⟨B.val⁻¹,B.property.inv⟩) ξ).trans (by
      rw [Nat.card_eq_fintype_card]; rfl)

private instance certificate_instance_0807 : OAI.SidorenkoCounterexample.ProofCertificate_0807 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11
  exact @certificate_proof_0807 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 p45 p46 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11

theorem certificate_proof_0808 (hd : D=2*r) (B C : SymMatrix K D)
    (hB : B.val.det≠0) (hC : C.val.det≠0) (ξ ζ θ : ℤ)
    (hmB : quadraticChar K B.val.det=quadraticChar K ((-1 : K)^r)*ξ*ζ)
    (hmC : quadraticChar K C.val.det=quadraticChar K ((-1 : K)^r)*ξ*θ) :
    (Nat.card {A : SymMatrix K D // A ∈ signedLayer K D r ξ ∧ A-B ∈ signedLayer K D r ζ ∧
      A-C ∈ signedLayer K D r θ} : ℝ) =
    (Nat.card {U : DimSubspace K (Fin D → K) r //
      (B.val⁻¹-C.val⁻¹).toBilin'.restrict U.val=0} : ℝ) *
      isotropicRestrictionFraction (⟨B.val⁻¹,B.property.inv⟩ : SymMatrix K D)
        (B.val⁻¹-C.val⁻¹).toBilin' r ξ := by
  classical
  let := Fintype.ofFinite {U : DimSubspace K (Fin D → K) r //
    (B.val⁻¹-C.val⁻¹).toBilin'.restrict U.val=0}
  have hn : B.val⁻¹.det≠0 := by simpa [Matrix.det_nonsing_inv] using inv_ne_zero hB
  rw [Nat.card_congr ((tripleSignedCenterEquiv hd B C hB hC ξ ζ θ hmB hmC).trans
    (signedProjectorIsotropicEquiv B.val⁻¹ B.property.inv hn r ξ _))]
  exact (restrictionSign_count (fun U : {U : DimSubspace K (Fin D → K) r //
    (B.val⁻¹-C.val⁻¹).toBilin'.restrict U.val=0} => U.val.val)
    (matrixFormEquiv D ⟨B.val⁻¹,B.property.inv⟩) ξ).trans (by
      rw [Nat.card_eq_fintype_card]; rfl)

private instance certificate_instance_0808 : OAI.SidorenkoCounterexample.ProofCertificate_0808 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15
  exact @certificate_proof_0808 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 p45 p46 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15

end Identities
end SidorenkoCounterexample
end
section
namespace SidorenkoCounterexample
open Module Filter
open scoped BigOperators
section Coeff
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
theorem certificate_proof_0809 (r : ℕ) :
    r*r+2*((r+1).choose 2)=(2*r+1).choose 2 := by
  have h := triangular_nat_add r r
  have he : r+r+1=2*r+1 := by omega
  rw [he] at h
  omega

private instance certificate_instance_0809 : OAI.SidorenkoCounterexample.ProofCertificate_0809 := by
  constructor
  intro q0
  exact @certificate_proof_0809 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 p45 p46 q0

theorem certificate_proof_0810 (r : ℕ) :
    r.choose 2+3*((r+1).choose 2)=(2*r+1).choose 2 := by
  have h : (r.choose 2 : ℚ)+3*((r+1).choose 2 : ℚ)=((2*r+1).choose 2 : ℚ) := by
    simp only [Nat.cast_choose_two,Nat.cast_add,Nat.cast_mul,Nat.cast_one,Nat.cast_ofNat]
    ring
  exact_mod_cast h

private instance certificate_instance_0810 : OAI.SidorenkoCounterexample.ProofCertificate_0810 := by
  constructor
  intro q0
  exact @certificate_proof_0810 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 p45 p46 q0

theorem certificate_proof_0811 (r : ℕ) (ξ ζ : ℤ) :
    pairCoefficient (K := K) r ξ ζ =
      grassmannFactor (2*r) r (Fintype.card K) /
        ((layerMass K (2*r) r ξ * (Fintype.card K : ℝ)^((r+1).choose 2)) *
          (layerMass K (2*r) r ζ * (Fintype.card K : ℝ)^((r+1).choose 2))) := by
  unfold pairCoefficient
  rw [subspace_count_normalized r (by simp; omega),←Nat.card_eq_fintype_card (α := SymMatrix K (2*r)),symMatrix_card]
  simp only [Module.finrank_fin_fun,show 2*r-r=r by omega,Nat.cast_pow]
  rw [←pair_exponent_cancel,pow_add,pow_mul]
  have hq : (Fintype.card K : ℝ)≠0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  field_simp
  ring

private instance certificate_instance_0811 : OAI.SidorenkoCounterexample.ProofCertificate_0811 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6
  exact @certificate_proof_0811 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 p45 p46 q0 q1 q2 q3 q4 q5 q6

theorem certificate_proof_0812 (hK : ringChar K≠2) (r : ℕ) (ξ ζ θ : ℤ) :
    tripleCoefficient (K := K) r ξ ζ θ =
      orthogonalFactor r (Fintype.card K) /
        ((layerMass K (2*r) r ξ * (Fintype.card K : ℝ)^((r+1).choose 2)) *
          (layerMass K (2*r) r ζ * (Fintype.card K : ℝ)^((r+1).choose 2)) *
          (layerMass K (2*r) r θ * (Fintype.card K : ℝ)^((r+1).choose 2))) := by
  have he := maxOrthogonal_normalized (K := K) hK r
  unfold tripleCoefficient
  rw [←he,←Nat.card_eq_fintype_card (α := SymMatrix K (2*r)),symMatrix_card,Nat.cast_pow,
    ←triple_exponent_cancel,pow_add,pow_mul]
  have hq : (Fintype.card K : ℝ)≠0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  field_simp
  ring

private instance certificate_instance_0812 : OAI.SidorenkoCounterexample.ProofCertificate_0812 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8
  exact @certificate_proof_0812 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 p45 p46 q0 q1 q2 q3 q4 q5 q6 q7 q8

theorem certificate_proof_0813 (r : ℕ) (ξ ζ : ℤ) : 0≤pairCoefficient (K := K) r ξ ζ := by
  unfold pairCoefficient layerMass
  positivity

private instance certificate_instance_0813 : OAI.SidorenkoCounterexample.ProofCertificate_0813 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6
  exact @certificate_proof_0813 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 p45 p46 q0 q1 q2 q3 q4 q5 q6

theorem certificate_proof_0814 (r : ℕ) (ξ ζ θ : ℤ) : 0≤tripleCoefficient (K := K) r ξ ζ θ := by
  unfold tripleCoefficient layerMass
  positivity

private instance certificate_instance_0814 : OAI.SidorenkoCounterexample.ProofCertificate_0814 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7
  exact @certificate_proof_0814 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 p45 p46 q0 q1 q2 q3 q4 q5 q6 q7

end Coeff
theorem certificate_proof_0815 (r : ℕ) (hr : 0<r) {ξ ζ : ℤ}
    (hξ : ξ=1 ∨ ξ= -1) (hζ : ζ=1 ∨ ζ= -1) :
    Tendsto (fun q : OddPrime => pairCoefficient (K := ZMod q.val) r ξ ζ)
      primeInfinity (nhds 4) := by
  have hx := layerMass_tendsto (2*r) r hr (by omega) hξ
  have hz := layerMass_tendsto (2*r) r hr (by omega) hζ
  have hf := (grassmannFactor_tendsto (2*r) r (by omega)).comp primeInfinity_real_tendsto
  have h := hf.div (hx.mul hz) (by norm_num)
  simp only [show 2*r-r=r by omega,Function.comp_def] at h
  norm_num only at h
  simp_rw [pairCoefficient_normalized,ZMod.card]
  convert h using 1 <;> rfl

private instance certificate_instance_0815 : OAI.SidorenkoCounterexample.ProofCertificate_0815 := by
  constructor
  intro q0 q1 q2 q3 q4 q5
  exact @certificate_proof_0815 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 p45 p46 q0 q1 q2 q3 q4 q5

theorem certificate_proof_0816 (r : ℕ) (hr : 0<r) {ξ ζ θ : ℤ}
    (hξ : ξ=1 ∨ ξ= -1) (hζ : ζ=1 ∨ ζ= -1) (hθ : θ=1 ∨ θ= -1) :
    Tendsto (fun q : OddPrime => tripleCoefficient (K := ZMod q.val) r ξ ζ θ)
      primeInfinity (nhds 16) := by
  have hx := layerMass_tendsto (2*r) r hr (by omega) hξ
  have hz := layerMass_tendsto (2*r) r hr (by omega) hζ
  have ht := layerMass_tendsto (2*r) r hr (by omega) hθ
  have hf := (orthogonalFactor_tendsto r hr).comp primeInfinity_real_tendsto
  have h := hf.div ((hx.mul hz).mul ht) (by norm_num)
  simp only [show 2*r-r=r by omega,Function.comp_def] at h
  norm_num only at h
  have he (q : OddPrime) := tripleCoefficient_normalized (K := ZMod q.val)
    (by simpa only [ZMod.ringChar_zmod_n] using q.property.2) r ξ ζ θ
  simp only [ZMod.card] at he
  simp_rw [he]
  exact h

private instance certificate_instance_0816 : OAI.SidorenkoCounterexample.ProofCertificate_0816 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7
  exact @certificate_proof_0816 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 p45 p46 q0 q1 q2 q3 q4 q5 q6 q7

end SidorenkoCounterexample
end
section
namespace SidorenkoCounterexample
open Module
open scoped BigOperators
section Sizes
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
omit [DecidableEq K] in
theorem certificate_proof_0817 (r : ℕ) :
    Fintype.card K ^ r.choose 2 ≤ Nat.card (MaxOrthogonal (K := K) (V := Fin r → K)) := by
  classical
  let : Finite (Module.Dual K (Fin r → K)) := Module.finite_of_finite K
  have h := Nat.card_le_card_of_injective (f := graphMaxOrthogonal (K := K) (⊤ : Submodule K (Fin r → K))) (graphMaxOrthogonal_form_injective
    (K := K) (⊤ : Submodule K (Fin r → K)))
  simpa only [altForm_card,finrank_top,Module.finrank_fin_fun] using h

private instance certificate_instance_0817 : OAI.SidorenkoCounterexample.ProofCertificate_0817 := by
  constructor
  intro q0 q1 q2 q3
  exact @certificate_proof_0817 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 p45 p46 q0 q1 q2 q3

theorem certificate_proof_0818 (r : ℕ) (L : LinearMap.BilinForm K (Fin (2*r) → K))
    (hs : L.IsSymm) (hL : L.Nondegenerate) (hK : ringChar K≠2)
    (hc : discriminantSign L hs=quadraticChar K ((-1 : K)^r)) :
    Nat.card {U : DimSubspace K (Fin (2*r) → K) r // L.restrict U.val=0} =
      Nat.card (MaxOrthogonal (K := K) (V := Fin r → K)) := by
  rw [Nat.card_congr (halfIsotropicEquiv L hL r (by simp))]
  exact split_form_card L hs hL hK r (by simp) hc

private instance certificate_instance_0818 : OAI.SidorenkoCounterexample.ProofCertificate_0818 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9
  exact @certificate_proof_0818 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 p45 p46 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9

omit [DecidableEq K] in
theorem certificate_proof_0819 (r : ℕ) (hr : 0<r) :
    (Fintype.card K : ℝ) ≤ Nat.card (DimSubspace K (Fin (2*r) → K) r) := by
  have h := subspace_count_lower (K := K) (V := Fin (2*r) → K) r (by simp; omega)
  simp only [Module.finrank_fin_fun,show 2*r-r=r by omega] at h
  apply le_trans _ h
  have hq : (1 : ℝ)≤Fintype.card K := by exact_mod_cast (Fintype.one_lt_card (α := K)).le
  simpa only [pow_one] using pow_le_pow_right₀ hq (show 1≤r*r from Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega)))

private instance certificate_instance_0819 : OAI.SidorenkoCounterexample.ProofCertificate_0819 := by
  constructor
  intro q0 q1 q2 q3 q4
  exact @certificate_proof_0819 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 p45 p46 q0 q1 q2 q3 q4

theorem certificate_proof_0820 (r : ℕ) (hr : 1<r)
    (L : LinearMap.BilinForm K (Fin (2*r) → K)) (hs : L.IsSymm) (hL : L.Nondegenerate)
    (hK : ringChar K≠2) (hc : discriminantSign L hs=quadraticChar K ((-1 : K)^r)) :
    (Fintype.card K : ℝ) ≤ Nat.card {U : DimSubspace K (Fin (2*r) → K) r // L.restrict U.val=0} := by
  rw [halfIsotropic_card r L hs hL hK hc]
  have h : (Fintype.card K : ℝ)^r.choose 2 ≤ Nat.card (MaxOrthogonal (K := K) (V := Fin r → K)) := by
    exact_mod_cast maxOrthogonal_card_lower (K := K) r
  apply le_trans _ h
  have hq : (1 : ℝ)≤Fintype.card K := by exact_mod_cast (Fintype.one_lt_card (α := K)).le
  simpa only [pow_one] using pow_le_pow_right₀ hq (Nat.choose_pos (show 2≤r by omega))

private instance certificate_instance_0820 : OAI.SidorenkoCounterexample.ProofCertificate_0820 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10
  exact @certificate_proof_0820 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 p45 p46 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10

end Sizes
section Bounds
variable {K I : Type} [Field K] [Fintype K] [DecidableEq K] [Fintype I] {D r : ℕ}
theorem certificate_proof_0821 (U : I → Submodule K (Fin D → K))
    (hinj : Function.Injective U) (hd : ∀ i, finrank K (U i)=r)
    (hc : (Fintype.card K : ℝ)≤Fintype.card I) (hK : ringChar K≠2)
    {ξ : ℤ} (hξ : ξ=1 ∨ ξ= -1) :
    uniformMean (fun Q : SymMatrix K D =>
      |uniformMean (fun i => formSignIndicator ξ (symFormPull (U i).subtype (matrixFormEquiv D Q)))-1/2|) ≤
        Real.sqrt (((r : ℝ)+1)/(Fintype.card K : ℝ)) := by
  have hq : (0 : ℝ)<Fintype.card K := Nat.cast_pos.mpr Fintype.card_pos
  have hi : (0 : ℝ)<Fintype.card I := hq.trans_le hc
  have : Nonempty I := Fintype.card_pos_iff.mp (Nat.cast_pos.mp hi)
  have he := uniformMean_equiv (matrixFormEquiv (K := K) D)
    (fun Q => |uniformMean (fun i => formSignIndicator ξ (symFormPull (U i).subtype Q))-1/2|)
  dsimp only [Function.comp_def] at he
  rw [he]
  have h := restriction_family_L1_sq U hinj r hd hK hξ
  have hiq : 1/(Fintype.card I : ℝ)≤1/(Fintype.card K : ℝ) := one_div_le_one_div_of_le hq hc
  have ht : (r : ℝ)/(Fintype.card K : ℝ)+1/(Fintype.card I : ℝ) ≤
      ((r : ℝ)+1)/(Fintype.card K : ℝ) := by rw [add_div]; linarith
  exact (Real.le_sqrt (uniformMean_nonneg (fun _ => abs_nonneg _)) (by positivity)).mpr (h.trans ht)

private instance certificate_instance_0821 : OAI.SidorenkoCounterexample.ProofCertificate_0821 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14
  exact @certificate_proof_0821 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 p45 p46 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14

theorem certificate_proof_0822 (r : ℕ) (hr : 0<r) (hK : ringChar K≠2)
    {ξ : ℤ} (hξ : ξ=1 ∨ ξ= -1) :
    uniformMean (fun Q : SymMatrix K (2*r) => |pairRestrictionFraction Q r ξ-1/2|) ≤
      Real.sqrt (((r : ℝ)+1)/(Fintype.card K : ℝ)) := by
  classical
  let := Fintype.ofFinite (DimSubspace K (Fin (2*r) → K) r)
  exact matrix_restriction_family_L1 (fun U : DimSubspace K (Fin (2*r) → K) r => U.val)
    Subtype.val_injective (fun U => U.property)
    (by simpa only [Nat.card_eq_fintype_card] using pairFamily_card_ge (K := K) r hr) hK hξ

private instance certificate_instance_0822 : OAI.SidorenkoCounterexample.ProofCertificate_0822 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8
  exact @certificate_proof_0822 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 p45 p46 q0 q1 q2 q3 q4 q5 q6 q7 q8

theorem certificate_proof_0823 (r : ℕ) (hr : 1<r)
    (L : LinearMap.BilinForm K (Fin (2*r) → K)) (hs : L.IsSymm) (hL : L.Nondegenerate)
    (hK : ringChar K≠2) (hc : discriminantSign L hs=quadraticChar K ((-1 : K)^r))
    {ξ : ℤ} (hξ : ξ=1 ∨ ξ= -1) :
    uniformMean (fun Q : SymMatrix K (2*r) => |isotropicRestrictionFraction Q L r ξ-1/2|) ≤
      Real.sqrt (((r : ℝ)+1)/(Fintype.card K : ℝ)) := by
  classical
  let := Fintype.ofFinite {U : DimSubspace K (Fin (2*r) → K) r // L.restrict U.val=0}
  exact matrix_restriction_family_L1 (fun U : {U : DimSubspace K (Fin (2*r) → K) r // L.restrict U.val=0} => U.val.val)
    (Subtype.val_injective.comp Subtype.val_injective) (fun U => U.val.property)
    (by simpa only [Nat.card_eq_fintype_card] using isotropicFamily_card_ge r hr L hs hL hK hc) hK hξ

private instance certificate_instance_0823 : OAI.SidorenkoCounterexample.ProofCertificate_0823 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12
  exact @certificate_proof_0823 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 p45 p46 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12

end Bounds
end SidorenkoCounterexample
end
section
namespace SidorenkoCounterexample
open scoped BigOperators
section Mean
variable {I A B : Type} [Fintype I] [DecidableEq I] [Fintype A] [Fintype B]
omit [DecidableEq I] in
theorem certificate_proof_0824 (f : I → A → ℝ) :
    uniformMean (fun a => ∑ i, f i a)=∑ i, uniformMean (f i) := by
  unfold uniformMean
  rw [Finset.sum_comm,Finset.sum_div]

private instance certificate_instance_0824 : OAI.SidorenkoCounterexample.ProofCertificate_0824 := by
  constructor
  intro q0 q1 q2 q3 q4
  exact @certificate_proof_0824 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 p45 p46 q0 q1 q2 q3 q4

theorem certificate_proof_0825 [Nonempty A] (i : I) (f : A → ℝ) :
    uniformMean (fun x : I → A => f (x i))=uniformMean f := by
  classical
  rw [←uniformMean_equiv (Equiv.piSplitAt i (fun _ : I => A)).symm,uniformMean_prod]
  simp only [Function.comp_def,Equiv.piSplitAt,Equiv.coe_fn_symm_mk]
  simp [uniformMean_const]

private instance certificate_instance_0825 : OAI.SidorenkoCounterexample.ProofCertificate_0825 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7
  exact @certificate_proof_0825 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 p45 p46 q0 q1 q2 q3 q4 q5 q6 q7

theorem certificate_proof_0826 [Nonempty A] (i : I) (f : (I → A) → ℝ) :
    uniformMean f=uniformMean (fun x : I → A => uniformMean (fun a : A => f (Function.update x i a))) := by
  classical
  let e := Equiv.funSplitAt i A
  have he (x : A × ({j : I // j≠i} → A)) (a : A) :
      Function.update (e.symm x) i a=e.symm (a,x.2) := by
    ext j
    by_cases hj : j=i
    · subst j; simp [e,Equiv.funSplitAt,Equiv.piSplitAt]
    · simp [e,Equiv.funSplitAt,Equiv.piSplitAt,hj]
  rw [←uniformMean_equiv e.symm,uniformMean_prod]
  conv_rhs => rw [←uniformMean_equiv e.symm,uniformMean_prod]
  simp only [Function.comp_def,he]
  rw [uniformMean_const]
  exact uniformMean_swap _

private instance certificate_instance_0826 : OAI.SidorenkoCounterexample.ProofCertificate_0826 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7
  exact @certificate_proof_0826 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 p45 p46 q0 q1 q2 q3 q4 q5 q6 q7

theorem certificate_proof_0827 (f : A → ℝ) (c : ℝ) :
    uniformMean (fun a => f a*c)=uniformMean f*c := by
  simpa only [mul_comm] using uniformMean_mul c f

private instance certificate_instance_0827 : OAI.SidorenkoCounterexample.ProofCertificate_0827 := by
  constructor
  intro q0 q1 q2 q3
  exact @certificate_proof_0827 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 p45 p46 q0 q1 q2 q3

theorem certificate_proof_0828 [Nonempty A] (P : A → Prop) [DecidablePred P]
    (f : A → ℝ) (b : ℝ) (hf : ∀ a, P a → f a≤b) (hb : 0≤b) :
    uniformMean (fun a => if P a then f a else 0)≤b := by
  apply uniformMean_bound
  intro a
  split_ifs with h
  · exact hf a h
  · exact hb

private instance certificate_instance_0828 : OAI.SidorenkoCounterexample.ProofCertificate_0828 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8
  exact @certificate_proof_0828 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 p45 p46 q0 q1 q2 q3 q4 q5 q6 q7 q8

end Mean
end SidorenkoCounterexample
end
section
namespace SidorenkoCounterexample
open scoped BigOperators
open Module
section Inverting
variable {K : Type} [Field K] [Fintype K]
omit [Fintype K] in
theorem certificate_proof_0829 (D : ℕ) : Function.Involutive (symmetricInverse (K := K) D) := by
  classical
  intro M
  by_cases h : M.val.det = 0
  · have he : symmetricInverse D M = M := by simp only [symmetricInverse, h, ↓reduceIte]
    rw [he, he]
  · let M' : SymMatrix K D := ⟨M.val⁻¹, M.property.inv⟩
    have he : symmetricInverse D M = M' := by simp only [symmetricInverse, h, ↓reduceIte, M']
    have hn : M'.val.det ≠ 0 := (M.val.isUnit_nonsing_inv_det (isUnit_iff_ne_zero.mpr h)).ne_zero
    have he' : symmetricInverse D M' = ⟨M'.val⁻¹, M'.property.inv⟩ := by
      simp only [symmetricInverse, hn, ↓reduceIte]
    rw [he, he']
    exact Subtype.ext (M.val.nonsing_inv_nonsing_inv (isUnit_iff_ne_zero.mpr h))

private instance certificate_instance_0829 : OAI.SidorenkoCounterexample.ProofCertificate_0829 := by
  constructor
  intro q0 q1 q2
  exact @certificate_proof_0829 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 p45 p46 q0 q1 q2

end Inverting
end SidorenkoCounterexample
end
section
namespace SidorenkoCounterexample
open Module Classical
open scoped Matrix BigOperators
section Center
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
theorem certificate_proof_0830 (r : ℕ) (ξ ζ : ℤ) (B : SymMatrix K (2*r)) :
    pairLocal r ξ ζ B =
      (Nat.card {A : SymMatrix K (2*r) // A ∈ signedLayer K (2*r) r ξ ∧
        A-B ∈ signedLayer K (2*r) r ζ} : ℝ) /
      (Fintype.card (SymMatrix K (2*r)) : ℝ) /
        (layerMass K (2*r) r ξ * layerMass K (2*r) r ζ) := by
  have he (A : SymMatrix K (2*r)) :
      rankKernel K (2*r) r ξ A * rankKernel K (2*r) r ζ (A-B) =
      (if A ∈ signedLayer K (2*r) r ξ ∧ A-B ∈ signedLayer K (2*r) r ζ then (1 : ℝ) else 0) *
        (layerMass K (2*r) r ξ * layerMass K (2*r) r ζ)⁻¹ := by
    unfold rankKernel
    split_ifs <;> simp_all [mul_comm]
  unfold pairLocal
  simp_rw [he]
  rw [uniformMean_mul_right,uniformMean_indicator,Nat.card_eq_fintype_card]
  rfl

private instance certificate_instance_0830 : OAI.SidorenkoCounterexample.ProofCertificate_0830 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7
  exact @certificate_proof_0830 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 p45 p46 q0 q1 q2 q3 q4 q5 q6 q7

theorem certificate_proof_0831 (r : ℕ) (ξ ζ θ : ℤ) (B C : SymMatrix K (2*r)) :
    tripleLocal r ξ ζ θ B C =
      (Nat.card {A : SymMatrix K (2*r) // A ∈ signedLayer K (2*r) r ξ ∧
        A-B ∈ signedLayer K (2*r) r ζ ∧ A-C ∈ signedLayer K (2*r) r θ} : ℝ) /
      (Fintype.card (SymMatrix K (2*r)) : ℝ) /
        (layerMass K (2*r) r ξ * layerMass K (2*r) r ζ * layerMass K (2*r) r θ) := by
  have he (A : SymMatrix K (2*r)) :
      rankKernel K (2*r) r ξ A * rankKernel K (2*r) r ζ (A-B) * rankKernel K (2*r) r θ (A-C) =
      (if A ∈ signedLayer K (2*r) r ξ ∧ A-B ∈ signedLayer K (2*r) r ζ ∧
        A-C ∈ signedLayer K (2*r) r θ then (1 : ℝ) else 0) *
        (layerMass K (2*r) r ξ * layerMass K (2*r) r ζ * layerMass K (2*r) r θ)⁻¹ := by
    unfold rankKernel
    split_ifs <;> simp_all [mul_comm,mul_assoc]
  unfold tripleLocal
  simp_rw [he]
  rw [uniformMean_mul_right,uniformMean_indicator,Nat.card_eq_fintype_card]
  rfl

private instance certificate_instance_0831 : OAI.SidorenkoCounterexample.ProofCertificate_0831 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9
  exact @certificate_proof_0831 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 p45 p46 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9

theorem certificate_proof_0832 (r : ℕ) (ξ ζ : ℤ) (B : SymMatrix K (2*r))
    (hB : B.val.det≠0) (hm : pairMatch r ξ ζ B) :
    pairLocal r ξ ζ B = pairCoefficient (K := K) r ξ ζ *
      pairRestrictionFraction (symmetricInverse (2*r) B) r ξ := by
  rw [pairLocal_card,pairCenter_card rfl B hB ξ ζ hm]
  simp only [symmetricInverse,hB,ite_false]
  unfold pairCoefficient
  ring

private instance certificate_instance_0832 : OAI.SidorenkoCounterexample.ProofCertificate_0832 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9
  exact @certificate_proof_0832 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 p45 p46 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9

theorem certificate_proof_0833 (r : ℕ) (ξ ζ : ℤ) (B : SymMatrix K (2*r))
    (hB : B.val.det≠0) (hm : ¬pairMatch r ξ ζ B) : pairLocal r ξ ζ B=0 := by
  unfold pairLocal
  have he (A : SymMatrix K (2*r)) :
      rankKernel K (2*r) r ξ A * rankKernel K (2*r) r ζ (A-B)=0 := by
    unfold rankKernel
    split_ifs with hx hz
    · obtain ⟨ha,hs⟩ := (mem_signedLayer ..).mp hx
      obtain ⟨hb,ht⟩ := (mem_signedLayer ..).mp hz
      have h := signed_pair_compatibility rfl A B hB ha hb
      rw [hs,ht] at h
      exact (hm h).elim
    all_goals simp
  simp_rw [he]
  exact uniformMean_const 0

private instance certificate_instance_0833 : OAI.SidorenkoCounterexample.ProofCertificate_0833 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9
  exact @certificate_proof_0833 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 p45 p46 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9

theorem certificate_proof_0834 (r : ℕ) (ξ ζ θ : ℤ) (B C : SymMatrix K (2*r))
    (hB : B.val.det≠0) (hC : C.val.det≠0) (hBC : (C-B).val.det≠0)
    (hm : ¬tripleMatch r ξ ζ θ B C) : tripleLocal r ξ ζ θ B C=0 := by
  unfold tripleLocal
  have he (A : SymMatrix K (2*r)) :
      rankKernel K (2*r) r ξ A * rankKernel K (2*r) r ζ (A-B) * rankKernel K (2*r) r θ (A-C)=0 := by
    unfold rankKernel
    split_ifs with hx hz ht
    · obtain ⟨ha,hs⟩ := (mem_signedLayer ..).mp hx
      obtain ⟨hb,hz⟩ := (mem_signedLayer ..).mp hz
      obtain ⟨hc,ht⟩ := (mem_signedLayer ..).mp ht
      have h1 := signed_pair_compatibility rfl A B hB ha hb
      have h2 := signed_pair_compatibility rfl A C hC ha hc
      have h3 := signed_pair_compatibility rfl (A-B) (C-B) hBC hb (by simpa using hc)
      simp only [sub_sub_sub_cancel_right] at h3
      rw [hs,hz] at h1
      rw [hs,ht] at h2
      rw [hz,ht] at h3
      exact (hm ⟨h1,h2,h3⟩).elim
    all_goals simp
  simp_rw [he]
  exact uniformMean_const 0

private instance certificate_instance_0834 : OAI.SidorenkoCounterexample.ProofCertificate_0834 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13
  exact @certificate_proof_0834 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 p45 p46 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13

omit [Fintype K] [DecidableEq K] in
theorem certificate_proof_0835 (D : ℕ) (B C : SymMatrix K D)
    (hB : B.val.det≠0) (hC : C.val.det≠0) :
    (B.val⁻¹-C.val⁻¹).det = B.val.det⁻¹ * (C-B).val.det * C.val.det⁻¹ := by
  rw [Matrix.inv_sub_inv (by
    exact iff_of_true ((Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hB))
      ((Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hC)))]
  simp only [Matrix.det_mul,Matrix.det_nonsing_inv,Ring.inverse_eq_inv,Submodule.coe_sub]

private instance certificate_instance_0835 : OAI.SidorenkoCounterexample.ProofCertificate_0835 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6
  exact @certificate_proof_0835 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 p45 p46 q0 q1 q2 q3 q4 q5 q6

omit [Fintype K] [DecidableEq K] in
theorem certificate_proof_0836 (D : ℕ) (B C : SymMatrix K D)
    (hB : B.val.det≠0) (hC : C.val.det≠0) (hBC : (C-B).val.det≠0) :
    (B.val⁻¹-C.val⁻¹).toBilin'.Nondegenerate := by
  apply Matrix.nondegenerate_toBilin'_iff.mpr
  apply Matrix.nondegenerate_iff_det_ne_zero.mpr
  rw [inverse_difference_det D B C hB hC]
  exact mul_ne_zero (mul_ne_zero (inv_ne_zero hB) hBC) (inv_ne_zero hC)

private instance certificate_instance_0836 : OAI.SidorenkoCounterexample.ProofCertificate_0836 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7
  exact @certificate_proof_0836 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 p45 p46 q0 q1 q2 q3 q4 q5 q6 q7

theorem certificate_proof_0837 (r : ℕ) (B C : SymMatrix K (2*r))
    (hB : B.val.det≠0) (hC : C.val.det≠0) (hBC : (C-B).val.det≠0)
    {ξ ζ θ : ℤ} (hξ : ξ=1 ∨ ξ= -1) (hζ : ζ=1 ∨ ζ= -1) (hθ : θ=1 ∨ θ= -1)
    (hm : tripleMatch r ξ ζ θ B C) :
    discriminantSign (B.val⁻¹-C.val⁻¹).toBilin'
      (Matrix.isSymm_toBilin'_iff_isSymm.mpr (B.property.inv.sub C.property.inv)) =
        quadraticChar K ((-1 : K)^r) := by
  rw [discriminantSign_nondegenerate _ _ (inverse_difference_nondegenerate (2*r) B C hB hC hBC)
    (Pi.basisFun K (Fin (2*r)))]
  change quadraticChar K ((B.val⁻¹-C.val⁻¹).toBilin'.toMatrix').det = _
  rw [LinearMap.BilinForm.toMatrix'_toBilin',inverse_difference_det (2*r) B C hB hC,
    map_mul,map_mul,quadraticChar_inverse hB,quadraticChar_inverse hC]
  rw [hm.1,hm.2.1,hm.2.2]
  have hc := quadraticChar_sq_one (F := K) (pow_ne_zero r (neg_ne_zero.mpr one_ne_zero))
  have hx : ξ^2=1 := by rcases hξ with rfl | rfl <;> norm_num
  have hz : ζ^2=1 := by rcases hζ with rfl | rfl <;> norm_num
  have ht : θ^2=1 := by rcases hθ with rfl | rfl <;> norm_num
  calc
    _ = quadraticChar K ((-1 : K)^r) * (quadraticChar K ((-1 : K)^r))^2 * ξ^2 * ζ^2 * θ^2 := by ring
    _ = _ := by rw [hc,hx,hz,ht]; ring

private instance certificate_instance_0837 : OAI.SidorenkoCounterexample.ProofCertificate_0837 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16
  exact @certificate_proof_0837 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 p45 p46 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16

theorem certificate_proof_0838 (hK : ringChar K≠2) (r : ℕ) (B C : SymMatrix K (2*r))
    (hB : B.val.det≠0) (hC : C.val.det≠0) (hBC : (C-B).val.det≠0)
    {ξ ζ θ : ℤ} (hξ : ξ=1 ∨ ξ= -1) (hζ : ζ=1 ∨ ζ= -1) (hθ : θ=1 ∨ θ= -1)
    (hm : tripleMatch r ξ ζ θ B C) :
    tripleLocal r ξ ζ θ B C = tripleCoefficient (K := K) r ξ ζ θ *
      isotropicRestrictionFraction (symmetricInverse (2*r) B) (B.val⁻¹-C.val⁻¹).toBilin' r ξ := by
  rw [tripleLocal_card,tripleCenter_card rfl B C hB hC ξ ζ θ hm.1 hm.2.1,
    halfIsotropic_card r _ (Matrix.isSymm_toBilin'_iff_isSymm.mpr (B.property.inv.sub C.property.inv))
      (inverse_difference_nondegenerate (2*r) B C hB hC hBC) hK
      (matching_inverse_difference_split r B C hB hC hBC hξ hζ hθ hm)]
  simp only [symmetricInverse,hB,ite_false]
  unfold tripleCoefficient
  ring

private instance certificate_instance_0838 : OAI.SidorenkoCounterexample.ProofCertificate_0838 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17
  exact @certificate_proof_0838 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 p45 p46 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17

end Center
end SidorenkoCounterexample
end
section
namespace SidorenkoCounterexample
open Module Classical
open scoped BigOperators
section Means
variable {A B : Type} [Fintype A] [Fintype B]
theorem certificate_proof_0839 {f : A → ℝ} (hf : ∀ a, f a ≤ 1) : uniformMean f ≤ 1 := by
  cases isEmpty_or_nonempty A
  · simp [uniformMean]
  · exact uniformMean_bound hf

private instance certificate_instance_0839 : OAI.SidorenkoCounterexample.ProofCertificate_0839 := by
  constructor
  intro q0 q1 q2 q3
  exact @certificate_proof_0839 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 p45 p46 q0 q1 q2 q3

variable [AddCommGroup A]
theorem certificate_proof_0840 (a : A) (f : A → ℝ) :
    uniformMean (fun x => f (a-x))=uniformMean f :=
  uniformMean_equiv (Equiv.subLeft a) f

private instance certificate_instance_0840 : OAI.SidorenkoCounterexample.ProofCertificate_0840 := by
  constructor
  intro q0 q1 q2 q3 q4
  exact @certificate_proof_0840 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 p45 p46 q0 q1 q2 q3 q4

end Means
section Range
variable {K : Type} [Field K] [Fintype K] [DecidableEq K] {D : ℕ}
theorem certificate_proof_0841 (Q : SymMatrix K D) (r : ℕ) (ξ : ℤ) :
    0 ≤ pairRestrictionFraction Q r ξ ∧ pairRestrictionFraction Q r ξ ≤ 1 := by
  let := Fintype.ofFinite (DimSubspace K (Fin D → K) r)
  unfold pairRestrictionFraction
  exact ⟨uniformMean_nonneg (fun _ => formSignIndicator_nonneg _ _),
    uniformMean_le_one (fun _ => formSignIndicator_le_one _ _)⟩

private instance certificate_instance_0841 : OAI.SidorenkoCounterexample.ProofCertificate_0841 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7
  exact @certificate_proof_0841 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 p45 p46 q0 q1 q2 q3 q4 q5 q6 q7

theorem certificate_proof_0842 (Q : SymMatrix K D)
    (L : LinearMap.BilinForm K (Fin D → K)) (r : ℕ) (ξ : ℤ) :
    0 ≤ isotropicRestrictionFraction Q L r ξ ∧ isotropicRestrictionFraction Q L r ξ ≤ 1 := by
  let := Fintype.ofFinite {U : DimSubspace K (Fin D → K) r // L.restrict U.val=0}
  unfold isotropicRestrictionFraction
  exact ⟨uniformMean_nonneg (fun _ => formSignIndicator_nonneg _ _),
    uniformMean_le_one (fun _ => formSignIndicator_le_one _ _)⟩

private instance certificate_instance_0842 : OAI.SidorenkoCounterexample.ProofCertificate_0842 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8
  exact @certificate_proof_0842 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 p45 p46 q0 q1 q2 q3 q4 q5 q6 q7 q8

omit [DecidableEq K] in
theorem certificate_proof_0843 (f : SymMatrix K D → ℝ) :
    uniformMean (fun B => f (symmetricInverse D B))=uniformMean f :=
  uniformMean_equiv (symmetricInverseEquiv D) f

private instance certificate_instance_0843 : OAI.SidorenkoCounterexample.ProofCertificate_0843 := by
  constructor
  intro q0 q1 q2 q3 q4
  exact @certificate_proof_0843 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 p45 p46 q0 q1 q2 q3 q4

end Range
end SidorenkoCounterexample
end
section
namespace SidorenkoCounterexample
open Module Classical Filter
open scoped BigOperators
section Error
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
end Error
end SidorenkoCounterexample
end
section
namespace SidorenkoCounterexample
open Module Classical Filter
open scoped BigOperators
section Bounds
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
end Bounds
end SidorenkoCounterexample
end
end OAI

theorem solution : OAI.SidorenkoCounterexample.ProofCertificate_0805 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0806 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0807 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0808 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0809 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0810 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0811 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0812 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0813 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0814 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0815 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0816 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0817 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0818 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0819 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0820 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0821 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0822 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0823 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0824 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0825 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0826 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0827 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0828 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0829 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0830 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0831 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0832 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0833 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0834 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0835 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0836 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0837 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0838 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0839 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0840 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0841 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0842 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0843 := by
  exact ⟨inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance⟩
end

