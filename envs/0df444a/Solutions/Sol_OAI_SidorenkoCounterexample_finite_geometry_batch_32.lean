-- Prove2me | solution 1 for OAI.SidorenkoCounterexample.finite_geometry_batch_32
-- status  : ACCEPTED   (prove)
-- author  : @abcdefg
-- created : 2026-10-09T06:38:36.678089+00:00
-- url     : https://prove2.me/submissions/60279d98-0573-4d7d-acac-269a3a5033e6

import Definitions.Def_SidorenkoCertificateBundleB
set_option linter.unusedVariables false
section
variable [p0 : OAI.SidorenkoCounterexample.ProofCertificate_0457]
  [p1 : OAI.SidorenkoCounterexample.ProofCertificate_0583]
  [p2 : OAI.SidorenkoCounterexample.ProofCertificate_0605]
  [p3 : OAI.SidorenkoCounterexample.ProofCertificate_0653]
  [p4 : OAI.SidorenkoCounterexample.ProofCertificate_0656]
  [p5 : OAI.SidorenkoCounterexample.ProofCertificate_0657]
  [p6 : OAI.SidorenkoCounterexample.ProofCertificate_0658]
  [p7 : OAI.SidorenkoCounterexample.ProofCertificate_0659]
  [p8 : OAI.SidorenkoCounterexample.ProofCertificate_0660]
  [p9 : OAI.SidorenkoCounterexample.ProofCertificate_0662]
  [p10 : OAI.SidorenkoCounterexample.ProofCertificate_0791]
  [p11 : OAI.SidorenkoCounterexample.ProofCertificate_0824]
  [p12 : OAI.SidorenkoCounterexample.ProofCertificate_0915]
  [p13 : OAI.SidorenkoCounterexample.ProofCertificate_0916]
  [p14 : OAI.SidorenkoCounterexample.ProofCertificate_0919]
  [p15 : OAI.SidorenkoCounterexample.ProofCertificate_0924]
  [p16 : OAI.SidorenkoCounterexample.ProofCertificate_0925]
  [p17 : OAI.SidorenkoCounterexample.ProofCertificate_0926]
  [p18 : OAI.SidorenkoCounterexample.ProofCertificate_0948]
  [p19 : OAI.SidorenkoCounterexample.ProofCertificate_0949]
  [p20 : OAI.SidorenkoCounterexample.ProofCertificate_0950]
  [p21 : OAI.SidorenkoCounterexample.ProofCertificate_0960]
  [p22 : OAI.SidorenkoCounterexample.ProofCertificate_0961]
  [p23 : OAI.SidorenkoCounterexample.ProofCertificate_0962]
  [p24 : OAI.SidorenkoCounterexample.ProofCertificate_0964]
  [p25 : OAI.SidorenkoCounterexample.ProofCertificate_0965]
  [p26 : OAI.SidorenkoCounterexample.ProofCertificate_0966]
  [p27 : OAI.SidorenkoCounterexample.ProofCertificate_0976]
  [p28 : OAI.SidorenkoCounterexample.ProofCertificate_0978]
  [p29 : OAI.SidorenkoCounterexample.ProofCertificate_0986]
  [p30 : OAI.SidorenkoCounterexample.ProofCertificate_0987]
include p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30

namespace OAI
section
namespace SidorenkoCounterexample
open Module Classical Filter
open scoped BigOperators
section FaceGraph
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
end FaceGraph
end SidorenkoCounterexample
end
section
namespace SidorenkoCounterexample
open Module Classical Filter
open scoped BigOperators
section Global
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
end Global
end SidorenkoCounterexample
end
section
namespace SidorenkoCounterexample
open Module Classical Filter
open scoped BigOperators
section GlobalProduct
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
theorem certificate_proof_0988 (r : ℕ) (ξ : Fin 22 → Fin 3 → ℤ) (j : Fin 22) :
    faceBound (K := K) r (ξ j)≤globalBound (K := K) r ξ := by
  have h := Finset.single_le_sum (s := (Finset.univ : Finset (Fin 22)))
    (fun k _ => le_trans (by norm_num : (0:ℝ)≤1) (faceBound_one (K := K) r (ξ k))) (Finset.mem_univ j)
  unfold globalBound; linarith

private instance certificate_instance_0988 : OAI.SidorenkoCounterexample.ProofCertificate_0988 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6
  exact @certificate_proof_0988 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 q0 q1 q2 q3 q4 q5 q6

theorem certificate_proof_0989 (hK : ringChar K≠2) (r : ℕ) (hr : 0<r)
    (T : Fin 22 → Finset (Fin 3)) (ξ : Fin 22 → Fin 3 → ℤ)
    (hξ : ∀ j i,ξ j i=1 ∨ ξ j i= -1) (X : Fin 13 → SymMatrix K (2*r)) (hX : fullTransverse X) :
    |configurationProduct r T ξ X-configurationPolynomial r T ξ X|≤
      globalBound (K := K) r ξ^22*∑ j,faceError r (ξ j) (X ∘ faceVertex j) := by
  have hC := globalBound_eight (K := K) r ξ
  have h := product_difference_bound Finset.univ
    (fun j => faceLocal r (T j) (ξ j) (X ∘ faceVertex j))
    (fun j => facePolynomial r (T j) (ξ j) (X ∘ faceVertex j)) (by linarith : 1≤globalBound (K := K) r ξ)
    (fun j _ => by
      rw [abs_of_nonneg (faceLocal_nonneg ..)]
      exact (faceLocal_bound hK r hr (T j) (ξ j) (hξ j) _ (fullTransverse_face X hX j)).trans (faceBound_le_global r ξ j))
    (fun j _ => (facePolynomial_abs_le r (T j) (ξ j) (hξ j) _).trans hC)
  simp only [Finset.card_univ,Fintype.card_fin] at h
  exact h.trans (mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun j _ =>
    faceLocal_error hK r hr (T j) (ξ j) (hξ j) _ (fullTransverse_face X hX j))) (by positivity))

private instance certificate_instance_0989 : OAI.SidorenkoCounterexample.ProofCertificate_0989 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11
  exact @certificate_proof_0989 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11

theorem certificate_proof_0990 (hK : ringChar K≠2) (r : ℕ) (hr : 0<r)
    (T : Fin 22 → Finset (Fin 3)) (ξ : Fin 22 → Fin 3 → ℤ)
    (hξ : ∀ j i,ξ j i=1 ∨ ξ j i= -1) :
    |transverseDifference (K := K) r T ξ|≤globalBound (K := K) r ξ^22*
      ∑ j,uniformMean (fun X : Fin 13 → SymMatrix K (2*r) => faceError r (ξ j) (X ∘ faceVertex j)) := by
  calc
    _ ≤ uniformMean (fun X : Fin 13 → SymMatrix K (2*r) =>
      |if fullTransverse X then configurationProduct r T ξ X-configurationPolynomial r T ξ X else 0|) := abs_uniformMean_le _
    _ ≤ uniformMean (fun X : Fin 13 → SymMatrix K (2*r) =>
        globalBound (K := K) r ξ^22*∑ j,faceError r (ξ j) (X ∘ faceVertex j)) := by
      apply uniformMean_mono; intro X
      split_ifs with hX
      · exact configuration_difference_bound hK r hr T ξ hξ X hX
      · rw [abs_zero]; exact mul_nonneg (by positivity) (Finset.sum_nonneg (fun j _ => faceError_nonneg ..))
    _ = _ := by rw [uniformMean_mul,uniformMean_sum]

private instance certificate_instance_0990 : OAI.SidorenkoCounterexample.ProofCertificate_0990 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9
  exact @certificate_proof_0990 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9

end GlobalProduct
theorem certificate_proof_0991 (r : ℕ) (hr : 0<r) (ξ : Fin 22 → Fin 3 → ℤ)
    (hξ : ∀ j i,ξ j i=1 ∨ ξ j i= -1) : Tendsto
    (fun q : OddPrime => globalBound (K := ZMod q.val) r ξ) primeInfinity (nhds 646) := by
  have hs := (tendsto_finsetSum Finset.univ (fun j _ => faceBound_tendsto r hr (ξ j) (hξ j))).const_add 8
  norm_num only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at hs
  exact hs

private instance certificate_instance_0991 : OAI.SidorenkoCounterexample.ProofCertificate_0991 := by
  constructor
  intro q0 q1 q2 q3
  exact @certificate_proof_0991 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 q0 q1 q2 q3

theorem certificate_proof_0992 (r : ℕ) (hr : 1<r)
    (T : Fin 22 → Finset (Fin 3)) (ξ : Fin 22 → Fin 3 → ℤ)
    (hξ : ∀ j i,ξ j i=1 ∨ ξ j i= -1) : Tendsto
    (fun q : OddPrime => transverseDifference (K := ZMod q.val) r T ξ) primeInfinity (nhds 0) := by
  have he := tendsto_finsetSum Finset.univ (fun j _ =>
    faceError_mean_tendsto r hr (ξ j) (hξ j) (faceVertex j) (faceVertex_injective j))
  simp only [Finset.sum_const_zero] at he
  have ht := ((globalBound_tendsto r (by omega) ξ hξ).pow 22).mul he
  simp only [mul_zero] at ht
  apply squeeze_zero_norm (fun q => ?_) ht
  rw [Real.norm_eq_abs]
  exact transverseDifference_bound (by simpa only [ZMod.ringChar_zmod_n] using q.property.2) r (by omega) T ξ hξ

private instance certificate_instance_0992 : OAI.SidorenkoCounterexample.ProofCertificate_0992 := by
  constructor
  intro q0 q1 q2 q3 q4
  exact @certificate_proof_0992 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 q0 q1 q2 q3 q4

end SidorenkoCounterexample
end
section
namespace SidorenkoCounterexample
open Module Classical Filter
open scoped BigOperators
theorem certificate_proof_0993 (c : ℝ) (hc : |c|≤1) (T : Finset (Fin 3))
    (ξ : Fin 3 → ℤ) (hξ : ∀ i,ξ i=1 ∨ ξ i= -1) (j : Fin 22) (η : Fin 33 → Bool) :
    |boolFacePolynomial c T ξ j η|≤8 := by
  have hs (i) : |(ξ i : ℝ)|=1 := by rcases hξ i with h|h <;> simp [h]
  have h := abs_prod_le_pow Finset.univ
    (fun k : Fin 3 => if slotLeft k∈T ∧ slotRight k∈T then
      1+c*boolSign (η (facePair j k))*(ξ (slotLeft k) : ℝ)*(ξ (slotRight k) : ℝ) else 1)
    (by norm_num : (0:ℝ)≤2) (fun k _ => by
      split_ifs
      · calc
          _ ≤ |(1:ℝ)|+|c*boolSign (η (facePair j k))*(ξ (slotLeft k) : ℝ)*(ξ (slotRight k) : ℝ)| := abs_add_le _ _
          _ ≤ 2 := by simp only [abs_one,abs_mul,boolSign_abs,hs,mul_one]; linarith
      · norm_num)
  norm_num only [Finset.card_univ,Fintype.card_fin,show (2:ℝ)^3=8 by norm_num] at h
  exact h

private instance certificate_instance_0993 : OAI.SidorenkoCounterexample.ProofCertificate_0993 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6
  exact @certificate_proof_0993 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 q0 q1 q2 q3 q4 q5 q6

theorem certificate_proof_0994 (c : ℝ) (hc : |c|≤1) (T : Fin 22 → Finset (Fin 3))
    (ξ : Fin 22 → Fin 3 → ℤ) (hξ : ∀ j i,ξ j i=1 ∨ ξ j i= -1) (η : Fin 33 → Bool) :
    |boolConfiguration c T ξ η|≤8^22 := by
  simpa only [boolConfiguration,Finset.card_univ,Fintype.card_fin] using
    abs_prod_le_pow Finset.univ (fun j => boolFacePolynomial c (T j) (ξ j) j η)
      (by norm_num : (0:ℝ)≤8) (fun j _ => boolFacePolynomial_abs_le c hc (T j) (ξ j) (hξ j) j η)

private instance certificate_instance_0994 : OAI.SidorenkoCounterexample.ProofCertificate_0994 := by
  constructor
  intro q0 q1 q2 q3 q4 q5
  exact @certificate_proof_0994 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 q0 q1 q2 q3 q4 q5

section GlobalBool
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
theorem certificate_proof_0995 (r : ℕ) (T : Fin 22 → Finset (Fin 3))
    (ξ : Fin 22 → Fin 3 → ℤ) (X : Fin 13 → SymMatrix K (2*r)) (hX : fullTransverse X) :
    configurationPolynomial r T ξ X=
      boolConfiguration (quadraticChar K ((-1:K)^r)) T ξ (pairBool X) := by
  apply Finset.prod_congr rfl
  intro j _
  exact facePolynomial_bool r (T j) (ξ j) X hX j

private instance certificate_instance_0995 : OAI.SidorenkoCounterexample.ProofCertificate_0995 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8
  exact @certificate_proof_0995 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 q0 q1 q2 q3 q4 q5 q6 q7 q8

theorem certificate_proof_0996 (r : ℕ) (T : Fin 22 → Finset (Fin 3))
    (ξ : Fin 22 → Fin 3 → ℤ) (hξ : ∀ j i,ξ j i=1 ∨ ξ j i= -1) :
    |boolSingular (K := K) r T ξ|≤8^22*(33*((2*r : ℕ):ℝ)/Fintype.card K) := by
  have hc : |(quadraticChar K ((-1:K)^r) : ℝ)|≤1 := by
    rcases quadraticChar_dichotomy (F := K) (pow_ne_zero r (neg_ne_zero.mpr one_ne_zero)) with h|h <;> simp [h]
  calc
    _ ≤ uniformMean (fun X : Fin 13 → SymMatrix K (2*r) =>
      |if fullTransverse X then 0 else boolConfiguration (quadraticChar K ((-1:K)^r)) T ξ (pairBool X)|) := abs_uniformMean_le _
    _ ≤ uniformMean (fun X : Fin 13 → SymMatrix K (2*r) =>
      8^22*(if fullTransverse X then 0 else 1)) := by
      apply uniformMean_mono; intro X; split_ifs
      · norm_num
      · simpa only [mul_one] using boolConfiguration_abs_le _ hc T ξ hξ (pairBool X)
    _ = 8^22*uniformMean (fun X : Fin 13 → SymMatrix K (2*r) => if fullTransverse X then 0 else 1) := uniformMean_mul _ _
    _ ≤ _ := by
      have h := mul_le_mul_of_nonneg_left (nonTransverse_mean (K := K) (D := 2*r)) (by positivity : (0:ℝ)≤8^22)
      simpa only [mul_div_assoc] using h

private instance certificate_instance_0996 : OAI.SidorenkoCounterexample.ProofCertificate_0996 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7
  exact @certificate_proof_0996 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 q0 q1 q2 q3 q4 q5 q6 q7

theorem certificate_proof_0997 (r : ℕ) (T : Fin 22 → Finset (Fin 3))
    (ξ : Fin 22 → Fin 3 → ℤ) :
    uniformMean (configurationProduct (K := K) r T ξ)-uniformMean
      (fun X : Fin 13 → SymMatrix K (2*r) => boolConfiguration (quadraticChar K ((-1:K)^r)) T ξ (pairBool X)) =
      transverseDifference (K := K) r T ξ+matrixSingularTail (K := K) r T ξ-boolSingular (K := K) r T ξ := by
  rw [←uniformMean_sub]
  unfold transverseDifference matrixSingularTail boolSingular
  rw [←uniformMean_add,←uniformMean_sub]
  apply uniformMean_congr
  intro X
  by_cases hx : fullTransverse X
  · simp only [hx,ite_true,add_zero,sub_zero,configurationPolynomial_bool r T ξ X hx]
  · simp only [hx,ite_false,zero_add]

private instance certificate_instance_0997 : OAI.SidorenkoCounterexample.ProofCertificate_0997 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6
  exact @certificate_proof_0997 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 q0 q1 q2 q3 q4 q5 q6

end GlobalBool
theorem certificate_proof_0998 (r : ℕ) (T : Fin 22 → Finset (Fin 3))
    (ξ : Fin 22 → Fin 3 → ℤ) (hξ : ∀ j i,ξ j i=1 ∨ ξ j i= -1) : Tendsto
    (fun q : OddPrime => boolSingular (K := ZMod q.val) r T ξ) primeInfinity (nhds 0) := by
  have hd : Tendsto (fun q : OddPrime => (33*((2*r : ℕ):ℝ))/(q.val:ℝ)) primeInfinity (nhds 0) :=
    tendsto_const_nhds.div_atTop primeInfinity_real_tendsto
  have ht := hd.const_mul (8^22 : ℝ)
  simp only [mul_zero] at ht
  apply squeeze_zero_norm (fun q => ?_) ht
  rw [Real.norm_eq_abs]
  simpa only [ZMod.card] using boolSingular_bound (K := ZMod q.val) r T ξ hξ

private instance certificate_instance_0998 : OAI.SidorenkoCounterexample.ProofCertificate_0998 := by
  constructor
  intro q0 q1 q2 q3
  exact @certificate_proof_0998 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 q0 q1 q2 q3

theorem certificate_proof_0999 (r : ℕ) (T : Fin 22 → Finset (Fin 3))
    (ξ : Fin 22 → Fin 3 → ℤ) (hξ : ∀ j i,ξ j i=1 ∨ ξ j i= -1)
    (hlarge : singularTailThreshold≤2*r) : Tendsto
    (fun q : OddPrime => uniformMean (configurationProduct (K := ZMod q.val) r T ξ)-uniformMean
      (fun X : Fin 13 → SymMatrix (ZMod q.val) (2*r) =>
        boolConfiguration (quadraticChar (ZMod q.val) ((-1:ZMod q.val)^r)) T ξ (pairBool X))) primeInfinity (nhds 0) := by
  have hr : 1<r := by have := singularTailThreshold_large; omega
  simp_rw [configuration_mean_identity]
  simpa only [add_zero,sub_zero] using
    ((transverseDifference_tendsto r hr T ξ hξ).add (matrixSingularTail_tendsto r T ξ hξ hlarge)).sub
      (boolSingular_tendsto r T ξ hξ)

private instance certificate_instance_0999 : OAI.SidorenkoCounterexample.ProofCertificate_0999 := by
  constructor
  intro c0 q0 q1 q2 q3 q4
  exact @certificate_proof_0999 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 q0 q1 q2 q3 q4

end SidorenkoCounterexample
end
section
namespace SidorenkoCounterexample
open Classical
open scoped BigOperators
namespace FiniteLaw
variable {A B C I : Type} [Fintype A] [Fintype B] [Fintype C] [Fintype I] [DecidableEq I]
theorem certificate_proof_1000 (p : FiniteLaw A) {f g : A → ℝ} (h : ∀ a,f a=g a) : p.mean f=p.mean g := by
  unfold mean; exact Finset.sum_congr rfl fun a _ => congrArg (p.weight a*·) (h a)

private instance certificate_instance_1000 : OAI.SidorenkoCounterexample.ProofCertificate_1000 := by
  constructor
  intro q0 q1 q2 q3 q4 q5
  exact @certificate_proof_1000 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 q0 q1 q2 q3 q4 q5

theorem certificate_proof_1001 (p : FiniteLaw A) (c : ℝ) : p.mean (fun _ => c)=c := by
  rw [mean,←Finset.sum_mul,p.total,one_mul]

private instance certificate_instance_1001 : OAI.SidorenkoCounterexample.ProofCertificate_1001 := by
  constructor
  intro q0 q1 q2 q3
  exact @certificate_proof_1001 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 q0 q1 q2 q3

theorem certificate_proof_1002 (p : FiniteLaw A) (f g : A → ℝ) :
    p.mean (fun a => f a+g a)=p.mean f+p.mean g := by simp only [mean,mul_add,Finset.sum_add_distrib]

private instance certificate_instance_1002 : OAI.SidorenkoCounterexample.ProofCertificate_1002 := by
  constructor
  intro q0 q1 q2 q3 q4
  exact @certificate_proof_1002 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 q0 q1 q2 q3 q4

theorem certificate_proof_1003 (p : FiniteLaw A) (f g : A → ℝ) :
    p.mean (fun a => f a-g a)=p.mean f-p.mean g := by simp only [mean,mul_sub,Finset.sum_sub_distrib]

private instance certificate_instance_1003 : OAI.SidorenkoCounterexample.ProofCertificate_1003 := by
  constructor
  intro q0 q1 q2 q3 q4
  exact @certificate_proof_1003 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 q0 q1 q2 q3 q4

theorem certificate_proof_1004 (p : FiniteLaw A) (c : ℝ) (f : A → ℝ) :
    p.mean (fun a => c*f a)=c*p.mean f := by unfold mean; rw [Finset.mul_sum]; congr 1; funext a; ring

private instance certificate_instance_1004 : OAI.SidorenkoCounterexample.ProofCertificate_1004 := by
  constructor
  intro q0 q1 q2 q3 q4
  exact @certificate_proof_1004 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 q0 q1 q2 q3 q4

theorem certificate_proof_1005 (p : FiniteLaw A) (f : A → ℝ) (c : ℝ) :
    p.mean (fun a => f a*c)=p.mean f*c := by unfold mean; rw [Finset.sum_mul]; congr 1; funext a; ring

private instance certificate_instance_1005 : OAI.SidorenkoCounterexample.ProofCertificate_1005 := by
  constructor
  intro q0 q1 q2 q3 q4
  exact @certificate_proof_1005 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 q0 q1 q2 q3 q4

omit [DecidableEq I] in
theorem certificate_proof_1006 (p : FiniteLaw A) (f : I → A → ℝ) :
    p.mean (fun a => ∑ i,f i a)=∑ i,p.mean (f i) := by unfold mean; simp_rw [Finset.mul_sum]; rw [Finset.sum_comm]

private instance certificate_instance_1006 : OAI.SidorenkoCounterexample.ProofCertificate_1006 := by
  constructor
  intro q0 q1 q2 q3 q4 q5
  exact @certificate_proof_1006 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 q0 q1 q2 q3 q4 q5

omit [Fintype I] [DecidableEq I] in
theorem certificate_proof_1007 (p : FiniteLaw A) (s : Finset I) (f : I → A → ℝ) :
    p.mean (fun a => ∑ i∈s,f i a)=∑ i∈s,p.mean (f i) := by unfold mean; simp_rw [Finset.mul_sum]; rw [Finset.sum_comm]

private instance certificate_instance_1007 : OAI.SidorenkoCounterexample.ProofCertificate_1007 := by
  constructor
  intro q0 q1 q2 q3 q4 q5
  exact @certificate_proof_1007 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 q0 q1 q2 q3 q4 q5

theorem certificate_proof_1008 (p : FiniteLaw A) {f : A → ℝ} (hf : ∀ a,0≤f a) : 0≤p.mean f :=
  Finset.sum_nonneg (fun a _ => mul_nonneg (p.nonneg a) (hf a))

private instance certificate_instance_1008 : OAI.SidorenkoCounterexample.ProofCertificate_1008 := by
  constructor
  intro q0 q1 q2 q3 q4
  exact @certificate_proof_1008 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 q0 q1 q2 q3 q4

theorem certificate_proof_1009 (p : FiniteLaw A) {f g : A → ℝ} (h : ∀ a,f a≤g a) : p.mean f≤p.mean g :=
  Finset.sum_le_sum (fun a _ => mul_le_mul_of_nonneg_left (h a) (p.nonneg a))

private instance certificate_instance_1009 : OAI.SidorenkoCounterexample.ProofCertificate_1009 := by
  constructor
  intro q0 q1 q2 q3 q4 q5
  exact @certificate_proof_1009 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 q0 q1 q2 q3 q4 q5

theorem certificate_proof_1010 (p : FiniteLaw A) {f : A → ℝ} {c : ℝ} (h : ∀ a,f a≤c) : p.mean f≤c := by
  simpa only [mean_const] using p.mean_mono h

private instance certificate_instance_1010 : OAI.SidorenkoCounterexample.ProofCertificate_1010 := by
  constructor
  intro q0 q1 q2 q3 q4 q5
  exact @certificate_proof_1010 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 q0 q1 q2 q3 q4 q5

theorem certificate_proof_1011 (p : FiniteLaw A) (f : A → ℝ) : |p.mean f|≤p.mean (fun a => |f a|) := by
  calc
    _ ≤ ∑ a,|p.weight a*f a| := Finset.abs_sum_le_sum_abs ..
    _ = _ := by simp only [mean,abs_mul,abs_of_nonneg (p.nonneg _)]

private instance certificate_instance_1011 : OAI.SidorenkoCounterexample.ProofCertificate_1011 := by
  constructor
  intro q0 q1 q2 q3
  exact @certificate_proof_1011 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 q0 q1 q2 q3

theorem certificate_proof_1012 (a : A) (f : A → ℝ) : (dirac a).mean f=f a := by simp [mean,dirac]

private instance certificate_instance_1012 : OAI.SidorenkoCounterexample.ProofCertificate_1012 := by
  constructor
  intro q0 q1 q2 q3
  exact @certificate_proof_1012 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 q0 q1 q2 q3

theorem certificate_proof_1013 [Nonempty A] (f : A → ℝ) : uniform.mean f=uniformMean f := by
  simp only [mean,uniform,uniformMean,div_eq_mul_inv,Finset.sum_mul,mul_comm]

private instance certificate_instance_1013 : OAI.SidorenkoCounterexample.ProofCertificate_1013 := by
  constructor
  intro q0 q1 q2 q3
  exact @certificate_proof_1013 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 q0 q1 q2 q3

theorem certificate_proof_1014 (p : FiniteLaw A) (q : FiniteLaw B) (f : A × B → ℝ) :
    (p.prod q).mean f=p.mean (fun a => q.mean (fun b => f (a,b))) := by
  unfold mean prod; rw [Fintype.sum_prod_type]; simp_rw [Finset.mul_sum,mul_assoc]

private instance certificate_instance_1014 : OAI.SidorenkoCounterexample.ProofCertificate_1014 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6
  exact @certificate_proof_1014 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 q0 q1 q2 q3 q4 q5 q6

theorem certificate_proof_1015 (p : FiniteLaw A) (q : FiniteLaw B) (f : A → B → ℝ) :
    p.mean (fun a => q.mean (f a))=q.mean (fun b => p.mean (fun a => f a b)) := by
  simp only [mean,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro b _
  apply Finset.sum_congr rfl; intro a _; ring

private instance certificate_instance_1015 : OAI.SidorenkoCounterexample.ProofCertificate_1015 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6
  exact @certificate_proof_1015 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 q0 q1 q2 q3 q4 q5 q6

theorem certificate_proof_1016 (p : I → FiniteLaw A) (f : I → A → ℝ) :
    (independent p).mean (fun x => ∏ i,f i (x i))=∏ i,(p i).mean (f i) := by
  simp only [mean,independent,←Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun i a => (p i).weight a*f i a)).symm

private instance certificate_instance_1016 : OAI.SidorenkoCounterexample.ProofCertificate_1016 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6
  exact @certificate_proof_1016 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 q0 q1 q2 q3 q4 q5 q6

theorem certificate_proof_1017 (p : I → FiniteLaw A) (f : I → A → ℝ) :
    (∏ i,(p i).mean (f i))=∑ x : I → A,∏ i,(p i).weight (x i)*f i (x i) := by
  simp only [mean,Fintype.prod_sum]

private instance certificate_instance_1017 : OAI.SidorenkoCounterexample.ProofCertificate_1017 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6
  exact @certificate_proof_1017 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 q0 q1 q2 q3 q4 q5 q6

theorem certificate_proof_1018 (p q : FiniteLaw A) (t : ℝ) (ht : 0≤t) (ht1 : t≤1) (f : A → ℝ) :
    (mixture p q t ht ht1).mean f=t*p.mean f+(1-t)*q.mean f := by
  unfold mean mixture; simp only [add_mul,mul_assoc,Finset.sum_add_distrib,Finset.mul_sum]

private instance certificate_instance_1018 : OAI.SidorenkoCounterexample.ProofCertificate_1018 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7
  exact @certificate_proof_1018 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 q0 q1 q2 q3 q4 q5 q6 q7

theorem certificate_proof_1019 (p : FiniteLaw A) (f : A → B) (g : B → ℝ) :
    (p.map f).mean g=p.mean (g ∘ f) := by
  simp only [mean,map,Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro a _
  simp

private instance certificate_instance_1019 : OAI.SidorenkoCounterexample.ProofCertificate_1019 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6
  exact @certificate_proof_1019 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 q0 q1 q2 q3 q4 q5 q6

theorem certificate_proof_1020 {Q : Type} {l : Filter Q} (p : FiniteLaw A) (f : Q → A → ℝ)
    (g : A → ℝ) (h : ∀ a,Filter.Tendsto (fun q => f q a) l (nhds (g a))) :
    Filter.Tendsto (fun q => p.mean (f q)) l (nhds (p.mean g)) := by
  exact tendsto_finsetSum Finset.univ (fun a _ => (h a).const_mul (p.weight a))

private instance certificate_instance_1020 : OAI.SidorenkoCounterexample.ProofCertificate_1020 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7
  exact @certificate_proof_1020 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 q0 q1 q2 q3 q4 q5 q6 q7

end FiniteLaw
end SidorenkoCounterexample
end
section
namespace SidorenkoCounterexample
open Classical
open scoped BigOperators symmDiff
section BooleanMoments
variable {K : Type} [Fintype K] [DecidableEq K]
theorem certificate_proof_1021 (s : Finset K) (η : K → Bool) :
    boolMonomial s η=∏ k,if k∈s then boolSign (η k) else 1 := by
  simp [boolMonomial,Finset.prod_ite_mem]

private instance certificate_instance_1021 : OAI.SidorenkoCounterexample.ProofCertificate_1021 := by
  constructor
  intro q0 q1 q2 q3 q4
  exact @certificate_proof_1021 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 q0 q1 q2 q3 q4

omit [Fintype K] [DecidableEq K] in
theorem certificate_proof_1022 (s : Finset K) (η : K → Bool) : |boolMonomial s η|=1 := by
  simp [boolMonomial,Finset.abs_prod]

private instance certificate_instance_1022 : OAI.SidorenkoCounterexample.ProofCertificate_1022 := by
  constructor
  intro q0 q1 q2
  exact @certificate_proof_1022 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 q0 q1 q2

theorem certificate_proof_1023 (s t : Finset K) (η : K → Bool) :
    boolMonomial s η*boolMonomial t η=boolMonomial (s ∆ t) η := by
  simp_rw [boolMonomial_asprod]
  rw [←Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl; intro k _
  by_cases hs : k∈s <;> by_cases ht : k∈t <;>
    simp only [Finset.mem_symmDiff,hs,ht,not_true_eq_false,not_false_eq_true,
      and_self,and_false,false_and,or_self,true_or,or_true,ite_true,ite_false,one_mul,mul_one]
  exact (pow_two (boolSign (η k))).symm.trans (boolSign_sq (η k))

private instance certificate_instance_1023 : OAI.SidorenkoCounterexample.ProofCertificate_1023 := by
  constructor
  intro q0 q1 q2 q3 q4 q5
  exact @certificate_proof_1023 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 q0 q1 q2 q3 q4 q5

theorem certificate_proof_1024 : uniformMean boolSign=0 := by
  norm_num [uniformMean,Fintype.sum_bool,boolSign]

private instance certificate_instance_1024 : OAI.SidorenkoCounterexample.ProofCertificate_1024 := by
  constructor
  exact @certificate_proof_1024 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30

theorem certificate_proof_1025 (s : Finset K) : uniformMean (boolMonomial s)=if s=∅ then 1 else 0 := by
  rw [uniformMean_congr (boolMonomial_asprod s)]
  rw [uniformMean_pi_product (fun k b => if k∈s then boolSign b else 1)]
  by_cases hs : s=∅
  · simp [hs,uniformMean_const]
  · rw [if_neg hs]
    obtain ⟨k,hk⟩ := Finset.nonempty_iff_ne_empty.mpr hs
    apply Finset.prod_eq_zero (Finset.mem_univ k)
    simp only [hk,ite_true,boolSign_mean]

private instance certificate_instance_1025 : OAI.SidorenkoCounterexample.ProofCertificate_1025 := by
  constructor
  intro q0 q1 q2 q3
  exact @certificate_proof_1025 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 q0 q1 q2 q3

theorem certificate_proof_1026 (s t : Finset K) :
    uniformMean (fun η => boolMonomial s η*boolMonomial t η)=if s=t then 1 else 0 := by
  simp_rw [boolMonomial_mul,boolMonomial_mean,Finset.symmDiff_eq_empty]

private instance certificate_instance_1026 : OAI.SidorenkoCounterexample.ProofCertificate_1026 := by
  constructor
  intro q0 q1 q2 q3 q4
  exact @certificate_proof_1026 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 q0 q1 q2 q3 q4

theorem certificate_proof_1027 (s : Finset K) (hs : s≠∅) (a : ℝ) (ha : |a|≤1) (f : (K → Bool) → ℝ) :
    (tiltLaw s hs a ha).mean f=uniformMean (fun η => (1+a*boolMonomial s η)*f η) := by
  unfold FiniteLaw.mean tiltLaw uniformMean
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl; intro η _; ring

private instance certificate_instance_1027 : OAI.SidorenkoCounterexample.ProofCertificate_1027 := by
  constructor
  intro c0 c1 c2 c3 c4 q0 q1 q2 q3 q4 q5 q6 q7
  exact @certificate_proof_1027 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 q0 q1 q2 q3 q4 q5 q6 q7

theorem certificate_proof_1028 (s t : Finset K) (hs : s≠∅) (a : ℝ) (ha : |a|≤1) :
    (tiltLaw s hs a ha).mean (boolMonomial t)=(if t=∅ then 1 else 0)+a*(if t=s then 1 else 0) := by
  rw [tiltLaw_mean]
  simp_rw [add_mul,one_mul,mul_assoc]
  rw [uniformMean_add,uniformMean_mul,boolMonomial_mean,boolMonomial_orthog]
  simp only [eq_comm (a := s) (b := t)]

private instance certificate_instance_1028 : OAI.SidorenkoCounterexample.ProofCertificate_1028 := by
  constructor
  intro c0 c1 c2 c3 c4 q0 q1 q2 q3 q4 q5 q6 q7
  exact @certificate_proof_1028 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 q0 q1 q2 q3 q4 q5 q6 q7

omit [Fintype K] in
theorem certificate_proof_1029 (z : Activation K) : activationPhi ∅ z=1 := by
  simp [activationPhi]

private instance certificate_instance_1029 : OAI.SidorenkoCounterexample.ProofCertificate_1029 := by
  constructor
  intro q0 q1 q2
  exact @certificate_proof_1029 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 q0 q1 q2

theorem certificate_proof_1030 (α β : Finset K) (z : Activation K) :
    activationPhi α z*activationPhi β z=
      if α∪β⊆z.1 then boolMonomial (α ∆ β) z.2 else 0 := by
  unfold activationPhi
  simp only [Finset.union_subset_iff]
  by_cases hα : α⊆z.1 <;> by_cases hβ : β⊆z.1 <;> simp [hα,hβ,boolMonomial_mul]

private instance certificate_instance_1030 : OAI.SidorenkoCounterexample.ProofCertificate_1030 := by
  constructor
  intro q0 q1 q2 q3 q4 q5
  exact @certificate_proof_1030 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 q0 q1 q2 q3 q4 q5

theorem certificate_proof_1031 (α β : Finset K) (h : Disjoint α β) (z : Activation K) :
    activationPhi α z*activationPhi β z=activationPhi (α∪β) z := by
  rw [activationPhi_mul,Finset.symmDiff_eq_union h]
  rfl

private instance certificate_instance_1031 : OAI.SidorenkoCounterexample.ProofCertificate_1031 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6
  exact @certificate_proof_1031 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 q0 q1 q2 q3 q4 q5 q6

theorem certificate_proof_1032 (S Γ α : Finset K) (hΓ : Γ≠∅) (a : ℝ) (ha : |a|≤1) :
    (branchLaw S Γ hΓ a ha).mean (activationPhi α)=
      if α⊆S then (if α=∅ then 1 else 0)+a*(if α=Γ then 1 else 0) else 0 := by
  unfold branchLaw
  rw [FiniteLaw.mean_prod,FiniteLaw.mean_dirac]
  by_cases hα : α⊆S
  · simp only [activationPhi,hα,ite_true]; exact tiltLaw_monomial Γ α hΓ a ha
  · simp only [activationPhi,hα,ite_false,FiniteLaw.mean_const]

private instance certificate_instance_1032 : OAI.SidorenkoCounterexample.ProofCertificate_1032 := by
  constructor
  intro c0 c1 c2 c3 c4 q0 q1 q2 q3 q4 q5 q6 q7 q8
  exact @certificate_proof_1032 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 q0 q1 q2 q3 q4 q5 q6 q7 q8

theorem certificate_proof_1033 (S Γ α β : Finset K) (hΓ : Γ≠∅) (a : ℝ) (ha : |a|≤1) :
    (branchLaw S Γ hΓ a ha).mean (fun z => activationPhi α z*activationPhi β z)=
      if α∪β⊆S then (if α=β then 1 else 0)+a*(if α ∆ β=Γ then 1 else 0) else 0 := by
  unfold branchLaw
  rw [FiniteLaw.mean_prod,FiniteLaw.mean_dirac]
  simp_rw [activationPhi_mul]
  by_cases h : α∪β⊆S
  · simp only [h,ite_true]
    rw [tiltLaw_monomial]
    simp only [Finset.symmDiff_eq_empty]
  · simp only [h,ite_false,FiniteLaw.mean_const]

private instance certificate_instance_1033 : OAI.SidorenkoCounterexample.ProofCertificate_1033 := by
  constructor
  intro c0 c1 c2 c3 c4 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9
  exact @certificate_proof_1033 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9

theorem certificate_proof_1034 (M Γ α : Finset K) (hΓ : Γ≠∅) (hΓM : Γ⊆M)
    (a : ℝ) (ha : |a|≤1) (hα : α≠∅) : (baseActivation M Γ hΓ a ha).mean (activationPhi α)=0 := by
  unfold baseActivation
  rw [FiniteLaw.mean_mixture,branchLaw_phi,branchLaw_phi]
  by_cases h : α=Γ
  · subst α; simp [hΓ,hΓM]; ring
  · simp [h,hα]

private instance certificate_instance_1034 : OAI.SidorenkoCounterexample.ProofCertificate_1034 := by
  constructor
  intro c0 c1 c2 c3 c4 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10
  exact @certificate_proof_1034 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10

theorem certificate_proof_1035 (p : FiniteLaw (Activation K)) : activationMoment p ∅ ∅=1 := by
  simp [activationMoment]

private instance certificate_instance_1035 : OAI.SidorenkoCounterexample.ProofCertificate_1035 := by
  constructor
  intro q0 q1 q2 q3
  exact @certificate_proof_1035 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 q0 q1 q2 q3

theorem certificate_proof_1036 (p : FiniteLaw (Activation K))
    (hp : ∀ α,α≠∅ → p.mean (activationPhi α)=0) (α β : Finset K)
    (hd : Disjoint α β) (hn : α∪β≠∅) : activationMoment p α β=0 := by
  unfold activationMoment
  simp_rw [activationPhi_disjoint α β hd]
  exact hp _ hn

private instance certificate_instance_1036 : OAI.SidorenkoCounterexample.ProofCertificate_1036 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8
  exact @certificate_proof_1036 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 q0 q1 q2 q3 q4 q5 q6 q7 q8

theorem certificate_proof_1037 (M Γ α β : Finset K) (hΓ : Γ≠∅)
    (a : ℝ) (ha : |a|≤1) : activationMoment (baseActivation M Γ hΓ a ha) α β=
    (1/2)*(if α∪β⊆M then (if α=β then 1 else 0)+a*(if α ∆ β=Γ then 1 else 0) else 0)+
    (1/2)*(if α∪β⊆Γ then (if α=β then 1 else 0)-a*(if α ∆ β=Γ then 1 else 0) else 0) := by
  unfold activationMoment baseActivation
  rw [FiniteLaw.mean_mixture,branchLaw_second,branchLaw_second]
  norm_num only [show (1:ℝ)-1/2=1/2 by norm_num,neg_mul,←sub_eq_add_neg]

private instance certificate_instance_1037 : OAI.SidorenkoCounterexample.ProofCertificate_1037 := by
  constructor
  intro c0 c1 c2 c3 c4 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9
  exact @certificate_proof_1037 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9

end BooleanMoments
end SidorenkoCounterexample
end
end OAI
namespace OAI
section
namespace SidorenkoCounterexample
open Classical
open scoped BigOperators symmDiff
theorem certificate_proof_1038 (k : ActCorner) (e : Fin 33) :
    k∈pairCorners e ↔ cornerPairL k=e ∨ cornerPairR k=e := by simp [pairCorners]

private instance certificate_instance_1038 : OAI.SidorenkoCounterexample.ProofCertificate_1038 := by
  constructor
  intro q0 q1
  exact @certificate_proof_1038 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 q0 q1

lemma certificate_proof_1039 : pairCorners 0=pairCornerTable 0 := by decide

private instance certificate_instance_1039 : OAI.SidorenkoCounterexample.ProofCertificate_1039 := by
  constructor
  exact @certificate_proof_1039 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30

lemma certificate_proof_1040 : pairCorners 1=pairCornerTable 1 := by decide

private instance certificate_instance_1040 : OAI.SidorenkoCounterexample.ProofCertificate_1040 := by
  constructor
  exact @certificate_proof_1040 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30

lemma certificate_proof_1041 : pairCorners 2=pairCornerTable 2 := by decide

private instance certificate_instance_1041 : OAI.SidorenkoCounterexample.ProofCertificate_1041 := by
  constructor
  exact @certificate_proof_1041 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30

lemma certificate_proof_1042 : pairCorners 3=pairCornerTable 3 := by decide

private instance certificate_instance_1042 : OAI.SidorenkoCounterexample.ProofCertificate_1042 := by
  constructor
  exact @certificate_proof_1042 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30

lemma certificate_proof_1043 : pairCorners 4=pairCornerTable 4 := by decide

private instance certificate_instance_1043 : OAI.SidorenkoCounterexample.ProofCertificate_1043 := by
  constructor
  exact @certificate_proof_1043 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30

lemma certificate_proof_1044 : pairCorners 5=pairCornerTable 5 := by decide

private instance certificate_instance_1044 : OAI.SidorenkoCounterexample.ProofCertificate_1044 := by
  constructor
  exact @certificate_proof_1044 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30

lemma certificate_proof_1045 : pairCorners 6=pairCornerTable 6 := by decide

private instance certificate_instance_1045 : OAI.SidorenkoCounterexample.ProofCertificate_1045 := by
  constructor
  exact @certificate_proof_1045 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30

lemma certificate_proof_1046 : pairCorners 7=pairCornerTable 7 := by decide

private instance certificate_instance_1046 : OAI.SidorenkoCounterexample.ProofCertificate_1046 := by
  constructor
  exact @certificate_proof_1046 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30

lemma certificate_proof_1047 : pairCorners 8=pairCornerTable 8 := by decide

private instance certificate_instance_1047 : OAI.SidorenkoCounterexample.ProofCertificate_1047 := by
  constructor
  exact @certificate_proof_1047 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30

lemma certificate_proof_1048 : pairCorners 9=pairCornerTable 9 := by decide

private instance certificate_instance_1048 : OAI.SidorenkoCounterexample.ProofCertificate_1048 := by
  constructor
  exact @certificate_proof_1048 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30

end SidorenkoCounterexample
end
end OAI

theorem solution : OAI.SidorenkoCounterexample.ProofCertificate_0988 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0989 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0990 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0991 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0992 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0993 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0994 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0995 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0996 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0997 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0998 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0999 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1000 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1001 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1002 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1003 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1004 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1005 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1006 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1007 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1008 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1009 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1010 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1011 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1012 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1013 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1014 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1015 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1016 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1017 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1018 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1019 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1020 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1021 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1022 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1023 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1024 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1025 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1026 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1027 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1028 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1029 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1030 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1031 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1032 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1033 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1034 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1035 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1036 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1037 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1038 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1039 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1040 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1041 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1042 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1043 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1044 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1045 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1046 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1047 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1048 := by
  exact ⟨inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance⟩
end

