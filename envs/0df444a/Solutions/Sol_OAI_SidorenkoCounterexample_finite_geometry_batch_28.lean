-- Prove2me | solution 1 for OAI.SidorenkoCounterexample.finite_geometry_batch_28
-- status  : ACCEPTED   (prove)
-- author  : @abcdefg
-- created : 2026-10-09T06:30:24.867454+00:00
-- url     : https://prove2.me/submissions/84fe9c24-2b76-483a-8b34-4a8e3e36eab7

import Definitions.Def_SidorenkoCertificateBundleB
set_option linter.unusedVariables false
section
variable [p0 : OAI.SidorenkoCounterexample.ProofCertificate_0643]
  [p1 : OAI.SidorenkoCounterexample.ProofCertificate_0653]
  [p2 : OAI.SidorenkoCounterexample.ProofCertificate_0656]
  [p3 : OAI.SidorenkoCounterexample.ProofCertificate_0657]
  [p4 : OAI.SidorenkoCounterexample.ProofCertificate_0659]
  [p5 : OAI.SidorenkoCounterexample.ProofCertificate_0660]
  [p6 : OAI.SidorenkoCounterexample.ProofCertificate_0661]
  [p7 : OAI.SidorenkoCounterexample.ProofCertificate_0663]
  [p8 : OAI.SidorenkoCounterexample.ProofCertificate_0754]
  [p9 : OAI.SidorenkoCounterexample.ProofCertificate_0791]
  [p10 : OAI.SidorenkoCounterexample.ProofCertificate_0813]
  [p11 : OAI.SidorenkoCounterexample.ProofCertificate_0814]
  [p12 : OAI.SidorenkoCounterexample.ProofCertificate_0815]
  [p13 : OAI.SidorenkoCounterexample.ProofCertificate_0816]
  [p14 : OAI.SidorenkoCounterexample.ProofCertificate_0822]
  [p15 : OAI.SidorenkoCounterexample.ProofCertificate_0823]
  [p16 : OAI.SidorenkoCounterexample.ProofCertificate_0832]
  [p17 : OAI.SidorenkoCounterexample.ProofCertificate_0833]
  [p18 : OAI.SidorenkoCounterexample.ProofCertificate_0834]
  [p19 : OAI.SidorenkoCounterexample.ProofCertificate_0836]
  [p20 : OAI.SidorenkoCounterexample.ProofCertificate_0837]
  [p21 : OAI.SidorenkoCounterexample.ProofCertificate_0838]
  [p22 : OAI.SidorenkoCounterexample.ProofCertificate_0840]
  [p23 : OAI.SidorenkoCounterexample.ProofCertificate_0841]
  [p24 : OAI.SidorenkoCounterexample.ProofCertificate_0842]
  [p25 : OAI.SidorenkoCounterexample.ProofCertificate_0843]
include p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25

namespace OAI
section
namespace SidorenkoCounterexample
open Module LinearMap
open scoped Matrix BigOperators
section Count
variable {I K V : Type} [Fintype I] [Field K] [Fintype K] [DecidableEq K]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]
end Count
section Identities
variable {K : Type} [Field K] [Fintype K] [DecidableEq K] {D r : ℕ}
end Identities
end SidorenkoCounterexample
end
section
namespace SidorenkoCounterexample
open Module Filter
open scoped BigOperators
section Coeff
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
end Coeff
end SidorenkoCounterexample
end
section
namespace SidorenkoCounterexample
open Module
open scoped BigOperators
section Sizes
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
end Sizes
section Bounds
variable {K I : Type} [Field K] [Fintype K] [DecidableEq K] [Fintype I] {D r : ℕ}
end Bounds
end SidorenkoCounterexample
end
section
namespace SidorenkoCounterexample
open scoped BigOperators
section Mean
variable {I A B : Type} [Fintype I] [DecidableEq I] [Fintype A] [Fintype B]
end Mean
end SidorenkoCounterexample
end
section
namespace SidorenkoCounterexample
open scoped BigOperators
open Module
section Inverting
variable {K : Type} [Field K] [Fintype K]
end Inverting
end SidorenkoCounterexample
end
section
namespace SidorenkoCounterexample
open Module Classical
open scoped Matrix BigOperators
section Center
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
end Center
end SidorenkoCounterexample
end
section
namespace SidorenkoCounterexample
open Module Classical
open scoped BigOperators
section Means
variable {A B : Type} [Fintype A] [Fintype B]
variable [AddCommGroup A]
end Means
section Range
variable {K : Type} [Field K] [Fintype K] [DecidableEq K] {D : ℕ}
omit [DecidableEq K] in
theorem certificate_proof_0844 (f : SymMatrix K D → SymMatrix K D → ℝ) :
    uniformMean (fun B => uniformMean fun C =>
      f (symmetricInverse D B) (symmetricInverse D B-symmetricInverse D C)) =
        uniformMean (fun L => uniformMean fun Q => f Q L) := by
  calc
    _ = uniformMean (fun B => uniformMean fun T => f (symmetricInverse D B) (symmetricInverse D B-T)) := by
      apply uniformMean_congr
      intro B
      exact uniformMean_inverse (fun T => f (symmetricInverse D B) (symmetricInverse D B-T))
    _ = uniformMean (fun B => uniformMean fun L => f (symmetricInverse D B) L) := by
      apply uniformMean_congr
      intro B
      exact uniformMean_subLeft (symmetricInverse D B) (f (symmetricInverse D B))
    _ = uniformMean (fun Q => uniformMean fun L => f Q L) :=
      uniformMean_inverse (fun Q => uniformMean fun L => f Q L)
    _ = _ := uniformMean_swap _

private instance certificate_instance_0844 : OAI.SidorenkoCounterexample.ProofCertificate_0844 := by
  constructor
  intro q0 q1 q2 q3 q4
  exact @certificate_proof_0844 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 q0 q1 q2 q3 q4

end Range
end SidorenkoCounterexample
end
section
namespace SidorenkoCounterexample
open Module Classical Filter
open scoped BigOperators
theorem certificate_proof_0845 (c f m : ℝ) (hc : 0 ≤ c) :
    |c*f-m| ≤ |c/2-m|+c*|f-1/2| := by
  calc
    _ = |(c/2-m)+c*(f-1/2)| := by congr 1; ring
    _ ≤ |c/2-m|+|c*(f-1/2)| := abs_add_le _ _
    _ = _ := by rw [abs_mul,abs_of_nonneg hc]

private instance certificate_instance_0845 : OAI.SidorenkoCounterexample.ProofCertificate_0845 := by
  constructor
  intro q0 q1 q2 q3
  exact @certificate_proof_0845 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 q0 q1 q2 q3

section Error
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
theorem certificate_proof_0846 (r : ℕ) (ξ : ℤ) (Q L : SymMatrix K (2*r)) :
    0 ≤ splitFractionError r ξ Q L := by unfold splitFractionError; split <;> positivity

private instance certificate_instance_0846 : OAI.SidorenkoCounterexample.ProofCertificate_0846 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7
  exact @certificate_proof_0846 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 q0 q1 q2 q3 q4 q5 q6 q7

theorem certificate_proof_0847 (r : ℕ) (ξ ζ : ℤ) (B : SymMatrix K (2*r)) :
    pairError r ξ ζ B ≤ |pairCoefficient (K := K) r ξ ζ/2-2|+
      pairCoefficient (K := K) r ξ ζ*|pairRestrictionFraction (symmetricInverse (2*r) B) r ξ-1/2| := by
  have hc := pairCoefficient_nonneg (K := K) r ξ ζ
  unfold pairError
  split_ifs with hB hm
  · rw [pairLocal_match r ξ ζ B hB hm]
    exact scalar_fraction_error _ _ _ hc
  · rw [pairLocal_mismatch r ξ ζ B hB hm]
    simp only [sub_zero,abs_zero]
    positivity
  · positivity

private instance certificate_instance_0847 : OAI.SidorenkoCounterexample.ProofCertificate_0847 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7
  exact @certificate_proof_0847 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 q0 q1 q2 q3 q4 q5 q6 q7

theorem certificate_proof_0848 (hK : ringChar K≠2) (r : ℕ) {ξ ζ θ : ℤ}
    (hξ : ξ=1 ∨ ξ= -1) (hζ : ζ=1 ∨ ζ= -1) (hθ : θ=1 ∨ θ= -1)
    (B C : SymMatrix K (2*r)) :
    tripleError r ξ ζ θ B C ≤ |tripleCoefficient (K := K) r ξ ζ θ/2-8|+
      tripleCoefficient (K := K) r ξ ζ θ * splitFractionError r ξ
        (symmetricInverse (2*r) B) (symmetricInverse (2*r) B-symmetricInverse (2*r) C) := by
  have hc := tripleCoefficient_nonneg (K := K) r ξ ζ θ
  have hf := splitFractionError_nonneg r ξ (symmetricInverse (2*r) B)
    (symmetricInverse (2*r) B-symmetricInverse (2*r) C)
  unfold tripleError
  split_ifs with ht hm
  · obtain ⟨hB,hC,hBC⟩ := ht
    have hs : matrixSplit r (symmetricInverse (2*r) B-symmetricInverse (2*r) C) := by
      simp only [matrixSplit,symmetricInverse,hB,hC,ite_false,Submodule.coe_sub]
      exact ⟨Matrix.nondegenerate_iff_det_ne_zero.mp
        (Matrix.nondegenerate_toBilin'_iff.mp (inverse_difference_nondegenerate (2*r) B C hB hC hBC)),
        matching_inverse_difference_split r B C hB hC hBC hξ hζ hθ hm⟩
    rw [tripleLocal_match hK r B C hB hC hBC hξ hζ hθ hm,splitFractionError,if_pos hs]
    simp only [symmetricInverse,hB,hC,ite_false,Submodule.coe_sub]
    exact scalar_fraction_error _ _ _ hc
  · rw [tripleLocal_mismatch r ξ ζ θ B C ht.1 ht.2.1 ht.2.2 hm]
    simp only [sub_zero,abs_zero]
    positivity
  · positivity

private instance certificate_instance_0848 : OAI.SidorenkoCounterexample.ProofCertificate_0848 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13
  exact @certificate_proof_0848 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13

theorem certificate_proof_0849 (hK : ringChar K≠2) (r : ℕ) (hr : 1<r)
    {ξ : ℤ} (hξ : ξ=1 ∨ ξ= -1) (L : SymMatrix K (2*r)) :
    uniformMean (fun Q => splitFractionError r ξ Q L) ≤
      Real.sqrt (((r : ℝ)+1)/(Fintype.card K : ℝ)) := by
  by_cases h : matrixSplit r L
  · simp only [splitFractionError,h,ite_true]
    exact isotropicRestrictionFraction_L1 r hr _
      (Matrix.isSymm_toBilin'_iff_isSymm.mpr L.property)
      (Matrix.nondegenerate_toBilin'_iff.mpr (Matrix.nondegenerate_iff_det_ne_zero.mpr h.1))
      hK h.2 hξ
  · simp only [splitFractionError,h,ite_false,uniformMean_const]
    positivity

private instance certificate_instance_0849 : OAI.SidorenkoCounterexample.ProofCertificate_0849 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9
  exact @certificate_proof_0849 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9

theorem certificate_proof_0850 (hK : ringChar K≠2) (r : ℕ) (hr : 0<r)
    {ξ ζ : ℤ} (hξ : ξ=1 ∨ ξ= -1) :
    uniformMean (pairError (K := K) r ξ ζ) ≤ |pairCoefficient (K := K) r ξ ζ/2-2|+
      pairCoefficient (K := K) r ξ ζ * Real.sqrt (((r : ℝ)+1)/(Fintype.card K : ℝ)) := by
  apply (uniformMean_mono (pairError_pointwise r ξ ζ)).trans
  rw [uniformMean_add,uniformMean_const,uniformMean_mul,
    uniformMean_inverse (fun Q => |pairRestrictionFraction Q r ξ-1/2|)]
  exact add_le_add le_rfl (mul_le_mul_of_nonneg_left (pairRestrictionFraction_L1 r hr hK hξ)
    (pairCoefficient_nonneg (K := K) r ξ ζ))

private instance certificate_instance_0850 : OAI.SidorenkoCounterexample.ProofCertificate_0850 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9
  exact @certificate_proof_0850 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9

theorem certificate_proof_0851 (hK : ringChar K≠2) (r : ℕ) (hr : 1<r)
    {ξ ζ θ : ℤ} (hξ : ξ=1 ∨ ξ= -1) (hζ : ζ=1 ∨ ζ= -1) (hθ : θ=1 ∨ θ= -1) :
    uniformMean (fun B => uniformMean (fun C => tripleError (K := K) r ξ ζ θ B C)) ≤
      |tripleCoefficient (K := K) r ξ ζ θ/2-8|+
        tripleCoefficient (K := K) r ξ ζ θ * Real.sqrt (((r : ℝ)+1)/(Fintype.card K : ℝ)) := by
  apply (uniformMean_mono (fun B => uniformMean_mono (tripleError_pointwise hK r hξ hζ hθ B))).trans
  simp_rw [uniformMean_add,uniformMean_const,uniformMean_mul]
  rw [uniformMean_inverse_difference]
  exact add_le_add le_rfl (mul_le_mul_of_nonneg_left
    (uniformMean_bound (splitFractionError_mean hK r hr hξ)) (tripleCoefficient_nonneg (K := K) r ξ ζ θ))

private instance certificate_instance_0851 : OAI.SidorenkoCounterexample.ProofCertificate_0851 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12
  exact @certificate_proof_0851 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12

end Error
end SidorenkoCounterexample
end
section
namespace SidorenkoCounterexample
open Module Classical Filter
open scoped BigOperators
section Bounds
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
theorem certificate_proof_0852 (r : ℕ) (ξ ζ : ℤ) (B : SymMatrix K (2*r)) : 0≤pairLocal r ξ ζ B :=
  uniformMean_nonneg fun _ => mul_nonneg (rankKernel_nonneg ..) (rankKernel_nonneg ..)

private instance certificate_instance_0852 : OAI.SidorenkoCounterexample.ProofCertificate_0852 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7
  exact @certificate_proof_0852 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 q0 q1 q2 q3 q4 q5 q6 q7

theorem certificate_proof_0853 (r : ℕ) (ξ ζ θ : ℤ) (B C : SymMatrix K (2*r)) :
    0≤tripleLocal r ξ ζ θ B C :=
  uniformMean_nonneg fun _ => mul_nonneg
    (mul_nonneg (rankKernel_nonneg ..) (rankKernel_nonneg ..)) (rankKernel_nonneg ..)

private instance certificate_instance_0853 : OAI.SidorenkoCounterexample.ProofCertificate_0853 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9
  exact @certificate_proof_0853 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9

theorem certificate_proof_0854 (r : ℕ) (ξ ζ : ℤ) (B : SymMatrix K (2*r)) : 0≤pairError r ξ ζ B := by
  unfold pairError; split <;> positivity

private instance certificate_instance_0854 : OAI.SidorenkoCounterexample.ProofCertificate_0854 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7
  exact @certificate_proof_0854 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 q0 q1 q2 q3 q4 q5 q6 q7

theorem certificate_proof_0855 (r : ℕ) (ξ ζ θ : ℤ) (B C : SymMatrix K (2*r)) :
    0≤tripleError r ξ ζ θ B C := by unfold tripleError; split <;> positivity

private instance certificate_instance_0855 : OAI.SidorenkoCounterexample.ProofCertificate_0855 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9
  exact @certificate_proof_0855 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9

theorem certificate_proof_0856 (r : ℕ) (ξ ζ : ℤ) (B : SymMatrix K (2*r)) (hB : B.val.det≠0) :
    pairLocal r ξ ζ B ≤ pairCoefficient (K := K) r ξ ζ := by
  by_cases hm : pairMatch r ξ ζ B
  · rw [pairLocal_match r ξ ζ B hB hm]
    exact mul_le_of_le_one_right (pairCoefficient_nonneg ..) (pairRestrictionFraction_range _ _ _).2
  · rw [pairLocal_mismatch r ξ ζ B hB hm]
    exact pairCoefficient_nonneg ..

private instance certificate_instance_0856 : OAI.SidorenkoCounterexample.ProofCertificate_0856 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8
  exact @certificate_proof_0856 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 q0 q1 q2 q3 q4 q5 q6 q7 q8

theorem certificate_proof_0857 (hK : ringChar K≠2) (r : ℕ) {ξ ζ θ : ℤ}
    (hξ : ξ=1 ∨ ξ= -1) (hζ : ζ=1 ∨ ζ= -1) (hθ : θ=1 ∨ θ= -1)
    (B C : SymMatrix K (2*r)) (hB : B.val.det≠0) (hC : C.val.det≠0) (hBC : (C-B).val.det≠0) :
    tripleLocal r ξ ζ θ B C ≤ tripleCoefficient (K := K) r ξ ζ θ := by
  by_cases hm : tripleMatch r ξ ζ θ B C
  · rw [tripleLocal_match hK r B C hB hC hBC hξ hζ hθ hm]
    exact mul_le_of_le_one_right (tripleCoefficient_nonneg ..) (isotropicRestrictionFraction_range _ _ _ _).2
  · rw [tripleLocal_mismatch r ξ ζ θ B C hB hC hBC hm]
    exact tripleCoefficient_nonneg ..

private instance certificate_instance_0857 : OAI.SidorenkoCounterexample.ProofCertificate_0857 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16
  exact @certificate_proof_0857 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16

end Bounds
theorem certificate_proof_0858 (r : ℕ) :
    Tendsto (fun q : OddPrime => Real.sqrt (((r : ℝ)+1)/(q.val : ℝ))) primeInfinity (nhds 0) := by
  have h := ((tendsto_inv_atTop_zero (𝕜 := ℝ)).comp primeInfinity_real_tendsto).const_mul ((r : ℝ)+1)
  have hs := Real.continuous_sqrt.continuousAt.tendsto.comp h
  simpa only [mul_zero,Real.sqrt_zero,Function.comp_def,←div_eq_mul_inv] using hs

private instance certificate_instance_0858 : OAI.SidorenkoCounterexample.ProofCertificate_0858 := by
  constructor
  intro q0
  exact @certificate_proof_0858 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 q0

theorem certificate_proof_0859 (r : ℕ) (hr : 0<r) {ξ ζ : ℤ}
    (hξ : ξ=1 ∨ ξ= -1) (hζ : ζ=1 ∨ ζ= -1) :
    Tendsto (fun q : OddPrime => uniformMean (pairError (K := ZMod q.val) r ξ ζ)) primeInfinity (nhds 0) := by
  have hc := pairCoefficient_tendsto r hr hξ hζ
  have ha := ((hc.div_const 2).sub_const 2).abs
  have hb := hc.mul (localFraction_error_tendsto r)
  have h := ha.add hb
  norm_num only at h
  apply squeeze_zero (fun q => uniformMean_nonneg (pairError_nonneg r ξ ζ)) (fun q => ?_) h
  simpa only [ZMod.card] using pairError_mean (K := ZMod q.val)
    (by simpa only [ZMod.ringChar_zmod_n] using q.property.2) r hr hξ

private instance certificate_instance_0859 : OAI.SidorenkoCounterexample.ProofCertificate_0859 := by
  constructor
  intro q0 q1 q2 q3 q4 q5
  exact @certificate_proof_0859 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 q0 q1 q2 q3 q4 q5

theorem certificate_proof_0860 (r : ℕ) (hr : 1<r) {ξ ζ θ : ℤ}
    (hξ : ξ=1 ∨ ξ= -1) (hζ : ζ=1 ∨ ζ= -1) (hθ : θ=1 ∨ θ= -1) :
    Tendsto (fun q : OddPrime => uniformMean (fun B => uniformMean
      (fun C => tripleError (K := ZMod q.val) r ξ ζ θ B C))) primeInfinity (nhds 0) := by
  have hc := tripleCoefficient_tendsto r (by omega) hξ hζ hθ
  have ha := ((hc.div_const 2).sub_const 8).abs
  have hb := hc.mul (localFraction_error_tendsto r)
  have h := ha.add hb
  norm_num only at h
  apply squeeze_zero (fun q => uniformMean_nonneg fun B => uniformMean_nonneg (tripleError_nonneg r ξ ζ θ B))
    (fun q => ?_) h
  simpa only [ZMod.card] using tripleError_mean (K := ZMod q.val)
    (by simpa only [ZMod.ringChar_zmod_n] using q.property.2) r hr hξ hζ hθ

private instance certificate_instance_0860 : OAI.SidorenkoCounterexample.ProofCertificate_0860 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7
  exact @certificate_proof_0860 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 q0 q1 q2 q3 q4 q5 q6 q7

end SidorenkoCounterexample
end
end OAI
namespace OAI
section
namespace SidorenkoCounterexample
open scoped BigOperators
open Module
section Gauss
variable {K V : Type} [Field K] [Fintype K]
  [AddCommGroup V] [Module K V] [Fintype V]
theorem certificate_proof_0861 (ψ : AddChar K ℂ) (a : K) :
    star (ψ a) = (ψ a)⁻¹ := (Complex.inv_eq_conj (ψ.norm_apply a)).symm

private instance certificate_instance_0861 : OAI.SidorenkoCounterexample.ProofCertificate_0861 := by
  constructor
  intro q0 q1 q2 q3 q4
  exact @certificate_proof_0861 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 q0 q1 q2 q3 q4

omit [Module K V] in
theorem certificate_proof_0862 (ψ : AddChar K ℂ) (f : V → K) :
    ‖∑ x, ψ (f x)‖ ^ 2 = ‖∑ u, ∑ z, ψ (f (z+u) - f z)‖ := by
  classical
  have h : (∑ u, ∑ z, ψ (f (z+u) - f z)) =
      (∑ x, ψ (f x)) * star (∑ x, ψ (f x)) := by
    simp only [AddChar.map_sub_eq_div, div_eq_mul_inv, ← char_conj]
    rw [Finset.sum_comm]
    simp only [← Finset.sum_mul]
    have ht (z : V) : (∑ u, ψ (f (z+u))) = ∑ x, ψ (f x) :=
      Fintype.sum_equiv (Equiv.addLeft z) _ _ (fun _ => rfl)
    simp only [ht, ← Finset.mul_sum, star_sum]
  rw [h, norm_mul, norm_star, pow_two]

private instance certificate_instance_0862 : OAI.SidorenkoCounterexample.ProofCertificate_0862 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7
  exact @certificate_proof_0862 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 q0 q1 q2 q3 q4 q5 q6 q7

omit [Fintype K] in
theorem certificate_proof_0863 (ψ : AddChar K ℂ) (hψ : ψ ≠ 0)
    (f : V →ₗ[K] K) (hf : f ≠ 0) : ∑ x, ψ (f x) = 0 := by
  classical
  have hsurj : Function.Surjective f := by
    have hex : ∃ x, f x ≠ 0 := by
      by_contra! h
      exact hf (LinearMap.ext h)
    obtain ⟨x, hx⟩ := hex
    intro a
    refine ⟨(a / f x) • x, ?_⟩
    simp [hx]
  change ∑ x, (ψ.compAddMonoidHom f.toAddMonoidHom) x = 0
  apply AddChar.sum_eq_zero_iff_ne_zero.mpr
  intro heq
  apply hψ
  ext a
  obtain ⟨x, rfl⟩ := hsurj a
  exact congrArg (fun χ : AddChar V ℂ => χ x) heq

private instance certificate_instance_0863 : OAI.SidorenkoCounterexample.ProofCertificate_0863 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9
  exact @certificate_proof_0863 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9

omit [Fintype K] [Fintype V] in
theorem certificate_proof_0864 (B : LinearMap.BilinForm K V) (hB : B.IsSymm)
    (l : V →ₗ[K] K) (c : K) (z u : V) :
    (B (z+u) (z+u) + l (z+u) + c) - (B z z + l z + c) =
      B u u + l u + (2 : K) * B u z := by
  simp only [map_add, LinearMap.add_apply, hB.eq z u]
  ring

private instance certificate_instance_0864 : OAI.SidorenkoCounterexample.ProofCertificate_0864 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10
  exact @certificate_proof_0864 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10

theorem certificate_proof_0865 (ψ : AddChar K ℂ) (hψ : ψ ≠ 0)
    (hodd : (2 : K) ≠ 0) (B : LinearMap.BilinForm K V) (hB : B.IsSymm)
    (l : V →ₗ[K] K) (c : K) :
    ‖∑ x, ψ (B x x + l x + c)‖ ^ 2 ≤
      (Fintype.card V : ℝ) * Nat.card B.ker := by
  classical
  rw [character_differencing]
  simp only [quadratic_difference B hB, AddChar.map_add_eq_mul]
  have hi (u : V) : (∑ z, ψ ((2:K) * B u z)) =
      if u ∈ B.ker then (Fintype.card V : ℂ) else 0 := by
    by_cases hu : u ∈ B.ker
    · have hz : B u = 0 := LinearMap.mem_ker.mp hu
      simp [hu, hz]
    · rw [if_neg hu]
      exact linear_character_sum_zero ψ hψ ((2:K) • B u) (by
        intro heq
        apply hu
        apply LinearMap.mem_ker.mpr
        exact (smul_eq_zero.mp heq).resolve_left hodd)
  simp only [← Finset.mul_sum, hi]
  calc
    ‖∑ u, ψ (B u u) * ψ (l u) *
        (if u ∈ B.ker then (Fintype.card V : ℂ) else 0)‖ ≤
        ∑ u, ‖ψ (B u u) * ψ (l u) *
        (if u ∈ B.ker then (Fintype.card V : ℂ) else 0)‖ := norm_sum_le _ _
    _ = (Fintype.card V : ℝ) * Nat.card B.ker := by
      simp only [norm_mul, AddChar.norm_apply, one_mul]
      simp only [apply_ite norm, Complex.norm_natCast, norm_zero]
      rw [Finset.sum_ite, Finset.sum_const_zero, add_zero,
        Finset.sum_const, nsmul_eq_mul]
      rw [mul_comm]
      congr 1
      rw [Nat.card_eq_fintype_card]
      simp [Fintype.card_subtype]

private instance certificate_instance_0865 : OAI.SidorenkoCounterexample.ProofCertificate_0865 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13
  exact @certificate_proof_0865 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13

theorem certificate_proof_0866 (ψ : AddChar K ℂ) (hψ : ψ ≠ 0)
    (hodd : (2 : K) ≠ 0) (B : LinearMap.BilinForm K V) (hB : B.IsSymm)
    (l : V →ₗ[K] K) (c : K) :
    ‖(Fintype.card V : ℂ)⁻¹ * ∑ x, ψ (B x x + l x + c)‖ ^ 2 ≤
      1 / (Fintype.card K : ℝ) ^ finrank K B.range := by
  classical
  have h := quadratic_gauss_bound ψ hψ hodd B hB l c
  have hv : (0 : ℝ) < Fintype.card V := by exact_mod_cast Fintype.card_pos
  have hk : (0 : ℝ) < Fintype.card K := by exact_mod_cast Fintype.card_pos
  have hc : (Fintype.card V : ℝ) =
      (Fintype.card K : ℝ) ^ finrank K B.range * Nat.card B.ker := by
    rw [Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := K) (V := V),
      Module.card_eq_pow_finrank (K := K) (V := B.ker)]
    push_cast
    rw [← pow_add, B.finrank_range_add_finrank_ker]
  simp only [norm_mul, norm_inv, Complex.norm_natCast, mul_pow]
  calc
    (Fintype.card V : ℝ)⁻¹ ^ 2 * ‖∑ x, ψ (B x x + l x + c)‖ ^ 2 ≤
      (Fintype.card V : ℝ)⁻¹ ^ 2 *
        ((Fintype.card V : ℝ) * Nat.card B.ker) :=
      mul_le_mul_of_nonneg_left h (sq_nonneg _)
    _ = 1 / (Fintype.card K : ℝ) ^ finrank K B.range := by
      have hp := pow_pos hk (finrank K B.range)
      field_simp
      nlinarith [hc]

private instance certificate_instance_0866 : OAI.SidorenkoCounterexample.ProofCertificate_0866 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13
  exact @certificate_proof_0866 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13

end Gauss
section Fourier
variable {K ι : Type} [Field K] [Fintype K] [Fintype ι] [DecidableEq ι] [DecidableEq K]
theorem certificate_proof_0867 (ψ : AddChar K ℂ) (hψ : ψ ≠ 0)
    (v : ι → K) :
    ∑ t : ι → K, ψ (t ⬝ᵥ v) = if v = 0 then (Fintype.card (ι → K) : ℂ) else 0 := by
  classical
  split_ifs with hv
  · simp [hv]
  · apply linear_character_sum_zero ψ hψ (coordinatePairing v)
    intro h
    apply hv
    apply dotProduct_eq_zero_iff.mp
    intro t
    simpa [coordinatePairing, dotProduct_comm] using
      congrArg (fun f : (ι → K) →ₗ[K] K => f t) h

private instance certificate_instance_0867 : OAI.SidorenkoCounterexample.ProofCertificate_0867 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9
  exact @certificate_proof_0867 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9

theorem certificate_proof_0868 (ψ : AddChar K ℂ) (hψ : ψ ≠ 0)
    (μ : (ι → K) → ℝ) :
    ∑ t, ‖finiteFourier ψ μ t‖ ^ 2 =
      (Fintype.card (ι → K) : ℝ) * ∑ x, (μ x)^2 := by
  classical
  apply Complex.ofReal_injective
  have hn (z : ℂ) : ((‖z‖^2 : ℝ) : ℂ) = z * star z := by
    rw [← Complex.normSq_eq_norm_sq, ← Complex.mul_conj]; rfl
  have hs (x : ℝ) : star (x : ℂ) = x := by simp
  simp only [Complex.ofReal_sum, Complex.ofReal_mul, hn, finiteFourier,
    star_sum, star_mul, hs,
    char_conj, Finset.sum_mul, Finset.mul_sum]
  have he (x y : ι → K) :
      (∑ t, (μ x : ℂ) * ψ (t ⬝ᵥ x) * ((ψ (t ⬝ᵥ y))⁻¹ * μ y)) =
      (μ x : ℂ) * μ y * (if x = y then (Fintype.card (ι → K) : ℂ) else 0) := by
    calc
      _ = (μ x : ℂ) * μ y * ∑ t, ψ (t ⬝ᵥ (x-y)) := by
        simp only [dotProduct_sub, AddChar.map_sub_eq_div, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro t _
        ring
      _ = _ := by rw [coordinate_character_sum ψ hψ]; simp only [sub_eq_zero]
  rw [Finset.sum_comm]
  conv_lhs => enter [2, x]; rw [Finset.sum_comm]
  simp only [he]
  simp [Finset.sum_ite_eq', pow_two, mul_comm, mul_assoc]

private instance certificate_instance_0868 : OAI.SidorenkoCounterexample.ProofCertificate_0868 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9
  exact @certificate_proof_0868 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9

theorem certificate_proof_0869 (ψ : AddChar K ℂ) (hψ : ψ ≠ 0)
    (μ : (ι → K) → ℝ) (hμ : ∑ x, μ x = 1) (t : ι → K) :
    finiteFourier ψ (fun x => μ x - (Fintype.card (ι → K) : ℝ)⁻¹) t =
      if t = 0 then 0 else finiteFourier ψ μ t := by
  classical
  have hc : (Fintype.card (ι → K) : ℂ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  simp only [finiteFourier, Complex.ofReal_sub, sub_mul, Finset.sum_sub_distrib,
    ← Finset.mul_sum, Complex.ofReal_inv, Complex.ofReal_natCast]
  have hs : ∑ x : ι → K, ψ (t ⬝ᵥ x) =
      if t = 0 then (Fintype.card (ι → K) : ℂ) else 0 := by
    simpa only [dotProduct_comm] using coordinate_character_sum ψ hψ t
  rw [hs]
  split_ifs with ht
  · simp [ht, ← Complex.ofReal_sum, hμ]
  · simp

private instance certificate_instance_0869 : OAI.SidorenkoCounterexample.ProofCertificate_0869 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11
  exact @certificate_proof_0869 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11

theorem certificate_proof_0870 (ψ : AddChar K ℂ) (hψ : ψ ≠ 0)
    (μ : (ι → K) → ℝ) (hμ : ∑ x, μ x = 1) :
    (∑ x, |μ x - (Fintype.card (ι → K) : ℝ)⁻¹|)^2 ≤
      ∑ t, if t = 0 then 0 else ‖finiteFourier ψ μ t‖^2 := by
  classical
  have hp := finite_parseval ψ hψ (fun x => μ x - (Fintype.card (ι → K) : ℝ)⁻¹)
  simp only [finiteFourier_sub_uniform ψ hψ μ hμ] at hp
  have hs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun _ : ι → K => (1:ℝ))
    (fun x => |μ x - (Fintype.card (ι → K) : ℝ)⁻¹|)
  simp only [one_mul, one_pow, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, mul_one, sq_abs] at hs
  rw [← hp] at hs
  simpa only [apply_ite norm, norm_zero, ite_pow, zero_pow (by decide : 2 ≠ 0)] using hs

private instance certificate_instance_0870 : OAI.SidorenkoCounterexample.ProofCertificate_0870 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10
  exact @certificate_proof_0870 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10

theorem certificate_proof_0871 (ψ : AddChar K ℂ) (hψ : ψ ≠ 0)
    (μ : (ι → K) → ℝ) (hμ : ∑ x, μ x = 1) (ε : ℝ) (hε : 0 ≤ ε)
    (hf : ∀ t ≠ 0, ‖finiteFourier ψ μ t‖ ^ 2 ≤ ε) :
    (∑ x, |μ x - (Fintype.card (ι → K) : ℝ)⁻¹|)^2 ≤
      (Fintype.card (ι → K) : ℝ) * ε := by
  classical
  refine (finite_fourier_l1_bound ψ hψ μ hμ).trans ?_
  calc
    _ ≤ ∑ _t : ι → K, ε := by
      apply Finset.sum_le_sum
      intro t _
      split_ifs with ht
      · exact hε
      · exact hf t ht
    _ = _ := by simp

private instance certificate_instance_0871 : OAI.SidorenkoCounterexample.ProofCertificate_0871 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13
  exact @certificate_proof_0871 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13

variable {Ω : Type} [Fintype Ω] [Nonempty Ω]
omit [Field K] in
theorem certificate_proof_0872 (f : Ω → ι → K) : ∑ x, uniformLaw f x = 1 := by
  classical
  simp only [uniformLaw, ← Finset.mul_sum]
  rw [Finset.sum_comm]
  simp

private instance certificate_instance_0872 : OAI.SidorenkoCounterexample.ProofCertificate_0872 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9
  exact @certificate_proof_0872 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9

omit [Field K] [Nonempty Ω] in
theorem certificate_proof_0873 (f : Ω → ι → K) (g : (ι → K) → ℝ) :
    ∑ x, uniformLaw f x * g x = (Fintype.card Ω : ℝ)⁻¹ * ∑ v, g (f v) := by
  classical
  simp only [uniformLaw, mul_assoc, ← Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro x _
  simp

private instance certificate_instance_0873 : OAI.SidorenkoCounterexample.ProofCertificate_0873 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9
  exact @certificate_proof_0873 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9

omit [Nonempty Ω] in
theorem certificate_proof_0874 (ψ : AddChar K ℂ) (f : Ω → ι → K) (t : ι → K) :
    finiteFourier ψ (uniformLaw f) t =
      (Fintype.card Ω : ℂ)⁻¹ * ∑ v, ψ (t ⬝ᵥ f v) := by
  classical
  simp only [finiteFourier, uniformLaw, Complex.ofReal_mul, Complex.ofReal_inv,
    Complex.ofReal_natCast, Complex.ofReal_sum, mul_assoc, ← Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro v _
  simp only [apply_ite, Complex.ofReal_one, Complex.ofReal_zero, ite_mul, one_mul, zero_mul]
  simp

private instance certificate_instance_0874 : OAI.SidorenkoCounterexample.ProofCertificate_0874 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11
  exact @certificate_proof_0874 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11

variable {V : Type} [AddCommGroup V] [Module K V] [Fintype V]
omit [Fintype K] [DecidableEq ι] [DecidableEq K] [Fintype V] in
theorem certificate_proof_0875 (B : ι → LinearMap.BilinForm K V)
    (l : ι → V →ₗ[K] K) (c t : ι → K) (v : V) :
    t ⬝ᵥ quadraticMap B l c v =
      (∑ i, t i • B i) v v + (∑ i, t i • l i) v + ∑ i, t i * c i := by
  simp [dotProduct, quadraticMap, Finset.sum_add_distrib, mul_add]

private instance certificate_instance_0875 : OAI.SidorenkoCounterexample.ProofCertificate_0875 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11
  exact @certificate_proof_0875 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11

theorem certificate_proof_0876 (ψ : AddChar K ℂ) (hψ : ψ ≠ 0)
    (hodd : (2:K) ≠ 0) (B : ι → LinearMap.BilinForm K V)
    (hB : ∀ i, (B i).IsSymm) (l : ι → V →ₗ[K] K) (c t : ι → K) :
    ‖finiteFourier ψ (uniformLaw (quadraticMap B l c)) t‖^2 ≤
      1 / (Fintype.card K : ℝ) ^ finrank K (∑ i, t i • B i).range := by
  rw [finiteFourier_uniformLaw]
  simp only [quadraticMap_frequency]
  apply normalized_quadratic_gauss_bound ψ hψ hodd
  constructor
  intro x y
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [(hB i).eq]

private instance certificate_instance_0876 : OAI.SidorenkoCounterexample.ProofCertificate_0876 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18
  exact @certificate_proof_0876 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18

theorem certificate_proof_0877 (ψ : AddChar K ℂ) (hψ : ψ ≠ 0)
    (hodd : (2:K) ≠ 0) (B : ι → LinearMap.BilinForm K V)
    (hB : ∀ i, (B i).IsSymm) (l : ι → V →ₗ[K] K) (c : ι → K)
    (hrank : ∀ t : ι → K, t ≠ 0 →
      Fintype.card ι + 1 ≤ finrank K (∑ i, t i • B i).range) :
    (∑ x, |uniformLaw (quadraticMap B l c) x -
      (Fintype.card (ι → K) : ℝ)⁻¹|)^2 ≤ 1 / (Fintype.card K : ℝ) := by
  have hq : (1:ℝ) ≤ Fintype.card K := by exact_mod_cast Fintype.card_pos (α := K)
  have hf (t : ι → K) (ht : t ≠ 0) :
      ‖finiteFourier ψ (uniformLaw (quadraticMap B l c)) t‖^2 ≤
        1 / (Fintype.card K : ℝ)^(Fintype.card ι+1) := by
    refine (quadraticMap_fourier_bound ψ hψ hodd B hB l c t).trans ?_
    exact one_div_le_one_div_of_le (pow_pos (by linarith) _)
      (pow_le_pow_right₀ hq (hrank t ht))
  have hh := finite_fourier_l1_of_uniform_bound ψ hψ _
    (uniformLaw_sum (quadraticMap B l c)) _ (by positivity) hf
  convert hh using 1
  rw [Fintype.card_fun, Nat.cast_pow, pow_succ]
  have hq0 : (Fintype.card K : ℝ) ≠ 0 := by linarith
  field_simp

private instance certificate_instance_0877 : OAI.SidorenkoCounterexample.ProofCertificate_0877 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18
  exact @certificate_proof_0877 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18

end Fourier
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open scoped BigOperators
open Module
section SignMoments
variable {K ι : Type} [Field K] [Fintype K] [DecidableEq K]
  [Fintype ι] [DecidableEq ι]
variable {V : Type} [AddCommGroup V] [Module K V] [Fintype V]
end SignMoments
end SidorenkoCounterexample
end
section
namespace SidorenkoCounterexample
open Module LinearMap
open scoped Matrix BigOperators
section Mom
variable {K ι : Type} [Field K] [Fintype K] [DecidableEq K]
  [Fintype ι] [DecidableEq ι] [Nonempty ι] {N : ℕ}
end Mom
end SidorenkoCounterexample
end
section
namespace SidorenkoCounterexample
open Module Classical
open scoped Matrix BigOperators
section Span
variable {K I : Type} [Field K] [Fintype K] [DecidableEq K]
  [Fintype I] [DecidableEq I] {N : ℕ}
end Span
end SidorenkoCounterexample
end
section
namespace SidorenkoCounterexample
open Module Classical
open scoped BigOperators
section Star
variable {K I J W : Type} [Field K] [AddCommGroup W] [Module K W]
variable [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] [Fintype W]
end Star
section Border
variable {K I : Type} [Field K] [Fintype K] [DecidableEq K] [Fintype I] [DecidableEq I]
end Border
end SidorenkoCounterexample
end
end OAI

theorem solution : OAI.SidorenkoCounterexample.ProofCertificate_0844 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0845 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0846 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0847 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0848 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0849 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0850 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0851 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0852 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0853 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0854 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0855 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0856 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0857 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0858 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0859 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0860 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0861 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0862 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0863 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0864 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0865 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0866 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0867 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0868 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0869 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0870 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0871 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0872 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0873 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0874 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0875 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0876 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0877 := by
  exact ⟨inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance⟩
end

