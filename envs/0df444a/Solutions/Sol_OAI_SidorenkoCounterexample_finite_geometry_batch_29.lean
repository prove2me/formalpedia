-- Prove2me | solution 1 for OAI.SidorenkoCounterexample.finite_geometry_batch_29
-- status  : ACCEPTED   (prove)
-- author  : @abcdefg
-- created : 2026-10-09T06:31:03.005892+00:00
-- url     : https://prove2.me/submissions/06750fe9-7cd2-4606-8d07-d1fb979648ff

import Definitions.Def_SidorenkoCertificateBundleB
set_option linter.unusedVariables false
section
variable [p0 : OAI.SidorenkoCounterexample.ProofCertificate_0051]
  [p1 : OAI.SidorenkoCounterexample.ProofCertificate_0373]
  [p2 : OAI.SidorenkoCounterexample.ProofCertificate_0510]
  [p3 : OAI.SidorenkoCounterexample.ProofCertificate_0633]
  [p4 : OAI.SidorenkoCounterexample.ProofCertificate_0635]
  [p5 : OAI.SidorenkoCounterexample.ProofCertificate_0636]
  [p6 : OAI.SidorenkoCounterexample.ProofCertificate_0652]
  [p7 : OAI.SidorenkoCounterexample.ProofCertificate_0653]
  [p8 : OAI.SidorenkoCounterexample.ProofCertificate_0654]
  [p9 : OAI.SidorenkoCounterexample.ProofCertificate_0655]
  [p10 : OAI.SidorenkoCounterexample.ProofCertificate_0656]
  [p11 : OAI.SidorenkoCounterexample.ProofCertificate_0657]
  [p12 : OAI.SidorenkoCounterexample.ProofCertificate_0659]
  [p13 : OAI.SidorenkoCounterexample.ProofCertificate_0660]
  [p14 : OAI.SidorenkoCounterexample.ProofCertificate_0662]
  [p15 : OAI.SidorenkoCounterexample.ProofCertificate_0663]
  [p16 : OAI.SidorenkoCounterexample.ProofCertificate_0664]
  [p17 : OAI.SidorenkoCounterexample.ProofCertificate_0678]
  [p18 : OAI.SidorenkoCounterexample.ProofCertificate_0715]
  [p19 : OAI.SidorenkoCounterexample.ProofCertificate_0754]
  [p20 : OAI.SidorenkoCounterexample.ProofCertificate_0787]
  [p21 : OAI.SidorenkoCounterexample.ProofCertificate_0824]
  [p22 : OAI.SidorenkoCounterexample.ProofCertificate_0825]
  [p23 : OAI.SidorenkoCounterexample.ProofCertificate_0826]
  [p24 : OAI.SidorenkoCounterexample.ProofCertificate_0829]
  [p25 : OAI.SidorenkoCounterexample.ProofCertificate_0873]
  [p26 : OAI.SidorenkoCounterexample.ProofCertificate_0877]
include p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26

namespace OAI
section
namespace SidorenkoCounterexample
open scoped BigOperators
open Module
section Gauss
variable {K V : Type} [Field K] [Fintype K]
  [AddCommGroup V] [Module K V] [Fintype V]
end Gauss
section Fourier
variable {K ι : Type} [Field K] [Fintype K] [Fintype ι] [DecidableEq ι] [DecidableEq K]
variable {Ω : Type} [Fintype Ω] [Nonempty Ω]
variable {V : Type} [AddCommGroup V] [Module K V] [Fintype V]
end Fourier
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open scoped BigOperators
open Module
section SignMoments
variable {K ι : Type} [Field K] [Fintype K] [DecidableEq K]
  [Fintype ι] [DecidableEq ι]
omit [DecidableEq ι] in
theorem certificate_proof_0878 (x : ι → K) : |characterProduct x| ≤ 1 := by
  rw [characterProduct, Finset.abs_prod]
  exact Finset.prod_le_one (fun _ _ => abs_nonneg _) (fun i _ => by
    have h := quadraticChar_dichotomy (F := K) (a := x i)
    by_cases hx : x i = 0
    · simp [hx]
    · rcases h hx with h | h <;> simp [h])

private instance certificate_instance_0878 : OAI.SidorenkoCounterexample.ProofCertificate_0878 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6
  exact @certificate_proof_0878 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 q0 q1 q2 q3 q4 q5 q6

theorem certificate_proof_0879 [Nonempty ι] (hodd : ringChar K ≠ 2) :
    ∑ x : ι → K, characterProduct x = 0 := by
  rw [show (∑ x : ι → K, characterProduct x) =
    ∏ _i : ι, ∑ a : K, (quadraticChar K a : ℝ) from (Fintype.prod_sum (fun (_i : ι) (a : K) => (quadraticChar K a : ℝ))).symm]
  have hz : ∑ a : K, (quadraticChar K a : ℝ) = 0 := by
    exact_mod_cast quadraticChar_sum_zero hodd
  rw [hz]
  simp

private instance certificate_instance_0879 : OAI.SidorenkoCounterexample.ProofCertificate_0879 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8
  exact @certificate_proof_0879 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 q0 q1 q2 q3 q4 q5 q6 q7 q8

omit [Field K] [DecidableEq K] in
theorem certificate_proof_0880 (μ ν : (ι → K) → ℝ) (g : (ι → K) → ℝ)
    (hg : ∀ x, |g x| ≤ 1) :
    |(∑ x, μ x * g x) - ∑ x, ν x * g x| ≤ ∑ x, |μ x-ν x| := by
  rw [← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  apply Finset.sum_le_sum
  intro x _
  rw [← sub_mul, abs_mul]
  exact mul_le_of_le_one_right (abs_nonneg _) (hg x)

private instance certificate_instance_0880 : OAI.SidorenkoCounterexample.ProofCertificate_0880 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8
  exact @certificate_proof_0880 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 q0 q1 q2 q3 q4 q5 q6 q7 q8

variable {V : Type} [AddCommGroup V] [Module K V] [Fintype V]
theorem certificate_proof_0881 [Nonempty ι]
    (ψ : AddChar K ℂ) (hψ : ψ ≠ 0) (hodd : (2:K) ≠ 0)
    (B : ι → LinearMap.BilinForm K V) (hB : ∀ i, (B i).IsSymm)
    (l : ι → V →ₗ[K] K) (c : ι → K)
    (hrank : ∀ t : ι → K, t ≠ 0 →
      Fintype.card ι + 1 ≤ finrank K (∑ i, t i • B i).range) :
    ((Fintype.card V : ℝ)⁻¹ * ∑ v, characterProduct (quadraticMap B l c v))^2 ≤
      1 / (Fintype.card K : ℝ) := by
  have hc : ringChar K ≠ 2 := by
    intro h
    apply hodd
    simpa using (ringChar.spec K 2).mpr (by rw [h])
  have hz : ∑ x : ι → K, (Fintype.card (ι → K) : ℝ)⁻¹ * characterProduct x = 0 := by
    rw [← Finset.mul_sum, characterProduct_sum hc, mul_zero]
  have hb := bounded_test_l1 (uniformLaw (quadraticMap B l c))
    (fun _ => (Fintype.card (ι → K) : ℝ)⁻¹) characterProduct characterProduct_abs_le
  rw [uniformLaw_average, hz, sub_zero] at hb
  have hf := quadraticMap_joint_l1_bound ψ hψ hodd B hB l c hrank
  have hh := ((sq_le_sq₀ (abs_nonneg _) (Finset.sum_nonneg (fun _ _ => abs_nonneg _))).mpr hb).trans hf
  simpa only [sq_abs] using hh

private instance certificate_instance_0881 : OAI.SidorenkoCounterexample.ProofCertificate_0881 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19
  exact @certificate_proof_0881 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19

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
omit [Fintype K] [DecidableEq K] in
theorem certificate_proof_0882 (M : Matrix (Fin N) (Fin N) K) :
    finrank K M.toBilin'.range=M.rank := by
  rw [←matrix_radical_quotient_rank]
  exact M.toBilin'.quotKerEquivRange.finrank_eq.symm

private instance certificate_instance_0882 : OAI.SidorenkoCounterexample.ProofCertificate_0882 := by
  constructor
  intro q0 q1 q2 q3
  exact @certificate_proof_0882 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 q0 q1 q2 q3

omit [Fintype K] [DecidableEq K] in
theorem certificate_proof_0883 (M : SymMatrix K N) (z w : Fin N → K) (a : K) :
    a-(z-w) ⬝ᵥ M.val⁻¹.mulVec (z-w) =
      (-M.val⁻¹.toBilin') z z + (2 • (M.val⁻¹.toBilin' w)) z +
        (a-M.val⁻¹.toBilin' w w) := by
  have hs := Matrix.isSymm_toBilin'_iff_isSymm.mpr M.property.inv
  have he : (z-w) ⬝ᵥ M.val⁻¹.mulVec (z-w) = M.val⁻¹.toBilin' (z-w) (z-w) := by
    rw [matrix_bilin_eval,M.property.inv,dotProduct_comm]
  rw [he]
  simp only [map_sub,LinearMap.sub_apply,LinearMap.neg_apply,LinearMap.smul_apply]
  rw [hs.eq z w]
  ring

private instance certificate_instance_0883 : OAI.SidorenkoCounterexample.ProofCertificate_0883 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6
  exact @certificate_proof_0883 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 q0 q1 q2 q3 q4 q5 q6

omit [Fintype K] [DecidableEq K] [DecidableEq ι] [Nonempty ι] in
theorem certificate_proof_0884 (M : ι → SymMatrix K N) (t : ι → K) :
    finrank K (∑ i, t i • (-((M i).val⁻¹.toBilin'))).range =
      (∑ i, t i • (M i).val⁻¹).rank := by
  have he : (∑ i, t i • (-((M i).val⁻¹.toBilin'))) =
      (-(∑ i, t i • (M i).val⁻¹)).toBilin' := by
    simp only [map_neg,map_sum,map_smul]
    apply LinearMap.ext
    intro x
    apply LinearMap.ext
    intro y
    simp
  rw [he,matrix_form_rank,matrix_rank_neg]

private instance certificate_instance_0884 : OAI.SidorenkoCounterexample.ProofCertificate_0884 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6
  exact @certificate_proof_0884 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 q0 q1 q2 q3 q4 q5 q6

theorem certificate_proof_0885 (hodd : ringChar K≠2)
    (M : ι → SymMatrix K N) (hM : ∀ i, (M i).val.det≠0)
    (w : ι → Fin N → K) (a : ι → K)
    (hrank : ∀ t : ι → K, t≠0 →
      Fintype.card ι+1≤(∑ i, t i • (M i).val⁻¹).rank) :
    (uniformMean (fun z : Fin N → K =>
      ∏ i, (quadraticChar K (symmetricBorder (M i) (z-w i) (a i)).val.det : ℝ)))^2 ≤
      1/(Fintype.card K : ℝ) := by
  obtain ⟨ψ,hψ⟩ := (AddChar.exists_apply_ne_zero (a := (1 : K))).mpr one_ne_zero
  have hp : ψ≠0 := by intro h; apply hψ; simp [h]
  have htwo : (2 : K)≠0 := by
    exact Ring.two_ne_zero hodd
  let B : ι → LinearMap.BilinForm K (Fin N → K) := fun i => -(M i).val⁻¹.toBilin'
  let l : ι → (Fin N → K) →ₗ[K] K := fun i => 2 • ((M i).val⁻¹.toBilin' (w i))
  let c : ι → K := fun i => a i-(M i).val⁻¹.toBilin' (w i) (w i)
  have hB : ∀ i, (B i).IsSymm := fun i =>
    (Matrix.isSymm_toBilin'_iff_isSymm.mpr (M i).property.inv).neg
  have hb := quadraticMap_character_moment ψ hp htwo B hB l c (fun t ht => by
    rw [inverse_form_span_rank M t]; exact hrank t ht)
  have hb' : (uniformMean (fun z => characterProduct (quadraticMap B l c z)))^2 ≤
      1/(Fintype.card K : ℝ) := by
    simpa only [uniformMean,div_eq_mul_inv,mul_comm] using hb
  have he (z : Fin N → K) : (∏ i, (quadraticChar K
      (symmetricBorder (M i) (z-w i) (a i)).val.det : ℝ)) =
      characterProduct (fun i => (M i).val.det) * characterProduct (quadraticMap B l c z) := by
    unfold characterProduct
    rw [←Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i _
    rw [symmetricBorder_det _ _ _ (hM i),map_mul,Int.cast_mul,schur_polynomial]
    rfl
  simp_rw [he]
  rw [uniformMean_mul,mul_pow]
  have hc := characterProduct_abs_le (fun i => (M i).val.det)
  have hc2 : characterProduct (fun i => (M i).val.det)^2≤1 := by
    simpa only [sq_abs,one_pow] using (sq_le_sq₀ (abs_nonneg _) zero_le_one).mpr hc
  exact (mul_le_of_le_one_left (sq_nonneg _) hc2).trans hb'

private instance certificate_instance_0885 : OAI.SidorenkoCounterexample.ProofCertificate_0885 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14
  exact @certificate_proof_0885 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14

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
omit [Fintype K] [DecidableEq K] [DecidableEq I] in
theorem certificate_proof_0886 (t : I → K) (Q : I → SymMatrix K N) :
    finrank K (weightedCombination t (fun i => matrixFormEquiv N (Q i))).val.range =
      (∑ i, t i • (Q i).val).rank := by
  have he : (weightedCombination t (fun i => matrixFormEquiv N (Q i))).val =
      (∑ i, t i • (Q i).val).toBilin' := by
    simp only [weightedCombination, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.proj_apply]
    change (symmetricFormSubmodule (K := K) (V := Fin N → K)).subtype
      (∑ i, t i • matrixFormEquiv N (Q i)) = _
    calc
      _ = ∑ i, (symmetricFormSubmodule (K := K) (V := Fin N → K)).subtype
          (t i • matrixFormEquiv N (Q i)) := map_sum _ _ _
      _ = _ := by
        simp only [map_sum,map_smul]
        apply Finset.sum_congr rfl
        intro i _
        exact map_smul (symmetricFormSubmodule (K := K) (V := Fin N → K)).subtype (t i) (matrixFormEquiv N (Q i))
  rw [he,matrix_form_rank]

private instance certificate_instance_0886 : OAI.SidorenkoCounterexample.ProofCertificate_0886 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6
  exact @certificate_proof_0886 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 q0 q1 q2 q3 q4 q5 q6

theorem certificate_proof_0887 (s : ℕ) (hs : s ≤ N) :
    uniformMean (fun Q : I → SymMatrix K N => if ∃ t : I → K, t≠0 ∧
      (∑ i, t i • (Q i).val).rank ≤ s then 1 else 0)  ≤
      (Fintype.card K : ℝ)^(Fintype.card I) *
        (2^(N-s)/(Fintype.card K : ℝ)^((N-s+1).choose 2)) := by
  classical
  let e : (I → SymMatrix K N) ≃ (I → SymForm K (Fin N → K)) :=
    Equiv.piCongrRight (fun _ => matrixFormEquiv N)
  have hp (Q : I → SymMatrix K N) : (∃ t : I → K, t≠0 ∧
      (∑ i, t i • (Q i).val).rank ≤ s) ↔
      ∃ t : I → K, t≠0 ∧ finrank K (weightedCombination t (e Q)).val.range ≤ s := by
    apply exists_congr
    intro t
    rw [show finrank K (weightedCombination t (e Q)).val.range =
      (∑ i, t i • (Q i).val).rank from matrix_combination_form_rank t Q]
  simp_rw [hp]
  rw [←Function.comp_def (fun Q : I → SymForm K (Fin N → K) => if ∃ t : I → K, t≠0 ∧
    finrank K (weightedCombination t Q).val.range ≤ s then (1 : ℝ) else 0) e,
    uniformMean_equiv e,uniformMean_indicator]
  simpa only [Nat.card_eq_fintype_card,Module.finrank_fin_fun] using
    (symmetric_low_rank_span_bound (K := K) (V := Fin N → K) (ι := I) s (by simpa using hs))

private instance certificate_instance_0887 : OAI.SidorenkoCounterexample.ProofCertificate_0887 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9
  exact @certificate_proof_0887 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9

theorem certificate_proof_0888 (hN : Fintype.card I ≤ N) :
    uniformMean (fun M : I → SymMatrix K N => if goodMinors M then 0 else 1)  ≤
      minorBadBound N (Fintype.card I) (Fintype.card K) := by
  classical
  let P (Q : I → SymMatrix K N) : Prop := ∃ t : I → K, t≠0 ∧
    (∑ i, t i • (Q i).val).rank ≤ Fintype.card I
  let e : (I → SymMatrix K N) ≃ (I → SymMatrix K N) :=
    Equiv.piCongrRight (fun _ => symmetricInverseEquiv N)
  have he (M : I → SymMatrix K N) (hM : ∀ i, (M i).val.det≠0) (i : I) :
      (e M i).val=(M i).val⁻¹ := by simp [e,symmetricInverseEquiv,symmetricInverse,hM i]
  have hp (M : I → SymMatrix K N) :
      (if goodMinors M then (0 : ℝ) else 1)  ≤
        (∑ i, if (M i).val.det=0 then 1 else 0)+(if P (e M) then 1 else 0) := by
    by_cases hg : goodMinors M
    · simp only [if_pos hg]; positivity
    · simp only [if_neg hg]
      by_cases hM : ∀ i, (M i).val.det≠0
      · have hr : P (e M) := by
          simp only [goodMinors,not_and,not_forall] at hg
          obtain ⟨t,ht⟩ := hg hM
          obtain ⟨htt1,htt2⟩ := ht
          refine ⟨t,htt1,?_⟩
          simp only [he M hM]
          omega
        simp only [if_pos hr]
        have : (0 : ℝ) ≤ ∑ i, if (M i).val.det=0 then (1 : ℝ) else 0 := by positivity
        linarith
      · push Not at hM
        obtain ⟨i,hi⟩ := hM
        have hb : (1 : ℝ) ≤ ∑ j, if (M j).val.det=0 then (1 : ℝ) else 0 := by
          simpa only [hi,ite_true] using Finset.single_le_sum
            (fun j (_ : j ∈ Finset.univ) => by positivity : ∀ j ∈ Finset.univ, 0 ≤ (if (M j).val.det=0 then (1 : ℝ) else 0))
            (Finset.mem_univ i)
        exact hb.trans (le_add_of_nonneg_right (by positivity))
  apply (uniformMean_mono hp).trans
  rw [uniformMean_add,uniformMean_sum]
  have hs (i : I) : uniformMean (fun M : I → SymMatrix K N => if (M i).val.det=0 then (1 : ℝ) else 0)  ≤
      (N : ℝ)/(Fintype.card K : ℝ) := by
    rw [uniformMean_coordinate i (fun A : SymMatrix K N => if A.val.det = 0 then (1 : ℝ) else 0)]
    exact symmetricSingularProb_bound (K := K) N
  have hb : uniformMean (fun M => if P (e M) then (1 : ℝ) else 0)  ≤
      (Fintype.card K : ℝ)^(Fintype.card I) *
        (2^(N-Fintype.card I)/(Fintype.card K : ℝ)^((N-Fintype.card I+1).choose 2)) := by
    rw [←Function.comp_def (fun M => if P M then (1 : ℝ) else 0) e,uniformMean_equiv]
    exact matrix_low_rank_span_bound (Fintype.card I) hN
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hs i)
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul] at hsum
  unfold minorBadBound
  rw [←mul_div_assoc] at hsum
  exact add_le_add hsum hb

private instance certificate_instance_0888 : OAI.SidorenkoCounterexample.ProofCertificate_0888 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8
  exact @certificate_proof_0888 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 q0 q1 q2 q3 q4 q5 q6 q7 q8

end Span
end SidorenkoCounterexample
end
section
namespace SidorenkoCounterexample
open Module Classical
open scoped BigOperators
section Star
variable {K I J W : Type} [Field K] [AddCommGroup W] [Module K W]
theorem certificate_proof_0889 (v : I) (k : J → I) (hk : Function.Injective k)
    (hv : ∀ j, k j≠v) : Function.Surjective (starDifference (K := K) (W := W) v k) := by
  intro M
  refine ⟨Function.extend k (fun j => -M j) (fun _ => 0),?_⟩
  ext j
  change Function.extend k (fun j => -M j) (fun _ => (0 : W)) v-
    Function.extend k (fun j => -M j) (fun _ => (0 : W)) (k j)=M j
  rw [hk.extend_apply,Function.extend_apply' _ _ v (by simpa using hv)]
  simp

private instance certificate_instance_0889 : OAI.SidorenkoCounterexample.ProofCertificate_0889 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10
  exact @certificate_proof_0889 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10

variable [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] [Fintype W]
include K in
theorem certificate_proof_0890 (v : I) (k : J → I) (hk : Function.Injective k)
    (hv : ∀ j, k j≠v) (f : (J → W) → ℝ) :
    uniformMean (fun X : I → W => f (fun j => X v-X (k j)))=uniformMean f :=
  uniformMean_surjective_linear (starDifference (K := K) v k)
    (starDifference_surjective v k hk hv) f

private instance certificate_instance_0890 : OAI.SidorenkoCounterexample.ProofCertificate_0890 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16
  exact @certificate_proof_0890 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16

end Star
section Border
variable {K I : Type} [Field K] [Fintype K] [DecidableEq K] [Fintype I] [DecidableEq I]
omit [Fintype K] [DecidableEq K] in
theorem certificate_proof_0891 {N : ℕ} (W V : SymMatrix K N) (z w : Fin N → K) (a b : K) :
    symmetricBorder W z a-symmetricBorder V w b=symmetricBorder (W-V) (z-w) (a-b) := by
  apply Subtype.ext
  ext i j
  change borderRaw W.val z a (borderIndex N i) (borderIndex N j)-
    borderRaw V.val w b (borderIndex N i) (borderIndex N j)=
      borderRaw (W-V).val (z-w) (a-b) (borderIndex N i) (borderIndex N j)
  cases borderIndex N i <;> cases borderIndex N j <;> rfl

private instance certificate_instance_0891 : OAI.SidorenkoCounterexample.ProofCertificate_0891 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8
  exact @certificate_proof_0891 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 q0 q1 q2 q3 q4 q5 q6 q7 q8

theorem certificate_proof_0892 {A B : Type} [Fintype A] [Fintype B]
    (f : (I → A × B) → ℝ) :
    uniformMean f=uniformMean fun a : I → A => uniformMean fun b : I → B => f (fun i => (a i,b i)) := by
  rw [←uniformMean_equiv (Equiv.arrowProdEquivProdArrow I (fun _ => A) (fun _ => B)).symm,
    uniformMean_prod]
  rfl

private instance certificate_instance_0892 : OAI.SidorenkoCounterexample.ProofCertificate_0892 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7
  exact @certificate_proof_0892 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 q0 q1 q2 q3 q4 q5 q6 q7

omit [DecidableEq K] in
theorem certificate_proof_0893 (N : ℕ) (f : (I → SymMatrix K (N+1)) → ℝ) :
    uniformMean f=uniformMean (fun W : I → SymMatrix K N =>
      uniformMean (fun z : I → (Fin N → K) => uniformMean (fun a : I → K =>
        f (fun i => symmetricBorder (W i) (z i) (a i))))) := by
  rw [←uniformMean_equiv (Equiv.piCongrRight (fun _ : I => (symmetricBorderEquiv (K := K) N).symm))]
  rw [uniformMean_pi_prod]
  apply uniformMean_congr
  intro W
  rw [uniformMean_pi_prod]
  rfl

private instance certificate_instance_0893 : OAI.SidorenkoCounterexample.ProofCertificate_0893 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7
  exact @certificate_proof_0893 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 q0 q1 q2 q3 q4 q5 q6 q7

end Border
end SidorenkoCounterexample
end
end OAI
namespace OAI
section
namespace SidorenkoCounterexample
open Module Classical
open scoped BigOperators
section StarMoment
variable {K I J : Type} [Field K] [Fintype K] [DecidableEq K]
  [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] [Nonempty J] {N : ℕ}
omit [Fintype I] [DecidableEq I] [DecidableEq J] [Nonempty J] in
theorem certificate_proof_0894 (v : I) (k : J → I) (W : I → SymMatrix K N)
    (z : I → (Fin N → K)) (a : I → K) : |starSign v k W z a| ≤ 1 :=
  characterProduct_abs_le _

private instance certificate_instance_0894 : OAI.SidorenkoCounterexample.ProofCertificate_0894 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12
  exact @certificate_proof_0894 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12

omit [Fintype I] in
theorem certificate_proof_0895 (hK : ringChar K≠2) (v : I) (k : J → I)
    (hv : ∀ j, k j≠v) (W : I → SymMatrix K N) (z : I → (Fin N → K)) (a : I → K)
    (hW : goodMinors (fun j => W v-W (k j))) :
    |uniformMean (fun z' => starSign v k W (Function.update z v z') a)| ≤
      Real.sqrt (1/(Fintype.card K : ℝ)) := by
  have he (z' : Fin N → K) : starSign v k W (Function.update z v z') a =
      ∏ j, (quadraticChar K (symmetricBorder (W v-W (k j)) (z'-z (k j)) (a v-a (k j))).val.det : ℝ) := by
    simp only [starSign,Function.update_self,Function.update_of_ne (hv _)]
  simp_rw [he]
  apply (Real.le_sqrt (abs_nonneg _) (by positivity)).mpr
  rw [sq_abs]
  exact schur_sign_moment hK (fun j => W v-W (k j)) hW.1 (fun j => z (k j))
    (fun j => a v-a (k j)) hW.2

private instance certificate_instance_0895 : OAI.SidorenkoCounterexample.ProofCertificate_0895 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18
  exact @certificate_proof_0895 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18

omit [Fintype I] in
theorem certificate_proof_0896 (hK : ringChar K≠2) (v : I) (k : J → I)
    (hv : ∀ j, k j≠v) (W : I → SymMatrix K N) (z : I → (Fin N → K)) (a : I → K)
    (R : (I → (Fin N → K)) → ℝ) (hR : ∀ z, |R z| ≤ 1)
    (hRi : ∀ z', R (Function.update z v z')=R z) :
    |uniformMean (fun z' => R (Function.update z v z') * starSign v k W (Function.update z v z') a)| ≤
      Real.sqrt (1/(Fintype.card K : ℝ)) +
        (if goodMinors (fun j => W v-W (k j)) then 0 else 1) := by
  simp_rw [hRi]
  rw [uniformMean_mul,abs_mul]
  by_cases hW : goodMinors (fun j => W v-W (k j))
  · rw [if_pos hW,add_zero]
    exact (mul_le_of_le_one_left (abs_nonneg _) (hR z)).trans (starSign_update_bound hK v k hv W z a hW)
  · rw [if_neg hW]
    apply le_trans _ (le_add_of_nonneg_left (Real.sqrt_nonneg _))
    apply (mul_le_of_le_one_left (abs_nonneg _) (hR z)).trans
    exact (abs_uniformMean_le _).trans (uniformMean_bound fun z' => starSign_abs_le v k W _ a)

private instance certificate_instance_0896 : OAI.SidorenkoCounterexample.ProofCertificate_0896 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19 q20
  exact @certificate_proof_0896 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19 q20

theorem certificate_proof_0897 (hK : ringChar K≠2) (v : I) (k : J → I)
    (hk : Function.Injective k) (hv : ∀ j, k j≠v) (hN : Fintype.card J ≤ N)
    (R : (I → SymMatrix K N) → (I → (Fin N → K)) → (I → K) → ℝ)
    (hR : ∀ W z a, |R W z a| ≤ 1)
    (hRi : ∀ W z a z', R W (Function.update z v z') a=R W z a) :
    |uniformMean (fun W => uniformMean fun a => uniformMean fun z => R W z a * starSign v k W z a)| ≤
       Real.sqrt (1/(Fintype.card K : ℝ)) + minorBadBound N (Fintype.card J) (Fintype.card K) := by
  have hpoint (W : I → SymMatrix K N) (a : I → K) :
      |uniformMean (fun z => R W z a * starSign v k W z a)| ≤
        Real.sqrt (1/(Fintype.card K : ℝ)) +
          (if goodMinors (fun j => W v-W (k j)) then 0 else 1) := by
    rw [uniformMean_update v]
    apply (abs_uniformMean_le _).trans
    exact uniformMean_bound (fun z => testedStar_update_bound hK v k hv W z a (fun z => R W z a)
      (fun z => hR W z a) (hRi W z a))
  apply (abs_uniformMean_le _).trans
  calc
    _ ≤ uniformMean (fun W : I → SymMatrix K N => Real.sqrt (1/(Fintype.card K : ℝ)) +
        (if goodMinors (fun j => W v-W (k j)) then 0 else 1)) := by
      apply uniformMean_mono
      intro W
      exact (abs_uniformMean_le _).trans (uniformMean_bound (hpoint W))
    _ = Real.sqrt (1/(Fintype.card K : ℝ)) +
        uniformMean (fun M : J → SymMatrix K N => if goodMinors M then 0 else 1) := by
      rw [uniformMean_add,uniformMean_const]
      congr 1
      exact uniformMean_starDifference (K := K) v k hk hv
        (fun M : J → SymMatrix K N => if goodMinors M then 0 else 1)
    _ ≤ _ := add_le_add le_rfl (badMinors_bound (K := K) hN)

private instance certificate_instance_0897 : OAI.SidorenkoCounterexample.ProofCertificate_0897 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19 q20
  exact @certificate_proof_0897 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19 q20

end StarMoment
end SidorenkoCounterexample
end
section
namespace SidorenkoCounterexample
open Module Classical
open scoped BigOperators
theorem certificate_proof_0898 : ∀ e, pairVertices e={pairLeft e,pairRight e} := by decide

private instance certificate_instance_0898 : OAI.SidorenkoCounterexample.ProofCertificate_0898 := by
  constructor
  intro q0
  exact @certificate_proof_0898 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 q0

theorem certificate_proof_0899 : ∀ e, pairLeft e≠pairRight e := by decide

private instance certificate_instance_0899 : OAI.SidorenkoCounterexample.ProofCertificate_0899 := by
  constructor
  intro q0
  exact @certificate_proof_0899 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 q0

theorem certificate_proof_0900 (v : Fin 13) (e : Fin 33) (_hv : v∈pairVertices e) : pairOther v e≠v := by
  unfold pairOther
  split_ifs with h
  · simpa only [h] using (pair_endpoints_ne e).symm
  · exact h

private instance certificate_instance_0900 : OAI.SidorenkoCounterexample.ProofCertificate_0900 := by
  constructor
  intro q0 q1 q2
  exact @certificate_proof_0900 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 q0 q1 q2

theorem certificate_proof_0901 (v : Fin 13) (e : Fin 33) (hv : v∈pairVertices e) :
    pairVertices e={v,pairOther v e} := by
  rw [pair_endpoints] at hv ⊢
  simp only [Finset.mem_insert,Finset.mem_singleton] at hv
  unfold pairOther
  split_ifs with h
  · rw [h]
  · rcases hv with h' | h'
    · exact (h h'.symm).elim
    · rw [h']; exact Finset.pair_comm _ _

private instance certificate_instance_0901 : OAI.SidorenkoCounterexample.ProofCertificate_0901 := by
  constructor
  intro q0 q1 q2
  exact @certificate_proof_0901 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 q0 q1 q2

theorem certificate_proof_0902 (F : Finset (Fin 33)) (v : Fin 13) : (selectedIncident F v).card ≤ 6 := by
  apply le_trans (Finset.card_le_card ?_) (incidentPairs_card_le v)
  intro e he
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp he).2⟩

private instance certificate_instance_0902 : OAI.SidorenkoCounterexample.ProofCertificate_0902 := by
  constructor
  intro q0 q1
  exact @certificate_proof_0902 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 q0 q1

theorem certificate_proof_0903 (F : Finset (Fin 33)) (v : Fin 13) :
    Function.Injective (fun e : selectedIncident F v => pairOther v e.val) := by
  intro e f h
  dsimp only at h
  apply Subtype.ext
  apply pairVertices_injective
  rw [pair_vertices_other v e.val (Finset.mem_filter.mp e.property).2,
    pair_vertices_other v f.val (Finset.mem_filter.mp f.property).2,h]

private instance certificate_instance_0903 : OAI.SidorenkoCounterexample.ProofCertificate_0903 := by
  constructor
  intro q0 q1
  exact @certificate_proof_0903 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 q0 q1

section Signs
variable {K : Type} [Field K] [Fintype K] [DecidableEq K] {D : ℕ}
theorem certificate_proof_0904 (X : Fin 13 → SymMatrix K D) (e : Fin 33) : |pairSign X e| ≤ 1 := by
  unfold pairSign
  by_cases h : (X (pairLeft e)-X (pairRight e)).val.det=0
  · rw [h]; norm_num
  · rcases quadraticChar_dichotomy (F := K) h with h | h <;> rw [h] <;> norm_num

private instance certificate_instance_0904 : OAI.SidorenkoCounterexample.ProofCertificate_0904 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6
  exact @certificate_proof_0904 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 q0 q1 q2 q3 q4 q5 q6

omit [Fintype K] [DecidableEq K] in
theorem certificate_proof_0905 (hD : Even D) (A B : SymMatrix K D) :
    (A-B).val.det=(B-A).val.det := by
  have he : A-B= -(B-A) := by abel
  rw [he,Submodule.coe_neg,Matrix.det_neg,Fintype.card_fin,hD.neg_pow,one_pow,one_mul]

private instance certificate_instance_0905 : OAI.SidorenkoCounterexample.ProofCertificate_0905 := by
  constructor
  intro q0 q1 q2 q3 q4 q5
  exact @certificate_proof_0905 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 q0 q1 q2 q3 q4 q5

theorem certificate_proof_0906 (hD : Even D) (X : Fin 13 → SymMatrix K D)
    (v : Fin 13) (e : Fin 33) (hv : v∈pairVertices e) :
    pairSign X e=quadraticChar K (X v-X (pairOther v e)).val.det := by
  rw [pair_endpoints] at hv
  simp only [Finset.mem_insert,Finset.mem_singleton] at hv
  unfold pairSign pairOther
  split_ifs with h
  · rw [h]
  · rcases hv with h' | h'
    · exact (h h'.symm).elim
    · rw [h',determinant_difference_even hD]

private instance certificate_instance_0906 : OAI.SidorenkoCounterexample.ProofCertificate_0906 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9
  exact @certificate_proof_0906 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9

theorem certificate_proof_0907 (F : Finset (Fin 33)) (X : Fin 13 → SymMatrix K D) :
    |∏ e∈F, pairSign X e| ≤ 1 := by
  rw [Finset.abs_prod]
  exact Finset.prod_le_one (fun e _ => abs_nonneg _) (fun e _ => pairSign_abs_le X e)

private instance certificate_instance_0907 : OAI.SidorenkoCounterexample.ProofCertificate_0907 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6
  exact @certificate_proof_0907 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 q0 q1 q2 q3 q4 q5 q6

end Signs
end SidorenkoCounterexample
end
section
namespace SidorenkoCounterexample
open Module Classical Filter
open scoped BigOperators
section Moment
variable {K : Type} [Field K] [Fintype K] [DecidableEq K] {N : ℕ}
theorem certificate_proof_0908 (F : Finset (Fin 33)) (v : Fin 13)
    (W : Fin 13 → SymMatrix K N) (z : Fin 13 → (Fin N → K)) (a : Fin 13 → K) :
    |nonincidentProduct F v W z a| ≤ 1 := pairSign_product_abs_le _ _

private instance certificate_instance_0908 : OAI.SidorenkoCounterexample.ProofCertificate_0908 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9
  exact @certificate_proof_0908 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9

theorem certificate_proof_0909 (F : Finset (Fin 33)) (v : Fin 13)
    (W : Fin 13 → SymMatrix K N) (z : Fin 13 → (Fin N → K)) (a : Fin 13 → K)
    (z' : Fin N → K) : nonincidentProduct F v W (Function.update z v z') a=
      nonincidentProduct F v W z a := by
  apply Finset.prod_congr rfl
  intro e he
  obtain ⟨heF,heN⟩ := Finset.mem_sdiff.mp he
  have hv : v∉pairVertices e := by
    intro h
    exact heN (Finset.mem_filter.mpr ⟨heF,h⟩)
  have hl : pairLeft e≠v := by
    intro h; apply hv; rw [pair_endpoints, h]; simp
  have hr : pairRight e≠v := by
    intro h; apply hv; rw [pair_endpoints, h]; simp
  simp only [pairSign,Function.update_of_ne hl,Function.update_of_ne hr]

private instance certificate_instance_0909 : OAI.SidorenkoCounterexample.ProofCertificate_0909 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10
  exact @certificate_proof_0909 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10

theorem certificate_proof_0910 (hN : Even (N+1)) (F : Finset (Fin 33)) (v : Fin 13)
    (W : Fin 13 → SymMatrix K N) (z : Fin 13 → (Fin N → K)) (a : Fin 13 → K) :
    (∏ e∈F, pairSign (fun i => symmetricBorder (W i) (z i) (a i)) e)=
      nonincidentProduct F v W z a * starSign v
        (fun e : selectedIncident F v => pairOther v e.val) W z a := by
  have he : starSign v (fun e : selectedIncident F v => pairOther v e.val) W z a=
      ∏ e∈selectedIncident F v, pairSign (fun i => symmetricBorder (W i) (z i) (a i)) e := by
    rw [←Finset.prod_coe_sort]
    apply Finset.prod_congr rfl
    intro e _
    rw [pairSign_other hN _ v e.val (Finset.mem_filter.mp e.property).2]
    rw [symmetricBorder_sub]
  rw [he]
  exact (Finset.prod_sdiff (Finset.filter_subset _ _)).symm

private instance certificate_instance_0910 : OAI.SidorenkoCounterexample.ProofCertificate_0910 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10
  exact @certificate_proof_0910 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10

theorem certificate_proof_0911 (hK : ringChar K≠2) (hN : Even (N+1))
    (F : Finset (Fin 33)) (v : Fin 13) (hne : (selectedIncident F v).Nonempty)
    (hc : (selectedIncident F v).card ≤ N) :
    |uniformMean (fun X : Fin 13 → SymMatrix K (N+1) => ∏ e∈F, pairSign X e)| ≤
      Real.sqrt (1/(Fintype.card K : ℝ)) +
        minorBadBound N (selectedIncident F v).card (Fintype.card K) := by
  let : Nonempty (selectedIncident F v) := ⟨⟨hne.choose,hne.choose_spec⟩⟩
  rw [uniformMean_bordered]
  simp_rw [pairSign_product_split hN F v]
  have he (W : Fin 13 → SymMatrix K N) := uniformMean_swap
    (fun z a => nonincidentProduct F v W z a * starSign v
      (fun e : selectedIncident F v => pairOther v e.val) W z a)
  simp_rw [he]
  simpa only [Fintype.card_coe] using testedStar_mean_bound hK v _ (pairOther_injective F v)
    (fun e => pairOther_ne v e.val (Finset.mem_filter.mp e.property).2)
    (by simpa using hc) (nonincidentProduct F v)
    (nonincidentProduct_abs_le F v) (nonincidentProduct_update F v)

private instance certificate_instance_0911 : OAI.SidorenkoCounterexample.ProofCertificate_0911 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10
  exact @certificate_proof_0911 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10

end Moment
theorem certificate_proof_0912 (N s : ℕ) (h : s<(N-s+1).choose 2) :
    Tendsto (minorBadBound N s) atTop (nhds 0) := by
  have ha : Tendsto (fun q : ℝ => (s : ℝ)*N/q) atTop (nhds 0) := by
    simpa only [mul_zero,div_eq_mul_inv] using
      (tendsto_inv_atTop_zero (𝕜 := ℝ)).const_mul ((s : ℝ)*N)
  have hb : Tendsto (fun q : ℝ => q^s*(2^(N-s)/q^((N-s+1).choose 2))) atTop (nhds 0) := by
    have ht := (inverse_power_tendsto_zero ((N-s+1).choose 2-s) (by omega)).const_mul ((2 : ℝ)^(N-s))
    simp only [mul_zero] at ht
    apply ht.congr' (eventually_atTop.mpr ⟨1,fun q hq => ?_⟩)
    have hq0 : q≠0 := by linarith
    have hn : (N-s+1).choose 2=s+((N-s+1).choose 2-s) := by omega
    rw [hn,pow_add]
    field_simp
    congr 1; omega
  change Tendsto (fun q : ℝ => (s : ℝ)*N/q + q^s*(2^(N-s)/q^((N-s+1).choose 2))) atTop (nhds 0)
  simpa only [add_zero] using ha.add hb

private instance certificate_instance_0912 : OAI.SidorenkoCounterexample.ProofCertificate_0912 := by
  constructor
  intro q0 q1 q2
  exact @certificate_proof_0912 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 q0 q1 q2

end SidorenkoCounterexample
end
section
namespace SidorenkoCounterexample
open Classical Filter
open scoped BigOperators
section Product
variable {I : Type} [DecidableEq I]
end Product
section Mean
variable {I A : Type} [Fintype I] [DecidableEq I] [Fintype A]
end Mean
end SidorenkoCounterexample
end
section
namespace SidorenkoCounterexample
open Module Classical Filter
open scoped BigOperators
section Difference
variable {K I W : Type} [Field K] [Fintype I] [DecidableEq I]
  [AddCommGroup W] [Module K W] [Fintype W]
end Difference
section Pair
variable {K : Type} [Field K] [Fintype K] [DecidableEq K] {D : ℕ}
end Pair
end SidorenkoCounterexample
end
section
namespace SidorenkoCounterexample
open Module Classical
open scoped BigOperators
section Graph
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
end Graph
end SidorenkoCounterexample
end
end OAI

theorem solution : OAI.SidorenkoCounterexample.ProofCertificate_0878 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0879 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0880 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0881 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0882 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0883 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0884 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0885 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0886 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0887 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0888 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0889 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0890 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0891 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0892 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0893 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0894 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0895 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0896 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0897 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0898 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0899 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0900 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0901 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0902 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0903 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0904 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0905 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0906 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0907 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0908 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0909 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0910 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0911 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0912 := by
  exact ⟨inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance⟩
end

