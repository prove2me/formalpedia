-- Prove2me | solution 1 for OAI.SidorenkoCounterexample.finite_geometry_batch_30
-- status  : ACCEPTED   (prove)
-- author  : @abcdefg
-- created : 2026-10-09T06:36:21.755121+00:00
-- url     : https://prove2.me/submissions/decd0017-8d11-440e-8def-fa9da04ce859

import Definitions.Def_SidorenkoCertificateBundleB
set_option linter.unusedVariables false
section
variable [p0 : OAI.SidorenkoCounterexample.ProofCertificate_0005]
  [p1 : OAI.SidorenkoCounterexample.ProofCertificate_0006]
  [p2 : OAI.SidorenkoCounterexample.ProofCertificate_0010]
  [p3 : OAI.SidorenkoCounterexample.ProofCertificate_0036]
  [p4 : OAI.SidorenkoCounterexample.ProofCertificate_0069]
  [p5 : OAI.SidorenkoCounterexample.ProofCertificate_0198]
  [p6 : OAI.SidorenkoCounterexample.ProofCertificate_0199]
  [p7 : OAI.SidorenkoCounterexample.ProofCertificate_0208]
  [p8 : OAI.SidorenkoCounterexample.ProofCertificate_0209]
  [p9 : OAI.SidorenkoCounterexample.ProofCertificate_0598]
  [p10 : OAI.SidorenkoCounterexample.ProofCertificate_0635]
  [p11 : OAI.SidorenkoCounterexample.ProofCertificate_0647]
  [p12 : OAI.SidorenkoCounterexample.ProofCertificate_0656]
  [p13 : OAI.SidorenkoCounterexample.ProofCertificate_0658]
  [p14 : OAI.SidorenkoCounterexample.ProofCertificate_0660]
  [p15 : OAI.SidorenkoCounterexample.ProofCertificate_0662]
  [p16 : OAI.SidorenkoCounterexample.ProofCertificate_0678]
  [p17 : OAI.SidorenkoCounterexample.ProofCertificate_0715]
  [p18 : OAI.SidorenkoCounterexample.ProofCertificate_0787]
  [p19 : OAI.SidorenkoCounterexample.ProofCertificate_0791]
  [p20 : OAI.SidorenkoCounterexample.ProofCertificate_0793]
  [p21 : OAI.SidorenkoCounterexample.ProofCertificate_0824]
  [p22 : OAI.SidorenkoCounterexample.ProofCertificate_0840]
  [p23 : OAI.SidorenkoCounterexample.ProofCertificate_0854]
  [p24 : OAI.SidorenkoCounterexample.ProofCertificate_0855]
  [p25 : OAI.SidorenkoCounterexample.ProofCertificate_0898]
  [p26 : OAI.SidorenkoCounterexample.ProofCertificate_0899]
  [p27 : OAI.SidorenkoCounterexample.ProofCertificate_0902]
  [p28 : OAI.SidorenkoCounterexample.ProofCertificate_0904]
  [p29 : OAI.SidorenkoCounterexample.ProofCertificate_0911]
  [p30 : OAI.SidorenkoCounterexample.ProofCertificate_0912]
include p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30

namespace OAI
section
namespace SidorenkoCounterexample
open Module Classical
open scoped BigOperators
section StarMoment
variable {K I J : Type} [Field K] [Fintype K] [DecidableEq K]
  [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] [Nonempty J] {N : ℕ}
end StarMoment
end SidorenkoCounterexample
end
section
namespace SidorenkoCounterexample
open Module Classical
open scoped BigOperators
section Signs
variable {K : Type} [Field K] [Fintype K] [DecidableEq K] {D : ℕ}
end Signs
end SidorenkoCounterexample
end
section
namespace SidorenkoCounterexample
open Module Classical Filter
open scoped BigOperators
section Moment
variable {K : Type} [Field K] [Fintype K] [DecidableEq K] {N : ℕ}
end Moment
theorem certificate_proof_0913 (N s : ℕ) (hN : 11≤N) (hs : s≤6) :
    s≤N ∧ s<(N-s+1).choose 2 := by
  have hd : 6≤N-s+1 := by omega
  have hc := Nat.choose_le_choose 2 hd
  rw [show (6:ℕ).choose 2=15 by decide] at hc
  omega

private instance certificate_instance_0913 : OAI.SidorenkoCounterexample.ProofCertificate_0913 := by
  constructor
  intro q0 q1 q2 q3
  exact @certificate_proof_0913 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 q0 q1 q2 q3

theorem certificate_proof_0914 (D : ℕ) (hD : Even D) (hbig : 12≤D)
    (F : Finset (Fin 33)) (hF : F.Nonempty) :
    Tendsto (fun q : OddPrime => uniformMean (fun X : Fin 13 → SymMatrix (ZMod q.val) D =>
      ∏ e∈F, pairSign X e)) primeInfinity (nhds 0) := by
  obtain ⟨e,he⟩ := hF
  let v := pairLeft e
  have hi : (selectedIncident F v).Nonempty := by
    refine ⟨e,Finset.mem_filter.mpr ⟨he,?_⟩⟩
    rw [pair_endpoints]; exact Finset.mem_insert_self _ _
  have hn : D=D-1+1 := by omega
  have hn' : Even (D-1+1) := hn ▸ hD
  have hc := sign_moment_dimension (D-1) (selectedIncident F v).card (by omega) (selectedIncident_card F v)
  have ht : Tendsto (fun q : OddPrime => Real.sqrt (1/(q.val : ℝ)) +
      minorBadBound (D-1) (selectedIncident F v).card q.val) primeInfinity (nhds 0) := by
    have ha := Real.continuous_sqrt.continuousAt.tendsto.comp
      ((inverse_power_tendsto_zero 1 (by omega)).comp primeInfinity_real_tendsto)
    simpa only [pow_one,Real.sqrt_zero,add_zero,Function.comp_def] using ha.add
      ((minorBadBound_tendsto (D-1) _ hc.2).comp primeInfinity_real_tendsto)
  apply squeeze_zero_norm (fun q => ?_) ht
  rw [Real.norm_eq_abs]
  conv_lhs => rw [hn]
  simpa only [ZMod.card] using pairSign_moment_bound
    (K := ZMod q.val) (by simpa only [ZMod.ringChar_zmod_n] using q.property.2) hn' F v hi hc.1

private instance certificate_instance_0914 : OAI.SidorenkoCounterexample.ProofCertificate_0914 := by
  constructor
  intro q0 q1 q2 q3 q4
  exact @certificate_proof_0914 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 q0 q1 q2 q3 q4

end SidorenkoCounterexample
end
section
namespace SidorenkoCounterexample
open Classical Filter
open scoped BigOperators
section Product
variable {I : Type} [DecidableEq I]
omit [DecidableEq I] in
theorem certificate_proof_0915 (s : Finset I) (f : I → ℝ) {C : ℝ} (_hC : 0≤C)
    (hf : ∀ i∈s, |f i|≤C) : |∏ i∈s, f i|≤C^s.card := by
  rw [Finset.abs_prod,←Finset.prod_const]
  exact Finset.prod_le_prod (fun _ _ => abs_nonneg _) hf

private instance certificate_instance_0915 : OAI.SidorenkoCounterexample.ProofCertificate_0915 := by
  constructor
  intro q0 q1 q2 q3 q4 q5
  exact @certificate_proof_0915 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 q0 q1 q2 q3 q4 q5

theorem certificate_proof_0916 (s : Finset I) (f g : I → ℝ) {C : ℝ} (hC : 1≤C)
    (hf : ∀ i∈s, |f i|≤C) (hg : ∀ i∈s, |g i|≤C) :
    |(∏ i∈s, f i)-(∏ i∈s, g i)| ≤ C^s.card * ∑ i∈s, |f i-g i| := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    have hC0 : 0≤C := le_trans (by norm_num) hC
    have hf' := fun i hi => hf i (Finset.mem_insert_of_mem hi)
    have hg' := fun i hi => hg i (Finset.mem_insert_of_mem hi)
    specialize ih hf' hg'
    rw [Finset.prod_insert ha,Finset.prod_insert ha,Finset.card_insert_of_notMem ha,
      Finset.sum_insert ha,pow_succ]
    calc
      _ = |f a*((∏ i∈s, f i)-(∏ i∈s, g i)) + (f a-g a)*(∏ i∈s, g i)| := by congr 1; ring
      _ ≤ |f a*((∏ i∈s, f i)-(∏ i∈s, g i))| + |(f a-g a)*(∏ i∈s, g i)| := abs_add_le _ _
      _ = |f a| * |(∏ i∈s, f i)-(∏ i∈s, g i)| + |f a-g a| * |∏ i∈s, g i| := by simp only [abs_mul]
      _ ≤ C*(C^s.card*∑ i∈s, |f i-g i|) + |f a-g a| * C^s.card :=
        add_le_add (mul_le_mul (hf a (Finset.mem_insert_self ..)) ih (abs_nonneg _) hC0)
          (mul_le_mul_of_nonneg_left (abs_prod_le_pow s g hC0 hg') (abs_nonneg _))
      _ ≤ _ := by
        have h : |f a-g a| * C^s.card ≤ C*(|f a-g a| * C^s.card) :=
          le_mul_of_one_le_left (mul_nonneg (abs_nonneg _) (pow_nonneg hC0 _)) hC
        nlinarith

private instance certificate_instance_0916 : OAI.SidorenkoCounterexample.ProofCertificate_0916 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8
  exact @certificate_proof_0916 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 q0 q1 q2 q3 q4 q5 q6 q7 q8

theorem certificate_proof_0917 (s : Finset I) (f g : I → ℝ)
    (hf : ∀ i∈s, |f i|≤1) (hg : ∀ i∈s, |g i|≤1) :
    |(∏ i∈s, f i)-(∏ i∈s, g i)| ≤ ∑ i∈s, |f i-g i| := by
  simpa only [one_pow,one_mul] using product_difference_bound s f g (le_refl 1) hf hg

private instance certificate_instance_0917 : OAI.SidorenkoCounterexample.ProofCertificate_0917 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6
  exact @certificate_proof_0917 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 q0 q1 q2 q3 q4 q5 q6

end Product
section Mean
variable {I A : Type} [Fintype I] [DecidableEq I] [Fintype A]
omit [Fintype I] [DecidableEq I] in
theorem certificate_proof_0918 (s : Finset I) (f : I → A → ℝ) :
    uniformMean (fun a => ∑ i∈s, f i a)=∑ i∈s, uniformMean (f i) := by
  unfold uniformMean
  rw [Finset.sum_comm,Finset.sum_div]

private instance certificate_instance_0918 : OAI.SidorenkoCounterexample.ProofCertificate_0918 := by
  constructor
  intro q0 q1 q2 q3 q4
  exact @certificate_proof_0918 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 q0 q1 q2 q3 q4

theorem certificate_proof_0919 (f : I → A → ℝ) :
    uniformMean (fun x : I → A => ∏ i, f i (x i))=∏ i, uniformMean (f i) := by
  unfold uniformMean
  rw [←Fintype.prod_sum,Finset.prod_div_distrib,Finset.prod_const,Finset.card_univ,
    Fintype.card_fun,Nat.cast_pow]

private instance certificate_instance_0919 : OAI.SidorenkoCounterexample.ProofCertificate_0919 := by
  constructor
  intro q0 q1 q2 q3 q4 q5
  exact @certificate_proof_0919 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 q0 q1 q2 q3 q4 q5

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
include K in
theorem certificate_proof_0920 (i k : I) (hik : i≠k) (f : W → ℝ) :
    uniformMean (fun X : I → W => f (X i-X k))=uniformMean f := by
  let L : (I → W) →ₗ[K] W :=
    { toFun := fun X => X i-X k
      map_add' := by intros; simp only [Pi.add_apply]; abel
      map_smul' := by intros; simp only [Pi.smul_apply,smul_sub,RingHom.id_apply] }
  have hL : Function.Surjective L := by
    intro w
    refine ⟨Function.update 0 i w,?_⟩
    change (Function.update (0 : I → W) i w) i-(Function.update (0 : I → W) i w) k=w
    simp [Function.update_of_ne hik.symm]
  exact uniformMean_surjective_linear L hL f

private instance certificate_instance_0920 : OAI.SidorenkoCounterexample.ProofCertificate_0920 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12
  exact @certificate_proof_0920 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12

end Difference
section Pair
variable {K : Type} [Field K] [Fintype K] [DecidableEq K] {D : ℕ}
omit [Fintype K] in
theorem certificate_proof_0921 (X : Fin 13 → SymMatrix K D) (e : Fin 33) : 0≤pairSingular X e := by
  unfold pairSingular; split <;> norm_num

private instance certificate_instance_0921 : OAI.SidorenkoCounterexample.ProofCertificate_0921 := by
  constructor
  intro q0 q1 q2 q3 q4 q5
  exact @certificate_proof_0921 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 q0 q1 q2 q3 q4 q5

theorem certificate_proof_0922 (e : Fin 33) :
    uniformMean (fun X : Fin 13 → SymMatrix K D => pairSingular X e)≤(D : ℝ)/Fintype.card K := by
  unfold pairSingular
  rw [uniformMean_point_difference (K := K) _ _ (pair_endpoints_ne e)
    (fun B : SymMatrix K D => if B.val.det=0 then 1 else 0)]
  exact symmetricSingularProb_bound D

private instance certificate_instance_0922 : OAI.SidorenkoCounterexample.ProofCertificate_0922 := by
  constructor
  intro q0 q1 q2 q3 q4 q5
  exact @certificate_proof_0922 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 q0 q1 q2 q3 q4 q5

omit [Fintype K] in
theorem certificate_proof_0923 (X : Fin 13 → SymMatrix K D) :
    (if fullTransverse X then 0 else 1 : ℝ) ≤ ∑ e, pairSingular X e := by
  by_cases h : fullTransverse X
  · rw [if_pos h]; exact Finset.sum_nonneg fun e _ => pairSingular_nonneg X e
  · rw [if_neg h]
    obtain ⟨e,he⟩ := not_forall.mp h
    have he := not_not.mp he
    calc
      (1 : ℝ) = pairSingular X e := by rw [pairSingular,if_pos he]
      _ ≤ _ := Finset.single_le_sum (fun e _ => pairSingular_nonneg X e) (Finset.mem_univ e)

private instance certificate_instance_0923 : OAI.SidorenkoCounterexample.ProofCertificate_0923 := by
  constructor
  intro q0 q1 q2 q3 q4
  exact @certificate_proof_0923 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 q0 q1 q2 q3 q4

theorem certificate_proof_0924 :
    uniformMean (fun X : Fin 13 → SymMatrix K D => if fullTransverse X then 0 else 1) ≤
      33*((D : ℝ)/Fintype.card K) := by
  apply (uniformMean_mono nonTransverse_pointwise).trans
  rw [uniformMean_sum]
  calc
    _ ≤ ∑ _e : Fin 33, (D : ℝ)/Fintype.card K := Finset.sum_le_sum fun e _ => pairSingular_mean e
    _ = _ := by simp

private instance certificate_instance_0924 : OAI.SidorenkoCounterexample.ProofCertificate_0924 := by
  constructor
  intro q0 q1 q2 q3 q4
  exact @certificate_proof_0924 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 q0 q1 q2 q3 q4

theorem certificate_proof_0925 (b : Bool) : |boolSign b|=1 := by cases b <;> norm_num [boolSign]

private instance certificate_instance_0925 : OAI.SidorenkoCounterexample.ProofCertificate_0925 := by
  constructor
  intro q0
  exact @certificate_proof_0925 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 q0

theorem certificate_proof_0926 (b : Bool) : boolSign b^2=1 := by cases b <;> norm_num [boolSign]

private instance certificate_instance_0926 : OAI.SidorenkoCounterexample.ProofCertificate_0926 := by
  constructor
  intro q0
  exact @certificate_proof_0926 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 q0

theorem certificate_proof_0927 (X : Fin 13 → SymMatrix K D) (e : Fin 33) :
    |boolSign (pairBool X e)-pairSign X e| ≤ pairSingular X e := by
  by_cases hz : (X (pairLeft e)-X (pairRight e)).val.det=0
  · have he : pairSign X e=0 := by unfold pairSign; rw [hz]; norm_num
    rw [pairSingular,if_pos hz,he]
    simp
  · have he : pairSign X e=1 ∨ pairSign X e= -1 := by
      unfold pairSign
      rcases quadraticChar_dichotomy (F := K) hz with h | h <;> rw [h] <;> norm_num
    rw [pairSingular,if_neg hz]
    rcases he with he | he <;> norm_num [pairBool,he,boolSign]

private instance certificate_instance_0927 : OAI.SidorenkoCounterexample.ProofCertificate_0927 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6
  exact @certificate_proof_0927 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 q0 q1 q2 q3 q4 q5 q6

theorem certificate_proof_0928 (F : Finset (Fin 33)) :
    |uniformMean (fun X : Fin 13 → SymMatrix K D => ∏ e∈F, boolSign (pairBool X e))-
      uniformMean (fun X : Fin 13 → SymMatrix K D => ∏ e∈F, pairSign X e)| ≤
        (F.card : ℝ)*((D : ℝ)/Fintype.card K) := by
  rw [←uniformMean_sub]
  apply (abs_uniformMean_le _).trans
  calc
    _ ≤ uniformMean (fun X : Fin 13 → SymMatrix K D => ∑ e∈F, pairSingular X e) := by
      apply uniformMean_mono
      intro X
      exact (product_difference_unit F _ _ (by simp) (fun e _ => pairSign_abs_le X e)).trans
        (Finset.sum_le_sum fun e _ => pairBool_error X e)
    _ = ∑ e∈F, uniformMean (fun X : Fin 13 → SymMatrix K D => pairSingular X e) := uniformMean_finset_sum _ _
    _ ≤ ∑ _e∈F, (D : ℝ)/Fintype.card K := Finset.sum_le_sum fun e _ => pairSingular_mean e
    _ = _ := by simp

private instance certificate_instance_0928 : OAI.SidorenkoCounterexample.ProofCertificate_0928 := by
  constructor
  intro q0 q1 q2 q3 q4 q5
  exact @certificate_proof_0928 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 q0 q1 q2 q3 q4 q5

end Pair
theorem certificate_proof_0929 (D : ℕ) (hD : Even D) (hbig : 12≤D)
    (F : Finset (Fin 33)) (hF : F.Nonempty) :
    Tendsto (fun q : OddPrime => uniformMean (fun X : Fin 13 → SymMatrix (ZMod q.val) D =>
      ∏ e∈F, boolSign (pairBool X e))) primeInfinity (nhds 0) := by
  have hm := pairSign_moment_tendsto D hD hbig F hF
  have hb : Tendsto (fun q : OddPrime => (F.card : ℝ)*((D : ℝ)/(q.val : ℝ))) primeInfinity (nhds 0) := by
    simpa only [mul_zero,Function.comp_def,div_eq_mul_inv] using
      (((tendsto_inv_atTop_zero (𝕜 := ℝ)).comp primeInfinity_real_tendsto).const_mul (D : ℝ)).const_mul (F.card : ℝ)
  have he : Tendsto (fun q : OddPrime =>
      uniformMean (fun X : Fin 13 → SymMatrix (ZMod q.val) D => ∏ e∈F, boolSign (pairBool X e))-
      uniformMean (fun X : Fin 13 → SymMatrix (ZMod q.val) D => ∏ e∈F, pairSign X e)) primeInfinity (nhds 0) := by
    apply squeeze_zero_norm (fun q => ?_) hb
    simpa only [Real.norm_eq_abs,ZMod.card] using pairBool_moment_error (K := ZMod q.val) (D := D) F
  simpa only [sub_add_cancel,add_zero] using he.add hm

private instance certificate_instance_0929 : OAI.SidorenkoCounterexample.ProofCertificate_0929 := by
  constructor
  intro q0 q1 q2 q3 q4
  exact @certificate_proof_0929 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 q0 q1 q2 q3 q4

end SidorenkoCounterexample
end
section
namespace SidorenkoCounterexample
open Module Classical
open scoped BigOperators
section Graph
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
theorem certificate_proof_0930 (D : ℕ) : Function.Injective (matrixLagrangian (K := K) (D := D)) := by
  intro A B h
  apply Subtype.ext
  apply Matrix.toBilin'.injective
  exact fullGraph_injective (congrArg Subtype.val h)

private instance certificate_instance_0930 : OAI.SidorenkoCounterexample.ProofCertificate_0930 := by
  constructor
  intro c0 q0 q1 q2
  exact @certificate_proof_0930 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 q0 q1 q2

theorem certificate_proof_0931 (D : ℕ) (A B : SymMatrix K D) :
    finrank K ↥((matrixLagrangian A).val⊓(matrixLagrangian B).val)+(A-B).val.rank=D := by
  have h := ((A-B).val.toBilin').ker.finrank_quotient_add_finrank
  rw [matrix_radical_quotient_rank] at h
  have he := (fullGraphIntersection A.val.toBilin' B.val.toBilin').finrank_eq
  have hf : (A-B).val.toBilin'=A.val.toBilin'-B.val.toBilin' := by rw [Submodule.coe_sub,map_sub]
  rw [hf] at h
  simp only [Module.finrank_pi,Fintype.card_fin] at h
  change finrank K ↥(A.val.toBilin'.graph⊓B.val.toBilin'.graph)+(A-B).val.rank=D
  omega

private instance certificate_instance_0931 : OAI.SidorenkoCounterexample.ProofCertificate_0931 := by
  constructor
  intro c0 q0 q1 q2 q3 q4
  exact @certificate_proof_0931 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 q0 q1 q2 q3 q4

theorem certificate_proof_0932 (D : ℕ) (A B : SymMatrix K D) :
    finrank K ↥((matrixLagrangian A).val⊓(matrixLagrangian B).val)=0 ↔ (A-B).val.det≠0 := by
  change finrank K ↥(A.val.toBilin'.graph⊓B.val.toBilin'.graph)=0 ↔ (A-B).val.det≠0
  rw [← (fullGraphIntersection A.val.toBilin' B.val.toBilin').finrank_eq]
  have hf : (A-B).val.toBilin'=A.val.toBilin'-B.val.toBilin' := by rw [Submodule.coe_sub,map_sub]
  rw [←hf,Submodule.finrank_eq_zero]
  exact LinearMap.BilinForm.nondegenerate_iff_ker_eq_bot.symm.trans
    (Matrix.nondegenerate_toBilin'_iff.trans Matrix.nondegenerate_iff_det_ne_zero)

private instance certificate_instance_0932 : OAI.SidorenkoCounterexample.ProofCertificate_0932 := by
  constructor
  intro c0 q0 q1 q2 q3 q4
  exact @certificate_proof_0932 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 q0 q1 q2 q3 q4

end Graph
end SidorenkoCounterexample
end
end OAI
namespace OAI
section
namespace SidorenkoCounterexample
open Module Classical Filter
open scoped BigOperators
section Mean
variable {A B : Type} [Fintype A] [Fintype B] [Nonempty B]
theorem certificate_proof_0933 (i : A → B) (hi : Function.Injective i) (f : B → ℝ)
    (hf : ∀ b,0≤f b) : uniformMean (f ∘ i) ≤
      ((Fintype.card B : ℝ)/Fintype.card A)*uniformMean f := by
  classical
  have hs : ∑ a, f (i a) ≤ ∑ b, f b := by
    rw [←Finset.sum_image (fun a _ b _ h => hi h)]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun b _ _ => hf b)
  unfold uniformMean
  dsimp only [Function.comp_def]
  have hn : (Fintype.card B : ℝ)≠0 := by exact_mod_cast (Fintype.card_pos (α := B)).ne'
  have he : ((Fintype.card B : ℝ)/Fintype.card A)*((∑ b,f b)/Fintype.card B)=
      (∑ b,f b)/Fintype.card A := by
    calc
      _ = ((∑ b,f b)/Fintype.card A)*((Fintype.card B : ℝ)/Fintype.card B) := by ring
      _ = _ := by rw [div_self hn,mul_one]
  rw [he]
  exact div_le_div_of_nonneg_right hs (Nat.cast_nonneg _)

private instance certificate_instance_0933 : OAI.SidorenkoCounterexample.ProofCertificate_0933 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8
  exact @certificate_proof_0933 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 q0 q1 q2 q3 q4 q5 q6 q7 q8

end Mean
section Norm
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
omit [DecidableEq K] in
theorem certificate_proof_0934 (D : ℕ) : 0≤chartRatio (K := K) D := by unfold chartRatio; positivity

private instance certificate_instance_0934 : OAI.SidorenkoCounterexample.ProofCertificate_0934 := by
  constructor
  intro q0 q1 q2 q3
  exact @certificate_proof_0934 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 q0 q1 q2 q3

omit [DecidableEq K] in
theorem certificate_proof_0935 (D : ℕ) : chartRatio (K := K) D≤lagrangianConstant D := by
  have hc : (Fintype.card (SymMatrix K D) : ℝ)=(Fintype.card K : ℝ)^((D+1).choose 2) := by
    rw [←Nat.card_eq_fintype_card,symMatrix_card,Nat.cast_pow]
  have hn : (0 : ℝ)<(Fintype.card K : ℝ)^((D+1).choose 2) := by positivity
  unfold chartRatio
  rw [hc]
  apply (div_le_iff₀ hn).mpr
  simpa only [Module.finrank_pi,Fintype.card_fin] using lagrangian_card_upper (K := K) (V := Fin D → K)

private instance certificate_instance_0935 : OAI.SidorenkoCounterexample.ProofCertificate_0935 := by
  constructor
  intro q0 q1 q2 q3
  exact @certificate_proof_0935 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 q0 q1 q2 q3

omit [DecidableEq K] in
theorem certificate_proof_0936 (D r : ℕ) (hr : r≤D) :
    Nat.card (CenterStratum (K := K) (V := Fin D → K) r) =
      Nat.card (DimSubspace K (Fin D → K) (D-r)) * (Fintype.card K)^((D-r+1).choose 2) := by
  have hD : r≤finrank K (Fin D → K) := by simpa only [Module.finrank_pi,Fintype.card_fin] using hr
  have h := vertical_pair_count (K := K) (V := Fin D → K) r hD
  simpa only [Module.finrank_pi,Fintype.card_fin,CenterStratum,DimSubspace] using h

private instance certificate_instance_0936 : OAI.SidorenkoCounterexample.ProofCertificate_0936 := by
  constructor
  intro q0 q1 q2 q3 q4 q5
  exact @certificate_proof_0936 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 q0 q1 q2 q3 q4 q5

omit [DecidableEq K] in
theorem certificate_proof_0937 (D : ℕ) : (0 : ℝ)<Nat.card (Lagrangian (K := K) (V := Fin D → K)) := by
  exact lt_of_lt_of_le (by positivity) (lagrangian_card_lower (K := K) (V := Fin D → K))

private instance certificate_instance_0937 : OAI.SidorenkoCounterexample.ProofCertificate_0937 := by
  constructor
  intro q0 q1 q2 q3
  exact @certificate_proof_0937 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 q0 q1 q2 q3

omit [DecidableEq K] in
theorem certificate_proof_0938 (D r : ℕ) (hr : r≤D) : 0<canonicalStratumMass (K := K) D r := by
  have hl := subspace_count_lower (K := K) (V := Fin D → K) (D-r) (by simp)
  have hp : 0<(Nat.card (DimSubspace K (Fin D → K) (D-r)) : ℝ) := lt_of_lt_of_le (by positivity) hl
  unfold canonicalStratumMass
  rw [canonicalStratum_card D r hr,Nat.cast_mul,Nat.cast_pow]
  apply div_pos (mul_pos hp (by positivity))
  exact canonicalLag_card_pos (K := K) D

private instance certificate_instance_0938 : OAI.SidorenkoCounterexample.ProofCertificate_0938 := by
  constructor
  intro q0 q1 q2 q3 q4 q5
  exact @certificate_proof_0938 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 q0 q1 q2 q3 q4 q5

omit [DecidableEq K] in
theorem certificate_proof_0939 (D r : ℕ) (hr : r≤D) :
    canonicalStratumMass (K := K) D r*(Fintype.card K : ℝ)^((r+1).choose 2)≤2^(D-r) := by
  let n : ℝ := Nat.card (Lagrangian (K := K) (V := Fin D → K))
  have hn : 0<n := canonicalLag_card_pos (K := K) D
  have hc : (Nat.card (CenterStratum (K := K) (V := Fin D → K) r) : ℝ)=
      (Nat.card (DimSubspace K (Fin D → K) (D-r)) : ℝ)*(Fintype.card K : ℝ)^((D-r+1).choose 2) := by
    rw [canonicalStratum_card D r hr,Nat.cast_mul,Nat.cast_pow]
  have hu := subspace_count_upper (K := K) (V := Fin D → K) (D-r) (by simp)
  simp only [Module.finrank_pi,Fintype.card_fin,Nat.sub_sub_self hr] at hu
  have he : (D-r)*r+(D-r+1).choose 2+(r+1).choose 2=(D+1).choose 2 := by
    simpa only [Nat.mul_comm] using symmetric_nullity_exponent D r hr
  have hl : (Fintype.card K : ℝ)^((D+1).choose 2)≤n := by
    simpa only [Module.finrank_pi,Fintype.card_fin] using lagrangian_card_lower (K := K) (V := Fin D → K)
  change ((Nat.card (CenterStratum (K := K) (V := Fin D → K) r) : ℝ)/n)*_≤_
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ hn).mpr
  rw [hc]
  calc
    _ ≤ (2^(D-r)*(Fintype.card K : ℝ)^((D-r)*r)) *
        (Fintype.card K : ℝ)^((D-r+1).choose 2)*(Fintype.card K : ℝ)^((r+1).choose 2) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hu (by positivity)) (by positivity)
    _ = 2^(D-r)*(Fintype.card K : ℝ)^((D+1).choose 2) := by rw [mul_assoc,mul_assoc,←pow_add,←pow_add,←Nat.add_assoc,he]
    _ ≤ _ := mul_le_mul_of_nonneg_left hl (by positivity)

private instance certificate_instance_0939 : OAI.SidorenkoCounterexample.ProofCertificate_0939 := by
  constructor
  intro q0 q1 q2 q3 q4 q5
  exact @certificate_proof_0939 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 q0 q1 q2 q3 q4 q5

end Norm
theorem certificate_proof_0940 (r : ℕ) (hr : 0<r) {ξ : ℤ} (hξ : ξ=1 ∨ ξ= -1) :
    ∀ᶠ q : OddPrime in primeInfinity,
      canonicalStratumMass (K := ZMod q.val) (2*r) r /
        layerMass (ZMod q.val) (2*r) r ξ ≤ 4*2^r := by
  have h := (layerMass_tendsto (2*r) r hr (by omega) hξ).eventually (lt_mem_nhds (by norm_num : (1/4 : ℝ)<1/2))
  filter_upwards [h] with q hq
  have he : 2*r-r=r := by omega
  rw [he] at hq
  have hb := canonicalStratumMass_bound (K := ZMod q.val) (2*r) r (by omega)
  rw [he,ZMod.card] at hb
  have hp : (0:ℝ)<(q.val : ℝ)^((r+1).choose 2) := by exact pow_pos (by exact_mod_cast q.property.1.pos) _
  have hd : 0<layerMass (ZMod q.val) (2*r) r ξ := by nlinarith
  apply (div_le_iff₀ hd).mpr
  nlinarith [mul_pos hp hd, pow_pos (by norm_num : (0:ℝ)<2) r]

private instance certificate_instance_0940 : OAI.SidorenkoCounterexample.ProofCertificate_0940 := by
  constructor
  intro q0 q1 q2 q3
  exact @certificate_proof_0940 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 q0 q1 q2 q3

end SidorenkoCounterexample
end
section
namespace SidorenkoCounterexample
open Module Classical Filter
open scoped BigOperators
section Face
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
theorem certificate_proof_0941 (r : ℕ) (ξ : Fin 3 → ℤ) (X : Fin 3 → SymMatrix K (2*r)) :
    faceLocal r ∅ ξ X=1 := by simp [faceLocal,uniformMean_const]

private instance certificate_instance_0941 : OAI.SidorenkoCounterexample.ProofCertificate_0941 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6
  exact @certificate_proof_0941 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 q0 q1 q2 q3 q4 q5 q6

theorem certificate_proof_0942 (hK : ringChar K≠2) (r : ℕ) (hr : 0<r)
    (ξ : Fin 3 → ℤ) (hξ : ∀ k, ξ k=1 ∨ ξ k= -1) (X : Fin 3 → SymMatrix K (2*r)) (k : Fin 3) :
    faceLocal r {k} ξ X=1 := by
  simp only [faceLocal,Finset.prod_singleton]
  rw [uniformMean_subLeft,uniformMean_rankKernel _ _ hr (by omega) hK (hξ k)]

private instance certificate_instance_0942 : OAI.SidorenkoCounterexample.ProofCertificate_0942 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10
  exact @certificate_proof_0942 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10

theorem certificate_proof_0943 (r : ℕ) (ξ : Fin 3 → ℤ) (X : Fin 3 → SymMatrix K (2*r))
    (k l : Fin 3) (hkl : k≠l) :
    faceLocal r {k,l} ξ X=pairLocal r (ξ k) (ξ l) (X k-X l) := by
  simp only [faceLocal,Finset.prod_pair hkl,pairLocal]
  have he (Y : SymMatrix K (2*r)) : X l-Y=(X k-Y)-(X k-X l) := by abel
  simp_rw [he]
  exact uniformMean_subLeft (X k) (fun A => rankKernel K (2*r) r (ξ k) A *
    rankKernel K (2*r) r (ξ l) (A-(X k-X l)))

private instance certificate_instance_0943 : OAI.SidorenkoCounterexample.ProofCertificate_0943 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9
  exact @certificate_proof_0943 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9

theorem certificate_proof_0944 (r : ℕ) (ξ : Fin 3 → ℤ) (X : Fin 3 → SymMatrix K (2*r)) :
    faceLocal r Finset.univ ξ X=tripleLocal r (ξ 0) (ξ 1) (ξ 2) (X 0-X 1) (X 0-X 2) := by
  simp only [faceLocal,Fin.prod_univ_three,tripleLocal]
  have h1 (Y : SymMatrix K (2*r)) : X 1-Y=(X 0-Y)-(X 0-X 1) := by abel
  have h2 (Y : SymMatrix K (2*r)) : X 2-Y=(X 0-Y)-(X 0-X 2) := by abel
  simp_rw [h1,h2]
  exact uniformMean_subLeft (X 0) (fun A => rankKernel K (2*r) r (ξ 0) A *
    rankKernel K (2*r) r (ξ 1) (A-(X 0-X 1))*rankKernel K (2*r) r (ξ 2) (A-(X 0-X 2)))

private instance certificate_instance_0944 : OAI.SidorenkoCounterexample.ProofCertificate_0944 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6
  exact @certificate_proof_0944 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 q0 q1 q2 q3 q4 q5 q6

theorem certificate_proof_0945 (c x ξ ζ : ℤ) (hc : c=1 ∨ c= -1) (hx : x=1 ∨ x= -1)
    (hξ : ξ=1 ∨ ξ= -1) (hζ : ζ=1 ∨ ζ= -1) :
    (1+(c : ℝ)*(x : ℝ)*(ξ : ℝ)*(ζ : ℝ))=(if x=c*ξ*ζ then 2 else 0) := by
  rcases hc with rfl|rfl <;> rcases hx with rfl|rfl <;>
    rcases hξ with rfl|rfl <;> rcases hζ with rfl|rfl <;> norm_num

private instance certificate_instance_0945 : OAI.SidorenkoCounterexample.ProofCertificate_0945 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7
  exact @certificate_proof_0945 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 q0 q1 q2 q3 q4 q5 q6 q7

theorem certificate_proof_0946 (r : ℕ) {ξ ζ : ℤ} (hξ : ξ=1 ∨ ξ= -1) (hζ : ζ=1 ∨ ζ= -1)
    (B : SymMatrix K (2*r)) (hB : B.val.det≠0) :
    pairPolynomial r ξ ζ B=if pairMatch r ξ ζ B then 2 else 0 := by
  have he := signs_polynomial _ _ _ _ (quadraticChar_dichotomy (F := K) (pow_ne_zero r (neg_ne_zero.mpr one_ne_zero)))
    (quadraticChar_dichotomy hB) hξ hζ
  unfold pairPolynomial pairMatch
  split_ifs with hm
  · rw [if_pos hm] at he; exact he
  · rw [if_neg hm] at he; exact he

private instance certificate_instance_0946 : OAI.SidorenkoCounterexample.ProofCertificate_0946 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10
  exact @certificate_proof_0946 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10

theorem certificate_proof_0947 (r : ℕ) (ξ : Fin 3 → ℤ) (hξ : ∀ k, ξ k=1 ∨ ξ k= -1)
    (X : Fin 3 → SymMatrix K (2*r)) (hX : faceTransverse r X) :
    facePolynomial r Finset.univ ξ X=
      if tripleMatch r (ξ 0) (ξ 1) (ξ 2) (X 0-X 1) (X 0-X 2) then 8 else 0 := by
  unfold facePolynomial
  simp only [Finset.mem_univ,and_self,ite_true]
  rw [pairPolynomial_eq r (hξ 0) (hξ 1) _ hX.1,
    pairPolynomial_eq r (hξ 0) (hξ 2) _ hX.2.1,pairPolynomial_eq r (hξ 1) (hξ 2) _ hX.2.2]
  have he : X 0-X 2-(X 0-X 1)=X 1-X 2 := by abel
  simp only [tripleMatch,he]
  split_ifs <;> norm_num <;> tauto

private instance certificate_instance_0947 : OAI.SidorenkoCounterexample.ProofCertificate_0947 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8
  exact @certificate_proof_0947 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 q0 q1 q2 q3 q4 q5 q6 q7 q8

theorem certificate_proof_0948 (r : ℕ) (ξ : Fin 3 → ℤ) (X : Fin 3 → SymMatrix K (2*r)) :
    0≤faceError r ξ X := by
  exact add_nonneg (add_nonneg (add_nonneg (pairError_nonneg ..) (pairError_nonneg ..))
    (pairError_nonneg ..)) (tripleError_nonneg ..)

private instance certificate_instance_0948 : OAI.SidorenkoCounterexample.ProofCertificate_0948 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6
  exact @certificate_proof_0948 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 q0 q1 q2 q3 q4 q5 q6

theorem certificate_proof_0949 (hK : ringChar K≠2) (r : ℕ) (hr : 0<r) (T : Finset (Fin 3))
    (ξ : Fin 3 → ℤ) (hξ : ∀ k, ξ k=1 ∨ ξ k= -1)
    (X : Fin 3 → SymMatrix K (2*r)) (hX : faceTransverse r X) :
    |faceLocal r T ξ X-facePolynomial r T ξ X|≤faceError r ξ X := by
  have he : X 0-X 2-(X 0-X 1)=X 1-X 2 := by abel
  have hfull : (X 0-X 1).val.det≠0 ∧ (X 0-X 2).val.det≠0 ∧
      (X 0-X 2-(X 0-X 1)).val.det≠0 := by simpa only [he,faceTransverse] using hX
  have n01 := pairError_nonneg r (ξ 0) (ξ 1) (X 0-X 1)
  have n02 := pairError_nonneg r (ξ 0) (ξ 2) (X 0-X 2)
  have n12 := pairError_nonneg r (ξ 1) (ξ 2) (X 1-X 2)
  have nt := tripleError_nonneg r (ξ 0) (ξ 1) (ξ 2) (X 0-X 1) (X 0-X 2)
  rcases fin3_subsets T with ht|ht|ht|ht|ht|ht|ht|ht
  · subst T; simpa [facePolynomial] using faceError_nonneg r ξ X
  · subst T; rw [faceLocal_singleton hK r hr ξ hξ]; simpa [facePolynomial] using faceError_nonneg r ξ X
  · subst T; rw [faceLocal_singleton hK r hr ξ hξ]; simpa [facePolynomial] using faceError_nonneg r ξ X
  · subst T; rw [faceLocal_singleton hK r hr ξ hξ]; simpa [facePolynomial] using faceError_nonneg r ξ X
  · subst T
    rw [faceLocal_pair r ξ X 0 1 (by decide)]
    simp [facePolynomial, show (2 : Fin 3)≠0 from by decide, show (2 : Fin 3)≠1 from by decide]
    rw [pairPolynomial_eq r (hξ 0) (hξ 1) _ hX.1]
    have hp : pairError r (ξ 0) (ξ 1) (X 0-X 1)=
        |pairLocal r (ξ 0) (ξ 1) (X 0-X 1)-(if pairMatch r (ξ 0) (ξ 1) (X 0-X 1) then 2 else 0)| := by
      rw [pairError,if_pos hX.1]
    unfold faceError; linarith
  · subst T
    rw [faceLocal_pair r ξ X 0 2 (by decide)]
    simp [facePolynomial, show (1 : Fin 3)≠0 from by decide, show (1 : Fin 3)≠2 from by decide]
    rw [pairPolynomial_eq r (hξ 0) (hξ 2) _ hX.2.1]
    have hp : pairError r (ξ 0) (ξ 2) (X 0-X 2)=
        |pairLocal r (ξ 0) (ξ 2) (X 0-X 2)-(if pairMatch r (ξ 0) (ξ 2) (X 0-X 2) then 2 else 0)| := by
      rw [pairError,if_pos hX.2.1]
    unfold faceError; linarith
  · subst T
    rw [faceLocal_pair r ξ X 1 2 (by decide)]
    simp [facePolynomial, show (0 : Fin 3)≠1 from by decide, show (0 : Fin 3)≠2 from by decide]
    rw [pairPolynomial_eq r (hξ 1) (hξ 2) _ hX.2.2]
    have hp : pairError r (ξ 1) (ξ 2) (X 1-X 2)=
        |pairLocal r (ξ 1) (ξ 2) (X 1-X 2)-(if pairMatch r (ξ 1) (ξ 2) (X 1-X 2) then 2 else 0)| := by
      rw [pairError,if_pos hX.2.2]
    unfold faceError; linarith
  · subst T
    rw [faceLocal_full,facePolynomial_full r ξ hξ X hX]
    have hp : tripleError r (ξ 0) (ξ 1) (ξ 2) (X 0-X 1) (X 0-X 2)=
        |tripleLocal r (ξ 0) (ξ 1) (ξ 2) (X 0-X 1) (X 0-X 2)-
          (if tripleMatch r (ξ 0) (ξ 1) (ξ 2) (X 0-X 1) (X 0-X 2) then 8 else 0)| := by
      rw [tripleError,if_pos hfull]
    unfold faceError; linarith

private instance certificate_instance_0949 : OAI.SidorenkoCounterexample.ProofCertificate_0949 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11
  exact @certificate_proof_0949 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11

end Face
end SidorenkoCounterexample
end
section
namespace SidorenkoCounterexample
open Classical Filter
open scoped BigOperators
section Boolean
variable {I : Type} [Fintype I] [DecidableEq I]
omit [Fintype I] [DecidableEq I] in
theorem certificate_proof_0950 (η : I → Bool) : boolMonomial ∅ η=1 := by simp [boolMonomial]

private instance certificate_instance_0950 : OAI.SidorenkoCounterexample.ProofCertificate_0950 := by
  constructor
  intro q0 q1
  exact @certificate_proof_0950 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 q0 q1

theorem certificate_proof_0951 (a b : Bool) : 1+boolSign a*boolSign b=if a=b then 2 else 0 := by
  cases a <;> cases b <;> norm_num [boolSign]

private instance certificate_instance_0951 : OAI.SidorenkoCounterexample.ProofCertificate_0951 := by
  constructor
  intro q0 q1
  exact @certificate_proof_0951 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 q0 q1

omit [DecidableEq I] in
theorem certificate_proof_0952 (η ε : I → Bool) :
    (if η=ε then 1 else 0 : ℝ) = (2^Fintype.card I : ℝ)⁻¹ *
      ∏ i, (1+boolSign (η i)*boolSign (ε i)) := by
  simp_rw [bool_factor]
  by_cases h : η=ε
  · subst ε
    simp
  · rw [if_neg h]
    obtain ⟨i,hi⟩ := Function.ne_iff.mp h
    have hp : (∏ i, (if η i=ε i then 2 else 0 : ℝ))=0 :=
      Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)
    rw [hp,mul_zero]

private instance certificate_instance_0952 : OAI.SidorenkoCounterexample.ProofCertificate_0952 := by
  constructor
  intro q0 q1 q2 q3
  exact @certificate_proof_0952 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 q0 q1 q2 q3

variable {A : Type} [Fintype A]
end Boolean
section Convergence
variable {I Q : Type} [Fintype I] [DecidableEq I] {l : Filter Q}
  {A : Q → Type} [∀ q, Fintype (A q)] [∀ q, Nonempty (A q)]
end Convergence
end SidorenkoCounterexample
end
section
namespace SidorenkoCounterexample
open Module Classical Filter
open scoped BigOperators
section Means
variable {K I W : Type} [Field K] [Fintype I] [DecidableEq I]
  [AddCommGroup W] [Module K W] [Fintype W]
end Means
section Bounds
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
end Bounds
end SidorenkoCounterexample
end
section
namespace SidorenkoCounterexample
open Module Classical
open scoped BigOperators
section ChartFace
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
end ChartFace
end SidorenkoCounterexample
end
end OAI

theorem solution : OAI.SidorenkoCounterexample.ProofCertificate_0913 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0914 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0915 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0916 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0917 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0918 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0919 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0920 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0921 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0922 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0923 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0924 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0925 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0926 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0927 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0928 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0929 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0930 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0931 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0932 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0933 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0934 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0935 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0936 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0937 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0938 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0939 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0940 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0941 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0942 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0943 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0944 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0945 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0946 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0947 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0948 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0949 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0950 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0951 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0952 := by
  exact ⟨inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance⟩
end

