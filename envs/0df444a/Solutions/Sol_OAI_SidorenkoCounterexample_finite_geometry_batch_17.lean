-- Prove2me | solution 1 for OAI.SidorenkoCounterexample.finite_geometry_batch_17
-- status  : ACCEPTED   (prove)
-- author  : @abcdefg
-- created : 2026-10-09T06:12:32.181955+00:00
-- url     : https://prove2.me/submissions/9ebde329-5952-44f4-834f-2b9405113e45

import Definitions.Def_SidorenkoCertificateBundleA
set_option linter.unusedVariables false
section
variable [p0 : OAI.SidorenkoCounterexample.ProofCertificate_0007]
  [p1 : OAI.SidorenkoCounterexample.ProofCertificate_0014]
  [p2 : OAI.SidorenkoCounterexample.ProofCertificate_0016]
  [p3 : OAI.SidorenkoCounterexample.ProofCertificate_0017]
  [p4 : OAI.SidorenkoCounterexample.ProofCertificate_0020]
  [p5 : OAI.SidorenkoCounterexample.ProofCertificate_0021]
  [p6 : OAI.SidorenkoCounterexample.ProofCertificate_0023]
  [p7 : OAI.SidorenkoCounterexample.ProofCertificate_0030]
  [p8 : OAI.SidorenkoCounterexample.ProofCertificate_0031]
  [p9 : OAI.SidorenkoCounterexample.ProofCertificate_0032]
  [p10 : OAI.SidorenkoCounterexample.ProofCertificate_0035]
  [p11 : OAI.SidorenkoCounterexample.ProofCertificate_0036]
  [p12 : OAI.SidorenkoCounterexample.ProofCertificate_0069]
  [p13 : OAI.SidorenkoCounterexample.ProofCertificate_0082]
  [p14 : OAI.SidorenkoCounterexample.ProofCertificate_0097]
  [p15 : OAI.SidorenkoCounterexample.ProofCertificate_0098]
  [p16 : OAI.SidorenkoCounterexample.ProofCertificate_0100]
  [p17 : OAI.SidorenkoCounterexample.ProofCertificate_0107]
  [p18 : OAI.SidorenkoCounterexample.ProofCertificate_0108]
  [p19 : OAI.SidorenkoCounterexample.ProofCertificate_0111]
  [p20 : OAI.SidorenkoCounterexample.ProofCertificate_0112]
  [p21 : OAI.SidorenkoCounterexample.ProofCertificate_0148]
  [p22 : OAI.SidorenkoCounterexample.ProofCertificate_0153]
  [p23 : OAI.SidorenkoCounterexample.ProofCertificate_0214]
  [p24 : OAI.SidorenkoCounterexample.ProofCertificate_0216]
  [p25 : OAI.SidorenkoCounterexample.ProofCertificate_0296]
  [p26 : OAI.SidorenkoCounterexample.ProofCertificate_0298]
  [p27 : OAI.SidorenkoCounterexample.ProofCertificate_0299]
  [p28 : OAI.SidorenkoCounterexample.ProofCertificate_0302]
  [p29 : OAI.SidorenkoCounterexample.ProofCertificate_0305]
  [p30 : OAI.SidorenkoCounterexample.ProofCertificate_0310]
  [p31 : OAI.SidorenkoCounterexample.ProofCertificate_0311]
  [p32 : OAI.SidorenkoCounterexample.ProofCertificate_0314]
  [p33 : OAI.SidorenkoCounterexample.ProofCertificate_0332]
  [p34 : OAI.SidorenkoCounterexample.ProofCertificate_0352]
  [p35 : OAI.SidorenkoCounterexample.ProofCertificate_0414]
  [p36 : OAI.SidorenkoCounterexample.ProofCertificate_0417]
  [p37 : OAI.SidorenkoCounterexample.ProofCertificate_0420]
  [p38 : OAI.SidorenkoCounterexample.ProofCertificate_0421]
include p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38

namespace OAI
namespace SidorenkoCounterexample
open Module
open scoped BigOperators
section PairDifference
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
variable (A B : Submodule K V)
end PairDifference
section PairBaseCounts
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
variable [Fintype K] [Finite V]
end PairBaseCounts
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
open scoped BigOperators
section PairLiftCounts
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
theorem certificate_proof_0422 (R S : Submodule K (Module.Dual K V))
    (F : SymForm K R.dualCoannihilator) (G : SymForm K S.dualCoannihilator) (h : ℕ)
    (hh : finrank K ↥((dualGraph R F).val ⊓ (dualGraph S G).val) = h) :
    h-finrank K ↥(R ⊓ S) ≤ finrank K (graphDifference _ _ F.val G.val).ker := by
  rw [dualGraph_pair_kernel_exact] at hh
  omega

private instance certificate_instance_0422 : OAI.SidorenkoCounterexample.ProofCertificate_0422 := by
  constructor
  intro c0 c1 c2 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11
  exact @certificate_proof_0422 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11

theorem certificate_proof_0423 {r h : ℕ} (hD : finrank K V=2*r) :
    Function.Injective (canonicalPairCoding (K := K) (V := V) (h := h) hD) := by
  let recover : (Σ p : PairParameters r h, Σ R : SubspacePairProfile (K := K) (V := Module.Dual K V) r p.val.val,
      DualPairLiftEvent R (h-p.val.val)) → Σ R : DualPairBase (K := K) (V := V) r, DualPairForms R :=
    fun T => ⟨T.2.1.val,T.2.2.val⟩
  intro P Q hh
  exact Subtype.ext (congrArg recover hh)

private instance certificate_instance_0423 : OAI.SidorenkoCounterexample.ProofCertificate_0423 := by
  constructor
  intro c0 c1 c2 c3 c4 c5 q0 q1 q2 q3 q4 q5 q6 q7 q8
  exact @certificate_proof_0423 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 q0 q1 q2 q3 q4 q5 q6 q7 q8

variable [Fintype K] [Finite V]
omit [Finite V] in
theorem certificate_proof_0424 {r : ℕ} (R : DualPairBase (K := K) (V := V) r) :
    Nat.card (DualPairForms R) = Fintype.card K ^ (2*((finrank K V-r+1).choose 2)) := by
  have h₁ := coannihilator_finrank R.1.val
  have h₂ := coannihilator_finrank R.2.val
  rw [R.1.property] at h₁
  rw [R.2.property] at h₂
  have hd₁ : finrank K R.1.val.dualCoannihilator=finrank K V-r := by omega
  have hd₂ : finrank K R.2.val.dualCoannihilator=finrank K V-r := by omega
  simp only [DualPairForms,Nat.card_prod,symForm_card,hd₁,hd₂,←pow_add,two_mul]

private instance certificate_instance_0424 : OAI.SidorenkoCounterexample.ProofCertificate_0424 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8
  exact @certificate_proof_0424 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 q0 q1 q2 q3 q4 q5 q6 q7 q8

theorem certificate_proof_0425 (r : ℕ) (hr : r ≤ finrank K V) :
    (Nat.card (CenterStratum (K := K) (V := V) r):ℝ)^2 =
      (Nat.card (DimSubspace K (Module.Dual K V) r):ℝ)^2 *
        (Fintype.card K:ℝ)^(2*((finrank K V-r+1).choose 2)) := by
  rw [vertical_pair_count r hr,Nat.cast_mul,Nat.cast_pow,mul_pow,
    Nat.card_congr (dualDimSubspaceEquiv (K := K) (V := V) r hr),←pow_mul,Nat.mul_comm _ 2]

private instance certificate_instance_0425 : OAI.SidorenkoCounterexample.ProofCertificate_0425 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9
  exact @certificate_proof_0425 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9

theorem certificate_proof_0426 {r p : ℕ} (hD : finrank K V=2*r)
    (R : SubspacePairProfile (K := K) (V := Module.Dual K V) r p) (t : ℕ) (ht : t ≤ p) :
    (Nat.card (DualPairLiftEvent R t):ℝ)/Nat.card (DualPairForms R.val) ≤
      2^t/(Fintype.card K:ℝ)^((t+1).choose 2) := by
  have hd := coannihilator_pair_finrank R.val.1.val R.val.2.val
  rw [R.val.1.property,R.val.2.property,R.property,hD] at hd
  exact pairFormDifference_nullity_bound _ _ t (by omega)

private instance certificate_instance_0426 : OAI.SidorenkoCounterexample.ProofCertificate_0426 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13
  exact @certificate_proof_0426 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13

theorem certificate_proof_0427 (r h : ℕ) (hD : finrank K V=2*r) (p : PairParameters r h) :
    (Nat.card (Σ R : SubspacePairProfile (K := K) (V := Module.Dual K V) r p.val.val,
      DualPairLiftEvent R (h-p.val.val)):ℝ) /
      (Nat.card (CenterStratum (K := K) (V := V) r):ℝ)^2 ≤
        2^(2*r+p.val.val+(h-p.val.val)) /
          (Fintype.card K:ℝ)^(p.val.val*p.val.val+(h-p.val.val+1).choose 2) := by
  classical
  let := Module.finite_of_finite K (M := Module.Dual K V)
  let RType := SubspacePairProfile (K := K) (V := Module.Dual K V) r p.val.val
  let q : ℝ := Fintype.card K
  let f := 2*((finrank K V-r+1).choose 2)
  let b : ℝ := 2^(h-p.val.val)/q^((h-p.val.val+1).choose 2)
  have hq : 0 < q := by dsimp [q]; exact_mod_cast Fintype.card_pos (α := K)
  have hforms (R : RType) : (Nat.card (DualPairLiftEvent R (h-p.val.val)):ℝ) ≤ b*q^f := by
    have hh := dualPairLift_probability_bound hD R (h-p.val.val) p.property.2
    rw [dualPairForms_card,Nat.cast_pow] at hh
    exact (div_le_iff₀ (pow_pos hq _)).mp hh
  have hc := real_card_sigma_le _ hforms
  have hr : r ≤ finrank K V := by omega
  have hg : 0 < (Nat.card (DimSubspace K (Module.Dual K V) r):ℝ) := by
    have hh := subspace_count_lower (K := K) (V := Module.Dual K V) r (by rw [Subspace.dual_finrank_eq]; exact hr)
    exact lt_of_lt_of_le (by positivity) hh
  have hp := subspacePairProfile_probability_bound (K := K) (V := Module.Dual K V) r p.val.val
    (by rwa [Subspace.dual_finrank_eq]) (by omega)
  rw [center_stratum_square r hr]
  calc
    _ ≤ (Nat.card RType:ℝ)*(b*q^f)/((Nat.card (DimSubspace K (Module.Dual K V) r):ℝ)^2*q^f) :=
      div_le_div_of_nonneg_right hc (by positivity)
    _ = ((Nat.card RType:ℝ)/(Nat.card (DimSubspace K (Module.Dual K V) r):ℝ)^2)*b := by
      field_simp
    _ ≤ (2^(2*r+p.val.val)/q^(p.val.val*p.val.val))*b := by
      apply mul_le_mul_of_nonneg_right _ (by dsimp [b]; positivity)
      apply (div_le_div_iff₀ (sq_pos_of_pos hg) (pow_pos hq _)).mpr
      simpa only [mul_comm] using hp
    _ = _ := by dsimp [b]; rw [div_mul_div_comm,←pow_add,←pow_add]

private instance certificate_instance_0427 : OAI.SidorenkoCounterexample.ProofCertificate_0427 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11
  exact @certificate_proof_0427 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11

end PairLiftCounts
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open scoped BigOperators
theorem certificate_proof_0428 (h p : ℕ) (hph : p ≤ h) (htp : h-p ≤ p) :
    ((h+1).choose 2 : ℝ) ≤ p*p+((h-p+1).choose 2 : ℕ)+((h/2+1).choose 2 : ℕ) := by
  rw [triangular_nat,triangular_nat,triangular_nat]
  have he : ((h-p : ℕ):ℝ)=(h:ℝ)-p := Nat.cast_sub hph
  rw [he]
  unfold triangular
  have hh : h=2*(h/2) ∨ h=2*(h/2)+1 := by omega
  have ha : (0:ℝ) ≤ h/2 := by positivity
  rcases hh with hh|hh
  · have hh' : (h:ℝ)=2*(h/2 : ℕ) := by exact_mod_cast hh
    have hpa : h/2 ≤ p := by omega
    by_cases hp : p=h/2
    · have hp' : (p:ℝ)=(h/2 : ℕ) := by exact_mod_cast hp
      nlinarith
    · have hp' : (h/2 : ℕ)+1 ≤ (p:ℝ) := by exact_mod_cast (show h/2+1 ≤ p by omega)
      have hm := mul_nonneg (sub_nonneg.mpr (show ((h/2 : ℕ):ℝ) ≤ p by linarith))
        (sub_nonneg.mpr (show (1:ℝ) ≤ p-(h/2 : ℕ) by linarith))
      have hm' := mul_nonneg (show (0:ℝ) ≤ (h/2 : ℕ) by positivity)
        (sub_nonneg.mpr (show ((h/2 : ℕ):ℝ) ≤ p by linarith))
      nlinarith
  · have hh' : (h:ℝ)=2*(h/2 : ℕ)+1 := by exact_mod_cast hh
    have hp' : (h/2 : ℕ)+1 ≤ (p:ℝ) := by exact_mod_cast (show h/2+1 ≤ p by omega)
    have hm := mul_nonneg (show (0:ℝ) ≤ (h/2 : ℕ) by positivity)
      (sub_nonneg.mpr (show (h/2 : ℕ)+1 ≤ (p:ℝ) from hp'))
    nlinarith [sq_nonneg ((p:ℝ)-(h/2 : ℕ)-1)]

private instance certificate_instance_0428 : OAI.SidorenkoCounterexample.ProofCertificate_0428 := by
  constructor
  intro q0 q1 q2 q3
  exact @certificate_proof_0428 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 q0 q1 q2 q3

section PairFinal
open Module
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] [Fintype K] [Finite V]
theorem certificate_proof_0429 (r h : ℕ) (hD : finrank K V=2*r) :
    (Nat.card (CenterPairProfile (K := K) (V := V) r h):ℝ) /
      (Nat.card (CenterStratum (K := K) (V := V) r):ℝ)^2 ≤
    ∑ p : PairParameters r h, 2^(2*r+p.val.val+(h-p.val.val)) /
      (Fintype.card K:ℝ)^(p.val.val*p.val.val+(h-p.val.val+1).choose 2) := by
  classical
  let := Module.finite_of_finite K (M := Module.Dual K V)
  have hr : r ≤ finrank K V := by omega
  rw [←Nat.card_congr (canonicalPairProfileEquiv r h hr)]
  have hc := Nat.card_le_card_of_injective _ (canonicalPairCoding_injective (K := K) (V := V) (h := h) hD)
  have hh : (Nat.card (CanonicalPairProfile (K := K) (V := V) r h):ℝ) ≤
      Nat.card (Σ p : PairParameters r h, Σ R : SubspacePairProfile (K := K) (V := Module.Dual K V) r p.val.val,
        DualPairLiftEvent R (h-p.val.val)) := by exact_mod_cast hc
  refine (div_le_div_of_nonneg_right hh (by positivity)).trans ?_
  rw [Nat.card_sigma,Nat.cast_sum,Finset.sum_div]
  exact Finset.sum_le_sum (fun p _ => pairPlanted_bound_one r h hD p)

private instance certificate_instance_0429 : OAI.SidorenkoCounterexample.ProofCertificate_0429 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9
  exact @certificate_proof_0429 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9

theorem certificate_proof_0430 (r h : ℕ) (hD : finrank K V=2*r) :
    (Fintype.card K:ℝ)^((h+1).choose 2) *
      ((Nat.card (CenterPairProfile (K := K) (V := V) r h):ℝ) /
        (Nat.card (CenterStratum (K := K) (V := V) r):ℝ)^2) ≤
      (Nat.card (PairParameters r h):ℝ)*2^(2*r+h)*(Fintype.card K:ℝ)^((h/2+1).choose 2) := by
  have hq : (1:ℝ) ≤ Fintype.card K := by exact_mod_cast Fintype.card_pos (α := K)
  have hqpos : (0:ℝ) < Fintype.card K := by positivity
  have hh := canonical_center_pair_probability_bound (K := K) (V := V) r h hD
  refine (mul_le_mul_of_nonneg_left hh (by positivity)).trans ?_
  rw [Finset.mul_sum]
  calc
    _ ≤ ∑ _p : PairParameters r h, 2^(2*r+h)*(Fintype.card K:ℝ)^((h/2+1).choose 2) := by
      apply Finset.sum_le_sum
      intro p _
      have hs : p.val.val+(h-p.val.val)=h := Nat.add_sub_of_le p.property.1
      have hg : (h+1).choose 2 ≤ p.val.val*p.val.val+(h-p.val.val+1).choose 2+(h/2+1).choose 2 := by
        have hb := two_active_gain_bound h p.val.val p.property.1 p.property.2
        exact_mod_cast hb
      rw [show 2*r+p.val.val+(h-p.val.val)=2*r+h by omega]
      rw [←mul_div_assoc]
      apply (div_le_iff₀ (pow_pos hqpos _)).mpr
      calc
        _ ≤ 2^(2*r+h)*(Fintype.card K:ℝ)^(p.val.val*p.val.val+(h-p.val.val+1).choose 2+(h/2+1).choose 2) := by
          rw [mul_comm]; exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hq hg) (by positivity)
        _ = _ := by rw [pow_add]; ring
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,Nat.card_eq_fintype_card]; ring

private instance certificate_instance_0430 : OAI.SidorenkoCounterexample.ProofCertificate_0430 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9
  exact @certificate_proof_0430 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9

end PairFinal
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
open scoped BigOperators
section SymplecticPairPlanted
variable {K E : Type} [Field K] [AddCommGroup E] [Module K E]
variable (ω : LinearMap.BilinForm K E)
variable [Fintype K] [Finite E]
omit [Fintype K] in
theorem certificate_proof_0431 (h2 : (2:K) ≠ 0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
    (r : ℕ) (L M : SymplecticLagrangian ω) :
    Nat.card (Σ Y : SymplecticLagrangian ω,
      SymplecticCenterPairProfile ω Y r (finrank K ↥(L.val ⊓ M.val))) =
    Nat.card (OrderedPairDim ω (finrank K ↥(L.val ⊓ M.val))) * Nat.card (PairCenterSet ω r L.val M.val) := by
  classical
  let := Fintype.ofFinite (OrderedPairDim ω (finrank K ↥(L.val ⊓ M.val)))
  rw [←Nat.card_congr (pairCenterProfileEquiv ω r (finrank K ↥(L.val ⊓ M.val))),Nat.card_sigma]
  have hc (p : OrderedPairDim ω (finrank K ↥(L.val ⊓ M.val))) :
      Nat.card (PairCenterSet ω r p.val.1.val p.val.2.val)=Nat.card (PairCenterSet ω r L.val M.val) := by
    obtain ⟨e,he,hL,hM⟩ := ordered_pair_transitivity ω h2 ha hω
      p.val.1.val p.val.2.val L.val M.val p.val.1.property p.val.2.property L.property M.property p.property
    have hh := Nat.card_congr (pairCenterIsometryEquiv ω r p.val.1.val p.val.2.val e he)
    rwa [hL,hM] at hh
  simp only [hc,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Nat.card_eq_fintype_card,Nat.cast_id]

private instance certificate_instance_0431 : OAI.SidorenkoCounterexample.ProofCertificate_0431 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12
  exact @certificate_proof_0431 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12

omit [Fintype K] in
theorem certificate_proof_0432 (h2 : (2:K) ≠ 0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
    (A B : SymplecticLagrangian ω) (r : ℕ) :
    Nat.card (SymplecticCenterStratum ω A r)=Nat.card (SymplecticCenterStratum ω B r) := by
  obtain ⟨e,he,hA⟩ := lagrangian_transitivity ω A.val h2 ha hω A.property B.val B.property
  exact Nat.card_congr ((lagrangianIsometryEquiv ω e he).subtypeEquiv (by
    intro L
    change _ ↔ finrank K ↥(L.val.map e.toLinearMap ⊓ B.val)=r
    rw [←hA,map_pair_finrank]))

private instance certificate_instance_0432 : OAI.SidorenkoCounterexample.ProofCertificate_0432 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12
  exact @certificate_proof_0432 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12

theorem certificate_proof_0433 (h2 : (2:K) ≠ 0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
    (r : ℕ) (hD : finrank K E=2*(2*r)) (Y : SymplecticLagrangian ω) (h : ℕ) :
    (Fintype.card K:ℝ)^((h+1).choose 2)*
      ((Nat.card (SymplecticCenterPairProfile ω Y r h):ℝ)/
        (Nat.card (SymplecticCenterStratum ω Y r):ℝ)^2) ≤
      (Nat.card (PairParameters r h):ℝ)*2^(2*r+h)*(Fintype.card K:ℝ)^((h/2+1).choose 2) := by
  obtain ⟨e,he,hY⟩ := exists_center_coordinates ω h2 ha hω Y
  rw [←Nat.card_congr (symplecticCenterPairProfileEquiv ω Y e he hY r h),
    ←Nat.card_congr (symplecticCenterStratumEquiv ω Y e he hY r)]
  have hd := self_orthogonal_twice_finrank ω Y.val hω Y.property
  exact canonical_center_pair_gain_bound r h (by omega)

private instance certificate_instance_0433 : OAI.SidorenkoCounterexample.ProofCertificate_0433 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14
  exact @certificate_proof_0433 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14

omit [Fintype K] [Finite E] in
theorem certificate_proof_0434 (r : ℕ) (A L M : SymplecticLagrangian ω) :
    0 ≤ pairFaceDensity ω r A L M := by unfold pairFaceDensity; positivity

private instance certificate_instance_0434 : OAI.SidorenkoCounterexample.ProofCertificate_0434 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9
  exact @certificate_proof_0434 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9

end SymplecticPairPlanted
theorem certificate_proof_0435 (L A O Z T C B : ℝ) (hL : 0<L) (hA : 0<A) (hZ : 0≤Z)
    (hC : 0≤C) (hMass : L^2≤C*(T*O)) (hGain : T*O*Z≤L*A^2*B) :
    Z*L/A^2≤C*B := by
  apply (div_le_iff₀ (sq_pos_of_pos hA)).mpr
  apply (mul_le_mul_iff_right₀ hL).mp
  calc
    L*(Z*L) = Z*L^2 := by ring
    _ ≤ Z*(C*(T*O)) := mul_le_mul_of_nonneg_left hMass hZ
    _ = C*(T*O*Z) := by ring
    _ ≤ C*(L*A^2*B) := mul_le_mul_of_nonneg_left hGain hC
    _ = L*(C*B*A^2) := by ring

private instance certificate_instance_0435 : OAI.SidorenkoCounterexample.ProofCertificate_0435 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12
  exact @certificate_proof_0435 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12

section PairPointwise
variable {K E : Type} [Field K] [AddCommGroup E] [Module K E] [Fintype K] [Finite E]
variable (ω : LinearMap.BilinForm K E)
theorem certificate_proof_0436 (h2 : (2:K) ≠ 0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
    (r : ℕ) (hD : 2*(2*r)=finrank K E) (A L M : SymplecticLagrangian ω) :
    pairFaceDensity ω r A L M ≤
      (lagrangianConstant (2*r))^2 *
        ((Nat.card (PairParameters r (finrank K ↥(L.val ⊓ M.val))):ℝ)*
          2^(2*r+finrank K ↥(L.val ⊓ M.val))*
          (Fintype.card K:ℝ)^((finrank K ↥(L.val ⊓ M.val)/2+1).choose 2)) := by
  classical
  let := Fintype.ofFinite (SymplecticLagrangian ω)
  let h := finrank K ↥(L.val ⊓ M.val)
  let q : ℝ := Fintype.card K
  let a : ℝ := Nat.card (SymplecticCenterStratum ω A r)
  let b : ℝ := (Nat.card (PairParameters r h):ℝ)*2^(2*r+h)*q^((h/2+1).choose 2)
  have hdim := self_orthogonal_twice_finrank ω L.val hω L.property
  have hh : h≤2*r := by have hb := Submodule.finrank_mono (show L.val ⊓ M.val ≤ L.val from inf_le_left); dsimp [h]; omega
  have ha0 : 0<a := symplectic_center_stratum_card_pos ω h2 ha hω (2*r) hD A r (by omega)
  have hq : 0<q := by dsimp [q]; exact_mod_cast Fintype.card_pos (α := K)
  have hLag := symplecticLagrangian_card_bounds ω h2 ha hω (2*r) hD
  have hL : (0:ℝ)<Nat.card (SymplecticLagrangian ω) := (pow_pos hq _).trans_le hLag.1
  have hMass : (Nat.card (SymplecticLagrangian ω):ℝ)^2 ≤
      (lagrangianConstant (2*r))^2*(q^((h+1).choose 2)*Nat.card (OrderedPairDim ω h)) := by
    calc
      _ ≤ (lagrangianConstant (2*r)*q^((2*r+1).choose 2))^2 := pow_le_pow_left₀ (by positivity) hLag.2 2
      _ = (lagrangianConstant (2*r))^2*q^(2*((2*r+1).choose 2)) := by rw [mul_pow,←pow_mul,Nat.mul_comm _ 2]
      _ ≤ _ := mul_le_mul_of_nonneg_left (orderedPairDim_card_lower ω h2 ha hω (2*r) hD h hh) (by positivity)
  have hg (Y : SymplecticLagrangian ω) :
      q^((h+1).choose 2)*(Nat.card (SymplecticCenterPairProfile ω Y r h):ℝ) ≤ a^2*b := by
    have hc := symplectic_center_pair_gain_bound ω h2 ha hω r hD.symm Y h
    rw [←symplectic_center_stratum_card_eq ω h2 ha hω A Y r,←mul_div_assoc] at hc
    exact (div_le_iff₀ (sq_pos_of_pos ha0)).mp hc |>.trans_eq (mul_comm _ _)
  have hGain : q^((h+1).choose 2)*(Nat.card (OrderedPairDim ω h):ℝ)*Nat.card (PairCenterSet ω r L.val M.val) ≤
      (Nat.card (SymplecticLagrangian ω):ℝ)*a^2*b := by
    rw [mul_assoc,←Nat.cast_mul,←pairCenter_profile_card ω h2 ha hω r L M,Nat.card_sigma,Nat.cast_sum,Finset.mul_sum]
    calc
      _ ≤ ∑ _Y : SymplecticLagrangian ω, a^2*b := Finset.sum_le_sum (fun Y _ => hg Y)
      _ = _ := by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Nat.card_eq_fintype_card]; ring
  exact normalized_pair_gain _ _ _ _ _ _ _ hL ha0 (by positivity) (by positivity) hMass hGain

private instance certificate_instance_0436 : OAI.SidorenkoCounterexample.ProofCertificate_0436 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15
  exact @certificate_proof_0436 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15

end PairPointwise
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
section ActualProfile
variable {K E : Type} [Field K] [AddCommGroup E] [Module K E] [Fintype K] [Finite E]
variable (ω : LinearMap.BilinForm K E)
theorem certificate_proof_0437 (ha : ω.IsAlt) (hω : ω.Nondegenerate)
    (D c u v w : ℕ) (hD : 2*D=finrank K E) (p : TripleDimProfile ω c u v w) :
    (u-c)+(v-c)+(w-c) ≤ D-c := by
  let S := tripleProfileCommon ω p
  obtain ⟨L,M,N,hzero,hu,hv,hw,_⟩ := fixedCommonProfile_injection ω ha S ⟨p,rfl⟩
  let : Finite (ReducedSpace ω S.val) := Module.finite_of_finite K
  have hc : c≤D := S.property.2 ▸ isotropic_finrank_le_half ω hω D hD S.val S.property.1
  have hd : 2*(D-c)=finrank K (ReducedSpace ω S.val) := by
    have hh := reducedSpace_finrank ω S.val hω S.property.1
    rw [S.property.2,←hD] at hh
    omega
  simpa only [hu,hv,hw] using symplectic_profile_pair_sum_le
    (symplecticReductionForm ω S.val ha) (symplecticReductionForm_nondegenerate ω S.val ha hω) (D-c) hd L M N hzero

private instance certificate_instance_0437 : OAI.SidorenkoCounterexample.ProofCertificate_0437 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16
  exact @certificate_proof_0437 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16

end ActualProfile
end SidorenkoCounterexample
end OAI
namespace OAI
namespace SidorenkoCounterexample
open scoped BigOperators
section Sequential
variable {A : Type} [Finite A]
theorem certificate_proof_0438 (k : ℕ) (R : (Fin k → A) → Prop)
    (P : (n : ℕ) → (Fin (k+n) → A) → A → Prop) (B : ℕ → ℝ)
    (hB : ∀ n, 0≤B n) (hb : ∀ n (x : ValidSeq k R P n), (Nat.card {a : A // P n x.val a}:ℝ) ≤ B n)
    (n : ℕ) : (Nat.card (ValidSeq k R P n):ℝ) ≤
      Nat.card {x : Fin k → A // R x} * ∏ i : Fin n, B i.val := by
  classical
  induction n with
  | zero => simp only [Fin.prod_univ_zero,mul_one]; exact le_rfl
  | succ n ih =>
    let := Fintype.ofFinite (ValidSeq k R P n)
    rw [Nat.card_congr (validSeqSuccEquiv k R P n),Nat.card_sigma,Nat.cast_sum]
    calc
      _ ≤ ∑ _x : ValidSeq k R P n, B n := Finset.sum_le_sum (fun x _ => hb n x)
      _ = (Nat.card (ValidSeq k R P n):ℝ)*B n := by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Nat.card_eq_fintype_card]
      _ ≤ (Nat.card {x : Fin k → A // R x} * ∏ i : Fin n, B i.val)*B n := mul_le_mul_of_nonneg_right ih (hB n)
      _ = _ := by rw [Fin.prod_univ_castSucc]; simp only [Fin.val_castSucc,Fin.val_last]; ring

private instance certificate_instance_0438 : OAI.SidorenkoCounterexample.ProofCertificate_0438 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8
  exact @certificate_proof_0438 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 q0 q1 q2 q3 q4 q5 q6 q7 q8

end Sequential
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open scoped BigOperators
theorem certificate_proof_0439 : ∀ j, faces j={faceVertex j 0,faceVertex j 1,faceVertex j 2} := by decide

private instance certificate_instance_0439 : OAI.SidorenkoCounterexample.ProofCertificate_0439 := by
  constructor
  intro q0
  exact @certificate_proof_0439 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 q0

theorem certificate_proof_0440 : ∀ c, Function.Bijective (classPoint c) := by decide

private instance certificate_instance_0440 : OAI.SidorenkoCounterexample.ProofCertificate_0440 := by
  constructor
  intro q0
  exact @certificate_proof_0440 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 q0

theorem certificate_proof_0441 : ∀ c, Function.Injective (classFace c) := by decide

private instance certificate_instance_0441 : OAI.SidorenkoCounterexample.ProofCertificate_0441 := by
  constructor
  intro q0
  exact @certificate_proof_0441 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 q0

theorem certificate_proof_0442 : ∀ c n, (classOldZero c n).val<3+n.val := by decide

private instance certificate_instance_0442 : OAI.SidorenkoCounterexample.ProofCertificate_0442 := by
  constructor
  intro q0 q1
  exact @certificate_proof_0442 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 q0 q1

theorem certificate_proof_0443 : ∀ c n, (classOldOne c n).val<3+n.val := by decide

private instance certificate_instance_0443 : OAI.SidorenkoCounterexample.ProofCertificate_0443 := by
  constructor
  intro q0 q1
  exact @certificate_proof_0443 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 q0 q1

theorem certificate_proof_0444 : ∀ c, faces (classFace c 0)={classPoint c 0,classPoint c 1,classPoint c 2} := by decide

private instance certificate_instance_0444 : OAI.SidorenkoCounterexample.ProofCertificate_0444 := by
  constructor
  intro q0
  exact @certificate_proof_0444 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 q0

theorem certificate_proof_0445 : ∀ c n, faces (classFace c n.succ)=
    {classPoint c (classOldZero c n),classPoint c (classOldOne c n),classPoint c ⟨3+n.val,by omega⟩} := by decide

private instance certificate_instance_0445 : OAI.SidorenkoCounterexample.ProofCertificate_0445 := by
  constructor
  intro q0 q1
  exact @certificate_proof_0445 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 q0 q1

theorem certificate_proof_0446 : ∀ c n, pairVertices (classOldPair c n)=
    {classPoint c (classOldZero c n),classPoint c (classOldOne c n)} := by decide

private instance certificate_instance_0446 : OAI.SidorenkoCounterexample.ProofCertificate_0446 := by
  constructor
  intro q0 q1
  exact @certificate_proof_0446 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 q0 q1

theorem certificate_proof_0447 : ∀ c n, pairVertices (classNewPairZero c n)=
    {classPoint c (classOldZero c n),classPoint c ⟨3+n.val,by omega⟩} := by decide

private instance certificate_instance_0447 : OAI.SidorenkoCounterexample.ProofCertificate_0447 := by
  constructor
  intro q0 q1
  exact @certificate_proof_0447 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 q0 q1

theorem certificate_proof_0448 : ∀ c n, pairVertices (classNewPairOne c n)=
    {classPoint c (classOldOne c n),classPoint c ⟨3+n.val,by omega⟩} := by decide

private instance certificate_instance_0448 : OAI.SidorenkoCounterexample.ProofCertificate_0448 := by
  constructor
  intro q0 q1
  exact @certificate_proof_0448 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 q0 q1

theorem certificate_proof_0449 : ∀ c n, (classParent c n).val<n.val+1 := by decide

private instance certificate_instance_0449 : OAI.SidorenkoCounterexample.ProofCertificate_0449 := by
  constructor
  intro q0 q1
  exact @certificate_proof_0449 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 q0 q1

theorem certificate_proof_0450 : ∀ c n, pairVertices (classOldPair c n) ⊆ faces (classFace c (classParent c n)) := by decide

private instance certificate_instance_0450 : OAI.SidorenkoCounterexample.ProofCertificate_0450 := by
  constructor
  intro q0 q1
  exact @certificate_proof_0450 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 q0 q1

theorem certificate_proof_0451 : ∀ c, Function.Injective (classOldPair c) := by decide
 

private instance certificate_instance_0451 : OAI.SidorenkoCounterexample.ProofCertificate_0451 := by
  constructor
  intro q0
  exact @certificate_proof_0451 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 q0

theorem certificate_proof_0452 : ∀ j, (Finset.univ.filter fun cn : Fin 6 × Fin 11 => classFace cn.1 cn.2=j).card=3 := by decide

private instance certificate_instance_0452 : OAI.SidorenkoCounterexample.ProofCertificate_0452 := by
  constructor
  intro q0
  exact @certificate_proof_0452 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 q0

theorem certificate_proof_0453 : ∀ e, (Finset.univ.filter fun c => classInternal c e).card=3-separationCount e := by decide

private instance certificate_instance_0453 : OAI.SidorenkoCounterexample.ProofCertificate_0453 := by
  constructor
  intro q0
  exact @certificate_proof_0453 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 q0

theorem certificate_proof_0454 : ∀ c n, classInternal c (classOldPair c n) := by decide

private instance certificate_instance_0454 : OAI.SidorenkoCounterexample.ProofCertificate_0454 := by
  constructor
  intro q0 q1
  exact @certificate_proof_0454 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 q0 q1

theorem certificate_proof_0455 : ∀ c n, Finset.image (facePair (classFace c n.succ)) Finset.univ =
    {classOldPair c n,classNewPairZero c n,classNewPairOne c n} := by decide

private instance certificate_instance_0455 : OAI.SidorenkoCounterexample.ProofCertificate_0455 := by
  constructor
  intro q0 q1
  exact @certificate_proof_0455 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 q0 q1

theorem certificate_proof_0456 : ∀ c n, classOldPair c n≠classNewPairZero c n ∧
    classOldPair c n≠classNewPairOne c n ∧ classNewPairZero c n≠classNewPairOne c n := by decide

private instance certificate_instance_0456 : OAI.SidorenkoCounterexample.ProofCertificate_0456 := by
  constructor
  intro q0 q1
  exact @certificate_proof_0456 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 q0 q1

theorem certificate_proof_0457 : ∀ j, Function.Injective (faceVertex j) := by decide

private instance certificate_instance_0457 : OAI.SidorenkoCounterexample.ProofCertificate_0457 := by
  constructor
  intro q0
  exact @certificate_proof_0457 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 q0

theorem certificate_proof_0458 : ∀ j k, pairVertices (facePair j k)=
    (![ {faceVertex j 0,faceVertex j 1}, {faceVertex j 0,faceVertex j 2}, {faceVertex j 1,faceVertex j 2}] : Fin 3 → Finset (Fin 13)) k := by decide

private instance certificate_instance_0458 : OAI.SidorenkoCounterexample.ProofCertificate_0458 := by
  constructor
  intro q0 q1
  exact @certificate_proof_0458 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 q0 q1

theorem certificate_proof_0459 : ∀ c, pairVertices (facePair (classFace c 0) 0)={classPoint c 0,classPoint c 1} := by decide

private instance certificate_instance_0459 : OAI.SidorenkoCounterexample.ProofCertificate_0459 := by
  constructor
  intro q0
  exact @certificate_proof_0459 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 q0

theorem certificate_proof_0460 : ∀ c, pairVertices (facePair (classFace c 0) 1)={classPoint c 0,classPoint c 2} := by decide

private instance certificate_instance_0460 : OAI.SidorenkoCounterexample.ProofCertificate_0460 := by
  constructor
  intro q0
  exact @certificate_proof_0460 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 q0

theorem certificate_proof_0461 : ∀ c, pairVertices (facePair (classFace c 0) 2)={classPoint c 1,classPoint c 2} := by decide

private instance certificate_instance_0461 : OAI.SidorenkoCounterexample.ProofCertificate_0461 := by
  constructor
  intro q0
  exact @certificate_proof_0461 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 q0

theorem certificate_proof_0462 : ∀ e, (Finset.univ.filter fun cn : Fin 6 × Fin 10 => classOldPair cn.1 cn.2=e).card=3-separationCount e := by decide

private instance certificate_instance_0462 : OAI.SidorenkoCounterexample.ProofCertificate_0462 := by
  constructor
  intro q0
  exact @certificate_proof_0462 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 q0

end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
theorem certificate_proof_0463 (q C L N : ℝ) (a : ℕ) (hq : 0<q)
    (h : q^a*N≤C*L) : N≤C*L*q^(-(a:ℝ)) := by
  rw [Real.rpow_neg hq.le,Real.rpow_natCast,←div_eq_mul_inv]
  apply (le_div_iff₀ (pow_pos hq a)).mpr
  simpa only [mul_comm] using h

private instance certificate_instance_0463 : OAI.SidorenkoCounterexample.ProofCertificate_0463 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6
  exact @certificate_proof_0463 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 q0 q1 q2 q3 q4 q5 q6

section RawProfile
variable {K E : Type} [Field K] [AddCommGroup E] [Module K E] [Fintype K] [Finite E]
variable (ω : LinearMap.BilinForm K E)
theorem certificate_proof_0464 (h2 : (2:K)≠0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
    (D : ℕ) (hD : 2*D=finrank K E) (c u v w : ℕ) (hc : c≤D) :
    (Nat.card (TripleDimProfile ω c u v w):ℝ) ≤ fullProfileConstant D *
      (Nat.card (SymplecticLagrangian ω):ℝ)^3 * (Fintype.card K:ℝ)^(-(naturalProfileCost D c u v w:ℝ)) := by
  have hq : 0<(Fintype.card K:ℝ) := by exact_mod_cast Fintype.card_pos (α:=K)
  have hb := (symplecticLagrangian_card_bounds ω h2 ha hω D hD).1
  apply inverse_power_inequality _ _ _ _ _ hq
  calc
    _ ≤ fullProfileConstant D*(Fintype.card K:ℝ)^(3*(D+1).choose 2) :=
      tripleProfile_card_upper ω h2 ha hω D hD c u v w hc
    _ ≤ _ := by
      gcongr
      · exact (fullProfileConstant_pos D).le
      · rw [mul_comm 3, pow_mul]
        exact pow_le_pow_left₀ (by positivity) hb 3

private instance certificate_instance_0464 : OAI.SidorenkoCounterexample.ProofCertificate_0464 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17
  exact @certificate_proof_0464 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17

theorem certificate_proof_0465 (h2 : (2:K)≠0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
    (D : ℕ) (hD : 2*D=finrank K E) (L M : SymplecticLagrangian ω) (c v w : ℕ) (hc : c≤D) :
    (Nat.card (PairCompletion ω L M c v w):ℝ) ≤ fullProfileConstant D *
      (Nat.card (SymplecticLagrangian ω):ℝ) * (Fintype.card K:ℝ)^
        (((finrank K ↥(L.val ⊓ M.val)+1).choose 2:ℝ)-(naturalProfileCost D c (finrank K ↥(L.val ⊓ M.val)) v w:ℝ)) := by
  have hq : 0<(Fintype.card K:ℝ) := by exact_mod_cast Fintype.card_pos (α:=K)
  have hb := (symplecticLagrangian_card_bounds ω h2 ha hω D hD).1
  have hh := conditionalProfile_card_upper ω h2 ha hω D hD L M c v w hc
  have hh' : (Fintype.card K:ℝ)^(naturalProfileCost D c (finrank K ↥(L.val ⊓ M.val)) v w)*
      (Nat.card (PairCompletion ω L M c v w):ℝ) ≤ fullProfileConstant D*
        ((Nat.card (SymplecticLagrangian ω):ℝ)*(Fintype.card K:ℝ)^((finrank K ↥(L.val ⊓ M.val)+1).choose 2)) := by
    change (Fintype.card K:ℝ)^(naturalProfileCost D c (finrank K ↥(L.val ⊓ M.val)) v w)*
      (Nat.card (PairCompletion ω L M c v w):ℝ) ≤ _ at hh
    refine hh.trans ?_
    rw [pow_add]
    calc
      _ ≤ fullProfileConstant D*((Fintype.card K:ℝ)^((finrank K ↥(L.val ⊓ M.val)+1).choose 2)*
        (Nat.card (SymplecticLagrangian ω):ℝ)) := by gcongr; exact (fullProfileConstant_pos D).le
      _ = _ := by ring
  have hh'' := inverse_power_inequality _ _ _ _ _ hq hh'
  convert hh'' using 1
  rw [Real.rpow_sub hq,Real.rpow_natCast,Real.rpow_natCast]
  rw [Real.rpow_neg hq.le,Real.rpow_natCast]
  ring

private instance certificate_instance_0465 : OAI.SidorenkoCounterexample.ProofCertificate_0465 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18
  exact @certificate_proof_0465 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18

end RawProfile
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
open scoped BigOperators
section ExposureProfile
variable {K E : Type} [Field K] [AddCommGroup E] [Module K E]
variable (ω : LinearMap.BilinForm K E)
variable [Fintype K] [Finite E]
end ExposureProfile
section GlobalExposure
variable {K E : Type} [Field K] [AddCommGroup E] [Module K E] [Fintype K] [Finite E]
variable (ω : LinearMap.BilinForm K E)
end GlobalExposure
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open scoped BigOperators
section ZeroSequential
variable {A : Type} [Finite A]
end ZeroSequential
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
open scoped BigOperators
section OrthogonalTuple
variable {K E : Type} [Field K] [AddCommGroup E] [Module K E]
variable (ω : LinearMap.BilinForm K E)
variable [Fintype K] [Finite E]
end OrthogonalTuple
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
open scoped BigOperators
section TupleRpow
variable {K E : Type} [Field K] [AddCommGroup E] [Module K E] [Fintype K] [Finite E]
variable (ω : LinearMap.BilinForm K E)
end TupleRpow
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
open scoped BigOperators
section AbstractTuple
variable {K E A : Type} [Field K] [AddCommGroup E] [Module K E] [Fintype K] [Finite E] [Fintype A]
variable (ω : LinearMap.BilinForm K E)
end AbstractTuple
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
open scoped BigOperators
section ResidualCount
variable {K E : Type} [Field K] [AddCommGroup E] [Module K E] [Fintype K] [Finite E]
variable (ω : LinearMap.BilinForm K E)
end ResidualCount
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
open scoped BigOperators
section FamilySpan
variable {K E I : Type} [Field K] [AddCommGroup E] [Module K E] [Fintype I]
variable [Finite E]
variable [Fintype K]
end FamilySpan
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
open scoped BigOperators
section DirectFamilies
variable {K E I : Type} [Field K] [AddCommGroup E] [Module K E] [Fintype I]
variable [Finite E]
variable (ω : LinearMap.BilinForm K E)
variable [Fintype K]
end DirectFamilies
end SidorenkoCounterexample
end OAI

theorem solution : OAI.SidorenkoCounterexample.ProofCertificate_0422 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0423 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0424 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0425 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0426 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0427 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0428 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0429 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0430 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0431 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0432 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0433 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0434 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0435 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0436 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0437 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0438 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0439 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0440 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0441 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0442 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0443 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0444 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0445 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0446 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0447 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0448 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0449 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0450 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0451 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0452 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0453 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0454 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0455 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0456 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0457 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0458 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0459 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0460 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0461 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0462 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0463 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0464 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0465 := by
  exact ⟨inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance⟩
end

