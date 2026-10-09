-- Prove2me | solution 1 for OAI.SidorenkoCounterexample.finite_geometry_batch_04
-- status  : ACCEPTED   (prove)
-- author  : @abcdefg
-- created : 2026-10-09T05:27:36.916862+00:00
-- url     : https://prove2.me/submissions/4e308193-2548-485a-b3b2-70f140b6467e

import Definitions.Def_SidorenkoFiniteGeometryCertificates04
set_option linter.unusedVariables false
section
variable [p0 : OAI.SidorenkoCounterexample.ProofCertificate_0014]
  [p1 : OAI.SidorenkoCounterexample.ProofCertificate_0016]
  [p2 : OAI.SidorenkoCounterexample.ProofCertificate_0017]
  [p3 : OAI.SidorenkoCounterexample.ProofCertificate_0020]
  [p4 : OAI.SidorenkoCounterexample.ProofCertificate_0021]
  [p5 : OAI.SidorenkoCounterexample.ProofCertificate_0023]
  [p6 : OAI.SidorenkoCounterexample.ProofCertificate_0035]
  [p7 : OAI.SidorenkoCounterexample.ProofCertificate_0081]
  [p8 : OAI.SidorenkoCounterexample.ProofCertificate_0082]
  [p9 : OAI.SidorenkoCounterexample.ProofCertificate_0083]
  [p10 : OAI.SidorenkoCounterexample.ProofCertificate_0086]
  [p11 : OAI.SidorenkoCounterexample.ProofCertificate_0092]
  [p12 : OAI.SidorenkoCounterexample.ProofCertificate_0094]
  [p13 : OAI.SidorenkoCounterexample.ProofCertificate_0097]
  [p14 : OAI.SidorenkoCounterexample.ProofCertificate_0098]
  [p15 : OAI.SidorenkoCounterexample.ProofCertificate_0099]
include p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15

namespace OAI
namespace SidorenkoCounterexample
open Module
open scoped BigOperators
section Bounds
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] [Fintype K] [Finite V]
end Bounds
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
section ContainingSubspaces
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
variable [Fintype K] [Finite V]
end ContainingSubspaces
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
open scoped BigOperators
section TripleSubspaces
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
variable [FiniteDimensional K V]
variable [Fintype K]
end TripleSubspaces
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
open scoped BigOperators
section SpanCount
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
variable [Fintype K]
end SpanCount
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
section PlantedSubspaceExponent
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Fintype K]
end PlantedSubspaceExponent
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
section DualPlantedBases
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
end DualPlantedBases
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
section NullityAll
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] [Fintype K] [Finite V]
end NullityAll
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
section NullityAllLift
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] [Fintype K] [Finite V]
variable (A₀ A₁ A₂ : Submodule K V)
end NullityAllLift
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
section DualProfileLift
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
variable {r p₀ p₁ p₂ n : ℕ}
end DualProfileLift
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
section ProfileConstraints
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
end ProfileConstraints
section DualLiftSum
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  [Fintype K] [Finite V]
end DualLiftSum
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
section CanonicalCoding
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
end CanonicalCoding
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
section ExtraFeasibility
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
theorem certificate_proof_0100 {r s : ℕ} (R S : DimSubspace K (Module.Dual K V) r)
    (F : SymForm K R.val.dualCoannihilator) (G : SymForm K S.val.dualCoannihilator)
    (hs : finrank K ↥((dualGraph R.val F).val ⊓ (dualGraph S.val G).val) = s) :
    (s-finrank K ↥(R.val ⊓ S.val))+2*r ≤ finrank K V+finrank K ↥(R.val ⊓ S.val) := by
  have h₁ := dualGraph_pair_finrank_ge R.val S.val F G
  have h₂ := dualGraph_pair_finrank_le R.val S.val F G
  have h₃ := coannihilator_pair_finrank R.val S.val
  rw [hs] at h₁ h₂
  rw [R.property,S.property] at h₃
  omega

private instance certificate_instance_0100 : OAI.SidorenkoCounterexample.ProofCertificate_0100 := by
  constructor
  intro c0 c1 c2 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12
  exact @certificate_proof_0100 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12

theorem certificate_proof_0101 {r p₀ p₁ p₂ n : ℕ}
    (R : SubspaceTripleSpanProfile (K := K) (V := Module.Dual K V) r p₀ p₁ p₂ n) :
    (finrank K V-n)+2*r ≤ finrank K V+p₀ ∧
    (finrank K V-n)+2*r ≤ finrank K V+p₁ ∧
    (finrank K V-n)+2*r ≤ finrank K V+p₂ := by
  let A := R.val.val.1.val
  let B := R.val.val.2.1.val
  let C := R.val.val.2.2.val
  have hdA : finrank K A = r := R.val.val.1.property
  have hdB : finrank K B = r := R.val.val.2.1.property
  have hdC : finrank K C = r := R.val.val.2.2.property
  have hp₀ : finrank K ↥(A ⊓ B) = p₀ := R.val.property.2.1
  have hp₁ : finrank K ↥(A ⊓ C) = p₁ := R.val.property.2.2.1
  have hp₂ : finrank K ↥(B ⊓ C) = p₂ := R.val.property.2.2.2
  have hn : finrank K ↥((A ⊔ B) ⊔ C) = n := R.property
  have hv := coannihilator_common_finrank A B C
  rw [hn] at hv
  have h₀ := Submodule.finrank_mono (show (A.dualCoannihilator ⊓ B.dualCoannihilator) ⊓ C.dualCoannihilator ≤
    A.dualCoannihilator ⊓ B.dualCoannihilator from inf_le_left)
  have h₁ := Submodule.finrank_mono (show (A.dualCoannihilator ⊓ B.dualCoannihilator) ⊓ C.dualCoannihilator ≤
    A.dualCoannihilator ⊓ C.dualCoannihilator from inf_le_inf inf_le_left le_rfl)
  have h₂ := Submodule.finrank_mono (show (A.dualCoannihilator ⊓ B.dualCoannihilator) ⊓ C.dualCoannihilator ≤
    B.dualCoannihilator ⊓ C.dualCoannihilator from inf_le_inf inf_le_right le_rfl)
  rw [hv] at h₀ h₁ h₂
  have hc₀ := coannihilator_pair_finrank A B
  have hc₁ := coannihilator_pair_finrank A C
  have hc₂ := coannihilator_pair_finrank B C
  rw [hdA,hdB,hp₀] at hc₀
  rw [hdA,hdC,hp₁] at hc₁
  rw [hdB,hdC,hp₂] at hc₂
  omega

private instance certificate_instance_0101 : OAI.SidorenkoCounterexample.ProofCertificate_0101 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11
  exact @certificate_proof_0101 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11

end ExtraFeasibility
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
section CanonicalParameterCount
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
theorem certificate_proof_0102 {r s₀ s₁ s₂ : ℕ}
    (P : CanonicalLiftProfile (K := K) (V := V) r s₀ s₁ s₂) :
    BaseFeasible r s₀ s₁ s₂ (canonicalLiftFourDims P) := by
  have hc := subspace_profile_constraints (canonicalLiftSubspaces P)
  refine ⟨hc.2.1,hc.2.2.1,hc.2.2.2.1,hc.2.2.2.2.1,hc.2.2.2.2.2,?_,?_,?_,?_,?_,?_,?_⟩
  · exact (dualGraph_pair_finrank_ge _ _ P.val.2.1 P.val.2.2.1).trans_eq P.property.2.1
  · exact (dualGraph_pair_finrank_ge _ _ P.val.2.1 P.val.2.2.2).trans_eq P.property.2.2.1
  · exact (dualGraph_pair_finrank_ge _ _ P.val.2.2.1 P.val.2.2.2).trans_eq P.property.2.2.2
  · exact dualGraph_pair_extra_feasible P.val.1.1 P.val.1.2.1 P.val.2.1 P.val.2.2.1 P.property.2.1
  · exact dualGraph_pair_extra_feasible P.val.1.1 P.val.1.2.2 P.val.2.1 P.val.2.2.2 P.property.2.2.1
  · exact dualGraph_pair_extra_feasible P.val.1.2.1 P.val.1.2.2 P.val.2.2.1 P.val.2.2.2 P.property.2.2.2
  · exact dual_common_pair_extra_feasible (canonicalLiftSubspaces P)

private instance certificate_instance_0102 : OAI.SidorenkoCounterexample.ProofCertificate_0102 := by
  constructor
  intro c0 c1 c2 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10
  exact @certificate_proof_0102 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10

theorem certificate_proof_0103 (R S : Submodule K (Module.Dual K V))
    (F : SymForm K R.dualCoannihilator) (G : SymForm K S.dualCoannihilator)
    {p s : ℕ} (hp : finrank K ↥(R ⊓ S) = p)
    (hs : finrank K ↥((dualGraph R F).val ⊓ (dualGraph S G).val) = s) :
    p+(s-p) ≤ finrank K ↥((dualGraph R F).val ⊓ (dualGraph S G).val) := by
  have h := dualGraph_pair_finrank_ge R S F G
  rw [hp,hs] at h
  rw [hs]
  omega

private instance certificate_instance_0103 : OAI.SidorenkoCounterexample.ProofCertificate_0103 := by
  constructor
  intro c0 c1 c2 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13
  exact @certificate_proof_0103 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13

theorem certificate_proof_0104 (r s₀ s₁ s₂ : ℕ) :
    Function.Injective (canonicalLiftCoding (K := K) (V := V) (r := r) (s₀ := s₀) (s₁ := s₁) (s₂ := s₂)) := by
  let recover : (Σ θ : BaseParameters (finrank K V) r s₀ s₁ s₂,
      Σ R : SubspaceTripleSpanProfile (K := K) (V := Module.Dual K V)
        r θ.val.1.val θ.val.2.1.val θ.val.2.2.1.val θ.val.2.2.2.val,
        DualLiftEvent R (s₀-θ.val.1.val) (s₁-θ.val.2.1.val) (s₂-θ.val.2.2.1.val)) →
      Σ R : DualBaseTriple (K := K) (V := V) r, DualBaseForms R :=
    fun T => ⟨T.2.1.val.val,T.2.2.val⟩
  intro P Q h
  exact Subtype.ext (congrArg recover h)

private instance certificate_instance_0104 : OAI.SidorenkoCounterexample.ProofCertificate_0104 := by
  constructor
  intro c0 c1 c2 c3 c4 c5 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9
  exact @certificate_proof_0104 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9

end CanonicalParameterCount
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
open scoped BigOperators
section CanonicalNumericalBound
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Fintype K] [Finite V]
theorem certificate_proof_0105 (r s₀ s₁ s₂ : ℕ)
    (θ : BaseParameters (finrank K V) r s₀ s₁ s₂) :
    (Nat.card (Σ R : SubspaceTripleSpanProfile (K := K) (V := Module.Dual K V)
        r θ.val.1.val θ.val.2.1.val θ.val.2.2.1.val θ.val.2.2.2.val,
        DualLiftEvent R (s₀-θ.val.1.val) (s₁-θ.val.2.1.val) (s₂-θ.val.2.2.1.val)) : ℝ) /
      (Nat.card (CenterStratum (K := K) (V := V) r) : ℝ)^3 ≤
    reducedPlantedConstant r s₀ s₁ s₂ θ.val *
      (Fintype.card K : ℝ)^(reducedPlantedExponent (finrank K V) r s₀ s₁ s₂ θ.val) := by
  let p₀ := θ.val.1.val
  let p₁ := θ.val.2.1.val
  let p₂ := θ.val.2.2.1.val
  let n := θ.val.2.2.2.val
  let t₀ := s₀-p₀
  let t₁ := s₁-p₁
  let t₂ := s₂-p₂
  have hn : n ≤ finrank K V := Nat.le_of_lt_succ θ.val.2.2.2.isLt
  have hcon := θ.property
  have hr : r ≤ n := hcon.1
  have hh := dual_lift_sum_probability_bound (K := K) (V := V) r p₀ p₁ p₂ n t₀ t₁ t₂ (hr.trans hn)
  have hp := subspace_span_probability_bound (K := K) (V := Module.Dual K V) r p₀ p₁ p₂ n
    (by rwa [Subspace.dual_finrank_eq]) hr hcon.2.1 hcon.2.2.1 hcon.2.2.2.1
  rw [Subspace.dual_finrank_eq] at hp
  refine hh.trans ((mul_le_mul_of_nonneg_right hp (by positivity)).trans_eq ?_)
  let q : ℝ := Fintype.card K
  have hq : 0 < q := by dsimp [q]; exact_mod_cast Fintype.card_pos (α := K)
  let e : ℝ := -((finrank K V:ℝ)-2*r)*(p₀+p₁+p₂) - ((p₀:ℝ)^2+p₁^2+p₂^2) -
    ((finrank K V:ℝ)-n)*(3*r-n-(p₀+p₁+p₂))
  change (2^(n+p₀+p₁+p₂+3*r) * q^e) *
    (2^(t₀+t₁+t₂)*q^((finrank K V-n+1).choose 2)/q^((t₀+1).choose 2+(t₁+1).choose 2+(t₂+1).choose 2)) = _
  have he : reducedPlantedExponent (finrank K V) r s₀ s₁ s₂ θ.val =
      e+((finrank K V-n+1).choose 2 : ℕ)-(((t₀+1).choose 2+(t₁+1).choose 2+(t₂+1).choose 2 : ℕ) : ℝ) := rfl
  rw [he,Real.rpow_sub hq (e+((finrank K V-n+1).choose 2 : ℕ))
    (((t₀+1).choose 2+(t₁+1).choose 2+(t₂+1).choose 2 : ℕ) : ℝ),
    Real.rpow_add hq e ((finrank K V-n+1).choose 2 : ℕ),Real.rpow_natCast,Real.rpow_natCast]
  simp only [reducedPlantedConstant, pow_add]
  change _ = 2^n*2^p₀*2^p₁*2^p₂*2^(3*r)*2^t₀*2^t₁*2^t₂ * _
  ring

private instance certificate_instance_0105 : OAI.SidorenkoCounterexample.ProofCertificate_0105 := by
  constructor
  intro c0 c1 c2 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12
  exact @certificate_proof_0105 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12

theorem certificate_proof_0106 (r s₀ s₁ s₂ : ℕ) (hr : r ≤ finrank K V) :
    (Nat.card (CenterTripleProfile (K := K) (V := V) r s₀ s₁ s₂) : ℝ) /
      (Nat.card (CenterStratum (K := K) (V := V) r) : ℝ)^3 ≤
    ∑ θ : BaseParameters (finrank K V) r s₀ s₁ s₂,
      reducedPlantedConstant r s₀ s₁ s₂ θ.val *
        (Fintype.card K : ℝ)^(reducedPlantedExponent (finrank K V) r s₀ s₁ s₂ θ.val) := by
  classical
  let : Finite (Module.Dual K V) := Module.finite_of_finite K
  have hi := Nat.card_le_card_of_injective _ (canonicalLiftCoding_injective (K := K) (V := V) r s₀ s₁ s₂)
  rw [Nat.card_congr (canonicalCenterProfileEquiv r s₀ s₁ s₂ hr),Nat.card_sigma] at hi
  have hi' := (Nat.cast_le (α := ℝ)).mpr hi
  rw [Nat.cast_sum] at hi'
  refine (div_le_div_of_nonneg_right hi' (by positivity)).trans ?_
  rw [Finset.sum_div]
  exact Finset.sum_le_sum (fun θ _ => reducedPlanted_bound_one r s₀ s₁ s₂ θ)

private instance certificate_instance_0106 : OAI.SidorenkoCounterexample.ProofCertificate_0106 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12
  exact @certificate_proof_0106 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12

end CanonicalNumericalBound
end SidorenkoCounterexample
end OAI
namespace OAI
namespace SidorenkoCounterexample
open Module
section Reduction
variable {K E : Type} [Field K] [AddCommGroup E] [Module K E]
variable (ω : LinearMap.BilinForm K E) (S : Submodule K E)
theorem certificate_proof_0107 (ha : ω.IsAlt) :
    (ω.compl₁₂ (ω.orthogonal S).subtype (ω.orthogonal S).subtype).IsAlt := by
  intro x
  exact ha x.val

private instance certificate_instance_0107 : OAI.SidorenkoCounterexample.ProofCertificate_0107 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7
  exact @certificate_proof_0107 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 q0 q1 q2 q3 q4 q5 q6 q7

theorem certificate_proof_0108 : reductionKernel ω S ≤
    (ω.compl₁₂ (ω.orthogonal S).subtype (ω.orthogonal S).subtype).ker := by
  intro x hx
  apply LinearMap.mem_ker.mpr
  ext y
  exact y.property x.val hx

private instance certificate_instance_0108 : OAI.SidorenkoCounterexample.ProofCertificate_0108 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6
  exact @certificate_proof_0108 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 q0 q1 q2 q3 q4 q5 q6

theorem certificate_proof_0109 (ha : ω.IsAlt) (x y : ω.orthogonal S) :
    symplecticReductionForm ω S ha
      ((reductionKernel ω S).mkQ x) ((reductionKernel ω S).mkQ y) = ω x.val y.val := rfl

private instance certificate_instance_0109 : OAI.SidorenkoCounterexample.ProofCertificate_0109 := by
  constructor
  intro c0 c1 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9
  exact @certificate_proof_0109 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9

theorem certificate_proof_0110 (ha : ω.IsAlt) :
    (symplecticReductionForm ω S ha).IsAlt := by
  intro x
  induction x using Submodule.Quotient.induction_on with
  | H x => exact ha x.val

private instance certificate_instance_0110 : OAI.SidorenkoCounterexample.ProofCertificate_0110 := by
  constructor
  intro c0 c1 q0 q1 q2 q3 q4 q5 q6 q7
  exact @certificate_proof_0110 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 q0 q1 q2 q3 q4 q5 q6 q7

theorem certificate_proof_0111 [FiniteDimensional K E]
    (ha : ω.IsAlt) (hω : ω.Nondegenerate) :
    (symplecticReductionForm ω S ha).Nondegenerate := by
  have hl (x : ReducedSpace ω S)
      (hx : ∀ y, symplecticReductionForm ω S ha x y = 0) : x = 0 := by
    induction x using Submodule.Quotient.induction_on with
    | H x =>
      apply (Submodule.Quotient.mk_eq_zero (reductionKernel ω S)).mpr
      change x.val ∈ S
      apply (ω.orthogonal_orthogonal hω ha.isRefl S).le
      intro y hy
      exact ha.isRefl _ _ (hx ((reductionKernel ω S).mkQ ⟨y,hy⟩))
  refine ⟨hl, ?_⟩
  intro x hx
  apply hl
  intro y
  exact (symplecticReductionForm_alt ω S ha).isRefl _ _ (hx y)

private instance certificate_instance_0111 : OAI.SidorenkoCounterexample.ProofCertificate_0111 := by
  constructor
  intro c0 c1 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9
  exact @certificate_proof_0111 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9

theorem certificate_proof_0112 [FiniteDimensional K E]
    (hω : ω.Nondegenerate) (hS : S ≤ ω.orthogonal S) :
    finrank K (ReducedSpace ω S) + 2 * finrank K S = finrank K E := by
  have hker : finrank K (reductionKernel ω S) = finrank K S :=
    (Submodule.comapSubtypeEquivOfLe hS).finrank_eq
  have hq := Submodule.finrank_quotient_add_finrank (reductionKernel ω S)
  have hp := ω.finrank_orthogonal hω S
  have hle := Submodule.finrank_le S
  change finrank K (ReducedSpace ω S) + finrank K (reductionKernel ω S) =
    finrank K (ω.orthogonal S) at hq
  rw [hker] at hq
  omega

private instance certificate_instance_0112 : OAI.SidorenkoCounterexample.ProofCertificate_0112 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9
  exact @certificate_proof_0112 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9

theorem certificate_proof_0113 (T : Submodule K (ReducedSpace ω S)) (x : E) :
    x ∈ liftReduction ω S T ↔ ∃ hx : x ∈ ω.orthogonal S,
      (reductionKernel ω S).mkQ ⟨x,hx⟩ ∈ T := by
  constructor
  · rintro ⟨y,hy,hx⟩
    cases hx
    exact ⟨y.property,hy⟩
  · rintro ⟨hx,ht⟩
    exact ⟨⟨x,hx⟩,ht,rfl⟩

private instance certificate_instance_0113 : OAI.SidorenkoCounterexample.ProofCertificate_0113 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8
  exact @certificate_proof_0113 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 q0 q1 q2 q3 q4 q5 q6 q7 q8

theorem certificate_proof_0114 (hS : S ≤ ω.orthogonal S)
    (T : Submodule K (ReducedSpace ω S)) : S ≤ liftReduction ω S T := by
  intro x hx
  apply (mem_liftReduction ω S T x).mpr
  refine ⟨hS hx, ?_⟩
  have hz : (reductionKernel ω S).mkQ ⟨x,hS hx⟩ = 0 :=
    (Submodule.Quotient.mk_eq_zero (reductionKernel ω S)).mpr hx
  rw [hz]
  exact T.zero_mem

private instance certificate_instance_0114 : OAI.SidorenkoCounterexample.ProofCertificate_0114 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8
  exact @certificate_proof_0114 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 q0 q1 q2 q3 q4 q5 q6 q7 q8

theorem certificate_proof_0115 (T : Submodule K (ReducedSpace ω S)) :
    liftReduction ω S T ≤ ω.orthogonal S := by
  rintro x ⟨y,hy,rfl⟩
  exact y.property

private instance certificate_instance_0115 : OAI.SidorenkoCounterexample.ProofCertificate_0115 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7
  exact @certificate_proof_0115 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 q0 q1 q2 q3 q4 q5 q6 q7

theorem certificate_proof_0116 (ha : ω.IsAlt) (hS : S ≤ ω.orthogonal S)
    (T : Submodule K (ReducedSpace ω S)) :
    ω.orthogonal (liftReduction ω S T) =
      liftReduction ω S ((symplecticReductionForm ω S ha).orthogonal T) := by
  ext x
  constructor
  · intro hx
    have hxP : x ∈ ω.orthogonal S := by
      intro s hs
      exact hx s (le_liftReduction ω S hS T hs)
    apply (mem_liftReduction ω S _ x).mpr
    refine ⟨hxP, ?_⟩
    intro y hy
    induction y using Submodule.Quotient.induction_on with
    | H y =>
      exact hx y.val ((mem_liftReduction ω S T y.val).mpr ⟨y.property,hy⟩)
  · intro hx
    obtain ⟨hxP,hxQ⟩ := (mem_liftReduction ω S _ x).mp hx
    intro y hy
    obtain ⟨hyP,hyQ⟩ := (mem_liftReduction ω S T y).mp hy
    exact hxQ ((reductionKernel ω S).mkQ ⟨y,hyP⟩) hyQ

private instance certificate_instance_0116 : OAI.SidorenkoCounterexample.ProofCertificate_0116 := by
  constructor
  intro c0 c1 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9
  exact @certificate_proof_0116 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9

theorem certificate_proof_0117 (ha : ω.IsAlt) (hS : S ≤ ω.orthogonal S)
    (T : Submodule K (ReducedSpace ω S))
    (hT : (symplecticReductionForm ω S ha).orthogonal T = T) :
    ω.orthogonal (liftReduction ω S T) = liftReduction ω S T := by
  rw [orthogonal_liftReduction ω S ha hS, hT]

private instance certificate_instance_0117 : OAI.SidorenkoCounterexample.ProofCertificate_0117 := by
  constructor
  intro c0 c1 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10
  exact @certificate_proof_0117 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10

theorem certificate_proof_0118 (T : Submodule K (ReducedSpace ω S)) :
    reduceSubspace ω S (liftReduction ω S T) = T := by
  ext z
  induction z using Submodule.Quotient.induction_on with
  | H z =>
    constructor
    · rintro ⟨y,hy,heq⟩
      obtain ⟨hyP,hyT⟩ := (mem_liftReduction ω S T y.val).mp hy
      change (reductionKernel ω S).mkQ y ∈ T at hyT
      exact heq ▸ hyT
    · intro hz
      refine ⟨z,?_,rfl⟩
      exact (mem_liftReduction ω S T z.val).mpr ⟨z.property,hz⟩

private instance certificate_instance_0118 : OAI.SidorenkoCounterexample.ProofCertificate_0118 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7
  exact @certificate_proof_0118 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 q0 q1 q2 q3 q4 q5 q6 q7

theorem certificate_proof_0119 : Function.Injective (liftReduction ω S) := by
  intro T U h
  have hh := congrArg (reduceSubspace ω S) h
  simpa only [reduce_lift] using hh

private instance certificate_instance_0119 : OAI.SidorenkoCounterexample.ProofCertificate_0119 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6
  exact @certificate_proof_0119 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 q0 q1 q2 q3 q4 q5 q6

theorem certificate_proof_0120 (L : Submodule K E) (hSL : S ≤ L) (hLP : L ≤ ω.orthogonal S) :
    liftReduction ω S (reduceSubspace ω S L) = L := by
  ext x
  constructor
  · intro hx
    obtain ⟨hxP,y,hy,hyeq⟩ := (mem_liftReduction ω S _ x).mp hx
    have hz : (reductionKernel ω S).mkQ (y - ⟨x,hxP⟩) = 0 := by
      rw [map_sub,hyeq,sub_self]
    have hzS : y.val-x ∈ S := (Submodule.Quotient.mk_eq_zero (reductionKernel ω S)).mp hz
    have hxL := L.sub_mem hy (hSL hzS)
    simpa only [Submodule.subtype_apply, sub_sub_cancel] using hxL
  · intro hx
    apply (mem_liftReduction ω S _ x).mpr
    exact ⟨hLP hx,⟨⟨x,hLP hx⟩,hx,rfl⟩⟩

private instance certificate_instance_0120 : OAI.SidorenkoCounterexample.ProofCertificate_0120 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9
  exact @certificate_proof_0120 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9

theorem certificate_proof_0121 (L : Submodule K E)
    (hL : ω.orthogonal L = L) (hSL : S ≤ L) : L ≤ ω.orthogonal S := by
  intro x hx s hs
  have hxO : x ∈ ω.orthogonal L := hL.symm ▸ hx
  exact hxO s (hSL hs)

private instance certificate_instance_0121 : OAI.SidorenkoCounterexample.ProofCertificate_0121 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9
  exact @certificate_proof_0121 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9

theorem certificate_proof_0122 (ha : ω.IsAlt) (hS : S ≤ ω.orthogonal S)
    (L : Submodule K E) (hL : ω.orthogonal L = L) (hSL : S ≤ L) :
    (symplecticReductionForm ω S ha).orthogonal (reduceSubspace ω S L) =
      reduceSubspace ω S L := by
  apply liftReduction_injective ω S
  rw [← orthogonal_liftReduction ω S ha hS,
    lift_reduce ω S L hSL (lagrangian_le_orthogonal ω S L hL hSL),hL]

private instance certificate_instance_0122 : OAI.SidorenkoCounterexample.ProofCertificate_0122 := by
  constructor
  intro c0 c1 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11
  exact @certificate_proof_0122 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11

theorem certificate_proof_0123 (U W : Submodule K E) :
    ω.orthogonal (U ⊔ W) = ω.orthogonal U ⊓ ω.orthogonal W := by
  ext x
  constructor
  · intro hx
    exact ⟨fun y hy => hx y ((le_sup_left : U ≤ U ⊔ W) hy), fun y hy => hx y ((le_sup_right : W ≤ U ⊔ W) hy)⟩
  · rintro ⟨hU,hW⟩ y hy
    obtain ⟨u,hu,w,hw,rfl⟩ := Submodule.mem_sup.mp hy
    simp only [map_add,LinearMap.add_apply,hU u hu,hW w hw,add_zero]

private instance certificate_instance_0123 : OAI.SidorenkoCounterexample.ProofCertificate_0123 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7
  exact @certificate_proof_0123 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 q0 q1 q2 q3 q4 q5 q6 q7

theorem certificate_proof_0124 [FiniteDimensional K E] (ha : ω.IsAlt) (hω : ω.Nondegenerate)
    (U W : Submodule K E) :
    ω.orthogonal (U ⊓ W) = ω.orthogonal U ⊔ ω.orthogonal W := by
  have hinj : Function.Injective ω.orthogonal := by
    intro A B h
    have hh := congrArg ω.orthogonal h
    simpa only [ω.orthogonal_orthogonal hω ha.isRefl] using hh
  apply hinj
  rw [ω.orthogonal_orthogonal hω ha.isRefl, orthogonal_sup_eq,
    ω.orthogonal_orthogonal hω ha.isRefl,ω.orthogonal_orthogonal hω ha.isRefl]

private instance certificate_instance_0124 : OAI.SidorenkoCounterexample.ProofCertificate_0124 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10
  exact @certificate_proof_0124 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10

theorem certificate_proof_0125 [FiniteDimensional K E]
    (ha : ω.IsAlt) (hω : ω.Nondegenerate) (hS : S ≤ ω.orthogonal S)
    (L : Submodule K E) (hL : ω.orthogonal L = L) :
    (symplecticReductionForm ω S ha).orthogonal (reduceSubspace ω S L) =
      reduceSubspace ω S L := by
  let U := (L ⊓ ω.orthogonal S) ⊔ S
  have hUL : ω.orthogonal U = U := by
    dsimp only [U]
    rw [orthogonal_sup_eq, orthogonal_inf_eq ω ha hω, hL,
      ω.orthogonal_orthogonal hω ha.isRefl]
    apply le_antisymm
    · rintro x ⟨hx,hxP⟩
      obtain ⟨l,hl,s,hs,rfl⟩ := Submodule.mem_sup.mp hx
      have hlP : l ∈ ω.orthogonal S := by
        have h := (ω.orthogonal S).sub_mem hxP (hS hs)
        simpa only [add_sub_cancel_right] using h
      exact Submodule.mem_sup.mpr ⟨l,⟨hl,hlP⟩,s,hs,rfl⟩
    · rintro x hx
      obtain ⟨l,hl,s,hs,rfl⟩ := Submodule.mem_sup.mp hx
      exact ⟨Submodule.mem_sup.mpr ⟨l,hl.1,s,hs,rfl⟩,
        (ω.orthogonal S).add_mem hl.2 (hS hs)⟩
  have hUred : reduceSubspace ω S U = reduceSubspace ω S L := by
    ext x
    constructor
    · rintro ⟨y,hy,rfl⟩
      obtain ⟨l,hl,s,hs,hls⟩ := Submodule.mem_sup.mp hy
      refine ⟨⟨l,hl.2⟩,hl.1,?_⟩
      have hz : (reductionKernel ω S).mkQ ⟨s,hS hs⟩ = 0 :=
        (Submodule.Quotient.mk_eq_zero (reductionKernel ω S)).mpr hs
      have heq : y = (⟨l,hl.2⟩ : ω.orthogonal S) + ⟨s,hS hs⟩ :=
        Subtype.ext hls.symm
      rw [heq,map_add,hz,add_zero]
    · rintro ⟨y,hy,rfl⟩
      exact ⟨y,(le_sup_left : L ⊓ ω.orthogonal S ≤ U) ⟨hy,y.property⟩,rfl⟩
  rw [← hUred]
  exact reduce_lagrangian ω S ha hS U hUL le_sup_right

private instance certificate_instance_0125 : OAI.SidorenkoCounterexample.ProofCertificate_0125 := by
  constructor
  intro c0 c1 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12
  exact @certificate_proof_0125 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12

end Reduction
section IsotropicExtension
variable {K E : Type} [Field K] [AddCommGroup E] [Module K E] [Finite E]
variable (ω : LinearMap.BilinForm K E)
omit [Finite E] in
theorem certificate_proof_0126 (ha : ω.IsAlt) (L : Submodule K E)
    (hL : L ≤ ω.orthogonal L) (x : E) (hx : x ∈ ω.orthogonal L) :
    L ⊔ K ∙ x ≤ ω.orthogonal (L ⊔ K ∙ x) := by
  intro y hy z hz
  obtain ⟨l,hl,v,hv,rfl⟩ := Submodule.mem_sup.mp hy
  obtain ⟨m,hm,w,hw,rfl⟩ := Submodule.mem_sup.mp hz
  obtain ⟨a,rfl⟩ := Submodule.mem_span_singleton.mp hv
  obtain ⟨b,rfl⟩ := Submodule.mem_span_singleton.mp hw
  have hxl : ω x l = 0 := ha.isRefl _ _ (hx l hl)
  simp only [map_add,map_smul,LinearMap.add_apply,LinearMap.smul_apply,
    hL hl m hm,hx m hm,hxl,ha x,smul_zero,add_zero]

private instance certificate_instance_0126 : OAI.SidorenkoCounterexample.ProofCertificate_0126 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10
  exact @certificate_proof_0126 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10

theorem certificate_proof_0127 (ha : ω.IsAlt) (S : Submodule K E)
    (hS : S ≤ ω.orthogonal S) :
    ∃ L : Submodule K E, S ≤ L ∧ ω.orthogonal L = L := by
  classical
  let A : Set (Submodule K E) := {L | S ≤ L ∧ L ≤ ω.orthogonal L}
  obtain ⟨L,hL,hmax⟩ := (Set.toFinite A).exists_maximal ⟨S,le_rfl,hS⟩
  refine ⟨L,hL.1,le_antisymm ?_ hL.2⟩
  intro x hx
  have hU : (L ⊔ K ∙ x) ∈ A :=
    ⟨hL.1.trans le_sup_left,isotropic_sup_line ω ha L hL.2 x hx⟩
  exact hmax hU le_sup_left ((le_sup_right : K ∙ x ≤ L ⊔ K ∙ x) (Submodule.mem_span_singleton_self x))

private instance certificate_instance_0127 : OAI.SidorenkoCounterexample.ProofCertificate_0127 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9
  exact @certificate_proof_0127 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9

end IsotropicExtension
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
section QuotientExtension
variable {K E : Type} [Field K] [AddCommGroup E] [Module K E]
variable [FiniteDimensional K E]
variable (ω : LinearMap.BilinForm K E) (S : Submodule K E)
omit [FiniteDimensional K E] in
theorem certificate_proof_0128 (ha : ω.IsAlt) (U : Submodule K E)
    (x y : U × ω.orthogonal U) :
    ω (x.1.val + x.2.val) (y.1.val + y.2.val) =
      ω x.1.val y.1.val + ω x.2.val y.2.val := by
  have hxy : ω x.1.val y.2.val = 0 := y.2.property x.1.val x.1.property
  have hyx : ω x.2.val y.1.val = 0 :=
    ha.isRefl _ _ (x.2.property y.1.val y.1.property)
  simp only [map_add, LinearMap.add_apply, hxy, hyx, add_zero, zero_add]

private instance certificate_instance_0128 : OAI.SidorenkoCounterexample.ProofCertificate_0128 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9
  exact @certificate_proof_0128 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9

theorem certificate_proof_0129 (ha : ω.IsAlt) (U : Submodule K E)
    (hU : (ω.restrict U).Nondegenerate) (f : U ≃ₗ[K] U)
    (hf : ∀ x y : U, ω (f x).val (f y).val = ω x.val y.val) :
    ∃ e : E ≃ₗ[K] E,
      (∀ x y, ω (e x) (e y) = ω x y) ∧
      (∀ x : U, e x.val = (f x).val) ∧
      (∀ x : ω.orthogonal U, e x.val = x.val) := by
  let c := U.prodEquivOfIsCompl (ω.orthogonal U)
    (ω.isCompl_orthogonal_of_restrict_nondegenerate ha.isRefl hU)
  let e := c.symm.trans ((f.prodCongr (LinearEquiv.refl K (ω.orthogonal U))).trans c)
  have he (x : U × ω.orthogonal U) : e (c x) = c (f x.1,x.2) := by
    simp [e]
  refine ⟨e, ?_, ?_, ?_⟩
  · intro x y
    obtain ⟨x,rfl⟩ := c.surjective x
    obtain ⟨y,rfl⟩ := c.surjective y
    rw [he,he]
    change ω ((f x.1).val + x.2.val) ((f y.1).val + y.2.val) =
      ω (x.1.val + x.2.val) (y.1.val + y.2.val)
    rw [form_orthogonal_sum ω ha U (f x.1,x.2) (f y.1,y.2),
      form_orthogonal_sum ω ha U x y,hf]
  · intro x
    have h := he (x,0)
    simpa [c] using h
  · intro x
    have h := he (0,x)
    simpa [c] using h

private instance certificate_instance_0129 : OAI.SidorenkoCounterexample.ProofCertificate_0129 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11
  exact @certificate_proof_0129 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11

omit [FiniteDimensional K E] in
theorem certificate_proof_0130 (ha : ω.IsAlt)
    (s : ReducedSpace ω S →ₗ[K] ω.orthogonal S)
    (hs : (reductionKernel ω S).mkQ.comp s = LinearMap.id)
    (x y : ReducedSpace ω S) :
    ω (s x).val (s y).val = symplecticReductionForm ω S ha x y := by
  have hx : (reductionKernel ω S).mkQ (s x) = x := LinearMap.congr_fun hs x
  have hy : (reductionKernel ω S).mkQ (s y) = y := LinearMap.congr_fun hs y
  calc
    _ = symplecticReductionForm ω S ha
      ((reductionKernel ω S).mkQ (s x)) ((reductionKernel ω S).mkQ (s y)) := rfl
    _ = _ := by rw [hx,hy]

private instance certificate_instance_0130 : OAI.SidorenkoCounterexample.ProofCertificate_0130 := by
  constructor
  intro c0 c1 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11
  exact @certificate_proof_0130 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11

end QuotientExtension
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
section ReductionLaws
variable {K E : Type} [Field K] [AddCommGroup E] [Module K E]
variable (ω : LinearMap.BilinForm K E) (S : Submodule K E)
variable [FiniteDimensional K E]
variable [Finite E]
end ReductionLaws
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
section IsotropicTransitivity
variable {K E : Type} [Field K] [AddCommGroup E] [Module K E]
  [FiniteDimensional K E] [Finite E]
variable (ω : LinearMap.BilinForm K E)
end IsotropicTransitivity
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
section TransversePairs
variable {K E : Type} [Field K] [AddCommGroup E] [Module K E]
  [FiniteDimensional K E]
variable (ω : LinearMap.BilinForm K E)
end TransversePairs
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
section PairTransitivity
variable {K E : Type} [Field K] [AddCommGroup E] [Module K E]
  [FiniteDimensional K E]
variable (ω : LinearMap.BilinForm K E)
end PairTransitivity
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
section PairReduction
variable {K E : Type} [Field K] [AddCommGroup E] [Module K E]
variable (ω : LinearMap.BilinForm K E) (S : Submodule K E)
variable [FiniteDimensional K E]
end PairReduction
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
section OrderedPairTransitivity
variable {K E : Type} [Field K] [AddCommGroup E] [Module K E]
  [FiniteDimensional K E] [Finite E]
variable (ω : LinearMap.BilinForm K E)
end OrderedPairTransitivity
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
section TripleBlocks
variable {K E : Type} [Field K] [AddCommGroup E] [Module K E]
  [FiniteDimensional K E]
variable (ω : LinearMap.BilinForm K E)
end TripleBlocks
end SidorenkoCounterexample
end OAI

theorem solution : OAI.SidorenkoCounterexample.ProofCertificate_0100 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0101 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0102 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0103 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0104 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0105 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0106 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0107 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0108 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0109 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0110 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0111 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0112 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0113 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0114 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0115 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0116 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0117 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0118 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0119 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0120 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0121 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0122 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0123 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0124 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0125 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0126 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0127 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0128 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0129 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0130 := by
  exact ⟨inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance⟩
end

