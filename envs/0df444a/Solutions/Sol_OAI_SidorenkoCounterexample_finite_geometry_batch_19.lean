-- Prove2me | solution 1 for OAI.SidorenkoCounterexample.finite_geometry_batch_19
-- status  : ACCEPTED   (prove)
-- author  : @abcdefg
-- created : 2026-10-09T06:20:47.700148+00:00
-- url     : https://prove2.me/submissions/03bd6601-fa01-4442-b809-51f82bd88978

import Definitions.Def_SidorenkoCertificateBundleA
set_option linter.unusedVariables false
section
variable [p0 : OAI.SidorenkoCounterexample.ProofCertificate_0000]
  [p1 : OAI.SidorenkoCounterexample.ProofCertificate_0372]
  [p2 : OAI.SidorenkoCounterexample.ProofCertificate_0373]
  [p3 : OAI.SidorenkoCounterexample.ProofCertificate_0487]
  [p4 : OAI.SidorenkoCounterexample.ProofCertificate_0490]
  [p5 : OAI.SidorenkoCounterexample.ProofCertificate_0491]
  [p6 : OAI.SidorenkoCounterexample.ProofCertificate_0495]
include p0 p1 p2 p3 p4 p5 p6

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
omit [Fintype I] in
theorem certificate_proof_0496 (h : I → ℕ) (R : I → I → Prop) :
    Function.Injective (directBasisForget ω h R) := by
  rintro ⟨A,s⟩ ⟨B,t⟩ hh
  have hv (i : I) (a : Fin (h i)) : ((s i).val a:E)=((t i).val a:E) :=
    congrArg (fun x : ConstrainedTuple ω (fun a b : Σ i, Fin (h i) => R a.1 b.1) => x.val ⟨i,a⟩) hh
  have hAB : A=B := by
    apply Subtype.ext
    funext i
    apply Subtype.ext
    rw [←tuple_spans (h i) (A.val i) (s i),←tuple_spans (h i) (B.val i) (t i)]
    congr 2
    exact funext (hv i)
  subst B
  congr 1
  funext i
  apply Subtype.ext
  funext a
  exact Subtype.ext (hv i a)

private instance certificate_instance_0496 : OAI.SidorenkoCounterexample.ProofCertificate_0496 := by
  constructor
  intro c0 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9
  exact @certificate_proof_0496 p0 p1 p2 p3 p4 p5 p6 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9

variable [Fintype K]
theorem certificate_proof_0497 {h : I → ℕ} {R : I → I → Prop} (A : DirectFamily ω h R) :
    (Fintype.card K:ℝ)^(∑ i, h i*h i) ≤ 2^(∑ i, h i)*(Nat.card (FamilyBases ω A):ℝ) := by
  classical
  have hp := Finset.prod_le_prod (s:=Finset.univ)
    (fun i _ => pow_nonneg (Nat.cast_nonneg (Fintype.card K)) (h i*h i))
    (fun i _ => independentTuples_card_lower (E:=(A.val i).val) (h i) (A.val i).property)
  rw [FamilyBases,Nat.card_pi,Nat.cast_prod]
  simpa only [Finset.prod_mul_distrib,Finset.prod_pow_eq_pow_sum] using hp

private instance certificate_instance_0497 : OAI.SidorenkoCounterexample.ProofCertificate_0497 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12
  exact @certificate_proof_0497 p0 p1 p2 p3 p4 p5 p6 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12

theorem certificate_proof_0498 (hω : ω.Nondegenerate) (h : I → ℕ) (R : I → I → Prop)
    (hR : ∀ i j, R i j → R j i) (hn : (∑ i, h i)≤finrank K E) :
    (Nat.card (DirectFamily ω h R):ℝ) ≤ 2^(∑ i,h i)*
      (Fintype.card K:ℝ)^((finrank K E:ℝ)*(∑ i, h i)-
        (Nat.card {p : (Σ i, Fin (h i))×(Σ i, Fin (h i)) // p.1≠p.2 ∧ R p.1.1 p.2.1}:ℝ)/2-
        ∑ i, (h i:ℝ)^2) := by
  classical
  let := Fintype.ofFinite (DirectFamily ω h R)
  have hq : 0<(Fintype.card K:ℝ) := by exact_mod_cast Fintype.card_pos (α:=K)
  have hb := constrainedTuple_card_rpow ω hω (fun a b : Σ i, Fin (h i) => R a.1 b.1)
    (fun a b hr => hR _ _ hr) (by simpa only [Fintype.card_sigma,Fintype.card_fin] using hn)
  have hf : (Nat.card (Σ A : DirectFamily ω h R, FamilyBases ω A):ℝ) ≤
      Nat.card (ConstrainedTuple ω (fun a b : Σ i, Fin (h i) => R a.1 b.1)) := by
    exact_mod_cast Nat.card_le_card_of_injective _ (directBasisForget_injective ω h R)
  have hl : (Nat.card (DirectFamily ω h R):ℝ)*(Fintype.card K:ℝ)^(∑ i, h i*h i) ≤
      2^(∑ i, h i)*(Nat.card (Σ A : DirectFamily ω h R, FamilyBases ω A):ℝ) := by
    rw [Nat.card_sigma,Nat.cast_sum,Finset.mul_sum]
    calc
      _ = ∑ _A : DirectFamily ω h R, (Fintype.card K:ℝ)^(∑ i, h i*h i) := by
        simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Nat.card_eq_fintype_card]
      _ ≤ _ := Finset.sum_le_sum (fun A _ => familyBases_card_lower ω A)
  have hm := hl.trans (mul_le_mul_of_nonneg_left (hf.trans hb) (by positivity : (0:ℝ)≤2^(∑ i,h i)))
  have he : ((∑ i, h i*h i:ℕ):ℝ)=∑ i, (h i:ℝ)^2 := by simp only [Nat.cast_sum,Nat.cast_mul,pow_two]
  rw [←Real.rpow_natCast,he] at hm
  have hsum : (Fintype.card (Σ i, Fin (h i)):ℝ)=∑ i, (h i:ℝ) := by simp only [Fintype.card_sigma,Fintype.card_fin,Nat.cast_sum]
  rw [hsum] at hm
  apply (le_div_iff₀ (Real.rpow_pos_of_pos hq _)).mpr at hm
  rw [mul_div_assoc,←Real.rpow_sub hq] at hm
  simpa only [Nat.cast_sum,mul_comm (∑ i, (h i:ℝ)) (finrank K E:ℝ)] using hm

private instance certificate_instance_0498 : OAI.SidorenkoCounterexample.ProofCertificate_0498 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14
  exact @certificate_proof_0498 p0 p1 p2 p3 p4 p5 p6 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14

end DirectFamilies
end SidorenkoCounterexample
end OAI
namespace OAI
namespace SidorenkoCounterexample
open Module
section Span
variable {K V P : Type} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Fintype P] [DecidableEq P]
omit [FiniteDimensional K V] [Fintype P] in
theorem certificate_proof_0499 (s : Finset (Finset P)) (H : Finset P → Submodule K V)
    (i : P) : localSpan s H i ≤ s.sup H :=
  Finset.sup_mono (Finset.filter_subset _ _)

private instance certificate_instance_0499 : OAI.SidorenkoCounterexample.ProofCertificate_0499 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9
  exact @certificate_proof_0499 p0 p1 p2 p3 p4 p5 p6 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9

omit [FiniteDimensional K V] [Fintype P] in
theorem certificate_proof_0500 (s : Finset (Finset P)) (e : Finset P)
    (H : Finset P → Submodule K V) (i : P) :
    localSpan (insert e s) H i = if i ∈ e then H e ⊔ localSpan s H i
      else localSpan s H i := by
  classical
  simp only [localSpan, Finset.filter_insert]
  split_ifs <;> simp

private instance certificate_instance_0500 : OAI.SidorenkoCounterexample.ProofCertificate_0500 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10
  exact @certificate_proof_0500 p0 p1 p2 p3 p4 p5 p6 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10

theorem certificate_proof_0501 (s : Finset (Finset P)) (e : Finset P)
    (H : Finset P → Submodule K V) :
    (∑ i, finrank K (localSpan (insert e s) H i)) +
      (∑ i ∈ e, finrank K (H e ⊓ localSpan s H i : Submodule K V)) =
    (∑ i, finrank K (localSpan s H i)) + e.card * finrank K (H e) := by
  classical
  have heq (i : P) : finrank K (localSpan (insert e s) H i) +
      (if i ∈ e then finrank K (H e ⊓ localSpan s H i : Submodule K V) else 0) =
      finrank K (localSpan s H i) + (if i ∈ e then finrank K (H e) else 0) := by
    by_cases hi : i ∈ e
    · rw [localSpan_insert, if_pos hi, if_pos hi, if_pos hi]
      exact (Submodule.finrank_sup_add_finrank_inf_eq (H e) (localSpan s H i)).trans (Nat.add_comm _ _)
    · rw [localSpan_insert, if_neg hi, if_neg hi, if_neg hi]
  have h := congrArg (fun f : P → ℕ => ∑ i, f i) (funext heq)
  simpa only [Finset.sum_add_distrib, Finset.sum_ite_mem, Finset.sum_const,
    smul_eq_mul, Finset.univ_inter] using h

private instance certificate_instance_0501 : OAI.SidorenkoCounterexample.ProofCertificate_0501 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11
  exact @certificate_proof_0501 p0 p1 p2 p3 p4 p5 p6 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11

theorem certificate_proof_0502 (s : Finset (Finset P))
    (H : Finset P → Submodule K V) (hs : ∀ e ∈ s, e.card = 2) :
    2 * finrank K (s.sup H : Submodule K V) ≤ ∑ i, finrank K (localSpan s H i) ∧
    ((∑ i, finrank K (localSpan s H i)) = 2 * finrank K (s.sup H : Submodule K V) →
      s.SupIndep H) := by
  classical
  induction s using Finset.induction with
  | empty =>
    rw [Finset.sup_empty]
    constructor
    · simp
    · intro _
      exact Finset.supIndep_empty H
  | @insert e s he ih =>
    have hse : ∀ f ∈ s, f.card = 2 := fun f hf => hs f (Finset.mem_insert_of_mem hf)
    obtain ⟨hbound, hrigid⟩ := ih hse
    have hecard := hs e (Finset.mem_insert_self _ _)
    obtain ⟨a, b, hab, heab⟩ := Finset.card_eq_two.mp hecard
    have hr := local_rank_insert s e H
    rw [hecard, heab] at hr
    simp only [Finset.sum_pair hab] at hr
    rw [← heab] at hr
    have hg := Submodule.finrank_sup_add_finrank_inf_eq (H e) (s.sup H)
    have hda := Submodule.finrank_mono
      (inf_le_inf_left (H e) (localSpan_le s H a))
    have hdb := Submodule.finrank_mono
      (inf_le_inf_left (H e) (localSpan_le s H b))
    rw [Finset.sup_insert]
    constructor
    · omega
    · intro heq
      have hold : (∑ i, finrank K (localSpan s H i)) = 2 * finrank K (s.sup H : Submodule K V) := by omega
      have hA : finrank K (H e ⊓ localSpan s H a : Submodule K V) =
          finrank K (H e ⊓ s.sup H : Submodule K V) := by omega
      have hB : finrank K (H e ⊓ localSpan s H b : Submodule K V) =
          finrank K (H e ⊓ s.sup H : Submodule K V) := by omega
      have hind := hrigid hold
      have hfilters : Disjoint (s.filter fun f => a ∈ f) (s.filter fun f => b ∈ f) := by
        rw [Finset.disjoint_left]
        intro f hfa hfb
        obtain ⟨hf, haf⟩ := Finset.mem_filter.mp hfa
        have hbf := (Finset.mem_filter.mp hfb).2
        have hef : e ⊆ f := by
          rw [heab]
          intro x hx
          rcases Finset.mem_insert.mp hx with hxa | hxb
          · exact hxa ▸ haf
          · exact (Finset.mem_singleton.mp hxb) ▸ hbf
        have heqf : e = f := Finset.eq_of_subset_of_card_le hef (by rw [hse f hf, hecard])
        exact he (heqf.symm ▸ hf)
      have hdis : Disjoint (localSpan s H a) (localSpan s H b) :=
        hind.disjoint_sup_sup (Finset.filter_subset _ _) (Finset.filter_subset _ _) hfilters
      have hAe := Submodule.eq_of_le_of_finrank_eq
        (inf_le_inf_left (H e) (localSpan_le s H a)) hA
      have hBe := Submodule.eq_of_le_of_finrank_eq
        (inf_le_inf_left (H e) (localSpan_le s H b)) hB
      have hnew : Disjoint (H e) (s.sup H) := by
        rw [disjoint_iff_inf_le]
        calc
          H e ⊓ s.sup H ≤ localSpan s H a ⊓ localSpan s H b := by
            exact le_inf (hAe ▸ inf_le_right) (hBe ▸ inf_le_right)
          _ ≤ ⊥ := hdis.le_bot
      exact hind.insert hnew

private instance certificate_instance_0502 : OAI.SidorenkoCounterexample.ProofCertificate_0502 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11
  exact @certificate_proof_0502 p0 p1 p2 p3 p4 p5 p6 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11

theorem certificate_proof_0503 (s : Finset (Finset P)) (H : Finset P → Submodule K V)
    (hs : ∀ e ∈ s, e.card = 2) :
    2 * finrank K (s.sup H : Submodule K V) ≤ ∑ i, finrank K (localSpan s H i) :=
  (span_inequality_with_rigidity s H hs).1

private instance certificate_instance_0503 : OAI.SidorenkoCounterexample.ProofCertificate_0503 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11
  exact @certificate_proof_0503 p0 p1 p2 p3 p4 p5 p6 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11

theorem certificate_proof_0504 (s : Finset (Finset P)) (H : Finset P → Submodule K V)
    (hs : ∀ e ∈ s, e.card = 2) (hn : ¬s.SupIndep H) :
    2 * finrank K (s.sup H : Submodule K V) + 1 ≤ ∑ i, finrank K (localSpan s H i) := by
  obtain ⟨hb, hr⟩ := span_inequality_with_rigidity s H hs
  have hne : (∑ i, finrank K (localSpan s H i)) ≠ 2 * finrank K (s.sup H : Submodule K V) :=
    fun h => hn (hr h)
  omega

private instance certificate_instance_0504 : OAI.SidorenkoCounterexample.ProofCertificate_0504 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12
  exact @certificate_proof_0504 p0 p1 p2 p3 p4 p5 p6 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12

end Span
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
open scoped BigOperators
section FiniteSpans
variable {K E I : Type} [Field K] [AddCommGroup E] [Module K E] [FiniteDimensional K E]
theorem certificate_proof_0505 (s : Finset I) (A : I → Submodule K E) :
    finrank K ↥(s.sup A) ≤ ∑ i∈s, finrank K (A i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.sup_insert,Finset.sum_insert hi]
    have := Submodule.finrank_sup_add_finrank_inf_eq (A i) (s.sup A)
    omega

private instance certificate_instance_0505 : OAI.SidorenkoCounterexample.ProofCertificate_0505 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8
  exact @certificate_proof_0505 p0 p1 p2 p3 p4 p5 p6 q0 q1 q2 q3 q4 q5 q6 q7 q8

theorem certificate_proof_0506 [Fintype I] (A : I → Submodule K E) :
    finrank K ↥(⨆ i,A i) ≤ ∑ i, finrank K (A i) := by
  have hh := finrank_finset_sup_le Finset.univ A
  exact (le_of_eq (congrArg (fun S : Submodule K E=>finrank K S)
    (Finset.sup_univ_eq_iSup A).symm)).trans hh

private instance certificate_instance_0506 : OAI.SidorenkoCounterexample.ProofCertificate_0506 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8
  exact @certificate_proof_0506 p0 p1 p2 p3 p4 p5 p6 q0 q1 q2 q3 q4 q5 q6 q7 q8

theorem certificate_proof_0507 (s : Finset I) (A : I → Submodule K E)
    (ha : iSupIndep A) : finrank K ↥(s.sup A) = ∑ i∈s, finrank K (A i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    have hd : Disjoint (A i) (s.sup A) := by
      rw [Finset.sup_eq_iSup]
      exact ha.disjoint_biSup hi
    have hh := Submodule.finrank_sup_add_finrank_inf_eq (A i) (s.sup A)
    rw [hd.eq_bot,finrank_bot,add_zero] at hh
    rw [Finset.sup_insert,Finset.sum_insert hi,hh,ih]

private instance certificate_instance_0507 : OAI.SidorenkoCounterexample.ProofCertificate_0507 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9
  exact @certificate_proof_0507 p0 p1 p2 p3 p4 p5 p6 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9

end FiniteSpans
instance (e f : Fin 33) : Decidable (pairRelated e f) := inferInstanceAs (Decidable (¬Disjoint _ _))
theorem certificate_proof_0508 (e f : Fin 33) : pairRelated e f → pairRelated f e := by
  unfold pairRelated; intro h hf; exact h hf.symm

private instance certificate_instance_0508 : OAI.SidorenkoCounterexample.ProofCertificate_0508 := by
  constructor
  intro q0 q1 q2
  exact @certificate_proof_0508 p0 p1 p2 p3 p4 p5 p6 q0 q1 q2

theorem certificate_proof_0509 : ∀ i, (incidentPairs i).card = (![4,6,4,6,5,4,5,5,5,6,5,6,5] : Fin 13 → ℕ) i := by decide

private instance certificate_instance_0509 : OAI.SidorenkoCounterexample.ProofCertificate_0509 := by
  constructor
  intro q0
  exact @certificate_proof_0509 p0 p1 p2 p3 p4 p5 p6 q0

theorem certificate_proof_0510 : ∀ i, (incidentPairs i).card≤6 := by decide

private instance certificate_instance_0510 : OAI.SidorenkoCounterexample.ProofCertificate_0510 := by
  constructor
  intro q0
  exact @certificate_proof_0510 p0 p1 p2 p3 p4 p5 p6 q0

theorem certificate_proof_0511 : ∀ e f, (Finset.univ.filter (fun i => e∈incidentPairs i ∧ f∈incidentPairs i)).card =
    if e=f then 2 else if pairRelated e f then 1 else 0 := by decide

private instance certificate_instance_0511 : OAI.SidorenkoCounterexample.ProofCertificate_0511 := by
  constructor
  intro q0 q1
  exact @certificate_proof_0511 p0 p1 p2 p3 p4 p5 p6 q0 q1

theorem certificate_proof_0512 (e : Fin 33) : (Finset.univ.filter (fun i => e∈incidentPairs i)).card=2 := by
  have he : Finset.univ.filter (fun i => e∈incidentPairs i)=pairVertices e := by
    ext i; simp only [Finset.mem_filter,Finset.mem_univ,true_and,incidentPairs]
  rw [he,pairVertices_card]

private instance certificate_instance_0512 : OAI.SidorenkoCounterexample.ProofCertificate_0512 := by
  constructor
  intro q0
  exact @certificate_proof_0512 p0 p1 p2 p3 p4 p5 p6 q0

theorem certificate_proof_0513 (f : Fin 33 → ℝ) :
    (∑ i : Fin 13, ∑ e∈incidentPairs i, f e)=2*∑ e,f e := by
  simp only [incidentPairs,Finset.sum_filter]
  rw [Finset.sum_comm]
  have hh (e : Fin 33) : (∑ i : Fin 13, if i∈pairVertices e then f e else 0)=2*f e := by
    rw [←Finset.sum_filter,Finset.sum_const]
    have hc : (Finset.univ.filter (fun i=>i∈pairVertices e)).card=2 := by
      have he : Finset.univ.filter (fun i=>i∈pairVertices e)=pairVertices e := by ext i; simp
      rw [he,pairVertices_card]
    rw [hc]; simp only [nsmul_eq_mul,Nat.cast_ofNat]
  simp_rw [hh]
  rw [Finset.mul_sum]

private instance certificate_instance_0513 : OAI.SidorenkoCounterexample.ProofCertificate_0513 := by
  constructor
  intro q0
  exact @certificate_proof_0513 p0 p1 p2 p3 p4 p5 p6 q0

theorem certificate_proof_0514 (h : Fin 33 → ℕ) (hh : ∀ e,h e≤2) (i : Fin 13) : localPairDim h i≤2*(incidentPairs i).card := by
  unfold localPairDim
  calc _ ≤ ∑ _e∈incidentPairs i, 2 := Finset.sum_le_sum (fun e _=>hh e)
       _ = _ := by simp only [Finset.sum_const,nsmul_eq_mul,Nat.cast_id]; omega

private instance certificate_instance_0514 : OAI.SidorenkoCounterexample.ProofCertificate_0514 := by
  constructor
  intro q0 q1 q2
  exact @certificate_proof_0514 p0 p1 p2 p3 p4 p5 p6 q0 q1 q2

theorem certificate_proof_0515 (h : Fin 33 → ℕ) (hh : ∀ e,h e≤2) (i : Fin 13) : localPairDim h i≤12 := by
  have := localPairDim_le h hh i
  have := incidentPairs_card_le i
  omega

private instance certificate_instance_0515 : OAI.SidorenkoCounterexample.ProofCertificate_0515 := by
  constructor
  intro q0 q1 q2
  exact @certificate_proof_0515 p0 p1 p2 p3 p4 p5 p6 q0 q1 q2

section GraphSpans
variable {K E : Type} [Field K] [AddCommGroup E] [Module K E]
theorem certificate_proof_0516 {A : Fin 33 → Submodule K E} {i : Fin 13} {L : Submodule K E}
    (h : ∀ e, i∈pairVertices e → A e≤L) : incidentSpan A i≤L := by
  apply Finset.sup_le
  intro e he
  exact h e (Finset.mem_filter.mp he).2

private instance certificate_instance_0516 : OAI.SidorenkoCounterexample.ProofCertificate_0516 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8
  exact @certificate_proof_0516 p0 p1 p2 p3 p4 p5 p6 q0 q1 q2 q3 q4 q5 q6 q7 q8

variable [FiniteDimensional K E]
theorem certificate_proof_0517 (h : Fin 33 → ℕ) (A : (e : Fin 33) → DimSubspace K E (h e)) (i : Fin 13) :
    finrank K (incidentSpan (fun e=>(A e).val) i)≤localPairDim h i := by
  unfold incidentSpan localPairDim
  calc _ ≤ ∑ e∈incidentPairs i, finrank K (A e).val := finrank_finset_sup_le _ _
       _ = _ := Finset.sum_congr rfl (fun e _ => (A e).property)

private instance certificate_instance_0517 : OAI.SidorenkoCounterexample.ProofCertificate_0517 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8
  exact @certificate_proof_0517 p0 p1 p2 p3 p4 p5 p6 q0 q1 q2 q3 q4 q5 q6 q7 q8

theorem certificate_proof_0518 (h : Fin 33 → ℕ) (A : (e : Fin 33) → DimSubspace K E (h e))
    (ha : iSupIndep (fun e=>(A e).val)) (i : Fin 13) :
    finrank K (incidentSpan (fun e=>(A e).val) i)=localPairDim h i := by
  unfold incidentSpan localPairDim
  calc _ = ∑ e∈incidentPairs i, finrank K (A e).val := finrank_finset_sup_direct _ _ ha
       _ = _ := Finset.sum_congr rfl (fun e _ => (A e).property)

private instance certificate_instance_0518 : OAI.SidorenkoCounterexample.ProofCertificate_0518 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9
  exact @certificate_proof_0518 p0 p1 p2 p3 p4 p5 p6 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9

omit [FiniteDimensional K E] in
theorem certificate_proof_0519 (A : Fin 33 → Submodule K E) (e : Fin 33) :
    extendPairSpace A (pairVertices e)=A e := pairVertices_injective.extend_apply _ _ _

private instance certificate_instance_0519 : OAI.SidorenkoCounterexample.ProofCertificate_0519 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6
  exact @certificate_proof_0519 p0 p1 p2 p3 p4 p5 p6 q0 q1 q2 q3 q4 q5 q6

omit [FiniteDimensional K E] in
theorem certificate_proof_0520 (A : Fin 33 → Submodule K E) :
    (Finset.univ.image pairVertices).sup (extendPairSpace A)=⨆ e,A e := by
  rw [Finset.sup_image]
  simp only [Function.comp_def,extendPairSpace_apply,Finset.sup_eq_iSup,Finset.mem_univ,iSup_pos]

private instance certificate_instance_0520 : OAI.SidorenkoCounterexample.ProofCertificate_0520 := by
  constructor
  intro q0 q1 q2 q3 q4 q5
  exact @certificate_proof_0520 p0 p1 p2 p3 p4 p5 p6 q0 q1 q2 q3 q4 q5

omit [FiniteDimensional K E] in
theorem certificate_proof_0521 (A : Fin 33 → Submodule K E) (i : Fin 13) :
    localSpan (Finset.univ.image pairVertices) (extendPairSpace A) i=incidentSpan A i := by
  unfold localSpan incidentSpan incidentPairs
  rw [Finset.filter_image,Finset.sup_image]
  simp only [Function.comp_def,extendPairSpace_apply]

private instance certificate_instance_0521 : OAI.SidorenkoCounterexample.ProofCertificate_0521 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6
  exact @certificate_proof_0521 p0 p1 p2 p3 p4 p5 p6 q0 q1 q2 q3 q4 q5 q6

theorem certificate_proof_0522 (A : Fin 33 → Submodule K E) (ha : ¬iSupIndep A) :
    2*finrank K ↥(⨆ e,A e)+1≤∑ i,finrank K (incidentSpan A i) := by
  have hn : ¬(Finset.univ.image pairVertices).SupIndep (extendPairSpace A) := by
    intro hs
    have hi := hs.independent
    have hj := hi.comp (f := fun e : Fin 33 => (⟨pairVertices e,Finset.mem_image.mpr ⟨e,Finset.mem_univ _,rfl⟩⟩ : ↥(Finset.univ.image pairVertices))) (by
      intro e f hef
      exact pairVertices_injective (congrArg Subtype.val hef))
    apply ha
    simpa only [Function.comp_def,extendPairSpace_apply] using hj
  have hb := strict_span_inequality (Finset.univ.image pairVertices) (extendPairSpace A)
    (by intro e he; obtain ⟨f,_,rfl⟩:=Finset.mem_image.mp he; exact pairVertices_card f) hn
  rw [extend_global_span] at hb
  have hs : (∑ i : Fin 13,finrank K (localSpan (Finset.univ.image pairVertices) (extendPairSpace A) i))=∑ i,finrank K (incidentSpan A i) :=
    Finset.sum_congr rfl (fun i _ => congrArg (fun S : Submodule K E => finrank K S) (extend_local_span A i))
  rw [hs] at hb
  exact hb

private instance certificate_instance_0522 : OAI.SidorenkoCounterexample.ProofCertificate_0522 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7
  exact @certificate_proof_0522 p0 p1 p2 p3 p4 p5 p6 q0 q1 q2 q3 q4 q5 q6 q7

end GraphSpans
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open scoped BigOperators
theorem certificate_proof_0523 (e : Fin 33) : pairRelated e e := by
  intro he
  have hb := disjoint_self.mp he
  have hc := pairVertices_card e
  rw [hb] at hc
  simp at hc

private instance certificate_instance_0523 : OAI.SidorenkoCounterexample.ProofCertificate_0523 := by
  constructor
  intro q0
  exact @certificate_proof_0523 p0 p1 p2 p3 p4 p5 p6 q0

theorem certificate_proof_0524 (h : Fin 33 → ℕ) :
    (Nat.card {p : (Σ e, Fin (h e))×(Σ e, Fin (h e)) // p.1≠p.2 ∧ pairRelated p.1.1 p.2.1}:ℝ)=
      (∑ e, ∑ f, if pairRelated e f then (h e:ℝ)*h f else 0)-∑ e,(h e:ℝ) := by
  classical
  rw [nat_card_subtype_sum,Nat.cast_sum,Fintype.sum_prod_type]
  have he (a b : Σ e, Fin (h e)) :
      (if a≠b ∧ pairRelated a.1 b.1 then (1:ℝ) else 0)=
        (if pairRelated a.1 b.1 then (1:ℝ) else 0)-(if a=b then 1 else 0) := by
    by_cases hab : a=b
    · subst b; simp [pairRelated_self]
    · by_cases hr : pairRelated a.1 b.1 <;> simp [hab,hr]
  simp only [Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  simp only [he,Finset.sum_sub_distrib]
  simp only [Finset.sum_ite_eq,Finset.mem_univ,ite_true,Finset.sum_const,Finset.card_univ,
    nsmul_eq_mul,mul_one,Fintype.card_sigma,Fintype.card_fin,Nat.cast_sum]
  congr 1
  simp_rw [Fintype.sum_sigma]
  simp [Finset.sum_const,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e _
  apply Finset.sum_congr rfl
  intro f _
  by_cases hr : pairRelated e f <;> simp [hr]

private instance certificate_instance_0524 : OAI.SidorenkoCounterexample.ProofCertificate_0524 := by
  constructor
  intro q0
  exact @certificate_proof_0524 p0 p1 p2 p3 p4 p5 p6 q0

theorem certificate_proof_0525 (f g : Fin 33 → ℝ) :
    (∑ i : Fin 13, (∑ e∈incidentPairs i,f e)*(∑ e∈incidentPairs i,g e))=
      ∑ e,∑ a, ((Finset.univ.filter (fun i=>e∈incidentPairs i ∧ a∈incidentPairs i)).card:ℝ)*f e*g a := by
  classical
  have hf (i : Fin 13) : (∑ e∈incidentPairs i,∑ a∈incidentPairs i,f e*g a)=
      ∑ e : Fin 33,∑ a : Fin 33, if e∈incidentPairs i ∧ a∈incidentPairs i then f e*g a else 0 := by
    symm
    simp only [ite_and]
    simp_rw [Finset.sum_ite_irrel,Finset.sum_ite_mem]
    simp only [Finset.sum_const_zero, Finset.sum_ite_mem, Finset.univ_inter]
  have hp (i : Fin 13) : (∑ e∈incidentPairs i,f e)*(∑ e∈incidentPairs i,g e)=
      ∑ e∈incidentPairs i,∑ a∈incidentPairs i,f e*g a := by
    rw [Finset.sum_mul]
    simp_rw [Finset.mul_sum]
  simp_rw [hp,hf]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  rw [←Finset.sum_filter,Finset.sum_const]
  simp only [nsmul_eq_mul,mul_assoc]

private instance certificate_instance_0525 : OAI.SidorenkoCounterexample.ProofCertificate_0525 := by
  constructor
  intro q0 q1
  exact @certificate_proof_0525 p0 p1 p2 p3 p4 p5 p6 q0 q1

theorem certificate_proof_0526 (h : Fin 33 → ℕ) :
    (∑ i : Fin 13,(localPairDim h i:ℝ)^2)=
      (∑ e,(h e:ℝ)^2)+(∑ e,∑ f,if pairRelated e f then (h e:ℝ)*h f else 0) := by
  classical
  have he : (∑ i : Fin 13,(localPairDim h i:ℝ)^2)=
      ∑ i : Fin 13,(∑ e∈incidentPairs i,(h e:ℝ))*(∑ e∈incidentPairs i,(h e:ℝ)) := by
    simp only [localPairDim,Nat.cast_sum,pow_two]
  rw [he,sum_local_products]
  have hp (e f : Fin 33) :
      ((Finset.univ.filter (fun i=>e∈incidentPairs i ∧ f∈incidentPairs i)).card:ℝ)*(h e:ℝ)*h f=
      (if e=f then (h e:ℝ)^2 else 0)+(if pairRelated e f then (h e:ℝ)*h f else 0) := by
    rw [pair_shared_card]
    by_cases hef : e=f
    · subst f; simp only [ite_true,pairRelated_self,Nat.cast_ofNat,pow_two]; ring
    · by_cases hr : pairRelated e f <;> simp [hef,hr]
  simp_rw [hp,Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq,Finset.mem_univ,ite_true]

private instance certificate_instance_0526 : OAI.SidorenkoCounterexample.ProofCertificate_0526 := by
  constructor
  intro q0
  exact @certificate_proof_0526 p0 p1 p2 p3 p4 p5 p6 q0

theorem certificate_proof_0527 (h : Fin 33 → ℕ) : (∑ i,(localPairDim h i:ℝ))=2*∑ e,(h e:ℝ) := by
  simpa only [localPairDim,Nat.cast_sum] using sum_incident (fun e=>(h e:ℝ))

private instance certificate_instance_0527 : OAI.SidorenkoCounterexample.ProofCertificate_0527 := by
  constructor
  intro q0
  exact @certificate_proof_0527 p0 p1 p2 p3 p4 p5 p6 q0

theorem certificate_proof_0528 (D : ℕ) (h : Fin 33 → ℕ) :
    2*(D:ℝ)*(∑ e,(h e:ℝ))-
      (Nat.card {p : (Σ e, Fin (h e))×(Σ e, Fin (h e)) // p.1≠p.2 ∧ pairRelated p.1.1 p.2.1}:ℝ)/2-
      (∑ e,(h e:ℝ)^2)+(∑ i : Fin 13, (-(D:ℝ)*localPairDim h i+(localPairDim h i:ℝ)*(localPairDim h i-1)/2))=
      -∑ e,triangular (h e) := by
  rw [related_label_count]
  have hl : (∑ i : Fin 13, (-(D:ℝ)*localPairDim h i+(localPairDim h i:ℝ)*(localPairDim h i-1)/2))=
      -(D:ℝ)*(∑ i,(localPairDim h i:ℝ))+((∑ i,(localPairDim h i:ℝ)^2)-(∑ i,(localPairDim h i:ℝ)))/2 := by
    simp only [mul_sub,mul_one,sub_div,←pow_two]
    simp only [Finset.sum_add_distrib,Finset.sum_sub_distrib,Finset.sum_div,Finset.mul_sum]
  rw [hl,sum_localPairDim,sum_local_squares]
  have ht : (∑ e,triangular (h e))=((∑ e,(h e:ℝ)^2)+(∑ e,(h e:ℝ)))/2 := by
    unfold triangular
    simp only [mul_add,mul_one,←pow_two]
    rw [←Finset.sum_div,Finset.sum_add_distrib]
  rw [ht]
  ring

private instance certificate_instance_0528 : OAI.SidorenkoCounterexample.ProofCertificate_0528 := by
  constructor
  intro q0 q1
  exact @certificate_proof_0528 p0 p1 p2 p3 p4 p5 p6 q0 q1

end SidorenkoCounterexample
namespace SidorenkoCounterexample
open scoped BigOperators
theorem certificate_proof_0529 : (∑ i : Fin 13,(2*(incidentPairs i).card).choose 2)=618 := by decide

private instance certificate_instance_0529 : OAI.SidorenkoCounterexample.ProofCertificate_0529 := by
  constructor
  exact @certificate_proof_0529 p0 p1 p2 p3 p4 p5 p6

theorem certificate_proof_0530 (ki : Fin 13 → ℕ) (hk : ∀ i,ki i≤2*(incidentPairs i).card) :
    (∑ i : Fin 13, (ki i:ℝ)*(ki i-1)/2)≤618 := by
  have hb : (∑ i : Fin 13,(ki i).choose 2)≤618 := by
    rw [←degree_choose_sum]
    exact Finset.sum_le_sum (fun i _=>Nat.choose_le_choose 2 (hk i))
  have hc : (∑ i : Fin 13, ((ki i).choose 2:ℝ))≤618 := by exact_mod_cast hb
  simpa only [Nat.cast_choose_two] using hc

private instance certificate_instance_0530 : OAI.SidorenkoCounterexample.ProofCertificate_0530 := by
  constructor
  intro q0 q1
  exact @certificate_proof_0530 p0 p1 p2 p3 p4 p5 p6 q0 q1

theorem certificate_proof_0531 (D k : ℕ) (h : Fin 33 → ℕ) (ki : Fin 13 → ℕ)
    (hh : ∀ e,h e=0 ∨ h e=2) (hk : ∀ i,ki i≤2*(incidentPairs i).card)
    (hs : 2*k+1≤∑ i,ki i) :
    (k:ℝ)*(2*D-k)+(∑ e,(h e:ℝ)*(k-h e))+
      (∑ i : Fin 13, (-(D:ℝ)*ki i+(ki i:ℝ)*(ki i-1)/2))≤-(D:ℝ)+1575 := by
  have hsq (e : Fin 33) : (h e:ℝ)^2=2*(h e:ℝ) := by rcases hh e with he|he <;> rw [he] <;> norm_num
  have hle (e : Fin 33) : (h e:ℝ)≤2 := by rcases hh e with he|he <;> rw [he] <;> norm_num
  have hb : (∑ e,(h e:ℝ))≤66 := by
    calc _ ≤ ∑ _e : Fin 33,(2:ℝ) := Finset.sum_le_sum (fun e _=>hle e)
         _ = _ := by norm_num
  have hn : 0≤∑ e,(h e:ℝ) := Finset.sum_nonneg (fun _ _=>Nat.cast_nonneg _)
  have hs' : 2*(k:ℝ)+1≤∑ i,(ki i:ℝ) := by exact_mod_cast hs
  have hc := local_choose_sum_bound ki hk
  have hh' : (∑ e,(h e:ℝ)*(k-h e))=(k:ℝ)*(∑ e,(h e:ℝ))-2*(∑ e,(h e:ℝ)) := by
    simp_rw [mul_sub,←pow_two,hsq]
    rw [Finset.sum_sub_distrib,←Finset.sum_mul,←Finset.mul_sum]
    ring
  have hg : (∑ i : Fin 13, (-(D:ℝ)*ki i+(ki i:ℝ)*(ki i-1)/2))=
      -(D:ℝ)*(∑ i,(ki i:ℝ))+(∑ i : Fin 13,(ki i:ℝ)*(ki i-1)/2) := by
    rw [Finset.sum_add_distrib,←Finset.mul_sum]
  rw [hh',hg]
  have hd := mul_nonneg (Nat.cast_nonneg D) (sub_nonneg.mpr hs')
  have hm := mul_nonneg hn (sub_nonneg.mpr hb)
  nlinarith [sq_nonneg ((k:ℝ)-(∑ e,(h e:ℝ))/2)]

private instance certificate_instance_0531 : OAI.SidorenkoCounterexample.ProofCertificate_0531 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6
  exact @certificate_proof_0531 p0 p1 p2 p3 p4 p5 p6 q0 q1 q2 q3 q4 q5 q6

end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
open scoped BigOperators
section Containment
variable {K E : Type} [Field K] [AddCommGroup E] [Module K E]
variable (ω : LinearMap.BilinForm K E)
theorem certificate_proof_0532 (L : Fin 13 → SymplecticLagrangian ω) (e : Fin 33) (i : Fin 13)
    (hi : i∈pairVertices e) : pairSpaces ω L e≤(L i).val := Finset.inf_le hi

private instance certificate_instance_0532 : OAI.SidorenkoCounterexample.ProofCertificate_0532 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9
  exact @certificate_proof_0532 p0 p1 p2 p3 p4 p5 p6 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9

theorem certificate_proof_0533 (L : Fin 13 → SymplecticLagrangian ω) (i : Fin 13) :
    incidentSpan (pairSpaces ω L) i≤(L i).val :=
  incidentSpan_le (fun e he=>pairSpaces_le ω L e i he)

private instance certificate_instance_0533 : OAI.SidorenkoCounterexample.ProofCertificate_0533 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7
  exact @certificate_proof_0533 p0 p1 p2 p3 p4 p5 p6 q0 q1 q2 q3 q4 q5 q6 q7

theorem certificate_proof_0534 (L : Fin 13 → SymplecticLagrangian ω) (e f : Fin 33)
    (hr : pairRelated e f) {x y : E} (hx : x∈pairSpaces ω L e) (hy : y∈pairSpaces ω L f) : ω x y=0 := by
  classical
  obtain ⟨i,he,hf⟩ := Finset.not_disjoint_iff.mp hr
  have hxi := pairSpaces_le ω L e i he hx
  have hyi := pairSpaces_le ω L f i hf hy
  have hyO : y∈ω.orthogonal (L i).val := (L i).property.symm ▸ hyi
  exact hyO x hxi

private instance certificate_instance_0534 : OAI.SidorenkoCounterexample.ProofCertificate_0534 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13
  exact @certificate_proof_0534 p0 p1 p2 p3 p4 p5 p6 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13

variable [Fintype K] [Finite E]
end Containment
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
open scoped BigOperators
section Nondirect
variable {K E : Type} [Field K] [AddCommGroup E] [Module K E]
variable (ω : LinearMap.BilinForm K E)
variable [Fintype K] [Finite E]
end Nondirect
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
open scoped BigOperators
section Actual
variable {K E : Type} [Field K] [AddCommGroup E] [Module K E] [Fintype K] [Finite E]
variable (ω : LinearMap.BilinForm K E)
end Actual
end SidorenkoCounterexample
end OAI

theorem solution : OAI.SidorenkoCounterexample.ProofCertificate_0496 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0497 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0498 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0499 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0500 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0501 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0502 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0503 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0504 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0505 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0506 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0507 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0508 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0509 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0510 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0511 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0512 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0513 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0514 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0515 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0516 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0517 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0518 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0519 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0520 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0521 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0522 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0523 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0524 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0525 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0526 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0527 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0528 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0529 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0530 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0531 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0532 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0533 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0534 := by
  exact ⟨inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance⟩
end

