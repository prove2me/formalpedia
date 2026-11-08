-- Prove2me | solution 1 for HodgeComputer.Verify.linear_coordinate_transport
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T15:26:00.158399+00:00
-- url     : https://prove2.me/submissions/1ef5ec63-1279-475b-8481-84a9301057d1

import Definitions.Def_DiamondCertificate
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import Mathlib.RingTheory.MvPolynomial.EulerIdentity
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.LinearCombination
open scoped BigOperators

noncomputable section
set_option autoImplicit false

section
set_option backward.isDefEq.respectTransparency true

open HodgeComputer MvPolynomial
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
namespace CertificateEulerAux
variable {n : ℕ}

def euler (P : AmbientPoly n) : AmbientPoly n := ∑ i, X i * pderiv i P

lemma euler_add (P Q : AmbientPoly n) : euler (P+Q)=euler P+euler Q := by
  simp [euler, map_add, mul_add, Finset.sum_add_distrib]

lemma euler_mul (P Q : AmbientPoly n) : euler (P*Q)=euler P*Q+P*euler Q := by
  simp only [euler,pderiv_mul,mul_add,Finset.sum_add_distrib,Finset.sum_mul,Finset.mul_sum]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro i hi <;> ring

lemma euler_coeff (P : AmbientPoly n) (m : Fin (n+1) →₀ ℕ) :
    coeff m (euler P) = (m.degree:ℂ)*coeff m P := by
  classical
  induction P using MvPolynomial.induction_on' with
  | add P Q hP hQ => simp only [euler_add, coeff_add, hP, hQ, mul_add]
  | monomial s a =>
    have h := (isHomogeneous_monomial a (rfl : s.degree=s.degree)).sum_X_mul_pderiv
    change coeff m (euler (monomial s a)) = _
    rw [show euler (monomial s a) = s.degree • monomial s a from h]
    rw [← Nat.cast_smul_eq_nsmul ℂ, coeff_smul]
    simp only [smul_eq_mul, coeff_monomial]
    split_ifs with hsm
    · subst s; rfl
    · simp

lemma homogeneous_iff_euler (P : AmbientPoly n) (k : ℤ) :
    Homogeneous P k ↔ euler P=(k:AmbientPoly n)*P := by
  constructor
  · intro h
    ext m
    rw [euler_coeff, show (k:AmbientPoly n)=C (k:ℂ) by simp, coeff_C_mul]
    by_cases hm : coeff m P=0
    · simp [hm]
    have he : (m.degree:ℂ)=(k:ℂ) := by exact_mod_cast h hm
    rw [he]
  · intro h m hm
    have hh := congrArg (coeff m) h
    rw [euler_coeff, show (k:AmbientPoly n)=C (k:ℂ) by simp, coeff_C_mul] at hh
    have he := mul_right_cancel₀ hm hh
    exact_mod_cast he

lemma hom_of_nat {P : AmbientPoly n} {k : ℕ} (h : P.IsHomogeneous k) : Homogeneous P (k:ℤ) := by
  intro m hm
  have he : m.degree=k := by simpa only [Finsupp.degree_eq_weight_one, Pi.one_def] using h hm
  exact_mod_cast he

lemma hom_add {P Q : AmbientPoly n} {k : ℤ} (hP : Homogeneous P k) (hQ : Homogeneous Q k) :
    Homogeneous (P+Q) k := by
  apply (homogeneous_iff_euler _ _).mpr
  rw [euler_add, (homogeneous_iff_euler _ _).mp hP, (homogeneous_iff_euler _ _).mp hQ]
  ring

lemma hom_sub {P Q : AmbientPoly n} {k : ℤ} (hP : Homogeneous P k) (hQ : Homogeneous Q k) :
    Homogeneous (P-Q) k := by
  intro m hm
  have hh : coeff m P≠0 ∨ coeff m Q≠0 := by
    by_contra! hh
    simp [coeff_sub,hh.1,hh.2] at hm
  exact hh.elim (fun h => hP h) (fun h => hQ h)

lemma hom_mul {P Q : AmbientPoly n} {a b : ℤ} (hP : Homogeneous P a) (hQ : Homogeneous Q b) :
    Homogeneous (P*Q) (a+b) := by
  apply (homogeneous_iff_euler _ _).mpr
  rw [euler_mul, (homogeneous_iff_euler _ _).mp hP, (homogeneous_iff_euler _ _).mp hQ]
  push_cast
  ring

lemma hom_sum {ι : Type*} [Fintype ι] (P : ι → AmbientPoly n) (k : ℤ)
    (h : ∀ i, Homogeneous (P i) k) : Homogeneous (∑ i, P i) k := by
  apply (homogeneous_iff_euler _ _).mpr
  simp only [euler,map_sum,Finset.mul_sum]
  rw [Finset.sum_comm]
  change (∑ i, euler (P i)) = _
  apply Finset.sum_congr rfl
  intro i hi
  exact (homogeneous_iff_euler _ _).mp (h i)

lemma hom_pderiv {P : AmbientPoly n} {k : ℤ} (hP : Homogeneous P k) (i : Fin (n+1)) :
    Homogeneous (pderiv i P) (k-1) := by
  intro m hm
  rw [coeff_pderiv] at hm
  have hh := hP (left_ne_zero_of_mul hm)
  simp only [map_add,Finsupp.degree_single,Nat.cast_add,Nat.cast_one] at hh
  omega

lemma hom_mul_cancel {P Q : AmbientPoly n} {a b : ℤ} (hP : Homogeneous P a)
    (hPQ : Homogeneous (P*Q) b) (hP0 : P≠0) : Homogeneous Q (b-a) := by
  apply (homogeneous_iff_euler _ _).mpr
  have h := (homogeneous_iff_euler _ _).mp hPQ
  rw [euler_mul, (homogeneous_iff_euler _ _).mp hP] at h
  have he : P*(euler Q-((b-a:ℤ):AmbientPoly n)*Q)=0 := by
    push_cast
    linear_combination h
  exact sub_eq_zero.mp ((mul_eq_zero.mp he).resolve_left hP0)

end CertificateEulerAux
end

section
set_option backward.isDefEq.respectTransparency true
open HodgeComputer MvPolynomial
namespace CertificateEulerAux
variable {n : ℕ}
lemma hom_const_mul {P : AmbientPoly n} {k : ℤ} (hP : Homogeneous P k) (c : ℂ) :
    Homogeneous (C c*P) k := by
  intro m hm
  rw [coeff_C_mul] at hm
  exact hP (right_ne_zero_of_mul hm)


end CertificateEulerAux

end

section
set_option backward.isDefEq.respectTransparency true
open HodgeComputer MvPolynomial
namespace CertificateCoordinateAux
variable {n : ℕ}
lemma hom_zero (k : ℤ) : Homogeneous (0 : AmbientPoly n) k := by
  intro m hm
  simp at hm

lemma hom_to_nat {P : AmbientPoly n} {k : ℤ} (h : Homogeneous P k) (hk : 0 ≤ k) :
    P.IsHomogeneous k.toNat := by
  intro m hm
  have he : m.degree = k.toNat := by
    have hh : (m.degree : ℤ) = (k.toNat : ℤ) := (h hm).trans (Int.toNat_of_nonneg hk).symm
    exact_mod_cast hh
  simpa only [Finsupp.degree_eq_weight_one,Pi.one_def] using he

lemma hom_eq_zero_of_neg {P : AmbientPoly n} {k : ℤ}
    (h : Homogeneous P k) (hk : k < 0) : P = 0 := by
  ext m
  by_contra hm
  have hm' : coeff m P ≠ 0 := by simpa using hm
  have he := h hm'
  omega


end CertificateCoordinateAux

end

section
set_option backward.isDefEq.respectTransparency true

open HodgeComputer MvPolynomial Matrix CertificateEulerAux CertificateCoordinateAux
open scoped BigOperators
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace PolynomialLinearSubstitutionAux
variable {n : ℕ}
abbrev Mat (n : ℕ) := Matrix (Fin (n+1)) (Fin (n+1)) ℂ

def linear (B : Mat n) (i : Fin (n+1)) : AmbientPoly n := ∑ j, C (B i j)*X j

def substPoly (B : Mat n) : AmbientPoly n →+* AmbientPoly n :=
  eval₂Hom C (linear B)

@[simp] lemma subst_C (B : Mat n) (c : ℂ) : substPoly B (C c) = C c := by simp [substPoly]
@[simp] lemma subst_X (B : Mat n) (i : Fin (n+1)) : substPoly B (X i) = linear B i := by
  simp [substPoly]

lemma subst_comp (B C' : Mat n) :
    (substPoly B).comp (substPoly C') = substPoly (C'*B) := by
  apply MvPolynomial.ringHom_ext
  · intro c
    simp
  · intro i
    simp only [RingHom.comp_apply,subst_X,linear,map_sum,map_mul,subst_C]
    simp only [subst_X,linear,Matrix.mul_apply,map_sum,map_mul,Finset.mul_sum,Finset.sum_mul]
    rw [Finset.sum_comm]
    simp only [mul_assoc]

lemma subst_one : substPoly (1 : Mat n) = RingHom.id (AmbientPoly n) := by
  apply MvPolynomial.ringHom_ext
  · intro c
    simp
  · intro i
    simp [linear,Matrix.one_apply]

lemma subst_inverse (B C' : Mat n) (h : C'*B=1) (P : AmbientPoly n) :
    substPoly B (substPoly C' P) = P := by
  change ((substPoly B).comp (substPoly C')) P = P
  rw [subst_comp,h,subst_one]
  rfl

lemma pderiv_linear (B : Mat n) (i j : Fin (n+1)) :
    pderiv j (linear B i) = C (B i j) := by
  simp [linear,pderiv_X,Pi.single_apply]

lemma pderiv_subst (B : Mat n) (j : Fin (n+1)) (P : AmbientPoly n) :
    pderiv j (substPoly B P) = ∑ i, C (B i j)*substPoly B (pderiv i P) := by
  induction P using MvPolynomial.induction_on with
  | C c => simp
  | add P Q hP hQ => simp [hP,hQ,mul_add,Finset.sum_add_distrib]
  | mul_X P k hP =>
    rw [map_mul,pderiv_mul,hP,subst_X,pderiv_linear]
    have hi (i : Fin (n+1)) : substPoly B (pderiv i (P*X k)) =
        substPoly B (pderiv i P)*linear B k + if i=k then substPoly B P else 0 := by
      by_cases hik : k=i
      · subst i
        simp [pderiv_X,Pi.single_apply,add_comm,mul_comm]
      · have hki : i ≠ k := Ne.symm hik
        simp [pderiv_X,Pi.single_apply,hik,hki,add_comm,mul_comm]
    simp_rw [hi]
    simp only [mul_add,Finset.sum_add_distrib,mul_ite,mul_zero,
      Finset.sum_ite_eq',Finset.mem_univ,if_true]
    rw [Finset.sum_mul]
    apply congrArg₂ (·+·)
    · apply Finset.sum_congr rfl
      intro i _
      ring
    · ring

end PolynomialLinearSubstitutionAux
end

section
set_option backward.isDefEq.respectTransparency true

open HodgeComputer MvPolynomial Matrix
open scoped BigOperators
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace PolynomialLinearSubstitutionAux
variable {n : ℕ}

def coeffMatrix (B : Mat n) : Matrix (Fin (n+1)) (Fin (n+1)) (AmbientPoly n) :=
  B.map (C : ℂ →+* AmbientPoly n)

lemma coeffMatrix_mul (B C' : Mat n) : coeffMatrix (B*C') = coeffMatrix B*coeffMatrix C' := by
  exact Matrix.map_mul

lemma coeffMatrix_one : coeffMatrix (1 : Mat n) = 1 := by
  ext i j
  simp [coeffMatrix,Matrix.one_apply]

def field (B C' : Mat n) (N : Fin (n+1) → AmbientPoly n) : Fin (n+1) → AmbientPoly n :=
  coeffMatrix C' *ᵥ (fun i => substPoly B (N i))

def jac (N : Fin (n+1) → AmbientPoly n) : Matrix (Fin (n+1)) (Fin (n+1)) (AmbientPoly n) :=
  fun i j => pderiv j (N i)

lemma pderiv_subst_vec (B : Mat n) (P : AmbientPoly n) :
    (fun j => pderiv j (substPoly B P)) =
      (fun i => substPoly B (pderiv i P)) ᵥ* coeffMatrix B := by
  funext j
  rw [pderiv_subst]
  change (∑ i, C (B i j)*substPoly B (pderiv i P)) =
    ∑ i, substPoly B (pderiv i P)*C (B i j)
  apply Finset.sum_congr rfl
  intro i _
  ring

lemma directional_chain (B : Mat n) (P : AmbientPoly n) (N : Fin (n+1) → AmbientPoly n) :
    directional (substPoly B P) N =
      (fun i => substPoly B (pderiv i P)) ⬝ᵥ (coeffMatrix B *ᵥ N) := by
  change (fun j => pderiv j (substPoly B P)) ⬝ᵥ N = _
  rw [pderiv_subst_vec,← Matrix.dotProduct_mulVec]

lemma directional_field (B C' : Mat n) (hBC : B*C'=1)
    (P : AmbientPoly n) (N : Fin (n+1) → AmbientPoly n) :
    directional (substPoly B P) (field B C' N) = substPoly B (directional P N) := by
  rw [directional_chain]
  unfold field
  rw [Matrix.mulVec_mulVec,← coeffMatrix_mul,hBC,coeffMatrix_one,Matrix.one_mulVec]
  simp only [dotProduct,directional,map_sum,map_mul]

lemma jac_field (B C' : Mat n) (N : Fin (n+1) → AmbientPoly n) :
    jac (field B C' N) = coeffMatrix C' * (jac N).map (substPoly B) * coeffMatrix B := by
  funext i j
  simp only [jac,field,Matrix.mulVec,dotProduct,coeffMatrix,Matrix.map_apply,
    map_sum,pderiv_C_mul,pderiv_subst,Matrix.mul_apply,Finset.mul_sum,Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  ring

lemma divergence_field (B C' : Mat n) (hBC : B*C'=1) (N : Fin (n+1) → AmbientPoly n) :
    divergence (field B C' N) = substPoly B (divergence N) := by
  change Matrix.trace (jac (field B C' N)) = _
  rw [jac_field,Matrix.trace_mul_cycle,← coeffMatrix_mul,hBC,coeffMatrix_one,one_mul]
  simp [Matrix.trace,jac,divergence]

lemma defect_field (B C' : Mat n) (hBC : B*C'=1) (F A D : AmbientPoly n) (q : ℕ)
    (N : Fin (n+1) → AmbientPoly n) :
    defect (substPoly B F) (substPoly B A) (substPoly B D) q (field B C' N) =
      substPoly B (defect F A D q N) := by
  simp only [defect,divergenceNumerator,directional_field B C' hBC,
    divergence_field B C' hBC,map_sub,map_add,map_mul,map_pow,map_natCast]

end PolynomialLinearSubstitutionAux
end

section
set_option backward.isDefEq.respectTransparency true

open HodgeComputer MvPolynomial Matrix CertificateEulerAux CertificateCoordinateAux
open scoped BigOperators
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace PolynomialLinearSubstitutionAux
variable {n : ℕ}

lemma linear_homogeneous (B : Mat n) (i : Fin (n+1)) : (linear B i).IsHomogeneous 1 := by
  exact IsHomogeneous.sum Finset.univ (fun j => C (B i j)*X j) 1
    (fun j _ => isHomogeneous_C_mul_X (B i j) j)

lemma subst_homogeneous (B : Mat n) {P : AmbientPoly n} {d : ℕ} (h : P.IsHomogeneous d) :
    (substPoly B P).IsHomogeneous d := by
  simpa only [substPoly,coe_eval₂Hom,one_mul] using
    h.eval₂ C (linear B) (fun c => isHomogeneous_C (Fin (n+1)) c) (linear_homogeneous B)

lemma subst_graded (B : Mat n) {P : AmbientPoly n} {k : ℤ} (h : Homogeneous P k) :
    Homogeneous (substPoly B P) k := by
  by_cases hk : 0 ≤ k
  · simpa only [Int.toNat_of_nonneg hk] using
      hom_of_nat (subst_homogeneous B (hom_to_nat h hk))
  · rw [hom_eq_zero_of_neg h (by omega),map_zero]
    exact hom_zero k

lemma subst_injective (B C' : Mat n) (hBC : B*C'=1) : Function.Injective (substPoly B) := by
  intro P Q h
  have he := congrArg (substPoly C') h
  simpa only [subst_inverse C' B hBC] using he

lemma subst_ne_zero (B C' : Mat n) (hBC : B*C'=1) {P : AmbientPoly n} (hP : P ≠ 0) :
    substPoly B P ≠ 0 := by
  intro h
  apply hP
  apply subst_injective B C' hBC
  simpa using h

lemma verify_linear_transport (B C' : Mat n) (hBC : B*C'=1) (hCB : C'*B=1)
    {F A D Q : AmbientPoly n} {d q : ℕ} {N : Fin (n+1) → AmbientPoly n}
    (h : Verify F A d q D N Q) :
    Verify (substPoly B F) (substPoly B A) d q (substPoly B D)
      (field B C' N) (substPoly B Q) := by
  have hD0 := subst_ne_zero B C' hBC h.denominator_ne_zero
  have hdeg := (subst_homogeneous B h.denominator_homogeneous).totalDegree hD0
  refine {
    hypersurface_ne_zero := subst_ne_zero B C' hBC h.hypersurface_ne_zero
    hypersurface_homogeneous := subst_homogeneous B h.hypersurface_homogeneous
    source_homogeneous := subst_graded B h.source_homogeneous
    denominator_ne_zero := hD0
    denominator_homogeneous := ?_
    numerator_homogeneous := ?_
    denominator_legal := ?_
    identity := ?_ }
  · rw [hdeg]
    exact subst_homogeneous B h.denominator_homogeneous
  · intro i
    rw [hdeg]
    change Homogeneous (∑ j, C (C' i j)*substPoly B (N j)) _
    apply hom_sum
    intro j
    exact hom_const_mul (subst_graded B (h.numerator_homogeneous j)) (C' i j)
  · intro P hP hPD
    have h1 : substPoly C' P ∣ F := by
      simpa only [subst_inverse C' B hBC] using map_dvd (substPoly C') hP
    have h2 : substPoly C' P ∣ D := by
      simpa only [subst_inverse C' B hBC] using map_dvd (substPoly C') hPD
    have hu := (h.denominator_legal h1 h2).map (substPoly B)
    simpa only [subst_inverse B C' hCB] using hu
  · rw [defect_field B C' hBC,h.identity,map_mul,map_pow]

end PolynomialLinearSubstitutionAux
end

theorem solution {n d q : ℕ}
    (B R : Matrix (Fin (n+1)) (Fin (n+1)) ℂ) (hBR : B*R=1) (hRB : R*B=1)
    {F A D Q : HodgeComputer.AmbientPoly n}
    {N : Fin (n+1) → HodgeComputer.AmbientPoly n}
    (h : HodgeComputer.Verify F A d q D N Q) :
    let T : HodgeComputer.AmbientPoly n →+* HodgeComputer.AmbientPoly n :=
      MvPolynomial.eval₂Hom MvPolynomial.C
        (fun i : Fin (n+1) => ∑ j, MvPolynomial.C (B i j)*MvPolynomial.X j)
    HodgeComputer.Verify (T F) (T A) d q (T D)
      (fun i => ∑ j, MvPolynomial.C (R i j)*T (N j)) (T Q) := by
  exact PolynomialLinearSubstitutionAux.verify_linear_transport B R hBR hRB h

#print axioms solution
