-- Prove2me | solution 1 for HodgeComputer.HasCertificate.finite_linear_combination
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T15:08:52.765917+00:00
-- url     : https://prove2.me/submissions/178dd69e-6e7f-4914-8a0d-8d886283d9b0

import Definitions.Def_DiamondCertificate
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import Mathlib.RingTheory.MvPolynomial.EulerIdentity
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
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
namespace CertificateEulerAux
variable {n : ℕ}

def radial (H : AmbientPoly n) : Fin (n+1) → AmbientPoly n := fun i => H*X i

lemma directional_add (P : AmbientPoly n) (N M : Fin (n+1) → AmbientPoly n) :
    directional P (N+M)=directional P N+directional P M := by
  simp [directional, Pi.add_apply, mul_add, Finset.sum_add_distrib]

lemma divergence_add (N M : Fin (n+1) → AmbientPoly n) :
    divergence (N+M)=divergence N+divergence M := by
  simp [divergence, Pi.add_apply, map_add, Finset.sum_add_distrib]

lemma directional_radial (P H : AmbientPoly n) : directional P (radial H)=euler P*H := by
  simp only [directional,radial,euler,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  ring

lemma divergence_radial (H : AmbientPoly n) : divergence (radial H)=euler H+(n+1)*H := by
  simp only [divergence,radial,pderiv_mul,pderiv_X_self,mul_one,Finset.sum_add_distrib,
    Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_add,Nat.cast_one,euler]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  ring

lemma hom_const_mul {P : AmbientPoly n} {k : ℤ} (hP : Homogeneous P k) (c : ℂ) :
    Homogeneous (C c*P) k := by
  intro m hm
  rw [coeff_C_mul] at hm
  exact hP (right_ne_zero_of_mul hm)

lemma radial_defect (F A D H : AmbientPoly n) (d q : ℕ)
    (N : Fin (n+1) → AmbientPoly n) (hF : F.IsHomogeneous d)
    (hD : D.IsHomogeneous D.totalDegree)
    (hH : Homogeneous H ((D.totalDegree:ℤ)+d*q-n-1)) :
    defect F A D q (N+radial H)=defect F A D q N := by
  have hEF := (homogeneous_iff_euler F (d:ℤ)).mp (hom_of_nat hF)
  have hED := (homogeneous_iff_euler D (D.totalDegree:ℤ)).mp (hom_of_nat hD)
  have hEH := (homogeneous_iff_euler H _).mp hH
  simp only [defect,divergenceNumerator,directional_add,divergence_add,directional_radial,
    divergence_radial,hEF,hED,hEH]
  push_cast
  ring

end CertificateEulerAux
end

section
set_option backward.isDefEq.respectTransparency true

/-!
Certificate addition follows the construction in hodge-computer's Apache-2.0
CertificateOperations.lean, commit 2d60d08d25fba3e02162b39d4c50f6b467e7f506.
That source credits fqlx's holdout-bundle construction (PR #161) and the
accepted one-reflection addition formula. Adapted to the canonical Prove2Me
definition, whose HasCertificate retains the explicit hypersurface degree.
-/

open HodgeComputer MvPolynomial CertificateEulerAux
open scoped BigOperators
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace CertificateOperationsAux
variable {n d q : ℕ}

lemma directional_mul (P H : AmbientPoly n) (N : Fin (n+1) → AmbientPoly n) :
    directional P (fun i => H*N i) = H*directional P N := by
  simp only [directional,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

lemma divergence_mul (H : AmbientPoly n) (N : Fin (n+1) → AmbientPoly n) :
    divergence (fun i => H*N i) = directional H N+H*divergence N := by
  simp only [divergence,pderiv_mul,Finset.sum_add_distrib,directional,Finset.mul_sum]

lemma divergenceNumerator_mul (D H : AmbientPoly n) (N : Fin (n+1) → AmbientPoly n) :
    divergenceNumerator (H*D) (fun i => H*N i) = H^2*divergenceNumerator D N := by
  have hd : directional (H*D) N = D*directional H N+H*directional D N := by
    simp only [directional,pderiv_mul,add_mul,Finset.sum_add_distrib,Finset.mul_sum]
    congr 1 <;> apply Finset.sum_congr rfl <;> intro i _ <;> ring
  simp only [divergenceNumerator,divergence_mul,directional_mul,hd]
  ring

lemma defect_scale_denominator (F A D H : AmbientPoly n) (q : ℕ)
    (N : Fin (n+1) → AmbientPoly n) :
    defect F A (H*D) q (fun i => H*N i) = H^2*defect F A D q N := by
  simp only [defect,directional_mul,divergenceNumerator_mul]
  ring

lemma defect_add_same (F A B D : AmbientPoly n) (q : ℕ)
    (N M : Fin (n+1) → AmbientPoly n) :
    defect F (A+B) D q (N+M) = defect F A D q N+defect F B D q M := by
  simp only [defect,divergenceNumerator,directional_add,divergence_add]
  ring

lemma verify_add {F A B D E Q R : AmbientPoly n} {N M : Fin (n+1) → AmbientPoly n}
    (h : Verify F A d q D N Q) (k : Verify F B d q E M R) :
    Verify F (A+B) d q (D*E) (fun i => E*N i+D*M i) (E^2*Q+D^2*R) := by
  refine {
    hypersurface_ne_zero := h.hypersurface_ne_zero
    hypersurface_homogeneous := h.hypersurface_homogeneous
    source_homogeneous := hom_add h.source_homogeneous k.source_homogeneous
    denominator_ne_zero := mul_ne_zero h.denominator_ne_zero k.denominator_ne_zero
    denominator_homogeneous := ?_
    numerator_homogeneous := ?_
    denominator_legal := h.denominator_legal.mul_right k.denominator_legal
    identity := ?_ }
  · rw [totalDegree_mul_of_isDomain h.denominator_ne_zero k.denominator_ne_zero]
    exact h.denominator_homogeneous.mul k.denominator_homogeneous
  · intro i
    have hn := hom_mul (hom_of_nat k.denominator_homogeneous) (h.numerator_homogeneous i)
    have hm := hom_mul (hom_of_nat h.denominator_homogeneous) (k.numerator_homogeneous i)
    rw [totalDegree_mul_of_isDomain h.denominator_ne_zero k.denominator_ne_zero,Nat.cast_add]
    apply hom_add
    · convert hn using 1 <;> ring
    · convert hm using 1 <;> ring
  · change defect F (A+B) (D*E) q
      ((fun i => E*N i)+(fun i => D*M i)) = _
    rw [defect_add_same]
    have hleft : defect F A (D*E) q (fun i => E*N i) = E^2*defect F A D q N := by
      rw [mul_comm D E]
      exact defect_scale_denominator F A D E q N
    rw [hleft,defect_scale_denominator,h.identity,k.identity]
    ring

lemma verify_const_mul {F A D Q : AmbientPoly n} {N : Fin (n+1) → AmbientPoly n}
    (h : Verify F A d q D N Q) (c : ℂ) :
    Verify F (C c*A) d q D (fun i => C c*N i) (C c*Q) := by
  refine {
    hypersurface_ne_zero := h.hypersurface_ne_zero
    hypersurface_homogeneous := h.hypersurface_homogeneous
    source_homogeneous := hom_const_mul h.source_homogeneous c
    denominator_ne_zero := h.denominator_ne_zero
    denominator_homogeneous := h.denominator_homogeneous
    numerator_homogeneous := fun i => hom_const_mul (h.numerator_homogeneous i) c
    denominator_legal := h.denominator_legal
    identity := ?_ }
  have hv : divergence (fun i => C c*N i) = C c*divergence N := by
    simp [divergence,pderiv_C_mul,Finset.mul_sum]
  have he : defect F (C c*A) D q (fun i => C c*N i) = C c*defect F A D q N := by
    simp only [defect,divergenceNumerator,directional_mul,hv]
    ring
  rw [he,h.identity]
  ring

lemma has_add {F A B : AmbientPoly n}
    (h : HasCertificate F A d q) (k : HasCertificate F B d q) : HasCertificate F (A+B) d q := by
  obtain ⟨D,N,Q,h⟩ := h
  obtain ⟨E,M,R,k⟩ := k
  exact ⟨D*E,(fun i => E*N i+D*M i),E^2*Q+D^2*R,verify_add h k⟩

lemma has_const_mul {F A : AmbientPoly n} (h : HasCertificate F A d q) (c : ℂ) :
    HasCertificate F (C c*A) d q := by
  obtain ⟨D,N,Q,h⟩ := h
  exact ⟨D,(fun i => C c*N i),C c*Q,verify_const_mul h c⟩

lemma has_zero (F : AmbientPoly n) (hF : F ≠ 0) (hd : F.IsHomogeneous d) (q : ℕ) :
    HasCertificate F 0 d q := by
  refine ⟨1,(fun _ => 0),0,?_⟩
  exact {
    hypersurface_ne_zero := hF
    hypersurface_homogeneous := hd
    source_homogeneous := by intro m hm;simp at hm
    denominator_ne_zero := one_ne_zero
    denominator_homogeneous := by simpa using isHomogeneous_one (Fin (n+1)) ℂ
    numerator_homogeneous := by intro i m hm;simp at hm
    denominator_legal := isRelPrime_one_right
    identity := by simp [defect,directional,divergenceNumerator,divergence] }

lemma finite_linear_combination {ι : Type*} [Fintype ι] (F : AmbientPoly n)
    (hF : F ≠ 0) (hd : F.IsHomogeneous d) (A : ι → AmbientPoly n) (c : ι → ℂ)
    (h : ∀ i, HasCertificate F (A i) d q) :
    HasCertificate F (∑ i, C (c i)*A i) d q := by
  classical
  have hs (S : Finset ι) : HasCertificate F (∑ i ∈ S, C (c i)*A i) d q := by
    induction S using Finset.induction_on with
    | empty => simpa using has_zero F hF hd q
    | @insert i S hi ih =>
      simpa only [Finset.sum_insert hi] using has_add (has_const_mul (h i) (c i)) ih
  simpa using hs Finset.univ

end CertificateOperationsAux
end

universe u
theorem solution {n d q : ℕ} {ι : Type u} [Fintype ι]
    (F : HodgeComputer.AmbientPoly n) (hF : F ≠ 0) (hd : F.IsHomogeneous d)
    (A : ι → HodgeComputer.AmbientPoly n) (c : ι → ℂ)
    (h : ∀ i, HodgeComputer.HasCertificate F (A i) d q) :
    HodgeComputer.HasCertificate F (∑ i, MvPolynomial.C (c i)*A i) d q :=
  CertificateOperationsAux.finite_linear_combination F hF hd A c h

#print axioms solution
