-- Prove2me | solution 1 for HodgeComputer.Verify.pole_reduction_transport
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T15:31:15.933943+00:00
-- url     : https://prove2.me/submissions/f322f500-0262-4098-b227-587b916a0805

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


end CertificateOperationsAux

end

section
set_option backward.isDefEq.respectTransparency true

open HodgeComputer MvPolynomial CertificateEulerAux CertificateOperationsAux
open scoped BigOperators
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace CertificatePoleReductionAux
variable {n d q : ℕ}

lemma directional_homogeneous {F : AmbientPoly n} (hF : F.IsHomogeneous d)
    (B : Fin (n+1) → AmbientPoly n) {k : ℤ} (hB : ∀ i, Homogeneous (B i) k) :
    Homogeneous (directional F B) ((d : ℤ)-1+k) := by
  exact hom_sum _ _ (fun i => hom_mul (hom_pderiv (hom_of_nat hF) i) (hB i))

lemma divergence_homogeneous (B : Fin (n+1) → AmbientPoly n) {k : ℤ}
    (hB : ∀ i, Homogeneous (B i) k) : Homogeneous (divergence B) (k-1) := by
  exact hom_sum _ _ (fun i => hom_pderiv (hB i) i)

def exactSource (F : AmbientPoly n) (q : ℕ) (B : Fin (n+1) → AmbientPoly n) :
    AmbientPoly n := (q : AmbientPoly n)*directional F B-F*divergence B

lemma exactSource_homogeneous {F : AmbientPoly n} (hF : F.IsHomogeneous d)
    (B : Fin (n+1) → AmbientPoly n)
    (hB : ∀ i, Homogeneous (B i) ((d : ℤ)*q-n)) :
    Homogeneous (exactSource F q B) ((d : ℤ)*(q+1)-(n+1)) := by
  apply hom_sub
  · have hh := hom_const_mul (directional_homogeneous hF B hB) (q : ℂ)
    simp only [map_natCast] at hh
    convert hh using 1 <;> ring
  · convert hom_mul (hom_of_nat hF) (divergence_homogeneous B hB) using 1 <;> ring

lemma exactSource_certificate {F : AmbientPoly n} (hF0 : F ≠ 0)
    (hF : F.IsHomogeneous d) (B : Fin (n+1) → AmbientPoly n)
    (hB : ∀ i, Homogeneous (B i) ((d : ℤ)*q-n)) :
    Verify F (exactSource F q B) d q 1 B 0 := by
  refine {
    hypersurface_ne_zero := hF0
    hypersurface_homogeneous := hF
    source_homogeneous := exactSource_homogeneous hF B hB
    denominator_ne_zero := one_ne_zero
    denominator_homogeneous := by simpa using isHomogeneous_one (Fin (n+1)) ℂ
    numerator_homogeneous := by simpa using hB
    denominator_legal := isRelPrime_one_right
    identity := ?_ }
  simp [defect,exactSource,divergenceNumerator,directional]

lemma defect_pole_lift (F A D : AmbientPoly n) (q : ℕ)
    (N B : Fin (n+1) → AmbientPoly n) :
    defect F (F*A+exactSource F (q+1) B) D (q+1)
      (fun i => D*B i+F*N i) = F*defect F A D q N := by
  change defect F (F*A+exactSource F (q+1) B) D (q+1)
    ((fun i => D*B i)+(fun i => F*N i)) = _
  simp only [defect,exactSource,divergenceNumerator,directional_add,divergence_add,
    directional_mul,divergence_mul,Nat.cast_add,Nat.cast_one]
  ring

lemma verify_pole_lift {F A D Q : AmbientPoly n}
    {N : Fin (n+1) → AmbientPoly n} (h : Verify F A d q D N Q)
    (B : Fin (n+1) → AmbientPoly n)
    (hB : ∀ i, Homogeneous (B i) ((d : ℤ)*(q+1)-n)) :
    Verify F (F*A+exactSource F (q+1) B) d (q+1) D
      (fun i => D*B i+F*N i) Q := by
  refine {
    hypersurface_ne_zero := h.hypersurface_ne_zero
    hypersurface_homogeneous := h.hypersurface_homogeneous
    source_homogeneous := ?_
    denominator_ne_zero := h.denominator_ne_zero
    denominator_homogeneous := h.denominator_homogeneous
    numerator_homogeneous := ?_
    denominator_legal := h.denominator_legal
    identity := ?_ }
  · apply hom_add
    · convert hom_mul (hom_of_nat h.hypersurface_homogeneous) h.source_homogeneous
        using 1 <;> push_cast <;> ring
    · exact exactSource_homogeneous h.hypersurface_homogeneous B hB
  · intro i
    apply hom_add
    · convert hom_mul (hom_of_nat h.denominator_homogeneous) (hB i) using 1 <;>
        push_cast <;> ring
    · convert hom_mul (hom_of_nat h.hypersurface_homogeneous) (h.numerator_homogeneous i)
        using 1 <;> push_cast <;> ring
  · rw [defect_pole_lift,h.identity,pow_succ F (q+1)]
    ring


end CertificatePoleReductionAux

end

theorem solution {n d q : ℕ}
    {F A D Q : HodgeComputer.AmbientPoly n}
    {N : Fin (n+1) → HodgeComputer.AmbientPoly n}
    (h : HodgeComputer.Verify F A d q D N Q)
    (B : Fin (n+1) → HodgeComputer.AmbientPoly n)
    (hB : ∀ i, HodgeComputer.Homogeneous (B i) ((d : ℤ)*(q+1)-n)) :
    HodgeComputer.Verify F
      (F*A+(q+1 : HodgeComputer.AmbientPoly n)*HodgeComputer.directional F B
        -F*HodgeComputer.divergence B) d (q+1) D
      (fun i => D*B i+F*N i) Q := by
  convert CertificatePoleReductionAux.verify_pole_lift h B hB using 1 <;>
    simp only [CertificatePoleReductionAux.exactSource,Nat.cast_add,Nat.cast_one] <;> ring

#print axioms solution
