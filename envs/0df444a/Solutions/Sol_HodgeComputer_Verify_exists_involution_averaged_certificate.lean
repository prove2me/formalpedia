-- Prove2me | solution 1 for HodgeComputer.Verify.exists_involution_averaged_certificate
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T15:52:22.198102+00:00
-- url     : https://prove2.me/submissions/5c158d68-b5f9-4e7a-92ee-3d20fef93f30

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


end CertificateOperationsAux

end

section
set_option backward.isDefEq.respectTransparency true

/-!
Coordinate changes for certificate constructions. The sign-involution formulas
come from `fqlx`'s one-reflection proof (#123); permutation transport comes from
`benediamond`'s cyclic-triple-fano proof (#153). Both now apply in every ambient
dimension. The field components transform as well as the polynomials.
-/
/- Adapted from the Apache-2.0 hodge-computer source at commit
2d60d08d25fba3e02162b39d4c50f6b467e7f506. The upstream source credits
fqlx (#123) for sign transport and benediamond (#153) for permutations.
This version retains Prove2Me's explicit degree parameter and supplies its
integer-homogeneity and coprimality arguments against the canonical definition. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace CertificateCoordinateAux
open HodgeComputer
open MvPolynomial CertificateEulerAux
open scoped BigOperators
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

def signChange (s : Fin (n + 1) → ℂ) : AmbientPoly n →+* AmbientPoly n :=
  MvPolynomial.eval₂Hom MvPolynomial.C (fun i => C (s i) * X i)

@[simp] theorem signChange_C (s : Fin (n + 1) → ℂ) (c : ℂ) :
    signChange s (C c) = C c := by simp [signChange]

@[simp] theorem signChange_X (s : Fin (n + 1) → ℂ) (i : Fin (n + 1)) :
    signChange s (X i) = C (s i) * X i := by simp [signChange]

theorem signChange_involutive (s : Fin (n + 1) → ℂ) (hs : ∀ i, s i * s i = 1) :
    (signChange s).comp (signChange s) = RingHom.id (AmbientPoly n) := by
  apply MvPolynomial.ringHom_ext
  · intro c; simp
  · intro i
    simp only [RingHom.comp_apply, RingHom.id_apply, signChange_X, map_mul, signChange_C]
    rw [← mul_assoc, ← map_mul, hs, map_one, one_mul]

@[simp] theorem signChange_twice (s : Fin (n + 1) → ℂ) (hs : ∀ i, s i * s i = 1) (p : AmbientPoly n) :
    signChange s (signChange s p) = p :=
  DFunLike.congr_fun (signChange_involutive s hs) p

theorem pderiv_signChange (s : Fin (n + 1) → ℂ) (i : Fin (n + 1)) (p : AmbientPoly n) :
    pderiv i (signChange s p) = C (s i) * signChange s (pderiv i p) := by
  induction p using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => simp [hp, hq, mul_add]
  | mul_X p j hp =>
    simp only [map_mul, signChange_X, pderiv_mul, pderiv_C, hp, map_add]
    by_cases hj : j = i
    · subst j; simp only [pderiv_X_self, map_one]; ring
    · simp only [pderiv_X_of_ne hj, map_zero]; ring

def signField (s : Fin (n + 1) → ℂ) (N : Fin (n + 1) → AmbientPoly n) : Fin (n + 1) → AmbientPoly n :=
  fun i => C (s i) * signChange s (N i)

theorem directional_signChange (s : Fin (n + 1) → ℂ) (hs : ∀ i, s i * s i = 1)
    (p : AmbientPoly n) (N : Fin (n + 1) → AmbientPoly n) :
    directional (signChange s p) (signField s N) = signChange s (directional p N) := by
  simp only [directional, signField, pderiv_signChange, map_sum, map_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [show C (s i) * signChange s (pderiv i p) *
      (C (s i) * signChange s (N i)) =
      C (s i * s i) * (signChange s (pderiv i p) * signChange s (N i)) by
        rw [map_mul]; ring, hs, map_one, one_mul]

theorem divergence_signField (s : Fin (n + 1) → ℂ) (hs : ∀ i, s i * s i = 1)
    (N : Fin (n + 1) → AmbientPoly n) :
    divergence (signField s N) = signChange s (divergence N) := by
  simp only [divergence, signField, pderiv_C_mul, pderiv_signChange, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [← mul_assoc, ← map_mul, hs, map_one, one_mul]

theorem divergenceNumerator_signChange (s : Fin (n + 1) → ℂ) (hs : ∀ i, s i * s i = 1)
    (D : AmbientPoly n) (N : Fin (n + 1) → AmbientPoly n) :
    divergenceNumerator (signChange s D) (signField s N) =
      signChange s (divergenceNumerator D N) := by
  simp only [divergenceNumerator, divergence_signField s hs,
    directional_signChange s hs, map_sub, map_mul]

theorem signChange_homogeneous (s : Fin (n + 1) → ℂ) {p : AmbientPoly n} {d : ℕ}
    (h : p.IsHomogeneous d) : (signChange s p).IsHomogeneous d := by
  simpa only [signChange, coe_eval₂Hom, one_mul] using
    h.eval₂ C (fun i => C (s i) * X i)
      (fun c => isHomogeneous_C (Fin (n + 1)) c)
      (fun i => isHomogeneous_C_mul_X (s i) i)

theorem signChange_graded (s : Fin (n + 1) → ℂ) {p : AmbientPoly n} {k : ℤ}
    (h : Homogeneous p k) : Homogeneous (signChange s p) k := by
  by_cases hk : 0 ≤ k
  · simpa only [Int.toNat_of_nonneg hk] using
      hom_of_nat (signChange_homogeneous s (hom_to_nat h hk))
  · rw [hom_eq_zero_of_neg h (by omega), map_zero]
    exact hom_zero _

theorem signChange_ne_zero (s : Fin (n + 1) → ℂ) (hs : ∀ i, s i * s i = 1)
    {p : AmbientPoly n} (hp : p ≠ 0) : signChange s p ≠ 0 := by
  intro hz
  have ht := congrArg (signChange s) hz
  rw [signChange_twice s hs, map_zero] at ht
  exact hp ht

/-- Pull a certificate through a diagonal sign involution. Polynomial
substitution alone is insufficient: every field component also receives its
coordinate's sign, which is necessary for both derivative identities. -/
theorem verify_sign_change (s : Fin (n + 1) → ℂ) (hs : ∀ i, s i * s i = 1)
    {F A D Q : AmbientPoly n} {d q : ℕ} {N : Fin (n + 1) → AmbientPoly n}
    (h : Verify F A d q D N Q) :
    Verify (signChange s F) (signChange s A) d q (signChange s D)
      (signField s N) (signChange s Q) where
  hypersurface_ne_zero := signChange_ne_zero s hs h.hypersurface_ne_zero
  hypersurface_homogeneous := signChange_homogeneous s h.hypersurface_homogeneous
  source_homogeneous := signChange_graded s h.source_homogeneous
  denominator_ne_zero := signChange_ne_zero s hs h.denominator_ne_zero
  denominator_homogeneous := by
    rw [(signChange_homogeneous s h.denominator_homogeneous).totalDegree
      (signChange_ne_zero s hs h.denominator_ne_zero)]
    exact signChange_homogeneous s h.denominator_homogeneous
  numerator_homogeneous := by
    intro i
    rw [(signChange_homogeneous s h.denominator_homogeneous).totalDegree
      (signChange_ne_zero s hs h.denominator_ne_zero)]
    exact hom_const_mul (signChange_graded s (h.numerator_homogeneous i)) (s i)
  denominator_legal := by
    intro p hp hq
    have hp' : signChange s p ∣ F := by
      simpa only [signChange_twice s hs] using map_dvd (signChange s) hp
    have hq' : signChange s p ∣ D := by
      simpa only [signChange_twice s hs] using map_dvd (signChange s) hq
    have hu := (h.denominator_legal hp' hq').map (signChange s)
    simpa only [signChange_twice s hs] using hu
  identity := by
    have hi := congrArg (signChange s) h.identity
    simpa only [defect, directional_signChange s hs,
      divergenceNumerator_signChange s hs, map_add, map_sub, map_mul, map_pow, map_natCast] using hi


end CertificateCoordinateAux

end

section
set_option backward.isDefEq.respectTransparency true

open HodgeComputer MvPolynomial CertificateEulerAux CertificateOperationsAux CertificateCoordinateAux
open scoped BigOperators
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace CertificateInvolutionAverageAux
variable {n d q : ℕ}

lemma average_odd_source (s : Fin (n+1) → ℂ) (hs : ∀ i, s i*s i=1)
    {F A D Q : AmbientPoly n} {N : Fin (n+1) → AmbientPoly n}
    (h : Verify F A d q D N Q) (hF : signChange s F=F) (hA : signChange s A= -A) :
    ∃ (M : Fin (n+1) → AmbientPoly n) (R : AmbientPoly n),
      Verify F A d q (D*signChange s D) M R ∧
      signChange s (D*signChange s D)=D*signChange s D ∧
      (∀ i, signChange s (M i)= -C (s i)*M i) ∧ signChange s R= -R := by
  let T := signChange s
  let half : AmbientPoly n := C ((2 : ℂ)⁻¹)
  let M : Fin (n+1) → AmbientPoly n :=
    fun i => half*(T D*N i+D*(C (-1)*(C (s i)*T (N i))))
  let R : AmbientPoly n := half*((T D)^2*Q+D^2*(C (-1)*T Q))
  have ht : Verify F (-A) d q (T D) (signField s N) (T Q) := by
    simpa only [hF,hA] using verify_sign_change s hs h
  have hn : Verify F A d q (T D) (fun i => C (-1)*signField s N i) (C (-1)*T Q) := by
    simpa only [map_neg,map_one,neg_one_mul,neg_neg] using verify_const_mul ht (-1)
  have hsource : C ((2 : ℂ)⁻¹)*(A+A)=A := by
    calc
      _ = C ((2 : ℂ)⁻¹+(2 : ℂ)⁻¹)*A := by rw [map_add];ring
      _ = A := by norm_num
  have hm : Verify F A d q (D*T D) M R := by
    have hh := verify_const_mul (verify_add h hn) ((2 : ℂ)⁻¹)
    rw [hsource] at hh
    exact hh
  refine ⟨M,R,hm,?_,?_,?_⟩
  · simp only [map_mul,signChange_twice s hs]
    exact mul_comm _ _
  · intro i
    have hsc : C (s i)*C (s i)=(1 : AmbientPoly n) := by rw [← map_mul,hs,map_one]
    dsimp only [M,half,T]
    simp only [map_mul,map_add,signChange_C,signChange_twice s hs,map_neg,map_one]
    linear_combination -C ((2 : ℂ)⁻¹)*D*signChange s (N i)*hsc
  · dsimp only [R,half,T]
    simp only [map_mul,map_add,map_pow,signChange_C,signChange_twice s hs,map_neg,map_one]
    ring

end CertificateInvolutionAverageAux
end

theorem solution {n d q : ℕ}
    (s : Fin (n+1) → ℂ) (hs : ∀ i, s i*s i=1)
    {F A D Q : HodgeComputer.AmbientPoly n}
    {N : Fin (n+1) → HodgeComputer.AmbientPoly n}
    (h : HodgeComputer.Verify F A d q D N Q) :
    let T : HodgeComputer.AmbientPoly n →+* HodgeComputer.AmbientPoly n :=
      MvPolynomial.eval₂Hom MvPolynomial.C
        (fun i : Fin (n+1) => MvPolynomial.C (s i)*MvPolynomial.X i)
    T F=F → T A= -A →
      ∃ (M : Fin (n+1) → HodgeComputer.AmbientPoly n) (R : HodgeComputer.AmbientPoly n),
        HodgeComputer.Verify F A d q (D*T D) M R ∧ T (D*T D)=D*T D ∧
        (∀ i, T (M i)= -MvPolynomial.C (s i)*M i) ∧ T R= -R := by
  dsimp only
  intro hF hA
  exact CertificateInvolutionAverageAux.average_odd_source s hs h hF hA

#print axioms solution
