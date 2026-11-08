-- Prove2me | solution 1 for HodgeComputer.Verify.signed_coordinate_transport
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T15:12:13.868029+00:00
-- url     : https://prove2.me/submissions/ca5ff807-bf21-49f2-82f1-8cd5c633c21d

import Definitions.Def_DiamondCertificate
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import Mathlib.RingTheory.MvPolynomial.EulerIdentity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.LinearCombination

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

def renamedVector (e : Fin (n + 1) ≃ Fin (n + 1)) (N : Fin (n + 1) → AmbientPoly n) :
    Fin (n + 1) → AmbientPoly n := fun i => rename e (N (e.symm i))

theorem rename_directional (e : Fin (n + 1) ≃ Fin (n + 1)) (F : AmbientPoly n)
    (N : Fin (n + 1) → AmbientPoly n) :
    HodgeComputer.directional (rename e F) (renamedVector e N) =
      rename e (HodgeComputer.directional F N) := by
  unfold HodgeComputer.directional
  rw [← Equiv.sum_comp e]
  simp only [renamedVector, Equiv.symm_apply_apply, pderiv_rename e.injective, map_sum, map_mul]

theorem rename_divergence (e : Fin (n + 1) ≃ Fin (n + 1)) (N : Fin (n + 1) → AmbientPoly n) :
    HodgeComputer.divergence (renamedVector e N) = rename e (HodgeComputer.divergence N) := by
  unfold HodgeComputer.divergence
  rw [← Equiv.sum_comp e]
  simp only [renamedVector, Equiv.symm_apply_apply, pderiv_rename e.injective, map_sum]


lemma hom_rename (e : Fin (n+1) ≃ Fin (n+1)) {P : AmbientPoly n} {k : ℤ}
    (h : Homogeneous P k) : Homogeneous (rename e P) k := by
  by_cases hk : 0 ≤ k
  · simpa only [Int.toNat_of_nonneg hk] using
      hom_of_nat ((hom_to_nat h hk).rename_isHomogeneous (f := e))
  · rw [hom_eq_zero_of_neg h (by omega),map_zero]
    exact hom_zero k

lemma verify_rename (e : Fin (n+1) ≃ Fin (n+1))
    {F A D Q : AmbientPoly n} {d q : ℕ} {N : Fin (n+1) → AmbientPoly n}
    (h : Verify F A d q D N Q) :
    Verify (rename e F) (rename e A) d q (rename e D) (renamedVector e N) (rename e Q) := by
  have hD0 : rename e D ≠ 0 :=
    (rename_injective _ e.injective).ne (by simpa using h.denominator_ne_zero)
  have hdeg := h.denominator_homogeneous.rename_isHomogeneous (f := e) |>.totalDegree hD0
  refine {
    hypersurface_ne_zero := (rename_injective _ e.injective).ne (by simpa using h.hypersurface_ne_zero)
    hypersurface_homogeneous := h.hypersurface_homogeneous.rename_isHomogeneous
    source_homogeneous := hom_rename e h.source_homogeneous
    denominator_ne_zero := hD0
    denominator_homogeneous := ?_
    numerator_homogeneous := ?_
    denominator_legal := ?_
    identity := ?_ }
  · rw [hdeg]
    exact h.denominator_homogeneous.rename_isHomogeneous
  · intro i
    rw [hdeg]
    exact hom_rename e (h.numerator_homogeneous (e.symm i))
  · let E := renameEquiv ℂ e
    change IsRelPrime (E F) (E D)
    intro p hp hq
    have h1 : E.symm p ∣ F := by simpa using map_dvd E.symm.toRingHom hp
    have h2 : E.symm p ∣ D := by simpa using map_dvd E.symm.toRingHom hq
    have hu := (h.denominator_legal h1 h2).map E.toRingHom
    simpa using hu
  · have hi := congrArg (rename e) h.identity
    simpa only [defect,divergenceNumerator,rename_directional,rename_divergence,
      map_sub,map_add,map_mul,map_pow,map_natCast] using hi

end CertificateCoordinateAux
end

theorem solution {n d q : ℕ} (e : Fin (n+1) ≃ Fin (n+1))
    (s : Fin (n+1) → ℂ) (hs : ∀ i, s i*s i=1)
    {F A D Q : HodgeComputer.AmbientPoly n}
    {N : Fin (n+1) → HodgeComputer.AmbientPoly n}
    (h : HodgeComputer.Verify F A d q D N Q) :
    let T : HodgeComputer.AmbientPoly n →+* HodgeComputer.AmbientPoly n :=
      MvPolynomial.eval₂Hom MvPolynomial.C
        (fun i : Fin (n+1) => MvPolynomial.C (s i)*MvPolynomial.X i)
    HodgeComputer.Verify (T (MvPolynomial.rename e F)) (T (MvPolynomial.rename e A)) d q
      (T (MvPolynomial.rename e D))
      (fun i => MvPolynomial.C (s i)*T (MvPolynomial.rename e (N (e.symm i))))
      (T (MvPolynomial.rename e Q)) := by
  exact CertificateCoordinateAux.verify_sign_change s hs
    (CertificateCoordinateAux.verify_rename e h)

#print axioms solution
