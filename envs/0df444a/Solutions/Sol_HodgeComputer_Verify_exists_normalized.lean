-- Prove2me | solution 1 for HodgeComputer.Verify.exists_normalized
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T13:03:56.012815+00:00
-- url     : https://prove2.me/submissions/f8f0f43f-cc45-493f-993e-08d6b9ec0e7f

import Definitions.Def_DiamondCertificate
import Mathlib.RingTheory.MvPolynomial.EulerIdentity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.LinearCombination

noncomputable section

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


open HodgeComputer MvPolynomial
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
namespace CertificateEulerAux
variable {n : ℕ}

lemma normalize {F A D : AmbientPoly n} {d q : ℕ} {N : Fin (n+1) → AmbientPoly n}
    {Q : AmbientPoly n} (h : Verify F A d q D N Q) (hd : 0<d) (hq : 0<q) :
    ∃ M : Fin (n+1) → AmbientPoly n,
      Verify F A d q D M Q ∧ (q:AmbientPoly n)*directional F M=A*D ∧
      divergenceNumerator D M=F^q*Q := by
  let T : AmbientPoly n := A*D-(q:AmbientPoly n)*directional F N
  have hFT : F ∣ T := by
    apply h.denominator_legal.dvd_of_dvd_mul_left
    have he : D*T=defect F A D q N-F*divergenceNumerator D N := by
      dsimp [T,defect]
      ring
    rw [he,h.identity,pow_succ]
    exact dvd_sub (dvd_mul_of_dvd_left (dvd_mul_left F (F^q)) Q) (dvd_mul_right F _)
  obtain ⟨R,hR⟩ := hFT
  let t : ℤ := (D.totalDegree:ℤ)+d*(q+1)-(n+1)
  have hT : Homogeneous T t := by
    apply hom_sub
    · convert hom_mul h.source_homogeneous (hom_of_nat h.denominator_homogeneous) using 1 <;> dsimp [t] <;> ring
    · have hdir : Homogeneous (directional F N) t := by
        apply hom_sum
        intro i
        convert hom_mul (hom_pderiv (hom_of_nat h.hypersurface_homogeneous) i)
          (h.numerator_homogeneous i) using 1 <;> dsimp [t] <;> ring
      simpa only [map_natCast] using hom_const_mul hdir (q:ℂ)
  have hRhom : Homogeneous R ((D.totalDegree:ℤ)+d*q-n-1) := by
    have hh := hom_mul_cancel (hom_of_nat h.hypersurface_homogeneous)
      (hR ▸ hT) h.hypersurface_ne_zero
    convert hh using 1 <;> dsimp [t] <;> push_cast <;> ring
  let H : AmbientPoly n := C (((q:ℂ)*(d:ℂ))⁻¹)*R
  have hH : Homogeneous H ((D.totalDegree:ℤ)+d*q-n-1) := hom_const_mul hRhom _
  let M : Fin (n+1) → AmbientPoly n := N+radial H
  have hMh (i : Fin (n+1)) : Homogeneous (M i) ((D.totalDegree:ℤ)+d*q-n) := by
    apply hom_add (h.numerator_homogeneous i)
    change Homogeneous (H*X i) _
    convert hom_mul hH (hom_of_nat (isHomogeneous_X ℂ i)) using 1 <;> ring
  have hdef : defect F A D q M=defect F A D q N :=
    radial_defect F A D H d q N h.hypersurface_homogeneous h.denominator_homogeneous hH
  have hM : Verify F A d q D M Q :=
    { hypersurface_ne_zero := h.hypersurface_ne_zero
      hypersurface_homogeneous := h.hypersurface_homogeneous
      source_homogeneous := h.source_homogeneous
      denominator_ne_zero := h.denominator_ne_zero
      denominator_homogeneous := h.denominator_homogeneous
      numerator_homogeneous := hMh
      denominator_legal := h.denominator_legal
      identity := hdef.trans h.identity }
  have hqC : (q:ℂ)≠0 := by exact_mod_cast (Nat.ne_of_gt hq)
  have hdC : (d:ℂ)≠0 := by exact_mod_cast (Nat.ne_of_gt hd)
  have hscale : (q:AmbientPoly n)*(d:AmbientPoly n)*C (((q:ℂ)*(d:ℂ))⁻¹)=1 := by
    rw [← map_natCast (C : ℂ →+* AmbientPoly n) q, ← map_natCast (C : ℂ →+* AmbientPoly n) d,
      ← map_mul, ← map_mul, mul_inv_cancel₀ (mul_ne_zero hqC hdC), map_one]
  have hEF : euler F=(d:AmbientPoly n)*F := by
    simpa only [Int.cast_natCast] using (homogeneous_iff_euler F (d:ℤ)).mp
      (hom_of_nat h.hypersurface_homogeneous)
  have hgrad : (q:AmbientPoly n)*directional F M=A*D := by
    change (q:AmbientPoly n)*directional F (N+radial H)=A*D
    rw [directional_add,directional_radial,hEF]
    calc
      _ = (q:AmbientPoly n)*directional F N+
          ((q:AmbientPoly n)*(d:AmbientPoly n)*C (((q:ℂ)*(d:ℂ))⁻¹))*(F*R) := by dsimp [H]; ring
      _ = A*D := by rw [hscale,one_mul]; dsimp [T] at hR; linear_combination -hR
  refine ⟨M,hM,hgrad,?_⟩
  apply mul_left_cancel₀ h.hypersurface_ne_zero
  calc
    F*divergenceNumerator D M = defect F A D q M := by
      unfold defect
      have he : (q:AmbientPoly n)*D*directional F M=D*((q:AmbientPoly n)*directional F M) := by ring
      rw [he,hgrad]
      ring
    _ = F*(F^q*Q) := by rw [hM.identity,pow_succ]; ring

end CertificateEulerAux

theorem solution {n : ℕ} {F A D : HodgeComputer.AmbientPoly n} {d q : ℕ}
    {N : Fin (n+1) → HodgeComputer.AmbientPoly n} {Q : HodgeComputer.AmbientPoly n}
    (h : HodgeComputer.Verify F A d q D N Q) (hd : 0<d) (hq : 0<q) :
    ∃ M : Fin (n+1) → HodgeComputer.AmbientPoly n,
      HodgeComputer.Verify F A d q D M Q ∧
      (q:HodgeComputer.AmbientPoly n)*HodgeComputer.directional F M=A*D ∧
      HodgeComputer.divergenceNumerator D M=F^q*Q :=
  CertificateEulerAux.normalize h hd hq

#print axioms solution
