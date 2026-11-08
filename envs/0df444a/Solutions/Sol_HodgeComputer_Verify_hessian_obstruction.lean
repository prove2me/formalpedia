-- Prove2me | solution 1 for HodgeComputer.Verify.hessian_obstruction
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T13:20:38.691193+00:00
-- url     : https://prove2.me/submissions/e7361049-4aea-48a7-838e-20f5eba8d4f8

import Definitions.Def_DiamondCertificate
import Mathlib.RingTheory.Regular.RegularSequence
import Mathlib.Data.List.OfFn
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.RingTheory.MvPolynomial.EulerIdentity
import Mathlib.RingTheory.Ideal.Quotient.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.LinearCombination

noncomputable section

open scoped BigOperators
open RingTheory.Sequence
set_option backward.isDefEq.respectTransparency false

namespace RegularSyzygyAux
variable {R : Type*} [CommRing R]

lemma ofList_ofFn {n : ℕ} (f : Fin n → R) :
    Ideal.ofList (List.ofFn f) = Ideal.span (Set.range f) := by
  change Ideal.span {x | x ∈ List.ofFn f} = Ideal.span (Set.range f)
  congr 1
  ext x
  exact List.mem_ofFn

lemma syzygy {n : ℕ} (f : Fin n → R)
    (hreg : IsWeaklyRegular R (List.ofFn f))
    (a : Fin n → R) (ha : ∑ i, a i*f i = 0) :
    ∃ U : Fin n → Fin n → R,
      ∀ i, a i = ∑ j, (U i j-U j i)*f j := by
  classical
  induction n with
  | zero => exact ⟨fun i => Fin.elim0 i,fun i => Fin.elim0 i⟩
  | succ n ih =>
    let g : Fin n → R := fun i => f i.castSucc
    have hsplit : List.ofFn f = List.ofFn g ++ [f (Fin.last n)] := by
      simpa only [g,List.concat_eq_append] using List.ofFn_succ' f
    rw [hsplit,isWeaklyRegular_append_iff] at hreg
    let J : Ideal R := Ideal.span (Set.range g)
    have hlast : IsSMulRegular (R ⧸ J) (f (Fin.last n)) := by
      have hh := (isWeaklyRegular_singleton_iff _ _).mp hreg.2
      rw [Ideal.smul_eq_mul] at hh
      change IsSMulRegular (R ⧸ (Ideal.ofList (List.ofFn g)*⊤)) _ at hh
      rw [Ideal.mul_top,ofList_ofFn] at hh
      exact hh
    have hprod : f (Fin.last n)*a (Fin.last n) ∈ J := by
      have heq := ha
      rw [Fin.sum_univ_castSucc] at heq
      have he : f (Fin.last n)*a (Fin.last n) =
          -(∑ i : Fin n, a i.castSucc*f i.castSucc) := by
        linear_combination heq
      rw [he]
      apply J.neg_mem
      apply J.sum_mem
      intro i hi
      exact J.mul_mem_left (a i.castSucc) (Ideal.subset_span ⟨i,rfl⟩)
    have hmem : a (Fin.last n) ∈ J :=
      mem_of_isSMulRegular_quotient_of_smul_mem hlast hprod
    obtain ⟨c,hc⟩ := Ideal.mem_span_range_iff_exists_fun.mp hmem
    let b : Fin n → R := fun i => a i.castSucc+c i*f (Fin.last n)
    have hb : ∑ i, b i*g i=0 := by
      dsimp only [b]
      simp only [add_mul,Finset.sum_add_distrib]
      have he : (∑ i, c i*f (Fin.last n)*g i) =
          (∑ i, c i*g i)*f (Fin.last n) := by
        simp only [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro i hi
        ring
      have heq := ha
      rw [Fin.sum_univ_castSucc] at heq
      rw [he,hc]
      exact heq
    obtain ⟨U,hU⟩ := ih g hreg.1 b hb
    let V : Fin (n+1) → Fin (n+1) → R :=
      Fin.snoc (fun i => Fin.snoc (U i) 0) (Fin.snoc c 0)
    refine ⟨V,?_⟩
    intro i
    refine Fin.lastCases ?_ (fun i => ?_) i
    · simpa [V,Fin.sum_univ_castSucc,g] using hc.symm
    · simp only [Fin.sum_univ_castSucc, V,Fin.snoc_castSucc,Fin.snoc_last,
        zero_sub,neg_mul]
      rw [← hU i]
      dsimp [b]
      ring

end RegularSyzygyAux


open scoped BigOperators
open MvPolynomial RingTheory.Sequence
set_option backward.isDefEq.respectTransparency false
namespace RegularSyzygyAux

variable {R σ : Type*} [CommRing R]

lemma component_mul_homogeneous (P : MvPolynomial σ R) {Q : MvPolynomial σ R}
    {d : ℕ} (hQ : Q.IsHomogeneous d) (r : ℕ) :
    homogeneousComponent (r+d) (P*Q) = homogeneousComponent r P*Q := by
  classical
  induction P using MvPolynomial.induction_on' with
  | monomial m c =>
    have hm : (monomial m c : MvPolynomial σ R).IsHomogeneous m.degree :=
      isHomogeneous_monomial c rfl
    rw [homogeneousComponent_of_mem (hm.mul hQ),homogeneousComponent_of_mem hm]
    simp only [Nat.add_right_cancel_iff,ite_mul,zero_mul]
  | add P S hP hS => simp only [add_mul,map_add,hP,hS]

lemma homogeneous_syzygy {n d r : ℕ} (f : Fin n → MvPolynomial σ R)
    (hf : ∀ i, (f i).IsHomogeneous d)
    (hreg : IsWeaklyRegular (MvPolynomial σ R) (List.ofFn f))
    (a : Fin n → MvPolynomial σ R) (ha : ∀ i, (a i).IsHomogeneous (r+d))
    (hsum : ∑ i, a i*f i = 0) :
    ∃ U : Fin n → Fin n → MvPolynomial σ R,
      (∀ i j, (U i j).IsHomogeneous r) ∧
      ∀ i, a i = ∑ j, (U i j-U j i)*f j := by
  obtain ⟨V,hV⟩ := syzygy f hreg a hsum
  refine ⟨fun i j => homogeneousComponent r (V i j),?_,?_⟩
  · intro i j
    exact homogeneousComponent_isHomogeneous r (V i j)
  · intro i
    have hh := congrArg (homogeneousComponent (r+d)) (hV i)
    rw [homogeneousComponent_eq_self (ha i),map_sum] at hh
    simpa only [component_mul_homogeneous _ (hf _),map_sub] using hh

end RegularSyzygyAux


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


open HodgeComputer MvPolynomial
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
namespace CertificateJacobianAux
variable {n : ℕ}

def jacobian (F : AmbientPoly n) : Ideal (AmbientPoly n) :=
  Ideal.span (Set.range (fun i => pderiv i F))

lemma partial_mem (F : AmbientPoly n) (i : Fin (n+1)) : pderiv i F ∈ jacobian F :=
  Ideal.subset_span ⟨i,rfl⟩

lemma polynomial_mem {F : AmbientPoly n} {d : ℕ} (hF : F.IsHomogeneous d) (hd : 0<d) :
    F ∈ jacobian F := by
  have he : (d:AmbientPoly n)*F ∈ jacobian F := by
    rw [← nsmul_eq_mul, ← hF.sum_X_mul_pderiv]
    apply Ideal.sum_mem
    intro i hi
    exact (jacobian F).mul_mem_left (X i) (partial_mem F i)
  have hdC : (d:ℂ)≠0 := by exact_mod_cast (Nat.ne_of_gt hd)
  have hi : C ((d:ℂ)⁻¹)*(d:AmbientPoly n)=1 := by
    rw [← map_natCast (C : ℂ →+* AmbientPoly n) d, ← map_mul, inv_mul_cancel₀ hdC, map_one]
  have hh := (jacobian F).mul_mem_left (C ((d:ℂ)⁻¹)) he
  simpa only [← mul_assoc,hi,one_mul] using hh

lemma hessian_obstruction {F A : AmbientPoly n} {d : ℕ}
    (hF : F.IsHomogeneous d) (hd : 0<d)
    (c : Fin (n+1) → AmbientPoly n) (N : Fin (n+1) → AmbientPoly n)
    (hN : ∀ i, N i-A*c i ∈ jacobian F)
    (hres : F ∣ divergenceNumerator (directional F c) N) :
    A*(∑ i, ∑ j, c i*c j*pderiv i (pderiv j F)) ∈ jacobian F := by
  let phi := Ideal.Quotient.mk (jacobian F)
  have hp (i : Fin (n+1)) : phi (pderiv i F)=0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (partial_mem F i)
  have hFc : phi F=0 := Ideal.Quotient.eq_zero_iff_mem.mpr (polynomial_mem hF hd)
  have hNc (i : Fin (n+1)) : phi (N i)=phi A*phi (c i) := by
    have hh : phi (N i-A*c i)=0 := Ideal.Quotient.eq_zero_iff_mem.mpr (hN i)
    simpa only [map_sub,map_mul,sub_eq_zero] using hh
  have hD : phi (directional F c)=0 := by simp [directional,map_sum,hp]
  have hDi (i : Fin (n+1)) : phi (pderiv i (directional F c)) =
      ∑ j, phi (pderiv i (pderiv j F))*phi (c j) := by
    simp [directional,map_sum,hp,mul_comm]
  obtain ⟨Q,hQ⟩ := hres
  have hB : phi (divergenceNumerator (directional F c) N)=0 := by
    rw [hQ,map_mul,hFc,zero_mul]
  rw [divergenceNumerator,map_sub,map_mul,hD,zero_mul,zero_sub] at hB
  rw [directional,map_sum] at hB
  simp only [map_mul,hDi,hNc] at hB
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  change phi (A*(∑ i, ∑ j, c i*c j*pderiv i (pderiv j F)))=0
  simp only [map_mul,map_sum]
  have he : phi A*(∑ i, ∑ j, phi (c i)*phi (c j)*phi (pderiv i (pderiv j F))) =
      ∑ i, (∑ j, phi (pderiv i (pderiv j F))*phi (c j))*(phi A*phi (c i)) := by
    simp only [Finset.mul_sum,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [he]
  exact neg_eq_zero.mp hB

lemma koszul_lift_hessian {F A : AmbientPoly n} {d : ℕ}
    (hF : F.IsHomogeneous d) (hd : 0<d)
    (c : Fin (n+1) → AmbientPoly n)
    (U : Fin (n+1) → Fin (n+1) → AmbientPoly n)
    (hres : F ∣ divergenceNumerator (directional F c)
      (fun i => A*c i+∑ j, (U i j-U j i)*pderiv j F)) :
    A*(∑ i, ∑ j, c i*c j*pderiv i (pderiv j F)) ∈ jacobian F := by
  apply hessian_obstruction hF hd c _ ?_ hres
  intro i
  simp only [add_sub_cancel_left]
  apply Ideal.sum_mem
  intro j hj
  exact (jacobian F).mul_mem_left (U i j-U j i) (partial_mem F j)

end CertificateJacobianAux


open HodgeComputer MvPolynomial RingTheory.Sequence
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

namespace CertificateKoszulAux
variable {n : ℕ}

lemma relation_zero {F : AmbientPoly n} (N M : Fin (n+1) → AmbientPoly n)
    (hlift : directional F N=directional F M) :
    ∑ i, (N i-M i)*pderiv i F=0 := by
  calc
    _ = directional F N-directional F M := by
      simp only [directional,← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ = 0 := sub_eq_zero.mpr hlift

lemma lifts_differ {F : AmbientPoly n}
    (hreg : IsWeaklyRegular (AmbientPoly n) (List.ofFn (fun i => pderiv i F)))
    (N M : Fin (n+1) → AmbientPoly n) (hlift : directional F N=directional F M) :
    ∃ U : Fin (n+1) → Fin (n+1) → AmbientPoly n,
      ∀ i, N i=M i+∑ j, (U i j-U j i)*pderiv j F := by
  have hz := relation_zero N M hlift
  obtain ⟨U,hU⟩ := RegularSyzygyAux.syzygy (fun i => pderiv i F) hreg _ hz
  refine ⟨U,fun i => ?_⟩
  rw [← hU i]
  ring

lemma homogeneous_lifts_differ {F : AmbientPoly n} {d r : ℕ}
    (hF : F.IsHomogeneous d)
    (hreg : IsWeaklyRegular (AmbientPoly n) (List.ofFn (fun i => pderiv i F)))
    (N M : Fin (n+1) → AmbientPoly n)
    (hN : ∀ i, (N i).IsHomogeneous (r+(d-1)))
    (hM : ∀ i, (M i).IsHomogeneous (r+(d-1)))
    (hlift : directional F N=directional F M) :
    ∃ U : Fin (n+1) → Fin (n+1) → AmbientPoly n,
      (∀ i j, (U i j).IsHomogeneous r) ∧
      ∀ i, N i=M i+∑ j, (U i j-U j i)*pderiv j F := by
  have hz := relation_zero N M hlift
  obtain ⟨U,hdeg,hU⟩ := RegularSyzygyAux.homogeneous_syzygy
    (fun i => pderiv i F) (fun _ => hF.pderiv) hreg
    (fun i => N i-M i) (fun i => (hN i).sub (hM i)) hz
  refine ⟨U,hdeg,fun i => ?_⟩
  rw [← hU i]
  ring

lemma normalized_hessian {F A : AmbientPoly n} {d : ℕ}
    (hF : F.IsHomogeneous d) (hd : 0<d)
    (hreg : IsWeaklyRegular (AmbientPoly n) (List.ofFn (fun i => pderiv i F)))
    (c N : Fin (n+1) → AmbientPoly n)
    (hlift : directional F N=A*directional F c)
    (hres : F ∣ divergenceNumerator (directional F c) N) :
    A*(∑ i, ∑ j, c i*c j*pderiv i (pderiv j F)) ∈
      Ideal.span (Set.range (fun i => pderiv i F)) := by
  have he : directional F N=directional F (fun i => A*c i) := by
    rw [hlift]
    simp only [directional,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  obtain ⟨U,hU⟩ := lifts_differ hreg N (fun i => A*c i) he
  have hN : N=(fun i => A*c i+∑ j, (U i j-U j i)*pderiv j F) := funext hU
  rw [hN] at hres
  exact CertificateJacobianAux.koszul_lift_hessian hF hd c U hres

end CertificateKoszulAux


open HodgeComputer MvPolynomial RingTheory.Sequence
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

namespace CertificateKoszulAux
variable {n : ℕ}

lemma directional_const_mul (F : AmbientPoly n) (N : Fin (n+1) → AmbientPoly n) (z : ℂ) :
    directional F (fun i => C z*N i)=C z*directional F N := by
  simp only [directional,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

lemma divergenceNumerator_const_mul (D : AmbientPoly n)
    (N : Fin (n+1) → AmbientPoly n) (z : ℂ) :
    divergenceNumerator D (fun i => C z*N i)=C z*divergenceNumerator D N := by
  have hd : divergence (fun i => C z*N i)=C z*divergence N := by
    simp only [divergence,pderiv_C_mul,Finset.mul_sum]
  rw [divergenceNumerator,hd,directional_const_mul,divergenceNumerator]
  ring

lemma certificate_hessian {F A : AmbientPoly n} {d q : ℕ}
    (c N : Fin (n+1) → AmbientPoly n) (Q : AmbientPoly n)
    (h : Verify F A d q (directional F c) N Q) (hd : 0<d) (hq : 0<q)
    (hreg : IsWeaklyRegular (AmbientPoly n) (List.ofFn (fun i => pderiv i F))) :
    A*(∑ i, ∑ j, c i*c j*pderiv i (pderiv j F)) ∈
      Ideal.span (Set.range (fun i => pderiv i F)) := by
  obtain ⟨M,_,hgrad,hdiv⟩ := CertificateEulerAux.normalize h hd hq
  let L : Fin (n+1) → AmbientPoly n := fun i => C (q:ℂ)*M i
  apply normalized_hessian h.hypersurface_homogeneous hd hreg c L
  · change directional F (fun i => C (q:ℂ)*M i)=A*directional F c
    rw [directional_const_mul,map_natCast]
    exact hgrad
  · have hF : F ∣ F^q := dvd_pow_self F (Nat.ne_of_gt hq)
    have hb : F ∣ divergenceNumerator (directional F c) M := by
      rw [hdiv]
      exact dvd_mul_of_dvd_left hF Q
    simpa only [L,divergenceNumerator_const_mul] using
      dvd_mul_of_dvd_right hb (C (q:ℂ))

end CertificateKoszulAux

theorem solution {n : ℕ} {F A : HodgeComputer.AmbientPoly n} {d q : ℕ}
    (c N : Fin (n+1) → HodgeComputer.AmbientPoly n) (Q : HodgeComputer.AmbientPoly n)
    (h : HodgeComputer.Verify F A d q (HodgeComputer.directional F c) N Q)
    (hd : 0<d) (hq : 0<q)
    (hreg : RingTheory.Sequence.IsWeaklyRegular (HodgeComputer.AmbientPoly n)
      (List.ofFn (fun i => MvPolynomial.pderiv i F))) :
    A*(∑ i, ∑ j, c i*c j*MvPolynomial.pderiv i (MvPolynomial.pderiv j F)) ∈
      Ideal.span (Set.range (fun i => MvPolynomial.pderiv i F)) :=
  CertificateKoszulAux.certificate_hessian c N Q h hd hq hreg

#print axioms solution
