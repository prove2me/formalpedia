-- Prove2me | solution 1 for HodgeComputer.Verify.exists_complete_koszul_search
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T13:37:00.969734+00:00
-- url     : https://prove2.me/submissions/9147c914-3da6-4c9a-bc02-84097a7e23a2

import Definitions.Def_DiamondCertificate
import Mathlib.RingTheory.Regular.RegularSequence
import Mathlib.Data.List.OfFn
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.RingTheory.MvPolynomial.EulerIdentity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Abel
open HodgeComputer MvPolynomial RingTheory.Sequence
open scoped BigOperators

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


open MvPolynomial Finsupp
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

namespace WeightedProjectionAux
variable {σ R Γ : Type*} [CommRing R] [AddCommGroup Γ]
variable (w : σ → Γ)

lemma component_self {P : MvPolynomial σ R} {a : Γ}
    (hP : P.IsWeightedHomogeneous w a) : weightedHomogeneousComponent w a P=P := by
  classical
  simp [weightedHomogeneousComponent_of_mem hP]

lemma component_mul (P : MvPolynomial σ R) {Q : MvPolynomial σ R}
    {b : Γ} (hQ : Q.IsWeightedHomogeneous w b) (a : Γ) :
    weightedHomogeneousComponent w (a+b) (P*Q) =
      weightedHomogeneousComponent w a P*Q := by
  classical
  induction P using MvPolynomial.induction_on' with
  | monomial m c =>
    have hm : (monomial m c : MvPolynomial σ R).IsWeightedHomogeneous w (weight w m) :=
      isWeightedHomogeneous_monomial w m c rfl
    rw [weightedHomogeneousComponent_of_mem (hm.mul hQ),weightedHomogeneousComponent_of_mem hm]
    simp only [add_left_inj,ite_mul,zero_mul]
  | add P S hP hS => simp only [add_mul,map_add,hP,hS]

lemma component_pderiv (P : MvPolynomial σ R) (a : Γ) (i : σ) :
    weightedHomogeneousComponent w (a-w i) (pderiv i P) =
      pderiv i (weightedHomogeneousComponent w a P) := by
  classical
  ext m
  simp only [coeff_weightedHomogeneousComponent,coeff_pderiv,map_add,weight_single,
    one_nsmul,ite_mul,zero_mul,eq_sub_iff_add_eq]

lemma pderiv_weighted {P : MvPolynomial σ R} {a : Γ}
    (hP : P.IsWeightedHomogeneous w a) (i : σ) :
    (pderiv i P).IsWeightedHomogeneous w (a-w i) := by
  have he := component_pderiv w P a i
  rw [component_self w hP] at he
  rw [← he]
  exact weightedHomogeneousComponent_isWeightedHomogeneous _ _

lemma preserves_degree {P : MvPolynomial σ ℂ} {d : ℤ}
    (hP : HodgeComputer.Homogeneous P d) (a : Γ) :
    HodgeComputer.Homogeneous (weightedHomogeneousComponent w a P) d := by
  classical
  intro m hm
  apply hP
  rw [coeff_weightedHomogeneousComponent] at hm
  split_ifs at hm with h
  · exact hm
  · exact False.elim (hm rfl)

end WeightedProjectionAux


open HodgeComputer MvPolynomial Finsupp
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

namespace WeightedProjectionAux
variable {n : ℕ} {Γ : Type*} [AddCommGroup Γ]
variable (w : Fin (n+1) → Γ)

def numerator (a : Γ) (N : Fin (n+1) → AmbientPoly n) : Fin (n+1) → AmbientPoly n :=
  fun i => weightedHomogeneousComponent w (a+w i) (N i)

lemma divergence_component (a : Γ) (N : Fin (n+1) → AmbientPoly n) :
    divergence (numerator w a N)=weightedHomogeneousComponent w a (divergence N) := by
  simp only [divergence,numerator,map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have he := component_pderiv w (N i) (a+w i) i
  simpa only [add_sub_cancel_right] using he.symm

lemma directional_component {P : AmbientPoly n} {b : Γ}
    (hP : P.IsWeightedHomogeneous w b) (a : Γ) (N : Fin (n+1) → AmbientPoly n) :
    directional P (numerator w a N)=weightedHomogeneousComponent w (a+b) (directional P N) := by
  simp only [directional,numerator,map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have he := component_mul w (N i) (pderiv_weighted w hP i) (a+w i)
  have ha : (a+w i)+(b-w i)=a+b := by abel
  rw [ha] at he
  simpa only [mul_comm] using he.symm

lemma divergenceNumerator_component {D : AmbientPoly n} {b : Γ}
    (hD : D.IsWeightedHomogeneous w b) (a : Γ) (N : Fin (n+1) → AmbientPoly n) :
    divergenceNumerator D (numerator w a N)=
      weightedHomogeneousComponent w (a+b) (divergenceNumerator D N) := by
  rw [divergenceNumerator,divergence_component,directional_component w hD]
  rw [divergenceNumerator,map_sub]
  congr 1
  have he := component_mul w (divergence N) hD a
  simpa only [mul_comm] using he.symm

lemma defect_component {F A D : AmbientPoly n} {a b : Γ}
    (hF : F.IsWeightedHomogeneous w 0) (hA : A.IsWeightedHomogeneous w a)
    (hD : D.IsWeightedHomogeneous w b) (q : ℕ) (N : Fin (n+1) → AmbientPoly n) :
    defect F A D q (numerator w (a+b) N)=
      weightedHomogeneousComponent w (a+b+b) (defect F A D q N) := by
  have hAD : (A*D^2).IsWeightedHomogeneous w (a+b+b) := by
    convert hA.mul (hD.pow 2) using 1
    simp only [two_nsmul]
    abel
  have hfirst := component_mul w (directional F N) hD (a+b)
  have hsecond := component_mul w (divergenceNumerator D N) hF (a+b+b)
  rw [add_zero] at hsecond
  have hcast : (q:AmbientPoly n)=C (q:ℂ) := by simp
  have he1 : weightedHomogeneousComponent w (a+b+b)
      ((q:AmbientPoly n)*D*directional F N) =
      (q:AmbientPoly n)*D*weightedHomogeneousComponent w (a+b) (directional F N) := by
    calc
      _ = C (q:ℂ)*weightedHomogeneousComponent w (a+b+b) (D*directional F N) := by
        rw [hcast,mul_assoc,weightedHomogeneousComponent_C_mul]
      _ = C (q:ℂ)*(weightedHomogeneousComponent w (a+b) (directional F N)*D) := by
        rw [mul_comm D (directional F N),hfirst]
      _ = _ := by rw [← hcast,mul_comm _ D,← mul_assoc]
  have he2 : weightedHomogeneousComponent w (a+b+b) (F*divergenceNumerator D N) =
      F*weightedHomogeneousComponent w (a+b+b) (divergenceNumerator D N) := by
    rw [mul_comm F (divergenceNumerator D N),hsecond,mul_comm]
  rw [defect,defect,map_add,map_sub,component_self w hAD,he1,he2]
  rw [directional_component w hF,add_zero,divergenceNumerator_component w hD]

end WeightedProjectionAux


open HodgeComputer MvPolynomial
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

namespace WeightedProjectionAux
variable {n : ℕ} {Γ : Type*} [AddCommGroup Γ]

lemma certificate_projection (w : Fin (n+1) → Γ) {F A D : AmbientPoly n} {a b : Γ}
    {d q : ℕ} {N : Fin (n+1) → AmbientPoly n} {Q : AmbientPoly n}
    (h : Verify F A d q D N Q)
    (hF : F.IsWeightedHomogeneous w 0) (hA : A.IsWeightedHomogeneous w a)
    (hD : D.IsWeightedHomogeneous w b) :
    Verify F A d q D (numerator w (a+b) N) (weightedHomogeneousComponent w (a+b+b) Q) := by
  refine { h with numerator_homogeneous := ?_, identity := ?_ }
  · intro i
    exact preserves_degree w (h.numerator_homogeneous i) _
  · rw [defect_component w hF hA hD,h.identity]
    have hpow : (F^(q+1)).IsWeightedHomogeneous w 0 := by
      simpa only [smul_zero] using hF.pow (q+1)
    have he := component_mul w Q hpow (a+b+b)
    rw [add_zero] at he
    simpa only [mul_comm] using he

lemma exists_weighted_certificate (w : Fin (n+1) → Γ) {F A D : AmbientPoly n} {a b : Γ}
    {d q : ℕ} {N : Fin (n+1) → AmbientPoly n} {Q : AmbientPoly n}
    (h : Verify F A d q D N Q)
    (hF : F.IsWeightedHomogeneous w 0) (hA : A.IsWeightedHomogeneous w a)
    (hD : D.IsWeightedHomogeneous w b) :
    ∃ (M : Fin (n+1) → AmbientPoly n) (S : AmbientPoly n),
      Verify F A d q D M S ∧
      (∀ i, (M i).IsWeightedHomogeneous w (a+b+w i)) ∧
      S.IsWeightedHomogeneous w (a+b+b) := by
  refine ⟨numerator w (a+b) N,weightedHomogeneousComponent w (a+b+b) Q,
    certificate_projection w h hF hA hD,?_,?_⟩
  · intro i
    exact weightedHomogeneousComponent_isWeightedHomogeneous _ _
  · exact weightedHomogeneousComponent_isWeightedHomogeneous _ _

end WeightedProjectionAux

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


end CertificateKoszulAux


open HodgeComputer MvPolynomial RingTheory.Sequence
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

namespace WeightedProjectionAux
variable {n : ℕ} {Γ : Type*} [AddCommGroup Γ]
variable (w : Fin (n+1) → Γ)

lemma preserves_other_weight {Δ : Type*} [AddCommMonoid Δ]
    (v : Fin (n+1) → Δ) {P : AmbientPoly n} {d : Δ}
    (hP : P.IsWeightedHomogeneous v d) (a : Γ) :
    (weightedHomogeneousComponent w a P).IsWeightedHomogeneous v d := by
  classical
  intro m hm
  apply hP
  rw [coeff_weightedHomogeneousComponent] at hm
  split_ifs at hm with h
  · exact hm
  · exact False.elim (hm rfl)

lemma weighted_lifts_differ {F : AmbientPoly n} {d r : ℕ} {a : Γ}
    (hF : F.IsHomogeneous d) (hFw : F.IsWeightedHomogeneous w 0)
    (hreg : IsWeaklyRegular (AmbientPoly n) (List.ofFn (fun i => pderiv i F)))
    (N M : Fin (n+1) → AmbientPoly n)
    (hN : ∀ i, (N i).IsHomogeneous (r+(d-1)))
    (hM : ∀ i, (M i).IsHomogeneous (r+(d-1)))
    (hNw : ∀ i, (N i).IsWeightedHomogeneous w (a+w i))
    (hMw : ∀ i, (M i).IsWeightedHomogeneous w (a+w i))
    (hlift : directional F N=directional F M) :
    ∃ U : Fin (n+1) → Fin (n+1) → AmbientPoly n,
      (∀ i j, (U i j).IsHomogeneous r ∧ (U i j).IsWeightedHomogeneous w (a+w i+w j)) ∧
      ∀ i, N i=M i+∑ j, (U i j-U j i)*pderiv j F := by
  obtain ⟨V,hVd,hV⟩ := CertificateKoszulAux.homogeneous_lifts_differ hF hreg N M hN hM hlift
  let U : Fin (n+1) → Fin (n+1) → AmbientPoly n :=
    fun i j => weightedHomogeneousComponent w (a+w i+w j) (V i j)
  refine ⟨U,?_,?_⟩
  · intro i j
    exact ⟨preserves_other_weight w 1 (hVd i j) _,
      weightedHomogeneousComponent_isWeightedHomogeneous _ _⟩
  · intro i
    have hh := congrArg (weightedHomogeneousComponent w (a+w i)) (hV i)
    rw [component_self w (hNw i),map_add,component_self w (hMw i),map_sum] at hh
    rw [hh]
    congr 1
    apply Finset.sum_congr rfl
    intro j hj
    have he := component_mul w (V i j-V j i) (pderiv_weighted w hFw j) (a+w i+w j)
    have hw : (a+w i+w j)+(0-w j)=a+w i := by abel
    rw [hw,map_sub] at he
    rw [he]
    dsimp only [U]
    have hw' : a+w i+w j=a+w j+w i := by abel
    rw [hw']

end WeightedProjectionAux

open HodgeComputer MvPolynomial RingTheory.Sequence
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

namespace CompleteCertificateAux
variable {n : ℕ} {Γ : Type*} [AddCommGroup Γ]
open WeightedProjectionAux

def upper (U : Fin (n+1) → Fin (n+1) → AmbientPoly n) (i j : Fin (n+1)) : AmbientPoly n :=
  if i<j then U i j-U j i else 0

lemma upper_skew (U : Fin (n+1) → Fin (n+1) → AmbientPoly n) (i j : Fin (n+1)) :
    upper U i j-upper U j i=U i j-U j i := by
  rcases lt_trichotomy i j with h|h|h
  · simp [upper,h,not_lt_of_ge (le_of_lt h)]
  · subst j; simp [upper]
  · simp [upper,h,not_lt_of_ge (le_of_lt h)]

lemma nat_homogeneous {P : AmbientPoly n} {k : ℕ}
    (hP : Homogeneous P (k:ℤ)) : P.IsHomogeneous k := by
  intro m hm
  have he := hP hm
  change Finsupp.weight (fun _ : Fin (n+1) => (1:ℕ)) m=k
  rw [← Finsupp.degree_eq_weight_one]
  exact_mod_cast he

lemma exists_complete_search (w : Fin (n+1) → Γ) {F A D : AmbientPoly n} {a b : Γ}
    {d q r : ℕ} {N : Fin (n+1) → AmbientPoly n} {Q : AmbientPoly n}
    (h : Verify F A d q D N Q) (hd : 0<d) (hq : 0<q)
    (hreg : IsWeaklyRegular (AmbientPoly n) (List.ofFn (fun i => pderiv i F)))
    (hF : F.IsWeightedHomogeneous w 0) (hA : A.IsWeightedHomogeneous w a)
    (hD : D.IsWeightedHomogeneous w b)
    (hr : (D.totalDegree:ℤ)+d*q-n=((r+(d-1):ℕ):ℤ))
    (M : Fin (n+1) → AmbientPoly n)
    (hM : ∀ i, (M i).IsHomogeneous (r+(d-1)))
    (hMw : ∀ i, (M i).IsWeightedHomogeneous w (a+b+w i))
    (hMdir : (q:AmbientPoly n)*directional F M=A*D) :
    ∃ (U : Fin (n+1) → Fin (n+1) → AmbientPoly n) (S : AmbientPoly n),
      (∀ i j, j ≤ i → U i j=0) ∧
      (∀ i j, (U i j).IsHomogeneous r ∧ (U i j).IsWeightedHomogeneous w (a+b+w i+w j)) ∧
      Verify F A d q D (fun i => M i+∑ j, (U i j-U j i)*pderiv j F) S ∧
      divergenceNumerator D (fun i => M i+∑ j, (U i j-U j i)*pderiv j F)=F^q*S := by
  obtain ⟨K,hK,hKdir,hKdiv⟩ := CertificateEulerAux.normalize h hd hq
  let L := numerator w (a+b) K
  let S := weightedHomogeneousComponent w (a+b+b) Q
  have hL : Verify F A d q D L S := certificate_projection w hK hF hA hD
  have hLdir : (q:AmbientPoly n)*directional F L=A*D := by
    have he := congrArg (weightedHomogeneousComponent w (a+b)) hKdir
    have hcast : (q:AmbientPoly n)=C (q:ℂ) := by simp
    rw [hcast,weightedHomogeneousComponent_C_mul,component_self w (hA.mul hD)] at he
    have hc : directional F L=weightedHomogeneousComponent w (a+b) (directional F K) := by
      simpa only [add_zero] using directional_component w hF (a+b) K
    rw [← hcast,← hc] at he
    exact he
  have hLdiv : divergenceNumerator D L=F^q*S := by
    change divergenceNumerator D (numerator w (a+b) K)=_
    rw [divergenceNumerator_component w hD,hKdiv]
    have hpow : (F^q).IsWeightedHomogeneous w 0 := by simpa only [smul_zero] using hF.pow q
    have he := component_mul w Q hpow (a+b+b)
    rw [add_zero] at he
    simpa only [mul_comm] using he
  have hLd (i : Fin (n+1)) : (L i).IsHomogeneous (r+(d-1)) := by
    apply nat_homogeneous
    rw [← hr]
    exact hL.numerator_homogeneous i
  have hLw (i : Fin (n+1)) : (L i).IsWeightedHomogeneous w (a+b+w i) :=
    weightedHomogeneousComponent_isWeightedHomogeneous _ _
  have hq0 : (q:AmbientPoly n)≠0 := by exact_mod_cast (Nat.ne_of_gt hq)
  have hsame : directional F L=directional F M :=
    mul_left_cancel₀ hq0 (hLdir.trans hMdir.symm)
  obtain ⟨U,hUd,hU⟩ := weighted_lifts_differ w h.hypersurface_homogeneous hF hreg
    L M hLd hM hLw hMw hsame
  have hVd (i j : Fin (n+1)) : (upper U i j).IsHomogeneous r ∧
      (upper U i j).IsWeightedHomogeneous w (a+b+w i+w j) := by
    by_cases hij : i<j
    · simp only [upper,if_pos hij]
      refine ⟨(hUd i j).1.sub (hUd j i).1,(hUd i j).2.sub ?_⟩
      have he : a+b+w j+w i=a+b+w i+w j := by abel
      simpa only [he] using (hUd j i).2
    · simp only [upper,if_neg hij]
      exact ⟨isHomogeneous_zero _ _ _,isWeightedHomogeneous_zero _ _ _⟩
  have hLeq : L=(fun i => M i+∑ j, (upper U i j-upper U j i)*pderiv j F) := by
    simpa only [upper_skew] using funext hU
  rw [hLeq] at hL hLdiv
  exact ⟨upper U,S,(fun i j hji => if_neg (not_lt_of_ge hji)),hVd,hL,hLdiv⟩

end CompleteCertificateAux
theorem solution {n : ℕ} {Γ : Type*} [AddCommGroup Γ] (w : Fin (n+1) → Γ) {F A D : AmbientPoly n} {a b : Γ}
    {d q r : ℕ} {N : Fin (n+1) → AmbientPoly n} {Q : AmbientPoly n}
    (h : Verify F A d q D N Q) (hd : 0<d) (hq : 0<q)
    (hreg : IsWeaklyRegular (AmbientPoly n) (List.ofFn (fun i => pderiv i F)))
    (hF : F.IsWeightedHomogeneous w 0) (hA : A.IsWeightedHomogeneous w a)
    (hD : D.IsWeightedHomogeneous w b)
    (hr : (D.totalDegree:ℤ)+d*q-n=((r+(d-1):ℕ):ℤ))
    (M : Fin (n+1) → AmbientPoly n)
    (hM : ∀ i, (M i).IsHomogeneous (r+(d-1)))
    (hMw : ∀ i, (M i).IsWeightedHomogeneous w (a+b+w i))
    (hMdir : (q:AmbientPoly n)*directional F M=A*D) :
    ∃ (U : Fin (n+1) → Fin (n+1) → AmbientPoly n) (S : AmbientPoly n),
      (∀ i j, j ≤ i → U i j=0) ∧
      (∀ i j, (U i j).IsHomogeneous r ∧ (U i j).IsWeightedHomogeneous w (a+b+w i+w j)) ∧
      Verify F A d q D (fun i => M i+∑ j, (U i j-U j i)*pderiv j F) S ∧
      divergenceNumerator D (fun i => M i+∑ j, (U i j-U j i)*pderiv j F)=F^q*S :=
  CompleteCertificateAux.exists_complete_search w h hd hq hreg hF hA hD hr M hM hMw hMdir

#print axioms solution
