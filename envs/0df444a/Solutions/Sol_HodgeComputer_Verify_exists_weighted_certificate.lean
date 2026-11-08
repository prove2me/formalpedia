-- Prove2me | solution 1 for HodgeComputer.Verify.exists_weighted_certificate
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T13:32:19.180208+00:00
-- url     : https://prove2.me/submissions/46f860f0-3367-4842-a040-d9d3fc051537

import Definitions.Def_DiamondCertificate
import Mathlib.Tactic.Abel

noncomputable section

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

theorem solution {n : ℕ} {Γ : Type*} [AddCommGroup Γ]
    (w : Fin (n+1) → Γ) {F A D : HodgeComputer.AmbientPoly n} {a b : Γ}
    {d q : ℕ} {N : Fin (n+1) → HodgeComputer.AmbientPoly n} {Q : HodgeComputer.AmbientPoly n}
    (h : HodgeComputer.Verify F A d q D N Q)
    (hF : F.IsWeightedHomogeneous w 0) (hA : A.IsWeightedHomogeneous w a)
    (hD : D.IsWeightedHomogeneous w b) :
    ∃ (M : Fin (n+1) → HodgeComputer.AmbientPoly n) (S : HodgeComputer.AmbientPoly n),
      HodgeComputer.Verify F A d q D M S ∧
      (∀ i, (M i).IsWeightedHomogeneous w (a+b+w i)) ∧
      S.IsWeightedHomogeneous w (a+b+b) :=
  WeightedProjectionAux.exists_weighted_certificate w h hF hA hD

#print axioms solution
