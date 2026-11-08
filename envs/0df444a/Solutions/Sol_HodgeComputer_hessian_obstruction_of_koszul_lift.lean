-- Prove2me | solution 1 for HodgeComputer.hessian_obstruction_of_koszul_lift
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T13:10:53.120889+00:00
-- url     : https://prove2.me/submissions/e7d53918-8b2c-48f5-82b5-50e43775a0ff

import Definitions.Def_DiamondCertificate
import Mathlib.RingTheory.MvPolynomial.EulerIdentity
import Mathlib.RingTheory.Ideal.Quotient.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

noncomputable section

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

theorem solution {n : ℕ} {F A : HodgeComputer.AmbientPoly n} {d : ℕ}
    (hF : F.IsHomogeneous d) (hd : 0 < d)
    (c : Fin (n+1) → HodgeComputer.AmbientPoly n)
    (U : Fin (n+1) → Fin (n+1) → HodgeComputer.AmbientPoly n)
    (hres : F ∣ HodgeComputer.divergenceNumerator (HodgeComputer.directional F c)
      (fun i => A*c i + ∑ j, (U i j-U j i)*MvPolynomial.pderiv j F)) :
    A*(∑ i, ∑ j, c i*c j*MvPolynomial.pderiv i (MvPolynomial.pderiv j F)) ∈
      Ideal.span (Set.range (fun i => MvPolynomial.pderiv i F)) :=
  CertificateJacobianAux.koszul_lift_hessian hF hd c U hres

#print axioms solution
