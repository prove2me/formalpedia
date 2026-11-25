-- Prove2me | solution 1 for HatAffineFullTheorem.affine_factor_alignment_of_extends
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T09:25:29.728856+00:00
-- url     : https://prove2.me/submissions/ea285381-461d-43d8-a8eb-49b5ac4bbbd2

import Definitions.Def_HatAffineGenericCore_G2
import Definitions.Def_HatAffineFactorAlignment_FactorAlignment
import Definitions.Def_HatAffineConstantRows_ConstantRows
import Definitions.Def_HatAffineFullTheorem_LeadingClassification
import Theorems.Thm_HatAffineConstantRows_eval_linearForm
import Theorems.Thm_HatAffineConstantRows_linearForm_ne_zero_iff
import Theorems.Thm_HatAffineConstantRows_linearForm_totalDegree_eq_one
import Theorems.Thm_HatAffineConstantRows_no_constant_row_of_extends_affine
import Theorems.Thm_HatAffineFactorAlignment_g3b_factor_alignment
import Theorems.Thm_HatAffineGeneral_extends_iff_coverable
import Theorems.Thm_HatAffineGenericCore_eval_linearForm
import Theorems.Thm_HatAffineGenericCore_g2_puncturedBox_decomposition_power
import Theorems.Thm_HatAffineGenericCore_mem_coeffSupport
import Theorems.Thm_HatAffineGenericCore_mem_puncturedValues
import Theorems.Thm_HatAffineGenericCore_puncturedValues_card
attribute [local simp] HatAffineGenericCore.mem_coeffSupport
attribute [local simp] HatAffineGenericCore.mem_puncturedValues
attribute [local simp] HatAffineGenericCore.puncturedValues_card


section
open scoped BigOperators
namespace HatAffineFullTheorem
universe u
open Finset
open MvPolynomial
open HatAffineGenericCore
private lemma homogeneousComponent_shifted_power
    {K : Type u} [Field K] {m : Nat}
    (j : Fin m) (c : K) (n : Nat) (hn : 0 < n) :
    homogeneousComponent n ((X j - C c) ^ n - 1) = X j ^ n := by
  classical
  have hone :
      homogeneousComponent n (1 : MvPolynomial (Fin m) K) = 0 := by
    rw [homogeneousComponent_of_mem
      (MvPolynomial.isHomogeneous_one (Fin m) K)]
    simp [hn.ne']
  rw [map_sub, hone, sub_zero, sub_eq_add_neg, add_pow, map_sum]
  calc
    (∑ k ∈ Finset.range (n + 1),
        homogeneousComponent n
          (X j ^ k * (-C c) ^ (n - k) *
            (n.choose k : MvPolynomial (Fin m) K))) =
        ∑ k ∈ Finset.range (n + 1),
          if k = n then X j ^ n else 0 := by
      apply Finset.sum_congr rfl
      intro k hk
      have hx :
          (X j ^ k : MvPolynomial (Fin m) K).IsHomogeneous k :=
        MvPolynomial.isHomogeneous_X_pow j k
      have hc :
          ((-C c) ^ (n - k) : MvPolynomial (Fin m) K).IsHomogeneous 0 := by
        have hc0 :
            (-C c : MvPolynomial (Fin m) K).IsHomogeneous 0 := by
          simpa using MvPolynomial.isHomogeneous_C (Fin m) (-c)
        simpa using hc0.pow (n - k)
      have hchoose :
          ((n.choose k : MvPolynomial (Fin m) K)).IsHomogeneous 0 := by
        simpa using
          MvPolynomial.isHomogeneous_C (Fin m) (n.choose k : K)
      have hterm :
          (X j ^ k * (-C c) ^ (n - k) *
            (n.choose k : MvPolynomial (Fin m) K) :
            MvPolynomial (Fin m) K).IsHomogeneous k := by
        simpa using (hx.mul hc).mul hchoose
      rw [homogeneousComponent_of_mem hterm]
      by_cases hkn : k = n
      · subst k
        simp
      · simp [hkn, Ne.symm hkn]
    _ = X j ^ n := by simp
private lemma homogeneousComponent_puncturedPower
    {K : Type u} [Field K] [Fintype K] {m : Nat}
    (g : Fin m → K) (j : Fin m) :
    homogeneousComponent (Fintype.card K - 1)
        (puncturedPower g j) =
      X j ^ (Fintype.card K - 1) := by
  have hn : 0 < Fintype.card K - 1 := by
    have hcard : 1 < Fintype.card K := Fintype.one_lt_card
    omega
  simpa only [puncturedPower] using
    homogeneousComponent_shifted_power j (g j)
      (Fintype.card K - 1) hn
private lemma genericLinearForm_isHomogeneous
    {K : Type u} [Field K] {m : Nat} (a : Fin m → K) :
    (linearForm a).IsHomogeneous 1 := by
  classical
  rw [linearForm]
  apply MvPolynomial.IsHomogeneous.sum
  intro j hj
  exact MvPolynomial.isHomogeneous_C_mul_X (a j) j
end HatAffineFullTheorem
end

set_option autoImplicit true
open scoped BigOperators
open HatAffineFullTheorem
universe u
open Finset
open MvPolynomial
open HatAffineGenericCore
namespace HatAffineFullTheorem
theorem _root_.solution
    {K : Type u} [Field K] [Fintype K] {m : Nat}
    (hm : 1 ≤ m) (hq : 4 ≤ Fintype.card K)
    (A : Fin (Fintype.card K - 1) → Fin m → K)
    (b : Fin (Fintype.card K - 1) → K)
    (F :
      (Fin m → K) →
      Fin (Fintype.card K - 1) → K)
    (hrealize : HatAffineConstantRows.AffineRealizes A b F)
    (hext : HatAffineGeneral.Extends F) :
    ∃ lambda : Fin m → K,
      HatAffineFactorAlignment.GenericTypeI A lambda ∨
      HatAffineFactorAlignment.GenericTypeII A lambda := by
  classical
  let P : MvPolynomial (Fin m) K := ∏ i, linearForm (A i)
  have hrows : ∀ i, A i ≠ 0 :=
    HatAffineConstantRows.no_constant_row_of_extends_affine
      hm hq A b F hrealize hext
  have hlinear_ne : ∀ i, linearForm (A i) ≠ 0 := by
    intro i
    simpa only [HatAffineGenericCore.linearForm,
      HatAffineConstantRows.linearForm] using
      (HatAffineConstantRows.linearForm_ne_zero_iff (A i)).mpr (hrows i)
  have hPne : P ≠ 0 := by
    change (∏ i, linearForm (A i)) ≠ 0
    exact Finset.prod_ne_zero_iff.mpr fun i hi => hlinear_ne i
  have hlinear_degree : ∀ i, (linearForm (A i)).totalDegree = 1 := by
    intro i
    simpa only [HatAffineGenericCore.linearForm,
      HatAffineConstantRows.linearForm] using
      HatAffineConstantRows.linearForm_totalDegree_eq_one (A i) (hrows i)
  have hPdeg : P.totalDegree ≤ Fintype.card K - 1 := by
    calc
      P.totalDegree ≤
          ∑ i : Fin (Fintype.card K - 1),
            (linearForm (A i)).totalDegree := by
        simpa only [P] using
          MvPolynomial.totalDegree_finsetProd
            (Finset.univ : Finset (Fin (Fintype.card K - 1)))
            (fun i => linearForm (A i))
      _ = Fintype.card K - 1 := by simp [hlinear_degree]
  have hPhomogeneous :
      @MvPolynomial.IsHomogeneous (Fin m) K
        ((inferInstance : CommRing K).toCommSemiring)
        P (Fintype.card K - 1) := by
    have hprod :
        @MvPolynomial.IsHomogeneous (Fin m) K
          ((inferInstance : CommRing K).toCommSemiring)
          (∏ i : Fin (Fintype.card K - 1), linearForm (A i))
          (∑ i : Fin (Fintype.card K - 1), (1 : Nat)) :=
      MvPolynomial.IsHomogeneous.prod
        (Finset.univ : Finset (Fin (Fintype.card K - 1)))
        (fun i => linearForm (A i)) (fun _ => (1 : Nat))
        (fun i hi => genericLinearForm_isHomogeneous (A i))
    have hsum :
        (∑ i : Fin (Fintype.card K - 1), (1 : Nat)) =
          Fintype.card K - 1 := by simp
    rw [hsum] at hprod
    simpa only [P] using hprod
  have hcovers := (HatAffineGeneral.extends_iff_coverable F).mp hext
  obtain ⟨g, hg⟩ := hcovers b
  have hvanish :
      ∀ y : Fin m → K,
        (∀ j, y j ≠ g j) → MvPolynomial.eval y P = 0 := by
    intro y hy
    have hleft : ∃ i, F y i = b i := by
      by_contra hnone
      have hybad : y ∈ HatAffineGeneral.BadSet F b := by
        intro i hi
        exact hnone ⟨i, hi⟩
      obtain ⟨j, hj⟩ := hg y hybad
      exact hy j hj
    obtain ⟨i, hi⟩ := hleft
    have hsum : (∑ j, A i j * y j) = 0 := by
      exact add_right_cancel
        (by simpa only [zero_add] using (hrealize y i).symm.trans hi)
    change MvPolynomial.eval y (∏ i, linearForm (A i)) = 0
    rw [map_prod]
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simpa only [HatAffineGenericCore.eval_linearForm] using hsum
  obtain ⟨lambda, hdecomposition⟩ :=
    HatAffineGenericCore.g2_puncturedBox_decomposition_power
      hm g P hPdeg hvanish
  have hidentity : P = diagonalForm lambda := by
    let H := @MvPolynomial.homogeneousComponent (Fin m) K
      ((inferInstance : CommRing K).toCommSemiring)
      (Fintype.card K - 1)
    have hPcomponent : H P = P := by
      exact homogeneousComponent_eq_self hPhomogeneous
    have hcomponent := congrArg
      (fun Q : MvPolynomial (Fin m) K => H Q)
      hdecomposition
    calc
      P = H P := hPcomponent.symm
      _ = H (∑ j, C (lambda j) * puncturedPower g j) := hcomponent
      _ = ∑ j, C (lambda j) * X j ^ (Fintype.card K - 1) := by
        dsimp only [H]
        simp only [map_sum, homogeneousComponent_C_mul,
          homogeneousComponent_puncturedPower]
      _ = diagonalForm lambda := by rfl
  have hlambda : lambda ≠ 0 := by
    intro hlambda0
    apply hPne
    rw [hidentity, hlambda0]
    simp [diagonalForm]
  refine ⟨lambda, ?_⟩
  exact HatAffineFactorAlignment.g3b_factor_alignment
    hm (by omega) A lambda hrows hlambda hidentity
end HatAffineFullTheorem
