-- Prove2me | solution 1 for HatAffineConstantRows.puncturedBox_vanishing_of_totalDegree_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T09:17:46.795289+00:00
-- url     : https://prove2.me/submissions/9db44de5-74c5-4dc3-b215-f7b7ae09f373

import Definitions.Def_HatAffineGenericCore_G2
import Definitions.Def_HatAffineConstantRows_LowDegreeBox
import Theorems.Thm_HatAffineGenericCore_g2_puncturedBox_decomposition_power
import Theorems.Thm_HatAffineGenericCore_mem_puncturedValues
import Theorems.Thm_HatAffineGenericCore_puncturedValues_card
attribute [local simp] HatAffineGenericCore.mem_puncturedValues
attribute [local simp] HatAffineGenericCore.puncturedValues_card


section
open scoped BigOperators
namespace HatAffineConstantRows
universe u
open Finset
open MvPolynomial
private lemma coeff_toMvPolynomial_single
    {R σ : Type*} [CommSemiring R] [DecidableEq σ]
    (p : Polynomial R) (i j : σ) (n : Nat) (hn : 0 < n) :
    MvPolynomial.coeff (Finsupp.single j n)
        (Polynomial.toMvPolynomial i p) =
      if i = j then p.coeff n else 0 := by
  classical
  by_cases hij : i = j
  · subst j
    rw [if_pos rfl, Polynomial.toMvPolynomial_eq_rename_comp]
    let f : Unit → σ := fun _ => i
    have hf : Function.Injective f := fun a b _ => Subsingleton.elim a b
    have hmap :
        (Finsupp.single (default : Unit) n).mapDomain f =
          Finsupp.single i n := by
      simp [f]
    change MvPolynomial.coeff (Finsupp.single i n)
      (MvPolynomial.rename f ((MvPolynomial.uniqueAlgEquiv R Unit).symm p)) =
        p.coeff n
    rw [← hmap, MvPolynomial.coeff_rename_mapDomain f hf]
    simpa only [Finsupp.single_eq_same] using
      (MvPolynomial.coeff_uniqueAlgEquiv_symm
        R p (Finsupp.single (default : Unit) n))
  · rw [if_neg hij, Polynomial.toMvPolynomial_eq_rename_comp]
    change MvPolynomial.coeff (Finsupp.single j n)
      (MvPolynomial.rename (fun _ : Unit => i)
        ((MvPolynomial.uniqueAlgEquiv R Unit).symm p)) = 0
    apply MvPolynomial.coeff_rename_eq_zero
    intro d hd
    exfalso
    have hjrange : j ∉ Set.range (fun _ : Unit => i) := by
      rintro ⟨a, ha⟩
      exact hij ha
    have hz := Finsupp.mapDomain_notin_range d j hjrange
    have heval := congrArg (fun e : σ →₀ Nat => e j) hd
    rw [hz] at heval
    simp only [Finsupp.single_eq_same] at heval
    omega
private lemma polynomial_shifted_power_sub_one_coeff_top
    {K : Type u} [Field K] (a : K) (n : Nat) (hn : 0 < n) :
    (((Polynomial.X - Polynomial.C a) ^ n - 1 : Polynomial K).coeff n) = 1 := by
  have hmonic :
      ((Polynomial.X - Polynomial.C a) ^ n : Polynomial K).Monic :=
    (Polynomial.monic_X_sub_C a).pow n
  have hnat :
      ((Polynomial.X - Polynomial.C a) ^ n : Polynomial K).natDegree = n := by
    simpa using (Polynomial.monic_X_sub_C a).natDegree_pow n
  have htop :
      ((Polynomial.X - Polynomial.C a) ^ n : Polynomial K).coeff n = 1 := by
    simpa only [hnat] using hmonic.coeff_natDegree
  rw [Polynomial.coeff_sub, htop]
  rw [Polynomial.coeff_one, if_neg hn.ne']
  simp
private lemma coeff_puncturedPower_pure
    {K : Type u} [Field K] [Fintype K] {m : Nat}
    (g : Fin m → K) {j k : Fin m}
    (hn : 0 < Fintype.card K - 1) :
    MvPolynomial.coeff (Finsupp.single j (Fintype.card K - 1))
        (HatAffineGenericCore.puncturedPower g k) =
      if k = j then 1 else 0 := by
  let n := Fintype.card K - 1
  have hp :
      HatAffineGenericCore.puncturedPower g k =
        Polynomial.toMvPolynomial k
          ((Polynomial.X - Polynomial.C (g k)) ^ n - 1) := by
    simp [HatAffineGenericCore.puncturedPower, n]
  rw [hp, coeff_toMvPolynomial_single _ k j n hn]
  by_cases hkj : k = j
  · rw [if_pos hkj, if_pos hkj]
    exact polynomial_shifted_power_sub_one_coeff_top (g k) n hn
  · simp [hkj]
end HatAffineConstantRows
end

set_option autoImplicit true
open scoped BigOperators
open HatAffineConstantRows
universe u
open Finset
open MvPolynomial
namespace HatAffineConstantRows
theorem _root_.solution
    {K : Type u} [Field K] [Fintype K] {m : Nat}
    (hm : 1 ≤ m) (hq : 4 ≤ Fintype.card K)
    (g : Fin m → K)
    (P : MvPolynomial (Fin m) K)
    (hdeg : P.totalDegree < Fintype.card K - 1)
    (hvanish :
      ∀ y : Fin m → K,
        (∀ j, y j ≠ g j) →
        MvPolynomial.eval y P = 0) :
    P = 0 := by
  classical
  have hncard : 0 < Fintype.card K - 1 := by
    have hq' := hq
    omega
  let n := Fintype.card K - 1
  have hn : 0 < n := by simpa [n] using hncard
  change P.totalDegree < n at hdeg
  obtain ⟨lambda, hP⟩ :=
    HatAffineGenericCore.g2_puncturedBox_decomposition_power
      hm g P (Nat.le_of_lt hdeg) hvanish
  have hlambda : lambda = 0 := by
    funext j
    have hcoeffP : MvPolynomial.coeff (Finsupp.single j n) P = 0 := by
      apply MvPolynomial.coeff_eq_zero_of_totalDegree_lt
      have hsum :
          ∑ i ∈ (Finsupp.single j n).support,
              (Finsupp.single j n) i = n := by
        rw [Finsupp.support_single j hn.ne']
        simp
      rw [hsum]
      exact hdeg
    have hcoeff := congrArg (MvPolynomial.coeff (Finsupp.single j n)) hP
    rw [hcoeffP] at hcoeff
    have hcoeffPower (k : Fin m) :
        MvPolynomial.coeff (Finsupp.single j n)
            (HatAffineGenericCore.puncturedPower g k) =
          if k = j then 1 else 0 := by
      change MvPolynomial.coeff
          (Finsupp.single j (Fintype.card K - 1))
            (HatAffineGenericCore.puncturedPower g k) =
        if k = j then 1 else 0
      exact coeff_puncturedPower_pure (g := g) hncard
    have hzero : (0 : K) = lambda j := by
      simpa [MvPolynomial.coeff_sum,
        hcoeffPower] using hcoeff
    exact hzero.symm
  simpa [hlambda] using hP
end HatAffineConstantRows
