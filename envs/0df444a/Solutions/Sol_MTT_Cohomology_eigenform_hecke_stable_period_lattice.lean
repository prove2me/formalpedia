-- Prove2me | solution 1 for MTT.Cohomology.eigenform_hecke_stable_period_lattice
-- status  : ACCEPTED   (prove)
-- author  : @davidloeffler
-- created : 2026-09-19T21:02:14.413014+00:00
-- url     : https://prove2.me/submissions/2941263d-ea70-47c6-9dc3-329fe9e70884

import Theorems.Thm_MTT_Cohomology_integral_finite_generation
import Theorems.Thm_MTT_Cohomology_base_change
import Theorems.Thm_MTT_Cohomology_integration_map
import Theorems.Thm_MTT_Cohomology_signed_evaluation
import Theorems.Thm_MTT_Cohomology_signed_packet_multiplicity_one
import Theorems.Thm_MTT_Cohomology_eigenclass_descent
import Theorems.Thm_MTT_Cohomology_evaluation_lattice
import Theorems.Thm_MTT_period_vanishing
import Mathlib.RingTheory.Flat.Localization
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.NumberTheory.ModularForms.LevelOne.Basic
import Mathlib.LinearAlgebra.Matrix.FixedDetMatrices

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open scoped BigOperators TensorProduct
open MTT.Cohomology

namespace P2MStable

open MvPolynomial

instance flat_int_rat : Module.Flat ℤ ℚ :=
  IsLocalization.flat ℚ (nonZeroDivisors ℤ)

instance flat_int_of_rat_algebra (K : Type*) [Field K] [Algebra ℚ K] :
    Module.Flat ℤ K :=
  haveI : Module.Free ℚ K := Module.Free.of_divisionRing ℚ K
  haveI : Module.Flat ℚ K := Module.Flat.of_free
  Module.Flat.trans ℤ ℚ K

theorem act_map {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (A : Matrix (Fin 2) (Fin 2) ℤ) (P : Binary R) :
    act A (MvPolynomial.map f P) = MvPolynomial.map f (act A P) := by
  unfold act
  simp only [AlgHom.toLinearMap_apply]
  show MvPolynomial.bind₁ (fun i : Fin 2 => ∑ a : Fin 2,
      (A a i : S) • MvPolynomial.X a) (MvPolynomial.map f P) =
    MvPolynomial.map f (MvPolynomial.bind₁
      (fun i : Fin 2 => ∑ a : Fin 2, (A a i : R) • MvPolynomial.X a) P)
  have hfun : (fun i : Fin 2 =>
      MvPolynomial.map f (∑ a : Fin 2, (A a i : R) • MvPolynomial.X a)) =
      fun i : Fin 2 => ∑ a : Fin 2, (A a i : S) • MvPolynomial.X a := by
    funext i
    simp [MvPolynomial.smul_eq_C_mul]
  rw [MvPolynomial.map_bind₁, hfun]

theorem map_smul_eq {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (a : R) (P : Binary R) :
    MvPolynomial.map f (a • P) = f a • MvPolynomial.map f P := by
  simp [MvPolynomial.smul_eq_C_mul]

theorem map_slash_apply {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (g : Matrix (Fin 2) (Fin 2) ℤ)
    (u : (Cusp × Cusp) → Binary R) (D : Cusp × Cusp) :
    MvPolynomial.map f (slash g u D) =
      slash g (fun E => MvPolynomial.map f (u E)) D := by
  unfold slash
  rw [act_map]

theorem map_primeHecke_apply {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (e : R) (q : ℕ)
    (u : (Cusp × Cusp) → Binary R) (D : Cusp × Cusp) :
    MvPolynomial.map f (primeHecke e q u D) =
      primeHecke (f e) q (fun E => MvPolynomial.map f (u E)) D := by
  simp only [primeHecke, Pi.add_apply, Finset.sum_apply, map_add, map_sum,
    map_slash_apply, Pi.smul_apply, map_smul_eq]

theorem slash_smul {R : Type*} [CommRing R] (g : Matrix (Fin 2) (Fin 2) ℤ)
    (c : R) (u : (Cusp × Cusp) → Binary R) :
    slash g (c • u) = c • slash g u := by
  funext D
  simp [slash]

theorem primeHecke_smul {R : Type*} [CommRing R] (e : R) (q : ℕ) (c : R)
    (u : (Cusp × Cusp) → Binary R) :
    primeHecke e q (c • u) = c • primeHecke e q u := by
  simp only [primeHecke, slash_smul, ← Finset.smul_sum, smul_add, smul_comm e c]

theorem reflection_smul {R : Type*} [CommRing R] (c : R)
    (u : (Cusp × Cusp) → Binary R) :
    reflection (c • u) = c • reflection u := by
  funext D
  simp [reflection]

theorem evaluation_extends {N n : ℕ} {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (ψ : Hc N n R) (φ : Hc N n S) (h : Extends f ψ φ)
    (j : ℕ) (r : ℚ) :
    evaluation j r φ = f (evaluation j r ψ) := by
  show MvPolynomial.coeff _ (φ.val (OnePoint.infty, (r : Cusp))) = _
  rw [h OnePoint.infty ((r : ℚ) : Cusp), MvPolynomial.coeff_map]
  rfl

/-- The exponent vector of `X^j Y^(n-j)`.  This is definitionally the exponent
used by `MTT.Cohomology.evaluation`; the source definition is internal to the
integration node, so we name it locally here. -/
def binaryExponent (n j : ℕ) : Fin 2 →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun i : Fin 2 => if i = 0 then j else n - j)

theorem binaryExponent_inj {n i j : ℕ}
    (h : binaryExponent n i = binaryExponent n j) : i = j := by
  have := congrArg (fun d : Fin 2 →₀ ℕ => d 0) h
  simpa [binaryExponent] using this

theorem degree_binaryExponent {n j : ℕ} (hj : j ≤ n) :
    (binaryExponent n j).degree = n := by
  rw [binaryExponent, Finsupp.degree_eq_sum, Fin.sum_univ_two]
  simp
  omega

theorem eq_binaryExponent_of_degree {n : ℕ} {d : Fin 2 →₀ ℕ}
    (hd : d.degree = n) : d = binaryExponent n (d 0) ∧ d 0 ≤ n := by
  have hsum : d 0 + d 1 = n := by
    rw [← hd, Finsupp.degree_eq_sum, Fin.sum_univ_two]
  refine ⟨?_, by omega⟩
  ext i
  fin_cases i
  · simp [binaryExponent]
  · simp [binaryExponent]
    omega

theorem homogeneous_expansion {R : Type*} [CommRing R] {n : ℕ}
    (P : Binary R) (hP : P ∈ MTT.Cohomology.Sym R n) :
    P = ∑ j ∈ Finset.range (n + 1),
      MvPolynomial.monomial (binaryExponent n j)
        (MvPolynomial.coeff (binaryExponent n j) P) := by
  apply MvPolynomial.ext
  intro d
  rw [MvPolynomial.coeff_sum]
  by_cases hd : d.degree = n
  · obtain ⟨heq, hj⟩ := eq_binaryExponent_of_degree hd
    rw [heq, Finset.sum_eq_single (d 0)]
    · simp
    · intro j hjmem hne
      rw [MvPolynomial.coeff_monomial, if_neg]
      exact fun h => hne (binaryExponent_inj h)
    · exact fun h => (h (Finset.mem_range.mpr (Nat.lt_succ_of_le hj))).elim
  · have hzero : MvPolynomial.coeff d P = 0 :=
      ((MvPolynomial.mem_homogeneousSubmodule n P).mp hP).coeff_eq_zero hd
    rw [hzero]
    symm
    refine Finset.sum_eq_zero fun j hj => ?_
    rw [MvPolynomial.coeff_monomial, if_neg]
    intro h
    apply hd
    rw [← h]
    exact degree_binaryExponent (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))

def DividedMem (L : Submodule ℤ MTT.Qbar) (n : ℕ) (P : Binary MTT.Qbar) : Prop :=
  ∀ j, j ≤ n →
    MvPolynomial.coeff (binaryExponent n j) P / (n.choose j : MTT.Qbar) ∈ L

theorem dividedMem_pair {N n : ℕ} (ψ : Hc N n MTT.Qbar)
    (L : Submodule ℤ MTT.Qbar)
    (hgen : ∀ j r, j ≤ n →
      evaluation j r ψ / (n.choose j : MTT.Qbar) ∈ L)
    (x y : Cusp) : DividedMem L n (ψ.val (x, y)) := by
  have hdiag (z : Cusp) : ψ.val (z, z) = 0 := by
    have h := ψ.2.2.1 z z z
    simpa only [add_eq_right] using h
  have hend : ∀ z : Cusp, DividedMem L n (ψ.val (OnePoint.infty, z)) := by
    intro z
    cases z with
    | none =>
        intro j hj
        change MvPolynomial.coeff (binaryExponent n j)
          (ψ.val (OnePoint.infty, OnePoint.infty)) / _ ∈ L
        rw [hdiag, MvPolynomial.coeff_zero, zero_div]
        exact L.zero_mem
    | some r =>
        intro j hj
        exact hgen j r hj
  intro j hj
  have hcoc := ψ.2.2.1 OnePoint.infty x y
  have heq : ψ.val (x, y) = ψ.val (OnePoint.infty, y) -
      ψ.val (OnePoint.infty, x) := by
    rw [← hcoc]
    abel
  rw [heq, MvPolynomial.coeff_sub, sub_div]
  exact L.sub_mem (hend y j hj) (hend x j hj)

def mono (n b : ℕ) : Binary MTT.Qbar :=
  MvPolynomial.X 0 ^ (n - b) * MvPolynomial.X 1 ^ b

def actAlg (A : Matrix (Fin 2) (Fin 2) ℤ) :
    Binary MTT.Qbar →ₐ[MTT.Qbar] Binary MTT.Qbar :=
  MvPolynomial.aeval fun i : Fin 2 =>
    ∑ a : Fin 2, (A a i : MTT.Qbar) • MvPolynomial.X a

theorem act_eq_actAlg (A : Matrix (Fin 2) (Fin 2) ℤ) (P : Binary MTT.Qbar) :
    act A P = actAlg A P := rfl

theorem binaryExponent_apply_zero (n j : ℕ) : binaryExponent n j 0 = j := by
  simp [binaryExponent]

theorem binaryExponent_apply_one (n j : ℕ) : binaryExponent n j 1 = n - j := by
  simp [binaryExponent]

theorem monomial_binaryExponent {n j : ℕ} (hj : j ≤ n) :
    (MvPolynomial.monomial (binaryExponent n j) 1 : Binary MTT.Qbar) =
      mono n (n - j) := by
  rw [mono, MvPolynomial.monomial_eq,
    Finsupp.prod_fintype _ _ (fun i => by simp), Fin.prod_univ_two,
    binaryExponent_apply_zero, binaryExponent_apply_one]
  have hsub : n - (n - j) = j := by omega
  rw [hsub]
  simp

theorem act_T_zpow_mono (n : ℕ) (h : ℤ) {b : ℕ} (hb : b ≤ n) :
    act (ModularGroup.T ^ h : Matrix.SpecialLinearGroup (Fin 2) ℤ).val (mono n b) =
      ∑ i ∈ Finset.range (b + 1),
        (((b.choose i : ℤ) * h ^ (b - i) : ℤ) : MTT.Qbar) • mono n i := by
  let Tm : Matrix (Fin 2) (Fin 2) ℤ :=
    (ModularGroup.T ^ h : Matrix.SpecialLinearGroup (Fin 2) ℤ).val
  have hX0 : actAlg Tm (MvPolynomial.X 0) = MvPolynomial.X 0 := by
    simp [actAlg, Tm, ModularGroup.coe_T_zpow, Fin.sum_univ_two]
  have hX1 : actAlg Tm (MvPolynomial.X 1) =
      MvPolynomial.X 1 + (h : MTT.Qbar) • MvPolynomial.X 0 := by
    simp [actAlg, Tm, ModularGroup.coe_T_zpow, Fin.sum_univ_two, add_comm]
  rw [act_eq_actAlg, mono, map_mul, map_pow, map_pow]
  change (actAlg Tm (MvPolynomial.X 0)) ^ (n - b) *
    (actAlg Tm (MvPolynomial.X 1)) ^ b = _
  rw [hX0, hX1]
  rw [add_pow, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Finset.mem_range] at hi
  simp only [mono, smul_eq_mul, Int.cast_mul, Int.cast_natCast, Int.cast_pow]
  rw [MvPolynomial.smul_eq_C_mul]
  simp only [mul_pow, ← MvPolynomial.C_pow, ← MvPolynomial.C_mul]
  have hpow : n - i = (n - b) + (b - i) := by omega
  rw [hpow, pow_add]
  simp only [MvPolynomial.smul_eq_C_mul, ← MvPolynomial.C_eq_coe_nat]
  ring_nf
  conv_lhs => rw [mul_assoc, ← MvPolynomial.C_mul]

def basisVec (n j : ℕ) : Binary MTT.Qbar :=
  ((n.choose j : ℕ) : MTT.Qbar) •
    MvPolynomial.monomial (binaryExponent n j) 1

theorem dividedMem_basis_smul {L : Submodule ℤ MTT.Qbar} {n j : ℕ}
    (hj : j ≤ n) {v : MTT.Qbar} (hv : v ∈ L) :
    DividedMem L n (v • basisVec n j) := by
  intro q hq
  by_cases he : binaryExponent n j = binaryExponent n q
  · have hjq : j = q := binaryExponent_inj he
    subst q
    have hc : ((n.choose j : ℕ) : MTT.Qbar) ≠ 0 := by
      exact_mod_cast Nat.choose_ne_zero hj
    simp [basisVec, MvPolynomial.coeff_smul, hc, hv]
  · have he' : binaryExponent n q ≠ binaryExponent n j := Ne.symm he
    simp [basisVec, MvPolynomial.coeff_smul, MvPolynomial.coeff_monomial, he, he', L.zero_mem]

theorem dividedMem_add {L : Submodule ℤ MTT.Qbar} {n : ℕ}
    {P Q : Binary MTT.Qbar} (hP : DividedMem L n P) (hQ : DividedMem L n Q) :
    DividedMem L n (P + Q) := by
  intro j hj
  rw [MvPolynomial.coeff_add, add_div]
  exact L.add_mem (hP j hj) (hQ j hj)

theorem dividedMem_sum {L : Submodule ℤ MTT.Qbar} {n : ℕ}
    {ι : Type*} (s : Finset ι) (P : ι → Binary MTT.Qbar)
    (hP : ∀ i ∈ s, DividedMem L n (P i)) :
    DividedMem L n (∑ i ∈ s, P i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [DividedMem, L.zero_mem]
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha]
      exact dividedMem_add (hP a (Finset.mem_insert_self _ _))
        (ih (fun i hi => hP i (Finset.mem_insert_of_mem hi)))

theorem divided_expansion {n : ℕ} (P : Binary MTT.Qbar)
    (hP : P ∈ MTT.Cohomology.Sym MTT.Qbar n) :
    P = ∑ j ∈ Finset.range (n + 1),
      (MvPolynomial.coeff (binaryExponent n j) P /
        (n.choose j : MTT.Qbar)) • basisVec n j := by
  calc
    P = ∑ j ∈ Finset.range (n + 1),
        MvPolynomial.monomial (binaryExponent n j)
          (MvPolynomial.coeff (binaryExponent n j) P) := homogeneous_expansion P hP
    _ = _ := by
      refine Finset.sum_congr rfl fun j hjmem => ?_
      have hj : j ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hjmem)
      have hc : ((n.choose j : ℕ) : MTT.Qbar) ≠ 0 := by
        exact_mod_cast Nat.choose_ne_zero hj
      simp [basisVec, smul_smul, hc, MvPolynomial.smul_monomial]

theorem choose_mul_disjoint {n i j : ℕ} (hij : i + j ≤ n) :
    n.choose j * (n - j).choose i = n.choose i * (n - i).choose j := by
  have hji : j ≤ i + j := by omega
  have hij' : i ≤ i + j := by omega
  have h1 := Nat.choose_mul (n := n) (k := i + j) (s := j) hji
  have h2 := Nat.choose_mul (n := n) (k := i + j) (s := i) hij'
  have hs : (i + j).choose j = (i + j).choose i := by
    rw [← Nat.choose_symm hji]
    congr
    omega
  rw [hs] at h1
  have hsub1 : i + j - j = i := by omega
  have hsub2 : i + j - i = j := by omega
  rw [hsub1] at h1
  rw [hsub2] at h2
  omega

theorem dividedMem_act_T_basis_smul {L : Submodule ℤ MTT.Qbar}
    {n j : ℕ} (hj : j ≤ n) {v : MTT.Qbar} (hv : v ∈ L) (h : ℤ) :
    DividedMem L n
      (act (ModularGroup.T ^ h : Matrix.SpecialLinearGroup (Fin 2) ℤ).val
        (v • basisVec n j)) := by
  rw [basisVec, smul_smul, monomial_binaryExponent hj, map_smul,
    act_T_zpow_mono n h (Nat.sub_le n j), Finset.smul_sum]
  apply dividedMem_sum
  intro i hi
  have hib : i ≤ n - j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  have hin : i ≤ n := hib.trans (Nat.sub_le n j)
  have hq : n - i ≤ n := Nat.sub_le n i
  have hsum : i + j ≤ n := by omega
  let z : ℤ := ((n - j).choose i : ℤ) * h ^ (n - j - i)
  let z' : ℤ := ((n - i).choose j : ℤ) * h ^ (n - j - i)
  have hv' : ((z' : ℤ) : MTT.Qbar) * v ∈ L := by
    simpa [z', mul_comm] using L.smul_mem z' hv
  have hbase := dividedMem_basis_smul (L := L) hq hv'
  have hmono : mono n i =
      MvPolynomial.monomial (binaryExponent n (n - i)) 1 := by
    symm
    simpa [Nat.sub_sub_self hin] using
      (monomial_binaryExponent (n := n) (j := n - i) hq)
  rw [hmono]
  convert hbase using 1
  simp only [z, z', basisVec, smul_smul, Int.cast_mul, Int.cast_natCast,
    Int.cast_pow]
  congr 1
  have hchoose := choose_mul_disjoint (n := n) (i := i) (j := j) hsum
  have hsymm : n.choose (n - i) = n.choose i := Nat.choose_symm hin
  rw [hsymm]
  have hcoef :
      (n.choose j : MTT.Qbar) * ((n - j).choose i : MTT.Qbar) *
          (h : MTT.Qbar) ^ (n - j - i) =
        (n.choose i : MTT.Qbar) * ((n - i).choose j : MTT.Qbar) *
          (h : MTT.Qbar) ^ (n - j - i) := by
    exact_mod_cast congrArg (fun t : ℕ => t * (h ^ (n - j - i) : ℤ)) hchoose
  calc
    v * (n.choose j : MTT.Qbar) *
        (((n - j).choose i : MTT.Qbar) * (h : MTT.Qbar) ^ (n - j - i)) =
      v * ((n.choose j : MTT.Qbar) * ((n - j).choose i : MTT.Qbar) *
        (h : MTT.Qbar) ^ (n - j - i)) := by ring
    _ = v * ((n.choose i : MTT.Qbar) * ((n - i).choose j : MTT.Qbar) *
        (h : MTT.Qbar) ^ (n - j - i)) := by rw [hcoef]
    _ = (((n - i).choose j : MTT.Qbar) * (h : MTT.Qbar) ^ (n - j - i)) *
        v * (n.choose i : MTT.Qbar) := by ring

theorem dividedMem_act_T {L : Submodule ℤ MTT.Qbar} {n : ℕ}
    {P : Binary MTT.Qbar} (hhom : P ∈ MTT.Cohomology.Sym MTT.Qbar n)
    (hP : DividedMem L n P) (h : ℤ) :
    DividedMem L n
      (act (ModularGroup.T ^ h : Matrix.SpecialLinearGroup (Fin 2) ℤ).val P) := by
  rw [divided_expansion P hhom, map_sum]
  apply dividedMem_sum
  intro j hjmem
  have hj : j ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hjmem)
  simpa only [map_smul] using dividedMem_act_T_basis_smul hj (hP j hj) h

theorem act_S_mono (n : ℕ) {b : ℕ} (hb : b ≤ n) :
    act (ModularGroup.S : Matrix.SpecialLinearGroup (Fin 2) ℤ).val (mono n b) =
      (((-1 : ℤ) ^ b : ℤ) : MTT.Qbar) • mono n (n - b) := by
  let Sm : Matrix (Fin 2) (Fin 2) ℤ :=
    (ModularGroup.S : Matrix.SpecialLinearGroup (Fin 2) ℤ).val
  have hX0 : actAlg Sm (MvPolynomial.X 0) = MvPolynomial.X 1 := by
    simp [actAlg, Sm, ModularGroup.S, Fin.sum_univ_two]
  have hX1 : actAlg Sm (MvPolynomial.X 1) =
      (-1 : MTT.Qbar) • MvPolynomial.X 0 := by
    simp [actAlg, Sm, ModularGroup.S, Fin.sum_univ_two]
  rw [act_eq_actAlg, mono, map_mul, map_pow, map_pow]
  change (actAlg Sm (MvPolynomial.X 0)) ^ (n - b) *
    (actAlg Sm (MvPolynomial.X 1)) ^ b = _
  rw [hX0, hX1]
  simp only [mono, smul_eq_mul, Int.cast_pow, Int.cast_neg, Int.cast_one,
    mul_pow, ← MvPolynomial.C_pow, MvPolynomial.smul_eq_C_mul]
  have hsub : n - (n - b) = b := by omega
  rw [hsub]
  ring

theorem dividedMem_act_S_basis_smul {L : Submodule ℤ MTT.Qbar}
    {n j : ℕ} (hj : j ≤ n) {v : MTT.Qbar} (hv : v ∈ L) :
    DividedMem L n
      (act (ModularGroup.S : Matrix.SpecialLinearGroup (Fin 2) ℤ).val
        (v • basisVec n j)) := by
  have hq : n - j ≤ n := Nat.sub_le n j
  let z : ℤ := (-1 : ℤ) ^ (n - j)
  have hv' : ((z : ℤ) : MTT.Qbar) * v ∈ L := by
    simpa [mul_comm] using L.smul_mem z hv
  have hbase := dividedMem_basis_smul (L := L) hq hv'
  rw [basisVec, smul_smul, monomial_binaryExponent hj, map_smul,
    act_S_mono n (Nat.sub_le n j)]
  convert hbase using 1
  simp only [z, basisVec, smul_smul, Int.cast_pow, Int.cast_neg, Int.cast_one]
  have hsymm : n.choose (n - j) = n.choose j := Nat.choose_symm hj
  rw [hsymm]
  rw [← monomial_binaryExponent hq]
  congr 1 <;> ring

theorem dividedMem_act_S {L : Submodule ℤ MTT.Qbar} {n : ℕ}
    {P : Binary MTT.Qbar} (hhom : P ∈ MTT.Cohomology.Sym MTT.Qbar n)
    (hP : DividedMem L n P) :
    DividedMem L n
      (act (ModularGroup.S : Matrix.SpecialLinearGroup (Fin 2) ℤ).val P) := by
  rw [divided_expansion P hhom, map_sum]
  apply dividedMem_sum
  intro j hjmem
  have hj : j ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hjmem)
  simpa only [map_smul] using dividedMem_act_S_basis_smul hj (hP j hj)

theorem act_mem_sym {n : ℕ} (A : Matrix (Fin 2) (Fin 2) ℤ)
    {P : Binary MTT.Qbar} (hP : P ∈ MTT.Cohomology.Sym MTT.Qbar n) :
    act A P ∈ MTT.Cohomology.Sym MTT.Qbar n := by
  rw [MvPolynomial.mem_homogeneousSubmodule] at hP ⊢
  have hg : ∀ i : Fin 2,
      (∑ a : Fin 2, (A a i : MTT.Qbar) • MvPolynomial.X a :
        Binary MTT.Qbar).IsHomogeneous 1 := by
    intro i
    have hmem : (∑ a : Fin 2, (A a i : MTT.Qbar) • MvPolynomial.X a :
        Binary MTT.Qbar) ∈ MvPolynomial.homogeneousSubmodule (Fin 2) MTT.Qbar 1 :=
      Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _
        (by rw [MvPolynomial.mem_homogeneousSubmodule]
            exact MvPolynomial.isHomogeneous_X _ _)
    exact hmem
  have h := hP.aeval (g := fun i : Fin 2 =>
    (∑ a : Fin 2, (A a i : MTT.Qbar) • MvPolynomial.X a : Binary MTT.Qbar)) hg
  rw [one_mul] at h
  exact h

theorem actAlg_comp (A B : Matrix (Fin 2) (Fin 2) ℤ) :
    (actAlg A).comp (actAlg B) = actAlg (A * B) := by
  apply MvPolynomial.algHom_ext
  intro i
  simp only [AlgHom.comp_apply, actAlg, MvPolynomial.aeval_X, map_sum, map_smul,
    Matrix.mul_apply, Int.cast_sum, Int.cast_mul, Finset.sum_smul,
    Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun a _ => ?_
  rw [mul_comm]

theorem act_act (A B : Matrix (Fin 2) (Fin 2) ℤ) (P : Binary MTT.Qbar) :
    act A (act B P) = act (A * B) P := by
  rw [act_eq_actAlg, act_eq_actAlg, act_eq_actAlg, ← AlgHom.comp_apply, actAlg_comp]

theorem act_one (P : Binary MTT.Qbar) :
    act (1 : Matrix (Fin 2) (Fin 2) ℤ) P = P := by
  rw [act_eq_actAlg]
  have h : actAlg 1 = AlgHom.id MTT.Qbar (Binary MTT.Qbar) := by
    apply MvPolynomial.algHom_ext
    intro i
    simp [actAlg, Matrix.one_apply]
  rw [h]
  rfl

theorem act_S_inv_mono (n : ℕ) {b : ℕ} (hb : b ≤ n) :
    act ((ModularGroup.S : Matrix.SpecialLinearGroup (Fin 2) ℤ)⁻¹).val (mono n b) =
      (((-1 : ℤ) ^ (n - b) : ℤ) : MTT.Qbar) • mono n (n - b) := by
  let Sm : Matrix (Fin 2) (Fin 2) ℤ :=
    ((ModularGroup.S : Matrix.SpecialLinearGroup (Fin 2) ℤ)⁻¹).val
  have hX0 : actAlg Sm (MvPolynomial.X 0) =
      (-1 : MTT.Qbar) • MvPolynomial.X 1 := by
    simp [actAlg, Sm, ModularGroup.S_inv, Fin.sum_univ_two]
  have hX1 : actAlg Sm (MvPolynomial.X 1) = MvPolynomial.X 0 := by
    simp [actAlg, Sm, ModularGroup.S_inv, Fin.sum_univ_two]
  rw [act_eq_actAlg, mono, map_mul, map_pow, map_pow]
  change (actAlg Sm (MvPolynomial.X 0)) ^ (n - b) *
    (actAlg Sm (MvPolynomial.X 1)) ^ b = _
  rw [hX0, hX1]
  simp only [mono, smul_eq_mul, Int.cast_pow, Int.cast_neg, Int.cast_one,
    mul_pow, ← MvPolynomial.C_pow, MvPolynomial.smul_eq_C_mul]
  have hsub : n - (n - b) = b := by omega
  rw [hsub]
  ring

theorem dividedMem_act_S_inv_basis_smul {L : Submodule ℤ MTT.Qbar}
    {n j : ℕ} (hj : j ≤ n) {v : MTT.Qbar} (hv : v ∈ L) :
    DividedMem L n
      (act ((ModularGroup.S : Matrix.SpecialLinearGroup (Fin 2) ℤ)⁻¹).val
        (v • basisVec n j)) := by
  have hq : n - j ≤ n := Nat.sub_le n j
  let z : ℤ := (-1 : ℤ) ^ j
  have hv' : ((z : ℤ) : MTT.Qbar) * v ∈ L := by
    simpa [mul_comm] using L.smul_mem z hv
  have hbase := dividedMem_basis_smul (L := L) hq hv'
  rw [basisVec, smul_smul, monomial_binaryExponent hj, map_smul,
    act_S_inv_mono n (Nat.sub_le n j)]
  convert hbase using 1
  simp only [z, basisVec, smul_smul, Int.cast_pow, Int.cast_neg, Int.cast_one]
  have hsymm : n.choose (n - j) = n.choose j := Nat.choose_symm hj
  have hsub : n - (n - j) = j := by omega
  rw [hsymm, monomial_binaryExponent hq, hsub]
  congr 1 <;> ring

theorem dividedMem_act_S_inv {L : Submodule ℤ MTT.Qbar} {n : ℕ}
    {P : Binary MTT.Qbar} (hhom : P ∈ MTT.Cohomology.Sym MTT.Qbar n)
    (hP : DividedMem L n P) :
    DividedMem L n
      (act ((ModularGroup.S : Matrix.SpecialLinearGroup (Fin 2) ℤ)⁻¹).val P) := by
  rw [divided_expansion P hhom, map_sum]
  apply dividedMem_sum
  intro j hjmem
  have hj : j ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hjmem)
  simpa only [map_smul] using dividedMem_act_S_inv_basis_smul hj (hP j hj)

def Good (L : Submodule ℤ MTT.Qbar) (n : ℕ)
    (g : Matrix.SpecialLinearGroup (Fin 2) ℤ) : Prop :=
  ∀ P : Binary MTT.Qbar, P ∈ MTT.Cohomology.Sym MTT.Qbar n →
    DividedMem L n P → DividedMem L n (act g.val P)

theorem good_one (L : Submodule ℤ MTT.Qbar) (n : ℕ) : Good L n 1 := by
  intro P hhom hP
  simpa only [Matrix.SpecialLinearGroup.coe_one, act_one] using hP

theorem good_mul {L : Submodule ℤ MTT.Qbar} {n : ℕ}
    {g h : Matrix.SpecialLinearGroup (Fin 2) ℤ}
    (hg : Good L n g) (hh : Good L n h) : Good L n (g * h) := by
  intro P hhom hP
  change DividedMem L n (act (g.val * h.val) P)
  rw [← act_act]
  exact hg _ (act_mem_sym h.val hhom) (hh P hhom hP)

def goodSubgroup (L : Submodule ℤ MTT.Qbar) (n : ℕ) :
    Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ) where
  carrier := {g | Good L n g ∧ Good L n g⁻¹}
  one_mem' := by simpa using And.intro (good_one L n) (good_one L n)
  mul_mem' := by
    intro g h hg hh
    refine ⟨good_mul hg.1 hh.1, ?_⟩
    rw [mul_inv_rev]
    exact good_mul hh.2 hg.2
  inv_mem' := by
    intro g hg
    refine ⟨hg.2, ?_⟩
    simpa only [inv_inv] using hg.1

theorem dividedMem_act_SL {L : Submodule ℤ MTT.Qbar} {n : ℕ}
    (g : Matrix.SpecialLinearGroup (Fin 2) ℤ) {P : Binary MTT.Qbar}
    (hhom : P ∈ MTT.Cohomology.Sym MTT.Qbar n) (hP : DividedMem L n P) :
    DividedMem L n (act g.val P) := by
  have hS : ModularGroup.S ∈ goodSubgroup L n := by
    constructor
    · intro Q hQhom hQ
      exact dividedMem_act_S hQhom hQ
    · intro Q hQhom hQ
      exact dividedMem_act_S_inv hQhom hQ
  have hT : ModularGroup.T ∈ goodSubgroup L n := by
    constructor
    · intro Q hQhom hQ
      simpa using dividedMem_act_T hQhom hQ (1 : ℤ)
    · intro Q hQhom hQ
      simpa using dividedMem_act_T hQhom hQ (-1 : ℤ)
  have hcl : Subgroup.closure ({ModularGroup.S, ModularGroup.T} :
      Set (Matrix.SpecialLinearGroup (Fin 2) ℤ)) ≤ goodSubgroup L n :=
    (Subgroup.closure_le (goodSubgroup L n)).mpr (by
      intro x hx
      rcases hx with (rfl | rfl)
      · exact hS
      · exact hT)
  have hgcl : g ∈ Subgroup.closure ({ModularGroup.S, ModularGroup.T} :
      Set (Matrix.SpecialLinearGroup (Fin 2) ℤ)) := by
    rw [SpecialLinearGroup.SL2Z_generators]
    trivial
  exact (hcl hgcl).1 P hhom hP

theorem act_diag_mono (n : ℕ) (a d : ℤ) {b : ℕ} (hb : b ≤ n) :
    act !![a, 0; 0, d] (mono n b) =
      ((a ^ (n - b) * d ^ b : ℤ) : MTT.Qbar) • mono n b := by
  let D : Matrix (Fin 2) (Fin 2) ℤ := !![a, 0; 0, d]
  have hX0 : actAlg D (MvPolynomial.X 0) =
      (a : MTT.Qbar) • MvPolynomial.X 0 := by
    simp [actAlg, D, Fin.sum_univ_two]
  have hX1 : actAlg D (MvPolynomial.X 1) =
      (d : MTT.Qbar) • MvPolynomial.X 1 := by
    simp [actAlg, D, Fin.sum_univ_two]
  rw [act_eq_actAlg, mono, map_mul, map_pow, map_pow]
  change (actAlg D (MvPolynomial.X 0)) ^ (n - b) *
    (actAlg D (MvPolynomial.X 1)) ^ b = _
  rw [hX0, hX1]
  simp only [mono, smul_eq_mul, Int.cast_mul, Int.cast_pow, mul_pow,
    ← MvPolynomial.C_pow, MvPolynomial.smul_eq_C_mul]
  trans MvPolynomial.X 0 ^ (n - b) * MvPolynomial.X 1 ^ b *
      (MvPolynomial.C ((a : MTT.Qbar) ^ (n - b)) *
        MvPolynomial.C ((d : MTT.Qbar) ^ b))
  · ring
  · rw [MvPolynomial.C_mul]
    ring

theorem dividedMem_act_diag_basis_smul {L : Submodule ℤ MTT.Qbar}
    {n j : ℕ} (hj : j ≤ n) {v : MTT.Qbar} (hv : v ∈ L) (a d : ℤ) :
    DividedMem L n (act !![a, 0; 0, d] (v • basisVec n j)) := by
  let z : ℤ := a ^ j * d ^ (n - j)
  have hv' : ((z : ℤ) : MTT.Qbar) * v ∈ L := by
    simpa [mul_comm] using L.smul_mem z hv
  have hbase := dividedMem_basis_smul (L := L) hj hv'
  rw [basisVec, smul_smul, monomial_binaryExponent hj, map_smul,
    act_diag_mono n a d (Nat.sub_le n j)]
  convert hbase using 1
  simp only [z, basisVec, smul_smul, Int.cast_mul, Int.cast_pow]
  have hsub : n - (n - j) = j := by omega
  rw [hsub]
  congr 1
  · ring
  · exact (monomial_binaryExponent hj).symm

theorem dividedMem_act_diag {L : Submodule ℤ MTT.Qbar} {n : ℕ}
    {P : Binary MTT.Qbar} (hhom : P ∈ MTT.Cohomology.Sym MTT.Qbar n)
    (hP : DividedMem L n P) (a d : ℤ) :
    DividedMem L n (act !![a, 0; 0, d] P) := by
  rw [divided_expansion P hhom, map_sum]
  apply dividedMem_sum
  intro j hjmem
  have hj : j ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hjmem)
  simpa only [map_smul] using dividedMem_act_diag_basis_smul hj (hP j hj) a d

def mkGamma0 {N : ℕ} (M : Matrix (Fin 2) (Fin 2) ℤ) (hdet : M.det = 1)
    (hc : (M 1 0 : ZMod N) = 0) : CongruenceSubgroup.Gamma0 N :=
  ⟨⟨M, hdet⟩, CongruenceSubgroup.Gamma0_mem.mpr hc⟩

def linv (N l : ℕ) : ℕ := ((l : ZMod N)⁻¹).val

theorem linv_mul {N l : ℕ} (hN : 0 < N) (hcop : Nat.Coprime l N) :
    ((linv N l : ℕ) : ZMod N) * (l : ZMod N) = 1 := by
  haveI : NeZero N := ⟨hN.ne'⟩
  rw [linv, ZMod.natCast_zmod_val, mul_comm]
  exact ZMod.mul_inv_of_unit _ ((ZMod.isUnit_iff_coprime l N).mpr hcop)

theorem N_dvd_linv_mul {N l : ℕ} (hN : 0 < N) (hcop : Nat.Coprime l N) :
    (N : ℤ) ∣ (linv N l : ℤ) * l - 1 := by
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  push_cast
  rw [linv_mul hN hcop, sub_self]

def sigmaL {N l : ℕ} (hN : 0 < N) (hcop : Nat.Coprime l N) :
    CongruenceSubgroup.Gamma0 N :=
  mkGamma0 !![(linv N l : ℤ), ((linv N l : ℤ) * l - 1) / N;
    (N : ℤ), (l : ℤ)]
    (by
      rw [Matrix.det_fin_two_of]
      have hdiv := Int.mul_ediv_cancel' (N_dvd_linv_mul hN hcop)
      linear_combination -hdiv)
    (by simp)

theorem sigmaL_11 {N l : ℕ} (hN : 0 < N) (hcop : Nat.Coprime l N) :
    (sigmaL hN hcop).val 1 1 = (l : ℤ) := rfl

theorem dividedMem_primeHecke {N n l : ℕ} (hN : 0 < N) (hl : l.Prime)
    (e : DirichletCharacter MTT.Qbar N) (ψ : Hc N n MTT.Qbar)
    (hneb : ∀ γ : CongruenceSubgroup.Gamma0 N, ∀ x y,
      ψ.val (cuspAct γ.val x, cuspAct γ.val y) =
        e (γ.val 1 1 : ZMod N) • act γ.val.val (ψ.val (x, y)))
    (L : Submodule ℤ MTT.Qbar)
    (hgen : ∀ j r, j ≤ n →
      evaluation j r ψ / (n.choose j : MTT.Qbar) ∈ L)
    (D : Cusp × Cusp) : DividedMem L n (primeHecke (e l) l ψ.val D) := by
  have hpair : ∀ x y, DividedMem L n (ψ.val (x, y)) :=
    dividedMem_pair ψ L hgen
  have hfinite : DividedMem L n
      ((∑ b : Fin l, slash !![1, (b.val : ℤ); 0, (l : ℤ)] ψ.val) D) := by
    simp only [Finset.sum_apply]
    apply dividedMem_sum
    intro b hb
    let g : Matrix (Fin 2) (Fin 2) ℤ := !![1, (b.val : ℤ); 0, (l : ℤ)]
    let P : Binary MTT.Qbar := ψ.val (fractional g D.1, fractional g D.2)
    have hPhom : P ∈ MTT.Cohomology.Sym MTT.Qbar n := ψ.2.1 _ _
    have hP : DividedMem L n P := hpair _ _
    have hmat : Matrix.adjugate g =
        (ModularGroup.T ^ (-(b.val : ℤ)) :
          Matrix.SpecialLinearGroup (Fin 2) ℤ).val * !![(l : ℤ), 0; 0, 1] := by
      rw [ModularGroup.coe_T_zpow]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [g, Matrix.adjugate_fin_two, Matrix.mul_apply]
    change DividedMem L n (act (Matrix.adjugate g) P)
    rw [hmat, ← act_act]
    exact dividedMem_act_T
      (act_mem_sym !![(l : ℤ), 0; 0, 1] hPhom)
      (dividedMem_act_diag hPhom hP l 1) (-(b.val : ℤ))
  have hinfty : DividedMem L n
      ((e l • slash !![(l : ℤ), 0; 0, 1] ψ.val) D) := by
    by_cases hdiv : l ∣ N
    · have hezero : e (l : ZMod N) = 0 := by
        rw [show (l : ZMod N) = ((l : ℤ) : ZMod N) by norm_num]
        rw [DirichletCharacter.apply_eq_zero_iff]
        intro hc
        have hldivZ : (l : ℤ) ∣ (N : ℤ) := by exact_mod_cast hdiv
        have hu : IsUnit (l : ℤ) := hc.isUnit_of_dvd hldivZ
        rw [Int.isUnit_iff] at hu
        have hl2 : 2 ≤ l := hl.two_le
        rcases hu with hu | hu <;> omega
      simp [hezero, DividedMem, L.zero_mem]
    · have hcop : Nat.Coprime l N := hl.coprime_iff_not_dvd.mpr hdiv
      let γ : CongruenceSubgroup.Gamma0 N := sigmaL hN hcop
      let g : Matrix (Fin 2) (Fin 2) ℤ := !![(l : ℤ), 0; 0, 1]
      let x : Cusp := fractional g D.1
      let y : Cusp := fractional g D.2
      let P' : Binary MTT.Qbar := ψ.val (cuspAct γ.val x, cuspAct γ.val y)
      have hP'hom : P' ∈ MTT.Cohomology.Sym MTT.Qbar n := ψ.2.1 _ _
      have hP' : DividedMem L n P' := hpair _ _
      have htrans : DividedMem L n
          (act (!![1, 0; 0, (l : ℤ)] * (γ.val⁻¹).val) P') := by
        rw [← act_act]
        exact dividedMem_act_diag
          (act_mem_sym (γ.val⁻¹).val hP'hom)
          (dividedMem_act_SL γ.val⁻¹ hP'hom hP') 1 l
      have hadj : Matrix.adjugate g = !![1, 0; 0, (l : ℤ)] := by
        ext i j
        fin_cases i <;> fin_cases j <;> simp [g, Matrix.adjugate_fin_two]
      have hneb' : P' = e (l : ZMod N) • act γ.val.val (ψ.val (x, y)) := by
        dsimp [P']
        rw [hneb γ x y]
        congr 2
        change (((sigmaL hN hcop).val 1 1 : ℤ) : ZMod N) = (l : ZMod N)
        rw [sigmaL_11]
        norm_num
      have hcancel :
          (!![1, 0; 0, (l : ℤ)] * (γ.val⁻¹).val) * γ.val.val =
            !![1, 0; 0, (l : ℤ)] := by
        rw [Matrix.mul_assoc]
        have hinv : (γ.val⁻¹).val * γ.val.val =
            (1 : Matrix (Fin 2) (Fin 2) ℤ) := by
          change ((γ.val⁻¹ * γ.val).val : Matrix (Fin 2) (Fin 2) ℤ) = _
          simp
        rw [hinv, Matrix.mul_one]
      have heq : (e l • slash g ψ.val) D =
          act (!![1, 0; 0, (l : ℤ)] * (γ.val⁻¹).val) P' := by
        simp only [Pi.smul_apply, slash]
        rw [hadj]
        change e (l : ZMod N) • act !![1, 0; 0, (l : ℤ)] (ψ.val (x, y)) = _
        rw [hneb', map_smul, act_act, hcancel]
      rw [heq]
      exact htrans
  change DividedMem L n
    (((∑ b : Fin l, slash !![1, (b.val : ℤ); 0, (l : ℤ)] ψ.val) D) +
      (e l • slash !![(l : ℤ), 0; 0, 1] ψ.val) D)
  exact dividedMem_add hfinite hinfty

theorem packet_smul {N n : ℕ} {R : Type*} [CommRing R]
    (e : ZMod N → R) (a : ℕ → R) (s : Bool) (φ : Hc N n R)
    (hφ : Packet e a s φ) (c : R) : Packet e a s (c • φ) := by
  refine ⟨?_, ?_, ?_⟩
  · intro q hq
    change primeHecke (e q) q (c • φ.val) = a q • (c • φ.val)
    rw [primeHecke_smul, hφ.1 q hq, smul_smul, smul_smul, mul_comm c]
  · intro γ x y
    change c • φ.val (cuspAct γ.val x, cuspAct γ.val y) =
      e (γ.val 1 1 : ZMod N) • act γ.val.val (c • φ.val (x, y))
    rw [hφ.2.1 γ x y, map_smul, smul_smul, smul_smul, mul_comm c]
  · change reflection (c • φ.val) = (MTT.sign s : R) • (c • φ.val)
    rw [reflection_smul, hφ.2.2, smul_smul, smul_smul, mul_comm c]

theorem packet_of_extends {N n : ℕ}
    (ι : MTT.Qbar →+* ℂ) (e : DirichletCharacter MTT.Qbar N)
    (a : ℕ → MTT.Qbar) (s : Bool)
    (ψ : Hc N n MTT.Qbar) (φ : Hc N n ℂ)
    (hext : Extends ι ψ φ)
    (hφ : Packet (fun d => ι (e d)) (fun q => ι (a q)) s φ) :
    Packet e a s ψ := by
  refine ⟨?_, ?_, ?_⟩
  · intro q hq
    funext D
    apply MvPolynomial.map_injective ι ι.injective
    rw [map_primeHecke_apply]
    have hfun : (fun E => MvPolynomial.map ι (ψ.val E)) = φ.val := by
      funext E
      exact (hext E.1 E.2).symm
    rw [hfun]
    rw [hφ.1 q hq]
    change ι (a q) • φ.val D = MvPolynomial.map ι (a q • ψ.val D)
    rw [map_smul_eq, hext]
  · intro γ x y
    apply MvPolynomial.map_injective ι ι.injective
    rw [map_smul_eq, ← act_map, ← hext, ← hext]
    exact hφ.2.1 γ x y
  · funext D
    apply MvPolynomial.map_injective ι ι.injective
    simp only [reflection]
    rw [← act_map]
    change act !![-1, 0; 0, 1]
      (MvPolynomial.map ι (ψ.val (fractional !![-1, 0; 0, 1] D.1,
        fractional !![-1, 0; 0, 1] D.2))) =
      MvPolynomial.map ι (((MTT.sign s : ℤ) : MTT.Qbar) • ψ.val D)
    rw [map_smul_eq, ← hext, ← hext]
    simpa [reflection] using congrFun hφ.2.2 D

end P2MStable

open P2MStable in
theorem solution
    {N k : ℕ} (hN : 0 < N) (hk : 2 ≤ k)
    (ι : MTT.Qbar →+* ℂ) (f : MTT.Eigenform N k ι)
    (l : ℕ) (hl : l.Prime) :
    ∃ (ψ : Bool → Hc N (k - 2) MTT.Qbar),
      (∀ s, Packet f.epsilon f.coeff s (ψ s)) ∧
      let L : Submodule ℤ MTT.Qbar :=
        Submodule.span ℤ {v : MTT.Qbar | ∃ s j r, j ≤ k - 2 ∧
          v = evaluation j r (ψ s) / ((k - 2).choose j : MTT.Qbar)}
      L ≠ ⊥ ∧ L.FG ∧ ∀ x ∈ L, f.coeff l * x ∈ L := by
  have hZ : Module.Finite ℤ (Hc N (k - 2) ℤ) :=
    MTT.Cohomology.integral_finite_generation hN
  have hQ : BaseChange N (k - 2) MTT.Qbar :=
    MTT.Cohomology.base_change hN _
  have hC : BaseChange N (k - 2) ℂ :=
    MTT.Cohomology.base_change hN _
  obtain ⟨I, -, hT, hI⟩ := MTT.Cohomology.integration_map hN hk
  obtain ⟨φ, hφ⟩ := MTT.Cohomology.signed_evaluation hN hk I hI hT ι f
  have hdesc : ∀ s : Bool, ∃ ω : ℂ, ω ≠ 0 ∧
      ∃ ψ : Hc N (k - 2) MTT.Qbar, Extends ι ψ (ω⁻¹ • φ s) := fun s =>
    MTT.Cohomology.eigenclass_descent hZ hQ hC ι f.epsilon f.coeff s
      (fun a b ha hb =>
        MTT.Cohomology.signed_packet_multiplicity_one hN hk ι f s a b ha hb)
      (φ s) (hφ s).2
  choose ω hω ψ hψ using hdesc
  have hpacket : ∀ s, Packet f.epsilon f.coeff s (ψ s) := by
    intro s
    exact packet_of_extends ι f.epsilon f.coeff s (ψ s) ((ω s)⁻¹ • φ s) (hψ s)
      (packet_smul _ _ _ _ (hφ s).2 (ω s)⁻¹)
  refine ⟨ψ, hpacket, ?_, MTT.Cohomology.evaluation_lattice hZ hQ ψ, ?_⟩
  · intro hL
    have hevalψ : ∀ s j r, j ≤ k - 2 → evaluation j r (ψ s) = 0 := by
      intro s j r hj
      have hmem : evaluation j r (ψ s) / ((k - 2).choose j : MTT.Qbar) ∈
          Submodule.span ℤ {v : MTT.Qbar | ∃ s j r, j ≤ k - 2 ∧
            v = evaluation j r (ψ s) / ((k - 2).choose j : MTT.Qbar)} :=
        Submodule.subset_span ⟨s, j, r, hj, rfl⟩
      rw [hL, Submodule.mem_bot] at hmem
      have hchoose : ((k - 2).choose j : MTT.Qbar) ≠ 0 := by
        exact_mod_cast Nat.choose_ne_zero hj
      exact ((div_eq_zero_iff.mp hmem).resolve_right hchoose)
    have hevalφ : ∀ s j r, j ≤ k - 2 → evaluation j r (φ s) = 0 := by
      intro s j r hj
      have hextval := evaluation_extends ι (ψ s) ((ω s)⁻¹ • φ s) (hψ s) j r
      rw [hevalψ s j r hj, map_zero] at hextval
      rw [map_smul, smul_eq_mul] at hextval
      exact (mul_eq_zero.mp hextval).resolve_left (inv_ne_zero (hω s))
    have hsigned : ∀ s j r, j ≤ k - 2 → MTT.signedIntegral f.form s j r = 0 := by
      intro s j r hj
      have hclass := (hφ s).1 j r hj
      rw [hevalφ s j r hj] at hclass
      have hchoose : ((k - 2).choose j : ℂ) ≠ 0 := by
        exact_mod_cast Nat.choose_ne_zero hj
      exact (mul_eq_zero.mp hclass.symm).resolve_left hchoose
    have hperiod : ∀ j : ℕ, j ≤ k - 2 → ∀ r : ℚ,
        MTT.modularIntegral f.form (Polynomial.X ^ j) r = 0 := by
      intro j hj r
      rw [← show MTT.signedIntegral f.form true j r +
        MTT.signedIntegral f.form false j r =
          MTT.modularIntegral f.form (Polynomial.X ^ j) r by
        simp [MTT.signedIntegral, MTT.sign]
        ring]
      rw [hsigned true j r hj, hsigned false j r hj, add_zero]
    have hfzero : f.form = 0 := MTT.period_vanishing hN hk f.form hperiod
    have hone : (UpperHalfPlane.qExpansion 1 f.form).coeff 1 = 1 := by
      rw [f.coeff_eq 1, f.normalized, map_one]
    rw [hfzero] at hone
    have hzero : (UpperHalfPlane.qExpansion 1
        ((0 : CuspForm (MTT.GammaOne N) (k : ℤ)) : UpperHalfPlane → ℂ)).coeff 1 = 0 := by
      rw [CuspForm.coe_zero, UpperHalfPlane.qExpansion_zero]
      rfl
    exact zero_ne_one (hzero.symm.trans hone)
  · intro x hx
    apply Submodule.span_induction (R := ℤ) (M := MTT.Qbar)
      (s := {v : MTT.Qbar | ∃ s j r, j ≤ k - 2 ∧
        v = evaluation j r (ψ s) / ((k - 2).choose j : MTT.Qbar)})
      (p := fun y hy => f.coeff l * y ∈
      Submodule.span ℤ {v : MTT.Qbar | ∃ s j r, j ≤ k - 2 ∧
        v = evaluation j r (ψ s) / ((k - 2).choose j : MTT.Qbar)})
    · intro y hy
      obtain ⟨s, j, r, hj, rfl⟩ := hy
      let L : Submodule ℤ MTT.Qbar :=
        Submodule.span ℤ {v : MTT.Qbar | ∃ s j r, j ≤ k - 2 ∧
          v = evaluation j r (ψ s) / ((k - 2).choose j : MTT.Qbar)}
      have hgen : ∀ q t, q ≤ k - 2 →
          evaluation q t (ψ s) / ((k - 2).choose q : MTT.Qbar) ∈ L := by
        intro q t hq
        exact Submodule.subset_span ⟨s, q, t, hq, rfl⟩
      have hT := dividedMem_primeHecke hN hl f.epsilon (ψ s)
        (hpacket s).2.1 L hgen (OnePoint.infty, (r : Cusp))
      have heig := congrFun ((hpacket s).1 l hl)
        (OnePoint.infty, (r : Cusp))
      rw [heig] at hT
      have hjmem := hT j hj
      change f.coeff l *
        (evaluation j r (ψ s) / ((k - 2).choose j : MTT.Qbar)) ∈ L
      simpa [MvPolynomial.coeff_smul, evaluation, binaryExponent, smul_eq_mul,
        mul_div_assoc]
        using hjmem
    · simpa using
        (Submodule.zero_mem (Submodule.span ℤ
          {v : MTT.Qbar | ∃ s j r, j ≤ k - 2 ∧
            v = evaluation j r (ψ s) / ((k - 2).choose j : MTT.Qbar)}))
    · intro a b ha hb hma hmb
      rw [mul_add]
      exact Submodule.add_mem _ hma hmb
    · intro a y hy hmy
      have hz := Submodule.smul_mem
        (Submodule.span ℤ {v : MTT.Qbar | ∃ s j r, j ≤ k - 2 ∧
          v = evaluation j r (ψ s) / ((k - 2).choose j : MTT.Qbar)}) a hmy
      simpa [smul_eq_mul, mul_assoc, mul_left_comm] using hz
    · exact hx
