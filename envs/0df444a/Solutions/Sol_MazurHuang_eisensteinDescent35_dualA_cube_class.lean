-- Prove2me | solution 1 for MazurHuang.eisensteinDescent35_dualA_cube_class
-- status  : ACCEPTED   (prove)
-- author  : @Xiang Huang
-- created : 2026-10-06T21:07:25.568766+00:00
-- url     : https://prove2.me/submissions/8360aa71-16be-4ffc-b755-659cef9afa00

/-
3-descent on the dual curve: the descent element is a unit times a cube in the Eisenstein integers.

Author: Xiang Huang
License: Apache-2.0
Source: Xiang Huang's FLT fork, https://github.com/xiangyazi24/FLT,
  commit 51bbb4f191ad0d3753b87123635c100a638ae580
  (Lean v4.31.0-rc2), ported to Lean v4.33.1 / Mathlib 0df444a360ea.
Port repairs inside the source ranges are marked `port v4.33.1` or listed in the
port notes of the staging repository; no statement of a non-private declaration
was changed.

Contents, in order (each source range sits in its own `section`):
  * FLT/Assumptions/MazurProof/RationalPointsX135Descent.lean (cube exponents of a conjugate product, coordinates and norms in Z[omega], the primes 2, 5,
    sqrt(-3), units modulo cubes, n35DualA_three_cubeclasses; the ring, omega, sqrt(-3) and the
    descent element come from the platform definition)
  * the published statement
-/
import Mathlib
import Definitions.Def_MazurHuang_EisensteinDescent35

/- Source: flt@51bbb4f191ad FLT/Assumptions/MazurProof/RationalPointsX135Descent.lean. -/
section

namespace MazurProof.RationalPointsX135

noncomputable section

open scoped NumberField

open UniqueFactorizationMonoid

open MazurHuang.EisensteinDescent35

-- FLT/Assumptions/MazurProof/RationalPointsX135Descent.lean, lines 11-136
/-- A conjugate product which is a cube has cube exponents factor by factor. -/
theorem n35_unit_mul_cube_of_mul_conj_cube
    {R : Type*} [CommRing R] [IsDomain R]
    [UniqueFactorizationMonoid R]
    (conj : R ≃+* R) (hinv : Function.Involutive conj)
    {A M : R} (hA : A ≠ 0) (hEq : A * conj A = M ^ 3)
    (hsep : ∀ p : R, Irreducible p →
      (Associated p (conj p) ∨ ¬(p ∣ A ∧ conj p ∣ A))) :
    ∃ eps : Rˣ, ∃ B : R, A = (eps : R) * B ^ 3 := by
  classical
  letI : StrongNormalizationMonoid R :=
    UniqueFactorizationMonoid.strongNormalizationMonoid
  have hconjA : conj A ≠ 0 := by
    intro h
    apply hA
    apply conj.injective
    simpa using h
  have hM : M ≠ 0 := by
    intro h
    have hz : A * conj A = 0 := by simpa [h] using hEq
    exact (mul_ne_zero hA hconjA) hz
  let fac : R →₀ ℕ := factorization A
  have hfac_dvd : ∀ p : R, 3 ∣ fac p := by
    intro p
    by_cases hp0 : fac p = 0
    · simp [hp0]
    have hpSupp : p ∈ fac.support := Finsupp.mem_support_iff.mpr hp0
    have hpNF : p ∈ normalizedFactors A :=
      Multiset.mem_toFinset.mp (by rw [← support_factorization]; exact hpSupp)
    have hpPrime : Prime p := prime_of_normalized_factor p hpNF
    have hpIrr : Irreducible p := hpPrime.irreducible
    have hpNorm : normalize p = p := normalize_normalized_factor p hpNF
    have hpDivA : p ∣ A := dvd_of_mem_normalizedFactors hpNF
    have hfinProd : FiniteMultiplicity p (A * conj A) :=
      FiniteMultiplicity.of_prime_left hpPrime (mul_ne_zero hA hconjA)
    have hfinM : FiniteMultiplicity p M :=
      FiniteMultiplicity.of_prime_left hpPrime hM
    have hmul : multiplicity p A + multiplicity p (conj A) =
        3 * multiplicity p M := by
      calc
        multiplicity p A + multiplicity p (conj A) =
            multiplicity p (A * conj A) :=
          (multiplicity_mul hpPrime hfinProd).symm
        _ = multiplicity p (M ^ 3) := by rw [hEq]
        _ = 3 * multiplicity p M :=
          FiniteMultiplicity.multiplicity_pow hpPrime hfinM
    have hmap : multiplicity p (conj A) = multiplicity (conj p) A := by
      have h := multiplicity_map_eq conj (a := conj p) (b := A)
      simpa only [hinv p] using h
    have hfacEq : fac p = multiplicity p A := by
      change factorization A p = multiplicity p A
      rw [factorization_eq_count,
        multiplicity_eq_count_normalizedFactors hpIrr hA, hpNorm]
    rw [hfacEq]
    rcases hsep p hpIrr with hpSelf | hpSeparated
    · have hconjMult : multiplicity (conj p) A = multiplicity p A :=
        multiplicity_eq_of_associated_left hpSelf
      rw [hmap, hconjMult] at hmul
      have hthree_two : 3 ∣ 2 * multiplicity p A := by
        refine ⟨multiplicity p M, ?_⟩
        simpa [two_mul] using hmul
      exact (Nat.prime_three.dvd_mul.mp hthree_two).resolve_left (by norm_num)
    · have hnotConj : ¬conj p ∣ A := by
        intro hpConj
        exact hpSeparated ⟨hpDivA, hpConj⟩
      have hzero : multiplicity (conj p) A = 0 :=
        multiplicity_eq_zero.mpr hnotConj
      rw [hmap, hzero, add_zero] at hmul
      exact ⟨multiplicity p M, hmul⟩
  let rootFac : R →₀ ℕ :=
    Finsupp.mapRange (fun n : ℕ => n / 3) (by simp) fac
  have hthree_rootFac : (3 : ℕ) • rootFac = fac := by
    ext p
    simpa only [Finsupp.nsmul_apply, rootFac,
      Finsupp.mapRange_apply, Nat.nsmul_eq_mul] using
      Nat.mul_div_cancel' (hfac_dvd p)
  let s : Multiset R := Finsupp.toMultiset rootFac
  have hroot_support : rootFac.support ⊆ fac.support := by
    dsimp [rootFac]
    exact Finsupp.support_mapRange
  have hsNF : ∀ p ∈ s, p ∈ normalizedFactors A := by
    intro p hp
    have hpRoot : p ∈ rootFac.support := by simpa [s] using hp
    have hpFac : p ∈ fac.support := hroot_support hpRoot
    exact Multiset.mem_toFinset.mp (by rw [← support_factorization]; exact hpFac)
  have hsIrr : ∀ p ∈ s, Irreducible p := by
    intro p hp
    exact irreducible_of_normalized_factor p (hsNF p hp)
  have hsNorm : ∀ p ∈ s, normalize p = p := by
    intro p hp
    exact normalize_normalized_factor p (hsNF p hp)
  let B : R := s.prod
  have hB : B ≠ 0 := by
    dsimp [B]
    apply Multiset.prod_ne_zero
    intro hzero
    exact (hsIrr 0 hzero).ne_zero rfl
  have hnormB : normalizedFactors B = s := by
    calc
      normalizedFactors B = s.map normalize := by
        dsimp [B]
        exact normalizedFactors_prod_eq s hsIrr
      _ = s.map id := by
        apply Multiset.map_congr rfl
        intro p hp
        simpa using hsNorm p hp
      _ = s := by simp
  have hfacB : factorization B = rootFac := by
    change Multiset.toFinsupp (normalizedFactors B) = rootFac
    rw [hnormB]
    change Multiset.toFinsupp (Finsupp.toMultiset rootFac) = rootFac
    exact Finsupp.toMultiset_toFinsupp rootFac
  have hfacCube : factorization (B ^ 3) = factorization A := by
    calc
      factorization (B ^ 3) = (3 : ℕ) • factorization B := factorization_pow
      _ = (3 : ℕ) • rootFac := by rw [hfacB]
      _ = fac := hthree_rootFac
      _ = factorization A := rfl
  have hAssoc : Associated (B ^ 3) A :=
    associated_of_factorization_eq (B ^ 3) A
      (pow_ne_zero 3 hB) hA hfacCube
  rcases hAssoc with ⟨eps, heps⟩
  refine ⟨eps, B, ?_⟩
  calc
    A = B ^ 3 * (eps : R) := heps.symm
    _ = (eps : R) * B ^ 3 := mul_comm _ _

-- FLT/Assumptions/MazurProof/RationalPointsX135Descent.lean, lines 569-576
local instance n35K3_isCyclotomic :
    IsCyclotomicExtension {3} ℚ N35K3 := by
  change IsCyclotomicExtension {3} ℚ (CyclotomicField 3 ℚ)
  exact CyclotomicField.isCyclotomicExtension 3 ℚ

local instance n35O3_isPrincipalIdealRing :
    IsPrincipalIdealRing N35O3 :=
  IsCyclotomicExtension.Rat.three_pid N35K3

-- FLT/Assumptions/MazurProof/RationalPointsX135Descent.lean, lines 656-869
theorem n35O3_exists_coords (x : N35O3) :
    ∃ a b : ℤ, x = (a : N35O3) + (b : N35O3) * n35Omega := by
  let pb := n35Zeta_isPrimitive.integralPowerBasis
  have hdim : pb.dim = 2 := by
    dsimp only [pb]
    rw [IsPrimitiveRoot.integralPowerBasis_dim]
    decide
  let B : Module.Basis (Fin 2) ℤ N35O3 :=
    pb.basis.reindex (finCongr hdim)
  let a : ℤ := B.repr x 0
  let b : ℤ := B.repr x 1
  refine ⟨a, b, ?_⟩
  have hB0 : B 0 = 1 := by
    simp [B, Module.Basis.reindex_apply, PowerBasis.basis_eq_pow]
  have hB1 : B 1 = n35Omega := by
    simp [B, Module.Basis.reindex_apply, PowerBasis.basis_eq_pow, pb,
      IsPrimitiveRoot.integralPowerBasis_gen, n35Omega]
  have hsum := B.sum_repr x
  rw [Fin.sum_univ_two] at hsum
  simpa [a, b, hB0, hB1, Algebra.smul_def] using hsum.symm

def n35NormForm (a b : ℤ) : ℤ := a ^ 2 - a * b + b ^ 2

theorem n35_coord_mul_conj (a b : ℤ) :
    ((a : N35O3) + (b : N35O3) * n35Omega) *
        n35ConjO ((a : N35O3) + (b : N35O3) * n35Omega) =
      (n35NormForm a b : N35O3) := by
  have hs : n35Omega ^ 2 = -n35Omega - 1 := by
    linear_combination n35Omega_relation
  simp only [map_add, map_mul, map_intCast, n35ConjO_omega]
  push_cast
  unfold n35NormForm
  ring_nf
  rw [hs, n35Omega_cube]
  push_cast
  ring

private theorem n35NormForm_nonneg (a b : ℤ) : 0 ≤ n35NormForm a b := by
  have hsq1 : 0 ≤ (2 * a - b) ^ 2 := sq_nonneg _
  have hsq2 : 0 ≤ b ^ 2 := sq_nonneg _
  unfold n35NormForm
  nlinarith

private theorem n35NormForm_eq_zero_iff (a b : ℤ) :
    n35NormForm a b = 0 ↔ a = 0 ∧ b = 0 := by
  constructor
  · intro h
    have hsq1 : 0 ≤ (2 * a - b) ^ 2 := sq_nonneg _
    have hsq2 : 0 ≤ b ^ 2 := sq_nonneg _
    unfold n35NormForm at h
    have hb : b = 0 := by nlinarith
    subst b
    norm_num at h ⊢
    nlinarith
  · rintro ⟨rfl, rfl⟩
    norm_num [n35NormForm]

private theorem n35NormForm_ne_two_mod_three :
    ∀ a b : ZMod 3, a ^ 2 - a * b + b ^ 2 ≠ 2 := by
  decide

theorem n35NormForm_ne_two (a b : ℤ) : n35NormForm a b ≠ 2 := by
  intro h
  apply n35NormForm_ne_two_mod_three (a : ZMod 3) (b : ZMod 3)
  have h' := congrArg (fun z : ℤ => (z : ZMod 3)) h
  simpa [n35NormForm] using h'

theorem n35NormForm_ne_five (a b : ℤ) : n35NormForm a b ≠ 5 := by
  intro h
  apply n35NormForm_ne_two_mod_three (a : ZMod 3) (b : ZMod 3)
  have h' := congrArg (fun z : ℤ => (z : ZMod 3)) h
  norm_num [n35NormForm] at h' ⊢
  exact h'

theorem n35_coord_norm_pos {x : N35O3} {a b : ℤ} (hx : x ≠ 0)
    (hcoord : x = (a : N35O3) + (b : N35O3) * n35Omega) :
    0 < n35NormForm a b := by
  have hn := n35NormForm_nonneg a b
  apply lt_of_le_of_ne hn
  intro hzero
  have hab := (n35NormForm_eq_zero_iff a b).mp hzero.symm
  apply hx
  rw [hcoord, hab.1, hab.2]
  norm_num

theorem n35_isUnit_of_coord_norm_one {x : N35O3} {a b : ℤ}
    (hcoord : x = (a : N35O3) + (b : N35O3) * n35Omega)
    (hnorm : n35NormForm a b = 1) : IsUnit x := by
  apply IsUnit.of_mul_eq_one (n35ConjO x)
  rw [hcoord, n35_coord_mul_conj, hnorm]
  norm_num

theorem n35_coord_norm_mul_eq_sq {x y : N35O3} {a b c d r : ℤ}
    (hx : x = (a : N35O3) + (b : N35O3) * n35Omega)
    (hy : y = (c : N35O3) + (d : N35O3) * n35Omega)
    (hxy : x * y = (r : N35O3)) :
    n35NormForm a b * n35NormForm c d = r ^ 2 := by
  have ho :
      ((n35NormForm a b * n35NormForm c d : ℤ) : N35O3) =
        ((r ^ 2 : ℤ) : N35O3) := by
    push_cast
    rw [← n35_coord_mul_conj a b, ← n35_coord_mul_conj c d,
      ← hx, ← hy]
    calc
      (x * n35ConjO x) * (y * n35ConjO y) =
          (x * y) * n35ConjO (x * y) := by rw [map_mul]; ring
      _ = (r : N35O3) * n35ConjO (r : N35O3) := by rw [hxy]
      _ = (r : N35O3) ^ 2 := by simp; ring
  exact_mod_cast ho

private theorem n35_intCast_not_isUnit {p : ℤ} (hp : 2 ≤ p) :
    ¬IsUnit (p : N35O3) := by
  intro hu
  obtain ⟨v, hv⟩ := isUnit_iff_exists_inv.mp hu
  obtain ⟨c, d, hvcoord⟩ := n35O3_exists_coords v
  have hv0 : v ≠ 0 := by
    intro hz
    rw [hz, mul_zero] at hv
    exact zero_ne_one hv
  have hnormpos := n35_coord_norm_pos hv0 hvcoord
  have hnorm := n35_coord_norm_mul_eq_sq
    (x := (p : N35O3)) (y := v) (a := p) (b := 0)
    (c := c) (d := d) (r := 1) (by ring) hvcoord hv
  have hpform : n35NormForm p 0 = p ^ 2 := by
    simp [n35NormForm]
  rw [hpform] at hnorm
  have hpSq : 4 ≤ p ^ 2 := by nlinarith [sq_nonneg p]
  have hN : 1 ≤ n35NormForm c d := by omega
  have hle : p ^ 2 ≤ p ^ 2 * n35NormForm c d :=
    by simpa using mul_le_mul_of_nonneg_left hN (sq_nonneg p)
  rw [hnorm] at hle
  omega

theorem n35_two_irreducible : Irreducible (2 : N35O3) := by
  rw [irreducible_iff]
  refine ⟨n35_intCast_not_isUnit (by norm_num), ?_⟩
  intro x y hxy
  by_cases hxU : IsUnit x
  · exact Or.inl hxU
  by_cases hyU : IsUnit y
  · exact Or.inr hyU
  exfalso
  obtain ⟨a, b, hxcoord⟩ := n35O3_exists_coords x
  obtain ⟨c, d, hycoord⟩ := n35O3_exists_coords y
  have hx0 : x ≠ 0 := by
    intro hx
    rw [hx, zero_mul] at hxy
    norm_num at hxy
  have hy0 : y ≠ 0 := by
    intro hy
    rw [hy, mul_zero] at hxy
    norm_num at hxy
  have hNxpos := n35_coord_norm_pos hx0 hxcoord
  have hNypos := n35_coord_norm_pos hy0 hycoord
  have hNx1 : n35NormForm a b ≠ 1 := by
    intro h
    exact hxU (n35_isUnit_of_coord_norm_one hxcoord h)
  have hNy1 : n35NormForm c d ≠ 1 := by
    intro h
    exact hyU (n35_isUnit_of_coord_norm_one hycoord h)
  have hprod := n35_coord_norm_mul_eq_sq hxcoord hycoord hxy.symm
  norm_num at hprod
  have hNxlo : 2 ≤ n35NormForm a b := by omega
  have hNylo : 2 ≤ n35NormForm c d := by omega
  have hNx : n35NormForm a b = 2 := by nlinarith
  exact n35NormForm_ne_two a b hNx

theorem n35_five_irreducible : Irreducible (5 : N35O3) := by
  rw [irreducible_iff]
  refine ⟨n35_intCast_not_isUnit (by norm_num), ?_⟩
  intro x y hxy
  by_cases hxU : IsUnit x
  · exact Or.inl hxU
  by_cases hyU : IsUnit y
  · exact Or.inr hyU
  exfalso
  obtain ⟨a, b, hxcoord⟩ := n35O3_exists_coords x
  obtain ⟨c, d, hycoord⟩ := n35O3_exists_coords y
  have hx0 : x ≠ 0 := by
    intro hx
    rw [hx, zero_mul] at hxy
    norm_num at hxy
  have hy0 : y ≠ 0 := by
    intro hy
    rw [hy, mul_zero] at hxy
    norm_num at hxy
  have hNxpos := n35_coord_norm_pos hx0 hxcoord
  have hNypos := n35_coord_norm_pos hy0 hycoord
  have hNx1 : n35NormForm a b ≠ 1 := by
    intro h
    exact hxU (n35_isUnit_of_coord_norm_one hxcoord h)
  have hNy1 : n35NormForm c d ≠ 1 := by
    intro h
    exact hyU (n35_isUnit_of_coord_norm_one hycoord h)
  have hprod := n35_coord_norm_mul_eq_sq hxcoord hycoord hxy.symm
  norm_num at hprod
  have hNxlo : 2 ≤ n35NormForm a b := by omega
  have hNylo : 2 ≤ n35NormForm c d := by omega
  have hNxhi : n35NormForm a b ≤ 12 := by nlinarith
  have hNx : n35NormForm a b = 5 := by
    interval_cases hN : n35NormForm a b <;> omega
  exact n35NormForm_ne_five a b hNx

noncomputable def n35Rho : N35K3 := 1 + n35Zeta

theorem n35Rho_sq : n35Rho ^ 2 = n35Zeta := by
  unfold n35Rho
  linear_combination n35Zeta_relation

theorem n35Rho_cube : n35Rho ^ 3 = -1 := by
  calc
    n35Rho ^ 3 = n35Rho * n35Rho ^ 2 := by ring
    _ = (1 + n35Zeta) * n35Zeta := by rw [n35Rho_sq]; rfl
    _ = -1 := by linear_combination n35Zeta_relation

-- FLT/Assumptions/MazurProof/RationalPointsX135Descent.lean, lines 874-910
theorem n35Omega_sub_one_prime : Prime (n35Omega - 1) := by
  letI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  letI : IsCyclotomicExtension {3 ^ (0 + 1)} ℚ N35K3 := by
    simpa using n35K3_isCyclotomic
  simpa [n35Omega] using
    (IsPrimitiveRoot.zeta_sub_one_prime_of_ne_two
      (p := 3) (k := 0) n35Zeta_isPrimitive (by norm_num))

theorem n35SqrtNegThree_prime : Prime n35SqrtNegThree := by
  have hassoc : Associated (n35Omega - 1) n35SqrtNegThree := by
    refine ⟨-n35ZetaUnit, ?_⟩
    change (n35Omega - 1) * (-n35Omega) = 1 + 2 * n35Omega
    have hs : n35Omega ^ 2 = -n35Omega - 1 := by
      linear_combination n35Omega_relation
    rw [mul_neg]
    change -((n35Omega - 1) * n35Omega) = _
    rw [show (n35Omega - 1) * n35Omega =
      n35Omega ^ 2 - n35Omega by ring, hs]
    ring
  exact (hassoc.prime_iff).mp n35Omega_sub_one_prime

theorem n35K3_unit_mod_cube (u : N35O3ˣ) :
    (∃ v : N35O3ˣ, u = v ^ 3) ∨
      (∃ v : N35O3ˣ, u = n35ZetaUnit * v ^ 3) ∨
      (∃ v : N35O3ˣ, u = n35ZetaUnit ^ 2 * v ^ 3) := by
  have hu := IsCyclotomicExtension.Rat.Three.Units.mem
    n35Zeta_isPrimitive u
  change u ∈ [1, -1, n35ZetaUnit, -n35ZetaUnit,
    n35ZetaUnit ^ 2, -(n35ZetaUnit ^ 2)] at hu
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hu
  rcases hu with h | h | h | h | h | h
  · exact Or.inl ⟨1, by simpa using h⟩
  · exact Or.inl ⟨-1, by rw [h]; ext; simp [pow_succ]⟩
  · exact Or.inr (Or.inl ⟨1, by simpa using h⟩)
  · exact Or.inr (Or.inl ⟨-1, by rw [h]; ext; simp [pow_succ]⟩)
  · exact Or.inr (Or.inr ⟨1, by simpa using h⟩)
  · exact Or.inr (Or.inr ⟨-1, by rw [h]; ext; simp [pow_succ]⟩)

-- FLT/Assumptions/MazurProof/RationalPointsX135Descent.lean, lines 932-1111
@[simp] theorem n35ConjO_dualA (m n d : ℤ) :
    n35ConjO (n35DualA m n d) =
      (n : N35O3) + n35SqrtNegThree *
      (d * (12 * m + 1500 * d ^ 2) : ℤ) := by
  unfold n35DualA
  rw [map_sub, map_intCast, map_mul, n35ConjO_sqrtNegThree,
    map_intCast]
  ring

theorem n35DualA_mul_conj {m n d : ℤ}
    (hcurve : n ^ 2 = m ^ 3 -
      3 * d ^ 2 * (12 * m + 1500 * d ^ 2) ^ 2) :
    n35DualA m n d * n35ConjO (n35DualA m n d) =
      (m : N35O3) ^ 3 := by
  rw [n35ConjO_dualA]
  unfold n35DualA
  have hc := congrArg (fun z : ℤ => (z : N35O3)) hcurve
  push_cast at hc ⊢
  ring_nf
  rw [n35SqrtNegThree_sq]
  linear_combination hc

private theorem n35_nonsymmetric_not_dvd_prime
    {pi r : N35O3} (hpi : Irreducible pi) (hr : Prime r)
    (hrconj : Associated (n35ConjO r) r)
    (hnself : ¬Associated pi (n35ConjO pi)) :
    ¬pi ∣ r := by
  intro hp
  have hpr : Associated pi r :=
    (hpi.dvd_irreducible_iff_associated hr.irreducible).mp hp
  have hcpr : Associated (n35ConjO pi) (n35ConjO r) :=
    hpr.map n35ConjO
  exact hnself (hpr.trans (hcpr.trans hrconj).symm)

private theorem n35_nonsymmetric_not_dvd_two
    {pi : N35O3} (hpi : Irreducible pi)
    (hnself : ¬Associated pi (n35ConjO pi)) : ¬pi ∣ (2 : N35O3) := by
  apply n35_nonsymmetric_not_dvd_prime hpi n35_two_irreducible.prime _ hnself
  have hmap : n35ConjO (2 : N35O3) = 2 := by
    ext
    rw [n35ConjO_coe]
    exact map_ofNat n35ConjK 2
  rw [hmap]

private theorem n35_nonsymmetric_not_dvd_five
    {pi : N35O3} (hpi : Irreducible pi)
    (hnself : ¬Associated pi (n35ConjO pi)) : ¬pi ∣ (5 : N35O3) := by
  apply n35_nonsymmetric_not_dvd_prime hpi n35_five_irreducible.prime _ hnself
  have hmap : n35ConjO (5 : N35O3) = 5 := by
    ext
    rw [n35ConjO_coe]
    exact map_ofNat n35ConjK 5
  rw [hmap]

private theorem n35_nonsymmetric_not_dvd_sqrtNegThree
    {pi : N35O3} (hpi : Irreducible pi)
    (hnself : ¬Associated pi (n35ConjO pi)) :
    ¬pi ∣ n35SqrtNegThree := by
  apply n35_nonsymmetric_not_dvd_prime hpi n35SqrtNegThree_prime _ hnself
  rw [n35ConjO_sqrtNegThree]
  exact Associated.rfl.neg_left

theorem n35DualA_no_common_nonsymmetric_factor
    {m n d : ℤ} (hd : 0 < d) (hcop : Int.gcd m d = 1)
    (hcurve : n ^ 2 = m ^ 3 -
      3 * d ^ 2 * (12 * m + 1500 * d ^ 2) ^ 2)
    {pi : N35O3} (hpi : Irreducible pi)
    (hnself : ¬Associated pi (n35ConjO pi)) :
    ¬(pi ∣ n35DualA m n d ∧ n35ConjO pi ∣ n35DualA m n d) := by
  rintro ⟨hpA, hpcA⟩
  have hpConjA : pi ∣ n35ConjO (n35DualA m n d) := by
    have hmapped := map_dvd n35ConjO hpcA
    simpa only [n35ConjO_involutive pi] using hmapped
  have hp2 : ¬pi ∣ (2 : N35O3) :=
    n35_nonsymmetric_not_dvd_two hpi hnself
  have hpq : ¬pi ∣ n35SqrtNegThree :=
    n35_nonsymmetric_not_dvd_sqrtNegThree hpi hnself
  have hp5 : ¬pi ∣ (5 : N35O3) :=
    n35_nonsymmetric_not_dvd_five hpi hnself
  have hpPrime : Prime pi := hpi.prime
  have hp2n : pi ∣ (2 * n : ℤ) := by
    have hs := dvd_add hpA hpConjA
    rw [n35ConjO_dualA] at hs
    unfold n35DualA at hs
    convert hs using 1 <;> push_cast <;> ring
  have hpn : pi ∣ (n : N35O3) := by
    have hsplit := hpPrime.dvd_mul.mp (by simpa only [Int.cast_mul] using hp2n)
    exact hsplit.resolve_left hp2
  have hpMpow : pi ∣ (m : N35O3) ^ 3 := by
    rw [← n35DualA_mul_conj hcurve]
    exact dvd_mul_of_dvd_left hpA _
  have hpm : pi ∣ (m : N35O3) := hpPrime.dvd_of_dvd_pow hpMpow
  let C : ℤ := d * (12 * m + 1500 * d ^ 2)
  have hp2qC : pi ∣ (2 : N35O3) * n35SqrtNegThree * (C : N35O3) := by
    have hdif := dvd_sub hpA hpConjA
    rw [n35ConjO_dualA] at hdif
    unfold n35DualA at hdif
    dsimp only [C]
    convert hdif.neg_right using 1 <;> push_cast <;> ring
  have hpqC : pi ∣ n35SqrtNegThree * (C : N35O3) :=
    (hpPrime.dvd_mul.mp (by simpa [mul_assoc] using hp2qC)).resolve_left hp2
  have hpC : pi ∣ (C : N35O3) :=
    (hpPrime.dvd_mul.mp hpqC).resolve_left hpq
  have hpd : ¬pi ∣ (d : N35O3) := by
    intro hpd
    have hcopI : IsCoprime (m : N35O3) (d : N35O3) := by
      have hz : IsCoprime m d := Int.isCoprime_iff_gcd_eq_one.mpr hcop
      exact hz.map (Int.castRingHom N35O3)
    exact hpi.not_isUnit (hcopI.isUnit_of_dvd' hpm hpd)
  have hpL : pi ∣ (12 * m + 1500 * d ^ 2 : ℤ) := by
    have hs : pi ∣ (d : N35O3) *
        (12 * m + 1500 * d ^ 2 : ℤ) := by
      simpa [C] using hpC
    exact (hpPrime.dvd_mul.mp hs).resolve_left hpd
  have hp1500d2 : pi ∣ (1500 : N35O3) * (d : N35O3) ^ 2 := by
    have hs := dvd_sub hpL (dvd_mul_of_dvd_right hpm (12 : N35O3))
    convert hs using 1 <;> push_cast <;> ring
  have hp1500 : pi ∣ (1500 : N35O3) := by
    rcases hpPrime.dvd_mul.mp hp1500d2 with hp1500 | hpd2
    · exact hp1500
    · exact (hpd (hpPrime.dvd_of_dvd_pow hpd2)).elim
  have hfactor : (1500 : N35O3) =
      (2 : N35O3) ^ 2 * ((3 : N35O3) * (5 : N35O3) ^ 3) := by norm_num
  rw [hfactor] at hp1500
  rcases hpPrime.dvd_mul.mp hp1500 with hp2sq | hp35
  · exact hp2 (hpPrime.dvd_of_dvd_pow hp2sq)
  · rcases hpPrime.dvd_mul.mp hp35 with hp3 | hp5cube
    · have hpneg3 : pi ∣ -(3 : N35O3) := hp3.neg_right
      have hpq2 : pi ∣ n35SqrtNegThree ^ 2 := by
        rwa [n35SqrtNegThree_sq]
      exact hpq (hpPrime.dvd_of_dvd_pow hpq2)
    · exact hp5 (hpPrime.dvd_of_dvd_pow hp5cube)

theorem n35DualA_unit_mul_cube
    {m n d : ℤ} (hd : 0 < d) (hcop : Int.gcd m d = 1)
    (hcurve : n ^ 2 = m ^ 3 -
      3 * d ^ 2 * (12 * m + 1500 * d ^ 2) ^ 2) :
    ∃ eps : N35O3ˣ, ∃ B : N35O3,
      n35DualA m n d = (eps : N35O3) * B ^ 3 := by
  have hm0 : m ≠ 0 := by
    intro hm
    subst m
    have hd0 : d ≠ 0 := ne_of_gt hd
    nlinarith [sq_nonneg n, sq_pos_of_ne_zero hd0]
  have hA0 : n35DualA m n d ≠ 0 := by
    intro hA
    have hp := n35DualA_mul_conj hcurve
    rw [hA, zero_mul] at hp
    exact (pow_ne_zero 3 (Int.cast_ne_zero.mpr hm0)) hp.symm
  apply n35_unit_mul_cube_of_mul_conj_cube n35ConjO
    n35ConjO_involutive hA0 (n35DualA_mul_conj hcurve)
  intro pi hpi
  by_cases hs : Associated pi (n35ConjO pi)
  · exact Or.inl hs
  · exact Or.inr (n35DualA_no_common_nonsymmetric_factor hd hcop hcurve hpi hs)

theorem n35DualA_three_cubeclasses
    {m n d : ℤ} (hd : 0 < d) (hcop : Int.gcd m d = 1)
    (hcurve : n ^ 2 = m ^ 3 -
      3 * d ^ 2 * (12 * m + 1500 * d ^ 2) ^ 2) :
    (∃ B : N35O3, n35DualA m n d = B ^ 3) ∨
      (∃ B : N35O3, n35DualA m n d = n35ZetaUnit * B ^ 3) ∨
      (∃ B : N35O3, n35DualA m n d = n35ZetaUnit ^ 2 * B ^ 3) := by
  obtain ⟨eps, B, hA⟩ := n35DualA_unit_mul_cube hd hcop hcurve
  rcases n35K3_unit_mod_cube eps with ⟨v, hv⟩ | ⟨v, hv⟩ | ⟨v, hv⟩
  · left
    refine ⟨(v : N35O3) * B, ?_⟩
    rw [hA, hv]
    push_cast
    ring
  · right; left
    refine ⟨(v : N35O3) * B, ?_⟩
    rw [hA, hv]
    push_cast
    ring
  · right; right
    refine ⟨(v : N35O3) * B, ?_⟩
    rw [hA, hv]
    push_cast
    ring


end

end MazurProof.RationalPointsX135

end

open MazurHuang.EisensteinDescent35

theorem solution
    {m n d : ℤ} (hd : 0 < d) (hcop : Int.gcd m d = 1)
    (hcurve : n ^ 2 = m ^ 3 - 3 * d ^ 2 * (12 * m + 1500 * d ^ 2) ^ 2) :
    (∃ B : N35O3, n35DualA m n d = B ^ 3) ∨
      (∃ B : N35O3, n35DualA m n d = n35ZetaUnit * B ^ 3) ∨
      (∃ B : N35O3, n35DualA m n d = n35ZetaUnit ^ 2 * B ^ 3) :=
  MazurProof.RationalPointsX135.n35DualA_three_cubeclasses hd hcop hcurve
