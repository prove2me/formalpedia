-- Prove2me | solution 1 for MazurProof.N13SexticIrreducible.fModThree_irreducible
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-10-09T03:32:47.268358+00:00
-- url     : https://prove2.me/submissions/5df3ba67-c3e7-4ce3-9d94-4bd55af62e53

import Mathlib
import Definitions.Def_MazurN13_L0

set_option maxHeartbeats 1000000

-- ===== FLT.Assumptions.MazurProof.N13SexticIrreducible =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13SexticIrreducible =====
section
/-!
# Irreducibility of the N13 sextic

The sextic defining the fake two-descent algebra is irreducible over `ℚ`.
We prove this structurally by reduction modulo three.  An irreducible
degree-`d` factor over `𝔽₃` divides `X ^ (3 ^ d) - X`, by applying finite-field
Frobenius in its adjoin-root field.  Three short Bézout identities exclude
degrees one through three, which is the full Rabin test for a sextic.  No
finite-field polynomials are enumerated.
-/
open Polynomial
namespace MazurProof.N13SexticIrreducible
noncomputable section
theorem fModThree_eq :
    fModThree = X ^ 6 + X ^ 5 - X ^ 3 + X ^ 2 - X + 1 := by
  simp [fModThree, fInt]
  have hthree : (3 : (ZMod 3)[X]) = 0 :=
    CharP.cast_eq_zero ((ZMod 3)[X]) 3
  linear_combination (X ^ 5 + 2 * X ^ 4 + X ^ 3 + X) * hthree
theorem fModThree_monic : fModThree.Monic := by
  rw [fModThree_eq]
  monicity!
theorem fModThree_natDegree : fModThree.natDegree = 6 := by
  rw [fModThree_eq]
  compute_degree!
theorem irreducible_dvd_own_frobenius
    {p : (ZMod 3)[X]} (hp : Irreducible p) :
    p ∣ X ^ (3 ^ p.natDegree) - X := by
  letI : Fact (Irreducible p) := ⟨hp⟩
  letI : Module.Finite (ZMod 3) (AdjoinRoot p) :=
    (AdjoinRoot.powerBasis hp.ne_zero).finite
  letI : Finite (AdjoinRoot p) :=
    Module.finite_of_finite (ZMod 3)
  letI : Fintype (AdjoinRoot p) :=
    Fintype.ofFinite (AdjoinRoot p)
  have hcard :
      Fintype.card (AdjoinRoot p) = 3 ^ p.natDegree := by
    rw [Module.card_eq_pow_finrank (K := ZMod 3) (V := AdjoinRoot p),
      (AdjoinRoot.powerBasis hp.ne_zero).finrank, ZMod.card,
      AdjoinRoot.powerBasis_dim]
  have hroot :
      (AdjoinRoot.root p) ^ (3 ^ p.natDegree) =
        AdjoinRoot.root p := by
    rw [← hcard]
    exact FiniteField.pow_card _
  rw [← AdjoinRoot.mk_eq_zero, map_sub, map_pow, AdjoinRoot.mk_X]
  exact sub_eq_zero.mpr hroot
theorem bezout_one :
    bezoutOneA * fModThree + bezoutOneB * (X ^ 3 - X) = 1 := by
  rw [fModThree_eq]
  simp [bezoutOneA, bezoutOneB]
  have hthree : (3 : (ZMod 3)[X]) = 0 :=
    CharP.cast_eq_zero ((ZMod 3)[X]) 3
  linear_combination
    (-X ^ 7 + X ^ 5 - X) * hthree
theorem bezout_two :
    bezoutTwoA * fModThree + bezoutTwoB * (X ^ 9 - X) = 1 := by
  rw [fModThree_eq]
  simp [bezoutTwoA, bezoutTwoB]
  have hthree : (3 : (ZMod 3)[X]) = 0 :=
    CharP.cast_eq_zero ((ZMod 3)[X]) 3
  linear_combination
    (X * (X ^ 9 - X ^ 7 + X ^ 4 - X ^ 2 - 1)) * hthree
theorem bezout_three :
    bezoutThreeA * fModThree + bezoutThreeB * (X ^ 27 - X) = 1 := by
  rw [fModThree_eq]
  simp [bezoutThreeA, bezoutThreeB]
  have hthree : (3 : (ZMod 3)[X]) = 0 :=
    CharP.cast_eq_zero ((ZMod 3)[X]) 3
  linear_combination
    (X ^ 4 * (X ^ 24 + X ^ 22 - X ^ 19 + X ^ 17 - X ^ 13 +
      X ^ 9 - X ^ 8 + X ^ 3 - X ^ 2 + X - 1)) * hthree
theorem coprime_frobenius_one :
    IsCoprime fModThree (X ^ 3 - X) :=
  ⟨bezoutOneA, bezoutOneB, bezout_one⟩
theorem coprime_frobenius_two :
    IsCoprime fModThree (X ^ 9 - X) :=
  ⟨bezoutTwoA, bezoutTwoB, bezout_two⟩
theorem coprime_frobenius_three :
    IsCoprime fModThree (X ^ 27 - X) :=
  ⟨bezoutThreeA, bezoutThreeB, bezout_three⟩
/-- The reduction of the N13 sextic modulo three is irreducible. -/
theorem fModThree_irreducible : Irreducible fModThree := by
  have hf1 : fModThree ≠ 1 := by
    intro h
    have := fModThree_natDegree
    rw [h] at this
    norm_num at this
  rw [fModThree_monic.irreducible_iff_lt_natDegree_lt hf1]
  intro q hq hdeg hqf
  rw [fModThree_natDegree] at hdeg
  have hdeg' : 0 < q.natDegree ∧ q.natDegree ≤ 3 := by
    simpa using (Finset.mem_Ioc.mp hdeg)
  obtain ⟨r, _hrm, hri, hrq⟩ :=
    Polynomial.exists_monic_irreducible_factor q
      (not_isUnit_of_natDegree_pos q hdeg'.1)
  have hrf : r ∣ fModThree :=
    dvd_trans hrq hqf
  have hrle : r.natDegree ≤ 3 :=
    (natDegree_le_of_dvd hrq hq.ne_zero).trans hdeg'.2
  have hrpos : 0 < r.natDegree :=
    hri.natDegree_pos
  have hcases :
      r.natDegree = 1 ∨ r.natDegree = 2 ∨ r.natDegree = 3 := by
    omega
  rcases hcases with hdegree | hdegree | hdegree
  · have hrfrob := irreducible_dvd_own_frobenius hri
    rw [hdegree] at hrfrob
    norm_num at hrfrob
    exact hri.not_isUnit
      (coprime_frobenius_one.isUnit_of_dvd' hrf hrfrob)
  · have hrfrob := irreducible_dvd_own_frobenius hri
    rw [hdegree] at hrfrob
    norm_num at hrfrob
    exact hri.not_isUnit
      (coprime_frobenius_two.isUnit_of_dvd' hrf hrfrob)
  · have hrfrob := irreducible_dvd_own_frobenius hri
    rw [hdegree] at hrfrob
    norm_num at hrfrob
    exact hri.not_isUnit
      (coprime_frobenius_three.isUnit_of_dvd' hrf hrfrob)
end
end MazurProof.N13SexticIrreducible
end

end

theorem solution : type_of% @MazurProof.N13SexticIrreducible.fModThree_irreducible := @MazurProof.N13SexticIrreducible.fModThree_irreducible
