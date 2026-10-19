-- Prove2me | solution 2 for OAI.CirculantHadamard.binary_residue_contradiction
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T11:22:06.218553+00:00
-- url     : https://prove2.me/submissions/c2843027-c1c5-4ea6-9a03-282cb629b998

-- Generated from openai/math@1581d4c lean/OAI/LinearAlgebra/CirculantHadamard/BinaryResidue.lean:L139-L198
-- (upload_full_project.md Phase 4): solution for node OAI.CirculantHadamard.binary_residue_contradiction. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_CirculantHadamard
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_Basic
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_Witnesses
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_MatrixBridge
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclicRing
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclicNorm
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclicProjection
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_LocalDVR
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_IntegerTwoLocal
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclicEvaluation
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclicPolynomial
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_RamifiedConjugation
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclotomicIntegerEvaluation
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_DyadicRemainder
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_RamifiedEisenstein
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_RamifiedLocal
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_OrderHalving
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_BinaryBlocks
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_BinaryCoefficients
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclotomicRings
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_PrimeComponents
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_PrimeCharacterEvaluations
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_BinaryEvaluation
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_LocalizationMaps
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_BinaryLocalization
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_BinaryLocalRing
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_AlternatingProducts
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_BinaryProductTransport
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_FirstOrderResidue
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_BinaryResidue
import Theorems.Thm_OAI_CirculantHadamard_binary_signed_product_residue_one
import Theorems.Thm_OAI_CirculantHadamard_first_order_sum_eq_zero_of_prod_eq_one

-- ---- from OAI.LinearAlgebra.CirculantHadamard.ResidueTorsion ----
namespace OAI

universe uR uK

/-!
# Torsion in the kernel of a residue map

The geometric-sum argument works for any ring homomorphism from a domain
to a field of characteristic `p`. In a local-ring application the map is
the residue homomorphism; the domain itself need not have characteristic `p`.
-/

namespace CirculantHadamard

open scoped BigOperators

variable {R : Type uR} {K : Type uK} [CommRing R] [IsDomain R] [Field K]

/-- A root whose image is one is trivial if one of its torsion exponents
is not divisible by the target characteristic. -/
theorem eq_one_of_residue_one_of_not_dvd {p m : ℕ} [CharP K p]
    (f : R →+* K) (z : R) (hmap : f z = 1) (hpow : z ^ m = 1)
    (hm : ¬ p ∣ m) : z = 1 := by
  by_contra hne
  have hprod : (∑ i ∈ Finset.range m, z ^ i) * (z - 1) = 0 := by
    rw [geom_sum_mul, hpow, sub_self]
  have hsum : (∑ i ∈ Finset.range m, z ^ i) = 0 :=
    (mul_eq_zero.mp hprod).resolve_right (sub_ne_zero.mpr hne)
  have hcast : (m : K) = 0 := by
    have h := congrArg f hsum
    simpa only [map_sum, map_pow, hmap, one_pow, Finset.sum_const,
      Finset.card_range, nsmul_eq_mul, mul_one, map_zero] using h
  exact hm ((CharP.cast_eq_zero_iff K p m).mp hcast)

/-- Coprime-order torsion in the residue-one subgroup is trivial. The
exponent need not be the exact order. -/
theorem eq_one_of_residue_one_of_coprime {p m : ℕ} [CharP K p]
    (f : R →+* K) (z : R) (hp : p.Prime) (hmap : f z = 1)
    (hpow : z ^ m = 1) (hcop : m.Coprime p) : z = 1 := by
  exact eq_one_of_residue_one_of_not_dvd f z hmap hpow
    (hp.coprime_iff_not_dvd.mp hcop.symm)

/-- The characteristic-two consequence needed for the two alternating
products: a unit of odd torsion exponent and residue one equals one. -/
theorem units_eq_one_of_residue_one_of_odd [CharP K 2]
    (f : R →+* K) (u : Rˣ) (hmap : f (u : R) = 1)
    (hfinite : ∃ m : ℕ, 0 < m ∧ Odd m ∧ u ^ m = 1) : u = 1 := by
  obtain ⟨m, _, hm, hu⟩ := hfinite
  have hpow : (u : R) ^ m = 1 := by
    simpa only [Units.val_pow_eq_pow_val, Units.val_one] using
      congrArg (fun v : Rˣ => (v : R)) hu
  apply Units.ext
  exact eq_one_of_residue_one_of_coprime f (u : R) Nat.prime_two hmap hpow
    hm.coprime_two_right

end CirculantHadamard

end OAI

-- ---- from OAI.LinearAlgebra.CirculantHadamard.BinaryResidue ----
namespace OAI

universe uO uk uIota

namespace CirculantHadamard

open scoped BigOperators

variable {O : Type uO} [CommRing O]

theorem binary_ratio_r (c d : Oˣ) (a b : O)
    (hc : (c : O) = a + b) (hd : (d : O) = a - b) :
    ((d * c⁻¹ : Oˣ) : O) = 1 + (2 : O) * binaryLr c b := by
  have hc' : (a + b) * (↑(c⁻¹) : O) = 1 := by
    rw [← hc]
    exact c.mul_inv
  calc
    ((d * c⁻¹ : Oˣ) : O) =
        (a + b) * (↑(c⁻¹) : O) + 2 * (-b * (↑(c⁻¹) : O)) := by
      change (d : O) * (↑(c⁻¹) : O) = _
      rw [hd]
      ring
    _ = 1 + (2 : O) * binaryLr c b := by rw [hc']; rfl

theorem binary_ratio_w (c g : Oˣ) (a b J U i : O)
    (hc : (c : O) = a + b)
    (hg : (g : O) = a + i * b - ((1 + i) * J + 2 * U))
    (hi : i ^ 2 = -1) :
    ((g * c⁻¹ : Oˣ) : O) = 1 + (1 + i) * binaryLw c i b J U := by
  have hc' : (a + b) * (↑(c⁻¹) : O) = 1 := by
    rw [← hc]
    exact c.mul_inv
  have hi' : i * i = -1 := by simpa only [pow_two] using hi
  calc
    ((g * c⁻¹ : Oˣ) : O) =
        (a + b) * (↑(c⁻¹) : O) + (1 + i) * binaryLw c i b J U -
          (i * i + 1) * (b + U) * (↑(c⁻¹) : O) := by
      change (g : O) * (↑(c⁻¹) : O) = _
      rw [hg]
      unfold binaryLw
      ring
    _ = 1 + (1 + i) * binaryLw c i b J U := by rw [hc', hi']; ring

/-- This identity is exact before applying the residue map. -/
theorem binaryLr_add_binaryLw (c : Oˣ) (i b J U : O) :
    binaryLr c b + binaryLw c i b J U =
      -J * (↑(c⁻¹) : O) - (1 - i) * (b + U) * (↑(c⁻¹) : O) := by
  unfold binaryLr binaryLw
  ring

/-- Nonvanishing of `2` also makes the second first-order parameter nonzero. -/
theorem binary_one_add_i_ne_zero (i : O) (hi : i ^ 2 = -1)
    (h2 : (2 : O) ≠ 0) : 1 + i ≠ 0 := by
  have hi' : i * i = -1 := by simpa only [pow_two] using hi
  have hfactor : (1 + i) * (1 - i) = (2 : O) := by
    calc
      (1 + i) * (1 - i) = 1 - i * i := by ring
      _ = 2 := by rw [hi']; ring
  intro hzero
  apply h2
  rw [← hfactor, hzero, zero_mul]

section Domain

variable [IsDomain O]

end Domain

section Residue

variable {k : Type uk} [Field k] [charTwo : CharP k 2]

/-- The two coefficients have residues summing to the residue of `J / c`. -/
theorem binary_residue_sum (φ : O →+* k) (c : Oˣ) (i b J U : O)
    (hi : φ i = 1) :
    φ (binaryLr c b) + φ (binaryLw c i b J U) =
      φ (J * (↑(c⁻¹) : O)) := by
  rw [← map_add, binaryLr_add_binaryLw]
  simp [hi, CharTwo.neg_eq]

variable [IsDomain O]

/-- The same-residue-field contradiction for a finite signed family of
binary decompositions. All arithmetic input to the concrete application is
explicit: unit decompositions, a square root of `-1`, odd torsion of both
signed products, and a nonzero signed `J / c` residue sum. -/
theorem binary_residue_contradiction {ι : Type uIota}
    (φ : O →+* k) (i : O) (hi : i ^ 2 = -1) (hφi : φ i = 1)
    (h2 : (2 : O) ≠ 0) (s : Finset ι) (ε : ι → ℤ)
    (c d g : ι → Oˣ) (a b J U : ι → O)
    (hc : ∀ j ∈ s, (c j : O) = a j + b j)
    (hd : ∀ j ∈ s, (d j : O) = a j - b j)
    (hg : ∀ j ∈ s,
      (g j : O) = a j + i * b j - ((1 + i) * J j + 2 * U j))
    (hrOdd : ∃ m : ℕ, 0 < m ∧ Odd m ∧
      (∏ j ∈ s, (d j * (c j)⁻¹) ^ (ε j)) ^ m = 1)
    (hwOdd : ∃ m : ℕ, 0 < m ∧ Odd m ∧
      (∏ j ∈ s, (g j * (c j)⁻¹) ^ (ε j)) ^ m = 1)
    (hnonzero : (∑ j ∈ s, (ε j : k) * φ (J j * (↑((c j)⁻¹) : O))) ≠ 0) :
    False := by
  have hφ2 : φ (2 : O) = 0 := by
    calc
      φ (2 : O) = φ (1 + 1) := by congr 1; ring
      _ = (1 : k) + 1 := by simp only [map_add, map_one]
      _ = 0 := CharTwo.add_self_eq_zero 1
  have hφpi : φ (1 + i) = 0 := by
    rw [map_add, map_one, hφi]
    exact CharTwo.add_self_eq_zero 1
  have hr (j : ι) (hj : j ∈ s) :
      ((d j * (c j)⁻¹ : Oˣ) : O) = 1 + (2 : O) * binaryLr (c j) (b j) :=
    binary_ratio_r (c j) (d j) (a j) (b j) (hc j hj) (hd j hj)
  have hw (j : ι) (hj : j ∈ s) :
      ((g j * (c j)⁻¹ : Oˣ) : O) =
        1 + (1 + i) * binaryLw (c j) i (b j) (J j) (U j) :=
    binary_ratio_w (c j) (g j) (a j) (b j) (J j) (U j) i (hc j hj) (hg j hj) hi
  have hrMap (j : ι) (hj : j ∈ s) : φ ((d j * (c j)⁻¹ : Oˣ) : O) = 1 := by
    rw [hr j hj, map_add, map_one, map_mul, hφ2, zero_mul, add_zero]
  have hwMap (j : ι) (hj : j ∈ s) : φ ((g j * (c j)⁻¹ : Oˣ) : O) = 1 := by
    rw [hw j hj, map_add, map_one, map_mul, hφpi, zero_mul, add_zero]
  have hrOne : (∏ j ∈ s, (d j * (c j)⁻¹) ^ (ε j)) = 1 :=
    units_eq_one_of_residue_one_of_odd φ _
      (binary_signed_product_residue_one φ s (fun j => d j * (c j)⁻¹) ε hrMap) hrOdd
  have hwOne : (∏ j ∈ s, (g j * (c j)⁻¹) ^ (ε j)) = 1 :=
    units_eq_one_of_residue_one_of_odd φ _
      (binary_signed_product_residue_one φ s (fun j => g j * (c j)⁻¹) ε hwMap) hwOdd
  have hrSum := first_order_sum_eq_zero_of_prod_eq_one φ (2 : O) h2 hφ2 s
    (fun j => d j * (c j)⁻¹) (fun j => binaryLr (c j) (b j)) ε hr hrOne
  have hwSum := first_order_sum_eq_zero_of_prod_eq_one φ (1 + i)
    (binary_one_add_i_ne_zero i hi h2) hφpi s
    (fun j => g j * (c j)⁻¹) (fun j => binaryLw (c j) i (b j) (J j) (U j)) ε hw hwOne
  apply hnonzero
  calc
    (∑ j ∈ s, (ε j : k) * φ (J j * (↑((c j)⁻¹) : O))) =
        ∑ j ∈ s, ((ε j : k) * φ (binaryLr (c j) (b j)) +
          (ε j : k) * φ (binaryLw (c j) i (b j) (J j) (U j))) := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [← mul_add, binary_residue_sum φ (c j) i (b j) (J j) (U j) hφi]
    _ = (∑ j ∈ s, (ε j : k) * φ (binaryLr (c j) (b j))) +
        ∑ j ∈ s, (ε j : k) * φ (binaryLw (c j) i (b j) (J j) (U j)) :=
      Finset.sum_add_distrib
    _ = 0 := by rw [hrSum, hwSum, add_zero]

end Residue

end CirculantHadamard

end OAI

-- ---- platform node ----
open OAI OAI.CirculantHadamard
open scoped BigOperators


theorem solution.{uO,uk,uIota} : type_of% @_root_.OAI.CirculantHadamard.binary_residue_contradiction.{uO,uk,uIota} := @_root_.OAI.CirculantHadamard.binary_residue_contradiction.{uO,uk,uIota}
