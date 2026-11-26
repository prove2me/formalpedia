-- Prove2me | solution 1 for MohP3.Gen.mem_of_nsmul_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T21:47:24.59555+00:00
-- url     : https://prove2.me/submissions/8bc419ad-b607-4643-882c-f06f5f747ec2

module
public import Mathlib
public import Definitions.Def_MohP3_Generic

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open MohP3 MohP3.Gen
variable {A : Type*} [CommRing A]
variable (x y z : A)
namespace MohP3.Gen
theorem _root_.solution [Algebra ℚ A] {I : Ideal A} {n : ℕ} (hn : n ≠ 0) {g : A}
    (h : (n : A) * g ∈ I) : g ∈ I := by
  have hcast : ((n : ℕ) : A) = algebraMap ℚ A (n : ℚ) := by
    simp
  have hunit : IsUnit ((n : ℕ) : A) := by
    rw [hcast]
    exact (isUnit_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr hn)).map (algebraMap ℚ A)
  obtain ⟨u, hu⟩ := hunit
  have := Ideal.mul_mem_left I (↑u⁻¹) h
  rwa [← mul_assoc, ← hu, Units.inv_mul, one_mul] at this
end MohP3.Gen
