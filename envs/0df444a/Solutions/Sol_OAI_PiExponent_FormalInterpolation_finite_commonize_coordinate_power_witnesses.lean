-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.finite_commonize_coordinate_power_witnesses
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T19:47:47.033218+00:00
-- url     : https://prove2.me/submissions/5b9b14d0-c699-4153-b8c7-2f0034fff0d9

import Definitions.Def_OAI_PiExponent_WeightedIdealCurveCriterion
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_finite_positive_exponents_have_common_multiple
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_coordinate_power_witness_scale

open OAI.PiExponent.FormalInterpolation

theorem solution {ι : Type} [Fintype ι] {R : Type} [CommSemiring R]
    (I : Ideal R) (X : ι → R) (w : ι → Real) (rho eps : Real)
    (heps : 0 < eps)
    (hcoord : ∀ i : ι, ∃ s n : Nat,
      0 < s ∧ 0 < n ∧ X i ^ n ∈ I ^ s ∧
        (n : Real) * w i < (s : Real) * (rho + eps / 2)) :
    ∃ s : Nat, 0 < s ∧ ∃ n : ι → Nat,
      (∀ i, 0 < n i) ∧
      (∀ i, X i ^ n i ∈ I ^ s) ∧
      (∀ i, (n i : Real) * w i < (s : Real) * (rho + eps / 2)) := by
  classical
  let s : ι → Nat := fun i => Classical.choose (hcoord i)
  let n : ι → Nat := fun i => Classical.choose (Classical.choose_spec (hcoord i))
  have hs : ∀ i, 0 < s i := by
    intro i
    exact (Classical.choose_spec (Classical.choose_spec (hcoord i))).1
  obtain ⟨S, hS, hdiv⟩ :=
    OAI.PiExponent.FormalInterpolation.finite_positive_exponents_have_common_multiple s hs
  refine ⟨S, hS, fun i => n i * (S / s i), ?_, ?_, ?_⟩
  · intro i
    have hdata := Classical.choose_spec (Classical.choose_spec (hcoord i))
    have hn : 0 < n i := hdata.2.1
    have hle : s i ≤ S := Nat.le_of_dvd hS (hdiv i)
    have hk : 0 < S / s i := Nat.div_pos hle (hs i)
    exact Nat.mul_pos hn hk
  · intro i
    have hdata := Classical.choose_spec (Classical.choose_spec (hcoord i))
    have hmem : X i ^ n i ∈ I ^ s i := hdata.2.2.1
    have hn : 0 < n i := hdata.2.1
    have hle : s i ≤ S := Nat.le_of_dvd hS (hdiv i)
    have hk : 0 < S / s i := Nat.div_pos hle (hs i)
    have hscaled :=
      OAI.PiExponent.FormalInterpolation.coordinate_power_witness_scale I (X i) (w i)
        (rho + eps / 2) (s i) (n i) (S / s i) (hs i) hn hk hmem hdata.2.2.2
    have hpow : s i * (S / s i) = S := Nat.mul_div_cancel' (hdiv i)
    simpa [hpow] using hscaled.2.1
  · intro i
    have hdata := Classical.choose_spec (Classical.choose_spec (hcoord i))
    have hn : 0 < n i := hdata.2.1
    have hle : s i ≤ S := Nat.le_of_dvd hS (hdiv i)
    have hk : 0 < S / s i := Nat.div_pos hle (hs i)
    have hscaled :=
      OAI.PiExponent.FormalInterpolation.coordinate_power_witness_scale I (X i) (w i)
        (rho + eps / 2) (s i) (n i) (S / s i) (hs i) hn hk hdata.2.2.1 hdata.2.2.2
    have hpow : s i * (S / s i) = S := Nat.mul_div_cancel' (hdiv i)
    have hcast : (s i : Real) * ((S / s i : Nat) : Real) = (S : Real) := by
      exact_mod_cast hpow
    simpa only [Nat.cast_mul, hcast] using hscaled.2.2