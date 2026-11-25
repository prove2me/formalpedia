-- Prove2me | solution 1 for GlobalTheory.FlatFibreRegular.mem_map_mul_of_mul_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T15:43:41.404587+00:00
-- url     : https://prove2.me/submissions/ada283ee-51aa-4234-9d5e-6296293de8e3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsReducedAlgebraOfSmoothOfIsNoetherianRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SmoothAlgebraLocalizationEqZeroOfAvoidFibreMinim
import Theorems.Thm_GlobalTheory_FlatFibreRegular_exists_minimal_generators
import Theorems.Thm_GlobalTheory_restrictPoints_val
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.restrictPoints_val



set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits
open scoped TensorProduct
open GlobalTheory GlobalTheory.FlatFibreRegular
namespace GlobalTheory.FlatFibreRegular
theorem _root_.solution {A L : Type} [CommRing A] [CommRing L] [Algebra A L] [Module.Flat A L]
    (𝔭 : Ideal A) [𝔭.IsPrime] (hu : ∀ s ∉ 𝔭, IsUnit (algebraMap A L s))
    (g : L) (hg : ∀ y, g * y ∈ 𝔭.map (algebraMap A L) → y ∈ 𝔭.map (algebraMap A L))
    (I : Ideal A) (hI : I.FG) (y : L) (hy : y ∈ I.map (algebraMap A L))
    (hgy : g * y ∈ (I * 𝔭).map (algebraMap A L)) : y ∈ (I * 𝔭).map (algebraMap A L) := by
  classical
  obtain ⟨S, hSI, hSgen, hrel⟩ := exists_minimal_generators 𝔭 I hI
  set J := 𝔭.map (algebraMap A L) with hJdef
  let v : S → L := fun i => algebraMap A L i
  have hspan : I.map (algebraMap A L) ≤ Ideal.span (Set.range v) := by
    rw [Ideal.map_le_iff_le_comap]
    intro x hx
    obtain ⟨s, hs, hsx⟩ := hSgen x hx
    have h1 : algebraMap A L (s * x) ∈ Ideal.span (Set.range v) := by
      have : Ideal.map (algebraMap A L) (Ideal.span (S : Set A)) ≤ Ideal.span (Set.range v) := by
        rw [Ideal.map_span]
        apply Ideal.span_mono
        rintro _ ⟨a, ha, rfl⟩
        exact ⟨⟨a, ha⟩, rfl⟩
      exact this (Ideal.mem_map_of_mem _ hsx)
    rw [map_mul] at h1
    obtain ⟨t, ht⟩ := (hu s hs).exists_left_inv
    have := Ideal.mul_mem_left _ t h1
    rwa [← mul_assoc, ht, one_mul] at this
  have hvI : ∀ i, v i ∈ I.map (algebraMap A L) := fun i => Ideal.mem_map_of_mem _ (hSI i.2)
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun L).1 (hspan hy)
  have hgy' : g * y ∈ J • Ideal.span (Set.range v) := by
    have h1 : (I * 𝔭).map (algebraMap A L) ≤ J • Ideal.span (Set.range v) := by
      rw [Ideal.smul_eq_mul, Ideal.map_mul, mul_comm]
      exact Ideal.mul_mono_right hspan
    exact h1 hgy
  obtain ⟨w, hwJ, hw⟩ := (Submodule.mem_ideal_smul_span_iff_exists_sum J v _).1 hgy'
  rw [Finsupp.sum_fintype _ _ (by simp)] at hw
  have hrel0 : ∑ i : S, (i : A) • (g * c i - w i) = 0 := by
    have e1 : ∑ i : S, (i : A) • (g * c i) = g * y := by
      rw [← hc, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [smul_eq_mul, v]; simp only [Algebra.smul_def]; ring
    have e2 : ∑ i : S, (i : A) • w i = g * y := by
      rw [← hw]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [smul_eq_mul, v]; simp only [Algebra.smul_def]; ring
    simp only [smul_sub, Finset.sum_sub_distrib, e1, e2, sub_self]
  obtain ⟨k, a, z, hx, hf⟩ := Module.Flat.isTrivialRelation_of_sum_smul_eq_zero (R := A) (M := L)
    (f := fun i : S => (i : A)) (x := fun i => g * c i - w i) hrel0
  have ha : ∀ i j, a i j ∈ 𝔭 := fun i j =>
    hrel (fun i => a i j) (by rw [← hf j]; exact Finset.sum_congr rfl fun i _ => mul_comm _ _) i
  have hcJ : ∀ i, c i ∈ J := by
    intro i
    apply hg
    have h1 : g * c i - w i ∈ J := by
      have hxi := hx i
      dsimp only at hxi
      rw [hxi]
      exact Ideal.sum_mem _ fun j _ => by
        rw [Algebra.smul_def]; exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ (ha i j))
    simpa using Ideal.add_mem _ h1 (hwJ i)
  rw [← hc, Ideal.map_mul]
  exact Ideal.sum_mem _ fun i _ => by
    rw [smul_eq_mul, mul_comm (c i)]; exact Ideal.mul_mem_mul (hvI i) (hcJ i)
end GlobalTheory.FlatFibreRegular
