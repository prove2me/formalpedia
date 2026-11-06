-- Prove2me | solution 1 for OAI.FiniteFieldSieve.character_sum_le_additive_energy
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:04:26.06427+00:00
-- url     : https://prove2.me/submissions/74baa3a8-4cd0-4880-b614-2fc27ae55c8f

import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_ExponentialSmoothing
import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_LogProfiles
import Theorems.Thm_OAI_FiniteFieldSieve_primitive_gauss_norm_sq
import Theorems.Thm_OAI_FiniteFieldSieve_character_gauss_expansion
section
namespace OAI
open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
namespace ShortDraftMellin
end ShortDraftMellin
namespace FiniteRingSieve
variable {R : Type*} [CommRing R] [Fintype R] [DecidableEq R]
attribute [local instance] logProfilesFintypeMulChar
end FiniteRingSieve
namespace FiniteFieldSieve
variable {F : Type*} [Field F] [Fintype F]
private theorem complex_sum_cauchy {ι : Type*} (S : Finset ι) (x y : ι → ℂ) :
    ‖∑ i ∈ S, x i * y i‖ ^ 2 ≤
      (∑ i ∈ S, ‖x i‖ ^ 2) * ∑ i ∈ S, ‖y i‖ ^ 2 := by
  have htri : ‖∑ i ∈ S, x i * y i‖ ≤ ∑ i ∈ S, ‖x i‖ * ‖y i‖ := by
    simpa only [norm_mul] using norm_sum_le S (fun i => x i * y i)
  have hsquare := (sq_le_sq₀ (norm_nonneg _) (Finset.sum_nonneg
      (fun i hi => mul_nonneg (norm_nonneg _) (norm_nonneg _)))).mpr htri
  exact hsquare.trans (Finset.sum_mul_sq_le_sq_mul_sq S (fun i => ‖x i‖)
    (fun i => ‖y i‖))
private theorem character_norm_le_one (χ : MulChar F ℂ) (u : F) : ‖χ u‖ ≤ 1 := by
  let : Fintype Fˣ := Fintype.ofFinite _
  by_cases hu : u = 0
  · rw [hu, MulChar.map_zero]
    simp
  · let v : Fˣ := Units.mk0 u hu
    have hv : (v : F) = u := rfl
    rw [← hv]
    have h : ‖χ (v : F)‖ = 1 := by
      simpa only [MulChar.coe_equivToUnitHom] using
        Complex.norm_eq_one_of_mem_rootsOfUnity (χ.apply_mem_rootsOfUnity v)
    exact h.le
end FiniteFieldSieve
namespace ProductResidueSieve
variable {R S : Type*} [CommRing R] [CommRing S]
end ProductResidueSieve
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open scoped ContDiff Manifold
namespace FourierBridge
end FourierBridge
end OAI
end

set_option autoImplicit false
open OAI
open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open OAI.FiniteFieldSieve
variable {F : Type*} [Field F] [Fintype F]
namespace OAI.FiniteFieldSieve
theorem _root_.solution {ι : Type*} (I : Finset ι)
    (n : ι → F) (a : ι → ℂ) (χ : MulChar F ℂ) (ψ : AddChar F ℂ)
    (hχ : χ ≠ 1) (hψ : ψ.IsPrimitive) :
    ‖∑ i ∈ I, a i * χ (n i)‖ ^ 2 ≤
      ∑ u : F, ‖∑ i ∈ I, a i * ψ (n i * u)‖ ^ 2 := by
  classical
  let g := gaussSum χ⁻¹ ψ
  let T (u : F) := ∑ i ∈ I, a i * ψ (n i * u)
  let S := ∑ i ∈ I, a i * χ (n i)
  have hsum : g * S = ∑ u : F, χ⁻¹ u * T u := by
    calc
      g * S = ∑ i ∈ I, a i * (χ (n i) * g) := by
        rw [mul_comm g S, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = ∑ i ∈ I, a i *
          (∑ u : F, χ⁻¹ u * ψ (n i * u)) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [character_gauss_expansion χ ψ hχ (n i)]
      _ = ∑ u : F, χ⁻¹ u * T u := by
        simp_rw [Finset.mul_sum]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro u _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring
  have hmass : (∑ u : F, ‖χ⁻¹ u‖ ^ 2) ≤ (Fintype.card F : ℝ) := by
    calc
      _ ≤ ∑ u : F, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro u _
        have hu := character_norm_le_one χ⁻¹ u
        nlinarith [norm_nonneg (χ⁻¹ u)]
      _ = _ := by simp
  have hcauchy := complex_sum_cauchy (Finset.univ : Finset F)
    (fun u => χ⁻¹ u) T
  have hgauss : ‖g‖ ^ 2 = (Fintype.card F : ℝ) := by
    exact primitive_gauss_norm_sq χ⁻¹ ψ (by simpa using hχ) hψ
  have hnonneg : 0 ≤ ∑ u : F, ‖T u‖ ^ 2 :=
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hpre : (Fintype.card F : ℝ) * ‖S‖ ^ 2 ≤
      (Fintype.card F : ℝ) * ∑ u : F, ‖T u‖ ^ 2 := by
    calc
      _ = ‖g * S‖ ^ 2 := by rw [norm_mul, mul_pow, hgauss]
      _ = ‖∑ u : F, χ⁻¹ u * T u‖ ^ 2 := by rw [hsum]
      _ ≤ (∑ u : F, ‖χ⁻¹ u‖ ^ 2) * ∑ u : F, ‖T u‖ ^ 2 := hcauchy
      _ ≤ _ := mul_le_mul_of_nonneg_right hmass hnonneg
  have hcard : 0 < (Fintype.card F : ℝ) := by exact_mod_cast Fintype.card_pos
  exact (mul_le_mul_iff_of_pos_left hcard).mp hpre
end OAI.FiniteFieldSieve
