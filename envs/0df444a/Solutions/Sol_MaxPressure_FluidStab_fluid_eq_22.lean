-- Prove2me | solution 1 for MaxPressure.FluidStab.fluid_eq_22
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T19:34:28.820079+00:00
-- url     : https://prove2.me/submissions/09f9cdcb-fed5-4bd7-9bef-d5b9a55a96dc

import Mathlib
import Definitions.Def_MaxPressure_FluidStab_Network

open Matrix MaxPressure.FluidStab in
theorem MaxPressure.FluidStab.fluid_eq_22_vec {I J K : ℕ} (N : Network I J K)
    (Zb : ℝ → Fin I → ℝ) (Tb : ℝ → Fin J → ℝ) (hsol : IsFluidSolution N Zb Tb) :
    ∀ s, 0 ≤ s → Zb s = Zb 0 - R N *ᵥ Tb s := by
  intro s hs
  funext i
  rw [hsol.1 s hs i]
  have key : (R N *ᵥ Tb s) i = ∑ j : Fin J, Tb s j * μ N j * N.B j i.succ
      - ∑ i' : Fin (I + 1), ∑ j : Fin J, Tb s j * μ N j * N.B j i' * N.P j i' i.succ := by
    rw [Finset.sum_comm (f := fun i' j => Tb s j * μ N j * N.B j i' * N.P j i' i.succ),
      ← Finset.sum_sub_distrib]
    simp only [mulVec, dotProduct, R]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [mul_sub, sub_mul, Finset.mul_sum, Finset.sum_mul]
    congr 1
    · ring
    · refine Finset.sum_congr rfl (fun i' _ => ?_)
      ring
  rw [Pi.sub_apply, key]
  ring

open Matrix MaxPressure.FluidStab in
theorem solution {I J K : ℕ} (N : Network I J K)
    (Zb : ℝ → Fin I → ℝ) (Tb : ℝ → Fin J → ℝ) (hsol : IsFluidSolution N Zb Tb) :
    (∀ s, 0 ≤ s → Zb s = Zb 0 - R N *ᵥ Tb s) ∧
    ∀ t, IsRegular Zb Tb t →
      HasDerivAt (fun s => ∑ i, Zb s i ^ 2) (2 * (deriv Zb t ⬝ᵥ Zb t)) t ∧
      2 * (deriv Zb t ⬝ᵥ Zb t) = -2 * pressure N (deriv Tb t) (Zb t) := by
  have hvec := MaxPressure.FluidStab.fluid_eq_22_vec N Zb Tb hsol
  refine ⟨hvec, fun t ht => ?_⟩
  obtain ⟨htpos, hZdiff, hTdiff⟩ := ht
  have hZd : HasDerivAt Zb (deriv Zb t) t := hZdiff.hasDerivAt
  have hTd : HasDerivAt Tb (deriv Tb t) t := hTdiff.hasDerivAt
  have hZi : ∀ i, HasDerivAt (fun s => Zb s i) (deriv Zb t i) t := hasDerivAt_pi.mp hZd
  have hTj : ∀ j, HasDerivAt (fun s => Tb s j) (deriv Tb t j) t := hasDerivAt_pi.mp hTd
  refine ⟨?_, ?_⟩
  · have hp : ∀ i, HasDerivAt (fun s => Zb s i ^ 2) (2 * Zb t i * deriv Zb t i) t := by
      intro i
      exact ((hZi i).fun_pow 2).congr_deriv (by norm_num)
    have hs : HasDerivAt (∑ i, fun s => Zb s i ^ 2) (∑ i, 2 * Zb t i * deriv Zb t i) t :=
      HasDerivAt.sum (fun i _ => hp i)
    have hf : (fun s => ∑ i, Zb s i ^ 2) = ∑ i, (fun s => Zb s i ^ 2) := by
      funext s
      simp [Finset.sum_apply]
    rw [hf]
    refine hs.congr_deriv ?_
    simp only [dotProduct, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    ring
  · have hg : HasDerivAt (fun s => Zb 0 - R N *ᵥ Tb s) (-(R N *ᵥ deriv Tb t)) t := by
      refine hasDerivAt_pi.mpr (fun i => ?_)
      have h1 := ((HasDerivAt.sum (u := Finset.univ)
        (fun j _ => (hTj j).const_mul (R N i j))).const_sub (Zb 0 i))
      convert h1 using 1
      · funext s
        simp [mulVec, dotProduct]
      · simp [mulVec, dotProduct]
    have heq : Zb =ᶠ[nhds t] (fun s => Zb 0 - R N *ᵥ Tb s) := by
      filter_upwards [Ioi_mem_nhds htpos] with s hs
      exact hvec s (le_of_lt hs)
    have hZ' : deriv Zb t = -(R N *ᵥ deriv Tb t) :=
      (hg.congr_of_eventuallyEq heq).deriv
    rw [hZ', pressure, neg_dotProduct, dotProduct_comm]
    ring
