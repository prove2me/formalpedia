-- Prove2me | solution 1 for OAI.Erdos3.initialReplacement_mesh_widths
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-08T11:34:49.249593+00:00
-- url     : https://prove2.me/submissions/7e25475b-aa3b-4e9e-877a-543b54d2c7b8

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B014

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.InitialReplacementMeshWidths
namespace OAI

section

namespace Erdos3

theorem baseWidth_of_upper_ratio {H width K : ℝ}
    (hwidth : 0 ≤ width) (hK : 0 ≤ K) (h : H ≤ K * width) :
    (K + 1)⁻¹ * H ≤ width := by
  have hden : 0 < K + 1 := by positivity
  have hmul : H ≤ width * (K + 1) := by nlinarith
  simpa only [div_eq_mul_inv, mul_comm] using (div_le_iff₀ hden).mpr hmul

theorem parameterWidth_of_relative {L width c : ℝ} {D : ℕ}
    (hL : 0 ≤ L) (hc : 0 < c) (hD : 0 < D) (h : c * L ≤ width) :
    L / (D : ℝ) ≤ c⁻¹ * width := by
  have hDr : (1 : ℝ) ≤ D := by exact_mod_cast hD
  have hDpos : (0 : ℝ) < D := by linarith
  have hdiv : L / (D : ℝ) ≤ L := (div_le_iff₀ hDpos).mpr (by nlinarith)
  have hrel : L ≤ width / c := (le_div_iff₀ hc).mpr (by nlinarith)
  simpa only [div_eq_mul_inv, mul_comm] using hdiv.trans hrel

theorem initialReplacement_mesh_widths {I J : Type*}
    (sourceLo sourceHi : Option J × I → ℤ) (parLo parHi : J → ℤ)
    (hsource : ∀ z, sourceLo z < sourceHi z) (hparameter : ∀ j, parLo j < parHi j)
    (H : I → ℝ) {L K c : ℝ} {D : ℕ} (hL : 0 ≤ L) (hK : 0 ≤ K) (hc : 0 < c) (hD : 0 < D)
    (hsourceScale : ∀ z : Option J × I, smoothPairCoefficientScale (H z.2) L z.1 ≤
      K * ((sourceHi z - sourceLo z : ℤ) : ℝ))
    (hrelative : ∀ j, c * L ≤ ((parHi j - parLo j : ℤ) : ℝ)) :
    (∀ i, (K + 1)⁻¹ * H i ≤ ((sourceHi (none,i) - sourceLo (none,i) : ℤ) : ℝ)) ∧
    (∀ z : Option J × I, smoothPairCoefficientScale (H z.2) L z.1 ≤
      K * ((sourceHi z - sourceLo z).toNat : ℝ)) ∧
    (∀ j, L / (D : ℝ) ≤ c⁻¹ * ((parHi j - parLo j).toNat : ℝ)) := by
  have hs (z) : (((sourceHi z - sourceLo z).toNat : ℕ) : ℝ) = ((sourceHi z - sourceLo z : ℤ) : ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg (sub_nonneg.mpr (hsource z).le)
  have ht (j) : (((parHi j - parLo j).toNat : ℕ) : ℝ) = ((parHi j - parLo j : ℤ) : ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg (sub_nonneg.mpr (hparameter j).le)
  refine ⟨?_, ?_, ?_⟩
  · intro i
    exact baseWidth_of_upper_ratio (by exact_mod_cast (sub_nonneg.mpr (hsource (none,i)).le)) hK (hsourceScale (none,i))
  · intro z
    rw [hs]
    exact hsourceScale z
  · intro j
    rw [ht]
    exact parameterWidth_of_relative hL hc hD (hrelative j)

end Erdos3

end

end OAI

end

theorem solution.{u_1, u_2} : type_of% @OAI.Erdos3.initialReplacement_mesh_widths.{u_1, u_2} := @OAI.Erdos3.initialReplacement_mesh_widths.{u_1, u_2}
