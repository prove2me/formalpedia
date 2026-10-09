-- Prove2me | solution 1 for OAI.Erdos3.physicalReplacementScaleThreshold_conditions
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-08T19:13:51.845791+00:00
-- url     : https://prove2.me/submissions/47e59697-0b5e-49ce-bbdb-0c41f83f7637

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B090
import Theorems.Thm_OAI_Erdos3_fullSmoothPairError_nonneg
import Theorems.Thm_OAI_Erdos3_physicalPairGridAccuracy_spec

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ResidualErrorAllocation
namespace OAI

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3.NativeModelingNumerics

end Erdos3.NativeModelingNumerics

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

theorem replacementAccuracy_spec {B epsilon : ℝ} (hB : 0 ≤ B) (hepsilon : 0 < epsilon) :
    0 < replacementAccuracy B epsilon ∧ replacementAccuracy B epsilon ≤ 1 ∧
      B * replacementAccuracy B epsilon ≤ epsilon := by
  have hden : 0 < 1 + B := by positivity
  refine ⟨lt_min zero_lt_one (div_pos hepsilon hden), min_le_left _ _, ?_⟩
  calc
    _ ≤ B * (epsilon / (1 + B)) := mul_le_mul_of_nonneg_left (min_le_right _ _) hB
    _ ≤ epsilon := by
      rw [← mul_div_assoc]
      apply (div_le_iff₀ hden).mpr
      nlinarith

theorem replacementAccuracy_cost {B epsilon x : ℝ} (hB : 0 ≤ B) (hepsilon : 0 < epsilon)
    (hx : x ≤ replacementAccuracy B epsilon) : B * x ≤ epsilon :=
  (mul_le_mul_of_nonneg_left hx hB).trans (replacementAccuracy_spec hB hepsilon).2.2

end Erdos3

end

section

namespace Erdos3

theorem replacementScaleThreshold_conditions {C delta rho J Q R U L H : ℝ} {N e : ℕ}
    (hC : 0 ≤ C) (hd : 0 < delta) (hr : 0 < rho) (hJ : 0 ≤ J) (hQ : 0 ≤ Q)
    (hR : 0 < R) (hU : 0 ≤ U) (hL : 1 ≤ L) (he : 2 ≤ e)
    (hscale : replacementScaleThreshold C delta rho J Q R U * L ^ e ≤ H)
    (hupper : H ≤ R * N) (hrR : rho * R ≤ 2) :
    0 < H ∧ 2 * C * L ^ 2 / H ≤ delta ∧ 4 ≤ rho * H ∧
      J ≤ rho * H / 4 ∧ Q ≤ N ∧ U ≤ H / L ∧ rho * H ≤ 2 * N := by
  have hLp : 0 < L := zero_lt_one.trans_le hL
  have hn2 : 0 ≤ 2 * C / delta := by positivity
  have hnJ : 0 ≤ 4 * J / rho := by positivity
  have hn4 : 0 ≤ 4 / rho := by positivity
  have hnRQ : 0 ≤ R * Q := by positivity
  have hT1 : 1 ≤ replacementScaleThreshold C delta rho J Q R U := by
    unfold replacementScaleThreshold
    linarith
  have hT0 := zero_le_one.trans hT1
  have hpow : 1 ≤ L ^ e := one_le_pow₀ hL
  have hT : replacementScaleThreshold C delta rho J Q R U ≤ H :=
    (le_mul_of_one_le_right hT0 hpow).trans hscale
  have hH : 0 < H := zero_lt_one.trans_le (hT1.trans hT)
  have hcoef : 2 * C / delta ≤ replacementScaleThreshold C delta rho J Q R U := by
    unfold replacementScaleThreshold
    linarith
  have hpow2 : L ^ 2 ≤ L ^ e := pow_le_pow_right₀ hL he
  have hmesh : (2 * C / delta) * L ^ 2 ≤ H :=
    (mul_le_mul hcoef hpow2 (sq_nonneg L) hT0).trans hscale
  have hfour : 4 / rho ≤ H := by unfold replacementScaleThreshold at hT; linarith
  have hcell : 4 * J / rho ≤ H := by unfold replacementScaleThreshold at hT; linarith
  have hRQ : R * Q ≤ H := by unfold replacementScaleThreshold at hT; linarith
  have hUT : U ≤ replacementScaleThreshold C delta rho J Q R U := by
    unfold replacementScaleThreshold
    linarith
  have hpowL : L ≤ L ^ e := by
    simpa only [pow_one] using pow_le_pow_right₀ hL (show 1 ≤ e by omega)
  refine ⟨hH, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · apply (div_le_iff₀ hH).mpr
    have hh := mul_le_mul_of_nonneg_left hmesh hd.le
    have hid : delta * ((2 * C / delta) * L ^ 2) = 2 * C * L ^ 2 := by field_simp
    rw [hid] at hh
    nlinarith
  · have hh := (div_le_iff₀ hr).mp hfour
    nlinarith
  · have hh := (div_le_iff₀ hr).mp hcell
    nlinarith
  · nlinarith [hRQ.trans hupper]
  · apply (le_div_iff₀ hLp).mpr
    exact (mul_le_mul hUT hpowL hLp.le hT0).trans hscale
  · have hh := mul_le_mul_of_nonneg_left hupper hr.le
    have hn := mul_le_mul_of_nonneg_right hrR (Nat.cast_nonneg N)
    nlinarith

end Erdos3

end

section

namespace Erdos3

theorem residualPointAccuracy_spec {M S F mesh epsilon : ℝ}
    (hM : 0 ≤ M) (hS : 0 ≤ S) (hF : 0 ≤ F) (hmesh : 0 ≤ mesh) (heps : 0 < epsilon) :
    0 < residualPointAccuracy M S F mesh epsilon ∧ residualPointAccuracy M S F mesh epsilon ≤ 1 ∧
      6 * M * S * F * residualPointAccuracy M S F mesh epsilon ≤ epsilon ∧
      mesh * residualPointAccuracy M S F mesh epsilon ≤ 1 / 2 := by
  have hfirst := replacementAccuracy_spec (by positivity : 0 ≤ 6 * M * S * F) heps
  have hsecond := replacementAccuracy_spec (by positivity : 0 ≤ 2 * mesh) (by norm_num : (0 : ℝ) < 1)
  have hp := replacementAccuracy_cost (by positivity : 0 ≤ 6 * M * S * F) heps (min_le_left _ (replacementAccuracy (2 * mesh) 1))
  have hm := replacementAccuracy_cost (by positivity : 0 ≤ 2 * mesh) (by norm_num : (0 : ℝ) < 1) (min_le_right (replacementAccuracy (6 * M * S * F) epsilon) _)
  exact ⟨lt_min hfirst.1 hsecond.1, (min_le_left _ _).trans hfirst.2.1, hp, by dsimp [residualPointAccuracy]; nlinarith [hm]⟩

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SmoothPairErrorLogBounds
namespace OAI

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

theorem smoothPairErrorCoefficient_nonneg {J : Type*} [Fintype J] [DecidableEq J]
    (n : ℕ) (k : J) (Q : ℕ) (C κ : ℝ) : 0 ≤ smoothPairErrorCoefficient n k Q C κ :=
  fullSmoothPairError_nonneg n k Q C κ 1 zero_le_one

end Erdos3

end

section

namespace Erdos3

variable {J : Type*} [Fintype J] [DecidableEq J]

end Erdos3

end

section

namespace Erdos3

variable {J : Type*} [Fintype J] [DecidableEq J]

end Erdos3

end

section

namespace Erdos3

variable {J : Type*} [Fintype J] [DecidableEq J]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PhysicalPairAccuracyLogBounds
namespace OAI

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

end Erdos3

end

section

namespace Erdos3

theorem physicalPairPointAccuracy_spec {J : Type*} [Fintype J] [DecidableEq J]
    (n : ℕ) (k : J) (Q : ℕ) (C κ : ℝ) {A epsilon : ℝ} (hA : 0 ≤ A) (heps : 0 < epsilon) :
    let delta := physicalPairPointAccuracy n k Q C κ A epsilon
    0 < delta ∧ delta ≤ 1 ∧
      6 * A ^ (2 * n) * (2 : ℝ) ^ n * smoothPairErrorCoefficient n k Q C κ * delta ≤ epsilon ∧
      ((4 : ℝ) ^ (2 + Fintype.card {j : J // j ≠ k}) * smoothPairRowLipschitz k) * delta ≤ 1 / 2 :=
  residualPointAccuracy_spec (by positivity) (by positivity) (smoothPairErrorCoefficient_nonneg n k Q C κ)
    (by positivity) heps

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

end Erdos3

end

section

namespace Erdos3

variable {J : Type*} [Fintype J] [DecidableEq J]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SmallWeightedPhysicalReplacement
namespace OAI

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

end Erdos3

end

section

namespace Erdos3

theorem physicalReplacementScaleThreshold_conditions {J : Type*} [Fintype J] [DecidableEq J]
    (n : ℕ) (k : J) (Q : ℕ) (C κ : ℝ) (degree : ℕ) (modLog dimLog : ℝ)
    {A epsilon L H : ℝ} {N e : ℕ} (hC : 0 ≤ C) (hA : 0 ≤ A) (heps : 0 < epsilon)
    (hL : 1 ≤ L) (he : 2 ≤ e)
    (hscale : physicalReplacementScaleThreshold n k Q C κ A epsilon degree modLog dimLog * L ^ e ≤ H)
    (hupper : H ≤ 2 * (N : ℝ)) :
    let delta := physicalPairPointAccuracy n k Q C κ A epsilon
    let rho := physicalPairGridAccuracy n k C κ A epsilon
    let accLog := physicalMeanAccuracyLog n k Q C κ A degree epsilon
    0 < H ∧ 2 * C * L ^ 2 / H ≤ delta ∧ 4 ≤ rho * H ∧
      Real.exp (modLog * (2 * degree : ℕ) + accLog + dimLog + 1) ≤ rho * H / 4 ∧
      (Q : ℝ) ≤ N ∧ 8 * (probabilityProfileLipschitz : ℝ) ≤ H / L ∧ rho * H ≤ 2 * N := by
  have hd := physicalPairPointAccuracy_spec n k Q C κ hA heps
  have hr := physicalPairGridAccuracy_spec n k C κ hA heps
  exact replacementScaleThreshold_conditions hC hd.1 hr.1 (Real.exp_nonneg _) (Nat.cast_nonneg Q)
    (by norm_num) (by positivity) hL he hscale hupper (by nlinarith [hr.2.1])

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

end Erdos3

end

section

namespace Erdos3

variable {J : Type*} [Fintype J] [DecidableEq J]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

end Erdos3

end

end OAI

end

theorem solution.{u_1} : type_of% @OAI.Erdos3.physicalReplacementScaleThreshold_conditions.{u_1} := @OAI.Erdos3.physicalReplacementScaleThreshold_conditions.{u_1}
