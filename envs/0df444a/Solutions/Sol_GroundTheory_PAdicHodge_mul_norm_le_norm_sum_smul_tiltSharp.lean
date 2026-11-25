-- Prove2me | solution 1 for GroundTheory.PAdicHodge.mul_norm_le_norm_sum_smul_tiltSharp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:38:13.655051+00:00
-- url     : https://prove2.me/submissions/ab7593fe-11c6-4817-82d9-b88366f25023

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_TiltAlgebra
import Definitions.Def_GroundTheory_PAdicHodge_OrthoBasis
import Definitions.Def_GroundTheory_PAdicHodge_UntiltIndep
import Theorems.Thm_GroundTheory_PAdicHodge_lt_norm_sum_smul_tiltSharp
import Theorems.Thm_GroundTheory_PAdicHodge_exists_norm_mem_Ioc
import Theorems.Thm_GroundTheory_PAdicHodge_tiltMap_algebraMap
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.PAdicHodge.tiltMap_algebraMap



set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.PAdicHodge
variable {K C : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
  [NontriviallyNormedField C] [IsUltrametricDist C] [NormedAlgebra K C]
variable {p : ℕ} [Fact p.Prime] [IsPerfectoidField K p] [IsPerfectoidField C p]
local notation "K♭" => Tilt K NormedField.valuation (normInteger K) normInteger_integers p
local notation "C♭" => Tilt C NormedField.valuation (normInteger C) normInteger_integers p
local notation "𝒪K♭" => PreTilt (normInteger K) p
local notation "𝒪C♭" => PreTilt (normInteger C) p
namespace GroundTheory.PAdicHodge
theorem _root_.solution {ι : Type*} [Fintype ι] {w : ι → C♭} {t r ρ : ℝ}
    (hw : ∀ (c : ι → K♭) (i : ι), t * ‖c i • w i‖ ≤ ‖∑ j, c j • w j‖)
    (hw1 : ∀ i, ‖w i‖ ≤ 1) (hwr : ∀ i, r < ‖w i‖) (ht : 0 < t) (hr : 0 ≤ r) (hρ : 0 < ρ)
    (hρ1 : ρ < 1) (hp : ‖(p : K)‖ ≤ t * r * ρ) (l : ι → K) (i : ι) :
    t * r * ρ * ‖l i‖ ≤ ‖∑ j, l j • tiltSharp C p (w j)‖ := by
  by_cases hli : l i = 0
  · rw [hli, norm_zero, mul_zero]; exact norm_nonneg _
  obtain ⟨i0, -, hi0⟩ := Finset.exists_max_image Finset.univ (fun j => ‖l j‖)
    ⟨i, Finset.mem_univ i⟩
  set m := ‖l i0‖ with hm
  have hli0 : ‖l i‖ ≤ m := hi0 i (Finset.mem_univ i)
  have hm0 : 0 < m := (norm_pos_iff.2 hli).trans_le hli0
  obtain ⟨c, hc1, hc2⟩ := exists_norm_mem_Ioc p (K := K) (div_pos hρ hm0)
    (div_lt_div_of_pos_right hρ1 hm0)
  have hc0 : 0 < ‖c‖ := (div_pos hρ hm0).trans hc1
  have hcm : ‖c‖ * m ≤ 1 := by rwa [le_div_iff₀ hm0] at hc2
  have hcm' : ρ < ‖c‖ * m := by rwa [div_lt_iff₀ hm0] at hc1
  have key := lt_norm_sum_smul_tiltSharp (C := C) hw hw1 hwr ht hr hρ hp
    (l := fun j => c * l j) (j := i0)
    (fun j => by
      rw [norm_mul]
      exact (mul_le_mul_of_nonneg_left (hi0 j (Finset.mem_univ j)) (norm_nonneg c)).trans hcm)
    (by rw [norm_mul]; exact hcm')
  have e : ∑ j, (c * l j) • tiltSharp C p (w j) = c • ∑ j, l j • tiltSharp C p (w j) := by
    rw [Finset.smul_sum]; simp only [mul_smul]
  rw [e, norm_smul] at key
  have hX := norm_nonneg (∑ j, l j • tiltSharp C p (w j))
  have htrρ : 0 ≤ t * r * ρ := by positivity
  calc t * r * ρ * ‖l i‖ ≤ t * r * ρ * m := by gcongr
    _ ≤ ‖c‖ * ‖∑ j, l j • tiltSharp C p (w j)‖ * m := by gcongr
    _ = (‖c‖ * m) * ‖∑ j, l j • tiltSharp C p (w j)‖ := by ring
    _ ≤ 1 * ‖∑ j, l j • tiltSharp C p (w j)‖ := by gcongr
    _ = _ := one_mul _
end GroundTheory.PAdicHodge
