-- Prove2me | solution 1 for GlobalTheory.NormUnits.exists_far_unit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T15:40:41.561617+00:00
-- url     : https://prove2.me/submissions/6599c0e3-cedc-4aa9-a9fb-1c97cfbe4752

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TotalDegreeCMulXMulX
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsMulStarEqOfNormOneUnramifiedQuadratic
import Theorems.Thm_P2M_GlobalTheory_NormUnits_norm_sub_le_max__752f971280ab

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.NormUnits
namespace GlobalTheory.NormUnits
theorem _root_.solution (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E]
    [StarRing E] [hU : Unram F E] :
    ∃ ζ : E, ‖ζ‖ = 1 ∧ ∀ b : F, 1 ≤ ‖ζ - algebraMap F E b‖ := by
  haveI : IsUltrametricDist E := hU.ultraE
  haveI : LocallyCompactSpace F := hU.lcF
  haveI : ProperSpace F := ProperSpace.of_locallyCompactSpace F
  obtain ⟨y, hy⟩ := hU.star_ne
  have hyF : ∀ b : F, algebraMap F E b ≠ y := fun b hb => hy (by rw [← hb, hU.star_fix])
  let g : F → ℝ := fun b => ‖y - algebraMap F E b‖
  have hg : Continuous g := continuous_norm.comp (continuous_const.sub (continuous_algebraMap F E))
  obtain ⟨b₀, -, hmin⟩ := (isCompact_closedBall (0 : F) ‖y‖).exists_isMinOn
    ⟨0, by simp⟩ hg.continuousOn
  have hmin' : ∀ b : F, g b₀ ≤ g b := by
    intro b
    by_cases hb : ‖b‖ ≤ ‖y‖
    · exact hmin (mem_closedBall_zero_iff.2 hb)
    · push_neg at hb
      have h0 : g b₀ ≤ g 0 := hmin (by simp)
      refine h0.trans ?_
      simp only [g, map_zero, sub_zero]
      by_contra hlt
      push_neg at hlt
      have : ‖algebraMap F E b‖ ≤ max ‖y‖ ‖y - algebraMap F E b‖ := by
        calc ‖algebraMap F E b‖ = ‖y - (y - algebraMap F E b)‖ := by rw [sub_sub_cancel]
          _ ≤ _ := norm_sub_le_max' _ _
      rw [norm_algebraMap'] at this
      rcases le_max_iff.1 this with h | h <;> linarith
  have hz0 : y - algebraMap F E b₀ ≠ 0 := sub_ne_zero.2 (hyF b₀).symm
  obtain ⟨x, hx⟩ := hU.unram (y - algebraMap F E b₀)
  have hnx : ‖algebraMap F E x‖ = ‖y - algebraMap F E b₀‖ := by rw [norm_algebraMap', hx]
  have hxE : algebraMap F E x ≠ 0 := by
    intro h; rw [h, norm_zero] at hnx; exact hz0 (norm_eq_zero.1 hnx.symm)
  refine ⟨(y - algebraMap F E b₀) / algebraMap F E x, ?_, fun b => ?_⟩
  · rw [norm_div, hnx, div_self (norm_ne_zero_iff.2 hz0)]
  · have e : (y - algebraMap F E b₀) / algebraMap F E x - algebraMap F E b =
        (y - algebraMap F E (b₀ + x * b)) / algebraMap F E x := by
      rw [map_add, map_mul]; field_simp; ring
    rw [e, norm_div, hnx, le_div_iff₀ (norm_pos_iff.2 hz0), one_mul]
    exact hmin' (b₀ + x * b)
end GlobalTheory.NormUnits
