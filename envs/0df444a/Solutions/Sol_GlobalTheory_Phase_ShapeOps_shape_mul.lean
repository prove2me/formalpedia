-- Prove2me | solution 1 for GlobalTheory.Phase.ShapeOps.shape_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T03:43:18.719703+00:00
-- url     : https://prove2.me/submissions/cb195429-5c36-42e0-bd76-e636a9117976

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IntMIffInt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_RationalSchwartzBruhatAlgebraIntegralLinear
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_IsCosetQuadraticPhaseTestFunctionConjCharacterMu
import Theorems.Thm_GlobalTheory_Phase_ShapeOps_ph_mul
import Theorems.Thm_GlobalTheory_Phase_ShapeOps_quad_mul
import Theorems.Thm_GlobalTheory_Phase_ShapeOps_quad_mono
import Theorems.Thm_GlobalTheory_Phase_ShapeOps_quad_shift
import Theorems.Thm_GlobalTheory_Phase_isMu_one
import Theorems.Thm_GlobalTheory_Phase_ph_zero
import Theorems.Thm_GlobalTheory_SW_isSB_algebra_haar_linear


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex GlobalTheory.SW GlobalTheory.Phase
open scoped ComplexConjugate Real
open GlobalTheory GlobalTheory.Phase GlobalTheory.Phase.ShapeOps
variable {κ ι : Type} [Fintype κ] [Fintype ι]
namespace GlobalTheory.Phase.ShapeOps
theorem _root_.solution {φ ψ : Matrix κ ι ℚ → ℂ} (h : Shape φ) (h' : Shape ψ) :
    Shape (fun x => φ x * ψ x) := by
  obtain ⟨hs, c, a, S, f, hc, hf, hφ⟩ := h
  obtain ⟨hs', c', a', S', f', hc', hf', hψ⟩ := h'
  refine ⟨(isSB_algebra_haar_linear ℚ κ ι φ ψ hs hs').2.2.1, ?_⟩
  by_cases hb : ∃ b, b - a ∈ S ∧ b - a' ∈ S'
  · obtain ⟨b, hb, hb'⟩ := hb
    refine ⟨c * c', b, S ⊓ S', _, ph_mul hc hc',
      quad_mul (quad_mono inf_le_left (quad_shift hf hb)) (quad_mono inf_le_right (quad_shift hf' hb')),
      fun x => ?_⟩
    have i1 : x - a ∈ S ↔ x - b ∈ S := by
      rw [show x - a = x - b + (b - a) by abel]; exact S.add_mem_cancel_right hb
    have i2 : x - a' ∈ S' ↔ x - b ∈ S' := by
      rw [show x - a' = x - b + (b - a') by abel]; exact S'.add_mem_cancel_right hb'
    simp only [hφ x, hψ x, sub_add_sub_cancel]
    by_cases p : x - b ∈ S
    · by_cases p' : x - b ∈ S'
      · rw [if_pos (i1.2 p), if_pos (i2.2 p'), if_pos (AddSubgroup.mem_inf.2 ⟨p, p'⟩)]; ring
      · rw [if_neg (mt i2.1 p'), mul_zero, if_neg (fun q => p' (AddSubgroup.mem_inf.1 q).2)]
    · rw [if_neg (mt i1.1 p), zero_mul, if_neg (fun q => p (AddSubgroup.mem_inf.1 q).1)]
  · refine ⟨0, 0, ⊥, fun _ => 1, ph_zero, ⟨fun _ _ => isMu_one, fun _ _ _ _ _ _ => rfl⟩, fun x => ?_⟩
    have : φ x * ψ x = 0 := by
      rw [hφ x, hψ x]
      by_cases p : x - a ∈ S
      · have p' : x - a' ∉ S' := fun p' => hb ⟨x, p, p'⟩
        simp [p']
      · simp [p]
    simp [this]
end GlobalTheory.Phase.ShapeOps
