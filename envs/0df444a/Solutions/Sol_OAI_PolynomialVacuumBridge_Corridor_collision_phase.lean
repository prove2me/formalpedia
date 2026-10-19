-- Prove2me | solution 1 for OAI.PolynomialVacuumBridge.Corridor.collision_phase
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T12:48:03.632999+00:00
-- url     : https://prove2.me/submissions/dee9df74-7f6d-4bc9-b377-0bf1997dd28e

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/HoneycombCorridor/CollisionPhase.lean:L99-L128
-- (upload_full_project.md Phase 4): solution for node OAI.PolynomialVacuumBridge.Corridor.collision_phase. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_HoneycombBridgeFiniteness
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_Basic
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_Excursions
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_IntegerPotential
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_EdgeFlow
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_Contours
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_Cells
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_RationalPotential
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_Currents
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_PotentialSupport
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_Incidence
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_Curvature
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_Polygons
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_CollisionPhase
import Theorems.Thm_OAI_PolynomialVacuumBridge_Corridor_simple_polygon_signed_turn

-- ---- from OAI.Combinatorics.HoneycombCorridor.CollisionPhase ----
namespace OAI

noncomputable section

namespace PolynomialVacuumBridge.Corridor

theorem collision_weights_conjugate (b : Bool) (w : List Bool) :
    wordWeight (b :: reverseTurns w) = starRingEnd ℂ (wordWeight ((!b) :: w)) := by
  rw [← wordWeight_reverse,reverseTurns_cons,Bool.not_not,wordWeight_append]
  simp [wordWeight,mul_comm]

theorem collision_weights_cos (b : Bool) (w : List Bool) :
    wordWeight ((!b) :: w) + wordWeight (b :: reverseTurns w) =
      (2 : ℂ) * (criticalActivity : ℂ) ^ (b :: w).length *
      (Real.cos (Real.pi / 8 * ((turnUnits (b :: w) - 2 * turnUnit b : ℤ) : ℝ)) : ℂ) := by
  rw [collision_weights_conjugate,wordWeight_turnUnits]
  have ht : turnUnits ((!b) :: w) = turnUnits (b :: w) - 2 * turnUnit b := by
    simp only [turnUnits_cons,turnUnit_not]
    ring
  rw [ht,Complex.exp_ofReal_mul_I]
  simp only [List.length_cons,map_mul,map_add,map_pow,Complex.conj_ofReal,
    map_mul,Complex.conj_I]
  ring

theorem numeric_unused_face (f : Fin 3 → ℤ) (ε : ℤ)
    (hε : ε = 1 ∨ ε = -1) (hf : ∀ l, f l = 0 ∨ f l = ε)
    (k : Fin 3) (b : Bool)
    (h : ∀ l : Fin 3, f l - f (l+2) =
      (if l = k + (if b then 2 else 1) then 1 else 0) - (if l = k then 1 else 0)) :
    2 * f (k + (if !b then 2 else 1)) = ε - turnUnit b := by
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  have hf0 := hf 0
  have hf1 := hf 1
  have hf2 := hf 2
  clear h hf
  rcases hε with rfl | rfl <;> fin_cases k <;> cases b <;>
    simp [turnUnit] at * <;> omega

theorem contour_unused_face (p : FaceIndex →₀ ℤ) (ε : ℤ)
    (hε : ε = 1 ∨ ε = -1) (hvals : ∀ a, p a = 0 ∨ p a = ε)
    (q : EdgeIndex →₀ ℤ) (hp : RepresentsFlow p q)
    (g : Germ) (b : Bool) (hw : LocalContour q g b) :
    2 * p (leftFace (g.1,unusedSlot g b)) = ε - turnUnit b := by
  let f : Fin 3 → ℤ := fun l => p (leftFace (g.1,l))
  have hl (l : Fin 3) : f l - f (l+2) =
      (if l = g.2 + (if b then 2 else 1) then 1 else 0) - (if l = g.2 then 1 else 0) := by
    have h := (hp (g.1,l)).symm.trans (hw l)
    simp only [f,rightFace_prev,outgoingSlot] at h ⊢
    exact h
  exact numeric_unused_face f ε hε (fun l => hvals _) g.2 b hl

theorem collision_phase : CollisionPhase := by
  intro g b w p ε hN hc hp hpne hε hvals
  have ht := simple_polygon_signed_turn g (b :: w) (by simp) hN hc p ε hp hpne hε hvals
  have hf := contour_unused_face p ε hε hvals (wordFlow g (b :: w)) hp g b
    (simple_closed_word_contour g (b :: w) hN hc).1
  rw [collision_weights_cos]
  have hhalf : (Real.pi : ℂ) / 8 * 4 = (Real.pi : ℂ) / 2 := by ring
  rcases hε with rfl | rfl <;> cases b
  · have htw : turnUnits (false :: w) = 6 := by simpa using ht
    have hpv : p (leftFace (g.1,unusedSlot g false)) = 1 := by
      norm_num [turnUnit] at hf
      omega
    norm_num [htw,hpv,turnUnit,hhalf,Complex.cos_pi_div_two]
  · have htw : turnUnits (true :: w) = 6 := by simpa using ht
    have hpv : p (leftFace (g.1,unusedSlot g true)) = 0 := by
      norm_num [turnUnit] at hf
      omega
    norm_num [htw,hpv,turnUnit,hhalf,Complex.cos_pi_div_two]
  · have htw : turnUnits (false :: w) = -6 := by
      simpa only [neg_one_mul,neg_eq_iff_eq_neg] using ht
    have hpv : p (leftFace (g.1,unusedSlot g false)) = 0 := by
      norm_num [turnUnit] at hf
      omega
    norm_num [htw,hpv,turnUnit,hhalf,Complex.cos_pi_div_two]
  · have htw : turnUnits (true :: w) = -6 := by
      simpa only [neg_one_mul,neg_eq_iff_eq_neg] using ht
    have hpv : p (leftFace (g.1,unusedSlot g true)) = -1 := by
      norm_num [turnUnit] at hf
      omega
    norm_num [htw,hpv,turnUnit,hhalf,Complex.cos_pi_div_two]
end PolynomialVacuumBridge.Corridor

end

end OAI

-- ---- platform node ----
open OAI OAI.PolynomialVacuumBridge OAI.PolynomialVacuumBridge.Corridor


theorem solution : type_of% @_root_.OAI.PolynomialVacuumBridge.Corridor.collision_phase := @_root_.OAI.PolynomialVacuumBridge.Corridor.collision_phase
