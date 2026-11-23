-- Prove2me | solution 1 for GlobalTheory.CubeLift.avg_mv_fst
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:01:55.271571+00:00
-- url     : https://prove2.me/submissions/da0fb99f-ce60-4a40-b109-00b7de357d10

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_IsNilpotentOfRd
import Theorems.Thm_GlobalTheory_CubeLift_mv_single
import Theorems.Thm_GlobalTheory_CubeLift_avg_single

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open AddMonoidAlgebra
open GlobalTheory GlobalTheory.CubeLift
variable {A : Type} [CommRing A] {X Y W : Type} [AddCommGroup X] [AddCommGroup Y] [AddCommGroup W]
namespace GlobalTheory.CubeLift
theorem _root_.solution (f : X × W →+ X × Y) (φ : W →+ Y) (h₁ : ∀ p, (f p).1 = p.1) (h₂ : ∀ w, (f (0, w)).2 = φ w)
    (u : A[X × W]) : avg (mv f u) = mv φ (avg u) := by
  induction u using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb => simp only [map_add, ha, hb]
  | single p r =>
    obtain ⟨a, b⟩ := p
    rw [mv_single, avg_single, avg_single, h₁]
    split_ifs with h
    · obtain rfl : a = 0 := h
      rw [h₂, mv_single]
    · simp
end GlobalTheory.CubeLift
