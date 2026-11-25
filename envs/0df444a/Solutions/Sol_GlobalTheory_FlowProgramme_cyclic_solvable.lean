-- Prove2me | solution 1 for GlobalTheory.FlowProgramme.cyclic_solvable
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:34:27.834858+00:00
-- url     : https://prove2.me/submissions/d2a1553e-43ca-4213-82c3-6edf914428aa

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_WtSubOneLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_CyclicSolvable
import Theorems.Thm_GlobalTheory_FlowProgramme_cyclic_nonneg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Sh
open GlobalTheory GlobalTheory.FlowProgramme
namespace GlobalTheory.FlowProgramme
theorem _root_.solution (l : ℝ) (d : ℕ) [NeZero d] (X : ZMod d → ℝ) (hl : 2 ≤ l) :
    ∃ y : ZMod d → ℝ, ∀ a, l * y a + y (a - 1) = X a := by
  let T : (ZMod d → ℝ) →ₗ[ℝ] (ZMod d → ℝ) :=
    { toFun := fun y a => l * y a + y (a - 1)
      map_add' := fun y z => by ext a; simp; ring
      map_smul' := fun c y => by ext a; simp; ring }
  have hinj : Function.Injective T := by
    rw [injective_iff_map_eq_zero]
    intro y hy
    have hy' : ∀ a, l * y a + y (a - 1) = 0 := fun a => congrFun hy a
    ext a
    have h1 := cyclic_nonneg l d (fun _ => 0) y hl (by simp) hy' a
    have h2 := cyclic_nonneg l d (fun _ => 0) (fun a => - y a) hl (by simp)
      (fun a => by have := hy' a; linarith) a
    simp only [Pi.zero_apply]
    linarith
  obtain ⟨y, hy⟩ := LinearMap.injective_iff_surjective.1 hinj X
  exact ⟨y, fun a => congrFun hy a⟩
end GlobalTheory.FlowProgramme
