-- Prove2me | solution 1 for GlobalTheory.K5.Basic.cong_gal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:55:33.936192+00:00
-- url     : https://prove2.me/submissions/51fc695c-2331-4e6e-93fb-73f8170036ec

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_NotCoboundaryConstantOne
import Theorems.Thm_GlobalTheory_K5_Basic_isInt_gal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.K5 GlobalTheory.K5.Basic
open Polynomial
variable {p : ℕ} [hp : Fact p.Prime] {Ω : Type*} [Field Ω] [Algebra (O0 p) Ω]
namespace GlobalTheory.K5.Basic
theorem _root_.solution {k : ℕ} {x y : Ω} (g : Gal p Ω) (h : Cong p k x y) : Cong p k (g x) (g y) := by
  obtain ⟨a, ha, e⟩ := h
  refine ⟨g a, isInt_gal g ha, ?_⟩
  rw [← map_sub, e, map_mul, map_pow, map_natCast]
end GlobalTheory.K5.Basic
