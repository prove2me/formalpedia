-- Prove2me | solution 1 for GlobalTheory.K5.Basic.exists_isKum_qq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T18:55:40.266259+00:00
-- url     : https://prove2.me/submissions/5d379764-81e4-40f3-9e17-3f4b3d92a0fe

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_NotCoboundaryConstantOne
import Theorems.Thm_GlobalTheory_K5_Basic_qq_pow
import Theorems.Thm_GlobalTheory_K5_Basic_qq_ne_zero
import Theorems.Thm_GlobalTheory_K5_Basic_exists_isKum

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
theorem _root_.solution (T : Tower p Ω) (n : ℕ) : ∃ a, IsKum T n ⊤ (T.qq n) a :=
  exists_isKum T n ⊤ (qq_ne_zero T n) fun g _ => by rw [qq_pow, AlgEquiv.commutes]
end GlobalTheory.K5.Basic
