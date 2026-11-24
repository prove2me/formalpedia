-- Prove2me | solution 1 for GlobalTheory.Cyc.Model.pow_lt_first_radius
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T14:06:53.989574+00:00
-- url     : https://prove2.me/submissions/c3d6a62a-5e99-44e6-b136-191185e464e3

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_HTBasis
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_PowLtFirstRadius

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.Cyc GlobalTheory.Cyc.Model
open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc Polynomial
variable {l : ℕ} [Fact l.Prime]
namespace GlobalTheory.Cyc.Model
theorem _root_.solution {m : ℕ} (h : Lev l m) : (l : ℝ) ^ (-(m : ℤ)) < rho1 l := by
  have hl : l.Prime := Fact.out
  have hl1 : (1 : ℝ) < l := by exact_mod_cast hl.one_lt
  rw [rho1, ← Real.rpow_intCast]
  apply Real.rpow_lt_rpow_of_exponent_lt hl1
  rw [lt_div_iff₀ (by linarith)]
  push_cast
  have h1 : (1 : ℝ) ≤ m := by exact_mod_cast h.1
  by_cases h2 : l = 2
  · have h3 : (2 : ℝ) ≤ m := by exact_mod_cast h.2 h2
    have h4 : (l : ℝ) = 2 := by exact_mod_cast h2
    rw [h4]; linarith
  · have : (3 : ℝ) ≤ l := by have := hl.two_le; exact_mod_cast (by omega : 3 ≤ l)
    nlinarith
end GlobalTheory.Cyc.Model
