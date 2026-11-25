-- Prove2me | solution 1 for GlobalTheory.Cyc.LiftExp.norm_pow_prime_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T07:01:39.97135+00:00
-- url     : https://prove2.me/submissions/c597a9a3-84b7-4fe0-b5db-886dcf710f6b

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_HTBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_PadicNormZpowSubOnePadicValInt
import Theorems.Thm_GlobalTheory_Cyc_LiftExp_norm_pow_prime

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc
open GlobalTheory GlobalTheory.Cyc GlobalTheory.Cyc.LiftExp
variable {l : ℕ} [hl : Fact l.Prime]
namespace GlobalTheory.Cyc.LiftExp
theorem _root_.solution (a : ℕ) (j : ℕ) (hj : Lev l j) (u : ℚ_[l])
    (hu : ‖u - 1‖ = (l : ℝ) ^ (-(j : ℤ))) :
    ‖u ^ (l ^ a) - 1‖ = (l : ℝ) ^ (-((j + a : ℕ) : ℤ)) := by
  induction a with
  | zero => simpa using hu
  | succ a ih =>
    have h : Lev l (j + a) := ⟨by have := hj.1; omega, fun h => by have := hj.2 h; omega⟩
    rw [pow_succ, pow_mul]
    exact norm_pow_prime (j + a) h _ ih
end GlobalTheory.Cyc.LiftExp
