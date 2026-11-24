-- Prove2me | solution 1 for GlobalTheory.UnitValueExistence.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:25:56.082707+00:00
-- url     : https://prove2.me/submissions/06192dac-2b42-474c-b323-9421610b8dba

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormOneAddEqOne
import Theorems.Thm_GlobalTheory_UnitValueExistence_exists_unit_value

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.UnitValueExistence
open Matrix
namespace GlobalTheory.UnitValueExistence
theorem _root_.solution : (let d1 : {E : Type} → [NormedField E] → {n m : Type} → Matrix n m E → Prop := @(fun {E : Type} [NormedField E] {n m : Type} (h : Matrix n m E) ↦ ∀ (i : n) (j : m), ‖h i j‖ ≤ (1 : ℝ)); ∀ {E : Type} [inst : NormedField E] [IsUltrametricDist E] [inst_2 : StarRing E], (∀ (y : E), ‖Star.star y‖ = ‖y‖) → ∀ (e0 : E), ‖e0‖ ≤ (1 : ℝ) → e0 + Star.star e0 = (1 : E) → ∀ {n : Type} [inst_3 : Fintype n] [inst_4 : DecidableEq n] [Nonempty n] (G : Matrix n n E), Matrix.IsHermitian G → d1 G → ‖Matrix.det G‖ = (1 : ℝ) → ∃ (i : n) (w : n → E), (∀ (a : n), ‖w a‖ ≤ (1 : ℝ)) ∧ w i = (1 : E) ∧ ‖Star.star w ⬝ᵥ Matrix.mulVec G w‖ = (1 : ℝ)) := by
  intro d1 E _ _ _ hstar e0 he htr n _ _ _ G hG hint hdet
  exact exists_unit_value hstar e0 he htr G hG hint hdet
end GlobalTheory.UnitValueExistence
