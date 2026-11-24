-- Prove2me | solution 1 for GlobalTheory.AdLat.lim_eq_of_congr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T15:04:40.197113+00:00
-- url     : https://prove2.me/submissions/0ab1e19f-72ac-4300-8817-888e5933febd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_Hat1
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_AdelicCompletionFractionalIdealProperties
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_AdelicCompletionRationalPointsAndApproximation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_AdelicCompletionRationalPointsAndApproximationStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_AdelicCompletionLatticeSeparatedCompleteStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_AdelicCompletionFractionalIdealDivisibleEqZero
import Theorems.Thm_GlobalTheory_T_adelicCompletion_lattice_separated_complete


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.AdLat
open scoped TensorProduct Matrix nonZeroDivisors
open GlobalTheory GlobalTheory.AdLat
variable (F : Type) {E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ}
variable [NumberField E]
namespace GlobalTheory.AdLat
theorem _root_.solution (L : Submodule (𝓞 E) (Fin n → E)) (hL : L.FG) (x y : Fin n → RA F E)
    (h : ∀ N : ℕ, 0 < N → ∃ w ∈ hat F (L : Set (Fin n → E)), x = y + N • w) : x = y := by
  rw [← sub_eq_zero]
  refine (GlobalTheory.T.adelicCompletion_lattice_separated_complete F E n L hL).1 _ fun N hN => ?_
  obtain ⟨w, hw, rfl⟩ := h N hN
  exact ⟨w, hw, by abel⟩
end GlobalTheory.AdLat
