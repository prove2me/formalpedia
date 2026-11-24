-- Prove2me | solution 1 for GlobalTheory.SmoothRiesz.exists_mem_eq_on_of_finiteDimensional
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T20:53:36.380156+00:00
-- url     : https://prove2.me/submissions/9a93ef92-79ea-4fbe-afee-97d65e0b2238

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_LeviRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_ExistsRepresent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_UnitaryAdmissibleMatrixCoefficient
import Theorems.Thm_GlobalTheory_ExistsRepresentation_exists_represent


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GodementJacquet MeasureTheory
open scoped Pointwise
open GlobalTheory GlobalTheory.SmoothRiesz
namespace GlobalTheory.SmoothRiesz
theorem _root_.solution {V : Type} [AddCommGroup V] [Module ℂ V]
    (Bf : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ) (hpos : ∀ v, v ≠ 0 → 0 < (Bf v v).re)
    (L : V →ₗ⋆[ℂ] ℂ) (W : Submodule ℂ V) [FiniteDimensional ℂ W] :
    ∃ u ∈ W, ∀ w ∈ W, L w = Bf u w := by
  first
  | exact @_root_.GlobalTheory.ExistsRepresentation.exists_represent
  | exact _root_.GlobalTheory.ExistsRepresentation.exists_represent
  | (apply _root_.GlobalTheory.ExistsRepresentation.exists_represent <;> assumption)
  | (intros; apply _root_.GlobalTheory.ExistsRepresentation.exists_represent <;> assumption)
  | (intros; apply @_root_.GlobalTheory.ExistsRepresentation.exists_represent <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.ExistsRepresentation.exists_represent ..)
end GlobalTheory.SmoothRiesz
