-- Prove2me | solution 1 for GlobalTheory.T.exists_lattice_and_inverting_automorphism_of_quasi_reflection
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:54:32.873565+00:00
-- url     : https://prove2.me/submissions/948ec9e0-616b-4b74-aca0-14200ea46232

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_QuasiReflectionStabilizesLattice
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_HermLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_QuasiReflectionStabilizesLatticeStatement
import Theorems.Thm_GlobalTheory_QRefl_qrefl_inverted


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E), IsHermND L Hm → ∀ (m : ℕ) (x : Fin m → Fin n → E), IsUnit (gramT L Hm x).det → ∀ a ∈ perp L Hm (Submodule.span E (Set.range x)), ∀ g, IsQRefl L Hm a g → ∃ Λ : Submodule L.O (Fin n → E), IsLat L Λ ∧ ∃ α : ((Fin n → E) ≃ₗ[E] (Fin n → E)) ≃* ((Fin n → E) ≃ₗ[E] (Fin n → E)), (fixG L Hm (Submodule.span E (Set.range x)) ⊓ stabL L Λ).map α.toMonoidHom = fixG L Hm (Submodule.span E (Set.range x)) ⊓ stabL L Λ ∧ α g = g⁻¹ := by
  first | exact @GlobalTheory.QRefl.qrefl_inverted | exact GlobalTheory.QRefl.qrefl_inverted | (intros; apply GlobalTheory.QRefl.qrefl_inverted <;> assumption)
end _root_.GlobalTheory.T
