-- Prove2me | solution 1 for GlobalTheory.T.latticeStabilizer_commensurable_unramified_hermitian
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:48:11.267973+00:00
-- url     : https://prove2.me/submissions/1b3e9fd8-a9e7-40b6-a3f8-9e1d046e700e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_LatticeStabilizerCommensurableUnramifiedHermitia
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_HermLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_LatticeStabilizerCommensurableUnramifiedHermitiaStatement
import Theorems.Thm_GlobalTheory_LatComm_stab_commensurable


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
theorem _root_.solution : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ {n : ℕ} (Λ Λ' : Submodule L.O (Fin n → E)), IsLat L Λ → IsLat L Λ' → ∀ H : Subgroup ((Fin n → E) ≃ₗ[E] (Fin n → E)), (H ⊓ stabL L Λ').relIndex (H ⊓ stabL L Λ) ≠ 0 ∧ ∀ g : ((Fin n → E) ≃ₗ[E] (Fin n → E)), IsLat L (g • Λ) ∧ stabL L (g • Λ) = MulAut.conj g • stabL L Λ := by
  first | exact @GlobalTheory.LatComm.stab_commensurable | exact GlobalTheory.LatComm.stab_commensurable | (intros; apply GlobalTheory.LatComm.stab_commensurable <;> assumption)
end _root_.GlobalTheory.T
