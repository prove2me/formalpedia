-- Prove2me | solution 1 for GlobalTheory.T.eichler_map_mem_unipotent_character
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:29:25.816099+00:00
-- url     : https://prove2.me/submissions/4119d4fd-869a-4a45-9dd5-b558cb8c150e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_EichlerMapMemUnipotentCharacter
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_EichlerMapMemUnipotentCharacterStatement
import Theorems.Thm_GlobalTheory_HL_EichlerUnip_eichler_mem_unip


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
theorem _root_.solution : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ (g : Fin (r + 1) → S.V) (gs : Fin r → S.V), (g = S.f ∧ gs = S.es) ∨ (g = S.f' ∧ gs = S.es') → ∀ (j : Fin r) (x u : S.V) (s : E), x ∈ S.spanTo g (j + 1) → u ∈ perp L S.Hm (S.spanTo g (j + 1)) → s + L.cj s = S.h u u → ∃ n ∈ S.Nof g, (∀ v, n v = eich L S.Hm x u s v) ∧ (∀ v, n⁻¹ v = eich L S.Hm x (-u) (L.cj s) v) ∧ (∀ v ∈ S.spanTo g (j + 1), n v = v) ∧ ∀ m ∈ S.Nof g, S.psiOf g gs n = L.psi0 (algebraMap F E S.th⁻¹ * (S.h x (gs j) * S.h (m (g j.succ)) u)) := by
  first | exact @GlobalTheory.HL.EichlerUnip.eichler_mem_unip | exact GlobalTheory.HL.EichlerUnip.eichler_mem_unip | (intros; apply GlobalTheory.HL.EichlerUnip.eichler_mem_unip <;> assumption)
end _root_.GlobalTheory.T
