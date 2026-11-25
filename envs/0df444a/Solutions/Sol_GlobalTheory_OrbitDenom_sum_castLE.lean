-- Prove2me | solution 1 for GlobalTheory.OrbitDenom.sum_castLE
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T03:34:42.861203+00:00
-- url     : https://prove2.me/submissions/06a690f4-6a79-418f-8023-f0e62d988f81

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_HermLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsEqZpowMulUnit
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_BasisOfIsCompl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_LeadingMinorsProdDenominatorUnitriangularFactors
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.OrbitDenom
variable {E : Type} [CommRing E]
namespace GlobalTheory.OrbitDenom
theorem _root_.solution {n l : ℕ} (h : l ≤ n) (g : Fin n → E) (hg : ∀ k : Fin n, l ≤ (k : ℕ) → g k = 0) :
    ∑ k, g k = ∑ k : Fin l, g (Fin.castLE h k) := by
  symm
  refine Finset.sum_of_injOn (Fin.castLE h) (fun a _ b _ hab => Fin.castLE_injective h hab)
    (fun _ _ => Finset.mem_univ _) ?_ (fun _ _ => rfl)
  intro k _ hk
  refine hg k ?_
  by_contra hlt
  exact hk ⟨⟨k, by omega⟩, by simp, Fin.ext rfl⟩
end GlobalTheory.OrbitDenom
