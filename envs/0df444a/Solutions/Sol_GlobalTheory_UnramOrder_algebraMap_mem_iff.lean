-- Prove2me | solution 1 for GlobalTheory.UnramOrder.algebraMap_mem_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T13:21:19.633032+00:00
-- url     : https://prove2.me/submissions/0fabe75f-f58d-4262-9b9d-df7db118e54c

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsEqTransposeMulMapOfIdempotent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
import Theorems.Thm_GlobalTheory_UnramOrder_algebraMap_inj

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
open GlobalTheory GlobalTheory.UnramOrder
open IsLocalRing Polynomial
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
namespace GlobalTheory.UnramOrder
theorem _root_.solution (L : LocE F E) (c : F) : algebraMap F E c ∈ L.O ↔ c ∈ 𝒪[F] := by
  rw [L.O_def, isIntegral_algebraMap_iff (algebraMap_inj L), IsIntegrallyClosed.isIntegral_iff]
  constructor
  · rintro ⟨y, rfl⟩; exact y.2
  · intro h; exact ⟨⟨c, h⟩, rfl⟩
end GlobalTheory.UnramOrder
