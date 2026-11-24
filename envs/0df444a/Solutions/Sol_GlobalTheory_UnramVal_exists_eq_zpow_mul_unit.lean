-- Prove2me | solution 1 for GlobalTheory.UnramVal.exists_eq_zpow_mul_unit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:08:25.805028+00:00
-- url     : https://prove2.me/submissions/a38d55e4-7873-47cd-b4f6-a45a76718c63

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsEqZpowMulUnit

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
open GlobalTheory GlobalTheory.UnramVal
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable [IsNonarchimedeanLocalField F]
namespace GlobalTheory.UnramVal
theorem _root_.solution {ϖ : 𝒪[F]} (hϖ : Irreducible ϖ) {x : F} (hx : x ≠ 0) :
    ∃ (k : ℤ) (u : (𝒪[F])ˣ), x = (ϖ : F) ^ k * ((u : 𝒪[F]) : F) := by
  obtain ⟨k, u, h⟩ := IsDiscreteValuationRing.exists_units_eq_smul_zpow_of_irreducible hϖ hx
  refine ⟨k, u, ?_⟩
  rw [h, mul_comm]; rfl
end GlobalTheory.UnramVal
