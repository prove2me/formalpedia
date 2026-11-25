-- Prove2me | solution 1 for GlobalTheory.DiscOver.mem_spanO
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T06:59:39.204673+00:00
-- url     : https://prove2.me/submissions/868154e0-70ef-4d4b-8648-1cc2b0e2d793

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsEqZpowMulUnit
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsBasisFgMaximalOrderSpanningFree
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_RelIndexSpanLatticeMatrixDetNorm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CardDiscriminantModuleIntegralOverlatticeSpan

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
open GlobalTheory GlobalTheory.DiscOver
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
namespace GlobalTheory.DiscOver
theorem _root_.solution (L : LocE F E) {n m : ℕ} (w : Fin m → Fin n → E) (x : Fin n → E) :
    x ∈ Submodule.span L.O (Set.range w) ↔ ∃ s : Fin m → E, (∀ i, s i ∈ L.O) ∧ ∑ i, s i • w i = x := by
  rw [Submodule.mem_span_range_iff_exists_fun]
  constructor
  · rintro ⟨s, hs⟩
    exact ⟨fun i => s i, fun i => (s i).2, hs⟩
  · rintro ⟨s, h, hs⟩
    exact ⟨fun i => ⟨s i, h i⟩, hs⟩
end GlobalTheory.DiscOver
