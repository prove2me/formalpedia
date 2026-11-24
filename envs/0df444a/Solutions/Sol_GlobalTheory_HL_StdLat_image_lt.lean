-- Prove2me | solution 1 for GlobalTheory.HL.StdLat.image_lt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T13:20:17.583946+00:00
-- url     : https://prove2.me/submissions/7c201630-1893-4d72-a3b0-df0cc17761f4

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_EichlerIsometry
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MemPerpSpan

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
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.StdLat
open GlobalTheory.HL.Eichler
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable (L : LocE F E) {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E)
namespace GlobalTheory.HL.StdLat
theorem _root_.solution {r : ℕ} {V : Type} (g : Fin (r + 1) → V) :
    g '' {i | (i : ℕ) < r} = Set.range fun j : Fin r => g j.castSucc := by
  ext x
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact ⟨⟨i, hi⟩, rfl⟩
  · rintro ⟨j, rfl⟩
    exact ⟨j.castSucc, j.2, rfl⟩
end GlobalTheory.HL.StdLat
