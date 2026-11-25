-- Prove2me | solution 1 for GlobalTheory.HL.PrimVol.mem_mul_tup
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:14:07.591068+00:00
-- url     : https://prove2.me/submissions/d4caa6b7-3d9e-4f27-a1cf-da3461de8d17

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_HermLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CardPrimitiveTuplesHermitianGramModUniformizerStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_OrthonormalBasisAndOneOrbit
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CommensurableCosetUnionContentIndependentNonnegStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_RelIndexTupleLatticeHermitianLatticeUniformizerStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_PrimitiveTuplesHermitianGramCosetContent
import Theorems.Thm_GlobalTheory_GramCount_Prim_map


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
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.PrimVol
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E)
namespace GlobalTheory.HL.PrimVol
theorem _root_.solution {n m : ℕ} (Λ : Submodule L.O (Fin n → E)) (p : E) (t : Fin m → Fin n → E) :
    t ∈ (tupLat L Λ m).map (DistribMulAction.toAddMonoidHom _ p) ↔
      ∃ w : Fin m → Fin n → E, (∀ a, w a ∈ Λ) ∧ t = p • w := by
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact ⟨w, fun a => hw a trivial, rfl⟩
  · rintro ⟨w, hw, rfl⟩
    exact ⟨w, fun a _ => hw a, rfl⟩
end GlobalTheory.HL.PrimVol
