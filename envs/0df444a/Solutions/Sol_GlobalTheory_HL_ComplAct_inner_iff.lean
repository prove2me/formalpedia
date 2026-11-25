-- Prove2me | solution 1 for GlobalTheory.HL.ComplAct.inner_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T07:35:51.359972+00:00
-- url     : https://prove2.me/submissions/7d73c619-b295-4c5e-994e-e250399356ad

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_BasisOfIsCompl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MemPerpSpan
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SelfDualLatticeUnipotentTranslateStandardStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_TermInvariantsIndependentOfWitnessesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianFramesComplementUnitaryActsOnTerms
import Theorems.Thm_GlobalTheory_HL_ComplAct_mem_smul
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_HL_StdLat_stdLat_spec
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
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.ComplAct
open GlobalTheory.HL.Eichler GlobalTheory.HL.StdLat
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E} {r k : ℕ} (S : Frames L r k)
variable [IsNonarchimedeanLocalField F] [CharZero F]
namespace GlobalTheory.HL.ComplAct
theorem _root_.solution {g : Fin (r + 1) → S.V} {gs : Fin r → S.V}
    (hg : (g = S.f ∧ gs = S.es) ∨ (g = S.f' ∧ gs = S.es')) {A : Submodule L.O S.V}
    (hA : S.IsInner g gs A) {n : S.GLV} (hn : n ∈ S.Nof g) (x : S.V) :
    x ∈ A ↔ ∃ y ∈ n • S.stdLat g gs A, y ∈ perp L S.Hm (S.spanTo g r) ∧ y - x ∈ S.spanTo g r := by
  rw [(stdLat_spec L r k S g gs hg A hA).2.2 x]
  have hi := (S.Nof g).inv_mem hn
  constructor
  · rintro ⟨y, hy, h1, h2⟩
    refine ⟨n y, Submodule.smul_mem_pointwise_smul y n _ hy, (hn.2.1 y).2 h1, ?_⟩
    simpa using Submodule.add_mem _ (hn.2.2 y h1) h2
  · rintro ⟨y, hy, h1, h2⟩
    refine ⟨n⁻¹ y, (mem_smul S n _ y).1 hy, (hi.2.1 y).2 h1, ?_⟩
    simpa using Submodule.add_mem _ (hi.2.2 y h1) h2
end GlobalTheory.HL.ComplAct
