-- Prove2me | solution 1 for GlobalTheory.HL.ComplAct.graph_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T07:31:56.097496+00:00
-- url     : https://prove2.me/submissions/02bd5279-f53b-4ec3-8ef0-97242b64371d

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_BasisOfIsCompl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MemPerpSpan
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SelfDualLatticeUnipotentTranslateStandardStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_TermInvariantsIndependentOfWitnessesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianFramesComplementUnitaryActsOnTerms
import Theorems.Thm_GlobalTheory_HL_ComplAct_spanTo_mono
import Theorems.Thm_GlobalTheory_HL_ComplAct_perp_map
import Theorems.Thm_GlobalTheory_HL_ComplAct_hermitianFrames_complementUnitary_fixes_ME
import Theorems.Thm_GlobalTheory_HL_FrameOnto_spanTo_mono


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
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.ComplAct
open GlobalTheory.HL.Eichler GlobalTheory.HL.StdLat
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E} {r k : ℕ} (S : Frames L r k)
variable [IsNonarchimedeanLocalField F] [CharZero F]
omit [IsNonarchimedeanLocalField F] [CharZero F]
namespace GlobalTheory.HL.ComplAct
theorem _root_.solution {h : S.GLV} (hh : h ∈ S.H0) {Λ : Submodule L.O S.V} {p : S.V × S.V}
    (hp : p ∈ S.graphOf Λ) : h • p ∈ S.graphOf (h • Λ) := by
  have hX : ∀ x ∈ S.X, h x = x := fun x hx =>
    hermitianFrames_complementUnitary_fixes_ME S hh x (Submodule.mem_sup_left (spanTo_mono S _ hx))
  have hX' : ∀ x ∈ S.X', h x = x := fun x hx =>
    hermitianFrames_complementUnitary_fixes_ME S hh x (Submodule.mem_sup_right (spanTo_mono S _ hx))
  obtain ⟨y', hy', y, hy, h1, h2, h3, h4, z, hz, h5⟩ := hp
  refine ⟨h y', Submodule.smul_mem_pointwise_smul y' h _ hy', h y,
    Submodule.smul_mem_pointwise_smul y h _ hy, perp_map S hh.1 hX' h1, perp_map S hh.1 hX h2, ?_, ?_,
    h z, Submodule.smul_mem_pointwise_smul z h _ hz, ?_⟩
  · change h y' - h p.1 ∈ _
    rw [← map_sub, hX' _ h3]; exact h3
  · change h y - h p.2 ∈ _
    rw [← map_sub, hX _ h4]; exact h4
  · rw [← map_sub, h5, map_smul]
end GlobalTheory.HL.ComplAct
