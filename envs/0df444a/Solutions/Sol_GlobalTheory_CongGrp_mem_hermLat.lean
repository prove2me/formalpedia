-- Prove2me | solution 1 for GlobalTheory.CongGrp.mem_hermLat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T07:29:02.50515+00:00
-- url     : https://prove2.me/submissions/48da3d89-c323-46ec-9a2a-93d4260aeb64

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_HermLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsEqZpowMulUnit
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CongruentOneMatricesTransitiveNearHermitianStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MatrixCongruentOneModUniformizerPowGroupAndOrbit
import Theorems.Thm_GlobalTheory_CongGrp_intM_add
import Theorems.Thm_GlobalTheory_CongGrp_intM_neg
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
open GlobalTheory GlobalTheory.CongGrp
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
namespace GlobalTheory.CongGrp
theorem _root_.solution (L : LocE F E) {m : ℕ} {X : Matrix (Fin m) (Fin m) E} :
    X ∈ hermLat L m ↔ IsHerm L X ∧ IsIntM L X := by
  refine ⟨fun h => ?_, fun h => AddSubgroup.subset_closure h⟩
  induction h using AddSubgroup.closure_induction with
  | mem x hx => exact hx
  | zero => exact ⟨by ext a b; simp [cT], fun a b => zero_mem _⟩
  | add x y _ _ hx hy =>
    refine ⟨?_, intM_add L hx.2 hy.2⟩
    ext a b
    have h1 := congrFun (congrFun hx.1 a) b
    have h2 := congrFun (congrFun hy.1 a) b
    simp only [cT] at h1 h2
    simp [cT, h1, h2]
  | neg x _ hx =>
    refine ⟨?_, intM_neg L hx.2⟩
    ext a b
    have h1 := congrFun (congrFun hx.1 a) b
    simp only [cT] at h1
    simp [cT, h1]
end GlobalTheory.CongGrp
