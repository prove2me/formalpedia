-- Prove2me | solution 1 for GlobalTheory.CongGrp.congK_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T07:44:34.735055+00:00
-- url     : https://prove2.me/submissions/207d9652-c1b8-41b6-b506-41ab77c39bf9

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
import Theorems.Thm_GlobalTheory_CongGrp_intM_smul
import Theorems.Thm_GlobalTheory_CongGrp_intM_one
import Theorems.Thm_GlobalTheory_CongGrp_mem_congK
import Theorems.Thm_P2M_GlobalTheory_CongGrp_pow_mem__de67754d33b0

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
open GlobalTheory GlobalTheory.CongGrp
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable [IsNonarchimedeanLocalField F] [CharZero F]
namespace GlobalTheory.CongGrp
theorem _root_.solution (L : LocE F E) (ϖ : 𝒪[F]) {m i : ℕ}
    {A : Matrix (Fin m) (Fin m) E} (hA : A ∈ congK L ϖ m i) : IsIntM L A := by
  obtain ⟨C, hC, rfl⟩ := (mem_congK L ϖ).1 hA
  exact intM_add L (intM_one L) (intM_smul L (pow_mem' L ϖ i) hC)
end GlobalTheory.CongGrp
