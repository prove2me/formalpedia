-- Prove2me | solution 1 for GlobalTheory.CongGrp.congK_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:03:09.669672+00:00
-- url     : https://prove2.me/submissions/deefe670-473d-4100-8899-4470e0a7d702

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_HermLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsEqZpowMulUnit
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CongruentOneMatricesTransitiveNearHermitianStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MatrixCongruentOneModUniformizerPowGroupAndOrbit
import Theorems.Thm_GlobalTheory_CongGrp_intM_mul
import Theorems.Thm_GlobalTheory_CongGrp_intM_add
import Theorems.Thm_GlobalTheory_CongGrp_mem_congK
import Theorems.Thm_GlobalTheory_CongGrp_congK_int

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
theorem _root_.solution (L : LocE F E) (ϖ : 𝒪[F]) {m i : ℕ} {A B : Matrix (Fin m) (Fin m) E}
    (hA : A ∈ congK L ϖ m i) (hB : B ∈ congK L ϖ m i) : A * B ∈ congK L ϖ m i := by
  have hB' := congK_int L ϖ hB
  obtain ⟨C, hC, rfl⟩ := (mem_congK L ϖ).1 hA
  obtain ⟨D, hD, hBD⟩ := (mem_congK L ϖ).1 hB
  refine (mem_congK L ϖ).2 ⟨D + C * B, intM_add L hD (intM_mul L hC hB'), ?_⟩
  rw [add_mul, one_mul, smul_add, ← add_assoc, ← hBD, Matrix.smul_mul]
end GlobalTheory.CongGrp
