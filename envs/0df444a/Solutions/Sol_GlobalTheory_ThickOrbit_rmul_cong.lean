-- Prove2me | solution 1 for GlobalTheory.ThickOrbit.rmul_cong
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T07:52:55.416321+00:00
-- url     : https://prove2.me/submissions/303609b2-9c69-4865-b43a-2e95ac662c5f

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsIntegralIff
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_HermLat
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NcardImageOfLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CongruentOneMatricesTransitiveNearHermitianStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MatrixCongruentOneModUniformizerPowGroupAndOrbitStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsIsometryNearIdentityCloseTuplesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsIsometryTupleMatrixRightMulNearIdentityStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_AlgMem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ThickOrbitSelfDualUnramifiedLattice
import Theorems.Thm_GlobalTheory_ThickOrbit_smul_mem
import Theorems.Thm_GlobalTheory_ThickOrbit_rmul_one
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
open GlobalTheory GlobalTheory.ThickOrbit
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
namespace GlobalTheory.ThickOrbit
theorem _root_.solution (L : LocE F E) {ϖ : 𝒪[F]} {n m i : ℕ} {Λ : Submodule L.O (Fin n → E)}
    {x : Fin m → Fin n → E} (hx : ∀ a, x a ∈ Λ) {A : Matrix (Fin m) (Fin m) E}
    (hA : A ∈ congK L ϖ m i) (a : Fin m) :
    ∃ w ∈ Λ, rmul x A a - x a = algebraMap F E ((ϖ : F) ^ i) • w := by
  choose c hc h using hA
  refine ⟨∑ k, c k a • x k, Λ.sum_mem fun k _ => smul_mem L (hc k a) (hx k), ?_⟩
  conv_lhs => rw [← congrFun (rmul_one x) a]
  simp only [rmul, Finset.smul_sum, smul_smul, ← h, sub_smul, Finset.sum_sub_distrib]
end GlobalTheory.ThickOrbit
