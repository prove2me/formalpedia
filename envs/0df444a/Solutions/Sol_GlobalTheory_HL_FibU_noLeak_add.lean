-- Prove2me | solution 1 for GlobalTheory.HL.FibU.noLeak_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T08:08:16.374661+00:00
-- url     : https://prove2.me/submissions/4333f6a9-b1ff-4bb5-aa04-55ae9f20135d

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_Cint
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NoLeak
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianDoubleCosetTermBasicFactsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_QuadricCharacterLeakSharesFiniteStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IndexMeasureIntegralEqMeanOverRepresentativesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsPowSmulMemOfIsLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_TermIntegralNearOneBound
import Theorems.Thm_GlobalTheory_HL_FibU_hf_addl
import Theorems.Thm_GlobalTheory_HL_FibU_hf_smull
import Theorems.Thm_GlobalTheory_HL_FibU_hf_smulr
import Theorems.Thm_GlobalTheory_HL_FibU_exists_inv_one_add
import Theorems.Thm_GlobalTheory_UnramOrder_algebraMap_mem_iff
import Theorems.Thm_GlobalTheory_UnramOrder_cj_mem


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL GlobalTheory.IdxInt MeasureTheory
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.FibU
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E} {r k : ℕ} (S : Frames L r k)
namespace GlobalTheory.HL.FibU
theorem _root_.solution {Λ : Submodule L.O S.V} (hΛ : IsSD L S.Hm Λ) {N : ℕ} (hN : 1 ≤ N) {u y : S.V}
    (hy : y ∈ Λ) (hZ : S.NoLeak Λ u) : S.NoLeak Λ (u + algebraMap F E ((S.ϖ : F) ^ N) • y) := by
  obtain ⟨x, hx, hxW, hux⟩ := hZ
  obtain ⟨m, rfl⟩ : ∃ m, N = m + 1 := ⟨N - 1, by omega⟩
  have hp : algebraMap F E ((S.ϖ : F) ^ m) ∈ L.O :=
    (GlobalTheory.UnramOrder.algebraMap_mem_iff L _).2 (pow_mem S.ϖ.2 m)
  obtain ⟨z, hz, hz1⟩ := exists_inv_one_add L S.ϖ S.ϖ_irr (L.O.mul_mem hp ((hΛ.2 x).2 hx y hy))
  refine ⟨L.cj z • x, Λ.smul_mem ⟨_, GlobalTheory.UnramOrder.cj_mem L hz⟩ hx, S.W0.smul_mem _ hxW, ?_⟩
  unfold Frames.h at hux ⊢
  rw [hf_smulr, hf_addl, hf_smull, hux, L.cj_cj, pow_succ, map_mul]
  linear_combination hz1
end GlobalTheory.HL.FibU
