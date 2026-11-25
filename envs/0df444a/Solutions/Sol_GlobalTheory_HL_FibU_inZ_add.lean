-- Prove2me | solution 1 for GlobalTheory.HL.FibU.inZ_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T08:08:14.663825+00:00
-- url     : https://prove2.me/submissions/3c9e531b-214a-4c0b-aed3-540ada8411b8

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
import Theorems.Thm_GlobalTheory_HL_FibU_hf_addr
import Theorems.Thm_GlobalTheory_HL_FibU_hf_smull
import Theorems.Thm_GlobalTheory_HL_FibU_hf_smulr
import Theorems.Thm_GlobalTheory_HL_FibU_hf_cj
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_HL_Eichler_hf_cj
import Theorems.Thm_GlobalTheory_UnramOrder_exists_int_of_fixed
import Theorems.Thm_GlobalTheory_UnramOrder_exists_trace
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL GlobalTheory.IdxInt MeasureTheory
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.FibU
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E} {r k : ℕ} (S : Frames L r k)
namespace GlobalTheory.HL.FibU
theorem _root_.solution {Λ : Submodule L.O S.V} (hΛ : IsSD L S.Hm Λ) {N : ℕ} (hN : S.a ≤ N) {u y : S.V}
    (hu : u ∈ Λ) (hy : y ∈ Λ) (hZ : S.InZ u) : S.InZ (u + algebraMap F E ((S.ϖ : F) ^ N) • y) := by
  obtain ⟨c, hc⟩ := hZ
  have h0 : (S.ϖ : F) ≠ 0 := fun h => S.ϖ_irr.ne_zero (Subtype.ext h)
  obtain ⟨m, hm⟩ : ∃ m : ℕ, (N : ℤ) = S.a + m := ⟨(N - S.a).toNat, by omega⟩
  have hpow : (S.ϖ : F) ^ N = (S.ϖ : F) ^ S.a * (S.ϖ : F) ^ m := by
    rw [← zpow_natCast, hm, zpow_add₀ h0, zpow_natCast]
  obtain ⟨t, ht⟩ := GlobalTheory.UnramOrder.exists_trace L ((hΛ.2 y).2 hy u hu)
  obtain ⟨s, hs⟩ := GlobalTheory.UnramOrder.exists_int_of_fixed L ((hΛ.2 y).2 hy y hy) (hf_cj L _ S.herm.1 y y)
  rw [hf_cj L _ S.herm.1] at ht
  refine ⟨c + S.ϖ ^ m * (t + S.ϖ ^ N * s), ?_⟩
  unfold Frames.h at hc ⊢
  simp only [hf_addl, hf_addr, hf_smull, hf_smulr, AlgEquiv.commutes, hc, hs]
  push_cast
  have h2 := congrArg (algebraMap F E) hpow
  simp only [map_mul, map_add, map_pow, ← ht] at h2 ⊢
  linear_combination (hf L S.Hm u y + hf L S.Hm y u + algebraMap F E S.ϖ ^ N * algebraMap F E s) * h2
end GlobalTheory.HL.FibU
