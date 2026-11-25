-- Prove2me | solution 1 for GlobalTheory.HL.PatternApprox.exists_clear
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:02:59.351254+00:00
-- url     : https://prove2.me/submissions/1368ecf3-d0c7-49e3-92e2-289157195346

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_PsiEDef
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_GFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_StrongApproximationAdditiveQuadraticExtensionStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_PatternUnitriangularStrongApproximation
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
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.PatternApprox
namespace GlobalTheory.HL.PatternApprox
theorem _root_.solution {Fp Ep : Type} [Field Fp] [ValuativeRel Fp] [TopologicalSpace Fp]
    [IsNonarchimedeanLocalField Fp] [CommRing Ep] [Algebra Fp Ep] [Module.Finite Fp Ep]
    (O : Subring Ep) (hO : ∀ x, x ∈ O ↔ IsIntegral 𝒪[Fp] x) {ι : Type} [Fintype ι] (x : ι → Ep) :
    ∃ a : Fp, a ≠ 0 ∧ ∀ i, algebraMap Fp Ep a * x i ∈ O := by
  have hfr : IsFractionRing 𝒪[Fp] Fp := (Valuation.integer.integers (valuation Fp)).isFractionRing
  have halg : ∀ i, IsAlgebraic 𝒪[Fp] (x i) := fun i =>
    (IsFractionRing.isAlgebraic_iff 𝒪[Fp] Fp Ep).mpr (Algebra.IsIntegral.isIntegral (R := Fp) (x i)).isAlgebraic
  choose y hy0 hyi using fun i => (halg i).exists_integral_multiple
  have hym : ∀ k, algebraMap Fp Ep (y k : Fp) ∈ O := fun k => by
    rw [hO, show algebraMap Fp Ep (y k : Fp) = algebraMap 𝒪[Fp] Ep (y k) from
      (IsScalarTower.algebraMap_apply 𝒪[Fp] Fp Ep (y k)).symm]
    exact isIntegral_algebraMap
  refine ⟨∏ k, (y k : Fp), ?_, fun i => ?_⟩
  · rw [Finset.prod_ne_zero_iff]
    intro k _ h
    exact hy0 k (Subtype.ext (by simpa using h))
  · have h1 : algebraMap Fp Ep (y i : Fp) * x i ∈ O := by
      rw [hO, show algebraMap Fp Ep (y i : Fp) = algebraMap 𝒪[Fp] Ep (y i) from
        (IsScalarTower.algebraMap_apply 𝒪[Fp] Fp Ep (y i)).symm, ← Algebra.smul_def]
      exact hyi i
    rw [map_prod, ← Finset.prod_erase_mul _ _ (Finset.mem_univ i), mul_assoc]
    exact O.mul_mem (O.prod_mem fun k _ => hym k) h1
end GlobalTheory.HL.PatternApprox
