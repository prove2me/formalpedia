-- Prove2me | solution 1 for GlobalTheory.IdealResProd.val_unif
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T07:45:54.466148+00:00
-- url     : https://prove2.me/submissions/7086cc37-2c33-4d2a-818d-c532a8c8cad0

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_PsiEDef
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_GFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsEqZpowMulUnit
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsIntegralOfQuad
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_AbsNormEqFinprod
import Theorems.Thm_GlobalTheory_IdealResProd_val_le_iff
import Theorems.Thm_GlobalTheory_IdealResProd_val_unit
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_HL_PlacesInt_val_le_iff
import Theorems.Thm_GlobalTheory_UnramVal_exists_eq_zpow_mul_unit
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
open GlobalTheory GlobalTheory.IdealResProd
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E}
variable {p : HeightOneSpectrum (𝓞 F)}
namespace GlobalTheory.IdealResProd
theorem _root_.solution (A : LocAt F E sig p) {ϖ : 𝒪[A.Fp]} (hϖ : Irreducible ϖ) {π : F}
    (hπ : p.valuation F π = WithZero.exp (-1)) :
    valuation A.Fp (A.ιF π) = valuation A.Fp ϖ := by
  haveI := A.lf
  have h0 : (ϖ : A.Fp) ≠ 0 := fun h => hϖ.ne_zero (Subtype.ext h)
  have hv0 : valuation A.Fp ϖ ≠ 0 := by simpa using h0
  have hlt : valuation A.Fp ϖ < 1 := by
    refine lt_of_le_of_ne ϖ.2 fun h => hϖ.not_isUnit ?_
    exact ((Valuation.integer.integers (valuation A.Fp)).isUnit_iff_valuation_eq_one).2 h
  have hπ0 : π ≠ 0 := by rintro rfl; simp at hπ; exact WithZero.exp_ne_zero hπ.symm
  have hπ1 : valuation A.Fp (A.ιF π) < 1 := by
    have : ¬ valuation A.Fp (A.ιF 1) ≤ valuation A.Fp (A.ιF π) := by
      rw [val_le_iff, hπ, map_one, not_le, ← WithZero.exp_zero, WithZero.exp_lt_exp]; norm_num
    simpa using this
  apply le_antisymm
  · obtain ⟨k, u, hk⟩ := GlobalTheory.UnramVal.exists_eq_zpow_mul_unit hϖ ((map_ne_zero A.ιF).2 hπ0)
    rw [hk, map_mul, val_unit, mul_one, map_zpow₀] at hπ1 ⊢
    have hk1 : 0 < k := (zpow_lt_one_iff_right_of_lt_one₀ (zero_lt_iff.2 hv0) hlt).1 hπ1
    calc _ ≤ valuation A.Fp ϖ ^ (1 : ℤ) := zpow_le_zpow_right_of_le_one₀ (zero_lt_iff.2 hv0) hlt.le hk1
      _ = _ := zpow_one _
  · have hn : {z : A.Fp | valuation A.Fp z = valuation A.Fp ϖ} ∈ nhds (ϖ : A.Fp) := by
      rw [IsValuativeTopology.mem_nhds_iff]
      refine ⟨Units.mk0 _ hv0, ?_⟩
      rintro _ ⟨z, hz, rfl⟩
      exact (valuation A.Fp).map_add_eq_of_lt_left hz
    obtain ⟨y, hy⟩ := A.dense.mem_nhds hn
    have hy : valuation A.Fp (A.ιF y) = valuation A.Fp ϖ := hy
    rw [← hy, val_le_iff, hπ]
    have h1 : ¬ p.valuation F 1 ≤ p.valuation F y := by
      rw [← val_le_iff A, hy, map_one, map_one, not_le]; exact hlt
    rw [map_one, not_le] at h1
    by_cases hz : p.valuation F y = 0
    · rw [hz]; exact zero_le
    · rw [← WithZero.exp_log hz] at h1 ⊢
      rw [← WithZero.exp_zero, WithZero.exp_lt_exp] at h1
      rw [WithZero.exp_le_exp]; omega
end GlobalTheory.IdealResProd
