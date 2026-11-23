-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.QL.Tame.extendedCharacter_congr_of_tame
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:28:27.434314+00:00
-- url     : https://prove2.me/submissions/984f796e-af23-4d68-affd-ffa5ffddb065

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_InstBorelGL
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_LocalFieldUniformizerNormPropertiesStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_LocalFieldTopologyNormBallsStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_MemIntegralGLIffIntegralUnitDetStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_BlockMatrixMulBlocks
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_ParahoricCharacterModulusProperties
import Theorems.Thm_GlobalTheory_CompanionTheory_QL_Tame_extendedCharacter_units
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
open MeasureTheory Matrix GlobalTheory.CompanionTheory.QL
open scoped ComplexConjugate ValuativeRel
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.QL GlobalTheory.CompanionTheory.QL.Tame
variable {F : Type} [Field F]
namespace GlobalTheory.CompanionTheory.QL.Tame
theorem _root_.solution {nrm : AbsoluteValue F ℝ} {δ : Fˣ →* ℂˣ} (hδ : Del nrm δ) {x y : F}
    (hy : nrm y = 1) (hxy : nrm (x - y) < 1) : chi0 δ x = chi0 δ y := by
  have hy0 : y ≠ 0 := by
    rintro rfl
    simp at hy
  have hx0 : x ≠ 0 := by
    rintro rfl
    simp [hy] at hxy
  have h1 : δ (Units.mk0 x hx0 / Units.mk0 y hy0) = 1 := by
    apply hδ.tame
    have e : (((Units.mk0 x hx0 / Units.mk0 y hy0 : Fˣ) : F) - 1) = (x - y) / y := by
      simp only [Units.val_div_eq_div_val, Units.val_mk0]
      field_simp
    rw [e, map_div₀, hy, div_one]
    exact hxy
  rw [map_div, div_eq_one] at h1
  have ex : x = ((Units.mk0 x hx0 : Fˣ) : F) := rfl
  have ey : y = ((Units.mk0 y hy0 : Fˣ) : F) := rfl
  rw [ex, ey, extendedCharacter_units, extendedCharacter_units, h1]
end GlobalTheory.CompanionTheory.QL.Tame
