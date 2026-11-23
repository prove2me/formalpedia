-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.QL.Tame.det_congr_mod
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:29:13.440453+00:00
-- url     : https://prove2.me/submissions/8d06ff7e-c7e6-4636-a1cf-60a7f1f0d45b

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_InstBorelGL
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_LocalFieldUniformizerNormPropertiesStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_LocalFieldTopologyNormBallsStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_MemIntegralGLIffIntegralUnitDetStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_BlockMatrixMulBlocks
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_ParahoricCharacterModulusProperties
import Theorems.Thm_GlobalTheory_CompanionTheory_QL_Tame_det_eq_coe
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
theorem _root_.solution {ι : Type} [Fintype ι] [DecidableEq ι] (O : Subring F) {ϖ : F} (hϖ : ϖ ∈ O)
    (X Y : Matrix ι ι F) (hX : ∀ i j, X i j ∈ O) (hY : ∀ i j, Y i j ∈ O)
    (h : ∀ i j, ∃ o ∈ O, X i j - Y i j = ϖ * o) : ∃ o ∈ O, X.det - Y.det = ϖ * o := by
  let Xo : Matrix ι ι O := fun i j => ⟨X i j, hX i j⟩
  let Yo : Matrix ι ι O := fun i j => ⟨Y i j, hY i j⟩
  let I : Ideal O := Ideal.span {⟨ϖ, hϖ⟩}
  have hmap : (Ideal.Quotient.mk I).mapMatrix Xo = (Ideal.Quotient.mk I).mapMatrix Yo := by
    ext i j
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply]
    rw [Ideal.Quotient.eq, Ideal.mem_span_singleton']
    obtain ⟨o, ho, e⟩ := h i j
    refine ⟨⟨o, ho⟩, Subtype.ext ?_⟩
    change o * ϖ = X i j - Y i j
    rw [e, mul_comm]
  have hdet : Ideal.Quotient.mk I Xo.det = Ideal.Quotient.mk I Yo.det := by
    rw [RingHom.map_det, RingHom.map_det, hmap]
  rw [Ideal.Quotient.eq, Ideal.mem_span_singleton'] at hdet
  obtain ⟨a, ha⟩ := hdet
  refine ⟨a, a.2, ?_⟩
  rw [det_eq_coe O X hX, det_eq_coe O Y hY]
  have := congrArg Subtype.val ha
  change (a : F) * ϖ = ((Xo.det : O) : F) - ((Yo.det : O) : F) at this
  change ((Xo.det : O) : F) - ((Yo.det : O) : F) = ϖ * a
  rw [← this, mul_comm]
end GlobalTheory.CompanionTheory.QL.Tame
