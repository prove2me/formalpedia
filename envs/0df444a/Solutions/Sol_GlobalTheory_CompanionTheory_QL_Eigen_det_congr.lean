-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.QL.Eigen.det_congr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T12:55:20.527529+00:00
-- url     : https://prove2.me/submissions/f87a1428-1b90-4ff6-8229-cb9ea905f870

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_InstBorelGL
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_BlockMatrixMulBlocks
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_LocalFieldUniformizerNormProperties
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_ParahoricSubgroupCompactOpenMeasure
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_MemIntegralGLIffIntegralUnitDetStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_ParahoricCharacterModulusPropertiesStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_ParabolicTestFunctionEquivariant
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.QL GlobalTheory.CompanionTheory.QL.Eigen
variable {F : Type} [Field F]
namespace GlobalTheory.CompanionTheory.QL.Eigen
theorem _root_.solution {O : Subring F} {ϖ : F} (hϖ : ϖ ∈ O) {n : ℕ} {P Q : Matrix (Fin n) (Fin n) F}
    (hP : P ∈ intMat O n n) (hQ : Q ∈ intMat O n n) (h : P - Q ∈ IIset O ϖ) :
    ∃ o ∈ O, P.det - Q.det = ϖ * o := by
  let P' : Matrix (Fin n) (Fin n) O := fun i j => ⟨P i j, hP i j⟩
  let Q' : Matrix (Fin n) (Fin n) O := fun i j => ⟨Q i j, hQ i j⟩
  let I : Ideal O := Ideal.span {(⟨ϖ, hϖ⟩ : O)}
  have hm : (Ideal.Quotient.mk I).mapMatrix P' = (Ideal.Quotient.mk I).mapMatrix Q' := by
    ext i j
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply]
    refine Ideal.Quotient.eq.2 (Ideal.mem_span_singleton'.2 ?_)
    obtain ⟨o, ho, e⟩ := h i j
    refine ⟨⟨o, ho⟩, Subtype.ext ?_⟩
    show o * ϖ = P i j - Q i j
    rw [mul_comm]; exact e.symm
  have hd : Ideal.Quotient.mk I P'.det = Ideal.Quotient.mk I Q'.det := by
    rw [RingHom.map_det, RingHom.map_det, hm]
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.1 (Ideal.Quotient.eq.1 hd)
  have hPd : P.det = ((P'.det : O) : F) := by
    have e : O.subtype.mapMatrix P' = P := by ext i j; rfl
    have := RingHom.map_det O.subtype P'
    rw [e] at this
    exact this.symm
  have hQd : Q.det = ((Q'.det : O) : F) := by
    have e : O.subtype.mapMatrix Q' = Q := by ext i j; rfl
    have := RingHom.map_det O.subtype Q'
    rw [e] at this
    exact this.symm
  have hv : (a : F) * ϖ = ((P'.det : O) : F) - ((Q'.det : O) : F) := congrArg Subtype.val ha
  exact ⟨a, a.2, by rw [hPd, hQd, ← hv, mul_comm]⟩
end GlobalTheory.CompanionTheory.QL.Eigen
