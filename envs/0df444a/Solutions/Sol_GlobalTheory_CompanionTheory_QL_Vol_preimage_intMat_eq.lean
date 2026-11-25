-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.QL.Vol.preimage_intMat_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:37:16.566264+00:00
-- url     : https://prove2.me/submissions/10aee76f-b07f-4cc0-ab17-768af87b8c20

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_InstBorelGL
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_MatrixAdditiveHaarNormalizedStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_MatrixHaarRightTranslateStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_MeasureUniformizerMultipleMatrices
import Theorems.Thm_GlobalTheory_CompanionTheory_QL_Vol_coe_scalarInvGL
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GroundTheory_Automorphic_Cartan_dominantEquivDoubleCoset_apply
import Theorems.Thm_GroundTheory_Automorphic_GLnLocal_quotientEquivLattice_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks
attribute [local simp] GroundTheory.Automorphic.Cartan.dominantEquivDoubleCoset_apply
attribute [local simp] GroundTheory.Automorphic.GLnLocal.quotientEquivLattice_mk



set_option autoImplicit false
open MeasureTheory Matrix GlobalTheory.CompanionTheory.QL
open scoped ComplexConjugate ValuativeRel
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.QL GlobalTheory.CompanionTheory.QL.Vol
namespace GlobalTheory.CompanionTheory.QL.Vol
theorem _root_.solution {F : Type} [Field F] (O : Subring F) {ϖ : F} (hϖ : ϖ ≠ 0) (n m : ℕ) :
    (fun x : Matrix (Fin n) (Fin m) F => x * ((scalarInvGL m ϖ hϖ : GL (Fin m) F) : Matrix (Fin m) (Fin m) F)) ⁻¹'
      intMat O n m = (IIset O ϖ : Set (Matrix (Fin n) (Fin m) F)) := by
  ext x
  simp only [Set.mem_preimage, intMat, Set.mem_setOf_eq, IIset, coe_scalarInvGL, Matrix.mul_diagonal]
  constructor
  · intro h i j
    exact ⟨x i j * ϖ⁻¹, h i j, by field_simp⟩
  · intro h i j
    obtain ⟨o, ho, e⟩ := h i j
    have : x i j * ϖ⁻¹ = o := by rw [e]; field_simp
    rw [this]; exact ho
end GlobalTheory.CompanionTheory.QL.Vol
