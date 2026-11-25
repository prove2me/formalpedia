-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.QL.PsiVolume.phi_mul_conj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:55:26.875734+00:00
-- url     : https://prove2.me/submissions/ce71c9f5-a41c-41ea-a13b-38c09be81b40

import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_InstBorelGL
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_BlockMatrixMulBlocks
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_ParabolicElementBlocks
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_LocalFieldUniformizerNormProperties
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_LocalFieldTopologyNormBallsStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_MatrixAdditiveHaarNormalizedStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_MeasureInvertibleIntegralMatricesStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_WeilIntegralUnipotentLeviFormula
import Theorems.Thm_GlobalTheory_CompanionTheory_QL_PsiVolume_blocks_mul_pEl
import Theorems.Thm_GlobalTheory_CompanionTheory_QL_PsiVolume_unramifiedCharExt_inv_mul_conj_inv
import Theorems.Thm_GlobalTheory_CompanionTheory_QL_PsiVolume_det_ne_of_mem_Jset
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.QL GlobalTheory.CompanionTheory.QL.PsiVolume
variable {F : Type} [Field F]
namespace GlobalTheory.CompanionTheory.QL.PsiVolume
theorem _root_.solution (O : Subring F) (ϖ : F) {δ : Fˣ →* ℂˣ} (hδ : ∀ x, ‖((δ x : ℂˣ) : ℂ)‖ = 1)
    {r d c : ℕ} (B : Matrix (Fin r) (Fin c) F) (m : GL (Fin c) F)
    (x : Matrix (Fin (r + d)) (Fin (r + c)) F) :
    phiQ O ϖ δ r d c (x * (pEl 1 B m : GL (Fin (r + c)) F).val) * conj (phiQ O ϖ δ r d c x) =
      (psiSet O ϖ B m : Set (Matrix (Fin (r + d)) (Fin (r + c)) F)).indicator (fun _ => (1 : ℂ)) x := by
  obtain ⟨h1, h2, h3, h4⟩ := blocks_mul_pEl x B m
  by_cases hx : x ∈ (psiSet O ϖ B m : Set (Matrix (Fin (r + d)) (Fin (r + c)) F))
  · rw [Set.indicator_of_mem hx]
    obtain ⟨a, b, e, f, g, h⟩ := hx
    have p1 : phiQ O ϖ δ r d c x = (chi0 δ (bAA x).det)⁻¹ := by
      unfold phiQ; rw [if_pos ⟨a, b, e, f⟩]
    have p2 : phiQ O ϖ δ r d c (x * (pEl 1 B m : GL (Fin (r + c)) F).val) =
        (chi0 δ (bAA x).det)⁻¹ := by
      unfold phiQ
      rw [h1, h2, h3, h4, if_pos ⟨a, b, g, h⟩]
    rw [p1, p2]
    exact unramifiedCharExt_inv_mul_conj_inv hδ (det_ne_of_mem_Jset a)
  · rw [Set.indicator_of_notMem hx]
    by_cases hc : bAA x ∈ Jset (GLint O r) ∧ bDA x ∈ IIset O ϖ ∧ bAD x ∈ intMat O r c ∧
        bDD x ∈ intMat O d c
    · have p2 : phiQ O ϖ δ r d c (x * (pEl 1 B m : GL (Fin (r + c)) F).val) = 0 := by
        unfold phiQ
        rw [h1, h2, h3, h4, if_neg]
        rintro ⟨-, -, g, h⟩
        exact hx ⟨hc.1, hc.2.1, hc.2.2.1, hc.2.2.2, g, h⟩
      rw [p2, zero_mul]
    · have p1 : phiQ O ϖ δ r d c x = 0 := by
        unfold phiQ; rw [if_neg hc]
      rw [p1]; simp
end GlobalTheory.CompanionTheory.QL.PsiVolume
