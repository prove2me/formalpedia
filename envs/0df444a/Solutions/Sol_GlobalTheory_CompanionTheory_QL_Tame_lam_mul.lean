-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.QL.Tame.lam_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T16:07:16.119358+00:00
-- url     : https://prove2.me/submissions/3ec32629-08dc-4f99-8744-cc155e0cb613

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_InstBorelGL
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_LocalFieldUniformizerNormPropertiesStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_LocalFieldTopologyNormBallsStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_MemIntegralGLIffIntegralUnitDetStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_BlockMatrixMulBlocks
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_ParahoricCharacterModulusProperties
import Theorems.Thm_GlobalTheory_CompanionTheory_QL_Tame_det_congr_mod
import Theorems.Thm_GlobalTheory_CompanionTheory_QL_Tame_unitCharExtendedByZero_mul
import Theorems.Thm_GlobalTheory_CompanionTheory_QL_Tame_extendedCharacter_congr_of_tame
import Theorems.Thm_GlobalTheory_CompanionTheory_QL_Tame_par_data
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_CompanionTheory_QL_BlockMul_blocks_mul
import Theorems.Thm_GlobalTheory_T_localField_uniformizer_norm_properties
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
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {O : Subring F} {ϖ : F} {nrm : AbsoluteValue F ℝ} {q : ℕ}
namespace GlobalTheory.CompanionTheory.QL.Tame
theorem _root_.solution (h : LF O ϖ nrm q) {δ : Fˣ →* ℂˣ} (hδ : Del nrm δ) {r c : ℕ}
    {k k' : GL (Fin (r + c)) F} (hk : k ∈ parJ O ϖ r c) (hk' : k' ∈ parJ O ϖ r c) :
    lamJ δ (k * k') = lamJ δ k * lamJ δ k' := by
  obtain ⟨-, hϖ, hO, hlt, -, -, -⟩ := GlobalTheory.T.localField_uniformizer_norm_properties h
  obtain ⟨-, hD, -⟩ := par_data h hk
  obtain ⟨-, hD', -⟩ := par_data h hk'
  unfold lamJ
  have hC := hk.2
  set M : Matrix (Fin (r + c)) (Fin (r + c)) F := (k : Matrix (Fin (r + c)) (Fin (r + c)) F) with hMdef
  set M' : Matrix (Fin (r + c)) (Fin (r + c)) F := (k' : Matrix (Fin (r + c)) (Fin (r + c)) F) with hM'def
  have hM : IsInt O M := hk.1.1
  have hM' : IsInt O M' := hk'.1.1
  have hprod : ((k * k' : GL (Fin (r + c)) F) : Matrix (Fin (r + c)) (Fin (r + c)) F) = M * M' := rfl
  have hblock : bDD (M * M') = bDA M * bAD M' + bDD M * bDD M' :=
    (GlobalTheory.CompanionTheory.QL.BlockMul.blocks_mul r c c c M M').2.2.2
  rw [hprod, hblock]
  choose o ho e using hC
  have hCB : ∀ i j, ∃ t ∈ O, (bDA M * bAD M') i j = ϖ * t := by
    intro i j
    refine ⟨∑ l, o i l * bAD M' l j, O.sum_mem fun l _ => O.mul_mem (ho i l) (hM' _ _), ?_⟩
    rw [Matrix.mul_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [e i l, mul_assoc]
  have hDD : ∀ i j, (bDD M * bDD M') i j ∈ O := by
    intro i j
    rw [Matrix.mul_apply]
    exact O.sum_mem fun l _ => O.mul_mem (hM _ _) (hM' _ _)
  obtain ⟨t, ht, et⟩ := det_congr_mod O hϖ (bDA M * bAD M' + bDD M * bDD M') (bDD M * bDD M')
    (by
      intro i j
      obtain ⟨t, ht, et⟩ := hCB i j
      rw [Matrix.add_apply, et]
      exact O.add_mem (O.mul_mem hϖ ht) (hDD i j))
    hDD
    (by
      intro i j
      obtain ⟨t, ht, et⟩ := hCB i j
      exact ⟨t, ht, by rw [Matrix.add_apply, et]; ring⟩)
  have hn : nrm (bDD M * bDD M').det = 1 := by
    rw [Matrix.det_mul, map_mul, hD, hD', one_mul]
  have hne : ∀ {x : F}, nrm x = 1 → x ≠ 0 := by
    rintro x hx rfl
    simp at hx
  rw [extendedCharacter_congr_of_tame hδ hn (by rw [et]; exact (hlt _).2 ⟨t, ht, rfl⟩), Matrix.det_mul,
    unitCharExtendedByZero_mul δ (hne hD) (hne hD')]
end GlobalTheory.CompanionTheory.QL.Tame
