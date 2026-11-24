-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.QL.Tame.tame_character
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T16:26:21.586269+00:00
-- url     : https://prove2.me/submissions/01f05f12-814d-48a6-b4dd-a297656cf454

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_InstBorelGL
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_LocalFieldUniformizerNormPropertiesStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_LocalFieldTopologyNormBallsStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_MemIntegralGLIffIntegralUnitDetStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_BlockMatrixMulBlocks
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_ParahoricCharacterModulusProperties
import Theorems.Thm_GlobalTheory_CompanionTheory_QL_Tame_bDD_one
import Theorems.Thm_GlobalTheory_CompanionTheory_QL_Tame_extendedCharacter_units
import Theorems.Thm_GlobalTheory_CompanionTheory_QL_Tame_unitCharExtendedByZero_mul
import Theorems.Thm_GlobalTheory_CompanionTheory_QL_Tame_extendedCharacter_congr_of_tame
import Theorems.Thm_GlobalTheory_CompanionTheory_QL_Tame_par_data
import Theorems.Thm_GlobalTheory_CompanionTheory_QL_Tame_lam_mul
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_T_localField_topology_norm_balls
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
namespace GlobalTheory.CompanionTheory.QL.Tame
theorem _root_.solution : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] {O : Subring F} {ϖ : F} {nrm : AbsoluteValue F ℝ} {q : ℕ}, LF O ϖ nrm q → ∀ δ : Fˣ →* ℂˣ, Del nrm δ → ∀ r c : ℕ, lamJ δ (1 : GL (Fin (r + c)) F) = 1 ∧ (∀ k ∈ parJ O ϖ r c, ‖lamJ δ k‖ = 1 ∧ nrm (bAA (k : Matrix (Fin (r + c)) (Fin (r + c)) F)).det = 1 ∧ nrm (bDD (k : Matrix (Fin (r + c)) (Fin (r + c)) F)).det = 1 ∧ ((δ (Matrix.GeneralLinearGroup.det k) : ℂˣ) : ℂ) = chi0 δ (bAA (k : Matrix (Fin (r + c)) (Fin (r + c)) F)).det * lamJ δ k ∧ ∀ k' ∈ parJ O ϖ r c, lamJ δ (k * k') = lamJ δ k * lamJ δ k') ∧ ContinuousOn (fun k : GL (Fin (r + c)) F => lamJ δ k) (parJ O ϖ r c) := by
  intro F _ _ _ _ O ϖ nrm q h δ hδ r c
  obtain ⟨-, hϖ, hO, hlt, -, -, -⟩ := GlobalTheory.T.localField_uniformizer_norm_properties h
  have hne : ∀ {x : F}, nrm x = 1 → x ≠ 0 := by
    rintro x hx rfl
    simp at hx
  refine ⟨?_, ?_, ?_⟩
  · unfold lamJ
    have e : ((1 : GL (Fin (r + c)) F) : Matrix (Fin (r + c)) (Fin (r + c)) F) = 1 := rfl
    rw [e, bDD_one, Matrix.det_one]
    have := extendedCharacter_units δ (1 : Fˣ)
    simpa using this
  · intro k hk
    obtain ⟨hA, hD, o, ho, e⟩ := par_data h hk
    refine ⟨?_, hA, hD, ?_, fun k' hk' => lam_mul h hδ hk hk'⟩
    · unfold lamJ
      have : (bDD (k : Matrix (Fin (r + c)) (Fin (r + c)) F)).det =
          ((Units.mk0 _ (hne hD) : Fˣ) : F) := rfl
      rw [this, extendedCharacter_units]
      exact hδ.unitary _
    · unfold lamJ
      rw [← extendedCharacter_units, ← unitCharExtendedByZero_mul δ (hne hA) (hne hD)]
      apply extendedCharacter_congr_of_tame hδ
      · rw [map_mul, hA, hD, one_mul]
      · rw [Matrix.GeneralLinearGroup.val_det_apply, e]
        exact (hlt _).2 ⟨o, ho, rfl⟩
  · obtain ⟨-, -, -, hcont, -, -⟩ := GlobalTheory.T.localField_topology_norm_balls h
    intro k₀ hk₀
    obtain ⟨-, hD₀, -⟩ := par_data h hk₀
    have hf : Continuous (fun k : GL (Fin (r + c)) F =>
        (bDD (k : Matrix (Fin (r + c)) (Fin (r + c)) F)).det) :=
      Continuous.matrix_det (Continuous.matrix_submatrix Units.continuous_val _ _)
    have hU : {k : GL (Fin (r + c)) F | nrm ((bDD (k : Matrix (Fin (r + c)) (Fin (r + c)) F)).det -
        (bDD (k₀ : Matrix (Fin (r + c)) (Fin (r + c)) F)).det) < 1} ∈ nhds k₀ := by
      refine IsOpen.mem_nhds (isOpen_lt (hcont.comp (hf.sub continuous_const)) continuous_const) ?_
      simp
    refine (continuousWithinAt_const (b := lamJ δ k₀)).congr_of_eventuallyEq ?_ rfl
    filter_upwards [mem_nhdsWithin_of_mem_nhds hU] with k hkU
    exact extendedCharacter_congr_of_tame hδ hD₀ hkU
end GlobalTheory.CompanionTheory.QL.Tame
