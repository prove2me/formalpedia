-- Prove2me | solution 1 for GlobalTheory.T.parahoric_character_modulus_properties
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T16:45:16.629028+00:00
-- url     : https://prove2.me/submissions/dee33c01-0caa-4b94-89cc-c22a8dd195af

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_ParahoricCharacterModulusProperties
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_InstBorelGL
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_ParahoricCharacterModulusPropertiesStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_QL_Tame_tame_character


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix GlobalTheory.CompanionTheory.QL
open scoped ComplexConjugate ValuativeRel
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] {O : Subring F} {ϖ : F} {nrm : AbsoluteValue F ℝ} {q : ℕ}, LF O ϖ nrm q → ∀ δ : Fˣ →* ℂˣ, Del nrm δ → ∀ r c : ℕ, lamJ δ (1 : GL (Fin (r + c)) F) = 1 ∧ (∀ k ∈ parJ O ϖ r c, ‖lamJ δ k‖ = 1 ∧ nrm (bAA (k : Matrix (Fin (r + c)) (Fin (r + c)) F)).det = 1 ∧ nrm (bDD (k : Matrix (Fin (r + c)) (Fin (r + c)) F)).det = 1 ∧ ((δ (Matrix.GeneralLinearGroup.det k) : ℂˣ) : ℂ) = chi0 δ (bAA (k : Matrix (Fin (r + c)) (Fin (r + c)) F)).det * lamJ δ k ∧ ∀ k' ∈ parJ O ϖ r c, lamJ δ (k * k') = lamJ δ k * lamJ δ k') ∧ ContinuousOn (fun k : GL (Fin (r + c)) F => lamJ δ k) (parJ O ϖ r c) := by
  first | exact @GlobalTheory.CompanionTheory.QL.Tame.tame_character | exact GlobalTheory.CompanionTheory.QL.Tame.tame_character | (intros; apply GlobalTheory.CompanionTheory.QL.Tame.tame_character <;> assumption)
end _root_.GlobalTheory.T
