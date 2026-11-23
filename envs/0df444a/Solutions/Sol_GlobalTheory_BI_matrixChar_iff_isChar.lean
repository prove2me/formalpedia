-- Prove2me | solution 1 for GlobalTheory.BI.matrixChar_iff_isChar
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:19:43.054236+00:00
-- url     : https://prove2.me/submissions/5851cfe7-a42a-4b92-9420-bf1f6f224764

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_MatrixTraceIffIsCharacterOverSubfieldComplex

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI
open GlobalTheory GlobalTheory.BI
namespace GlobalTheory.BI
theorem _root_.solution : ∀ (G : Type) [Group G] (χ : G → ℂ),
    (∃ (n : ℕ) (ρ : G →* GL (Fin n) ℂ), ∀ x, χ x = Matrix.trace (ρ x : Matrix (Fin n) (Fin n) ℂ)) ↔
      IsChar ℂ ℂ χ := by
  intro G _ χ
  constructor
  · rintro ⟨n, ρ, hρ⟩
    refine ⟨n, (Matrix.toLinAlgEquiv' (R := ℂ) (n := Fin n)).toRingEquiv.toMonoidHom.comp
      ((Units.coeHom _).comp ρ), fun g => ?_⟩
    rw [hρ g]
    show _ = Representation.character _ g
    rw [Representation.character,
      LinearMap.trace_eq_matrix_trace ℂ (Pi.basisFun ℂ (Fin n)), LinearMap.toMatrix_eq_toMatrix']
    change _ = (LinearMap.toMatrix' (Matrix.toLin' _)).trace
    rw [LinearMap.toMatrix'_toLin']
    rfl
  · rintro ⟨n, ρ, hρ⟩
    refine ⟨n, Matrix.GeneralLinearGroup.toLin.symm.toMonoidHom.comp ρ.asGroupHom, fun g => ?_⟩
    rw [hρ g]
    show Representation.character _ g = _
    rw [Representation.character,
      LinearMap.trace_eq_matrix_trace ℂ (Pi.basisFun ℂ (Fin n)), LinearMap.toMatrix_eq_toMatrix']
    rfl
end GlobalTheory.BI
