-- Prove2me | solution 1 for GlobalTheory.KSp.parFun_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:43:17.868381+00:00
-- url     : https://prove2.me/submissions/2a405c71-0844-46ec-b986-44c2e09b1762

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_UnipVal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SplitUnitarySiegelParabolicBlockRelationsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HermitianMatrixColumnPairingAlgebraicPropertiesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_QuadExtTopologyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SiegelParabolicPreservesSchwartzBruhat
import Theorems.Thm_GlobalTheory_T_hermitianMatrixColumnPairing_algebraic_properties
import Theorems.Thm_GlobalTheory_T_quadExt_topological_properties
import Theorems.Thm_GlobalTheory_T_splitUnitarySiegelParabolic_block_relations
import Theorems.Thm_GlobalTheory_WeilM_isLocallyConstant_addChar
import Theorems.Thm_GlobalTheory_WeilM_nonarch_field


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)
open GlobalTheory GlobalTheory.KSp
namespace GlobalTheory.KSp
theorem _root_.solution : ∀ (F : Type) [Field F] [CharZero F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (E : Type) [Field E] [Algebra F E] [TopologicalSpace E] [IsModuleTopology F E] (c : E →ₐ[F] E) (δ : E) (hE : IsQuad c δ) (α : Type) [Fintype α] [DecidableEq α] (ν : Type) [Fintype ν] [DecidableEq ν] (Q : Matrix α α E) (_ : IsHerm c Q) (ψ : AddChar F ℂ) (hψ : Continuous ψ) (_ : ∀ t, ‖ψ t‖ = 1) (_ : ψ ≠ 1) (χ : Eˣ →* Circle) (_ : Continuous χ) (_ : ResEtaPow (R := F) ⊥ χ (Fintype.card α)) (p : UG c (stdJ ν E)), p ∈ sieg c ν → ∀ φ ∈ SB (Matrix α ν E), parFun c ψ χ Q (mat c p) φ ∈ SB (Matrix α ν E) := by
  intro F _ _ _ _ _ E _ _ _ _ c δ hE α _ _ ν _ _ Q hQ ψ hψ _ _ χ _ _ p hp φ hφ
  obtain ⟨-, hring, -, -, hc, -, htr, -⟩ := GlobalTheory.T.quadExt_topological_properties F E c δ hE
  obtain ⟨β, hβ, -, -, -, hform⟩ := GlobalTheory.T.hermitianMatrixColumnPairing_algebraic_properties F E c δ hE α ν Q hQ
  obtain ⟨hinv, -, -⟩ := GlobalTheory.T.splitUnitarySiegelParabolic_block_relations F E c δ hE ν p hp
  haveI := GlobalTheory.WeilM.nonarch_field F
  set a := (mat c p).toBlocks₁₁ with ha
  set b := (mat c p).toBlocks₁₂ with hb
  set d := (((mat c p).toBlocks₂₂).map c)ᵀ with hd
  have hinv' : d * a = 1 := mul_eq_one_comm.mp hinv
  have hca : Continuous fun x : Matrix α ν E => x * a := continuous_id.matrix_mul continuous_const
  have hcb : Continuous fun x : Matrix α ν E => x * b := continuous_id.matrix_mul continuous_const
  have hcd : Continuous fun x : Matrix α ν E => x * d := continuous_id.matrix_mul continuous_const
  let e : Matrix α ν E ≃ₜ Matrix α ν E :=
    { toFun := fun x => x * a
      invFun := fun x => x * d
      left_inv := fun x => by simp only [Matrix.mul_assoc, hinv, Matrix.mul_one]
      right_inv := fun x => by simp only [Matrix.mul_assoc, hinv', Matrix.mul_one]
      continuous_toFun := hca
      continuous_invFun := hcd }
  have hpr : Continuous fun x : Matrix α ν E => (2⁻¹ : F) * pr c Q (x * a) (x * b) := by
    refine continuous_const.mul ?_
    have : (fun x : Matrix α ν E => pr c Q (x * a) (x * b)) = fun x =>
        2⁻¹ * Algebra.trace F E (Matrix.trace (Qᵀ * ((x * a) * ((x * b).map c)ᵀ))) := by
      funext x; rw [← hβ, hform]
    rw [this]
    exact continuous_const.mul (htr.comp (continuous_const.matrix_mul
      (hca.matrix_mul (hcb.matrix_map hc).matrix_transpose)).matrix_trace)
  have h1 := (GlobalTheory.WeilM.isLocallyConstant_addChar ψ hψ).comp_continuous hpr
  have h2 : IsLocallyConstant (φ ∘ fun x : Matrix α ν E => x * a) := hφ.1.comp_continuous hca
  have h3 : HasCompactSupport (φ ∘ e) := hφ.2.comp_homeomorph e
  refine ⟨(IsLocallyConstant.const _).mul (h1.mul h2), ?_⟩
  exact HasCompactSupport.mul_left (HasCompactSupport.mul_left h3)
end GlobalTheory.KSp
