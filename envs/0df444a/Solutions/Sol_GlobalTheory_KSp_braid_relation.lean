-- Prove2me | solution 1 for GlobalTheory.KSp.braid_relation
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:43:15.400238+00:00
-- url     : https://prove2.me/submissions/05ccd220-ccaa-4d7d-b794-86a6e40c383a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_UnipVal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsSelfDualBicharacterPairingOfSymmBilinFormStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HermitianMatrixColumnPairingAlgebraicPropertiesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitaryCharacterAbsScalarBasicPropertiesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_QuadExtTopologyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_WeilFormulaFourierQuadraticCharacterStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FourierHermitianMultiplierBraidRelation
import Theorems.Thm_GlobalTheory_SplitWeil_HasConductor_continuous
import Theorems.Thm_GlobalTheory_T_hermitianMatrixColumnPairing_algebraic_properties
import Theorems.Thm_GlobalTheory_T_isSelfDualBicharacterPairing_of_symmBilinForm
import Theorems.Thm_GlobalTheory_T_quadExt_topological_properties
import Theorems.Thm_GlobalTheory_T_unitaryCharacterAbsScalar_basic_properties
import Theorems.Thm_GlobalTheory_T_weil_formula_fourier_quadratic_character


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
theorem _root_.solution : ∀ (F : Type) [Field F] [CharZero F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (E : Type) [Field E] [Algebra F E] [TopologicalSpace E] [IsModuleTopology F E] (c : E →ₐ[F] E) (δ : E) (hE : IsQuad c δ) (α : Type) [Fintype α] [DecidableEq α] (ν : Type) [Fintype ν] [DecidableEq ν] (Q : Matrix α α E) (_ : IsHerm c Q) (ψ : AddChar F ℂ) (hψ : Continuous ψ) (_ : ∀ t, ‖ψ t‖ = 1) (_ : ψ ≠ 1) (χ : Eˣ →* Circle) (_ : Continuous χ) (_ : ResEtaPow (R := F) ⊥ χ (Fintype.card α)) [MeasurableSpace (Matrix α ν E)] [BorelSpace (Matrix α ν E)] (μ : Measure (Matrix α ν E)) [μ.IsAddHaarMeasure] (b : Matrix ν ν E) (γ : ℂ), (b.map c)ᵀ = b → b.det ≠ 0 → HasGauss μ (fun x => ψ (2⁻¹ * pr c Q x (x * b))) γ → ∀ φ ∈ SB (Matrix α ν E), sc F χ (Fintype.card α) (-b⁻¹).det • fou c ψ Q μ (parFun c ψ χ Q (fromBlocks 1 b 0 1) (fou c ψ Q μ φ)) = γ • parFun c ψ χ Q (fromBlocks (-b⁻¹) 1 0 (-b)) (fou c ψ Q μ (parFun c ψ χ Q (fromBlocks 1 (-b⁻¹) 0 1) φ)) := by
  intro F _ _ _ _ _ E _ _ _ _ c δ hE α _ _ ν _ _ Q hQ ψ hψ hn h1 χ _ hχ _ _ μ _ b γ hb hd hG φ hφ
  obtain ⟨hfd, hring, -, -, -, -, -, hM⟩ := GlobalTheory.T.quadExt_topological_properties F E c δ hE
  obtain ⟨hmod, hgood⟩ := hM α ν
  obtain ⟨β, hβ, hs, hnd, hadj, -⟩ := GlobalTheory.T.hermitianMatrixColumnPairing_algebraic_properties F E c δ hE α ν Q hQ
  have hsc := (GlobalTheory.T.unitaryCharacterAbsScalar_basic_properties F E c δ hE (Fintype.card α) χ hχ).1
  have hP := GlobalTheory.T.isSelfDualBicharacterPairing_of_symmBilinForm F (Matrix α ν E) ψ hψ hn h1 β hs hnd
  have hu : IsUnit b.det := isUnit_iff_ne_zero.mpr hd
  have hi : b⁻¹ * b = 1 := Matrix.nonsing_inv_mul b hu
  have hi' : b * b⁻¹ = 1 := Matrix.mul_nonsing_inv b hu
  have hbb : ∀ x y : Matrix α ν E, β (x * b) y = β x (y * b) := fun x y => by rw [hadj, hb]
  have hbi : ∀ x y : Matrix α ν E, β (x * b⁻¹) y = β x (y * b⁻¹) := fun x y => by
    have := hbb (x * b⁻¹) (y * b⁻¹)
    rw [Matrix.mul_assoc, Matrix.mul_assoc, hi, Matrix.mul_one, Matrix.mul_one] at this
    exact this.symm
  have hpr : (pr c Q : Matrix α ν E → Matrix α ν E → F) = fun x y => β x y := by
    funext x y; exact (hβ x y).symm
  have hf : Continuous fun y : Matrix α ν E => ψ (2⁻¹ * β y (y * b)) := by
    have h2 : Continuous fun y : Matrix α ν E => (y, y * ((2⁻¹ : F) • b)) :=
      continuous_id.prodMk (continuous_id.matrix_mul continuous_const)
    have := hP.lc.continuous.comp h2
    refine this.congr fun y => ?_
    simp [Matrix.mul_smul]
  have hW := GlobalTheory.T.weil_formula_fourier_quadratic_character (Matrix α ν E) hgood μ _ hP (fun y => ψ (2⁻¹ * β y (y * b)))
    (fun u => ψ (-(2⁻¹ * β (u * b⁻¹) u))) (fun u => u * b⁻¹) γ hf
    (continuous_id.matrix_mul continuous_const) (fun y u => by
      rw [← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul]
      congr 1
      have h3 : β (u * b⁻¹) (y * b) = β y u := by
        rw [← hbb, Matrix.mul_assoc, hi, Matrix.mul_one, hs]
      rw [Matrix.add_mul, Matrix.mul_assoc u, hi, Matrix.mul_one]
      simp only [map_add, LinearMap.add_apply, h3]
      ring) (by simpa only [hpr] using hG) φ hφ
  funext x
  have hL : parFun c ψ χ Q (fromBlocks 1 b 0 1) (fou c ψ Q μ φ) =
      fun y => ψ (2⁻¹ * β y (y * b)) * four μ (fun x y => ψ (β x y)) φ y := by
    funext y
    simp [parFun, fou, hsc, hpr]
  rw [hL]
  simp only [Pi.smul_apply, smul_eq_mul, fou, hpr]
  rw [hW x]
  simp only [parFun, four, hpr, toBlocks_fromBlocks₁₁, toBlocks_fromBlocks₁₂, det_one, hsc, Matrix.mul_one, one_mul]
  rw [mul_left_comm, ← integral_const_mul (ψ _)]
  congr 3
  funext z
  rw [← mul_assoc, ← mul_assoc, ← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul]
  congr 2
  have h4 : β (z * b⁻¹) x = β (x * b⁻¹) z := by rw [hbi, hs]
  simp only [Matrix.add_mul, Matrix.mul_neg, map_add, map_neg, LinearMap.add_apply, LinearMap.neg_apply, h4, ← hbi z z]
  ring
end GlobalTheory.KSp
