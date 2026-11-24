-- Prove2me | solution 1 for GlobalTheory.CollapseCompare.exists_rescaled
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:22:11.938895+00:00
-- url     : https://prove2.me/submissions/0c2d188f-5d6a-4b64-8c0b-2f296c045a86

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_OnesRepresent
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_SiegelEisenstein_FlatOmegaSeries
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHilbertSchmidtOfFiniteDimensional
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsUnitarisableOfCharIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_EventuallyCompSideMulEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_AddCharConductorAndHaarIntegersExist
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_RootExchangeUnipotentHaarAndModulus
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IntegralCompBlocks
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_MemNormalizerOfTri
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_SmulFrameMulFrameInvApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_CoreIffCollapsesWith
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_IdealChain_opE_rescale_frame
import Theorems.Thm_GlobalTheory_RootEx_OpELevi_opE_const_mul
import Theorems.Thm_GlobalTheory_SplitWeil_HasConductor_continuous
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.IndefiniteRowSideFullHecke.FlatOmegaSeries
open scoped NNReal ENNReal
noncomputable section
open GlobalTheory GlobalTheory.CollapseCompare
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}
open GlobalTheory.IndefiniteRowSideFullHecke.HalfPowerSpherical (frame)
variable [MeasurableSpace k] [BorelSpace k]
namespace GlobalTheory.CollapseCompare
theorem _root_.solution (β : kˣ) (ν ν₀ : Measure k) [ν.IsAddHaarMeasure] [ν₀.IsAddHaarMeasure]
    {t : GL (n ⊕ Fin c) k} (ht : t = frame n c fun i => 1⁻¹ * β⁻¹ ^ i)
    {Φ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ} (hΦ : Φ ∈ SB _) :
    ∃ Φ₀ ∈ SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k),
      (∀ ψ μ h, flat (ψ.mulShift (β : k)) ν₀ μ Φ₀ 1 h = flat ψ ν μ Φ 1 (t * h * t⁻¹)) ∧
      ∀ μ h (z : ℂ), om μ 1 (t * h * t⁻¹) Φ = z • Φ → om μ 1 h Φ₀ = z • Φ₀ := by
  obtain ⟨C, -, hC⟩ := IdealChain.opE_rescale_frame k n n' c 1 1 β (fun i => β⁻¹ ^ i) ν ν₀
    (fun i _ _ => by simp [pow_succ]) inferInstance inferInstance
  rw [← ht] at hC
  set t' := frame n' (c + 1) fun i => β⁻¹ ^ i
  simp only [Units.val_one, one_smul, inv_one] at hC
  have key : ∀ μ h, om μ 1 h (fun y : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k => (C : ℂ) * Φ (t.val * y * (t'⁻¹).val)) =
      fun y : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k => (C : ℂ) * om μ 1 (t * h * t⁻¹) Φ (t.val * y * (t'⁻¹).val) := fun μ h => by
    funext y
    have e1 : Matrix.GeneralLinearGroup.det (t * h * t⁻¹) = Matrix.GeneralLinearGroup.det h := by
      rw [map_mul, map_mul, map_inv, mul_inv_cancel_comm]
    have e2 : ((t * h * t⁻¹)⁻¹).val * (t.val * y * (t'⁻¹).val) = t.val * ((h⁻¹).val * y) * (t'⁻¹).val := by
      rw [show (t * h * t⁻¹)⁻¹ = t * h⁻¹ * t⁻¹ by group]
      simp only [Units.val_mul, Matrix.mul_assoc]
      rw [← Matrix.mul_assoc (t⁻¹).val, Units.inv_mul, Matrix.one_mul]
    simp only [om, e1, Units.val_one, Matrix.mul_one, e2]
    ring
  refine ⟨fun y : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k => (C : ℂ) * Φ (t.val * y * (t'⁻¹).val), (SB _).smul_mem (C : ℂ)
    (x := fun y => Φ (sideMul t'⁻¹ t⁻¹ y))
    ⟨hΦ.1.comp_continuous (sideMul t'⁻¹ t⁻¹).continuous, hΦ.2.comp_homeomorph (sideMul t'⁻¹ t⁻¹)⟩,
    fun ψ μ h => funext fun x => ?_, fun μ h z hz => ?_⟩
  · rw [flat, flat, hC, key, OpELevi.opE_const_mul]
  · rw [key, hz]
    funext y
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
end GlobalTheory.CollapseCompare
