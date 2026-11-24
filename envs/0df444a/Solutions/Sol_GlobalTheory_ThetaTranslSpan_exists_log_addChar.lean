-- Prove2me | solution 1 for GlobalTheory.ThetaTranslSpan.exists_log_addChar
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:33:05.716236+00:00
-- url     : https://prove2.me/submissions/83505a18-733f-4d50-a617-fdc5d9ca388b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_FourierCoeffUnitCubeTranslateOfEntirePeriodic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_EntirePeriodicEqZeroOfFourierCoeffEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_CardLePowOfLinearIndependent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_IsUnitOfLagrangian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_CardLePowOfLinearIndependentThetaPrincipal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsImEqLattice
import Theorems.Thm_GlobalTheory_orthogonalQuotientForm_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.orthogonalQuotientForm_mk



set_option autoImplicit false
open Matrix
open scoped ComplexOrder
open GlobalTheory GlobalTheory.ThetaTranslSpan
variable {g : ℕ} {Hm : Matrix (Fin g) (Fin g) ℂ}
namespace GlobalTheory.ThetaTranslSpan
theorem _root_.solution {A : Type} [AddCommGroup A] [Module.Free ℤ A] (ψ : AddChar A ℂ)
    (hψ : ∀ a, ‖ψ a‖ = 1) :
    ∃ φ : A →ₗ[ℤ] ℝ, ∀ a, ψ a = Complex.exp (2 * Real.pi * Complex.I * (φ a : ℝ)) := by
  let b := Module.Free.chooseBasis ℤ A
  let φ : A →ₗ[ℤ] ℝ := b.constr ℤ fun i => (ψ (b i)).arg / (2 * Real.pi)
  refine ⟨φ, fun a => ?_⟩
  have ha : a ∈ Submodule.span ℤ (Set.range b) := b.span_eq ▸ Submodule.mem_top
  induction ha using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    rw [Module.Basis.constr_basis]
    conv_lhs => rw [← Complex.norm_mul_exp_arg_mul_I (ψ (b i)), hψ]
    push_cast
    rw [one_mul]; congr 1; field_simp
  | zero => simp
  | add x y _ _ hx hy =>
    rw [AddChar.map_add_eq_mul, hx, hy, map_add, ← Complex.exp_add]; congr 1; push_cast; ring
  | smul t x _ hx =>
    rw [AddChar.map_zsmul_eq_zpow, hx, map_zsmul, ← Complex.exp_int_mul]; congr 1
    simp; ring
end GlobalTheory.ThetaTranslSpan
