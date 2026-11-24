-- Prove2me | solution 1 for GlobalTheory.WpFam.Act.rightActions
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:28:16.239876+00:00
-- url     : https://prove2.me/submissions/b34a2dd3-cfad-43a3-b05c-0281a4276088

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ZetaActRefl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ModularGroupRowVecAndConjRightActions
import Theorems.Thm_GlobalTheory_WpFam_Act_redGL_mul
import Theorems.Thm_GlobalTheory_WpFam_Act_redGL_one
import Theorems.Thm_GlobalTheory_WpFam_Act_vmul_vmul
import Theorems.Thm_GlobalTheory_WpFam_Act_vmul_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open GlobalTheory.QFam GlobalTheory.WpFam
open GlobalTheory GlobalTheory.WpFam GlobalTheory.WpFam.Act
open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
namespace GlobalTheory.WpFam.Act
namespace _root_.GlobalTheory.WpFam.Act
theorem _root_.solution : ∀ (N : ℕ), _root_.GlobalTheory.QFam.IsRAct (_root_.GlobalTheory.WpFam.vact N) ∧ (∀ D, _root_.GlobalTheory.QFam.IsRAct (_root_.GlobalTheory.WpFam.gact N D)) ∧ (∀ (x : Fin 2 → ZMod N) α β, _root_.GlobalTheory.WpFam.vmul (_root_.GlobalTheory.WpFam.vmul x α) β = _root_.GlobalTheory.WpFam.vmul x (α * β)) ∧ (∀ x : Fin 2 → ZMod N, _root_.GlobalTheory.WpFam.vmul x 1 = x) ∧ (∀ (x : Fin 2 → ZMod N) α, _root_.GlobalTheory.WpFam.vmul x α = 0 ↔ x = 0) ∧ (∀ (M : ℕ) (x : Fin 2 → ZMod N) α, _root_.GlobalTheory.WpFam.vmul (M • x) α = M • _root_.GlobalTheory.WpFam.vmul x α) ∧ (∀ (x : Fin 2 → ZMod N) (a : (ZMod N)ˣ), _root_.GlobalTheory.WpFam.vmul x (_root_.GlobalTheory.WpFam.dg a) = ![x 0, (a : ZMod N) * x 1]) ∧ (∀ γ δ, _root_.GlobalTheory.WpFam.redGL N (γ * δ) = _root_.GlobalTheory.WpFam.redGL N γ * _root_.GlobalTheory.WpFam.redGL N δ) ∧ _root_.GlobalTheory.WpFam.redGL N 1 = 1 := by
  intro N
  refine ⟨?_, ?_, _root_.GlobalTheory.WpFam.Act.vmul_vmul, _root_.GlobalTheory.WpFam.Act.vmul_one, ?_, ?_, ?_,
    _root_.GlobalTheory.WpFam.Act.redGL_mul N, _root_.GlobalTheory.WpFam.Act.redGL_one N⟩
  · refine ⟨fun x => ?_, fun x γ δ => ?_⟩
    · unfold _root_.GlobalTheory.WpFam.vact
      rw [_root_.GlobalTheory.WpFam.Act.redGL_one, _root_.GlobalTheory.WpFam.Act.vmul_one]
    · unfold _root_.GlobalTheory.WpFam.vact
      rw [_root_.GlobalTheory.WpFam.Act.vmul_vmul, _root_.GlobalTheory.WpFam.Act.redGL_mul]
  · intro D
    refine ⟨fun α => ?_, fun α γ δ => ?_⟩
    · unfold _root_.GlobalTheory.WpFam.gact
      rw [_root_.GlobalTheory.WpFam.Act.redGL_one]
      group
    · unfold _root_.GlobalTheory.WpFam.gact
      rw [_root_.GlobalTheory.WpFam.Act.redGL_mul]
      group
  · intro x α
    constructor
    · intro h
      have key := congrArg (fun y => _root_.GlobalTheory.WpFam.vmul y α⁻¹) h
      simp only [_root_.GlobalTheory.WpFam.Act.vmul_vmul, mul_inv_cancel, _root_.GlobalTheory.WpFam.Act.vmul_one] at key
      rw [key]
      unfold _root_.GlobalTheory.WpFam.vmul
      simp
    · rintro rfl
      unfold _root_.GlobalTheory.WpFam.vmul
      simp
  · intro M x α
    unfold _root_.GlobalTheory.WpFam.vmul
    rw [Matrix.smul_vecMul]
  · intro x a
    unfold _root_.GlobalTheory.WpFam.vmul _root_.GlobalTheory.WpFam.dg
    ext i
    fin_cases i <;> simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two, mul_comm]
end _root_.GlobalTheory.WpFam.Act
end GlobalTheory.WpFam.Act
