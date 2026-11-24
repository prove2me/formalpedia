-- Prove2me | solution 1 for GlobalTheory.RootEx.Exchange.exchange_isPos
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:01:38.612148+00:00
-- url     : https://prove2.me/submissions/d8e5d270-ff92-4796-be92-ae44a07cad9a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSumRowCol
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_RootExchangeSupportAndFourierRelation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LinearChangeOfVariablesLocalFieldMatrix
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IntegrableOfMemSB
import Theorems.Thm_GlobalTheory_RootEx_Exchange_rowE_mul_embX
import Theorems.Thm_GlobalTheory_RootEx_Exchange_colE_mul_embX
import Theorems.Thm_GlobalTheory_RootEx_Exchange_rowE_mul_mem
import Theorems.Thm_GlobalTheory_RootEx_Exchange_colE_mul_mem
import Theorems.Thm_GlobalTheory_RootEx_Exchange_isNEquiv_integral
import Theorems.Thm_GlobalTheory_RootEx_Exchange_integral_embX
import Theorems.Thm_GlobalTheory_RootEx_ExchangeSupport_exchange_support
import Theorems.Thm_GlobalTheory_SplitWeil_nabs_mul
import Theorems.Thm_GlobalTheory_SplitWeil_nabs_one
import Theorems.Thm_GlobalTheory_SplitWeil_nabs_pos


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx
noncomputable section
open GlobalTheory GlobalTheory.RootEx GlobalTheory.RootEx.Exchange
namespace GlobalTheory.RootEx.Exchange
theorem _root_.solution : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n : Type) [Fintype n] [DecidableEq n] (c p : ℕ) (_ : 1 ≤ p) (_ : p < c) (ψ : AddChar k Circle) (_ : Continuous ψ) (_ : ψ ≠ 1) (ν : Measure k) [ν.IsAddHaarMeasure] (A : Type) [AddCommGroup A] [Module ℂ A] (σ : Representation ℂ (GL (n ⊕ Fin c) k) A) (_ : IsSmoothRep σ), (∀ l : A →ₗ[ℂ] ℂ, IsNEquiv ψ p σ l → ∃ l' : A →ₗ[ℂ] ℂ, (∀ v, l' v = exUp ν p σ l v) ∧ IsNEquiv ψ (p + 1) σ l') ∧ (∀ l : A →ₗ[ℂ] ℂ, IsNEquiv ψ (p + 1) σ l → ∃ l' : A →ₗ[ℂ] ℂ, (∀ v, l' v = exDown ν p σ l v) ∧ IsNEquiv ψ p σ l') ∧ ∀ (P : Type) [AddCommGroup P] [Module ℂ P] (π : Representation ℂ (GL n k) P) (b : P →ₗ[ℂ] A →ₗ[ℂ] ℂ), (IsPos ψ p π σ b → ∃ b' : P →ₗ[ℂ] A →ₗ[ℂ] ℂ, (∀ φ v, b' φ v = exUp ν p σ (b φ) v) ∧ IsPos ψ (p + 1) π σ b') ∧ (IsPos ψ (p + 1) π σ b → ∃ b' : P →ₗ[ℂ] A →ₗ[ℂ] ℂ, (∀ φ v, b' φ v = exDown ν p σ (b φ) v) ∧ IsPos ψ p π σ b') := by
  intro k _ _ _ _ _ _ n _ _ c p hp hpc ψ hψ hψ1 ν _ A _ _ σ hσ
  have H := GlobalTheory.RootEx.ExchangeSupport.exchange_support k n c p hp hpc ψ hψ hψ1 ν A σ hσ
  have up : ∀ l : A → ℂ, IsNEquiv ψ p σ l → IsNEquiv ψ (p + 1) σ (exUp ν p σ l) := fun l hl => by
    obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
    exact isNEquiv_integral ν hl _ fun g hg => rowE_mul_mem ⟨q, by omega⟩ hg
  have down : ∀ l : A → ℂ, IsNEquiv ψ (p + 1) σ l → IsNEquiv ψ p σ (exDown ν p σ l) := fun l hl =>
    isNEquiv_integral ν hl _ fun g hg => colE_mul_mem ⟨p, hpc⟩ hg
  refine ⟨fun l hl => ⟨avg ν (fun u => σ (rowE c p u)) l fun v => ((H l v).1 hl).1, fun v => rfl, up l hl⟩,
    fun l hl => ⟨avg ν (fun u => σ (colE c (p + 1) u)) l fun v => ((H l v).2 hl).1, fun v => rfl, down l hl⟩,
    fun P _ _ π b => ⟨fun hb => ⟨avg₂ ν (fun u => σ (rowE c p u)) b fun φ v => ((H (b φ) v).1 (hb.1 φ)).1,
      fun φ v => rfl, fun φ => up _ (hb.1 φ), fun g φ v => ?_⟩,
    fun hb => ⟨avg₂ ν (fun u => σ (colE c (p + 1) u)) b fun φ v => ((H (b φ) v).2 (hb.1 φ)).1,
      fun φ v => rfl, fun φ => down _ (hb.1 φ), fun g φ v => ?_⟩⟩⟩
  · let m : GL n k := ⟨g.valᵀ, (g⁻¹).valᵀ, by rw [← transpose_mul, Units.inv_mul, transpose_one],
      by rw [← transpose_mul, Units.mul_inv, transpose_one]⟩
    have hm : Matrix.GeneralLinearGroup.det m = Matrix.GeneralLinearGroup.det g := by
      ext; simp [m]
    refine (integral_embX ν (rowE c p) g m _ φ (hb.2 g φ) (fun u => rowE_mul_embX p u g) v).trans ?_
    rw [hm, ← Real.rpow_neg_one, ← Real.rpow_add (nabs_pos k _)]
    congr 3
    push_cast; ring
  · refine (integral_embX ν (colE c (p + 1)) g g⁻¹ _ φ (hb.2 g φ) (fun u => colE_mul_embX (p + 1) u g) v).trans ?_
    have hm : (nabs k (Matrix.GeneralLinearGroup.det g⁻¹))⁻¹ = nabs k (Matrix.GeneralLinearGroup.det g) := by
      apply inv_eq_of_mul_eq_one_right
      rw [← nabs_mul, ← map_mul, inv_mul_cancel, map_one, nabs_one]
    rw [hm, ← Real.rpow_add_one (nabs_pos k _).ne']
    congr 3
    push_cast; ring
end GlobalTheory.RootEx.Exchange
