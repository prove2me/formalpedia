-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.LocalFieldChar.isOpen_addChar_ker
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T13:08:23.661613+00:00
-- url     : https://prove2.me/submissions/bbf04f2e-168c-4e5a-a108-7837f04728ab

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IsOpenAdditiveCharacterKernel
import Theorems.Thm_GlobalTheory_CompanionTheory_LocalFieldChar_circle_eq_one_of_forall_re_pow_pos

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology ValuativeRel
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.LocalFieldChar
namespace GlobalTheory.CompanionTheory.LocalFieldChar
theorem _root_.solution : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle), Continuous ψ →
    IsOpen {x : k | ψ x = 1} := by
  intro k _ _ _ _ ψ hψ
  let H : AddSubgroup k :=
    { carrier := {x | ψ x = 1}
      add_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq] at ha hb ⊢
        rw [AddChar.map_add_eq_mul, ha, hb, one_mul]
      zero_mem' := by simp
      neg_mem' := fun {a} ha => by
        simp only [Set.mem_setOf_eq] at ha ⊢
        rw [AddChar.map_neg_eq_inv, ha, inv_one] }
  have hV : IsOpen {z : Circle | 0 < (z : ℂ).re} :=
    isOpen_lt continuous_const (Complex.continuous_re.comp continuous_induced_dom)
  have hU : ψ ⁻¹' {z : Circle | 0 < (z : ℂ).re} ∈ 𝓝 (0 : k) :=
    (hV.preimage hψ).mem_nhds (by simp)
  obtain ⟨γ, hγ, hball⟩ := (IsValuativeTopology.hasBasis_nhds_zero' k).mem_iff.1 hU
  have hsmul : ∀ x : k, valuation k x < γ → ∀ n : ℕ, valuation k (n • x) < γ := by
    intro x hx n
    induction n with
    | zero => simpa using zero_lt_iff.2 hγ
    | succ n ih =>
      rw [succ_nsmul]
      exact Valuation.map_add_lt _ ih hx
  have hone : ∀ x : k, valuation k x < γ → x ∈ H := by
    intro x hx
    refine circle_eq_one_of_forall_re_pow_pos (ψ x) fun n => ?_
    have h1 : 0 < ((ψ (n • x) : Circle) : ℂ).re := hball (hsmul x hx n)
    rwa [AddChar.map_nsmul_eq_pow] at h1
  have hnh : (H : Set k) ∈ 𝓝 (0 : k) :=
    (IsValuativeTopology.hasBasis_nhds_zero' k).mem_iff.2 ⟨γ, hγ, fun x hx => hone x hx⟩
  exact H.isOpen_of_mem_nhds hnh
end GlobalTheory.CompanionTheory.LocalFieldChar
