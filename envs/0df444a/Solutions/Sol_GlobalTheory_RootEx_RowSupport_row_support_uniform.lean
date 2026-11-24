-- Prove2me | solution 1 for GlobalTheory.RootEx.RowSupport.row_support_uniform
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T20:32:55.42406+00:00
-- url     : https://prove2.me/submissions/e09da007-9bb6-4700-af7e-a800401193ad

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_RootExchangeSupportAndFourierRelation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_RowSupportUniform
import Theorems.Thm_GlobalTheory_RootEx_RowSupport_exists_box
import Theorems.Thm_GlobalTheory_RootEx_ExchangeSupport_colE_zero
import Theorems.Thm_GlobalTheory_RootEx_ExchangeSupport_conj_col
import Theorems.Thm_GlobalTheory_RootEx_ExchangeSupport_continuous_colE


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx
open Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.RootEx GlobalTheory.RootEx.RowSupport
open GlobalTheory.RootEx.ExchangeSupport
namespace GlobalTheory.RootEx.RowSupport
theorem _root_.solution : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : Type) [Fintype n] [DecidableEq n] (c p : ℕ) (_ : 1 ≤ p) (_ : p < c) (ψ : AddChar k Circle) (_ : ψ ≠ 1) (A : Type) [AddCommGroup A] [Module ℂ A] (σ : Representation ℂ (GL (n ⊕ Fin c) k) A) (_ : IsSmoothRep σ) (F : A) (Ω : Set (GL (n ⊕ Fin c) k)) (_ : IsCompact Ω), ∃ B : Set (n → k), IsCompact B ∧ ∀ l : A →ₗ[ℂ] ℂ, IsNEquiv ψ p σ l → ∀ w ∈ Ω, ∀ u, u ∉ B → l (σ (rowE c p u) (σ w F)) = 0 := by
  intro k _ _ _ _ n _ _ c p hp hc ψ hψ A _ _ σ hσ F Ω hΩ
  set S : Set (GL (n ⊕ Fin c) k) := {g | σ g F = F} with hSdef
  have hS : IsOpen S := hσ F
  have hcol : Continuous fun β : n → k => colE (k := k) c (p + 1) β :=
    ExchangeSupport.continuous_colE
  have hfix : ∀ᶠ β in 𝓝 (0 : n → k), ∀ w ∈ Ω, σ (colE c (p + 1) β) (σ w F) = σ w F := by
    refine hΩ.eventually_forall_of_forall_eventually fun w _ => ?_
    have hc2 : Continuous fun z : (n → k) × GL (n ⊕ Fin c) k => z.2⁻¹ * colE c (p + 1) z.1 * z.2 :=
      ((continuous_snd.inv).mul (hcol.comp continuous_fst)).mul continuous_snd
    have hmem : ((0 : n → k), w).2⁻¹ * colE c (p + 1) ((0 : n → k), w).1 * ((0 : n → k), w).2 ∈ S := by
      simp [hSdef, ExchangeSupport.colE_zero]
    filter_upwards [hc2.continuousAt.preimage_mem_nhds (hS.mem_nhds hmem)] with z hz
    have hz' : σ (z.2⁻¹ * colE c (p + 1) z.1 * z.2) F = F := hz
    calc σ (colE c (p + 1) z.1) (σ z.2 F)
        = σ (z.2 * (z.2⁻¹ * colE c (p + 1) z.1 * z.2)) F := by
          rw [map_mul σ z.2, Module.End.mul_apply, map_mul, map_mul, Module.End.mul_apply,
            Module.End.mul_apply]
          rw [← Module.End.mul_apply (σ z.2), ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
      _ = σ z.2 F := by rw [map_mul, Module.End.mul_apply, hz']
  obtain ⟨B, hB, hBout⟩ := exists_box hψ {β | ∀ w ∈ Ω, σ (colE c (p + 1) β) (σ w F) = σ w F} hfix
  refine ⟨B, hB, fun l hl w hw u hu => ?_⟩
  obtain ⟨β, hβ, hne⟩ := hBout u hu
  obtain ⟨hN, hsum⟩ := ExchangeSupport.conj_col (k := k) (n := n) hp hc u β
  have key := hl _ hN (σ (rowE c p u) (σ w F))
  rw [hsum] at key
  have lhs : σ (rowE c p u * colE c (p + 1) β * (rowE c p u)⁻¹) (σ (rowE c p u) (σ w F)) =
      σ (rowE c p u) (σ w F) := by
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel_right, map_mul, Module.End.mul_apply, hβ w hw]
  rw [lhs] at key
  have hne' : (ψ (u ⬝ᵥ β) : ℂ) ≠ 1 := by
    intro h
    exact hne (Subtype.ext (by simpa using h))
  have : (1 - (ψ (u ⬝ᵥ β) : ℂ)) * l (σ (rowE c p u) (σ w F)) = 0 := by
    rw [sub_mul, one_mul, ← key, sub_self]
  rcases mul_eq_zero.mp this with h | h
  · exact absurd (sub_eq_zero.mp h).symm hne'
  · exact h
end GlobalTheory.RootEx.RowSupport
