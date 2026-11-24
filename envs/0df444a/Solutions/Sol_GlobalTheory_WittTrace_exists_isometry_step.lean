-- Prove2me | solution 1 for GlobalTheory.WittTrace.exists_isometry_step
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:28:12.122802+00:00
-- url     : https://prove2.me/submissions/ce3e1329-2ed6-4b72-84a2-83d8085c2770

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_ExistsGlIsometryCompEqOfNondegenerate
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsIsometryOfLinearIndependent
import Theorems.Thm_GlobalTheory_WittTrace_exists_dual_ne_zero
import Theorems.Thm_GlobalTheory_HermWitt_apply_quasiRefl_quasiRefl
import Theorems.Thm_GlobalTheory_HermWitt_exists_isometry_of_apply_sub_ne_zero
import Theorems.Thm_GlobalTheory_HermWitt_quasiRefl_apply
import Theorems.Thm_GlobalTheory_HermWitt_quasiRefl_quasiRefl


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.WittTrace
open Module Matrix GlobalTheory.HermDiag GlobalTheory.HermWitt
variable {E : Type*} [Field E] {c : E →+* E} {V : Type*} [AddCommGroup V] [Module E V]
namespace GlobalTheory.WittTrace
theorem _root_.solution (hs : ∀ b : E, c b = b → ∃ s : E, s ≠ 0 ∧ s + c s = b)
    (hc : ∀ t, c (c t) = t) {B : V →ₗ[E] V →ₛₗ[c] E} (hB : ∀ x y, c (B x y) = B y x)
    (hrep : ∀ ψ : V →ₗ[E] E, ∃ w, ∀ z, B z w = ψ z) (S : Set V) {x y : V}
    (hx : x ∉ Submodule.span E S) (hy : y ∉ Submodule.span E S) (hxy : B x x = B y y)
    (hS : ∀ h ∈ S, B h x = B h y) :
    ∃ γ : V ≃ₗ[E] V, (∀ z w, B (γ z) (γ w) = B z w) ∧ γ x = y ∧ ∀ h ∈ S, γ h = h := by
  have hSxy : ∀ h ∈ S, B h (x - y) = 0 := fun h hh => by rw [map_sub, hS h hh, sub_self]
  by_cases hne : B x (x - y) = 0
  swap
  · obtain ⟨γ, hγ, hγx, hγu⟩ := exists_isometry_of_apply_sub_ne_zero hB hxy hne
    exact ⟨γ, hγ, hγx, fun h hh => hγu h (hSxy h hh)⟩
  obtain ⟨ψ, hψH, hψx, hψy⟩ := exists_dual_ne_zero (Submodule.span E S) hx hy
  obtain ⟨v, hv⟩ := hrep ψ
  obtain ⟨a, ha, hav⟩ := hs (B v v) (hB v v)
  have hca : c a ≠ 0 := (map_ne_zero c).2 ha
  have hvS : ∀ h ∈ S, B h v = 0 := fun h hh => by
    rw [hv]; exact hψH h (Submodule.subset_span hh)
  obtain ⟨σ, hσq⟩ : ∃ σ : V ≃ₗ[E] V, ∀ z, σ z = quasiRefl B v a z :=
    ⟨LinearEquiv.ofLinear (quasiRefl B v a) (quasiRefl B v (c a))
      (LinearMap.ext fun z => quasiRefl_quasiRefl B hca ha (by rw [add_comm]; exact hav) z)
      (LinearMap.ext fun z => quasiRefl_quasiRefl B ha hca hav z), fun _ => rfl⟩
  have hσ : ∀ z w, B (σ z) (σ w) = B z w := fun z w => by
    rw [hσq, hσq]; exact apply_quasiRefl_quasiRefl hB ha hav z w
  have hσS : ∀ h ∈ S, σ h = h := fun h hh => by
    rw [hσq, quasiRefl_apply, hvS h hh, mul_zero, zero_smul, sub_zero]
  have hσx : σ x = x - (a⁻¹ * B x v) • v := by rw [hσq, quasiRefl_apply]
  have key : B (σ x) (σ x - y) = a⁻¹ * B x v * B v y := by
    have h0 : B x x - B x y = 0 := by rw [← map_sub]; exact hne
    rw [map_sub, hσ x x, hσx]
    simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul]
    linear_combination h0
  have hkey : B (σ x) (σ x - y) ≠ 0 := by
    rw [key]
    refine mul_ne_zero (mul_ne_zero (inv_ne_zero ha) (by rw [hv]; exact hψx)) ?_
    rw [← hB y v, hv]
    exact (map_ne_zero c).2 hψy
  obtain ⟨γ, hγ, hγx, hγu⟩ :=
    exists_isometry_of_apply_sub_ne_zero hB (by rw [hσ]; exact hxy) hkey
  refine ⟨σ.trans γ, fun z w => by simp only [LinearEquiv.trans_apply, hγ, hσ], ?_, ?_⟩
  · simp only [LinearEquiv.trans_apply]; exact hγx
  · intro h hh
    simp only [LinearEquiv.trans_apply, hσS h hh]
    refine hγu h ?_
    have e := hσ h x
    rw [hσS h hh] at e
    rw [map_sub, e, hS h hh, sub_self]
end GlobalTheory.WittTrace
